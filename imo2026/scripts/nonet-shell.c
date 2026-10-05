#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

int main(int argc, char **argv) {
  (void)argc;
  const char *library = getenv("HUMANIZE_NONET_LIB");
  const char *real_bash = getenv("HUMANIZE_REAL_BASH");
  const char *audit = getenv("HUMANIZE_SHELL_AUDIT");
  if (library == NULL || real_bash == NULL) return 126;
  if (audit != NULL && *audit != '\0') {
    int fd = open(audit, O_WRONLY | O_CREAT | O_APPEND, 0600);
    if (fd >= 0) {
      dprintf(fd, "%ld\n", (long)getpid());
      close(fd);
    }
  }
  if (setenv("LD_PRELOAD", library, 1) != 0) return 126;
  execv(real_bash, argv);
  perror("execv(real bash)");
  return errno == 0 ? 127 : errno;
}
