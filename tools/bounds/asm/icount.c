/* Count the user-space instructions executed by a program, by single-stepping it. */
#include <stdio.h>
#include <stdlib.h>
#include <sys/personality.h>
#include <sys/ptrace.h>
#include <sys/wait.h>
#include <unistd.h>

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: icount prog args...\n"); return 2; }
  pid_t pid = fork();
  if (pid == 0) {
    personality(ADDR_NO_RANDOMIZE);    /* the same addresses, the same counts */
    ptrace(PTRACE_TRACEME, 0, NULL, NULL);
    execv(argv[1], argv + 1);
    perror("execv");
    _exit(127);
  }
  int status;
  long long n = 0;
  waitpid(pid, &status, 0);            /* stopped at exec */
  while (1) {
    if (ptrace(PTRACE_SINGLESTEP, pid, NULL, NULL) < 0) { perror("ptrace"); return 1; }
    waitpid(pid, &status, 0);
    if (WIFEXITED(status) || WIFSIGNALED(status)) break;
    n++;
  }
  printf("%lld\n", n);
  return 0;
}
