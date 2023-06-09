/*
 * COMP 321 Project 4: Shell
 *
 * This program implements a tiny shell with job control.
 *
 * Aditi Raju, ar139 & Eric Breyer, eab17
 */

#include <sys/types.h>
#include <sys/wait.h>

#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <signal.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <termios.h>
#include <unistd.h>

#include "./circularBuffer/ringBuffer.h"

// You may assume that these constants are large enough.
#define MAXLINE 1024     // max line size
#define MAXARGS 128      // max args on a command line
#define MAXJOBS 16       // max jobs at any point in time
#define MAXJID (1 << 16) // max job ID

// The job states are:
#define UNDEF 0 // undefined
#define FG 1    // running in foreground
#define BG 2    // running in background
#define ST 3    // stopped

/*
 * The job state transitions and enabling actions are:
 *     FG -> ST  : ctrl-z
 *     ST -> FG  : fg command
 *     ST -> BG  : bg command
 *     BG -> FG  : fg command
 * At most one job can be in the FG state.
 */

struct Job {
    pid_t pid;             // job PID
    int jid;               // job ID [1, 2, ...]
    int state;             // UNDEF, FG, BG, or ST
    char cmdline[MAXLINE]; // command line
};
typedef volatile struct Job *JobP;

/*
 * Define the jobs list using the "volatile" qualifier because it is accessed
 * by a signal handler (as well as the main program).
 */
static volatile struct Job jobs[MAXJOBS];
static int nextjid = 1; // next job ID to allocate

extern char **environ; // defined by libc

static char prompt[] = " esh> "; // command line prompt (DO NOT CHANGE)
char cwd[MAXLINE];

static char *getPrompt() {
    memset(cwd, 0, MAXLINE);
    if (getcwd(cwd, sizeof(cwd) - sizeof(prompt)) != NULL) {
        // printf("Current working dir: %s\n", cwd);
        strcat(cwd, prompt);
    } else {
        perror("getcwd() error");
        strcpy(cwd, prompt);
    }
    return cwd;
}

static bool verbose = false; // If true, print additional output.

char **pathDirs = NULL;
int pathDirsLen = 0;

struct ringBuffer *prevCommands;

/*
 * The following array can be used to map a signal number to its name.
 * This mapping is valid for x86(-64)/Linux systems, such as CLEAR.
 * The mapping for other versions of Unix, such as FreeBSD, Mac OS X, or
 * Solaris, differ!
 */
static const char *const signame[NSIG] = {"Signal 0", "HUP", /* SIGHUP */
                                          "INT",             /* SIGINT */
                                          "QUIT",            /* SIGQUIT */
                                          "ILL",             /* SIGILL */
                                          "TRAP",            /* SIGTRAP */
                                          "ABRT",            /* SIGABRT */
                                          "BUS",             /* SIGBUS */
                                          "FPE",             /* SIGFPE */
                                          "KILL",            /* SIGKILL */
                                          "USR1",            /* SIGUSR1 */
                                          "SEGV",            /* SIGSEGV */
                                          "USR2",            /* SIGUSR2 */
                                          "PIPE",            /* SIGPIPE */
                                          "ALRM",            /* SIGALRM */
                                          "TERM",            /* SIGTERM */
                                          "STKFLT",          /* SIGSTKFLT */
                                          "CHLD",            /* SIGCHLD */
                                          "CONT",            /* SIGCONT */
                                          "STOP",            /* SIGSTOP */
                                          "TSTP",            /* SIGTSTP */
                                          "TTIN",            /* SIGTTIN */
                                          "TTOU",            /* SIGTTOU */
                                          "URG",             /* SIGURG */
                                          "XCPU",            /* SIGXCPU */
                                          "XFSZ",            /* SIGXFSZ */
                                          "VTALRM",          /* SIGVTALRM */
                                          "PROF",            /* SIGPROF */
                                          "WINCH",           /* SIGWINCH */
                                          "IO",              /* SIGIO */
                                          "PWR",             /* SIGPWR */
                                          "Signal 31"};

// You must implement the following functions:

static bool builtin_cmd(char **argv);
static void do_bgfg(char **argv);
static void change_dir(char **argv);
static void eval(const char *cmdline);
static void initpath(const char *pathstr); //
static void waitfg(pid_t pid);             //

static void sigchld_handler(int signum); //
static void sigint_handler(int signum);  //
static void sigtstp_handler(int signum); //

struct Command {
    char **argv;
    bool bg;
    char *re_stdout;
    char *re_stdin;
    char *re_stderr;
};
// We are providing the following functions to you:

static bool parseline(const char *cmdline, struct Command *cmd);

static void sigquit_handler(int signum);

static bool addjob(JobP jobs, pid_t pid, int state, const char *cmdline);
static void clearjob(JobP job);
static bool deletejob(JobP jobs, pid_t pid);
static pid_t fgpid(JobP jobs);
static JobP getjobjid(JobP jobs, int jid);
static JobP getjobpid(JobP jobs, pid_t pid);
static void initjobs(JobP jobs);
static void listjobs(JobP jobs);
static int maxjid(JobP jobs);
static int pid2jid(pid_t pid);

static void app_error(const char *msg);
static void unix_error(const char *msg);
static void usage(void);

static void Sio_error(const char s[]);
static ssize_t Sio_putl(long v);
static ssize_t Sio_puts(const char s[]);
static void sio_error(const char s[]);
static void sio_ltoa(long v, char s[], int b);
static ssize_t sio_putl(long v);
static ssize_t sio_puts(const char s[]);
static void sio_reverse(char s[]);
static size_t sio_strlen(const char s[]);

/*
 * Requires:
 *   Nothing.
 *
 * Effects:
 *   Allocates a pointer of size size and returns it on success, throws and
 *   error and exits the program on out of memory failure.
 */
static void *Malloc(size_t size) {
    void *ptr = malloc(size);
    if (ptr == NULL) {
        Sio_error("malloc returned out of memory\n");
    }
    return ptr;
}

/*
 * Requires:
 *   Nothing.
 *
 * Effects:
 *   Sends the signal sig to the process identified by pid on sucess, throws an
 *   error and exits the program if the kill is unsuccessful.
 */
static void Kill(int pid, int sig) {
    if (kill(pid, sig)) {
        Sio_puts("Unable to send signal ");
        Sio_putl(sig);
        Sio_puts(" to process ");
        Sio_putl(pid);
        unix_error("\n");
    }
}

/*
 * Requires:
 *   Nothing.
 *
 * Effects:
 *   Initializes set ss to full on sucess, throws an
 *   error and exits the program if the sigfillset is unsuccessful.
 */
static void Sigfillset(sigset_t *ss) {
    if (sigfillset(ss)) {
        unix_error("Unable to fill signal set\n");
    }
}

/*
 * Requires:
 *   Nothing.
 *
 * Effects:
 *   Initializes the signal set given by ss to empty, throws an
 *   error and exits the program if the sigemptyset is unsuccessful.
 */
static void Sigemptyset(sigset_t *ss) {
    if (sigemptyset(ss)) {
        unix_error("Unable to empty signal set\n");
    }
}

/*
 * Requires:
 *   Nothing.
 *
 * Effects:
 *   Adds signal sig to set ss, throws an
 *   error and exits the program if the sigaddset is unsuccessful.
 */
static void Sigaddset(sigset_t *ss, int sig) {
    if (sigaddset(ss, sig)) {
        unix_error("Unable to add to signal set\n");
    }
}

/*
 * Requires:
 *   Nothing
 *
 * Effects:
 *   Calls sigprocmask with the given arguments, throws an
 *   error and exits the program if the sigprocmask is unsuccessful.
 */
static void Sigprocmask(int sig, sigset_t *ss, sigset_t *ps) {
    if (sigprocmask(sig, ss, ps)) {
        unix_error("Unable to sig proc mask\n");
    }
}

struct termios orig_termios;
void disableRawMode() { tcsetattr(STDIN_FILENO, TCSAFLUSH, &orig_termios); }
void enableRawMode() {
    tcgetattr(STDIN_FILENO, &orig_termios);
    atexit(disableRawMode);
    struct termios raw = orig_termios;
    raw.c_lflag &= ~(ECHO | ICANON);
    tcsetattr(STDIN_FILENO, TCSAFLUSH, &raw);
}

/*
 * Requires:
 *   Nothing.
 *
 * Effects:
 *   Installs all the necessary handlers for the shell's job control
 *   operations. Initializes the search path and read-evaluates the command
 *   line. Then, the command line operations are executed.
 */
int main(int argc, char **argv) {
    struct sigaction action;
    int c;
    char cmdline[MAXLINE];
    char *path = NULL;
    bool emit_prompt = true; // Emit a prompt by default.

    enableRawMode();
    prevCommands = constructRingBuffer(30);
    /*
     * Redirect stderr to stdout (so that driver will get all output
     * on the pipe connected to stdout).
     */
    if (dup2(1, 2) < 0)
        unix_error("dup2 error");

    // Parse the command line.
    while ((c = getopt(argc, argv, "hvp")) != -1) {
        switch (c) {
        case 'h': // Print a help message.
            usage();
            break;
        case 'v': // Emit additional diagnostic info.
            verbose = true;
            break;
        case 'p': // Don't print a prompt.
            // This is handy for automatic testing.
            emit_prompt = false;
            break;
        default:
            usage();
        }
    }

    /*
     * Install sigint_handler() as the handler for SIGINT (ctrl-c).  SET
     * action.sa_mask TO REFLECT THE SYNCHRONIZATION REQUIRED BY YOUR
     * IMPLEMENTATION OF sigint_handler().
     */
    action.sa_handler = sigint_handler;
    action.sa_flags = SA_RESTART;
    /*
     * Block all signals while in sigint_handler, this is convertive in
     * it's restrictiveness but garuntees we won't run into problems.
     */
    if (sigfillset(&action.sa_mask) < 0)
        unix_error("sigemptyset error");
    if (sigaction(SIGINT, &action, NULL) < 0)
        unix_error("sigaction error");

    /*
     * Install sigtstp_handler() as the handler for SIGTSTP (ctrl-z).  SET
     * action.sa_mask TO REFLECT THE SYNCHRONIZATION REQUIRED BY YOUR
     * IMPLEMENTATION OF sigtstp_handler().
     */
    action.sa_handler = sigtstp_handler;
    action.sa_flags = SA_RESTART;
    /*
     * Block all signals while in sigtstp_handler, this is convertive in
     * it's restrictiveness but garuntees we won't run into problems.
     */
    if (sigfillset(&action.sa_mask) < 0)
        unix_error("sigemptyset error");
    if (sigaction(SIGTSTP, &action, NULL) < 0)
        unix_error("sigaction error");

    /*
     * Install sigchld_handler() as the handler for SIGCHLD (terminated or
     * stopped child).  SET action.sa_mask TO REFLECT THE SYNCHRONIZATION
     * REQUIRED BY YOUR IMPLEMENTATION OF sigchld_handler().
     */
    action.sa_handler = sigchld_handler;
    action.sa_flags = SA_RESTART;
    /*
     * Block all signals while in sigchld_handler, this is convertive in
     * it's restrictiveness but garuntees we won't run into problems.
     */
    if (sigfillset(&action.sa_mask) < 0)
        unix_error("sigemptyset error");
    if (sigaction(SIGCHLD, &action, NULL) < 0)
        unix_error("sigaction error");

    /*
     * Install sigquit_handler() as the handler for SIGQUIT.  This handler
     * provides a clean way for the test harness to terminate the shell.
     * Preemption of the processor by the other signal handlers during
     * sigquit_handler() does no harm, so action.sa_mask is set to empty.
     */
    action.sa_handler = sigquit_handler;
    action.sa_flags = SA_RESTART;
    if (sigfillset(&action.sa_mask) < 0)
        unix_error("sigemptyset error");
    if (sigaction(SIGQUIT, &action, NULL) < 0)
        unix_error("sigaction error");

    // signal (SIGTTIN, SIG_IGN);
    signal(SIGTTOU, SIG_IGN);

    // Initialize the search path.
    path = getenv("PATH");
    initpath(path);

    // Initialize the jobs list.
    initjobs(jobs);

    if (argc > 1) {
        freopen(argv[1], "r", stdin);
    }

    // Execute the shell's read/eval loop.
    while (true) {

        // Read the command line.
        if (emit_prompt) {
            printf("%s", getPrompt());
            fflush(stdout);
        }

        memset(cmdline, 0, MAXLINE);
        char ch;
        int linePos = 0;
        int k = 0;
        int histOffset = 0;
        // ringBuffer_print(prevCommands);
        enableRawMode();
        while ((ch = fgetc(stdin)) != '\n' && !feof(stdin)) {
            if (ch == 27) // if ch is the escape sequence with num code 27, k
                          // turns 1 to signal the next
                k = 1;
            else if (ch == 91 &&
                     k == 1) // if the previous char was 27, and the
                             // current 91, k turns 2 for further use
                k = 2;
            else if (ch == 'A' && k == 2) { // finally, if the last char of the
                // sequence matches, you've got a key !
                for (int i = 0; i < linePos; ++i) {
                    if (emit_prompt)
                        printf("\b \b");
                }
                memset(cmdline, 0, MAXLINE);
                strcpy(cmdline, ringBuffer_get(prevCommands, ++histOffset));
                cmdline[strlen(cmdline) - 1] = '\0';
                if (emit_prompt)
                    printf("%s", cmdline);
                linePos = strlen(cmdline);
            } else if (ch == 'B' && k == 2) {
                for (int i = 0; i < linePos; ++i) {
                    if (emit_prompt)
                        printf("\b \b");
                }
                memset(cmdline, 0, MAXLINE);
                if (histOffset > 1) {
                    strcpy(cmdline, ringBuffer_get(prevCommands, --histOffset));
                    cmdline[strlen(cmdline) - 1] = '\0';
                }
                if (emit_prompt)
                    printf("%s", cmdline);
                linePos = strlen(cmdline);
            } else if (ch == 'C' && k == 2) {
                fseek(stdin, +1, SEEK_CUR);
                linePos++;
                printf("\e[1C");
            } else if (ch == 'D' && k == 2) {
                fseek(stdin, -1, SEEK_CUR);
                linePos--;
                printf("\e[1D");
            } else if (ch == 127) {
                if (linePos) {
                    linePos--;
                    if (emit_prompt)
                        printf("\b \b");
                }
            } else {
                k = 0;
                printf("%c", ch);
                cmdline[linePos++] = ch;
            }
        }
        k = 0;
        printf("%c", '\n');
        cmdline[strlen(cmdline)] = ch;
        disableRawMode();

        // Evaluate the command line.
        ringBuffer_insert(prevCommands, cmdline);
        eval(cmdline);
        fflush(stdout);

        if (feof(stdin)) { // End of file (ctrl-d)
            int runningCount;
            do {
                runningCount = 0;
                for (int i = 0; i < MAXJOBS; i++) {
                    if (jobs[i].pid != 0) {
                        ++runningCount;
                    }
                }
            } while (runningCount);

            exit(0);
            app_error("bruh");
        }
    }

    // Control never reaches here.
    assert(false);
}

/*
 * eval - Evaluate the command line that the user has just typed in.
 *
 * If the user has requested a built-in command (quit, jobs, bg or fg)
 * then execute it immediately.  Otherwise, fork a child process and
 * run the job in the context of the child.  If the job is running in
 * the foreground, wait for it to terminate and then return.  Note:
 * each child process must have a unique process group ID so that our
 * background children don't receive SIGINT (SIGTSTP) from the kernel
 * when we type ctrl-c (ctrl-z) at the keyboard.
 *
 * Requires:
 *   The command line typed by the user, "cmdline" should consist of a
 *   "name"(argv[0]) and zero or more arguments, all separated by one or more
 *   spaces. "name" should be a built-in command or the name of an executable
 *   file.
 *
 * Effects:
 *   Parses the command line and performs the necessary commands. If "name"
 *   is a built-in command, handle it immediately. Otherwise, load and run
 *   the executable file names "name" in the context of an initial child
 *   process. If "name" does not start with a directory and the search path
 *   is not null, search the directories in the path for an executable file
 *   names "name", then load and run the first file that is found.If "name"
 *   starts with a directory or the search path is NULL, tsh should assume
 *   that "name" is the path name of an executable file
 */
static void eval(const char *cmdline) {

    // Declare and initialize some variables and mask sets we will need.
    int childPID = 0;
    sigset_t mask_all, mask_one, prev_one;
    Sigfillset(&mask_all);
    Sigemptyset(&mask_one);
    Sigaddset(&mask_one, SIGCHLD);
    FILE *executable_file = NULL;
    char *executeable_path = Malloc(MAXLINE);

    // Parse and store the command line data.

    struct Command cmd;
    cmd.argv = Malloc(MAXARGS * sizeof(char *));
    parseline(cmdline, &cmd);
    bool bg = cmd.bg;
    char **argv = cmd.argv;

    // If the command is builtin, execute it now and return.
    if (builtin_cmd(argv))
        return;
    // If the command is a path, that is the executable path.
    if (argv[0][0] == '.' || argv[0][0] == '/') {
        strcpy(executeable_path, argv[0]);
    }
    // else, search the directories in the $PATH for the executable
    else {
        for (int dirIdx = 0; dirIdx < pathDirsLen; ++dirIdx) {
            sprintf(executeable_path, "%s/%s", pathDirs[dirIdx], argv[0]);
            if ((executable_file = fopen(executeable_path, "r")) == NULL) {
                strcpy(executeable_path, "\0");
                continue;
            }
            fclose(executable_file);
            break;
        }
    }
    // Block sigchilds while we spawn the task.
    Sigprocmask(SIG_BLOCK, &mask_one, &prev_one);
    // Fork the process to spawn a child.
    if ((childPID = fork()) == 0) { // child
        // Make a new process group so sigint doesn't kill tsh.
        if (setpgid(0, 0)) {
            unix_error("Unable to set gpid");
        }
        if (cmd.re_stdin) {
            FILE *f = fopen(cmd.re_stdin, "r");
            dup2(fileno(f), STDIN_FILENO);
            fclose(f);
        }
        if (cmd.re_stderr) {
            FILE *f = fopen(cmd.re_stderr, "w");
            dup2(fileno(f), STDERR_FILENO);
            fclose(f);
        }
        if (cmd.re_stdout) {
            FILE *f = fopen(cmd.re_stdout, "w");
            dup2(fileno(f), STDOUT_FILENO);
            fclose(f);
        }
        if (!bg)
            tcsetpgrp(STDIN_FILENO, getpgrp());
        // Child inherits masks so reset it.
        Sigprocmask(SIG_SETMASK, &prev_one, NULL);
        /*
         * Try to run the program at the path, if it can't be found then
         * exit.
         */
        execve(executeable_path, argv, environ);
        fprintf(stderr, "%s: Command not found.\n", argv[0]);
        exit(0);
    }
    // Mask all signals while we add the job to the list to prevent races.
    Sigprocmask(SIG_BLOCK, &mask_all, NULL); // Parent
    addjob(jobs, childPID, bg ? BG : FG, cmdline);
    // Print aditional info if the job is to run in the background.
    if (bg)
        printf("[%d] (%d) %s", pid2jid(childPID), childPID,
               getjobpid(jobs, childPID)->cmdline);
    else
        tcsetpgrp(STDIN_FILENO, childPID);
    // Reset the mask.
    Sigprocmask(SIG_SETMASK, &prev_one, NULL);
    free(executeable_path); // dont need this anymore

    // Wait on a foreground process (waitfg will just pass if we spawn a bg)
    waitfg(childPID);

    tcsetpgrp(STDIN_FILENO, getpgrp());
    free(argv);
}

enum fileRedirector {
    FR_NONE,
    FR_IN,
    FR_OUT,
    FR_ERR,
};

/*
 * parseline - Parse the command line and build the argv array.
 *
 * Requires:
 *   "cmdline" is a NUL ('\0') terminated string with a trailing
 *   '\n' character.  "cmdline" must contain less than MAXARGS
 *   arguments.
 *
 * Effects:
 *   Builds "argv" array from space delimited arguments on the command line.
 *   The final element of "argv" is set to NULL.  Characters enclosed in
 *   single quotes are treated as a single argument.  Returns true if
 *   the user has requested a BG job and false if the user has requested
 *   a FG job.
 *
 * Note:
 *   In the textbook, this function has the return type "int", but "bool"
 *   is more appropriate.
 */
static bool parseline(const char *cmdline, struct Command *cmd) {
    int argc;                   // number of args
    static char array[MAXLINE]; // local copy of command line
    char *buf = array;          // ptr that traverses command line
    char *delim;                // points to first space delimiter

    char **argv = cmd->argv;
    cmd->re_stderr = NULL;
    cmd->re_stdin = NULL;
    cmd->re_stdout = NULL;

    strcpy(buf, cmdline);

    // Replace trailing '\n' with space.
    buf[strlen(buf) - 1] = ' ';

    // Ignore leading spaces.
    while (*buf != '\0' && *buf == ' ')
        buf++;

    enum fileRedirector fr = FR_NONE;

    // Build the argv list.
    argc = 0;
    if (*buf == '\'') {
        buf++;
        delim = strchr(buf, '\'');
    } else
        delim = strchr(buf, ' ');
    while (delim != NULL) {
        *delim = '\0';
        if (strcmp(buf, "<") == 0) {
            fr = FR_IN;
        } else if (strcmp(buf, ">") == 0) {
            fr = FR_OUT;
        } else if (strcmp(buf, "2>") == 0) {
            fr = FR_ERR;
        } else {
            switch (fr) {
            case FR_NONE:
                argv[argc++] = buf;
                break;
            case FR_IN:
                cmd->re_stdin = buf;
                fr = FR_NONE;
                break;
            case FR_OUT:
                cmd->re_stdout = buf;
                fr = FR_NONE;
                break;
            case FR_ERR:
                cmd->re_stderr = buf;
                fr = FR_NONE;
                break;
            default:
                break;
            }
        }
        buf = delim + 1;
        while (*buf != '\0' && *buf == ' ') // Ignore spaces.
            buf++;
        if (*buf == '\'') {
            buf++;
            delim = strchr(buf, '\'');
        } else
            delim = strchr(buf, ' ');
    }
    argv[argc] = NULL;

    // Ignore blank line.
    if (argc == 0)
        return (true);

    // Should the job run in the background?
    if ((cmd->bg = (*argv[argc - 1] == '&')) != 0)
        argv[--argc] = NULL;

    return (true);
}

/*
 * builtin_cmd - If the user has typed a built-in command then execute
 *  it immediately.
 *
 * Requires:
 *   argv consists of a name followed by zero or more arguments, where name
 *   is a built-in command supported by tsh - quit, jobs, bg or fg.
 *
 * Effects:
 *   Returns true if the first element of argv is a built-in command, and
 *   performs the appropriate command, returns false otherwise.
 *
 * Note:
 *   In the textbook, this function has the return type "int", but "bool"
 *   is more appropriate.
 */
static bool builtin_cmd(char **argv) {
    // If there are no arguments just pass and tell eval we handled it.
    if (argv[0] == NULL) {
        return true;
    }
    // Exit normally on a quit.
    if (strcmp(argv[0], "quit") == 0) {
        int runningCount = 0;
        for (int i = 0; i < MAXJOBS; i++) {
            if (jobs[i].pid != 0) {
                ++runningCount;
            }
        }
        if (runningCount) {
            printf("Still jobs running in background, type \"quit_hard\" to "
                   "quit\n");
            listjobs(jobs);
            return true;
        }
        exit(0);
    }
    if (strcmp(argv[0], "quit_hard") == 0) {
        exit(0);
    }
    // List the jobs and return that we found a builtin.
    else if (strcmp(argv[0], "jobs") == 0) {
        listjobs(jobs);
        return true;
    } else if (strcmp(argv[0], "cd") == 0) {
        change_dir(argv);
        return true;
    }
    // Delegate handling bg/fg to helper and return that we found a builtin.
    else if (strcmp(argv[0], "bg") == 0 || strcmp(argv[0], "fg") == 0) {
        do_bgfg(argv);
        return true;
    }
    // If we did not recognize a builtin, return false.
    return (false); // This is not a built-in command.
}

static void change_dir(char **argv) {
    if (!argv[1]) {
        return;
    }
    if (chdir(argv[1])) {
        printf("%s: No Such Directory\n", argv[1]);
    }
}

/*
 * do_bgfg - Execute the built-in bg and fg commands.
 *
 * Requires:
 *   "argv" is a bg or fg command followed by an argument that is either
 *    a valid PID or JID of a job.
 *
 * Effects:
 *   Sends a SIGCONT signal to the job and runs the job in the foreground if
 *   the command is "fg", or background if the command is "bg".
 */
static void do_bgfg(char **argv) {
    if (!argv[1]) {
        printf("No such job\n");
        return;
    }
    // Get the pid from argv[1] (can either be a jid or pid).
    pid_t pid = atoi(argv[1]);
    if (argv[1][0] == '%') {
        int jid = atoi(&argv[1][1]);
        JobP job = getjobjid(jobs, jid);
        if (!job) {
            printf("%s: No such job\n", argv[1]);
            return;
        }
        pid = job->pid;
    } else {
        pid = atoi(argv[1]);
        if (pid == 0) {
            printf("%s: argument must be a PID or %%jobid\n", argv[0]);
            return;
        }
    }

    JobP job = getjobpid(jobs, pid);
    if (!job) {
        printf("(%d): No such process\n", pid);
        return;
    }

    // If the command is bg, send a continue and put it in the background.
    if (strcmp(argv[0], "bg") == 0) {
        printf("[%d] (%d) %s", pid2jid(pid), pid, job->cmdline);
        Kill(pid, SIGCONT);
        getjobpid(jobs, pid)->state = BG;

    }
    // If the command is fg, send a continue and put it in the foreground.
    else if (strcmp(argv[0], "fg") == 0) {
        Kill(pid, SIGCONT);
        getjobpid(jobs, pid)->state = FG;
        tcsetpgrp(STDIN_FILENO, pid);
        waitfg(pid);
        tcsetpgrp(STDIN_FILENO, getpgrp());
    }
}

/*
 * waitfg - Block until process pid is no longer the foreground process.
 *
 * Requires:
 *   The given pid is a valid pid of a foreground process.
 *
 * Effects:
 *   Waits for the foreground process to complete while the process is still
 *   running in the foreground by blocking the shell.
 */
static void waitfg(pid_t pid) {
    // Get the current signal mask.
    sigset_t prev;
    Sigprocmask(-1, NULL, &prev);
    // Block while the job is still in the foreground.
    while (fgpid(jobs) == pid) {
        sigsuspend(&prev);
    }
}

/*
 * initpath - Perform all necessary initialization of the search path,
 *  which may be simply saving the path.
 *
 * Requires:
 *   "pathstr" is a valid search path.
 *
 * Effects:
 *   Creates an array of strings by splitting the search path, where each entry
 *   in the array is a directory in the search path, pathstr.
 */
static void initpath(const char *pathstr) {
    // count how many directories exist by the amount of colons that exist+1
    int colons = 0;
    for (unsigned int i = 0; pathstr && i < strlen(pathstr); ++i) {
        if (pathstr[i] == ':')
            ++colons;
    }
    // Number of paths is one more than the number of colons.
    pathDirs = Malloc(sizeof *pathDirs * (colons + 1));
    pathDirsLen = colons + 1;

    // Use strtok to split the string on colons and add to the dir list.
    char *tok = strtok((char *)pathstr, ":");
    for (int i = 0; i < pathDirsLen; ++i) {
        if (tok == NULL) {
            tok = ".";
        }
        pathDirs[i] = tok;
        tok = strtok(NULL, ":");
    }
}

/*
 * The signal handlers follow.
 */

/*
 * sigchld_handler - The kernel sends a SIGCHLD to the shell whenever
 *  a child job terminates (becomes a zombie), or stops because it
 *  received a SIGSTOP or SIGTSTP signal.  The handler reaps all
 *  available zombie children, but doesn't wait for any other
 *  currently running children to terminate.
 *
 * Requires:
 *   "signum" is SIGCHLD
 *
 * Effects:
 *   Reaps the zombie children by finding the child processes that have
 *   changed state, then deleting the job entry if the process exited
 *   normally. Prints message if the child process exited abnormally.
 */
static void sigchld_handler(int signum) {
    // Prevent an "unused parameter" warning.
    (void)signum;
    int olderrno = errno;

    // Declare information varialbes.
    pid_t pid;
    int status;

    // Check for tasks that need to be reaped or stopped but don't hang.
    while ((pid = waitpid(-1, &status, WUNTRACED | WNOHANG)) >
           0) { /* Reap a zombie child */
        // Just delete our reference to the job on normal exit.
        if (WIFEXITED(status)) {
            deletejob(jobs, pid); /* Delete the child from the job list */
        }
        // Print message on abnormal exit and delete reference to job.
        if (WIFSIGNALED(status)) {
            Sio_puts("Job [");
            Sio_putl(pid2jid(pid));
            Sio_puts("] (");
            Sio_putl(pid);
            Sio_puts(") terminated by signal SIG");
            Sio_puts(signame[WTERMSIG(status)]);
            Sio_puts("\n");
            deletejob(jobs, pid); /* Delete the child from the job list */
        }
        // Print message and update job status to stopped.
        if (WIFSTOPPED(status)) {
            Sio_puts("Job [");
            Sio_putl(pid2jid(pid));
            Sio_puts("] (");
            Sio_putl(pid);
            Sio_puts(") stopped by signal SIG");
            Sio_puts(signame[WSTOPSIG(status)]);
            Sio_puts("\n");
            JobP stoppedJob = getjobpid(jobs, pid);
            stoppedJob->state = ST;
        }
        status = 0;
    }
    errno = olderrno;
}

/*
 * sigint_handler - The kernel sends a SIGINT to the shell whenever the
 *  user types ctrl-c at the keyboard.  Catch it and send it along
 *  to the foreground job.
 *
 * Requires:
 *   "signum" is SIGINT
 *
 * Effects:
 *   Sends a SIGINT signal to every process in the foreground process group,
 *   which terminates the foreground process.
 */
static void sigint_handler(int signum) {

    // Prevent an "unused parameter" warning.
    (void)signum;
    // Kill all tasks in the forground group if it exists.
    int pid;
    if ((pid = -fgpid(jobs)) != 0) {
        Kill(pid, SIGINT);
    }
}

/*
 * sigtstp_handler - The kernel sends a SIGTSTP to the shell whenever
 *  the user types ctrl-z at the keyboard.  Catch it and suspend the
 *  foreground job by sending it a SIGTSTP.
 *
 * Requires:
 *   "signum" is SIGTSTP
 *
 * Effects:
 *   Sends a SIGTSTP signal to every process in the foreground process group,
 *   which suspepends the foreground job.
 */
static void sigtstp_handler(int signum) {

    // Prevent an "unused parameter" warning.
    (void)signum;
    int pid;
    // Stop all tasks in the forground group if it exists.
    if ((pid = -fgpid(jobs)) != 0) {
        Kill(pid, SIGTSTP);
    }
}

/*
 * sigquit_handler - The driver program can gracefully terminate the
 *  child shell by sending it a SIGQUIT signal.
 *
 * Requires:
 *   "signum" is SIGQUIT.
 *
 * Effects:
 *   Terminates the program.
 */
static void sigquit_handler(int signum) {

    // Prevent an "unused parameter" warning.
    (void)signum;
    _exit(1);
}

/*
 * This comment marks the end of the signal handlers.
 */

/*
 * The following helper routines manipulate the jobs list.
 */

/*
 * Requires:
 *   "job" points to a job structure.
 *
 * Effects:
 *   Clears the fields in the referenced job structure.
 */
static void clearjob(JobP job) {

    job->pid = 0;
    job->jid = 0;
    job->state = UNDEF;
    job->cmdline[0] = '\0';
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Initializes the jobs list to an empty state.
 */
static void initjobs(JobP jobs) {
    int i;

    for (i = 0; i < MAXJOBS; i++)
        clearjob(&jobs[i]);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Returns the largest allocated job ID.
 */
static int maxjid(JobP jobs) {
    int i, max = 0;

    for (i = 0; i < MAXJOBS; i++)
        if (jobs[i].jid > max)
            max = jobs[i].jid;
    return (max);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures, and "cmdline" is
 *   a properly terminated string.
 *
 * Effects:
 *   Tries to add a job to the jobs list.  Returns true if the job was added
 *   and false otherwise.
 */
static bool addjob(JobP jobs, pid_t pid, int state, const char *cmdline) {
    int i;

    if (pid < 1)
        return (false);
    for (i = 0; i < MAXJOBS; i++) {
        if (jobs[i].pid == 0) {
            jobs[i].pid = pid;
            jobs[i].state = state;
            jobs[i].jid = nextjid++;
            if (nextjid > MAXJOBS)
                nextjid = 1;
            // Remove the "volatile" qualifier using a cast.
            strcpy((char *)jobs[i].cmdline, cmdline);
            if (verbose) {
                printf("Added job [%d] %d %s\n", jobs[i].jid, (int)jobs[i].pid,
                       jobs[i].cmdline);
            }
            return (true);
        }
    }
    printf("Tried to create too many jobs\n");
    return (false);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Tries to delete the job from the jobs list whose PID equals "pid".
 *   Returns true if the job was deleted and false otherwise.
 */
static bool deletejob(JobP jobs, pid_t pid) {
    int i;

    if (pid < 1)
        return (false);
    for (i = 0; i < MAXJOBS; i++) {
        if (jobs[i].pid == pid) {
            clearjob(&jobs[i]);
            nextjid = maxjid(jobs) + 1;
            return (true);
        }
    }
    return (false);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Returns the PID of the current foreground job or 0 if no foreground
 *   job exists.
 */
static pid_t fgpid(JobP jobs) {
    int i;

    for (i = 0; i < MAXJOBS; i++)
        if (jobs[i].state == FG)
            return (jobs[i].pid);
    return (0);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Returns a pointer to the job structure with process ID "pid" or NULL if
 *   no such job exists.
 */
static JobP getjobpid(JobP jobs, pid_t pid) {
    int i;

    if (pid < 1)
        return (NULL);
    for (i = 0; i < MAXJOBS; i++)
        if (jobs[i].pid == pid)
            return (&jobs[i]);
    return (NULL);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Returns a pointer to the job structure with job ID "jid" or NULL if no
 *   such job exists.
 */
static JobP getjobjid(JobP jobs, int jid) {
    int i;

    if (jid < 1)
        return (NULL);
    for (i = 0; i < MAXJOBS; i++)
        if (jobs[i].jid == jid)
            return (&jobs[i]);
    return (NULL);
}

/*
 * Requires:
 *   Nothing.
 *
 * Effects:
 *   Returns the job ID for the job with process ID "pid" or 0 if no such
 *   job exists.
 */
static int pid2jid(pid_t pid) {
    int i;

    if (pid < 1)
        return (0);
    for (i = 0; i < MAXJOBS; i++)
        if (jobs[i].pid == pid)
            return (jobs[i].jid);
    return (0);
}

/*
 * Requires:
 *   "jobs" points to an array of MAXJOBS job structures.
 *
 * Effects:
 *   Prints the jobs list.
 */
static void listjobs(JobP jobs) {
    int i;

    for (i = 0; i < MAXJOBS; i++) {
        if (jobs[i].pid != 0) {
            printf("[%d] (%d) ", jobs[i].jid, (int)jobs[i].pid);
            switch (jobs[i].state) {
            case BG:
                printf("Running ");
                break;
            case FG:
                printf("Foreground ");
                break;
            case ST:
                printf("Stopped ");
                break;
            default:
                printf("listjobs: Internal error: "
                       "job[%d].state=%d ",
                       i, jobs[i].state);
            }
            printf("%s", jobs[i].cmdline);
        }
    }
}

/*
 * This comment marks the end of the jobs list helper routines.
 */

/*
 * Other helper routines follow.
 */

/*
 * Requires:
 *   Nothing.
 *
 * Effects:
 *   Prints a help message.
 */
static void usage(void) {

    printf("Usage: shell [-hvp]\n");
    printf("   -h   print this message\n");
    printf("   -v   print additional diagnostic information\n");
    printf("   -p   do not emit a command prompt\n");
    exit(1);
}

/*
 * Requires:
 *   "msg" is a properly terminated string.
 *
 * Effects:
 *   Prints a Unix-style error message and terminates the program.
 */
static void unix_error(const char *msg) {

    fprintf(stdout, "%s: %s\n", msg, strerror(errno));
    exit(1);
}

/*
 * Requires:
 *   "msg" is a properly terminated string.
 *
 * Effects:
 *   Prints "msg" and terminates the program.
 */
static void app_error(const char *msg) {

    fprintf(stdout, "%s\n", msg);
    exit(1);
}

/*
 * Requires:
 *   The character array "s" is sufficiently large to store the ASCII
 *   representation of the long "v" in base "b".
 *
 * Effects:
 *   Converts a long "v" to a base "b" string, storing that string in the
 *   character array "s" (from K&R).  This function can be safely called by
 *   a signal handler.
 */
static void sio_ltoa(long v, char s[], int b) {
    int c, i = 0;

    do
        s[i++] = (c = v % b) < 10 ? c + '0' : c - 10 + 'a';
    while ((v /= b) > 0);
    s[i] = '\0';
    sio_reverse(s);
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Reverses a string (from K&R).  This function can be safely called by a
 *   signal handler.
 */
static void sio_reverse(char s[]) {
    int c, i, j;

    for (i = 0, j = sio_strlen(s) - 1; i < j; i++, j--) {
        c = s[i];
        s[i] = s[j];
        s[j] = c;
    }
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Computes and returns the length of the string "s".  This function can be
 *   safely called by a signal handler.
 */
static size_t sio_strlen(const char s[]) {
    size_t i = 0;

    while (s[i] != '\0')
        i++;
    return (i);
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Prints the long "v" to stdout using only functions that can be safely
 *   called by a signal handler, and returns either the number of characters
 *   printed or -1 if the long could not be printed.
 */
static ssize_t sio_putl(long v) {
    char s[128];

    sio_ltoa(v, s, 10);
    return (sio_puts(s));
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Prints the string "s" to stdout using only functions that can be safely
 *   called by a signal handler, and returns either the number of characters
 *   printed or -1 if the string could not be printed.
 */
static ssize_t sio_puts(const char s[]) {

    return (write(STDOUT_FILENO, s, sio_strlen(s)));
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Prints the string "s" to stdout using only functions that can be safely
 *   called by a signal handler, and exits the program.
 */
static void sio_error(const char s[]) {

    sio_puts(s);
    _exit(1);
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Prints the long "v" to stdout using only functions that can be safely
 *   called by a signal handler.  Either returns the number of characters
 *   printed or exits if the long could not be printed.
 */
static ssize_t Sio_putl(long v) {
    ssize_t n;

    if ((n = sio_putl(v)) < 0)
        sio_error("Sio_putl error");
    return (n);
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Prints the string "s" to stdout using only functions that can be safely
 *   called by a signal handler.  Either returns the number of characters
 *   printed or exits if the string could not be printed.
 */
static ssize_t Sio_puts(const char s[]) {
    ssize_t n;

    if ((n = sio_puts(s)) < 0)
        sio_error("Sio_puts error");
    return (n);
}

/*
 * Requires:
 *   "s" is a properly terminated string.
 *
 * Effects:
 *   Prints the string "s" to stdout using only functions that can be safely
 *   called by a signal handler, and exits the program.
 */
static void Sio_error(const char s[]) { sio_error(s); }

// Prevent "unused function" and "unused variable" warnings.
static const void *dummy_ref[] = {Sio_error, Sio_putl,  addjob,    builtin_cmd,
                                  deletejob, do_bgfg,   dummy_ref, fgpid,
                                  getjobjid, getjobpid, listjobs,  parseline,
                                  pid2jid,   signame,   waitfg};
