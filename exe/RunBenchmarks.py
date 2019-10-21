#!/usr/bin/env python3

import os
import sys
import signal
from time import monotonic as timer
from subprocess import Popen, PIPE, TimeoutExpired

# Run command, catching exceptions, timing the execution, and recording output
def runWithTimeout(cmd, timeout):

    # Start timer and open subprocess
    start = timer()
    with Popen(cmd, shell=True, stdout=PIPE, stderr=PIPE, preexec_fn=os.setsid) as process:

        # Run command with timeout
        try:
            out, err = process.communicate(timeout=timeout)
            if err:
                cvc4_error = "CVC4 interrupted by SIGTERM."
                err = [e for e in err.decode("utf-8").split('\n') if (e != cvc4_error and e != '')]

            output = "ERROR\n{}".format("\n".join(err)) if err else out.decode("utf-8").split("\n")[-2]
            elapsed = timer() - start

        # Command times out
        except TimeoutExpired:
            elapsed = timer() - start
            os.killpg(process.pid, signal.SIGINT)
            output = "timeout"

    return elapsed, output

def main():

    # Arg validation
    if len(sys.argv) != 3:
        exit("usage: ./RunBenchmarks.py outfile timeout")
    try:
        timeout = int(sys.argv[2])
    except:
        exit("error: timeout must be an integer number of seconds")
    if os.path.exists(sys.argv[1]):
        exit("error: specified output file already exists")

    # Helper
    def zipInts(s, n):
        import itertools
        return list(zip([s]*n, itertools.count(1)))

    # Collect filenames
    filenames = zipInts("strings", 10) + zipInts("lia", 19) + zipInts("slia", 9)
    benchmarks = ["benchmarks/synthesis/{}_{}".format(logic, n) for logic, n in filenames]

    # Run each benchmark, storing the output in a file
    print("\ncheck file '{}' to see test results\n".format(sys.argv[1]))
    with open(sys.argv[1], 'w') as outfile:

        # Iterate over directories and filenames of benchmarks
        for f in benchmarks:

            # Run LIVS, catching exceptions and timing the execution
            print("{}...".format(f))
            cmd = "cabal new-run livs -- --code-file={}/fullGrammar.js".format(f)
            elapsed, output = runWithTimeout(cmd, timeout)

            # Write time and output to file
            elapsed_str = "{0:.3f}s".format(elapsed).ljust(7)
            outfile.write("{}".format(f).ljust(31) + " : {} : {}\n".format(elapsed_str, output))
            outfile.flush()

    # Reminder
    print("\ncheck file '{}' to see test results\n".format(sys.argv[1]))

# Entry point
if __name__ == "__main__":
    main()
