#!/usr/bin/env python3

import sys
import subprocess
import time

def main():

    # Arg validation
    if len(sys.argv) != 3:
        print("usage: ./RunBenchmarks.py outfile timeout")
        return 1
    try:
        timeout = int(sys.argv[2])
    except:
        print("error: timeout must be an integer number of seconds")
        return 1

    # Helper
    def zipInts(s, n):
        import itertools
        return list(zip([s]*n, itertools.count(1)))

    # Collect filenames
    filenames = zipInts("lia", 18) + zipInts("slia", 8) + zipInts("strings", 10)
    benchmarks = ["benchmarks/synthesis/{}_{}".format(logic, n) for logic, n in filenames]

    # Run each benchmark, storing the output in a file
    print("\ncheck {} to see test results\n".format(sys.argv[1]))
    with open(sys.argv[1], 'w') as outfile:

        # Iterate over directories and filenames of benchmarks
        for f in benchmarks:

            # Print the current file
            print("{}...".format(f))
            stats = {}

            # Run LIVS, catching exceptions and timing the execution
            start = time.time()
            try:

                # Collect output from command
                cmd = ["runhaskell", "exe/Main.hs", "--code-file={}/fullGrammar.js".format(f)]
                res = subprocess.check_output(cmd, stderr=subprocess.STDOUT, timeout=timeout)
                output = res.decode("utf-8").split("\n")[:-2]
                end = time.time()

            # LIVS throws an exception
            except subprocess.CalledProcessError as exc:
                end = time.time()
                output = "ERROR {}".format(exc.output.decode("utf-8"))

            # LIVS times out
            except subprocess.TimeoutExpired as exc:
                end = time.time()
                output = "timeout"

            # Write time and output to file
            time_str = "{0:.3f}s".format(end - start).ljust(7)
            outfile.write("{}".format(f).ljust(31) + " : {} : {}\n".format(time_str, output))
            outfile.flush()

    # Reminder
    print("\ncheck {} to see test results\n".format(sys.argv[1]))

# Entry point
if __name__ == "__main__":
    main()
