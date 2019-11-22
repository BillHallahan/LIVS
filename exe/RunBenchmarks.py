#!/usr/bin/env python3

import os
import sys
import signal
from time import monotonic as timer
from subprocess import Popen, PIPE, TimeoutExpired
import itertools
import csv

# Run command, catching exceptions, timing the execution, and recording output
def runWithTimeout(cmd, timeout):

    # Start timer and open subprocess
    start = timer()
    with Popen(cmd, shell=True, stdout=PIPE, stderr=PIPE, preexec_fn=os.setsid) as process:

        # Run command with timeout
        try:
            out, err = process.communicate(timeout=timeout)
            if err:
                ignore = [
                    "CVC4 interrupted by SIGTERM.",
                    "CVC4 suffered a segfault.",
                    "Looks like a NULL pointer was dereferenced.",
                    ""
                ]
                err = [e for e in err.decode("utf-8").split('\n') if not (e in ignore or e.startswith("Offending "))]

            output = out.decode("utf-8") if not err else "ERROR\n{}".format("\n".join(err))
            elapsed = timer() - start

        # Command times out
        except TimeoutExpired:
            elapsed = timer() - start
            os.killpg(process.pid, signal.SIGINT)
            output = "timeout\n"

    return elapsed, output

def main():

    # Arg validation
    if len(sys.argv) != 3:
        exit("usage: ./RunBenchmarks.py MODE timeout")
    try:
        timeout = int(sys.argv[2])
    except:
        exit("error: timeout must be an integer number of seconds")
    mode = sys.argv[1]
    if mode != "mturk" and mode != "gen":
        exit("error: MODE must be one of 'mturk' or 'gen'")

    # Constants
    logics = ["lia", "strings", "slia"]
    primitives = 6
    generations = 20
    files_per_gen = 10

    # Benchmark locations
    if mode == "gen":

        logic_dirs = ["benchmarks/generated/{}".format(logic) for logic in logics]
        dirs = [["{}/{}".format(lld, str(n)) for lld, n in list(zip([ld]*generations, itertools.count(0)))] for ld in logic_dirs]
        benchmarks = []
        for sublist in dirs:
            for d in sublist:
                for n in range(files_per_gen):
                    benchmarks.append("{}/{}.js".format(d, str(n)))

    else:

        mturk_names = ["00401.js", "26903.js", "4697.js",  "85808.js", "00975.js", "34491.js", "69645.js",
                       "87350.js", "36976.js", "80286.js", "92431.js", "25948.js", "41127.js", "84873.js"]
        benchmarks = ["benchmarks/mturk/{}".format(f) for f in mturk_names]

    # Run each benchmark, storing the output in a file
    results = []
    with open("dump_results_{}.txt".format(mode), 'w') as txtfile:

        # Iterate over directories and filenames of benchmarks
        for f in benchmarks:

            # Run LIVS, catching exceptions and timing the execution
            print("{}...".format(f))
            cmd = "cabal new-run livs -- --code-file={}".format(f)
            elapsed, output = runWithTimeout(cmd, timeout)
            output_lines = output.split('\n')

            # Write to dump file
            elapsed_str = "{0:.3f}s".format(elapsed).ljust(7)
            txtfile.write("{}".format(f).ljust(31) + " : {} : {}\n".format(elapsed_str, output_lines[-2]))
            txtfile.flush()

            # If CVC4 erred, throw out result
            if output_lines[0] == 'ERROR':
                print("erred on {}".format(f))
                print(output_lines)
                continue

            # Write to results
            ignore = ["CVC4 interrupted by SIGTERM.", "Up to date"]
            cvc4_time = sum([float(line[:-1]) for line in output_lines[:-2] if line not in ignore])
            stats = {
                'logic': "slia" if "slia" in f else "lia" if "lia" in f else "strings" if "strings" in f else "mturk",
                'components': int(f[-4]) + primitives if mode == 'gen' else 2,
                'solved': 0 if output_lines[0] == "timeout" else 1,
                'cvc4_time': cvc4_time,
                'total_time': elapsed
            }
            results.append(stats)

        txtfile.write(str(results))

    if mode == 'mturk':

        fieldnames = ['logic', 'components', 'cvc4_time', 'total_time', 'solved']
        with open('mturk_results.csv', 'w') as csvfile:
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            writer.writeheader()
            for row in results:
                writer.writerow(row)

    else:

        # Parse results into tables
        tbls = {}
        for logic in logics:
            tbls[logic] = []
        for logic, components in itertools.product(logics, list(range(primitives, primitives + files_per_gen))):

            # filter results
            filtered = [r for r in results if r['logic'] == logic and r['components'] == components]
            solved = len([r for r in filtered if r['solved']])

            # create single row of a final table from results
            tbls[logic].append({
                'components': components,
                'avg_cvc4_time': sum([r['cvc4_time'] for r in filtered if r['solved']]) / solved,
                'avg_total_time': sum([r['total_time'] for r in filtered if r['solved']]) / solved,
                'timeouts': len(filtered) - solved
            })

        # Write one csv file summarizing results for each logic
        fieldnames = ['components', 'avg_cvc4_time', 'avg_total_time', 'timeouts']
        for logic, tbl in tbls.items():
            with open('{}_results.csv'.format(logic), 'w') as csvfile:
                writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
                writer.writeheader()
                for row in tbl:
                    writer.writerow(row)

# Entry point
if __name__ == "__main__":
    main()
