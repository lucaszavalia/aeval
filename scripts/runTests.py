#! /bin/python3

import os
import sys
import time
import subprocess
import re
import csv
from datetime import datetime

def displayHelp():
    print("Script runs aeval on s_part and t_part benchmarks located in bench/tasks")
    print("Usage = ./runTests.py [--help] [--debug] [--skol]")
    print("Arguments:")
    print("--help Display this help message and exit")
    print("--skol Produce skolems")
    print("--debug Perform sanity checks (run with debug level 1)")
    

def parseArgs():
    args = []
    read = 1
    if "--help" in sys.argv:
        displayHelp()
        exit(0)
    if "--skol" in sys.argv:
        args.append("--skol")
        read += 1
    if "--debug" in sys.argv:
        args += ["--debug",  "1"]
        read += 1
    if len(sys.argv) != read:
        print("Could not parse arguments, try --help")
        exit(1)
    return args

def main():
    inputArgs = parseArgs()

    suffixlen = len("s_part.smt2")

    projDir = os.path.abspath( os.path.dirname( __file__ ) ) + "/.."
    path_to_tests = projDir + "/bench/tasks"
    tests_set = set()
    for file in os.listdir(path_to_tests):
        testName = path_to_tests + '/' + file[:-suffixlen]
        tests_set.add(testName)

    resTable = [["test", "stdout", "time"]]

    numTests = len(tests_set)
    i = 1
    for t in tests_set:
        print(f"Test {i}/{numTests}: ", t)
        result = [t]
        args = [projDir + "/build/tools/aeval/aeval"] + inputArgs + [t + "s_part.smt2", t + "t_part.smt2"]
        t1 = time.time()
        try:
            output = subprocess.run(args, timeout=300, stdout=subprocess.PIPE)
            output = output.stdout
            t2 = time.time()
            if output:
                output = output.decode("utf-8").strip()
                result.append(output)
            else:
                result.append("emptyStdout")
            result.append(t2-t1)
        except Exception as e:
            result.append(e)
        i += 1
        resTable.append(result)

    now = datetime.now()
    current_time = now.strftime("%d.%m.%Y-%H:%M:%S")
    outName = "results_" + current_time + ".csv"
    with open(outName, 'w') as file:
        writer = csv.writer(file)
        writer.writerows(resTable)

if __name__ == "__main__":
    main()