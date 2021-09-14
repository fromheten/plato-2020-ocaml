#!/usr/bin/env python3

import sys
import os
import json
import subprocess

test_dir = sys.argv.pop()

tests_files = os.listdir(test_dir)

def read_file(file_path):
    text_file = open(file_path, "r")
    data = text_file.read()
    text_file.close()
    return data

def read_files(tests_files):
    tests = []
    for file in tests_files:
        tests.append(read_file(test_dir + file))
    return tests

tests = list(map(json.loads, read_files(tests_files)))

def produce_test_result(test):
    if "expression" in test:
        command = "echo \"(Log (string " + test["expression"] + "))" + "\" | dune exec bin/platoc.exe -- --stdin"
    elif "command" in test:
        command = test["command"]
    else:
        raise ValueError("Test lacks command or expression: ", json.dumpts(test, indent = 1))

    process = subprocess.run(
        [command],
        capture_output=True,
        shell=True)
    return {
        "command": command,
        "stdout": process.stdout.decode('utf8'),
        "stderr": process.stderr.decode('utf8'),
        "exitCode": process.returncode
    }

def main():
    results = list(map(produce_test_result, tests))
    for (test, result) in zip(tests, results):
        if test["stdout"].strip() == result["stdout"].strip():
            print("ok")
        else:
            print("error!")
            print("expected: ", json.dumps(test, indent = 1))
            print("actual:   ", json.dumps(result, indent = 1))
main()
