#!/usr/bin/env python3

import os
import sys
import signal
from time import monotonic as timer
from subprocess import Popen, PIPE, TimeoutExpired
from random import randint, choice

# List of currently used function ids (cannot repeat ids, to avoid namespace conflicts)
ids = []

# Class for a callable JavaScript function
class JSFunction:

    # Initialize new JS function
    # name: string
    # id: string
    # in: [int] -> list of input types
    # out: int -> output type (0 for integer type, 1 for string type)
    # body: string -> JS function body
    def __init__(self, id, in_type, out_type, body, name="f"):
        self.name = name
        self.id = id
        self.in = in_type
        self.out = out_type
        self.body = body

    # String representation of this function
    def __repr__(self):
        return "function f{}({})\n{{\n\t{}\n}}".format(self.id, makeArgs(len(self.in)), self.body)

    # Type-checks if this function can take the given list of functions as arguments
    # fs: [JSFunction] -> list of functions to be used as input arguments
    def composable(self, fs):
        return all([self_in == f.out for self_in, f in list(zip(self.in, fs))])

    # Return a new function which is the composition of this function with the given functions as args
    # fs: [JSFunction] -> list of functions to be used as input arguments
    def composeWith(self, fs):

        # Check if this is a valid composition
        if not self.composable(fs):
            return None

        # Random id for the new function
        new_id = 0
        while new_id not in ids:
            new_id = str(randint(0, 1000))
        ids.append(new_id)

        # Input and output types for the new function
        new_in = flatten([f.in for f in fs])
        new_out = self.out

        # Function body
        args = makeArgs(len(new_in))
        sub_function_calls = ["{}{}({})".format(f.name, f.id, ", ".join([args.pop(0) for args in f.in])) for f in fs]
        new_body = "return {}{}({});".format(self.name, self.id, ", ".join(sub_function_calls))

        # Return new function
        return JSFunction(new_id, new_in, new_out, new_body)

    # call function and get results
    # fs: [JSFunction] -> all functions that need to be defined in the file in order to call the target
    # target: JSFunction -> the function to call
    # args: [int OR string] -> arguments to call the function with
    def call(self, fs, target, args):
        # write string rep of all functions to tmpfile.js
        # write call to target funtion to tmpfile.js
        # execute 'node tmpfile.js'
        # collect output
        # remove tmpfile.js
        pass

# Give a list of arguments in the form x_i
# n: int -> number of args
def makeArgs(n):
    return ["x_" + str(i) for i in range(n)]

# flatten a list of lists (concatmap)
# list_of_lists: [[a]] -> list to flatten
def flatten(list_of_lists):
    return [item for sublist in list_of_lists for item in sublist]

# generate a new function which is a composition of some members of all_funcs
# all_funcs: [JSFunction] -> list of options to compose from
def generateFunction(all_funcs):
    # randomly choose some function
    # randomly choose some other functions which need not be unique but must not be the first chosen function
    # attemt to compose them together
    # if successful, and the new function isn't one we've generated before, return it
    # if unsuccessful, repeat
    pass

# load a collection of primitive JS functions from a .js file
# file: string -> .js file to load from
def loadPrimitives(filename):

    # read lines into list
    with open(filename) as f:
        contents = f.readlines()

    # iterate over lines looking for primitives
    primitives = []
    for i in range(len(contents)):

        # look for type annotations
        line = contents[i]
        if line.startswith("// @type: "):

            # get info about the function
            type = [int(t) for t in line[10:]]
            fname = contents[i+1].split(' ')[1]
            fname = fname[:fname.index('(')]
            body = contents[i+2].strip()

            # create and append new function
            new_func = JSFunction('', type[:-1], type[-1], body, name=fname)
            primitives.append(new_func)

    # return full list when finished
    return primitives

# Randomly generate JS functions that are compositions of a list of provided primitives,
# and format generated functions as synthesis problems over the primitives by fuzzing each function
# and writing the inputs and outputs as pbe examples, along with the primitive definitions, to a file
def main():

    # Arg validation
    if len(sys.argv) != 3:
        exit("usage: ./Generator.py primtives.js n")

    filename = sys.argv[1]
    if not os.path.exists(filename):
        exit("error: specified primitives file does not exist")

    try:
        n = int(sys.argv[2])
    except:
        exit("error: argument must be an integer")

    # Generate a list of n functions composed from the provided primitives
    primitives = loadPrimitives(filename)
    all_funcs = list(primitives)
    for _ in range(n - len(primitives)):
        new_func = generateFunction(all_funcs)
        all_funcs.append(new_func)

    # Split over call tree and make synthesis problems
    # For each function above a certain depth
    # Get all of its dependencies
    # Write dependency definitions to a file
    # Fuzz the function with call()
    # Write pbe examples to file
    pass

# Entry point
if __name__ == "__main__":
    main()
