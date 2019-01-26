#!/usr/bin/python
"""
Creates a JSON file containing a set of hashed features for each identified function in a valid M7700 BIN
"""

__all__ = ['function']
__version__ = '0.1.0'
__author__ = 'Greg'

import sys
import argparse
import json
import jsongraph
import pprint
import r2pipe
import os
import logging
import re
import subprocess
import networkx as nx
import pygraphviz
import md5
import pprint
import collections
from collections import OrderedDict
from networkx.drawing import nx_agraph
from subprocess import check_call
from datetime import datetime
from itertools import cycle

# all function data types

class instruction:
    # smallest data type for function class, the individual instructions
    # field contains: base addr (where in memory this is)
    #               : opcode
    #               : all parameters used by instruction

    def __init__(self, _base_addr, opcode):
        self._base_addr = hex(_base_addr)
        _ = opcode.split()
        self._opcode = _[0]
        self._params = _[1:]

    def __str__(self):
        if self._params:
            ret = "OP: {}\nParams: {}\n".format(
                self._opcode, self._params)
        else:
            ret = "OP: {}\n".format(self._opcode)
        return ret

class block:
    # a set of instructions that are isolated from other sub-instructions behind a _jump condition or a branch
    # field contains: base addr (where in memory these instructions begin)
    #               : _instruction_block - list of all instruction objects stored within a block
    #               : _fail - pointer to next block specified by "failed" _jump conditions
    #               : _jump - pointer to next block specified by
    #                       successful _jump conditions, or unconditional jumps
    #               : _parents - list containing all member blocks that call this block
    ######## Note: Jump and Fail pointers are set by the CFG class constructor

    _parents = None
    _fail    = None
    _jump    = None

    def __init__(self, _base_addr, seq_json):
        self._base_addr = hex(_base_addr)
        self._instruction_block = OrderedDict()
        self._parents = list()
        for entry in seq_json:
            self._instruction_block[entry[u'offset']] = instruction(
                entry[u'offset'], entry[u'opcode'])

    # simple helper function to return the nth item in the instruction dict
    # normally this dict is sorted by the address of the instruction, this
    # helper allows you to circumvent that
    def _get_instruction(self, index):
        iter = cycle(self._instruction_block.items())
        ret = None
        if index >= len(self._instruction_block):
            raise IndexError(index, "Index {} out of bounds.".format(index))
        for _ in range (-1, index):
           ret = next(iter) 
        if ret is None:
            raise IndexError(index, "Index {} out of bounds.".format(index))
        
        return ret[1]

    # Returns a hash of the instructions
    # takes entire instruction list for a block,
    # hashes it with the md5 hash algorithm,
    # and returns. Does nothing else.
    def _get_hashed_list(self):
        ret = ur""
        for _ in self._instruction_block.values():
            ret = ret + ur"{}".format(_._opcode)

        return [(md5.new(ret).hexdigest())]

    # Creates a list of all instructions for this block
    # tokenized into n-gram blocks. Returns that list.
    # Filter ignores the BRA instructions, leaving them out of gram creation.
    # Default program gram length: 2
    # If the grams provided exceed the length for a list, only items matching that length will
    # be added to the index. 
    def _n_gram(self, n_grams, filter, filter_list, get_consts):
        ret = list()
        opcodes = []
        start = 0
        # generate a filtered list of opcodes given the provided filter
        for key in self._instruction_block.keys():
            if (filter and self._instruction_block[key]._opcode in filter_list):
                continue
            else:
                opcodes.append(self._instruction_block[key]._opcode)
                # if get_consts:
                #     for param in self._instruction_block[key]._params:
                #         if "#" in param:
                #             opcodes.append(param)

        # split that list into N-gram opcodes                       
        for _ in opcodes:
            gram = ur""
            for i in range(start, n_grams + start):
                if start + n_grams < len(opcodes):
                    gram = ur"{}{}".format(gram, 
                                        opcodes[i])
                else: 
                    break
            start += 1
            # append gram to list if it's not an empty value
            if gram is not ur"":
                ret.append(gram)

        return ret

    # Returns a list of the edges of this block, tokenized into two-gram sections
    # first items are the edges for the parent caller blocks and the first instruction
    # last items are the final instructions of this block and its callees
    # Filter ignores the BRA instructions, returning the previous instruction instead
    def _edge_list(self, filter, filter_list):
        ret = list()
        current = self._instruction_block.get(int(self._base_addr, 16))

        for parent in self._parents:
            parent_last_instruction = parent._get_instruction(len(parent._instruction_block) - 1)._opcode
            if (filter and parent_last_instruction in filter_list):
                _ = 1
                parent_last_instruction = None
                while parent_last_instruction is None:
                    # attempt to find a valid instruction that is not in the filter list
                    if parent._get_instruction(len(parent._instruction_block) - _) not in filter_list:
                        parent_last_instruction = parent._get_instruction(len(parent._instruction_block) - _)._opcode
                    _ += 1
                    if _ >= len(parent._instruction_block):
                        break
            if parent_last_instruction is not None:
                ret.append(ur"{}{}".format(parent_last_instruction, 
                    current._opcode
                ))

        # add in child edges
        if self._jump is not None:

            next_instr = self._jump._instruction_block[int(self._jump._base_addr, 16)]._opcode
            if (filter and next_instr in filter_list):
                _ = 0
                next_instr = None
                while next_instr is None and _ < len(self._jump._instruction_block):
                    # attempt to find a valid instruction that is not in the filter list
                    if self._jump._get_instruction(_)._opcode not in filter_list:
                        next_instr = self._jump._get_instruction(_)._opcode
                    _ += 1
                    # if _ > len(self._jump._instruction_block):
                    #     break
            if next_instr is not None:
                ret.append(ur"{}{}".format(current._opcode, next_instr))
            
        if self._fail is not None:
            next_instr = self._fail._instruction_block[int(self._fail._base_addr, 16)]._opcode
            if (filter and next_instr in filter_list):
                _ = 0
                next_instr = None
                while next_instr is None and _ < len(self._fail._instruction_block):
                    # attempt to find a valid instruction that is not in the filter list
                    if self._fail._get_instruction(_)._opcode not in filter_list:
                        next_instr = self._fail._get_instruction(_)._opcode
                    _ += 1
                    # if _ > len(self._fail._instruction_block):
                    #     break
            if next_instr is not None:
                ret.append(ur"{}{}".format(current._opcode, next_instr))
            
        return ret

    # Main feature generation algorithm, parses args passed at run-time 
    # and generates a complete feature vector using those params
    # Full list of args can be located down by the main method
    def _get_features(self, args):
        ret = []
        ret.extend(self._n_gram(args.ngrams, args.ignore, ["BRA"], True)) # placeholder values for now

        if args.edges:
            ret.extend(self._edge_list(args.ignore, ["BRA"]))

        # TODO: add additional command line args to parse
        # - bottleneck/subgraph detection and parsing
        # - additional features

        return ret

    def _print_inst(self):
        for instruction in self._instruction_block.itervalues():
            print(instruction)

    def __str__(self):
        ret = "Base_addr: 0x{:04x}\n".format(self._base_addr)
        if self._fail:
            ret += "\tFail: 0x{:04x}\n".format(self._fail._base_addr)
        if self._jump:
            ret += "\tJump: 0x{:04x}\n".format(self._jump._base_addr)
        return ret

class CFG:
    # a tree of blocks that compose a complete function
    # field contains: base addr (where in memory these blocks begin)
    #               : first - pointer to the first block in memory
    #               : json - json representation of the CFG
    # constructor is responsible for populating the block data-types given a JSON representation from R2

    _first = None

    def __init__(self, json):
        
        if json:
            self._json = json[0]
        else:
            self._json = ""
        if u'offset' in self._json: 
            # JSON objects from R2 use offset as their base address, seek here and begin parsing
            self._base_addr = hex(self._json[u'offset'])
            if u'blocks' in self._json:
                # Populate block objects using the 'blocks' field in R2's JSON
                blocks = self._json[u'blocks']
                dict_block = {}

                # pass addr of first block, ops of first block, and pointers of first block
                #self._first = block(blocks[000][u'offset'], blocks[000][u'ops'])

                # create a dictionary of all blocks using this information
                for blk in blocks:
                    dict_block[blk[u'offset']] = [block(
                        blk[u'offset'],
                        blk[u'ops']), blk]
                # match up all the block objects to their corresponding _jump, _fail addresses
                for _, pair in dict_block.items():
                    block_obj = pair[0]
                    block_json = pair[1]
                    if u'fail' in block_json:
                        try:
                            block_obj._fail = dict_block[block_json[u'fail']][0]
                            block_obj._fail._parents.append(block_obj)
                        except KeyError:
                            # KeyErrors result if no valid jumps exist, can be safely ignored
                            continue

                    if u'jump' in block_json:
                        try:
                            block_obj._jump = dict_block[block_json[u'jump']][0]
                            block_obj._jump._parents.append(block_obj)
                        except KeyError:
                            # KeyErrors result if no valid jumps exist, can be safely ignored
                            continue
                # save first block, keeping entire tree in mem
                self._first = dict_block[blocks[000][u'offset']][0] 

    def __str__(self):
        ret = ""
        node = self._first
        while node is not None:
            ret += "{}\n".format(node)
            if node._fail:
                node = node._fail
            else:
                node = node._jump
        return ret

    # Bottleneck feature searching
    # attempts to find "bottlenecks" - single conditional jumps with multiple parents
    # default depth - 2
    def _bottlenecks(self, args, visited, depth=2):
        # Very WIP
        # TODO: find bottlenecks, analyze subgraphs, create feature vector out of that
        # TODO: add in an optional depth detection
        
        ret = list() # feature list, containing grams back
        
        # first - identify all bottlenecks within a function, store in list
        bottlenecks = self._get_bottlenecks(self._first, visited)
        # then  - get features from bottlenecks of depth N back
        for bottleneck in bottlenecks:
            ret.extend(self._bottleneck_seek_back(bottleneck, depth, args, visited))
     #   print "wew"
        return ret

    # recursively traverses function CFG and gathers a list of all bottlenecks
    def _get_bottlenecks(self, current, visited):

        ret = list()
        if current is None or current in visited:  
            # Ignore blocks we've already resited, base condition
            return ret  # if block has 4 or more _parents, define as a bottleneck

        if (len(current._parents) >= 4):
            ret.append(current)

        visited.append(current)

        if current._fail is not None:
            ret.extend(self._get_bottlenecks(current._fail, visited))

        if current._jump is not None:
            ret.extend(self._get_bottlenecks(current._jump, visited))

        return ret

    # recursively seeks back N blocks from bottleneck
    # returns a list of all N-gram features including this block and any prior
    def _bottleneck_seek_back(self, bottleneck, depth, args, visited):

        ret = list()
        current = bottleneck

        if depth == 0 or bottleneck is None:  # base condition
            return ret

        # visited.append(bottleneck)
        # current = bottleneck

        # add block's current features to ret
        ret.extend(current._get_features(args))

        # add in edge instruction for each parent
        for parent in current._parents:

            parent_op = parent._get_instruction(len(parent._instruction_block) - 1)._opcode
            if "BRA" in parent_op:

                try:
                    parent_op = parent._get_instruction(len(parent._instruction_block) - 2)._opcode
                    self_op = current._get_instruction(0)._opcode
                    ret.append(ur"{}{}".format(self_op, 
                    parent_op))
                except IndexError:
                    continue # ignore index errors, just don't add the instruction pair as the block was a single BRA instruction

            subgraph = self._bottleneck_seek_back(parent, depth - 1, args, visited)
            if subgraph:
                ret.extend(subgraph)

        return ret

class function:
    # overall function datatype, containing the CFG
    # field contains: base addr (where in memory these instructions begin)
    #               : json - json rep of data structure from R2
    #               : dot - dot rep of data structure from R2
    #               : children - functions called by this function
    #               : _parents  - functions that call this function

    _unique_id = -1 # dummied out for now, trying to figure out a unique way to label matching functions
    _base_addr = 0x0  # address of the function
    _json = ""      # json representation of function pointed to
    _dot = ""       # dot representation of function pointed to
    
    def __init__(self, _base_addr, cfg):
        self._base_addr = hex(_base_addr)
        self._children = {}
        self._parents = {}
        self._cfg = cfg

    def __str__(self):
        ret = "0x{:04x}\n".format(self._base_addr)
        for child in self._children.values():
            ret += "\t{}".format(child)
        return ret

    # adds a child to list of functions that this function calls
    def _push_child(self, func):
        self._children[func._base_addr] = func

    # Master-function to grab features from block sub-classes
    # Returns a complete list of features for this entire function
    def _get_features(self, args):
        ret = []
        if self._cfg._first is None:
            return

        ret += self._get_features_helper(self._cfg._first, [], args)

        if args.bottlenecks:
            ret += self._cfg._bottlenecks(args, [], args.depth)

        return ret

    # recursive helper for _get_features
    def _get_features_helper(self, block, __visited, args):
        ret = []
        if block is None or block in __visited:  
            # Ignore blocks we've already resited, base condition
            return ret
        # get feature list from block
        ret.extend(block._get_features(args))
        __visited.append(block)

        # grab features from block's children
        if block._jump is not None:
            ret.extend(self._get_features_helper(block._jump, __visited, args))
        if block._fail is not None:
            ret.extend(self._get_features_helper(block._fail, __visited, args))
        return ret

# locates the reset vector address from a valid M7700 binary
# using a currently open radare2 session
# used to find initial location for mem searches
def _get_rst(r2):
    # seek to the address for the reset vector (const for all of our binaries)
    r2.cmd("s 0xfffe")
    logging.debug("R2 Command used: 's 0xfffe'")

    rst_addr = str(r2.cmd("px0"))  # print last two bytes of rst vector
    logging.debug("R2 Command used: 'px0'")

    rst = 0x0

    if rst_addr:
        # flip endianness of last two bytes (start off little, need to be big)
        rst = int("{}{}".format(rst_addr[2:4], rst_addr[:2]), 16)
        logging.debug("rst vector address found at: 0x{:04x}".format(rst))
    else:
        logging.debug("ERR - reset vector search failed")

    return rst

# Helper function for recursive_parse_func
# grabs all child function calls from a function analysis in R2
# our arch only uses JSR for function calls, so this works for now
def _get_children(child_str):
    # this regex searches for any functions starting with JSR
    p = ur"JSR.*[^$](0x[0-9a-fA-F]{4})"  
    children = re.findall(p, child_str)
    p1 = ur"JSR.*fcn.0000([0-9a-fA-F]{4})"
    ch2 = re.findall(p1, child_str)
    children.extend(ch2)  

    int_children = list()
    for child in children:
        try:
            int_children.append(int(child, 16))
        except TypeError:
            print (child)
    del children
    return int_children

# helper function for recursive parse func
# popluates CFG data structure for each function, given a valid func_json
def _populate_cfg(addr, func_json):
    # nice solution found at https://grimhacker.com/2016/04/24/loading-dirty-json-with-python/
    # helps handle "dirty" JSON input
    regex_replace = [(r"([ \{,:\[])(u)?'([^']+)'", r'\1"\3"'), (r" False([, \}\]])", r' false\1'), (r" True([, \}\]])", r' true\1')]
    for r, s in regex_replace:
        func_json = re.sub(r, s, func_json)

    json_obj = json.loads(unicode(func_json, errors='ignore'),
                          strict=False, object_pairs_hook=collections.OrderedDict)
    cfg = CFG(json_obj)
    return cfg

# recursively parses a binary, given address
# function parsing is as follows in terms of radare2 instructions
#   - 0x{addr} -  seek to address
#   - aa       -  analyze function to end of basic block (analyze all) - more consistent than running aaa at start of binary
#   - sf.      -  seek to beginning of any already-identified functions (limits repeats)
#   - pdf      - print disassembly of function (For parsing to get children)
#   - agj      - print analyzed json data structure
#  for each child found in pdf (a child defined as a JSR to another unique function address), this method recurses
#  found children addresses are added to a "_visited" global data structure, and are not recursed if _visited multiple times
#       instead, _visited children just have their list of _parents updated whenever something else finds them
def _recursive_parse_func(addr, visited, r2):

    r2.cmd("0x{:04x}".format(addr))     # seek to address
    logging.debug("R2 Command used: '0x{:04x}'".format(addr))

    r2.cmd("aa")                        # analyze all
    logging.debug("R2 Command used: aa")

    r2.cmd("sf.")                       # seek to beginning of func
    addr = int(r2.cmd("s"), 16)

    child_str = r2.cmd("pdf")          # grab list of func params
    logging.debug("R2 Command used: 'pdf'")

    children = _get_children(child_str)  # pull list of children from func list

    if addr in visited.keys():
        # attempt to see if we've traversed down that function branch before (ie, defined it and its children)
        func = visited[addr]
        return func
    else:
        # iterate over all of this function's children, and recursively travel down each branch
        cfg = _populate_cfg(addr, r2.cmd("agj")) # create a CFG for each function from R2's JSON
        logging.debug("R2 Command used: 'agj'")
        func = function(addr, cfg)
        visited[addr] = func

    for child_addr in children:
        if child_addr in visited.keys():  # we don't need to recursively parse a function's children if it's already parsed
            visited[child_addr]._parents[addr] = func  # store reference to parent in child object
            func._push_child(visited[child_addr]) # store the child in the base func object
        else:
            visited[child_addr] = _recursive_parse_func(child_addr, visited, r2) # store reference to parent in child object
            visited[child_addr]._parents[addr] = func # store the child in the base func object
            func._push_child(visited[child_addr])
    return func

# simple helper function to split a function string into a list and return any found addresses in that list
def _func_parse_str(func_str):
    ret = []
    fs = func_str.splitlines()
    for line in fs:
        try:
            addr = int(line[:10], 16) # first 10 spots in line are the hex address
        except TypeError:
            continue
        if addr and addr >= 36864: # sanity check to make sure we're not including addresses from MMIO/RAM
            ret.append(addr)
    return ret

# secondary function search method - attempts to identify all functions within radare, 
# then passes each to the recursive parse
# not strictly "linear" because it uses our recursive method, 
# but it does attempt to brute-force non found functions instead of just recursing from the reset vector
# catches a few extra functions that a normal recurse from the RST vector does not
def _linear_parse_func(func, visited, r2):
    func_list = []
    r2.cmd("aaa")
    func_str = r2.cmd('afl')  # pull a complete list of functions
    logging.debug("R2 Command used: 'afl'")
    r2.cmd("af-")
    l = _func_parse_str(func_str)
    for addr in l:
        if addr not in visited.keys():
            # attempt to manually parse each address with recursion
            func_list.append(_recursive_parse_func(addr, visited, r2))
    return func_list

# Creates an array of hashed features representing the instruction grams of each block within a function
def _grab_features(func, visited, args):

    func_dict = {}
    if func in visited:
        return func_dict

    sig = func._get_features(args)
    func_dict[ur"{}".format(func._base_addr)] = ur"{}".format(sig)
    visited.append(func)

    for child in func._children.values():
        func_dict.update(_grab_features(child, visited, args))

    return func_dict

# helper to attempt to locate the start of our M7700 binaries
# very sloppy, but our start methods across each binary 
# all start with the same instruction
def _get_start(infile):
    addr = 0x0000

    try:
        # load infile into R2 - error if not found
        r2 = r2pipe.open(infile, ["-2"])
        r2.cmd("e asm.arch=m7700")
        addr = 0
        val = r2.cmd("/c CMP al #0xf0")  # attempt to find the initial address
        if val is "":
            # attempt to find the initial address (if the flags aren't set properly yet)
            val = r2.cmd("/c CMP ax #0xf0f0")
        vals = val.split()

        try:
            r2.cmd("s {}".format(vals[0]))
        except IndexError:
            None
        addr = int(r2.cmd("s"), 16)
        r2.quit()
    except IOError:
        print "Could not locate start of binary"
    return addr

# this method is responsible for
# - automatically parsing the rom file for functions
# - generating a graph from said functions
# - loading that graph into memory
def _parse_rom(infile, args):

    visited = {}
    print("Loading '{}' into R2...".format(infile))
    start = _get_start(infile)
    
    try:
        # load infile into R2 - error if not found
        r2 = r2pipe.open(infile, ["-2"])
    except IOError:
        print "R2 Couldn't open file {}\n".format(infile)
    if r2:                             # assert the R2 file opened correctly
        r2.cmd('e asm.arch=m7700')     # set the architecture env variable
        logging.debug("R2 Command used: 'e asm.arch=m7700'")

        # check that arch loaded properly
        logging.info("R2 loaded arch: " + r2.cmd('e asm.arch'))

        # first, attempt to generate a full graph from the reset vector
        rst = _get_rst(r2)
        logging.info("Binary reset vector located at 0x{:04x}".format(rst))

        if (rst < start):  # some RST vectors are located below the test fcn
            start = rst

        r2.cmd("e anal.limits=true")
        r2.cmd("e anal.from=0x{:04x}".format(start))
        # ffd0 onward are just vectors and should be reserved, not functions
        r2.cmd("e anal.to=0xffd0")
        logging.debug("e anal.hasnext: {}".format(r2.cmd("e anal.hasnext")))
        logging.debug("e anal.from: {}".format(r2.cmd("e anal.from")))
        logging.debug("e anal.to: {}".format(r2.cmd("e anal.to")))

        # build func from a recursive function parse
        func_list = []
        func = None
        try:
            # visited struct is passed by reference, and should be populated in both cases
            func = _recursive_parse_func(rst, visited, r2)
            func_list.append(func)

        except ValueError as valerr:
            print valerr
            print ("Recursive disassembly parse for ROM failed:")

        # then attempt to find additional functoins that were missed in the initial sweep with a recursive search
        try:
            func_list.extend(_linear_parse_func(func, visited, r2))
        except ValueError as valerr:
            print valerr
            print("Linear disassembly parse for ROM failed.")
        feature_dictionary = {}

        for funcs in func_list:
            # pass the functions, an empty list (visited), and our option flags to the feature parser
            feature_dictionary.update(_grab_features(funcs, [], args))

        # functions.append(func_list)
        
    else:
        print("Error parsing R2")
    r2.quit()
    print("Quitting R2...")
    return feature_dictionary

# helper function to check if a string is a hex string or not
def _isHex(num):
    try:
        int(num, 16)
        return True
    except ValueError:
        return False

# Program Flag options
# Default options - func_finder.py filename ...
# Filename can be multiple options, each subsequent filename loads in an additional ROM
# additional options:
#   -o: outfile  - specify the name for the output JSON file
#   -n: grams    - specify the number of grams to break the software for an ECU into
#   -i: ignore   - ignore certain instructions
#   -e: edges    - add in edge processing to graph
#   -b: bot.necks- attempt bottleneck subgraph processing instead of full graph processing
#   -d: depth    - set the depth variable of the bottleneck to specify how far back to go
def main():
    # set up the parser first
    # default parser args - filename, opens file for JSON parsing
    # can also output JSON file as a .DOT file, or pull in a ROM and call R2
    parser = argparse.ArgumentParser(
        description='Import and process M7700 JSON Graph files.')

    parser.add_argument('filename', metavar='filename', nargs='+', type=str, default=sys.stdin,
                        help='M7700 ROM file for parsing')

    parser.add_argument('-o', '--outfile', metavar='outfile', default="file.json", type=str,
                        help='Specify Filename')
                        
    parser.add_argument('-n', '--ngrams', metavar='ngrams', default=2, type=int,
                   help='Specify number of grams to break feature vectors into')

    parser.add_argument('-i', '--ignore', metavar='ignore', default=True, type=bool,
                   help='Ignore BRA instructions')
    
    parser.add_argument('-e', '--edges', metavar='edges', default=False, type=bool,
                   help='Process edges')

    parser.add_argument('-b', '--bottlenecks', metavar='bottlenecks', default=False, type=bool,
                   help='Search for and process bottleneck subgraphs')

    parser.add_argument('-d', '--depth', metavar='depth', default=2, type=int,
                   help='Change bottleneck subgraph depth')

    logging.basicConfig(filename='log_filename.txt', level=logging.DEBUG)

    args = parser.parse_args()
    outfile = args.outfile
    jsons = {}

    for infile in args.filename:
        if infile is not None:
            print("Opening file: {}".format(infile))

        feature_dict = _parse_rom(infile, args)
        jsons[infile] = feature_dict 

    with open(outfile, 'w') as out:
        json.dump(jsons, out, indent=4, sort_keys=True)

    out.close()

# start
if __name__ == '__main__':
    main()