#!/bin/bash

tlc='/usr/bin/java -cp /usr/local/bin/tla2tools-v1.8.jar tlc2.TLC -noGenerateSpecTE'$
tlc -workers 8 -dumpTrace json trace.json -deadlock AbstractRaft
python3 logtree.py && cp log_tree.html /Users/william.schultz/Documents/projects/will62794.github.io/_includes
