Haskell Operads

This is a modified version of the Gröbner bases for operads software created by Willem Heijltjes under the supervision of Vladimir Dotsenko. This version includes parallel computation, the triangle lemma, and memoisation in the generation of the normal forms. Additionally, some new options are outlined below.

1) Adjusting chunk sizes (number of instructions per chunk) during parallel computation (chunk),
2) Printing the number of normal forms at each stage of the computation of a Gröbner basis (stageCount), 
3) Only printing the leading terms of newly added stable pairs (leading),
4) Saving new stable pairs in a custom file (save).

Instructions:

To install the program, you may clone the GitHub directory by either clicking the green "Code" button on the upper right corner of the main page of the repository, or by entering "git clone https://github.com/MedetJuma/haskellOperads.git" in the terminal.

Once installed, install ghcup by following the instructions (https://www.haskell.org/ghcup/install/). You may also need to install cabal (https://www.haskell.org/cabal/).

Then, modify the "input.txt" file by specifying the theory. An example theory currently in the repository's input file is the mock-Lie operad, which is an unsigned shuffle operad. You may also adjust other options, such as arity limit, measure, or count limit.

To run the program, use the following command:

cabal run OperadsHaskell -- +RTS -N -A64m

The -N flag can be adjusted by appending a number of processors. For example, -N30 would mean that the process will use at most 30 processors. The -A64m flag specifies the size of the garbage collector, which is set to 64 MB.
