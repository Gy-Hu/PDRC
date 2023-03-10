# PDRC
Reproduce of [A Supervisory Control Algorithm Based on Property-Directed Reachability](https://arxiv.org/pdf/1711.06501.pdf)

* Initialize and download the submodules that you are interested in:

> git submodule init <list-of-submodules>

> git submodule update

Instructions to replicate results from HVC2017 paper "A Supervisory Control Algorithm Based on Property-Directed Reachability"

Written by Jonatan Kilhamn


We assume you want to run the PDRC algorithm on one of the Extended Dining Philosophers problems. Regrettably, I don't have a script to automatically re-run exactly those results included in the paper.

1. Build tip. The repository https://github.com/JonatanKilhamn/supermini is a deep copy of https://github.com/niklasso/supermini, and shares the same build instructions. These are available in the README file present in both of those repositories. Build and make tip. I will use "tip" to denote the command used to run the executable [...]/build/tip/tip.

2. Modify the file PhilosophersParsed.hs so that the constants "nbrPhils" and "nbrSteps" correspond to your desired parameters. E.g. to run the experiment denoted EDP5_100, set nbrPhils = 5 and nbrSteps = 100.

3. Open GHCi and run:

```
:l PhilosophersParsed.hs
PhilosophersParsed.main
```

This will write the file phils5_100 to the Examples folder. The problem is parsed from the file EDP5_100.wmod, which has the problem in the .wmod format.

4. Run tip on the problem. When compiling tip from the JonatanKilhamn/supermini repository, the PDRC behaviour is the only available setting (the original tip behaviour, with no synthesis, is not available through e.g. a parameter setting). In a non-ghci terminal, go to the top-level directory of this repository (JonatanKilhamn/tipcheck) and run:

>  tip Examples/phils5_100

or using tip in other locations:

> ~/coding_env/PDR_based_SC/supermini/build/tip/tip Examples/phils5_1000

This will print some results, including the header "Resources used"; the figure given for "CPU Time" is the one reported in the paper. The command will also write to output.txt.

5. In order to inspect the synthesised controller, open GHCi again, and run:

```
:l TransitionSystemIO
TransitionSystemIO.main
```

However, this depends on modifications in the source file to run the correct file. Inside TransitionSystemIO.main, there are three lines of which two are commented-out:

> s <- philSynch -- EDP  
> -- s <- cmtSynch -- CMT  
> -- s <- pmeSynch -- PME

The one corresponding to the problem class of interested should be uncommented. Furthermore, the corresponding file (PhilosophersParsed.hs, CatMouseParsed.hs, PMEParsed.hs, respectively) should be set up exactly the same as it was when its respective "main" function generated the file that was used as input to tip.

The output from TransitionSystemIO.main is in the internal Synchronisation format, which specifies a number of synchronised automata and their shared events and variables. This step takes some time, but this is because PDRC operates on the monolithic circuit version of the synchronised system, and this presentation requires decomposition into each automaton. Compared to the claims in the paper, this is an unnecessary step, which is why we implemented it in the less-efficient Haskell over C++, and why we didn't include it in the runtime measurements.
