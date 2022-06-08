# abagraph

**abagraph** is a Prolog implementation of a graph-based dispute derivation algorithm for assumption-based argumentation (ABA).  The algorithm and associated theory is described in the paper:

   [Argument Graphs and Assumption-Based Argumentation](http://robertcraven.org/papers/2016_arggraphs.pdf).  
   Robert Craven and Francesca Toni. Artificial Intelligence 233, 2016, 1–59.

## Requirements

**abagraph** has been tested on Ubuntu Linux, with SICStus Prolog 4.2+.

## Usage

Basic usage can be described as follows.

- After cloning the repository, `cd` to the `src/` directory.
- Load abagraph by `sicstus -l abagraph.pl`.
- ABA framework files are placed in `frameworks/`.  (This contains some examples.)
- To load a file from the `frameworks/` directory—such as `a12.pl`—do `loadf(a12).`.
- To find a derivation for, say, the sentence `y1`, do `derive(y1, X).`.

## Options

Current values of options are displayed by:

    ?- options.

To print the derivation steps during a call to `derive/2`, use:

    ?- set_verbose.

To hide the derivation steps (default), use:

    ?- set_quiet.

To output the solutions, as found, to a `.dot` file for visualization with graphviz, use:

    ?- set_print.

To set not to print, use:

    ?- set_noprint.

To use AB-dispute derivations, do:

    ?- set_ab.

To use GB-dispute derivations, do:

    ?- set_gb.

To change strategies, use:

    ?- set_strategies(StratList).

StratList has the form: [T,OJ,PS,OS,PR].

- turn choice (T):

        p - proponent priority [DEFAULT]
        o - opponent priority
        s - smallest number of sentences/justification-pairs first

- opponent justification set choice (OJ):

        n - newest
        o - oldest
        s - smallest set of pending (unmarked) sentences [DEFAULT]
        l - largest set of pending (unmarked) sentences
        lmb - lowest maximum 'branching' coefficient

- sentence choice (proponent PS, and opponent OS):

        n - newest
        o - oldest
        e - eager (choose an assumption if possible)
        p - patient (choose non-assumption if poss.) [DEFAULT (prop and opp)]
        be - sentence with smallest 'branching' coefficient (eager)
        bp - sentence with smallest 'branching' coefficient (patient)

- proponent rule choice (PR):

        s - smallest rule body first
        l1 - look-ahead, 1-step [DEFAULT]
