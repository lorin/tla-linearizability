# Reading the Herlihy & Wing Linearizability paper with TLA+

The [Herlihy & Wing 1990](http://dx.doi.org/10.1145/78969.78972) paper
introduced *linearizability* as a correctness condition for reasoning about the
behavior of concurrent data structures.

## Figure 1

Figure one shows several possible histories for a concurrently accessed queue.
Figures 1(a) and 1(c) are linearizable, and Figures 1(b) and 1(d) are not.

![Figure 1](fig1.png)

Each interval represents an operation. There are two types of operations: {E,
D} for enqueue and dequeue. There are two processes: {A, B}. There are three
items that can be added to the queue: {x, y, z}.


## Definition of linearizability

From p469:

A history H is linearizable if it can be extended (by appending zero or more
response events) to some history H’ such that:

* L1: complete(H’) is equivalent to some legal sequential history S, and
* L2: <<sub>H</sub> ⊆ <<sub>S</sub>



