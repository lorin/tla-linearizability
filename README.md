# Reading the Herlihy & Wing Linearizability paper with TLA+

The [Herlihy & Wing 1990](http://dx.doi.org/10.1145/78969.78972) paper entitled
*Linearizability: a correctness condition for concurrent objects*
introduced *linearizability* as a correctness condition for reasoning about the
behavior of concurrent data structures.

There are several linearizable data stores with TLA+ specifications:

* Lamport's book [Specifying Systems][specifying-systems] uses an example of a linearizable memory in
Section 5.3.
* The [Raft][raft] Consensus algorithm supports linearizable semantics and has a
  [TLA+ specification][raft-tla].
* [Azure Cosmos DB][cosmosdb] supports a consistency model with linearizable reads and has 
  [high-level TLA+ specifications][cosmosdb-tla].
  

[specifying-systems]: https://lamport.azurewebsites.net/tla/book.html
[raft]: https://raft.github.io/
[raft-tla]: https://github.com/ongardie/raft.tla
[cosmosdb]: http://cosmosdb.com/
[cosmosdb-tla]: https://github.com/Azure/azure-cosmos-tla

However, none of these models use the definition of linearizability outlined in
the original paper by Herlihy & Wing.

As an exercise in becoming more familiar with both the definition of
linearizability and with modeling in TLA+, I translated the definiton of
linearizability from the original paper into a TLA+ model.

**Note: This is a work-in-progress**.

## Figure 1

Figure one shows several possible histories for a concurrently accessed queue.
Figures 1(a) and 1(c) are linearizable, and Figures 1(b) and 1(d) are not.

![Figure 1](fig1.png)

Each interval represents an operation. There are two types of operations: {E,
D} for enqueue and dequeue. There are three processes: {A, B, C}. There are three
items that can be added to the queue: {x, y, z}.


## Definition of linearizability

The definitions are on p469 of the paper.

### Linearizable object

A *linearizable object* is one whose concurrent histories are linearizable with
respect to some sequential specification.

### Linearizable history

A history H is linearizable if it can be extended (by appending zero or more
response events) to some history H’ such that:

* L1: complete(H’) is equivalent to some legal sequential history S, and
* L2: <<sub>H</sub> ⊆ <<sub>S</sub>



