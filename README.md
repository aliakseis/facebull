![Image](https://github.com/user-attachments/assets/ee2e6303-1a14-4fbe-805e-417b30854acf)

Facebull
========

Comprehensive reference for **facebull.cpp**, a standalone C++ program that computes a minimal‐cost sequence of machines to process a set of chemical compounds.

Overview
--------

facebull.cpp ingests a list of machines, each converting one compound into another at a given price.

It models each compound state as a bitmask and performs a best‐first search with custom memory pooling to find the cheapest sequence of machines that reduces all secondary compounds into the “body” state.

Building
--------

Compile with a C++11 (or later) compiler:

`   g++ -std=c++11 facebull.cpp -O2 -o facebull   `

Usage
-----

`   ./facebull input_file   `

*   input\_file: text file where each line defines a machine.
    

Input Format
------------

Each machine is specified as:

`M<number> <compound_from> <compound_to> <price>`   

*   number: unique machine identifier.
    
*   compound_from: name of input compound.
    
*   compound_to: name of output compound.
    
*   price: integer cost.
    

Lines not matching this pattern are ignored.

Core Data Structures
--------------------

### Plex

Lightweight linked‐block allocator, similar to MFC’s CPlex, that allocates a chunk of raw memory plus bookkeeping.

*   static Plex\* Create(Plex\*& head, size\_t count, size\_t elemSize)
    
*   void FreeDataChain()
    

### FixedAlloc

Fixed‐size allocator built on top of Plex, optimized for allocating many small objects (e.g., graph vertices).

*   FixedAlloc(UINT allocSize, UINT blockSize = 64)
    
*   void\* Alloc()
    
*   void Free(void\* p)
    
*   void FreeAll()
    

### Machine

Represents a single machine:

*   number Machine ID
*   price Twice the input cost (internal scaling)
*   compound1idx Index of input compound
*   compound1flg Bitmask flag for input compound
*   compound2idx Index of output compound
*   compound2flg Bitmask flag for output compound

Machines are bucketed into machinesByInIdx\[32\] based on their input‐flag hash.

### VertexKey

Key that encodes current compound state:

*   unsigned int body
    
*   unsigned int tails
    

Hashing uses Knuth’s multiplicative method on (body << 1) ^ tails.

### Vertex

Node in the search graph, pooled via FixedAlloc:

*   Pointers: next (hash chain), parent (path reconstruction)
    
*   Union:
    
    *   data\[2\]: best‐so‐far cost values
        
    *   projection: encodes visit state
        
*   Methods:
    
    *   bool visited()
        
    *   unsigned int estimate()
        
    *   Custom new/delete operators
        

Global pool: FixedAlloc Vertex::s\_alloc(sizeof(Vertex), 64).

### Priority & Destination

*   **Destination**: enum { notDef, tails, body, nowhere }
    
*   **Priority**: wraps a Vertex\*, its parent, and an encoded weight\_finishing for use in std::priority\_queue.
    
    *   Lower weight = higher priority
        
    *   LSB denotes finishing state
        

Algorithm Workflow
------------------

### Initialization

1.  Parse all machines from input.
    
2.  Map compound names to small integer indices via GetCompoundIndex().
    
3.  Track the cheapest price seen for each compound as forward and reverse estimates.
    
4.  Bucket machines by input‐flag hash.
    
5.  Compute global mask bitmask covering all compounds.
    
6.  Create an initial Vertex with state (body = mask, tails = highest‐bit) and push it onto the priority queue.
    

### Graph Search

*   While the queue is not empty:
    
    1.  Pop highest‐priority Priority.
        
    2.  If it’s a finishing state (body==1 && tails==1), output result.
        
    3.  Otherwise, expand the vertex via handleVertex or handleVertex.
        
    4.  Mark the vertex as visited.
        

### Branch-and-Bound & Heuristics

*   Maintain minFinishing, the best finishing cost seen so far.
    
*   Prune any extension whose estimate ≥ minFinishing.
    
*   Use estimates\[\] and estimates2\[\] as admissible heuristics to guide the search.
    
*   Detect dominated vertices via findSubstitute() and skip re‐expansion.
    

### Solution Reporting

Once the finishing state is dequeued:

1.  Print total cost (weight\_finishing/2).
    
2.  Reconstruct the path of machine IDs by walking back through parent pointers.
    
3.  Sort and print machine numbers in ascending order on one line.
    

Example
-------

Given machines.txt:

`   M1 A B 10  M2 B C 20  M3 C A 15   `

Run:

`   ./facebull machines.txt   `

Output:

`   45  1 2 3   `

_(This is illustrative; actual output depends on compound names and search ordering.)_

Extensibility & Notes
---------------------

*   Custom allocator reduces per‐vertex overhead and fragmentation.
    
*   Machine bucketing by single‐bit hashes accelerates neighbor lookup.
    
*   Heuristics ensure admissible pruning for optimality.
    
*   To add multi‐threading, protect global pools and hash table.
    
*   To support more compounds, increase machinesByInIdx buckets or adjust HASH\_BITS.
    

# Algorithm Overview

## Purpose

This project solves a **minimum-cost synthesis / transformation planning problem**.

Given a collection of machines

```
Machine:
    Input Compound
    Output Compound
    Cost
```

the program finds the **lowest-cost subset of machines** capable of transforming an initial compound into every required compound while satisfying dependency constraints.

Unlike a shortest-path problem, this is a **state-space optimization** problem because every decision changes the set of currently available compounds and affects future possibilities.

The implementation is essentially an optimized **A\*-like graph search** with aggressive pruning and several domain-specific heuristics.

---

# Problem Representation

Every machine represents a directed transformation

```
Compound A
      |
      | Machine
      V
Compound B
```

Each machine has

- machine identifier
- source compound
- destination compound
- execution price

Multiple machines may connect identical compounds.

Only the cheapest equivalent transformation is retained.

---

# Compound Encoding

Every compound is converted into an integer index.

```cpp
map<string,int> compoundsMapping;
```

Each compound becomes one bit inside a 32-bit mask.

Example

```
Compound A -> bit 0
Compound B -> bit 1
Compound C -> bit 2
...
```

This allows operations such as

```
contains compound?
```

to become

```cpp
mask & flag
```

instead of expensive map lookups.

---

# State Representation

A search state is represented by

```cpp
struct VertexKey
{
    unsigned int body;
    unsigned int tails;
};
```

These two bitmasks completely describe the current synthesis state.

---

## body

Represents compounds already placed inside the current synthesis body.

Example

```
body

A
B
C
```

encoded as

```
111000...
```

---

## tails

Represents compounds still exposed as unfinished outputs.

Think of them as open branches of the synthesis tree.

Example

```
body

A
|
+-- B
|
+-- C
```

B and C remain in tails.

---

## Why two masks?

A single bitmask is insufficient.

The algorithm must distinguish between

- compounds permanently integrated
- compounds that are temporary frontier nodes

which directly affects legal machine applications.

---

# Search Graph

Every unique `(body, tails)` pair is one graph vertex.

Applying one machine creates another vertex.

```
State 1

(body,tails)

        |
        | machine
        V

State 2
```

The search graph is generated lazily.

Only reachable states are created.

---

# Hash Table

Vertices are stored in

```cpp
hashTable[HASH_SIZE]
```

using

```cpp
VertexKey::hash()
```

which applies

```
Knuth multiplicative hashing

2654435769
```

This gives

- constant lookup
- no STL overhead
- cache-friendly access

Collision chains are handled by linked lists.

---

# Custom Memory Allocator

Millions of vertices may be generated.

Instead of

```
new
delete
```

for every node,

the project uses

```
FixedAlloc
```

which allocates memory in blocks.

```
Block

+---------------------+
|Vertex|
|Vertex|
|Vertex|
|Vertex|
+---------------------+
```

Advantages

- almost zero allocation overhead
- no heap fragmentation
- cache locality
- deterministic performance

Very similar to MFC's

```
CFixedAlloc
```

implemented over

```
CPlex
```

style memory blocks.

---

# Priority Queue Search

The algorithm maintains

```cpp
priority_queue<Priority>
```

Each entry contains

```
vertex
parent
estimated total cost
finished flag
```

Vertices are always expanded in order of the smallest estimated total cost.

This makes the algorithm equivalent to

```
Best-First Search
```

with A*-style evaluation.

---

# Cost Function

Each vertex stores

```cpp
data[0]
data[1]
```

representing two independent optimistic cost estimates.

The effective estimate is

```cpp
max(data0,data1)
```

Using the maximum guarantees admissibility for both optimization criteria.

---

# Lower Bound Heuristics

Two heuristic arrays are precomputed.

```cpp
estimates[]
```

Minimum incoming cost.

```
minimum cost producing compound X
```

---

```cpp
estimates2[]
```

Minimum outgoing cost.

```
minimum cost consuming compound X
```

These provide optimistic lower bounds.

Whenever a machine is applied,

the corresponding heuristic is subtracted

```cpp
data0 -= estimates[]
data1 -= estimates2[]
```

This keeps estimates tight.

---

# State Expansion

Expansion occurs in

```
handleVertex()
```

For every currently available compound

```
for every applicable machine
```

the algorithm

1. validates legality
2. constructs new state
3. computes new estimate
4. inserts state into priority queue

---

# Machine Legality

The most complicated routine is

```
getNextKey()
```

Its job is determining whether one machine may legally execute.

It verifies

- body constraints
- tail constraints
- dependency ordering
- recursive ancestry consistency

Only legal transformations generate successors.

---

# Recursive Dependency Checking

```
checkVertex()
```

performs recursive verification that

a partial synthesis can eventually reconnect to the main body.

Without this check,

the search would explore many impossible states.

This is one of the strongest pruning heuristics.

---

# Dominance Pruning

When a state already exists

```
same body
same tails
```

only the cheaper one survives.

```
existing estimate <= new estimate

↓

discard
```

This prevents exponential duplication.

---

# Substitute Pruning

```
findSubstitute()
```

implements an additional dominance rule.

If a more general state already achieves

an equal or better estimate,

the specialized state is ignored.

This substantially reduces search size.

---

# Recursive Bound Tightening

Whenever enough compounds have become fixed,

```
evaluateVertex()
```

recursively explores future possibilities

without inserting nodes into the global queue.

Purpose

```
improve upper bound
```

The resulting

```
minFinishing
```

becomes smaller,

allowing later branches to be pruned immediately.

---

# Upper Bound

Global variable

```cpp
minFinishing
```

stores

```
best complete solution found so far
```

Every new estimate satisfies

```
estimate >= minFinishing

↓

discard
```

Classic Branch-and-Bound pruning.

---

# Goal Detection

A finished solution is

```
body == 1
tails == 1
```

meaning

- all compounds resolved
- no unfinished branches remain

When reached,

the search terminates.

---

# Path Reconstruction

Each vertex stores

```
parent
```

After completion,

```
reportSolution()
```

walks backwards

```
Goal

↓

Parent

↓

Parent

↓

Start
```

recovering every machine used.

The final machine identifiers are sorted before printing.

---

# Complexity

Worst case

```
Exponential
```

because the problem is fundamentally a combinatorial state-space search.

Practical complexity is dramatically reduced through

- admissible heuristics
- A*-style ordering
- dominance pruning
- substitute pruning
- recursive feasibility checking
- branch-and-bound
- duplicate elimination
- custom memory allocator

allowing surprisingly large problem instances to be solved efficiently.

---

# Algorithm Summary

The overall algorithm is

```
Read input
        │
        ▼
Compress compounds into bitmasks
        │
        ▼
Remove dominated machines
        │
        ▼
Compute heuristic lower bounds
        │
        ▼
Create initial search state
        │
        ▼
Priority Queue (Best-First / A*)
        │
        ▼
Expand legal machines
        │
        ▼
Generate successor states
        │
        ▼
Prune duplicates
        │
        ▼
Prune impossible states
        │
        ▼
Prune using upper bound
        │
        ▼
Reach complete synthesis
        │
        ▼
Reconstruct optimal machine sequence
```

---

# Technical Characteristics

- **Search paradigm:** Heuristic Best-First Search (A\*-like)
- **Optimization:** Branch-and-Bound
- **State encoding:** Dual bitmask (`body`, `tails`)
- **Graph construction:** Lazy (on-demand)
- **Duplicate detection:** Custom hash table
- **Memory management:** Block allocator (`FixedAlloc`)
- **Heuristics:** Dual admissible lower-bound estimates
- **Pruning:** Dominance, substitute-state elimination, recursive feasibility, upper-bound pruning
- **Complexity:** Exponential worst case, heavily reduced in practice by layered heuristics
