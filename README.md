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
    

License
-------

Distributed under the MIT License.
