#include <stdio.h>
#include <assert.h>

#include <cstddef>
#include <iostream>
#include <queue>
#include <map>
#include <string>
#include <vector>
#include <algorithm>

using std::cerr;
using std::cout;
using std::map;
using std::string;
using std::vector;


struct Plex     // Similar to MFC CPlex
    // warning variable length structure
{
    Plex* pNext;
    int dwReserved[1];    // align on 8 byte boundary

    void* data() { return this + 1; }

    // like 'calloc' but no zero fill
    // may throw memory exceptions
    static Plex* Create(Plex*& pHead, size_t nMax, size_t cbElement)
    {
        assert(nMax > 0 && cbElement > 0);
        Plex* p = (Plex*) operator new(sizeof(Plex) + nMax * cbElement);
        // may throw exception
        p->pNext = pHead;
        pHead = p;  // change head (adds in reverse order for simplicity)
        return p;
    }

    void FreeDataChain()       // free this one and links
    {
        Plex* p = this;
        while (p != 0)
        {
            void* bytes = p;
            p = p->pNext;
            operator delete(bytes);
        }
    }
};

typedef unsigned int UINT;

class FixedAlloc    // Similar to MFC CFixedAlloc
{
    // Constructors
public:
    FixedAlloc(UINT nAllocSize, UINT nBlockSize = 64);

    // Attributes
    UINT GetAllocSize() { return m_nAllocSize; }

    // Operations
public:
    void* Alloc();  // return a chunk of memory of nAllocSize
    void Free(void* p); // free chunk of memory returned from Alloc
    void FreeAll(); // free everything allocated from this allocator

    // Implementation
public:
    ~FixedAlloc();

protected:
    struct CNode
    {
        CNode* pNext;	// only valid when in free list
    };

    UINT m_nAllocSize;	// size of each block from Alloc
    UINT m_nBlockSize;	// number of blocks to get at a time
    Plex* m_pBlocks;	// linked list of blocks (is nBlocks*nAllocSize)
    CNode* m_pNodeFree;	// first free node (0 if no free nodes)
};

FixedAlloc::FixedAlloc(UINT nAllocSize, UINT nBlockSize)
{
    assert(nAllocSize >= sizeof(CNode));
    assert(nBlockSize > 1);

    if (nAllocSize < sizeof(CNode))
        nAllocSize = sizeof(CNode);
    if (nBlockSize <= 1)
        nBlockSize = 64;

    m_nAllocSize = nAllocSize;
    m_nBlockSize = nBlockSize;
    m_pNodeFree = 0;
    m_pBlocks = 0;
}

FixedAlloc::~FixedAlloc()
{
    FreeAll();
}

void FixedAlloc::FreeAll()
{
    m_pBlocks->FreeDataChain();
    m_pBlocks = 0;
    m_pNodeFree = 0;
}

void* FixedAlloc::Alloc()
{
    if (m_pNodeFree == 0)
    {
        // add another block
        Plex* pNewBlock = Plex::Create(m_pBlocks, m_nBlockSize, m_nAllocSize);

        // chain them into free list
        // free in reverse order to make it easier to debug
        char* pData = (char*)pNewBlock->data() + m_nAllocSize * (m_nBlockSize - 1);
        for (int i = m_nBlockSize; i > 0; i--, pData -= m_nAllocSize)
        {
            CNode* pNode = (CNode*)pData;
            pNode->pNext = m_pNodeFree;
            m_pNodeFree = pNode;
        }
    }
    assert(m_pNodeFree != 0);  // we must have something

    // remove the first available node from the free list
    void* pNode = m_pNodeFree;
    m_pNodeFree = m_pNodeFree->pNext;
    return pNode;
}

void FixedAlloc::Free(void* p)
{
    if (p != 0)
    {
        // simply return the node to the free list
        CNode* pNode = (CNode*)p;
        pNode->pNext = m_pNodeFree;
        m_pNodeFree = pNode;
    }
}



struct Machine
{
    unsigned int number;
    unsigned int price;
    unsigned int compound1idx;
    unsigned int compound1flg;
    unsigned int compound2idx;
    unsigned int compound2flg;
};

inline bool operator < (const Machine& m1, const Machine& m2)
{
    return m1.price < m2.price;
}

map<string, int> compoundsMapping;

int compoundIndex = 0;

int GetCompoundIndex(const char* number)
{
    int result;

    map<string, int>::iterator lb = compoundsMapping.lower_bound(number);
    if (lb != compoundsMapping.end() && !compoundsMapping.key_comp()(number, lb->first))
        result = lb->second;
    else
    {
        result = compoundIndex++;
        typedef map<string, int>::value_type MVT;
        compoundsMapping.insert(lb, MVT(number, result));
    }

    return result;
}

vector<Machine> machinesByInIdx[32];

enum { HASH_BITS = 21, HASH_SIZE = 1 << HASH_BITS };


struct VertexKey
{
    unsigned int body;
    unsigned int tails;

    int hash() const
    {
        return (unsigned int)(((body << 1) ^ tails) * 2654435769U) >> (32 - HASH_BITS);
    }
};

inline bool operator == (const VertexKey& left, const VertexKey& right)
{
    return left.body == right.body && left.tails == right.tails;
}


struct Vertex
{
    Vertex* next;
    VertexKey key;
    union
    {
        unsigned int data[2];
        const Vertex* parent;
        std::size_t projection;
    };

    bool visited() { return (projection & 1u) == 0; }
    unsigned int estimate() { return data[data[1] > data[0]]; }

    bool empty() const { return key.body == 0 && key.tails == 0; }

    void* operator new(size_t size)
    {
        assert(size == s_alloc.GetAllocSize());
        return s_alloc.Alloc();
    }
    void* operator new(size_t, void* p){ return p; }
    void operator delete(void* p) { s_alloc.Free(p); }

protected:
    static FixedAlloc s_alloc;
};

FixedAlloc Vertex::s_alloc(sizeof(Vertex), 64);

Vertex hashTable[HASH_SIZE];

unsigned int estimates[32];
unsigned int estimates2[32];

class Priority
{
    friend bool operator < (const Priority& left, const Priority& right);
public:
    Vertex* vertex;
    Vertex* parent;
    unsigned int weight() { return weight_finishing >> 1; }
    bool finishing() { return !(weight_finishing & 1u); }
    Priority(Vertex* vertex_, Vertex* parent_, unsigned int weight_, bool finishing_)
        : vertex(vertex_), parent(parent_), weight_finishing((weight_ << 1) + !finishing_) {}
private:
    unsigned int weight_finishing;
};

inline bool operator < (const Priority& left, const Priority& right)
{
    return left.weight_finishing > right.weight_finishing;
}



Vertex* findItem(const VertexKey& newKey, int idx)
{
    Vertex* vertex = hashTable + idx;
    if (!vertex->empty())
    {
        do
        {
            if (vertex->key == newKey)
            {
                return vertex;
            }
            vertex = vertex->next;
        } while (vertex != 0);
    }

    return 0;
}

bool findSubstitute(const VertexKey& key, unsigned int estimate)
{
    if (key.tails > 1)
    {
        VertexKey newKey = { key.body & ~(key.tails - 1), 1 };

        Vertex* v = findItem(newKey, newKey.hash());
        if (v != 0)
        {
            if (v->estimate() <= estimate)
            {
                return true;
            }
        }
    }

    return false;
}

unsigned int mask;

unsigned int minFinishing = 0xFFFFFFFF;

typedef std::priority_queue<Priority> PriorityQueue;

enum Destination { notDef, tails, body, nowhere };

template<bool inBody>
bool getNextKey(const Machine& machine, const VertexKey& key,
    const Vertex* parent, VertexKey& newKey, Destination& destination)
{
    const bool inTails = !inBody;

    const bool outBody = !(key.body & machine.compound2flg);
    if (inBody && outBody)
    {
        return false;
    }
    const bool outTails = !!(key.tails & machine.compound2flg);
    if (inBody && outTails)
    {
        return false;
    }
    if (inTails && outTails && machine.compound2flg != 1)
    {
        return false;
    }
    if (inTails && outBody && machine.compound2flg != 1)
    {
        if ((key.tails & 1) == 0)
        {
            return false;
        }

        if (parent)
        {
            bool wasOutBody = false;
            // tricky
            for (const Vertex* v = parent; v != 0; v = v->parent)
            {
                if (1 == v->key.tails)
                {
                    wasOutBody = !(v->key.body & machine.compound2flg);
                    break;
                }
            }
            if (!wasOutBody)
            {
                return false;
            }
        }
    }

    if (inBody && (key.tails & 1) != 0 && parent != 0)
    {
        const Vertex* v = parent;
        const Vertex* parent = v->parent;

        if ((v->key.tails & 1) != 0)
        {
            do
            {
                if (parent->key.tails == 1 && v->key.tails > 1)
                {
                    if (v->key.tails < (machine.compound2flg | 1)
                        && !(parent->key.body & machine.compound1flg))
                    {
                        return false;
                    }
                    break;
                }

                v = parent;
                parent = v->parent;
            } while (parent != 0);
        }
    }

    assert(!(inBody && inTails));
    assert(!(outBody && outTails));

    newKey = key;
    if (inBody)
    {
        assert(!outBody && !outTails);
        newKey.tails |= machine.compound2flg;
    }
    else
    {
        newKey.body &= ~machine.compound1flg;
        newKey.tails &= ~machine.compound1flg;
        if (!outBody)
        {
            newKey.tails |= machine.compound2flg;
        }
    }

    assert(0 == (~newKey.body & newKey.tails));

    destination = outBody ? body : (outTails ? tails : nowhere);

    return true;
}


bool checkVertex(const VertexKey& key, const Vertex* parent)
{
    const unsigned int flag = key.tails & ~1;

    const int idx = ((unsigned int)(flag * 0x077CB531U)) >> 27;

    for (vector<Machine>::iterator it(machinesByInIdx[idx].begin()), itEnd(machinesByInIdx[idx].end()); it != itEnd; ++it)
    {
        const Machine& machine = *it;
        VertexKey newKey;
        Destination destination;
        if (!getNextKey<false>(machine, key, parent, newKey, destination))
        {
            continue;
        }

        if (newKey.tails == 1) // in body
        {
            return true;
        }

        Vertex link;
        link.key = key;
        link.parent = parent;
        if (checkVertex(newKey, &link))
        {
            return true;
        }
    }

    return false;
}


template<bool inBody>
bool evaluateVertex(const VertexKey& key, const unsigned int data[2], const Vertex* parent)
{
    bool result = false;

    const bool inTails = !inBody;
    unsigned int inFlags = inBody ? (mask ^ key.body) : (key.tails & ~1);
    while (inFlags)
    {
        const unsigned int buffer = inFlags & (inFlags - 1);
        const unsigned int flag = inFlags - buffer;
        inFlags = buffer;

        const int idx = ((unsigned int)(flag * 0x077CB531U)) >> 27;

        for (vector<Machine>::iterator it(machinesByInIdx[idx].begin()), itEnd(machinesByInIdx[idx].end())
            ; it != itEnd
            ; ++it)
        {
            const Machine& machine = *it;
            VertexKey newKey;
            Destination destination;
            if (!getNextKey<inBody>(machine, key, parent, newKey, destination))
            {
                continue;
            }


            unsigned int data0 = data[0] + machine.price;
            if (inTails)
            {
                data0 -= estimates[machine.compound1idx];
            }
            unsigned int data1 = data[1] + machine.price;
            if (nowhere == destination)
            {
                data1 -= estimates2[machine.compound2idx];
            }

            const bool finishing = 1 == newKey.body && 1 == newKey.tails;

            const unsigned int estimate = std::max(data0, data1);
            if (estimate >= minFinishing)
            {
                continue;
            }

            if (finishing)
            {
                if (minFinishing > estimate)
                {
                    result = true;
                    minFinishing = estimate;
                }
                continue;
            }


            unsigned int newData[2];
            newData[0] = data0;
            newData[1] = data1;

            Vertex link;
            link.key = key;
            link.parent = parent;

            bool ok = (newKey.tails == 1) // in body
                ? evaluateVertex<true>(newKey, newData, &link)
                : evaluateVertex<false>(newKey, newData, &link);

            result = result || ok;
        }
    }

    return result;
}

void reportSolution(const Vertex* vertex, const Vertex* parent, unsigned int extraMachine = 0xFFFFFFFF)
{
    vector<unsigned int> bestPath;

    if (extraMachine != 0xFFFFFFFF)
        bestPath.push_back(extraMachine);

    do
    {
        unsigned int number;
        unsigned int price = 0xFFFFFFFF;

        const bool inBody = parent->key.tails == 1;


        const VertexKey& key = parent->key;
        unsigned int inFlags = inBody ? (mask ^ key.body) : (key.tails & ~1);
        while (inFlags)
        {
            const unsigned int buffer = inFlags & (inFlags - 1);
            const unsigned int flag = inFlags - buffer;
            inFlags = buffer;

            const int idx = ((unsigned int)(flag * 0x077CB531U)) >> 27;

            for (vector<Machine>::iterator it(machinesByInIdx[idx].begin()), itEnd(machinesByInIdx[idx].end())
                ; it != itEnd
                ; ++it)
            {
                const Machine& machine = *it;
                VertexKey newKey;
                Destination destination;
                const bool ok = inBody
                    ? getNextKey<true>(machine, key, parent->parent, newKey, destination)
                    : getNextKey<false>(machine, key, parent->parent, newKey, destination);
                if (!ok)
                {
                    continue;
                }

                if (newKey == vertex->key && machine.price < price)
                {
                    price = machine.price;
                    number = machine.number;
                }
            }
        }

        bestPath.push_back(number);

        vertex = parent;
        parent = vertex->parent;
    } while (parent != 0);

    std::sort(bestPath.begin(), bestPath.end());
    cout << bestPath[0];
    for (unsigned int i = 1; i < bestPath.size(); ++i)
        cout << ' ' << bestPath[i];
    cout << '\n';
}


inline bool reachedEstimation(unsigned int body)
{
    unsigned int temp = ((body - 1) & (body - 2));
    unsigned int temp2 = (temp & (temp - 1));
    return 0 == (temp2 & (temp2 - 1));
}


template<bool inBody>
void handleVertex(const Priority& priority, PriorityQueue& queue)
{
    const VertexKey& key = priority.vertex->key;
    const bool inTails = !inBody;
    unsigned int inFlags = inBody ? (mask ^ key.body) : (key.tails & ~1);
    while (inFlags)
    {
        const unsigned int buffer = inFlags & (inFlags - 1);
        const unsigned int flag = inFlags - buffer;
        inFlags = buffer;

        const int idx = ((unsigned int)(flag * 0x077CB531U)) >> 27;

        for (vector<Machine>::iterator it(machinesByInIdx[idx].begin()), itEnd(machinesByInIdx[idx].end()); it != itEnd; ++it)
        {
            const Machine& machine = *it;
            VertexKey newKey;
            Destination destination;
            if (!getNextKey<inBody>(machine, key, priority.parent, newKey, destination))
            {
                continue;
            }

            unsigned int data[] =
            {
                priority.vertex->data[0] + machine.price,
                priority.vertex->data[1] + machine.price,
            };
            if (inTails)
            {
                data[0] -= estimates[machine.compound1idx];
            }
            if (nowhere == destination)
            {
                data[1] -= estimates2[machine.compound2idx];
            }

            const bool finishing = 1 == newKey.body && 1 == newKey.tails;

            const unsigned int estimate = std::max(data[0], data[1]);
            if (estimate > minFinishing)
            {
                continue;
            }

            const int idx = newKey.hash();
            Vertex* v = findItem(newKey, idx);
            if (v && v->visited())
            {
                continue;
            }
            if (v && v->estimate() <= estimate)
            {
                continue;
            }
            if (findSubstitute(newKey, estimate))
            {
                continue;
            }

            if (finishing && minFinishing > estimate)
            {
                minFinishing = estimate;
            }

            if (!inBody && newKey.tails != 1)
            {
                // check if it reaches body
                if (!checkVertex(newKey, priority.parent))
                {
                    continue;
                }
            }

            if (reachedEstimation(newKey.body) && !reachedEstimation(key.body) && !finishing)
            {
                Vertex link;
                link.key = key;
                link.parent = priority.parent;

                (newKey.tails == 1) // in body
                    ? evaluateVertex<true>(newKey, data, &link)
                    : evaluateVertex<false>(newKey, data, &link);
            }

            if (!v)
            {
                if (hashTable[idx].empty())
                {
                    v = hashTable + idx;
                }
                else
                {
                    v = new Vertex();
                    v->next = hashTable[idx].next;
                    hashTable[idx].next = v;
                }
                v->key = newKey;
            }

            v->data[0] = data[0];
            v->data[1] = data[1];
            queue.push(Priority(v, priority.vertex, estimate, finishing));
        }
    }
}



int main(int argc, char* argv[])
{
    if (argc != 2)
    {
        cerr << "Usage: " << argv[0] << " input_file\n";
        return 1;
    }
    FILE* f = fopen(argv[1], "r");

    Machine machine;
    char compound1[1024];
    char compound2[1024];

    for (unsigned int i = 0; i < sizeof(estimates) / sizeof(estimates[0]); ++i)
    {
        estimates[i] = 0x7FFFFFFF;
    }
    for (unsigned int i = 0; i < sizeof(estimates2) / sizeof(estimates2[0]); ++i)
    {
        estimates2[i] = 0x7FFFFFFF;
    }

    int numMachines = 0;
    while (4 == fscanf(f, "M%d %s %s %d\n", &machine.number, compound1, compound2, &machine.price))
    {
        machine.price *= 2;

        int compound1idx = GetCompoundIndex(compound1);
        if (0 == compound1idx)
        {
            compound1idx = 31;
        }
        machine.compound1idx = compound1idx;
        machine.compound1flg = 1u << compound1idx;
        machine.compound2idx = GetCompoundIndex(compound2);
        machine.compound2flg = 1u << machine.compound2idx;

        if (estimates[compound1idx] > machine.price)
        {
            estimates[compound1idx] = machine.price;
        }

        if (estimates2[machine.compound2idx] > machine.price)
        {
            estimates2[machine.compound2idx] = machine.price;
        }

        const int idx = ((unsigned int)(machine.compound1flg * 0x077CB531U)) >> 27;

        bool found = false;
        for (vector<Machine>::iterator it(machinesByInIdx[idx].begin()), itEnd(machinesByInIdx[idx].end())
            ; it != itEnd
            ; ++it)
        {
            if (it->compound1flg == machine.compound1flg && it->compound2flg == machine.compound2flg)
            {
                found = true;
                if (it->price > machine.price)
                {
                    it->price = machine.price;
                    it->number = machine.number;
                }

                break;
            }
        }

        if (!found)
        {
            machinesByInIdx[idx].push_back(machine);
            ++numMachines;
        }
    }

    fclose(f);

    for (int i = 0; i < sizeof(machinesByInIdx) / sizeof(machinesByInIdx[0]); ++i)
    {
        std::sort(machinesByInIdx[i].begin(), machinesByInIdx[i].end());
    }

    unsigned int totalEstimate = estimates[31];
    unsigned int totalEstimate2 = estimates2[0];
    for (int i = 1; i < compoundIndex; ++i)
    {
        totalEstimate += estimates[i];
        totalEstimate2 += estimates2[i];
    }

    PriorityQueue queue;

    mask = ((1 << compoundIndex) - 1) | 0x80000000;

    VertexKey initialKey = { mask, 0x80000000 };
    int initialIdx = initialKey.hash();
    Vertex* v = hashTable + initialIdx;
    v->next = 0;
    v->key = initialKey;
    v->data[0] = totalEstimate + 1;
    v->data[1] = totalEstimate2 + 1;
    queue.push(Priority(v, 0, std::max(totalEstimate, totalEstimate2), false));

    do
    {
        Priority priority = queue.top();
        if (priority.finishing())
        {
            cout
                << (priority.weight() / 2) << '\n';

            reportSolution(priority.vertex, priority.parent);
            break;
        }

        queue.pop();

        if (priority.vertex->visited())
        {
            continue;
        }

        const bool inBody = priority.vertex->key.tails == 1;
        if (inBody)
            handleVertex<true>(priority, queue);
        else
            handleVertex<false>(priority, queue);

        // visited
        priority.vertex->parent = priority.parent;
    } while (!queue.empty());

    return 0;
}
