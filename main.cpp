#include <iostream>
#include <algorithm>
#include <list>
#include <queue>
#include <vector>
#include <cassert>


using std::string;
using std::cin;
using std::cout;
using std::list;
using std::endl;
using std::queue;
using std::min;
using std::vector;


class Network
{
private:
    struct Edge
    {
        int capacity, flow;
        int from, to;

        Edge(int from, int to, int capacity) : from(from), to(to), capacity(capacity), flow(0) {}

        int remainCapacity() const
        {
            return capacity - flow;
        }

        bool isNotFull() const
        {
            return flow < capacity;
        }

        bool isFull() const {
            return capacity == flow;
        }

        void increaseEdgeFlow(int delta)
        {
            flow += delta;
#ifdef DEBUG
            assert(flow <= capacity);
#endif // DEBUG
        }
    };

    vector<Edge> edgesList;
    int countVertex, startVertex, finishVertex;
    vector<vector<int>> edgesFromVertex;
    bool oriented_;

    int addEdgeHelper(int from, int to, int capacity)
    {
        edgesList.emplace_back(from, to, capacity);
        return (int) (edgesList.size() - 1);
    }

public:
    const int INF = 1e7;

    Network(int n, int start, int finish) :
            edgesList(),
            edgesFromVertex(n),
            countVertex(n),
            startVertex(start),
            finishVertex(finish)
    {
        assert(start < n);
        assert(finish < n);
        assert(start != finish);
    }

    void addEdge(int from, int to, int capacity)
    {
#ifdef DEBUG
        assert(from < size_);
        assert(to < size_);
        assert(capacity >= 0);
#endif // DEBUG
        edgesFromVertex[from].push_back(addEdgeHelper(from, to, capacity));
        edgesFromVertex[to].push_back(addEdgeHelper(to, from, oriented_ ? 0 : capacity));
    }

    const int edgesCnt() const
    {
        return edgesList.size();
    }

    int getCountVertex() const
    {
        return countVertex;
    }

    int getStart() const
    {
        return startVertex;
    }

    int getFinish() const
    {
        return finishVertex;
    }

    const vector<int>& edgesOf(int vertex) const
    {
        return edgesFromVertex[vertex];
    }

    const int getReverseEdgeInd(int edgeInd) const
    {
        return (edgeInd ^ 1);
    };

    const Edge& getEdge(int edgeInd) const
    {
        return edgesList[edgeInd];
    }

    void increaseFlow(int edge, int delta)
    {
        edgesList[getReverseEdgeInd(edge)].increaseEdgeFlow(-delta);
        edgesList[edge].increaseEdgeFlow(delta);
    }

    void makeFlowZero()
    {
        for (int i = 0; i < edgesList.size(); ++i)
        {
            edgesList[i].flow = 0;
        }
    }
};


class MalhotraKumarMaheshwari
{
private:
    Network& network;
    vector<int> dist, pIn, pOut;
    vector<int> edgeForward, edgeBackward;

    MalhotraKumarMaheshwari(Network& net) :
            network(net),
            edgeBackward(net.getCountVertex()),
            edgeForward(net.getCountVertex()),
            dist(net.getCountVertex(), -1),
            pOut(net.getCountVertex()),
            pIn(net.getCountVertex())
    {
        update();
    }

    int potential(int v) const // изменить название функции p на potential
    {
        return min(pIn[v], pOut[v]);
    }

    void bfs()
    {
        dist.assign(network.getCountVertex(), -network.INF);
        dist[network.getStart()] = 0;
        queue<int> q;
        vector<bool> used(network.getCountVertex());
        used.assign(network.getCountVertex(), false);
        used[network.getStart()] = true;
        q.push(network.getStart());
        while (!q.empty())
        {
            int v = q.front();
            q.pop();
            for (auto e : network.edgesOf(v))
            {
                int u = network.getEdge(e).to;
                if (!used[u] && network.getEdge(e).isNotFull())
                {
                    dist[u] = dist[v] + 1;
                    q.push(u);
                    used[u] = true;
                }
            }
        }
    }

    void update() {
        bfs();
        pOut.assign(network.getCountVertex(), 0);
        pIn.assign(network.getCountVertex(), 0);
        for (int i = 0; i < network.edgesCnt(); ++i)
        {
            if (dist[network.getEdge(i).from] + 1 == dist[network.getEdge(i).to])
            {
                pOut[network.getEdge(i).from] += network.getEdge(i).remainCapacity();
                pIn[network.getEdge(i).to] += network.getEdge(i).remainCapacity();
            }
        }
        pOut[network.getFinish()] = network.INF;
        pIn[network.getStart()] = network.INF;
        edgeBackward.assign(network.getCountVertex(), 0);
        edgeForward.assign(network.getCountVertex(), 0);
    }

    void eraseVertex(int curV)
    {
        for (int e : network.edgesOf(curV))
        {
            if (dist[network.getEdge(e).to] == dist[curV] + 1)
            {
                int deltaFlow = network.getEdge(e).remainCapacity();
                pIn[network.getEdge(e).to] -= deltaFlow;
            }
            else if (dist[network.getEdge(e).to] == dist[curV] - 1)
            {
                int deltaFlow = network.getEdge(network.getReverseEdgeInd(e)).remainCapacity(); // завести функцию revegt(e) возваращающую обратное ребро
                pOut[network.getEdge(e).to] -= deltaFlow;
            }
        }
        dist[curV] = -network.INF;
    }

    void tryToPush(int u, int& edgePtr, int possibleDist, bool reversed, int t, queue<int>& q, vector<int>& flowToPush)
    {
        int edgeInd = network.edgesOf(u)[edgePtr];
        const auto& edge = network.getEdge(edgeInd);
        if (dist[edge.to] != possibleDist || (!reversed && dist[edge.to] >= dist[t] && edge.to != t))
        {
            ++edgePtr;
            return;
        }
        int orientedEdge = reversed ? (network.getReverseEdgeInd(edgeInd)) : edgeInd;
        int toPush = min(network.getEdge(orientedEdge).remainCapacity(), flowToPush[u]);
        if (toPush > 0)
        {
            if (flowToPush[edge.to] == 0)
            {
                q.push(edge.to);
            }
            flowToPush[u] -= toPush;
            flowToPush[edge.to] += toPush;
            (reversed ? pOut : pIn)[edge.to] -= toPush;
            (reversed ? pIn : pOut)[u] -= toPush;
            network.increaseFlow(orientedEdge, toPush);
        }
        else
        {
            ++edgePtr;
        }
    }

    void pushBlockingFlow(int beginPotential, int beginV, int finalV, bool reversed)
    {
        vector<int> flowToPush(network.getCountVertex());
        queue<int> q;
        flowToPush[beginV] = beginPotential;
        q.push(beginV);
        while (!q.empty())
        {
            int curV = q.front();
            q.pop();
            if (curV == finalV)
            {
                flowToPush[curV] = 0;
                continue;
            }
            int possibleDist = dist[curV] + (reversed ? -1 : 1);
            int& edgePtr = reversed ? edgeBackward[curV] : edgeForward[curV];
            while (flowToPush[curV] > 0)
            {
                tryToPush(curV, edgePtr, possibleDist, reversed, finalV, q, flowToPush);
            }
        }
    }

public:
    static int findMaxFlow(Network& network)
    {
        const int INVALID = -1;
        MalhotraKumarMaheshwari data(network);
        int result = 0;
        while (data.dist[network.getFinish()] >= 0)
        {
            int curV;
            while (true)
            {
                curV = INVALID;
                for (int i = 0; i < network.getCountVertex(); ++i)
                {
                    if (data.dist[i] >= 0 && (curV == INVALID || data.potential(i) < data.potential(curV)))
                    {
                        curV = i;
                    }
                }
                if (curV == INVALID)
                {
                    break;
                }

                int potentialFromCurV = data.potential(curV);
                if (potentialFromCurV > 0)
                {
                    data.pushBlockingFlow(potentialFromCurV, curV, network.getFinish(), false);
                    data.pushBlockingFlow(potentialFromCurV, curV, network.getStart(), true);
                    result += potentialFromCurV;
                }
                else
                {
                    data.eraseVertex(curV);
                }
            }
            data.update();
        }

        return result;
    }
};


class Preflow
{
private:
    Network& network;
    vector<int> height, excess;
    vector<int> edgePtrs;

    Preflow(Network& network) :
            network(network),
            edgePtrs(network.getCountVertex(), 0),
            excess(network.getCountVertex(), 0),
            height(network.getCountVertex(), 0)
    {
        for (int e : network.edgesOf(network.getStart()))
        {
            int u = network.getEdge(e).to;
            int cap = network.getEdge(e).capacity;
            network.increaseFlow(e, cap);
            excess[network.getStart()] -= cap;
            excess[u] += cap;
        }
        height[network.getStart()] = network.getCountVertex();
    }

    void push(int e)
    {
        const auto& edge = network.getEdge(e);
        int delta = min(edge.capacity - edge.flow, excess[edge.from]);
        network.increaseFlow(e, delta);
        excess[edge.to] += delta;
        excess[edge.from] -= delta;
    }

    void relabel(int u)
    {
        int h = 2 * network.getCountVertex(); // it should be enough cuz h[v] <= 2 * countVertex - 1 for all vertices
        for (auto e : network.edgesOf(u))
        {
            if (network.getEdge(e).isNotFull())
            {
                h = min(h, height[network.getEdge(e).to]);
            }
        }
        height[u] = h + 1;
    }

    void discharge(int u)
    {
        while (excess[u] > 0)
        {
            if (edgePtrs[u] == network.edgesOf(u).size())
            {
                relabel(u);
                edgePtrs[u] = 0;
            }
            else
            {
                int e = network.edgesOf(u)[edgePtrs[u]];
                int v = network.getEdge(e).to;
                if (network.getEdge(e).isNotFull() && height[u] == height[v] + 1)
                {
                    push(e);
                }
                else
                {
                    ++edgePtrs[u];
                }
            }
        }
    }

public:
    static int findMaxFlow(Network& network)
    {
        Preflow data(network);
        list<int> vertices;
        for (int i = 0; i < network.getCountVertex(); ++i)
        {
            if (i != network.getFinish() && i != network.getStart())
            {
                vertices.push_back(i);
            }
        }
        auto iter = vertices.begin();
        while (iter != vertices.end())
        {
            int v = *iter;
            int heightBefore = data.height[v];
            data.discharge(v);
            if (data.height[v] > heightBefore)
            {
                vertices.erase(iter);
                vertices.push_front(v);
                iter = vertices.begin();
            }
            ++iter;
        }
        return data.excess[network.getFinish()];
    }
};


Network readNetwork(std::istream& in, int& maxVal)
{
    maxVal = 0;
    int cnt_vertex;
    in >> cnt_vertex;
    int s = cnt_vertex, t = cnt_vertex + 1;
    Network network(cnt_vertex + 2, s, t);

    for (int i = 0; i < cnt_vertex; ++i)
    {
        int cap;
        in >> cap;
        if (cap <= 0)
        {
            network.addEdge(i, t, -cap);
        }
        else
        {
            maxVal += cap;
            network.addEdge(s, i, cap);
        }
    }

    for (int i = 0; i < cnt_vertex; ++i)
    {
        int relations_cnt;
        in >> relations_cnt;
        int relation_subj = -1;
        for(int j = 0; j < relations_cnt; ++j)
        {
            in >> relation_subj;
            --relation_subj;
            network.addEdge(i, relation_subj, network.INF);
        }
    }

    return network;
}


int Solver(Network& network, string&& algorithm) // You can choose which algorithm do you want to use to find MaxFlow of your Network
{
    assert(algorithm == "MKM" || algorithm == "Preflow");
    int maxFlow = ((algorithm == "MKM") ? MalhotraKumarMaheshwari::findMaxFlow(network) : Preflow::findMaxFlow(network));
    return maxFlow;
}

int main()
{
#ifdef DEBUG
    assert(freopen("N1.in", "r", stdin) != 0);
#endif // DEBUG
    int maxVal;
    Network network = readNetwork(cin, maxVal);
    int MKM_ans = Solver(network, "MKM");
    network.makeFlowZero();
    int Preflow_ans = Solver(network, "Preflow");
    assert(MKM_ans == Preflow_ans);
    cout << maxVal - MKM_ans << endl;

    return 0;
}
