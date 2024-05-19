import sys
import time
from heapq import heappush, heappop
from random import choice
import math
import collections
from binary_heap import *
import networkx as nx
import numpy as np
import heapq
import random
import time
from func_timeout import func_set_timeout, FunctionTimedOut

# 并查集合并集合的复杂度是O（1）
class DisjointSet:
    def __init__(self, vertices):
        self.parent = {v: v for v in vertices}  # 初始情况下，每个顶点的父节点都是其自身
        self.rank = {v: 0 for v in vertices}    # 初始情况下，每个顶点的秩都是0。秩用于在合并操作中决定树的合并方式，以保持树的平衡。

    # 查找：判断两个元素是否在一个集合
    # 这个函数是并查集中的路径压缩方法。它用于查找给定顶点的根节点，并在查找的过程中压缩路径，以减小树的深度，提高后续查找的效率。
    # 如果当前顶点的父节点不是根节点（即不是自己），则递归地调用find函数查找其父节点的根节点，并将当前顶点的父节点设置为根节点，从而实现路径压缩。
    def find(self, vertex):
        path = []  # 存储路径
        while self.parent[vertex] != vertex:
            path.append(vertex)
            vertex = self.parent[vertex]
        for v in path:  # 路径压缩
            self.parent[v] = vertex
        return vertex

    # 合并：合并两个集合
    # 这个函数是并查集中的合并操作。它用于将两个顶点所在的连通分量合并起来。
    # 首先，它找到每个顶点的根节点。
    # 如果两个根节点相同，表示这两个顶点已经在同一个连通分量中，无需再合并，直接返回。
    # 如果根节点不同，则比较它们的秩（rank），将秩较小的根节点指向秩较大的根节点，这样可以保证合并后的树的深度至少不会增加。
    # 如果两个根节点的秩相同，选择一个作为新的根节点，并将另一个根节点的秩增加1。
    def union(self, vertex1, vertex2):
        root1 = self.find(vertex1)
        root2 = self.find(vertex2)

        if root1 == root2:
            return

        if self.rank[root1] < self.rank[root2]:
            self.parent[root1] = root2  # 将一棵树a接到另一棵树b后，树a的所有结点高度都会加1，而树b不会变化，所以让秩小的树接到秩大的根节点付出的代价相对更少
        elif self.rank[root1] > self.rank[root2]:
            self.parent[root2] = root1
        else:
            self.parent[root2] = root1
            self.rank[root1] += 1

# 定义超时异常
class TimeoutException(Exception):
    pass

# 装饰器函数，设置超时时间
def func_set_timeout(timeout):
    def decorator(func):
        def wrapper(*args, **kwargs):
            start_time = time.time()
            result = None
            try:
                # 设置超时时间
                result = func(*args, **kwargs)
            except TimeoutException:
                print(f"Function {func.__name__} timed out")
            except Exception as e:
                print(f"Function {func.__name__} encountered an error: {str(e)}")
            finally:
                # 计算函数执行时间
                execution_time = time.time() - start_time
                print(f"Function {func.__name__} executed in {execution_time:.2f} seconds")
                return result
        return wrapper
    return decorator

# 超时装饰器
def timeout(seconds):
    def decorator(func):
        def wrapper(*args, **kwargs):
            raise TimeoutException()
        return wrapper
    return decorator

class Graph:

    def __init__(self, dataset):
        self.dataset = dataset
        self.adj_list, self.deg, self.edge = self.graph_list()
        self.n = len(self.adj_list)
        self.m = 0
        for u in self.adj_list:
            self.m += len(self.adj_list[u])
        self.m = self.m / 2
        print("number of nodes:" + str(self.n))
        print("number of edges:" + str(self.m))

    def graph_list(self):
        starttime = time.time()
        adj_list = {}
        edge = set()
        print("........................")
        print(self.dataset + " is loading...")
        file = open(self.dataset)
        while 1:
            lines = file.readlines(50000)
            if not lines:
                break
            for line in lines:
                line = line.split()
                if str(line[0]) == "#":
                    continue
                if int(line[0]) == int(line[1]):
                    continue
                doubleedge = [(int(line[0]), int(line[1])), (int(line[1]), int(line[0]))]
                for (f_id, t_id) in doubleedge:
                    if f_id in adj_list:
                        adj_list[f_id].add(t_id)
                    else:
                        adj_list[f_id] = {t_id}

                if (int(line[0]),int(line[1])) in edge or (int(line[1]),int(line[0])) in edge:
                    continue
                edge.add((int(line[0]),int(line[1])))

        file.close()
        deg = {}
        for u in adj_list:
            deg[u] = len(adj_list[u])
        endtime = time.time()
        print("load_time(s)" + str(endtime - starttime))
        return adj_list, deg, edge

    def compu_conductance(self, S):
        d = {}
        dout = {}
        sum_d = 0
        sum_dout = 0
        for u in S:
            d[u] = len(self.adj_list[u])
            sum_d += d[u]
            dout[u] = d[u] - len(set(self.adj_list[u]) & set(S))
            sum_dout += dout[u]
        if 2 * self.m != sum_d:
            condu = sum_dout / min(sum_d, 2 * self.m - sum_d)
            return condu
        else:
            return float('inf')  # 最好的情况condu = 0.0

    # 并查集路径压缩判断图连通：O(V+E)
    def is_connected(self, S):
        ds = DisjointSet(S)
        start_node = int(random.choice(list(S)))

        for v1 in S:
            for v2 in self.adj_list[v1]:
                if v2 in S:
                    ds.union(v1, v2)

        root_vertex = ds.find(start_node)  # 获取start_node所属的连通分量的根节点
        # root_vertex = ds.find(QID)  # 获取 QID 所属的连通分量的根节点
        for v in S:
            if ds.find(v) != root_vertex:
                return False
            else:
                return True

    # initial community
    def find_max_clique(self):
        g = nx.Graph(C_adj_list)  # 创建 NetworkX 图
        cliques = list(nx.find_cliques(g))
        max_clique = max(cliques, key=lambda clique: len(clique) if QID in clique else 0, default=[])

        return max_clique

    # 不重叠的最大k-clique
    def find_clique(self):
        g = nx.Graph(C_adj_list)  # 创建 NetworkX 图
        cliques = [clique for clique in nx.enumerate_all_cliques(g) if QID in clique and len(clique) >= 4]
        if not cliques:
            return [[QID]]

        result = []
        for clique in cliques:
            for existing_clique in result:
                if set(clique).issubset(existing_clique):
                    break
            else:
                result = [c for c in result if not set(c).issubset(clique)]  # 移除已包含当前团的团
                result.append(clique)
        return result

    # CS&PPR
    @func_set_timeout(7200)
    def sweep_cut_PPR(self, alpha, epsilon):
        starttime = time.time()
        pi = self.fpush(alpha, epsilon)[0]
        for u in pi:
            pi[u] = pi[u] / self.deg[u]
        pi = sorted(pi.items(), key=lambda kv: (kv[1], kv[0]), reverse=True)
        S = set()
        volS = 0
        cutS = 0
        best_condu, best_index, count = float('inf'), 0, 0
        best_set = set()
        for x in pi:
            u = x[0]
            S.add(u)
            count += 1
            cutS = cutS - 2 * len(set(self.adj_list[u]) & S) + self.deg[u]
            volS = volS + self.deg[u]
            if min(volS, 2 * self.m - volS) != 0 and cutS / min(volS,2 * self.m - volS) < best_condu and volS <= self.m:
                best_condu = cutS / min(volS, 2 * self.m - volS)
                best_index = count
        for x in range(best_index):   
            best_set.add(pi[x][0])
        # if len(best_set) > self.n / 2:
        #     best_set = set(self.adj_list) - set(best_set)
        # sweep_set = best_set
        # sweep_condu = best_condu
        # endtime = time.time()
        # sweep_time = endtime - starttime
        # return sweep_time, sweep_set, sweep_condu

        sweep_set = self.maintain_connected(best_set)    # 包含QID且connected
        endtime = time.time()
        sweep_time = endtime - starttime
        return sweep_time, sweep_set

    def fpush(self, alpha, epsilon):  # NIBBLE_PPR
        starttime = time.time()
        pi, r = {}, {}
        r[QID] = 1
        q = collections.deque()
        q.append(QID)
        while q:
            u = q.popleft()
            for v in self.adj_list[u]:
                if v not in r:
                    r[v] = 0
                update = (1 - alpha) * r[u] / self.deg[u]
                r[v] = r[v] + update  # unweighted graph
                if (r[v] - update) / self.deg[v] < epsilon and r[v] / self.deg[v] >= epsilon:
                    q.append(v)
            if u not in pi:
                pi[u] = 0
            pi[u] = pi[u] + alpha * r[u]
            r[u] = 0
        endtime = time.time()
        return pi, endtime - starttime

    # HK-Relax   
    @func_set_timeout(7200)
    def sweep_cut_HK(self, t, epsilon):
        starttime = time.time()
        pi = self.hk_relax(t, epsilon)[0]
        for u in pi:
            pi[u] = pi[u] / self.deg[u]
        pi = sorted(pi.items(), key=lambda kv: (kv[1], kv[0]), reverse=True)
        S = set()
        volS = 0
        cutS = 0
        best_condu, best_index, count = float('inf'), 0, 0
        best_set = set()
        for x in pi:
            u = x[0]
            S.add(u)
            count += 1
            cutS = cutS - 2 * len(set(self.adj_list[u]) & S) + self.deg[u]
            volS = volS + self.deg[u]
            if min(volS, 2 * self.m - volS) != 0 and cutS / min(volS,2 * self.m - volS) < best_condu and volS <= self.m:
                best_condu = cutS / min(volS, 2 * self.m - volS)
                best_index = count
        for x in range(best_index):   
            best_set.add(pi[x][0])
        # if len(best_set) > self.n / 2:
        #     best_set = set(self.adj_list) - set(best_set)
        # sweep_set = best_set
        # sweep_condu = best_condu
        # endtime = time.time()
        # sweep_time = endtime - starttime
        # return sweep_time, sweep_set, sweep_condu

        sweep_set = self.maintain_connected(best_set)    # 包含QID且connected
        endtime = time.time()
        sweep_time = endtime - starttime
        return sweep_time, sweep_set

    def hk_relax(self, t, epsilon):
        N = int(2 * t * math.log(1 / epsilon)) + 1
        starttime = time.time()
        psis = {}
        psis[N] = 1.
        for i in range(N - 1, -1, -1):
            psis[i] = psis[i + 1] * t / (float(i + 1.)) + 1.  # eq(6) of hk-relax
        x = {}  # Store x, r as dictionaries
        r = {}  # initialize residual
        Q = collections.deque()  # initialize queue

        r[(QID, 0)] = 1.
        Q.append((QID, 0))
        while len(Q) > 0:
            (v, j) = Q.popleft()  # v has r[(v,j)] ...
            rvj = r[(v, j)]
            # perform the hk-relax step
            if v not in x: x[v] = 0.
            x[v] += rvj
            r[(v, j)] = 0.
            mass = (t * rvj / (float(j) + 1.)) / self.deg[v]
            for u in self.adj_list[v]:  # for neighbors of v
                next = (u, j + 1)  # in the next block
                if j + 1 == N:
                    if u not in x: x[u] = 0.
                    x[u] += rvj / self.deg[v]
                    continue
                if next not in r: r[next] = 0.
                thresh = math.exp(t) * epsilon * self.deg[u]
                thresh = thresh / (2 * N * psis[j + 1])
                if r[next] < thresh and r[next] + mass >= thresh:
                    Q.append(next)  # add u to queue
                r[next] = r[next] + mass
        endtime = time.time()
        return x, endtime - starttime

    # CSM
    def maintain_connected(self, temp):  # BFS: connected && QID
        q, visited = [QID], {QID}
        while q:
            v = q.pop()
            for u in self.adj_list[v]:
                if u in temp and u not in visited:
                    q.append(u)
                    visited.add(u)
        return visited

    def Global_CSM(self, C):
        deg = {}
        mymin_heap = MinHeap([])
        for u in C:
            deg[u] = len(set(self.adj_list[u]) & C)
            mymin_heap.insert([u, deg[u]])
        best = mymin_heap.peek()[1]  # 最小度
        D, best_index = [], 0
        temp = C.copy()
        while mymin_heap:
            u = mymin_heap.remove()[0]
            temp.remove(u)
            if str(u) == str(QID):
                break
            D.append(u)
            for v in self.adj_list[u]:
                if v in temp:
                    deg[v] -= 1
                    mymin_heap.decrease_key(v, deg[v])
            if mymin_heap.peek()[1] > best:
                best = mymin_heap.peek()[1]
                best_index = len(D)
        R = C - set(D[:best_index])
        result = self.maintain_connected(R)
        return result
    
    @func_set_timeout(7200)
    def Local_CSM(self):
        starttime = time.time()
        best, C, D = 0, set(), {QID}
        inter_degree, inter_degree_min_heap = {}, MinHeap([])
        Q = MaxHeap([])
        Q.insert([QID, 0])
        Q_with_C = {}
        while Q.heap:
            v = Q.remove()[0]
            C.add(v)
            temp = set(self.adj_list[v]) & C  # C中v的邻居集合
            inter_degree[v] = len(temp)
            inter_degree_min_heap.insert([v, inter_degree[v]])
            for u in temp:
                inter_degree[u] = inter_degree[u] + 1
                inter_degree_min_heap.increase_key(u, inter_degree[u])
            for w in self.adj_list[v]:
                if w in Q.heap_dict:
                    Q_with_C[w] = Q_with_C[w] + 1
                    Q.increase_key(w, Q_with_C[w])
            if (inter_degree_min_heap.peek())[1] > best:
                best = (inter_degree_min_heap.peek())[1]
                if best == len(self.adj_list[QID]) or best == math.floor((1 + math.sqrt(9 + 8 * (self.m - self.n))) / 2):
                    endtime = time.time()
                    CSM_time = endtime - starttime
                    return CSM_time, C
            for u in self.adj_list[v]:
                if u not in D:
                    D.add(u)
                    if len(self.adj_list[u]) >= best:
                        Q_with_C[u] = len(set(self.adj_list[u]) & C)
                        Q.insert([u, Q_with_C[u]])
        CSM_set = self.Global_CSM(C)
        endtime = time.time()
        CSM_time = endtime - starttime
        return CSM_time, CSM_set

    # TCP
    def truss_decompisition(self):
        deg = {}
        for node_id in self.adj_list:
            deg[node_id] = len(self.adj_list[node_id])
        supp = {}
        myMinHeap = MinHeap([])
        for (u, v) in self.edge:
            small_degre_node = u
            large_degre_node = v
            if deg[u] > deg[v]:
                small_degre_node = v
                large_degre_node = u
            supp[(small_degre_node, large_degre_node)] = 0
            for w in self.adj_list[small_degre_node]:
                if w in self.adj_list[large_degre_node]:
                    supp[(small_degre_node, large_degre_node)] += 1
            myMinHeap.insert([(small_degre_node, large_degre_node), supp[(small_degre_node, large_degre_node)]])
        max_truss,truss_number, truss_renumber = 0,{}, {}
        while myMinHeap.heap:
            x = myMinHeap.remove()
            if x[1]> max_truss:
                max_truss = x[1]
            truss_number[x[0]] = max_truss

            if truss_number[x[0]] in truss_renumber:
                truss_renumber[truss_number[x[0]]].add(x[0])
            else:
                truss_renumber[truss_number[x[0]]] = {x[0]}

            small_degre_node,large_degre_node=x[0][0],x[0][1]
            for w in self.adj_list[small_degre_node]:
                if w in self.adj_list[large_degre_node]:
                    if (w, small_degre_node) in supp and (w, small_degre_node) not in truss_number:
                        supp[(w, small_degre_node)] -= 1
                        myMinHeap.decrease_key((w, small_degre_node), supp[(w, small_degre_node)])
                    if (small_degre_node, w) in supp and (small_degre_node, w) not in truss_number:
                        supp[(small_degre_node, w)] -= 1
                        myMinHeap.decrease_key((small_degre_node, w), supp[(small_degre_node, w)])

                    if (w, large_degre_node) in supp and (w, large_degre_node) not in truss_number:
                        supp[(w, large_degre_node)] -= 1
                        myMinHeap.decrease_key((w, large_degre_node), supp[(w, large_degre_node)])
                    if (large_degre_node, w) in supp and (large_degre_node, w) not in truss_number:
                        supp[(large_degre_node, w)] -= 1
                        myMinHeap.decrease_key((large_degre_node, w), supp[(large_degre_node, w)])

        #堆truss_number和truss_renumber存了两遍
        for (u,v) in self.edge:
            if (u,v) in truss_number:
                truss_number[(v,u)]=truss_number[(u,v)]
                truss_renumber[truss_number[(v,u)]].add((v,u))
            if (v,u) in truss_number:
                truss_number[(u,v)]=truss_number[(v,u)]
                truss_renumber[truss_number[(u,v)]].add((u,v))
        # print("max_truss"+str(max_truss))
        return truss_number, truss_renumber

    @func_set_timeout(7200)
    def truss_community(self):  # xin huang sigmod2014
        starttime=time.time()
        visited,l=set(),0
        C= {}
        truss_number, truss_renumber = self.truss_decompisition()
        k = float("inf")
        for u in G.adj_list[QID]:
            if truss_number[(QID, u)] < k:
                k = truss_number[(QID, u)]

        for u in self.adj_list[QID]:
            if truss_number[(QID,u)]>=k and (QID,u) not in visited:
                    l+=1
                    C[l]=set()
                    Q=[]
                    Q.append((QID,u))
                    visited.add((QID,u)),visited.add((u,QID)) #需要存两次
                    while Q:
                        (x,y)=Q.pop()
                        C[l].add((x,y))
                        for z in self.adj_list[x]:
                            if z in self.adj_list[y]:
                                if truss_number[(x,z)]>=k and truss_number[(y, z)] >= k:
                                        if (x,z) not in visited:
                                            Q.append((x,z))
                                            visited.add((x,z)), visited.add((z,x))
                                        if (y,z) not in visited:
                                            Q.append((y,z))
                                            visited.add((y,z)),visited.add((z,y))
        endtime = time.time()
        #return maximum ktruss community
        max_C_size, best_index = 0, 0
        for i in C:
            if len(C[i]) > max_C_size:
                max_C_size = len(C[i])
                best_index = i

        C_set = set()
        for (f_id, t_id) in C[best_index]:
            if f_id not in C_set:
                C_set.add(f_id)
            if t_id not in C_set:
                C_set.add(t_id)
        endtime = time.time()
        C_time = endtime - starttime
        return C_time, C_set

    # SM
    def is_or_not_connected(self, S):
        visited = set()
        start_node = int(random.choice(list(S)))
        queue = [(start_node)]
 
        while queue:
            u = heapq.heappop(queue)
            visited.add(u)
            for v in self.adj_list[u]:
                if v not in visited:
                    queue.append(v)
        
        if len(visited) == len(S):
            return True
        else:
            return False

    def compute_M(self, new_S):
        new_ind = 0  # S内部边数/S的割边数
        new_vold = 0
        for u in new_S:
            new_ind += len(set(self.adj_list[u]) & new_S)
            new_vold += self.deg[u]
        new_outd = new_vold - new_ind
        new_M = (new_ind / 2) / new_outd if new_outd != 0 else float('inf')
        return new_M
  
    @func_set_timeout(7200)
    def subgraph_modularity(self):   # Luo 2006
        starttime = time.time()
        # Initialize the subgraph with the seed vertex and its neighbors
        S = {QID}
        N = set(self.adj_list[QID])
        # Calculate the initial in-degree and out-degree
        M = self.compute_M(S)
        # print("M = " + str(M))
        while True:
            Q = []
            while N:
                # Addition step
                best_vertex = None
                # print("best_vertex = " + str(best_vertex))
                for u in N:
                    if u not in S:
                        # Calculate the increase in modularity by adding the vertex
                        new_S = S.copy()
                        new_S.add(u)
                        new_M = self.compute_M(new_S)
                        # print("u = " + str(u) + ", new_S = " + str(new_S) + ", new_M=" + str(new_M))

                        if new_M > M:
                            M = new_M
                            best_vertex = u
                            # print("best_vertex=" + str(best_vertex) + ", u =" + str(u))

                # Add the best vertex to the subgraph
                if best_vertex != None:
                    S.add(best_vertex)
                    N.remove(best_vertex)
                    Q.append(best_vertex)
                    M = self.compute_M(S)
                    # print("M = " + str(M) + ", S = " + str(S) + ", N = " + str(N))
                else:
                    break

            # Deletion step
            new_S = S.copy()
            deleteQ = []
            for u in S:
                # Calculate the increase in modularity by removing the vertex
                new_S.remove(u)
                new_M = self.compute_M(new_S)
                # print("u = " + str(u) + ", new_S = " + str(new_S) + ", new_M = " + str(new_M))

                # Update if the M is increase so far and the subgraph remains connected
                if new_M > M and self.is_connected(new_S):
                    deleteQ.append(u)
                    M = new_M
                    if u in Q:
                        Q.remove(u)
                else:
                    new_S.add(u)
                
            for u in deleteQ:
                S.remove(u)

            # Add vertices to neighbor set N
            if len(Q) != 0:
                for u in Q:
                    for v in self.adj_list[u]:
                        if v not in S and v not in N:
                            N.add(v)
                # print("N = " + str(N))
            else:
                break
        
        endtime = time.time()
        SM_time = endtime - starttime
        if M > 0 and QID in S:
            return SM_time, S
        else:
            S = set()
            # print('no module found for QID')
            return SM_time, S

    # LM
    def compute_R(self, new_S):
        I = 0
        T = 0
        a = 0
        b = 0
        B = set()
        for u in new_S:
            if self.deg[u] != len(set(self.adj_list[u]) & new_S):
                B.add(u)
        for u in B:
            for v in self.adj_list[u]:
                if v in new_S:
                    I += 1
                if v in B:
                    a += 1
                if v not in B:
                    T += 1
                if v in B:
                    b += 1
        I = I - a / 2
        T = T + b / 2
        # print("B = " + str(B) + ", I = " + str(I) + ", T = " + str(T))
        R = I / T if T != 0 else 0
        return R
    
    @func_set_timeout(7200)
    def local_modularity(self, k):  # Clauset 2005
        starttime = time.time()
        S = {QID}  # Initialize C with the source vertex
        U = set(self.adj_list[QID])  # Initialize U with neighbors of v0
        R = 0
        # print("R = " + str(R))
        while len(S) < k:
            best_vertex = None
            # Compute R for each vertex in U
            for u in U:
                new_S = S.copy()
                new_S.add(u)
                new_R = self.compute_R(new_S)
                # print("u = " + str(u) + ", new_S = " + str(new_S) + ", new_R = " + str(new_R))
                if new_R > R:
                    R = new_R
                    best_vertex = u
                    # print("best_vertex = " + str(best_vertex) + ", R = " + str(R))

            # Add the vertex with maximum R to C and update sets
            if best_vertex != None:
                S.add(best_vertex)
                U.update(self.adj_list[best_vertex])  # 集合U在原有元素的基础上增加原先集合t所独有的元素，两集合相加
                U.difference_update(S)   # 将集合U更新为集合U与集合S的差集
                # print("S = " + str(S) + ", U = " + str(U))
            else:
                break
        
        endtime = time.time()
        LM_time = endtime - starttime
        return LM_time, S

    # sample
    def sample_subgraph(self, hop, min_vertices, max_vertices):
        starttime = time.time()
        sample_S = set()
        # compute_distances
        distances = {}
        visited = set()
        queue = [(0, QID)]
        while queue:
            distance, u = heapq.heappop(queue)
            sample_S.add(u)
            if u in visited:
                continue
            visited.add(u)
            if len(distances) < min_vertices:
                distances[u] = distance
                for v in self.adj_list[u]:
                    if v not in distances:
                        heapq.heappush(queue, (distance + 1, v))
                
            else:
                if distance > hop:  # 仅访问 hop-hop 内的顶点
                    break
                distances[u] = distance
                for v in self.adj_list[u]:
                    if v not in distances:
                        heapq.heappush(queue, (distance + 1, v))
                if len(distances) > max_vertices:
                    break
        # sample_S = sorted(distances.keys(), key=lambda x: distances[x])
        endtime = time.time()
        sample_time = endtime - starttime
        return sample_S, sample_time

    # SCCS
    @func_set_timeout(7200)
    def SCCS(self, count):
        starttime = time.time()
        # initializePhase
        max_clique = self.find_max_clique()
        
        # max_clique = self.find_clique_around_node()
        S = set(max_clique)      
        B = set()  # 待检查的边界顶点集
        sumS = 0
        volS = 0
        for u in S:
            sumS += len(set(self.adj_list[u]) & S)  # sumS
            volS += self.deg[u]  # volS
            if self.deg[u] != len(set(self.adj_list[u]) & S) and u != QID:
                B.add(u)
        score_best = sumS / volS
 
        for u in B:
                new_S = S.copy()
                new_S.remove(u)
                sumS_remove = sumS - 2 * len(set(self.adj_list[u]) & new_S)
                volS_remove = volS - self.deg[u]
                score_remove = sumS_remove / volS_remove
                if score_remove > score_best:
                    S.remove(u)
                    sumS = sumS_remove
                    volS = volS_remove
                    score_best = score_remove

        while True:
            mymax_heap = MaxHeap([])
            for u in S:
                for v in C_adj_list[u]:
                    if v not in S:
                        sumS_in = sumS + 2 * len(set(self.adj_list[v]) & S)
                        volS_in = volS + self.deg[v]
                        idxs = [i[0] for i in mymax_heap.heap]
                        if v not in idxs:
                            score = sumS_in / volS_in
                            mymax_heap.insert([v, score])
            
            i = count
            S_temp = S.copy()
            volS_temp = volS
            sumS_temp = sumS
            while len(mymax_heap.heap) != 0 and volS < self.m:
                u = mymax_heap.remove()[0]
                if i > 0:
                    S_temp.add(u)
                    # 计算 score
                    sumS_temp = sumS_temp + 2 * len(set(self.adj_list[u]) & S_temp)
                    volS_temp = volS_temp + self.deg[u]
                    score = sumS_temp / volS_temp
                    for pair in mymax_heap.heap:  # 只更新堆中元素
                        v = pair[0]
                        sumS_in = sumS_temp + 2 * len(set(self.adj_list[v]) & S_temp)
                        volS_in = volS_temp + self.deg[v]
                        score_in = sumS_in / volS_in
                        if score_in >= mymax_heap.heap_dict[v]:
                            mymax_heap.increase_key(v, score_in)
                        else:
                            mymax_heap.decrease_key(v, score_in)
                    for v in C_adj_list[u]:
                        idxs = [i[0] for i in mymax_heap.heap]
                        if v not in S_temp and v not in idxs:
                            sumS_in = sumS_temp + 2 * len(set(self.adj_list[v]) & S_temp)
                            volS_in = volS_temp + self.deg[v]
                            score_in = sumS_in / volS_in
                            mymax_heap.insert([v, score_in])
                    if score > score_best:
                        i = count
                        S = S_temp.copy()
                        sumS = sumS_temp
                        volS = volS_temp
                        score_best = score
                    else:
                        i -= 1
                        continue
                else:
                    break

            # checkPhase：从B中移除使得best_score增大的顶点
            changed = False
            B = set()
            for u in S:
                if self.deg[u] != len(set(self.adj_list[u]) & S) and u != QID:
                    B.add(u)
            for u in B:
                new_S = S.copy()
                new_S.remove(u)
                sumS_remove = sumS - 2 * len(set(self.adj_list[u]) & new_S)
                volS_remove = volS - self.deg[u]
                score_remove = sumS_remove / volS_remove
                if score_remove > score_best and self.is_connected(new_S):
                    changed = True
                    S.remove(u)
                    sumS = sumS_remove
                    volS = volS_remove
                    score_best = score_remove
            if changed == False or volS >= self.m:
                break

        endtime = time.time()
        LCCS_time = endtime - starttime
        return LCCS_time, S

    # f1_score
    def calculate_f1_score(self, true_community, predicted_community):
        true_positive = len(set(true_community) & set(predicted_community))
        false_positive = len(set(predicted_community) - set(true_community))
        false_negative = len(set(true_community) - set(predicted_community))

        precision = true_positive / (true_positive + false_positive) if (true_positive + false_positive) != 0 else 0
        recall = true_positive / (true_positive + false_negative) if (true_positive + false_negative) != 0 else 0

        f1_score = 2 * (precision * recall) / (precision + recall) if (precision + recall) != 0 else 0

        return f1_score, precision, recall

    # separability, density, conductance
    def metric(self, S):
        deg = {}
        dout = {}
        sum_d = 0
        sum_deg = 0
        sum_dout = 0
        for u in S:
            sum_d += self.deg[u]
            deg[u] = len(set(self.adj_list[u] & S))
            sum_deg += deg[u]  # S中的总度数
            dout[u] = self.deg[u] - deg[u]
            sum_dout += dout[u]  # S割边总数
        separability = (sum_deg / 2) / sum_dout if sum_dout != 0 else (sum_deg / 2)
        density = (sum_deg / 2) / len(S)
        if 2 * self.m != sum_d:
            condu = sum_dout / min(sum_d, 2 * self.m - sum_d)
        else:
            condu = float('inf')  # 最好的情况condu = 0.0

        return condu, separability, density

        # 多跳_max_cliqu


if __name__ == "__main__":
    dataset1 = sys.argv[1]  # Network
    dataset2 = sys.argv[2]  # Ground True

    G = Graph(dataset1)
    with open(dataset2, 'r') as file:
        lines = file.readlines()

    lines_list = []
    for line in lines:
        line = line.strip()
        size = line.split('\t')
        if len(size) >= 3:
            lines_list.append(list(map(int, size)))
    lines_new = [[int(num) for num in sublist] for sublist in lines_list]

    avg_PPR_time = 0
    avg_PPR_size = 0
    avg_PPR_condu = 0
    avg_PPR_f1 = 0
    avg_PPR_precision = 0
    avg_PPR_recall = 0

    avg_HK_time = 0
    avg_HK_size = 0
    avg_HK_condu = 0
    avg_HK_f1 = 0
    avg_HK_precision = 0
    avg_HK_recall = 0
    
    avg_CSM_time = 0
    avg_CSM_size = 0
    avg_CSM_condu = 0
    avg_CSM_f1 = 0
    avg_CSM_precision = 0
    avg_CSM_recall = 0

    avg_TCP_time = 0
    avg_TCP_size = 0
    avg_TCP_condu = 0
    avg_TCP_f1 = 0
    avg_TCP_precision = 0
    avg_TCP_recall = 0

    avg_SM_time = 0
    avg_SM_size = 0
    avg_SM_condu = 0
    avg_SM_f1 = 0
    avg_SM_precision = 0
    avg_SM_recall = 0

    avg_LM_time = 0
    avg_LM_size = 0
    avg_LM_condu = 0
    avg_LM_f1 = 0
    avg_LM_precision = 0
    avg_LM_recall = 0

    avg_SCCS_time = 0
    avg_SCCS_size = 0
    avg_SCCS_condu = 0
    avg_SCCS_f1 = 0
    avg_SCCS_precision = 0
    avg_SCCS_recall = 0

    k = 25000
    alpha = 0.15
    t = 5
    epsilon = 1 / G.n
    hop = 3
    min_vertices = 300
    max_vertices = 5000
    num_columns_to_select = 50
    selected_columns = random.sample(lines_new, num_columns_to_select)
    num = 0

    for line in selected_columns:
        QID = int(random.choice(line))

        PPR_time, PPR_set = G.sweep_cut_PPR(alpha, epsilon)
        avg_PPR_time += PPR_time
        avg_PPR_size += len(PPR_set)
        PPR_condu, PPR_separability, PPR_density = G.metric(PPR_set)
        avg_PPR_condu += PPR_condu
        PPR_f1, PPR_precision, PPR_recall = G.calculate_f1_score(line, PPR_set)
        avg_PPR_f1 += PPR_f1
        avg_PPR_precision += PPR_precision
        avg_PPR_recall += PPR_recall

        HK_time, HK_set = G.sweep_cut_HK(t,epsilon)
        avg_HK_time += HK_time
        avg_HK_size += len(HK_set)
        HK_condu, HK_separability, HK_density = G.metric(HK_set)
        avg_HK_condu += HK_condu
        HK_f1, HK_precision, HK_recall = G.calculate_f1_score(line, HK_set)
        avg_HK_f1 += HK_f1
        avg_HK_precision += HK_precision
        avg_HK_recall += HK_recall

        CSM_time, CSM_set = G.Local_CSM()
        avg_CSM_time += CSM_time
        avg_CSM_size += len(CSM_set)
        CSM_condu, CSM_separability, CSM_density = G.metric(CSM_set)
        avg_CSM_condu += CSM_condu
        CSM_f1, CSM_precision, CSM_recall = G.calculate_f1_score(line, CSM_set)
        avg_CSM_f1 += CSM_f1
        avg_CSM_precision += CSM_precision
        avg_CSM_recall += CSM_recall

        TCP_time, TCP_set = G.truss_community()
        avg_TCP_time += TCP_time
        avg_TCP_size += len(TCP_set)
        TCP_condu, TCP_separability, TCP_density = G.metric(TCP_set)
        avg_TCP_condu += TCP_condu
        TCP_f1, TCP_precision, TCP_recall = G.calculate_f1_score(line, TCP_set)
        avg_TCP_f1 += TCP_f1
        avg_TCP_precision += TCP_precision
        avg_TCP_recall += TCP_recall

        SM_time, SM_set = G.subgraph_modularity()
        if len(SM_set) != 0:
            avg_SM_time += SM_time
            avg_SM_size += len(SM_set)
            SM_condu, SM_separability, SM_density = G.metric(SM_set)
            avg_SM_condu += SM_condu
            SM_f1, SM_precision, SM_recall = G.calculate_f1_score(line, SM_set)
            avg_SM_f1 += SM_f1
            avg_SM_precision += SM_precision
            avg_SM_recall += SM_recall
        else:
            num += 1

        LM_time, LM_set = G.local_modularity(k)
        avg_LM_time += LM_time
        avg_LM_size += len(LM_set)
        LM_condu, LM_separability, LM_density = G.metric(LM_set)
        avg_LM_condu += LM_condu
        LM_f1, LM_precision, LM_recall = G.calculate_f1_score(line, LM_set)
        avg_LM_f1 += LM_f1
        avg_LM_precision += LM_precision
        avg_LM_recall += LM_recall

        sample_S, sample_time = G.sample_subgraph(hop, min_vertices, max_vertices)
        C_adj_list = {}
        C_deg = {}
        volC = 0
        for u in sample_S:
            C_adj_list[u] = set(G.adj_list[u] & set(sample_S))
            C_deg[u] = len(C_adj_list[u])
            volC += C_deg[u]

        SCCS_time, SCCS_set = G.SCCS(2)
        avg_SCCS_time += SCCS_time + sample_time
        avg_SCCS_size += len(SCCS_set)
        SCCS_condu, SCCS_separability, SCCS_density = G.metric(SCCS_set)
        avg_SCCS_condu += SCCS_condu
        SCCS_f1, SCCS_precision, SCCS_recall = G.calculate_f1_score(line, SCCS_set)
        avg_SCCS_f1 += SCCS_f1
        avg_SCCS_precision += SCCS_precision
        avg_SCCS_recall += SCCS_recall

    print("avg_PPR_time: " + str(avg_PPR_time / num_columns_to_select))
    print("avg_PPR_size: " + str(avg_PPR_size / num_columns_to_select))
    print("avg_PPR_condu: " + str(avg_PPR_condu / num_columns_to_select))
    print("avg_PPR_f1: " + str(avg_PPR_f1 / num_columns_to_select))
    print("avg_PPR_precision: " + str(avg_PPR_precision / num_columns_to_select))
    print("avg_PPR_recall: " + str(avg_PPR_recall / num_columns_to_select) + '\n')

    print("avg_HK_time: " + str(avg_HK_time / num_columns_to_select))
    print("avg_HK_size: " + str(avg_HK_size / num_columns_to_select))
    print("avg_HK_condu: " + str(avg_HK_condu / num_columns_to_select))
    print("avg_HK_f1: " + str(avg_HK_f1 / num_columns_to_select))
    print("avg_HK_precision: " + str(avg_HK_precision / num_columns_to_select))
    print("avg_HK_recall: " + str(avg_HK_recall / num_columns_to_select) + '\n')

    print("avg_CSM_time: " + str(avg_CSM_time / num_columns_to_select))
    print("avg_CSM_size: " + str(avg_CSM_size / num_columns_to_select))
    print("avg_CSM_condu: " + str(avg_CSM_condu / num_columns_to_select))
    print("avg_CSM_f1: " + str(avg_CSM_f1 / num_columns_to_select))
    print("avg_CSM_precision: " + str(avg_CSM_precision / num_columns_to_select))
    print("avg_CSM_recall: " + str(avg_CSM_recall / num_columns_to_select) + '\n')

    print("avg_TCP_time: " + str(avg_TCP_time / num_columns_to_select))
    print("avg_TCP_size: " + str(avg_TCP_size / num_columns_to_select))
    print("avg_TCP_condu: " + str(avg_TCP_condu / num_columns_to_select))
    print("avg_TCP_f1: " + str(avg_TCP_f1 / num_columns_to_select))
    print("avg_TCP_precision: " + str(avg_TCP_precision / num_columns_to_select))
    print("avg_TCP_recall: " + str(avg_TCP_recall / num_columns_to_select) + '\n')

    print("num = " + str(num))
    print("avg_SM_time: " + str(avg_SM_time / num_columns_to_select))
    print("avg_SM_size: " + str(avg_SM_size / (num_columns_to_select - num)))
    print("avg_SM_condu: " + str(avg_SM_condu / (num_columns_to_select - num)))
    print("avg_SM_f1: " + str(avg_SM_f1 / (num_columns_to_select)))
    print("avg_SM_precision: " + str(avg_SM_precision / (num_columns_to_select)))
    print("avg_SM_recall: " + str(avg_SM_recall / (num_columns_to_select)) + '\n')

    print("avg_LM_time: " + str(avg_LM_time / num_columns_to_select))
    print("avg_LM_size: " + str(avg_LM_size / num_columns_to_select))
    print("avg_LM_condu: " + str(avg_LM_condu / num_columns_to_select))
    print("avg_LM_f1: " + str(avg_LM_f1 / num_columns_to_select))
    print("avg_LM_precision: " + str(avg_LM_precision / num_columns_to_select))
    print("avg_LM_recall: " + str(avg_LM_recall / num_columns_to_select) + '\n')

    print("avg_SCCS_time: " + str(avg_SCCS_time / num_columns_to_select))
    print("avg_SCCS_size: " + str(avg_SCCS_size / num_columns_to_select))
    print("avg_SCCS_condu: " + str(avg_SCCS_condu / num_columns_to_select))
    print("avg_SCCS_f1: " + str(avg_SCCS_f1 / num_columns_to_select))
    print("avg_SCCS_precision: " + str(avg_SCCS_precision / num_columns_to_select))
    print("avg_SCCS_recall: " + str(avg_SCCS_recall / num_columns_to_select) + '\n')







