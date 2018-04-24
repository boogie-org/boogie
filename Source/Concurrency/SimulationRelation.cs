using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Boogie.GraphUtil;

namespace Microsoft.Boogie
{
    /// <summary>
    /// Implements the simulation relation algorithm from the paper:
    ///   Monika Rauch Henzinger, Thomas A. Henzinger, Peter W. Kopke
    ///   Computing Simulations on Finite and Infinite Graphs
    ///   FOCS 1995
    /// </summary>
    /// <typeparam name="A">node type of graph A</typeparam>
    /// <typeparam name="B">node type of graph B</typeparam>
    /// <typeparam name="L">type of edge labels</typeparam>
    public class SimulationRelation<A, B, L>
    {
        class Graph<T>
        {
            HashSet<T> nodes;
            Dictionary<T, Dictionary<L, List<T>>> successors;
            Dictionary<T, Dictionary<L, List<T>>> predecessors;

            public Graph(List<Tuple<T, L, T>> edges)
            {
                nodes = new HashSet<T>();
                successors = new Dictionary<T, Dictionary<L, List<T>>>();
                predecessors = new Dictionary<T, Dictionary<L, List<T>>>();
                foreach (Tuple<T, L, T> edge in edges)
                {
                    T source = edge.Item1;
                    L label = edge.Item2;
                    T dest = edge.Item3;
                    nodes.Add(source);
                    nodes.Add(dest);
                    if (!successors.ContainsKey(source))
                    {
                        successors[source] = new Dictionary<L, List<T>>();
                    }
                    if (!successors[source].ContainsKey(label))
                    {
                        successors[source][label] = new List<T>();
                    }
                    if (!predecessors.ContainsKey(dest))
                    {
                        predecessors[dest] = new Dictionary<L, List<T>>();
                    }
                    if (!predecessors[dest].ContainsKey(label))
                    {
                        predecessors[dest][label] = new List<T>();
                    }
                    successors[source][label].Add(dest);
                    predecessors[dest][label].Add(source);
                }
            }

            public IEnumerable<T> Nodes { get { return nodes; } }

            public IEnumerable<T> Post(T t, L l)
            {
                if (successors.ContainsKey(t) && successors[t].ContainsKey(l))
                {
                    return successors[t][l];
                }
                else
                {
                    return Enumerable.Empty<T>();
                }
            }

            public IEnumerable<T> Post(IEnumerable<T> set, L l)
            {
                return set.Select(x => Post(x, l)).Aggregate(Enumerable.Empty<T>(), (p, q) => p.Concat(q));
            }

            public IEnumerable<T> Pre(T t, L l)
            {
                if (predecessors.ContainsKey(t) && predecessors[t].ContainsKey(l))
                {
                    return predecessors[t][l];
                }
                else
                {
                    return Enumerable.Empty<T>();
                }
            }

            public IEnumerable<T> Pre(IEnumerable<T> set, L l)
            {
                return set.Select(x => Pre(x, l)).Aggregate(Enumerable.Empty<T>(), (p, q) => p.Concat(q));
            }

            public IEnumerable<L> PostLabels(T t)
            {
                if (successors.ContainsKey(t))
                {
                    return successors[t].Keys;
                }
                else
                {
                    return Enumerable.Empty<L>();
                }
            }

            public IEnumerable<L> PreLabels(T t)
            {
                if (predecessors.ContainsKey(t))
                {
                    return predecessors[t].Keys;
                }
                else
                {
                    return Enumerable.Empty<L>();
                }
            }
        }

        Graph<A> aGraph;
        Graph<B> bGraph;
        Dictionary<A, HashSet<B>> initialConstraints;

        public SimulationRelation(List<Tuple<A, L, A>> aEdges, List<Tuple<B, L, B>> bEdges, Dictionary<A, HashSet<B>> initialConstraints)
        {
            this.aGraph = new Graph<A>(aEdges);
            this.bGraph = new Graph<B>(bEdges);
            this.initialConstraints = initialConstraints;
        }

        public Dictionary<A, HashSet<B>> ComputeSimulationRelation()
        {
            Dictionary<A, HashSet<B>> prevsim;
            Dictionary<A, HashSet<B>> sim;
            Dictionary<Tuple<A, L>, HashSet<B>> remove;
            Queue<Tuple<A,L>> workQueue;

            prevsim = new Dictionary<A, HashSet<B>>();
            sim = new Dictionary<A, HashSet<B>>();
            remove = new Dictionary<Tuple<A, L>, HashSet<B>>();
            workQueue = new Queue<Tuple<A,L>>();
            foreach (var a in aGraph.Nodes)
            {
                prevsim[a] = new HashSet<B>(bGraph.Nodes);
                sim[a] = new HashSet<B>();
                HashSet<L> aOutgoingLabels = new HashSet<L>(aGraph.PostLabels(a));
                foreach (var b in bGraph.Nodes)
                {
                    IEnumerable<L> bOutgoingLabels = bGraph.PostLabels(b);
                    if (aOutgoingLabels.IsSubsetOf(bOutgoingLabels))
                    {
                        sim[a].Add(b);
                    }
                }
                if (initialConstraints.ContainsKey(a))
                {
                    sim[a].IntersectWith(initialConstraints[a]);
                }

                foreach (var l in aGraph.PreLabels(a))
                {
                    Tuple<A, L> x = new Tuple<A, L>(a, l);
                    remove[x] = new HashSet<B>(bGraph.Pre(prevsim[a], l).Except(bGraph.Pre(sim[a], l)));
                    if (remove[x].Count > 0)
                    {
                        workQueue.Enqueue(x);
                    }
                }
            }

            while (workQueue.Count > 0)
            {
                Tuple<A,L> x = workQueue.Dequeue();
                A v = x.Item1;
                foreach (A u in aGraph.Pre(v, x.Item2))
                {
                    foreach (B w in remove[x])
                    {
                        if (sim[u].Contains(w))
                        {
                            sim[u].Remove(w);
                            foreach (L l in bGraph.PreLabels(w))
                            {
                                foreach (B b in bGraph.Pre(w, l))
                                {
                                    if (bGraph.Post(b, l).Intersect(sim[u]).Count() == 0)
                                    {
                                        Tuple<A, L> z = new Tuple<A, L>(u, l);
                                        if (!remove.ContainsKey(z))
                                            remove[z] = new HashSet<B>();
                                        remove[z].Add(b);
                                        workQueue.Enqueue(z);
                                    }
                                }
                            }
                        }
                    }
                }
                prevsim[v] = new HashSet<B>(sim[v]);
                remove[x] = new HashSet<B>();
            }

            return sim;
        }
    }
}
