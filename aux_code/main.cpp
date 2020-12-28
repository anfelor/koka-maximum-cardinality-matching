#include <iostream>
#include <cstdlib>
#include <variant>
#include <algorithm>
#include <set>

#include "graph.hpp"

const std::size_t none = std::numeric_limits<size_t>::max();
const std::pair<size_t, size_t> noedge = {none, none};

class Matching {
public:
   Matching(std::size_t num_nodes):
      _match(num_nodes, none) {};

   ED::NodeId matching(ED::NodeId n) const {
      return _match[n];
   }

   void unmatch(ED::NodeId n) {
      if(_match[n] != none) {
         _match[_match[n]] = none;
      }
      _match[n] = none;
   }

   void match(ED::NodeId n, ED::NodeId m) {
      unmatch(n);
      unmatch(m);
      _match[n] = m;
      _match[m] = n;
   }

   ED::NodeId find_exposed(const std::vector<bool>& to_ignore) const {
      for(ED::NodeId n = 0; n < _match.size(); n++) {
         if(_match[n] == none && (!to_ignore[n])) {
            return n;
         }
      }
      return none;
   }

   std::size_t num_nodes() const {
      return _match.size();
   }

   std::size_t cardinality() const {
      std::size_t card = 0;
      for(auto &c : _match) {
         if(c != none) card++;
      }
      return card / 2;
   }
private:
   std::vector<ED::NodeId> _match;
};

class Components {
public:
   Components(std::size_t num_nodes):
      _card(num_nodes, 0), _id(num_nodes, 0) {
      for(std::size_t i = 0; i < num_nodes; ++i) {
         _id[i] = i;
      }
   };

   void merge(ED::NodeId x, ED::NodeId y) {
      auto x_ = id(x);
      auto y_ = id(y);
      if(_card[x_] < _card[y_]) {
         _id[x_] = y_;
         _card[y_] += _card[x_];
      } else { 
         _id[y_] = x_;
         _card[x_] += _card[y_];
      }
   }

   // The combined cost of k calls to this function
   // is O(nlog(n) + k), since the recursion can only
   // happen more than once if x was in the smaller component during a merge
   // (which can only happen log(n) times for each node).
   ED::NodeId id(ED::NodeId x) {
      if(x != _id[x]) {
         _id[x] = id(_id[x]);
      }
      return _id[x];
   }
private:
   std::vector<std::size_t> _card;
   std::vector<ED::NodeId> _id;
};

typedef std::pair<ED::NodeId, ED::NodeId> Edge;
typedef std::tuple<ED::NodeId, std::vector<bool>, std::vector<bool>> EvenOddTree;

// The first element is the apex (e.g. the node of the cycle
// highest up in the tree at the moment of creation).
// The second element are the edges. Since we use pseudo-nodes
// each node is given by the endpoint of its entering edges.
typedef std::pair<std::pair<ED::NodeId, ED::NodeId>, std::vector<Edge>> Cycle;

void reverse(std::vector<Edge> &c) {
   std::reverse(c.begin(), c.end());
   for(auto j = c.begin(); j != c.end(); ++j) {
      *j = {j->second, j->first};
   }
}

// Unlike in the presentation in the lecture, we don't actually
// shrink and unshrink. Instead we save the cycles and "unshrink"
// by finding an M-augmenting path in each cycle to align the
// near-perfect matching correctly.
class Unshrinking {
public:
   Unshrinking(std::size_t num_nodes): matched_cycle(num_nodes, none) {};

   void add_cycle(const Matching &m, Cycle &c) {
      cycles.push_back(c);
      for(auto i = c.second.begin(); i != c.second.end(); ++i) {
         if(m.matching(i->first) == i->second) {
            matched_cycle[i->first] = cycles.size() - 1; 
            matched_cycle[i->second] = cycles.size() - 1; 
         }
      }
   }

   // Unshrink the matching cycle for a node R(x), where
   // x has an incident matching edge into R(x).
   void unshrink(Matching &m, Components &c, ED::NodeId x) {
      std::set<size_t> expanded;
      unshrink_go(m, c, x, expanded);
   }

   void unshrink_go(Matching &m, Components &c, ED::NodeId x, std::set<size_t> &expanded) {
      auto y = m.matching(x);
      auto comp = c.id(x);
      auto mc = matched_cycle[x];
      if(y == none || c.id(y) != comp || expanded.find(mc) != expanded.end()) return;
      expanded.insert(mc);
      auto &cyc = cycles[mc];

      auto pos = none;
      for(auto i = cyc.second.begin(); i != cyc.second.end(); ++i) {
         if(i->first == x && i->second == y) {
            pos = std::distance(cyc.second.begin(), i);
            break;
         }
         if(i->second == x && i->first == y) {
            pos = std::distance(i, cyc.second.end()) - 1;
            reverse(cyc.second);
            break;
         }
      }

      auto next = cyc.second.begin() + pos;
      auto match_next = false;
      while(next->first != cyc.first.first && next->first != cyc.first.second) {
         if(match_next) {
            if(matched_cycle[next->first] != mc) {
               unshrink_go(m, c, next->first, expanded);
            }
            if(matched_cycle[next->second] != mc) {
               unshrink_go(m, c, next->second, expanded);
            }
            m.match(next->first, next->second);
         }
         match_next = !match_next;
         next++;
         if(next == cyc.second.end()) {
            next = cyc.second.begin();
         }
      }
   }
private:
   std::vector<Cycle> cycles;
   std::vector<size_t> matched_cycle;
};

void add_neighbors(std::vector<Edge> &L, const ED::Graph &g, ED::NodeId x, const std::vector<bool>& to_ignore) {
   for(auto& y : g.node(x).neighbors()) {
      if(to_ignore[y]) continue;
      L.push_back({x, y});
   }
}

// Find the path P between x and y in the tree given by pred \circ s.id
// in time O(|P|*log(|P|))
Cycle find_cycle(std::vector<Edge> &pred, Components &s, ED::NodeId x, ED::NodeId y) {
   std::vector<Edge> from_x = {{x, x}};
   std::set<ED::NodeId> visited_x = {s.id(x)};
   std::vector<Edge> from_y = {{y, y}};
   std::set<ED::NodeId> visited_y = {s.id(y)};
   while(true) {
      auto comp = [&s](Edge e) { return s.id(e.second); };
      auto merge = [&s, &comp](std::vector<Edge> &fr, std::vector<Edge> &ba) {
         auto i = std::find_if(fr.begin(), fr.end(), [&](const Edge x) {return comp(x) == comp(ba.back());});
         fr.erase(i+1, fr.end());
         Edge apex = {fr.back().second, ba.back().second};
         reverse(ba);
         fr.insert(fr.end(), ba.begin(), ba.end());
         fr[0] = {fr.back().second, fr[0].first}; // [{x,x} .... {y,y}] -> [{y, x} ...]
         fr.pop_back();
         return Cycle{apex, fr};
      };
      auto push = [&comp](Edge x, std::vector<Edge> &from, std::set<ED::NodeId> &visited) {
         if(x != noedge) {
            from.push_back(x);
            visited.insert(comp(x));
         }
      };
      if(visited_x.find(comp(from_y.back())) != visited_x.end()) {
         return merge(from_x, from_y);
      }
      if(visited_y.find(comp(from_x.back())) != visited_y.end()) {
         return merge(from_y, from_x);
      }
      auto x = pred[comp(from_x.back())];
      auto y = pred[comp(from_y.back())];
      push(x, from_x, visited_x);
      push(y, from_y, visited_y);
   }
}

// This returns the root of the tree, if no perfect matching could be found.
// Else, it just builds up the matching and ends without output.
std::optional<EvenOddTree> perfect_matching(const ED::Graph &g, Matching &m, const std::vector<bool>& to_ignore) {
   restart: // TCO does not fire here, so we use it manually
   ED::NodeId r = m.find_exposed(to_ignore);
   if(r == none) {
      return {};
   }

   Components c(g.num_nodes());
   Unshrinking u(g.num_nodes());

   // A node in G is even if it is in a (node in G') in Even(T)
   std::vector<bool> is_even(g.num_nodes(), false);
   is_even[r] = true;

   // A node in G is odd if it is in Odd(T)
   std::vector<bool> is_odd(g.num_nodes(), false);

   // The edge connecting to the predecessor in the tree.
   // Note that the first entry of the edge is the node from
   // which the current pseudo-node is left from.
   std::vector<Edge> pred(g.num_nodes(), noedge);
   std::vector<Edge> L;
   add_neighbors(L, g, r, to_ignore);

   while(! L.empty()) {
      auto [ x, y ] = L.back();
      L.pop_back();

      if(is_odd[y]) continue;
      if(c.id(x) == c.id(y)) continue;

      if(! is_even[y]) {
         auto z = m.matching(y);
         pred[c.id(y)] = {y, x};
         if(z == none) {
            while(y != none) {
               auto e = pred[c.id(y)];
               u.unshrink(m, c, e.second);
               m.match(e.first, e.second);
               y = pred[c.id(e.second)].second;
            };
            goto restart;
         } else {
            is_odd[y] = true;
            is_even[z] = true;
            pred[c.id(z)] = {z, y};
            add_neighbors(L, g, z, to_ignore);
         }
      } else {
         auto cycle = find_cycle(pred, c, x, y);
         auto apex_pred = pred[c.id(cycle.first.first)];
         for(auto i = cycle.second.begin(); i != cycle.second.end(); ++i) {
            if(is_odd[i->first]) {
               add_neighbors(L, g, i->first, to_ignore);
               is_even[i->first] = true;
               is_odd[i->first] = false;
            }
            c.merge(i->first, i->second);
         }
         pred[c.id(cycle.first.first)] = apex_pred;
         u.add_cycle(m, cycle);
      }
   }
   return EvenOddTree{r, is_even, is_odd};
}

Matching max_cardinality_matching(const ED::Graph& g) {
   std::vector<bool> to_ignore(g.num_nodes(), false);
   Matching m(g.num_nodes());
   while(true) {
      auto frtree = perfect_matching(g, m, to_ignore);
      if(frtree) { // we have a frustrated tree with root r
         auto [r, is_even, is_odd] = frtree.value();
         to_ignore[r] = true;
         for(ED::NodeId i = 0; i < g.num_nodes(); i++) {
            if(is_even[i] || is_odd[i]) {
               to_ignore[i] = true;
            }
         }
      } else { // there is no exposed, non-ignored node in the graph
         return m;
      }
   }
}

ED::Graph from_matching(const Matching& m) {
   auto g = ED::Graph(m.num_nodes());
   for(ED::NodeId x = 0; x < m.num_nodes(); ++x) {
      auto y = m.matching(x);
      if(y != none && x < y) {
         g.add_edge(x, y);
      }
   }
   return g;
}

int main(int argc, char** argv)
{
   if (argc != 2)
   {
      std::cerr << "Wrong number of arguments. Program call: <program_name> <input_graph>" << std::endl;
      return EXIT_FAILURE;
   }
   ED::Graph graph = ED::Graph::build_graph(argv[1]);
   auto m = max_cardinality_matching(graph);
   std::cout << m.cardinality() << std::endl;
   // std::cout << from_matching(m);
   return EXIT_SUCCESS;
}
