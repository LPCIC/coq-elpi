module Graph :
  sig
    type 'a node = {
      mutable pred : 'a node list;
      name : 'a;
      mutable succ : 'a node list;
    }
    type 'a graph = { nodes : ('a, 'a node) Hashtbl.t; }
    exception Graph_with_cycle
    
    val build_graph : ('a * 'a list) list -> 'a graph
    val topo_sort : 'a graph -> 'a node list
    val print_node : ('a -> unit) -> 'a node -> unit
    val print_graph : ('a -> unit) -> 'a graph -> unit
  end
