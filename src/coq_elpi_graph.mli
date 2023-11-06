module Graph :
  sig
    type 'a graph 
    exception Invalid_graph of string
    val build : ('a * 'a list) list -> 'a graph
    val topo_sort : 'a graph -> 'a list
    val print : ('a -> string) -> 'a graph -> unit
  end
