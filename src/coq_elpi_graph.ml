module Graph = struct
  type 'a node = {
    mutable pred : 'a node list;
    name : 'a;
    mutable succ : 'a node list;
  }

  type 'a graph = { nodes : ('a, 'a node) Hashtbl.t }

  exception Graph_with_cycle

  let rec queue_to_list q =
    if Queue.is_empty q then []
    else
      let elt = Queue.pop q in
      elt :: queue_to_list q

  let init_node name = { pred = []; name; succ = [] }

  let remove_succ rem_node n =
    n.succ <- List.filter (fun succ -> succ.name <> rem_node.name) n.succ

  let add_succ pred succ =
    pred.succ <- succ :: pred.succ;
    succ.pred <- pred :: succ.pred

  let remove_pred rem_node n =
    n.pred <- List.filter (fun pred -> pred.name <> rem_node.name) n.pred

  let remove_node node =
    List.iter
      (fun n ->
        remove_pred node n;
        remove_succ node n)
      node.succ

  (* 
    We can build the graph from a list of type (A, B) : ('a * 'a list)
    where A is a node and B is the list of its successors
  *)
  let build_graph l : 'a graph =
    let graph = { nodes = Hashtbl.create (List.length l) } in
    List.iter (fun (node, _) -> Hashtbl.add graph.nodes node (init_node node)) l;
    List.iter
      (fun (node_name, dep_names) ->
        let prev = Hashtbl.find graph.nodes node_name in
        List.iter
          (fun succ_name ->
            try
              let succ = Hashtbl.find graph.nodes succ_name in
              add_succ prev succ
            with Not_found -> ())
          dep_names)
      l;
    graph

  let topo_sort graph : 'a node list =
    let res = Queue.create () in
    let to_treat = Queue.create () in
    Hashtbl.iter
      (fun _ n -> if List.length n.pred = 0 then Queue.add n to_treat)
      graph.nodes;
    while Queue.is_empty to_treat |> not do
      let current_node = Queue.pop to_treat in
      Queue.push current_node res;
      let succ = current_node.succ in
      remove_node current_node;
      List.iter
        (fun succ -> if List.length succ.pred = 0 then Queue.push succ to_treat)
        succ
    done;
    if Queue.length res <> Hashtbl.length graph.nodes then raise Graph_with_cycle
    else queue_to_list res

  let print_node pf n =
    let pf e =
      pf e.name;
      print_string ","
    in
    pf n;
    print_string "[ succ: ";
    List.iter pf n.succ;
    print_string " ;; pred: ";
    List.iter pf n.pred;
    print_string "]"

  let print_graph pf g =
    Hashtbl.iter
      (fun _ n ->
        print_node pf n;
        print_string "\n")
      g.nodes
end
