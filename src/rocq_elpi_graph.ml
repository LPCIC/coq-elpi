module Node = struct 
  type 'a t = {
    mutable pred : 'a t list;
    name : 'a;
    mutable succ : 'a t list;
  }

  let init name = { pred = []; name; succ = [] }

  let remove_succ rem_node n =
    n.succ <- List.filter (fun succ -> succ.name <> rem_node.name) n.succ

  let add_succ current succ =
    current.succ <- succ :: current.succ;
    succ.pred <- current :: succ.pred

  let remove_pred rem_node n =
    n.pred <- List.filter (fun pred -> pred.name <> rem_node.name) n.pred

  let clear node = node.pred <- []; node.succ <- []

  let remove current =
    List.iter (fun succ -> remove_pred current succ) current.succ;
    List.iter (fun pred -> remove_succ current pred) current.pred;
    clear current

  let print pf n =
    let pf e = Printf.sprintf "%s " (pf e.name) in
    let pf_fold e = List.fold_left (fun acc e -> Printf.sprintf "%s%s, " acc (pf e)) "" e in 
    Printf.printf "%s : [ succ: %s ;; pred : %s ]\n%!" 
      (pf n) (pf_fold n.succ) (pf_fold n.pred);
end

module Graph = struct

  type 'a graph = { nodes : ('a, 'a Node.t) Hashtbl.t }

  exception Invalid_graph of string

  let rec queue_to_list q =
    if Queue.is_empty q then []
    else
      let elt = Queue.pop q in
      elt :: queue_to_list q

  let add_node graph node_name = 
    if Hashtbl.mem graph.nodes node_name then 
      raise (Invalid_graph "The nodes of the graph should be unique") 
    else 
    let node = Node.init node_name in 
    Hashtbl.add graph.nodes node_name node;
    node

  (* 
    We can build the graph from a list of type (A, B) : ('a * 'a list)
    where A is a node and B is the list of its successors
  *)
  let build l : 'a graph =
    let graph = { nodes = Hashtbl.create (List.length l) } in
    List.iter (fun (node, _) -> add_node graph node |> ignore) l;
    List.iter
      (fun (current_name, succ_names) ->
        let current = Hashtbl.find graph.nodes current_name in
        List.iter
          (fun succ_name ->
              let succ = 
                try Hashtbl.find graph.nodes succ_name 
                with Not_found -> add_node graph succ_name in 
              Node.add_succ current succ
            )
          succ_names)
      l;
    graph

  let topo_sort graph : 'a list =
    let res = Queue.create () in
    let to_treat = Queue.create () in
    Hashtbl.iter
      (fun _ (n: 'a Node.t) -> if List.length n.pred = 0 then Queue.add n to_treat)
      graph.nodes;
    while Queue.is_empty to_treat |> not do
      let current_node = Queue.pop to_treat in
      Queue.push current_node.name res;
      let succ = current_node.succ in
      Node.remove current_node;
      List.iter
        (fun (succ: 'a Node.t) -> if List.length succ.pred = 0 then Queue.push succ to_treat)
        succ
    done;
    if Queue.length res <> Hashtbl.length graph.nodes then 
      raise (Invalid_graph "Cannot do topological sort on cyclic graph")
    else queue_to_list res

  let print pf g =
    Hashtbl.iter (fun _ n -> Node.print pf n)
      g.nodes
end