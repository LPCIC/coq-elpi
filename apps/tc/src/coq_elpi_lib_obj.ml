let add_obj_no_discharge name cache =
  Libobject.(declare_object 
    (global_object_nodischarge name ~cache ~subst:None))