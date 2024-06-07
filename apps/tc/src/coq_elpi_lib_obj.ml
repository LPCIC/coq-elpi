let add_obj_no_discharge name cache =
  Libobject.(declare_object 
    (global_object_nodischarge name ~cache ~subst:None))

let add_superobj_no_discharge name cache =
  Libobject.(declare_object 
    (superglobal_object_nodischarge name ~cache ~subst:None))