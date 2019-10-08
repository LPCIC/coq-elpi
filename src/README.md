# Coq Elpi plugin

This directory contains the OCaml code bridging Elpi and Coq.

The most interesting file is [coq_elpi_HOAS.ml](coq_elpi_HOAS.ml) where
conversions for term, context and evar_map are provided.

The exposed Coq API is in [coq_elpi_builtins.ml](coq_elpi_builtins.ml).

