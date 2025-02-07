# Coq Elpi plugin

This directory contains the OCaml code bridging Elpi and Coq.

The most interesting file is [rocq_elpi_HOAS.ml](rocq_elpi_HOAS.ml) where
conversions for term, context and evar_map are provided.

The exposed Coq API is in [rocq_elpi_builtins.ml](rocq_elpi_builtins.ml).

