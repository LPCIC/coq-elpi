
if coqc --print-version | cut -d ' ' -f 1 | grep -q "^9" ; then STDLIB="Stdlib"; else STDLIB=""; fi

if [ -z "$DEPS" ]; then DEPS="elpi_elpi elpi $STDLIB"; else DEPS="elpi_elpi elpi $STDLIB $DEPS"; fi

cat > dune <<EOF
(env
 (dev
  (env-vars
   (COQ_ELPI_ATTRIBUTES "test=yes,str=\"some-string\""))))

(coq.theory
 (name test)
 (theories ${DEPS}))
EOF

cat > dune-project <<EOF
(lang dune 3.13)
(using coq 0.8)
EOF

if ocamlfind query rocq-core; then
  export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
else
  export COQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
fi
export DUNE_CACHE=disabled
