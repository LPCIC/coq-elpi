cat > dune <<EOF
(env
 (dev
  (env-vars
   (COQ_ELPI_ATTRIBUTES "test=yes,str=\"some-string\""))))

(coq.theory
 (name test)
 (theories elpi))
EOF

cat > dune-project <<EOF
(lang dune 3.13)
(using coq 0.8)
EOF

export COQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
export DUNE_CACHE=disabled
