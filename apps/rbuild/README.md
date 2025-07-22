## RBuild

RBuild implements a handy syntax to build/update records, see
the [example](examples/usage_rbuild.v) file. In short
`« a := v; b := r »` and
`« r with a := v »` without an explicit mention of the recrod type/constructor.

This app is experimental.

### Ideas

- update not based on lenses, i.e.
  `« x with a := v »` epands to
  `« a := v; ... fi := x.(fi) ...  »` that is a special case of
  `« ... »` when some fields are missing (instead of error user a default):
  - pros: works even if lenses don't (dependent records)
  - cons: no lemmas from lenses
- when a record is dependent, eg `Record r := { t : Type; op : t -> t -> t }`
  one could accept `« r with op := f »` and expand it to
  `« r with t := _ ; op := f »`
- liquid fields, eg `« .b := v »` to mean any field called `b` (possibly deep)

