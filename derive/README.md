# Derive

This directory contains the elpi files implementing various automatic
derivation of terms.  The corresponding .v files, defining the Coq commands,
are in `theories/derive/`.


![Big picture](derive.svg)

## derive.isK

Given an inductive `I` type it generates for each constructor `K` a function to `bool` names `${prefix}K` where `prefix` is `is` by default. The type of `isK` is `forall params idxs, I params idxs -> bool`. Example:
```coq
Elpi derive.isK list. Print isnil. (*
isnil = 
  fun (A : Type) (i : list A) =>
    match i with
    | nil => true
    | (_ :: _)%list => false
    end
*)
```
coverage: ?? full CIC

