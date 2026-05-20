# Preliminaries

In the following, CA, CB, … will implicitly denote the type of complexity
bounds for elements of type A.

# On the type of complexity bounds

The complexity bounds for functions of type (A -> B) is ℂI A -> ℂO B, where:

1. ℂI A bundles a value of type A and a complexity bound of type CA.
2. It seems that ℂI A should also bundle a proof that the complexity bound
  is indeed a complexity bound for the value it contains.
  An example where this seems to be required is the complexity of the List.tl
  function, where we need to know that the complexity bound of the input list
  is related to the input list itself, as it should be a list of the same length.
3. On the other hand, ℂO bundles:
  + a cost (say in nat for now)
  + the complexity bound for the ouput.
4. It feels like ℂO should also contain the output value and the related
   complexity proof, because of 2. and to allow composition of functions.
   So maybe ℂO B should really be nat * ℂI B.

# First-order bounds
It might be possible to build a cost model that only applies to first-order
functions, so that complexity bounds for ground-types can safely be ignored.
