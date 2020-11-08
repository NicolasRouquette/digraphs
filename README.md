# Directed graphs in [Lean](https://leanprover-community.github.io/index.html)

This is adapted for Lean 3.23.0 based on Nick Scheel's gist:
https://gist.github.com/MonoidMusician/1c8cc2ec787ebaf91b95d67cbc5c3498

Scheel formalized the watershed condition for a directed graph
based on a [2018 midterm exam](http://www-users.math.umn.edu/~dgrinber/comb2/mt3.pdf) 
in Prof. Darij Grinber's Math 4707 class at the University of Minnesota, briefly:


```lean
def arcT (V : Type) : Type := V × V

structure digraph (V E : Type) : Type :=
  mk :: (φ : E → arcT V)
```

## 1) Constructing examples of directed graphs

To construct a directed graph, we need three things:
- A type `V` of vertices
- A type `E` of edges
- A mapping `E → arcT V`

### 1.1) Defining `V` and `E` as subsets of strings

See [src/data-as-subsets.lean](src/data-as-subsets.lean)

### 1.2) Defining `V` and `E` as subtypes of strings

See [src/data-as-subsets.lean](src/data-as-subtypes.lean)

## 2) Constructing a mapping

A single-edge mapping seems ok; however, the following definition is incorrect because
it is not a total function for all possible values of `eT`:

```lean
def phi1: eT → arcT vT
| e1 := arc1
```

However, defining a total function on `eT` produces errors:

```lean
def phi2: eT → arcT vT
| e1 := arc1
| e2 := arc2
| e3 := arc3
```

Error on the 2nd line is:

```
equation compiler error, equation #2 has not been used in the compilation, note that the left-hand-side of equation #1 is a variable
```


## Questions

#### Convenience constructor for an instance of a subset or subtype 

* Q1 How can we write a convenience constructor for `vt_a`,... `vt_d` below?

```lean
def vs : list string := ["a", "b", "c", "d"]
def isV (s: string) : Prop := s ∈ vs
def vT := {s:string // isV s}

def vt_a : vT := ⟨ "a", begin refine list.nth_mem _, let n := 0, exact n, exact rfl, end⟩
def vt_b : vT := ⟨ "b", begin refine list.nth_mem _, let n := 1, exact n, exact rfl, end⟩
def vt_c : vT := ⟨ "c", begin refine list.nth_mem _, let n := 2, exact n, exact rfl, end⟩
def vt_d : vT := ⟨ "d", begin refine list.nth_mem _, let n := 3, exact n, exact rfl, end⟩
```

* Q2: How can I define a mapping properly with the equation compiler?


```lean
def phi2: eT → arcT vT
| e1 := arc1
| e2 := arc2
| e3 := arc3
```

* Q3: How to verify propositions?

For example, the library defines:

```lean
def has_arc
    {V E : Type} (G : digraph V E)
    (v1 v2 : V) : Prop :=
        ∃ (e : E), G.φ e = arcT.mk v1 v2
```

The following is not very helpful because it just says the expression has type `Prop`:

```
#check has_arc g1 vt_a
```

Is there a way to evaluate what the proposition is?

