import .graph

-- The list of unique vertex identifiers.
def vs : list string := ["a", "b", "c", "d"]
def isV (s: string) : Prop := s ∈ vs

-- vT is the set of strings that are vertex identifiers.
-- Defining vT as a subtype, {s:string // isV s}, would require defining a
-- typeclass instance for has_lift_t vT string
def vT := {s:string | isV s}

-- The elements of vT are pairs: a string s and a proof that it satisfies isV s
def vt_a : vT := ⟨ "a", begin refine list.nth_mem _, let n := 0, exact n, exact rfl, end⟩
def vt_b : vT := ⟨ "b", begin refine list.nth_mem _, let n := 1, exact n, exact rfl, end⟩
def vt_c : vT := ⟨ "c", begin refine list.nth_mem _, let n := 2, exact n, exact rfl, end⟩
def vt_d : vT := ⟨ "d", begin refine list.nth_mem _, let n := 3, exact n, exact rfl, end⟩


-- The list of unique edge identifiers.
def es : list string := [ "e1", "e2", "e3" ]
def isE (e: string) : Prop := e ∈ es

-- eT is the set of strings that are edge identifiers.
-- Defining eT as a subtype, {s:string // isE s}, would require defining a
-- typeclass instance for has_lift_t eT string
def eT := { e:string | isE e }

-- The elements of eT are pairs: a string s and a proof that it satisfies isE s
def e1 : eT := ⟨ "e1", begin refine list.nth_mem _, let n := 0, exact n, exact rfl, end ⟩
def e2 : eT := ⟨ "e2", begin refine list.nth_mem _, let n := 1, exact n, exact rfl, end ⟩
def e3 : eT := ⟨ "e3", begin refine list.nth_mem _, let n := 2, exact n, exact rfl, end ⟩

-- The type of directed graphs with vertices in vT and edges in eT
def gT := digraph vT eT

def arc1 : arcT vT := arcT.mk vt_a vt_b
def arc2 : arcT vT := arcT.mk vt_a vt_c
def arc3 : arcT vT := arcT.mk vt_c vt_d

def phi1: eT → arcT vT
| e1 := arc1

def g1 : gT := digraph.mk phi1

def e1_source := digraph.source g1 e1
#eval e1_source
-- result: "a"

def phi2: eT → arcT vT
| e1 := arc1
| e2 := arc2
| e3 := arc3

def g2 : gT := digraph.mk phi2

