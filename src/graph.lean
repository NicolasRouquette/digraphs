-- A basic framework for graph theory on multidigraphs in Lean
-- and a proof that no_watershed_condition is sufficient to
-- establish that a graph has a unique sink for each vertex
--
-- I hope to give some introduction to the syntax of how Lean works here,
-- but I assume some familiarity with functions, pattern matching,
-- type theory, and proofs.
--
-- The most important thing to note is that `begin` and `end` delineate
-- sections of code in "tactic/interactive proof mode" (as opposed to
-- "term mode"). The Lean compiler shows the proof goal and the available
-- assumptions and context, and then shows how it changes after tactics
-- are executed. The best way to see this happen is to download Lean from
-- the following links and open it in VSCode (or emacs) and walk through
-- the steps of a proof to see the changes.
--
-- VSCode: "Typing ctrl-shift-enter opens up a message window which shows you
-- error messages, warnings, output, and goal information when in tactic mode."
-- Emacs: "C-c C-g	show goal in tactic proof (lean-show-goal-at-pos)"
-- (https://leanprover.github.io/reference/using_lean.html)
--
-- Make sure to create a project folder and install mathlib as explained here:
-- https://leanprover.github.io/reference/using_lean.html#using-the-package-manager
--
-- http://leanprover.github.io/
-- https://github.com/leanprover/lean

-- Quick primer on Lean:
--
-- Propositions are types. This means that the mathematical language of Lean is
-- the language of types, which can encode any sensical sentence about math.
-- Types are, of course, also used in the design of computable programming
-- languages, which Lean also is. But "mere" propositions don't contain data
-- to compute on: only the type of a proof matters, really, not its exact details.
--
-- The term language and the type language are the same, which means that values
-- can be mentioned in types, and vice-versa. This is a result of dependent type
-- theory, and it allows encoding interesting propositions, such as about the value
-- of functions: given some (f : ℝ → ℝ), (∀ x : ℝ, x > 0 → f x = 0) is the
-- proposition that, for positive values of `x`, `f x` evaluates to zero. Note that
-- `f` is a fixed value, and `x` is a variable value, both mentioned at the type level.
--
-- ∀ is actually the same thing as Π – they are notation for dependently-typed
-- functions. (f : Π (a : α), β a) is a function that takes an element `a` of type `α`
-- and returns a result that `β a`, with a type that can depend on the value of `a`.
-- Putting this together, if we have `f` as above, and some `v : α`, then `f v : β v`
-- (meaning, the value of `f` applied to `v` has type `β v`).
-- If `β a` does _not_ depend on `a` (that is, if `β` is a constant function, say,
-- β = λ _, γ), then the type of `f` can be written as `α → γ`, the type of a
-- non-dependent function, also familiar as implication from logic.
-- The cool bit about dependent functions, though, is that they are also used to
-- introduce polymorphism, if `α` is chosen to be `Type` (or `Prop`, or `Sort u`
-- most generally). So `(λ _ a, a) : ∀ {α : Type}, α → α` is the polymorphic
-- identity function. Note that function terms are introduced with lambdas:
--    def f : Π (a : α), β a :=
--      λ (a : α), <some value of type `β a` using `a : α` in scope>
--
-- But more typically, top-level definitions will have this alternate syntax:
--    def f (a : α) : β a := <some value of type `β a` using `a : α` in scope>
-- There are subtle differences, but they are basically the same, just note
-- that in this latter form, (a : α) is already in scope without the lambda binder!
--
-- I mention this below, but for completeness, there is existential quantification:
-- (∃ (a : α), p a) : Prop, and dependent products: (Σ' (a : α), p a) : Type.
-- Dependent products give access to the value and the proof, whereas existentials
-- only assert that there is such a value, without giving it explicitly.
-- This is the difference between (non-computable) classical logic and (computable)
-- intuitionistic logic. See https://homotopytypetheory.org/book/ for more.
--
-- Definitional versus propositional equality: there are two varieties of equality:
-- `:=` is the syntax used to declare equalities, most of the time, and
-- `=` is the proposition that two things are equal. The Lean compiler will solve
-- definitional equalities, and this can be turned into a propositional equality
-- using `refl a : a = a` (standing for the reflexivity of equality).
-- For example, `refl 1 : 1 = 1` is the proof that 1 equals itself. Duh!
-- `eq.trans (e1 : a = b) (e2 : b = c) : a = c` is an example where, even though
-- `a`, `b`, and `c` are not known in advance (and thus are not definitionally
-- equal), their propositional equalities can still be combined.

-- Import libraries that this file depends on
import data.fintype.basic data.equiv.basic

-- Just a universe variable (used to avoid Girard's/Russel's paradox).
-- Not so important; see the following for more:
-- https://leanprover.github.io/reference/other_commands.html
-- https://en.wikipedia.org/wiki/Intuitionistic_type_theory#Universe_Types
universe u

-- A few helpful lemmata, explanations skipped
theorem psigma_elim_exists {α : Type} {β : α → Prop} {r : Prop} :
    Exists β → (psigma β → r) → r :=
        λ e f, exists.elim e (λ a b, f (psigma.mk a b))

theorem subtype_elim_exists {α : Type} {β : α → Prop} {r : Prop} :
    Exists β → (subtype β → r) → r :=
        λ e f, exists.elim e (λ a b, f (subtype.mk a b))

lemma list.nodup_tail_of_nodup {α : Type} {l : list α} :
    list.nodup l → list.nodup (list.tail l) :=
    begin
    intro nd,
    cases l,
    exact list.nodup_nil,
    rw list.tail_cons,
    apply list.nodup_of_nodup_cons,
    exact nd,
    end

-- end lemmata

-- First we will need to define the types that characterize a (multi)digraph.

-- An arc connects a starting and ending vertex; this defines the Type for that.
-- in particular, this states that, given a Type (call it V), arcT V is a Type
-- defined as `V × V`, which is an ordered pair consisting of two elements of type V.
def arcT (V : Type) : Type := V × V
def arcT.mk {V : Type} (v1 v2 : V) : arcT V :=
    prod.mk v1 v2

-- Each digraph has a particular type of vertices, type of arcs, and consists of
-- the mapping φ from specific arcs to their starting and ending vertices.
structure digraph
    (V E : Type) : Type :=
    mk :: (φ : E → arcT V)

-- `arc G v1 v2` is an arc that goes from v1 to v2 in graph G.
-- V and E are implicit arguments (since they use {}): they can be filled in
-- once we know what the type of G is, since (G : digraph V E) mentions V and E.
def arc
    {V E : Type} (G : digraph V E)
    (v1 v2 : V) :=
        -- this is an edge paired with a proof that the edge connects
        -- the vertices mentioned in the type of the arc
        Σ'(e : E), G.φ e = arcT.mk v1 v2

-- The proposition that an arc exists, without specifying the arc itself.
def has_arc
    {V E : Type} (G : digraph V E)
    (v1 v2 : V) : Prop :=
        ∃ (e : E), G.φ e = arcT.mk v1 v2

-- Eliminate the existential has_arc with a non-dependent proof function taking an arc.
def has_arc.elim
    {V E : Type} {G : digraph V E}
    {v1 v2 : V} {r : Prop} :
    has_arc G v1 v2 → (arc G v1 v2 → r) → r :=
        psigma_elim_exists

namespace digraph

-- Get the source of an edge E in a graph G
def source
    {V E : Type} (G : digraph V E)
    (e : E) : V := (G.φ e).1

-- Target of an arc
def target
    {V E : Type} (G : digraph V E)
    (e : E) : V := (G.φ e).2

-- An initial vertex has no edges leading to it in G
def is_initial
    {V E : Type} (G : digraph V E)
    (v : V) : Prop :=
        ¬∃ (e : E), target G e = v

-- A final vertex has no edges leading from it in G
def is_final
    {V E : Type} (G : digraph V E)
    (v : V) : Prop :=
        ¬∃ (e : E), source G e = v

-- Subtype generated by is_initial
-- (that is, a vertex with a proof that it is initial)
def initial
    {V E : Type} (G : digraph V E) :=
        { v : V // is_initial G v }

-- Subtype generated by is_final
def final
    {V E : Type} (G : digraph V E) :=
        { v : V // is_final G v }

-- A walk, as an inductive type, consists of arcs where each next arc leads
-- from the previous arc. This is encoded by matching the vertices at the type
-- level: only an arc from v1 to v2 and a walk from v2 to v3 can produce a walk
-- from v1 to v3.
-- Again, V and E can be figured out from an explicit G.
inductive walk
    {V E : Type} (G : digraph V E) :
    V → V → Type
    | empty {v : V} : walk v v
    | step {v1 v2 v3 : V} : arc G v1 v2 → walk v2 v3 → walk v1 v3

-- This begins a namespace; everything declared in this namespace will be accessed
-- with the prefix `walk.` outside of the namespace, like `walk.length`
namespace walk

-- The edges underlying a walk.
-- This is a function defined by taking some arguments (most notably a walk)
-- and returning a list of elements of type E.
-- Note that G is implicit: it's inferrable from the type of the walk given to edges
def edges
    {V E : Type} {G : digraph V E}
    {v1 v2 : V} :
    walk G v1 v2 → list E :=
    -- this is tactic mode
    begin
    -- `intro` introduces the argument `w : walk G v1 v2`
    intro w,
    -- `induction` takes apart the two cases of `w` (`empty` and `step`)
    -- and adds an induction hypothesis for the nested walk in the `step` case
    induction w,
    -- for the first case, we want to produce an empty list
    -- `exact` just means that we are finishing the goal with a suitable term
    exact list.nil,
    -- for the second case, we `cons`truct a new list by adding the edge
    -- of the arc on the front to the front on the rest of the edges
    -- (note that w_ᾰ and w_ih are names automatically generated by `induction w`)
    exact list.cons w_ᾰ.1 w_ih,
    end

-- The vertices visited in a walk, including the start and end vertices
-- (which are already mentioned in the type).
def vertices
    {V E : Type} {G : digraph V E}
    {v1 v2 : V} :
    walk G v1 v2 → list V :=
    begin
    -- similar story, but we start with v2 in the empty case
    intro w, induction w,
    exact list.cons v2 list.nil,
    -- and add v1 at each step
    exact list.cons w_v1 w_ih,
    end

-- The length of a walk, i.e. the number of arcs used in it, as a natural number.
def length
    {V E : Type} {G : digraph V E}
    {v1 v2 : V} :
    walk G v1 v2 → ℕ :=
    begin
    intro w,
    induction w,
    exact 0,
    -- Note: nat.succ n = n+1, get used to it ;)
    exact nat.succ w_ih,
    end

-- This is our first lemma; it's like a definition but usually it contains a proof,
-- (in this case: a proof that the length of an empty walk is 0). Conceptually,
-- in type theory, there is no real difference: this is just another
-- dependently-typed function, taking variables V E G and v and returning a result.
@[simp] -- this attribute lets it get picked up by the `simp` tactic
lemma length_empty
    {V E : Type} {G : digraph V E}
    {v : V} :
    -- (empty G : walk G v v) is just a type annotation specifying v
    -- This could be written (empty _ : walk G v v), since G is
    -- inferrable by unification
    length (empty: walk G v v) = 0 :=
      by refl -- definitional equality holds here

@[simp]
lemma length_step
    {V E : Type} {G : digraph V E}
    {v1 v2 v3 : V}
    (a : arc G v1 v2)
    (w : walk G v2 v3) :
    length (step a w) = length w + 1 :=
      by refl

-- A walk from v1 to v2 can be concatenated with a walk from v2 to v3 by first
-- taking the arcs from the first walk, then taking the arcs from the second.
-- This is a binary function with two arguments, nothing else is new.
def concat
    {V E : Type} {G : digraph V E}
    {v1 v2 v3 : V} :
    walk G v1 v2 → walk G v2 v3 → walk G v1 v3 :=
    begin
    intros w1 w2,
    induction w1,
    exact w2,
    exact step w1_ᾰ (w1_ih w2),
    end

-- A proof of a fact that's obvious enough for the equation compiler to solve
@[simp]
lemma concat_empty_left
    {V E : Type} {G : digraph V E}
    {v1 v2 : V}
    (w : walk G v1 v2) :
    concat (empty) w = w :=
      by refl

-- Again, pretty obvious
lemma concat_step_left
    {V E : Type} {G : digraph V E}
    {v1 v2 v3 v4 : V}
    (a : arc G v1 v2)
    (w1 : walk G v2 v3)
    (w2 : walk G v3 v4) :
    concat (step a w1) w2 = step a (concat w1 w2) :=
      by refl

-- But this one needs to be solved by induction, since there's no special case
-- for an empty walk on the right (one must walk through all of the first walk).
@[simp]
lemma concat_empty_right
    {V E : Type} {G : digraph V E}
    {v1 v2 : V}
    (w : walk G v1 v2) :
    concat w (empty) = w :=
    begin
    -- luckily it is simple using induction
    induction w,
    refl,
    -- `rw` (or `rewrite`) is a tactic that changes the type of the goal
    -- given particular equalities; in this case, it finishes the goal too.
    rw [concat_step_left, w_ih],
    end

-- Concatenating walks adds their length.
lemma concat_length
    {V E : Type} {G : digraph V E}
    {v1 v2 v3 : V}
    (w1 : walk G v1 v2)
    (w2 : walk G v2 v3) :
    length (concat w1 w2) = length w1 + length w2 :=
    begin
    induction w1,
    -- this is easy enough for the tactic to solve by simplification,
    -- by using these facts (available with the [simp] attribute):
    -- 1. concat (empty G) w2 = w2
    -- 2. length (empty G) = 0
    simp,
    -- provide two additional theorems to help `simp` close the goal:
    simp [concat_step_left, w1_ih],
    rw add_assoc,
    rw add_assoc,
    rw add_comm 1 w2.length,
    end

-- Useful lemmata regarding walk.vertices
-- (still inside the walk namespace!)
namespace vertices

-- Takes an assumption that the walk is empty, making it easier to use
-- when the proof is not obviously `refl`. When it is obvious, use:
--     rw [walk.vertices.empty _ rfl],
@[simp]
def empty
    {V E : Type} {G : digraph V E}
    {v : V}
    (w : walk G v v) :
    (w = walk.empty) → walk.vertices w = [v] :=
        λ h, eq.substr h rfl

-- Takes an assumption that the walk is nonempty, making it easier to use
-- when the proof is not obviously `refl`. When it is obvious, use:
--     rw [walk.vertices.step _ _ _ rfl],
@[simp]
def step
    {V E : Type} {G : digraph V E}
    {v1 v2 v3 : V}
    (a : arc G v1 v2)
    (w : walk G v2 v3)
    (w' : walk G v1 v3) :
    (w' = walk.step a w) → walk.vertices w' = v1 :: walk.vertices w :=
        λ h, eq.substr h rfl

-- The list of vertices of a walk starts with the starting vertex of the walk.
def starts_with
    {V E : Type} {G : digraph V E}
    {v1 v2 : V}
    (w : walk G v1 v2) :
    walk.vertices w = v1 :: list.tail (walk.vertices w) :=
    begin
    cases w, refl, refl,
    end

-- The list of vertices follow concatenation ... except for the first vertex of
-- the second walk, which would be duplicated by just joining the verticces,
-- since it is the last entry in `walk.vertices w1` already.
def concat
    {V E : Type} {G : digraph V E}
    {v1 v2 v3 : V}
    (w1 : walk G v1 v2)
    (w2 : walk G v2 v3)
    (w3 : walk G v1 v3) :
    (w3 = walk.concat w1 w2) →
        walk.vertices w3 = walk.vertices w1 ++ list.tail (walk.vertices w2) :=
    begin
    intro h, rw h,
    induction w1,
    { simp, exact starts_with w2 },
    rw [concat_step_left w1_ᾰ w1_ᾰ_1 w2],
    -- simplify right side
    rw [step w1_ᾰ w1_ᾰ_1 _ rfl],
    -- simplify left side
    rw [step w1_ᾰ (concat w1_ᾰ_1 w2) _ rfl],
    -- pass through the cons, and apply induction hypothesis
    congr, apply w1_ih _ _ rfl,
    end

end vertices
end walk
-- close out the namespaces; back to the default namespace of this file

-- Back to types, a similar story regarding paths as walks:
-- A path is a walk with a proof that vertices are not repeated.
def path
    {V E : Type} (G : digraph V E) :
    V → V → Type :=
    λ v1 v2, { w : walk G v1 v2 // list.nodup (walk.vertices w) }

-- The proposition that a path between two vertices merely exists.
def has_path
    {V E : Type} (G : digraph V E) :
    V → V → Prop :=
    λ v1 v2, ∃ (w : walk G v1 v2), list.nodup (walk.vertices w)

-- Eliminate the existential has_path via a real path
def has_path.elim
    {V E : Type} {G : digraph V E}
    {v1 v2 : V} {r : Prop} :
    has_path G v1 v2 → (path G v1 v2 → r) → r :=
        subtype_elim_exists

namespace path

-- An empty path is simple to generate; its list of 1 vertex obviously has no
-- duplicates.
def empty
    {V E : Type} (G : digraph V E)
    {v : V} : path G v v :=
    begin
    -- `apply` is sort of like `exact`, but it expects a function that requires more
    -- arguments to reach the proof goal.
    -- In particular, this starts to create a subtype with the value `empty`
    apply subtype.mk (walk.empty),
    -- but it requires a proof that there are no duplicates in its vertex list:
    simp [walk.vertices.empty, list.nodup_singleton],
    end

-- An arc between distinct vertices gives a path
def from_arc
    {V E : Type} (G : digraph V E)
    {v1 v2 : V} : (v1 ≠ v2) → arc G v1 v2 → path G v1 v2 :=
    begin
    intro h, intro a,
    -- `let` binds a local constant in a way that it can be referred to
    -- in other proof terms
    let w := walk.step a (walk.empty),
    apply subtype.mk w,
    -- `have` just provides a usuable constant whose definition can't be referred to
    have : walk.vertices w = [v1, v2], refl,
    rw this,
    -- `simp` helps make progress on the goal
    simp [list.nodup_singleton],
    -- the only thing missing is a proof that the vertices are distinct,
    -- which is true by assumption
    exact h -- or we could even use the `assumption` tactic
    end

@[reducible] -- [reducible] makes this definition more transparent
def length
    {V E : Type} {G : digraph V E}
    {v1 v2 : V} :
    path G v1 v2 → ℕ :=
        λ p, walk.length p.1

-- This is a big topic: creating a path from a walk
-- Note that my proofs in this section are ugly, so feel free to skip them
-- (the high-level idea is easy enough to grasp; just know that it's
-- machine-verified ;D)
namespace from_walk

-- A helpful invariant: a walk with just a vertex removed preserves the property
-- of having no duplicates.
def preserves_nodup
    {V E : Type} {G : digraph V E}
    {v v1 v2 : V}
    (w : walk G v1 v2)
    (w' : walk G v v2) :=
        list.nodup (list.tail (walk.vertices w)) →
        list.nodup (list.tail (walk.vertices w'))

-- But it turns out that the desired walk being a subwalk is sufficient
def split_at
    {V E : Type} {G : digraph V E}
    {v1 v2 : V} (w : walk G v1 v2) (v : V) :=
    Σ' (w1 : walk G v1 v) (w2 : walk G v v2),
        w = walk.concat w1 w2

-- This includes the other invariant we want to guarantee (that v does not
-- appear except as the first vertex of w2).
def split_at_without
    {V E : Type} {G : digraph V E}
    {v1 v2 : V} (w : walk G v1 v2) (v : V) :=
    Σ' (w1 : walk G v1 v) (w2 : walk G v v2),
        (v ∉ list.tail (walk.vertices w2)) ∧
        w = walk.concat w1 w2

-- Weaken the latter to the former ...
-- Note: `a_of_b` is convention to indicate a function/lemma with a type like `b → a`
def split_at_of_split_at_without
    {V E : Type} {G : digraph V E}
    {v1 v2 : V} {w : walk G v1 v2} {v : V} :
    split_at_without w v → split_at w v :=
    begin
    intro s, constructor, constructor, exact s.2.2.2
    end

-- And recover the invariant from it
lemma split_at.preserves_nodup
    {V E : Type} {G : digraph V E}
    {v1 v2 : V} {w : walk G v1 v2} {v : V}
    (s : split_at w v) : preserves_nodup w s.2.1 :=
    begin
    cases s with w1 s, cases s with w2 p,
    intro nd, simp,
    rw [walk.vertices.concat _ _ _ p] at nd,
    rw [walk.vertices.starts_with _] at nd,
    simp at nd,
    rw list.nodup_append at nd,
    exact nd.2.1,
    end

def discard_vertex.split_at
    {V E : Type} [decidable_eq V] {G : digraph V E}
    (v : V) {v1 v2 : V} (w : walk G v1 v2) :
    psum (split_at_without w v) (v ∉ list.tail (walk.vertices w)) :=
    begin
    induction w with v0 v1 v2 v3 a w ih,
    right,
    simp [walk.vertices.empty _ rfl],
    simp [walk.vertices.step _ _ _ rfl],
    cases ih, left,
    apply psigma.mk (walk.step a ih.1),
    apply psigma.mk ih.2.1,
    apply and.intro ih.2.2.1,
    rw [walk.concat_step_left _ _ _],
    congr,
    exact ih.2.2.2,
    by_cases h : v = v2,
    left, rw h, rw h at ih,
    have : walk.concat (walk.step a (walk.empty)) w = walk.step a w,
    {
        simp [walk.concat_step_left _ _ _],
    },
    exact psigma.mk (walk.step a (walk.empty)) (psigma.mk w (and.intro ih this)),
    right,
    have : walk.vertices w = v2 :: list.tail (walk.vertices w),
        cases w, refl, refl,
    rw this, intro vin, cases vin,
    exact h vin, exact ih vin,
    end

-- Remove any occurrence of a vertex from a walk, by either returning a new walk
-- formed as a subset of the previous walk but starting from the vertex to be
-- removed (along with proofs that the vertex was removed, and that the new walk
-- contains no dupicates if the original did), OR a proof that the vertex
-- does not occur in the original walk.
--
-- This is obviously ugly, but encodes enough information to make from_walk work.
def discard_vertex
    {V E : Type} [decidable_eq V] {G : digraph V E}
    (v : V) {v1 v2 : V} (w : walk G v1 v2) :
    psum
        -- either a new walk
        (Σ' (w' : walk G v v2), -- from v to v2
            -- where v does not occur
            (v ∉ list.tail (walk.vertices w')) ∧
            -- and preserving the no duplicates property
            preserves_nodup w w')
        -- or a proof that the vertex does not occur in the original walk
        (v ∉ list.tail (walk.vertices w)) :=
    begin
    induction w with v0 v1 v2 v3 a w ih,
    right,
    simp [walk.vertices.empty _ rfl],
    simp [walk.vertices.step _ _ _ rfl],
    cases ih, left, apply psigma.mk ih.1, apply and.intro ih.2.1,
    intro ndaw, simp [walk.vertices.step _ _ _ rfl] at ndaw, apply ih.2.2,
    apply list.nodup_tail_of_nodup, exact ndaw,
    by_cases h : v = v2,
    left, rw h, rw h at ih,
    have : preserves_nodup (walk.step a w) w,
    {
        intro ndaw,
        simp [walk.vertices.step _ _ _ rfl] at ndaw,
        apply list.nodup_tail_of_nodup, exact ndaw,
    },
    exact psigma.mk w (and.intro ih this),
    right,
    have : walk.vertices w = v2 :: list.tail (walk.vertices w),
        cases w, refl, refl,
    rw this, intro vin, cases vin,
    exact h vin, exact ih vin,
    end

-- This can obviously be used to discard repeats of the first vertex of a walk.
-- But this is actually unused ...
def discard_vertex.beginning
    {V E : Type} [decidable_eq V] {G : digraph V E}
    {v1 v2 : V} (w : walk G v1 v2) :
    Σ' (w' : walk G v1 v2),
        (v1 ∉ list.tail (walk.vertices w')) ∧
        preserves_nodup w w' :=
    begin
    have := discard_vertex v1 w,
    cases this, exact this,
    exact psigma.mk w (and.intro this id),
    end

-- Using induction on the walk, discard all the vertex repeats to generate a
-- path. This has the effect of removing all cycles in the walk.
def discard_vertex.all.explicit
    {V E : Type} [decidable_eq V] {G : digraph V E}
    {v1 v2 : V} (w : walk G v1 v2) : path G v1 v2 :=
    begin
    -- Induction on a walk considers the base case (empty) and the step case
    induction w with v v1 v2 v3 a w ih,
    -- If the walk is empty, we already know how to generate an empty path; done.
    exact path.empty _,
    -- But if v1 = v2, we discard the arc, and just return the induction
    -- hypothesis (that is, the path generated from the tail), once we have
    -- rewritten v1 as v2.
    by_cases v1_v2 : (v1 = v2), rw v1_v2, exact ih,
    -- Just splits up the induction hypothesis into the walk and the proof.
    cases ih with ih_w ih_nodup,
    -- Now we discard the starting vertex from the induction hypothesis' walk
    have ih_w' := discard_vertex v1 ih_w,
    -- Consider the cases: a new walk, or the same walk
    cases ih_w', cases ih_w' with w' p,
    -- If we obtained a new walk, it is the walk we want to return
    apply subtype.mk w',
    -- Construct a proof that the walk has no duplicates
    rw [walk.vertices.starts_with, list.nodup_cons], constructor,
    -- from the fact that v does not occur in the rest of the vertices
    exact p.1,
    -- and the fact that the ih had no duplicates, so the tail of this has none
    exact (p.2 (list.nodup_tail_of_nodup ih_nodup)),
    -- Otherwise, we should return the walk consisting of this arc and the ih walk
    apply subtype.mk (walk.step a ih_w),
    -- Do some rewrites of the goal ...
    rw [walk.vertices.step _ _ _ rfl, list.nodup_cons], constructor,
    rw [walk.vertices.starts_with, list.mem_cons_iff],
    -- We know that v1 is not the second vertex v2, nor is it in ih_w
    apply not_or v1_v2 ih_w',
    -- And the rest of the ih already had no duplicates, by induction
    exact ih_nodup,
    end

-- This contains the above algorithm but also produces the proof that either
-- the result is the same, or the walk/graph contained a cycle.
--
-- This can be used to prove the equivalence of walks and paths in acyclic
-- digraphs.
def discard_vertex.all.acyc_prf
    {V E : Type} [decidable_eq V] {G : digraph V E}
    {v1 v2 : V} (w : walk G v1 v2) :
        Σ' (p : path G v1 v2),
            p.1 = w ∨ ∃(v : V) (c : walk G v v), c ≠ walk.empty :=
    begin
    induction w with v v1 v2 v3 a w ih,
    exact psigma.mk (path.empty _) (or.inl rfl),
    by_cases v1_v2 : (v1 = v2),
    apply psigma.mk, right, tactic.swap,
    rw v1_v2, exact ih.1,
    apply exists.intro v2,
    rw v1_v2 at a,
    apply exists.intro (walk.step a (walk.empty)),
    exact λ h, walk.no_confusion h,
    cases ih with ih prf, cases ih with ih_w ih_nodup,
    have ih_w' := discard_vertex.split_at v1 ih_w,
    cases ih_w',
    have := split_at.preserves_nodup (split_at_of_split_at_without ih_w'),
    cases ih_w' with w1 ih_w', cases ih_w' with w2 p,
    apply psigma.mk (subtype.mk w2
        begin
        rw [walk.vertices.starts_with, list.nodup_cons], constructor,
        exact p.1,
        exact (this (list.nodup_tail_of_nodup ih_nodup)),
        end : path G v1 v3),
    right, apply exists.intro v1,
    apply exists.intro (walk.step a w1),
    exact λ h, walk.no_confusion h,
    apply psigma.mk (subtype.mk (walk.step a ih_w)
        begin
        rw [walk.vertices.step _ _ _ rfl],
        rw [list.nodup_cons], constructor,
        rw [walk.vertices.starts_with],
        rw list.mem_cons_iff,
        apply not_or v1_v2 ih_w',
        exact ih_nodup,
        end : path G v1 v3),
    cases prf,
    left,
    simp at prf,
    simp [prf],
    right,
    exact prf,
    end

-- This defeq will be important
@[reducible]
def discard_vertex.all
    {V E : Type} [decidable_eq V] {G : digraph V E}
    {v1 v2 : V} (w : walk G v1 v2) : path G v1 v2 :=
    (discard_vertex.all.acyc_prf w).1

end from_walk

-- This just references the version inside the from_walk namespace
@[reducible]
def from_walk
    {V E : Type} [decidable_eq V] {G : digraph V E}
    {v1 v2 : V} :
    walk G v1 v2 → path G v1 v2 := from_walk.discard_vertex.all

-- This concatenates the underlying paths then removes cycles to generate
-- the new path.
def concat
    {V E : Type} [decidable_eq V] {G : digraph V E}
    {v1 v2 v3 : V}
    (p1 : path G v1 v2)
    (p2 : path G v2 v3) :
    path G v1 v3 := from_walk (walk.concat p1.1 p2.1)

-- A maximal path is a path going to a final vertex.
def maximal
    {V E : Type} (G : digraph V E)
    (v1 v2 : V) := pprod (path G v1 v2) (is_final G v2)
                    -- (pprod stores a piece of data and a separate proof)

-- Proposition that one exists.
def has_maximal
    {V E : Type} (G : digraph V E)
    (v1 v2 : V) := (has_path G v1 v2) ∧ (is_final G v2) -- regular conjunction

-- Eliminate it following the usual pattern
def has_maximal.elim
    {V E : Type} {G : digraph V E}
    {v1 v2 : V} {r : Prop} :
    has_maximal G v1 v2 → (maximal G v1 v2 → r) → r :=
        λ h f, has_path.elim h.1 (λ p, f (pprod.mk p h.2))

-- Hopefully this makes sense now by just looking at the types!
def maximal.concat
    {V E : Type} [decidable_eq V] {G : digraph V E}
    {v1 v2 v3 : V}
    (p1 : path G v1 v2)
    (p2 : path.maximal G v2 v3) :
    path.maximal G v1 v3 :=
    begin
    constructor,
    exact path.concat p1 p2.1,
    exact p2.2,
    end

def has_maximal.concat
    {V E : Type} [decidable_eq V] {G : digraph V E}
    {v1 v2 v3 : V}
    (p1 : path G v1 v2)
    (p2 : path.has_maximal G v2 v3) :
    path.has_maximal G v1 v3 :=
    flip and.intro p2.2
    begin
    apply exists.elim p2.1, intro w, intro nodup,
    exact subtype.exists_of_subtype (path.concat p1 (subtype.mk w nodup)),
    end

-- If the walk underlying a path is nonempty, produce the path corresponding
-- to its tail.
def vertices.step_back
    {V E : Type} [decidable_eq V] {G : digraph V E}
    {v1 v2 v3 : V}
    (a : arc G v1 v2)
    (w : walk G v2 v3)
    (p : path G v1 v3) :
    (p.1 = walk.step a w) → path G v2 v3 :=
    begin
    intro h, cases p, simp at h,
    apply subtype.mk w,
    rw [walk.vertices.step _ _ _ h] at p_property,
    exact list.nodup_of_nodup_cons p_property,
    end

end path

-- One encoding (fairly direct and easy to use) of the property of an acyclic
-- graph: all walks from a vertex to itself are empty.
def is_acyclic
    {V E : Type} (G : digraph V E) :=
        ∀ (v : V) (w : walk G v v), w = walk.empty

-- Subtype generated from that (unused).
def acyclic
    {V E : Type} :=
        { G : digraph V E // is_acyclic G }

-- It turns out that in acyclic graphs, from_walk just elaborates the same walk
-- with a proof term.
lemma is_acyclic.from_walk
    {V E : Type} [decidable_eq V] {G : digraph V E}
    {v1 v2 : V}
    (acyc : is_acyclic G)
    (w : walk G v1 v2) :
    (path.from_walk w).val = w :=
    begin
    let fw := path.from_walk.discard_vertex.all.acyc_prf w,
    have : path.from_walk w = fw.1, refl, rw this,
    cases h : fw with p prf,
    simp,
    cases prf,
    exact prf,
    exfalso,
    apply exists.elim prf, intro v, intro prf',
    apply exists.elim prf', intro c, intro prf'',
    exact prf'' (acyc v c)
    end

-- Thus paths and walks are equivalent in acyclic digraphs.
def path.equiv_walk
    {V E : Type} [decidable_eq V] {G : digraph V E}
    {v1 v2 : V} :
    is_acyclic G →
    walk G v1 v2 ≃ path G v1 v2 := λ acyc,
    -- this is an equivalence a ≃ b: a pair of functions a → b and b → a,
    -- with proofs that they are inverses of each other
    equiv.mk path.from_walk subtype.val
        (is_acyclic.from_walk acyc)
        (λ p, subtype.eq (is_acyclic.from_walk acyc p.val))

-- Since the cycle elimination algorithm does nothing in an acyclic graph,
-- lengths are preserved through concatenation
lemma path.acyclic_concat_length
    {V E : Type} [decidable_eq V] {G : digraph V E}
    {v1 v2 v3 : V}
    (p1 : path G v1 v2)
    (p2 : path G v2 v3) :
    is_acyclic G →
    path.length (path.concat p1 p2) = path.length p1 + path.length p2 :=
    begin
    intro acyc,
    show walk.length (path.concat p1 p2).1 = walk.length p1.1 + walk.length p2.1,
    show walk.length (path.from_walk (walk.concat p1.1 p2.1)).1
       = walk.length p1.1 + walk.length p2.1,
    rw [is_acyclic.from_walk acyc _],
    exact walk.concat_length _ _,
    end

-- Okay, done with types! On to the main course:


-- The so-called “no-watershed condition”: for any two vertices with arcs
-- from(!) a common vertex, there is another vertex that has paths from
-- both of those. (Obviously true if {u,v,w} are not distinct.)
-- See section 0.2 in http://www-users.math.umn.edu/~dgrinber/comb2/mt3.pdf
def no_watershed_condition
    {V E : Type} (G : digraph V E) : Prop :=
    Π (u v w : V),
        arc G u v → arc G u w →
        ∃ (t : V), has_path G v t ∧ has_path G w t

-- Having the no-watershed condition in an acyclic graph produces the result
-- that each vertex has a unique sink; that is, a vertex with a maximal path
-- from the other vertex.
namespace unique_sink

-- Inside a namespace/section, we can use the following commands to declare variables
-- used in the definitions/lemmata for this section:
-- implicit and explicit arguments
variables {V E : Type} (G : digraph V E)
variables acyc : is_acyclic G
-- and typeclass arguments! these are variables of a special type that have a
-- canonical value
-- In particular:
-- decidable_eq V gives a function Π(v1 v2 : V), (v1 = v2) ∨ (v1 ≠ v2)
-- that decides whether two vertices are equal, giving a proof either way
-- fintype V asserts that V has finitely many inhabitants, by giving a list
-- of them all (actually a finite set `finset`), and a proof that every
-- element occurs in it: ∀ v : V, v ∈ univ V
variables [decidable_eq V] [decidable_eq E] [fintype V] [fintype E]

-- Now that we have G as a fixed local variable, we can use it in notation!
-- who doesn't love syntactic sugar?!?!? :D
local infix `⟶`:50 := arc G
local infix `~⟶`:50 := walk G -- unused
local infix `*⟶`:50 := path G
local infix `×⟶`:50 := path.maximal G
-- and their propositional equivalents
local infix `⟼`:50 := has_arc G
local infix `*⟼`:50 := has_path G
local infix `×⟼`:50 := path.has_maximal G

-- In finite acyclic graphs, each vertex will have a longest path;
-- if `bounded_by p n` is provided, then the longest path from p is at most n steps.
def bounded_by (p : V) (n : ℕ) := ∀ (q : V) (w : p *⟶ q), path.length w ≤ n

-- This is the proposition used for induction. It limits the results to
-- only pertain to vertices p whose paths away from them have length at most n.
def P (n : ℕ) :=
    ∀ (p : V),
        bounded_by G p n →
        ∃! (q : V), p ×⟼ q

-- Helper: These are logically equivalent via two existing lemmate...
lemma eq_zero_iff_le_zero {n : nat} : n ≤ 0 ↔ n = 0 :=
    iff.intro nat.eq_zero_of_le_zero nat.le_of_eq

-- A walk of length 0 obviously connects the same two vertices.
lemma length0 {v1 v2 : V} (w : v1 ~⟶ v2) :
    walk.length w = 0 → v1 = v2 :=
    begin
    intro h,
    -- obviously the `empty` case is trivial:
    cases w, refl,
    -- but the `step` case is absurd!
    rw [walk.length_step] at h,
    exact absurd h (nat.succ_ne_zero (walk.length w_ᾰ_1)),
    end

-- Two maximal paths from the same vertex cannot have one be empty and the other
-- be nonempty.
lemma not_diff_emptiness
    {p q1 q2 : V}
    (w1 : p ×⟶ q1)
    (w2 : p ×⟶ q2) :
    ¬(path.length w1.1 = 0 ∧ path.length w2.1 > 0) :=
    begin
    intro h,
    have pq1 := length0 G w1.1.1 h.1,
    have q1_final := w1.2,
    rw [← pq1] at q1_final,
    apply q1_final,
    let w := w2.1.1,
    cases hw : w,
    apply flip absurd (ne_of_gt h.2),
    show walk.length w = 0,
    rw hw, exact walk.length_empty,
    apply exists.intro ᾰ.1,
    have x : (arcT.mk p v2).1 = p, refl,
    rw [← ᾰ.2] at x,
    exact x,
    end

-- ... basically the same as above, but more explicit.
lemma same_emptiness
    {p q1 q2 : V}
    (w1 : p ×⟶ q1)
    (w2 : p ×⟶ q2) :
    (path.length w1.1 = 0 ∧ path.length w2.1 = 0) ∨
    (path.length w1.1 > 0 ∧ path.length w2.1 > 0) :=
    begin
    cases h1 : path.length w1.1,
    left, constructor, refl,
    cases h2 : path.length w2.1, refl,
    apply flip absurd (not_diff_emptiness G w1 w2),
    constructor, exact h1,
    have := nat.zero_lt_succ n,
    rw [← h2] at this,
    exact this,
    right, constructor, exact nat.zero_lt_succ n,
    cases h2 : path.length w2.1,
    apply flip absurd (not_diff_emptiness G w2 w1),
    constructor, exact h2,
    have := nat.zero_lt_succ n,
    rw [← h1] at this,
    exact this,
    exact nat.zero_lt_succ n_1,
    end

-- A proof that each path has finite length, bounded above by the number of vertices
lemma finite {p q : V} (w : p *⟶ q) : path.length w + 1 ≤ fintype.card V :=
    begin
    cases w with w nodup,
    -- this should really be a separate lemma, but it's easy enough to prove inline...
    have : walk.length w + 1 = list.length (walk.vertices w),
    {
        induction w,
        refl, simp [walk.vertices.step _ _ _ rfl],
        apply w_ih,
        rw [walk.vertices.step _ _ _ rfl] at nodup,
        exact list.nodup_of_nodup_cons nodup,
    },
    rw this,
    -- now we don't need the fact that it is a list of vertices anymore
    -- so replace it with a generic `l : list V` in the hypothesis and goal:
    generalize_hyp h : walk.vertices w = l at nodup, rw h,
    -- make a finite set from the list
    let fs : finset V := finset.mk (quotient.mk l) nodup,
    -- with the same size
    have : list.length l = finset.card fs :=
    by symmetry; apply quot.lift_beta list.length multiset.card._proof_1,
    rw this,
    -- it must be smaller or the same size, since it is a subset
    exact finset.card_le_of_subset (finset.subset_univ _),
    end

-- A vertex is either final or it has an arc leading from it to some other vertex.
-- Relies on [fintype E]
def any_arc_from (p : V) :
    (∃ (v : V), p ⟼ v) ∨ is_final G p :=
    begin
    let elems : finset E := finset.univ,
    -- Prove that these are equivalent
    -- instead of proving each direction separately, we use bijections at each step
    have : (p ∈ multiset.map (source G) elems.val) ↔ (∃(e : E), source G e = p),
        symmetry,
        rw multiset.mem_map,
        apply exists_congr,
        intro e,
        symmetry,
        apply and_iff_right,
        exact finset.mem_univ e,
    -- this is a decidable proposition, so we can determine whether it is true or false
    by_cases h : p ∈ multiset.map (source G) elems.val,
    {
        rw this at h,
        left,
        apply exists.elim h, intro e, intro he,
        apply exists.intro (target G e),
        apply exists.intro e,
        apply prod.eq_iff_fst_eq_snd_eq.2, constructor,
        show (G.φ e).1 = p, exact he,
        show (G.φ e).2 = target G e, refl,
    },
    {
        rw this at h,
        right, exact h,
    },
    end

-- tactic mode doesn't know to include this variable
-- we will use it in the remaining proofs
include acyc

-- If all paths leading out of a vertex have length 0, it must be a sink
def is_final_of_bounded_by_zero (v : V) :
    bounded_by G v 0 → is_final G v :=
    begin
    intros len,
    have := any_arc_from G v,
    cases this,
    {
        exfalso,
        apply exists.elim this, intros v1 ha,
        apply has_arc.elim ha, intro a,
        let p : v *⟶ v1 := path.from_walk (walk.step a (walk.empty)),
        have len0 := len _ p,
        rw [eq_zero_iff_le_zero] at len0,
        suffices : path.length p = 1, cc,
        have : p.1 = walk.step a (walk.empty),
            from is_acyclic.from_walk acyc _,
        unfold path.length, rw this, refl
    },
    exact this,
    end

-- Helper for induction: giving a path from v1 to v2 with length no less
-- than m and the fact that all paths from v1 are at most length n+m, means
-- that a path from v2 to v3 must have length at most n.
lemma reduce_length
    {v1 v2 v3 : V}
    {n m : ℕ}
    (w : v1 *⟶ v2)
    (p : v2 *⟶ v3)
    (lw : path.length w ≥ m)
    (mh : bounded_by G v1 (n+m)) :
    path.length p ≤ n :=
    begin
    let wp : v1 *⟶ v3 := path.concat w p,
    have lwp : path.length wp = path.length w + path.length p,
        from path.acyclic_concat_length w p acyc,
    -- rewrite lw at lwp,
    apply @nat.le_of_add_le_add_left (path.length w) _ _,
    rw [← lwp, add_comm],
    transitivity,
    apply mh v3,
    exact nat.add_le_add_left lw _,
    end

-- All vertices have a sink.
-- This is a smaller proof following the style of the larger proof.
-- We prove it by induction for all vertices that are bounded by n,
-- then we pick a sufficiently large n to cover all vertices.
lemma find_sink.bounded (n : ℕ) (v1 : V) :
    bounded_by G v1 n →
    ∃ (s : V), v1 ×⟼ s :=
    begin
    intros len,
    induction n with n ih generalizing v1,
    {
        apply exists.intro v1,
        apply and.intro (subtype.exists_of_subtype (path.empty G)),
        apply is_final_of_bounded_by_zero, assumption, assumption,
    },
    have := any_arc_from G v1,
    cases this,
    {
        apply exists.elim this, intros v2 ha,
        apply has_arc.elim ha, intro a,
        let p : v1 *⟶ v2 := path.from_walk (walk.step a (walk.empty)),
        have := ih v2
            begin
            have : path.length p = 1,
                have : p.1 = walk.step a (walk.empty),
                    from is_acyclic.from_walk acyc _,
                unfold path.length, rw this, refl,
            intros v' p',
            apply reduce_length G acyc p,
            exact ge_of_eq this,
            exact len,
            end,
        apply exists.elim this, intros s hm,
        apply exists.intro s,
        exact path.has_maximal.concat p hm
    },
    {
        apply exists.intro v1,
        apply and.intro (subtype.exists_of_subtype (path.empty G)),
        assumption,
    },
    end

-- Using `finite`, we pick a sufficient n to bound all vertices
lemma find_sink
    (v1 : V) :
    ∃ (s : V), v1 ×⟼ s :=
        find_sink.bounded G acyc _ v1
            begin
            unfold bounded_by, intros,
            rw ← nat.pred_succ (path.length w),
            apply nat.pred_le_pred,
            apply unique_sink.finite G
            end

-- Final vertices are their own sink
lemma P_final (p : V) : is_final G p → ∃!(q : V), p ×⟼ q :=
    begin
    intro final, apply exists_unique.intro p,
    constructor, exact subtype.exists_of_subtype (path.empty G), exact final,
    intro sink, intro has_max, apply subtype_elim_exists has_max.1,
    intro p, cases p, cases p_val, refl, exfalso,
    apply final,
    apply exists.intro p_val_ᾰ.1,
    show (G.φ p_val_ᾰ.1).1 = p,
    rw p_val_ᾰ.2, refl
    end

-- The base case, basically applies only to sinks, which are their own
-- sink, obviously.
lemma P0 : P G 0 :=
    λ p len, P_final _ acyc p (is_final_of_bounded_by_zero _ acyc p len)

-- The whole proof together.
--
-- Big picture idea:
-- For any vertex p with bounded_by G p n, try to find an arc leading out of it, call
-- its target v (≠ p). The unique sink can be obtained by applying induction to v.
-- But to establish that it is also unique for p, we take any otherSink
-- with a maximal path from p, take the first new vertex visited by that path v2
-- and we can apply the watershed condition to an arc p v and an arc p v2 to get t with
-- a path v t and a path v2 t. But by using this, the sinks from v, t, and v2 must
-- all be the same since we can extend the maximal path from t to be from v or v2.
-- This is essentially the statement that connected vertices share the same sink...
-- (Obviously the computer requires more details to formalize this and accept
-- it as rigorous, but they are explained below.)
theorem Pn : no_watershed_condition G → ∀ (n : ℕ), P G n :=
    begin
    -- introduce the watershed condition as a variable in scope
    intro watershed,
    -- this is the variable for induction, named n' since n will be in scope
    intro n,
    -- regular induction on natural numbers (just a special case of induction in DTT)
    induction n with n ih,
    -- base case, already proved as P0 above
    exact P0 G acyc,
    -- this is the vertex of interest
    intro p,
    -- and the proof that maximal paths from p have length at most n+1
    intro len,
    -- try to obtain an arc from p
    have aa := any_arc_from G p,
    -- this splits it up into the two cases, replacing aa with the result of each case
    -- (what follows is mostly the proof of the first case, the second takes one line)
    cases aa,
    apply exists.elim aa,
    -- obtain the vertex it goes to, and the proof that there is an arc
    intro v, assume ha : p ⟼ v,
    -- obtain some actual arc from p to v
    apply has_arc.elim ha, assume a : p ⟶ v,
    -- a funny proof by contradiction that p ≠ v since it is in an acyclic graph
    -- TODO: factor this out
    by_cases (p = v),
    {
        let a' : p ⟶ v := a,
        rw h at a',
        have := acyc _ (walk.step a' (walk.empty)),
        exfalso,
        exact walk.no_confusion this,
    },
    -- using that we can make a path from the arc ...
    let start : p *⟶ v := path.from_arc G h a,
    -- ... of length 1 (duh!)
    have len1 : path.length start = 1, refl,
    -- Now we can apply the induction hypothesis onto v, since `start`
    -- guarantees that the length will go down by 1.
    have exu := ih v
        begin
        intro v', intro p',
        apply reduce_length G acyc start p' (ge_of_eq len1) len,
        end,
    -- Now we unpack the existentials ...
    apply exists_unique.elim exu, simp,
    -- ... to obtain the sink, the existence of a maximal path from v to that
    -- sink, and the proof that that sink is unique
    intro sink, intro has_maxPathToSink, intro uniq,
    -- so we know that this is the sink we want, just need to prove it has a
    -- maximal path ...
    apply exists_unique.intro sink,
    apply subtype_elim_exists has_maxPathToSink.1,
    assume pathToSink : v *⟶ sink,
    constructor,
    apply subtype.exists_of_subtype,
    apply path.concat start pathToSink,
    exact has_maxPathToSink.2,
    -- ... and that it is unique. Oh boy.
    -- Given otherSink and a max path from p to otherSink, prove that they are
    -- the same sink.
    intro otherSink, intro has_maxPathToOtherSink,
    show otherSink = sink,
    apply path.has_maximal.elim has_maxPathToOtherSink,
    assume maxPathToOtherSink : p ×⟶ otherSink,
    -- Argue that the maximal path is nonempty.
    cases hp : maxPathToOtherSink.1.1,
    {
        exfalso, apply maxPathToOtherSink.2, apply exists.intro a.1,
        show (G.φ a.1).1 = p,
        exact (prod.eq_iff_fst_eq_snd_eq.1 (a.2)).1,
    },
    -- Now we have hp : (maxPathToOtherSink.fst).val = walk.step a_1 a_2
    -- so ᾰ is an arc from p to some v2
    -- Apply the watershed condition with a : arc G p v, ᾰ : arc G p v2
    have water1 := watershed p v v2 a ᾰ,
    -- so there is some t with paths from v to t and from v2 to t
    apply exists.elim water1, intro t, simp,
    intro has_vt, intro has_v2t,
    apply subtype_elim_exists has_vt, intro vt,
    apply subtype_elim_exists has_v2t, intro v2t,
    -- now we have another path like starting, but from p to t, via v.
    let startt : p *⟶ t := path.concat start vt,
    -- Induction again!
    have exu2 := ih t
        begin
        intro v', intro p',
        -- startt has length at least 1, since start has length 1, and
        -- vt may have length greater than 1, and since it is acyclic.
        have len_ge1 : path.length startt ≥ 1,
            have : path.length startt = path.length start + path.length vt,
                from path.acyclic_concat_length start vt acyc,
            rw len1 at this,
            transitivity,
            exact le_of_eq (eq.symm this),
            rw [add_comm],
            exact nat.succ_le_succ (nat.zero_le (path.length vt)),
        apply reduce_length G acyc startt p' len_ge1 len,
        end,
    apply exists_unique.elim exu2, simp,
    -- Oh here is anotherSink! the unique sink from t
    intro anotherSink, intro has_maxPathToAnotherSink, intro uniq2,
    -- but anotherSink = sink, since any maxpath can be extended along vt
    have := uniq _ (path.has_maximal.concat vt has_maxPathToAnotherSink),
    -- again argue that an arc connects distinct vertices
    by_cases (p = v2),
    {
        let a' : p ⟶ v2 := ᾰ,
        rw h at a',
        have := acyc _ (walk.step a' (walk.empty)),
        exfalso, exact walk.no_confusion this,
    },
    -- So there's a path from p to v2 just using the arc ᾰ.
    let startv2 : p *⟶ v2 := path.from_arc G h ᾰ,
    -- Induction yet again! last time I promise
    have exuv2 := ih v2
        begin
        intro v', intro p',
        apply reduce_length G acyc startv2 p',
        exact ge_of_eq (rfl : path.length startv2 = 1),
        exact len,
        end,
    apply exists_unique.elim exuv2, simp,
    -- finalSink is the unique sink from v2
    intro finalSink, intro has_maxPathToFinalSink, intro uniqv2,
    -- but finalSink = otherSink, due to the maxpath a_2 from v2 to otherSink
    have := uniqv2 otherSink
        begin
        -- construct the maxpath
        constructor,
        -- we can demonstrate the exact path, but we just need its existence,
        apply subtype.exists_of_subtype,
        -- hp : (maxPathToOtherSink.fst).val = walk.step a_1 a_2
        -- means that just the walk a_2 creates a path too
        exact path.vertices.step_back _ _ maxPathToOtherSink.1 hp,
        -- and is maximal since otherSink is still final
        exact maxPathToOtherSink.2,
        end,
    -- and finalSink = anotherSink, by extending maxpaths along v2t
    have := uniqv2 anotherSink
                (path.has_maximal.concat v2t has_maxPathToAnotherSink),
    -- so the congruence closure calculates that otherSink = sink via
    -- the equalities in scope
    cc,
    -- Oh yeah, and if aa had no arcs, then its a final vertex and we're done.
    exact P_final G acyc p aa,
    end

end unique_sink

-- It turns out that we can pick a sufficient n such that Pn holds for all p
theorem unique_sink
    {V E : Type} {G : digraph V E}
    [decidable_eq V] [decidable_eq E] [fintype V] [fintype E] :
    is_acyclic G → no_watershed_condition G →
    ∀ (p : V), ∃! (q : V), path.has_maximal G p q :=
        λ acyc watershed p, unique_sink.Pn G acyc watershed _ p
            begin
            unfold unique_sink.bounded_by, intros,
            rw ← nat.pred_succ (path.length w),
            apply nat.pred_le_pred,
            apply unique_sink.finite G
            end


end digraph
