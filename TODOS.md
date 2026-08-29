## Usability 
- [ ] Use camltac over ocaml plugin 
- [ ] Recover Build_mon - mon as a sublattice of monotone heterogenous functions?  
- [ ] make progress a true typeclass 
s.t. the type of di_similarity is
Progress X X -> Progress X X -> X. 
## Bugfixes
- [x] gfp in premise bug
- [ ] apply_ptower (auto inf closed) for tower induction.
- [ ] Reflexive_chain failing when elem has arguments.
- [x] accumulate unsupported subterm 
- [x] accumulate no such chain
- [ ] better stepping. 
- [ ] Damien: use preorder library. 


CHANGELOG 
- fixed gfp in premise bug, which was an ocaml recognition error solved
  by reverting and introducing gfp-based hypotheses. 
- fixed accumulate not working when premises were of a certain shape
  (`f (elem c)` for any `f`. )
- rewrote plugin infra in ltac, deprecating ocaml. includes infrastructure 
  for automatic dispatch of inf_closed goals. 
- used infra to rewrite coinduction and accumulate tactics
- NEXT: used infra to rewrite symmetric tactic 
- NEXT: inf_closed dispatch for automatic tower induction proofs. 
- NEXT: better step 
- NEXT: active-step support 

## Basics
- [x] Port lattice (trivial)
- [x] Port mon_h 
- [x] Port progress
- [x] Port rest
## Theory 

- [ ] Main quest prelim: build the tower from (s, f)
- [x] Relate similarity (of a single function) to di-similarity (of a pair of functions): di-similarity just says each function in the pair must progress to itself under a given progression. The two progressions can 
be different, but if they are the same and the two functions in the pair
are as well, this is just similarity. 

- [x] What if the two functions are the same but the progressions 
are different - we have (f p f, f a f)? well, if p and a are opaque, 
this is still the same as before. 
Thought: 
Where definitions come in is in evolutions: when we have 
s, f p-evolves to itself and 
s a-evolves to f 
and f p|a evolves to f, 

(s, f) is compatible. 

the companion is the greatest compatible object and is a pair of monotone functions. 

we also have that the image of the single-function companion t is the tower. 

So what is the image of the pair-companion w.r.t. the tower? 

where can we find the gfp within that tower? 

being below the companion is being in the tower. 

is that true? 

prove it in combine_companions. already proved: leq_t'/compat_chain

ok, so what about being below ucompan or wcompan? 

what does it mean for a pair to be compatible? 

ok, so compat functions are below t, and are thus their images are in the tower 

so if (s, f) is below (u, w), then...? 

well, we should prove that indeed w(⊥) = di_similarity (p, b)


thoughts:
similarity (gfp) in diacritical paper is parametric over an (X -> X -> Prop), 
and is defined over the sup of all progressions from R to R (self-progressions),
aka all bisimulations. 

gfp is : 
sup of all bisimulations 
sup of all self-progressions 
t(⊥)
w(⊥)
bottom of the tower 

real proof question: does w admit the tower? 
what does u admit? 

IDEA

the diacritical companion is kinda adding information: 
before, we just had functions f, and had to prove they were compatible 
now we have compatibility of pairs, but half the pair is something that 
already was compatible by itself: that's represented by w, i think. 
this should be proved or found in the paper. in the (s, f) pair, is 
f the part that is strongly compatible or weakly compatible? 
get definitions sorted: that's pretty easy. 

w is the weak companion. 

u represents 
the half that's valid in all cases or on only the weak case?

- can it be that this is 
equivalent to "weak compatibility?" - and it depends on w, of course. 

proof: does sound mean in the tower? 
well, sound means below t, which means in the tower, probably. 


what about reformulating the companion as the greatest sound function? 

well then how do we show it's compatible? 
- maybe there's a result on this already... either way. 
either the companion as the greatest compat is the greatest sound, 
or as the greatest sound is compat and therefore the greatest compat


so if we have an f, and f is compatible already, the game is to find an s such that 
(s, f) is compatible 

game: find "strong partner" of f



lemma 8 of tower paper, the up-to lemma, is the most interesting right now. 

let g be monotone. then the following are equivalent:

g <= t 
g ° t <= t 
∀ x, g (t x) <= t x -> g (b (t x)) <= b (t x)

(here t being the companion of b)

they also show b (t x) is below t (x).  

these are ways to prove soundness of g. (corollary is that b is sound)

 t x is in the tower, so g x <= t x means g x is in or below the tower. if g x
 is in the tower... is it sound? 


 where does w (x) fall w.r.t. the tower? 

well, w ⊥ = di_similarity p a == gfp (b1 ∪ b2)
what is w ⊤ ? maybe it is top 

research idea: 
disqualification of up-to-ness. 
a procedure that uses many characterizations of a function to attempt to 
decide if it is not a valid up to. 
can such a thing be sound? probably. can it be complete? probably not. 



- [ ] Key: diacritical companions via the tower (vice versa)
- [x] Prove theorem 2.6 : Let R ∈ L. If R ↣ᵇ(t R) then R <= ν( b ).

## Usability 
- [ ] Recover Build_mon - mon as a sublattice of monotone heterogenous functions?  
- [ ] make progress a true typeclass 
s.t. the type of di_similarity is
Progress X X -> Progress X X -> X. 
scratch

paper example 3.8 

R ↣ₚ R 
R ↣ₐ S 

x v1 ecxt(R) E2[e2]
x R e2 
y v1 R E2[y]

x v1 open-stuck, so must show E2 [e2] 
reduces to open-stuck 

x R e2 /\ R ↣ₚ R 
------------------
exists v, e2 ->* v /\ x z R v z, z fresh 

why? by definition 


y v1 R E2[y] x z R v z, z fresh 
----------------------
x v1 subst(R) E2[v]

why? 

y v1 R E2[y] /\  x x' R v x', x' fresh  
------------------------------
x v1 subst (R) E2[v]

sure, but very little explanation 
of how substitution works 


 
 relate definition 4.1 to t 

 evolve on Remark 4.9 so that diff between 
 respectfulness and compatibility goes
 away and we can recover good properties 
 of composition 

 we really need simplicity here. 
 things are hard to piece together. 

 Supposedly a picture: 

             top  ●───────────────────────────  (full relation)
                 │ \
                 │  \   ← b'-tower: the THIN CHAIN
       b' top →  ●   \     top ≥ b'top ≥ b'²top ≥ … ≥ gfp,
                 │    \    closed under b' and infima
      b'² top →  ●     \
                 │   ○ ← w R   (a w-closed element: above gfp,
                 │  /            below top, NOT on the b'-chain)
                 ● /
                  X  ← gfp b'  (= w bot = t b' bot : shared bottom)
                 ╱ ╲
                ╱   ╲  ← region BELOW gfp: also not in the tower
          bot  ●─────────────────────────────  (empty relation)

## Findings from porting InteractionTrees onto this library

- [x] `ic`/`mon` hint dbs were `#[export]`, so `icauto`/`monauto` silently had an
      empty database in any client that reached the library through an
      intermediate module. Now `#[global]`.
- [x] `coinduction R H` failed with "R is already used" when the goal's own
      telescope bound `R`. The candidate is now introduced privately and renamed
      after the telescope is reverted.
- [x] `coinduction` could not see a fixpoint hidden behind a definition, as in
      `Definition eutt := gfp b`. `apply gfp_prop` took `P` constant and the
      failure surfaced later as `pattern` finding no subterm. `expose_gfp` now
      unfolds to the fixpoint first, and reports a clear error when there is none.
- [x] `step` was `apply sub_bChain`, which only types at binary relations. It now
      goes through `leq` and works at any arity, with `step in`, `unstep`,
      `unstep in`, and the same unfolding as `coinduction`.
- [x] `icauto` now handles `Reflexive`/`Symmetric`/`Transitive`/`Proper` at
      arbitrary arity, so `Reflexive_chain` and friends are no longer limited to
      `mon (relation A)`. This closes "Reflexive_chain failing when elem has
      arguments".
- [x] `accumulate` reported an inf-closedness failure instead of its own error
      when the conclusion was spelt `elem (chain_b c)` rather than `b (elem c)`.

## Where definitions sit badly (survey only, nothing changed)

Line numbers are from the state at the end of the InteractionTrees port.

### coinduction library

1. `all.v` is `Require Export lattice tower rel tactics`. It does not export
   `companion.v`, and nothing else requires it, so `From Coinduction Require
   Import all` gives a user no companion theory at all. Either the companion
   belongs in `all.v` or it is dead code.

2. The `inf_closed` theory is spread over three files. `tower.v:11-33` has the
   definition together with `inf_closed_cap`, `inf_closed_all`,
   `inf_closed_impl` and `inf_closed_leq`. `tactics.v:35` adds
   `inf_closed_and` and `tactics.v:409` adds `inf_closed_cap_elem`. `rel.v:54-105`
   adds `inf_closed_reflexive`, `_symmetric`, `_transitive`, `_preorder`,
   `_equivalence`, `_respectful` and `_proper`. A reader looking for "what is
   known to be inf-closed" has to visit all three.

3. `tactics.v` is not only tactics. It defines `inf_closed_and` (line 35),
   `and_uncurry` and `and_curry` (294, 296), and a whole `Section s` (405-444)
   holding `inf_closed_cap_elem`, `Symmetrical'` and `by_symmetry'`. Those are
   ordinary lemmas and definitions that the tactics happen to apply.

4. The two solvers are declared in different files and in different styles.
   `icauto` and its `ic` database are in `tactics.v:44-58`. `monauto` and its
   `mon` database are in `lattice.v:617-670`, along with `apply_leq`,
   `induct_on_premise`, `functor_mono` and `mon_lift`. `lattice.v` also carries
   `CL_split` (105) and `dual` (152). Either both solvers belong next to the
   theory they discharge, or both belong in `tactics.v`.

5. Dead material in `lattice.v`, all with zero uses anywhere in the library:
   `lattice_bot` (58), `inf''` and `inf_same` (466-468, already marked
   "todo: remove this"), `CompleteLattice_Product` (491), `fst_monotone` and
   `snd_monotone` (516, 519), and the two `Add Parametric Morphism` blocks
   `fst_mor` and `snd_mor` (523-534, marked "TODO: make these instances").
   The product lattice and the projections were the support for `fst_mon` and
   `snd_mon`, which the return to an endofunctor `mon` removed.

6. `companion.v` carries abandoned experiments in the file body rather than in a
   scratch file: `B_` at 604 under a "Roger & Steve experiments" heading,
   `compat_chain_reverse` stated and `Abort`ed at 639-642 under a comment saying
   it is not true, two more `Abort`ed statements of `Ct` at 648 and 659, and a
   thirty-line commented-out block from 717 to the end of the file.

### InteractionTrees

7. `Eq/Eqit.v` is 2556 lines and holds every kind of thing at once. Its 52 tactic
   definitions arrive in thirteen separate clusters, at lines 229-387, 768-770,
   1442, 1703-1705, 1826-1829, 1968, 2045-2081, 2136 and 2327, interleaved with
   definitions, notations, inversion lemmas, `Proper` instances and the
   equational theory.

8. Two test modules ship inside that library file: `Module step_notation_tests`
   at 390-422 and `Module Tests` at 1260-1350.

9. `Section eqit_elem` at 2322 restates order facts about chain elements that
   `Section eqit_gen` at 609 already proves. `Reflexive_elem_eutt`,
   `Symmetric_elem_eutt` and `Equivalence_elem_ff` overlap
   `Reflexive_elem` (664), `Symmetric_elem` (672) and `Equivalence_elem`.

10. The `*Facts` split documented in `DEV.md` is inverted for `rutt`. `Eq/Rutt.v`
    is 287 lines with 18 lemmas, while `Eq/RuttFacts.v` is 460 lines with 11.
    The definition file carries most of the theory.

11. `Basics/Utils.v` is a grab-bag with no theme beyond "general". After the port
    it holds 18 tactics and one lemma, ranging from `inv` to `flatten_all` to
    `under_forall`.

12. `Interp/Traces.v:201` and `:211` define `step_` and `step`, which read as the
    coinduction `step` tactic. They are unrelated, and the names cost a reader a
    lookup every time.

## Why the b-form / F-form split exists, and how to close it

`eqit` has two shapes for the same proposition. The b-form is
`eqit_mon b1 b2 sim R1 R2 RR t1 t2`, whose two interesting arguments are
itrees. The F-form is `eqitF RR b1 b2 (sim R1 R2 RR) ot1 ot2`, whose two
interesting arguments are observations. Rewriting needs the b-form, because the
`Proper` instances are stated about itrees. Induction needs the F-form, because
`induction H` has to generalise the two arguments, and it cannot generalise
`observe t`.

Converting b-form to F-form is free, being delta and iota. Converting back is
not, and that is the whole reason `to_mon` exists. Going back means inventing a
`t` with `observe t = ot`, which eta on the itree record would supply. Rocq does
not supply it: definitional eta holds only for non-recursive primitive records,
and `itree` is coinductive. Checked three ways, and the error is

```
The term "eq_refl" has type "{| _observe := observe t |} = {| _observe := observe t |}"
while it is expected to have type "{| _observe := observe t |} = t"
```

`Set Primitive Projections` is already on in `Core/ITreeDefinition.v`, so this is
not something a flag fixes. `to_mon` fakes the missing eta with `change`, and
pays for it by turning `t` into `go (observe t)`, which is why it needs a second
case for the already-observed arguments and why a single-case version does not
compile. `bcbn` is the same symptom one level up: its tail rewrites
`go (observe t)` back to `t` with the propositional `itree_eta`, because the
definitional one does not exist.

The way to have both forms is equations rather than conversion, and the pieces
are already in the tree. `genobs t ot` is `remember (observe t) as ot`. It gives
induction a variable to generalise, and it leaves `Heqot : ot = observe t` in
context, which `simpobs` uses to rewrite back to tree form. The codebase does
this by hand at 86 sites. What is missing is that entering the functor and
remembering the observations are separate steps, so `icbn` throws the way back
away and `to_mon` has to guess it.

Proposal, one tactic that does both:

```coq
Ltac iview := cbn [body eqit_mon eqit_];
              repeat match goal with |- context [observe ?t] => genobs t ? end.
```

with `simpobs` as the return trip. If it works, `to_mon`, `to_mon_core`,
`to_mon_in`, `to_mon in`, `to_rmon`, `to_rmon_core` and `bcbn` all go, taking
the plumbing families from seven to about three. The risks are that 32 `to_mon`
call sites move, and that proofs already calling `genobs` by hand would remember
twice unless the tactic is idempotent.

Two smaller items in the same direction. `icbn` is `repeat red`, which unfolds
whatever head it meets; `rcbn` is `cbn [rutt_mon body]; try unfold rutt_`, which
names exactly what to unfold and cannot over-reduce. Standardising on the second
shape would let `icbn`, `rcbn` and the `cbn` half of `bcbn` become one tactic
parameterised by three names. And `icoinduction` stays: landing in b-form and
then stepping is a normal thing to want, so the wrapper carries real information.

## Done: library module boundaries

`monauto`, the `mon` hint database, `mon_lift`, `apply_leq`, `induct_on_premise`
and `functor_mono` moved from `lattice.v` to `tactics.v`, next to `icauto` and
the `ic` database. `inf_closed_and` and `inf_closed_cap_elem` moved from
`tactics.v` to `tower.v`, next to the other inf-closedness lemmas.
`Symmetrical'` and `by_symmetry'` moved from `tactics.v` to `rel.v`, which is
where `converse` lives and so the only file where they can be stated. `tactics.v`
now holds tactics and the two propositional helpers `and_curry` and `and_uncurry`
that `accumulate` applies.

