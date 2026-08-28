## Usability 
- [x] Use camltac over ocaml plugin (moot: the plugin is gone, src/ removed,
      the tactics are pure ltac in tactics.v)
- [ ] Recover Build_mon - mon as a sublattice of monotone heterogenous functions?  
- [ ] make progress a true typeclass 
s.t. the type of di_similarity is
Progress X X -> Progress X X -> X. 
## Bugfixes
- [x] gfp in premise bug
- [x] apply_ptower (auto inf closed) for tower induction.
- [x] accumulate on hypotheses of shape `f (elem c) u v` -- regressed in the
      ltac rewrite, now fixed. monauto could not show
      `Proper (leq ==> leq) (fun P => ba P z y)`: body_mono is the right lemma
      but auto cannot invert `fun w => f w u v` into `fun w => Q (f w)` (not a
      miller pattern). fixed by mon_lift in lattice.v -- peel the arguments,
      then lift the leq hypothesis through each f via Hbody, which is the same
      two-step decomposition the plugin's qTs_mono did with f carried in the
      tcons cell. the old suite (theories/bugfixes.v, 5f59023) is now in
      tests.v as section accumulate_body; 10 of its 11 cases pass, including
      the two the plugin could not do (its uniformity restriction was a
      reification limit, not a real one). the 11th, a conclusion of shape
      `b (elem c) x y`, correctly still fails: `fun P => b P x y` is genuinely
      not inf-closed.
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
- used infra to rewrite symmetric tactic (symmetric', tactics.v)
- inf_closed dispatch for automatic tower induction proofs (icauto + `tower induction`)
- removed the ocaml plugin outright, and the diacritical/experiment files;
  everything removed is recoverable from commit 5f59023.
- fixed the accumulate regression on `f (elem c) u v` hypotheses (mon_lift)
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
(combine_companions.v was removed; recover from 5f59023)

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



- [x] Key: diacritical companions via the tower (vice versa) -- ANSWERED.
      (from theories/diacritical_redesign.v, removed; recover from 5f59023)

      question: can the passive law (P) `evolution p f f` (compat-strength) be
      relaxed to `f <= t b1` (up-to strength), giving a tower-native diacritical
      companion?

      NO for a FIRST-ORDER tower on the base lattice X, and the obstruction is
      structural rather than about compat-vs-<=t strength. the active law's
      conditional premise `R -p-> R` is a b1-POST-fixpoint condition (`R <= b1 R`,
      i.e. below gfp: it selects bisimulation candidates). tower induction lives
      on the opposite side -- chain elements are PRE-fixpoints (`b `x <= `x`,
      above gfp) -- and ptower's relativiser Q must be MONOTONE (up-closed), so
      it can never supply a post-fixpoint premise. the two sides meet only at gfp.
      `R <= b1 R` is not Proper (leq ==> leq): if it were, x <= y with x <= b1 x
      would give y <= b1 y -- false, take y := top.
      checked: active_premise_forces_fixpoint; w_in_tower_b2_stalls (tower
      induction for `w `x <= `x` stalls at exactly `b2 `x <= b1 (b2 `x)`).

      so the extra active power comes precisely from the post-fixpoint
      conditional law, a COINDUCTION-side object. realizable design: use ordinary
      tower induction, and at an active position SWAP to coinduction via
      di_coinduction (one lemma application) to get w.

      BUT the impossibility is specific to the first-order tower on X. it does
      NOT rule out a tower on the PAIR lattice L_lift X: the diacritical
      companion (u,w) is a di_similarity of the two evolution progressions on
      L_lift X, hence a gfp of a monotone SECOND-ORDER operator B_di --
      experiments.v: B_di, compan_gfp (compan == gfp B_di), B_di_spec, and the
      tower-induction principles di_chain_ind / di_tower. the post-fixpoint guard
      `R <= b1 R` becomes a harmless fixed side-condition inside B_di (it does
      not mention B_di's argument, so monotonicity survives).
      so: no first-order base-lattice tower, but a genuine SECOND-order
      pair-lattice tower -- the honest "tower induction based on the diacritical
      companion".

- up-to-eutt for itrees is NOT `<= w`, and the OPEN note at the end of
  diacritical_tower_example's Section weak is now settled (theories/itree_active_upto.v).
  - the cause is a head-KIND mismatch, not divergence as the note guessed. c_p is
    permissive WITHIN a frontier (CpRet/CpVis ignore their payload) but still demands
    both heads be the same kind, and eutt_clo strips the very taus a CpTau step relied
    on. witness over E := fun _ => unit, R := nat:
      S := {(Ret 0, Vis tt k)}      R0 := {(Tau (Ret 0), Tau (Vis tt k))}
    `passive_law_fails` kills the passive law of f_below_w AND the weakened
    f_below_w_cup target `cup (f S) S`. `eutt_clo_not_below_w` kills the conclusion
    outright, via the repo's own not_below_w.
  - it does not contradict the old paco euttG: euttG never uses up-to-eutt as a sound
    up-to function. only `eqitC _ _ false false` (the STRONG closure) is ever proved
    compatible in itrees; transU (the eutt one) lives fenced behind the high slot rH,
    and only a Vis restores it. up-to-eutt is a state transition paid for with
    observable progress, not a licence.
- [ ] SPIKE RESULT: ptower cannot carry the Vis guard.
  - the STEP goal DOES discharge (`spike_step`): with Q x := eutt_clo S <= x and
    P x := S <= x, a Vis-guarded S whose continuations lie in `cup (eutt_clo S) S` is
    covered by Q and P. this is what plain tower induction lacked.
  - but the CONCLUSION is circular (`Q_at_gfp_implies_goal`): ptower gives
    `forall x : Chain, Q x -> P x`, and instantiating at chain_gfp demands
    `eutt_clo S <= eutt`, which already yields the goal `S <= eutt`.
  - and the repair Q x := eutt_clo x <= x is not Proper (leq ==> leq)
    (`eutt_closedness_not_monotone`, witness bot <= S0). same obstruction as
    diacritical_redesign.v: a down-closed side condition where ptower wants up-closed.
  - so the guard needs something other than a monotone relativiser. NEXT: decide
    between a standalone bool-indexed relation (mini-euttG with its own soundness
    proof) and something else.

- a genuinely ACTIVE-ONLY up-to technique exists, with a counterexample showing
  it is not an ordinary one. (from theories/active_only.v, removed; recover from
  5f59023.) setting: passive step pstep total and deterministic, active qstep
  arbitrary; upto_pstep S = S u {(pstep u, pstep v) | S u v} ("up to one passive
  step").
  - upto_pstep_below_w: sound ACTIVE technique (<= w). its active law genuinely
    consumes the diacritical premise R <= bp R.
  - upto_pstep_not_ordinary: NOT a sound ordinary up-to technique
    (not <= t (bp cap bq)) -- six-state counterexample: two chains of passive
    steps, the A-side middle state has a q-step and the B-side does not, so A0
    and B0 are not bisimilar, yet {(A0,B0)} progresses into upto_pstep of itself.
    so this is the phenomenon the diacritical companion exists for: usable in
    active position, unsound in passive position.
  - C0_D0_chain: an active-only technique used INSIDE an ordinary coinduction
    proof, via the guarded behaviour b_uw (experiments.v) -- the passive conjunct
    of the goal offers u, the active conjunct offers w, so the position in the
    goal decides which techniques are legitimate.
  - the TOWER is NECESSARY, not just convenient, for upto_pstep_strict (drop the
    S summand, return only shifted pairs: not inflationary, which breaks the
    compatibility-style proof). f_below_w_b would need
    `forall R S, R <= bp R -> R <= bq S -> f R <= bq (f S)`, and that is FALSE
    for upto_pstep_strict -- witness: two parallel chains of four states with a
    single q-step in the middle of each. the tower target `snd x S` does contain
    S (id_below_snd_chain), so f_below_w_cup goes through.
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
