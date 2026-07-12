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
