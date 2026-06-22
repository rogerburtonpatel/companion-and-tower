## Basics
- [x] Port lattice (trivial)
- [x] Port mon_h 
- [x] Port progress
- [x] Port rest
## Theory 
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



so if we have an f, and f is compatible already, the game is to find an s such that 
(s, f) is compatible 

lemma 8 of tower paper, the up-to lemma, is the most interesting right now. 

let g be monotone. then the following are equivalent:

g <= t 
g ° t <= t 
∀ x, g (t x) <= t x -> g (f (t x)) <= f (t x)

(here t being the companion of f)

they also show f (t x) is below t (x).  

these are ways to prove soundness of g. (corollary is that f is sound)




research idea: 
disqualification of up-to-ness. 
a procedure that uses many characterizations of a function to attempt to 
decide if it is not a valid up to. 
can such a thing be sound? probably. can it be complete? probably not. 



- [ ] Key: diacritical companions via the tower (vice versa)
- [x] Prove theorem 2.6 : Let R ∈ L. If R ↣ᵇ(t R) then R <= ν( b ).

## Usability 
- [ ] Recover Build_mon - mon as a sublattice of monotone heterogenous functions?  

