The theory of diacritical companions tells us that (s, f) is a pair of 
sound up-to functions when 
... laws... 

This approach gives us validity of both a strong *and* a weak up-to 
technique (s and f, respectively). But determining the validity of 
a strong up-to technique is already achievable via a simpler approach
that is more uniform with proof by coinduction; namely, tower induction: 
...

The ability to discover a weak up-to technique, however, is extremely 
useful. 

IDEA: the strong up-to technique is ALWAYS the companion, aka the function that
works as a strong technique all the time. Finding the weak up-to is then the
game. 

What we need to do is get a p, a s.t. we don't have to work too hard. 

Ideally p is b, yes? 

Or can we derive an auto-split? 

How did gpaco do weak compatibility? 
Well, they used the vclo parameter - when you went under vis, 
you could do coinduction up to vclo; when you went under tau, 
you could only do coinduction up to sim. 
This let you do transitivity only when valid. 

Can we recover this without having to change our definitions? 
I mean, we define our passive and active progresses in terms of 
boolean flags and vclo on eqitF.

So what do we do now? 

What we want: a new, simpler equational theory for weak bisim. 
No more gclo or vclo, just b as simple as can be. 

How? 

Well, the simple fact is that in order for any of this to work, we need a
passive and active process. This is something that we need vclo for. 
Just use id for the start and make everything simple. 

Then a way to prove soundness of up-to: 

Rather than doing it for (s, f), do for one at a time: find 
a "default" s/f s.t. they ALWAYS fulfill the laws for a real instantiation
of the other. Maybe bot, id, top, t, ... 

But really we don't care about s. And we REALLY don't want to use vclo if 
we can avoid it, though that still might be the simplest way of deriving 
a `p` and `a` from `b`... 

The tricky bit is is that we need to get `w`, for which we need a `p` and 
`a.` 

So, is there any simpler way than vclo to define `p` and `a` from `b`? 
Maybe not. But it should be ALWAYS IGNORABLE. 

This would be really nice to do with metaprogramming, huh? 

The real application domain here is ctrees: if we find a way to 
show off the power of the technique in making ctrees very flexible 
with what constitutes weak/strong bisimulation, that would be amazing...



So here is a goal:


Define `b` 
prove it monotone 

Then declare constructors that are passive vs active. 
Automatically insert vclo with a metaprogram. 
This would be sick. 

So what is `p` and `a`? `a` is the version with `vclo` switched on, 
`p` is the version without that...? this is a subtle but very important 
point. I don't know what defines it, exactly.  

take its gfp. 