# Decomposition examples

It would probably be useful to have examples of varying difficulty.
For our use case we know that our target field will be largely unfamiliar to any agent,
at least compared to natural numbers or standard datatypes (e.g. lists).
Conceptually, if we visuallize theorems as a tree, then we can think of a theorems "difficulty" as being
a combination of a proofs incoming neighbers and it depth with respect to root node of the tree.
The depth part of this difficulty can most likely be discharged via recursion (at least, conceptually this makes sense)
Discharging the depth of a theorem *is* part of decomposition, however since it gives relatively little information about
a model's actual planning ability, this is not as useful to test.
Moreover, we are generally working in a synthetic domain; in which, hopefully, we don't have to deal with deep axioms.
The breadth part of this is our job: what lemmas does a theorem need to use in its proof?

I was also thinking about what a "good" decomposition would be.
It's certainly not how small and granular we can make the decomposition--that would just be tactics.
And more on this point, "smaller" is never our goal here. It's *mostly* true,
but for problems where you reduce to something more general (e.g. FLT), it's not true.
It's also probably not a literal code extraction. Technically you could inline all your lemmas, but this is obviously bad.

Here I will detail the "decomposition difficulty" (for a model) of the examples and explain whether they are naturally
proof guided, goal guided, or some combination.
By natural here I mean just what I would imagine the average mathematician (or really, me) would do for each proof.
It's also important to note that I am using goal/proof-guided to describe how one of these proofs works.
In practice, these are methods that a model would use
## Easy:
- Straight forward proofs like commutativity, associativity of natural numbers, etc.
- ListReversal: Putting this one here because it's generally canonical. 
  This theorem seems to naturally be proof-guided, since a user would likely attempt induction,
  hit a roadblock at the reverse-distribution part, then write the lemma for that.
## Medium:
- InifinitudeOfPrimes: This is an elementary number theory proof so it's definitely medium.
  For sake of this proof I am thinking of Euclid's proof.
  I would say this more proof-guided than goal-guided. Since in my example I only
  state the ring theoretic definition of prime, which does not contain the irreducible quality
  that primes also have in $\mathbb{Z}$, one could argue that a model would have to plan out how to include this definition / factoring property for primes.
- Yoneda: While abstract, the Yoneda lemma is more of a constructive direct proof. Honestly probably more naturally proof-guided.
## Hard:
- LeftAdjointColimit: Harder since definition and deals with cones (frowns). This is goal-guided, I would
  hope that a model passes to hom-functors.
- CircleFundamentalGroup: Hard. Absolutely goal-guided.
- I would like to include one here that I would say is naturally proof-guided, but the first thing that comes to mind is preservation in STLC with de Bruijn. I don't want to code that again.