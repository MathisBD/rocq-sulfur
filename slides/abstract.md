Sulfur: substitution generation using a logical framework

When formalizing the meta-theory of lambda calculi in proof assistants
such as Rocq, a central design decision is the choice of binder representation.
De Bruijn indices are a popular option because they make alpha-equivalence
coincide with syntactic equality. However, they also introduce significant
overhead in the form of lift and renaming operations, which require many
technical lemmas and can make proofs tedious.

To address this, tools such as Autosubst automate repetitive aspects of
dealing with de Bruijn indices and substitution using boilerplate generation.
In this talk, I present Sulfur, a Rocq plugin that similarly automates reasoning
about substitutions, but with a different and more efficient approach.

Given a user-defined language signature, Sulfur automatically generates:
1. Substitution functions.
2. Standard lemmas about substitution.
3. A tactic `asimpl` to simplify terms involving substitutions.
While Sulfur provides the same user interface as Autosubst,
its implementation diverges significantly. In particular, Autosubst's
`asimpl` tactic relies on Rocq's setoid rewrite facilities, and has significant
performance issues when used in large developments.
Sulfur aims to improve performance by using a logical framework approach:
it defines a generic notion of syntax within Rocq, on top of which substitution
and standard sigma calculus lemmas are developed. The framework is
instantiated to a specific (user-provided) language using
meta-programming. The key benefit of this approach is that `asimpl`
can be implemented as a reification tactic: we implement a simplification
function on our generic syntax, and prove it correct once and for all.
We will discuss the tradeoffs of the logical framework approach,
in particular regarding implementation effort and performance of `asimpl`.

This work was carried out during an internship supervised by Théo
Winterhalter.