import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.RegularExpressions

open Classical

#check RegularExpression

inductive Alphabet where
  | a | b | c

section
open Alphabet RegularExpression

#check [a, a, b]
#check comp (star (char a)) (star (char b))

/-- Example theorem showing that `aab` is in `a*b*`. -/
private theorem my_first_theorem: [a,a,b] ∈ matches' (comp (star (char a)) (star (char b))) := by
  simp
  use [a,a]
  constructor
  · rw [Language.mem_kstar_iff_exists_nonempty]
    use [[a],[a]]
    simp
    rfl
  · use [b]
    constructor
    · rw [Language.mem_kstar_iff_exists_nonempty]
      use [[b]]
      simp only [List.flatten_cons, List.flatten_nil, List.singleton_append, List.mem_singleton, ne_eq,
        forall_eq, List.cons_ne_self, not_false_eq_true, and_true, true_and]
      rfl
    simp
end

#check Symbol
#check Symbol Alphabet Unit

private abbrev a : Symbol Alphabet Unit := .terminal Alphabet.a
private abbrev b : Symbol Alphabet Unit := .terminal Alphabet.b
private abbrev c : Symbol Alphabet Unit := .terminal Alphabet.c
private abbrev S : Symbol Alphabet Unit := .nonterminal ()

private def myfirstrule : ( ContextFreeRule Alphabet Unit ) where
  input := ()
  output := List.nil

private def mysecondrule : (ContextFreeRule Alphabet Unit) where
  input := ()
  output := [a, S, b]

#check Finset (ContextFreeRule Alphabet Unit)
#check ContextFreeGrammar Alphabet

private noncomputable def mygrammar : ( ContextFreeGrammar Alphabet ) where
  NT := Unit
  initial := ()
  rules := { myfirstrule, mysecondrule }

#print mygrammar
#print myfirstrule
#print mysecondrule

#check ContextFreeGrammar.language mygrammar
#check [a,b]

/-- example theorem showing that ε is in the language of the grammar S -> ε | aSb -/
private theorem my_second_theorem : List.nil ∈ mygrammar.language := by
  rw [ContextFreeGrammar.mem_language_iff]
  apply ContextFreeGrammar.Produces.single
  use myfirstrule
  constructor
  · unfold mygrammar
    simp
  · rw [ContextFreeRule.rewrites_iff]
    use [], []
    unfold mygrammar myfirstrule
    simp

/-- example theorem showing that ab is in the language of the grammar S -> ε | aSb -/
private theorem my_third_theorem : [.a, .b] ∈ mygrammar.language := by
  apply (ContextFreeGrammar.mem_language_iff mygrammar [.a, .b]).mpr
  have fst : mygrammar.Derives [Symbol.nonterminal mygrammar.initial] [a, S, b] := by
    apply ContextFreeGrammar.Produces.single
    use mysecondrule
    constructor
    · unfold mygrammar
      simp
    · rw [ContextFreeRule.rewrites_iff]
      use [], []
      unfold mygrammar mysecondrule
      simp
  have snd : mygrammar.Derives [a, S, b] [a, b] := by
    apply ContextFreeGrammar.Produces.single
    use myfirstrule
    constructor
    · unfold mygrammar
      simp
    · rw [ContextFreeRule.rewrites_iff]
      use [a], [b]
      unfold myfirstrule
      simp
  exact ContextFreeGrammar.Derives.trans fst snd

/-- example theorem showing that aab is not in the language of the grammar S -> ε | aSb -/
private theorem my_fourth_theorem : [.a, .a, .b] ∉ mygrammar.language := by
 sorry

--#min_imports
