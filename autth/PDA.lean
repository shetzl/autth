import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Tactic
import Mathlib.Data.List.Join
import Mathlib.Util.Delaborators
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.EpsilonNFA

structure PDA (Q T S : Type) [Fintype Q] [Fintype T] [Fintype S] where
  initial_state : Q
  start_symbol : S
  final_states : Set Q
  transition_fun : Q → T → S → Set (Q × List S)
  transition_fun' : Q → S → Set (Q × List S)

namespace PDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

@[ext]
structure conf (p : PDA Q T S) where
  state : Q
  input : List T
  stack : List S

variable {pda : PDA Q T S}

namespace conf

abbrev appendInput (r : conf pda) (x : List T) : conf pda :=
  ⟨r.state, r.input++x, r.stack⟩

abbrev appendStack (r : conf pda) (β : List S) : conf pda :=
  ⟨r.state, r.input, r.stack++β⟩

abbrev stackPostfix (r : conf pda) (β : List S) : Prop :=
  ∃ α : List S, r.stack = α++β

abbrev stackPostfixNontriv (r : conf pda) (β : List S): Prop :=
  ∃ α : List S, α.length > 0 ∧ r.stack = α++β

end conf

def step (r₁ : conf pda) : Set (conf pda) :=
  match r₁ with
    | ⟨q, a::w, Z::α⟩ =>
        { r₂ : conf pda | ∃ (p : Q) (β : List S), (p,β) ∈ pda.transition_fun q a Z ∧
                          r₂ = ⟨p, w, (β ++ α)⟩ } ∪
        { r₂ : conf pda | ∃ (p : Q) (β : List S), (p,β) ∈ pda.transition_fun' q Z ∧
                          r₂ = ⟨p, a :: w, (β ++ α)⟩ }
    | ⟨q, [], Z::α⟩ => { r₂ : conf pda | ∃ (p : Q) (β : List S), (p,β) ∈ pda.transition_fun' q Z ∧
                                          r₂ = ⟨p, [], (β ++ α)⟩ }
    | ⟨q, w, []⟩ => { r₂ : conf pda | r₂ = ⟨q, w, []⟩ } -- Empty stack

def stepSet (R : Set (conf pda)) : Set (conf pda) :=
  ⋃ r ∈ R, step r

def stepSetN (n : ℕ) (R : Set (conf pda))  : Set (conf pda) :=
  match n with
  | 0 => R
  | Nat.succ m => stepSet (stepSetN m R)


def Reaches₁ (r₁ r₂ : conf pda) : Prop := r₂ ∈ step r₁
def Reaches : conf pda → conf pda → Prop := Relation.ReflTransGen Reaches₁

inductive ReachesIn : ℕ → conf pda → conf pda → Prop :=
  | refl : (r₁ : conf pda)  → ReachesIn 0 r₁ r₁
  | step : {n: ℕ} → {r₁ r₂ r₃ : conf pda} → ReachesIn n r₁ r₂ → Reaches₁ r₂ r₃ → ReachesIn (n+1) r₁ r₃


def acceptsByEmptyStack (pda : PDA Q T S) : Language T :=
  { w : List T | ∃ q : Q,
      Reaches (⟨pda.initial_state, w, [pda.start_symbol]⟩ : conf pda) ⟨q, [], []⟩ }

def acceptsByFinalState (pda : PDA Q T S) : Language T :=
  { w : List T | ∃ q  ∈ pda.final_states, ∃ γ : List S,
      Reaches (⟨pda.initial_state, w, [pda.start_symbol]⟩ : conf pda) ⟨q, [], γ⟩ }

-- Martin: This theorem already exists.
private theorem append_cancel (v x w : List T) : v ++ x = w ++ x ↔ v = w := by
  apply List.append_left_inj

@[refl]
theorem Reaches.refl (r₁ : conf pda) : Reaches r₁ r₁ := Relation.ReflTransGen.refl

@[refl]
theorem reachesIn.refl (r₁ : conf pda) : ReachesIn 0 r₁ r₁ := ReachesIn.refl r₁

variable {r₁ r₂ : conf pda}


theorem reachesIn_zero (h: ReachesIn 0 r₁ r₂) : r₁ = r₂ := by
  rcases h with _|_
  · rfl

theorem reaches₁_iff_reachesIn_one : Reaches₁ r₁ r₂ ↔ ReachesIn 1 r₁ r₂ := by
  constructor
  · exact ReachesIn.step (by rfl)
  · intro h
    rcases h with _ | ⟨h₁,h₂⟩
    · apply reachesIn_zero at h₁
      simp_all

theorem reachesIn_of_n_one {r₃ : conf pda} {n : ℕ} (h₁ : ReachesIn n r₁ r₂) (h₂ : ReachesIn 1 r₂ r₃) :
    ReachesIn (n+1) r₁ r₃ :=  ReachesIn.step h₁ (reaches₁_iff_reachesIn_one.mpr h₂)


theorem reachesIn_one : ReachesIn 1 r₁ r₂ ↔ r₂ ∈ step r₁ := by
  rw [←reaches₁_iff_reachesIn_one,Reaches₁]

theorem reachesIn_iff_split_last {n : ℕ} :
    (∃ c : conf pda, ReachesIn n r₁ c ∧ ReachesIn 1 c r₂) ↔ ReachesIn (n+1) r₁ r₂ := by
  constructor
  · intro ⟨c,h⟩
    exact reachesIn_of_n_one h.1 h.2
  · intro h
    rcases h with _ | @⟨n,_,c,_,h₀,h₁⟩
    use c
    exact ⟨h₀,reaches₁_iff_reachesIn_one.mp h₁⟩


theorem reachesIn_of_one_n {r₃ : conf pda} {n : ℕ} (h₁ : ReachesIn 1 r₁ r₂) (h₂ : ReachesIn n r₂ r₃) :
    ReachesIn (n+1) r₁ r₃ := by
  induction' n with n ih generalizing r₃
  · obtain ⟨rfl⟩ := reachesIn_zero h₂
    simp_all
  · obtain ⟨c,hc₁,hc₂⟩ := reachesIn_iff_split_last.mpr h₂
    apply ReachesIn.step
    exact ih hc₁
    exact reaches₁_iff_reachesIn_one.mpr hc₂

theorem reachesIn_iff_split_first {n : ℕ}:
    (∃ c : conf pda, ReachesIn 1 r₁ c ∧ ReachesIn n c r₂) ↔ ReachesIn (n+1) r₁ r₂ := by
  constructor
  · intro ⟨c,h₁,h₂⟩
    exact reachesIn_of_one_n h₁ h₂
  · intro h
    induction' n with n ih generalizing r₂
    · use r₂
    · rcases h with _|@⟨_,_,r₂',_,h₁,h₂⟩
      obtain ⟨c,hc₁,hc₂⟩ := ih h₁
      refine ⟨c,hc₁,?_⟩
      apply reachesIn_of_n_one
      exact hc₂
      exact reaches₁_iff_reachesIn_one.mp h₂


theorem ReachesIn.trans {r₃ : conf pda} {n m : ℕ} (h₁ : ReachesIn n r₁ r₂) (h₂ : ReachesIn m r₂ r₃) :
    ∃ k ≤ n+m, ReachesIn k r₁ r₃ := by
  induction' m with m ih generalizing r₃
  · use n
    apply reachesIn_zero at h₂
    simp_all
  · obtain ⟨c,hc₁,hc₂⟩:= reachesIn_iff_split_last.mpr h₂
    obtain ⟨k,ih⟩ := ih hc₁
    use k+1
    exact ⟨by linarith [ih.1],reachesIn_iff_split_last.mp ⟨c, ih.2, hc₂⟩⟩

theorem reaches_iff_reachesIn : Reaches r₁ r₂ ↔ ∃ n : ℕ, ReachesIn n r₁ r₂ := by
  constructor
  · intro h
    induction h with
    | refl => use 0
    | @tail c r₂ h₁ h₂ ih =>
      obtain ⟨n,hn⟩ := ih
      use n+1
      rw [←reachesIn_iff_split_last]
      exact ⟨c, hn, reaches₁_iff_reachesIn_one.mp h₂⟩
  · intro ⟨n,hn⟩
    induction' n with n ih generalizing r₂
    · apply reachesIn_zero at hn
      rw [hn]
    · obtain ⟨c,hc₁,hc₂⟩ :=  reachesIn_iff_split_last.mpr hn
      rw [←reaches₁_iff_reachesIn_one] at hc₂
      exact Relation.ReflTransGen.tail (ih hc₁) hc₂

theorem Reaches.trans {r₃ : conf pda} (h₁ : Reaches r₁ r₂) (h₂ : Reaches r₂ r₃) :
    Reaches r₁ r₃ := Relation.ReflTransGen.trans h₁ h₂

theorem decreasing_input_one (h : ReachesIn 1 r₁ r₂) :
    ∃ w : List T, r₁.input = w ++ r₂.input := by
  apply reachesIn_one.mp at h
  rcases r₁ with ⟨q,_|⟨a,w⟩,_|⟨Z,β⟩⟩ <;> simp [PDA,conf,step] at *
  · rw [h]
  · obtain ⟨_,_,h⟩ := h
    rw [h.2]
  · rw [h]
    simp [PDA]
  · rcases h with h|h
    · obtain ⟨p,β,h⟩ := h
      rw [h.2]
      simp
      use [a]
      simp
    · obtain ⟨p,β,h⟩ := h
      rw [h.2]
      simp

theorem decreasing_input (h : Reaches r₁ r₂) :
    ∃ w : List T, r₁.input = w ++ r₂.input := by
  rw [reaches_iff_reachesIn] at h
  obtain ⟨n,h'⟩ := h
  induction' n with n ih generalizing r₂
  · apply reachesIn_zero at h'
    use []
    simp_all
  · apply reachesIn_iff_split_last.mpr at h'
    obtain ⟨c,h',h''⟩ := h'
    apply ih at h'
    apply decreasing_input_one at h''
    obtain ⟨w₁,hw₁⟩ :=  h'
    obtain ⟨w₂,hw₂⟩ :=  h''
    use w₁++w₂
    simp [hw₁,hw₂]

theorem unconsumed_input_one (x : List T) :
    ReachesIn 1 r₁ r₂ ↔ ReachesIn 1 (r₁.appendInput x) (r₂.appendInput x) := by
  constructor
  · intro h
    rcases r₂ with ⟨p,v,α⟩
    rcases r₁ with ⟨q,_|⟨a,w⟩,_|⟨Z,β⟩⟩ <;>
    simp [reachesIn_one,step,conf.appendInput] at *
    · assumption
    · rcases x with _|⟨a,w⟩ <;> simp_all
    · simp [h]
    · rw [←List.cons_append]
      rw [append_cancel]
      exact h
  · intro h
    rcases r₂ with ⟨p,v,α⟩
    rcases r₁ with ⟨q,_|⟨a,w⟩,_|⟨Z,β⟩⟩ <;>
    simp [reachesIn_one,step,conf.appendInput] at *
    · assumption
    · rcases x with _|⟨a,w⟩
      · simp at h; assumption
      · simp at h
        rcases h with h|h
        · obtain ⟨p,β,h⟩ := h
          have : (v ++ a :: w).length = w.length := by rw [h.2.2.1]
          rw [List.length_append,List.length_cons] at this
          linarith
        · assumption
    · rwa [←List.cons_append, append_cancel] at h
    · rwa [←List.cons_append, append_cancel] at h

theorem unconsumed_input_N {n : ℕ} (x : List T) :
    ReachesIn n r₁ r₂ ↔ ReachesIn n (r₁.appendInput x) (r₂.appendInput x) := by
  constructor
  · induction' n with n ih generalizing r₁ r₂
    case zero =>
      intro h
      apply reachesIn_zero at h
      rw [h]
    case succ =>
      intro h
      apply reachesIn_iff_split_last.mpr at h
      obtain ⟨c,h'⟩ := h
      have : ReachesIn n (r₁.appendInput x) (c.appendInput x) := ih h'.1
      apply And.right at h'
      rw [unconsumed_input_one x] at h'
      rw [←reachesIn_iff_split_last]
      use c.appendInput x
  · induction' n with n ih generalizing r₁ r₂
    · intro h
      apply reachesIn_zero at h
      simp only [conf.appendInput,conf.mk.injEq] at h
      obtain rfl : r₁ = r₂ := by ext <;> simp_all
      rfl
    · intro h
      rw [←reachesIn_iff_split_last] at *
      obtain ⟨c,h⟩ := h
      have := decreasing_input_one h.2
      obtain ⟨w,h'⟩ := this
      set c' : conf pda := ⟨c.state,w++r₂.input,c.stack⟩ with def_c'
      have : c'.appendInput x = c := by
        rcases c with ⟨q,l,β⟩
        simp [def_c',h',conf.appendInput,conf] at *
        exact h'.symm
      rw [←this] at h
      use c'
      constructor
      · apply ih
        exact h.1
      · apply (unconsumed_input_one x).mpr
        exact h.2

theorem unconsumed_input (x : List T) :
    Reaches r₁ r₂ ↔ Reaches (r₁.appendInput x) (r₂.appendInput x) := by
  rw [reaches_iff_reachesIn,reaches_iff_reachesIn]
  constructor <;> intro ⟨n,h'⟩ <;> use n
  · exact (unconsumed_input_N x).mp h'
  · exact (unconsumed_input_N x).mpr h'


theorem reachesIn_pos_of_not_self {n : ℕ} (h : r₁ ≠ r₂) :
    ReachesIn n r₁ r₂ → n > 0 := by
  rcases n with _ | ⟨n⟩
  · intro h
    apply reachesIn_zero at h
    contradiction
  · intro _
    apply Nat.zero_lt_succ

theorem reachesIn_one_on_empty_stack {q p: Q}{w w': List T}{α : List S}:
    pda.ReachesIn 1 ⟨q, w, []⟩ ⟨p, w', α⟩ → w=w' ∧ α = [] ∧ q=p:= by
  intro h
  rw [reachesIn_one] at h
  simp only [step] at h
  rw [Set.mem_setOf, conf.mk.injEq] at h
  simp [h]

theorem reaches_on_empty_stack {q p: Q}{w w': List T}{α : List S}:
    pda.Reaches ⟨q, w, []⟩ ⟨p, w', α⟩ → w=w' ∧ α = [] := by
  intro h
  rw [reaches_iff_reachesIn] at h
  obtain ⟨n,hr⟩ := h
  induction' n with n ih
  · apply reachesIn_zero at hr
    rw [conf.mk.injEq] at hr
    simp [hr]
  · rw [←reachesIn_iff_split_first] at hr
    obtain ⟨⟨q',v,α'⟩,h₁,h₂⟩ := hr
    apply reachesIn_one_on_empty_stack at h₁
    rw  [←h₁.1, h₁.2.1, ←h₁.2.2] at h₂
    apply ih at h₂
    simp [h₂]

theorem reaches_of_reachesIn  {n: ℕ}(h: pda.ReachesIn n r₁ r₂) : pda.Reaches r₁ r₂ :=
  reaches_iff_reachesIn.mpr ⟨n, h⟩
