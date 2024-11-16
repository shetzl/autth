/-
Copyright (c) 2024 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/
import autth.leftmost_deriv

universe uT uN
variable {T : Type uT}

namespace ContextFreeGrammar
open Symbol

/-- Given a context-free grammar `g`, strings `u` and `v`, and number `n`
`g.DerivesLeftmostIn u v n` means that `g` can transform `u` to `v` in `n` rewriting steps. -/
inductive DerivesLeftmostIn (g : ContextFreeGrammar.{uN} T) : List (Symbol T g.NT) → List (Symbol T g.NT) → ℕ → Prop
  | refl (w : List (Symbol T g.NT)) : g.DerivesLeftmostIn w w 0
  | tail (u v w : List (Symbol T g.NT)) (n : ℕ) : g.DerivesLeftmostIn u v n → g.ProducesLeftmost v w → g.DerivesLeftmostIn u w n.succ


lemma derivesLeftmost_iff_derivesLeftmostIn
    (g : ContextFreeGrammar.{uN} T) (v w : List (Symbol T g.NT)) :
    g.DerivesLeftmost v w ↔ ∃ n : ℕ, g.DerivesLeftmostIn v w n := by
  constructor
  · intro hgvw
    induction hgvw with
    | refl =>
      use 0
      left
    | tail _ last ih =>
      obtain ⟨n, ihn⟩ := ih
      use n.succ
      right
      · exact ihn
      · exact last
  · intro ⟨n, hgvwn⟩
    induction hgvwn with
    | refl => rfl
    | tail _ _ _ _ last ih => exact ih.trans_produces last

lemma mem_language_iff_derivesLeftmostIn (g : ContextFreeGrammar.{uN} T) (w : List T) :
    w ∈ g.language ↔ ∃ n, g.DerivesLeftmostIn [Symbol.nonterminal g.initial] (w.map Symbol.terminal) n := by
  rw [mem_language_iff, ←derives_leftmost_iff, derivesLeftmost_iff_derivesLeftmostIn]

variable {g : ContextFreeGrammar.{uN} T}

lemma DerivesLeftmostIn.zero_steps (w : List (Symbol T g.NT)) : g.DerivesLeftmostIn w w 0 := by
  left

lemma DerivesLeftmostIn.zero {w v: List (Symbol T g.NT)}(h : g.DerivesLeftmostIn w v 0) : v = w := by
  cases h
  · rfl

lemma ProducesLeftmost.single_step {v w : List (Symbol T g.NT)} (hvw : g.ProducesLeftmost v w) :
    g.DerivesLeftmostIn v w 1 := by
  right
  left
  exact hvw

variable {n : ℕ}

lemma DerivesLeftmostIn.trans_producesLeftmost {u v w : List (Symbol T g.NT)}
  (huv : g.DerivesLeftmostIn u v n) (hvw : g.ProducesLeftmost v w) :
    g.DerivesLeftmostIn u w n.succ :=
  DerivesLeftmostIn.tail u v w n huv hvw

@[trans]
lemma DerivesLeftmostIn.trans {u v w : List (Symbol T g.NT)} {m : ℕ}
    (huv : g.DerivesLeftmostIn u v n) (hvw : g.DerivesLeftmostIn v w m) :
    g.DerivesLeftmostIn u w (n + m) := by
  induction hvw with
  | refl => exact huv
  | tail _ _ _ _ last ih => exact trans_producesLeftmost ih last

lemma ProducesLeftmost.trans_derivesLeftmostIn {u v w : List (Symbol T g.NT)}
    (huv : g.ProducesLeftmost u v) (hvw : g.DerivesLeftmostIn v w n) :
    g.DerivesLeftmostIn u w n.succ :=
  n.succ_eq_one_add ▸ huv.single_step.trans hvw

lemma DerivesLeftmostIn.tail_of_succ {u w : List (Symbol T g.NT)}
    (huw : g.DerivesLeftmostIn u w n.succ) :
    ∃ v : List (Symbol T g.NT), g.DerivesLeftmostIn u v n ∧ g.ProducesLeftmost v w := by
  cases huw with
  | tail v w n huv hvw =>
    use v

lemma DerivesLeftmostIn.head_of_succ {u w : List (Symbol T g.NT)}
    (huw : g.DerivesLeftmostIn u w n.succ) :
    ∃ v : List (Symbol T g.NT), g.ProducesLeftmost u v ∧ g.DerivesLeftmostIn v w n := by
  induction n generalizing w with
  | zero =>
    cases huw with
    | tail v w n huv hvw =>
      cases huv with
      | refl => exact ⟨w, hvw, zero_steps w⟩
  | succ m ih =>
    cases huw with
    | tail v w n huv hvw =>
      obtain ⟨x, hux, hxv⟩ := ih huv
      exact ⟨x, hux, hxv.trans_producesLeftmost hvw⟩

/-- Add extra prefix to context-free deriving (number of steps unchanged). -/
lemma DerivesLeftmostIn.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.DerivesLeftmostIn v w n) (p : List T) :
    g.DerivesLeftmostIn ((p.map terminal) ++ v) ((p.map terminal) ++ w) n := by
  induction hvw with
  | refl => left
  | tail _ _ _ _ last ih => exact ih.trans_producesLeftmost <| last.append_left p

/-- Add extra postfix to context-free deriving (number of steps unchanged). -/
lemma DerivesLeftmostIn.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.DerivesLeftmostIn v w n) (p : List (Symbol T g.NT)) :
    g.DerivesLeftmostIn (v ++ p) (w ++ p) n := by
  induction hvw with
  | refl => left
  | tail _ _ _ _ last ih => exact ih.trans_producesLeftmost <| last.append_right p

theorem DerivesLeftmostIn.empty {n : ℕ} {v : List (Symbol T g.NT)}
    (h : g.DerivesLeftmostIn [] v n) : v = [] := by
  rcases n with _ | ⟨n⟩
  · have := h.zero
    exact this
  · obtain ⟨u, h₁, h₂⟩ := h.head_of_succ
    rw [ProducesLeftmost] at h₁
    obtain ⟨r, hr, h₁⟩ := h₁
    cases h₁

theorem derivesLeftmostIn_cons {n : ℕ}{x : Symbol T g.NT} {v u : List (Symbol T g.NT)}
    (h : g.DerivesLeftmostIn (x :: v) u n) :
    (∃ (u' : List (Symbol T g.NT)), u = u' ++ v ∧ g.DerivesLeftmostIn [x] u' n) ∨
    (∃ (w₁ : List T) (u₂ : List (Symbol T g.NT))(m₁ m₂ : ℕ),m₁ ≤ n ∧ m₂ ≤ n ∧
    u = w₁.map terminal ++ u₂ ∧ g.DerivesLeftmostIn [x] (w₁.map terminal) m₁ ∧
    g.DerivesLeftmostIn v u₂ m₂) := by
  induction h with
  | refl =>
    left
    use [x]
    exact ⟨by simp, DerivesLeftmostIn.refl _⟩
  | tail _ _ n _ last ih =>
    obtain ⟨u₁,hu⟩|⟨w₁,u₂, m₁, m₂, hm₁, hm₂, hu⟩ := ih
    · rw [hu.1] at last
      obtain ⟨r,hr,last⟩ := last
      obtain ⟨o₁,o₂,ho⟩|⟨w₁,o₂,ho⟩ := ContextFreeRule.rewrites_leftmost_append last
      · left
        exact ⟨o₁, by simp_all, hu.2.trans_producesLeftmost ⟨r,hr,ho.2.1⟩⟩
      · right
        refine ⟨w₁, o₂, n, 1, by linarith, by linarith, by simp_all,?_,?_⟩
        · simp_all
        · exact ProducesLeftmost.single_step ⟨r,hr,ho.2.2⟩
    · rw [hu.1] at last
      right
      use w₁
      obtain ⟨r,hr,last⟩ := last
      obtain ⟨o₁,o₂,ho⟩|⟨w₁', o₂, ho⟩ := ContextFreeRule.rewrites_leftmost_append last
      · exfalso
        exact ContextFreeRule.RewritesLeftmost.rewrite_terminal _ _ _ ho.2.1
      · exact ⟨o₂, m₁, m₂+1, by linarith, by linarith, by simp_all, hu.2.1,
        hu.2.2.trans_producesLeftmost ⟨r,hr,ho.2.2⟩⟩



/-
@[elab_as_elim]
lemma DerivesLeftmostIn.induction_refl_head {b : List (Symbol T g.NT)}
    {P : ∀ n : ℕ, ∀ a : List (Symbol T g.NT), g.DerivesLeftmostIn a b n → Prop}
    (refl : P 0 b (DerivesLeftmostIn.zero_steps b))
    (head : ∀ {n a c} (hac : g.ProducesLeftmost a c) (hcb : g.DerivesLeftmostIn c b n),
      P n c hcb → P n.succ a (hac.trans_derivesLeftmostIn hcb))
    {a : List (Symbol T g.NT)} (hab : g.DerivesLeftmostIn a b n) :
    P n a hab := by
  induction hab with
  | refl => exact refl
  | tail _ _ _ _ last ih =>
    apply ih
    · exact head last _ refl
    · intro _ _ _ produc deriv
      exact head produc (deriv.tail _ last)

-- Generic well-founded induction
@[elab_as_elim]
lemma induction_wf_head {n : ℕ} {b : List (Symbol T g.NT)}
    {P : ∀ n : ℕ, ∀ a : List (Symbol T g.NT), g.DerivesIn a b n → Prop}
    (step : ∀ {n a} {hab : g.DerivesIn a b n} (_ : ∀ m < n, ∀ c, (hcb : g.DerivesIn c b m) → P m c hcb),
      P n a hab)
    {a : List (Symbol T g.NT)} (hab : g.DerivesIn a b n) :
    P n a hab := by
    apply step
    intros m _ c hcb
    apply induction_wf_head
    exact step

private lemma DerivesIn.empty_of_append_left_aux {w u v : List (Symbol T g.NT)} {n : ℕ}
  (hwe : g.DerivesIn w [] n) (heq : w = u ++ v) : ∃ m ≤ n, g.DerivesIn u [] m := by
  revert u v
  induction hwe using DerivesIn.induction_refl_head with
  | refl => simp [DerivesIn.zero_steps]
  | @head m  u v huv _ ih =>
    intro x y heq
    obtain ⟨r, rin, huv⟩ := huv
    obtain ⟨p, q, h1, h2⟩ := ContextFreeRule.Rewrites.exists_parts huv
    rw [heq, List.append_assoc, List.append_eq_append_iff] at h1
    cases h1 with
    | inl h =>
      obtain ⟨x', hx, _⟩ := h
      have hveq : v = x ++ (x' ++ r.output ++ q) := by simp [h2, hx]
      obtain ⟨m', _, _⟩ := ih hveq
      use m'
      constructor <;> tauto
    | inr h =>
      obtain ⟨x', hx, hr⟩ := h
      cases x' with
      | nil =>
        have hveq : v = x ++ (r.output ++ q) := by simp [hx, h2]
        obtain ⟨m', _, _⟩ := ih hveq
        use m'
        constructor <;> tauto
      | cons h t =>
        obtain ⟨_, _⟩ := hr
        simp [←List.append_assoc] at h2
        obtain ⟨m', hm, hd⟩ := ih h2
        use m'.succ
        constructor
        · exact Nat.succ_le_succ hm
        · apply Produces.trans_derivesIn
          use r
          constructor
          exact rin
          rw [ContextFreeRule.rewrites_iff]
          use p, t
          constructor
          · simp [hx]
          · rfl
          exact hd

lemma DerivesIn.empty_of_append_left {u v : List (Symbol T g.NT)} (huv : g.DerivesIn (u ++ v) [] n) :
    ∃ m ≤ n, g.DerivesIn u [] m := by
  apply empty_of_append_left_aux <;> tauto

lemma DerivesIn.empty_of_append_right_aux {w u v : List (Symbol T g.NT)} {n : ℕ}
  (hwe : g.DerivesIn w [] n) (heq : w = u ++ v) : ∃ m ≤ n, g.DerivesIn v [] m := by
  revert u v
  induction hwe using DerivesIn.induction_refl_head with
  | refl => simp [DerivesIn.zero_steps]
  | @head m u v huv _ ih =>
    intro x y heq
    obtain ⟨r, rin, huv⟩ := huv
    obtain ⟨p, q, h1, h2⟩ := huv.exists_parts
    rw [heq, List.append_assoc, List.append_eq_append_iff] at h1
    cases h1 with
    | inl h =>
      obtain ⟨y', h1 , hy⟩ := h
      rw [h1, List.append_assoc, List.append_assoc] at h2
      obtain ⟨m', hm, hd⟩ := ih h2
      use m'.succ
      constructor
      · exact Nat.succ_le_succ hm
      · apply Produces.trans_derivesIn
        use r
        constructor
        exact rin
        rw [ContextFreeRule.rewrites_iff]
        use y', q
        constructor
        · simp
          exact hy
        · rfl
        simp [hd]
    | inr h =>
      obtain ⟨q', hx, hq⟩ := h
      cases q' with
      | nil =>
        simp at hq h2
        obtain ⟨m', hm, hd⟩ := ih h2
        use m'.succ
        constructor
        · exact Nat.succ_le_succ hm
        · apply Produces.trans_derivesIn
          use r
          constructor
          exact rin
          rw [ContextFreeRule.rewrites_iff]
          use [], q
          constructor
          · simp
            tauto
          · rfl
          exact hd
      | cons h t =>
        obtain ⟨_,_⟩ := hq
        simp at h2
        repeat rw [←List.append_assoc] at h2
        obtain ⟨m', hm, hd⟩ := ih h2
        use m'
        constructor
        · exact Nat.le_succ_of_le hm
        · exact hd

lemma DerivesIn.empty_of_append_right {u v : List (Symbol T g.NT)} (huv : g.DerivesIn (u ++ v) [] n) :
    ∃ m ≤ n, g.DerivesIn v [] m := by
  apply empty_of_append_right_aux <;> tauto

lemma DerivesIn.empty_of_append {w u v: List (Symbol T g.NT)} {n : ℕ}
  (hwe : g.DerivesIn (w ++ u ++ v) [] n) : ∃ m ≤ n, g.DerivesIn u [] m := by
  obtain ⟨m1, hm1n, hm1e⟩ := hwe.empty_of_append_left
  obtain ⟨m2, hm2n, hm2e⟩ := hm1e.empty_of_append_right
  exact ⟨m2, Nat.le_trans hm2n hm1n, hm2e⟩
-/
