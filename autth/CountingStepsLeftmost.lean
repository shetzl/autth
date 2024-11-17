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

theorem DerivesLeftmostIn.terminal {n : ℕ} {v : List (Symbol T g.NT)}{x : List T}
    (h : g.DerivesLeftmostIn (x.map terminal) v n) : v = x.map terminal := by
  rcases n with _ | ⟨n⟩
  · have := h.zero
    exact this
  · obtain ⟨u, ⟨r, hr, hx⟩, h₂⟩ := h.head_of_succ
    exfalso
    exact hx.rewrite_terminal

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

theorem derivesLeftmostIn_cons' {n : ℕ}{x : Symbol T g.NT} {v : List (Symbol T g.NT)}{u : List T}
    (h : g.DerivesLeftmostIn (x :: v) (u.map terminal) n) :
    (∃ (w₁ w₂: List T) (m₁ m₂ : ℕ),m₁ ≤ n ∧ m₂ ≤ n ∧
    u = w₁ ++ w₂ ∧ g.DerivesLeftmostIn [x] (w₁.map terminal) m₁ ∧
    g.DerivesLeftmostIn v (w₂.map terminal) m₂) := by
  obtain ⟨u', hu, hu'⟩|⟨w₁, u₂, m₁, m₂, hm₁, hm₂, hu, h⟩ := derivesLeftmostIn_cons h
  · rw [List.map_eq_append_iff] at hu
    obtain ⟨w₁, w₂, hu, hw₁, hw₂⟩ := hu
    use w₁, w₂, n, 0
    refine ⟨by linarith, by linarith, hu, ?_, ?_⟩
    · simpa [hw₁] using hu'
    · rw [hw₂]
      exact DerivesLeftmostIn.refl _
  · obtain ⟨w₁', w₂, hu', hw₁', hw₂⟩ := List.map_eq_append_iff.mp hu
    rw [←hw₂] at hu
    use w₁', w₂, m₁, m₂, hm₁, hm₂, hu'
    rw [hw₁', hw₂]
    exact h
