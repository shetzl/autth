import autth.PDA

open PDA

-- applies to any PDA -> move to PDA.lean?
theorem reaches1_of_transition_fun {Q T S: Type} [Fintype Q] [Fintype T] [Fintype S] (M : PDA Q T S)
  (p q : Q) (w : List T) (Z : S) (β γ : List S) (h: (p,β) ∈ M.transition_fun' q Z) :
  Reaches₁ (⟨q, w, Z::γ⟩ : conf M) ⟨p,w,β++γ⟩ := by
  unfold Reaches₁
  unfold step
  match w with
    | a::v => simp; exact h
    | [] => simp; exact h

-- add new inital and final states
inductive add_init_final ( π : Type ) where
  | newinit
  | newfinal
  | oldstate: π -> (add_init_final π )
deriving Fintype
open add_init_final

-- add new start symbol to stack alphabet
inductive add_start_symbol ( σ : Type ) where
  | newstart
  | oldsymbol : σ → ( add_start_symbol σ)
deriving Fintype
open add_start_symbol

-- states Q, alphabet T, stack alphabet S
variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

-- coercions
instance : Coe Q (add_init_final Q) where
  coe q := (oldstate q)
instance : Coe S (add_start_symbol S) where
  coe Z := (oldsymbol Z)
instance : Coe (Q × (List S)) ((add_init_final Q) × (List (add_start_symbol S))) where
  coe p := ( (p.1), (p.2) )
instance : Coe (Set (Q × (List S))) (Set ((add_init_final Q) × (List (add_start_symbol S)))) where
  coe A := { (x.1,x.2) | x ∈ A }

--- define new transition function
abbrev newtransition_fun' (M : PDA Q T S) (q : (add_init_final Q)) (Z : (add_start_symbol S)) : Set ((add_init_final Q) × List (add_start_symbol S)) :=
  match q with
    | newinit => match Z with
      | newstart => {((oldstate M.initial_state),[(oldsymbol M.start_symbol),newstart])}
      | (oldsymbol _) => ∅
    | (oldstate p) => match Z with
      | newstart => {(newfinal,[])}
      | (oldsymbol Y) => (M.transition_fun' p Y)
    | newfinal => ∅

abbrev newtransition_fun (M : PDA Q T S) (q : (add_init_final Q)) (a : T) (Z : (add_start_symbol S)) : Set ((add_init_final Q) × List (add_start_symbol S)) :=
  match q with
    | newinit => ∅
    | (oldstate p) => match Z with
      | newstart => ∅
      | (oldsymbol Y) => (M.transition_fun p a Y)
    | newfinal => ∅

-- define translation function of PDAs
abbrev estack_to_fstate (M : PDA Q T S) : PDA (add_init_final Q) T (add_start_symbol S) := {
  initial_state := newinit
  start_symbol := newstart
  final_states := { newfinal }
  transition_fun := newtransition_fun M
  transition_fun' := newtransition_fun' M
  finite := by
    intros q a Z
    simp[newtransition_fun]
    match q with
     | newinit => simp
     | (oldstate p) => simp; match Z with
        | newstart => simp
        | (oldsymbol Y) =>
          simp
          sorry -- TODO: need (essentially): image of finite set is finite
      | newfinal => simp
  finite' := by
    intros q Z
    simp[newtransition_fun']
    match q with
      | newinit => simp ; match Z with
        | newstart => simp
        | (oldsymbol Y) => simp
      | (oldstate p) => simp; match Z with
        | newstart => simp
        | (oldsymbol Y) =>
          simp
          sorry -- TODO: need (essentially): image of finite set is finite
      | newfinal => simp
}

-- coercion for configurations
instance {M : PDA Q T S} : Coe (conf M) (conf (estack_to_fstate M)) where
  coe r := ⟨r.state, r.input, r.stack⟩

theorem inject_transition_fun' (M : PDA Q T S) (p q : Q) (Z : S) (β : List S)
  ( h: (p,β) ∈ (M.transition_fun' q Z) ) :
  ((p,β): (add_init_final Q × List (add_start_symbol S))) ∈ ((estack_to_fstate M).transition_fun' q Z) := by
  unfold estack_to_fstate newtransition_fun'
  simp
  use p
  use β

theorem inject_transition_fun (M : PDA Q T S) (p q : Q) (a : T) (Z : S) (β : List S)
  ( h: (p,β) ∈ (M.transition_fun q a Z) ) :
  ((p,β): (add_init_final Q × List (add_start_symbol S))) ∈ ((estack_to_fstate M).transition_fun q a Z) := by
  unfold estack_to_fstate newtransition_fun
  simp
  use p
  use β

theorem inject_step (M : PDA Q T S) (r s : M.conf) (h: s ∈ (step r)) :
  (s : conf (estack_to_fstate M)) ∈ (step (r : conf (estack_to_fstate M))) := by
  unfold step at h
  match r with
    | ⟨q, a::w, Z::α⟩ =>
      simp at h
      rcases h with h | h
      · rcases h with ⟨p,β,h₁,h₂⟩
        simp
        unfold step
        simp
        left
        use p
        use β
        simp
        rw[h₂]
        simp
        apply inject_transition_fun
        exact h₁
      · rcases h with ⟨p,β,h₁,h₂⟩
        simp
        unfold step
        simp
        right
        use p
        use β
        simp
        rw[h₂]
        simp
        apply inject_transition_fun'
        exact h₁
    | ⟨q, [], Z::α⟩ =>
      simp at h
      rcases h with ⟨p, β, h₁, h₂⟩
      simp
      unfold step
      simp
      use p
      use β
      simp
      rw[h₂]
      simp
      apply inject_transition_fun'
      exact h₁
    | ⟨q, w, []⟩ =>
      simp at h
      simp
      unfold step
      simp
      rw[h]
      simp

theorem inject_reaches₁ (M : PDA Q T S) (r₁ r₂: M.conf) (h: M.Reaches₁ r₁ r₂) :
  ((estack_to_fstate M).Reaches₁ r₁ r₂) := by
  unfold Reaches₁ at *
  apply inject_step
  exact h

theorem inject_reaches (M: PDA Q T S) (r₁ r₂: M.conf) (h: M.Reaches r₁ r₂) :
 ((estack_to_fstate M).Reaches r₁ r₂) := by
  apply Relation.ReflTransGen.lift _ _ h
  intro a b h
  apply inject_reaches₁
  exact h

theorem map_estackpath_to_fstatepath (M : PDA Q T S) (w: List T) (q : Q)
  (hr: M.Reaches ⟨M.initial_state,w,[M.start_symbol]⟩ ⟨q,[],[]⟩) :
  (estack_to_fstate M).Reaches ⟨newinit,w,[newstart]⟩ ⟨newfinal,[],[]⟩ := by
  have initstep: (estack_to_fstate M).Reaches ⟨newinit,w,[newstart]⟩
    ⟨(M.initial_state),w,[M.start_symbol,newstart]⟩ := by
    clear hr
    unfold Reaches
    apply Relation.ReflTransGen.single
    apply reaches1_of_transition_fun _ _ _ _ _ [oldsymbol M.start_symbol,newstart]
    simp[transition_fun',newtransition_fun']
  have injpath: (estack_to_fstate M).Reaches
    ⟨(oldstate M.initial_state),w,[oldsymbol M.start_symbol] ++ [newstart]⟩
    ⟨oldstate q,[],[] ++ [newstart]⟩ := by
    apply Reaches.append_stack
    apply inject_reaches at hr
    exact hr
  have finalstep: (estack_to_fstate M).Reaches ⟨oldstate q,[],[newstart]⟩ ⟨newfinal,[],[]⟩ := by
    unfold Reaches
    apply Relation.ReflTransGen.single
    unfold Reaches₁
    unfold step
    simp[newtransition_fun']
  apply Relation.ReflTransGen.trans initstep (Relation.ReflTransGen.trans injpath finalstep)

theorem map_fstatepath_to_estackpath (M : PDA Q T S) (w: List T) (γ: List (add_start_symbol S))
  (hr: (estack_to_fstate M).Reaches ⟨newinit,w,[newstart]⟩ ⟨newfinal,[],γ⟩):
  ∃ q, M.Reaches ⟨M.initial_state,w,[M.start_symbol]⟩ ⟨q,[],[]⟩ := by
  sorry

-- main theorem
theorem fstate_of_estack (M : PDA Q T S):
  M.acceptsByEmptyStack = (estack_to_fstate M).acceptsByFinalState := by
  ext w
  constructor
  · intro h -- left-to-right inclusion
    dsimp[acceptsByEmptyStack] at h
    rw[Set.mem_setOf] at h
    rcases h with ⟨ q, h ⟩
    dsimp[acceptsByFinalState]
    rw[Set.mem_setOf]
    use newfinal
    refine And.symm ⟨?h.left, rfl⟩
    use []
    apply map_estackpath_to_fstatepath M w q
    exact h
  · intro h -- right-to-left inclusion
    dsimp [acceptsByFinalState] at h
    rw[Set.mem_setOf] at h
    rcases h with ⟨ q, qfin, γ, h ⟩
    rw[Set.mem_singleton_iff] at qfin
    rw[qfin] at h
    dsimp[acceptsByEmptyStack]
    rw[Set.mem_setOf]
    apply map_fstatepath_to_estackpath M w γ
    exact h
