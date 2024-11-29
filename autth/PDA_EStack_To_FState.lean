import autth.PDA

open PDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

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

-- Stefan: this is awful, what is a better way to do this?
def oldinject1 ( q : Q ) : ( add_init_final Q ) := (oldstate q)
def oldinject2 ( Z : S ) : ( add_start_symbol S ) := (oldsymbol Z)
def oldinject3 ( L : (List S) ) : ( List (add_start_symbol S)) := L.map (λ x => oldinject2 x)
def oldinject4 ( out : Q × (List S) ) : ( (add_init_final Q) × (List (add_start_symbol S)))
  := ( (oldinject1 out.1), (oldinject3 out.2) )
def oldinject5 ( out: Set (Q × (List S))) : Set ((add_init_final Q) × (List (add_start_symbol S)))
  := { oldinject4 x | x ∈ out }

--- define new transition function
abbrev newtransition_fun' (M : PDA Q T S) (q : (add_init_final Q)) (Z : (add_start_symbol S)) : Set ((add_init_final Q) × List (add_start_symbol S)) :=
  match q with
    | newinit => match Z with
      | newstart => {((oldstate M.initial_state),[(oldsymbol M.start_symbol),newstart])}
      | (oldsymbol _) => ∅
    | (oldstate p) => match Z with
      | newstart => {(newfinal,[])}
      | (oldsymbol Y) => (oldinject5 (M.transition_fun' p Y))
    | newfinal => ∅

abbrev newtransition_fun (M : PDA Q T S) (q : (add_init_final Q)) (a : T) (Z : (add_start_symbol S)) : Set ((add_init_final Q) × List (add_start_symbol S)) :=
  match q with
    | newinit => ∅
    | (oldstate p) => match Z with
      | newstart => ∅
      | (oldsymbol Y) => (oldinject5 (M.transition_fun p a Y))
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
      | (oldstate p) => match Z with
        | newstart => simp
        | (oldsymbol Y) =>
          simp
          sorry -- TODO: need (oldinject5 (M.transition_fun p a Y)).Finite
      | newfinal => simp
  finite' := by
    intros q Z
    simp[newtransition_fun']
    match q with
      | newinit => match Z with
        | newstart => simp
        | (oldsymbol Y) => simp
      | (oldstate p) => match Z with
        | newstart => simp
        | (oldsymbol Y) =>
          simp
          sorry -- TODO: need: (oldinject5 (M.transition_fun' p Y)).Finite
      | newfinal => simp
}

def oldinject6 (M : PDA Q T S) (r : conf M) : (conf (estack_to_fstate M)) where
  state := oldstate r.state
  input := r.input
  stack := oldinject3 r.stack

theorem inject_reaches₁ (M: PDA Q T S) (r₁ r₂: M.conf) (h: M.Reaches₁ r₁ r₂) :
 ((estack_to_fstate M).Reaches₁ (oldinject6 M r₁) (oldinject6 M r₂)) := by
  unfold oldinject6
  unfold Reaches₁
  sorry

theorem inject_reaches (M: PDA Q T S) (r₁ r₂: M.conf) (h: M.Reaches r₁ r₂) :
 ((estack_to_fstate M).Reaches (oldinject6 M r₁) (oldinject6 M r₂)) := by
  sorry

theorem map_estackpath_to_fstatepath (M : PDA Q T S) (w: List T) (q : Q)
  (hr: M.Reaches ⟨M.initial_state,w,[M.start_symbol]⟩ ⟨q,[],[]⟩):
  ∃ γ, (estack_to_fstate M).Reaches ⟨newinit,w,[newstart]⟩ ⟨newfinal,[],γ⟩ := by
  have initstep: (estack_to_fstate M).Reaches ⟨newinit,w,[newstart]⟩
    ⟨(oldstate M.initial_state),w,[oldsymbol M.start_symbol,newstart]⟩ := by
    sorry
  have injpath: (estack_to_fstate M).Reaches
    ⟨(oldstate M.initial_state),w,[oldsymbol M.start_symbol,newstart]⟩
    ⟨oldstate q,[],[newstart]⟩ := by
    sorry -- use inject_reaches
  have finalstep: (estack_to_fstate M).Reaches ⟨oldstate q,[],[newstart]⟩ ⟨newfinal,[],[]⟩ := by
    sorry
  use []
  apply Relation.ReflTransGen.trans initstep (Relation.ReflTransGen.trans injpath finalstep)

theorem map_fstatepath_to_estackpath (M : PDA Q T S) (w: List T) (γ: List (add_start_symbol S)) (q: Q) (qfin : q ∈ M.final_states)
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
    apply map_fstatepath_to_estackpath M w γ -- Stefan: something weird is going on here... where do goals 1 and 3 come from?
    · sorry
    · exact h
    · sorry
