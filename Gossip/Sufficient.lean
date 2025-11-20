import Mathlib.Data.List.Indexes

import Gossip.Basic

/-! # Sufficient

We show that for n ≥ 4 agents there is a call sequence of length 2n - 4
that makes each agent learn the secrets of all others (become an expert).

Authors: Timo Doherty, Malvin Gattinger
-/

/-- We can replace addAgent with initialState (n + 1) in the following lemma n ≥ 4. -/
lemma addAgentEqualsSucc {n : ℕ} :
    addAgent (initialState n) = (initialState (Nat.succ n)) := by
  funext x y
  simp only [addAgent, Nat.succ_eq_add_one, beq_iff_eq, Bool.false_eq_true, eq_iff_iff]
  cases x using Fin.lastCases <;> cases y using Fin.lastCases  <;> simp [initialState]
  next k =>
    rcases k with ⟨k, k_lt⟩
    unfold Fin.last
    simp
    omega

/-- addAgent (initialState n) is replacable with initialState (n + 1) in the following lemma. -/
lemma singleMakeCalls {n : Nat} (initial_call : Call (n + 1)) (expandedSeq : List (Call (n + 1))) :
  makeCall (makeCalls (makeCall (addAgent (initialState n)) initial_call) expandedSeq) initial_call =
  makeCalls (initialState (n + 1)) ([initial_call] ++ expandedSeq ++ [initial_call]) := by
  rw [← makeCalls_cons, addAgentEqualsSucc, makeCalls_snoc]
  simp_all only [List.singleton_append]

/-- addAgent and makeCall commute if the call doesn't contain the new agent. -/
lemma addAgentMakeCallCommute {n : Nat} (c : Call n) (someState : GossipState n):
      makeCall (addAgent someState) c
    = addAgent (makeCall someState c) := by
  funext x y
  rcases c with ⟨a,b⟩
  simp only [makeCall, Nat.succ_eq_add_one, eq_iff_iff]
  by_cases x = a.castSucc <;> by_cases x = b.castSucc <;>
    cases y using Fin.lastCases <;> cases x using Fin.lastCases
  all_goals
    simp_all [addAgent, makeCall]

/-- addAgent and makeCalls commute if the call sequence doesn't contain the new agent. -/
lemma addAgentMakeCallsCommute {n : Nat} (σ : List (Call n)) (someState : GossipState n):
      makeCalls (addAgent someState) σ
    = addAgent (makeCalls someState σ) := by
  induction σ generalizing someState
  case nil =>
    simp_all [makeCalls]
  case cons c σ IH =>
    rcases c with ⟨a,b⟩
    specialize IH (makeCall someState (a, b))
    simp_all [makeCalls]
    rw [← IH]
    clear IH
    have equiv : makeCall (addAgent someState) (Fin.castSucc a, Fin.castSucc b) = addAgent (makeCall someState (a, b)) :=
      addAgentMakeCallCommute (a,b) _ -- Uses the lemma for a single call.
    rw [equiv]

/-- Given that only a knows a and b, then we can show that all agents that learn a also learn b. -/
lemma twoSecretsSuccSingle {n : Nat} (s : GossipState (Nat.succ (n + 4))) (a b : Fin (Nat.succ (n + 4))) (seq : List (Call (Nat.succ (n + 4))))
  (a_def : a = 0)
  (b_def : b = Fin.last (n + 4))
  (only_ab_know_ab : ∀ (i : Fin (Nat.succ (n + 4))), (i ≠ a ∧ i ≠ b) → ¬ s i a ∧ ¬ s i b)
  (a_knows_b : s a b)
  (b_knows_a : s b a)
  (fin_succ_knows_own : s b b)
  :
  (∀ k, (makeCalls s seq) k a → (makeCalls s seq) k b) := by
  induction seq using List.reverseRecOn
  case nil =>
    intro k k_knows_a
    subst_eqs
    simp only [makeCalls, Nat.succ_eq_add_one, List.foldl_nil, ne_eq, and_imp] at *
    cases em (k = 0) <;> cases em (k = Fin.last (n+4))
    all_goals
      simp_all
  case append_singleton seq theCall IH =>
    simp only [Nat.succ_eq_add_one, ne_eq, and_imp, makeCalls, List.foldl_append, List.foldl_cons,
      List.foldl_nil, makeCall] at *
    aesop

/-- Given that only agent a knows a and b, and some sequence makes everyone else learn a, then everyone else also learns b. -/
lemma twoSecretsSucc {n : Nat} (s : GossipState (Nat.succ (n + 4))) (a b : Fin (Nat.succ (n + 4))) (seq : List (Call (Nat.succ (n + 4))))
  (a_def : a = 0)
  (b_def : b = Fin.last (n + 4))
  (only_ab_know_ab : ∀ (i : Fin (Nat.succ (n + 4))), (i ≠ a ∧ i ≠ b) → ¬ s i a ∧ ¬ s i b)
  (a_knows_b : s a b)
  (b_knows_a : s b a)
  (all_learn_a : ∀ j, (makeCalls s seq) j a)
  (fin_succ_knows_own : s b b)
  :
  (∀ k, (makeCalls s seq) k b) := by
  intro k
  apply twoSecretsSuccSingle s a b seq a_def b_def only_ab_know_ab a_knows_b b_knows_a fin_succ_knows_own
  apply all_learn_a

/-- Definitions to avoid repetition. -/
def zero_fin : (Fin (Nat.succ (n + 4))) := 0
def succ_fin : (Fin (Nat.succ (n + 4))) := Fin.last (n + 4)
def initial_call : Call (Nat.succ (k + 4)) := (zero_fin, succ_fin)

/-- The first agent learns all old secrets. -/
lemma lemma_1 {k : Nat} (seq : List (Call (k + 4))) (IH : allExpert (makeCalls (initialState (k + 4)) seq)) :
    ∀ i : Fin (Nat.succ (k + 4)), i ≠ Fin.last (k + 4) →
      makeCalls (makeCall (addAgent (initialState (k + 4))) (zero_fin, succ_fin)) seq zero_fin i := by
  unfold allExpert at IH
  let expandedSeq := (seq : List (Call (Nat.succ (k + 4))))
  let new_state := makeCall (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) seq) initial_call
  let calls_without_final_call := [initial_call] ++ expandedSeq
  let temp_state := makeCalls (addAgent (initialState (k + 4))) calls_without_final_call

  have single_calls : new_state = makeCalls (initialState (Nat.succ (k + 4))) ([initial_call] ++ expandedSeq ++ [initial_call]) := by
    simp [new_state]
    apply singleMakeCalls

  have h : ∀ i, i ≠ succ_fin → makeCalls (addAgent (initialState (k + 4))) seq zero_fin i := by
    simp_all only [isExpert]
    simp only [Nat.succ_eq_add_one, succ_fin, ne_eq, List.pure_def, List.bind_eq_flatMap]
    apply Fin.lastCases
    · intro a
      simp_all only [Nat.succ_eq_add_one, List.cons_append, List.nil_append, not_true_eq_false]
    · intro i _
      simp_all only [Nat.succ_eq_add_one, new_state, expandedSeq]
      have h' : isExpert (makeCalls (initialState (k + 4)) seq) 0 := by
        apply IH
      rw [addAgentExpertOld] at h'
      have replacement := addAgentMakeCallsCommute seq
      aesop

  -- New_state contains more gossip than temp_state.
  have h' : moreGossip (makeCalls (addAgent (initialState (k + 4))) expandedSeq) temp_state := by
    simp [temp_state, calls_without_final_call, expandedSeq]
    rw [addAgentEqualsSucc, makeCalls_cons]
    apply makeCallsIncreasesGossip
    unfold moreGossip
    intro a b
    apply makeCallMakesGossip

  intro i a
  simp_all only [ne_eq, new_state, initial_call, zero_fin, succ_fin, expandedSeq]
  apply h'
  aesop

/-- Shows that the first agent learns the new agent's secret. -/
lemma lemma_2 {k : Nat} (seq : List (Call (k + 4))) :
  (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) seq) zero_fin succ_fin := by
  let new_state := makeCall (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) seq) initial_call
  have l : moreGossip (makeCall (addAgent (initialState (k + 4))) initial_call) (makeCalls ((makeCall (addAgent (initialState (k + 4))) initial_call)) seq) := by
    apply callsIncreaseGossip
  apply l
  simp [initial_call, makeCall, addAgent, initialState, succ_fin]

/-- Combining lemma_1 and lemma_2 to show that the first agent is an expert. -/
lemma lemma_3 {k : Nat} (seq : List (Call (k + 4))) (IH : allExpert (makeCalls (initialState (k + 4)) seq)) :
  isExpert (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) seq) zero_fin := by
  unfold isExpert
  let calls_without_final_call := [initial_call] ++ (seq : List (Call (k + 4).succ))
  let temp_state := makeCalls (addAgent (initialState (k + 4))) calls_without_final_call
  intro j
  have h1 : j ≠ succ_fin → temp_state zero_fin j := by
    exact lemma_1 seq IH j
  have h2 : j = succ_fin → temp_state zero_fin j := by
    intro h
    rw [h]
    exact lemma_2 seq
  by_cases (j = succ_fin) <;> aesop

/-- Main lemma for the inductive step. -/
lemma inductiveCase (k : Nat) (seq : List (Call (k + 4))) :
    allExpert (makeCalls (initialState (k + 4)) seq) →
    ∃ seq', seq'.length = 2 + seq.length ∧ allExpert (makeCalls (initialState (Nat.succ k + 4)) seq') := by
  intro IH
  let expandedSeq := (seq : List (Call (k + 4).succ))
  let zero_fin : Fin (Nat.succ (k + 4)) := 0
  let succ_fin : Fin (Nat.succ (k + 4)) := Fin.last (k + 4)
  let initial_call : Call (Nat.succ (k + 4)) := (0, succ_fin)
  let new_state := makeCall (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) expandedSeq) initial_call
  let calls_without_final_call := [initial_call] ++ expandedSeq
  let temp_state := makeCalls (addAgent (initialState (k + 4))) calls_without_final_call

  -- We can rewrite new_state so it contains a single call sequence.
  have single_calls : new_state = makeCalls (initialState (Nat.succ (k + 4))) ([initial_call] ++ expandedSeq ++ [initial_call]) := by
    simp [new_state]
    apply singleMakeCalls

  -- Putting milestone_1 and milestone_2 together, we get that all but the last agents are experts
  have milestone_4 : ∀ i, i ≠ succ_fin → isExpert new_state i := by
    -- The goal is true for temp_state.
    have subgoal_1 : ∀ i, i ≠ succ_fin → ∀ j, temp_state i j := by
      intro i h
      simp [temp_state, calls_without_final_call, expandedSeq]
      simp [allExpert] at IH

      -- All old agents know all old secrets in temp_state.
      have oldLearnOld : ∀ (j : Fin (k + 4)), (makeCalls (addAgent (initialState (k + 4))) (initial_call :: seq)) i (Fin.castSucc j) := by

        -- Its true for this state.
        have weaker_state : ∀ (j : Fin (k + 4)), makeCalls (addAgent (initialState (k + 4))) seq i j.castSucc := by

          -- For all fin (k + 4), they know all but the last secret.
          have know_all_but_last : ∀ (i : Fin (k + 4)), ∀ (j : Fin (k + 4)), makeCalls (addAgent (initialState (k + 4))) seq i.castSucc j.castSucc := by
            intro i j
            rw [addAgentMakeCallsCommute]
            simp [addAgent]
            aesop

          -- Turn the type into Fin (Nat.succ (k + 4)) with i ≠ Fin.last (k + 4).
          have type_cast : ∀ (i : Fin (Nat.succ (k + 4))), i ≠ Fin.last (k + 4) → ∀ (j : Fin (k + 4)), makeCalls (addAgent (initialState (k + 4))) seq i j.castSucc := by
            intro i i_neq_last
            cases i using Fin.lastCases
            case last => exfalso; tauto
            case cast i => exact fun j => know_all_but_last i j
          aesop

        -- This state is stronger.
        have stronger_state : moreGossip (makeCalls (addAgent (initialState (k + 4))) seq) (makeCalls (addAgent (initialState (k + 4))) (initial_call :: seq)) := by
          apply makeCallsIncreasesGossip
          apply makeCallMakesGossip

        aesop

      -- All i learn the secret of the new agent as well.
      have oldLearnNew : makeCalls (addAgent (initialState (k + 4))) (initial_call :: seq) i succ_fin := by
        -- prepare for the lemma.
        have agent_0_knows_both : temp_state zero_fin succ_fin ∧ temp_state zero_fin zero_fin := by
          constructor
          · apply lemma_3 seq IH
          · apply lemma_3 seq IH

        cases i using Fin.lastCases
        case last => exfalso; tauto
        case cast i =>
          -- All agents get to learn the new agent's secret.
          apply twoSecretsSucc _ _ succ_fin seq (by aesop) (by unfold succ_fin; rfl)
          case only_ab_know_ab =>
            intro i ⟨h1,h2⟩
            constructor
            · cases i using Fin.lastCases
              case last =>
                simp_all [makeCall, addAgent, initial_call, initialState, zero_fin, Fin.lastCases]
              case cast i =>
                simp only [makeCall, Nat.succ_eq_add_one, h1, ↓reduceIte, h2, addAgent, beq_iff_eq,
                  Fin.zero_eq_last_iff, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false,
                  Bool.false_eq_true, Fin.lastCases_castSucc, initial_call]
                have : (0 : Fin (k + 4).succ) = Fin.castSucc 0 := by rfl
                rw [this]
                -- the trick here is to *not* simp with `Fin.castSucc_zero`.
                rw [Fin.lastCases_castSucc]
                unfold initialState
                simp at h1
                exact h1
            · cases i using Fin.lastCases
              case last =>
                aesop
              case cast i =>
                simp [initial_call, makeCall, addAgent, initialState]
                aesop
          case a_knows_b =>
            simp [makeCall]
            right
            simp [addAgent, initialState]
            aesop
          case b_knows_a =>
            simp only [makeCall, Nat.succ_eq_add_one, Fin.last_eq_zero_iff, Nat.add_eq_zero_iff,
              OfNat.ofNat_ne_zero, and_false, ↓reduceIte, addAgent, beq_iff_eq,
              Fin.zero_eq_last_iff, Bool.false_eq_true, initialState, Fin.lastCases_last, false_or,
              succ_fin, initial_call]
            change Fin.lastCases False _ (Fin.castSucc 0)
            rw [Fin.lastCases_castSucc]
            change Fin.lastCases False _ (Fin.castSucc 0)
            rw [Fin.lastCases_castSucc]
          case all_learn_a =>
            have old_agents_learn_a : ∀ (j : Fin (k + 4)), makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) seq j.castSucc zero_fin := by
              intro j
              have know_all_but_last : ∀ (i : Fin (k + 4)), ∀ (j : Fin (k + 4)), makeCalls (addAgent (initialState (k + 4))) seq i.castSucc j.castSucc := by
                intro i j
                rw [addAgentMakeCallsCommute]
                simp_all only [Nat.succ_eq_add_one, List.cons_append, List.nil_append, ne_eq,
                  addAgent, beq_iff_eq, Bool.false_eq_true, Fin.lastCases_castSucc]
                apply IH
              have weaker : moreGossip (makeCalls (addAgent (initialState (k + 4))) seq)
                            (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) seq) := by
                apply makeCallsIncreasesGossip
                apply makeCallMakesGossip
              apply weaker; clear weaker
              convert know_all_but_last j 0
            have new_agent_learns_a : makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) seq succ_fin zero_fin := by
              have weaker : moreGossip
                (makeCall (addAgent (initialState (k + 4))) initial_call)
                (makeCalls (makeCall (addAgent (initialState (k + 4))) initial_call) seq)
                  := by apply callsIncreaseGossip
              apply weaker
              unfold initial_call
              simp only [makeCall, addAgent, initialState]
              rw [if_neg]
              · simp_all [succ_fin, zero_fin]
                change Fin.lastCases False _ (Fin.castSucc 0)
                rw [Fin.lastCases_castSucc]
                change Fin.lastCases False _ (Fin.castSucc 0)
                rw [Fin.lastCases_castSucc]
              · have less : 1 < Fin.last (k + 4) := by
                  apply Fin.one_lt_last
                aesop

            intro j
            cases j using Fin.lastCases
            case last => exact new_agent_learns_a
            case cast j =>
              rw [makeCalls_cons] at oldLearnOld
              exact old_agents_learn_a j

          rcases initial_call with ⟨a,b⟩ -- agents in call
          simp only [makeCall, Nat.succ_eq_add_one, addAgent, beq_iff_eq, Bool.false_eq_true]
          split <;> aesop

      -- Putting them together in the right format.
      have final : ∀ (j : Fin (Nat.succ (k + 4))), temp_state i j := by
        apply Fin.lastCases <;> aesop
      aesop

    simp [new_state, isExpert]

    -- The goal is true for temp_state, which is weaker than new_state, so it's true for new_state.
    have subgoal_2 : moreGossip temp_state new_state := by
      simp [temp_state, new_state, calls_without_final_call, expandedSeq]
      apply makeCallMakesGossip

    intro i a j
    simp_all only [ne_eq, new_state]
    apply subgoal_2
    simp_all only [not_false_eq_true]

  -- HERE we choose the new sequence:
  use [initial_call] ++ expandedSeq ++ [initial_call]
  constructor
  · simp [expandedSeq]
    omega
  · -- milestone_5
    -- putting milestone_3 and milestone_4 together, we get that everyone is an expert.
    have new_becomes_expert : isExpert new_state succ_fin := by

      have state_equiv : new_state = makeCall temp_state initial_call := by
        rw [single_calls]
        simp [temp_state, calls_without_final_call, expandedSeq]
        repeat rw [makeCalls_cons]
        rw [makeCalls_snoc, addAgentEqualsSucc]

      rw [state_equiv]
      apply expertMakesExpert
      apply lemma_3
      simp_all
    intro i
    by_cases h : (i = succ_fin)
    · convert new_becomes_expert; simp_all
    · convert milestone_4 i h; simp_all

/-- Main theorem: for n ≥ 4 agents there exists a sequence of calls that makes everyone an expert. -/
theorem sufficiency (n : Nat) : (n ≥ 4) → ∃ (seq : List (Call n)), seq.length = (2 * n - 4) ∧ allExpert (makeCalls (initialState n) seq) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | 2 => by simp
  | 3 => by simp
  | (m + 4) =>  by -- we perform induction on m = n - 4 so the base case is m = 0, i.e. n = 4
                intro h
                induction m
                case zero =>
                  simp at h
                  exists [(0, 1), (2, 3), (0, 2), (1, 3)]
                case succ k IH =>
                  simp at IH
                  rcases IH with ⟨seq, claim⟩
                  have length : seq.length = 2 * (k + 4) - 4 := by
                    exact claim.left
                  have add_two_still_2nmin4 : 2 + seq.length = 2 * (Nat.succ (k + 4)) - 4 := by
                    rw [length]
                    simp_all only [Nat.succ_add, ge_iff_le, true_and, zero_add]
                    apply Eq.refl
                  rw [← add_two_still_2nmin4]
                  exact inductiveCase k seq claim.right
