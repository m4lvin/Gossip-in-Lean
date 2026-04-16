import Gossip.Error.SemProp

namespace Error

open Form

/-- If `a` is in `C` and has neither value of `b` after call `C`,
then before the call they also cannot have had the real value. -/
lemma involved_not_have_before_of_not_have_after {n : ℕ} {b : @Agent n} {S : @Dist n} {k : Bool}
    (is_k : S b = k) (C : Call) (σ : List Call) (a : Agent) (o : maxOne (C :: σ))
    (r_in : roleOfIn a C ≠ Role.Other)
    (a_has_no_k : (b, k) ∉ S⌈⟨C :: σ, o⟩⌉a)
    (a_has_no_not_k : (b, !k) ∉ S⌈⟨C :: σ, o⟩⌉a)
    : (b, k) ∉ S⌈⟨σ, ⁻o⟩⌉a := by
  intro suppose
  absurd a_has_no_k; clear a_has_no_k
  unfold resultSet
  cases r_def : roleOfIn a C
  case Other =>
    exfalso
    grind
  all_goals
    let copyC := C
    cases C
    case normal callee => -- works :)
      simp_all [Call.pair]
      subst_eqs
      constructor
      · intro hyp
        have := true_of_knowldege hyp
        simp at this
      · refine ⟨S, ⟨σ,o⟩, ⟨rfl, equiv_refl⟩, ⟨copyC, ?_⟩⟩
        simp [o, copyC]
    case fstE callee => -- copy-pasta but broken??
      rcases callee with ⟨callee, callee_neq_callee⟩
      simp_all [Call.pair]
      subst_eqs
      simp [roleOfIn]
      constructor
      · intro hyp
        have := true_of_knowldege hyp
        simp at this
      · refine ⟨S, ⟨σ,⁻o⟩, ⟨rfl, equiv_refl⟩, ⟨copyC, ?_⟩⟩
        simp_all [copyC]
    case sndE callee _ => -- copy-pasta but broken??
      rcases callee with ⟨callee, callee_neq_callee⟩
      simp_all [Call.pair]
      subst_eqs
      simp [roleOfIn]
      constructor
      · intro hyp
        have := true_of_knowldege hyp
        simp at this
      · refine ⟨S, ⟨σ,⁻o⟩, ⟨rfl, equiv_refl⟩, ⟨copyC, ?_⟩⟩
        simp_all [copyC]

/-- New Lemma 2 -/
lemma two {n : Nat} (a b : @Agent n) {S : @Dist n} {σ : @OSequence n}
    {k : Bool} (is_k : S b = k)
    (a_has_no_k : (b, k) ∉ S⌈σ⌉a)
    : equiv a (S, ⟨σ, rfl⟩) (S.switch b, ⟨σ, rfl⟩) := by
  rcases σ with ⟨σ, o⟩
  induction σ generalizing a -- need IH for other agents
  case nil =>
    cases b
    simp_all [Dist.switch]
    grind
  case cons C σ IH =>
    have b_neq_a : b ≠ a := by
      have := @stubbornness n S b k _ ⟨_,o⟩ rfl; grind [eval]
    cases r_def : roleOfIn a C
    case Caller =>
      simp [equiv, r_def]
      -- cases a has_no_k into disjunctions?
      by_cases disj : (b, !k) ∈ S⌈⟨_,o⟩⌉a
      rotate_left -- to match the order in the paper
      · -- (*) "then already"
        have a_has_no_before : (b, k) ∉ S⌈⟨σ, ⁻o⟩⌉a :=
          involved_not_have_before_of_not_have_after is_k C σ _ o (by grind) a_has_no_k disj
        have but_how_do_we_get_that_too : (b, k) ∉ S⌈⟨σ, ⁻o⟩⌉(C.pair.2) := by
          -- From here on we are unsure.
          -- Maybe we still need a different Lemma than "involved_not_have_before_of_not_have_after" here.
          apply @involved_not_have_before_of_not_have_after n b S k is_k C σ C.pair.2 o (by simp)
          -- Maybe add extra lemmas for this.
          · sorry
          · sorry
        have by_IH_a := IH a (⁻o) a_has_no_before
        have by_IH_callee := IH (C.pair.2) (⁻o) but_how_do_we_get_that_too
        refine ⟨by_IH_a, ?_⟩
        apply @callee_contribSet_eq_of_resultSet_eq n C.pair.2 C S _ _ _ _
        · unfold roleOfIn Call.pair; grind
        apply indistinguishable_then_same_values -- Lemma 7
        exact equi_of_equiv by_IH_callee
      · -- (**) "there are more subcases to consider"
        -- What really are the three(?) subcases here?
        -- by_cases (b, !k) ∈ S⌈⟨C::σ,o⟩⌉C.pair.2  -- Not sure if this is ther right case split.
        sorry
    case Callee =>
      -- This is probably analogous.
      -- Only work on this when the Caller case is fully done and sorry-free.
      sorry
    case Other => -- easy :-)
      simp [equiv, r_def]
      unfold resultSet at a_has_no_k
      simp [r_def] at a_has_no_k
      apply @IH a (⁻o) a_has_no_k

-- Maybe rename this later ;-)
lemma caller_the_hard_case {a b : @Agent n} {k} S C σ
    (o : maxOne (C :: σ))
    (knows : S⌈⟨C :: σ, o⟩⌉ ⊧ K a ((b, k)@b))
    (ra : roleOfIn a C = .Caller)
    (not_know_before : ¬ S⌈⟨σ,⁻o⟩⌉ ⊧ K a ((b, k)@b))
    : S⌈⟨C :: σ, o⟩⌉ ⊧ (b, k)@a := by
  have is_k := true_of_knowldege knows
  simp only [OSequence.length_def, List.length_cons, stubbornness] at is_k
  cases C
  case normal _a c =>
    simp at ra; subst ra
    by_cases ha : (b, k) ∈ S⌈⟨σ,⁻o⟩⌉a <;> by_cases hc : (b, k) ∈ S⌈⟨σ,⁻o⟩⌉c
    · simp_all [eval,resultSet]
      constructor
      · refine ⟨S, ⟨⟨σ,⁻o⟩, by simp ⟩, knows _ ⟨_,o⟩ (by simp) equiv_refl⟩
      · refine ⟨S, ⟨σ,⁻o⟩, ⟨⟨rfl, equiv_refl⟩, ⌜a c⌝, by simp, rfl, rfl, o, ?_⟩⟩
        apply knows S ⟨_, o⟩ (by simp) equiv_refl
    · simp_all [eval,resultSet]
      constructor
      · refine ⟨S, ⟨⟨σ,⁻o⟩, by simp ⟩, knows _ ⟨_,o⟩ (by simp) equiv_refl⟩
      · refine ⟨S, ⟨σ,⁻o⟩, ⟨⟨rfl, equiv_refl⟩, ⌜a c⌝, by simp, rfl, rfl, o, ?_⟩⟩
        apply knows S ⟨_, o⟩ (by simp) equiv_refl
    · simp_all [eval,resultSet]
      constructor
      · refine ⟨S, ⟨⟨σ,⁻o⟩, by simp ⟩, knows _ ⟨_,o⟩ (by simp) equiv_refl⟩
      · refine ⟨S, ⟨σ,⁻o⟩, ⟨⟨rfl, equiv_refl⟩, ⌜a c⌝, by simp, rfl, rfl, o, ?_⟩⟩
        apply knows S ⟨_, o⟩ (by simp) equiv_refl
    · simp_all [eval,resultSet]
      -- "We therefore only have the following *four* remaining cases ..."
      have claim : (b, k) ∉ S⌈⟨⌜a c⌝ :: σ, o⟩⌉a := by unfold resultSet; grind
      have byLemma := @two n a b S ⟨⌜a c⌝ :: σ, o⟩ _ is_k claim -- using new Lemma 2 here
      absurd knows
      simp
      exact ⟨S.switch b, ⟨⟨⌜a c⌝ :: σ, o⟩, by simp, byLemma⟩ , by simpa [Dist.switch]⟩

  case fstE =>
    -- unsure how analogous this will be.
    sorry
  case sndE =>
    -- unsure how analogous this will be.
    sorry

/-- Proposition 12.
Again the parts (i) and (ii) are given by different `k` values. -/
lemma knowledge_implies_correct_belief {n} {a b : @Agent n} {k} :
  ⊨ (K a ((b,k) @ b)) ⟹ ( ((b,k) @ b) ⋀ ((b,k) @ a) ⋀ ( ¬' (b, !k) @ a) ) := by
  intro S σ
  rw [eval_impl]
  intro knows
  rcases σ with ⟨σ,o⟩
  induction σ -- TODO: `cases` induction on length, not specific sequence?
  case nil =>
    simp [eval]
    have := true_of_knowldege knows
    by_cases b = a
    · simp_all [eval]
    · exfalso
      simp_all [eval]
      have := knows S ⟨[], by simp [maxOne]⟩ (by simp)
      have := knows (S.switch b) ⟨[], by simp [maxOne]⟩ (by simp) (by simp [Dist.switch]; grind)
      simp_all [Dist.switch]
  case cons C σ IH =>
    cases ra : roleOfIn a C -- "For σ = τ.bcᴷ we distnguish ..."
    case Other => -- "where b,c ≠ a"
      have := @not_in_call_then_invariant_k _ k _ _ ra b S σ o
      specialize IH (⁻o) (this.mp knows) -- induction
      simp_all [eval, not_in_call_then_invariant_resultSet ra S σ o]
    case Caller => -- "assume S,σ.ac^κ ⊨ Kₐ b_b" (`knows`)
      rw [eval_con, eval_con]
      -- "We distinguish two subcases."
      by_cases h : eval S ⟨σ,⁻o⟩ (K a ((b,k) @ b))
      · -- "If S, σ |= Ka b b, by induction we can conclude that S, σ |= ...":
        specialize IH (⁻o) h
        rw [eval_con, eval_con] at IH
        -- "Again from stubbornness and again from the call semantics, ..."
        refine ⟨by simp_all, ?_, ?_⟩
        · exact caller_keeps_known_value C ra S σ o h IH.2.1
        · exact caller_rejects_opposite_of_known_value C ra S σ o h
      · -- If S, σ |= ¬Kabb, this is the harder case, and the case of most interest in the proof.
        -- clear IH -- here we do not use it? BUT WE SHOULD!
        -- "We show the three conjuncts separately, where the (hardest) second comes last.""
        refine ⟨?one, ?two, ?three⟩
        case one => exact true_of_knowldege knows
        case three => exact caller_rejects_opposite_of_afterwards_known_value C ra S σ o knows
        case two => exact caller_the_hard_case S C σ o knows ra h
    case Callee =>
      -- Analogous, but will need `callee_...` lemmas instead of `caller_...`.
      -- Only work on this sorry *after* the "Caller" case is sorry-free and
      -- also the lemma caller_the_hard_case is fully done.
      sorry

/-- Corollary 13. -/
lemma knowledge_is_justified_true_belief {n} {a b : @Agent n} :
    ⊨ K a ((b,k) @ b) ⇔ K a ( ((b,k) @ b) ⋀ ((b,k) @ a) ⋀ ( ¬' (b, !k) @ a) ) := by
  intro S σ
  rw [eval_biimpl]
  constructor
  · -- left to right: "apart from Proposition 13, use Lemma 8."
    intro lhs
    rw [eval]
    intro T τ samel_ln
    have fromProp13 := @knowledge_implies_correct_belief _ a b k T τ
    rw [eval_impl] at fromProp13
    apply fromProp13
    exact (equiv_then_know_same samel_ln ((b, k)@b)).mp lhs -- using, not Lemma 8 here!
  · -- "right to left is obvious"
    grind [eval]
