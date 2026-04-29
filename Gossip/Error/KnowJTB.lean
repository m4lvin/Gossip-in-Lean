import Gossip.Error.SemProp
import Gossip.Error.Cor

namespace Error

/-! # Knowledge is justified true belief -/

/-! ## Helper Lemmas -/

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
    case fstE callee =>
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
    case sndE callee _ =>
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

/-- For errFree sequences, all values in the result set are correct. -/
lemma errFree_resultSet_correct {n} (c : @Agent n) (S : @Dist n)
    (σ : @Sequence n) (o : maxOne σ) (h : errFree σ) (j : Agent) (d : Bool)
    : (mem : (j, d) ∈ resultSet c S ⟨σ, o⟩) → d = S j := by
  induction σ generalizing S c j d
  case nil => simp_all
  case cons k σ ih =>
    cases k <;> simp_all [errFree]
    case normal caller callee =>
      unfold resultSet
      cases h' : roleOfIn c ⌜caller callee⌝ <;> simp_all
      · cases d <;> simp_all <;> grind
      · cases d <;> simp_all <;> grind
      · cases d <;> specialize ih c S (⁻o) j <;> aesop

/-- If σ is errFree and after σ agent c has the real value (j, S j), then for any other initial
distribution T we also have that after σ agent c has the real value (j, T j). -/
lemma errFree_resultSet_dist_independent {n} (c j : @Agent n) (S T : @Dist n)
    (σ : @Sequence n) (o : maxOne σ) (h : errFree σ)
    (mem : (j, S j) ∈ resultSet c S ⟨σ, o⟩)
    : (j, T j) ∈ resultSet c T ⟨σ, o⟩ := by
  revert j
  induction σ generalizing c S T
  case nil => simp_all
  case cons κ σ ih =>
    cases κ <;> simp_all [errFree]
    rename_i k hk
    cases eq_or_ne c k <;> simp_all
    · unfold resultSet; simp
      intro j hj₁ hj₂ x x_1 x_2 hx_3 x_3 hx_4 hx_5 hx_6 hx_7 hx_8
      refine' ⟨ ⟨ _, _ ⟩, _ ⟩
      · grind
      · intro H
        have := true_of_knowldege H
        simp_all
      · refine' ⟨ T, ⟨ σ, Sequence.maxOne_of_errFree h ⟩, ⟨ rfl, equiv_refl ⟩, ?_ ⟩
        aesop
    · intro j hj
      by_cases hc : c = hk.1 <;> simp_all
      · unfold resultSet at hj ⊢; simp_all [ Set.mem_diff, Set.mem_union ]
        refine' ⟨ ⟨ _, _ ⟩, _ ⟩
        · grind
        · intro H
          have := true_of_knowldege H; simp_all
        · refine' ⟨ T, _, _, _ ⟩
          exact ⟨ _, h |> fun h => by simpa using Sequence.maxOne_of_errFree h ⟩
          · exact ⟨ rfl, equiv_refl ⟩
          · use ⌜k hk⌝
            aesop
      · rw [ not_in_call_then_invariant_resultSet ] at hj
        · rw [ not_in_call_then_invariant_resultSet ]
          · exact ih _ _ _ ( by aesop ) _ hj
          · unfold roleOfIn; aesop
        · unfold roleOfIn; aesop

/- For errFree sequences, inverting b in the result set is the same as swtiching the initial
distribution and then executing the same sequence. -/
lemma resultSet_switch_invert_errFree {n : ℕ} (b c : @Agent n) (S : @Dist n)
    (σ : @Sequence n) (o : maxOne σ) (h : errFree σ)
    : invert b (S⌈⟨σ,o⟩⌉c) = (S.switch b)⌈⟨σ,o⟩⌉c := by
  ext ⟨j, d⟩
  constructor <;> intro h_mem
  · rw [ mem_invert_iff ] at h_mem
    have h_correct : (if j = b then (j, !d) else (j, d)).2
                  = S (if j = b then (j, !d) else (j, d)).1 :=
        errFree_resultSet_correct c S σ o h (if j = b then (j, !d) else (j, d)).1
          (if j = b then (j, !d) else (j, d)).2 h_mem
    have h_dist_independent : (j, (S.switch b) j) ∈ (Dist.switch b S)⌈⟨σ, o⟩⌉c := by
      convert errFree_resultSet_dist_independent c j S ( Dist.switch b S ) σ o h _ using 1; grind
    unfold Dist.switch at *
    aesop
  · have h_correct : d = (S.switch b) j :=
      errFree_resultSet_correct c (Dist.switch b S) σ o h j d h_mem
    have h_dist_indep : (j, S j) ∈ resultSet c S ⟨σ, o⟩ := by
      have h_dist_indep : (j, (S.switch b) j) ∈ resultSet c (S.switch b) ⟨σ, o⟩ := by grind
      have := errFree_resultSet_dist_independent c j ( Dist.switch b S ) S σ o h h_dist_indep; aesop
    rw [ mem_invert_iff ]
    unfold Dist.switch at *
    aesop

/-- If `a` is the Caller, `S b = k`, and `(b,k)` is NOT in `a`'s result set after the call,
then `(b,k)` was NOT in `a`'s result set before the call either.
This is because the true value can never be refused or deleted. -/
lemma caller_real_value_not_before {n : ℕ} {b : @Agent n} {S : @Dist n} {k : Bool}
    (is_k : S b = k) (κ : @Call n) (σ : List Call) (a : Agent) (o : maxOne (κ :: σ))
    (ra : roleOfIn a κ = .Caller)
    (a_has_no_k : (b, k) ∉ S⌈⟨κ :: σ, o⟩⌉a)
    : (b, k) ∉ S⌈⟨σ, ⁻o⟩⌉a := by
  contrapose! a_has_no_k
  unfold resultSet
  rcases κ with ( _ | _ | _ ) <;> simp [ * ] at *
  · constructor
    · constructor
      · aesop
      · intro h
        have := true_of_knowldege h
        exact absurd this ( by simp [ is_k ] )
    · refine' ⟨ S, ⟨ σ, _ ⟩, _, _ ⟩ <;> aesop
  · refine' ⟨ ⟨ Or.inl _, _ ⟩, _ ⟩
    · aesop
    · intro h
      have := true_of_knowldege h
      exact absurd this ( by simp [ is_k ] )
    · refine' ⟨ S, ⟨ σ, _ ⟩, _, _ ⟩ <;> norm_num
      exact Sequence.maxOne_of_errFree o
      · rfl
      · aesop
  · constructor
    · refine' ⟨ Or.inl _, _ ⟩
      · aesop
      · intro h; have := true_of_knowldege h; simp_all [ stubbornness ]
    · refine' ⟨ S, ⟨ σ, by aesop ⟩, _, _ ⟩ <;> aesop

/-- Extract callee not having (b,k) from caller not having (b,k) after normal call. -/
lemma callee_real_value_not_in_normal {n : ℕ} {b : @Agent n} {S : @Dist n} {k : Bool}
    (is_k : S b = k) (a : Agent) (c : { b : Agent // b ≠ a }) (σ : List Call) (o : maxOne (⌜a c⌝ :: σ))
    (a_has_no_k : (b, k) ∉ S⌈⟨⌜a c⌝ :: σ, o⟩⌉a)
    : (b, k) ∉ S⌈⟨σ, ⁻o⟩⌉c := by
  contrapose! a_has_no_k
  unfold resultSet
  simp at *
  refine ⟨ ⟨ Or.inr a_has_no_k, ?_ ⟩, ?_ ⟩
  · intro h
    absurd true_of_knowldege h
    simp [is_k]
  · refine' ⟨ S, ⟨ σ, ⁻o ⟩, _, _ ⟩ <;> norm_num; aesop

/-- Extract callee not having (b,k) from caller not having (b,k) after fstE call. -/
lemma callee_real_value_not_in_fstE {n : ℕ} {b : @Agent n} {S : @Dist n} {k : Bool}
    (is_k : S b = k) (a : Agent) (e : Agent) (c : { b : Agent // b ≠ a }) (σ : List Call)
    (o : maxOne (⌜a^e c⌝ :: σ))
    (a_has_no_k : (b, k) ∉ S⌈⟨⌜a^e c⌝ :: σ, o⟩⌉a)
    : (b, k) ∉ S⌈⟨σ, ⁻o⟩⌉c := by
  contrapose! a_has_no_k
  unfold resultSet
  simp +zetaDelta at *
  refine' ⟨ ⟨ Or.inr a_has_no_k, _ ⟩, _ ⟩
  · intro h
    exact absurd ( true_of_knowldege h ) ( by simp [is_k] )
  · aesop

/-- If `a` is the Callee, `S b = k`, and `(b,k)` is NOT in `a`'s result set after the call,
 then `(b,k)` was NOT in `a`'s result set before the call either. -/
lemma callee_real_value_not_before {n : ℕ} {b : @Agent n} {S : @Dist n} {k : Bool}
    (is_k : S b = k) (κ : @Call n) (σ : List Call) (a : Agent) (o : maxOne (κ :: σ))
    (ra : roleOfIn a κ = .Callee)
    (a_has_no_k : (b, k) ∉ S⌈⟨κ :: σ, o⟩⌉a)
    : (b, k) ∉ S⌈⟨σ, ⁻o⟩⌉a := by
      unfold resultSet at a_has_no_k
      contrapose! a_has_no_k
      rcases κ with ( _ | _ | _ ) <;> simp [ * ] at *
      · refine' ⟨ ⟨ Or.inr _, _ ⟩, _ ⟩
        · simp_all
        · intro h; have := true_of_knowldege h; simp_all [ stubbornness ]
        · refine' ⟨ S, ⟨σ, ⁻o⟩, _, _ ⟩ <;> norm_num
          grind +suggestions
      · refine' ⟨ ⟨ Or.inr _, _ ⟩, _ ⟩
        · aesop
        · intro h; have := true_of_knowldege h; simp_all [ stubbornness ]
        · refine' ⟨ S, ⟨ σ, _ ⟩, _, _ ⟩ <;> norm_num [ is_k ] <;> grind +suggestions
      · refine' ⟨ ⟨ Or.inr _, _ ⟩, S, ⟨ σ, by aesop ⟩, _, _ ⟩ <;> norm_num
        · aesop
        · intro h; have := true_of_knowldege h; simp_all [ stubbornness ]
        · grind +suggestions

/-- Extract caller not having (b,k) from callee not having (b,k) after normal call. -/
lemma caller_real_value_not_in_normal {n : ℕ} {b : @Agent n} {S : @Dist n} {k : Bool}
    (is_k : S b = k) (a : Agent) (c : { b : Agent // b ≠ a }) (σ : List Call) (o : maxOne (⌜a c⌝ :: σ))
    (c_has_no_k : (b, k) ∉ S⌈⟨⌜a c⌝ :: σ, o⟩⌉c.1)
    : (b, k) ∉ S⌈⟨σ, ⁻o⟩⌉a := by
      contrapose! c_has_no_k
      simp_all [resultSet]
      constructor
      · intro h; have := Error.true_of_knowldege h; simp_all [ Error.stubbornness ]
      · refine' ⟨S, ⟨σ, ⁻o⟩, _, _⟩ <;> norm_num; use ⌜a c⌝; aesop

/-- Extract caller not having (b,k) from callee not having (b,k) after fstE call with e ≠ b. -/
lemma caller_real_value_not_in_fstE {n : ℕ} {b : @Agent n} {S : @Dist n} {k : Bool}
    (is_k : S b = k) (a : Agent) (e : Agent) (ne : e ≠ b)
    (c : { b : Agent // b ≠ a }) (σ : List Call)
    (o : maxOne (⌜a^e c⌝ :: σ))
    (c_has_no_k : (b, k) ∉ S⌈⟨⌜a^e c⌝ :: σ, o⟩⌉c.1)
    : (b, k) ∉ S⌈⟨σ, ⁻o⟩⌉a := by
      contrapose! c_has_no_k
      unfold resultSet; simp
      refine' ⟨ ⟨ Or.inl _, _ ⟩, _ ⟩
      · exact ⟨ _, c_has_no_k, by aesop ⟩
      · intro h; exact absurd ( true_of_knowldege h ) ( by simp [ is_k ] )
      · refine' ⟨ S, ⟨ σ, _ ⟩, _, _ ⟩ <;> norm_num
        exact Sequence.maxOne_of_errFree o
        · rfl
        · exact ⟨ ⌜a^e c⌝, by aesop ⟩

/-- Extract caller not having (b,k) from callee not having (b,k) after sndE call. -/
lemma caller_real_value_not_in_sndE {n : ℕ} {b : @Agent n} {S : @Dist n} {k : Bool}
    (is_k : S b = k) (a : Agent) (e : Agent)
    (c : { b : Agent // b ≠ a }) (σ : List Call) (o : maxOne (⌜a c^e⌝ :: σ))
    (c_has_no_k : (b, k) ∉ S⌈⟨⌜a c^e⌝ :: σ, o⟩⌉c.1)
    : (b, k) ∉ S⌈⟨σ, ⁻o⟩⌉a := by
      unfold Error.resultSet at c_has_no_k
      simp +zetaDelta at *
      contrapose! c_has_no_k
      refine' ⟨ Or.inl c_has_no_k, _, _ ⟩
      · intro h; have := true_of_knowldege h; simp_all
      · refine' ⟨ S, ⟨ σ, _ ⟩, _, _, _ ⟩ <;> norm_num
        exact Sequence.maxOne_of_errFree o
        · rfl
        · use ⌜a c^e⌝
          aesop

/-- Extract callee not having (b,k) from caller not having (b,k) after sndE call with e ≠ b. -/
lemma callee_real_value_not_in_sndE {n : ℕ} {b : @Agent n} {S : @Dist n} {k : Bool}
    (is_k : S b = k) (a : Agent) (e : Agent) (ne : e ≠ b)
    (c : { b : Agent // b ≠ a }) (σ : List Call) (o : maxOne (⌜a c^e⌝ :: σ))
    (a_has_no_k : (b, k) ∉ S⌈⟨⌜a c^e⌝ :: σ, o⟩⌉a)
    : (b, k) ∉ S⌈⟨σ, ⁻o⟩⌉c := by
  contrapose! a_has_no_k
  unfold resultSet
  simp [ roleOfIn ]
  refine' ⟨ ⟨ Or.inr _, _ ⟩, _ ⟩
  · exact ⟨ ( b, k ), a_has_no_k, by aesop ⟩
  · intro h
    exact absurd ( true_of_knowldege h ) ( by simp [ is_k ] )
  · refine' ⟨ S, ⟨ σ, _ ⟩, _, _ ⟩
    · exact Sequence.maxOne_of_errFree o
    · exact ⟨ rfl, equiv_refl ⟩
    · use ⌜a c^e⌝
      aesop

/-- Helper for the Caller case of consider_corrected. -/
lemma consider_corrected_caller {n : Nat} (a b : @Agent n) {S : @Dist n}
    {k : Bool} (real_b_is_k : S b = k)
    (κ : @Call n) (σ : List Call) (o : maxOne (κ :: σ))
    (a_has_no_b_k : (b, k) ∉ S⌈⟨κ :: σ, o⟩⌉a)
    (role_def : roleOfIn a κ = Role.Caller)
    (IH : ∀ (c : @Agent n), (b, k) ∉ S⌈⟨σ, ⁻o⟩⌉c →
        equiv c (S, ⟨⟨σ, ⁻o⟩, rfl⟩) (S.switch b, ⟨⟨cor b σ, cor_maxOne (⁻o)⟩, cor_same_length⟩))
    : equiv a (S, ⟨⟨κ :: σ, o⟩, rfl⟩)
        (S.switch b, ⟨⟨κ.cor b :: cor b σ,
          by rw [← cor_cons]; exact cor_maxOne o⟩,
          by simp [OSequence.length]⟩) := by
  unfold equiv
  refine' ⟨ IH _ _, _, _ ⟩
  · exact caller_real_value_not_before real_b_is_k κ σ a o role_def a_has_no_b_k
  · exact Eq.symm Call.cor_same_role
  · rcases κ with ( _ | _ | _ ) <;> simp_all [Call.cor ]
    · have h_callee_real_value_not_in_normal : (b, k) ∉ S⌈⟨σ, ⁻o⟩⌉‹{ b // b ≠ _ }› := by
        apply callee_real_value_not_in_normal real_b_is_k _ _ _ o a_has_no_b_k
      have := IH _ h_callee_real_value_not_in_normal
      convert indistinguishable_then_same_values ( equi_of_equiv this ) using 1
      · unfold contribSet; aesop
      · unfold contribSet; aesop
    · split_ifs <;> simp_all [Call.pair ]
      · rename_i h₁ h₂ h₃
        have h_callee : (b, k) ∉ S⌈⟨σ, ⁻o⟩⌉h₁ := by
          (expose_names;
            exact
              callee_real_value_not_in_fstE real_b_is_k caller b h₁ σ
                (congrFun' (congrArg List.cons (congrFun' (congrArg (Call.fstE caller) h₂) h₁)) σ ▸
                  o)
                a_has_no_b_k)
        have := IH _ h_callee
        unfold contribSet; simp
        exact indistinguishable_then_same_values ( equi_of_equiv this )
      · unfold contribSet; simp
        rename_i h₁ h₂ h₃
        have := IH h₂ ( callee_real_value_not_in_fstE real_b_is_k _ _ _ _ _ a_has_no_b_k )
        exact indistinguishable_then_same_values ( equi_of_equiv this )
    · split_ifs <;> simp_all [Call.pair ]
      · unfold contribSet; simp [* ]
        have h_errFree : errFree σ := by
          exact bif S a then o else o
        grind +suggestions
      · unfold contribSet; simp [* ]
        rename_i c hc
        have := callee_real_value_not_in_sndE real_b_is_k _ _ hc _ _ _ a_has_no_b_k
        have := IH _ this
        have := indistinguishable_then_same_values ( equi_of_equiv this ) ; aesop

/-- Helper for the Callee case of consider_corrected. -/
lemma consider_corrected_callee {n : Nat} (a b : @Agent n) {S : @Dist n}
    {k : Bool} (real_b_is_k : S b = k)
    (κ : @Call n) (σ : List Call) (o : maxOne (κ :: σ))
    (a_has_no_b_k : (b, k) ∉ S⌈⟨κ :: σ, o⟩⌉a)
    (role_def : roleOfIn a κ = Role.Callee)
    (IH : ∀ (c : @Agent n), (b, k) ∉ S⌈⟨σ, ⁻o⟩⌉c →
        equiv c (S, ⟨⟨σ, ⁻o⟩, rfl⟩) (S.switch b, ⟨⟨cor b σ, cor_maxOne (⁻o)⟩, cor_same_length⟩))
    : equiv a (S, ⟨⟨κ :: σ, o⟩, rfl⟩)
        (S.switch b, ⟨⟨κ.cor b :: cor b σ,
          by rw [← cor_cons]; exact cor_maxOne o⟩,
          by simp [OSequence.length]⟩) := by
  unfold equiv
  refine' ⟨ _, _, _ ⟩
  · exact IH _ ( callee_real_value_not_before real_b_is_k κ σ a o role_def a_has_no_b_k )
  · exact Eq.symm Call.cor_same_role
  · unfold contribSet; rcases κ with ( _ | _ | _ ) <;> simp_all [ Call.cor ]
    · have := IH _ ( caller_real_value_not_in_normal real_b_is_k _ _ _ _ a_has_no_b_k ) ; ( have := indistinguishable_then_same_values ( equi_of_equiv this ) ; aesop; )
    · split_ifs <;> simp_all [ Call.pair ]
      · have h_errFree : errFree σ := bif S a then o else o
        grind +suggestions
      · rename_i h₁ h₂
        rename_i c e
        have := IH c ( caller_real_value_not_in_fstE real_b_is_k c e h₂ h₁ σ o a_has_no_b_k )
        exact congr_arg (invert e) (indistinguishable_then_same_values (equi_of_equiv this))
    · split_ifs <;> simp_all [ Call.pair ]
      · have := IH _ ( caller_real_value_not_in_sndE real_b_is_k _ _ _ _ _ a_has_no_b_k )
        exact indistinguishable_then_same_values ( equi_of_equiv this )
      · have := IH _ ( caller_real_value_not_in_sndE real_b_is_k _ _ _ _ _ a_has_no_b_k )
        exact indistinguishable_then_same_values ( equi_of_equiv this )

/-- Key Lemma 12 that helps to show `knowledge_implies_correct_belief`.
If the actual values of b is k, but agent a does not yet have it, then agent a considers
possible the b-switched distribution with the b-correction of the actual sequence. -/
lemma consider_corrected {n : Nat} (a b : @Agent n) {S : @Dist n} {σ : @OSequence n}
    {k : Bool} (real_b_is_k : S b = k)
    (a_has_no_b_k : (b, k) ∉ S⌈σ⌉a)
    : equiv a (S, ⟨σ, rfl⟩) (S.switch b, ⟨⟨cor b σ, cor_maxOne σ.2⟩, cor_same_length⟩) := by
  rcases σ_def : σ with ⟨σ,o⟩
  cases σ
  · simp_all
    grind [Dist.switch]
  case cons κ σ =>
    cases role_def : roleOfIn a κ
    case Other =>
      have : (b, k) ∉ S⌈⟨σ,⁻o⟩⌉a := by grind [not_in_call_then_invariant_resultSet]
      have IH := consider_corrected a b real_b_is_k this
      -- easy, sort of.
      rw! [cor_cons]
      have := @not_in_call_equiv_of_equiv n (κ.cor b) σ ?_ (cor b σ) ?_
        cor_same_length ?_ S (Dist.switch b S) a (by simp_all) IH
      · exact equiv_trans (not_in_call_then_consider_cor role_def) this
      · exact Call.cor_cons_maxOne o
      · have := @cor_maxOne _ _ b o
        rw [cor_cons] at this
        exact this
      · simp
    case Caller =>
      subst σ_def
      have a_no_bk_before := caller_real_value_not_before real_b_is_k κ σ a o role_def a_has_no_b_k
      rw! [cor_cons]
      exact consider_corrected_caller a b real_b_is_k κ σ o a_has_no_b_k role_def
        (fun c hc => consider_corrected c b real_b_is_k hc)
    case Callee =>
      subst σ_def
      have a_no_bk_before := callee_real_value_not_before real_b_is_k κ σ a o role_def a_has_no_b_k
      rw! [cor_cons]
      exact consider_corrected_callee a b real_b_is_k κ σ o a_has_no_b_k role_def
        (fun c hc => consider_corrected c b real_b_is_k hc)
termination_by
  σ.1.length

/-! ## Lemmas about Keeping and Rejecting -/

open Form

lemma callee_keeps_known_value {a b : @Agent n} {k} C
    (ra : roleOfIn a C = .Callee) S σ o
    (know_before : S⌈⟨σ, ⁻o⟩⌉ ⊧ K a ((b, k)@b))
    (had_before : S⌈⟨σ,⁻o⟩⌉ ⊧ (b, k)@a)
    : S⌈⟨C :: σ, o⟩⌉ ⊧ (b, k)@a := by
      rcases C with ⟨a', c⟩|⟨a', d, c⟩|⟨a', c, d⟩
      · unfold eval resultSet; simp_all [ roleOfIn ]
        refine' ⟨ _, S, ⟨ σ, by tauto ⟩, _, _ ⟩
        · have := true_of_knowldege know_before; simp_all [ eval ]
          exact ⟨ by
            grind, S, ⟨ ⟨ σ, by tauto ⟩, rfl, by
            exact equiv_refl ⟩, this ⟩
        · exact ⟨ rfl, equiv_refl ⟩
        · use ⌜a' c⌝
          exact ⟨ by tauto, rfl, rfl, by tauto, by have := true_of_knowldege know_before; aesop ⟩
      · unfold eval at *; simp_all [ roleOfIn ]
        grind +suggestions
      · unfold eval resultSet; simp
        simp [ *, Set.mem_diff, Set.mem_union, Set.mem_setOf_eq ]
        constructor
        · constructor
          · unfold eval at had_before; aesop
          · intro h
            have := true_of_knowldege know_before; have := true_of_knowldege h; simp_all [ eval ]
        · refine' ⟨ S, ⟨ σ, _ ⟩, _, _ ⟩ <;> norm_num
          grind
          · rfl
          · use ⌜a' c^d⌝
            have := true_of_knowldege know_before; simp_all [ eval ]

lemma callee_rejects_opposite_of_known_value {a b : @Agent n} {k} C
    (ra : roleOfIn a C = .Callee) S σ o
    (know_before : S⌈⟨σ,⁻o⟩⌉ ⊧ K a ((b, k)@b))
    : S⌈⟨C :: σ, o⟩⌉ ⊧ ( ¬'(b, !k)@a) := by
      contrapose! know_before
      unfold eval at know_before
      unfold eval at know_before
      unfold resultSet at know_before
      grind

lemma callee_rejects_opposite_of_afterwards_known_value {a b : @Agent n} {k} C
    (ra : roleOfIn a C = .Callee) S σ o
    (know_after : S⌈⟨C :: σ, o⟩⌉ ⊧ K a ((b, k)@b))
    : S⌈⟨C :: σ, o⟩⌉ ⊧ ( ¬'(b, !k)@a) := by
      revert know_after
      intro know_after
      unfold eval at know_after
      unfold eval eval
      unfold resultSet
      rcases C with ( _ | _ | _ ) <;> simp [ ra ] at know_after ⊢
      · contrapose! know_after
        obtain ⟨ T, τ, h, equ, D, hD₁, hD₂, hD₃, hD₄, hD₅ ⟩ := know_after.2.2
        use T, ⟨D :: τ.val, hD₄⟩
        simp +zetaDelta at *
        refine' ⟨ ⟨ _, _ ⟩, hD₅ ⟩
        exact h
        unfold equiv; simp [ hD₂, hD₃ ]
        exact ⟨ equ, hD₁.symm ▸ by simp [ ra ], by simp [ ra ] ⟩
      · intro h₁ h₂ x y z h₃ h₄ h₅ h₆ h₇ h₈
        convert know_after x ⟨ h₄ :: y, h₈ ⟩ _ _ using 1
        exact congr_arg ( · + 1 ) z
        unfold equiv; simp [ h₃ ]
        exact ⟨ by rw [ ← h₅, ← ra ], by rw [ ra ] ; exact ⟨ h₆, h₇ ⟩ ⟩
      · intro h1 h2 x y h3 h4 z h5 h6 h7 h8
        convert know_after _ _ _ _ using 1
        exact ⟨ z :: y, h8 ⟩
        · simp [OSequence.length_def]; rw [OSequence.length] at h3; omega
        unfold equiv; simp [ h4, h5.symm, h6, h7 ]
        exact ⟨ by simpa using ra, by simp [ ra ] ⟩

/-! ## Main Result -/

/-- Proposition 13.
Parts (i) and (ii) are given by different `k` values. -/
lemma knowledge_implies_correct_belief {n} {a b : @Agent n} {k} :
  ⊨ (K a ((b,k) @ b)) ⟹ ( ((b,k) @ b) ⋀ ((b,k) @ a) ⋀ ( ¬' (b, !k) @ a) ) := by
  intro S σ
  rw [eval_impl]
  intro knows
  rcases σ with ⟨σ,o⟩
  induction σ
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
        clear IH -- here we do not use it
        -- "We show the three conjuncts separately, where the (hardest) second comes last.""
        refine ⟨?one, ?two, ?three⟩
        case one => exact true_of_knowldege knows
        case three => exact caller_rejects_opposite_of_afterwards_known_value C ra S σ o knows
        case two =>
          -- Use the contrapose approach: if a doesn't have (b,k), then consider_corrected
          -- provides an equivalent scenario where b has the opposite value, contradicting knows.
          have is_k := true_of_knowldege knows
          simp only [OSequence.length_def, List.length_cons, stubbornness] at is_k
          unfold eval at *
          contrapose! knows
          use S.switch b, ⟨⟨cor b (C :: σ), cor_maxOne o⟩, cor_same_length⟩
          constructor
          · exact consider_corrected a b is_k knows
          · simp_all [Dist.switch]
    case Callee =>
      rw [eval_con, eval_con]
      by_cases h : eval S ⟨σ,⁻o⟩ (K a ((b,k) @ b))
      · specialize IH (⁻o) h
        rw [eval_con, eval_con] at IH
        refine ⟨by simp_all, ?_, ?_⟩
        · exact callee_keeps_known_value C ra S σ o h IH.2.1
        · exact callee_rejects_opposite_of_known_value C ra S σ o h
      · refine ⟨?one, ?two, ?three⟩
        case one => exact true_of_knowldege knows
        case three => exact callee_rejects_opposite_of_afterwards_known_value C ra S σ o knows
        case two =>
          -- Use the contrapose approach: if a doesn't have (b,k), then consider_corrected
          -- provides an equivalent scenario where b has the opposite value, contradicting knows.
          have is_k := true_of_knowldege knows
          simp only [OSequence.length_def, List.length_cons, stubbornness] at is_k
          unfold eval at *
          contrapose! knows
          use S.switch b, ⟨⟨cor b (C :: σ), cor_maxOne o⟩, cor_same_length⟩
          constructor
          · exact consider_corrected a b is_k knows
          · simp_all [Dist.switch]

/-- Corollary 14. -/
lemma knowledge_is_justified_true_belief {n} {a b : @Agent n} :
    ⊨ K a ((b,k) @ b) ⇔ K a ( ((b,k) @ b) ⋀ ((b,k) @ a) ⋀ ( ¬' (b, !k) @ a) ) := by
  intro S σ
  rw [eval_biimpl]
  constructor
  · -- left to right
    intro lhs
    rw [eval]
    intro T τ samel_ln
    have fromProp13 := @knowledge_implies_correct_belief _ a b k T τ
    rw [eval_impl] at fromProp13
    apply fromProp13
    exact (equiv_then_know_same samel_ln ((b, k)@b)).mp lhs -- using, not Lemma 8 here!
  · -- right to left, easy
    grind [eval]
