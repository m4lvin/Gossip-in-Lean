import Mathlib.Data.Set.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic.DepRewrite
import Mathlib.Tactic.Linarith

import Gossip.Error.Basic

namespace Error

open Form

/-! # Synchronous One-Error Gossip with Correction -/

/-! ## Properties of the Semantics -/

set_option maxHeartbeats 2000000 in
/-- Lemma 7 -/
lemma indistinguishable_then_same_values {n} {a : @Agent n} {S T: @Dist n} {σ τ : OSequence} :
    (S, σ) ~_a (T, τ)  →  S⌈σ⌉a = T⌈τ⌉a := by
  rcases σ with ⟨σ,o⟩
  rcases τ with ⟨τ,o'⟩
  intro ⟨same_len, equ⟩
  induction σ generalizing τ o'
  case nil =>
    have := List.length_eq_zero_iff.mp same_len.symm
    aesop
  case cons C σ IH =>
    simp at IH
    rcases List.exists_cons_of_length_eq_add_one same_len.symm with ⟨D, τ, _def⟩
    subst _def
    simp only [equiv] at equ
    specialize IH (⁻o) _ (⁻o') (by simp at same_len; assumption) equ.1 -- IH is now `S⌈σ⌉a = T⌈τ⌉a`
    -- distinguish cases whether/how a is involved in C (and thus also D) or not
    cases r : roleOfIn a C
    case Caller => -- first out of three outer cases
      simp only [r] at equ
      rcases equ with ⟨prev_equ, Caller_eq, prev_same_contrib, same_pair⟩
      unfold contribSet at prev_same_contrib
      let C_copy := C
      cases C <;> cases D <;> simp [Call.pair, roleOfIn_eq_Caller_iff] at *
      -- TODO: after Lean / batteries update speed up below with merged `simp_all?` suggestions
      all_goals -- 9 subcases
        rcases same_pair with ⟨_,_⟩
        subst_eqs
        simp only [OSequence.length_def, List.length_cons, Nat.add_right_cancel_iff] at same_len
        clear Caller_eq
        simp only [roleOfIn_a, resultSet, Subtype.forall, OSequence.length_def,
          roleOfIn_sndE_eq_Caller_iff, roleOfIn_fstE_eq_Caller_iff, roleOfIn_sndE_eq_Caller_iff]
        ext ⟨d,k⟩
        constructor
        all_goals
          intro dk_in
          simp only [Set.mem_diff, Set.mem_union, Set.mem_setOf_eq, not_forall] at dk_in
          rcases dk_in with ⟨⟨someone_had_dk_before, dk_not_refused⟩, not_self_corrected⟩
        · simp_all [← IH, ← equiv_then_know_same prev_equ]
          rcases not_self_corrected with ⟨S2, σ2, len2, C2, same_p, mO, same_contrib, role2, equ2, ndk⟩
          refine ⟨S2, σ2, ⟨by omega, ?_⟩, C2, ?_, by grind [contribSet], mO, same_p, ndk⟩
          · convert equiv_trans (equiv_symm.mp prev_equ) equ2; simp_all
          · rw [← role2]; try simp [roleOfIn]
        · simp_all [equiv_then_know_same prev_equ]
          rcases not_self_corrected with ⟨S2, σ2, len2, C2, same_p, mO, same_contrib, role2, equ2, ndk⟩
          refine ⟨S2, σ2, ⟨by omega, ?_⟩, C2, ?_, by grind [contribSet], mO, same_p, ndk⟩
          · apply equiv_trans prev_equ; rw! [same_len]; convert equ2
          · rw [← role2]; try simp [roleOfIn]
    case Callee => -- second of three outer cases, very similar to `Caller`
      simp only [r] at equ
      rcases equ with ⟨prev_equ, Callee_eq, prev_same_contrib, same_pair⟩
      unfold contribSet at prev_same_contrib
      let C_copy := C
      cases C <;> cases D <;> simp [Call.pair, roleOfIn_eq_Callee_iff] at *
      all_goals -- again 9 subcases, same proof
        rcases same_pair with ⟨_,_⟩
        rcases r with ⟨_,_⟩
        subst_eqs
        simp only [OSequence.length_def, List.length_cons, Nat.add_right_cancel_iff] at same_len
        clear Callee_eq
        simp_all [resultSet]
        ext ⟨d,k⟩
        constructor
        all_goals
          intro dk_in
          simp only [Set.mem_diff, Set.mem_union, Set.mem_setOf_eq, not_forall] at dk_in
          rcases dk_in with ⟨⟨someone_had_dk_before, dk_not_refused⟩, not_self_corrected⟩
        · simp_all [← IH, ← equiv_then_know_same prev_equ]
          rcases not_self_corrected with ⟨S2, σ2, len2, C2, same_p, mO, same_contrib, role2, equ2, ndk⟩
          refine ⟨S2, σ2, ⟨by omega, ?_⟩, C2, ?_, by grind [contribSet], mO, same_p, ndk⟩
          · convert equiv_trans (equiv_symm.mp prev_equ) equ2; simp_all
          · rw [← role2]; try simp [roleOfIn]
        · simp_all [equiv_then_know_same prev_equ]
          rcases not_self_corrected with ⟨S2, σ2, len2, C2, same_p, mO, same_contrib, role2, equ2, ndk⟩
          refine ⟨S2, σ2, ⟨by omega, ?_⟩, C2, ?_, by grind [contribSet], mO, same_p, ndk⟩
          · apply equiv_trans prev_equ; rw! [same_len]; convert equ2
          · rw [← role2]; try simp [roleOfIn]
    case Other => -- third out of three outer cases, easy
      unfold resultSet
      rw [r]
      rw [equ.2.1] at r
      rw [r]
      simp only
      exact IH

/-- Knowledge is truthful. This follows from `equiv_refl`. -/
lemma true_of_knowldege {S σ a} {φ : @Form n} :
    S⌈σ⌉ ⊧ K a φ  →  S⌈σ⌉ ⊧ φ := by
  intro hyp
  simp [eval] at hyp
  exact hyp S σ rfl equiv_refl

/-- Agents know their own initial state. This is *not* the same as Lemma 7. -/
lemma know_self m σ τ (h1 : σ.length = m) (h2 : τ.1.length = m) :
    equiv a (S, ⟨σ, h1⟩) (T, ⟨τ, h2⟩) → S a = T a  := by
  rcases σ with ⟨σ,o⟩
  rcases τ with ⟨τ,o'⟩
  induction m generalizing S T σ τ
  · rw [OSequence.length_def, List.length_eq_zero_iff] at h1
    simp [List.length_eq_zero_iff] at h2
    subst h1 h2
    simp
  case succ n IH =>
    rcases List.exists_cons_of_length_eq_add_one h1 with ⟨c1, σ, σ_def⟩
    rcases List.exists_cons_of_length_eq_add_one h2 with ⟨c2, τ, τ_def⟩
    unfold equiv
    cases h : roleOfIn a c1
    all_goals
      simp at h1 h2
      aesop

/-- Lemma 8. The truth value of any $b_a$ atom is known by agent $a$.
Note that `k` here says whether we have $b$ or $\overline{b}$. -/
lemma local_is_known {a b : @Agent n} (k : Bool) :
      ⊨ ((     ⟨b,k⟩ @ a ) ⟹ (K a (     ⟨b,k⟩ @ a) ))
    ∧ ⊨ ((Neg (⟨b,k⟩ @ a)) ⟹ (K a (Neg (⟨b,k⟩ @ a)))) := by
  constructor
  all_goals
  · simp only [valid, eval, not_not, Subtype.forall, not_forall, not_and, not_exists]
    intro S σ bk_in T τ same_len equ
    have := indistinguishable_then_same_values ⟨?_, equ⟩ -- using Lemma 7
    <;> grind only

/-- Lemma 9. Agents are stubborn about their own secrets. -/
@[simp]
lemma stubbornness m σ (h : σ.length = m) :
    S⌈σ⌉ ⊧ (a, k) @ a  ↔  S a = k := by
  rcases σ with ⟨σ,o⟩
  simp [eval]
  induction m generalizing σ k S
  case zero =>
    rw [OSequence.length_def, List.length_eq_zero_iff] at h
    subst h
    simp
    grind
  case succ m IH =>
    rcases List.exists_cons_of_length_eq_add_one h with ⟨c, σ, σ_def⟩
    subst σ_def
    unfold resultSet
    simp
    let c_copy := c
    cases rh : roleOfIn a c
    case Caller =>
     cases c <;> simp <;> simp at h
     all_goals
      simp at rh
      subst rh
      constructor
      · rintro ⟨(ak_in|ak_in), not_k⟩
        · rw [IH _ (⁻o) h] at ak_in; assumption
        · simp [eval] at not_k
          rcases not_k with ⟨T, τ, ⟨same, equ⟩, not_in⟩
          have := know_self _ _ _ _ _ equ
          specialize @IH T (!k) τ.1 _ (by aesop)
          aesop
      · intro ak_in
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · left
          rw [IH _ (⁻o) h]
          assumption
        · intro hyp
          simp [eval] at hyp
          specialize hyp S ⟨σ,⁻o⟩ rfl equiv_refl
          simp at IH
          grind
        · refine ⟨S, ⟨σ,⁻o⟩, ⟨rfl, equiv_refl⟩, ?_⟩
          use c_copy
          simp [c_copy, eval, o]
          rw [@IH _ _ σ (⁻o) h]
          simpa [roleOfIn]
    case Callee =>
     cases c <;> simp <;> simp at h
     all_goals -- Callee
      simp at rh
      rcases rh with ⟨rh1,rh2⟩
      subst rh2
      constructor
      · rintro ⟨(ak_in|ak_in), not_k⟩
        · simp [eval] at not_k
          rcases not_k with ⟨T, τ, ⟨same, equ⟩, not_in⟩
          have := know_self _ _ _ _ _ equ
          specialize @IH T (!k) τ.1 _ (by aesop)
          aesop
        · rw [IH _ (⁻o) h] at ak_in; assumption
      · intro ak_in
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · right
          rw [IH _ (⁻o) h]
          assumption
        · intro hyp
          simp [eval] at hyp
          specialize hyp S ⟨σ,⁻o⟩ rfl equiv_refl
          simp at IH
          grind
        · refine ⟨S, ⟨σ,⁻o⟩, (by simp), ?_⟩
          use c_copy
          simp [c_copy, eval, roleOfIn]
          rw [@IH _ _ σ (⁻o) h]
          simp
          tauto
    case Other =>
      cases c <;> simp <;> simp at h
      all_goals
        simp at rh
        rcases rh with ⟨rh1,rh2⟩
        rw [IH _ _ h]

/-- A useful corollary of `stubbornness`. -/
@[simp]
lemma not_notMem_resultSet : (b, ! S b) ∉ S⌈σ⌉b := by
  have := @stubbornness _ S b (! S b) _ σ rfl
  unfold eval at this
  simp [this]

/-- Lemma 10. Parts (i) and (ii) are given by the two `k` values.
The proof uses `stubbornness`. -/
lemma knowledge_of_secrets_is_preserved {a b : Agent} (k : Bool)
    (hKv : S⌈σ⌉ ⊧ K a ((b,k) @ b))
    (hSub : σ ⊑ τ)
    : S⌈τ⌉ ⊧ K a ((b,k) @ b) := by
  rcases σ with ⟨σ,o⟩
  rcases τ with ⟨τ,o'⟩
  rcases hSub with ⟨ρ, def_τ⟩ -- the `ρ` is called `τ \ σ` in the paper.
  induction ρ generalizing σ τ S o'
  · simp_all
  case cons C ρ IH =>
    subst def_τ
    have ρσ_o : maxOne (ρ ++ σ) := by exact ⁻o'
    simp only at IH hKv
    unfold eval
    simp only [List.cons_append, Subtype.forall]
    intro T τ same_len1 equ
    rcases τ with ⟨τ,o'⟩
    simp only [OSequence.length_def, List.length_cons, List.length_append] at same_len1
    -- The usual trick to split a list.
    rcases List.exists_cons_of_length_eq_add_one same_len1 with ⟨Cτ, τ, τ_def⟩
    subst τ_def
    specialize @IH S σ _ hKv (ρ ++ σ) ρσ_o rfl
    rw [stubbornness _ ⟨(Cτ :: τ), o'⟩ same_len1]
    unfold equiv at equ
    have know_same := equiv_then_know_same equ.1 ((b, k) @ b)
    rw [know_same] at IH
    have := true_of_knowldege IH
    simp only at this
    rw [stubbornness _ _ rfl] at this
    assumption

/-- Corollary 11. `Kv` of secrets is preserved. -/
lemma kv_of_secrets_is_preserved {a b : @Agent n}
    (hKv : S⌈σ⌉ ⊧ Kv a b) (hSub : σ ⊑ τ) : S⌈τ⌉ ⊧ Kv a b := by
  unfold eval eval eval at hKv
  rw [← or_iff_not_and_not] at hKv
  unfold eval eval eval
  rw [← or_iff_not_and_not]
  rcases hKv with (h|h)
  · left
    exact @knowledge_of_secrets_is_preserved n S σ τ a b true h hSub
  · right
    exact @knowledge_of_secrets_is_preserved n S σ τ a b false h hSub

/-- Agents know their own value. Follows from `stubbornness`. -/
lemma know_your_own {a : @Agent n} :
    ⊨ Kv a a := by
  intro S σ
  unfold eval eval eval
  rw [← @or_iff_not_and_not]
  cases h : S a
  · right
    unfold eval
    simp_rw [stubbornness]
    intro T ⟨τ, same_len⟩ equ
    rw [know_self _ _ _ _ _ equ] at h
    exact h
  · left
    unfold eval
    simp_rw [stubbornness]
    intro T ⟨τ, same_len⟩ equ
    rw [know_self _ _ _ _ _ equ] at h
    exact h

/-- Helper for Prop 12 "iff (call semantics)" -/
lemma not_in_call_then_invariant_resultSet {a : @Agent n} {C : @Call n}
    (h : roleOfIn a C = .Other) S σ o
    : S⌈⟨C :: σ, o⟩⌉a = S⌈⟨σ, ⁻o⟩⌉a := by
  conv => left; unfold resultSet
  simp [h]

/-- Helper for Prop 12 "iff (semantics of formulas and observation relation)" -/
lemma not_in_call_then_invariant_kv {a : @Agent n} {C : @Call n}
    (h : roleOfIn a C = .Other) b S σ o
    : eval S ⟨C :: σ,  o⟩ (Kv a b)
    ↔ eval S ⟨     σ, ⁻o⟩ (Kv a b) := by
  constructor
  · intro know_after
    unfold eval eval eval at *
    rw [← @or_iff_not_and_not] at *
    rcases know_after with know_after|know_after
    · left
      simp only [eval, stubbornness, Subtype.forall, OSequence.length_def, List.length_cons] at *
      intro T τ same_len equ
      let CnoErr : Call := match C with -- we remove the error from `C` if needed.
        | ⌜d e⌝ => ⌜d e⌝
        | ⌜d^c e⌝ => ⌜d e⌝
        | ⌜d e^c⌝ => ⌜d e⌝
      have h' : roleOfIn a CnoErr = .Other := by unfold CnoErr; cases C <;> simp_all
      apply know_after T ⟨CnoErr :: τ.1, ?_⟩ (by simp [OSequence.length]; exact same_len)
      · unfold equiv; simp [h, h', equ]
      · unfold CnoErr; cases C <;> simp [maxOne]
    · right
      simp only [eval, stubbornness, Subtype.forall, OSequence.length_def, List.length_cons] at *
      intro T τ same_len equ
      let CnoErr : Call := match C with -- we remove the error from `C` if needed.
        | ⌜d e⌝ => ⌜d e⌝
        | ⌜d^c e⌝ => ⌜d e⌝
        | ⌜d e^c⌝ => ⌜d e⌝
      have h' : roleOfIn a CnoErr = .Other := by unfold CnoErr; cases C <;> simp_all
      apply know_after T ⟨CnoErr :: τ.1, ?_⟩ (by simp [OSequence.length]; exact same_len)
      · unfold equiv; simp [h, h', equ]
      · unfold CnoErr; cases C <;> simp [maxOne]
  · intro hyp
    apply kv_of_secrets_is_preserved hyp
    simp

/-- Stronger value-specific helper for Prop 12 "iff (semantics of formulas and observation relation)" -/
lemma not_in_call_then_invariant_k {k} {a : @Agent n} {C : @Call n}
    (h : roleOfIn a C = .Other) b S σ o
    : eval S ⟨C :: σ,  o⟩ (K a (⟨b, k⟩ @ b))
    ↔ eval S ⟨     σ, ⁻o⟩ (K a (⟨b, k⟩ @ b)) := by
  constructor
  · intro know_after
    have := @not_in_call_then_invariant_kv n a C h b S σ o
    rw [eval_dis] at this
    cases k
    · have := this.mp (Or.inr know_after)
      rw [eval_dis] at this
      rcases this with h|h
      · exfalso
        have := true_of_knowldege h
        have := true_of_knowldege know_after
        simp at *
        grind
      · exact h
    · have := this.mp (Or.inl know_after)
      rw [eval_dis] at this
      rcases this with h|h
      · exact h
      · exfalso
        have := true_of_knowldege h
        have := true_of_knowldege know_after
        simp at *
        grind
  · intro hyp
    apply @knowledge_of_secrets_is_preserved n S ⟨σ,⁻o⟩ ⟨_,o⟩ a b k hyp
    simp

lemma caller_keeps_known_value {a b : @Agent n} {k} C
    (ra : roleOfIn a C = .Caller) S σ o
    (know_before : S⌈⟨σ, ⁻o⟩⌉ ⊧ K a ((b, k)@b))
    (had_before : S⌈⟨σ,⁻o⟩⌉ ⊧ (b, k)@a)
    : S⌈⟨C :: σ, o⟩⌉ ⊧ (b, k)@a := by
  have bkb := true_of_knowldege know_before
  rcases C with ⟨a',c⟩|⟨a',d,c⟩|⟨a',c,d⟩ <;> simp at ra <;> subst ra
  · unfold eval resultSet; simp
    refine ⟨⟨by simp_all [eval], ?_⟩, ?_⟩
    · intro hyp
      have := true_of_knowldege hyp
      simp_all
    · use S, ⟨σ,⁻o⟩; simp; use ⌜a c⌝; simp_all
  · unfold eval resultSet
    simp [roleOfIn]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp_all [eval]
    · intro hyp
      have := true_of_knowldege hyp
      simp_all
    · use S, ⟨σ,⁻o⟩; simp
      use ⌜a^d c⌝ -- the ^d here does not matter
      simp_all [contribSet]
  · unfold eval resultSet
    simp [roleOfIn]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp_all [eval]
    · intro hyp
      have := true_of_knowldege hyp
      simp_all
    · use S, ⟨σ,⁻o⟩; simp
      use ⌜a c^d⌝ -- but here the ^d *does* matter
      simp_all [contribSet]

lemma caller_rejects_opposite_of_known_value {a b : @Agent n} {k} C
    (ra : roleOfIn a C = .Caller) S σ o
    (know_before : S⌈⟨σ,⁻o⟩⌉ ⊧ K a ((b, k)@b))
    : S⌈⟨C :: σ, o⟩⌉ ⊧ ( ¬'(b, !k)@a) := by
  have bkb := true_of_knowldege know_before
  rcases C with ⟨a',c⟩|⟨a',d,c⟩|⟨a',c,d⟩ <;> simp at ra <;> subst ra
  all_goals
    unfold eval
    intro h
    unfold eval resultSet at h
    simp [roleOfIn] at h
    rcases h with ⟨⟨h1, h2⟩, h3⟩
    absurd h2
    exact know_before

/-- Footnote 1. "in fact the knowledge is already there" -/
lemma caller_rejects_opposite_of_afterwards_known_value {a b : @Agent n} {k} C
    (ra : roleOfIn a C = .Caller) S σ o
    (know_after : S⌈⟨C :: σ, o⟩⌉ ⊧ K a ((b, k)@b))
    : S⌈⟨C :: σ, o⟩⌉ ⊧ ( ¬'(b, !k)@a) := by
  unfold eval at know_after
  unfold eval eval
  unfold resultSet
  simp [ra]
  rcases C with ⟨a',c⟩|⟨a',d,c⟩|⟨a',c,d⟩ <;> simp at ra <;> subst ra <;> simp only <;> simp_all
  all_goals
    intro h1 h2 T τ same_len equ D role_D same_set same_p mO
    apply know_after T ⟨D :: τ.1, mO⟩
    · simp_all [equiv, contribSet]
      cases D <;> cases same_p <;> simp_all [roleOfIn]
    · rw [OSequence.length, ← same_len]; rfl

-- Maybe rename this later ;-)
lemma caller_the_hard_case {a b : @Agent n} {k} S C σ
    (o : maxOne (C :: σ))
    (knows : S⌈⟨C :: σ, o⟩⌉ ⊧ K a ((b, k)@b))
    (ra : roleOfIn a C = .Caller)
    (not_know_before : ¬ S⌈⟨σ,⁻o⟩⌉ ⊧ K a ((b, k)@b))
    : S⌈⟨C :: σ, o⟩⌉ ⊧ (b, k)@a := by
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
      -- "First ..." That is `Dist.switch`.
      -- "Second ..."
      rcases not_know_before with ⟨T, ⟨τ, same_len, equ⟩, Tb_not_k⟩
      absurd knows
      simp
      by_cases (b, !k) ∉ S⌈⟨σ,⁻o⟩⌉a <;> by_cases (b, !k) ∉ S⌈⟨σ,⁻o⟩⌉c
      · refine ⟨T, ⟨⟨⌜a c⌝ :: τ.1, by simp_all [maxOne]⟩, ?_⟩ , by simp [*]⟩
        simp [equiv, OSequence.length, contribSet, ← same_len, equ]
        sorry
      · sorry
      · sorry
      · sorry
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
        clear IH -- here we do not use it?
        -- "We show the three conjuncts separately, where the (hardest) second comes last.""
        refine ⟨?one, ?two, ?three⟩
        case one => exact true_of_knowldege knows
        case three => exact caller_rejects_opposite_of_afterwards_known_value C ra S σ o knows
        case two => exact caller_the_hard_case S C σ o knows ra h
    case Callee =>
      -- Analogous, but will need `callee_...` lemmas instead of `caller_...`.
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

end Error
