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

@[grind]
def cor {n} : @Agent n → @Sequence n → @Sequence n
  | _, [] => []
  | b, .normal a c :: σ => .normal a c :: cor b σ
  | b, .fstE a e c :: σ =>
      if e = b  then .normal a c :: cor b σ
                else .fstE a e c :: cor b σ
  | b, .sndE a c e :: σ =>
      if e = b  then .normal a c :: cor b σ
                else .fstE a e c :: cor b σ
termination_by
  _ σ => σ
decreasing_by
  all_goals simp_all

@[simp, grind .]
lemma cor_errFree {n} {σ : @Sequence n} {b : @Agent n} (h : errFree σ) : errFree (cor b σ) := by
  induction σ
  case nil => simp_all [errFree, cor]
  case cons κ σ IH => cases κ <;> simp_all [cor, errFree]

@[simp, grind .]
lemma cor_maxOne {n} {σ : @Sequence n} {b : @Agent n} (h : maxOne σ) : maxOne (cor b σ) := by
  cases σ
  case nil => simp_all [cor]
  case cons κ σ =>
    cases κ
    case normal =>
      simp [cor]
      simp [maxOne]
      simp [maxOne] at h
      exact @cor_maxOne _ _ b h
    case fstE a e c =>
      simp [cor]
      by_cases eb : e = b
      · simp [eb]
        simp [maxOne]
        exact @cor_maxOne _ _ b (⁻h)
      · simp_all [maxOne]
    case sndE a c e =>
      simp [cor]
      by_cases eb : e = b
      · simp [eb]
        simp [maxOne]
        exact @cor_maxOne _ _ b (⁻h)
      · simp_all [maxOne]

@[simp]
lemma cor_same_length : (cor b σ).length = σ.length := by
  induction σ
  · simp_all [cor]
  case cons κ σ IH =>
    cases κ <;> simp_all [cor] <;> split <;> simp_all

def Call.cor : @Agent n → @Call n → @Call n
  | _, .normal a c => .normal a c
  | b, .fstE a e c => if e = b  then .normal a c else .fstE a e c
  | b, .sndE a c e => if e = b  then .normal a c else .fstE a e c

lemma cor_cons {σ : @Sequence n} : cor b (κ :: σ) = κ.cor b :: cor b σ := by
  induction κ <;> simp [cor, Call.cor] <;> split <;> simp

lemma Call.cor_cons_maxOne : maxOne (κ :: σ) → maxOne (Call.cor b κ :: σ) := by
  intro h
  cases κ
  case normal c d =>
    simp_all [maxOne, cor]
  case fstE c e d =>
    rcases d with ⟨d, c_neq_d⟩
    simp_all [cor]
    split <;> simp_all [maxOne]; exact Sequence.maxOne_of_errFree h
  case sndE c d e =>
    rcases d with ⟨d, c_neq_d⟩
    simp_all [cor]
    split <;> simp_all [maxOne]; exact Sequence.maxOne_of_errFree h

@[simp, grind .]
lemma Call.cor_same_role {a b : @Agent n} {κ : @Call n} :
    roleOfIn a (κ.cor b) = roleOfIn a κ:= by
  cases κ
  case normal c d =>
    rcases d with ⟨d, c_neq_d⟩
    by_cases a = c <;> by_cases a = d <;> subst_eqs <;> simp_all [cor]
  case fstE c e d =>
    rcases d with ⟨d, c_neq_d⟩
    by_cases a = c <;> by_cases a = d <;> subst_eqs <;> simp_all [cor] <;> split <;> simp [roleOfIn]
  case sndE c d e =>
    rcases d with ⟨d, c_neq_d⟩
    by_cases a = c <;> by_cases a = d <;> subst_eqs <;> simp_all [cor] <;> split <;> simp [roleOfIn]

@[grind .]
lemma not_in_call_equiv_of_equiv
    {S T : @Dist n}
    (a : @Agent n)
    (not_in_call : roleOfIn a κ = Role.Other)
    (equ_before : equiv a (S, ⟨⟨σ, ⁻o⟩, rfl⟩) (T, ⟨⟨τ, ⁻p⟩, h1⟩))
    : equiv a (S, ⟨⟨κ :: σ, o⟩, rfl⟩) (T, ⟨⟨κ :: τ, p⟩, h2⟩) := by
  unfold equiv; simp_all

lemma not_in_call_then_consider_cor
    (not_in_call : roleOfIn a κ = Role.Other)
    : equiv a (S, ⟨⟨κ :: σ, o⟩, h1⟩) (S, ⟨⟨Call.cor b κ :: σ, o'⟩, h2⟩) := by
  unfold equiv; simp_all

/-- New Lemma that should help.
If the actual values of b is k, but agent a does not yet hae it, then agent a considers
the b-flipped distribution possible, with the b-correction of the actual sequence. -/
lemma consider_corrected {n : Nat} (a b : @Agent n) {S : @Dist n} {σ : @OSequence n}
    {k : Bool} (real_b_is_k : S b = k)
    (a_has_no_b_k : (b, k) ∉ S⌈σ⌉a)
    : equiv a (S, ⟨σ, rfl⟩) (S.switch b, ⟨⟨cor b σ, cor_maxOne σ.2⟩, cor_same_length⟩) := by
  rcases σ_def : σ with ⟨σ,o⟩
  cases σ
  · simp_all [cor]
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
      -- TODO NEXT
      by_cases (b, !k) ∈ S⌈⟨κ::σ,o⟩⌉a
      case neg a_has_no_op_k =>
        -- claim "then already ..."
        -- have IHa :=
        -- have IH_callee :=
        sorry
      case pos a_has_k =>
        -- "there are more subcases to consider"
        sorry

    case Callee => -- hopefully analogous, don't do it yet.
      sorry
termination_by
  σ.1.length

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
      have byLemma := @consider_corrected n a b S ⟨⌜a c⌝ :: σ, o⟩ k is_k claim
      absurd knows
      simp
      refine ⟨S.switch b, ⟨⟨_, cor_maxOne o⟩, ?_, byLemma⟩ , by simpa [Dist.switch]⟩
      simp

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
