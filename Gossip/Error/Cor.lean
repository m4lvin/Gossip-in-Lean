import Gossip.Error.Basic

namespace Error

/-! # Synchronous One-Error Gossip with Correction -/

/-! ## Call Correction -/

/-! ### Single Call Correction -/

def Call.cor : @Agent n → @Call n → @Call n
  | _, .normal a c => .normal a c
  | b, .fstE a e c => if e = b  then .normal a c else .fstE a e c
  | b, .sndE a c e => if e = b  then .normal a c else .sndE a c e

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

/-- The pair of `κ.cor` is the same as pair of `κ`. -/
@[simp]
lemma call_cor_pair {n} (b : @Agent n) (κ : @Call n) : (κ.cor b).pair = κ.pair := by
  cases κ <;> simp [Call.cor] <;> aesop

/-! ### Sequence Call Correction -/

@[grind]
def cor {n} : @Agent n → @Sequence n → @Sequence n
  | _, [] => []
  | b, .normal a c :: σ => .normal a c :: cor b σ
  | b, .fstE a e c :: σ =>
      if e = b  then .normal a c :: cor b σ
                else .fstE a e c :: cor b σ
  | b, .sndE a c e :: σ =>
      if e = b  then .normal a c :: cor b σ
                else .sndE a c e :: cor b σ
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

lemma cor_cons {σ : @Sequence n} : cor b (κ :: σ) = κ.cor b :: cor b σ := by
  induction κ <;> simp [cor, Call.cor] <;> split <;> simp

lemma not_in_call_then_consider_cor
    (not_in_call : roleOfIn a κ = Role.Other)
    : equiv a (S, ⟨⟨κ :: σ, o⟩, h1⟩) (S, ⟨⟨Call.cor b κ :: σ, o'⟩, h2⟩) := by
  unfold equiv; simp_all

/-- If `σ` is error-free, then `cor b σ = σ`. -/
@[simp]
lemma cor_errFree_id {n} (b : @Agent n) (σ : @Sequence n) (h : errFree σ) : cor b σ = σ := by
  induction σ generalizing b
  case nil => simp [cor]
  case cons k σ ih => cases k <;> simp_all [errFree, cor]
