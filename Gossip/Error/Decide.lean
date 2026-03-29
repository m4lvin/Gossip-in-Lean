import Mathlib.Data.Set.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic.DepRewrite
import Mathlib.Tactic.Linarith

import Gossip.Error.DecHelp
import Gossip.Error.Basic

namespace Error

def Value.all : List (@Value n) := sorry

def Value.all_spec : x ∈ Value.all := sorry

/-! ## List of all distributions -/

def Dist.all : {n : Nat} → List (@Dist n)
  | 0 => [ fun x => by exfalso; cases x; grind ]
  | k+1 => (@Dist.all k).flatMap ( fun f => [ fun k => k.lastCases false f
                                            , fun k => k.lastCases true f ] )

/-- Forget about the maximum agent. -/
abbrev Dist.forget {n : Nat} (S : @Dist (n+1)) : @Dist n := fun a => S a.castSucc

lemma Dist.all_spec (S : @Dist n) : S ∈ Dist.all := by
  induction n
  · grind [Dist.all]
  case succ n IH =>
    simp only [all, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    cases h : S (Fin.last _)
    · refine ⟨S.forget, IH S.forget, Or.inl ?_⟩
      ext k
      apply @Fin.lastCases n _ _ _ k <;> simp_all
    · refine ⟨S.forget, IH S.forget, Or.inr ?_⟩
      ext k
      apply @Fin.lastCases n _ _ _ k <;> simp_all

/-! ## List of all calls -/

def Call.castSucc {n} : @Call n → @Call (n+1)
  | .normal a b => .normal a.castSucc b.castSucc
  | .fstE a c b => .fstE a.castSucc c.castSucc b.castSucc
  | .sndE a b c => .sndE a.castSucc b.castSucc c.castSucc

def Call.allAmong {n : Nat} : @Agent n → @Agent n → List (@Call n)
  | a, b => [ .normal a b, .normal b a ]
        ++ (List.range n).attach.map (fun c => .fstE a ⟨c.1, by grind⟩ b)
        ++ (List.range n).attach.map (fun c => .fstE b ⟨c.1, by grind⟩ a)
        ++ (List.range n).attach.map (fun c => .sndE a b ⟨c.1, by grind⟩)
        ++ (List.range n).attach.map (fun c => .sndE b a ⟨c.1, by grind⟩)

-- small worry: is it okay to let an agent call itself?

def Call.all : {n : Nat} → List (@Call n)
  | 0 => [ ]
  | k+1 => (@Call.all k).map Call.castSucc ++
      (List.range k).attach.flatMap (fun b => Call.allAmong ⟨k,by grind⟩ ⟨b.1,by grind⟩)

lemma Call.all_spec (C : @Call n) : C ∈ Call.all := by
  cases n
  case zero =>
    exfalso; cases C <;> next a => cases a; grind
  case succ n =>
    unfold Call.all
    simp
    sorry

/-! ## List of all OSequences of a given length -/

mutual

instance instDecErrFree : Decidable (errFree σ) := by
  cases σ
  · simp_all [errFree]
    exact instDecidableTrue
  case cons C σ =>
    cases C <;> simp [errFree]
    · exact instDecErrFree
    · exact instDecidableFalse
    · exact instDecidableFalse

instance instDecMaxOne : Decidable (maxOne σ) := by
  cases σ
  · simp_all [maxOne]
    exact instDecidableTrue
  case cons C σ =>
    cases C <;> simp [maxOne]
    · exact instDecMaxOne
    · exact instDecErrFree
    · exact instDecErrFree
end

def OSequence.fixLen_all : (k : Nat) → List { σ : @OSequence n // σ.length = k }
  | 0 => [ ⟨⟨[], by simp⟩,by simp⟩ ]
  | k+1 => (OSequence.fixLen_all k).flatMap (fun ⟨⟨σ,o⟩,hk⟩ =>
              Call.all.flatMap (fun C =>
                if ho : Error.maxOne (C :: σ)
                then [⟨⟨C :: σ, ho⟩, by simp_all⟩]
                else []))

lemma OSequence.fixLen_all_spec (σ : { σ : @OSequence n // σ.length = k }) :
    σ ∈ OSequence.fixLen_all k := by
  rcases σ with ⟨⟨σ,o⟩,hk⟩
  cases k <;> cases σ
  case zero.nil =>
    simp_all [OSequence.fixLen_all]
  case zero.cons =>
    exfalso; simp_all
  case succ.nil =>
    exfalso; simp_all
  case succ.cons k C σ =>
    unfold fixLen_all
    simp
    have IH := @OSequence.fixLen_all_spec n k ⟨⟨σ,⁻o⟩, by simp_all⟩
    refine ⟨⟨σ,⁻o⟩, by simp at hk; simp_all, IH, ?_⟩
    simp [Call.all_spec]

/-! ## Deciding the Semantics -/

mutual

instance instDecResultSetMem {n} {S : @Dist n} {σ : OSequence} {a : Agent} {x : Value} :
    Decidable (x ∈ S⌈σ⌉a) := by
  rcases σ with ⟨σ, o⟩
  cases σ
  case nil =>
    simp
    exact decEq x (a, S a)
  case cons C σ =>
    cases C
    case normal b c =>
      unfold resultSet roleOfIn
      by_cases a = b <;> by_cases a = c <;> simp_all
      · refine @instDecidableAnd _ _ (@instDecidableAnd _ _ ?_ ?_) ?_
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ b x
        · exact @instDecidableNot _ (@instDecEval n S ⟨σ,⁻o⟩ (Form.K b ((x.1, !x.2)@x.1)))
        · sorry
      · refine @instDecidableAnd _ _ (@instDecidableAnd _ _ (@instDecidableOr _ _ ?_ ?_) ?_) ?_
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ b x
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ c x
        · exact @instDecidableNot _ (@instDecEval n S ⟨σ,⁻o⟩ (Form.K b ((x.1, !x.2)@x.1)))
        · sorry
      · refine @instDecidableAnd _ _ (@instDecidableAnd _ _ (@instDecidableOr _ _ ?_ ?_) ?_) ?_
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ b x
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ c x
        · exact @instDecidableNot _ (@instDecEval n S ⟨σ,⁻o⟩ (Form.K c ((x.1, !x.2)@x.1)))
        · sorry
      · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ a x
    case fstE =>
      sorry
    case sndE =>
      sorry
termination_by
  (σ.length, 0) -- should be below contribSet
decreasing_by
  all_goals
    apply Prod.Lex.left; grind [OSequence.length] -- Sequence becomes shorter in all cases.

instance instDecResultSetEq {n} {S T : @Dist n} {σ τ : OSequence} {a b : Agent} :
    Decidable (S⌈σ⌉a = T⌈τ⌉b) := by
  rw [Set.ext_iff]
  apply Decidable.forall_of_list_mem (@Value.all_spec _)
  intro x
  have := @instDecResultSetMem n S σ a x
  have := @instDecResultSetMem n T τ b x
  exact instDecidableIff
termination_by
  (σ.1.length, 0)
decreasing_by
  · sorry
  · sorry

instance instDecContribSetOneEq {n} {S T : @Dist n} {σ τ C D} :
    Decidable ((contribSet S σ C).1 = (contribSet T τ D).1) := by
  unfold contribSet
  cases C <;> cases D <;> simp
  · exact @instDecResultSetEq n S T σ τ _ _
  · sorry -- invert
  · exact instDecResultSetEq
  · sorry -- invert
  · sorry -- invert
  · sorry -- invert
  · exact instDecResultSetEq
  · sorry -- invert
  · exact instDecResultSetEq
termination_by
  (σ.1.length, 0) -- ??
decreasing_by
  · sorry -- ??
  · sorry -- ??
  · sorry -- ??
  · sorry -- ??

instance instDecContribSetTwoEq :
    Decidable ((contribSet S σ C).2 = (contribSet T τ D).2) := by
  sorry
termination_by
  (σ.1.length, 0)

instance instDecEquiv : Decidable (equiv a ⟨S,σ⟩ (T,τ))  := by
  rcases σ with ⟨⟨σ,o⟩,len_σ⟩
  rcases τ with ⟨⟨τ,o'⟩,len_τ⟩
  unfold equiv
  cases σ <;> cases τ
  case nil.nil =>
    simp_all
    exact (S a).decEq (T a)
  · exfalso; grind [OSequence.length]
  · exfalso; grind [OSequence.length]
  case cons.cons C σ D τ =>
    simp_all
    refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_)
    · exact instDecEquiv
    · exact decEq (roleOfIn a C) (roleOfIn a D)
    · cases roleOfIn a C <;> simp
      · refine @instDecidableAnd _ _ ?_ ?_
        · exact instDecContribSetTwoEq
        · apply decEq
      · refine @instDecidableAnd _ _ ?_ ?_
        · exact instDecContribSetOneEq
        · apply decEq
      · exact instDecidableTrue
termination_by
  (σ.1.length, 0) -- should be above contribSet
decreasing_by
  all_goals
    apply Prod.Lex.left; grind [OSequence.length]

instance instDecEval {n} {S : @Dist n} {σ φ} : Decidable (eval S σ φ) := by
  cases φ
  case Top =>
    simp [eval]
    exact instDecidableTrue
  case Con φ1 φ2 =>
    have := @instDecEval n S σ φ1
    have := @instDecEval n S σ φ2
    rw [eval_con]
    exact instDecidableAnd
  case Neg φ =>
    have := @instDecEval n S σ φ
    simp [eval]
    exact instDecidableNot
  case Has =>
    unfold eval
    apply instDecResultSetMem
  case K =>
    unfold eval
    -- We use a helper to decide ∀ here, similar to epistemic sabotage code.
    apply Decidable.forall_of_list_mem Dist.all_spec
    intro S
    simp only
    apply Decidable.forall_of_list_mem OSequence.fixLen_all_spec
    intro τ
    simp
    refine @instDecidableForall _ _ ?_ ?_ -- why is this not called `instDecidableImpl`?
    · apply instDecEquiv
    · apply instDecEval
termination_by
  (σ.length, φ.length)
decreasing_by -- Sequence length stays the same, but formula becomes shorter.
  · apply Prod.Lex.right; simp; linarith
  · apply Prod.Lex.right; simp
  · apply Prod.Lex.right; simp -- Here we need `resultSet  <  Has i i`.
  · apply Prod.Lex.right; simp
  · apply Prod.Lex.right; simp -- needs `somestuff < K i φ` here?
  /-
  · apply Prod.Lex.right; simp
  · apply Prod.Lex.right; simp -- Here we need `equiv  <  K i φ`.
  -/
  · rw [τ.2] -- Here `σ` and `τ` must have the same length.
    apply Prod.Lex.right
    simp_wf

end
