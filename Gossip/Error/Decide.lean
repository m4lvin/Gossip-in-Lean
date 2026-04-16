import Mathlib.Data.Set.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic.DepRewrite
import Mathlib.Tactic.Linarith

import Gossip.Error.DecHelp
import Gossip.Error.Basic

namespace Error

def Value.all : List (@Value n) :=
  (List.range n).attach.flatMap (fun a => [ ⟨⟨a.1, by grind⟩, true⟩
                                          , ⟨⟨a.1, by grind⟩, false⟩ ])

def Value.all_spec : x ∈ Value.all := by
  rcases x with ⟨a,b⟩
  unfold Value.all
  simp
  grind

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
  | .normal a b => .normal a.castSucc ⟨b.1.castSucc, by cases b; simpa [Fin.castSucc_inj]⟩
  | .fstE a c b => .fstE a.castSucc c.castSucc ⟨b.1.castSucc, by cases b; simpa [Fin.castSucc_inj]⟩
  | .sndE a b c => .sndE a.castSucc ⟨b.1.castSucc, by cases b; simpa [Fin.castSucc_inj]⟩ c.castSucc

def Call.allAmong {n : Nat} : @Agent n → @Agent n → List (@Call n)
  | a, b => if h : b = a then []
            else .normal a ⟨b, h⟩
            :: (List.range n).attach.map (fun c => .fstE a ⟨c.1, by grind⟩ ⟨b,h⟩)
            ++ (List.range n).attach.map (fun c => .sndE a ⟨b,h⟩ ⟨c.1, by grind⟩)

def Call.all {n : Nat} : List (@Call n) :=
  (List.range n).attach.flatMap (fun a =>
    (List.range n).attach.flatMap (fun b =>
      Call.allAmong ⟨a.1,by grind⟩ ⟨b.1,by grind⟩))

lemma Call.all_spec (C : @Call n) : C ∈ Call.all := by
  cases n
  case zero =>
    exfalso; cases C <;> next a => cases a; grind
  case succ n =>
    unfold Call.all
    cases C <;> simp [allAmong] <;> grind

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

set_option maxHeartbeats 400000 in
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
    -- NORMAL
    case normal b c =>
      unfold resultSet roleOfIn
      by_cases a = b <;> by_cases a = c <;>
        simp_all only [Classical.not_imp, Set.mem_diff, Set.mem_setOf_eq, Set.mem_union, Set.union_self, exists_and_left, not_forall, ↓reduceIte]
      · refine @instDecidableAnd _ _ (@instDecidableAnd _ _ ?_ ?_) ?_
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ b x
        · exact @instDecidableNot _ (@instDecEval n S ⟨σ,⁻o⟩ (Form.K b ((x.1, !x.2)@x.1)))
        · refine Decidable.exists_of_list_mem Dist.all_spec (fun T => ?_)
          refine Decidable.exists_of_list_mem (@OSequence.fixLen_all_spec n σ.length) (fun τ => ?_)
          refine @instDecidableAnd _ _ instDecEquiv ?_
          · apply Decidable.exists_of_list_mem Call.all_spec
            rintro (⟨x,y⟩|⟨x,z,y⟩|⟨x,y,z⟩) <;> by_cases b = x <;> by_cases b = y
              <;> simp_all [Call.pair] <;> try exact instDecidableFalse
            all_goals
              refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_)
              <;> try refine @instDecidableAnd _ _ ?_ ?_
            all_goals try exact instDecMaxOne
            all_goals try exact @instDecidableNot _ instDecEval
            all_goals apply @instDecContribSetTwoEq n σ.length S T ⟨⟨σ,o⟩, rfl⟩ τ
      · refine @instDecidableAnd _ _ (@instDecidableAnd _ _ (@instDecidableOr _ _ ?_ ?_) ?_) ?_
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ b x
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ c x
        · exact @instDecidableNot _ (@instDecEval n S ⟨σ,⁻o⟩ (Form.K b ((x.1, !x.2)@x.1)))
        · refine Decidable.exists_of_list_mem Dist.all_spec (fun T => ?_)
          refine Decidable.exists_of_list_mem (@OSequence.fixLen_all_spec n σ.length) (fun τ => ?_)
          refine @instDecidableAnd _ _ instDecEquiv ?_
          · apply Decidable.exists_of_list_mem Call.all_spec
            rintro (⟨x,y⟩|⟨x,z,y⟩|⟨x,y,z⟩) <;> by_cases b = x <;> by_cases b = y
              <;> simp_all [Call.pair] <;> try exact instDecidableFalse
            all_goals
              refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_)
              <;> try refine @instDecidableAnd _ _ ?_ ?_
            all_goals try exact instDecMaxOne
            all_goals try exact @instDecidableNot _ instDecEval
            all_goals try apply decEq
            all_goals apply @instDecContribSetTwoEq n σ.length S T ⟨⟨σ,o⟩, rfl⟩ τ
      · refine @instDecidableAnd _ _ (@instDecidableAnd _ _ (@instDecidableOr _ _ ?_ ?_) ?_) ?_
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ b x
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ c x
        · exact @instDecidableNot _ (@instDecEval n S ⟨σ,⁻o⟩ (Form.K c ((x.1, !x.2)@x.1)))
        · refine Decidable.exists_of_list_mem Dist.all_spec (fun T => ?_)
          refine Decidable.exists_of_list_mem (@OSequence.fixLen_all_spec n σ.length) (fun τ => ?_)
          refine @instDecidableAnd _ _ instDecEquiv ?_
          · apply Decidable.exists_of_list_mem Call.all_spec
            rintro (⟨x,y⟩|⟨x,z,y⟩|⟨x,y,z⟩) <;> by_cases b = x <;> by_cases b = y
              <;> simp_all [Call.pair] <;> try exact instDecidableFalse
            all_goals
              refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_)
            all_goals try refine @instDecidableAnd _ _ ?_ ?_
            all_goals try refine @instDecidableAnd _ _ ?_ ?_
            all_goals try exact instDecMaxOne
            all_goals try exact @instDecidableNot _ instDecEval
            all_goals try apply decEq
            all_goals apply @instDecContribSetOneEq n σ.length S T ⟨⟨σ,o⟩, rfl⟩ τ
      · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ a x
    -- fstE
    case fstE b e d =>
      unfold resultSet roleOfIn
      by_cases a = b <;> by_cases a = d <;>
        simp_all only [Classical.not_imp, Set.mem_diff, Set.mem_setOf_eq, Set.mem_union,
          Set.union_self, exists_and_left, not_forall, ↓reduceIte]
      -- a = b ∧ a = d (Caller, union collapses)
      · refine @instDecidableAnd _ _ (@instDecidableAnd _ _ ?_ ?_) ?_
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ b x
        · exact @instDecidableNot _ (@instDecEval n S ⟨σ,⁻o⟩ (Form.K b ((x.1, !x.2)@x.1)))
        · refine Decidable.exists_of_list_mem Dist.all_spec (fun T => ?_)
          refine Decidable.exists_of_list_mem (@OSequence.fixLen_all_spec n σ.length) (fun τ => ?_)
          refine @instDecidableAnd _ _ instDecEquiv ?_
          · apply Decidable.exists_of_list_mem Call.all_spec
            rintro (⟨x,y⟩|⟨x,z,y⟩|⟨x,y,z⟩) <;> by_cases b = x <;> by_cases b = y
              <;> simp_all [Call.pair] <;> try exact instDecidableFalse
            all_goals
              refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_)
              <;> try refine @instDecidableAnd _ _ ?_ ?_
            all_goals try exact instDecMaxOne
            all_goals try exact @instDecidableNot _ instDecEval
            all_goals apply @instDecContribSetTwoEq n σ.length S T ⟨⟨σ,⁻o⟩, rfl⟩ τ
      -- a = b ∧ a ≠ d (Caller)
      · refine @instDecidableAnd _ _ (@instDecidableAnd _ _ (@instDecidableOr _ _ ?_ ?_) ?_) ?_
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ b x
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ d x
        · exact @instDecidableNot _ (@instDecEval n S ⟨σ,⁻o⟩ (Form.K b ((x.1, !x.2)@x.1)))
        · refine Decidable.exists_of_list_mem Dist.all_spec (fun T => ?_)
          refine Decidable.exists_of_list_mem (@OSequence.fixLen_all_spec n σ.length) (fun τ => ?_)
          refine @instDecidableAnd _ _ instDecEquiv ?_
          · apply Decidable.exists_of_list_mem Call.all_spec
            rintro (⟨x,y⟩|⟨x,z,y⟩|⟨x,y,z⟩) <;> by_cases b = x <;> by_cases b = y
              <;> simp_all [Call.pair] <;> try exact instDecidableFalse
            all_goals
              refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_)
              <;> try refine @instDecidableAnd _ _ ?_ ?_
            all_goals try exact instDecMaxOne
            all_goals try exact @instDecidableNot _ instDecEval
            all_goals try apply decEq
            all_goals apply @instDecContribSetTwoEq n σ.length S T ⟨⟨σ,⁻o⟩, rfl⟩ τ
      -- a ≠ b ∧ a = d (Callee, uses invert for caller's contribution)
      · refine @instDecidableAnd _ _ (@instDecidableAnd _ _ (@instDecidableOr _ _ ?_ ?_) ?_) ?_
        · exact @instDecInvertMem n S ⟨σ,⁻o⟩ b e x
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ d x
        · exact @instDecidableNot _ (@instDecEval n S ⟨σ,⁻o⟩ (Form.K d ((x.1, !x.2)@x.1)))
        · refine Decidable.exists_of_list_mem Dist.all_spec (fun T => ?_)
          refine Decidable.exists_of_list_mem (@OSequence.fixLen_all_spec n σ.length) (fun τ => ?_)
          refine @instDecidableAnd _ _ instDecEquiv ?_
          · apply Decidable.exists_of_list_mem Call.all_spec
            rintro (⟨x,y⟩|⟨x,z,y⟩|⟨x,y,z⟩) <;> by_cases b = x <;> by_cases b = y
              <;> simp_all [Call.pair] <;> try exact instDecidableFalse
            all_goals
              refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_)
            all_goals try refine @instDecidableAnd _ _ ?_ ?_
            all_goals try refine @instDecidableAnd _ _ ?_ ?_
            all_goals try exact instDecMaxOne
            all_goals try exact @instDecidableNot _ instDecEval
            all_goals try apply decEq
            all_goals apply @instDecContribSetOneEq n σ.length S T ⟨⟨σ,⁻o⟩, rfl⟩ τ
      -- a ≠ b ∧ a ≠ d (Other)
      · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ a x
    -- sndE
    case sndE b d e =>
      unfold resultSet roleOfIn
      by_cases a = b <;> by_cases a = d <;>
        simp_all only [Classical.not_imp, Set.mem_diff, Set.mem_setOf_eq, Set.mem_union,
          exists_and_left, not_forall, ↓reduceIte]
      -- a = b ∧ a = d (Caller, union has invert on second part)
      · refine @instDecidableAnd _ _ (@instDecidableAnd _ _ (@instDecidableOr _ _ ?_ ?_) ?_) ?_
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ b x
        · exact @instDecInvertMem n S ⟨σ,⁻o⟩ b e x
        · exact @instDecidableNot _ (@instDecEval n S ⟨σ,⁻o⟩ (Form.K b ((x.1, !x.2)@x.1)))
        · refine Decidable.exists_of_list_mem Dist.all_spec (fun T => ?_)
          refine Decidable.exists_of_list_mem (@OSequence.fixLen_all_spec n σ.length) (fun τ => ?_)
          refine @instDecidableAnd _ _ instDecEquiv ?_
          · apply Decidable.exists_of_list_mem Call.all_spec
            rintro (⟨x,y⟩|⟨x,z,y⟩|⟨x,y,z⟩) <;> by_cases b = x <;> by_cases b = y
              <;> simp_all [Call.pair] <;> try exact instDecidableFalse
            all_goals
              refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_)
              <;> try refine @instDecidableAnd _ _ ?_ ?_
            all_goals try exact instDecMaxOne
            all_goals try exact @instDecidableNot _ instDecEval
            all_goals apply @instDecContribSetTwoEq n σ.length S T ⟨⟨σ,⁻o⟩, rfl⟩ τ
      -- a = b ∧ a ≠ d (Caller, invert on callee's contribution)
      · refine @instDecidableAnd _ _ (@instDecidableAnd _ _ (@instDecidableOr _ _ ?_ ?_) ?_) ?_
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ b x
        · exact @instDecInvertMem n S ⟨σ,⁻o⟩ d e x
        · exact @instDecidableNot _ (@instDecEval n S ⟨σ,⁻o⟩ (Form.K b ((x.1, !x.2)@x.1)))
        · refine Decidable.exists_of_list_mem Dist.all_spec (fun T => ?_)
          refine Decidable.exists_of_list_mem (@OSequence.fixLen_all_spec n σ.length) (fun τ => ?_)
          refine @instDecidableAnd _ _ instDecEquiv ?_
          · apply Decidable.exists_of_list_mem Call.all_spec
            rintro (⟨x,y⟩|⟨x,z,y⟩|⟨x,y,z⟩) <;> by_cases b = x <;> by_cases b = y
              <;> simp_all [Call.pair] <;> try exact instDecidableFalse
            all_goals
              refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_)
              <;> try refine @instDecidableAnd _ _ ?_ ?_
            all_goals try exact instDecMaxOne
            all_goals try exact @instDecidableNot _ instDecEval
            all_goals try apply decEq
            all_goals apply @instDecContribSetTwoEq n σ.length S T ⟨⟨σ,⁻o⟩, rfl⟩ τ
      -- a ≠ b ∧ a = d (Callee, no invert)
      · refine @instDecidableAnd _ _ (@instDecidableAnd _ _ (@instDecidableOr _ _ ?_ ?_) ?_) ?_
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ b x
        · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ d x
        · exact @instDecidableNot _ (@instDecEval n S ⟨σ,⁻o⟩ (Form.K d ((x.1, !x.2)@x.1)))
        · refine Decidable.exists_of_list_mem Dist.all_spec (fun T => ?_)
          refine Decidable.exists_of_list_mem (@OSequence.fixLen_all_spec n σ.length) (fun τ => ?_)
          refine @instDecidableAnd _ _ instDecEquiv ?_
          · apply Decidable.exists_of_list_mem Call.all_spec
            rintro (⟨x,y⟩|⟨x,z,y⟩|⟨x,y,z⟩) <;> by_cases b = x <;> by_cases b = y
              <;> simp_all [Call.pair] <;> try exact instDecidableFalse
            all_goals
              refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_)
            all_goals try refine @instDecidableAnd _ _ ?_ ?_
            all_goals try refine @instDecidableAnd _ _ ?_ ?_
            all_goals try exact instDecMaxOne
            all_goals try exact @instDecidableNot _ instDecEval
            all_goals try apply decEq
            all_goals apply @instDecContribSetOneEq n σ.length S T ⟨⟨σ,⁻o⟩, rfl⟩ τ
      -- a ≠ b ∧ a ≠ d (Other)
      · exact @instDecResultSetMem n S ⟨σ,⁻o⟩ a x
termination_by
  (σ.length, 0) -- should be below contribSet
decreasing_by
  all_goals -- Sequence becomes shorter in all cases.
    apply Prod.Lex.left
    simp_all only [OSequence.length_def, OSequence.ofLen_length, List.length_cons]
    omega

/-- Decidability of membership in `invert c (S⌈σ⌉a)`. -/
instance instDecInvertMem {n} {S : @Dist n} {σ : OSequence} {a c : Agent} {x : Value} :
    Decidable (x ∈ invert c (S⌈σ⌉a)) := by
  rw [mem_invert_iff]
  exact instDecResultSetMem
termination_by
  (σ.length, 1)
decreasing_by
  all_goals apply Prod.Lex.right; simp

instance instDecResultSetEq {n k} {S T : @Dist n}
    {σ τ : {σ : @OSequence n // σ.length = k}} {a b}
    : Decidable (S⌈σ⌉a = T⌈τ⌉b) := by
  rw [Set.ext_iff]
  apply Decidable.forall_of_list_mem (@Value.all_spec _)
  intro x
  have := @instDecResultSetMem n S σ a x
  have := @instDecResultSetMem n T τ b x
  exact instDecidableIff
termination_by
  (σ.1.length, 2)
decreasing_by
  · apply Prod.Lex.right; simp
  · simp only [OSequence.ofLen_length]; apply Prod.Lex.right; simp

/-- Decidability of `invert c (S⌈σ⌉a) = T⌈τ⌉b`. -/
instance instDecInvertResultSetEq {n k} {S T : @Dist n}
    {σ τ : {σ : @OSequence n // σ.length = k}} {c : Agent} {a b}
    : Decidable (invert c (S⌈σ⌉a) = T⌈τ⌉b) := by
  rw [Set.ext_iff]
  apply Decidable.forall_of_list_mem (@Value.all_spec _)
  intro x
  have := @instDecInvertMem n S σ a c x
  have := @instDecResultSetMem n T τ b x
  exact instDecidableIff
termination_by
  (σ.1.length, 2)
decreasing_by
  · apply Prod.Lex.right; simp
  · simp only [OSequence.ofLen_length]; apply Prod.Lex.right; simp

/-- Decidability of `S⌈σ⌉a = invert c (T⌈τ⌉b)`. -/
instance instDecResultSetInvertEq {n k} {S T : @Dist n}
    {σ τ : {σ : @OSequence n // σ.length = k}} {c : Agent} {a b}
    : Decidable (S⌈σ⌉a = invert c (T⌈τ⌉b)) := by
  rw [Set.ext_iff]
  apply Decidable.forall_of_list_mem (@Value.all_spec _)
  intro x
  have := @instDecResultSetMem n S σ a x
  have := @instDecInvertMem n T τ b c x
  exact instDecidableIff
termination_by
  (σ.1.length, 2)
decreasing_by
  · apply Prod.Lex.right; simp
  · simp only [OSequence.ofLen_length]; apply Prod.Lex.right; simp

/-- Decidability of `invert c (S⌈σ⌉a) = invert d (T⌈τ⌉b)`. -/
instance instDecInvertInvertEq {n k} {S T : @Dist n}
    {σ τ : {σ : @OSequence n // σ.length = k}} {c d : Agent} {a b}
    : Decidable (invert c (S⌈σ⌉a) = invert d (T⌈τ⌉b)) := by
  rw [Set.ext_iff]
  apply Decidable.forall_of_list_mem (@Value.all_spec _)
  intro x
  have := @instDecInvertMem n S σ a c x
  have := @instDecInvertMem n T τ b d x
  exact instDecidableIff
termination_by
  (σ.1.length, 2)
decreasing_by
  · apply Prod.Lex.right; simp
  · simp only [OSequence.ofLen_length]; apply Prod.Lex.right; simp

instance instDecContribSetOneEq {n k} {S T : @Dist n}
    {σ τ : {σ : @OSequence n // σ.length = k}} {C D}
    : Decidable ((contribSet S σ C).1 = (contribSet T τ D).1) := by
  unfold contribSet
  cases C <;> cases D <;> simp
  · exact @instDecResultSetEq n k S T σ τ _ _
  · exact instDecResultSetInvertEq
  · exact instDecResultSetEq
  · exact instDecInvertResultSetEq
  · exact instDecInvertInvertEq
  · exact instDecInvertResultSetEq
  · exact instDecResultSetEq
  · exact instDecResultSetInvertEq
  · exact instDecResultSetEq
termination_by
  (σ.1.length, 3)
decreasing_by
  all_goals
    apply Prod.Lex.right; simp

instance instDecContribSetTwoEq {n k} {S T : @Dist n}
    {σ τ : {σ : @OSequence n // σ.length = k}} {C D}
    : Decidable ((contribSet S σ.1 C).2 = (contribSet T τ.1 D).2) := by
  unfold contribSet
  cases C <;> cases D <;> simp
  · exact @instDecResultSetEq n k S T σ τ _ _
  · exact instDecResultSetEq
  · exact instDecResultSetInvertEq
  · exact instDecResultSetEq
  · exact instDecResultSetEq
  · exact instDecResultSetInvertEq
  · exact instDecInvertResultSetEq
  · exact instDecInvertResultSetEq
  · exact instDecInvertInvertEq
termination_by
  (σ.1.length, 3)

instance instDecEquiv
    {n k}
    {a : @Agent n}
    {S T : @Dist n}
    {σ τ : {σ : @OSequence n // σ.length = k}}
    : Decidable (equiv a ⟨S,σ⟩ ⟨T,τ⟩) := by
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
        · have := @instDecContribSetTwoEq n (k-1) S T
            ⟨⟨σ,⁻o⟩, by simp at len_σ; rw [← len_σ]; simp⟩
            ⟨⟨τ,⁻o'⟩,by simp at len_τ; rw [← len_τ]; simp⟩
            C D
          exact this
        · apply decEq
      · refine @instDecidableAnd _ _ ?_ ?_
        · have := @instDecContribSetOneEq n (k-1) S T
            ⟨⟨σ,⁻o⟩, by simp at len_σ; rw [← len_σ]; simp⟩
            ⟨⟨τ,⁻o'⟩,by simp at len_τ; rw [← len_τ]; simp⟩
            C D
          exact this
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
  · apply Prod.Lex.right; simp_wf; omega
  · apply Prod.Lex.right; simp_wf
  · apply Prod.Lex.right; simp_wf -- Here we need `resultSet  <  Has i i`.
  · apply Prod.Lex.right; simp_wf
  · apply Prod.Lex.right; simp_wf -- needs `somestuff < K i φ` here?
  · rw [τ.2] -- Here `σ` and `τ` must have the same length.
    apply Prod.Lex.right
    simp_wf

end
