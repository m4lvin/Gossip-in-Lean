import Gossip.Error.Decide
import Gossip.Error.SemProp

open Error Form Call Role

example :
  let S : @Dist 3 := fun _ => true
  let σ : @OSequence 3 := ⟨[], by simp⟩
  S⌈σ⌉ ⊧ .Top := by
    -- decide -- mmwah?!
    sorry

#eval
  let S : @Dist 3 := fun _ => true
  let σ : @OSequence 3 := ⟨[ ⌜ 0 1^1 ⌝ ], by simp [maxOne]⟩
  S⌈σ⌉ ⊧ (⟨1,true⟩ @ 0)

def goalForm (a b : @Agent n) : @Form n :=
      (¬'(b @ a)) ⋀ (K a (b @ b))

def validAt {n : Nat} (k : Nat) (φ : @Form n) : Prop :=
  ∀ S, ∀ σ : { σ : @OSequence n // σ.length = k } , S⌈σ.1⌉ ⊧ φ

instance instDecValidAt : Decidable (@validAt n k φ) := by
  unfold validAt
  refine Decidable.forall_of_list_mem Dist.all_spec (fun S => ?_)
  refine Decidable.forall_of_list_mem OSequence.fixLen_all_spec (fun σ => ?_)
  exact instDecEval

-- #eval (@Call.all 3).length
-- #eval (3 * 3) + (3* 3 * 3) + (3* 3 * 3)

-- #eval
--   (@OSequence.fixLen_all 3 1).length

-- #eval
--   @validAt 3 2 (¬' goalForm 0 1)

/-! ## Examples -/

/-- Initial distribution with all values set to true. -/
def ini (n : Nat) : @Dist n := fun _ => true

#eval
  let a : @Agent 2 := 0
  let b : @Agent 2 := 1
  eval (ini 2) ⟨[ ⌜a b⌝ ], by simp [maxOne]⟩ $
      (    b @ a)  -- a believes b
    ⋀ (¬'(‾b @ a)) -- (and does not believe not-b)
    ⋀ (   b @ b)   -- correctly,
    ⋀ (¬'(Kv a b)) -- but a does not *know* the value of b.

-- FIXME: make it easier to define a state / give a sequence without writing `simp [maxOne]`.

/-- Correct belief need not imply knowledge: given `ini 2`, after an initial call
`ab` agent `a` correclty believes `b`, but a does not know the secret of `b`, because `a`
also considers it possible that the call was `a b^b` instead. -/
lemma example_correct_belief_does_not_imply_knowledege (a b : Agent) (h : a ≠ b) :
    eval (ini 2) ⟨[ ⌜a b⌝ ], by simp [maxOne]⟩ $
      (    b @ a)  -- a believes b
    ⋀ (¬'(‾b @ a)) -- (and does not believe not-b)
    ⋀ (   b @ b)   -- correctly,
    ⋀ (¬'(Kv a b)) -- but a does not *know* the value of b.
    := by
  unfold ini
  unfold eval
  constructor
  · simp [eval, resultSet, contribSet]
    constructor
    · use ini 2
      unfold ini
      simp only [and_true]
      use ⟨[], maxOne_nil⟩
      simp
    · refine ⟨_, _, ⟨ ⟨ ?_, equiv_refl⟩ , ?_ ⟩  ⟩ <;> simp
      use ⌜a b⌝
      simp [contribSet, maxOne]
  · unfold eval
    constructor
    · simp [eval, resultSet, contribSet]
    · simp_all [eval]
      use (ini 2).switch b
      simp only [Dist.switch, ini, Bool.not_true, Bool.if_true_right, Bool.or_false, ↓reduceIte,
        true_and]
      constructor
      · use ⟨[⌜a b^b⌝], by simp [maxOne]⟩
        simp_all [equiv, roleOfIn, contribSet, invert, Call.pair]
      · use ini 2
        simp only [ini, and_true]
        use ⟨[⌜a b⌝], by simp [maxOne]⟩
        simp_all [equiv, roleOfIn, contribSet, Call.pair, ini]
