import Gossip.Error.Decide
import Gossip.Error.SemProp

open Error Form Call Role

/-- Just write `1` for an `Agent` that is not `0`. -/
instance : OfNat { b : @Agent (k+2) // b ≠ 0 } 1 := ⟨1, by simp⟩

/-- Just write `2` for a second `Agent` that is not `0`. -/
instance : OfNat { b : @Agent (k+3) // b ≠ 0 } 2 := ⟨⟨2, by simp⟩, by simp⟩

-- After the sequence  01,0^12 (in reverse below!) agent 0
-- has the true value of 2 and the false value of 1.
/--
info: true
-/
#guard_msgs in
#eval
  let S : @Dist 3 := fun _ => true
  let σ : @OSequence 3 := ⟨[ ⌜ 0^1 2 ⌝, ⌜ 0 1 ⌝ ], by simp [maxOne,errFree]⟩
  S⌈σ⌉ ⊧ ((⟨0,true⟩ @ 2) ⋀ (⟨1,false⟩ @ 2))

def claimForm (a b : @Agent n) : @Form n := (K a (b @ b)) ⟹ (b @ a)

def counterExampleForm (a b : @Agent n) : @Form n := (¬'(b @ a)) ⋀ (K a (b @ b))

def validAt {n : Nat} (k : Nat) (φ : @Form n) : Prop :=
  ∀ S, ∀ σ : { σ : @OSequence n // σ.length = k } , S⌈σ.1⌉ ⊧ φ

instance instDecValidAt : Decidable (@validAt n k φ) := by
  unfold validAt
  refine Decidable.forall_of_list_mem Dist.all_spec (fun S => ?_)
  refine Decidable.forall_of_list_mem OSequence.fixLen_all_spec (fun σ => ?_)
  exact instDecEval

/- There are 42 different calls among 3 agents. -/
example : (@Call.all 3).length = 3 * 2 + 3 * 2 * 3 + 3 * 2 * 3 := by decide

-- There are 468 many call sequences of length 2 among 3 agents:
/--
info: 468
-/
#guard_msgs in
#eval (@OSequence.fixLen_all 3 2).length

/--
info: true
-/
#guard_msgs in
#eval @validAt 3 1 $ claimForm (0 : Agent) (1 : Agent)

/-! ## Examples -/

/-- Initial distribution with all values set to true. -/
def ini (n : Nat) : @Dist n := fun _ => true

-- Correct belief need not imply knowledge: given `ini 2`, after an initial call
-- `ab` agent `a` correclty believes `b`, but a does not know the secret of `b`, because `a`
-- also considers it possible that the call was `a b^b` instead.
/--
info: true
-/
#guard_msgs in
#eval
  let a : @Agent 2 := 0
  let b : { b : @Agent 2 // b ≠ a } := ⟨1, by simp [a]⟩
  eval (ini 2) ⟨[ ⌜a b⌝ ], by simp [maxOne]⟩ $
      (    b @ a)  -- a believes b
    ⋀ (¬'(‾b @ a)) -- (and does not believe not-b)
    ⋀ (   b @ b)   -- correctly,
    ⋀ (¬'(Kv a b)) -- but a does not *know* the value of b.

-- FIXME: make it easier to define a state / give a sequence without writing `simp [maxOne]`.

/-- Example that is relevant for new Lemma 2. -/
example:
    let a := 0
    let b := ⟨1, by simp⟩
    let S := ini 3
    let σ := ⟨[⌜a b^b⌝], by simp [maxOne]⟩
    -- Then we have:
    ⟨b,false⟩ ∈ S⌈σ⌉a
    ∧ ⟨b,true⟩ ∉ S⌈σ⌉a
    ∧ ¬ equiv a (S, ⟨σ, rfl⟩) (S.switch b.1, ⟨σ, rfl⟩)
  := by native_decide
