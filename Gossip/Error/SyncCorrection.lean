import Mathlib.Data.Set.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic.Linarith

/-! # Synchronous One-Error Gossip with Correction -/

/-! ## Basics

Here we define: agents, values, calls, sequents.
-/

abbrev Agent := Nat -- IDEA use `Fin n`

abbrev Value := (Agent × Bool)

abbrev State : Type := Agent → Set Value

/-- Every agent only has their own value. -/
def isInitial (s : State) : Prop := ∀ a, s a = { ⟨a,True⟩ } ∨ s a = { ⟨a,False⟩ }

inductive Call : Type
  | normal : (caller : Agent) → (callee : Agent) → Call -- a b
  | fstE : (caller : Agent) → (err : Agent) → (callee : Agent) → Call -- a^c b
  | sndE : (caller : Agent) → (callee : Agent) → (err : Agent) → Call -- a b^c

-- IDEA nice notation for `Call` values

instance instMembershipAgentCall : Membership Agent Call := .mk $ fun c i => match c with
  | .normal a b => i = a ∨ i = b
  | .fstE a _ b => i = a ∨ i = b
  | .sndE a b _ => i = a ∨ i = b

instance {a : Agent} {c : Call} : Decidable (a ∈ c) := by
  rcases c with (⟨d,e⟩|⟨d,_,e⟩|⟨d,e,_⟩) <;> by_cases a = d <;> by_cases a = e
  all_goals
    simp_all [instMembershipAgentCall]
    try exact instDecidableTrue
    try exact instDecidableFalse

/-- History of calls in reverse order, newest call is the first element. -/
abbrev Sequence : Type := List Call

/-- Flip the value of the secret of this agent in the given set. -/
def invert : Agent -> Set Value -> Set Value
  | i, vs => vs.image (fun (j,b) => if j = i then (j, not b) else (j,b))

/-! ## Syntax -/

inductive Form : Type
  | Top : Form
  | Con : Form → Form → Form
  | Neg : Form → Form
  | S : Agent → (Agent × Bool) → Form -- S a (b, k) means a has value k of b
  | K : Agent → Form → Form

@[simp]
def Form.length : Form → Nat
  | Top => 0
  | Con φ1 φ2 => 1 + φ1.length + φ2.length
  | Neg φ => 1 + φ.length
  | S _ _ => 1
  | K _ φ => 1 + φ.length

open Form

inductive Role : Type
  | Caller : Role
  | Callee : Role
  | Other : Role

open Role

def roleOfIn (i : Agent) : (c : Call) → Role
  | .normal a b => if i = a then Caller else if i = b then Callee else Other
  | .fstE a _ b => if i = a then Caller else if i = b then Callee else Other
  | .sndE a b _ => if i = a then Caller else if i = b then Callee else Other

/-! ## Semantics -/

mutual

/-- (Def 4) Call Semantics

What values does this agent have after this sequence? -/
def resultSet : Agent → State → Sequence → Set Value
  | i, s, [] => s i -- initial distribution is given by the state
  | i, s, (C :: σ) =>
    let old := resultSet i s σ
    let knownWrongBy k : Set Value := fun v => -- this is * in the paper
      match v with
        | ⟨j,true ⟩ => eval s σ (K k (S j (j,false)))
        | ⟨j,false⟩ => eval s σ (K k (S j (j,true )))
    match C, roleOfIn i C with
      -- Not involved:
      | _, Other => old
      -- Normal calls:
      | .normal a b, Caller => (resultSet a s σ) ∪ (resultSet b s σ \ knownWrongBy b)
      | .normal a b, Callee => (resultSet a s σ \ knownWrongBy a) ∪ (resultSet b s σ)
      -- transmission error by a:
      | .fstE a _ b, Caller => (resultSet a s σ) ∪ (resultSet b s σ \ knownWrongBy b) -- no self-error!
      | .fstE a c b, Callee => (invert c $ resultSet a s σ \ knownWrongBy a) ∪ (resultSet b s σ)
      -- transmission error by b:
      | .sndE a b c, Caller => (resultSet a s σ) ∪ (invert c $ resultSet b s σ \ knownWrongBy b)
      | .sndE a b _, Callee => (resultSet a s σ \ knownWrongBy a) ∪ (resultSet b s σ) -- no self-error!
termination_by
  _ _  σ => (σ.length, 0) -- should be below contribSet
decreasing_by
  all_goals
    apply Prod.Lex.left; simp -- sequence becomes shorter in all recursive calls!

/-- Right after sequence `σ`, what values will caller and callee contribute to the call? -/
def contribSet (s : State) (σ : Sequence) : Call → Set Value × Set Value
  | .normal a b => (resultSet a s σ, resultSet b s σ)
  | .fstE a c b => (invert c $ resultSet a s σ, resultSet b s σ)
  | .sndE a b c => (resultSet a s σ, invert c $ resultSet b s σ)
termination_by
  _ => (σ.length, 1) -- should be above resultSet
decreasing_by
  all_goals
    apply Prod.Lex.right; simp

/-- (Def 5) The *synchronous* epistemic accessibility relation ≈ₐ -/
def equiv {k} : Agent → (State × {σ : Sequence // σ.length = k}) → (State × {σ : Sequence // σ.length = k}) → Prop
  | i, (s1, ⟨[],_⟩), (s2, ⟨[],_⟩) => isInitial s1 ∧ isInitial s2 ∧ s1 i = s2 i
  | i, (s1, ⟨C :: σ,_⟩), (s2, ⟨D :: τ,_⟩) =>
                          @equiv (k-1) i (s1,⟨σ, by aesop⟩) (s2,⟨τ, by aesop⟩)
                        ∧ roleOfIn i C = roleOfIn i D
                        -- Depending on the role, observe the contribSet of the other agent in the call:
                        ∧ match roleOfIn i C with
                          | Other => True
                          | Caller => (contribSet s1 σ C).2 = (contribSet s2 τ D).2
                          | Callee => (contribSet s1 σ C).1 = (contribSet s2 τ D).1

termination_by
  _ s1σ _ => (s1σ.2.1.length, 0) -- should be above contribSet
decreasing_by
  · apply Prod.Lex.left; simp
  · apply Prod.Lex.left; simp
  all_goals
    apply Prod.Lex.left
    have : σ.length = τ.length := by aesop
    aesop

/-- (Def 6) Semantics -/
def eval : State → Sequence → Form → Prop
  | _, _, .Top => True
  | s, σ, .Neg φ => ¬ eval s σ φ
  | s, σ, .S i (j, k) =>
      if i == j
      then (j, k) ∈ s i -- Here we hard-code stubbornness :-)
      else (j, k) ∈ resultSet i s σ
  | s, σ, .Con φ ψ => eval s σ φ ∧ eval s σ ψ
  | s, σ, .K i φ => ∀ t, ∀ τ , (he : equiv i (s,⟨σ,rfl⟩) (t,τ)) → eval t τ φ
termination_by
  _ σ φ => (σ.length, φ.length)
decreasing_by -- Sequence (length) stays the same, but formula becomes simpler in all cases.
  · apply Prod.Lex.right; simp
  · apply Prod.Lex.right; simp -- Here we need `resultSet  <  S i i`
  · apply Prod.Lex.right; simp; linarith
  · apply Prod.Lex.right; simp
  · apply Prod.Lex.right; simp -- Here we need `equiv  <  K i φ`
  · rw [τ.2] -- The trick!
    apply Prod.Lex.right
    simp_wf

end
