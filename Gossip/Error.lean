import Mathlib.Data.Set.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic.Linarith

/-! # Gossip with up to one error -/

/-! ## Basics

Here we define: agents, values, calls, sequents.
-/

abbrev Agent := Nat -- FIXME use `Fin n`

abbrev Value := (Agent × Bool)

abbrev Holding := Set Value

inductive Call : Type
  | normal : (caller : Agent) → (callee : Agent) → Call -- a b
  | fstE : (caller : Agent) → (err : Agent) → (callee : Agent) → Call -- a^c b
  | sndE : (caller : Agent) → (callee : Agent) → (err : Agent) → Call -- a b^c

-- TODO: nice notation for `Call` values

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
  | S _ _ => 4 -- hmm
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
def resultSet : Agent → Sequence → Set Value
  | i, [] => { (i, true) } -- initial distribution
  | i, (C :: σ) =>
    let old := resultSet i σ
    let knownWrongBy k : Set Value := fun v => -- this is * in the paper
      match v with
        | ⟨j,true ⟩ => eval σ (K k (S j (j,false)))
        | ⟨j,false⟩ => eval σ (K k (S j (j,true )))
    match C, roleOfIn i C with
      -- Not involved:
      | _, Other => old
      -- Normal calls:
      | .normal a b, Caller => (resultSet a σ) ∪ (resultSet b σ \ knownWrongBy b)
      | .normal a b, Callee => (resultSet a σ \ knownWrongBy a) ∪ (resultSet b σ)
      -- transmission error by a:
      | .fstE a c b, Caller => (resultSet a σ) ∪ (resultSet b σ \ knownWrongBy b) -- no self-error!
      | .fstE a c b, Callee => (invert c $ resultSet a σ \ knownWrongBy a) ∪ (resultSet b σ)
      -- transmission error by b:
      | .sndE a b c, Caller => (resultSet a σ) ∪ (invert c $ resultSet b σ \ knownWrongBy b)
      | .sndE a b c, Callee => (resultSet a σ \ knownWrongBy a) ∪ (resultSet b σ) -- no self-error!
termination_by
  i σ => (3, σ.length) -- Here we need resultSet a formula, value must be larger than `K k (S j j)`.
decreasing_by
  · apply Prod.Lex.right; simp
  · simp -- Here we need `K k (S j j)  <  resultSet`
    -- apply Prod.Lex.left; simp
    sorry
  · sorry -- same problem
  all_goals
    try (apply Prod.Lex.right; simp) -- sequence becomes shorter in all recursive calls!

/-- Right after sequence `σ`, what values will caller and callee contribute to the call? -/
def contribSet (σ : Sequence) : Call → Set Value × Set Value
  | .normal a b => (resultSet a σ, resultSet b σ)
  | .fstE a c b => (invert c $ resultSet a σ, resultSet b σ)
  | .sndE a b c => (resultSet a σ, invert c $ resultSet b σ)
termination_by
  c => (4, σ.length)
decreasing_by
  -- Here we need `resultSet  <  contribSet`
  all_goals
    apply Prod.Lex.left; simp

/-- (Def 5) The epistemic accessibility relation ∼ₐ

>>> TODO TODO this still needs to be made asynchronous <<<
Then it will call `contribSet` on sequences of arbitrary length.
Or should the recursion-order label then be σ.length + τ.length ?
-/
def equiv : Agent → Sequence → Sequence → Prop
  | _, [], [] => true
  | i, C :: σ, D :: τ => equiv i σ τ
                       ∧ roleOfIn i C = roleOfIn i D
                       -- Using `resultSet (other i C) σ = resultSet (other i C) τ` here would
                       -- be wrong because it would ignore errors. Hence we need `contribSet`.
                       -- The following is still entirely correct, we should not care about i's contrib!
                       -- FIXME
                       ∧ contribSet σ = contribSet τ
  | _, _, _ => false
termination_by
  i σ τ => (5, σ.length) -- no formula here, should be above contribSet
decreasing_by
  · apply Prod.Lex.right; simp
  · sorry -- Here we need `contribSet < equiv`
  · sorry -- Here we need `contribSet < equiv`

/-- (Def 6) Semantics -/
def eval : Sequence → Form → Prop
  | _, .Top => True
  | σ, .Neg φ => ¬ eval σ φ
  | σ, .S i (j, k) => (j, k) ∈ resultSet i σ
  | σ, .Con φ ψ => eval σ φ ∧ eval σ ψ
  | σ, .K i φ => ∀ τ, equiv i σ τ → eval τ φ
termination_by
  σ φ => (φ.length, σ.length)
decreasing_by
  -- formula becomes simpler in all cases!
  · apply Prod.Lex.left; simp
  · apply Prod.Lex.left; simp -- Here we need `resultSet  <  S i i`
  · apply Prod.Lex.left; simp; linarith
  · apply Prod.Lex.left; simp
  · apply Prod.Lex.left; simp; sorry -- Here we need `equiv  <  K i φ`
  · apply Prod.Lex.left; simp

end
