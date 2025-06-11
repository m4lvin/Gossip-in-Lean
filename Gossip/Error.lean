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
abbrev Sequent : Type := List Call

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

/-- Values known by agent i after the given sequent. -/
def resultSet : Agent → Sequent → Set Value
  | i, [] => { (i, true) } -- initial distribution
  | i, (C :: σ) =>
    let old := resultSet i σ
    let knownWrongBy k : Set Value := fun v =>
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
  i σ => (σ.length, 0)
decreasing_by
  all_goals
    apply Prod.Lex.left; simp -- sequence becomes shorter in all recursive calls!

/-- The epistemic accessibility relation -/
def equiv : Agent → Sequent → Sequent → Prop
  | u, σ, τ => sorry -- this will call `resultSet`

def eval : Sequent → Form → Prop
  | _, .Top => True
  | σ, .Neg φ => ¬ eval σ φ
  | σ, .S i (j, k) => (j, k) ∈ resultSet i σ
  | σ, .Con φ ψ => eval σ φ ∧ eval σ ψ
  | σ, .K i φ => ∀ τ, equiv i σ τ → eval τ φ
termination_by
  σ φ => (σ.length, sizeOf φ)
decreasing_by
  · apply Prod.Lex.right; simp -- formula becomes simpler in these cases
  · apply Prod.Lex.right; simp
  · apply Prod.Lex.right; simp; linarith
  · apply Prod.Lex.right; simp
  · sorry -- PROBLEM: clause for K goes to longer/arbitrary sequences !
end
