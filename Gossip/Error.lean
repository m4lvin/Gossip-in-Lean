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

def other (i : Agent) : Call → Agent
  | .normal a b => if i = a then b else a
  | .fstE a _ b => if i = a then b else a
  | .sndE a b _ => if i = a then b else a

-- nicer notation to make `Call` values

notation "_(" a ", " b ")" => Call.normal a b
notation "_(" a "^" c "," b ")" => Call.fstE a c b
notation "_(" a ", " b "^" c ")" => Call.sndE a b c

example := _(1^2, 2)

example := [ _(1^2, 2) ]

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
/-- Right after sequence `σ`, what values will caller and callee contribute to the call? -/
def contribSet (σ : Sequence) : Call → Set Value × Set Value
  | .normal a b => (resultSet a σ, resultSet b σ)
  | .fstE a c b => (invert c $ resultSet a σ, resultSet b σ)
  | .sndE a b c => (resultSet a σ, invert c $ resultSet b σ)

/-- Values known by agent `i` after the given sequence. -/
def resultSet (i : Agent) : Sequence → Set Value -- IDEA: better use `Finset` here?
  | [] => { (i, true) } -- initial distribution
  | (C :: σ) =>
    let old := resultSet i σ
    match roleOfIn i C with
      | Caller => old ∪ (contribSet σ C).2 \ {(i, false)}
      | Callee => old ∪ (contribSet σ C).1 \ {(i, false)}
      | Other => old
end

def State : Type := Agent → Set Value -- hmm

/-- The epistemic accessibility relation -/
def equiv : Agent → Sequence → Sequence → Prop
  | _, [], [] => true
  | i, C :: σ, D :: τ => equiv i σ τ
                       ∧ roleOfIn i C = roleOfIn i D
                       -- ∧ resultSet (other i C) σ = resultSet (other i C) τ -- wrong, this would ignore errors
                       ∧ contribSet σ = contribSet τ -- FIXME HMMM ist this correct?
  | _, _, _ => false

def eval : Sequence → Form → Prop
  | _, .Top => True
  | σ, .Neg φ => ¬ eval σ φ
  | σ, .S i (j, k) => (j, k) ∈ resultSet i σ
  | σ, .Con φ ψ => eval σ φ ∧ eval σ ψ
  | σ, .K i φ => ∀ τ, equiv i σ τ → eval τ φ
