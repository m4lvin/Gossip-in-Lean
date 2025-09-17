import Mathlib.Data.Set.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic.Linarith

/-! # Synchronous One-Error Gossip with Correction -/

/-! ## Basics

Here we define: agents, values, calls, sequents.
-/

abbrev Agent := Nat -- IDEA use `Fin n` with `variable {n : Nat}` later

abbrev Value := (Agent × Bool) -- using Bool instead of 0 and 1

-- We allow to write "a" for "(a, 1)", meaning NOT "(a, 0)" as in paper at the moment.
instance : Coe Agent Value := ⟨fun a => ⟨a,true⟩⟩

/-- (Def 1) Secret distribution -/
abbrev Dist := Agent → Set Value

/-- Every agent only has their own value. -/
def isInitial (ι : Dist) :=
  ∀ a, ι a = { ⟨a,True⟩ } ∨ ι a = { ⟨a,False⟩ }

inductive Call : Type
  | normal : (caller : Agent) → (callee : Agent) → Call -- a b
  | fstE : (caller : Agent) → (err : Agent) → (callee : Agent) → Call -- a^c b
  | sndE : (caller : Agent) → (callee : Agent) → (err : Agent) → Call -- a b^c

-- Nicer notation for `Call`
notation "⌜" a:arg  b:arg "⌝" => Call.normal a b
notation "⌜" a:arg "^" c:arg b:arg "⌝" => Call.fstE a c b
notation "⌜"  a:arg b:arg "^" c:arg "⌝" => Call.sndE a b c

/-- The pair of agents in the call, ignoring whether an error is made. -/
def Call.pair : Call → (Agent × Agent)
  | ⌜ a   b   ⌝ => (a , b)
  | ⌜ a^_ b   ⌝ => (a , b)
  | ⌜ a   b^_ ⌝ => (a , b)

instance instMembershipAgentCall : Membership Agent Call := .mk $ fun c i => match c with
  | ⌜ a   b   ⌝ => i = a ∨ i = b
  | ⌜ a^_ b   ⌝ => i = a ∨ i = b
  | ⌜ a   b^_ ⌝ => i = a ∨ i = b

instance {a : Agent} {c : Call} : Decidable (a ∈ c) := by
  rcases c with (⟨d,e⟩|⟨d,_,e⟩|⟨d,e,_⟩) <;> by_cases a = d <;> by_cases a = e
  all_goals
    simp_all [instMembershipAgentCall]
    try exact instDecidableTrue
    try exact instDecidableFalse

/-- (Def 2) Call sequence.
For easier pattern matching this is in *reverse* order, i.e. the newest call is the first element. -/
abbrev Sequence : Type := List Call

/-- Subsequence relation: τ extends σ.
Because the lists are with the newest call first, this can be defined as saying that σ is a suffix of tau. -/
notation σ:arg "⊑" τ:arg => σ <:+ τ

/-- Flip the value of the secret of this agent in the given set. -/
def invert : Agent -> Set Value -> Set Value
  | i, vs => vs.image (fun (j,b) => if j = i then (j, not b) else (j,b))

/-! ## Syntax -/

/-- (Def 3) Logical language -/
inductive Form : Type
  | Top : Form -- ⊤
  | Con : Form → Form → Form -- ∧
  | Neg : Form → Form -- ¬
  | S : (a : Agent) → (Agent × Bool) → Form -- S a (b, k) means agent a has value k of agent b
  | K : (a : Agent) → (φ : Form) → Form -- knowing that

open Form

notation "¬'" φ:arg => Neg φ
notation φ1:arg "⋀" φ2:arg => Con φ1 φ2
notation φ1:arg "⋁" φ2:arg => Neg (Con (Neg φ1) (Neg φ2))
notation φ1:arg "⟹" φ2:arg => (Neg φ1) ⋁ φ2

notation "Kv" a:arg b:arg => (K a (S b b)) ⋁ (K a (S b (b,false)))

@[simp]
def Form.length : Form → Nat
  | Top => 0
  | Con φ1 φ2 => 1 + φ1.length + φ2.length
  | Neg φ => 1 + φ.length
  | S _ _ => 1
  | K _ φ => 1 + φ.length

inductive Role : Type
  | Caller : Role
  | Callee : Role
  | Other : Role
deriving DecidableEq

open Role

def roleOfIn (i : Agent) : (c : Call) → Role
  | ⌜ a   b   ⌝ => if i = a then Caller else if i = b then Callee else Other
  | ⌜ a^_ b   ⌝ => if i = a then Caller else if i = b then Callee else Other
  | ⌜ a   b^_ ⌝ => if i = a then Caller else if i = b then Callee else Other

@[simp]
lemma roleOfIn_a : roleOfIn a ⌜ a b ⌝ = Caller := by simp [roleOfIn]
lemma roleOfIn_eq_Caller_iff : roleOfIn a ⌜ x y ⌝ = Caller ↔ a = x := by simp [roleOfIn]; grind
lemma roleOfIn_eq_Callee_iff : roleOfIn a ⌜ x y ⌝ = Callee ↔ a ≠ x ∧ a = y := by simp [roleOfIn]; grind
lemma roleOfIn_eq_Other_iff : roleOfIn a ⌜ x y ⌝ = Other ↔ a ≠ x ∧ a ≠ y := by simp [roleOfIn]; grind

/- TODO same lemmas for error calls?
  | ⌜ a^_ b   ⌝ => if i = a then Caller else if i = b then Callee else Other
  | ⌜ a   b^_ ⌝ => if i = a then Caller else if i = b then Callee else Other
-/



/-! ## Semantics -/

mutual

/-- (Def 4) Semantics of call.
What values does this agent have after this sequence? -/
def resultSet (a : Agent) : Dist → Sequence → Set Value
  | ι, [] => ι a -- for the basis, ι[ε] = ι
  | ι, (C :: σ) =>
    let old := resultSet a ι σ
    let knownIncorrect k : Set Value := fun v => -- the set *
      match v with
        | ⟨j,true ⟩ => eval ι σ (K k (S j (j,false)))
        | ⟨j,false⟩ => eval ι σ (K k (S j (j,true )))
    match C, roleOfIn a C with
      -- Not involved:
      | _, Other => old
      -- Normal calls:
      | ⌜ a b ⌝, Caller => (resultSet a ι σ) ∪ (resultSet b ι σ \ knownIncorrect b)
      | ⌜ a b ⌝, Callee => (resultSet a ι σ \ knownIncorrect a) ∪ (resultSet b ι σ)
      -- error from a:
      | ⌜ a^_ b ⌝, Caller => (resultSet a ι σ) ∪ (resultSet b ι σ \ knownIncorrect b) -- no self-error!
      | ⌜ a^c b ⌝, Callee => (invert c $ resultSet a ι σ \ knownIncorrect a) ∪ (resultSet b ι σ)
      -- error from b:
      | ⌜ a b^c ⌝, Caller => (resultSet a ι σ) ∪ (invert c $ resultSet b ι σ \ knownIncorrect b)
      | ⌜ a b^_ ⌝, Callee => (resultSet a ι σ \ knownIncorrect a) ∪ (resultSet b ι σ) -- no self-error!
termination_by
  _ σ => (σ.length, 0) -- should be below contribSet
decreasing_by
  all_goals
    apply Prod.Lex.left; simp -- sequence becomes shorter in all recursive calls!

/-- Right after sequence `σ`, what values will caller and callee contribute to the call? -/
def contribSet (ι : Dist) (σ : Sequence) : Call → Set Value × Set Value
  | ⌜ a   b   ⌝ => (resultSet a ι σ           ,            resultSet b ι σ)
  | ⌜ a^c b   ⌝ => (invert c $ resultSet a ι σ,            resultSet b ι σ)
  | ⌜ a   b^c ⌝ => (resultSet a ι σ           , invert c $ resultSet b ι σ)
termination_by
  _ => (σ.length, 1) -- should be above resultSet
decreasing_by
  all_goals
    apply Prod.Lex.right; simp

/-- (Def 5) Observation relation.
This is *synchronous*. -/
def equiv {k} (a : Agent) : (Dist × {σ : Sequence // σ.length = k}) → (Dist × {σ : Sequence // σ.length = k}) → Prop
  | (ι, ⟨[]    ,_⟩), (ι', ⟨[]    ,_⟩) => isInitial ι ∧ isInitial ι' ∧ ι a = ι' a
  | (ι, ⟨C :: σ,_⟩), (ι', ⟨D :: τ,_⟩) =>
                          @equiv (k-1) a (ι,⟨σ, by aesop⟩) (ι',⟨τ, by aesop⟩)
                        ∧ roleOfIn a C = roleOfIn a D
                        -- Depending on the role, observe who is in the call and the contribSet of the other
                        ∧ match roleOfIn a C with
                          | Other => True
                          | Caller => (contribSet ι σ C).2 = (contribSet ι' τ D).2 ∧ C.pair = D.pair
                          | Callee => (contribSet ι σ C).1 = (contribSet ι' τ D).1 ∧ C.pair = D.pair

termination_by
  ισ _ => (ισ.2.1.length, 0) -- should be above contribSet
decreasing_by
  · apply Prod.Lex.left; simp
  · apply Prod.Lex.left; simp
  all_goals
    apply Prod.Lex.left
    have : σ.length = τ.length := by aesop
    aesop

/-- (Def 6) Semantics. -/
def eval : Dist → Sequence → Form → Prop
  | _, _, .Top => True
  | ι, σ, .Neg φ => ¬ eval ι σ φ
  | ι, σ, .S a (j, k) =>
      if a == j
      then (j, k) ∈ ι a -- Here we hard-code stubbornness :-)
      else (j, k) ∈ resultSet a ι σ
  | ι, σ, .Con φ ψ => eval ι σ φ ∧ eval ι σ ψ
  | ι, σ, .K a φ => ∀ t, ∀ τ , (he : equiv a (ι,⟨σ,rfl⟩) (t,τ)) → eval t τ φ
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

notation ι:arg "⌈" σ:arg "⌉" a:arg => resultSet a ι σ

/-- An abbreviation to easily say that we have the same length and (can thus say) `equiv`. -/
def equi (a : Agent) (ισ : Dist × Sequence) (ι'τ : Dist × Sequence) : Prop :=
  ∃ h : ισ.2.length = ι'τ.2.length, equiv a ⟨ισ.1, ⟨ισ.2, rfl⟩⟩ ⟨ι'τ.1, ⟨ι'τ.2, h.symm⟩⟩

notation ισ:arg " ~_ " a:arg ι'τ:arg => equi a ισ ι'τ

notation ισ "⊧" φ => eval ισ.1 ισ.2 φ

/-- Validity of formulas -/
def valid (φ : Form) := ∀ ι σ, eval ι σ φ
prefix:100 "⊨" => valid -- FIXME what's a good precedence value here?

lemma same_set_then_know_same (same_set : ι⌈σ'⌉b = ι'⌈τ'⌉b) :
    eval ι' τ' (K b (S a (a, v))) ↔ eval ι σ' (K b (S a (a, v))) := by
  sorry


/-- Lemma 7 -/
lemma indistinguishable_then_same_values {ι ι': Dist} {σ τ : Sequence} :
    (ι, σ) ~_a (ι', τ)  →  ι⌈σ⌉a = ι'⌈τ⌉a := by
  intro ⟨same_len, equ⟩
  simp at same_len
  induction σ generalizing τ
  case nil =>
    have := List.length_eq_zero_iff.mp same_len.symm
    subst this
    simp_all [resultSet, equiv]
  case cons κ σ' IH =>
    simp at same_len
    rcases List.exists_cons_of_length_eq_add_one same_len.symm with ⟨κ', τ', τ_def⟩
    subst (τ_def : τ = κ' :: τ')
    simp only [List.length_cons, equiv, Nat.add_one_sub_one] at equ
    specialize IH (by grind) equ.1 -- IH now says `ι⌈σ'⌉a = ι'⌈τ'⌉a`
    -- distinguish cases whether a is involved in κ (and this also κ') or not
    cases r : roleOfIn a κ
    case Caller =>
      simp [r] at equ
      rcases equ with ⟨prev_equ, Caller_eq, prev_same_contrib, same_pair⟩
      unfold contribSet at prev_same_contrib
      cases κ <;> cases κ' <;> simp at * -- 6 cases should drop out here?
      case normal.normal a_ b a__ b__ =>
        rw [roleOfIn_eq_Caller_iff] at r
        subst r
        rw [Eq.comm, roleOfIn_eq_Caller_iff] at Caller_eq
        subst Caller_eq
        simp [Call.pair] at same_pair
        subst same_pair
        simp at same_len
        unfold resultSet
        simp
        ext x
        simp
        constructor
        · intro hyp; convert hyp using 2
          · aesop
          · aesop
          · rcases x with ⟨v,b⟩
            cases b <;> simp [Set.instMembership, Set.Mem]
            all_goals
              rw [same_set_then_know_same]; tauto
        · intro hyp; convert hyp using 2
          · aesop
          · rcases x with ⟨v,b⟩
            cases b <;> simp [Set.instMembership, Set.Mem]
            all_goals
              rw [same_set_then_know_same]; tauto
      all_goals
        -- 8 more cases ... can we do this in a more general helper lemma?
        sorry
    case Callee =>
      sorry
    case Other =>
      sorry

/-- Lemma 8. Note that `v` here says whether we have b or \overline{b}. -/
lemma local_is_known {a b : Agent} (v : Bool) :
      ⊨ ((S a ⟨b,v⟩) ⟹ (K a (S a ⟨b,v⟩)))
    ∧ ⊨ ((Neg (S a ⟨b,true⟩)) ⟹ (K a (S a ⟨b,true⟩)))
    := by
  sorry

/-- Lemma 9 -/
lemma knowledge_of_secrets_is_preserved {a b : Agent} {v : Bool} :
    ((ι,σ) ⊧ Kv a b)
    ∧
    (σ ⊑ τ)
    →
    ((ι,σ) ⊧ Kv a b)
    := by
  sorry

/-- Lemma 10 -/
lemma know_your_own : ⊨ Kv a a := by
  sorry

/-!

Still to do:

/-- Lemma 11 -/

/-- Corollary 12 -/

/-- Corollary 13 -/

Examples?

/-- Proposition 17, 18 and 19 maybe too hard? -/

-/
