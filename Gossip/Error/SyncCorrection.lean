import Mathlib.Data.Set.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic.DepRewrite
import Mathlib.Tactic.Linarith

namespace Error

/-! # Synchronous One-Error Gossip with Correction -/

/-! ## Basics

Here we define: agents, values, distributions, calls, sequents.

We use `n` for the number of agents.
-/
variable {n : Nat}

abbrev Agent : Type := Fin n

abbrev Value : Type := (@Agent n × Bool)

/-- We allow writing just the agent `a` for the value `⟨a, true⟩`. -/
instance : Coe (@Agent n) (@Value n) := ⟨fun a => ⟨a,true⟩⟩

set_option quotPrecheck false in
/-- We write `‾a` for the value `⟨a, false⟩`. -/
notation "‾" a:arg => ⟨a, false⟩

/-- An *initial* secret distribution, each agent only has their own value. -/
abbrev Dist := @Agent n → Bool

/-- In the given distribution, invert the value for this agent i -/
def Dist.switch : @Agent n -> @Dist n -> @Dist n
  | i, ι => fun a => if a = i then not (ι a) else ι a

inductive Call : Type
  | normal : (caller : @Agent n) → (callee : @Agent n) → Call -- a b
  | fstE : (caller : @Agent n) → (err : @Agent n) → (callee : @Agent n) → Call -- a^c b
  | sndE : (caller : @Agent n) → (callee : @Agent n) → (err : @Agent n) → Call -- a b^c

-- Nicer notation for `Call`
notation "⌜" a:arg  b:arg "⌝" => Call.normal a b
notation "⌜" a:arg "^" c:arg b:arg "⌝" => Call.fstE a c b
notation "⌜"  a:arg b:arg "^" c:arg "⌝" => Call.sndE a b c

/-- The pair of agents in the call, ignoring whether an error is made. -/
def Call.pair : @Call n → (@Agent n × @Agent n)
  | ⌜ a   b   ⌝ => (a , b)
  | ⌜ a^_ b   ⌝ => (a , b)
  | ⌜ a   b^_ ⌝ => (a , b)

/-- (Def 2) A sequence is a list of calls.
For easy pattern matching this is in *reverse* order: the newest call is the first element. -/
abbrev Sequence : Type := List (@Call n)

/-- Flip the value of the secret of this agent in the given set. -/
def invert : @Agent n -> Set (@Value n) -> Set (@Value n)
  | i, vs => vs.image (fun (j,b) => if j = i then (j, not b) else (j,b))

/-! ## Syntax -/

/-- (Def 3) Logical language -/
inductive Form : Type
  /-- True constant -/
  | Top : Form -- ⊤
  /-- Conjunction -/
  | Con : Form → Form → Form
  /-- Negation -/
  | Neg : Form → Form
  /-- `B a (b, k)` means agent `a` has value `k` of agent `b`. -/
  | Has : (a : @Agent n) → (@Value n) → Form
  /-- `K a φ` means agent `a` knows that `φ` is true. -/
  | K : (a : @Agent n) → (φ : Form) → Form

open Form

notation " ¬'" φ:arg => Neg φ

infixr:60 " ⋀ " => Con

notation φ1:arg " ⋁ " φ2:arg => Neg (Con (Neg φ1) (Neg φ2))
notation φ1:arg "⟹" φ2:arg => (Neg φ1) ⋁ φ2
notation φ1:(arg-1) " ⇔ " φ2:(arg-1) => Con (φ1 ⟹ φ2) (φ2 ⟹ φ1)

/-- We write `v @ a` to say that agent `a` has value `v`. -/
notation v:(arg-1) "@" a:arg => Has a v

notation "Kv" a:arg b:arg => (K a (b @ b)) ⋁ (K a (‾b @ b))

@[simp]
def Form.length : @Form n → Nat
  | Top => 0
  | Con φ1 φ2 => 1 + φ1.length + φ2.length
  | Neg φ => 1 + φ.length
  | Has _ _ => 1
  | K _ φ => 1 + φ.length

/-! ## Roles -/

inductive Role : Type
  | Caller : Role
  | Callee : Role
  /-- Not participating in the call -/
  | Other : Role
deriving DecidableEq

open Role

/-- What is the `Role` of `i` in this call? -/
def roleOfIn (i : @Agent n) : (c : @Call n) → Role
  | ⌜ a   b   ⌝ => if i = a then Caller else if i = b then Callee else Other
  | ⌜ a^_ b   ⌝ => if i = a then Caller else if i = b then Callee else Other
  | ⌜ a   b^_ ⌝ => if i = a then Caller else if i = b then Callee else Other

@[simp]
lemma roleOfIn_a : roleOfIn a ⌜ a b ⌝ = Caller := by simp [roleOfIn]

@[simp]
lemma roleOfIn_eq_Caller_iff : roleOfIn a ⌜ x y ⌝ = Caller ↔ a = x := by simp [roleOfIn]; grind
@[simp]
lemma roleOfIn_eq_Callee_iff : roleOfIn a ⌜ x y ⌝ = Callee ↔ a ≠ x ∧ a = y := by simp [roleOfIn]; grind
@[simp]
lemma roleOfIn_eq_Other_iff : roleOfIn a ⌜ x y ⌝ = Other ↔ a ≠ x ∧ a ≠ y := by simp [roleOfIn]; grind

@[simp]
lemma roleOfIn_fstE_eq_Caller_iff : roleOfIn a ⌜ x^z y ⌝ = Caller ↔ a = x := by simp [roleOfIn]; grind
@[simp]
lemma roleOfIn_fstE_eq_Callee_iff : roleOfIn a ⌜ x^z y ⌝ = Callee ↔ a ≠ x ∧ a = y := by simp [roleOfIn]; grind
@[simp]
lemma roleOfIn_fstE_eq_Other_iff : roleOfIn a ⌜ x^z y ⌝ = Other ↔ a ≠ x ∧ a ≠ y := by simp [roleOfIn]; grind

@[simp]
lemma roleOfIn_sndE_eq_Caller_iff : roleOfIn a ⌜ x y^z ⌝ = Caller ↔ a = x := by simp [roleOfIn]; grind
@[simp]
lemma roleOfIn_sndE_eq_Callee_iff : roleOfIn a ⌜ x y^z ⌝ = Callee ↔ a ≠ x ∧ a = y := by simp [roleOfIn]; grind
@[simp]
lemma roleOfIn_sndE_eq_Other_iff : roleOfIn a ⌜ x y^z ⌝ = Other ↔ a ≠ x ∧ a ≠ y := by simp [roleOfIn]; grind

/-- Who is the other agent than `i` in this call? If `i` is not in the call, return caller. -/
def other (i : @Agent n) : (c : @Call n) → @Agent n
  | ⌜ a   b   ⌝ => if i = a then b else a
  | ⌜ a^_ b   ⌝ => if i = a then b else a
  | ⌜ a   b^_ ⌝ => if i = a then b else a

/-! ## Sequences with at most one transmission error -/

/-- This sequence contains no transmission errors. -/
def errFree : @Sequence n → Prop
  | [] => True
  | ⌜_ _⌝ :: rest => errFree rest
  | ⌜_^_ _⌝ :: _ => False
  | ⌜_ _^_⌝ :: _ => False

/-- This sequence contains at most one transmission error. -/
def maxOne : @Sequence n → Prop
  | [] => True
  | ⌜_   _⌝ :: rest => maxOne rest
  | ⌜_^_ _⌝ :: rest => errFree rest
  | ⌜_ _^_⌝ :: rest => errFree rest

@[aesop unsafe apply]
lemma Sequence.maxOne_of_errFree : errFree σ → maxOne σ := by
  induction σ
  · simp [errFree,maxOne]
  case cons C σ IH =>
    cases C <;> simp only [errFree, maxOne, IsEmpty.forall_iff]
    exact IH

@[aesop unsafe apply]
lemma Sequence.maxOne_cons : maxOne (C :: σ) → maxOne σ := by
  intro
  cases C <;> simp [maxOne] at * <;> aesop

/-- Short notation for the frequently needed proof that
if σ.κ has at most one error then σ has at most one error. -/
notation "⁻" o:arg => Sequence.maxOne_cons o

/-- Sequence with at most one error. -/
def OSequence : Type := @Subtype (@Sequence n) maxOne

/-- Subsequence relation: τ extends σ.
Because the lists are with the newest call first, this is defined as σ being a suffix of τ. -/
notation σ:arg "⊑" τ:arg => σ.1 <:+ τ.1

instance : Coe (@OSequence n) (@Sequence n) := ⟨Subtype.val⟩

def OSequence.length (σ : @OSequence n) : Nat := σ.1.length

@[simp]
lemma OSequence.length_nil : OSequence.length (⟨[], h⟩ : @OSequence n) = 0 := by
  simp [OSequence.length]

@[simp]
lemma OSequence.length_def (σ : @Sequence n) h :
  OSequence.length ⟨σ, h⟩ = σ.length := by unfold OSequence.length; simp

/-! ## Semantics -/

mutual

/-- (Def 4) Semantics of call.
What values does this agent have after this sequence? -/
def resultSet (i : @Agent n) : @Dist n → @OSequence n → Set (@Value n)
  | ι, ⟨[],_⟩ => { (i, ι i) } -- for the basis, ι[ε] = ι
  | ι, ⟨(C :: σ),o⟩ =>
    /- (*) Values that `i` already knows to be wrong before the call (and can thus refuse). -/
    let refuse : Set Value := { ⟨j, d⟩ | eval ι ⟨σ,⁻o⟩ (K i (Has j (j, !d))) }
    /- (**) Values that `i` knows to be wrong after the call (and can thus delete).
    The `sel` here decides which part of `contribSet` agent `a` may see (namely: not its own). -/
    let delete sel : Set Value := { ⟨j, d⟩ | ∀ ι' τ D, equiv i (ι,⟨⟨σ,⁻o⟩,rfl⟩) (ι',τ)
                                                → roleOfIn i C = roleOfIn i D
                                                → sel (contribSet ι ⟨σ,⁻o⟩ C) = sel (contribSet ι' τ D)
                                                → eval ι' τ (Has j (j, !d)) }
    match C, roleOfIn i C with
      -- Not involved:
      | _, Other => resultSet i ι ⟨σ,⁻o⟩
      -- Normal calls:
      | ⌜ a b ⌝, Caller => ((resultSet a ι ⟨σ,⁻o⟩ ∪ resultSet b ι ⟨σ,⁻o⟩) \ refuse) \ delete Prod.snd
      | ⌜ a b ⌝, Callee => ((resultSet a ι ⟨σ,⁻o⟩ ∪ resultSet b ι ⟨σ,⁻o⟩) \ refuse) \ delete Prod.fst
      -- Error from a (but not for a itself):
      | ⌜ a^_ b ⌝, Caller => ((          resultSet a ι ⟨σ,⁻o⟩  ∪ resultSet b ι ⟨σ,⁻o⟩) \ refuse) \ delete Prod.snd
      | ⌜ a^c b ⌝, Callee => ((invert c (resultSet a ι ⟨σ,⁻o⟩) ∪ resultSet b ι ⟨σ,⁻o⟩) \ refuse) \ delete Prod.fst
      -- Error from b (but not for b itself):
      | ⌜ a b^c ⌝, Caller => ((resultSet a ι ⟨σ,⁻o⟩ ∪ invert c (resultSet b ι ⟨σ,⁻o⟩)) \ refuse) \ delete Prod.snd
      | ⌜ a b^_ ⌝, Callee => ((resultSet a ι ⟨σ,⁻o⟩ ∪           resultSet b ι ⟨σ,⁻o⟩ ) \ refuse) \ delete Prod.fst
termination_by
  _ σ => (σ.length, 0) -- should be below contribSet
decreasing_by
  all_goals
    apply Prod.Lex.left; grind [OSequence.length] -- sequence becomes shorter in all recursive calls!

/-- Right after sequence `σ`, what values will caller and callee contribute to the call? -/
def contribSet (ι : @Dist n) (σ : @OSequence n) : @Call n → Set (@Value n) × Set (@Value n)
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
def equiv {k} (a : @Agent n) :
    (@Dist n × {σ : @OSequence n // σ.length = k}) → (@Dist n × {σ : @OSequence n // σ.length = k}) → Prop
  | (ι, ⟨⟨[]    ,_⟩,_⟩), (ι', ⟨⟨[]    ,_⟩,_⟩) => ι a = ι' a
  | (ι, ⟨⟨C :: σ,o⟩,_⟩), (ι', ⟨⟨D :: τ,q⟩,_⟩) =>
                          @equiv (k-1) a (ι,⟨⟨σ,⁻o⟩, by grind [OSequence.length]⟩) (ι',⟨⟨τ,⁻q⟩, by grind [OSequence.length]⟩)
                        ∧ roleOfIn a C = roleOfIn a D
                        -- Depending on role, observe (contribSet of) the other agent in the call
                        ∧ match roleOfIn a C with
                          | Other => True
                          | Caller => (contribSet ι ⟨σ,⁻o⟩ C).2 = (contribSet ι' ⟨τ,⁻q⟩ D).2 ∧ C.pair = D.pair
                          | Callee => (contribSet ι ⟨σ,⁻o⟩ C).1 = (contribSet ι' ⟨τ,⁻q⟩ D).1 ∧ C.pair = D.pair

termination_by
  ισ _ => (ισ.2.1.length, 0) -- should be above contribSet
decreasing_by
  all_goals
    apply Prod.Lex.left; grind [OSequence.length]

/-- (Def 6) Semantics. -/
def eval : @Dist n → @OSequence n → @Form n → Prop
  | _, _, .Top => True
  | ι, σ, .Neg φ => ¬ eval ι σ φ
  | ι, σ, .Has a (j, k) => (j, k) ∈ resultSet a ι σ
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

@[simp]
lemma resultSet_nil {ι i} :
    @resultSet n i ι ⟨[],o⟩ = { (i, ι i) } := by
  simp [resultSet]

@[simp]
lemma equiv_nil :
    equiv i (ι, ⟨⟨[],o1⟩,h1⟩) (κ, ⟨⟨[],o2⟩,h2⟩) ↔ ι i = κ i := by
  simp [equiv]

/-! ## Notation and Abbreviations -/

notation ι:arg "⌈" σ:arg "⌉ " " ⊧ " φ:(arg-1) => eval ι σ φ

/-- An abbreviation to easily say that we have the same length and (can thus say) `equiv`. -/
def equi (a : @Agent n) (ισ : @Dist n × @OSequence n) (ι'τ : @Dist n × @OSequence n) : Prop :=
  ∃ h : ισ.2.length = ι'τ.2.length, equiv a ⟨ισ.1, ⟨ισ.2, rfl⟩⟩ ⟨ι'τ.1, ⟨ι'τ.2, h.symm⟩⟩

notation ισ:arg " ~_ " a:arg ι'τ:arg => equi a ισ ι'τ

lemma equi_of_equiv :
    equiv a ⟨ι, ⟨σ, h1⟩⟩ ⟨ι', ⟨τ, h2⟩⟩ → equi a ⟨ι,σ⟩ ⟨ι',τ⟩ := by
  intro hyp
  constructor
  · simp
    convert hyp
  · linarith

lemma equiv_of_equi :
    equi a ⟨ι,σ⟩ ⟨ι',τ⟩  → equiv a ⟨ι, ⟨σ, h1⟩⟩ ⟨ι', ⟨τ, h2⟩⟩ := by
  rintro ⟨h, equ⟩
  convert equ
  linarith

/-- Validity of formulas -/
def valid (φ : @Form n) := ∀ ι σ, eval ι σ φ

prefix:100 "⊨ " => valid -- FIXME what's a good precedence value here?

/-! ## Properties of the Semantics -/

lemma sameRole_of_equiv :
    equiv a (ι, ⟨⟨C₁ :: σ, o1⟩, h1⟩) (κ, ⟨⟨C₂ :: τ, o2⟩ , h2⟩) →
    roleOfIn a C₁ = roleOfIn a C₂ := by
  unfold equiv
  simp_all

@[simp]
lemma equiv_refl {n} {a : @Agent n} {ι : @Dist n} {k} {σ : { σ : OSequence // σ.length = k }} :
    equiv (a : Agent) (ι, σ) (ι, σ) := by
  unfold equiv
  split
  · simp_all
  case h_2 he1 he2 =>
    simp_all [OSequence.length]
    rcases he1 with ⟨_,_,_⟩
    rcases he2 with ⟨_,_⟩
    subst_eqs
    simp
    cases roleOfIn a _ <;> simp_all <;> apply equiv_refl

lemma equiv_symm {i m ι} {σ : @OSequence n} {h1 : σ.length = m} {κ τ h2} :
      equiv i (ι, ⟨σ, h1⟩) (κ, ⟨τ, h2⟩)
    ↔ equiv i (κ, ⟨τ, h2⟩) (ι, ⟨σ, h1⟩) := by
  rcases σ with ⟨σ,o⟩
  rcases τ with ⟨τ,o'⟩
  induction σ generalizing m τ
  · subst h1
    simp [OSequence.length] at h2
    subst h2
    simp at *
    grind
  case cons C₁ σ IH =>
    subst h1
    rcases List.exists_cons_of_length_eq_add_one h2 with ⟨C₂, τ, τ_def⟩
    subst τ_def
    simp [OSequence.length] at h2
    unfold equiv
    rw [IH]
    grind

lemma equiv_trans {a m ι} {σ : @OSequence n} {h1 : σ.length = m} {κ τ h2 η ρ h3} :
      equiv a (ι, ⟨σ, h1⟩) (κ, ⟨τ, h2⟩)
    → equiv a (κ, ⟨τ, h2⟩) (η, ⟨ρ, h3⟩)
    → equiv a (ι, ⟨σ, h1⟩) (η, ⟨ρ, h3⟩) := by
  rcases σ with ⟨σ,o⟩
  rcases τ with ⟨τ,o'⟩
  rcases ρ with ⟨ρ,o''⟩
  intro ha hb
  induction σ generalizing m ι κ τ η ρ
  · subst h1
    simp at h2 h3
    subst h2 h3
    simp at *
    grind
  case cons C₁ σ IH =>
    simp [OSequence.length]  at h1
    subst h1
    rcases List.exists_cons_of_length_eq_add_one h2 with ⟨C₂, τ, τ_def⟩
    subst τ_def
    simp at h2
    rcases List.exists_cons_of_length_eq_add_one h3 with ⟨C₃, η, η_def⟩
    subst η_def
    simp at h3
    unfold equiv
    refine ⟨?_, ?_, ?_⟩
    · simp [equiv] at ha
      simp [equiv] at hb
      exact IH _ _ _ _ _ ha.1 hb.1
    · rw [sameRole_of_equiv ha, sameRole_of_equiv hb]
    · grind [equiv]

instance : Equivalence (@equiv n k i) :=
  ⟨ fun _ => equiv_refl
  , equiv_symm.mp
  , equiv_trans ⟩

/-- Agents know their own initial state. -/
lemma true_of_knowldege {ι σ a} {φ : @Form n} :
    ι⌈σ⌉ ⊧ K a φ  → ι⌈σ⌉ ⊧ φ := by
  intro hyp
  simp [eval] at hyp
  exact hyp ι σ rfl equiv_refl

/-- Agents know their own initial state. -/
lemma know_self m σ τ (h1 : σ.length = m) (h2 : τ.1.length = m) :
    equiv a (ι, ⟨σ, h1⟩) (κ, ⟨τ, h2⟩) → ι a = κ a  := by
  rcases σ with ⟨σ,o⟩
  rcases τ with ⟨τ,o'⟩
  induction m generalizing ι κ σ τ
  · rw [OSequence.length_def, List.length_eq_zero_iff] at h1
    simp [List.length_eq_zero_iff] at h2
    subst h1 h2
    simp
  case succ n IH =>
    rcases List.exists_cons_of_length_eq_add_one h1 with ⟨c1, σ, σ_def⟩
    rcases List.exists_cons_of_length_eq_add_one h2 with ⟨c2, τ, τ_def⟩
    unfold equiv
    cases h : roleOfIn a c1
    all_goals
      simp at h1 h2
      aesop

/-- Agents are stubborn about their own secrets. -/
@[simp]
lemma stubbornness m σ (h : σ.length = m) :
    ι⌈σ⌉ ⊧ (a, k) @ a  ↔  ι a = k := by
  rcases σ with ⟨σ,o⟩
  simp [eval]
  induction m generalizing σ k ι
  case zero =>
    rw [OSequence.length_def, List.length_eq_zero_iff] at h
    subst h
    simp
    grind
  case succ m IH =>
    rcases List.exists_cons_of_length_eq_add_one h with ⟨c, σ, σ_def⟩
    subst σ_def
    unfold resultSet
    simp
    let c_copy := c
    cases rh : roleOfIn a c
    case Caller =>
     cases c <;> simp <;> simp at h
     all_goals
      simp at rh
      subst rh
      constructor
      · rintro ⟨(ak_in|ak_in), not_k⟩
        · rw [IH _ (⁻o) h] at ak_in; assumption
        · simp [eval] at not_k
          rcases not_k with ⟨κ, τ, ⟨same, equ⟩, not_in⟩
          have := know_self _ _ _ _ _ equ
          specialize @IH κ (!k) τ.1 _ (by aesop)
          aesop
      · intro ak_in
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · left
          rw [IH _ (⁻o) h]
          assumption
        · intro hyp
          simp [eval] at hyp
          specialize hyp ι ⟨σ,⁻o⟩ rfl equiv_refl
          simp at IH
          grind
        · refine ⟨ι, ⟨σ,⁻o⟩, ⟨rfl, equiv_refl⟩, ?_⟩
          use c_copy
          simp [c_copy, eval]
          rw [@IH _ _ σ (⁻o) h]
          simpa [roleOfIn]
    case Callee =>
     cases c <;> simp <;> simp at h
     all_goals -- Callee
      simp at rh
      rcases rh with ⟨rh1,rh2⟩
      subst rh2
      constructor
      · rintro ⟨(ak_in|ak_in), not_k⟩
        · simp [eval] at not_k
          rcases not_k with ⟨κ, τ, ⟨same, equ⟩, not_in⟩
          have := know_self _ _ _ _ _ equ
          specialize @IH κ (!k) τ.1 _ (by aesop)
          aesop
        · rw [IH _ (⁻o) h] at ak_in; assumption
      · intro ak_in
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · right
          rw [IH _ (⁻o) h]
          assumption
        · intro hyp
          simp [eval] at hyp
          specialize hyp ι ⟨σ,⁻o⟩ rfl equiv_refl
          simp at IH
          grind
        · refine ⟨ι, ⟨σ,⁻o⟩, (by simp), ?_⟩
          use c_copy
          simp [c_copy, eval, roleOfIn]
          rw [@IH _ _ σ (⁻o) h]
          simp
          tauto
    case Other =>
      cases c <;> simp <;> simp at h
      all_goals
        simp at rh
        rcases rh with ⟨rh1,rh2⟩
        rw [IH _ _ h]

/-- A useful corollary of `stubbornness`. -/
@[simp]
lemma not_notMem_resultSet : (b, ! ι b) ∉ ι⌈σ⌉b := by
  have := @stubbornness _ ι b (! ι b) _ σ rfl
  unfold eval at this
  simp [this]

lemma equiv_then_know_same {a m ι} {σ : @OSequence n} {h1 : σ.length = m} {κ τ h2}
    (equ : equiv a (ι, ⟨σ, h1⟩) (κ, ⟨τ, h2⟩))
    φ
    : eval ι σ (K a φ) ↔ eval κ τ (K a φ) := by
  rcases σ with ⟨σ,o⟩
  unfold eval
  simp
  constructor
  · intro hyp η ρ same_len equ'
    apply hyp η ρ (by simp at h1; aesop)
    have := @equiv_trans n a m ι ⟨σ,o⟩ h1 κ τ h2 η ρ (by grind) equ (by convert equ'; grind)
    convert this
  · intro hyp η ρ same_len equ'
    apply hyp η ρ (by aesop)
    rw [equiv_symm] at equ
    have := @equiv_trans n a m κ τ h2 ι ⟨σ,o⟩ h1 η ρ (by grind) equ (by convert equ'; grind)
    convert this

set_option maxHeartbeats 2000000 in
/-- Lemma 7 -/
lemma indistinguishable_then_same_values {n} {a : @Agent n} {ι ι': @Dist n} {σ τ : OSequence} :
    (ι, σ) ~_a (ι', τ)  →  ι⌈σ⌉a = ι'⌈τ⌉a := by
  rcases σ with ⟨σ,o⟩
  rcases τ with ⟨τ,o'⟩
  intro ⟨same_len, equ⟩
  induction σ generalizing τ o'
  case nil =>
    have := List.length_eq_zero_iff.mp same_len.symm
    aesop
  case cons C σ IH =>
    simp at IH
    rcases List.exists_cons_of_length_eq_add_one same_len.symm with ⟨D, τ, _def⟩
    subst _def
    simp only [equiv] at equ
    specialize IH (⁻o) _ (⁻o') (by simp at same_len; assumption) equ.1 -- IH now says `ι⌈σ⌉a = ι'⌈τ⌉a`
    -- distinguish cases whether/how a is involved in C (and thus also D) or not
    cases r : roleOfIn a C
    case Caller => -- first out of three outer cases
      simp only [r] at equ
      rcases equ with ⟨prev_equ, Caller_eq, prev_same_contrib, same_pair⟩
      unfold contribSet at prev_same_contrib
      let C_copy := C
      cases C <;> cases D <;> simp [Call.pair, roleOfIn_eq_Caller_iff] at *
      all_goals -- 9 subcases
        rcases same_pair with ⟨_,_⟩
        subst_eqs
        simp only [OSequence.length_def, List.length_cons, Nat.add_right_cancel_iff] at same_len
        clear Caller_eq
        simp only [roleOfIn_a, resultSet, Subtype.forall, OSequence.length_def,
          roleOfIn_sndE_eq_Caller_iff, roleOfIn_fstE_eq_Caller_iff, roleOfIn_sndE_eq_Caller_iff]
        ext ⟨d,k⟩
        constructor
        all_goals
          intro dk_in
          simp only [Set.mem_diff, Set.mem_union, Set.mem_setOf_eq, not_forall] at dk_in
          rcases dk_in with ⟨⟨someone_had_dk_before, dk_not_refused⟩, not_self_corrected⟩
        · simp_all [← IH, ← equiv_then_know_same prev_equ]
          rcases not_self_corrected with ⟨ι2, σ2, len2, C2, same_contrib_2, role2, equ2, ndk⟩
          refine ⟨ι2, σ2, ⟨by omega, ?_⟩, C2, ?_, by grind [contribSet], ndk⟩
          · convert equiv_trans (equiv_symm.mp prev_equ) equ2; simp_all
          · rw [← role2]; try simp [roleOfIn]
        · simp_all [equiv_then_know_same prev_equ]
          rcases not_self_corrected with ⟨ι2, σ2, len2, C2, same_contrib_2, role2, equ2, ndk⟩
          refine ⟨ι2, σ2, ⟨by omega, ?_⟩, C2, ?_, by grind [contribSet], ndk⟩
          · apply equiv_trans prev_equ; rw! [same_len]; convert equ2
          · rw [← role2]; try simp [roleOfIn]
    case Callee => -- second of three outer cases, very similar to `Caller`
      simp [r] at equ
      rcases equ with ⟨prev_equ, Callee_eq, prev_same_contrib, same_pair⟩
      unfold contribSet at prev_same_contrib
      let C_copy := C
      cases C <;> cases D <;> simp [Call.pair, roleOfIn_eq_Callee_iff] at *
      all_goals -- again 9 subcases, same proof
        rcases same_pair with ⟨_,_⟩
        rcases r with ⟨_,_⟩
        subst_eqs
        simp only [OSequence.length_def, List.length_cons, Nat.add_right_cancel_iff] at same_len
        clear Callee_eq
        simp_all [resultSet]
        ext ⟨d,k⟩
        constructor
        all_goals
          intro dk_in
          simp only [Set.mem_diff, Set.mem_union, Set.mem_setOf_eq, not_forall] at dk_in
          rcases dk_in with ⟨⟨someone_had_dk_before, dk_not_refused⟩, not_self_corrected⟩
        · simp_all [← IH, ← equiv_then_know_same prev_equ]
          rcases not_self_corrected with ⟨ι2, σ2, len2, C2, same_contrib_2, role2, equ2, ndk⟩
          refine ⟨ι2, σ2, ⟨by omega, ?_⟩, C2, ?_, by grind [contribSet], ndk⟩
          · convert equiv_trans (equiv_symm.mp prev_equ) equ2; simp_all
          · rw [← role2]; try simp [roleOfIn]
        · simp_all [equiv_then_know_same prev_equ]
          rcases not_self_corrected with ⟨ι2, σ2, len2, C2, same_contrib_2, role2, equ2, ndk⟩
          refine ⟨ι2, σ2, ⟨by omega, ?_⟩, C2, ?_, by grind [contribSet], ndk⟩
          · apply equiv_trans prev_equ; rw! [same_len]; convert equ2
          · rw [← role2]; try simp [roleOfIn]
    case Other => -- third out of three outer cases, easy
      unfold resultSet
      rw [r]
      rw [equ.2.1] at r
      rw [r]
      simp only
      exact IH

/-- Lemma 8. The truth value of any "a has ..." atom is known by a.
Note that `k` here says whether we have b or \overline{b}. -/
lemma local_is_known {a b : @Agent n} (k : Bool) :
      ⊨ ((     ⟨b,k⟩ @ a ) ⟹ (K a (     ⟨b,k⟩ @ a) ))
    ∧ ⊨ ((Neg (⟨b,k⟩ @ a)) ⟹ (K a (Neg (⟨b,k⟩ @ a)))) := by
  constructor
  all_goals
  · simp [valid, eval]
    intro ι σ bk_in κ τ same_len equ
    have := indistinguishable_then_same_values ⟨?_, equ⟩ -- using Lemma 7
    <;> grind only

/-! NOTE: the remaining lemmas do *not* use Lemma 7 and 8. -/

/-- Helper for Lemma 9, stronger version using a specific `k` and not `Kv`. -/
lemma knowledge_of_secrets_is_preserved' {a b : Agent} (k : Bool)
    (hKv : ι⌈σ⌉ ⊧ K a ((b,k) @ b))
    (hSub : σ ⊑ τ)
    : ι⌈τ⌉ ⊧ K a ((b,k) @ b) := by
  rcases σ with ⟨σ,o⟩
  rcases τ with ⟨τ,o'⟩
  rcases hSub with ⟨ρ, def_τ⟩ -- the `ρ` is called `τ \ σ` in the paper.
  induction ρ generalizing σ τ ι o'
  · simp_all
  case cons C ρ IH =>
    subst def_τ
    simp only at IH hKv
    unfold eval
    simp only [List.cons_append, Subtype.forall]
    intro κ τ same_len1 equ
    rcases τ with ⟨τ,o'⟩
    simp only [OSequence.length_def, List.length_cons, List.length_append] at same_len1
    -- The usual trick to split a list. Used so often, maybe make it a custom named tactic?
    rcases List.exists_cons_of_length_eq_add_one same_len1 with ⟨Cτ, τ, τ_def⟩
    subst τ_def
    specialize @IH ι σ _ hKv (ρ ++ σ) sorry rfl -- TODO: `ρ ++ σ` may have at most one error!
    rw [stubbornness _ ⟨(Cτ :: τ), o'⟩ same_len1]
    unfold equiv at equ
    have know_same := equiv_then_know_same equ.1 ((b, k) @ b)
    rw [know_same] at IH
    have := true_of_knowldege IH
    simp only at this
    rw [stubbornness _ _ rfl] at this
    assumption

/-- Lemma 9. Knowledge of secrets is preserved. -/
lemma knowledge_of_secrets_is_preserved {a b : @Agent n}
    (hKv : ι⌈σ⌉ ⊧ Kv a b) (hSub : σ ⊑ τ) : ι⌈τ⌉ ⊧ Kv a b := by
  unfold eval eval eval at hKv
  rw [← or_iff_not_and_not] at hKv
  unfold eval eval eval
  rw [← or_iff_not_and_not]
  rcases hKv with (h|h)
  · left
    exact @knowledge_of_secrets_is_preserved' n ι σ τ a b true h hSub
  · right
    exact @knowledge_of_secrets_is_preserved' n ι σ τ a b false h hSub

/-- Lemma 10. Agents know their own value. Follows from `stubbornness`. -/
lemma know_your_own {a : @Agent n} :
    ⊨ Kv a a := by
  intro ι σ
  unfold eval eval eval
  rw [← @or_iff_not_and_not]
  cases h : ι a
  · right
    unfold eval
    simp_rw [stubbornness]
    intro κ ⟨τ, same_len⟩ equ
    rw [know_self _ _ _ _ _ equ] at h
    exact h
  · left
    unfold eval
    simp_rw [stubbornness]
    intro κ ⟨τ, same_len⟩ equ
    rw [know_self _ _ _ _ _ equ] at h
    exact h

/-- Helper for Lemma 11 "iff (call semantics)" -/
lemma not_in_call_then_invariant_resultSet {a : @Agent n} {C : @Call n}
    (h : roleOfIn a C = Other) ι σ o
    : ι⌈⟨C :: σ, o⟩⌉a = ι⌈⟨σ, ⁻o⟩⌉a := by
  conv => left; unfold resultSet
  simp [h]

-- FIXME move up
@[simp]
lemma OSequence.maxOne {σ : @OSequence n} : maxOne σ.1 := by
  cases σ; simp_all

/-- Helper for Lemma 11 "iff (semantics of formulas and observation relation)" -/
lemma not_in_call_then_invariant_kv {a : @Agent n} {C : @Call n}
    (h : roleOfIn a C = Other) b ι σ o
    : eval ι ⟨C :: σ,  o⟩ (Kv a b)
    ↔ eval ι ⟨     σ, ⁻o⟩ (Kv a b) := by
  constructor
  · intro know_after
    unfold eval eval eval at *
    rw [← @or_iff_not_and_not] at *
    rcases know_after with know_after|know_after
    · left
      simp only [eval, stubbornness, Subtype.forall, OSequence.length_def, List.length_cons] at *
      intro T τ same_len equ
      let CnoErr : Call := match C with -- we remove the error from `C` if needed.
        | ⌜d e⌝ => ⌜d e⌝
        | ⌜d^c e⌝ => ⌜d e⌝
        | ⌜d e^c⌝ => ⌜d e⌝
      have h' : roleOfIn a CnoErr = Other := by unfold CnoErr; cases C <;> simp_all
      apply know_after T ⟨CnoErr :: τ, ?_⟩ (by simp [OSequence.length]; exact same_len)
      · unfold equiv; simp [h, h', equ]
      · unfold CnoErr; cases C <;> simp [maxOne]
    · right
      simp only [eval, stubbornness, Subtype.forall, OSequence.length_def, List.length_cons] at *
      intro T τ same_len equ
      let CnoErr : Call := match C with -- we remove the error from `C` if needed.
        | ⌜d e⌝ => ⌜d e⌝
        | ⌜d^c e⌝ => ⌜d e⌝
        | ⌜d e^c⌝ => ⌜d e⌝
      have h' : roleOfIn a CnoErr = Other := by unfold CnoErr; cases C <;> simp_all
      apply know_after T ⟨CnoErr :: τ, ?_⟩ (by simp [OSequence.length]; exact same_len)
      · unfold equiv; simp [h, h', equ]
      · unfold CnoErr; cases C <;> simp [maxOne]
  · intro hyp
    apply knowledge_of_secrets_is_preserved hyp
    simp

/-- Lemma 11 -/
lemma knowledge_implies_correct_belief {n} {ι : @Dist n} {σ : @OSequence n} {a b : @Agent n} :
    ι⌈σ⌉ ⊧ (Kv a b) → (b, ι b) ∈ ι⌈σ⌉a := by
  intro a_kv_b
  rcases σ with ⟨σ,o⟩
  induction σ
  case nil =>
    unfold eval eval eval at a_kv_b
    simp only [not_and_or, not_not] at a_kv_b
    rcases a_kv_b with h|h
    all_goals
      simp_all [eval]
      by_cases b = a
      · aesop
      · exfalso
        have := h ι ⟨[], by simp [maxOne]⟩ (by simp)
        have := h (ι.switch b) ⟨[], by simp [maxOne]⟩ (by simp) (by simp [Dist.switch]; grind)
        simp_all [Dist.switch]
  case cons C σ IH =>
    cases ra : roleOfIn a C -- "For σ = τ.acᴷ ..."
    case Caller =>
      -- "... we distinguish two cases."
      by_cases h : eval ι ⟨σ,⁻o⟩ (Kv a b)
      · -- "Either already ...""
        specialize IH (⁻o) h
        unfold resultSet
        let C_copy := C
        cases C <;> simp [ra] <;> simp at ra <;> subst ra
        all_goals
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · left; assumption
          · simp only [eval, stubbornness, Subtype.forall, OSequence.length_def, not_forall,
              Bool.not_eq_not]
            use ι
            simp only [exists_prop, and_true]
            use ⟨σ,⁻o⟩
            simp
          · use ι, ⟨σ,⁻o⟩; simp; use C_copy; unfold C_copy; simp [roleOfIn]
      · -- "Or ..."
        simp [eval] at h
        -- "The assumption ... then implies that ..."
        -- TODO NEXT
        sorry
    case Callee =>
      -- analogous?
      sorry
    case Other => -- "where b,c ≠ a"
      rw [not_in_call_then_invariant_kv ra b ι σ o] at a_kv_b
      specialize IH (⁻o) a_kv_b -- induction
      rw [not_in_call_then_invariant_resultSet ra ι σ o]
      assumption

/-- Initial distribution with all values set to true. -/
def ini (n : Nat) : @Dist n := fun _ => true

-- FIXME: make it easier to define a state / give a sequence without writing `simp [maxOne]`.

/-- Correct belief need not imply knowledge: given `ini 2`, after an initial call
`ab` agent `a` correclty believes `b`, but a does not know the secret of `b`, because `a`
also considers it possible that the call was `a b^b` instead. -/
example (a b : Agent) (h : a ≠ b) : eval (ini 2) ⟨[ ⌜a b⌝ ], by simp [maxOne]⟩ $
      (   (b,true ) @ a) -- a believes b
    ⋀ (¬'((b,false) @ a))
    ⋀ (   (b,true  )@ b) -- correctly
    ⋀ (¬'(Kv a b)) -- but a does not *know* the value of b
    := by
  unfold ini
  unfold eval
  constructor
  · simp [eval, resultSet, contribSet]
    sorry
  · unfold eval
    constructor
    · simp [eval, resultSet, contribSet]
    · simp_all [eval]
      sorry

lemma corollary_twelve {a b : @Agent n} :
      ⊨ ( (K a ( b @ b)) ⟹ (( b @ b) ⋀ ( b @ a) ⋀ (¬' (‾b @ a))) )
    ∧ ⊨ ( (K a (‾b @ b)) ⟹ ((‾b @ b) ⋀ (‾b @ a) ⋀ (¬' ( b @ a))) )
    := by
  constructor
  · simp [valid, eval]
    intro ι σ lhs
    sorry
  · sorry

lemma corollary_thirteen {a b : @Agent n} :
      ⊨ ( (K a ( b @ b)) ⇔ K a (( b @ b) ⋀ ( b @ a) ⋀ (¬' (‾b @ a))) )
    ∧ ⊨ ( (K a (‾b @ b)) ⇔ K a ((‾b @ b) ⋀ (‾b @ a) ⋀ (¬' ( b @ a))) )
    := by
  constructor
  · sorry
  · sorry

/-!

Examples?

/-- Proposition 17, 18 and 19 maybe too hard? -/

-/

end Error
