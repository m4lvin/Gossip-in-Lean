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
  | i, S => fun a => if a = i then not (S a) else S a

inductive Call : Type
  /-- ⌜a b⌝ -/
  | normal : (caller : @Agent n) → (callee : { b : @Agent n // b ≠ caller }) → Call
  /-- ⌜a^c b⌝ -/
  | fstE : (caller : @Agent n) → (err : @Agent n) → (callee : { b : @Agent n // b ≠ caller }) → Call
  /-- ⌜a b^c⌝ -/
  | sndE : (caller : @Agent n) → (callee : { b : @Agent n // b ≠ caller }) → (err : @Agent n) → Call

-- Nicer notation for `Call`
notation "⌜" a:arg  b:arg "⌝" => Call.normal a b
notation "⌜" a:arg "^" c:arg b:arg "⌝" => Call.fstE a c b
notation "⌜"  a:arg b:arg "^" c:arg "⌝" => Call.sndE a b c

/-- The pair of agents in the call, ignoring whether an error is made. -/
def Call.pair : @Call n → (@Agent n × @Agent n)
  | ⌜ a   b   ⌝ => (a , b.1)
  | ⌜ a^_ b   ⌝ => (a , b.1)
  | ⌜ a   b^_ ⌝ => (a , b.1)

/-- (Def 2) A sequence is a list of calls.
For easy pattern matching this is in *reverse* order: the newest call is the first element. -/
abbrev Sequence : Type := List (@Call n)

/-- Flip the value of the secret of this agent in the given set. -/
def invert : @Agent n -> Set (@Value n) -> Set (@Value n)
  | i, vs => vs.image (fun (j,b) => if j = i then (j, not b) else (j,b))

/-- Membership in `invert c A` reduces to membership of the "flipped" value in `A`. -/
lemma mem_invert_iff {c : @Agent n} {A : Set Value} {v : Value} :
    v ∈ invert c A ↔ (if v.1 = c then (v.1, !v.2) else v) ∈ A := by
  rcases v with ⟨j, b⟩
  simp only [invert, Set.mem_image]
  constructor
  · rintro ⟨⟨j', b'⟩, hm, heq⟩
    split_ifs at heq ⊢ <;> simp_all
  · intro hm
    split_ifs at hm with h
    · exact ⟨⟨j, !b⟩, by subst h; simpa⟩
    · exact ⟨⟨j, b⟩, by simpa [h]⟩

/-! ## Syntax -/

/-- (Def 3) Logical language -/
inductive Form : Type
  /-- True constant -/
  | Top : Form
  /-- Conjunction -/
  | Con : Form → Form → Form
  /-- Negation -/
  | Neg : Form → Form
  /-- `Has a (b, k)` means agent `a` has value `k` of agent `b`. -/
  | Has : (a : @Agent n) → (@Value n) → Form
  /-- `K a φ` means agent `a` knows that `φ` is true. -/
  | K : (a : @Agent n) → (φ : Form) → Form

open Form

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
lemma roleOfIn_eq_caller {a : @Agent n} {b} : roleOfIn a ⌜ a b ⌝ = Caller := by simp [roleOfIn]
@[simp]
lemma roleOfIn_eq_callee {a : @Agent n} {b} : roleOfIn b.1 ⌜ a b ⌝ = Callee := by grind [roleOfIn]

@[simp]
lemma roleOfIn_fstE_eq_caller  {a c : @Agent n} {b} : roleOfIn a ⌜ a^c b ⌝ = Caller := by simp [roleOfIn]
@[simp]
lemma roleOfIn_fstE_eq_callee {a c : @Agent n} {b} : roleOfIn b.1 ⌜ a^c b ⌝ = Callee := by grind [roleOfIn]

@[simp]
lemma roleOfIn_sndE_eq_caller {a c : @Agent n} {b} : roleOfIn a ⌜ a b^c ⌝ = Caller := by simp [roleOfIn]
@[simp]
lemma roleOfIn_sndE_eq_callee {a c : @Agent n} {b} : roleOfIn b.1 ⌜ a b^c ⌝ = Callee := by grind [roleOfIn]

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

@[simp]
lemma roleOfIn_pair_fst :
    roleOfIn C.pair.1 C = Role.Caller := by
  cases C <;> simp [roleOfIn] <;> grind [Call.pair]

@[simp]
lemma roleOfIn_pair_snd :
    roleOfIn C.pair.2 C = Role.Callee := by
  cases C <;> simp [roleOfIn] <;> grind [Call.pair]

/-! ## Sequences with at most one transmission error -/

/-- This sequence contains no transmission errors. -/
def errFree : @Sequence n → Prop
  | [] => True
  | ⌜_ _⌝ :: rest => errFree rest
  | ⌜_^_ _⌝ :: _ => False
  | ⌜_ _^_⌝ :: _ => False

@[simp]
lemma errFree_nil : @errFree n [] := by simp [errFree]

/-- This sequence contains at most one transmission error. -/
def maxOne : @Sequence n → Prop
  | [] => True
  | ⌜_   _⌝ :: rest => maxOne rest
  | ⌜_^_ _⌝ :: rest => errFree rest
  | ⌜_ _^_⌝ :: rest => errFree rest

@[simp]
lemma maxOne_nil : @maxOne n [] := by simp [maxOne]

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

/-- If `o` proves that `C :: σ` has at most one error then we use the
short notation `⁻o` to get a proof that `σ` has at most one error. -/
notation "⁻" o:arg => Sequence.maxOne_cons o

/-- Sequence with at most one error. -/
def OSequence : Type := @Subtype (@Sequence n) maxOne

/-- Subsequence relation: `σ⊑τ` means that `τ` extends `σ`.
Because sequences are lists with the newest call first we define this as `List.IsSuffix σ τ`. -/
notation σ:arg "⊑" τ:arg => σ.1 <:+ τ.1

instance : Coe (@OSequence n) (@Sequence n) := ⟨Subtype.val⟩

def OSequence.length (σ : @OSequence n) : Nat := σ.1.length

@[simp]
def OSequence.nil : @OSequence n := ⟨[], by simp⟩

@[simp]
lemma OSequence.length_nil : OSequence.length (⟨[], h⟩ : @OSequence n) = 0 := by
  simp [OSequence.length]

@[simp]
lemma OSequence.length_def (σ : @Sequence n) h :
  OSequence.length ⟨σ, h⟩ = σ.length := by unfold OSequence.length; simp

@[simp]
lemma OSequence.ofLen_length (σ : { σ : @OSequence n // σ.length = k }) :
  σ.1.length = k := by grind

@[simp]
lemma OSequence.maxOne {σ : @OSequence n} : maxOne σ.1 := by
  cases σ; simp_all

/-! ## Semantics -/

mutual

/-- (Def 4) Semantics of call.
What values does this agent have after this sequence? -/
def resultSet (i : @Agent n) : @Dist n → @OSequence n → Set (@Value n)
  | S, ⟨[],_⟩ => { (i, S i) } -- for the basis, S[ε] = S
  | S, ⟨(C :: σ),o⟩ =>
    /- (*) Values that `i` already knows to be wrong before the call (and can thus refuse). -/
    let refuse : Set Value := { ⟨j, d⟩ | eval S ⟨σ,⁻o⟩ (K i (Has j (j, !d))) }
    /- (**) Values that `i` knows to be wrong after the call (and can thus delete).
    The `sel` here decides which part of `contribSet` agent `a` may see (namely: not its own). -/
    let delete sel : Set Value := { ⟨j, d⟩ | ∀ T τ D, equiv i (S,⟨⟨σ,⁻o⟩,rfl⟩) (T,τ)
                                                → roleOfIn i C = roleOfIn i D -- must be ≠ Other
                                                → sel (contribSet S ⟨σ,⁻o⟩ C) = sel (contribSet T τ D)
                                                → C.pair = D.pair -- involved, so observe the pair!
                                                → maxOne (D :: τ) -- ignore forbidden sequences
                                                → eval T τ (Has j (j, !d)) }
    match C, roleOfIn i C with
      -- Not involved:
      | _, Other => resultSet i S ⟨σ,⁻o⟩
      -- Normal calls:
      | ⌜ a b ⌝, Caller => ((resultSet a S ⟨σ,⁻o⟩ ∪ resultSet b S ⟨σ,⁻o⟩) \ refuse) \ delete Prod.snd
      | ⌜ a b ⌝, Callee => ((resultSet a S ⟨σ,⁻o⟩ ∪ resultSet b S ⟨σ,⁻o⟩) \ refuse) \ delete Prod.fst
      -- Error from a (but not for a itself):
      | ⌜ a^_ b ⌝, Caller => ((          resultSet a S ⟨σ,⁻o⟩  ∪ resultSet b S ⟨σ,⁻o⟩) \ refuse) \ delete Prod.snd
      | ⌜ a^c b ⌝, Callee => ((invert c (resultSet a S ⟨σ,⁻o⟩) ∪ resultSet b S ⟨σ,⁻o⟩) \ refuse) \ delete Prod.fst
      -- Error from b (but not for b itself):
      | ⌜ a b^c ⌝, Caller => ((resultSet a S ⟨σ,⁻o⟩ ∪ invert c (resultSet b S ⟨σ,⁻o⟩)) \ refuse) \ delete Prod.snd
      | ⌜ a b^_ ⌝, Callee => ((resultSet a S ⟨σ,⁻o⟩ ∪           resultSet b S ⟨σ,⁻o⟩ ) \ refuse) \ delete Prod.fst
termination_by
  _ σ => (σ.length, 0) -- should be below contribSet
decreasing_by
  all_goals
    apply Prod.Lex.left; grind [OSequence.length] -- Sequence becomes shorter in all cases.

/-- Right after sequence `σ`, what values will caller and callee contribute to the call? -/
def contribSet (S : @Dist n) (σ : @OSequence n) : @Call n → Set (@Value n) × Set (@Value n)
  | ⌜ a   b   ⌝ => (resultSet a S σ           ,            resultSet b S σ)
  | ⌜ a^c b   ⌝ => (invert c $ resultSet a S σ,            resultSet b S σ)
  | ⌜ a   b^c ⌝ => (resultSet a S σ           , invert c $ resultSet b S σ)
termination_by
  _ => (σ.length, 1) -- should be above resultSet
decreasing_by
  all_goals
    apply Prod.Lex.right; simp

/-- (Def 5) Observation relation.
This is *synchronous*. -/
def equiv {k} (a : @Agent n) : (@Dist n × {σ : @OSequence n // σ.length = k})
                             → (@Dist n × {σ : @OSequence n // σ.length = k}) → Prop
  | (S, ⟨⟨[]    ,_⟩,_⟩), (T, ⟨⟨[]    ,_⟩,_⟩) => S a = T a
  | (S, ⟨⟨C :: σ,o⟩,_⟩), (T, ⟨⟨D :: τ,q⟩,_⟩) =>
        @equiv (k-1) a (S,⟨⟨σ,⁻o⟩, by grind [OSequence.length]⟩) (T,⟨⟨τ,⁻q⟩, by grind [OSequence.length]⟩)
      ∧ roleOfIn a C = roleOfIn a D
      -- Depending on role, observe (contribSet of) the other agent in the call
      ∧ match roleOfIn a C with
        | Other => True
        | Caller => (contribSet S ⟨σ,⁻o⟩ C).2 = (contribSet T ⟨τ,⁻q⟩ D).2 ∧ C.pair = D.pair
        | Callee => (contribSet S ⟨σ,⁻o⟩ C).1 = (contribSet T ⟨τ,⁻q⟩ D).1 ∧ C.pair = D.pair
termination_by
  Sσ _ => (Sσ.2.1.length, 0) -- should be above contribSet
decreasing_by
  all_goals
    apply Prod.Lex.left; grind [OSequence.length]

/-- (Def 6) Semantics. -/
def eval : @Dist n → @OSequence n → @Form n → Prop
  | _, _, .Top => True
  | S, σ, .Neg φ => ¬ eval S σ φ
  | S, σ, .Has a (j, k) => (j, k) ∈ resultSet a S σ
  | S, σ, .Con φ ψ => eval S σ φ ∧ eval S σ ψ
  | S, σ, .K a φ => ∀ T, ∀ τ , (he : equiv a (S,⟨σ,rfl⟩) (T,τ)) → eval T τ φ
termination_by
  _ σ φ => (σ.length, φ.length)
decreasing_by -- Sequence length stays the same, but formula becomes shorter.
  · apply Prod.Lex.right; simp
  · apply Prod.Lex.right; simp -- Here we need `resultSet  <  Has i i`.
  · apply Prod.Lex.right; simp; linarith
  · apply Prod.Lex.right; simp
  · apply Prod.Lex.right; simp -- Here we need `equiv  <  K i φ`.
  · rw [τ.2] -- Here `σ` and `τ` must have the same length.
    apply Prod.Lex.right
    simp_wf

end

notation S:arg "⌈" σ:arg "⌉" a:arg => resultSet a S σ

@[simp]
lemma resultSet_nil {S i} :
    @resultSet n i S ⟨[],o⟩ = { (i, S i) } := by
  simp [resultSet]

@[simp]
lemma equiv_nil :
    equiv i (S, ⟨⟨[],o1⟩,h1⟩) (T, ⟨⟨[],o2⟩,h2⟩) ↔ S i = T i := by
  simp [equiv]

/-! ## Notation and Abbreviations -/

prefix:70 " ¬'" => Form.Neg

infixr:60 " ⋀ " => Form.Con

notation φ1:arg " ⋁ " φ2:arg => Neg (Con (Neg φ1) (Neg φ2))
notation φ1:arg "⟹" φ2:arg => (Neg φ1) ⋁ φ2
notation φ1:(arg-1) " ⇔ " φ2:(arg-1) => Con (φ1 ⟹ φ2) (φ2 ⟹ φ1)

/-- We write `v @ a` to say that agent `a` has value `v`. -/
notation v:(arg-1) "@" a:arg => Has a v

notation "Kv" a:arg b:arg => (K a (b @ b)) ⋁ (K a (‾b @ b))

notation S:arg "⌈" σ:arg "⌉ " " ⊧ " φ:(arg-1) => eval S σ φ

/-- Validity of formulas -/
def valid (φ : @Form n) := ∀ S σ, eval S σ φ

prefix:100 "⊨ " => valid -- FIXME what's a good precedence value here?

-- @[simp]
lemma eval_biimpl : S⌈σ⌉ ⊧ φ1 ⇔ φ2 ↔ (S⌈σ⌉ ⊧ φ1 ↔ S⌈σ⌉ ⊧ φ2) := by
  simp [eval]; tauto

-- @[simp]
lemma eval_impl : S⌈σ⌉ ⊧ φ1 ⟹ φ2 ↔ (S⌈σ⌉ ⊧ φ1 → S⌈σ⌉ ⊧ φ2) := by
  simp [eval]

-- @[simp]
lemma eval_con : S⌈σ⌉ ⊧ (φ1 ⋀ φ2) ↔ S⌈σ⌉ ⊧ φ1 ∧ S⌈σ⌉ ⊧ φ2 := by
  simp [eval]

-- @[simp]
lemma eval_dis : S⌈σ⌉ ⊧ φ1 ⋁ φ2 ↔ S⌈σ⌉ ⊧ φ1 ∨ S⌈σ⌉ ⊧ φ2 := by
  simp [eval]; tauto

/-! ## The observation relation is an equivalence -/

/-- An abbreviation to easily say that we have the same length and (can thus say) `equiv`. -/
def equi (a : @Agent n) (Sσ : @Dist n × @OSequence n) (Tτ : @Dist n × @OSequence n) : Prop :=
  ∃ h : Sσ.2.length = Tτ.2.length, equiv a ⟨Sσ.1, ⟨Sσ.2, rfl⟩⟩ ⟨Tτ.1, ⟨Tτ.2, h.symm⟩⟩

notation Sσ:arg " ~_ " a:arg Tτ:arg => equi a Sσ Tτ

lemma equi_of_equiv :
    equiv a ⟨S, ⟨σ, h1⟩⟩ ⟨T, ⟨τ, h2⟩⟩ → equi a ⟨S,σ⟩ ⟨T,τ⟩ := by
  intro hyp
  constructor
  · simp
    convert hyp
  · linarith

lemma equiv_of_equi :
    equi a ⟨S,σ⟩ ⟨T,τ⟩  → equiv a ⟨S, ⟨σ, h1⟩⟩ ⟨T, ⟨τ, h2⟩⟩ := by
  rintro ⟨h, equ⟩
  convert equ
  linarith

lemma sameRole_of_equiv :
    equiv a (S, ⟨⟨C₁ :: σ, o1⟩, h1⟩) (T, ⟨⟨C₂ :: τ, o2⟩ , h2⟩) →
    roleOfIn a C₁ = roleOfIn a C₂ := by
  unfold equiv
  simp_all

@[simp]
lemma equiv_refl {n} {a : @Agent n} {S : @Dist n} {k} {σ : { σ : OSequence // σ.length = k }} :
    equiv (a : Agent) (S, σ) (S, σ) := by
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

lemma equiv_symm {i m S} {σ : @OSequence n} {h1 : σ.length = m} {T τ h2} :
      equiv i (S, ⟨σ, h1⟩) (T, ⟨τ, h2⟩)
    ↔ equiv i (T, ⟨τ, h2⟩) (S, ⟨σ, h1⟩) := by
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

lemma equiv_trans {a m S} {σ : @OSequence n} {h1 : σ.length = m} {T τ h2 R ρ h3} :
      equiv a (S, ⟨σ, h1⟩) (T, ⟨τ, h2⟩)
    → equiv a (T, ⟨τ, h2⟩) (R, ⟨ρ, h3⟩)
    → equiv a (S, ⟨σ, h1⟩) (R, ⟨ρ, h3⟩) := by
  rcases σ with ⟨σ,o⟩
  rcases τ with ⟨τ,o'⟩
  rcases ρ with ⟨ρ,o''⟩
  intro ha hb
  induction σ generalizing m S T τ R ρ
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

/-- The observation relation `equiv` $∼_a$ is an equivalence relation. -/
theorem equiv_Equivalence : Equivalence (@equiv n k i) :=
  ⟨fun _ => equiv_refl, equiv_symm.mp, equiv_trans⟩

lemma equiv_then_know_same {a m S} {σ : @OSequence n} {h1 : σ.length = m} {T τ h2}
    (equ : equiv a (S, ⟨σ, h1⟩) (T, ⟨τ, h2⟩))
    φ
    : eval S σ (K a φ) ↔ eval T τ (K a φ) := by
  rcases σ with ⟨σ,o⟩
  unfold eval
  simp
  constructor
  · intro hyp η ρ same_len equ'
    apply hyp η ρ (by simp at h1; aesop)
    have := @equiv_trans n a m S ⟨σ,o⟩ h1 T τ h2 η ρ (by grind) equ (by convert equ'; grind)
    convert this
  · intro hyp η ρ same_len equ'
    apply hyp η ρ (by aesop)
    rw [equiv_symm] at equ
    have := @equiv_trans n a m T τ h2 S ⟨σ,o⟩ h1 η ρ (by grind) equ (by convert equ'; grind)
    convert this
