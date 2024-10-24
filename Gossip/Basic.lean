-- Basic.lean
--
-- Authors: Timo Doherty, Malvin Gattinger
--
-- Description:
-- - This file contains the representation of gossip in Lean.

import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.Linarith

-- State representation that contains the all gossip information between any agents.
def GossipState (n : Nat) : Type := Fin n → Fin n → Prop

-- A Call is a pair of agents.
def Call (n : Nat): Type := Fin n × Fin n

-- Generates the initial state where agents only know their own secret.
def initialState (n : Nat) : GossipState n := fun i j => i = j

instance {n : ℕ} : DecidableRel (initialState n) := decEq

-- Check if an agent is an expert.
def isExpert (s : GossipState n) (i : Fin n): Prop := ∀ j, s i j

-- Instance that allows isExpert to evaluate on Decidable GossipStates.
instance {s : GossipState n} [DecidableRel s] {i : Fin n} : Decidable (isExpert s i) :=
  Fintype.decidableForallFintype

-- Check if all agents are experts.
def allExpert (s : GossipState n) : Prop := ∀ i, isExpert s i

-- Instance that allows allExpert to evaluate on Decidable GossipStates.
instance {s : GossipState n} [DecidableRel s] : Decidable (allExpert s) :=
  Fintype.decidableForallFintype

-- Executes a single call.
def makeCall (s : GossipState n) : Call n → GossipState n
  | (i, j), x, y =>
    if x = i
    then s x y ∨ s j y
    else
      if x = j
        then s x y ∨ s i y
        else s x y

-- Instance that allows Decidable GossipStates built with makeCall to be decidable.
instance {s : GossipState n} [DecidableRel s] : ∀ {c : Call n}, DecidableRel (makeCall s c)
| (i, j), x, y =>
    if h : x = i
      then decidable_of_iff (s i y ∨ s j y) (by simp [makeCall, h])
      else
        if h' : x = j
          then decidable_of_iff (s j y ∨ s i y) (by cases h'; simp [makeCall, h])
          else decidable_of_iff (s x y) (by simp [makeCall, h, h'])

-- Executes multiple calls sequentially.
def makeCalls (s : GossipState n) (cs : List (Call n)) : GossipState n :=
  cs.foldl makeCall s

-- Instance that allows Decidable GossipStates built with makeCalls to be decidable.
instance {s : GossipState n} [DecidableRel s] {cs : List (Call n)} :
    DecidableRel (makeCalls s cs) := by
  induction cs generalizing s
  case nil hs => exact hs
  case cons c _ ih hs => exact ih


-- Rather than making a repr instance for GossipState, its easier to assume s is decidable and use repr.
def showState (s : GossipState n) [DecidableRel s] : Lean.Format :=
    repr (fun i j => if s i j then "True " else "False")


-- Prop: All gossip that is known in s1 is also known in s2.
def moreGossip (s1 s2 : GossipState n) : Prop := ∀ a b : Fin n, (s1 a b) → (s2 a b)

-- Adds an agent to a state, that knows only their own secret.
def addAgent (s : GossipState n) : GossipState (n.succ) :=
  λ a b => Fin.lastCases (b == Fin.last n)
                         (fun i => Fin.lastCases (false)
                                                 (fun b => s i b)
                                                b) a

-- Same call contents, but different type to match the larger state.
def expandCall {n : ℕ} (c : Call n) : Call (Nat.succ n) :=
  match c with
    | (i, j) => (i.castSucc, j.castSucc)

-- Expands a list of calls to the larger state.
def expandCalls {n : ℕ} (cs : List (Call n)) : List (Call (Nat.succ n)) :=
  cs.map expandCall

-- Two states are identical if they contain the same gossip.
def stateEquivalence : GossipState n → GossipState n → Prop :=
  λ s1 s2 => ∀ a b, s1 a b ↔ s2 a b

-- The call sequence contains contain agent a.
def contains (σ : List (Call n)) (a : Fin (n)) : Bool :=
  σ.any (λ c' => c'.1 = a ∨ c'.2 = a)


-- Being called by an expert means becoming an expert.
lemma expertMakesExpert {s : GossipState n} {i j : Fin n} :
  isExpert s i → isExpert (makeCall s (i, j)) j := by
  unfold isExpert
  intro h j_1
  simp [makeCall]
  simp_all only [or_true, ite_self]


-- Makecalls is the same as makeCall on head followed by makeCalls on tail.
lemma makeCalls_cons (s : GossipState n) (c : Call n) (cs : List (Call n)) :
  makeCalls s (c :: cs) = makeCalls (makeCall s c) cs := by
    rfl


-- Makecalls is the same as makeCalls on init followed by makeCall on last.
lemma makeCalls_snoc (s : GossipState n) (cs : List (Call n)) (c : Call n) :
  makeCalls s (cs ++ [c]) = makeCall (makeCalls s cs) c := by
    induction cs generalizing s
    case nil =>
      rfl
    case cons c' cs ih =>
      simp [makeCalls, ih]


-- Adding the same call to two states means the gossip relation remains.
lemma makeCall_increases_gossip (s1 s2 : GossipState n) (c : Call n) :
  moreGossip s1 s2 → moreGossip (makeCall s1 c) (makeCall s2 c) := by
    intro h a b -- There's gotta be a nicer way of doing this.
    simp [makeCall]
    intro a_1
    simp_all only
    split
    simp_all only
    split
    rename_i h_1
    subst h_1
    simp_all only [↓reduceIte]
    cases a_1
    · apply Or.inl
      apply h
      simp_all only
    · apply Or.inr
      apply h
      simp_all only
    simp_all only [↓reduceIte]
    split
    · rename_i a_j
      subst a_j
      simp_all only [↓reduceIte]
      cases a_1
      · apply Or.inl
        apply h
        simp_all only
      · apply Or.inr
        apply h
        simp_all only
    · simp_all only [↓reduceIte]
      apply h
      simp_all only



-- Adding the same calls to two states means the gossip relation remains.
lemma makeCallsIncreasesGossip (s1 s2 : GossipState n) (cs : List (Call n)) :
    moreGossip s1 s2 → moreGossip (makeCalls s1 cs) (makeCalls s2 cs) := by
    intro h
    induction cs generalizing s1 s2
    case nil =>
      simp [makeCalls]
      exact h
    case cons head tail ih =>
      rw [makeCalls_cons, makeCalls_cons]
      have h_call : moreGossip (makeCall s1 head) (makeCall s2 head) :=
        makeCall_increases_gossip s1 s2 head h -- uses the previous lemma for a single call.
      exact ih (makeCall s1 head) (makeCall s2 head) h_call


-- Adding a call to a state doesn't decrease the amount of gossip.
lemma makeCallMakesGossip (s : GossipState n) (c : Call n) :
    moreGossip s (makeCall s c) := by
  unfold moreGossip
  intro a b h
  simp [makeCall]
  simp_all only
  split
  simp_all only
  split
  rename_i h_1
  subst h_1
  simp_all only [true_or]
  rename_i c f g i j k
  if hyp: a = j then
    rw [hyp, if_pos]
    subst hyp
    simp_all only [true_or]
    rfl
  else
    rw [if_neg]
    simp_all only
    exact hyp


-- Adding calls to a state don't decrease the amount of gossip.
lemma callsIncreaseGossip (s : GossipState n) (cs : List (Call n)) :
    moreGossip s (makeCalls s cs) := by
    induction cs generalizing s
    case nil =>
      simp [makeCalls]
      unfold moreGossip
      intro a b h
      exact h
    case cons c cs ih =>
      rw [makeCalls_cons]
      have l : moreGossip s (makeCall s c) := by
        apply makeCallMakesGossip -- uses the previous lemma for a single call.
      simp_all [moreGossip]


-- An expert in the old state knows all but the new agent's secret if an agent is added.
lemma addAgentExpertOld {s : GossipState n} {i : Fin n} :
  isExpert s i ↔ ∀ j : Fin n, addAgent s i.castSucc j.castSucc := by
  have h1 : isExpert s i → ∀ j : Fin n, addAgent s i.castSucc j.castSucc := by
    intro h
    simp [addAgent]
    apply h
  have h2 : (∀ j : Fin n, addAgent s i.castSucc j.castSucc) → isExpert s i := by
    intro h
    unfold isExpert
    intro j
    simp [addAgent] at h
    exact h j
  exact Iff.intro h1 h2
