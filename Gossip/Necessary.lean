import Mathlib
-- Necessary.lean
--
-- Authors: Timo Doherty, Malvin Gattinger
--
-- Description:
-- We prove that 2n-4 calls are required for all agents to become experts.

/-
Alternative proofs to consider:
- Hajnal, Milner, and Szemeredi (1972)
- Richard T. Bumby (1981) https://doi.org/10.1137/0602002
- Tijdeman (1971)
- Hurkens (2000)
- Baker and Shostak (1972) https://doi.org/10.1016/0012-365x(72)90001-5

A nicely typeset version of Tijdeman (1971) and Baker and Shostak (1972)
is at https://www.math.uni-bielefeld.de/~sillke/PUZZLES/gossips.pdf

For now we try to follow Baker and Shostak (1972).
-/

import Mathlib.Data.List.Indexes
import Mathlib.Data.List.Basic

import Gossip.Sufficient

variable {n : Nat}

abbrev after (σ : List (Call n)) := makeCalls (initialState n) σ

/-! ## Helper functions about properties of `Nat`s. -/

/-- Suppose there exists a natural number satisfying φ.
Then there exists a *minimal* natural number that satisfies φ. -/
lemma exists_to_minimal_exists (φ : Nat → Prop):
    (∃ k, φ k) → (∃ m, φ m ∧ ∀ n < m, ¬ φ n) := by
  intro ⟨k, h_k⟩
  induction k using Nat.strong_induction_on
  case h k IH =>
    cases k
    case zero =>
      use 0
      constructor
      · exact h_k
      · simp
    case succ k =>
      by_cases φ k
      case pos h =>
        exact IH k (by simp) h
      case neg h =>
        by_cases ∃ l < k, φ l
        case pos hl =>
          rcases hl with ⟨l, l_lt_, phi_l⟩
          exact IH l (by linarith) phi_l
        case neg hl =>
          use k + 1
          constructor
          · exact h_k
          · intro j j_lt_k_succ
            rw [@Nat.lt_add_one_iff_lt_or_eq] at j_lt_k_succ
            cases j_lt_k_succ
            · simp at hl
              apply hl
              assumption
            · convert h

/-- f(n) = k -/
def is_f n k :=
  ∃ σ : List (Call n), allExpert (after σ)
  ∧ σ.length = k
  ∧ ¬ ∃ σ' : List (Call n), allExpert (after σ') ∧ σ'.length < k

def is_f_leq n k :=
  ∃ σ : List (Call n), allExpert (after σ)
  ∧ σ.length ≤  k

/-- Nobody hears their own secret in the given sequence, i.e. before each call
in the sequence, the agents in that call do not know each other's secrets. -/
def noHo (σ : List (Call n)) : Prop :=
  ∀ i : Fin σ.length,
      ¬ (after (σ.take (i - 1))) σ[i].fst σ[i].snd
    ∧ ¬ (after (σ.take (i - 1))) σ[i].snd σ[i].fst

def phi (n : Nat) : Prop :=
  n > 4 ∧ is_f_leq n (2*n - 5)

def is_minimal (m : Nat) :=
  phi m
  ∧ ∀ n < m, ¬ phi n -- note: corrected > to be < here.

/-- Given a sequence `σ` of length `2m-5` or less that makes all `m` agents experts,
if `m` is minimal, then nobody hears their own secret in σ. -/
lemma noHo_of_minimal_expert_sequence (σ : List (Call m))
    (σ_short : σ.length ≤ 2 * m - 5)
    (hExp : allExpert (after σ))
    (h_min : is_minimal m)
    : noHo σ := by
    obtain ⟨h_phi, h_minimal⟩ := h_min
  -- rearranging argument
    sorry

theorem helper {k n} (h : 4 ≤ n) : k ≤ 2 * n - 5 ↔ k < 2 * n - 4 := by
  rw [Nat.two_mul]
  have := @Nat.add_one_le_iff (k + 4) (n + n)
  rw [add_assoc] at this
  simp at this
  have five_le : 5 ≤ n + n := by linarith
  rw [le_tsub_iff_right five_le]
  rw [this]
  exact Iff.symm Nat.lt_sub_iff_add_lt

/-- For n ≥ 4 agents, any sequence that makes everyone an expert, has length 2n-4 or higher. -/
theorem necessity :
    ∀ n > 4, ∀ σ : List (Call n), allExpert (after σ) → σ.length ≥ 2*n - 4 := by
  by_contra hyp
  simp only [gt_iff_lt, ge_iff_le, not_forall, not_le] at hyp
  -- FIXME later with newer lean: avoid `∃ _` proofs, `simp` does it but `simp only` does not.
  -- let φ n := ∃ (_ : 4 < n), ∃ σ : List (Call n), ∃ (h : allExpert (after σ)), σ.length < 2 * n - 4
  have := exists_to_minimal_exists _ hyp
  rcases this with ⟨m, ⟨le_m, ⟨S, S_allExp, S_len_lt⟩⟩, m_is_minimal⟩
  rw [← helper (by linarith)] at S_len_lt
  -- `m_is_minimal` is not yet exactly the right input for `noHo_of_minimal_expert_sequence`.
  have is_minimal_m : is_minimal m := by
    simp at m_is_minimal
    unfold is_minimal phi is_f_leq
    simp
    constructor
    · exact ⟨le_m, S, ⟨S_allExp, S_len_lt⟩⟩
    · intro k k_lt_m four_lt_k
      intro σ σ_AllExp
      have := m_is_minimal k k_lt_m four_lt_k σ σ_AllExp
      simp_rw [@Nat.le_iff_lt_add_one] at this
      omega
  -- Now we can use the lemma.
  have noHo_S : noHo S := noHo_of_minimal_expert_sequence S S_len_lt S_allExp is_minimal_m

  -- TODO: define final and initial first
  -- have claim1 : sorry := sorry -- "all calls in S are final for both or neither"
  -- have claim2 : sorry := sorry -- "all calls in S are initial for both or neither"

  -- TODO: define graph

  let initPart : List (Call m) := sorry
  let midPart : List (Call m) := sorry
  let finalPart : List (Call m) := sorry

  have : S.length = initPart.length + midPart.length + finalPart.length := by
    sorry

  have : m / 2 = initPart.length := by sorry

  have : m / 2 = finalPart.length := by sorry

  have : m = initPart.length + finalPart.length := by sorry -- division problem?

  have len_s_at_least : m ≤ S.length := by linarith

  have : midPart.length ≤ m - 5 := by sorry -- or was it flipped around?

  sorry
