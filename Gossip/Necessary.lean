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

/-- Helper about properties of `Nat`s. Move to helper file. -/
lemma exists_to_minimal_exists (φ : Nat → Prop):
    (∃ k, φ k) → (∃ m, φ m ∧ ∀ n < m, ¬ φ n) := by
  intro ⟨k, h_k⟩
  induction k using Nat.strong_induction_on
  case h k IH =>
    cases k
    case zero =>
      use 0
      constructor
      · assumption
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

/-- Nobody hears their own sequence. -/
def noHo (σ : List (Call n)) : Prop :=
  ∀ i : Fin σ.length,
      ¬ (after (σ.take (i - 1))) σ[i].fst σ[i].snd
    ∧ ¬ (after (σ.take (i - 1))) σ[i].snd σ[i].fst

/-- Given a sequence of length 2n-4 or less that makes all agents experts,
before each of the calls of the sequence, the agents in that call do
not know each other's secrets. -/
lemma noHo_of_minimal_expert_sequence (σ : List (Call n))
    (h : σ.length ≤ 2 * n - 5)
    (hExp : allExpert (after σ))
    -- FIXME: needs extra assumptions about minimality
    : noHo σ := by
  -- rearranging argument
  sorry

theorem bla : ∀ n, is_f n (2*n -4) := by
  by_contra hyp
  rw [not_forall] at hyp
  have := exists_to_minimal_exists _ hyp
  simp at this
  rcases hyp with ⟨x, hx⟩
  rcases this with ⟨m, hm, h_min⟩
  by_cases h : x < m
  case pos =>
    have := h_min _ h
    exact hx this
  case neg =>
    simp at h
    rcases lt_or_eq_of_le h with h_less | h_eq
    case inl =>
      -- have := h_min _ h_less
      sorry
    case inr =>
      -- have := hx _ h_eq
      sorry

/-
/-- For n ≥ 4 agents, any sequence of 2n-5 or fewer calls cannot make everyone experts. -/
theorem low_not_sufficient (h : n ≥ 4) (σ : List (Call n))
    (hLen : σ.length ≤ 2*n - 5)
    : ¬ allExpert (after σ) := by
  have no_hears_own := noSelfHearing σ hLen
  sorry
-/

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
    ∀ n ≥ 4, ∀ σ : List (Call n), allExpert (after σ) → σ.length ≥ 2*n - 4 := by
  by_contra hyp
  simp only [ge_iff_le, not_forall, not_le] at hyp
  -- let φ n := ∃ (_ : 4 ≤ n), ∃ σ : List (Call n), ∃ (h : allExpert (after σ)), σ.length < 2 * n - 4
  have := exists_to_minimal_exists _ hyp
  rcases this with ⟨m, ⟨le_m, ⟨S, S_allExp, S_len_lt⟩⟩, m_is_minimal⟩

  rw [← helper le_m] at S_len_lt

  have noHo_S : noHo S := by
    apply noHo_of_minimal_expert_sequence
    -- TODO ;-)
    all_goals assumption

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
