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

#print List.countP

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

/-- Nobody hears their own secret in the given sequence, i.e. before each call
in the sequence, the agents in that call do not know each other's secrets. -/
def noHo (σ : List (Call n)) : Prop :=
  ∀ i : Fin σ.length,
      ¬ (after (σ.take (i - 1))) σ[i].fst σ[i].snd
    ∧ ¬ (after (σ.take (i - 1))) σ[i].snd σ[i].fst

/-- Number of calls that k directly participates in. -/
def v (S : List (Call m)) (k : Fin m) : Nat := -- easy?
  --S.foldl (λ (counter c) => ite (c.fst = k ∨ c.snd = k) (counter + 1) counter) 0
  S.countP (λ (c : Call m) => c.fst = k ∨ c.snd = k)

#eval v [(1,2),(0,6),(7,2)] (2 : Fin 10)

/-- Among n agents, to make k an expert, we need at least n-1 calls. -/
lemma exp_needs_n_min_one_calls (S : List (Call n))
    (h : isExpert (after S) k)
    : n - 1 < S.length := by
  sorry

/-- Among n agents, to make everyone know k's secret, we need at least n-1 calls. -/
lemma known_needs_n_min_one_calls (S : List (Call n))
    (h : allKnow (after S) k)
    : n - 1 < S.length := by
  sorry

/-- Given a noHo sequence, to make k an expert and make everyone know k, we need this many calls. -/
lemma noHo_exp_and_known_needs_many_calls (S : List (Call n))
    (S_noHo : noHo S)
    (k : Fin n)
    (h : isExpert (after S) k)
    (h2 : allKnow (after S) k)
    : 2 * n - 2 - v S k ≤ S.length := by
  -- use Lemma 6 "calls needed for both spreading and informing are those in v S k"
  sorry

/-- f(n) = k -/
def is_f n k :=
  ∃ σ : List (Call n), allExpert (after σ)
  ∧ σ.length = k
  ∧ ¬ ∃ σ' : List (Call n), allExpert (after σ') ∧ σ'.length < k

#check List.filter

def is_f_leq n k :=
  ∃ σ : List (Call n), allExpert (after σ)
  ∧ σ.length ≤  k

def phi (n : Nat) : Prop :=
  n > 4 ∧ is_f_leq n (2*n - 5)

def is_minimal (m : Nat) :=
  phi m
  ∧ ∀ n < m, ¬ phi n -- note: corrected > to be < here.

def initial (S : List (Call m)) (k : Fin m) : Option (Call m) :=
  S.find? (λ c => c.fst = k ∨ c.snd = k)

#eval initial [(4, 3), (0, 2), (0, 3)] (0 : Fin 5)

def final (S : List (Call m)) (k : Fin m) : Option (Call m) :=
  S.reverse.find? (λ c => c.fst = k ∨ c.snd = k)

#eval final [(4, 3), (0, 2), (0, 3), (2, 4)] (0 : Fin 5)

def isAgentInitialCall (S : List (Call m)) (k : Fin m) (c : Call m) : Bool :=
  initial S k = c

#eval isAgentInitialCall [(4, 3), (0, 2), (0, 3)] (0 : Fin 5) (0, 3)

def isAgentFinalCall (S : List (Call m)) (k : Fin m) (c : Call m) : Bool :=
  final S k = c

#eval isAgentFinalCall [(4, 3), (0, 2), (0, 3)] (0 : Fin 5) (0, 3)

def isInitialCall (S : List (Call m)) (c : Call m) : Bool :=
  isAgentInitialCall S c.fst c ∨ isAgentInitialCall S c.snd c

#eval isInitialCall ([(4, 3), (0, 2), (0, 3), (2, 3)] : List (Call 5)) (2, 3)

#eval isAgentInitialCall [(4, 3), (0, 2), (0, 3)] (0 : Fin 5) (0, 3)
#eval isAgentInitialCall ([(4, 3), (0, 2), (0, 3)] : List (Call 4)) 0 (0, 2)

def isFinalCall (S : List (Call m)) (c : Call m) : Bool :=
  isAgentFinalCall S c.fst c ∨ isAgentFinalCall S c.snd c

#eval isAgentFinalCall [(4, 3), (0, 2), (0, 3)] (0 : Fin 5) (0, 3)
#eval isAgentFinalCall ([(4, 3), (0, 2), (0, 3)] : List (Call 4)) 0 (0, 2)

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

  -- 1.3 Graph Building -- TODO


  let initPart : List (Call m) :=
  -- ∀(a : Fin m) ∈ S, ∀(c : Call m) ∈ S, isInitialCall S a c
  S.filter (fun c => (isInitialCall S c))

  let midPart : List (Call m) := sorry

  let finalPart : List (Call m) :=
  S.filter (fun c => (isFinalCall S c))


  have : S.length = initPart.length + midPart.length + finalPart.length := by
    sorry

  have : m / 2 = initPart.length := by sorry

  have : m / 2 = finalPart.length := by sorry

  have : m = initPart.length + finalPart.length := by sorry -- division problem?

  have len_s_at_least : m ≤ S.length := by linarith

  have : midPart.length ≤ m - 5 := by sorry -- or was it flipped around?

  -- number of calls that do not affect what k learns or who learns k
  let c : (k : Fin m) → Nat := sorry -- hard?

  -- Now we show "S.length > 2.5 * m".
  have : 5 * m < 2 * S.length := by
    have : ∀ k, 2 * m - 2 - v S k + c k ≤ 2 * m - 5 := by
      sorry
    have S_len_def : ∀ k, S.length = 2 * m - 2 - v S k + c k := by
      intro k
      have := noHo_exp_and_known_needs_many_calls S noHo_S k ?_ ?_
      sorry -- need def of c first
      · intro j; apply S_allExp
      · intro j; apply S_allExp

    have := S_len_def ⟨0, Nat.zero_lt_of_lt le_m⟩
    rewrite [this]
    sorry

  -- contradiction :-)
  omega
