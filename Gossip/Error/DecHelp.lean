
theorem exists_in_all_iff_exists {α} {all : List α} (all_spec : ∀ x, x ∈ all) {P : α → Prop} :
    (∃ x ∈ all, P x) ↔ (∃ x, P x) := by
  grind

def Decidable.exists_of_list_mem {α} {all : List α} (all_spec : ∀ x, x ∈ all) {P : α → Prop}
    (h : DecidablePred P) : Decidable (∃ x, P x) := by
  apply @decidable_of_iff (∃ x, P x) (∃ x ∈ all, P x) (exists_in_all_iff_exists all_spec)

theorem forall_in_all_iff_forall {α} {all : List α} (all_spec : ∀ x, x ∈ all) {P : α → Prop} :
    (∀ x ∈ all, P x) ↔ (∀ x, P x) := by
  grind

def Decidable.forall_of_list_mem {α} {all : List α} (all_spec : ∀ x, x ∈ all) {P : α → Prop}
    (h : DecidablePred P) : Decidable (∀ x, P x) := by
  apply @decidable_of_iff (∀ x, P x) (∀ x ∈ all, P x) (forall_in_all_iff_forall all_spec)

def Decidable.forall_implies_of_list_mem {α} {P Q : α → Prop} (all : List α)
    (all_spec : ∀ x, Q x ↔ x ∈ all) (h : DecidablePred P)
    : Decidable (∀ x, Q x → P x) := by
  have : Decidable (∀ (x : α), x ∈ all → P x) := List.decidableBAll P all
  apply @decidable_of_iff _ (∀ (x : α), x ∈ all → P x)
  grind

def Decidable.forall_attach_list {α} {L : List α} {P : {x : α // x ∈ L} → Prop}
    (h : DecidablePred P) : Decidable (∀ x, ∀ h : x ∈ L, P ⟨x, h⟩) := by
  apply @decidable_of_iff (∀ (x : α) (h : x ∈ L), P ⟨x, h⟩) (∀ x ∈ L.attach, P x) ?_ ?_
  · grind
  · apply @Decidable.forall_of_list_mem _ L.attach (by simp)
    simp
    exact h
