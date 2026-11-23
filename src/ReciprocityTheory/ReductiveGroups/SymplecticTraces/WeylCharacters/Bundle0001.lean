module

public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.AntitoneOfMemInterl

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.BlockCombStatement
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

def numK {K : Type*} [Field K] {n : ℕ} (ε : Fin n → Bool) (a : Fin n → ℤ) (t : Fin n → K) : K :=
  ∑ σ ∈ (univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => ∀ i, ε (σ i) = ε i),
    ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, t (σ i) ^ a i

def wdenK {K : Type*} [Field K] {n : ℕ} (ε : Fin n → Bool) (t : Fin n → K) : K :=
  ∏ i : Fin n, ∏ j : Fin n, if i < j ∧ ε i = ε j then t i - t j else 1

def rhoK {n : ℕ} (ε : Fin n → Bool) : Fin n → ℤ :=
  fun i => ((univ.filter fun j : Fin n => i < j ∧ ε j = ε i).card : ℤ)

def cnt {n : ℕ} (ε : Fin n → Bool) (b : Bool) : ℕ := (univ.filter fun i : Fin n => ε i = b).card

def blk {n : ℕ} (ε : Fin n → Bool) (b : Bool) : Fin (cnt ε b) → Fin n :=
  fun r => (univ.filter fun i : Fin n => ε i = b).orderEmbOfFin rfl r

def BlockCombStatement : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (ε : Fin n → Bool) (a : Fin n → ℤ) (t : Fin n → K),
    wdenK ε t = wden (cnt ε true) (t ∘ blk ε true) * wden (cnt ε false) (t ∘ blk ε false) ∧
    numK ε a t = alt (cnt ε true) (a ∘ blk ε true) (t ∘ blk ε true) *
      alt (cnt ε false) (a ∘ blk ε false) (t ∘ blk ε false) ∧
    ∀ b : Bool, rhoK ε ∘ blk ε b = delta (cnt ε b)

theorem blk_mem {n : ℕ} (ε : Fin n → Bool) (b : Bool) (r : Fin (cnt ε b)) : ε (blk ε b r) = b := by
  have h := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = b) rfl r
  exact (Finset.mem_filter.mp h).2

theorem blk_strictMono {n : ℕ} (ε : Fin n → Bool) (b : Bool) : StrictMono (blk ε b) :=
  fun _ _ h => (Finset.orderEmbOfFin (univ.filter fun i : Fin n => ε i = b) rfl).strictMono h

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Branch
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

theorem gtChar_zero {K : Type*} [Field K] : ∀ (n : ℕ) (t : Fin n → K), gtChar n 0 t = 1
  | 0, _ => rfl
  | n + 1, t => by
    rw [gtChar]
    have h : interl (0 : Fin (n + 1) → ℤ) = {0} := by
      ext mu
      simp only [interl, Fintype.mem_piFinset, Pi.zero_apply, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · intro h; funext i; have := h i; simp only [Pi.zero_apply]; omega
      · rintro rfl i; simp
    rw [h, Finset.sum_singleton, gtChar_zero n]
    simp [wsum]

end ReciprocityTheory.ChartRestriction.TR.Weyl
end
end

