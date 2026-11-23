module

public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HermitianFormBaseVectorRight
section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section hpk
variable (k r : ℕ)

theorem hpk_out' {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mid' {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mulVec' (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  simp only [mulVec, dotProduct]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    simp only [hpk_out' k r h1]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp
  · rw [if_neg h1]
    simp only [hpk_mid' k r h1]
    rw [Finset.sum_eq_single i]
    · split_ifs <;> first | (exfalso; omega) | simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp

theorem hpk_conjT' : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [conjTranspose_apply, Hpk, Fin.mk.injEq]
  split_ifs <;> first | (exfalso; omega) | simp

theorem herm_bvec (v : Fin (2 * r + k + 1) → ℂ) (q : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec q) v = star ((Hpk k r *ᵥ v) q) := by
  have hc : ∀ p, star (Hpk k r q p) = Hpk k r p q := fun p => by
    have := congrFun (congrFun (hpk_conjT' k r) p) q
    rwa [conjTranspose_apply] at this
  unfold herm bvec
  rw [mulVec_single_one]
  simp only [dotProduct, mulVec, star_sum, star_mul', hc, Pi.star_apply]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

end hpk

section vec
variable (k r' : ℕ)

theorem goodRowsProjector_apply_eq_sum (p : Fin (2 * (1 + r') + k + 1)) : e0 k r' p = if p.val = 0 then 1 else 0 := by
  unfold e0 bvec
  rw [Pi.single_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff]
  simp [eI, a0]

theorem last_basis_apply (p : Fin (2 * (1 + r') + k + 1)) :
    es0 k r' p = if p.val = 2 * (1 + r') + k then 1 else 0 := by
  unfold es0 bvec
  rw [Pi.single_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff]
  simp [esI, a0]

theorem liftVec_apply (z : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1)) :
    liftVec k 1 r' z p = if h : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 then z ⟨p.val - 1, by omega⟩ else 0 :=
  rfl

theorem liftVec_lev (z : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' z (levPos k 1 r' i) = z i := by
  rw [liftVec_apply, dif_pos (by simp [levPos]; omega)]
  congr 1

theorem liftVec_out (z : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1))
    (h : p.val = 0 ∨ p.val = 2 * (1 + r') + k) : liftVec k 1 r' z p = 0 := by
  rw [liftVec_apply, dif_neg (by omega)]

theorem bvec_lev (j : Fin (2 * r' + k + 1)) : bvec (levPos k 1 r' j) = liftVec k 1 r' (bvec j) := by
  ext p
  rw [liftVec_apply]
  simp only [bvec, Pi.single_apply, Fin.ext_iff, levPos]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hermitian_form_base_vector_right (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) u (e0 k r') = u ⟨2 * (1 + r') + k, by omega⟩ := by
  unfold herm
  simp only [dotProduct, Pi.star_apply, goodRowsProjector_apply_eq_sum]
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · rw [hpk_mulVec']; simp
  · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
  · simp

theorem hermitianForm_mulVec_basisSum : Hpk k (1 + r') *ᵥ es0 k r' = e0 k r' := by
  ext p
  rw [hpk_mulVec', goodRowsProjector_apply_eq_sum, last_basis_apply, last_basis_apply]
  split_ifs <;> (try simp only at *) <;> first | rfl | (exfalso; omega) | simp

theorem hermitian_dual_base_vector_left (v : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (es0 k r') v = star (v ⟨0, by omega⟩) := by
  unfold herm
  rw [hermitianForm_mulVec_basisSum]
  simp only [dotProduct, Pi.star_apply, goodRowsProjector_apply_eq_sum]
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · simp
  · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
  · simp

end vec

section lev
variable (k r' : ℕ)

theorem levPos_val (j : Fin (2 * r' + k + 1)) : (levPos k 1 r' j).val = j.val + 1 := rfl

theorem levPos_inj : Function.Injective (levPos k 1 r') := by
  intro a b h; ext; have := congrArg Fin.val h; simp only [levPos_val] at this; omega

theorem sum_lev {M : Type*} [AddCommMonoid M] (F : Fin (2 * (1 + r') + k + 1) → M)
    (hF : ∀ q : Fin (2 * (1 + r') + k + 1), ¬(1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1) → F q = 0) :
    ∑ q, F q = ∑ j : Fin (2 * r' + k + 1), F (levPos k 1 r' j) := by
  symm
  have e := Finset.sum_map Finset.univ ⟨levPos k 1 r', levPos_inj k r'⟩ F
  simp only [Function.Embedding.coeFn_mk] at e
  rw [← e]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro q _ hq
  apply hF
  rintro ⟨h1, h2⟩
  apply hq
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  exact ⟨⟨q.val - 1, by omega⟩, by ext; simp only [levPos_val]; omega⟩

theorem sum_lev_le (F : Fin (2 * (1 + r') + k + 1) → ℝ) (hF : ∀ q, 0 ≤ F q) :
    ∑ j : Fin (2 * r' + k + 1), F (levPos k 1 r' j) ≤ ∑ q, F q := by
  have e := Finset.sum_map Finset.univ ⟨levPos k 1 r', levPos_inj k r'⟩ F
  simp only [Function.Embedding.coeFn_mk] at e
  rw [← e]
  exact Finset.sum_le_univ_sum_of_nonneg hF

theorem ιLev_mulVec (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1)) :
    (ιLev k 1 r' g *ᵥ u) p = if h : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 then
      (g *ᵥ fun j => u (levPos k 1 r' j)) ⟨p.val - 1, by omega⟩ else u p := by
  simp only [mulVec, dotProduct]
  by_cases h : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · rw [dif_pos h, sum_lev k r']
    · apply Finset.sum_congr rfl
      intro j _
      have hj : 1 ≤ (levPos k 1 r' j).val ∧ (levPos k 1 r' j).val < 2 * r' + k + 1 + 1 := by
        rw [levPos_val]; omega
      simp only [ιLev, dif_pos h, dif_pos hj]
      congr 2
    · intro q hq
      simp only [ιLev, dif_pos h, dif_neg hq, zero_mul]
  · rw [dif_neg h]
    simp only [ιLev, dif_neg h]
    rw [Finset.sum_eq_single p]
    · simp
    · intro b _ hb; rw [if_neg (fun e => hb e.symm)]; simp
    · simp

theorem ιLev_liftVec (g : Mat k r') (z : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' g *ᵥ liftVec k 1 r' z = liftVec k 1 r' (g *ᵥ z) := by
  ext p
  rw [ιLev_mulVec, liftVec_apply]
  split_ifs with h
  · have e : (fun j => liftVec k 1 r' z (levPos k 1 r' j)) = z := funext (liftVec_lev k r' z)
    rw [e, liftVec_apply, dif_pos h]
  · rw [liftVec_apply, dif_neg h]

theorem ιLev_fix (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ)
    (hu : ∀ q : Fin (2 * (1 + r') + k + 1), (1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1) → u q = 0) :
    ιLev k 1 r' g *ᵥ u = u := by
  ext p
  rw [ιLev_mulVec]
  split_ifs with h
  · have : (fun j => u (levPos k 1 r' j)) = 0 := by
      ext j; apply hu; rw [levPos_val]; omega
    rw [this, mulVec_zero, hu p h]; rfl
  · rfl

theorem levi_embedding_mulVec_e0 (g : Mat k r') : ιLev k 1 r' g *ᵥ e0 k r' = e0 k r' :=
  ιLev_fix k r' g _ fun q hq => by rw [goodRowsProjector_apply_eq_sum, if_neg (by omega)]

theorem levelEmbedding_mulVec_es0 (g : Mat k r') : ιLev k 1 r' g *ᵥ es0 k r' = es0 k r' :=
  ιLev_fix k r' g _ fun q hq => by rw [last_basis_apply, if_neg (by omega)]

theorem reflection_apply_entries (c : ℂ) (p q : Fin (2 * (1 + r') + k + 1)) :
    w0 k r' c p q = if p.val = 0 ∧ q.val = 2 * (1 + r') + k then (star c)⁻¹
      else if p.val = 2 * (1 + r') + k ∧ q.val = 0 then c
      else if p = q ∧ 0 < p.val ∧ p.val < 2 * (1 + r') + k then 1 else 0 := rfl

theorem reflection_mulVec_levelPos (c : ℂ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) :
    (w0 k r' c *ᵥ u) (levPos k 1 r' i) = u (levPos k 1 r' i) := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single (levPos k 1 r' i)]
  · rw [reflection_apply_entries, if_neg (by rw [levPos_val]; omega), if_neg (by rw [levPos_val]; omega),
      if_pos ⟨rfl, by rw [levPos_val]; omega, by rw [levPos_val]; omega⟩, one_mul]
  · intro b _ hb
    rw [reflection_apply_entries, if_neg (by rw [levPos_val]; omega), if_neg (by rw [levPos_val]; omega),
      if_neg (fun h => hb h.1.symm), zero_mul]
  · simp

theorem rankOneMatrix_last_coord (c : ℂ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    (w0 k r' c *ᵥ u) ⟨2 * (1 + r') + k, by omega⟩ = c * u ⟨0, by omega⟩ := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · rw [reflection_apply_entries, if_neg (by simp only; omega), if_pos ⟨rfl, rfl⟩]
  · intro b _ hb
    have hb' : b.val ≠ 0 := fun h => hb (Fin.ext h)
    rw [reflection_apply_entries, if_neg (by simp only; omega), if_neg (by simp only; omega),
      if_neg (fun h => absurd h.2.2 (lt_irrefl _)), zero_mul]
  · simp

end lev

end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def Kset (k r : ℕ) : Set (Mat k r) := {g | g ∈ GV k r ∧ gᴴ * g = 1}

def epsV (k r : ℕ) : Fin (2 * r + k + 1) → ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (bvec (wI k r 0) + bvec (wI k r (Fin.last k)))

def phiV (k r : ℕ) (a : Fin (r + 1)) : Fin (2 * r + k + 1) → ℂ :=
  if h : a.val < r then bvec (esI k r ⟨a.val, h⟩) else epsV k r

def phiV' (k r : ℕ) (a : Fin (r + 1)) : Fin (2 * r + k + 1) → ℂ := Hpk k r *ᵥ phiV k r a

def Ga (k r : ℕ) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) : ℝ :=
  (Matrix.det (Matrix.of fun a b : Fin (l.val + 1) =>
    star (Y (Fin.castLE (by omega) a)) ⬝ᵥ Y (Fin.castLE (by omega) b))).re

def Del (k r : ℕ) (l : Fin (r + 1)) (x : Mat k r) : ℝ := Real.sqrt (Ga k r l fun a => x *ᵥ phiV k r a)

def Dl (k r : ℕ) (l : Fin (r + 1)) (g : Mat k r) : ℂ :=
  Matrix.det (Matrix.of fun a b : Fin (l.val + 1) =>
    herm (Hpk k r) (g *ᵥ phiV' k r (Fin.castLE (by omega) b)) (phiV' k r (Fin.castLE (by omega) a)))

def s0 (k r : ℕ) (l : Fin (r + 1)) : ℝ := if l.val < r then 2 else (k : ℝ)

def SAdm (k r : ℕ) (s : Fin (r + 1) → ℝ) : Prop := ∀ l, 0 < s0 k r l - s l ∧ s0 k r l - s l ≤ 1 / 10

def xiR (k r : ℕ) (s : Fin (r + 1) → ℝ) (x : Mat k r) : ℝ := ∏ l, Del k r l x ^ (-s l)

def xiN (k r : ℕ) (s : Fin (r + 1) → ℝ) (x : Mat k r) : ℝ≥0 := Real.toNNReal (xiR k r s x)

def FsE (k r : ℕ) (s : Fin (r + 1) → ℝ) (g : Mat k r) : ℝ≥0∞ := ∏ l, (‖Dl k r l g‖₊ : ℝ≥0∞) ^ (-s l)

def fsR (k r : ℕ) (s : Fin (r + 1) → ℝ) (x : Mat k r) : ℝ := ∏ l, Ga k r l (fun a => x *ᵥ phiV' k r a) ^ (-s l / 2)

def JInt {k r : ℕ} (μG : Measure (Mt k r)) (A : ℝ) (s : Fin (r + 1) → ℝ) : ℝ≥0∞ :=
  ∫⁻ g : Mt k r, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s (Matrix.of g) ∂μG

def IInt {k r : ℕ} (μN : Measure (Mt k r)) (z : Fin (2 * r + k + 1) → ℂ) (s : Fin (r + 1) → ℝ) (δ : ℝ) : ℝ≥0∞ :=
  ∫⁻ n : Mt k r, ENNReal.ofReal (xiR k r s (Matrix.of n)) *
    ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-δ)) ∂μN

def AAt (k r : ℕ) : Prop :=
  ∀ s, SAdm k r s → ∀ μG : Measure (Mt k r), IsHaarOn (GV k r) μG → ∀ A : ℝ, AB k r ≤ A → JInt μG A s < ∞

def BAt (k r : ℕ) (δ : ℝ) : Prop :=
  ∃ eS : ℝ, 0 < eS ∧ ∀ s : Fin (r + 1) → ℝ, (∀ l, 0 < s0 k r l - s l ∧ s0 k r l - s l ≤ eS) →
    ∀ z : Fin (2 * r + k + 1) → ℂ, inWb k r z → 0 < Tz k r z →
      ∀ μN : Measure (Mt k r), IsHaarOn (Nset k r) μN → IInt μN z s δ < ∞

def InductiveHeisenbergInputs : Prop :=
  OneStepInt ∧ OneStepCoord ∧ OneStepMem ∧ NRecHaar ∧ NBase ∧ HeisConjLev ∧ HeisConjLevMeas ∧ HeisInv ∧ HeisMul ∧
    HeisMem ∧ HeisClosed ∧ HeisHaar ∧ ConjInvAll ∧ CompactW ∧ GNIntSharp ∧ GNLower ∧ HaarUnique ∧ HaarInv ∧
    CompactHaarExists ∧ ClosedG ∧ ClosedN ∧ ClosedW ∧ LevHaar ∧ HaarWExists ∧ HaarNExists ∧
    HaarGExists ∧ HeisAct

def IW : Prop :=
  ∀ (k r : ℕ) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ), 1 ≤ k → LinearIndependent ℂ Y →
    (∀ a b, herm (Hpk k r) (Y a) (Y b) = 0) →
    ∃ κ ∈ Kset k r, ∃ τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, τ.BlockTriangular id ∧
      (∀ a, Y a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) ∧
      ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r l Y

def TLeft : Prop :=
  ∀ (k r : ℕ) (s : Fin (r + 1) → ℝ) (μG : Measure (Mt k r)) (Φ : Mt k r → ℝ≥0∞), 1 ≤ k → IsHaarOn (GV k r) μG →
    Measurable Φ → (∀ κ ∈ Kset k r, ∀ g, Φ (lmulM κ g) = Φ g) → ∀ x ∈ GV k r,
      (∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g) ∂μG) = ENNReal.ofReal (fsR k r s x) * ∫⁻ g, Φ g * FsE k r s (Matrix.of g) ∂μG

def TBoth : Prop :=
  ∀ (k r : ℕ) (s : Fin (r + 1) → ℝ) (μG : Measure (Mt k r)) (Φ : Mt k r → ℝ≥0∞), 1 ≤ k → IsHaarOn (GV k r) μG →
    Measurable Φ → (∀ κ ∈ Kset k r, ∀ g, Φ (lmulM κ g) = Φ g ∧ Φ (rmulF κ g) = Φ g) → ∀ x ∈ GV k r, ∀ y ∈ GV k r,
      (∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g * y) ∂μG) =
        ENNReal.ofReal (fsR k r s x * fsR k r s y) * ∫⁻ g, Φ g * FsE k r s (Matrix.of g) ∂μG

def DET : Prop :=
  ∀ (k r : ℕ) (s : Fin (r + 1) → ℝ) (A : ℝ), 1 ≤ k → (∀ l, 0 ≤ s l) → ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s l ≤ A →
    ∃ C : ℝ≥0, ∀ h ∈ GV k r, ENNReal.ofReal (gN h ^ (-A)) ≤ (C : ℝ≥0∞) * FsE k r s h

def CoefStep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) (A : ℝ)
    (s : Fin (r + 1) → ℝ), SAdm k r s → AB k r ≤ A → JInt D.μG A s < ∞ → CoefBound D (xiN k r s) A

def XiIntStep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (s : Fin (r + 1) → ℝ), SAdm k r s → IInt D.μN D.z s (1 / 2) < ∞ → IInt D.μN D.z' s (1 / 2) < ∞ →
      XiInt D (xiN k r s) 2

def hcoord (k r' : ℕ) (x : HPar k r') : Xp (1 + r') (k - 1) :=
  let a : Fin (1 + r') → ℂ := fun j => herm (Hpk k r') x.1 (phiV k r' (Fin.cast (by omega) j))
  let a' : Fin (1 + r') → ℂ := fun j => herm (Hpk k r') x.1 (phiV' k r' (Fin.cast (by omega) j))
  (a, a', (fun i : Fin (k - 1) => x.1 (wI k r' ⟨i.val + 1, by omega⟩)),
    x.2 + (∑ j, a' j * star (a j)).im)

def FormulaF : Prop :=
  ∀ k r' : ℕ, 1 ≤ k →
    (∀ (x : HPar k r') (l : Fin (1 + r' + 1)), Del k (1 + r') l (heis0 k r' x) = de (hcoord k r' x) l) ∧
    MeasurePreserving (hcoord k r') volume volume

def AStepSucc : Prop := ∀ k r r' : ℕ, r = 1 + r' → 1 ≤ k → AAt k r' → AAt k r

def AStepBase : Prop := ∀ k : ℕ, 1 ≤ k → AAt k 0

def BStepSucc : Prop := ∀ k r r' : ℕ, r = 1 + r' → 1 ≤ k → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → BAt k r' (δ / 4) → BAt k r δ

def BStepBase : Prop := ∀ k : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → BAt k 0 δ

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

