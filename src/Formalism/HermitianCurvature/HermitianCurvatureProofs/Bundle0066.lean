module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0058
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0030
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDomainMeasurable
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
public import Formalism.HermitianCurvature.Bundle0009
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliCoordinates

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermFibreKernels
section
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section propG

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem eventually_ne_cocompact (c : ℂ) : ∀ᶠ x in cocompact ℂ, x ≠ c := by
  filter_upwards [(isCompact_singleton : IsCompact ({c} : Set ℂ)).compl_mem_cocompact] with x hx
  simpa using hx

theorem eventually_rate_cocompact (σ : ℂ) (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in cocompact ℂ, C * ‖x + σ‖⁻¹ ≤ δ := by
  have h0 : Tendsto (fun x : ℂ => ‖x‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  have h := h0.eventually_ge_atTop (‖σ‖ + |C| / δ + 1)
  filter_upwards [h] with x hx
  have h1 : |C| / δ + 1 ≤ ‖x + σ‖ := by
    have := norm_sub_norm_le x (-σ)
    rw [norm_neg, sub_neg_eq_add] at this
    linarith
  have hpos : 0 < ‖x + σ‖ := lt_of_lt_of_le (by positivity) h1
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  have h2 : |C| = δ * (|C| / δ) := by
    first
    | (field_simp; ring)
    | field_simp
  calc C ≤ |C| := le_abs_self C
    _ = δ * (|C| / δ) := h2
    _ ≤ δ * ‖x + σ‖ := by
        apply mul_le_mul_of_nonneg_left _ hδ.le
        linarith

theorem integral_sq_sub_le {μ : Measure ℂ} {u a : ℂ → H} {ab : ℂ → ℝ} (hu : MemLp u 2 μ) (ha : MemLp a 2 μ)
    (hab : MemLp ab 2 μ) (hd : ∀ᵐ D ∂μ, ‖a D‖ ≤ ab D) :
    ∫ D, ‖u D - a D‖ ^ 2 ∂μ ≤ 2 * ∫ D, ‖u D‖ ^ 2 ∂μ + 2 * ∫ D, ab D ^ 2 ∂μ := by
  have i1 : Integrable (fun D => ‖u D - a D‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hu.sub ha).aestronglyMeasurable).1 (hu.sub ha)
  have i2 : Integrable (fun D => ‖u D‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have i3 : Integrable (fun D => ab D ^ 2) μ := (memLp_two_iff_integrable_sq hab.aestronglyMeasurable).1 hab
  calc ∫ D, ‖u D - a D‖ ^ 2 ∂μ ≤ ∫ D, (2 * ‖u D‖ ^ 2 + 2 * ab D ^ 2) ∂μ := by
        refine integral_mono_ae i1 ((i2.const_mul 2).add (i3.const_mul 2)) ?_
        filter_upwards [hd] with D hD
        have h1 : ‖u D - a D‖ ≤ ‖u D‖ + ‖a D‖ := norm_sub_le _ _
        have h2 : 0 ≤ ‖a D‖ := norm_nonneg _
        have h3 : 0 ≤ ‖u D - a D‖ := norm_nonneg _
        have e1 : ‖u D - a D‖ ^ 2 ≤ (‖u D‖ + ‖a D‖) ^ 2 := pow_le_pow_left₀ h3 h1 2
        have e2 : ‖a D‖ ^ 2 ≤ ab D ^ 2 := pow_le_pow_left₀ h2 hD 2
        nlinarith [sq_nonneg (‖u D‖ - ‖a D‖)]
    _ = 2 * ∫ D, ‖u D‖ ^ 2 ∂μ + 2 * ∫ D, ab D ^ 2 ∂μ := by
        rw [integral_add (i2.const_mul 2) (i3.const_mul 2), integral_const_mul, integral_const_mul]

variable {ι : Type} {μ : Measure ℂ} {Y : Finset ι} {U A : ι × ℂ → ℂ → H} {N : ℂ → ι → ι → ℂ}

end propG

end

end Formalism.FourierDecayAlt.P.PBK
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLevelMinors
section
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.HeisenbergLevelMinors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma norm_le_gN (M : Mat k r) : ‖M‖ ≤ gN M := by
  have hg : gN M = Real.sqrt (∑ i, ∑ j, Complex.normSq (M i j)) := rfl
  rw [hg, Matrix.norm_le_iff (Real.sqrt_nonneg _)]
  intro i j
  have h2 : ‖M i j‖ ^ 2 ≤ ∑ i, ∑ j, Complex.normSq (M i j) := by
    rw [← Complex.normSq_eq_norm_sq]
    calc Complex.normSq (M i j) ≤ ∑ j', Complex.normSq (M i j') :=
          Finset.single_le_sum (f := fun j' => Complex.normSq (M i j'))
            (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', Complex.normSq (M i' j') :=
          Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (M i' j'))
            (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  calc ‖M i j‖ = |‖M i j‖| := (abs_of_nonneg (norm_nonneg _)).symm
    _ ≤ _ := Real.abs_le_sqrt h2

lemma gN_unit {X : Mat k r} (hX : ∀ i j, ‖X i j‖ ≤ 1) : gN X ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
  have hg : gN X = Real.sqrt (∑ i, ∑ j, Complex.normSq (X i j)) := rfl
  have h1 : ∀ i j, Complex.normSq (X i j) ≤ 1 := fun i j => by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hX i j, norm_nonneg (X i j)]
  have hs : (∑ i, ∑ j, Complex.normSq (X i j)) ≤
      ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := by
    calc (∑ i, ∑ j, Complex.normSq (X i j))
        ≤ ∑ _i : Fin (2 * r + k + 1), ∑ _j : Fin (2 * r + k + 1), (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
      _ = ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hg]
  calc Real.sqrt _ ≤ Real.sqrt (((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ)) :=
        Real.sqrt_le_sqrt hs
    _ = _ := Real.sqrt_mul_self (Nat.cast_nonneg _)

lemma gN_conjT (M : Mat k r) : gN Mᴴ = gN M := by
  show Real.sqrt _ = Real.sqrt _
  congr 1
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  exact Finset.sum_comm

private lemma gN_mul_le_hermitian_curvature (A B : Mat k r) : gN (A * B) ≤ gN A * gN B := by
  have hA : gN A = Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j)) := rfl
  have hB : gN B = Real.sqrt (∑ i, ∑ j, Complex.normSq (B i j)) := rfl
  have hAB : gN (A * B) = Real.sqrt (∑ i, ∑ j, Complex.normSq ((A * B) i j)) := rfl
  have hSA : 0 ≤ ∑ i, ∑ j, Complex.normSq (A i j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have entry : ∀ i j, Complex.normSq (∑ l, A i l * B l j) ≤
      (∑ l, Complex.normSq (A i l)) * (∑ l, Complex.normSq (B l j)) := by
    intro i j
    rw [Complex.normSq_eq_norm_sq]
    have h1 : ‖∑ l, A i l * B l j‖ ≤ ∑ l, ‖A i l‖ * ‖B l j‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => norm_mul _ _))
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖A i l‖) (fun l => ‖B l j‖)
    have h3 : ∀ l, Complex.normSq (A i l) = ‖A i l‖ ^ 2 := fun l => Complex.normSq_eq_norm_sq _
    have h4 : ∀ l, Complex.normSq (B l j) = ‖B l j‖ ^ 2 := fun l => Complex.normSq_eq_norm_sq _
    simp only [h3, h4]
    have h5 : ‖∑ l, A i l * B l j‖ ^ 2 ≤ (∑ l, ‖A i l‖ * ‖B l j‖) ^ 2 := by
      have := norm_nonneg (∑ l, A i l * B l j)
      nlinarith
    exact h5.trans h2
  have hS : (∑ i, ∑ j, Complex.normSq ((A * B) i j)) ≤
      (∑ i, ∑ j, Complex.normSq (A i j)) * (∑ i, ∑ j, Complex.normSq (B i j)) := by
   calc (∑ i, ∑ j, Complex.normSq ((A * B) i j))
      = ∑ i, ∑ j, Complex.normSq (∑ l, A i l * B l j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          congrArg Complex.normSq Matrix.mul_apply
    _ ≤ ∑ i, ∑ j, (∑ l, Complex.normSq (A i l)) * (∑ l, Complex.normSq (B l j)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => entry i j
    _ = (∑ i, ∑ l, Complex.normSq (A i l)) * (∑ j, ∑ l, Complex.normSq (B l j)) := by
        rw [Finset.sum_mul_sum]
    _ = (∑ i, ∑ j, Complex.normSq (A i j)) * (∑ i, ∑ j, Complex.normSq (B i j)) := by
        rw [Finset.sum_comm (f := fun j l => Complex.normSq (B l j))]
  rw [hA, hB, hAB]
  exact (Real.sqrt_le_sqrt hS).trans (le_of_eq (Real.sqrt_mul hSA _))

lemma gN_inv_le {g : Mat k r} (hg : g ∈ GV k r) : gN g⁻¹ ≤ gN (Hpk k r) ^ 2 * gN g := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  rw [Matrix.inv_eq_left_inv hl]
  have h0 : ∀ M : Mat k r, 0 ≤ gN M := fun M => Real.sqrt_nonneg _
  calc gN (Hpk k r * gᴴ * Hpk k r) ≤ gN (Hpk k r * gᴴ) * gN (Hpk k r) := gN_mul_le_hermitian_curvature _ _
    _ ≤ gN (Hpk k r) * gN gᴴ * gN (Hpk k r) :=
        mul_le_mul_of_nonneg_right (gN_mul_le_hermitian_curvature _ _) (h0 _)
    _ = gN (Hpk k r) ^ 2 * gN g := by rw [gN_conjT]; ring

section vol

open Formalism.FourierDecayAlt.P.B2x6

variable {k r' : ℕ}

end vol

end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IdentityOperator
section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

theorem identity_operator : TL.IdOp := by
  intro k r Wp Wq _ _ _ _ _ Bs
  let T : B.DTerm k r Wp Wq :=
    { coef := fun _ => 1
      coefAdj := fun _ => 1
      word := []
      word_lie := fun X hX => by simp at hX
      adj_id := fun _ _ _ => rfl }
  have hap : ∀ F, B.opApply [T] F = F := by
    intro F
    funext g
    simp [B.opApply, B.Rw, T]
  refine ⟨[T], ⟨?_, ?_, ?_⟩, hap⟩
  · intro T' hT'
    simp only [List.mem_singleton] at hT'
    subst hT'
    refine ⟨?_, ?_⟩ <;> intro g₀ _ <;>
      refine ⟨Set.univ, fun _ => 1, ?_, Set.mem_univ _, ?_, fun _ _ _ => rfl⟩
    all_goals
      first
      | exact isOpen_univ
      | exact contDiffOn_const
      | (open scoped Formalism.FourierDecayAlt.B in exact contDiffOn_const)
      | (open scoped Matrix.Norms.Elementwise in exact contDiffOn_const)
      | (open scoped Matrix.Norms.Operator in exact contDiffOn_const)
      | exact @contDiffOn_const _ _ _ _ _ _ _ _ _ _ _ _
  · intro p _ f _ g _
    simp only [hap]
  · intro T' hT'
    simp only [List.mem_singleton] at hT'
    subst hT'
    refine ⟨fun _ => 1, 0, 0, 0, [], ⟨1, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp
    · intro g
      simp
    · intro l _ _
      simp
    · simp [T]
    · simp
    · intro g _
      simp [C6.monoM, C6.Epart, T]

end

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LieListProducts
section
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LieListProducts

theorem alg_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (a b : ℂ) (A₁ A₂ : M) :
    (a • A₁ - b • A₂) + Complex.I • (a • A₂ + b • A₁) = (a + b * Complex.I) • (A₁ + Complex.I • A₂) := by
  have h : Complex.I • Complex.I • A₂ = -A₂ := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [smul_add, add_smul, mul_smul, h]
  module

theorem alg_bracket {R : Type*} [Ring R] [Algebra ℂ R] (A₁ A₂ B₁ B₂ : R) :
    (A₁ + Complex.I • A₂) * (B₁ + Complex.I • B₂) - (B₁ + Complex.I • B₂) * (A₁ + Complex.I • A₂) =
      ((A₁ * B₁ - B₁ * A₁) - (A₂ * B₂ - B₂ * A₂)) + Complex.I • ((A₁ * B₂ - B₂ * A₁) + (A₂ * B₁ - B₁ * A₂)) := by
  have h : ∀ x : R, Complex.I • Complex.I • x = -x := fun x => by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, h]
  module

section Lie

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

theorem lie_zero : InLieW k r z 0 := by
  refine ⟨⟨by simp, fun a _ => ⟨by simp, by simp⟩⟩, by simp⟩

theorem lie_add {X Y : Mx k r} (hX : InLieW k r z X) (hY : InLieW k r z Y) : InLieW k r z (X + Y) := by
  refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    have h1 := hX.1.1
    have h2 := hY.1.1
    calc _ = (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [h1, h2, add_zero]
  · rw [Matrix.add_mulVec, (hX.1.2 a ha).1, (hY.1.2 a ha).1, add_zero]
  · rw [Matrix.add_mulVec, (hX.1.2 a ha).2, (hY.1.2 a ha).2, add_zero]
  · rw [Matrix.add_mulVec, hX.2, hY.2, add_zero]

theorem lie_smul {X : Mx k r} (hX : InLieW k r z X) (s : ℝ) : InLieW k r z ((s : ℂ) • X) := by
  refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    have : star (s : ℂ) = (s : ℂ) := Complex.conj_ofReal s
    rw [this, ← smul_add, hX.1.1, smul_zero]
  · rw [Matrix.smul_mulVec, (hX.1.2 a ha).1, smul_zero]
  · rw [Matrix.smul_mulVec, (hX.1.2 a ha).2, smul_zero]
  · rw [Matrix.smul_mulVec, hX.2, smul_zero]

theorem lie_sub {X Y : Mx k r} (hX : InLieW k r z X) (hY : InLieW k r z Y) : InLieW k r z (X - Y) := by
  have := lie_add hX (lie_smul hY (-1))
  simpa [sub_eq_add_neg] using this

theorem conj_lie {X : Mx k r} (hX : InLieW k r z X) : (Hpk k r)⁻¹ * Xᴴ * Hpk k r = -X := by
  have h : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX.1.1
  rw [Qx8.hpk_inv, Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc, WeylGroupFacts.hpk_sq, Matrix.one_mul]

theorem hpart1_lie {X : Mx k r} (hX : InLieW k r z X) : hpart1 (Hpk k r) X = X := by
  unfold hpart1
  rw [conj_lie hX, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
  norm_num

theorem hpart2_lie {X : Mx k r} (hX : InLieW k r z X) : hpart2 (Hpk k r) X = 0 := by
  unfold hpart2
  rw [conj_lie hX, add_neg_cancel, smul_zero]

theorem hpart1_comb {X₁ X₂ : Mx k r} (h1 : InLieW k r z X₁) (h2 : InLieW k r z X₂) :
    hpart1 (Hpk k r) (X₁ + Complex.I • X₂) = X₁ := by
  rw [CapelliCoordinates.hpart1_add, CapelliCoordinates.hpart1_smul, hpart1_lie h1, hpart1_lie h2, hpart2_lie h2]
  simp

theorem hpart2_comb {X₁ X₂ : Mx k r} (h1 : InLieW k r z X₁) (h2 : InLieW k r z X₂) :
    hpart2 (Hpk k r) (X₁ + Complex.I • X₂) = X₂ := by
  rw [CapelliCoordinates.hpart2_add, CapelliCoordinates.hpart2_smul, hpart2_lie h1, hpart1_lie h2, hpart2_lie h2]
  simp

theorem hsum (Z : Mx k r) : hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z = Z := by
  unfold hpart1 hpart2
  rw [smul_smul]
  have e : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp [Complex.I_ne_zero]
  rw [e, ← smul_add, sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]
  norm_num

theorem gl_comb {X₁ X₂ : Mx k r} (h1 : InLieW k r z X₁) (h2 : InLieW k r z X₂) :
    InGlW k r z (X₁ + Complex.I • X₂) := by
  unfold InGlW
  rw [hpart1_comb h1 h2, hpart2_comb h1 h2]
  exact ⟨h1, h2⟩

theorem ec_comb {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (π : Mx k r → (W →L[ℂ] W))
    {X₁ X₂ : Mx k r} (h1 : InLieW k r z X₁) (h2 : InLieW k r z X₂) :
    ecOp π (X₁ + Complex.I • X₂) = dOp π X₁ + Complex.I • dOp π X₂ := by
  unfold ecOp
  rw [hpart1_comb h1 h2, hpart2_comb h1 h2]

end Lie

end LieListProducts

open LieListProducts in
theorem qr_ecLie_of : Qr.DOpLin → Qr.DOpBracket → Qr.EcLie := by
  intro hLin hBr W _ _ _ k r z π hπ Z Z' hZ hZ'
  obtain ⟨hX₁, hX₂⟩ := hZ
  obtain ⟨hY₁, hY₂⟩ := hZ'
  have eZ := hsum Z
  have eZ' := hsum Z'
  set X₁ := hpart1 (Hpk k r) Z
  set X₂ := hpart2 (Hpk k r) Z
  set Y₁ := hpart1 (Hpk k r) Z'
  set Y₂ := hpart2 (Hpk k r) Z'
  have dadd : ∀ X Y, InLieW k r z X → InLieW k r z Y → dOp π (X + Y) = dOp π X + dOp π Y :=
    fun X Y hX hY => (hLin W k r z π hπ X Y hX hY).1
  have dsm : ∀ X (s : ℝ), InLieW k r z X → dOp π ((s : ℂ) • X) = (s : ℂ) • dOp π X := fun X s hX => by
    rw [(hLin W k r z π hπ X X hX hX).2 s, Complex.coe_smul]
  have dsub : ∀ X Y, InLieW k r z X → InLieW k r z Y → dOp π (X - Y) = dOp π X - dOp π Y := fun X Y hX hY => by
    have e : X - Y = X + (((-1 : ℝ) : ℂ)) • Y := by simp [sub_eq_add_neg]
    rw [e, dadd _ _ hX (lie_smul hY _), dsm _ _ hY]
    simp [sub_eq_add_neg]
  have ecZ : ecOp π Z = dOp π X₁ + Complex.I • dOp π X₂ := rfl
  have ecZ' : ecOp π Z' = dOp π Y₁ + Complex.I • dOp π Y₂ := rfl
  refine ⟨?_, fun c => ?_, ?_⟩
  · have e : Z + Z' = (X₁ + Y₁) + Complex.I • (X₂ + Y₂) := by
      rw [← eZ, ← eZ', smul_add]; abel
    rw [e]
    refine ⟨gl_comb (lie_add hX₁ hY₁) (lie_add hX₂ hY₂), ?_⟩
    rw [ec_comb π (lie_add hX₁ hY₁) (lie_add hX₂ hY₂), dadd _ _ hX₁ hY₁, dadd _ _ hX₂ hY₂, ecZ, ecZ', smul_add]
    abel
  · have e : c • Z = ((c.re : ℂ) • X₁ - (c.im : ℂ) • X₂) + Complex.I • ((c.re : ℂ) • X₂ + (c.im : ℂ) • X₁) := by
      rw [alg_smul, Complex.re_add_im, eZ]
    have l1 := lie_sub (lie_smul hX₁ c.re) (lie_smul hX₂ c.im)
    have l2 := lie_add (lie_smul hX₂ c.re) (lie_smul hX₁ c.im)
    rw [e]
    refine ⟨gl_comb l1 l2, ?_⟩
    rw [ec_comb π l1 l2, dsub _ _ (lie_smul hX₁ c.re) (lie_smul hX₂ c.im),
      dadd _ _ (lie_smul hX₂ c.re) (lie_smul hX₁ c.im), dsm X₁ c.re hX₁, dsm X₂ c.im hX₂, dsm X₂ c.re hX₂, dsm X₁ c.im hX₁, alg_smul, Complex.re_add_im, ecZ]
  · have b11 := hBr W k r z π hπ X₁ Y₁ hX₁ hY₁
    have b22 := hBr W k r z π hπ X₂ Y₂ hX₂ hY₂
    have b12 := hBr W k r z π hπ X₁ Y₂ hX₁ hY₂
    have b21 := hBr W k r z π hπ X₂ Y₁ hX₂ hY₁
    have e : Z * Z' - Z' * Z = ((X₁ * Y₁ - Y₁ * X₁) - (X₂ * Y₂ - Y₂ * X₂)) +
        Complex.I • ((X₁ * Y₂ - Y₂ * X₁) + (X₂ * Y₁ - Y₁ * X₂)) := by
      rw [← alg_bracket, eZ, eZ']
    have l1 := lie_sub b11.1 b22.1
    have l2 := lie_add b12.1 b21.1
    rw [e]
    refine ⟨gl_comb l1 l2, ?_⟩
    rw [ec_comb π l1 l2, dsub _ _ b11.1 b22.1, dadd _ _ b12.1 b21.1, b11.2, b22.2, b12.2, b21.2, ecZ, ecZ']
    exact (alg_bracket (dOp π X₁) (dOp π X₂) (dOp π Y₁) (dOp π Y₂)).symm

namespace LieListProducts

theorem unitB_mul {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (Bs : Fin m → Fin n → ℂ)
    (ho : ∀ a b, herm H (Bs a) (Bs b) = if a = b then 1 else 0) (a b c d : Fin m) :
    unitB H Bs a b * unitB H Bs c d = if b = c then unitB H Bs a d else 0 := by
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec, Qx8.unitB_mulVec H Bs c d, Matrix.mulVec_smul, Qx8.unitB_mulVec, ho]
  by_cases h : b = c
  · rw [if_pos h, if_pos h.symm, one_smul, Qx8.unitB_mulVec]
  · rw [if_neg h, if_neg (Ne.symm h), zero_smul, smul_zero, Matrix.zero_mulVec]

theorem list_prod_apply {W : Type*} [AddCommGroup W] [Module ℂ W] (L : List (Module.End ℂ W)) (v : W) :
    (L.map fun T : Module.End ℂ W => fun y : W => T y).foldr (fun T h => T h) v = L.prod v := by
  induction L with
  | nil => rfl
  | cons T L ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    rw [ih]
    rfl

end LieListProducts

open LieListProducts in
theorem qr_frameGl_of : Qr.EcLie → Qr.FrameGl := by
  intro hE W _ _ _ k r m z π Bs hπ hB
  have hgl : ∀ a b, InGlW k r z (unitB (Hpk k r) Bs a b) := fun a b => frame_lie hB a b
  have h0 : InGlW k r z 0 ∧ ecOp π (0 : Mx k r) = 0 := by
    have h := (hE W k r z π hπ 0 0 ?_ ?_).2.1 0
    · simpa using h
    all_goals
      unfold InGlW
      rw [hpart1_lie (z := z) lie_zero, hpart2_lie (z := z) lie_zero]
      exact ⟨lie_zero, lie_zero⟩
  have hsub : ∀ Z Z', InGlW k r z Z → InGlW k r z Z' → ecOp π (Z - Z') = ecOp π Z - ecOp π Z' := by
    intro Z Z' hZ hZ'
    have h1 := (hE W k r z π hπ Z' Z' hZ' hZ').2.1 (-1)
    have h2 := (hE W k r z π hπ Z ((-1 : ℂ) • Z') hZ h1.1).1.2
    rw [h1.2] at h2
    simpa [sub_eq_add_neg] using h2
  have hite : ∀ (p : Prop) [Decidable p] (Z : Mx k r), InGlW k r z Z →
      InGlW k r z (if p then Z else 0) ∧ ecOp π (if p then Z else 0) = if p then ecOp π Z else 0 := by
    intro p _ Z hZ
    by_cases h : p
    · simpa [h] using hZ
    · simpa [h] using h0
  refine ⟨fun a b c d => ?_, fun w v => ?_⟩
  · have h := (hE W k r z π hπ _ _ (hgl a b) (hgl c d)).2.2.2
    rw [unitB_mul _ _ hB.2.1, unitB_mul _ _ hB.2.1, hsub _ _ (hite _ _ (hgl a d)).1 (hite _ _ (hgl c b)).1,
      (hite _ _ (hgl a d)).2, (hite _ _ (hgl c b)).2] at h
    unfold EB
    ext x
    have hx := congrArg (fun T : W →L[ℂ] W => T x) h
    by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2] at hx ⊢ <;> exact hx.symm
  · unfold capRep qmF qdet qminor
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Module.End.mul_apply, ← list_prod_apply, List.map_ofFn]
    have e : ((Equiv.Perm.sign σ : ℤ) : Module.End ℂ W) = (((Equiv.Perm.sign σ : ℤ) : ℂ)) • (1 : Module.End ℂ W) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [e, LinearMap.smul_apply, Module.End.one_apply]
    congr 3
    funext j y
    simp only [Function.comp, Tm, id, LinearMap.add_apply]
    rw [ecRep_eq hπ.1 hπ.2 (hgl _ _).1 (hgl _ _).2]
    congr 1
    by_cases h : σ j = j
    · simp [h, Algebra.algebraMap_eq_smul_one]
    · simp [h]

end Formalism.FourierDecayAlt.P
end
end

