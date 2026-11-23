module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0014

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyInvariant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyInvariance

open ChartMongeAmpereAffineInvariance

def EnergyInvariantUnder {e : ℕ} (C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) : Prop :=
  ∀ M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ, M.PosDef → N.PosDef → ∀ k : ℕ,
    chartMixedEnergy (Cᴴ * M * C) (Cᴴ * N * C) k = chartMixedEnergy M N k

variable {e : ℕ}

theorem posDef_conj {M C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (hC : C.det ≠ 0) :
    (Cᴴ * M * C).PosDef :=
  hM.conjTranspose_mul_mul_same
    (mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC)))

theorem conj_mul (M A B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    (A * B)ᴴ * M * (A * B) = Bᴴ * (Aᴴ * M * A) * B := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem invariantUnder_mul {A B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hA : EnergyInvariantUnder A)
    (hB : EnergyInvariantUnder B) (hAdet : A.det ≠ 0) : EnergyInvariantUnder (A * B) := by
  intro M N hM hN k
  rw [conj_mul, conj_mul, hB _ _ (posDef_conj hM hAdet) (posDef_conj hN hAdet), hA M N hM hN]

theorem invariantUnder_of_mul_right {C V : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ}
    (hCV : EnergyInvariantUnder (C * V)) (hV : EnergyInvariantUnder V) (hC : C.det ≠ 0) :
    EnergyInvariantUnder C := by
  intro M N hM hN k
  rw [← hV _ _ (posDef_conj hM hC) (posDef_conj hN hC), ← conj_mul, ← conj_mul, hCV M N hM hN]

theorem maDensity_comp_affine_family {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (c : Fin D → ℂ)
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) (κ : ℝ) (z : Fin D → ℂ) :
    maDensity (fun j => fun y => φ j (c + P *ᵥ y) + κ) z =
      Complex.normSq P.det * maDensity φ (c + P *ᵥ z) := by
  have hQ : (P.map (starRingEnd ℂ)).det = starRingEnd ℂ P.det := (RingHom.map_det (starRingEnd ℂ) P).symm
  have hH : ∀ j, cxHessian (fun y => φ j (c + P *ᵥ y) + κ) z =
      Pᵀ * cxHessian (φ j) (c + P *ᵥ z) * P.map (starRingEnd ℂ) := fun j =>
    cxHessian_comp_affine (φ j) c P hP κ z
  simp only [maDensity, hH]
  rw [mixedDisc_mul_mul (Pᵀ) (P.map (starRingEnd ℂ)) (fun j => cxHessian (φ j) (c + P *ᵥ z)), det_transpose, hQ,
    Complex.mul_conj, Complex.re_ofReal_mul]
  ring

theorem invariantUnder_of_row_zero (T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hT : ∀ j : Fin e, T 0 j.succ = 0)
    (hdet : T.det ≠ 0) : EnergyInvariantUnder T := by
  intro M N hM hN k
  have ht : T 0 0 ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, zero_mul])
  have hC : (T.submatrix Fin.succ Fin.succ).det ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, mul_zero])
  set P := (T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ with hPdef
  set c : Fin e → ℂ := (T 0 0)⁻¹ • (fun i => T i.succ 0) with hcdef
  have hP : P.det ≠ 0 := by
    rw [hPdef, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) hC
  have hfM : hermChartPot (Tᴴ * M * T) = fun y => hermChartPot M (c + P *ᵥ y) + Real.log ‖T 0 0‖ :=
    funext (hermChartPot_conj M T hM hT ht)
  have hfN : hermChartPot (Tᴴ * N * T) = fun y => hermChartPot N (c + P *ᵥ y) + Real.log ‖T 0 0‖ :=
    funext (hermChartPot_conj N T hN hT ht)
  set Φ : Fin e → (Fin e → ℂ) → ℝ := fun j => if (j : ℕ) < k then hermChartPot M else hermChartPot N with hΦ
  have hfam : (fun j : Fin e => if (j : ℕ) < k then hermChartPot (Tᴴ * M * T) else hermChartPot (Tᴴ * N * T)) =
      fun j => fun y => Φ j (c + P *ᵥ y) + Real.log ‖T 0 0‖ := by
    funext j y
    by_cases h : (j : ℕ) < k <;> simp [hΦ, h, hfM, hfN]
  set f : (Fin e → ℂ) → ℝ := fun w => (hermChartPot M w - hermChartPot N w) * maDensity Φ w with hf
  have hpt : ∀ y, (hermChartPot (Tᴴ * M * T) y - hermChartPot (Tᴴ * N * T) y) *
      maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot (Tᴴ * M * T) else hermChartPot (Tᴴ * N * T)) y =
      Complex.normSq P.det * f (c + P *ᵥ y) := fun y => by
    rw [hfam, maDensity_comp_affine_family Φ c P hP, hfM, hfN, hf]
    ring
  unfold chartMixedEnergy
  simp_rw [hpt]
  rw [integral_const_mul, integral_comp_affine f c P hP, ← mul_assoc,
    mul_inv_cancel₀ (Complex.normSq_pos.mpr hP).ne', one_mul]

theorem invariantUnder_of_row_one (hS : ChartEnergySwapInvariant.Statement)
    (C : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) (hC : C.det ≠ 0) (h1 : C 0 1 ≠ 0) :
    EnergyInvariantUnder C := by
  have h01 : (0 : Fin (e + 1 + 1)) ≠ 1 := by simp
  set S : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ := swapFirstTwo e with hSdef
  have hSinv : EnergyInvariantUnder S := fun M N hM hN k => hS e M N hM hN k
  have hSdet : S.det ≠ 0 := by
    rw [hSdef, swapFirstTwo, det_permutation, Equiv.Perm.sign_swap h01]
    norm_num
  set T : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ :=
    (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ).updateRow 1 (C 0) with hTdef
  have hT0 : ∀ j : Fin (e + 1), T 0 j.succ = 0 := fun j => by
    rw [hTdef, updateRow_ne h01, one_apply_ne (Fin.succ_ne_zero j).symm]
  have hTdet : T.det = C 0 1 := by
    have hrow : ∑ m, C 0 m • (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) m = C 0 := by
      funext p
      simp [Finset.sum_apply, Matrix.one_apply]
    have h := det_updateRow_sum (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) 1 (C 0)
    rw [hrow] at h
    simpa using h
  have hTdet' : T.det ≠ 0 := by rw [hTdet]; exact h1
  have hST0 : ∀ m, C 0 m = (S * T) 0 m := fun m => by
    rw [hSdef, swapFirstTwo, PEquiv.toMatrix_toPEquiv_mul, submatrix_apply, Equiv.swap_apply_left, id, hTdef,
      updateRow_self]
  have hSTdet : (S * T).det ≠ 0 := by
    rw [det_mul]
    exact mul_ne_zero hSdet hTdet'
  have hU : IsUnit (S * T).det := isUnit_iff_ne_zero.mpr hSTdet
  set A := C * (S * T)⁻¹ with hAdef
  have hCA : C = A * (S * T) := by rw [hAdef, Matrix.mul_assoc, nonsing_inv_mul _ hU, Matrix.mul_one]
  have hA0 : ∀ j : Fin (e + 1), A 0 j.succ = 0 := fun j => by
    rw [hAdef, Matrix.mul_apply]
    simp_rw [hST0]
    rw [← Matrix.mul_apply, mul_nonsing_inv _ hU, one_apply_ne (Fin.succ_ne_zero j).symm]
  have hAdet : A.det ≠ 0 := fun h => hC (by rw [hCA, det_mul, h, zero_mul])
  have h := invariantUnder_mul (invariantUnder_of_row_zero A hA0 hAdet)
    (invariantUnder_mul hSinv (invariantUnder_of_row_zero T hT0 hTdet') hSdet) hAdet
  rwa [← hCA] at h

end ChartEnergyInvariance


open ChartEnergyInvariance in
theorem ChartEnergyLinearInvariant.proof (hS : ChartEnergySwapInvariant.Statement) :
    ChartEnergyLinearInvariant.Statement := by
  intro e M N C hM hN hC k
  by_cases hrow : ∀ j : Fin e, C 0 j.succ = 0
  · exact invariantUnder_of_row_zero C hrow hC M N hM hN k
  · push Not at hrow
    obtain ⟨j, hj⟩ := hrow
    cases e with
    | zero => exact j.elim0
    | succ e =>
      set V : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ :=
        (Equiv.swap (1 : Fin (e + 1 + 1)) j.succ).permMatrix ℂ with hVdef
      have hs0 : Equiv.swap (1 : Fin (e + 1 + 1)) j.succ 0 = 0 :=
        Equiv.swap_apply_of_ne_of_ne (by simp) (Fin.succ_ne_zero j).symm
      have hV0 : ∀ m : Fin (e + 1), V 0 m.succ = 0 := fun m => by
        simp [hVdef, PEquiv.toMatrix_apply, hs0, (Fin.succ_ne_zero m).symm]
      have hVdet : V.det ≠ 0 := by
        rw [hVdef, det_permutation]
        rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (1 : Fin (e + 1 + 1)) j.succ)) with h | h <;>
          simp [h]
      have hCV1 : (C * V) 0 1 ≠ 0 := by
        rw [hVdef, PEquiv.mul_toMatrix_toPEquiv, submatrix_apply, Equiv.symm_swap, Equiv.swap_apply_left, id]
        exact hj
      have hCVdet : (C * V).det ≠ 0 := by
        rw [det_mul]
        exact mul_ne_zero hC hVdet
      exact invariantUnder_of_mul_right (invariantUnder_of_row_one hS (C * V) hCVdet hCV1)
        (invariantUnder_of_row_zero V hV0 hVdet) hC M N hM hN k

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsConjInvariant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace FubiniStudyConjugationInvariant

theorem fsMetric_conj {n : Type*} [Fintype n] (w : n → ℂ) :
    (fsMetric (ι := n)).ρ (fun i => (starRingEnd ℂ) (w i)) = (fsMetric (ι := n)).ρ w := by
  simp [fsMetric, EuclideanSpace.norm_eq]

end FubiniStudyConjugationInvariant

theorem FsConjInvariant.proof : FsConjInvariant.Statement := by
  intro K _ ι _ z
  simp only [fsMulti, HermLine.ofMetrics]
  exact Finset.prod_congr rfl fun k _ => by
    rw [FubiniStudyConjugationInvariant.fsMetric_conj (fun i => z ⟨k, i⟩)]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSmooth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace FubiniStudySmooth

theorem contDiffAt_blockNorm {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (k : K)
    (z : (Σ k, ι k) → ℂ) (hz : ∃ i, z ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : (Σ k, ι k) → ℂ => ‖WithLp.toLp 2 (fun i => w ⟨k, i⟩)‖) z := by
  have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : (Σ k, ι k) → ℂ => WithLp.toLp 2 (fun i => w ⟨k, i⟩)) :=
    PiLp.contDiff_toLp.comp (contDiff_pi.2 fun i => contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, ι k))
  have hne : WithLp.toLp 2 (fun i => z ⟨k, i⟩) ≠ 0 := by
    obtain ⟨i, hi⟩ := hz
    intro h0
    exact hi (by simpa using congrArg (fun v : WithLp 2 (ι k → ℂ) => v.ofLp i) h0)
  exact (contDiffAt_norm ℂ hne).comp z hL.contDiffAt

end FubiniStudySmooth

theorem FsLineSmooth.proof : FsLineSmooth.Statement := by
  intro K _ ι _
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : (Σ k, ι k) → ℂ => ∏ k, ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖ ^ ((1 : K → ℤ) k)) _
  refine contDiffOn_prod fun k _ => ?_
  intro z hz
  simp only [Pi.one_apply, zpow_one]
  exact (FubiniStudySmooth.contDiffAt_blockNorm ι k z (hz k)).contDiffWithinAt

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassArithVar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace GrassmannianArithmeticVariety

theorem det_submatrix_sign {R : Type*} [CommRing R] {j N : ℕ} (A : Matrix (Fin j) (Fin N) R)
    (g h : Fin j → Fin N) (hg : Function.Injective g) (hh : Function.Injective h)
    (hr : Set.range h = Set.range g) :
    ∃ s : ℤˣ, (A.submatrix id h).det = ((s : ℤ) : R) * (A.submatrix id g).det := by
  let σ : Equiv.Perm (Fin j) :=
    (Equiv.ofInjective h hh).trans ((Equiv.subtypeEquivRight (fun x => by rw [hr])).trans (Equiv.ofInjective g hg).symm)
  have hσ : ∀ i, g (σ i) = h i := by
    intro i
    simp [σ, Equiv.apply_ofInjective_symm]
  refine ⟨Equiv.Perm.sign σ, ?_⟩
  have : A.submatrix id h = (A.submatrix id g).submatrix id σ := by
    ext r i; simp [hσ]
  rw [this, det_permute']

def col {j m : ℕ} (a : Fin j) (b : Fin m) (i : Fin j) : Fin (j + m) :=
  if i = a then Fin.natAdd j b else Fin.castAdd m i

theorem col_injective {j m : ℕ} (a : Fin j) (b : Fin m) : Function.Injective (col a b) := by
  intro x y hxy
  simp only [col] at hxy
  split_ifs at hxy with h1 h2 h2
  · exact h1.trans h2.symm
  · rw [Fin.ext_iff] at hxy; simp at hxy; omega
  · rw [Fin.ext_iff] at hxy; simp at hxy; omega
  · rw [Fin.ext_iff] at hxy; exact Fin.ext (by simpa using hxy)

def idx {j m : ℕ} (a : Fin j) (b : Fin m) : PlIdx j m :=
  ⟨Finset.univ.map ⟨col a b, col_injective a b⟩, by simp⟩

theorem minor_idx {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R)
    (a : Fin j) (b : Fin m) :
    ∃ s : ℤˣ, (colsOf (onePipe Z) (idx a b)).det = ((s : ℤ) : R) * Z a b := by
  obtain ⟨s, hs⟩ := det_submatrix_sign (onePipe Z) (col a b) _ (col_injective a b)
    ((idx a b).1.orderEmbOfFin (idx a b).2).injective (by
      rw [Finset.range_orderEmbOfFin]; simp [idx])
  refine ⟨s, ?_⟩
  have hcol : (onePipe Z).submatrix id (col a b) = (1 : Matrix (Fin j) (Fin j) R).updateCol a
      (fun r => Z r b) := by
    ext r i
    by_cases hi : i = a
    · simp [col, onePipe, hi]
    · simp [col, onePipe, hi]
  rw [colsOf, hs, hcol, ← cramer_apply, cramer_one]
  rfl

theorem colsOf_anchor {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R) :
    colsOf (onePipe Z) (plAnchor j m) = 1 := by
  have he : ((plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 : Fin j → Fin (j + m)) =
      Fin.castAdd m :=
    (Finset.orderEmbOfFin_unique _ (fun x => by simp [plAnchor]) (Fin.strictMono_castAdd m)).symm
  ext r i
  simp [colsOf, onePipe, he]

end GrassmannianArithmeticVariety


open GrassmannianArithmeticVariety in
theorem GrassArithVar.proof (h : CoordConeArithVar.Statement) : GrassArithVar.Statement := by
  intro f j m hf
  let e : Fin (f * j * m) ≃ Fin f × Fin j × Fin m :=
    finProdFinEquiv.symm.trans
      ((finProdFinEquiv.symm.prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))
  let φ := IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m)
  let t : Fin (f * j * m) → GrassField f j m := fun i => φ (X (e i))
  have anchor : ∀ τ, grassCoord f j m ⟨τ, plAnchor j m⟩ = 1 := by
    intro τ
    have hp : grassPolyCoord f j m ⟨τ, plAnchor j m⟩ = 1 :=
      (congrArg Matrix.det (colsOf_anchor _)).trans det_one
    rw [grassCoord, hp, map_one]
  have hmem : ∀ q : MvPolynomial (Fin f × Fin j × Fin m) ℚ,
      algebraMap _ (GrassField f j m) q ∈ IntermediateField.adjoin ℚ (Set.range t) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact IntermediateField.algebraMap_mem _ c
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨e.symm i, by simp [t, φ]⟩)
  refine h (Fin f) (plBlocks f j m) (GrassField f j m) (grassCoord f j m) (fun _ => plAnchor j m)
    (f * j * m) t ⟨⟨0, hf⟩⟩ (fun τ => by rw [anchor]; exact one_ne_zero) ?_ ?_ ?_
  · exact ((MvPolynomial.algebraicIndependent_X _ ℚ).map' (f := φ)
      (IsFractionRing.injective _ _)).comp e e.injective
  · intro i
    rcases hi : e i with ⟨τ, a, b⟩
    obtain ⟨s, hs⟩ : ∃ s : ℤˣ, grassPolyCoord f j m ⟨τ, idx a b⟩ =
        ((s : ℤ) : MvPolynomial (Fin f × Fin j × Fin m) ℚ) * X (τ, a, b) :=
      minor_idx _ a b
    have hr : grassCoord f j m ⟨τ, idx a b⟩ / grassCoord f j m ⟨τ, plAnchor j m⟩ ∈
        IntermediateField.adjoin ℚ (coneRatios (grassCoord f j m) fun _ => plAnchor j m) :=
      IntermediateField.subset_adjoin _ _ ⟨⟨τ, idx a b⟩, rfl⟩
    have hy : grassCoord f j m ⟨τ, idx a b⟩ = ((s : ℤ) : GrassField f j m) * t i := by
      rw [grassCoord, hs, map_mul, map_intCast]
      simp [t, φ, hi]
    rw [anchor, div_one, hy] at hr
    rcases Int.units_eq_one_or s with rfl | rfl
    · simpa using hr
    · simpa using neg_mem hr
  · rintro r ⟨⟨τ, I⟩, rfl⟩
    have hr : grassCoord f j m ⟨τ, I⟩ / grassCoord f j m ⟨τ, plAnchor j m⟩ ∈
        IntermediateField.adjoin ℚ (Set.range t) := by
      rw [anchor, div_one]; exact hmem _
    exact isAlgebraic_algebraMap (R := IntermediateField.adjoin ℚ (Set.range t))
      (A := GrassField f j m) ⟨_, hr⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassHeightBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

theorem GrassHeightBound.proof (hArith : GrassArithVar.Statement) (hRoot : RootArithVar.Statement)
    (hSemi : FsLineSemipositive.Statement) (hNef : NefOfNonneg.Statement)
    (hConj : FsConjInvariant.Statement) (hLe : GrassLeRoot.Statement) (hHt : RootHeight.Statement)
    (hDense : RootDense.Statement) : GrassHeightBound.Statement := by
  intro hZ2 f j m hf II hII
  refine hZ2 (Fin f) (plBlocks f j m) (grassIdeal f j m) ⊥ (f * j * m) (fsMulti (plBlocks f j m))
    (grassConst f j m) (rootFamily f j m) II hII (hArith f j m hf) bot_le (hSemi _ _ _)
    (hNef _ _ _ _ fun _ => ?_) (hConj _ _) ?_ (hDense f j m)
  · show (0 : ℤ) ≤ 1
    exact zero_le_one
  · rintro W ⟨ζ, hζ, rfl⟩
    exact ⟨hRoot f j m ζ hf hζ, hLe f j m ζ, hHt f j m ζ hf hζ II hII⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassLeRoot
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace GrassmannianRootBound

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def cone {R : Type*} [CommRing R] (y : (Σ k, ι k) → R) : MRing ι →ₐ[ℤ] MvPolynomial K R :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem map_cone {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (y : (Σ k, ι k) → R)
    (g : MRing ι) : MvPolynomial.map φ (cone y g) = cone (fun p => φ (y p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [cone]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp]; simp [cone]

theorem eval_grassPolyCoord {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ)
    (p : Σ _ : Fin f, PlIdx j m) :
    aeval (fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2) (grassPolyCoord f j m p) =
      rootCoord ζ p := by
  let φ : MvPolynomial (Fin f × Fin j × Fin m) ℚ →+* ℂ :=
    (aeval fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2).toRingHom
  show φ _ = _
  rw [grassPolyCoord, RingHom.map_det, rootCoord]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, colsOf, onePipe, submatrix_apply, of_apply, id]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) (p.2.1.orderEmbOfFin p.2.2 b)
  · simp [Fin.append_left, Matrix.one_apply, apply_ite φ]
  · simp [Fin.append_right, φ]

end GrassmannianRootBound


open GrassmannianRootBound in
theorem GrassLeRoot.proof : GrassLeRoot.Statement := by
  intro f j m ζ g hg
  have h0 : mConeMap (grassCoord f j m) g = 0 := hg
  have h1 : cone (grassPolyCoord f j m) g = 0 := by
    apply MvPolynomial.map_injective (algebraMap (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m))
      (IsFractionRing.injective _ _)
    rw [map_cone, map_zero]
    exact h0
  have h2 := congrArg (MvPolynomial.map
    (aeval fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2).toRingHom) h1
  rw [map_cone, map_zero] at h2
  show (aeval fun p => MvPolynomial.C (rootCoord ζ p) * MvPolynomial.X p.1) g = 0
  simpa [cone, eval_grassPolyCoord] using h2

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PNefOfNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace NefOfNonnegAlt

theorem geoNum_zero_nonneg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (V : Ideal (MRing ι)) (a : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 V a := by
  unfold geoNum
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl

theorem geoNum_one_nonneg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (V : Ideal (MRing ι)) (a : K → ℤ) (ha : ∀ k, 0 ≤ a k) : 0 ≤ geoNum 1 V (fun _ => a) := by
  unfold geoNum
  split_ifs
  · refine Finset.sum_nonneg fun k _ => mul_nonneg (ha k) ?_
    refine finsum_nonneg fun W => finsum_nonneg fun _ => ?_
    exact mul_nonneg (Int.natCast_nonneg _) (geoNum_zero_nonneg _ _)
  · exact le_rfl

end NefOfNonnegAlt

theorem NefOfNonneg.proof : NefOfNonneg.Statement := by
  intro K _ ι _ P a ha W _ _ _ _
  exact NefOfNonnegAlt.geoNum_one_nonneg W a ha

end GroundTheory.Heights₂.Heights
end

