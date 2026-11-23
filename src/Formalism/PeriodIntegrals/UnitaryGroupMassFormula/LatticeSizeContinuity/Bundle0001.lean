module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.LatSizeContOfSteps
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0002
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.DetMono
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity

lemma star_dot_self {n : ℕ} (w : Fin n → ℂ) : star w ⬝ᵥ w = ((nsq w : ℝ) : ℂ) := by
  unfold nsq dotProduct
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.conj_mul']

lemma quad {n j : ℕ} (C : Matrix (Fin n) (Fin j) ℂ) (z : Fin j → ℂ) :
    star z ⬝ᵥ ((Cᴴ * C) *ᵥ z) = ((nsq (C *ᵥ z) : ℝ) : ℂ) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, star_dot_self]

lemma sandwich {j : ℕ} (y X : Matrix (Fin j) (Fin j) ℂ) (v : Fin j → ℂ) :
    star v ⬝ᵥ ((yᴴ * X * y) *ᵥ v) = star (y *ᵥ v) ⬝ᵥ (X *ᵥ (y *ᵥ v)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

lemma nsq_nonneg {n : ℕ} (w : Fin n → ℂ) : 0 ≤ nsq w :=
  Finset.sum_nonneg fun _ _ => by positivity

end PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity

namespace PI.UnitaryGroupMassFormula.LSC

open DeterminantMonotonicity in
theorem determinant_monotone : DetMono := by
  intro n j C M κ hκ hM
  classical
  have hB : (Cᴴ * C).PosSemidef := posSemidef_conjTranspose_mul_self C
  have hA : ((M * C)ᴴ * (M * C)).PosSemidef := posSemidef_conjTranspose_mul_self (M * C)
  have hBre : 0 ≤ ((Cᴴ * C).det).re := by
    simpa using (Complex.le_def.mp hB.det_nonneg).1
  refine ⟨hBre, ?_⟩
  have hqA : ∀ z : Fin j → ℂ, star z ⬝ᵥ (((M * C)ᴴ * (M * C)) *ᵥ z) = ((nsq (M *ᵥ (C *ᵥ z)) : ℝ) : ℂ) := by
    intro z; rw [quad, mulVec_mulVec]
  by_cases h0 : (Cᴴ * C).det = 0
  · obtain ⟨z, hz, hBz⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have h1 : nsq (C *ᵥ z) = 0 := by
      have := quad C z
      rw [hBz, dotProduct_zero] at this
      exact_mod_cast this.symm
    have h2 : nsq (M *ᵥ (C *ᵥ z)) = 0 :=
      le_antisymm (by simpa [h1] using hM (C *ᵥ z)) (nsq_nonneg _)
    have h3 : ((M * C)ᴴ * (M * C)) *ᵥ z = 0 := by
      rw [← hA.dotProduct_mulVec_zero_iff, hqA, h2]; simp
    have h4 : ((M * C)ᴴ * (M * C)).det = 0 := exists_mulVec_eq_zero_iff.mp ⟨z, hz, h3⟩
    rw [h4, h0]; simp
  · have hPD : (Cᴴ * C).PosDef := hB.posDef_iff_det_ne_zero.mpr h0
    obtain ⟨y, hy, hyB⟩ := posDefCongruentOne j _ hPD
    have hN : (yᴴ * ((M * C)ᴴ * (M * C)) * y).PosSemidef := hA.conjTranspose_mul_mul_same y
    have hev : ∀ i, hN.1.eigenvalues i ≤ κ := by
      intro i
      have hv1 : star (⇑(hN.1.eigenvectorBasis i) : Fin j → ℂ) ⬝ᵥ ⇑(hN.1.eigenvectorBasis i) = 1 := by
        rw [dotProduct_comm]
        simp only [← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
          hN.1.eigenvectorBasis.orthonormal.1 i]
        simp
      have hBv : star (⇑(hN.1.eigenvectorBasis i) : Fin j → ℂ) ⬝ᵥ
          ((yᴴ * (Cᴴ * C) * y) *ᵥ ⇑(hN.1.eigenvectorBasis i)) = 1 := by
        rw [hyB, one_mulVec, hv1]
      rw [sandwich, quad] at hBv
      have hn1 : nsq (C *ᵥ (y *ᵥ ⇑(hN.1.eigenvectorBasis i))) = 1 := by exact_mod_cast hBv
      rw [hN.1.eigenvalues_eq, sandwich, hqA]
      have := hM (C *ᵥ (y *ᵥ ⇑(hN.1.eigenvectorBasis i)))
      rw [hn1, mul_one] at this
      simpa using this
    have hdetN : (yᴴ * ((M * C)ᴴ * (M * C)) * y).det = ((∏ i, hN.1.eigenvalues i : ℝ) : ℂ) := by
      rw [hN.1.det_eq_prod_eigenvalues]; push_cast; rfl
    have hP : ∏ i, hN.1.eigenvalues i ≤ κ ^ j := by
      calc ∏ i, hN.1.eigenvalues i ≤ ∏ _i : Fin j, κ :=
            Finset.prod_le_prod₀ (fun i _ => hN.eigenvalues_nonneg i) (fun i _ => hev i)
        _ = κ ^ j := by simp
    have hd0 : y.det ≠ 0 := hy.ne_zero
    have hnd : 0 < Complex.normSq y.det := Complex.normSq_pos.mpr hd0
    have e1 : ((Complex.normSq y.det : ℝ) : ℂ) * ((M * C)ᴴ * (M * C)).det
        = ((∏ i, hN.1.eigenvalues i : ℝ) : ℂ) := by
      rw [← hdetN, det_mul, det_mul, det_conjTranspose, Complex.normSq_eq_conj_mul_self]
      simp only [Complex.star_def]; ring
    have e2 : ((Complex.normSq y.det : ℝ) : ℂ) * (Cᴴ * C).det = 1 := by
      have := congrArg Matrix.det hyB
      rw [det_mul, det_mul, det_conjTranspose, det_one] at this
      rw [Complex.normSq_eq_conj_mul_self, ← this]
      simp only [Complex.star_def]; ring
    have r1 := congrArg Complex.re e1
    have r2 := congrArg Complex.re e2
    rw [Complex.re_ofReal_mul, Complex.ofReal_re] at r1
    rw [Complex.re_ofReal_mul, Complex.one_re] at r2
    refine le_of_mul_le_mul_left ?_ hnd
    calc Complex.normSq y.det * (((M * C)ᴴ * (M * C)).det).re = ∏ i, hN.1.eigenvalues i := r1
      _ ≤ κ ^ j := hP
      _ = κ ^ j * (Complex.normSq y.det * ((Cᴴ * C).det).re) := by rw [r2, mul_one]
      _ = Complex.normSq y.det * (κ ^ j * ((Cᴴ * C).det).re) := by ring

end PI.UnitaryGroupMassFormula.LSC
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.LatticeIsometry
section
noncomputable section

open NumberField
open scoped TensorProduct
open PI.LatSizeCont

namespace PI.UnitaryGroupMassFormula.LSC

namespace LatIs

theorem lamAf_eq (I : Formalism.MainNotions.S.AutInst) :
    I.Lf = Formalism.UG.latS (F := I.F) (Formalism.MainNotions.S.Af I.F) (Formalism.MainNotions.S.IntAf I.F I.E) I.L := by
  show Formalism.MainNotions.S.lamAf (F := I.F) I.L = _
  unfold Formalism.MainNotions.S.lamAf Formalism.UG.latS
  congr 1
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem latSet_eq (I : Formalism.MainNotions.S.AutInst) (x : I.GA) :
    Size.latSet I x = (Formalism.UG.CS.globLat (F := I.F)
      (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) I.L : Set (Fin I.n → I.E)) := by
  ext u
  simp only [Size.latSet, Set.mem_setOf_eq, SetLike.mem_coe]
  rw [lamAf_eq]
  rfl

end LatIs

theorem lattice_isometry : LatIs := by
  intro I x
  have hL := Formalism.UG.P.csGlob_lattice (F := I.F) I.L (Module.Finite.iff_fg.2 I.L_fg)
    I.L_span (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))
  letI : Submodule.IsFullLattice I.E _ := hL
  exact ⟨_, hL.fg, Submodule.IsFullLattice.span_eq_top, LatIs.latSet_eq I x⟩

end PI.UnitaryGroupMassFormula.LSC
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.NormProd
section
noncomputable section

open NumberField

namespace PI.UnitaryGroupMassFormula.LSC.NormProd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem algebraMap_norm_eq (hc : Formalism.BasicNotions.CMData F E) (m : E) :
    algebraMap F E (Algebra.norm F m) = m * star m := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hc.deg2]; norm_num)
  have hfix : ∀ r : F, starRingAut (algebraMap F E r) = algebraMap F E r := fun r =>
    (hc.fixed _).mpr ⟨r, rfl⟩
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := starRingAut) hfix
  have hσ : ∀ a, σ a = star a := fun _ => rfl
  have hne : (1 : E ≃ₐ[F] E) ≠ σ := by
    intro h
    have hall : ∀ a : E, a ∈ (algebraMap F E).range := fun a => by
      rw [← hc.fixed, ← hσ, ← h]; rfl
    have hbot : (⊥ : Subalgebra F E) = ⊤ := by
      ext a; simpa [Algebra.mem_bot] using hall a
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hbot
    rw [hc.deg2] at h1; norm_num at h1
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ 2 := by
    rw [← hc.deg2]
    exact (Fintype.card_le_of_injective (fun e : E ≃ₐ[F] E => (e : E →ₐ[F] E))
      (fun a b h => AlgEquiv.coe_algHom_injective h)).trans AlgHom.card_le
  have hge : 2 ≤ Fintype.card (E ≃ₐ[F] E) := by
    rw [← Finset.card_pair hne]; exact Finset.card_le_univ _
  have hcard : Fintype.card (E ≃ₐ[F] E) = Module.finrank F E := by
    rw [hc.deg2]; omega
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card]; exact hcard)
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ} :=
    (Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by rw [Finset.card_univ, Finset.card_pair hne]; omega)).symm
  rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hne]
  rfl

end PI.UnitaryGroupMassFormula.LSC.NormProd

namespace PI.UnitaryGroupMassFormula.LSC

open PI.UnitaryGroupMassFormula.LSC.NormProd

theorem norm_product_formula : NormProd := by
  intro I m
  letI := I.fF; letI := I.nF; letI := I.fE; letI := I.nE; letI := I.sE; letI := I.aFE
  have hc := I.cm
  set N := Algebra.norm I.F m with hN
  have hv : ∀ v : InfinitePlace I.F, ‖I.φ v m‖ ^ 2 = v N := by
    intro v
    have h1 : I.φ v (m * star m) = v.embedding N := by
      rw [← algebraMap_norm_eq hc m, I.φ_over]
    rw [map_mul, hc.cmUnram.2.1, Complex.mul_conj] at h1
    rw [← InfinitePlace.norm_embedding_eq, ← h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  simp_rw [hv]
  have hmult : ∀ v : InfinitePlace I.F, v.mult = 1 := fun v =>
    InfinitePlace.mult_isReal ⟨v, hc.totReal.isReal v⟩
  have := InfinitePlace.prod_eq_abs_norm N
  simp only [hmult, pow_one] at this
  rw [this, hN, Algebra.norm_norm, Rat.cast_abs]

end PI.UnitaryGroupMassFormula.LSC
end
end

