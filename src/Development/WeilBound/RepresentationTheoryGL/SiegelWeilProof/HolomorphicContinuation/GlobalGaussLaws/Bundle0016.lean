module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0014
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0013
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0010
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0008
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DRConjTranspose
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.VacD

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacB

variable {n : ℕ}

def dR (β : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => (β j : ℂ)

theorem dR_conjTranspose (β : Fin n → ℝ) : (dR β)ᴴ = dR β := by
  simp [dR, Matrix.diagonal_conjTranspose]

theorem dR_mul (β β' : Fin n → ℝ) : dR β * dR β' = dR (fun j => β j * β' j) := by
  simp [dR, Matrix.diagonal_mul_diagonal]

theorem dR_add (β β' : Fin n → ℝ) : dR β + dR β' = dR (fun j => β j + β' j) := by
  simp [dR, Matrix.diagonal_add]

theorem dR_neg (β : Fin n → ℝ) : -dR β = dR (fun j => -β j) := by
  simp [dR, Matrix.diagonal_neg]

theorem dR_one : dR (fun _ : Fin n => (1 : ℝ)) = 1 := by
  simp [dR]

theorem dR_inv (β : Fin n → ℝ) (hβ : ∀ j, β j ≠ 0) : (dR β)⁻¹ = dR (fun j => (β j)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [dR_mul]
  rw [← dR_one]
  congr 1
  funext j
  exact inv_mul_cancel₀ (hβ j)

theorem kth_eq (θ : Fin n → ℝ) : kth θ = fromBlocks (dR fun j => Real.cos (θ j)) (dR fun j => Real.sin (θ j))
    (-dR fun j => Real.sin (θ j)) (dR fun j => Real.cos (θ j)) := rfl

theorem kth_decomp (θ : Fin n → ℝ) (hc : ∀ j, Real.cos (θ j) ≠ 0) :
    kth θ = nU (dR fun j => Real.tan (θ j)) * nbar (dR fun j => -(Real.sin (θ j) * Real.cos (θ j))) *
      mM (dR fun j => (Real.cos (θ j))⁻¹) := by
  have hinv : ((dR fun j => (Real.cos (θ j))⁻¹)ᴴ)⁻¹ = dR fun j => Real.cos (θ j) := by
    rw [dR_conjTranspose, dR_inv _ (fun j => inv_ne_zero (hc j))]
    simp only [inv_inv]
  rw [kth_eq]
  simp only [nU, nbar, mM, hinv, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.add_mul, dR_mul]
  rw [dR_add, dR_neg]
  congr 1
  · congr 1
    funext j
    have h1 := hc j
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    linear_combination (Real.sin_sq_add_cos_sq (θ j))
  · congr 1
    funext j
    have h1 := hc j
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  · congr 1
    funext j
    have h1 := hc j
    field_simp

theorem kth_half (θ : Fin n → ℝ) : kth θ = kth (fun j => θ j / 2) * kth (fun j => θ j / 2) := by
  have hc : ∀ j, Real.cos (θ j) = Real.cos (θ j / 2) * Real.cos (θ j / 2) -
      Real.sin (θ j / 2) * Real.sin (θ j / 2) := by
    intro j
    have := Real.cos_two_mul (θ j / 2)
    rw [show 2 * (θ j / 2) = θ j by ring] at this
    rw [this]
    linear_combination Real.sin_sq_add_cos_sq (θ j / 2)
  have hs : ∀ j, Real.sin (θ j) = Real.cos (θ j / 2) * Real.sin (θ j / 2) +
      Real.sin (θ j / 2) * Real.cos (θ j / 2) := by
    intro j
    have := Real.sin_two_mul (θ j / 2)
    rw [show 2 * (θ j / 2) = θ j by ring] at this
    rw [this]
    ring
  rw [kth_eq, kth_eq, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_neg, Matrix.neg_mul, dR_mul, dR_neg, dR_add]
  congr 1
  · congr 1
    funext j
    rw [hc j]
    ring
  · congr 1
    funext j
    rw [hs j]
  · congr 1
    funext j
    rw [hs j]
    ring
  · congr 1
    funext j
    rw [hc j]
    ring

end PositivityTheory.Rg.Sw.Glob.VacD
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchB
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GCSchH

variable {m n : ℕ}

def qF (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) (u v : Fin m → Fin n → ℂ) : ℂ :=
  -(Complex.I * c * ∑ a ∈ S, star (u a) ⬝ᵥ (Zᵀ *ᵥ v a) - Complex.I * c * ∑ a ∈ S', star (u a) ⬝ᵥ (Z'ᵀ *ᵥ v a))

def qL (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (qF S S' c Z Z')
    (fun u₁ u₂ v => by
      simp only [qF, Pi.add_apply, star_add, add_dotProduct, Finset.sum_add_distrib]; ring)
    (fun r u v => by
      simp only [qF, Pi.smul_apply, star_smul, star_trivial, smul_dotProduct, Complex.real_smul, ← Finset.mul_sum]
      ring)
    (fun u v₁ v₂ => by
      simp only [qF, Pi.add_apply, Matrix.mulVec_add, dotProduct_add, Finset.sum_add_distrib]; ring)
    (fun r u v => by
      simp only [qF, Pi.smul_apply, Matrix.mulVec_smul, dotProduct_smul, Complex.real_smul, ← Finset.mul_sum]
      ring)

def qB (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    (Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((Fin m → Fin n → ℂ) →ₗ[ℝ] ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ qL S S' c Z Z')

theorem qB_apply (S S' : Finset (Fin m)) (c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) (u v : Fin m → Fin n → ℂ) :
    qB S S' c Z Z' u v = qF S S' c Z Z' u v := rfl

theorem re_I_mul (c : ℝ) (z : ℂ) : (Complex.I * c * z).re = -(c * z.im) := by
  simp [Complex.mul_re, Complex.mul_im]

theorem quad_nonneg {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) (y : Fin n → ℂ) : 0 ≤ (star y ⬝ᵥ (P *ᵥ y)).re := (Complex.nonneg_iff.mp (hP.posSemidef.dotProduct_mulVec_nonneg y)).1

theorem quad_pos {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) {y : Fin n → ℂ} (hy : y ≠ 0) :
    0 < (star y ⬝ᵥ (P *ᵥ y)).re := (Complex.pos_iff.mp (hP.dotProduct_mulVec_pos hy)).1

end PositivityTheory.Rg.Sw.Glob.GCSchH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GIautoOf
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem gIauto_of (hT : PositivityTheory.PfSWUS.ThetaAuto) (hM : TensMem) : GIauto := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC Ψ hΨ
  have hm := hM D n V θ l s τ ε fr hC.hθ (lNZ D ψ θ l hC.hψ hC.hθ hC.hl) hC.hs hC.hfr Ψ hΨ 1
  have hphi : (phiS θ τ fr (cLoc l τ) Ψ 1).1 = tens θ τ fr (fP (cLoc l τ) 1) Ψ := by
    unfold phiS
    rw [dite_eq_left hm.1]
  have hStd : PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (phiS θ τ fr (cLoc l τ) Ψ 1) :=
    ⟨hC.hψ, hC.hχ, hC.hη, hC.hθ, hC.hμ, hC.hω, hC.hH, hC.hl, hC.hs, hC.hν, by rw [hphi]; exact hm.2⟩
  obtain ⟨h1, h2⟩ := hT D n V ψ χ θ μ ω H l s ν _ hStd hC.hr
  exact ⟨h1, fun γ hγ g => h2 γ hγ g⟩

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussC
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem identG {g : M2 n} (hg : InG g) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    (g.toBlocks₁₁ * X + g.toBlocks₁₂)ᴴ * (g.toBlocks₂₁ * Y + g.toBlocks₂₂) -
      (g.toBlocks₂₁ * X + g.toBlocks₂₂)ᴴ * (g.toBlocks₁₁ * Y + g.toBlocks₁₂) = Xᴴ - Y := by
  obtain ⟨h1, h2, h3⟩ := inG_rel hg
  have h3' : g.toBlocks₂₂ᴴ * g.toBlocks₁₁ - g.toBlocks₁₂ᴴ * g.toBlocks₂₁ = 1 := by
    have := congrArg conjTranspose h3
    simpa [conjTranspose_sub, conjTranspose_mul] using this
  have key : (g.toBlocks₁₁ * X + g.toBlocks₁₂)ᴴ * (g.toBlocks₂₁ * Y + g.toBlocks₂₂) -
      (g.toBlocks₂₁ * X + g.toBlocks₂₂)ᴴ * (g.toBlocks₁₁ * Y + g.toBlocks₁₂) =
      Xᴴ * (g.toBlocks₁₁ᴴ * g.toBlocks₂₂ - g.toBlocks₂₁ᴴ * g.toBlocks₁₂) -
        (g.toBlocks₂₂ᴴ * g.toBlocks₁₁ - g.toBlocks₁₂ᴴ * g.toBlocks₂₁) * Y +
        Xᴴ * (g.toBlocks₁₁ᴴ * g.toBlocks₂₁ - g.toBlocks₂₁ᴴ * g.toBlocks₁₁) * Y +
        (g.toBlocks₁₂ᴴ * g.toBlocks₂₂ - g.toBlocks₂₂ᴴ * g.toBlocks₁₂) := by
    simp only [conjTranspose_add, conjTranspose_mul]
    noncomm_ring
  rw [key, h3, h3', h1, h2]
  simp

theorem det_CZD {g : M2 n} (hg : InG g) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSiegel Z) :
    IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hid := identG hg Z Z
  have h0 : star v ⬝ᵥ ((Zᴴ - Z) *ᵥ v) = 0 := by
    rw [← hid, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hMv, mulVec_zero, dotProduct_sub,
      dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hMv]
    simp
  have h0' : star v ⬝ᵥ ((Z - Zᴴ) *ᵥ v) = 0 := by
    rw [← neg_sub, neg_mulVec, dotProduct_neg, h0, neg_zero]
  have hpos := Matrix.PosDef.dotProduct_mulVec_pos hZ hv
  rw [smul_mulVec, dotProduct_smul, h0', smul_zero] at hpos
  exact lt_irrefl _ hpos

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LinSecOf
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

theorem thetaInt_smul {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n))
    (ν : Measure (GA D V)) (Φ : schwartzA θ V.rank n) (a : ℂ) (g : G D n) :
    thetaInt ω ν (a • Φ) g = a * thetaInt ω ν Φ g := by
  have h : GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω (a • Φ) g) = fun q => a * GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g) q := by
    funext q
    simp [GlobalTheory.AutomorphicL2Unitary.descend, theta, map_smul, tsum_mul_left]
  simp only [thetaInt, h, MeasureTheory.average, MeasureTheory.integral_const_mul]

theorem tens_fP_add {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (Ψ : Mx D m n → ℂ) (P Q : PX m n) :
    tens θ τ fr (fP c (P + Q)) Ψ = tens θ τ fr (fP c P) Ψ + tens θ τ fr (fP c Q) Ψ := by
  funext x
  simp only [tens, fP, evX, map_add (f := _), Pi.add_apply]
  ring

theorem tens_fP_smul {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (Ψ : Mx D m n → ℂ) (a : ℂ) (P : PX m n) :
    tens θ τ fr (fP c (a • P)) Ψ = a • tens θ τ fr (fP c P) Ψ := by
  funext x
  simp only [tens, fP, evX, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, Pi.smul_apply, smul_eq_mul]
  ring

theorem linSec_of : ThLin → LinSec := by
  intro hTL D n V ψ χ θ μ ω H l s ν τ ε fr ι c Ψ hΨ
  have hl0 : ∀ τ, l τ ≠ 0 := lNZ D ψ θ l c.hψ c.hθ c.hl
  have hm : ∀ P, tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ schwartzA θ V.rank n ∧
      tens θ τ fr (fP (cLoc l τ) P) Ψ ∈ fockA θ V n l s :=
    fun P => tensMem D n V θ l s τ ε fr c.hθ hl0 c.hs c.hfr Ψ hΨ P
  have hphi : ∀ P, phiS θ τ fr (cLoc l τ) Ψ P = ⟨_, (hm P).1⟩ := fun P => dif_pos (hm P).1
  have hadd : ∀ P Q, phiS θ τ fr (cLoc l τ) Ψ (P + Q) = phiS θ τ fr (cLoc l τ) Ψ P + phiS θ τ fr (cLoc l τ) Ψ Q := by
    intro P Q
    rw [hphi, hphi, hphi]
    exact Subtype.ext (tens_fP_add θ τ fr _ Ψ P Q)
  have hsmul : ∀ (a : ℂ) P, phiS θ τ fr (cLoc l τ) Ψ (a • P) = a • phiS θ τ fr (cLoc l τ) Ψ P := by
    intro a P
    rw [hphi, hphi]
    exact Subtype.ext (tens_fP_smul θ τ fr _ Ψ a P)
  have hstd : ∀ P, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν (phiS θ τ fr (cLoc l τ) Ψ P) := fun P =>
    ⟨c.hψ, c.hχ, c.hη, c.hθ, c.hμ, c.hω, c.hH, c.hl, c.hs, c.hν, by rw [hphi]; exact (hm P).2⟩
  refine ⟨{ toFun := fun P => secF ω τ fr (cLoc l τ) Ψ P
            map_add' := fun P Q => by
              funext g
              simp only [secF, hadd, map_add (f := _), Submodule.coe_add, Pi.add_apply]
            map_smul' := fun a P => by
              funext g
              simp only [secF, hsmul, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] },
          { toFun := fun P => thF ω ν τ fr (cLoc l τ) Ψ P
            map_add' := fun P Q => by
              funext g
              simp only [thF, Pi.add_apply]
              rw [hadd]
              exact hTL D n V ψ χ θ μ ω H l s ν _ _ (hstd P) (hstd Q) c.hr g
            map_smul' := fun a P => by
              funext g
              simp only [thF, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
              rw [hsmul]
              exact thetaInt_smul ω ν _ a g }, fun P => rfl, fun P => rfl⟩

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ThetaIntSmul
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.IInvH

variable {D : D7} {m n : ℕ}

theorem isUe_zRe (ε : Fin m → Bool) (a b : Fin m) : IsUe ε (zRe ε a b) := by
  have e1 : star ((1 : ℂ) / 2) = 1 / 2 := by simp
  ext i j
  simp only [IsUe, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply, zRe, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.single_apply, star_mul', star_sub, e1]
  by_cases h1 : a = i <;> by_cases h2 : b = j <;> by_cases h3 : b = i <;> by_cases h4 : a = j <;>
    simp only [h1, h2, h3, h4, and_true, true_and, and_false, false_and, if_true, if_false, mul_zero, zero_mul, sub_zero,
      zero_sub, add_zero, zero_add, mul_one, star_one, star_zero, star_neg, neg_zero, star_mul', sgn_star] <;>
    (try subst_vars) <;> unfold sgn <;> split_ifs <;>
    first | (exfalso; tauto) | (simp only [star_one, star_zero]; ring) | norm_num | (simp only [star_one, star_zero]; norm_num)

theorem isUe_zIm (ε : Fin m → Bool) (a b : Fin m) : IsUe ε (zIm ε a b) := by
  have e2 : star (-(Complex.I / 2)) = Complex.I / 2 := by
    apply Complex.ext <;> simp <;> norm_num
  ext i j
  simp only [IsUe, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply, zIm, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.single_apply, star_mul', star_add, e2]
  by_cases h1 : a = i <;> by_cases h2 : b = j <;> by_cases h3 : b = i <;> by_cases h4 : a = j <;>
    simp only [h1, h2, h3, h4, and_true, true_and, and_false, false_and, if_true, if_false, mul_zero, zero_mul, sub_zero,
      zero_sub, add_zero, zero_add, mul_one, star_one, star_zero, star_neg, neg_zero, star_mul', sgn_star] <;>
    (try subst_vars) <;> unfold sgn <;> split_ifs <;>
    first | (exfalso; tauto) | (simp only [star_one, star_zero]; ring) | ring | (simp only [star_one, star_zero]; norm_num)

theorem thetaInt_at {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V))
    (Φ : schwartzA θ V.rank n) (g : G D n) : thetaInt ω ν Φ g = thetaInt ω ν (ω g Φ) 1 := by
  have h : theta ω Φ g = theta ω (ω g Φ) 1 := by
    funext h
    simp only [theta, map_one, Module.End.one_apply]
  simp only [thetaInt, h]

theorem thetaInt_smul {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V))
    (r : ℂ) (Φ : schwartzA θ V.rank n) (g : G D n) : thetaInt ω ν (r • Φ) g = r * thetaInt ω ν Φ g := by
  have h : theta ω (r • Φ) g = fun h => r * theta ω Φ g h := by
    funext h
    simp only [theta, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact tsum_mul_left
  simp only [thetaInt, h, GlobalTheory.AutomorphicL2Unitary.descend, MeasureTheory.average_eq, integral_const_mul]
  exact (mul_smul_comm _ _ _).symm

theorem phiS_of_mem {θ : InfFam D} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ) (Ψ : Mx D m n → ℂ)
    (P : PX m n) (h : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : phiS θ τ fr c Ψ P = ⟨_, h⟩ := by
  unfold phiS; rw [dite_eq_left h]

theorem tens_add_smul {θ : InfFam D} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (c : ℝ) (Ψ : Mx D m n → ℂ)
    (A B : PX m n) (r : ℂ) :
    tens θ τ fr (fP c (A + r • B)) Ψ = tens θ τ fr (fP c A) Ψ + r • tens θ τ fr (fP c B) Ψ := by
  funext x
  simp only [tens, fP, evX, map_add (f := _), MvPolynomial.smul_eval, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.Rg.Sw.Glob.IInvH

namespace PositivityTheory.Rg.Sw.Glob

open IInvH in
theorem gIinv_of (hT : TensMem) (hL : ThLin) (hC : LieComm) (hO : DerivOne) : GIinv := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hx Ψ hΨ g a b P
  have hmem := fun Q => hT D n V θ l s τ ε fr hx.hθ (lNZ D ψ θ l hx.hψ hx.hθ hx.hl) hx.hs hx.hfr Ψ hΨ Q
  have hstd : ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ :=
    fun Φ hΦ => ⟨hx.hψ, hx.hχ, hx.hη, hx.hθ, hx.hμ, hx.hω, hx.hH, hx.hl, hx.hs, hx.hν, hΦ⟩

  have h0 : ∀ X, IsUe ε X → ∀ Q, thF ω ν τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X Q) g = 0 := by
    intro X hX Q
    unfold thF
    rw [thetaInt_at]
    exact hO D n V ψ χ θ μ ω H l s ν τ ε fr ι hx X hX (ω g (phiS θ τ fr (cLoc l τ) Ψ Q))
      (ω g (phiS θ τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X Q))) (fun x => hC D n V ψ χ θ μ ω H l s ν τ ε fr ι hx Ψ hΨ X hX Q g x)
  rw [hOp_eq]
  set A := vfX (cLoc l τ) (zRe ε a b) P
  set B := vfX (cLoc l τ) (zIm ε a b) P
  have hA := phiS_of_mem τ fr (cLoc l τ) Ψ A (hmem A).1
  have hB := phiS_of_mem τ fr (cLoc l τ) Ψ B (hmem B).1
  have hAB := phiS_of_mem τ fr (cLoc l τ) Ψ (A + Complex.I • B) (hmem (A + Complex.I • B)).1
  have hsum : phiS θ τ fr (cLoc l τ) Ψ (A + Complex.I • B) =
      phiS θ τ fr (cLoc l τ) Ψ A + Complex.I • phiS θ τ fr (cLoc l τ) Ψ B := by
    rw [hA, hB, hAB]
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul]
    exact tens_add_smul τ fr (cLoc l τ) Ψ A B Complex.I
  have hfA : (phiS θ τ fr (cLoc l τ) Ψ A).1 ∈ fockA θ V n l s := by rw [hA]; exact (hmem A).2
  have hfB : (Complex.I • phiS θ τ fr (cLoc l τ) Ψ B).1 ∈ fockA θ V n l s := by
    rw [hB, Submodule.coe_smul]; exact (fockA θ V n l s).smul_mem _ (hmem B).2
  unfold thF
  rw [hsum, hL D n V ψ χ θ μ ω H l s ν _ _ (hstd _ hfA) (hstd _ hfB) hx.hr g, thetaInt_smul]
  have e1 := h0 _ (isUe_zRe ε a b) P
  have e2 := h0 _ (isUe_zIm ε a b) P
  unfold thF at e1 e2
  rw [e1, e2]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end

