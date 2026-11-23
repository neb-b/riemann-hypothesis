module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.FromHCB

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem derivExists_allPos : DerivExistsAllPosStatement := by
  intro k V _ _ _ τ hτ
  classical
  have : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
  let ε : Fin k → Bool := fun _ => true
  let σ (g : Matrix (Fin k) (Fin k) ℂ) : V →L[ℂ] V :=
    if hg : g ∈ Kset ε then (τ (torepK ε hg)).val else 1
  have hσ {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Kset ε) :
      σ g = (τ (torepK ε hg)).val := dite_eq_left hg
  have hrep : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) σ := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have h1 : (1 : Matrix (Fin k) (Fin k) ℂ) ∈ Kset ε :=
        ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩
      rw [hσ h1, show torepK ε h1 = 1 from onep_KG_ext (toMK_torepK ε h1), map_one]
      rfl
    · intro a ha b hb
      change a ∈ Kset ε at ha
      change b ∈ Kset ε at hb
      have hab : a * b ∈ Kset ε := by
        refine ⟨Submonoid.mul_mem _ ha.1 hb.1, ?_⟩
        rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]
      have hmul : torepK ε hab = torepK ε ha * torepK ε hb := by
        apply onep_KG_ext
        change toMK (torepK ε hab) = toMK (torepK ε ha) * toMK (torepK ε hb)
        rw [toMK_torepK, toMK_torepK, toMK_torepK]
      rw [hσ hab, hσ ha, hσ hb, hmul]
      exact fh_op_mul τ _ _
    · intro g hg v
      rw [hσ hg]
      exact Unitary.norm_map _ v
    · intro v
      rw [continuousOn_iff_continuous_domRestrict]
      have hc : Continuous fun g : Kset ε => (τ (torepK ε g.2)).val v :=
        (continuous_subtype_val.comp (hτ.comp (continuous_torepK ε))).clm_apply continuous_const
      exact hc.congr fun g => (congrArg (fun A : V →L[ℂ] V => A v) (hσ g.2)).symm
  let b := stdOrthonormalBasis ℂ V
  have hcoeff (i j : Fin (Module.finrank ℂ V)) :=
    polynomial_coefficients k V σ ⊤ hrep inferInstance
      (fun _ _ _ _ => Submodule.mem_top) (b j) Submodule.mem_top (b i)
  choose m P hP using hcoeff
  let F (A : Matrix (Fin k) (Fin k) ℂ) : V →L[ℂ] V :=
    ∑ i, ∑ j, (MvPolynomial.eval (fhEnt k A) (P i j) * (A.det ^ m i j)⁻¹) •
      ((innerSL ℂ (b j)).smulRight (b i))
  have hF (g : KG ε) : F (toMK g) = (τ g).val := by
    have hg : toMK g ∈ Kset ε := g.2
    have hσg : σ (toMK g) = (τ g).val := by rw [hσ hg, torepK_toMK]
    have hc (i j : Fin (Module.finrank ℂ V)) :
        MvPolynomial.eval (fhEnt k (toMK g)) (P i j) * ((toMK g).det ^ m i j)⁻¹ =
          inner ℂ (b i) ((τ g).val (b j)) := by
      rw [← hσg, mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ (fh_det_ne_zero hg))]
      exact (hP i j _ hg).symm
    ext v
    simp only [F, hc, sum_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply]
    conv_rhs => rw [← b.sum_repr' v]
    simp only [map_sum, map_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [← b.sum_repr' ((τ g).val (b j)), Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  let _ : NormedRing (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedAlgebra
  let _ : NormedAlgebra ℝ (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedAlgebra
  have hdet : DifferentiableAt ℂ (fun A : Matrix (Fin k) (Fin k) ℂ => A.det) 1 := by
    rw [show (fun A : Matrix (Fin k) (Fin k) ℂ => A.det) = _ from funext fh_det_eq]
    exact fh_diff_eval _ _
  have hdiff : DifferentiableAt ℂ F 1 := by
    apply DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => ?_
    exact ((fh_diff_eval (P i j) _).mul ((hdet.pow _).inv (by simp))).smul_const _
  refine ⟨(fderiv ℂ F 1).toLinearMap, ?_⟩
  intro X _ γ hγ
  have hexp := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at hexp
  have hcomp := (hdiff.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 hexp (by simp)
  have hcurve : (fun t : ℝ => (τ (γ t)).val) = F ∘ fun t : ℝ => NormedSpace.exp (t • X) := by
    funext t
    rw [Function.comp_apply, ← Complex.coe_smul, ← hγ t, hF]
  rw [hcurve]
  exact hcomp

theorem kType_of_hcTypeU {k : ℕ} {u : Fin k → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (hπ : Formalism.MainNotions.S.IsHCTypeU k u π) :
    ∃ T : KType (fun _ : Fin k => true) (lowK (fun _ : Fin k => true) u), ∃ U : H ≃ₗᵢ[ℂ] T.V,
      ∀ (g : KG (fun _ : Fin k => true)) (v : H), U (π (toMK g) v) = T.op g (U v) := by
  obtain ⟨hnt, hfd, hU, hK⟩ := hπ
  haveI := hfd
  haveI : CompleteSpace H := FiniteDimensional.complete ℂ H
  obtain ⟨dτ, hd⟩ := derivExists_allPos k H (fhTau π hU) (fhTau_cont π hU)
  have hσ : ∀ g, π (toMK g) = ((fhTau π hU g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) :=
    fun g => (fhTau_coe π hU g).symm
  obtain ⟨_, _, hirr, ⟨v, -, hv0, hvw⟩, hdom⟩ := hK
  have hwt := fun a => fh_dτ_of_wt (fhTau π hU) dτ hd π hσ hvw a
  have hhw := fun a b hab => fh_hw (fhTau π hU) dτ hd π hσ hdom hvw a b hab
  let T : KType (fun _ : Fin k => true) (lowK (fun _ : Fin k => true) u) :=
    { V := H
      τ := fhTau π hU
      cont := fhTau_cont π hU
      irred := ?irr
      dτ := dτ
      hasDeriv := hd
      w := ((‖v‖⁻¹ : ℝ) : ℂ) • v
      w_norm := ?nrm
      w_wt := ?wt
      w_hw := ?hw }
  refine ⟨T, LinearIsometryEquiv.refl ℂ H, ?_⟩
  case irr =>
    intro W hW
    apply hirr W le_top
    intro g hg x hx
    have := hW (torepK _ hg) x hx
    rw [← hσ] at this
    first
    | (rwa [toMK_torepK (fun _ : Fin k => true) hg] at this)
    | (convert this using 2; exact (toMK_torepK (fun _ : Fin k => true) hg).symm)
  case nrm =>
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)
  case wt =>
    intro a
    rw [map_smul, hwt a]
    exact smul_comm _ _ _
  case hw =>
    intro a b hab _
    rw [map_smul, hhw a b hab, smul_zero]
  intro g x
  first
  | (simp only [LinearIsometryEquiv.refl_apply, KType.op, hσ])
  | (show π (toMK g) x = ((fhTau π hU g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x; rw [hσ])

end ReciprocityTheory.ChartRestriction.DS.HW
