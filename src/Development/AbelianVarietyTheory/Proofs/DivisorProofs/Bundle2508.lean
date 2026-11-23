module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousPeriodLatticeBasisArc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.Rigdesc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0080
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousPeriodBasisAlongArcStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_period_basis_along_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), GoodEmb c σ → 1 ≤ Dw.p + Dw.q → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ∀ s, (spMap (ψ u) ≫ x) s ∉ genBd Z) → ∃ (T₀ : ℝ) (m : ℕ) (lam : ℂ → Fin m → Fin g → ℂ), (∀ w : ℂ, T₀ < w.im → eTwoPi w ∈ Metric.ball (0 : ℂ) r) ∧ ContinuousOn lam {w : ℂ | T₀ < w.im} ∧ (∀ w : ℂ, T₀ < w.im → LinearIndependent ℝ (lam w) ∧ Submodule.span ℝ (Set.range (lam w)) = ⊤) ∧ (∀ w : ℂ, T₀ < w.im → ∀ ex : (Fin g → ℂ) → (Over.mk (spMap (ψ (eTwoPi w)) ≫ x ≫ genι Z) ⟶ Z.t.G), (∀ z z', ex (z + z') = ex z * ex z') → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ Z.t.G.left from (ex z).left)) → (∀ j, IsDerivAt0 (fun z => (ex z).left) (Pi.single j 1) (spMap (dualMap (ψ (eTwoPi w))) ≫ fr.v (e j).1 (e j).2)) → ∀ z, ex z = 1 ↔ ∃ n : Fin m → ℤ, z = ∑ j, n j • lam w j) ∧ ∀ R : ℝ, ∃ (C : ℝ) (B : ℕ), ∀ w : ℂ, T₀ < w.im → |w.re| ≤ R → ‖lam w‖ ≤ C * w.im ^ B := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ r g e hσ hpq harc hin
  obtain ⟨g', ρ, e', hρ, hρr, hol, hexp, -⟩ := _root_.GlobalTheory.RelExp.exists_exp_along_disc Z.X Z.t.G (fun u => spMap (ψ u) ≫ x ≫ genι Z) r
    Z.t.semi harc.1.1 (GlobalTheory.ShFam.BdArc.LatSec.isHolTo_spMap harc.1 _)
  obtain ⟨h, hh⟩ := _root_.GlobalTheory.ShFam.BdArc.exists_frame_change E H Dw l Xo c O β Z σ A φ x fr ψ r g e g' ρ e' harc hρ hρr hol hexp
  obtain ⟨ρ₀, m, lamE, hρ₀, hρ₀ρ, hcont, hlat, C, k, hC⟩ :=
    _root_.GlobalTheory.ShFam.BdArc.ArcLat.exists_continuous_latBasis_of_arc E H Dw l Xo c O β Z σ A φ x ψ r g' ρ e' hσ hpq harc hin hρ hρr hol hexp
  have hper : ∀ s : ℂ, s.re < 0 → ∀ z, (∃ n : Fin m → ℤ, z = ∑ j, n j • lamE (s + 2 * Real.pi * Complex.I) j) ↔
      ∃ n : Fin m → ℤ, z = ∑ j, n j • lamE s j := by
    intro s hs z
    have hs' : (s + 2 * Real.pi * Complex.I).re < 0 := by simpa using hs
    rw [← (hlat _ hs').2.2, ← (hlat s hs).2.2, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hcb : Metric.closedBall (0 : ℂ) (ρ₀ / 2) ⊆ Metric.ball 0 ρ := Metric.closedBall_subset_ball (by linarith)
  obtain ⟨Ch, hCh⟩ := (isCompact_closedBall (0 : ℂ) (ρ₀ / 2)).exists_bound_of_continuousOn
    (fun u hu => ((hh u (hcb hu)).2.1).continuousWithinAt)
  have hCh0 : 0 ≤ Ch := (norm_nonneg _).trans (hCh 0 (Metric.mem_closedBall_self (by linarith)))
  set T₀ : ℝ := max 1 (Real.log (2 / ρ₀) / (2 * Real.pi)) with hT₀
  let sOf : ℂ → ℂ := fun w => 2 * Real.pi * Complex.I * w - (Real.log ρ₀ : ℂ)
  have hsOf : Continuous sOf := by fun_prop
  have hnorm : ∀ w : ℂ, ‖eTwoPi w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
    intro w
    rw [eTwoPi, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  have hsmall : ∀ w : ℂ, T₀ < w.im → ‖eTwoPi w‖ < ρ₀ / 2 := by
    intro w hw
    have h1 : Real.log (2 / ρ₀) < 2 * Real.pi * w.im := by
      have := (le_max_right _ _).trans_lt hw
      rw [div_lt_iff₀ (by positivity)] at this
      linarith
    rw [hnorm]
    calc Real.exp (-(2 * Real.pi * w.im)) < Real.exp (-Real.log (2 / ρ₀)) := Real.exp_lt_exp.2 (by linarith)
      _ = ρ₀ / 2 := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have hueq : ∀ w : ℂ, (ρ₀ : ℂ) * Complex.exp (sOf w) = eTwoPi w := by
    intro w
    simp only [sOf, eTwoPi]
    rw [Complex.exp_sub, ← Complex.ofReal_exp, Real.exp_log hρ₀, mul_div_cancel₀ _ (by exact_mod_cast hρ₀.ne')]
  have hexps : ∀ w : ℂ, ‖Complex.exp (sOf w)‖ = ‖eTwoPi w‖ / ρ₀ := by
    intro w
    rw [← hueq w, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ₀.le, mul_div_cancel_left₀ _ hρ₀.ne']
  have hexp2 : ∀ w : ℂ, T₀ < w.im → ‖Complex.exp (sOf w)‖ ≤ 1 / 2 := by
    intro w hw
    rw [hexps, div_le_iff₀ hρ₀]
    linarith [hsmall w hw]
  have hsre : ∀ w : ℂ, T₀ < w.im → (sOf w).re < 0 := by
    intro w hw
    have h1 := hexp2 w hw
    rw [Complex.norm_exp] at h1
    by_contra hc
    push_neg at hc
    have := Real.one_le_exp hc
    linarith
  have hub : ∀ w : ℂ, T₀ < w.im → eTwoPi w ∈ Metric.closedBall (0 : ℂ) (ρ₀ / 2) := fun w hw =>
    mem_closedBall_zero_iff.2 (hsmall w hw).le
  refine ⟨T₀, m, fun w j => (h (eTwoPi w)).inverse (lamE (sOf w) j), fun w hw => ?_, ?_, fun w hw => ?_,
    fun w hw ex hadd hex hd z => ?_, fun R => ?_⟩
  · exact Metric.ball_subset_ball (hρ₀ρ.le.trans hρr) (Metric.ball_subset_ball (by linarith) (mem_ball_zero_iff.2 (hsmall w hw)))
  · have hopen : IsOpen {w : ℂ | T₀ < w.im} := isOpen_lt continuous_const Complex.continuous_im
    refine fun w hw => ContinuousAt.continuousWithinAt ?_
    have hi : ContinuousAt (fun w => (h (eTwoPi w)).inverse) w :=
      ContinuousAt.comp (f := eTwoPi) (g := fun u => (h u).inverse) ((hh _ (hcb (hub w hw))).2.1)
        (by unfold eTwoPi; fun_prop)
    have hl : ContinuousAt (fun w => lamE (sOf w)) w :=
      ContinuousAt.comp (g := lamE) ((hcont.continuousAt (isOpen_lt Complex.continuous_re continuous_const |>.mem_nhds (hsre w hw))))
        hsOf.continuousAt
    exact continuousAt_pi.2 fun j => hi.clm_apply ((continuous_apply j).continuousAt.comp hl)
  · obtain ⟨L, hL⟩ := (hh _ (hcb (hub w hw))).1
    obtain ⟨hli, hsp, -⟩ := hlat _ (hsre w hw)
    simp only [← hL, ContinuousLinearMap.inverse_equiv]
    refine ⟨hli.map' (L.symm.toLinearEquiv.restrictScalars ℝ).toLinearMap (LinearEquiv.ker _), ?_⟩
    have : (Set.range fun j => (L.symm : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (lamE (sOf w) j)) =
        (L.symm.toLinearEquiv.restrictScalars ℝ).toLinearMap '' Set.range (lamE (sOf w)) := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨L, hL⟩ := (hh _ (hcb (hub w hw))).1
    have h1 := (hlat _ (hsre w hw)).2.2 (h (eTwoPi w) z)
    rw [hueq w] at h1
    rw [(hh _ (hcb (hub w hw))).2.2 ex hadd hex hd z, h1]
    simp only [← hL, ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe]
    refine exists_congr fun n => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ∑ j, n j • L.symm (lamE (sOf w) j) = L.symm (∑ j, n j • lamE (sOf w) j) by
        rw [map_sum]; exact Finset.sum_congr rfl fun j _ => (map_zsmul L.symm _ _).symm,
      ContinuousLinearEquiv.eq_symm_apply]
  · obtain ⟨C', hC'⟩ := _root_.GlobalTheory.StripGrowth.strip_growth g' m lamE C k hcont (fun s hs => (hlat s hs).1) hper hC (2 * Real.pi * |R|)
    set D : ℝ := 1 + 2 * Real.pi + |Real.log ρ₀| + 2 * Real.pi * |R|
    refine ⟨Ch * max C' 0 * D ^ k, k, fun w hw hR => ?_⟩
    have hw1 : 1 ≤ w.im := (le_max_left _ _).trans hw.le
    have hsim : (sOf w).im = 2 * Real.pi * w.re := by simp [sOf, Complex.mul_re, Complex.mul_im]
    have hsre' : (sOf w).re = -(2 * Real.pi * w.im) - Real.log ρ₀ := by simp [sOf, Complex.mul_re, Complex.mul_im]
    have hsi : |(sOf w).im| ≤ 2 * Real.pi * |R| := by
      rw [hsim, abs_mul, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left (hR.trans (le_abs_self R)) (by positivity)
    have hb := hC' _ (hsre w hw) (hexp2 w hw) hsi
    have hsn : 1 + ‖sOf w‖ ≤ D * w.im := by
      have h2 := Complex.norm_le_abs_re_add_abs_im (sOf w)
      have h3 : |(sOf w).re| ≤ 2 * Real.pi * w.im + |Real.log ρ₀| := by
        rw [hsre']
        refine (abs_sub _ _).trans ?_
        rw [abs_neg, abs_of_pos (by positivity)]
      have h4 : 0 ≤ w.im - 1 := by linarith
      have h5 : 0 ≤ |Real.log ρ₀| + 2 * Real.pi * |R| + 1 := by positivity
      nlinarith [Real.pi_pos]
    have hpow : (1 + ‖sOf w‖) ^ k ≤ D ^ k * w.im ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hsn k
    have hlamn : ‖lamE (sOf w)‖ ≤ max C' 0 * (D ^ k * w.im ^ k) :=
      hb.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hpow (le_max_right _ _)))
    have hCu := hCh _ (hub w hw)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    calc ‖(h (eTwoPi w)).inverse (lamE (sOf w) j)‖ ≤ ‖(h (eTwoPi w)).inverse‖ * ‖lamE (sOf w) j‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ Ch * ‖lamE (sOf w)‖ := mul_le_mul hCu (norm_le_pi_norm _ j) (norm_nonneg _) hCh0
      _ ≤ Ch * (max C' 0 * (D ^ k * w.im ^ k)) := mul_le_mul_of_nonneg_left hlamn hCh0
      _ = Ch * max C' 0 * D ^ k * w.im ^ k := by ring

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeeperPointIntegralClosureGaloisStalk
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.RingSide

variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂]
  [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {z₁ : M₁.Z}
  [Algebra (M₁.Z.presheaf.stalk z₁) Ω₂]

def jMap (z₂ : M₂.Z) (h : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂) :
    integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ →+* M₂.Z.presheaf.stalk z₂ :=
  (M₂.stalkEquiv z₂).symm.toRingHom.comp ((RingHom.id Ω₂).restrict _ (M₂.O z₂) h)

theorem stalkHom_jMap (z₂ : M₂.Z) (h : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) : M₂.stalkHom z₂ (jMap z₂ h b) = b := by
  rw [← RatModel.coe_stalkEquiv]
  simp [jMap]

theorem jMap_mem_max_iff (z₂ : M₂.Z) (h : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (c : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) :
    jMap z₂ h c ∈ maximalIdeal (M₂.Z.presheaf.stalk z₂) ↔ ¬ ((c : Ω₂) ≠ 0 ∧ (c : Ω₂)⁻¹ ∈ M₂.O z₂) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ← MulEquiv.isUnit_map (M₂.stalkEquiv z₂).toMulEquiv, RatModel.isUnit_O_iff]
  change ¬ ((M₂.stalkEquiv z₂ (jMap z₂ h c) : Ω₂) ≠ 0 ∧ (M₂.stalkEquiv z₂ (jMap z₂ h c) : Ω₂)⁻¹ ∈ M₂.O z₂) ↔ _
  rw [RatModel.coe_stalkEquiv, stalkHom_jMap]

theorem algHom_mem_integralClosure
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x))
    (τ : Ω₂ →ₐ[Ω₁] Ω₂) {b : Ω₂} (hb : b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) :
    τ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ := by
  let τ' : Ω₂ →ₐ[M₁.Z.presheaf.stalk z₁] Ω₂ :=
    { τ.toRingHom with
      commutes' := fun x => by
        change τ (algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x) = algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x
        rw [halg]
        exact τ.commutes _ }
  exact IsIntegral.map τ' hb

theorem algHom_mem_O
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x)) {z₂ : M₂.Z}
    (hB : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (hloc : ∀ x ∈ M₂.O z₂, ∃ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      ∃ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 ∧ s⁻¹ ∈ M₂.O z₂ ∧ x = b / s)
    (τ : Ω₂ →ₐ[Ω₁] Ω₂)
    (hu : ∀ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 → s⁻¹ ∈ M₂.O z₂ → (τ s)⁻¹ ∈ M₂.O z₂)
    {x : Ω₂} (hx : x ∈ M₂.O z₂) : τ x ∈ M₂.O z₂ := by
  obtain ⟨b, hb, s, hs, hs0, hsO, rfl⟩ := hloc x hx
  rw [map_div₀, div_eq_mul_inv]
  exact mul_mem (hB _ (algHom_mem_integralClosure halg τ hb)) (hu s hs hs0 hsO)

end GlobalTheory.Poinc.RingSide

namespace GlobalTheory.Poinc.RingSide

variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂]
  [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {z₁ : M₁.Z}
  [Algebra (M₁.Z.presheaf.stalk z₁) Ω₂]

theorem exists_stalk_ringEquiv
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x)) (z₂ : M₂.Z)
    (hB : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (hloc : ∀ x ∈ M₂.O z₂, ∃ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      ∃ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 ∧ s⁻¹ ∈ M₂.O z₂ ∧ x = b / s)
    (σ : Ω₂ ≃ₐ[Ω₁] Ω₂)
    (H : ∀ b b' : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, (b' : Ω₂) = σ b →
      (jMap z₂ hB b ∈ maximalIdeal (M₂.Z.presheaf.stalk z₂) ↔ jMap z₂ hB b' ∈ maximalIdeal (M₂.Z.presheaf.stalk z₂))) :
    ∃ σ₂ : M₂.Z.presheaf.stalk z₂ ≃+* M₂.Z.presheaf.stalk z₂, ∀ x, M₂.stalkHom z₂ (σ₂ x) = σ (M₂.stalkHom z₂ x) := by
  have hu : ∀ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 → s⁻¹ ∈ M₂.O z₂ →
      (σ.toAlgHom s)⁻¹ ∈ M₂.O z₂ := by
    intro s hs hs0 hsO
    have hs' : σ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ :=
      algHom_mem_integralClosure halg σ.toAlgHom hs
    have key := H ⟨s, hs⟩ ⟨σ s, hs'⟩ rfl
    rw [jMap_mem_max_iff, jMap_mem_max_iff] at key
    exact ((not_iff_not.mp key).mp ⟨hs0, hsO⟩).2
  have hu' : ∀ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 → s⁻¹ ∈ M₂.O z₂ →
      (σ.symm.toAlgHom s)⁻¹ ∈ M₂.O z₂ := by
    intro s hs hs0 hsO
    have ht : σ.symm s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ :=
      algHom_mem_integralClosure halg σ.symm.toAlgHom hs
    have key := H ⟨σ.symm s, ht⟩ ⟨s, hs⟩ (σ.apply_symm_apply s).symm
    rw [jMap_mem_max_iff, jMap_mem_max_iff] at key
    exact ((not_iff_not.mp key).mpr ⟨hs0, hsO⟩).2
  have hσ : ∀ x ∈ M₂.O z₂, σ x ∈ M₂.O z₂ := fun x hx =>
    algHom_mem_O halg hB hloc σ.toAlgHom hu hx
  have hσ' : ∀ x ∈ M₂.O z₂, σ.symm x ∈ M₂.O z₂ := fun x hx =>
    algHom_mem_O halg hB hloc σ.symm.toAlgHom hu' hx
  let e : M₂.O z₂ ≃+* M₂.O z₂ :=
    { toFun := fun x => ⟨σ x, hσ x x.2⟩
      invFun := fun x => ⟨σ.symm x, hσ' x x.2⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : Ω₂))
      right_inv := fun x => Subtype.ext (σ.apply_symm_apply (x : Ω₂))
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : Ω₂) y)
      map_add' := fun x y => Subtype.ext (map_add σ (x : Ω₂) y) }
  refine ⟨(M₂.stalkEquiv z₂).trans (e.trans (M₂.stalkEquiv z₂).symm), fun x => ?_⟩
  rw [← RatModel.coe_stalkEquiv, ← RatModel.coe_stalkEquiv]
  simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  rfl

theorem injective_of_ext
    (halg : ∀ x, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₂ x = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x)) {z₂ : M₂.Z}
    (hB : ∀ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ M₂.O z₂)
    (hloc : ∀ x ∈ M₂.O z₂, ∃ b ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      ∃ s ∈ integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, s ≠ 0 ∧ s⁻¹ ∈ M₂.O z₂ ∧ x = b / s)
    {V V' : Type} [CommRing V] [CommRing V'] (ev : M₁.Z.presheaf.stalk z₁ →+* V) (io : V →+* V')
    (ev₂ : M₂.Z.presheaf.stalk z₂ →+* V') (hev : Function.Injective ev) (hio : Function.Injective io)
    (hE : ∀ x x₂, M₂.stalkHom z₂ x₂ = algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ x) → ev₂ x₂ = io (ev x)) :
    Function.Injective ev₂ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  by_contra hy0
  have hY : M₂.stalkHom z₂ y ≠ 0 := by
    intro h
    apply hy0
    apply M₂.stalkHom_injective z₂
    rw [h, map_zero]
  have hYO : M₂.stalkHom z₂ y ∈ M₂.O z₂ := by
    rw [← RatModel.coe_stalkEquiv]
    exact (M₂.stalkEquiv z₂ y).2
  obtain ⟨b, hb, s, hs, hs0, -, hYe⟩ := hloc _ hYO
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_div] at hYe
    exact hY hYe
  have hjb : jMap z₂ hB ⟨b, hb⟩ = y * jMap z₂ hB ⟨s, hs⟩ := by
    apply M₂.stalkHom_injective z₂
    rw [map_mul, stalkHom_jMap, stalkHom_jMap, hYe]
    exact (div_mul_cancel₀ b hs0).symm
  have hev0 : ev₂ (jMap z₂ hB ⟨b, hb⟩) = 0 := by
    rw [hjb, map_mul, hy, zero_mul]
  have hbB : (⟨b, hb⟩ : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) ≠ 0 := fun h =>
    hb0 (congrArg Subtype.val h)
  have hne := Ideal.comap_ne_bot_of_integral_mem hbB (Ideal.mem_span_singleton_self _)
    (integralClosure.isIntegral _)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, hc⟩ := ha
  have h1 : ev₂ (jMap z₂ hB (algebraMap _ _ a)) = io (ev a) := by
    apply hE
    rw [stalkHom_jMap]
    exact halg a
  have h2 : ev₂ (jMap z₂ hB (algebraMap _ _ a)) = 0 := by
    rw [← hc, map_mul, map_mul, hev0, mul_zero]
  rw [h2] at h1
  have h3 : ev a = ev 0 := hio (by rw [map_zero, map_zero, ← h1])
  exact ha0 (hev h3)

end GlobalTheory.Poinc.RingSide


open GlobalTheory.Poinc.RingSide in
theorem GlobalTheory.Poinc.Sep.Tower.exists_point_integralClosure_stalk : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra; ∃ (z₂ : 𝔗.X₂.M.Z) (j₂ : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ →+* 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.p z₂ = z₁ ∧ (∀ b, 𝔗.X₂.M.stalkHom z₂ (j₂ b) = b) ∧ ((maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂).IsMaximal ∧ (∀ x : 𝔗.X₂.Ω₁, (∀ w, 𝔗.p w = z₁ → x ∈ 𝔗.X₂.M.O w) → x ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁) ∧ (∀ σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁, (∀ b b' : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, (b' : 𝔗.X₂.Ω₁) = σ b → (j₂ b ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂) ↔ j₂ b' ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂))) → ∃ σ₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ ≃+* 𝔗.X₂.M.Z.presheaf.stalk z₂, ∀ x, 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = σ (𝔗.X₂.M.stalkHom z₂ x)) ∧ ∀ (V : Type) [CommRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (V' : Type) [CommRing V'] (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective ev → Function.Injective io → 𝔗.Ext ev io ev₂ → Function.Injective ev₂ := by
  intro g n F W Z i X₁ act 𝔗 z₁
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ :=
    ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
  have halg : ∀ x, algebraMap (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ x =
      algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom z₁ x) := fun _ => rfl
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme 𝔗.X₂.M.Z := by
    exact @GlobalTheory.IsNormalScheme.pred _ 𝔗.X₂.normal
  obtain ⟨𝔷, h𝔷⟩ := Ideal.exists_maximal (integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁)
  obtain ⟨z₂, hz₂, hmem⟩ := GlobalTheory.Poinc.FinPts.maximal_point hN 𝔗.p_fin 𝔗.p_pt halg 𝔷 h𝔷
  have hB : ∀ b ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, b ∈ 𝔗.X₂.M.O z₂ :=
    fun b hb => GlobalTheory.Poinc.FinPts.mem_O_of_isIntegral hN 𝔗.p_pt halg hb hz₂
  have hloc := GlobalTheory.Poinc.exists_div_integralClosure_of_mem_O _ _ _ _ X₁.M 𝔗.X₂.M 𝔗.p hN
    𝔗.p_fin 𝔗.p_pt z₁ z₂ hz₂
  refine ⟨z₂, jMap z₂ hB, hz₂, fun b => stalkHom_jMap z₂ hB b, ?_, ?_, ?_, ?_⟩
  · have hc : (maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap (jMap z₂ hB) = 𝔷 := by
      ext c
      rw [Ideal.mem_comap, jMap_mem_max_iff, hmem c]
      tauto
    rw [hc]
    exact h𝔷
  · intro x hx
    exact GlobalTheory.Poinc.FinPts.isIntegral_of_mem_O 𝔗.p_fin 𝔗.p_pt halg hx
  · intro σ H
    exact exists_stalk_ringEquiv halg z₂ hB hloc σ H
  · intro V _ ev V' _ io ev₂ hev hio hE
    exact injective_of_ext halg hB hloc ev io ev₂ hev hio hE.2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentMumfordBundleQuotient
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotDesc

def idq {S : Scheme.{0}} {A B : Over S} (q : A ⟶ B) : A ⊗ A ⟶ A ⊗ B := lift (fst A A) (snd A A ≫ q)

theorem evc_lam {S : Scheme.{0}} {A Y : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hΛ : (abelian₂ A L).IsLB)
    (a b : Y ⟶ A) : evc hΛ a b = lam (cls L hL) a b := by
  rw [evc, show cls _ hΛ = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hΛ, pull_lam, lift_fst,
    lift_snd]

theorem lam_mul_right_sub {S : Scheme.{0}} {A Y : Over S} [GrpObj A] [IsCommMonObj A] (c : Pic A.left)
    (a k y : Y ⟶ A) : lam c a (k * y) - lam c a y = lam c (a * y) k - lam c y k := by
  simp only [lam]
  rw [show a * y * k = a * (k * y) by rw [_root_.mul_assoc, _root_.mul_comm y k],
    show y * k = k * y from _root_.mul_comm y k]
  abel

theorem exists_descent_lam : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (H : Over (Sp R)) [GrpObj H] (i : H ⟶ A), IsMonHom i →
    Mono i → IsFinite H.hom → Flat H.hom →
    (∀ (T : Over (Sp R)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ i = x) →
    ∀ (B : Over (Sp R)) [GrpObj B] (q : A ⟶ B), IsAbelianScheme B → IsMonHom q → IsFinite q.left → Flat q.left →
    Surjective q.left → IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q →
    ∃ (P : LB (A ⊗ B).left) (hP : P.IsLB), ∀ (Y : Over (Sp R)) (a x : Y ⟶ A),
      evc hP a (x ≫ q) = GlobalTheory.CechPic.pull (a * x).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) -
        GlobalTheory.CechPic.pull x.left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL) := by
  intro R _ _ A _ hA L hL H _ i _ _ _ _ hK B _ q hB _ hqf hqfl hqs hpb
  have := hA.comm
  have hΛ : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hku : lam (cls L hL) (fst A H) (snd A H ≫ i) = 0 := by
    rw [← evc_lam hL hΛ, ← triv_ev_iff hΛ]
    exact lam_triv_of_memKL _ A hA L hL H i ((hK H i).2 ⟨𝟙 H, Category.id_comp i⟩)
  have := hB.smooth
  have := hqf
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have hlfp : LocallyOfFinitePresentation q.left := inferInstance
  obtain ⟨-, h2⟩ := CompanionTheory.PfDual.rigDescent_holds (Sp R) A A B hA q hqfl hlfp hqs
  have hrig : Triv (ev (abelian₂ A L) (1 : A ⟶ A) (𝟙 A)) := by
    rw [triv_ev_iff hΛ, evc_lam hL hΛ, lam_one_left]
  have hinv : ∀ (T : Over (Sp R)) (x x' : T ⟶ A), x ≫ q = x' ≫ q →
      LBIso (ev (abelian₂ A L) (fst A T) (snd A T ≫ x)) (ev (abelian₂ A L) (fst A T) (snd A T ≫ x')) := by
    intro T x x' hxx
    refine (cls_eq_iff (pull_isLB hΛ _) (pull_isLB hΛ _)).1 ?_
    rw [cls_ev hΛ, cls_ev hΛ, evc_lam hL hΛ, evc_lam hL hΛ]
    obtain ⟨z, hz1, hz2⟩ : ∃ z : T ⟶ H ⊗ A, z ≫ ((fst H A ≫ i) * snd H A) = x ∧ z ≫ snd H A = x' :=
      ⟨_, hpb.lift_fst x x' hxx, hpb.lift_snd x x' hxx⟩
    subst hz1 hz2
    have ex : snd A T ≫ z ≫ ((fst H A ≫ i) * snd H A) =
        (snd A T ≫ z ≫ fst H A ≫ i) * (snd A T ≫ z ≫ snd H A) := by
      rw [MonObj.comp_mul, MonObj.comp_mul]
    rw [ex, ← sub_eq_zero, lam_mul_right_sub]
    have k : ∀ u : A ⊗ T ⟶ A, lam (cls L hL) u (snd A T ≫ z ≫ fst H A ≫ i) = 0 := fun u => by
      have e := congrArg (GlobalTheory.CechPic.pull (lift u (snd A T ≫ z ≫ fst H A)).left) hku
      rwa [map_zero, pull_lam, lift_fst, lift_snd_assoc, Category.assoc, Category.assoc] at e
    rw [k, k, sub_zero]
  obtain ⟨N, hN, -, hiso⟩ := h2 (abelian₂ A L) hΛ hrig hinv
  refine ⟨N, hN, fun Y a x => ?_⟩
  have hPc : GlobalTheory.CechPic.pull (idq q).left (cls N hN) = cls (abelian₂ A L) hΛ :=
    ((cls_eq_iff hΛ (pull_isLB hN _)).2 hiso).symm
  have e : lift a (x ≫ q) = lift a x ≫ idq q := by
    simp [idq]
  rw [evc, e, Over.comp_left, pull_comp, hPc, show cls _ hΛ = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hΛ, pull_lam, lift_fst,
    lift_snd]
  rfl

end GlobalTheory.QuotDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrCentredPointGenericBothModels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DvrTrait
open GlobalTheory.Points

theorem exists_factor_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    {K : Type} [Field K] (y : Sp K ⟶ M.Z) (hy : ∀ w, y w = genericPoint M.Z) :
    ∃ β : Ω →+* K, y = spMap β ≫ M.pt := by
  have hs : ∀ w, y w ⤳ genericPoint M.Z := fun w => (hy w) ▸ specializes_rfl
  have hm : ∀ x : Ω, x ∈ M.O (genericPoint M.Z) := fun x => by rw [RatModel.O_genericPoint]; trivial
  let β : Ω →+* K := (RatModel.valHomOf y _ hs).comp
    ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z)).toSubring hm)
  refine ⟨β, ?_⟩
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) (x := genericPoint M.Z) (U := ⊤) trivial
  have h1 := top_le_preimage_of_specializes hs hz
  have h2 : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt ⟨_, hz⟩
  refine ext_of_valR hU h1 (le_preimage_comp _ _ h2 (le_preimage_top _)) fun f => ?_
  exact ((valR_spMap_comp β M.pt U h2 f).trans (RatModel.val_valF ((top_le_preimage_iff _ _).1 h1) f)).symm

theorem exists_trait : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (Y X M : RatModel o Ω)
    (f : M.Z ⟶ X.Z) (d : Y.Z ⟶ X.Z), X.IsHom M (AlgHom.id o Ω) f → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d →
    ∀ z : M.Z, f z ∈ Set.range d → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (ξ : Sp V ⟶ M.Z) (τ : Sp V ⟶ Y.Z) (κ : Ω →+* FractionRing V), z ∈ Set.range ξ ∧
      spMap (algebraMap V (FractionRing V)) ≫ ξ = spMap κ ≫ M.pt ∧
      spMap (algebraMap V (FractionRing V)) ≫ τ = spMap κ ≫ Y.pt := by
  intro o Ω _ _ _ _ Y X M f d hf hd hop z hz
  obtain ⟨V, _, _, _, _, ξ, -, hξ, w, hw⟩ := GlobalTheory.DvrCentre.exists_complete_dvr_centre o Ω M z
  have ef : M.pt ≫ f = X.pt := by
    have h := hf
    have e : spMap (AlgHom.id o Ω).toRingHom = 𝟙 _ := Spec.map_id _
    rw [RatModel.IsHom, e, Category.id_comp] at h
    exact h
  have ed : Y.pt ≫ d = X.pt := by
    have h := hd
    have e : spMap (AlgHom.id o Ω).toRingHom = 𝟙 _ := Spec.map_id _
    rw [RatModel.IsHom, e, Category.id_comp] at h
    exact h
  have hbot : ξ (⊥ : PrimeSpectrum V) = genericPoint M.Z := by
    have h2 : (⊥ : PrimeSpectrum V) ⤳ w := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    have h3 := h2.map ξ.continuous
    rw [hw] at h3
    exact (h3.antisymm (genericPoint_specializes _)).eq
  have hy : ∀ u, (spMap (algebraMap V (FractionRing V)) ≫ ξ) u = genericPoint M.Z := fun u => by
    refine (Scheme.Hom.comp_apply _ _ _).trans (Eq.trans (congrArg ξ ?_) hbot)
    rw [Subsingleton.elim u (⊥ : PrimeSpectrum (FractionRing V))]
    exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V)))
  obtain ⟨κ, hκ⟩ := exists_factor_pt M _ hy
  have hsp : ∀ u : Sp V, (ξ ≫ f) u ⤳ f z := fun u => by
    rw [← hξ, Scheme.Hom.comp_apply]
    exact ((IsLocalRing.specializes_closedPoint (R := V) u).map ξ.continuous).map f.continuous
  have hr : Set.range (ξ ≫ f) ⊆ Set.range d := by
    rintro _ ⟨u, rfl⟩
    exact (hsp u).mem_open d.isOpenEmbedding.isOpen_range hz
  refine ⟨V, inferInstance, inferInstance, inferInstance, ξ, IsOpenImmersion.lift d (ξ ≫ f) hr, κ,
    ⟨_, hξ⟩, hκ, ?_⟩
  rw [← cancel_mono d, Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc, hκ, Category.assoc,
    Category.assoc, ef, ed]

end GlobalTheory.DvrTrait
end

