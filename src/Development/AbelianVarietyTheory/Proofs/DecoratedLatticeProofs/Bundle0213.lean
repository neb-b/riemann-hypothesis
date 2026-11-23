module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunEqZeroOfOrthHeisenbergTranslates
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaIrred

theorem prod_eq_zero {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (v : VolM D T.rank S.rank)
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (horth : ∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u g) = 0) (u x : WO S T) :
    f x * star (heisO ψ S T u g x) = 0 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have hμ : v.μ.IsAddHaarMeasure := v.covol.1
  have h𝓕 : IsAddFundamentalDomain (ratL T S) v.𝓕 v.μ := v.covol.2.1
  obtain ⟨l1, l2, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  obtain ⟨hth, hcomp, -⟩ := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hu := hth u g hg
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      have : Continuous fun x : WO S T => symplOH S T x (γ : WO S T) :=
        GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const
      simp only [← l4]
      exact hψ.1.1.comp (this.add this))
    (fun γ x y => by
      simp only [← l4, l1, AddChar.map_add_eq_mul]
      ring)
    (fun γ γ' x => by
      simp only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]
      ring)
    (fun x => by
      simp only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by
      rw [← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    v.μ v.𝓕 hμ h𝓕 (fun x => f x * star (heisO ψ S T u g x))
    (hf.cont.mul hu.cont.star)
    (fun γ hγ x => GlobalTheory.ThetaSchur.prod_periodic hψ hf hu hγ x)
    (fun γ => by
      have hneg : ∀ x, symplO S T x ((-γ : ratL T S) : WO S T) = -symplO S T x (γ : WO S T) := by
        intro x
        have h0 := l2 x (γ : WO S T) (-(γ : WO S T))
        rw [add_neg_cancel, GlobalTheory.WeilVacMove.symplOH_zero_right] at h0
        simp only [← l4, AddSubgroup.coe_neg]
        linear_combination (-2 : AF D.host.F) * h0
      have e : (fun x => ψ (symplO S T x γ) * (f x * star (heisO ψ S T u g x))) = fun x =>
          star (ψ (symplOH S T (-(γ : WO S T)) u)) * (f x * star (heisO ψ S T (-(γ : WO S T) + u) g x)) := by
        funext x
        have E := congrFun (hcomp (-(γ : WO S T)) u g) x
        rw [GlobalTheory.ThetaSchur.heisO_rat hu (neg_mem γ.2) x, Pi.smul_apply, smul_eq_mul] at E
        have E' := congrArg star E
        rw [star_mul', star_mul'] at E'
        have hs : star (ψ (-symplO S T x (γ : WO S T))) = ψ (symplO S T x (γ : WO S T)) := by
          have h1 := GlobalTheory.ThetaSchur.mul_star_psi hψ (-symplO S T x (γ : WO S T))
          have h2 : ψ (-symplO S T x (γ : WO S T)) * ψ (symplO S T x (γ : WO S T)) = 1 := by
            rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
          linear_combination ψ (symplO S T x (γ : WO S T)) * h1 - star (ψ (-symplO S T x (γ : WO S T))) * h2
        have hn := hneg x
        simp only [AddSubgroup.coe_neg] at hn
        rw [hn] at E'
        linear_combination (f x) * E' - (f x * star (heisO ψ S T u g x)) * hs
      show ∫ x in v.𝓕, ψ (symplO S T x γ) * (f x * star (heisO ψ S T u g x)) ∂v.μ = 0
      rw [e, integral_const_mul]
      have := horth (-(γ : WO S T) + u)
      unfold thPair at this
      rw [this, mul_zero])
  exact congrFun key x

theorem eq_zero_of_orth_heis : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (v : VolM D T.rank S.rank) (f g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → g ≠ 0 → (∀ u : WO S T, thPair v.μ v.𝓕 f (heisO ψ S T u g) = 0) → f = 0 := by
  intro D ψ hψ S T v f g hf hg hg0 horth
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hg0
  funext x
  have h := prod_eq_zero hψ v hf hg horth (y - x) x
  have hz : ψ (symplOH S T x (y - x)) ≠ 0 := fun h0 => by
    have := hψ.1.2.1 (symplOH S T x (y - x))
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  simp only [heisO, add_sub_cancel, star_mul'] at h
  rcases mul_eq_zero.1 h with h | h
  · exact h
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd (star_eq_zero.1 h) hz
    · exact absurd (star_eq_zero.1 h) hy

end GlobalTheory.ThetaIrred

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorCommutesSuperpositionSlicesSource
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.WeilSuperpos

variable {D : D7}

theorem pair_swap {S A B T : HSp D} (o : OrthDec S A B) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (k : Ω → WO B T) (a : Ω → ℂ) (hk : Measurable k) (ha : Integrable a μ)
    (ν : Measure (WO A T)) [IsFiniteMeasure ν]
    (Φ : WO S T → ℂ) (hΦc : Continuous Φ) (CΦ : ℝ) (hΦ : ∀ x, ‖Φ x‖ ≤ CΦ)
    (g : WO A T → ℂ) (hgc : Continuous g) (Cg : ℝ) (hg : ∀ x, ‖g x‖ ≤ Cg) :
    ∫ u, (∫ w, a w * Φ ((o.resS T).symm (u, k w)) ∂μ) * star (g u) ∂ν =
      ∫ w, a w * ∫ u, Φ ((o.resS T).symm (u, k w)) * star (g u) ∂ν ∂μ := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : BorelSpace (WO A T) := ⟨rfl⟩
  haveI : BorelSpace (WO B T) := ⟨rfl⟩
  haveI : SFinite ν := @instSFiniteOfSigmaFinite _ _ ν (@IsFiniteMeasure.toSigmaFinite _ _ ν _)
  obtain ⟨-, -, hA2, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨-, -, hB2, -⟩ := lattice_Mx D T.rank B.rank
  have hσ : Measurable fun q : WO A T × Ω => Φ ((o.resS T).symm (q.1, k q.2)) :=
    hΦc.measurable.comp ((o.continuous_resS_symm T).measurable.comp
      (measurable_fst.prodMk (hk.comp measurable_snd)))
  have hgm : Measurable fun q : WO A T × Ω => star (g q.1) :=
    (continuous_star.comp hgc).measurable.comp measurable_fst
  have h1 : Integrable (fun q : WO A T × Ω => a q.2) (ν.prod μ) := ha.comp_snd ν
  have hint : Integrable (Function.uncurry fun u w => a w * Φ ((o.resS T).symm (u, k w)) * star (g u))
      (ν.prod μ) := by
    refine (h1.norm.mul_const (CΦ * Cg)).mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
    · exact (h1.aestronglyMeasurable.mul hσ.aestronglyMeasurable).mul hgm.aestronglyMeasurable
    · rcases q with ⟨u, w⟩
      simp only [Function.uncurry_apply_pair, norm_mul, norm_star]
      have hC : 0 ≤ CΦ := (norm_nonneg _).trans (hΦ 0)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hΦ _) (hg _) (norm_nonneg _) hC) (norm_nonneg _)
  calc ∫ u, (∫ w, a w * Φ ((o.resS T).symm (u, k w)) ∂μ) * star (g u) ∂ν
      = ∫ u, ∫ w, a w * Φ ((o.resS T).symm (u, k w)) * star (g u) ∂μ ∂ν := by
        congr 1; funext u; rw [integral_mul_const]
    _ = ∫ w, ∫ u, a w * Φ ((o.resS T).symm (u, k w)) * star (g u) ∂ν ∂μ := integral_integral_swap hint
    _ = ∫ w, a w * ∫ u, Φ ((o.resS T).symm (u, k w)) * star (g u) ∂ν ∂μ := by
        congr 1; funext w; rw [← integral_const_mul]; congr 1; funext u; ring

theorem exists_sfinite {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Ω → ℂ) (ha : Integrable a μ) :
    ∃ s : Set Ω, SigmaFinite (μ.restrict s) ∧ ∀ X : Ω → ℂ, ∫ w, a w * X w ∂μ = ∫ w, a w * X w ∂(μ.restrict s) := by
  have hf := ha.aefinStronglyMeasurable
  refine ⟨hf.sigmaFiniteSet, hf.sigmaFinite_restrict, fun X => ?_⟩
  have hs : MeasurableSet hf.sigmaFiniteSet := hf.measurableSet
  have h0 : ∀ᵐ w ∂μ, w ∉ hf.sigmaFiniteSet → a w = 0 := by
    have := hf.ae_eq_zero_compl
    rw [Filter.EventuallyEq, ae_restrict_iff' hs.compl] at this
    exact this.mono fun w hw hws => hw hws
  exact (setIntegral_eq_integral_of_ae_compl_eq_zero (h0.mono fun w hw hws => by rw [hw hws, zero_mul])).symm

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem comm_sfinite {S A B T : HSp D} (o : OrthDec S A B) {χ χ' : (AE D)ˣ →* Circle} {om : Om A T}
    (hW : IsWeilDatumO ψ A T χ χ' om) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] (k : Ω → WO B T) (a : Ω → ℂ)
    (hk : Measurable k) (ha : Integrable a μ) (p : GA D A × GA D T) (u₀ : WO A T) :
    om p (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) u₀ =
      ∫ w, a w * om p (fun u => F ((o.resS T).symm (u, k w))) u₀ ∂μ := by
  have hψ := hW.std
  set H : WO S T → ℂ := fun x => om p (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1 with hH
  have hHt : IsThetaFunO ψ S T H := (_root_.GlobalTheory.WeilSlice.weilSlice_theta D ψ S A B T o F hF).1 χ χ' om hW p
  have hHs : ∀ u b, H ((o.resS T).symm (u, b)) = om p (fun u' => F ((o.resS T).symm (u', b))) u := by
    intro u b; simp only [hH, AddEquiv.apply_symm_apply]
  have hsl : ∀ b, IsThetaFunO ψ A T (fun u => F ((o.resS T).symm (u, b))) := by
    intro b
    have := _root_.GlobalTheory.SuperposS.superpos_isTheta D ψ hψ S A B T o F hF Unit (Measure.dirac ()) (fun _ => b) (fun _ => 1)
      measurable_const (integrable_const _)
    simpa using this
  set G : WO A T → ℂ := fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ with hGdef
  set R : WO A T → ℂ := fun u => ∫ w, a w * om p (fun u' => F ((o.resS T).symm (u', k w))) u ∂μ with hRdef
  have hG : IsThetaFunO ψ A T G := _root_.GlobalTheory.SuperposS.superpos_isTheta D ψ hψ S A B T o F hF Ω μ k a hk ha
  have hR' : R = fun u => ∫ w, a w * H ((o.resS T).symm (u, k w)) ∂μ := by
    funext u; simp only [hRdef, hHs]
  have hR : IsThetaFunO ψ A T R := by
    rw [hR']; exact _root_.GlobalTheory.SuperposS.superpos_isTheta D ψ hψ S A B T o H hHt Ω μ k a hk ha
  have hL : IsThetaFunO ψ A T (om p G) := hW.om_pres p G hG
  obtain ⟨v⟩ := GlobalTheory.Unf.Inhab.nonempty_volM D T.rank A.rank
  obtain ⟨hhaar, hfd, hvol⟩ := v.covol
  haveI := hhaar
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
  have key : ∀ g, IsThetaFunO ψ A T g → thPair v.μ v.𝓕 (om p G) g = thPair v.μ v.𝓕 R g := by
    intro g hg
    have hg' : IsThetaFunO ψ A T (om p⁻¹ g) := hW.om_pres _ _ hg
    have hinv : om p (om p⁻¹ g) = g := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    obtain ⟨Cg, hCg⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hg
    obtain ⟨Cg', hCg'⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hg'
    obtain ⟨CF, hCF⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hF
    obtain ⟨CH, hCH⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hHt
    calc thPair v.μ v.𝓕 (om p G) g = thPair v.μ v.𝓕 (om p G) (om p (om p⁻¹ g)) := by rw [hinv]
      _ = thPair v.μ v.𝓕 G (om p⁻¹ g) := _root_.GlobalTheory.WeilPairing.thPair_om_eq D ψ A T χ χ' om hW v p _ _ hG hg'
      _ = ∫ w, a w * thPair v.μ v.𝓕 (fun u => F ((o.resS T).symm (u, k w))) (om p⁻¹ g) ∂μ := by
          unfold thPair
          exact pair_swap o μ k a hk ha _ F hF.cont CF hCF _ hg'.cont Cg' hCg'
      _ = ∫ w, a w * thPair v.μ v.𝓕 (om p (fun u => F ((o.resS T).symm (u, k w)))) g ∂μ := by
          congr 1; funext w; congr 1
          rw [← _root_.GlobalTheory.WeilPairing.thPair_om_eq D ψ A T χ χ' om hW v p _ _ (hsl _) hg', hinv]
      _ = ∫ w, a w * thPair v.μ v.𝓕 (fun u => H ((o.resS T).symm (u, k w))) g ∂μ := by
          simp only [hHs]
      _ = thPair v.μ v.𝓕 R g := by
          rw [hR']; unfold thPair
          exact (pair_swap o μ k a hk ha _ H hHt.cont CH hCH g hg.cont Cg hCg).symm
  have hd : IsThetaFunO ψ A T (om p G - R) := GlobalTheory.WeilVacMove.isTheta_sub hL hR
  have hkd := key _ hd
  obtain ⟨CL, hCL⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hL
  obtain ⟨CR, hCR⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hR
  obtain ⟨Cd, hCd⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hd
  haveI : BorelSpace (WO A T) := ⟨rfl⟩
  have bint : ∀ f : WO A T → ℂ, Continuous f → ∀ C : ℝ, (∀ x, ‖f x‖ ≤ C) →
      Integrable (fun x => f x * star ((om p G - R) x)) (v.μ.restrict v.𝓕) := by
    intro f hf C hC
    refine (integrable_const (C * Cd)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hf.mul (continuous_star.comp hd.cont)).aestronglyMeasurable
    · rw [norm_mul, norm_star]
      exact mul_le_mul (hC x) (hCd x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))
  have h0 : ∫ x in v.𝓕, ((Complex.normSq ((om p G - R) x) : ℝ) : ℂ) ∂v.μ = 0 := by
    have e : ∀ x, ((Complex.normSq ((om p G - R) x) : ℝ) : ℂ) =
        om p G x * star ((om p G - R) x) - R x * star ((om p G - R) x) := by
      intro x
      rw [← sub_mul, ← Pi.sub_apply, Complex.star_def, Complex.mul_conj]
    simp only [e]
    rw [integral_sub (bint _ hL.cont CL hCL) (bint _ hR.cont CR hCR)]
    unfold thPair at hkd
    rw [hkd, sub_self]
  rw [integral_complex_ofReal] at h0
  have h1 : ∫ x in v.𝓕, Complex.normSq ((om p G - R) x) ∂v.μ = 0 := by exact_mod_cast h0
  have hnn : 0 ≤ᵐ[v.μ.restrict v.𝓕] fun x => Complex.normSq ((om p G - R) x) :=
    Filter.Eventually.of_forall fun x => Complex.normSq_nonneg _
  have hi : Integrable (fun x => Complex.normSq ((om p G - R) x)) (v.μ.restrict v.𝓕) := by
    refine (integrable_const (Cd * Cd)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (Complex.continuous_normSq.comp hd.cont).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, sq]
      exact mul_le_mul (hCd x) (hCd x) (norm_nonneg _) ((norm_nonneg _).trans (hCd x))
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hi).1 h1
  have hae' : ∀ᵐ x ∂v.μ.restrict v.𝓕, (om p G - R) x = 0 :=
    hae.mono fun x hx => Complex.normSq_eq_zero.1 hx
  obtain ⟨i1, -, i3, -, i5, -⟩ := lattice_Mx D T.rank A.rank
  haveI := i1; haveI := i3; haveI := i5
  have hz := GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratMx D T.rank A.rank) v.μ v.𝓕 hfd (om p G - R) hd.cont
    (GlobalTheory.WeilVacMove.norm_periodic hψ hd) hae'
  have := congrFun hz u₀
  rw [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

theorem weil_comm_superpos : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO B T) (a : Ω → ℂ), Measurable k → Integrable a μ → ∀ p, IsThetaFunO ψ S T (fun x => om p (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1) ∧ ∀ u₀, om p (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) u₀ = ∫ w, a w * om p (fun u => F ((o.resS T).symm (u, k w))) u₀ ∂μ := by
  intro D ψ S A B T o χ χ' om hW F hF Ω _ μ k a hk ha p
  refine ⟨(_root_.GlobalTheory.WeilSlice.weilSlice_theta D ψ S A B T o F hF).1 χ χ' om hW p, fun u₀ => ?_⟩
  obtain ⟨s, hs, hr⟩ := exists_sfinite μ a ha
  have e1 : (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) =
      fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂(μ.restrict s) := funext fun u => hr _
  rw [e1, hr]
  exact comm_sfinite o hW hF (μ.restrict s) k a hk ha.restrict p u₀

end GlobalTheory.WeilSuperpos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariablePreservesSqNormOrthogonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.WeilSliceUnit

open scoped ENNReal NNReal Pointwise

variable {D : D7}

theorem borel_Mx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩

theorem isAddFundamentalDomain_prod {A B : Type*} [AddGroup A] [AddGroup B] [MeasurableSpace A]
    [MeasurableSpace B] {Γ : AddSubgroup A} {Δ : AddSubgroup B} {μ : Measure A} {ν : Measure B} [SFinite μ]
    [SFinite ν] {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) := by
  refine ⟨hs.nullMeasurableSet.prod ht.nullMeasurableSet, ?_, ?_⟩
  · have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae ht.ae_covers
    filter_upwards [h1, h2] with p hp hq
    obtain ⟨g, hg⟩ := hp
    obtain ⟨h, hh⟩ := hq
    exact ⟨⟨((g : A), (h : B)), AddSubgroup.mem_prod.2 ⟨g.2, h.2⟩⟩, hg, hh⟩
  · intro g h hgh
    change μ.prod ν ((g +ᵥ s ×ˢ t) ∩ (h +ᵥ s ×ˢ t)) = 0
    let g1 : Γ := ⟨(g : A × B).1, (AddSubgroup.mem_prod.1 g.2).1⟩
    let h1 : Γ := ⟨(h : A × B).1, (AddSubgroup.mem_prod.1 h.2).1⟩
    let g2 : Δ := ⟨(g : A × B).2, (AddSubgroup.mem_prod.1 g.2).2⟩
    let h2 : Δ := ⟨(h : A × B).2, (AddSubgroup.mem_prod.1 h.2).2⟩
    by_cases e1 : g1 = h1
    · have e2 : g2 ≠ h2 := fun e2 => hgh (Subtype.ext (Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2)))
      have h0 : ν ((g2 +ᵥ t) ∩ (h2 +ᵥ t)) = 0 := ht.aedisjoint e2
      refine measure_mono_null (t := Set.univ ×ˢ ((g2 +ᵥ t) ∩ (h2 +ᵥ t))) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨Set.mem_univ _, ?_, ?_⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.2
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.2
      · rw [Measure.prod_prod, h0, mul_zero]
    · have h0 : μ ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) = 0 := hs.aedisjoint e1
      refine measure_mono_null (t := ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) ×ˢ Set.univ) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.1
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.1
      · rw [Measure.prod_prod, h0, zero_mul]

theorem lintegral_resS {S A B T : HSp D} (o : OrthDec S A B) (μ : Measure (WO S T)) [μ.IsAddHaarMeasure]
    (𝓕 : Set (WO S T)) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (μA : Measure (WO A T)) (μB : Measure (WO B T))
    [μA.IsAddHaarMeasure] [μB.IsAddHaarMeasure] (FA : Set (WO A T)) (FB : Set (WO B T))
    (hA : IsAddFundamentalDomain (ratL T A) FA μA) (hB : IsAddFundamentalDomain (ratL T B) FB μB) :
    ∃ c : ℝ≥0, ∀ Φ : WO A T × WO B T → ℝ≥0∞, (∀ γ ∈ ratL T S, ∀ x, Φ (o.resS T (γ + x)) = Φ (o.resS T x)) →
      ∫⁻ x in 𝓕, Φ (o.resS T x) ∂μ = c • ∫⁻ y, Φ y ∂((μA.restrict FA).prod (μB.restrict FB)) := by
  haveI := borel_Mx (D := D) T.rank S.rank
  haveI := borel_Mx (D := D) T.rank A.rank
  haveI := borel_Mx (D := D) T.rank B.rank
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D T.rank S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D T.rank B.rank
  haveI : Countable (ratL T S) :=
    (TopologicalSpace.separableSpace_iff_countable.1 inferInstance : Countable (ratMx D T.rank S.rank))
  haveI : MeasurableConstVAdd (ratL T S) (WO S T) := ⟨fun _ => (continuous_const.add continuous_id).measurable⟩
  haveI : VAddInvariantMeasure (ratL T S) (WO S T) μ := ⟨fun c s _ => measure_preimage_add μ (c : WO S T) s⟩
  let e : WO S T ≃ₜ (WO A T × WO B T) :=
    { (o.resS T).toEquiv with continuous_toFun := o.continuous_resS T, continuous_invFun := o.continuous_resS_symm T }
  let em := e.toMeasurableEquiv
  haveI : (μ.map em).IsAddHaarMeasure :=
    (o.resS T).isAddHaarMeasure_map μ (o.continuous_resS T) (o.continuous_resS_symm T)
  obtain ⟨c, hmeq⟩ : ∃ c : ℝ≥0, μ.map em = c • μA.prod μB :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map em) (μA.prod μB)⟩
  refine ⟨c, fun Φ hper => ?_⟩
  have hqmp : QuasiMeasurePreserving em μ (μA.prod μB) :=
    ⟨em.measurable.aemeasurable, by rw [hmeq]; exact Measure.smul_absolutelyContinuous⟩
  have hprod := isAddFundamentalDomain_prod hA hB
  have hmem : ∀ g : (ratL T A).prod (ratL T B), (o.resS T).symm (g : WO A T × WO B T) ∈ ratL T S := fun g => by
    rw [o.mem_ratL_resS, AddEquiv.apply_symm_apply]; exact AddSubgroup.mem_prod.1 g.2
  have hP : IsAddFundamentalDomain (ratL T S) (em ⁻¹' (FA ×ˢ FB)) μ := by
    refine hprod.preimage_of_equiv hqmp (e := fun g => ⟨_, hmem g⟩) ⟨fun g g' h => ?_, fun h => ?_⟩ fun g x => ?_
    · exact Subtype.ext ((o.resS T).symm.injective (congrArg Subtype.val h))
    · refine ⟨⟨o.resS T h, AddSubgroup.mem_prod.2 ((o.mem_ratL_resS T h).1 h.2)⟩, Subtype.ext ?_⟩
      exact (o.resS T).symm_apply_apply h
    · change o.resS T ((o.resS T).symm (g : WO A T × WO B T) + x) = (g : WO A T × WO B T) + o.resS T x
      rw [map_add (f := _), AddEquiv.apply_symm_apply]
  rw [h𝓕.setLIntegral_eq hP (fun x => Φ (o.resS T x)) (fun g x => hper g g.2 x)]
  change ∫⁻ x in em ⁻¹' (FA ×ˢ FB), Φ (em x) ∂μ = _
  rw [← lintegral_map_equiv _ em, ← em.restrict_map, hmeq, Measure.restrict_smul, lintegral_smul_measure,
    Measure.prod_restrict]

end GlobalTheory.WeilSliceUnit

namespace GlobalTheory.WeilSliceUnit

open scoped ENNReal NNReal

variable {D : D7}

theorem enorm_sq_periodic {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : ∀ γ ∈ ratL T S, ∀ x, ‖f (γ + x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2 := by
  rintro _ ⟨g, rfl⟩ x
  have h : ‖f (ratW T S g + x)‖ = ‖f x‖ := by rw [hf.quasi, norm_mul, hψ.1.2.1, one_mul]
  show ‖f (ratW T S g + x)‖ₑ ^ 2 = _
  rw [← ofReal_norm, ← ofReal_norm, h]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ p, ∫⁻ x in 𝓕, ‖om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ) ∧ ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om → ∀ p, ∫⁻ x in 𝓕, ‖om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ := by
  intro D ψ S A B T o μ 𝓕 hμ h𝓕 f hf
  haveI := borel_Mx (D := D) T.rank S.rank
  haveI := borel_Mx (D := D) T.rank A.rank
  haveI := borel_Mx (D := D) T.rank B.rank
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D T.rank S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D T.rank B.rank
  obtain ⟨μA, FA, hA⟩ := exists_isCovolOne D T.rank A.rank
  obtain ⟨μB, FB, hB⟩ := exists_isCovolOne D T.rank B.rank
  haveI := hA.1
  haveI := hB.1
  have hFA : IsAddFundamentalDomain (ratL T A) FA μA := hA.2.1
  have hFB : IsAddFundamentalDomain (ratL T B) FB μB := hB.2.1
  obtain ⟨c, hc⟩ := lintegral_resS o μ 𝓕 h𝓕 μA μB FA FB hFA hFB
  have hslice := _root_.GlobalTheory.WeilSlice.weilSlice_theta D ψ S A B T o f hf
  have hΦ0 : Measurable fun y : WO A T × WO B T => ‖f ((o.resS T).symm y)‖ₑ ^ 2 :=
    ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hf.cont.comp (o.continuous_resS_symm T)))).measurable
  have e0 : ∀ hψ : IsStdChar D ψ (-1), ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ = c • ∫⁻ y, ‖f ((o.resS T).symm y)‖ₑ ^ 2
      ∂((μA.restrict FA).prod (μB.restrict FB)) := by
    intro hψ
    have h := hc (fun y => ‖f ((o.resS T).symm y)‖ₑ ^ 2) (fun γ hγ x => by
      simp only [AddEquiv.symm_apply_apply]; exact enorm_sq_periodic hψ hf γ hγ x)
    simpa only [AddEquiv.symm_apply_apply] using h
  refine ⟨fun χ χ' om hW p => ?_, fun χ χ' om hW p => ?_⟩
  · have hψ := hW.std
    have hF := hslice.1 χ χ' om hW p
    have hbox := (_root_.GlobalTheory.BoxSlice.main D ψ hψ S A B T o).2.2.2 f hf
    have hfun : (fun y : WO A T × WO B T => ‖om p (fun u => f ((o.resS T).symm (u, y.2))) y.1‖ₑ ^ 2) =
        fun y => ‖(fun x => om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1)
          ((o.resS T).symm y)‖ₑ ^ 2 := by
      funext y; simp only [AddEquiv.apply_symm_apply]
    have hΦ1 : Measurable fun y : WO A T × WO B T => ‖om p (fun u => f ((o.resS T).symm (u, y.2))) y.1‖ₑ ^ 2 := by
      rw [hfun]
      exact ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hF.cont.comp (o.continuous_resS_symm T)))).measurable
    have e1 := hc (fun y => ‖om p (fun u => f ((o.resS T).symm (u, y.2))) y.1‖ₑ ^ 2)
      (fun γ hγ x => enorm_sq_periodic hψ hF γ hγ x)
    rw [e1, e0 hψ]
    congr 1
    rw [lintegral_prod_symm _ hΦ1.aemeasurable, lintegral_prod_symm _ hΦ0.aemeasurable]
    refine lintegral_congr fun v => ?_
    show ∫⁻ u in FA, ‖om p (fun u => f ((o.resS T).symm (u, v))) u‖ₑ ^ 2 ∂μA =
      ∫⁻ u in FA, ‖f ((o.resS T).symm (u, v))‖ₑ ^ 2 ∂μA
    exact hW.om_unit μA FA hA.1 hFA p (fun u => f ((o.resS T).symm (u, v))) (hbox.1 v)
  · have hψ := hW.std
    have hF := hslice.2 χ χ' om hW p
    have hbox := (_root_.GlobalTheory.BoxSlice.main D ψ hψ S A B T o).2.2.2 f hf
    have hfun : (fun y : WO A T × WO B T => ‖om p (fun v => f ((o.resS T).symm (y.1, v))) y.2‖ₑ ^ 2) =
        fun y => ‖(fun x => om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2)
          ((o.resS T).symm y)‖ₑ ^ 2 := by
      funext y; simp only [AddEquiv.apply_symm_apply]
    have hΦ1 : Measurable fun y : WO A T × WO B T => ‖om p (fun v => f ((o.resS T).symm (y.1, v))) y.2‖ₑ ^ 2 := by
      rw [hfun]
      exact ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hF.cont.comp (o.continuous_resS_symm T)))).measurable
    have e1 := hc (fun y => ‖om p (fun v => f ((o.resS T).symm (y.1, v))) y.2‖ₑ ^ 2)
      (fun γ hγ x => enorm_sq_periodic hψ hF γ hγ x)
    rw [e1, e0 hψ]
    congr 1
    rw [lintegral_prod _ hΦ1.aemeasurable, lintegral_prod _ hΦ0.aemeasurable]
    refine lintegral_congr fun u => ?_
    show ∫⁻ v in FB, ‖om p (fun v => f ((o.resS T).symm (u, v))) v‖ₑ ^ 2 ∂μB =
      ∫⁻ v in FB, ‖f ((o.resS T).symm (u, v))‖ₑ ^ 2 ∂μB
    exact hW.om_unit μB FB hB.1 hFB p (fun v => f ((o.resS T).symm (u, v))) (hbox.2 u)

end GlobalTheory.WeilSliceUnit

end
end

