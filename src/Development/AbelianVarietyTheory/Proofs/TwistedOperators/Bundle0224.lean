module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0007
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignCompatibleNumberingOfWittTowerLower
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumHeckeEigenvalueGeneratingSeriesGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsotropicDualFrameOfSplitEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistDual

variable {D : D7}

theorem adj_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = Aᴴ := by
  funext i j
  rfl

theorem hT_coord (V : HSp D) (x y : V.V) :
    V.hT x y = ∑ i, ∑ j, star (V.frame.repr x i) * V.gram i j * V.frame.repr y j := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, HSpace.gram]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RingHom.id_apply, starRingEnd_apply, mul_comm]

theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have : V.frame.equivFun.symm v = 0 := by
    apply V.nondeg.2
    intro x
    rw [hT_coord]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : ∑ j, V.gram i j * v j = 0 := congr_fun h0 i
    have h2 : ∀ j, V.frame.repr (V.frame.equivFun.symm v) j = v j := fun j =>
      congr_fun (V.frame.equivFun.apply_symm_apply v) j
    simp only [h2, mul_assoc, ← Finset.mul_sum, h1, mul_zero]
  exact V.frame.equivFun.symm.map_eq_zero_iff.1 this

theorem gram_ct (V : HSp D) : V.gramᴴ = V.gram := by
  funext i j
  exact V.herm.eq (V.frame j) (V.frame i)

theorem exists_isotropic_dual : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B →
    ∃ C' : Matrix (Fin V.rank) (Fin r) D.host.E,
      adj D C * V.gram * C' = 1 ∧ adj D C' * V.gram * C' = 0 ∧ adj D C' * V.gram * B = 0 := by
  intro D V V' r C B hs
  simp only [adj_eq]
  have hCC : Cᴴ * V.gram * C = 0 := by rw [← adj_eq]; exact hs.frame.2.2
  have hBB : (Bᴴ * V.gram * B).det ≠ 0 := by rw [← adj_eq, hs.isom]; exact gram_det_ne V'
  have hCB : Cᴴ * V.gram * B = 0 := by rw [← adj_eq]; exact hs.orth
  exact exists_dual (gram_ct V) (gram_det_ne V) hs.frame.2.1 hCC hBB hCB

end GlobalTheory.TwistDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowerWittTowerIsotropicSplitEmbedding
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerSplit

theorem signCard_of_isEnum {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε) (b : Bool) :
    GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard S b = (Finset.univ.filter fun a => ε a = b).card := by
  obtain ⟨hl, q, hq, rfl⟩ := h
  have hinj : Function.Injective q := fun a c hac => hl.injective (by rw [hq, hq, hac])
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard
  rw [Finset.filter_image, Finset.card_image_of_injective]
  intro a c hac
  exact hinj (Prod.ext_iff.1 hac).1

theorem hasSignature_of_model {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    Formalism.UG.HasSignature (gramAt D V τ) (GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard (S τ) true)
      (GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard (S τ) false) := by
  rw [signCard_of_isEnum (M.enum τ), signCard_of_isEnum (M.enum τ)]
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  refine GlobalTheory.AutInhab.hasSignature_of_frame (P := (M.fr τ)⁻¹) ?_ ?_
  · exact IsUnit.of_mul_eq_one _ (Matrix.nonsing_inv_mul _ hd)
  · rw [← M.fr_gram τ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, h1, conjTranspose_one,
      Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem exists_isoSplit : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (_M : DSModel V S) (r : ℕ)
    (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∃ (V' : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B ∧
      GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered S r V' := by
  intro D V S M r C hC
  obtain ⟨e, rfl⟩ := GlobalTheory.BesselCompare.eMat_surj V C
  have he : LinearIndependent D.host.E e :=
    LinearIndependent.of_comp V.frame.equivFun.toLinearMap hC.2.1
  have hiso : ∀ a b, V.hT (e a) (e b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hC.2.2]; rfl
  obtain ⟨V', ι, h1, h2, h3⟩ := GlobalTheory.WittLow.exists_lower Examples₂.star_isIntegral V e he hiso
  have hlow : IsWittLower V V' r := by
    refine ⟨h1, ι, h2, _, ⟨hC.2.1, hC.2.2⟩, ?_⟩
    refine Matrix.ext fun a b => ?_
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]
    exact h3 _ _
  refine ⟨V', frameMat V V' ι, ⟨hC, ?_, ?_, by omega⟩, fun τ => ?_⟩
  · refine Matrix.ext fun a b => ?_
    unfold adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]
    exact h2 _ _
  · refine Matrix.ext fun a b => ?_
    unfold adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul, ← V.herm.eq, h3]
    simp
  · obtain ⟨s, hs⟩ := GlobalTheory.WittLow.exists_sig V' (tauE D τ)
    have hs' : Formalism.UG.HasSignature (gramAt D V' τ) s.1 s.2 := hs
    obtain ⟨e1, e2⟩ := Formalism.UG.P.signature_unique _ _ _ _ _ _ (GlobalTheory.WittSign.hasSignature_of_isWittLower hlow τ hs')
      (hasSignature_of_model M τ)
    exact ⟨s.1, s.2, e1, e2, hs'⟩

end GlobalTheory.TowerSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroAtZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilDetermined

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_om_inv (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p (om p⁻¹ f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem om_inv_om (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p⁻¹ (om p f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_scalar (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') (p : GA D S × GA D T) :
    ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → om p f = (c : ℂ) • om' p f := by
  obtain ⟨c, hc, h⟩ := GlobalTheory.ThetaSchur.schur D ψ H.std S T (om' p⁻¹ * om p)
    (fun f hf => H'.om_pres _ _ (H.om_pres _ _ hf))
    (fun w f hf => by
      obtain ⟨g, h⟩ := p
      have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ w
      rw [inv_inv, inv_inv] at e
      rw [Module.End.mul_apply, Module.End.mul_apply, H.om_heis g h w f hf, Prod.inv_mk,
        H'.om_heis _ _ _ _ (H.om_pres _ _ hf), e])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, H'.om_unit μ 𝓕 hμ h𝓕 _ _ (H.om_pres _ _ hf), H.om_unit μ 𝓕 hμ h𝓕 _ _ hf])
  refine ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, fun f hf => ?_⟩
  have := congrArg (om' p) (h f hf)
  rwa [Module.End.mul_apply, om_om_inv, map_smul] at this

theorem exists_ne_zero_at_zero (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : f ≠ 0) :
    ∃ f₀, IsThetaFunO ψ S T f₀ ∧ f₀ 0 ≠ 0 := by
  obtain ⟨w, hw⟩ := Function.ne_iff.1 h0
  refine ⟨heisO ψ S T w f, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w, ?_⟩
  unfold heisO
  rw [zero_add]
  refine mul_ne_zero ?_ hw
  exact (ψ.val_isUnit _).ne_zero

theorem exists_isDetAt {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) (e * cA D (Formalism.L2.Theta.mt V g).det + (1 - e)) (by
    linear_combination (e * e) * det_conj_mul V g +
      (2 - (Formalism.L2.Theta.mt V g).det - cA D (Formalism.L2.Theta.mt V g).det) * he), Units.val_mkOfMulEqOne _⟩

theorem suppAt_one (e : AE D) (V : HSp D) : SuppAt e V 1 := by
  intro i j
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

theorem scalar_split (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') {e : AE D}
    (he : IsSplitIdem D e) {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {c : Circle}
    (hc : ∀ f, IsThetaFunO ψ S T f → om (g, h) f = (c : ℂ) • om' (g, h) f) : c = 1 := by
  obtain ⟨x, hx⟩ := exists_isDetAt he.1 S g
  obtain ⟨y, hy⟩ := exists_isDetAt he.1 T h
  obtain ⟨r, hr, h1⟩ := H.om_split e he g h hg hh x y hx hy
  obtain ⟨r', hr', h2⟩ := H'.om_split e he g h hg hh x y hx hy
  obtain ⟨ℓ, hℓ, f, hf, hne⟩ := GlobalTheory.HalfCoinv.exists_invariant_form D ψ H.std S T e he
  have e1 := h1 ℓ hℓ f hf
  rw [hc f hf, map_smul, h2 ℓ hℓ f hf, smul_eq_mul] at e1
  have e2 : (c : ℂ) * r' = r := by
    apply mul_right_cancel₀ (mul_ne_zero (Circle.coe_ne_zero (splitFacO χS χT x y)) hne)
    linear_combination e1
  have e3 : r' = r := by
    have := congrArg norm e2
    rwa [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr.le,
      Real.norm_of_nonneg hr'.le] at this
  subst e3
  apply Circle.ext
  apply mul_right_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne')
  rw [e2, Circle.coe_one, one_mul]

theorem agree_on_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om om' : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f := by
  intro D ψ hψ S T χS χT om om' H H' p f hf
  by_cases h0 : f = 0
  · rw [h0, map_zero, map_zero]
  obtain ⟨f₀, hf₀, h00⟩ := exists_ne_zero_at_zero hψ hf h0
  have hne : ∀ q, om' q f₀ ≠ 0 := fun q hq => by
    have := om_inv_om om' q f₀
    rw [hq, map_zero] at this
    exact h00 (by rw [← this]; rfl)
  choose c hc using exists_scalar H H'
  have hmul : ∀ q q', c (q * q') = c q * c q' := fun q q' => by
    apply Circle.ext
    apply smul_left_injective ℂ (hne (q * q'))
    have := hc (q * q') f₀ hf₀
    dsimp only
    rw [← this, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hc q' f₀ hf₀, map_smul,
      hc q _ (H'.om_pres _ _ hf₀), smul_smul, Circle.coe_mul, mul_comm]
  have hcont : Continuous c := by
    refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun q => ?_)
    obtain ⟨w, hw⟩ := Function.ne_iff.1 (hne q)
    have h1 : ContinuousAt (fun q' => om q' f₀ w / om' q' f₀ w) q :=
      (H.om_cont f₀ hf₀ w).continuousAt.div (H'.om_cont f₀ hf₀ w).continuousAt hw
    refine h1.congr ?_
    filter_upwards [(H'.om_cont f₀ hf₀ w).continuousAt.eventually_ne hw] with q' hq'
    rw [hc q' f₀ hf₀, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hq']
    rfl
  have hrat : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, c (γ, γ') = 1 := fun γ hγ γ' hγ' => by
    have h1 := congrFun (hc (γ, γ') f₀ hf₀) 0
    rw [Pi.smul_apply, H.om_aut γ hγ γ' hγ' f₀ hf₀, H'.om_aut γ hγ γ' hγ' f₀ hf₀, smul_eq_mul] at h1
    apply Circle.ext
    apply mul_right_cancel₀ h00
    rw [← h1, Circle.coe_one, one_mul]
  let ν : GA D S × GA D T →* Circle := MonoidHom.mk' c hmul
  have hS := GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D S (ν.comp (MonoidHom.inl _ _)) (hcont.comp (Continuous.prodMk_left _))
    (fun γ hγ => hrat γ hγ 1 (one_mem _))
    (fun e he g hg => scalar_split H H' he hg (suppAt_one e T) (hc (g, 1)))
  have hT := GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D T (ν.comp (MonoidHom.inr _ _)) (hcont.comp (Continuous.prodMk_right _))
    (fun γ hγ => hrat 1 (one_mem _) γ hγ)
    (fun e he h hh => scalar_split H H' he (suppAt_one e S) hh (hc (1, h)))
  have h1 : c p = 1 := by
    have e : p = (p.1, 1) * (1, p.2) := by rw [Prod.mk_mul_mk, mul_one, one_mul]
    rw [e, hmul, show c (p.1, 1) = 1 from hS p.1, show c (1, p.2) = 1 from hT p.2, mul_one]
  rw [hc p f hf, h1, Circle.coe_one, one_smul]

theorem hecke_of_mul {χ ξ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (h : IsHeckeChar D (χ * ξ)) :
    IsHeckeChar D ξ := by
  have := GlobalTheory.WeilChange.hecke_mul (GlobalTheory.WeilChange.hecke_inv hχ) h
  rwa [inv_mul_cancel_left] at this

theorem exists_isTildeDet (V : HSp D) {ξ : (AE D)ˣ →* Circle} (hξ : IsHeckeChar D ξ)
    (h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.TrivOnF D ξ) (g : GA D V) :
    ∃ x, IsDetRoot V g x ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.IsTildeDet V ξ g (ξ x) := by
  obtain ⟨a, aval, -⟩ := GlobalTheory.Member.exists_muVal D V ξ hξ h0
  obtain ⟨x, hx⟩ := aval.1 g
  refine ⟨x, hx, ⟨x, hx⟩, fun y hy => Circle.ext ?_⟩
  rw [← aval.2 g x hx, ← aval.2 g y hy]

theorem weilDatumTwist (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.WeilDatumTwist D := by
  intro ψ S T χS χT ξ ξ' om om' h0 h0' H H' g h
  have hξ := hecke_of_mul H.hecS H'.hecS
  have hξ' := hecke_of_mul H.hecT H'.hecT
  obtain ⟨om'', H'', hv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ H.std S T χS χT ξ ξ' om H hξ hξ'
    ⟨H.resS.1, fun η _ a => by rw [h0 a, pow_zero]⟩ ⟨H.resS.1, fun η _ a => by rw [h0' a, pow_zero]⟩
  obtain ⟨x, hx, ha⟩ := exists_isTildeDet S hξ' h0' g
  obtain ⟨y, hy, hb⟩ := exists_isTildeDet T hξ h0 h
  refine ⟨ξ' x, ξ y, ha, hb, fun f hf => ?_⟩
  rw [agree_on_theta D ψ H.std S T _ _ om' om'' H' H'' (g, h) f hf, hv g h x y hx hy, LinearMap.smul_apply]

theorem weilDatumDetermined (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.WeilDatumDetermined D :=
  ⟨(weilDatumTwist D).unique, weilDatumTwist D⟩

end GlobalTheory.WeilDetermined
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalLeviScalingIsotropicFrame
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LeviScale

section Alg

variable {E : Type} [Field E] [CharZero E] (σ : E →+* E)

theorem cT_fromCols {ι α β : Type} (X : Matrix ι α E) (Y : Matrix ι β E) :
    Formalism.UG.cT σ (fromCols X Y) = fromRows (Formalism.UG.cT σ X) (Formalism.UG.cT σ Y) := by
  ext (i | i) j <;> rfl

theorem cT_diagonal {ι : Type} [DecidableEq ι] (d : ι → E) (hd : ∀ i, σ (d i) = d i) :
    Formalism.UG.cT σ (diagonal d) = diagonal d := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Formalism.UG.cT, hd]
  · simp [Formalism.UG.cT, diagonal_apply_ne _ h, diagonal_apply_ne _ (Ne.symm h)]

theorem levi_alg (hσ : ∀ x, σ (σ x) = x) {n m r : ℕ} (hn : n = m + 2 * r)
    (G : Matrix (Fin n) (Fin n) E) (G' Gi : Matrix (Fin m) (Fin m) E) (hGi : Gi * G' = 1)
    (hG : Formalism.UG.cT σ G = G)
    (C C' : Matrix (Fin n) (Fin r) E) (B : Matrix (Fin n) (Fin m) E)
    (h11 : Formalism.UG.cT σ C * G * C = 0) (h12 : Formalism.UG.cT σ C * G * B = 0)
    (h22 : Formalism.UG.cT σ B * G * B = G')
    (h13 : Formalism.UG.cT σ C * G * C' = 1) (h33 : Formalism.UG.cT σ C' * G * C' = 0)
    (h32 : Formalism.UG.cT σ C' * G * B = 0) :
    ∃ A A' : Matrix (Fin n) (Fin n) E, A * A' = 1 ∧ A' * A = 1 ∧ Formalism.UG.cT σ A * G * A = G ∧
      A * C = (2 : E) • C ∧ A * B = B ∧ (2 : E) • (A * C') = C' := by
  have hcc : ∀ {a : ℕ} (X : Matrix (Fin n) (Fin a) E), Formalism.UG.cT σ (Formalism.UG.cT σ X) = X := by
    intro a X; ext i j; simp [Formalism.UG.cT, hσ]
  have swap : ∀ {a b : ℕ} (X : Matrix (Fin n) (Fin a) E) (Y : Matrix (Fin n) (Fin b) E),
      Formalism.UG.cT σ (Formalism.UG.cT σ X * G * Y) = Formalism.UG.cT σ Y * G * X := by
    intro a b X Y
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hG, hcc, Matrix.mul_assoc]
  have cT0 : ∀ {a b : ℕ}, Formalism.UG.cT σ (0 : Matrix (Fin a) (Fin b) E) = 0 := by
    intro a b; ext i j; simp [Formalism.UG.cT]
  have h21 : Formalism.UG.cT σ B * G * C = 0 := by rw [← swap C B, h12, cT0]
  have h23 : Formalism.UG.cT σ B * G * C' = 0 := by rw [← swap C' B, h32, cT0]
  have h31 : Formalism.UG.cT σ C' * G * C = 1 := by rw [← swap C C', h13, Formalism.UG.cT_one]
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin r ⊕ (Fin m ⊕ Fin r)) E, P = fromCols C (fromCols B C') := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin r ⊕ (Fin m ⊕ Fin r)) (Fin n) E,
      Q = fromRows (Formalism.UG.cT σ C' * G) (fromRows (Gi * Formalism.UG.cT σ B * G) (Formalism.UG.cT σ C * G)) := ⟨_, rfl⟩
  have as3 : ∀ {a : ℕ} (X : Matrix (Fin n) (Fin a) E), Gi * Formalism.UG.cT σ B * G * X = Gi * (Formalism.UG.cT σ B * G * X) := by
    intro a X; simp only [Matrix.mul_assoc]
  have hQC : Q * C = fromRows 1 (fromRows 0 0) := by
    rw [hQ, fromRows_mul, fromRows_mul, h31, h11, as3, h21, Matrix.mul_zero]
  have hQB : Q * B = fromRows 0 (fromRows 1 0) := by
    rw [hQ, fromRows_mul, fromRows_mul, h32, h12, as3, h22, hGi]
  have hQC' : Q * C' = fromRows 0 (fromRows 0 1) := by
    rw [hQ, fromRows_mul, fromRows_mul, h33, h13, as3, h23, Matrix.mul_zero]
  have hQP : Q * P = 1 := by
    rw [hP, mul_fromCols, mul_fromCols, hQC, hQB, hQC']
    ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply]
  have hPQ : P * Q = 1 := by
    have e : (Fin r ⊕ (Fin m ⊕ Fin r)) ≃ Fin n := Fintype.equivOfCardEq (by simp; omega)
    exact (Matrix.mul_eq_one_comm_of_equiv e).1 hQP
  obtain ⟨d, hd⟩ : ∃ d : Fin r ⊕ (Fin m ⊕ Fin r) → E,
      d = Sum.elim (fun _ => 2) (Sum.elim (fun _ => 1) (fun _ => 2⁻¹)) := ⟨_, rfl⟩
  obtain ⟨d', hd'⟩ : ∃ d' : Fin r ⊕ (Fin m ⊕ Fin r) → E,
      d' = Sum.elim (fun _ => 2⁻¹) (Sum.elim (fun _ => 1) (fun _ => 2)) := ⟨_, rfl⟩
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  have hdd : (fun i => d i * d' i) = fun _ => 1 := by
    funext i; rcases i with i | i | i <;> simp [hd, hd', h2]
  have hdd' : (fun i => d' i * d i) = fun _ => 1 := by
    funext i; rcases i with i | i | i <;> simp [hd, hd', h2]
  have hσd : ∀ i, σ (d i) = d i := by
    intro i; rcases i with i | i | i <;> simp [hd, map_inv₀, map_ofNat]
  have hK : Formalism.UG.cT σ P * G * P = fromCols (fromRows 0 (fromRows 0 1))
      (fromCols (fromRows 0 (fromRows G' 0)) (fromRows 1 (fromRows 0 0))) := by
    rw [hP, cT_fromCols, cT_fromCols]
    simp only [fromRows_mul, mul_fromCols]
    rw [h11, h12, h13, h21, h22, h23, h31, h32, h33]
  have hDKD : diagonal d * (Formalism.UG.cT σ P * G * P) * diagonal d = Formalism.UG.cT σ P * G * P := by
    rw [hK]
    ext (i | i | i) (j | j | j) <;> simp [diagonal_mul, mul_diagonal, hd] <;> ring
  refine ⟨P * diagonal d * Q, P * diagonal d' * Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc P * diagonal d * Q * (P * diagonal d' * Q) = P * (diagonal d * (Q * P) * diagonal d') * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, diagonal_mul_diagonal, hdd, diagonal_one, Matrix.mul_one, hPQ]
  · calc P * diagonal d' * Q * (P * diagonal d * Q) = P * (diagonal d' * (Q * P) * diagonal d) * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, diagonal_mul_diagonal, hdd', diagonal_one, Matrix.mul_one, hPQ]
  · have hA : Formalism.UG.cT σ (P * diagonal d * Q) = Formalism.UG.cT σ Q * diagonal d * Formalism.UG.cT σ P := by
      rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_diagonal σ d hσd, Matrix.mul_assoc]
    calc Formalism.UG.cT σ (P * diagonal d * Q) * G * (P * diagonal d * Q)
        = Formalism.UG.cT σ Q * (diagonal d * (Formalism.UG.cT σ P * G * P) * diagonal d) * Q := by
          rw [hA]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σ (P * Q) * G * (P * Q) := by
          rw [hDKD, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hPQ, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  · have h : diagonal d * (Q * C) = (2 : E) • (Q * C) := by
      rw [hQC]; ext (i | i | i) j <;> simp [diagonal_mul, hd]
    calc P * diagonal d * Q * C = P * (diagonal d * (Q * C)) := by simp only [Matrix.mul_assoc]
      _ = (2 : E) • (P * Q * C) := by rw [h, Matrix.mul_smul, Matrix.mul_assoc]
      _ = (2 : E) • C := by rw [hPQ, Matrix.one_mul]
  · have h : diagonal d * (Q * B) = Q * B := by
      rw [hQB]; ext (i | i | i) j <;> simp [diagonal_mul, hd]
    calc P * diagonal d * Q * B = P * (diagonal d * (Q * B)) := by simp only [Matrix.mul_assoc]
      _ = P * Q * B := by rw [h, Matrix.mul_assoc]
      _ = B := by rw [hPQ, Matrix.one_mul]
  · have h : diagonal d * (Q * C') = (2 : E)⁻¹ • (Q * C') := by
      rw [hQC']; ext (i | i | i) j <;> simp [diagonal_mul, hd]
    calc (2 : E) • (P * diagonal d * Q * C') = (2 : E) • (P * (diagonal d * (Q * C'))) := by
          simp only [Matrix.mul_assoc]
      _ = ((2 : E) * (2 : E)⁻¹) • (P * Q * C') := by rw [h, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = C' := by rw [hPQ, Matrix.one_mul, mul_inv_cancel₀ h2, one_smul]

end Alg

theorem exists_levi_scale : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∃ a : GA D V, a ∈ GQ V ∧ HMul.hMul (matHom V a).1 (C.map (incA D)) = (2 : AE D) • C.map (incA D) ∧ HMul.hMul (matHom V a).1 (B.map (incA D)) = B.map (incA D) ∧ (2 : AE D) • HMul.hMul (matHom V a).1 (C'.map (incA D)) = C'.map (incA D) := by
  intro D V V' r C C' B hs h1 h2 h3
  obtain ⟨A, A', hAA', hA'A, hU, hC, hB, hC'⟩ :=
    levi_alg (D.sp.cm.sig : D.host.E →+* D.host.E) (fun x => star_star x) hs.rank V.gram V'.gram V'.gram⁻¹
      (Matrix.nonsing_inv_mul _ (GlobalTheory.AutFunCounterexample.gram_det_ne V').isUnit) (GlobalTheory.AutFunCounterexample.gram_herm V)
      C C' B hs.frame.2.2 hs.orth hs.isom h1 h2 h3
  let g : GL (Fin V.rank) D.host.E := ⟨A, A', hAA', hA'A⟩
  have hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := hU
  have hmem : Formalism.UG.bc (incA D) g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (A.map (incA D)) * V.gram.map (incA D) * A.map (incA D) =
      V.gram.map (incA D)
    rw [GlobalTheory.AutFunCounterexample.cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul, hU]
  have hsm : ∀ {k : ℕ} (X : Matrix (Fin V.rank) (Fin k) D.host.E),
      ((2 : D.host.E) • X).map (incA D) = (2 : AE D) • X.map (incA D) := by
    intro k X; ext i j; simp [Matrix.map_apply, Matrix.smul_apply, map_ofNat]
  refine ⟨⟨Formalism.UG.bc (incA D) g, hmem⟩, ?_, ?_, ?_, ?_⟩
  · show (⟨Formalism.UG.bc (incA D) g, hmem⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram) ∈
      (HFin (AF D.host.F) D.sp.cm.sig V.gram).subgroupOf (HR (AF D.host.F) D.sp.cm.sig V.gram)
    rw [Subgroup.mem_subgroupOf]
    exact ⟨g, hg, rfl⟩
  · change HMul.hMul (A.map (incA D)) (C.map (incA D)) = _
    rw [← Matrix.map_mul, hC, hsm]
  · change HMul.hMul (A.map (incA D)) (B.map (incA D)) = _
    rw [← Matrix.map_mul, hB]
  · change (2 : AE D) • HMul.hMul (A.map (incA D)) (C'.map (incA D)) = _
    rw [← Matrix.map_mul, ← hsm, hC']

end GlobalTheory.LeviScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumHeckeEigenvalueGeneratingSeriesGLStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_heckeEigenvalue_generatingSeries_GL : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → ∀ ϖ, IsUnifV E w ϖ → ∀ t : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (t d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∀ c : (Fin r → ℤ) → ℂ, (∀ d, heckeVec ρ (KGL w (n := r)) (dosetInd ℂ (KGL w (n := r)) (t d)) x = c d • x) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => c d.1 * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac B ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B.map (·⁻¹)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  first | exact @GlobalTheory.FinZeta.GLSeries.hasSum_hecke_eigenvalues | exact GlobalTheory.FinZeta.GLSeries.hasSum_hecke_eigenvalues | (intros; apply GlobalTheory.FinZeta.GLSeries.hasSum_hecke_eigenvalues <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IncASmulMemAdelicCompletionMatrixGroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.incA_smul_mem_adelicCompletionMatrixGroup : ∀ (D : D7) (S T : HSp D) (Λ : Lt D.host.E S.rank) (L1 L2 : Lt D.host.E T.rank) (c : D.host.E), (∀ v ∈ L1, c • v ∈ L2) → ∀ u ∈ hatA S T (tens Λ L1), incA D c • u ∈ hatA S T (tens Λ L2) := by
  first | exact @GlobalTheory.HatScalar.incA_smul_mem_hatA | exact GlobalTheory.HatScalar.incA_smul_mem_hatA | (intros; apply GlobalTheory.HatScalar.incA_smul_mem_hatA <;> assumption)
end

