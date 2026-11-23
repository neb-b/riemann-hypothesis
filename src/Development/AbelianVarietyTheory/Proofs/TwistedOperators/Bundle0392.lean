module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupCongruentOfTwoLatticeMoves
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianConjMonomialMomentEqTaylorCoefficient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HkRelFrOfTransportIff
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfRationalLevelInvariantAgreeChosen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.ExtInv

theorem eq_of_invariant : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (M : ℕ), 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ φ ψ : GA D T → ℂ, (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ γ ∈ GQ T, ∀ g, ψ (γ * g) = ψ g) → (∀ k, C.LevK Lv k 1 → ∀ g, φ (g * k) = φ g) → (∀ k, C.LevK Lv k 1 → ∀ g, ψ (g * k) = ψ g) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = ψ (gL L * a)) → φ = ψ := by
  intro D S T C Lv M hM hM𝔪 gL hgL φ ψ hφ hψ hφk hψk hag
  have hΛ : C.X.Λ.FG ∧ Submodule.span D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ :=
    ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ := by rw [Red.fmt_one]; exact Red.isMov_one _
  obtain ⟨-, hL⟩ := _root_.GlobalTheory.Ker.MovLev.mov_mem_lattices D S T C
  have hI : C.under Lv ≠ ⊥ := (hL Lv 1 _ hΛ.1 hm1).2.2.1
  have hgrp := ((_root_.GlobalTheory.Ker.Grp.rational_points_and_parts D S T C).2.2.2 T).2.1
  have hcomm := ((_root_.GlobalTheory.Ker.Grp.rational_points_and_parts D S T C).2.2.2 T).2.2.2.1
  funext g
  obtain ⟨γ, hγ, a, ha, g', hg', k, hk, hg, ht, -, hck, hcJ⟩ := _root_.GlobalTheory.Ker.CutAt.exists_rat_real_trivAt_cong D T C.X.Λ (C.under Lv) M hΛ hI hM g
  have hinv : fmt T g' * fmt T g'⁻¹ = 1 := by rw [← (hgrp g' g'⁻¹).2.1, mul_inv_cancel, Red.fmt_one]
  obtain ⟨L, hLf, hLm⟩ := ((_root_.GlobalTheory.Ker.isMov_laws D _ C.X.Λ hΛ).2.2.2 _ _ hinv).1
  have hLl : L ∈ Lv.lats := (hL Lv g' L hLf.1 hLm).2.1 ht
  obtain ⟨h1, h2, h3⟩ := hgL L hLl
  have hk1 : C.LevK Lv k 1 := Red.levK_one C Lv k hk hck.1 (hcJ _ hM𝔪)
  have hk2 : C.LevK Lv ((gL L)⁻¹ * g') 1 := _root_.GlobalTheory.Ker.LevMove.levK_of_two_moves D S T C Lv (gL L) g' L h1 hg' h2 ht hLf.1 h3 hLm
  have e : g = γ * (gL L * a * ((gL L)⁻¹ * g') * k) := by
    rw [hg, ← (hcomm a ha).2.2 _ h1]
    group
  rw [e, hφ γ hγ, hψ γ hγ, hφk k hk1, hψk k hk1, hφk _ hk2, hψk _ hk2]
  exact hag L hLl a ha

end GlobalTheory.Ker.ExtInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteUnitarySelfDualFrameToBaseLatticeFra
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SelfDualFrameConj

section SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
open GlobalTheory.StdFrames GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.IdemSupport Formalism.IndefR.Datum Formalism.L2.NTheta GlobalTheory.NormSum.AdLattice Formalism.L2.Herm

variable {D : D7}


set_option maxHeartbeats 800000 in
theorem exists_gfc (V : HSp D) (γ : GL (Fin V.rank) (Ef D)) (hγ : Unimod (OA D) (gramOf V γ)) :
    ∃ k ∈ Formalism.L2.Theta.GfC V, crdLat V V.L0 = lat ((Formalism.IndefR.Lev.finE V k)⁻¹ * γ) := by
  let L : Submodule (𝓞 D.host.E) V.V :=
    (lat γ).comap ((crd V : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E))
  have hL : crdLat V L = lat γ := Submodule.map_comap_eq_of_surjective
    (f := (crd V : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)) (crd V).surjective _
  have hm : ∀ x, x ∈ L ↔ crd V x ∈ lat γ := fun _ => Iff.rfl
  have h1 : Submodule.IsLattice D.host.E L := by
    apply Submodule.IsLattice.of_fg D.host.E
    exact Submodule.fg_of_fg_map_injective
      ((crd V : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)) (crd V).injective
      (hL ▸ (lat_isLattice γ).fg : (crdLat V L).FG)
  have h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L := by
    ext x
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
      Submodule.mem_one]
    rw [hm, mem_lat_iff_dual hγ]
    constructor
    · intro h y hy
      obtain ⟨y, rfl⟩ := (crd V).surjective y
      have := h y hy
      rw [hT_crd D.sp.cm] at this
      exact this
    · intro h y hy
      rw [hT_crd D.sp.cm]
      exact h _ hy
  obtain ⟨k, hkG, hk⟩ := GlobalTheory.VolumeRatioTypings.exists_conj V L h1 h2
  refine ⟨k, hkG, eq_lat (fun x => ?_) (by
    first | exact isLattice_crdLat V V.standardTuple_isLattice | exact isFullLattice_crdLat V)⟩
  have hk' : ∀ y, y ∈ GlobalTheory.AdLat.hat D.host.F (crdLat V V.L0 : Set (Fin V.rank → D.host.E)) ↔
      finMat D.sp.cm.sig V.gram k *ᵥ y ∈ GlobalTheory.AdLat.hat D.host.F (lat γ : Set (Fin V.rank → D.host.E)) := by
    rw [← hL, GlobalTheory.LevelChoices.coe_crdLat]
    have := GlobalTheory.LevelChoices.coe_crdLat (GlobalTheory.VolRatioCompare.reLat V L h1 h2)
    rw [← this] at hk
    exact hk
  refine (hatL_of_hat _ _ _ hk' x).trans ((isFrame_lat γ _).trans ?_)
  rw [mulVec_mulVec, _root_.mul_inv_rev, inv_inv, Units.val_mul]
  rfl

end SlopeTestRemainingChoices

end GlobalTheory.SelfDualFrameConj

theorem GlobalTheory.SelfDualFrameConj.frame_conj : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∃ t ∈ GfC V, IsFrame (finE V t * β) (Formalism.L2.Herm.crdLat V V.L0) := by
  intro D V β Λ N h
  obtain ⟨k, hk, hL⟩ := GlobalTheory.SelfDualFrameConj.exists_gfc V β (GlobalTheory.StdFrames.unimod_of_isSD h)
  refine ⟨k⁻¹, inv_mem hk, ?_⟩
  rw [map_inv, hL]
  exact GlobalTheory.StdFrames.isFrame_lat _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarOfCommuteSchrodingerOperators
section
noncomputable section

open MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace

namespace GlobalTheory.RealWeil

theorem fderiv_gaussianSchwartz_single_add {l : Type} [Fintype l] [DecidableEq l] (j : l) (x : EuclideanSpace ℝ l) :
    fderiv ℝ (⇑(GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))) x (EuclideanSpace.single j 1) +
      2 * Real.pi * (x j : ℂ) * GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) x = 0 := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ l => -Real.pi * ‖y‖ ^ 2)
      (-Real.pi • (2 • (innerSL ℝ) x ∘L ContinuousLinearMap.id ℝ _)) x :=
    ((hasFDerivAt_id x).norm_sq).const_mul (-Real.pi)
  have h2 := (ofRealCLM.hasFDerivAt (x := Real.exp (-Real.pi * ‖x‖ ^ 2))).comp x h1.exp
  have e : ⇑(GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)) =
      (ofRealCLM : ℝ →L[ℝ] ℂ) ∘ fun y : EuclideanSpace ℝ l => Real.exp (-Real.pi * ‖y‖ ^ 2) := by
    funext y; simp
  rw [e, h2.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

theorem inner_toLp_map_of_integral_norm_sq : ∀ (l : Type) [Fintype l] (S : Sch l →ₗ[ℂ] Sch l),
    (∀ f, ∫ x, ‖S f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) →
    ∀ f g, inner ℂ ((S f).toLp 2 volume) ((S g).toLp 2 volume) = inner ℂ (f.toLp 2 volume) (g.toLp 2 volume) := by
  intro l _ S hiso f g
  set U := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l)) with hU
  have hn : ∀ h : Sch l, ‖U (S h)‖ = ‖U h‖ := by
    intro h
    simp only [hU, SchwartzMap.toLpCLM_apply]
    rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num), SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [hiso]
  have e1 : (S f).toLp 2 volume = U (S f) := rfl
  have e2 : (S g).toLp 2 volume = U (S g) := rfl
  have e3 : f.toLp 2 volume = U f := rfl
  have e4 : g.toLp 2 volume = U g := rfl
  rw [e1, e2, e3, e4, inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  simp only [← map_add (f := _), ← map_sub, ← map_smul, hn]

theorem exists_eq_smul_of_commute_rhoFun : ∀ (l : Type) [Fintype l] (S : Sch l →ₗ[ℂ] Sch l),
    (∀ f, ∫ x, ‖S f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) →
    (∀ w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(S f₁) = rhoFun w ⇑(S f)) → ∃ c : ℂ, ∀ f, S f = c • f := by
  intro l _ S hiso hcomm
  classical
  have hl : ∀ g : Sch l, ∫⁻ x, ‖g x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2) := by
    intro g
    rw [ofReal_integral_eq_lintegral_ofReal ((g.memLp (2 : ℕ) volume).integrable_norm_pow (by norm_num))
      (.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hbound : ∀ f, ∫⁻ x, ‖S f x‖ₑ ^ 2 ≤ 1 * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
    intro f
    rw [one_mul, hl, hl, hiso]
  have hd := _root_.GlobalTheory.RealWeil.DRhoTransfer.dRho_intertwine l LinearMap.id S 1 ENNReal.one_ne_top hbound (by simpa using hcomm)
  set G : Sch l := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hG
  have hN : ∀ (j : l) (h : Sch l) x, (dRho (Pi.single (Sum.inl j) 1) h - I • dRho (Pi.single (Sum.inr j) 1) h) x =
      fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x := by
    intro j h x
    rw [SchwartzMap.sub_apply, SchwartzMap.smul_apply, dRho_single_inl, dRho_single_inr,
      SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
    ring_nf
    rw [I_sq]
    ring
  have hSG : ∀ j (x : EuclideanSpace ℝ l), fderiv ℝ (⇑(S G)) x (EuclideanSpace.single j 1) +
      2 * Real.pi * (x j : ℂ) * S G x = 0 := by
    intro j x
    have h0 : dRho (Pi.single (Sum.inl j) 1) G - I • dRho (Pi.single (Sum.inr j) 1) G = 0 := by
      ext y
      rw [hN, hG, fderiv_gaussianSchwartz_single_add]
      rfl
    have := congrArg S h0
    rw [map_sub, map_smul, hd, hd, map_zero] at this
    rw [← hN, LinearMap.id_apply, LinearMap.id_apply] at *
    rw [this]
    rfl
  set c : ℂ := S G 0 with hc
  have hSGc : S G = c • G := by
    ext x
    rw [GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_add_eq_zero' l (S G) hSG x, SchwartzMap.smul_apply, smul_eq_mul, hG, GroundTheory.Global.gaussianSchwartz_apply]
  have hrho : ∀ w, S (rhoSch w G) = c • rhoSch w G := by
    intro w
    ext x
    rw [hcomm w G (rhoSch w G) (coe_rhoSch w G), hSGc, SchwartzMap.smul_apply, coe_rhoSch]
    simp only [rhoFun, SchwartzMap.smul_apply, smul_eq_mul]
    ring
  have key : ∀ f : Sch l, (starRingEnd ℂ c) • S f = f := by
    intro f
    rw [← sub_eq_zero]
    apply _root_.GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian l
    intro w
    have hsm : ∀ (a : ℂ) (g : Sch l), (a • g).toLp 2 volume = a • g.toLp 2 volume := fun a g =>
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_smul a g
    have hsub : ∀ (g g' : Sch l), (g - g').toLp 2 volume = g.toLp 2 volume - g'.toLp 2 volume := fun g g' =>
      (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_sub g g'
    have hp := inner_toLp_map_of_integral_norm_sq l S hiso (rhoSch w G) f
    rw [hrho, hsm, inner_smul_left] at hp
    rw [hsub, hsm, inner_sub_right, inner_smul_right, hp, sub_self]
  have hc0 : starRingEnd ℂ c ≠ 0 := by
    intro h0
    have := congrArg (fun g : Sch l => g 0) (key G)
    simp [h0, hG] at this
  exact ⟨(starRingEnd ℂ c)⁻¹, fun f => by rw [← key f, smul_smul, inv_mul_cancel₀ hc0, one_smul, key]⟩

end GlobalTheory.RealWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockBargmannReproducingFormula
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

namespace GlobalTheory.FockRepr

theorem expand_real (κ : Type) [Fintype κ] (x : κ → ℝ) :
    HasSum (fun m : κ →₀ ℕ => m.prod fun k n => x k ^ n / (n.factorial : ℝ)) (Real.exp (∑ k, x k)) := by
  have h := _root_.GlobalTheory.hasSum_finsupp_prod_pow_div_factorial_exp κ (fun k => (x k : ℂ))
  rw [← Complex.ofReal_sum, ← Complex.ofReal_exp] at h
  refine Complex.hasSum_ofReal.mp ?_
  convert h using 1
  funext m
  simp [Finsupp.prod]

theorem conjMono_continuous {ι : Type} [Fintype ι] {a b : ℕ} (m : DVar ι a b →₀ ℕ) : Continuous (conjMono m) := by
  unfold conjMono Finsupp.prod; fun_prop

theorem gq_continuous {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) : Continuous (gq (a := a) (b := b) c) := by
  unfold gq; fun_prop

theorem bargmann_repr : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ G : VCx ι a b → ℂ, Differentiable ℂ G → (∃ M : ℝ, ∀ z, ‖G z‖ ≤ M * Real.exp (gq c z / 2)) → ∀ z₀, G z₀ = ((∏ τ, (c τ / Real.pi) ^ (a * b) : ℝ) : ℂ) * ∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z := by
  intro ι _ a b c hc G hG ⟨M, hM⟩ z₀
  have hbk : ∀ z, bk c z₀ z = ∑ k : DVar ι a b, (c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2) := by
    intro z; simp only [bk, Fintype.sum_prod_type]
  let coef : (DVar ι a b →₀ ℕ) → ℂ := fun m => m.prod fun k n => ((c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2) ^ n / (n.factorial : ℂ)
  have hcm : ∀ (m : DVar ι a b →₀ ℕ) z, coef m * conjMono m z = m.prod fun k n => ((c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2)) ^ n / (n.factorial : ℂ) := by
    intro m z
    simp only [coef, conjMono, ← Finsupp.prod_mul]
    refine Finset.prod_congr rfl fun k _ => ?_
    ring
  let F : (DVar ι a b →₀ ℕ) → VCx ι a b → ℂ := fun m z => coef m * (conjMono m z * (Real.exp (-gq c z) : ℂ) * G z)
  have hlim : ∀ z, HasSum (fun m => F m z) (Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z) := by
    intro z
    have := (_root_.GlobalTheory.hasSum_finsupp_prod_pow_div_factorial_exp (DVar ι a b) (fun k => (c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2))).mul_right ((Real.exp (-gq c z) : ℂ) * G z)
    rw [← hbk] at this
    have e : (fun m => F m z) = fun m => (m.prod fun k n => ((c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2)) ^ n / (n.factorial : ℂ)) * ((Real.exp (-gq c z) : ℂ) * G z) := by
      funext m
      rw [← hcm]
      simp only [F]
      ring
    rw [e, mul_assoc]
    exact this
  have hnorm : ∀ m z, ‖F m z‖ = (m.prod fun k n => (‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) ^ n / (n.factorial : ℝ)) * (Real.exp (-gq c z) * ‖G z‖) := by
    intro m z
    have e1 : F m z = (coef m * conjMono m z) * ((Real.exp (-gq c z) : ℂ) * G z) := by simp only [F]; ring
    rw [e1, hcm, norm_mul, norm_mul, Finsupp.prod, Finsupp.prod, norm_prod, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_div, norm_pow, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
  have hnsum : ∀ z, HasSum (fun m => ‖F m z‖) (Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * ‖G z‖)) := by
    intro z
    simp only [hnorm]
    exact (expand_real (DVar ι a b) _).mul_right _
  have hGc : Continuous G := hG.continuous
  have hFc : ∀ m, Continuous (F m) := by
    intro m
    have h1 := conjMono_continuous m
    have h2 := gq_continuous (a := a) (b := b) c
    simp only [F]
    fun_prop
  have hS : Continuous fun z : VCx ι a b => ∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖ := by
    fun_prop
  have hint : Integrable (fun z => ∑' m, ‖F m z‖) := by
    have e : (fun z => ∑' m, ‖F m z‖) = fun z => Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * ‖G z‖) := by
      funext z; exact (hnsum z).tsum_eq
    rw [e]
    refine ((GlobalTheory.T.integrable_gaussian_exp_linear_norm_term_complex_matrix ι a b c hc z₀).const_mul M).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have h2 := gq_continuous (a := a) (b := b) c
      exact Continuous.aestronglyMeasurable (by fun_prop)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hz := hM z
      calc Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * ‖G z‖)
          ≤ Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * (M * Real.exp (gq c z / 2))) := by
            gcongr
        _ = M * Real.exp ((∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2) := by
            rw [show (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2
              = (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) + (-gq c z) + gq c z / 2 by ring,
              Real.exp_add, Real.exp_add]
            ring
  have hsumI : HasSum (fun m => ∫ z, F m z) (∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z) :=
    hasSum_integral_of_dominated_convergence (fun m z => ‖F m z‖) (fun m => (hFc m).aestronglyMeasurable)
      (fun m => Filter.Eventually.of_forall fun z => le_rfl) (Filter.Eventually.of_forall fun z => (hnsum z).summable)
      hint (Filter.Eventually.of_forall hlim)
  set P : ℝ := ∏ τ, (Real.pi / c τ) ^ (a * b) with hP
  have hFm : ∀ m, ∫ z, F m z = (P : ℂ) * ((m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ)) * derivAt0 G m) := by
    intro m
    simp only [F]
    rw [MeasureTheory.integral_const_mul, _root_.GlobalTheory.FockMoment.gaussMoment ι a b c hc G hG ⟨M, hM⟩ m]
    have hc' : coef m * (((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ)) : ℂ) = m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ) := by
      simp only [coef, Finsupp.prod, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have : (c k.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hc k.1).ne'
      push_cast
      rw [mul_pow, mul_div_assoc, mul_comm, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ this, one_pow, one_mul]
    rw [← hc']
    ring
  have hT := (_root_.GlobalTheory.FockTaylor.hasSum_derivAt0 ι a b G hG z₀).mul_left (P : ℂ)
  simp only [← hFm] at hT
  have heq := hsumI.unique hT
  rw [heq, ← mul_assoc]
  have h1 : (∏ τ, (c τ / Real.pi) ^ (a * b) : ℝ) * P = 1 := by
    rw [hP, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [← mul_pow]
    have : c τ ≠ 0 := (hc τ).ne'
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    rw [show c τ / Real.pi * (Real.pi / c τ) = 1 by field_simp, one_pow]
  rw [← Complex.ofReal_mul, h1, Complex.ofReal_one, one_mul]

end GlobalTheory.FockRepr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelValueSumWeightTriangularFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeckeWeight
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeckePointLaw (scaleAt tanMap tanMap_scale scaleAt_comm isCombAt_iff tanMap_left)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem comp_listProd {X Y : Over Xo.X} (f : X ⟶ Y) (L : List (Y ⟶ Xo.univ.t.G)) :
    f ≫ L.prod = (L.map (f ≫ ·)).prod := by
  induction L with
  | nil => simp [MonObj.comp_one]
  | cons b L ih => simp [List.prod_cons, MonObj.comp_mul, ih]

theorem isLieImg_comb {Ω : Type} [Field Ω] {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'} (h : IsLinHom ψ) (p : ℕ)
    {m : ℕ} {v v' : Fin m → (Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left)} (hv : ∀ k, IsLieImg p ψ (v k) (v' k))
    {cf : Fin m → Ω} {w w' : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left} (hw : IsCombAt x v cf w)
    (hw' : IsCombAt x' v' cf w') (ht : IsTanAt x w) (ht' : IsTanAt x' w') : IsLieImg p ψ w w' := by
  choose a ha hpa using fun k => (hv k).2.2
  let b : Fin m → (tEps x' ⟶ Xo.univ.t.G) := fun k => Over.homMk (v' k) (hv k).2.1.1
  have hb : ∀ k, tanMap h (a k) = scaleAt x' p ≫ b k := fun k => Over.OverMorphism.ext (by
    rw [tanMap_left, Over.comp_left, ← hpa k]; rfl)
  let W : tEps x ⟶ Xo.univ.t.G := Over.homMk w ht.1
  let W' : tEps x' ⟶ Xo.univ.t.G := Over.homMk w' ht'.1
  have eW : (List.ofFn fun k => scaleAt x (cf k) ≫ a k).prod = W := by
    rw [← isCombAt_iff]
    have : v = fun k => (a k).left := funext fun k => (ha k).symm
    subst this
    exact hw
  have eW' : (List.ofFn fun k => scaleAt x' (cf k) ≫ b k).prod = W' := (isCombAt_iff b cf W').1 hw'
  refine ⟨ht, ht', W, rfl, ?_⟩
  have key : scaleAt x' p ≫ W' = tanMap h W := by
    rw [← eW, ← eW', comp_listProd, map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 2
    funext k
    simp only [Function.comp_apply]
    rw [tanMap_scale, hb, ← Category.assoc, ← Category.assoc, scaleAt_comm]
  have := congrArg (·.left) key
  simp only [Over.comp_left, tanMap_left] at this
  exact this


open GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection (TotalAt FunAt) in
theorem hkVal_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), admitted l P p → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.TotalAt Xo c P p i → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.FunAt Xo c P p i → ∀ f ∈ sec Xo c a n, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (y y' : FrPt Xo c Ω), FrBor t y y' → hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y' = wchar (ex Dw a n) t * hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z) f y := by
  intro E _ _ _ H Dw l Xo c P p i a n hA hT hF f hf Ω _ _ _ t y y' hB
  have hS : GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.IsSplitOff l P p := hA
  obtain ⟨g, hgt, hgd, hch⟩ := (frBor_iff_frChg y y' t).1 hB
  have hdet : ∀ τ, IsUnit (g τ).det := fun τ => by
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hgt τ i j hij)]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun j _ => by rw [hgd]; exact Units.ne_zero _)
  obtain ⟨x', xo', u', tan', eig', bas', s', gen'⟩ := y'
  obtain rfl : x' = y.x := hch.1
  have hw0 : wchar (ex Dw a n) t ≠ (0 : Ω) := by
    unfold wchar
    exact Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (t j).ne_zero
  have key : ∀ C : hkKer (Xo := Xo) P p i Ω y,
      hkTerm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
        (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z)
        f (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C =
      wchar (ex Dw a n) t * hkTerm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
        (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z)
        f y C := by
    intro C
    have ex' := hT Ω (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C
    have ex := hT Ω y C
    unfold hkTerm
    rw [dite_eq_left ex', dite_eq_left ex]
    have hz' := ex'.choose_spec
    have hz := ex.choose_spec
    generalize ex'.choose = z' at hz' ⊢
    generalize ex.choose = z at hz ⊢
    obtain ⟨ψ, hψ, hL, hθ⟩ := (GlobalTheory.HeckeFrCompare.hkPt_iff hS _ y C.1 z).1 hz
    rw [hkTr, Equiv.apply_symm_apply] at hθ
    obtain ⟨z'', hz'', -⟩ := existsUnique_frChg E H Dw l Xo c Ω z g (t none) hdet
    have hB' : FrBor t z z'' := (frBor_iff_frChg _ _ t).2 ⟨g, hgt, hgd, hz''⟩
    obtain ⟨x'', xo'', u'', tan'', eig'', bas'', s'', gen''⟩ := z''
    obtain rfl : x'' = z.x := hz''.1
    have hP : hkRelFr P p i (hkTr Xo c p) Ω (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C
        ⟨z.x, xo'', u'', tan'', eig'', bas'', s'', gen''⟩ := by
      show HkPt p (hkTr Xo c p Ω) (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C.1
        ⟨z.x, xo'', u'', tan'', eig'', bas'', s'', gen''⟩
      refine (GlobalTheory.HeckeFrCompare.hkPt_iff hS (hkTr Xo c p Ω) (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C.1
        ⟨z.x, xo'', u'', tan'', eig'', bas'', s'', gen''⟩).2 ⟨ψ, hψ, fun τ j => ?_, ?_⟩
      · exact GlobalTheory.HeckeWeight.isLieImg_comb hψ.2.1 p (hL τ) (hch.2.1 τ j) (hz''.2.1 τ j) (tan' τ j) (tan'' τ j)
      · rw [hkTr, Equiv.apply_symm_apply]
        exact hθ.smul (toΓ Ω (t none : Ω)) ((ChgOf.secBC_id_iff _ _ _ _).1 hch.2.2)
          ((ChgOf.secBC_id_iff _ _ _ _).1 hz''.2.2)
    obtain rfl := (frMap_unique_refl_iff E H Dw l Xo c Ω Ω (AlgHom.id c.F Ω) z').1 _ _
      (frMap_unique_refl_iff E H Dw l Xo c Ω Ω (AlgHom.id c.F Ω) z').2.1 (hF Ω (⟨y.x, xo', u', tan', eig', bas', s', gen'⟩ : FrPt Xo c Ω) C z' _ hz' hP)
    exact (algebraic_laws lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 Ω inferInstance a n f hf t z _ hB'
  unfold hkVal
  refine (finsum_congr key).trans ?_
  exact (mul_finsum _ _).symm

end GlobalTheory.HeckeWeight
end
end

