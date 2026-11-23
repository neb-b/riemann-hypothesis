module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorTargetSummandPreservesThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer
section
noncomputable section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabAtPlace

variable {D : D7} {θ : InfFam D} {T T₀ : HSp D} {r : ℕ}

theorem mx_ext (hθ : IsInfFam θ) {m n : ℕ} {A B : Mx D m n} (hf : A.map (finPart D) = B.map (finPart D))
    (hi : ∀ τ, compAt θ τ A = compAt θ τ B) : A = B := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  ext i j
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · rw [RingHom.map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun hf i) j)
  · rw [RingHom.map_sub, RingHom.map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (hi τ) i) j)

theorem comp_mul (τ : D.what₂.Tau) {m n k : ℕ} (A : Mx D m n) (B : Mx D n k) :
    compAt θ τ (A ⬝ B) = compAt θ τ A * compAt θ τ B :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem absE_single (hθ : IsInfFam θ) (x : (AE D)ˣ) (τ : D.what₂.Tau) (hf : finPart D (x : AE D) = 1)
    (hi : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) :
    absE D.host.F D.host.E x = ‖θ τ (infPart D (x : AE D))‖₊ ^ 2 := by
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).1
  haveI := hcm.1
  have e1 : (∏ᶠ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v x)) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by rw [GlobalTheory.HalfModTorus.unitFin_eq_one v _ hf, map_one]
  have hw : ∀ τ : D.what₂.Tau, absEw D.host.F D.host.E
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
      (unitInf D.host.F D.host.E _ x) = ‖θ τ (infPart D (x : AE D))‖₊ ^ 2 := by
    intro τ
    let t' : GlobalTheory.AdelicU.EmbOver D.host.E (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) :=
      ⟨tauE D τ, (InfinitePlace.embedding_mk_eq_of_isReal
        (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))).symm⟩
    rw [absEw_eq_sq hcm t', GlobalTheory.AutFunCompare.isInfEmb_unique _ _ _ (hθ τ) (GlobalTheory.AdelicU.isInfEmb_infProj t')]
    exact congrArg (fun z : ℂ => ‖z‖₊ ^ 2) (GlobalTheory.HalfModTorus.compInf_eq _ t' _)
  have e2 : (∏ w, absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x)) = ‖θ τ (infPart D (x : AE D))‖₊ ^ 2 := by
    rw [← (GlobalTheory.CMTypePlaces.places_bijective D).prod_comp
      (fun w => absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x))]
    simp only [hw]
    refine Finset.prod_eq_single τ (fun τ' _ c => ?_) fun c => absurd (Finset.mem_univ _) c
    rw [hi τ' c, nnnorm_one, one_pow]
  rw [absE_apply, e1, e2, mul_one]

end GlobalTheory.StabAtPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumRestrictionRankZero
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.ChainOnto
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.RankZeroVac

variable {D : D7}

theorem incA_tmul' (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

section
variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (T : HSp D)

theorem continuous_wittExtendByZero : Continuous (d.ext0 T) := continuous_id.matrix_mul continuous_const

theorem heisenbergOperator_wittExtendByZero (ψ : AddChar (AF D.host.F) ℂ) (u : WO W₀ T) (f : WO W T → ℂ) :
    heisO ψ W₀ T u (fun w => f (d.ext0 T w)) = fun w => heisO ψ W T (d.ext0 T u) f (d.ext0 T w) := by
  funext w
  simp only [heisO, map_add (f := _), d.wittDecomp_sympl_extAnisotropic_extAnisotropic]

theorem isThetaFunction_comp_wittExtendByZero {ψ : AddChar (AF D.host.F) ℂ} {f : WO W T → ℂ} (hf : IsThetaFunO ψ W T f) :
    IsThetaFunO ψ W₀ T (fun w => f (d.ext0 T w)) := {
  quasi γ w := by
    have h := hf.quasi (γ * d.q0) (d.ext0 T w)
    have hr : ratW T W (γ * d.q0) = d.ext0 T (ratW T W₀ γ) := by
      rw [ratW_eq, ratW_eq, rat_mul, d.matrixExtendByZero_apply]; rfl
    rw [hr, d.wittDecomp_sympl_extAnisotropic_extAnisotropic] at h
    simp only [map_add (f := _)]
    exact h
  level := by
    obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (d.ext0 T), hU.preimage (continuous_wittExtendByZero d T), fun u hu hinf => ?_⟩
    rw [heisenbergOperator_wittExtendByZero]
    have h0 : (d.ext0 T u).map (infPart D) = 0 := by
      rw [d.matrixExtendByZero_apply, Matrix.map_mul, hinf, Matrix.zero_mul]
    rw [hfix _ hu h0]
  cont := hf.cont.comp (continuous_wittExtendByZero d T)
  smooth k L hL hLf w := by
    have h := hf.smooth k ((d.ext0 T).comp L) ((continuous_wittExtendByZero d T).comp hL) (fun t => by
      show (d.ext0 T (L t)).map (finPart D) = 0
      rw [d.matrixExtendByZero_apply, Matrix.map_mul, hLf t, Matrix.zero_mul]) (d.ext0 T w)
    simpa only [AddMonoidHom.comp_apply, map_add (f := _)] using h }

theorem isHalf_wittHyperbolicExtendByZero_apply {e : AE D} {u : WO W₀ T} (h : IsHalf e u) : IsHalf e (d.ext0 T u) := by
  intro i j
  have hl : ∀ l, e * ((u : Matrix (Fin T.rank) (Fin W₀.rank) (AE D)) i l * d.p0 l j) =
      (u : Matrix (Fin T.rank) (Fin W₀.rank) (AE D)) i l * d.p0 l j := fun l => by rw [← mul_assoc, h i l]
  rw [d.matrixExtendByZero_apply, Matrix.mul_apply]
  show e * ∑ l, _ = _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => hl l

end

end GlobalTheory.RankZeroVac

namespace GlobalTheory.RankZeroVac

variable {D : D7}

section
variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (T : HSp D)

theorem wittDecomposition_gram_projection_identity (s : Fin W₀.rank → D.host.E) (j : Fin W.rank) :
    ∑ l, (∑ k, star (s k) * W₀.gram k l) * d.q0 l j = ∑ m, star ((Matrix.mulVec d.i₀ s) m) * W.gram m j := by
  have h : Matrix.vecMul (Matrix.vecMul (star s) W₀.gram) d.q0 = Matrix.vecMul (star (Matrix.mulVec d.i₀ s)) W.gram := by
    rw [Matrix.vecMul_vecMul, HypDec.q0, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det W₀),
      Matrix.one_mul, ← Matrix.vecMul_vecMul, Matrix.star_mulVec]
  have hj := congrFun h j
  simpa only [Matrix.vecMul, dotProduct, Pi.star_apply] using hj

end

end GlobalTheory.RankZeroVac

namespace GlobalTheory.RankZeroVac

variable {D : D7}

section
variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (T : HSp D)

end

end GlobalTheory.RankZeroVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepCommutesSliceSuperpositionTarget
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.SliceSumTarget

theorem decomp_re_im (z : ℂ) : ((max z.re 0 : ℝ) : ℂ) + -1 * ((max (-z.re) 0 : ℝ) : ℂ) + Complex.I * ((max z.im 0 : ℝ) : ℂ) +
    -Complex.I * ((max (-z.im) 0 : ℝ) : ℂ) = z := by
  have h1 := max_zero_sub_max_neg_zero_eq_self z.re
  have h2 := max_zero_sub_max_neg_zero_eq_self z.im
  apply Complex.ext
  · simp
    linarith
  · simp
    linarith

theorem isThetaFunO_sliceT {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {T A B S : HSp D}
    (o : OrthDec T A B) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F) (y : WO S B) :
    IsThetaFunO ψ S A fun u => F ((o.resT S).symm (u, y)) := by
  have h := _root_.GlobalTheory.SuperposT.superpos_target D ψ hψ T A B S o F hF Unit (Measure.dirac ()) (fun _ => y) (fun _ => 1) measurable_const
    (integrable_const _)
  simpa only [integral_dirac, one_mul] using h

theorem weil_comm_sliceSum_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T A B S : HSp D) (o : OrthDec T A B) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S A), IsWeilDatumO ψ S A χ χ' om → ∀ (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO S B) (a : Ω → ℂ), Measurable k → Integrable a μ → ∀ p, IsThetaFunO ψ S T (fun x => om p (fun u => F ((o.resT S).symm (u, (o.resT S x).2))) (o.resT S x).1) ∧ ∀ u₀, om p (fun u => ∫ w, a w * F ((o.resT S).symm (u, k w)) ∂μ) u₀ = ∫ w, a w * om p (fun u => F ((o.resT S).symm (u, k w))) u₀ ∂μ := by
  intro D ψ T A B S o χ χ' om hW F hF Ω _ μ k a hk ha p
  have hψ := hW.std
  have h1 := _root_.GlobalTheory.SliceTarget.main D ψ T A B S o F hF χ χ' om hW p
  refine ⟨h1, fun u₀ => ?_⟩
  obtain ⟨-, -, iB3, -⟩ := lattice_Mx D B.rank S.rank
  haveI : BorelSpace (WO S B) := ⟨rfl⟩

  set Fs : WO S B → WO S A → ℂ := fun y u => F ((o.resT S).symm (u, y)) with hFs
  set G : WO S T → ℂ := fun x => om p (fun u => F ((o.resT S).symm (u, (o.resT S x).2))) (o.resT S x).1 with hG
  have hGs : ∀ y u, om p (Fs y) u = G ((o.resT S).symm (u, y)) := by
    intro y u; simp only [hG, hFs, AddEquiv.apply_symm_apply]
  have cFs : Continuous fun q : WO S B × WO S A => Fs q.1 q.2 :=
    hF.cont.comp ((o.continuous_resT_symm S).comp (continuous_snd.prodMk continuous_fst))
  have cGs : Continuous fun q : WO S B × WO S A => om p (Fs q.1) q.2 := by
    simp only [hGs]
    exact h1.cont.comp ((o.continuous_resT_symm S).comp (continuous_snd.prodMk continuous_fst))
  obtain ⟨CF, hCF⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF
  obtain ⟨CG, hCG⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ G h1
  have bFs : ∀ y u, ‖Fs y u‖ ≤ CF := fun y u => hCF _
  have bGs : ∀ y u, ‖om p (Fs y) u‖ ≤ CG := fun y u => by rw [hGs]; exact hCG _

  have mF : ∀ u, AEStronglyMeasurable (fun w => Fs (k w) u) μ := fun u =>
    ((cFs.comp (continuous_id.prodMk continuous_const)).measurable.comp hk).aestronglyMeasurable
  have mG : AEStronglyMeasurable (fun w => om p (Fs (k w)) u₀) μ :=
    ((cGs.comp (continuous_id.prodMk continuous_const)).measurable.comp hk).aestronglyMeasurable

  let P : (Ω → ℂ) → Prop := fun c => Integrable c μ ∧
    om p (fun u => ∫ w, c w * Fs (k w) u ∂μ) u₀ = ∫ w, c w * om p (Fs (k w)) u₀ ∂μ
  have intF : ∀ c, Integrable c μ → ∀ u, Integrable (fun w => c w * Fs (k w) u) μ := fun c hc u => by
    have := hc.bdd_mul (mF u) (c := CF) (Filter.Eventually.of_forall fun w => bFs _ _)
    simpa only [mul_comm] using this
  have intG : ∀ c, Integrable c μ → Integrable (fun w => c w * om p (Fs (k w)) u₀) μ := fun c hc => by
    have := hc.bdd_mul mG (c := CG) (Filter.Eventually.of_forall fun w => bGs _ _)
    simpa only [mul_comm] using this
  have Padd : ∀ c₁ c₂, P c₁ → P c₂ → P (c₁ + c₂) := by
    intro c₁ c₂ h₁ h₂
    refine ⟨h₁.1.add h₂.1, ?_⟩
    have e1 : (fun u => ∫ w, (c₁ + c₂) w * Fs (k w) u ∂μ) =
        (fun u => ∫ w, c₁ w * Fs (k w) u ∂μ) + (fun u => ∫ w, c₂ w * Fs (k w) u ∂μ) := by
      funext u
      simp only [Pi.add_apply, add_mul]
      exact integral_add (intF _ h₁.1 u) (intF _ h₂.1 u)
    rw [e1, map_add (f := _), Pi.add_apply, h₁.2, h₂.2]
    simp only [Pi.add_apply, add_mul]
    exact (integral_add (intG _ h₁.1) (intG _ h₂.1)).symm
  have Psmul : ∀ (z : ℂ) c, P c → P (fun w => z * c w) := by
    intro z c h
    refine ⟨h.1.const_mul z, ?_⟩
    have e1 : (fun u => ∫ w, (z * c w) * Fs (k w) u ∂μ) = z • (fun u => ∫ w, c w * Fs (k w) u ∂μ) := by
      funext u
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul z _
    rw [e1, map_smul, Pi.smul_apply, smul_eq_mul, h.2]
    simp only [mul_assoc]
    exact (integral_const_mul z _).symm

  have Ppos : ∀ b : Ω → ℝ, Measurable b → (∀ w, 0 ≤ b w) → Integrable b μ → P (fun w => (b w : ℂ)) := by
    intro b hbm hb0 hbi
    refine ⟨hbi.ofReal, ?_⟩
    let ν : Measure (WO S B) := (μ.withDensity fun w => ((Real.toNNReal (b w) : NNReal) : ENNReal)).map k
    haveI : IsFiniteMeasure (μ.withDensity fun w => ((Real.toNNReal (b w) : NNReal) : ENNReal)) :=
      isFiniteMeasure_withDensity_ofReal hbi.2
    have tr : ∀ φ : WO S B → ℂ, Continuous φ → ∫ y, φ y ∂ν = ∫ w, (b w : ℂ) * φ (k w) ∂μ := by
      intro φ hφ
      rw [integral_map hk.aemeasurable hφ.aestronglyMeasurable,
        integral_withDensity_eq_integral_smul (hbm.real_toNNReal) _]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only [NNReal.smul_def, Real.coe_toNNReal _ (hb0 w), Complex.real_smul]
    have hth : IsThetaFunO ψ S A fun u => ∫ y, Fs y u ∂ν := by
      have e : (fun u => ∫ y, Fs y u ∂ν) = fun u => ∫ w, (b w : ℂ) * F ((o.resT S).symm (u, k w)) ∂μ := by
        funext u
        exact tr (fun y => Fs y u) (cFs.comp (continuous_id.prodMk continuous_const))
      rw [e]
      exact _root_.GlobalTheory.SuperposT.superpos_target D ψ hψ T A B S o F hF Ω μ k _ hk hbi.ofReal
    have hc := _root_.GlobalTheory.CommIntBdd.om_integral_comm_bdd D ψ S A χ χ' om hW (WO S B) ν Fs p (isThetaFunO_sliceT hψ o hF) cFs ⟨CF, bFs⟩ cGs
      ⟨CG, bGs⟩ hth u₀
    have e : (fun u => ∫ y, Fs y u ∂ν) = fun u => ∫ w, (b w : ℂ) * Fs (k w) u ∂μ := by
      funext u
      exact tr (fun y => Fs y u) (cFs.comp (continuous_id.prodMk continuous_const))
    rw [e] at hc
    rw [hc]
    exact tr (fun y => om p (Fs y) u₀) (cGs.comp (continuous_id.prodMk continuous_const))

  set a' := ha.1.mk a with ha'
  have hae : a =ᵐ[μ] a' := ha.1.ae_eq_mk
  have ha'm : Measurable a' := ha.1.stronglyMeasurable_mk.measurable
  have ha'i : Integrable a' μ := ha.congr hae
  have hre := ha'i.re
  have him := ha'i.im
  have mre : Measurable fun w => (a' w).re := Complex.measurable_re.comp ha'm
  have mim : Measurable fun w => (a' w).im := Complex.measurable_im.comp ha'm
  have P1 := Ppos _ (mre.max measurable_const) (fun w => le_max_right _ _) hre.pos_part
  have P2 := Psmul (-1) _ (Ppos _ (mre.neg.max measurable_const) (fun w => le_max_right _ _) hre.neg_part)
  have P3 := Psmul Complex.I _ (Ppos _ (mim.max measurable_const) (fun w => le_max_right _ _) him.pos_part)
  have P4 := Psmul (-Complex.I) _ (Ppos _ (mim.neg.max measurable_const) (fun w => le_max_right _ _) him.neg_part)
  have Pa' := Padd _ _ (Padd _ _ (Padd _ _ P1 P2) P3) P4
  have Pa'' : P a' := by
    have heq : (fun w => (((max (a' w).re 0 : ℝ) : ℂ) +
        -1 * ((max (-(a' w).re) 0 : ℝ) : ℂ) +
        Complex.I * ((max (a' w).im 0 : ℝ) : ℂ)) +
        -Complex.I * ((max (-(a' w).im) 0 : ℝ) : ℂ)) = a' := by
      funext w
      exact decomp_re_im (a' w)
    change P (fun w => (((max (a' w).re 0 : ℝ) : ℂ) +
        -1 * ((max (-(a' w).re) 0 : ℝ) : ℂ) +
        Complex.I * ((max (a' w).im 0 : ℝ) : ℂ)) +
        -Complex.I * ((max (-(a' w).im) 0 : ℝ) : ℂ)) at Pa'
    rwa [heq] at Pa'
  have e1 : (fun u => ∫ w, a w * Fs (k w) u ∂μ) = fun u => ∫ w, a' w * Fs (k w) u ∂μ := by
    funext u; exact integral_congr_ae (hae.mono fun w hw => by simp only [hw])
  have e2 : ∫ w, a w * om p (Fs (k w)) u₀ ∂μ = ∫ w, a' w * om p (Fs (k w)) u₀ ∂μ :=
    integral_congr_ae (hae.mono fun w hw => by simp only [hw])
  have := Pa''.2
  simp only [hFs] at this e1 e2 ⊢
  rw [e1, e2]
  exact this

end GlobalTheory.SliceSumTarget
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepOrthogonalSumEqUnitSmulProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.WeilSumScalar
variable {D : D7} {S A B T : HSp D} (o : OrthDec S A B)

def opA (M : Module.End ℂ (WO A T → ℂ)) : Module.End ℂ (WO S T → ℂ) where
  toFun f x := M (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1
  map_add' f g := by funext x; show M (_ + _) _ = _; rw [map_add (f := _)]; rfl
  map_smul' c f := by funext x; show M (c • _) _ = _; rw [map_smul]; rfl

def opB (M : Module.End ℂ (WO B T → ℂ)) : Module.End ℂ (WO S T → ℂ) where
  toFun f x := M (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2
  map_add' f g := by funext x; show M (_ + _) _ = _; rw [map_add (f := _)]; rfl
  map_smul' c f := by funext x; show M (c • _) _ = _; rw [map_smul]; rfl

theorem opA_apply (M : Module.End ℂ (WO A T → ℂ)) (f : WO S T → ℂ) (x : WO S T) :
    opA o M f x = M (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1 := rfl

theorem opB_apply (M : Module.End ℂ (WO B T → ℂ)) (f : WO S T → ℂ) (x : WO S T) :
    opB o M f x = M (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2 := rfl

theorem heisO_sum (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (f : WO S T → ℂ) (u : WO A T) (v : WO B T) :
    heisO ψ S T w f ((o.resS T).symm (u, v)) =
      ψ (symplOH A T u (o.resS T w).1) * ψ (symplOH B T v (o.resS T w).2) *
        f ((o.resS T).symm (u + (o.resS T w).1, v + (o.resS T w).2)) := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddChar.map_add_eq_mul]
  congr 2
  rw [← Prod.mk_add_mk, map_add (f := _), AddEquiv.symm_apply_apply]

theorem opB_heisO {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : (AE D)ˣ →* Circle} {om : Om B T}
    (hom : IsWeilDatumO ψ B T χ χ' om) (b : GA D B) (h : GA D T) (w : WO S T) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    opB o (om (b, h)) (heisO ψ S T w f) =
      heisO ψ S T ((o.resS T).symm ((o.resS T w).1, actO B T b h (o.resS T w).2)) (opB o (om (b, h)) f) := by
  funext x
  obtain ⟨⟨u, v⟩, rfl⟩ := (o.resS T).symm.surjective x
  have hg := ((_root_.GlobalTheory.BoxSlice.main D ψ hom.std S A B T o).2.2.2 f hf).2 (u + (o.resS T w).1)
  have e : (fun v' => heisO ψ S T w f ((o.resS T).symm (u, v'))) =
      ψ (symplOH A T u (o.resS T w).1) •
        heisO ψ B T (o.resS T w).2 (fun v' => f ((o.resS T).symm (u + (o.resS T w).1, v'))) := by
    funext v'
    rw [heisO_sum, Pi.smul_apply, smul_eq_mul, heisO]
    ring
  rw [heisO_sum, opB_apply, opB_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  simp only [AddEquiv.apply_symm_apply]
  rw [e, map_smul, hom.om_heis b h _ _ hg, Pi.smul_apply, smul_eq_mul, heisO]
  ring

theorem opA_heisO {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : (AE D)ˣ →* Circle} {om : Om A T}
    (hom : IsWeilDatumO ψ A T χ χ' om) (a : GA D A) (h : GA D T) (w : WO S T) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    opA o (om (a, h)) (heisO ψ S T w f) =
      heisO ψ S T ((o.resS T).symm (actO A T a h (o.resS T w).1, (o.resS T w).2)) (opA o (om (a, h)) f) := by
  funext x
  obtain ⟨⟨u, v⟩, rfl⟩ := (o.resS T).symm.surjective x
  have hg := ((_root_.GlobalTheory.BoxSlice.main D ψ hom.std S A B T o).2.2.2 f hf).1 (v + (o.resS T w).2)
  have e : (fun u' => heisO ψ S T w f ((o.resS T).symm (u', v))) =
      ψ (symplOH B T v (o.resS T w).2) •
        heisO ψ A T (o.resS T w).1 (fun u' => f ((o.resS T).symm (u', v + (o.resS T w).2))) := by
    funext u'
    rw [heisO_sum, Pi.smul_apply, smul_eq_mul, heisO]
    ring
  rw [heisO_sum, opA_apply, opA_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  simp only [AddEquiv.apply_symm_apply]
  rw [e, map_smul, hom.om_heis a h _ _ hg, Pi.smul_apply, smul_eq_mul, heisO]
  ring

def opAB (omA : Om A T) (omB : Om B T) (a : GA D A) (b : GA D B) (h : GA D T) : Module.End ℂ (WO S T → ℂ) :=
  opA o (omA (a, h)) * opB o (omB (b, h))

end GlobalTheory.WeilSumScalar


open GlobalTheory.WeilSumScalar in
theorem GlobalTheory.WeilSumScalar.omS_eq_smul_prod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (χA χB χT : (AE D)ˣ →* Circle) (omS : Om S T) (omA : Om A T) (omB : Om B T), IsWeilDatumO ψ S T (χA * χB) χT omS → IsWeilDatumO ψ A T χA χT omA → IsWeilDatumO ψ B T χB χT omB → ∀ a b h, ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → ∀ u v, omS (o.emb (a, b), h) f ((o.resS T).symm (u, v)) = (c : ℂ) * omA (a, h) (fun u' => omB (b, h) (fun v' => f ((o.resS T).symm (u', v'))) v) u := by
  intro D ψ S A B T o χA χB χT omS omA omB hS hA hB a b h
  set N := opAB o omA omB a b h with hN
  set p : GA D S × GA D T := (o.emb (a, b), h) with hp
  have hNapp : ∀ f, N f = opA o (omA (a, h)) (opB o (omB (b, h)) f) := fun f => rfl

  have hNpres : ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (N f) := by
    intro f hf
    have h1 : IsThetaFunO ψ S T (opB o (omB (b, h)) f) := (_root_.GlobalTheory.WeilSlice.weilSlice_theta D ψ S A B T o f hf).2 _ _ _ hB (b, h)
    rw [hNapp]
    exact (_root_.GlobalTheory.WeilSlice.weilSlice_theta D ψ S A B T o _ h1).1 _ _ _ hA (a, h)

  have hNheis : ∀ w f, IsThetaFunO ψ S T f → N (heisO ψ S T w f) = heisO ψ S T (actO S T (o.emb (a, b)) h w) (N f) := by
    intro w f hf
    have h1 : IsThetaFunO ψ S T (opB o (omB (b, h)) f) := (_root_.GlobalTheory.WeilSlice.weilSlice_theta D ψ S A B T o f hf).2 _ _ _ hB (b, h)
    rw [hNapp, hNapp, opB_heisO o hB b h w hf, opA_heisO o hA a h _ h1]
    congr 1
    rw [AddEquiv.apply_symm_apply, ← o.resS_actO T a b h w, AddEquiv.symm_apply_apply]

  have hNunit : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖N f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ := by
    intro μ 𝓕 hμ h𝓕 f hf
    have h1 : IsThetaFunO ψ S T (opB o (omB (b, h)) f) := (_root_.GlobalTheory.WeilSlice.weilSlice_theta D ψ S A B T o f hf).2 _ _ _ hB (b, h)
    rw [hNapp]
    exact ((_root_.GlobalTheory.WeilSliceUnit.main D ψ S A B T o μ 𝓕 hμ h𝓕 _ h1).1 _ _ _ hA (a, h)).trans
      ((_root_.GlobalTheory.WeilSliceUnit.main D ψ S A B T o μ 𝓕 hμ h𝓕 f hf).2 _ _ _ hB (b, h))

  have hinv : ∀ g, omS p (omS p⁻¹ g) = g := by
    intro g
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨c, hc, hM⟩ := GlobalTheory.ThetaSchur.schur D ψ hS.std S T (omS p⁻¹ * N)
    (fun f hf => hS.om_pres _ _ (hNpres f hf))
    (fun w f hf => by
      have hpi : p⁻¹ = ((o.emb (a, b))⁻¹, h⁻¹) := rfl
      have hw := GlobalTheory.AdelicLatMove.actO_actO_inv S T (o.emb (a, b))⁻¹ h⁻¹ w
      rw [inv_inv, inv_inv] at hw
      rw [Module.End.mul_apply, Module.End.mul_apply, hNheis w f hf, hpi,
        hS.om_heis _ _ _ _ (hNpres f hf), hw])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, hS.om_unit μ 𝓕 hμ h𝓕 _ _ (hNpres f hf), hNunit μ 𝓕 hμ h𝓕 f hf])
  have hc0 : c ≠ 0 := by intro h0; rw [h0, norm_zero] at hc; exact zero_ne_one hc
  refine ⟨⟨c⁻¹, by simp [Submonoid.unitSphere, hc]⟩, fun f hf u v => ?_⟩
  have e : N f = c • omS p f := by
    have := congrArg (omS p) (hM f hf)
    rwa [Module.End.mul_apply, hinv, map_smul] at this
  have e2 : omS p f = c⁻¹ • N f := by rw [e, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [e2, Pi.smul_apply, smul_eq_mul, hNapp, opA_apply]
  simp only [AddEquiv.apply_symm_apply, opB_apply]

end
end

