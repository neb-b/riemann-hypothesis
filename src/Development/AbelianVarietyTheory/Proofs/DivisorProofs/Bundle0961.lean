module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0018
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDiagonalCoordsEqPosMulAdeleHaar
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

noncomputable section
namespace GlobalTheory.DiagFormGlue

open GlobalTheory.DiagForm

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

theorem shiftOf_glue (p : Vi F κ × Vf F κ) : shiftOf (glue p) = p := by
  refine Prod.ext ?_ rfl
  change (eI F κ).symm (fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ p.1 i))) = p.1
  simp only [RingEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem glue_shiftOf (x : κ → AdeleRing (𝓞 F) F) : glue (shiftOf x) = x := by
  funext i
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ ((eI F κ).symm _) i) = (x i).1
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact RingEquiv.symm_apply_apply _ _

theorem glue_add (p q : Vi F κ × Vf F κ) : glue (p + q) = glue p + glue q := by
  conv_lhs => rw [← shiftOf_glue q]
  exact glue_add_shiftOf p (glue q)

theorem ringEquiv_symm_eq :
    ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm = ⇑(GroundTheory.Global.homeomorphMixedSpace F).symm := by
  funext z
  apply (GroundTheory.Global.homeomorphMixedSpace F).injective
  rw [Homeomorph.apply_symm_apply, GroundTheory.Global.homeomorphMixedSpace_apply, RingEquiv.apply_symm_apply]

theorem continuous_glue : Continuous (glue : Vi F κ × Vf F κ → κ → AdeleRing (𝓞 F) F) := by
  refine continuous_pi fun i => ?_
  show Continuous fun p : Vi F κ × Vf F κ =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ p.1 i), p.2 i) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  rw [ringEquiv_symm_eq]
  exact ((GroundTheory.Global.homeomorphMixedSpace F).symm.continuous.comp
    ((continuous_apply i).comp ((eI F κ).continuous.comp continuous_fst))).prodMk
    ((continuous_apply i).comp continuous_snd)

theorem continuous_shiftOf : Continuous (shiftOf : (κ → AdeleRing (𝓞 F) F) → Vi F κ × Vf F κ) := by
  refine Continuous.prodMk ((eI F κ).symm.continuous.comp (continuous_pi fun i => ?_))
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
  show Continuous fun x : κ → AdeleRing (𝓞 F) F => GroundTheory.Global.homeomorphMixedSpace F (x i).1
  exact (GroundTheory.Global.homeomorphMixedSpace F).continuous.comp (continuous_fst.comp (continuous_apply i))


variable (F κ) in
def glueEquiv : (Vi F κ × Vf F κ) ≃+ (κ → AdeleRing (𝓞 F) F) where
  toFun := glue
  invFun := shiftOf
  left_inv := shiftOf_glue
  right_inv := glue_shiftOf
  map_add' := glue_add

theorem exists_glue_measure :
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
    ∃ c : NNReal, 0 < c ∧ (mu F κ).map glue = c • (adeleMeasurePi F (ι := κ)) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : (mu F κ).IsAddHaarMeasure := by unfold mu; infer_instance
  haveI : ((mu F κ).map (glueEquiv F κ)).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map _ (glueEquiv F κ) continuous_glue continuous_shiftOf
  have h := Measure.isAddLeftInvariant_eq_smul ((mu F κ).map (glueEquiv F κ)) (adeleMeasurePi F (ι := κ))
  refine ⟨_, ?_, h⟩
  refine pos_iff_ne_zero.2 fun h0 => ?_
  rw [h0, zero_smul] at h
  exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := (mu F κ).map (glueEquiv F κ))).open_pos
    Set.univ isOpen_univ Set.univ_nonempty (by rw [h]; rfl)


variable (F κ) in
def glueMEquiv :
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
    (Vi F κ × Vf F κ) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.borelSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  (Homeomorph.mk (glueEquiv F κ).toEquiv continuous_glue continuous_shiftOf).toMeasurableEquiv

end GlobalTheory.DiagFormGlue

namespace GlobalTheory

theorem diagForm_glue_integral : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ H : (κ → AF F) → ℂ, (Integrable (fun p => H (GlobalTheory.DiagForm.glue p)) (GlobalTheory.DiagForm.mu F κ) ↔
      Integrable H (adeleMeasurePi F)) ∧
      ∫ p, H (GlobalTheory.DiagForm.glue p) ∂(GlobalTheory.DiagForm.mu F κ) = c₀ * ∫ t, H t ∂(adeleMeasurePi F) := by
  intro F _ _ κ _
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := GroundTheory.Global.measurableSpace_adeleRing F
  obtain ⟨c, hc, hmap⟩ := DiagFormGlue.exists_glue_measure (F := F) (κ := κ)
  have hmap' : (GlobalTheory.DiagForm.mu F κ).map (DiagFormGlue.glueMEquiv F κ) = c • adeleMeasurePi F (ι := κ) := hmap
  refine ⟨c, hc, fun H => ⟨?_, ?_⟩⟩
  · rw [← (integrable_smul_measure (f := H) (μ := adeleMeasurePi F (ι := κ)) (c := (c : ENNReal))
      (by exact_mod_cast hc.ne') ENNReal.coe_ne_top)]
    have e2 : (c : ENNReal) • adeleMeasurePi F (ι := κ) = c • adeleMeasurePi F (ι := κ) := rfl
    rw [e2, ← hmap', integrable_map_equiv]
    rfl
  · have h1 := integral_map_equiv (μ := GlobalTheory.DiagForm.mu F κ) (DiagFormGlue.glueMEquiv F κ) H
    rw [hmap', integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h1
    exact h1.symm
end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralLocalCenterFiniteMaximalIdeals
section
noncomputable section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem iotaF_injective (G : HTGroup p) (v : AwayP p) : Function.Injective (iotaF G v) := by
  have hf : Function.Injective (IsScalarTower.toAlgHom ℚ G.F G.C).toLinearMap :=
    (algebraMap G.F G.C).injective
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := Qv v) _ hf

def intFAlgMap (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    v.1.adicCompletionIntegers ℚ →+* intF G v h1 hm :=
  ((algebraMap (Qv v) (Qv v ⊗[ℚ] G.F)).comp (v.1.adicCompletionIntegers ℚ).subtype).codRestrict _ fun c => by
    rw [mem_intF]
    intro i
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      map_smul, Finsupp.smul_apply, smul_eq_mul, map_one]
    exact mul_mem c.2 (h1 i)

def intFCoord (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    letI := (intFAlgMap G v h1 hm).toAlgebra
    intF G v h1 hm →ₗ[v.1.adicCompletionIntegers ℚ] (Fin (Module.finrank ℚ G.C) → v.1.adicCompletionIntegers ℚ) :=
  letI := (intFAlgMap G v h1 hm).toAlgebra
  { toFun := fun m i => ⟨(basV G v).repr (iotaF G v m) i, (mem_intF G v h1 hm m).1 m.2 i⟩
    map_add' := fun a b => by
      funext i; apply Subtype.ext
      simp [map_add (f := _)]
    map_smul' := fun c m => by
      funext i; apply Subtype.ext
      show (basV G v).repr (iotaF G v (algebraMap (Qv v) (Qv v ⊗[ℚ] G.F) (c : Qv v) * m)) i =
        (c : Qv v) * (basV G v).repr (iotaF G v m) i
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, map_smul]
      rfl }

theorem intFCoord_injective (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    Function.Injective (intFCoord G v h1 hm) := by
  intro a b hab
  apply Subtype.ext
  apply iotaF_injective G v
  apply (basV G v).repr.injective
  refine Finsupp.ext fun i => ?_
  exact congrArg Subtype.val (congrFun hab i)

theorem intF_finite (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    letI := (intFAlgMap G v h1 hm).toAlgebra
    Module.Finite (v.1.adicCompletionIntegers ℚ) (intF G v h1 hm) :=
  letI := (intFAlgMap G v h1 hm).toAlgebra
  Module.Finite.of_injective (intFCoord G v h1 hm) (intFCoord_injective G v h1 hm)

theorem intF_finite_maximal : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)),
    Set.Finite {I : Ideal (intF G v h1 hm) | I.IsMaximal} := by
  intro p _ G v h1 hm
  letI := (intFAlgMap G v h1 hm).toAlgebra
  haveI := intF_finite G v h1 hm
  exact ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.finite_maximal_ideals_of_finite (R := v.1.adicCompletionIntegers ℚ) (intF G v h1 hm)

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCartanInvOneSplitStab
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

noncomputable section

theorem mt_mul_splitStab {D : D7} (V : HSp D) (g h : GA D V) : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_one_splitStab {D : D7} (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_one, Units.val_one]

theorem idem_unit_splitStab {R : Type} [CommRing R] {e d d' : R} (he : e * e = e) (h : d' * d = 1) :
    (e * d + (1 - e)) * (e * d' + (1 - e)) = 1 := by
  linear_combination (e * e) * h + (2 - d - d') * he

theorem exists_isDetAt_splitStab {D : D7} {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne _ _ (idem_unit_splitStab he (det_conj_mul V g)), Units.val_mkOfMulEqOne _⟩

open scoped ComplexOrder in
theorem isCartanInv_one_splitStab (k : ℕ) : IsCartanInv (1 : Matrix (Fin k) (Fin k) ℂ) 1 := by
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one]
  exact Matrix.PosDef.one

theorem heisO_zero_splitStab {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (f : WO V W → ℂ) : heisO ψ V W 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem om_vacuum_split_stab : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ (e : AE D) (k : GA D W), IsSplitIdem D e → SuppAt e W k → (∀ u, u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ actO V W 1 k u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True)) → om (1, k) f = mu k • f := by
  intro D ψ θ V W χV χW om hP mu hmu ΛV ΛW hV hW s hs f hf e k he hk hst
  obtain ⟨y, hy⟩ := exists_isDetAt_splitStab he.1 W k
  have h1 : ∀ τ, IsCartanInv (gramAt D V τ) ((fun _ => 1 : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ) := by
    intro τ
    have : gramAt D V τ = 1 := by
      unfold gramAt
      rw [hP.std]
      simp
    rw [this]
    exact isCartanInv_one_splitStab _
  have hs1 : SuppAt e V 1 := by
    intro i j
    rw [mt_one_splitStab, sub_self, Matrix.zero_apply, mul_zero]
  have hx : IsDetAt e V 1 1 := by
    unfold IsDetAt
    rw [mt_one_splitStab, Matrix.det_one, Units.val_one]
    ring
  have hact : ∀ u, actO V W 1 k (actO V W 1 k⁻¹ u) = u := by
    intro u
    unfold actO
    rw [inv_one, mt_one_splitStab, Matrix.mul_one, Matrix.mul_one, ← Matrix.mul_assoc, ← mt_mul_splitStab,
      mul_inv_cancel, mt_one_splitStab, Matrix.one_mul]
  have key := GlobalTheory.SplitScalar.om_vacuum_eq_splitFac_smul_sum D ψ θ V W χV χW om hP.weil hP.inf hP.sigV hP.sigW
    (fun _ => 1) s h1 hs ΛV ΛV ΛW ΛW hV hV hW hW e he 1 k hs1 hk 1 y hx hy
    (fun u => ⟨fun hu => ⟨actO V W 1 k⁻¹ u, (hst _).2 (by rw [hact]; exact hu), (hact u).symm⟩,
      fun ⟨u₀, hu₀, h⟩ => h ▸ (hst u₀).1 hu₀⟩)
    {0} {0}
    (fun u hu => by
      rw [Finset.mem_singleton.1 hu]
      exact ⟨zero_mem _, fun i j => mul_zero _⟩)
    (fun u hu _ => ⟨0, ⟨Finset.mem_singleton_self _, by rwa [sub_zero]⟩, fun v hv => Finset.mem_singleton.1 hv.1⟩)
    (fun u hu => by
      rw [Finset.mem_singleton.1 hu]
      exact ⟨zero_mem _, fun i j => mul_zero _⟩)
    (fun u hu _ => ⟨0, ⟨Finset.mem_singleton_self _, by rwa [sub_zero]⟩, fun v hv => Finset.mem_singleton.1 hv.1⟩)
    f hf
  have hr : IsDetRoot W k y := isDetAt_root he W k hk y hy
  rw [key, hmu.2 k y hr]
  simp [heisO_zero_splitStab, splitFacO]

end

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjugateDualTwistByTwistOfConjSelfDual
section
open NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open GlobalTheory.CuspRep Formalism.L2.Host

namespace GlobalTheory.ConjDualTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {m : ℕ}

theorem opTriv_thetaOp (o : Op E m) : opTriv (thetaOp o) = opTriv o := by
  cases o <;> rfl

theorem act_mulChi_oneFn (ψ : HChar E) (o : Op E m) :
    act o (mulChi m ψ (oneFn E m)) = (((opMul ψ o : ℂˣ) : ℂ) * opTriv o + opAdd ψ o) • mulChi m ψ (oneFn E m) := by
  rw [act_mulChi, act_oneFn, smul_smul, ← add_smul, map_smul]

theorem pull_oneFn : GlobalTheory.ThetaPull.pull E m (oneFn E m) = oneFn E m := Subtype.ext rfl

theorem scalar_thetaOp (χ : HChar E) (o : Op E m) :
    ((opMul χ (thetaOp o) : ℂˣ) : ℂ) * opTriv o + opAdd χ (thetaOp o) =
      ((opMul (GlobalTheory.ThetaPull.thetaChar χ) o : ℂˣ) : ℂ) * opTriv o + opAdd (GlobalTheory.ThetaPull.thetaChar χ) o := by
  have h1 := GlobalTheory.ThetaPull.act_pull o (mulChi m χ (oneFn E m))
  simp only [act_mulChi_oneFn, map_smul, GlobalTheory.ThetaPull.pull_mulChi, pull_oneFn, opTriv_thetaOp] at h1
  have hF : mulChi m (GlobalTheory.ThetaPull.thetaChar χ) (oneFn E m) ≠ 0 :=
    (LinearEquiv.map_ne_zero_iff _).2 oneFn_ne_zero
  exact (smul_left_injective ℂ hF h1).symm

theorem isConjDualBy_twist_thetaChar : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {m : ℕ} {π : GlobalTheory.CuspRep.CuspSub E m}, π.IsCsd → ∀ χ : Formalism.L2.Host.HChar E, GlobalTheory.GalOfCusp.IsConjDualBy (π.twist χ) (χ * (GlobalTheory.ThetaPull.thetaChar χ)⁻¹) := by
  intro E _ _ _ m π hπ χ
  refine GlobalTheory.GalOfCusp.isConjDualBy_twist hπ fun o => ?_
  have e : χ * (χ * (GlobalTheory.ThetaPull.thetaChar χ)⁻¹)⁻¹ = GlobalTheory.ThetaPull.thetaChar χ := by
    rw [mul_inv_rev, inv_inv, mul_comm (GlobalTheory.ThetaPull.thetaChar χ), ← mul_assoc, mul_inv_cancel, one_mul]
  rw [e]
  have h := scalar_thetaOp χ o
  cases o with
  | fin k => exact ⟨Units.ext (by simpa [opTriv, opAdd, thetaOp] using h), rfl⟩
  | cpt k => exact ⟨Units.ext (by simpa [opTriv, opAdd, thetaOp] using h), rfl⟩
  | lie X => exact ⟨rfl, by simpa [opTriv, opMul, thetaOp] using h⟩

end GlobalTheory.ConjDualTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaConjUnique
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open Formalism.L2.JoinChr
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramCharUnique

theorem eq_one_of_loc {D : D7} {χ : (AE D)ˣ →* Circle} (h : ChrEq χ 1) (x : (AE D)ˣ) : χ x = 1 := by
  refine HeckeFinTrivial.eq_one_of_trivial_on_finite D χ h.1 (fun y hy => ?_) x
  obtain ⟨j, h1, h2, h3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j h1 h2 (PlaceIdem.exists_isPlIdem D j h1 h2 h3) χ 1 h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom y)
  exact Subtype.ext ((hprod y hy S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS').trans
    (Finset.prod_eq_one fun P _ => rfl))

theorem loc_parts {D : D7} {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsPlIdem D e P) (k : D.host.E)
    (hk : P.valuation D.host.E k ≤ 1) : infPart D (locE D e k) = 1 ∧ finPart D (locE D e k) ∈ intAE D := by
  obtain ⟨ι, hι, hint, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨h1, h2, h3⟩ := HeckeTensorRead.isPlIdem_parts D ι hι hint he
  refine ⟨(HeckeTensorRead.map_loc (infPart D) e _).trans (by rw [h1, zero_mul, add_zero]), (hint _).2 fun Q => ?_⟩
  have h4 : ι (finPart D (incA D k)) = algebraMap D.host.E _ k := hι k
  have h5 : ι (finPart D (locE D e k)) = 1 + ι (finPart D e) * (algebraMap D.host.E _ k - 1) := by
    rw [← h4]
    exact HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _
  rw [h5]
  change Valued.v (1 + ι (finPart D e) Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) k - 1)) ≤ 1
  by_cases hQ : Q = P
  · subst hQ
    rw [h2, one_mul, add_sub_cancel, GlobalTheory.CharLocProd.val_algebraMap]
    exact hk
  · rw [h3 Q hQ, zero_mul, add_zero, map_one]

noncomputable def locHom {D : D7} {e : AE D} (he : e * e = e) : D.host.Eˣ →* (AE D)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun k => locE D e (k : D.host.E)
      map_one' := by simp [locE]
      map_mul' := fun k l => (locE_mul_locE he k l).symm }

theorem eq_one_of_unif {D : D7} {c : (AE D)ˣ →* Circle} (hc : IsHeckeChar D c) (hu : UnramEverywhere D c)
    (h : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ x : (AE D)ˣ,
      (x : AE D) = locE D e (Formalism.L2.Host.unif P : D.host.Eˣ) → c x = 1) (x : (AE D)ˣ) : c x = 1 := by
  refine eq_one_of_loc ⟨hc, fun P e he k y hy => ?_⟩ x
  obtain rfl : y = locHom he.1 k := Units.ext hy
  have hπ : P.valuation D.host.E ((Formalism.L2.Host.unif P : D.host.Eˣ) : D.host.E) = WithZero.exp (-1 : ℤ) :=
    (GlobalTheory.CharLocProd.val_algebraMap P _).symm.trans (Formalism.L2.Host.unif_spec P)
  have h0 : P.valuation D.host.E (k : D.host.E) ≠ 0 := by simp
  obtain ⟨n, hn⟩ : ∃ n : ℤ, P.valuation D.host.E (k : D.host.E) = WithZero.exp n := ⟨_, (WithZero.exp_log h0).symm⟩
  let u : D.host.Eˣ := k * Formalism.L2.Host.unif P ^ n
  have hv : P.valuation D.host.E (u : D.host.E) = 1 := by
    simp only [u, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hn, hπ]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hv' : P.valuation D.host.E ((u⁻¹ : D.host.Eˣ) : D.host.E) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  have h1 : c (locHom he.1 u) = 1 :=
    hu _ (loc_parts he _ hv.le).1 (loc_parts he _ hv.le).2 (by
      rw [← map_inv]
      exact (loc_parts he _ hv'.le).2)
  rw [map_mul, map_mul, map_zpow, map_zpow, h P e he (locHom he.1 (Formalism.L2.Host.unif P)) rfl, one_zpow, mul_one] at h1
  rw [h1]
  rfl

theorem isEtaConj_unique : ∀ (D : D7) (σ : D.what₂.LL →+* ℂ) (η η' η'' : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ η η' → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ η η'' → η' = η'' := by
  rintro D σ η η' η'' ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
  refine MonoidHom.ext fun x => mul_inv_eq_one.1 (eq_one_of_unif (c := η' * η''⁻¹)
    ⟨h1.1.mul g1.1.inv, fun k => mul_inv_eq_one.2 ((h1.2 k).trans (g1.2 k).symm)⟩
    (fun y a b c => mul_inv_eq_one.2 ((h2 y a b c).trans (g2 y a b c).symm))
    (fun P e he y hy => mul_inv_eq_one.2 ?_) x)
  obtain ⟨a, ha, ha'⟩ := h3 P e he y hy
  obtain ⟨b, hb, hb'⟩ := g3 P e he y hy
  obtain rfl : a = b := D.what₂.embLL.injective (ha.trans hb.symm)
  have : Finite (kP P) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  have hpos : (0 : ℝ) < (Nat.card (kP P) : ℝ) := Nat.cast_pos.2 Nat.card_pos
  exact Subtype.ext (mul_right_cancel₀ (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 hpos).ne'))
    (ha'.symm.trans hb'))

end GlobalTheory.UnramCharUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfAdicIntegralTensorBasisRing
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.AdicSpan

theorem isIntegral_of_isIntB : ∀ (v : HeightOneSpectrum ℤ) (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (κ : Type)
    (b : Module.Basis κ ℚ C), IsIntB v b 1 → (∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z)) →
      ∀ y, IsIntB v b y → IsIntegral (v.adicCompletionIntegers ℚ) y := by
  intro v C _ _ _ κ b h1 hmul y hy
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  set e := Algebra.TensorProduct.basis (v.adicCompletion ℚ) b with he
  have hsmul : ∀ (a : v.adicCompletionIntegers ℚ) (x : v.adicCompletion ℚ ⊗[ℚ] C),
      a • x = (a : v.adicCompletion ℚ) • x := fun a x => (algebraMap_smul (v.adicCompletion ℚ) a x).symm
  have hadd : ∀ x z, IsIntB v b x → IsIntB v b z → IsIntB v b (x + z) := fun x z hx hz i => by
    rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hx i) (hz i)
  let S : Subalgebra (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ ⊗[ℚ] C) :=
    { carrier := {x | IsIntB v b x}
      mul_mem' := fun {x z} hx hz => hmul x z hx hz
      one_mem' := h1
      add_mem' := fun {x z} hx hz => hadd x z hx hz
      zero_mem' := isIntB_zero v b
      algebraMap_mem' := fun a => by
        show IsIntB v b (algebraMap _ _ a)
        rw [Algebra.algebraMap_eq_smul_one, hsmul]
        intro i
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact mul_mem a.2 (h1 i) }
  have hS : Subalgebra.toSubmodule S = Submodule.span (v.adicCompletionIntegers ℚ)
      (Set.range fun i => (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] b i) := by
    apply le_antisymm
    · intro x hx
      rw [← e.sum_repr x]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨c, hc⟩ : ∃ c : v.adicCompletionIntegers ℚ, (c : v.adicCompletion ℚ) = e.repr x i :=
        ⟨⟨_, hx i⟩, rfl⟩
      rw [← hc, ← hsmul, he, Algebra.TensorProduct.basis_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact isIntB_tmul_basis v b j
  refine IsIntegral.of_mem_of_fg S ?_ y hy
  rw [hS]
  exact Submodule.fg_span (Set.finite_range _)

end GlobalTheory.AdicSpan
end

