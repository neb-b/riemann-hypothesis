module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0721
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0155
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0088
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0008
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0083
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjSplitLocalModelBySupportedPair
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm

namespace GlobalTheory.LocTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def conjH (gk : GL Y' k) (hk : GL Y k) : Matrix Y Y' k ≃ₜ Matrix Y Y' k where
  toFun x := (hk⁻¹).val * x * gk.val
  invFun x := hk.val * x * (gk⁻¹).val
  left_inv x := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  right_inv x := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def twist (c : ℂ) (gk : GL Y' k) (hk : GL Y k) : SB (Matrix Y Y' k) →ₗ[ℂ] SB (Matrix Y Y' k) where
  toFun Φ := ⟨fun x => c * Φ.1 ((hk⁻¹).val * x * gk.val),
    (SB _).smul_mem c (show Φ.1 ∘ conjH gk hk ∈ SB _ from ⟨Φ.2.1.comp_continuous (conjH gk hk).continuous,
      Φ.2.2.comp_homeomorph (conjH gk hk)⟩)⟩
  map_add' Φ Ψ := by
    apply Subtype.ext; funext x
    simp only [Submodule.coe_add, Pi.add_apply]; ring
  map_smul' a Φ := by
    apply Subtype.ext; funext x
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem twist_apply (c : ℂ) (gk : GL Y' k) (hk : GL Y k) (Φ : SB (Matrix Y Y' k)) (x) :
    (twist c gk hk Φ).1 x = c * Φ.1 ((hk⁻¹).val * x * gk.val) := rfl

variable {D : D7} (p : Place D k)

theorem mt_inv_mul' {S : HSp D} (g : GA D S) : mt S g⁻¹ * mt S g = 1 := by
  rw [show mt S g⁻¹ * mt S g = mt S (g⁻¹ * g) by simp [Formalism.L2.Theta.mt], inv_mul_cancel]
  simp [Formalism.L2.Theta.mt]

theorem actO_up {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {g : GA D S} {gk : GL Y' k}
    {h : GA D T} {hk : GL Y k} (hg : p.IsLoc FS g gk) (hh : p.IsLoc FT h hk) (x : Matrix Y Y' k) :
    actO S T g h (p.up FS FT x) = p.up FS FT (hk.val * x * (gk⁻¹).val) := by
  have h1 : IsHalf p.e (actO S T g h (p.up FS FT x)) :=
    GlobalTheory.SplitHecke.isHalf_actO g h (Witness.up_half p FS FT x)
  rw [← Witness.up_down p FS FT h1]
  congr 1
  set M := (mt S g⁻¹).map p.π with hMdef
  have hM : M * (FS.β * gk.val * FS.γ) = 1 := by
    rw [← hg.2, hMdef, ← Matrix.map_mul, mt_inv_mul', Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : FS.γ * (M * FS.β) * gk.val = 1 := by
    have : FS.γ * (M * (FS.β * gk.val * FS.γ)) * FS.β = 1 := by rw [hM, Matrix.mul_one, FS.γβ]
    rw [← this]
    simp only [Matrix.mul_assoc, FS.γβ, Matrix.mul_one]
  have hN : FS.γ * (M * FS.β) = (gk⁻¹).val := by
    calc FS.γ * (M * FS.β) = FS.γ * (M * FS.β) * gk.val * (gk⁻¹).val := by
          rw [Matrix.mul_assoc (FS.γ * (M * FS.β)), Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [e1, Matrix.one_mul]
  have hu : (p.up FS FT x).map p.π = FT.β * x * FS.γ := Matrix.ext fun _ _ => p.π_ι _
  unfold Place.down actO
  rw [Matrix.map_mul, Matrix.map_mul, hh.2, hu, ← hMdef]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc FT.γ FT.β, FT.γβ, Matrix.one_mul, ← Matrix.mul_assoc FT.γ FT.β, FT.γβ, Matrix.one_mul, hN]

end GlobalTheory.LocTwist

namespace GlobalTheory.LocTwist

theorem conj_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : Om S T), IsWeilDatumO ψ S T χS χT ω → ∀ (μS μT : kˣ →* ℂˣ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)), p.IsModel ψ FS FT Tm → ∀ (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k), p.IsLoc FS g gk → p.IsLoc FT h hk → ∃ T₂ : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ), p.IsModel ψ FS FT T₂ ∧ ∀ Φ Φ' : SB (Matrix Y Y' k), Φ'.1 = (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk Φ.1 → T₂ Φ = ω (g⁻¹, h⁻¹) (Tm Φ') := by
  intro D k _ _ _ _ p ψ S T χS χT ω hW μS μT Y Y' _ _ _ _ FS FT Tm hm g gk h hk hg hh
  set c : ℂ := (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) *
    ((μS⁻¹ (Matrix.GeneralLinearGroup.det gk) : ℂ) * ((μS⁻¹ (Matrix.GeneralLinearGroup.det hk))⁻¹ : ℂˣ) *
    ((nabs k (Matrix.GeneralLinearGroup.det gk) ^ ((Fintype.card Y : ℝ) / 2) : ℝ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det hk) ^ (-(Fintype.card Y' : ℝ) / 2) : ℝ) : ℂ)) with hc
  let L := LocTwist.twist c gk hk
  let W₀ : Module.End ℂ (WO S T → ℂ) := ω (g⁻¹, h⁻¹)
  have hA := LocTwist.actO_up p FS FT hg hh
  have hback : ∀ z, actO S T g⁻¹ h⁻¹ (p.up FS FT (hk.val * z * (gk⁻¹).val)) = p.up FS FT z := fun z => by
    rw [← hA, GlobalTheory.SplitHecke.actO_inv_actO]
  refine ⟨W₀ ∘ₗ Tm ∘ₗ L, ⟨fun Φ => hW.om_pres _ _ (hm.theta _), fun x Φ Φ₁ hΦ => ?_, fun y hy Φ Φ₁ hΦ => ?_⟩, fun Φ Φ' e => ?_⟩
  · have h1 : ∀ t, (L Φ₁).1 t = (L Φ).1 (t + hk.val * x * (gk⁻¹).val) := fun t => by
      simp only [L, LocTwist.twist_apply, hΦ]
      congr 2
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc ((hk⁻¹).val) hk.val, Units.inv_mul, Matrix.one_mul]
    have h2 := hm.trans _ (L Φ) (L Φ₁) h1
    simp only [LinearMap.comp_apply]
    rw [h2]
    show ω (g⁻¹, h⁻¹) _ = _
    rw [hW.om_heis _ _ _ _ (hm.theta _), hback]
  · set y' := actO S T g h y
    have hy' : IsHalf (cA D p.e) y' := GlobalTheory.SplitHecke.isHalf_actO g h hy
    have h1 : ∀ t, (L Φ₁).1 t = ψ (symplO S T (p.up FS FT t) y') * (L Φ).1 t := fun t => by
      simp only [L, LocTwist.twist_apply, hΦ]
      have hu : p.up FS FT ((hk⁻¹).val * t * gk.val) = actO S T g⁻¹ h⁻¹ (p.up FS FT t) := by
        rw [← hback ((hk⁻¹).val * t * gk.val)]
        congr 2
        simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      have hs : symplO S T (p.up FS FT ((hk⁻¹).val * t * gk.val)) y = symplO S T (p.up FS FT t) y' := by
        rw [hu, ← GlobalTheory.SplitHecke.symplO_actO S T g⁻¹ h⁻¹ (p.up FS FT t) y', GlobalTheory.SplitHecke.actO_inv_actO]
      rw [hs]; ring
    have h2 := hm.modul y' hy' (L Φ) (L Φ₁) h1
    simp only [LinearMap.comp_apply]
    rw [h2]
    show ω (g⁻¹, h⁻¹) _ = _
    rw [hW.om_heis _ _ _ _ (hm.theta _), GlobalTheory.SplitHecke.actO_inv_actO]
  · have : Φ' = L Φ := by
      apply Subtype.ext; funext t
      rw [e]
      simp only [L, LocTwist.twist_apply, Pi.smul_apply, smul_eq_mul, om, hc]
      ring
    rw [this]; rfl

end GlobalTheory.LocTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteScalarComponentIsCuspAndCongruenceFixedA
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.DownLift.DefiniteComp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem extV_mul_inf (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    {k : GA D (Vc D i)} (hk : k ∈ GinfC (Vc D i)) (h : GA D (Vc D i)) :
    R.extV i t y (h * k) = (R.cV i).ρ k⁻¹ (R.extV i t y h) := by
  have hr : (finHom (Vc D i)).rangeRestrict (h * k) = (finHom (Vc D i)).rangeRestrict h := by
    apply Subtype.ext
    simp [MonoidHom.mem_ker.1 hk]
  show (R.cV i).ρ (h * k)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * k))) =
    (R.cV i).ρ k⁻¹ ((R.cV i).ρ h⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h)))
  refine (congrArg ((R.cV i).ρ (h * k)⁻¹) (congrArg ((R.HV i t).e y) hr)).trans ?_
  have e : (R.cV i).ρ (h * k)⁻¹ = (R.cV i).ρ k⁻¹ * (R.cV i).ρ h⁻¹ := by rw [_root_.mul_inv_rev, map_mul]
  exact congrArg (fun f : Module.End ℂ (R.cV i).W => f ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h))) e

theorem extV_mul_Kg (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    {κ : GA D (Vc D i)} (hκ : κ ∈ GfC (Vc D i))
    (hK : finE (Vc D i) κ ∈ Kg D.sp.cm (Vc D i).gram (R.βV i) (R.Pg ∪ R.Q t)) (h : GA D (Vc D i)) :
    R.extV i t y (h * κ) = R.extV i t y h := by
  have h2 : Kg D.sp.cm (Vc D i).gram (R.βV i) (R.Pg ∪ R.Q t) ≤
      lev D.sp.cm (Vc D i).gram (R.βV i) (flag1L (R.datVt i t)) :=
    Kg_le_lev (D := flag1L (R.datVt i t)) Finset.subset_union_left Finset.subset_union_right
  have hlev : κ ∈ levG (Vc D i) (R.βV i) (flag1L (R.datVt i t)) := mem_levA.2 ⟨hκ, h2 hK⟩
  have hred : ∀ PP ∈ R.Pg ∪ R.Q t, redFn (R.βV i) PP (finE (Vc D i) κ) = 1 := fun PP hP =>
    (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hK.2 PP) hP)).2
  have hfn : levFn (R.βV i) (flag1L (R.datVt i t)) (finE (Vc D i) κ) = 1 :=
    GlobalTheory.ThetaIntegrand.levFn_eq_one (R.βV i) _ (flag1L (R.datVt i t))
      (fun PP hP => hred PP (Finset.mem_union_left _ hP)) (fun PP hP => hred PP (Finset.mem_union_right _ hP))
  have hchi : levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ = 1 :=
    (congrArg (fun u : ℂˣ => (u : ℂ)) hfn).trans Units.val_one
  exact (GlobalTheory.DownLift.GenFinite.extV_type R hM i t y κ hlev h).trans (by simp only [hchi, one_smul])

def compL (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) :
    ((R.cV i).W →ₗ[ℂ] ℂ) →ₗ[ℂ] (GA D (Vc D i) → ℂ) :=
  LinearMap.pi fun g => LinearMap.applyₗ (R := ℂ) (R.extV i t y g)

theorem mul_inf_mem_range (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ)
    {k : GA D (Vc D i)} (hk : k ∈ GinfC (Vc D i)) :
    (fun g => l (R.extV i t y (g * k))) ∈ LinearMap.range (compL R i t y) :=
  ⟨l ∘ₗ (R.cV i).ρ k⁻¹, funext fun g => (congrArg l (extV_mul_inf R i t y hk g)).symm⟩

theorem definiteScalarComponent_isCusp_and_congruence_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t cA a, Defin R.θ (Vc D i) cA a → ∀ (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ), (fun g => l (R.extV i t y g)) ∈ GlobalTheory.Cusp.A0 R.θ (Vc D i) cA ∧ ∀ κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), ∀ g, l (R.extV i t y (g * κ)) = l (R.extV i t y g) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t cA a hd y l
  have hM : R.IsModels := hG.core.models
  have hf : (R.HV i t).e y ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hM.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hcont : Continuous fun g => l (R.extV i t y g) :=
    (LinearMap.continuous_of_finiteDimensional l).comp
      (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hM.cV i) (R.βV i) (R.datVt i t) hf)
  have hleft : ∀ γ ∈ GQ (Vc D i), ∀ g, l (R.extV i t y (γ * g)) = l (R.extV i t y g) := fun γ hγ g =>
    congrArg l (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hf γ hγ g)
  have hlevel : ∃ U : Subgroup (GA D (Vc D i)), IsOpen (U : Set (GA D (Vc D i))) ∧
      ∀ k ∈ U, k ∈ GfC (Vc D i) → ∀ g, l (R.extV i t y (g * k)) = l (R.extV i t y g) :=
    ⟨_, GlobalTheory.DefiniteEnd.isOpen_Kg (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), fun k hk hkf g =>
      congrArg l (extV_mul_Kg R hM i t y hkf hk g)⟩
  have hkfin : FiniteDimensional ℂ (Submodule.span ℂ {ψ : GA D (Vc D i) → ℂ |
      ∃ k ∈ GinfC (Vc D i), ψ = rTr (Vc D i) k fun g => l (R.extV i t y g)}) :=
    Submodule.finiteDimensional_of_le (Submodule.span_le.2 (by
      rintro _ ⟨k, hk, rfl⟩
      exact mul_inf_mem_range R i t y l hk))
  have hdef : IsAutFunDef (Vc D i) fun g => l (R.extV i t y g) := ⟨⟨hleft, hlevel, hcont⟩, hkfin⟩
  have hdefn : (Vc D i).IsDefinite := fun τ => Or.inl (hd.pos τ)
  have hsm := ((GlobalTheory.DefiniteForms.autFunDefIffSm D) R.θ hd.inf (Vc D i) hd.sig hdefn _).1 hdef
  have hcusp : IsCuspFun (Vc D i) fun g => l (R.extV i t y g) := fun r C hC =>
    absurd hC (GlobalTheory.Per.isAniso_of_posDef hd.sig hd.pos r C)
  have hK : GlobalTheory.Doubling.IsKFinite (GlobalTheory.Cusp.Kinf R.θ (Vc D i) cA) fun g => l (R.extV i t y g) :=
    GlobalTheory.Doubling.isKFinite_iff.2 ⟨LinearMap.range (compL R i t y), inferInstance, fun k hk =>
      mul_inf_mem_range R i t y l (GlobalTheory.Cusp.Kinf_le hk)⟩
  refine ⟨GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨hsm, hcusp⟩, hK⟩, fun κ hκ g => ?_⟩
  have h1 := mem_levA.1 hκ
  have h2 : finE (Vc D i) κ ∈ Kg D.sp.cm (Vc D i).gram (R.βV i) (R.Pg ∪ R.Q t) :=
    (Model.lev_prinDat (Vc D i) (R.βV i) (R.Pg ∪ R.Q t)) ▸ h1.2
  exact congrArg l (extV_mul_Kg R hM i t y h1.1 h2 g)

end GlobalTheory.DownLift.DefiniteComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteStepSmallVectorFockVacuumSpherical
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.SmallVac

theorem smallVec_vac_sph : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) → IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f → IsThetaFunO ψ A H f ∧ f ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO (sA τ) (sH τ)) f) ∧ IsSphOff ψ A H (frameLat A) (frameLat H) (under Z) f := by
  classical
  intro D ψ θ A H χA om sA sH hθ hη hω hsA hsH hr β Z hZ βH f₀ f hβH h
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.Chain.StepVac.stepVec_vac (GlobalTheory.Core.Rk.IP.frameLat_isSelfDualC A)
    (GlobalTheory.Core.Rk.IP.frameLat_isSelfDualC H) hr h
  refine ⟨h1, h2, h3, ?_⟩
  obtain ⟨hvac, e, he, hth⟩ := h
  have hle : latO A H (frameLat A) (frameLat H) (fun v => v ∉ under Z) ≤
      latO A H (frameLat A) (frameLat H) fun _ => True :=
    GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  have hlat := hvac.2.lat
  have hZu : ∀ PP ∈ (prinDat A Z).Pg ∪ ∅, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ under Z := by
    intro PP hPP
    rw [Finset.union_empty] at hPP
    unfold under
    exact Finset.mem_image_of_mem _ hPP
  have fix : ∀ u ∈ latO A H (frameLat A) (frameLat H) (fun v => v ∉ under Z), heisO ψ A H u f₀ = f₀ →
      heisO ψ A H u f = f := fun u hu h0 =>
    GlobalTheory.Hk3.heisO_fix_thetaAt_off ψ A H e _ 1 f₀ _ f hth u
      (GlobalTheory.FockSph.idemSum_mul_of he (fun PP hPP hn => hn (hZu PP hPP)) hu) h0
  exact ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hlat.1 u (hle hu)),
    fun e' he' u hu hh => fix u hu (hlat.2 e' he' u (hle hu) hh)⟩

end GlobalTheory.Core.Rk.SmallVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingBasicIdentityFlatSectionCuspForms
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem basicIdentity_flat : GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → ∀ θ : GlobalTheory.Mem.Th.InfF D, IsInfFam θ → ∀ A : CptF V, ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ ∈ GlobalTheory.Cusp.A0 θ V A, ∀ f₂ ∈ GlobalTheory.Cusp.A0 θ V A, ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → GlobalTheory.Eis.BasicIdentity V μ m (flat V a φ s₁ s) f₁ f₂ :=
  fun hE hC D V hV a ha hI μ hμ _ _ hφ _ hθ _ m hm f₁ h₁ f₂ h₂ s hs =>
    _root_.GlobalTheory.Core.Rk.BasicId.basicIdentity_unfold D V a ha μ hμ s hs _ (GlobalTheory.Eis.flat_mem hI hφ s) (_root_.GlobalTheory.Eis.modGrowth_eis_sph hE D V hV a ha hI s.re hs) m hm f₁ f₂
      (GlobalTheory.Grow.rapidDec_of_cuspForm hC hθ (GlobalTheory.Cusp.mem_cuspForms.1 h₁).1.1 (GlobalTheory.Cusp.mem_cuspForms.1 h₁).1.2)
      (GlobalTheory.Grow.rapidDec_of_cuspForm hC hθ (GlobalTheory.Cusp.mem_cuspForms.1 h₂).1.1 (GlobalTheory.Cusp.mem_cuspForms.1 h₂).1.2)
      (GlobalTheory.Cusp.mem_cuspForms.1 h₁).1.2

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyNhdsOneAdelicMatrixCongruentOneAtPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

namespace GlobalTheory.TwU.NearOne

theorem congAt_eventually_nhds_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n N : ℕ) (P : HeightOneSpectrum (𝓞 E)), letI := Formalism.L2.Col.rlt_top (F := F) (E := E); ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, GlobalTheory.TwU.CongAt P N u := by
  intro F E _ _ _ _ _ n N P
  letI : TopologicalSpace (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Formalism.L2.Col.rlt_top (F := F) (E := E)
  haveI : IsTopologicalRing (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
  show ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ a b, _
  refine Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => ?_
  have hop : IsOpen ((fun y : E ⊗[F] FiniteAdeleRing (𝓞 F) F =>
      Formalism.L2.Col.iA F E (((Formalism.L2.Col.qOf P : ℕ) : E) ^ N)⁻¹ * y) ⁻¹'
      (Formalism.L2.Herm.intAf F E : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) :=
    Formalism.L2.Col.rlt_isOpen_intAf.preimage (continuous_const.mul continuous_id)
  have h0 : (0 : E ⊗[F] FiniteAdeleRing (𝓞 F) F) ∈ (fun y : E ⊗[F] FiniteAdeleRing (𝓞 F) F =>
      Formalism.L2.Col.iA F E (((Formalism.L2.Col.qOf P : ℕ) : E) ^ N)⁻¹ * y) ⁻¹'
      (Formalism.L2.Herm.intAf F E : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
    simp only [Set.mem_preimage, mul_zero]
    exact zero_mem _
  have hcont : Continuous fun u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
      (u : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b -
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b :=
    (Units.continuous_val.matrix_elem a b).sub continuous_const
  have ht := hcont.tendsto' 1 0 (by simp)
  filter_upwards [ht (hop.mem_nhds h0)] with u hu
  refine ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
  simpa [Matrix.sub_apply] using hu

end GlobalTheory.TwU.NearOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCharExponentInfinityKernelShift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.TwDat

theorem int_eq_sub_half (R : Ranks) (j : ℕ) (s z : ℤ) (h : (s : ℚ) = z - (R.N j : ℚ) / 2) : s = z - (R.N j : ℤ) / 2 := by
  obtain ⟨b, hb⟩ := N_even R j
  have e : (s : ℚ) = ((z - b : ℤ) : ℚ) := by rw [h, hb]; push_cast; ring
  have e' : s = z - b := by exact_mod_cast e
  rw [e', hb]
  omega


set_option maxHeartbeats 800000 in
theorem chr_exp_shifts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∃ e : (I.rec7 l Z).what₂.Tau → ℤ, (∀ τ, HasInfExp (I.rec7 l Z) (A.chr (i + 1)) τ (e τ)) ∧ ∀ τ, (I.chain l u a).sSharp i τ = -e τ - ((I.rec7 l Z).sp.X (i + 1)).rank / 2 ∧ -(I.chain l u a).sDiv i τ = e τ + ((I.rec7 l Z).sp.X i).rank / 2 ∧ 0 ≤ shiftOf (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u i) τ + (I.chain l u a).sSharp i τ := by
  intro B X I hI _ l Z u a Ch A hA i hi
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host _ B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  obtain ⟨n, hn, hord⟩ := htw.1
  choose e he using fun τ => (B.hc τ).e_int ⟨i, hi⟩
  have hinf := Formalism.L2.Host.HChar.HasInfQ.mul_triv (I.C.isMu0 ⟨i, hi⟩).inf
    (Formalism.L2.Host.HChar.inf_eq_one_of_order hn hord)
  have hexp := (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ (I.rec7 l Z) _ _ _ (hA.chr ⟨i, hi⟩)).2 hinf
  refine ⟨fun τ => -e τ, fun τ => ?_, fun τ => ?_⟩
  · have e1 : ((-e τ : ℤ) : ℚ) = -(B.hc τ).e ⟨i, hi⟩ := by rw [Int.cast_neg, ← he τ]
    exact e1 ▸ hexp τ
  · have hw : (B.hcW u τ).e ⟨i, hi⟩ = e τ := by
      have h : (B.hcW u τ).e = (B.hc τ).e := (I.rec7 l Z).hcW_e u τ
      rw [h, he τ]
    have h1 : (I.chain l u a).sSharp i τ = e τ - (B.R.N (i + 1) : ℤ) / 2 := by
      apply int_eq_sub_half
      rw [(I.chain l u a).sSharp_eq i hi τ, ← hw]
      rfl
    have h2 : (I.chain l u a).sDiv i τ = e τ - (B.R.N i : ℤ) / 2 := by
      apply int_eq_sub_half
      rw [(I.chain l u a).sDiv_eq i hi τ, ← hw]
      rfl
    have r1 : ((I.rec7 l Z).sp.X (i + 1)).rank = B.R.N (i + 1) := rankN (I.rec7 l Z) (i + 1) hi
    have r0 : ((I.rec7 l Z).sp.X i).rank = B.R.N i := rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)
    refine ⟨?_, ?_, ?_⟩
    · rw [r1, h1, neg_neg]
    · rw [r0, h2]; ring
    · obtain ⟨k, -, hk, -⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ (I.fm l u a) i hi
      exact (Int.natCast_nonneg (k τ)).trans_eq (hk τ).symm

end GlobalTheory.AdForm.TwDat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocMod.SevPl

open GlobalTheory.IdemSupport

theorem pr_eq_zero {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {f : Formalism.L2.Theta.AE D} (h : q.e * f = 0) : q.pr f = 0 := by
  rw [← q.pr_sec (q.pr f), q.sec_pr, h, map_zero]

end GlobalTheory.LocMod.SevPl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharValueSplitPrimeNotRootOfUnity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitValueAdelic

theorem not_isOfFinOrder_val : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ → (∀ τ : D.what₂.Tau, ∃ a : ℚ, a ≠ 0 ∧ HasInfExp D χ τ a) → ∀ p : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.LFun.UnrAt χ w → ¬ IsOfFinOrder (GlobalTheory.LFun.val (F := D.host.F) χ w) := by
  intro D χ hχ ha p hp w hw _
  obtain ⟨H, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D χ hχ
  choose a ha0 ha using ha
  have h1 := (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D χ H a hH).1 ha
  rw [(GlobalTheory.ChrTie.unrAt_iff_and_val_eq D χ H hH w).2]
  exact _root_.GlobalTheory.SplitValuePow.not_isOfFinOrder_val D H a p h1 ha0 hp w hw

end GlobalTheory.SplitValueAdelic
end

