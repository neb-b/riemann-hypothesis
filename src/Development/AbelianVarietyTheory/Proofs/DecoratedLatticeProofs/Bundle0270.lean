module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0322
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepAverageKillsThetaOfDenseFamily
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0266
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightSelfDualLatticesEqConj
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

theorem hgtL_eq_conj_of_selfDual : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' → ∃ k ∈ GfC A, ∀ (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ g, hgtL A L' a g = hgtL A L a (k⁻¹ * g * k) := by
  intro D A L L' hL hL'
  obtain ⟨k, hk, hK⟩ := _root_.GlobalTheory.Core.Rk.LatMove.exists_conj_KAd_of_selfDual D A L L' hL hL'
  refine ⟨k, hk, fun a ha g => ?_⟩
  letI := GlobalTheory.OntoModPf.selfDual_isFullLattice A L hL
  letI := GlobalTheory.OntoModPf.selfDual_isFullLattice A L' hL'
  have hI := _root_.GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D A L' a hL' ha
  have hj : io A (k, k) ∈ siegel A := (io_mem_siegel A).2 rfl
  obtain ⟨p, κ, hκ, hx⟩ := hI (io A (g, 1))
  have hκ' : (io A (k, k))⁻¹ * κ * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a := (hK a κ).1 hκ
  have e : io A (k⁻¹ * g * k, 1) =
      ((⟨io A (k, k), hj⟩⁻¹ * p * ⟨io A (k, k), hj⟩ : siegel A) : GA D (dblSp A)) *
        ((io A (k, k))⁻¹ * κ * io A (k, k)) := by
    have h1 : io A (k⁻¹ * g * k, 1) = (io A (k, k))⁻¹ * io A (g, 1) * io A (k, k) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      simp
    rw [h1, hx]
    simp [mul_assoc]
  change hgtAd _ _ L' a (io A (g, 1)) = hgtAd _ _ L a (io A (k⁻¹ * g * k, 1))
  rw [hx, e]
  calc
    hgtAd _ _ L' a (↑p * κ) = _ := hgtAd_mul (isCMExt_host D) p hκ
    _ = _ := by
      congr 1
      rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
    _ = hgtAd _ _ L a (↑(⟨io A (k, k), hj⟩⁻¹ * p * ⟨io A (k, k), hj⟩ : siegel A) *
        ((io A (k, k))⁻¹ * κ * io A (k, k))) :=
      (hgtAd_mul (isCMExt_host D) _ hκ').symm

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralsVanishOfAllLiftsVanish
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

namespace GlobalTheory.Core.Rk.Kill

variable {D : D7}

theorem exists_bound_of_fundamentalDomain {A : HSp D} {m : Measure (GA D A)} [m.IsHaarMeasure] {X K : Set (GA D A)}
    (hX : IsFundamentalDomain (GQ A) X m) (hK : IsCompact K) (hXK : X ⊆ K) {u : GA D A → ℂ} (hu : Continuous u)
    (hi : ∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) : ∃ C : ℝ, ∀ g, ‖u g‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hu.continuousOn
  refine ⟨C, fun g => ?_⟩
  by_contra hg
  push_neg at hg
  have hopen : IsOpen {x | C < ‖u x‖} := isOpen_lt continuous_const hu.norm
  have hpos : 0 < m {x | C < ‖u x‖} := hopen.measure_pos m ⟨g, hg⟩
  have hnull : m {x | C < ‖u x‖} = 0 := by
    have hcov := hX.ae_covers
    rw [ae_iff] at hcov
    refine measure_mono_null (fun x hx => ?_) hcov
    simp only [Set.mem_setOf_eq, not_exists]
    intro γ hγ
    have h1 := hC _ (hXK hγ)
    rw [Subgroup.smul_def, smul_eq_mul, hi _ γ.2] at h1
    exact absurd h1 (not_le.2 hx)
  exact hpos.ne' hnull

theorem thetaKO_rat {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h : GA D T) :
    ∀ γ ∈ GQ S, ∀ g, thetaKO om (γ * g) h f = thetaKO om g h f := fun γ hγ g => by
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
  simp only [thetaKO]
  rw [e, map_mul, Module.End.mul_apply]
  exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ f hf)

theorem continuous_thetaKO {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h : GA D T) :
    Continuous fun g => thetaKO om g h f :=
  (hom.om_cont f hf 0).comp (continuous_id.prodMk continuous_const)

theorem kills_of_noLift : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A W : HSp D) (χA χW : (AE D)ˣ →* Circle)
    (om : WRep A W) (omh : WRep (dblSp A) W), HSpace.SigOK A → HSpace.IsPosDef A → IsWeilDatumO ψ A W χA χW om →
    IsWeilDatumO ψ (dblSp A) W 1 χW omh → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u →
    (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → NoLift ψ om m u → Kills ψ χW omh m u := by
  intro D ψ A W χA χW om omh hsig hpos hom homh m hm u hu hui hno φ hφ h
  haveI := hm
  obtain ⟨-, X, K, hXm, hX, hK, hXK⟩ := _root_.GlobalTheory.DefFund.coCpt_and_fundamentalDomain_subset_compact D A hsig hpos m hm
  have hTC := _root_.GlobalTheory.DoublingTheta.thetaClause D ψ A W χA χW om omh hom homh
  obtain ⟨C, hC⟩ := exists_bound_of_fundamentalDomain hX hK hXK hu hui
  have hχ : IsHeckeChar D χW := hom.hecT
  have hχi : IsHeckeChar D χW⁻¹ :=
    ⟨continuous_inv.comp hχ.1, fun x => by rw [MonoidHom.inv_apply, hχ.2 x, inv_one]⟩

  have hEc : Continuous fun g => thetaKO omh g h φ := continuous_thetaKO homh hφ h
  have hEi : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (dblSp A)) fun g => thetaKO omh g h φ := thetaKO_rat homh hφ h
  have hcu : Continuous fun g => conj (u g) := Complex.continuous_conj.comp hu
  have hcui : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) fun g => conj (u g) := fun γ hγ g => by
    simp only [hui γ hγ g]

  have hFc := Eis.continuous_dblIntegrand (V := A) hχi hEc hcu hcu
  have hFi := Eis.leftInv_dblIntegrand (V := A) hχi hEi hcui hcui
  have hFint : IntegrableOn (Eis.dblIntegrand A χW⁻¹ (fun g => thetaKO omh g h φ) (fun g => conj (u g))
      (fun g => conj (u g))) (X ×ˢ X) (m.prod m) :=
    (hFc.continuousOn.integrableOn_compact (hK.prod hK)).mono_set (Set.prod_mono hXK hXK)
  have hconv := (Eis.dblConv_iff hFi hFc.measurable hX).2 hFint
  show Eis.dblInt A χW⁻¹ m (fun g => thetaKO omh g h φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0
  rw [(hconv.dblInt_eq hX).2, ← Measure.prod_restrict]
  haveI : IsFiniteMeasure (m.restrict X) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hXK).trans_lt hK.measure_lt_top⟩

  set μ : Measure (GA D A × GA D A) := (m.restrict X).prod (m.restrict X) with hμ
  set c : GA D A × GA D A → ℂ := fun g => u g.1 * conj (u g.2) * (χW (detA A g.2) : ℂ) with hc
  set p : GA D A × GA D A → GA D (dblSp A) × GA D W := fun g => (io A g, h) with hp
  have hint : ∀ G : GA D A × GA D A → ℂ, Continuous G → Integrable G μ := fun G hG => by
    rw [hμ, Measure.prod_restrict]
    exact (hG.continuousOn.integrableOn_compact (hK.prod hK)).mono_set (Set.prod_mono hXK hXK)
  have hFeq : ∀ g, Eis.dblIntegrand A χW⁻¹ (fun g => thetaKO omh g h φ) (fun g => conj (u g))
      (fun g => conj (u g)) g = c g * omh (p g) φ 0 := fun g => by
    simp only [Eis.dblIntegrand, hc, hp, thetaKO, MonoidHom.inv_apply, Circle.coe_inv, inv_inv, Complex.conj_conj]
    ring
  simp_rw [hFeq]
  have hcc : Continuous c :=
    ((hu.comp continuous_fst).mul (Complex.continuous_conj.comp (hu.comp continuous_snd))).mul
      (continuous_subtype_val.comp (hχ.1.comp (Eis.continuous_detA.comp continuous_snd)))
  have hcb : ∀ g, ‖c g‖ ≤ C * C := fun g => by
    simp only [hc, norm_mul, Complex.norm_conj, Circle.norm_coe, mul_one]
    exact mul_le_mul (hC _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hC g.1))
  have hpc : Continuous p := (continuous_io A).prodMk continuous_const
  have hK' : IsCompact (p '' (K ×ˢ K)) := (hK.prod hK).image hpc
  have hae : ∀ᵐ x ∂μ, p x ∈ p '' (K ×ˢ K) := by
    rw [hμ, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (hXm.prod hXm)] with x hx
    exact ⟨x, Set.prod_mono hXK hXK hx, rfl⟩

  set M : Submodule ℂ (WO (dblSp A) W → ℂ) := Submodule.span ℂ
    {φ | ∃ f₁ f₂, IsThetaFunO ψ A W f₁ ∧ IsThetaFunO ψ A W f₂ ∧ φ = delta A W f₁ f₂} with hM
  have h83 : (∀ g ∈ M, IsThetaFunO ψ (dblSp A) W g) ∧ (∀ g ∈ M, ∀ w, heisO ψ (dblSp A) W w g ∈ M) ∧
      ∀ f, IsThetaFunO ψ (dblSp A) W f → GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.UnifLimit M f := GlobalTheory.T.doublingMap_span_dense_heisenbergStable D ψ A W hom.std
  obtain ⟨hMθ, hMh, hMlim⟩ := h83

  have hintθ : ∀ g, IsThetaFunO ψ (dblSp A) W g → Integrable (fun x => c x * omh (p x) g 0) μ := fun g hg =>
    hint _ (hcc.mul ((homh.om_cont g hg 0).comp hpc))

  have hup : ∀ f, IsThetaFunO ψ A W f → ∫ g, thetaKO om g h f * u g ∂(m.restrict X) = 0 := fun f hf => by
    have hinv : ∀ γ ∈ GQ A, ∀ g, thetaKO om (γ * g) h f * u (γ * g) = thetaKO om g h f * u g := fun γ hγ g => by
      rw [thetaKO_rat hom hf h γ hγ g, hui γ hγ g]
    rw [← GlobalTheory.ChainOnto.integral_autMeasure_eq_setIntegral D A m X hm hX (fun g => thetaKO om g h f * u g) hinv
      ((continuous_thetaKO hom hf h).mul hu).aestronglyMeasurable]
    exact hno f hf h
  have hkill : ∀ g ∈ M, ∫ x, c x * omh (p x) g 0 ∂μ = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f₁, f₂, h₁, h₂, rfl⟩ := hx
      have e : ∀ x : GA D A × GA D A, c x * omh (p x) (delta A W f₁ f₂) 0 =
          (thetaKO om x.1 h f₁ * u x.1) * conj (thetaKO om x.2 h f₂ * u x.2) := by
        rintro ⟨x₁, x₂⟩
        have t := ((hTC f₁ f₂ h₁ h₂).2 x₁ x₂ h).2
        have hz : (χW (detA A x₂) : ℂ) ≠ 0 := Circle.coe_ne_zero _
        change c (x₁, x₂) * thetaKO omh (io A (x₁, x₂)) h (delta A W f₁ f₂) = _
        rw [t, Circle.coe_inv, hc]
        simp only [map_mul]
        field_simp
      simp_rw [e]
      rw [hμ, integral_prod_mul (fun g => thetaKO om g h f₁ * u g) (fun g => conj (thetaKO om g h f₂ * u g)),
        hup f₁ h₁, zero_mul]
    | zero => simp
    | add x y hx hy ihx ihy =>
      simp only [map_add (f := _), Pi.add_apply, mul_add]
      rw [integral_add (hintθ x (hMθ x hx)) (hintθ y (hMθ y hy)), ihx, ihy, add_zero]
    | smul a x hx ih =>
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_left_comm _ a]
      rw [integral_const_mul, ih, mul_zero]
  exact _root_.GlobalTheory.AvgKill.average_kills_theta D ψ (dblSp A) W 1 χW omh homh (GA D A × GA D A) μ p c (p '' (K ×ˢ K)) hpc hcc ⟨C * C, hcb⟩ hK'
    hae M hMθ hMh hkill φ hφ (hMlim φ hφ)

end GlobalTheory.Core.Rk.Kill

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause lagr evZero)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.SwSecMem

variable {D : D7} (A B : HSp D) (omh : WRep (dblSp A) B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B))

def intSub : Submodule ℂ (WO (dblSp A) B → ℂ) where
  carrier := {f | ∀ g : GA D (dblSp A), IntegrableOn (fun w => omh (g, 1) f (lagr A B w)) 𝓕 ν}
  zero_mem' g := by
    simp only [map_zero, Pi.zero_apply]
    exact integrableOn_zero
  add_mem' {f f'} hf hf' g := by
    simp only [map_add (f := _), Pi.add_apply]
    exact Integrable.add (hf g) (hf' g)
  smul_mem' c f hf g := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    exact Integrable.const_mul (hf g) c

def swLin : intSub A B omh ν 𝓕 →ₗ[ℂ] (GA D (dblSp A) → ℂ) where
  toFun f := swSec A B omh ν 𝓕 f
  map_add' f f' := by
    funext g
    simp only [swSec, evZero, Submodule.coe_add, map_add (f := _), Pi.add_apply]
    exact integral_add (f.2 g) (f'.2 g)
  map_smul' c f := by
    funext g
    simp only [swSec, evZero, Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

theorem swSec_mul (φ : WO (dblSp A) B → ℂ) (g k : GA D (dblSp A)) :
    swSec A B omh ν 𝓕 φ (g * k) = swSec A B omh ν 𝓕 (omh (k, 1) φ) g := by
  have : ((g * k, 1) : GA D (dblSp A) × GA D B) = (g, 1) * (k, 1) := by simp
  simp only [swSec]
  rw [this, map_mul, Module.End.mul_apply]

theorem swSec_mem_degPS : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → ∀ a : GL (Fin A.rank) (AE D), IsKFinVec omh (Khat A a) φ → swSec A B omh ν 𝓕 φ ∈ degPS A a χB⁻¹ (sZero A B) := by
  intro hW D ψ A B χB omh hω ν 𝓕 hν φ hφ a hK
  have hint : ∀ f, IsThetaFunO ψ (dblSp A) B f → f ∈ intSub A B omh ν 𝓕 := fun f hf g =>
    (_root_.GlobalTheory.Core.Rk.IP.swSec_integrable_continuous D ψ A B χB omh hω ν 𝓕 hν _ (hω.om_pres (g, 1) f hf)).1
  refine (mem_degPS A a).2 ⟨_root_.GlobalTheory.Core.Rk.SWLaw.swSec_law hW D ψ A B χB omh hω ν 𝓕 hν φ hφ,
    (_root_.GlobalTheory.Core.Rk.IP.swSec_integrable_continuous D ψ A B χB omh hω ν 𝓕 hν φ hφ).2, ?_⟩
  let S := Submodule.span ℂ {f : WO (dblSp A) B → ℂ | ∃ k ∈ Khat A a, f = omh (k, 1) φ}
  haveI : FiniteDimensional ℂ S := hK
  have hS : S ≤ intSub A B omh ν 𝓕 := Submodule.span_le.2 (by
    rintro _ ⟨k, -, rfl⟩
    exact hint _ (hω.om_pres _ _ hφ))
  refine isKFinite_iff.2 ⟨LinearMap.range ((swLin A B omh ν 𝓕).comp (Submodule.inclusion hS)), inferInstance,
    fun k hk => ⟨⟨omh (k, 1) φ, Submodule.subset_span ⟨k, hk, rfl⟩⟩, funext fun g => ?_⟩⟩
  exact (swSec_mul A B omh ν 𝓕 φ g k).symm

end GlobalTheory.SwSecMem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

namespace GlobalTheory.FrameGlob

open Matrix

theorem exists_gl_of_lattices {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (Λ₁ Λ₂ : Submodule 𝒪[k] (n → k)) (h₁ : Λ₁.IsFullLattice k)
    (h₂ : Λ₂.IsFullLattice k) : ∃ g : GL n k, ∀ z, z ∈ Λ₁ ↔ g.val *ᵥ z ∈ Λ₂ := by
  have key : ∀ (Λ : Submodule 𝒪[k] (n → k)), Λ.IsFullLattice k →
      ∃ e : (Fin (Fintype.card n) → k) ≃ₗ[k] (n → k), ∀ y, e y ∈ Λ ↔ ∀ i, y i ∈ 𝒪[k] := by
    intro Λ hΛ
    let : Module.Free 𝒪[k] Λ := Submodule.IsLattice.free k Λ
    let : Module.Finite 𝒪[k] Λ := Submodule.IsLattice.finite k Λ
    let b := Module.finBasisOfFinrankEq 𝒪[k] Λ
      ((Submodule.IsFullLattice.finrank_eq k Λ).trans (Module.finrank_fintype_fun_eq_card k))
    let b' := b.extendOfIsFullLattice k
    have hkey : ∀ c : Fin (Fintype.card n) → 𝒪[k],
        b'.equivFun.symm (fun i => (c i : k)) = ((∑ i, c i • b i : Λ) : n → k) := by
      intro c
      rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Module.Basis.extendOfIsFullLattice_apply]
      rfl
    refine ⟨b'.equivFun.symm, fun y => ⟨fun h => ?_, fun h => ?_⟩⟩
    · have h1 := hkey (b.repr ⟨_, h⟩)
      rw [b.sum_repr] at h1
      rw [← b'.equivFun.symm.injective h1]
      exact fun i => (b.repr ⟨_, h⟩ i).2
    · have h1 := hkey fun i => ⟨y i, h i⟩
      have h2 : b'.equivFun.symm y = _ := h1
      rw [h2]
      exact Subtype.property _
  obtain ⟨e₁, he₁⟩ := key Λ₁ h₁
  obtain ⟨e₂, he₂⟩ := key Λ₂ h₂
  let φ : (n → k) ≃ₗ[k] (n → k) := e₁.symm.trans e₂
  refine ⟨⟨LinearMap.toMatrix' φ.toLinearMap, LinearMap.toMatrix' φ.symm.toLinearMap, ?_, ?_⟩, fun z => ?_⟩
  · rw [← LinearMap.toMatrix'_mul]
    have : φ.toLinearMap * φ.symm.toLinearMap = LinearMap.id := by ext; simp
    rw [this, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_mul]
    have : φ.symm.toLinearMap * φ.toLinearMap = LinearMap.id := by ext; simp
    rw [this, LinearMap.toMatrix'_id]
  · show z ∈ Λ₁ ↔ LinearMap.toMatrix' φ.toLinearMap *ᵥ z ∈ Λ₂
    rw [LinearMap.toMatrix'_mulVec]
    have h := he₁ (e₁.symm z)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.coe_coe, ← he₂]
    rfl

end GlobalTheory.FrameGlob

namespace GlobalTheory.FrameGlob

open Matrix

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mem_idAt (p : SplitPt D k) : p.e ∈ idAt D (· = p.v) := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  obtain ⟨hee, hec, -⟩ := p.split
  refine ((_root_.GlobalTheory.FinPl.placeIdem_acts D p.v ε hε).1 p.e).2 ?_
  rw [← hsum, add_mul, hee, mul_comm (cA D p.e), hec, add_zero]

theorem sec_eq_mul (p : SplitPt D k) (a : k) : p.sec a = p.e * p.sec a := by
  have h := p.sec_pr (p.sec a)
  rwa [p.pr_sec] at h

theorem sec_mem_idAt (p : SplitPt D k) (a : k) : p.sec a ∈ idAt D (· = p.v) := by
  rw [sec_eq_mul]
  exact Ideal.mul_mem_right _ _ (e_mem_idAt p)

variable {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem mt_gl_vec {p : SplitPt D k} (β : Frame p S n) (g : GL n k) (z : n → k) :
    mt S (β.gl g) *ᵥ (fun i => p.sec ((β.b *ᵥ z) i)) = fun i => p.sec ((β.b *ᵥ (g.val *ᵥ z)) i) := by
  funext i
  set m := mt S (β.gl g)
  set y : Fin S.rank → AE D := fun i => p.sec ((β.b *ᵥ z) i)
  have he : (m *ᵥ y) i = p.e * (m *ᵥ y) i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show m i j * p.sec _ = p.e * (m i j * p.sec _)
    conv_lhs => rw [sec_eq_mul]
    ring
  have hpr : p.pr ((m *ᵥ y) i) = ((m.map p.pr) *ᵥ (β.b *ᵥ z)) i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, y, p.pr_sec]
  rw [he, ← p.sec_pr, hpr, β.gl_mat, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.mul_assoc, β.b'b, Matrix.mul_one]

theorem mt_gl_off {p : SplitPt D k} (β : Frame p S n) (g : GL n k) (y : Fin S.rank → AE D)
    (hy : ∀ i, y i ∈ idAt D (· ≠ p.v)) : mt S (β.gl g) *ᵥ y = y := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  have h0 : (mt S (β.gl g) - 1) *ᵥ y = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← β.gl_supp g i j, hsum]
    calc algebraMap (AF D.host.F) (AE D) ε * (mt S (β.gl g) - 1) i j * y j
        = (mt S (β.gl g) - 1) i j * (algebraMap (AF D.host.F) (AE D) ε * y j) := by ring
      _ = 0 := by rw [(_root_.GlobalTheory.FinPl.placeIdem_acts D p.v ε hε).2 _ (hy j), mul_zero]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
  exact h0

theorem main : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (L : Lat S)
    (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → Λ.IsFullLattice k →
    ∃ M : Lat S, IsSelfDualC S M ∧ β.IsLat M Λ ∧ latV S M (· ≠ p.v) = latV S L (· ≠ p.v) := by
  intro D k _ _ _ _ p S n _ _ β L Λ hL hΛ
  obtain ⟨Λ₁, hΛ₁, hLat₁, -⟩ := _root_.GlobalTheory.FinPl.FrameLat.exists_lat D k p S n β L hL
  have hFull₁ : Λ₁.IsFullLattice k := by
    refine { toIsLattice := hΛ₁, span_eq_top := eq_top_iff.mpr fun x _ => ?_ }
    obtain ⟨m, s, c, hs, hc, -⟩ := FrameLat.exists_gen (p := p) hL
    have hx := congrArg (β.b' *ᵥ ·) (hc (β.b *ᵥ x))
    simp only [Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec, Matrix.mulVec_sum,
      Matrix.mulVec_smul] at hx
    rw [hx]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    apply (hLat₁ _).2
    rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
    exact FrameLat.sec_inc_mem (p := p) (hs l)
  obtain ⟨g, hg⟩ := exists_gl_of_lattices Λ₁ Λ hFull₁ hΛ
  obtain ⟨M, hM, hMv⟩ := (_root_.GlobalTheory.FinPl.GlobImage.glob D S L hL).1 (β.gl g)
  have supp : ∀ (N : Lat S), IsSelfDualC S N → ∀ y, y ∈ latV S N (· ≠ p.v) → ∀ i, y i ∈ idAt D (· ≠ p.v) :=
    fun N hN y hy => (((_root_.GlobalTheory.FinPl.localComponents D (· ≠ p.v)).2 S).2.2.2 N y hN.1 |>.1 hy).1
  refine ⟨M, hM, fun x => ?_, ?_⟩
  · have hx : x = g.val *ᵥ ((g⁻¹).val *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [hx, ← hg, hLat₁, hMv (· = p.v) _ (fun i => sec_mem_idAt p _), mt_gl_vec]
  · ext y
    constructor
    · intro hy
      have hs := supp M hM y hy
      rw [← mt_gl_off β g y hs] at hy
      exact (hMv (· ≠ p.v) y hs).2 hy
    · intro hy
      have hs := supp L hL y hy
      have h := (hMv (· ≠ p.v) y hs).1 hy
      rwa [mt_gl_off β g y hs] at h

end GlobalTheory.FrameGlob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstTermExistenceOfUniversal
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.FirstTermCompare

variable {D : D7}

theorem hasIw_of_good {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {l : Lvl T} (hl : l.Good) :
    HasIw d l.K ∧ IsCompact (l.K : Set (GA D T)) := by
  have h := _root_.GlobalTheory.RegSch.good_level_conj_stab D T T₀ r d l.c hl.2.2
    (GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer D T T₀ r d l.c GlobalTheory.Core.Rk.IP.Model.isSplit_two hl.2.2) l hl
  exact ⟨h.1, h.2.1⟩

end GlobalTheory.RegSch.FirstTermCompare

end
end

