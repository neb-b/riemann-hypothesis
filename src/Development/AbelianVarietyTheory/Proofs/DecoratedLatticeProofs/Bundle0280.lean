module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0274
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharAnnihilatorOpenSubgroupFinPartCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.CondBound

open Filter Topology

variable (D : D7)

abbrev line : HSp D :=
  Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E)
    Formalism.BasicNotions.Examples₂.star_isIntegral 1

def o : Fin (line D).rank := ⟨0, Nat.one_pos⟩

theorem sum_line (f : Fin (line D).rank → AE D) : ∑ i, f i = f (o D) := Fin.sum_univ_one f

theorem hO_line (x y : WO (line D) (line D)) :
    hO (line D) (line D) x y = incA D ((line D).gram⁻¹ (o D) (o D)) * cA D (y (o D) (o D)) *
      incA D ((line D).gram (o D) (o D)) * x (o D) (o D) := by
  unfold hO
  simp only [sum_line]

abbrev latL : AddSubgroup (WO (line D) (line D)) :=
  latO (line D) (line D) (GlobalTheory.PlaceModel.latFrame (line D) : Set (Fin (line D).rank → D.host.E))
    (GlobalTheory.PlaceModel.latFrame (line D) : Set (Fin (line D).rank → D.host.E)) fun _ => True

theorem infPart_latL {u : WO (line D) (line D)} (hu : u ∈ latL D) : infPart D (u (o D) (o D)) = 0 := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, -, a, -, s, -, t, -, rfl⟩ := hw
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
    exact TensorProduct.zero_tmul _ _
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_apply, RingHom.map_add (f := _), hx, hy, add_zero]
  | neg x _ hx => rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

theorem infPart_r (a : Af D.host.F) : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 a)) = 0 := by
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  exact TensorProduct.zero_tmul _ _

theorem finPart_r (N : ℕ) :
    finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (N : Af D.host.F))) = finPart D (incA D (N : D.host.E)) := by
  rw [map_natCast, map_natCast]
  show (N : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = _
  rw [← map_natCast (algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)) N]
  rfl

theorem den_latL : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ latL D, M • finPart D (u (o D) (o D)) ∈ intAE D := by
  have hΛ := GlobalTheory.PlaceModel.isSelfDualC_latFrame (line D)
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := line D) (T := line D) hΛ.1.fg hΛ.1.fg
  refine ⟨M, hM, fun u hu => ?_⟩
  have h2 : toEAf D ((M : AE D) * u (o D) (o D)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [RingHom.map_mul, map_natCast]; exact hden u hu (o D) (o D)
  have h3 := GlobalTheory.PlaceDatum.finPart_mem_of_toEAf h2
  rw [RingHom.map_mul, map_natCast] at h3
  rw [nsmul_eq_mul]
  exact h3

theorem exists_compact_fin (M : ℕ) (hM : 0 < M) : ∃ K0 : Set (AE D), IsCompact K0 ∧
    ∀ z : AE D, infPart D z = 0 → M • finPart D z ∈ intAE D → z ∈ K0 := by
  obtain ⟨C, hC, hCd⟩ := GlobalTheory.SmoothForms.Cover.exists_compact_denom D M hM
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm '' ({0} ×ˢ C), (isCompact_singleton.prod hC).image hc, fun z h1 h2 => ?_⟩
  have e1 : (e z).1 = 0 := by have := (he z).1; exact this.trans h1
  have e2 : M • (e z).2 ∈ intAE D := by have := (he z).2; rw [this]; exact h2
  exact ⟨e z, Set.mk_mem_prod (Set.mem_singleton_iff.2 e1) (hCd _ e2), e.symm_apply_apply z⟩

theorem tendsto_r : Tendsto (fun n : ℕ => algebraMap (AF D.host.F) (AE D)
    (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F))) atTop (𝓝 0) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have h : Tendsto (fun n : ℕ => pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F)) atTop (𝓝 (0 : AF D.host.F)) :=
    (tendsto_const_nhds (x := (0 : Ainf D.host.F))).prodMk_nhds
      (GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele D.host.F)
  have hcont : Continuous (algebraMap (AF D.host.F) (AE D)) := by
    have hfun : (algebraMap (AF D.host.F) (AE D) : AF D.host.F → AE D) = fun t => t • (1 : AE D) := by
      funext t; exact Algebra.algebraMap_eq_smul_one t
    haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
    rw [hfun]; exact continuous_id.smul (continuous_const (y := (1 : AE D)))
  have := (hcont.tendsto 0).comp h
  rwa [map_zero] at this

theorem exists_small (C' : Set (AE D)) (hC' : IsCompact C') (U : AddSubgroup (AE D)) (hU : IsOpen (U : Set (AE D))) :
    ∃ n : ℕ, ∀ z ∈ C', algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F)) * z ∈ U := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have hev : ∀ᶠ t in 𝓝 (0 : AE D), ∀ z ∈ C', t * z ∈ U := by
    refine hC'.eventually_forall_of_forall_eventually fun z _ => ?_
    have h0 : ((0 : AE D), z).1 * ((0 : AE D), z).2 ∈ U := by rw [zero_mul]; exact U.zero_mem
    exact (continuous_mul.continuousAt (x := ((0 : AE D), z))).preimage_mem_nhds (hU.mem_nhds h0)
  exact ((tendsto_r D).eventually hev).exists

theorem isCompact_mul (c : AE D) {K : Set (AE D)} (hK : IsCompact K) : IsCompact ((fun z => c * z) '' K) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact hK.image (continuous_const.mul continuous_id)

theorem isCompact_mul_conj (c : AE D) {K : Set (AE D)} (hK : IsCompact K) :
    IsCompact ((fun z => c * cA D z) '' K) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact hK.image (continuous_const.mul (GlobalTheory.ConjAutProps.continuous_conjA D))


set_option maxHeartbeats 1000000 in
theorem annihilator_finPart_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (AE D),
    IsOpen (U : Set (AE D)) → ∃ K : Set (AE D), IsCompact K ∧ ∀ x : AE D,
      (∀ a ∈ U, infPart D a = 0 → ψ (Algebra.trace (AF D.host.F) (AE D) (x * a)) = 1) →
        ∃ k ∈ K, finPart D (x - k) = 0 := by
  intro D ψ hψ U hU
  have hΛ := GlobalTheory.PlaceModel.isSelfDualC_latFrame (line D)
  obtain ⟨M, hM, hden⟩ := den_latL D
  obtain ⟨K0, hK0c, mem0⟩ := exists_compact_fin D M hM
  have memL : ∀ u ∈ latL D, u (o D) (o D) ∈ K0 := fun u hu => mem0 _ (infPart_latL D hu) (hden u hu)
  let c0 : AE D := incA D D.host.xi0 * incA D ((line D).gram⁻¹ (o D) (o D)) * incA D ((line D).gram (o D) (o D))
  obtain ⟨n, hn⟩ := exists_small D _ (isCompact_mul_conj D c0 hK0c) U hU
  let r : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F))
  have hN : ((n.factorial : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_pos n).ne'
  refine ⟨(fun z => incA D ((n.factorial : ℕ) : D.host.E)⁻¹ * z) '' K0, isCompact_mul D _ hK0c, ?_⟩
  intro x hx
  let u : WO (line D) (line D) := Matrix.of fun _ _ => x * r
  have hu0 : u.map (infPart D) = 0 := by
    ext i j
    show infPart D (x * r) = 0
    rw [RingHom.map_mul, infPart_r, mul_zero]
  have huL : u ∈ latL D := by
    refine ((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ (line D) (line D) _ _ hψ hΛ hΛ).1 u hu0).2 fun u' hu' => ?_
    have ha : r * (c0 * cA D (u' (o D) (o D))) ∈ U := hn _ ⟨_, memL u' hu', rfl⟩
    have hai : infPart D (r * (c0 * cA D (u' (o D) (o D)))) = 0 := by
      rw [RingHom.map_mul, infPart_r, zero_mul]
    have h := hx _ ha hai
    rw [symplO, hO_line]
    convert h using 3
    show _ = x * _
    simp only [c0, u, Matrix.of_apply]
    ring
  refine ⟨_, ⟨_, memL u huL, rfl⟩, ?_⟩
  show finPart D (x - incA D ((n.factorial : ℕ) : D.host.E)⁻¹ * (x * r)) = 0
  have h1 : finPart D (incA D ((n.factorial : ℕ) : D.host.E)⁻¹) * finPart D r = 1 := by
    rw [finPart_r, ← RingHom.map_mul, ← RingHom.map_mul, inv_mul_cancel₀ hN, map_one, map_one]
  rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, mul_left_comm, h1, mul_one, sub_self]

end GlobalTheory.CondBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFiniteDatumIsSchwartzBruhatHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.ChainOnto

theorem isSBHalf_stepDatum : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Z : Finset (Pl D.host.E)) (e : AE D), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsIdemSum e Z → IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) := by
  classical
  intro D S T ΛS ΛT βS βT L χ ξ Z e hS hT _ _ he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) βS βT
  exact GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
    (GlobalTheory.PlaceDatum.exists_den_frMapO hS.1.fg hT.1.fg βS βT)
    ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ L.Pg
    (fun y => omegaG L χ y * omegaQ ∅ L.r ξ 1 y) fun y y' h => by
      rw [GlobalTheory.PlaceDatum.omegaG_congr L χ y y' h,
        GlobalTheory.PlaceDatum.omegaQ_congr ∅ L.r ξ 1 y y' fun PP hP => absurd hP (Finset.notMem_empty PP)]

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralEqSiegelEisensteinOfWeilRange
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

theorem thetaMean_eq_eis_of_weil : GlobalTheory.Published.WeilSiegelFormulaUnitary → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → 2 * A.rank < B.rank → (wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank) → ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ mH : Measure (GA D B), mH.IsHaarMeasure → ∀ φ : WO (dblSp A) B → ℂ, IsThetaFunO ψ (dblSp A) B φ → (∀ g, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧ GlobalTheory.ThetaMean.thetaMean omh mH φ = GlobalTheory.Eis.eis A (swSec A B omh ν 𝓕 φ) := by
  intro hWeil D ψ A B ha hb hwitt χB omh homh ν 𝓕 hcov mH hmH φ hφ
  have hwitt' : Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by
    rw [GlobalTheory.RallisIP.wittIdx_eq_wittIndex]; exact hwitt
  obtain ⟨-, hW2⟩ := hWeil D A B mH hmH ha hwitt'
  obtain ⟨hint, hser⟩ := hW2 ψ χB omh homh φ hφ
  refine ⟨hint, ?_⟩
  obtain ⟨-, h2⟩ := hser hb ν 𝓕 hcov
  funext g
  rw [← swSection_eq_swSec]
  exact ((h2 g).2).symm

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftWittIndexVanishing
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

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VanishingGramBoundUniformWindowAndParams
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Deg

theorem vanishingGramBound_uniformWindow_and_weightData : (VanishingGramTermsBoundWindow → ∀ c : ℝ, On {c} VanishingGramTermsBound) ∧ (VanishingGramTermsBoundParams → Led1 VanishingGramTermsBound) := by
  refine ⟨fun h c => ?_, fun h => ?_⟩
  · intro Cg cb Cu cT CT h1 h2
    obtain ⟨a, b, H⟩ := h Cg cb Cu cT CT c h1 h2
    refine ⟨max a b, fun C0 hC0 C' Cl hC' hCl D large₂ X Y hF hI u _ t r s d e => ?_⟩
    rw [Set.mem_singleton_iff] at hC0
    subst hC0
    exact H C' Cl (le_trans (le_max_left _ _) hC') (le_trans (le_max_right _ _) hCl) D large₂ X Y hF hI u t r s d e
  · intro Cg cb Cu cT CT h1 h2
    obtain ⟨a, b, H⟩ := h Cg cb Cu cT CT h1 h2
    exact ⟨max a b, fun C' Cl hC' hCl D large₂ X Y hF hI u _ t r s n d e =>
      H C' Cl (le_trans (le_max_left _ _) hC') (le_trans (le_max_right _ _) hCl) D large₂ X Y hF hI u t r s n d e⟩

end GlobalTheory.Core.Deg
end

