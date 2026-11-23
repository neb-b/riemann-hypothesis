module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAvgLinear
section
namespace I195MixedCoordinates_5faa2c9cd849d5d53bf59d46

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_5faa2c9cd849d5d53bf59d46

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped GlobalTheory.HalfAverage

noncomputable section

namespace GlobalTheory.HalfLinForm


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem halfAvg_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, ∀ H : AddSubgroup (Mx D T.rank ρ), (∀ x, x ∈ H ↔ ∀ i j, cA D e * x i j = x i j) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsAddHaarMeasure], ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, ∀ f, IsThetaFunO ψ S T f → ℓ f = ∫ x : H, ℓ₀ ((_root_.I195MixedCoordinates_5faa2c9cd849d5d53bf59d46.source d) T ψ μ 𝓕 f x.1) ∂ν := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ H hH _ _ ν _
  haveI : IsTopologicalAddGroup (Mx D T.rank ρ) := GlobalTheory.HalfAverage.tagMx _ _
  haveI : T2Space (Mx D T.rank ρ) := GlobalTheory.HalfAverage.t2Mx _ _
  haveI : T2Space H := inferInstance
  haveI : R1Space H := T2Space.r1Space
  haveI : ContinuousSub (Mx D T.rank ρ) := by first | exact IsTopologicalAddGroup.to_continuousSub | exact inferInstance
  have hHc : IsClosed (H : Set (Mx D T.rank ρ)) := by
    have : (H : Set (Mx D T.rank ρ)) = ⋂ i, ⋂ j, {t : Mx D T.rank ρ | cA D e * t i j = t i j} := by
      ext t; simp only [SetLike.mem_coe, hH, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
        ((continuous_apply j).comp (continuous_apply i))

  have hint : ∀ f, IsThetaFunO ψ S T f → Integrable (fun x : H => ℓ₀ ((_root_.I195MixedCoordinates_5faa2c9cd849d5d53bf59d46.source d) T ψ μ 𝓕 f x.1)) ν := by
    intro f hf
    obtain ⟨⟨U, hUo, hU⟩, K, hK, hKs⟩ := GlobalTheory.MixHalf.mixS_half D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he f hf
    have hKc : IsCompact ((Subtype.val : H → Mx D T.rank ρ) ⁻¹' K) :=
      hHc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hKc fun t ht => ?_)
    · refine IsLocallyConstant.continuous ?_
      rw [IsLocallyConstant.iff_eventually_eq]
      intro t
      have hn : {s : H | (s : Mx D T.rank ρ) - t ∈ U} ∈ nhds t := by
        refine IsOpen.mem_nhds (hUo.preimage (continuous_subtype_val.sub continuous_const)) ?_
        show (t : Mx D T.rank ρ) - t ∈ U
        rw [sub_self]; exact U.zero_mem
      filter_upwards [hn] with s hs
      have hsH : ∀ i j, cA D e * ((s : Mx D T.rank ρ) - t) i j = ((s : Mx D T.rank ρ) - t) i j :=
        (hH _).1 (H.sub_mem s.2 t.2)
      have h1 := hU _ hs hsH t
      rw [show (t : Mx D T.rank ρ) + ((s : Mx D T.rank ρ) - t) = s by abel] at h1
      change ℓ₀ (_root_.I195MixedCoordinates_41a545e47d405c9816345b57.source d T ψ μ 𝓕 f s) = ℓ₀ (_root_.I195MixedCoordinates_41a545e47d405c9816345b57.source d T ψ μ 𝓕 f t)
      rw [h1]
    · by_contra hne
      exact ht (hKs _ ((hH _).1 t.2) fun h0 => hne (by
        change ℓ₀ (_root_.I195MixedCoordinates_41a545e47d405c9816345b57.source d T ψ μ 𝓕 f t) = 0
        rw [h0, map_zero]))

  have madd : ∀ f g : WO S T → ℂ,
      (∀ x w, IntegrableOn (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0) 𝓕 μ) →
      (∀ x w, IntegrableOn (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) g)) 0) 𝓕 μ) →
      ∀ x, (_root_.I195MixedCoordinates_5faa2c9cd849d5d53bf59d46.source d) T ψ μ 𝓕 (f + g) x = (_root_.I195MixedCoordinates_5faa2c9cd849d5d53bf59d46.source d) T ψ μ 𝓕 f x + (_root_.I195MixedCoordinates_5faa2c9cd849d5d53bf59d46.source d) T ψ μ 𝓕 g x := by
    intro f g hf hg x
    funext w
    have h1 := hf x w
    have h2 := hg x w
    change (∫ a in 𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) (f + g))) 0 ∂μ) = (∫ a in 𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0 ∂μ) + (∫ a in 𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) g)) 0 ∂μ)
    simp only [HypDec.integrandS_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
    exact integral_add h1 h2
  have msmul : ∀ (c : ℂ) (f : WO S T → ℂ) x, (_root_.I195MixedCoordinates_5faa2c9cd849d5d53bf59d46.source d) T ψ μ 𝓕 (c • f) x = c • (_root_.I195MixedCoordinates_5faa2c9cd849d5d53bf59d46.source d) T ψ μ 𝓕 f x := by
    intro c f x
    funext w
    change (∫ a in 𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) (c • f))) 0 ∂μ) = c • (∫ a in 𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0 ∂μ)
    simp only [HypDec.integrandS_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]
  let P : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {f | (∀ x w, IntegrableOn
          (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0) 𝓕 μ) ∧
        Integrable (fun x : H => ℓ₀ ((_root_.I195MixedCoordinates_5faa2c9cd849d5d53bf59d46.source d) T ψ μ 𝓕 f x.1)) ν}
      add_mem' := by
        rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
        refine ⟨fun x w => ?_, ?_⟩
        · have h1 := hf1 x w
          have h2 := hg1 x w
          simp only [HypDec.integrandS_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
          exact h1.add h2
        · refine (hf2.add hg2).congr (Filter.Eventually.of_forall fun x => ?_)
          simp only [Pi.add_apply, madd f g hf1 hg1, map_add (f := _)]
      zero_mem' := by
        have h0 : ∀ x, (_root_.I195MixedCoordinates_5faa2c9cd849d5d53bf59d46.source d) T ψ μ 𝓕 (0 : WO S T → ℂ) x = 0 := fun x => by
          simpa using msmul 0 0 x
        refine ⟨fun x w => ?_, ?_⟩
        · simp only [HypDec.integrandS_eq, Pi.zero_apply, mul_zero]; exact integrableOn_zero
        · simp only [h0, map_zero]; exact integrable_zero _ _ _
      smul_mem' := by
        rintro c f ⟨hf1, hf2⟩
        refine ⟨fun x w => ?_, ?_⟩
        · have h1 := hf1 x w
          simp only [HypDec.integrandS_eq, Pi.smul_apply, smul_eq_mul] at h1 ⊢
          simp only [mul_left_comm _ c]
          exact h1.const_mul c
        · refine (hf2.const_mul c).congr (Filter.Eventually.of_forall fun x => ?_)
          simp only [msmul, map_smul, smul_eq_mul] }
  have hP : ∀ f, IsThetaFunO ψ S T f → f ∈ P := fun f hf =>
    ⟨fun x w => d.integrableOn_mixS hψ.1.1 hμ hf x w, hint f hf⟩
  let L : P →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x : H, ℓ₀ ((_root_.I195MixedCoordinates_5faa2c9cd849d5d53bf59d46.source d) T ψ μ 𝓕 f.1 x.1) ∂ν
      map_add' := by
        rintro ⟨f, hf1, hf2⟩ ⟨g, hg1, hg2⟩
        show ∫ x : H, ℓ₀ ((_root_.I195MixedCoordinates_5faa2c9cd849d5d53bf59d46.source d) T ψ μ 𝓕 (f + g) x.1) ∂ν =
          ∫ x : H, ℓ₀ ((_root_.I195MixedCoordinates_5faa2c9cd849d5d53bf59d46.source d) T ψ μ 𝓕 f x.1) ∂ν + ∫ x : H, ℓ₀ ((_root_.I195MixedCoordinates_5faa2c9cd849d5d53bf59d46.source d) T ψ μ 𝓕 g x.1) ∂ν
        rw [← integral_add hf2 hg2]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [madd f g hf1 hg1, map_add (f := _)]
      map_smul' := by
        rintro c ⟨f, hf1, hf2⟩
        show ∫ x : H, ℓ₀ ((_root_.I195MixedCoordinates_5faa2c9cd849d5d53bf59d46.source d) T ψ μ 𝓕 (c • f) x.1) ∂ν = c • ∫ x : H, ℓ₀ ((_root_.I195MixedCoordinates_5faa2c9cd849d5d53bf59d46.source d) T ψ μ 𝓕 f x.1) ∂ν
        rw [smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [msmul, map_smul, smul_eq_mul] }
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend L
  exact ⟨ℓ, fun f hf => LinearMap.congr_fun hℓ ⟨f, hP f hf⟩⟩

end GlobalTheory.HalfLinForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlaceStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasIwasawaDecomposition_doubled_split_place : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ v : FinPl D, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → HasIwasawa D.sp.cm.sig (dblSp A).gram (KFin D.sp.cm.sig (dblSp A).gram L v) := by
  first | exact @GlobalTheory.Core.Rk.IwSplit.hasIwasawa_split | exact GlobalTheory.Core.Rk.IwSplit.hasIwasawa_split | (intros; apply GlobalTheory.Core.Rk.IwSplit.hasIwasawa_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharValueInertPlaceAndSegment
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.InertValue

theorem npow_eq_zpow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (N : ℕ)
    (hN : Ideal.absNorm w.asIdeal = N ^ 2) (k : ℤ) (z : ℂ) (hz : 2 * z = k) :
    GlobalTheory.LFun.npow w z = (N : ℂ) ^ k := by
  have hlog : (Complex.log (N : ℂ) * ((2 : ℕ) : ℂ)).im = 0 := by
    rw [Complex.mul_im, Complex.log_im, Complex.log_re, ← Complex.ofReal_natCast N,
      Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)]
    simp
  rw [GlobalTheory.LFun.npow, hN, Nat.cast_pow, ← Complex.cpow_natCast (N : ℂ) 2,
    ← Complex.cpow_mul (x := (N : ℂ)) (y := ((2 : ℕ) : ℂ)) (z := z) (by rw [hlog]; linarith [Real.pi_pos]) (by rw [hlog]; linarith [Real.pi_pos])]
  rw [show ((2 : ℕ) : ℂ) * z = (k : ℂ) by rw [← hz]; norm_num, Complex.cpow_intCast]

theorem range_reflect (t : ℕ) : (Multiset.range t).map (fun i => t - 1 - i) = Multiset.range t := by
  refine (Multiset.Nodup.ext ?_ (Multiset.nodup_range t)).2 fun a => ?_
  · refine (Multiset.nodup_range t).map_on fun x hx y hy h => ?_
    rw [Multiset.mem_range] at hx hy
    omega
  · simp only [Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨b, hb, rfl⟩; omega
    · intro ha; exact ⟨t - 1 - a, by omega, by omega⟩

end GlobalTheory.ChainOnto.InertValue


open GlobalTheory.ChainOnto.InertValue in
theorem GlobalTheory.ChainOnto.val_seg_of_isInertAt : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → Formalism.L2.Theta.ResEta D χ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsInertAt D.host.F D.host.E v w → UnrAt χ w → val (F := D.host.F) χ w = (-1) ^ n ∧ ∀ (qu z : ℂˣ) (t : ℕ), (qu : ℂ) = qV D.host.F v → seg w z t = (GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str qu t).map (z * ·) := by
  intro D χ n _ hres v w hwv hw hu
  refine ⟨GlobalTheory.LFun.ResEta.val_of_isInertAt D.sp.cm.deg2 hres hw hu, ?_⟩
  intro qu z t hqu
  have hN : Ideal.absNorm w.asIdeal = qV D.host.F v ^ 2 := GlobalTheory.LFun.InertChart.absNorm_eq D.sp.cm.deg2 hw
  rw [GlobalTheory.LFun.seg, GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str, Int.toNat_natCast, Multiset.map_map, Finset.range_val]
  conv_lhs => rw [← range_reflect t, Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Multiset.mem_range] at hi
  simp only [Function.comp_apply]
  congr 1
  refine Units.ext ?_
  rw [GlobalTheory.LFun.coe_npowU, Units.val_zpow_eq_zpow_val, hqu]
  refine npow_eq_zpow w _ hN _ _ ?_
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorMoveAcrossInvariantBilinear
section
noncomputable section

namespace GlobalTheory.ChainOnto

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

section Move

variable {G : Type} [Group G] {K : Subgroup G}

theorem mem_doubleCoset_inv_iff {a g : G} :
    g⁻¹ ∈ DoubleCoset.doubleCoset a (K : Set G) K ↔ g ∈ DoubleCoset.doubleCoset a⁻¹ (K : Set G) K := by
  simp only [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨h, hh, k, hk, e⟩
    refine ⟨k⁻¹, K.inv_mem hk, h⁻¹, K.inv_mem hh, ?_⟩
    have hg : g = (h * a * k)⁻¹ := by rw [← e, inv_inv]
    rw [hg]
    group
  · rintro ⟨h, hh, k, hk, e⟩
    refine ⟨k⁻¹, K.inv_mem hk, h⁻¹, K.inv_mem hh, ?_⟩
    rw [e]
    group

theorem dosetInd_comp_inv (a : G) : (fun g => dosetInd ℂ K a g⁻¹) = dosetInd ℂ K a⁻¹ := by
  funext g
  simp only [dosetInd]
  by_cases h : g ∈ DoubleCoset.doubleCoset a⁻¹ (K : Set G) K
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (mem_doubleCoset_inv_iff.mpr h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (mem_doubleCoset_inv_iff.mp h'))]

theorem out_mem_doubleCoset_iff (a : G) (c : G ⧸ K) :
    c.out ∈ DoubleCoset.doubleCoset a (K : Set G) K ↔ ∃ k ∈ K, c = ((k * a : G) : G ⧸ K) := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨h, hh, k, hk, e⟩
    refine ⟨h, hh, ?_⟩
    have hc : ((c.out : G) : G ⧸ K) = c := QuotientGroup.out_eq' c
    rw [← hc, e, QuotientGroup.eq]
    have hx : (h * a * k)⁻¹ * (h * a) = k⁻¹ := by group
    rw [hx]
    exact K.inv_mem hk
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K (k * a)
    exact ⟨k, hk, h, h.2, hh⟩

private theorem finite_left_cosets_of_isCommensurated (hK : IsCommensurated K) (a : G) :
    {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)}.Finite := by
  have h := hK a
  set H := K.map (MulAut.conj a).toMonoidHom with hH
  have hfin : Finite (K ⧸ H.subgroupOf K) := by
    unfold Subgroup.relIndex at h
    exact Subgroup.index_ne_zero_iff_finite.mp h
  apply (Set.finite_range (fun q : K ⧸ H.subgroupOf K => ((((q.out : K) : G) * a : G) : G ⧸ K))).subset
  rintro c ⟨k, hk, rfl⟩
  obtain ⟨h', hh'⟩ := QuotientGroup.mk_out_eq_mul (H.subgroupOf K) (⟨k, hk⟩ : K)
  refine ⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩
  simp only
  rw [hh', QuotientGroup.eq]
  have hm : ((h' : K) : G) ∈ H := Subgroup.mem_subgroupOf.mp h'.2
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hm
  have hy' : ((h' : K) : G) = a * y * a⁻¹ := by
    rw [← hyeq]
    simp [MulAut.conj_apply]
  have hx : ((((⟨k, hk⟩ : K) * (h' : K) : K) : G) * a)⁻¹ * (k * a) = y⁻¹ := by
    rw [Subgroup.coe_mul, hy']
    simp only [Subgroup.coe_mk]
    group
  rw [hx]
  exact K.inv_mem hy

theorem finsum_dosetInd_out (hK : IsCommensurated K) (a : G) :
    ∑ᶠ c : G ⧸ K, dosetInd ℂ K a c.out = (Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} : ℂ) := by
  classical
  set S := {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} with hSdef
  have hS : S.Finite := finite_left_cosets_of_isCommensurated hK a
  have hind : ∀ c : G ⧸ K, dosetInd ℂ K a c.out = S.indicator (fun _ => (1 : ℂ)) c := by
    intro c
    simp only [dosetInd, Set.indicator_apply, out_mem_doubleCoset_iff, hSdef, Set.mem_setOf_eq, Pi.one_apply]
  rw [finsum_congr hind, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  have hcard : Nat.card S = hS.toFinset.card := Nat.card_eq_card_finite_toFinset hS
  exact_mod_cast hcard.symm

private theorem apply_eq_of_mem_fixed {G V : Type} [Group G] {K : Subgroup G} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {v : V} (hv : v ∈ fixed ρ K) {k : G} (hk : k ∈ K) : ρ k v = v := by
  have h : ∀ h : K, ρ h v = ((1 : K →* ℂˣ) h : ℂ) • v := hv
  simpa using h ⟨k, hk⟩

private theorem invariant_pairing_doubleCoset_eq {G U X X' : Type} [Group G] {K : Subgroup G} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    (π : Representation ℂ G U) (ρ : Representation ℂ G X) (b : U →ₗ[ℂ] X →ₗ[ℂ] X')
    (hb : ∀ g u y, b (π g u) (ρ g y) = b u y) {u : U} (hu : u ∈ fixed π K) {y : X} (hy : y ∈ fixed ρ K)
    {a w : G} (hw : w ∈ DoubleCoset.doubleCoset a (K : Set G) K) : b (π w u) y = b (π a u) y := by
  obtain ⟨k, hk, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hw
  have hu' : π k' u = u := apply_eq_of_mem_fixed π hu hk'
  have hy' : ρ k⁻¹ y = y := apply_eq_of_mem_fixed ρ hy (K.inv_mem hk)
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hu']
  calc b (π k (π a u)) y = b (π k (π a u)) (ρ k (ρ k⁻¹ y)) := by rw [Representation.self_inv_apply]
    _ = b (π a u) (ρ k⁻¹ y) := hb k _ _
    _ = b (π a u) y := by rw [hy']

private theorem pairing_heckeVec_dosetInd_eq_card_smul {G U X X' : Type} [Group G] {K : Subgroup G} (hK : IsCommensurated K)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    (π : Representation ℂ G U) (ρ : Representation ℂ G X) (b : U →ₗ[ℂ] X →ₗ[ℂ] X')
    (hb : ∀ g u y, b (π g u) (ρ g y) = b u y) {u : U} (hu : u ∈ fixed π K) {y : X} (hy : y ∈ fixed ρ K)
    (r : ℂ) (a : G) :
    b (heckeVec π K (r • dosetInd ℂ K a) u) y =
      (r * (Nat.card {c : G ⧸ K // ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} : ℂ)) • b (π a u) y := by
  classical
  have hS := finite_left_cosets_of_isCommensurated hK a
  have hind : ∀ c : G ⧸ K, c ∉ {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)} → dosetInd ℂ K a c.out = 0 := by
    intro c hc
    simp only [dosetInd]
    exact Set.indicator_of_notMem (fun h => hc ((out_mem_doubleCoset_iff a c).mp h)) _
  rw [← LinearMap.flip_apply b (heckeVec π K (r • dosetInd ℂ K a) u) y]
  unfold heckeVec
  have hsupp : (Function.support fun c : G ⧸ K => (r • dosetInd ℂ K a) c.out • π c.out u).Finite := by
    apply hS.subset
    intro c hc
    by_contra hcS
    apply hc
    simp [hind c hcS]
  rw [map_finsum _ hsupp]
  have hterm : ∀ c : G ⧸ K, (b.flip y) ((r • dosetInd ℂ K a) c.out • π c.out u) =
      (r * dosetInd ℂ K a c.out) • b (π a u) y := by
    intro c
    rw [map_smul, LinearMap.flip_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hc : c ∈ {c : G ⧸ K | ∃ k ∈ K, c = ((k * a : G) : G ⧸ K)}
    · rw [invariant_pairing_doubleCoset_eq π ρ b hb hu hy ((out_mem_doubleCoset_iff a c).mpr hc)]
    · simp [hind c hc]
  rw [finsum_congr hterm, ← finsum_smul, ← mul_finsum, finsum_dosetInd_out hK a]

private theorem comp_inv_mem_hecke {G : Type} [Group G] {K : Subgroup G} {ψ : G → ℂ} (hψ : ψ ∈ Hecke ℂ K) :
    (fun g => ψ g⁻¹) ∈ Hecke ℂ K := by
  classical
  have h : IsBiInv K ψ ∧ FinDosetSupp K ψ := hψ
  obtain ⟨hbi, S, hS⟩ := h
  show IsBiInv K (fun g => ψ g⁻¹) ∧ FinDosetSupp K (fun g => ψ g⁻¹)
  refine ⟨fun a b g => ?_, S.image (fun s => s⁻¹), fun g hg => ?_⟩
  · have e := hbi b⁻¹ a⁻¹ g⁻¹
    simp only [Subgroup.coe_inv] at e
    simp only
    rw [← e]
    congr 1
    group
  · obtain ⟨s, hs, a, b, e⟩ := hS g⁻¹ hg
    refine ⟨s⁻¹, Finset.mem_image_of_mem _ hs, b⁻¹, a⁻¹, ?_⟩
    have hg' : g = (↑a * s * ↑b)⁻¹ := by rw [← e, inv_inv]
    rw [hg', Subgroup.coe_inv, Subgroup.coe_inv]
    group

end Move

theorem heckeVec_move : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → CosetSym K →
    ∀ (U X X' : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    (π : Representation ℂ G U) (ρ : Representation ℂ G X) (b : U →ₗ[ℂ] X →ₗ[ℂ] X'),
    (∀ g u y, b (π g u) (ρ g y) = b u y) → ∀ f ∈ fixed π K, ∀ x ∈ fixed ρ K, ∀ φ ∈ Hecke ℂ K,
    (fun g => φ g⁻¹) ∈ Hecke ℂ K ∧ b (heckeVec π K φ f) x = b f (heckeVec ρ K (fun g => φ g⁻¹) x) := by
  intro G _ K hK hsym U X X' _ _ _ _ _ _ π ρ b hb f hf x hx φ hφ
  refine ⟨comp_inv_mem_hecke hφ, ?_⟩
  refine hecke_induction (p := fun ψ => b (heckeVec π K ψ f) x = b f (heckeVec ρ K (fun g => ψ g⁻¹) x))
    ?_ ?_ ?_ hφ
  · simp [heckeVec]
  · intro ψ hψ ψ' hψ' e e'
    have hsum : (fun g => (ψ + ψ') g⁻¹) = (fun g => ψ g⁻¹) + (fun g => ψ' g⁻¹) := rfl
    rw [heckeVec_add hK π hψ hψ' f, hsum, heckeVec_add hK ρ (comp_inv_mem_hecke hψ) (comp_inv_mem_hecke hψ') x,
      map_add, LinearMap.add_apply, map_add, e, e']
  · intro r a
    have hc : (fun g => (r • dosetInd ℂ K a) g⁻¹) = r • dosetInd ℂ K a⁻¹ := by
      funext g
      rw [Pi.smul_apply, Pi.smul_apply, ← dosetInd_comp_inv a]
    have hb' : ∀ g y u, b.flip (ρ g y) (π g u) = b.flip y u := fun g y u => by
      rw [LinearMap.flip_apply, LinearMap.flip_apply, hb]
    rw [hc, pairing_heckeVec_dosetInd_eq_card_smul hK π ρ b hb hf hx r a, ← LinearMap.flip_apply b f (heckeVec ρ K (r • dosetInd ℂ K a⁻¹) x),
      pairing_heckeVec_dosetInd_eq_card_smul hK ρ π b.flip hb' hx hf r a⁻¹, LinearMap.flip_apply, hsym a]
    congr 1
    rw [← hb a f (ρ a⁻¹ x), Representation.self_inv_apply]

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
section
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ContDiff

namespace GlobalTheory.EisCont.CentreFinite

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isRealLine_conj (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (a : GAd σ J) :
    IsRealLine σ J fun t => a⁻¹ * γ t * a := by
  obtain ⟨w, τ, Z, hZ, hγ⟩ := hγ
  have hu : ∀ x : GArch σ J w, (GlobalTheory.Orb.archMat σ J τ x)ᴴ * J.map τ.1 * GlobalTheory.Orb.archMat σ J τ x = J.map τ.1 :=
    fun x => (archEquiv J h τ x).2
  have h1 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have u1 := hu (projArch σ J w a)
  have u2 := hu (projArch σ J w a)⁻¹
  refine ⟨w, τ, GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a), ?_,
    fun t => ?_⟩
  · generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
    generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
    generalize J.map τ.1 = Q at u1 u2 hZ ⊢
    have e1 : M'ᴴ * Q = Q * M := by
      conv_rhs => rw [← u2, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e2 : Q * M' = Mᴴ * Q := by
      conv_lhs => rw [← u1, Matrix.mul_assoc, h2, Matrix.mul_one]
    calc (M' * Z * M)ᴴ * Q + Q * (M' * Z * M) = Mᴴ * Zᴴ * (M'ᴴ * Q) + (Q * M') * Z * M := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Mᴴ * (Zᴴ * Q + Q * Z) * M := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨y, e1, e2⟩ := hγ t
    refine ⟨(projArch σ J w a)⁻¹ * y * projArch σ J w a, ?_, ?_⟩
    · show a⁻¹ * γ t * a = _
      rw [e1]
      refine GAd_ext σ J (fun u => ?_) fun v => by simp
      by_cases e : u = w
      · subst e; simp
      · simp [projArch_embArch_ne σ J e]
    · rw [map_mul, map_mul, e2]
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
      have hM : IsUnit M := ⟨⟨M, M', h2, h1⟩, rfl⟩
      rw [← Matrix.inv_eq_left_inv h1, ← Matrix.exp_conj' _ _ hM, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.EisCont.CentreFinite
end

