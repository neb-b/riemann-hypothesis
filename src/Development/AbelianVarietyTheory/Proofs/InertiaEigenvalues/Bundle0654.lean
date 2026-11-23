module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0567
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0642
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDerivativeInducedTensorForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumInnerProductFinsuppLocalCosetFamilies
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineClassFromMonodromyKernelElement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.ExtClass

theorem lift_phi_sub {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ]
    [DecidableEq μ] {η H : ℕ} {D₀ : BKDat O K l e a ι η H} {D₁ : BKDat O K l e a κ η H}
    {D₂ : BKDat O K l e a μ η H} (F : BKHom D₀ D₁) (G : BKHom D₁ D₂) (hex : IsExactTriple F.toHom G.toHom)
    {x : Vec K a κ} (hx : x ∈ D₁.Minv) (hG : G.app (D₁.phi x - x) = 0) :
    ∃ y ∈ D₀.Y, F.app y = D₁.phi x - x ∧ D₀.Mon y = 0 := by
  have hL : D₁.phi x ∈ D₁.L := D₁.phi_mem_L hx.1
  have hM : E K l e ^ η • (D₁.phi x - x) ∈ D₁.M := by
    rw [smul_sub]
    exact sub_mem (D₁.upper _ hL) (D₁.M.smul_mem (EIn l e (A O K) ^ η) hx.1)
  have hG0 : G.app (E K l e ^ η • (D₁.phi x - x)) = 0 := by rw [map_smul, hG, smul_zero]
  obtain ⟨w, hw, hFw⟩ := (hex.exact _ hM).1 hG0
  have hu : IsUnit (E K l e ^ η) := (isUnit_E l e).pow η
  set y₀ := Ezpow K l e (-(η : ℤ)) • w with hy₀def
  have hE : E K l e ^ η • y₀ = w := by
    rw [hy₀def, smul_smul, E_pow_mul_Ezpow_neg, one_smul]
  have hFy₀ : F.app y₀ = D₁.phi x - x := by
    refine (hu.smul_left_cancel).1 ?_
    rw [← map_smul, hE]
    exact hFw
  have hy₀ : y₀ ∈ D₀.EM η := by
    rw [mem_divE, hE]
    exact hw
  have hinj : ∀ v ∈ D₀.EM η, F.app v = 0 → v = 0 := fun v hv h =>
    (hu.smul_left_cancel).1 (by
      rw [smul_zero]
      exact hex.inj _ hv (by rw [map_smul, h, smul_zero]))
  have hinv2 : ∀ g, D₁.desc.act g (D₁.phi x - x) = D₁.phi x - x := fun g => by
    rw [map_sub, D₁.desc.act_phi, hx.2 g]
  refine ⟨y₀, ⟨hy₀, fun g => ?_⟩, hFy₀, ?_⟩
  · rw [← sub_eq_zero]
    refine hinj _ (sub_mem (D₀.desc.act_mem_EM g hy₀) hy₀) ?_
    rw [map_sub, F.app_act, hFy₀, hinv2, sub_self]
  · refine (_root_.GlobalTheory.exactTriple_jumps_chars_lift O K l e a ι κ μ η H D₀ D₁ D₂ F G hex).2.2.1 ?_
    rw [map_zero, Hom.onPol_Mon, hFy₀, PhiMod.Mon_phi_sub,
      (D₁.cls_eq_zero_iff).2 (D₁.EN_mem_Man (D₁.M_le_Man hx.1)), neg_zero]

end GlobalTheory.BKGal.ExtClass

namespace GlobalTheory.BKGal.ExtClass

theorem xi_red_of_phi_eq {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PhiMod O K l e a ι) {u : Vec K a ι} (hu : P.phi u = u) : P.xi (red u) = u := by
  have := P.raises_phi.eq_zero (α := Unit) (σ := id) Function.surjective_id
    (δ := fun _ => u - P.xi (red u)) (fun _ => by rw [mem_uPow_one, map_sub, PhiMod.red_xi, sub_self])
    (fun _ => by rw [map_sub, hu, PhiMod.phi_xi, ← PhiMod.red_phi, hu]) ()
  exact (sub_eq_zero.1 this).symm


set_option maxHeartbeats 4000000 in
theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig U → ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∀ Pk : Pack a ϖ η H T, ∀ c ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, ∃ y ∈ Pk.D.Y, Pk.D.Mon y = 0 ∧ Pk.R.ClassOf y ((l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) • c) := by
  intro hBS hFB l _ a e _ _ ϖ LL _ _ Pl AI hStd N η H Sig U hN T hT Pk c hc
  have hl2 : l ≠ 2 := by
    have h1 := hN.large
    have h2 := hN.two_le
    rintro rfl
    have : 8 ≤ N ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ N ^ 3 := Nat.pow_le_pow_left h2 3
    omega
  obtain ⟨hUnit, hExt⟩ := GlobalTheory.T.extensionLattice_isCrysTameTypeWithJumps hFB l a e ϖ LL Pl AI hStd Sig U hN.zero_mem_Sig hN.zero_mem_U
  obtain ⟨Tp, f, g, v, hfg, hv, hgv, hcv, hTp⟩ := hExt T hT c hc
  obtain ⟨Pp, hPp⟩ := _root_.GlobalTheory.BKGal.exists_pack_isOfType hBS hFB l a e ϖ LL hl2 Pl AI hStd η H Sig U hN.range_U Tp hTp
  obtain ⟨Pu, hPu⟩ := _root_.GlobalTheory.BKGal.exists_pack_isOfType hBS hFB l a e ϖ LL hl2 Pl AI hStd η H Sig U hN.range_U _ hUnit
  obtain ⟨F, hF⟩ := _root_.GlobalTheory.BKGal.PackMap.main hBS l a e ϖ LL η H T Tp Pk Pp f
  have hG' := _root_.GlobalTheory.BKGal.PackMap.main hBS l a e ϖ LL η H Tp (unitLat (Gl l) : QLat LL) Pp Pu g
  obtain ⟨G, hG⟩ := hG'
  have hex : IsExactTriple F.toHom G.toHom :=
    GlobalTheory.T.isExactTriple_breuilKisin_of_shortExactLattices l a e ϖ LL _ _ _ Pk.D.toPhiMod Pp.D.toPhiMod Pu.D.toPhiMod T Tp (unitLat (Gl l) : QLat LL) Pk.R.I Pp.R.I Pu.R.I f g
      F.toHom G.toHom hfg hF hG
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H :=
    ⟨hN.frob_mem, hN.zero_mem_Sig, hN.card_Sig, hN.two_le, hN.range_U, hN.zero_mem_U, hN.card_U, hN.one_le,
      hN.lt, hN.large⟩
  have hK := _root_.GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main (↥(OL LL)) (↥LL.1) l e a (Fin Pp.n) (Fin Pu.n) Sig U N η H hB Pp.D Pu.D hPp
    hPu.chars_subset G hex.finiteLength
  obtain ⟨u, x, hx1, hu, hφu, hux⟩ := _root_.GlobalTheory.BKGal.UnitDatum.main hBS l a e ϖ LL η H Pu
  obtain ⟨x₂, hx₂, hGx₂⟩ := hK.2.2.2.1 u.1 hu
  have hG0 : G.app (Pp.D.phi x₂ - x₂) = 0 := by
    rw [map_sub, G.toHom.app_phi, hGx₂, map_nsmul, hφu, sub_self]
  obtain ⟨y, hy, hFy, hMon⟩ := lift_phi_sub F G hex hx₂ hG0
  refine ⟨y, hy, hMon, ?_⟩
  have hFinj := _root_.GlobalTheory.BK.IsExactTriple.injective_app _ _ _ _ _ _ _ _ _ _ _ F.toHom G.toHom hex
  set d := red (Pp.D.phi x₂) with hd
  have hL : Pp.D.phi x₂ ∈ Pp.D.L := Pp.D.phi_mem_L hx₂.1
  have hσp : Pp.D.phi x₂ - Pp.D.xi d ∈ Pp.D.MMl := by
    refine sub_mem (Pp.D.ext_mono ((A_le_S l e).trans (le_away _ _)) hL) ?_
    rw [PhiMod.xi_apply]
    refine ((_root_.GlobalTheory.BK.xi_trivialises_invL_S (↥(OL LL)) (↥LL.1) l e a (Fin Pp.n) Pp.D.toPhiMod).2 _).2 ?_
    exact mem_tot.2 fun τ i => by
      rw [cst_apply]
      exact HasK.C_mem _
  have hGσ : G.app (Pp.D.phi x₂ - Pp.D.xi d) = 0 := by
    rw [map_sub, Hom.app_xi, hd, ← Hom.red_app, G.toHom.app_phi, hGx₂, map_nsmul, hφu, map_nsmul, map_nsmul,
      xi_red_of_phi_eq _ hφu, sub_self]
  obtain ⟨σ, hσ, hFσ⟩ := _root_.GlobalTheory.BK.exists_preimage_invL_S_of_exactTriple _ _ _ _ _ _ _ _ _ _ _ F.toHom G.toHom hex _ hσp hGσ
  have hσinv : σ ∈ Pk.D.desc.inv := fun γ => hFinj (by
    rw [F.app_act, hFσ, map_sub, Pp.D.desc.act_phi, hx₂.2 γ, Descent.act_xi, hd, ← Descent.red_act,
      Pp.D.desc.act_phi, hx₂.2 γ])
  exact GlobalTheory.T.extensionClass_eq_lPow_smul_galois l a e ϖ LL η H T Tp f g hfg Pk Pp Pu F G hF hG hex hFinj u x hx1 hu hφu hux
    (GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) x₂ hx₂ hGx₂ v c hv hgv hcv σ hσ hσinv hFσ y hy hFy

end GlobalTheory.BKGal.ExtClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseNumberFieldOfContinuousCompletionEquiv
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory

open IsDedekindDomain.HeightOneSpectrum

theorem valuationSubring_le_one_of_ringOfIntegers {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω']
    [Algebra E' Ω'] (A' : ValuationSubring Ω') (m : 𝓞 E') :
    A'.valuation (algebraMap E' Ω' (m : E')) ≤ 1 :=
  (A'.valuation_le_one_iff _).2
    (mem_of_isIntegral_int A' (map_isIntegral_int (algebraMap E' Ω') (RingOfIntegers.isIntegral_coe m)))

theorem valuationSubring_lt_one_of_placeOver {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω']
    [Algebra E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (hP : IsPlaceOver A' w')
    (t : E') (ht : w'.valuation E' t < 1) : A'.valuation (algebraMap E' Ω' t) < 1 := by
  obtain ⟨s, hs, hq⟩ := GlobalTheory.exists_notMem_mul_valuation_le_one_of_ne w' (fun _ : Unit => t)
  have hsle : w'.valuation E' (s : E') ≤ 1 := by
    rw [RingOfIntegers.coe_eq_algebraMap]; exact w'.valuation_le_one (K := E') s
  have hw : w'.valuation E' ((s : E') * t) < 1 := by
    rw [map_mul]
    calc w'.valuation E' (s : E') * w'.valuation E' t ≤ 1 * w'.valuation E' t := by gcongr
      _ < 1 := by rwa [one_mul]
  have hall : ∀ q : HeightOneSpectrum (𝓞 E'), q.valuation E' ((s : E') * t) ≤ 1 := by
    intro q
    by_cases hq' : q = w'
    · subst hq'; exact hw.le
    · exact hq q hq' ()
  obtain ⟨m, hm⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E' _ hall
  have hmw : m ∈ w'.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E')]
    show w'.valuation E' (algebraMap (𝓞 E') E' m) < 1
    rw [hm]; exact hw
  have h1 := (hP m).2 hmw
  have h2 : A'.valuation (algebraMap E' Ω' (s : E')) = 1 :=
    le_antisymm (valuationSubring_le_one_of_ringOfIntegers A' s) (not_lt.1 (fun h => hs ((hP s).1 h)))
  have hm' : ((m : 𝓞 E') : E') = (s : E') * t := by rw [← hm]
  rw [hm', map_mul, map_mul, h2, one_mul] at h1
  exact h1

theorem exists_int_valuationSubring_le {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω']
    [Algebra E' Ω'] [Algebra.IsAlgebraic E' Ω'] (A' : ValuationSubring Ω') {δ : Ω'} (hδ : δ ≠ 0) :
    ∃ n : ℤ, n ≠ 0 ∧ A'.valuation (algebraMap E' Ω' (n : E')) ≤ A'.valuation δ := by
  haveI : Algebra.IsAlgebraic ℤ E' :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ E').mpr (Algebra.IsAlgebraic.isAlgebraic x)⟩
  haveI : Algebra.IsAlgebraic ℤ Ω' := Algebra.IsAlgebraic.trans ℤ E' Ω'
  obtain ⟨n, hn, hint⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) δ⁻¹).exists_integral_multiple
  refine ⟨n, hn, ?_⟩
  have hle := (A'.valuation_le_one_iff _).2 (mem_of_isIntegral_int A' hint)
  rw [zsmul_eq_mul, map_mul, map_inv₀] at hle
  have hd : A'.valuation δ ≠ 0 := by simpa using hδ
  rw [map_intCast]
  calc A'.valuation (n : Ω') = A'.valuation (n : Ω') * (A'.valuation δ)⁻¹ * A'.valuation δ := by
        rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
    _ ≤ 1 * A'.valuation δ := by gcongr
    _ = A'.valuation δ := one_mul _

end GlobalTheory

namespace GlobalTheory

theorem approx_of_completion_equiv : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [Algebra.IsAlgebraic E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')), IsPlaceOver A' w' → ∀ (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) → ∀ (y : E') (δ : Ω'), δ ≠ 0 → ∃ x : E, A'.valuation (algebraMap E' Ω' y - algebraMap E' Ω' (j x)) < A'.valuation δ := by
  intro E _ _ w E' Ω' _ _ _ _ _ A' w' hP j i hi hij y δ hδ
  obtain ⟨n, hn, hnδ⟩ := exists_int_valuationSubring_le (E' := E') A' hδ
  set c : E' := (n : E') with hcdef
  have hc : c ≠ 0 := Int.cast_ne_zero.mpr hn
  let U : Set (w'.adicCompletion E') :=
    {z | Valued.v ((z - algebraMap E' _ y) * (algebraMap E' (w'.adicCompletion E') c)⁻¹) < 1}
  have hU : IsOpen U := by
    have h := (Valued.isOpen_ball (w'.adicCompletion E') 1).preimage
      ((continuous_sub_right (algebraMap E' (w'.adicCompletion E') y)).mul
        (continuous_const (y := (algebraMap E' (w'.adicCompletion E') c)⁻¹)))
    convert h using 2 with z
    simp [U, Valuation.restrict_lt_iff_lt_embedding]
  have hdense : DenseRange (i ∘ algebraMap E (w.adicCompletion E)) :=
    i.surjective.denseRange.comp (HeightOneSpectrum.denseRange_algebraMap E w) hi
  obtain ⟨x, hx⟩ := hdense.exists_mem_open hU ⟨algebraMap E' _ y, by simp [U]⟩
  refine ⟨x, ?_⟩
  have hx' : w'.valuation E' ((j x - y) * c⁻¹) < 1 := by
    have e : (i (algebraMap E _ x) - algebraMap E' (w'.adicCompletion E') y) *
        (algebraMap E' (w'.adicCompletion E') c)⁻¹ = algebraMap E' (w'.adicCompletion E') ((j x - y) * c⁻¹) := by
      rw [hij, map_mul, map_sub, map_inv₀]
    have hx2 : (i ∘ algebraMap E (w.adicCompletion E)) x ∈ U := hx
    simp only [Function.comp, U, Set.mem_ofPred_eq] at hx2
    rw [e] at hx2
    have hv : Valued.v (algebraMap E' (w'.adicCompletion E') ((j x - y) * c⁻¹)) = w'.valuation E' ((j x - y) * c⁻¹) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w' _
    rw [hv] at hx2
    exact hx2
  have ht := valuationSubring_lt_one_of_placeOver A' w' hP _ hx'
  have e2 : algebraMap E' Ω' y - algebraMap E' Ω' (j x) = -(algebraMap E' Ω' ((j x - y) * c⁻¹) * algebraMap E' Ω' c) := by
    rw [← map_mul, ← map_sub, ← map_neg]; congr 1; field_simp; ring
  have hcpos : 0 < A'.valuation (algebraMap E' Ω' c) := by
    rw [zero_lt_iff]; simpa using hc
  rw [e2, Valuation.map_neg, map_mul]
  calc _ < A'.valuation (algebraMap E' Ω' c) := mul_lt_of_lt_one_left hcpos ht
    _ ≤ A'.valuation δ := hnδ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DropPlInsert
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def OffPl {S T' : HSp D} (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (u : WO S T') : Prop :=
  u.map (infPart D) = 0 ∧
    ∀ v ∈ Sb, ∀ ε, IsPlaceIdem D v ε → ∀ i j, algebraMap (AF D.host.F) (AE D) ε * u i j = 0

def SuppIn (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (V : HSp D) (g : GA D V) : Prop :=
  (mt V g - 1).map (infPart D) = 0 ∧
    ∀ v, v ∉ Sb → ∀ ε, IsPlaceIdem D v ε → ∀ i j, algebraMap (AF D.host.F) (AE D) ε * (mt V g - 1) i j = 0

def Over (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal

def LikeOff (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ c : WO (Vc D i) (Wc D i) →₀ ℂ, (∀ u ∈ c.support, OffPl Sb u) →
    (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u (R.vP i t)) = 0 →
    (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u f) = 0

def TypeIn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t), SuppIn Sb (Vc D i) κ →
    R.ωP i t (κ, 1) f = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • f

def CleanIn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    (∃ v ∈ Sb, Over PP.1 v) → ∀ κ : G → GA D (Vc D i), IsLifts R i t κ →
      (∀ g, mirC R i PP a tr ε g ≠ 0 → SuppIn Sb (Vc D i) (κ g)) → avgW R i t PP a tr ε κ f = 0

def StepGen (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ (g : GA D (Wc D i)) (f : WO (Vc D i) (Wc D i) → ℂ),
    TypeIn R i t Sb f ∧ CleanIn R i t Sb f ∧ LikeOff R i t Sb f ∧ φ = R.ωP i t (1, g) f}


open Classical in
def dropPl (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  Sb.erase v

theorem dropPl_insert [DecidableEq (HeightOneSpectrum (𝓞 D.host.F))] {s : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ s) : dropPl (insert v s) v = s := by
  unfold dropPl
  convert Finset.erase_insert hv

end GlobalTheory.DownLift.GenFinite

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfHasSupportSingleton
section
noncomputable section

open ValuativeRel GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.DZeroDegOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_hasSupport_singleton {y z : IrrGL (k := k)} (h : HasSupport y.rep {z}) : y = z := by
  obtain ⟨r, u, hu, hi, hc, e, hsub⟩ := h
  obtain rfl : r = 1 := by simpa using congrArg Multiset.card hu
  obtain rfl : u = fun _ => z := funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa using hu
  obtain ⟨d, c⟩ := y
  obtain rfl : z.1 = d := by simpa using Fintype.card_congr e
  have hd : ∑ _ : Fin 1, z.1 = z.1 := by simp
  let e' := stdBlocks (fun _ : Fin 1 => z.1) hd
  obtain ⟨φ⟩ : Nonempty ((multiProd e fun _ => z.rep).Equiv (multiProd e' fun _ => z.rep)) := by
    obtain ⟨w, hw⟩ := Placing.exists_moves (R := k) e' e
    have hw' : Placing.Moves e e' w⁻¹ := by
      intro g x y
      rw [← hw (w⁻¹ * g * w⁻¹⁻¹) x y]
      simp [mul_assoc]
    let ρ := twist (piTensor fun _ : Fin 1 => z.rep) (deltaHalf k fun _ : Fin 1 => Fin z.1)
    have conjugate {f f' : (Σ _ : Fin 1, Fin z.1) ≃ Fin z.1} {v : GL (Fin z.1) k}
        (hv : Placing.Moves f f' v) (p : parab k f) :
        ∃ q : parab k f', (q : GL (Fin z.1) k) = v * p * v⁻¹ ∧
          (ρ.comp (leviProj k f')) q = (ρ.comp (leviProj k f)) p := by
      have hq : v * (p : GL (Fin z.1) k) * v⁻¹ ∈ parab k f' := by
        rw [mem_parab]
        intro i j hij
        exact (hij.ne (Subsingleton.elim _ _)).elim
      refine ⟨⟨_, hq⟩, rfl, ?_⟩
      simp only [MonoidHom.comp_apply]
      congr 1
      refine funext fun a => Units.ext (Matrix.ext fun i j => ?_)
      simpa only [leviProj_apply] using hv (p : GL (Fin z.1) k) ⟨a, i⟩ ⟨a, j⟩
    exact Placing.smInd_equiv w (conjugate hw) (conjugate hw')
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one z hd
  let χ := φ.trans ψ.symm
  obtain ⟨θ⟩ := IsSubquotient.nonempty_equiv
    (hsub.trans (.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective)) hi z.2.rep.irr
  exact ((IrrGL.of_rep z).symm.trans ((IrrGL.of_eq_of.2 ⟨θ⟩).trans (IrrGL.of_rep ⟨_, c⟩))).symm

end GlobalTheory.DZeroDegOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSetStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugate_splitPlace_off_stableSet : ∀ (D : D7) (S0 : Finset (PlE D.host)) (Sb : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : PlE D.host),
    (∀ P1 P2, P1 ∈ S0 → IsConjPl D.host P1 P2 → P2 ∈ S0) → placesOver D.host.E 2 ⊆ (S0 : Set (PlE D.host)) →
    (∀ Q ∈ Sb, Q ∈ S0) → IsSplitPl D.host P → P ∉ S0 →
    ∃ P' : PlE D.host, IsConjPl D.host P P' ∧ IsSplitPl D.host P' ∧ P' ∉ S0 ∧
      Formalism.IndefR.Bridge.SplitOff P (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      Formalism.IndefR.Bridge.SplitOff P' (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal := by
  first | exact @GlobalTheory.ConjPlaceOff.exists_conj_off | exact GlobalTheory.ConjPlaceOff.exists_conj_off | (intros; apply GlobalTheory.ConjPlaceOff.exists_conj_off <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvalSum
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

noncomputable section

namespace GlobalTheory.KFinExp

theorem exists_eval_sum {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    (W : Submodule ℂ (Sm E N)) [FiniteDimensional ℂ W] (l : Module.Dual ℂ W) :
    ∃ a : GA E N →₀ ℂ, ∀ w : W, l w = ∑ x ∈ a.support, a x * w.1.1 x := by
  let ev : GA E N → Module.Dual ℂ W := fun x =>
    (LinearMap.proj x : (GA E N → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (Sm E N).subtype ∘ₗ W.subtype
  have hs : Submodule.span ℂ (Set.range ev) = ⊤ := Submodule.span_eq_top_of_ne_zero fun z hz => by
    by_contra h
    refine hz (Subtype.ext (Subtype.ext (funext fun x => ?_)))
    by_contra hx
    exact h ⟨ev x, ⟨x, rfl⟩, hx⟩
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hs ▸ Submodule.mem_top : l ∈ _)
  refine ⟨a, fun w => ?_⟩
  rw [← ha, Finsupp.sum, LinearMap.sum_apply]
  rfl

theorem exists_expansion (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (φ : Sm E N)
    (hφ : φ ∈ finVec (cptRep E N)) :
    ∃ (r : ℕ) (ψ : Fin r → Sm E N) (C : Fin r → Lie E N → ℂ),
      (∀ j, ψ j ∈ Submodule.span ℂ (Set.range fun k => cptRep E N k φ)) ∧
      (∀ j, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (C j) (oneL E N)) ∧
      ∀ k : Kinf E N, cptRep E N k φ = ∑ j, C j (toL k.1) • ψ j := by
  set W := Submodule.span ℂ (Set.range fun k => cptRep E N k φ)
  have hf : FiniteDimensional ℂ W := hφ
  let b := Module.finBasis ℂ W
  choose a ha using fun j => exists_eval_sum W (b.coord j)
  refine ⟨_, fun j => (b j).1, fun j y => ∑ x ∈ (a j).support, a j x * chart φ.1 x y, fun j => (b j).2,
    fun j => ContDiffAt.sum fun x _ => contDiffAt_const.mul (contDiffAt_chart φ.2 x isUnit_one), fun k => ?_⟩
  let w : W := ⟨cptRep E N k φ, Submodule.subset_span ⟨k, rfl⟩⟩
  have h := congrArg Subtype.val (b.sum_repr w)
  rw [Submodule.coe_sum] at h
  refine h.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [Submodule.coe_smul]
  congr 1
  refine (ha j w).trans (Finset.sum_congr rfl fun x _ => ?_)
  congr 1
  exact (chart_val φ.1 x (Unitary.toUnits k)).symm

end GlobalTheory.KFinExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumInnerProductFinsuppLocalCosetFamiliesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_innerProduct_finsupp_localCosetFamilies : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LevProd R i → TransLaws R i → FinMult R i t → LevFix R i t → VecNe R i t → FinSum R i t → ∀ th, IsRaw R i t th → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∃ a : ℝ, 0 < a ∧ ∀ x y, HasSum (fun F : {F : ∀ v, Eu.LX R i v // {w | F w ≠ Eu.lx0 R i w}.Finite} => (a : ℂ) * ((∏ᶠ v, Eu.acoef R i t μ 𝓕 v (F.1 v)) * ⟪x, Eu.Bfam R i F.1 y⟫_ℂ)) ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ := by
  first | exact @GlobalTheory.RawLift.FamSum.hasSum_families | exact GlobalTheory.RawLift.FamSum.hasSum_families | (intros; apply GlobalTheory.RawLift.FamSum.hasSum_families <;> assumption)
end

