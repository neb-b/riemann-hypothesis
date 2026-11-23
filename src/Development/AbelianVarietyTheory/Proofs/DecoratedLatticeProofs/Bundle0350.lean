module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryThetaInnerProductFormulaConvergentRange
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

theorem innerProduct_convergent : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : GlobalTheory.Core.Rk.IP.WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure → ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧ Integrable (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) m ∧ petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = volQ B mH * ∫ g, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m := by
  intro hC hWS hSEC D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hwitt hat m mH hm hmH Φ₁ Φ₂ hΦ₁ hΦ₂ u₁ hu₁ u₂ hu₂
  have hW := GlobalTheory.weilRepresentationUnitaryPair
  obtain ⟨ha, ht, hb, hθ, hSig, hCart, -⟩ := hP.setting
  obtain ⟨omh, homh⟩ := _root_.GlobalTheory.Core.Rk.exists_doubled_weilDatum hW D ψ A B χA χB om hP.weil
  have hTC := _root_.GlobalTheory.DoublingTheta.thetaClause D ψ A B χA χB om omh hP.weil homh
  have hCC := _root_.GlobalTheory.Core.Rk.coefClause_of_thetaClause D ψ A B χA χB om omh hP.weil hTC ν 𝓕 hP.covol
  obtain ⟨hφ, hid⟩ := hTC Φ₁ Φ₂ hΦ₁.1 hΦ₂.1
  have hK := _root_.GlobalTheory.Core.Rk.IP.delta_isKFinVec D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP omh homh Φ₁ Φ₂ hΦ₁ hΦ₂
  have h2a : 2 * A.rank < B.rank := by omega
  have hw : wittIndex B = 0 ∨ A.rank + wittIndex B < B.rank := by
    rcases hwitt with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)

  obtain ⟨-, hEis⟩ := _root_.GlobalTheory.Core.Rk.IP.thetaMean_eq_eis_of_weil hWS D ψ A B ha h2a hw χB omh homh ν 𝓕 hP.covol mH hmH (delta A B Φ₁ Φ₂) hφ
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    _root_.GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hP.maj
  have hmem := _root_.GlobalTheory.SwSecMem.swSec_mem_degPS hW D ψ A B χB omh homh ν 𝓕 hP.covol (delta A B Φ₁ Φ₂) hφ a hK
  have hHk : IsHeckeChar D χB⁻¹ := by
    have h := homh.hecT
    refine ⟨?_, fun x => ?_⟩
    · have : (χB⁻¹ : (AE D)ˣ →* Circle) = fun x => (χB x)⁻¹ := rfl
      rw [this]; exact h.1.inv
    · rw [MonoidHom.inv_apply, h.2 x, inv_one]

  have hf₁ := _root_.GlobalTheory.Core.Rk.CuspConj.conj_comp_mem_A0 D θ A cA hθ u₁ hu₁
  have hf₂ := _root_.GlobalTheory.Core.Rk.CuspConj.conj_comp_mem_A0 D θ A cA hθ u₂ hu₂
  have rd : ∀ u ∈ A0 θ A cA, GlobalTheory.Grow.RapidDec A u := fun u hu =>
    GlobalTheory.Grow.rapidDec_of_cuspForm hC hθ (mem_cuspForms.1 hu).1.1 (mem_cuspForms.1 hu).1.2

  have hre : (A.rank : ℝ) / 2 < (sZero A B).re := by
    have e : (sZero A B).re = ((B.rank : ℝ) - A.rank) / 2 := by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, Complex.div_re]
    rw [e]
    have : (A.rank : ℝ) < t := by exact_mod_cast hat
    have hb' : (B.rank : ℝ) = A.rank + t := by exact_mod_cast hb
    rw [hb']; linarith
  have hBI := _root_.GlobalTheory.Core.Rk.IP.basicIdentity_flat hSEC hC D A (by omega) a hP.maj hI χB⁻¹ hHk (sZero A B)
    (swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂)) hmem θ hθ cA m hm _ hf₁ _ hf₂ (sZero A B) hre
  simp only [flatH_self] at hBI
  obtain ⟨-, hZc, hZe⟩ := hBI

  have hpt : ∀ g, swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂) (io A (g, 1)) *
      conj (GlobalTheory.Eis.petCoef A m (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) g) =
      wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g := by
    intro g
    have e1 : swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂) (io A (g, 1)) = wcoef om ν 𝓕 Φ₁ Φ₂ g :=
      (hCC Φ₁ Φ₂ hΦ₁.1 hΦ₂.1).2 g
    have e2 : conj (GlobalTheory.Eis.petCoef A m (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) g) = rcoef m u₁ u₂ g := by
      simp only [GlobalTheory.Eis.petCoef, rcoef, petersson, pet, rTr, GlobalTheory.AutomorphicL2Unitary.descend]
      rw [← integral_conj]
      congr 1
      ext x
      simp
    rw [e1, e2]
  have hInt : Integrable (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) m := by
    have e : (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) = fun g =>
        swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂) (io A (g, 1)) *
          starRingEnd ℂ (GlobalTheory.Eis.petCoef A m (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) g) :=
      funext fun g => (hpt g).symm
    rw [e]
    exact hZc
  have hZ : GlobalTheory.Eis.dblInt A χB⁻¹ m (GlobalTheory.Eis.eis A (swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂)))
      (fun x => conj (u₁ x)) (fun x => conj (u₂ x)) = ∫ g, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m := by
    rw [hZe]
    unfold zetaH pairInt
    exact integral_congr_ae (.of_forall fun g => hpt g)

  have hKer : ∀ Φ, IsFockVec ψ θ A B sA sB Φ →
      Continuous (Function.uncurry fun g h => thetaKO om g h Φ) ∧
      (∀ γ ∈ GQ A, ∀ g h, thetaKO om (γ * g) h Φ = thetaKO om g h Φ) ∧
      (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO om g h Φ) ∧
      (GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (fun h => thetaKO om g h Φ) fun h => thetaKO om g h Φ) ∧
      ∀ h, GlobalTheory.Grow.ModGrowth A fun g => thetaKO om g h Φ := by
    intro Φ hΦ
    obtain ⟨hL2, hMG⟩ := _root_.GlobalTheory.Core.Rk.IP.normSq_theta_modGrowth_big hWS hSEC D ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hwitt hat mH hmH Φ hΦ
    refine ⟨hP.weil.om_cont Φ hΦ.1 0, fun γ hγ g h => ?_, hL2, hMG, fun h => ?_⟩
    · have e : ((γ * g, h) : GA D A × GA D B) = (γ, 1) * (g, h) := by simp
      unfold thetaKO
      rw [e, map_mul]
      exact hP.weil.om_aut γ hγ 1 (one_mem _) _ (hP.weil.om_pres _ _ hΦ.1)
    · obtain ⟨C, N, hCN⟩ := _root_.GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ D ψ A B χA χB om hP.weil Φ hΦ.1
      refine ⟨C * GlobalTheory.Grow.height B h ^ N, N, fun g => (hCN g h).trans (le_of_eq ?_)⟩
      rw [mul_pow]; ring
  obtain ⟨i₁, i₂, l₁, l₂, hss⟩ := GlobalTheory.T.seesaw_fubini_two_lifts_moderate_growth_kernels D A B m mH hm hmH (fun g h => thetaKO om g h Φ₁)
    (fun g h => thetaKO om g h Φ₂) (fun K hK => by
      rcases hK with rfl | rfl
      exacts [hKer Φ₁ hΦ₁, hKer Φ₂ hΦ₂]) u₁ u₂ (rd u₁ hu₁) (rd u₂ hu₂)
  refine ⟨⟨i₁, l₁⟩, ⟨i₂, l₂⟩, hInt, ?_⟩
  rw [← hZ, ← hEis]

  have key : ∀ g₁ g₂ h, thetaKO om g₁ h Φ₁ * conj (thetaKO om g₂ h Φ₂) =
      ((χB (detA A g₂) : Circle) : ℂ) * thetaKO omh (io A (g₁, g₂)) h (delta A B Φ₁ Φ₂) := by
    intro g₁ g₂ h
    rw [(hid g₁ g₂ h).2]
    have e : ((χB (detA A g₂) : Circle) : ℂ) * (((χB (detA A g₂))⁻¹ : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
    linear_combination (-(thetaKO om g₁ h Φ₁ * conj (thetaKO om g₂ h Φ₂))) * e
  have hpet : ∀ g₁ g₂, petersson B mH (fun h => thetaKO om g₁ h Φ₁) (fun h => thetaKO om g₂ h Φ₂) =
      ((χB (detA A g₂) : Circle) : ℂ) *
        ((volQ B mH : ℂ) * GlobalTheory.ThetaMean.thetaMean omh mH (delta A B Φ₁ Φ₂) (io A (g₁, g₂))) := by
    intro g₁ g₂
    have e1 : petersson B mH (fun h => thetaKO om g₁ h Φ₁) (fun h => thetaKO om g₂ h Φ₂) =
        ((χB (detA A g₂) : Circle) : ℂ) *
          ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO omh (io A (g₁, g₂)) h (delta A B Φ₁ Φ₂)) q
            ∂autMeasure B mH := by
      rw [← integral_const_mul]
      simp only [petersson, pet, GlobalTheory.AutomorphicL2Unitary.descend]
      congr 1
      funext q
      exact key g₁ g₂ _
    rw [e1, ← measure_smul_average, GlobalTheory.ThetaMean.thetaMean, Complex.real_smul]
    rfl
  have hss' : petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = _ := hss
  rw [hss', GlobalTheory.Eis.dblInt, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun q => ?_)
  simp only [GlobalTheory.Eis.dblIntegrandQ, GlobalTheory.Eis.dblIntegrand, hpet, MonoidHom.inv_apply, Circle.coe_inv, inv_inv,
    RCLike.conj_conj]
  ring

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.RatioUnit

theorem natCast_notMem_of_primes {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ m : ℕ, m ≠ 0 → (∀ p : ℕ, p.Prime → p ∣ m → (p : R) ∉ P) → (m : R) ∉ P := by
  intro m
  induction m using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; rw [Nat.cast_one]; exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)
  | prime p hp => intro _ h; exact h p hp dvd_rfl
  | mul a b ha hb =>
    intro hab h hmem
    rw [Nat.cast_mul] at hmem
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact ha (left_ne_zero_of_mul hab) (fun p hp hd => h p hp (dvd_mul_of_dvd_left hd b)) h1
    · exact hb (right_ne_zero_of_mul hab) (fun p hp hd => h p hp (dvd_mul_of_dvd_right hd a)) h1

theorem not_dvd_both {r : ℚ} {p : ℕ} (hp : p.Prime) (h1 : p ∣ r.num.natAbs) (h2 : p ∣ r.den) : False :=
  hp.not_dvd_one (by simpa [Nat.Coprime.gcd_eq_one r.reduced] using Nat.dvd_gcd h1 h2)

theorem padicValRat_ne_zero_of_dvd_num {r : ℚ} (hr : r ≠ 0) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ r.num.natAbs) : padicValRat p r ≠ 0 := by
  haveI := Fact.mk hp
  have hnd : ¬ p ∣ r.den := fun hd' => not_dvd_both hp hd hd'
  have h0 : r.num.natAbs ≠ 0 := by simpa using hr
  have h1 := one_le_padicValNat_of_dvd h0 hd
  simp only [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hnd]
  omega

theorem padicValRat_ne_zero_of_dvd_den {r : ℚ} {p : ℕ} (hp : p.Prime)
    (hd : p ∣ r.den) : padicValRat p r ≠ 0 := by
  haveI := Fact.mk hp
  have hnd : ¬ p ∣ r.num.natAbs := fun hd' => not_dvd_both hp hd' hd
  have h1 := one_le_padicValNat_of_dvd r.den_nz hd
  simp only [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hnd]
  omega

end GlobalTheory.Fam.RatioUnit

namespace GlobalTheory.Fam
open Formalism.DivisionValues GlobalTheory.Fam.RatioUnit

theorem RatioUnit.intCast_notMem_of_natAbs {R : Type} [CommRing R] (P : Ideal R) (z : ℤ)
    (h : ((z.natAbs : ℕ) : R) ∉ P) : ((z : ℤ) : R) ∉ P := by
  rcases Int.natAbs_eq z with e | e
  · rw [e]; simpa using h
  · rw [e]; simpa [Ideal.neg_mem_iff] using h

theorem vw_eq_zero_of_unitRatio : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (w : HeightOneSpectrum (𝓞 K)) (S : ℕ → Prop) (x y : ℂ), GlobalTheory.Fam.UnitRatio S x y → (∀ p : ℕ, p.Prime → S p → (p : 𝓞 K) ∉ w.asIdeal) → ∀ a : K, σ a = x / y → Formalism.DivisionValues.vw w a = 0 := by
  intro K _ _ σ w S x y hU hS a ha

  letI : StarRing K := starRingOfComm
  obtain ⟨_, n, hn, r, hr0, hpow, hrS⟩ := hU
  have hpow' : a ^ n = (r : K) := by
    apply σ.injective
    rw [map_pow, ha, hpow, map_ratCast]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hpow'
    exact hr0 (by exact_mod_cast hpow'.symm)
  have hnum : ((r.num : ℤ) : 𝓞 K) ∉ w.asIdeal := by
    refine intCast_notMem_of_natAbs _ _ (natCast_notMem_of_primes w.asIdeal _ (by simpa using hr0) ?_)
    intro p hp hd
    exact hS p hp (hrS p hp (padicValRat_ne_zero_of_dvd_num hr0 hp hd))
  have hden : ((r.den : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    refine natCast_notMem_of_primes w.asIdeal _ r.den_nz ?_
    intro p hp hd
    exact hS p hp (hrS p hp (padicValRat_ne_zero_of_dvd_den hp hd))
  have vnum := ReductionFirst.vw_unit w _ hnum
  have vden := ReductionFirst.vw_unit w _ hden
  rw [show (((r.num : ℤ) : 𝓞 K) : K) = (r.num : K) from map_intCast (algebraMap (𝓞 K) K) _] at vnum
  rw [show (((r.den : ℕ) : 𝓞 K) : K) = (r.den : K) from map_natCast (algebraMap (𝓞 K) K) _] at vden
  have hd0 : (r.den : K) ≠ 0 := by exact_mod_cast r.den_nz
  have hrK0 : (r : K) ≠ 0 := by exact_mod_cast hr0
  have key : (r : K) * (r.den : K) = (r.num : K) := by
    rw [Rat.cast_def]; field_simp
  have h1 := ReductionFirst.vw_mul w hrK0 hd0
  rw [key, vnum, vden] at h1
  have h2 := ReductionFirst.vw_pow w a n
  rw [hpow'] at h2
  have h3 : (n : ℤ) * vw w a = 0 := by rw [← h2]; omega
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (by exact_mod_cast h) hn.ne'
  · exact h

end GlobalTheory.Fam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCoefficientPureTensorEqSmulInner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
noncomputable section
open scoped ComplexConjugate

namespace GlobalTheory.WeilCoefScalar

theorem integrableOn_mul_conj {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) {ν : Measure (WO S T)}
    {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕) :
    IntegrableOn (fun w => f w * conj (g w)) 𝓕 ν := by
  refine GlobalTheory.MixModel.covolOne_integrableOn hν _
    (hf.cont.mul (Complex.continuous_conj.comp hg.cont)) ?_
  rintro _ ⟨γ, rfl⟩ a
  have e1 := hf.quasi γ a
  have e2 := hg.quasi γ a
  have hn : ∀ x, conj (ψ x) * ψ x = 1 := fun x => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.1.2.1 x]; norm_num
  change f (ratW T S γ + a) * conj (g (ratW T S γ + a)) = f a * conj (g a)
  rw [e1, e2, map_mul]
  linear_combination (f a * conj (g a)) * hn (-symplOH S T (ratW T S γ) a)

end GlobalTheory.WeilCoefScalar

namespace GlobalTheory.WeilCoefScalar

theorem wcoef_pure_eq_smul_inner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) ν 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) ν 𝓕 → ∃ z : ℂ, (∀ (w : (R.cV i).W), ∀ b ∈ GinfC (Vc D i), GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) b = z * ⟪w, (R.cV i).ρ b w⟫_ℂ) ∧ ∀ w : (R.cV i).W, R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w) ≠ 0 → z ≠ 0 := by

  intro D G _ _ Pl0 T A Ks _ _ _ R F hC _hF i t v ν 𝓕 hν
  have hc : (R.cV i).Is := hC.models.cV i
  have hW := hC.thP.ωP i t
  have hio := (hC.thP.ioP i t).1
  let J : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
      (onb (R.MW i (sg0 D A))) (R.vP i t)).comp (R.ioP i (PiTensorProduct.tprod ℂ v))
  have hJ : ∀ x, R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) x) = J x := fun x => rfl
  have hth : ∀ x, IsThetaFunO R.ψ (Vc D i) (Wc D i) (J x) := fun x => hC.thP.pt_theta i t _
  have hint : ∀ x y, IntegrableOn (fun w => J y w * conj (J x w)) 𝓕 ν := fun x y =>
    integrableOn_mul_conj hW.std (hth y) (hth x) hν
  let B : (R.cV i).W →ₗ⋆[ℂ] (R.cV i).W →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ∫ w in 𝓕, J y w * conj (J x w) ∂ν)
      (fun x x' y => by
        simp only [map_add (f := _), Pi.add_apply, mul_add]
        exact integral_add (hint x y) (hint x' y))
      (fun a x y => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
        rw [← integral_const_mul]
        congr 1; funext w; ring)
      (fun x y y' => by
        simp only [map_add (f := _), Pi.add_apply, add_mul]
        exact integral_add (hint x y) (hint x y'))
      (fun a x y => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext w; ring)
  have hB : ∀ x y, B x y = ∫ w in 𝓕, J y w * conj (J x w) ∂ν := fun x y => rfl
  have hom : ∀ u ∈ GinfC (Vc D i), ∀ x, R.ωP i t (u, 1) (J x) = J ((R.cV i).ρ u x) := fun u hu x => by
    rw [← hJ, ← hJ]; exact hio u hu _ x
  have hinv : ∀ u ∈ GinfC (Vc D i), ∀ x y, B ((R.cV i).ρ u x) ((R.cV i).ρ u y) = B x y := by
    intro u hu x y
    rw [hB, hB, ← hom u hu x, ← hom u hu y]
    exact GlobalTheory.Mem.LiftPolar.scalar_eq D R.ψ hW.std _ _ ν 𝓕 hν.1 hν.2.1 (R.ωP i t (u, 1))
      (fun f hf => hW.om_pres _ f hf) (fun f hf => hW.om_unit ν 𝓕 hν.1 hν.2.1 _ f hf) (J y) (J x) (hth y) (hth x)
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.CoefRealSchur.form_eq_smul_inner D (Vc D i) (R.cV i) hc B hinv
  refine ⟨z, fun w b hb => ?_, fun w hw hz0 => ?_⟩
  · rw [hJ, ← hz, hB, GlobalTheory.Core.Rk.IP.wcoef, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, hom b hb w]
  · rw [hJ] at hw
    have h1 := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hW.std (hth w) hw hν
    apply h1
    have h2 := hz w w
    rw [hz0, zero_mul, hB] at h2
    rw [GlobalTheory.RawLift.thetaIP, ← h2]
    congr 1; funext x
    rw [Complex.star_def, mul_comm]

end GlobalTheory.WeilCoefScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WithMuEq
section
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel Matrix

noncomputable section

namespace GlobalTheory.SeeSaw.MuUnits

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem Phi_eq {a t : Type} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] (Q Q' : TypeDatum k a)
    (hJ : Q.J = Q'.J) (hl : ∀ x (hx : x ∈ Q.J) (hx' : x ∈ Q'.J), Q.lam ⟨x, hx⟩ = Q'.lam ⟨x, hx'⟩)
    (μ μ' : kˣ →* ℂˣ) (hμ : ∀ x : kˣ, valuation k (x : k) = 1 → μ x = μ' x) (x : Matrix (a ⊕ t) a k) :
    Q.Phi t μ x = Q'.Phi t μ' x := by
  by_cases h : (∃ g ∈ Q.J, g.val = x.toRows₁) ∧ MaxM x.toRows₂
  · obtain ⟨⟨g, hg, e⟩, h2⟩ := h
    have hg' : g ∈ Q'.J := hJ ▸ hg
    rw [Q.Phi_of_mem μ ⟨g, hg⟩ e h2, Q'.Phi_of_mem μ' ⟨g, hg'⟩ e h2, hl g hg hg',
      hμ _ (valuation_det_of_mem_KO (Q.le_KO hg))]
  · have h' : ¬ ((∃ g ∈ Q'.J, g.val = x.toRows₁) ∧ MaxM x.toRows₂) := by rwa [← hJ]
    rw [not_not.1 (mt (Q.Phi_ne_zero_iff μ).1 h), not_not.1 (mt (Q'.Phi_ne_zero_iff μ').1 h')]

theorem iter_eq {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ μ' : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hμ' : ∀ j, IsTame (μ' j))
    (h : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = μ' j x) (j : ℕ) :
    (P.iter t μ hμ j).J = (P.iter t μ' hμ' j).J ∧ ∀ x (hx : x ∈ (P.iter t μ hμ j).J) (hx' : x ∈ (P.iter t μ' hμ' j).J),
      (P.iter t μ hμ j).lam ⟨x, hx⟩ = (P.iter t μ' hμ' j).lam ⟨x, hx'⟩ := by
  induction j with
  | zero => exact ⟨rfl, fun _ _ _ => rfl⟩
  | succ j ih =>
    obtain ⟨hJ, hl⟩ := ih
    set Q := P.iter t μ hμ j
    set Q' := P.iter t μ' hμ' j
    have hS : Q.stepJ t = Q'.stepJ t := by
      ext g; rw [TypeDatum.mem_stepJ, TypeDatum.mem_stepJ, hJ]
    refine ⟨?_, fun x hx hx' => ?_⟩
    · rw [TypeDatum.iter_succ, TypeDatum.iter_succ]
      change (Q.stepJ t).comap _ = (Q'.stepJ t).comap _
      rw [hS]
    · have hx1 : (reGL (ixSucc r t j)).symm x ∈ Q.stepJ t := hx
      have hx1' : (reGL (ixSucc r t j)).symm x ∈ Q'.stepJ t := hx'
      change (Q.step t (μ (j + 1)) (hμ _)).lam ⟨_, hx1⟩ = (Q'.step t (μ' (j + 1)) (hμ' _)).lam ⟨_, hx1'⟩
      have hg' : ((Q.corner ⟨_, hx1⟩ : Q.J) : GL _ k) ∈ Q'.J := hJ ▸ (Q.corner ⟨_, hx1⟩).2
      refine (Q.step_lam _ _ ⟨_, hx1⟩ (Q.corner ⟨_, hx1⟩) (Q.corner_val _)).trans
        (Eq.trans ?_ (Q'.step_lam _ _ ⟨_, hx1'⟩ ⟨_, hg'⟩ (Q.corner_val _)).symm)
      rw [hl _ (Q.corner ⟨_, hx1⟩).2 hg',
        h _ _ (valuation_det_of_mem_KO (Q.le_KO (Q.corner ⟨_, hx1⟩).2)), h _ _ (valuation_det_of_mem_KO hx1.1)]

theorem withMu_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ)
    (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) :
    (∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = S.μ j x) →
      (∀ j a H, ((withMu S μ hμ).T t).Phi j a H = (S.T t).Phi j a H) ∧
      ∀ j a H, (((withMu S μ hμ).T t).lev j a H).J = ((S.T t).lev j a H).J ∧
        ∀ x hx hx', (((withMu S μ hμ).T t).lev j a H).lam ⟨x, hx⟩ = ((S.T t).lev j a H).lam ⟨x, hx'⟩ := by
  intro h
  have E := iter_eq (t := t) S.P μ S.μ hμ S.tame h
  refine ⟨fun j a H => funext fun x => ?_, fun j a H => ⟨?_, fun x hx hx' => ?_⟩⟩
  · change (S.P.iter t μ hμ j).Phi t (μ (j + 1)) _ = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1)) _
    exact Phi_eq _ _ (E j).1 (E j).2 _ _ (h (j + 1)) _
  · change (S.P.iter t μ hμ j).J.comap _ = (S.P.iter t S.μ S.tame j).J.comap _
    rw [(E j).1]; rfl
  · exact (E j).2 _ hx hx'

end GlobalTheory.SeeSaw.MuUnits
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedCoordinateWeilTranslateCompactMajorant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
noncomputable section

namespace GlobalTheory.Unf

theorem mixS_om_compact_maj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ Kp : Set (GA D S × GA D T), IsCompact Kp → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ p ∈ Kp, ∀ x w, ‖d.mixS T ψ v.μ v.𝓕 (om p f) x w‖ ≤ C * maj θ K N x := by
  intro D ψ S T χS χT om hω θ hθ S₀ ρ d v f hf Kp hKp
  obtain ⟨U, hU, hUK⟩ := _root_.GlobalTheory.LevelCompact.exists_level_compact D ψ S T χS χT om hω f hf Kp hKp
  obtain ⟨K, hK, hKN⟩ := _root_.GlobalTheory.Unf.mixS_le_maj D ψ hω.std θ hθ S S₀ T ρ d v U hU
  refine ⟨K, hK, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hKN N
  obtain ⟨A, hA⟩ := GlobalTheory.WeilWordGrowth.sup_words_growth D ψ S T χS χT om hω θ hθ N
  obtain ⟨c, hc⟩ := hA f hf
  have hcont : Continuous fun p : GA D S × GA D T =>
      c * (GlobalTheory.Grow.height S p.1 * GlobalTheory.Grow.height T p.2) ^ A :=
    continuous_const.mul ((((GlobalTheory.Grow.continuous_height S).comp continuous_fst).mul
      ((GlobalTheory.Grow.continuous_height T).comp continuous_snd)).pow A)
  obtain ⟨B, hB⟩ := hKp.bddAbove_image hcont.continuousOn
  refine ⟨(C : ℝ) * max B 0, fun p hp x w => ?_⟩
  have h1 := hC (om p f) (hUK p hp) x w
  have h2 : supSob ψ θ N (om p f) ≤ ENNReal.ofReal (max B 0) :=
    (hc p.1 p.2).trans (ENNReal.ofReal_le_ofReal ((hB ⟨p, hp, rfl⟩).trans (le_max_left _ _)))
  have hm := maj_nonneg θ K N x
  have h3 : ‖d.mixS T ψ v.μ v.𝓕 (om p f) x w‖ₑ ≤ ENNReal.ofReal ((C : ℝ) * max B 0 * maj θ K N x) := by
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
    gcongr
  rw [← ofReal_norm_eq_enorm] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

end GlobalTheory.Unf

end
end

