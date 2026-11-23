module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Formalism.LocalRingCardinality.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftMultiplicitySpacesOfHyp
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsKilledHeisenbergAverageIsotropic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1866
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffCartierCompl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedCartierDivisorOfSncClosed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKernelVectorUnitMulDilatedFlat
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseCmp


open Classical in
theorem kerDat_twoStep {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    {i : Fin D.R.m} {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {Q : Finset (Pl D.host.E)} {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ} (hK : KerDat R i ξ χ ξR Q ω φ)
    (hQ : ∃ t, Q ⊆ R.Q t) {eg eQ : AE D} {fg : WO (Vc D i) (Wc D i) → ℂ} (hg : IsIdemSum eg R.Pg) (hq : IsIdemSum eQ Q)
    (hfg : IsTypeVec R i eg fg) :
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eQ) (lattice₂ R i) 1 fg
      (fun x => if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) φ := by
  obtain ⟨⟨hψ, -⟩, e, he, hTe⟩ := hK.vec
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  obtain ⟨t, ht⟩ := hQ
  have hd : Disjoint R.Pg Q := Disjoint.mono_right ht (GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces R F hC t)
  have hsum : e = eg + eQ := by
    rw [← GlobalTheory.ExportSeries.idem_eq he, ← GlobalTheory.ExportSeries.idem_eq hg, ← GlobalTheory.ExportSeries.idem_eq hq]
    exact Finset.sum_union hd
  subst hsum
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hgQ : eg * eQ = 0 := by
    refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
    push_cast
    linear_combination hee - heg - heQ
  have hcg : cA D eg * cA D eg = cA D eg := by rw [← map_mul, heg]
  have hcQ : cA D eQ * cA D eQ = cA D eQ := by rw [← map_mul, heQ]
  have hQg : cA D eQ * cA D eg = 0 := by rw [← map_mul, mul_comm, hgQ, map_zero]
  have hgQ' : cA D eg * cA D eQ = 0 := by rw [mul_comm, hQg]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True),
      a • u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) :=
    fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu
  have hinfg : infPart D (cA D eg) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
  have hinfQ : infPart D (cA D eQ) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hq)
  have hSBg := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    R.Pg (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h
  have hSBQ := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) hinfQ (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    Q (fun y => omegaQ Q (Wc D i).rank ξR (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  obtain ⟨⟨Te, hTe1⟩, hTe2⟩ := hTe
  have hc : cA D (eg + eQ) = cA D eQ + cA D eg := by rw [map_add (f := _), add_comm]
  have hc' : cA D (eg + eQ) = cA D eg + cA D eQ := map_add _ _ _
  have hm1 := GlobalTheory.TwoStepModel.isPlaceModel_comp_tensorHalf hcQ hcg hQg hΛ hSBg (hc ▸ hTe1)
  have hm2 := GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf hcg hcQ hgQ' hΛ (hc' ▸ hTe1)
  have hbase := hfg.2 _ hm2
  simp only [LinearMap.comp_apply] at hbase
  rw [← hbase] at hm1
  refine ⟨⟨_, hm1⟩, fun T' hT' => ?_⟩
  rw [hTe2 Te hTe1, GlobalTheory.TwoStepModel.datum_eq_tensorHalf (R.βV i) (R.βW i) hg hq hd he ξR]
  exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hcQ hinfQ hm1 hT' hSBQ

end GlobalTheory.BaseCmp

namespace GlobalTheory.BaseCmp


open GlobalTheory.ChainOnto in
theorem kerDat_xiR_ne : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle)
    (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ),
    KerDat R i ξ χ ξR Q ω φ → ∀ PP ∈ Q, ξR PP ≠ 1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _ i ξ χ ξR Q ω φ hK
  intro PP hP h1
  refine (hK.ram PP).2 (Or.inl hP) fun x hx => ?_
  have hc := hK.res PP hP
  rw [h1] at hc
  have hU : IsOpen {z : PP.adicCompletion D.host.E | Valued.v (z - x) < 1} :=
    (GlobalTheory.ChainOnto.TameRes.isOpen_ltOne PP).preimage (continuous_sub_right _)
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap D.host.E PP).exists_mem_open hU ⟨x, by simp⟩
  have hk' : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) < Valued.v (x : PP.adicCompletion D.host.E) := by
    rw [hx]; exact hk
  have hv : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k) = 1 := by
    rw [Valuation.map_eq_of_sub_lt _ hk']; exact hx
  have hv1 : PP.valuation D.host.E k = 1 := by rw [← GlobalTheory.ChainOnto.TameRes.val_alg]; exact hv
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hv1
  obtain ⟨a, s, h⟩ := PP.exists_primeCompl_mul_eq_of_integer k hv1.le
  have hs : (s : 𝓞 D.host.E) ∉ PP.asIdeal := s.2
  have hsv := GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem PP _ hs
  have hav : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E a) = 1 := by
    rw [← h, map_mul, hv1, hsv, one_mul]
  have ha : a ∉ PP.asIdeal := fun hm =>
    absurd hav (ne_of_lt ((PP.valuation_lt_one_iff_mem (K := D.host.E) a).mpr hm))
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  have key : ∀ (b : 𝓞 D.host.E), b ∉ PP.asIdeal → ∀ y : D.host.Eˣ, (y : D.host.E) = b → ξ.locK PP y = 1 := by
    intro b hb y hy
    have hms : (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hb
    obtain ⟨b', hb'⟩ := Ideal.Quotient.exists_inv hms
    exact (hc b y (Units.mkOfMulEqOne _ b' hb') hy rfl).symm
  have hs0 : algebraMap (𝓞 D.host.E) D.host.E s ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hsv; exact zero_ne_one hsv
  have ha0 : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hav; exact zero_ne_one hav
  have hkk : Units.mk0 k hk0 * Units.mk0 _ hs0 = Units.mk0 _ ha0 := Units.ext h
  have hk1 : ξ.locK PP (Units.mk0 k hk0) = 1 := by
    have := congrArg (ξ.locK PP) hkk
    rwa [map_mul, key _ hs (Units.mk0 _ hs0) rfl, key _ ha (Units.mk0 _ ha0) rfl, mul_one] at this
  set y := Formalism.L2.Host.atFin PP (Units.mk0 k hk0) with hy
  have hyv : (y : PP.adicCompletion D.host.E) = algebraMap D.host.E (PP.adicCompletion D.host.E) k := rfl
  have ht := hK.tame PP (y * x⁻¹) (by
    unfold Formalism.L2.Host.IsUnitAt at *
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hyv, hv, hx, inv_one, mul_one]) (by
    have e : ((y * x⁻¹ : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) - 1 =
        (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) * (x : PP.adicCompletion D.host.E)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hyv, sub_mul, mul_inv_cancel₀ x.ne_zero]
    unfold Formalism.L2.Host.IsUnitAt at hx
    rw [e, map_mul, map_inv₀, hx, inv_one, mul_one]
    have hlt : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) < 1 := hk
    generalize Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) = z at hlt
    rcases eq_or_ne z 0 with rfl | hz
    · exact zero_le'
    · rw [← WithZero.exp_log hz] at hlt ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      rw [WithZero.exp_le_exp]
      push_cast
      omega)
  have hk2 : ξ.loc PP y = 1 := hk1
  rw [map_mul, hk2, one_mul, map_inv, inv_eq_one] at ht
  exact ht

end GlobalTheory.BaseCmp

namespace GlobalTheory.BaseCmp


open Classical in
theorem liftKer_of_ne : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle)
    (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ),
    KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ Q → IsTypeVec R i eg fg →
    ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
      ∃ Gc : ℂ, UnitOff N Gc ∧ IsSBHalf eQ (lattice₂ R i) (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) ∧
        ∀ Tm, IsModel R i eQ fg Tm → φ = Tm (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i hV ξ χ ξR Q ω φ hK hQ N hN hNQ eg eQ fg hg hq hfg ϖ hϖ0 hϖ
  have hθ := kerDat_twoStep hC hK hQ hg hq hfg
  obtain ⟨Y, a, Gc, hU, hY, hΦ, hS⟩ := _root_.GlobalTheory.LiftFour.datum_conj_half_fourier D G Pl0 T0 A Ks R F hC hG i hV ξR Q hQ
    (kerDat_xiR_ne D G Pl0 T0 A Ks R F hC i ξ χ ξR Q ω φ hK) N hN hNQ eQ hq ϖ hϖ0 hϖ
  refine ⟨Gc, hU, _root_.GlobalTheory.DilFlat.isSBHalf_dilFlat D G Pl0 T0 A Ks R F hC hG i hV ξR Q hQ eQ hq ϖ hϖ0 hϖ Gc, fun Tm hTm => ?_⟩
  have h1 := GlobalTheory.DatumFourier.thetaAt_eq_sum (fun q : Y => q.1) (fun q : Y => a q.1) hθ
    (fun q => by rw [GlobalTheory.LatVac.cA_cA]; exact hY q.1 q.2)
    (fun t => by rw [hΦ t]; congr 1; exact (Finset.sum_coe_sort Y fun y => a y * R.ψ (symplO (Vc D i) (Wc D i) t y)).symm)
  have h2 : (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) =
      ∑ y ∈ Y, a y • fun t => halfInd eQ (lattice₂ R i) (t + y) := by
    funext t
    rw [← hS t, Finset.sum_apply]
    rfl
  have hvac : Tm (halfInd eQ (lattice₂ R i)) = fg := by simpa using hTm.vac
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, h2, map_sum, ← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, hTm.trans _ (GlobalTheory.isSBHalf_halfInd eQ (lattice₂ R i)) _ (hY q.1 q.2), hvac]

end GlobalTheory.BaseCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLabelClassZeroOfDividesAllThetaConstants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.DivInt

theorem ratio {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ) {a : X₁.S.Gam} (ha : X₁.M.Div X₁.S.th a z₁) (b : X₁.S.Gam) :
    ∃ v : V, 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ = algebraMap V (FractionRing V) v * 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ := by
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  set yC : Sp V ⟶ X₁.M.Z := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hyC
  have hC : yC (closedPoint V) ⤳ z₁ := sp _
  set y : Sp (FractionRing V) ⟶ X₁.M.Z := jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy
  set ξ := y (closedPoint (FractionRing V)) with hξ
  have hyξ : ∀ w, y w ⤳ ξ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hξz : ξ ⤳ z₁ := sp _
  have hr : X₁.S.th b / X₁.S.th a ∈ X₁.M.O z₁ := ha.2 b
  have hrξ : X₁.S.th b / X₁.S.th a ∈ X₁.M.O ξ := RatModel.O_le_of_specializes hξz hr
  have haξ : X₁.S.th a ∈ X₁.M.O ξ := 𝔪.reg _ (X₁.S.th_mem a)
  refine ⟨RatModel.valLoc yC z₁ hC ⟨_, hr⟩, ?_⟩
  have e1 : X₁.S.th b = X₁.S.th b / X₁.S.th a * X₁.S.th a := (div_mul_cancel₀ _ ha.1).symm
  have e2 : X₁.M.val y (X₁.S.th b / X₁.S.th a) = algebraMap V (FractionRing V) (RatModel.valLoc yC z₁ hC ⟨_, hr⟩) :=
    RatModel.val_spMap_comp (algebraMap V (FractionRing V)) yC hC ⟨_, hr⟩
  rw [𝔪.yK_eq, 𝔪.yK_eq]
  show X₁.M.val y (X₁.S.th b) = _ * X₁.M.val y (X₁.S.th a)
  rw [← e2, ← RatModel.val_mul hyξ hrξ haξ, ← e1]

theorem label_zero_of_mem_supI : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → 𝔪.YY a 0 := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 a ha
  have ha' : X₁.M.Div X₁.S.th a z₁ := ha
  obtain ⟨b₀, hb₀⟩ := _root_.GlobalTheory.Poinc.Sep.UMem.exists_th_ne_zero g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  have hane : 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := ratio 𝔪 ha' b₀
    rw [h0, mul_zero] at hv
    exact hb₀ hv
  obtain ⟨ν, hν1, hνm⟩ := GlobalTheory.T.exists_discreteValuation_centred_completeNormal V 𝔪.cn
  have hmax : ∀ b, ν (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) ≤ ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) := fun b => by
    obtain ⟨v, hv⟩ := ratio 𝔪 ha' b
    rw [hv, map_mul]
    exact mul_le_of_le_one_left' (hν1 v)
  obtain ⟨w, hw, hle⟩ := GlobalTheory.T.thetaConstant_le_commonBound_monomial g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 ν hν1 hνm _ hmax a
  have h0 : ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2) ≠ 0 :=
    pow_ne_zero _ ((Valuation.ne_zero_iff ν).2 hane)
  have h1 : 1 ≤ ν (algebraMap V (FractionRing V) (mono W t δ w)) := by
    have := mul_le_mul_of_nonneg_left hle
      (zero_le' : (0 : WithZero (Multiplicative ℤ)) ≤ (ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2))⁻¹)
    rwa [← _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.one_mul] at this
  by_cases hw0 : w = 0
  · exact hw0 ▸ hw
  · exact absurd h1 (not_le.2 (hνm _ (𝔪.mono_mem hw0)))

end GlobalTheory.Poinc.Sep.DivInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRealisationLabelsInjectiveOfGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem realPt_comp_pow {S : Scheme.{0}} {A T T₀ : Over S} [GrpObj A] (u : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) :
    u ≫ x ^ n = (u ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem realPt_inj_of_grpPullback : ∀ {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₂ : ThetaSys o₂ Ω₂) (ρ₂ : S₂.Real) {T : Scheme.{0}} (G : Over T) [GrpObj G] (f : Sp S₂.R ⟶ T) (φ : ρ₂.P.A.left ⟶ G.left), IsGrpPullback ρ₂.P.A G f φ → ∀ x y : S₂.Gam, (ρ₂.pt x).left ≫ φ = (ρ₂.pt y).left ≫ φ → x = y := by
  intro o₂ Ω₂ _ _ _ S₂ ρ₂ T G _ f φ hφ x y hxy
  have hpt : ρ₂.pt x = ρ₂.pt y := by
    ext
    exact hφ.1.hom_ext hxy (by simp only [Category.assoc, Over.w])
  have hzero : ρ₂.pt 0 = 1 := by
    have h := ρ₂.pt_add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hsmul : ∀ (a : S₂.Gam) (n : ℕ), ρ₂.pt (n • a) = ρ₂.pt a ^ n := by
    intro a n
    induction n with
    | zero => rw [zero_smul, pow_zero, hzero]
    | succ n ih => rw [succ_nsmul, ρ₂.pt_add, ih, pow_succ]
  have hkill : ∀ a : S₂.Gam, ρ₂.pt a ^ (S₂.r * S₂.N) = 1 := by
    intro a
    rw [← hsmul]
    have : (S₂.r * S₂.N) • a = 0 := by
      funext i
      simp [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self]
    rw [this, hzero]
  let K := AlgebraicClosure Ω₂
  let x₀ : Sp K ⟶ Sp S₂.R := spMap ((algebraMap Ω₂ K).comp (S₂.R.val : S₂.R →+* Ω₂))
  let u : Over.mk x₀ ⟶ baseOver (Sp S₂.R) := Over.homMk x₀ (by simp)
  have hz : (u ≫ ρ₂.pt x) ^ (S₂.r * S₂.N) = 1 := by
    rw [← realPt_comp_pow, hkill, MonObj.comp_one]
  obtain ⟨a, _, huniq⟩ := ρ₂.pt_bij K x₀ (u ≫ ρ₂.pt x) hz
  have h1 := huniq x rfl
  have h2 := huniq y (by rw [hpt])
  exact h1.trans h2.symm

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalBoundaryLocalEquation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdEquation
open GlobalTheory.Cartier GlobalTheory.ZH GlobalTheory.FlagBundle

theorem dvd_pow_of_vanishing {Y : Scheme.{0}} (O V : Y.Opens) (t : Γ(Y, V))
    (ht : ∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ O) (W : Y.Opens) (hW : W ≤ V) (f : Γ(Y, W))
    (hf : ∀ z (hz : z ∈ W), z ∉ O → ger z hz f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z))
    (z : Y) (hz : z ∈ W) : ∃ n : ℕ, ger z (hW hz) t ∣ ger z hz f ^ n := by
  obtain ⟨A, hA, hzA, e⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hz
  have hA' : IsAffineOpen A := hA
  let f' : Γ(Y, A) := Y.presheaf.map (homOfLE e).op f
  let t' : Γ(Y, A) := Y.presheaf.map (homOfLE (e.trans hW)).op t
  have hle : Y.basicOpen f' ≤ Y.basicOpen t' := by
    intro x hx
    have hxA : x ∈ A := Y.basicOpen_le _ hx
    rw [Y.mem_basicOpen _ x hxA] at hx ⊢
    rw [Y.presheaf.germ_res_apply] at hx ⊢
    refine (ht x _).2 ?_
    by_contra hO
    exact hf x (e hxA) hO hx
  have h2 : PrimeSpectrum.basicOpen f' ≤ PrimeSpectrum.basicOpen t' := by
    rw [← hA'.fromSpec_preimage_basicOpen, ← hA'.fromSpec_preimage_basicOpen]
    exact fun x hx => hle hx
  obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_le_basicOpen_iff _ _).1 h2
  have h3 := map_dvd (Y.presheaf.germ A z hzA).hom (Ideal.mem_span_singleton.1 hn)
  rw [map_pow] at h3
  refine ⟨n, ?_⟩
  rw [← Y.presheaf.germ_res_apply (homOfLE (e.trans hW)) z hzA t, ← Y.presheaf.germ_res_apply (homOfLE e) z hzA f]
  exact h3

theorem exists_section {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (hD : D.Eff)
    (hr : ∀ (y : X) (g : X.functionFieldˣ), D.IsEqn y g → ∀ (f : X.functionField) (n : ℕ), RegAt y f →
      RegAt y (f ^ n / g) → RegAt y (f / g)) (y : X) :
    ∃ (V : X.Opens) (_ : y ∈ V) (t : Γ(X, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∉ D.supp) ∧
      ∀ z (hz : z ∈ V) (b : X.presheaf.stalk z) (n : ℕ), ger z hz t ∣ b ^ n → ger z hz t ∣ b := by
  obtain ⟨U, hyU, g, hg⟩ := D.exists_isEqn_nhds y
  obtain ⟨a, ha⟩ := (hg y hyU).regularAt_iff.1 (hD y)
  rw [one_mul] at ha
  obtain ⟨W, hyW, s, rfl⟩ := X.presheaf.germ_exist a
  have inj := fun z : X => IsFractionRing.injective (X.presheaf.stalk z) X.functionField
  have key : ∀ z (hz : z ∈ W ⊓ U), algebraMap _ X.functionField
      (ger z hz (X.presheaf.map (homOfLE inf_le_left).op s)) = g := fun z hz => by
    refine Eq.trans ?_ ((algebraMap_germ hz.1 s).trans ((algebraMap_germ hyW s).symm.trans ha))
    exact congrArg _ (X.presheaf.germ_res_apply (homOfLE inf_le_left) z hz s)
  refine ⟨W ⊓ U, ⟨hyW, hyU⟩, X.presheaf.map (homOfLE inf_le_left).op s, fun z hz => ?_, fun z hz b n hb => ?_⟩
  · rw [(hg z hz.2).mem_supp_iff, not_not]
    refine ⟨fun h => ⟨_, h, key z hz⟩, fun ⟨u, hu, e⟩ => ?_⟩
    rwa [inj z (e.trans (key z hz).symm)] at hu
  · obtain ⟨c, hc⟩ := hb
    obtain ⟨d, hd⟩ := hr z g (hg z hz.2) (algebraMap _ X.functionField b) n ⟨b, rfl⟩ ⟨c, by
      rw [eq_div_iff g.ne_zero, ← map_pow, hc, map_mul, key z hz, mul_comm]⟩
    refine ⟨d, inj z ?_⟩
    rw [map_mul, key z hz, hd, mul_div_cancel₀ _ g.ne_zero]

theorem exists_reduced_equation : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, y ∉ U₀ TF.X Z → ∃ (V : (Y₀ TF.X Z).Opens) (_ : y ∈ V) (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) ∧ (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) := by
  intro _ E _ _ _ H Dw l Xo c T Z hF _ y _
  have hsm := GlobalTheory.VarFlag.smooth_gen T.smooth
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) T.Y c.F (RingEquiv.refl _) hF hsm
  have := (hB Z).1
  obtain ⟨C, f, hπ, -, hl⟩ :=
    GlobalTheory.FlagBundle.exists_flagCpt T.Y (RingEquiv.refl _) (_root_.GlobalTheory.VarFlag.snc_genBdIdeal_of_snc_boundary T.snc) (B Z) (j Z) (hB Z).2.2.1
  obtain ⟨h, hiso, hh, -, -⟩ := GlobalTheory.CompProport.exists_iso T Z B j hB hcov C f hπ hl
  have hmem : ∀ z : Y₀ T.X Z, h z ∉ CartierDiv.supp C.bd ↔ z ∈ U₀ T.X Z := fun z => by
    have e : GlobalTheory.Toroidal.genι T.Y (C.π (h z)) = T.X.π (inc₀ T.X Z z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hh]
    refine (not_congr (C.bd_supp (h z))).trans (not_not.trans ?_)
    change C.π (h z) ∈ Set.range T.Y.jQ ↔ T.X.π (inc₀ T.X Z z) ∈ Set.range T.Y.j
    refine exists_congr fun x => ?_
    rw [← e, Model.j, Scheme.Hom.comp_apply]
    exact (GlobalTheory.Toroidal.genι T.Y).isOpenEmbedding.injective.eq_iff.symm
  obtain ⟨V, hyV, t, ht, hrad⟩ := exists_section C.bd C.bd_eff C.bd_red (h y)
  have hg : ∀ z (hz : z ∈ h ⁻¹ᵁ V), ger z hz (h.app V t) = (h.stalkMap z).hom (ger (h z) hz t) :=
    fun z hz => (Scheme.Hom.germ_stalkMap_apply h V z hz t).symm
  have hu : ∀ z (hz : z ∈ h ⁻¹ᵁ V), IsUnit (ger z hz (h.app V t)) ↔ z ∈ U₀ T.X Z := fun z hz => by
    rw [hg, isUnit_map_iff]
    exact (ht (h z) hz).trans (hmem z)
  refine ⟨h ⁻¹ᵁ V, hyV, h.app V t, hu, fun W hW s hs z hz => ?_⟩
  obtain ⟨n, c', hc⟩ := dvd_pow_of_vanishing _ _ _ hu W hW s hs z hz
  have hb := GlobalTheory.BoundaryDivisor.stalkMap_bijective h z
  obtain ⟨b, hb'⟩ := hb.2 (ger z hz s)
  obtain ⟨c'', rfl⟩ := hb.2 c'
  rw [hg, ← hb', ← map_pow, ← map_mul] at hc
  rw [hg, ← hb']
  exact map_dvd _ (hrad _ _ b n ⟨c'', hb.1 hc⟩)

end GlobalTheory.BdEquation
end
end

