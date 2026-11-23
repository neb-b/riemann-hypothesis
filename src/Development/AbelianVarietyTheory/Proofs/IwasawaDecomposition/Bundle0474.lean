module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0017
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.CoordRat
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphismCongrOneOnAdjoinRootUniformiser
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

open Polynomial

namespace GlobalTheory.RootOfUniformiserDVR

theorem val_term_le_one' {F : Type} [Field F] {O : ValuationSubring F} {β : Type} (s : Finset β) (f : β → F)
    (hf : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → O.valuation (f i) = O.valuation (f j) → i = j)
    (hs : O.valuation (∑ i ∈ s, f i) ≤ 1) : ∀ i ∈ s, O.valuation (f i) ≤ 1 := by
  classical
  intro i hi
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => O.valuation (f i)) ⟨i, hi⟩
  by_cases h0 : f j = 0
  · refine (hmax i hi).trans ?_
    simp [h0]
  refine (hmax i hi).trans ?_
  rw [← Finset.add_sum_erase s f hj] at hs
  rwa [Valuation.map_add_eq_of_lt_left] at hs
  refine Valuation.map_sum_lt _ (by simpa using h0) fun k hk => ?_
  rw [Finset.mem_erase] at hk
  exact lt_of_le_of_ne (hmax k hk.2) fun he => hk.1 (hf j hj k hk.2 h0 he.symm).symm

theorem cong_on_adjoin : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (F : Type) [Field F]
    [Algebra (FractionRing W) F] [Algebra W F] [IsScalarTower W (FractionRing W) F]
    (O : ValuationSubring F),
    (∀ w : W, algebraMap W F w ∈ O) → (∀ w ∈ maximalIdeal W, algebraMap W F w ∈ O.nonunits) →
    ∀ (ϖ : W), Irreducible ϖ → ∀ (l : ℕ), l ≠ 0 → ∀ (x : F), x ^ l = algebraMap W F ϖ →
    ∀ (g : F ≃ₐ[FractionRing W] F) (b : F), b ∈ IntermediateField.adjoin (FractionRing W) {x} →
    O.valuation b ≤ 1 → O.valuation (g b - b) < 1 := by
  intro W _ _ _ F _ _ _ _ O hO hm ϖ hϖ l hl0 x hx g b hb hb1
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  set ϖK : FractionRing W := algebraMap W (FractionRing W) ϖ with hϖK
  have hx' : x ^ l = algebraMap (FractionRing W) F ϖK := by
    rw [hx, hϖK, ← IsScalarTower.algebraMap_apply]
  have hunit : ∀ u : Wˣ, O.valuation (algebraMap W F (u : W)) = 1 := by
    intro u
    have a1 := (O.valuation_le_one_iff _).2 (hO u)
    have a2 := (O.valuation_le_one_iff _).2 (hO ((u⁻¹ : Wˣ) : W))
    have e : O.valuation (algebraMap W F (u : W)) * O.valuation (algebraMap W F ((u⁻¹ : Wˣ) : W)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    refine le_antisymm a1 ?_
    by_contra hc
    push_neg at hc
    have := mul_lt_one_of_lt_of_le hc a2
    rw [e] at this
    exact lt_irrefl _ this
  have hϖlt : O.valuation (algebraMap W F ϖ) < 1 := by
    have := hm ϖ ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit)
    exact this
  have hWv : ∀ w : W, w ≠ 0 → ∃ n : ℕ,
      O.valuation (algebraMap W F w) = O.valuation (algebraMap W F ϖ) ^ n := by
    intro w hw
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw hϖ
    exact ⟨n, by rw [map_mul, map_mul, hunit, _root_.one_mul, map_pow, map_pow]⟩

  have hvpos : ∀ w : W, w ≠ 0 → O.valuation (algebraMap W F w) ≠ 0 := by
    intro w hw
    rw [Valuation.ne_zero_iff]
    intro h0
    apply hw
    have : algebraMap W (FractionRing W) w = 0 := by
      rw [IsScalarTower.algebraMap_apply W (FractionRing W) F] at h0
      exact (map_eq_zero _).mp h0
    exact (IsFractionRing.injective W (FractionRing W)) (by rw [this, map_zero])
  have hK : ∀ a : FractionRing W, a ≠ 0 → ∃ m : ℤ,
      O.valuation (algebraMap (FractionRing W) F a) = O.valuation (algebraMap (FractionRing W) F ϖK) ^ m := by
    intro a ha
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := W) a
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hp0 : p ≠ 0 := by rintro rfl; simp at ha
    obtain ⟨n, hn⟩ := hWv p hp0
    obtain ⟨k, hk⟩ := hWv q hq0
    refine ⟨(n : ℤ) - k, ?_⟩
    rw [map_div₀, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hϖK,
      ← IsScalarTower.algebraMap_apply, hn, hk, zpow_sub₀ (hvpos ϖ hϖ0), zpow_natCast, zpow_natCast]
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hl0, eq_comm] at hx
    exact hvpos ϖ hϖ0 (by rw [hx, map_zero])
  set t := O.valuation x with ht
  have htl : O.valuation (algebraMap (FractionRing W) F ϖK) = t ^ l := by rw [← hx', map_pow]
  have ht0 : 0 < t := zero_lt_iff.mpr (by simpa [ht] using hx0)
  have ht1 : t < 1 := by
    have := hϖlt
    rw [IsScalarTower.algebraMap_apply W (FractionRing W) F, ← hϖK, htl] at this
    exact (pow_lt_one_iff hl0).mp this
  have hinj : Function.Injective fun n : ℤ => t ^ n := zpow_right_injective₀ ht0 ht1.ne
  have hval : ∀ (a : FractionRing W) (i : ℕ), algebraMap (FractionRing W) F a * x ^ i ≠ 0 →
      ∃ m : ℤ, O.valuation (algebraMap (FractionRing W) F a * x ^ i) = t ^ ((i : ℤ) + l * m) := by
    intro a i ha
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    obtain ⟨m, hm⟩ := hK a ha0
    refine ⟨m, ?_⟩
    rw [map_mul, hm, htl, map_pow, zpow_add₀ ht0.ne', zpow_mul, zpow_natCast, zpow_natCast, mul_comm]
  have hmod : ∀ (i j : ℕ) (m n : ℤ), i < l → j < l → t ^ ((i : ℤ) + l * m) = t ^ ((j : ℤ) + l * n) →
      i = j := by
    intro i j m n hi hj he
    have := congrArg (· % (l : ℤ)) (hinj he)
    simp only [Int.add_mul_emod_self_left] at this
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at this
    omega
  have hq : (X ^ l - C ϖK).Monic := monic_X_pow_sub_C _ hl0
  have hint : IsIntegral (FractionRing W) x := ⟨X ^ l - C ϖK, hq, by simp [hx']⟩
  have hb' : b ∈ Algebra.adjoin (FractionRing W) {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]; exact hb
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb'
  obtain ⟨p₀, rfl⟩ := hb'
  set p := p₀ %ₘ (X ^ l - C ϖK)
  have hp : aeval x p = aeval x p₀ := aeval_modByMonic_eq_self_of_root (by simp [hx'])
  have hdeg : p.natDegree < l := by
    have := natDegree_modByMonic_lt p₀ hq (by
      intro h1
      have := congrArg natDegree h1
      rw [natDegree_X_pow_sub_C _, natDegree_one] at this
      exact hl0 this)
    rwa [natDegree_X_pow_sub_C _] at this
  change O.valuation (aeval x p₀) ≤ 1 at hb1
  change O.valuation (g (aeval x p₀) - aeval x p₀) < 1
  rw [← hp, aeval_eq_sum_range' hdeg] at hb1 ⊢
  simp only [Algebra.smul_def] at hb1 ⊢
  have hle := val_term_le_one' _ _ (fun i hi j hj h0 he => by
    obtain ⟨m, hm⟩ := hval _ i h0
    obtain ⟨n, hn⟩ := hval (p.coeff j) j (by
      intro h00
      rw [h00, map_zero] at he
      exact h0 (by simpa using he))
    exact hmod i j m n (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (by rw [← hm, ← hn, he])) hb1
  have hgx : O.valuation (g x) = t := by
    refine (pow_left_injective hl0 : Function.Injective (fun a : O.ValueGroup => a ^ l)) ?_
    show _ ^ l = t ^ l
    rw [← map_pow, ← map_pow, hx', g.commutes, htl]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  have hlt : O.valuation (algebraMap (FractionRing W) F (p.coeff i) * x ^ i) < 1 := by
    refine lt_of_le_of_ne (hle i hi) fun he => ?_
    obtain ⟨m, hm⟩ := hval (p.coeff i) i (by intro h0; simp [h0] at he)
    have := hmod i 0 m 0 (Finset.mem_range.mp hi) (by omega) (by rw [← hm, he]; simp)
    omega
  refine Valuation.map_sub_lt _ ?_ hlt
  rw [map_mul g, g.commutes, map_pow g, map_mul, map_pow, hgx]
  rwa [map_mul, map_pow] at hlt

end GlobalTheory.RootOfUniformiserDVR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelComplexPointsInjectiveExtendedData
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftInj

section Conc

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem baseLevelComplexPoints_injective_of_independent (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool) (i : Fin D.R.m)
    (hU : ∀ (n : ℕ) (c : Fin n → (Fin (R.nW i) → D.what₂.LL)), LinearIndependent D.what₂.LL c →
      LinearIndependent ℂ fun k => (R.FW i).j (sg0 D A3.A) (c k)) :
    Function.Injective ((R.toCx3 F).w0C b i) := by
  have hb : LinearIndependent D.what₂.LL (R.toRealDat.bL F.lv2 b i) :=
    (Module.finBasis D.what₂.LL (R.toRealDat.WL F.lv2 b i)).linearIndependent.map' (R.toRealDat.WL F.lv2 b i).subtype
      (Submodule.ker_subtype _)
  refine (injective_iff_map_eq_zero _).2 fun c hc => funext fun l => ?_
  have h1 := Fintype.linearIndependent_iff.1 (hU _ _ hb) _ ((Formalism.IndefR.FWT.principal_form_tensor_expansion R F b i c).symm.trans hc) l
  have h2 := congrArg (Links.cj (twAt D.what₂.embLL A3.A.v0)) h1
  rwa [cj_cj, map_zero] at h2

end Conc


set_option maxHeartbeats 1000000 in
theorem baseLevelComplexPoints_injective_extendedData : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        Function.Injective ((z'.R.toCx3 z'.F).w0C false j')) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ => ?_
  intro B f T w _ _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' hF _ _ j' _ _ _
  exact baseLevelComplexPoints_injective_of_independent z'.R z'.F false j'
    (GlobalTheory.TiedUnif.indep_span_of_tie z'.geo.fw z'.pins.char.base.models.HW z'.geo.bar hF.2.1.jUnif j' _).1

end GlobalTheory.Mem.R3.LiftInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelLiftExtendedDataEqMapSmallerField
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC

theorem unipotentBaseLevelChar_map_coefficientField {E : Type} [Field E] [NumberField E] {K K' : Type} [Field K] [Field K'] (φ : K →+* K') (Pg : Finset (Pl E)) (r : ℕ)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) K) (ψ' : ∀ PP : Pl E, AddChar (kP PP) K') (h : ∀ PP c, ψ' PP c = φ (ψ PP c))
    (g : G0 Pg r) (hg : g ∈ (P0 Pg r ψ).H) (hg' : g ∈ (P0 Pg r ψ').H) :
      ((((P0 Pg r ψ').chi⁻¹ ⟨g, hg'⟩ : K'ˣ)) : K') = φ (((P0 Pg r ψ).chi⁻¹ ⟨g, hg⟩ : Kˣ) : K) := by
  simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
  congr 1
  unfold P0 LevelP.ofLocal at *
  dsimp only
  rw [MonoidHom.finsetProd_apply, MonoidHom.finsetProd_apply, Units.coe_prod, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun PP _ => ?_
  exact h _ _

theorem exists_int_of_mem_vGs {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} (hPr : Pr.Ok) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ Pr.vGs) (x : 𝓞 X.E ⧸ P.asIdeal) : ∃ b : ℤ, x = b := by
  classical
  have h : ∃ i, P ∈ Pr.vG i := by
    unfold Formalism.L2.Col.Primes.vGs at hP
    rcases Finset.mem_union.1 hP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := h
  have hc : Nat.card (𝓞 X.E ⧸ P.asIdeal) = Pr.g i := by
    rw [← hPr.vG_norm i P hi, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 X.E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ (hPr.g_prime i).ne_zero)
  exact Formalism.L2.Col.owedC_exists_int (hPr.g_prime i) hc x

theorem baseLevels_correspond_weilAdditiveChars {B B' : Base} {px : PreX B.toPre} {px' : PreX B'.toPre} (I : ColIn B px) (I' : ColIn B' px')
    (hB : B'.toPre = B.toPre) (hpx : HEq px' px) (hPr : (B.primes px).Ok) (hw : I.Ch.WeilTied B.embLL B.host.xi0)
    (hw' : I'.Ch.WeilTied B'.embLL B'.host.xi0)
    (φ : B.LL →+* B'.LL) (hφ : ∀ x, B'.embLL (φ x) = B.embLL x) (e : Gc B px ≃* Gc B' px') (he : ∀ g, HEq (e g) g) :
    ∃ hP : lev0 I' = (lev0 I).map e.toMonoidHom, ∀ h : lev0 I,
      (((chr0 I')⁻¹ ⟨e h, hP ▸ Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : B'.LLˣ) : B'.LL) =
        φ (((chr0 I)⁻¹ h : B.LLˣ) : B.LL) := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  obtain rfl : px' = px := eq_of_heq hpx
  have he' : e = MulEquiv.refl _ := MulEquiv.ext fun g => eq_of_heq (he g)
  subst he'
  refine ⟨(Subgroup.map_id _).symm, fun h => ?_⟩
  refine unipotentBaseLevelChar_map_coefficientField φ _ _ (psiC I) (psiC I') (fun PP c => ?_) h.1 h.2 h.2
  unfold psiC
  split_ifs with hP hQ hQ
  · obtain ⟨b, hb⟩ := exists_int_of_mem_vGs hPr hP (Formalism.L2.Col.redP PP P'.host.xi0 * c)
    apply RingHom.injective (Base.embLL _)
    exact (hw' ⟨PP, hP⟩ c b hb).trans ((hφ _).trans (hw ⟨PP, hP⟩ c b hb)).symm
  · exact absurd hP hQ
  · exact absurd hQ hP
  · rw [AddChar.one_apply, AddChar.one_apply, map_one]


set_option maxHeartbeats 2000000 in
theorem lev_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (e : Gc B w.px ≃* Gc B' w'.px), (∀ g, HEq (e g) g) → ∃ hP : ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0).P = ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).P.map e.toMonoidHom, ∀ h : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).P, ((((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.lvlA z'.F.P0 z'.F.ψ0).ψ ⟨e h, hP ▸ Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.lvlA z.F.P0 z.F.ψ0).ψ h : (w.st Z).toD7.what₂.LL)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' _ φ hφ e he => ?_
  exact baseLevels_correspond_weilAdditiveChars w.I w'.I hE.1 hpx w.l.pr w.ok.weil w'.ok.weil φ hφ e he

end GlobalTheory.Mem.R3.DefLatBC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelLiftMatrixSolvesRelationExtendedData
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftMatBase

section Gen

open Formalism.IndefR.CxPass LevelOperators

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3}
  {P1 : Subgroup G} {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}

theorem dnLevL_of_ratZL {s : ℕ} (hok : A3.fam3.Ok3 s) {gW : ∀ j, Representation ℂ G (X.W j)}
    (Hs : ∀ j t, Hyp A3.fam3.base3.v0.embedding (X.jL j t) (A3.fam3.F.L j t).r (fun g => X.opLC j t (Sum.inr g)) (gW j)
      (X.θ' j t))
    (hRZ : ∀ j t, Submodule.span ℂ ((X.jL j t) '' (X.Zl j t : Set (A3.fam3.amb3.FL j t))) =
      LinearMap.range (LinearMap.adjoint (X.θ' j t)))
    {cv : CrdV A3.fam3.amb3} {b : Bool} (P : Subgroup G) (ψ : P →* Kˣ)
    (hv : ∀ j t, cv.v0L X.zs b j t = BlockGood.goodR (A3.fam3.F.L j t) (A3.fam3.F.lvlA P ψ))
    (hE : LevelTypeOfLifts A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW b P ψ) :
    X.DnLevL cv b := by
  intro j t
  rintro _ ⟨u, hu, rfl⟩
  have hu0 : u ∈ Submodule.span ℂ (X.jL j t '' (BlockGood.goodR (A3.fam3.F.L j t) (A3.fam3.F.lvlA P ψ) : Set _)) := by
    have := hu
    unfold CxData.goodPartComplexPoints at this
    rwa [hv j t] at this
  rw [lift_good_part_complex_eq_range_family (Hs j t) (hv j t)] at hu
  rw [hE j]
  refine ⟨?_, ?_⟩
  · have hle : LinearMap.range (opV A3.fam3.base3.v0.embedding (fun g => X.opLC j t (Sum.inr g))
          (goodAt (A3.fam3.F.lvlA P ψ).X (A3.fam3.F.lvlA P ψ).P (A3.fam3.F.lvlA P ψ).ψ)) ≤
        LinearMap.range (opV A3.fam3.base3.v0.embedding (fun g => X.opLC j t (Sum.inr g))
          (goodAt (A3.fam3.F.lvlA ⊥ 1).X (A3.fam3.F.lvlA ⊥ 1).P (A3.fam3.F.lvlA ⊥ 1).ψ)) := by
      have e1 : goodAt (A3.fam3.F.lvlA ⊥ 1).X (A3.fam3.F.lvlA ⊥ 1).P (A3.fam3.F.lvlA ⊥ 1).ψ = idemOf A3.fam3.F.X :=
        goodAt_bot A3.fam3.F.X _
      rw [e1]
      exact (Hs j t).range_le A3.fam3.F.X P ψ⁻¹
    obtain ⟨u', hu', hΘ⟩ := (Hs j t).dn _ (opF_goodAt_idem _ (A3.fam3.F.lvlA ⊥ 1).X hok.ok2.irr _ _) (hle hu)
    rw [← (Hs j t).ratLev (hRZ j t) _ (opF_goodAt_idem _ (A3.fam3.F.lvlA ⊥ 1).X hok.ok2.irr _ _)] at hu'
    have hZeq : ((LinearMap.range (LinearMap.adjoint (X.θ' j t))).comap (X.jL j t) ⊓
          LinearMap.range (opF (A3.fam3.F.L j t).r (goodAt (A3.fam3.F.lvlA ⊥ 1).X (A3.fam3.F.lvlA ⊥ 1).P (A3.fam3.F.lvlA ⊥ 1).ψ))) =
        LinearMap.range ((A3.fam3.F.L j t).toF (A3.fam3.F.lvlA ⊥ 1) (X.Zl j t)) := by
      rw [range_toF, goodR_eq]
      rfl
    rw [hZeq] at hu'
    have h2 : Submodule.span ℂ (X.jL j t '' (LinearMap.range ((A3.fam3.F.L j t).toF (A3.fam3.F.lvlA ⊥ 1) (X.Zl j t)) :
          Set _)) ≤ LinearMap.range (lin (X.uL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t)) := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨cpt A3.fam3.base3.v0.embedding x, (X.jL_toL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t x).symm⟩
    obtain ⟨c, hc⟩ := h2 hu'
    show X.θ' j t u ∈ principalFormsSubspace A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) j
    refine Submodule.mem_iSup_of_mem t ?_
    rw [← hΘ, ← hc, ← X.tC_eq]
    exact ⟨c, rfl⟩
  · show X.θ' j t u ∈ typeSubspace A3 X j (gW j) P ψ⁻¹
    unfold typeSubspace
    rw [Submodule.mem_iInf]
    intro h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    refine (Hs j t).type (h : G) (((ψ⁻¹) h : Kˣ) : K) _ (fun x hx => ?_) hu0
    rw [goodR_eq] at hx
    exact opF_goodAt_type _ _ hok.ok2.irr P ψ⁻¹ h x hx

end Gen

section Conc

open Formalism.IndefR.CxPass

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem tC_single_mem (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hL : Rw.HoldsL R F)
    (j : Fin D.R.m) (k : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ j A3.A.μ0)) :
    (R.toCx3 F).tC F.cr false j A3.A.μ0 (Pi.single k 1) ∈ LinearMap.range ((R.toCx3 F).w0C false j) := by
  have kL := RealDat3.kFormL_of (F := F) hC.base.models
  have jL := RealDat3.jIsoL_of (F := F) hC.base.models
  have rz : ∀ j t, Submodule.span ℂ (((R.toCx3 F).jL j t) '' ((R.toCx3 F).Zl j t : Set (A3.fam3.amb3.FL j t))) =
      LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' j t)) := fun j t => by
    obtain ⟨N, ψ, hψ, hr⟩ := hL.liftTest j
    exact Formalism.IndefR.Rat.range_adjoint_rat A3.fam3.base3.v0.embedding ((R.toCx3 F).jL j t)
      ((cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1).hL j t) _ (kL j t).1 (kL j t).2 (jL j t) _ ψ hψ (fun i x => hr t i x)
  have hdn : (R.toCx3 F).DnLevL (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) false :=
    dnLevL_of_ratZL (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) hL.ok
      (fun j t => lift_hypotheses_of_unitary hL.ok kL (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) (fun _ _ _ _ => rfl) jL hL.gUnit.2 hL.gEquiv.2 j t)
      rz F.P0 F.ψ0 (fun _ _ => rfl) hL.levW
  rw [Formalism.IndefR.Cx.CxData.tC, Formalism.IndefR.Cx.lin_single]
  exact hdn j _ ⟨_, Submodule.subset_span ⟨_, lift_coordinates_in_good_part_family (P0 := F.P0) (ψ0 := F.ψ0) (P1 := F.P1) (ψ1 := F.ψ1)
    (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.toCx3 F) false j _ (Pi.single k 1), rfl⟩, rfl⟩

theorem liftMatC_isRat (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hL : Rw.HoldsL R F) (j : Fin D.R.m) :
    Formalism.IndefR.Cx.IsRat A3.fam3.base3.v0.embedding ((R.toCx3 F).liftMatC F.cr false j A3.A.μ0) := by
  intro i k
  obtain ⟨N, ψ, hψ, hr, hbase⟩ := hL.liftTestB j
  have hinj := (R.toCx3 F).principal_form_injective false (RealDat3.kForm_of (F := F) hL.unif false) (RealDat3.ewNorm false)
    (RealDat.nP_pos false) j
  have hmem := tC_single_mem R F hC hL j k
  obtain ⟨a, ha⟩ := Formalism.IndefR.Rat.coord_rat _ ψ hψ ((R.toCx3 F).w0C false j) hinj (fun i l => hbase i l)
    (Formalism.IndefR.Cx.solve ((R.toCx3 F).w0C false j) ((R.toCx3 F).tC F.cr false j A3.A.μ0 (Pi.single k 1)))
    (fun i' => by
      rw [Formalism.IndefR.Cx.solve_spec _ hmem, Formalism.IndefR.Cx.CxData.tC, Formalism.IndefR.Cx.lin_single]
      exact hr _ _ _) i
  exact ⟨a, by simpa [Formalism.IndefR.Cx.CxData.liftMatC, Formalism.IndefR.Cx.relMat] using ha⟩

theorem liftMatrix_computes_lift_rational (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hL : Rw.HoldsL R F) (j : Fin D.R.m)
    (x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ j A3.A.μ0) → D.what₂.LL) :
    (R.toCx3 F).w0C false j (Formalism.IndefR.Cx.cpt A3.fam3.base3.v0.embedding
        (((R.toCx3 F).liftMat F.cr false j A3.A.μ0).mulVec x)) =
      (R.toCx3 F).tC F.cr false j A3.A.μ0 (Formalism.IndefR.Cx.cpt A3.fam3.base3.v0.embedding x) := by
  rw [Formalism.IndefR.Cx.cpt_mulVec, Formalism.IndefR.Cx.CxData.liftMat, Formalism.IndefR.Cx.kMat_map _ (liftMatC_isRat R F hC hL j)]
  exact Formalism.IndefR.Cx.relMat_spec _ _ (tC_single_mem R F hC hL j) _

end Conc

set_option maxHeartbeats 12000000 in
theorem baseLevelLiftMatrix_solves_relation_extendedData : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL, (z.R.toCx3 z.F).w0C false j (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding ((s0Of z.R z.F).θ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 *ᵥ x)) = (z.R.toCx3 z.F).tC z.F.cr false j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding x)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ => ?_
  intro B f T w _ _ _ _ Z hX Wt z _ _ _ hHL _ _ _ _ _ _ _ _ _ _ _ _ _ x
  exact liftMatrix_computes_lift_rational z.R z.F z.pins.char hHL _ x

end GlobalTheory.Mem.R3.LiftMatBase
end
end

