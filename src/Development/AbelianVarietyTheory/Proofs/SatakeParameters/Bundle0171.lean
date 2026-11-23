module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0162
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0087
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Formalism.LocalRingCardinality.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDatumFrobeniusRestrictHostField
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.FrobPeriod

theorem norm_int_le_one {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖c (x : E)‖ ≤ 1 := by
  have hx : IsIntegral ℤ (c (x : E)) := map_isIntegral_int c x.isIntegral_coe
  have h : c (x : E) ∈ (NormedField.valuation (K := PadicAlgCl l)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).mem_of_integral
      hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem exists_comp_of_normal {E L : Type} [Field E] [Field L] [CharZero E] [CharZero L]
    [Normal ℚ E] (φ ψ : E →+* L) : ∃ g : E ≃ₐ[ℚ] E, ∀ x, ψ x = φ (g x) := by
  letI : Algebra E L := φ.toAlgebra
  haveI : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  refine ⟨AlgHom.restrictNormal' ψ.toRatAlgHom E, fun x => ?_⟩
  exact (AlgHom.restrictNormal_commutes ψ.toRatAlgHom E x).symm

theorem liesOver_of_mem {E : Type} [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime]
    (v : HeightOneSpectrum (𝓞 E)) (h : ((l : ℕ) : 𝓞 E) ∈ v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := by
  constructor
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl.out).irreducible
  refine hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change (algebraMap ℤ (𝓞 E) (l : ℤ)) ∈ v.asIdeal
  simpa using h

theorem card_quot_under {E : Type} [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime]
    (Q : Ideal (𝓞 E)) [h : Q.LiesOver (Ideal.span {(l : ℤ)})] :
    Nat.card (ℤ ⧸ Q.under ℤ) = l := by
  rw [← h.over, Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]

end GlobalTheory.FrobPeriod


open GlobalTheory.FrobPeriod in
theorem GlobalTheory.FrobPeriod.periodFrob_restrict : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (c : D.host.E →+* ↥K.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → ∀ (x : D.host.E) (y : ↥(K0 K)), algebraMap ↥(K0 K) ↥K.1 y = c x → algebraMap ↥(K0 K) ↥K.1 ((P.PD K).σ y) = c (D.host.sigmaOf (DV.frobG D l) x) := by
  intro D l _ P K c h2 hq hd x y hy
  have hlN : ¬ l ∣ D.host.condN := fun h => by
    rcases (D.host.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  let c' : D.host.E →+* PadicAlgCl l := K.1.val.toRingHom.comp c
  have hK : ∀ z, c' z ∈ K0 K := fun z =>
    IntermediateField.mem_inf.2 ⟨(c z).2, _root_.GlobalTheory.HostKur.host_image_mem_Kur D.host l h2 hq hd c' z⟩
  let c0 : D.host.E →+* ↥(K0 K) := c'.codRestrict (K0 K) hK
  have hc0 : ∀ z, ((c0 z : ↥(K0 K)) : PadicAlgCl l) = c' z := fun z => rfl
  have hyx : y = c0 x := Subtype.ext (congrArg (fun t : ↥K.1 => (t : PadicAlgCl l)) hy)
  let σ0 := (P.PD K).σ
  obtain ⟨g, hg⟩ := exists_comp_of_normal c0 ((σ0 : ↥(K0 K) →+* ↥(K0 K)).comp c0)
  obtain ⟨v, hvl, hv⟩ := _root_.GlobalTheory.LocPlace.exists_place_of_emb l D.host.E c'
  haveI := liesOver_of_mem l v hvl
  have hgl : ∀ z : 𝓞 D.host.E, g • z - z ^ l ∈ v.asIdeal := fun z => by
    refine (hv _).2 ?_
    have h := P.PD_σ K (c0 z) (by rw [hc0]; exact norm_int_le_one c' z)
    have e : ((g • z - z ^ l : 𝓞 D.host.E) : D.host.E) = g (z : D.host.E) - (z : D.host.E) ^ l := by
      push_cast
      rfl
    rw [e, map_sub, map_pow, ← hc0, ← hc0, ← hg]
    exact h
  set F := D.host.sigmaOf (DV.frobG D l) with hFdef
  have hF : ∀ z : 𝓞 D.host.E, F • z - z ^ l ∈ v.asIdeal := fun z => by
    have h := (_root_.GlobalTheory.FrobSign.frobG_isArithFrob_and_sign D l h2 hq hd).1 v.asIdeal z
    rw [card_quot_under l v.asIdeal] at h
    exact h
  have hin := (D.host.der.frob l hlN v.asIdeal).2.2.2
  have hgF : g * F⁻¹ = 1 := by
    refine (hin _).1 fun z => ?_
    have h := v.asIdeal.sub_mem (hgl (F⁻¹ • z)) (hF (F⁻¹ • z))
    have e : (g * F⁻¹) • z - z = g • F⁻¹ • z - (F⁻¹ • z) ^ l - (F • F⁻¹ • z - (F⁻¹ • z) ^ l) := by
      rw [mul_smul, smul_inv_smul]
      ring
    rw [e]
    exact h
  have hgF' : g = F := by simpa using mul_inv_eq_one.1 hgF
  subst hyx
  apply Subtype.ext
  change (((σ0 (c0 x) : ↥(K0 K)) : PadicAlgCl l)) = c' (F x)
  have := hg x
  simp only [RingHom.comp_apply] at this
  rw [show (σ0 (c0 x)) = c0 (g x) from this, hc0, hgF']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceOverPInducedByAlgebraicPadicEmbedding
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H

noncomputable section

namespace GlobalTheory.DatumJets.Place

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

theorem norm_int_le (ι : K →+* ℂ_[p]) (y : 𝓞 K) : ‖ι (y : K)‖ ≤ 1 :=
  GlobalTheory.MomPlace.norm_le_one_of_isIntegral_int (by
    convert map_isIntegral_int ι (RingOfIntegers.isIntegral_coe y)
    exact Subsingleton.elim _ _)

def smallIdeal (ι : K →+* ℂ_[p]) : Ideal (𝓞 K) where
  carrier := {y | ‖ι (y : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : ι ((a + b : 𝓞 K) : K) = ι (a : K) + ι (b : K) := by simp
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : ι ((c • a : 𝓞 K) : K) = ι (c : K) * ι (a : K) := by simp
    rw [this, norm_mul]
    have h1 := norm_int_le ι c
    nlinarith [norm_nonneg (ι (c : K)), norm_nonneg (ι (a : K))]

theorem mem_smallIdeal (ι : K →+* ℂ_[p]) (y : 𝓞 K) : y ∈ smallIdeal ι ↔ ‖ι (y : K)‖ < 1 := Iff.rfl

theorem smallIdeal_isPrime (ι : K →+* ℂ_[p]) : (smallIdeal ι).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro a b hab
    rw [mem_smallIdeal] at hab
    rw [mem_smallIdeal, mem_smallIdeal]
    have : ι ((a * b : 𝓞 K) : K) = ι (a : K) * ι (b : K) := by simp
    rw [this, norm_mul] at hab
    by_contra hcon
    push Not at hcon
    nlinarith [hcon.1, hcon.2]

theorem dvd_of_natCast_mem {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) {q M : ℕ} (hq : q.Prime)
    (h1 : (q : R) ∈ I) (h2 : (M : R) ∈ I) : q ∣ M := by
  by_contra hnd
  have hc : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).2 hnd
  obtain ⟨u, v, huv⟩ : IsCoprime (q : R) (M : R) := Nat.Coprime.cast hc
  exact hI ((Ideal.eq_top_iff_one _).2
    (huv ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem exists_embedding (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    ∃ ι : K →+* ℂ_[p], w.asIdeal = smallIdeal ι := by
  by_contra hcon
  push Not at hcon
  have hnle : ∀ σ : K →ₐ[ℚ] ℂ_[p], ¬ w.asIdeal ≤ smallIdeal (σ : K →+* ℂ_[p]) := by
    intro σ hle
    exact hcon (σ : K →+* ℂ_[p]) (w.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top hle)
  have σ0 : K →ₐ[ℚ] ℂ_[p] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hav : ¬ ((w.asIdeal : Set (𝓞 K)) ⊆
      ⋃ σ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] ℂ_[p])) : Set (K →ₐ[ℚ] ℂ_[p])),
        (smallIdeal (σ : K →+* ℂ_[p]) : Set (𝓞 K))) := by
    rw [Ideal.subset_union_prime σ0 σ0 (fun σ _ _ _ => smallIdeal_isPrime _)]
    rintro ⟨σ, -, hle⟩
    exact hnle σ hle
  obtain ⟨x, hxw, hx⟩ := Set.not_subset.1 hav
  have hxσ : ∀ σ : K →ₐ[ℚ] ℂ_[p], 1 ≤ ‖σ (x : K)‖ := by
    intro σ
    by_contra hlt
    exact hx (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ σ)) (not_le.1 hlt))
  have hN : ((Algebra.norm ℤ x).natAbs : 𝓞 K) ∈ w.asIdeal := by
    have h1 := Ideal.absNorm_mem (Ideal.span {x})
    rw [Ideal.absNorm_span_singleton] at h1
    exact (Ideal.span_singleton_le_iff_mem _).2 hxw h1
  have hpN : p ∣ (Algebra.norm ℤ x).natAbs :=
    dvd_of_natCast_mem w.asIdeal w.isPrime.ne_top Fact.out hw hN
  obtain ⟨m, hm⟩ : (p : ℤ) ∣ Algebra.norm ℤ x := Int.natCast_dvd.2 hpN
  have hprod : ((Algebra.norm ℤ x : ℤ) : ℂ_[p]) = ∏ σ : K →ₐ[ℚ] ℂ_[p], σ (x : K) := by
    rw [← Algebra.norm_eq_prod_embeddings ℚ ℂ_[p] (x : K), ← Algebra.coe_norm_int x]
    simp
  have h1 : 1 ≤ ‖((Algebra.norm ℤ x : ℤ) : ℂ_[p])‖ := by
    rw [hprod, norm_prod]
    exact Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
      le_rfl fun σ _ => hxσ σ
  have h2 : ((Algebra.norm ℤ x : ℤ) : ℂ_[p]) = (p : ℂ_[p]) * ((m : ℤ) : ℂ_[p]) := by
    rw [hm]; push_cast; ring
  have h3 : ‖((m : ℤ) : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ m
  rw [h2, norm_mul] at h1
  have h4 := norm_p_lt_one (p := p)
  nlinarith [norm_nonneg (p : ℂ_[p]), norm_nonneg ((m : ℤ) : ℂ_[p])]

theorem valuation_le_one_of_norm (ι : K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) (x : K) (hx : ‖ι x‖ ≤ 1) :
    w.valuation K x ≤ 1 := by
  by_contra hcon
  have hgt : 1 < w.valuation K x := not_le.1 hcon
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hgt
  have hinv : w.valuation K x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hgt
  obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x⁻¹ hinv.le
  have hd : 1 ≤ ‖ι ((d : 𝓞 K) : K)‖ := not_lt.1 fun hlt => d.2 ((hw _).2 hlt)
  have hn : n ∈ w.asIdeal := by
    rw [← w.valuation_lt_one_iff_mem (K := K)]
    change w.valuation K (algebraMap (𝓞 K) K n) < 1
    rw [← h, map_mul]
    calc w.valuation K x⁻¹ * w.valuation K (algebraMap (𝓞 K) K d) ≤ w.valuation K x⁻¹ * 1 :=
          mul_le_mul_right (w.valuation_le_one _) _
      _ < 1 := by rwa [mul_one]
  have hn' := (hw n).1 hn
  have h2 : ((d : 𝓞 K) : K) = x * (n : K) := by
    have h' : x⁻¹ * ((d : 𝓞 K) : K) = (n : K) := h
    rw [← h', ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
  rw [h2, map_mul, norm_mul] at hd
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι (n : K))]

theorem placeAbove : GlobalTheory.DatumJets.PlaceAbove := by
  intro K _ _ σ p _ w hw
  obtain ⟨ι, hι⟩ := exists_embedding w hw
  have hw' : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1 := fun y => by rw [hι]; rfl
  obtain ⟨lam, hlam⟩ := GlobalTheory.MomPlace.exists_extension K p σ ι
  refine ⟨lam, fun k => ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt
  rw [(hlam k).2]
  exact ⟨fun h => valuation_le_one_of_norm ι w hw' k h.2,
    fun h => ⟨(hlam k).1, GlobalTheory.MomPlace.norm_le_one_of_valuation K p ι w hw' k h⟩⟩

end GlobalTheory.DatumJets.Place
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHecke
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.Hk3.StepX

variable {D : D7}

theorem gram_posDef_X (τ : D.what₂.Tau) : (gramAt D D.sp.X' τ).PosDef := by
  have := D.sp.X'_sig (tauE D τ)
  rw [D7.X'_posDef D] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem lift_symm_comp {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))
    (x : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)) :
    PiTensorProduct.lift.symm (L ∘ₗ x) = postOn M L (PiTensorProduct.lift.symm x) := by
  refine MultilinearMap.ext fun v => ?_
  rw [postOn_apply]
  simp [PiTensorProduct.lift_symm]

theorem integ_X {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D D.sp.X' →* Module.End ℂ (WO S D.sp.X' → ℂ)}
    (hW : IsWeilDatumO ψ S D.sp.X' χS χT om) {f : WO S D.sp.X' → ℂ} (hf : IsThetaFunO ψ S D.sp.X' f)
    (Φ : GA D D.sp.X' → ℂ) (hΦc : Continuous Φ) (hl : ∀ γ ∈ GQ D.sp.X', ∀ h, Φ (γ * h) = Φ h)
    (ν : Measure (GA D D.sp.X')) (hν : ν.IsHaarMeasure) (𝓕 : Set (GA D D.sp.X'))
    (h𝓕 : IsFundamentalDomain (GQ D.sp.X') 𝓕 ν) (g : GA D S) (y : GA D D.sp.X') :
    IntegrableOn (fun h => thetaKO om g h f * Φ (h * y)) 𝓕 ν := by
  have : IsTopologicalGroup (GA D D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D D.sp.X') := ⟨rfl⟩
  have : Countable (GQ D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig D.sp.X'.gram
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact D.sp.X' gram_posDef_X
  refine GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ (GQ D.sp.X') C hC (fun h => ?_) ν hν 𝓕 h𝓕 _ ?_ ?_
  · obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩
  · exact ((hW.om_cont f hf 0).comp (Continuous.prodMk_right g)).mul (hΦc.comp (continuous_mul_const y))
  · intro γ hγ h
    have h1 := (GlobalTheory.thetaKO_rat_left_and_eigen_right ψ S D.sp.X' χS χT om hW f hf).1 1 (one_mem _) γ hγ g h
    rw [one_mul] at h1
    show thetaKO om g (γ * h) f * Φ (γ * h * y) = thetaKO om g h f * Φ (h * y)
    rw [h1, mul_assoc, hl γ hγ]

theorem hyp_inv {V : HSp D} (c : CoefA V) (hc : c.Is) {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1) {L : LevDat D.host.E ℂ V.rank}
    {P : Pl D.host.E} (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    {f : Bridge.Gf V → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) :
    ∀ k ∈ hyp V P, ∀ h, c.ext f (h * k) = c.ext f h := by
  obtain ⟨n, hB⟩ := hβ
  have hlev := (GlobalTheory.LevOp.level_operators V β Λ _ (flag1L L) hB P (GlobalTheory.DefLiftHecke.one_pow_notMem P n) hP).1
  exact fun k hk h => GlobalTheory.DefLiftHecke.ext_level c hc hf (hlev k hk).1 (hlev k hk).2 h

theorem mult_stable {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
    (hβ : IsSDFrame V β Λ N) {L : LevDat D.host.E ℂ V.rank} {P : Pl D.host.E} (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) (c : List ℤ →₀ ℂ) {U : MMap M}
    (hU : U ∈ Mult θ M (levS V β L) (levChi V β L)) : postOn M (hk V P c) U ∈ Mult θ M (levS V β L) (levChi V β L) := by
  obtain ⟨n, hB⟩ := hβ
  have hN' : ((N ^ n : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h' =>
    hN (P.isPrime.mem_of_pow_mem n (by rwa [Nat.cast_pow] at h'))
  exact (GlobalTheory.LevOp.level_operators V β Λ _ L hB P hN' hP).2.2.2.2 S θ M c hθ U hU

theorem toMap_hkF {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (P : Pl D.host.E) (z : List ℤ →₀ ℂ) (f : Bridge.Gf V → c.W) (w : Dm) :
    c.toMap pr (hkF V P z f) w = hk V P z (c.toMap pr f w) := by
  funext h
  show pr (c.ext (hkF V P z f) h) w = _
  rw [GlobalTheory.DefLiftHecke.ext_hkF c hc, GlobalTheory.ThetaIntHecke.hk_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl


set_option maxHeartbeats 2000000 in
theorem liftInt_toMap_hk {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D D.sp.X' →* Module.End ℂ (WO S D.sp.X' → ℂ)} {P : Pl D.host.E}
    (hW : IsWeilDatumO ψ S D.sp.X' χS χT om) {ν : Measure (GA D D.sp.X')} {𝓕 : Set (GA D D.sp.X')}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ D.sp.X') 𝓕 ν) (hfix : VacFix ψ om P)
    (cS cX : List ℤ →₀ ℂ) (hM : Match ψ om P cS (dualC cX)) {f0 : WO S D.sp.X' → ℂ} (hf0 : IsVacAt ψ S D.sp.X' P f0)
    (c : CoefA D.sp.X') (hc : c.Is) {β : GL (Fin D.sp.X'.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (hβ : IsSDFrame D.sp.X' β Λ 1)
    {L : LevDat D.host.E ℂ D.sp.X'.rank} (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm] (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) {f : Bridge.Gf D.sp.X' → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF D.sp.X') c.coef.ρ (levEnv _ β L).J (levEnv _ β L).χ) (w : Dm) :
    Lift.liftInt ν 𝓕 (thetaKO om) f0 (c.toMap pr (hkF D.sp.X' P cX f) w) =
      hk S P cS (Lift.liftInt ν 𝓕 (thetaKO om) f0 (c.toMap pr f w)) := by
  have he : c.toMap pr f w = (pr.flip w) ∘ c.ext f := rfl
  have hlev := hyp_inv c hc hβ hP hf
  have hcont : Continuous (c.toMap pr f w) := by
    rw [he]
    exact (LinearMap.continuous_of_finiteDimensional (pr.flip w)).comp (GlobalTheory.ThetaIntegrand.ext_continuous c hc β L hf)
  have hl : ∀ γ ∈ GQ D.sp.X', ∀ h, c.toMap pr f w (γ * h) = c.toMap pr f w h := fun γ hγ h => by
    rw [he, Function.comp_apply, Function.comp_apply, GlobalTheory.ThetaIntegrand.ext_invariant c hf γ hγ h]
  have hr : ∀ k ∈ hyp D.sp.X' P, ∀ h, c.toMap pr f w (h * k) = c.toMap pr f w h := fun k hk h => by
    rw [he, Function.comp_apply, Function.comp_apply, hlev k hk h]
  rw [toMap_hkF c hc pr]
  exact GlobalTheory.ThetaIntHecke.liftInt_hk ψ S D.sp.X' χS χT om P hW ν 𝓕 hν h𝓕 hfix cS cX hM f0 hf0 _ hl hr
    (fun g z _ => integ_X hW hf0.1 _ hcont hl ν hν 𝓕 h𝓕 g z)

theorem sub_comp_apply {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (u u' : M →ₗ[ℂ] N)
    (H : N →ₗ[ℂ] N) (x : M) (h : u' x = H (u x)) : (u' - H ∘ₗ u) x = 0 := by
  rw [LinearMap.sub_apply, LinearMap.comp_apply, h, sub_self]

theorem eq_of_sub_comp {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (u u' : M →ₗ[ℂ] N)
    (H : N →ₗ[ℂ] N) (h : u' - H ∘ₗ u = 0) (x : M) : u' x = H (u x) := by
  have := congrArg (fun L => L x) h
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply, sub_eq_zero] at this
  exact this

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 2000000 in
theorem at_It (R : RealDat D A Ks) (F : Face D A) (hC : Core R F) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (hfix : VacFix R.ψ (R.ωX t) P) (cS cX : List ℤ →₀ ℂ) (hM : Match R.ψ (R.ωX t) P cS (dualC cX))
    (y y' : (R.HX t).H) (hy : (R.HX t).e y' = hkF D.sp.X' P cX ((R.HX t).e y)) (φ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank)
    (w : SmT R.MX) :
    (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 (R.ItX φ w) =
      hk _ P cS ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 (R.ItX φ w)) := by
  have hIo := hC.chain.ioX t
  have hν := hC.models.νX t
  have hmem : (R.HX t).e y ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J
      (levEnv _ R.βX (R.datXt t)).χ :=
    (hC.models.HX t).2.1.le (LinearMap.mem_range_self _ y)
  have k := liftInt_toMap_hk (hC.chain.ωX t) hν.1.1 hν.2 hfix cS cX hM ((_root_.GlobalTheory.VacGood.fock_vacua_good R F hC t P hP).2.1 φ)
    R.cX hC.models.cX hC.lev.βX (L := R.datXt t) hP R.prX hmem w
  have e1 : (((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y' : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) :
      SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w = R.cX.toMap R.prX (hkF D.sp.X' P cX ((R.HX t).e y)) w :=
    congrArg (fun f => R.cX.toMap R.prX f w) hy
  have hyY : Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t φ) (R.cX.toMap R.prX ((R.HX t).e y) w) =
      (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 (R.ItX φ w) :=
    funext fun g' => hIo.eq ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y) φ w g'
  have hyY' : Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t φ)
      ((((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y' : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) :
        SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w) =
      (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 (R.ItX φ w) :=
    funext fun g' => hIo.eq ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y') φ w g'
  exact hyY'.symm.trans ((congrArg (Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t φ)) e1).trans
    (k.trans (congrArg (hk _ P cS) hyY)))

end GlobalTheory.Hk3.StepX


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Hk3.StepX.stepX_hk : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ t P, Good R t P → VacFix R.ψ (R.ωX t) P → ∀ cS cX, Match R.ψ (R.ωX t) P cS (dualC cX) → ∀ y y' : (R.HX t).H, (R.HX t).e y' = hkF D.sp.X' P cX ((R.HX t).e y) → ∀ v, (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 v = hk _ P cS ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 v) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS t P hP hfix cS cX hM y y' hy
  have hm := D.R.two_le_m
  have hu : (hk (Yc D (D.R.m - 1)) P cS ∘ₗ
      ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1)) ∈ R.CC t (D.R.m - 1) := by
    rw [mem_multT, GlobalTheory.Hk3.StepX.lift_symm_comp]
    exact GlobalTheory.Hk3.StepX.mult_stable R.θ hC.models.inf (R.MY (D.R.m - 1)) (hC.lev.βY (D.R.m - 1) (by omega))
      (L := R.datYt t (D.R.m - 1) R.triv) ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.1 t P hP).1 hP cS
      ((mem_multT _ _ _ _ _).1 (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).2)
  have hz := GlobalTheory.multT_eq_zero_of_apply_eq_zero R.θ (R.MY (D.R.m - 1)) _ _ (R.νY t (D.R.m - 1)) (R.fdY t (D.R.m - 1))
    hC.models.inf (hC.models.νY' t).1.1 (hC.models.νY' t).2 (hS.1 t (D.R.m - 1) (by omega))
    (((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1) - hk (Yc D (D.R.m - 1)) P cS ∘ₗ
      ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1))
    (sub_mem (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).2 hu)
  have hex : ∃ φ w, R.ItX φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact (hC.chain.ItX t).ne (LinearMap.ext fun φ => LinearMap.ext fun w => hcon φ w)
  refine hex.elim fun φ0 hw0 => hw0.elim fun w0 hne => ?_
  have h0 := hz _ hne (GlobalTheory.Hk3.StepX.sub_comp_apply _ _ _ _ (GlobalTheory.Hk3.StepX.at_It R F hC t P hP hfix cS cX hM y y' hy φ0 w0))
  exact GlobalTheory.Hk3.StepX.eq_of_sub_comp _ _ _ h0
end

