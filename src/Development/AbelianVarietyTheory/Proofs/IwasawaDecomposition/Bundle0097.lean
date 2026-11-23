module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Formalism.LocalToGlobal.Divisibility.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem.FieldsLaws

open Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} (H : Host R)

theorem galE_sigmaOf (g : R.GG) : H.galE (H.sigmaOf g) = g :=
  (H.gal).apply_symm_apply g

theorem sigmaOf_galE (σ : H.E ≃ₐ[ℚ] H.E) : H.sigmaOf (H.galE σ) = σ :=
  (H.gal).symm_apply_apply σ

theorem gal_comm (s t : H.E ≃ₐ[ℚ] H.E) : s * t = t * s := by
  apply (H.gal).injective
  rw [map_mul, map_mul, mul_comm]

theorem mem_K_iff (x : H.E) : x ∈ H.K ↔ ∀ τ : R.Psi, H.sigmaOf τ x = x := by
  have hG : IsGalois ℚ H.E := H.hostE_isGalois
  have key : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ H.K.fixingSubgroup ↔ H.galE σ ∈ R.Psi := by
    intro σ
    rw [H.galE_mem_Psi_iff, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h
      exact h _ (IntermediateField.mem_adjoin_simple_self ℚ _)
    · intro h y hy
      have hle : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
        refine IntermediateField.adjoin_simple_le_iff.2 ?_
        rw [IntermediateField.mem_fixedField_iff]
        intro f hf
        have : Subgroup.zpowers σ ≤ MulAction.stabilizer _ (H.sqd) := by
          rw [Subgroup.zpowers_le]
          exact h
        exact this hf
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hy) σ (Subgroup.mem_zpowers σ)
  constructor
  · intro hx τ
    have h : H.sigmaOf τ ∈ H.K.fixingSubgroup := by
      rw [key, galE_sigmaOf]
      exact τ.2
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 h x hx
  · intro hx
    rw [← IsGalois.fixedField_fixingSubgroup H.K, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have := hx ⟨_, (key σ).1 hσ⟩
    rwa [sigmaOf_galE] at this

theorem unram (P : HeightOneSpectrum (𝓞 H.E)) :
    ¬ (P.asIdeal.comap (algebraMap (𝓞 H.F) (𝓞 H.E))).map (algebraMap (𝓞 H.F) (𝓞 H.E)) ≤ P.asIdeal ^ 2 := by
  have hcm : IsCMField H.E := H.isCMField_hostE
  intro hle
  obtain ⟨π, hπ⟩ := (P.under (𝓞 H.F)).intValuation_exists_uniformizer
  have hmem : π ∈ (P.under (𝓞 H.F)).asIdeal := by
    have := ((P.under (𝓞 H.F)).intValuation_le_pow_iff_mem π 1).1 (by rw [hπ]; simp)
    rwa [pow_one] at this
  have h2 : algebraMap (𝓞 H.F) (𝓞 H.E) π ∈ P.asIdeal ^ 2 := hle (Ideal.mem_map_of_mem _ hmem)
  have h3 := (P.intValuation_le_pow_iff_mem _ 2).2 h2
  have h4 := HostCM.valuation_eq_of_unram H.E (fun P hP h0 h =>
    H.der.unramEF P hP h0 fun x => by
      have hx : H.conj • x = IsCMField.complexConj H.E • x :=
        RingOfIntegers.ext (H.φ₀.injective ((H.conjE_apply H.φ₀ x).trans
          (IsCMField.complexEmbedding_complexConj H.E H.φ₀ x).symm))
      rw [hx]
      exact h x) P (π : H.F)
  have h5 : P.valuation H.E (algebraMap (𝓞 H.E) H.E (algebraMap (𝓞 H.F) (𝓞 H.E) π)) =
      (P.under (𝓞 H.F)).valuation H.F (algebraMap (𝓞 H.F) H.F π) := h4
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hπ] at h5
  rw [h5, WithZero.exp_le_exp] at h3
  omega

end Host

variable (B : Base)

theorem embLL_comp_embBar (τ : Tau B.R) :
    B.embLL.comp (B.fields.embBar τ) = B.host.emb ((τ : B.R.GG) * B.R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp, ← B.fields_embC]
  refine RingHom.ext fun x => ?_
  exact congrArg (fun y => B.embLL (B.tauLL τ y)) (B.fields_sig x)

theorem embLL_comp_emb (τ : Tau B.R) : B.embLL.comp (B.fields.emb τ) = B.host.emb (τ : B.R.GG) :=
  B.fields_embC τ

theorem mem_Kq_iff (x : B.host.E) : x ∈ B.fields.Kq ↔ x ∈ B.host.K := by
  rw [mem_K_iff]
  constructor
  · intro h τ
    have h1 := B.embE.injective (h τ (1 : B.R.Psi))
    have h2 : B.host.sigmaOf ((1 : B.R.Psi) : B.R.GG) = 1 := map_one (B.host.gal).symm
    have h3 : B.host.sigmaOf τ x = B.host.sigmaOf ((1 : B.R.Psi) : B.R.GG) x := h1
    rw [h3, h2]
    rfl
  · intro h τ τ'
    rw [B.fields_emb_apply, B.fields_emb_apply, h τ, h τ']

theorem fields_ok : B.fields.Ok := by
  have hcm : IsCMField B.host.E := B.host.isCMField_hostE
  letI := B.host.cmStar
  have cm := host_cmData B.R B.host
  have hinj : ∀ {φ ψ : B.host.E →+* B.LL}, B.embLL.comp φ = B.embLL.comp ψ → φ = ψ := fun h =>
    RingHom.ext fun x => B.embLL.injective (RingHom.congr_fun h x)
  refine
    { realF := cm.totReal
      rankE := cm.deg2
      star_F := fun x => (cm.fixed _).2 ⟨x, rfl⟩
      conjE := fun φ x => ?_
      cplxE := inferInstanceAs (IsTotallyComplex B.host.E)
      emb_star := fun τ x => ?_
      card_Tau := ?_
      emb_inj := fun τ τ' h => ?_
      emb_ne := fun τ τ' h => ?_
      emb_all := fun φ => ?_
      cplxK := ?_
      normalK := inferInstanceAs (Normal ℚ B.LL)
      conjK := ⟨B.embLL, B.starLL_cx⟩
      quad := ?_ }
  · exact (congrArg φ (B.fields_star x)).trans (B.host.conjE_apply φ x)
  · apply B.embLL.injective
    rw [B.starLL_cx]
    exact (congrArg (B.embLL.comp (B.tauLL τ)) (B.fields_star x)).trans (B.host.conjE_apply (B.embLL.comp (B.tauLL τ)) x)
  · refine (card_Tau B.host).trans (Eq.trans ?_ (B.host.finrank_hostF).symm)
    rfl
  · have h1 := congrArg B.embLL.comp h
    rw [embLL_comp_emb, embLL_comp_emb] at h1
    exact Subtype.ext ((factEmb B.R B.host).1.1 h1)
  · have h1 := congrArg B.embLL.comp h
    rw [embLL_comp_emb, embLL_comp_embBar] at h1
    have h2 := (factEmb B.R B.host).1.1 h1
    exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 τ'.2 (h2 ▸ τ.2)
  · obtain ⟨g, hg⟩ := (factEmb B.R B.host).1.2 (B.embLL.comp φ)
    by_cases h : g ∈ B.R.Psi
    · exact ⟨⟨g, h⟩, Or.inl (hinj (by rw [← hg]; exact (embLL_comp_emb B ⟨g, h⟩).symm))⟩
    · have hcc : B.R.cc * B.R.cc = 1 := B.R.cc_mul_cc
      have h' : g * B.R.cc ∈ B.R.Psi := by
        rw [Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem, mul_assoc, hcc, mul_one]
        exact h
      refine ⟨⟨_, h'⟩, Or.inr (hinj ?_)⟩
      rw [← hg, embLL_comp_embBar B ⟨_, h'⟩]
      show _ = B.host.emb (g * B.R.cc * B.R.cc)
      rw [mul_assoc, hcc, mul_one]
  · letI : Algebra B.host.E B.LL := B.embE.toAlgebra
    exact isTotallyComplex_of_algebra B.host.E B.LL
  · let e : B.fields.Kq ≃+* B.host.K :=
      RingEquiv.subringCongr (s := B.fields.Kq.toSubring) (t := B.host.K.toSubfield.toSubring)
        (Subring.ext fun x => mem_Kq_iff B x)
    rw [← SplitK.finrank_K B.host.hyp.2.1.pos B.host.sqrtMinusD_sq]
    exact (AlgEquiv.ofRingEquiv (R := ℚ) (f := e) (fun r => map_ratCast e r)).toLinearEquiv.finrank_eq

theorem fields_satisfy_definite_laws : ∀ B : Base, B.fields.AbelianUnramifiedExtensionConditions ∧ B.fields.f = B.R.f := by
  intro B
  refine ⟨⟨fields_ok B, ?_, B.host.hostE_isGalois, gal_comm B.host, unram B.host⟩, B.fields_f⟩
  rw [B.fields_f]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le B.host.two_le_e
  obtain ⟨m, hm⟩ := B.R.two_pow_dvd_ord
  refine ⟨2 ^ k * m, ?_⟩
  show 2 * B.R.ord = _
  rw [hm, hk]
  ring

end GlobalTheory.Mem.FieldsLaws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BijectiveCmType
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.HeckeGal

namespace GlobalTheory.Mem.CharAlg

theorem bijective_cmType {L : Type} [Field L] [_root_.NumberField.IsTotallyComplex L] {I : Type} (φ : I → L →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) :
    Function.Bijective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))) := by
  have hne : ∀ i j, φ i ≠ ComplexEmbedding.conjugate (φ j) := by
    intro i j hij
    have h1 : i = j := h.1 (by
      show InfinitePlace.mk (φ i) = InfinitePlace.mk (φ j)
      rw [hij, InfinitePlace.mk_conjugate_eq])
    subst h1
    exact IsTotallyComplex.complexEmbedding_not_isReal (φ i) (ComplexEmbedding.isReal_iff.2 hij.symm)
  constructor
  · rintro (i | i) (j | j) hij
    · have hij' : φ i = φ j := hij
      exact congrArg Sum.inl (h.1 (congrArg InfinitePlace.mk hij'))
    · exact absurd hij (hne i j)
    · exact absurd hij.symm (hne j i)
    · have hij' : ComplexEmbedding.conjugate (φ i) = ComplexEmbedding.conjugate (φ j) := hij
      refine congrArg Sum.inr (h.1 ?_)
      show InfinitePlace.mk (φ i) = InfinitePlace.mk (φ j)
      rw [← InfinitePlace.mk_conjugate_eq (φ i), hij', InfinitePlace.mk_conjugate_eq]
  · intro ψ
    obtain ⟨i, hi⟩ := h.2 (InfinitePlace.mk ψ)
    rcases InfinitePlace.mk_eq_iff.1 hi with hi | hi
    · exact ⟨Sum.inl i, hi⟩
    · exact ⟨Sum.inr i, hi⟩

theorem prod_split {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) (f : (L →+* ℂ) → ℂ) :
    ∏ ψ, f ψ = ∏ i, (f (φ i) * f (ComplexEmbedding.conjugate (φ i))) := by
  rw [← (bijective_cmType φ h).prod_comp f, Fintype.prod_sum_type, Finset.prod_mul_distrib]
  rfl

theorem isAlg_of {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar L) (a b : I → ℤ)
    (hχ : ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, (φ i k ^ a i * (starRingEnd ℂ (φ i k)) ^ b i)) :
    ∃ n, χ.IsAlg n := by
  let e := Equiv.ofBijective _ (bijective_cmType φ h)
  refine ⟨fun ψ => Sum.elim a b (e.symm ψ), fun k => ?_⟩
  rw [hχ k, prod_split φ h]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : e.symm (φ i) = Sum.inl i := e.symm_apply_eq.2 rfl
  have h2 : e.symm (ComplexEmbedding.conjugate (φ i)) = Sum.inr i := e.symm_apply_eq.2 rfl
  simp only [h1, h2, Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq]

theorem even_pow {z : ℂ} (hz : z ≠ 0) (c : ℤ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * c) = z ^ c * (starRingEnd ℂ z) ^ (-c) := by
  have hc : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have h : (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 : ℤ) = z / starRingEnd ℂ z := by
    rw [zpow_ofNat, div_pow, ← Complex.mul_conj', sq, mul_div_mul_left _ _ hz]
  rw [zpow_mul, h, div_zpow, zpow_neg, div_eq_mul_inv]

theorem odd_pow {z : ℂ} (hz : z ≠ 0) (m : ℕ) :
    ((z / ((‖z‖ : ℝ) : ℂ)) ^ (1 : ℤ))⁻¹ *
      (((‖z‖ : ℝ) : ℂ) ^ (((-((2 * m + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) *
        ((‖z‖ : ℝ) : ℂ) ^ (((-((2 * m + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ)) =
      z ^ (-1 - (m : ℤ)) * (starRingEnd ℂ z) ^ (-(m : ℤ)) := by
  have hc : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by simpa using hz
  have he : (((-((2 * m + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) + (((-((2 * m + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) =
      -((2 * m + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [← Complex.cpow_add _ _ hn, he, Complex.cpow_neg, Complex.cpow_natCast, pow_succ, pow_mul,
    ← Complex.mul_conj', zpow_sub₀ hz, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, zpow_one, zpow_one, mul_pow]
  field_simp

theorem isAlg_even_odd : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), (∀ (χ : HChar H.E) (c : R.Psi → ℤ), χ.HasInf (embPsi H) (fun τ => 2 * c τ) → ∃ n, χ.IsAlg n) ∧ ∀ (η : HChar H.E), η.HasInf (embPsi H) (fun _ => 1) → ∀ r : ℕ, Odd r → ∃ n, (η⁻¹ * GlobalTheory.HeckeGal.Model.absPow H.E (-(r : ℝ) / 2)).IsAlg n := by
  intro R H
  obtain ⟨c0, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have := hcm.cplx
  have hz : ∀ (i : R.Psi) (k : (H.E)ˣ), embPsi H i (k : H.E) ≠ 0 := fun i k => by simp
  refine ⟨fun χ c hχ => isAlg_of (embPsi H) hcm.bij χ c (fun i => -c i) fun k => ?_, ?_⟩
  · rw [hχ k]
    exact Finset.prod_congr rfl fun i _ => even_pow (hz i k) (c i)
  · rintro η hη r ⟨m, rfl⟩
    refine isAlg_of (embPsi H) hcm.bij _ (fun _ => -1 - (m : ℤ)) (fun _ => -(m : ℤ)) fun k => ?_
    rw [HChar.inf_mul, HChar.inf_inv, Units.val_mul, Units.val_inv_eq_inv_val, hη k,
      (GlobalTheory.HeckeGal.Model.absPow_isAbsPow H.E _).2.2 k, prod_split (embPsi H) hcm.bij, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
    exact odd_pow (hz i k) m

end GlobalTheory.Mem.CharAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped Pointwise

namespace GlobalTheory.Mem.Chr

section General

variable {L : Type} [Field L] [NumberField L]

theorem liesOver_span_of_natCast_mem {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 L)) [P.IsPrime] (h : ((p : ℕ) : 𝓞 L) ∈ P) :
    P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have : Fact p.Prime := ⟨hp⟩
  have hm : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  refine ⟨hm.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  show algebraMap ℤ (𝓞 L) (p : ℤ) ∈ P
  simpa using h

theorem ncard_places_eq_primesOver {p : ℕ} (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal}.ncard =
      ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard := by
  rw [← Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h :
    Function.Injective (HeightOneSpectrum.asIdeal (R := 𝓞 L)))]
  congr 1
  ext P
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, liesOver_span_of_natCast_mem hp _ hv⟩
  · rintro ⟨h1, h2⟩
    have hm : ((p : ℕ) : 𝓞 L) ∈ P := by
      have : (p : ℤ) ∈ P.under ℤ := by rw [← h2.over]; exact Ideal.mem_span_singleton_self _
      simpa using (show algebraMap ℤ (𝓞 L) (p : ℤ) ∈ P from this)
    refine ⟨⟨P, h1, ?_⟩, hm, rfl⟩
    rintro rfl
    exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hm))

theorem splitsC_place [IsGalois ℚ L] {p : ℕ} (hp : p.Prime) (hs : SplitsC L p) (v : HeightOneSpectrum (𝓞 L))
    (hv : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal) :
    Ideal.absNorm v.asIdeal = p ∧ ((p : ℕ) : 𝓞 L) ∉ v.asIdeal ^ 2 ∧
      ∀ σ : L ≃ₐ[ℚ] L, σ • v.asIdeal = v.asIdeal → σ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have := v.isPrime
  have := liesOver_span_of_natCast_mem hp _ hv
  have hm : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have h0 : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by simpa using hp.ne_zero
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 L) (L ≃ₐ[ℚ] L)
  unfold SplitsC at hs
  rw [← ncard_places_eq_primesOver hp, hs, IsGalois.card_aut_eq_finrank] at h1
  have h2 : (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 L) * (Ideal.span {(p : ℤ)}).inertiaDegIn (𝓞 L) = 1 :=
    (mul_eq_left₀ Module.finrank_pos.ne').1 h1
  have h3 := Ideal.card_stabilizer_eq (G := L ≃ₐ[ℚ] L) (Ideal.span {(p : ℤ)}) v.asIdeal
  rw [h2] at h3
  have he := Nat.eq_one_of_mul_eq_one_right h2
  have hf := Nat.eq_one_of_mul_eq_one_left h2
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ v.asIdeal (L ≃ₐ[ℚ] L),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) v.asIdeal h0] at he
  rw [Ideal.inertiaDegIn_eq_inertiaDeg _ v.asIdeal (L ≃ₐ[ℚ] L)] at hf
  refine ⟨?_, ?_, ?_⟩
  · rw [← Ideal.pow_inertiaDeg p v.asIdeal, hf, pow_one]
  · intro h
    refine (Ideal.ramificationIdx'_ne_one_iff ?_).2 ?_ he
    · simpa [Ideal.map_span] using hv
    · simpa [Ideal.map_span] using h
  · intro σ hσ
    have : (MulAction.stabilizer (L ≃ₐ[ℚ] L) v.asIdeal) = ⊥ := Subgroup.card_eq_one.1 h3
    exact Subgroup.mem_bot.1 (this ▸ hσ)

theorem conjPl_iff_smul (σ : L ≃ₐ[ℚ] L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl σ.toRingEquiv v v' ↔ σ • v.asIdeal = v'.asIdeal := by
  rw [conjPl_iff_mem]
  constructor
  · intro h
    ext y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    exact h _ _ (σ.apply_symm_apply (y : L)).symm
  · intro h x y hxy
    have e : y = σ • x := RingOfIntegers.ext hxy
    rw [e, ← h, Ideal.smul_mem_pointwise_smul_iff]

theorem under_smul_of_fix (b : L) (σ : L ≃ₐ[ℚ] L) (h : σ b = b) (P : Ideal (𝓞 L)) :
    (σ • P).under (𝓞 (IntermediateField.adjoin ℚ {b})) = P.under (𝓞 (IntermediateField.adjoin ℚ {b})) := by
  have hfix : ∀ x ∈ IntermediateField.adjoin ℚ {b}, σ x = x := by
    intro x hx
    have : IntermediateField.adjoin ℚ {b} ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
      rintro _ hτ
      have : Subgroup.zpowers σ ≤ MulAction.stabilizer _ b := (Subgroup.zpowers_le).2 h
      exact this hτ
    exact (IntermediateField.mem_fixedField_iff _ _).1 (this hx) σ (Subgroup.mem_zpowers σ)
  ext a
  have e : σ • algebraMap _ (𝓞 L) a = algebraMap _ (𝓞 L) a := RingOfIntegers.ext (hfix _ (a : IntermediateField.adjoin ℚ {b}).2)
  rw [Ideal.mem_under, Ideal.mem_under]
  conv_lhs => rw [← e]
  rw [Ideal.smul_mem_pointwise_smul_iff]

theorem exists_smul_fix_of_under_eq [IsGalois ℚ L] (b : L) (P P' : Ideal (𝓞 L)) [P.IsPrime] [P'.IsPrime]
    (h : P.under (𝓞 (IntermediateField.adjoin ℚ {b})) = P'.under (𝓞 (IntermediateField.adjoin ℚ {b}))) :
    ∃ σ : L ≃ₐ[ℚ] L, σ b = b ∧ σ • P = P' := by
  set K := IntermediateField.adjoin ℚ {b} with hK
  have : P'.LiesOver (P.under (𝓞 K)) := ⟨h⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (P.under (𝓞 K)) P P' (L ≃ₐ[K] L)
  refine ⟨τ.restrictScalars ℚ, τ.commutes (⟨b, IntermediateField.mem_adjoin_simple_self ℚ b⟩ : K), ?_⟩
  rw [← hτ]
  ext y
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem under_eq_iff_under_ne [IsGalois ℚ L] {p : ℕ} (hp : p.Prime) (hs : SplitsC L p) (b : L) (hb0 : b ≠ 0)
    (hb : ∀ σ : L ≃ₐ[ℚ] L, σ b = b ∨ σ b = -b) (c : L ≃ₐ[ℚ] L) (hc : c b = -b)
    (v v' : HeightOneSpectrum (𝓞 L)) (hv : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal) (hvv : c • v.asIdeal = v'.asIdeal)
    (Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin ℚ {b})))
    (hQ : ((p : ℕ) : 𝓞 (IntermediateField.adjoin ℚ {b})) ∈ Q.asIdeal) :
    v.under (𝓞 (IntermediateField.adjoin ℚ {b})) = Q ↔ v'.under (𝓞 (IntermediateField.adjoin ℚ {b})) ≠ Q := by
  have := v.isPrime
  have := v'.isPrime
  constructor
  · rintro rfl h
    obtain ⟨σ, hσb, hσ⟩ := exists_smul_fix_of_under_eq b v.asIdeal v'.asIdeal
      (congrArg HeightOneSpectrum.asIdeal h).symm
    have h1 : σ⁻¹ * c = 1 := (splitsC_place hp hs v hv).2.2 _ (by rw [mul_smul, hvv, ← hσ, inv_smul_smul])
    rw [inv_mul_eq_one] at h1
    rw [h1, hc] at hσb
    exact hb0 (by linear_combination (-1 / 2 : L) * hσb)
  · intro h
    have := Q.isPrime
    obtain ⟨⟨W, hW, hWQ⟩⟩ := (inferInstance : Nonempty (Q.asIdeal.primesOver (𝓞 L)))
    have hpW : ((p : ℕ) : 𝓞 L) ∈ W := by
      rw [hWQ.over, Ideal.mem_under] at hQ
      simpa using hQ
    have := liesOver_span_of_natCast_mem hp _ hv
    have := liesOver_span_of_natCast_mem hp _ hpW
    obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) v.asIdeal W (L ≃ₐ[ℚ] L)
    rcases hb σ with h1 | h1
    · apply HeightOneSpectrum.ext
      rw [hWQ.over, ← hσ, under_smul_of_fix b σ h1]
      rfl
    · exfalso
      apply h
      apply HeightOneSpectrum.ext
      have h2 : (σ * c⁻¹) b = b := by
        have : c⁻¹ b = -b := by
          have h3 : c⁻¹ (c b) = b := c.symm_apply_apply b
          rw [hc, map_neg] at h3
          exact neg_eq_iff_eq_neg.1 h3
        rw [AlgEquiv.mul_apply, this, map_neg, h1, neg_neg]
      have h4 : (σ * c⁻¹) • v'.asIdeal = W := by rw [← hvv, mul_smul, inv_smul_smul, hσ]
      rw [hWQ.over, ← h4, under_smul_of_fix b _ h2]
      rfl

end General


open Classical in
theorem splitsC_main : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime → SplitsC H.E p → ∀ v : HeightOneSpectrum (𝓞 H.E), OverP H p v → Ideal.absNorm v.asIdeal = p ∧ ((p : ℕ) : 𝓞 H.E) ∉ v.asIdeal ^ 2 ∧ IsSplitPl H v ∧ ∀ (Q : HeightOneSpectrum (𝓞 H.K)), ((p : ℕ) : 𝓞 H.K) ∈ Q.asIdeal → ∀ v', ConjPl H.conj.toRingEquiv v v' → OverP H p v' ∧ (v.under (𝓞 H.K) = Q ↔ v'.under (𝓞 H.K) ≠ Q) := by
  intro R H p hp hs v hv
  have hG : IsGalois ℚ H.E := H.hostE_isGalois
  have hsq := H.sqrtMinusD_sq
  have hc := H.conj_sqrtMinusD
  have hb0 : H.sqrtMinusD ≠ 0 := by
    intro h
    rw [h] at hsq
    have : (H.d : H.E) = 0 := by linear_combination hsq
    have h1 : H.d = 0 := by exact_mod_cast this
    have := H.qd_big.2
    omega
  have hb : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ H.sqrtMinusD = H.sqrtMinusD ∨ σ H.sqrtMinusD = -H.sqrtMinusD := by
    intro σ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [← map_pow, hsq, map_neg, map_natCast]
  obtain ⟨h1, h2, h3⟩ := splitsC_place hp hs v hv
  refine ⟨h1, h2, ?_, fun Q hQ v' hvv => ⟨?_, ?_⟩⟩
  · by_contra hn
    unfold IsSplitPl at hn
    push Not at hn
    have hle : H.conj • v.asIdeal ≤ v.asIdeal := by
      intro y hy
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
      obtain ⟨z, hz, hzv⟩ := hn _ hy
      have e : z = y := RingOfIntegers.ext (hz.trans (H.conj.apply_symm_apply (y : H.E)))
      exact e ▸ hzv
    obtain ⟨w, hw, -⟩ := existsUnique_conjPl H.conj.toRingEquiv v
    have hw' := (conjPl_iff_smul H.conj v w).1 hw
    have heq : H.conj • v.asIdeal = v.asIdeal := by
      rw [hw'] at hle ⊢
      exact w.isMaximal.eq_of_le v.isPrime.ne_top hle
    rw [h3 _ heq] at hc
    have hc' : H.sqrtMinusD = -H.sqrtMinusD := hc
    exact hb0 (by linear_combination (1 / 2 : H.E) * hc')
  · exact ((conjPl_iff_mem _ v v').1 hvv _ _ (by simp)).1 hv
  · exact under_eq_iff_under_ne hp hs H.sqrtMinusD hb0 hb H.conj hc v v' hv ((conjPl_iff_smul H.conj v v').1 hvv) Q hQ

end GlobalTheory.Mem.Chr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_unramified_ae_and_exists_level : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), {v | ¬ χ.UnrAt v}.Finite ∧ ∀ v, ∃ n, χ.LevelLe v n := by
  first | exact @GlobalTheory.Mem.UnrAe.unr_ae_and_level | exact GlobalTheory.Mem.UnrAe.unr_ae_and_level | (intros; apply GlobalTheory.Mem.UnrAe.unr_ae_and_level <;> assumption)
end

