module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPtCompClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliSchemeAffineFrameCoverTwoEigenParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1972

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalMvPolynomialLocalization
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.DedekindDimFormula
open ReciprocityTheory.CA

theorem isMaximal_comap_C {o : Type} [CommRing o] [IsJacobsonRing o] (N : ℕ)
    (𝔑 : Ideal (MvPolynomial (Fin N) o)) [𝔑.IsMaximal] :
    (𝔑.comap (MvPolynomial.C : o →+* MvPolynomial (Fin N) o)).IsMaximal := by
  have hi := MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing 𝔑
  letI := Ideal.Quotient.field 𝔑
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hi
    (⊥ : Ideal (MvPolynomial (Fin N) o ⧸ 𝔑))
  rwa [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at this

theorem isCM_localization (o : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] :
    ∃ δ : ℕ, ∀ (p : Ideal o) [p.IsMaximal],
      IsCM (Localization.AtPrime p) ∧ ringKrullDim (Localization.AtPrime p) = δ := by
  by_cases hf : IsField o
  · refine ⟨0, fun p _ => ?_⟩
    letI := hf.toField
    have hp : p = ⊥ := (Ideal.eq_bot_or_top p).resolve_right (Ideal.IsMaximal.ne_top inferInstance)
    have hd : ringKrullDim (Localization.AtPrime p) = 0 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hp,
        Ideal.height_bot]
      rfl
    refine ⟨⟨inferInstance, 0, by rw [hd]; rfl, ?_⟩, hd⟩
    refine ⟨[], rfl, by simp, ?_⟩
    rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simp)]
    exact RingTheory.Sequence.IsWeaklyRegular.nil _ _
  · refine ⟨1, fun p _ => ?_⟩
    have hp : p ≠ ⊥ := by
      intro h
      exact hf (Ring.isField_iff_maximal_bot.mpr (h ▸ inferInstance))
    haveI : IsDiscreteValuationRing (Localization.AtPrime p) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain o hp _
    have hd := IsDiscreteValuationRing.ringKrullDim_eq_one (Localization.AtPrime p)
    refine ⟨⟨inferInstance, 1, by rw [hd]; rfl, ?_⟩, by rw [hd]; rfl⟩
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
    have hm : ϖ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := hϖ.not_isUnit
    refine ⟨[ϖ], rfl, by simpa using hm, ?_⟩
    rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simpa using hm),
      RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    exact IsSMulRegular.of_ne_zero hϖ.ne_zero

theorem exists_maximal_mvPolynomial_localization' {o : Type} [CommRing o] (N : ℕ) (p : Ideal o) [p.IsMaximal] (𝔑 : Ideal (MvPolynomial (Fin N) o)) [𝔑.IsMaximal]
    (hc : 𝔑.comap (MvPolynomial.C : o →+* MvPolynomial (Fin N) o) = p) :
    ∃ (𝔑' : Ideal (MvPolynomial (Fin N) (Localization.AtPrime p))) (_ : 𝔑'.IsMaximal),
      𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ∧
      Nonempty (Localization.AtPrime 𝔑' ≃+* Localization.AtPrime 𝔑) ∧ 𝔑'.height = 𝔑.height := by
  classical
  letI : Algebra (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.algebraMvPolynomial
  let W : Submonoid (MvPolynomial (Fin N) o) := p.primeCompl.map (MvPolynomial.C (σ := Fin N))
  haveI hL : IsLocalization W (MvPolynomial (Fin N) (Localization.AtPrime p)) :=
    MvPolynomial.isLocalization p.primeCompl (Localization.AtPrime p)
  have hdisj : Disjoint (W : Set (MvPolynomial (Fin N) o)) (𝔑 : Set _) := by
    rw [Set.disjoint_left]
    rintro x ⟨m, hm, rfl⟩ hx
    exact hm (hc ▸ (show m ∈ 𝔑.comap MvPolynomial.C from hx))
  let 𝔑' := 𝔑.map (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))
  haveI hP : 𝔑'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint W _ 𝔑 inferInstance hdisj
  have hcm : 𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) = 𝔑 :=
    IsLocalization.under_map_of_isPrime_disjoint W _ inferInstance hdisj
  haveI hM : 𝔑'.IsMaximal := by
    refine ⟨⟨hP.ne_top, fun J hJ => ?_⟩⟩
    by_contra hJt
    have h1 : 𝔑 ≤ J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) :=
      hcm ▸ Ideal.comap_mono hJ.le
    have h2 : J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) ≠ ⊤ := by
      intro h
      apply hJt
      rw [Ideal.eq_top_iff_one]
      have : (1 : MvPolynomial (Fin N) o) ∈ J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p))) := h ▸ Submodule.mem_top
      simpa using this
    have h3 := (‹𝔑.IsMaximal›.eq_of_le h2 h1)
    have h4 : J = 𝔑' := by
      have h5 := IsLocalization.map_under W (MvPolynomial (Fin N) (Localization.AtPrime p)) J
      change Ideal.map _ (J.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))) = J at h5
      rw [← h3] at h5
      exact h5.symm
    exact hJ.ne' h4
  refine ⟨𝔑', hM, ?_, ?_, IsLocalization.height_map_of_disjoint W 𝔑 hdisj⟩
  · haveI : (𝔑'.comap (MvPolynomial.C : Localization.AtPrime p →+* _)).IsPrime := Ideal.comap_isPrime _ _
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : (MvPolynomial.C (algebraMap o (Localization.AtPrime p) x) : MvPolynomial (Fin N) (Localization.AtPrime p)) =
        algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)) (MvPolynomial.C x) := by
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C]
    rw [e]
    exact Ideal.mem_map_of_mem _ (by rw [← hc] at hx; exact hx)
  · haveI h0 : IsLocalization.AtPrime (Localization.AtPrime 𝔑')
        (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization W _ 𝔑'
    haveI : IsLocalization 𝔑.primeCompl (Localization.AtPrime 𝔑') := by
      have hsub : (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl = 𝔑.primeCompl :=
        Submonoid.ext fun x => by simp only [Ideal.mem_primeCompl_iff, hcm]
      have h0' : IsLocalization (𝔑'.comap (algebraMap (MvPolynomial (Fin N) o) (MvPolynomial (Fin N) (Localization.AtPrime p)))).primeCompl (Localization.AtPrime 𝔑') := h0
      rw [hsub] at h0'
      exact h0'
    exact ⟨(IsLocalization.algEquiv 𝔑.primeCompl (Localization.AtPrime 𝔑') (Localization.AtPrime 𝔑)).toRingEquiv⟩

theorem polyEquidim : ∀ (o : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [IsJacobsonRing o] (N : ℕ),
    ∃ d : ℕ, ∀ (𝔑 : Ideal (MvPolynomial (Fin N) o)) [𝔑.IsMaximal],
      IsCM (Localization.AtPrime 𝔑) ∧ 𝔑.height = (d : ℕ∞) := by
  intro o _ _ _ _ N
  obtain ⟨δ, hδ⟩ := isCM_localization o
  refine ⟨δ + N, fun 𝔑 _ => ?_⟩
  haveI := isMaximal_comap_C N 𝔑
  obtain ⟨hCM, hdim⟩ := hδ (𝔑.comap (MvPolynomial.C : o →+* MvPolynomial (Fin N) o))
  obtain ⟨𝔑', h𝔑', hc, ⟨e⟩, hh⟩ := exists_maximal_mvPolynomial_localization' N _ 𝔑 rfl
  have h := isCM_localization_mvPolynomial hCM N 𝔑' hc
  refine ⟨h.1.of_ringEquiv e, ?_⟩
  have h2 := h.2
  rw [hdim, hh] at h2
  have h3 : ((𝔑.height : ℕ∞) : WithBot ℕ∞) = (((δ + N : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [h2]; push_cast; ring
  exact WithBot.coe_injective h3

end GlobalTheory.DedekindDimFormula

namespace GlobalTheory.DedekindDimFormula

theorem affine_heights (o A : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [IsJacobsonRing o]
    [CommRing A] [IsDomain A] [Algebra o A] [Algebra.FiniteType o A] :
    ∃ h : ℕ, (∀ (M : Ideal A) [M.IsMaximal], M.height = (h : ℕ∞)) ∧
      ∀ (P M : Ideal A) [P.IsPrime] [M.IsMaximal],
        (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) := by
  obtain ⟨N, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType o A›
  obtain ⟨d, hd⟩ := polyEquidim o N
  set Q := RingHom.ker (f : MvPolynomial (Fin N) o →+* A) with hQdef
  haveI : Q.IsPrime := RingHom.ker_isPrime _
  let e : (MvPolynomial (Fin N) o ⧸ Q) ≃+* A :=
    RingHom.quotientKerEquivOfSurjective (f := (f : MvPolynomial (Fin N) o →+* A)) hf
  obtain ⟨M₀, hM₀⟩ := Ideal.exists_maximal (MvPolynomial (Fin N) o ⧸ Q)
  haveI : (M₀.comap (Ideal.Quotient.mk Q)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hQle : Q.height ≤ d := by
    rw [← (hd (M₀.comap (Ideal.Quotient.mk Q))).2]
    exact Ideal.height_mono fun x hx => by
      simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx, M₀.zero_mem]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Q.height = k := by
    have : Q.height ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top d) hQle
    exact ⟨Q.height.toNat, (ENat.coe_toNat this).symm⟩
  have hkd : k ≤ d := by rw [hk] at hQle; exact_mod_cast hQle
  refine ⟨d - k, fun M _ => ?_, fun P M _ _ => ?_⟩
  · haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
    haveI : ((M.comap e).comap (Ideal.Quotient.mk Q)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨hCM, hh⟩ := hd ((M.comap e).comap (Ideal.Quotient.mk Q))
    have e1 := GlobalTheory.FinTypeIntCatenary.height_comap_mk Q (M.comap e) hCM
    rw [hh, hk, RingEquiv.height_comap] at e1
    have : ((d - k : ℕ) : ℕ∞) + k = M.height + k := by
      rw [← Nat.cast_add, Nat.sub_add_cancel hkd, e1, add_comm]
    exact (WithTop.add_right_cancel (ENat.coe_ne_top k) this).symm
  · haveI : (P.comap e).IsPrime := Ideal.comap_isPrime _ _
    haveI : (M.comap e).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective
    have h := GlobalTheory.FinTypeIntCatenary.height_le_of_equidim d (fun 𝔑 _ => hd 𝔑) Q (P.comap e) (M.comap e)
    rw [RingEquiv.height_comap, RingEquiv.height_comap] at h
    have hdim : ringKrullDim ((MvPolynomial (Fin N) o ⧸ Q) ⧸ P.comap e) = ringKrullDim (A ⧸ P) :=
      ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e
        (Ideal.map_comap_of_surjective _ e.surjective P).symm)
    rwa [hdim] at h

end GlobalTheory.DedekindDimFormula

namespace GlobalTheory.DedekindDimFormula

end GlobalTheory.DedekindDimFormula
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonKltCentreOfNotKltAfterAdding
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep.Centre

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem centreAt_of_dominatesStalk {E : DivOver p} {z : X} (h : DominatesStalk E.ring z) :
    CentreAt E z := by
  refine ⟨by rintro _ ⟨a, rfl⟩; exact h.1 a, ?_⟩
  rintro f ⟨a, ha⟩ h0
  have hinv : ((f⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring :=
    (E.ord_nonneg_iff f⁻¹).1 (by rw [E.ord_inv, h0]; simp)
  have hu : IsUnit a := by
    by_contra hu
    have h1 := (E.ring.coe_mem_nonunits_iff (a := ⟨_, h.1 a⟩)).mp (h.2 a hu)
    refine h1 (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_))
    change algebraMap _ X.functionField a * _ = 1
    rw [ha]
    exact f.mul_inv
  obtain ⟨u, rfl⟩ := hu
  refine ⟨((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z), ?_⟩
  have e : algebraMap _ X.functionField
      ((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z) * (f : X.functionField) = 1 := by
    rw [← ha, ← map_mul, Units.inv_mul, map_one]
  exact (Units.inv_eq_of_mul_eq_one_left e).symm

theorem exists_centreAt {E : DivOver p} {x : X} (h : E.Through x) :
    ∃ z, z ⤳ x ∧ CentreAt E z :=
  have ⟨z, hz, hd⟩ := exists_specializes_dominatesStalk_of_regAt X E.ring x h
  ⟨z, hz, centreAt_of_dominatesStalk hd⟩

theorem exists_isLogEqn_add [IsLocallyNoetherian X] {n : ℕ} {Δ D : X → ℚ} {η : RatForms p n}
    {x : X} {m : ℕ} {g : X.functionFieldˣ} (hD : IsQCart D) (hm : 0 < m)
    (hg : IsLogEqn p Δ η x m g) :
    ∃ (m' : ℕ) (g' : X.functionFieldˣ), 0 < m' ∧ IsLogEqn p (Δ + D) η x m' g' := by
  obtain ⟨r, D₀, hr, -, rfl⟩ := hD
  obtain ⟨d, hd⟩ := D₀.exists_isEqn x
  obtain ⟨V, hV, hdV⟩ := hd.exists_nhds
  refine ⟨m * r, g ^ r * d ^ m, Nat.mul_pos hm hr, fun z hz E hE => ?_⟩
  have h1 := (hdV z (hz.mem_open V.isOpen hV)).mult_eq
  rw [← hE.ord_eq] at h1
  have h2 := hg z hz E hE
  have : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [E.ord_mul, E.ord_pow, E.ord_pow, Pi.add_apply, qWeil, h1]
  push_cast
  rw [← h2]
  field_simp
  ring

theorem exists_isNkltCentre : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D : X → ℚ) (x : X), IsQCart D → KltAt p n Δ x → ¬ KltAt p n (Δ + D) x →
    ∃ z, z ⤳ x ∧ IsNkltCentre p n (Δ + D) z := by
  intro X _ _ _ p n hp hn Δ D x hD hk hnk
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨η, m, g, hη, hm, hg, -⟩ := hk
  obtain ⟨m', g', hm', hg'⟩ := exists_isLogEqn_add hD hm hg
  rw [hg'.kltAt_iff hn hη hm'] at hnk
  push_neg at hnk
  obtain ⟨E, hE, hd⟩ := hnk
  obtain ⟨z, hz, hc⟩ := exists_centreAt hE
  exact ⟨z, hz, E, η, m', g', hη, hm', fun w hw => hg' w (hw.trans hz), hc, hd⟩

end GlobalTheory.PairStep.Centre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingExtensionNormalCompactificatio
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.ExtendNormal

open FromGeneric

theorem valR_eq_one {X : Scheme.{0}} [IsReduced X] {U : X.Opens} {K : Type} [Field K] (x : Sp K ⟶ X)
    (hx : Set.range x ⊆ U) (hd : ∀ z ∈ U, x (IsLocalRing.closedPoint K) ⤳ z) {f : Γ(X, U)} (hf : valR x U f = 1)
    {R : Type} [CommRing R] (x' : Sp R ⟶ X) (hx' : Set.range x' ⊆ U) : valR x' U f = 1 := by
  have h : ⊤ ≤ x ⁻¹ᵁ U := fun z _ => hx ⟨z, rfl⟩
  have h' : ⊤ ≤ x' ⁻¹ᵁ U := fun z _ => hx' ⟨z, rfl⟩
  have h0 : (x.appLE U ⊤ h).hom (f - 1) = 0 := by
    rw [valR, dite_eq_left h] at hf
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1
    rw [map_sub, map_sub, map_one, map_one, map_zero]
    exact sub_eq_zero.2 hf
  have h1 : f - 1 = 0 := by
    refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun z hz => ?_)
    have h2 : x (IsLocalRing.closedPoint K) ∈ X.basicOpen (f - 1) :=
      (hd z (X.basicOpen_le _ hz)).mem_open (X.basicOpen _).isOpen hz
    have h3 := Scheme.basicOpen_appLE x ⊤ U h (f - 1)
    rw [show (x.appLE U ⊤ h) (f - 1) = 0 from h0, Scheme.basicOpen_zero] at h3
    have h4 : IsLocalRing.closedPoint K ∈ (⊤ ⊓ x ⁻¹ᵁ X.basicOpen (f - 1) : (Sp K).Opens) := ⟨trivial, h2⟩
    rw [← h3] at h4
    exact h4.elim
  rw [sub_eq_zero.1 h1, valR, dite_eq_left h', map_one, map_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem exists_frame_local {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X}
    {τ : E →+* ℂ} {p q : ℕ} (hcov : FrameCover t π s V (HermitianCompactForm.chi c τ) p q) {R : Type} [CommRing R] [IsLocalRing R]
    (x : Sp R ⟶ X) (hx : x (IsLocalRing.closedPoint R) ∈ V) :
    ∃ (j : c.F →+* R) (v : Fin p → (epsAt (x ≫ π) ⟶ t.G)) (w : Fin q → (epsAt (x ≫ π) ⟶ t.G)),
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w := by
  obtain ⟨W, hW, j, v, w, hz, h⟩ := hcov _ hx
  have : IsOpenImmersion (show Sp Γ(X, W) ⟶ X from hW.fromSpec) := inferInstanceAs (IsOpenImmersion hW.fromSpec)
  obtain ⟨m, hm⟩ := exists_lift (show Sp Γ(X, W) ⟶ X from hW.fromSpec) x (range_subset _
    (show Sp Γ(X, W) ⟶ X from hW.fromSpec).isOpenEmbedding.isOpen_range (by
      rw [show Set.range _ = _ from hW.range_fromSpec]; exact hz))
  obtain ⟨v', w', h', -⟩ := exists_pull m h hm
  exact ⟨_, v', w', h'⟩

theorem unitAtPt_of_dvr {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X}
    {τ : E →+* ℂ} {p q : ℕ} (hcov : FrameCover t π s V (HermitianCompactForm.chi c τ) p q) {B : Scheme.{0}} [IsIntegral B]
    [IsLocallyNoetherian B] (hB : ∀ y : B, IsIntegrallyClosed (B.presheaf.stalk y)) (io : B ⟶ X)
    (hio : ∀ y, io y ∈ V) {j₀ : c.F →+* B.functionField} {v₀ w₀}
    (h₀ : IsFrame t π s V (HermitianCompactForm.chi c τ) (p := p) (q := q) j₀ (genPt B ≫ io) v₀ w₀) {δ : B.functionField} (hδ : δ ≠ 0)
    (hdvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R B.functionField]
      [IsFractionRing R B.functionField] (j : c.F →+* R) (x : Sp R ⟶ X) v w M N,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w →
      IsChg t π (algebraMap R B.functionField) x v w (genPt B ≫ io) v₀ w₀ M N →
      ∃ u : Rˣ, N.det * algebraMap R B.functionField u = M.det * δ) (y : B) :
    UnitAtPt t π s V (HermitianCompactForm.chi c τ) io v₀ w₀ δ y := by
  obtain ⟨j, v, w, h⟩ := exists_frame_local hcov (locPt B y ≫ io) (by rw [locPt_comp_closedPoint]; exact hio y)
  obtain ⟨-, M, N, hc⟩ := exists_chg (algebraMap (B.presheaf.stalk y) B.functionField) h h₀
    (by rw [genPt_eq y, Category.assoc])
  obtain ⟨hM, hN⟩ := chg_isUnit h h₀ hc
  have hφ : M.det * δ / N.det ≠ 0 := div_ne_zero (mul_ne_zero hM.ne_zero hδ) hN.ne_zero
  have key : ∀ z : B, z ⤳ y → IsDiscreteValuationRing (B.presheaf.stalk z) →
      ∃ u : (B.presheaf.stalk z)ˣ, algebraMap _ B.functionField (u : B.presheaf.stalk z) = M.det * δ / N.det := by
    intro z hz _
    let g : B.presheaf.stalk y →+* B.presheaf.stalk z := (B.presheaf.stalkSpecializes hz).hom
    have hg : (algebraMap (B.presheaf.stalk z) B.functionField).comp g =
        algebraMap (B.presheaf.stalk y) B.functionField :=
      congrArg CommRingCat.Hom.hom (B.presheaf.stalkSpecializes_comp ((genericPoint_spec B).specializes trivial) hz)
    obtain ⟨v', w', h', a, b⟩ := exists_pull g h rfl
    obtain ⟨u, hu⟩ := hdvr _ _ _ v' w' M N h' ⟨by
      rw [← Category.assoc, ← DetExtendZero.spMap_comp, hg]; exact hc.1, fun i => by
      simp only [a, ← Category.assoc, ← DetExtendZero.dual_comp, hg]; exact hc.2.1 i, fun i => by
      simp only [b, ← Category.assoc, ← DetExtendZero.dual_comp, hg]; exact hc.2.2 i⟩
    exact ⟨u, by rw [← hu, mul_div_cancel_left₀ _ hN.ne_zero]⟩
  obtain ⟨a, ha⟩ := GlobalTheory.Hartogs.regAt_of_forall_dvr B hB (M.det * δ / N.det) y fun z hz hz' => by
    obtain ⟨u, hu⟩ := key z hz hz'
    exact ⟨u, hu⟩
  obtain ⟨b, hb⟩ := GlobalTheory.Hartogs.regAt_of_forall_dvr B hB (M.det * δ / N.det)⁻¹ y fun z hz hz' => by
    obtain ⟨u, hu⟩ := key z hz hz'
    exact ⟨(u⁻¹ : (B.presheaf.stalk z)ˣ), by rw [← hu, map_units_inv]⟩
  have hab : a * b = 1 := IsFractionRing.injective (B.presheaf.stalk y) B.functionField (by
    rw [map_mul, map_one, ha, hb, mul_inv_cancel₀ hφ])
  refine ⟨j, v, w, M, N, Units.mkOfMulEqOne a b hab, h, hc, ?_⟩
  rw [Units.val_mkOfMulEqOne, ha, mul_div_cancel₀ _ hN.ne_zero]

theorem exists_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z : Model Xo c β') (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (σZ : RuleY Z) (σ : RuleU Xo c), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → τ (H.rt : E) = H.rt0 → SecY Z (compactOf Z U) τ σZ → NzY Z (compactOf Z U) τ σZ → SecU Xo c U τ σ → Restricts Z U τ σZ σ → ∃ σb : RuleY Y, SecY Y (compactOf Y U) τ σb ∧ NzY Y (compactOf Y U) τ σb ∧ Restricts Y U τ σb σ := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ β' Z U τ σZ σ hn hcl hU hτ hσZ hZ hσ hres
  obtain ⟨V, hV, hint⟩ := _root_.GlobalTheory.DetLine.exists_open_compactOf_isIntegral E H D l Xo c O β Y U hn hcl hU
  have := Y.jQ_open
  have : IsProper (genStr Y) := isProper_genStr Y
  have : IsLocallyNoetherian (gen Y) := LocallyOfFiniteType.isLocallyNoetherian (genStr Y)
  have : IsReduced (gen Y) := by
    have := fun y => (hn y).1
    exact isReduced_of_isReduced_stalk _
  have : IsReduced (Xo.XF c) := isReduced_of_isOpenImmersion Y.jQ
  have hB : ∀ y : V.toScheme, IsIntegrallyClosed (V.toScheme.presheaf.stalk y) := fun y =>
    haveI := (hn (V.ι y)).2
    IsIntegrallyClosed.of_equiv (asIso (V.ι.stalkMap y)).commRingCatIsoToRingEquiv
  have hcov := frameCover_gen E H D l Xo c O β Y V τ hτ
  rw [hV] at hcov
  have hio : ∀ y, V.ι y ∈ compactOf Y U := fun y => hV ▸ y.2
  have hpt : (genPt V.toScheme ≫ V.ι) (IsLocalRing.closedPoint _) = V.ι (genericPoint V.toScheme) :=
    locPt_comp_closedPoint V.ι _
  have hsp : ∀ z ∈ compactOf Y U, V.ι (genericPoint V.toScheme) ⤳ z := fun z hz =>
    (genericPoint_specializes (α := V.toScheme) (⟨z, (hV ▸ hz : z ∈ (V : Set (gen Y)))⟩ : V.toScheme)).map V.ι.continuous
  have hgen : V.ι (genericPoint V.toScheme) ∈ Y.jQ '' (U : Set (Xo.XF c)) := by
    obtain ⟨z, hz⟩ := closure_nonempty_iff.1 ⟨_, hio (genericPoint V.toScheme)⟩
    exact (hsp z (subset_closure hz)).mem_open (Y.jQ.isOpenEmbedding.isOpenMap _ U.isOpen) hz
  obtain ⟨j₀, v₀, w₀, h₀⟩ := exists_frame_local hcov (genPt V.toScheme ≫ V.ι) (by rw [hpt]; exact hio _)
  have main : ∀ (K : Type) [Field K] (xb : Sp K ⟶ gen Y) (j₀ : c.F →+* K) v₀ w₀,
      xb (IsLocalRing.closedPoint K) = V.ι (genericPoint V.toScheme) → FrY Y (compactOf Y U) τ j₀ xb v₀ w₀ →
      ∃ δ : K, δ ≠ 0 ∧ (∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R K]
        [IsFractionRing R K] (j : c.F →+* R) (x : Sp R ⟶ gen Y) v w M N, FrY Y (compactOf Y U) τ j x v w →
        IsChg Y.t (genι Y) (algebraMap R K) x v w xb v₀ w₀ M N → ∃ u : Rˣ, N.det * algebraMap R K u = M.det * δ) ∧
        ∀ σb : RuleY Y, SecY Y (compactOf Y U) τ σb → NzY Y (compactOf Y U) τ σb → σb K xb v₀ w₀ = δ →
          Restricts Y U τ σb σ := by
    intro K _ xb j₀ v₀ w₀ hxb h₀
    obtain ⟨x, rfl⟩ : ∃ x : Sp K ⟶ Xo.XF c, x ≫ Y.jQ = xb :=
      ⟨IsOpenImmersion.lift Y.jQ xb (range_subset _ Y.jQ.isOpenEmbedding.isOpen_range
        (hxb ▸ Set.image_subset_range _ _ hgen)), IsOpenImmersion.lift_fac _ _ _⟩
    have hxb' : Y.jQ (x (IsLocalRing.closedPoint K)) = V.ι (genericPoint V.toScheme) :=
      (Scheme.Hom.comp_apply _ _ _).symm.trans hxb
    have hxU : Set.range x ⊆ U := range_subset _ U.isOpen (by
      obtain ⟨z, hz, e⟩ := hgen
      rwa [Y.jQ.isOpenEmbedding.injective (hxb'.trans e.symm)])
    obtain ⟨v, w, h, sv, sw⟩ := (frame_transfer E H D l Xo c O β Y U τ K j₀ x).2 _ v₀ w₀ hxU h₀
    refine ⟨σ K x v w, ?_, fun R _ _ _ _ _ j xR vR wR M N hR hc => ?_, fun σb hb hnz e => ?_⟩
    · obtain ⟨vz, wz, hz, a, b⟩ := (frame_transfer E H D l Xo c O' β' Z U τ K j₀ x).1 v w h
      rw [← hres K j₀ x v w vz wz h hz a b]
      exact (hZ K j₀ _ vz wz hz).ne_zero
    · obtain ⟨vb, wb, hb, a, b⟩ := exists_pull (algebraMap R K) hR hc.1
      obtain ⟨v', w', h', sv', sw'⟩ := (frame_transfer E H D l Xo c O β Y U τ K _ x).2 _ vb wb hxU hb
      obtain ⟨u, hu⟩ := _root_.GlobalTheory.DetLine.DvrUnit.unit_in_integral_frame E H D l Xo c O β Y O' β' Z U τ σZ σ hσZ hZ hres R K j xR x _ vR wR v' w' vb wb
        hR h' hc.1 sv' sw' a b
      have hid : x = spMap (RingHom.id K) ≫ x := by rw [DetExtendZero.spMap_id, Category.id_comp]
      refine ⟨u, ?_⟩
      rw [← hu]
      refine sec_chg (g := RingHom.id K) hσ h' h ⟨hid, fun i => ?_, fun i => ?_⟩
      · refine (isCombination_iff_of_sameVecs E H D l Xo c O β Y K K _ x x _ v' vb v v₀ hid sv' sv _ i).2 ?_
        simp only [DetExtendZero.dual_id, Category.id_comp, a]
        exact hc.2.1 i
      · refine (isCombination_iff_of_sameVecs E H D l Xo c O β Y K K _ x x _ w' wb w w₀ hid sw' sw _ i).2 ?_
        simp only [DetExtendZero.dual_id, Category.id_comp, b]
        exact hc.2.2 i
    · obtain ⟨σ₁, h1, h2, h3⟩ := _root_.GlobalTheory.DetLine.Restrict.exists_restriction E H D l Xo c O β Y U τ σb hb
      obtain ⟨f, hf⟩ := GlobalTheory.detLine_exists_ratio E H l c _ _ _ _ _ τ _ _ U σ₁ σ
        (frameCover_univ E H D l Xo c U τ hτ) h1 (h3 hnz) hσ
      have e1 : valR x U f = 1 := by
        have e2 := hf K j₀ x v w h
        rw [← e, h2 K j₀ x v w v₀ w₀ h h₀ sv sw] at e2
        exact ((h3 hnz K j₀ x v w h).mul_right_cancel ((_root_.one_mul _).trans e2)).symm
      intro R _ j x' v' w' vb wb h' hb' a b
      rw [h2 R j x' v' w' vb wb h' hb' a b, hf R j x' v' w' h',
        valR_eq_one x hxU (fun z hz => ?_) e1 x' h'.2.1, _root_.one_mul]
      rw [← Y.jQ.isOpenEmbedding.isInducing.specializes_iff, hxb']
      exact hsp _ (subset_closure ⟨z, hz, rfl⟩)
  obtain ⟨δ, hδ, hdvr, hfin⟩ := main _ _ j₀ v₀ w₀ hpt h₀
  obtain ⟨σb, h1, h2, h3⟩ := exists_section E H l c _ _ _ _ _ τ _ _ V.toScheme V.ι _ inferInstance
    (V.range_ι.trans hV) hcov j₀ v₀ w₀ δ h₀ (unitAtPt_of_dvr hcov hB V.ι hio h₀ hδ hdvr)
  exact ⟨σb, h1, h2, hfin σb h1 h2 h3⟩

end GlobalTheory.DetLine.ExtendNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNotMemRingKrullDimQuotientEqOne
section
namespace GlobalTheory

theorem exists_prime_notMem_ringKrullDim_quotient_eq_one :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (h : R),
      h ≠ 0 → h ∈ IsLocalRing.maximalIdeal R →
      ∃ q : Ideal R, q.IsPrime ∧ h ∉ q ∧ ringKrullDim (R ⧸ q) = 1 := by
  intro R _ _ _ _ h h0 hhm
  obtain ⟨q, hq, -, h1⟩ := exists_mem_height_map_le_one (IsLocalRing.maximalIdeal R)
    (PrimeSpectrum.basicOpen h).isOpen ⟨⟨⊥, inferInstance⟩, by simpa using h0, bot_le⟩
  have hq' : h ∉ q.asIdeal := hq
  refine ⟨q.asIdeal, q.isPrime, hq', ?_⟩
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have hqm : q.asIdeal ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal q.isPrime.ne_top
  have hmax : ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk q.asIdeal)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (by simpa using hqm)
  have h2 : ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk q.asIdeal)).height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff]
    intro e
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk q.asIdeal) hhm
    rw [e, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hq' this
  have h3 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h2)
  have : IsLocalRing (R ⧸ q.asIdeal) := IsLocalRing.of_surjective' _ hsurj
  have he : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk q.asIdeal) =
      IsLocalRing.maximalIdeal (R ⧸ q.asIdeal) := IsLocalRing.eq_maximalIdeal hmax
  rw [he] at h3
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h3]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHorizontalLieDeterminantSectionOfConjStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHorizontalLieDeterminantSection_of_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c) (e : c.F →+* ℂ), SecU Xo c U τ σ → IsFlatAt Xo c U τ σ ((starRingEnd ℂ).comp e) → IsFlatAt Xo c U τ σ e := by
  first | exact @GlobalTheory.isFlatAt_of_conj | exact GlobalTheory.isFlatAt_of_conj | (intros; apply GlobalTheory.isFlatAt_of_conj <;> assumption)
end

