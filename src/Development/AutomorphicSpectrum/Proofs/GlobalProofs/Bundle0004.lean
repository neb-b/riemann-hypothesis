module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DifferentDvdRamifiedPrimePower
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Glob

theorem exists_prime_mem_of_natCast_mem {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime]
    (t : ℕ) (ht : t ≠ 0) (htP : (t : R) ∈ P) : ∃ p : ℕ, p.Prime ∧ p ∣ t ∧ (p : R) ∈ P :=
  _root_.UpperTheory.Reformulated.B.DYdc5.main P t ht htP

theorem prime_pow_dvd_span_of_dvd_differentIdeal (E : Type) [Field E] [NumberField E] (t : ℕ)
    (ht : t ≠ 0)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (t : 𝓞 E) ∈ P)
    (P : Ideal (𝓞 E)) (hPp : Prime P) (i : ℕ) (hi : P ^ i ∣ differentIdeal ℤ (𝓞 E)) :
    P ^ i ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · simp
  have hPD : P ∣ differentIdeal ℤ (𝓞 E) := (dvd_pow_self P hipos.ne').trans hi
  have hP0 : P ≠ ⊥ := hPp.ne_zero
  haveI hPprime : P.IsPrime := Ideal.isPrime_of_prime hPp
  obtain ⟨p, hp, hpt, hpP⟩ := exists_prime_mem_of_natCast_mem P t ht (h P hPprime hP0 hPD)
  have hp0 : ((p : 𝓞 E)) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hS0 : Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} ≠ 0 := by
    intro h0
    have := Ideal.span_singleton_eq_bot.1 h0
    exact pow_ne_zero _ hp0 this
  obtain ⟨J, hJ, hnd⟩ :=
    (FiniteMultiplicity.of_not_isUnit hPp.not_unit hS0).exists_eq_pow_mul_and_not_dvd
  have hnot := GlobalTheory.T.prime_power_not_dvd_different E P J p _ hp hpP hnd hJ
  have hlt : i < multiplicity P (Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)}) := by
    by_contra hle
    exact hnot ((pow_dvd_pow P (not_lt.1 hle)).trans hi)
  have h1 : P ^ i ∣ Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
    exact ((pow_dvd_pow P hlt.le).mul_right J).trans (dvd_of_eq hJ.symm)
  refine h1.trans ?_
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton]
  exact pow_dvd_pow_of_dvd (Nat.cast_dvd_cast hpt) _

theorem differentIdeal_dvd_span_pow : ∀ (E : Type) [Field E] [NumberField E] (t : ℕ), t ≠ 0 →
    (∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (t : 𝓞 E) ∈ P) →
    differentIdeal ℤ (𝓞 E) ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
  intro E _ _ t ht h
  have hD : differentIdeal ℤ (𝓞 E) ≠ 0 := differentIdeal_ne_bot
  have key : ∀ I : Ideal (𝓞 E), I ≠ 0 → I ∣ differentIdeal ℤ (𝓞 E) →
      I ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_coprime with
    | h0 => exact fun h0 => absurd rfl h0
    | h1 hu => exact fun _ _ => hu.dvd
    | hpr i hq =>
      exact fun _ hd => prime_pow_dvd_span_of_dvd_differentIdeal E t ht h _ hq i hd
    | hcp hxy hx hy =>
      intro h0 hd
      exact hxy.mul_dvd (hx (left_ne_zero_of_mul h0) ((dvd_mul_right _ _).trans hd))
        (hy (right_ne_zero_of_mul h0) ((dvd_mul_left _ _).trans hd))
  exact key _ hD dvd_rfl

end GlobalTheory.CompanionTheory.Glob
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.KaehlerBasisOnLocalizationAway
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.Glob.ResKCoords

theorem isCoords_basicOpen_of_away :
    ∀ (K : Type) [Field K] (Y : Scheme.{0}) (g : Y ⟶ Sp K) (U : Y.affineOpens) (s : Γ(Y, U.1)) {n : ℕ}
      (x : Fin n → Γ(Y, U.1)),
      (letI := secAlgebra g U.1;
        ∀ (B : Type) [CommRing B] [Algebra Γ(Y, U.1) B] [Algebra K B] [IsScalarTower K Γ(Y, U.1) B]
          [IsLocalization.Away s B],
          LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) ∧
            Submodule.span B (Set.range fun i =>
              KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) = ⊤) →
        IsCoords g (Y.basicOpen s) (fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)) := by
  intro K _ Y g U s n x h
  letI aU : Algebra K Γ(Y, U.1) := secAlgebra g U.1
  letI aB : Algebra K Γ(Y, Y.basicOpen s) := secAlgebra g (Y.basicOpen s)
  letI aUB : Algebra Γ(Y, U.1) Γ(Y, Y.basicOpen s) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op).hom.toAlgebra
  haveI tower : IsScalarTower K Γ(Y, U.1) Γ(Y, Y.basicOpen s) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appLE ⊤ (Y.basicOpen s) (fun _ _ => trivial)).hom = _
    have e : g.appLE ⊤ U.1 (fun _ _ => trivial) ≫ Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op =
        g.appLE ⊤ (Y.basicOpen s) (fun _ _ => trivial) := by
      exact Scheme.Hom.appLE_map _ _ _
    rw [← e]
    rfl
  haveI loc : IsLocalization.Away s Γ(Y, Y.basicOpen s) := U.2.isLocalization_basicOpen s
  exact h Γ(Y, Y.basicOpen s)

end GlobalTheory.CompanionTheory.Glob.ResKCoords
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.KaehlerBasisSpreadsToNeighbourhood
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.KaehlerSpread

open KaehlerDifferential

noncomputable abbrev diffMap (K : Type) {A : Type} [Field K] [CommRing A] [Algebra K A] {n : ℕ}
    (x : Fin n → A) : (Fin n →₀ A) →ₗ[A] Ω[A⁄K] :=
  Finsupp.linearCombination A fun i => D K A (x i)

theorem map_diffMap_eq (K : Type) {A : Type} [Field K] [CommRing A] [Algebra K A] {n : ℕ}
    (x : Fin n → A) (S : Submonoid A) (B : Type) [CommRing B] [Algebra A B] [Algebra K B]
    [IsScalarTower K A B] [IsLocalization S B] :
    (IsLocalizedModule.mapExtendScalars S
      (Finsupp.mapRange.linearMap (Algebra.linearMap A B) : (Fin n →₀ A) →ₗ[A] (Fin n →₀ B))
      (map K K A B) B (diffMap K x)) =
      Finsupp.linearCombination B fun i => D K B (algebraMap A B (x i)) := by
  refine Finsupp.lhom_ext' fun i => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  have h1 : (Finsupp.single i (1 : B) : Fin n →₀ B) =
      Finsupp.mapRange.linearMap (Algebra.linearMap A B) (Finsupp.single i (1 : A)) := by
    simp
  rw [h1, IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply]
  simp [diffMap]

theorem bijective_linearCombination_iff {B M ι : Type} [CommRing B] [AddCommGroup M] [Module B M]
    (v : ι → M) :
    Function.Bijective (Finsupp.linearCombination B v) ↔
      LinearIndependent B v ∧ Submodule.span B (Set.range v) = ⊤ := by
  rw [Function.Bijective, ← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  rfl

theorem spread : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A] (P : Ideal A) [P.IsPrime] {n : ℕ} (x : Fin n → A), (LinearIndependent (Localization.AtPrime P) (fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) ∧ Submodule.span (Localization.AtPrime P) (Set.range fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) = ⊤) → ∃ s ∉ P, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [IsLocalization.Away s B], LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) ∧ Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) = ⊤ := by
  intro K A _ _ _ _ P _ n x hP
  classical
  let l₁ : (Fin n →₀ A) →ₗ[A] (Fin n →₀ Localization.AtPrime P) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization.AtPrime P))
  let l₂ : Ω[A⁄K] →ₗ[A] Ω[Localization.AtPrime P⁄K] :=
    KaehlerDifferential.map K K A (Localization.AtPrime P)
  have hP' : Function.Bijective (IsLocalizedModule.map P.primeCompl l₁ l₂ (diffMap K x)) := by
    have h := (bijective_linearCombination_iff _).mpr hP
    rw [← map_diffMap_eq K x P.primeCompl (Localization.AtPrime P)] at h
    exact h
  obtain ⟨s, hs, hbij⟩ :=
    Module.FinitePresentation.exists_notMem_bijective (diffMap K x) P l₁ l₂ hP'
  refine ⟨s, hs, ?_⟩
  intro B _ _ _ _ _
  rw [← bijective_linearCombination_iff, ← map_diffMap_eq K x (Submonoid.powers s) B]
  exact (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (Finsupp.mapRange.linearMap (Algebra.linearMap A B)) (KaehlerDifferential.map K K A B)).mpr hbij

end GlobalTheory.CompanionTheory.KaehlerSpread
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RegularSequenceGermsRegularLocal
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.ResKCoords

theorem map_maximalIdeal_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) :
    Ideal.map e (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by
  ext x
  rw [← Ideal.comap_symm, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  exact isUnit_map_iff e.symm x

theorem rsp_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) (m : ℕ) (r : Fin m → R) (h : FinalTheorems.Rsp R m r) :
    FinalTheorems.Rsp S m (fun i => e (r i)) := by
  refine ⟨?_, h.2.trans (ringKrullDim_eq_of_ringEquiv e)⟩
  have h1 : Set.range (fun i => e (r i)) = (e : R → S) '' Set.range r := by
    rw [← Set.range_comp]; rfl
  rw [h1, ← map_maximalIdeal_of_ringEquiv e, ← h.1]
  exact (Ideal.map_span e (Set.range r)).symm

theorem stalk_to_localization : ∀ (Y : Scheme.{0}) (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1),
    IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
    FinalTheorems.Rsp (Y.presheaf.stalk y) m (fun i => Y.presheaf.germ U.1 y hy (f i)) →
    IsRegularLocalRing (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) ∧
    FinalTheorems.Rsp (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) m
      (fun i => algebraMap Γ(Y, U.1) _ (f i)) ∧
    ∀ s : Γ(Y, U.1), y ∈ Y.basicOpen s ↔ s ∉ (U.2.primeIdealOf ⟨y, hy⟩).asIdeal := by
  intro Y U y hy hreg m f hr
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hy⟩ : U.1)
  haveI hloc : IsLocalization.AtPrime (Y.presheaf.stalk y) (U.2.primeIdealOf ⟨y, hy⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨y, hy⟩
  let e : Y.presheaf.stalk y ≃+* Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal :=
    (IsLocalization.algEquiv (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y)
      (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)).toRingEquiv
  have he : ∀ a : Γ(Y, U.1), e (Y.presheaf.germ U.1 y hy a) = algebraMap Γ(Y, U.1) _ a := fun a =>
    (IsLocalization.algEquiv (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y)
      (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)).commutes a
  refine ⟨IsRegularLocalRing.of_ringEquiv e, ?_, fun s => ?_⟩
  · have h := rsp_of_ringEquiv e m _ hr
    simpa only [he] using h
  · rw [Scheme.mem_basicOpen Y s y hy]
    have h := IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y)
      (U.2.primeIdealOf ⟨y, hy⟩).asIdeal s
    exact h.trans Iff.rfl

end GlobalTheory.CompanionTheory.ResKCoords
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothLocalRingFreeDifferentials
section
noncomputable section

namespace GlobalTheory.CompanionTheory.ResKCoords

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

theorem kaehler_atPrime_of_away (K A : Type) [Field K] [CommRing A] [Algebra K A] (D : ℕ) (s : Set A)
    (hs : Ideal.span s = ⊤)
    (h : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t))
    (P : Ideal A) [P.IsPrime] :
    Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
      Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  obtain ⟨t, ht, htP⟩ : ∃ t ∈ s, t ∉ P := by
    by_contra hc
    push_neg at hc
    exact (‹P.IsPrime›).ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  have hle : Submonoid.powers t ≤ P.primeCompl := by
    rintro _ ⟨n, rfl⟩
    exact fun hm => htP (‹P.IsPrime›.mem_of_pow_mem n hm)
  letI : Algebra (Localization.Away t) (Localization.AtPrime P) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers t) P.primeCompl hle
  haveI : IsScalarTower A (Localization.Away t) (Localization.AtPrime P) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  haveI : IsScalarTower K (Localization.Away t) (Localization.AtPrime P) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply K A (Localization.Away t),
        ← IsScalarTower.algebraMap_apply A (Localization.Away t) (Localization.AtPrime P),
        ← IsScalarTower.algebraMap_apply K A (Localization.AtPrime P)]
  haveI := IsLocalization.isLocalization_of_submonoid_le (Localization.Away t) (Localization.AtPrime P)
    (Submonoid.powers t) P.primeCompl hle
  haveI : Algebra.FormallyEtale (Localization.Away t) (Localization.AtPrime P) :=
    Algebra.FormallyEtale.of_isLocalization
      (P.primeCompl.map (algebraMap A (Localization.Away t)))
  haveI := h t ht
  haveI : Nontrivial (Localization.Away t) :=
    (algebraMap (Localization.Away t) (Localization.AtPrime P)).domain_nontrivial
  haveI : Algebra.IsStandardSmooth K (Localization.Away t) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D
  have r := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := K)
    (S := Localization.Away t) D
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (Localization.Away t)
    (Localization.AtPrime P)
  refine ⟨.of_equiv e, .equiv e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_baseChange, Module.finrank, r]
  simp

theorem finitePresentation_of_away (K A : Type) [Field K] [CommRing A] [Algebra K A] (D : ℕ) (s : Set A)
    (hs : Ideal.span s = ⊤)
    (h : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t)) :
    Algebra.FinitePresentation K A := by
  refine RingHom.finitePresentation_algebraMap.1
    (RingHom.finitePresentation_ofLocalizationSpanTarget (algebraMap K A) s hs fun r => ?_)
  haveI := h r.1 r.2
  haveI : Algebra.IsStandardSmooth K (Localization.Away r.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D
  rw [← IsScalarTower.algebraMap_eq K A (Localization.Away r.1)]
  exact (RingHom.finitePresentation_algebraMap).2 inferInstance

theorem finitePresentation_and_kaehler_atPrime :
    ∀ (K : Type) [Field K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K), SmoothOfRelativeDimension D g →
      ∀ (U : Y.affineOpens) (P : Ideal Γ(Y, U.1)) [P.IsPrime],
      letI := secAlgebra g U.1
      Algebra.FinitePresentation K Γ(Y, U.1) ∧
        Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
        Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧
        Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  intro K _ D Y g hg U P _
  letI := secAlgebra g U.1
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) g hg
    ⟨⊤, isAffineOpen_top _⟩ U (fun _ _ => trivial)
  have key : ∀ t ∈ s, Algebra.IsStandardSmoothOfRelativeDimension D K (Localization.Away t) := by
    intro t ht
    have h2 := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := D)).2
      _ (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv (h' t ht)
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    rw [IsScalarTower.algebraMap_eq K Γ(Y, U.1) (Localization.Away t)]
    exact h2
  exact ⟨finitePresentation_of_away K _ D s hs key, kaehler_atPrime_of_away K _ D s hs key P⟩

end GlobalTheory.CompanionTheory.ResKCoords
end
end

