module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0002
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatible
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EtaleOverIntegersLocalization
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.CommAlg.OrderEtale

theorem formallyUnramified_fractionRing (k K : Type) [CommRing k] [IsDomain k] [CharZero k]
    [Module.Finite ℤ k] [Field K] [Algebra k K] [IsFractionRing k K] [Algebra ℤ K] :
    Algebra.FormallyUnramified ℤ K := by
  have hinj : Function.Injective (algebraMap k K) := IsFractionRing.injective k K
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  haveI := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℚ) (A := K) (RingHom.ext_int _ _)
  haveI := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := k) (A := K) (RingHom.ext_int _ _)
  haveI : Algebra.IsIntegral ℤ k := Algebra.IsIntegral.of_finite ℤ k
  have hint : ∀ a : k, IsIntegral ℚ (algebraMap k K a) := fun a =>
    IsIntegral.tower_top (A := ℚ)
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).algebraMap (B := K))
  haveI : Algebra.IsAlgebraic ℚ K := by
    constructor
    intro x
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := k) x
    rw [div_eq_mul_inv]
    have hb : IsIntegral ℚ (algebraMap k K b)⁻¹ :=
      (IsAlgebraic.inv_iff.mpr (hint b).isAlgebraic).isIntegral
    exact ((hint a).mul hb).isAlgebraic
  haveI : Algebra.FormallyUnramified ℚ K := Algebra.FormallyUnramified.of_isSeparable ℚ K
  haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
  exact Algebra.FormallyUnramified.comp ℤ ℚ K

theorem isUnramifiedAt_bot (k : Type) [CommRing k] [IsDomain k] [CharZero k]
    [Module.Finite ℤ k] : Algebra.IsUnramifiedAt ℤ (⊥ : Ideal k) := by
  have hM : (⊥ : Ideal k).primeCompl = nonZeroDivisors k := by
    ext x
    simp [Ideal.mem_primeCompl_iff, mem_nonZeroDivisors_iff_ne_zero]
  haveI : IsFractionRing k (Localization.AtPrime (⊥ : Ideal k)) := by
    unfold IsFractionRing
    rw [← hM]
    infer_instance
  letI : Field (Localization.AtPrime (⊥ : Ideal k)) := IsFractionRing.toField k
  exact formallyUnramified_fractionRing k (Localization.AtPrime (⊥ : Ideal k))

theorem exists_etale_away (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] :
    ∃ N : ℕ, N ≠ 0 ∧ (Int.castRingHom (Localization.Away (N : k))).Etale := by
  have hU : IsOpen (Algebra.unramifiedLocus ℤ k) := Algebra.isOpen_unramifiedLocus
  have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) ∈ Algebra.unramifiedLocus ℤ k :=
    isUnramifiedAt_bot k
  obtain ⟨V, ⟨f, rfl⟩, hfV, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hbot hU
  have hf0 : f ≠ 0 := by
    intro h
    simp [h] at hfV
  have hint : Algebra.IsIntegral ℤ k := Algebra.IsIntegral.of_finite ℤ k
  have hne : Ideal.comap (algebraMap ℤ k) (Ideal.span {f}) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.subset_span rfl) (Algebra.IsIntegral.isIntegral f)
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, eq_intCast] at hm
  have hmN : (m : k) ∣ ((m.natAbs : ℤ) : k) := map_dvd (Int.castRingHom k) (Int.dvd_natAbs.mpr dvd_rfl)
  have hfN : f ∣ ((m.natAbs : ℕ) : k) := by
    have := hm.trans hmN
    simpa using this
  obtain ⟨g, hg⟩ := hfN
  refine ⟨m.natAbs, Int.natAbs_ne_zero.mpr hm0, ?_⟩
  have hS : Algebra.FormallyUnramified ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := by
    rw [← Algebra.basicOpen_subset_unramifiedLocus_iff]
    refine subset_trans ?_ hVU
    rw [hg]
    exact PrimeSpectrum.basicOpen_mul_le_left f g
  have hfree : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'
  have hflat : Module.Flat ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := by
    have := IsLocalization.flat (Localization.Away ((m.natAbs : ℕ) : k))
      (Submonoid.powers ((m.natAbs : ℕ) : k))
    exact Module.Flat.trans ℤ k _
  have hfp : Algebra.FinitePresentation ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := by
    have : Algebra.FinitePresentation ℤ k := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    have := IsLocalization.Away.finitePresentation (S := Localization.Away ((m.natAbs : ℕ) : k))
      ((m.natAbs : ℕ) : k)
    exact Algebra.FinitePresentation.trans ℤ k _
  have hE : Algebra.Etale ℤ (Localization.Away ((m.natAbs : ℕ) : k)) :=
    Algebra.Etale.of_formallyUnramified_of_flat
  have h2 : Int.castRingHom (Localization.Away ((m.natAbs : ℕ) : k)) =
      algebraMap ℤ (Localization.Away ((m.natAbs : ℕ) : k)) := RingHom.ext_int _ _
  rw [h2, RingHom.etale_algebraMap]
  exact hE

end GlobalTheory.CompanionTheory.CommAlg.OrderEtale
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EtalePolynomialBaseChangeIff
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.EtaleCoord

theorem etale_of_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S)
    (g : S →+* T) (hf : f.Etale) (h : (g.comp f).Etale) : g.Etale := by
  algebraize [f, g, g.comp f]
  exact Algebra.Etale.of_restrictScalars R S T

theorem etale_eval₂Hom_iff_int : ∀ (k A : Type) [CommRing k] [CommRing A] (N : ℕ), (Int.castRingHom (Localization.Away (N : k))).Etale → ∀ (φ : k →+* A), IsUnit (N : A) → ∀ (D : ℕ) (x : Fin D → A), (MvPolynomial.eval₂Hom φ x).Etale ↔ (MvPolynomial.eval₂Hom (Int.castRingHom A) x).Etale := by
  intro k A _ _ N hN φ hu D x
  let ι : k →+* Localization.Away (N : k) := algebraMap k _
  have hφN : IsUnit (φ (N : k)) := by simpa using hu
  let ψ : Localization.Away (N : k) →+* A := IsLocalization.Away.lift (N : k) hφN
  have hψ : ψ.comp ι = φ := by
    ext a
    simp [ψ, ι]
  have hι : ι.Etale := by
    rw [RingHom.etale_algebraMap]
    exact Algebra.Etale.of_isLocalizationAway (N : k)
  have ha : (MvPolynomial.map (σ := Fin D) ι).Etale := etale_mvPolynomial_map_of_etale ι hι
  have hb : (MvPolynomial.map (σ := Fin D) (Int.castRingHom (Localization.Away (N : k)))).Etale :=
    etale_mvPolynomial_map_of_etale _ hN
  let Θ := MvPolynomial.eval₂Hom ψ x
  have e1 : MvPolynomial.eval₂Hom φ x = Θ.comp (MvPolynomial.map ι) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Θ, ← hψ]
    · intro j
      simp [Θ]
  have e2 : MvPolynomial.eval₂Hom (Int.castRingHom A) x =
      Θ.comp (MvPolynomial.map (Int.castRingHom (Localization.Away (N : k)))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Θ]
    · intro j
      simp [Θ]
  rw [e1, e2]
  exact ⟨fun h => RingHom.Etale.stableUnderComposition _ _ hb (etale_of_comp _ _ ha h),
    fun h => RingHom.Etale.stableUnderComposition _ _ ha (etale_of_comp _ _ hb h)⟩

end GlobalTheory.CompanionTheory.Ar.EtaleCoord
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GenericPointOpenImmersion
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.ValGeneric

theorem exists_pow_mem_of_ne_zero (R : Type) [CommRing R] [IsDomain R] [ValuationRing R]
    [Ring.DimensionLEOne R] :
    ∃ π : R, π ≠ 0 ∧ ∀ b : R, b ≠ 0 → ∃ (n : ℕ) (c : R), π ^ n = b * c := by
  by_cases hm : IsLocalRing.maximalIdeal R = ⊥
  · refine ⟨1, one_ne_zero, fun b hb => ?_⟩
    have hu : IsUnit b := by
      by_contra h
      have hbm : b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal b).2 h
      rw [hm] at hbm
      exact hb (by simpa using hbm)
    obtain ⟨u, rfl⟩ := hu
    exact ⟨0, ((u⁻¹ : Rˣ) : R), by simp⟩
  · obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
    refine ⟨π, hπ0, fun b hb => ?_⟩
    by_cases hu : IsUnit b
    · obtain ⟨u, rfl⟩ := hu
      exact ⟨0, ((u⁻¹ : Rˣ) : R), by simp⟩
    have hrad : π ∈ (Ideal.span {b}).radical := by
      rw [Ideal.radical_eq_sInf]
      refine Ideal.mem_sInf.2 ?_
      rintro J ⟨hbJ, hJ⟩
      have hbJ' : b ∈ J := hbJ (Ideal.mem_span_singleton_self b)
      have hJ0 : J ≠ ⊥ := fun h => hb (by simpa [h] using hbJ')
      have hmax := Ring.DimensionLEOne.maximalOfPrime hJ0 hJ
      rw [IsLocalRing.eq_maximalIdeal hmax]
      exact hπ
    obtain ⟨n, hn⟩ := hrad
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    exact ⟨n, c, by rw [← hc, mul_comm]⟩

theorem isOpenImmersion_spMap_fraction :
    ∀ (C : Type) [Field C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C], IsOpenImmersion (spMap (algebraMap R C)) := by
  intro C _ R _ _ _ _ _ _
  obtain ⟨π, hπ0, h⟩ := exists_pow_mem_of_ne_zero R
  have inj := IsFractionRing.injective R C
  haveI : IsLocalization.Away π C := by
    refine IsLocalization.Away.mk π ?_ ?_ ?_
    · exact ((map_ne_zero_iff _ inj).2 hπ0).isUnit
    · intro s
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) s
      obtain ⟨n, c, hc⟩ := h b (nonZeroDivisors.ne_zero hb)
      refine ⟨n, a * c, ?_⟩
      have hb' : algebraMap R C b ≠ 0 :=
        (map_ne_zero_iff _ inj).2 (nonZeroDivisors.ne_zero hb)
      rw [← map_pow, hc, map_mul, map_mul]
      field_simp
    · intro a b hab
      exact ⟨0, by rw [inj hab]⟩
  exact IsOpenImmersion.of_isLocalization π

end GlobalTheory.CompanionTheory.ValGeneric
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HenselianAlgClosedResidue
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.CommAlg.Hens

open Polynomial IsLocalRing

theorem exists_isRoot_of_monic {C : Type} [Field C] [IsAlgClosed C] {R : Type} [CommRing R]
    [IsDomain R] [ValuationRing R] [Algebra R C] [IsFractionRing R C]
    {f : R[X]} (hf : f.Monic) (hd : 0 < f.natDegree) : ∃ r : R, f.IsRoot r := by
  have hinj : Function.Injective (algebraMap R C) := IsFractionRing.injective R C
  have hdeg : (f.map (algebraMap R C)).degree ≠ 0 := by
    rw [hf.degree_map]
    exact (natDegree_pos_iff_degree_pos.mp hd).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (f.map (algebraMap R C)) hdeg
  have hxa : aeval x f = 0 := by
    rw [aeval_def, ← Polynomial.eval_map]
    exact hx
  have hint : IsIntegral R x := ⟨f, hf, by rw [← aeval_def]; exact hxa⟩
  obtain ⟨r, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨r, hinj ?_⟩
  have hr0 : algebraMap R C (f.eval r) = aeval (algebraMap R C r) f :=
    (aeval_algebraMap_apply_eq_algebraMap_eval r f).symm
  rw [hr0, hxa, map_zero]

theorem exists_root_near {C : Type} [Field C] [IsAlgClosed C] {R : Type} [CommRing R]
    [IsDomain R] [ValuationRing R] [Algebra R C] [IsFractionRing R C] (n : ℕ) :
    ∀ (f : R[X]), f.Monic → f.natDegree = n → ∀ a₀ : R, f.eval a₀ ∈ maximalIdeal R →
      ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R := by
  induction n with
  | zero =>
    intro f hf hn a₀ h
    have : f = 1 := hf.natDegree_eq_zero.mp hn
    subst this
    rw [eval_one] at h
    exact absurd h (Ideal.ne_top_iff_one _ |>.mp (maximalIdeal.isMaximal R).ne_top)
  | succ n ih =>
    intro f hf hn a₀ h
    obtain ⟨r, hr⟩ := exists_isRoot_of_monic (C := C) hf (by omega)
    have hfac : (X - Polynomial.C r) * (f /ₘ (X - Polynomial.C r)) = f :=
      mul_divByMonic_eq_iff_isRoot.mpr hr
    have hgm : (f /ₘ (X - Polynomial.C r)).Monic := (monic_X_sub_C r).of_mul_monic_left (hfac.symm ▸ hf)
    have hgd : (f /ₘ (X - Polynomial.C r)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C, hn]; rfl
    rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at h
    rcases (maximalIdeal.isMaximal R).isPrime.mem_or_mem h with h1 | h1
    · refine ⟨r, hr, ?_⟩
      have := (maximalIdeal R).neg_mem h1
      simpa using this
    · obtain ⟨a, ha, ham⟩ := ih _ hgm hgd a₀ h1
      refine ⟨a, ?_, ham⟩
      rw [IsRoot.def, ← hfac, eval_mul, ha.eq_zero, mul_zero]

theorem henselian_and_residueField_isAlgClosed : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra R C] [IsFractionRing R C],
    HenselianLocalRing R ∧ IsAlgClosed (IsLocalRing.ResidueField R) := by
  intro C _ _ R _ _ _ _ _
  refine ⟨⟨fun f hf a₀ h _ => exists_root_near (C := C) _ f hf rfl a₀ h⟩, ?_⟩
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hlift : p ∈ lifts (residue R) :=
    (lifts_iff_coeff_lifts p).mpr fun n => residue_surjective (p.coeff n)
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift hp
  have hpos : 0 < q.natDegree := by
    rw [hqd]; exact hirr.natDegree_pos
  obtain ⟨r, hr⟩ := exists_isRoot_of_monic (C := C) hqm hpos
  refine ⟨residue R r, ?_⟩
  rw [← hq, eval_map_apply, hr.eq_zero, map_zero]

end GlobalTheory.CompanionTheory.CommAlg.Hens
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardGenericFibreInjective
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.CompanionTheory.ValFibre

theorem isUnit_of_basicOpen_eq_top' {Y : Scheme.{0}} (a : Γ(Y, ⊤)) (h : Y.basicOpen a = ⊤) :
    IsUnit a := by
  have key : ∀ (g : Opposite.op (⊤ : Y.Opens) ⟶ Opposite.op (Y.basicOpen a))
      (g' : Opposite.op (Y.basicOpen a) ⟶ Opposite.op ⊤),
      (Y.presheaf.map g').hom ((Y.presheaf.map g).hom a) = a := by
    intro g g'
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, Subsingleton.elim (g ≫ g') (𝟙 _),
      CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  have u := (Y.toRingedSpace.isUnit_res_basicOpen a).map
    (Y.presheaf.map (homOfLE (le_of_eq h.symm)).op).hom
  convert u using 1
  exact (key _ _).symm

theorem point_cases (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    (r : Sp R) : r.asIdeal = ⊥ ∨ r = IsLocalRing.closedPoint R := by
  by_cases h : r.asIdeal = ⊥
  · exact .inl h
  · refine .inr (PrimeSpectrum.ext ?_)
    have := Ring.DimensionLEOne.maximalOfPrime h r.isPrime
    exact IsLocalRing.eq_maximalIdeal this

theorem exists_factor (R C : Type) [CommRing R] [IsDomain R] [Field C] [Algebra R C] [IsFractionRing R C]
    {Y : Scheme.{0}} (f : Y ⟶ Sp R) (hf : ∀ y : Y, (f y).asIdeal = ⊥) :
    ∃ g : Y ⟶ Sp C, g ≫ spMap (algebraMap R C) = f := by
  let ψ : R →+* Γ(Y, ⊤) := (f.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hu : ∀ r : nonZeroDivisors R, IsUnit (ψ r) := by
    intro r
    refine isUnit_of_basicOpen_eq_top' _ (top_unique fun y _ => ?_)
    show y ∈ Y.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r.1))
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    show r.1 ∉ (f y).asIdeal
    rw [hf y]
    exact nonZeroDivisors.ne_zero r.2
  let φ : C →+* Γ(Y, ⊤) := IsLocalization.lift (M := nonZeroDivisors R) hu
  have hφ : φ.comp (algebraMap R C) = ψ := IsLocalization.lift_comp hu
  refine ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_⟩
  have e : (Sp R).toSpecΓ = Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [← Scheme.isoSpec_hom, Scheme.isoSpec_Spec_hom]
  have h1 : CommRingCat.ofHom (algebraMap R C) ≫ CommRingCat.ofHom φ =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop := by
    rw [← CommRingCat.ofHom_comp, hφ]
    rfl
  rw [Category.assoc, spMap, ← Spec.map_comp, h1, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc, e, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.comp_id]

theorem geometricallyIntegral_open {X S : Scheme.{0}} (p : X ⟶ S) [GeometricallyIntegral p] (Y : X.Opens)
    (hY : ∀ s : S, ∃ y : X, y ∈ Y ∧ p y = s) : GeometricallyIntegral (Y.ι ≫ p) := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  let g : Z ⟶ pullback p y := pullback.lift (fst ≫ Y.ι) snd (by simpa using h.w)
  have hg : IsPullback fst g Y.ι (pullback.fst p y) :=
    IsPullback.of_bot (by simpa [g] using h) (by simp [g]) (IsPullback.of_hasPullback p y)
  have : IsOpenImmersion g := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hg inferInstance
  have : IsIntegral (pullback p y) :=
    GeometricallyIntegral.geometrically_isIntegral y _ _ (IsPullback.of_hasPullback p y)
  have : Nonempty Z := by
    obtain ⟨x, hx, hxs⟩ := hY (y (IsLocalRing.closedPoint K))
    obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Y.ι ≫ p) (g := y) (⟨x, hx⟩ : Y) (IsLocalRing.closedPoint K) (by simpa using hxs)
    exact ⟨h.isoPullback.inv z⟩
  exact isIntegral_of_isOpenImmersion g

theorem eq_zero_of_pull_generic_eq_zero : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ Y : A.left.Opens, IsCompact (Y : Set A.left) →
    ∀ q : Pic Y.toScheme, pull (pullback.fst A.hom (spMap (algebraMap R C)) ∣_ Y) q = 0 → q = 0 := by
  intro C _ _ R _ _ _ _ _ _ A _ hA Y hY q hq
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hGI : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have hsq : IsPullback (pullback.fst A.hom (spMap (algebraMap R C)) ∣_ Y)
      ((pullback.fst A.hom (spMap (algebraMap R C)) ⁻¹ᵁ Y).ι ≫ pullback.snd A.hom (spMap (algebraMap R C)))
      (Y.ι ≫ A.hom) (spMap (algebraMap R C)) :=
    IsPullback.paste_vert (isPullback_morphismRestrict _ _) (IsPullback.of_hasPullback _ _)
  by_cases hc : ∃ x : A.left, x ∈ Y ∧ A.hom x = IsLocalRing.closedPoint R
  · obtain ⟨x, hxY, hx⟩ := hc
    have hgen : ∀ r : Sp R, ∃ y : A.left, y ∈ Y ∧ A.hom y = r := by
      intro r
      have hs : r ⤳ A.hom x := by
        rw [hx]
        exact IsLocalRing.specializes_closedPoint r
      obtain ⟨y, hy, hyr⟩ := (Flat.generalizingMap A.hom) hs
      exact ⟨y, hy.mem_open Y.isOpen hxY, hyr⟩
    have : GeometricallyIntegral (Y.ι ≫ A.hom) := geometricallyIntegral_open _ _ hgen
    have : CompactSpace Y.toScheme := isCompact_iff_compactSpace.1 hY
    have : QuasiCompact (Y.ι ≫ A.hom) := (quasiCompact_iff_compactSpace _).2 inferInstance
    obtain ⟨M, hM, rfl⟩ := cls_surj q
    refine (cls_eq_zero_iff hM).2 ?_
    refine GlobalTheory.ValGenExtend.triv_of_triv_generic R C _ _ (Y.ι ≫ A.hom) _ _ hsq inferInstance inferInstance
      inferInstance M hM ?_
    exact (cls_eq_zero_iff (pull_isLB hM _)).1 hq
  · have hall : ∀ y : Y.toScheme, ((Y.ι ≫ A.hom) y).asIdeal = ⊥ := by
      intro y
      refine (point_cases R _).resolve_right fun h => hc ⟨y.1, y.2, ?_⟩
      simpa using h
    obtain ⟨g, hg⟩ := exists_factor R C (Y.ι ≫ A.hom) hall
    have e := hsq.lift_fst (𝟙 _) g (by simpa using hg.symm)
    have := pull_comp (hsq.lift (𝟙 _) g (by simpa using hg.symm))
      (pullback.fst A.hom (spMap (algebraMap R C)) ∣_ Y) q
    rw [e, pull_id, hq, map_zero] at this
    exact this

end GlobalTheory.CompanionTheory.ValFibre
end
end

