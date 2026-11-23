module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0542

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeRootOfUnityEqOneOfGeometricPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.RootUnitGeom

theorem eq_one_of_pow_eq_one_of_isNilpotent {A : Type*} [CommRing A] {v : A} {k : ℕ}
    (hk : IsUnit (k : A)) (hv : v ^ k = 1) (hn : IsNilpotent (v - 1)) : v = 1 := by
  have hw : IsNilpotent (∑ i ∈ Finset.range k, (v ^ i - 1)) := by
    refine isNilpotent_sum fun i _ => ?_
    have : v ^ i - 1 = (∑ j ∈ Finset.range i, v ^ j) * (v - 1) := (geom_sum_mul v i).symm
    rw [this]
    exact mem_nilradical.1 (Ideal.mul_mem_left _ _ (mem_nilradical.2 hn))
  have hs : ∑ i ∈ Finset.range k, v ^ i = (k : A) + ∑ i ∈ Finset.range k, (v ^ i - 1) := by
    simp [Finset.sum_sub_distrib]
  have hu : IsUnit (∑ i ∈ Finset.range k, v ^ i) := by
    rw [hs]
    exact hw.isUnit_add_left_of_commute hk (Commute.all _ _)
  have h0 : (∑ i ∈ Finset.range k, v ^ i) * (v - 1) = 0 := by
    rw [geom_sum_mul, hv, sub_self]
  have : v - 1 = 0 := (hu.mul_right_eq_zero).1 h0
  exact sub_eq_zero.1 this

end GlobalTheory.RootUnitGeom

namespace GlobalTheory.RootUnitGeom

theorem fromSpecResidueField_appTop_comp (S : Scheme.{0}) (x : S) :
    (S.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso _).hom = S.evaluation ⊤ x trivial := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality]
  have e : (homOfLE (le_top : (⊤ : (Spec (S.presheaf.stalk x)).Opens) ≤ ⊤)) = 𝟙 _ := rfl
  rw [e, op_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc]
  rfl

theorem evaluation_eq_one (R : Type) [CommRing R] (S : Scheme.{0}) (s : S ⟶ Sp R)
    (u : Γ(S, ⊤)ˣ)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β →
      Units.map x.appTop.hom.toMonoidHom u = 1) (q : S) :
    S.evaluation ⊤ q trivial (u : Γ(S, ⊤)) = 1 := by
  let K := AlgebraicClosure (S.residueField q)
  let f : S.residueField q ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap (S.residueField q) K)
  let x : Sp K ⟶ S := Spec.map f ≫ S.fromSpecResidueField q
  have hx : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := by
    simp [spMap]
  have h1 := h K x _ hx
  have h2 : x.appTop (u : Γ(S, ⊤)) = 1 := by
    have := congrArg Units.val h1
    simpa using this
  have e : x.appTop ≫ (Scheme.ΓSpecIso _).hom = S.evaluation ⊤ q trivial ≫ f := by
    simp only [x, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
    rw [← Category.assoc, fromSpecResidueField_appTop_comp]
  have h3 := congrArg (fun g => g (u : Γ(S, ⊤))) (congrArg (fun g => (CategoryTheory.ConcreteCategory.hom g : _ → _)) e)
  simp only [CategoryTheory.comp_apply, h2, map_one] at h3
  apply (algebraMap (S.residueField q) K).injective
  rw [map_one]
  exact h3.symm

end GlobalTheory.RootUnitGeom

namespace GlobalTheory.RootUnitGeom

theorem germ_isNilpotent (S : Scheme.{0}) (ε : Γ(S, ⊤)) (hε : S.basicOpen ε = ⊥) (q : S) :
    IsNilpotent (S.presheaf.germ ⊤ q trivial ε) := by
  obtain ⟨U, hU, hqU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens)
    (show q ∈ (⊤ : S.Opens) from trivial)
  have hb : S.basicOpen (S.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ε) = ⊥ := by
    rw [Scheme.basicOpen_res, hε, inf_bot_eq]
  have hn := (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact
    (IsAffineOpen.isCompact hU) _).2 hb
  have := hn.map (S.presheaf.germ U q hqU).hom
  rwa [TopCat.Presheaf.germ_res_apply] at this

end GlobalTheory.RootUnitGeom


open GlobalTheory.RootUnitGeom in
theorem GlobalTheory.rootOfUnity_eq_one_of_geom : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (s : S ⟶ Sp R) (k : ℕ)
    (u : Γ(S, ⊤)ˣ), IsUnit (k : R) → u ^ k = 1 →
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β →
      Units.map x.appTop.hom.toMonoidHom u = 1) → u = 1 := by
  intro R _ S s k u hk hu h
  have hε : S.basicOpen ((u : Γ(S, ⊤)) - 1) = ⊥ := by
    rw [Scheme.basicOpen_eq_bot_iff_forall_evaluation_eq_zero]
    intro x
    rw [map_sub, map_one, evaluation_eq_one R S s u h x.1, sub_self]
  ext1
  apply TopCat.Presheaf.section_ext S.sheaf ⊤
  intro q hq
  let φ : R →+* S.presheaf.stalk q :=
    (S.presheaf.germ ⊤ q trivial).hom.comp (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  have hk' : IsUnit (k : S.presheaf.stalk q) := by
    simpa [map_natCast] using hk.map φ
  have hv : (S.presheaf.germ ⊤ q trivial (u : Γ(S, ⊤))) ^ k = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]
  have hn : IsNilpotent (S.presheaf.germ ⊤ q trivial (u : Γ(S, ⊤)) - 1) := by
    have := germ_isNilpotent S _ hε q
    rwa [map_sub, map_one] at this
  have := eq_one_of_pow_eq_one_of_isNilpotent hk' hv hn
  change S.presheaf.germ ⊤ q trivial (u : Γ(S, ⊤)) = S.presheaf.germ ⊤ q trivial ((1 : Γ(S, ⊤)ˣ) : Γ(S, ⊤))
  rw [this, Units.val_one, map_one]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim
section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

namespace GlobalTheory.FlatFibreRegular

theorem exists_minimal_generators {A : Type} [CommRing A] (𝔭 : Ideal A) [𝔭.IsPrime] (I : Ideal A)
    (hI : I.FG) :
    ∃ S : Finset A, (↑S ⊆ (I : Set A)) ∧ (∀ x ∈ I, ∃ s ∉ 𝔭, s * x ∈ Ideal.span (S : Set A)) ∧
      ∀ c : S → A, ∑ i, c i * (i : A) = 0 → ∀ i, c i ∈ 𝔭 := by
  classical
  let P : Finset A → Prop := fun S =>
    (↑S ⊆ (I : Set A)) ∧ ∀ x ∈ I, ∃ s ∉ 𝔭, s * x ∈ Ideal.span (S : Set A)
  have hex : ∃ n, ∃ S : Finset A, S.card = n ∧ P S := by
    obtain ⟨S, hS⟩ := hI
    refine ⟨S.card, S, rfl, fun a ha => ?_, fun x hx => ⟨1, ?_, ?_⟩⟩
    · rw [← hS]; exact Ideal.subset_span ha
    · exact fun h => (Ideal.IsPrime.ne_top' (I := 𝔭)) ((Ideal.eq_top_iff_one _).2 h)
    · rw [one_mul, hS]; exact hx
  obtain ⟨S, hcard, hSI, hSgen⟩ := Nat.find_spec hex
  refine ⟨S, hSI, hSgen, fun c hc k => ?_⟩
  by_contra hk
  have hlt : (S.erase k).card < Nat.find hex := by
    rw [← hcard]; exact Finset.card_erase_lt_of_mem k.2
  apply Nat.find_min hex hlt
  refine ⟨S.erase k, rfl, fun x hx => hSI (Finset.mem_of_mem_erase hx), fun x hx => ?_⟩
  obtain ⟨s, hs, hsx⟩ := hSgen x hx
  refine ⟨c k * s, fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hk hs), ?_⟩
  have key : Ideal.span (S : Set A) ≤
      Submodule.comap (LinearMap.mulLeft A (c k)) (Ideal.span ((S.erase k : Finset A) : Set A)) := by
    rw [Ideal.span_le]
    intro a ha
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    by_cases hak : a = k
    · rw [hak]
      have h1 := Finset.add_sum_erase Finset.univ (fun i : S => c i * (i : A)) (Finset.mem_univ k)
      rw [hc] at h1
      rw [eq_neg_of_add_eq_zero_left h1]
      refine neg_mem (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      exact Finset.mem_erase.2 ⟨fun h => hik (Subtype.ext h), i.2⟩
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Finset.mem_erase.2 ⟨hak, ha⟩))
  have := key hsx
  simpa [mul_assoc] using this

theorem mem_map_mul_of_mul_mem {A L : Type} [CommRing A] [CommRing L] [Algebra A L] [Module.Flat A L]
    (𝔭 : Ideal A) [𝔭.IsPrime] (hu : ∀ s ∉ 𝔭, IsUnit (algebraMap A L s))
    (g : L) (hg : ∀ y, g * y ∈ 𝔭.map (algebraMap A L) → y ∈ 𝔭.map (algebraMap A L))
    (I : Ideal A) (hI : I.FG) (y : L) (hy : y ∈ I.map (algebraMap A L))
    (hgy : g * y ∈ (I * 𝔭).map (algebraMap A L)) : y ∈ (I * 𝔭).map (algebraMap A L) := by
  classical
  obtain ⟨S, hSI, hSgen, hrel⟩ := exists_minimal_generators 𝔭 I hI
  set J := 𝔭.map (algebraMap A L) with hJdef
  let v : S → L := fun i => algebraMap A L i
  have hspan : I.map (algebraMap A L) ≤ Ideal.span (Set.range v) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨s, hs, hsx⟩ := hSgen x hx
    have h1 : algebraMap A L (s * x) ∈ Ideal.span (Set.range v) := by
      have : Ideal.map (algebraMap A L) (Ideal.span (S : Set A)) ≤ Ideal.span (Set.range v) := by
        rw [Ideal.map_span]
        apply Ideal.span_mono
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
      exact this (Ideal.mem_map_of_mem _ hsx)
    rw [map_mul] at h1
    obtain ⟨t, ht⟩ := (hu s hs).exists_left_inv
    have := Ideal.mul_mem_left _ t h1
    rwa [← mul_assoc, ht, one_mul] at this
  have hvI : ∀ i, v i ∈ I.map (algebraMap A L) := fun i => Ideal.mem_map_of_mem _ (hSI i.2)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 (hspan hy)
  have hgy' : g * y ∈ J • Ideal.span (Set.range v) := by
    have h1 : (I * 𝔭).map (algebraMap A L) ≤ J • Ideal.span (Set.range v) := by
      rw [Ideal.smul_eq_mul, Ideal.map_mul, mul_comm]
      exact Ideal.mul_mono_right hspan
    exact h1 hgy
  obtain ⟨w, hwJ, hw⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum J v _).1 hgy'
  rw [Finsupp.sum_fintype _ _ (by simp)] at hw
  have hrel0 : ∑ i : S, (i : A) • (g * c i - w i) = 0 := by
    have e1 : ∑ i : S, (i : A) • (g * c i) = g * y := by
      rw [← hc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [smul_eq_mul, v]; simp only [Algebra.smul_def]; ring
    have e2 : ∑ i : S, (i : A) • w i = g * y := by
      rw [← hw]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [smul_eq_mul, v]; simp only [Algebra.smul_def]; ring
    simp only [smul_sub, Finset.sum_sub_distrib, e1, e2, sub_self]
  obtain ⟨k, a, z, hx, hf⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A) (M := L)
    (f := fun i : S => (i : A)) (x := fun i => g * c i - w i) hrel0
  have ha : ∀ i j, a i j ∈ 𝔭 := fun i j =>
    hrel (fun i => a i j) (by rw [← hf j]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _) i
  have hcJ : ∀ i, c i ∈ J := by
    intro i
    apply hg
    have h1 : g * c i - w i ∈ J := by
      have hxi := hx i
      dsimp only at hxi
      rw [hxi]
      exact Ideal.sum_mem _ fun j _ => by
        rw [Algebra.smul_def]; exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (ha i j))
    simpa using Ideal.add_mem _ h1 (hwJ i)
  rw [← hc, Ideal.map_mul]
  exact Ideal.sum_mem _ fun i _ => by
    rw [smul_eq_mul, mul_comm (c i)]; exact Ideal.mul_mem_mul (hvI i) (hcJ i)

theorem eq_zero_of_mul_eq_zero {A L : Type} [CommRing A] [IsNoetherianRing A] [CommRing L]
    [IsLocalRing L] [IsNoetherianRing L] [Algebra A L] [Module.Flat A L]
    (𝔭 : Ideal A) [𝔭.IsPrime] (hu : ∀ s ∉ 𝔭, IsUnit (algebraMap A L s))
    (hJ : 𝔭.map (algebraMap A L) ≠ ⊤)
    (g : L) (hg : ∀ y, g * y ∈ 𝔭.map (algebraMap A L) → y ∈ 𝔭.map (algebraMap A L))
    (y : L) (hgy : g * y = 0) : y = 0 := by
  have hn : ∀ n : ℕ, y ∈ (𝔭 ^ n).map (algebraMap A L) := by
    intro n
    induction n with
    | zero => rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; exact Submodule.mem_top
    | succ n ih =>
      rw [pow_succ]
      exact mem_map_mul_of_mul_mem 𝔭 hu g hg (𝔭 ^ n) (IsNoetherian.noetherian _) y ih
        (by rw [hgy]; exact zero_mem _)
  rw [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ hJ, Ideal.mem_iInf]
  intro n
  rw [← Ideal.map_pow]
  exact hn n

theorem isRadical_map_of_smooth {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] (𝔭 : Ideal A) [𝔭.IsPrime] : (𝔭.map (algebraMap A B)).IsRadical := by
  haveI : _root_.IsReduced ((A ⧸ 𝔭) ⊗[A] B) :=
    GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (A ⧸ 𝔭) _
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B 𝔭).toRingEquiv.trans
    (Algebra.TensorProduct.comm A B (A ⧸ 𝔭)).toRingEquiv
  haveI : _root_.IsReduced (B ⧸ 𝔭.map (algebraMap A B)) :=
    isReduced_of_injective e.toRingHom e.injective
  exact (Ideal.isRadical_iff_quotient_reduced _).2 this

theorem mem_of_mul_mem {B : Type} [CommRing B] (u : Ideal B) [u.IsPrime] (I₀ : Ideal B)
    (hrad : I₀.IsRadical) (g : B) (hg : ∀ Q ∈ I₀.minimalPrimes, Q ≤ u → g ∉ Q)
    (y : Localization.AtPrime u)
    (hy : algebraMap B _ g * y ∈ I₀.map (algebraMap B (Localization.AtPrime u))) :
    y ∈ I₀.map (algebraMap B (Localization.AtPrime u)) := by
  set L := Localization.AtPrime u
  set J := I₀.map (algebraMap B L) with hJdef
  have hJrad : J.IsRadical := by
    rintro x ⟨n, hn⟩
    obtain ⟨⟨b, s⟩, hx⟩ := IsLocalization.mk'_surjective u.primeCompl x
    dsimp only at hx
    subst hx
    have h1 : algebraMap B L (b ^ n) ∈ J := by
      have := Ideal.mul_mem_right (algebraMap B L ((s ^ n : u.primeCompl) : B)) J hn
      rwa [← IsLocalization.mk'_pow, IsLocalization.mk'_spec] at this
    obtain ⟨t, ht, htb⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff u.primeCompl L _ _).1 h1
    have h2 : t * b ∈ I₀ := hrad ⟨n + 1, by
      rw [show (t * b) ^ (n + 1) = (t ^ n * b) * (t * b ^ n) by ring]
      exact Ideal.mul_mem_left _ _ htb⟩
    have h3 : algebraMap B L b ∈ J := by
      have h4 := Ideal.mem_map_of_mem (algebraMap B L) h2
      rw [map_mul] at h4
      obtain ⟨t', ht'⟩ := (IsLocalization.map_units L (⟨t, ht⟩ : u.primeCompl)).exists_left_inv
      have := Ideal.mul_mem_left _ t' h4
      rwa [← mul_assoc, ht', one_mul] at this
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ h3
  by_contra hyJ
  rw [← hJrad.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf] at hyJ
  push_neg at hyJ
  obtain ⟨P, hP, hyP⟩ := hyJ
  haveI : P.IsPrime := hP.1.1
  have hgP : algebraMap B L g ∈ P := ((Ideal.IsPrime.mem_or_mem inferInstance (hP.1.2 hy)).resolve_right hyP)
  set Q := P.comap (algebraMap B L)
  have hQu : Q ≤ u := by
    intro x hx
    by_contra hxu
    exact (Ideal.IsPrime.ne_top inferInstance : P ≠ ⊤)
      (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.map_units L (⟨x, hxu⟩ : u.primeCompl)))
  have hQmin : Q ∈ I₀.minimalPrimes := by
    refine ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.1 hP.1.2⟩, fun Q' hQ' hle => ?_⟩
    haveI : Q'.IsPrime := hQ'.1
    have hd : Disjoint (u.primeCompl : Set B) (Q' : Set B) :=
      Set.disjoint_left.2 fun x hxM hxI => hxM (hQu (hle hxI))
    haveI := IsLocalization.isPrime_of_isPrime_disjoint u.primeCompl L Q' hQ'.1 hd
    have hc := IsLocalization.under_map_of_isPrime_disjoint u.primeCompl L hQ'.1 hd
    have hPP : P ≤ Q'.map (algebraMap B L) :=
      hP.2 ⟨inferInstance, Ideal.map_mono hQ'.2⟩ (Ideal.map_le_iff_le_comap.2 hle)
    intro x hx
    rw [← hc]
    exact hPP hx
  exact hg Q hQmin hQu hgP

theorem localization_eq_zero_of_mul_eq_zero : ∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  intro A B _ _ _ _ _ b g u hgb hg
  set 𝔭 := u.asIdeal.comap (algebraMap A B)
  set L := Localization.AtPrime u.asIdeal
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  haveI : Module.Flat A L := Module.Flat.trans A B L
  have hmapeq : 𝔭.map (algebraMap A L) = (𝔭.map (algebraMap A B)).map (algebraMap B L) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hu : ∀ s ∉ 𝔭, IsUnit (algebraMap A L s) := by
    intro s hs
    rw [IsScalarTower.algebraMap_apply A B L]
    exact IsLocalization.map_units L (⟨algebraMap A B s, hs⟩ : u.asIdeal.primeCompl)
  have hJ : 𝔭.map (algebraMap A L) ≠ ⊤ := by
    rw [hmapeq]
    refine ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal L).ne_top ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono (Ideal.map_le_iff_le_comap.2 le_rfl)
  have hg' : ∀ y : L, algebraMap B L g * y ∈ 𝔭.map (algebraMap A L) →
      y ∈ 𝔭.map (algebraMap A L) := by
    intro y hy
    rw [hmapeq] at hy ⊢
    exact mem_of_mul_mem u.asIdeal _ (isRadical_map_of_smooth 𝔭) g hg y hy
  apply eq_zero_of_mul_eq_zero 𝔭 hu hJ (algebraMap B L g) hg'
  rw [← map_mul, hgb, map_zero]

end GlobalTheory.FlatFibreRegular
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstFormalGroupLawNatMultipleEqCoboundarySum
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.NmulSubst

theorem subst_zero_fun {R : Type} [CommRing R] {σ τ : Type} [Finite σ] (g : MvPowerSeries σ R) :
    subst (fun _ : σ => (0 : MvPowerSeries τ R)) g = C (constantCoeff g) := by
  have ha : HasSubst (fun _ : σ => (0 : MvPowerSeries τ R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst ha, finsum_eq_single _ 0]
  · classical
    rw [Finsupp.prod_zero_index, coeff_one, coeff_C, coeff_zero_eq_constantCoeff_apply]
    split_ifs <;> simp
  · intro x hx
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra! hc
      exact hx (Finsupp.ext hc)
    have : (x.prod fun _ n => (0 : MvPowerSeries τ R) ^ n) = 0 :=
      Finset.prod_eq_zero (i := i) (Finsupp.mem_support_iff.2 hi) (zero_pow hi)
    rw [this, map_zero, smul_zero]

theorem nmul_succ {R : Type} [CommRing R] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (k : ℕ) : nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
  unfold nmul
  exact Function.iterate_succ_apply' _ _ _

theorem constantCoeff_nmul {R : Type} [CommRing R] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul]
  | succ k ih =>
    intro i
    rw [nmul_succ]
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · exact constantCoeff_X _
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

end GlobalTheory.QLog.NmulSubst


open GlobalTheory.QLog.NmulSubst in
theorem GlobalTheory.QLog.subst_nmul_eq (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (g : MvPowerSeries (Fin d) R) (n : ℕ) :
    subst (nmul μ n) g = C (constantCoeff g) + (n : R) • g +
      ∑ k ∈ Finset.range n, at2 (cob1 μ g) (nmul μ k) (fun i => X i) := by
  induction n with
  | zero =>
    have : nmul μ 0 = fun _ => 0 := rfl
    rw [this, subst_zero_fun]
    simp
  | succ k ih =>
    have hE : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul μ hμ k j
      · exact constantCoeff_X _
    have hsE := hasSubst_of_constantCoeff_zero hE
    have hμs : HasSubst μ := hasSubst_of_constantCoeff_zero hμ
    have hX : ∀ (f : Fin d → Fin d ⊕ Fin d),
        HasSubst (fun i => (X (f i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
      fun _ => hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    rw [nmul_succ]
    change subst (fun i => subst (Sum.elim (nmul μ k) fun i => X i) (μ i)) g = _
    rw [← subst_comp_subst_apply hμs hsE]
    have hsplit : subst μ g = cob1 μ g + inL g + inR g := by unfold cob1; abel
    have hL : subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (inL g) =
        subst (nmul μ k) g := by
      unfold inL
      rw [subst_comp_subst_apply (hX Sum.inl) hsE]
      congr 1
      funext i
      rw [subst_X hsE]
      rfl
    have hR : subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (inR g) = g := by
      unfold inR
      rw [subst_comp_subst_apply (hX Sum.inr) hsE]
      have : (fun i => subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R))
          (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) = X := by
        funext i
        rw [subst_X hsE]
        rfl
      rw [this, subst_self]
      rfl
    rw [hsplit, subst_add hsE, subst_add hsE, hL, hR, ih, Finset.sum_range_succ]
    change _ = _ + _ + (_ + subst (Sum.elim (nmul μ k) fun i => X i) (cob1 μ g))
    push_cast
    rw [add_smul, one_smul]
    abel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzValueOfFamily
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam

theorem sz_value_of_family (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])
    (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (r : ℝ) (τ₀ : ℍ) (Ω : ℂ)
    (hN : 0 < N) (hact : ActBij act) (hf : IsFam act w f) (hq : ∀ i, QAll (Sz l lam r) N (f i))
    (hj : Sz l lam 0 (jT τ₀)) (hΩ : Ω ^ 12 = DD τ₀) (i : ι) :
    Sz l lam r (f i τ₀ / Ω ^ w) := by
  refine _root_.GlobalTheory.QFam.sz_of_forall_rat_gt l lam r _ fun q hrq => ?_
  obtain ⟨c, hc0, hc, hc'⟩ := _root_.GlobalTheory.QFam.exists_sz_scale l lam q
  obtain ⟨R, hR, hcl⟩ := _root_.GlobalTheory.QFam.exists_szRing l lam
  obtain ⟨hconst, hmono, -, hmul, -⟩ := _root_.GlobalTheory.QFam.QSz.qAll_sz_ring l lam N hN
  have hfam : IsFam act w fun i τ => c * f i τ := (GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act).2.2.1 w c f hf
  have hq' : ∀ i, QAll (· ∈ R) N fun τ => c * f i τ := fun i => by
    obtain ⟨a, ha, ha'⟩ := hmono _ 0 _ (by linarith) (hmul _ _ _ _ (hconst _ c hc) (hq i))
    exact ⟨a, ha, fun n => (hR _).2 (ha' n)⟩
  have hjR : IsIntegral R (jT τ₀) :=
    isIntegral_algebraMap (R := R) (A := ℂ) (x := ⟨jT τ₀, (hR _).2 hj⟩)
  have h0 : Sz l lam 0 (c * f i τ₀ / Ω ^ w) :=
    (hR _).1 (hcl _ (GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow ι act w N _ R τ₀ Ω hN hact hfam hq' hjR hΩ i))
  have h1 := (_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).2.2.1 _ _ _ _ hc' h0
  have e : c⁻¹ * (c * f i τ₀ / Ω ^ w) = f i τ₀ / Ω ^ w := by
    rw [mul_div_assoc, inv_mul_cancel_left₀ hc0]
  rwa [add_zero, e] at h1

end GlobalTheory.QFam
end

