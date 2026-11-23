module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1153
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2031
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2027
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfMonomialQuotientIntegral
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

namespace GlobalTheory.EtRoot

open MvPolynomial

theorem not_X_dvd_X {K : Type} [Field K] {n : ℕ} {i k : Fin n} (hik : i ≠ k) :
    ¬ (X i : MvPolynomial (Fin n) K) ∣ X k := by
  rintro ⟨q, hq⟩
  have := congrArg (MvPolynomial.eval (fun j => if j = i then (0 : K) else 1)) hq
  simp [hik.symm] at this

theorem prod_X_dvd_of_dvd_X_mul {K : Type} [Field K] {n : ℕ} (k : Fin n) :
    ∀ (S : Finset (Fin n)), k ∉ S → ∀ h : MvPolynomial (Fin n) K,
      (∏ j ∈ S, X j) ∣ X k * h → (∏ j ∈ S, X j) ∣ h := by
  intro S
  induction S using Finset.induction_on with
  | empty => intros; simp
  | insert i S hi ih =>
    intro hk h hd
    rw [Finset.prod_insert hi] at hd ⊢
    have hik : i ≠ k := fun e => hk (e ▸ Finset.mem_insert_self _ _)
    have hXi : (X i : MvPolynomial (Fin n) K) ∣ h := by
      rcases (X_prime (R := K) (i := i)).dvd_or_dvd (dvd_trans (dvd_mul_right _ _) hd) with h1 | h1
      · exact absurd h1 (not_X_dvd_X hik)
      · exact h1
    obtain ⟨h', rfl⟩ := hXi
    have hd' : X i * (∏ j ∈ S, X j) ∣ X i * (X k * h') := by
      rw [mul_left_comm (X i) (X k) h']; exact hd
    have h2 := (mul_dvd_mul_iff_left (X_ne_zero (R := K) i)).1 hd'
    exact mul_dvd_mul_left _ (ih (fun h => hk (Finset.mem_insert_of_mem h)) h' h2)

theorem prod_X_dvd_of_dvd_X_pow_mul {K : Type} [Field K] {n : ℕ} (k : Fin n)
    (S : Finset (Fin n)) (hk : k ∉ S) :
    ∀ (e : ℕ) (h : MvPolynomial (Fin n) K), (∏ j ∈ S, X j) ∣ X k ^ e * h → (∏ j ∈ S, X j) ∣ h := by
  intro e
  induction e with
  | zero => intro h hd; simpa using hd
  | succ e ih =>
    intro h hd
    apply ih
    apply prod_X_dvd_of_dvd_X_mul k S hk
    rwa [pow_succ, mul_comm _ (X k), mul_assoc] at hd

theorem prod_X_dvd_of_dvd_pow {K : Type} [Field K] {n : ℕ} :
    ∀ (S : Finset (Fin n)) (f : MvPolynomial (Fin n) K) (m : ℕ),
      (∏ j ∈ S, X j) ∣ f ^ m → (∏ j ∈ S, X j) ∣ f := by
  intro S
  induction S using Finset.induction_on with
  | empty => intros; simp
  | insert k S hk ih =>
    intro f m hd
    rw [Finset.prod_insert hk] at hd ⊢
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [pow_zero] at hd
      exact dvd_trans hd (one_dvd _)
    have hXk : (X k : MvPolynomial (Fin n) K) ∣ f :=
      (X_prime (R := K) (i := k)).dvd_of_dvd_pow (dvd_trans (dvd_mul_right _ _) hd)
    obtain ⟨f', rfl⟩ := hXk
    have h1 : (∏ j ∈ S, X j) ∣ X k ^ m * f' ^ m := by
      rw [← mul_pow]; exact dvd_trans (dvd_mul_left _ _) hd
    exact mul_dvd_mul_left _ (ih f' m (prod_X_dvd_of_dvd_X_pow_mul k S hk m _ h1))

theorem isRadical_span_prod_X {K : Type} [Field K] {n : ℕ} (S : Finset (Fin n)) :
    (Ideal.span {∏ j ∈ S, (X j : MvPolynomial (Fin n) K)}).IsRadical := by
  intro y hy
  obtain ⟨e, he⟩ := (Ideal.mem_radical_iff).1 hy
  rw [Ideal.mem_span_singleton] at he ⊢
  exact prod_X_dvd_of_dvd_pow S y e he

end GlobalTheory.EtRoot

namespace GlobalTheory.EtRoot

open MvPolynomial

theorem dvd_of_dvd_pow_prod_coords (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A]
    [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A)
    (he : (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale) (S : Finset (Fin n))
    (z : A) (k : ℕ) (hz : (∏ j ∈ S, t j) ∣ z ^ k) : (∏ j ∈ S, t j) ∣ z := by
  letI : Algebra (MvPolynomial (Fin n) (ZMod p)) A := (MvPolynomial.aeval t).toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) (ZMod p)) A := he
  have h1 := GlobalTheory.EtaleReducedEq.isRadical_map_of_etale (C := A)
    (Ideal.span {∏ j ∈ S, (X j : MvPolynomial (Fin n) (ZMod p))}) (isRadical_span_prod_X S)
  rw [Ideal.map_span, Set.image_singleton] at h1
  have h2 : algebraMap (MvPolynomial (Fin n) (ZMod p)) A (∏ j ∈ S, X j) = ∏ j ∈ S, t j := by
    rw [RingHom.algebraMap_toAlgebra, map_prod]
    simp
  rw [h2] at h1
  have hmem : z ∈ (Ideal.span {∏ j ∈ S, t j}).radical :=
    (Ideal.mem_radical_iff).2 ⟨k, Ideal.mem_span_singleton.2 hz⟩
  exact Ideal.mem_span_singleton.1 (h1 hmem)

theorem mem_local_of_pow_mem (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A]
    [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A)
    (he : (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale) (P : Ideal A) [P.IsPrime]
    (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (x : L) (m : ℕ) (hm : 0 < m)
    (hx : ∃ a b : A, b ∉ P ∧ x ^ m * algebraMap A L b = algebraMap A L a) :
    ∃ a b : A, b ∉ P ∧ x * algebraMap A L b = algebraMap A L a := by
  let Q := MvPolynomial (Fin n) (ZMod p)
  letI : Algebra Q A := (MvPolynomial.aeval t).toRingHom.toAlgebra
  haveI : Algebra.Etale Q A := he
  let T := Localization.AtPrime P
  haveI : Algebra.FormallyEtale Q T := inferInstance
  haveI : Algebra.EssFiniteType A T := Algebra.EssFiniteType.of_isLocalization T P.primeCompl
  haveI : Algebra.EssFiniteType Q T := Algebra.EssFiniteType.comp Q A T
  haveI : IsIntegrallyClosed Q := isIntegrallyClosed_mvPolynomial_fin (ZMod p) n
  obtain ⟨_, hT⟩ := GlobalTheory.EtNormal.isDomain_and_isIntegrallyClosed_of_formallyEtale Q T
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap A L y) := fun y => by
    have hy : (y : A) ≠ 0 := fun h => y.2 (h ▸ P.zero_mem)
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective A L)).2 hy)
  letI : Algebra T L := (IsLocalization.lift (M := P.primeCompl) (S := T) hunit).toAlgebra
  haveI : IsScalarTower A T L := IsScalarTower.of_algebraMap_eq
    (fun y => (IsLocalization.lift_eq (M := P.primeCompl) (S := T) hunit y).symm)
  haveI : IsFractionRing T L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl T L
  have hmk : ∀ (a : A) (b : P.primeCompl),
      algebraMap T L (IsLocalization.mk' T a b) * algebraMap A L b = algebraMap A L a := by
    intro a b
    rw [IsScalarTower.algebraMap_apply A T L b, ← map_mul, IsLocalization.mk'_spec,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨a, b, hb, hab⟩ := hx
  have hbL : algebraMap A L b ≠ 0 := (hunit ⟨b, hb⟩).ne_zero
  have hxm : x ^ m = algebraMap T L (IsLocalization.mk' T a (⟨b, hb⟩ : P.primeCompl)) := by
    apply mul_right_cancel₀ hbL
    rw [hab]; exact (hmk a ⟨b, hb⟩).symm
  have hint : IsIntegral T x := by
    apply IsIntegral.of_pow hm
    rw [hxm]; exact isIntegral_algebraMap
  obtain ⟨u, hu⟩ := (IsIntegrallyClosed.isIntegral_iff (R := T) (K := L)).1 hint
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl u
  refine ⟨c, s, s.2, ?_⟩
  rw [← hu]; exact hmk c s

theorem div_prod_coords_mem_of_pow : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (P : Ideal A) [P.IsPrime] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (S : Finset (Fin n)) (g : L) (m : ℕ), 0 < m → (∃ a b : A, b ∉ P ∧ g ^ m / algebraMap A L (∏ j ∈ S, t j) * algebraMap A L b = algebraMap A L a) → ∃ a b : A, b ∉ P ∧ g / algebraMap A L (∏ j ∈ S, t j) * algebraMap A L b = algebraMap A L a := by
  intro p _ A _ _ _ n t he P _ L _ _ _ S g m hm ⟨a, b, hb, hab⟩
  have h1P : (1 : A) ∉ P := (Ideal.ne_top_iff_one P).1 (Ideal.IsPrime.ne_top ‹_›)
  by_cases h0 : (∏ j ∈ S, t j) = 0
  · exact ⟨0, 1, h1P, by simp [h0]⟩
  have hπL : algebraMap A L (∏ j ∈ S, t j) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A L)).2 h0
  have h1 : ∃ a' b' : A, b' ∉ P ∧ g ^ m * algebraMap A L b' = algebraMap A L a' :=
    ⟨a * ∏ j ∈ S, t j, b, hb, by
      rw [map_mul, ← hab, div_mul_eq_mul_div, div_mul_cancel₀ _ hπL]⟩
  obtain ⟨x, s, hs, hxs⟩ := mem_local_of_pow_mem p A t he P L g m hm h1
  have hbs : s * b ∉ P := fun h => ((‹P.IsPrime›).mem_or_mem h).elim hs hb
  have h2 : x ^ m * b = a * (∏ j ∈ S, t j) * s ^ m := by
    apply IsFractionRing.injective A L
    simp only [map_mul, map_pow]
    rw [← hxs, ← hab]
    field_simp
    ring
  have h3 : (∏ j ∈ S, t j) ∣ (x * b) ^ m := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    refine ⟨a * s ^ (k + 1) * b ^ k, ?_⟩
    calc (x * b) ^ (k + 1) = (x ^ (k + 1) * b) * b ^ k := by ring
      _ = _ := by rw [h2]; ring
  obtain ⟨y, hy⟩ := dvd_of_dvd_pow_prod_coords p A t he S (x * b) m h3
  refine ⟨y, s * b, hbs, ?_⟩
  have h4 : algebraMap A L (x * b) = algebraMap A L (∏ j ∈ S, t j) * algebraMap A L y := by
    rw [hy, map_mul]
  rw [map_mul, ← hxs] at h4
  rw [map_mul, div_mul_eq_mul_div, div_eq_iff hπL]
  linear_combination h4

end GlobalTheory.EtRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameLineBundleFamilyDescendsFlatSurjectiveQuasiC
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem isPullback_prod_map {S : Scheme.{0}} (A : Over S) {V V' : Over S} (v : V ⟶ V') :
    IsPullback (lift (fst A V) (snd A V ≫ v)).left (snd A V).left (snd A V').left v.left := by
  have hT : IsPullback (fst A V).left (snd A V).left A.hom V.hom := IsPullback.of_hasPullback _ _
  have hY : IsPullback (fst A V').left (snd A V').left A.hom V'.hom := IsPullback.of_hasPullback _ _
  have m₁ : (lift (fst A V) (snd A V ≫ v)).left ≫ (fst A V').left = (fst A V).left := by
    rw [← Over.comp_left, lift_fst]
  have m₂ : (lift (fst A V) (snd A V ≫ v)).left ≫ (snd A V').left = (snd A V).left ≫ v.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hT' : IsPullback ((lift (fst A V) (snd A V ≫ v)).left ≫ (fst A V').left) (snd A V).left A.hom
      (v.left ≫ V'.hom) := by
    rw [m₁, Over.w v]; exact hT
  exact IsPullback.of_right hT' m₂ hY

theorem isPullback_prod_kernel {S : Scheme.{0}} (A Y Y' W : Over S) (c : Y' ⟶ Y) (w₁ w₂ : W ⟶ Y')
    (hK : IsPullback w₁.left w₂.left c.left c.left) :
    IsPullback (lift (fst A W) (snd A W ≫ w₁)).left (lift (fst A W) (snd A W ≫ w₂)).left
      (lift (fst A Y') (snd A Y' ≫ c)).left (lift (fst A Y') (snd A Y' ≫ c)).left := by
  have Hc := isPullback_prod_map A c
  have H₂ := isPullback_prod_map A w₂
  have outer := H₂.flip.paste_horiz hK
  have e₁ : (lift (fst A W) (snd A W ≫ w₁)).left ≫ (snd A Y').left = (snd A W).left ≫ w₁.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have e₂ : (lift (fst A Y') (snd A Y' ≫ c)).left ≫ (snd A Y).left = (snd A Y').left ≫ c.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hw : w₁ ≫ c = w₂ ≫ c := Over.OverMorphism.ext hK.w
  refine IsPullback.of_right (h₁₂ := (snd A Y').left) (h₂₂ := (snd A Y).left) ?_ ?_ Hc.flip
  · rw [e₁, e₂]; exact outer
  · rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, lift_fst, lift_fst, lift_snd_assoc,
      lift_snd_assoc, Category.assoc, Category.assoc, hw]

theorem same_of_fpqc : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (T U Y Y' : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left), Fam A N → Fam A M → ∀ (y : Y ⟶ T) (u : Y ⟶ U) (c : Y' ⟶ Y), Flat c.left → Surjective c.left → QuasiCompact c.left → Same A N M (c ≫ y) (c ≫ u) → Same A N M y u := by
  intro S A _ hA T U Y Y' N M hN hM y u c hfl hsu hqc hc
  rw [same_iff hN.isLB hM.isLB, ← sub_eq_zero]
  obtain ⟨L, hL, hcl⟩ := cls_surj (evc hN.isLB (fst A Y) (snd A Y ≫ y) - evc hM.isLB (fst A Y) (snd A Y ≫ u))
  rw [← hcl]
  have key : ∀ {X : Scheme.{0}} (f : X ⟶ (A ⊗ Y).left), Triv (L.pull f) ↔
      CechPic.pull f (evc hN.isLB (fst A Y) (snd A Y ≫ y)) = CechPic.pull f (evc hM.isLB (fst A Y) (snd A Y ≫ u)) := by
    intro X f
    rw [← sub_eq_zero, ← map_sub, ← hcl, ← cls_pull hL f (pull_isLB hL f)]
    exact (cls_eq_zero_iff (pull_isLB hL f)).symm
  refine (cls_eq_zero_iff hL).2 ?_
  let F : A ⊗ Y' ⟶ A ⊗ Y := lift (fst A Y') (snd A Y' ≫ c)
  let e : Y ⟶ A ⊗ Y := lift 1 (𝟙 Y)
  let e' : Y' ⟶ A ⊗ Y' := lift 1 (𝟙 Y')
  have h0 : Triv (L.pull e.left) := by
    rw [key]
    simp only [e, pull_evc, lift_fst, lift_snd_assoc, Category.id_comp]
    rw [hN.add.evc_one hN.isLB, hM.add.evc_one hM.isLB]
  have h1 : Triv (L.pull F.left) := by
    rw [key]
    simp only [F, pull_evc, lift_fst, lift_snd_assoc]
    rw [same_iff hN.isLB hM.isLB] at hc
    simpa only [Category.assoc] using hc
  have hEF : e' ≫ F = c ≫ e := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [e, e', F]
  have hep : e' ≫ snd A Y' = 𝟙 Y' := lift_snd _ _

  have hT : IsPullback (fst A Y').left (snd A Y').left A.hom Y'.hom := IsPullback.of_hasPullback _ _
  have hY : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := IsPullback.of_hasPullback _ _
  have m₁ : F.left ≫ (fst A Y).left = (fst A Y').left := by rw [← Over.comp_left, lift_fst]
  have m₂ : F.left ≫ (snd A Y).left = (snd A Y').left ≫ c.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hT' : IsPullback (F.left ≫ (fst A Y).left) (snd A Y').left A.hom (c.left ≫ Y.hom) := by
    rw [m₁, Over.w c]; exact hT
  have H : IsPullback F.left (snd A Y').left (snd A Y).left c.left := IsPullback.of_right hT' m₂ hY
  have hF₁ : Flat F.left := MorphismProperty.of_isPullback H.flip hfl
  have hF₂ : Surjective F.left := MorphismProperty.of_isPullback H.flip hsu
  have hF₃ : QuasiCompact F.left := MorphismProperty.of_isPullback H.flip hqc

  let W : Over S := Over.mk (pullback.fst c.left c.left ≫ Y'.hom)
  let w₁ : W ⟶ Y' := Over.homMk (pullback.fst c.left c.left) rfl
  let w₂ : W ⟶ Y' := Over.homMk (pullback.snd c.left c.left) (by
    show pullback.snd c.left c.left ≫ Y'.hom = pullback.fst c.left c.left ≫ Y'.hom
    rw [← Over.w c, ← Category.assoc, ← pullback.condition, Category.assoc])
  have hw : w₁ ≫ c = w₂ ≫ c := Over.OverMorphism.ext pullback.condition
  have hK : IsPullback w₁.left w₂.left c.left c.left := IsPullback.of_hasPullback c.left c.left
  let g₁ : A ⊗ W ⟶ A ⊗ Y' := lift (fst A W) (snd A W ≫ w₁)
  let g₂ : A ⊗ W ⟶ A ⊗ Y' := lift (fst A W) (snd A W ≫ w₂)
  have hKP : IsPullback g₁.left g₂.left F.left F.left := isPullback_prod_kernel A Y Y' W c w₁ w₂ hK
  have hg : g₁.left ≫ F.left = g₂.left ≫ F.left := hKP.w

  obtain ⟨g, hgg⟩ := h0
  obtain ⟨t, ht⟩ := h1
  have n₁ : (snd A Y' ≫ e').left ≫ F.left = (snd A Y' ≫ c).left ≫ e.left := by
    rw [← Over.comp_left, ← Over.comp_left, Category.assoc, hEF, Category.assoc]
  obtain ⟨t', ht', hv⟩ := exists_gen hL (K' := PUnit) (φ' := fun _ => F.left) (ε' := fun _ => 1)
    (fun U _ k => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, n₁]
      simp)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (snd A Y' ≫ e').left)))
      (LB.pullGen L _ _ g (snd A Y' ≫ c).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.pullGen_isGen _ _ _ _ hgg _))
  have norm : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y'.left) (z : Z) (J), Geo.Tor.Good L z J →
      val t' (r ≫ e'.left) z J = val g (r ≫ c.left) z J := by
    intro Z r z J hJ
    have a₁ : (r ≫ e'.left) ≫ (snd A Y' ≫ e').left = r ≫ e'.left := by
      rw [Category.assoc, ← Over.comp_left, ← Category.assoc e', hep, Category.id_comp]
    have a₂ : (r ≫ e'.left) ≫ (snd A Y' ≫ c).left = r ≫ c.left := by
      rw [Category.assoc, ← Over.comp_left, ← Category.assoc e', hep, Category.id_comp]
    rw [hv Z _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, a₁, a₂, mul_inv_cancel,
      _root_.one_mul]
  refine _root_.GlobalTheory.FlatDescent.triv_of_gen_descent L hL F.left hF₁ hF₂ hF₃ g₁.left g₂.left hKP t' ht' (fun z J hJ => ?_)
  let o : W ⟶ A ⊗ W := lift 1 (𝟙 W)
  have hg1 : o.left ≫ g₁.left = w₁.left ≫ e'.left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [o, g₁, e']
  have hg2 : o.left ≫ g₂.left = w₂.left ≫ e'.left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [o, g₂, e']
  have ho : o.left ≫ (snd A W).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
  have hwc : w₁.left ≫ c.left = w₂.left ≫ c.left := by rw [← Over.comp_left, ← Over.comp_left, hw]
  have key2 := gen_unique' hL (φ := fun _ : PUnit => g₁.left ≫ F.left) (ε := fun _ => (1 : ℤ))
    (φ' := fun _ : PUnit => g₂.left ≫ F.left) (ε' := fun _ => 1)
    (fun U _ k => by simp only [hg]) (snd A W).left o.left ho (surj_snd GlobalTheory.SemiRigid.globalFns hA W)
    (u := LB.pullGen L _ _ t' g₁.left) (u' := LB.pullGen L _ _ t' g₂.left)
    (DVR.pullGen_isGen _ _ _ _ ht' _) (DVR.pullGen_isGen _ _ _ _ ht' _)
    (fun y I hI => by rw [val_pull hI, val_pull hI, hg1, hg2, norm _ _ _ _ hI, norm _ _ _ _ hI, hwc])
    _ (𝟙 _) z J hJ
  rwa [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at key2

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarQuotientStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.NormCover

theorem isIso_ι_of_eq_top {Z : Scheme.{0}} (V : Z.Opens) (hV : V = ⊤) : IsIso V.ι := by
  rw [← Z.isoOfEq_hom_ι hV, ← Z.topIso_hom]
  infer_instance

theorem isUnit_of_basicOpen_eq_top {Z : Scheme.{0}} (a : Γ(Z, ⊤)) (h : Z.basicOpen a = ⊤) : IsUnit a :=
  Z.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => (Z.mem_basicOpen _ x hx).1 (h.ge hx)

theorem preimage_eq_top {X Y₀ : Scheme.{0}} (U : X.Opens) (g : Y₀ ⟶ U) : (g ≫ U.ι) ⁻¹ᵁ U = ⊤ := by
  refine top_unique fun x _ => ?_
  change (g ≫ U.ι) x ∈ U
  rw [Scheme.Hom.comp_apply]
  exact (g x).2

theorem exists_normalization_of_etale {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X Y₀ : Scheme.{0}} (π : X ⟶ Sp R) [Smooth π] (U : X.Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (g : Y₀ ⟶ U) [IsFinite g] [Etale g] (hchar : ∀ y : Y₀, CharZero (Y₀.residueField y)) :
    ∃ (Y : Scheme.{0}) (s : Y ⟶ X) (i : Y₀ ⟶ Y), IsOpenImmersion i ∧ IsDominant i ∧ i ≫ s = g ≫ U.ι ∧
      IsFinite s ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧ Flat (s ≫ π) ∧
      IsLocallyNoetherian Y ∧
      ∀ (S : Scheme.{0}) (f : S ⟶ Y), Set.range (f ≫ s) ⊆ U → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f := by
  let s₀ := g ≫ U.ι
  haveI : QuasiCompact s₀ := inferInstance
  haveI : QuasiSeparated s₀ := inferInstance
  haveI : Smooth (s₀ ≫ π) := inferInstance
  haveI : GlobalTheory.IsNormalScheme Y₀ := GlobalTheory.isNormalScheme_of_smooth (s₀ ≫ π)
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : IsLocallyNoetherian Y₀ := LocallyOfFiniteType.isLocallyNoetherian (s₀ ≫ π)
  haveI : IsReduced Y₀ := inferInstance
  haveI hfin : IsFinite s₀.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_locallyOfFiniteType (o := CommRingCat.of R) s₀ π fun y _ => hchar y
  haveI : GlobalTheory.IsNormalScheme s₀.normalization := GlobalTheory.IsNormalScheme.normalization s₀
  have htop₀ : s₀ ⁻¹ᵁ U = ⊤ := preimage_eq_top U g
  haveI : IsIntegralHom (s₀ ∣_ U) := by
    haveI := isIso_ι_of_eq_top _ htop₀
    have e : s₀ ∣_ U = (s₀ ⁻¹ᵁ U).ι ≫ g := by
      rw [← cancel_mono U.ι, morphismRestrict_ι, Category.assoc]
    rw [e]
    infer_instance
  let W := s₀.fromNormalization ⁻¹ᵁ U
  haveI hiso : IsIso (s₀.toNormalization ∣_ W) := GlobalTheory.isIso_toNormalization_morphismRestrict s₀ U
  have htop : s₀.toNormalization ⁻¹ᵁ W = ⊤ := by
    refine top_unique fun x _ => ?_
    change s₀.fromNormalization (s₀.toNormalization x) ∈ U
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact (g x).2
  haveI := isIso_ι_of_eq_top _ htop
  have hi : s₀.toNormalization = inv (s₀.toNormalization ⁻¹ᵁ W).ι ≫ (s₀.toNormalization ∣_ W) ≫ W.ι := by
    rw [morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  haveI : Flat (s₀.toNormalization ≫ s₀.fromNormalization ≫ π) := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
    infer_instance
  refine ⟨s₀.normalization, s₀.fromNormalization, s₀.toNormalization, ?_, inferInstance,
    Scheme.Hom.toNormalization_fromNormalization s₀, hfin,
    fun y => ((GlobalTheory.isNormalScheme_iff _).mp inferInstance y).2,
    GlobalTheory.flat_normalization s₀ (s₀.fromNormalization ≫ π),
    LocallyOfFiniteType.isLocallyNoetherian s₀.fromNormalization, ?_⟩
  · rw [hi]
    infer_instance
  · intro S f hf
    have hr : Set.range f ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hf ⟨x, rfl⟩
    refine ⟨IsOpenImmersion.lift W.ι f hr ≫ inv (s₀.toNormalization ∣_ W) ≫ (s₀.toNormalization ⁻¹ᵁ W).ι, ?_⟩
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]

end GlobalTheory.UPel.HT.ES.NormCover

namespace GlobalTheory.UPel.HT.ES.NormCover

theorem exists_finite_normal_model : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (M : Model b N) (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ M.X) (g : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), IsFinite g → Etale g → g ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → ∃ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i ∧ IsDominant i ∧ i ≫ s = s₀ ∧ IsFinite s ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧ Flat (s ≫ M.s) ∧ IsLocallyNoetherian Y ∧ (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) := by
  intro p _ D R _ _ _ _ b N _ M Y₀ s₀ g hgf hge hs
  subst hs
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  have hp : IsUnit ((p : ℕ) : Γ(Y₀, ⊤)) := by
    apply isUnit_of_basicOpen_eq_top
    have h := preimage_eq_top (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) g
    rw [Scheme.Hom.preimage_basicOpen, map_natCast] at h
    exact h
  have hcop : ∀ m : ℕ, m.Coprime p → IsUnit ((m : ℕ) : Γ(Y₀, ⊤)) := by
    intro m hm
    have := (b.unit m hm).map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (g ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι ≫ M.s).appTop).hom
    rwa [map_natCast] at this
  have hunit : ∀ n : ℕ, n ≠ 0 → IsUnit ((n : ℕ) : Γ(Y₀, ⊤)) := by
    intro n hn
    obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
    push_cast
    exact (hp.pow a).mul (hcop m ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm).symm)
  have hchar : ∀ y : Y₀, CharZero (Y₀.residueField y) := by
    intro y
    refine charZero_of_inj_zero fun n hn => ?_
    by_contra h
    have := (hunit n h).map (Y₀.Γevaluation y).hom
    rw [map_natCast, hn] at this
    exact not_isUnit_zero this
  obtain ⟨Y, s, i, h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_normalization_of_etale M.s _ g hchar
  refine ⟨Y, s, i, h1, h2, h3, h4, h5, h6, h7, fun S f hpS => h8 S f ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ (f ≫ s) ⁻¹ᵁ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) := by
    rw [Scheme.Hom.preimage_basicOpen, map_natCast]
    have hpS' : IsUnit ((p : ℕ) : Γ(S, (f ≫ s) ⁻¹ᵁ ⊤)) := hpS
    exact (Scheme.basicOpen_of_isUnit S hpS').ge trivial
  exact hx

end GlobalTheory.UPel.HT.ES.NormCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAtFirstOrderOfTangentsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_value_eq_at_first_order_of_tangents : ∀ (K C : Type) [Field K] [Field C] [Algebra K C] (P : PolAV (Sp K))
    (ρ : LB.Gen (P.L.pull (eSec P.A))) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))))
    (i₀ : P.L.ι), ⊤ ≤ (spMap (algebraMap K C) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ →
    ∀ (v w : epsR K ⟶ P.A), IsTangent v → IsTangent w →
    ∀ (yv yw : Sp (DualNumber C) ⟶ (Over.mk (spMap (algebraMap K C)) ⊗ P.A).left),
      yv ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yv ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ v.left →
      yw ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yw ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ w.left →
    ∀ (a b a' b' : C),
      valR yv ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b) →
      valR yw ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a' + TrivSqZeroExt.inr b') → a = a' := by
  intro K C hK hC hKC P ρ k t i₀ hi v w hv hw yv yw hv1 hv2 hw1 hw2 a b a' b' ev ew
  exact @GlobalTheory.TangentFirstOrder.fst_eq_of_tangent K C hK hC hKC P ρ k t i₀ hi v w hv hw yv yw hv1 hv2 hw1 hw2 a b a' b' ev ew
end

