module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.Bundle0071
public import Development.EtaleCohomology.EtaleSheaves.Bundle0069

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveLineChartsOfHenselianFinite
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry HomogeneousLocalization

namespace UpperTheory.Cb.ChartsOfProjectiveLine

section General

variable {σ : Type*} {R : Type} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

private theorem fromSpec_fac {f : R} {m : ℕ} (hf : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj.isAffineOpen_basicOpen 𝒜 f hf hm).fromSpec =
      Spec.map (Proj.awayToSection 𝒜 f) ≫ Proj.awayι 𝒜 f hf hm := by
  have h : (Proj.basicOpenIsoSpec 𝒜 f hf hm).hom =
      (Proj.isAffineOpen_basicOpen 𝒜 f hf hm).isoSpec.hom ≫ Spec.map (Proj.awayToSection 𝒜 f) := by
    rw [IsAffineOpen.isoSpec_hom, Proj.basicOpenIsoSpec_hom]
    rfl
  rw [IsAffineOpen.fromSpec, Iso.inv_comp_eq, Proj.awayι, ← Category.assoc, ← Category.assoc, ← h,
    Iso.hom_inv_id, Category.id_comp]

private theorem basicOpen_section {f g : R} {m e : ℕ} (hf : f ∈ 𝒜 m) (hg : g ∈ 𝒜 e) (hm : 0 < m)
    (he : 0 < e) :
    (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) =
      Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g := by
  have hU := Proj.isAffineOpen_basicOpen 𝒜 f hf hm
  have h1 : hU.fromSpec ⁻¹ᵁ (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) =
      hU.fromSpec ⁻¹ᵁ Proj.basicOpen 𝒜 g := by
    rw [hU.fromSpec_preimage_basicOpen, show hU.fromSpec = _ from fromSpec_fac 𝒜 hf hm,
      Scheme.Hom.comp_preimage, Proj.awayι_preimage_basicOpen 𝒜 hf hm hg he,
      SpecMap_preimage_basicOpen]
  have key := congrArg (fun W => hU.fromSpec ''ᵁ W) h1
  simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, hU.opensRange_fromSpec] at key
  rw [← key]
  exact (inf_eq_right.mpr (Scheme.basicOpen_le _ _)).symm

private theorem res_inf {X : Scheme.{0}} {U V W : X.Opens} (hU : W ≤ U) (hV : W ≤ V) (hW : W = U ⊓ V)
    (x : Γ(X, U)) (y : Γ(X, V))
    (h : X.presheaf.map (homOfLE hU).op x * X.presheaf.map (homOfLE hV).op y = 1) :
    X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op x *
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op y = 1 := by
  subst hW
  exact h

private theorem away_mul_one {f g : R} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) :
    awayMap 𝒜 hg (rfl : f * g = f * g) (Away.isLocalizationElem hf hg) *
      awayMap 𝒜 hf (mul_comm f g : f * g = g * f) (Away.isLocalizationElem hg hf) = 1 := by
  rw [awayMap_mk, awayMap_mk]
  apply val_injective
  rw [val_mul, Away.val_mk, Away.val_mk, val_one, Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

private theorem sections_mul_one {f g : R} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) :
    (Proj 𝒜).presheaf.map (homOfLE (inf_le_left :
        Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f)).op
        (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) *
      (Proj 𝒜).presheaf.map (homOfLE (inf_le_right :
        Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 g)).op
        (Proj.awayToSection 𝒜 g (Away.isLocalizationElem hg hf)) = 1 := by
  have e1 := congrArg (fun φ => φ.hom (Away.isLocalizationElem hf hg))
    (Proj.awayMap_awayToSection 𝒜 hg (rfl : f * g = f * g))
  have e2 := congrArg (fun φ => φ.hom (Away.isLocalizationElem hg hf))
    (Proj.awayMap_awayToSection 𝒜 hf (mul_comm f g : f * g = g * f))
  refine res_inf (Proj.basicOpen_mono 𝒜 _ _ ⟨_, rfl⟩)
    (Proj.basicOpen_mono 𝒜 _ _ ⟨_, mul_comm f g⟩) (Proj.basicOpen_mul 𝒜 f g) _ _ ?_
  have e3 := congrArg (Proj.awayToSection 𝒜 (f * g)) (away_mul_one 𝒜 hf hg)
  rw [map_mul, map_one] at e3
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e1 e2
  refine Eq.trans ?_ e3
  exact congrArg₂ _ e1.symm e2.symm

private theorem section_surjective {f g : R} {m e : ℕ} (hf : f ∈ 𝒜 m) (hg : g ∈ 𝒜 e) (hm : 0 < m)
    (h : Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom (Away 𝒜 f))
      (Away.isLocalizationElem hf hg))) :
    Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(Proj 𝒜, Proj.basicOpen 𝒜 f))
      (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg))) := by
  intro y
  obtain ⟨p, hp⟩ := h ((Proj.basicOpenIsoAway 𝒜 f hf hm).inv y)
  refine ⟨p, ?_⟩
  have hy : Proj.awayToSection 𝒜 f ((Proj.basicOpenIsoAway 𝒜 f hf hm).inv y) = y :=
    (Proj.basicOpenIsoAway 𝒜 f hf hm).inv_hom_id_apply y
  rw [← hy, ← hp]
  simp only [Polynomial.coe_eval₂RingHom]
  have := Polynomial.hom_eval₂ p (Int.castRingHom (Away 𝒜 f)) (Proj.awayToSection 𝒜 f).hom
    (Away.isLocalizationElem hf hg)
  rw [show ((Proj.awayToSection 𝒜 f).hom).comp (Int.castRingHom (Away 𝒜 f)) = Int.castRingHom _ from
    RingHom.ext_int _ _] at this
  exact this.symm

private theorem charts_gen {f g : R} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (hcov : Proj.basicOpen 𝒜 f ⊔ Proj.basicOpen 𝒜 g = ⊤)
    (h1 : Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom (Away 𝒜 f))
      (Away.isLocalizationElem hf hg)))
    (h2 : Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom (Away 𝒜 g))
      (Away.isLocalizationElem hg hf))) :
    ∃ (U V : (Proj 𝒜).Opens) (s : Γ(Proj 𝒜, U)) (s' : Γ(Proj 𝒜, V)), IsAffineOpen U ∧ IsAffineOpen V ∧
      U ⊔ V = ⊤ ∧ (Proj 𝒜).basicOpen s = U ⊓ V ∧ (Proj 𝒜).basicOpen s' = U ⊓ V ∧
      (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s *
        (Proj 𝒜).presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s' = 1 ∧
      Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(Proj 𝒜, U)) s) ∧
      Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(Proj 𝒜, V)) s') :=
  ⟨_, _, Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg),
    Proj.awayToSection 𝒜 g (Away.isLocalizationElem hg hf),
    Proj.isAffineOpen_basicOpen 𝒜 f hf one_pos, Proj.isAffineOpen_basicOpen 𝒜 g hg one_pos, hcov,
    basicOpen_section 𝒜 hf hg one_pos one_pos,
    (basicOpen_section 𝒜 hg hf one_pos one_pos).trans (inf_comm _ _),
    sections_mul_one 𝒜 hf hg, section_surjective 𝒜 hf hg one_pos h1,
    section_surjective 𝒜 hg hf one_pos h2⟩

end General

section Line

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem scale {S : Type} [CommRing S] (φ ψ : MvPolynomial (Fin 2) ℤ →+* S) (c : S)
    (h : ∀ k, ψ (X k) = c * φ (X k)) {n : ℕ} {a : MvPolynomial (Fin 2) ℤ} (ha : a.IsHomogeneous n) :
    ψ a = c ^ n * φ a := by
  have hC : ∀ r : ℤ, ψ (C r) = φ (C r) := fun r => by
    rw [show (C r : MvPolynomial (Fin 2) ℤ) = (r : MvPolynomial (Fin 2) ℤ) from eq_intCast C r,
      map_intCast, map_intCast]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [a.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    by_contra hne
    exact (mem_support_iff.mp hd) (ha.coeff_eq_zero hne)
  rw [monomial_eq, map_mul, map_mul, hC, Finsupp.prod, map_prod, map_prod]
  simp only [map_pow, h, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

private abbrev G : ℕ → Submodule ℤ (MvPolynomial (Fin 2) ℤ) := homogeneousSubmodule (Fin 2) ℤ

private theorem X_mem (i : Fin 2) : (X i : MvPolynomial (Fin 2) ℤ) ∈ G 1 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X ℤ i)

private theorem surj_away {i j : Fin 2} (hij : j ≠ i) :
    Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom (Away G (X i)))
      (Away.isLocalizationElem (X_mem i) (X_mem j))) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective G (X_mem i) z
  have ha' : a.IsHomogeneous n := by
    have := (mem_homogeneousSubmodule _ _).mp ha
    simpa using this
  let q := Polynomial.eval₂RingHom (Int.castRingHom (Away G (X i)))
    (Away.isLocalizationElem (X_mem i) (X_mem j))
  let D : MvPolynomial (Fin 2) ℤ →+* Polynomial ℤ :=
    (aeval (fun k => if k = i then (1 : Polynomial ℤ) else Polynomial.X)).toRingHom
  let ι : Away G (X i) →+* Localization.Away (X i : MvPolynomial (Fin 2) ℤ) := algebraMap _ _
  let α : MvPolynomial (Fin 2) ℤ →+* Localization.Away (X i : MvPolynomial (Fin 2) ℤ) := algebraMap _ _
  have hX : ∀ k, α (X k) = α (X i) * (ι.comp (q.comp D)) (X k) := by
    intro k
    by_cases hk : k = i
    · subst hk
      simp [D]
    · have hkj : k = j := by omega
      subst hkj
      have hD : D (X k) = Polynomial.X := by simp [D, hk]
      have hq : (ι.comp (q.comp D)) (X k) = ι (Away.isLocalizationElem (X_mem i) (X_mem k)) := by
        simp [hD, q]
      have hsp := IsLocalization.mk'_spec' (Localization.Away (X i : MvPolynomial (Fin 2) ℤ))
        (X k ^ 1 : MvPolynomial (Fin 2) ℤ)
        (⟨X i ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers (X i : MvPolynomial (Fin 2) ℤ))
      have hι : ι (Away.isLocalizationElem (X_mem i) (X_mem k)) =
          IsLocalization.mk' (Localization.Away (X i : MvPolynomial (Fin 2) ℤ))
            (X k ^ 1 : MvPolynomial (Fin 2) ℤ)
            (⟨X i ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers (X i : MvPolynomial (Fin 2) ℤ)) := by
        rw [← Localization.mk_eq_mk']
        rfl
      rw [hq, hι, ← pow_one (α (X k)), ← pow_one (α (X i)), ← map_pow, ← map_pow]
      exact hsp.symm
  have hs := scale (ι.comp (q.comp D)) α (α (X i)) hX ha'
  refine ⟨D a, ?_⟩
  apply val_injective
  rw [Away.val_mk, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  change ι (q (D a)) * α (X i ^ n) = α a
  rw [hs, map_pow, mul_comm]
  rfl

private theorem cover : Proj.basicOpen G (X 0) ⊔ Proj.basicOpen G (X 1) = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top' G (X : Fin 2 → MvPolynomial (Fin 2) ℤ)
    (fun i => ⟨1, X_mem i⟩) (by
      rw [eq_top_iff]
      intro p _
      induction p using MvPolynomial.induction_on with
      | C a => exact Subalgebra.algebraMap_mem _ (⟨C a, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ a)⟩ : G 0)
      | add p q hp hq => exact add_mem (hp trivial) (hq trivial)
      | mul_X p i hp => exact mul_mem (hp trivial) (Algebra.subset_adjoin ⟨i, rfl⟩))
  rw [eq_top_iff, ← h]
  refine iSup_le fun i => ?_
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

private theorem intersectionNumber_baseChange : LateralTheory.E.ProjectiveLineCharts₂.ProjectiveLineTwoAffineChartsPolynomialGenerated :=
  charts_gen G (X_mem 0) (X_mem 1) cover (surj_away (by decide)) (surj_away (by decide))

end Line

end UpperTheory.Cb.ChartsOfProjectiveLine

theorem UpperTheory.Cb.projectiveLineCharts_of_henselianFinite :
    LateralTheory.E.LZProperCut.LZHensFinite → LateralTheory.E.ProjectiveLineCharts₂.ProjectiveLineTwoAffineChartsPolynomialGenerated := fun _ =>
  UpperTheory.Cb.ChartsOfProjectiveLine.intersectionNumber_baseChange
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProperGluingExistence
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf
  LateralTheory.E.LeafGlueIsProperPf

namespace UpperTheory.Cb

private lemma ringLift {Q R K : Type} [CommRing Q] [CommRing R] [CommRing K] (j : R →+* K)
    (hj : Function.Injective j) (ψ : Q →+* K) (h : ∀ q, ψ q ∈ j.range) :
    ∃ g : Q →+* R, j.comp g = ψ := by
  let e : R ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b hab => hj (congrArg Subtype.val hab), j.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict j.range h), ?_⟩
  ext q
  change ((e (e.symm (ψ.codRestrict j.range h q)) : j.range) : K) = ψ q
  rw [e.apply_symm_apply]
  rfl

private lemma compat {X : Scheme.{0}} {Ω Q : Type} [Field Ω] [CommRing Q] [Algebra Ω Q]
    (c : X ⟶ Sp Ω) (i : Sp Q ⟶ X)
    (hc : i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap Ω Q)))
    (S : ValuativeCommSq c) (ψ : Q →+* S.K)
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ i = S.i₁)
    (w : CommRingCat.of Ω ⟶ CommRingCat.of S.R) (hw : Spec.map w = S.i₂) :
    ψ.comp (algebraMap Ω Q) = (algebraMap S.R S.K).comp w.hom := by
  have h1 := S.commSq.w
  rw [← hψ, ← hw, Category.assoc, hc, ← Spec.map_comp, ← Spec.map_comp] at h1
  have h2 := Spec.map_injective h1
  ext a
  have h3 := congrArg (fun f => f.hom a) h2
  simpa using h3

private lemma closeSq {X : Scheme.{0}} {Ω Q : Type} [Field Ω] [CommRing Q] [Algebra Ω Q]
    (c : X ⟶ Sp Ω) (i : Sp Q ⟶ X)
    (hc : i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap Ω Q)))
    (S : ValuativeCommSq c) (ψ : Q →+* S.K)
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫ i = S.i₁)
    (hR : ∀ q, ψ q ∈ (algebraMap S.R S.K).range) : S.commSq.HasLift := by
  have hinj : Function.Injective (algebraMap S.R S.K) := IsFractionRing.injective S.R S.K
  obtain ⟨g, hg⟩ := ringLift (algebraMap S.R S.K) hinj ψ hR
  have hw : Spec.map (Spec.preimage S.i₂) = S.i₂ := Spec.map_preimage _
  have hcomp := compat c i hc S ψ hψ (Spec.preimage S.i₂) hw
  have hgψ : CommRingCat.ofHom g ≫ CommRingCat.ofHom (algebraMap S.R S.K) = CommRingCat.ofHom ψ := by
    rw [← CommRingCat.ofHom_comp, hg]
  refine ⟨⟨⟨Spec.map (CommRingCat.ofHom g) ≫ i, ?_, ?_⟩⟩⟩
  · rw [← Category.assoc, ← Spec.map_comp, hgψ, hψ]
  · rw [Category.assoc, hc, ← Spec.map_comp, ← hw]
    congr 1
    ext a
    apply hinj
    have h1 := congrArg (fun f => f a) hcomp
    have h2 := congrArg (fun f => f (algebraMap Ω Q a)) hg
    simp only [RingHom.comp_apply] at h1 h2
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [h2, h1]

private lemma closedCase {Ω P R K : Type} [Field Ω] [CommRing P] [IsDomain P] [Algebra Ω P]
    [Algebra.FiniteType Ω P] (hd : ringKrullDim P = 1) [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (ω : Ω →+* R) (ψ : P →+* K)
    (hω : ψ.comp (algebraMap Ω P) = (algebraMap R K).comp ω)
    (hker : ¬ Function.Injective ψ) (q : P) : ψ q ∈ (algebraMap R K).range := by
  haveI hdim : Ring.KrullDimLE 1 P := by
    rw [Ring.krullDimLE_iff, hd]
    rfl
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hne : RingHom.ker ψ ≠ ⊥ := fun h => hker ((RingHom.injective_iff_ker_eq_bot ψ).mpr h)
  haveI : (RingHom.ker ψ).IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot ‹_› hne
  letI : Field (P ⧸ RingHom.ker ψ) := Ideal.Quotient.field _
  haveI : Module.Finite Ω (P ⧸ RingHom.ker ψ) :=
    finite_of_finite_type_of_isJacobsonRing Ω (P ⧸ RingHom.ker ψ)
  obtain ⟨p, hmon, hp⟩ : IsIntegral Ω (Ideal.Quotient.mk (RingHom.ker ψ) q) :=
    Algebra.IsIntegral.isIntegral _
  have hpq : Polynomial.aeval q p ∈ RingHom.ker ψ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk Ω,
      ← Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk, Polynomial.aeval_def]
    exact hp
  rw [RingHom.mem_ker, Polynomial.aeval_def, Polynomial.hom_eval₂, hω,
    ← Polynomial.eval₂_map] at hpq
  have hi : IsIntegral R (ψ q) := ⟨p.map ω, hmon.map ω, hpq⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  exact ⟨y, hy⟩

private lemma genericVal {Ω L R K : Type} [Field Ω] [Field L] [Algebra Ω L] [CommRing R] [IsDomain R]
    [ValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (ω : Ω →+* R) (f : L →+* K)
    (h : f.comp (algebraMap Ω L) = (algebraMap R K).comp ω) :
    ∃ V : ValuationSubring L, (∀ a : Ω, algebraMap Ω L a ∈ V) ∧
      ∀ x ∈ V, f x ∈ (algebraMap R K).range := by
  let V : ValuationSubring L :=
    { (algebraMap R K).range.comap f with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger R (f x) with hx | hx
        · left
          obtain ⟨y, hy⟩ := hx
          exact ⟨y, hy⟩
        · right
          obtain ⟨y, hy⟩ := hx
          refine ⟨y, ?_⟩
          change algebraMap R K y = f x⁻¹
          rw [map_inv₀]
          exact hy }
  refine ⟨V, fun a => ?_, fun x hx => hx⟩
  refine ⟨ω a, ?_⟩
  have h1 := congrArg (fun g => g a) h
  simp only [RingHom.comp_apply] at h1
  exact h1.symm

private lemma chart {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {X : Scheme.{0}}
    (c : X ⟶ Sp Ω) (P Q : Subalgebra Ω L) (iP : Sp P ⟶ X) (iQ : Sp Q ⟶ X)
    (hP : iP ≫ c = Spec.map (CommRingCat.ofHom (algebraMap Ω P)))
    (hQ : iQ ≫ c = Spec.map (CommRingCat.ofHom (algebraMap Ω Q)))
    [Algebra.FiniteType Ω P] (hd : ringKrullDim P = 1) [IsFractionRing P L]
    (hV : ∀ V : ValuationSubring L, (∀ a : Ω, algebraMap Ω L a ∈ V) →
      (P : Set L) ⊆ V ∨ (Q : Set L) ⊆ V)
    (hag : ∀ (K : Type) [Field K] (f : L →+* K),
      Spec.map (CommRingCat.ofHom (f.comp (algebraMap P L))) ≫ iP =
        Spec.map (CommRingCat.ofHom (f.comp (algebraMap Q L))) ≫ iQ)
    (S : ValuativeCommSq c) (φ : P →+* S.K)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ iP = S.i₁) : S.commSq.HasLift := by
  have hw : Spec.map (Spec.preimage S.i₂) = S.i₂ := Spec.map_preimage _
  have hcomp := compat c iP hP S φ hφ (Spec.preimage S.i₂) hw
  by_cases hinj : Function.Injective φ
  · let f : L →+* S.K := IsFractionRing.lift hinj
    have hf : f.comp (algebraMap P L) = φ :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    have hfΩ : f.comp (algebraMap Ω L) =
        (algebraMap S.R S.K).comp (Spec.preimage S.i₂).hom := by
      rw [IsScalarTower.algebraMap_eq Ω P L, ← RingHom.comp_assoc, hf, hcomp]
    obtain ⟨V, hΩV, hVR⟩ := genericVal (Spec.preimage S.i₂).hom f hfΩ
    rcases hV V hΩV with hPV | hQV
    · refine closeSq c iP hP S φ hφ fun q => ?_
      rw [← hf]
      exact hVR _ (hPV q.2)
    · have hψ : Spec.map (CommRingCat.ofHom (f.comp (algebraMap Q L))) ≫ iQ = S.i₁ := by
        rw [← hag S.K f, hf, hφ]
      exact closeSq c iQ hQ S _ hψ fun q => hVR _ (hQV q.2)
  · exact closeSq c iP hP S φ hφ (closedCase hd (Spec.preimage S.i₂).hom φ hcomp hinj)

end UpperTheory.Cb

open UpperTheory.Cb in
theorem UpperTheory.Cb.properGluing_existence :
    LateralTheory.E.LeafGlueIsProperPf.LeafGlueExistence := by
  intro Ω L _ _ _ A B u h G S
  obtain ⟨-, -, -, hfA, hfB, -, -, hdA, hdB, hFA, hFB, hadj, hV⟩ := h
  haveI := hfA
  haveI := hfB
  haveI := hFA
  haveI := hFB
  haveI := G.hiA
  haveI := G.hiB
  have hagA : ∀ (K : Type) [Field K] (f : L →+* K),
      Spec.map (CommRingCat.ofHom (f.comp (algebraMap A L))) ≫ G.iA =
        Spec.map (CommRingCat.ofHom (f.comp (algebraMap B L))) ≫ G.iB := by
    intro K _ f
    have eA : f.comp (algebraMap A L) = (f.comp (algebraMap (Dr Ω A u) L)).comp
        (Subalgebra.inclusion (le_Dr_A A u)).toRingHom := by
      ext x
      rfl
    have eB : f.comp (algebraMap B L) = (f.comp (algebraMap (Dr Ω A u) L)).comp
        (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom := by
      ext x
      rfl
    rw [eA, eB]
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, G.agree]
  obtain ⟨x0⟩ : Nonempty (Spec (CommRingCat.of S.K)) := inferInstance
  have hx : S.i₁ x0 ∈ Set.range G.iA ∪ Set.range G.iB := by
    rw [G.cover]
    trivial
  rcases hx with hA | hB
  · have hr : Set.range S.i₁ ⊆ Set.range G.iA := by
      rintro _ ⟨y, rfl⟩
      rwa [Subsingleton.elim y x0]
    have hg := IsOpenImmersion.lift_fac G.iA S.i₁ hr
    refine chart G.c0 A B G.iA G.iB G.hcA G.hcB hdA hV hagA S
      (Spec.preimage (IsOpenImmersion.lift G.iA S.i₁ hr)).hom ?_
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, hg]
  · have hr : Set.range S.i₁ ⊆ Set.range G.iB := by
      rintro _ ⟨y, rfl⟩
      rwa [Subsingleton.elim y x0]
    have hg := IsOpenImmersion.lift_fac G.iB S.i₁ hr
    refine chart G.c0 B A G.iB G.iA G.hcB G.hcA hdB (fun V hV' => (hV V hV').symm)
      (fun K _ f => (hagA K f).symm) S
      (Spec.preimage (IsOpenImmersion.lift G.iB S.i₁ hr)).hom ?_
    rw [CommRingCat.ofHom_hom, Spec.map_preimage, hg]
end
end

