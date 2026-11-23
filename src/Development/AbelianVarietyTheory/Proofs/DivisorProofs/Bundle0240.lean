module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0204
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0207
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericResidueLinearIndependence
section
namespace GlobalTheory

open IsLocalRing

theorem derivation_mem_of_mem_sq {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
    (δ : Derivation k A A) (q : Ideal A) {x : A} (hx : x ∈ q ^ 2) : δ x ∈ q := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm n hn
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact q.add_mem (q.mul_mem_right _ hm) (q.mul_mem_right _ hn)
  · intro x y hx hy
    rw [map_add (f := _)]; exact q.add_mem hx hy

theorem residue_algebraMap_eq_zero_iff_mem {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] (q : Ideal A) [q.IsPrime] [IsLocalization.AtPrime R q] (x : A) :
    residue R (algebraMap A R x) = 0 ↔ x ∈ q := by
  rw [residue_eq_zero_iff]
  conv_rhs => rw [← IsLocalization.AtPrime.under_maximalIdeal R q]
  rfl

theorem cotangent_relation_derivation {k A R : Type} [CommRing k] [CommRing A] [Algebra k A]
    (q : Ideal A) [q.IsPrime] [CommRing R] [IsLocalRing R] [Algebra A R]
    [IsLocalization.AtPrime R q]
    (δ : Derivation k A A) {κ : Type} (J : Finset κ) (g : κ → A)
    (hg : ∀ j, algebraMap A R (g j) ∈ maximalIdeal R) (c : κ → ResidueField R)
    (hrel : ∑ j ∈ J, c j • (maximalIdeal R).toCotangent ⟨_, hg j⟩ = 0) :
    ∑ j ∈ J, c j * residue R (algebraMap A R (δ (g j))) = 0 := by
  set ψ : A →+* ResidueField R := (residue R).comp (algebraMap A R) with hψdef
  have hψ : ∀ x, ψ x = 0 ↔ x ∈ q := fun x => residue_algebraMap_eq_zero_iff_mem q x
  have hgq : ∀ j, g j ∈ q := fun j => (hψ _).1 ((residue_eq_zero_iff _).2 (hg j))
  set r : κ → R := fun j => (residue_surjective (c j)).choose with hr
  have hrc : ∀ j, residue R (r j) = c j := fun j => (residue_surjective (c j)).choose_spec
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples q.primeCompl J r
  have hb' : ∀ i ∈ J, ∃ x : A, algebraMap A R x = (b : A) • r i := fun i hi => hb i hi
  choose! a ha using hb'
  have hb0 : ψ b ≠ 0 := fun h => b.2 ((hψ _).1 h)
  have hψa : ∀ j ∈ J, ψ (a j) = ψ b * c j := by
    intro j hj
    simp only [hψdef, RingHom.comp_apply, ha j hj, Algebra.smul_def, map_mul, hrc]
  set y : A := ∑ j ∈ J, a j * g j with hy
  have hyq : y ∈ q := q.sum_mem fun j _ => q.mul_mem_left _ (hgq j)

  have hT : (maximalIdeal R).toCotangent
      (∑ j ∈ J, algebraMap A R (a j) • (⟨_, hg j⟩ : maximalIdeal R)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have : ∀ j ∈ J, (maximalIdeal R).toCotangent (algebraMap A R (a j) • (⟨_, hg j⟩ : maximalIdeal R))
        = ψ b • (c j • (maximalIdeal R).toCotangent ⟨_, hg j⟩) := by
      intro j hj
      rw [map_smul, smul_smul, ← hψa j hj]
      exact (algebraMap_smul (ResidueField R) (algebraMap A R (a j)) _).symm
    rw [Finset.sum_congr rfl this, ← Finset.smul_sum, hrel, smul_zero]
  rw [Ideal.toCotangent_eq_zero] at hT
  have hcoe : ((∑ j ∈ J, algebraMap A R (a j) • (⟨_, hg j⟩ : maximalIdeal R) : maximalIdeal R) : R)
      = algebraMap A R y := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hy, Submodule.coe_sum, map_sum, map_mul, Algebra.smul_def]
  rw [hcoe, ← IsLocalization.AtPrime.map_eq_maximalIdeal q R, ← Ideal.map_pow,
    IsLocalization.mem_map_algebraMap_iff q.primeCompl R] at hT
  obtain ⟨⟨x, s⟩, hxs⟩ := hT
  rw [← map_mul, IsLocalization.eq_iff_exists q.primeCompl R] at hxs
  obtain ⟨t, ht⟩ := hxs
  have hz : (t : A) * (y * s) ∈ q ^ 2 := ht ▸ Ideal.mul_mem_left _ _ x.2
  have hδz := (hψ _).2 (derivation_mem_of_mem_sq δ q hz)
  have hs0 : ψ s ≠ 0 := fun h => s.2 ((hψ _).1 h)
  have ht0 : ψ t ≠ 0 := fun h => t.2 ((hψ _).1 h)
  have hy0 : ψ y = 0 := (hψ _).2 hyq
  have hδy : ψ (δ y) = 0 := by
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, hy0] at hδz
    simpa [hs0, ht0] using hδz
  have hg0 : ∀ j, ψ (g j) = 0 := fun j => (hψ _).2 (hgq j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hy, map_sum, map_sum] at hδy
  simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, hg0, zero_mul, add_zero] at hδy
  rw [Finset.sum_congr rfl (fun j hj => by rw [hψa j hj, mul_assoc]), ← Finset.mul_sum] at hδy
  exact (mul_eq_zero.1 hδy).resolve_left hb0

end GlobalTheory

namespace GlobalTheory
open IsLocalRing

theorem bertini_cotangent_independent : ∀ (k A : Type) [Field k] [CharZero k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ), ∃ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 ∧ ∀ u : Fin M × ι → k, MvPolynomial.eval u Q ≠ 0 → ∀ (q : Ideal A) [q.IsPrime] (R : Type) [CommRing R] [IsLocalRing R] [Algebra A R] [IsLocalization.AtPrime R q], (∃ p, f p ∉ q) → LinearIndependent (IsLocalRing.ResidueField R) (fun j : {j : Fin M // algebraMap A R (∑ p, u (j, p) • f p) ∈ IsLocalRing.maximalIdeal R} => ((IsLocalRing.maximalIdeal R).toCotangent ⟨_, j.2⟩ : IsLocalRing.CotangentSpace R)) := by
  intro k A _ _ _ _ _ ι _ f M
  obtain ⟨n, δ, ω, hD⟩ := _root_.GlobalTheory.bertini_derivation_split k A
  have hC := fun (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι) (h : i₀ ∈ J) =>
    _root_.GlobalTheory.BertiniC.no_dependence_of_general k A n δ ω hD f M J i₀ p₀ h
  classical
  let Qf : Finset (Fin M) × Fin M × ι → MvPolynomial (Fin M × ι) k := fun x =>
    if h : x.2.1 ∈ x.1 then (hC x.1 x.2.1 x.2.2 h).choose else 1
  refine ⟨∏ x, Qf x, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro x _
    simp only [Qf]
    split_ifs with h
    · exact (hC _ _ _ h).choose_spec.1
    · exact one_ne_zero
  · intro u hu q _ R _ _ _ _ hp
    obtain ⟨p₀, hp₀⟩ := hp
    rw [map_prod, Finset.prod_ne_zero_iff] at hu
    rw [linearIndependent_iff']
    intro s w hw i₀ hi₀
    by_contra hne
    let ψ : A →+* ResidueField R := (residue R).comp (algebraMap A R)
    letI : Algebra k (ResidueField R) := (ψ.comp (algebraMap k A)).toAlgebra
    let φ : A →ₐ[k] ResidueField R := { ψ with commutes' := fun _ => rfl }
    let J : Finset (Fin M) := s.map (Function.Embedding.subtype _)
    let c : Fin M → ResidueField R := fun j =>
      if h : algebraMap A R (∑ p, u (j, p) • f p) ∈ maximalIdeal R then w ⟨j, h⟩ / w i₀ else 0
    have hJ : i₀.1 ∈ J := Finset.mem_map_of_mem _ hi₀
    have hx := hu (J, i₀.1, p₀) (Finset.mem_univ _)
    simp only [Qf, dif_pos hJ] at hx
    refine (hC J i₀.1 p₀ hJ).choose_spec.2 u hx (ResidueField R) φ c ?_ ?_ ?_ ?_
    · exact fun h => hp₀ ((residue_algebraMap_eq_zero_iff_mem q _).1 h)
    · show c i₀.1 = 1
      rw [show c i₀.1 = w i₀ / w i₀ from dif_pos i₀.2]
      exact div_self hne
    · intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hi
      exact (residue_eq_zero_iff _).2 j.2
    · intro l
      have hrel : ∑ j ∈ s, (w j / w i₀) •
          (maximalIdeal R).toCotangent ⟨_, j.2⟩ = 0 := by
        simp_rw [div_eq_mul_inv, mul_comm _ (w i₀)⁻¹, mul_smul]
        rw [← Finset.smul_sum, hw, smul_zero]
      have key := cotangent_relation_derivation q (δ l) s
        (fun j => ∑ p, u (j.1, p) • f p) (fun j => j.2) (fun j => w j / w i₀) hrel
      rw [Finset.sum_map]
      convert key using 2 with j hj
      show c j.1 * φ _ = _
      rw [show c j.1 = w j / w i₀ from dif_pos j.2]
      rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLFieldAutomorphismStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_fieldAutomorphism : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F ≃+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (x : GL (Fin n) F), hc a b α β n (gal (t : F →+* F) n x) = hc a b (fun y => α (gal (t : F →+* F) a y)) (fun y => β (gal (t : F →+* F) b y)) n x := by
  first | (exact @GlobalTheory.Shin.HcGal.hc_gal) | (exact GlobalTheory.Shin.HcGal.hc_gal) | (intros; apply GlobalTheory.Shin.HcGal.hc_gal  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLOneLeftRightUnitStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_one_left_right_unit : ∀ (F : Type) [Field F] [Finite F], ∀ (a : ℕ) (α : GL (Fin a) F → ℂ), IsCl α → hc 0 a (fun _ => 1) α a = α ∧ hc a 0 α (fun _ => 1) a = α := by
  first | (exact @GlobalTheory.Shin.HcUnit.main) | (exact GlobalTheory.Shin.HcUnit.main) | (intros; apply GlobalTheory.Shin.HcUnit.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFderivAtSchwartzOperatorFirstStatement
section
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.has_fderiv_at_schwartz_operator_first : ∀ {V W V' E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V'] [NormedAddCommGroup E] [NormedSpace ℂ E] (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (y : W) (x' : V'), HasFDerivAt (opFst T f) ((fderiv ℝ (T (sliceCLM x' f)) y).comp (ContinuousLinearMap.fst ℝ W V') + (dSndCLM T f (y, x')).comp (ContinuousLinearMap.snd ℝ W V')) (y, x') := by
  first | exact @GlobalTheory.SchwartzFstOp.hasFDerivAt_opFst | exact GlobalTheory.SchwartzFstOp.hasFDerivAt_opFst | (intros; apply GlobalTheory.SchwartzFstOp.hasFDerivAt_opFst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictlySemistableChartAtOfSmooth
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.SmChart

open MvPolynomial

noncomputable def subst {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (i : Fin (n + 1)) : MvPolynomial (Fin n) O :=
  Fin.cases (C ϖ) (fun j => X j) i

theorem prod_lt_one {O : Type} [CommRing O] (n : ℕ) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1), (X i : MvPolynomial (Fin (n + 1)) O)) = X 0 := by
  have : Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1) = {0} := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; exact Fin.ext (by simpa using h)
    · rintro rfl; simp
  rw [this, Finset.prod_singleton]

noncomputable abbrev gen {O : Type} [CommRing O] (ϖ : O) (n : ℕ) : Ideal (MvPolynomial (Fin (n + 1)) O) :=
  Ideal.span {X 0 - C ϖ}

theorem subst_vanish {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    ∀ a ∈ gen ϖ n, (aeval (subst ϖ n)).toRingHom a = 0 := by
  intro a ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  simp [subst, algebraMap_eq]

noncomputable def quotMap {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (MvPolynomial (Fin (n + 1)) O ⧸ gen ϖ n) →+* MvPolynomial (Fin n) O :=
  Ideal.Quotient.lift _ (aeval (subst ϖ n)).toRingHom (subst_vanish ϖ n)

noncomputable def quotInv {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    MvPolynomial (Fin n) O →+* (MvPolynomial (Fin (n + 1)) O ⧸ gen ϖ n) :=
  (Ideal.Quotient.mk _).comp (rename Fin.succ).toRingHom

theorem quotMap_mk {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (a : MvPolynomial (Fin (n + 1)) O) :
    quotMap ϖ n (Ideal.Quotient.mk _ a) = aeval (subst ϖ n) a := rfl

theorem quotMap_quotInv {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (quotMap ϖ n).comp (quotInv ϖ n) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [quotInv, quotMap_mk]
  · intro i
    simp [quotInv, quotMap_mk, subst]

theorem quotInv_quotMap {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (quotInv ϖ n).comp (quotMap ϖ n) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [quotInv, quotMap_mk]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [RingHom.comp_apply, quotMap_mk, aeval_X, subst, Fin.cases_zero, RingHom.id_apply]
      simp only [quotInv, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, rename_C]
      rw [Ideal.Quotient.eq]
      rw [← neg_sub]; exact neg_mem (Ideal.subset_span rfl)
    · simp [quotInv, quotMap_mk, subst]

theorem quotMap_bijective {O : Type} [CommRing O] (ϖ : O) (n : ℕ) : Function.Bijective (quotMap ϖ n) :=
  ⟨Function.LeftInverse.injective (g := quotInv ϖ n) (fun a => congr($(quotInv_quotMap ϖ n) a)),
    Function.RightInverse.surjective (g := quotInv ϖ n) (fun a => congr($(quotMap_quotInv ϖ n) a))⟩

theorem quotMap_algebraMap {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    (quotMap ϖ n).comp (algebraMap O _) = C := by
  refine RingHom.ext fun c => ?_
  change quotMap ϖ n (Ideal.Quotient.mk _ (C c)) = C c
  rw [quotMap_mk, aeval_C, algebraMap_eq]

end GlobalTheory.SmChart


open GlobalTheory.SmChart in
theorem GlobalTheory.SSG.chartAt_of_smooth : ∀ (O : Type) [CommRing O] (ϖ : O) (X : Scheme.{0})
    (p : X ⟶ Spec (CommRingCat.of O)) (V : X.Opens) (x : X), x ∈ V → Smooth (V.ι ≫ p) →
    GlobalTheory.SSG.ChartAt ϖ p x := by
  intro O _ ϖ X p V x hx hsm
  set f := V.ι ≫ p with hf
  let x' : V.toScheme := ⟨x, hx⟩
  obtain ⟨W, hW, hxW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp V.toScheme.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top x')
  have hW : IsAffineOpen W := hW
  have e : W ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hφ : (f.appLE ⊤ W e).hom.Smooth := f.smooth_appLE (isAffineOpen_top _) hW e
  rw [RingHom.smooth_iff_locally_isStandardSmooth,
    RingHom.locally_iff_isLocalization RingHom.isStandardSmooth_respectsIso] at hφ
  obtain ⟨s, hs, hfs⟩ := hφ
  have hs' := iSup_basicOpen_of_span_eq_top W (s : Set Γ(V.toScheme, W)) hs
  have hmem : x' ∈ (⨆ i ∈ (s : Set Γ(V.toScheme, W)), V.toScheme.basicOpen i) := hs'.symm ▸ hxW
  obtain ⟨r, hr, hxr⟩ : ∃ r ∈ s, x' ∈ V.toScheme.basicOpen r := by simpa using hmem
  have hW' : IsAffineOpen (V.toScheme.basicOpen r) := hW.basicOpen r
  have e' : V.toScheme.basicOpen r ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  haveI : IsLocalization.Away r Γ(V.toScheme, V.toScheme.basicOpen r) := hW.isLocalization_basicOpen r
  have hst : (f.appLE ⊤ _ e').hom.IsStandardSmooth := by
    rw [← f.appLE_map e (homOfLE (V.toScheme.basicOpen_le r)).op]
    exact hfs r hr _
  obtain ⟨n, g, hgC, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hst
  let c : O →+* Γ(Spec (CommRingCat.of O), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hc : Function.Bijective c := (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv.bijective
  let k := V.ι.appIso (V.toScheme.basicOpen r)
  have hk : Function.Bijective k.inv.hom := k.symm.commRingCatIsoToRingEquiv.bijective
  have hU : IsAffineOpen (V.ι ''ᵁ V.toScheme.basicOpen r) := hW'.image_of_isOpenImmersion V.ι
  have hxU : x ∈ V.ι ''ᵁ V.toScheme.basicOpen r := ⟨x', hxr, rfl⟩
  have hcomp : p.appLE ⊤ (V.ι ''ᵁ V.toScheme.basicOpen r) le_top ≫ k.hom = f.appLE ⊤ _ e' := by
    have h1 := Scheme.Hom.appLE_comp_appLE V.ι p ⊤ (V.ι ''ᵁ V.toScheme.basicOpen r) (V.toScheme.basicOpen r)
      le_top (V.ι.preimage_image_eq _).ge
    have h2 : k.hom = V.ι.appLE _ _ (V.ι.preimage_image_eq _).ge := by
      rw [Scheme.Hom.appIso_hom, Scheme.Hom.appLE]; rfl
    rw [h2]; exact h1
  refine ⟨_, hU, hxU, n + 1, 1, le_rfl, by omega, ?_⟩
  rw [prod_lt_one]
  refine ⟨k.inv.hom.comp (g.comp ((MvPolynomial.map c).comp (quotMap ϖ n))), ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.stableUnderComposition _ _
        (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective (quotMap_bijective ϖ n))
          (RingHom.Etale.of_bijective ⟨MvPolynomial.map_injective _ hc.1, MvPolynomial.map_surjective _ hc.2⟩))
        hg) (RingHom.Etale.of_bijective hk)
  · refine RingHom.ext fun a => ?_
    change k.inv.hom (g (MvPolynomial.map c (quotMap ϖ n (algebraMap O _ a)))) =
      (p.appLE ⊤ (V.ι ''ᵁ V.toScheme.basicOpen r) le_top).hom (c a)
    rw [show quotMap ϖ n (algebraMap O _ a) = MvPolynomial.C a from congr($(quotMap_algebraMap ϖ n) a),
      MvPolynomial.map_C, show g (MvPolynomial.C (c a)) = (f.appLE ⊤ _ e').hom (c a) from congr($hgC (c a)),
      ← hcomp]
    simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinFourierTermMoveUnit
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwoUnit

theorem phi_smul (σ : ℂ) {l : ℝ} (hl : l ≠ 0) (w : ℂ) :
    phi σ ((l : ℂ) * w) = ((l : ℂ)⁻¹ ^ 2 * ((|l| : ℝ) : ℂ) ^ (-2 * σ)) * phi σ w := by
  unfold phi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (abs_nonneg l) (norm_nonneg w), mul_inv, mul_pow]
  ring

theorem abs_mul_inv_sq {l : ℝ} (hl : l ≠ 0) :
    ((|l| : ℝ) : ℂ) * (l : ℂ)⁻¹ ^ 2 = ((|l| : ℝ) : ℂ)⁻¹ := by
  have h1 : ((|l| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.2 hl
  have h2 : (l : ℂ) ^ 2 = ((|l| : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
  rw [inv_pow, h2]; field_simp

theorem hTrans_smul (σ : ℂ) {l : ℝ} (hl : l ≠ 0) (ν y : ℝ) :
    hTrans σ ν (l * y) = ((|l| : ℝ) : ℂ) ^ (-1 - 2 * σ) * hTrans σ (l * ν) y := by
  have key := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => phi σ ((t : ℂ) + ((l * y : ℝ) : ℂ) * I) *
      Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))) l
  unfold hTrans
  rw [← smul_eq_mul (a := ((|l| : ℝ) : ℂ) ^ _)]
  have habs : |l⁻¹| = |l|⁻¹ := abs_inv l
  have hpos : 0 < |l| := abs_pos.2 hl
  have e1 : ∫ t : ℝ, phi σ ((t : ℂ) + ((l * y : ℝ) : ℂ) * I) *
      Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))) =
      |l| • ∫ t : ℝ, phi σ (((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * ((l * t : ℝ) : ℂ))) := by
    rw [key, habs, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  rw [e1]
  have e2 : ∀ t : ℝ, phi σ (((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * ((l * t : ℝ) : ℂ))) =
      ((l : ℂ)⁻¹ ^ 2 * ((|l| : ℝ) : ℂ) ^ (-2 * σ)) * (phi σ ((t : ℂ) + (y : ℂ) * I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * I * ((l * ν : ℝ) : ℂ) * (t : ℂ)))) := by
    intro t
    rw [show ((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I = (l : ℂ) * ((t : ℂ) + (y : ℂ) * I) by push_cast; ring,
      phi_smul σ hl]
    push_cast; ring_nf
  simp_rw [e2]
  rw [MeasureTheory.integral_const_mul, Complex.real_smul, smul_eq_mul, ← mul_assoc, ← mul_assoc,
    abs_mul_inv_sq hl]
  congr 1
  have h1 : ((|l| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [sub_eq_add_neg, Complex.cpow_add _ _ h1, Complex.cpow_neg_one, neg_mul]

end GlobalTheory.HeckeTwoUnit

namespace GlobalTheory.HeckeTwoUnit

theorem prod_abs_unit_cpow {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (ε : (𝓞 F)ˣ) (s : ℂ) :
    ∏ τ : Emb F, ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s = 1 := by
  have hprod : ∀ (S : Finset (Emb F)), ∏ τ ∈ S, ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s =
      ((∏ τ ∈ S, |τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s := by
    classical
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (Finset.prod_nonneg fun _ _ => abs_nonneg _)]
  rw [hprod]
  have h := GlobalTheory.HeckeTwoExp.abs_norm_eq_prod ((ε : 𝓞 F) : F)
  rw [← Complex.ofReal_prod] at h
  have hn : |((Algebra.norm ℚ ((ε : 𝓞 F) : F) : ℚ) : ℝ)| = 1 := by
    have := Units.norm F ε
    exact_mod_cast this
  rw [← h, hn, Complex.ofReal_one, Complex.one_cpow]

theorem fTerm_unit_mul {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (σ : ℂ) (z : Emb F → ℂ) (b ν : F)
    (ε : (𝓞 F)ˣ) :
    fTerm σ z (((ε : 𝓞 F) : F) * b) ν = fTerm σ z b (((ε : 𝓞 F) : F) * ν) := by
  have hne : ∀ τ : Emb F, τ ((ε : 𝓞 F) : F) ≠ 0 := fun τ h => by
    have hu : ((ε : 𝓞 F) : F) ≠ 0 := by
      intro h0; have := unit_inv_mul ε; rw [h0, mul_zero] at this; exact zero_ne_one this
    exact hu ((map_eq_zero τ).1 h)
  unfold fTerm
  have e : ∀ τ : Emb F, Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ (((ε : 𝓞 F) : F) * b) * (z τ).re : ℝ) : ℂ)) *
      hTrans σ (τ ν) (τ (((ε : 𝓞 F) : F) * b) * (z τ).im) =
      ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ (-1 - 2 * σ) *
      (Complex.exp (2 * (Real.pi : ℂ) * I * ((τ (((ε : 𝓞 F) : F) * ν) * τ b * (z τ).re : ℝ) : ℂ)) *
      hTrans σ (τ (((ε : 𝓞 F) : F) * ν)) (τ b * (z τ).im)) := by
    intro τ
    rw [map_mul, map_mul, mul_assoc (τ ((ε : 𝓞 F) : F)) (τ b), hTrans_smul σ (hne τ)]
    rw [show τ ν * (τ ((ε : 𝓞 F) : F) * τ b) * (z τ).re = τ ((ε : 𝓞 F) : F) * τ ν * τ b * (z τ).re by ring]
    ring
  simp_rw [e]
  rw [Finset.prod_mul_distrib, prod_abs_unit_cpow, one_mul]

end GlobalTheory.HeckeTwoUnit

namespace GlobalTheory.HeckeTwoUnit

theorem fTerm_unit_move : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (σ : ℂ) (z : Emb F → ℂ) (b ν : F) (ε : (𝓞 F)ˣ),
    fTerm σ z (((ε : 𝓞 F) : F) * b) ν = fTerm σ z b (((ε : 𝓞 F) : F) * ν) :=
  fun _ _ _ _ σ z b ν ε => fTerm_unit_mul σ z b ν ε

end GlobalTheory.HeckeTwoUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierTransformZeroEqStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePhiFourierTransform_zero_eq : ∀ (σ : ℂ) (y : ℝ), y ≠ 0 → GlobalTheory.HeckeTwo.hTrans σ 0 y = GlobalTheory.HeckeTwo.cConst σ * ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
  first | exact @GlobalTheory.HeckeTwo.hTrans_zero_eq | exact GlobalTheory.HeckeTwo.hTrans_zero_eq | (intros; apply GlobalTheory.HeckeTwo.hTrans_zero_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOnePrimeOverConstantIdeal
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_one_prime_over_constant_ideal : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (E : Type) [CommRing E] [Algebra A[X] E] [Algebra A E] [IsScalarTower A A[X] E]
    [Algebra.Etale A[X] E] (Q : Ideal E) [Q.IsPrime] (P : Ideal (Localization.AtPrime Q)) [P.IsPrime]
    (p : Ideal A) [p.IsPrime], p.height = 1 →
    P.comap (algebraMap A[X] (Localization.AtPrime Q)) = p.map (Polynomial.C : A →+* A[X]) →
    (∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P)) ∧
      ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime p) π) →
        Irreducible (algebraMap A (Localization.AtPrime P) π) := by
  first | (exact @GlobalTheory.EtalePolyDvr.isDiscreteValuationRing_atPrime_of_etale_polynomial) | (exact GlobalTheory.EtalePolyDvr.isDiscreteValuationRing_atPrime_of_etale_polynomial) | (intros; apply GlobalTheory.EtalePolyDvr.isDiscreteValuationRing_atPrime_of_etale_polynomial  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianModelsConjUnitaryOfNormClassStatement
section
open GlobalTheory.UnitLemma Polynomial Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianModels_conj_unitary_of_norm_class : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ γ' : Matrix (Fin n) (Fin n) K.E) (x x' v : B.Aˣ) (ψ ψ' : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ → GlobalTheory.InertUnitOrb.IsModel B γ' x' ψ' → (x' : B.A) = x * (v * B.σ v) → ∃ u : Matrix (Fin n) (Fin n) K.E, (u.map K.c)ᵀ * u = 1 ∧ γ * u = u * γ' := by
  first | exact @GlobalTheory.InertUnitOrb.conj_of_norm_class | exact GlobalTheory.InertUnitOrb.conj_of_norm_class | (intros; apply GlobalTheory.InertUnitOrb.conj_of_norm_class <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointGlueOpenCoverStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_point_glue_open_cover : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x : ∀ i, GlobalTheory.HilbGlue.HPt z r (𝒰.X i)), (∀ i j (R : Scheme.{0}) (b : R ⟶ 𝒰.X i) (c : R ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → GlobalTheory.HilbGlue.HPt.map b (x i) = GlobalTheory.HilbGlue.HPt.map c (x j)) → ∃ y : GlobalTheory.HilbGlue.HPt z r Y, ∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) y = x i := by
  first | (exact @GlobalTheory.HilbGlue.HPt.exists_glue) | (exact GlobalTheory.HilbGlue.HPt.exists_glue) | (intros; apply GlobalTheory.HilbGlue.HPt.exists_glue <;> assumption)
end

