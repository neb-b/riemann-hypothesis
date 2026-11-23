module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.HomologyRowExactOfStabilisationPattern
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.Row

theorem hMap_zero' {k G : Type} [CommRing k] [Group G] (A B : Rep k G) (n : ℕ) :
    hMap (0 : A ⟶ B) n = 0 := by
  simp [hMap, groupHomology.map]

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p),
    (∀ p, d (p + 1) ≫ d p = 0) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k)
    (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q) (T : ℕ),
    (∀ p q, p ≤ T → IsIso (e p q)) →
    (∀ p q, p + 1 ≤ T → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) →
    ∀ p q, p + 2 ≤ T → (Even p → Function.Injective (s p q).hom) →
    (Odd p → Function.Surjective (s (p + 1) q).hom) →
    Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom := by
  intro k G _ _ C d hd M e s T hiso hrel p q hp hinj hsurj
  have bij : ∀ p q, p ≤ T → Function.Bijective (e p q).hom := fun p q h =>
    (ConcreteCategory.isIso_iff_bijective (e p q)).1 (hiso p q h)
  have rel : ∀ p q, p + 1 ≤ T → ∀ m, (hMap (d p) q).hom ((e (p + 1) q).hom m) =
      (if Even p then s p q ≫ e p q else 0).hom m :=
    fun p q h m => congrArg (fun f => ModuleCat.Hom.hom f m) (hrel p q h)
  intro y
  obtain ⟨m, rfl⟩ := (bij (p + 1) q (by omega)).2 y
  rcases Nat.even_or_odd p with hev | hod
  · have hnot : ¬ Even (p + 1) := by
      rw [Nat.even_add_one]
      exact not_not.2 hev
    rw [rel p q (by omega), if_pos hev]
    constructor
    · intro h0
      have h1 : (s p q).hom m = 0 := by
        apply (bij p q (by omega)).1
        rw [map_zero]
        exact h0
      have h2 : m = 0 := by
        apply hinj hev
        rw [h1, map_zero]
      exact ⟨0, by rw [h2, map_zero, map_zero]⟩
    · rintro ⟨z, hz⟩
      obtain ⟨w, rfl⟩ := (bij (p + 2) q hp).2 z
      have hw := rel (p + 1) q (by omega) w
      rw [if_neg hnot] at hw
      have hm : (e (p + 1) q).hom m = 0 := by
        rw [← hz]
        exact hw
      have hm0 : m = 0 := (bij (p + 1) q (by omega)).1 (by rw [hm, map_zero])
      rw [hm0, map_zero]
  · have hnot : ¬ Even p := Nat.not_even_iff_odd.2 hod
    have hev1 : Even (p + 1) := hod.add_one
    rw [rel p q (by omega), if_neg hnot]
    constructor
    · intro _
      obtain ⟨w, hw⟩ := hsurj hod m
      refine ⟨(e (p + 2) q).hom w, ?_⟩
      rw [rel (p + 1) q (by omega), if_pos hev1, ← hw]
      rfl
    · intro _
      rfl

end GlobalTheory.HomStab.Row

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.homology_row_exact_of_stabilisation_pattern : ∀ (k G : Type) [CommRing k] [Group G] (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q) (T : ℕ), (∀ p q, p ≤ T → IsIso (e p q)) → (∀ p q, p + 1 ≤ T → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → ∀ p q, p + 2 ≤ T → (Even p → Function.Injective (s p q).hom) → (Odd p → Function.Surjective (s (p + 1) q).hom) → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom := by
  first
  | exact @GlobalTheory.HomStab.Row.main
  | exact @GlobalTheory.HomStab.Row.hMap_zero'
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PermCoefPreservesShortExact
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem permCoef_shortExact : ∀ (k G : Type) [CommRing k] [Group G] (X : Type) [MulAction G X] (S : ShortComplex (Rep k G)), S.ShortExact → ∃ h : permCoef X S.f ≫ permCoef X S.g = 0, (ShortComplex.mk (permCoef X S.f) (permCoef X S.g) h).ShortExact := by
  intro k G _ _ X _ S hS
  have hf : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have hex : LinearMap.range S.f.hom.toLinearMap = LinearMap.ker S.g.hom.toLinearMap :=
    (hS.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  have hfg : ∀ a, S.g.hom (S.f.hom a) = 0 := fun a => by
    have := congrArg (fun φ => Rep.Hom.hom φ a) S.zero
    exact this
  have hz : permCoef X S.f ≫ permCoef X S.g = 0 := by
    ext x a y
    change S.g.hom (S.f.hom (Finsupp.single x a y)) = 0
    exact hfg _
  refine ⟨hz, ?_⟩
  have hm : Mono (permCoef X S.f) := by
    rw [Rep.mono_iff_injective]
    exact Finsupp.mapRange_injective _ (map_zero _) hf
  have he : Epi (permCoef X S.g) := by
    rw [Rep.epi_iff_surjective]
    exact Finsupp.mapRange_surjective _ (map_zero _) hg
  refine { exact := ?_ }
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change (Finsupp.mapRange.linearMap S.f.hom.toLinearMap : (X →₀ S.X₁) →ₗ[k] (X →₀ S.X₂)).range =
    (Finsupp.mapRange.linearMap S.g.hom.toLinearMap : (X →₀ S.X₂) →ₗ[k] (X →₀ S.X₃)).ker
  rw [Finsupp.ker_mapRange, Finsupp.range_mapRange_linearMap _ (LinearMap.ker_eq_bot.2 hf), hex]

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.permCoef_preserves_shortExact : ∀ (k G : Type) [CommRing k] [Group G] (X : Type) [MulAction G X] (S : ShortComplex (Rep k G)), S.ShortExact → ∃ h : permCoef X S.f ≫ permCoef X S.g = 0, (ShortComplex.mk (permCoef X S.f) (permCoef X S.g) h).ShortExact := by
  first
  | exact @GlobalTheory.HomStab.permCoef_shortExact
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ProjectivePermTensorFree
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

noncomputable section

namespace GlobalTheory.HomStab

variable {k G : Type} [CommRing k] [Group G]

def freeSwap (G X ι : Type) [Group G] [MulAction G X] : (X × ι) × G ≃ (X × ι) × G where
  toFun p := ((p.2⁻¹ • p.1.1, p.1.2), p.2)
  invFun p := ((p.2 • p.1.1, p.1.2), p.2)
  left_inv p := by simp
  right_inv p := by simp

def freeLEquiv (k G X ι : Type) [CommRing k] [Group G] [MulAction G X] :
    (X →₀ ι →₀ MonoidAlgebra k G) ≃ₗ[k] ((X × ι) →₀ MonoidAlgebra k G) :=
  Finsupp.mapRange.linearEquiv (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k)) ≪≫ₗ
    (Finsupp.curryLinearEquiv k).symm ≪≫ₗ (Finsupp.curryLinearEquiv k).symm ≪≫ₗ
    Finsupp.domLCongr (freeSwap G X ι) ≪≫ₗ Finsupp.curryLinearEquiv k ≪≫ₗ
    Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k).symm

theorem freeLEquiv_single (X ι : Type) [MulAction G X] (x : X) (i : ι) (g : G) (r : k) :
    freeLEquiv k G X ι (Finsupp.single x (Finsupp.single i (MonoidAlgebra.single g r))) =
      Finsupp.single (g⁻¹ • x, i) (MonoidAlgebra.single g r) := by
  simp [freeLEquiv, freeSwap]

def permFreeIso (k G : Type) [CommRing k] [Group G] (X ι : Type) [MulAction G X] :
    permT X (Rep.free k G ι) ≅ Rep.free k G (X × ι) :=
  Rep.mkIso { freeLEquiv k G X ι with
    isIntertwining' := fun h => by
      ext x i g : 4
      simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, MonoidAlgebra.lsingle_apply]
      rw [permRep_single]
      erw [Representation.free_single_single]
      simp [freeLEquiv_single, Representation.free_single_single, mul_smul] }

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (X ι : Type) [MulAction G X],
    Projective (permT X (Rep.free k G ι)) := by
  intro k G _ _ X ι _
  exact Projective.of_iso (permFreeIso k G X ι).symm inferInstance

end GlobalTheory.HomStab

end

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.projective_perm_tensor_free : ∀ (k G : Type) [CommRing k] [Group G] (X ι : Type) [MulAction G X], Projective (permT X (Rep.free k G ι)) := by
  first
  | exact @GlobalTheory.HomStab.main
  | exact @GlobalTheory.HomStab.freeLEquiv_single
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ProjectiveRepGroupHomologyPosVanishes
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem isZero_groupHomology_succ_of_projective : ∀ (k G : Type) [CommRing k] [Group G] (P : Rep k G), Projective P → ∀ n : ℕ, IsZero (groupHomology P (n + 1)) := by
  intro k G _ _ P hP n
  classical
  let S : Subgroup G := ⊥
  let B : Rep k S := Rep.res S.subtype P
  let adj := Rep.indResAdjunction k S.subtype
  let ε : (Rep.indFunctor k S.subtype).obj B ⟶ P := adj.counit.app P
  have hε : Epi ε := by
    rw [Rep.epi_iff_surjective]
    intro x
    refine ⟨(adj.unit.app B).hom x, ?_⟩
    have h2 := congrArg (fun f => f.hom x) (adj.right_triangle_components P)
    exact h2
  let s := Projective.factorThru (𝟙 P) ε
  have hs : s ≫ ε = 𝟙 P := Projective.factorThru_comp _ _
  have hZ : IsZero (groupHomology (Rep.ind S.subtype B) (n + 1)) :=
    (isZero_groupHomology_succ_of_subsingleton B n).of_iso
      (groupHomology.indIso S B (n + 1))
  rw [IsZero.iff_id_eq_zero]
  have hid : (groupHomology.functor k G (n + 1)).map (s ≫ ε) = 𝟙 _ := by
    rw [hs]
    exact CategoryTheory.Functor.map_id _ _
  refine Eq.trans hid.symm ?_
  rw [CategoryTheory.Functor.map_comp,
    hZ.eq_of_tgt ((groupHomology.functor k G (n + 1)).map s) 0]
  exact zero_comp

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.projective_rep_groupHomology_pos_vanishes : ∀ (k G : Type) [CommRing k] [Group G] (P : Rep k G), Projective P → ∀ n : ℕ, IsZero (groupHomology P (n + 1)) := by
  first
  | exact @GlobalTheory.HomStab.isZero_groupHomology_succ_of_projective
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ProjectiveResFreeRepOfInjective
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem resFunctor_isEquivalence_of_bijective {k G H : Type} [CommRing k] [Group G] [Group H]
    (ψ : H →* G) (hψ : Function.Bijective ψ) : (Rep.resFunctor (k := k) ψ).IsEquivalence := by
  let e : H ≃* G := MulEquiv.ofBijective ψ hψ
  haveI : (Rep.resFunctor (k := k) ψ).Full := Rep.full_res ψ hψ.2
  haveI : (Rep.resFunctor (k := k) ψ).EssSurj := ⟨fun N => ⟨Rep.of (N.ρ.comp e.symm.toMonoidHom),
    ⟨Rep.mkIso (.mk (LinearEquiv.refl k N.V) fun h => by
      ext x
      change N.ρ (e.symm (ψ h)) x = N.ρ h x
      have : e.symm (ψ h) = h := e.symm_apply_apply h
      rw [this])⟩⟩⟩
  exact { }

theorem projective_res_of_injective {k G H : Type} [CommRing k] [Group G] [Group H]
    (φ : H →* G) (hφ : Function.Injective φ) (P : Rep k G) [Projective P] :
    Projective (Rep.res φ P) := by
  let ψ : H →* φ.range := φ.rangeRestrict
  have hψ : Function.Bijective ψ := ⟨φ.rangeRestrict_injective_iff.2 hφ, φ.rangeRestrict_surjective⟩
  haveI := resFunctor_isEquivalence_of_bijective (k := k) ψ hψ
  have h1 : Projective (Rep.res φ.range.subtype P) :=
    (Rep.resFunctor (k := k) φ.range.subtype).projective_obj_of_projective (X := P) inferInstance
  have h2 : Projective (Rep.res ψ (Rep.res φ.range.subtype P)) :=
    (Rep.resFunctor (k := k) ψ).projective_obj_of_projective h1
  exact h2

end GlobalTheory.HomStab

theorem GlobalTheory.HomStab.projective_res_free_of_injective : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G), Function.Injective φ → ∀ ι : Type, Projective (Rep.res φ (Rep.free k G ι)) := by
  intro k G H _ _ _ φ hφ ι
  exact GlobalTheory.HomStab.projective_res_of_injective φ hφ _

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.projective_res_free_rep_of_injective : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G), Function.Injective φ → ∀ ι : Type, Projective (Rep.res φ (Rep.free k G ι)) := by
  first
  | exact @GlobalTheory.HomStab.projective_res_free_of_injective
  | exact @GlobalTheory.HomStab.projective_res_of_injective
  | exact @GlobalTheory.HomStab.resFunctor_isEquivalence_of_bijective
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainBoundaryCompBoundaryApply
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx.BdBd

theorem bd_single (V : Type) (l : List V) (r : ℤ) :
    bd V (Finsupp.single l r) =
      r • ∑ i ∈ Finset.range l.length, (-1 : ℤ) ^ i • Finsupp.single (l.eraseIdx i) (1 : ℤ) := by
  simp [bd, Finsupp.linearCombination_single]

noncomputable def consMap (V : Type) (x : V) : (List V →₀ ℤ) →ₗ[ℤ] (List V →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun l : List V => x :: l)

theorem bd_single_cons (V : Type) (x : V) (l : List V) :
    bd V (Finsupp.single (x :: l) 1) =
      Finsupp.single l 1 - consMap V x (bd V (Finsupp.single l 1)) := by
  rw [bd_single, bd_single, one_smul, one_smul, List.length_cons, Finset.sum_range_succ']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [consMap, map_sum, map_zsmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, pow_zero, one_smul, pow_succ, mul_neg_one,
    neg_smul, Finset.sum_neg_distrib]
  abel

theorem bd_consMap (V : Type) (x : V) :
    bd V ∘ₗ consMap V x = LinearMap.id - consMap V x ∘ₗ bd V := by
  apply Finsupp.lhom_ext
  intro l r
  have h : Finsupp.single l r = r • Finsupp.single l (1 : ℤ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [h]
  simp only [map_zsmul]
  rw [show consMap V x (Finsupp.single l 1) = Finsupp.single (x :: l) 1 by
    simp [consMap, Finsupp.mapDomain_single], bd_single_cons, smul_sub]

theorem bd_bd_single (V : Type) (l : List V) : bd V (bd V (Finsupp.single l 1)) = 0 := by
  induction l with
  | nil => simp [bd_single]
  | cons x l ih =>
    rw [bd_single_cons, map_sub]
    have := congrArg (fun f => f (bd V (Finsupp.single l 1))) (bd_consMap V x)
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at this
    rw [this, ih, map_zero]
    abel

end GlobalTheory.SeqCx.BdBd

namespace GlobalTheory.SeqCx

theorem bd_bd : ∀ (V : Type) (c : List V →₀ ℤ), bd V (bd V c) = 0 := by
  intro V c
  have h : bd V ∘ₗ bd V = 0 := by
    apply Finsupp.lhom_ext
    intro l r
    have e : Finsupp.single l r = r • Finsupp.single l (1 : ℤ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [e, map_zsmul, map_zsmul, GlobalTheory.SeqCx.BdBd.bd_bd_single, smul_zero]
  exact congrArg (fun f => f c) h

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqChain_boundary_comp_boundary_apply : ∀ (V : Type) (c : List V →₀ ℤ), bd V (bd V c) = 0 := by
  first
  | exact @GlobalTheory.SeqCx.bd_bd
  | exact @GlobalTheory.SeqCx.BdBd.bd_bd_single
  | exact @GlobalTheory.SeqCx.BdBd.bd_consMap
  | exact @GlobalTheory.SeqCx.BdBd.bd_single_cons
  | exact @GlobalTheory.SeqCx.BdBd.bd_single
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainBoundaryPrefixChain
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

private theorem bd_single_eq_sum_neg_one_pow_eraseIdx (V : Type) (l : List V) :
    bd V (Finsupp.single l 1) =
      ∑ i ∈ Finset.range l.length, (-1 : ℤ) ^ i • Finsupp.single (l.eraseIdx i) 1 := by
  simp [bd, Finsupp.linearCombination_single]

theorem bd_single_append (V : Type) (τ w : List V) :
    bd V (Finsupp.single (τ ++ w) 1) =
      Finsupp.mapDomain (fun σ => σ ++ w) (bd V (Finsupp.single τ 1)) +
      (-1 : ℤ) ^ τ.length • Finsupp.mapDomain (fun w => τ ++ w) (bd V (Finsupp.single w 1)) := by
  simp only [bd_single_eq_sum_neg_one_pow_eraseIdx, Finsupp.mapDomain_finsetSum, Finset.smul_sum]
  rw [List.length_append, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single, List.eraseIdx_append_of_lt_length hi]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single,
      List.eraseIdx_append_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      pow_add, mul_smul]

theorem bd_mapDomain_prepend : ∀ (V : Type) (τ : List V) (c : List V →₀ ℤ), bd V (Finsupp.mapDomain (fun w => τ ++ w) c) = (c.sum fun w a => a • Finsupp.mapDomain (fun σ => σ ++ w) (bd V (Finsupp.single τ 1))) + (-1 : ℤ) ^ τ.length • Finsupp.mapDomain (fun w => τ ++ w) (bd V c) := by
  intro V τ c
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add, map_add (f := _), hf, hg, map_add (f := _), Finsupp.mapDomain_add, smul_add,
      Finsupp.sum_add_index' (by intro; simp) (by intros; simp [add_smul])]
    abel
  | single w a =>
    rw [Finsupp.mapDomain_single, Finsupp.sum_single_index (by simp)]
    have h1 : Finsupp.single (τ ++ w) a = a • Finsupp.single (τ ++ w) (1 : ℤ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    have h2 : Finsupp.single w a = a • Finsupp.single w (1 : ℤ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h1, h2, map_smul, map_smul, bd_single_append, Finsupp.mapDomain_smul, smul_add, smul_comm a]

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqChain_boundary_prefix_chain : ∀ (V : Type) (τ : List V) (c : List V →₀ ℤ), bd V (Finsupp.mapDomain (fun w => τ ++ w) c) = (c.sum fun w a => a • Finsupp.mapDomain (fun σ => σ ++ w) (bd V (Finsupp.single τ 1))) + (-1 : ℤ) ^ τ.length • Finsupp.mapDomain (fun w => τ ++ w) (bd V c) := by
  first
  | exact @GlobalTheory.SeqCx.bd_mapDomain_prepend
  | exact @GlobalTheory.SeqCx.bd_single_append
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainCycleBoundedByCone
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

theorem cone_cycle_isBoundary : ∀ (V : Type) (F G : Set (List V)) (x : V), (∀ l ∈ G, x :: l ∈ F) →
    ∀ (p : ℕ), ∀ c ∈ chains G p, bd V c = 0 → ∃ b ∈ chains F (p + 1), bd V b = c := by
  classical
  intro V F G x hx p c hc hbd
  let cone : (List V →₀ ℤ) →ₗ[ℤ] (List V →₀ ℤ) := Finsupp.lmapDomain ℤ ℤ (fun l : List V => x :: l)
  have hcone : ∀ l : List V, cone (Finsupp.single l 1) = Finsupp.single (x :: l) 1 := by
    intro l
    simp [cone, Finsupp.mapDomain_single]
  have hs : ∀ l : List V, bd V (cone (Finsupp.single l 1)) =
      Finsupp.single l 1 - cone (bd V (Finsupp.single l 1)) := by
    intro l
    rw [hcone]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [bd, Finsupp.linearCombination_single, one_smul, List.length_cons,
      Finset.sum_range_succ', List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, pow_zero,
      map_sum, map_zsmul, hcone, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib]
    abel
  have key : ∀ d : List V →₀ ℤ, bd V (cone d) = d - cone (bd V d) := by
    intro d
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      rw [map_add (f := _), map_add (f := _), hf, hg, map_add (f := _), map_add (f := _)]
      abel
    | single l n =>
      rw [← Finsupp.smul_single_one]
      simp only [map_zsmul, hs, smul_sub]
  refine ⟨cone c, ?_, ?_⟩
  · rw [chains, Finsupp.mem_supported]
    intro l hl
    have hl' := Finsupp.mapDomain_support hl
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hl'
    have hm' := (Finsupp.mem_supported _ _).mp hc hm
    exact ⟨hx m hm'.1, by simp [hm'.2]⟩
  · rw [key, hbd, map_zero, sub_zero]

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqChain_cycle_bounded_by_cone : ∀ (V : Type) (F G : Set (List V)) (x : V), (∀ l ∈ G, x :: l ∈ F) → ∀ (p : ℕ), ∀ c ∈ chains G p, bd V c = 0 → ∃ b ∈ chains F (p + 1), bd V b = c := by
  first
  | exact @GlobalTheory.cone_cycle_isBoundary
end
end

