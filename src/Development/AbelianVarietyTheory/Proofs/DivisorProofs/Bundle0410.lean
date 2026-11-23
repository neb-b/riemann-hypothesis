module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0392
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyEqualOrUnit
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_equal_or_unit : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) (e u : A' ⊗[A] A'), (∀ a : A', (a ⊗ₜ[A] (1 : A') - (1 : A') ⊗ₜ[A] a) * e = 0) → algebraMap A (A' ⊗[A] A') f * u = 1 - e → ∀ (T : Scheme.{0}) (y y' : T ⟶ Spec (CommRingCat.of A')), y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) = y' ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) → Loc T fun V k => k ≫ y = k ≫ y' ∨ IsUnit (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (k ≫ y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop).hom f) := by
  first | (exact @GlobalTheory.EtC.PairDich.pair_dich) | (exact GlobalTheory.EtC.PairDich.pair_dich) | (intros; apply GlobalTheory.EtC.PairDich.pair_dich  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeIsKInjectiveBijectiveHypercohomologyIStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mappingCone_isKInjective_bijective_hypercohomology_iff : ∀ (R : Type) [CommRing R] {D C : Cx R} (f : D ⟶ C) (m : ℤ), D.IsStrictlyGE m → C.IsStrictlyGE m → (∀ n, CategoryTheory.Injective (D.X n)) → (∀ n, CategoryTheory.Injective (C.X n)) → (mappingCone f).IsKInjective ∧ ∀ K : Cx R, ((∀ n, Function.Bijective (cpush K f n)) ↔ ∀ n, Subsingleton (CohomologyClass K (mappingCone f) n)) := by
  first | (exact @GlobalTheory.EtC.cone_kinj_and_bijective_iff) | (exact GlobalTheory.EtC.cone_kinj_and_bijective_iff) | (intros; apply GlobalTheory.EtC.cone_kinj_and_bijective_iff  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeShortExactAugmentationClassEq
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConeClass

variable {R : Type} [CommRing R]

theorem mk_ofHom_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) :
    CohomologyClass.mk (Cocycle.ofHom (f ≫ g)) = cpull f M 0 (CohomologyClass.mk (Cocycle.ofHom g)) := by
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem mk_injective_sgl (X : Shv R) (I : Cx R) [I.IsStrictlyGE 0] :
    Function.Injective (CohomologyClass.mk : Cocycle (sgl X) I 0 → CohomologyClass (sgl X) I 0) := by
  intro a b h
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff (m := -1) (hm := by norm_num)] at h
  obtain ⟨β, hβ⟩ := h
  have hβ0 : β = 0 := by
    refine Cochain.ext _ _ fun p q hpq => ?_
    by_cases hp : p = 0
    · subst hp
      exact (CochainComplex.isZero_of_isStrictlyGE I 0 q (by omega)).eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _
  rw [hβ0, δ_zero] at hβ
  exact sub_eq_zero.1 (Cocycle.ext hβ.symm)

theorem cpull_single_injective {X Y : Shv R} (g : X ⟶ Y) [Epi g] (I : Cx R) [I.IsStrictlyGE 0] :
    Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map g) I 0) := by
  intro x y h
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  have h' := mk_injective_sgl X I h
  have hg : Epi (((CochainComplex.singleFunctor (Shv R) 0).map g).f 0) := by
    change Epi (((HomologicalComplex.single _ _ 0).map g).f 0)
    rw [HomologicalComplex.single_map_f_self]
    infer_instance
  congr 1
  refine Cocycle.ext (Cochain.ext _ _ fun p q hpq => ?_)
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = 0 := by omega
    have e := congrArg (fun z : Cocycle (sgl X) I 0 => z.1.v 0 0 (add_zero 0)) h'
    simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe, Cochain.comp_v _ _ (zero_add 0) 0 0 0 (add_zero 0) (add_zero 0),
      Cochain.ofHom_v] at e
    exact (cancel_epi _).1 e
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _

theorem mk_ofHom_eq_of_homotopy {K L : Cx R} (f g : K ⟶ L) (h : Homotopy f g) :
    CohomologyClass.mk (Cocycle.ofHom f) = CohomologyClass.mk (Cocycle.ofHom g) := by
  have e := congrArg (fun φ => φ (CohomologyClass.mk (Cocycle.ofHom (𝟙 L)))) ((GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.2.2.2 f g ⟨h⟩ L 0).1
  simpa only [← mk_ofHom_comp, Category.comp_id] using e

end GlobalTheory.EtC.ConeClass

namespace GlobalTheory.EtC.ConeClass

theorem cone_class_eq : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
    ∀ (hc : (CochainComplex.singleFunctor (Shv R) 0).map S.f ≫ resAug S.X₂ = resAug S.X₁ ≫ resMap R S.f)
    (e : HomotopyEquiv (mappingCone (resMap R S.f)) (res R S.X₃)),
    Homotopy (mappingCone.inr (resMap R S.f) ≫ e.hom) (resMap R S.g) →
    CohomologyClass.mk (Cocycle.ofHom
        (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0)) ≫ resAug S.X₃)) =
      CohomologyClass.mk (Cocycle.ofHom
        (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)) := by
  intro R _ S hS hc e hh
  have hS' : (S.map (CochainComplex.singleFunctor (Shv R) 0)).ShortExact :=
    hS.map_of_exact (HomologicalComplex.single _ _ _)
  haveI : QuasiIso (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) :=
    mappingCone.quasiIso_descShortComplex hS'
  haveI : (res R S.X₃).IsKInjective := inferInstanceAs ((injectiveResolution S.X₃).cochainComplex.IsKInjective)
  haveI : (res R S.X₃).IsStrictlyGE 0 := inferInstanceAs ((injectiveResolution S.X₃).cochainComplex.IsStrictlyGE 0)
  haveI : Epi S.g := hS.epi_g
  have hbij := GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso R (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) (res R S.X₃) 0
  obtain ⟨c, hc'⟩ := hbij.2 (CohomologyClass.mk (Cocycle.ofHom
    (mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)))
  refine (mk_ofHom_comp _ _).trans (Eq.trans ?_ hc')
  refine congrArg _ ?_
  have hinr : mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫
      mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc = resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) := by
    simp [mappingCone.map]
  have hres : resAug S.X₂ ≫ resMap R S.g = (CochainComplex.singleFunctor (Shv R) 0).map S.g ≫ resAug S.X₃ :=
    InjectiveResolution.Hom.ι'_comp_hom'
      ⟨InjectiveResolution.desc S.g (injectiveResolution _) (injectiveResolution _),
        InjectiveResolution.desc_commutes_zero _ _ _⟩
  apply cpull_single_injective S.g (res R S.X₃)
  have hA : cpull ((CochainComplex.singleFunctor (Shv R) 0).map S.g) (res R S.X₃) 0
      (CohomologyClass.mk (Cocycle.ofHom (resAug S.X₃))) =
      CohomologyClass.mk (Cocycle.ofHom (resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) ≫ e.hom)) := by
    calc cpull ((CochainComplex.singleFunctor (Shv R) 0).map S.g) (res R S.X₃) 0
            (CohomologyClass.mk (Cocycle.ofHom (resAug S.X₃)))
        = CohomologyClass.mk (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv R) 0).map S.g ≫ resAug S.X₃)) :=
          (mk_ofHom_comp _ _).symm
      _ = CohomologyClass.mk (Cocycle.ofHom (resAug S.X₂ ≫ resMap R S.g)) := by rw [hres]
      _ = CohomologyClass.mk (Cocycle.ofHom (resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) ≫ e.hom)) :=
          (mk_ofHom_eq_of_homotopy _ _ (hh.compLeft (resAug S.X₂))).symm
  have hB1 : CohomologyClass.mk (Cocycle.ofHom (mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫
        mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)) =
      cpull (mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f) (res R S.X₃) 0
          (cpull (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) (res R S.X₃) 0 c) := by
    rw [hc', mk_ofHom_comp]
  have hB2 : cpull (mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f) (res R S.X₃) 0
          (cpull (mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor (Shv R) 0))) (res R S.X₃) 0 c) =
      cpull ((CochainComplex.singleFunctor (Shv R) 0).map S.g) (res R S.X₃) 0 c := by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1, mappingCone.inr_descShortComplex]
    rfl
  have hC : (CohomologyClass.mk (Cocycle.ofHom (resAug S.X₂ ≫ mappingCone.inr (resMap R S.f) ≫ e.hom)) :
        CohomologyClass (sgl S.X₂) (res R S.X₃) 0) =
      CohomologyClass.mk (Cocycle.ofHom (mappingCone.inr (S.map (CochainComplex.singleFunctor (Shv R) 0)).f ≫
        mappingCone.map _ (resMap R S.f) (resAug S.X₁) (resAug S.X₂) hc ≫ e.hom)) := by
    rw [reassoc_of% hinr]
  exact hA.trans (hC.trans (hB1.trans hB2))

end GlobalTheory.EtC.ConeClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatActApply
section
noncomputable section

namespace GlobalTheory.UPel.HT.LieLin

open NumberField

section Mod

variable {O T V : Type} [CommRing O] [CommRing T] [AddCommGroup V] [Module T V]

def eigSub (μ : O →+* Module.End T V) (τ : O →+* T) : Submodule T V where
  carrier := {v | ∀ c, μ c v = τ c • v}
  add_mem' {u v} hu hv c := by simp only [Set.mem_setOf_eq, map_add (f := _), hu c, hv c, smul_add]
  zero_mem' c := by simp
  smul_mem' r v hv c := by simp only [Set.mem_setOf_eq, map_smul, hv c, smul_comm r]

theorem mem_eigSub {μ : O →+* Module.End T V} {τ : O →+* T} {v : V} :
    v ∈ eigSub μ τ ↔ ∀ c, μ c v = τ c • v := Iff.rfl

def LieMod (μ : O →+* Module.End T V) (ω : O) (ρ : T) {a : ℕ} (τ : Fin a → (O →+* T)) : Prop :=
  ∀ v, μ ω v = ρ • v → ∃ w : Fin a → V, (∀ i, w i ∈ eigSub μ (τ i)) ∧ v = ∑ i, w i

end Mod

def matAct {O B T : Type} [CommRing O] [CommRing B] [CommRing T] {n : ℕ} (M : O →+* Matrix (Fin n) (Fin n) B)
    (f : B →+* T) : O →+* Module.End T (Fin n → T) :=
  (Matrix.toLinAlgEquiv' (R := T) (n := Fin n)).toRingEquiv.toRingHom.comp (f.mapMatrix.comp M)

theorem matAct_apply {O B T : Type} [CommRing O] [CommRing B] [CommRing T] {n : ℕ}
    (M : O →+* Matrix (Fin n) (Fin n) B) (f : B →+* T) (c : O) (v : Fin n → T) :
    matAct M f c v = ((M c).map f).mulVec v := rfl

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def lieMat (b : Base D R) {B : Type} [CommRing B] (βB : R →+* B) {n : ℕ} (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B)
    (c : Fin D.a → 𝓞 D.F) : Matrix (Fin n) (Fin n) B :=
  (List.ofFn fun i => M (c i) - algebraMap B (Matrix (Fin n) (Fin n) B) (βB (b.t i (c i)))).prod *
    (M D.ω - algebraMap B (Matrix (Fin n) (Fin n) B) (βB ((D.tr : R) - b.ρ)))

def lieIdeal (b : Base D R) {B : Type} [CommRing B] (βB : R →+* B) {n : ℕ}
    (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) : Ideal B :=
  Ideal.span {x | ∃ (c : Fin D.a → 𝓞 D.F) (i j : Fin n), lieMat b βB M c i j = x}

def LieHerMat (b : Base D R) {B : Type} [CommRing B] {n : ℕ} (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B)
    {T : Type} [CommRing T] (f : B →+* T) (β : R →+* T) : Prop :=
  ∀ (T' : Type) [CommRing T'] (g : T →+* T'),
    LieMod (matAct M (g.comp f)) D.ω (g (β b.ρ)) (fun i => (g.comp β).comp (b.t i)) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (h : T' →+* k) (i : Fin D.a),
      Module.finrank k (eigSub (matAct M (h.comp (g.comp f))) ((h.comp (g.comp β)).comp (b.t i))) = D.m

end GlobalTheory.UPel.HT.LieLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRegularFormsOfWedgePairingPerfect
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

section Wedge

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem omB_smul_mem (B : Subalgebra k K) (q : ℕ) {c : K} (hc : c ∈ B) {z : DR k K}
    (hz : z ∈ omB k K B q) : c • z ∈ omB k K B q := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hz
    exact Submodule.subset_span ⟨c * b, B.mul_mem hc hb, v, hv, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

def topCoefBasis {n : ℕ} (b : Module.Basis (Fin n) K Ω[K⁄k]) : DR k K →ₗ[K] K :=
  ExteriorAlgebra.liftAlternating (fun i => if h : i = n then h ▸ b.det else 0)

theorem topCoefBasis_ιMulti {n : ℕ} (b : Module.Basis (Fin n) K Ω[K⁄k]) (v : Fin n → Ω[K⁄k]) :
    topCoefBasis b (ExteriorAlgebra.ιMulti K n v) = b.det v := by
  simp [topCoefBasis, ExteriorAlgebra.liftAlternating_apply_ιMulti]

theorem topCoefBasis_mem (B : Subalgebra k K) {n : ℕ} (b : Module.Basis (Fin n) K Ω[K⁄k]) (f : K)
    (hf : ∀ (v : B) (j : Fin n), ∃ c : B, f * b.repr (D k K (v : K)) j = c)
    {z : DR k K} (hz : z ∈ omB k K B n) : ∃ e : B, f ^ n * topCoefBasis b z = e := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b0, hb0, v, hv, rfl⟩ := hz
    choose M hM using fun i j => hf ⟨v j, hv j⟩ i
    have hmat : f • b.toMatrix (fun j => D k K (v j)) = (B.val : B →+* K).mapMatrix (Matrix.of M) := by
      ext i j
      simp [Module.Basis.toMatrix_apply, ← hM]
    have hdet := congrArg Matrix.det hmat
    rw [Matrix.det_smul, Fintype.card_fin, ← RingHom.map_det] at hdet
    refine ⟨⟨b0, hb0⟩ * (Matrix.of M).det, ?_⟩
    rw [map_smul, topCoefBasis_ιMulti, Module.Basis.det_apply, smul_eq_mul, mul_left_comm, hdet]
    simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨e1, h1⟩ := hx
    obtain ⟨e2, h2⟩ := hy
    exact ⟨e1 + e2, by rw [map_add (f := _), mul_add, h1, h2]; simp⟩
  | smul r x _ hx =>
    obtain ⟨e, he⟩ := hx
    exact ⟨r • e, by rw [LinearMap.map_smul_of_tower, mul_smul_comm, he]; simp⟩

theorem eq_sum_exteriorPower_basis {n q : ℕ} (b : Module.Basis (Fin n) K Ω[K⁄k]) (Y : ⋀[K]^q Ω[K⁄k]) :
    (Y : DR k K) = ∑ t, (b.exteriorPower q).repr Y t •
      ExteriorAlgebra.ιMulti K q (b ∘ (Set.powersetCard.ofFinEmbEquiv.symm t)) := by
  conv_lhs => rw [← (b.exteriorPower q).sum_repr Y]
  simp [exteriorPower.coe_basis, exteriorPower.ιMulti_family]

theorem wedge_coef_mem (B : Subalgebra k K) {p q : ℕ} (b : Module.Basis (Fin (p + q)) K Ω[K⁄k])
    (u : Fin (p + q) → B) (hb : ∀ j, b j = D k K (u j : K)) (f : K)
    (hf : ∀ (v : B) (j : Fin (p + q)), ∃ c : B, f * b.repr (D k K (v : K)) j = c)
    (Y : ⋀[K]^q Ω[K⁄k]) (hmul : ∀ a ∈ omB k K B p, a * (Y : DR k K) ∈ omB k K B (p + q))
    (s : Set.powersetCard (Fin (p + q)) q) :
    ∃ e : B, f ^ (p + q) * (b.exteriorPower q).repr Y s = e := by
  classical
  have hcard : (s.val)ᶜ.card = p := by
    rw [Finset.card_compl, Fintype.card_fin, s.prop]; omega
  set g := Finset.orderEmbOfFin (s.val)ᶜ hcard with hg
  set a : DR k K := ExteriorAlgebra.ιMulti K p (b ∘ g) with ha_def
  have ha : a ∈ omB k K B p :=
    Submodule.subset_span ⟨1, B.one_mem, fun j => (u (g j) : K), fun j => (u (g j)).2,
      by simp [a, Function.comp_def, hb]⟩
  obtain ⟨e, he⟩ := topCoefBasis_mem B b f hf (hmul a ha)
  have happ : ∀ h : Fin q → Fin (p + q),
      Fin.append (b ∘ g) (b ∘ h) = b ∘ Fin.append (fun i => g i) h := by
    intro h; funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  have hterm : ∀ t, t ≠ s → topCoefBasis b
      (a * ExteriorAlgebra.ιMulti K q (b ∘ (Set.powersetCard.ofFinEmbEquiv.symm t))) = 0 := by
    intro t hts
    obtain ⟨i, hit, his⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne t s).mp hts
    have hi1 : i ∈ Set.range g := by
      rw [hg, Finset.range_orderEmbOfFin]; simpa using his
    have hi2 : i ∈ Set.range (Set.powersetCard.ofFinEmbEquiv.symm t) :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t i).mpr hit
    obtain ⟨a1, ha1⟩ := hi1
    obtain ⟨a2, ha2⟩ := hi2
    rw [ha_def, ExteriorAlgebra.ιMulti_mul_ιMulti, topCoefBasis_ιMulti, happ]
    refine b.det.map_eq_zero_of_eq _ (i := Fin.castAdd q a1) (j := Fin.natAdd p a2) ?_ ?_
    · simp [ha1, ha2]
    · intro h; have := congrArg Fin.val h; simp at this; omega
  have hdiag : ∃ ε : ℤˣ, topCoefBasis b
      (a * ExteriorAlgebra.ιMulti K q (b ∘ (Set.powersetCard.ofFinEmbEquiv.symm s))) = ((ε : ℤ) : K) := by
    set h := Fin.append (fun i => g i) (Set.powersetCard.ofFinEmbEquiv.symm s) with hh
    have hinj : Function.Injective h := by
      rw [hh, Fin.append_injective_iff]
      refine ⟨g.injective, (Set.powersetCard.ofFinEmbEquiv.symm s).injective, fun i j hij => ?_⟩
      have h1 : g i ∈ (s.val)ᶜ := by
        rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin (s.val)ᶜ hcard]; exact ⟨i, rfl⟩
      have h2 : Set.powersetCard.ofFinEmbEquiv.symm s j ∈ s.val :=
        (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨j, rfl⟩
      rw [hij] at h1
      exact (Finset.mem_compl.mp h1) h2
    set σ := Equiv.ofBijective h (Finite.injective_iff_bijective.mp hinj)
    refine ⟨Equiv.Perm.sign σ, ?_⟩
    rw [ha_def, ExteriorAlgebra.ιMulti_mul_ιMulti, topCoefBasis_ιMulti, happ]
    have : b ∘ h = b ∘ σ := rfl
    rw [this, b.det.map_perm, Module.Basis.det_self, Units.smul_def, zsmul_eq_mul, mul_one]
  obtain ⟨ε, hε⟩ := hdiag
  have hsum : topCoefBasis b (a * (Y : DR k K)) = (b.exteriorPower q).repr Y s * ((ε : ℤ) : K) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_exteriorPower_basis b Y, Finset.mul_sum, map_sum, Finset.sum_eq_single s]
    · rw [mul_smul_comm, map_smul, hε, smul_eq_mul]
    · intro t _ hts; rw [mul_smul_comm, map_smul, hterm t hts, smul_zero]
    · intro h; exact absurd (Finset.mem_univ s) h
  refine ⟨e * ((ε : ℤ) : B), ?_⟩
  have hεε : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  push_cast
  rw [← he, hsum]
  calc f ^ (p + q) * (b.exteriorPower q).repr Y s
      = f ^ (p + q) * (b.exteriorPower q).repr Y s * (((ε : ℤ) : K) * ((ε : ℤ) : K)) := by rw [hεε, mul_one]
    _ = _ := by ring

theorem mem_omB_of_mul_mem_omB :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K]
      [Algebra.Smooth k B] (d p q : ℕ), Module.finrank K Ω[K⁄k] = d → p + q = d →
      ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K B p, a * y ∈ omB k K B d) → y ∈ omB k K B q := by
  intro k K _ _ _ B _ _ d p q hd hpq y hy hmul
  classical
  subst hpq
  let I : Ideal B :=
    { carrier := {c | (c : K) • y ∈ omB k K B q}
      add_mem' := fun {a c} ha hc => by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, add_smul] at *
        exact Submodule.add_mem _ ha hc
      zero_mem' := by simp
      smul_mem' := fun a c hc => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, mul_smul] at *
        exact omB_smul_mem B q a.2 hc }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨f, u, b, hfP, hb, hf⟩ := GlobalTheory.T.exists_local_kaehlerD_basis_smooth_subalgebra k K B (p + q) hd P
    apply hfP
    refine hP.isPrime.mem_of_pow_mem (p + q) (hIP ?_)
    show ((f ^ (p + q) : B) : K) • y ∈ omB k K B q
    have hy' := eq_sum_exteriorPower_basis b ⟨y, hy⟩
    simp only at hy'
    rw [hy', Finset.smul_sum]
    refine Submodule.sum_mem _ fun t _ => ?_
    obtain ⟨e, he⟩ := wedge_coef_mem B b u hb (f : K) hf ⟨y, hy⟩ hmul t
    rw [smul_smul, SubmonoidClass.coe_pow, he]
    exact Submodule.subset_span ⟨e, e.2, fun j => (u (Set.powersetCard.ofFinEmbEquiv.symm t j) : K),
      fun j => (u _).2,
      by simp [Function.comp_def, hb]⟩
  have h1 : (1 : B) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

end Wedge

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSymmetricCocyclesOfPullbackMulPStatement
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_symmetricCocycles_of_pullback_mulP : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ) (c : G.A n ⊗[R] G.A n), pullbackTwo (G.mulP n) c ∈ symCocycles R (G.A (n + 1)) → c ∈ symCocycles R (G.A n) := by
  first | exact @GlobalTheory.PDivGroup.mem_symCocycles_of_pullTwo_mulP | exact GlobalTheory.PDivGroup.mem_symCocycles_of_pullTwo_mulP | (intros; apply GlobalTheory.PDivGroup.mem_symCocycles_of_pullTwo_mulP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastSmulMemAugIdealSqSupMapMulPStatement
section
open scoped TensorProduct
open Coalgebra GlobalTheory.PDiv in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCast_smul_mem_augIdealSq_sup_map_mulP : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ), ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))), (p : R) • a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 ⊔ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  intro p R _ G n a ha
  have ha₀ : counit (R := R) a = 0 := ha
  have hres : G.res n a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A n)) := by
    change counit (R := R) (G.res n a) = 0
    rw [CoalgHomClass.counit_comp_apply, ha₀]
  have hmap : mulBy R (G.A (n + 1)) p a ∈ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map
      ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
    rw [← G.mulP_res n a]
    exact Ideal.mem_map_of_mem _ hres
  have hdiff : mulBy R (G.A (n + 1)) p a - (p : R) • a ∈
      RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 := by
    have hd : dUnit (R := R) (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0 := by
      change GlobalTheory.AugCot.d (Bialgebra.counitAlgHom R (G.A (n + 1)))
        (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0
      rw [map_sub, map_smul]
      change dUnit (R := R) (mulBy R (G.A (n + 1)) p a) - (p : R) • dUnit (R := R) a = 0
      rw [← cotMap_d, cotMap_mulBy, sub_self]
    have h := (GlobalTheory.AugCot.d_eq_zero_iff _ _).1 hd
    have hc : Bialgebra.counitAlgHom R (G.A (n + 1))
        (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0 := by
      change counit (R := R) (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0
      rw [map_sub, map_smul, CoalgHomClass.counit_comp_apply, ha₀, smul_zero, sub_zero]
    rwa [hc, map_zero, sub_zero] at h
  have hsmul : (p : R) • a = mulBy R (G.A (n + 1)) p a - (mulBy R (G.A (n + 1)) p a - (p : R) • a) :=
    (sub_sub_cancel _ _).symm
  rw [hsmul]
  exact sub_mem (Ideal.mem_sup_right hmap) (Ideal.mem_sup_left hdiff)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfPEqZeroStatement
section
open GlobalTheory.PDiv

theorem GlobalTheory.T.omega_baseChange_bijective_of_p_eq_zero {p : ℕ} {R : Type}
    [CommRing R] (G : GlobalTheory.PDivGroup p R) (R' : Type) [CommRing R'] [Algebra R R']
    (hp : (p : R) = 0) : Function.Bijective (liftSemi (G.toBase R').omega) :=
  G.omega_baseChange_bijective R' hp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicFaithfullyFlatDescentUnitCocyclesStatement
section
open TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles : ∀ (A : Type) [CommRing A], ∃ δ : ∀ (B : Type) [CommRing B] [Algebra A B], (B ⊗[A] B)ˣ → CommRing.Pic A, ∀ (B : Type) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B], (∀ u v, UCoc A B u → UCoc A B v → δ B (u * v) = δ B u * δ B v) ∧ (∀ u, UCoc A B u → (δ B u = 1 ↔ ∃ w : Bˣ, (u : B ⊗[A] B) * (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) w = (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) w)) ∧ (∀ c : CommRing.Pic A, CommRing.Pic.mapAlgebra A B c = 1 → ∃ u, UCoc A B u ∧ δ B u = c) ∧ (∀ u, UCoc A B u → ∃ _ : Module.Invertible A (descMod A B u), CommRing.Pic.mk A (descMod A B u) = δ B u) ∧ ∀ (B' : Type) [CommRing B'] [Algebra A B'] [Module.FaithfullyFlat A B'] (φ : B →ₐ[A] B') (u : (B ⊗[A] B)ˣ) (u' : (B' ⊗[A] B')ˣ), UCoc A B u → (u' : B' ⊗[A] B') = Algebra.TensorProduct.map φ φ (u : B ⊗[A] B) → δ B' u' = δ B u := by
  first | (exact @GlobalTheory.pic_cech_descent) | (exact GlobalTheory.pic_cech_descent) | (intros; apply GlobalTheory.pic_cech_descent  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeTensorPolynomialIsMaximalOfMemImageStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_tensor_polynomial_isMaximal_of_mem_image : ∀ (T : Type) [CommRing T] [IsDomain T], AIC T → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ P : Ideal (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), P.IsPrime → ∀ g : Polynomial T, g ≠ 0 → algebraMap (Polynomial T) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) g ∈ P → P.IsMaximal ∧ ∀ x : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)), ∃ c d : T, d ≠ 0 ∧ algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) d * x - algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) c ∈ P := by
  first | (exact @GlobalTheory.ClosedFibre.isMaximal_of_mem) | (exact GlobalTheory.ClosedFibre.isMaximal_of_mem) | (intros; apply GlobalTheory.ClosedFibre.isMaximal_of_mem  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyPairProdRootSumStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveFunctionCharpoly_pair_prod_rootSum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (m k l : ℕ) (e : Fin l → ℕ), 0 < m → ∑ᶠ x, psiG (rootSum θ k) m x * star (chG (fun P => ∏ j, rootSum θ (e j) P) m x) = (Nat.card (GL (Fin m) F) : ℂ) * ((Finset.univ.filter fun a : Fin l → Fin m => k ≡ ∑ j, e j * Nat.card F ^ (a j : ℕ) [MOD Nat.card F ^ m - 1]).card : ℂ) := by
  first | (exact @GlobalTheory.Shin.psiG_rootSum_pair_prod_rootSum) | (exact GlobalTheory.Shin.psiG_rootSum_pair_prod_rootSum) | (intros; apply GlobalTheory.Shin.psiG_rootSum_pair_prod_rootSum <;> assumption)
end

