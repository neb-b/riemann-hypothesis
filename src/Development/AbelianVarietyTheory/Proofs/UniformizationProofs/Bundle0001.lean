module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EigenTensorFullLeftSupport
section
namespace GlobalTheory

open TensorProduct

noncomputable def rightContract {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) : TensorProduct F E E' →ₗ[F] E :=
  (TensorProduct.rid F E).toLinearMap ∘ₗ TensorProduct.map LinearMap.id l

theorem rightContract_tmul {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) (x : E) (y : E') :
    rightContract l (x ⊗ₜ[F] y) = l y • x := by
  simp [rightContract]

theorem rightContract_map {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) (f : E →ₗ[F] E) (g : E' →ₗ[F] E')
    (w : TensorProduct F E E') :
    rightContract l (TensorProduct.map f g w) = f (rightContract (l ∘ₗ g) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [rightContract_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem eq_zero_of_rightContract {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (w : TensorProduct F E E')
    (h : ∀ l : E' →ₗ[F] F, rightContract l w = 0) : w = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace F E'
  have key : ∀ (i) (v : TensorProduct F E E'),
      TensorProduct.equivFinsuppOfBasisRight b v i = rightContract (b.coord i) v := by
    intro i v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [rightContract_tmul]
    | add a c ha hc => simp only [map_add (f := _), Finsupp.add_apply, ha, hc]
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  rw [key, h]
  simp

theorem eigenTensor_full_left_support :
    ∀ (F : Type) [Field F] (E E' Ix : Type) [AddCommGroup E] [Module F E] [AddCommGroup E'] [Module F E'] (Φ : Ix → (E →ₗ[F] E)) (Φ' : Ix → (E' ≃ₗ[F] E')), (∀ U : Submodule F E, (∀ i, ∀ v ∈ U, Φ i v ∈ U) → U = ⊥ ∨ U = ⊤) → ∀ w : TensorProduct F E E', w ≠ 0 → (∀ i, ∃ r : F, TensorProduct.map (Φ i) (Φ' i : E' →ₗ[F] E') w = r • w) → ∀ π : E →ₗ[F] E, TensorProduct.map π (LinearMap.id : E' →ₗ[F] E') w = 0 → π = 0 := by
  intro F _ E E' Ix _ _ _ _ Φ Φ' hirr w hw heig π hπ
  let U : Submodule F E := Submodule.span F (Set.range fun l : E' →ₗ[F] F => rightContract l w)
  have hmem : ∀ l : E' →ₗ[F] F, rightContract l w ∈ U := fun l => Submodule.subset_span ⟨l, rfl⟩
  have hstab : ∀ i, ∀ v ∈ U, Φ i v ∈ U := by
    intro i v hv
    have hle : U ≤ U.comap (Φ i) := by
      apply Submodule.span_le.2
      rintro _ ⟨l, rfl⟩
      obtain ⟨r, hr⟩ := heig i
      have h1 := rightContract_map (l ∘ₗ ((Φ' i).symm : E' →ₗ[F] E')) (Φ i) (Φ' i : E' →ₗ[F] E') w
      have h2 : (l ∘ₗ ((Φ' i).symm : E' →ₗ[F] E')) ∘ₗ (Φ' i : E' →ₗ[F] E') = l := by
        ext y; simp
      rw [h2, hr, map_smul] at h1
      show Φ i (rightContract l w) ∈ U
      rw [← h1]
      exact U.smul_mem _ (hmem _)
    exact hle hv
  rcases hirr U hstab with hU | hU
  · exfalso
    apply hw
    apply eq_zero_of_rightContract
    intro l
    have := hmem l
    rwa [hU, Submodule.mem_bot] at this
  · have hle : U ≤ LinearMap.ker π := by
      apply Submodule.span_le.2
      rintro _ ⟨l, rfl⟩
      have h1 := rightContract_map l π LinearMap.id w
      rw [hπ, map_zero, LinearMap.comp_id] at h1
      exact h1.symm
    rw [hU, top_le_iff] at hle
    exact LinearMap.ker_eq_top.1 hle

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCommonMultiple
section
open Module

namespace GlobalTheory.FiniteCover

theorem finrank_le_of_range_le {K P Q E : Type*} [Field K] [AddCommGroup P] [Module K P]
    [AddCommGroup Q] [Module K Q] [AddCommGroup E] [Module K E] [Module.Finite K Q]
    (L : P →ₗ[K] E) (hL : Function.Injective L) (B : Q →ₗ[K] E) (h : ∀ p, ∃ q, B q = L p) :
    finrank K P ≤ finrank K Q := by
  rw [← LinearMap.finrank_range_of_inj hL]
  refine (Submodule.finrank_mono (t := LinearMap.range B) ?_).trans B.finrank_range_le
  rintro _ ⟨p, rfl⟩
  exact h p

theorem exists_denominator {A C F F' ι : Type*} [CommRing A] [IsDomain A] [CommRing C] [IsDomain C]
    [Field F] [Field F'] [Algebra A C] [Module.Finite A C] [Algebra A F] [IsFractionRing A F]
    [Algebra C F'] [IsFractionRing C F'] [Algebra F F'] [Algebra A F'] [IsScalarTower A F F']
    [IsScalarTower A C F'] [Fintype ι] (e : Basis ι F F') :
    ∃ c : A, c ≠ 0 ∧
      (∀ j (y : C), ∃ a : A, algebraMap A F a = algebraMap A F c * e.repr (algebraMap C F' y) j) ∧
      ∀ j, ∃ y : C, algebraMap C F' y = algebraMap A F c • e j := by
  classical
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := C)
  obtain ⟨c₁, hc₁⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A)
    (fun p : ι × Fin n => e.repr (algebraMap C F' (g p.2)) p.1)
  have h2 : ∀ j, ∃ c : A, c ≠ 0 ∧ ∃ y : C, algebraMap C F' y = algebraMap A F c • e j := by
    intro j
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := C) (e j)
    have hinj : Function.Injective (algebraMap A C) := by
      have : Function.Injective (algebraMap A F') := by
        rw [IsScalarTower.algebraMap_eq A F F']
        exact (algebraMap F F').injective.comp (IsFractionRing.injective A F)
      rw [IsScalarTower.algebraMap_eq A C F'] at this
      exact Function.Injective.of_comp this
    have hal : IsAlgebraic A q := (Algebra.IsIntegral.isIntegral (R := A) q).isAlgebraic
    obtain ⟨c, hc, z, hz⟩ := hal.exists_nonzero_dvd hq
    refine ⟨c, hc, z * p, ?_⟩
    have hq' : algebraMap C F' q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    rw [← hpq, Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A C F', hz, map_mul, map_mul]
    field_simp
  choose c₂ hc₂ y₂ hy₂ using h2
  refine ⟨c₁ * ∏ j, c₂ j, mul_ne_zero (nonZeroDivisors.coe_ne_zero c₁)
    (Finset.prod_ne_zero_iff.2 fun j _ => hc₂ j), fun j y => ?_, fun j => ?_⟩
  · have hy : y ∈ Submodule.span A (Set.range g) := hg ▸ Submodule.mem_top
    suffices h : ∃ a : A, algebraMap A F a = algebraMap A F c₁ * e.repr (algebraMap C F' y) j by
      obtain ⟨a, ha⟩ := h
      exact ⟨a * ∏ j, c₂ j, by rw [map_mul, map_mul, ha]; ring⟩
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      obtain ⟨a, ha⟩ := hc₁ (j, k)
      exact ⟨a, by rw [ha, Algebra.smul_def]⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), map_add (f := _), Finsupp.add_apply, ha, hb, mul_add]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨r * a, ?_⟩
      have : algebraMap C F' (r • x) = algebraMap A F r • algebraMap C F' x := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, ha]
      ring
  · refine ⟨(c₁ * ∏ k ∈ Finset.univ.erase j, c₂ k : A) • y₂ j, ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), ← mul_assoc, map_mul (algebraMap A F) _ (c₂ j),
      mul_smul (algebraMap A F _), ← hy₂, Algebra.smul_def, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem exists_common_multiple {F I : Type*} [Field F] [Fintype I] (A : I → Subring F) (ρ c : I → F)
    (hρ : ∀ i, ρ i ≠ 0) (hc : ∀ i, c i ≠ 0) (hr : ∀ i k, ρ i / ρ k ∈ A k)
    (hext : ∀ i k, ∃ m : ℕ, c i * (ρ i / ρ k) ^ m ∈ A k) :
    ∃ (a : ℕ) (u : F), u ≠ 0 ∧ ∀ i, ∃ b ∈ A i, u = ρ i ^ a * c i * b := by
  classical
  choose m hm using hext
  let M : I → ℕ := fun i => ∑ k, m i k
  have hM : ∀ i k, c i * (ρ i / ρ k) ^ M i ∈ A k := fun i k => by
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (f := m i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    change c i * (ρ i / ρ k) ^ (∑ k, m i k) ∈ A k
    rw [hl, pow_add, ← mul_assoc]
    exact mul_mem (hm i k) (pow_mem (hr i k) _)
  refine ⟨∑ i, M i, ∏ i, c i * ρ i ^ M i,
    Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hc i) (pow_ne_zero _ (hρ i)), fun k => ?_⟩
  refine ⟨∏ i ∈ Finset.univ.erase k, c i * (ρ i / ρ k) ^ M i, prod_mem fun i _ => hM i k, ?_⟩
  have e : ∀ i, c i * ρ i ^ M i = ρ k ^ M i * (c i * (ρ i / ρ k) ^ M i) := fun i => by
    have := hρ k
    rw [div_pow]
    field_simp
  rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ k), div_self (hρ k), one_pow, mul_one, mul_assoc]

theorem finrank_sandwich {K F F' I : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Fintype I] {d : ℕ} (e : Basis (Fin d) F F')
    (A : I → Subring F) (C : I → Subring F') (ρ c : I → F)
    (hρ : ∀ i, ρ i ≠ 0) (hc : ∀ i, c i ≠ 0) (hr : ∀ i k, ρ i / ρ k ∈ A k)
    (hext : ∀ i k, ∃ m : ℕ, c i * (ρ i / ρ k) ^ m ∈ A k)
    (hAC : ∀ i, ∀ a ∈ A i, algebraMap F F' a ∈ C i)
    (hc₁ : ∀ i j, ∀ y ∈ C i, c i * e.repr y j ∈ A i) (hc₂ : ∀ i j, c i • e j ∈ C i)
    (V W : ℕ → Type*) [∀ t, AddCommGroup (V t)] [∀ t, Module K (V t)] [∀ t, AddCommGroup (W t)]
    [∀ t, Module K (W t)] (hV : ∀ t, Module.Finite K (V t)) (hW : ∀ t, Module.Finite K (W t))
    (α : ∀ t, V t →ₗ[K] F) (β : ∀ t, W t →ₗ[K] F') (hα : ∀ t, Function.Injective (α t))
    (hβ : ∀ t, Function.Injective (β t))
    (rα : ∀ t x, (∃ v, α t v = x) ↔ ∀ i, ∃ a ∈ A i, x = a * ρ i ^ t)
    (rβ : ∀ t y, (∃ w, β t w = y) ↔ ∀ i, ∃ a ∈ C i, y = a * algebraMap F F' (ρ i ^ t)) :
    ∃ a : ℕ, ∀ t : ℕ, d * finrank K (V t) ≤ finrank K (W (t + a)) ∧
      finrank K (W t) ≤ d * finrank K (V (t + a)) := by
  obtain ⟨a, u, hu, hub⟩ := exists_common_multiple A ρ c hρ hc hr hext
  have hpi : ∀ t, finrank K (Fin d → V t) = d * finrank K (V t) := fun t => by
    rw [Module.finrank_pi_fintype]
    simp
  refine ⟨a, fun t => ⟨?_, ?_⟩⟩
  · rw [← hpi]
    let L : (Fin d → V t) →ₗ[K] F' :=
      ((e.equivFun.symm.toLinearMap.restrictScalars K).comp
        (((LinearMap.mulLeft K u).comp (α t)).compLeft (Fin d)))
    have hL : ∀ v, L v = ∑ j, (u * α t (v j)) • e j := fun v => e.equivFun_symm_apply _
    refine finrank_le_of_range_le L ?_ (β (t + a)) fun v => (rβ _ _).2 fun i => ?_
    · intro v w h
      have h' := e.equivFun.symm.injective h
      funext j
      exact hα t (mul_left_cancel₀ hu (congrFun h' j))
    · obtain ⟨b, hb, rfl⟩ := hub i
      choose x hx hx' using fun j => (rα t _).1 ⟨v j, rfl⟩ i
      refine ⟨∑ j, algebraMap F F' (b * x j) * (c i • e j),
        sum_mem fun j _ => mul_mem (hAC i _ (mul_mem hb (hx j))) (hc₂ i j), ?_⟩
      rw [hL, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hx' j]
      simp only [Algebra.smul_def, map_mul, map_pow, pow_add]
      ring
  · rw [← hpi]
    let L : W t →ₗ[K] (Fin d → F) := ((LinearMap.mulLeft K u).compLeft (Fin d)).comp
      ((e.equivFun.toLinearMap.restrictScalars K).comp (β t))
    have hL : ∀ w j, L w j = u * e.repr (β t w) j := fun w j => rfl
    refine finrank_le_of_range_le L ?_ ((α (t + a)).compLeft (Fin d)) fun w => ?_
    · intro v w h
      refine hβ t (e.equivFun.injective (funext fun j => ?_))
      exact mul_left_cancel₀ hu (congrFun h j)
    · have key : ∀ j, ∃ v, α (t + a) v = L w j := fun j => (rα _ _).2 fun i => by
        obtain ⟨b, hb, hub⟩ := hub i
        obtain ⟨y, hy, hy'⟩ := (rβ t _).1 ⟨w, rfl⟩ i
        refine ⟨b * (c i * e.repr y j), mul_mem hb (hc₁ i j y hy), ?_⟩
        rw [hL, hy', mul_comm y, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, hub,
          pow_add]
        ring
      choose v hv using key
      exact ⟨v, funext hv⟩

end GlobalTheory.FiniteCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFactorFractionRing
section
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.AffineFactorExists

theorem exists_affine_factor {F : Type} [Field F] {X : Scheme.{0}}
    (x : Spec (CommRingCat.of F) ⟶ X) :
    ∃ (A : CommRingCat.{0}) (ι : Spec A ⟶ X) (_ : IsOpenImmersion ι) (φ : A ⟶ CommRingCat.of F),
      Spec.map φ ≫ ι = x := by
  obtain ⟨i, z, hz⟩ := X.affineCover.exists_eq (x default)
  let ι : Spec _ ⟶ X := X.affineCover.f i
  have hι : IsOpenImmersion ι := inferInstanceAs (IsOpenImmersion (X.affineCover.f i))
  have hr : Set.range x ⊆ Set.range ι := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = default := Subsingleton.elim _ _
    exact ⟨z, hz⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift ι x hr)
  exact ⟨_, ι, hι, φ, by rw [hφ, IsOpenImmersion.lift_fac]⟩

theorem exists_factor_fractionRing {V A F : Type} [CommRing V] [CommRing A] [Field F]
    [Algebra V A] [Algebra V F] (φ : A →ₐ[V] F) (s : Set A) (hs : Algebra.adjoin V s = ⊤)
    (W : Subalgebra V F)
    (h : ∀ a ∈ s, ∃ u ∈ W, ∃ v ∈ W, v ≠ (0 : F) ∧ φ a * v = u) :
    ∃ (j : FractionRing W →+* F) (φ' : A →+* FractionRing W),
      j.comp (algebraMap W (FractionRing W)) = algebraMap W F ∧ j.comp φ' = φ.toRingHom := by
  have hinj : Function.Injective (algebraMap W F) := Subtype.val_injective
  let j : FractionRing W →+* F := IsFractionRing.lift hinj
  have hj : ∀ w : W, j (algebraMap W (FractionRing W) w) = w := fun w =>
    IsFractionRing.lift_algebraMap hinj w
  have hmem : ∀ a : A, φ a ∈ j.range := by
    intro a
    have ha : a ∈ Algebra.adjoin V s := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨u, hu, v, hv, hv0, e⟩ := h a ha
      refine ⟨algebraMap W _ ⟨u, hu⟩ / algebraMap W _ ⟨v, hv⟩, ?_⟩
      rw [map_div₀, hj, hj, div_eq_iff hv0, e]
    | algebraMap r =>
      exact ⟨algebraMap W _ (algebraMap V W r), by rw [hj, AlgHom.commutes]; rfl⟩
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let e : FractionRing W ≃+* j.range :=
    RingEquiv.ofBijective j.rangeRestrict
      ⟨j.rangeRestrict.injective, j.rangeRestrict_surjective⟩
  refine ⟨j, e.symm.toRingHom.comp (φ.toRingHom.codRestrict j.range hmem), RingHom.ext hj, ?_⟩
  ext a
  exact congrArg Subtype.val (e.apply_symm_apply ⟨φ a, hmem a⟩)

theorem exists_finset_extends (V F : Type) [CommRing V] [Field F] [Algebra V F]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [IsProper f]
    (x : Spec (CommRingCat.of F) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V F))) :
    ∃ t : Finset F, ∀ W : Subalgebra V F, ValuationRing W →
      (∀ x ∈ t, ∃ a ∈ W, ∃ b ∈ W, b ≠ (0 : F) ∧ x * b = a) →
      ∃ y : Spec (CommRingCat.of W) ⟶ X,
        y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V W)) ∧
        Spec.map (CommRingCat.ofHom (algebraMap W F)) ≫ y = x := by
  classical
  obtain ⟨A, ι, hι, φ, hφ⟩ := exists_affine_factor x
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (ι ≫ f)
  have hft : ψ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hψ]
    infer_instance
  have hcomp : ψ ≫ φ = CommRingCat.ofHom (algebraMap V F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, ← Category.assoc, hφ, hx]
  let : Algebra V A := ψ.hom.toAlgebra
  have hft' : Algebra.FiniteType V A := hft
  obtain ⟨s, hs⟩ := hft'.out
  let φa : A →ₐ[V] F :=
    { φ.hom with commutes' := fun r => congrArg (fun g => g.hom r) hcomp }
  refine ⟨s.image φ.hom, fun W hW ht => ?_⟩
  obtain ⟨j, φ', hj, hφ'⟩ := exists_factor_fractionRing φa s hs W
    (fun a ha => ht _ (Finset.mem_image_of_mem _ ha))
  have hE : ValuativeCriterion.Existence f := by
    have : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at this
    exact this.1
  have hring : ψ ≫ CommRingCat.ofHom φ' =
      CommRingCat.ofHom (algebraMap V W) ≫
        CommRingCat.ofHom (algebraMap W (FractionRing W)) := by
    ext r
    apply j.injective
    have h1 := RingHom.congr_fun hφ' (ψ.hom r)
    have h2 := RingHom.congr_fun hj (algebraMap V W r)
    exact (h1.trans (φa.commutes r)).trans h2.symm
  have w : (Spec.map (CommRingCat.ofHom φ') ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap W (FractionRing W))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V W)) := by
    rw [Category.assoc, ← hψ, ← Spec.map_comp, ← Spec.map_comp, hring]
  obtain ⟨l, hl₁, hl₂⟩ :=
    (hE { R := W, K := FractionRing W, commSq := ⟨w⟩, .. }).exists_lift
  dsimp only at hl₁ hl₂
  refine ⟨l, hl₂, ?_⟩
  have e₁ : CommRingCat.ofHom (algebraMap W F) =
      CommRingCat.ofHom (algebraMap W (FractionRing W)) ≫ CommRingCat.ofHom j := by
    rw [← hj]; rfl
  have e₂ : φ = CommRingCat.ofHom φ' ≫ CommRingCat.ofHom j := by
    ext a
    exact (RingHom.congr_fun hφ' a).symm
  rw [e₁, Spec.map_comp, Category.assoc, hl₁, ← Category.assoc, ← Spec.map_comp, ← e₂, hφ]

end GlobalTheory.AffineFactorExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteSeparablePoint
section
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.FiniteSeparablePoints

theorem exists_factor_of_unramified {k Ω S : Type} [Field k] [Field Ω] [Algebra k Ω] [CommRing S]
    [Algebra k S] [Algebra.FormallyUnramified k S] [Algebra.FiniteType k S] (φ : S →ₐ[k] Ω) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ ψ : S →+* K, (algebraMap K Ω).comp ψ = φ.toRingHom := by
  classical
  let R : Subalgebra k Ω := φ.range
  have hsurj : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have : Algebra.FiniteType k R := Algebra.FiniteType.of_surjective φ.rangeRestrict hsurj
  have : Algebra.FormallyUnramified k R := Algebra.FormallyUnramified.of_surjective φ.rangeRestrict hsurj
  have : Module.Finite k R := Algebra.FormallyUnramified.finite_of_free k R
  have hF : IsField R := isField_of_isIntegral_of_isField' (R := k) (Field.toIsField k)
  let K : IntermediateField k Ω := R.toIntermediateField' hF
  have hmem : ∀ x, φ x ∈ K.toSubalgebra := fun x => ⟨x, rfl⟩
  let ψ : S →ₐ[k] K := φ.codRestrict K.toSubalgebra hmem
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have : Algebra.FiniteType k K := Algebra.FiniteType.of_surjective ψ hψ
  have : Algebra.FormallyUnramified k K := Algebra.FormallyUnramified.of_surjective ψ hψ
  have : Module.Finite k K := Algebra.FormallyUnramified.finite_of_free k K
  refine ⟨K, inferInstance, (Algebra.FormallyUnramified.iff_isSeparable k K).1 inferInstance,
    ψ.toRingHom, ?_⟩
  ext x
  rfl

theorem exists_finite_separable_point {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {X : Scheme} (p : X ⟶ Spec (CommRingCat.of k)) [FormallyUnramified p]
    [LocallyOfFiniteType p] (a : Spec (CommRingCat.of Ω) ⟶ X)
    (h : a ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ b : Spec (CommRingCat.of K) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ b = a := by
  classical
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
  obtain ⟨_, ⟨U, hU0, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (a pt)) isOpen_univ
  have hU : IsAffineOpen U := hU0
  have hrange : Set.range a ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    rwa [Subsingleton.elim y pt]
  have hca : IsOpenImmersion.lift hU.fromSpec a hrange ≫ hU.fromSpec = a :=
    IsOpenImmersion.lift_fac _ _ _
  obtain ⟨f, hf⟩ : ∃ f, Spec.map f = IsOpenImmersion.lift hU.fromSpec a hrange :=
    ⟨_, Spec.map_preimage _⟩
  obtain ⟨g, hg⟩ : ∃ g, Spec.map g = hU.fromSpec ≫ p := ⟨_, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom (algebraMap k Ω) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hf, hg, ← Category.assoc, hca, h]
  have hU1 : RingHom.FormallyUnramified g.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @FormallyUnramified), hg]
    exact HasRingHomProperty.comp_of_isOpenImmersion @FormallyUnramified hU.fromSpec p ‹_›
  have hU2 : RingHom.FiniteType g.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hg]
    infer_instance
  let _ : Algebra k Γ(X, U) := g.hom.toAlgebra
  have : Algebra.FormallyUnramified k Γ(X, U) := hU1
  have : Algebra.FiniteType k Γ(X, U) := hU2
  let φ' : Γ(X, U) →ₐ[k] Ω :=
    { f.hom with
      commutes' := fun r => by
        have e := congrArg (fun q => q.hom r) hgf
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
        exact e }
  obtain ⟨K, hK1, hK2, ψ, hψ⟩ := exists_factor_of_unramified φ'
  refine ⟨K, hK1, hK2, Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_⟩
  have e : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap K Ω) = f := by
    ext x
    exact congrArg (fun q => q x) hψ
  rw [← Category.assoc, ← Spec.map_comp, e, hf, hca]

end GlobalTheory.FiniteSeparablePoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemPowOfRatioOfTorsionFree
section
namespace GlobalTheory

theorem exists_mem_pow_of_ratio_of_torsionFree :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type) [CommRing O]
      (io : V →+* O), (∀ v : V, v ≠ 0 → ∀ x : O, io v * x = 0 → x = 0) →
      ∀ (f h : O) (p q : V) (m n : ℕ), q ≠ 0 → io q * f = io p * h →
      f ∈ (IsLocalRing.maximalIdeal V ^ (m + n)).map io →
      h ∉ (IsLocalRing.maximalIdeal V ^ (m + 1)).map io →
      ∃ r ∈ IsLocalRing.maximalIdeal V ^ n, p = r * q := by
  intro V _ _ _ O _ io htf f h p q m n hq e hf hh
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hm : IsLocalRing.maximalIdeal V = Ideal.span {π} := hπ.maximalIdeal_eq
  have hπn : π ^ n ∈ IsLocalRing.maximalIdeal V ^ n := by
    rw [hm, Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _
  have key : π ^ n * q ∣ p → ∃ r ∈ IsLocalRing.maximalIdeal V ^ n, p = r * q := by
    rintro ⟨c, hc⟩
    exact ⟨π ^ n * c, Ideal.mul_mem_right _ _ hπn, by rw [hc]; ring⟩
  rcases ValuationRing.dvd_total (π ^ n * q) p with hd | ⟨c, hc⟩
  · exact key hd
  by_cases hu : IsUnit c
  · apply key
    obtain ⟨u, rfl⟩ := hu
    exact ⟨(u⁻¹ : Vˣ), by rw [hc, mul_assoc, Units.mul_inv, mul_one]⟩
  exfalso
  apply hh
  have hcm : c ∈ IsLocalRing.maximalIdeal V := hu
  rw [hm, Ideal.mem_span_singleton] at hcm
  obtain ⟨d, rfl⟩ := hcm
  have hp : p ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (pow_ne_zero n hπ.ne_zero) hq (by simpa using hc)
  rw [hm, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at hf ⊢
  obtain ⟨g, rfl⟩ := hf
  refine ⟨io d * g, ?_⟩
  have h0 := htf p hp (h - io (π ^ (m + 1)) * (io d * g)) (by
    have hc' := congrArg io hc
    simp only [map_mul, map_pow] at hc' e ⊢
    linear_combination (io π ^ m * g) * hc' - e)
  exact sub_eq_zero.mp h0

end GlobalTheory
end

