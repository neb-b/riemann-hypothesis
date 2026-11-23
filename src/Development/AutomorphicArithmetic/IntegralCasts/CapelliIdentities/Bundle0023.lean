module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteSubfieldSpecial
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp :
    (R : Type) → [CommRing R] → AlgebraicGeometry.Scheme :=
    fun (R : Type) [CommRing R] ↦ AlgebraicGeometry.Spec (CommRingCat.of R)

@[reducible] noncomputable def UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.spMap :
    {R R' : Type} →
      [inst : CommRing R] → [inst_1 : CommRing R'] → (R →+* R') → (UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp R' ⟶ UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp R) :=
    fun {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') ↦ AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)

private lemma UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.exists_finite_subfield {A C : Type} [CommRing A] [Field C] [CharZero C]
    [Algebra.IsAlgebraic ℚ C] [Algebra.FiniteType ℤ A] (φ : A →+* C) :
    ∃ K : IntermediateField ℚ C, FiniteDimensional ℚ K ∧ ∀ a, φ a ∈ K := by
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℤ A).FG)
  refine ⟨IntermediateField.adjoin ℚ (φ '' (s : Set A)), ?_, ?_⟩
  · have : Finite (φ '' (s : Set A)) := (s.finite_toSet.image φ).to_subtype
    exact IntermediateField.finiteDimensional_adjoin
      (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral)
  · intro a
    have ha : a ∈ Algebra.adjoin ℤ (s : Set A) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | algebraMap r =>
      have : φ (algebraMap ℤ A r) = (r : C) := by simp
      rw [this]
      exact intCast_mem _ r
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

open AlgebraicGeometry CategoryTheory in
theorem UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.main :
    ∀ (C : Type) [inst : Field C] [inst_1 : CharZero C] [Algebra.IsAlgebraic ℚ C] (X : AlgebraicGeometry.Scheme)
      (π : X ⟶ UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp ℤ) [AlgebraicGeometry.LocallyOfFiniteType π] (x : UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp C ⟶ X),
      ∃ (K : Type) (x_1 : Field K) (_ : NumberField K) (e : K →+* C) (x' : UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.Sp K ⟶ X),
        CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.spMap e) x' = x := by
  intro C _ _ _ X π _ x
  let pt : Spec (CommRingCat.of C) := IsLocalRing.closedPoint C
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x pt) (U := ⊤) trivial
  have hrange : Set.range x ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have : y = pt := Subsingleton.elim _ _
    rw [this]
    exact hxU
  let y := IsOpenImmersion.lift hU.fromSpec x hrange
  have hy : y ≫ hU.fromSpec = x := IsOpenImmersion.lift_fac _ _ _
  let φ : Γ(X, U) →+* C := (Spec.preimage y).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = y := Spec.map_preimage y
  have hft : (π.appLE ⊤ U (by simp)).hom.FiniteType :=
    π.finiteType_appLE (isAffineOpen_top _) hU _
  have hft' : ((π.appLE ⊤ U (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom).FiniteType :=
    RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _
      ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv).2))
  have hA : Algebra.FiniteType ℤ Γ(X, U) := by
    have h : algebraMap ℤ Γ(X, U) = ((π.appLE ⊤ U (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom) := Subsingleton.elim _ _
    rw [← h] at hft'
    exact RingHom.finiteType_algebraMap.mp hft'
  obtain ⟨K, hK, hmem⟩ := UpperTheory.Reformulated.B.SpecPointFactorsThroughNumberField.exists_finite_subfield φ
  let ψ : Γ(X, U) →+* K := φ.codRestrict K hmem
  refine ⟨K, inferInstance, { to_finiteDimensional := hK }, K.val.toRingHom,
    Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_⟩
  rw [← hy, ← hφ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitelyGeneratedModPow
section
namespace UpperTheory.Reformulated.B.FinitelyGeneratedModPow

theorem fg_mod_pow {O A : Type} [CommRing O] [CommRing A] [Algebra O A] [IsNoetherianRing A]
    (m : Ideal A) (hres : ∀ x : A, ∃ a : O, x - algebraMap O A a ∈ m) (n : ℕ) :
    ∃ N : Submodule O A, N.FG ∧ ∀ x : A, ∃ y ∈ N, x - y ∈ m ^ n := by
  induction n with
  | zero => exact ⟨⊥, Submodule.fg_bot, fun x => ⟨0, Submodule.zero_mem _, by simp⟩⟩
  | succ n ih =>
    obtain ⟨N, hN, hx⟩ := ih
    obtain ⟨s, hs⟩ : (m ^ n).FG := IsNoetherian.noetherian (m ^ n)
    have key : ∀ z ∈ Ideal.span (s : Set A),
        ∃ w ∈ Submodule.span O (s : Set A), z - w ∈ m ^ (n + 1) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => exact ⟨z, Submodule.subset_span hz, by simp⟩
      | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
      | add z₁ z₂ _ _ h₁ h₂ =>
        obtain ⟨w₁, hw₁, e₁⟩ := h₁
        obtain ⟨w₂, hw₂, e₂⟩ := h₂
        refine ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, ?_⟩
        have : z₁ + z₂ - (w₁ + w₂) = (z₁ - w₁) + (z₂ - w₂) := by ring
        rw [this]
        exact Ideal.add_mem _ e₁ e₂
      | smul a z hz h =>
        obtain ⟨w, hw, e⟩ := h
        obtain ⟨c, hc⟩ := hres a
        have hz' : z ∈ m ^ n := by rw [← hs]; exact hz
        refine ⟨c • w, Submodule.smul_mem _ c hw, ?_⟩
        have : a • z - c • w = z * (a - algebraMap O A c) + algebraMap O A c * (z - w) := by
          rw [smul_eq_mul, Algebra.smul_def]; ring
        rw [this]
        refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ e)
        rw [pow_succ]
        exact Ideal.mul_mem_mul hz' hc
    refine ⟨N ⊔ Submodule.span O (s : Set A), hN.sup ⟨s, rfl⟩, fun x => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hx x
    rw [← hs] at hxy
    obtain ⟨w, hw, e⟩ := key _ hxy
    refine ⟨y + w, Submodule.add_mem_sup hy hw, ?_⟩
    rwa [← sub_sub]

end UpperTheory.Reformulated.B.FinitelyGeneratedModPow
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinrankOfPlace
section
theorem UpperTheory.Reformulated.B.FinrankIntEqFinrankRat.finrank_eq_of_place :
    ∀ {M V : Type} [inst : AddCommGroup M]
    [Module.Free ℤ M] [Module.Finite ℤ M] [inst_3 : AddCommGroup V] [inst_4 : _root_.Module ℚ V] (j : M →+ V),
    Function.Injective (⇑j : M → V) →
      (∀ (w : V), ∃ (m : ℕ) (u : M), m ≠ (0 : ℕ) ∧ m • w = (j : M → V) u) → Module.finrank ℤ M = Module.finrank ℚ V := by
  intro M V _ _ _ _ _ j hj hs
  classical
  let b := Module.Free.chooseBasis ℤ M
  have h1 : LinearIndependent ℤ (j.toIntLinearMap ∘ b) :=
    b.linearIndependent.map' j.toIntLinearMap (LinearMap.ker_eq_bot.mpr hj)
  have h2 : LinearIndependent ℚ (j.toIntLinearMap ∘ b) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp h1
  have key : ∀ u : M, j u ∈ Submodule.span ℚ (Set.range (j.toIntLinearMap ∘ b)) := by
    intro u
    have hu : j u = ∑ i, (b.repr u i) • j (b i) := by
      conv_lhs => rw [← b.sum_repr u]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zsmul]
    rw [hu]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
  have h3 : ⊤ ≤ Submodule.span ℚ (Set.range (j.toIntLinearMap ∘ b)) := by
    intro w _
    obtain ⟨m, u, hm, hw⟩ := hs w
    have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have : w = (m : ℚ)⁻¹ • j u := by
      rw [← hw, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hm', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (key u)
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis (Module.Basis.mk h2 h3)]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementA
section
theorem UpperTheory.Reformulated.B.FirstStatementA.main :
    ∀ {E : Type} [inst : Field E]
    [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)),
    ∀ x ∈ Submodule.span E (↑L : Set (Fin n → E)), ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ m • x ∈ L := by
  intro E _ _ n L x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨a, ha, hya⟩ := h1
    obtain ⟨b, hb, hzb⟩ := h2
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : (a * b) • (y + z) = b • (a • y) + a • (b • z) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm a b y]
    rw [e]
    exact L.add_mem (L.smul_of_tower_mem b hya) (L.smul_of_tower_mem a hzb)
  | smul c y _ h =>
    obtain ⟨a, ha, hya⟩ := h
    have halg : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨d, hd, hint⟩ := halg.exists_integral_multiple
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    let r : NumberField.RingOfIntegers E := ⟨d • c, hint⟩
    have e : (d * a) • (c • y) = r • (a • y) := by
      have : r • (a • y) = (d • c) • (a • y) := rfl
      rw [this, mul_smul, smul_comm a c y, smul_assoc]
    rw [e]
    exact L.smul_mem r hya
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementB
section
theorem UpperTheory.Reformulated.B.DoubleSumDiagonalOffDiagonal.main.{u_3} :
    ∀ {n : ℕ} {M : Type u_3} [inst : AddCommMonoid M]
    (F : Fin n → Fin n → M),
    ∑ a : Fin n, ∑ b : Fin n, F a b =
      ∑ a : Fin n, F a a + ∑ a : Fin n, ∑ b : Fin n, if a < b then F a b + F b a else (0 : M) := by
  intro n M _ F
  have h1 : ∀ a b : Fin n, F a b = (if a = b then F a b else 0) + ((if a < b then F a b else 0)
      + (if b < a then F a b else 0)) := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp
    · simp [h, h.ne', not_lt.mpr h.le]
  have hd : ∀ a : Fin n, (∑ b : Fin n, if a = b then F a b else 0) = F a a := by
    intro a
    rw [Finset.sum_ite_eq]
    simp
  have hc : (∑ a : Fin n, ∑ b : Fin n, if b < a then F a b else 0)
      = ∑ a : Fin n, ∑ b : Fin n, if a < b then F b a else 0 := by
    rw [Finset.sum_comm]
  calc ∑ a : Fin n, ∑ b : Fin n, F a b
      = ∑ a : Fin n, ∑ b : Fin n, ((if a = b then F a b else 0) + ((if a < b then F a b else 0)
      + (if b < a then F a b else 0))) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => h1 a b
    _ = ∑ a : Fin n, F a a + ((∑ a : Fin n, ∑ b : Fin n, if a < b then F a b else 0)
        + ∑ a : Fin n, ∑ b : Fin n, if b < a then F a b else 0) := by
        simp only [Finset.sum_add_distrib, hd]
    _ = _ := by
        rw [hc, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementC
section
theorem UpperTheory.Reformulated.B.OneAddPowLeTwoPowMul.main :
    ∀ (t : ℝ), (0 : ℝ) ≤ t → ∀ (N : ℕ), ((1 : ℝ) + t) ^ N ≤ (2 : ℝ) ^ N * ((1 : ℝ) + t ^ N) := by
  intro t ht N
  have h1 : (1 : ℝ) + t ≤ 2 * max 1 t := by
    linarith [le_max_left (1 : ℝ) t, le_max_right (1 : ℝ) t]
  have h2 : ((1 : ℝ) + t) ^ N ≤ (2 * max 1 t) ^ N := pow_le_pow_left₀ (by linarith) h1 N
  rw [mul_pow] at h2
  have h3 : (max (1 : ℝ) t) ^ N ≤ 1 + t ^ N := by
    rcases le_total t 1 with h | h
    · rw [max_eq_left h, one_pow]
      have : (0 : ℝ) ≤ t ^ N := pow_nonneg ht N
      linarith
    · rw [max_eq_right h]
      linarith
  calc ((1 : ℝ) + t) ^ N ≤ 2 ^ N * (max 1 t) ^ N := h2
    _ ≤ 2 ^ N * (1 + t ^ N) := mul_le_mul_of_nonneg_left h3 (by positivity)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementD
section
theorem UpperTheory.Reformulated.B.LocallyTrivialClassesAddEquiv.main :
    ∀ {R ι H C : Type} [inst : CommRing R] [inst_1 : AddCommGroup H] [inst_2 : _root_.Module R H] [inst_3 : AddCommGroup C]
      {Hv Cv : ι → Type} [inst_4 : (v : ι) → AddCommGroup (Hv v)] [inst_5 : (v : ι) → AddCommGroup (Cv v)]
      (res : (v : ι) → H →+ Hv v) (pres : (v : ι) → C →+ Cv v) (E : H ≃+ C) (Ev : (v : ι) → Hv v ≃+ Cv v),
      (∀ (v : ι) (x : H), (Ev v : Hv v → Cv v) ((res v : H → Hv v) x) = (pres v : C → Cv v) ((E : H → C) x)) →
        ∀ (U : Submodule R H) (T : AddSubgroup C),
          (∀ (x : H), x ∈ U ↔ ∀ (v : ι), (res v : H → Hv v) x = (0 : Hv v)) →
            (∀ (y : C), y ∈ T ↔ ∀ (v : ι), (pres v : C → Cv v) y = (0 : Cv v)) → Nonempty (↥U ≃+ ↥T) := by
  intro R ι H C _ _ _ _ Hv Cv _ _ res pres E Ev hcomm U T hU hT
  have key : ∀ x : H, x ∈ U ↔ E x ∈ T := by
    intro x
    rw [hU, hT]
    refine forall_congr' fun v => ?_
    rw [← hcomm v x]
    constructor
    · intro h; rw [h, map_zero]
    · intro h
      have := congrArg (Ev v).symm h
      simpa using this
  exact ⟨{ toFun := fun x => ⟨E x.1, (key x.1).1 x.2⟩
           invFun := fun y => ⟨E.symm y.1, (key _).2 (by simpa using y.2)⟩
           left_inv := fun x => by ext; simp
           right_inv := fun y => by ext; simp
           map_add' := fun x y => by ext; simp }⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementE
section
theorem UpperTheory.Reformulated.B.ProdSubProdLeOfFactorsClose.main.{u_1} :
    ∀ {ι : Type u_1} (ν : Valuation ℂ NNReal) (s : Finset ι) (f g : ι → ℂ) (m : NNReal),
      (∀ i ∈ s, (ν : ℂ → NNReal) (f i) ≤ (1 : NNReal)) →
        (∀ i ∈ s, (ν : ℂ → NNReal) (g i) ≤ (1 : NNReal)) →
          (∀ i ∈ s, (ν : ℂ → NNReal) (f i - g i) ≤ m) →
            (ν : ℂ → NNReal) (∏ i ∈ s, f i) ≤ (1 : NNReal) ∧
              (ν : ℂ → NNReal) (∏ i ∈ s, g i) ≤ (1 : NNReal) ∧ (ν : ℂ → NNReal) (∏ i ∈ s, f i - ∏ i ∈ s, g i) ≤ m := by
  classical
  intro ι ν s f g m
  induction s using Finset.induction_on with
  | empty =>
    intro _ _ _
    simp
  | insert a s ha ih =>
    intro hf hg hfg
    obtain ⟨h1, h2, h3⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    have fa := hf a (Finset.mem_insert_self a s)
    have ga := hg a (Finset.mem_insert_self a s)
    have fga := hfg a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    refine ⟨?_, ?_, ?_⟩
    · rw [map_mul]
      calc ν (f a) * ν (∏ i ∈ s, f i) ≤ 1 * 1 := mul_le_mul' fa h1
        _ = 1 := one_mul 1
    · rw [map_mul]
      calc ν (g a) * ν (∏ i ∈ s, g i) ≤ 1 * 1 := mul_le_mul' ga h2
        _ = 1 := one_mul 1
    · have e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
          = f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
      rw [e]
      refine le_trans (Valuation.map_add ν _ _) (max_le ?_ ?_)
      · rw [map_mul]
        calc ν (f a) * ν (∏ i ∈ s, f i - ∏ i ∈ s, g i) ≤ 1 * m := mul_le_mul' fa h3
          _ = m := one_mul m
      · rw [map_mul]
        calc ν (f a - g a) * ν (∏ i ∈ s, g i) ≤ m * 1 := mul_le_mul' fga h2
          _ = m := mul_one m
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FixedQuadraticMemBase
section
theorem UpperTheory.fixed_quadratic_mem_base :
    ∀ {F E : Type} [Field F] [Field E] [Algebra F E], Module.finrank F E = 2 → ∀ (σ : E →ₐ[F] E) (α : E), σ α ≠ α → ∀ x, σ x = x → x ∈ (algebraMap F E).range := by
  intro F E _ _ _ h σ α hα x hx
  by_contra hxr
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have li : LinearIndependent F ![(1 : E), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hxr
      refine ⟨-(s / t), ?_⟩
      have hst' : algebraMap F E s + algebraMap F E t * x = 0 := by
        simpa [Algebra.smul_def] using hst
      have ht' : algebraMap F E t ≠ 0 := by
        simpa using ht
      rw [map_neg, map_div₀]
      field_simp
      linear_combination -hst'
    subst ht
    simp only [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
    exact ⟨by simpa using hst, rfl⟩
  have hspan : Submodule.span F (Set.range ![(1 : E), x]) = ⊤ :=
    li.span_eq_top_of_card_eq_finrank' (by simp [h])
  have hmem : α ∈ Submodule.span F (Set.range ![(1 : E), x]) := by
    rw [hspan]; exact Submodule.mem_top
  refine hα ?_
  clear hα
  induction hmem using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    fin_cases i
    · simp
    · simpa using hx
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _), ha, hb]
  | smul c a _ ha => rw [map_smul, ha]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FixedSubgroup
section
noncomputable def UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd :
    {A H M : Type} →
      [inst : CommRing A] →
        [inst_1 : Group H] →
          [inst_2 : AddCommGroup M] → [inst_3 : _root_.Module A M] → Representation A H M → Subgroup H → Submodule A M :=
  fun {_A _H _M} _ _ _ _ ρ K =>
    { carrier := {v | ∀ k ∈ K, ρ k v = v}
      add_mem' := fun {a b} ha hb k hk => by
        rw [map_add (f := _), ha k hk, hb k hk]
      zero_mem' := fun k _ => map_zero (ρ k)
      smul_mem' := fun c v hv k hk => by
        rw [map_smul, hv k hk] }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FormalGroupCoeffMem
section
private theorem coeff_mul_mem_of_lt {R : Type} [CommRing R] (S : Subring R) (n : ℕ)
    (f g : PowerSeries R) (hf : ∀ k < n, PowerSeries.coeff k f ∈ S)
    (hg : ∀ k < n, PowerSeries.coeff k g ∈ S) :
    ∀ k < n, PowerSeries.coeff k (f * g) ∈ S := by
  intro k hk
  rw [PowerSeries.coeff_mul]
  refine S.sum_mem fun p hp => ?_
  have hp' : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  exact S.mul_mem (hf _ (by omega)) (hg _ (by omega))

private theorem coeff_mul_mem_step {R : Type} [CommRing R] (S : Subring R) (n : ℕ)
    (f g : PowerSeries R) (hf0 : PowerSeries.constantCoeff f = 0)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hf : ∀ k < n, PowerSeries.coeff k f ∈ S)
    (hg : ∀ k < n, PowerSeries.coeff k g ∈ S) :
    PowerSeries.coeff n (f * g) ∈ S := by
  rw [PowerSeries.coeff_mul]
  refine S.sum_mem fun p hp => ?_
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h1 : p.1 = 0
  · rw [h1, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, zero_mul]
    exact S.zero_mem
  by_cases h2 : p.2 = 0
  · rw [h2, PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0, mul_zero]
    exact S.zero_mem
  exact S.mul_mem (hf _ (by omega)) (hg _ (by omega))

theorem UpperTheory.formal_group_coeff_mem :
    ∀ (R : Type) [CommRing R] (S : Subring R) (a₁ a₂ a₃ a₄ a₆ : R) (w : PowerSeries R), a₁ ∈ S → a₂ ∈ S → a₃ ∈ S → a₄ ∈ S → a₆ ∈ S → PowerSeries.constantCoeff w = 0 → w = PowerSeries.X ^ 3 + PowerSeries.C a₁ * PowerSeries.X * w + PowerSeries.C a₂ * PowerSeries.X ^ 2 * w + PowerSeries.C a₃ * w ^ 2 + PowerSeries.C a₄ * PowerSeries.X * w ^ 2 + PowerSeries.C a₆ * w ^ 3 → ∀ n, PowerSeries.coeff n w ∈ S := by
  intro R _ S a₁ a₂ a₃ a₄ a₆ w h₁ h₂ h₃ h₄ h₆ h0 hw n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hX : ∀ k < n, PowerSeries.coeff k (PowerSeries.X : PowerSeries R) ∈ S := by
      intro k _
      rw [PowerSeries.coeff_X]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    have hX0 : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 :=
      PowerSeries.constantCoeff_X
    have hX3 : PowerSeries.coeff n ((PowerSeries.X : PowerSeries R) ^ 3) ∈ S := by
      rw [PowerSeries.coeff_X_pow]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    have hXw0 : PowerSeries.constantCoeff (PowerSeries.X * w) = 0 := by
      rw [map_mul, h0, mul_zero]
    have hww0 : PowerSeries.constantCoeff (w * w) = 0 := by
      rw [map_mul, h0, mul_zero]
    have hXw := coeff_mul_mem_of_lt S n _ _ hX ih
    have hww := coeff_mul_mem_of_lt S n _ _ ih ih
    have e : w = PowerSeries.X ^ 3 + PowerSeries.C a₁ * (PowerSeries.X * w)
        + PowerSeries.C a₂ * (PowerSeries.X * (PowerSeries.X * w))
        + PowerSeries.C a₃ * (w * w) + PowerSeries.C a₄ * (PowerSeries.X * (w * w))
        + PowerSeries.C a₆ * (w * (w * w)) := by
      refine hw.trans ?_
      ring
    have e' := congrArg (PowerSeries.coeff n) e
    rw [e']
    simp only [map_add (f := _), PowerSeries.coeff_C_mul]
    exact S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem hX3
      (S.mul_mem h₁ (coeff_mul_mem_step S n _ _ hX0 h0 hX ih)))
      (S.mul_mem h₂ (coeff_mul_mem_step S n _ _ hX0 hXw0 hX hXw)))
      (S.mul_mem h₃ (coeff_mul_mem_step S n _ _ h0 h0 ih ih)))
      (S.mul_mem h₄ (coeff_mul_mem_step S n _ _ hX0 hww0 hX hww)))
      (S.mul_mem h₆ (coeff_mul_mem_step S n _ _ h0 hww0 ih hww))
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FrobInPowCong
section
theorem UpperTheory.Reformulated.B.Qf16.frobIn_pow_cong :
    ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω)
    {a b : Ω},
    (A.valuation : Ω → A.ValueGroup) a ≤ (1 : A.ValueGroup) →
      (A.valuation : Ω → A.ValueGroup) b ≤ (1 : A.ValueGroup) →
        (A.valuation : Ω → A.ValueGroup) (a - b) < (1 : A.ValueGroup) →
          ∀ (m : ℕ), (A.valuation : Ω → A.ValueGroup) (a ^ m - b ^ m) < (1 : A.ValueGroup) := by
  intro Ω inst A a b ha hb hab m
  induction m with
  | zero => simp
  | succ n ih =>
    have h : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [h]
    refine A.valuation.map_add_lt ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) ih
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hb n)) hab
end

