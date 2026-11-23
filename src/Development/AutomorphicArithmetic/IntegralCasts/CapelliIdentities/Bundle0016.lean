module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExComp
section
theorem UpperTheory.Reformulated.B.Qh44.ex_comp :
    ∀ {F M Ω : Type} [inst : Field F] [NumberField F] [inst_2 : Field M]
    [NumberField M] [inst_4 : Field Ω] [inst_5 : Algebra F Ω] [Algebra.IsAlgebraic F Ω] (g : M →+* Ω),
    FiniteDimensional F ↥(IntermediateField.adjoin F (Set.range (⇑g : M → Ω))) := by
  intro F M Ω _ _ _ _ _ _ _ g
  let b := Module.finBasis ℚ M
  have h : IntermediateField.adjoin F (Set.range (⇑g : M → Ω))
      = IntermediateField.adjoin F (Set.range (fun i => g (b i))) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← b.sum_repr x, map_sum]
      refine sum_mem (fun i _ => ?_)
      rw [Rat.smul_def, map_mul, map_ratCast]
      exact mul_mem (SubfieldClass.ratCast_mem _ _)
        (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    · apply IntermediateField.adjoin.mono
      rintro _ ⟨i, rfl⟩
      exact ⟨_, rfl⟩
  rw [h]
  haveI : Finite (Set.range (fun i => g (b i))) := Set.finite_range _
  exact IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExLift
section
theorem UpperTheory.Reformulated.B.Qj6.ex_lift :
    ∀ {M Ω C : Type} [inst : Field M] [NumberField M] [inst_2 : Field Ω]
    [CharZero Ω] [IsAlgClosed Ω] [inst_5 : Field C] [CharZero C] (j : Ω →+* C) (f : M →+* C),
    ∃ (g : M →+* Ω), ∀ (x : M), (j : Ω → C) ((g : M → Ω) x) = (f : M → C) x := by
  intro M Ω C _ _ _ _ _ _ _ j f
  have key : ∀ x : M, f x ∈ j.fieldRange := by
    intro x
    have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    have hs : ((minpoly ℚ x).map (algebraMap ℚ Ω)).Splits := IsAlgClosed.splits _
    have hm : ((minpoly ℚ x).map (algebraMap ℚ Ω)).map j = (minpoly ℚ x).map (algebraMap ℚ C) := by
      rw [Polynomial.map_map]
      congr 1
      exact Subsingleton.elim _ _
    have hne : ((minpoly ℚ x).map (algebraMap ℚ Ω)).map j ≠ 0 := by
      rw [hm]
      exact ((minpoly.monic hx).map _).ne_zero
    have hr : f x ∈ (((minpoly ℚ x).map (algebraMap ℚ Ω)).map j).roots := by
      rw [Polynomial.mem_roots hne, hm, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
      have h := Polynomial.aeval_algHom_apply f.toRatAlgHom x (minpoly ℚ x)
      rw [minpoly.aeval, map_zero] at h
      exact h
    rw [hs.roots_map, Multiset.mem_map] at hr
    obtain ⟨y, -, hy⟩ := hr
    exact ⟨y, hy⟩
  choose g hg using fun x => RingHom.mem_fieldRange.mp (key x)
  refine ⟨{ toFun := g, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hg⟩
  · exact j.injective (by simp [hg])
  · intro a b
    exact j.injective (by simp [hg])
  · exact j.injective (by simp [hg])
  · intro a b
    exact j.injective (by simp [hg])
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsAnti
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh37.Lp :
    (L : Type) → [Field L] → Type :=
    fun (L : Type) [Field L] ↦ ↥(NumberField.maximalRealSubfield L)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh37.Lsq :
    (R : Type) → [CommRing R] → R → Type :=
    fun (R : Type) [CommRing R] (Δ : R) ↦ QuadraticAlgebra R Δ (0 : R)


open NumberField NumberField.IsCMField in
private theorem UpperTheory.Reformulated.B.Qh37.exists_anti (L : Type) [Field L] [NumberField L] [IsCMField L] :
    ∃ δ : L, δ ≠ 0 ∧ complexConj L δ = -δ := by
  have h : ∃ x : L, complexConj L x ≠ x := by
    by_contra h
    push Not at h
    exact complexConj_ne_one L (AlgEquiv.ext h)
  obtain ⟨x, hx⟩ := h
  refine ⟨x - complexConj L x, sub_ne_zero.mpr hx.symm, ?_⟩
  rw [map_sub, complexConj_apply_apply, neg_sub]

theorem UpperTheory.Reformulated.B.Qh37.globEx :
    ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] [inst_2 : NumberField.IsCMField L],
      ∃ (Δ : UpperTheory.Reformulated.B.Qh37.Lp L) (e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ ≃+* L),
        (∀ (x : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ),
            (e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ → L) (Star.star x) =
              (NumberField.IsCMField.complexConj L : L → L) ((e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ → L) x)) ∧
          (∀ (a : UpperTheory.Reformulated.B.Qh37.Lp L),
              (e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ → L)
                  ((Algebra.algebraMap (UpperTheory.Reformulated.B.Qh37.Lp L) (UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ) :
                      UpperTheory.Reformulated.B.Qh37.Lp L → UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ)
                    a) =
                (Algebra.algebraMap (UpperTheory.Reformulated.B.Qh37.Lp L) L : UpperTheory.Reformulated.B.Qh37.Lp L → L) a) ∧
            ∀ (σ : UpperTheory.Reformulated.B.Qh37.Lp L →+* ℝ), (σ : UpperTheory.Reformulated.B.Qh37.Lp L → ℝ) Δ < (0 : ℝ) := by
  intro L _ _ _
  obtain ⟨δ, hδ0, hδ⟩ := UpperTheory.Reformulated.B.Qh37.exists_anti L
  have hmem : δ * δ ∈ NumberField.maximalRealSubfield L := by
    rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_mul, hδ, neg_mul_neg]
  let Δ : NumberField.maximalRealSubfield L := ⟨δ * δ, hmem⟩
  have hΔ : algebraMap (NumberField.maximalRealSubfield L) L Δ = δ * δ := rfl
  let f : QuadraticAlgebra (NumberField.maximalRealSubfield L) Δ 0 →ₐ[NumberField.maximalRealSubfield L] L :=
    QuadraticAlgebra.lift ⟨δ, by rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one, hΔ]⟩
  have hω : f QuadraticAlgebra.omega = δ := by
    have := (QuadraticAlgebra.lift (R := NumberField.maximalRealSubfield L) (a := Δ) (b := 0)
      (A := L)).symm_apply_apply ⟨δ, by rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one, hΔ]⟩
    exact congrArg Subtype.val this
  have hf : ∀ x y, f ⟨x, y⟩ = algebraMap _ L x + algebraMap _ L y * δ := by
    intro x y
    rw [QuadraticAlgebra.mk_eq_add_smul_omega, map_add (f := _), map_smul, AlgHom.commutes, hω,
      Algebra.smul_def]
  have hstar : ∀ z, f (star z) = NumberField.IsCMField.complexConj L (f z) := by
    rintro ⟨x, y⟩
    rw [QuadraticAlgebra.star_mk, hf, hf, map_add (f := _), map_add (f := _), map_mul, map_mul,
      AlgEquiv.commutes, AlgEquiv.commutes, hδ, map_neg, map_zero]
    ring
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨x, y⟩ h
    have h' := hstar ⟨x, y⟩
    rw [h, map_zero, QuadraticAlgebra.star_mk, hf, map_add (f := _), map_mul, map_neg, map_zero] at h'
    rw [hf] at h
    have hx : algebraMap _ L x = 0 := by linear_combination (h + h') / 2
    have hy : algebraMap _ L y * δ = 0 := by linear_combination (h - h') / 2
    have hy' := (mul_eq_zero.mp hy).resolve_right hδ0
    rw [map_eq_zero] at hx hy'
    subst hx hy'
    rfl
  have hsurj : Function.Surjective f := by
    intro z
    have h1 : (z + NumberField.IsCMField.complexConj L z) / 2 ∈
        NumberField.maximalRealSubfield L := by
      rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_div₀, map_add (f := _), map_ofNat,
        NumberField.IsCMField.complexConj_apply_apply, add_comm]
    have h2 : (z - NumberField.IsCMField.complexConj L z) / (2 * δ) ∈
        NumberField.maximalRealSubfield L := by
      rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, map_ofNat,
        NumberField.IsCMField.complexConj_apply_apply, hδ]
      field_simp
      ring
    refine ⟨⟨⟨_, h1⟩, ⟨_, h2⟩⟩, ?_⟩
    rw [hf]
    change (z + NumberField.IsCMField.complexConj L z) / 2 +
      (z - NumberField.IsCMField.complexConj L z) / (2 * δ) * δ = z
    field_simp
    ring
  refine ⟨Δ, RingEquiv.ofBijective f.toRingHom ⟨hinj, hsurj⟩, hstar, f.commutes, fun σ ↦ ?_⟩
  let φ : L →+* ℂ := NumberField.ComplexEmbedding.lift L (Complex.ofRealHom.comp σ)
  have h1 : φ δ * φ δ = (σ Δ : ℂ) := by
    rw [← map_mul, ← hΔ]
    exact NumberField.ComplexEmbedding.lift_algebraMap_apply L (Complex.ofRealHom.comp σ) Δ
  have h2 : (starRingEnd ℂ) (φ δ) = -φ δ := by
    rw [← NumberField.IsCMField.complexEmbedding_complexConj, hδ, map_neg]
  have h3 : ((Complex.normSq (φ δ) : ℝ) : ℂ) = ((-σ Δ : ℝ) : ℂ) := by
    rw [← Complex.mul_conj, h2, mul_neg, h1, Complex.ofReal_neg]
  have h4 : 0 < Complex.normSq (φ δ) := Complex.normSq_pos.mpr ((map_ne_zero φ).mpr hδ0)
  rw [Complex.ofReal_injective h3] at h4
  exact neg_pos.mp h4
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsAverage
section
namespace UpperTheory.Reformulated.B.ExistsAverage

private theorem exists_op {K : Type*} {M : Type*} [Group K] [AddCommGroup M] [Module ℂ M]
    (ρ : K →* Module.End ℂ M) (H : Subgroup K) [H.Normal] [H.FiniteIndex] :
    ∃ A : M →ₗ[ℂ] M,
      (∀ m, (∀ h ∈ H, ρ h m = m) → ∀ k, ρ k (A m) = A m) ∧
      (∀ m, (∀ h ∈ H, ρ h m = m) → ∀ k, A (ρ k m) = A m) ∧
      (∀ m, (∀ k, ρ k m = m) → A m = m) ∧
      (∀ m, m - A m ∈ Submodule.span ℂ {x : M | ∃ k y, x = y - ρ k y}) := by
  classical
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  have hc : ((Fintype.card (K ⧸ H) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have key : ∀ m, (∀ h ∈ H, ρ h m = m) → ∀ g : K, ρ g m = ρ ((g : K ⧸ H).out) m := by
    intro m hm g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    rw [hh, map_mul, Module.End.mul_apply, hm h h.2]
  have hA : ∀ m, (((Fintype.card (K ⧸ H) : ℕ) : ℂ)⁻¹ • ∑ q : K ⧸ H, (ρ q.out : M →ₗ[ℂ] M)) m
      = ((Fintype.card (K ⧸ H) : ℕ) : ℂ)⁻¹ • ∑ q : K ⧸ H, ρ q.out m := by
    intro m
    rw [LinearMap.smul_apply, LinearMap.sum_apply]
  have hconst : ∀ m : M, ((Fintype.card (K ⧸ H) : ℕ) : ℂ)⁻¹ • ∑ _q : K ⧸ H, m = m := by
    intro m
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  refine ⟨((Fintype.card (K ⧸ H) : ℕ) : ℂ)⁻¹ • ∑ q : K ⧸ H, (ρ q.out : M →ₗ[ℂ] M),
    ?_, ?_, ?_, ?_⟩
  · intro m hm k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hA, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft (k : K ⧸ H)) _ _ fun q => ?_
    rw [← Module.End.mul_apply, ← map_mul, key m hm]
    simp
  · intro m hm k
    rw [hA, hA]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulRight (k : K ⧸ H)) _ _ fun q => ?_
    rw [← Module.End.mul_apply, ← map_mul, key m hm]
    simp
  · intro m hm
    rw [hA]
    simp only [hm]
    exact hconst m
  · intro m
    rw [hA]
    nth_rewrite 1 [← hconst m]
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    exact Submodule.smul_mem _ _
      (Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨_, _, rfl⟩)

private theorem exists_sub {K : Type*} {M : Type*} [Group K] [AddCommGroup M] [Module ℂ M]
    [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (ρ : K →* Module.End ℂ M) (hs : ∀ m : M, IsOpen {k : K | ρ k m = m}) (m : M) :
    ∃ H : Subgroup K, H.Normal ∧ H.FiniteIndex ∧ ∀ h ∈ H, ρ h m = m := by
  let S : Subgroup K :=
    { carrier := {k : K | ρ k m = m}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        nth_rewrite 1 [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  haveI : Finite (K ⧸ S) := Subgroup.quotient_finite_of_isOpen S (hs m)
  haveI : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact ⟨S.normalCore, inferInstance, inferInstance, fun h hh => S.normalCore_le hh⟩

theorem exists_avg {K : Type*} {M : Type*} [Group K] [AddCommGroup M] [Module ℂ M]
    [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (ρ : K →* Module.End ℂ M) (hs : ∀ m : M, IsOpen {k : K | ρ k m = m}) :
    ∃ P : M →ₗ[ℂ] M, (∀ (m : M) (k : K), ρ k (P m) = P m) ∧
      (∀ m : M, (∀ k : K, ρ k m = m) → P m = m) ∧
      ∀ T : M →ₗ[ℂ] M, (∀ (k : K) (m : M), T (ρ k m) = ρ k (T m)) →
        ∀ m : M, T (P m) = P (T m) := by
  set N : Submodule ℂ M := Submodule.span ℂ {x : M | ∃ k y, x = y - ρ k y} with hN
  have hdis : ∀ x ∈ N, (∀ k, ρ k x = x) → x = 0 := by
    intro x hx hfix
    have : ∃ H : Subgroup K, H.Normal ∧ H.FiniteIndex ∧ ∀ A : M →ₗ[ℂ] M,
        (∀ m, (∀ h ∈ H, ρ h m = m) → ∀ k, A (ρ k m) = A m) → A x = 0 := by
      clear hfix
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, y, rfl⟩ := hx
        obtain ⟨H, h1, h2, h3⟩ := exists_sub ρ hs y
        exact ⟨H, h1, h2, fun A hA => by rw [map_sub, hA y h3, sub_self]⟩
      | zero => exact ⟨⊤, inferInstance, inferInstance, fun A _ => map_zero A⟩
      | add x y _ _ hx hy =>
        obtain ⟨H, h1, h2, h3⟩ := hx
        obtain ⟨H', h1', h2', h3'⟩ := hy
        refine ⟨H ⊓ H', inferInstance, inferInstance, fun A hA => ?_⟩
        rw [map_add (f := _), h3 A fun m hm => hA m fun h hh => hm h hh.1,
          h3' A fun m hm => hA m fun h hh => hm h hh.2, add_zero]
      | smul c x _ hx =>
        obtain ⟨H, h1, h2, h3⟩ := hx
        exact ⟨H, h1, h2, fun A hA => by rw [map_smul, h3 A hA, smul_zero]⟩
    obtain ⟨H, h1, h2, h3⟩ := this
    obtain ⟨A, -, a2, a3, -⟩ := exists_op ρ H
    rw [← a3 x hfix]
    exact h3 A a2
  have hex : ∀ m : M, ∃ p : M, (∀ k, ρ k p = p) ∧ m - p ∈ N := by
    intro m
    obtain ⟨H, h1, h2, h3⟩ := exists_sub ρ hs m
    obtain ⟨A, a1, -, -, a4⟩ := exists_op ρ H
    exact ⟨A m, a1 m h3, a4 m⟩
  choose f hf1 hf2 using hex
  have huniq : ∀ m p : M, (∀ k, ρ k p = p) → m - p ∈ N → f m = p := by
    intro m p hp hm
    rw [← sub_eq_zero]
    refine hdis _ ?_ fun k => by rw [map_sub, hf1, hp]
    have := N.sub_mem hm (hf2 m)
    rwa [sub_sub_sub_cancel_left] at this
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, hf1, ?_, ?_⟩
  · intro x y
    refine huniq _ _ (fun k => by rw [map_add (f := _), hf1, hf1]) ?_
    rw [add_sub_add_comm]
    exact N.add_mem (hf2 x) (hf2 y)
  · intro c x
    refine huniq _ _ (fun k => by rw [map_smul, hf1]) ?_
    rw [RingHom.id_apply, ← smul_sub]
    exact N.smul_mem c (hf2 x)
  · intro m hm
    exact huniq m m hm (by rw [sub_self]; exact N.zero_mem)
  · intro T hT m
    refine (huniq (T m) (T (f m)) (fun k => by rw [← hT, hf1]) ?_).symm
    rw [← map_sub]
    have hle : N ≤ N.comap T := by
      rw [hN, Submodule.span_le]
      rintro _ ⟨k, y, rfl⟩
      exact Submodule.subset_span ⟨k, T y, by rw [map_sub, hT]⟩
    exact hle (hf2 m)

end UpperTheory.Reformulated.B.ExistsAverage
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsBasisOfPid
section
theorem UpperTheory.Reformulated.B.Qi33.aux1.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) {x y : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  intro R _ W _ _ S L x y hx hy
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨t, ht, hy⟩ := hy
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  rw [smul_add]
  refine L.add_mem ?_ ?_
  · rw [mul_comm, mul_smul]
    exact L.smul_mem t hx
  · rw [mul_smul]
    exact L.smul_mem s hy

theorem UpperTheory.Reformulated.B.Qi33.aux2.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W), ∃ s ∈ S, s • (0 : W) ∈ L := by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by simp⟩

theorem UpperTheory.Reformulated.B.Qi33.aux3.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) (r : R) {x : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → r • x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  intro R _ W _ _ S L r x hx
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem r hx

noncomputable def UpperTheory.Reformulated.B.Qi33.locS.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submonoid R → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [inst : CommRing R] {W : Type u_4} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
        (S : Submonoid R) (L : Submodule R W) ↦
      { carrier := {x : W | ∃ s ∈ S, s • x ∈ L}, add_mem' := @UpperTheory.Reformulated.B.Qi33.aux1 R inst W inst_1 inst_2 S L,
        zero_mem' := UpperTheory.Reformulated.B.Qi33.aux2 S L, smul_mem' := UpperTheory.Reformulated.B.Qi33.aux3 S L : Submodule R W }

noncomputable def UpperTheory.Reformulated.B.Qi33.localization₂.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] →
            [inst_2 : _root_.Module R W] → (p : Ideal R) → [p.IsPrime] → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [CommRing R] {W : Type u_4} [AddCommGroup W] [_root_.Module R W] (p : Ideal R) [p.IsPrime]
        (L : Submodule R W) ↦
      UpperTheory.Reformulated.B.Qi33.locS p.primeCompl L

private theorem UpperTheory.Reformulated.B.Qi33.mem_locS_iff {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W]
    [Module R W] (S : Submonoid R) (R' : Type*) [CommRing R'] [Algebra R R'] [IsLocalization S R']
    [Module R' W] [IsScalarTower R R' W] (L : Submodule R W) (x : W) :
    x ∈ UpperTheory.Reformulated.B.Qi33.locS S L ↔ x ∈ Submodule.span R' (L : Set W) := by
  rw [IsLocalization.mem_span_iff S, Submodule.span_eq]
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨s • x, hx, ⟨s, hs⟩, ?_⟩
    rw [← algebraMap_smul R' s x, smul_smul]
    have h := IsLocalization.mk'_spec R' (1 : R) (⟨s, hs⟩ : S)
    simp only [map_one] at h
    rw [h, one_smul]
  · rintro ⟨y, hy, z, rfl⟩
    refine ⟨z, z.2, ?_⟩
    rw [← algebraMap_smul R' (z : R), smul_smul]
    have h := IsLocalization.mk'_spec' R' (1 : R) z
    simp only [map_one] at h
    rw [h, one_smul]
    exact hy

private theorem UpperTheory.Reformulated.B.Qi33.exists_basis_of_pid {D K Z : Type} [CommRing D] [IsDomain D]
    [IsPrincipalIdealRing D] [Field K] [Algebra D K] [IsFractionRing D K] [AddCommGroup Z]
    [Module K Z] [Module D Z] [IsScalarTower D K Z] (M : Submodule D Z) (hM : M.FG)
    (hs : Submodule.span K (M : Set Z) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank K Z)) K Z, Submodule.span D (Set.range b) = M := by
  haveI : Module.Finite D M := Module.Finite.iff_fg.mpr hM
  haveI : Module.IsTorsionFree D Z := Module.IsTorsionFree.trans_faithfulSMul D K Z
  haveI : Module.Free D M := inferInstance
  let c := Module.finBasis D M
  let v : Fin (Module.finrank D M) → Z := fun i => (c i : Z)
  have hli : LinearIndependent D v := c.linearIndependent.map' M.subtype M.ker_subtype
  have hliK : LinearIndependent K v := (LinearIndependent.iff_fractionRing D K).mp hli
  have hsp : Submodule.span D (Set.range v) = M := by
    have h1 : Set.range v = M.subtype '' Set.range c := by
      rw [← Set.range_comp]; rfl
    rw [h1, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspK : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← Submodule.span_span_of_tower D K (Set.range v), hsp, hs]
  let b0 := Module.Basis.mk hliK hspK
  have hn : Module.finrank K Z = Module.finrank D M := by
    simpa using Module.finrank_eq_card_basis b0
  refine ⟨b0.reindex (finCongr hn.symm), ?_⟩
  rw [Module.Basis.range_reindex, Module.Basis.coe_mk, hsp]

theorem UpperTheory.Reformulated.B.Qi33.exists_loc_basis :
    ∀ {K : Type} [inst : Field K] [NumberField K] [StarRing K] {Z : Type} [inst_3 : AddCommGroup Z]
      [inst_4 : _root_.Module K Z] [inst_5 : _root_.Module (NumberField.RingOfIntegers K) Z]
      [IsScalarTower (NumberField.RingOfIntegers K) K Z] [FiniteDimensional K Z]
      (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (A : Submodule (NumberField.RingOfIntegers K) Z),
      A.FG →
        Submodule.span K (↑A : Set Z) = ⊤ →
          ∃ (b : Module.Basis (Fin (Module.finrank K Z)) K Z),
            UpperTheory.Reformulated.B.Qi33.localization₂ w.asIdeal A =
              UpperTheory.Reformulated.B.Qi33.localization₂ w.asIdeal
                (Submodule.span (NumberField.RingOfIntegers K) (Set.range (⇑b : Fin (Module.finrank K Z) → Z))) := by
  intro K _ _ _ Z _ _ _ _ _ w A hA hsp
  let D := Localization.subalgebra.ofField K w.asIdeal.primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors w.asIdeal)
  haveI hloc : IsLocalization w.asIdeal.primeCompl D :=
    Localization.subalgebra.isLocalization_ofField K _ _
  haveI : IsFractionRing D K := Localization.subalgebra.isFractionRing_ofField K _ _
  haveI : IsDiscreteValuationRing D :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (NumberField.RingOfIntegers K) w.ne_bot D
  haveI : IsScalarTower (NumberField.RingOfIntegers K) D Z :=
    IsScalarTower.of_algebraMap_smul fun r z => algebraMap_smul K r z
  have hfg : (Submodule.span D (A : Set Z)).FG := by
    obtain ⟨t, rfl⟩ := hA
    exact ⟨t, (Submodule.span_span_of_tower _ _ _).symm⟩
  obtain ⟨b, hb⟩ := UpperTheory.Reformulated.B.Qi33.exists_basis_of_pid (D := D) (K := K) _ hfg
    (by rw [Submodule.span_span_of_tower, hsp])
  refine ⟨b, ?_⟩
  ext x
  unfold UpperTheory.Reformulated.B.Qi33.localization₂
  rw [UpperTheory.Reformulated.B.Qi33.mem_locS_iff _ D, UpperTheory.Reformulated.B.Qi33.mem_locS_iff _ D,
    Submodule.span_span_of_tower, hb]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsBoundPolyMulExpAlt
section
theorem UpperTheory.Reformulated.B.Rd2.exists_bound_poly_mul_exp :
    ∀ (c : ℝ),
    (0 : ℝ) < c →
      ∀ (N : ℕ), ∃ (C : ℝ), ∀ (r : ℝ), (0 : ℝ) ≤ r → ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ))) ≤ C := by
  intro c hc N
  refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * c)), fun r hr => ?_⟩
  have h1 : (1 + r) ^ N ≤ Real.exp ((N : ℝ) * r) := by
    rw [Real.exp_nat_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ N
    linarith [Real.add_one_le_exp r]
  have h2 : (N : ℝ) * r + -(c * r ^ 2) ≤ (N : ℝ) ^ 2 / (4 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((N : ℝ) - 2 * c * r)]
  calc (1 + r) ^ N * Real.exp (-(c * r ^ 2))
      ≤ Real.exp ((N : ℝ) * r) * Real.exp (-(c * r ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((N : ℝ) * r + -(c * r ^ 2)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((N : ℝ) ^ 2 / (4 * c)) := Real.exp_le_exp.mpr h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCommonMultiple
section
theorem UpperTheory.Reformulated.B.Qm7.exists_common_multiple.{u_2} :
    ∀ {ι : Type u_2} (s : Finset ι)
    (P : ι → ℕ → Prop),
    (∀ (i : ι) (a b : ℕ), P i a → a ∣ b → P i b) →
      (∀ i ∈ s, ∃ (a : ℕ), (0 : ℕ) < a ∧ P i a) → ∃ (d : ℕ), (0 : ℕ) < d ∧ ∀ i ∈ s, P i d := by
  intro ι s P hP h
  choose! a ha using h
  exact ⟨∏ i ∈ s, a i, Finset.prod_pos fun i hi => (ha i hi).1,
    fun i hi => hP i _ _ (ha i hi).2 (Finset.dvd_prod_of_mem a hi)⟩
end

