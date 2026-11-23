module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsRootOfAdicComplete
section
open Polynomial

namespace UpperTheory.Reformulated.B.AdicCompleteRootExistence

private lemma exists_root_of_adicComplete {R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.eval a = 0 ∧ a - a₀ ∈ I := by
  classical
  obtain ⟨f', hf'⟩ : ∃ f' : R[X], f' = derivative f := ⟨_, rfl⟩
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℕ → R, c 0 = a₀ ∧
      ∀ n, c (n + 1) = c n - f.eval (c n) * Ring.inverse (f'.eval (c n)) :=
    ⟨fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * Ring.inverse (f'.eval b), rfl,
      fun _ => rfl⟩
  rw [← hf'] at h₂
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rw [hc0]
    | succ n ih =>
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert! h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [hc0, zero_add, pow_one] using h₁
    | succ n ih =>
      obtain ⟨q, hq⟩ := Polynomial.binomExpansion f (c n)
        (-(f.eval (c n) * Ring.inverse (f'.eval (c n))))
      rw [hc, sub_eq_add_neg, hq]
      have hcancel : f'.eval (c n) * Ring.inverse (f'.eval (c n)) = 1 :=
        Ring.mul_inverse_cancel _ (hf'c n)
      have hz : eval (c n) f + eval (c n) (derivative f) *
          (-(f.eval (c n) * Ring.inverse (f'.eval (c n)))) = 0 := by
        rw [← hf']
        linear_combination (-(f.eval (c n))) * hcancel
      rw [hz, zero_add]
      have hle : I ^ (2 * (n + 1)) ≤ I ^ (n + 1 + 1) :=
        Ideal.pow_le_pow_right (by omega)
      refine Ideal.mul_mem_left _ _ (hle ?_)
      rw [pow_mul']
      exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih =>
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [add_assoc]
      exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · specialize ha (0 + 1)
    rw [hc, hc0, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁

private lemma root_of_local {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {ϖ : R}
    (hϖ : ϖ ∈ IsLocalRing.maximalIdeal R) (f : R[X]) (a : R) (k : ℕ) (ε : Rˣ)
    (h1 : f.derivative.eval a = ϖ ^ k * ε) (h2 : ϖ ^ (2 * k + 1) ∣ f.eval a) :
    ∃ b : R, f.eval b = 0 ∧ ϖ ^ (k + 1) ∣ b - a := by
  obtain ⟨c, hc⟩ := h2
  obtain ⟨q, hq⟩ := Polynomial.binomExpansion (f.map C) (C a) (C (ϖ ^ (k + 1)) * X)
  have hcomp : eval (C a + C (ϖ ^ (k + 1)) * X) (f.map C) =
      f.comp (C a + C (ϖ ^ (k + 1)) * X) := by
    rw [eval_map]; rfl
  rw [hcomp, eval_map_apply, derivative_map, eval_map_apply, h1, hc] at hq
  let g : R[X] := C c + C (ε : R) * X + C ϖ * q * X ^ 2
  have hgy : ∀ y, g.eval y = c + ε * y + ϖ * (q.eval y * y ^ 2) := by
    intro y; simp only [g, eval_add, eval_mul, eval_C, eval_X, eval_pow]; ring
  have hg'y : ∀ y, g.derivative.eval y =
      ε + ϖ * (q.derivative.eval y * y ^ 2 + q.eval y * (2 * y)) := by
    intro y
    simp only [g, derivative_add, derivative_mul, derivative_C, derivative_X, derivative_X_pow,
      eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_zero, eval_one, map_natCast, eval_natCast]
    norm_num
    ring
  set y₀ : R := -((ε⁻¹ : Rˣ) : R) * c with hy₀
  have hεy : (ε : R) * y₀ = -c := by
    rw [hy₀, ← mul_assoc, mul_neg, Units.mul_inv]; ring
  have hroot₀ : g.eval y₀ ∈ IsLocalRing.maximalIdeal R := by
    rw [hgy, add_assoc, ← add_assoc c, hεy, add_neg_cancel, zero_add]
    exact Ideal.mul_mem_right _ _ hϖ
  have hunit : IsUnit (g.derivative.eval y₀) := by
    rw [hg'y]
    by_contra hn
    have hm := (IsLocalRing.mem_maximalIdeal _).2 hn
    have hε : (ε : R) ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ hm (Ideal.mul_mem_right
        (q.derivative.eval y₀ * y₀ ^ 2 + q.eval y₀ * (2 * y₀)) _ hϖ)
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _).1 hε ε.isUnit
  obtain ⟨y, hy, -⟩ := exists_root_of_adicComplete (IsLocalRing.maximalIdeal R) g y₀ hroot₀
    (hunit.map _)
  refine ⟨a + ϖ ^ (k + 1) * y, ?_, ⟨y, by ring⟩⟩
  have hev := congrArg (eval y) hq
  simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_pow] at hev
  rw [hev]
  have : ϖ ^ (2 * k + 1) * g.eval y = 0 := by rw [hy, mul_zero]
  rw [hgy] at this
  linear_combination this

end UpperTheory.Reformulated.B.AdicCompleteRootExistence

theorem UpperTheory.Reformulated.B.AdicCompleteRootExistence.exists_root_of_dvd.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K] [IsNonarchimedeanLocalField K]
      {ϖ : ↥(ValuativeRel.valuation K).integer},
      Irreducible ϖ →
        ∀ (f : Polynomial ↥(ValuativeRel.valuation K).integer) (a : ↥(ValuativeRel.valuation K).integer) (k : ℕ)
          (ε : (↥(ValuativeRel.valuation K).integer)ˣ),
          Polynomial.eval a
                ((Polynomial.derivative :
                    Polynomial ↥(ValuativeRel.valuation K).integer → Polynomial ↥(ValuativeRel.valuation K).integer)
                  f) =
              ϖ ^ k * (↑ε : ↥(ValuativeRel.valuation K).integer) →
            ϖ ^ ((2 : ℕ) * k + (1 : ℕ)) ∣ Polynomial.eval a f →
              ∃ (b : ↥(ValuativeRel.valuation K).integer),
                Polynomial.eval b f = (0 : ↥(ValuativeRel.valuation K).integer) ∧ ϖ ^ (k + (1 : ℕ)) ∣ b - a := by
  intro K _ _ _ _ ϖ hϖ f a k ε h1 h2
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact UpperTheory.Reformulated.B.AdicCompleteRootExistence.root_of_local
    ((IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit) f a k ε h1 h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSemi
section
theorem UpperTheory.Reformulated.B.Ra9.exists_semi :
    ∀ {A K : Type} [inst : CommRing A]
    [inst_1 : Field K] (M : Type) [inst_2 : AddCommGroup M] [inst_3 : _root_.Module A M] [inst_4 : Algebra A K]
    [Module.Free A M] {C W : Type} [inst_6 : Field C] [inst_7 : AddCommGroup W] [inst_8 : _root_.Module C W] (ι : K ≃+* C)
    (sp : M →+ W),
    (∀ (a : A) (m : M), (sp : M → W) (a • m) = (ι : K → C) ((Algebra.algebraMap A K : A → K) a) • (sp : M → W) m) →
      (∀ (κ : Type) (b : Module.Basis κ A M), LinearIndependent C fun (i : κ) ↦ (sp : M → W) ((b : κ → M) i)) →
        ∃ (Ψ : TensorProduct A K M →+ W),
          (∀ (k : K) (m : M), (Ψ : TensorProduct A K M → W) (k ⊗ₜ[A] m) = (ι : K → C) k • (sp : M → W) m) ∧
            (∀ (k : K) (v : TensorProduct A K M),
                (Ψ : TensorProduct A K M → W) (k • v) = (ι : K → C) k • (Ψ : TensorProduct A K M → W) v) ∧
              Function.Injective (⇑Ψ : TensorProduct A K M → W) ∧
                ∀ (w : W),
                  w ∈ Submodule.span C (Set.range (⇑sp : M → W)) ↔
                    ∃ (v : TensorProduct A K M), (Ψ : TensorProduct A K M → W) v = w := by
  intro A K _ _ M _ _ _ _ C W _ _ _ ι sp hsp hli
  classical
  let f : K →+ M →+ W :=
    { toFun := fun k =>
        { toFun := fun m => ι k • sp m
          map_zero' := by simp
          map_add' := by intro x y; simp [smul_add] }
      map_zero' := by ext m; simp
      map_add' := by intro x y; ext m; simp [add_smul] }
  have hfa : ∀ (k : K) (m : M), f k m = ι k • sp m := fun _ _ => rfl
  have hf : ∀ (r : A) (k : K) (m : M), f (r • k) m = f k (r • m) := by
    intro r k m
    have h := hsp r m
    rw [hfa, hfa, h, Algebra.smul_def, map_mul, mul_smul, smul_comm]
  let Ψ : TensorProduct A K M →+ W := TensorProduct.liftAddHom f hf
  have hΨ : ∀ (k : K) (m : M), Ψ (k ⊗ₜ[A] m) = ι k • sp m := fun k m => by
    simp only [Ψ, TensorProduct.liftAddHom_tmul, hfa]
  have hsemi : ∀ (k : K) (v : TensorProduct A K M), Ψ (k • v) = ι k • Ψ v := by
    intro k v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x m => rw [TensorProduct.smul_tmul', hΨ, hΨ, smul_eq_mul, map_mul, mul_smul]
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  refine ⟨Ψ, hΨ, hsemi, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero Ψ).2 ?_
    intro v hv
    let b := Module.Free.chooseBasis A M
    let bK := Algebra.TensorProduct.basis K b
    have hsum : Ψ v = Finsupp.linearCombination C (fun i => sp (b i))
        ((bK.repr v).mapRange ι (map_zero ι)) := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
      conv_lhs => rw [← bK.linearCombination_repr v]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsemi, Algebra.TensorProduct.basis_apply, hΨ, map_one, one_smul]
    have hl := (linearIndependent_iff.1 (hli _ b)) _ (hsum.symm.trans hv)
    have hr : bK.repr v = 0 := by
      ext i
      have h := DFunLike.congr_fun hl i
      simpa using h
    simpa using hr
  · intro w
    constructor
    · intro hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, rfl⟩ := hx
        exact ⟨1 ⊗ₜ[A] m, by rw [hΨ, map_one, one_smul]⟩
      | zero => exact ⟨0, map_zero Ψ⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨c, rfl⟩ := hy
        exact ⟨a + c, map_add Ψ a c⟩
      | smul c x _ hx =>
        obtain ⟨v, rfl⟩ := hx
        exact ⟨ι.symm c • v, by rw [hsemi, RingEquiv.apply_symm_apply]⟩
    · rintro ⟨v, rfl⟩
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul k m =>
        rw [hΨ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
      | add x y hx hy =>
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hx hy
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSmoothExtensionNear
section
theorem UpperTheory.exists_smooth_extension_near :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {m : ℕ∞} {U : Set E},
      IsOpen U → ∀ {F : E → V}, ContDiffOn ℝ (m : WithTop ℕ∞) F U → ∀ {x : E}, x ∈ U →
        ∃ G : E → V, ContDiff ℝ (m : WithTop ℕ∞) G ∧ G =ᶠ[nhds x] F := by
  intro E _ _ _ V _ _ m U hU F hF x hx
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  let b : ContDiffBump x := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have hsub : tsupport (b : E → ℝ) ⊆ U := by
    rw [b.tsupport_eq]
    exact hball
  refine ⟨fun y => b y • F y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact (b.contDiff (n := m)).contDiffAt.smul (hF.contDiffAt (hU.mem_nhds hy))
    · have h0 : (b : E → ℝ) =ᶠ[nhds y] 0 :=
        notMem_tsupport_iff_eventuallyEq.1 fun h => hy (hsub h)
      have h1 : (fun z => b z • F z) =ᶠ[nhds y] fun _ => (0 : V) := by
        filter_upwards [h0] with z hz
        simp [hz]
      exact contDiffAt_const.congr_of_eventuallyEq h1
  · filter_upwards [b.eventuallyEq_one] with z hz
    simp [hz]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSpanModSq
section
theorem UpperTheory.Reformulated.B.Ra7.exists_span_mod_sq :
    ∀ {O R K : Type} [inst : CommRing O]
    [inst_1 : CommRing R] [inst_2 : Algebra O R] [IsNoetherianRing R] [inst_4 : CommRing K] [inst_5 : Algebra O K]
    (y : R →ₐ[O] K),
    Module.Finite O ↥y.range →
      ∃ (s : Finset R), ∀ (a : R), ∃ b ∈ Submodule.span O (↑s : Set R), a - b ∈ RingHom.ker y ^ (2 : ℕ) := by
  intro O R K _ _ _ _ _ _ y hfin
  classical
  obtain ⟨t', ht'⟩ := hfin.fg_top
  have hsurj : Function.Surjective y.rangeRestrict := y.rangeRestrict_surjective
  obtain ⟨σ, hσ⟩ := hsurj.hasRightInverse
  obtain ⟨g, hg⟩ : (RingHom.ker y).FG := IsNoetherian.noetherian _
  let t : Finset R := t'.image σ
  have h1 : ∀ a : R, ∃ b ∈ Submodule.span O (↑t : Set R), a - b ∈ RingHom.ker y := by
    intro a
    have hm : Submodule.map y.rangeRestrict.toLinearMap (Submodule.span O (↑t : Set R)) = ⊤ := by
      rw [Submodule.map_span, eq_top_iff, ← ht']
      apply Submodule.span_mono
      intro z hz
      exact ⟨σ z, Finset.mem_coe.2 (Finset.mem_image_of_mem σ hz), hσ z⟩
    have hz : y.rangeRestrict a ∈
        Submodule.map y.rangeRestrict.toLinearMap (Submodule.span O (↑t : Set R)) := by
      rw [hm]; exact Submodule.mem_top
    obtain ⟨b, hb, hab⟩ := hz
    refine ⟨b, hb, ?_⟩
    have hab' : y b = y a := congrArg Subtype.val hab
    rw [RingHom.mem_ker, map_sub, hab', sub_self]
  let s : Finset R := t ∪ Finset.image₂ (· * ·) t g
  have h2 : ∀ x ∈ g, ∀ b ∈ Submodule.span O (↑t : Set R),
      b * x ∈ Submodule.span O (↑s : Set R) := by
    intro x hx b hb
    induction hb using Submodule.span_induction with
    | mem z hz =>
      exact Submodule.subset_span (Finset.mem_coe.2
        (Finset.mem_union_right _ (Finset.mem_image₂_of_mem hz hx)))
    | zero => rw [zero_mul]; exact zero_mem _
    | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
    | smul c u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hu
  have h3 : ∀ x ∈ Ideal.span (↑g : Set R), ∀ r : R,
      ∃ b ∈ Submodule.span O (↑s : Set R), r * x - b ∈ RingHom.ker y ^ (2 : ℕ) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      intro r
      obtain ⟨b, hb, hrb⟩ := h1 r
      refine ⟨b * z, h2 z hz b hb, ?_⟩
      have hzI : z ∈ RingHom.ker y := by
        rw [← hg]; exact Ideal.subset_span hz
      rw [← sub_mul, pow_two]
      exact Ideal.mul_mem_mul hrb hzI
    | zero => intro r; exact ⟨0, zero_mem _, by rw [mul_zero, sub_zero]; exact zero_mem _⟩
    | add u v _ _ hu hv =>
      intro r
      obtain ⟨b, hb, hb'⟩ := hu r
      obtain ⟨c, hc, hc'⟩ := hv r
      refine ⟨b + c, add_mem hb hc, ?_⟩
      have e : r * (u + v) - (b + c) = (r * u - b) + (r * v - c) := by ring
      rw [e]; exact add_mem hb' hc'
    | smul c u _ hu =>
      intro r
      rw [smul_eq_mul, ← mul_assoc]
      exact hu (r * c)
  refine ⟨s, fun a => ?_⟩
  obtain ⟨b, hb, hab⟩ := h1 a
  obtain ⟨c, hc, hc'⟩ := h3 (a - b) (by rw [hg]; exact hab) 1
  refine ⟨b + c, add_mem (Submodule.span_mono ?_ hb) hc, ?_⟩
  · exact Finset.coe_subset.2 Finset.subset_union_left
  · have e : a - (b + c) = 1 * (a - b) - c := by ring
    rw [e]; exact hc'
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSum
section
theorem UpperTheory.Reformulated.B.Qg3.exists_sum.{u_1} :
    ∀ {G : Type u_1} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [MeasureTheory.IsFiniteMeasureOnCompacts μ] (K : Subgroup G),
    IsOpen (↑K : Set G) →
      IsCompact (↑K : Set G) →
        ∀ {S : Set G},
          IsCompact S →
            ∃ (T : Finset (G ⧸ K)) (r : G ⧸ K → G) (c : G ⧸ K → ℂ),
              ∀ (F : G → ℂ),
                (∀ (g k : G), k ∈ K → F (g * k) = F g) →
                  (∀ g ∉ S, F g = (0 : ℂ)) → ∫ (g : G), F g ∂μ = ∑ x ∈ T, c x * F (r x) := by
  intro G _ _ _ _ _ μ _ K hKo hKc S hS
  classical
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have hcont : Continuous (QuotientGroup.mk : G → G ⧸ K) := QuotientGroup.continuous_mk
  have hfin : ((QuotientGroup.mk : G → G ⧸ K) '' S).Finite :=
    (hS.image hcont).finite_of_discrete
  let C : G ⧸ K → Set G := fun x => (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {x}
  have hmem : ∀ (x : G ⧸ K) (g : G), g ∈ C x ↔ (x.out)⁻¹ * g ∈ K := by
    intro x g
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  have hmeas : ∀ x, MeasurableSet (C x) := fun x =>
    ((isOpen_discrete {x}).preimage hcont).measurableSet
  have hcomp : ∀ x, IsCompact (C x) := by
    intro x
    have h : C x = (fun k => x.out * k) '' (K : Set G) := by
      ext g
      rw [hmem]
      constructor
      · intro h
        exact ⟨_, h, by simp⟩
      · rintro ⟨k, hk, rfl⟩
        simpa using hk
    rw [h]
    exact hKc.image (continuous_const.mul continuous_id)
  refine ⟨hfin.toFinset, fun x => x.out, fun x => (μ.real (C x) : ℂ), ?_⟩
  intro F hF h0
  have hout : ∀ g : G, F (QuotientGroup.mk g : G ⧸ K).out = F g := by
    intro g
    have h := hF (QuotientGroup.mk g : G ⧸ K).out _ ((hmem _ g).1 rfl)
    rw [mul_inv_cancel_left] at h
    exact h.symm
  have hdec : ∀ g, F g = ∑ x ∈ hfin.toFinset, (C x).indicator (fun _ => F x.out) g := by
    intro g
    rw [Finset.sum_eq_single (QuotientGroup.mk g : G ⧸ K)]
    · rw [Set.indicator_of_mem (show g ∈ C (QuotientGroup.mk g) from rfl), hout]
    · intro x _ hx
      have hg : g ∉ C x := fun h => hx (Eq.symm h)
      rw [Set.indicator_of_notMem hg]
    · intro hg
      rw [Set.indicator_of_mem (show g ∈ C (QuotientGroup.mk g) from rfl), hout]
      exact h0 g fun hgS => hg (hfin.mem_toFinset.2 ⟨g, hgS, rfl⟩)
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hdec),
    MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [MeasureTheory.integral_indicator_const _ (hmeas x), Complex.real_smul]
  · intro x _
    rw [MeasureTheory.integrable_indicator_iff (hmeas x)]
    exact MeasureTheory.integrableOn_const (hcomp x).measure_lt_top.ne
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSumTmul
section
theorem UpperTheory.Reformulated.B.Qj2.exists_sum_tmul :
    ∀ {R O B σ : Type} [inst : CommRing R]
    [inst_1 : AddCommGroup O] [inst_2 : _root_.Module R O] [inst_3 : AddCommGroup B] [inst_4 : _root_.Module R B]
    [inst_5 : Fintype σ] (ω : Module.Basis σ R O) (x : TensorProduct R O B),
    ∃ (y : σ → B), x = ∑ s : σ, (ω : σ → O) s ⊗ₜ[R] y s := by
  intro R O B σ _ _ _ _ _ _ ω x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul o b =>
    refine ⟨fun s => ω.repr o s • b, ?_⟩
    conv_lhs => rw [← ω.sum_repr o]
    rw [TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun s _ => TensorProduct.smul_tmul _ _ _
  | add x₁ x₂ h₁ h₂ =>
    obtain ⟨y₁, rfl⟩ := h₁
    obtain ⟨y₂, rfl⟩ := h₂
    refine ⟨y₁ + y₂, ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => (TensorProduct.tmul_add _ _ _).symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSupported
section
theorem UpperTheory.Reformulated.B.Qo8.exists_supported :
    ∀ {F : Type} [inst : Field F] [NumberField F]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
    ∃ (π : NumberField.RingOfIntegers F),
      π ≠ (0 : NumberField.RingOfIntegers F) ∧
        π ∈ p.asIdeal ∧
          ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), v ≠ p → π ∉ v.asIdeal := by
  intro F _ _ p
  have hp : p.asIdeal ∈ nonZeroDivisors (Ideal (NumberField.RingOfIntegers F)) :=
    mem_nonZeroDivisors_of_ne_zero p.ne_bot
  obtain ⟨n, hn, hpow⟩ :=
    (isOfFinOrder_of_finite (ClassGroup.mk0 ⟨p.asIdeal, hp⟩)).exists_pow_eq_one
  rw [← map_pow] at hpow
  have hprin : (p.asIdeal ^ n).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff (pow_mem hp n)).1 hpow
  obtain ⟨π, hπ⟩ := hprin
  have hπ' : p.asIdeal ^ n = Ideal.span {π} := hπ
  have hmem : π ∈ p.asIdeal ^ n := hπ' ▸ Ideal.mem_span_singleton_self π
  refine ⟨π, ?_, Ideal.pow_le_self hn.ne' hmem, ?_⟩
  · rintro rfl
    rw [Ideal.span_singleton_zero] at hπ'
    exact pow_ne_zero n p.ne_bot hπ'
  · intro v hv hπv
    have hle : p.asIdeal ^ n ≤ v.asIdeal := by
      rw [hπ', Ideal.span_le, Set.singleton_subset_iff]
      exact hπv
    have hle' : p.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le hle
    exact hv (IsDedekindDomain.HeightOneSpectrum.ext
      (p.isMaximal.eq_of_le v.isPrime.ne_top hle').symm)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FrobeniusElementAlt
section
noncomputable def UpperTheory.Reformulated.B.FrobeniusElementAlt.frb :
    {l : ℕ} → [Fact (Nat.Prime l)] → {B : Type} → [inst : CommRing B] → (↑l : B) = (0 : B) → B →+* B :=
  fun {l} hl {B} _ h =>
    { toFun := fun x => x ^ l
      map_one' := one_pow l
      map_mul' := fun x y => mul_pow x y l
      map_zero' := zero_pow hl.out.ne_zero
      map_add' := fun x y => by
        rw [add_pow_prime_eq hl.out x y, h]
        simp }
end

