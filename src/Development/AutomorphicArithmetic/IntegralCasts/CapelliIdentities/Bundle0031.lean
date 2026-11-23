module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraTail
section
theorem UpperTheory.Reformulated.B.Ydd5.main :
    ∀ {I : Type} (s : Finset I) (c : ℝ),
      (0 : ℝ) < c → ∀ (f : I → ℝ), (∀ (i : I), (0 : ℝ) < f i) → ∃ (ρ : ℝ), (0 : ℝ) < ρ ∧ ρ ≤ c ∧ ∀ i ∈ s, ρ ≤ f i := by
  intro I s c hc f hf
  classical
  refine Finset.induction_on s ?_ ?_
  · exact ⟨c, hc, le_rfl, by simp⟩
  · intro a t _ ih
    obtain ⟨ρ, h0, h1, h2⟩ := ih
    refine ⟨min ρ (f a), lt_min h0 (hf a), (min_le_left _ _).trans h1, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h2 i hi)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurther
section
theorem UpperTheory.Reformulated.B.DYdd7.main :
    ∀ {l : ℕ} (f : ℕ → ℚ),
      (∀ (k : ℕ), f (k + l) = f k) → ∀ (a : ℕ), ∑ k ∈ Finset.range l, f (a + k) = ∑ k ∈ Finset.range l, f k := by
  intro l f hf a
  induction a with
  | zero => simp
  | succ n ih =>
    rw [← ih]
    have h1 := Finset.sum_range_succ (fun k => f (n + k)) l
    have h2 := Finset.sum_range_succ' (fun k => f (n + k)) l
    have h3 : f (n + l) = f n := hf n
    have h4 : ∑ k ∈ Finset.range l, f (n + 1 + k) = ∑ k ∈ Finset.range l, f (n + (k + 1)) :=
      Finset.sum_congr rfl (fun k _ => by rw [add_assoc, add_comm 1 k])
    simp only [add_zero] at h2
    rw [h4]
    linarith
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherBis
section
theorem UpperTheory.Reformulated.B.Qk57.eval₂_scale.{u_1, u_2} :
    ∀ {A : Type u_1} {S : Type u_2} [inst : CommRing A] [inst_1 : CommRing S] {n : ℕ} (g : A →+* S) (x : Fin n → S)
    (w : S) {m : ℕ} {a : MvPolynomial (Fin n) A},
    a.IsHomogeneous m → MvPolynomial.eval₂ g (fun (l : Fin n) ↦ w * x l) a = w ^ m * MvPolynomial.eval₂ g x a := by
  intro A S _ _ n g x w m a h
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = m := by
    have h1 := h (MvPolynomial.mem_support_iff.mp hd)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h1
    simpa using h1
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherExtra
section
open MeasureTheory in
theorem UpperTheory.Reformulated.B.Qo7.eq_zero_of_orth :
    ∀ {K : Type} [inst : TopologicalSpace K] [CompactSpace K]
    [inst_2 : MeasurableSpace K] [BorelSpace K] (μ : MeasureTheory.Measure K) [MeasureTheory.IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (S : Set C(K, ℂ)),
    (1 : C(K, ℂ)) ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) →
        (∀ a ∈ S, Star.star a ∈ S) →
          (∀ (x y : K), x ≠ y → ∃ a ∈ S, (a : K → ℂ) x ≠ (a : K → ℂ) y) →
            ∀ (f : C(K, ℂ)), (∀ a ∈ S, ∫ (x : K), (a : K → ℂ) x * (f : K → ℂ) x ∂μ = (0 : ℂ)) → f = (0 : C(K, ℂ)) := by
  intro K _ _ _ _ μ _ _ S h1 hmul hstar hsep f hf
  have hint : ∀ g : C(K, ℂ), Integrable (fun x => g x) μ := fun g =>
    (BoundedContinuousFunction.mkOfCompact g).integrable μ
  have hint' : ∀ a : C(K, ℂ), Integrable (fun x => a x * f x) μ := fun a => hint (a * f)
  let L0 : C(K, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun a => ∫ x, a x * f x ∂μ
      map_add' := fun a b => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hint' a) (hint' b)
      map_smul' := fun c a => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul c _ }
  have hL : Continuous L0 := by
    refine (L0.mkContinuous (‖f‖ * μ.real Set.univ) fun a => ?_).continuous
    have : ‖∫ x, a x * f x ∂μ‖ ≤ (‖a‖ * ‖f‖) * μ.real Set.univ := by
      refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul]
      exact mul_le_mul (a.norm_coe_le_norm x) (f.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)
    calc ‖L0 a‖ ≤ (‖a‖ * ‖f‖) * μ.real Set.univ := this
      _ = _ := by ring
  have hspan : ∀ a ∈ StarAlgebra.adjoin ℂ S, a ∈ Submodule.span ℂ S := by
    intro a ha
    induction ha using StarAlgebra.adjoin_induction with
    | mem x hx => exact Submodule.subset_span hx
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      have h := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at h
      refine Submodule.span_mono ?_ h
      rintro _ ⟨u, hu, v, hv, rfl⟩
      exact hmul u hu v hv
    | star x _ hx =>
      clear * - hx hstar
      induction hx using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span (hstar y hy)
      | zero => simp
      | add y z _ _ hy hz => rw [star_add]; exact Submodule.add_mem _ hy hz
      | smul c y _ hy => rw [star_smul]; exact Submodule.smul_mem _ _ hy
  have hker : Submodule.span ℂ S ≤ LinearMap.ker L0 :=
    Submodule.span_le.2 fun a ha => hf a ha
  have hsp : (StarAlgebra.adjoin ℂ S).SeparatesPoints := by
    intro x y hxy
    obtain ⟨a, ha, hne⟩ := hsep x y hxy
    exact ⟨a, ⟨a, StarAlgebra.subset_adjoin ℂ S ha, rfl⟩, hne⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsp
  have hall : ∀ a : C(K, ℂ), L0 a = 0 := by
    intro a
    have ha : a ∈ closure (StarAlgebra.adjoin ℂ S : Set C(K, ℂ)) := by
      have : a ∈ (StarAlgebra.adjoin ℂ S).topologicalClosure := by
        rw [htop]; exact StarSubalgebra.mem_top
      exact this
    exact closure_minimal (t := {b | L0 b = 0}) (fun b hb => hker (hspan b hb))
      (isClosed_eq hL continuous_const) ha
  have h0 : ∫ x, ‖f x‖ ^ 2 ∂μ = 0 := by
    have h := hall (star f)
    change ∫ x, (star f) x * f x ∂μ = 0 at h
    have e : (fun x => (star f) x * f x) = fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
      funext x
      simp only [ContinuousMap.star_apply, RCLike.star_def]
      rw [Complex.conj_mul']
      push_cast
      rfl
    rw [e, integral_complex_ofReal] at h
    exact_mod_cast h
  have hc : Continuous fun x => ‖f x‖ ^ 2 := by fun_prop
  have hi : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, hc⟩).integrable μ
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hi).1 h0
  have heq := (hc.ae_eq_iff_eq μ continuous_zero).1 hae
  ext x
  simpa using congrFun heq x
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherFurther
section
theorem UpperTheory.Reformulated.B.Qo3.exists_smul_mem_of_mem_span :
    ∀ {L V : Type} [inst : Field L] [NumberField L] [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module L V] [inst_4 : _root_.Module (NumberField.RingOfIntegers L) V]
    [IsScalarTower (NumberField.RingOfIntegers L) L V] (Y : Submodule (NumberField.RingOfIntegers L) V) {S : Set V},
    (∀ x ∈ S, x ∈ Y) →
      ∀ {p : V},
        p ∈ Submodule.span L S →
          ∃ (b : NumberField.RingOfIntegers L), b ≠ (0 : NumberField.RingOfIntegers L) ∧ b • p ∈ Y := by
  intro L V _ _ _ _ _ _ Y S hS p hp
  induction hp using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hS x hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Y.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Y.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Y.smul_mem b hax
    · rw [mul_smul]; exact Y.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers L)) c
    refine ⟨a * d, mul_ne_zero ha (nonZeroDivisors.coe_ne_zero d), ?_⟩
    have h : (d : NumberField.RingOfIntegers L) • (c • x) = n • x := by
      rw [← algebraMap_smul L (d : NumberField.RingOfIntegers L), smul_smul, mul_comm, hnd,
        algebraMap_smul]
    rw [mul_smul, h, smul_comm]
    exact Y.smul_mem n hax
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherMore
section
theorem UpperTheory.Reformulated.B.Qk8.exists_place :
    ∀ {F : Type} [inst : Field F] [NumberField F] (p : ℕ),
    Nat.Prime p →
      ∃ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
        (↑p : NumberField.RingOfIntegers F) ∈ w.asIdeal := by
  intro F _ _ p hp
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hinj : Function.Injective (algebraMap ℤ (NumberField.RingOfIntegers F)) :=
    (algebraMap ℤ (NumberField.RingOfIntegers F)).injective_int
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := NumberField.RingOfIntegers F) (Ideal.span {(p : ℤ)}) ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have hx0 : x = 0 := hinj (by rw [hx, map_zero])
      rw [hx0]
      exact Ideal.zero_mem _)
  have hmem : (p : NumberField.RingOfIntegers F) ∈ Q := by
    have h : (p : ℤ) ∈ Q.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQP]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at h
    exact h
  refine ⟨⟨Q, hQ, ?_⟩, hmem⟩
  intro hbot
  rw [hbot, Ideal.mem_bot] at hmem
  exact hp.ne_zero (Nat.cast_eq_zero.mp hmem)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherSide
section
theorem UpperTheory.Reformulated.B.Rc5.exists_reps :
    ∀ {α : Type} (r : α → α → Prop),
    (∀ (a b : α), r a b → r b a) →
      (∀ (a b c : α), r a b → r b c → r a c) →
        ∀ (t : Finset α), ∃ C ⊆ t, (∀ a ∈ C, ∀ b ∈ C, r a b → a = b) ∧ ∀ x ∈ t, x ∈ C ∨ ∃ c ∈ C, r x c := by
  intro α r hs _ t
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  | insert y s _ ih =>
    obtain ⟨C, hC, h1, h2⟩ := ih
    by_cases h : ∃ c ∈ C, r y c
    · refine ⟨C, hC.trans (Finset.subset_insert _ _), h1, ?_⟩
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Or.inr h
      · exact h2 x hx
    · refine ⟨insert y C, Finset.insert_subset_insert _ hC, ?_, ?_⟩
      · intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with ha | ha
        · rcases Finset.mem_insert.1 hb with hb | hb
          · rw [ha, hb]
          · exact absurd ⟨b, hb, ha ▸ hab⟩ h
        · rcases Finset.mem_insert.1 hb with hb | hb
          · exact absurd ⟨a, ha, hb ▸ hs a b hab⟩ h
          · exact h1 a ha b hb hab
      · intro x hx
        rcases Finset.mem_insert.1 hx with hx | hx
        · exact Or.inl (Finset.mem_insert.2 (Or.inl hx))
        · rcases h2 x hx with h3 | ⟨c, hc, h3⟩
          · exact Or.inl (Finset.mem_insert_of_mem h3)
          · exact Or.inr ⟨c, Finset.mem_insert_of_mem hc, h3⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherTer
section
theorem UpperTheory.Reformulated.B.Qk64.diag_mul :
    ∀ {n : ℕ} {Q : Type} [inst : CommRing Q]
    (a b : Matrix (Fin n) (Fin n) Q),
    (∀ (i j : Fin n), i < j → a i j = (0 : Q)) →
      (∀ (i j : Fin n), i < j → b i j = (0 : Q)) → ∀ (i : Fin n), (a * b) i i = a i i * b i i := by
  intro n Q _ a b ha hb i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hb j i h, mul_zero]
  · rw [ha i j h, zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsLast
section
theorem UpperTheory.Reformulated.B.DYhb1.main :
    ∀ (A M : Type) [inst : CommRing A] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module A M] [Module.Finite A M]
      [Module.Projective A M],
      ∃ (n : ℕ) (e : Fin n → M) (f : Fin n → Module.Dual A M), ∀ (m : M), ∑ i : Fin n, (f i : M → A) m • e i = m := by
  intro A M _ _ _ _ _
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' A M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p LinearMap.id hp
  refine ⟨n, fun i => p (fun j => if i = j then 1 else 0),
    fun i => (LinearMap.proj i).comp s, fun m => ?_⟩
  have h1 : p (s m) = m := by
    have := LinearMap.congr_fun hs m
    simpa using this
  have h2 := LinearMap.pi_apply_eq_sum_univ p (s m)
  rw [h1] at h2
  exact h2.symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMore
section
theorem UpperTheory.Reformulated.B.DYdc6.main :
    ∀ {X : ℕ → Type} [∀ (n : ℕ), Finite (X n)] [∀ (n : ℕ), Nonempty (X n)] (f : (n : ℕ) → X (n + (1 : ℕ)) → X n),
      ∃ (x : (n : ℕ) → X n), ∀ (n : ℕ), f n (x (n + (1 : ℕ))) = x n := by
  intro X _ _ f
  let F : CategoryTheory.Functor ℕᵒᵖ Type :=
    CategoryTheory.Functor.ofOpSequence (X := X) (fun n => TypeCat.ofHom (f n))
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => inferInstanceAs (Finite (X j.unop))
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => inferInstanceAs (Nonempty (X j.unop))
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun n => s (Opposite.op n), fun n => ?_⟩
  have h := hs (CategoryTheory.homOfLE (Nat.le_add_right n 1)).op
  rw [CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreFurther
section
theorem UpperTheory.Reformulated.B.Qh12.ell :
    ∀ (O Λ Γ X : Type) [inst : CommRing O] [inst_1 : CommRing Λ] [inst_2 : Algebra O Λ]
    [inst_3 : CommGroup Γ] [inst_4 : AddCommGroup X] [inst_5 : _root_.Module O X] (th₀ : Λ →ₐ[O] O) (d : Λ →ₗ[O] X)
    (χ : Γ →* Multiplicative X),
    (∀ (a b : Λ), (d : Λ → X) (a * b) = (th₀ : Λ → O) a • (d : Λ → X) b + (th₀ : Λ → O) b • (d : Λ → X) a) →
      ∃ (th : MonoidAlgebra Λ Γ →ₐ[O] O) (ell : MonoidAlgebra Λ Γ →ₗ[O] X),
        (∀ (g : Γ) (a : Λ), (th : MonoidAlgebra Λ Γ → O) (MonoidAlgebra.single g a) = (th₀ : Λ → O) a) ∧
          (∀ (a b : MonoidAlgebra Λ Γ),
              (ell : MonoidAlgebra Λ Γ → X) (a * b) =
                (th : MonoidAlgebra Λ Γ → O) a • (ell : MonoidAlgebra Λ Γ → X) b +
                  (th : MonoidAlgebra Λ Γ → O) b • (ell : MonoidAlgebra Λ Γ → X) a) ∧
            ∀ (g : Γ) (a : Λ),
              (ell : MonoidAlgebra Λ Γ → X) (MonoidAlgebra.single g a) =
                (d : Λ → X) a +
                  (th₀ : Λ → O) a • (Multiplicative.toAdd : Multiplicative X → X) ((χ : Γ → Multiplicative X) g) := by
  intro O Λ Γ X _ _ _ _ _ _ th₀ d χ hd
  classical
  let th : MonoidAlgebra Λ Γ →ₐ[O] O :=
    MonoidAlgebra.liftNCAlgHom th₀ (1 : Γ →* O) (fun _ _ => Commute.all _ _)
  have hth : ∀ (g : Γ) (a : Λ), th (MonoidAlgebra.single g a) = th₀ a := by
    intro g a
    simp [th]
  let ell : MonoidAlgebra Λ Γ →ₗ[O] X :=
    (Finsupp.lsum O (fun g : Γ => d + th₀.toLinearMap.smulRight (Multiplicative.toAdd (χ g)))) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv O).toLinearMap
  have hell : ∀ (g : Γ) (a : Λ), ell (MonoidAlgebra.single g a)
      = d a + th₀ a • Multiplicative.toAdd (χ g) := by
    intro g a
    simp [ell]
  refine ⟨th, ell, hth, ?_, hell⟩
  intro a b
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' =>
    simp only [add_mul, map_add (f := _), ha, ha', add_smul, smul_add]
    abel
  | single g a =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' hb hb' =>
      simp only [mul_add, map_add (f := _), hb, hb', add_smul, smul_add]
      abel
    | single h b =>
      rw [MonoidAlgebra.single_mul_single, hell, hell, hell, hth, hth, hd, map_mul, map_mul,
        toAdd_mul]
      module
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreLast
section
theorem UpperTheory.Reformulated.B.Qk10.exists_w :
    ∀ (K : Type) [inst : Field K] [NumberField K] {p : ℕ},
    Nat.Prime p →
      ∃ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (↑p : NumberField.RingOfIntegers K) ∈ w.asIdeal := by
  intro K _ _ p hp
  have hnu : ¬ IsUnit (p : NumberField.RingOfIntegers K) := by
    intro h
    have h1 : IsUnit (algebraMap ℤ (NumberField.RingOfIntegers K) (p : ℤ)) := by
      simpa using h
    have h2 : IsUnit (p : ℤ) := (isUnit_map_iff _ _).mp h1
    exact (Nat.prime_iff_prime_int.mp hp).not_unit h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal
    (Ideal.span {(p : NumberField.RingOfIntegers K)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : (p : NumberField.RingOfIntegers K) ∈ M :=
    hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  rw [Ideal.mem_bot] at hmem
  exact hp.ne_zero (Nat.cast_eq_zero.mp hmem)
end

