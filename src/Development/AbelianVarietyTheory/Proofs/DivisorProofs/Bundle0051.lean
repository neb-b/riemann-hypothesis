module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatSurjectiveClosedSubschemeOfOpenCover
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_isPullback_of_factor_iff {C : Type*} [Category C] {X X' A B : C} (m : X' ⟶ X)
    (b : B ⟶ X) (a : A ⟶ X') [Mono a] [Mono b]
    (h : ∀ (Y : C) (g : Y ⟶ X'), (∃ z : Y ⟶ B, z ≫ b = g ≫ m) ↔ (∃ z : Y ⟶ A, z ≫ a = g)) :
    ∃ k : A ⟶ B, IsPullback k a b m := by
  obtain ⟨k, hk⟩ := (h A a).2 ⟨𝟙 A, Category.id_comp a⟩
  refine ⟨k, ⟨hk⟩, ⟨PullbackCone.IsLimit.mk hk
    (fun s => ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose) ?_ ?_ ?_⟩⟩
  · intro s
    have hs := ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose_spec
    rw [← cancel_mono b, Category.assoc, hk, ← Category.assoc, hs, s.condition]
  · intro s
    exact ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose_spec
  · intro s l _ hl
    have hs := ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose_spec
    rw [← cancel_mono a, hl, hs]

theorem of_isPullback_openCover (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    {B T : Scheme.{0}} (f : B ⟶ T) {ι : Type} (V : ι → T.Opens) (hV : iSup V = ⊤)
    (A : ι → Scheme.{0}) (k : ∀ i, A i ⟶ B) (g : ∀ i, A i ⟶ (V i).toScheme)
    (h : ∀ i, IsPullback (k i) (g i) f (V i).ι) (hg : ∀ i, P (g i)) : P f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) V hV]
  intro i
  have h' := (isPullback_morphismRestrict f (V i)).flip
  have e : (h'.isoIsPullback _ _ (h i)).hom ≫ g i = f ∣_ V i := by simp
  rw [← e]
  exact (P.cancel_left_of_respectsIso _ _).2 (hg i)


set_option backward.isDefEq.respectTransparency.types false in
theorem finite_flat_surjective_of_openCover : ∀ (X T₀ : Scheme.{0}) (p : X ⟶ T₀) (ι : Type) (V : ι → T₀.Opens), iSup V = ⊤ → ∀ (Xi : ι → Scheme.{0}) (m : ∀ i, Xi i ⟶ X) (q : ∀ i, Xi i ⟶ (V i).toScheme), (∀ i, IsPullback (m i) (q i) p (V i).ι) → ∀ (B : Scheme.{0}) (b : B ⟶ X), IsClosedImmersion b → ∀ (A : ι → Scheme.{0}) (a : ∀ i, A i ⟶ Xi i), (∀ i, IsClosedImmersion (a i)) → (∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i), (∃ z : Y ⟶ B, z ≫ b = g ≫ m i) ↔ (∃ z : Y ⟶ A i, z ≫ a i = g)) → (∀ i, IsFinite (a i ≫ q i) ∧ Flat (a i ≫ q i) ∧ Surjective (a i ≫ q i)) → IsFinite (b ≫ p) ∧ Flat (b ≫ p) ∧ Surjective (b ≫ p) := by
  intro X T₀ p ι V hV Xi m q hpb B b hb A a ha hrep hP
  have H : ∀ i, ∃ k : A i ⟶ B, IsPullback k (a i ≫ q i) (b ≫ p) (V i).ι := by
    intro i
    have := ha i
    obtain ⟨k, hk⟩ := exists_isPullback_of_factor_iff (m i) b (a i) (hrep i)
    exact ⟨k, hk.paste_vert (hpb i)⟩
  choose k hk using H
  have hfin : IsZariskiLocalAtTarget @IsFinite.{0} :=
    inferInstance
  have hflat : IsZariskiLocalAtTarget @Flat.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0})
  exact ⟨of_isPullback_openCover @IsFinite _ V hV A k _ hk (fun i => (hP i).1),
    of_isPullback_openCover @Flat _ V hV A k _ hk (fun i => (hP i).2.1),
    of_isPullback_openCover @Surjective _ V hV A k _ hk (fun i => (hP i).2.2)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteLeftOfFiniteTensorProductComplex
section
open scoped TensorProduct

namespace GlobalTheory

open scoped TensorProduct in
private lemma trace_eq_zero_of_not_finite' {V : Type} [AddCommGroup V] [Module ℂ V]
    (h : ¬ Module.Finite ℂ V) (f : V →ₗ[ℂ] V) : LinearMap.trace ℂ V f = 0 := by
  have hb : ¬ ∃ s : Finset V, Nonempty (Module.Basis s ℂ V) := by
    rintro ⟨s, ⟨b⟩⟩
    exact h (Module.Finite.of_basis b)
  simp [LinearMap.trace, hb]

open scoped TensorProduct in
private lemma finite_left_of_finite_tensor_of_nontrivial {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Nontrivial W] [Module.Finite ℂ (V ⊗[ℂ] W)] :
    Module.Finite ℂ V := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W, φ w ≠ 0 := by
    by_contra! h
    exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).mp h)
  let p : V ⊗[ℂ] W →ₗ[ℂ] V :=
    (TensorProduct.rid ℂ V).toLinearMap ∘ₗ TensorProduct.map LinearMap.id φ
  refine Module.Finite.of_surjective p fun v => ⟨v ⊗ₜ ((φ w)⁻¹ • w), ?_⟩
  simp [p, hφ]

open scoped TensorProduct in
private lemma finite_right_of_finite_tensor_of_nontrivial {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [Nontrivial V] [Module.Finite ℂ (V ⊗[ℂ] W)] :
    Module.Finite ℂ W := by
  have : Module.Finite ℂ (W ⊗[ℂ] V) :=
    Module.Finite.equiv (TensorProduct.comm ℂ V W)
  exact finite_left_of_finite_tensor_of_nontrivial (W := V)


open scoped TensorProduct in
theorem _root_.GlobalTheory.trace_tensorProduct_map_complex {U U' : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] (T : U →ₗ[ℂ] U) (T' : U' →ₗ[ℂ] U') :
    LinearMap.trace ℂ (U ⊗[ℂ] U') (TensorProduct.map T T') =
      LinearMap.trace ℂ U T * LinearMap.trace ℂ U' T' := by
  by_cases hU : Module.Finite ℂ U
  · by_cases hU' : Module.Finite ℂ U'
    · exact LinearMap.trace_tensorProduct' T T'
    · rw [trace_eq_zero_of_not_finite' hU' T', mul_zero]
      by_cases hUU : Module.Finite ℂ (U ⊗[ℂ] U')
      · rcases subsingleton_or_nontrivial U with hs | hs
        · rw [Subsingleton.elim T 0, TensorProduct.map_zero_left, map_zero]
        · exact absurd (finite_right_of_finite_tensor_of_nontrivial (V := U)) hU'
      · exact trace_eq_zero_of_not_finite' hUU _
  · rw [trace_eq_zero_of_not_finite' hU T, zero_mul]
    by_cases hUU : Module.Finite ℂ (U ⊗[ℂ] U')
    · rcases subsingleton_or_nontrivial U' with hs | hs
      · rw [Subsingleton.elim T' 0, TensorProduct.map_zero_right, map_zero]
      · exact absurd (finite_left_of_finite_tensor_of_nontrivial (W := U')) hU
    · exact trace_eq_zero_of_not_finite' hUU _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicRootsBddMulIsIntegral
section
open NumberField Polynomial

namespace GlobalTheory

theorem isIntegral_pow_mul_esymm (s : Multiset ℂ) (c : ℂ) (m : ℕ)
    (h : ∀ w ∈ s, IsIntegral ℤ (c * w)) : IsIntegral ℤ (c ^ m * s.esymm m) := by
  rw [Multiset.esymm, ← Multiset.sum_map_mul_left]
  refine (integralClosure ℤ ℂ).multiset_sum_mem ?_
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
  rw [Multiset.mem_powersetCard] at ht
  have : c ^ m * t.prod = (t.map (fun w => c * w)).prod := by
    rw [Multiset.prod_map_mul (f := fun _ => c) (g := fun w => w), Multiset.map_const', Multiset.prod_replicate,
      Multiset.map_id', ht.2]
  rw [this]
  refine (integralClosure ℤ ℂ).multiset_prod_mem ?_
  intro y hy
  obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hy
  exact h w (Multiset.mem_of_le ht.1 hw)

theorem finite_monic_roots_bdd_mul_isIntegral :
    ∀ (F : Type) [Field F] [NumberField F] (n N : ℕ) (B : ℝ), 0 < N →
    {P : Polynomial F | P.Monic ∧ P.natDegree = n ∧ ∀ φ : F →+* ℂ, ∀ w ∈ (P.map φ).roots,
      ‖w‖ ≤ B ∧ IsIntegral ℤ ((N : ℂ) * w)}.Finite := by
  intro F _ _ n N B hN
  let φ₀ : F →+* ℂ := (Classical.arbitrary (InfinitePlace F)).embedding
  let B₁ : ℝ := max |B| 1
  let C : ℝ := (N : ℝ) ^ n * (B₁ ^ n * 2 ^ n)
  have hT := Embeddings.finite_of_norm_le F ℂ C
  let f : F[X] → Fin (n + 1) → F := fun P k => (N : F) ^ n * P.coeff k
  refine Set.Finite.of_finite_image (f := f) ((Set.Finite.pi (fun _ => hT)).subset ?_) ?_
  · rintro _ ⟨P, ⟨hm, hd, hr⟩, rfl⟩ k -
    have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.2
    refine ⟨?_, fun φ => ?_⟩
    · have hcard : Multiset.card (P.map φ₀).roots = (P.map φ₀).natDegree :=
        IsAlgClosed.card_roots_eq_natDegree
      have hdeg : (P.map φ₀).natDegree = n := by rw [hm.natDegree_map, hd]
      have hc := coeff_eq_esymm_roots_of_card hcard (k := k) (by omega)
      rw [(hm.map φ₀).leadingCoeff, hdeg, one_mul, coeff_map] at hc
      rw [← isIntegral_algHom_iff φ₀.toIntAlgHom φ₀.injective]
      show IsIntegral ℤ (φ₀ ((N : F) ^ n * P.coeff k))
      rw [map_mul, map_pow, map_natCast, hc]
      have hsplit : (N : ℂ) ^ n * ((-1) ^ (n - k) * (P.map φ₀).roots.esymm (n - k)) =
          ((N : ℂ) ^ (k : ℕ) * (-1) ^ (n - k)) *
            ((N : ℂ) ^ (n - k) * (P.map φ₀).roots.esymm (n - k)) := by
        have : (N : ℂ) ^ n = (N : ℂ) ^ (k : ℕ) * (N : ℂ) ^ (n - k) := by
          rw [← pow_add, Nat.add_sub_cancel' hk]
        rw [this]; ring
      rw [hsplit]
      refine IsIntegral.mul (IsIntegral.mul ((isIntegral_natCast N).pow _)
        ((isIntegral_one.neg).pow _)) ?_
      exact GlobalTheory.isIntegral_pow_mul_esymm _ _ _ (fun w hw => (hr φ₀ w hw).2)
    · show ‖φ ((N : F) ^ n * P.coeff k)‖ ≤ C
      rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast]
      have hb := coeff_le_of_roots_le (p := P) (f := φ) (B := B₁) k hm (IsAlgClosed.splits _)
        (fun z hz => (hr φ z hz).1.trans ((le_abs_self B).trans (le_max_left _ _)))
      rw [coeff_map, hd] at hb
      have hB₁ : (1 : ℝ) ≤ B₁ := le_max_right _ _
      have h2 : B₁ ^ (n - k) * (n.choose k : ℝ) ≤ B₁ ^ n * 2 ^ n :=
        mul_le_mul (pow_le_pow_right₀ hB₁ (Nat.sub_le _ _))
          (by exact_mod_cast Nat.choose_le_two_pow n k) (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (hb.trans h2) (by positivity)
  · rintro P ⟨-, hdP, -⟩ Q ⟨-, hdQ, -⟩ hPQ
    ext i
    by_cases hi : i ≤ n
    · have h := congrFun hPQ ⟨i, by omega⟩
      exact mul_left_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne')) h
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfBoundedEmbeddingsAndValuations
section
open NumberField IsDedekindDomain Filter

namespace GlobalTheory.BddFinite

theorem exists_le_exp_nat (B : WithZero (Multiplicative ℤ)) : ∃ n : ℕ, B ≤ WithZero.exp (n : ℤ) := by
  induction B using WithZero.recZeroCoe with
  | zero => exact ⟨0, zero_le'⟩
  | coe m =>
    refine ⟨(Multiplicative.toAdd m).toNat, ?_⟩
    rw [WithZero.exp, WithZero.coe_le_coe, ← Multiplicative.toAdd_le]
    simp only [toAdd_ofAdd]
    exact Int.self_le_toNat _

theorem exists_clearing {K : Type} [Field K] [NumberField K] (A : Set K)
    (w : HeightOneSpectrum (𝓞 K)) (B : WithZero (Multiplicative ℤ))
    (hB : ∀ x ∈ A, w.valuation K x ≤ B) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ x ∈ A, w.valuation K ((a : K) * x) ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_le_exp_nat B
  have hne : w.asIdeal ^ n ≠ ⊥ := pow_ne_zero n w.ne_bot
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨r, hr0, fun x hx => ?_⟩
  have h1 : w.intValuation r ≤ WithZero.exp (-(n : ℤ)) := (w.intValuation_le_pow_iff_mem r n).2 hr
  rw [map_mul]
  have h2 : w.valuation K (r : K) = w.intValuation r := w.valuation_of_algebraMap r
  rw [h2]
  calc w.intValuation r * w.valuation K x ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp (n : ℤ) :=
        mul_le_mul' h1 ((hB x hx).trans hn)
    _ = 1 := by rw [← WithZero.exp_add]; simp

theorem finite_of_bdd : ∀ (K : Type) [Field K] [NumberField K] (A : Set K) (R : ℝ), (∀ x ∈ A, ∀ τ : K →+* ℂ, ‖τ x‖ ≤ R) → (∀ w : HeightOneSpectrum (𝓞 K), ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ A, w.valuation K x ≤ B) → (∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite, ∀ x ∈ A, w.valuation K x ≤ 1) → A.Finite := by
  classical
  intro K _ _ A R hR hB hcof
  choose B hB using hB
  choose a ha0 ha using fun w => exists_clearing A w (B w) (hB w)
  have hF : {w : HeightOneSpectrum (𝓞 K) | ¬ ∀ x ∈ A, w.valuation K x ≤ 1}.Finite :=
    Filter.eventually_cofinite.mp hcof
  set F := hF.toFinset with hFdef
  set d : 𝓞 K := ∏ w ∈ F, a w with hd
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun w _ => ha0 w)
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0

  have hval : ∀ x ∈ A, ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K ((d : K) * x) ≤ 1 := by
    intro x hx v
    by_cases hv : v ∈ F
    · have hsplit : (d : K) = ((∏ w ∈ F.erase v, a w : 𝓞 K) : K) * (a v : K) := by
        rw [hd, ← Finset.prod_erase_mul F a hv]; push_cast; ring
      rw [hsplit, mul_assoc, map_mul]
      exact mul_le_one' (v.valuation_le_one _) (ha v x hx)
    · have hv' : ∀ y ∈ A, v.valuation K y ≤ 1 := by
        have : v ∉ {w : HeightOneSpectrum (𝓞 K) | ¬ ∀ x ∈ A, w.valuation K x ≤ 1} := by
          simpa [F] using hv
        simpa using this
      rw [map_mul]
      exact mul_le_one' (v.valuation_le_one _) (hv' x hx)
  set M : ℝ := ∑ τ : K →+* ℂ, ‖τ (d : K)‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun τ _ => norm_nonneg _)
  have hfin := NumberField.Embeddings.finite_of_norm_le K ℂ (M * R)
  refine (hfin.image (fun y => (d : K)⁻¹ * y)).subset ?_
  intro x hx
  refine ⟨(d : K) * x, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K _ (hval x hx)
    rw [← hy]
    exact (NumberField.RingOfIntegers.isIntegral_coe y)
  · intro τ
    rw [map_mul, norm_mul]
    have h1 : ‖τ (d : K)‖ ≤ M :=
      Finset.single_le_sum (f := fun τ : K →+* ℂ => ‖τ (d : K)‖) (fun τ _ => norm_nonneg _) (Finset.mem_univ τ)
    exact mul_le_mul h1 (hR x hx τ) (norm_nonneg _) hM0
  · simp only
    rw [← mul_assoc, inv_mul_cancel₀ hdK, one_mul]

end GlobalTheory.BddFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfLocallyFiniteFreeLocalizations
section
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocFreeProj

theorem finite_projective_of_locally_free : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M], (∀ q : PrimeSpectrum R, ∃ r : R, r ∉ q.asIdeal ∧ ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F) (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F) (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F) (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ) → Module.Finite R M ∧ Module.Projective R M := by
  intro R _ M _ _ h
  let s : Set R := {r | ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
    (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
    (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F)
    (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hP⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hsm (Ideal.subset_span hP))
  have hg : ∀ g : s, g.1 ∈ s := fun g => g.2
  choose F iA iM iL iT iFin iFree ϕ hϕ using hg
  letI := iA
  letI := iM
  letI := iL
  haveI := iT
  haveI := iFin
  haveI := iFree
  haveI := hϕ
  haveI (g : s) : Module.Flat R (F g) := by
    haveI : Module.Flat R (Localization.Away g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans R (Localization.Away g.1) (F g)
  haveI hfp : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := F)
      (Rₚ := fun g : s => Localization.Away g.1) ϕ
      fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat R M :=
    Module.flat_of_isLocalized_span R M s hs F ϕ fun _ => inferInstance
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.LocFreeProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfValuationBoundedNormLeOne
section
open NumberField IsDedekindDomain Filter

namespace GlobalTheory.BCT.SuppFin

theorem exists_ne_zero_intValuation_le_of_finset {E : Type} [Field E] [NumberField E]
    (T : Finset (HeightOneSpectrum (𝓞 E))) (n : HeightOneSpectrum (𝓞 E) → ℕ) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ v ∈ T, v.intValuation d ≤ WithZero.exp (-(n v : ℤ)) := by
  classical
  have hJ : (∏ v ∈ T, v.asIdeal ^ n v) ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    exact fun v _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  exact ⟨d, hd0, fun v hv => (v.intValuation_le_pow_iff_mem d (n v)).mpr
    ((Ideal.prod_le_inf.trans (Finset.inf_le hv)) hd)⟩

theorem finite_of_valuation_bounded_of_norm_le_one :
    ∀ (E : Type) [Field E] [NumberField E] (X : Set E),
      (∀ w : HeightOneSpectrum (𝓞 E), ∃ N : ℤ, ∀ a ∈ X, w.valuation E a ≤ WithZero.exp N) →
      (∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ a ∈ X, w.valuation E a ≤ 1) →
      (∀ a ∈ X, ∀ τ : E →+* ℂ, ‖τ a‖ ≤ 1) → X.Finite := by
  intro E _ _ X hN hcof hτ
  classical
  choose N hN using hN
  have hTf := Filter.eventually_cofinite.1 hcof
  obtain ⟨d, hd0, hd⟩ := exists_ne_zero_intValuation_le_of_finset (E := E) hTf.toFinset
    (fun w => (N w).toNat)
  set d' : E := algebraMap (𝓞 E) E d with hd'
  have hd'0 : d' ≠ 0 := by
    rw [hd']; exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).2 hd0
  set B : ℝ := ∑ τ : E →+* ℂ, ‖τ d'‖ with hB
  have hval : ∀ a ∈ X, ∀ w : HeightOneSpectrum (𝓞 E), w.valuation E (d' * a) ≤ 1 := by
    intro a ha w
    rw [map_mul, hd', HeightOneSpectrum.valuation_of_algebraMap]
    by_cases hw : w ∈ hTf.toFinset
    · have h1 := hd w hw
      have h2 := hN w a ha
      have h3 : w.intValuation d ≤ WithZero.exp (-(N w)) :=
        h1.trans (WithZero.exp_le_exp.2 (by omega))
      calc w.intValuation d * w.valuation E a ≤ WithZero.exp (-(N w)) * WithZero.exp (N w) :=
            mul_le_mul' h3 h2
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · have h2 : ∀ a ∈ X, w.valuation E a ≤ 1 := by
        simpa [Set.Finite.mem_toFinset] using hw
      exact mul_le_one' (w.intValuation_le_one d) (h2 a ha)
  have himg : (fun x => d' * x) '' X ⊆
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ B} := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, fun φ => ?_⟩
    · obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (d' * a) (hval a ha)
      show IsIntegral ℤ (d' * a)
      rw [← hr]
      exact RingOfIntegers.isIntegral_coe r
    · show ‖φ (d' * a)‖ ≤ B
      rw [map_mul, norm_mul]
      calc ‖φ d'‖ * ‖φ a‖ ≤ ‖φ d'‖ * 1 :=
            mul_le_mul_of_nonneg_left (hτ a ha φ) (norm_nonneg _)
        _ = ‖φ d'‖ := mul_one _
        _ ≤ B := Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ d'‖)
              (fun _ _ => norm_nonneg _) (Finset.mem_univ φ)
  exact Set.Finite.of_finite_image ((NumberField.Embeddings.finite_of_norm_le E ℂ B).subset himg)
    (fun x _ y _ hxy => mul_left_cancel₀ hd'0 hxy)

end GlobalTheory.BCT.SuppFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSublevelOfIntQuadraticGeOne
section
namespace GlobalTheory

theorem posquad_finite : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (q : X → ℤ), (∀ a, q (-a) = q a) → (∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b)) → (∀ a, a ≠ 0 → 1 ≤ q a) → ∀ N : ℤ, {a | q a ≤ N}.Finite := by
  intro X _ _ q hneg hcube hpos N
  have h0 : q 0 = 0 := by
    have := hcube 0 0 0
    simp only [add_zero] at this
    linarith
  have hnn : ∀ a, 0 ≤ q a := by
    intro a
    by_cases ha : a = 0
    · simp [ha, h0]
    · linarith [hpos a ha]
  let B : X → X → ℤ := fun a b => q (a + b) - q a - q b
  have Bsymm : ∀ a b, B a b = B b a := by
    intro a b; simp only [B, add_comm a b]; ring
  have Badd : ∀ a a' b, B (a + a') b = B a b + B a' b := by
    intro a a' b
    simp only [B]
    linarith [hcube a a' b]
  let L : X → (X →+ ℤ) := fun b => AddMonoidHom.mk' (fun a => B a b) (fun a a' => Badd a a' b)
  have L_apply : ∀ a b, L b a = B a b := fun _ _ => rfl
  have Bdiag : ∀ a, B a a = 2 * q a := by
    intro a
    have h := hcube a (-a) a
    simp only [add_neg_cancel, neg_add_cancel, zero_add, hneg, h0] at h
    show q (a + a) - q a - q a = 2 * q a
    linarith
  have Bbound : ∀ a s, |B a s| ≤ q a + q s := by
    intro a s
    have h1 : B a s = q (a + s) - q a - q s := rfl
    have h2 : B (-a) s = q (-a + s) - q (-a) - q s := rfl
    have h3 : B (-a) s = - B a s := by
      rw [← L_apply, ← L_apply, map_neg]
    rw [hneg] at h2
    have := hnn (a + s)
    have := hnn (-a + s)
    rw [abs_le]; constructor <;> linarith
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  have hzero : ∀ c, (∀ i ∈ S, B c i = 0) → c = 0 := by
    intro c hc
    have hle : Submodule.span ℤ (S : Set X) ≤ (L c).ker.toIntSubmodule := by
      rw [Submodule.span_le]
      intro x hx
      change (L c) x = 0
      rw [L_apply, Bsymm]; exact hc x hx
    have hc' : c ∈ (L c).ker.toIntSubmodule := hle (hS ▸ Submodule.mem_top)
    change (L c) c = 0 at hc'
    rw [L_apply, Bdiag] at hc'
    by_contra hne
    have := hpos c hne
    omega
  let φ : X → (S → ℤ) := fun a i => B a i
  have φinj : Function.Injective φ := by
    intro a a' h
    have : a - a' = 0 := by
      apply hzero
      intro i hi
      have hi' := congrFun h ⟨i, hi⟩
      simp only [φ] at hi'
      rw [← L_apply, map_sub, L_apply, L_apply, hi', sub_self]
    exact sub_eq_zero.mp this
  have hfin : (Set.pi Set.univ (fun i : S => Set.Icc (-(N + q i)) (N + q i))).Finite :=
    Set.Finite.pi (fun i => Set.finite_Icc _ _)
  refine (hfin.preimage φinj.injOn).subset ?_
  intro a ha
  simp only [Set.mem_setOf_eq] at ha
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro i
  have := Bbound a i
  rw [abs_le] at this
  simp only [φ]
  constructor <;> linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumReindexEquivalentSubtypes
section
open scoped Classical

namespace GlobalTheory

theorem finsum_ite_eq_of_equiv {A B : Type} (PA : A → Prop) (PB : B → Prop)
    (e : {a // PA a} ≃ {b // PB b}) (g : A → ℂ) (h : B → ℂ)
    (hgh : ∀ a, h (e a).1 = g a.1) :
    (∑ᶠ a, if PA a then g a else 0) = ∑ᶠ b, if PB b then h b else 0 := by
  have hA : (∑ᶠ a, if PA a then g a else 0) = ∑ᶠ a : {a // PA a}, g a.1 := by
    rw [finsum_subtype_eq_finsum_cond]
    exact finsum_congr fun a => (finsum_eq_if).symm
  have hB : (∑ᶠ b, if PB b then h b else 0) = ∑ᶠ b : {b // PB b}, h b.1 := by
    rw [finsum_subtype_eq_finsum_cond]
    exact finsum_congr fun b => (finsum_eq_if).symm
  rw [hA, hB, ← finsum_comp_equiv e]
  exact finsum_congr fun a => (hgh a).symm

end GlobalTheory
end

