module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.ExistsNatCombinationIsUnitOfIsUnitCombination
section
open MvPolynomial in
private lemma UpperTheory.rational_polynomial_vanishing_naturals {K : Type} [Field K] [CharZero K] {m : ℕ}
    (P : MvPolynomial (Fin m) K) (hP : P ≠ 0) :
    ∃ Q : MvPolynomial (Fin m) ℚ, Q ≠ 0 ∧ ∀ a : Fin m → ℕ,
      eval (fun i => (a i : K)) P = 0 → eval (fun i => (a i : ℚ)) Q = 0 := by
  classical
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hP
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℚ K, φ (P.coeff d) ≠ 0 := by
    by_contra h
    push Not at h
    exact hd ((Module.forall_dual_apply_eq_zero_iff ℚ _).mp h)
  refine ⟨∑ e ∈ P.support, monomial e (φ (P.coeff e)), ?_, ?_⟩
  · apply MvPolynomial.ne_zero_iff.mpr
    refine ⟨d, ?_⟩
    rw [coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    simpa [mem_support_iff, hd] using hφ
  · intro a ha
    have h1 := congrArg φ ha
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eval_eq', map_sum, map_zero] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← h1]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
    have : P.coeff e * ∏ i, (a i : K) ^ e i = (∏ i, (a i : ℚ) ^ e i) • P.coeff e := by
      rw [Rat.smul_def, mul_comm]
      push_cast
      rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]

open MvPolynomial in
private lemma UpperTheory.exists_nat_point_avoiding_polynomials {W : Type} [Finite W] {K : W → Type} [∀ w, Field (K w)]
    [∀ w, CharZero (K w)] {m : ℕ}
    (P : ∀ w, MvPolynomial (Fin m) (K w)) (hP : ∀ w, P w ≠ 0) :
    ∃ a : Fin m → ℕ, ∀ w, eval (fun i => (a i : K w)) (P w) ≠ 0 := by
  classical
  haveI := Fintype.ofFinite W
  choose Q hQ hQ' using fun w => UpperTheory.rational_polynomial_vanishing_naturals (P w) (hP w)
  have hprod : ∏ w, Q w ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hQ w
  by_contra h
  push Not at h
  apply hprod
  apply MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → ℚ))
    (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
  intro x hx
  choose a ha using fun i => hx i (Set.mem_univ i)
  obtain rfl : x = fun i => (a i : ℚ) := funext fun i => (ha i).symm
  obtain ⟨w, hw⟩ := h a
  rw [map_prod, map_zero]
  exact Finset.prod_eq_zero (Finset.mem_univ w) (hQ' w a hw)

theorem UpperTheory.exists_nat_combination_isUnit_of_isUnit_combination :
    ∀ (W : Type) [Finite W] (K : W → Type) [∀ w, Field (K w)] [∀ w, CharZero (K w)] (n m : ℕ) (z : Fin m → Matrix (Fin n) (Fin n) (∀ w, K w)) (x : Fin m → ∀ w, K w), IsUnit (∑ i, x i • z i) → ∃ a : Fin m → ℕ, IsUnit (∑ i, ((a i : ℕ) : ∀ w, K w) • z i) := by
  intro W _ K _ _ n m z x hx
  let P : ∀ w, MvPolynomial (Fin m) (K w) := fun w =>
    (Matrix.of fun j k => ∑ i, MvPolynomial.X i * MvPolynomial.C (z i j k w)).det
  have key : ∀ (y : Fin m → ∀ w, K w) (w : W),
      (∑ i, y i • z i).det w = MvPolynomial.eval (fun i => y i w) (P w) := by
    intro y w
    have h1 := RingHom.map_det (Pi.evalRingHom K w) (∑ i, y i • z i)
    simp only [Pi.evalRingHom_apply] at h1
    rw [h1, RingHom.map_det]
    congr 1
    ext j k
    simp [Matrix.sum_apply, Finset.sum_apply]
  have hiff : ∀ y : Fin m → ∀ w, K w, IsUnit (∑ i, y i • z i) ↔
      ∀ w, MvPolynomial.eval (fun i => y i w) (P w) ≠ 0 := by
    intro y
    rw [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
    simp only [key, isUnit_iff_ne_zero]
  obtain ⟨a, ha⟩ := UpperTheory.exists_nat_point_avoiding_polynomials P (fun w h => (hiff x).mp hx w (by simp [h]))
  exact ⟨a, (hiff fun i => (a i : ∀ w, K w)).mpr (by simpa using ha)⟩
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.InnerProductIntegralFundamentalDomainOfCompact
section
open MeasureTheory

theorem UpperTheory.innerProduct_integral_fundamentalDomain_of_compact :
    ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsOpenPosMeasure] (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → ∀ Ω : Set H, IsCompact Ω → (∀ g, ∃ γ ∈ Γ, γ * g ∈ Ω) → ∀ f g : H → ℂ, Continuous f → Continuous g → (∀ γ ∈ Γ, ∀ h, f (γ * h) = f h) → (∀ γ ∈ Γ, ∀ h, g (γ * h) = g h) → IntegrableOn (fun h => f h * starRingEnd ℂ (g h)) 𝓕 μ ∧ (∀ y, ∫ h in 𝓕, f (h * y) * starRingEnd ℂ (g (h * y)) ∂μ = ∫ h in 𝓕, f h * starRingEnd ℂ (g h) ∂μ) ∧ (f ≠ 0 → 0 < (∫ h in 𝓕, f h * starRingEnd ℂ (f h) ∂μ).re) := by
  intro H _ _ _ _ _ μ _ _ _ Γ _ 𝓕 h𝓕 hfin Ω hΩ hcov f g hf hg hfi hgi
  have bdd : ∀ u : H → ℂ, Continuous u → (∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) → ∃ C, ∀ h, ‖u h‖ ≤ C := by
    intro u hu hinv
    obtain ⟨C, hC⟩ := hΩ.exists_bound_of_continuousOn hu.continuousOn
    refine ⟨C, fun h => ?_⟩
    obtain ⟨γ, hγ, hmem⟩ := hcov h
    rw [← hinv γ hγ h]
    exact hC _ hmem
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.mpr hfin.ne
  have intg : ∀ u : H → ℂ, Continuous u → (∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) → IntegrableOn u 𝓕 μ := by
    intro u hu hinv
    obtain ⟨C, hC⟩ := bdd u hu hinv
    exact Integrable.of_bound hu.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  set u : H → ℂ := fun h => f h * starRingEnd ℂ (g h) with hu_def
  have hu : Continuous u := hf.mul (Complex.continuous_conj.comp hg)
  have hui : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h := by
    intro γ hγ h
    simp [u, hfi γ hγ, hgi γ hγ]
  refine ⟨intg u hu hui, ?_, ?_⟩
  · intro y
    let t := (fun h => h * y⁻¹) ⁻¹' 𝓕
    have ht : IsFundamentalDomain Γ t μ :=
      h𝓕.preimage_of_equiv (measurePreserving_mul_right μ y⁻¹).quasiMeasurePreserving
        (e := id) Function.bijective_id (fun γ x => by
          simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc])
    have hset : 𝓕 = (fun h => h * y) ⁻¹' t := by
      ext h
      simp [t]
    have h1 : ∫ h in 𝓕, u (h * y) ∂μ = ∫ h in t, u h ∂μ := by
      rw [hset]
      exact (measurePreserving_mul_right μ y).setIntegral_preimage_emb
        (MeasurableEquiv.mulRight y).measurableEmbedding u t
    have h2 : ∫ h in t, u h ∂μ = ∫ h in 𝓕, u h ∂μ :=
      ht.setIntegral_eq h𝓕 (fun γ x => by
        simp only [Subgroup.smul_def, smul_eq_mul]
        exact hui γ γ.2 x)
    exact h1.trans h2
  · intro hne
    have hff : ∀ h, f h * starRingEnd ℂ (f h) = ((Complex.normSq (f h) : ℝ) : ℂ) :=
      fun h => Complex.mul_conj _
    simp_rw [hff]
    rw [integral_complex_ofReal, Complex.ofReal_re]
    have hnn : 0 ≤ fun h => Complex.normSq (f h) := fun h => Complex.normSq_nonneg _
    have hint : IntegrableOn (fun h => Complex.normSq (f h)) 𝓕 μ := by
      have := (intg (fun h => f h * starRingEnd ℂ (f h)) (hf.mul (Complex.continuous_conj.comp hf))
        (fun γ hγ h => by simp [hfi γ hγ])).re
      simp only [hff, Complex.ofReal_re] at this
      exact this
    refine lt_of_le_of_ne (integral_nonneg hnn) (fun h0 => hne ?_)
    have hae := (integral_eq_zero_iff_of_nonneg hnn hint).mp h0.symm
    have hae' : (fun h => ‖f h‖ₑ) =ᵐ[μ.restrict 𝓕] 0 := by
      filter_upwards [hae] with h hh
      simp only [Pi.zero_apply, Complex.normSq_eq_zero] at hh
      simp [hh]
    have hl𝓕 : ∫⁻ h in 𝓕, ‖f h‖ₑ ∂μ = 0 := by
      rw [lintegral_congr_ae hae']
      simp
    have hlall : ∫⁻ h, ‖f h‖ₑ ∂μ = 0 := by
      rw [h𝓕.lintegral_eq_tsum'']
      have : ∀ γ : Γ, ∫⁻ x in 𝓕, ‖f (γ • x)‖ₑ ∂μ = 0 := by
        intro γ
        simp only [Subgroup.smul_def, smul_eq_mul, hfi γ γ.2]
        exact hl𝓕
      simp [this]
    have hz := (lintegral_eq_zero_iff' hf.enorm.aemeasurable).mp hlall
    have hz' : f =ᵐ[μ] fun _ => (0 : ℂ) := by
      filter_upwards [hz] with h hh
      simpa using hh
    exact (Continuous.ae_eq_iff_eq μ hf continuous_const).mp hz'
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.InvariantSesquilinearFormEqSmulOfIrreducible
section
theorem UpperTheory.invariant_sesquilinearForm_eq_smul_of_irreducible :
    ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] (ρ : G →* Module.End ℂ V)
      (_hI : ∀ W : Submodule ℂ V, (∀ g, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
      (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (_hh : ∀ a b, B b a = star (B a b)) (_hp : ∀ a, a ≠ 0 → 0 < (B a a).re)
      (_hinv : ∀ g a b, B (ρ g a) (ρ g b) = B a b) (B₁ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ g a b, B₁ (ρ g a) (ρ g b) = B₁ a b) → ∃ c : ℂ, ∀ a b, B₁ a b = c * B a b := by
  intro G V _ _ _ _ _ ρ hI B hh hp hinv B₁ h₁
  classical
  let n := Module.finrank ℂ V
  let e := Module.finBasis ℂ V
  let φB : V →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun j => B.flip (e j))
  let φ₁ : V →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun j => B₁.flip (e j))
  have hinj : Function.Injective φB := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have h0 : B a = 0 := e.ext (fun j => by
      have := congrFun ha j
      simpa [φB] using this)
    by_contra hne
    have := hp a hne
    rw [h0] at this
    simp at this
  have hsurj : Function.Surjective φB :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [Module.finrank_fin_fun])).mp hinj
  let E := LinearEquiv.ofBijective φB ⟨hinj, hsurj⟩
  let T : Module.End ℂ V := E.symm.toLinearMap ∘ₗ φ₁
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hTv : T v = c • v := hv.apply_eq_smul
  have hv0 : v ≠ 0 := hv.2
  have key : B₁ v = c • B v := by
    apply e.ext
    intro j
    have h1 : φB (T v) = φ₁ v := E.apply_symm_apply (φ₁ v)
    rw [hTv] at h1
    have h2 := congrFun h1 j
    simp [φB, φ₁] at h2
    simpa [LinearMap.smul_apply] using h2.symm
  let W := LinearMap.ker (B₁ - c • B)
  have hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W := by
    intro g w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have hw' : ∀ b, B₁ w b = c * B w b := by
      intro b
      have := LinearMap.congr_fun hw b
      simp at this
      linear_combination this
    ext b
    have hb : ρ g (ρ g⁻¹ b) = b := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    obtain ⟨b', rfl⟩ : ∃ b', ρ g b' = b := ⟨_, hb⟩
    simp [h₁, hinv, hw']
  rcases hI W hW with h | h
  · have hvW : v ∈ W := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, key, sub_self]
    rw [h] at hvW
    exact absurd ((Submodule.mem_bot ℂ).mp hvW) hv0
  · refine ⟨c, fun a b => ?_⟩
    have ha : a ∈ W := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at ha
    have := LinearMap.congr_fun ha b
    simp at this
    linear_combination this
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.IsOpenEmbeddingUnitsValGeneralLinearPi
section
theorem UpperTheory.isOpenEmbedding_units_val_generalLinearPi :
    ∀ (W : Type) [Finite W] (K : W → Type) [∀ w, NontriviallyNormedField (K w)] (n : ℕ), Topology.IsOpenEmbedding (Units.val : GL (Fin n) (∀ w, K w) → Matrix (Fin n) (Fin n) (∀ w, K w)) := by
  intro W _ K _ n
  have hdet : Continuous (fun M : Matrix (Fin n) (Fin n) (∀ w, K w) => M.det) :=
    continuous_id.matrix_det
  have hadj : Continuous (fun M : Matrix (Fin n) (Fin n) (∀ w, K w) => M.adjugate) :=
    continuous_id.matrix_adjugate
  have hU : ∀ M : Matrix (Fin n) (Fin n) (∀ w, K w), IsUnit M ↔ ∀ w, M.det w ≠ 0 := by
    intro M
    rw [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
    simp only [isUnit_iff_ne_zero]
  refine ⟨?_, ?_⟩
  · refine Units.isEmbedding_val_mk'
      (f := fun M : Matrix (Fin n) (Fin n) (∀ w, K w) =>
        (fun w => (M.det w)⁻¹ : ∀ w, K w) • M.adjugate) ?_ ?_
    · have h1 : ContinuousOn (fun M : Matrix (Fin n) (Fin n) (∀ w, K w) =>
          (fun w => (M.det w)⁻¹ : ∀ w, K w)) {x | IsUnit x} := by
        refine continuousOn_pi.2 fun w => ?_
        exact (((continuous_apply w).comp hdet).continuousOn).inv₀ fun M hM => (hU M).1 hM w
      refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
      exact h1.mul (hadj.matrix_elem i j).continuousOn
    · intro u
      have hu := (hU u.1).1 u.isUnit
      symm
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
      have : ((fun w => ((u.1).det w)⁻¹ : ∀ w, K w) * (u.1).det) = 1 := by
        funext w
        exact inv_mul_cancel₀ (hu w)
      rw [this, one_smul]
  · have : Set.range (Units.val : GL (Fin n) (∀ w, K w) → Matrix (Fin n) (Fin n) (∀ w, K w))
        = ⋂ w, {M : Matrix (Fin n) (Fin n) (∀ w, K w) | M.det w ≠ 0} := by
      ext M
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      exact hU M
    rw [this]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_ne_fun ((continuous_apply w).comp hdet) continuous_const
end

