module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DiscrMulDetEqNormOfAnnihilator
section
namespace GlobalTheory

open scoped TensorProduct

theorem annihilator_diagonal_form_swap {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    {d : ℕ} (b : Fin d → B) (M : Matrix (Fin d) (Fin d) R)
    (h : ∀ x : B, (∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j)) *
      (TensorProduct.tmul R x 1 - TensorProduct.tmul R 1 x) = 0)
    (f : B →ₗ[R] R) (y : B) :
    ∑ i, ∑ j, (M i j * f (b i * y)) • b j = ∑ i, ∑ j, (M i j * f (b i)) • (b j * y) := by
  classical
  let L : TensorProduct R B B →ₗ[R] B :=
    TensorProduct.lift ((LinearMap.lsmul R B).compl₁₂ f LinearMap.id)
  have hL : ∀ a c : B, L (TensorProduct.tmul R a c) = f a • c := fun a c => by simp [L]
  have e := h y
  rw [mul_sub, sub_eq_zero] at e
  simp only [Finset.sum_mul, smul_mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one] at e
  have e2 := congrArg L e
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hL, smul_smul] at e2
  exact e2

theorem annihilator_diagonal_trace {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    {d : ℕ} (b : Module.Basis (Fin d) R B) (M : Matrix (Fin d) (Fin d) R)
    (h : ∀ x : B, (∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j)) *
      (TensorProduct.tmul R x 1 - TensorProduct.tmul R 1 x) = 0) :
    ∑ i, ∑ j, (M i j * Algebra.trace R B (b i)) • b j = ∑ i, ∑ j, M i j • (b i * b j) := by
  classical
  have htr : ∀ z : B, Algebra.trace R B z = ∑ k, b.repr (z * b k) k := by
    intro z
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
    simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  have key : ∀ k, ∑ i, ∑ j, (M i j * b.repr (b i * b k) k) • b j =
      ∑ i, ∑ j, (M i j * b.repr (b i) k) • (b j * b k) :=
    fun k => annihilator_diagonal_form_swap (fun i => b i) M h (b.coord k) (b k)
  have hij : ∀ i j, ∑ k, (M i j * b.repr (b i) k) • (b j * b k) = M i j • (b i * b j) := by
    intro i j
    conv_rhs => rw [mul_comm, ← b.sum_repr (b i)]
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, smul_smul]
  calc ∑ i, ∑ j, (M i j * Algebra.trace R B (b i)) • b j
      = ∑ i, ∑ j, ∑ k, (M i j * b.repr (b i * b k) k) • b j := by
        simp only [htr, Finset.mul_sum, Finset.sum_smul]
    _ = ∑ k, ∑ i, ∑ j, (M i j * b.repr (b i * b k) k) • b j := by
        symm
        exact Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => Finset.sum_comm)
    _ = ∑ k, ∑ i, ∑ j, (M i j * b.repr (b i) k) • (b j * b k) :=
        Finset.sum_congr rfl fun k _ => key k
    _ = ∑ i, ∑ j, ∑ k, (M i j * b.repr (b i) k) • (b j * b k) :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => Finset.sum_comm)
    _ = ∑ i, ∑ j, M i j • (b i * b j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hij i j

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EntireEqZeroOrEqZeroOfMulEqZero
section
namespace GlobalTheory

theorem entire_eq_zero_or_eq_zero_of_mul_eq_zero {g : ℕ} (A B : (Fin g → ℂ) → ℂ)
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B) (hAB : ∀ z, A z * B z = 0) :
    (∀ z, A z = 0) ∨ (∀ z, B z = 0) := by
  by_cases hz : ∀ z, A z = 0
  · exact Or.inl hz
  right
  obtain ⟨z0, hz0⟩ := not_forall.1 hz
  intro z
  have hLd : Differentiable ℂ (fun t : ℂ => z0 + t • (z - z0)) := by fun_prop
  have ha : Differentiable ℂ (fun t : ℂ => A (z0 + t • (z - z0))) := hA.comp hLd
  have hb : Differentiable ℂ (fun t : ℂ => B (z0 + t • (z - z0))) := hB.comp hLd
  have ha0 : ∀ᶠ t in nhds (0 : ℂ), A (z0 + t • (z - z0)) ≠ 0 := by
    have h0 : A (z0 + (0 : ℂ) • (z - z0)) ≠ 0 := by simpa using hz0
    exact ha.continuous.continuousAt.eventually_ne h0
  have hb0 : (fun t : ℂ => B (z0 + t • (z - z0))) =ᶠ[nhds (0 : ℂ)] 0 := by
    filter_upwards [ha0] with t ht
    exact (mul_eq_zero.1 (hAB (z0 + t • (z - z0)))).resolve_left ht
  have hbA : AnalyticOnNhd ℂ (fun t : ℂ => B (z0 + t • (z - z0))) Set.univ := fun t _ => hb.analyticAt t
  have h1 := hbA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) hb0
    (Set.mem_univ (1 : ℂ))
  simpa using h1

theorem entire_eq_mul_of_sq_eq_mul_sq :
    ∀ (g : ℕ) (f h q : (Fin g → ℂ) → ℂ) (C : ℂ), Differentiable ℂ f → Differentiable ℂ h →
      Differentiable ℂ q → (∀ z, f z ^ 2 = C * Complex.exp (2 * q z) * h z ^ 2) →
      ∃ c : ℂ, c ^ 2 = C ∧ ∀ z, f z = c * Complex.exp (q z) * h z := by
  intro g f h q C hf hh hq hsq
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq C (by norm_num : 0 < 2)
  have hF : Differentiable ℂ fun z => f z * Complex.exp (-q z) := hf.mul hq.neg.cexp
  have key : ∀ z, (f z * Complex.exp (-q z) - c * h z) * (f z * Complex.exp (-q z) + c * h z) = 0 := by
    intro z
    have e1 : Complex.exp (-q z) ^ 2 * Complex.exp (2 * q z) = 1 := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      convert Complex.exp_zero using 2
      push_cast
      ring
    linear_combination Complex.exp (-q z) ^ 2 * hsq z + C * h z ^ 2 * e1 - h z ^ 2 * hc
  have e2 : ∀ z, Complex.exp (-q z) * Complex.exp (q z) = 1 := by
    intro z
    rw [← Complex.exp_add]
    simp
  rcases entire_eq_zero_or_eq_zero_of_mul_eq_zero (fun z => f z * Complex.exp (-q z) - c * h z)
      (fun z => f z * Complex.exp (-q z) + c * h z) (hF.sub ((differentiable_const c).mul hh))
      (hF.add ((differentiable_const c).mul hh)) key with h1 | h1
  · refine ⟨c, hc, fun z => ?_⟩
    linear_combination Complex.exp (q z) * h1 z - f z * e2 z
  · refine ⟨-c, by rw [neg_sq]; exact hc, fun z => ?_⟩
    linear_combination Complex.exp (q z) * h1 z - f z * e2 z

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsAlgHomNeZeroOfCountable
section
namespace GlobalTheory

theorem exists_eval_ne_zero_of_countable {σ : Type} [Finite σ] (T : Set (MvPolynomial σ ℂ))
    (hT : T.Countable) (h0 : (0 : MvPolynomial σ ℂ) ∉ T) :
    ∃ c : σ → ℂ, ∀ p ∈ T, MvPolynomial.eval c p ≠ 0 := by
  classical
  have := Fintype.ofFinite σ
  have hd : Dense (⋂ p ∈ T, {c : σ → ℂ | MvPolynomial.eval c p ≠ 0}) := by
    refine dense_biInter_of_isOpen (fun p _ => ?_) hT (fun p hp => ?_)
    · exact isOpen_ne_fun (MvPolynomial.continuous_eval p) continuous_const
    · intro c
      by_contra hc
      have hev : (fun c : σ → ℂ => MvPolynomial.eval c p) =ᶠ[nhds c] 0 := by
        have h1 : (closure {c : σ → ℂ | MvPolynomial.eval c p ≠ 0})ᶜ ∈ nhds c :=
          isClosed_closure.isOpen_compl.mem_nhds hc
        filter_upwards [h1] with x hx
        by_contra hx'
        exact hx (subset_closure hx')
      have hz := (AnalyticOnNhd.eval_mvPolynomial p).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ c) hev
      have : p = 0 := MvPolynomial.funext fun x => by
        simpa using hz (Set.mem_univ x)
      exact h0 (this ▸ hp)
  obtain ⟨c, hc⟩ := hd.nonempty
  exact ⟨c, fun p hp => Set.mem_iInter₂.1 hc p hp⟩

theorem exists_algHom_ne_zero_of_countable (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E]
    [Algebra.FiniteType ℂ E] (T : Set E) (hT : T.Countable) (h0 : (0 : E) ∉ T) :
    ∃ s : E →ₐ[ℂ] ℂ, ∀ r ∈ T, s r ≠ 0 := by
  classical
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ E
  letI : Algebra (MvPolynomial (Fin d) ℂ) E := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin d) ℂ) E := hfin
  have hn : ∀ r : E, r ≠ 0 → ∃ n : MvPolynomial (Fin d) ℂ, n ≠ 0 ∧
      algebraMap (MvPolynomial (Fin d) ℂ) E n ∈ Ideal.span {r} := by
    intro r hr
    have := Ideal.comap_ne_bot_of_integral_mem (R := MvPolynomial (Fin d) ℂ)
      (I := Ideal.span {r}) hr (Ideal.mem_span_singleton_self r)
      (Algebra.IsIntegral.isIntegral r)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
    exact ⟨n, hn0, hn⟩
  choose! n hn0 hnr using hn
  have hne : ∀ r ∈ T, r ≠ 0 := fun r hr h => h0 (h ▸ hr)
  obtain ⟨c, hc⟩ := exists_eval_ne_zero_of_countable (n '' T) (hT.image n) (by
    rintro ⟨r, hr, h⟩
    exact hn0 r (hne r hr) h)
  have hsurj : Function.Surjective (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ) :=
    fun z => ⟨MvPolynomial.C z, by simp⟩
  haveI hmax : (RingHom.ker (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ hsurj
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := E)
    (RingHom.ker (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ)) (by
      have : RingHom.ker (algebraMap (MvPolynomial (Fin d) ℂ) E) = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot _).1 hinj
      rw [this]
      exact bot_le)
  letI : Field (E ⧸ Q) := Ideal.Quotient.field Q
  haveI : Module.Finite ℂ (E ⧸ Q) := finite_of_finite_type_of_isJacobsonRing ℂ (E ⧸ Q)
  have hbij : Function.Bijective (Algebra.ofId ℂ (E ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃ₐ[ℂ] (E ⧸ Q) := AlgEquiv.ofBijective _ hbij
  refine ⟨(e.symm : (E ⧸ Q) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ Q), fun r hr h => ?_⟩
  have h1 : Ideal.Quotient.mk Q r = 0 := by
    apply e.symm.injective
    rw [map_zero]
    exact h
  have h2 : r ∈ Q := Ideal.Quotient.eq_zero_iff_mem.1 h1
  have h3 : n r ∈ Q.under (MvPolynomial (Fin d) ℂ) :=
    (Ideal.mem_under (MvPolynomial (Fin d) ℂ) Q).2
      ((Ideal.span_singleton_le_iff_mem Q).2 h2 (hnr r (hne r hr)))
  rw [hQp] at h3
  exact hc (n r) ⟨r, hr, rfl⟩ h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsAlgHomOfIsTranscendenceBasis
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericValue

open MvPolynomial

variable {K : Type} [Field K]

theorem exists_algHom_of_isTranscendenceBasis {E Ω ι : Type} [Field E] [Algebra K E] [Field Ω] [IsAlgClosed Ω]
    [Algebra K Ω] {v : ι → E} (hv : IsTranscendenceBasis K v) {T : ι → Ω} (hT : AlgebraicIndependent K T) :
    ∃ j : E →ₐ[K] Ω, ∀ i, j (v i) = T i := by
  let A := Algebra.adjoin K (Set.range v)
  let g : A →ₐ[K] Ω := (aeval T).comp hv.1.aevalEquiv.symm.toAlgHom
  have hg : Function.Injective g := fun p q h =>
    hv.1.aevalEquiv.symm.injective (algebraicIndependent_iff_injective_aeval.1 hT h)
  letI : Algebra A Ω := g.toRingHom.toAlgebra
  haveI : IsScalarTower K A Ω := IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  haveI : FaithfulSMul A Ω := (faithfulSMul_iff_algebraMap_injective A Ω).2 hg
  haveI := hv.isAlgebraic
  let j : E →ₐ[A] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨j.restrictScalars K, fun i => ?_⟩
  have h := j.commutes (hv.1.aevalEquiv (X i))
  have e : algebraMap A E (hv.1.aevalEquiv (X i)) = v i := by
    rw [hv.1.algebraMap_aevalEquiv, aeval_X]
  rw [e] at h
  refine h.trans ?_
  show aeval T (hv.1.aevalEquiv.symm (hv.1.aevalEquiv (X i))) = T i
  rw [AlgEquiv.symm_apply_apply, aeval_X]

theorem algebraicIndependent_add_one {E ι : Type} [CommRing E] [Algebra K E] {v : ι → E}
    (hv : AlgebraicIndependent K v) : AlgebraicIndependent K fun i => v i + 1 := by
  have h₁ : AlgebraicIndependent K fun i : ι => (X i + 1 : MvPolynomial ι K) := by
    refine AlgebraicIndependent.of_comp (aeval fun i : ι => (X i - 1 : MvPolynomial ι K)) ?_
    convert algebraicIndependent_X ι K using 1
    ext i
    simp
  convert h₁.map' (algebraicIndependent_iff_injective_aeval.1 hv) using 1
  ext i
  simp

theorem mem_range_of_fixed [IsAlgClosed K] {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (a : Ω)
    (h : ∀ j : Ω →ₐ[K] Ω, j a = a) : a ∈ Set.range (algebraMap K Ω) := by
  by_contra ha
  have ht : Transcendental K a := fun hal => ha <| by
    have := minpoly.mem_range_of_degree_eq_one K a
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hal.isIntegral))
    exact this
  have hi : AlgebraicIndepOn K id ({a} : Set Ω) := by
    unfold AlgebraicIndepOn
    exact (algebraicIndependent_singleton_iff (⟨a, rfl⟩ : ({a} : Set Ω))).2 ht
  obtain ⟨t, hst, hb⟩ := exists_isTranscendenceBasis_superset hi
  obtain ⟨j, hj⟩ := exists_algHom_of_isTranscendenceBasis hb (algebraicIndependent_add_one hb.1)
  have := (h j).symm.trans (hj ⟨a, hst rfl⟩)
  simp at this

abbrev Gen (F I : Type) [Field F] : Type := AlgebraicClosure (FractionRing (MvPolynomial I F))

def genX (F I : Type) [Field F] : I → Gen F I := fun i => algebraMap (MvPolynomial I F) _ (X i)

theorem isTranscendenceBasis_genX (F I : Type) [Field F] : IsTranscendenceBasis F (genX F I) := by
  haveI : Algebra.IsAlgebraic (MvPolynomial I F) (FractionRing (MvPolynomial I F)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  haveI : Algebra.IsAlgebraic (MvPolynomial I F) (Gen F I) :=
    Algebra.IsAlgebraic.trans _ (FractionRing (MvPolynomial I F)) _
  haveI : FaithfulSMul (MvPolynomial I F) (Gen F I) := (faithfulSMul_iff_algebraMap_injective _ _).2 <| by
    rw [IsScalarTower.algebraMap_eq _ (FractionRing (MvPolynomial I F))]
    exact (algebraMap (FractionRing (MvPolynomial I F)) (Gen F I)).injective.comp (IsFractionRing.injective _ _)
  exact (IsTranscendenceBasis.mvPolynomial I F).algebraMap_comp

theorem exists_generization {F I : Type} [Field F] [Algebra K F] (T : I → F) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Algebra K O)
      (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra K Ω) (r : O →ₐ[K] Ω) (e : F →ₐ[K] Ω) (S : I → O),
      RingHom.ker r = IsLocalRing.maximalIdeal O ∧ AlgebraicIndependent K S ∧ r ∘ S = e ∘ T := by
  let Ω := Gen F I
  let P : I → Polynomial Ω := fun i => Polynomial.C (algebraMap F Ω (T i)) +
    Polynomial.C (genX F I i - algebraMap F Ω (T i)) * Polynomial.X
  have hX : AlgebraicIndependent K (genX F I) :=
    (isTranscendenceBasis_genX F I).1.restrictScalars (algebraMap K F).injective
  have hP : AlgebraicIndependent K P := by
    refine AlgebraicIndependent.of_comp ((Polynomial.aeval (1 : Ω)).restrictScalars K) ?_
    convert hX using 1
    ext i
    simp [P]
  let c : Polynomial Ω →ₐ[K] PowerSeries Ω := (Polynomial.coeToPowerSeries.algHom Ω).restrictScalars K
  have hc : Function.Injective c := by
    intro p q h
    apply Polynomial.coe_injective Ω
    simpa [c] using h
  let r : PowerSeries Ω →ₐ[K] Ω :=
    { PowerSeries.constantCoeff (R := Ω) with commutes' := fun a => by simp [PowerSeries.algebraMap_apply] }
  refine ⟨PowerSeries Ω, inferInstance, inferInstance, inferInstance, inferInstance, Ω, inferInstance, inferInstance,
    inferInstance, r, IsScalarTower.toAlgHom K F Ω, c ∘ P, ?_, hP.map' hc, ?_⟩
  · exact PowerSeries.ker_coeff_eq_max_ideal
  · ext i
    simp [r, c, P]

theorem exists_value [IsAlgClosed K] {I : Type}
    (V : ∀ (R : Type) [CommRing R] [Algebra K R], (I → R) → R → Prop)
    (bc : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R']
      [Algebra K R] [Algebra K R'] (j : R →ₐ[K] R') (T : I → R) (a : R), V R T a → V R' (j ∘ T) (j a))
    (uniq : ∀ (F : Type) [Field F] [Algebra K F] (T : I → F) (a a' : F), V F T a → V F T a' → a = a')
    (ex : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (T : I → Ω), AlgebraicIndependent K T → ∃ a, V Ω T a)
    (gg : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (T T' : I → Ω) (a a' : Ω),
      AlgebraicIndependent K (Sum.elim T T') → V Ω T a → V Ω T' a' → a = a')
    (lift : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra K O] (Ω : Type) [Field Ω]
      [IsAlgClosed Ω] [Algebra K Ω] (r : O →ₐ[K] Ω) (T : I → O) (a : Ω),
      RingHom.ker r = IsLocalRing.maximalIdeal O → V Ω (r ∘ T) a →
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : Algebra K O')
        (j : O →ₐ[K] O') (r' : O' →ₐ[K] Ω) (u : O'), Function.Injective j ∧ r'.comp j = r ∧ V O' (j ∘ T) u) :
    ∃ κ : K, (∀ (F : Type) [Field F] [Algebra K F] (T : I → F) (a : F), V F T a → a = algebraMap K F κ) ∧
      V (Gen K I) (genX K I) (algebraMap K _ κ) := by
  have hA : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (T T' : I → Ω) (a a' : Ω),
      AlgebraicIndependent K T → AlgebraicIndependent K T' → V Ω T a → V Ω T' a' → a = a' := by
    intro Ω _ _ _ T T' a a' hT hT' h h'
    let j := IsScalarTower.toAlgHom K Ω (Gen Ω I)
    have hX := (isTranscendenceBasis_genX Ω I).1
    obtain ⟨b, hb⟩ := ex (Gen Ω I) _ (hX.restrictScalars (algebraMap K Ω).injective)
    have key : ∀ (S : I → Ω) (c : Ω), AlgebraicIndependent K S → V Ω S c → b = j c := fun S c hS hc =>
      gg (Gen Ω I) _ _ _ _ (hS.sumElim_comp hX) hb (bc Ω _ j S c hc)
    exact j.toRingHom.injective ((key T a hT h).symm.trans (key T' a' hT' h'))
  have hB := isTranscendenceBasis_genX K I
  obtain ⟨a₁, ha₁⟩ := ex (Gen K I) _ hB.1
  obtain ⟨κ, rfl⟩ := mem_range_of_fixed (K := K) a₁ fun j =>
    hA _ _ _ _ _ (hB.1.map' j.toRingHom.injective) hB.1 (bc _ _ j _ _ ha₁) ha₁
  refine ⟨κ, fun F _ _ T a h => ?_, ha₁⟩
  obtain ⟨O, _, _, _, _, Ω, _, _, _, r, e, S, hr, hS, hT⟩ := exists_generization (K := K) T
  have h₁ := bc _ _ e T a h
  rw [← hT] at h₁
  obtain ⟨O', _, _, _, _, j, r', u, hj, hr', hu⟩ := lift O Ω r S _ hr h₁
  have h₂ := bc _ _ r' _ _ hu
  rw [← Function.comp_assoc, ← AlgHom.coe_comp, hr'] at h₂
  have h₃ := uniq _ _ _ _ h₁ h₂
  let Ω' := AlgebraicClosure (FractionRing O')
  let i := IsScalarTower.toAlgHom K O' Ω'
  have hi : Function.Injective i := by
    show Function.Injective (algebraMap O' Ω')
    rw [IsScalarTower.algebraMap_eq _ (FractionRing O')]
    exact (algebraMap (FractionRing O') Ω').injective.comp (IsFractionRing.injective _ _)
  obtain ⟨m, hm⟩ := exists_algHom_of_isTranscendenceBasis hB ((hS.map' hj).map' hi)
  have h₄ := bc _ _ m _ _ ha₁
  rw [show m ∘ genX K I = i ∘ j ∘ S from funext hm] at h₄
  have h₅ : u = algebraMap K O' κ := hi ((uniq _ _ _ _ (bc _ _ i _ _ hu) h₄).trans (by simp))
  apply e.toRingHom.injective
  simpa [h₅] using h₃

end GlobalTheory.GenericValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsCountableLocalPidSubring
section
namespace GlobalTheory

theorem exists_countable_local_pid_subring (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsPrincipalIdealRing R] (S : Set R) (hS : S.Countable) :
    ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀),
      Countable R₀ ∧ S ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ Module.FaithfullyFlat R₀ R := by
  classical
  let K := FractionRing R
  let K₀ : Subfield K := Subfield.closure (algebraMap R K '' S)
  let R₀ : Subring R := K₀.toSubring.comap (algebraMap R K)
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmem : ∀ x : R, x ∈ R₀ ↔ algebraMap R K x ∈ K₀ := fun x => Iff.rfl
  have hdvd : ∀ a b : R₀, (a : R) ∣ (b : R) → a ∣ b := by
    rintro a b ⟨c, hc⟩
    by_cases ha : (a : R) = 0
    · have : b = 0 := Subtype.ext (by rw [hc, ha]; simp)
      rw [this]; exact dvd_zero _
    · have ha' : algebraMap R K a ≠ 0 := fun h => ha (hinj (by simpa using h))
      have hcm : c ∈ R₀ := by
        rw [hmem]
        have : algebraMap R K c = algebraMap R K b / algebraMap R K a := by
          rw [hc, map_mul, mul_div_cancel_left₀ _ ha']
        rw [this]
        exact K₀.div_mem ((hmem _).1 b.2) ((hmem _).1 a.2)
      exact ⟨⟨c, hcm⟩, Subtype.ext hc⟩
  have hloc : IsLocalHom R₀.subtype := ⟨fun a ha => by
    rw [isUnit_iff_dvd_one] at ha ⊢
    exact hdvd a 1 ha⟩
  have hlr : IsLocalRing R₀ := RingHom.domain_isLocalRing R₀.subtype
  have hpid : IsPrincipalIdealRing R₀ := ⟨fun I => by
    obtain ⟨M, ⟨a, haI, rfl⟩, hM⟩ := set_has_maximal_iff_noetherian.mpr
      (inferInstance : IsNoetherian R R)
      {J : Ideal R | ∃ a : R₀, a ∈ I ∧ Ideal.span {(a : R)} = J} ⟨_, 0, I.zero_mem, rfl⟩
    refine ⟨⟨a, le_antisymm (fun b hb => ?_) ?_⟩⟩
    · change b ∈ Ideal.span {a}
      rw [Ideal.mem_span_singleton]
      apply hdvd
      rcases ValuationRing.dvd_total (a : R) (b : R) with h | h
      · exact h
      · have h1 : Ideal.span {(a : R)} ≤ Ideal.span {(b : R)} :=
          Ideal.span_singleton_le_span_singleton.mpr h
        have h2 := hM _ ⟨b, hb, rfl⟩
        exact Ideal.span_singleton_le_span_singleton.mp (eq_of_le_of_not_lt h1 h2).ge
    · exact (Ideal.span_singleton_le_iff_mem I).mpr haI⟩
  have hK : Countable K₀ := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (Subfield.cardinalMk_closure_le_max _).trans (max_le ?_ le_rfl)
    rw [Cardinal.mk_le_aleph0_iff]
    exact (hS.image _).to_subtype
  have hc : Countable R₀ := by
    let f : R₀ → K₀ := fun x => ⟨algebraMap R K x, (hmem _).1 x.2⟩
    have : Function.Injective f := fun x y h =>
      Subtype.ext (hinj (congrArg Subtype.val h))
    exact this.countable
  refine ⟨R₀, hlr, hpid, hc, fun x hx => Subfield.subset_closure ⟨x, hx, rfl⟩, hloc, ?_⟩
  have : IsLocalHom (algebraMap R₀ R) := hloc
  have : Module.Flat R₀ R := inferInstance
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsSymmMulVecAddDiagModTwo
section
namespace GlobalTheory

theorem exists_isSymm_mulVec_add_diag_mod_two :
    ∀ (g : ℕ) (n n' : Fin g → ℤ), Even (n ⬝ᵥ n') →
      ∃ S : Matrix (Fin g) (Fin g) ℤ, S.IsSymm ∧
        ∀ i, (2 : ℤ) ∣ (S.mulVec n) i + S i i - n' i := by
  intro g n n' h
  by_cases hall : ∀ i, Even (n i)
  · refine ⟨Matrix.diagonal n', Matrix.isSymm_diagonal _, fun i => ?_⟩
    obtain ⟨k, hk⟩ := hall i
    rw [Matrix.mulVec_diagonal, Matrix.diagonal_apply_eq, hk]
    exact ⟨n' i * k, by ring⟩
  · obtain ⟨p, hp⟩ := not_forall.mp hall
    obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hp
    obtain ⟨m, hm⟩ := h
    refine ⟨Matrix.of fun i j => (if i = p then n' j else 0) + (if j = p then n' i else 0),
      ?_, fun i => ?_⟩
    · ext i j
      simp only [Matrix.transpose_apply, Matrix.of_apply]
      ring
    · have hm' : ∑ j, n' j * n j = m + m := by
        rw [← hm]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      have h2 : ∑ j, (if j = p then n' i else 0) * n j = n' i * n p := by
        simp
      by_cases hi : i = p
      · subst hi
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
          if_true, hm', h2, hk]
        exact ⟨m + n' i * k + n' i, by ring⟩
      · simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
          if_neg hi, h2, hk, zero_mul, Finset.sum_const_zero]
        exact ⟨n' i * k, by ring⟩

end GlobalTheory
end

