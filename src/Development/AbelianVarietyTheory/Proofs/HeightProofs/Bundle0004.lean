module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SchurLatticeConjugates
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.BeSumStatementIffDefectSumBound
section
open NumberField IsDedekindDomain Pointwise Formalism.L2.Pj.QAt GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

namespace GlobalTheory.DefectSumCompare

theorem pow_finrank_eq_span_absNorm {E : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hfix : ∀ σ : E ≃ₐ[ℚ] E, σ • I = I) :
    I ^ Module.finrank ℚ E = Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 E)} := by
  classical
  have hI0 : I ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 E)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have hprin : (I ^ h).IsPrincipal := by
    have h1 : ClassGroup.mk0 (⟨I, hI0⟩ ^ h) = 1 := by rw [map_pow, pow_card_eq_one]
    exact (ClassGroup.mk0_eq_one_iff (pow_mem hI0 h)).1 h1
  obtain ⟨x, hx⟩ := hprin
  have hx' : I ^ h = Ideal.span {x} := hx
  have hσ : ∀ σ : E ≃ₐ[ℚ] E, Ideal.span {σ • x} = I ^ h := by
    intro σ
    have : σ • (I ^ h) = I ^ h := by rw [smul_pow', hfix]
    rw [← this, hx', Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
    rfl
  have hnorm : ((Algebra.norm ℤ x : ℤ) : 𝓞 E) = ∏ σ : E ≃ₐ[ℚ] E, σ • x := by
    apply RingOfIntegers.ext
    have h1 := Algebra.norm_eq_prod_automorphisms ℚ (x : E)
    rw [← Algebra.coe_norm_int] at h1
    change algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
    rw [map_prod, map_intCast]
    rw [map_intCast] at h1
    exact h1
  have h2 : Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 E)} ^ h = (I ^ Module.finrank ℚ E) ^ h := by
    rw [Ideal.span_singleton_pow, ← Nat.cast_pow, ← map_pow, hx', Ideal.absNorm_span_singleton]
    have h3 : Ideal.span {(((Algebra.norm ℤ x).natAbs : ℕ) : 𝓞 E)} =
        Ideal.span {((Algebra.norm ℤ x : ℤ) : 𝓞 E)} := by
      rcases Int.natAbs_eq (Algebra.norm ℤ x) with h4 | h4
      · conv_rhs => rw [h4]
        rw [Int.cast_natCast]
      · conv_rhs => rw [h4]
        rw [Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]
    rw [h3, hnorm, ← Ideal.prod_span_singleton]
    simp only [hσ]
    rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      ← pow_mul, ← pow_mul, mul_comm]
  exact (pow_left_injective hpos h2).symm

theorem ord_vw_eq_vla {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : ord_vw la I = vla la I := by
  classical
  unfold ord_vw vla
  rw [Ideal.count_associates_factors_eq hI la.isPrime la.ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hI]

theorem lrd_eq_lrdOf (E : Type) [Field E] [NumberField E] : lrd E = lrdOf E := by
  unfold lrd lrdOf
  rw [rootDiscr_def, one_div, Int.cast_abs]

theorem log_discr_eq (E : Type) [Field E] [NumberField E] :
    Real.log |((discr E : ℤ) : ℝ)| = (Module.finrank ℚ E : ℝ) * lrd E := by
  have hd : (0 : ℝ) < |((discr E : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero E))
  have hn : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [lrd_eq_lrdOf]
  unfold lrdOf
  rw [Real.log_rpow hd]
  field_simp

theorem conjDifferent_pow {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K]
    (σ : E →+* K) : conjDifferent σ ^ Module.finrank ℚ E = discAt E K := by
  unfold conjDifferent discAt
  rw [← Ideal.map_pow, pow_finrank_eq_span_absNorm _ differentIdeal_ne_bot
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.smul_differentIdeal, absNorm_differentIdeal E, Ideal.map_span,
    Set.image_singleton, map_natCast]

theorem vla_pow {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (k : ℕ) : vla la (I ^ k) = k * vla la I := by
  unfold vla
  rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr hI) la.associates_irreducible]

section Galois

variable {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K]

theorem vla_discAt (σ : E →+* K) (la : HeightOneSpectrum (𝓞 K)) :
    vla la (discAt E K) = Module.finrank ℚ E * ord_vw la (conjDifferent σ) := by
  rw [← conjDifferent_pow σ, vla_pow la (conjDifferent_ne_bot σ), ord_vw_eq_vla la (conjDifferent_ne_bot σ)]

end Galois

end GlobalTheory.DefectSumCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.BicommutantTensorFactorPermMemSpan
section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

theorem bicomm_left_mul {ι G : Type} [Fintype ι] [DecidableEq ι] (ρ : G → Matrix ι ι ℂ)
    (p : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ) (hp : ∀ g X, p (ρ g * X) = ρ g * p X) (M : Matrix ι ι ℂ)
    (hM : ∀ T : Matrix ι ι ℂ, (∀ g, T * ρ g = ρ g * T) → M * T = T * M) (X : Matrix ι ι ℂ) :
    p (M * X) = M * p X := by
  have key : ∀ (A : Matrix ι ι ℂ) (i j a b : ι),
      ((Matrix.of fun a b => p (Matrix.single b i 1) a j) * A) a b = p (A * Matrix.single b i 1) a j := by
    intro A i j a b
    have : A * Matrix.single b i 1 = ∑ c, A c b • Matrix.single c i (1 : ℂ) := by
      ext x y
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.single_apply, smul_eq_mul]
      by_cases h : i = y <;> simp [h]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    simp only [Matrix.mul_apply, Matrix.sum_apply, map_smul, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, mul_comm]
  have key2 : ∀ (A : Matrix ι ι ℂ) (i j a b : ι),
      (A * (Matrix.of fun a b => p (Matrix.single b i 1) a j)) a b = (A * p (Matrix.single b i 1)) a j := by
    intro A i j a b
    simp [Matrix.mul_apply]
  have h1 : ∀ b i, p (M * Matrix.single b i 1) = M * p (Matrix.single b i 1) := by
    intro b i
    ext a j
    rw [← key, ← key2, hM]
    intro g
    ext a b
    rw [key, key2, hp]
  have h2 : X = ∑ b, ∑ i, X b i • Matrix.single b i (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp [Matrix.smul_single]
  rw [h2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_sum, map_sum, Matrix.mul_smul, map_smul, h1]

theorem bicomm_mem_span {ι G : Type} [Fintype ι] [DecidableEq ι] [Group G] [Fintype G] (ρ : G → Matrix ι ι ℂ)
    (h1 : ρ 1 = 1) (hmul : ∀ g h, ρ g * ρ h = ρ (h * g)) (M : Matrix ι ι ℂ)
    (hM : ∀ T : Matrix ι ι ℂ, (∀ g, T * ρ g = ρ g * T) → M * T = T * M) :
    M ∈ Submodule.span ℂ (Set.range ρ) := by
  set B := Submodule.span ℂ (Set.range ρ) with hB
  have hst : ∀ g, ∀ X ∈ B, ρ g * X ∈ B := by
    intro g X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [hmul]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mul_add]; exact B.add_mem hx hy
    | smul c x _ hx => rw [Matrix.mul_smul]; exact B.smul_mem c hx
  obtain ⟨q, hq⟩ := LinearMap.exists_extend (LinearMap.id : B →ₗ[ℂ] B)
  have hq' : ∀ X ∈ B, (q X : Matrix ι ι ℂ) = X := fun X hX => by
    have := LinearMap.congr_fun hq ⟨X, hX⟩
    exact congrArg Subtype.val this
  let p : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
    ∑ g : G, LinearMap.mulLeft ℂ (ρ g⁻¹) ∘ₗ B.subtype ∘ₗ q ∘ₗ LinearMap.mulLeft ℂ (ρ g)
  have hp : ∀ X, p X = ∑ g : G, ρ g⁻¹ * (q (ρ g * X) : Matrix ι ι ℂ) := fun X => by
    simp [p, LinearMap.sum_apply]
  have hpB : ∀ X, p X ∈ B := fun X => by
    rw [hp]
    exact B.sum_mem fun g _ => hst _ _ (q _).2
  have hone : (1 : Matrix ι ι ℂ) ∈ B := Submodule.subset_span ⟨1, h1⟩
  have hp1 : p 1 = (Fintype.card G : ℂ) • (1 : Matrix ι ι ℂ) := by
    rw [hp]
    have : ∀ g : G, ρ g⁻¹ * (q (ρ g * 1) : Matrix ι ι ℂ) = 1 := fun g => by
      rw [hq' _ (hst _ _ hone), mul_one, hmul, mul_inv_cancel, h1]
    simp only [this]
    rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hpρ : ∀ h X, p (ρ h * X) = ρ h * p X := fun h X => by
    rw [hp, hp, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft]
    rw [← mul_assoc, hmul, ← mul_assoc, hmul]
    simp
  have := bicomm_left_mul ρ p hpρ M hM 1
  rw [hp1, mul_one, Matrix.mul_smul, mul_one] at this
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h3 := B.smul_mem (Fintype.card G : ℂ)⁻¹ (hpB M)
  rwa [this, smul_smul, inv_mul_cancel₀ hc, one_smul] at h3

theorem bicomm_permMat : ∀ (n d : ℕ) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ), (∀ T : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ, (∀ π, T * permMat n d π = permMat n d π * T) → M * T = T * M) → M ∈ Submodule.span ℂ (Set.range (permMat n d)) := by
  intro n d M hM
  refine bicomm_mem_span (permMat n d) ?_ ?_ M hM
  · ext I K
    simp [permMat, Matrix.one_apply]
  · intro g h
    ext I K
    simp only [permMat, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single (K ∘ h)]
    · rw [if_pos rfl, mul_one]
      rfl
    · intro J _ hJ
      simp [hJ]
    · simp

end GlobalTheory.SmoothForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutantLiftModStableSelfAdjoint
section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory

theorem matrix_exists_sub_mem_trace_orthogonal {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Submodule ℂ (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    ∃ M₀ : Matrix ι ι ℂ, M - M₀ ∈ N ∧ ∀ n ∈ N, (nᴴ * M₀).trace = 0 := by
  let e : Matrix ι ι ℂ →ₗ[ℂ] EuclideanSpace ℂ (ι × ι) :=
    { toFun := fun A => WithLp.toLp 2 (fun p : ι × ι => A p.1 p.2)
      map_add' := fun A B => rfl
      map_smul' := fun c A => rfl }
  have hin : ∀ A B : Matrix ι ι ℂ, inner ℂ (e A) (e B) = (Aᴴ * B).trace := by
    intro A B
    simp only [e, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply, Matrix.trace,
      Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm]
    rfl
  obtain ⟨y, hy, z, hz, h⟩ := (N.map e).exists_add_mem_mem_orthogonal (e M)
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨M - y', by simpa using hy', fun n hn => ?_⟩
  rw [← hin, map_sub, h, add_sub_cancel_left]
  exact (Submodule.mem_orthogonal _ _).1 hz _ ⟨n, hn, rfl⟩

theorem matrix_commutant_lift_mod_stable :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (Matrix ι ι ℂ))
      (N : Submodule ℂ (Matrix ι ι ℂ)), (∀ x ∈ S, xᴴ ∈ S) →
      (∀ x ∈ S, ∀ y ∈ N, x * y - y * x ∈ N) → ∀ M : Matrix ι ι ℂ,
      (∀ x ∈ S, x * M - M * x ∈ N) →
      ∃ M₀ : Matrix ι ι ℂ, M - M₀ ∈ N ∧ ∀ x ∈ S, x * M₀ = M₀ * x := by
  intro ι _ _ S N hS hN M hM
  obtain ⟨M₀, h1, h2⟩ := matrix_exists_sub_mem_trace_orthogonal N M
  refine ⟨M₀, h1, fun x hx => ?_⟩
  have hw : x * M₀ - M₀ * x ∈ N := by
    have := N.sub_mem (hM x hx) (hN x hx _ h1)
    convert this using 1
    noncomm_ring
  set w := x * M₀ - M₀ * x with hwdef
  have h3 := h2 _ (hN _ (hS x hx) w hw)
  have h4 : (wᴴ * w).trace = 0 := by
    rw [← h3]
    have : (wᴴ * (M₀ * x)).trace = (x * wᴴ * M₀).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    conv_lhs => rw [hwdef, Matrix.mul_sub, ← hwdef]
    rw [Matrix.trace_sub, this]
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_assoc]
  open scoped ComplexOrder in
  exact sub_eq_zero.1 (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h4)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutatorGlGeneratorTensorWordMapMatrixUnits
section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

theorem commutator_prod_ofFn {A : Type} [Ring A] (x : A) :
    ∀ (d : ℕ) (f : Fin d → A), x * (List.ofFn f).prod - (List.ofFn f).prod * x =
      ∑ p, (List.ofFn (Function.update f p (x * f p - f p * x))).prod
  | 0, f => by simp
  | d + 1, f => by
    have ih := commutator_prod_ofFn x d (fun i => f i.succ)
    have h : ∀ (p : Fin d) (y : A), (fun i : Fin d => Function.update f p.succ y i.succ) =
        Function.update (fun i => f i.succ) p y := fun p y => by
      funext i
      by_cases h : i = p
      · subst h; simp
      · simp [Function.update_of_ne h, Function.update_of_ne (fun h' => h (Fin.succ_injective _ h'))]
    rw [Fin.sum_univ_succ]
    simp only [List.ofFn_succ, List.prod_cons, Function.update_self, h,
      Function.update_of_ne (Fin.succ_ne_zero _), Function.update_of_ne (Fin.succ_ne_zero _).symm]
    rw [← Finset.mul_sum, ← ih]
    noncomm_ring

theorem sum_polar_left {A : Type} [AddCommGroup A] [Module ℂ A] {n d : ℕ} (a b : Fin n) (I : Fin d → Fin n)
    (g : (Fin d → Fin n) → A) :
    ∑ J, polar n d a b J I • g J = ∑ p, if b = I p then g (Function.update I p a) else 0 := by
  simp only [polar, Matrix.of_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : ∀ J : Fin d → Fin n, (J p = a ∧ I p = b ∧ ∀ q, q ≠ p → J q = I q) ↔
      (b = I p ∧ J = Function.update I p a) := fun J => by
    rw [Function.eq_update_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2.symm, h1, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1.symm, h3⟩
  simp only [h]
  by_cases hb : b = I p <;> simp [hb]

theorem sum_polar_right {A : Type} [AddCommGroup A] [Module ℂ A] {n d : ℕ} (a b : Fin n) (K : Fin d → Fin n)
    (g : (Fin d → Fin n) → A) :
    ∑ J, polar n d a b K J • g J = ∑ p, if K p = a then g (Function.update K p b) else 0 := by
  simp only [polar, Matrix.of_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : ∀ J : Fin d → Fin n, (K p = a ∧ J p = b ∧ ∀ q, q ≠ p → K q = J q) ↔
      (K p = a ∧ J = Function.update K p b) := fun J => by
    rw [Function.eq_update_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun q hq => (h3 q hq).symm⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun q hq => (h3 q hq).symm⟩
  simp only [h]
  by_cases hb : K p = a <;> simp [hb]

theorem commutator_word {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E)
    {d : ℕ} (a b : Fin n) (I K : Fin d → Fin n) :
    E a b * (List.ofFn fun q => E (I q) (K q)).prod - (List.ofFn fun q => E (I q) (K q)).prod * E a b =
      ∑ J, polar n d a b J I • (List.ofFn fun q => E (J q) (K q)).prod -
        ∑ J, polar n d a b K J • (List.ofFn fun q => E (I q) (J q)).prod := by
  rw [commutator_prod_ofFn, sum_polar_left, sum_polar_right, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h1 : (fun q => E (Function.update I p a q) (K q)) =
      Function.update (fun q => E (I q) (K q)) p (E a (K p)) := by
    funext q
    by_cases h : q = p
    · subst h; simp
    · simp [Function.update_of_ne h]
  have h2 : (fun q => E (I q) (Function.update K p b q)) =
      Function.update (fun q => E (I q) (K q)) p (E (I p) b) := by
    funext q
    by_cases h : q = p
    · subst h; simp
    · simp [Function.update_of_ne h]
  rw [h1, h2, hE a b (I p) (K p)]
  simp only [← MultilinearMap.mkPiAlgebraFin_apply (R := ℂ), MultilinearMap.map_update_sub]
  congr 1 <;> split_ifs <;> simp only [MultilinearMap.map_update_zero]

theorem commutator_wordMap : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A),
    Formalism.REAL.GlRel E → ∀ (d : ℕ) (a b : Fin n) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ),
    E a b * wordMap E d M - wordMap E d M * E a b =
      wordMap E d (polar n d a b * M - M * polar n d a b) := by
  intro A _ _ n E hE d a b M
  have hw : ∀ N, wordMap E d N = ∑ I, ∑ K, N I K • (List.ofFn fun q : Fin d => E (I q) (K q)).prod := fun _ => rfl
  have hl : wordMap E d (polar n d a b * M) =
      ∑ I, ∑ K, M I K • ∑ J, polar n d a b J I • (List.ofFn fun q => E (J q) (K q)).prod := by
    simp only [hw, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hr : wordMap E d (M * polar n d a b) =
      ∑ I, ∑ K, M I K • ∑ J, polar n d a b K J • (List.ofFn fun q => E (I q) (J q)).prod := by
    simp only [hw, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_comm]
  rw [map_sub, hl, hr, hw, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [← smul_sub, ← commutator_word hE, smul_sub, mul_smul_comm, smul_mul_assoc]

end GlobalTheory.SmoothForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CommutingAlgebrasFiniteSpan
section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.FiniteOrbit

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem exists_finiteDimensional_stable (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type)
    [Finite ι] (A : ι → Subalgebra ℂ (Module.End ℂ M))
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) (m : M)
    (hm : ∀ i, FiniteDimensional ℂ (Submodule.span ℂ {x : M | ∃ a ∈ A i, x = a m})) :
    ∃ W : Submodule ℂ M, FiniteDimensional ℂ W ∧ m ∈ W ∧ ∀ i, ∀ a ∈ A i, ∀ x ∈ W, a x ∈ W := by
  first
  | exact @_root_.GlobalTheory.OrbitGrowth.main
  | exact _root_.GlobalTheory.OrbitGrowth.main
  | (apply _root_.GlobalTheory.OrbitGrowth.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrbitGrowth.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrbitGrowth.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrbitGrowth.main ..)

end GlobalTheory.FiniteOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSmoothLogNearOneOfIsUnitaryLieExpData
section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

theorem anti_map_exp {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] (σ : 𝔸 →ₗ[ℝ] 𝔸)
    (anti : ∀ a b, σ (a * b) = σ b * σ a) (one : σ 1 = 1) (X : 𝔸) :
    σ (NormedSpace.exp X) = NormedSpace.exp (σ X) := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hp : ∀ n : ℕ, σ (X ^ n) = σ X ^ n := fun n => by
    induction n with
    | zero => simpa using one
    | succ n ih => rw [pow_succ, anti, ih, pow_succ']
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X).map σ.toAddMonoidHom
    σ.continuous_of_finiteDimensional
  refine h1.unique ?_
  convert NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (σ X) using 1
  funext n
  simp [hp]

theorem exists_local_log (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] :
    ∃ l : 𝔸 → 𝔸, ContDiffAt ℝ ∞ l 1 ∧ (∀ᶠ h in 𝓝 (1 : 𝔸), NormedSpace.exp (l h) = h) ∧
      ∀ᶠ X in 𝓝 (0 : 𝔸), l (NormedSpace.exp X) = X := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hc : ContDiffAt ℝ ∞ (NormedSpace.exp : 𝔸 → 𝔸) 0 := (NormedSpace.exp_analytic (𝕂 := ℝ) 0).contDiffAt
  have hd : HasFDerivAt (NormedSpace.exp : 𝔸 → 𝔸)
      ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := hasFDerivAt_exp_zero
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hc.localInverse hd hn, ?_, ?_, (hc.hasStrictFDerivAt' hd hn).eventually_left_inverse⟩
  · have := hc.to_localInverse hd hn
    rwa [NormedSpace.exp_zero] at this
  · have := (hc.hasStrictFDerivAt' hd hn).eventually_right_inverse
    rw [NormedSpace.exp_zero] at this
    exact this

theorem hasLog_of_isLieData (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G)
    (H : IsLieData σ j s) : HasLog σ j := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  haveI : FiniteDimensional ℝ L := FiniteDimensional.of_injective j H.inj
  obtain ⟨l, h1, h2, h3⟩ := exists_local_log 𝔸
  obtain ⟨p, hp⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 H.inj)
  have hp' : ∀ Y, p (j Y) = Y := fun Y => LinearMap.congr_fun hp Y
  have hl : l 1 = 0 := by simpa using h3.self_of_nhds
  refine ⟨fun h => p (l h), (LinearMap.toContinuousLinearMap p).contDiff.contDiffAt.comp 1 h1, ?_, ?_⟩
  · have ht : Filter.Tendsto (fun h => -σ (l h)) (𝓝 1) (𝓝 0) := by
      have := (σ.continuous_of_finiteDimensional.continuousAt.comp h1.continuousAt).neg.tendsto
      have e : (-(⇑σ ∘ l)) 1 = 0 := by simp [hl]
      rw [e] at this
      exact this
    filter_upwards [h2, ht.eventually h3] with h ha hb hu
    have e1 : NormedSpace.exp (σ (l h)) * h = 1 := by
      rw [← anti_map_exp σ H.anti H.one, ha, hu]
    have e2 : NormedSpace.exp (-σ (l h)) * NormedSpace.exp (σ (l h)) = 1 := by
      rw [← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left, neg_add_cancel, NormedSpace.exp_zero]
    have e3 : NormedSpace.exp (-σ (l h)) = h := by
      rw [← mul_one (NormedSpace.exp (-σ (l h))), ← e1, ← mul_assoc, e2, one_mul]
    rw [e3] at hb
    obtain ⟨Y, hY⟩ := (H.skew (l h)).1 (neg_eq_iff_eq_neg.1 hb.symm)
    rw [← hY, hp', hY, ha]
  · have ht : Filter.Tendsto j (𝓝 0) (𝓝 0) := by
      simpa using j.continuous_of_finiteDimensional.tendsto 0
    filter_upwards [ht.eventually h3] with X hX
    rw [hX, hp']

end GlobalTheory.SmoothForms
end

