module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKqEx
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pKqEx :
    TraceType → KqEx := by
  intro _ E _ _ _ A
  obtain ⟨w, hw⟩ : ∃ w : E, w = (A.ω : E) := ⟨_, rfl⟩
  have h1 : w + IsCMField.complexConj E w = (A.tr : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) A.tr_eq
    simpa [A.bar_eq, hw] using h
  have h2 : w * IsCMField.complexConj E w = (A.nm : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) A.nm_eq
    simpa [A.bar_eq, hw] using h
  have hq : w ^ 2 - (A.tr : E) * w + (A.nm : E) = 0 := by
    linear_combination w * h1 - h2
  have him : ∀ τ : E →+* ℂ, (τ w).im ≠ 0 := by
    intro τ h0
    have hz : (τ w) ^ 2 - (A.tr : ℂ) * τ w + (A.nm : ℂ) = 0 := by
      have h := congrArg τ hq
      simpa using h
    have hr : τ w = (((τ w).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h0])
    obtain ⟨r, hr'⟩ : ∃ r : ℝ, τ w = (r : ℂ) := ⟨_, hr⟩
    rw [hr'] at hz
    have hz' : r ^ 2 - (A.tr : ℝ) * r + (A.nm : ℝ) = 0 := by exact_mod_cast hz
    have hd : ((A.tr : ℝ)) ^ 2 - 4 * (A.nm : ℝ) < 0 := by exact_mod_cast A.disc_neg
    nlinarith [sq_nonneg (2 * r - (A.tr : ℝ))]
  have hint : IsIntegral ℚ w := Algebra.IsIntegral.isIntegral w
  have hdeg : (minpoly ℚ w).natDegree = 2 := by
    have hpd : (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ).natDegree = 2 := by
      compute_degree!
    have hp0 : (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ) ≠ 0 := by
      intro h
      rw [h] at hpd
      simp at hpd
    have hroot : Polynomial.aeval w (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ) = 0 := by
      simpa using hq
    have hle := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ w hroot) hp0
    have hpos := minpoly.natDegree_pos hint
    have hne : (minpoly ℚ w).natDegree ≠ 1 := by
      intro h
      obtain ⟨q, hq'⟩ := minpoly.natDegree_eq_one_iff.1 h
      apply him A.τ₀
      rw [← hq']
      simp
    omega
  have hfr : Module.finrank ℚ (IntermediateField.adjoin ℚ {w}) = 2 := by
    rw [IntermediateField.adjoin.finrank hint, hdeg]
  have hmem : w ∈ IntermediateField.adjoin ℚ {w} := IntermediateField.mem_adjoin_simple_self ℚ w
  refine ⟨(IntermediateField.adjoin ℚ {w}).toSubfield, hw ▸ hmem, ⟨?_, fun τ => ⟨w, hmem, him τ⟩⟩, ?_⟩
  · exact hfr
  · intro x hx
    rw [← hw]
    let pb := IntermediateField.adjoin.powerBasis hint
    obtain ⟨f, hf, hfx⟩ := pb.exists_eq_aeval ⟨x, hx⟩
    have hdim : pb.dim = 2 := by
      rw [IntermediateField.adjoin.powerBasis_dim, hdeg]
    have hf1 : f.natDegree ≤ 1 := by omega
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hf1] at hfx
    refine ⟨f.coeff 0, f.coeff 1, ?_⟩
    have h := congrArg (fun z : IntermediateField.adjoin ℚ {w} => (z : E)) hfx
    simp [pb] at h
    rw [h]
    simp [add_comm]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.POrbEx
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pOrbEx :
    OrbEx := by
  intro E _ _ p _ Kq u τ₁ h₁
  classical
  let S := {τ : E →+* PadicAlgCl p // LiesOver Kq u τ}
  let R : Setoid S :=
    { r := fun a b => ∃ σ : Gal(PadicAlgCl p/ℚ_[p]),
        b.1 = ((σ.toRingEquiv : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp a.1
      iseqv := ⟨fun a => ⟨1, by ext x; simp⟩,
        fun {a b} ⟨σ, hσ⟩ => ⟨σ⁻¹, by rw [hσ]; ext x; simp⟩,
        fun {a b c} ⟨σ, hσ⟩ ⟨ρ, hρ⟩ => ⟨ρ * σ, by rw [hρ, hσ]; ext x; simp⟩⟩ }
  haveI : Finite (E →+* PadicAlgCl p) := inferInstance
  haveI : Finite S := Subtype.finite
  haveI : Finite (Quotient R) := Quotient.finite _
  let s₁ : S := ⟨τ₁, h₁⟩
  let rep : Quotient R → S := fun q => if q = Quotient.mk R s₁ then s₁ else q.out
  have hrep : ∀ q, Quotient.mk R (rep q) = q := by
    intro q
    by_cases hq : q = Quotient.mk R s₁
    · simp only [rep, if_pos hq]
      exact hq.symm
    · simp only [rep, if_neg hq]
      exact Quotient.out_eq q
  let eq := Finite.equivFin (Quotient R)
  refine ⟨Nat.card (Quotient R), fun i => (rep (eq.symm i)).1, eq (Quotient.mk R s₁), ?_, ?_, ?_, ?_⟩
  · simp [rep, s₁]
  · intro i
    exact (rep _).2
  · intro i j σ hij
    apply eq.symm.injective
    rw [← hrep (eq.symm i), ← hrep (eq.symm j)]
    exact Quotient.sound ⟨σ, hij.symm⟩
  · intro τ hτ
    obtain ⟨σ, hσ⟩ := Quotient.exact (hrep (Quotient.mk R ⟨τ, hτ⟩))
    exact ⟨eq (Quotient.mk R ⟨τ, hτ⟩), σ, by simpa using hσ⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPerfCof
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pPerfCof :
    PerfCof := by
  intro E _ _ _ A
  classical
  have hδ : A.δ ≠ 0 := by
    intro h
    have h2 := A.δ_sign A.τ₀ rfl
    rw [h, map_zero, Complex.zero_im] at h2
    exact lt_irrefl _ h2
  let Ψ : E →ₗ[ℚ] Module.Dual ℚ E :=
    ((LinearMap.mul ℚ E).compr₂ (Algebra.trace ℚ E)) ∘ₗ LinearMap.mulLeft ℚ A.δ
  have hΨ : ∀ x z, Ψ x z = Algebra.trace ℚ E (A.δ * x * z) := fun x z => rfl
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have h1 := LinearMap.congr_fun hx (A.δ * x)⁻¹
    rw [hΨ, mul_inv_cancel₀ (mul_ne_zero hδ hx0), LinearMap.zero_apply,
      show (1 : E) = algebraMap ℚ E 1 from (map_one _).symm, Algebra.trace_algebraMap] at h1
    have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
    simp at h1
    omega
  have hsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).mp hinj
  let bQ := NumberField.integralBasis E
  let b := NumberField.RingOfIntegers.basis E
  choose ξ hξ using fun i => hsurj (bQ.coord i)
  obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image ξ)
  have hint : ∀ i, ∃ w : 𝓞 E, algebraMap (𝓞 E) E w = y • ξ i := fun i =>
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp
      (hyint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  choose w hw using hint
  let η : _ → 𝓞 E := fun i => (y : 𝓞 E) * w i
  have hηc : ∀ i, algebraMap (𝓞 E) E (η i) = (y : E) * ((y : E) * ξ i) := by
    intro i
    change algebraMap (𝓞 E) E ((y : 𝓞 E) * w i) = _
    rw [map_mul, map_intCast, hw i, zsmul_eq_mul]
  have hDz : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := Int.natAbs_mul_self
  have hDpos : 0 < y.natAbs * y.natAbs :=
    Nat.mul_pos (Int.natAbs_pos.mpr hy0) (Int.natAbs_pos.mpr hy0)
  have key : ∀ i z, A.trd (η i * z) = ((y.natAbs * y.natAbs : ℕ) : ℤ) * b.coord i z := by
    intro i
    have hlin : A.trd ∘ₗ LinearMap.mulLeft ℤ (η i) = ((y.natAbs * y.natAbs : ℕ) : ℤ) • b.coord i := by
      refine b.ext fun j => ?_
      apply Int.cast_injective (α := ℚ)
      have hb : bQ j = algebraMap (𝓞 E) E (b j) := NumberField.integralBasis_apply E j
      have hc : (((η i * b j : 𝓞 E)) : E) = (y : E) * ((y : E) * ξ i) * bQ j := by
        change algebraMap (𝓞 E) E (η i * b j) = _
        rw [map_mul, hηc, hb]
      rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, A.trd_spec, hc, LinearMap.smul_apply,
        smul_eq_mul, hDz,
        show A.δ * ((y : E) * ((y : E) * ξ i) * bQ j) = ((y * y : ℤ) : ℚ) • (A.δ * ξ i * bQ j) by
          rw [Algebra.smul_def, map_intCast]
          push_cast
          ring,
        map_smul, smul_eq_mul, ← hΨ, hξ]
      rw [Module.Basis.coord_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
        Module.Basis.repr_self]
      rcases eq_or_ne j i with h | h
      · subst h
        simp
      · simp [Finsupp.single_apply, h]
    intro z
    exact LinearMap.congr_fun hlin z
  have hdual : ∀ f : 𝓞 E →ₗ[ℤ] ℤ, ∃ x : 𝓞 E, ∀ z,
      A.trd (x * z) = ((y.natAbs * y.natAbs : ℕ) : ℤ) * f z := by
    intro f
    refine ⟨∑ i, f (b i) • η i, fun z => ?_⟩
    conv_rhs => rw [← b.sum_dual_apply_smul_coord f]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum, LinearMap.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, key, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  have hc0 : A.c ≠ 0 := by
    intro h
    exact A.c_ne (by rw [h]; rfl)
  have hN0 : 0 < Ideal.absNorm (Ideal.span {A.c}) := by
    refine Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {A.c}))
  refine ⟨y.natAbs * y.natAbs * Ideal.absNorm (Ideal.span {A.c}), Nat.mul_pos hDpos hN0,
    fun q hq => ⟨_, hq, fun f => ?_, ⟨c' * ((y.natAbs * y.natAbs : ℕ) : 𝓞 E), ?_⟩⟩⟩
  · obtain ⟨x, hx⟩ := hdual ((Ideal.absNorm (Ideal.span {A.c}) : ℤ) • f)
    refine ⟨x, fun z => ?_⟩
    rw [hx, LinearMap.smul_apply, smul_eq_mul]
    push_cast
    ring
  · rw [← mul_assoc, ← hc']
    push_cast
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPerfOf
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private theorem exists_trace_rep (E : Type) [Field E] [NumberField E] (f : 𝓞 E →ₗ[ℤ] ℤ) :
    ∃ z : E, ∀ y : 𝓞 E, Algebra.trace ℚ E (z * (y : E)) = ((f y : ℤ) : ℚ) := by
  let g : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ (fun i => ((f (RingOfIntegers.basis E i) : ℤ) : ℚ))
  have hg : ∀ y : 𝓞 E, g (y : E) = ((f y : ℤ) : ℚ) := by
    have hext : ((g.restrictScalars ℤ).comp ((Algebra.linearMap (𝓞 E) E).restrictScalars ℤ)) =
        (Algebra.linearMap ℤ ℚ).comp f := by
      refine (RingOfIntegers.basis E).ext fun i => ?_
      simp [g, ← integralBasis_apply]
    intro y
    simpa using LinearMap.congr_fun hext y
  have hnd : (Algebra.traceForm ℚ E).Nondegenerate := traceForm_nondegenerate ℚ E
  refine ⟨(LinearMap.BilinForm.toDual (Algebra.traceForm ℚ E) hnd).symm g, fun y => ?_⟩
  rw [← Algebra.traceForm_apply, ← LinearMap.BilinForm.toDual_def hnd, LinearEquiv.apply_symm_apply]
  exact hg y

theorem UpperTheory.Gal.W2.Seed.pPerfOf :
    PerfOf := by
  intro E _ _ _ A M hgen hc q hq
  obtain ⟨_, e1, he1, hz⟩ := hgen
  obtain ⟨e2, he2, c', hc'⟩ := hc
  refine ⟨e1 * e2, Nat.Coprime.mul_left (he1.coprime_dvd_right hq) (he2.coprime_dvd_right hq), ?_, ⟨c' * e1, ?_⟩⟩
  · intro f
    obtain ⟨z, hzf⟩ := exists_trace_rep E f
    have hzc : InCodiff z := fun y => ⟨f y, hzf y⟩
    obtain ⟨x, hx⟩ := hz z hzc
    refine ⟨(e2 : 𝓞 E) * x, fun y => ?_⟩
    have h := A.trd_spec ((e2 : 𝓞 E) * x * y)
    have hmul : A.δ * ((((e2 : 𝓞 E) * x * y : 𝓞 E)) : E) = ((e1 * e2 : ℕ) : ℚ) • (z * (y : E)) := by
      rw [Algebra.smul_def, map_natCast]
      push_cast
      linear_combination (-((e2 : E) * (y : E))) * hx
    have hq' : ((A.trd ((e2 : 𝓞 E) * x * y) : ℤ) : ℚ) = (((e1 * e2 : ℕ) : ℤ) : ℚ) * ((f y : ℤ) : ℚ) := by
      rw [h, hmul, map_smul, hzf, smul_eq_mul]
      push_cast; ring
    exact_mod_cast hq'
  · rw [← mul_assoc, hc']
    push_cast
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPosGen
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pPosGen :
    CodiffUnit → PosGen := by
  intro hCU E _ _ _ M hM t htc hg
  obtain ⟨hin, e, he, hz⟩ := id hg

  have h1 : InCodiff (1 : E) := by
    intro x
    have hx : IsIntegral ℤ (Algebra.trace ℚ E (x : E)) := Algebra.isIntegral_trace x.2
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
    exact ⟨m, by rw [one_mul, ← hm]; simp⟩

  obtain ⟨N, hN⟩ := exists_nat_gt (∑ τ : E →+* ℂ, |(τ t).re|)
  have hbound : ∀ τ : E →+* ℂ, |(τ t).re| < N := fun τ =>
    lt_of_le_of_lt (Finset.single_le_sum (f := fun τ : E →+* ℂ => |(τ t).re|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)) hN
  have hin' : InCodiff (t + (M : E) * (N : E)) := by
    intro x
    obtain ⟨a, ha⟩ := hin x
    obtain ⟨b, hb⟩ := h1 x
    refine ⟨a + M * N * b, ?_⟩
    have hs : (t + (M : E) * (N : E)) * (x : E) = t * x + ((M : ℚ) * (N : ℚ)) • (1 * (x : E)) := by
      rw [Algebra.smul_def]; simp; ring
    rw [hs, map_add (f := _), map_smul, ha, hb]
    simp
  obtain ⟨x, hx⟩ := hz 1 h1
  have hgen : GenCodiff M (t + (M : E) * (N : E)) := by
    refine hCU E M hM t _ hg hin' ?_
    intro P hP hMP
    have heP : (e : 𝓞 E) ∉ P := by
      intro h
      have hc : ((e.gcdA M : ℤ) : 𝓞 E) * (e : 𝓞 E) + ((e.gcdB M : ℤ) : 𝓞 E) * (M : 𝓞 E) = 1 := by
        have := Nat.gcd_eq_gcd_ab e M
        rw [he.gcd_eq_one] at this
        have h2 : ((e : ℤ) * e.gcdA M + (M : ℤ) * e.gcdB M) = 1 := by
          rw [← this]; simp
        have h3 := congrArg (Int.cast : ℤ → 𝓞 E) h2
        push_cast at h3
        rw [← h3]; ring
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one, ← hc]
      exact P.add_mem (P.mul_mem_left _ h) (P.mul_mem_left _ hMP)
    refine ⟨(e : 𝓞 E), (e : 𝓞 E) + (M : 𝓞 E) * ((N : 𝓞 E) * x), heP, ?_, ?_⟩
    · intro h
      exact heP ((P.add_mem_iff_left (P.mul_mem_right _ hMP)).mp h)
    · have hx' : (e : E) = t * x := by simpa using hx
      push_cast
      linear_combination ((M : E) * (N : E)) * hx'
  refine ⟨t + (M : E) * (N : E), ?_, hgen, ?_⟩
  · simp [htc]
  · intro τ
    have hb := abs_lt.mp (hbound τ)
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hre : (τ (t + (M : E) * (N : E))).re = (τ t).re + (M : ℝ) * (N : ℝ) := by
      simp
    rw [hre]
    nlinarith [hb.1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRealGen
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma traceCM_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z

private lemma conj_conj' {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    IsCMField.complexConj E (IsCMField.complexConj E z) = z :=
  IsCMField.complexConj_apply_apply E z

private lemma inCodiff_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) {y : E} (hy : InCodiff y) :
    InCodiff (IsCMField.complexConj E y) := by
  intro x
  obtain ⟨m, hm⟩ := hy (bar.symm x)
  refine ⟨m, ?_⟩
  have h : IsCMField.complexConj E y * (x : E) =
      IsCMField.complexConj E (y * ((bar.symm x : 𝓞 E) : E)) := by
    rw [map_mul, ← hbar, RingEquiv.apply_symm_apply]
  rw [h, traceCM_conj, hm]

private lemma inCodiff_mul {E : Type} [Field E] [NumberField E] {y : E} (hy : InCodiff y) (a : 𝓞 E) :
    InCodiff (y * (a : E)) := by
  intro x
  obtain ⟨m, hm⟩ := hy (a * x)
  refine ⟨m, ?_⟩
  rw [mul_assoc, ← hm]
  push_cast
  rfl

private lemma inCodiff_add {E : Type} [Field E] [NumberField E] {y z : E} (hy : InCodiff y) (hz : InCodiff z) :
    InCodiff (y + z) := by
  intro x
  obtain ⟨m, hm⟩ := hy x
  obtain ⟨n, hn⟩ := hz x
  refine ⟨m + n, ?_⟩
  rw [add_mul, map_add (f := _), hm, hn]
  push_cast
  rfl

theorem UpperTheory.Gal.W2.Seed.pRealGen :
    CodiffGen → CodiffUnit → RealGen := by
  intro hgen hunit E _ _ _ bar hbar M hM ε hε
  obtain ⟨y, hy⟩ := hgen E M hM
  by_cases hy0 : y = 0
  · subst hy0
    exact ⟨0, map_zero _, hy⟩
  obtain ⟨hyc, e, he, hegen⟩ := hy
  have hcy : InCodiff (IsCMField.complexConj E y) := inCodiff_conj bar hbar hyc
  obtain ⟨x0, hx0⟩ := hegen _ hcy
  have hx0' : (e : E) * y = IsCMField.complexConj E y * ((bar x0 : 𝓞 E) : E) := by
    have h := congrArg (IsCMField.complexConj E) hx0
    rw [map_mul, map_mul, conj_conj', map_natCast] at h
    rw [hbar, h]
  have hnorm : x0 * bar x0 = (e : 𝓞 E) ^ 2 := by
    apply RingOfIntegers.ext
    have h1 : y * ((e : E) ^ 2) = y * ((x0 : E) * ((bar x0 : 𝓞 E) : E)) := by
      calc y * ((e : E) ^ 2) = (e : E) * ((e : E) * y) := by ring
        _ = (e : E) * IsCMField.complexConj E y * ((bar x0 : 𝓞 E) : E) := by rw [hx0']; ring
        _ = y * (x0 : E) * ((bar x0 : 𝓞 E) : E) := by rw [hx0]
        _ = _ := by ring
    have h2 := mul_left_cancel₀ hy0 h1
    push_cast
    exact h2.symm
  set t : E := y * (ε : E) + IsCMField.complexConj E (y * (ε : E)) with ht
  refine ⟨t, ?_, ?_⟩
  · rw [ht, map_add (f := _), conj_conj', add_comm]
  · apply hunit E M hM y t ⟨hyc, e, he, hegen⟩
      (inCodiff_add (inCodiff_mul hyc ε) (inCodiff_conj bar hbar (inCodiff_mul hyc ε)))
    intro P hP hMP
    have heP : (e : 𝓞 E) ∉ P := by
      intro heP
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr he
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one]
      have h3 : ((a * e + b * M : ℤ) : 𝓞 E) = 1 := by rw [hab]; simp
      rw [← h3]
      push_cast
      exact P.add_mem (P.mul_mem_left _ heP) (P.mul_mem_left _ hMP)
    have hx0P : x0 ∉ P := by
      intro h
      apply heP
      have h4 : (e : 𝓞 E) ^ 2 ∈ P := hnorm ▸ P.mul_mem_right _ h
      exact hP.isPrime.mem_of_pow_mem 2 h4
    obtain ⟨h1, h2⟩ := hε P hP hMP
    refine ⟨e, e * ε + x0 * bar ε, heP, ?_, ?_⟩
    · intro hu
      rcases hP.isPrime.mem_or_mem h2 with hεP | hεP
      · apply hx0P
        have h5 : x0 = (e * ε + x0 * bar ε) - (e - x0) * ε - x0 * (ε + bar ε - 1) := by ring
        rw [h5]
        exact P.sub_mem (P.sub_mem hu (P.mul_mem_left _ hεP)) (P.mul_mem_left _ h1)
      · apply heP
        have h5 : (e : 𝓞 E) = (e * ε + x0 * bar ε) - e * (ε + bar ε - 1) + (e - x0) * bar ε := by ring
        rw [h5]
        exact P.add_mem (P.sub_mem hu (P.mul_mem_left _ h1)) (P.mul_mem_left _ hεP)
    · rw [ht, map_mul, ← hbar]
      push_cast
      linear_combination ((bar ε : 𝓞 E) : E) * hx0
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepEx
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pRepEx :
    RepEx := by
  intro E _ _ n
  classical
  let b := NumberField.RingOfIntegers.basis E
  let bZ := Pi.basis (fun _ : Fin n => b)
  let bQ := Pi.basis (fun _ : Fin n => NumberField.integralBasis E)
  let b1 := Algebra.TensorProduct.basis ℚ bZ
  refine ⟨b1.equiv bQ (Equiv.refl _), ?_⟩
  let f1 : (Fin n → 𝓞 E) →ₗ[ℤ] (Fin n → E) :=
    ((b1.equiv bQ (Equiv.refl _)).toLinearMap.restrictScalars ℤ) ∘ₗ
      TensorProduct.mk ℤ ℚ (Fin n → 𝓞 E) 1
  let f2 : (Fin n → 𝓞 E) →ₗ[ℤ] (Fin n → E) :=
    LinearMap.pi (fun i => (algebraMap (𝓞 E) E).toIntAlgHom.toLinearMap ∘ₗ LinearMap.proj i)
  have hf : f1 = f2 := by
    refine bZ.ext fun k => ?_
    have hk : f1 (bZ k) = b1.equiv bQ (Equiv.refl _) (b1 k) := by
      rw [Algebra.TensorProduct.basis_apply]
      rfl
    rw [hk, Module.Basis.equiv_apply]
    obtain ⟨i, j⟩ := k
    funext l
    simp [bQ, bZ, f2, Pi.basis_apply, Pi.single_apply, NumberField.integralBasis_apply]
    split_ifs <;> simp
    rfl
  intro v i
  exact congr_fun (LinearMap.congr_fun hf v) i
end

