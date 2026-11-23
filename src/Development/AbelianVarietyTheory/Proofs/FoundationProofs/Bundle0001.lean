module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified
section
open NumberField IsDedekindDomain

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified :
    ∀ (E : Type) [Field E] [NumberField E],
      (∀ P : HeightOneSpectrum (𝓞 E),
        (Ideal.absNorm P.asIdeal).Prime ↔ P.asIdeal.inertiaDeg ℤ = 1) ∧
      {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.ramificationIdx ℤ ≠ 1}.Finite := by
  intro E _ _
  have key : ∀ P : HeightOneSpectrum (𝓞 E), (Ideal.absNorm (P.asIdeal.under ℤ)).Prime ∧
      Ideal.absNorm P.asIdeal = Ideal.absNorm (P.asIdeal.under ℤ) ^ P.asIdeal.inertiaDeg ℤ := by
    intro P
    haveI : NeZero P.asIdeal := ⟨P.ne_bot⟩
    exact ⟨Nat.absNorm_under_prime P.asIdeal,
      (Ideal.absNorm_pow_inertiaDeg (P.asIdeal.under ℤ) P.asIdeal).symm⟩
  refine ⟨fun P => ?_, ?_⟩
  · obtain ⟨hq, hN⟩ := key P
    rw [hN]
    constructor
    · intro hpow
      have hf0 : P.asIdeal.inertiaDeg ℤ ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at hpow
        exact Nat.not_prime_one hpow
      rcases hpow.eq_one_or_self_of_dvd _ (dvd_pow_self _ hf0) with h1 | h1
      · exact absurd h1 hq.one_lt.ne'
      · exact Nat.pow_right_injective hq.two_le (by simpa using h1.symm)
    · intro h1
      rw [h1, pow_one]
      exact hq
  · set d := (discr E).natAbs with hd_def
    have hd : 0 < d := Int.natAbs_pos.mpr (discr_ne_zero E)
    refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 E) (d ^ Module.finrank ℤ (𝓞 E))).preimage
      (fun P _ Q _ h => HeightOneSpectrum.ext h)).subset ?_
    intro P hP
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hP ⊢
    obtain ⟨hq, -⟩ := key P
    set q := Ideal.absNorm (P.asIdeal.under ℤ) with hq_def
    have hmem := Int.absNorm_under_mem P.asIdeal
    rw [← hq_def] at hmem
    have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    have hqd : (q : ℤ) ∣ discr E := by
      by_contra hnd
      have hun := (not_dvd_discr_iff_isUnramifiedIn E (𝓞 E) hqZ).mp hnd
      have hlies : P.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) :=
        (Ideal.liesOver_span_iff P.isPrime.ne_top hqZ).mpr (by simpa using hmem)
      exact hP (hun.ramificationIdx_eq_one hlies)
    have hqle : q ≤ d := Nat.le_of_dvd hd (by simpa using Int.natAbs_dvd_natAbs.mpr hqd)
    have hdvd : Ideal.absNorm P.asIdeal ∣ q ^ Module.finrank ℤ (𝓞 E) := by
      have hle : Ideal.span {((q : ℤ) : 𝓞 E)} ≤ P.asIdeal := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        simpa using hmem
      have hnorm : Algebra.norm ℤ ((q : ℤ) : 𝓞 E) = (q : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
        rw [← eq_intCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap]
      have h := Ideal.absNorm_dvd_absNorm_of_le hle
      rw [Ideal.absNorm_span_singleton, hnorm, Int.natAbs_pow, Int.natAbs_natCast] at h
      exact h
    calc Ideal.absNorm P.asIdeal ≤ q ^ Module.finrank ℤ (𝓞 E) :=
          Nat.le_of_dvd (pow_pos hq.pos _) hdvd
      _ ≤ d ^ Module.finrank ℤ (𝓞 E) := Nat.pow_le_pow_left hqle _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormSqOfMulConjEqDifferentIdeal
section
open Real NumberField
namespace GlobalTheory

theorem absNorm_map_ringEquiv_self {R : Type} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] (e : R ≃+* R) (J : Ideal R) :
    Ideal.absNorm (J.map e.toRingHom) = Ideal.absNorm J := by
  letI : Infinite R := Module.Free.infinite ℤ R
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv J (J.map e.toRingHom) e rfl).toEquiv).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveDualAddChar
section
namespace GlobalTheory.StandardAdditiveCharacter

theorem exists_stdAddChar_eq (n : ℕ) [NeZero n] (z : ℂ) (hz : z ^ n = 1) :
    ∃ j : ZMod n, ZMod.stdAddChar j = z := by
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).eq_pow_of_pow_eq_one hz
  refine ⟨((i : ℤ) : ZMod n), ?_⟩
  rw [ZMod.stdAddChar_coe, ← hi, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem bijective_dual_addChar (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A]
    [Module (ZMod n) A] :
    Function.Bijective fun (φ : Module.Dual (ZMod n) A) ↦
      AddChar.compAddMonoidHom ZMod.stdAddChar (LinearMap.toAddMonoidHom φ) := by
  constructor
  · intro φ ψ h
    apply LinearMap.ext
    intro a
    have h' := congr_arg (fun χ : AddChar A ℂ => χ a) h
    simp only [AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe] at h'
    exact ZMod.injective_stdAddChar h'
  · intro ψ
    have hroot : ∀ a : A, (ψ a) ^ n = 1 := by
      intro a
      rw [← AddChar.map_nsmul_eq_pow]
      have h0 : n • a = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
      rw [h0, AddChar.map_zero_eq_one]
    choose j hj using fun a => exists_stdAddChar_eq n (ψ a) (hroot a)
    let F : A →+ ZMod n :=
      { toFun := j
        map_zero' := ZMod.injective_stdAddChar (by simp [hj])
        map_add' := fun a b => ZMod.injective_stdAddChar (by simp only [AddChar.map_add_eq_mul, hj]) }
    refine ⟨F.toZModLinearMap n, ?_⟩
    ext a
    simp [F, hj]

end GlobalTheory.StandardAdditiveCharacter
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CauchyParallelogramUpperHalfPlane
section
open MeasureTheory Filter Topology Set

namespace GlobalTheory

theorem cauchy_parallelogram_upper_half_plane :
    ∀ (g : ℂ → ℂ) (τ : ℂ) (S : ℝ), DifferentiableOn ℂ g {z : ℂ | 0 < z.im} → 0 < τ.im → 0 ≤ S →
    (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I)) =
      Complex.I * (∫ s in (0:ℝ)..S, g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in (0:ℝ)..S, g (τ + s * Complex.I)) +
        (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I) := by
  intro g τ S hg hτ hS
  set φ : ℝ × ℝ → ℂ := fun x => Complex.I + (x.1 : ℂ) * (τ - Complex.I) + (x.2 : ℂ) * Complex.I
    with hφdef
  set L : ℝ × ℝ →L[ℝ] ℂ := (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (τ - Complex.I) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Complex.I with hLdef
  have hφL : φ = fun x => Complex.I + L x := by
    funext x; simp [φ, L, Complex.real_smul]; ring
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hpos : ∀ x : ℝ × ℝ, 0 ≤ x.1 → x.1 ≤ 1 → 0 ≤ x.2 → 0 < (φ x).im := by
    rintro ⟨t, s⟩ h0 h1 h2
    simp only [φ, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
    rcases h1.lt_or_eq with h | h
    · nlinarith [mul_nonneg h0 hτ.le]
    · subst h; simp at *; nlinarith
  have hφc : Continuous φ := by
    rw [hφL]; exact continuous_const.add L.continuous
  have hcont : ContinuousOn (fun x => g (φ x)) (uIcc (0:ℝ) 1 ×ˢ uIcc (0:ℝ) S) := by
    refine hg.continuousOn.comp hφc.continuousOn ?_
    intro x hx
    rw [uIcc_of_le zero_le_one, uIcc_of_le hS] at hx
    exact hpos x hx.1.1 hx.1.2 hx.2.1
  set F' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun x =>
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv g (φ x))).restrictScalars ℝ).comp L
  have hder : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1) ×ˢ Ioo (min (0:ℝ) S) (max (0:ℝ) S),
      HasFDerivAt (fun x => g (φ x)) (F' x) x := by
    intro x hx
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one, min_eq_left hS, max_eq_right hS] at hx
    have hz : 0 < (φ x).im := hpos x hx.1.1.le hx.1.2.le hx.2.1.le
    have hgd : HasDerivAt g (deriv g (φ x)) (φ x) :=
      (hg.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
    have hφd : HasFDerivAt φ L x := by
      rw [hφL]; exact L.hasFDerivAt.const_add _
    exact (hgd.hasFDerivAt.restrictScalars ℝ).comp x hφd
  have key := integral2_divergence_prod_of_hasFDerivAt
    (fun x => Complex.I * g (φ x)) (fun x => -(τ - Complex.I) * g (φ x))
    (fun x => Complex.I • F' x) (fun x => (-(τ - Complex.I)) • F' x) 0 0 1 S
    (continuousOn_const.mul hcont) (continuousOn_const.mul hcont)
    (fun x hx => (hder x hx).const_mul _) (fun x hx => (hder x hx).const_mul _)
    (by
      have : (fun x : ℝ × ℝ => (Complex.I • F' x) (1, 0) + ((-(τ - Complex.I)) • F' x) (0, 1))
          = fun _ => 0 := by
        funext x; simp [F', L]; ring
      rw [this]; exact integrableOn_zero)
  have hzero : ∀ x : ℝ × ℝ, (Complex.I • F' x) (1, 0) + ((-(τ - Complex.I)) • F' x) (0, 1) = 0 := by
    intro x; simp [F', L]; ring
  simp only [hzero, intervalIntegral.integral_zero, intervalIntegral.integral_const_mul] at key
  have e1 : ∀ s : ℝ, φ (1, s) = τ + s * Complex.I := by
    intro s; simp only [φ]; push_cast; ring
  have e0 : ∀ s : ℝ, φ (0, s) = Complex.I + s * Complex.I := by
    intro s; simp only [φ]; push_cast; ring
  have eS : ∀ t : ℝ, φ (t, S) = Complex.I + t * (τ - Complex.I) + S * Complex.I := fun _ => rfl
  have eT : ∀ t : ℝ, φ (t, 0) = Complex.I + t * (τ - Complex.I) := by
    intro t; simp only [φ]; push_cast; ring
  simp only [e1, e0, eS, eT] at key
  linear_combination -key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfPadicAlgClUniformApprox
section
open scoped Matrix

namespace GlobalTheory.UniformCoboundary

theorem exists_finset_fixed {K : Type} [Field K] {Γ : Type} (S : Set Γ)
    (M : Γ → Matrix (Fin 2) (Fin 2) K) :
    ∃ T : Finset Γ, (↑T ⊆ S) ∧
      ∀ v : Fin 2 → K, (∀ t ∈ T, M t *ᵥ v = v) → ∀ s ∈ S, M s *ᵥ v = v := by
  classical
  let W : Finset Γ → Submodule K (Fin 2 → K) :=
    fun T => ⨅ t ∈ T, LinearMap.ker (Matrix.toLin' (M t) - LinearMap.id)
  have hW : ∀ (T : Finset Γ) (v : Fin 2 → K), v ∈ W T ↔ ∀ t ∈ T, M t *ᵥ v = v := by
    intro T v
    simp only [W, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      Matrix.toLin'_apply, LinearMap.id_apply, sub_eq_zero]
  obtain ⟨_, ⟨T, hTS, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule K (Fin 2 → K))).has_min
      {P | ∃ T : Finset Γ, ↑T ⊆ S ∧ W T = P} ⟨_, ∅, by simp, rfl⟩
  refine ⟨T, hTS, fun v hv s hs => ?_⟩
  have hle : W (insert s T) ≤ W T := by
    intro w hw
    rw [hW] at hw ⊢
    exact fun t ht => hw t (Finset.mem_insert_of_mem ht)
  have hnlt : ¬ W (insert s T) < W T :=
    hmin _ ⟨insert s T, by rw [Finset.coe_insert]; exact Set.insert_subset hs hTS, rfl⟩
  have heq : W (insert s T) = W T := (hle.lt_or_eq).resolve_left hnlt
  have hv' : v ∈ W (insert s T) := by rw [heq, hW]; exact hv
  exact (hW _ _).1 hv' s (Finset.mem_insert_self s T)

theorem exists_bound {K : Type} [NormedField K] {ι : Type} [Fintype ι]
    (L : (ι → K) →ₗ[K] (Fin 2 → K)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : ι → K) (ε : ℝ), 0 ≤ ε → (∀ p, ‖w p‖ ≤ ε) → ∀ k, ‖L w k‖ ≤ C * ε := by
  classical
  refine ⟨∑ k, ∑ p, ‖L (Pi.single p 1) k‖, by positivity, fun w ε hε hw k => ?_⟩
  have h1 : w = ∑ p, w p • (Pi.single p 1 : ι → K) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : L w k = ∑ p, w p * L (Pi.single p 1) k := by
    conv_lhs => rw [h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Finset.sum_apply]
  have h3 : ‖L w k‖ ≤ (∑ p, ‖L (Pi.single p 1) k‖) * ε := by
    rw [h2, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hw p) (norm_nonneg _)
  refine h3.trans (mul_le_mul_of_nonneg_right ?_ hε)
  exact Finset.single_le_sum (f := fun k => ∑ p, ‖L (Pi.single p 1) k‖)
    (fun k _ => by positivity) (Finset.mem_univ k)

theorem coboundary_of_approx {K : Type} [NormedField K] (q : K) (hq : ‖q‖ < 1) (Γ : Type)
    (S : Set Γ) (M : Γ → Matrix (Fin 2) (Fin 2) K) (f : ℕ → Γ → Fin 2 → K) (y : Γ → Fin 2 → K)
    (hM : ∀ s i j, ‖M s i j‖ ≤ 1)
    (hf : ∀ r, ∃ v : Fin 2 → K, ∀ s ∈ S, f r s = M s *ᵥ v - v)
    (hy : ∀ r s i, ‖y s i - f r s i‖ ≤ ‖q ^ r‖) :
    ∃ v : Fin 2 → K, ∀ s ∈ S, y s = M s *ᵥ v - v := by
  classical
  obtain ⟨T, hTS, hT⟩ := exists_finset_fixed S M
  let e : (Fin 2 → K) →ₗ[K] (T × Fin 2 → K) :=
    LinearMap.pi fun p => (LinearMap.proj p.2).comp (Matrix.toLin' (M p.1) - LinearMap.id)
  have he : ∀ v (p : T × Fin 2), e v p = (M p.1 *ᵥ v - v) p.2 := by
    intro v p
    simp [e, Matrix.toLin'_apply]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective e.rangeRestrict
    (LinearMap.range_rangeRestrict e)
  obtain ⟨L, hL⟩ := LinearMap.exists_extend g
  have heL : ∀ v, e (L (e v)) = e v := by
    intro v
    have h1 : L (e v) = g (e.rangeRestrict v) := LinearMap.congr_fun hL (e.rangeRestrict v)
    have h2 : e.rangeRestrict (g (e.rangeRestrict v)) = e.rangeRestrict v :=
      LinearMap.congr_fun hg (e.rangeRestrict v)
    rw [h1]
    exact congrArg Subtype.val h2
  have hSL : ∀ v, ∀ s ∈ S, M s *ᵥ (L (e v)) - L (e v) = M s *ᵥ v - v := by
    intro v s hs
    have h0 : e (L (e v) - v) = 0 := by rw [map_sub, heL, sub_self]
    have h1 : ∀ t ∈ T, M t *ᵥ (L (e v) - v) = L (e v) - v := by
      intro t ht
      rw [← sub_eq_zero]
      funext i
      have := congrFun h0 (⟨t, ht⟩, i)
      rw [he] at this
      exact this
    have h2 := hT _ h1 s hs
    rw [Matrix.mulVec_sub] at h2
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact h2
  obtain ⟨C, hC, hCb⟩ := exists_bound L
  let Y : T × Fin 2 → K := fun p => y p.1 p.2
  refine ⟨L Y, fun s hs => ?_⟩
  funext i
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  have key : ∀ r : ℕ, ‖y s i - (M s *ᵥ L Y - L Y) i‖ ≤ (1 + 3 * C) * ‖q‖ ^ r := by
    intro r
    obtain ⟨vr, hvr⟩ := hf r
    have hε : 0 ≤ ‖q‖ ^ r := by positivity
    have hu : ∀ k, ‖L (Y - e vr) k‖ ≤ C * ‖q‖ ^ r := by
      refine hCb _ _ hε fun p => ?_
      rw [Pi.sub_apply, he, ← hvr p.1 (hTS p.1.2), ← norm_pow]
      exact hy r p.1 p.2
    have hv : L Y = L (e vr) + L (Y - e vr) := by simp [map_sub]
    generalize L (Y - e vr) = u at hu hv
    have hid : M s *ᵥ L Y - L Y = f r s + (M s *ᵥ u - u) := by
      rw [hvr s hs, ← hSL vr s hs, hv, Matrix.mulVec_add]
      abel
    have hMu : ‖(M s *ᵥ u) i‖ ≤ 2 * (C * ‖q‖ ^ r) := by
      have : (M s *ᵥ u) i = M s i 0 * u 0 + M s i 1 * u 1 := by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [this]
      have hb : ∀ k, ‖M s i k * u k‖ ≤ C * ‖q‖ ^ r := fun k => by
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hM s i k)).trans (hu k)
      have := norm_add_le (M s i 0 * u 0) (M s i 1 * u 1)
      linarith [hb 0, hb 1]
    have h1 : y s i - (M s *ᵥ L Y - L Y) i = (y s i - f r s i) - ((M s *ᵥ u) i - u i) := by
      rw [hid]
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    have h2 := hy r s i
    rw [norm_pow] at h2
    rw [h1]
    have h3 := norm_sub_le (y s i - f r s i) ((M s *ᵥ u) i - u i)
    have h4 := norm_sub_le ((M s *ᵥ u) i) (u i)
    have h5 := hu i
    linarith
  have hlim : Filter.Tendsto (fun r : ℕ => (1 + 3 * C) * ‖q‖ ^ r) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).const_mul (1 + 3 * C)
  exact ge_of_tendsto' hlim key

theorem coboundary_of_padic_approx : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) (S : Set Γ) (M : Γ → Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) (f : ℕ → Γ → Fin 2 → PadicAlgCl l) (y : Γ → Fin 2 → PadicAlgCl l), (∀ s i j, ‖M s i j‖ ≤ 1) → (∀ r, ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, f r s = M s *ᵥ v - v) → (∀ r s i, ‖y s i - f r s i‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ r‖) → ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, y s = M s *ᵥ v - v := by
  intro l _ Γ S M f y hM hf hy
  refine coboundary_of_approx ((l : ℕ) : PadicAlgCl l) ?_ Γ S M f y hM hf hy
  have h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    rw [map_natCast]
  have h0 : ‖algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])‖ = ‖(l : ℚ_[l])‖ :=
    PadicAlgCl.norm_extends l _
  rw [h, h0]
  exact Padic.norm_p_lt_one

end GlobalTheory.UniformCoboundary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffNormLeOne
section
namespace GlobalTheory.IntegralCoefficientNormBound

open Polynomial

theorem coeff_norm_le_one (l : ℕ) [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  rw [show algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] a)
      = ((algebraMap ℤ_[l] ℚ_[l] a : ℚ_[l]) : PadicAlgCl l) from rfl, PadicAlgCl.norm_extends]
  exact PadicInt.norm_le_one a

theorem norm_le_one_of_isIntegral :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l), IsIntegral ℤ_[l] x → ‖x‖ ≤ (1 : ℝ) := by
  intro l _ x hx
  obtain ⟨p, hm, hp⟩ := hx
  by_contra h
  push_neg at h
  have hx1 : (1 : ℝ) ≤ ‖x‖ := h.le
  have key : (aeval x p) = x ^ p.natDegree +
      ∑ i ∈ Finset.range p.natDegree, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i := by
    conv_lhs => rw [hm.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_add (f := _), map_sum, aeval_C, aeval_X_pow]
  rw [← aeval_def] at hp
  rw [hp] at key
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0] at key
    simp at key
  have hsum : ‖∑ i ∈ Finset.range p.natDegree, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i‖
      ≤ ‖x‖ ^ (p.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow]
    calc ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by
          gcongr
          exact coeff_norm_le_one l _
      _ = ‖x‖ ^ i := one_mul _
      _ ≤ ‖x‖ ^ (p.natDegree - 1) := pow_le_pow_right₀ hx1 (by omega)
  have heq : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree,
      algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i := eq_neg_of_add_eq_zero_left key.symm
  have : ‖x‖ ^ p.natDegree ≤ ‖x‖ ^ (p.natDegree - 1) := by
    rw [← norm_pow, heq, norm_neg]; exact hsum
  have hlt : ‖x‖ ^ (p.natDegree - 1) < ‖x‖ ^ p.natDegree := pow_lt_pow_right₀ h (by omega)
  linarith

end GlobalTheory.IntegralCoefficientNormBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousToZModPow
section
namespace GlobalTheory.ContinuousZModPow

theorem continuous_toZModPow (l : ℕ) [hl : Fact (Nat.Prime l)] (n : ℕ) :
    Continuous (⇑(PadicInt.toZModPow n) : ℤ_[l] → ZMod (l ^ n)) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast hl.out.pos) _
  have hev : ∀ᶠ y in nhds x, PadicInt.toZModPow n y = PadicInt.toZModPow n x := by
    filter_upwards [Metric.closedBall_mem_nhds x hpos] with y hy
    rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
      ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hy
    exact hy
  exact tendsto_nhds_of_eventually_eq hev

theorem main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (n : ℕ),
    Continuous (⇑(PadicInt.toZModPow n) : ℤ_[l] → ZMod (l ^ n)) := by
  intro l _ n
  exact continuous_toZModPow l n

end GlobalTheory.ContinuousZModPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntSmulIntegral
section
universe u_1 u_2

namespace GlobalTheory.IntegerScalarIntegral

open NumberField

theorem exists_int_smul_integral {K : Type u_1} [Field K] [NumberField K] (c : K) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ (d • c) := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (.of_finite ℚ c)
  exact hc.exists_integral_multiple

theorem exists_int_smul_mem {K : Type u_1} {V : Type u_2} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) (y : V) :
    ∃ m : ℤ, m ≠ 0 ∧ m • y ∈ L := by
  have hy : y ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hax b
    · rw [mul_smul]; exact zsmul_mem hbz a
  | smul c x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨d, hd, hint⟩ := exists_int_smul_integral c
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩
    let r : 𝓞 K := ⟨d • c, hint⟩
    have hr : (algebraMap (𝓞 K) K r) = d • c := rfl
    have key : (d * m) • (c • x) = r • (m • x) := by
      rw [← algebraMap_smul K r (m • x), hr, smul_comm (d • c) m x, smul_assoc, mul_comm, mul_smul]
    rw [key]
    exact L.smul_mem r hmx

theorem main : ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V),
    Submodule.span K (↑L : Set V) = ⊤ → ∀ (y : V), ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ m • y ∈ L :=
  fun L hL y => exists_int_smul_mem L hL y

end GlobalTheory.IntegerScalarIntegral
end

