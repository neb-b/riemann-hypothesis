module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPrimeInvolutionOfRingInvolution
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

theorem exists_primeInvolution_of_ringInvolution {R : Type} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] (s : R ≃+* R) (hs : ∀ x, s (s x) = x) :
    ∃ c : HeightOneSpectrum R ≃ HeightOneSpectrum R, (∀ P, c (c P) = P) ∧
      (∀ P, Ideal.absNorm (c P).asIdeal = Ideal.absNorm P.asIdeal) ∧
      (∀ P x, s x ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧
      (∀ P x, s x ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2) := by
  have hm : ∀ (I : Ideal R) (x : R), s x ∈ I.map s ↔ x ∈ I := by
    intro I x
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨y, hy, h⟩
      rwa [← s.injective h]
    · intro h
      exact ⟨x, h, rfl⟩
  let f : HeightOneSpectrum R → HeightOneSpectrum R := fun P =>
    { asIdeal := P.asIdeal.map s
      isPrime := by
        have := P.isPrime
        exact Ideal.map_isPrime_of_equiv s
      ne_bot := by
        intro h
        apply P.ne_bot
        rw [eq_bot_iff]
        intro x hx
        have h1 := (hm _ x).2 hx
        rw [h, Ideal.mem_bot] at h1
        rw [Ideal.mem_bot]
        exact s.injective (by simpa using h1) }
  have hf : Function.Involutive f := by
    intro P
    ext x
    show x ∈ (P.asIdeal.map s).map s ↔ _
    rw [← hm P.asIdeal x, ← hm _ (s x), hs]
  refine ⟨hf.toPerm f, hf, ?_, ?_, ?_⟩
  · intro P
    show Ideal.absNorm (P.asIdeal.map s) = _
    rw [Ideal.absNorm_of_ne_bot (f P).ne_bot, Ideal.absNorm_of_ne_bot P.ne_bot,
      Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal (P.asIdeal.map s) s rfl).toEquiv).symm
  · intro P x
    exact hm _ x
  · intro P x
    show s x ∈ (P.asIdeal.map s) ^ 2 ↔ _
    rw [← Ideal.map_pow, hm]

theorem cmConjugation_on_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → (∀ x, σ (σ x) = x) ∧ ∃ c : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E), (∀ P, c (c P) = P) ∧ (∀ P, Ideal.absNorm (c P).asIdeal = Ideal.absNorm P.asIdeal) ∧ (∀ x : 𝓞 E, ∃ y : 𝓞 E, (y : E) = σ x) ∧ (∀ P (x y : 𝓞 E), (y : E) = σ x → (y ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧ (y ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2)) ∧ ∀ P Q : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = Q.under (𝓞 F) ↔ Q = P ∨ Q = c P := by
  intro F E _ _ _ _ _ σ _ hE h2 hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hσ, hσ, star_star]
  have hfix : ∀ x, σ x = x → ∃ a : F, algebraMap F E a = x := by
    intro x hx
    have := Subalgebra.isSimpleOrder_of_finrank h2
    rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
    · have hx' : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
      rw [h] at hx'
      exact hx'
    · exfalso
      apply IsTotallyComplex.complexEmbedding_not_isReal τ
      rw [ComplexEmbedding.isReal_iff]
      ext y
      have hy : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
      have hy' : σ y = y := hy
      rw [ComplexEmbedding.conjugate_coe_eq]
      have := hσ τ y
      rw [hy'] at this
      exact this.symm
  let e : E ≃+* E :=
    { toFun := σ, invFun := σ, left_inv := hinv, right_inv := hinv,
      map_mul' := map_mul σ, map_add' := map_add σ }
  let s : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv e
  have hs : ∀ x : 𝓞 E, ((s x : 𝓞 E) : E) = σ x := fun x => rfl
  have hss : ∀ x, s (s x) = x := by
    intro x
    apply RingOfIntegers.ext
    rw [hs, hs, hinv]
  have hsF : ∀ a : 𝓞 F, s (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
    intro a
    apply RingOfIntegers.ext
    rw [hs]
    exact σ.commutes (a : F)
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := exists_primeInvolution_of_ringInvolution s hss
  refine ⟨hinv, c, hc1, hc2, fun x => ⟨s x, hs x⟩, ?_, ?_⟩
  · intro P x y hy
    have : y = s x := RingOfIntegers.ext (by rw [hy, hs])
    subst this
    exact ⟨hc3 P x, hc4 P x⟩
  · intro P Q
    have hu : ∀ (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 F),
        a ∈ (P.under (𝓞 F)).asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) a ∈ P.asIdeal := fun P a => Iff.rfl
    constructor
    · intro h
      by_contra hne
      push Not at hne
      have hnot : ¬ ((Q.asIdeal : Set (𝓞 E)) ⊆ P.asIdeal ∪ (c P).asIdeal) := by
        rw [Ideal.subset_union]
        rintro (h' | h')
        · exact hne.1 (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h'))
        · exact hne.2 (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (c P).isPrime.ne_top h'))
      rw [Set.not_subset] at hnot
      obtain ⟨x, hxQ, hx⟩ := hnot
      simp only [Set.mem_union, SetLike.mem_coe, not_or] at hx hxQ
      obtain ⟨a, ha⟩ := hfix ((x * s x : 𝓞 E) : E) (by
        rw [← hs, map_mul, hss, mul_comm])
      have hai : IsIntegral ℤ a := by
        have h1 : IsIntegral ℤ (algebraMap F E a) := by
          rw [ha]; exact RingOfIntegers.isIntegral_coe _
        exact (isIntegral_algebraMap_iff ).1 h1
      obtain ⟨b, hb⟩ : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = x * s x :=
        ⟨⟨a, hai⟩, RingOfIntegers.ext ha⟩
      have h1 : b ∈ (Q.under (𝓞 F)).asIdeal := by
        rw [hu, hb]; exact Ideal.mul_mem_right _ _ hxQ
      rw [← h, hu, hb] at h1
      rcases P.isPrime.mem_or_mem h1 with h3 | h3
      · exact hx.1 h3
      · apply hx.2
        have := (hc3 P _).2 h3
        rwa [hss] at this
    · rintro (rfl | rfl)
      · rfl
      · ext a
        rw [hu, hu, ← hc3 P, hsF]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingHomAdicCompletion
section
open NumberField IsDedekindDomain
open scoped Matrix WithZero

theorem GlobalTheory.LocalQuad.exists_ringHom_adicCompletion (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (w : HeightOneSpectrum (𝓞 L)) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (φ : v.adicCompletion K →+* w.adicCompletion L),
      ∀ x : K, φ (algebraMap K (v.adicCompletion K) x) =
        algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  let v : HeightOneSpectrum (𝓞 K) := w.under (𝓞 K)
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver K L v w).continuous
  refine ⟨v, ((HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv K v).toRingHom, fun x => ?_⟩
  apply HeightOneSpectrum.adicCompletion.ext
  exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExpSeriesContDiffAndHasDerivAt
section
open scoped ContDiff

namespace GlobalTheory

section ExpSeries

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {I : Type}

end ExpSeries

open scoped ContDiff in
private lemma norm_smulRight_le_opNorm_mul_norm {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (L : V →L[ℝ] ℂ) (w : E) :
    ‖L.smulRight w‖ ≤ ‖L‖ * ‖w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul]
  calc ‖L h‖ * ‖w‖ ≤ ‖L‖ * ‖h‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_right (L.le_opNorm h) (norm_nonneg _)
    _ = ‖L‖ * ‖w‖ * ‖h‖ := by ring

open scoped ContDiff in
private lemma mul_exp_mul_le_exp_add_one_mul (r R : ℝ) :
    r * Real.exp (R * r) ≤ Real.exp ((R + 1) * r) := by
  calc r * Real.exp (R * r) ≤ Real.exp r * Real.exp (R * r) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp r]) (Real.exp_pos _).le
    _ = Real.exp ((R + 1) * r) := by rw [← Real.exp_add]; ring_nf

open scoped ContDiff in
private lemma summable_norm_smulRight_mul_exp {V E I : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℂ E] (m : I → V →L[ℝ] ℂ) (w : I → E)
    (hw : ∀ R : ℝ, Summable fun i => ‖w i‖ * Real.exp (R * ‖m i‖)) (R : ℝ) :
    Summable fun i => ‖(m i).smulRight (w i)‖ * Real.exp (R * ‖m i‖) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hw (R + 1))
  calc ‖(m i).smulRight (w i)‖ * Real.exp (R * ‖m i‖)
      ≤ ‖m i‖ * ‖w i‖ * Real.exp (R * ‖m i‖) :=
        mul_le_mul_of_nonneg_right (norm_smulRight_le_opNorm_mul_norm _ _) (Real.exp_pos _).le
    _ = ‖w i‖ * (‖m i‖ * Real.exp (R * ‖m i‖)) := by ring
    _ ≤ ‖w i‖ * Real.exp ((R + 1) * ‖m i‖) :=
        mul_le_mul_of_nonneg_left (mul_exp_mul_le_exp_add_one_mul _ _) (norm_nonneg _)

open scoped ContDiff in
private lemma norm_cexp_le_exp_mul_opNorm_of_norm_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℂ) {y : V} {r : ℝ} (hy : ‖y‖ ≤ r) :
    ‖Complex.exp (L y)‖ ≤ Real.exp (r * ‖L‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  calc (L y).re ≤ ‖L y‖ := Complex.re_le_norm _
    _ ≤ ‖L‖ * ‖y‖ := L.le_opNorm y
    _ ≤ r * ‖L‖ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)

open scoped ContDiff in
private lemma hasFDerivAt_tsum_cexp_smul_of_summable_exp {V E I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (m : I → V →L[ℝ] ℂ) (w : I → E)
    (hw : ∀ R : ℝ, Summable fun i => ‖w i‖ * Real.exp (R * ‖m i‖)) (x : V) :
    HasFDerivAt (fun v => ∑' i, Complex.exp (m i v) • w i)
      (∑' i, Complex.exp (m i x) • (m i).smulRight (w i)) x := by
  set r := ‖x‖ + 1
  have hx : x ∈ Metric.ball (0 : V) r := by rw [mem_ball_zero_iff]; simp [r]
  refine hasFDerivAt_tsum_of_isPreconnected (u := fun i => ‖(m i).smulRight (w i)‖ *
      Real.exp (r * ‖m i‖)) (f := fun i v => Complex.exp (m i v) • w i)
    (f' := fun i y => Complex.exp (m i y) • (m i).smulRight (w i))
    (summable_norm_smulRight_mul_exp m w hw r) Metric.isOpen_ball
    (convex_ball _ _).isPreconnected ?_ ?_ hx ?_ hx
  · intro i y _
    refine (((m i).hasFDerivAt.cexp).smul_const (w i)).congr_fderiv ?_
    ext h
    simp [smul_smul]
  · intro i y hy
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (norm_cexp_le_exp_mul_opNorm_of_norm_le _ (by rw [mem_ball_zero_iff] at hy; exact hy.le)) (norm_nonneg _)
  · refine Summable.of_norm_bounded (hw r) fun i => ?_
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_cexp_le_exp_mul_opNorm_of_norm_le _ (by simp [r])) (norm_nonneg _)

open scoped ContDiff in
private lemma contDiff_tsum_cexp_smul_of_summable_exp {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : I → V →L[ℝ] ℂ) (n : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (w : I → E),
      (∀ R : ℝ, Summable fun i => ‖w i‖ * Real.exp (R * ‖m i‖)) →
      ContDiff ℝ n (fun v => ∑' i, Complex.exp (m i v) • w i) := by
  induction n with
  | zero =>
    intro E _ _ _ w hw
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
      (hasFDerivAt_tsum_cexp_smul_of_summable_exp m w hw x).continuousAt)
  | succ n ih =>
    intro E _ _ _ w hw
    have hd := fun x => hasFDerivAt_tsum_cexp_smul_of_summable_exp m w hw x
    push_cast
    refine contDiff_succ_iff_fderiv.2 ⟨fun x => (hd x).differentiableAt, fun h => by simp at h, ?_⟩
    have hfd : fderiv ℝ (fun v => ∑' i, Complex.exp (m i v) • w i) =
        fun x => ∑' i, Complex.exp (m i x) • (m i).smulRight (w i) :=
      funext fun x => (hd x).fderiv
    rw [hfd]
    exact ih (V →L[ℝ] E) (fun i => (m i).smulRight (w i))
      (summable_norm_smulRight_mul_exp m w hw)


open scoped ContDiff in
theorem _root_.GlobalTheory.expSeries_contDiff_and_hasDerivAt :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (I : Type) (c : I → ℂ)
      (m : I → V →L[ℝ] ℂ), (∀ R : ℝ, Summable fun i => ‖c i‖ * Real.exp (R * ‖m i‖)) →
      ContDiff ℝ ∞ (fun v : V => ∑' i, c i * Complex.exp (m i v)) ∧
        ∀ z : V, Summable (fun i => c i * m i z) ∧
          HasDerivAt (fun t : ℝ => ∑' i, c i * Complex.exp (m i (t • z)))
            (∑' i, c i * m i z) 0 := by
  intro V _ _ I c m hc
  have hfun : (fun v : V => ∑' i, c i * Complex.exp (m i v)) =
      fun v => ∑' i, Complex.exp (m i v) • c i :=
    funext fun v => tsum_congr fun i => by rw [smul_eq_mul, mul_comm]
  have hz : ∀ z : V, Summable fun i => c i * m i z := by
    intro z
    refine Summable.of_norm_bounded ((hc 1).mul_left ‖z‖) fun i => ?_
    rw [norm_mul, one_mul]
    have h1 : 0 ≤ ‖c i‖ * ‖z‖ * (Real.exp ‖m i‖ - ‖m i‖) :=
      mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (by linarith [Real.add_one_le_exp ‖m i‖])
    have h2 : ‖c i‖ * ‖m i z‖ ≤ ‖c i‖ * (‖m i‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left ((m i).le_opNorm z) (norm_nonneg _)
    nlinarith
  refine ⟨?_, fun z => ⟨hz z, ?_⟩⟩
  · rw [hfun]
    exact contDiff_infty.2 fun n => contDiff_tsum_cexp_smul_of_summable_exp m n ℂ c hc
  · have hF := hasFDerivAt_tsum_cexp_smul_of_summable_exp m c hc (0 : V)
    have hl := (hasDerivAt_id (0 : ℝ)).smul_const z
    have h := hF.comp_hasDerivAt_of_eq (0 : ℝ) hl (zero_smul ℝ z).symm
    have hS : Summable fun i => (m i).smulRight (c i) := by
      refine Summable.of_norm ?_
      simpa using summable_norm_smulRight_mul_exp m c hc 0
    have hS' : Summable fun i => Complex.exp (m i 0) • (m i).smulRight (c i) := by
      simpa using hS
    have hfeq : (fun t : ℝ => ∑' i, c i * Complex.exp (m i (t • z))) =
        ((fun v => ∑' i, Complex.exp (m i v) • c i) ∘ fun y => id y • z) :=
      funext fun t => tsum_congr fun i => by simp [mul_comm]
    rw [hfeq]
    refine h.congr_deriv ?_
    have happ := (hS'.hasSum.mapL (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ) • z))).tsum_eq
    simp only [ContinuousLinearMap.apply_apply] at happ
    rw [← happ]
    exact tsum_congr fun i => by simp [mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasSumLogZetaSqMul
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.LogEulerSeries

theorem hasSum_neg_log_succ {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1)) (-Complex.log (1 - z)) := by
  have h := Complex.hasSum_taylorSeries_neg_log hz
  have h2 := (hasSum_nat_add_iff' 1).mpr h
  simpa using h2

theorem hasSum_prod_neg_log {ι : Type} (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1 / 2)
    (hs : Summable fun i => ‖z i‖) :
    HasSum (fun p : ι × ℕ => z p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1))
      (∑' i, -Complex.log (1 - z i)) := by
  have hsum : Summable (fun p : ι × ℕ => z p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1)) := by
    have hb : Summable (fun p : ι × ℕ => ‖z p.1‖ * ((1 / 2 : ℝ) ^ p.2)) :=
      hs.mul_of_nonneg summable_geometric_two (fun i => norm_nonneg _) (fun k => by positivity)
    refine Summable.of_norm_bounded hb ?_
    rintro ⟨i, k⟩
    simp only
    have h1 : (1 : ℝ) ≤ ‖(k : ℂ) + 1‖ := by
      have : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]
      exact_mod_cast Nat.le_add_left 1 k
    rw [norm_div, norm_pow, pow_succ, mul_comm]
    calc ‖z i‖ * ‖z i‖ ^ k / ‖(k : ℂ) + 1‖ ≤ ‖z i‖ * ‖z i‖ ^ k := div_le_self (by positivity) h1
      _ ≤ ‖z i‖ * (1 / 2 : ℝ) ^ k := by gcongr; exact hz i
  have hf : ∀ i, HasSum (fun k : ℕ => z i ^ (k + 1) / ((k : ℂ) + 1)) (-Complex.log (1 - z i)) :=
    fun i => hasSum_neg_log_succ (by linarith [hz i])
  have h3 := hsum.hasSum.prod_fiberwise hf
  rw [h3.tsum_eq]
  exact hsum.hasSum

theorem hasSum_one {ι : Type} (N : ι → ℕ) (c : ι → ℂ) (hN : ∀ i, 2 ≤ N i) (hc : ∀ i, ‖c i‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) (hsum : Summable fun i => (N i : ℝ) ^ (-s.re)) :
    HasSum (fun p : ι × ℕ => c p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1) *
        Complex.exp (-((((p.2 : ℝ) + 1) * Real.log (N p.1) : ℝ) : ℂ) * s))
      (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) := by
  have hpos : ∀ i, 0 < N i := fun i => by have := hN i; omega
  have hn : ∀ i, ‖c i * ((N i : ℕ) : ℂ) ^ (-s)‖ ≤ (N i : ℝ) ^ (-s.re) := fun i => by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (hpos i), Complex.neg_re]
    exact mul_le_of_le_one_left (by positivity) (hc i)
  have h := hasSum_prod_neg_log (fun i => c i * ((N i : ℕ) : ℂ) ^ (-s)) (fun i => by
    refine (hn i).trans ?_
    have h2 : (2 : ℝ) ≤ N i := by exact_mod_cast hN i
    calc (N i : ℝ) ^ (-s.re) ≤ (N i : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 / (N i : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2)
    (Summable.of_nonneg_of_le (fun i => norm_nonneg _) hn hsum)
  convert h using 2 with p
  obtain ⟨i, k⟩ := p
  have hne : ((N i : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (hpos i).ne'
  simp only
  rw [mul_pow, Complex.cpow_def_of_ne_zero hne, ← Complex.exp_nat_mul, ← Complex.natCast_log]
  push_cast
  rw [show ((k : ℂ) + 1) * (Complex.log (N i) * -s) = -(((k : ℂ) + 1) * Complex.log (N i)) * s by ring]
  ring

theorem hasSum_log_zeta_sq_mul : ∀ (ι : Type) (N : ι → ℕ) (c : ι → ℂ), (∀ i, 2 ≤ N i) → (∀ i, ‖c i‖ ≤ 1) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → ∀ s : ℂ, 1 < s.re → HasSum (fun p : ι × ℕ => (((2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1) : ℝ) : ℂ) * Complex.exp (-((((p.2 : ℝ) + 1) * Real.log (N p.1) : ℝ) : ℂ) * s)) (2 * (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s))) + (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) + (∑' i, -Complex.log (1 - starRingEnd ℂ (c i) * ((N i : ℕ) : ℂ) ^ (-s)))) := by
  intro ι N c hN hc hsum s hs
  have h1 := hasSum_one N (fun _ => 1) hN (fun _ => by simp) s hs (hsum _ hs)
  have h2 := hasSum_one N c hN hc s hs (hsum _ hs)
  have h3 := hasSum_one N (fun i => starRingEnd ℂ (c i)) hN (fun i => by simpa using hc i) s hs
    (hsum _ hs)
  have h := ((h1.mul_left 2).add h2).add h3
  convert h using 1
  funext p
  revert p
  rintro ⟨i, k⟩
  simp only
  generalize Complex.exp _ = E
  rw [← map_pow]
  have := Complex.add_conj (c i ^ (k + 1))
  rw [Complex.ofReal_div, Complex.ofReal_add, ← this]
  push_cast
  ring

end GlobalTheory.LogEulerSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ImportsBis
section
namespace GlobalTheory.NatMulIntegralNsmul

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ M : ℕ, 0 < M ∧ IsIntegral ℤ ((M : E) * a) := by
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  have hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  rcases Int.natAbs_eq y with h | h
  · rw [hc, ← h]; exact hint
  · have h2 : (y.natAbs : ℤ) = -y := by omega
    rw [hc, h2, Int.cast_neg, neg_mul]
    exact hint.neg

theorem exists_nsmul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (h : Submodule.IsFullLattice E Λ)
    (v : Fin n → E) : ∃ (N : ℕ), (0 : ℕ) < N ∧ N • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
    rw [h.span_eq_top]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.one_pos, by simpa using hx⟩
  | zero => exact ⟨1, Nat.one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, hy⟩ := hy
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_smul]; exact nsmul_mem hx M
    · rw [mul_comm, mul_smul]; exact nsmul_mem hy N
  | smul a x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, hint⟩ := exists_nat_mul_integral a
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    obtain ⟨r, hr⟩ : ∃ r : NumberField.RingOfIntegers E,
        algebraMap (NumberField.RingOfIntegers E) E r = (M : E) * a := ⟨⟨(M : E) * a, hint⟩, rfl⟩
    have hmem := Λ.smul_mem r hx
    have e : (M * N) • a • x = r • N • x := by
      rw [← algebraMap_smul E r (N • x), hr]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul, Pi.mul_apply,
        Pi.natCast_apply]
      ring
    rw [e]; exact hmem

end GlobalTheory.NatMulIntegralNsmul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ProdLeftEqMaps
section
namespace GlobalTheory.ProductLeftMaps

open TensorProduct

theorem prodLeft_eq_maps {F A B E : Type} [Field F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (z : TensorProduct F (A × B) E) :
    TensorProduct.prodLeft F F A B E z =
      ((Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) :
          TensorProduct F (A × B) E → TensorProduct F A E) z,
       (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) :
          TensorProduct F (A × B) E → TensorProduct F B E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul x e =>
    obtain ⟨a, b⟩ := x
    simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy =>
    rw [map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
    rfl

theorem main : ∀ {F A B E : Type} [inst : Field F] [inst_1 : CommRing A] [inst_2 : CommRing B]
    [inst_3 : CommRing E] [inst_4 : Algebra F A] [inst_5 : Algebra F B] [inst_6 : Algebra F E]
    (z : TensorProduct F (A × B) E),
    (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) :
        TensorProduct F (A × B) E → TensorProduct F A E) z = (0 : TensorProduct F A E) →
    (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) :
        TensorProduct F (A × B) E → TensorProduct F B E) z = (0 : TensorProduct F B E) →
    z = (0 : TensorProduct F (A × B) E) := by
  intro F A B E _ _ _ _ _ _ _ z h1 h2
  apply (TensorProduct.prodLeft F F A B E).injective
  rw [prodLeft_eq_maps, h1, h2, map_zero]
  rfl

end GlobalTheory.ProductLeftMaps
end

