module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def frameBasisRadius (r p0 f : ℕ) (d laStar ρ : ℝ) : ℝ :=
  (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (laStar / Real.sqrt f)) ρ) ^ (2 * p0 + 1)

def frameRadius (w : ℝ) (r : ℕ) : ℝ := 1 / (10 * Real.sqrt (w * r))

def LamBasis {r : ℕ} (X : DataX E r) (La : ℝ) (x : Frame X.Ψ r) (lam : Fin r → Fin r → E) : Prop :=
  (∀ j, lam j ∈ X.L') ∧ LinearIndependent E lam ∧
  (∀ j k : Fin r, (j : ℕ) < X.p0 → X.p0 ≤ (k : ℕ) → herm X.Gm (lam j) (lam k) = 0) ∧
  (∀ j : Fin r, (j : ℕ) < X.p0 → ∀ τ : X.Ψ, 0 < (τ.1 (herm X.Gm (lam j) (lam j))).re) ∧
  (∀ j : Fin r, X.p0 ≤ (j : ℕ) → ∀ τ : X.Ψ, (τ.1 (herm X.Gm (lam j) (lam j))).re < 0) ∧
  (∀ j (τ : X.Ψ), ‖τ.1 (herm X.Gm (lam j) (lam j))‖ ≤ La ^ 2) ∧
  ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le a)) =
    Submodule.span ℂ (Set.range fun a : Fin X.p0 => Data.emb τ.1 (lam (Fin.castLE X.p0_le a)))

def LatticeBoundAtMaximum : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (z0 x0 : Frame X.Ψ r) (laStar ρ : ℝ),
    z0 ∈ X.dom → x0 ∈ X.dom → X.IsOrtho x0 → X.SameFlag z0 x0 → 0 < laStar → laStar ≤ 1 → 0 < ρ → ρ ≤ 1 →
    (∀ v ∈ X.L', v ≠ 0 → laStar ^ 2 ≤ ∑ τ, X.maj z0 τ (Data.emb τ.1 v)) →
    ∃ (lam : Fin r → Fin r → E) (Z : X.Coord), X.zN Z ≤ ρ / 3 ∧
      LamBasis X (frameBasisRadius r X.p0 (fdeg E) (dE E) laStar ρ) (X.xZ x0 Z) lam

end

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NsqMulVecLeOpN
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

def nsq {n : ℕ} (v : Fin n → ℂ) : ℝ := ∑ j, ‖v j‖ ^ 2

lemma nsq_nonneg {n : ℕ} (v : Fin n → ℂ) : 0 ≤ nsq v := by
  unfold nsq
  positivity

lemma nsq_mulVec_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    nsq (A.mulVec v) ≤ (∑ i, ∑ j, ‖A i j‖ ^ 2) * nsq v := by
  unfold nsq
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have h1 : ‖A.mulVec v i‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => norm_mul _ _
  calc ‖A.mulVec v i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma opN_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    BddAbove {t | ∃ v : Fin n → ℂ, v ≠ 0 ∧
      t = Real.sqrt (∑ i, ‖Matrix.mulVec A v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} := by
  refine ⟨Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2), ?_⟩
  rintro t ⟨v, -, rfl⟩
  have hF : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by positivity
  have key := nsq_mulVec_le A v
  have hb : 0 ≤ nsq v := nsq_nonneg v
  unfold nsq at key hb
  rcases hb.eq_or_lt with h | h
  · rw [← h]
    simp
  · rw [div_le_iff₀ (Real.sqrt_pos.2 h), ← Real.sqrt_mul hF]
    exact Real.sqrt_le_sqrt key

lemma opN_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : 0 ≤ Data.opN A := by
  unfold Data.opN
  apply Real.sSup_nonneg
  rintro t ⟨v, -, rfl⟩
  positivity

lemma nsq_mulVec_le_opN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    nsq (A.mulVec v) ≤ Data.opN A ^ 2 * nsq v := by
  by_cases hv : v = 0
  · subst hv
    simp [nsq, Matrix.mulVec_zero]
  have hmem : Real.sqrt (nsq (A.mulVec v)) / Real.sqrt (nsq v) ≤ Data.opN A :=
    le_csSup (opN_bdd A) ⟨v, hv, rfl⟩
  have hpos : 0 < nsq v := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    unfold nsq
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hj) 2)
      (Finset.single_le_sum (fun k _ => sq_nonneg ‖v k‖) (Finset.mem_univ j))
  rw [div_le_iff₀ (Real.sqrt_pos.2 hpos)] at hmem
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hmem 2
  rwa [mul_pow, Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt hpos.le] at h2

lemma opN_le_zN {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (Z : X.Coord) (τ : X.Ψ) : Data.opN (Matrix.of (Z τ)) ≤ X.zN Z := by
  unfold Data.zN
  exact le_ciSup (f := fun τ : X.Ψ => Data.opN (Matrix.of (Z τ))) (Set.finite_range _).bddAbove τ

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PackingSeparation
section
namespace ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation

open NumberField InfinitePlace Module MeasureTheory Metric TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical

theorem pack {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] (μ : Measure W) [μ.IsAddHaarMeasure]
    (S : Finset W) (R : ℝ) (hR : 0 ≤ R) (hS : ∀ p ∈ S, ‖p‖ ≤ R)
    (hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 1 ≤ ‖p - q‖) :
    (S.card : ℝ) ≤ (1 + 2 * R) ^ finrank ℝ W := by
  set d := finrank ℝ W
  have hdisj : (S : Set W).PairwiseDisjoint fun p => ball p (1 / 2) := by
    intro p hp q hq hpq
    rw [Function.onFun, Set.disjoint_left]
    intro z hzp hzq
    rw [mem_ball, dist_eq_norm] at hzp hzq
    have h1 := hsep p hp q hq hpq
    have h2 : ‖p - q‖ ≤ ‖z - p‖ + ‖z - q‖ := by
      calc ‖p - q‖ = ‖(z - q) - (z - p)‖ := by congr 1; abel
        _ ≤ ‖z - q‖ + ‖z - p‖ := norm_sub_le _ _
        _ = ‖z - p‖ + ‖z - q‖ := add_comm _ _
    linarith
  have hsub : (⋃ p ∈ S, ball p (1 / 2)) ⊆ ball (0 : W) (R + 1 / 2) := by
    intro z hz
    simp only [Set.mem_iUnion, mem_ball, dist_eq_norm] at hz
    obtain ⟨p, hp, hzp⟩ := hz
    rw [mem_ball, dist_eq_norm, sub_zero]
    calc ‖z‖ = ‖(z - p) + p‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - p‖ + ‖p‖ := norm_add_le _ _
      _ < 1 / 2 + R := by linarith [hS p hp]
      _ = R + 1 / 2 := add_comm _ _
  have h := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)] at h
  simp only [Measure.addHaar_ball μ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    Measure.addHaar_ball μ _ (by positivity : (0 : ℝ) ≤ R + 1 / 2), Finset.sum_const,
    nsmul_eq_mul] at h
  rw [← mul_assoc] at h
  have hc0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hctop : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  have h2 := (ENNReal.mul_le_mul_iff_left hc0 hctop).mp h
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have h3 : (S.card : ℝ) = (S.card : ℝ) * (1 / 2) ^ d * 2 ^ d := by
    rw [mul_assoc, ← mul_pow]
    norm_num
  rw [h3]
  calc (S.card : ℝ) * (1 / 2) ^ d * 2 ^ d ≤ (R + 1 / 2) ^ d * 2 ^ d :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = (1 + 2 * R) ^ d := by
        rw [← mul_pow]
        congr 1
        ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma one_le_abs_norm (γ : 𝓞 E) (hγ : γ ≠ 0) : 1 ≤ |(Algebra.norm ℚ (γ : E) : ℝ)| := by
  have h := Algebra.coe_norm_int γ
  have hne : Algebra.norm ℤ γ ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at h
    exact (Algebra.norm_ne_zero_iff.mpr (by exact_mod_cast hγ : (γ : E) ≠ 0)) h.symm
  rw [← h]
  have := Int.one_le_abs hne
  push_cast
  exact_mod_cast this

lemma sep (γ : 𝓞 E) (hγ : γ ≠ 0) : ∃ w : CP E, 1 ≤ ‖w.1.embedding (γ : E)‖ := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
  set w1 : CP E := ⟨w0, IsTotallyComplex.isComplex w0⟩
  have h := prod_norm (E := E) (γ : E)
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w1)] at h
  have hle : ∏ w ∈ Finset.univ.erase w1, ‖w.1.embedding (γ : E)‖ ^ 2 ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => by positivity)
      (fun w _ => pow_le_one₀ (norm_nonneg _) (hcon w).le)
  have hlt : ‖w1.1.embedding (γ : E)‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) (hcon w1) two_ne_zero
  have := one_le_abs_norm γ hγ
  rw [← h] at this
  nlinarith [mul_le_of_le_one_right (sq_nonneg ‖w1.1.embedding (γ : E)‖) hle]

theorem count (R : ℝ) (hR : 0 ≤ R) :
    {α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}.Finite ∧
      ({α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}.ncard : ℝ) ≤ (1 + 2 * R) ^ (2 * fdeg E) := by
  set T := {α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}
  have hT : T.Finite := by
    have h := Embeddings.finite_of_norm_le E ℂ R
    refine (h.preimage (Set.injOn_of_injective RingOfIntegers.coe_injective)).subset ?_
    intro α hα
    exact ⟨α.isIntegral_coe, hα⟩
  refine ⟨hT, ?_⟩
  let p : 𝓞 E → (CP E → ℂ) := fun α w => w.1.embedding (α : E)
  have hpinj : Function.Injective p := by
    intro α β h
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
    have := congrFun h ⟨w0, IsTotallyComplex.isComplex w0⟩
    exact RingOfIntegers.coe_injective (w0.embedding.injective this)
  have hd : finrank ℝ (CP E → ℂ) = 2 * fdeg E := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, (card_CP (E := E)).1, mul_comm]
  have hcard : T.ncard = (hT.toFinset.image p).card := by
    rw [Finset.card_image_of_injective _ hpinj, Set.ncard_eq_toFinset_card _ hT]
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
  have : Nonempty (CP E) := ⟨⟨w0, IsTotallyComplex.isComplex w0⟩⟩
  rw [hcard, ← hd]
  refine pack volume _ R hR ?_ ?_
  · intro q hq
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hq
    rw [Set.Finite.mem_toFinset] at hα
    exact (pi_norm_le_iff_of_nonneg hR).mpr fun w => hα _
  · intro q hq q' hq' hne
    obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨β, -, rfl⟩ := Finset.mem_image.mp hq'
    have hαβ : α - β ≠ 0 := sub_ne_zero.mpr fun h => hne (by rw [h])
    obtain ⟨w, hw⟩ := sep (α - β) hαβ
    calc (1 : ℝ) ≤ ‖w.1.embedding ((α - β : 𝓞 E) : E)‖ := hw
      _ = ‖(p α - p β) w‖ := by simp [p]
      _ ≤ ‖p α - p β‖ := norm_le_pi_norm _ w

end ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RingOfIntegersCovering
section
namespace ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering

open NumberField InfinitePlace Module Submodule TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cover_OE (Z : VS E) :
    ∃ α : 𝓞 E, ‖Z - iota E (α : E)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by
  set f : ℝ := (Fintype.card (CP E) : ℝ) with hf_def
  have hf : 0 < f := Nat.cast_pos.mpr card_complexPlaces_pos
  set D := dE E with hD_def
  have hD : 0 < D := dE_pos
  set t := D ^ (1 / f) with ht_def
  have ht : 0 < t := Real.rpow_pos_of_pos hD _
  have htinv : D ^ (-(1 / f)) = t⁻¹ := Real.rpow_neg hD.le _
  set lam := Real.sqrt (4 * f * t⁻¹) with hlam_def
  have hlam : 0 < lam := Real.sqrt_pos.mpr (by positivity)
  have hlam2 : lam ^ 2 = 4 * f * t⁻¹ := Real.sq_sqrt (by positivity)
  have hmin : ∀ x ∈ span ℤ (Set.range (bd E)), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    have hnorm := norm_bd_ge x hx hx0
    rw [← hf_def, ← hD_def, htinv] at hnorm
    rw [hlam_def, ← Real.sqrt_sq (norm_nonneg x)]
    exact Real.sqrt_le_sqrt hnorm
  obtain ⟨x, hx, hxb⟩ := BabaiCovering.cover (bas E) (bd E) inner_bas_bd lam hlam hmin Z
  obtain ⟨α, rfl⟩ := mem_span_bas hx
  refine ⟨α, ?_⟩
  have hn : (finrank ℝ (VS E) : ℝ) = 2 * f := by
    rw [finrank_VS, (card_CP (E := E)).2]
    push_cast
    ring
  have hfdeg : (fdeg E : ℝ) = f := by rw [← (card_CP (E := E)).1]
  have hrd : rdE E ^ 2 = t := by
    rw [rdE, ← hD_def, (card_CP (E := E)).2, ← Real.rpow_natCast, ← Real.rpow_mul hD.le]
    congr 1
    push_cast
    rw [← hf_def]
    field_simp
  rw [hn] at hxb
  have hbound : (2 * f) / 4 * ((2 * f) ^ 2 / lam) ^ 2 = 2 * f ^ 4 * t := by
    rw [div_pow, hlam2]
    field_simp
    ring
  rw [hbound] at hxb
  have hB : 0 ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by
    have : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
    positivity
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hB (by norm_num : (2 : ℕ) ≠ 0)]
  calc ‖Z - iota E (α : E)‖ ^ 2 ≤ 2 * f ^ 4 * t := hxb
    _ ≤ 4 * f ^ 4 * t := by nlinarith [pow_pos hf 4]
    _ = (2 * (fdeg E : ℝ) ^ 2 * rdE E) ^ 2 := by
        rw [mul_pow, mul_pow, hrd, hfdeg]
        ring

end ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SchwarzLemmaBallHolds
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open Metric Set

lemma exp_nine_quarters_lt : Real.exp (9 / 4) < 9.5 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : |Real.exp (1 / 4) - ∑ m ∈ Finset.range 4, (1 / 4 : ℝ) ^ m / m.factorial| ≤
      |(1 / 4 : ℝ)| ^ 4 * ((Nat.succ 4 : ℕ) / ((Nat.factorial 4 : ℕ) * 4)) :=
    Real.exp_bound (by norm_num [abs_of_pos]) (by norm_num)
  have h3 : Real.exp (1 / 4) < 1.2841 := by
    have := (abs_le.mp h2).2
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have h4 : Real.exp (9 / 4) = Real.exp 1 * Real.exp 1 * Real.exp (1 / 4) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he4 : 0 < Real.exp (1 / 4) := Real.exp_pos _
  rw [h4]
  calc Real.exp 1 * Real.exp 1 * Real.exp (1 / 4) ≤ 2.7182818286 * 2.7182818286 * 1.2841 := by
        gcongr
    _ < 9.5 := by norm_num

theorem schwarzLemmaBall_holds : SchwarzLemmaBall := by
  intro V _ _ γ ρ S hρ hd hb h1 h2 Z hZ
  have hS : 0 < S := by linarith [norm_nonneg (γ 0)]
  have hmaps : MapsTo γ (ball 0 ρ) (closedBall (γ 0) ((Real.exp (9 / 4) + 1) * S)) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    calc ‖γ z - γ 0‖ ≤ ‖γ z‖ + ‖γ 0‖ := norm_sub_le _ _
      _ ≤ Real.exp (9 / 4) * S + S := add_le_add (hb z (ball_subset_closedBall hz)) h2
      _ = (Real.exp (9 / 4) + 1) * S := by ring
  have hZρ : Z ∈ ball (0 : V) ρ := ball_subset_ball (by linarith) hZ
  have key := Complex.dist_le_div_mul_dist_of_mapsTo_ball (hd.mono ball_subset_closedBall) hmaps hZρ
  have hZn : ‖Z‖ < ρ / 21 := by simpa using hZ
  rw [dist_zero_right] at key
  intro h0
  rw [h0, dist_comm, dist_zero_right] at key
  have hexp := exp_nine_quarters_lt
  have : (Real.exp (9 / 4) + 1) * S / ρ * ‖Z‖ < S / 2 := by
    calc (Real.exp (9 / 4) + 1) * S / ρ * ‖Z‖ ≤ (Real.exp (9 / 4) + 1) * S / ρ * (ρ / 21) := by
          gcongr
      _ = (Real.exp (9 / 4) + 1) * S / 21 := by field_simp
      _ < S / 2 := by nlinarith
  linarith

end ReciprocityTheory.ChartRestriction.G.FD
end

