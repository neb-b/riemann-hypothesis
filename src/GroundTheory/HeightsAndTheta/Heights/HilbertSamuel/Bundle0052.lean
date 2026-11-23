module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0015

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionProduct
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionProduct

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] in
theorem isMultiHomog_pow {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (j : ℕ) :
    IsMultiHomog (g ^ j) (j • d) := by
  induction j with
  | zero =>
    rw [pow_zero, zero_smul]
    classical
    intro m hm k
    have h : (1 : MRing ι) = monomial 0 1 := by simp
    rw [h] at hm
    rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
    simp
  | succ j ih =>
    rw [pow_succ, succ_nsmul]
    classical
    intro m hm k
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hm)
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]
    rw [ih m₁ hm₁ k, hg m₂ hm₂ k]

end SectionProduct


open SectionBoundedMul SectionProduct in
theorem SectionProduct.proof : SectionProduct.Statement := open SectionBoundedMul in by
  intro K _ ι _ Ω _ y A B C n j τ s t hdeg hmet hs ht
  have hdk : ∀ k, (τ : ℤ) * C.a k = (n : ℤ) * A.a k + (j : ℤ) * B.a k := fun k => by
    have := congrFun hdeg k
    simpa [smul_eq_mul] using this
  refine ⟨?_, ?_⟩
  ·
    intro c hc
    have hs' := hs c hc
    have ht' := ht c hc
    have heq : s * t ^ j * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * C.a k)) =
        (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * A.a k))) *
          (t * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * B.a k))) ^ j := by
      have hp : ∀ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * C.a k)) =
          y ⟨k, c k⟩ ^ (-((n : ℤ) * A.a k)) * (y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * B.a k))) ^ j := fun k => by
        have h0 := hc k
        rw [← zpow_natCast (y ⟨k, c k⟩ ^ _) j, ← zpow_mul, ← zpow_add₀ h0, hdk k]
        congr 1
        push_cast
        ring
      simp only [hp, Finset.prod_mul_distrib, Finset.prod_pow]
      ring
    rw [heq]
    exact mul_mem hs' (pow_mem ht' j)
  ·
    intro cc cc' hbs hbt dG dH G H z hG hH hdGH hrep hz
    choose c hc using hz.1
    have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
      intro k h0
      have hX := isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k, c k⟩ : Σ k, ι k) 1) 1
      rw [← X] at hX
      have hmem := mem_mCoordIdeal_of_aeval_eq_zero y hX (by rw [aeval_X, h0])
      have hz0 := hz.2 _ hmem
      simp only [map_X, eval_X] at hz0
      exact hc k hz0
    obtain ⟨N, dgs, gs, hgs, hdgs, hvs⟩ := exists_chartForm y A.a n hs c hy
    obtain ⟨M, dgt, gt, hgt, hdgt, hvt⟩ := exists_chartForm y B.a 1 ht c hy
    have bs := hbs dgs N gs (chartMono c N) z hgs (isMultiHomog_chartMono c N) hdgs hvs hz
    have bt := hbt dgt M gt (chartMono c M) z hgt (isMultiHomog_chartMono c M) hdgt hvt hz

    have hdeq : dgs + j • dgt + dH = dG + (N + j • M) := by
      funext k
      have e1 := hdgs k
      have e2 := hdgt k
      have e3 := hdGH k
      have e4 := hdk k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : ((dgs k + j * dgt k + dH k : ℕ) : ℤ) = ((dG k + (N k + j * M k) : ℕ) : ℤ) := by
        push_cast at e1 e2 e3 ⊢
        linear_combination e1 + (j : ℤ) * e2 - e3 - e4
      exact_mod_cast this
    have hF : IsMultiHomog (gs * gt ^ j * H - G * chartMono c (N + j • M)) (dgs + j • dgt + dH) := by
      refine isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_mul hgs (isMultiHomog_pow hgt j)) hH) ?_
      rw [hdeq]
      exact isMultiHomog_mul hG (isMultiHomog_chartMono c (N + j • M))
    have hmono : ∀ {R : Type} [CommRing R] (w : (Σ k, ι k) → R),
        ∏ k, w ⟨k, c k⟩ ^ (N + j • M) k = (∏ k, w ⟨k, c k⟩ ^ N k) * (∏ k, w ⟨k, c k⟩ ^ M k) ^ j := by
      intro R _ w
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by
        rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_add, pow_mul']
    have hF0 : aeval y (gs * gt ^ j * H - G * chartMono c (N + j • M)) = 0 := by
      rw [map_sub, map_mul, map_mul, map_pow, map_mul, hvs, hvt, hrep, aeval_chartMono, aeval_chartMono,
        aeval_chartMono, hmono]
      ring
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF hF0)
    simp only [map_sub, map_mul, map_pow] at hz0
    rw [sub_eq_zero] at hz0

    set ev : MRing ι → ℂ := fun f => eval z (map (Int.castRingHom ℂ) f) with hev
    have hmz : ev (chartMono c (N + j • M)) = ev (chartMono c N) * ev (chartMono c M) ^ j := by
      simp only [hev, eval_chartMono]
      exact hmono z
    have hpos : 0 < ‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ ^ j := by
      refine mul_pos (norm_pos_iff.mpr ?_) (pow_pos (norm_pos_iff.mpr ?_) j) <;>
      · simp only [hev, eval_chartMono]
        exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    have key : ‖ev G‖ * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ ^ j) =
        ‖ev gs‖ * ‖ev gt‖ ^ j * ‖ev H‖ := by
      rw [← norm_pow, ← norm_mul, ← hmz, ← norm_mul, ← norm_pow, ← norm_mul, ← norm_mul]
      exact congrArg norm hz0.symm
    have hprod : ‖ev gs‖ * ‖ev gt‖ ^ j ≤
        (cc * ‖ev (chartMono c N)‖ * A.h z ^ n) * (cc' * ‖ev (chartMono c M)‖ * B.h z ^ 1) ^ j :=
      mul_le_mul bs (pow_le_pow_left₀ (norm_nonneg _) bt j) (pow_nonneg (norm_nonneg _) j)
        ((norm_nonneg _).trans bs)
    rw [hmet z hz]
    refine le_of_mul_le_mul_right ?_ hpos
    rw [key]
    calc ‖ev gs‖ * ‖ev gt‖ ^ j * ‖ev H‖
        ≤ (cc * ‖ev (chartMono c N)‖ * A.h z ^ n) * (cc' * ‖ev (chartMono c M)‖ * B.h z ^ 1) ^ j * ‖ev H‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ = cc * cc' ^ j * ‖ev H‖ * (A.h z ^ n * B.h z ^ j) *
            (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ ^ j) := by
          ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSpanStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionSpanStep

variable {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]

theorem mul_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n j : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a j) : s * t ∈ chartLat y a (n + j) := by
  intro c hc
  have h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  rw [h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]
  exact MulMemClass.mul_mem (hs c hc) (ht c hc)

theorem prod_pow_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {q : ℕ} {w : Fin q → Ω}
    (hw : ∀ j, w j ∈ chartLat y a 1) (ν : Fin q → ℕ) (S : Finset (Fin q)) :
    ∏ j ∈ S, w j ^ ν j ∈ chartLat y a (∑ j ∈ S, ν j) := by
  have hpow : ∀ (j : Fin q) (e : ℕ), w j ^ e ∈ chartLat y a e := by
    intro j e
    induction e with
    | zero => intro c _; simp
    | succ e ih => rw [pow_succ]; exact mul_mem ih (hw j)
  refine Finset.induction_on S ?_ ?_
  · intro c _
    simp
  · intro j S hj ih
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact mul_mem (hpow j (ν j)) ih

end SectionSpanStep


open SectionSpanStep in
theorem SectionSpanStep.proof (hH : SpanStepHomog.Statement) (hS : SerreGraded.Statement) :
    SectionSpanStep.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen
  obtain ⟨m, r, t, ht, hloc⟩ := hH K ι Ω y a q w hy hw hgen
  have hne : ∃ j, w j ≠ 0 := by
    by_contra h
    push Not at h
    choose c hc using hy
    obtain ⟨u, -, hu⟩ := hgen c hc
    simp [h] at hu
  obtain ⟨n₀, hn₀⟩ := hS Ω q r w (fun _ => m) t hne
  refine ⟨max n₀ m, fun n hn s hs => ?_⟩
  have hs' : s ∈ gradedSpan w (fun _ => m) t (n + 1) :=
    hn₀ (n + 1) (by omega) s fun j hj => hloc (n + 1) s hs j hj
  refine (AddSubgroup.closure_le _).2 ?_ hs'
  rintro x ⟨l, μ, hdeg, rfl⟩
  have hdeg : m + ∑ i, μ i = n + 1 := hdeg
  obtain ⟨j, hj⟩ : ∃ j, 0 < μ j := by
    by_contra h
    push Not at h
    have h0 : ∑ i, μ i = 0 := Finset.sum_eq_zero fun i _ => Nat.le_zero.1 (h i)
    omega
  set μ' : Fin q → ℕ := μ - Pi.single j 1 with hμ'
  have hμ : μ = μ' + Pi.single j 1 := by
    funext i
    by_cases hij : i = j
    · subst hij
      simp [hμ']
      omega
    · simp [hμ', hij]
  have hsum : ∑ i, μ i = ∑ i, μ' i + 1 := by
    rw [hμ]
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
    simp
  have hprod : ∏ i, w i ^ μ i = (∏ i, w i ^ μ' i) * w j := by
    rw [hμ]
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_eq_single j]
    · simp
    · intro i hi
      simp [hi]
  apply AddSubgroup.subset_closure
  refine ⟨t l * ∏ i, w i ^ μ' i, ?_, j, by rw [hprod, mul_assoc]⟩
  have hmem := mul_mem (ht l) (prod_pow_mem hw μ' Finset.univ)
  have hdeg' : m + ∑ i, μ' i = n := by omega
  rwa [hdeg'] at hmem

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSupBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionSupBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartPiece (c : ∀ k, ι k) : Set ((Σ k, ι k) → ℂ) :=
  Metric.closedBall 0 1 ∩ {w | ∀ k, w ⟨k, c k⟩ = 1}

theorem isCompact_chartPiece (c : ∀ k, ι k) : IsCompact (chartPiece c) := by
  refine (isCompact_closedBall _ _).inter_right ?_
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun k => isClosed_eq (continuous_apply _) continuous_const

theorem exists_lower (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) (c : ∀ k, ι k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖) →
      (∀ k, z ⟨k, c k⟩ ≠ 0) → ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k ≤ M * A.h z := by
  have hsub : chartPiece c ⊆ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := fun w hw k =>
    ⟨c k, by rw [hw.2 k]; exact one_ne_zero⟩
  have hcont : ContinuousOn (fun w => (A.h w)⁻¹) (chartPiece c) :=
    (hA.mono hsub).inv₀ fun w hw => (A.pos w (hsub hw)).ne'
  obtain ⟨M, hM⟩ := (isCompact_chartPiece c).exists_bound_of_continuousOn hcont
  refine ⟨|M|, abs_nonneg M, fun z hmax hz0 => ?_⟩
  have hr : ∀ k, 0 < ‖z ⟨k, c k⟩‖ := fun k => norm_pos_iff.mpr (hz0 k)
  set s : K → ℂ := fun k => (z ⟨k, c k⟩)⁻¹ with hs
  have hs0 : ∀ k, s k ≠ 0 := fun k => inv_ne_zero (hz0 k)
  set w : (Σ k, ι k) → ℂ := fun p => s p.1 * z p with hw
  have hwS : w ∈ chartPiece c := by
    refine ⟨?_, fun k => inv_mul_cancel₀ (hz0 k)⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro p
    obtain ⟨k, i⟩ := p
    show ‖(z ⟨k, c k⟩)⁻¹ * z ⟨k, i⟩‖ ≤ 1
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ (hr k), mul_one]
    exact hmax k i
  have hwpos : 0 < A.h w := A.pos w (hsub hwS)
  have h1 : 1 ≤ |M| * A.h w := by
    have := (hM w hwS).trans (le_abs_self M)
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hwpos] at this
    rw [inv_le_iff_one_le_mul₀ hwpos] at this
    exact this
  have hAw : A.h w = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ * A.h z := by
    rw [hw, A.smul s z hs0, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hs, norm_inv, inv_zpow]
  have hR : 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k := Finset.prod_pos fun k _ => zpow_pos (hr k) _
  rw [hAw] at h1
  calc ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) * 1 := (mul_one _).symm
    _ ≤ (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) * (|M| * ((∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ * A.h z)) :=
        mul_le_mul_of_nonneg_left h1 hR.le
    _ = |M| * A.h z := by field_simp

end SectionSupBound


open SectionBounded SectionSupBound in
theorem SectionSupBound.proof : SectionSupBound.Statement := by
  intro K _ ι _ Ω _ y A τ e hA he
  classical
  choose M hM0 hM using fun c => SectionSupBound.exists_lower A hA c
  choose B hB0 hB using fun c hc => SectionBounded.exists_upper y A.a τ he c hc
  set S : ℝ := ∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M c ^ τ else 0 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun c' _ => by
    split_ifs with hc'
    · exact mul_nonneg (hB0 c' hc') (pow_nonneg (hM0 c') τ)
    · exact le_rfl
  refine ⟨Real.log (1 + S), Real.log_nonneg (by linarith), ?_⟩
  rw [Real.exp_log (by linarith)]
  intro dg dh g h z hg hh hdeg hgy hz
  have hmax : ∀ k, ∃ i, ∀ i', ‖z ⟨k, i'⟩‖ ≤ ‖z ⟨k, i⟩‖ := fun k => by
    obtain ⟨i0, _⟩ := hz.1 k
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z ⟨k, i⟩‖) ⟨i0, Finset.mem_univ _⟩
    exact ⟨i, fun i' => hi i' (Finset.mem_univ _)⟩
  choose c hcmax using hmax
  have hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨i0, hi0⟩ := hz.1 k
    have := hcmax k i0
    rw [h0, norm_zero] at this
    exact hi0 (norm_le_zero_iff.mp this)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hz0 k (by
    have := vanish hz (homog_X ⟨k, c k⟩) (by rw [aeval_X]; exact h0)
    simpa using this)
  have h1 := hB c hyc dg dh g h z hg hh hdeg hgy hz hcmax hz0
  have h2 := hM c z hcmax hz0
  have hpow : ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) ^ τ := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [mul_comm, zpow_mul, zpow_natCast]
  have h3 : ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) ≤ M c ^ τ * A.h z ^ τ := by
    rw [hpow, ← mul_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _) h2 τ
  have hCge : B c hyc * M c ^ τ ≤ 1 + S := by
    have := Finset.single_le_sum (f := fun c : (∀ k, ι k) =>
        if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M c ^ τ else 0)
      (fun c' _ => by
        split_ifs with hc'
        · exact mul_nonneg (hB0 c' hc') (pow_nonneg (hM0 c') τ)
        · exact le_rfl) (Finset.mem_univ c)
    simp only [dif_pos hyc] at this
    linarith
  have hAh : 0 ≤ A.h z ^ τ := pow_nonneg (A.pos z hz.1).le τ
  calc ‖eval z (map (Int.castRingHom ℂ) g)‖
      ≤ B c hyc * ‖eval z (map (Int.castRingHom ℂ) h)‖ * ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) := h1
    _ ≤ B c hyc * ‖eval z (map (Int.castRingHom ℂ) h)‖ * (M c ^ τ * A.h z ^ τ) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg (hB0 c hyc) (norm_nonneg _))
    _ = (B c hyc * M c ^ τ) * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by ring
    _ ≤ _ := by gcongr

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallPacking
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

theorem SmallPacking.proof (hR : NmSectionsRankBound.Statement) (hS : SmallSectionsSeparated.Statement) :
    SmallPacking.Statement := by
  classical
  intro K _ ι _ Ω _ y D A La hX hB hA hLa
  obtain ⟨hfin, C₁, hC₁, hrank⟩ := hR K ι Ω y D A.a hX hB
  obtain ⟨C, hC, hsep⟩ := hS K ι Ω y D A hX hB hA
  have key : ∀ (τ : ℕ) (T : Finset (La τ)), (∀ s ∈ T, IsSmallH (mCoordIdeal y) y A τ (s : Ω)) →
      Real.log T.card ≤ C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3) := by
    intro τ T hT
    obtain ⟨Z, ev, hZ, hrep, hsepτ⟩ := hsep τ
    have hpos : ∀ z : Z, 0 < A.h z := fun z => A.pos _ (hZ z z.2).1
    let φ : chartLatNm y A.a τ →+ (Z → ℂ) :=
      { toFun := fun s z => ev s z / ((A.h z : ℂ) ^ τ)
        map_zero' := by funext z; simp
        map_add' := by intro s t; funext z; simp [add_div] }
    have hφ : ∀ s z, ‖φ s z‖ = ‖ev s z‖ / A.h z ^ τ := fun s z => by
      simp [φ, norm_pow, abs_of_pos (hpos z)]
    have hnorm : ∀ s : chartLatNm y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) → ‖φ s‖ ≤ 1 := by
      intro s hs
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun z => ?_
      obtain ⟨dg, dh, g, h, hg, hh, hdeg, heq, hz0, hev⟩ := hrep s z
      have hle := hs dg dh g h z hg hh hdeg heq (hZ z z.2)
      rw [← hev, norm_mul] at hle
      rw [hφ, div_le_one (pow_pos (hpos z) τ)]
      exact le_of_mul_le_mul_right (by linarith) (norm_pos_iff.2 hz0)
    have hdist : ∀ s t : chartLatNm y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) →
        IsSmallH (mCoordIdeal y) y A τ (t : Ω) → s ≠ t →
        Real.exp (-(C * ((τ : ℝ) + 1))) ≤ ‖φ s - φ t‖ := by
      intro s t hs ht hst
      obtain ⟨z, hz⟩ := hsepτ s t hs ht hst
      refine le_trans ?_ (norm_le_pi_norm (φ s - φ t) z)
      rw [← map_sub φ, hφ, map_sub ev, Pi.sub_apply, le_div_iff₀ (pow_pos (hpos z) τ)]
      exact hz
    let ι' : La τ →+ chartLatNm y A.a τ := AddSubgroup.inclusion (hLa τ)
    have := hfin τ
    let L : Submodule ℤ (Z → ℂ) := LinearMap.range φ.toIntLinearMap
    have hsmall : ∀ s ∈ T, IsSmallH (mCoordIdeal y) y A τ ((ι' s : chartLatNm y A.a τ) : Ω) := hT
    have hinj : Set.InjOn (fun s => φ (ι' s)) T := by
      intro s hs t ht hst
      by_contra hne
      have hne' : ι' s ≠ ι' t := fun h => hne (Subtype.ext (by simpa [ι'] using congrArg Subtype.val h))
      have := hdist _ _ (hsmall s hs) (hsmall t ht) hne'
      simp only at hst
      rw [hst, sub_self, norm_zero] at this
      exact absurd this (not_le.2 (Real.exp_pos _))
    have hP := Packing.proof (Z → ℂ) L (T.image fun s => φ (ι' s)) (C * ((τ : ℝ) + 1)) (by positivity)
      (by intro v hv; obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hv; exact ⟨ι' s, rfl⟩)
      (by intro v hv; obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv; exact hnorm _ (hsmall s hs))
      (by
        intro v hv w hw hvw
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hv
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hw
        exact hdist _ _ (hsmall s hs) (hsmall t ht) fun h => hvw (by rw [h]))
    rw [Finset.card_image_of_injOn hinj] at hP
    have hL : (Module.finrank ℤ L : ℝ) ≤ Module.finrank ℤ (chartLatNm y A.a τ) := by
      exact_mod_cast LinearMap.finrank_range_le φ.toIntLinearMap
    refine hP.trans (mul_le_mul_of_nonneg_right (hL.trans (hrank τ)) (by positivity))
  have hfinite : ∀ τ, {s : La τ | IsSmallH (mCoordIdeal y) y A τ (s : Ω)}.Finite := by
    intro τ
    by_contra hinf
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf
      (⌈Real.exp (C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3))⌉₊ + 1)
    have h1 := key τ T (fun s hs => hTsub hs)
    rw [hTcard, Real.log_le_iff_le_exp (by positivity)] at h1
    push_cast at h1
    linarith [Nat.le_ceil (Real.exp (C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3)))]
  refine ⟨hfinite, C₁ * (C + Real.log 3), fun τ => ?_⟩
  unfold smallSectionCount
  rw [show Nat.card {s : La τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} = (hfinite τ).toFinset.card from
    Nat.card_eq_card_finite_toFinset (hfinite τ)]
  refine (key τ _ fun s hs => (hfinite τ).mem_toFinset.1 hs).trans ?_
  have h1 : (1 : ℝ) ≤ (τ : ℝ) + 1 := by linarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ)]
  have hl : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  calc C₁ * ((τ : ℝ) + 1) ^ D * (C * ((τ : ℝ) + 1) + Real.log 3)
      ≤ C₁ * ((τ : ℝ) + 1) ^ D * ((C + Real.log 3) * ((τ : ℝ) + 1)) := by gcongr; nlinarith
    _ = C₁ * (C + Real.log 3) * ((τ : ℝ) + 1) ^ (D + 1) := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedKleimanTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def MixedKleimanTop.Statement : Prop :=
  ∀ d : ℕ, 2 ≤ d → MixedKleiman.AtDim (d - 1) → MixedKleiman.LowAt d → MixedKleiman.TopAt d

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

