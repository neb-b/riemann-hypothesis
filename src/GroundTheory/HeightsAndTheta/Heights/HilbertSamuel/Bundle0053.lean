module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallGenTwist
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SectionBoundedMul

noncomputable section

namespace SmallGenTwist

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def SmallGen (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : Prop :=
  ∃ (n : ℕ) (w : Fin n → Ω), (∀ j, w j ∈ chartLat y A.a 1) ∧ KH.GeneratesOn y A.a w ∧
    ∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)

theorem exists_chart (y : (Σ k, ι k) → Ω) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    ∃ c : ∀ k, ι k, (∀ k, z ⟨k, c k⟩ ≠ 0) ∧ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using hz.1
  refine ⟨c, hc, fun k h0 => ?_⟩
  have hX : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, c k⟩ : MRing ι) _ :=
    (by have h := isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k, c k⟩ : Σ k, ι k) 1) 1
        rwa [← X] at h)
  have hmem := mem_mCoordIdeal_of_aeval_eq_zero y hX (by rw [aeval_X, h0])
  have hz0 := hz.2 _ hmem
  simp only [map_X, eval_X] at hz0
  exact hc k hz0


omit [∀ k, Fintype (ι k)] in
theorem mul_mem_chartLat (y : (Σ k, ι k) → Ω) {a b : K → ℤ} {s t : Ω} (hs : s ∈ chartLat y a 1)
    (ht : t ∈ chartLat y b 1) : s * t ∈ chartLat y (a + b) 1 := by
  intro c hc
  have h := mul_mem (hs c hc) (ht c hc)
  convert h using 1
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_add₀ (hc k)]
  congr 1
  simp only [Pi.add_apply, Nat.cast_one, one_mul]
  ring


omit [∀ k, Fintype (ι k)] in
theorem generatesOn_mul (y : (Σ k, ι k) → Ω) {a b : K → ℤ} {n m : ℕ} {w : Fin n → Ω} {v : Fin m → Ω}
    (hw : KH.GeneratesOn y a w) (hv : KH.GeneratesOn y b v) :
    KH.GeneratesOn y (a + b)
      (fun j : Fin (n * m) => w (finProdFinEquiv.symm j).1 * v (finProdFinEquiv.symm j).2) := by
  intro c hc
  obtain ⟨u, hu, hsum⟩ := hw c hc
  obtain ⟨u', hu', hsum'⟩ := hv c hc
  refine ⟨fun j => u (finProdFinEquiv.symm j).1 * u' (finProdFinEquiv.symm j).2,
    fun j => mul_mem (hu _) (hu' _), ?_⟩
  set Pa := ∏ k, y ⟨k, c k⟩ ^ (-a k) with hPa
  set Pb := ∏ k, y ⟨k, c k⟩ ^ (-b k) with hPb
  have hP : ∏ k, y ⟨k, c k⟩ ^ (-((a + b) k)) = Pa * Pb := by
    rw [hPa, hPb, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    simp only [Pi.add_apply]
    ring
  rw [hP, Fintype.sum_equiv finProdFinEquiv.symm _
    (fun p : Fin n × Fin m => u p.1 * u' p.2 * (w p.1 * v p.2 * (Pa * Pb))) (fun _ => rfl),
    Fintype.sum_prod_type]
  calc ∑ i, ∑ l, u i * u' l * (w i * v l * (Pa * Pb))
      = (∑ i, u i * (w i * Pa)) * ∑ l, u' l * (v l * Pb) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    _ = 1 := by rw [hsum, hsum', one_mul]

theorem isSmallH_mul (y : (Σ k, ι k) → Ω) (A B C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hCa : ∀ k, C.a k = A.a k + B.a k)
    (hCh : ∀ z, C.h z = A.h z * B.h z) {s t : Ω} (hs : s ∈ chartLat y A.a 1) (ht : t ∈ chartLat y B.a 1)
    (hbs : IsSmallH (mCoordIdeal y) y A 1 s) (hbt : IsSmallH (mCoordIdeal y) y B 1 t) :
    IsSmallH (mCoordIdeal y) y C 1 (s * t) := by
  intro dg dh g h z hg hh hdeg he hz
  obtain ⟨c, hc, hy⟩ := exists_chart y hz
  obtain ⟨N, dgs, gs, hgs, hdgs, hvs⟩ := exists_chartForm y A.a 1 hs c hy
  obtain ⟨M, dgt, gt, hgt, hdgt, hvt⟩ := exists_chartForm y B.a 1 ht c hy
  have bs := hbs dgs N gs (chartMono c N) z hgs (isMultiHomog_chartMono c N) hdgs hvs hz
  have bt := hbt dgt M gt (chartMono c M) z hgt (isMultiHomog_chartMono c M) hdgt hvt hz

  have hdeq : dgs + dgt + dh = dg + (N + M) := by
    funext k
    have e1 := hdgs k
    have e2 := hdgt k
    have e3 := hdeg k
    have e4 := hCa k
    simp only [Pi.add_apply]
    have : ((dgs k + dgt k + dh k : ℕ) : ℤ) = ((dg k + (N k + M k) : ℕ) : ℤ) := by
      push_cast at e1 e2 e3 ⊢
      linear_combination e1 + e2 - e3 - e4
    exact_mod_cast this
  have hF : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (gs * gt * h - g * chartMono c (N + M)) (dgs + dgt + dh) := by
    refine isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_mul hgs hgt) hh) ?_
    rw [hdeq]
    exact isMultiHomog_mul hg (isMultiHomog_chartMono c (N + M))
  have hmono : ∀ (w : (Σ k, ι k) → Ω), aeval w (chartMono c (N + M)) =
      aeval w (chartMono c N) * aeval w (chartMono c M) := fun w => by
    rw [aeval_chartMono, aeval_chartMono, aeval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hF0 : aeval y (gs * gt * h - g * chartMono c (N + M)) = 0 := by
    rw [map_sub, map_mul, map_mul, map_mul, hvs, hvt, he, hmono]
    ring
  have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF hF0)
  simp only [map_sub, map_mul] at hz0
  rw [sub_eq_zero] at hz0

  set ev : MRing ι → ℂ := fun f => eval z (map (Int.castRingHom ℂ) f) with hev
  have hmz : ev (chartMono c (N + M)) = ev (chartMono c N) * ev (chartMono c M) := by
    simp only [hev, eval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hpos : 0 < ‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ := by
    refine mul_pos (norm_pos_iff.mpr ?_) (norm_pos_iff.mpr ?_) <;>
    · simp only [hev, eval_chartMono]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have key : ‖ev g‖ * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖) =
      ‖ev gs‖ * ‖ev gt‖ * ‖ev h‖ := by
    rw [← norm_mul, ← hmz, ← norm_mul, ← norm_mul, ← norm_mul]
    exact congrArg norm hz0.symm
  have hprod : ‖ev gs‖ * ‖ev gt‖ ≤
      (‖ev (chartMono c N)‖ * A.h z ^ 1) * (‖ev (chartMono c M)‖ * B.h z ^ 1) :=
    mul_le_mul bs bt (norm_nonneg _) ((norm_nonneg _).trans bs)
  refine le_of_mul_le_mul_right ?_ hpos
  rw [key]
  calc ‖ev gs‖ * ‖ev gt‖ * ‖ev h‖
      ≤ (‖ev (chartMono c N)‖ * A.h z ^ 1) * (‖ev (chartMono c M)‖ * B.h z ^ 1) * ‖ev h‖ :=
        mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = ‖ev h‖ * C.h z ^ 1 * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖) := by
        rw [hCh]
        ring

theorem smallGen_mul (y : (Σ k, ι k) → Ω) (A B C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hCa : C.a = A.a + B.a)
    (hCh : ∀ z, C.h z = A.h z * B.h z) (hA : SmallGen y A) (hB : SmallGen y B) : SmallGen y C := by
  obtain ⟨n, w, hw, hgw, hsw⟩ := hA
  obtain ⟨m, v, hv, hgv, hsv⟩ := hB
  refine ⟨n * m, fun j => w (finProdFinEquiv.symm j).1 * v (finProdFinEquiv.symm j).2,
    fun j => ?_, ?_, fun j => ?_⟩
  · rw [hCa]
    exact mul_mem_chartLat y (hw _) (hv _)
  · rw [hCa]
    exact generatesOn_mul y hgw hgv
  · exact isSmallH_mul y A B C (fun k => by rw [hCa]; rfl) hCh (hw _) (hv _) (hsw _) (hsv _)

theorem smallGen_of_trivial (y : (Σ k, ι k) → Ω) (E : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hEa : E.a = 0) (hEh : ∀ z, E.h z = 1) :
    SmallGen y E := by
  refine ⟨1, fun _ => 1, fun _ => ?_, ?_, fun _ => ?_⟩
  · intro c hc
    simp [hEa]
  · intro c hc
    refine ⟨fun _ => 1, fun _ => one_mem _, ?_⟩
    simp [hEa]
  · intro dg dh g h z hg hh hdeg he hz
    have hd : dg = dh := funext fun k => by
      have := hdeg k
      rw [hEa] at this
      simp only [Pi.zero_apply, mul_zero, add_zero] at this
      exact_mod_cast this
    subst hd
    have h0 : aeval y (g - h) = 0 := by rw [map_sub, he, one_mul, sub_self]
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y (isMultiHomog_sub hg hh) h0)
    simp only [map_sub, sub_eq_zero] at hz0
    rw [hz0, hEh, pow_one, mul_one]


omit [∀ k, Fintype (ι k)] in
theorem fsH_a [∀ k, Fintype (ι k)] : (fsH ι).a = fun _ => 1 := by
  funext k
  simp [fsH, HermLine.ofMetrics]

theorem smallGen_fsH (y : (Σ k, ι k) → Ω) : SmallGen y (fsH ι) := by
  classical
  set e := Fintype.equivFin (∀ k, ι k) with he_def
  refine ⟨Fintype.card (∀ k, ι k), fun j => aeval y (chartMono (e.symm j) 1), fun j => ?_, ?_, fun j => ?_⟩
  · intro c hc
    beta_reduce
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    refine prod_mem fun k _ => ?_
    have hmem : y ⟨k, (e.symm j) k⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c :=
      Algebra.subset_adjoin ⟨⟨k, (e.symm j) k⟩, rfl⟩
    convert hmem using 1
    simp [fsH_a, div_eq_mul_inv]
  · intro c hc
    refine ⟨fun j => if e.symm j = c then 1 else 0, fun j => by beta_reduce; split_ifs <;> simp, ?_⟩
    rw [Fintype.sum_equiv e.symm _ (fun i => (if i = c then (1 : Ω) else 0) *
      (aeval y (chartMono i 1) * ∏ k, y ⟨k, c k⟩ ^ (-(fsH ι).a k))) (fun _ => rfl)]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by simp [fsH_a, hc k]
  · intro dg dh g h z hg hh hdeg he hz
    have hd : dg = 1 + dh := funext fun k => by
      have := hdeg k
      simp only [fsH_a, Nat.cast_one, one_mul] at this
      simp only [Pi.add_apply, Pi.one_apply]
      omega
    have hF : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g - chartMono (e.symm j) 1 * h) dg :=
      isMultiHomog_sub hg (by rw [hd]; exact isMultiHomog_mul (isMultiHomog_chartMono _ 1) hh)
    have h0 : aeval y (g - chartMono (e.symm j) 1 * h) = 0 := by
      rw [map_sub, map_mul, he, sub_self]
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF h0)
    simp only [map_sub, map_mul, sub_eq_zero] at hz0
    rw [hz0, norm_mul, eval_chartMono, pow_one, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    simp only [Pi.one_apply, pow_one, norm_prod]
    have hH : (fsH ι).h z = ∏ k, ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖ := by
      simp [fsH, HermLine.ofMetrics, fsMetric]
    rw [hH]
    refine Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => ?_
    have := PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) ((e.symm j) k)
    rwa [PiLp.toLp_apply] at this

theorem smallGen_zcomb (y : (Σ k, ι k) → Ω) (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hL : SmallGen y L) (q p : ℕ) :
    SmallGen y (HermLine.zcomb L (fsH ι) q p) := by
  induction q with
  | zero =>
    induction p with
    | zero =>
      exact smallGen_of_trivial y _ (by funext k; simp [HermLine.zcomb]) (fun z => by simp [HermLine.zcomb])
    | succ p ih =>
      refine smallGen_mul y _ (fsH ι) _ ?_ (fun z => ?_) ih (smallGen_fsH y)
      · funext k
        simp only [HermLine.zcomb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        ring
      · simp only [HermLine.zcomb, zpow_natCast, pow_succ]
        ring
  | succ q ih =>
    refine smallGen_mul y _ L _ ?_ (fun z => ?_) ih hL
    · funext k
      simp only [HermLine.zcomb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    · simp only [HermLine.zcomb, zpow_natCast, pow_succ]
      ring

end SmallGenTwist

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsSeparated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

set_option linter.unusedSectionVars false

namespace SmallSectionsSeparated

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp [Finset.sum_add_distrib, hf m1 hm1 k, hg m2 hm2 k]

theorem isMultiHomog_sub {f g : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f - g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_sub _ f g hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem mem_mCoordIdeal_of_homog (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d)
    (h0 : aeval y f = 0) : f ∈ mCoordIdeal y := by
  rw [mCoordIdeal, RingHom.mem_ker, GroundTheory.Heights₂.Heights.ConeTrdeg.mConeMap_of_isMultiHomog y hf, h0, map_zero,
    zero_mul]

def IsRepAt (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) (g h : MRing ι) : Prop :=
  ∃ dg dh : K → ℕ, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g dg ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + τ * a k) ∧
    aeval y g = s * aeval y h ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0

theorem rep_cross {y : (Σ k, ι k) → Ω} {a : K → ℤ} {τ : ℕ} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {g h g' h' : MRing ι} (hr : IsRepAt y a τ s z g h)
    (hr' : IsRepAt y a τ s z g' h') :
    eval z (map (Int.castRingHom ℂ) g) * eval z (map (Int.castRingHom ℂ) h') =
      eval z (map (Int.castRingHom ℂ) g') * eval z (map (Int.castRingHom ℂ) h) := by
  obtain ⟨dg, dh, hg, hh, hd, hy, -⟩ := hr
  obtain ⟨dg', dh', hg', hh', hd', hy', -⟩ := hr'
  have hdeg : dg + dh' = dg' + dh := by
    funext k
    have : ((dg k + dh' k : ℕ) : ℤ) = ((dg' k + dh k : ℕ) : ℤ) := by
      push_cast
      linarith [hd k, hd' k]
    simp only [Pi.add_apply]
    exact_mod_cast this
  have hF : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g * h' - g' * h) (dg + dh') := by
    refine isMultiHomog_sub (isMultiHomog_mul hg hh') ?_
    rw [hdeg]
    exact isMultiHomog_mul hg' hh
  have h0 : aeval y (g * h' - g' * h) = 0 := by
    rw [map_sub, map_mul, map_mul, hy, hy']
    ring
  have := hz.2 _ (mem_mCoordIdeal_of_homog y hF h0)
  simp only [map_sub, map_mul] at this
  exact sub_eq_zero.mp this

theorem rep_add {y : (Σ k, ι k) → Ω} {a : K → ℤ} {τ : ℕ} {s t : Ω} {z : (Σ k, ι k) → ℂ} {g h g' h' : MRing ι}
    (hr : IsRepAt y a τ s z g h) (hr' : IsRepAt y a τ t z g' h') :
    IsRepAt y a τ (s + t) z (g * h' + g' * h) (h * h') := by
  obtain ⟨dg, dh, hg, hh, hd, hy, hz0⟩ := hr
  obtain ⟨dg', dh', hg', hh', hd', hy', hz0'⟩ := hr'
  have hdeg : dg' + dh = dg + dh' := by
    funext k
    have : ((dg' k + dh k : ℕ) : ℤ) = ((dg k + dh' k : ℕ) : ℤ) := by
      push_cast
      linarith [hd k, hd' k]
    simp only [Pi.add_apply]
    exact_mod_cast this
  refine ⟨dg + dh', dh + dh', isMultiHomog_add (isMultiHomog_mul hg hh') ?_, isMultiHomog_mul hh hh', ?_, ?_, ?_⟩
  · rw [← hdeg]
    exact isMultiHomog_mul hg' hh
  · intro k
    simp only [Pi.add_apply]
    push_cast
    linarith [hd k]
  · rw [map_add (f := _), map_mul, map_mul, map_mul, hy, hy']
    ring
  · simp only [map_mul]
    exact mul_ne_zero hz0 hz0'

end SmallSectionsSeparated


open SmallSectionsSeparated in
theorem SmallSectionsSeparated.proof (hG : GridSeparation.Statement) : SmallSectionsSeparated.Statement := by
  intro K _ ι _ Ω _ y D A hV hB hA
  obtain ⟨C, hC, hZ⟩ := hG K ι Ω y D A hV hB hA
  refine ⟨C, hC, fun τ => ?_⟩
  obtain ⟨Z, hZP, hrep, hsep⟩ := hZ τ
  classical
  have hR : ∀ (s : chartLatNm y A.a τ) (z : Z), ∃ gh : MRing ι × MRing ι,
      IsRepAt y A.a τ (s : Ω) (z : (Σ k, ι k) → ℂ) gh.1 gh.2 := by
    intro s z
    obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz⟩ := hrep s s.2 z z.2
    exact ⟨(g, h), dg, dh, hg, hh, hd, hy, hz⟩
  choose gh hgh using hR
  let val : chartLatNm y A.a τ → Z → ℂ := fun s z =>
    eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) (gh s z).1) /
      eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) (gh s z).2)

  have hval : ∀ (s : chartLatNm y A.a τ) (z : Z) (g h : MRing ι),
      IsRepAt y A.a τ (s : Ω) (z : (Σ k, ι k) → ℂ) g h →
      val s z = eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) g) /
        eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) h) := by
    intro s z g h hr
    have h1 := (hgh s z).choose_spec.choose_spec.2.2.2.2
    have h2 := hr.choose_spec.choose_spec.2.2.2.2
    rw [div_eq_div_iff h1 h2]
    exact rep_cross (hZP z z.2) (hgh s z) hr
  let ev : chartLatNm y A.a τ →+ (Z → ℂ) := AddMonoidHom.mk' (fun s z => val s z) (by
    intro s t
    funext z
    have hst := rep_add (hgh s z) (hgh t z)
    rw [Pi.add_apply, hval (s + t) z _ _ (by simpa using hst)]
    have h1 := (hgh s z).choose_spec.choose_spec.2.2.2.2
    have h2 := (hgh t z).choose_spec.choose_spec.2.2.2.2
    simp only [val, map_add (f := _), map_mul]
    field_simp)
  refine ⟨Z, ev, hZP, ?_, ?_⟩
  · intro s z
    obtain ⟨dg, dh, hg, hh, hd, hy, hz⟩ := hgh s z
    refine ⟨dg, dh, (gh s z).1, (gh s z).2, hg, hh, hd, hy, hz, ?_⟩
    show val s z * _ = _
    simp only [val]
    exact div_mul_cancel₀ _ hz
  · intro s t _ _ hst
    have hu : ((s - t : chartLatNm y A.a τ) : Ω) ≠ 0 := by
      intro h0
      exact hst (sub_eq_zero.mp (Subtype.ext h0))
    obtain ⟨z, hzZ, dg, dh, g, h, hg, hh, hd, hy, hz, hb⟩ := hsep _ (s - t).2 hu
    refine ⟨⟨z, hzZ⟩, ?_⟩
    have hev : ev s ⟨z, hzZ⟩ - ev t ⟨z, hzZ⟩ = val (s - t) ⟨z, hzZ⟩ := by
      rw [← Pi.sub_apply, ← map_sub]
      rfl
    rw [hev, hval (s - t) ⟨z, hzZ⟩ g h ⟨dg, dh, hg, hh, hd, hy, hz⟩, norm_div]
    rw [le_div_iff₀ (norm_pos_iff.mpr hz)]
    exact hb

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace TwistIntersection

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sheetDensity_add_locConst (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ j, ∀ z ∈ mcPts P, ∃ c : ℝ, ∀ᶠ u in 𝓝 z, φ' j u = φ j u + c)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ' g y w = sheetDensity P Ψ φ g y w := by
  unfold sheetDensity
  split_ifs with hγ
  · congr 1
    have hev := hγ.choose_spec.2
    have hH : ∀ k, cxHessian (fun y' => φ' k (hγ.choose y')) y =
        cxHessian (fun y' => φ k (hγ.choose y')) y := by
      intro k
      obtain ⟨c, hc⟩ := h k _ hev.self_of_nhds.2.1
      have h1 : (fun y' => φ' k (hγ.choose y')) =ᶠ[𝓝 y] fun y' => φ k (hγ.choose y') + c :=
        hev.self_of_nhds.1.continuousAt.eventually hc
      have h2 : fderiv ℝ (fun y' => φ' k (hγ.choose y')) =ᶠ[𝓝 y]
          fderiv ℝ (fun y' => φ k (hγ.choose y')) := by
        filter_upwards [h1.eventuallyEq_nhds] with x hx
        rw [hx.fderiv_eq, fderiv_add_const]
      unfold cxHessian
      rw [h2.fderiv_eq]
    simp only [maDensity, hH]
  · rfl

theorem ptsIntegral_add_locConst (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ j, ∀ z ∈ mcPts P, ∃ c : ℝ, ∀ᶠ u in 𝓝 z, φ' j u = φ j u + c) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ' g = ptsIntegral P φ g := by
  unfold ptsIntegral
  split_ifs
  · simp only [ptsIntegralAt, sheetDensity_add_locConst P h]
  · rfl

theorem I_snoc_degZero {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {P : Ideal (MRing ι)} {n : ℕ} {L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hP : IsArithVar P (n + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hB : IsSmoothHerm B) (ha : B.a = 0) :
    I P (n + 1) (Fin.snoc L B) = -ptsIntegral P (pot L) (logNorm B 1) := by
  have hhom : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι) 0 := by
    intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have hnot : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  rw [hI.2.2 P n L B 1 0 hP hL hB (fun k => by simp [ha]) hhom hnot]
  have hsupp : divSupp P (1 : MRing ι) = ∅ := by
    ext W
    refine ⟨fun hW => ?_, fun h => h.elim⟩
    have h1 : P ⊔ Ideal.span {(1 : MRing ι)} = ⊤ := by simp
    have hp : W.IsPrime := hW.1.1.1
    have hle : P ⊔ Ideal.span {(1 : MRing ι)} ≤ W := hW.1.1.2
    rw [h1] at hle
    exact hp.ne_top (top_le_iff.1 hle)
  unfold recR arInt
  simp only [hsupp, finsum_mem_empty, zero_sub]
  rfl

end TwistIntersection

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

