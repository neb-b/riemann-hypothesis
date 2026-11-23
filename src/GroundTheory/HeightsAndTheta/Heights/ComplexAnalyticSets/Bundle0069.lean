module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0053
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PevEqZeroOfPresentation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

namespace IsGermCombination

variable {σ : Type} [Fintype σ] {w : σ → ℂ} {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ}

theorem congr {f g : (σ → ℂ) → ℂ} (hf : IsGermCombination w p f) (h : ∀ᶠ z in 𝓝 w, f z = g z) :
    IsGermCombination w p g := by
  obtain ⟨c, hc, he⟩ := hf
  exact ⟨c, hc, by filter_upwards [he, h] with z hz h' using h' ▸ hz⟩

theorem zero : IsGermCombination w p (fun _ => 0) :=
  ⟨fun _ _ => 0, fun _ => analyticAt_const, Eventually.of_forall fun z => by simp⟩

theorem generator (i : Fin k) : IsGermCombination w p (p i) := by
  classical
  refine ⟨fun j _ => if j = i then 1 else 0, fun _ => analyticAt_const, Eventually.of_forall fun z => ?_⟩
  simp

theorem add {f g : (σ → ℂ) → ℂ} (hf : IsGermCombination w p f) (hg : IsGermCombination w p g) :
    IsGermCombination w p (fun z => f z + g z) := by
  obtain ⟨c, hc, he⟩ := hf
  obtain ⟨c', hc', he'⟩ := hg
  refine ⟨fun i => c i + c' i, fun i => (hc i).add (hc' i), ?_⟩
  filter_upwards [he, he'] with z hz hz'
  simp only [Pi.add_apply, hz, hz', add_mul, Finset.sum_add_distrib]

theorem mul_left {f g : (σ → ℂ) → ℂ} (hg : AnalyticAt ℂ g w) (hf : IsGermCombination w p f) :
    IsGermCombination w p (fun z => g z * f z) := by
  obtain ⟨c, hc, he⟩ := hf
  refine ⟨fun i => g * c i, fun i => hg.mul (hc i), ?_⟩
  filter_upwards [he] with z hz
  simp only [Pi.mul_apply, hz, Finset.mul_sum, mul_assoc]

theorem neg {f : (σ → ℂ) → ℂ} (hf : IsGermCombination w p f) :
    IsGermCombination w p (fun z => - f z) :=
  (mul_left (g := fun _ => (-1 : ℂ)) analyticAt_const hf).congr (Eventually.of_forall fun z => by ring)

theorem sub {f g : (σ → ℂ) → ℂ} (hf : IsGermCombination w p f) (hg : IsGermCombination w p g) :
    IsGermCombination w p (fun z => f z - g z) :=
  (hf.add hg.neg).congr (Eventually.of_forall fun z => by ring)

theorem sum {ι : Type*} (s : Finset ι) {f : ι → (σ → ℂ) → ℂ} (h : ∀ i ∈ s, IsGermCombination w p (f i)) :
    IsGermCombination w p (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : IsGermCombination w p fun _ => 0)
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact (h1.add h2).congr (Eventually.of_forall fun z => by rw [Finset.sum_insert ha])

theorem pow_sub_pow {f g : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w) (hg : AnalyticAt ℂ g w)
    (h : IsGermCombination w p (fun z => f z - g z)) (n : ℕ) :
    IsGermCombination w p (fun z => f z ^ n - g z ^ n) := by
  induction n with
  | zero => exact zero.congr (Eventually.of_forall fun z => by simp)
  | succ n ih =>
    exact ((mul_left hf ih).add (mul_left (hg.pow n) h)).congr
      (Eventually.of_forall fun z => by simp only [Pi.pow_apply]; ring)

theorem prod_sub_prod {ι : Type*} (s : Finset ι) {f g : ι → (σ → ℂ) → ℂ}
    (hf : ∀ i, AnalyticAt ℂ (f i) w) (hg : ∀ i, AnalyticAt ℂ (g i) w)
    (h : ∀ i, IsGermCombination w p (fun z => f i z - g i z)) :
    IsGermCombination w p (fun z => ∏ i ∈ s, f i z - ∏ i ∈ s, g i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact zero.congr (Eventually.of_forall fun z => by simp)
  | insert a s ha ih =>
    have hgs : AnalyticAt ℂ (fun z => ∏ i ∈ s, g i z) w := Finset.analyticAt_fun_prod s fun i _ => hg i
    exact ((mul_left (hf a) ih).add (mul_left hgs (h a))).congr
      (Eventually.of_forall fun z => by rw [Finset.prod_insert ha, Finset.prod_insert ha]; ring)

end IsGermCombination

def analyticSubring {d : ℕ} (y₀ : Fin d → ℂ) : Subring ((Fin d → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f y₀}
  mul_mem' ha hb := AnalyticAt.mul ha hb
  one_mem' := analyticAt_const
  add_mem' ha hb := AnalyticAt.add ha hb
  zero_mem' := analyticAt_const
  neg_mem' ha := AnalyticAt.neg ha

def evalAt {d : ℕ} (y₀ y : Fin d → ℂ) : analyticSubring y₀ →+* ℂ :=
  (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y).comp (analyticSubring y₀).subtype

def pev {d : ℕ} {y₀ : Fin d → ℂ} (y : Fin d → ℂ) (t : ℂ) : (analyticSubring y₀)[X] →+* ℂ :=
  (Polynomial.evalRingHom t).comp (Polynomial.mapRingHom (evalAt y₀ y))

section pev

variable {d : ℕ} {y₀ : Fin d → ℂ}

@[simp] theorem pev_C (y : Fin d → ℂ) (t : ℂ) (f : analyticSubring y₀) :
    pev y t (C f) = (f : (Fin d → ℂ) → ℂ) y := by
  simp [pev, evalAt]

@[simp] theorem pev_X (y : Fin d → ℂ) (t : ℂ) : pev (y₀ := y₀) y t X = t := by
  simp [pev]

theorem pev_eq_sum_range (H : (analyticSubring y₀)[X]) {n : ℕ} (hn : H.natDegree < n) (y : Fin d → ℂ)
    (t : ℂ) : pev y t H = ∑ i ∈ Finset.range n, (H.coeff i : (Fin d → ℂ) → ℂ) y * t ^ i := by
  simp only [pev, RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, coe_mapRingHom, eval_map]
  rw [eval₂_eq_sum_range' _ hn]
  rfl

theorem analyticAt_pev_comp {σ : Type} [Fintype σ] (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (ℓ : (σ → ℂ) →L[ℂ] ℂ) (H : (analyticSubring (A w))[X]) :
    AnalyticAt ℂ (fun z => pev (A z) (ℓ z) H) w := by
  have e : (fun z => pev (A z) (ℓ z) H) =
      fun z => ∑ i ∈ Finset.range (H.natDegree + 1), (H.coeff i : (Fin d → ℂ) → ℂ) (A z) * ℓ z ^ i :=
    funext fun z => pev_eq_sum_range H (Nat.lt_succ_self _) _ _
  rw [e]
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact (AnalyticAt.comp (g := ((H.coeff i : analyticSubring (A w)) : (Fin d → ℂ) → ℂ))
    (H.coeff i).2 (A.analyticAt w)).mul ((ℓ.analyticAt w).pow i)

end pev

def presPoly {d N : ℕ} {y₀ : Fin d → ℂ} (c : Fin N → (Fin d → ℂ) → ℂ) (hc : ∀ j, AnalyticAt ℂ (c j) y₀) :
    (analyticSubring y₀)[X] :=
  X ^ N + ∑ j : Fin N, C (⟨c j, hc j⟩ : analyticSubring y₀) * X ^ (j : ℕ)

theorem presPoly_monic {d N : ℕ} {y₀ : Fin d → ℂ} (c : Fin N → (Fin d → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) y₀) : (presPoly c hc).Monic :=
  monic_X_pow_add (degree_sum_fin_lt _)

theorem presPoly_degree {d N : ℕ} {y₀ : Fin d → ℂ} (c : Fin N → (Fin d → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) y₀) : (presPoly c hc).degree = N := by
  unfold presPoly
  rw [degree_add_eq_left_of_degree_lt] <;> rw [degree_X_pow]
  exact degree_sum_fin_lt _

theorem pev_presPoly {d N : ℕ} {y₀ : Fin d → ℂ} (c : Fin N → (Fin d → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) y₀) (y : Fin d → ℂ) (t : ℂ) :
    pev y t (presPoly c hc) = t ^ N + ∑ j, c j y * t ^ (j : ℕ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [presPoly, map_sum]

theorem pev_eq_zero_of_presentation {σ : Type} [Fintype σ] {w : σ → ℂ} {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ}
    {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {ℓ : (σ → ℂ) →L[ℂ] ℂ} {N : ℕ} {c : Fin N → (Fin d → ℂ) → ℂ}
    {δ : (Fin d → ℂ) → ℂ} (hP : IsPrimitivePresentation w p A ℓ c δ) (H : (analyticSubring (A w))[X])
    (hH : IsGermCombination w p (fun z => pev (A z) (ℓ z) H)) :
    ∀ᶠ y in 𝓝 (A w), ∀ t : ℂ, t ^ N + ∑ j, c j y * t ^ (j : ℕ) = 0 → pev y t H = 0 := by
  obtain ⟨hc, -, h1, h2, -⟩ := hP
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact Eventually.of_forall fun y t ht => by simp at ht
  set F := presPoly c hc with hFdef
  have hmon : F.Monic := presPoly_monic c hc
  set R := H %ₘ F with hRdef
  set Q := H /ₘ F with hQdef
  have hdec : ∀ y t, pev y t H = pev y t R + pev y t F * pev y t Q := by
    intro y t
    rw [← map_mul, ← map_add (f := _), hRdef, hQdef, modByMonic_add_div]
  have hRdeg : R.natDegree < N := by
    by_cases hR0 : R = 0
    · rw [hR0, natDegree_zero]; exact hN
    rw [natDegree_lt_iff_degree_lt hR0, ← presPoly_degree c hc]
    exact degree_modByMonic_lt _ hmon
  have hRsum : ∀ y t, pev y t R = ∑ j : Fin N, (R.coeff j : (Fin d → ℂ) → ℂ) y * t ^ (j : ℕ) := by
    intro y t
    rw [pev_eq_sum_range R hRdeg, Fin.sum_univ_eq_sum_range (fun i => (R.coeff i : (Fin d → ℂ) → ℂ) y * t ^ i)]
  have hRP : IsGermCombination w p
      (fun z => ∑ j : Fin N, (R.coeff j : (Fin d → ℂ) → ℂ) (A z) * ℓ z ^ (j : ℕ)) := by
    refine (hH.sub (IsGermCombination.mul_left (analyticAt_pev_comp w A ℓ Q) h1)).congr
      (Eventually.of_forall fun z => ?_)
    rw [← hRsum, hdec, pev_presPoly]
    ring
  have hzero := h2 (fun j => (R.coeff j : (Fin d → ℂ) → ℂ)) (fun j => (R.coeff j).2) hRP
  filter_upwards [eventually_all.2 hzero] with y hy t ht
  rw [hdec, hRsum, pev_presPoly, ht, zero_mul, add_zero]
  exact Finset.sum_eq_zero fun j _ => by rw [hy j, zero_mul]

theorem roots_near_of_centred {E : Type*} [TopologicalSpace E] {n : ℕ} (b : Fin n → E → ℂ) (y₀ : E) (u : ℂ)
    (hb : ∀ j, ContinuousAt (b j) y₀) (h0 : ∀ T : ℂ, T ^ n + ∑ j, b j y₀ * T ^ (j : ℕ) = (T - u) ^ n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 y₀, ∀ x : ℂ, x ^ n + ∑ j, b j y * x ^ (j : ℕ) = 0 → ‖x - u‖ < ε := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact Eventually.of_forall fun y x hx => by simp at hx
  set S : E → ℝ := fun y => ∑ j, ‖b j y‖ with hS
  set B : ℝ := max 1 (S y₀ + 1) with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hSt : Tendsto S (𝓝 y₀) (𝓝 (S y₀)) :=
    tendsto_finsetSum _ fun j _ => (hb j).tendsto.norm
  have hDt : Tendsto (fun y => ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ)) (𝓝 y₀) (𝓝 0) := by
    have : Tendsto (fun y => ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ)) (𝓝 y₀)
        (𝓝 (∑ j : Fin n, ‖b j y₀ - b j y₀‖ * B ^ (j : ℕ))) :=
      tendsto_finsetSum _ fun j _ => ((tendsto_const_nhds.sub (hb j).tendsto).norm).mul_const _
    simpa using this
  have hεn : (0 : ℝ) < ε ^ n := pow_pos hε n
  filter_upwards [hSt.eventually (gt_mem_nhds (lt_add_one (S y₀))), hDt.eventually (gt_mem_nhds hεn)]
    with y hSy hDy x hx

  have hxB : ‖x‖ ≤ B := by
    by_cases hx1 : ‖x‖ ≤ 1
    · exact hx1.trans hB1
    replace hx1 := lt_of_not_ge hx1
    have hxn : x ^ n = -∑ j, b j y * x ^ (j : ℕ) := eq_neg_of_add_eq_zero_left hx
    have hle : ‖x‖ ^ n ≤ S y * ‖x‖ ^ (n - 1) := by
      calc ‖x‖ ^ n = ‖∑ j, b j y * x ^ (j : ℕ)‖ := by rw [← norm_pow, hxn, norm_neg]
        _ ≤ ∑ j, ‖b j y * x ^ (j : ℕ)‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin n, ‖b j y‖ * ‖x‖ ^ (n - 1) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1.le (by omega)) (norm_nonneg _)
        _ = S y * ‖x‖ ^ (n - 1) := by rw [hS, Finset.sum_mul]
    have hpos : 0 < ‖x‖ ^ (n - 1) := pow_pos (zero_lt_one.trans hx1) _
    have : ‖x‖ * ‖x‖ ^ (n - 1) ≤ S y * ‖x‖ ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hn]; exact hle
    have hxS : ‖x‖ ≤ S y := le_of_mul_le_mul_right this hpos
    exact hxS.trans (hSy.le.trans (le_max_right _ _))

  have hid : (x - u) ^ n = ∑ j, (b j y₀ - b j y) * x ^ (j : ℕ) := by
    rw [← h0 x]
    have : x ^ n = -∑ j, b j y * x ^ (j : ℕ) := eq_neg_of_add_eq_zero_left hx
    rw [this]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hle : ‖x - u‖ ^ n ≤ ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ) := by
    calc ‖x - u‖ ^ n = ‖∑ j, (b j y₀ - b j y) * x ^ (j : ℕ)‖ := by rw [← norm_pow, hid]
      _ ≤ ∑ j, ‖(b j y₀ - b j y) * x ^ (j : ℕ)‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n, ‖b j y₀ - b j y‖ * B ^ (j : ℕ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxB _) (norm_nonneg _)
  have : ‖x - u‖ ^ n < ε ^ n := hle.trans_lt hDy
  exact lt_of_pow_lt_pow_left₀ n hε.le this

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RingKrullDimQuotientMinimalPrimeAddOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

theorem graphChart_of_eq_on_open {n d : ℕ} {Y Y' U : Set (Fin n → ℂ)} {q : Fin n → ℂ}
    (hU : IsOpen U) (hqU : q ∈ U) (hYU : Y' ∩ U = Y ∩ U)
    (h : ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
      (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ g O ∧
        (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O) :
    ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
      (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ g O ∧
        (∀ y ∈ O, A (g y) = y) ∧ Y' ∩ V = g '' O := by
  obtain ⟨A, O, V, g, hO, hV, hqV, hg, hAg, hYV⟩ := h
  refine ⟨A, O ∩ g ⁻¹' U, V ∩ U, g, hg.continuousOn.isOpen_inter_preimage hO hU, hV.inter hU, ⟨hqV, hqU⟩,
    fun y hy => hg y hy.1, fun y hy => hAg y hy.1, ?_⟩
  rw [Set.image_inter_preimage, ← hYV]
  ext x
  constructor
  · rintro ⟨hx, hxV, hxU⟩
    have hx' : x ∈ Y ∩ U := by rw [← hYU]; exact ⟨hx, hxU⟩
    exact ⟨⟨hx'.1, hxV⟩, hxU⟩
  · rintro ⟨⟨hx, hxV⟩, hxU⟩
    have hx' : x ∈ Y' ∩ U := by rw [hYU]; exact ⟨hx, hxU⟩
    exact ⟨hx'.1, hxV, hxU⟩

theorem ringKrullDim_quotient_minimalPrime_add_one {n : ℕ} {V W : Ideal (MvPolynomial (Fin n) ℂ)} [hVp : V.IsPrime]
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∉ V) (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes)
    (hfin : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V) ≠ ⊤) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) + 1 = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V) := by
  have hPW : V ≤ W := le_sup_left.trans hW.1.2
  have hfW : f ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hq : W.map (Ideal.Quotient.mk V) ∈ (Ideal.span {Ideal.Quotient.mk V f}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk V f} = (Ideal.span {f}).map (Ideal.Quotient.mk V) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm]
    exact ⟨W, hW, rfl⟩
  have : (W.map (Ideal.Quotient.mk V)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk V f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hh : (W.map (Ideal.Quotient.mk V)).height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h0
    have : Ideal.Quotient.mk V f ∈ W.map (Ideal.Quotient.mk V) := Ideal.mem_map_of_mem _ hfW
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hf this
  have : IsDomain (MvPolynomial (Fin n) ℂ ⧸ V) := Ideal.Quotient.isDomain V
  have : Algebra.FiniteType ℂ (MvPolynomial (Fin n) ℂ ⧸ V) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ V) (Ideal.Quotient.mkₐ_surjective ℂ V)
  have : IsNoetherianRing (MvPolynomial (Fin n) ℂ ⧸ V) := Algebra.FiniteType.isNoetherianRing ℂ _
  have : FiniteRingKrullDim (MvPolynomial (Fin n) ℂ ⧸ V) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨fun h => by
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ V)
      rw [h] at h0
      exact absurd h0 (by simp), hfin⟩
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field ℂ (MvPolynomial (Fin n) ℂ ⧸ V)
  have key := ReciprocityTheory.ChartRestriction.G.Geo.DimF.dim_quot_add_height (A := MvPolynomial (Fin n) ℂ ⧸ V)
    (fun M N hM hN => (hs M hM).trans (hs N hN).symm) (W.map (Ideal.Quotient.mk V))
  rw [hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)] at key
  exact_mod_cast key

theorem ringKrullDim_quotient_sup_span_lt {R : Type*} [CommRing R] {L : Ideal R} {f : R} {d : ℕ}
    (hf : ∀ W ∈ L.minimalPrimes, f ∉ W) (hd : ∀ W ∈ L.minimalPrimes, ringKrullDim (R ⧸ W) = d) :
    ringKrullDim (R ⧸ (L ⊔ Ideal.span {f})) < d := by
  rw [ringKrullDim_quotient, Order.krullDim_lt_coe_iff]
  intro l
  have hLP : L ≤ l.head.1.asIdeal := fun x hx => l.head.2 (Ideal.mem_sup_left hx)
  have hfP : f ∈ l.head.1.asIdeal := l.head.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨W, hW, hWP⟩ := Ideal.exists_minimalPrimes_le hLP
  let W' : PrimeSpectrum R := ⟨W, hW.1.1⟩
  have hlt : W' < l.head.1 := lt_of_le_of_ne hWP fun h => hf W hW (by rw [← h] at hfP; exact hfP)
  have h1 : (l.length : ℕ∞) ≤ Order.coheight l.head.1 := by
    exact Order.length_le_coheight_head (p := l.map Subtype.val (fun _ _ => id))
  have h2 : Order.coheight l.head.1 + 1 ≤ Order.coheight W' := Order.coheight_add_one_le hlt
  have hIci : Set.Ici W' = PrimeSpectrum.zeroLocus (R := R) (W : Set R) := by
    ext p
    exact Iff.rfl
  have h3 : ((Order.coheight W' : ℕ∞) : WithBot ℕ∞) = (d : WithBot ℕ∞) := by
    rw [Order.coheight_eq_krullDim_Ici, hIci, ← ringKrullDim_quotient]
    exact hd W hW
  have h3' : Order.coheight W' = (d : ℕ∞) := by exact_mod_cast h3
  have h4 : ((l.length + 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞) := by
    rw [← h3']
    push_cast
    calc (l.length : ℕ∞) + 1 ≤ Order.coheight l.head.1 + 1 := by gcongr
      _ ≤ Order.coheight W' := h2
  have h5 : l.length + 1 ≤ d := by exact_mod_cast h4
  omega

theorem graphChart_of_frameGraphGeneric (hG : FrameGraphGeneric.Statement) {n e : ℕ}
    (W : Ideal (MvPolynomial (Fin n) ℂ)) (hW : W.IsPrime)
    (he : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = e) :
    ∃ h : MvPolynomial (Fin n) ℂ, h ∉ W ∧ ∀ z ∈ zeroSet W, eval z h ≠ 0 →
      ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin e → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ g O ∧
          (∀ y ∈ O, A (g y) = y) ∧ zeroSet W ∩ V = g '' O := by
  obtain ⟨I₀, h, hcard, hhW, hreg⟩ := hG n e W hW he (EuclideanSpace.basisFun (Fin n) ℂ)
  let T : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ) :=
    ((EuclideanSpace.equiv (Fin n) ℂ : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)))
  have hT : ∀ x i, T x i = x i := fun x i => rfl
  have hS : ∀ w i, S w i = w i := fun w i => rfl
  have hST : ∀ x, S (T x) = x := fun x => funext fun i => by rw [hS, hT]
  have hTS : ∀ w, T (S w) = w := fun w => by ext i; rw [hT, hS]
  have hZ : ∀ x : Fin n → ℂ, x ∈ zeroSet W ↔ T x ∈ zeroSetEuc W := by
    intro x
    have hx : (fun i => T x i) = x := funext fun i => hT x i
    simp only [zeroSet, zeroSetEuc, Set.mem_ofPred_eq, hx]
  refine ⟨h, hhW, fun z hz hzh => ?_⟩
  have hzh' : eval (fun i => T z i) h ≠ 0 := by
    have hx : (fun i => T z i) = z := funext fun i => hT z i
    rwa [hx]
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, hgraph⟩ := hreg (T z) ((hZ z).mp hz) hzh'
  let eI : I₀ ≃ Fin e := I₀.equivFinOfCardEq hcard
  let Ψ : (Fin e → ℂ) →L[ℂ] (I₀ → ℂ) :=
    ContinuousLinearMap.pi fun i : I₀ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) (eI i)
  let A : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) :=
    ContinuousLinearMap.pi fun k : Fin e =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) ((eI.symm k : I₀) : Fin n)
  have hΨ : ∀ y i, Ψ y i = y (eI i) := fun y i => rfl
  have hA : ∀ x k, A x k = x ((eI.symm k : I₀) : Fin n) := fun x k => rfl
  have hO : IsOpen (Ψ ⁻¹' Ω) := hΩ.preimage Ψ.continuous
  refine ⟨A, Ψ ⁻¹' Ω, T ⁻¹' V, fun y => S (g (Ψ y)), hO, hV.preimage T.continuous, hzV, ?_, ?_, ?_⟩
  · exact IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn_fin hO (S.differentiable.comp_differentiableOn
      (hg.comp Ψ.differentiable.differentiableOn fun y hy => hy))
  · intro y hy
    ext k
    have h1 := congrFun (hproj (Ψ y) hy) (eI.symm k)
    simp only [frameProj, EuclideanSpace.basisFun_inner] at h1
    show A (S (g (Ψ y))) k = y k
    rw [hA, hS, h1, hΨ, Equiv.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨hxZ, hxV⟩
      have hmem : T x ∈ zeroSetEuc W ∩ V := ⟨(hZ x).mp hxZ, hxV⟩
      rw [hgraph] at hmem
      obtain ⟨w, hw, hgw⟩ := hmem
      have hΨw : Ψ (fun k => w (eI.symm k)) = w := funext fun i => by simp [hΨ]
      refine ⟨fun k => w (eI.symm k), ?_, ?_⟩
      · show Ψ _ ∈ Ω
        rwa [hΨw]
      · simp only [hΨw, hgw, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (Ψ y) ∈ zeroSetEuc W ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      refine ⟨(hZ _).mpr ?_, ?_⟩
      · rw [hTS]
        exact hmem.1
      · show T (S (g (Ψ y))) ∈ V
        rw [hTS]
        exact hmem.2

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeSliceSheetParam
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def ConeSliceSheetParam.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (A : Matrix (Fin e) (Fin n) ℂ),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J → IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A →
      ∃ (U D : ℕ → Set (Fin e → ℂ)) (N : ℕ → ℕ)
        (s : (k : ℕ) → Fin (N k) → (Fin e → ℂ) → Fin n → ℂ),
        (∀ k, IsOpen (U k) ∧ MeasurableSet (D k) ∧ D k ⊆ U k ∧
          ∀ j, DifferentiableOn ℂ (s k j) (U k)) ∧
        Pairwise (Function.onFun Disjoint D) ∧
        volume (⋃ k, D k)ᶜ = 0 ∧
        (∀ k, ∀ y ∈ U k,
          ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y = Set.range (fun j => s k j y) ∧
          Function.Injective (fun j => s k j y) ∧
          ∀ j, IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) (s k j)) ∧
        Set.InjOn (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
            q.2.2 • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s q.1.1 q.1.2 q.2.1))
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ∧
        (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
            q.2.2 • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s q.1.1 q.1.2 q.2.1)) ''
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ⊆
          {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0} ∧
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
          ({z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0} \
            (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
              q.2.2 • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s q.1.1 q.1.2 q.2.1)) ''
              {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0}) = 0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffGradient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def CutOffGradient.Statement : Prop :=
  ∃ K : ℝ, ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (k : ℕ)
    (y : Fin (d + 1) → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
        (vecCons (logLogCutAlong A P k) φ) y ≤ K / ((k : ℝ) + 1) * tubeDens J A P R φ y ∧
    chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
        (vecCons (fun x => logLogCutAlong A P k x ^ 2 / 2) φ) y ≤
      K / ((k : ℝ) + 1) * tubeDens J A P R φ y ∧
    chartAbsDens J A ((Metric.closedBall 0 R).indicator (logLogCutAlong A P k))
        (vecCons (logLogCutAlong A P k) φ) y ≤ K / ((k : ℝ) + 1) * tubeDens J A P R φ y

end

end GroundTheory.Heights₂.Heights
end

