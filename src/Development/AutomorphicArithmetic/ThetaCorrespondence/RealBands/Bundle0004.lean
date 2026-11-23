module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.DecaysZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Bundle0003
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.InvMemFlagN
section
open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

private theorem act_mul {n : ℕ} {ε : Fin n → Bool} (g h : UJ ε) (y : Fin n → ℂ) :
    uMat (g * h) *ᵥ y = uMat g *ᵥ (uMat h *ᵥ y) := by
  rw [mulVec_mulVec]; rfl

private theorem act_inv {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) (y : Fin n → ℂ) :
    uMat g⁻¹ *ᵥ (uMat g *ᵥ y) = y := by
  rw [← act_mul, inv_mul_cancel]; exact one_mulVec y

private theorem act_inv' {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) (y : Fin n → ℂ) :
    uMat g *ᵥ (uMat g⁻¹ *ᵥ y) = y := by
  rw [← act_mul, mul_inv_cancel]; exact one_mulVec y

private theorem keeps_perp {n a : ℕ} {ε : Fin n → Bool} {W : Flag n a} {p : UJ ε} (hp : p ∈ parab ε W)
    {y : Fin n → ℂ} (hy : ∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ y) = 0) :
    ∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ (uMat p *ᵥ y)) = 0 := by
  intro z hz
  have hpiS : ∀ i, ∀ y ∈ W i, uMat p⁻¹ *ᵥ y ∈ W i := (parab ε W).inv_mem hp
  have h1 : Jm ε *ᵥ (uMat p *ᵥ y) = (uMat p⁻¹)ᴴ *ᵥ (Jm ε *ᵥ y) := by
    rw [mulVec_mulVec, mulVec_mulVec, conjTranspose_inv_mul_Jm]
  rw [h1, dotProduct_mulVec, ← star_mulVec]
  exact hy _ (hpiS _ _ hz)

private theorem conj_mem {n a : ℕ} {ε : Fin n → Bool} {W : Flag n a} {p m : UJ ε} (hp : p ∈ parab ε W)
    (hm : m ∈ flagN ε W) : p⁻¹ * m * p ∈ flagN ε W := by
  have e : ∀ y, uMat (p⁻¹ * m * p) *ᵥ y - y = uMat p⁻¹ *ᵥ (uMat m *ᵥ (uMat p *ᵥ y) - uMat p *ᵥ y) := fun y => by
    rw [mulVec_sub, act_inv, act_mul, act_mul]
  have hi := (parab ε W).inv_mem hp
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · rw [e]; exact hi _ _ (hm.1 i _ (hp _ y hy))
  · rw [e]; exact hi _ _ (hm.2 _ (keeps_perp hp hy))

private theorem comm_mem {n a : ℕ} {ε : Fin n → Bool} {W : Flag n a} {p t : UJ ε} {x : Fin a → ℝ}
    (hp : p ∈ parab ε W) (ht : IsSplit ε W x t) : t⁻¹ * (p * t * p⁻¹) ∈ flagN ε W := by
  have hpS : ∀ i, ∀ y ∈ W i, uMat p *ᵥ y ∈ W i := hp
  have hpiS : ∀ i, ∀ y ∈ W i, uMat p⁻¹ *ᵥ y ∈ W i := (parab ε W).inv_mem hp
  have htS : ∀ i, ∀ y ∈ W i, uMat t *ᵥ y ∈ W i := fun i y hy => (ht.1 i y hy).1
  have htiS : ∀ i, ∀ y ∈ W i, uMat t⁻¹ *ᵥ y ∈ W i :=
    (parab ε W).inv_mem (show t ∈ parab ε W from htS)
  simp only [flagN, Set.mem_setOf_eq]
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · have e : uMat (t⁻¹ * (p * t * p⁻¹)) *ᵥ y - y =
        uMat t⁻¹ *ᵥ (uMat p *ᵥ (uMat t *ᵥ (uMat p⁻¹ *ᵥ y) -
          (Real.exp (x i) : ℂ) • (uMat p⁻¹ *ᵥ y))) -
          uMat t⁻¹ *ᵥ (uMat t *ᵥ y - (Real.exp (x i) : ℂ) • y) := by
      simp only [act_mul, mulVec_sub, mulVec_smul, act_inv, act_inv']
      abel
    rw [e]
    exact Submodule.sub_mem _ (htiS _ _ (hpS _ _ (ht.2.1 i _ (hpiS _ _ hy))))
      (htiS _ _ (ht.2.1 i y hy))
  · have e : uMat (t⁻¹ * (p * t * p⁻¹)) *ᵥ y - y =
        uMat t⁻¹ *ᵥ (uMat p *ᵥ (uMat t *ᵥ (uMat p⁻¹ *ᵥ y) - uMat p⁻¹ *ᵥ y)) -
          uMat t⁻¹ *ᵥ (uMat t *ᵥ y - y) := by
      simp only [act_mul, mulVec_sub, act_inv, act_inv']
      abel
    rw [e]
    exact Submodule.sub_mem _
      (htiS _ _ (hpS _ _ (ht.2.2 _ (keeps_perp ((parab ε W).inv_mem hp) hy))))
      (htiS _ _ (ht.2.2 y hy))

theorem UpperTheory.Lit.Cusp.exists_isRay :
    ∀ (n : ℕ) (ε : Fin n → Bool) (j : Fin 1 → ℕ) (W : Flag n 1), IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
      ∃ (a : ℝ → UJ ε) (H : UJ ε → ℝ), IsRay (flagN ε W) a H := by
  intro n ε j W hW hj
  obtain ⟨a, ha_cont, ha_add, ha_split⟩ := exists_split n ε j W hW
  obtain ⟨h, hh_cont, hh1, hhK, hhP⟩ := exists_height hW hj
  obtain ⟨⟨N, hN⟩, -, -⟩ := UnipRad.flagN_subgroup_closed_keeps n ε 1 j W hW
  have hone_levi : (1 : UJ ε) ∈ leviOne ε W := (leviOne ε W).one_mem
  have hone_N : (1 : UJ ε) ∈ flagN ε W := hN ▸ N.one_mem
  have hN_inv : ∀ m ∈ flagN ε W, m⁻¹ ∈ flagN ε W := by
    intro m hm
    rw [← hN] at hm ⊢
    exact N.inv_mem hm
  have hsplit_par : ∀ t, a t ∈ parab ε W := fun t =>
    show ∀ i, ∀ y ∈ W i, uMat (a t) *ᵥ y ∈ W i from fun i y hy => ((ha_split t).1 i y hy).1
  have hheight : ∀ x t g, IsSplit ε W x t → h (t * g) = x + h g := by
    intro x t g hs
    have := hhP 1 hone_N 1 hone_levi x t hs g
    rwa [one_mul, one_mul] at this
  have ha0 : a 0 = 1 := by
    have h0 := congrArg (fun g => (a 0)⁻¹ * g) (ha_add 0 0)
    simp only [add_zero, inv_mul_cancel, ← mul_assoc, one_mul] at h0
    exact h0.symm
  have hainv : ∀ t, (a t)⁻¹ = a (-t) := fun t => by
    have h2 : a t * a (-t) = 1 := by rw [← ha_add, add_neg_cancel, ha0]
    exact (eq_inv_of_mul_eq_one_right h2).symm
  have hK : IsCompact (KG ε : Set (UJ ε)) := isCompact_iff_compactSpace.2 (instCompactKG n ε)
  have hkmem : ∀ k ∈ maxK ε, k ∈ KG ε := fun k hk => by
    rw [← SetLike.mem_coe, KG_eq]
    exact hk
  have hshift : ∀ y g : UJ ε, ∃ k ∈ KG ε, h (y * g) = h y + h (k * g) := by
    intro y g
    obtain ⟨k, hkK, hk⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hW y
    obtain ⟨u, hu, m, hm, x, t, hs, hp⟩ := exists_langlands_decomp hW hj hk
    have hkG := hkmem k hkK
    refine ⟨k, hkG, ?_⟩
    have e1 : y * g = u * m * t * (k * g) := by
      rw [← hp]
      group
    have e2 : y = u * m * t * k := by
      rw [← hp]
      group
    have hk0 : h k = 0 := by
      have := hhK 1 k hkG
      rwa [one_mul, hh1] at this
    rw [e1, hhP u hu m hm x t hs, e2, hhP u hu m hm x t hs, hk0, add_zero]
  refine ⟨a, fun g => -(h g⁻¹ 0), ha_cont, ha_add, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t m hm
    exact conj_mem (hsplit_par t) hm
  · exact ((continuous_apply 0).comp (hh_cont.comp continuous_inv)).neg
  · intro g m hm
    show -(h (g * m)⁻¹ 0) = -(h g⁻¹ 0)
    have := hhP m⁻¹ (hN_inv m hm) 1 hone_levi 0 1 isSplit_one g⁻¹
    rw [mul_one, mul_one, zero_add] at this
    rw [_root_.mul_inv_rev, this]
  · intro g t
    show -(h (g * a t)⁻¹ 0) = -(h g⁻¹ 0) + t
    rw [_root_.mul_inv_rev, hainv, hheight _ _ _ (ha_split (-t))]
    simp only [Pi.add_apply]
    ring
  · intro D hD
    have hS : IsCompact ((fun q : UJ ε × UJ ε => q.1 * q.2) '' ((KG ε : Set (UJ ε)) ×ˢ D)) :=
      (hK.prod hD).image continuous_mul
    obtain ⟨c, hc⟩ := hS.exists_bound_of_continuousOn (f := fun g => h g 0)
      ((continuous_apply 0).comp hh_cont).continuousOn
    refine ⟨c, fun g hg x => ?_⟩
    obtain ⟨k, hk, hyg⟩ := hshift x⁻¹ g
    show |-(h (g⁻¹ * x)⁻¹ 0) - -(h x⁻¹ 0)| ≤ c
    rw [_root_.mul_inv_rev, _root_.inv_inv, hyg]
    have hb := hc (k * g) ⟨(k, g), ⟨hk, hg⟩, rfl⟩
    rw [Real.norm_eq_abs] at hb
    have e : -((h x⁻¹ + h (k * g)) 0) - -(h x⁻¹ 0) = -(h (k * g) 0) := by
      simp only [Pi.add_apply]
      ring
    rw [e, abs_neg]
    exact hb
  · refine ⟨(KG ε : Set (UJ ε)), hK, fun x => ?_⟩
    obtain ⟨k, hkK, hk⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hW x⁻¹
    have hkG := hkmem k hkK
    refine ⟨k⁻¹, (KG ε).inv_mem hkG, fun t => ?_⟩
    have hq : x⁻¹ * k⁻¹ ∈ parab ε W := hk
    refine ⟨(a t)⁻¹ * ((x⁻¹ * k⁻¹) * a t * (x⁻¹ * k⁻¹)⁻¹), comm_mem hq (ha_split t), ?_⟩
    group
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Weight
section
open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

private lemma wt_le {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) (x : MatrixCoordinates n)
    (h : hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4) :
    (wt g)⁻¹ ≤ (Real.sqrt n + 1) ^ (2 * n ^ 2 + 1) * (1 + ‖x‖) ^ (-((2 * n ^ 2 + 1 : ℕ) : ℝ)) := by
  set R : ℝ := Real.sqrt (hs (umat g)) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hs0 : 0 ≤ hs (umat g) := by unfold hs; positivity
  have hg : hs (coeMatrixAlt ε g) ≤ R ^ 2 := by rw [hR, Real.sq_sqrt hs0]; exact le_rfl
  have hn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hρ0 : 0 ≤ R * (Real.sqrt n + 1) := by positivity
  have hx : ‖x‖ ≤ R * (Real.sqrt n + 1) := by
    rw [pi_norm_le_iff_of_nonneg hρ0]
    intro i
    rw [pi_norm_le_iff_of_nonneg hρ0]
    intro j
    have := norm_entry_mul_near_one_le (g := coeMatrixAlt ε g) hR0 hg h i j
    rw [← Matrix.mul_assoc, determinant_character_mul_inv, Matrix.one_mul] at this
    exact this
  have h1 : 1 + ‖x‖ ≤ (Real.sqrt n + 1) * (1 + R) := by nlinarith
  have h2 : (1 + ‖x‖) ^ (2 * n ^ 2 + 1) ≤ (Real.sqrt n + 1) ^ (2 * n ^ 2 + 1) * wt g := by
    unfold wt
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 _
  have hw : 0 < wt g := by unfold wt; positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, inv_eq_one_div,
    div_le_div_iff₀ hw (by positivity), one_mul]
  exact h2

private lemma slice_le {n : ℕ} {ε : Fin n → Bool} (S : Subgroup (UJ ε)) (ν : Measure (UJ ε))
    (hν : IsHaarSub (S : Set (UJ ε)) ν) (x : MatrixCoordinates n) :
    ν {g | hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4} ≤
      ν {k | hsG k ≤ (2 * Real.sqrt n + 1) ^ 2} := by
  obtain ⟨-, -, h0, hinv⟩ := hν
  set A : Set (UJ ε) := {g | hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4} with hA
  set W : Set (UJ ε) := {k | hsG k ≤ (2 * Real.sqrt n + 1) ^ 2} with hW
  have hWm : MeasurableSet W :=
    (isClosed_le (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)) continuous_const).measurableSet
  by_cases hne : (A ∩ (S : Set (UJ ε))).Nonempty
  · obtain ⟨h, hh, hS⟩ := hne
    calc ν A ≤ ν ((fun g => h⁻¹ * g) ⁻¹' W) := by
          refine measure_mono fun g hg => ?_
          show hs (coeMatrixAlt ε (h⁻¹ * g)) ≤ _
          refine frobenius_bound_of_mul_near_one hg hh ?_
          rw [determinant_character_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (coeMatrixAlt ε h⁻¹),
            determinant_character_mul_inv, Matrix.mul_one]
      _ = ν.map (fun g => h⁻¹ * g) W := (Measure.map_apply (measurable_const_mul _) hWm).symm
      _ = ν W := by rw [hinv h⁻¹ (S.inv_mem hS)]
  · have : ν A = 0 := measure_mono_null (show A ⊆ (S : Set (UJ ε))ᶜ from fun g hg hS => hne ⟨g, hg, hS⟩) h0
    rw [this]
    exact bot_le

theorem UpperTheory.Lit.Cusp.integrable_wt :
    ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (UJ ε)) (ν : Measure (UJ ε)), IsHaarSub (S : Set (UJ ε)) ν →
      Integrable (fun g : UJ ε => (wt g)⁻¹) ν := by
  intro n ε S ν hν
  classical
  haveI : IsFiniteMeasureOnCompacts ν := hν.2.1
  let lam : Measure (MatrixCoordinates n) := Measure.addHaar
  let O : Set (MatrixCoordinates n) := {x | hs (Matrix.of x - 1) < 1 / 4}
  let W : Set (UJ ε) := {k | hsG k ≤ (2 * Real.sqrt n + 1) ^ 2}
  have hof : Continuous (fun x : MatrixCoordinates n => Matrix.of x) := continuous_id
  have hO_open : IsOpen O :=
    isOpen_lt (continuous_hs_real_place_taylor.comp (hof.sub continuous_const)) continuous_const
  have hO_pos : 0 < lam O := hO_open.measure_pos lam ⟨Matrix.of.symm 1, by simp [O, hs]⟩
  have hW_fin : ν W < ⊤ := by
    have hc : IsCompact W := by
      have := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage
        ((hermitian_small_ball n ε).1 ((2 * Real.sqrt n + 1) ^ 2))
      convert this using 1
      ext g
      exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
    exact hc.measure_lt_top
  have hwpos : ∀ g : UJ ε, 0 < wt g := fun g => by unfold wt; positivity
  have hwc : Continuous fun g : UJ ε => (wt g)⁻¹ := by
    refine Continuous.inv₀ ?_ fun g => (hwpos g).ne'
    exact (continuous_const.add (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)).sqrt).pow _
  let w : UJ ε → ENNReal := fun g => ENNReal.ofReal (wt g)⁻¹
  have hwm : Measurable w := hwc.measurable.ennreal_ofReal
  let U : Set (UJ ε × MatrixCoordinates n) := {p | hs (coeMatrixAlt ε p.1⁻¹ * Matrix.of p.2 - 1) < 1 / 4}
  have hU : MeasurableSet U :=
    (isOpen_lt (continuous_hs_real_place_taylor.comp ((((continuous_coeMatrix ε).comp (continuous_inv.comp continuous_fst)).matrix_mul
      (hof.comp continuous_snd)).sub continuous_const)) continuous_const).measurableSet
  let f : UJ ε → MatrixCoordinates n → ENNReal := fun g x => U.indicator (fun p => w p.1) (g, x)
  have hf : Measurable (Function.uncurry f) := (hwm.comp measurable_fst).indicator hU
  have h1 : ∫⁻ g, ∫⁻ x, f g x ∂lam ∂ν = (∫⁻ g, w g ∂ν) * lam O := by
    rw [← lintegral_mul_const _ hwm]
    refine lintegral_congr fun g => ?_
    have hdet : LinearMap.det (leftMulReal (coeMatrixAlt ε g⁻¹)) = 1 := det_leftMulReal_eq_one (g⁻¹).2
    have e : f g = (leftMulReal (coeMatrixAlt ε g⁻¹) ⁻¹' O).indicator fun _ => w g := by
      funext x
      rfl
    have hm : MeasurableSet (leftMulReal (coeMatrixAlt ε g⁻¹) ⁻¹' O) :=
      (hO_open.preimage (LinearMap.continuous_of_finiteDimensional _)).measurableSet
    rw [e, lintegral_indicator_const hm,
      Measure.addHaar_preimage_linearMap lam (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  let c : ENNReal := ENNReal.ofReal ((Real.sqrt n + 1) ^ (2 * n ^ 2 + 1))
  let b : MatrixCoordinates n → ENNReal := fun x => ENNReal.ofReal ((1 + ‖x‖) ^ (-((2 * n ^ 2 + 1 : ℕ) : ℝ)))
  have hfr : Module.finrank ℝ (MatrixCoordinates n) = 2 * n ^ 2 := by
    simp [MatrixCoordinates, Module.finrank_pi_fintype, Complex.finrank_real_complex]; ring
  have hb : ∫⁻ x, b x ∂lam < ⊤ :=
    finite_integral_one_add_norm (by rw [hfr]; exact_mod_cast Nat.lt_succ_self _)
  have h2 : ∀ x, ∫⁻ g, f g x ∂ν ≤ (c * ν W) * b x := by
    intro x
    have hm : MeasurableSet {g : UJ ε | hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4} :=
      measurable_prodMk_right hU
    calc ∫⁻ g, f g x ∂ν
        ≤ ∫⁻ g, {g : UJ ε | hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4}.indicator
            (fun _ => c * b x) g ∂ν := by
          refine lintegral_mono fun g => ?_
          by_cases hg : hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4
          · have hgU : (g, x) ∈ U := hg
            simp only [f]
            rw [Set.indicator_of_mem hgU, Set.indicator_of_mem (by exact hg)]
            simp only [w, c, b]
            rw [← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (wt_le g x hg)
          · have hgU : (g, x) ∉ U := hg
            simp only [f]
            rw [Set.indicator_of_notMem hgU]
            exact bot_le
      _ = c * b x * ν {g : UJ ε | hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4} :=
          lintegral_indicator_const hm _
      _ ≤ c * b x * ν W := mul_le_mul' le_rfl (slice_le S ν hν x)
      _ = (c * ν W) * b x := by ring
  have hcW : c * ν W ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW_fin.ne
  have h3 : (∫⁻ g, w g ∂ν) * lam O < ⊤ := by
    rw [← h1, lintegral_lintegral_swap hf.aemeasurable]
    refine (lintegral_mono h2).trans_lt ?_
    rw [lintegral_const_mul' _ _ hcW]
    exact ENNReal.mul_lt_top hcW.lt_top hb
  have h4 : ∫⁻ g, w g ∂ν < ⊤ := ENNReal.lt_top_of_mul_ne_top_left h3.ne hO_pos.ne'
  refine ⟨hwc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun g => inv_nonneg.2 (hwpos g).le)]
  exact h4
end

