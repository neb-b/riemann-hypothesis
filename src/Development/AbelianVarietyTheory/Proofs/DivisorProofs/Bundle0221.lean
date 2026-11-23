module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0078

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFlatOfCompFlatOfMapMaximalIdeal
section
open TensorProduct LinearMap IsLocalRing

namespace GlobalTheory

namespace LocalFlatMax

universe u

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]

theorem lTensor_injective_of_smul_le (I : Ideal A) [hI : I.IsMaximal]
    (h : Function.Injective (I.subtype.lTensor M))
    {F : Type u} [AddCommGroup F] [Module A F] (N : Submodule A F)
    (hN : I • (⊤ : Submodule A F) ≤ N) : Function.Injective (N.subtype.lTensor M) := by
  let p : (M →₀ A) →ₗ[A] M := Finsupp.linearCombination A id
  have hp : Function.Surjective p := Finsupp.linearCombination_id_surjective A M
  have h1 : Function.Injective ((ker p).subtype.lTensor (A ⧸ I)) :=
    lTensor_injective_of_exact_of_exact_of_rTensor_injective (exact_subtype_mkQ I)
      (Submodule.mkQ_surjective I) (exact_subtype_ker_map p) hp
      ((lTensor_inj_iff_rTensor_inj _ _).mp h)
      (Module.Flat.lTensor_preserves_injective_linearMap _ (ker p).injective_subtype)
  have htors : Module.IsTorsionBySet A (F ⧸ N) I := by
    intro x a
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    change N.mkQ (a.1 • x) = 0
    exact (Submodule.Quotient.mk_eq_zero N).mpr (hN (Submodule.smul_mem_smul a.2 trivial))
  letI : Module (A ⧸ I) (F ⧸ N) := htors.module
  haveI : IsScalarTower A (A ⧸ I) (F ⧸ N) := htors.isScalarTower
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  have h2 : Function.Injective ((ker p).subtype.lTensor (F ⧸ N)) := by
    have h3 : Function.Injective
        ((AlgebraTensorModule.lTensor (A ⧸ I) (A ⧸ I) (ker p).subtype).lTensor (F ⧸ N)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ h1
    have : AlgebraTensorModule.lTensor (A ⧸ I) (F ⧸ N) (ker p).subtype =
        (AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) (F ⧸ N) _).toLinearMap ∘ₗ
          (AlgebraTensorModule.lTensor (A ⧸ I) (A ⧸ I) (ker p).subtype).lTensor (F ⧸ N) ∘ₗ
          (AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) (F ⧸ N) _).symm.toLinearMap := by
      ext
      simp
    change Function.Injective (AlgebraTensorModule.lTensor (A ⧸ I) (F ⧸ N) (ker p).subtype)
    rw [this]
    simpa using h3
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective (exact_subtype_ker_map p) hp
    (exact_subtype_mkQ N) (Submodule.mkQ_surjective N) ((lTensor_inj_iff_rTensor_inj _ _).mp h2)
    (Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype)

theorem lTensor_injective_of_pow_smul_le (I : Ideal A) [hI : I.IsMaximal]
    (h : Function.Injective (I.subtype.lTensor M))
    {F : Type u} [AddCommGroup F] [Module A F] (n : ℕ) (N : Submodule A F)
    (hN : I ^ n • (⊤ : Submodule A F) ≤ N) : Function.Injective (N.subtype.lTensor M) := by
  induction n generalizing N with
  | zero => exact lTensor_injective_of_smul_le I h N (le_top.trans (by simpa using hN))
  | succ n ih =>
    let N' : Submodule A F := N ⊔ I ^ n • ⊤
    have h1 := ih N' le_sup_right
    have h2 := lTensor_injective_of_smul_le I h (N.comap N'.subtype) (by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_subtype_top,
        Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ']
      exact sup_le Submodule.smul_le_right hN)
    have : N.subtype = N'.subtype ∘ₗ (N.comap N'.subtype).subtype ∘ₗ
        (Submodule.comapSubtypeEquivOfLe (le_sup_left : N ≤ N')).symm.toLinearMap := by
      ext
      rfl
    rw [this, lTensor_comp, lTensor_comp]
    exact h1.comp (h2.comp (LinearEquiv.lTensor M _).injective)

theorem relationsLift_of_lTensor_injective (K : Ideal A)
    (h : ∀ L : Ideal A, K ≤ L → Function.Injective (L.subtype.lTensor M)) :
    LocalFlat.RelationsLift K M := by
  intro F _ _ f x hx
  have hy : ∃ y : M ⊗[A] K, TensorProduct.rid A M (K.subtype.lTensor M y) =
      TensorProduct.rid A M (f.lTensor M x) := by
    refine Submodule.smul_induction_on (p := fun d => ∃ y : M ⊗[A] K,
      TensorProduct.rid A M (K.subtype.lTensor M y) = d) hx ?_ ?_
    · intro r hr m _
      exact ⟨m ⊗ₜ ⟨r, hr⟩, by simp⟩
    · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a + b, by simp⟩
  obtain ⟨y, hy⟩ := hy
  replace hy := (TensorProduct.rid A M).injective hy
  let g : F × K →ₗ[A] A := f.coprod (-K.subtype)
  let z : M ⊗[A] (F × K) := (inl A F K).lTensor M x + (inr A F K).lTensor M y
  have hgz : g.lTensor M z = 0 := by
    simp only [z, g, map_add (f := _), ← lTensor_comp_apply, coprod_inl, coprod_inr, lTensor_neg,
      LinearMap.neg_apply, hy, add_neg_cancel]
  have hL : K ≤ range g := fun a ha => ⟨(0, ⟨-a, neg_mem ha⟩), by simp [g]⟩
  have hz : g.rangeRestrict.lTensor M z = 0 := by
    apply h _ hL
    rw [← lTensor_comp_apply, map_zero]
    exact hgz
  obtain ⟨w, hw⟩ := (lTensor_exact M (exact_subtype_ker_map g.rangeRestrict)
    g.surjective_rangeRestrict z).mp hz
  refine LocalFlat.range_lTensor_le (fst A F K ∘ₗ (ker g.rangeRestrict).subtype) _ ?_ ⟨w, ?_⟩
  · rintro ⟨⟨v, k⟩, hv⟩
    have : f v + -(k : A) = 0 := congrArg Subtype.val hv
    change f v ∈ K
    rw [add_neg_eq_zero.mp this]
    exact k.2
  · rw [lTensor_comp_apply, hw]
    simp only [z, map_add (f := _), ← lTensor_comp_apply, fst_comp_inl, fst_comp_inr, lTensor_id,
      lTensor_zero, LinearMap.zero_apply, add_zero, id_apply]

theorem flat_of_lTensor_injective [IsNoetherianRing A] (B : Type*) [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [Module B M] [IsScalarTower A B M] [Module.Finite B M] (I : Ideal A)
    [I.IsMaximal] (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥)
    (h : Function.Injective (I.subtype.lTensor M)) : Module.Flat A M :=
  LocalFlat.flat_of_relationsLift B hI fun n =>
    relationsLift_of_lTensor_injective _ fun L hL =>
      lTensor_injective_of_pow_smul_le I h n L (by simpa using hL)

theorem lTensor_map_injective {O : Type*} [CommRing O] [Algebra O A] [Module O M]
    [IsScalarTower O A M] [Module.Flat O M] (J : Ideal O) :
    Function.Injective ((J.map (algebraMap O A)).subtype.lTensor M) := by
  let j : J →ₗ[O] J.map (algebraMap O A) :=
    { toFun := fun a => ⟨algebraMap O A a, Ideal.mem_map_of_mem _ a.2⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun a b => Subtype.ext (by simp [Algebra.smul_def]) }
  let t : M ⊗[O] J →ₗ[O] M ⊗[A] J.map (algebraMap O A) :=
    mapOfCompatibleSMul A O O M _ ∘ₗ j.lTensor M
  have ht : ∀ x, ∃ y, t y = x := by
    intro x
    induction x with
    | add a b ha hb =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      exact ⟨a + b, map_add _ _ _⟩
    | tmul m r =>
      obtain ⟨r, hr⟩ := r
      induction hr using Submodule.span_induction generalizing m with
      | mem r hr =>
        obtain ⟨a, ha, rfl⟩ := hr
        exact ⟨m ⊗ₜ ⟨a, ha⟩, rfl⟩
      | zero => exact ⟨0, (map_zero _).trans (tmul_zero _ _).symm⟩
      | add a b ha hb iha ihb =>
        obtain ⟨a', ha'⟩ := iha m
        obtain ⟨b', hb'⟩ := ihb m
        exact ⟨a' + b', by rw [map_add (f := _), ha', hb', ← tmul_add]; rfl⟩
      | smul c a ha iha =>
        obtain ⟨a', ha'⟩ := iha (c • m)
        exact ⟨a', by rw [ha', smul_tmul]; rfl⟩
  have hc : ∀ y, TensorProduct.rid A M ((J.map (algebraMap O A)).subtype.lTensor M (t y)) =
      TensorProduct.rid O M (J.subtype.lTensor M y) := by
    intro y
    induction y with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul m a => simp [t, j]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := ht x
  have h0 := hc y
  rw [hx, map_zero, eq_comm, LinearEquiv.map_eq_zero_iff] at h0
  have h1 : y = 0 :=
    Module.Flat.lTensor_preserves_injective_linearMap _ J.injective_subtype
      (h0.trans (map_zero _).symm)
  rw [h1, map_zero]

end LocalFlatMax

theorem ringHom_flat_of_comp_flat_of_map_maximalIdeal :
    ∀ (O R' E : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R']
      [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [IsNoetherianRing E]
      (φ' : O →+* R') (b : R' →+* E), φ'.Flat → (maximalIdeal O).map φ' = maximalIdeal R' →
      IsLocalHom b → (b.comp φ').Flat → b.Flat := by
  intro O R' E _ _ _ _ _ _ _ _ _ φ' b _ hm hb hc
  algebraize [φ', b, b.comp φ']
  refine LocalFlatMax.flat_of_lTensor_injective E (maximalIdeal R') ?_ ?_
  · have h : (maximalIdeal R').map b ≤ maximalIdeal E := ((local_hom_tfae b).out 1 3).mp hb
    exact h.trans (maximalIdeal_le_jacobson _)
  · rw [← hm]
    exact LocalFlatMax.lTensor_map_injective (maximalIdeal O)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumsTwoThreeClosedFormRealNonInteger
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open Filter Topology

namespace GlobalTheory.WpFam.RowReal

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma norm_add_intCast_eq_abs_of_im_eq_zero {w : ℂ} (hw : w.im = 0) (m : ℤ) :
    ‖w + m‖ = |(m : ℝ) + w.re| := by
  have h : w + m = ((w.re + m : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hw])
  rw [h, Complex.norm_real, Real.norm_eq_abs, add_comm]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma exists_pos_le_norm_add_intCast_of_im_eq_zero {w : ℂ} (hw : w.im = 0) (hn : ∀ n : ℤ, w ≠ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℤ, δ ≤ ‖w + m‖ := by
  have hwx : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hw])
  have hf0 : 0 < Int.fract w.re := by
    rcases (Int.fract_nonneg w.re).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hn ⌊w.re⌋
      have h2 := Int.floor_add_fract w.re
      rw [← h, add_zero] at h2
      exact Complex.ext (by simp [h2]) (by simp [hw])
  have hf1 := Int.fract_lt_one w.re
  refine ⟨min (Int.fract w.re) (1 - Int.fract w.re), lt_min hf0 (by linarith), fun m => ?_⟩
  rw [norm_add_intCast_eq_abs_of_im_eq_zero hw m]
  have hx := Int.floor_add_fract w.re
  rcases le_or_gt 0 (⌊w.re⌋ + m) with h | h
  · have h' : (0 : ℝ) ≤ ((⌊w.re⌋ + m : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_left _ _).trans (by linarith)
  · have h' : ((⌊w.re⌋ + m : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : ⌊w.re⌋ + m ≤ -1)
    push_cast at h'
    rw [abs_of_neg (by linarith)]
    exact (min_le_right _ _).trans (by linarith)

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma tsum_one_div_add_int_pow_of_real_of_continuousAt {w : ℂ} (hw : w.im = 0)
    (hn : ∀ n : ℤ, w ≠ n) {k : ℕ} (hk : 2 ≤ k) {G : ℂ → ℂ} (hG : ContinuousAt G w)
    (hEq : ∀ z : ℂ, 0 < z.im → ∑' m : ℤ, 1 / (z + m) ^ k = G z) :
    ∑' m : ℤ, 1 / (w + m) ^ k = G w := by
  obtain ⟨δ, hδ, hδm⟩ := exists_pos_le_norm_add_intCast_of_im_eq_zero hw hn
  have hsum : Summable fun m : ℤ => 2 ^ k * (1 / ‖w + m‖ ^ k) := by
    refine Summable.mul_left _ ?_
    have h := (Real.summable_one_div_int_add_rpow w.re (k : ℝ)).2
      (by exact_mod_cast (by omega : 1 < k))
    refine h.congr fun m => ?_
    rw [Real.rpow_natCast, norm_add_intCast_eq_abs_of_im_eq_zero hw m]
  have hlow : ∀ (m : ℤ) (x : ℂ), x ∈ Metric.closedBall w (δ / 2) → ‖w + m‖ / 2 ≤ ‖x + m‖ := by
    intro m x hx
    have hxw : ‖x - w‖ ≤ δ / 2 := by rw [← dist_eq_norm]; exact hx
    have h1 := hδm m
    have h2 := norm_sub_norm_le (w + m) (x + m)
    rw [show (w + (m : ℂ)) - (x + m) = -(x - w) by ring, norm_neg] at h2
    linarith
  have hcont : ContinuousOn (fun x : ℂ => ∑' m : ℤ, 1 / (x + (m : ℂ)) ^ k)
      (Metric.closedBall w (δ / 2)) := by
    refine continuousOn_tsum (fun m => ?_) hsum (fun m x hx => ?_)
    · refine ContinuousOn.div₀ continuousOn_const (by fun_prop) (fun x hx => pow_ne_zero _ ?_)
      have h1 := hlow m x hx
      have h2 := hδm m
      exact norm_ne_zero_iff.mp (by linarith)
    · have hpos : 0 < ‖w + m‖ / 2 := by linarith [hδm m]
      rw [norm_div, norm_one, norm_pow]
      calc 1 / ‖x + m‖ ^ k ≤ 1 / (‖w + m‖ / 2) ^ k :=
            one_div_le_one_div_of_le (pow_pos hpos k) (pow_le_pow_left₀ hpos.le (hlow m x hx) k)
        _ = 2 ^ k * (1 / ‖w + m‖ ^ k) := by rw [div_pow, one_div_div, mul_one_div]
  have hcw : ContinuousAt (fun x : ℂ => ∑' m : ℤ, 1 / (x + (m : ℂ)) ^ k) w :=
    hcont.continuousAt (Metric.closedBall_mem_nhds w (by linarith))
  have hpath : Tendsto (fun ε : ℝ => w + ε * Complex.I) (𝓝[>] 0) (𝓝 w) := by
    have hc : Continuous (fun ε : ℝ => w + ε * Complex.I) := by fun_prop
    have h := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_nhds_unique ((hcw.tendsto.comp hpath).congr' ?_) (hG.tendsto.comp hpath)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hEq _ (by simpa [hw] using hε)

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma tsum_one_div_add_int_sq_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    ∑' m : ℤ, 1 / (z + m) ^ 2 = (2 * (Real.pi : ℂ) * Complex.I) ^ 2 *
      (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)
        / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)) ^ 2) := by
  have h := EisensteinSeries.qExpansion_identity (k := 1) le_rfl ⟨z, hz⟩
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩
  simp only [UpperHalfPlane.coe_mk] at h hq
  simp only [Nat.reduceAdd, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  rw [h, tsum_coe_mul_geometric_of_norm_lt_one hq]
  ring

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma tsum_sq_mul_geometric_of_norm_lt_one {r : ℂ} (hr : ‖r‖ < 1) :
    ∑' n : ℕ, (n : ℂ) ^ 2 * r ^ n = r * (1 + r) / (1 - r) ^ 3 := by
  have hne : 1 - r ≠ 0 := by
    intro h
    have : r = 1 := by linear_combination -h
    rw [this, norm_one] at hr
    exact lt_irrefl _ hr
  have hS : Summable fun n : ℕ => (n : ℂ) ^ 2 * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have hS1 : Summable fun n : ℕ => (n : ℂ) * r ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hG : Summable fun n : ℕ => r ^ n := summable_geometric_of_norm_lt_one hr
  have h1 := tsum_coe_mul_geometric_of_norm_lt_one hr
  have hg := tsum_geometric_of_norm_lt_one hr
  have hsplit := hS.tsum_eq_zero_add
  have hshift : (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ 2 * r ^ (n + 1))
      = fun n : ℕ => r * ((n : ℂ) ^ 2 * r ^ n) + 2 * r * ((n : ℂ) * r ^ n) + r * r ^ n := by
    funext n
    push_cast
    ring
  rw [hshift, ((hS.mul_left r).add (hS1.mul_left (2 * r))).tsum_add (hG.mul_left r),
    (hS.mul_left r).tsum_add (hS1.mul_left (2 * r)), tsum_mul_left, tsum_mul_left, tsum_mul_left,
    h1, hg] at hsplit
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, pow_zero,
    mul_one, zero_add] at hsplit
  set S := ∑' n : ℕ, (n : ℂ) ^ 2 * r ^ n
  have e1 : r / (1 - r) ^ 2 * (1 - r) ^ 2 = r := div_mul_cancel₀ _ (pow_ne_zero 2 hne)
  have e2 : (1 - r)⁻¹ * (1 - r) = 1 := inv_mul_cancel₀ hne
  rw [eq_div_iff (pow_ne_zero 3 hne)]
  linear_combination (1 - r) ^ 2 * hsplit + 2 * r * e1 + r * (1 - r) * e2

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma tsum_one_div_add_int_pow_three_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    ∑' m : ℤ, 1 / (z + m) ^ 3 = -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 *
      (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)
        * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z))
        / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)) ^ 3) := by
  have h := EisensteinSeries.qExpansion_identity (k := 2) (by norm_num) ⟨z, hz⟩
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩
  simp only [UpperHalfPlane.coe_mk] at h hq
  simp only [Nat.reduceAdd, Nat.factorial_two, Nat.cast_ofNat] at h
  rw [h, tsum_sq_mul_geometric_of_norm_lt_one hq]
  ring


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
theorem _root_.GlobalTheory.WpFam.RowReal.row_real : ∀ w : ℂ, w.im = 0 → (∀ n : ℤ, w ≠ n) → (∑' m : ℤ, 1 / (w + m) ^ 2 = (2 * (Real.pi : ℂ) * Complex.I) ^ 2 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 2)) ∧ ∑' m : ℤ, 1 / (w + m) ^ 3 = -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 3) := by
  intro w hw hn
  have hne : 1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) ≠ 0 := by
    intro h
    have h1 : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) = 1 := by linear_combination -h
    obtain ⟨n, hn'⟩ := Complex.exp_eq_one_iff.mp h1
    apply hn n
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ h2
    linear_combination hn'
  have hE : ContinuousAt (fun x : ℂ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)) w := by
    fun_prop
  have hD2 : ContinuousAt
      (fun x : ℂ => (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)) ^ 2) w := by
    fun_prop
  have hD3 : ContinuousAt
      (fun x : ℂ => (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)) ^ 3) w := by
    fun_prop
  have hN3 : ContinuousAt (fun x : ℂ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)
      * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x))) w := by
    fun_prop
  constructor
  · exact tsum_one_div_add_int_pow_of_real_of_continuousAt (k := 2) hw hn le_rfl
      (continuousAt_const.mul (hE.div hD2 (pow_ne_zero 2 hne)))
      tsum_one_div_add_int_sq_of_im_pos
  · exact tsum_one_div_add_int_pow_of_real_of_continuousAt (k := 3) hw hn (by norm_num)
      (continuousAt_const.mul (hN3.div hD3 (pow_ne_zero 3 hne)))
      tsum_one_div_add_int_pow_three_of_im_pos

end GlobalTheory.WpFam.RowReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzProductDecomposition
section
open Topology Filter Set
open scoped Classical

noncomputable section

namespace GlobalTheory.SBProd

theorem exists_compact_clopen_nhd {H : Type} [TopologicalSpace H] [LocallyCompactSpace H] [T2Space H]
    [TotallyDisconnectedSpace H] {x : H} {U : Set H} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set H, IsClopen V ∧ IsCompact V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨s, comp, xs, sU⟩ := exists_compact_subset hU hx
  obtain ⟨V, hV, hxV, hVs⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 (isOpen_interior.mem_nhds xs)
  exact ⟨V, hV, comp.of_isClosed_subset hV.1 (hVs.trans interior_subset), hxV,
    (hVs.trans interior_subset).trans sU⟩

theorem isLocallyConstant_filter {H ι : Type} [TopologicalSpace H] (F : Finset ι) (U : ι → Set H)
    (hU : ∀ i, IsClopen (U i)) : IsLocallyConstant fun a => F.filter (fun i => a ∈ U i) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ i ∈ F, ∀ᶠ y in 𝓝 x, (y ∈ U i ↔ x ∈ U i) := by
    intro i _
    by_cases h : x ∈ U i
    · filter_upwards [(hU i).isOpen.mem_nhds h] with y hy
      exact iff_of_true hy h
    · filter_upwards [(hU i).compl.isOpen.mem_nhds h] with y hy
      exact iff_of_false hy h
  filter_upwards [(Filter.eventually_all_finset F).2 this] with y hy
  exact Finset.filter_congr fun i hi => hy i hi

theorem exists_sum_box (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] (κ κ' : Type) [Fintype κ] [Fintype κ'] (g : (κ ⊕ κ' → X) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (κ ⊕ κ' → X)) :
    ∃ (ι : Type) (_ : Fintype ι) (g₁ : ι → (κ → X) → ℂ) (g₂ : ι → (κ' → X) → ℂ),
      (∀ i, g₁ i ∈ GlobalTheory.WeilM.SB (κ → X)) ∧ (∀ i, g₂ i ∈ GlobalTheory.WeilM.SB (κ' → X)) ∧
      g = ∑ i, fun z => g₁ i (z ∘ Sum.inl) * g₂ i (z ∘ Sum.inr) := by
  obtain ⟨hlc, hcs⟩ := hg
  let e : (κ ⊕ κ' → X) ≃ₜ (κ → X) × (κ' → X) := Homeomorph.sumArrowHomeomorphProdArrow
  let h : (κ → X) × (κ' → X) → ℂ := g ∘ e.symm
  have hgh : ∀ z, g z = h (z ∘ Sum.inl, z ∘ Sum.inr) := fun z => by
    have : (z ∘ Sum.inl, z ∘ Sum.inr) = e z := rfl
    simp [h, this]
  have hlc' : IsLocallyConstant h := hlc.comp_continuous e.symm.continuous
  have hcs' : HasCompactSupport h := hcs.comp_homeomorph e.symm
  have key : ∀ p : (κ → X) × (κ' → X), ∃ U : Set (κ → X), ∃ V : Set (κ' → X), IsClopen U ∧ IsCompact U ∧
      IsClopen V ∧ IsCompact V ∧ p.1 ∈ U ∧ p.2 ∈ V ∧ ∀ a ∈ U, ∀ b ∈ V, h (a, b) = h p := by
    rintro ⟨a₀, b₀⟩
    obtain ⟨u, v, hu, hv, hpu, hpv, huv⟩ :=
      isOpen_prod_iff.1 (hlc'.isOpen_fiber (h (a₀, b₀))) a₀ b₀ rfl
    obtain ⟨U, hU, hUc, haU, hUu⟩ := exists_compact_clopen_nhd hu hpu
    obtain ⟨V, hV, hVc, hbV, hVv⟩ := exists_compact_clopen_nhd hv hpv
    exact ⟨U, V, hU, hUc, hV, hVc, haU, hbV, fun a ha b hb => huv (mk_mem_prod (hUu ha) (hVv hb))⟩
  choose U V hU hUc hV hVc hpU hpV hconst using key
  obtain ⟨F, hF⟩ := hcs'.isCompact.elim_finite_subcover (fun p => U p ×ˢ V p)
    (fun p => (hU p).isOpen.prod (hV p).isOpen) (fun q _ => mem_iUnion.2 ⟨q, hpU q, hpV q⟩)
  let σ : (κ → X) → Finset F := fun a => Finset.univ.filter (fun i : F => a ∈ U i)
  let τ : (κ' → X) → Finset F := fun b => Finset.univ.filter (fun i : F => b ∈ V i)
  have hσ : IsLocallyConstant σ := isLocallyConstant_filter _ (fun i : F => U i) fun i => hU i
  have hτ : IsLocallyConstant τ := isLocallyConstant_filter _ (fun i : F => V i) fun i => hV i
  let c : Finset F → Finset F → ℂ := fun S T =>
    if hx : (S ∩ T).Nonempty then h (hx.choose : (κ → X) × (κ' → X)) else 0
  refine ⟨Finset F × Finset F, inferInstance,
    fun x a => if σ a = x.1 ∧ x.1.Nonempty then c x.1 x.2 else 0,
    fun x b => if τ b = x.2 ∧ x.2.Nonempty then 1 else 0, ?_, ?_, ?_⟩
  · intro x
    refine ⟨hσ.comp fun s => if s = x.1 ∧ x.1.Nonempty then c x.1 x.2 else 0, ?_⟩
    by_cases hx : x.1.Nonempty
    · obtain ⟨i, hi⟩ := hx
      refine HasCompactSupport.intro (hUc i) fun a ha => if_neg fun hs => ha ?_
      rw [← hs.1] at hi
      simpa [σ] using hi
    · exact HasCompactSupport.intro isCompact_empty fun a _ => if_neg fun hs => hx hs.2
  · intro x
    refine ⟨hτ.comp fun s => if s = x.2 ∧ x.2.Nonempty then (1 : ℂ) else 0, ?_⟩
    by_cases hx : x.2.Nonempty
    · obtain ⟨i, hi⟩ := hx
      refine HasCompactSupport.intro (hVc i) fun b hb => if_neg fun hs => hb ?_
      rw [← hs.1] at hi
      simpa [τ] using hi
    · exact HasCompactSupport.intro isCompact_empty fun b _ => if_neg fun hs => hx hs.2
  · funext z
    rw [Finset.sum_apply, hgh z]
    generalize z ∘ Sum.inl = a
    generalize z ∘ Sum.inr = b
    rw [Fintype.sum_eq_single (σ a, τ b)]
    · by_cases hst : (σ a ∩ τ b).Nonempty
      · have hs : (σ a).Nonempty := hst.mono Finset.inter_subset_left
        have ht : (τ b).Nonempty := hst.mono Finset.inter_subset_right
        have hmem := Finset.mem_inter.1 hst.choose_spec
        simp only [σ, τ, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        have hc : c (σ a) (τ b) = h (hst.choose : (κ → X) × (κ' → X)) := dif_pos hst
        simp only [true_and, hs, ht, and_self, if_true, hc, mul_one]
        exact hconst _ a hmem.1 b hmem.2
      · have hc : c (σ a) (τ b) = 0 := dif_neg hst
        simp only [hc, ite_self, zero_mul]
        by_contra hne
        obtain ⟨i, hi, hab⟩ := mem_iUnion₂.1 (hF (subset_tsupport h hne))
        exact hst ⟨⟨i, hi⟩, Finset.mem_inter.2 ⟨by simpa [σ] using hab.1, by simpa [τ] using hab.2⟩⟩
    · intro x hx
      by_cases h1 : σ a = x.1
      · have h2 : τ b ≠ x.2 := fun h2 => hx (Prod.ext h1.symm h2.symm)
        simp [h2]
      · simp [h1]

end GlobalTheory.SBProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlongCurveProductsStableStatement
section
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_along_curve_products_stable_alt : ∀ (G : Type) [Group G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : G →* (K →L[ℂ] K)) (P : Type) (A : Set P) (e : P → ℝ → G) (v : K), (∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v) → (∀ p ∈ A, ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (deriv (fun r : ℝ => ρ (e p r) v) 0)) ∧ (∀ (m : ℕ) (qs : Fin m → P) (r : Fin m → ℝ), (∀ i, qs i ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (ρ (List.ofFn fun i => e (qs i) (r i)).prod v)) ∧ ∀ l : List P, (∀ p ∈ l, p ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) (ρ (List.ofFn fun i => e (ps i) (t i)).prod v) := by
  first | exact @GlobalTheory.smooth_along_curve_products_stable | exact GlobalTheory.smooth_along_curve_products_stable | (intros; apply GlobalTheory.smooth_along_curve_products_stable <;> assumption)
end

