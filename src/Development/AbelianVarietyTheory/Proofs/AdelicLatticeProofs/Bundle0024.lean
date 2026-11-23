module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSmoothHomogeneousHasSumUnitSmul
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory
namespace UnitPartition
open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace

theorem hasSum_quot {G : Type} [Group G] (T : Subgroup G) [Finite T] (f : G ⧸ T → ℝ) (s : ℝ)
    (hf : HasSum f s) : HasSum (fun g : G => f (g : G ⧸ T) / Nat.card T) s := by
  classical
  have : Fintype T := Fintype.ofFinite T
  have hT : (Nat.card T : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  let e : G ≃ (G ⧸ T) × T := Subgroup.groupEquivQuotientProdSubgroup
  have he : ∀ g : G, (e g).1 = (g : G ⧸ T) := fun g => rfl
  have hp : ∀ p : (G ⧸ T) × T, ((e.symm p : G) : G ⧸ T) = p.1 := fun p => by
    rw [← he, e.apply_symm_apply]
  have hfun : (fun g : G => f (g : G ⧸ T) / Nat.card T) ∘ e.symm =
      fun p : (G ⧸ T) × T => f p.1 * (Nat.card T : ℝ)⁻¹ := by
    funext p
    simp only [Function.comp_apply, hp p, div_eq_mul_inv]
  have hg : HasSum (fun _ : T => (Nat.card T : ℝ)⁻¹) 1 := by
    have h0 := hasSum_fintype (fun _ : T => (Nat.card T : ℝ)⁻¹)
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
      mul_inv_cancel₀ hT] at h0
  have hprod : HasSum (fun p : (G ⧸ T) × T => f p.1 * (Nat.card T : ℝ)⁻¹) s := by
    have hs1 : Summable fun q : G ⧸ T => ‖f q‖ := by
      simpa only [Real.norm_eq_abs] using hf.summable.abs
    have hs2 : Summable fun _ : T => ‖(Nat.card T : ℝ)⁻¹‖ := Summable.of_finite
    have hs : Summable fun p : (G ⧸ T) × T => f p.1 * (fun _ : T => (Nat.card T : ℝ)⁻¹) p.2 :=
      summable_mul_of_summable_norm (R := ℝ) (f := f) (g := fun _ : T => (Nat.card T : ℝ)⁻¹) hs1 hs2
    have h0 := HasSum.mul (f := f) (g := fun _ : T => (Nat.card T : ℝ)⁻¹) hf hg hs
    rwa [mul_one] at h0
  rw [← e.symm.hasSum_iff, hfun]
  exact hprod

variable {K : Type} [Field K] [NumberField K]

theorem contDiffAt_normAtPlace (w : InfinitePlace K) (x : mixedSpace K)
    (hx : normAtPlace w x ≠ 0) : ContDiffAt ℝ ∞ (fun y : mixedSpace K => normAtPlace w y) x := by
  rcases w.isReal_or_isComplex with hw | hw
  · have e : (fun y : mixedSpace K => normAtPlace w y) = fun y => ‖y.1 ⟨w, hw⟩‖ :=
      funext fun y => normAtPlace_apply_of_isReal hw y
    rw [normAtPlace_apply_of_isReal hw] at hx
    rw [e]
    exact ContDiffAt.norm ℝ (by fun_prop) (norm_ne_zero_iff.1 hx)
  · have e : (fun y : mixedSpace K => normAtPlace w y) = fun y => ‖y.2 ⟨w, hw⟩‖ :=
      funext fun y => normAtPlace_apply_of_isComplex hw y
    rw [normAtPlace_apply_of_isComplex hw] at hx
    rw [e]
    exact ContDiffAt.norm ℝ (by fun_prop) (norm_ne_zero_iff.1 hx)

theorem contDiffAt_logMap (x : mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) :
    ContDiffAt ℝ ∞ (logMap (K := K)) x := by
  have hN : ∀ w, normAtPlace w x ≠ 0 := mixedEmbedding.norm_ne_zero_iff.1 hx
  have hnorm : ContDiffAt ℝ ∞ (fun y : mixedSpace K => mixedEmbedding.norm y) x := by
    have e : (fun y : mixedSpace K => mixedEmbedding.norm y) =
        fun y => ∏ w, normAtPlace w y ^ mult w := funext fun y => mixedEmbedding.norm_apply y
    rw [e]
    exact contDiffAt_prod fun w _ => (contDiffAt_normAtPlace w x (hN w)).pow _
  refine contDiffAt_pi.2 fun w => ?_
  simp only [logMap_apply]
  exact contDiffAt_const.mul (((contDiffAt_normAtPlace w.1 x (hN w.1)).log (hN w.1)).sub
    ((hnorm.log hx).mul contDiffAt_const))

private lemma le_of_mul_le_of_one_le' {m t B : ℝ} (hm : 1 ≤ m) (hB : 0 ≤ B) (h : m * t ≤ B) :
    t ≤ B := by
  rcases le_or_gt t 0 with ht | ht
  · exact ht.trans hB
  · nlinarith

theorem log_le (x : mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) (w : InfinitePlace K) :
    Real.log (normAtPlace w x) ≤ Fintype.card (InfinitePlace K) * ‖logMap x‖ +
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹ := by
  classical
  have hN : ∀ w, normAtPlace w x ≠ 0 := mixedEmbedding.norm_ne_zero_iff.1 hx
  have hd0 : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
  have hL : Real.log (mixedEmbedding.norm x) =
      ∑ v, (mult v : ℝ) * Real.log (normAtPlace v x) := by
    rw [mixedEmbedding.norm_apply, Real.log_prod (fun v _ => pow_ne_zero _ (hN v))]
    simp only [Real.log_pow]
  have hm : ∑ v : InfinitePlace K, (mult v : ℝ) = Module.finrank ℚ K := by
    rw [← sum_mult_eq, Nat.cast_sum]
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace K) := by
    exact_mod_cast Fintype.card_pos
  have hpos : 0 ≤ ‖logMap x‖ := norm_nonneg _
  have hB : 0 ≤ Fintype.card (InfinitePlace K) * ‖logMap x‖ := by positivity
  have hle : ‖logMap x‖ ≤ Fintype.card (InfinitePlace K) * ‖logMap x‖ :=
    le_mul_of_one_le_left hpos hcard
  rw [← sub_le_iff_le_add]
  by_cases hw : w = w₀
  · subst hw
    set L := Real.log (mixedEmbedding.norm x)
    set d : ℝ := (Module.finrank ℚ K : ℝ)
    have h1 := Fintype.sum_eq_add_sum_subtype_ne
      (fun v => (mult v : ℝ) * Real.log (normAtPlace v x)) w₀
    have h2 := Fintype.sum_eq_add_sum_subtype_ne (fun v : InfinitePlace K => (mult v : ℝ)) w₀
    rw [← hL] at h1
    rw [hm] at h2
    have hS : ∑ v : {v : InfinitePlace K // v ≠ w₀}, logMap x v =
        ∑ v : {v : InfinitePlace K // v ≠ w₀}, (mult v.1 : ℝ) * Real.log (normAtPlace v.1 x) -
          (∑ v : {v : InfinitePlace K // v ≠ w₀}, (mult v.1 : ℝ)) * (L * d⁻¹) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [logMap_apply]
      ring
    have hdd : d * d⁻¹ = 1 := mul_inv_cancel₀ hd0.ne'
    have hkey : (mult (w₀ : InfinitePlace K) : ℝ) * (Real.log (normAtPlace w₀ x) - L * d⁻¹) =
        -∑ v : {v : InfinitePlace K // v ≠ w₀}, logMap x v := by
      rw [hS]
      linear_combination (-1 : ℝ) * h1 + (L * d⁻¹) * h2 - L * hdd
    have hSle : -∑ v : {v : InfinitePlace K // v ≠ w₀}, logMap x v ≤
        Fintype.card (InfinitePlace K) * ‖logMap x‖ := by
      refine (neg_le_abs _).trans ((Finset.abs_sum_le_sum_abs _ _).trans ?_)
      refine (Finset.sum_le_sum fun v _ => (show |logMap x v| ≤ ‖logMap x‖ from
        (Real.norm_eq_abs (logMap x v)).symm.trans_le (norm_le_pi_norm (logMap x) v))).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Fintype.card_subtype_le _) hpos
    exact le_of_mul_le_of_one_le' one_le_mult hB (hkey.trans_le hSle)
  · have hv : logMap x ⟨w, hw⟩ = (mult w : ℝ) * (Real.log (normAtPlace w x) -
        Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹) := logMap_apply x ⟨w, hw⟩
    refine le_of_mul_le_of_one_le' (one_le_mult (w := w)) hB ?_
    rw [← hv]
    exact (le_abs_self _).trans (((Real.norm_eq_abs _).symm.trans_le
      (norm_le_pi_norm (logMap x) ⟨w, hw⟩)).trans hle)

end UnitPartition


open UnitPartition NumberField.Units NumberField.Units.dirichletUnitTheorem in
theorem exists_smooth_homogeneous_hasSum_unit_smul : ∀ (K : Type) [Field K] [NumberField K], ∃ h : mixedSpace K → ℝ, ContDiffOn ℝ ∞ h {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ (t : ℝ) x, 0 < t → h (t • x) = h x) ∧ (∀ x, mixedEmbedding.norm x ≠ 0 → HasSum (fun u : (𝓞 K)ˣ => h (u • x)) 1) ∧ (∀ a b : ℝ, 0 < a → ∃ C : Set (mixedSpace K), IsCompact C ∧ (∀ x ∈ C, mixedEmbedding.norm x ≠ 0) ∧ ∀ x, h x ≠ 0 → a ≤ mixedEmbedding.norm x → mixedEmbedding.norm x ≤ b → x ∈ C) := by
  intro K _ _
  obtain ⟨η, hη, hηc, hηs⟩ := exists_smooth_compactSupport_hasSum_lattice_translates
    ({w : InfinitePlace K // w ≠ w₀} → ℝ) (unitLattice K)
  refine ⟨fun x => if mixedEmbedding.norm x = 0 then 0 else
    η (logMap x) / (Nat.card (torsion K) : ℝ), ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : mixedEmbedding.norm x ≠ 0 := hx
    have hopen : IsOpen {y : mixedSpace K | mixedEmbedding.norm y ≠ 0} :=
      isOpen_ne_fun (mixedEmbedding.continuous_norm K) continuous_const
    refine ContDiffAt.contDiffWithinAt ?_
    have hev : (fun y : mixedSpace K => if mixedEmbedding.norm y = 0 then 0 else
        η (logMap y) / (Nat.card (torsion K) : ℝ)) =ᶠ[nhds x]
        fun y => η (logMap y) / (Nat.card (torsion K) : ℝ) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      rw [if_neg hy]
    exact ((hη.contDiffAt.comp x (contDiffAt_logMap x hx')).div_const _).congr_of_eventuallyEq hev
  · intro t x ht
    have ht0 : t ≠ 0 := ht.ne'
    simp only [mixedEmbedding.norm_smul]
    by_cases hx : mixedEmbedding.norm x = 0
    · simp [hx]
    · have hne : |t| ^ Module.finrank ℚ K * mixedEmbedding.norm x ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (abs_ne_zero.2 ht0)) hx
      rw [if_neg hne, if_neg hx, logMap_real_smul hx ht0]
  · intro x hx
    let e : ((𝓞 K)ˣ ⧸ torsion K) ≃ unitLattice K :=
      Additive.ofMul.trans (logEmbeddingEquiv K).toEquiv
    have hq : HasSum ((fun l : unitLattice K => η (logMap x + l)) ∘ e) 1 :=
      e.hasSum_iff.2 (hηs (logMap x))
    have hu := hasSum_quot (torsion K) _ 1 hq
    convert hu using 2 with u
    have hux : mixedEmbedding.norm (u • x) ≠ 0 := by rwa [norm_unit_smul]
    dsimp only
    rw [if_neg hux, logMap_unit_smul u hx, add_comm]
    simp only [Function.comp_apply, e, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
      logEmbeddingEquiv_apply]
  · intro a b ha
    obtain ⟨R, hR⟩ := hηc.isCompact.isBounded.exists_norm_le
    refine ⟨Metric.closedBall 0 (Real.exp (Fintype.card (InfinitePlace K) * R +
        Real.log b * (Module.finrank ℚ K : ℝ)⁻¹)) ∩ {x | a ≤ mixedEmbedding.norm x},
      (isCompact_closedBall _ _).inter_right
        (isClosed_le continuous_const (mixedEmbedding.continuous_norm K)),
      fun x hx => (ha.trans_le hx.2).ne', fun x hx hax hxb => ⟨?_, hax⟩⟩
    have hx0 : mixedEmbedding.norm x ≠ 0 := (ha.trans_le hax).ne'
    dsimp only at hx
    rw [if_neg hx0] at hx
    have hηx : η (logMap x) ≠ 0 := fun h0 => hx (by rw [h0, zero_div])
    have hlog : ‖logMap x‖ ≤ R := hR _ (subset_tsupport _ hηx)
    rw [mem_closedBall_zero_iff, norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le _ _ fun w _ => ?_
    have hNw : 0 < normAtPlace w x :=
      lt_of_le_of_ne (normAtPlace_nonneg w x) (mixedEmbedding.norm_ne_zero_iff.1 hx0 w).symm
    rw [← Real.exp_log hNw]
    refine Real.exp_le_exp.2 ((log_le x hx0 w).trans (add_le_add
      (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)) ?_))
    exact mul_le_mul_of_nonneg_right (Real.log_le_log (ha.trans_le hax) hxb) (by positivity)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTwoPlacesOverOfIsSquareLocal
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem val_integer_le_one {E Γ : Type} [Field E] [LinearOrderedCommGroupWithZero Γ]
    (u : Valuation E Γ) (x : 𝓞 E) : u (algebraMap (𝓞 E) E x) ≤ 1 := by
  have h : IsIntegral u.integer (algebraMap (𝓞 E) E x) :=
    (RingOfIntegers.isIntegral_coe x).tower_top
  exact (Valuation.integer.integers u).mem_of_integral h

theorem exists_centre_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (u : Valuation E ℤᵐ⁰)
    (hu : ∀ a : F, u (algebraMap F E a) = v.valuation F a) :
    ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧
      ∀ x : 𝓞 E, x ∈ w.asIdeal ↔ u (algebraMap (𝓞 E) E x) < 1 := by
  let I : Ideal (𝓞 E) :=
    { carrier := {x | u (algebraMap (𝓞 E) E x) < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add (f := _)] at *
        exact u.map_add_lt ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_integer_le_one u c)) hx }
  have hI : ∀ x : 𝓞 E, x ∈ I ↔ u (algebraMap (𝓞 E) E x) < 1 := fun x => Iff.rfl
  have hp : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hI]; simp
    · intro a b hab
      rw [hI, map_mul, map_mul] at hab
      rw [hI, hI]
      by_contra hc
      push Not at hc
      exact absurd hab (not_lt.2 (one_le_mul hc.1 hc.2))
  have hc : ∀ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a ∈ I ↔ a ∈ v.asIdeal := by
    intro a
    rw [hI, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E, hu]
    exact v.valuation_lt_one_iff_mem a
  have hne : I ≠ ⊥ := by
    intro h0
    apply v.ne_bot
    rw [eq_bot_iff]
    intro a ha
    have := (hc a).2 ha
    rw [h0, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).1 this
  refine ⟨⟨I, hp, hne⟩, ?_, hI⟩
  ext a
  exact hc a

theorem IsQuad.exists_embedding_root {F E L : Type} [Field F] [Field E] [Algebra F E] [Field L]
    {δ : F} {θ : E} {σ : E ≃ₐ[F] E} (h : IsQuad δ θ σ) (φ : F →+* L) (r : L)
    (hr : φ δ = r * r) :
    ∃ ψ : E →+* L, (∀ a : F, ψ (algebraMap F E a) = φ a) ∧ ψ θ = r := by
  choose A B hAB using h.span
  have key : ∀ (x : E) (a b : F), x = algebraMap F E a + algebraMap F E b * θ →
      φ (A x) + φ (B x) * r = φ a + φ b * r := by
    intro x a b hx
    have := h.coord_indep (A x - a) (B x - b) (by
      rw [map_sub, map_sub]; linear_combination hx - hAB x)
    rw [sub_eq_zero.1 this.1, sub_eq_zero.1 this.2]
  refine ⟨{ toFun := fun x => φ (A x) + φ (B x) * r
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · rw [key 1 1 0 (by simp)]; simp
  · intro x y
    rw [key (x * y) (A x * A y + δ * B x * B y) (A x * B y + B x * A y) (by
      simp only [map_add (f := _), map_mul, ← h.sq]
      linear_combination y * hAB x + (algebraMap F E (A x) + algebraMap F E (B x) * θ) * hAB y)]
    simp only [map_add (f := _), map_mul, hr]; ring
  · rw [key 0 0 0 (by simp)]; simp
  · intro x y
    rw [key (x + y) (A x + A y) (B x + B y) (by
      simp only [map_add (f := _)]
      linear_combination hAB x + hAB y)]
    simp only [map_add (f := _)]; ring
  · intro a
    change φ (A _) + φ (B _) * r = _
    rw [key _ a 0 (by simp)]; simp
  · change φ (A _) + φ (B _) * r = _
    rw [key _ 0 1 (by simp)]; simp

theorem exists_val_sub_mul_lt_one {F L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ]
    [Valued L Γ] (φ : F → L) (hφ : DenseRange φ) (r c : L) :
    ∃ ρ : F, Valued.v ((r - φ ρ) * c) < (1 : Γ) := by
  have hopen : IsOpen {x : L | Valued.v x < (1 : Γ)} := by
    simpa only [Valuation.restrict_lt_one_iff] using (Valued.isOpen_ball L 1)
  have hcont : Continuous fun x : L => (r - x) * c := by fun_prop
  exact hφ.exists_mem_open (hopen.preimage hcont) ⟨r, by simp⟩

theorem two_places_of_isSquare : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ v : HeightOneSpectrum (𝓞 F), IsSquare (algebraMap F (v.adicCompletion F) δ) → ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 F) = v ∧ w'.under (𝓞 F) = v := by
  intro F E _ _ _ _ _ δ θ σ h v ⟨r, hr⟩
  obtain ⟨ψ, hψ, hθ⟩ := h.exists_embedding_root (algebraMap F (v.adicCompletion F)) r hr
  let u : Valuation E ℤᵐ⁰ := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).comap ψ
  let u' : Valuation E ℤᵐ⁰ := u.comap (σ : E →+* E)
  have hu : ∀ a : F, u (algebraMap F E a) = v.valuation F a := by
    intro a
    change Valued.v (ψ _) = _
    rw [hψ]
    exact v.valuedAdicCompletion_eq_valuation' a
  have hu' : ∀ a : F, u' (algebraMap F E a) = v.valuation F a := by
    intro a
    change u (σ _) = _
    rw [AlgEquiv.commutes, hu]
  obtain ⟨w, hw, hwm⟩ := exists_centre_over v u hu
  obtain ⟨w', hw', hwm'⟩ := exists_centre_over v u' hu'
  refine ⟨w, w', ?_, hw, hw'⟩
  rintro rfl
  have hr0 : r ≠ 0 := by
    rw [← hθ]; exact (map_ne_zero ψ).2 h.root_ne_zero
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    have : (2 : v.adicCompletion F) = algebraMap F _ 2 := by rw [map_ofNat]
    rw [this]; exact (map_ne_zero _).2 two_ne_zero
  obtain ⟨ρ, hρ⟩ := exists_val_sub_mul_lt_one _ (HeightOneSpectrum.denseRange_algebraMap F v)
    r (2 * r)⁻¹
  set t := (r - algebraMap F (v.adicCompletion F) ρ) * (2 * r)⁻¹ with ht
  have hn : θ - algebraMap F E ρ ≠ 0 := by
    intro h0
    exact one_ne_zero (h.coord_indep (-ρ) 1 (by simp; linear_combination h0)).2
  have hd : -θ - algebraMap F E ρ ≠ 0 := by
    intro h0
    exact one_ne_zero (h.coord_indep ρ 1 (by simp; linear_combination -h0)).2
  set y := (θ - algebraMap F E ρ) / (-θ - algebraMap F E ρ) with hy
  have hy1 : y * σ y = 1 := by
    rw [hy, map_div₀, map_sub, map_sub, map_neg, h.conj, AlgEquiv.commutes, neg_neg]
    field_simp
  have huy : u y < 1 := by
    change Valued.v (ψ y) < 1
    have e1 : r - algebraMap F (v.adicCompletion F) ρ = 2 * r * t := by
      rw [ht]; field_simp
    have e2 : -r - algebraMap F (v.adicCompletion F) ρ = -(2 * r * (1 - t)) := by
      linear_combination e1
    rw [hy, map_div₀, map_sub, map_sub, map_neg, hθ, hψ, e1, e2, map_div₀, Valuation.map_neg,
      map_mul _ _ t, map_mul _ _ (1 - t), Valuation.map_one_sub_of_lt _ hρ, mul_one,
      mul_div_cancel_left₀ _ ((Valuation.ne_zero_iff _).2 (mul_ne_zero h2 hr0))]
    exact hρ
  have huu : u y * u' y = 1 := by
    change u y * u (σ y) = 1
    rw [← map_mul, hy1, map_one]
  obtain ⟨n, ⟨d, hd'⟩, hnd | hnd⟩ := w.exists_primeCompl_mul_eq_or_mul_eq (K := E) y
  · have hd1 : 1 ≤ u' (algebraMap (𝓞 E) E d) := not_lt.1 fun a => hd' ((hwm' d).2 a)
    have h1 : u' y ≤ 1 := by
      have := val_integer_le_one u' n
      rw [← hnd, map_mul] at this
      exact le_trans (le_mul_of_one_le_right' hd1) this
    have : u y * u' y < 1 := lt_of_le_of_lt (mul_le_of_le_one_right' h1) huy
    exact this.ne huu
  · have hd1 : 1 ≤ u (algebraMap (𝓞 E) E d) := not_lt.1 fun a => hd' ((hwm d).2 a)
    rw [← hnd, map_mul] at hd1
    exact absurd (lt_of_le_of_lt (mul_le_of_le_one_right' (val_integer_le_one u n)) huy)
      (not_lt.2 hd1)

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisPlacesTransitive
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct Pointwise

namespace GlobalTheory.CNorm

theorem galois_places_transitive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E], (∀ (τ : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)), ∃ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) ∧ ∀ y : E, w'.valuation E y = w.valuation E (τ y)) ∧ ∀ w w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) → ∃ τ : E ≃ₐ[F] E, ∀ y : E, w'.valuation E y = w.valuation E (τ y) := by
  intro F E _ _ _ _ _ _
  refine ⟨fun σ w => ?_, fun w w' hu => ?_⟩
  · set e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv σ.toRingEquiv with he
    have hc : ∀ x : 𝓞 E, ((e x : 𝓞 E) : E) = σ (x : E) := fun x => rfl
    have hfix : ∀ a : 𝓞 F, e (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
      intro a
      apply RingOfIntegers.ext
      rw [hc]
      exact σ.commutes (a : F)
    refine ⟨w.comap (e : 𝓞 E →+* 𝓞 E) e.surjective, ?_, ?_⟩
    · apply HeightOneSpectrum.ext
      ext a
      change e (algebraMap (𝓞 F) (𝓞 E) a) ∈ w.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) a ∈ w.asIdeal
      rw [hfix]
    · intro y
      exact valuation_of_eq_comap σ.toRingEquiv w _ rfl y
  · haveI := w.isPrime
    haveI := w'.isPrime
    haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    haveI : w'.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := hu ▸ ⟨rfl⟩
    obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (w.under (𝓞 F)).asIdeal
      w'.asIdeal w.asIdeal (E ≃ₐ[F] E)
    refine ⟨σ, fun y => valuation_of_eq_comap σ.toRingEquiv w w' ?_ y⟩
    ext x
    rw [Ideal.mem_comap, ← hσ]
    change _ ↔ σ • x ∈ _
    exact Ideal.smul_mem_pointwise_smul_iff.symm

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexFormulaNormsInvolution
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem two_mul_index_sqs_mul_relIndex_norm_involution :
    ∀ (A : Type) [CommGroup A] (σ : A →* A) (ε : A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → ε ≠ 1 → ε ^ 2 = 1 → σ ε = ε → (∀ a : A, a ^ 2 = 1 → a = 1 ∨ a = ε) → 2 * (sqs (⊤ : Subgroup A)).index * (MonoidHom.id A * σ).range.relIndex (σ.eqLocus (MonoidHom.id A)) = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) ^ 2 := by
  intro A _ σ ε h1 h2 h3 h4 h5 h6
  have hn := _root_.GlobalTheory.QNorm.relIndex_norm_mul_relIndex_sqs_ker A σ h1 h2
  have hs := _root_.GlobalTheory.QNorm.two_mul_index_sqs_involution A σ ε h1 h2 h3 h4 h5 h6
  rw [hs, sq, mul_assoc, mul_comm ((sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker), hn]

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteSpanAlgebraMapOfFreeFinite
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mem_smul_top_iff_repr {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (J : Ideal R) (x : M) :
    x ∈ (J • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ J := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun y z hy hz => ?_)
    · simpa using J.mul_mem_right _ hr
    · simpa using J.add_mem hy hz
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem isAdicComplete_of_free_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (I : Ideal R) (h : IsAdicComplete I R) :
    IsAdicComplete I M := by
  classical
  let b := Module.Free.chooseBasis R M
  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] ↔
      ∀ i, b.repr x i ≡ b.repr y i [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro n x y
    rw [SModEq.sub_mem, mem_smul_top_iff_repr b]
    refine forall_congr' fun i => ?_
    rw [SModEq.sub_mem]
    simp
  have hH : IsHausdorff I M := by
    refine ⟨fun x hx => ?_⟩
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    have := h.toIsHausdorff.haus (b.repr x i) fun n => by
      simpa using (key n x 0).1 (hx n) i
    simpa using this
  have hP : IsPrecomplete I M := by
    refine ⟨fun f hf => ?_⟩
    have hc : ∀ i, ∃ L : R, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] :=
      fun i => h.toIsPrecomplete.prec (f := fun n => b.repr (f n) i)
        fun {m n} hmn => (key m _ _).1 (hf hmn) i
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    have : b.repr (b.equivFun.symm L) i = L i := by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [this]
    exact hL i n
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

theorem isAdicComplete_span_algebraMap_of_free_finite :
    ∀ (R O : Type) [CommRing R] [CommRing O] [Algebra R O] [Module.Free R O] [Module.Finite R O]
      (t : R), IsAdicComplete (Ideal.span {t}) R →
        IsAdicComplete (Ideal.span {algebraMap R O t}) O := by
  intro R O _ _ _ _ _ t h
  have h1 : IsAdicComplete (Ideal.span {t}) O := isAdicComplete_of_free_finite _ h
  have h2 : Ideal.span {algebraMap R O t} = (Ideal.span {t}).map (algebraMap R O) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [h2]
  exact (IsAdicComplete.map_algebraMap_iff _ O).2 h1

end GlobalTheory.CNorm
end

