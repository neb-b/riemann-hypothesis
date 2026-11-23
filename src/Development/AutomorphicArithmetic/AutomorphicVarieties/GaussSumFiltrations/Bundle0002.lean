module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0156

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramQuadFormTotallyPositiveProperness
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.TPos

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem reAt_eq (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  unfold reAt
  have h := InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x
  rw [← h, Complex.ofReal_re]

theorem abs_reAt (v : InfinitePlace F) (x : F) : |reAt v x| = v x := by
  rw [reAt_eq, ← InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal v), Real.norm_eq_abs]

theorem reAt_QF {κ : Type} [Fintype κ] (G : Matrix κ κ ℤ) (x : κ → F) (v : InfinitePlace F) :
    reAt v (QF G x) =
      (fun i => reAt v (x i)) ⬝ᵥ (G.map (Int.cast : ℤ → ℝ)) *ᵥ (fun i => reAt v (x i)) / 2 := by
  set φ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) with hφ
  have hx : (fun i => reAt v (x i)) = φ ∘ x := by
    funext i
    simp [reAt_eq, hφ]
  have hG : (G.map (Int.cast : ℤ → ℝ)) = (G.map (Int.cast : ℤ → F)).map φ := by
    ext i j
    simp
  rw [hx, hG, reAt_eq, ← hφ]
  unfold QF BF
  rw [map_div₀, map_ofNat, RingHom.map_dotProduct]
  congr 2
  funext i
  exact RingHom.map_mulVec φ _ x i

theorem posDef_lower {κ : Type} [Fintype κ] (M : Matrix κ κ ℝ) (hM : M.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : κ → ℝ, c * ∑ i, y i ^ 2 ≤ y ⬝ᵥ M *ᵥ y := by
  classical
  rcases isEmpty_or_nonempty κ with hκ | ⟨⟨i0⟩⟩
  · refine ⟨1, one_pos, fun y => ?_⟩
    simp [dotProduct]
  set f : (κ → ℝ) → ℝ := fun y => y ⬝ᵥ M *ᵥ y with hf
  have hfc : Continuous f := by
    simp only [hf, dotProduct, Matrix.mulVec]
    fun_prop
  have hpos : ∀ y : κ → ℝ, y ≠ 0 → 0 < f y := by
    intro y hy
    have := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hy
    simpa [hf] using this
  set S : Set (κ → ℝ) := {y | ∑ i, y i ^ 2 = 1} with hS
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_eq (by fun_prop) continuous_const
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun y hy => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs]
      have h1 : y i ^ 2 ≤ ∑ j, y j ^ 2 :=
        Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [show ∑ j, y j ^ 2 = 1 from hy] at h1
      exact (sq_le_one_iff_abs_le_one _).mp h1
  have hSn : S.Nonempty := ⟨Pi.single i0 1, by simp [hS, Pi.single_apply]⟩
  obtain ⟨y0, hy0S, hmin⟩ := hSc.exists_isMinOn hSn hfc.continuousOn
  have hy0 : y0 ≠ 0 := by
    rintro rfl
    simp [hS] at hy0S
  refine ⟨f y0, hpos y0 hy0, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    simp
  set s := ∑ i, y i ^ 2 with hs
  have hs0 : 0 < s := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    have h1 : y i ^ 2 ≤ s :=
      Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hi' : y i ≠ 0 := by simpa using hi
    have : 0 < y i ^ 2 := by positivity
    linarith
  set t := Real.sqrt s with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hs0
  have htt : t ^ 2 = s := Real.sq_sqrt hs0.le
  have hz : t⁻¹ • y ∈ S := by
    simp only [hS, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [← Finset.mul_sum, ← hs, inv_pow, htt, inv_mul_cancel₀ hs0.ne']
  have hfz : f (t⁻¹ • y) = (t ^ 2)⁻¹ * f y := by
    simp only [hf, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have := hmin hz
  simp only [Set.mem_setOf_eq] at this
  rw [hfz, htt] at this
  have h2 := mul_le_mul_of_nonneg_left this hs0.le
  rw [← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul] at h2
  linarith [mul_comm s (f y0)]

end GlobalTheory.TPos


open GlobalTheory.TPos in
theorem GlobalTheory.HilbertThetaSeries.qf_totPos_proper : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ]
    (G : Matrix κ κ ℤ), EvenPos G → (∀ x : κ → F, x ≠ 0 → TP (QF G x)) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ (x : κ → F) v, c * ∑ i, reAt v (x i) ^ 2 ≤ reAt v (QF G x)) ∧
      ∀ (a ξ : F), {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}.Finite := by
  intro F _ _ _ κ _ _ G hG
  have hM : (G.map (Int.cast : ℤ → ℝ)).PosDef := hG.1
  obtain ⟨c, hc, hcb⟩ := posDef_lower _ hM
  have key : ∀ (x : κ → F) v, (c / 2) * ∑ i, reAt v (x i) ^ 2 ≤ reAt v (QF G x) := by
    intro x v
    rw [reAt_QF]
    have := hcb (fun i => reAt v (x i))
    linarith
  have hinj : ∀ (v : InfinitePlace F) (y : F), reAt v y = 0 → y = 0 := by
    intro v y h
    rw [reAt_eq] at h
    exact (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)).injective (by simpa using h)
  refine ⟨?_, ⟨c / 2, by positivity, key⟩, ?_⟩
  · intro x hx v
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have hyi : reAt v (x i) ≠ 0 := fun h => hi (hinj v _ h)
    have h1 : reAt v (x i) ^ 2 ≤ ∑ j, reAt v (x j) ^ 2 :=
      Finset.single_le_sum (f := fun j => reAt v (x j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : 0 < reAt v (x i) ^ 2 := by positivity
    have h3 := mul_pos (half_pos hc) (lt_of_lt_of_le h2 h1)
    have := key x v
    linarith
  · intro a ξ
    by_cases ha : a = 0
    · apply (Set.finite_singleton (0 : κ → F)).subset
      rintro x ⟨hx, -⟩
      unfold aL at hx
      obtain ⟨z, -, rfl⟩ := AddSubgroup.mem_map.mp hx
      simp [ha]
    set B : ℝ := ∑ v : InfinitePlace F, Real.sqrt (reAt v ξ / (c / 2)) / v a with hB
    set T : Set F := {y : F | IsIntegral ℤ y ∧ ∀ φ : F →+* ℂ, ‖φ y‖ ≤ B} with hT
    have hTf : T.Finite := NumberField.Embeddings.finite_of_norm_le F ℂ B
    apply ((Set.Finite.pi (t := fun _ : κ => T) (fun _ => hTf)).image (fun z => a • z)).subset
    rintro x ⟨hx, hxξ⟩
    unfold aL at hx
    obtain ⟨z, hz, rfl⟩ := AddSubgroup.mem_map.mp hx
    refine ⟨z, fun i _ => ?_, rfl⟩
    unfold LL at hz
    have hzi := (AddSubgroup.mem_pi _).mp hz i (Set.mem_univ _)
    refine ⟨hzi, fun φ => ?_⟩
    rw [← NumberField.InfinitePlace.apply]
    set w := InfinitePlace.mk φ
    have hxi : (DistribSMul.toAddMonoidHom (κ → F) a z) i = a * z i := by simp
    have hwa : 0 < w a := (InfinitePlace.pos_iff).mpr ha
    have hk := key (DistribSMul.toAddMonoidHom (κ → F) a z) w
    rw [hxξ] at hk
    have h1 : reAt w ((DistribSMul.toAddMonoidHom (κ → F) a z) i) ^ 2 ≤
        ∑ j, reAt w ((DistribSMul.toAddMonoidHom (κ → F) a z) j) ^ 2 :=
      Finset.single_le_sum (f := fun j => reAt w ((DistribSMul.toAddMonoidHom (κ → F) a z) j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : reAt w ((DistribSMul.toAddMonoidHom (κ → F) a z) i) ^ 2 ≤ reAt w ξ / (c / 2) := by
      rw [le_div_iff₀ (half_pos hc)]
      nlinarith
    have h3 := Real.abs_le_sqrt h2
    rw [abs_reAt, hxi, map_mul] at h3
    have h4 : w (z i) ≤ Real.sqrt (reAt w ξ / (c / 2)) / w a := by
      rw [le_div_iff₀ hwa]
      linarith [mul_comm (w a) (w (z i))]
    refine h4.trans ?_
    exact Finset.single_le_sum (f := fun v : InfinitePlace F => Real.sqrt (reAt v ξ / (c / 2)) / v a)
      (fun v _ => div_nonneg (Real.sqrt_nonneg _) (apply_nonneg v a)) (Finset.mem_univ w)

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenPosGram_quadForm_totallyPositive_properness : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → (∀ x : κ → F, x ≠ 0 → TP (QF G x)) ∧ (∃ c : ℝ, 0 < c ∧ ∀ (x : κ → F) v, c * ∑ i, reAt v (x i) ^ 2 ≤ reAt v (QF G x)) ∧ ∀ (a ξ : F), {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}.Finite := by
  first | exact @GlobalTheory.HilbertThetaSeries.qf_totPos_proper | exact GlobalTheory.HilbertThetaSeries.qf_totPos_proper | (intros; apply GlobalTheory.HilbertThetaSeries.qf_totPos_proper <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsDifferentGeneratorTotallyPositiveTranslate
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.DelGen

variable {F : Type} [Field F] [NumberField F]

theorem exists_pos_val (T : Finset (HeightOneSpectrum (𝓞 F))) (γ : HeightOneSpectrum (𝓞 F) → WithZero (Multiplicative ℤ))
    (hγ : ∀ w ∈ T, γ w ≠ 0) :
    ∃ a : F, (∀ w ∈ T, w.valuation F a = γ w) ∧ ∀ φ : F →+* ℝ, 0 < φ a := by
  choose t ht using fun w : HeightOneSpectrum (𝓞 F) => w.valuation_surjective F (γ w)
  set M : ℕ := T.sup (fun w => (WithZero.log (γ w)).natAbs) + 1 with hM
  obtain ⟨a, ha, hpos⟩ := GlobalTheory.FinPlaceApproxPos.approxpos_target F T t M
  refine ⟨a, fun w hw => ?_, hpos⟩
  have hle : (WithZero.log (γ w)).natAbs ≤ T.sup (fun w => (WithZero.log (γ w)).natAbs) :=
    Finset.le_sup (f := fun w => (WithZero.log (γ w)).natAbs) hw
  have hlt : WithZero.exp (-(M : ℤ)) < γ w := by
    conv_rhs => rw [← WithZero.exp_log (hγ w hw)]
    rw [WithZero.exp_lt_exp]
    omega
  rw [← ht w]
  exact Valuation.map_eq_of_sub_lt _ (lt_of_le_of_lt (ha w hw) (by rw [ht w]; exact hlt))

theorem finite_over (p : ℕ) (hp : p ≠ 0) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ w, w ∈ T ↔ ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine ⟨(Ideal.finite_factors h0).toFinset, fun w => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]

end GlobalTheory.HilbertThetaSeries.DelGen


open GlobalTheory.HilbertThetaSeries.DelGen in
theorem GlobalTheory.HilbertThetaSeries.del_exists_and_move : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → (∃ δ : F, IsDel p δ) ∧ ∀ δ : F, IsDel p δ → ∀ y : (Af F)ˣ, ∃ ξ : Fˣ, TP (ξ : F) ∧ AtP p δ (Units.map (algebraMap F (Af F)).toMonoidHom ξ * y) := by
  intro F _ _ _ p hp
  obtain ⟨T, hT⟩ := finite_over (F := F) p hp.ne_zero
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha, -⟩ := exists_pos_val T (fun w => WithZero.exp (-(ordI w (differentIdeal ℤ (𝓞 F)) : ℤ)))
      (fun w _ => WithZero.exp_ne_zero)
    exact ⟨a, fun w hw => ha w ((hT w).2 hw)⟩
  · intro δ hδ y
    have hne : ∀ w ∈ T, Valued.v (pLoc F w (y : Af F)) * w.valuation F δ ≠ 0 := by
      intro w hw
      refine mul_ne_zero ?_ ?_
      · rw [Ne, map_eq_zero]
        exact ((y.map (pLoc F w).toMonoidHom).ne_zero)
      · rw [hδ w ((hT w).1 hw)]
        exact WithZero.exp_ne_zero
    obtain ⟨a, ha, hpos⟩ := exists_pos_val T (fun w => (Valued.v (pLoc F w (y : Af F)) * w.valuation F δ)⁻¹)
      (fun w hw => inv_ne_zero (hne w hw))
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
    have ha0 : a ≠ 0 := by
      intro h
      have h1 := hpos (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))
      rw [h, map_zero] at h1
      exact lt_irrefl _ h1
    refine ⟨Units.mk0 a ha0, fun u => ?_, fun w hw => ?_⟩
    · show 0 < (u.embedding a).re
      rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal u), Complex.ofReal_re]
      exact hpos _
    · have hw' := (hT w).2 hw
      rw [Units.val_mul, Units.coe_map, map_mul]
      show Valued.v ((a : w.adicCompletion F) * pLoc F w (y : Af F)) * w.valuation F δ = 1
      rw [map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ha w hw', mul_assoc, inv_mul_cancel₀ (hne w hw')]

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_different_generator_totallyPositive_translate : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → (∃ δ : F, IsDel p δ) ∧ ∀ δ : F, IsDel p δ → ∀ y : (Af F)ˣ, ∃ ξ : Fˣ, TP (ξ : F) ∧ AtP p δ (Units.map (algebraMap F (Af F)).toMonoidHom ξ * y) := by
  first | exact @GlobalTheory.HilbertThetaSeries.del_exists_and_move | exact GlobalTheory.HilbertThetaSeries.del_exists_and_move | (intros; apply GlobalTheory.HilbertThetaSeries.del_exists_and_move <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsFiniteRepsScaledLatticeCardNorm
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.RepsLat

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem mem_aL_iff (a : F) (x : κ → F) :
    x ∈ aL κ a ↔ ∃ m : κ → 𝓞 F, x = fun i => a * (m i : F) := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨fun i => ⟨l i, (AddSubgroup.mem_pi _).1 hl i (Set.mem_univ _)⟩, ?_⟩
    funext i
    rfl
  · rintro ⟨m, rfl⟩
    refine ⟨fun i => (m i : F), ?_, ?_⟩
    · exact (AddSubgroup.mem_pi _).2 fun i _ => (m i).2
    · funext i
      rfl

end GlobalTheory.HilbertThetaSeries.RepsLat

namespace GlobalTheory.HilbertThetaSeries


open GlobalTheory.HilbertThetaSeries.RepsLat in
theorem exists_isReps_aL : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (a b : F),
    a ≠ 0 → b ≠ 0 → IsIntegral ℤ (a / b) → ∃ T : Finset (κ → F), IsReps (aL κ a) (aL κ b) T ∧ 0 ∈ T ∧
      aL κ a ≤ aL κ b ∧ (T.card : ℚ) = |Algebra.norm ℚ (a / b)| ^ Fintype.card κ := by
  intro F _ _ κ _ _ a b ha hb hc
  obtain ⟨c, hcF⟩ : ∃ c : 𝓞 F, (c : F) = a / b := ⟨⟨a / b, hc⟩, rfl⟩
  have hab : a = b * (c : F) := by rw [hcF]; field_simp
  have hc0 : c ≠ 0 := by
    intro h
    apply ha
    have h0 : (c : F) = 0 := by rw [h]; rfl
    rw [hcF, div_eq_zero_iff] at h0
    tauto
  let I : Ideal (𝓞 F) := Ideal.span {c}
  have hcard : Nat.card (𝓞 F ⧸ I) = (Algebra.norm ℤ c).natAbs := by
    rw [← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hne : (Algebra.norm ℤ c).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero, Algebra.norm_ne_zero_iff]
    exact hc0
  haveI : Finite (𝓞 F ⧸ I) := Nat.finite_of_card_ne_zero (hcard ▸ hne)
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  classical
  let s : 𝓞 F ⧸ I → 𝓞 F := fun q => if q = 0 then 0 else Classical.choose (Ideal.Quotient.mk_surjective q)
  have hs : ∀ q, Ideal.Quotient.mk I (s q) = q := by
    intro q
    by_cases h : q = 0
    · simp [s, h]
    · simp only [s, if_neg h]
      exact Classical.choose_spec (Ideal.Quotient.mk_surjective q)
  have hs0 : s 0 = 0 := by simp [s]
  let e : (κ → 𝓞 F ⧸ I) → (κ → F) := fun q i => b * (s (q i) : F)
  have he : Function.Injective e := by
    intro q q' h
    funext i
    have h1 := mul_left_cancel₀ hb (congrFun h i)
    have h3 : s (q i) = s (q' i) := RingOfIntegers.ext h1
    rw [← hs (q i), ← hs (q' i), h3]
  refine ⟨Finset.univ.image e, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact (mem_aL_iff b _).2 ⟨fun i => s (q i), rfl⟩
  · intro x hx
    obtain ⟨m, rfl⟩ := (mem_aL_iff b x).1 hx
    refine ⟨e (fun i => Ideal.Quotient.mk I (m i)), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have hI : ∀ i, m i - s (Ideal.Quotient.mk I (m i)) ∈ I := fun i => by
        rw [← Ideal.Quotient.eq, hs]
      choose r hr using fun i => Ideal.mem_span_singleton'.1 (hI i)
      refine (mem_aL_iff a _).2 ⟨r, ?_⟩
      funext i
      have h1 := congrArg (fun z : 𝓞 F => (z : F)) (hr i)
      simp only [map_mul, map_sub] at h1
      simp only [e, Pi.sub_apply]
      rw [hab]
      linear_combination -b * h1
    · rintro y ⟨hyT, hy⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hyT
      have hq : q = fun i => Ideal.Quotient.mk I (m i) := by
        funext i
        obtain ⟨r, hr⟩ := (mem_aL_iff a _).1 hy
        have h1 := congrFun hr i
        simp only [e, Pi.sub_apply] at h1
        have h2 : ((m i - s (q i) : 𝓞 F) : F) = ((r i * c : 𝓞 F) : F) := by
          simp only [map_mul, map_sub]
          apply mul_left_cancel₀ hb
          rw [hab] at h1
          linear_combination h1
        have h3 : m i - s (q i) ∈ I := Ideal.mem_span_singleton'.2 ⟨r i, (RingOfIntegers.ext h2).symm⟩
        rw [← hs (q i)]
        exact (Ideal.Quotient.eq.2 h3).symm
      rw [hq]
  · refine Finset.mem_image.2 ⟨0, Finset.mem_univ _, ?_⟩
    funext i
    simp [e, hs0]
  · intro x hx
    obtain ⟨m, rfl⟩ := (mem_aL_iff a x).1 hx
    refine (mem_aL_iff b _).2 ⟨fun i => c * m i, ?_⟩
    funext i
    simp only [map_mul]
    rw [hab]
    ring
  · rw [Finset.card_image_of_injective _ he, Finset.card_univ, Fintype.card_fun, ← Nat.card_eq_fintype_card,
      hcard, ← hcF, Nat.cast_pow, Nat.cast_natAbs, ← Algebra.coe_norm_int, Int.cast_abs]

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_reps_scaled_lattice_card_norm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (a b : F), a ≠ 0 → b ≠ 0 → IsIntegral ℤ (a / b) → ∃ T : Finset (κ → F), IsReps (aL κ a) (aL κ b) T ∧ 0 ∈ T ∧ aL κ a ≤ aL κ b ∧ (T.card : ℚ) = |Algebra.norm ℚ (a / b)| ^ Fintype.card κ := by
  first | exact @GlobalTheory.HilbertThetaSeries.exists_isReps_aL | exact GlobalTheory.HilbertThetaSeries.exists_isReps_aL | (intros; apply GlobalTheory.HilbertThetaSeries.exists_isReps_aL <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertHolomorphicUnnormalizedSlashOfPos
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.HolKeep

open UpperHalfPlane hiding I

variable {F : Type} [Field F] [NumberField F]

def U (F : Type) [Field F] [NumberField F] : Set (InfinitePlace F → ℂ) := {z | ∀ v, 0 < (z v).im}

theorem cmp_det (h : GL (Fin 2) (InfinitePlace F → ℝ)) (v : InfinitePlace F) :
    ((cmp v h).det : ℝ) = (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v := by
  simp [cmp, Matrix.GeneralLinearGroup.map_det]

def mob (h : GL (Fin 2) (InfinitePlace F → ℝ)) (z : InfinitePlace F → ℂ) : InfinitePlace F → ℂ :=
  fun v => num (cmp v h) (z v) / denom (cmp v h) (z v)

theorem mob_im_pos {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) {z} (hz : z ∈ U F) (v) :
    0 < (mob h z v).im := by
  have hd : 0 < ((cmp v h).det : ℝ) := by
    rw [cmp_det]
    exact hh v
  have hzv : 0 < (z v).im := hz v
  show 0 < (num (cmp v h) (z v) / denom (cmp v h) (z v)).im
  rw [moebius_im]
  exact div_pos (mul_pos hd hzv) (normSq_denom_pos _ hzv.ne')

theorem mob_mapsTo {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) : Set.MapsTo (mob h) (U F) (U F) := by
  intro z hz
  show ∀ v, 0 < (mob h z v).im
  exact fun v => mob_im_pos hh hz v

theorem mob_diff (h : GL (Fin 2) (InfinitePlace F → ℝ)) : DifferentiableOn ℂ (mob h) (U F) := by
  rw [differentiableOn_pi]
  intro v z hz
  have hzv : (z v).im ≠ 0 := (hz v).ne'
  have hp : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => w v) z := differentiable_apply v z
  have hn : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => num (cmp v h) (w v)) z :=
    (hp.const_mul _).add_const _
  have hd : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => denom (cmp v h) (w v)) z :=
    (hp.const_mul _).add_const _
  apply DifferentiableAt.differentiableWithinAt
  show DifferentiableAt ℂ (fun w => num (cmp v h) (w v) / denom (cmp v h) (w v)) z
  simp only [div_eq_mul_inv]
  exact hn.mul (hd.inv (denom_ne_zero_of_im _ hzv))

theorem act_eq {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) {z} (hz : z ∈ U F) :
    act h (fun v => ofComplex (z v)) = fun v => ofComplex (mob h z v) := by
  funext v
  rw [act.eq_1, ofComplex_apply_of_im_pos (hz v), ofComplex_apply_of_im_pos (mob_im_pos hh hz v)]
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by rw [cmp_det]; exact hh v)]
  rfl

theorem hilbertHolomorphic_unnormalizedSlash_of_pos (k : ℕ) {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) {f : Hn F → ℂ} (hf : Hol f) :
    Hol (sl0 k h f) := by
  have hF : DifferentiableOn ℂ (fun z : InfinitePlace F → ℂ => f (fun v => ofComplex (z v))) (U F) := hf
  have hcomp := hF.comp (mob_diff h) (mob_mapsTo hh)
  have hden : DifferentiableOn ℂ
      (fun z : InfinitePlace F → ℂ => (∏ v, denom (cmp v h) (z v))⁻¹ ^ k) (U F) := by
    intro z hz
    have hne : (∏ v, denom (cmp v h) (z v)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun v _ => denom_ne_zero_of_im _ (hz v).ne'
    have hpr : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => ∏ v, denom (cmp v h) (w v)) z := by
      simp only [denom]
      fun_prop
    exact ((hpr.inv hne).pow k).differentiableWithinAt
  show DifferentiableOn ℂ (fun z : InfinitePlace F → ℂ => sl0 k h f (fun v => ofComplex (z v))) (U F)
  refine (hden.mul hcomp).congr ?_
  intro z hz
  have hc : ∀ v, ((ofComplex (z v) : ℍ) : ℂ) = z v := fun v => by
    rw [ofComplex_apply_of_im_pos (hz v)]
  simp only [sl0.eq_1, act_eq hh hz, hc, Function.comp_apply, Pi.mul_apply]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (f g : Hn F → ℂ) (c : ℂ), Hol f → Hol g → Hol (f + g) ∧ Hol (c • f) ∧ Hol (f * g) ∧ Hol (1 : Hn F → ℂ) ∧ Hol (0 : Hn F → ℂ) ∧ ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → Hol (sl0 k h f) ∧ Hol (sl k h f) := by
  intro F _ _ k f g c hf hg
  refine ⟨DifferentiableOn.add hf hg, DifferentiableOn.const_smul hf c, DifferentiableOn.mul hf hg,
    differentiableOn_const 1, differentiableOn_const 0, fun h hh => ⟨hilbertHolomorphic_unnormalizedSlash_of_pos k hh hf, ?_⟩⟩
  exact DifferentiableOn.mul (differentiableOn_const _) (hilbertHolomorphic_unnormalizedSlash_of_pos k hh hf)

end GlobalTheory.HilbertThetaSeries.HolKeep
end
end

