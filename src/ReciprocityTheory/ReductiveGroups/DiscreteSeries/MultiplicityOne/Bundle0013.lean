module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBePosB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.BeIntIntegrableOf

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBePos
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem bePos_hyp (h : UnitaryGroupStructuralFacts) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) : BesselPositivity.Hyp D := by
  have hS := stSInt h
  obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h16, h17, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, a13, -, a15, a16, -, a18, -, a20, a21, a22, -, -, -, -, -⟩ := h1
  exact ⟨a22, a21, a20, a16, a15, a13 k r Wp Wp D, a18, h17, h16, fun b hb => hS k r Wp D hD b hb⟩

private theorem two_mul_AB_le_aM (k r : ℕ) : 2 * AB k r ≤ aM k r := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  simp only [AB, aM, nR]
  push_cast
  nlinarith [mul_nonneg hk hr, mul_nonneg (mul_nonneg hk hr) hr, mul_nonneg (mul_nonneg hk hk) hr,
    mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg hk hk) hk, mul_nonneg hr hr, mul_nonneg hk hk]

private theorem exists_bessel_coef_of_mem_Vfl {k r : ℕ} (X : SigData k r) (haM : aM k r ≤ X.a) {u : X.Hs}
    (hu : u ∈ Vfl X) : ∃ C : ℝ, BesselPositivity.Coef (mc X u X.w) C X.a := by
  obtain ⟨C, hC⟩ := hu
  refine ⟨max C 0, ⟨?_, le_max_right _ _, (two_mul_AB_le_aM k r).trans haM, ?_⟩⟩
  ·
    have h1 := X.rep.2.2 u
    exact (continuous_const.inner continuous_id).comp_continuousOn h1
  · intro y hy
    have ht : 0 ≤ gN y ^ (-X.a) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    exact (hC y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht)

private lemma inner_apply_right_inverse_eq_inner_of_isometry {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (T S : E →L[ℂ] E)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (hTS : T.comp S = 1) (x : E) : ⟪x, S x⟫_ℂ = ⟪T x, x⟫_ℂ := by
  let L : E →ₗᵢ[ℂ] E := ⟨T.toLinearMap, hT⟩
  have h1 : ⟪T x, T (S x)⟫_ℂ = ⟪x, S x⟫_ℂ := L.inner_map_map x (S x)
  have h2 : T (S x) = x := by
    have := congrArg (fun F : E →L[ℂ] E => F x) hTS
    simpa using this
  rw [h2] at h1
  exact h1.symm

theorem bePos_inner_eq {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] (D : RealPlaceData k r Wp Wp) (X : SigData k r) (H : BesselPositivity.Hyp D)
    {d : ℝ} (hd : IsFdegG D X d) {u : X.Hs} {C a : ℝ} (hc : BesselPositivity.Coef (mc X u X.w) C a) (ξ : Wp)
    (hI : Integrable (beInt D X u u) (D.μW.prod D.μN)) :
    ⟪ξ, beOp D X u u ξ⟫_ℂ = (d : ℂ) * ∫ g, BesselPositivity.phi D (mc X u X.w) ξ (Matrix.of g) ∂D.μG := by
  obtain ⟨hd0, hdS⟩ := hd
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hA : ⟪ξ, beOp D X u u ξ⟫_ℂ = ∫ p, ⟪ξ, beInt D X u u p ξ⟫_ℂ ∂(D.μW.prod D.μN) := by
    unfold beOp
    rw [ContinuousLinearMap.integral_apply hI, integral_inner (hI.apply_continuousLinearMap ξ)]
  have hGae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r := by
    first
    | exact ae_iff.2 D.haarG.conc
    | exact measure_mono_null (fun a ha => ha) D.haarG.conc
  rw [hA, ← BesselPositivity.fubini1 D H hc ξ, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [BesselPositivity.ae_SS (D := D)] with p hp
  have hs : BesselPositivity.sP p ∈ GV k r := BesselPositivity.sP_mem H.cg hp

  have hSch : ∫ g, mc X u X.w (Matrix.of g * BesselPositivity.sP p) * star (mc X u X.w (Matrix.of g)) ∂D.μG =
      mc X u u (BesselPositivity.sP p) / d := by
    have hc1 : ∀ᵐ g ∂D.μG, mc X u X.w (Matrix.of g * BesselPositivity.sP p) * star (mc X u X.w (Matrix.of g)) =
        mc X (X.σ (BesselPositivity.sP p) u) X.w (Matrix.of g) * star (mc X u X.w (Matrix.of g)) := by
      filter_upwards [hGae] with g hg
      simp only [mc, X.rep.1.2 _ hg _ hs, ContinuousLinearMap.comp_apply]
    rw [integral_congr_ae hc1, ((hdS (X.σ (BesselPositivity.sP p) u) X.w u X.w).2)]
    simp only [mc, inner_self_eq_norm_sq_to_K, X.w_norm]
    simp
  rw [hSch]
  have ha := hp.1
  have hinv := inner_apply_right_inverse_eq_inner_of_isometry (D.π (Matrix.of p.1)) (D.π (Matrix.of p.1)⁻¹) (D.π_unitary _ ha) (by
    rw [← D.π_rep.2 _ ha _ ((H.cw k r D.z).inv_mem _ ha), Matrix.mul_nonsing_inv _ ((H.cw k r D.z).unit _ ha),
      D.π_rep.1]) ξ
  have hc2 : star ⟪ξ, D.π (Matrix.of p.1) ξ⟫_ℂ = ⟪D.π (Matrix.of p.1) ξ, ξ⟫_ℂ := inner_conj_symm _ _
  simp only [beInt, BesselPositivity.Kf, BesselPositivity.PiO, BesselPositivity.sP, inner_smul_right, ContinuousLinearMap.smul_apply,
    inner_smul_right, star_mul', hinv, hc2]
  field_simp

theorem bePos_identity (h : UnitaryGroupStructuralFacts) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (haM : aM k r ≤ X.a)
    {d : ℝ} (hd : IsFdegG D X d) {u : X.Hs} (hu : u ∈ Vfl X) (ξ : Wp)
    (hI : Integrable (beInt D X u u) (D.μW.prod D.μN)) :
    ⟪ξ, beOp D X u u ξ⟫_ℂ =
      (d : ℂ) * ((∫ g, BesselPositivity.bet D (Matrix.of g) * ‖BesselPositivity.Bv D (mc X u X.w) ξ (Matrix.of g)‖ ^ 2 ∂D.μG : ℝ) : ℂ) := by
  obtain ⟨C, hc⟩ := exists_bessel_coef_of_mem_Vfl X haM hu
  have H := bePos_hyp h D hD
  rw [bePos_inner_eq D X H hd hc ξ hI, BesselPositivity.phi_eq D H hc ξ]

theorem stBePos (h : UnitaryGroupStructuralFacts) : StBePos := by
  intro k r Wp _ _ _ D X hD hX ha u hu ξ
  obtain ⟨d, hd⟩ := stSchurG k r Wp D X hD hX
  by_cases hI : Integrable (beInt D X u u) (D.μW.prod D.μN)
  swap
  · have h0 : beOp D X u u = 0 := integral_undef hI
    rw [h0]
    simp
  rw [bePos_identity h D X hD ha hd hu ξ hI]
  have h0 : 0 ≤ ∫ g, BesselPositivity.bet D (Matrix.of g) * ‖BesselPositivity.Bv D (mc X u X.w) ξ (Matrix.of g)‖ ^ 2 ∂D.μG :=
    integral_nonneg fun g => mul_nonneg (BesselPositivity.bet_nonneg (D := D) _) (sq_nonneg _)
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg hd.1.le h0

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MinorsOnOfDD
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem repro_scalar (D : RealPlaceData k r Wp Wp) (X : SigData k r) (d : ℝ) {u v : X.Hs} (e f : Wp)
    (hI : Integrable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v) D.μG)
    (hR : beOp D X u v = (d : ℂ) • ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG) :
    Integrable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
      ⟪e, beOp D X (X.σ (Matrix.of y) X.w) v f⟫_ℂ) D.μG ∧
    ⟪e, beOp D X u v f⟫_ℂ = (d : ℂ) * ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
      ⟪e, beOp D X (X.σ (Matrix.of y) X.w) v f⟫_ℂ ∂D.μG := by
  let L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e).comp (ContinuousLinearMap.apply ℂ Wp f)
  have hL : ∀ A : Wp →L[ℂ] Wp, L A = ⟪e, A f⟫_ℂ := fun A => by
    simp [L, innerSL_apply_apply]
  have hLa : ∀ (c : ℂ) (A : Wp →L[ℂ] Wp), L (c • A) = c * ⟪e, A f⟫_ℂ := fun c A => by
    rw [map_smul, hL, smul_eq_mul]
  refine ⟨(L.integrable_comp hI).congr (Filter.Eventually.of_forall fun y => hLa _ _), ?_⟩
  rw [hR, ContinuousLinearMap.smul_apply, inner_smul_right, ← hL, ← L.integral_comp_comm hI]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => hLa _ _)

theorem opint (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp) (ha0 : 0 ≤ X.a) {b : ℝ}
    (hab : AB k r ≤ X.a - b) {u v : X.Hs} (hu : u ∈ Vfl X)
    (hbv : ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b) :
    Integrable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v) D.μG := by
  obtain ⟨Cc, hCc0, hCc⟩ := coef_bound X ha0 hu
  obtain ⟨Cb, hCb⟩ := hbv
  have hm : AEStronglyMeasurable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ •
      beOp D X (X.σ (Matrix.of y) X.w) v) D.μG :=
    (show AEStronglyMeasurable (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ) D.μG from
      (sig_aesm D X X.w).inner aestronglyMeasurable_const).smul (be_aesm D X v)
  refine ((gN_integrable D hGN hab).const_mul (Cc * Cb)).mono' hm ?_
  filter_upwards [ae_G D] with y hy
  rw [norm_smul]
  have e : gN (Matrix.of y) ^ (-(X.a - b)) = gN (Matrix.of y) ^ (-X.a) * gN (Matrix.of y) ^ b := by
    rw [← Real.rpow_add (gN_pos hy)]; ring_nf
  rw [e]
  calc ‖⟪X.σ (Matrix.of y) X.w, u⟫_ℂ‖ * ‖beOp D X (X.σ (Matrix.of y) X.w) v‖
      ≤ (Cc * gN (Matrix.of y) ^ (-X.a)) * (Cb * gN (Matrix.of y) ^ b) :=
        mul_le_mul (hCc _ hy) (hCb _ hy) (norm_nonneg _)
          (mul_nonneg hCc0 (Real.rpow_nonneg (gN_nonneg _) _))
    _ = _ := by ring

theorem ext1 (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp) (ha0 : 0 ≤ X.a) {d b : ℝ}
    (hd : 0 < d) (hb0 : 0 ≤ b) (hab : AB k r ≤ X.a - b)
    (hbe : ∀ v ∈ Vfl X, ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b)
    (hRep : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, beOp D X u v = (d : ℂ) • ∫ y : Mt k r,
      ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG)
    {u₂ u₄ : X.Hs} (hu₂ : u₂ ∈ Vfl X) (hu₄ : u₄ ∈ Vfl X) (u₃ : X.Hs) (e₁ e₂ e₃ e₄ : Wp)
    (h : ∀ φ : Mat k r → ℂ, IsTestG φ → Mn D X (sigInt D X φ X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0) :
    ∀ u ∈ Vfl X, Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
  refine vanish_core D X hGN ha0 hd hb0 hab (fun u => Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄) ?_ ?_ ?_ h
  · let L₂ : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e₁).comp (ContinuousLinearMap.apply ℂ Wp e₂)
    let L₄ : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e₁).comp (ContinuousLinearMap.apply ℂ Wp e₄)
    have m2 := L₂.continuous.comp_aestronglyMeasurable (be_aesm D X u₂)
    have m4 := L₄.continuous.comp_aestronglyMeasurable (be_aesm D X u₄)
    exact (m2.mul aestronglyMeasurable_const).sub (m4.mul aestronglyMeasurable_const)
  · obtain ⟨C₂, h₂⟩ := hbe u₂ hu₂
    obtain ⟨C₄, h₄⟩ := hbe u₄ hu₄
    refine ⟨‖e₁‖ * ‖e₂‖ * C₂ * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ +
      ‖e₁‖ * ‖e₄‖ * C₄ * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖, fun y hy => ?_⟩
    simp only [Mn]
    calc ‖⟪e₁, beOp D X (X.σ y X.w) u₂ e₂⟫_ℂ * ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ -
          ⟪e₁, beOp D X (X.σ y X.w) u₄ e₄⟫_ℂ * ⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖
        ≤ ‖⟪e₁, beOp D X (X.σ y X.w) u₂ e₂⟫_ℂ‖ * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ +
          ‖⟪e₁, beOp D X (X.σ y X.w) u₄ e₄⟫_ℂ‖ * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖ := by
          rw [← norm_mul, ← norm_mul]; exact norm_sub_le _ _
      _ ≤ (‖e₁‖ * ‖e₂‖ * (C₂ * gN y ^ b)) * ‖⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ‖ +
          (‖e₁‖ * ‖e₄‖ * (C₄ * gN y ^ b)) * ‖⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_right ((kbound _ _ _).trans
              (mul_le_mul_of_nonneg_left (h₂ y hy) (by positivity))) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right ((kbound _ _ _).trans
              (mul_le_mul_of_nonneg_left (h₄ y hy) (by positivity))) (norm_nonneg _))
      _ = _ := by ring
  · intro u hu
    obtain ⟨i2, r2⟩ := repro_scalar D X d e₁ e₂ (opint D X hGN ha0 hab hu (hbe u₂ hu₂)) (hRep u hu u₂ hu₂)
    obtain ⟨i4, r4⟩ := repro_scalar D X d e₁ e₄ (opint D X hGN ha0 hab hu (hbe u₄ hu₄)) (hRep u hu u₄ hu₄)
    have e5 : ∀ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
        Mn D X (X.σ (Matrix.of y) X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ =
        (⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * ⟪e₁, beOp D X (X.σ (Matrix.of y) X.w) u₂ e₂⟫_ℂ) *
          ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ -
        (⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * ⟪e₁, beOp D X (X.σ (Matrix.of y) X.w) u₄ e₄⟫_ℂ) *
          ⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ := fun y => by simp only [Mn]; ring
    show Mn D X u u₂ u₃ u₄ e₁ e₂ e₃ e₄ = (d : ℂ) * ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
      Mn D X (X.σ (Matrix.of y) X.w) u₂ u₃ u₄ e₁ e₂ e₃ e₄ ∂D.μG
    simp only [e5]
    rw [integral_sub (i2.mul_const _) (i4.mul_const _), integral_mul_const, integral_mul_const]
    simp only [Mn]
    rw [r2, r4]
    ring

theorem mn_swap (D : RealPlaceData k r Wp Wp) (X : SigData k r) (u₁ u₂ u₃ u₄ : X.Hs) (e₁ e₂ e₃ e₄ : Wp) :
    Mn D X u₃ u₂ u₁ u₄ e₃ e₂ e₁ e₄ = -Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ := by
  unfold Mn; ring

theorem mn_herm (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hH : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ)
    {u₁ u₂ u₃ u₄ : X.Hs} (h₁ : u₁ ∈ Vfl X) (h₂ : u₂ ∈ Vfl X) (h₃ : u₃ ∈ Vfl X) (h₄ : u₄ ∈ Vfl X)
    (e₁ e₂ e₃ e₄ : Wp) :
    Mn D X u₂ u₁ u₄ u₃ e₂ e₁ e₄ e₃ = starRingEnd ℂ (Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄) := by
  have kc : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, ∀ e f : Wp,
      ⟪f, beOp D X v u e⟫_ℂ = starRingEnd ℂ ⟪e, beOp D X u v f⟫_ℂ := by
    intro u hu v hv e f
    rw [hH v hv u hu e f, inner_conj_symm]
  unfold Mn
  rw [kc u₁ h₁ u₂ h₂ e₁ e₂, kc u₃ h₃ u₄ h₄ e₃ e₄, kc u₃ h₃ u₂ h₂ e₃ e₂, kc u₁ h₁ u₄ h₄ e₁ e₄]
  simp only [map_sub, map_mul]
  ring

theorem minorsOn_of_DD (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp) (ha0 : 0 ≤ X.a)
    {d b : ℝ} (hd : 0 < d) (hb0 : 0 ≤ b) (hab : AB k r ≤ X.a - b)
    (hbe : ∀ v ∈ Vfl X, ∃ C : ℝ, ∀ y ∈ GV k r, ‖beOp D X (X.σ y X.w) v‖ ≤ C * gN y ^ b)
    (hRep : ∀ u ∈ Vfl X, ∀ v ∈ Vfl X, beOp D X u v = (d : ℂ) • ∫ y : Mt k r,
      ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG)
    (hH : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ)
    (hDD : ∀ u₁ ∈ DDinf D X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0) : MinorsOn D X := by
  have hDV : ∀ u ∈ DDinf D X, u ∈ Vfl X := by
    rintro u ⟨φ, hφ, rfl⟩; exact dd_mem D X ha0 hφ
  have hT : ∀ φ : Mat k r → ℂ, IsTestG φ → sigInt D X φ X.w ∈ DDinf D X := fun φ hφ => ⟨φ, hφ, rfl⟩
  have S1 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep (hDV _ hu₂) (hDV _ hu₄) u₃ e₁ e₂ e₃ e₄
      (fun φ hφ => hDD _ (hT φ hφ) _ hu₂ _ hu₃ _ hu₄ e₁ e₂ e₃ e₄) u₁ hu₁
  have S2 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ DDinf D X, ∀ u₃ ∈ Vfl X, ∀ u₄ ∈ DDinf D X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    rw [← neg_eq_zero, ← mn_swap]
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep (hDV _ hu₂) (hDV _ hu₄) u₁ e₃ e₂ e₁ e₄
      (fun φ hφ => by
        rw [← neg_eq_zero, ← mn_swap]
        exact S1 u₁ hu₁ _ hu₂ _ (hT φ hφ) _ hu₄ e₁ e₂ e₃ e₄) u₃ hu₃
  have S3 : ∀ u₁ ∈ DDinf D X, ∀ u₂ ∈ Vfl X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ Vfl X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    rw [mn_herm D X hH hu₂ (hDV _ hu₁) hu₄ (hDV _ hu₃) e₂ e₁ e₄ e₃,
      S2 u₂ hu₂ u₁ hu₁ u₄ hu₄ u₃ hu₃ e₂ e₁ e₄ e₃, map_zero]
  have S4 : ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ Vfl X, ∀ u₃ ∈ DDinf D X, ∀ u₄ ∈ Vfl X, ∀ e₁ e₂ e₃ e₄ : Wp,
      Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep hu₂ hu₄ u₃ e₁ e₂ e₃ e₄
      (fun φ hφ => S3 _ (hT φ hφ) _ hu₂ _ hu₃ _ hu₄ e₁ e₂ e₃ e₄) u₁ hu₁
  intro u₁ hu₁ u₂ hu₂ u₃ hu₃ u₄ hu₄ e₁ e₂ e₃ e₄
  have : Mn D X u₁ u₂ u₃ u₄ e₁ e₂ e₃ e₄ = 0 := by
    rw [← neg_eq_zero, ← mn_swap]
    exact ext1 D X hGN ha0 hd hb0 hab hbe hRep hu₂ hu₄ u₁ e₃ e₂ e₁ e₄
      (fun φ hφ => by
        rw [← neg_eq_zero, ← mn_swap]
        exact S4 u₁ hu₁ u₂ hu₂ _ (hT φ hφ) u₄ hu₄ e₁ e₂ e₃ e₄) u₃ hu₃
  exact sub_eq_zero.1 this

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH
end
end

