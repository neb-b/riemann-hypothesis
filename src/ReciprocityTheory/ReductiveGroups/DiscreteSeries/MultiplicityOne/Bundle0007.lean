module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JReproA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeConvA

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JPairs
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ConjugateNormInequalities

theorem stPairs (h : UnitaryGroupStructuralFacts) : StPairs := by
  have h' := h
  unfold UnitaryGroupStructuralFacts ReciprocityTheory.ChartRestriction.DS.Xi.InductiveHeisenbergInputs at h'
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hInt, hLow, -⟩, -⟩ := h'
  intro k r Wp _ _ _ D X _ _ d hd a₁ a₂ u hu v hv
  set a := min a₁ a₂ with ha_def
  set b := AG k r + 1 with hb_def
  have hone : (1 : Mat k r) ∈ GV k r := by
    show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  have hlow : ∀ x ∈ GV k r, 1 ≤ gN x := fun x hx => hLow k r x hx
  have hb0 : 0 ≤ b := by
    have : 0 ≤ AG k r := by unfold AG; positivity
    linarith
  by_cases hab : b ≤ a
  swap
  · refine ⟨‖u‖ * ‖v‖, fun x hx => ?_⟩
    have h1 : ‖mc X u v x‖ ≤ ‖u‖ * ‖v‖ := by
      calc ‖mc X u v x‖ = ‖⟪v, X.σ x u⟫_ℂ‖ := rfl
        _ ≤ ‖v‖ * ‖X.σ x u‖ := norm_inner_le_norm _ _
        _ = ‖u‖ * ‖v‖ := by rw [X.rep.2.1 x hx u]; ring
    have h2 : 1 ≤ gN x ^ (-(min a₁ a₂ - AG k r - 1)) := by
      apply Real.one_le_rpow (hlow x hx)
      rw [← ha_def]
      linarith
    calc ‖mc X u v x‖ ≤ ‖u‖ * ‖v‖ := h1
      _ = ‖u‖ * ‖v‖ * 1 := by ring
      _ ≤ ‖u‖ * ‖v‖ * gN x ^ (-(min a₁ a₂ - AG k r - 1)) := by gcongr
  obtain ⟨C₁, hC₁⟩ := hu
  obtain ⟨C₂, hC₂⟩ := hv
  have hpos : ∀ x ∈ GV k r, 0 < gN x := fun x hx => lt_of_lt_of_le one_pos (hlow x hx)
  have hC₁0 : 0 ≤ C₁ := by
    have h1 := hC₁ 1 hone
    have h2 := Real.rpow_pos_of_pos (hpos 1 hone) (-a₁)
    by_contra hneg'
    have hneg := lt_of_not_ge hneg'
    have : C₁ * gN (1 : Mat k r) ^ (-a₁) < 0 := mul_neg_of_neg_of_pos hneg h2
    linarith [norm_nonneg (mc X u X.w 1)]
  have hC₂0 : 0 ≤ C₂ := by
    have h1 := hC₂ 1 hone
    have h2 := Real.rpow_pos_of_pos (hpos 1 hone) (-a₂)
    by_contra hneg'
    have hneg := lt_of_not_ge hneg'
    have : C₂ * gN (1 : Mat k r) ^ (-a₂) < 0 := mul_neg_of_neg_of_pos hneg h2
    linarith [norm_nonneg (mc X v X.w 1)]
  set c := gN (Hpk k r) ^ 2 with hc_def
  have hc : 0 < c := by
    have h1 : gN (1 : Mat k r) ≤ gN (Hpk k r) * gN (Hpk k r) := by
      have := gN_mul_le (Hpk k r) (Hpk k r)
      rwa [Hpk_sq] at this
    have h2 := hlow 1 hone
    rw [hc_def]
    nlinarith
  have hmeas : Measurable (fun g : Mt k r => gN (Matrix.of g)) := by
    unfold gN
    fun_prop
  have hae : ∀ᵐ g ∂D.μG, (Matrix.of g : Mat k r) ∈ GV k r := by
    rw [ae_iff]
    exact D.haarG.conc
  have hAB : AB k r ≤ b := AB_le_AG k r
  have hfin := hInt k r D.μG b D.haarG hAB
  have hI : Integrable (fun g : Mt k r => gN (Matrix.of g) ^ (-b)) D.μG := by
    refine ⟨(hmeas.pow_const _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · exact hfin
    · exact Filter.Eventually.of_forall fun g => Real.rpow_nonneg (by unfold gN; positivity) _
  set I := ∫ g : Mt k r, gN (Matrix.of g) ^ (-b) ∂D.μG with hI_def
  refine ⟨d * (C₁ * C₂ * I * (c⁻¹) ^ (-(a - b))), fun x hx => ?_⟩
  have hd0 : 0 < d := hd.1
  obtain ⟨-, hEq⟩ := hd.2 (X.σ x u) X.w v X.w
  have hww : ⟪X.w, X.w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, X.w_norm]
    simp
  rw [hww, mul_one] at hEq
  set F : Mt k r → ℂ := fun g => mc X (X.σ x u) X.w (Matrix.of g) * star (mc X v X.w (Matrix.of g)) with hF_def
  have hmc : mc X u v x = (d : ℂ) * ∫ g, F g ∂D.μG := by
    rw [hEq]
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    change ⟪v, X.σ x u⟫_ℂ = (d : ℂ) * (⟪v, X.σ x u⟫_ℂ / (d : ℂ))
    field_simp
  set G : Mt k r → ℝ := fun g => C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * gN (Matrix.of g) ^ (-b) with hG_def
  have hGi : Integrable G D.μG := hI.const_mul _
  have hpt : ∀ᵐ g ∂D.μG, ‖F g‖ ≤ G g := by
    filter_upwards [hae] with g hg
    have hgx : Matrix.of g * x ∈ GV k r := GV_mul k r hg hx
    have hFg : ‖F g‖ = ‖mc X u X.w (Matrix.of g * x)‖ * ‖mc X v X.w (Matrix.of g)‖ := by
      rw [hF_def]
      simp only [norm_mul, norm_star]
      congr 1
      show ‖⟪X.w, X.σ (Matrix.of g) (X.σ x u)⟫_ℂ‖ = ‖⟪X.w, X.σ (Matrix.of g * x) u⟫_ℂ‖
      rw [X.rep.1.2 _ hg _ hx]
      rfl
    have hA1 := hlow _ hgx
    have hB1 := hlow _ hg
    have e1 : ‖mc X u X.w (Matrix.of g * x)‖ ≤ C₁ * gN (Matrix.of g * x) ^ (-a) := by
      refine (hC₁ _ hgx).trans ?_
      gcongr
      exact min_le_left a₁ a₂
    have e2 : ‖mc X v X.w (Matrix.of g)‖ ≤ C₂ * gN (Matrix.of g) ^ (-a) := by
      refine (hC₂ _ hg).trans ?_
      gcongr
      exact min_le_right a₁ a₂
    have key := real_key hA1 hB1 (hpos x hx) hc hb0 hab (gN_le_mul hg x)
    rw [hFg, hG_def]
    calc ‖mc X u X.w (Matrix.of g * x)‖ * ‖mc X v X.w (Matrix.of g)‖
        ≤ (C₁ * gN (Matrix.of g * x) ^ (-a)) * (C₂ * gN (Matrix.of g) ^ (-a)) :=
          mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg hC₁0 (Real.rpow_nonneg (hpos _ hgx).le _))
      _ = C₁ * C₂ * (gN (Matrix.of g * x) ^ (-a) * gN (Matrix.of g) ^ (-a)) := by ring
      _ ≤ C₁ * C₂ * ((gN x * c⁻¹) ^ (-(a - b)) * gN (Matrix.of g) ^ (-b)) := by
          gcongr
      _ = C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * gN (Matrix.of g) ^ (-b) := by ring
  have hbound : ‖∫ g, F g ∂D.μG‖ ≤ ∫ g, G g ∂D.μG :=
    (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hGi hpt)
  have hGint : ∫ g, G g ∂D.μG = C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * I := by
    rw [hG_def, integral_const_mul]
  have hsplit : (gN x * c⁻¹) ^ (-(a - b)) = gN x ^ (-(a - b)) * (c⁻¹) ^ (-(a - b)) :=
    Real.mul_rpow (hpos x hx).le (inv_nonneg.mpr hc.le)
  have hexp : -(min a₁ a₂ - AG k r - 1) = -(a - b) := by
    rw [ha_def, hb_def]; ring
  rw [hmc, norm_mul, hexp]
  have hdn : ‖(d : ℂ)‖ = d := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
  rw [hdn]
  calc d * ‖∫ g, F g ∂D.μG‖ ≤ d * (C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * I) := by
        rw [← hGint]; exact mul_le_mul_of_nonneg_left hbound hd0.le
    _ = d * (C₁ * C₂ * I * (c⁻¹) ^ (-(a - b))) * gN x ^ (-(a - b)) := by
        rw [hsplit]; ring

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JReproB
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.ReproducingFormula

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ}

theorem first_pointwise_bound (hCG : IsClosedSubgroup (GV k r)) (hL : ∀ g ∈ GV k r, 1 ≤ gN g) {a : ℝ} (ha : 0 ≤ a)
    {s y : Mat k r} (hs : s ∈ GV k r) (hy : y ∈ GV k r) {c1 c2 C1 C2 : ℝ}
    (h1 : c1 ≤ C1 * gN y ^ (-a)) (h2 : c2 ≤ C2 * gN (s * y) ^ (-a)) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) :
    c1 * c2 ≤ C1 * C2 * KH k r ^ (a / 2) * (gN y ^ (-(a / 2)) * gN s ^ (-(a / 2))) := by
  have hK := KH_pos hCG hL
  have hsy : s * y ∈ GV k r := hCG.mul_mem _ hs _ hy
  have hX : gN s ≤ KH k r * (gN y * gN (s * y)) := by
    have e : s * y * y⁻¹ = s := by rw [Matrix.mul_assoc, GV_mul_inv hy, Matrix.mul_one]
    calc gN s = gN (s * y * y⁻¹) := by rw [e]
      _ ≤ gN (s * y) * gN y⁻¹ := gN_mul_le _ _
      _ ≤ gN (s * y) * (KH k r * gN y) := mul_le_mul_of_nonneg_left (gN_inv_le hy) (gN_nonneg _)
      _ = KH k r * (gN y * gN (s * y)) := by ring
  have hkb := key_bound (hL y hy) (hL _ hsy) (hL s hs) hK ha hX
  calc c1 * c2 ≤ (C1 * gN y ^ (-a)) * (C2 * gN (s * y) ^ (-a)) :=
        mul_le_mul h1 h2 hc2 (le_trans hc1 h1)
    _ = C1 * C2 * (gN y ^ (-a) * gN (s * y) ^ (-a)) := by ring
    _ ≤ C1 * C2 * (KH k r ^ (a / 2) * (gN y ^ (-(a / 2)) * gN s ^ (-(a / 2)))) :=
        mul_le_mul_of_nonneg_left hkb (mul_nonneg hC1 hC2)
    _ = _ := by ring

theorem second_pointwise_bound (hCG : IsClosedSubgroup (GV k r)) (hL : ∀ g ∈ GV k r, 1 ≤ gN g) {a : ℝ} (ha : 0 ≤ a)
    {s y : Mat k r} (hs : s ∈ GV k r) (hy : y ∈ GV k r) {c1 c2 C1 C2 : ℝ}
    (h1 : c1 ≤ C1 * gN y ^ (-a)) (h2 : c2 ≤ C2 * gN (s⁻¹ * y) ^ (-a)) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) :
    c1 * c2 ≤ C1 * C2 * KH k r ^ (a / 2) * KH k r ^ (a / 2) * (gN y ^ (-(a / 2)) * gN s ^ (-(a / 2))) := by
  have hK := KH_pos hCG hL
  have hsi : s⁻¹ ∈ GV k r := inv_mem_G hCG hs
  have h3 := first_pointwise_bound hCG hL ha hsi hy h1 h2 hc1 hc2 hC1 hC2
  have h4 : gN s⁻¹ ^ (-(a / 2)) ≤ KH k r ^ (a / 2) * gN s ^ (-(a / 2)) :=
    rpow_inv_le (by linarith [hL s hs]) hK (by linarith) (gN_le_inv hCG hs)
  have h5 : 0 ≤ gN y ^ (-(a / 2)) := Real.rpow_nonneg (gN_nonneg _) _
  have h6 : 0 ≤ C1 * C2 * KH k r ^ (a / 2) := mul_nonneg (mul_nonneg hC1 hC2) (Real.rpow_nonneg hK.le _)
  calc c1 * c2 ≤ C1 * C2 * KH k r ^ (a / 2) * (gN y ^ (-(a / 2)) * gN s⁻¹ ^ (-(a / 2))) := h3
    _ ≤ C1 * C2 * KH k r ^ (a / 2) * (gN y ^ (-(a / 2)) * (KH k r ^ (a / 2) * gN s ^ (-(a / 2)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 h5) h6
    _ = _ := by ring

theorem int_G (hGI : GNIntSharp) (μ : Measure (Mt k r)) (hμ : IsHaarOn (GV k r) μ) {b : ℝ} (hb : AB k r ≤ b) :
    Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-b)) μ := by
  have hlt := hGI k r μ b hμ hb
  have hm : Measurable (fun y : Mt k r => gN (Matrix.of y) ^ (-b)) :=
    Measurable.pow_const (show Continuous (fun y : Mt k r => gN (Matrix.of y)) from continuous_gN).measurable _
  have := integrable_toReal_of_lintegral_ne_top hm.ennreal_ofReal.aemeasurable hlt.ne
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (gN_nonneg _) _)

def EE (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (Mt k r × (Mt k r × Mt k r)) :=
  {q | Matrix.of q.1 ∈ GV k r ∧ Matrix.of q.2.1 ∈ UWset k r z ∧ Matrix.of q.2.2 ∈ Nset k r}

theorem EE_closed (z : Fin (2 * r + k + 1) → ℂ) (hCG : IsClosedSubgroup (GV k r))
    (hCW : IsClosedSubgroup (UWset k r z)) (hCN : IsClosedSubgroup (Nset k r)) : IsClosed (EE k r z) :=
  (hCG.closed.preimage continuous_fst).inter ((hCW.closed.preimage (continuous_fst.comp continuous_snd)).inter
    (hCN.closed.preimage (continuous_snd.comp continuous_snd)))

section setting

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem ae_EE (D : RealPlaceData k r Wp Wp) :
    ∀ᵐ q ∂(D.μG.prod (D.μW.prod D.μN)), q ∈ EE k r D.z := by
  have hG : ∀ᵐ y ∂D.μG, Matrix.of y ∈ GV k r := ae_iff.2 (measure_mono_null (fun y hy => hy) D.haarG.conc)
  have hW : ∀ᵐ y ∂D.μW, Matrix.of y ∈ UWset k r D.z :=
    ae_iff.2 (measure_mono_null (fun y hy => hy) D.haarW.conc)
  have hN : ∀ᵐ y ∂D.μN, Matrix.of y ∈ Nset k r := ae_iff.2 (measure_mono_null (fun y hy => hy) D.haarN.conc)
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := D.μG) (ν := D.μW.prod D.μN)).ae hG
  have hW' := (Measure.quasiMeasurePreserving_fst (μ := D.μW) (ν := D.μN)).ae hW
  have hN' := (Measure.quasiMeasurePreserving_snd (μ := D.μW) (ν := D.μN)).ae hN
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := D.μG) (ν := D.μW.prod D.μN)).ae (hW'.and hN')
  filter_upwards [h1, h2] with q hq1 hq2
  exact ⟨hq1, hq2.1, hq2.2⟩

theorem pi_inv (D : RealPlaceData k r Wp Wp) (hCW : IsClosedSubgroup (UWset k r D.z)) {h : Mat k r}
    (hh : h ∈ UWset k r D.z) : D.π h⁻¹ = ContinuousLinearMap.adjoint (D.π h) :=
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  rep_inv_eq_adjoint D.π_rep D.π_unitary hh (hCW.inv_mem _ hh) (Matrix.mul_nonsing_inv _ (hCW.unit _ hh))

theorem cont_adj_pi (D : RealPlaceData k r Wp Wp) :
    ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) => ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1)))
      (EE k r D.z) :=
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  (ContinuousLinearMap.adjoint : (Wp →L[ℂ] Wp) ≃ₗᵢ⋆[ℂ] (Wp →L[ℂ] Wp)).continuous.comp_continuousOn
    (D.π_cont.comp (continuous_fst.comp continuous_snd).continuousOn fun q hq => hq.2.1)

theorem cont_psi (D : RealPlaceData k r Wp Wp) :
    Continuous (fun q : Mt k r × (Mt k r × Mt k r) => star (psiD D (Matrix.of q.2.2))) :=
  continuous_star.comp ((psi_cont D.z cStd).comp (continuous_snd.comp continuous_snd))

theorem cont_sig_fst (X : SigData k r) (z : Fin (2 * r + k + 1) → ℂ) (x : X.Hs) :
    ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) => X.σ (Matrix.of q.1) x) (EE k r z) :=
  (X.rep.2.2 x).comp continuous_fst.continuousOn fun q hq => hq.1

theorem representation_continuousOn_product (X : SigData k r) (z : Fin (2 * r + k + 1) → ℂ) (hCG : IsClosedSubgroup (GV k r)) (x : X.Hs) :
    ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) => X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) x) (EE k r z) := by
  have hm : Continuous (fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.2 * Matrix.of q.2.1 : Mat k r)) :=
    (continuous_snd.comp continuous_snd).matrix_mul (continuous_fst.comp continuous_snd)
  exact (X.rep.2.2 x).comp hm.continuousOn fun _ hq => hCG.mul_mem _ hq.2.2.1 _ hq.2.1.1

theorem cont_sig_sy (X : SigData k r) (z : Fin (2 * r + k + 1) → ℂ) (hCG : IsClosedSubgroup (GV k r)) (x : X.Hs) :
    ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) =>
      X.σ (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1) x) (EE k r z) := by
  have hm : Continuous (fun q : Mt k r × (Mt k r × Mt k r) =>
      (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1 : Mat k r)) :=
    ((continuous_snd.comp continuous_snd).matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul continuous_fst
  exact (X.rep.2.2 x).comp hm.continuousOn fun _ hq =>
    hCG.mul_mem _ (hCG.mul_mem _ hq.2.2.1 _ hq.2.1.1) _ hq.1

end setting

section reproducing_fst

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem first_joint_integrable (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hCG : IsClosedSubgroup (GV k r)) (hCW : IsClosedSubgroup (UWset k r D.z)) (hCN : IsClosedSubgroup (Nset k r))
    (hL : ∀ g ∈ GV k r, 1 ≤ gN g) (ha : 0 ≤ X.a)
    (hIG : Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-(X.a / 2))) D.μG)
    (hIS : Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-(X.a / 2)))
      (D.μW.prod D.μN))
    {u v : X.Hs} (hu : u ∈ Vfl X) (hv : v ∈ Vfl X) :
    Integrable (fun q : Mt k r × (Mt k r × Mt k r) =>
      ⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ • beInt D X (X.σ (Matrix.of q.1) X.w) v q.2) (D.μG.prod (D.μW.prod D.μN)) := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : IsFiniteMeasureOnCompacts D.μG := ⟨fun _ hK => D.haarG.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun _ hK => D.haarW.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun _ hK => D.haarN.finite_compact _ hK⟩
  obtain ⟨Cu, hCu0, hCu⟩ := dec_adj X hCG hL ha hu
  obtain ⟨Cv, hCv0, hCv⟩ := dec_adj X hCG hL ha hv

  have hform : ∀ q ∈ EE k r D.z,
      ⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ • beInt D X (X.σ (Matrix.of q.1) X.w) v q.2 =
        ⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ • ((⟪v, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1) X.w⟫_ℂ *
          star (psiD D (Matrix.of q.2.2))) • ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1))) := by
    intro q hq
    obtain ⟨hy, hh, hn⟩ := hq
    have hs : Matrix.of q.2.2 * Matrix.of q.2.1 ∈ GV k r := hCG.mul_mem _ hn.1 _ hh.1
    have e1 : X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) (X.σ (Matrix.of q.1) X.w) =
        X.σ (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1) X.w := by
      rw [X.rep.1.2 _ hs _ hy]; rfl
    simp only [beInt, mc]
    rw [e1, pi_inv D hCW hh]
  have hcont : ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) =>
      ⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ • beInt D X (X.σ (Matrix.of q.1) X.w) v q.2) (EE k r D.z) := by
    refine ContinuousOn.congr ?_ hform
    exact (ContinuousOn.inner (𝕜 := ℂ) (cont_sig_fst X D.z X.w) continuousOn_const).smul
      (((ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (cont_sig_sy X D.z hCG X.w)).mul
        (cont_psi D).continuousOn).smul (cont_adj_pi D))
  have hmeas : AEStronglyMeasurable (fun q : Mt k r × (Mt k r × Mt k r) =>
      ⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ • beInt D X (X.σ (Matrix.of q.1) X.w) v q.2)
      (D.μG.prod (D.μW.prod D.μN)) := by
    have := hcont.aestronglyMeasurable (μ := D.μG.prod (D.μW.prod D.μN)) (EE_closed D.z hCG hCW hCN).measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (ae_EE D)] at this
  have hbd : ∀ᵐ q ∂(D.μG.prod (D.μW.prod D.μN)),
      ‖⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ • beInt D X (X.σ (Matrix.of q.1) X.w) v q.2‖ ≤
        Cu * Cv * KH k r ^ (X.a / 2) *
          (gN (Matrix.of q.1) ^ (-(X.a / 2)) * gN (Matrix.of q.2.2 * Matrix.of q.2.1) ^ (-(X.a / 2))) := by
    filter_upwards [ae_EE D] with q hq
    rw [hform q hq]
    obtain ⟨hy, hh, hn⟩ := hq
    have hs : Matrix.of q.2.2 * Matrix.of q.2.1 ∈ GV k r := hCG.mul_mem _ hn.1 _ hh.1
    have A1 : ‖⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ‖ ≤ Cu * gN (Matrix.of q.1) ^ (-X.a) := by
      rw [norm_inner_symm]; exact hCu _ hy
    have A2 : ‖⟪v, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1) X.w⟫_ℂ‖ ≤
        Cv * gN (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1) ^ (-X.a) :=
      hCv _ (hCG.mul_mem _ hs _ hy)
    have B := first_pointwise_bound hCG hL ha hs hy A1 A2 (norm_nonneg _) (norm_nonneg _) hCu0 hCv0
    have hT : ‖ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1))‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]; exact opNorm_le_one_of_iso (D.π_unitary _ hh)
    have hψ : ‖star (psiD D (Matrix.of q.2.2))‖ ≤ 1 := by rw [norm_star]; exact norm_psi_le _ _ _
    rw [norm_smul, norm_smul, norm_mul]
    calc ‖⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ‖ * (‖⟪v, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1) X.w⟫_ℂ‖ *
          ‖star (psiD D (Matrix.of q.2.2))‖ * ‖ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1))‖)
        ≤ ‖⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ‖ *
          (‖⟪v, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1) X.w⟫_ℂ‖ * 1 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hψ (norm_nonneg _)) hT
            (norm_nonneg _) (by positivity)) (norm_nonneg _)
      _ = ‖⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ‖ *
          ‖⟪v, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1) X.w⟫_ℂ‖ := by ring
      _ ≤ _ := B
  exact ((hIG.mul_prod hIS).const_mul (Cu * Cv * KH k r ^ (X.a / 2))).mono' hmeas hbd

theorem reproducing_fst (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hCG : IsClosedSubgroup (GV k r)) (hCW : IsClosedSubgroup (UWset k r D.z)) (hCN : IsClosedSubgroup (Nset k r))
    (hL : ∀ g ∈ GV k r, 1 ≤ gN g) (ha : 0 ≤ X.a)
    (hIG : Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-(X.a / 2))) D.μG)
    (hIS : Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-(X.a / 2)))
      (D.μW.prod D.μN))
    {d : ℝ} (hd : IsFdegG D X d) {u v : X.Hs} (hu : u ∈ Vfl X) (hv : v ∈ Vfl X) :
    beOp D X u v = (d : ℂ) •
      ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : IsFiniteMeasureOnCompacts D.μG := ⟨fun _ hK => D.haarG.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun _ hK => D.haarW.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun _ hK => D.haarN.finite_compact _ hK⟩
  have hint := first_joint_integrable D X hCG hCW hCN hL ha hIG hIS hu hv
  have hpt : ∀ p : Mt k r × Mt k r,
      ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beInt D X (X.σ (Matrix.of y) X.w) v p ∂D.μG =
        ((d : ℂ)⁻¹) • beInt D X u v p := by
    intro p
    simp only [beInt, smul_smul]
    rw [integral_smul_const]
    congr 1
    have e : ∀ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
        (mc X (X.σ (Matrix.of y) X.w) v (Matrix.of p.2 * Matrix.of p.1) * star (psiD D (Matrix.of p.2))) =
        ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
          ⟪ContinuousLinearMap.adjoint (X.σ (Matrix.of p.2 * Matrix.of p.1)) v, X.σ (Matrix.of y) X.w⟫_ℂ *
          star (psiD D (Matrix.of p.2)) := by
      intro y; rw [mc, ContinuousLinearMap.adjoint_inner_left]; ring
    simp_rw [e]
    rw [integral_mul_const, schur_pt D X hd, ContinuousLinearMap.adjoint_inner_left, mc]
    ring
  have hsw := swap_smul D.μG (D.μW.prod D.μN) (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ)
    (fun (y : Mt k r) (p : Mt k r × Mt k r) => beInt D X (X.σ (Matrix.of y) X.w) v p) hint
  have key : ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG =
      ((d : ℂ)⁻¹) • beOp D X u v := by
    simp only [beOp]
    rw [hsw]
    simp_rw [hpt]
    rw [integral_smul]
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  rw [key, smul_smul, mul_inv_cancel₀ hd0, one_smul]

end reproducing_fst

end ReciprocityTheory.ChartRestriction.DS.Mult1.ReproducingFormula
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StCut1p
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def StCut0 : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), ∀ g ∈ GV k r, ∀ v ∈ DDinf D X, X.σ g v ∈ DDinf D X

def StCut1p : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (A : ℝ) (m : ℕ) (f : Mat k r → ℂ) (X₀ : Wp →L[ℂ] Wp), InCC A m f → InCC A m (fun g => f g • X₀)

def StCut1 : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → ∀ d : ℝ, IsFdegG D X d →
    ∀ (f : Mat k r → ℂ) (x y a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp), (∀ g ∈ GV k r, f g = mc X x y g) →
    ∀ p : SS k r, D.inSS p →
      Ph D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀) p =
        hsInner ((D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹)) X₀ *
          (mc X x a₂ (Matrix.of p.2.2 * Matrix.of p.2.1) *
            star (mc X y b₂ (Matrix.of p.1.2 * Matrix.of p.1.1))) / (d : ℂ)

def StCut2 : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → ∀ d : ℝ, IsFdegG D X d →
    ∀ (f : Mat k r → ℂ) (x y a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp), (∀ g ∈ GV k r, f g = mc X x y g) →
    Integrable (beInt D X x a₂) (D.μW.prod D.μN) → Integrable (beInt D X y b₂) (D.μW.prod D.μN) →
      Integrable (Ph D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀)) D.μSS ∧
      ∫ p, xiTau D (1, 1) p * Ph D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀) p ∂D.μSS =
        hsInner ((ContinuousLinearMap.adjoint (beOp D X y b₂)).comp (beOp D X x a₂)) X₀ / (d : ℂ)

def StCut4 : Prop :=
  StSchurW →
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp), IsDiag D → ∀ (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (P₁ Q P₂ Q₂ : Wp →L[ℂ] Wp),
    (∀ h ∈ UWset k r D.z, (ContinuousLinearMap.adjoint P₁).comp ((D.π h).comp Q) =
      (ContinuousLinearMap.adjoint P₂).comp ((D.π (th k r γ h)).comp Q₂)) →
    ((∀ x y x' y' : Wp, ∫ h : Mt k r, ⟪y, D.π (th k r γ (Matrix.of h)) x⟫_ℂ *
        star ⟪y', D.π (Matrix.of h) x'⟫_ℂ ∂D.μW = 0) →
      ∀ x y ξ η : Wp, ⟪η, Q x⟫_ℂ * ⟪P₁ y, ξ⟫_ℂ = 0) ∧
    (∀ C₀ : Wp ≃ₗᵢ⋆[ℂ] Wp,
      (∀ h ∈ UWset k r D.z, ∀ x y : Wp, ⟪y, D.π (th k r γ h) x⟫_ℂ = ⟪C₀ x, D.π h (C₀ y)⟫_ℂ) →
      ∀ x y ξ η : Wp, ⟪η, Q x⟫_ℂ * ⟪P₁ y, ξ⟫_ℂ = ⟪η, C₀ (P₂ y)⟫_ℂ * ⟪C₀ (Q₂ x), ξ⟫_ℂ)

def StCut3 : Prop :=
  StInvGroup →
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    (∀ x y x' y' : X.Hs,
      ∫ g : Mt k r, ⟪y, X.σ (th k r γ (Matrix.of g)) x⟫_ℂ * star ⟪y', X.σ (Matrix.of g) x'⟫_ℂ ∂D.μG = 0) →
    ∀ (a₁ b₁ a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp) (p : SS k r), D.inSS p →
      Ph D (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) (fun g => mc X a₂ b₂ g • X₀) p = 0

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSInt
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stSInt (h : UnitaryGroupStructuralFacts) : StSInt := by
  intro k r Wp _ _ _ D hD b hb
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGL, -, -, -, hCG, -⟩, -⟩ := id h
  have sW := bc_isHaarOn_sigmaFinite D.haarW
  have sN := bc_isHaarOn_sigmaFinite D.haarN
  have hfin := bc_lintegral_S_pow_AB h D (by rw [hD.μW_eq])
  have hAB1 : 1 ≤ AB k r := by
    rw [AB]; have := Nat.cast_nonneg (α := ℝ) k; have := Nat.cast_nonneg (α := ℝ) r; nlinarith
  have hmeas : Measurable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) :=
    ((bc_gN_cont_mt.comp (bc_continuous_mulM.comp continuous_swap)).measurable).pow_const _
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => Real.rpow_nonneg (bc_gN_nonneg _) _)]
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hfin
  have aeS : ∀ᵐ p1 ∂(D.μW.prod D.μN), (Matrix.of p1.1 : Mat k r) ∈ UWset k r D.z ∧
      (Matrix.of p1.2 : Mat k r) ∈ Nset k r :=
    bc_ae_prod_and (bc_isHaarOn_ae_mem D.haarW) (bc_isHaarOn_ae_mem D.haarN)
  filter_upwards [aeS] with p hp
  have hG : (Matrix.of p.2 : Mat k r) * Matrix.of p.1 ∈ GV k r := (hCG k r).mul_mem _ hp.2.1 _ hp.1.1
  change ENNReal.ofReal (gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) ≤
    ENNReal.ofReal (gN (Matrix.of p.2 * Matrix.of p.1) ^ (-AB k r))
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (hGL k r _ hG) (by linarith))

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

