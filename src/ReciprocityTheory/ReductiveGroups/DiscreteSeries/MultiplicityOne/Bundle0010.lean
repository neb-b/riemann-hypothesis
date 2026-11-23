module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoWA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0007

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoW
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stDichoW (h : UnitaryGroupStructuralFacts) : StDichoW := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCW, -, -, -, hHI, -, -, -, hClW, -⟩ := h.1
  intro k r Wp _ _ _ D X hD hX γ hγ
  obtain ⟨-, -, hgW, -, hth_mul, hth_th, -, -, hμgbar⟩ := stInvGroup h k r Wp D X hD hX γ hγ
  by_cases hWp : Subsingleton Wp
  · left
    intro x y x' y'
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]
  have : Nontrivial Wp := not_subsingleton_iff_nontrivial.1 hWp
  have hU : IsClosedSubgroup (UWset k r D.z) := hClW k r D.z
  have hμW := D.haarW
  have hme := MatrixSubsetMeasurability.me_val hU
  have hleft : (MatrixSubsetMeasurability.nu hU D.μW).IsMulLeftInvariant := MatrixSubsetMeasurability.nu_left hμW
  have hinvI : (MatrixSubsetMeasurability.nu hU D.μW).IsInvInvariant := MatrixSubsetMeasurability.nu_inv hHI hμW
  have hmapnu : (MatrixSubsetMeasurability.nu hU D.μW).map (fun g : MatrixSubsetMeasurability.SG hU => g.1) = D.μW := MatrixSubsetMeasurability.map_nu hμW
  have hνuniv : MatrixSubsetMeasurability.nu hU D.μW Set.univ = 1 := by
    have e := congrArg (fun m : Measure (Mt k r) => m Set.univ) hmapnu
    simp only [Measure.map_apply hme.measurable MeasurableSet.univ, Set.preimage_univ] at e
    rw [e, hD.mass]
  have hcpt : IsCompact {x : Mt k r | Matrix.of x ∈ UWset k r D.z} := hCW k r D.z D.z_mem D.T_pos
  have : CompactSpace (MatrixSubsetMeasurability.SG hU) := isCompact_iff_compactSpace.1 hcpt
  have hpos : (MatrixSubsetMeasurability.nu hU D.μW).IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact Set.univ isCompact_univ (by rw [hνuniv]; exact one_ne_zero)
  have hfin : IsFiniteMeasure (MatrixSubsetMeasurability.nu hU D.μW) := ⟨by rw [hνuniv]; exact ENNReal.one_lt_top⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : MatrixSubsetMeasurability.SG hU → MatrixSubsetMeasurability.SG hU, θ = fun g =>
      (MatrixSubsetMeasurability.mk hU (gbar k r γ (MatrixSubsetMeasurability.mat g)) (hgW _ (MatrixSubsetMeasurability.mat_mem g)))⁻¹ := ⟨_, rfl⟩
  have hmθ : ∀ g, MatrixSubsetMeasurability.mat (θ g) = th k r γ (MatrixSubsetMeasurability.mat g) := by
    intro g
    simp only [hθ]
    rw [MatrixSubsetMeasurability.mat_inv, MatrixSubsetMeasurability.mat_mk]
    rfl
  have hgc : Continuous fun A : Mat k r => gbar k r γ A := by
    have h1 : Continuous fun A : Mat k r => (embWb k r γ)⁻¹ * A := continuous_const.matrix_mul continuous_id
    have h2 : Continuous fun A : Mat k r => (embWb k r γ)⁻¹ * A * embWb k r γ := h1.matrix_mul continuous_const
    have h3 : Continuous fun A : Mat k r => ((embWb k r γ)⁻¹ * A * embWb k r γ).map (starRingEnd ℂ) :=
      h2.matrix_map Complex.continuous_conj
    have h4 : Continuous fun A : Mat k r =>
        embWb k r γ * ((embWb k r γ)⁻¹ * A * embWb k r γ).map (starRingEnd ℂ) :=
      continuous_const.matrix_mul h3
    exact h4.matrix_mul continuous_const
  have hgbc : Continuous fun g : MatrixSubsetMeasurability.SG hU =>
      MatrixSubsetMeasurability.mk hU (gbar k r γ (MatrixSubsetMeasurability.mat g)) (hgW _ (MatrixSubsetMeasurability.mat_mem g)) := by
    apply continuous_induced_rng.2
    exact hgc.comp MatrixSubsetMeasurability.continuous_mat
  have hθc : Continuous θ := by
    rw [hθ]
    exact hgbc.inv
  have hθmul : ∀ a b, θ (a * b) = θ b * θ a := by
    intro a b
    apply MatrixSubsetMeasurability.ext'
    rw [MatrixSubsetMeasurability.mat_mul, hmθ, hmθ, hmθ, MatrixSubsetMeasurability.mat_mul]
    exact hth_mul _ (MatrixSubsetMeasurability.mat_mem a).1 _ (MatrixSubsetMeasurability.mat_mem b).1
  have hθθ : ∀ g, θ (θ g) = g := by
    intro g
    apply MatrixSubsetMeasurability.ext'
    rw [hmθ, hmθ]
    exact hth_th _ (MatrixSubsetMeasurability.mat_mem g).1
  have hgF : Measurable fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j := by
    apply Continuous.measurable
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply j).comp ((continuous_apply i).comp (hgc.comp continuous_id))
  have hθμ : (MatrixSubsetMeasurability.nu hU D.μW).map θ = MatrixSubsetMeasurability.nu hU D.μW := by
    have hval : (fun g : MatrixSubsetMeasurability.SG hU => g.1) ∘ θ =
        (invM ∘ fun x : Mt k r => fun i j => gbar k r γ (Matrix.of x) i j) ∘ fun g : MatrixSubsetMeasurability.SG hU => g.1 := by
      funext g
      exact hmθ g
    have key : ((MatrixSubsetMeasurability.nu hU D.μW).map θ).map (fun g : MatrixSubsetMeasurability.SG hU => g.1) = D.μW := by
      rw [Measure.map_map hme.measurable hθc.measurable, hval,
        ← Measure.map_map (InvGrp.measurable_invM.comp hgF) hme.measurable, hmapnu,
        ← Measure.map_map InvGrp.measurable_invM hgF, hμgbar]
      exact hHI k r _ D.μW hU hμW
    rw [← hme.comap_map ((MatrixSubsetMeasurability.nu hU D.μW).map θ), key]
    rfl
  have hπc : Continuous fun g : MatrixSubsetMeasurability.SG hU => D.π (MatrixSubsetMeasurability.mat g) :=
    D.π_cont.comp_continuous MatrixSubsetMeasurability.continuous_mat fun g => MatrixSubsetMeasurability.mat_mem g
  have hρ1 : D.π (MatrixSubsetMeasurability.mat (1 : MatrixSubsetMeasurability.SG hU)) = 1 := by
    rw [MatrixSubsetMeasurability.mat_one]
    exact D.π_rep.1
  have hρmul : ∀ a b : MatrixSubsetMeasurability.SG hU,
      D.π (MatrixSubsetMeasurability.mat (a * b)) = (D.π (MatrixSubsetMeasurability.mat a)).comp (D.π (MatrixSubsetMeasurability.mat b)) := by
    intro a b
    rw [MatrixSubsetMeasurability.mat_mul]
    exact D.π_rep.2 _ (MatrixSubsetMeasurability.mat_mem a) _ (MatrixSubsetMeasurability.mat_mem b)
  have hρn : ∀ (g : MatrixSubsetMeasurability.SG hU) (v : Wp), ‖D.π (MatrixSubsetMeasurability.mat g) v‖ = ‖v‖ :=
    fun g v => D.π_unitary _ (MatrixSubsetMeasurability.mat_mem g) v
  have hρc : ∀ v : Wp, Continuous fun g : MatrixSubsetMeasurability.SG hU => D.π (MatrixSubsetMeasurability.mat g) v :=
    fun v => hπc.clm_apply continuous_const
  have hmem : ∀ v w : Wp, MemLp (fun g : MatrixSubsetMeasurability.SG hU => ⟪w, D.π (MatrixSubsetMeasurability.mat g) v⟫_ℂ) 2
      (MatrixSubsetMeasurability.nu hU D.μW) := by
    intro v w
    refine MemLp.of_bound (continuous_const.inner (hρc v)).aestronglyMeasurable (‖w‖ * ‖v‖)
      (Filter.Eventually.of_forall fun g => ?_)
    calc ‖⟪w, D.π (MatrixSubsetMeasurability.mat g) v⟫_ℂ‖ ≤ ‖w‖ * ‖D.π (MatrixSubsetMeasurability.mat g) v‖ := norm_inner_le_norm _ _
      _ = ‖w‖ * ‖v‖ := by rw [hρn]
  have hirr : ∀ S : Submodule ℂ Wp, IsClosed (S : Set Wp) →
      (∀ (g : MatrixSubsetMeasurability.SG hU), ∀ v ∈ S, D.π (MatrixSubsetMeasurability.mat g) v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS hinv
    refine hD.irr S hS fun g hg v hv => ?_
    have e := hinv (MatrixSubsetMeasurability.mk hU g hg) v hv
    rwa [MatrixSubsetMeasurability.mat_mk] at e
  rcases schurDichotomy (MatrixSubsetMeasurability.SG hU) (MatrixSubsetMeasurability.nu hU D.μW) Wp θ (fun g => D.π (MatrixSubsetMeasurability.mat g))
      hθc hθmul hθθ hθμ hρ1 hρmul hρn hρc hmem hirr with hL | ⟨C, hC1, hC2⟩
  · left
    intro x y x' y'
    rw [← hmapnu, hme.integral_map]
    have e := hL x y x' y'
    simp only [hmθ] at e
    exact e
  · right
    refine ⟨C, fun g hg x y => ?_, fun g hg v => ?_⟩
    · have e := hC1 (MatrixSubsetMeasurability.mk hU g hg) x y
      simp only [hmθ, MatrixSubsetMeasurability.mat_mk] at e
      exact e
    · have e := hC2 (MatrixSubsetMeasurability.mk hU g hg) v
      simp only [MatrixSubsetMeasurability.mat_inv, hmθ, MatrixSubsetMeasurability.mat_mk] at e
      exact e

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JMixed
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ConjugateNormInequalities MixedNormBounds

theorem stMixed (h : UnitaryGroupStructuralFacts) : StMixed := by
  obtain ⟨hB2, -, -, -, hUWb, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hInt, hLow, -, -, -, hCG, -⟩ := hB2
  intro k r Wp _ _ _ D X hD hSq γ hγ haM C hC u hu
  have hG := hCG k r
  have hEG : embWb k r γ ∈ GV k r := by
    have hmem : embWb k r γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγ.1, rfl⟩
    exact hmem.1
  have hE := hG.unit _ hEG
  obtain ⟨d, hd⟩ := stSchurG k r Wp D X hD hSq
  obtain ⟨C₁, hC₁⟩ := hu
  have hn1 : (1 : ℝ) ≤ nR k r := by simp only [nR]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have ha0 : 0 ≤ X.a := le_trans (by simp only [aM]; positivity) haM
  set b := AG k r + 1 with hb
  have hb0 : 0 ≤ b := by simp only [hb, AG]; positivity
  have hab : b ≤ X.a := by
    refine le_trans ?_ haM
    simp only [hb, AG, aM]
    nlinarith [mul_le_mul hn1 hn1 zero_le_one (by linarith), sq_nonneg (nR k r)]
  have hCw : C X.w ≠ 0 := by
    intro h0
    have h1 := C.norm_map X.w
    rw [h0, norm_zero, X.w_norm] at h1
    exact zero_ne_one h1
  obtain ⟨g₂, hg₂, hc₀⟩ := exists_inner_ne X hG (C X.w) hCw
  have hg2i : g₂⁻¹ ∈ GV k r := hG.inv_mem _ hg₂

  set K : ℝ := (gN (embWb k r γ) * gN (embWb k r γ)⁻¹) ^ 2 with hK
  have hK0 : 0 < K := by
    have h1 := hLow k r _ hEG
    have h2 := hLow k r _ (hG.inv_mem _ hEG)
    have : 1 ≤ gN (embWb k r γ) * gN (embWb k r γ)⁻¹ := by nlinarith
    simp only [hK]; positivity
  set c : ℝ := max (gN (Hpk k r) ^ 2) 1 with hc
  have hc0 : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
  set Lc : ℝ := c * gN g₂⁻¹ with hLc
  have hL0 : 0 < Lc := mul_pos hc0 (by linarith [hLow k r _ hg2i])
  set K₁ : ℝ := max C₁ 0 * K ^ X.a with hK₁
  set K₂ : ℝ := max X.Cw 0 * Lc ^ X.a with hK₂
  have hK₁0 : 0 ≤ K₁ := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hK0.le _)
  have hK₂0 : 0 ≤ K₂ := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hL0.le _)

  have f1 : ∀ y ∈ GV k r, ‖⟪C X.w, X.σ y (C u)⟫_ℂ‖ ≤ K₁ * gN y ^ (-X.a) := by
    intro y hy
    have hgb := InvGrp.gbar_mem_GV hG hEG y hy
    have e : ⟪C X.w, X.σ y (C u)⟫_ℂ = ⟪X.σ (gbar k r γ y) u, X.w⟫_ℂ := by
      rw [← hC y hy X.w u, inner_sig_left X hG hgb]
      rfl
    rw [e, norm_inner_symm]
    have hb1 : ‖⟪X.w, X.σ (gbar k r γ y) u⟫_ℂ‖ ≤ C₁ * gN (gbar k r γ y) ^ (-X.a) := hC₁ _ hgb
    have hy1 := hLow k r y hy
    have hrb := rpow_bound (by linarith) hK0 ha0 (gN_le_gbar hE y)
    calc ‖⟪X.w, X.σ (gbar k r γ y) u⟫_ℂ‖ ≤ C₁ * gN (gbar k r γ y) ^ (-X.a) := hb1
      _ ≤ max C₁ 0 * gN (gbar k r γ y) ^ (-X.a) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (gN_nonneg _) _)
      _ ≤ max C₁ 0 * (K ^ X.a * gN y ^ (-X.a)) := mul_le_mul_of_nonneg_left hrb (le_max_right _ _)
      _ = K₁ * gN y ^ (-X.a) := by rw [hK₁]; ring
  have f2 : ∀ g ∈ GV k r, ‖⟪X.σ g₂ X.w, X.σ g X.w⟫_ℂ‖ ≤ K₂ * gN g ^ (-X.a) := by
    intro g hg
    have hm := hG.mul_mem _ hg2i _ hg
    have e : ⟪X.σ g₂ X.w, X.σ g X.w⟫_ℂ = ⟪X.w, X.σ (g₂⁻¹ * g) X.w⟫_ℂ := by
      rw [inner_sig_left X hG hg₂, X.rep.1.2 _ hg2i _ hg]
      rfl
    rw [e]
    have hb1 := X.dec _ hm
    have hle : gN g ≤ Lc * gN (g₂⁻¹ * g) := by
      calc gN g ≤ gN (Hpk k r) ^ 2 * (gN g₂⁻¹ * gN (g₂⁻¹ * g)) := gN_le_mul hg2i g
        _ ≤ c * (gN g₂⁻¹ * gN (g₂⁻¹ * g)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg (gN_nonneg _) (gN_nonneg _))
        _ = Lc * gN (g₂⁻¹ * g) := by rw [hLc]; ring
    have hrb := rpow_bound (by linarith [hLow k r g hg]) hL0 ha0 hle
    calc ‖⟪X.w, X.σ (g₂⁻¹ * g) X.w⟫_ℂ‖ ≤ X.Cw * gN (g₂⁻¹ * g) ^ (-X.a) := hb1
      _ ≤ max X.Cw 0 * gN (g₂⁻¹ * g) ^ (-X.a) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (gN_nonneg _) _)
      _ ≤ max X.Cw 0 * (Lc ^ X.a * gN g ^ (-X.a)) := mul_le_mul_of_nonneg_left hrb (le_max_right _ _)
      _ = K₂ * gN g ^ (-X.a) := by rw [hK₂]; ring

  set c₀ : ℂ := ⟪C X.w, X.σ g₂ X.w⟫_ℂ with hc₀def
  set I : ℝ≥0∞ := ∫⁻ g : Mt k r, ENNReal.ofReal (gN (Matrix.of g) ^ (-b)) ∂D.μG with hI
  have hIfin : I < ∞ := hInt k r D.μG b D.haarG (AB_le_AG k r)
  refine ⟨d / ‖c₀‖ * (K₁ * K₂ * c⁻¹ ^ (-(X.a - b)) * I.toReal), fun x hx => ?_⟩
  have hexp : -(X.a - AG k r - 1) = -(X.a - b) := by rw [hb]; ring
  rw [hexp]
  have hX1 : 1 ≤ gN x := hLow k r x hx
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.1.ne'
  obtain ⟨-, hEq⟩ := hd.2 (X.σ x (C u)) (C X.w) X.w (X.σ g₂ X.w)
  have hmc : mc X (C u) X.w x = (d : ℂ) / c₀ *
      ∫ g : Mt k r, mc X (X.σ x (C u)) (C X.w) (Matrix.of g) * star (mc X X.w (X.σ g₂ X.w) (Matrix.of g)) ∂D.μG := by
    rw [hEq]
    simp only [mc, ← hc₀def]
    field_simp
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r := by
    rw [ae_iff]; exact measure_mono_null (fun g hg => hg) D.haarG.conc
  have hpt : ∀ᵐ g ∂D.μG,
      ENNReal.ofReal ‖mc X (X.σ x (C u)) (C X.w) (Matrix.of g) * star (mc X X.w (X.σ g₂ X.w) (Matrix.of g))‖ ≤
        ENNReal.ofReal (K₁ * K₂ * (gN x * c⁻¹) ^ (-(X.a - b))) * ENNReal.ofReal (gN (Matrix.of g) ^ (-b)) := by
    filter_upwards [hae] with g hg
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    set G : Mat k r := Matrix.of g
    have hGx : G * x ∈ GV k r := hG.mul_mem _ hg _ hx
    have hA := hLow k r _ hGx
    have hB := hLow k r _ hg
    have e1 : mc X (X.σ x (C u)) (C X.w) G = ⟪C X.w, X.σ (G * x) (C u)⟫_ℂ := by
      unfold mc; rw [X.rep.1.2 G hg x hx]; rfl
    have hXle : gN x ≤ c * (gN G * gN (G * x)) :=
      (gN_le_mul hg x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (mul_nonneg (gN_nonneg _) (gN_nonneg _)))
    have key := real_key hA hB (by linarith) hc0 hb0 hab hXle
    rw [e1, norm_mul, norm_star]
    calc ‖⟪C X.w, X.σ (G * x) (C u)⟫_ℂ‖ * ‖mc X X.w (X.σ g₂ X.w) G‖
        ≤ (K₁ * gN (G * x) ^ (-X.a)) * (K₂ * gN G ^ (-X.a)) :=
          mul_le_mul (f1 _ hGx) (f2 _ hg) (norm_nonneg _) (mul_nonneg hK₁0 (Real.rpow_nonneg (by linarith) _))
      _ = K₁ * K₂ * (gN (G * x) ^ (-X.a) * gN G ^ (-X.a)) := by ring
      _ ≤ K₁ * K₂ * ((gN x * c⁻¹) ^ (-(X.a - b)) * gN G ^ (-b)) :=
          mul_le_mul_of_nonneg_left key (mul_nonneg hK₁0 hK₂0)
      _ = K₁ * K₂ * (gN x * c⁻¹) ^ (-(X.a - b)) * gN G ^ (-b) := by ring
  have hnorm : ‖∫ g : Mt k r, mc X (X.σ x (C u)) (C X.w) (Matrix.of g) *
      star (mc X X.w (X.σ g₂ X.w) (Matrix.of g)) ∂D.μG‖ ≤
      (ENNReal.ofReal (K₁ * K₂ * (gN x * c⁻¹) ^ (-(X.a - b))) * I).toReal :=
    (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIfin.ne)
      ((lintegral_mono_ae hpt).trans_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)))
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hnorm
  have hc₀n : 0 < ‖c₀‖ := norm_pos_iff.2 hc₀
  calc ‖mc X (C u) X.w x‖
      = d / ‖c₀‖ * ‖∫ g : Mt k r, mc X (X.σ x (C u)) (C X.w) (Matrix.of g) *
          star (mc X X.w (X.σ g₂ X.w) (Matrix.of g)) ∂D.μG‖ := by
        rw [hmc, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hd.1.le]
    _ ≤ d / ‖c₀‖ * (K₁ * K₂ * (gN x * c⁻¹) ^ (-(X.a - b)) * I.toReal) :=
        mul_le_mul_of_nonneg_left hnorm (div_nonneg hd.1.le hc₀n.le)
    _ = d / ‖c₀‖ * (K₁ * K₂ * c⁻¹ ^ (-(X.a - b)) * I.toReal) * gN x ^ (-(X.a - b)) := by
        rw [Real.mul_rpow (gN_nonneg x) (inv_nonneg.2 hc0.le)]; ring

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRepro
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.ReproducingFormula

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem second_joint_integrable (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hCG : IsClosedSubgroup (GV k r)) (hCW : IsClosedSubgroup (UWset k r D.z)) (hCN : IsClosedSubgroup (Nset k r))
    (hL : ∀ g ∈ GV k r, 1 ≤ gN g) (ha : 0 ≤ X.a)
    (hIG : Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-(X.a / 2))) D.μG)
    (hIS : Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-(X.a / 2)))
      (D.μW.prod D.μN))
    {u v : X.Hs} (hu : u ∈ Vfl X) (hv : v ∈ Vfl X) :
    Integrable (fun q : Mt k r × (Mt k r × Mt k r) =>
      ⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of q.1) X.w) q.2) (D.μG.prod (D.μW.prod D.μN)) := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : IsFiniteMeasureOnCompacts D.μG := ⟨fun _ hK => D.haarG.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun _ hK => D.haarW.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun _ hK => D.haarN.finite_compact _ hK⟩
  obtain ⟨Cu, hCu0, hCu⟩ := dec_adj X hCG hL ha hu
  obtain ⟨Cv, hCv0, hCv⟩ := dec_adj X hCG hL ha hv
  have hform : ∀ q ∈ EE k r D.z,
      ⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of q.1) X.w) q.2 =
        ⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • ((⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ *
          star (psiD D (Matrix.of q.2.2))) • ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1))) := by
    intro q hq
    obtain ⟨_, hh, _⟩ := hq
    simp only [beInt, mc]
    rw [pi_inv D hCW hh]
  have hcont : ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) =>
      ⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of q.1) X.w) q.2) (EE k r D.z) := by
    refine ContinuousOn.congr ?_ hform
    exact (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (cont_sig_fst X D.z X.w)).smul
      (((ContinuousOn.inner (𝕜 := ℂ) (cont_sig_fst X D.z X.w) (representation_continuousOn_product X D.z hCG u)).mul
        (cont_psi D).continuousOn).smul (cont_adj_pi D))
  have hmeas : AEStronglyMeasurable (fun q : Mt k r × (Mt k r × Mt k r) =>
      ⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of q.1) X.w) q.2)
      (D.μG.prod (D.μW.prod D.μN)) := by
    have := hcont.aestronglyMeasurable (μ := D.μG.prod (D.μW.prod D.μN)) (EE_closed D.z hCG hCW hCN).measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (ae_EE D)] at this
  have hbd : ∀ᵐ q ∂(D.μG.prod (D.μW.prod D.μN)),
      ‖⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of q.1) X.w) q.2‖ ≤
        Cv * Cu * KH k r ^ (X.a / 2) * KH k r ^ (X.a / 2) *
          (gN (Matrix.of q.1) ^ (-(X.a / 2)) * gN (Matrix.of q.2.2 * Matrix.of q.2.1) ^ (-(X.a / 2))) := by
    filter_upwards [ae_EE D] with q hq
    rw [hform q hq]
    obtain ⟨hy, hh, hn⟩ := hq
    have hs : Matrix.of q.2.2 * Matrix.of q.2.1 ∈ GV k r := hCG.mul_mem _ hn.1 _ hh.1
    have hsi := inv_mem_G hCG hs
    have A1 : ‖⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ‖ ≤ Cv * gN (Matrix.of q.1) ^ (-X.a) := hCv _ hy
    have e : ⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ =
        ⟪X.σ ((Matrix.of q.2.2 * Matrix.of q.2.1)⁻¹ * Matrix.of q.1) X.w, u⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← sig_inv X hCG hs, X.rep.1.2 _ hsi _ hy]; rfl
    have A2 : ‖⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ‖ ≤
        Cu * gN ((Matrix.of q.2.2 * Matrix.of q.2.1)⁻¹ * Matrix.of q.1) ^ (-X.a) := by
      rw [e, norm_inner_symm]; exact hCu _ (hCG.mul_mem _ hsi _ hy)
    have B := second_pointwise_bound hCG hL ha hs hy A1 A2 (norm_nonneg _) (norm_nonneg _) hCv0 hCu0
    have hT : ‖ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1))‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]; exact opNorm_le_one_of_iso (D.π_unitary _ hh)
    have hψ : ‖star (psiD D (Matrix.of q.2.2))‖ ≤ 1 := by rw [norm_star]; exact norm_psi_le _ _ _
    rw [norm_smul, norm_smul, norm_mul]
    calc ‖⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ‖ *
          (‖⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ‖ *
          ‖star (psiD D (Matrix.of q.2.2))‖ * ‖ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1))‖)
        ≤ ‖⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ‖ *
          (‖⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ‖ * 1 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hψ (norm_nonneg _)) hT
            (norm_nonneg _) (by positivity)) (norm_nonneg _)
      _ = ‖⟪v, X.σ (Matrix.of q.1) X.w⟫_ℂ‖ *
          ‖⟪X.σ (Matrix.of q.1) X.w, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) u⟫_ℂ‖ := by ring
      _ ≤ _ := B
  exact ((hIG.mul_prod hIS).const_mul (Cv * Cu * KH k r ^ (X.a / 2) * KH k r ^ (X.a / 2))).mono' hmeas hbd

theorem reproducing_snd (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hCG : IsClosedSubgroup (GV k r)) (hCW : IsClosedSubgroup (UWset k r D.z)) (hCN : IsClosedSubgroup (Nset k r))
    (hL : ∀ g ∈ GV k r, 1 ≤ gN g) (ha : 0 ≤ X.a)
    (hIG : Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-(X.a / 2))) D.μG)
    (hIS : Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-(X.a / 2)))
      (D.μW.prod D.μN))
    {d : ℝ} (hd : IsFdegG D X d) {u v : X.Hs} (hu : u ∈ Vfl X) (hv : v ∈ Vfl X) :
    beOp D X u v = (d : ℂ) •
      ∫ y : Mt k r, ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • beOp D X u (X.σ (Matrix.of y) X.w) ∂D.μG := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : IsFiniteMeasureOnCompacts D.μG := ⟨fun _ hK => D.haarG.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun _ hK => D.haarW.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun _ hK => D.haarN.finite_compact _ hK⟩
  have hint := second_joint_integrable D X hCG hCW hCN hL ha hIG hIS hu hv
  have hpt : ∀ p : Mt k r × Mt k r,
      ∫ y : Mt k r, ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • beInt D X u (X.σ (Matrix.of y) X.w) p ∂D.μG =
        ((d : ℂ)⁻¹) • beInt D X u v p := by
    intro p
    simp only [beInt, smul_smul]
    rw [integral_smul_const]
    congr 1
    have e : ∀ y : Mt k r, ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ *
        (mc X u (X.σ (Matrix.of y) X.w) (Matrix.of p.2 * Matrix.of p.1) * star (psiD D (Matrix.of p.2))) =
        ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of p.2 * Matrix.of p.1) u⟫_ℂ * ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ *
          star (psiD D (Matrix.of p.2)) := by
      intro y; rw [mc]; ring
    simp_rw [e]
    rw [integral_mul_const, schur_pt D X hd v (X.σ (Matrix.of p.2 * Matrix.of p.1) u), mc]
    ring
  have hsw := swap_smul D.μG (D.μW.prod D.μN) (fun y : Mt k r => ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ)
    (fun (y : Mt k r) (p : Mt k r × Mt k r) => beInt D X u (X.σ (Matrix.of y) X.w) p) hint
  have key : ∫ y : Mt k r, ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • beOp D X u (X.σ (Matrix.of y) X.w) ∂D.μG =
      ((d : ℂ)⁻¹) • beOp D X u v := by
    simp only [beOp]
    rw [hsw]
    simp_rw [hpt]
    rw [integral_smul]
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  rw [key, smul_smul, mul_inv_cancel₀ hd0, one_smul]

end ReciprocityTheory.ChartRestriction.DS.Mult1.ReproducingFormula

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReproducingFormula

section

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem repro_setup (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (haM : aM k r ≤ X.a) :
    IsClosedSubgroup (GV k r) ∧ IsClosedSubgroup (UWset k r D.z) ∧ IsClosedSubgroup (Nset k r) ∧
      (∀ g ∈ GV k r, 1 ≤ gN g) ∧ 0 ≤ X.a ∧
      Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-(X.a / 2))) D.μG ∧
      Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-(X.a / 2)))
        (D.μW.prod D.μN) := by
  have h' := h
  obtain ⟨hB2, -⟩ := h'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hGI, hGL, -, -, -, hCG, hCN, hCW, -⟩ := hB2
  have ha : 0 ≤ X.a := le_trans (by unfold aM nR; positivity) haM
  have hAB := AB_le_half k r haM
  exact ⟨hCG k r, hCW k r D.z, hCN k r, hGL k r, ha, int_G hGI D.μG D.haarG hAB,
    stSInt h k r Wp D hD (X.a / 2) hAB⟩

end

theorem stRepro (h : UnitaryGroupStructuralFacts) : StRepro := by
  intro k r Wp _ _ _ D X hD _ haM d hd u hu v hv
  obtain ⟨hCG, hCW, hCN, hL, ha, hIG, hIS⟩ := repro_setup h D X hD haM
  exact ⟨reproducing_fst D X hCG hCW hCN hL ha hIG hIS hd hu hv, reproducing_snd D X hCG hCW hCN hL ha hIG hIS hd hu hv⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

