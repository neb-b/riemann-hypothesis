module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0170
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0172
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportHer
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0065
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfChoices
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermZeroRight
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem hpk_mulVec (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ x) i = if i.val < r ∨ r + k < i.val then x ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -x i else x i := by
  rw [mulVec, dotProduct]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · have : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1 := by
        unfold Hpk
        rcases h with h | h
        · rw [if_pos ⟨h, by simp; omega⟩]
        · rw [if_neg (by simp; omega), if_pos ⟨by simp; omega, by simp; omega⟩]
      rw [this, one_mul]
    · intro j _ hj
      have : Hpk k r i j = 0 := by
        unfold Hpk
        have hj' : j.val ≠ 2 * r + k - i.val := fun e => hj (Fin.ext (by simpa using e))
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [this, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · rw [if_neg h, Finset.sum_eq_single i]
    · unfold Hpk
      rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩]
      split_ifs <;> ring
    · intro j _ hj
      have : Hpk k r i j = 0 := by
        unfold Hpk
        rw [if_neg (by omega), if_neg (by omega), if_neg (fun e => hj e.2.2.symm)]
      rw [this, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'

theorem hpk_symm' : (Hpk k r)ᵀ = Hpk k r := by
  ext i j
  simp only [transpose_apply, Hpk]
  by_cases h1 : j.val < r ∧ j.val + i.val = 2 * r + k
  · rw [if_pos h1]
    by_cases h2 : i.val < r ∧ i.val + j.val = 2 * r + k
    · rw [if_pos h2]
    · rw [if_neg h2, if_pos ⟨h1.1, by omega⟩]
  · rw [if_neg h1]
    by_cases h2 : i.val < r ∧ j.val + i.val = 2 * r + k
    · rw [if_pos h2, if_pos ⟨h2.1, by omega⟩]
    · rw [if_neg h2]
      by_cases h3 : i.val < r ∧ i.val + j.val = 2 * r + k
      · exact absurd ⟨h3.1, by omega⟩ h2
      · by_cases h4 : j.val < r ∧ i.val + j.val = 2 * r + k
        · exact absurd ⟨h4.1, by omega⟩ h1
        · rw [if_neg h3, if_neg h4]
          by_cases h5 : i = j
          · subst h5; rfl
          · rw [if_neg (fun e => h5 e.2.2.symm), if_neg (fun e => h5 e.2.2)]

theorem hpk_conjT : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, ← transpose_apply (Hpk k r) j i, hpk_symm']
  unfold Hpk
  split_ifs <;> simp

theorem herm_eq (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = ∑ i, star (y i) * (Hpk k r *ᵥ x) i := rfl

theorem herm_add_left (x x' y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (x + x') y = herm (Hpk k r) x y + herm (Hpk k r) x' y := by
  simp only [herm, mulVec_add, dotProduct_add]

theorem herm_smul_left (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (c • x) y = c * herm (Hpk k r) x y := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_sub_left (x x' y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (x - x') y = herm (Hpk k r) x y - herm (Hpk k r) x' y := by
  simp only [herm, mulVec_sub, dotProduct_sub]

theorem herm_add_right (x y y' : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (y + y') = herm (Hpk k r) x y + herm (Hpk k r) x y' := by
  simp only [herm, star_add, add_dotProduct]

theorem herm_smul_right (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (c • y) = star c * herm (Hpk k r) x y := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

theorem herm_zero_left (y : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) 0 y = 0 := by
  simp [herm]

theorem herm_zero_right (x : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) x 0 = 0 := by
  simp [herm]

theorem herm_swap (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = star (herm (Hpk k r) y x) := by
  simp only [herm]
  rw [star_dotProduct, star_mulVec, hpk_conjT, dotProduct_mulVec]

theorem herm_skew {ξ : B.Mat k r} (hξ : B.inLie k r ξ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (ξ *ᵥ x) y = -herm (Hpk k r) x (ξ *ᵥ y) := by
  have h : ξᴴ * Hpk k r = -(Hpk k r * ξ) := eq_neg_of_add_eq_zero_left hξ
  simp only [herm]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h, neg_mulVec, dotProduct_neg, neg_neg]

theorem trace_xuv (ξ : B.Mat k r) (u v : Fin (2 * r + k + 1) → ℂ) :
    Matrix.trace (ξ * Xuv k r u v) = herm (Hpk k r) (ξ *ᵥ u) v - herm (Hpk k r) (ξ *ᵥ v) u := by
  have key : ∀ a b : Fin (2 * r + k + 1) → ℂ,
      Matrix.trace (ξ * vecMulVec a (star (Hpk k r *ᵥ b))) = herm (Hpk k r) (ξ *ᵥ a) b := by
    intro a b
    have hb : star (Hpk k r *ᵥ b) = star b ᵥ* Hpk k r := by
      rw [star_mulVec, hpk_conjT]
    rw [hb, herm, dotProduct_mulVec]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [Xuv, Matrix.mul_sub, Matrix.trace_sub, key, key]

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentRankOne
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem asm_contOn_of_ckOn {r : ℕ} {m : ℕ∞} {F : B.Mat k r → E} (hF : B.CkOn m (B.GV k r) F) :
    ContinuousOn F (B.GV k r) := by
  intro g₀ hg₀
  obtain ⟨W0, F', hU, hgU, hF', hag⟩ := hF g₀ hg₀
  have hc : ContinuousAt F' g₀ := (hF'.continuousOn).continuousAt (hU.mem_nhds hgU)
  refine (hc.continuousWithinAt (s := B.GV k r)).congr_of_eventuallyEq ?_ (hag g₀ hgU hg₀)
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g hgU' hgG
  exact hag g hgU' hgG

theorem asm_star_cpt (j ρ : ℕ) (F : B.Mat k (j + ρ) → E) (hFc : B.CkOn ⊤ (B.GV k (j + ρ)) F)
    (R : ℝ) (hR : ∀ g ∈ B.GV k (j + ρ), F g ≠ 0 → B.gN g ≤ R) (χD : ℂ → ℂ) (hχ : U.IsCutC χD) (A₁ : ℝ)
    (hA₁ : 0 ≤ A₁) :
    ∃ B₁, U.Star k j ρ (fun g => χD (U.DjU k j ρ g) • F g) A₁ 0 B₁ ((fun w : ℂ => ‖w‖) '' tsupport χD) := by
  have hχc : Continuous χD := hχ.1.continuous
  have hDc := Formalism.FourierDecayAlt.P.JCTx6.Pos.cont_DjU k j ρ
  obtain ⟨Cχ, hCχ⟩ := hχc.bounded_above_of_compact_support hχ.2.1
  have hKc : IsCompact (B.GV k (j + ρ) ∩ {g : B.Mat k (j + ρ) | B.gN g ≤ R}) :=
    (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k (j + ρ) R).inter_left (Formalism.FourierDecayAlt.P.unitary_group_closed k (j + ρ)).closed
  obtain ⟨CF, hCF⟩ := hKc.exists_bound_of_continuousOn ((asm_contOn_of_ckOn hFc).mono Set.inter_subset_left)
  refine ⟨(max R 0) ^ A₁ * (max Cχ 0 * max CF 0), ⟨?_, ?_, ?_⟩⟩
  · intro g₀ hg₀
    obtain ⟨W0, F', hU, hgU, hF', hag⟩ := hFc g₀ hg₀
    refine ⟨W0, fun g => χD (U.DjU k j ρ g) • F' g, hU, hgU, ?_, fun g hg hgG => by simp only [hag g hg hgG]⟩
    exact contDiffOn_zero.2 ((hχc.comp hDc).continuousOn.smul (hF'.continuousOn))
  · intro g _ hne
    refine ⟨U.DjU k j ρ g, subset_tsupport _ (fun h0 => hne ?_), rfl⟩
    simp only [h0, zero_smul]
  · intro u v hu hv hl g hg
    have hu0 : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hv0 : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu0 hv0
    show B.gN g ^ A₁ * ‖χD (U.DjU k j ρ g) • F g‖ ≤ _
    by_cases h0 : F g = 0
    · rw [h0, smul_zero, norm_zero, mul_zero]
      exact mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
    · have hgR := hR g hg h0
      have hg0 : 0 ≤ B.gN g := Real.sqrt_nonneg _
      refine mul_le_mul (Real.rpow_le_rpow hg0 (hgR.trans (le_max_left _ _)) hA₁) ?_ (norm_nonneg _)
        (Real.rpow_nonneg (le_max_right _ _) _)
      rw [norm_smul]
      exact mul_le_mul ((hCχ _).trans (le_max_left _ _)) ((hCF g ⟨hg, hgR⟩).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)

theorem asm_gInt_int (ph ρ : ℕ) (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ) (hd : ∀ i, d i ≠ 0) (ht : t ≠ 0)
    (z z' : Fin (2 * (ph + (0 + 1) + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + (0 + 1) + ρ) → E)
    (hFc : B.CkOn ⊤ (B.GV k (ph + (0 + 1) + ρ)) F) (R : ℝ)
    (hR : ∀ g ∈ B.GV k (ph + (0 + 1) + ρ), F g ≠ 0 → B.gN g ≤ R) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ) :
    Integrable (Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' F γ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ) := by
  have hw : (G.wMat (0 + 1)).det ≠ 0 := Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero (0 + 1)
  set c₀ : ℂ := (U.hMat σ d).det * (t ^ (0 + 1) * (G.wMat (0 + 1)).det) with hc₀def
  have hc₀ : c₀ ≠ 0 := mul_ne_zero (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd) (mul_ne_zero (pow_ne_zero _ ht) hw)
  obtain ⟨χD, hχD, hχD1, hχDs⟩ := Formalism.FourierDecayAlt.P.JCTx6.Pos.bump_exists hc₀
  have hR0 : (0 : ℝ) ≤ ((ph + (0 + 1) + ρ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA₁ : (0 : ℝ) ≤ 8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1) *
      (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) + 1) := by positivity
  obtain ⟨B₁, hStar⟩ := asm_star_cpt (ph + (0 + 1)) ρ F hFc R hR χD hχD _ hA₁
  have hK : IsCompact ((fun w : ℂ => ‖w‖) '' tsupport χD) := hχD.2.1.isCompact.image continuous_norm
  have hK0 : (fun w : ℂ => ‖w‖) '' tsupport χD ⊆ Set.Ioi 0 := by
    rintro _ ⟨w, hw', rfl⟩
    have := norm_pos_iff.mpr hc₀
    exact lt_of_lt_of_le (by positivity) (hχDs w hw').1
  have hthr : 2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) <
      8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1) *
        (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) + 1) /
        (8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1)) := by
    rw [mul_div_cancel_left₀ _ (by positivity)]
    linarith
  have h1 := Formalism.FourierDecayAlt.P.JCTx6.Int.intG k ph 0 ρ σ d t hd ht _ hK hK0 0 _ hthr z z' E _ B₁ hStar γ hγ
  have e : Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' F γ =
      Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' (fun g => χD (U.DjU k (ph + (0 + 1)) ρ g) • F g) γ := by
    funext y
    have hdet : G.detM (Matrix.of.symm (t • G.wMat (0 + 1) * G.upper y.2.2)) = t ^ (0 + 1) * (G.wMat (0 + 1)).det :=
      Formalism.FourierDecayAlt.P.JCTx6.Pos.detM_Zv 0 t y.2.2
    have hD : U.DjU k (ph + (0 + 1)) ρ (U.gaXi (p := ph) (s := 0 + 1) k ρ σ d (y.1, y.2.1)
        (Matrix.of.symm (t • G.wMat (0 + 1) * G.upper y.2.2)) γ) = c₀ := by
      rw [Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice, hdet]
    simp only [Formalism.FourierDecayAlt.P.JCTx6.gInt]
    rw [hD, hχD1 c₀ (by rw [dist_self]; positivity), one_smul]
  rw [e]; exact h1

theorem integrable_unipotent_rank_one (ph ρ : ℕ) (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (c : ℂ)
    (z z' : Fin (2 * (ph + 1 + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + 1 + ρ) → E) (γ : B.Mat k ρ)
    (h : Integrable (Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d c z z' F γ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ)) :
    Integrable (fun ξ : U.Xi k ph 1 ρ σ => U.psiStar k ρ σ z z' ξ • F (U.gaXi k ρ σ d ξ (fun _ _ => c) γ))
      (U.muXi k ph 1 ρ σ) := by
  have hE : IsEmpty (G.UT (0 + 1)) := ⟨fun q => by have h := q.2; rw [Fin.lt_def] at h; omega⟩
  let v₀ : G.UT (0 + 1) → ℂ := fun q => isEmptyElim q
  have hvol : (volume : Measure (G.UT (0 + 1) → ℂ)) = Measure.dirac v₀ := by
    rw [volume_pi]; exact Measure.pi_of_empty _ _
  have a1 : SigmaFinite (volume : Measure (Fin (0 + 1) → Fin ph → ℂ)) := inferInstance
  have a2 : SigmaFinite (volume : Measure (Fin ph → Fin (0 + 1) → ℂ)) := inferInstance
  have a3 : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  have a4 : SigmaFinite (volume : Measure (G.UT ph → ℂ)) := inferInstance
  have b1 : SigmaFinite (volume : Measure ((Fin (0 + 1) → Fin ph → ℂ) × (Fin ph → Fin (0 + 1) → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have b2 : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT ph → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have b3 : SigmaFinite (volume : Measure (U.XiH ph (0 + 1) σ)) := by
    haveI := b1; haveI := b2
    rw [Measure.volume_eq_prod]; infer_instance
  have b4 : SigmaFinite (U.muXiH ph (0 + 1) σ) := by unfold U.muXiH; exact b3
  have hg : MeasurePreserving (fun b : U.XiH ph (0 + 1) σ => (b, v₀)) volume
      ((volume : Measure (U.XiH ph (0 + 1) σ)).prod (volume : Measure (G.UT (0 + 1) → ℂ))) := by
    rw [hvol]
    exact ⟨measurable_id.prodMk measurable_const, (Measure.prod_dirac _).symm⟩
  have := Formalism.FourierDecayAlt.P.Dx2.SL.sigma_RC k (ph + (0 + 1)) ρ
  have hφ : MeasurePreserving (Prod.map (id : U.RC k (ph + (0 + 1)) ρ × U.RC k (ph + (0 + 1)) ρ → _)
      (fun b : U.XiH ph (0 + 1) σ => (b, v₀))) (U.muXi k ph 1 ρ σ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ) :=
    (MeasurePreserving.id _).prod hg
  have h2 := (hφ.integrable_comp h.aestronglyMeasurable).2 h
  refine h2.congr (ae_of_all _ fun ξ => ?_)
  have hs : G.superSum (G.upper v₀) = 0 := by simp [G.superSum]
  have hZ : (Matrix.of.symm (c • G.wMat (0 + 1) * G.upper v₀) : G.Mat (0 + 1)) = fun _ _ => c := by
    funext i j
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp)
    have hj : j = 0 := Fin.ext (by have := j.isLt; simp)
    subst hi hj
    simp [G.wMat, G.upper, G.strictUpper, Matrix.mul_apply]
  simp only [Function.comp_apply, Prod.map, id, Formalism.FourierDecayAlt.P.JCTx6.gInt, hs, hZ]
  simp [G.psi]

end Formalism.FourierDecayAlt.P.PBH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSquareIntegrableOfTransport
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Shift

def shIdx {r : ℕ} (i : Fin (r + 1)) : {l : Fin (r - i) // (0 : Fin (r - i + 1)).val ≤ l.val} ≃ {l : Fin r // i.val ≤ l.val} where
  toFun l := ⟨⟨l.1.val + i.val, by have := l.1.isLt; have := i.isLt; omega⟩, Nat.le_add_left _ _⟩
  invFun l := ⟨⟨l.1.val - i.val, by have := l.1.isLt; have := l.2; omega⟩, Nat.zero_le _⟩
  left_inv l := by
    apply Subtype.ext; apply Fin.ext
    show l.1.val + i.val - i.val = l.1.val
    omega
  right_inv l := by
    apply Subtype.ext; apply Fin.ext
    show l.1.val - i.val + i.val = l.1.val
    have := l.2; omega

def shEq {r : ℕ} (i : Fin (r + 1)) : Cf (r - i) 0 ≃ᵐ Cf r i :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (shIdx i)

theorem shEq_mp {r : ℕ} (i : Fin (r + 1)) : MeasurePreserving (shEq i) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ => ℂ) (shIdx i)

theorem shEq_apply {r : ℕ} (i : Fin (r + 1)) (c' : Cf (r - i) 0) (l : {l : Fin r // i.val ≤ l.val}) :
    shEq i c' l = c' ((shIdx i).symm l) := by
  unfold shEq
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rfl

theorem shiftCf_glue {r : ℕ} (i : Fin (r + 1)) (c'' : Fin (r - i) → ℂ) (c' : Cf (r - i) 0) :
    Formalism.FourierDecayAlt.P.PTie.shiftCf i (glue 0 c'' c') = shEq i c' := by
  funext l
  rw [shEq_apply]
  simp [Formalism.FourierDecayAlt.P.PTie.shiftCf, shIdx]
  rfl

theorem wtI_shEq {r : ℕ} (i : Fin (r + 1)) (c' : Cf (r - i) 0) : wtI i (shEq i c') = wtI 0 c' := by
  unfold wtI
  congr 1
  simp_rw [shEq_apply]
  exact Fintype.prod_equiv (shIdx i).symm _ _ fun l => rfl

end Shift

section Transfer

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem level_square_integrable_of_transport {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : Measure (Mt k r)) (i : Fin (r + 1)) (c : Fin r → ℂ)
    {zi zi' : Fin (2 * (r - i) + k + 1) → ℂ} {πi : Mx k (r - i) → (Wp →L[ℂ] Wp)} {πi' : Mx k (r - i) → (Wq →L[ℂ] Wq)}
    (μi : Measure (Mt k (r - i))) (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - i) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i c'')))
    (v : RadSp k r z z' π π') (c'' : Fin (r - i) → ℂ) (h : LevelSquareIntegrable μi 0 (T v) c'') : LevelSquareIntegrable μ i v c := by
  unfold LevelSquareIntegrable at h ⊢
  have e : (fun c' : Cf r i => wtI i c' * pairAt μ v v (glue i c c')) ∘ (shEq i) =
      fun c' => (κ : ℂ)⁻¹ * (wtI 0 c' * pairAt μi (T v) (T v) (glue 0 c'' c')) := by
    funext c'
    simp only [Function.comp_apply]
    rw [hT, shiftCf_glue, wtI_shEq]
    have : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    field_simp
  have h2 := h.const_mul ((κ : ℂ)⁻¹)
  rw [← e] at h2
  exact ((shEq_mp i).integrable_comp_emb (shEq i).measurableEmbedding).mp h2

end Transfer

section Lev

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem act_tr {k r k' r' : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} {zi zi' : Fin (2 * r' + k' + 1) → ℂ} {πi : Mx k' r' → (Wp →L[ℂ] Wp)}
    {πi' : Mx k' r' → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k' r' zi zi' πi πi') {M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))}
    {M' : SlopeTestRemainingChoices S (Pr (RadSp k' r' zi zi' πi πi'))} (h : Formalism.FourierDecayAlt.P.PBH.ARel T M M')
    (x : Ix S → RadSp k r z z' π π') (a : Ix S) : T (act M x a) = act M' (fun b => T (x b)) a := by
  unfold act
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := congrArg (fun f => f (x b)) (h a b).1
  simpa using this.symm

end Lev

end Formalism.FourierDecayAlt.P5.HerD
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftDegreeLemmas
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section nice

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def NV {S : Type} (Bs : B.RealPlaceData k ρ Wp Wq) (ε : ℝ) (x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ e, JC.NiceCoef Bs ε (x e)

variable {S : Type} {Bs : B.RealPlaceData k ρ Wp Wq} {ε : ℝ}

theorem nv_zero : NV (S := S) Bs ε 0 := fun _ => JCx2.mn_nice_zero

theorem nv_add {x y : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : NV Bs ε x) (hy : NV Bs ε y) : NV Bs ε (x + y) :=
  fun e => JCx2.mn_nice_add (hx e) (hy e)

theorem nv_smul (c : ℂ) {x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : NV Bs ε x) : NV Bs ε (c • x) :=
  fun e => JCx2.mn_nice_smul c (hx e)

theorem nice_mono {F : B.Mat k ρ → (Wq →L[ℂ] Wp)} {ε ε' : ℝ} (h : JC.NiceCoef Bs ε F) (h' : ε' ≤ ε) :
    JC.NiceCoef Bs ε' F :=
  ⟨h.1, h.2.1, fun g hg hne => h'.trans (h.2.2 g hg hne)⟩

theorem nv_mono {x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} {ε ε' : ℝ} (h : NV Bs ε x) (h' : ε' ≤ ε) : NV Bs ε' x :=
  fun e => nice_mono (h e) h'

theorem nice_of_cpt {F : B.Mat k ρ → (Wq →L[ℂ] Wp)} (h : KB.CptCoef Bs F) : ∃ ε, 0 < ε ∧ JC.NiceCoef Bs ε F := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := h
  refine ⟨ε, hε, hs, fun A m => JFxG.cptInCC_G hs (PBE.isCompact_gN_le k ρ R) (fun g hg hgC => ?_) A m, hG⟩
  by_contra h0
  exact hgC (hR g hg h0)

end nice

section forms

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem nv_common {α S : Type} {k ρ : ℕ} {Bs : B.RealPlaceData k ρ Wp Wq} (Y : Finset α)
    (u : α → Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) (h : ∀ a ∈ Y, ∃ ε, 0 < ε ∧ NV Bs ε (u a)) :
    ∃ ε, 0 < ε ∧ ∀ a ∈ Y, NV Bs ε (u a) := by
  obtain ⟨ε, hε, hall⟩ := common_eps (ι := Y) (fun a ε => NV Bs ε (u a)) (fun a ε ε' h h0 h' => nv_mono h h')
    (fun a => h a a.2)
  exact ⟨ε, hε, fun a ha => hall ⟨a, ha⟩⟩

theorem slv_nv (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F) (j : ℕ)
    (hj : j ≤ P.r) (w : List C.Letter) (a : C.LPt) (ha : D.IsLocPt a j) :
    ∃ ε, 0 < ε ∧ NV (p.T.bs j) ε (KB.slv p.T F j hj w a ha.2) := by
  have h := fun e => nice_of_cpt (Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w a ha hF e)
  obtain ⟨ε, hε, hall⟩ := common_eps (fun e ε => JC.NiceCoef (p.T.bs j) ε (KB.slv p.T F j hj w a ha.2 e))
    (fun e ε ε' h h0 h' => nice_mono h h') h
  exact ⟨ε, hε, hall⟩

theorem form_eq' (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) :
    p.form j hj w = D.formLev p.T (M.sgn P p.l0) ⟨j, by omega⟩ w := rfl

theorem form_sl (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) {ε : ℝ}
    (x₁ x₂ y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (h₁ : NV (p.T.bs j) ε x₁) (h₂ : NV (p.T.bs j) ε x₂) (hy : NV (p.T.bs j) ε y) :
    p.form j hj w (x₁ + c • x₂) y = p.form j hj w x₁ y + c * p.form j hj w x₂ y :=
  PBG.form_sesq_left P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w x₁ x₂ y c (PBG.decV_of_nice h₁) (PBG.decV_of_nice h₂)
    (PBG.decV_of_nice hy)

theorem form_sr (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) {ε : ℝ}
    (x y₁ y₂ : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : NV (p.T.bs j) ε x) (h₁ : NV (p.T.bs j) ε y₁) (h₂ : NV (p.T.bs j) ε y₂) :
    p.form j hj w x (y₁ + c • y₂) = p.form j hj w x y₁ + conj c * p.form j hj w x y₂ :=
  PBG.form_sesq_right P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w x y₁ y₂ c (PBG.decV_of_nice hx) (PBG.decV_of_nice h₁)
    (PBG.decV_of_nice h₂)

end forms

end

end Formalism.FourierDecayAlt.P.PBL
end

