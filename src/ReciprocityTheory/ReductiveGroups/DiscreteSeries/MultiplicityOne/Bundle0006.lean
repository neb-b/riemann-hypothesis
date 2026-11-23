module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MulVecApplyOfRow
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0016
public import Formalism.FormalDegreeBessel.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0005

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.BigCellCommuteFrameElement
section
open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

lemma Hb_mul_self : Hb k * Hb k = 1 := by
  unfold Hb
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

lemma unit_of_frame {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : γᴴ * Hb k * γ = Hb k) : IsUnit γ.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hb k * γᴴ * Hb k)
  calc Hb k * γᴴ * Hb k * γ = Hb k * (γᴴ * Hb k * γ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Hb_mul_self]

lemma emb_inv {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hγ : IsUnit γ.det) :
    (embWb k r γ)⁻¹ = embWb k r γ⁻¹ :=
  Matrix.inv_eq_right_inv (by rw [← emb_mul, Matrix.mul_nonsing_inv _ hγ, emb_one])

lemma emb_unit {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hγ : IsUnit γ.det) : IsUnit (embWb k r γ).det :=
  Matrix.isUnit_det_of_right_inverse (B := embWb k r γ⁻¹) (by rw [← emb_mul, Matrix.mul_nonsing_inv _ hγ, emb_one])

section gbar

variable (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : IsUnit (embWb k r γ).det)
include hE

lemma gbar_mul (g h : Mat k r) : gbar k r γ (g * h) = gbar k r γ g * gbar k r γ h := by
  unfold gbar
  have e : (embWb k r γ)⁻¹ * (g * h) * embWb k r γ =
      ((embWb k r γ)⁻¹ * g * embWb k r γ) * ((embWb k r γ)⁻¹ * h * embWb k r γ) := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hE]
  rw [e, Matrix.map_mul]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hE]

lemma gbar_one : gbar k r γ 1 = 1 := by
  unfold gbar
  rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hE, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.mul_nonsing_inv _ hE]

lemma gbar_gbar (g : Mat k r) : gbar k r γ (gbar k r γ g) = g := by
  unfold gbar
  have h1 : (embWb k r γ)⁻¹ * (embWb k r γ * ((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ) *
      (embWb k r γ)⁻¹) * embWb k r γ = ((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ) := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hE, Matrix.nonsing_inv_mul _ hE,
      Matrix.mul_one]
  rw [h1]
  have h2 : (((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ)).map (starRingEnd ℂ) =
      (embWb k r γ)⁻¹ * g * embWb k r γ := by
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, Complex.conj_conj]
  rw [h2]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hE, Matrix.mul_nonsing_inv _ hE,
    Matrix.mul_one]

lemma gbar_mul_inv {x : Mat k r} (hx : IsUnit x.det) : gbar k r γ x * gbar k r γ x⁻¹ = 1 := by
  rw [← gbar_mul γ hE, Matrix.mul_nonsing_inv _ hx, gbar_one γ hE]

lemma gbar_inv {x : Mat k r} (hx : IsUnit x.det) : gbar k r γ x⁻¹ = (gbar k r γ x)⁻¹ :=
  (Matrix.inv_eq_right_inv (gbar_mul_inv γ hE hx)).symm

lemma gbar_unit {x : Mat k r} (hx : IsUnit x.det) : IsUnit (gbar k r γ x).det :=
  Matrix.isUnit_det_of_right_inverse (gbar_mul_inv γ hE hx)

lemma th_five {a b g c d : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det) (hg : th k r γ g = g) :
    th k r γ (a⁻¹ * b⁻¹ * g * c * d) =
      (gbar k r γ d)⁻¹ * (gbar k r γ c)⁻¹ * g * gbar k r γ b * gbar k r γ a := by
  unfold th at hg ⊢
  rw [gbar_mul γ hE, gbar_mul γ hE, gbar_mul γ hE, gbar_mul γ hE, gbar_inv γ hE ha, gbar_inv γ hE hb]
  simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE ha),
    Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE hb), hg, Matrix.mul_assoc]

lemma th_mul_inv {h h' : Mat k r} (hh' : IsUnit h'.det) :
    th k r γ (h * h'⁻¹) = gbar k r γ h' * (gbar k r γ h)⁻¹ := by
  unfold th
  rw [gbar_mul γ hE, gbar_inv γ hE hh', Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE hh')]

end gbar

lemma psi_conj (z : Fin (2 * r + k + 1) → ℂ) {a : Mat k r} (ha : a ∈ UWset k r z) (c : ℂ) (n : Mat k r) :
    psi k r z c (a * n * a⁻¹) = psi k r z c n := by
  unfold psi
  rw [ell_conj z (uw_block ha) (uw_block (uw_inv ha)) (uw_inv ha).2.2]

lemma tau_wI (j : Fin (k + 1)) : tau k r (wI k r j) = wI k r j := by
  have := j.isLt
  unfold tau wI
  apply Fin.ext
  simp only
  split_ifs with h <;> omega

lemma mud_off (d : ℂ) (x y : Fin (k + 1)) (h : (x ≠ 0 ∧ x ≠ Fin.last k) ∨ (y ≠ 0 ∧ y ≠ Fin.last k)) :
    mud k d x y = if x = y then 1 else 0 := by
  unfold mud
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

lemma emb_mud_off (d : ℂ) (i j : Fin (2 * r + k + 1))
    (h : (i ≠ wI k r 0 ∧ i ≠ wI k r (Fin.last k)) ∨ (j ≠ wI k r 0 ∧ j ≠ wI k r (Fin.last k))) :
    embWb k r (mud k d) i j = if i = j then 1 else 0 := by
  by_cases hi : mid k r i
  · by_cases hj : mid k r j
    · rw [emb_mid _ i j hi hj, mud_off]
      · by_cases e : i = j
        · subst e; simp
        · rw [if_neg e, if_neg (fun h' => e (by rw [← wI_midx hi, ← wI_midx hj, h']))]
      · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left
          exact ⟨fun h' => h1 (by rw [← wI_midx hi, h']), fun h' => h2 (by rw [← wI_midx hi, h'])⟩
        · right
          exact ⟨fun h' => h1 (by rw [← wI_midx hj, h']), fun h' => h2 (by rw [← wI_midx hj, h'])⟩
    · exact emb_out_col _ i j hj
  · exact emb_out_row _ i j hi

lemma comm_mud (hk : 1 ≤ k) {R : Mat k r} (hR : R ∈ UH (Hpk k r))
    (h0 : R *ᵥ bvec (wI k r 0) = bvec (wI k r 0)) (hL : R *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k)))
    (d : ℂ) : R * embWb k r (mud k d) = embWb k r (mud k d) * R := by
  set a := wI k r 0
  set b := wI k r (Fin.last k)
  have hne : a ≠ b := fun h => by
    have := congrArg Fin.val (wI_inj h)
    simp at this
    omega
  have c0 := col_of_fix h0
  have cL := col_of_fix hL
  have r0 : ∀ j, R a j = if a = j then 1 else 0 := by
    intro j
    have := row_of_fixed_col hR a c0 j
    rwa [tau_wI] at this
  have rL : ∀ j, R b j = if b = j then 1 else 0 := by
    intro j
    have := row_of_fixed_col hR b cL j
    rwa [tau_wI] at this
  set P : Mat k r := embWb k r (mud k d) - 1 with hPdef
  have hM : embWb k r (mud k d) = 1 + P := by rw [hPdef]; abel
  have hP : ∀ i j, ((i ≠ a ∧ i ≠ b) ∨ (j ≠ a ∧ j ≠ b)) → P i j = 0 := by
    intro i j h
    rw [hPdef, Matrix.sub_apply, emb_mud_off d i j h, Matrix.one_apply, sub_self]
  have RP : R * P = P := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_eq_add a b hne (fun l hl => by rw [hP l j (Or.inl hl), mul_zero]),
      c0, cL]
    by_cases ha : i = a
    · subst ha; rw [if_pos rfl, if_neg hne, one_mul, zero_mul, add_zero]
    · by_cases hb : i = b
      · subst hb; rw [if_neg (Ne.symm hne), if_pos rfl, one_mul, zero_mul, zero_add]
      · rw [if_neg ha, if_neg hb, zero_mul, zero_mul, add_zero, hP i j (Or.inl ⟨ha, hb⟩)]
  have PR : P * R = P := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_eq_add a b hne (fun l hl => by rw [hP i l (Or.inr hl), zero_mul]),
      r0, rL]
    by_cases ha : j = a
    · subst ha; rw [if_pos rfl, if_neg (Ne.symm hne), mul_one, mul_zero, add_zero]
    · by_cases hb : j = b
      · subst hb; rw [if_neg hne, if_pos rfl, mul_one, mul_zero, zero_add]
      · rw [if_neg (Ne.symm ha), if_neg (Ne.symm hb), mul_zero, mul_zero, add_zero, hP i j (Or.inr ⟨ha, hb⟩)]
  rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, RP, PR]

lemma big_cell_commute_frame_element (hBCF : BigCellFactor) (hUWb : UWbFacts) (hk : 1 ≤ k) {z : Fin (2 * r + k + 1) → ℂ}
    {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hγ : IsZFrame k r z γ) {u : Mat k r} (hu : u ∈ UUset k r z γ)
    (c : Fin r → ℂ) (d : ℂ) : u * g0 k r γ c d = g0 k r γ c d * u := by
  have hγu := unit_of_frame hγ.1
  have hEu : IsUnit (embWb k r γ).det := emb_unit hγu
  have hEW : embWb k r γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγ.1, rfl⟩
  have hEG : embWb k r γ ∈ UH (Hpk k r) := hEW.1
  have huW : u ∈ UWb k r := (hUWb k r).2.1 z hu.1
  set E := embWb k r γ with hEdef
  set R := E⁻¹ * u * E with hRdef
  have hR : R ∈ UH (Hpk k r) := uh_mul (uh_mul (uh_inv hEG) hu.1.1) hEG
  have fixR : ∀ v, E *ᵥ v = v → True := fun _ _ => trivial
  have h0 : R *ᵥ bvec (wI k r 0) = bvec (wI k r 0) := by
    rw [hRdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change E⁻¹ *ᵥ (u *ᵥ w1 k r γ) = _
    rw [hu.2, w1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hEu, Matrix.one_mulVec]
  have hL : R *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k)) := by
    rw [hRdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hγ.2, Matrix.mulVec_smul, hu.1.2.2, ← hγ.2,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hEu, Matrix.one_mulVec]
  have hRM := comm_mud hk hR h0 hL d
  have hu' : u = E * R * E⁻¹ := by
    rw [hRdef]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hEu, Matrix.mul_nonsing_inv _ hEu,
      Matrix.mul_one]
  have key : u * (E * embWb k r (mud k d) * E⁻¹) = E * embWb k r (mud k d) * E⁻¹ * u := by
    rw [hu']
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hEu]
    rw [← Matrix.mul_assoc R, hRM, Matrix.mul_assoc]
  unfold g0
  rw [(hBCF k r c _).1, emb_mul, emb_mul, ← emb_inv hγu]
  have hc := (hUWb k r).2.2 c u huW
  calc u * (bigCell k r c 1 * (E * embWb k r (mud k d) * E⁻¹))
      = bigCell k r c 1 * (u * (E * embWb k r (mud k d) * E⁻¹)) := by rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc]
    _ = bigCell k r c 1 * (E * embWb k r (mud k d) * E⁻¹) * u := by rw [key]; simp only [Matrix.mul_assoc]

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymA
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.InHolds
section
namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem multiplicity_one_hypotheses_hold : UnitaryGroupStructuralFacts :=
  ⟨ReciprocityTheory.ChartRestriction.DS.Xi.heisenbergHaarFacts_hold,
    Formalism.FourierDecayAlt.P.setting_with_prescribed_data_exists,
    Formalism.FourierDecayAlt.P.b2_rank_one_coord,
    Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization,
    Formalism.FourierDecayAlt.P.unipotent_weyl_properties,
    Formalism.FourierDecayAlt.P.conjugation_preserves_haar,
    Formalism.FourierDecayAlt.P.lemma_b_from_xi,
    Formalism.FourierDecayAlt.P.orbital_integral_ae_convergence_continuity,
    Formalism.FourierDecayAlt.P.phase_function_bound,
    Formalism.FourierDecayAlt.P.regularized_beta_bound_continuity_sesquilinear,
    Formalism.FourierDecayAlt.P.regularised_average_identity,
    Formalism.FourierDecayAlt.P.unfolding_identity_of_integration_formula,
    Formalism.FourierDecayAlt.P.ae_equality_from_test_functions,
    Formalism.FourierDecayAlt.P.dilation_jacobian_every_setting,
    Formalism.FourierDecayAlt.P.normalisation_unique_every_setting,
    Formalism.QuantumDeterminants.uWNormal,
    Formalism.QuantumDeterminants.ellAdd,
    Formalism.QuantumDeterminants.nSubgroup⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBetaInf
section
namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stBetaInf (h : UnitaryGroupStructuralFacts) : StBetaInf := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hRB, hRA, -, hAe, hDJ⟩ := h
  have hDJ' : DilJacAll := by first | exact hDJ | exact hDJ.1
  intro k r Wp Wq _ _ _ _ _ _ D A hXi hA F F' hF hF' hP
  obtain ⟨Ξ, hCB, hXI⟩ := hXi k r Wp Wq D A hA
  exact BetaInfA.betaInf_eq_of D A hAe (hRB k r Wp Wq D Ξ A hA hCB hXI)
    (hRA k r Wp Wq D Ξ A hA hCB hXI (hDJ' k r Wp Wq D)) (BetaInfA.inCC_five_four hF)
    (BetaInfA.inCC_five_four hF') hP

end ReciprocityTheory.ChartRestriction.DS.Mult1
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JFrame
section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stFrame : StFrame := by
  intro k r z _hk hz hT
  set T := Tz k r z with hTdef
  set s : ℝ := (Real.sqrt T)⁻¹ with hs

  have hTeq : T = ‖z (wI k r (Fin.last k))‖ ^ 2 - ∑ l : Fin k, ‖z (wI k r l.castSucc)‖ ^ 2 := by
    have h := frame_herm k r z hz
    simp only [frameMat_star_mul_self] at h
    rw [hTdef, Tz, h, ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re]
    ring
  have hsT : s ^ 2 * T = 1 := by
    rw [hs, inv_pow, Real.sq_sqrt hT.le, inv_mul_cancel₀ hT.ne']
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  refine ⟨frameMat k (fun j => (s : ℂ) * z (wI k r j)), ?_⟩
  unfold IsZFrame
  constructor
  · apply frameMat_unitary
    simp only [frameMat_star_mul_self]
    have key : ∑ l : Fin k, ‖(s : ℂ) * z (wI k r l.castSucc)‖ ^ 2 =
        ‖(s : ℂ) * z (wI k r (Fin.last k))‖ ^ 2 - 1 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0, mul_pow,
        ← Finset.mul_sum]
      linear_combination (-1 : ℝ) * hsT + s ^ 2 * hTeq
    rw [← Complex.ofReal_sum, key, Complex.ofReal_sub, Complex.ofReal_one]
  · have hlast : (wI k r (Fin.last k)).val = r + k := by simp [frame_wI_val]
    funext i
    simp only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul]
    unfold embWb
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · rw [dite_eq_left ⟨hi, by omega, by omega⟩]
      rw [show ∀ p, (⟨(wI k r (Fin.last k)).val - r, p⟩ : Fin (k + 1)) = Fin.last k from
        fun p => Fin.ext (by simp only [Fin.val_last]; omega)]
      rw [frameMat_col]
      rw [show ∀ p, wI k r (⟨i.val - r, p⟩ : Fin (k + 1)) = i from
        fun p => Fin.ext (by rw [frame_wI_val]; show r + (i.val - r) = i.val; omega)]
    · rw [dite_eq_right (fun h => hi h.1)]
      have hne : ¬ (i = wI k r (Fin.last k) ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k)) := by
        rintro ⟨rfl, h⟩
        exact h ⟨by omega, by omega⟩
      rw [if_neg hne, hz i (by omega), mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroup
section
noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stInvGroup (h : UnitaryGroupStructuralFacts) : StInvGroup := by
  obtain ⟨hB2, -, -, -, hUWb, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hHU, hHI, -, hCG, hCN, hCW, -⟩ := hB2
  intro k r Wp _ _ _ D X _ _ γ hγ
  have hG := hCG k r
  have hEG : embWb k r γ ∈ GV k r := by
    have hmem : embWb k r γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγ.1, rfl⟩
    exact hmem.1
  have hE := hG.unit _ hEG
  have hz := InvGrp.frame_conjugation_fixes_point hG hEG D.z D.T_pos hγ.2
  let gb : Mt k r → Mt k r := fun x i j => gbar k r γ (Matrix.of x) i j
  have hgb : Continuous gb := by
    simp only [gb, gbar]; fun_prop
  have hff : ∀ x, gb (gb x) = x := by
    intro x; funext i j
    change gbar k r γ (gbar k r γ (Matrix.of x)) i j = x i j
    rw [InvGrp.gbar_gbar hE]; rfl
  have hl : ∀ U : Set (Mat k r), (∀ a ∈ U, gbar k r γ a ∈ U) →
      ∀ a ∈ U, ∃ b ∈ U, ∀ x, lmulM a (gb x) = gb (lmulM b x) := by
    intro U hU a ha
    refine ⟨gbar k r γ a, hU a ha, fun x => ?_⟩
    funext i j
    change (a * gbar k r γ (Matrix.of x)) i j = gbar k r γ (gbar k r γ a * Matrix.of x) i j
    rw [InvGrp.gbar_mul hE, InvGrp.gbar_gbar hE]
  have hG1 : ∀ g ∈ GV k r, gbar k r γ g ∈ GV k r := InvGrp.gbar_mem_GV hG hEG
  have hN1 : ∀ m ∈ Nset k r, gbar k r γ m ∈ Nset k r := InvGrp.gbar_mem_N hG hEG
  have hW1 : ∀ h ∈ UWset k r D.z, gbar k r γ h ∈ UWset k r D.z := InvGrp.gbar_mem_UW hG hEG D.z hz
  have hmapG : D.μG.map gb = D.μG :=
    InvGrp.map_invol_eq hHU hG D.haarG gb hgb hff (fun x hx => hG1 _ hx) (hl _ hG1)
  refine ⟨hG1, hN1, hW1, InvGrp.gbar_mem_UU hG hEG D.z hz, ?_, ?_, ?_, ?_, ?_⟩
  · intro g _ g' _
    unfold th
    rw [InvGrp.gbar_mul hE, Matrix.mul_inv_rev]
  · intro g hg
    unfold th
    rw [InvGrp.gbar_inv hE _ (hG.unit _ (hG1 g hg)), InvGrp.gbar_gbar hE]
    exact Matrix.nonsing_inv_nonsing_inv g (hG.unit g hg)
  · have hth : (fun x : Mt k r => fun i j => th k r γ (Matrix.of x) i j) = invM ∘ gb := by
      funext x; rfl
    rw [hth, ← Measure.map_map InvGrp.measurable_invM hgb.measurable, hmapG, hHI k r (GV k r) D.μG hG D.haarG]
  · exact InvGrp.map_invol_eq hHU (hCN k r) D.haarN gb hgb hff (fun x hx => hN1 _ hx) (hl _ hN1)
  · exact InvGrp.map_invol_eq hHU (hCW k r D.z) D.haarW gb hgb hff (fun x hx => hW1 _ hx) (hl _ hW1)

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JMixedA
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.MixedNormBounds

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ConjugateNormInequalities

variable {k r : ℕ}

theorem gN_map_conj (M : Mat k r) : gN (M.map (starRingEnd ℂ)) = gN M := by
  simp only [gN, Matrix.map_apply, Complex.normSq_conj]

theorem gN_le_gbar {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hE : IsUnit (embWb k r γ).det) (y : Mat k r) :
    gN y ≤ (gN (embWb k r γ) * gN (embWb k r γ)⁻¹) ^ 2 * gN (gbar k r γ y) := by
  obtain ⟨y', hy'⟩ : ∃ y', y' = gbar k r γ y := ⟨_, rfl⟩
  have h1 : gN y = gN (gbar k r γ y') := by rw [hy', InvGrp.gbar_gbar hE]
  rw [h1, ← hy']
  unfold gbar
  set E := embWb k r γ
  have hE0 := gN_nonneg E
  have hEi0 := gN_nonneg E⁻¹
  calc gN (E * (E⁻¹ * y' * E).map (starRingEnd ℂ) * E⁻¹)
      ≤ gN E * gN ((E⁻¹ * y' * E).map (starRingEnd ℂ)) * gN E⁻¹ :=
        (gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right (gN_mul_le _ _) hEi0)
    _ = gN E * gN (E⁻¹ * y' * E) * gN E⁻¹ := by rw [gN_map_conj]
    _ ≤ gN E * (gN E⁻¹ * gN y' * gN E) * gN E⁻¹ := by
        gcongr
        exact (gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right (gN_mul_le _ _) hE0)
    _ = (gN E * gN E⁻¹) ^ 2 * gN y' := by ring

theorem rpow_bound {A B K a : ℝ} (hA : 0 < A) (hK : 0 < K) (ha : 0 ≤ a) (h : A ≤ K * B) :
    B ^ (-a) ≤ K ^ a * A ^ (-a) := by
  have hB : A / K ≤ B := by rw [div_le_iff₀ hK, mul_comm]; exact h
  have hAK : 0 < A / K := div_pos hA hK
  calc B ^ (-a) ≤ (A / K) ^ (-a) := Real.rpow_le_rpow_of_nonpos hAK hB (by linarith)
    _ = K ^ a * A ^ (-a) := by
      rw [Real.div_rpow hA.le hK.le, Real.rpow_neg hK.le, div_eq_mul_inv, inv_inv, mul_comm]

theorem inner_sig_sig (X : SigData k r) {h : Mat k r} (hh : h ∈ GV k r) (a b : X.Hs) :
    ⟪X.σ h a, X.σ h b⟫_ℂ = ⟪a, b⟫_ℂ := (⟨(X.σ h).toLinearMap, X.rep.2.1 h hh⟩ : X.Hs →ₗᵢ[ℂ] X.Hs).inner_map_map a b

theorem inner_sig_left (X : SigData k r) (hG : IsClosedSubgroup (GV k r)) {h : Mat k r} (hh : h ∈ GV k r)
    (a b : X.Hs) : ⟪X.σ h a, b⟫_ℂ = ⟪a, X.σ h⁻¹ b⟫_ℂ := by
  have hi : h⁻¹ ∈ GV k r := hG.inv_mem h hh
  have hb : X.σ h (X.σ h⁻¹ b) = b := by
    have e := X.rep.1.2 h hh h⁻¹ hi
    rw [Matrix.mul_nonsing_inv _ (hG.unit h hh), X.rep.1.1] at e
    have e2 := congrArg (fun T : X.Hs →L[ℂ] X.Hs => T b) e
    simpa using e2.symm
  conv_lhs => rw [← hb]
  exact inner_sig_sig X hh a _

theorem exists_inner_ne (X : SigData k r) (hG : IsClosedSubgroup (GV k r)) (v : X.Hs) (hv : v ≠ 0) :
    ∃ g ∈ GV k r, ⟪v, X.σ g X.w⟫_ℂ ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  let S : Submodule ℂ X.Hs :=
    { carrier := {u | ∀ g ∈ GV k r, ⟪v, X.σ g u⟫_ℂ = 0}
      add_mem' := by
        intro a b ha hb g hg
        rw [map_add (f := _), inner_add_right, ha g hg, hb g hg, add_zero]
      zero_mem' := by
        intro g hg
        rw [map_zero, inner_zero_right]
      smul_mem' := by
        intro c a ha g hg
        rw [map_smul, inner_smul_right, ha g hg, mul_zero] }
  have hSc : IsClosed (S : Set X.Hs) := by
    have e : (S : Set X.Hs) = ⋂ g ∈ GV k r, (fun u => ⟪v, X.σ g u⟫_ℂ) ⁻¹' {0} := by
      ext u
      show (∀ g ∈ GV k r, ⟪v, X.σ g u⟫_ℂ = 0) ↔ _
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    rw [e]
    exact isClosed_biInter fun g _ => isClosed_singleton.preimage (continuous_const.inner (X.σ g).continuous)
  have hSi : ∀ g ∈ GV k r, ∀ u ∈ S, X.σ g u ∈ S := by
    intro g hg u hu g' hg'
    have e := X.rep.1.2 g' hg' g hg
    have e2 : X.σ g' (X.σ g u) = X.σ (g' * g) u := by rw [e]; rfl
    show ⟪v, X.σ g' (X.σ g u)⟫_ℂ = 0
    rw [e2]
    exact hu _ (hG.mul_mem g' hg' g hg)
  have hw : X.w ∈ S := fun g hg => hcon g hg
  rcases X.irr S hSc hSi with h | h
  · have h0 : X.w = 0 := by
      rw [h] at hw
      exact (Submodule.mem_bot ℂ).mp hw
    have h1 := X.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  · have hv' : v ∈ S := by rw [h]; exact Submodule.mem_top
    have h0 := hv' 1 hG.one_mem
    rw [X.rep.1.1, ContinuousLinearMap.one_apply, inner_self_eq_zero] at h0
    exact hv h0

end ReciprocityTheory.ChartRestriction.DS.Mult1.MixedNormBounds
end
end

