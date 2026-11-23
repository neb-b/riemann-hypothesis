module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CompactDerivativesBounded

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.GenApplyZero
section
open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

namespace CoordinateExpansion

theorem exp_localHomeo (n : ℕ) :
    ∃ e : OpenPartialHomeomorph (Matrix (Fin n) (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ),
      (0 : Matrix (Fin n) (Fin n) ℂ) ∈ e.source ∧ ∀ Z ∈ e.source, e Z = NormedSpace.exp Z := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hf : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)) 0 := by
    exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix (Fin n) (Fin n) ℂ)
  exact ⟨hf.toOpenPartialHomeomorph _, hf.mem_toOpenPartialHomeomorph_source, fun Z _ => rfl⟩

variable {n : ℕ}

def coord (Z : Matrix (Fin n) (Fin n) ℂ) (p : Fin n × Fin n) : ℝ :=
  if p.1 = p.2 then (Z p.1 p.1).im else if p.1 < p.2 then (Z p.1 p.2).re else (Z p.2 p.1).im

theorem continuous_coord (p : Fin n × Fin n) : Continuous fun Z : Matrix (Fin n) (Fin n) ℂ => coord Z p := by
  unfold coord
  split_ifs
  · exact Complex.continuous_im.comp (continuous_id.matrix_elem _ _)
  · exact Complex.continuous_re.comp (continuous_id.matrix_elem _ _)
  · exact Complex.continuous_im.comp (continuous_id.matrix_elem _ _)

theorem entry_of_inG {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z) (a b : Fin n) :
    Z a b = -((sg ε (a, b) : ℝ) : ℂ) * star (Z b a) := by
  have h := congrFun (congrFun hZ a) b
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Jm, Matrix.conjTranspose_apply,
    Matrix.zero_apply] at h
  simp only [sg]
  cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at h ⊢ <;>
    first | linear_combination h | linear_combination -h

theorem sg_swap (ε : Fin n → Bool) (a b : Fin n) : sg ε (b, a) = sg ε (a, b) := by
  simp only [sg]
  by_cases h : ε a = ε b
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun h' => h h'.symm), if_neg h]

theorem gen_apply_zero (ε : Fin n → Bool) (p : Fin n × Fin n) (i j : Fin n) (h1 : p ≠ (i, j)) (h2 : p ≠ (j, i)) :
    gen ε p i j = 0 := by
  obtain ⟨p1, p2⟩ := p
  simp only [ne_eq, Prod.mk.injEq] at h1 h2
  unfold gen
  split_ifs <;> simp [Matrix.single_apply] <;> aesop

theorem eq_sum_gen {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z) :
    Z = ∑ p, ((coord Z p : ℝ) : ℂ) • gen ε p := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [Fintype.sum_eq_add (i, j) (j, i) (by simp [h.ne])
      (fun q hq => by rw [gen_apply_zero ε q i j hq.1 hq.2, mul_zero])]
    simp [coord, gen, h, h.ne, h.ne', not_lt.mpr h.le, Matrix.single_apply]
  · rw [Fintype.sum_eq_single (i, i) (fun q hq => by rw [gen_apply_zero ε q i i hq hq, mul_zero])]
    have he := entry_of_inG hZ i i
    simp only [sg, if_true] at he
    have hre : (Z i i).re = 0 := by
      have h2 := congrArg Complex.re he
      simp at h2
      linarith
    simp [coord, gen, Matrix.single_apply]
    try (apply Complex.ext <;> simp [hre])
  · rw [Fintype.sum_eq_add (i, j) (j, i) (by simp [h.ne'])
      (fun q hq => by rw [gen_apply_zero ε q i j hq.1 hq.2, mul_zero])]
    rw [entry_of_inG hZ i j]
    simp [coord, gen, h, h.ne, h.ne', not_lt.mpr h.le, Matrix.single_apply, sg_swap]
    try (apply Complex.ext <;> simp <;> ring)

theorem inG_of_log {ε : Fin n → Bool} (e : OpenPartialHomeomorph (Matrix (Fin n) (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ))
    (hee : ∀ Z ∈ e.source, e Z = NormedSpace.exp Z) {Z g : Matrix (Fin n) (Fin n) ℂ} (hZ : Z ∈ e.source)
    (hτZ : -(Jm ε * Zᴴ * Jm ε) ∈ e.source) (hg : inUJ ε g) (hZg : NormedSpace.exp Z = g) : inG ε Z := by

  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Jm ε) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_left_inverse hJJ)
  have hJh : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    split_ifs with ha <;> simp [ha]
  have hg' : gᴴ * Jm ε * g = Jm ε := hg

  have hgl : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hJJ]
  have hgi : g⁻¹ = Jm ε * gᴴ * Jm ε := Matrix.inv_eq_left_inv hgl
  have key : NormedSpace.exp (-(Jm ε * Zᴴ * Jm ε)) = g := by
    have h1 : -(Jm ε * Zᴴ * Jm ε) = Jm ε * (-Z)ᴴ * (Jm ε)⁻¹ := by
      rw [hJi, Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul]
    rw [h1, Matrix.exp_conj _ _ hJu, Matrix.exp_conjTranspose, Matrix.exp_neg, hZg, hgi, hJi,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJh]
    simp only [← Matrix.mul_assoc]
    rw [hJJ, Matrix.one_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hτ : -(Jm ε * Zᴴ * Jm ε) = Z := e.injOn hτZ hZ (by rw [hee _ hτZ, hee _ hZ, key, hZg])
  show Zᴴ * Jm ε + Jm ε * Z = 0
  have hJZ : Jm ε * Z = -(Zᴴ * Jm ε) := by
    calc Jm ε * Z = Jm ε * (-(Jm ε * Zᴴ * Jm ε)) := by rw [hτ]
      _ = -(Zᴴ * Jm ε) := by
        rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  rw [hJZ, add_neg_cancel]

end CoordinateExpansion

theorem c6 : SmallMotionNeighbourhood := by
  intro n ε H _ _ _ σ D hD W C' hC' hdense
  obtain ⟨e, he0, hee⟩ := CoordinateExpansion.exp_localHomeo n
  set M := max C' 0 with hM
  let τ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun Z => -(Jm ε * Zᴴ * Jm ε)
  have hτ : Continuous τ :=
    ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const).neg
  let V : Set (Matrix (Fin n) (Fin n) ℂ) :=
    e.source ∩ τ ⁻¹' e.source ∩ {Z | (∑ p, |CoordinateExpansion.coord Z p|) * M < 1 / 2}
  have hVo : IsOpen V := by
    refine (e.open_source.inter (e.open_source.preimage hτ)).inter (isOpen_lt ?_ continuous_const)
    exact (continuous_finsetSum _ fun p _ => (CoordinateExpansion.continuous_coord p).abs).mul continuous_const
  have hV0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ V := by
    refine ⟨⟨he0, ?_⟩, ?_⟩
    · simpa [τ] using he0
    · simp [CoordinateExpansion.coord]
  have himg : IsOpen (e '' V) := e.isOpen_image_of_subset_source hVo (fun Z h => h.1.1)
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ e '' V := ⟨0, hV0, by rw [hee 0 he0, NormedSpace.exp_zero]⟩
  refine ⟨(fun g : UJ ε => umat g) ⁻¹' (e '' V), ?_, ?_⟩
  · exact continuous_umat.continuousAt.preimage_mem_nhds (himg.mem_nhds (by exact h1))
  · rintro g ⟨Z, hZV, hZg⟩ v hv
    have hZg' : NormedSpace.exp Z = umat g := by rw [← hee Z hZV.1.1]; exact hZg
    have hG : inG ε Z := CoordinateExpansion.inG_of_log e hee hZV.1.1 hZV.1.2 (umat_mem g) hZg'
    have key : ((D ⊓ W : Submodule ℂ H) : Set H) ⊆ {u : H | ‖σ (umat g) u - u‖ ≤ ‖u‖ / 2} := by
      intro u hu
      have huD : u ∈ D := hu.1
      have huW : u ∈ W := hu.2
      show ‖σ (umat g) u - u‖ ≤ ‖u‖ / 2
      rw [← hZg']
      calc ‖σ (NormedSpace.exp Z) u - u‖ ≤ ‖dS σ Z u‖ := hD.mv Z hG u huD
        _ = ‖∑ p, ((CoordinateExpansion.coord Z p : ℝ) : ℂ) • dS σ (gen ε p) u‖ := by
          rw [← hD.lin _ u huD, ← CoordinateExpansion.eq_sum_gen hG]
        _ ≤ ∑ p, |CoordinateExpansion.coord Z p| * (M * ‖u‖) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          refine mul_le_mul_of_nonneg_left ((hC' p u huD huW).trans ?_) (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ = ((∑ p, |CoordinateExpansion.coord Z p|) * M) * ‖u‖ := by
          rw [Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun p _ => by ring
        _ ≤ (1 / 2) * ‖u‖ := mul_le_mul_of_nonneg_right hZV.2.le (norm_nonneg _)
        _ = ‖u‖ / 2 := by ring
    have hcl : IsClosed {u : H | ‖σ (umat g) u - u‖ ≤ ‖u‖ / 2} :=
      isClosed_le (((σ (umat g)).continuous.sub continuous_id).norm) (continuous_norm.div_const _)
    exact closure_minimal key hcl (hdense v hv)

end Formalism.L2.SG.Pf.admitted
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.HasDerivAtDS
section
open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace AdmissibleVectors

section Lie

variable {n : ℕ} {ε : Fin n → Bool}

theorem inG_zero : inG ε (0 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold inG; simp

theorem inG_add {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) : inG ε (X + Y) := by
  unfold inG at *
  calc (X + Y)ᴴ * Jm ε + Jm ε * (X + Y) = (Xᴴ * Jm ε + Jm ε * X) + (Yᴴ * Jm ε + Jm ε * Y) := by
        rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]; abel
    _ = 0 := by rw [hX, hY, add_zero]

theorem inG_rsmul (r : ℝ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : inG ε ((r : ℂ) • X) := by
  unfold inG at *
  rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX,
    smul_zero]

theorem inG_iff (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε X ↔ ∀ i j, star (X j i) * (if ε j then 1 else -1) + (if ε i then 1 else -1) * X i j = 0 := by
  unfold inG Jm
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    simpa [Matrix.add_apply, conjTranspose_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  · intro h
    ext i j
    simpa [Matrix.add_apply, conjTranspose_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] using h i j

theorem inG_gen (p : Fin n × Fin n) : inG ε (gen ε p) := by
  rw [inG_iff]
  intro i j
  obtain ⟨a, b⟩ := p
  simp only [gen, sg]
  by_cases h1 : a = b
  · subst h1
    simp only [if_true, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases hi : a = i <;> by_cases hj : a = j
    · subst hi; subst hj; cases ε a <;> simp
    · subst hi; simp [hj]
    · subst hj; simp [hi]
    · simp [hi, hj]
  · rw [if_neg h1]
    have hne : b ≠ a := fun h => h1 h.symm
    by_cases h2 : a < b
    · rw [if_pos h2]
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      by_cases hia : a = i <;> by_cases hib : b = i <;> by_cases hja : a = j <;> by_cases hjb : b = j <;>
        simp only [hia, hib, hja, hjb, true_and, and_true, false_and, and_false, if_true, if_false] <;>
        subst_vars <;> simp_all <;> cases hεa : ε a <;> cases hεb : ε b <;> simp_all
    · rw [if_neg h2]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      by_cases hia : a = i <;> by_cases hib : b = i <;> by_cases hja : a = j <;> by_cases hjb : b = j <;>
        simp only [hia, hib, hja, hjb, true_and, and_true, false_and, and_false, if_true, if_false] <;>
        subst_vars <;> simp_all <;> cases hεa : ε a <;> cases hεb : ε b <;> simp_all

theorem inG_comb (z : Fin n × Fin n → ℝ) : inG ε (∑ p, ((z p : ℝ) : ℂ) • gen ε p) :=
  Finset.sum_induction _ (inG ε) (fun _ _ h1 h2 => inG_add h1 h2) inG_zero
    (fun p _ => inG_rsmul (z p) (inG_gen p))

end Lie

section Vec

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem vec_smul' (w : H) (c : ℂ) (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Formalism.MainNotions.BridgeCPX.vec ε σ w (c • Φ) = c • Formalism.MainNotions.BridgeCPX.vec ε σ w Φ := by
  unfold Formalism.MainNotions.BridgeCPX.vec
  rw [← integral_smul]
  congr 1
  funext y
  simp [smul_smul]

theorem vec_sum' (hσ : IsURepOn (UJset ε) σ) (w : H) {ι : Type} (s : Finset ι)
    (Φ : ι → Matrix (Fin n) (Fin n) ℂ → ℂ) (hΦ : ∀ i, IsTest (Φ i)) :
    Formalism.MainNotions.BridgeCPX.vec ε σ w (∑ i ∈ s, Φ i) = ∑ i ∈ s, Formalism.MainNotions.BridgeCPX.vec ε σ w (Φ i) := by
  unfold Formalism.MainNotions.BridgeCPX.vec
  rw [← integral_finsetSum s (fun i _ => vec_integrable hσ w (hΦ i))]
  congr 1
  funext y
  simp [Finset.sum_apply, Finset.sum_smul]

theorem der_comb (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (z : Fin n × Fin n → ℝ)
    (G : Fin n × Fin n → Matrix (Fin n) (Fin n) ℂ) :
    der (-(∑ p, ((z p : ℝ) : ℂ) • G p)) Φ = ∑ p, ((z p : ℝ) : ℂ) • der (-(G p)) Φ := by
  funext m
  simp only [der, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have e : -(∑ p, ((z p : ℝ) : ℂ) • G p) * m = ∑ p, (z p) • (-(G p) * m) := by
    rw [Matrix.neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.smul_mul, Matrix.neg_mul, smul_neg, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, Complex.real_smul]

theorem hasDerivAt_dS (hσ : IsURepOn (UJset ε) σ) (w : H) {v : H} (hv : v ∈ Vsub ε hσ w)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (dS σ X v) 0 := by
  obtain ⟨x', -, hx'⟩ := Vsub_deriv hσ w hv hX
  unfold dS
  rw [hx'.deriv]
  exact hx'

theorem dS_mem (hσ : IsURepOn (UJset ε) σ) (w : H) {v : H} (hv : v ∈ Vsub ε hσ w)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : dS σ X v ∈ Vsub ε hσ w := by
  obtain ⟨x', hm, hx'⟩ := Vsub_deriv hσ w hv hX
  unfold dS
  rw [hx'.deriv]
  exact hm

theorem dS_vec (hσ : IsURepOn (UJset ε) σ) (w : H) {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    dS σ X (Formalism.MainNotions.BridgeCPX.vec ε σ w Φ) = Formalism.MainNotions.BridgeCPX.vec ε σ w (der (-X) Φ) := by
  have h := hasDerivAt_vec hσ w hΦ (inG_neg hX)
  have h' : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (Formalism.MainNotions.BridgeCPX.vec ε σ w Φ)) (Formalism.MainNotions.BridgeCPX.vec ε σ w (der (-X) Φ)) 0 := by
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    show σ (NormedSpace.exp ((t : ℂ) • X)) (Formalism.MainNotions.BridgeCPX.vec ε σ w Φ) = Formalism.MainNotions.BridgeCPX.vec ε σ w (ltr (NormedSpace.exp ((t : ℂ) • (-X))) Φ)
    rw [← umat_expG (inG_neg hX) t, ← rep_vec hσ w hΦ, expG_neg_inv hX, umat_expG hX]
  unfold dS
  exact h'.deriv

theorem dS_lin (hσ : IsURepOn (UJset ε) σ) (w : H) (z : Fin n × Fin n → ℝ) {v : H} (hv : v ∈ Vsub ε hσ w) :
    dS σ (∑ p, ((z p : ℝ) : ℂ) • gen ε p) v = ∑ p, ((z p : ℝ) : ℂ) • dS σ (gen ε p) v := by
  obtain ⟨Φ, hΦ, rfl⟩ := hv
  rw [dS_vec hσ w hΦ (inG_comb z), der_comb, vec_sum' hσ w _ _ (fun p => test_smul _ (test_der hΦ _))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [vec_smul', dS_vec hσ w hΦ (inG_gen p)]

theorem dS_skew (hσ : IsURepOn (UJset ε) σ) (w : H) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    {u v : H} (hu : u ∈ Vsub ε hσ w) (hv : v ∈ Vsub ε hσ w) :
    ⟪dS σ X u, v⟫_ℂ = - ⟪u, dS σ X v⟫_ℂ := by
  have h := (hasDerivAt_dS hσ w hu hX).inner ℂ (hasDerivAt_dS hσ w hv hX)
  have hc : (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • X)) u, σ (NormedSpace.exp ((t : ℂ) • X)) v⟫_ℂ) =
      fun _ => ⟪u, v⟫_ℂ := by
    funext t
    rw [← umat_expG hX t, rep_inner hσ]
  rw [hc] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) ⟪u, v⟫_ℂ)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1] at h0
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h0)

theorem dS_conj (hσ : IsURepOn (UJset ε) σ) (w : H) (g : UJ ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    {v : H} (hv : v ∈ Vsub ε hσ w) :
    σ (umat g) (dS σ X v) = dS σ (umat g * X * umat g⁻¹) (σ (umat g) v) := by
  have hd := hasDerivAt_dS hσ w hv hX
  have h2 : HasDerivAt (fun t : ℝ => σ (umat g) (σ (NormedSpace.exp ((t : ℂ) • X)) v)) (σ (umat g) (dS σ X v)) 0 :=
    ((σ (umat g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
  have he : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (umat g * X * umat g⁻¹))) (σ (umat g) v)) =
      fun t : ℝ => σ (umat g) (σ (NormedSpace.exp ((t : ℂ) • X)) v) := by
    funext t
    have hinv : umat g⁻¹ = (umat g)⁻¹ := Matrix.coe_units_inv _
    have h1 : NormedSpace.exp ((t : ℂ) • (umat g * X * umat g⁻¹)) = umat (g * expG ε X t * g⁻¹) := by
      rw [show umat (g * expG ε X t * g⁻¹) = umat g * umat (expG ε X t) * umat g⁻¹ from rfl, umat_expG hX, hinv,
        ← Matrix.exp_conj _ _ (Units.isUnit _), Matrix.mul_smul, Matrix.smul_mul]
    rw [h1, rep_mul hσ, rep_inv_apply hσ, rep_mul hσ, umat_expG hX]
  unfold dS
  rw [he]
  exact h2.deriv.symm

theorem dS_mv (hσ : IsURepOn (UJset ε) σ) (w : H) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    {v : H} (hv : v ∈ Vsub ε hσ w) : ‖σ (NormedSpace.exp X) v - v‖ ≤ ‖dS σ X v‖ := by
  have hd := hasDerivAt_dS hσ w hv hX
  have hder : ∀ t : ℝ, HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) v)
      (σ (NormedSpace.exp ((t : ℂ) • X)) (dS σ X v)) t := by
    intro t
    have h1 := ((σ (NormedSpace.exp ((t : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (t - t) (by rw [sub_self]; exact hd)
    have h2 := HasDerivAt.comp_sub_const t t h1
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    show σ (NormedSpace.exp ((s : ℂ) • X)) v =
      σ (NormedSpace.exp ((t : ℂ) • X)) (σ (NormedSpace.exp (((s - t : ℝ) : ℂ) • X)) v)
    rw [← umat_expG hX t, ← umat_expG hX (s - t), ← rep_mul hσ,
      show umat (expG ε X t * expG ε X (s - t)) = umat (expG ε X t) * umat (expG ε X (s - t)) from rfl,
      umat_expG hX, umat_expG hX, ← one_parameter_subgroup_holds n X t (s - t), add_sub_cancel]
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) v)
    (fun t _ => (hder t).hasDerivWithinAt)
    (fun t _ => le_of_eq (hσ.2.1 _ ((umat_expG hX t) ▸ umat_mem _) _))
  simpa [hσ.1.1] using key

end Vec

end AdmissibleVectors

theorem c1 : CalculusOnSmoothVectors := by
  intro n ε H _ _ _ σ hσ w
  exact
    { der := fun X hX v hv => AdmissibleVectors.hasDerivAt_dS hσ w hv hX
      mem := fun X hX v hv => AdmissibleVectors.dS_mem hσ w hv hX
      lin := fun z v hv => AdmissibleVectors.dS_lin hσ w z hv
      skew := fun X hX u hu v hv => AdmissibleVectors.dS_skew hσ w hX hu hv
      conj := fun g X hX v hv => AdmissibleVectors.dS_conj hσ w g hX hv
      mv := fun X hX v hv => AdmissibleVectors.dS_mv hσ w hX hv }

end Formalism.L2.SG.Pf.admitted
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.KavgFixRange
section
open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace ExponentialDecomposition

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kavg_fix_range {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hst : IsKStableOn ε σ S)
    {e : KG ε → ℂ} (he : Continuous e) (hfix : ∀ x ∈ S, kavg hσ he x = x) (Θ : S →ₗ[ℂ] H)
    (hΘ : ∀ (a : KG ε) (v w : S), (w : H) = σ (toMK a) v → Θ w = σ (toMK a) (Θ v)) (s : S) :
    kavg hσ he (Θ s) = Θ s := by
  have hs : kavg hσ he (s : H) = s := hfix s s.2
  have hval : ∀ x : H, kavg hσ he x = ∫ k, e k • σ (toMK k) x ∂muK ε := fun x => by
    unfold Formalism.MainNotions.BridgeCPX.kavg
    rfl
  have hkS : ∀ k : KG ε, σ (toMK k) s ∈ S := fun k => hst _ k.2 _ s.2
  let F : KG ε → S := fun k => e k • ⟨σ (toMK k) s, hkS k⟩
  have hΘF : ∀ k, Θ (F k) = e k • σ (toMK k) (Θ s) := fun k => by
    simp only [F, map_smul]
    rw [hΘ k s ⟨σ (toMK k) s, hkS k⟩ rfl]
  have hsub : ((∫ k, F k ∂muK ε : S) : H) = ∫ k, (F k : H) ∂muK ε :=
    (S.subtypeₗᵢ.integral_comp_comm F).symm
  have hint : (∫ k, F k ∂muK ε) = s := by
    apply Subtype.ext
    rw [hsub, ← hs, hval]
    rfl
  rw [hval, integral_congr_ae (Filter.Eventually.of_forall fun k => (hΘF k).symm)]
  by_cases hFi : Integrable F (muK ε)
  · have h := (LinearMap.toContinuousLinearMap Θ).integral_comp_comm hFi
    simp only [LinearMap.coe_toContinuousLinearMap'] at h
    rw [h, hint]
  · rw [integral_undef hFi] at hint
    subst hint
    have h0 : ∀ k, F k = 0 := fun k => by
      ext
      simp [F]
    simp only [h0, map_zero, integral_zero]

theorem kavg_fix_isoK {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hst : IsKStableOn ε σ S)
    {e : KG ε → ℂ} (he : Continuous e) (hfix : ∀ x ∈ S, kavg hσ he x = x) {v : H} (hv : v ∈ isoK ε σ S) :
    kavg hσ he v = v := by
  have hle : isoK ε σ S ≤ LinearMap.ker
      ((((kavg hσ he : H →L[ℂ] H) - ContinuousLinearMap.id ℂ H : H →L[ℂ] H)) : H →ₗ[ℂ] H) := by
    refine sSup_le ?_
    rintro T ⟨Θ, hΘ, rfl⟩
    rintro x ⟨s, rfl⟩
    simp [LinearMap.mem_ker, sub_eq_zero, kavg_fix_range hσ hst he hfix Θ hΘ s]
  have h := hle hv
  simpa [LinearMap.mem_ker, sub_eq_zero] using h

end ExponentialDecomposition

theorem c0 : SmoothVectorsDense := by
  intro n ε H _ _ _ σ hσ hirr w hw S hfd hst v hv
  obtain ⟨e, he, hfix, hrange⟩ := compactProj (KG ε) (muK ε) H (fun k : KG ε => σ (toMK k)) hσ.1.1
    (fun a b => hσ.1.2 _ (umat_mem (a : UJ ε)) _ (umat_mem (b : UJ ε)))
    (fun a v => hσ.2.1 _ (umat_mem (a : UJ ε)) v)
    (fun v => (cont_orbit hσ v).comp continuous_subtype_val) S hfd (fun a v hv => hst _ a.2 v hv)
  have hfix' : ∀ x ∈ S, kavg hσ he x = x := fun x hx => by
    rw [kavg_apply]
    exact hfix x hx
  have hE : kavg hσ he v = v := ExponentialDecomposition.kavg_fix_isoK hσ hst he hfix' hv
  have hvc : v ∈ closure (Vsub ε hσ w : Set H) := by
    have h := Vsub_dense hσ hirr hw
    have h2 : v ∈ (Vsub ε hσ w).topologicalClosure := by
      rw [h]
      trivial
    exact h2
  have h3 : kavg hσ he v ∈ closure ((Vsub ε hσ w ⊓ isoK ε σ S : Submodule ℂ H) : Set H) := by
    refine map_mem_closure (kavg hσ he).continuous hvc ?_
    rintro _ ⟨Φ, hΦ, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_inf]
    refine ⟨⟨kconv ε e Φ, test_kconv he hΦ, kavg_vec hσ w he hΦ⟩, ?_⟩
    rw [kavg_apply]
    exact hrange _
  rwa [hE] at h3

end Formalism.L2.SG.Pf.admitted
end
end

