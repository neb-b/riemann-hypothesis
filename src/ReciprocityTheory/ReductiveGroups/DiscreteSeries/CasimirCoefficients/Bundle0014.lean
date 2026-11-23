module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0010
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousOnFderivPhiP
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandPsB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0013
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandPs
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

private lemma conj_single_lemma (A B : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    A * Matrix.single a b (1 : ℂ) * B =
      ∑ c, ∑ d, (Aᵀ a c * Bᵀ d b) • Matrix.single c d (1 : ℂ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and, ite_mul, mul_ite,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

private lemma mul_single_rev_mul_eq_sum (A B : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    A * Matrix.single (Fin.rev b) (Fin.rev a) (1 : ℂ) * B =
      ∑ c, ∑ d, (B.submatrix Fin.rev Fin.rev a c * A.submatrix Fin.rev Fin.rev d b) •
        Matrix.single (Fin.rev d) (Fin.rev c) (1 : ℂ) := by
  rw [conj_single_lemma, Finset.sum_comm]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun d => ?_
  refine Fintype.sum_equiv Fin.revPerm _ _ fun c => ?_
  simp [mul_comm]

private lemma toMK_inv_mul_and_mul_inv (g : KG ε) : toMK g⁻¹ * toMK g = 1 ∧ toMK g * toMK g⁻¹ = 1 := by
  have hg : toMK g ∈ Kset ε := g.2
  simp only [Kset, Set.mem_setOf_eq] at hg
  rw [Ps1.toMK_inv_eq]
  refine ⟨?_, ?_⟩
  · first
      | simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hg.1
      | simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mul_self_of_mem hg.1
  · first
      | simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hg.1
      | simpa [Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem hg.1

private lemma submatrix_rev_mul_eq_one_of_mul_eq_one (M N : Matrix (Fin n) (Fin n) ℂ) (h : M * N = 1) :
    M.submatrix Fin.rev Fin.rev * N.submatrix Fin.rev Fin.rev = 1 := by
  have e := Matrix.submatrix_mul_equiv M N (Fin.revPerm : Fin n → Fin n) Fin.revPerm
    (Fin.revPerm : Fin n → Fin n)
  rw [h, Matrix.submatrix_one_equiv] at e
  first
    | exact e
    | simpa [Fin.revPerm] using e

theorem gelfand_psM (T : KType ε Λ) (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧ DifferentiableOn ℂ (psM T μ) U ∧
      ∀ z ∈ U, ∀ k : ℕ,
        opGelfand (fun a b => Lhol (Matrix.single a b (1 : ℂ))) k (psM T μ) z =
            ((-1 : ℂ) ^ k * gval (icShift lam) k) • psM T μ z ∧
          opGelfand (fun a b => Lhol (Matrix.single (Fin.rev b) (Fin.rev a) (1 : ℂ))) k (psM T μ) z =
            gval (icShift (-lam)) k • psM T μ z := by
  haveI := compactSpace_KG ε
  obtain ⟨U₀, hU₀o, hpos, -, hdiff, -⟩ := psM_holo T μ
  refine ⟨U₀ ∩ Ps1.Uset ε, hU₀o.inter Ps1.isOpen_Uset,
    fun z hz => ⟨hpos hz, Ps1.posSet_subset_Uset hz⟩, hdiff.mono Set.inter_subset_left,
    fun z hz k => ⟨?_, ?_⟩⟩
  · refine GPs.gelfand_Fint T μ _ k _ (fun g y hy => ?_) hz.2
    have hAB : toMK g⁻¹ * toMK g = 1 := by
      exact (toMK_inv_mul_and_mul_inv g).1
    have hBA : toMK g * toMK g⁻¹ = 1 := by
      exact (toMK_inv_mul_and_mul_inv g).2
    rw [GPs.gelfand_conj isOpen_omega _ (toMK g⁻¹) (toMK g) hAB hBA (toMK g⁻¹)ᵀ (toMK g)ᵀ
      (fun a b => conj_single_lemma _ _ a b)
      (by rw [← Matrix.transpose_mul, hBA, Matrix.transpose_one])
      (by rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]) (phiM_contDiffOn μ) k hy]
    exact (gelfand_phiM μ lam hμ k hy).1
  · refine GPs.gelfand_Fint T μ _ k _ (fun g y hy => ?_) hz.2
    have hAB : toMK g⁻¹ * toMK g = 1 := by
      exact (toMK_inv_mul_and_mul_inv g).1
    have hBA : toMK g * toMK g⁻¹ = 1 := by
      exact (toMK_inv_mul_and_mul_inv g).2
    rw [GPs.gelfand_conj isOpen_omega _ (toMK g⁻¹) (toMK g) hAB hBA
      ((toMK g).submatrix Fin.rev Fin.rev) ((toMK g⁻¹).submatrix Fin.rev Fin.rev)
      (fun a b => mul_single_rev_mul_eq_sum _ _ a b)
      (submatrix_rev_mul_eq_one_of_mul_eq_one _ _ hBA) (submatrix_rev_mul_eq_one_of_mul_eq_one _ _ hAB) (phiM_contDiffOn μ) k hy]
    exact (gelfand_phiM μ lam hμ k hy).2

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsMInfNhd
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

theorem psM_inf_nhd (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧ DifferentiableOn ℂ (psM T μ) U ∧
      ∀ z ∈ U, ∀ Y : Matrix (Fin n) (Fin n) ℂ, IsBlock ε Y →
        fderiv ℂ (psM T μ) z (z * Y) = -(T.dτ Y * psM T μ z) ∧
          fderiv ℂ (psM T μ) z (Y * z) = -(psM T μ z * T.dτ Y) := by
  obtain ⟨U0, hU0o, hpos0, hΩ, hdiff, hfd⟩ := psM_holo (μ := μ) T
  refine ⟨{z | ∃ x : Matrix (Fin n) (Fin n) ℂ, x.PosDef ∧ ∃ r : ℝ, 0 < r ∧ ‖z - x‖ < r ∧
      (∀ w : Matrix (Fin n) (Fin n) ℂ, ‖w - x‖ < 3 * r → w ∈ U0) ∧
      (∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → ‖H‖ < 3 * r → (x + H).PosDef)},
      ?_, ?_, ?_, ?_⟩
  · refine Metric.isOpen_iff.mpr ?_
    rintro z ⟨x, hx, r, hr, hzx, hU, hP⟩
    refine ⟨r - ‖z - x‖, sub_pos.mpr hzx, fun z' hz' => ⟨x, hx, r, hr, ?_, hU, hP⟩⟩
    rw [Metric.mem_ball, dist_eq_norm] at hz'
    have h1 : z' - x = (z' - z) + (z - x) := by abel
    rw [h1]
    have h2 := norm_add_le (z' - z) (z - x)
    linarith
  · intro x hx
    have hx' : x.PosDef := hx
    obtain ⟨δ, hδ, hδP⟩ := IdB.posDef_nhd hx'
    obtain ⟨e, he, heU⟩ := Metric.isOpen_iff.mp hU0o x (hpos0 hx)
    have hm : 0 < min δ e / 3 := div_pos (lt_min hδ he) (by norm_num)
    refine ⟨x, hx', min δ e / 3, hm, by rw [sub_self, norm_zero]; exact hm, ?_, ?_⟩
    · intro w hw
      apply heU
      rw [Metric.mem_ball, dist_eq_norm]
      have : min δ e ≤ e := min_le_right δ e
      linarith
    · intro H hH hHn
      apply hδP H hH
      have : min δ e ≤ δ := min_le_left δ e
      linarith
  · refine hdiff.mono ?_
    intro z hz
    obtain ⟨x, hx, r, hr, hzx, hU, hP⟩ := hz
    exact hU z (by linarith)
  · rintro z ⟨x, hx, r, hr, hzx, hU, hP⟩ Y hY
    have hxH : xᴴ = x := hx.1.eq
    have h12 : star (1 / 2 : ℂ) = 1 / 2 := by
      have h := Complex.conj_ofReal (1 / 2 : ℝ)
      push_cast at h
      exact h
    have hsI : star Complex.I = -Complex.I := Complex.conj_I
    have hn12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) ℂ, A = (1 / 2 : ℂ) • (z + zᴴ) := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℂ,
        B = (1 / 2 : ℂ) • (Complex.I • (zᴴ - z)) := ⟨_, rfl⟩
    have hAH : A.IsHermitian := by
      rw [Matrix.IsHermitian, hA]
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
        star_mul', star_add, star_star, h12]
      ring
    have hBH : B.IsHermitian := by
      rw [Matrix.IsHermitian, hB]
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
        star_mul', star_sub, star_star, h12, hsI]
      ring
    have hAB : A + Complex.I • B = z := by
      rw [hA, hB]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply,
        smul_eq_mul]
      linear_combination ((1 / 2 : ℂ) * (star (z j i) - z i j)) * Complex.I_sq
    have hAx : A - x = (1 / 2 : ℂ) • ((z - x) + (z - x)ᴴ) := by
      rw [hA, Matrix.conjTranspose_sub, hxH]; module
    have hBx : B = (1 / 2 : ℂ) • (Complex.I • ((z - x)ᴴ - (z - x))) := by
      rw [hB, Matrix.conjTranspose_sub, hxH]; module
    have hAn : ‖A - x‖ ≤ ‖z - x‖ := by
      have h := norm_add_le (z - x) (z - x)ᴴ
      rw [Matrix.norm_conjTranspose] at h
      rw [hAx, norm_smul, hn12]
      linarith
    have hBn : ‖B‖ ≤ ‖z - x‖ := by
      have h := norm_sub_le (z - x)ᴴ (z - x)
      rw [Matrix.norm_conjTranspose] at h
      rw [hBx, norm_smul, norm_smul, hn12, Complex.norm_I]
      linarith
    have hbound : ∀ s : ℂ, ‖s‖ < 2 → ‖A + s • B - x‖ < 3 * r := by
      intro s hs
      have e1 : A + s • B - x = (A - x) + s • B := by abel
      rw [e1]
      have h1 := norm_add_le (A - x) (s • B)
      rw [norm_smul] at h1
      have h2 : ‖s‖ * ‖B‖ ≤ 2 * ‖z - x‖ := mul_le_mul hs.le hBn (norm_nonneg _) (by norm_num)
      linarith
    have key : ∀ s : ℂ, ‖s‖ < 2 → A + s • B ∈ U0 := fun s hs => hU _ (hbound s hs)
    have hposR : ∀ t : ℝ, |t| < 2 → (A + (t : ℂ) • B).PosDef := by
      intro t ht
      have hs : ‖(t : ℂ)‖ < 2 := by rwa [Complex.norm_real, Real.norm_eq_abs]
      have hBt : ((t : ℂ) • B).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hBH.eq]
        rw [show star (t : ℂ) = (t : ℂ) from Complex.conj_ofReal t]
      have hH : (A + (t : ℂ) • B - x).IsHermitian := (hAH.add hBt).sub hx.1
      have := hP _ hH (hbound _ hs)
      simpa using this
    have hI : ‖Complex.I‖ < 2 := by rw [Complex.norm_I]; norm_num
    constructor
    · let g : ℂ → (T.V →L[ℂ] T.V) := fun s =>
        ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          (∫ k, IdA.dPhi2 μ (toMK k⁻¹ * (A + s • B) * toMK k,
            toMK k⁻¹ * (A * Y + s • (B * Y)) * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))
          + T.dτ Y * psM T μ (A + s • B)
      have hgeq : ∀ s : ℂ, A + s • B ∈ U0 →
          g s = fderiv ℂ (psM T μ) (A + s • B) ((A + s • B) * Y) + T.dτ Y * psM T μ (A + s • B) := by
        intro s hs
        rw [hfd _ hs]
        simp only [g, add_mul, Matrix.smul_mul] <;> rfl
      have hgd : ∀ s : ℂ, ‖s‖ < 2 → DifferentiableAt ℂ g s := by
        intro s hs
        have hw : DifferentiableAt ℂ (fun y : ℂ => A + y • B) s :=
          (differentiableAt_const A).add (differentiableAt_id.smul_const B)
        have hψ := (hdiff.differentiableAt (hU0o.mem_nhds (key s hs))).comp s hw
        exact ((line_int_differentiableAt T μ hU0o hΩ A B (A * Y) (B * Y) (key s hs)).const_smul
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))).add (hψ.const_mul (T.dτ Y))
      have hgr : ∀ t : ℝ, |t| < 2 → g t = 0 := by
        intro t ht
        have hs : ‖(t : ℂ)‖ < 2 := by rwa [Complex.norm_real, Real.norm_eq_abs]
        rw [hgeq _ (key _ hs), (psM_inf_right T μ hμ (hposR t ht) hY).1]
        simp
      have h0 := IdB.line_zero g hgd hgr
      rw [hgeq _ (key _ hI), hAB] at h0
      exact eq_neg_of_add_eq_zero_left h0
    · let g : ℂ → (T.V →L[ℂ] T.V) := fun s =>
        ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          (∫ k, IdA.dPhi2 μ (toMK k⁻¹ * (A + s • B) * toMK k,
            toMK k⁻¹ * (Y * A + s • (Y * B)) * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))
          + psM T μ (A + s • B) * T.dτ Y
      have hgeq : ∀ s : ℂ, A + s • B ∈ U0 →
          g s = fderiv ℂ (psM T μ) (A + s • B) (Y * (A + s • B)) + psM T μ (A + s • B) * T.dτ Y := by
        intro s hs
        rw [hfd _ hs]
        simp only [g, mul_add, Matrix.mul_smul] <;> rfl
      have hgd : ∀ s : ℂ, ‖s‖ < 2 → DifferentiableAt ℂ g s := by
        intro s hs
        have hw : DifferentiableAt ℂ (fun y : ℂ => A + y • B) s :=
          (differentiableAt_const A).add (differentiableAt_id.smul_const B)
        have hψ := (hdiff.differentiableAt (hU0o.mem_nhds (key s hs))).comp s hw
        exact ((line_int_differentiableAt T μ hU0o hΩ A B (Y * A) (Y * B) (key s hs)).const_smul
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))).add (hψ.mul_const (T.dτ Y))
      have hgr : ∀ t : ℝ, |t| < 2 → g t = 0 := by
        intro t ht
        have hs : ‖(t : ℂ)‖ < 2 := by rwa [Complex.norm_real, Real.norm_eq_abs]
        rw [hgeq _ (key _ hs), (psM_inf_right T μ hμ (hposR t ht) hY).2]
        simp
      have h0 := IdB.line_zero g hgd hgr
      rw [hgeq _ (key _ hI), hAB] at h0
      exact eq_neg_of_add_eq_zero_left h0

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

