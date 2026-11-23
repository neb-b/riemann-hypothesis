module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFormCoeffSeqDirichletTwistLevelMulSq
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.CharTwist

lemma exists_coeffs {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) :
    ∃ c : ZMod M → ℂ, (∀ n : ZMod M, ∑ u, c u * ZMod.stdAddChar (u * n) = ψ n) ∧
      ∀ d u : ZMod M, IsUnit d → c u = ψ d * c (d * u) := by
  refine ⟨fun u => (M : ℂ)⁻¹ * ZMod.dft (fun j => ψ j) u, fun n => ?_, fun d u hd => ?_⟩
  · have h := ZMod.invDFT_apply (ZMod.dft (fun j => ψ j)) n
    rw [LinearEquiv.symm_apply_apply] at h
    rw [h, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_eq_mul]; ring
  · obtain ⟨d, rfl⟩ := hd
    have h := ZMod.dft_comp_unitMul (fun j => ψ j) d (d * u)
    simp only [map_mul] at h
    rw [ZMod.dft_const_mul, Units.inv_mul_cancel_left] at h
    simp only [← h]; ring

lemma summable_of_polyB {a : ℕ → ℂ} (h : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * τ) := by
  obtain ⟨C, A, hC⟩ := h
  set q : ℂ := cexp (2 * π * Complex.I * τ) with hq
  have hq1 : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
  have hq0 : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 (Complex.exp_ne_zero _)
  have h1 : Summable fun n : ℕ => (n : ℝ) ^ A * ‖q‖ ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one A (by rwa [norm_norm])
  have h2 := ((summable_nat_add_iff 1).2 h1).mul_left (C * ‖q‖⁻¹)
  refine Summable.of_norm_bounded h2 fun n => ?_
  have e : cexp (2 * π * Complex.I * n * τ) = q ^ n := by
    rw [hq, ← Complex.exp_nat_mul]; congr 1; ring
  rw [e, norm_mul, norm_pow]
  calc ‖a n‖ * ‖q‖ ^ n ≤ C * ((n : ℝ) + 1) ^ A * ‖q‖ ^ n :=
        mul_le_mul_of_nonneg_right (hC n) (by positivity)
    _ = _ := by push_cast; field_simp; ring

lemma qs_twist {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) {c : ZMod M → ℂ}
    (hc : ∀ n : ZMod M, ∑ u, c u * ZMod.stdAddChar (u * n) = ψ n) {g : ℕ → ℂ} (hg : PolyB g) (τ : ℍ) :
    qs (fun n => ψ n * g n) τ = ∑ u : ZMod M, c u * qs g ((((u.val : ℤ) : ℝ) / M) +ᵥ τ) := by
  have a := hasSum_sum (s := Finset.univ) fun (u : ZMod M) _ =>
    (summable_of_polyB hg ((((u.val : ℤ) : ℝ) / M) +ᵥ τ)).hasSum.mul_left (c u)
  unfold qs
  rw [← a.tsum_eq]
  refine tsum_congr fun m => ?_
  beta_reduce
  rw [← hc, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  have : u * (m : ZMod M) = ((u.val * m : ℤ) : ZMod M) := by simp
  have e2 : ZMod.stdAddChar (u * (m : ZMod M)) * cexp (2 * π * Complex.I * m * τ) =
      cexp (2 * π * Complex.I * m * (((((u.val : ℤ) : ℝ) / M) +ᵥ τ : ℍ) : ℂ)) := by
    rw [this, ZMod.stdAddChar_coe, ← Complex.exp_add, coe_vadd]
    congr 1
    push_cast
    ring
  rw [← e2]
  ring

lemma vadd_smul {N M : ℕ} [NeZero M] (γ : SL(2, ℤ)) (hγ : ((N * M ^ 2 : ℕ) : ℤ) ∣ γ 1 0) (u v : ℤ)
    (h : (v : ZMod M) = ((γ 1 1 : ℤ) : ZMod M) ^ 2 * u) (τ : ℍ) :
    ∃ δ : SL(2, ℤ), (N : ℤ) ∣ δ 1 0 ∧ ((δ 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) ∧
      ((u : ℝ) / M) +ᵥ (γ • τ) = δ • (((v : ℝ) / M) +ᵥ τ) ∧
      ((δ 1 0 : ℤ) : ℂ) * ((((v : ℝ) / M) +ᵥ τ : ℍ) : ℂ) + ((δ 1 1 : ℤ) : ℂ) =
        ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
  obtain ⟨c, hc⟩ := hγ
  push_cast at hc
  have hd := γ.det_coe
  rw [Matrix.det_fin_two, hc] at hd
  have hd' := congrArg (Int.cast : ℤ → ZMod M) hd
  push_cast at hd'
  rw [ZMod.natCast_self] at hd'
  have h1 : (M : ℤ) ∣ u * γ 1 1 - v * γ 0 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h]
    linear_combination (-(u : ZMod M) * ((γ 1 1 : ℤ) : ZMod M)) * hd'
  obtain ⟨e, he⟩ := h1
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  obtain ⟨δ, d00, d01, d10, d11⟩ : ∃ δ : SL(2, ℤ), δ 0 0 = γ 0 0 + u * N * c * M ∧
      δ 0 1 = γ 0 1 + e - u * v * N * c ∧ δ 1 0 = N * M ^ 2 * c ∧ δ 1 1 = γ 1 1 - N * c * v * M := by
    refine ⟨⟨!![γ 0 0 + u * N * c * M, γ 0 1 + e - u * v * N * c; N * M ^ 2 * c, γ 1 1 - N * c * v * M], ?_⟩,
      rfl, rfl, rfl, rfl⟩
    rw [Matrix.det_fin_two_of]
    linear_combination hd + N * M * c * he
  have hden : ((δ 1 0 : ℤ) : ℂ) * ((((v : ℝ) / M) +ᵥ τ : ℍ) : ℂ) + ((δ 1 1 : ℤ) : ℂ) =
        ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    rw [d10, d11, hc, coe_vadd]
    push_cast
    field_simp
    ring
  refine ⟨δ, ⟨M ^ 2 * c, by rw [d10]; ring⟩, by rw [d11]; simp, ?_, hden⟩
  apply UpperHalfPlane.ext
  have e1 := UpperHalfPlane.coe_specialLinearGroup_apply γ τ
  have e2 := UpperHalfPlane.coe_specialLinearGroup_apply δ (((v : ℝ) / M) +ᵥ τ)
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast] at e1 e2
  have hz := UpperHalfPlane.denom_ne_zero γ τ
  rw [UpperHalfPlane.denom] at hz
  simp at hz
  have he' : (u : ℂ) * (γ 1 1 : ℤ) - v * (γ 0 0 : ℤ) = M * e := by exact_mod_cast he
  have hc' : ((γ 1 0 : ℤ) : ℂ) = N * M ^ 2 * c := by exact_mod_cast hc
  rw [coe_vadd, e1, e2, hden, eq_div_iff hz, add_mul, div_mul_cancel₀ _ hz, d00, d01, coe_vadd, hc']
  push_cast
  field_simp
  linear_combination he'

theorem cf_twist : ∀ (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ), 0 < M →
    CF k N (ch χ) g → CF k (N * M ^ 2) (fun d => ch χ d * ch φ d ^ 2) (fun n => φ n * g n) := by
  intro k N M χ φ g hM ⟨⟨hp, hi⟩, B, hB⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨c, hc1, hc2⟩ := exists_coeffs φ
  refine ⟨⟨?_, ?_⟩, (∑ u, ‖c u‖ ^ 2) * ∑ _u : ZMod M, B, fun τ => ?_⟩
  · obtain ⟨C, A, hC⟩ := hp
    refine ⟨C, A, fun n => le_trans ?_ (hC n)⟩
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one φ _)
  · intro γ hγ τ
    have hu : IsUnit ((γ 1 1 : ℤ) : ZMod M) := by
      obtain ⟨e, he⟩ := hγ
      have dγ := congrArg (Int.cast : ℤ → ZMod M) (γ.det_coe)
      rw [Matrix.det_fin_two, he] at dγ
      push_cast at dγ
      rw [ZMod.natCast_self] at dγ
      exact IsUnit.of_mul_eq_one ((γ 0 0 : ℤ) : ZMod M) (by linear_combination dγ)
    have hb : Function.Bijective fun u : ZMod M => ((γ 1 1 : ℤ) : ZMod M) ^ 2 * u :=
      ((hu.pow 2).unit.mulLeft).bijective
    rw [qs_twist φ hc1 hp, qs_twist φ hc1 hp,
      ← hb.sum_comp fun u : ZMod M => c u * qs g ((((u.val : ℤ) : ℝ) / M) +ᵥ τ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    obtain ⟨δ, h0, h1, h2, h3⟩ := vadd_smul γ hγ (u.val : ℤ) ((((γ 1 1 : ℤ) : ZMod M) ^ 2 * u).val : ℤ)
      (by simp) τ
    rw [h2, hi δ h0, h3, hc2 _ u (hu.pow 2)]
    simp only [ch, h1, map_pow]
    ring
  · rw [qs_twist φ hc1 hp]
    have hy : 0 ≤ τ.im ^ k := pow_nonneg τ.im_pos.le k
    set x : ZMod M → ℂ := fun u => qs g ((((u.val : ℤ) : ℝ) / M) +ᵥ τ) with hx
    have h1 : ‖∑ u, c u * x u‖ ≤ ∑ u, ‖c u‖ * ‖x u‖ :=
      (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun u _ => norm_mul _ _)
    have h2 : ‖∑ u, c u * x u‖ ^ 2 ≤ (∑ u, ‖c u‖ ^ 2) * ∑ u, ‖x u‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
    refine (mul_le_mul_of_nonneg_right h2 hy).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun u _ => sq_nonneg _)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun u _ => ?_
    have := hB ((((u.val : ℤ) : ℝ) / M) +ᵥ τ)
    rwa [vadd_im] at this

end GlobalTheory.EisM.CharTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepLowerLevel
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma repL_det (L q : ℕ) (i : Option (Fin q)) : (repL L q i).det = q := by
  cases i <;> simp [repL, Matrix.det_fin_two_of]

lemma gamma0_lower_dvd {L : ℕ} (γ : Gamma0 L) : (L : ℤ) ∣ ((γ : SL(2, ℤ)) : M2) 1 0 := by
  have := Gamma0_mem.mp γ.2
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast this)

lemma exists_kernel_param {K : Type*} [Field K] (a b c d l : K) (hl : l ≠ 0)
    (hdet : a * d - b * c = 0) (hbd : b ≠ 0 ∨ d ≠ 0) : ∃ u, a = l * u * b ∧ c = l * u * d := by
  by_cases hd : d = 0
  · have hb : b ≠ 0 := hbd.resolve_right (by simpa using hd)
    refine ⟨a / (l * b), by field_simp, ?_⟩
    subst hd
    have : b * c = 0 := by linear_combination -hdet
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hb
    · simp [h]
  · refine ⟨c / (l * d), ?_, by field_simp⟩
    field_simp
    linear_combination hdet

theorem repL_LRep : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → LRep L (DT L q) (repL L q) := by
  intro L q hq hqL
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hqLZ : ¬ (q : ℤ) ∣ L := by exact_mod_cast hqL
  haveI := Fact.mk hq
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨γ, i⟩ -
    refine ⟨?_, ?_⟩
    · simp [Matrix.det_mul, repL_det]
    · have h := gamma0_lower_dvd γ
      cases i with
      | none => simpa [repL, Matrix.mul_apply, Fin.sum_univ_two] using h
      | some j =>
        simp only [repL, Matrix.mul_apply, Fin.sum_univ_two]
        simp
        exact dvd_add (dvd_mul_of_dvd_left h _) (Dvd.dvd.mul_left (dvd_mul_right _ _) _)
  · rintro ⟨γ, i⟩ - ⟨γ', i'⟩ - h
    dsimp only at h
    have hd := (γ : SL(2, ℤ)).2
    have hd' := (γ' : SL(2, ℤ)).2
    rw [Matrix.det_fin_two] at hd hd'
    have e00 := congrFun (congrFun h 0) 0
    have e01 := congrFun (congrFun h 0) 1
    have e10 := congrFun (congrFun h 1) 0
    have e11 := congrFun (congrFun h 1) 1
    have hq0' : q ≠ 0 := hq.ne_zero
    have hq1 : ¬ (q : ℤ) ∣ 1 := hqZ.not_dvd_one
    rcases i with _ | j <;> rcases i' with _ | j' <;>
      simp [repL, Matrix.mul_apply, Fin.sum_univ_two, hq0'] at e00 e01 e10 e11
    · refine Prod.ext (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)) rfl
      fin_cases i <;> fin_cases j <;> simp <;> assumption
    · exact absurd (Dvd.intro (((γ' : SL(2, ℤ)) : M2) 0 0 * ((γ : SL(2, ℤ)) : M2) 1 1 -
          ((γ : SL(2, ℤ)) : M2) 0 1 * ((γ' : SL(2, ℤ)) : M2) 1 0)
        (by linear_combination hd' + ((γ' : SL(2, ℤ)) : M2) 0 0 * e11 - ((γ' : SL(2, ℤ)) : M2) 1 0 * e01)) hq1
    · exact absurd (Dvd.intro (((γ : SL(2, ℤ)) : M2) 0 0 * ((γ' : SL(2, ℤ)) : M2) 1 1 -
          ((γ' : SL(2, ℤ)) : M2) 0 1 * ((γ : SL(2, ℤ)) : M2) 1 0)
        (by linear_combination hd - ((γ : SL(2, ℤ)) : M2) 0 0 * e11 + ((γ : SL(2, ℤ)) : M2) 1 0 * e01)) hq1
    · have h0 : (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) * ((γ : SL(2, ℤ)) : M2) 0 1 :=
        Dvd.intro (((γ' : SL(2, ℤ)) : M2) 0 0 - ((γ : SL(2, ℤ)) : M2) 0 0)
          (by linear_combination -e00 + ((L : ℤ) * ((j' : ℕ) : ℤ)) * e01)
      have h1 : (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) * ((γ : SL(2, ℤ)) : M2) 1 1 :=
        Dvd.intro (((γ' : SL(2, ℤ)) : M2) 1 0 - ((γ : SL(2, ℤ)) : M2) 1 0)
          (by linear_combination -e10 + ((L : ℤ) * ((j' : ℕ) : ℤ)) * e11)
      have hjj : (q : ℤ) ∣ ((j : ℕ) - (j' : ℕ) : ℤ) := by
        by_contra hn
        have hLj : ¬ (q : ℤ) ∣ (L : ℤ) * ((j : ℕ) - (j' : ℕ) : ℤ) := fun hh =>
          (hqZ.dvd_or_dvd hh).elim hqLZ hn
        have a0 := (hqZ.dvd_or_dvd h0).resolve_left hLj
        have a1 := (hqZ.dvd_or_dvd h1).resolve_left hLj
        apply hq1
        rw [← hd]
        exact (Dvd.dvd.mul_left a1 _).sub (Dvd.dvd.mul_right a0 _)
      have hj := j.isLt
      have hj' := j'.isLt
      have hz := Int.eq_zero_of_abs_lt_dvd hjj (abs_sub_lt_iff.mpr ⟨by omega, by omega⟩)
      have hjeq : j = j' := Fin.ext (by omega)
      subst hjeq
      refine Prod.ext (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i k => ?_)) rfl
      have f00 : ((γ : SL(2, ℤ)) : M2) 0 0 = ((γ' : SL(2, ℤ)) : M2) 0 0 :=
        mul_right_cancel₀ hq0 (by linear_combination e00 - ((L : ℤ) * ((j : ℕ) : ℤ)) * e01)
      have f10 : ((γ : SL(2, ℤ)) : M2) 1 0 = ((γ' : SL(2, ℤ)) : M2) 1 0 :=
        mul_right_cancel₀ hq0 (by linear_combination e10 - ((L : ℤ) * ((j : ℕ) : ℤ)) * e11)
      fin_cases i <;> fin_cases k <;> simp <;> assumption
  · rintro δ ⟨hdet, hL⟩
    rw [Matrix.det_fin_two] at hdet
    by_cases hbd : (q : ℤ) ∣ δ 0 1 ∧ (q : ℤ) ∣ δ 1 1
    · obtain ⟨⟨b', hb⟩, ⟨d', hd⟩⟩ := hbd
      have hdet1 : (!![δ 0 0, b'; δ 1 0, d'] : M2).det = 1 := by
        rw [Matrix.det_fin_two_of]
        apply mul_left_cancel₀ hq0
        rw [hb, hd] at hdet
        linear_combination hdet
      let g : SL(2, ℤ) := ⟨_, hdet1⟩
      have hg : g ∈ Gamma0 L := by
        rw [Gamma0_mem]
        have : ((δ 1 0 : ℤ) : ZMod L) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hL
        simpa [g] using this
      refine ⟨(⟨g, hg⟩, none), trivial, ?_⟩
      ext i k
      fin_cases i <;> fin_cases k <;> simp [g, repL, Matrix.mul_apply, Fin.sum_univ_two, hb, hd] <;> ring
    · have hu : ∃ u : ZMod q, ((δ 0 0 : ℤ) : ZMod q) = (L : ZMod q) * u * ((δ 0 1 : ℤ) : ZMod q) ∧
          ((δ 1 0 : ℤ) : ZMod q) = (L : ZMod q) * u * ((δ 1 1 : ℤ) : ZMod q) := by
        apply exists_kernel_param
        · rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqL
        · have := congrArg (fun x : ℤ => (x : ZMod q)) hdet
          simpa using this
        · by_contra hn
          push_neg at hn
          exact hbd ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn.1,
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn.2⟩
      obtain ⟨u, hu0, hu1⟩ := hu
      set j : Fin q := ⟨u.val, ZMod.val_lt u⟩ with hjdef
      have hju : (((j : ℕ) : ℤ) : ZMod q) = u := by simp [hjdef]
      obtain ⟨x, hx⟩ : (q : ℤ) ∣ δ 0 0 - L * (j : ℕ) * δ 0 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast at hju ⊢
        rw [hju, hu0]; ring
      obtain ⟨z, hz⟩ : (q : ℤ) ∣ δ 1 0 - L * (j : ℕ) * δ 1 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast at hju ⊢
        rw [hju, hu1]; ring
      have hcop : IsCoprime (L : ℤ) (q : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqL).symm
      have hLz : (L : ℤ) ∣ z := by
        apply hcop.dvd_of_dvd_mul_left
        rw [← hz]
        exact dvd_sub hL (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _)
      have hdet1 : (!![x, δ 0 1; z, δ 1 1] : M2).det = 1 := by
        rw [Matrix.det_fin_two_of]
        apply mul_left_cancel₀ hq0
        linear_combination -(δ 1 1) * hx + δ 0 1 * hz + hdet
      let g : SL(2, ℤ) := ⟨_, hdet1⟩
      have hg : g ∈ Gamma0 L := by
        rw [Gamma0_mem]
        have : ((z : ℤ) : ZMod L) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hLz
        simpa [g] using this
      refine ⟨(⟨g, hg⟩, some j), trivial, ?_⟩
      ext i k
      fin_cases i <;> fin_cases k <;> simp [g, repL, Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | linear_combination -hx | linear_combination -hz

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepTOperator
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.LRepTriangular

theorem firstCol_ne_zero (q : ℕ) [Fact q.Prime] (γ : SL(2, ℤ))
    (h0 : (((γ : M2) 0 0 : ℤ) : ZMod q) = 0) (h1 : (((γ : M2) 1 0 : ℤ) : ZMod q) = 0) : False := by
  have hd : (γ : M2).det = 1 := γ.2
  rw [Matrix.det_fin_two] at hd
  have := congrArg (fun x : ℤ => (x : ZMod q)) hd
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, h0, h1] at this
  simp at this

end GlobalTheory.EisM.LRepTriangular

namespace GlobalTheory.EisM


open GlobalTheory.EisM.LRepTriangular in
theorem lRep_DT_repT : ∀ L q : ℕ, q.Prime → ¬ q ∣ L → LRep L (DT L q) (repT q) := by
  intro L q hq hqL
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨γ, x⟩ -
    have hγ := γ.2
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
    refine ⟨?_, ?_⟩
    · show (((γ : SL(2, ℤ)) : M2) * repT q x).det = q
      rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul]
      cases x <;> simp [repT, repU, Matrix.det_fin_two_of]
    · show (L : ℤ) ∣ (((γ : SL(2, ℤ)) : M2) * repT q x) 1 0
      cases x <;> simp [repT, repU, Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | exact hγ | exact Dvd.dvd.mul_right hγ _
  · rintro ⟨γ, x⟩ - ⟨γ', y⟩ - h
    simp only at h
    have e : ∀ i k, (((γ : SL(2, ℤ)) : M2) * repT q x) i k = (((γ' : SL(2, ℤ)) : M2) * repT q y) i k :=
      fun i k => by rw [h]
    have hxy : x = y := by
      cases x with
      | none =>
        cases y with
        | none => rfl
        | some j' =>
          exfalso
          have e00 := e 0 0; have e10 := e 1 0
          simp [repT, repU, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
          apply firstCol_ne_zero q (γ' : SL(2, ℤ))
          · rw [← e00]; push_cast; simp
          · rw [← e10]; push_cast; simp
      | some j =>
        cases y with
        | none =>
          exfalso
          have e00 := e 0 0; have e10 := e 1 0
          simp [repT, repU, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
          apply firstCol_ne_zero q (γ : SL(2, ℤ))
          · rw [e00]; push_cast; simp
          · rw [e10]; push_cast; simp
        | some j' =>
          have e00 := e 0 0; have e10 := e 1 0; have e01 := e 0 1; have e11 := e 1 1
          simp [repT, repU, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10 e01 e11
          have c01 := congrArg (fun z : ℤ => (z : ZMod q)) e01
          have c11 := congrArg (fun z : ℤ => (z : ZMod q)) e11
          push_cast at c01 c11
          simp only [ZMod.natCast_self, mul_zero, add_zero, e00, e10] at c01 c11
          by_cases hJ : ((j : ℕ) : ZMod q) = ((j' : ℕ) : ZMod q)
          · rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt j'.isLt] at hJ
            rw [Fin.ext hJ]
          · exfalso
            have hs : ((j : ℕ) : ZMod q) - ((j' : ℕ) : ZMod q) ≠ 0 := sub_ne_zero.mpr hJ
            apply firstCol_ne_zero q (γ' : SL(2, ℤ))
            · have : (((γ' : SL(2, ℤ)) : M2) 0 0 : ZMod q) * (((j : ℕ) : ZMod q) - ((j' : ℕ) : ZMod q)) = 0 := by
                rw [mul_sub, c01, sub_self]
              exact (mul_eq_zero.mp this).resolve_right hs
            · have : (((γ' : SL(2, ℤ)) : M2) 1 0 : ZMod q) * (((j : ℕ) : ZMod q) - ((j' : ℕ) : ZMod q)) = 0 := by
                rw [mul_sub, c11, sub_self]
              exact (mul_eq_zero.mp this).resolve_right hs
    subst hxy
    have hm : ((γ : SL(2, ℤ)) : M2) = ((γ' : SL(2, ℤ)) : M2) := by
      have h2 := congrArg (· * (repT q x).adjugate) h
      simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h2
      have hdet : (repT q x).det = q := by cases x <;> simp [repT, repU, Matrix.det_fin_two_of]
      rw [hdet] at h2
      exact smul_right_injective M2 hq0 h2
    exact Prod.ext (Subtype.ext (Subtype.ext hm)) rfl
  · rintro δ ⟨hdet, hL⟩
    obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ℤ, δ = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two δ⟩
    simp [Matrix.det_fin_two_of] at hdet hL
    by_cases hac : (q : ℤ) ∣ a ∧ (q : ℤ) ∣ c
    · obtain ⟨⟨a', ha⟩, ⟨c', hc⟩⟩ := hac
      subst ha hc
      have hdet' : a' * d - b * c' = 1 := by
        apply mul_left_cancel₀ hq0; linear_combination hdet
      have hcop : IsCoprime (L : ℤ) (q : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqL))
      have hLc : (L : ℤ) ∣ c' := hcop.dvd_of_dvd_mul_left hL
      let g : SL(2, ℤ) := ⟨!![a', b; c', d], by rw [Matrix.det_fin_two_of]; exact hdet'⟩
      have hg : g ∈ Gamma0 L := by
        rw [Gamma0_mem]; simpa [g] using (ZMod.intCast_zmod_eq_zero_iff_dvd c' L).mpr hLc
      refine ⟨(⟨g, hg⟩, none), trivial, ?_⟩
      ext i k; fin_cases i <;> fin_cases k <;> simp [g, repT, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    · have hd0 : (a : ZMod q) * d - b * c = 0 := by
        have := congrArg (fun x : ℤ => (x : ZMod q)) hdet
        push_cast at this; simpa using this
      obtain ⟨J, hb, hd⟩ : ∃ J : ZMod q, (b : ZMod q) = (a : ZMod q) * J ∧ (d : ZMod q) = (c : ZMod q) * J := by
        by_cases ha : (a : ZMod q) = 0
        · have hc : (c : ZMod q) ≠ 0 := fun hc => hac
            ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ha, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc⟩
          refine ⟨d / c, ?_, ?_⟩
          · rw [ha, zero_mul]; rw [ha, zero_mul, zero_sub, neg_eq_zero] at hd0
            exact (mul_eq_zero.mp hd0).resolve_right hc
          · field_simp
        · refine ⟨b / a, ?_, ?_⟩
          · field_simp
          · field_simp; linear_combination hd0
      obtain ⟨u, hu⟩ : (q : ℤ) ∣ b - a * ((J.val : ℕ) : ℤ) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ZMod.natCast_zmod_val, hb]; ring
      obtain ⟨v, hv⟩ : (q : ℤ) ∣ d - c * ((J.val : ℕ) : ℤ) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ZMod.natCast_zmod_val, hd]; ring
      have hdet' : a * v - u * c = 1 := by
        apply mul_left_cancel₀ hq0; linear_combination hdet - a * hv + c * hu
      let g : SL(2, ℤ) := ⟨!![a, u; c, v], by rw [Matrix.det_fin_two_of]; exact hdet'⟩
      have hg : g ∈ Gamma0 L := by
        rw [Gamma0_mem]; simpa [g] using (ZMod.intCast_zmod_eq_zero_iff_dvd c L).mpr hL
      refine ⟨(⟨g, hg⟩, some ⟨J.val, ZMod.val_lt J⟩), trivial, ?_⟩
      ext i k; fin_cases i <;> fin_cases k <;> simp [g, repT, repU, Matrix.mul_apply, Fin.sum_univ_two, -ZMod.natCast_val] <;> linarith

end GlobalTheory.EisM
end

