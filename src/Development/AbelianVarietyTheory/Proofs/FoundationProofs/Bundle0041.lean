module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSmulInvOfMulTendstoInvertibleMatrix
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem tendsto_smul_inv_of_mul_tendsto_invertible (r : ℕ) (A U : ℍ → Matrix (Fin r) (Fin r) ℂ)
    (L : Matrix (Fin r) (Fin r) ℂ) (d : ℍ → ℂ) (hL : L.det ≠ 0)
    (hAU : Tendsto (fun τ => A τ * U τ) atImInfty (𝓝 L))
    (hdU : Tendsto (fun τ => d τ • U τ) atImInfty (𝓝 0)) :
    Tendsto (fun τ => d τ • (A τ)⁻¹) atImInfty (𝓝 0) := by
  have hdet : Tendsto (fun τ => (A τ * U τ).det) atImInfty (𝓝 L.det) :=
    ((continuous_id.matrix_det).tendsto L).comp hAU
  have hev : ∀ᶠ τ in atImInfty, (A τ * U τ).det ≠ 0 := hdet.eventually_ne hL

  have hinvdet : Tendsto (fun τ => Ring.inverse (A τ * U τ).det) atImInfty (𝓝 (Ring.inverse L.det)) := by
    simp only [Ring.inverse_eq_inv']
    exact hdet.inv₀ hL
  have hadj : Tendsto (fun τ => (A τ * U τ).adjugate) atImInfty (𝓝 L.adjugate) :=
    ((continuous_id.matrix_adjugate).tendsto L).comp hAU
  have hinv : Tendsto (fun τ => (A τ * U τ)⁻¹) atImInfty (𝓝 L⁻¹) := by
    simp only [Matrix.inv_def]
    exact hinvdet.smul hadj
  have hlim : Tendsto (fun τ => (d τ • U τ) * (A τ * U τ)⁻¹) atImInfty (𝓝 0) := by
    have := hdU.mul hinv
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [hev] with τ hτ
  have hu : IsUnit (A τ * U τ).det := isUnit_iff_ne_zero.mpr hτ
  have h1 : A τ * (U τ * (A τ * U τ)⁻¹) = 1 := by
    rw [← mul_assoc]; exact Matrix.mul_nonsing_inv _ hu
  rw [Matrix.inv_eq_right_inv h1, Matrix.smul_mul]

end GlobalTheory.OddFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeMulCardOddFrameWeightsDvdThree
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame.ThirdDiv

def uEl : SL(2, ℤ) := ⟨!![0, -1; 1, 1], by norm_num [Matrix.det_fin_two_of]⟩

noncomputable def μ : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

theorem μ_sq : μ ^ 2 = μ - 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [μ, pow_two] <;> nlinarith [h3]

theorem coe_ρ : (ρ : ℂ) = μ - 1 := by
  apply Complex.ext <;> simp [μ, UpperHalfPlane.ρ] <;> norm_num

theorem μ_ne : μ ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [μ] at this

theorem denom_uEl : denom (uEl : GL (Fin 2) ℝ) ρ = μ := by
  simp only [denom, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
  simp [uEl, coe_ρ]

theorem uEl_smul_ρ : uEl • ρ = ρ := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  simp [uEl, coe_ρ]
  rw [div_eq_iff (by simpa using μ_ne), neg_eq_iff_eq_neg]
  linear_combination μ_sq

theorem re_μ_zpow {w : ℤ} (hw : Odd w) :
    (μ ^ (-w)).re = if (3 : ℤ) ∣ w then -1 else 1 / 2 := by
  have h3 : μ ^ 3 = -1 := by linear_combination (μ + 1) * μ_sq
  have h5 : μ ^ 5 = 1 - μ := by linear_combination μ ^ 2 * h3 - μ_sq
  have h6 : μ ^ (6 : ℤ) = 1 := by
    rw [zpow_ofNat]; linear_combination (μ ^ 3 - 1) * h3
  have key : ∀ q t : ℤ, μ ^ (6 * q + t) = μ ^ t := fun q t => by
    rw [zpow_add₀ μ_ne, zpow_mul, h6, one_zpow, one_mul]
  have hre : μ.re = 1 / 2 := rfl
  obtain ⟨m, hm⟩ := hw
  have hc : -w = 6 * (-w / 6) + 1 ∨ -w = 6 * (-w / 6) + 3 ∨ -w = 6 * (-w / 6) + 5 := by omega
  rcases hc with h | h | h
  · rw [if_neg (by omega), h, key, zpow_one, hre]
  · rw [if_pos (by omega), h, key, zpow_ofNat, h3]; simp
  · rw [if_neg (by omega), h, key, zpow_ofNat, h5, Complex.sub_re, hre]; norm_num

theorem not_fixed {N : ℕ} (hN : 5 ≤ N) {γ x : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) :
    ¬ (x * uEl = γ * x ∨ x * uEl = -(γ * x)) := by
  obtain ⟨h0, h1, -⟩ := (CongruenceSubgroup.Gamma1_mem N γ).1 hγ
  have htr : ((x * uEl * x⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel_left]
    simp [uEl, Matrix.trace_fin_two]
  rintro (h | h)
  · rw [h, mul_inv_cancel_right, Matrix.trace_fin_two] at htr
    have h2 := congrArg (Int.cast : ℤ → ZMod N) htr
    push_cast at h2
    have h3 : ((1 : ℕ) : ZMod N) = 0 := by
      push_cast; linear_combination h2 - h0 - h1
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).1 h3)
    omega
  · rw [h, neg_mul, mul_inv_cancel_right, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg,
      Matrix.trace_fin_two] at htr
    have h2 := congrArg (Int.cast : ℤ → ZMod N) htr
    push_cast at h2
    have h3 : ((3 : ℕ) : ZMod N) = 0 := by
      push_cast; linear_combination - h2 - h0 - h1
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).1 h3)
    omega

theorem three_mul_card_dvd (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (hN : 5 ≤ N) (hΓ : Γ ≤ CongruenceSubgroup.Gamma1 N) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (hdet : (evM s w F ρ).det ≠ 0) :
    3 * (Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card = r := by
  classical
  obtain ⟨π, hπ⟩ := hs.exists_perm uEl
  have hε : ∀ i, ∃ ε : ℂ, ∀ j, evM s w F ρ i j * μ ^ (-w j) = ε * evM s w F ρ (π i) j := by
    intro i
    have h0 : ∀ j, (F j ∣[w j] (s i * uEl)) ρ = evM s w F ρ i j * μ ^ (-w j) := fun j => by
      rw [slash_mul_apply, uEl_smul_ρ, denom_uEl]; rfl
    obtain ⟨γ, hγ, h | h⟩ := hπ i
    · refine ⟨1, fun j => ?_⟩
      rw [← h0, h, (hF j).2.slash_mul hγ, one_mul]; rfl
    · refine ⟨-1, fun j => ?_⟩
      rw [← h0, h, slash_neg_of_odd (hF j).1, (hF j).2.slash_mul hγ, neg_one_mul]; rfl
  choose ε hε using hε
  have hne : ∀ i, π i ≠ i := fun i hi => by
    obtain ⟨γ, hγ, h⟩ := hπ i
    rw [hi] at h
    exact not_fixed hN (hΓ hγ) h
  set A := evM s w F ρ with hA
  let P : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i i' => if i' = π i then ε i else 0
  have hAP : A * Matrix.diagonal (fun j => μ ^ (-w j)) = P * A := by
    ext i j
    rw [Matrix.mul_diagonal, hε, Matrix.mul_apply]
    simp [P]
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  have hD : Matrix.diagonal (fun j => μ ^ (-w j)) = A⁻¹ * (P * A) := by
    rw [← hAP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have htr : ∑ j, μ ^ (-w j) = 0 := by
    rw [← Matrix.trace_diagonal, hD, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
      Matrix.mul_one]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [P, (hne i).symm]
  have hre := congrArg Complex.re htr
  rw [Complex.re_sum, Finset.sum_congr rfl fun j _ => re_μ_zpow (hF j).1, Finset.sum_ite] at hre
  simp only [Finset.sum_const, nsmul_eq_mul, Complex.zero_re] at hre
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin r)))
    (fun j => (3 : ℤ) ∣ w j)
  rw [Finset.card_univ, Fintype.card_fin] at hc
  have hc' := congrArg (Nat.cast : ℕ → ℝ) hc
  push_cast at hc'
  have : (3 : ℝ) * ((Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card : ℝ) = r := by linarith
  exact_mod_cast this

end GlobalTheory.OddFrame.ThirdDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperMulEqMulDiamondDiagGamma1InterGamma0
section
open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.Hk

theorem upper_mul_eq_mul_diamond_diag : ∀ (N l q j : ℕ) (σ γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ →
    j < q → γ ∈ GlobalTheory.Hk.lev N l → (q : ℤ) ∣ mat γ 0 0 + j * mat γ 1 0 →
    ∃ γ' ∈ GlobalTheory.Hk.lev N l, !![(1 : ℤ), (j : ℤ); 0, (q : ℤ)] * mat γ = mat γ' * (mat σ * dg q 1) := by
  intro N l q j σ γ _ _ hσ _ hγ hdiv
  obtain ⟨t, ht⟩ := hdiv
  obtain ⟨hσ10, hσ11⟩ := hσ
  have hγ1 := (Gamma1_mem N γ).1 (Subgroup.mem_inf.1 hγ).1
  have hcl := Gamma0_mem.1 (Subgroup.mem_inf.1 hγ).2
  obtain ⟨ha, hd, hc⟩ := hγ1
  have hdγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have hdσ : σ 0 0 * σ 1 1 - σ 0 1 * σ 1 0 = 1 := by
    have := σ.2; rw [Matrix.det_fin_two] at this; exact this
  have ht' : γ 0 0 + (j : ℤ) * γ 1 0 = q * t := ht
  have hM : Matrix.det !![t * σ 1 1 - (γ 0 1 + j * γ 1 1) * σ 1 0, (γ 0 1 + j * γ 1 1) * σ 0 0 - t * σ 0 1;
      γ 1 0 * σ 1 1 - q * γ 1 1 * σ 1 0, q * γ 1 1 * σ 0 0 - γ 1 0 * σ 0 1] = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination (q * t * γ 1 1 - (γ 0 1 + j * γ 1 1) * γ 1 0) * hdσ + hdγ - γ 1 1 * ht'
  have hdvd : ((N * l : ℕ) : ℤ) ∣ σ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hσ10
  have h10N : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans ⟨l, by push_cast; ring⟩ hdvd)
  have h10l : ((σ 1 0 : ℤ) : ZMod l) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans ⟨N, by push_cast; ring⟩ hdvd)
  have hdN := congrArg (fun x : ℤ => (x : ZMod N)) hdσ
  have htN := congrArg (fun x : ℤ => (x : ZMod N)) ht'
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_natCast, h10N, hσ11, ha, hc] at hdN htN
  refine ⟨⟨_, hM⟩, Subgroup.mem_inf.2 ⟨(Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩, Gamma0_mem.2 ?_⟩, ?_⟩
  · show ((t * σ 1 1 - (γ 0 1 + j * γ 1 1) * σ 1 0 : ℤ) : ZMod N) = 1
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_natCast, h10N, hσ11]
    linear_combination -htN
  · show ((q * γ 1 1 * σ 0 0 - γ 1 0 * σ 0 1 : ℤ) : ZMod N) = 1
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, hc, hd]
    linear_combination hdN
  · show ((γ 1 0 * σ 1 1 - q * γ 1 1 * σ 1 0 : ℤ) : ZMod N) = 0
    simp only [Int.cast_sub, Int.cast_mul, hc, h10N]
    ring
  · show ((γ 1 0 * σ 1 1 - q * γ 1 1 * σ 1 0 : ℤ) : ZMod l) = 0
    simp only [Int.cast_sub, Int.cast_mul, hcl, h10l]
    ring
  · ext i k
    fin_cases i <;> fin_cases k <;>
      simp [mat, dg, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination ht' - q * t * hdσ
    · linear_combination -(γ 0 1 + j * γ 1 1) * hdσ
    · linear_combination -(q * γ 1 0) * hdσ
    · linear_combination -(q * γ 1 1) * hdσ

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperTriangularMulEqMulUpperTriangularGamma1Inte
section
open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.Hk

theorem tinv_fin_fin : ∀ (N l q j : ℕ) (γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → j < q → γ ∈ GlobalTheory.Hk.lev N l →
    ¬ (q : ℤ) ∣ mat γ 0 0 + j * mat γ 1 0 → ∃ j' < q, ∃ γ' ∈ GlobalTheory.Hk.lev N l,
      !![(1 : ℤ), (j : ℤ); 0, (q : ℤ)] * mat γ = mat γ' * !![(1 : ℤ), (j' : ℤ); 0, (q : ℤ)] := by
  intro N l q j γ hq _ _ hγ hA
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.mp hγ
  rw [Gamma1_mem] at h1
  rw [Gamma0_mem] at h0
  obtain ⟨ha1, hd1, hc0⟩ := h1
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  set a := γ 0 0 with ha
  set b := γ 0 1 with hb
  set c := γ 1 0 with hc
  set d := γ 1 1 with hd
  have hmat : mat γ = !![a, b; c, d] := by
    ext i k; fin_cases i <;> fin_cases k <;> rfl
  rw [hmat] at hA ⊢
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const] at hA
  set A : ℤ := a + j * c with hAdef
  set B : ℤ := b + j * d with hBdef
  have hAq : ((A : ℤ) : ZMod q) ≠ 0 := by
    intro h
    exact hA ((ZMod.intCast_zmod_eq_zero_iff_dvd A q).mp h)
  set j' : ℕ := ((B : ZMod q) * (A : ZMod q)⁻¹).val with hj'
  have hj'lt : j' < q := ZMod.val_lt _
  have hdiv : (q : ℤ) ∣ B - j' * A := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hj', ZMod.natCast_zmod_val]
    field_simp
    ring
  obtain ⟨e, he⟩ := hdiv
  have hdet' : !![A, e; (q : ℤ) * c, d - c * j'].det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + c * he
  let g : SL(2, ℤ) := ⟨!![A, e; (q : ℤ) * c, d - c * j'], hdet'⟩
  refine ⟨j', hj'lt, g, Subgroup.mem_inf.mpr ⟨(Gamma1_mem N g).mpr ⟨?_, ?_, ?_⟩, Gamma0_mem.mpr ?_⟩, ?_⟩
  · show ((a + j * c : ℤ) : ZMod N) = 1
    push_cast; rw [ha1, hc0]; ring
  · show ((d - c * j' : ℤ) : ZMod N) = 1
    push_cast; rw [hd1, hc0]; ring
  · show (((q : ℤ) * c : ℤ) : ZMod N) = 0
    push_cast; rw [hc0]; ring
  · show (((q : ℤ) * c : ℤ) : ZMod l) = 0
    push_cast; rw [h0]; ring
  · show _ = !![A, e; (q : ℤ) * c, d - c * j'] * _
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    have e00 : 1 * a + (j : ℤ) * c = A * 1 + e * 0 := by rw [hAdef]; ring
    have e01 : 1 * b + (j : ℤ) * d = A * j' + e * q := by linear_combination he - hBdef
    have e10 : 0 * a + (q : ℤ) * c = (q : ℤ) * c * 1 + (d - c * j') * 0 := by ring
    have e11 : 0 * b + (q : ℤ) * d = (q : ℤ) * c * j' + (d - c * j') * q := by ring
    rw [e00, e01, e10, e11]

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationAddPowSubLe
section
namespace GlobalTheory.AlmostEt

open scoped NNReal

theorem valuation_natCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (n : ℕ) :
    v (n : L) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (v.map_add _ _).trans (max_le ih (by simp))

theorem valuation_add_pow_sub_le (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ)
    (hp : p.Prime) (y β : L) :
    v ((y + β) ^ p - y ^ p - β ^ p) ≤ v (p : L) * v β * (max (v y) (v β)) ^ (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  have key : (y + β) ^ (q + 1) - y ^ (q + 1) - β ^ (q + 1) =
      ∑ i ∈ Finset.range q, y ^ (i + 1) * β ^ (q + 1 - (i + 1)) * ((q + 1).choose (i + 1) : L) := by
    rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp
  rw [key]
  apply Valuation.map_sum_le
  intro i hi
  have hi : i < q := Finset.mem_range.mp hi
  set M := max (v y) (v β)
  obtain ⟨k, hk⟩ := hp.dvd_choose_self (Nat.succ_ne_zero i) (by omega)
  have hsub : q + 1 - (i + 1) = (q - (i + 1)) + 1 := by omega
  rw [hk, hsub]
  push_cast
  simp only [map_mul, map_pow]
  have h1 : v y ^ (i + 1) ≤ M ^ (i + 1) := pow_le_pow_left₀ (by positivity) (le_max_left _ _) _
  have h2 : v β ^ (q - (i + 1)) ≤ M ^ (q - (i + 1)) := pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
  have h3 : v (k : L) ≤ 1 := valuation_natCast_le_one v k
  have hM : M ^ (i + 1) * M ^ (q - (i + 1)) = M ^ q := by
    rw [← pow_add]; congr 1; omega
  rw [pow_succ (v β)]
  calc _ ≤ M ^ (i + 1) * (M ^ (q - (i + 1)) * v β) * (v ((q : L) + 1) * 1) := by gcongr
    _ = _ := by simp only [Nat.add_sub_cancel, ← hM]; ring

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationEqOneOfPowEqSpan
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem valuation_eq_one_of_pow_eq_span :
    ∀ (E Ω R : Type) [Field E] [Field Ω] [Algebra E Ω] [CommRing R] [Algebra R E] (B : ValuationSubring Ω)
      (J : Submodule R E) (N : ℕ), 0 < N → (∀ x : R, algebraMap E Ω (algebraMap R E x) ∈ B) → ∀ w : E, w ≠ 0 →
      (J ^ N = Submodule.span R {w}) → ∃ c : E, c ≠ 0 ∧ B.valuation (algebraMap E Ω (w / c ^ N)) = 1 := by
  intro E Ω R _ _ _ _ _ B J N hN hRB w hw hJ
  set v := B.valuation.comap (algebraMap E Ω) with hv
  have hva : ∀ x, v x = B.valuation (algebraMap E Ω x) := fun x => rfl
  have hR : ∀ r : R, v (algebraMap R E r) ≤ 1 := fun r => by
    rw [hva]; exact (B.valuation_le_one_iff _).mpr (hRB r)
  have hsm : ∀ (r : R) (z : E), v (r • z) ≤ v z := fun r z => by
    rw [Algebra.smul_def, v.map_mul]
    calc v (algebraMap R E r) * v z ≤ 1 * v z := mul_le_mul' (hR r) le_rfl
      _ = v z := one_mul _
  let S : ℕ → Submodule R E := fun n =>
    { carrier := {z | ∃ c ∈ J, v z ≤ v c ^ (n + 1)}
      zero_mem' := ⟨0, J.zero_mem, by simp⟩
      add_mem' := by
        rintro z₁ z₂ ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩
        rcases le_total (v c₁) (v c₂) with h | h
        · refine ⟨c₂, hc₂, (v.map_add z₁ z₂).trans (max_le ?_ h₂)⟩
          exact h₁.trans (pow_le_pow_left₀ zero_le' h _)
        · refine ⟨c₁, hc₁, (v.map_add z₁ z₂).trans (max_le h₁ ?_)⟩
          exact h₂.trans (pow_le_pow_left₀ zero_le' h _)
      smul_mem' := by
        rintro r z ⟨c, hc, h⟩
        exact ⟨c, hc, (hsm r z).trans h⟩ }
  have key : ∀ n : ℕ, J ^ (n + 1) ≤ S n := by
    intro n
    induction n with
    | zero =>
      intro z hz
      rw [pow_one] at hz
      exact ⟨z, hz, by simp⟩
    | succ n ih =>
      rw [pow_succ]
      refine Submodule.mul_le.mpr ?_
      intro y hy z' hz'
      obtain ⟨c, hc, h⟩ := ih hy
      show ∃ c ∈ J, v (y * z') ≤ v c ^ (n + 1 + 1)
      rw [v.map_mul]
      rcases le_total (v c) (v z') with h' | h'
      · refine ⟨z', hz', ?_⟩
        rw [pow_succ]
        exact mul_le_mul' (h.trans (pow_le_pow_left₀ zero_le' h' _)) le_rfl
      · refine ⟨c, hc, ?_⟩
        rw [pow_succ]
        exact mul_le_mul' h h'
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hwmem : w ∈ J ^ (n + 1) := by rw [hJ]; exact Submodule.mem_span_singleton_self w
  obtain ⟨c, hc, hle⟩ := key n hwmem
  have hcN : c ^ (n + 1) ∈ Submodule.span R {w} := hJ ▸ Submodule.pow_mem_pow J hc (n + 1)
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hcN
  have hge : v (c ^ (n + 1)) ≤ v w := by
    rw [← hr]; exact hsm r w
  have heq : v (c ^ (n + 1)) = v w := le_antisymm hge (by rw [v.map_pow]; exact hle)
  have hw0 : v w ≠ 0 := by
    rw [hva]; exact (Valuation.ne_zero_iff _).mpr ((_root_.map_ne_zero _).mpr hw)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hw0
    rw [← heq]; simp
  refine ⟨c, hc0, ?_⟩
  have : v (w / c ^ (n + 1)) = 1 := by
    rw [map_div₀, heq, div_self hw0]
  simpa [hva] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationFrobeniusSumSubLeNatCastPrime
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem frob_sum_sub_le (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ) (hp : p.Prime)
    (ι : Type) (s : Finset ι) (x : ι → L) (hx : ∀ i ∈ s, v (x i) ≤ 1) :
    v ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) ≤ v (p : L) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [zero_pow hp.ne_zero]
  | insert a s ha ih =>
    have hxa : v (x a) ≤ 1 := hx a (Finset.mem_insert_self a s)
    have hxs : ∀ i ∈ s, v (x i) ≤ 1 := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hS : v (∑ i ∈ s, x i) ≤ 1 := by
      have : (∑ i ∈ s, x i) ∈ v.integer :=
        Subring.sum_mem _ (fun i hi => (Valuation.mem_integer_iff v _).2 (hxs i hi))
      exact (Valuation.mem_integer_iff v _).1 this
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp
      (⟨x a, (Valuation.mem_integer_iff v _).2 hxa⟩ : v.integer)
      ⟨∑ i ∈ s, x i, (Valuation.mem_integer_iff v _).2 hS⟩
    have hr' : (x a + ∑ i ∈ s, x i) ^ p = x a ^ p + (∑ i ∈ s, x i) ^ p + (p : L) * (x a * (∑ i ∈ s, x i) * (r : L)) := by
      have := congrArg (fun z : v.integer => (z : L)) hr
      push_cast at this
      rw [this]; ring
    have hrle : v (x a * (∑ i ∈ s, x i) * (r : L)) ≤ 1 := by
      rw [Valuation.map_mul, Valuation.map_mul]
      have hr1 : v (r : L) ≤ 1 := (Valuation.mem_integer_iff v _).1 r.2
      calc v (x a) * v (∑ i ∈ s, x i) * v (r : L) ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by simp
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hr']
    have heq : x a ^ p + (∑ i ∈ s, x i) ^ p + (p : L) * (x a * (∑ i ∈ s, x i) * (r : L)) - (x a ^ p + ∑ i ∈ s, x i ^ p)
        = (p : L) * (x a * (∑ i ∈ s, x i) * (r : L)) + ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) := by ring
    rw [heq]
    refine (Valuation.map_add v _ _).trans (max_le ?_ (ih hxs))
    rw [Valuation.map_mul]
    calc v (p : L) * v (x a * (∑ i ∈ s, x i) * (r : L)) ≤ v (p : L) * 1 := by gcongr
      _ = v (p : L) := mul_one _

theorem frob_sum_sub_le' : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ (ι : Type) (s : Finset ι) (x : ι → L), (∀ i ∈ s, v (x i) ≤ 1) →
      v ((∑ i ∈ s, x i) ^ p - ∑ i ∈ s, x i ^ p) ≤ v (p : L) :=
  fun L _ v p hp ι s x hx => frob_sum_sub_le L v p hp ι s x hx

end GlobalTheory.AlmostEt
end

