module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0105
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0005
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HilbertSchmidtLowerBoundInverseDifferentStatement
section
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSchmidt_lower_bound_inverseDifferent :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (a b : ℕ)
      (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
      (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ)
      (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (lo hi : ℝ),
      (∀ w, IsUnit (X w).det) → (∀ w, IsUnit (X' w).det) → A.FG → B.FG → 0 < lo →
      (∀ N, N ≤ A → N ≠ ⊥ → lo ≤ Formalism.HN.size (Pi.basisFun K (Fin a)) X N) →
      Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B ≤ hi →
      ∀ ψ : Matrix (Fin a) (Fin b) K, (∃ y ∈ B, ψ *ᵥ y ≠ 0) →
        (∀ δ ∈ differentIdeal ℤ (𝓞 K), ∀ y ∈ B, δ • (ψ *ᵥ y) ∈ A) →
        (Formalism.HN.nPl K : ℝ) *
            (lo / (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) * hi)) ^ 2 ≤
          ∑ w, ∑ i, ∑ j, ‖((X w)⁻¹ * ψ.map w.embedding * X' w) i j‖ ^ 2 := by
  intro K _ _ _ _ a b X X' A B lo hi hX hX' _ hB hlo hA hhi ψ ⟨y, hyB, hy⟩ hψ
  let φ : (Fin b → K) →ₗ[K] (Fin a → K) := Matrix.toLin' ψ
  let A' : Submodule (𝓞 K) (Fin a → K) := B.map (φ.restrictScalars (𝓞 K))
  let rd : ℝ := |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ)))
  have hrdpos : 0 < rd :=
    Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)) _
  have hA'fg : A'.FG := hB.map _
  have hA'0 : A' ≠ ⊥ := by
    intro h
    have hmem : ψ *ᵥ y ∈ A' := ⟨y, hyB, by simp [φ]⟩
    rw [h] at hmem
    exact hy hmem
  have hB0 : B ≠ ⊥ := by
    intro h
    apply hA'0
    simp [A', h]
  have hd : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  have hleast : lo / rd ≤ leastSize (Pi.basisFun K (Fin a)) X A' := by
    refine le_csInf ⟨_, A', le_rfl, hA'0, rfl⟩ ?_
    rintro t ⟨N, hN, hN0, rfl⟩
    have hNfg : N.FG := Submodule.FG.of_le hA'fg hN
    have hle : differentIdeal ℤ (𝓞 K) • N ≤ A := by
      refine Submodule.smul_le.2 fun δ hδ v hv => ?_
      obtain ⟨z, hz, rfl⟩ := hN hv
      simpa [φ] using hψ δ hδ z hz
    have hspan := Formalism.HN.DualPolygon.twist_span_smul N _ hd
    have hne : differentIdeal ℤ (𝓞 K) • N ≠ ⊥ := by
      intro h
      rw [h] at hspan
      apply hN0
      rw [eq_bot_iff]
      intro v hv
      have hmem : v ∈ Submodule.span K (N : Set (Fin a → K)) := Submodule.subset_span hv
      rw [← hspan] at hmem
      simpa using hmem
    have hsize :
        Formalism.HN.size (Pi.basisFun K (Fin a)) X (differentIdeal ℤ (𝓞 K) • N) =
          Formalism.HN.size (Pi.basisFun K (Fin a)) X N * rd := by
      have hrk : rkK (differentIdeal ℤ (𝓞 K) • N) = rkK N := by
        unfold rkK
        rw [hspan]
      have hnorm : (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) =
          |(NumberField.discr K : ℝ)| := by
        rw [NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs, Int.cast_abs]
      have hj : (rkK N : ℝ) ≠ 0 := by
        exact_mod_cast (Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hN0).ne'
      have hf : (Formalism.HN.nPl K : ℝ) ≠ 0 := by
        have hcard : 0 < Formalism.HN.nPl K := Fintype.card_pos
        exact_mod_cast hcard.ne'
      unfold Formalism.HN.size rd
      rw [Formalism.LFunctionChainParameters.slopeLatticeData.ht_ideal _ X hX hNfg hd, hrk, hnorm,
        Real.mul_rpow (Formalism.LFunctionChainParameters.slopeLatticeData.ht_pos _ X hX hNfg).le
          (by positivity),
        ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      congr 2
      field_simp
    rw [div_le_iff₀ hrdpos, ← hsize]
    exact hA _ hle hne
  have hLpos : 0 < Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B := by
    rw [(sizeMu K _ _ (Pi.basisFun K (Fin b)) X' hX' B hB hB0).2.2.2.2.1]
    exact Real.exp_pos _
  have hM := sizeIneq K _ _ _ _ (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X hX' hX φ B A'
    hB hA'fg le_rfl hA'0
  have h4 : lo / (rd * hi) ≤
      (∏ v, opNormAt (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X v φ) ^
        ((1 : ℝ) / (Formalism.HN.nPl K : ℝ)) := by
    refine le_trans ?_ hM
    rw [← div_div]
    exact div_le_div₀ ((div_pos hlo hrdpos).le.trans hleast) hleast hLpos hhi
  have h5 := GlobalTheory.DualBound.card_mul_geom_sq_le
    (fun v => opNormAt (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X v φ)
    (fun v => norm_nonneg _)
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (div_nonneg hlo.le (mul_nonneg hrdpos.le (hLpos.le.trans hhi))) h4 2)
      (Nat.cast_nonneg _)
    _ ≤ _ := h5
    _ ≤ _ := by
      refine Finset.sum_le_sum fun w _ => ?_
      have hmatrix : LinearMap.toMatrix (Pi.basisFun K (Fin b)) (Pi.basisFun K (Fin a)) φ = ψ := by
        ext i j
        simp [φ]
      unfold opNormAt
      rw [hmatrix]
      exact GlobalTheory.DualBound.opNorm_sq_le_hs _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsLeWeightedSumBlockVariancesOfGap
section
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.GapSum

theorem inP_apply_eq_zero {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : inP ε Y) {a b : Fin n} (hab : ε a = ε b) : Y a b = 0 := by
  have h := congrFun (congrFun hY.2 a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.neg_apply, Matrix.diagonal_mul, hab] at h
  by_cases hb : ε b = true
  · simp only [hb, if_true] at h
    linear_combination h / 2
  · simp only [hb] at h
    simp only [Bool.false_eq_true, if_false] at h
    linear_combination -h / 2

theorem inP_norm_symm {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : inP ε Y) (a b : Fin n) : ‖Y a b‖ = ‖Y b a‖ := by
  have h := congrFun (congrFun hY.1 a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.add_apply, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply, Matrix.zero_apply] at h
  have h2 := congrArg norm (eq_neg_of_add_eq_zero_left h)
  rw [norm_neg, norm_mul, norm_mul, norm_star] at h2
  have e : ∀ c : Fin n, ‖(if ε c = true then (1 : ℂ) else -1)‖ = 1 := by
    intro c; split_ifs <;> simp
  rw [e, e] at h2
  linarith

theorem telescope (L : ℕ → ℝ) (m a b : ℕ) (ha : a ≤ m) :
    ∑ i ∈ range m, (if i + 1 ≤ a ∧ b < i + 1 then L i - L (i + 1) + 1 else 0) =
      if b < a then L b - L a + ((a : ℝ) - b) else 0 := by
  rw [← Finset.sum_filter]
  have hf : (range m).filter (fun i => i + 1 ≤ a ∧ b < i + 1) = Finset.Ico b a := by
    ext i; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [hf]
  split_ifs with hba
  · have hle : b ≤ a := hba.le
    clear hf ha hba
    induction a, hle using Nat.le_induction with
    | base => simp
    | succ k hk ih => rw [Finset.sum_Ico_succ_top hk, ih]; push_cast; ring
  · rw [Finset.Ico_eq_empty hba, Finset.sum_empty]

theorem sum_symm_half {n : ℕ} (N : Fin n → Fin n → ℝ) (hs : ∀ a b, N a b = N b a)
    (h0 : ∀ a, N a a = 0) :
    ∑ a, ∑ b, N a b = 2 * ∑ a, ∑ b, if b < a then N a b else 0 := by
  have h1 : ∑ a, ∑ b, (if b < a then N a b else 0) = ∑ a, ∑ b, if a < b then N a b else 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hs]
  rw [two_mul]
  nth_rewrite 2 [h1]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.not_gt]
  · subst h; simp [h0]
  · simp [h, h.not_gt]

theorem gap_mul_hs_le : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (Y : Matrix (Fin n) (Fin n) ℂ), StrictAnti lam → GapAtLeast ε lam h → inP ε Y → h * hs Y / 2 ≤ ∑ i : Fin (n - 1), (lam ⟨i.val, by omega⟩ - lam ⟨i.val + 1, by omega⟩ + 1) * ∑ a : Fin n, ∑ b : Fin n, if i.val + 1 ≤ a.val ∧ b.val < i.val + 1 then ‖Y a b‖ ^ 2 else 0 := by
  intro n ε lam h Y hanti hgap hY
  let L : ℕ → ℝ := fun k => if hk : k < n then lam ⟨k, hk⟩ else 0
  have hL : ∀ a : Fin n, L a.val = lam a := fun a => by simp [L]
  have hR : (∑ i : Fin (n - 1), (lam ⟨i.val, by omega⟩ - lam ⟨i.val + 1, by omega⟩ + 1) *
      ∑ a : Fin n, ∑ b : Fin n, if i.val + 1 ≤ a.val ∧ b.val < i.val + 1 then ‖Y a b‖ ^ 2 else 0) =
      ∑ a : Fin n, ∑ b : Fin n,
        (if b.val < a.val then lam b - lam a + ((a.val : ℝ) - b.val) else 0) * ‖Y a b‖ ^ 2 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hL a, ← hL b, ← telescope L (n - 1) a b (by omega), Finset.sum_mul,
      ← Fin.sum_univ_eq_sum_range (fun i => (if i + 1 ≤ a.val ∧ b.val < i + 1 then
        L i - L (i + 1) + 1 else 0) * ‖Y a b‖ ^ 2) (n - 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hL ⟨i.val, by omega⟩, ← hL ⟨i.val + 1, by omega⟩]
    split_ifs <;> simp
  rw [hR, hs, sum_symm_half (fun a b => ‖Y a b‖ ^ 2)
    (fun a b => by simp only [inP_norm_symm hY a b])
    (fun a => by simp [inP_apply_eq_zero hY (rfl : ε a = ε a)])]
  rw [show ∀ S : ℝ, h * (2 * S) / 2 = h * S from fun S => by ring, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases hba : b < a
  · have hba' : b.val < a.val := hba
    rw [if_pos hba, if_pos hba']
    by_cases he : ε a = ε b
    · simp [inP_apply_eq_zero hY he]
    · have h1 := hgap a b he
      have h2 := hanti hba
      have h3 : (b.val : ℝ) < a.val := by exact_mod_cast hba'
      rw [abs_of_neg (by linarith)] at h1
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hba' : ¬ b.val < a.val := hba
    simp [hba, hba']

end GlobalTheory.GapSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadMinorExpHermitianEqConvexExpSum
section
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.LeadMinorExp

theorem sum_dite_card {n l : ℕ} {M : Type*} [AddCommMonoid M] (f : Set.powersetCard (Fin n) l → M) :
    ∑ J : Finset (Fin n), (if h : J.card = l then f ⟨J, h⟩ else 0) = ∑ S, f S := by
  symm
  refine Finset.sum_of_injOn (fun S : Set.powersetCard (Fin n) l => S.1)
    (fun _ _ _ _ h => Subtype.ext h) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro J _ hJ
    rw [dif_neg]
    intro h
    exact hJ ⟨⟨J, h⟩, by simp, rfl⟩
  · intro S _
    have h : S.1.card = l := S.2
    rw [dite_eq_left h]

theorem exp_smul_eq {n : ℕ} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y.IsHermitian) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Y) =
      (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        diagonal (fun j => ((Real.exp (t * hY.eigenvalues j) : ℝ) : ℂ)) *
        (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have h1 : U * Uᴴ = 1 := (hY.eigenvectorUnitary).2.2
  have h2 : Uᴴ * U = 1 := (hY.eigenvectorUnitary).2.1
  have hs : Y = U * diagonal (fun j => ((hY.eigenvalues j : ℝ) : ℂ)) * Uᴴ := by
    have := hY.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have h3 : (t : ℂ) • Y = U * diagonal (fun j => ((t * hY.eigenvalues j : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hs]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
    congr 3
    funext j
    simp
  rw [h3]
  refine (Matrix.exp_units_conj (⟨U, Uᴴ, h1, h2⟩ : (Matrix (Fin n) (Fin n) ℂ)ˣ) _).trans ?_
  rw [Matrix.exp_diagonal]
  change U * _ * Uᴴ = _
  congr 3
  funext j
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

theorem leadMinor_exp_eq_sum (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) (l : ℕ)
    (hl : l ≤ n) :
    ∃ w : Finset (Fin n) → ℝ, (∀ J, 0 ≤ w J) ∧ (∀ J, w J ≠ 0 → J.card = l) ∧ ∑ J, w J = 1 ∧
      ∀ t : ℝ, leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl =
        ((∑ J, w J * Real.exp (t * ∑ j ∈ J, hY.eigenvalues j) : ℝ) : ℂ) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hY.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have h1 : U * Uᴴ = 1 := (hY.eigenvectorUnitary).2.2
  set A : Matrix (Fin l) (Fin n) ℂ := U.submatrix (Fin.castLE hl) id with hA
  have hAA : A * Aᴴ = 1 := by
    rw [hA, conjTranspose_submatrix, ← submatrix_mul U Uᴴ _ id _ Function.bijective_id, h1]
    exact submatrix_one _ (Fin.castLE_injective hl)
  refine ⟨fun J => if h : J.card = l then
    ‖(A.submatrix id (GlobalTheory.subsetEnum (⟨J, h⟩ : Set.powersetCard (Fin n) l))).det‖ ^ 2 else 0,
    ?_, ?_, ?_, ?_⟩
  · intro J
    dsimp only
    split_ifs <;> positivity
  · intro J hJ
    by_contra h
    exact hJ (dif_neg h)
  · rw [sum_dite_card (fun S => ‖(A.submatrix id (GlobalTheory.subsetEnum S)).det‖ ^ 2)]
    exact GlobalTheory.sum_norm_sq_minors_eq_one A hAA
  · intro t
    have hsum : (∑ J : Finset (Fin n), (if h : J.card = l then
        ‖(A.submatrix id (GlobalTheory.subsetEnum (⟨J, h⟩ : Set.powersetCard (Fin n) l))).det‖ ^ 2 else 0) *
          Real.exp (t * ∑ j ∈ J, hY.eigenvalues j)) =
        ∑ S : Set.powersetCard (Fin n) l, ‖(A.submatrix id (GlobalTheory.subsetEnum S)).det‖ ^ 2 *
          Real.exp (t * ∑ j ∈ S.1, hY.eigenvalues j) := by
      rw [← sum_dite_card]
      refine Finset.sum_congr rfl fun J _ => ?_
      split_ifs <;> simp
    rw [hsum, exp_smul_eq hY t, leadMinor]
    rw [submatrix_mul _ _ _ id _ Function.bijective_id,
      submatrix_mul _ _ _ id _ Function.bijective_id, submatrix_id_id,
      ← conjTranspose_submatrix]
    refine (GlobalTheory.det_mul_diagonal_mul_eq_sum_minors A _ Aᴴ).trans ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← conjTranspose_submatrix, det_conjTranspose, Complex.star_def, Complex.mul_conj',
      Finset.mul_sum, Real.exp_sum]
    push_cast
    ring

end GlobalTheory.LeadMinorExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUJsetOfKset
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory
namespace LowKProj

section General
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem fix_of_mem {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) :
    ∀ x ∈ S, E x = x := by
  intro x hx
  obtain ⟨hidem, -, hrange⟩ := hE
  rw [← hrange] at hx
  obtain ⟨y, rfl⟩ := hx
  change E (E y) = E y
  rw [← ContinuousLinearMap.comp_apply, hidem]

theorem apply_mem {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) (x : H) :
    E x ∈ S := by
  rw [← hE.2.2]
  exact ⟨x, rfl⟩

theorem norm_le_one {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) :
    ‖E‖ ≤ 1 := by
  obtain ⟨hidem, hsym, -⟩ := hE
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  have hEE : E (E x) = E x := by rw [← ContinuousLinearMap.comp_apply, hidem]
  have hsq : ‖E x‖ ^ 2 ≤ ‖x‖ * ‖E x‖ := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hsym, hEE]
    exact re_inner_le_norm x (E x)
  have h0 : 0 ≤ ‖x‖ := norm_nonneg x
  have h1 : 0 ≤ ‖E x‖ := norm_nonneg (E x)
  nlinarith

theorem exists_proj (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    ∃ E : H →L[ℂ] H, IsOrthProjOnto E S := by
  have : CompleteSpace S := FiniteDimensional.complete ℂ S
  refine ⟨S.starProjection, ?_, ?_, ?_⟩
  · exact S.isIdempotentElem_starProjection
  · exact S.inner_starProjection_left_eq_right
  · exact S.range_starProjection

theorem comm_of_stable {E A B : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S)
    (hAB : ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, B y⟫_ℂ) (hA : ∀ v ∈ S, A v ∈ S) (hB : ∀ v ∈ S, B v ∈ S) :
    E ∘L A = A ∘L E := by
  have hfix := fix_of_mem hE
  have hmem := apply_mem hE
  have hsym := hE.2.1
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  refine ext_inner_right ℂ fun y => ?_

  calc ⟪E (A x), y⟫_ℂ = ⟪A x, E y⟫_ℂ := hsym _ _
    _ = ⟪x, B (E y)⟫_ℂ := hAB _ _
    _ = ⟪x, E (B (E y))⟫_ℂ := by rw [hfix _ (hB _ (hmem y))]
    _ = ⟪E x, B (E y)⟫_ℂ := (hsym _ _).symm
    _ = ⟪A (E x), E y⟫_ℂ := (hAB _ _).symm
    _ = ⟪E (A (E x)), y⟫_ℂ := (hsym _ _).symm
    _ = ⟪A (E x), y⟫_ℂ := by rw [hfix _ (hA _ (hmem x))]

end General

theorem mem_UJset_of_Kset {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : k ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  have h2 : star k * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
  show kᴴ * Jm ε * k = Jm ε
  rw [← Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

private lemma star_mem_Kset {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : star k ∈ Kset ε := by
  obtain ⟨hu, hc⟩ := hk
  have h1 : k * star k = 1 := (Matrix.mem_unitaryGroup_iff).1 hu
  have h2 : star k * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
  refine ⟨(Matrix.mem_unitaryGroup_iff).2 (by rw [star_star]; exact h2), ?_⟩
  calc star k * Jm ε = star k * Jm ε * (k * star k) := by rw [h1, Matrix.mul_one]
    _ = star k * (Jm ε * k) * star k := by simp only [Matrix.mul_assoc]
    _ = star k * (k * Jm ε) * star k := by rw [hc]
    _ = (star k * k) * Jm ε * star k := by simp only [Matrix.mul_assoc]
    _ = Jm ε * star k := by rw [h2, Matrix.one_mul]

theorem inner_adj {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x y : H) :
    ⟪σ k x, y⟫_ℂ = ⟪x, σ (star k) y⟫_ℂ := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hσ
  have hkU := mem_UJset_of_Kset hk
  have hsU := mem_UJset_of_Kset (star_mem_Kset hk)
  have hks : k * star k = 1 := (Matrix.mem_unitaryGroup_iff).1 hk.1

  let L : H →ₗᵢ[ℂ] H := ⟨(σ k : H →ₗ[ℂ] H), fun v => hiso k hkU v⟩
  have hy : σ k (σ (star k) y) = y := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul k hkU (star k) hsU, hks, h1]
    rfl
  calc ⟪σ k x, y⟫_ℂ = ⟪L x, L (σ (star k) y)⟫_ℂ := by
        change ⟪σ k x, y⟫_ℂ = ⟪σ k x, σ k (σ (star k) y)⟫_ℂ
        rw [hy]
    _ = ⟪x, σ (star k) y⟫_ℂ := L.inner_map_map _ _

theorem lowKSub_stable {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (lowKSub ε lam σ) := by
  intro g hg v hv

  have hle : lowKSub ε lam σ ≤ (lowKSub ε lam σ).comap (σ g : H →ₗ[ℂ] H) :=
    sSup_le fun S hS w hw => le_sSup hS (hS.2.1 g hg w hw)
  exact hle hv

theorem lowK_projection : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → (∃ w, IsHighestUnit ε lam σ w) ∧ IsKStableOn ε σ (lowKSub ε lam σ) ∧ (FiniteDimensional ℂ (lowKSub ε lam σ) → ∃ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ)) ∧ ∀ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ) → ‖E‖ ≤ 1 ∧ (∀ x ∈ lowKSub ε lam σ, E x = x) ∧ ∀ k ∈ Kset ε, E ∘L σ k = σ k ∘L E ∧ ‖σ k‖ ≤ 1 := by
  intro n ε lam H _ _ _ σ hDS
  obtain ⟨-, -, hrep, -, -, ⟨S, hS⟩, -⟩ := hDS
  refine ⟨?_, lowKSub_stable ε lam σ, fun _ => exists_proj _, ?_⟩
  ·
    obtain ⟨v, hvS, hv0, hwt⟩ := hS.2.2.2.1
    have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hv0
    refine ⟨((‖v‖ : ℂ)⁻¹) • v, ?_, ?_, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)
    · have hle : S ≤ lowKSub ε lam σ :=
        le_sSup (show S ∈ {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} from hS)
      exact Submodule.smul_mem _ _ (hle hvS)
    · intro θ hθ
      rw [map_smul, hwt θ hθ, smul_comm]
  · intro E hE
    refine ⟨norm_le_one hE, fix_of_mem hE, fun k hk => ⟨?_, ?_⟩⟩
    · exact comm_of_stable hE (inner_adj hrep hk) (fun v hv => lowKSub_stable ε lam σ k hk v hv)
        (fun v hv => lowKSub_stable ε lam σ (star k) (star_mem_Kset hk) v hv)
    · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        rw [hrep.2.1 k (mem_UJset_of_Kset hk) x, one_mul]

end LowKProj
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RhoNNormLeAndCasimirArith
section
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory

theorem rpow_three_halves_sq_eq_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ ((3 : ℝ) / 2)) ^ 2 = x ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem rhoN_norm_le_and_casimir_arith :
    (∀ (n : ℕ) (ε : Fin n → Bool), Real.sqrt (nsq (rhoN ε)) ≤ 0.58 * (n : ℝ) ^ ((3 : ℝ) / 2)) ∧
    ∀ (L a n : ℝ), 0 ≤ L → 0 ≤ a → 0 ≤ n →
      2 * (L + a) ^ 2 - L ^ 2 + n ^ 3 / 12 ≤ (L + 2 * a + 0.3 * n ^ ((3 : ℝ) / 2)) ^ 2 := by
  refine ⟨fun n ε => ?_, fun L a n hL ha hn => ?_⟩
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hs := rpow_three_halves_sq_eq_cube hn
    have hp : 0 ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hn _
    have h1 : nsq (rhoN ε) ≤ (n : ℝ) * ((n : ℝ) / 2) ^ 2 := by
      have : ∑ a : Fin n, (rhoN ε a) ^ 2 ≤ ∑ _a : Fin n, ((n : ℝ) / 2) ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        obtain ⟨h1, h2⟩ := rho_rhoN_bound ε a
        exact sq_le_sq' h1 h2
      simpa [nsq, dot, sq] using this
    refine Real.sqrt_le_iff.mpr ⟨by positivity, h1.trans ?_⟩
    rw [mul_pow, hs]
    have : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
    nlinarith
  · have hs := rpow_three_halves_sq_eq_cube hn
    have hp : 0 ≤ n ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hn _
    generalize n ^ ((3 : ℝ) / 2) = s at hs hp
    rw [← hs]
    nlinarith [mul_nonneg hL hp, mul_nonneg ha hp, sq_nonneg a, sq_nonneg s]

end GlobalTheory
end

