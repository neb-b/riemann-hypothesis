module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsBase

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoefEx
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

private lemma oexp_pow (π : Equiv.Perm (Fin (2 + 2))) (ψ : U4 → ℂ) (μ : Fin (2 + 2) → ℤ) (h : OExp π ψ μ) (n : ℕ) :
    OExp π (fun k => ψ k ^ n) (n • μ) := by
  induction n with
  | zero =>
    have h0 := (expBasic π).2.2.2 0
    simp only [zpow_zero] at h0
    simp only [pow_zero, zero_smul]
    exact h0
  | succ n ih =>
    have h1 := expMul π _ _ _ _ ih h
    simp only [pow_succ, succ_nsmul]
    exact h1

private noncomputable def F (i j l : Fin (2 + 2)) (α β γ : ℕ) (δ : ℤ) (k : U4) : ℂ :=
  en i i k ^ α * (en i i k * en j j k - en i j k * en j i k) ^ β * conj (en l l k) ^ γ *
    (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det ^ δ

private lemma F_exp (π : Equiv.Perm (Fin (2 + 2))) (i j l : Fin (2 + 2)) (hi : π 0 = i) (hj : π 1 = j) (hl : π 3 = l)
    (α β γ : ℕ) (δ : ℤ) (μ : Fin (2 + 2) → ℤ)
    (hμ : μ = α • (Pi.single i 1 : Fin (2 + 2) → ℤ) + β • (Pi.single i 1 + Pi.single j 1) + γ • (-Pi.single l 1) + fun _ => δ) :
    WExp (F i j l α β γ δ) μ := by
  subst hi hj hl hμ
  obtain ⟨h1, h2, h3, h4⟩ := expBasic π
  exact expNorm π _ _ (expMul π _ _ _ _ (expMul π _ _ _ _ (expMul π _ _ _ _ (oexp_pow π _ _ h1 α) (oexp_pow π _ _ h2 β))
    (oexp_pow π _ _ h3 γ)) (h4 δ))

private lemma en_inv (i j : Fin (2 + 2)) (k : U4) : en i j k⁻¹ = conj (en j i k) := rfl

private lemma F_star (i j l : Fin (2 + 2)) (α β γ : ℕ) (δ : ℤ) (k : U4) :
    F i j l α β γ δ k⁻¹ = conj (F i j l α β γ δ k) := by
  have hd : ((k⁻¹ : U4) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det = conj ((k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det) := by
    change (star (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ)).det = _
    rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]; rfl
  simp only [F, en_inv, hd, map_mul, map_pow, map_zpow₀, map_sub]
  ring

private lemma en_bd (i j : Fin (2 + 2)) (a b : U2) : en i j (bd a b) =
    fromBlocks (a : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (b : Matrix (Fin 2) (Fin 2) ℂ) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := by
  unfold en
  rw [u4.1 a b]
  rfl

private lemma det_bd (a b : U2) : (bd a b : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ).det =
    (a : Matrix (Fin 2) (Fin 2) ℂ).det * (b : Matrix (Fin 2) (Fin 2) ℂ).det := by
  rw [u4.1 a b, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

private lemma s0 : (finSumFinEquiv.symm (0 : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = Sum.inl 0 := by decide
private lemma s1 : (finSumFinEquiv.symm (1 : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = Sum.inl 1 := by decide
private lemma s2 : (finSumFinEquiv.symm (2 : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = Sum.inr 0 := by decide
private lemma s3 : (finSumFinEquiv.symm (3 : Fin (2 + 2)) : Fin 2 ⊕ Fin 2) = Sum.inr 1 := by decide

private lemma unitary_two_conj_entry_eq (m : U2) : conj ((m : Matrix (Fin 2) (Fin 2) ℂ) 1 1) =
    (m : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * ((m : Matrix (Fin 2) (Fin 2) ℂ).det)⁻¹ := by
  have hd := det_ne_zero_of_U2 m
  have h : star (m : Matrix (Fin 2) (Fin 2) ℂ) * (m : Matrix (Fin 2) (Fin 2) ℂ) = 1 := m.2.1
  have h0 := congrFun (congrFun h 1) 0
  have h1 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at h0 h1
  rw [eq_mul_inv_iff_mul_eq₀ hd, Matrix.det_fin_two]
  linear_combination ((m : Matrix (Fin 2) (Fin 2) ℂ) 0 0) * h1 - ((m : Matrix (Fin 2) (Fin 2) ℂ) 0 1) * h0

private lemma c1 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = α) (hq : q = β + δ)
    (hn' : n' = γ) (hq' : q' = δ - γ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 0 ∧ π 1 = 1 ∧ π 3 = 3 := by decide
  refine ⟨F 0 1 3 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

private lemma c2 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = α + β) (hq : q = δ)
    (hn' : n' = β + γ) (hq' : q' = δ - γ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 0 ∧ π 1 = 2 ∧ π 3 = 3 := by decide
  refine ⟨F 0 2 3 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

private lemma c3 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = α + β + γ) (hq : q = δ - γ)
    (hn' : n' = β) (hq' : q' = δ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 0 ∧ π 1 = 2 ∧ π 3 = 1 := by decide
  refine ⟨F 0 2 1 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

private lemma c4 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = β) (hq : q = δ)
    (hn' : n' = α + β + γ) (hq' : q' = δ - γ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 2 ∧ π 1 = 0 ∧ π 3 = 3 := by decide
  refine ⟨F 2 0 3 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

private lemma c5 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = β + γ) (hq : q = δ - γ)
    (hn' : n' = α + β) (hq' : q' = δ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 2 ∧ π 1 = 0 ∧ π 3 = 1 := by decide
  refine ⟨F 2 0 1 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

private lemma c6 (α β γ : ℕ) (δ : ℤ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (hn : n = γ) (hq : q = δ - γ)
    (hn' : n' = α) (hq' : q' = β + δ) : ∃ ψ, Coef ψ n q n' q' := by
  obtain ⟨π, hi, hj, hl⟩ : ∃ π : Equiv.Perm (Fin (2 + 2)), π 0 = 2 ∧ π 1 = 3 ∧ π 3 = 1 := by decide
  refine ⟨F 2 3 1 α β γ δ, F_exp π _ _ _ hi hj hl α β γ δ _ ?_, F_star _ _ _ _ _ _ _, fun a b => ?_⟩
  · funext x
    fin_cases x <;> simp [wt, Pi.single_apply] <;> omega
  · have ha := det_ne_zero_of_U2 a
    have hb := det_ne_zero_of_U2 b
    rw [hn, hq, hn', hq']
    simp only [F, en_bd, det_bd, s0, s1, s2, s3, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, unitary_two_conj_entry_eq, ← Matrix.det_fin_two, KT.psi, Nat.sub_self, pow_zero, mul_one, mul_zero, sub_zero,
      zpow_add₀ ha, zpow_add₀ hb, zpow_sub₀ ha, zpow_sub₀ hb, zpow_natCast, mul_zpow, mul_pow, inv_pow, pow_add]
    field_simp

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coefEx :
    ∀ n q n' q', ∃ ψ, Coef ψ n q n' q' := by
  intro n q n' q'
  by_cases h1 : (n' : ℤ) + q' ≤ q
  · exact c1 n (q - n' - q').toNat n' (n' + q') n q n' q' rfl (by omega) rfl (by omega)
  by_cases h2 : (n : ℤ) + q ≤ q'
  · exact c6 n' (q' - n - q).toNat n (n + q) n q n' q' rfl (by omega) rfl (by omega)
  by_cases h3 : (n' : ℤ) + q' ≤ n + q
  · by_cases h4 : q' ≤ q
    · exact c2 (n + q - n' - q').toNat (n' + q' - q).toNat (q - q').toNat q n q n' q' (by omega) (by omega) (by omega) (by omega)
    · exact c3 (n + q - n' - q').toNat n' (q' - q).toNat q' n q n' q' (by omega) (by omega) (by omega) (by omega)
  · by_cases h4 : q' ≤ q
    · exact c4 (n' + q' - n - q).toNat n (q - q').toNat q n q n' q' (by omega) (by omega) (by omega) (by omega)
    · exact c5 (n' + q' - n - q).toNat (n + q - q').toNat (q' - q).toNat q' n q n' q' (by omega) (by omega) (by omega) (by omega)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoefFix
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private theorem fixOf (μ : Measure U4) (hμ : Haar4 μ) (ψ : U4 → ℂ) (hψ : Continuous ψ) (ι : U2 → U4) (hι : Continuous ι)
    (n : ℕ) (q : ℤ)
    (hin : ∀ k, ∫ m, KT.psi n q n m * ψ ((ι m)⁻¹ * k) ∂μK = ((KT.normSqInt n q : ℝ) : ℂ) * ψ k)
    (Φ : U4 → ℂ) (hΦ : Continuous Φ) (hfix : RFix μ (eOf μ ψ) Φ) (g : U4) :
    ∫ m, T n q m * Φ (g * ι m) ∂μK = Φ g := by
  haveI := hμ.prob
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcpt, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.u4
  have hN : ((KT.normSqInt n q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (KT.normSqInt_pos n q).ne'
  have hec : Continuous (eOf μ ψ) := by
    unfold eOf
    exact continuous_const.mul (Complex.continuous_conj.comp hψ)
  have hTc : Continuous (T n q) := by
    unfold T
    exact continuous_const.mul (KT.continuous_conj_psi n q n)
  have hA : ∀ m, Φ (g * ι m) = ∫ k, eOf μ ψ ((ι m)⁻¹ * k) * Φ (g * k) ∂μ := by
    intro m
    rw [← hfix (g * ι m)]
    have h := (hμ.left (ι m)).integral_comp (Homeomorph.mulLeft (ι m)).measurableEmbedding
      (fun k => eOf μ ψ ((ι m)⁻¹ * k) * Φ (g * k))
    rw [← h]
    congr 1; funext k
    simp only [inv_mul_cancel_left, mul_assoc]
  have hint : Integrable (Function.uncurry fun m k => T n q m * (eOf μ ψ ((ι m)⁻¹ * k) * Φ (g * k))) (μK.prod μ) := by
    have hcont : Continuous (Function.uncurry fun m k => T n q m * (eOf μ ψ ((ι m)⁻¹ * k) * Φ (g * k))) := by
      unfold Function.uncurry
      refine (hTc.comp continuous_fst).mul ((hec.comp ?_).mul (hΦ.comp (continuous_const.mul continuous_snd)))
      exact ((hι.comp continuous_fst).inv).mul continuous_snd
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hB : ∀ k, ∫ m, T n q m * eOf μ ψ ((ι m)⁻¹ * k) ∂μK = eOf μ ψ k := by
    intro k
    have h := congrArg conj (hin k)
    rw [← integral_conj] at h
    have e : ∀ m, T n q m * eOf μ ψ ((ι m)⁻¹ * k) = (((KT.normSqInt n q : ℝ) : ℂ)⁻¹ * ((∫ h, ‖ψ h‖ ^ 2 ∂μ : ℝ) : ℂ)⁻¹) *
        conj (KT.psi n q n m * ψ ((ι m)⁻¹ * k)) := by
      intro m
      simp only [T, eOf, map_mul]
      ring
    simp only [e]
    rw [integral_const_mul, h, map_mul, Complex.conj_ofReal, eOf]
    field_simp
  calc ∫ m, T n q m * Φ (g * ι m) ∂μK
      = ∫ m, ∫ k, T n q m * (eOf μ ψ ((ι m)⁻¹ * k) * Φ (g * k)) ∂μ ∂μK := by
        congr 1; funext m
        rw [hA m, integral_const_mul]
    _ = ∫ k, ∫ m, T n q m * (eOf μ ψ ((ι m)⁻¹ * k) * Φ (g * k)) ∂μK ∂μ := integral_integral_swap hint
    _ = ∫ k, eOf μ ψ k * Φ (g * k) ∂μ := by
        congr 1; funext k
        rw [← hB k, ← integral_mul_const]
        congr 1; funext m
        ring
    _ = Φ g := hfix g

private theorem innerOf (ψ : U4 → ℂ) (ι : U2 → U4) (hι : Continuous ι) (n : ℕ) (q : ℤ)
    {J : Type} [Fintype J] (j₀ : J) (a b : J → U4 → ℂ) (hc : ∀ j, Continuous (a j) ∧ Continuous (b j))
    (hexp : ∀ h k, ψ (h * k) = ∑ j, a j h * b j k) (ha : a j₀ = ψ) (hb : b j₀ = ψ)
    (hz : ∀ j, j ≠ j₀ → ∫ m, KT.psi n q n m * a j (ι m)⁻¹ ∂μK = 0)
    (hres : ∀ m, ψ (ι m)⁻¹ = conj (KT.psi n q n m)) (k : U4) :
    ∫ m, KT.psi n q n m * ψ ((ι m)⁻¹ * k) ∂μK = ((KT.normSqInt n q : ℝ) : ℂ) * ψ k := by
  have hci : ∀ j, Integrable (fun m => KT.psi n q n m * a j (ι m)⁻¹) μK := fun j =>
    KT.integrable_of_continuous ((KT.continuous_psi n q n).mul ((hc j).1.comp hι.inv))
  have h1 : ∀ m, KT.psi n q n m * ψ ((ι m)⁻¹ * k) = ∑ j, (KT.psi n q n m * a j (ι m)⁻¹) * b j k := by
    intro m
    rw [hexp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [h1]
  rw [integral_finsetSum _ fun j _ => (hci j).mul_const _]
  simp only [integral_mul_const]
  rw [Finset.sum_eq_single j₀ (fun j _ hj => by rw [hz j hj, zero_mul]) (fun h => absurd (Finset.mem_univ _) h), ha, hb]
  congr 1
  rw [← KT.integral_conj_psi_self n q]
  congr 1; funext m
  rw [hres, mul_comm]

private theorem vanish (a₀ : U4 → ℂ) (ν μ₀ : Fin (2 + 2) → ℤ) (ι : U2 → U4) (n : ℕ) (q : ℤ) (D D' : ℝ → ℝ → Fin (2 + 2) → ℝ)
    (hr : ∀ θ h, a₀ (h * dg θ) = chi ν θ * a₀ h) (hl : ∀ θ h, a₀ (dg θ * h) = chi μ₀ θ * a₀ h)
    (hmul : ∀ x y, ι (x * y) = ι x * ι y) (hD : ∀ s t, ι (tC s t) = dg (D s t))
    (hD' : ∀ s t m, dg (D' s t) * ι m = ι m * dg (D' s t))
    (hψ : ∀ s t m, KT.psi n q n (tC s t * m) = chi μ₀ (D s t) * KT.psi n q n m)
    (hsplit : (∀ s t, chi ν (D s t) = chi μ₀ (D s t)) → (∀ s t, chi ν (D' s t) = chi μ₀ (D' s t)) → ν = μ₀)
    (hne : ν ≠ μ₀) : ∫ m, KT.psi n q n m * a₀ (ι m)⁻¹ ∂μK = 0 := by
  by_contra hI
  refine hne (hsplit (fun s t => ?_) fun s t => ?_)
  · apply mul_right_cancel₀ hI
    conv_lhs => rw [← integral_mul_left_K _ (tC s t)]
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1; funext m
    have e : a₀ (ι m)⁻¹ = chi ν (D s t) * a₀ (ι (tC s t * m))⁻¹ := by
      rw [← hr, hmul, hD, _root_.mul_inv_rev, inv_mul_cancel_right]
    rw [hψ, e]
    ring
  · have hx : ∃ m, a₀ (ι m)⁻¹ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hI (by simp [hcon])
    obtain ⟨m, hm⟩ := hx
    apply mul_right_cancel₀ hm
    have hcomm : Commute (dg (D' s t)) (ι m)⁻¹ := (show Commute (dg (D' s t)) (ι m) from hD' s t m).inv_right
    rw [← hr, ← hl, hcomm.eq]

private theorem chi_add (ν : Fin (2 + 2) → ℤ) (θ θ' : Fin (2 + 2) → ℝ) : chi ν (θ + θ') = chi ν θ * chi ν θ' := by
  simp only [chi]
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  push_cast
  ring

private theorem chi_split (hchi : ∀ ν ν' : Fin (2 + 2) → ℤ, (∀ θ, chi ν θ = chi ν' θ) → ν = ν') (ν ν' : Fin (2 + 2) → ℤ)
    (h1 : ∀ s t : ℝ, chi ν ![s, t, 0, 0] = chi ν' ![s, t, 0, 0])
    (h2 : ∀ s t : ℝ, chi ν ![0, 0, s, t] = chi ν' ![0, 0, s, t]) : ν = ν' := by
  refine hchi _ _ fun θ => ?_
  have e : θ = ![θ 0, θ 1, 0, 0] + ![0, 0, θ 2, θ 3] := by
    funext i; fin_cases i <;> simp
  rw [e, chi_add, chi_add, h1, h2]

private theorem chi_wt₁ (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (s t : ℝ) :
    chi (wt n q n' q') ![s, t, 0, 0] = Complex.exp (Complex.I * ((((n : ℝ) + q) * s + ((n : ℝ) - n + q) * t : ℝ) : ℂ)) := by
  rw [chi]
  congr 2
  have := Fin.sum_univ_four (fun i : Fin 4 => ((wt n q n' q' i : ℤ) : ℂ) * (((![s, t, 0, 0] : Fin 4 → ℝ) i : ℝ) : ℂ))
  refine this.trans ?_
  simp [wt]

private theorem chi_wt₂ (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (s t : ℝ) :
    chi (wt n q n' q') ![0, 0, s, t] = Complex.exp (Complex.I * ((((n' : ℝ) + q') * s + ((n' : ℝ) - n' + q') * t : ℝ) : ℂ)) := by
  rw [chi]
  congr 2
  have := Fin.sum_univ_four (fun i : Fin 4 => ((wt n q n' q' i : ℤ) : ℂ) * (((![0, 0, s, t] : Fin 4 → ℝ) i : ℝ) : ℂ))
  refine this.trans ?_
  simp [wt]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coefFix :
    ∀ (μ : Measure U4) ψ n q n' q', Haar4 μ → μ.IsOpenPosMeasure → Coef ψ n q n' q' → ∀ Φ : U4 → ℂ, Continuous Φ → RFix μ (eOf μ ψ) Φ → ∀ g,
      ∫ m, T n q m * Φ (g * bd m 1) ∂μK = Φ g ∧ ∫ m, T n' q' m * Φ (g * bd 1 m) ∂μK = Φ g := by
  intro μ ψ n q n' q' hH hO hC Φ hΦ hfix g
  obtain ⟨hψc, -, -, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coefIdem μ ψ n q n' q' hH hO hC
  obtain ⟨-, hmul, -, hinv, hcont, -, -, -, hdg, -, hchi, -, -⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.u4
  obtain ⟨J, _, j₀, a, b, ν, hc, hexp, ha, hb, -, hw, -, hne⟩ := hC.exp
  have ht0 : tC 0 0 = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tC]
  have h1 : ∀ s t : ℝ, bd (tC s t) 1 = dg ![s, t, 0, 0] := fun s t => by rw [hdg, ht0]
  have h2 : ∀ s t : ℝ, bd 1 (tC s t) = dg ![0, 0, s, t] := fun s t => by rw [hdg, ht0]
  have hι₁ : Continuous fun m : U2 => bd m 1 := hcont.comp (continuous_id.prodMk continuous_const)
  have hι₂ : Continuous fun m : U2 => bd 1 m := hcont.comp (continuous_const.prodMk continuous_id)
  constructor
  · refine fixOf μ hH ψ hψc (fun m => bd m 1) hι₁ n q
      (fun k => innerOf ψ (fun m => bd m 1) hι₁ n q j₀ a b hc hexp ha hb (fun j hj => ?_) (fun m => ?_) k)
      Φ hΦ hfix g
    · refine vanish (a j) (ν j) (wt n q n' q') (fun m => bd m 1) n q (fun s t => ![s, t, 0, 0]) (fun s t => ![0, 0, s, t])
        (fun θ h => (hw j θ h).1) (fun θ h => (hw j θ h).2.1) (fun x y => ?_) h1 (fun s t m => ?_) (fun s t m => ?_)
        (chi_split hchi _ _) (hne j hj)
      · simp only [hmul, mul_one]
      · simp only [← h2, hmul, mul_one, one_mul]
      · rw [KT.psi_tC_mul n q le_rfl, chi_wt₁]
    · simp only [hinv, hC.res, inv_one, KT.psi_one, mul_one, KT.psi_self_inv]
  · refine fixOf μ hH ψ hψc (fun m => bd 1 m) hι₂ n' q'
      (fun k => innerOf ψ (fun m => bd 1 m) hι₂ n' q' j₀ a b hc hexp ha hb (fun j hj => ?_) (fun m => ?_) k)
      Φ hΦ hfix g
    · refine vanish (a j) (ν j) (wt n q n' q') (fun m => bd 1 m) n' q' (fun s t => ![0, 0, s, t]) (fun s t => ![s, t, 0, 0])
        (fun θ h => (hw j θ h).1) (fun θ h => (hw j θ h).2.1) (fun x y => ?_) h2 (fun s t m => ?_) (fun s t m => ?_)
        (fun e₂ e₁ => chi_split hchi _ _ e₁ e₂) (hne j hj)
      · simp only [hmul, mul_one]
      · simp only [← h1, hmul, mul_one, one_mul]
      · rw [KT.psi_tC_mul n' q' le_rfl, chi_wt₂]
    · simp only [hinv, hC.res, inv_one, KT.psi_one, one_mul, KT.psi_self_inv]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LineVal
section
open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

private theorem int_map {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (C : Co K ι) (n : ℕ)
    [MeasurableSpace (unitaryGroup (Fin n) ℂ)] [BorelSpace (unitaryGroup (Fin n) ℂ)]
    (ν : Measure (ι → unitaryGroup (Fin n) ℂ)) (F : archCompact K n → ℂ) :
    ∫ k, F k ∂(Measure.map (C.Φ n).symm ν) = ∫ y, F ((C.Φ n).symm y) ∂ν :=
  ((C.Φ n).symm.toHomeomorph.measurableEmbedding).integral_map F

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.lineVal :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), Pair μ₂ τ₁ τ₂ →
      ∀ (μ : Measure U4) (e : ι → U4 → ℂ) n q n' q' (x : ι → U4), Haar4 μ → ExtP μ e n q n' q' x →
      IdemA (C.κ₄ μ) (C.e e) ∧ ∀ f, IsSec τ₁ τ₂ f → FixA (C.κ₄ μ) (C.e e) f → ∀ h : FA K (2 + 2),
        (∀ m₂, FixA C.κ₂ (C.p n q) fun m₁ => f (lv m₁ m₂ 0 * arc1 ((C.Φ (2 + 2)).symm x) * fin1 h)) ∧
        ∀ m₁, FixA C.κ₂ (C.p n' q') fun m₂ => f (lv m₁ m₂ 0 * arc1 ((C.Φ (2 + 2)).symm x) * fin1 h) := by
  intro K _ _ _ ι _ C μ₂ _ τ₁ τ₂ _ μ e n q n' q' x h4 hE
  obtain ⟨hκ₂, hκ₄, -, -, -, -, -, -, -, hlv, hcomm, -⟩ := coLaws K ι C
  have hb := blkLaws (K := K)
  have hmul := hb.2.1
  have he : ∀ k, C.e e ((C.Φ (2 + 2)).symm k) = ∏ i, e i (k i) := by
    intro k; simp only [Co.e, ContinuousMulEquiv.apply_symm_apply]
  have hp : ∀ (a : ι → ℕ) (b : ι → ℤ) k, C.p a b ((C.Φ 2).symm k) = ∏ i, T (a i) (b i) (k i) := by
    intro a b k; simp only [Co.p, ContinuousMulEquiv.apply_symm_apply]
  have ha : ∀ a b : ι → U4, arc1 ((C.Φ (2 + 2)).symm (a * b)) =
      arc1 ((C.Φ (2 + 2)).symm a) * arc1 ((C.Φ (2 + 2)).symm b) := by
    intro a b
    change arc1 ((C.Φ (2 + 2)).symm.toMulEquiv (a * b)) =
      arc1 ((C.Φ (2 + 2)).symm.toMulEquiv a) * arc1 ((C.Φ (2 + 2)).symm.toMulEquiv b)
    rw [(C.Φ (2 + 2)).symm.toMulEquiv.map_mul]
    simp [arc1]
  have h1 : (arc1 ((C.Φ 2).symm (1 : ι → U2)) : G1 K 2) = 1 := by simp [arc1, map_one]
  refine ⟨⟨hκ₄ μ h4, ?_, ?_, ?_⟩, ?_⟩
  · exact hE.idem.cont.comp (C.Φ (2 + 2)).continuous
  · intro k
    have := hE.idem.star (C.Φ (2 + 2) k)
    simp only [Co.e, map_inv]
    exact this
  · intro k
    have := hE.idem.idem (C.Φ (2 + 2) k)
    rw [Co.κ₄, int_map]
    simp only [Co.e, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply]
    exact this
  · intro f hf hfix h
    have hc : ∀ L : G1 K (2 + 2), Continuous fun k : ι → U4 => f (L * fin1 h * arc1 ((C.Φ (2 + 2)).symm k)) := by
      intro L
      refine hf.cont.comp (continuous_const.mul ?_)
      exact continuous_archP.comp (continuous_subtype_val.comp (C.Φ (2 + 2)).symm.continuous)
    have hr : ∀ L : G1 K (2 + 2), RFix (Measure.pi fun _ : ι => μ) (fun k => ∏ i, e i (k i))
        fun k : ι → U4 => f (L * fin1 h * arc1 ((C.Φ (2 + 2)).symm k)) := by
      intro L g
      have := hfix (L * fin1 h * arc1 ((C.Φ (2 + 2)).symm g))
      rw [Co.κ₄, int_map] at this
      simp only [he] at this
      simp only [ha, ← mul_assoc]
      exact this
    refine ⟨fun m₂ g => ?_, fun m₁ g => ?_⟩
    · have := (hE.fix _ (hc (lv g m₂ 0)) (hr (lv g m₂ 0)) 1).1
      simp only [one_mul] at this
      change ∫ k, C.p n q k * f (lv (g * arc1 k) m₂ 0 * arc1 ((C.Φ (2 + 2)).symm x) * fin1 h) ∂C.κ₂ = _
      rw [Co.κ₂, int_map]
      simp only [hp]
      have e1 : ∀ m : ι → U2, lv (g * arc1 ((C.Φ 2).symm m)) m₂ 0 * arc1 ((C.Φ (2 + 2)).symm x) * fin1 h =
          lv g m₂ 0 * fin1 h * arc1 ((C.Φ (2 + 2)).symm ((fun i => bd (m i) 1) * x)) := by
        intro m
        have hl := hlv m 1
        rw [h1] at hl
        have h2 : lv (g * arc1 ((C.Φ 2).symm m)) m₂ 0 =
            lv g m₂ 0 * arc1 ((C.Φ (2 + 2)).symm fun i => bd (m i) 1) := by
          have := hmul g m₂ (arc1 ((C.Φ 2).symm m)) 1 0 0
          rw [hl, mul_one, add_zero] at this
          exact this.symm
        rw [h2, ha, mul_assoc (lv g m₂ 0), mul_assoc (lv g m₂ 0), mul_assoc (lv g m₂ 0), ← ha,
          (hcomm _ _ h).eq]
      simp only [e1]
      rw [this, mul_assoc (lv g m₂ 0), mul_assoc (lv g m₂ 0), (hcomm _ _ h).eq]
    · have := (hE.fix _ (hc (lv m₁ g 0)) (hr (lv m₁ g 0)) 1).2
      simp only [one_mul] at this
      change ∫ k, C.p n' q' k * f (lv m₁ (g * arc1 k) 0 * arc1 ((C.Φ (2 + 2)).symm x) * fin1 h) ∂C.κ₂ = _
      rw [Co.κ₂, int_map]
      simp only [hp]
      have e1 : ∀ m : ι → U2, lv m₁ (g * arc1 ((C.Φ 2).symm m)) 0 * arc1 ((C.Φ (2 + 2)).symm x) * fin1 h =
          lv m₁ g 0 * fin1 h * arc1 ((C.Φ (2 + 2)).symm ((fun i => bd 1 (m i)) * x)) := by
        intro m
        have hl := hlv 1 m
        rw [h1] at hl
        have h2 : lv m₁ (g * arc1 ((C.Φ 2).symm m)) 0 =
            lv m₁ g 0 * arc1 ((C.Φ (2 + 2)).symm fun i => bd 1 (m i)) := by
          have := hmul m₁ g 1 (arc1 ((C.Φ 2).symm m)) 0 0
          rw [hl, mul_one, add_zero] at this
          exact this.symm
        rw [h2, ha, mul_assoc (lv m₁ g 0), mul_assoc (lv m₁ g 0), mul_assoc (lv m₁ g 0), ← ha,
          (hcomm _ _ h).eq]
      simp only [e1]
      rw [this, mul_assoc (lv m₁ g 0), mul_assoc (lv m₁ g 0), (hcomm _ _ h).eq]
end

