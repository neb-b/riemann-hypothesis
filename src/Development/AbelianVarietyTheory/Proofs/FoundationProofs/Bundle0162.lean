module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0157

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqMulAndQExpansion
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem polyB_mul (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) : PolyB (mul a b) := by
  obtain ⟨C, A, hC⟩ := ha
  obtain ⟨C', A', hC'⟩ := hb
  have C0 : 0 ≤ C := by
    have := hC 0
    simp at this
    exact le_trans (norm_nonneg _) this
  have C0' : 0 ≤ C' := by
    have := hC' 0
    simp at this
    exact le_trans (norm_nonneg _) this
  refine ⟨C * C', A + A' + 1, fun n => ?_⟩
  unfold mul
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  calc ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2‖
      ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ‖a p.1 * b p.2‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, C * C' * ((n : ℝ) + 1) ^ (A + A') := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        rw [norm_mul]
        have h1 : ((p.1 : ℝ) + 1) ≤ (n : ℝ) + 1 := by
          have : p.1 ≤ n := by omega
          exact_mod_cast Nat.add_le_add_right this 1
        have h2 : ((p.2 : ℝ) + 1) ≤ (n : ℝ) + 1 := by
          have : p.2 ≤ n := by omega
          exact_mod_cast Nat.add_le_add_right this 1
        have e1 : ‖a p.1‖ ≤ C * ((n : ℝ) + 1) ^ A :=
          (hC p.1).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 A) C0)
        have e2 : ‖b p.2‖ ≤ C' * ((n : ℝ) + 1) ^ A' :=
          (hC' p.2).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 A') C0')
        calc ‖a p.1‖ * ‖b p.2‖ ≤ (C * ((n : ℝ) + 1) ^ A) * (C' * ((n : ℝ) + 1) ^ A') :=
              mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
          _ = C * C' * ((n : ℝ) + 1) ^ (A + A') := by rw [pow_add]; ring
    _ = (n + 1 : ℕ) * (C * C' * ((n : ℝ) + 1) ^ (A + A')) := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
    _ = C * C' * ((n : ℝ) + 1) ^ (A + A' + 1) := by push_cast; ring

theorem qs_mul (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) :
    qs (mul a b) = fun τ => qs a τ * qs b τ := by
  funext τ
  have sa := (_root_.GlobalTheory.EisM.qs_summable_continuous a ha).1 τ
  have sb := (_root_.GlobalTheory.EisM.qs_summable_continuous b hb).1 τ
  unfold qs
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm sa sb]
  congr 1
  funext n
  unfold mul
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have e : cexp (2 * π * Complex.I * (n : ℂ) * τ) =
      cexp (2 * π * Complex.I * (p.1 : ℂ) * τ) * cexp (2 * π * Complex.I * (p.2 : ℂ) * τ) := by
    rw [← Complex.exp_add, ← hp]
    congr 1
    push_cast
    ring
  rw [e]
  ring

theorem mul_main : (∀ a b : ℕ → ℂ, PolyB a → PolyB b → PolyB (mul a b) ∧ qs (mul a b) = fun τ => qs a τ * qs b τ) ∧ ∀ (k k' L : ℕ) (χ χ' : ℤ → ℂ) (a b : ℕ → ℂ), MF k L χ a → MF k' L χ' b → MF (k + k') L (fun d => χ d * χ' d) (mul a b) := by
  refine ⟨fun a b ha hb => ⟨polyB_mul a b ha hb, qs_mul a b ha hb⟩, ?_⟩
  intro k k' L χ χ' a b ha hb
  refine ⟨polyB_mul a b ha.1 hb.1, ?_⟩
  intro γ hγ τ
  rw [qs_mul a b ha.1 hb.1]
  simp only
  rw [ha.2 γ hγ τ, hb.2 γ hγ τ, pow_add]
  ring

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGammaOneOfCoeffSeq
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.OnGammaOne

theorem slash_inv {k L N : ℕ} {ε : DirichletCharacter ℂ N} (hNL : N ∣ L) {f : ℍ → ℂ}
    (hf : Inv k L (ch ε) f) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 L) : f ∣[(k : ℤ)] γ = f := by
  obtain ⟨-, h11, h10⟩ := (Gamma1_mem L γ).1 hγ
  have hc : (L : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h10
  have hd1 : (L : ℤ) ∣ γ 1 1 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h11, sub_self]
  have hd : ch ε (γ 1 1) = 1 := by
    have h2 : (N : ℤ) ∣ γ 1 1 - 1 := (Int.natCast_dvd_natCast.2 hNL).trans hd1
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    push_cast at h2
    have h3 : ((γ 1 1 : ℤ) : ZMod N) = 1 := sub_eq_zero.1 h2
    simp [ch, h3]
  funext τ
  rw [ModularForm.slash_action_eq'_iff, hf γ hc τ, hd, one_mul, zpow_natCast]

theorem periodic {k L : ℕ} {f : ℍ → ℂ} (hinv : ∀ γ ∈ Gamma1 L, f ∣[(k : ℤ)] γ = f)
    (γ : SL(2, ℤ)) (τ : ℍ) : (f ∣[(k : ℤ)] γ) ((L : ℝ) +ᵥ τ) = (f ∣[(k : ℤ)] γ) τ := by
  have hT : (ModularGroup.T ^ (L : ℤ)) • τ = (L : ℝ) +ᵥ τ := by
    rw [modular_T_zpow_smul]; simp
  have hδ : γ * ModularGroup.T ^ (L : ℤ) * γ⁻¹ ∈ Gamma1 L := by
    have h1 : ModularGroup.T ^ (L : ℤ) ∈ CongruenceSubgroup.Gamma L := by
      simpa using ModularGroup_T_pow_mem_Gamma (L : ℤ) (L : ℤ) dvd_rfl
    have h2 := (Gamma_normal L).conj_mem _ h1 γ
    rw [Gamma_mem] at h2
    rw [Gamma1_mem]
    exact ⟨h2.1, h2.2.2.2, h2.2.2.1⟩
  have e : (f ∣[(k : ℤ)] γ) ∣[(k : ℤ)] (ModularGroup.T ^ (L : ℤ)) = f ∣[(k : ℤ)] γ := by
    rw [← SlashAction.slash_mul,
      (inv_mul_cancel_right (γ * ModularGroup.T ^ (L : ℤ)) γ).symm,
      SlashAction.slash_mul, hinv _ hδ]
  have h := congrFun e τ
  have hden : denom (ModularGroup.T ^ (L : ℤ) : SL(2, ℤ)) τ = 1 := by
    rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]; simp
  rw [ModularForm.SL_slash_apply (f := f ∣[(k : ℤ)] γ), hT, hden, one_zpow, mul_one] at h
  exact h

end GlobalTheory.EisM.OnGammaOne

namespace GlobalTheory.EisM.OnGammaOne

theorem normSq_denom_bounds (L : ℕ) (γ : SL(2, ℤ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℍ, 1 ≤ τ.im → |τ.re| ≤ L →
      1 ≤ Complex.normSq (denom γ τ) ∧ Complex.normSq (denom γ τ) ≤ K * τ.im ^ 2 := by
  set c : ℝ := ((γ 1 0 : ℤ) : ℝ)
  set d : ℝ := ((γ 1 1 : ℤ) : ℝ)
  refine ⟨(|c| * L + |d|) ^ 2 + c ^ 2, by positivity, fun τ h1 h2 => ?_⟩
  have hns : Complex.normSq (denom γ τ) = (c * τ.re + d) ^ 2 + (c * τ.im) ^ 2 := by
    rw [ModularGroup.denom_apply, Complex.normSq_apply]
    simp [c, d]
    ring
  rw [hns]
  have hy0 : 0 ≤ τ.im := τ.im_pos.le
  have hy2 : 1 ≤ τ.im ^ 2 := by nlinarith
  constructor
  · by_cases hc : γ 1 0 = 0
    · have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
        have := γ.2; rw [Matrix.det_fin_two] at this; exact this
      rw [hc, mul_zero, sub_zero] at hdet
      have hd : γ 1 1 = 1 ∨ γ 1 1 = -1 := by
        rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with h | h
        · exact Or.inl h.2
        · exact Or.inr h.2
      have hc' : c = 0 := by simp [c, hc]
      have hd' : d ^ 2 = 1 := by rcases hd with h | h <;> simp [d, h]
      rw [hc']; nlinarith
    · have hc1 : 1 ≤ c ^ 2 := by
        have : (1 : ℤ) ≤ (γ 1 0) ^ 2 := by
          have := Int.one_le_abs hc
          nlinarith [sq_abs (γ 1 0)]
        have : ((1 : ℤ) : ℝ) ≤ (((γ 1 0) ^ 2 : ℤ) : ℝ) := by exact_mod_cast this
        simpa [c] using this
      nlinarith [sq_nonneg (c * τ.re + d)]
  · have hM : |c * τ.re + d| ≤ |c| * L + |d| := by
      calc |c * τ.re + d| ≤ |c * τ.re| + |d| := abs_add_le _ _
        _ = |c| * |τ.re| + |d| := by rw [abs_mul]
        _ ≤ |c| * L + |d| := by gcongr
    have hM2 : (c * τ.re + d) ^ 2 ≤ (|c| * L + |d|) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hM 2
    have hM0 : 0 ≤ (|c| * L + |d|) ^ 2 := by positivity
    nlinarith

theorem growth {f : ℍ → ℂ} (hf : Mod f) (k L : ℕ) (γ : SL(2, ℤ)) :
    ∃ (C : ℝ) (A : ℕ), ∀ τ : ℍ, 1 ≤ τ.im → |τ.re| ≤ L → ‖(f ∣[(k : ℤ)] γ) τ‖ ≤ C * τ.im ^ A := by
  obtain ⟨C, A, hC⟩ := hf
  obtain ⟨K, hK0, hK⟩ := normSq_denom_bounds L γ
  refine ⟨|C| * (1 + K ^ A), A, fun τ h1 h2 => ?_⟩
  obtain ⟨hD1, hDK⟩ := hK τ h1 h2
  set D := Complex.normSq (denom γ τ) with hD
  set y := τ.im with hy
  have hy0 : 0 < y := τ.im_pos
  have hD0 : 0 < D := by linarith
  have him : (γ • τ).im = y / D := ModularGroup.im_smul_eq_div_normSq γ τ
  have hw1 : (γ • τ).im ^ A ≤ y ^ A := by
    rw [him]
    exact pow_le_pow_left₀ (by positivity) (div_le_self hy0.le hD1) A
  have hw2 : ((γ • τ).im ^ A)⁻¹ ≤ K ^ A * y ^ A := by
    rw [him, ← inv_pow, inv_div, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ A
    rw [div_le_iff₀ hy0]
    nlinarith
  have hden : ‖denom γ τ ^ (-(k : ℤ))‖ ≤ 1 := by
    have hn : 1 ≤ ‖denom γ τ‖ := by
      have : 1 ≤ ‖denom γ τ‖ ^ 2 := by rw [← Complex.normSq_eq_norm_sq]; exact hD1
      nlinarith [norm_nonneg (denom γ τ)]
    rw [norm_zpow, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hn)
  rw [ModularForm.SL_slash_apply, norm_mul]
  have hfw := hC (γ • τ)
  have hpos : 0 ≤ (γ • τ).im ^ A + ((γ • τ).im ^ A)⁻¹ := by
    have := (γ • τ).im_pos; positivity
  calc ‖f (γ • τ)‖ * ‖denom γ τ ^ (-(k : ℤ))‖ ≤ ‖f (γ • τ)‖ * 1 :=
        mul_le_mul_of_nonneg_left hden (norm_nonneg _)
    _ ≤ |C| * ((γ • τ).im ^ A + ((γ • τ).im ^ A)⁻¹) := by
        rw [mul_one]; exact hfw.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hpos)
    _ ≤ |C| * (y ^ A + K ^ A * y ^ A) := by gcongr
    _ = |C| * (1 + K ^ A) * y ^ A := by ring

end GlobalTheory.EisM.OnGammaOne


open GlobalTheory.EisM.OnGammaOne in
theorem GlobalTheory.EisM.modularForm_gammaOne_of_MF :
    ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 0 < L → N ∣ L → MF k L (ch ε) a →
      ∃ f : ModularForm (Gamma1 L) (k : ℤ), ⇑f = qs a := by
  intro k L N ε a hL hNL ha
  haveI : NeZero L := ⟨hL.ne'⟩
  have hinv : ∀ γ ∈ Gamma1 L, qs a ∣[(k : ℤ)] γ = qs a := fun γ hγ => slash_inv hNL ha.2 γ hγ
  have hhol := _root_.GlobalTheory.EisM.qs_mdifferentiable a ha.1
  refine ⟨{ toFun := qs a, slash_action_eq' := ?_, holo' := hhol, bdd_at_cusps' := ?_ }, rfl⟩
  · rintro _ ⟨A, (hA : A ∈ Gamma1 L), rfl⟩
    exact hinv A hA
  · intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    obtain ⟨C, A, hC⟩ := growth (_root_.GlobalTheory.EisM.mod_qs_of_polyB a ha.1) k L γ
    have hs : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qs a ∣[(k : ℤ)] γ) := by
      rw [ModularForm.SL_slash]; exact hhol.slash _ _
    exact _root_.GlobalTheory.isBoundedAtImInfty_of_periodic_of_polyBound _ L C A hL hs (periodic hinv γ) hC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonDoubleCosetAdjoint
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.PetAdj

def toG (δ : M2) : GL (Fin 2) ℝ :=
  if hd : ((Int.castRingHom ℝ).mapMatrix δ).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd else 1

lemma toG_val (δ : M2) (hδ : δ.det ≠ 0) :
    (toG δ : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix δ := by
  have hd : ((Int.castRingHom ℝ).mapMatrix δ).det ≠ 0 := by
    rw [← RingHom.map_det]; simpa using hδ
  rw [toG, dite_eq_left hd]; rfl

lemma toG_det (δ : M2) (hδ : 0 < δ.det) : 0 < (toG δ).det.val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, toG_val δ hδ.ne', ← RingHom.map_det]
  simpa using hδ

def K (k N : ℕ) (ε : DirichletCharacter ℂ N) (h f : ℍ → ℂ) (δ : M2) (τ : ℍ) : ℂ :=
  ch ε (δ 0 0) * (conj (h τ) * slz k δ f τ * (τ.im : ℂ) ^ k)

lemma ch_unit (N : ℕ) (ε : DirichletCharacter ℂ N) (γ : SL(2, ℤ)) (hγ : (N : ℤ) ∣ γ 1 0) :
    ch ε (γ 0 0) * ch ε (γ 1 1) = 1 := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have h0 : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hγ
  have h2 : (((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ)) : ZMod N) = 1 := by rw [hdet]; simp
  push_cast at h2
  rw [h0, mul_zero, sub_zero] at h2
  simp only [ch, ← map_mul, h2, map_one]

lemma conj_ch_inv (N : ℕ) (ε : DirichletCharacter ℂ N) (x : ℤ) : conj (ch ε⁻¹ x) = ch ε x := by
  have := MulChar.star_apply' ε⁻¹ (x : ZMod N)
  simp only [inv_inv] at this
  exact this

lemma K_left (k L N : ℕ) (ε : DirichletCharacter ℂ N) (h f : ℍ → ℂ) (hk : 1 ≤ k) (hNL : N ∣ L)
    (hf : Inv k L (ch ε) f) (γ : SL(2, ℤ)) (hγ : (L : ℤ) ∣ γ 1 0) (δ : M2) (hδ : 0 < δ.det)
    (hδN : (N : ℤ) ∣ δ 1 0) (τ : ℍ) :
    K k N ε h f ((γ : M2) * δ) τ = K k N ε h f δ τ := by
  obtain ⟨hcoc, -, hinv, -, -⟩ := _root_.GlobalTheory.EisM.slz_props k f hk
  have hγN : (N : ℤ) ∣ γ 1 0 := dvd_trans (Int.natCast_dvd_natCast.mpr hNL) hγ
  have h1 : slz k ((γ : M2) * δ) f τ = ch ε (γ 1 1) * slz k δ f τ := by
    rw [hcoc _ _ (by simp) hδ, (hinv L (ch ε)).mp hf γ hγ]
    simp only [slz]; ring
  have hd : ((δ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hδN
  have e : ch ε (((γ : M2) * δ) 0 0) = ch ε (γ 0 0) * ch ε (δ 0 0) := by
    simp only [ch, ← map_mul]
    congr 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, hd]
  have hu := ch_unit N ε γ hγN
  simp only [K, h1, e]
  linear_combination (ch ε (δ 0 0) * (conj (h τ) * slz k δ f τ * (τ.im : ℂ) ^ k)) * hu

lemma K_right (k L N : ℕ) (ε : DirichletCharacter ℂ N) (h f : ℍ → ℂ) (hk : 1 ≤ k) (hNL : N ∣ L)
    (hh : Inv k L (ch ε) h) (γ : SL(2, ℤ)) (hγ : (L : ℤ) ∣ γ 1 0) (δ : M2) (hδ : 0 < δ.det) (τ : ℍ) :
    K k N ε h f (δ * (γ : M2)) τ = K k N ε h f δ (γ • τ) := by
  have hcoc := (_root_.GlobalTheory.EisM.slz_props k f hk).1
  have hsl := (_root_.GlobalTheory.EisM.slz_props k (slz k δ f) hk).2.1
  have hγN : (N : ℤ) ∣ γ 1 0 := dvd_trans (Int.natCast_dvd_natCast.mpr hNL) hγ
  have e2 := hh γ hγ τ
  have e1 := (congrFun (hcoc δ (γ : M2) hδ (by simp)) τ).trans (hsl γ τ)
  have hden : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ)
      = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    simp [denom]
  have hj : ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact denom_ne_zero _ _
  have e3 := ModularGroup.im_smul_eq_div_normSq γ τ
  rw [hden] at e3
  generalize ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) = j at *
  have e3' : ((γ • τ).im : ℂ) = (τ.im : ℂ) / (j * conj j) := by
    rw [e3, Complex.mul_conj]; push_cast; rfl
  have hd : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hγN
  have e4 : ch ε ((δ * (γ : M2)) 0 0) = ch ε (δ 0 0) * ch ε (γ 0 0) := by
    simp only [ch, ← map_mul]
    congr 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, hd]
  have hu := ch_unit N ε γ hγN
  have hc : conj (ch ε (γ 1 1)) = ch ε (γ 0 0) := by
    have h1 : conj (ch ε (γ 1 1)) = (ch ε (γ 1 1))⁻¹ := by
      have := MulChar.star_apply' ε ((γ 1 1 : ℤ) : ZMod N)
      rw [MulChar.inv_apply_eq_inv'] at this
      exact this
    rw [h1]; exact (eq_inv_of_mul_eq_one_left hu).symm
  have hj' : conj j ≠ 0 := by simpa using hj
  simp only [K, e1, e2, e3', e4, map_mul, map_pow, hc, div_pow, mul_pow]
  field_simp

lemma K_adj (k N : ℕ) (ε : DirichletCharacter ℂ N) (h f : ℍ → ℂ) (α : M2) (hα : 0 < α.det) (s : ℍ) :
    K k N ε h f α s = conj (ch ε⁻¹ (α 0 0) * slz k α.adjugate h (toG α • s)) * f (toG α • s) *
      ((toG α • s).im : ℂ) ^ k := by
  have hv := toG_val α hα.ne'
  have hden : denom (toG α) (s : ℂ) = ((α 1 0 : ℤ) : ℂ) * s + ((α 1 1 : ℤ) : ℂ) := by
    simp [denom, hv]
  have hnum : num (toG α) (s : ℂ) = ((α 0 0 : ℤ) : ℂ) * s + ((α 0 1 : ℤ) : ℂ) := by
    simp [num, hv]
  have hj : ((α 1 0 : ℤ) : ℂ) * s + ((α 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact denom_ne_zero _ _
  have ht := coe_smul_of_det_pos (toG_det α hα) s
  have him := im_smul_eq_div_normSq (toG α) s
  have hdet : (toG α).det.val = (α.det : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hv, ← RingHom.map_det]; simp
  rw [abs_of_pos (toG_det α hα), hdet, hden] at him
  rw [hden, hnum] at ht
  generalize toG α • s = t at *
  have hQ : ((α.det : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have hQe : ((α.det : ℤ) : ℂ) = (α 0 0 : ℂ) * (α 1 1 : ℂ) - (α 0 1 : ℂ) * (α 1 0 : ℂ) := by
    rw [Matrix.det_fin_two]; push_cast; ring
  have hda : α.adjugate.det = α.det := by
    rw [Matrix.det_adjugate]; simp
  have hA : ((α.adjugate 1 0 : ℤ) : ℂ) * t + ((α.adjugate 1 1 : ℤ) : ℂ)
      = ((α.det : ℤ) : ℂ) / (((α 1 0 : ℤ) : ℂ) * s + ((α 1 1 : ℤ) : ℂ)) := by
    rw [hQe, ht, Matrix.adjugate_fin_two, eq_div_iff hj]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    linear_combination (-((α 1 0 : ℤ) : ℂ) * (((α 0 0 : ℤ) : ℂ) * s + ((α 0 1 : ℤ) : ℂ))) * mul_inv_cancel₀ hj
  have hB : ((α.adjugate 0 0 : ℤ) : ℂ) * t + ((α.adjugate 0 1 : ℤ) : ℂ)
      = ((α.det : ℤ) : ℂ) * s / (((α 1 0 : ℤ) : ℂ) * s + ((α 1 1 : ℤ) : ℂ)) := by
    rw [hQe, ht, Matrix.adjugate_fin_two, eq_div_iff hj]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    linear_combination (((α 1 1 : ℤ) : ℂ) * (((α 0 0 : ℤ) : ℂ) * s + ((α 0 1 : ℤ) : ℂ))) * mul_inv_cancel₀ hj
  simp only [K, slz]
  rw [hA, hB, ← ht, hda, ofComplex_apply]
  generalize ((α 1 0 : ℤ) : ℂ) * s + ((α 1 1 : ℤ) : ℂ) = j at *
  have hs : ((α.det : ℤ) : ℂ) * s / j / (((α.det : ℤ) : ℂ) / j) = s := by field_simp
  have him' : (t.im : ℂ) = ((α.det : ℤ) : ℂ) * (s.im : ℂ) / (j * conj j) := by
    rw [him, Complex.mul_conj, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_intCast]
  have hj' : conj j ≠ 0 := by simpa using hj
  rw [hs, ofComplex_apply, him']
  simp only [map_mul, map_pow, map_inv₀, map_div₀, map_intCast, conj_ch_inv, div_pow, mul_pow]
  field_simp

end GlobalTheory.EisM.PetAdj


open GlobalTheory.EisM.PetAdj in
theorem GlobalTheory.EisM.pet_hsum_adjoint : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (Δ : Set M2) (ι κ : Type) [Fintype ι] [Fintype κ] (β : ι → M2) (α : κ → M2) (h f : ℍ → ℂ), 1 ≤ k → 0 < N → N ∣ L → 0 < q → q.Coprime N → Wt L ρ → (∀ δ ∈ Δ, δ.det = q ∧ (N : ℤ) ∣ δ 1 0) → LRep L Δ β → RRep L Δ α → Inv k L (ch ε) h → Inv k L (ch ε) f → Continuous h → Continuous f → (∀ i, Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (h τ) * slz k (β i) f τ * (τ.im : ℂ) ^ k))) → pet k ρ h (hsum k (ch ε) β f) = pet k ρ (fun τ => ∑ j, ch ε⁻¹ (α j 0 0) * slz k (α j).adjugate h τ) f := by
  intro k L N q ε ρ Δ ι κ _ _ β α h f hk _ hNL hq _ hρ hΔ hL hR hh hf hhc hfc hint
  have hcont := (_root_.GlobalTheory.EisM.slz_props k f hk).2.2.2.1
  have hβ : ∀ i, β i ∈ Δ := fun i => by
    simpa using hL.mapsTo (Set.mem_univ ((1 : Gamma0 L), i))
  have hα : ∀ j, α j ∈ Δ := fun j => by
    simpa using hR.mapsTo (Set.mem_univ (j, (1 : Gamma0 L)))
  have hdet : ∀ δ ∈ Δ, 0 < δ.det := fun δ hδ => by rw [(hΔ δ hδ).1]; exact_mod_cast hq
  have hΓ : ∀ γ : Gamma0 L, (L : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := fun γ =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp γ.2)
  let eL : Gamma0 L × ι ≃ Δ := (Equiv.Set.univ _).symm.trans (Set.BijOn.equiv _ hL)
  let eR : κ × Gamma0 L ≃ Δ := (Equiv.Set.univ _).symm.trans (Set.BijOn.equiv _ hR)
  obtain ⟨e, he⟩ : ∃ e : Gamma0 L × ι ≃ κ × Gamma0 L, ∀ p : Gamma0 L × ι,
      ((p.1 : SL(2, ℤ)) : M2) * β p.2 = α (e p).1 * (((e p).2 : SL(2, ℤ)) : M2) :=
    ⟨eL.trans eR.symm, fun p => (congrArg Subtype.val (eR.apply_symm_apply (eL p))).symm⟩
  let φ : Gamma0 L →* GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ).comp (Gamma0 L).subtype
  have hφv : ∀ γ : Gamma0 L, (φ γ : Matrix (Fin 2) (Fin 2) ℝ)
      = (Int.castRingHom ℝ).mapMatrix ((γ : SL(2, ℤ)) : M2) := fun γ => rfl
  have hP : ∀ i, Integrable (fun x : ℍ => (ρ x : ℂ) * K k N ε h f (β i) x) := fun i => by
    refine ((hint i).const_mul (ch ε (β i 0 0))).congr (Eventually.of_forall fun x => ?_)
    simp only [K]; ring
  haveI : Countable SL(2, ℤ) := by
    unfold Matrix.SpecialLinearGroup Matrix; infer_instance
  obtain ⟨hQ, key⟩ := _root_.GlobalTheory.EisM.abstract_double_coset_adjoint (GL (Fin 2) ℝ) ℍ (Gamma0 L) ι κ volume φ ρ (fun i => toG (β i))
    (fun j => toG (α j)) e (fun i => K k N ε h f (β i)) (fun j => K k N ε h f (α j))
    hρ.meas hρ.nonneg hρ.sum
    (fun p => by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hφv, hφv, toG_val _ (hdet _ (hβ _)).ne',
        toG_val _ (hdet _ (hα _)).ne', ← map_mul, ← map_mul, he])
    (fun p x => by
      rw [← K_left k L N ε h f hk hNL hf p.1 (hΓ _) _ (hdet _ (hβ _)) (hΔ _ (hβ _)).2, he,
        K_right k L N ε h f hk hNL hh _ (hΓ _) _ (hdet _ (hα _))]
      rfl)
    hP
    (fun j => by
      refine Continuous.aestronglyMeasurable ?_
      have := hcont _ (hdet _ (hα j)) hfc
      have him : Continuous fun τ : ℍ => (τ.im : ℂ) :=
        Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im
      exact continuous_const.mul (((Complex.continuous_conj.comp hhc).mul this).mul (him.pow k)))
  have hC : ∀ j (x : ℍ), K k N ε h f (α j) ((toG (α j))⁻¹ • x) =
      conj (ch ε⁻¹ (α j 0 0) * slz k (α j).adjugate h x) * f x * (x.im : ℂ) ^ k := fun j x => by
    rw [K_adj k N ε h f _ (hdet _ (hα j)), smul_inv_smul]
  rw [← integral_finsetSum _ fun i _ => hP i, ← integral_finsetSum _ fun j _ => hQ j] at key
  simp only [hC] at key
  unfold pet hsum
  refine Eq.trans ?_ (key.trans ?_)
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [K, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.mul_sum, Finset.sum_mul]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerLevelEqPowMulHeckeVStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_slash_heckeRepLowerLevel_eq_pow_mul_heckeV : ∀ (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ), 1 ≤ k → 0 < l → MF k N (ch ε) h → ∀ τ : ℍ, ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ k * qs (Vo l h) τ := by
  first | exact @GlobalTheory.EisM.adjU_sum | exact GlobalTheory.EisM.adjU_sum | (intros; apply GlobalTheory.EisM.adjU_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSumIccPeriodicMulInvFloorDivStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_sum_Icc_periodic_mul_inv_floor_div : ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im → hat φ 0 = 0 → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R:ℤ)) R, φ d * (z + (L * (d / L) : ℤ))⁻¹) atTop (𝓝 0) := by
  first | exact @GlobalTheory.FloorTelescope.tendsto_sum_Icc_div | exact GlobalTheory.FloorTelescope.tendsto_sum_Icc_div | (intros; apply GlobalTheory.FloorTelescope.tendsto_sum_Icc_div <;> assumption)
end

