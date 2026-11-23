module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0175
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0160
public import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0176
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerSlashIsModularFormCoeffSeq
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.AtkinLehnerForm

theorem toGL_entry (A : M2) (hA : A.det ≠ 0) (i j : Fin 2) :
    (↑(GlobalTheory.HeckeFamilyMatrices.toGL A) : Matrix (Fin 2) (Fin 2) ℝ) i j = (A i j : ℝ) := by
  rw [GlobalTheory.HeckeFamilyMatrices.toGL_val A hA]; simp

theorem slz_eq_slash (k : ℕ) (hk : 1 ≤ k) (δ : M2) (hδ : 0 < δ.det) (f : ℍ → ℂ) :
    slz k δ f = f ∣[(k : ℤ)] GlobalTheory.HeckeFamilyMatrices.toGL δ := by
  funext τ
  have hd : 0 < (GlobalTheory.HeckeFamilyMatrices.toGL δ).det.val := GlobalTheory.HeckeFamilyMatrices.toGL_det_pos δ hδ
  have hpt : ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)))
      = GlobalTheory.HeckeFamilyMatrices.toGL δ • τ := by
    ext1
    rw [slzMob_coe δ hδ τ, UpperHalfPlane.coe_smul_of_det_pos hd]
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, toGL_entry δ hδ.ne']
  rw [ModularForm.slash_apply, GlobalTheory.HeckeFamilyMatrices.sigma_pos hd, slz, hpt]
  have hdet : (GlobalTheory.HeckeFamilyMatrices.toGL δ).det.val = (δ.det : ℝ) := GlobalTheory.HeckeFamilyMatrices.toGL_det δ hδ.ne'
  rw [hdet, abs_of_pos (by exact_mod_cast hδ)]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e1 : (((m + 1 : ℕ) : ℤ) - 1) = ((m : ℕ) : ℤ) := by push_cast; ring
  rw [e1, zpow_natCast, zpow_neg, zpow_natCast]
  simp only [Nat.add_sub_cancel, UpperHalfPlane.denom, toGL_entry δ hδ.ne', Complex.ofReal_intCast]
  ring

end GlobalTheory.EisM.AtkinLehnerForm

namespace GlobalTheory.EisM.AtkinLehnerForm

theorem qs_add_int (a : ℕ → ℂ) (τ : ℍ) (m : ℤ) : qs a (ofComplex ((τ : ℂ) + m)) = qs a τ := by
  have him : 0 < ((τ : ℂ) + m).im := by simpa using τ.im_pos
  have hcoe : ((ofComplex ((τ : ℂ) + m) : ℍ) : ℂ) = (τ : ℂ) + m := by
    rw [ofComplex_apply_of_im_pos him]
  simp only [qs, hcoe]
  congr 1
  funext n
  have e : cexp (2 * π * Complex.I * n * ((τ : ℂ) + m)) = cexp (2 * π * Complex.I * n * τ) := by
    rw [show 2 * π * Complex.I * n * ((τ : ℂ) + m) = 2 * π * Complex.I * n * τ + ((n * m : ℤ) : ℂ) * (2 * π * Complex.I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [e]

theorem slz_levelOne (k : ℕ) (a : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ) (h : a₀ * d₀ = 1) :
    slz k !![((1 : ℕ) : ℤ) * a₀, b₀; ((1 : ℕ) : ℤ) * ((0 : ℕ) : ℤ) * c₀, ((1 : ℕ) : ℤ) * d₀] (qs a)
      = fun τ => ((d₀ : ℂ) ^ k)⁻¹ * qs a τ := by
  funext τ
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e : (((((1 : ℕ) : ℤ) * 1 : ℤ) : ℂ) * (τ : ℂ) + ((b₀ : ℤ) : ℂ)) / (((((1 : ℕ) : ℤ) * ((0 : ℕ) : ℤ) * c₀ : ℤ) : ℂ) * (τ : ℂ) + ((((1 : ℕ) : ℤ) * 1 : ℤ) : ℂ))
        = (τ : ℂ) + ((b₀ : ℤ) : ℂ) := by push_cast; ring
    simp only [slz, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.det_fin_two_of, e, qs_add_int]
    push_cast
    try simp
  · have e : (((((1 : ℕ) : ℤ) * (-1) : ℤ) : ℂ) * (τ : ℂ) + ((b₀ : ℤ) : ℂ)) / (((((1 : ℕ) : ℤ) * ((0 : ℕ) : ℤ) * c₀ : ℤ) : ℂ) * (τ : ℂ) + ((((1 : ℕ) : ℤ) * (-1) : ℤ) : ℂ))
        = (τ : ℂ) + ((-b₀ : ℤ) : ℂ) := by push_cast; ring
    simp only [slz, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.det_fin_two_of, e, qs_add_int]
    push_cast
    try simp

end GlobalTheory.EisM.AtkinLehnerForm


open GlobalTheory.EisM.AtkinLehnerForm in
theorem GlobalTheory.EisM.atkinLehner_MF : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → MF k (N * l) (ch χ) a → ∃ a' : ℕ → ℂ, MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) := by
  intro k N l χ a a₀ b₀ c₀ d₀ h hk hN ha
  have hinv := _root_.GlobalTheory.EisM.inv_slz_atkinLehner k N l χ (qs a) a₀ b₀ c₀ d₀ h hk hN ha.2
  suffices hex : ∃ a' : ℕ → ℂ, PolyB a' ∧ qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) by
    obtain ⟨a', h1, h2⟩ := hex
    exact ⟨a', ⟨h1, h2 ▸ hinv⟩, h2⟩
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have h' : (N : ℤ) * (a₀ * d₀) = 1 := by linear_combination h
    have hN1 : N = 1 := by exact_mod_cast Int.eq_one_of_mul_eq_one_right (by positivity) h'
    subst hN1
    have had : a₀ * d₀ = 1 := by simpa using h'
    rw [slz_levelOne k a a₀ b₀ c₀ d₀ had]
    obtain ⟨C, A, hC⟩ := ha.1
    refine ⟨fun n => ((d₀ : ℂ) ^ k)⁻¹ * a n, ⟨‖((d₀ : ℂ) ^ k)⁻¹‖ * C, A, fun n => ?_⟩, ?_⟩
    · rw [norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)
    · funext τ
      simp only [qs]
      rw [← tsum_mul_left]
      congr 1
      funext n
      ring
  · set δ : M2 := !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] with hδdef
    have hdet : δ.det = N := by rw [hδdef, Matrix.det_fin_two_of]; linear_combination (N : ℤ) * h
    have hδ : 0 < δ.det := by rw [hdet]; exact_mod_cast hN
    have hL : 0 < N * l := Nat.mul_pos hN hl
    haveI : NeZero (N * l) := ⟨hL.ne'⟩
    obtain ⟨f, hf⟩ := GlobalTheory.EisM.modularForm_gammaOne_of_MF k (N * l) N χ a hL (dvd_mul_right N l) ha
    have hF : slz k δ (qs a) = ⇑f ∣[(k : ℤ)] GlobalTheory.HeckeFamilyMatrices.toGL δ := by rw [hf]; exact slz_eq_slash k hk δ hδ _
    let F : ModularForm (Gamma1 (N * l)) (k : ℤ) :=
      { toFun := slz k δ (qs a)
        slash_action_eq' := by
          rintro _ ⟨A, (hA : A ∈ Gamma1 (N * l)), rfl⟩
          exact GlobalTheory.EisM.OnGammaOne.slash_inv (dvd_mul_right N l) hinv A hA
        holo' := by
          show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (slz k δ (qs a))
          rw [hF]; exact (ModularFormClass.holo f).slash _ _
        bdd_at_cusps' := by
          intro c hc
          show c.IsBoundedAt (slz k δ (qs a)) (k : ℤ)
          rw [hF, ← OnePoint.IsBoundedAt.smul_iff]
          apply ModularFormClass.bdd_at_cusps f
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
          exact GlobalTheory.HeckeFamilyMatrices.isCusp_SL2Z_toGL_smul δ hδ.ne' hc }
    refine ⟨coef F, ?_, qs_coef_of_mfc F⟩
    have hb := ModularFormClass.qExpansion_isBigO (Int.natCast_nonneg k) F
    simp only [strictWidthInfty_Gamma1, zpow_natCast] at hb
    exact polyB_of_isBigO hb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BadLabelTupleWeightLeBound
section
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem conv_dirac_sub_sum {G κ : Type} [Group G] [Fintype G] (s : Finset κ) (a : κ → G → ℂ) (b : G → ℂ) (x : G) :
    conv (dirac - ∑ i ∈ s, a i) b x = b x - ∑ i ∈ s, conv (a i) b x := by
  unfold conv dirac
  simp only [Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  rw [Finset.sum_eq_single (1 : G)]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

theorem sum_goodSet_le_one (g : ℕ) [Fact g.Prime] (N m : ℕ) (ι : Type) [Fintype ι] (ch : ι → Fin m → (ZMod g)ˣ) :
    ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ ≤ 1 := by
  have h1 : ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ ≤
      ∑ F ∈ Fintype.piFinset fun _ : ι => sqSet g N, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun F _ _ => ?_
    exact Finset.prod_nonneg fun v _ => inv_nonneg.2 (Nat.cast_nonneg _)
  refine h1.trans ?_
  rw [← Finset.prod_univ_sum (fun _ : ι => sqSet g N) fun _ f => ((torusCard g f : ℝ))⁻¹]
  have h2 := (_root_.GlobalTheory.BadShare.divisor_bound g).1 N
  have h3 := mass_nonneg (g := g) N fun _ => True
  simp only [mass, Finset.filter_true] at h2 h3
  exact Finset.prod_le_one₀ (fun _ _ => h3) fun _ _ => h2

theorem badWeight_le : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (m q d : ℕ) (ι : Type) [Fintype ι] (L : ι → Lev g N) (τ : ι → (ZMod g)[X] → GG g N → ℂ) (ch : ι → Fin m → (ZMod g)ˣ), 100000 ≤ N → PrimeOK g q d → (∀ v, IsSeries (τ v)) → ∃ w : ℝ, conv (dirac - eGood τ ch) (tens fun v => (L v).e) 1 = (w : ℂ) * (tens fun v => (L v).e) 1 ∧ w ≤ badBound g (Fintype.card ι) m N ((min q d : ℕ) : ℝ) := by
  intro g _ N m q d ι _ L τ ch hN hP hτ
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hg⟩ := hP
  have hS := _root_.GlobalTheory.BadShare.goodSet_weight_ge g N m q d ι ch hN hg ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hS1 := sum_goodSet_le_one g N m ι ch
  have hS0 : 0 ≤ ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ :=
    Finset.sum_nonneg fun F _ => Finset.prod_nonneg fun v _ => inv_nonneg.2 (Nat.cast_nonneg _)
  choose! w hw1 hw2 using fun v => _root_.GlobalTheory.BadShare.series_weight_lower_bound g N (L v) (τ v) (hτ v)
  have hmem : ∀ F ∈ goodSet g N ch, ∀ v, F v ∈ sqSet g N := fun F hF =>
    (good_iff.1 (mem_goodSet_iff_good.1 hF)).1
  refine ⟨1 - ∑ F ∈ goodSet g N ch, ∏ v, w v (F v), ?_, ?_⟩
  · unfold eGood
    rw [conv_dirac_sub_sum]
    push_cast
    rw [sub_mul, one_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun F hF => ?_
    rw [(tens_calculus ι (GG g N) (GG g N)).1]
    unfold tens
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => hw1 v (F v) (hmem F hF v)
  · have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (Fact.out : g.Prime).one_le
    have hg0 : (0 : ℝ) < g := by linarith
    have hinv : 1 / (g : ℝ) ≤ 1 := by rw [div_le_one hg0]; exact hg1
    have hinv0 : 0 ≤ 1 / (g : ℝ) := by positivity
    have hA : (1 - 1 / (g : ℝ)) ^ Fintype.card ι * ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ ≤
        ∑ F ∈ goodSet g N ch, ∏ v, w v (F v) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun F hF => ?_
      rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀ (fun v _ => ?_) fun v _ => hw2 v (F v) (hmem F hF v)
      exact mul_nonneg (by linarith) (inv_nonneg.2 (Nat.cast_nonneg _))
    have hB : 1 - (Fintype.card ι : ℝ) / g ≤ (1 - 1 / (g : ℝ)) ^ Fintype.card ι := by
      have := one_add_mul_le_pow (a := -(1 / (g : ℝ))) (by linarith) (Fintype.card ι)
      rw [← sub_eq_add_neg] at this
      refine le_trans (le_of_eq ?_) this
      ring
    have hC : 0 ≤ (Fintype.card ι : ℝ) / g := by positivity
    have hD := mul_le_mul_of_nonneg_right hB hS0
    have hE := mul_le_mul_of_nonneg_left hS1 hC
    nlinarith

end GlobalTheory.BadShare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupKummerCoboundaryOfNorms
section
open GlobalTheory.NeedB Polynomial

theorem GlobalTheory.cup_kummer_coboundary_of_norms : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  (∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 → ∃ x : L, Algebra.norm K x = c) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧ ∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix hnorm a b α β ha hb hα hβ
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨w, hwc, hw⟩ := GlobalTheory.T.kummer_carry_cocycle_coboundary_of_norms K Ω N ζ hN hζ hfix hnorm a b α β ha hb hα hβ
  obtain ⟨v, hvc, hv⟩ := GlobalTheory.T.kummer_carry_coboundary_twist_cochain K Ω N ζ hN hζ hfix a b α β ha hb hα hβ w hwc hw
  exact _root_.GlobalTheory.Hilbert90CupCoboundary.zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle K Ω N ζ hN hζ hfix (fun g h => kum ζ α g * kum ζ β h) v hvc hv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeFunctionIsModularFormCoeffSeq
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisForm

lemma sum_shift (L : ℕ) [NeZero L] (φ : ZMod L → ℂ) (u e : ZMod L) (he : IsUnit e) :
    ∑ r ∈ Finset.range L, φ (u + (r : ZMod L) * e) = ∑ y, φ y := by
  rw [Finset.sum_range (fun r => φ (u + (r : ZMod L) * e))]
  refine Fintype.sum_bijective (fun i : Fin L => u + ((i : ℕ) : ZMod L) * e) ?_ _ _ (fun _ => rfl)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp [ZMod.card]⟩
  intro i i' h
  simp only [add_right_inj] at h
  have h' := he.mul_right_cancel h
  rw [ZMod.natCast_eq_natCast_iff'] at h'
  ext
  rwa [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt i'.2] at h'

lemma hat_zero (L : ℕ) [NeZero L] (φ : ZMod L → ℂ) : hat φ 0 = ∑ y, φ y := by
  have := sum_shift L φ 0 1 isUnit_one
  simp only [zero_add, mul_one] at this
  rw [← this]; simp [hat]

lemma bdd_of_periodic (L₂ : ℕ) (hL : 0 < L₂) (b : ℤ → ℂ) (hb : ∀ x, b (x + L₂) = b x) :
    ∃ C : ℝ, ∀ x, ‖b x‖ ≤ C := by
  have hp : Function.Periodic b (L₂ : ℤ) := hb
  have hpz : ∀ y n : ℤ, b (y + n * L₂) = b y := fun y n => by simpa using hp.int_mul n y
  refine ⟨∑ i ∈ Finset.range L₂, ‖b i‖, fun x => ?_⟩
  have h1 := Int.emod_nonneg x (by omega : (L₂ : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos x (by omega : (0 : ℤ) < L₂)
  have e : b x = b (((x % L₂).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg h1, ← hpz (x % L₂) (x / L₂)]
    congr 1
    rw [Int.emod_def]; ring
  rw [e]
  exact Finset.single_le_sum (f := fun i : ℕ => ‖b i‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_range.mpr (by omega))

lemma latF_trans (L₁ L₂ : ℕ) (hL₁ : 0 < L₁) (b χ₁ χ₂ : ℤ → ℂ) (φ : ZMod L₁ → ℂ)
    (hb : ∀ x, b (x + L₂) = b x)
    (hχ : ∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ y, φ y = χ₁ d * φ (y * d)) ∧ ∀ x, b (x * d) = χ₂ d * b x)
    (a b' k d : ℤ) (hdet : a * d - b' * (L₁ * L₂ * k) = 1) (x : ℤ × ℤ) :
    latF L₁ b φ x = χ₁ d * χ₂ d * latF L₁ b φ (x.1 * a + x.2 * (L₁ * L₂ * k), x.1 * b' + x.2 * d) := by
  have hp : Function.Periodic b (L₂ : ℤ) := hb
  have hpz : ∀ y n : ℤ, b (y + n * L₂) = b y := fun y n => by simpa using hp.int_mul n y
  have hL : (L₁ : ℤ) ≠ 0 := by exact_mod_cast hL₁.ne'
  have hcop : IsCoprime d ((L₁ * L₂ : ℕ) : ℤ) := ⟨a, -(b' * k), by push_cast; linear_combination hdet⟩
  obtain ⟨hφ, hbχ⟩ := hχ d hcop
  have hcopa : IsCoprime (L₁ : ℤ) a := ⟨-(b' * L₂ * k), d, by linear_combination hdet⟩
  unfold latF
  by_cases h : (L₁ : ℤ) ∣ x.1
  · obtain ⟨m, hm⟩ := h
    have h2 : (L₁ : ℤ) ∣ x.1 * a + x.2 * (L₁ * L₂ * k) := ⟨m * a + x.2 * L₂ * k, by rw [hm]; ring⟩
    rw [if_pos ⟨m, hm⟩, if_pos h2]
    have e1 : x.1 / L₁ = m := by rw [hm, Int.mul_ediv_cancel_left _ hL]
    have e2 : (x.1 * a + x.2 * (L₁ * L₂ * k)) / L₁ = m * a + (x.2 * k) * L₂ := by
      rw [show x.1 * a + x.2 * (L₁ * L₂ * k) = L₁ * (m * a + (x.2 * k) * L₂) by rw [hm]; ring,
        Int.mul_ediv_cancel_left _ hL]
    have e3 : (((x.1 * b' + x.2 * d : ℤ)) : ZMod L₁) = (x.2 : ZMod L₁) * (d : ZMod L₁) := by
      rw [hm]; push_cast; rw [ZMod.natCast_self]; ring
    rw [e1, e2, e3, hpz]
    have e4 : b m = χ₂ d * b (m * a) := by
      rw [← hbχ, ← hpz m (m * b' * L₁ * k)]
      congr 1
      linear_combination (-m) * hdet
    rw [e4, hφ (x.2 : ZMod L₁)]; ring
  · have h2 : ¬ (L₁ : ℤ) ∣ x.1 * a + x.2 * (L₁ * L₂ * k) := by
      intro h2; apply h
      have h3 : (L₁ : ℤ) ∣ x.2 * (L₁ * L₂ * k) := ⟨x.2 * L₂ * k, by ring⟩
      exact hcopa.dvd_of_dvd_mul_right ((dvd_add_left h3).mp h2)
    rw [if_neg h, if_neg h2, mul_zero]

lemma latF_kills (L₁ L₂ : ℕ) (hL₁ : 0 < L₁) (b : ℤ → ℂ) (φ : ZMod L₁ → ℂ)
    (hb : ∀ x, b (x + L₂) = b x) (hhat : hat φ 0 = 0) (k d : ℤ) (hd : IsUnit (d : ZMod L₁)) :
    Kills L₁ (L₁ * L₂ * k, d) (latF L₁ b φ) := by
  haveI : NeZero L₁ := ⟨hL₁.ne'⟩
  have hp : Function.Periodic b (L₂ : ℤ) := hb
  have hpz : ∀ y n : ℤ, b (y + n * L₂) = b y := fun y n => by simpa using hp.int_mul n y
  have hL : (L₁ : ℤ) ≠ 0 := by exact_mod_cast hL₁.ne'
  rw [hat_zero] at hhat
  intro x
  by_cases h : (L₁ : ℤ) ∣ x.1
  · obtain ⟨m, hm⟩ := h
    calc ∑ r ∈ Finset.range L₁, latF L₁ b φ (x - (r : ℤ) • ((L₁ : ℤ) * L₂ * k, d))
        = ∑ r ∈ Finset.range L₁, b m * φ ((x.2 : ZMod L₁) + (r : ZMod L₁) * (-(d : ZMod L₁))) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [latF, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]
          rw [if_pos ⟨m - r * L₂ * k, by rw [hm]; ring⟩,
            show x.1 - (r : ℤ) * (L₁ * L₂ * k) = L₁ * (m + (-(r * k)) * L₂) by rw [hm]; ring,
            Int.mul_ediv_cancel_left _ hL, hpz]
          congr 2; push_cast; ring
      _ = 0 := by rw [← Finset.mul_sum, sum_shift L₁ φ _ _ hd.neg, hhat, mul_zero]
  · refine Finset.sum_eq_zero fun r _ => ?_
    simp only [latF, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]
    rw [if_neg]
    intro h2; apply h
    have h3 : (L₁ : ℤ) ∣ (r : ℤ) * (L₁ * L₂ * k) := ⟨r * L₂ * k, by ring⟩
    simpa using dvd_add h2 h3

end GlobalTheory.EisForm

namespace GlobalTheory.EisForm

theorem eis_latF_mf : ∀ (j L₁ L₂ : ℕ) (b χ₁ χ₂ : ℤ → ℂ) (φ : ZMod L₁ → ℂ), 1 ≤ j → 0 < L₁ → 0 < L₂ → hat φ 0 = 0 →
    (∀ x, b (x + L₂) = b x) →
    (∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ y, φ y = χ₁ d * φ (y * d)) ∧ ∀ x, b (x * d) = χ₂ d * b x) →
    χ₁ (-1) * χ₂ (-1) = (-1) ^ j →
    ∃ c : ℂ, MF j (L₁ * L₂) (fun d => χ₁ d * χ₂ d) (eis j c (hat φ) b) ∧
      ∀ τ : ℍ, lat j 0 L₁ (0, 1) (latF L₁ b φ) τ = 2 * (-2 * π * Complex.I / L₁) ^ j / (j - 1).factorial * qs (eis j c (hat φ) b) τ := by
  intro j L₁ L₂ b χ₁ χ₂ φ hj hL₁ hL₂ hhat hb hχ hpar
  haveI : NeZero L₁ := ⟨hL₁.ne'⟩
  obtain ⟨Cb, hCb⟩ := bdd_of_periodic L₂ hL₂ b hb
  have hparity : ∀ x y : ℤ, b (-x) * φ (-(y : ZMod L₁)) = (-1) ^ j * (b x * φ y) := by
    intro x y
    obtain ⟨hφ, hbb⟩ := hχ (-1) ⟨-1, 0, by ring⟩
    have h1 := hφ (-(y : ZMod L₁))
    have h2 := hbb x
    rw [show -(y : ZMod L₁) * ((-1 : ℤ) : ZMod L₁) = y by push_cast; ring] at h1
    rw [mul_neg_one] at h2
    rw [h1, h2, ← hpar]; ring
  obtain ⟨c, hP, hq⟩ := _root_.GlobalTheory.LatQ.lat_qexp j L₁ b φ hj hL₁ ⟨Cb, hCb⟩ hhat hparity
  refine ⟨c, ⟨hP, ?_⟩, hq⟩
  set K : ℂ := 2 * (-2 * π * Complex.I / L₁) ^ j / (j - 1).factorial with hKdef
  have hK : K ≠ 0 := by
    have hL : (L₁ : ℂ) ≠ 0 := by exact_mod_cast hL₁.ne'
    simp [hKdef, Real.pi_ne_zero, Complex.I_ne_zero, hL, Nat.factorial_ne_zero]
  set Φ := latF L₁ b φ with hΦ
  have hq' : ∀ τ, qs (eis j c (hat φ) b) τ = K⁻¹ * lat j 0 L₁ (0, 1) Φ τ := fun τ => by
    rw [hq τ, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]
  have hΦb : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C := by
    have hC0 : 0 ≤ Cb := le_trans (norm_nonneg _) (hCb 0)
    refine ⟨Cb * ∑ y, ‖φ y‖, fun x => ?_⟩
    simp only [hΦ, latF]
    split_ifs
    · rw [norm_mul]
      exact mul_le_mul (hCb _) (Finset.single_le_sum (f := fun y => ‖φ y‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ _)) (norm_nonneg _) hC0
    · simpa using mul_nonneg hC0 (Finset.sum_nonneg fun y _ => norm_nonneg (φ y))
  intro γ hc τ
  obtain ⟨k, hk⟩ := hc
  push_cast at hk
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * ((L₁ : ℤ) * L₂ * k) = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    rw [← hk]; exact this
  have hunit : IsUnit ((γ 1 1 : ℤ) : ZMod L₁) := by
    refine isUnit_iff_exists_inv.mpr ⟨((γ 0 0 : ℤ) : ZMod L₁), ?_⟩
    have := congrArg (fun z : ℤ => (z : ZMod L₁)) hdet
    push_cast at this
    rw [ZMod.natCast_self] at this
    linear_combination this
  set χd := χ₁ (γ 1 1) * χ₂ (γ 1 1) with hχd
  have htr : ∀ x : ℤ × ℤ, (fun y => χd * Φ y) (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1) = Φ x := by
    intro x
    have := latF_trans L₁ L₂ hL₁ b χ₁ χ₂ φ hb hχ (γ 0 0) (γ 0 1) k (γ 1 1) hdet x
    rw [← hk] at this
    exact this.symm
  have hlin : ∀ w, lat j 0 L₁ w (fun y => χd * Φ y) τ = χd * lat j 0 L₁ w Φ τ := by
    intro w
    unfold lat
    rw [← tsum_mul_left]
    congr 1; ext x; ring
  have hw : ((0 : ℤ) * γ 0 0 + 1 * γ 1 0, (0 : ℤ) * γ 0 1 + 1 * γ 1 1) = ((L₁ : ℤ) * L₂ * k, γ 1 1) := by
    simp [hk]
  have hk1 : Kills L₁ ((L₁ : ℤ) * L₂ * k, γ 1 1) Φ := latF_kills L₁ L₂ hL₁ b φ hb hhat k (γ 1 1) hunit
  have hk0 : Kills L₁ (0, 1) Φ := by
    simpa using latF_kills L₁ L₂ hL₁ b φ hb hhat 0 1 (by simp)
  rw [hq', hq', GlobalTheory.T.regularizedEisensteinLatticeSum_slTwo_smul j L₁ (0, 1) Φ (fun y => χd * Φ y) γ τ htr, hlin]
  simp only [Prod.fst, Prod.snd]
  rw [hw, _root_.GlobalTheory.EisM.lat_indep j L₁ _ (0, 1) Φ τ hj hL₁ hΦb hk1 hk0]
  ring

end GlobalTheory.EisForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsColumnChainNonempty
section
open Formalism.BasicNotions NumberField

namespace GlobalTheory

theorem unitChain_num_sub_half (R : Ranks) (q : ℚ) (hq : ∃ z : ℤ, q = z) (j : ℕ) :
    (((q - (R.N j : ℚ) / 2).num : ℤ) : ℚ) = q - (R.N j : ℚ) / 2 := by
  obtain ⟨z, rfl⟩ := hq
  have hN : Even (R.N j) := by
    unfold Ranks.N
    exact R.k_even.add ((R.t_odd.add_one).mul_left j)
  obtain ⟨a, ha⟩ := hN
  have h : (z : ℚ) - (R.N j : ℚ) / 2 = ((z - a : ℤ) : ℚ) := by
    rw [ha]; push_cast; ring
  rw [h, Rat.num_intCast]

def unitColumnChain (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) :
    ColumnChain R ι hc where
  cls _ := Unit
  stab _ _ := PUnit
  DGam := 1
  DGam_pos := Nat.one_pos
  dvd_DGam _ _ _ := by simp
  Y _ := Unit
  de _ _ _ := 1
  de_ne _ _ _ := one_ne_zero
  rhoDet _ _ := 1
  rhoDet' _ _ := 1
  rho_norm _ _ _ := norm_one
  rho'_norm _ _ _ := norm_one
  unf _ _ _ := LinearMap.id
  sSharp i τ := if h : i < R.m then (sExp' R ((hc τ).e ⟨i, h⟩) (i + 1)).num else 0
  sSharp_eq i h τ := by
    rw [dite_eq_left h]
    exact unitChain_num_sub_half R _ ((hc τ).e_int _) _
  sDiv i τ := if h : i < R.m then (sExp R ((hc τ).e ⟨i, h⟩) (i + 1)).num else 0
  sDiv_eq i h τ := by
    rw [dite_eq_left h]
    exact unitChain_num_sub_half R _ ((hc τ).e_int _) _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaSubOneMemSpanGaloisDifferencesStatement
section
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_sub_one_mem_span_galois_differences : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ j : ℕ, 1 ≤ j → ∀ g ∈ Hinf T, g r ≠ r →
  T.ζ j - 1 ∈ Submodule.span (FixI (Hfix T r)) {y : Ω | ∃ x ∈ FixI (Hfix T r), y = g x - x} := by
  first | exact @GlobalTheory.KumIdeal.zeta_sub_one_mem_span | exact GlobalTheory.KumIdeal.zeta_sub_one_mem_span | (intros; apply GlobalTheory.KumIdeal.zeta_sub_one_mem_span <;> assumption)
end

