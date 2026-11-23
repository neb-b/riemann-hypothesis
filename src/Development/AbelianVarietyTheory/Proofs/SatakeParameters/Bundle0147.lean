module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FourthPowerTheta
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementH
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteSkewHermitianValuationMaxQuotSum
section
open Matrix

namespace GlobalTheory.Hk3.GramSep

theorem gam_quot_finite : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K) →
  ∀ (r : ℕ) (e : Fin r → ℕ), Finite (↥(GlobalTheory.Hk3.GramSep.gam σ ϖ e) ⧸
    (GlobalTheory.Hk3.GramSep.gam0 σ ϖ e).addSubgroupOf (GlobalTheory.Hk3.GramSep.gam σ ϖ e)) := by
  intro L _ _ ϖ σ hϖ hR r e
  classical
  have hle1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ]
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) ≤ 1)
  set K : ℕ := ∑ k, ∑ j, (e k + e j) with hK
  obtain ⟨R, -, hRc⟩ := hR K
  have hKge : ∀ k j, e k + e j ≤ K := by
    intro k j
    have h1 : e k + e j ≤ ∑ j', (e k + e j') :=
      Finset.single_le_sum (f := fun j' => e k + e j') (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : ∑ j', (e k + e j') ≤ ∑ k', ∑ j', (e k' + e j') :=
      Finset.single_le_sum (f := fun k' => ∑ j', (e k' + e j')) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    exact h1.trans h2
  have hint : ∀ Γ : ↥(gam σ ϖ e), ∀ k j, (Γ : Matrix (Fin r) (Fin r) L) k j ∈ Formalism.UG.intL L := by
    intro Γ k j
    show Valued.v ((Γ : Matrix (Fin r) (Fin r) L) k j) ≤ 1
    exact (Γ.2.2 k j).trans (pow_le_one' hle1 _)
  have hch : ∀ Γ : ↥(gam σ ϖ e), ∀ k j, ∃ x ∈ R, Valued.v ((Γ : Matrix (Fin r) (Fin r) L) k j - x) ≤ Valued.v ϖ ^ K :=
    fun Γ k j => hRc _ (hint Γ k j)
  let g : ↥(gam σ ϖ e) → (Fin r → Fin r → ↥R) := fun Γ k j => ⟨(hch Γ k j).choose, (hch Γ k j).choose_spec.1⟩
  have hg : ∀ (Γ : ↥(gam σ ϖ e)) k j, Valued.v ((Γ : Matrix (Fin r) (Fin r) L) k j - (g Γ k j : L)) ≤ Valued.v ϖ ^ K :=
    fun Γ k j => (hch Γ k j).choose_spec.2
  let h : (↥(gam σ ϖ e) ⧸ (gam0 σ ϖ e).addSubgroupOf (gam σ ϖ e)) → (Fin r → Fin r → ↥R) :=
    fun q => g (Quotient.out q)
  have hinj : Function.Injective h := by
    intro q1 q2 hq
    rw [← QuotientAddGroup.out_eq' q1, ← QuotientAddGroup.out_eq' q2, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    set a := Quotient.out q1
    set b := Quotient.out q2
    have hab : g a = g b := hq
    have hmem : ((-a + b : ↥(gam σ ϖ e)) : Matrix (Fin r) (Fin r) L) ∈ gam σ ϖ e := (-a + b).2
    refine ⟨hmem.1, fun k j => ?_⟩
    have e1 : ((-a + b : ↥(gam σ ϖ e)) : Matrix (Fin r) (Fin r) L) k j
        = ((b : Matrix (Fin r) (Fin r) L) k j - (g b k j : L)) - ((a : Matrix (Fin r) (Fin r) L) k j - (g a k j : L)) := by
      rw [hab]; simp; ring
    rw [e1]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · exact (hg b k j).trans (pow_le_pow_right_of_le_one' hle1 (hKge k j))
    · exact (hg a k j).trans (pow_le_pow_right_of_le_one' hle1 (hKge k j))
  exact Finite.of_injective h hinj

end GlobalTheory.Hk3.GramSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodFormsBaseLevelIffGoodProjection
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem goodForms_baseLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ i (x : (R.HW i (sg0 D A)).H), (R.HW i _).e x ∈ R.Wat i (sg0 D A) (R.levL F false (sg0 D A)) ↔ eH R i x = x ∧ ∀ p : F.P0, R.gW i (sg0 D A) p x = sg0 D A ((F.ψ0⁻¹ p : D.what₂.LLˣ) : D.what₂.LL) • x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC _ i x
  have hW := hC.models.HW
  have hg := hC.models.gW
  have hl := GlobalTheory.GalLift.Transl.lifts R i hC.lev
  have hx : (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := (hW i _).2.1.le (LinearMap.mem_range_self _ x)
  have hm := (GlobalTheory.MultMem.mem_mult_iff ..).1 hx
  have hT := GlobalTheory.GalLift.Transl.hasType R i hW (sg0 D A) x
  have hsum : (∑ g, RealDat.eC (A := A) (sg0 D A) g • R.gW i (sg0 D A) g x) = eH R i x := by
    simp [eH, LinearMap.sum_apply]
  have hproj : eH R i x = x ↔ ∀ v, R.eWf i (sg0 D A) ((R.HW i (sg0 D A)).e x v) = (R.HW i (sg0 D A)).e x v := by
    constructor
    · intro h v
      rw [GlobalTheory.GalLift.Transl.proj R i hg, hsum, h]
    · intro h
      apply (hW i _).1
      ext v : 1
      rw [← h v, GlobalTheory.GalLift.Transl.proj R i hg, hsum]
  unfold RealDat.Wat
  rw [mem_goodPart, GlobalTheory.MultMem.mem_mult_iff, hproj]
  have hmem : ∀ p : F.P0, R.eG p ∈ (R.levL F false (sg0 D A)).H := fun p => by
    show R.eG.symm (R.eG p) ∈ F.P0
    rw [MulEquiv.symm_apply_apply]; exact p.2
  have hchi : ∀ p : F.P0, (((R.levL F false (sg0 D A)).chi ⟨R.eG p, hmem p⟩ : ℂˣ) : ℂ) =
      sg0 D A ((F.ψ0⁻¹ p : D.what₂.LLˣ) : D.what₂.LL) := fun p => by
    show sg0 D A ((F.ψ0⁻¹ ⟨R.eG.symm (R.eG p), _⟩ : D.what₂.LLˣ) : D.what₂.LL) = _
    congr 4
    exact R.eG.symm_apply_apply _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun p => ?_⟩
    apply (hW i _).1
    rw [hg, map_smul]
    ext v h
    have h3 := GlobalTheory.LevelRows.levelType_eigenfunction_of_liftable_element (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv)
      (P := R.levL F false (sg0 D A)) (F := (R.HW i (sg0 D A)).e x v) (fun κ hκ h => h1.lev v κ hκ h) ⟨R.eG p, hmem p⟩ (hl _)
    exact (congrFun h3 h).trans (congrArg (· * (R.HW i (sg0 D A)).e x v h) (hchi p))
  · rintro ⟨h2, h⟩
    refine ⟨⟨hm.aut, hm.cusp, fun v => ?_, hm.equiv, hm.cont⟩, h2⟩
    have hP : IsPLevel (Wc D i) (R.βW i) (R.datWp i R.triv) (R.levL F false (sg0 D A)) ((R.HW i (sg0 D A)).e x v) := by
      refine ⟨hT v, fun p => ?_⟩
      have hp : R.eG.symm p.1 ∈ F.P0 := p.2
      have h4 := congrArg (fun z => (R.HW i (sg0 D A)).e z v) (h ⟨R.eG.symm p.1, hp⟩)
      simp only [hg _ _ _ x, map_smul] at h4
      have h5 : R.eG (R.eG.symm p.1) = p.1 := R.eG.apply_symm_apply p.1
      rw [h5] at h4
      exact h4
    exact fun κ hκ y => hP.hasType κ hκ y

end GlobalTheory.Hk3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodModelTwoScaleOne
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.ThLoc

theorem goodModelTwo_scaleOne : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ →
    ∀ ι : ℂ ≃+* ℂ_[2], ∃ W : WeierstrassCurve ℂ_[2], Unif 2 (cmL a₀ b₀ D.host.d ha hd lam hlam) ι W ∧ IntCurve W ∧
      ‖W.a₁‖ = 1 := by
  intro hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hok hlat ι
  set L := cmL a₀ b₀ D.host.d ha hd lam hlam with hLdef
  obtain ⟨hsq, -, hcm⟩ := LocJets.data ha hd lam hlam hok
  have h8 : D.host.d % 8 = 7 := by have := D.host.hyp.2.2.2.1; omega
  obtain ⟨c, hc, W', ⟨e2, e3⟩, ⟨h1, h2, h3, h4, h6, hΔ⟩, ha1⟩ := hIn.modelTwo D.host.d L hsq h8 hcm ι
  have hL1 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have hL' : (L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by rw [← hlat]; rfl
    obtain ⟨f2, f3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L hL'
    rw [← f2, ← f3]
    exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  have hh := Formalism.L2.Th1.F.homogeneity L c hc
  have s2 : (Formalism.L2.Th1.F.scalePair L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ := hh.2.2.2.2.2.2.2.2.2.1
  have s3 : (Formalism.L2.Th1.F.scalePair L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃ := hh.2.2.2.2.2.2.2.2.2.2
  have g2W : W'.c₄ / 12 = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ := e2
  have g3W : W'.c₆ / 216 = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ := e3
  set u : ℂ_[2] := ι c with hu
  have hu0 : u ≠ 0 := by simpa [hu] using hc

  have hW'Δ : W'.Δ = (u ^ 12)⁻¹ := by
    have hrel := W'.c_relation
    have hc4 : W'.c₄ = 12 * ((u ^ 4)⁻¹ * ι L.g₂) := by
      rw [← map_pow, ← map_inv₀, ← map_mul, ← s2, ← g2W]; ring
    have hc6 : W'.c₆ = 216 * ((u ^ 6)⁻¹ * ι L.g₃) := by
      rw [← map_pow, ← map_inv₀, ← map_mul, ← s3, ← g3W]; ring
    have hι1 : ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2 = 1 := by
      rw [← map_pow, ← map_pow, ← map_ofNat ι 27, ← map_mul, ← map_sub, hL1, map_one]
    rw [hc4, hc6] at hrel
    have h1728 : (1728 : ℂ_[2]) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h1728
    rw [hrel]
    field_simp
    linear_combination (1728 : ℂ_[2]) * hι1
  have hun : ‖u‖ = 1 := by
    rw [hW'Δ, norm_inv, norm_pow] at hΔ
    have h12 : ‖u‖ ^ 12 = 1 := by
      have hpos : 0 < ‖u‖ ^ 12 := pow_pos (norm_pos_iff.2 hu0) _
      field_simp at hΔ; linarith
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h12
  let C : WeierstrassCurve.VariableChange ℂ_[2] := ⟨(Units.mk0 u hu0)⁻¹, 0, 0, 0⟩
  have hCu : ((C.u⁻¹ : ℂ_[2]ˣ) : ℂ_[2]) = u := by simp [C]
  refine ⟨C • W', ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (C • W').c₄ / 12 = ι L.g₂
    rw [WeierstrassCurve.variableChange_c₄, hCu, mul_div_assoc, g2W, s2, map_mul, map_inv₀, map_pow, ← hu]
    field_simp
  · show (C • W').c₆ / 216 = ι L.g₃
    rw [WeierstrassCurve.variableChange_c₆, hCu, mul_div_assoc, g3W, s3, map_mul, map_inv₀, map_pow, ← hu]
    field_simp
  · rw [WeierstrassCurve.variableChange_a₁, hCu]
    simp only [C, mul_zero, add_zero, norm_mul, hun, one_mul]; exact h1
  · rw [WeierstrassCurve.variableChange_a₂, hCu]
    simp only [C, zero_mul, mul_zero, sub_zero, add_zero, zero_pow two_ne_zero, norm_mul, norm_pow, hun, one_pow,
      one_mul]; exact h2
  · rw [WeierstrassCurve.variableChange_a₃, hCu]
    simp only [C, zero_mul, mul_zero, add_zero, norm_mul, norm_pow, hun, one_pow, one_mul]; exact h3
  · rw [WeierstrassCurve.variableChange_a₄, hCu]
    simp only [C, zero_mul, mul_zero, sub_zero, add_zero, zero_add, zero_pow two_ne_zero, norm_mul, norm_pow, hun,
      one_pow, one_mul]; exact h4
  · rw [WeierstrassCurve.variableChange_a₆, hCu]
    simp only [C, zero_mul, mul_zero, sub_zero, add_zero, zero_add, zero_pow two_ne_zero, zero_pow three_ne_zero,
      norm_mul, norm_pow, hun, one_pow, one_mul]; exact h6
  · rw [WeierstrassCurve.variableChange_Δ, hCu, norm_mul, norm_pow, hun, one_pow, one_mul]; exact hΔ
  · rw [WeierstrassCurve.variableChange_a₁, hCu]
    simp only [C, mul_zero, add_zero, norm_mul, hun, one_mul]; exact ha1

end GlobalTheory.ThLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassEqOfSigmaHermitianFormBounds
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.GramConv

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem hform_add_left' (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (u u' w : Fin n → L) :
    Formalism.UG.hform σ J (u + u') w = Formalism.UG.hform σ J u w + Formalism.UG.hform σ J u' w := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_add_right' (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (u w w' : Fin n → L) :
    Formalism.UG.hform σ J u (w + w') = Formalism.UG.hform σ J u w + Formalism.UG.hform σ J u w' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right' (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (c : L) (u w : Fin n → L) :
    Formalism.UG.hform σ J u (c • w) = c * Formalism.UG.hform σ J u w := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_smul_left' (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (c : L)
    (u w : Fin n → L) : Formalism.UG.hform σ J (σ c • u) w = c * Formalism.UG.hform σ J u w := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, hσ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_sub_mat (σ : L →+* L) {n : ℕ} (J J' : Matrix (Fin n) (Fin n) L) (u w : Fin n → L) :
    Formalism.UG.hform σ (J - J') u w = Formalism.UG.hform σ J u w - Formalism.UG.hform σ J' u w := by
  simp only [Formalism.UG.hform, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_eq_dot (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (u w : Fin n → L) :
    Formalism.UG.hform σ J u w = (fun i => σ (u i)) ⬝ᵥ (J *ᵥ w) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec_mulVec (σ : L →+* L) {n r : ℕ} (J : Matrix (Fin n) (Fin n) L) (B : Matrix (Fin n) (Fin r) L)
    (α β : Fin r → L) :
    Formalism.UG.hform σ J (B *ᵥ α) (B *ᵥ β) = Formalism.UG.hform σ (Formalism.UG.cT σ B * J * B) α β := by
  have hs : (fun i => σ ((B *ᵥ α) i)) = (fun k => σ (α k)) ᵥ* Formalism.UG.cT σ B := by
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Formalism.UG.cT, map_sum, map_mul, Matrix.transpose_apply,
      Matrix.map_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hform_eq_dot, hform_eq_dot, hs, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem mulVec_int' {a b : ℕ} {A : Matrix (Fin a) (Fin b) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) {w : Fin b → L}
    (hw : ∀ j, w j ∈ Formalism.UG.intL L) (i : Fin a) : (A *ᵥ w) i ∈ Formalism.UG.intL L := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hw j)

theorem hform_int' (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} {J : Matrix (Fin n) (Fin n) L}
    (hJ : ∀ i j, J i j ∈ Formalism.UG.intL L) {u w : Fin n → L} (hu : ∀ i, u i ∈ Formalism.UG.intL L)
    (hw : ∀ i, w i ∈ Formalism.UG.intL L) : Formalism.UG.hform σ J u w ∈ Formalism.UG.intL L := by
  have hsu : ∀ i, σ (u i) ∈ Formalism.UG.intL L := fun i => by
    show Valued.v (σ (u i)) ≤ 1
    rw [hv]; exact hu i
  exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
    Subring.mul_mem _ (Subring.mul_mem _ (hsu i) (hJ i j)) (hw j)

theorem gramEq_of_gram_bounds : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ϖ ∈ Formalism.UG.intL L →
  ∀ (n n' r : ℕ) (JT : GL (Fin n') L) (a : GL (Fin n) L) (x y : Matrix (Fin n') (Fin n) L)
    (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
  (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
    ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔ ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) → (∀ i j, (x * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) → (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → (∀ m : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧
      ∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (m - M *ᵥ α)) i ∈ Formalism.UG.intL L) → (∀ β : Fin r → L, (∀ k, β k ∈ Formalism.UG.intL L) → (∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (M *ᵥ β)) i ∈ Formalism.UG.intL L) →
      ∀ k, Valued.v (β k) ≤ Valued.v ϖ ^ e k) →
  (∀ j k, ((Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M)) - (Formalism.UG.cT σ (x * M) * (JT : Matrix (Fin n') (Fin n') L) * (x * M))) j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.HoweG.GramEq σ JT x y := by
  intro L _ _ ϖ σ hσ hv hϖ n n' r JT a x y M e hJ hJh hiff hxa hya hM hAM hdec hbd hG
  intro m m' hm hm' c hc hxm hxm'
  have toV : ∀ t : L, t ∈ Formalism.UG.intL L → Valued.v t ≤ 1 := fun t h => h
  have ofV : ∀ t : L, Valued.v t ≤ 1 → t ∈ Formalism.UG.intL L := fun t h => h
  set A : Matrix (Fin n) (Fin n) L := (a : Matrix (Fin n) (Fin n) L) with hA
  set Ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAi
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hAAi : A * Ai = 1 := by rw [hA, hAi]; exact a.mul_inv
  have hAiA : Ai * A = 1 := by rw [hA, hAi]; exact a.inv_mul

  have key : ∀ μ : Fin n → L, (∀ i, μ i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ (c • μ)) i ∈ Formalism.UG.intL L) →
      ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧ (∀ i, (Ai *ᵥ (μ - M *ᵥ α)) i ∈ Formalism.UG.intL L) ∧
        (∀ i, (Ai *ᵥ (M *ᵥ (c • α))) i ∈ Formalism.UG.intL L) ∧ ∀ k, Valued.v (c * α k) ≤ Valued.v ϖ ^ e k := by
    intro μ hμ hxμ
    obtain ⟨α, hα, hν⟩ := hdec μ hμ
    have hcμ : ∀ i, (c • μ) i ∈ Formalism.UG.intL L := fun i => Subring.mul_mem _ hc (hμ i)
    obtain ⟨u, hu, hcu⟩ := (hiff (c • μ) hcμ).2 hxμ
    have heq : Ai *ᵥ (M *ᵥ (c • α)) = u - c • (Ai *ᵥ (μ - M *ᵥ α)) := by
      have h1 : M *ᵥ (c • α) = c • μ - c • (μ - M *ᵥ α) := by
        rw [Matrix.mulVec_smul, smul_sub, sub_sub_cancel]
      rw [h1, Matrix.mulVec_sub, hcu, Matrix.mulVec_mulVec, hAiA, Matrix.one_mulVec, Matrix.mulVec_smul]
    have hint : ∀ i, (Ai *ᵥ (M *ᵥ (c • α))) i ∈ Formalism.UG.intL L := by
      intro i
      rw [heq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact Subring.sub_mem _ (hu i) (Subring.mul_mem _ hc (hν i))
    have hcα : ∀ k, (c • α) k ∈ Formalism.UG.intL L := fun k => Subring.mul_mem _ hc (hα k)
    refine ⟨α, hα, hν, hint, fun k => ?_⟩
    have := hbd (c • α) hcα hint k
    simpa only [Pi.smul_apply, smul_eq_mul] using this
  obtain ⟨α, hα, hν, hcαA, hbdα⟩ := key m hm hxm
  obtain ⟨α', hα', hν', hcα'A, hbdα'⟩ := key m' hm' hxm'

  have hσcα : ∀ i, (Ai *ᵥ (M *ᵥ (σ c • α))) i ∈ Formalism.UG.intL L := by
    intro i
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    refine Subring.sum_mem _ fun k _ => ofV _ ?_
    calc Valued.v ((Ai * M) i k * (σ c * α k)) = Valued.v ((Ai * M) i k) * Valued.v (c * α k) := by
          rw [map_mul, map_mul, map_mul, hv]
      _ ≤ Valued.v ((Ai * M) i k) * Valued.v ϖ ^ e k := mul_le_mul' le_rfl (hbdα k)
      _ = Valued.v ((Ai * M) i k * ϖ ^ e k) := by rw [map_mul, map_pow]
      _ ≤ 1 := toV _ (hAM i k)

  have hz : ∀ z : Matrix (Fin n') (Fin n) L, (∀ i j, (z * A) i j ∈ Formalism.UG.intL L) →
      c * Formalism.UG.hform σ J (z *ᵥ m) (z *ᵥ m') - c * Formalism.UG.hform σ J (z *ᵥ (M *ᵥ α)) (z *ᵥ (M *ᵥ α'))
        ∈ Formalism.UG.intL L := by
    intro z hzA
    have hzw : ∀ w : Fin n → L, (∀ i, (Ai *ᵥ w) i ∈ Formalism.UG.intL L) → ∀ i, (z *ᵥ w) i ∈ Formalism.UG.intL L := by
      intro w hw
      have : z *ᵥ w = (z * A) *ᵥ (Ai *ᵥ w) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hAAi, Matrix.mul_one]
      rw [this]; exact mulVec_int' hzA hw
    have e1 : z *ᵥ m = z *ᵥ (M *ᵥ α) + z *ᵥ (m - M *ᵥ α) := by
      rw [← Matrix.mulVec_add, add_sub_cancel]
    have e2 : z *ᵥ m' = z *ᵥ (M *ᵥ α') + z *ᵥ (m' - M *ᵥ α') := by
      rw [← Matrix.mulVec_add, add_sub_cancel]
    have s1 : σ c • (z *ᵥ (M *ᵥ α)) = z *ᵥ (M *ᵥ (σ c • α)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    have s2 : c • (z *ᵥ (M *ᵥ α')) = z *ᵥ (M *ᵥ (c • α')) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    have hexp : c * Formalism.UG.hform σ J (z *ᵥ m) (z *ᵥ m') - c * Formalism.UG.hform σ J (z *ᵥ (M *ᵥ α)) (z *ᵥ (M *ᵥ α')) =
        Formalism.UG.hform σ J (σ c • (z *ᵥ (M *ᵥ α))) (z *ᵥ (m' - M *ᵥ α')) +
        Formalism.UG.hform σ J (z *ᵥ (m - M *ᵥ α)) (c • (z *ᵥ (M *ᵥ α'))) +
        c * Formalism.UG.hform σ J (z *ᵥ (m - M *ᵥ α)) (z *ᵥ (m' - M *ᵥ α')) := by
      rw [hform_smul_left' σ hσ, hform_smul_right', e1, e2, hform_add_left', hform_add_right', hform_add_right']
      ring
    rw [hexp, s1, s2]
    have hJi : ∀ i j, J i j ∈ Formalism.UG.intL L := hJ
    refine Subring.add_mem _ (Subring.add_mem _ ?_ ?_) (Subring.mul_mem _ hc ?_)
    · exact hform_int' σ hv hJi (hzw _ hσcα) (hzw _ hν')
    · exact hform_int' σ hv hJi (hzw _ hν) (hzw _ hcα'A)
    · exact hform_int' σ hv hJi (hzw _ hν) (hzw _ hν')

  have hmain : c * (Formalism.UG.hform σ J (y *ᵥ (M *ᵥ α)) (y *ᵥ (M *ᵥ α')) -
      Formalism.UG.hform σ J (x *ᵥ (M *ᵥ α)) (x *ᵥ (M *ᵥ α'))) ∈ Formalism.UG.intL L := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hform_mulVec_mulVec, hform_mulVec_mulVec, ← hform_sub_mat, ← hform_smul_right']
    set D := Formalism.UG.cT σ (y * M) * J * (y * M) - Formalism.UG.cT σ (x * M) * J * (x * M) with hD
    refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ofV _ ?_
    have h1 : Valued.v (α i) * Valued.v (c * α' j) ≤ Valued.v ϖ ^ max (e i) (e j) := by
      rcases le_total (e i) (e j) with h | h
      · rw [max_eq_right h]
        calc Valued.v (α i) * Valued.v (c * α' j) ≤ 1 * Valued.v ϖ ^ e j := mul_le_mul' (toV _ (hα i)) (hbdα' j)
          _ = _ := one_mul _
      · rw [max_eq_left h]
        calc Valued.v (α i) * Valued.v (c * α' j) = Valued.v (c * α i) * Valued.v (α' j) := by
              rw [map_mul, map_mul, mul_left_comm, ← mul_assoc]
          _ ≤ Valued.v ϖ ^ e i * 1 := mul_le_mul' (hbdα i) (toV _ (hα' j))
          _ = _ := mul_one _
    calc Valued.v (σ (α i) * D i j * (c • α') j) = (Valued.v (α i) * Valued.v (c * α' j)) * Valued.v (D i j) := by
          rw [Pi.smul_apply, smul_eq_mul, map_mul, map_mul, hv, mul_right_comm]
      _ ≤ Valued.v ϖ ^ max (e i) (e j) * Valued.v (D i j) := mul_le_mul' h1 le_rfl
      _ = Valued.v (D i j * ϖ ^ max (e i) (e j)) := by rw [map_mul, map_pow, mul_comm]
      _ ≤ 1 := toV _ (hG i j)
  have hfin : c * (Formalism.UG.hform σ J (y *ᵥ m) (y *ᵥ m') - Formalism.UG.hform σ J (x *ᵥ m) (x *ᵥ m')) =
      (c * Formalism.UG.hform σ J (y *ᵥ m) (y *ᵥ m') - c * Formalism.UG.hform σ J (y *ᵥ (M *ᵥ α)) (y *ᵥ (M *ᵥ α'))) -
      (c * Formalism.UG.hform σ J (x *ᵥ m) (x *ᵥ m') - c * Formalism.UG.hform σ J (x *ᵥ (M *ᵥ α)) (x *ᵥ (M *ᵥ α'))) +
      c * (Formalism.UG.hform σ J (y *ᵥ (M *ᵥ α)) (y *ᵥ (M *ᵥ α')) -
        Formalism.UG.hform σ J (x *ᵥ (M *ᵥ α)) (x *ᵥ (M *ᵥ α'))) := by ring
  rw [hfin]
  exact Subring.add_mem _ (Subring.sub_mem _ (hz y hya) (hz x hxa)) hmain

end GlobalTheory.Hk3.GramConv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramDifferenceEntryMemUniformizerPowIntegers
section
open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem gram_entry_eq_hform {L : Type} [Field L] (σ : L →+* L) {n n' r : ℕ}
    (J : Matrix (Fin n') (Fin n') L) (z : Matrix (Fin n') (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (j k : Fin r) :
    (Formalism.UG.cT σ (z * M) * J * (z * M)) j k =
      Formalism.UG.hform σ J (z *ᵥ fun i => M i j) (z *ᵥ fun i => M i k) := by
  have hz : ∀ a l, (z * M) a l = (z *ᵥ fun i => M i l) a := fun a l => by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp only [Formalism.UG.cT, Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hz,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem gramDiff_entry_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (n n' r : ℕ) (JT : GL (Fin n') L) (a : GL (Fin n) L)
  (x y : Matrix (Fin n') (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
  ϖ ∈ Formalism.UG.intL L → (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
    ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔ ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) → (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.GramEq σ JT x y →
  ∀ j k, ((Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M)) - (Formalism.UG.cT σ (x * M) * (JT : Matrix (Fin n') (Fin n') L) * (x * M))) j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ n n' r JT a x y M e hϖ hiff hM haM hG j k
  have hcO : ∀ t : ℕ, ϖ ^ t ∈ Formalism.UG.intL L := fun t => Subring.pow_mem _ hϖ t
  have hx : ∀ l, e l ≤ max (e j) (e k) →
      ∀ i, (x *ᵥ ((ϖ ^ max (e j) (e k)) • fun i => M i l)) i ∈ Formalism.UG.intL L := by
    intro l hl
    refine (hiff ((ϖ ^ max (e j) (e k)) • fun i => M i l) (fun i => ?_)).1
      ⟨(ϖ ^ max (e j) (e k)) • (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ fun i => M i l),
        fun i => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; exact Subring.mul_mem _ (hcO _) (hM i l)
    · have h1 : ((ϖ ^ max (e j) (e k)) • (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ fun i => M i l)) i =
          ((((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i l * ϖ ^ e l) * ϖ ^ (max (e j) (e k) - e l) := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hl]
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm]
      rw [h1]; exact Subring.mul_mem _ (haM i l) (hcO _)
    · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, a.mul_inv, Matrix.one_mulVec]
  have key := hG (fun i => M i j) (fun i => M i k) (fun i => hM i j) (fun i => hM i k) _ (hcO _)
    (hx j (le_max_left _ _)) (hx k (le_max_right _ _))
  rw [Matrix.sub_apply, gram_entry_eq_hform, gram_entry_eq_hform, mul_comm]
  exact key

end GlobalTheory.Hk3.HoweG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RegularAlgebraicPurityOfClozel
section
namespace GlobalTheory

theorem regularAlgebraicPurity_of_clozel (hP : GlobalTheory.Published.ClozelPurity) (hC : GlobalTheory.Published.ClozelCohomological) :
    GlobalTheory.Published.RegularAlgebraicPurity := by
  intro E _ _ _ a ha π hr
  exact ⟨hP E a ha π fun τ => (hr τ).2, hC E a ha π hr⟩

end GlobalTheory
end

