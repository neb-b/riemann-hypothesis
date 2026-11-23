module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalTheta
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetTranslateProjectedVacuumLe
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HalvesFreeAndAdjoint
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0073
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaValueStandardLatticeEqClassicalTheta
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormShortGeneratorEvalLeOrthonormalFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ShortPoint

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem isSB_smul (c : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (c • φ) :=
  (_root_.GlobalTheory.SW.isSB_algebra_haar_linear ℚ _ _ φ φ h h).2.1 c

theorem thA_sum (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (f : T → TF n g) (hf : ∀ i, IsSB (f i)) :
    thA X bas idx (∑ i ∈ s, f i) x = ∑ i ∈ s, thA X bas idx (f i) x := by
  induction s using Finset.induction_on with
  | empty => simpa using UnAct.thA_smul (X := X) (bas := bas) idx x 0 (0 : TF n g)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact UnAct.thA_add idx hs hx (hf a) (RecSum.isSB_sum s f hf)

theorem theta_sum₂ (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (W : T → ℂ) (f : T → TF n g) (hf : ∀ i, IsSB (f i))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thP X hr bas idx (∑ i ∈ s, W i • f i) P x = ∑ i ∈ s, W i * thP X hr bas idx (f i) P x := by
  unfold thP
  rw [← Jet.polyDeriv_sum_fun P _ s W _ fun i _ => ThetaHol.differentiable_thA idx hs (hf i) hx,
    thA_sum idx hs hx s _ fun i => isSB_smul _ (hf i)]
  congr 1
  funext w
  simp only [Finset.sum_apply, UnAct.thA_smul, Pi.smul_apply, smul_eq_mul]

theorem norm_mean_le (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (W : T → ℂ) (f : T → TF n g) (hf : ∀ i, IsSB (f i))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (κ : ℂ) {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hW : ∀ i, ‖W i‖ ≤ C)
    (hb : ∀ i, ‖κ * thP X hr bas idx (f i) P x‖ ≤ B) :
    ‖((Nat.card T : ℂ))⁻¹ * (κ * thP X hr bas idx (∑ᶠ i, W i • f i) P x)‖ ≤ C * B := by
  by_cases h0 : Nat.card T = 0
  · rw [h0]
    simpa using mul_nonneg hC hB
  haveI : Finite T := Nat.finite_of_card_ne_zero h0
  haveI := Fintype.ofFinite T
  have hpos : (0 : ℝ) < Nat.card T := by exact_mod_cast Nat.pos_of_ne_zero h0
  rw [finsum_eq_sum_of_fintype, theta_sum₂ hr idx hs hx _ W f hf, Finset.mul_sum, norm_mul, norm_inv,
    Complex.norm_natCast, inv_mul_le_iff₀ hpos]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (C * B) fun i _ => ?_).trans ?_)
  · rw [mul_left_comm, norm_mul]
    exact mul_le_mul (hW i) (hb i) (norm_nonneg _) hC
  · rw [Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]


omit [IsCMField E] in
theorem index_Ln (Λ : GenLat E n) (h : stdLat E n = stdL E n) :
    (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index =
      (stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup := by
  rw [← h, ← AddSubgroup.inf_relIndex_left]
  rfl


omit [IsCMField E] in
theorem zCard_eq (Λ : GenLat E n) (h : stdLat E n = stdL E n) {N M : ℕ} (hN : Λ.LevOK N M) (r : ℕ) :
    Λ.zCard N r = Λ.mIdx N r * ((stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup) ^ r := by
  rw [← index_Ln Λ h, GenLat.zCard, GenLat.mIdx, ← mul_pow]
  congr 1
  exact (AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hN.2.2)
    (Submodule.toAddSubgroup_mono (inf_le_left : Λ.Ln ≤ Λ.La))).symm

end Classical

theorem map_mem_HHa {T : Type} (m : T → ℕ) (n : ℕ) {F F' : IntermediateField ℚ ℂ} (h : F = F') (cc : T → T)
    (isX : T → Prop) (a : T → ℕ → ℕ) {P : MvPolynomial (Letter T m n) F} (hP : P ∈ HHa m n F cc isX a) :
    MvPolynomial.map (IntermediateField.equivOfEq h : F →+* F') P ∈ HHa m n F' cc isX a := by
  subst h
  have : (IntermediateField.equivOfEq (rfl : F = F) : F →+* F) = RingHom.id F := RingHom.ext fun _ => rfl
  rw [this, MvPolynomial.map_id]
  exact hP

theorem sum_coeff_rename {F S S' : Type} [Field F] (σ : F →+* ℂ) (e : S ≃ S') (P : MvPolynomial S F) :
    ∑ m ∈ (MvPolynomial.rename e (MvPolynomial.map σ P)).support,
      ‖(MvPolynomial.rename e (MvPolynomial.map σ P)).coeff m‖ = ∑ m ∈ P.support, ‖σ (P.coeff m)‖ := by
  rw [MvPolynomial.support_rename_of_injective e.injective, Finset.sum_image
    fun a _ b _ h => Finsupp.mapDomain_injective e.injective h,
    MvPolynomial.support_map_of_injective _ σ.injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain _ e.injective, MvPolynomial.coeff_map]

theorem norm_index_cancellation_le_bound {b κ t : ℂ} {m z Q : ℕ} {J C B : ℝ} {j : ℕ} (hJ : J = j) (hj : 0 < j) (hz : z = m * j)
    (hb : ‖b‖ ^ 2 = J) (hC : 0 ≤ C * (B / Real.sqrt J))
    (h : ‖((Q : ℂ))⁻¹ * (κ * t)‖ ≤ C * (B / Real.sqrt J)) :
    ‖b⁻¹ * (m : ℂ)⁻¹ * (Q : ℂ)⁻¹ * (z : ℂ) * κ * t‖ ≤ C * B := by
  have hJ0 : 0 < J := by rw [hJ]; exact_mod_cast hj
  have hs : 0 < Real.sqrt J := Real.sqrt_pos.2 hJ0
  have hbn : ‖b‖ = Real.sqrt J := by rw [← hb, Real.sqrt_sq (norm_nonneg _)]
  have hm : ‖(m : ℂ)⁻¹ * (z : ℂ)‖ ≤ J := by
    rw [hz, hJ, Nat.cast_mul, ← _root_.mul_assoc, norm_mul, Complex.norm_natCast]
    refine mul_le_of_le_one_left (Nat.cast_nonneg _) ?_
    by_cases h0 : (m : ℂ) = 0
    · simp [h0]
    · rw [inv_mul_cancel₀ h0, norm_one]
  calc ‖b⁻¹ * (m : ℂ)⁻¹ * (Q : ℂ)⁻¹ * (z : ℂ) * κ * t‖
      = (Real.sqrt J)⁻¹ * (‖(m : ℂ)⁻¹ * (z : ℂ)‖ * ‖((Q : ℂ))⁻¹ * (κ * t)‖) := by
        rw [← hbn, ← norm_inv, ← norm_mul, ← norm_mul]
        congr 1
        ring
    _ ≤ (Real.sqrt J)⁻¹ * (J * (C * (B / Real.sqrt J))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hm h (norm_nonneg _) hJ0.le) (inv_nonneg.2 hs.le)
    _ = C * B := by
        have := Real.mul_self_sqrt hJ0.le
        set s := Real.sqrt J
        rw [← this]
        field_simp

theorem norm_evR_le : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → r ≤ n → ∀ d : DeltaDat Xo c n, d.IsLev → 0 < d.pd → l.A = 1 → d.l₂.A = 1 → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (∃ ph ψ x₀, d.PhiPin ph ψ x₀) → UnitC d → ∀ (Λ : GenLat E n) (N : ℕ) (x0 : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → (∃ β : c.F, β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) → P ∈ harmL c Λ a → IsShortRule Xo c d Λ N x0 P f → ∀ k (x : (U.X k).dom), (U.X k).IsOrtho x.1 → ∀ lam : ℝ, 0 < lam → lam ^ 2 ≤ (U.X k).firstMinimumSq x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ≤ (d.pd : ℝ) ^ (fdeg E * r * n) * ((∑ m ∈ P.support, ‖σ (P.coeff m)‖) * (Real.pi * Real.exp 1 * t * (Formalism.L2.Pj.DF Dw a : ℕ)) ^ (((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (fdeg E * r : ℕ) * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (fdeg E * r * n)) := by
  intro hci E _ _ _ H Dw l Xo c σ r U hσ hU hr1 t ht hct a n hDom hrn d hlev hpd _ _ hnab hpin hunit Λ N x0 P f
    hΛu hΛt hΛl hβ hP hrule k x hxo lam hlam hlam2
  obtain ⟨sr, hnab⟩ := hnab
  obtain ⟨ph, ψ, x₀, hpin⟩ := hpin
  have hr : r = Dw.p + Dw.q := hU.1
  have hn : Even n := hDom.2
  letI A₁ : Algebra c.F ℂ := σ.toAlgebra
  let σ₂ : d.c₂.F →+* ℂ := σ.comp (d.eF.symm : d.c₂.F →+* c.F)
  letI A₂ : Algebra d.c₂.F ℂ := σ₂.toAlgebra
  have hσ₂ : ∀ s : c.F, σ₂ (d.eF s) = σ s := fun s => congrArg σ (d.eF.symm_apply_apply s)
  have hcomp : ∀ s : c.F, algebraMap d.c₂.F ℂ (d.eF s) = algebraMap c.F ℂ s := hσ₂
  have huf : IsUnitFr (U.X k) x.1 := fun τ i => by
    unfold dmin lminor
    rw [hxo τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    simp only [Function.comp, FD.sgn]
    split_ifs <;> simp
  obtain ⟨W, Dc, A, θ, v, κ, he, hg, hw, hL, hmk, hA, hrd, hth, hmean, hvac, hprod⟩ :=
    GlobalTheory.T.exists_analyticData_unitFrame_framedPoint E H Dw l Xo c σ r U hσ hU hr1 a n hDom k x huf
  obtain ⟨-, -, hlen, -, -⟩ := hx_ortho E r (U.X k) W.g Dc.bas Dc.idx Dc.sympl x.1 x.2 hxo
  obtain ⟨y₂, hy₂⟩ := hlev.2.2.2.2.2.2.1 ℂ hcomp (unC U k x)
  obtain ⟨B, hB, mk₂, hmk₂, hB₂, -⟩ := _root_.GlobalTheory.Dict.Lift.anFib_lift E H Dw l Xo c n d hcomp hlev r W.g (U.X k) Dc.bas Dc.idx W.e x.1
    (U.X k).Λ (unC U k x) A Dc.sympl x.2 hL y₂ hy₂ (W.mark k) hA
  obtain ⟨v0, hv0, hev⟩ := hrule ℂ hcomp (unC U k x) y₂ hy₂
  have hM : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  obtain ⟨-, hV, hVd, hstd⟩ := GenLatCmp.genLat_vset E n Λ.La
  have hΛ : Λ.La ∈ Vset E n d.l₂.M := hV _ N hM hΛu hΛt hΛl
  have hΛ1 : Λ.La ∈ Vset E n 1 := hVd 1 _ (one_dvd _) hΛ
  obtain ⟨Y, hY⟩ := (_root_.GlobalTheory.Dict.DualMark.dual_marking E H Dw d.l₂ r (U.X k) (U.X k).Λ mk₂ _ hL hmk₂
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 n N hΛl.1.pos
  have hval := _root_.GlobalTheory.Dict.shortValAt_eq_thP hci E H Dw d.l₂ d.Xo₂ d.c₂ r W.g (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ y₂ B
    Dc.sympl x.2 hL Dw.p n Dc.hr Dc.eL hr hn (he ▸ Dc.dir_eq) d.nab₂ hnab θ v κ (hB θ hrd) hvac hprod mk₂ hmk₂ hB₂
    Λ.La hΛ N hΛl Y hY a _ (map_mem_HHa _ n d.hF.symm _ _ _ hP.1) (d.w x0) _ v0 hv0
  have hmap : MvPolynomial.map (algebraMap d.c₂.F ℂ)
      (MvPolynomial.map (IntermediateField.equivOfEq d.hF.symm : c.F →+* d.c₂.F) P) = MvPolynomial.map σ P := by
    rw [MvPolynomial.map_map]
    exact congrArg (fun s => MvPolynomial.map s P) (RingHom.ext hσ₂)
  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)).IsHomogeneous (Formalism.L2.Pj.DF Dw a) :=
    (((GlobalTheory.T.exists_integralHarmonic_ne_zero_and_isHomogeneous E H Dw l c a n).2 P hP.1).map σ).rename_isHomogeneous
  have hcore := fun y => _root_.GlobalTheory.Dict.VacJet.jet_projA_le E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn H.w0 hw _ hL Λ.La hΛ1
    v hvac x.1 x.2 hxo t ht (hct k) θ κ hth hmean hprod lam hlam (fun u hu hu0 => hlam2.trans (hlen u hu hu0)) y _ _
    hhom
  obtain ⟨R, -, -, hR, hR0, -⟩ := VacMean.vac_proj_mean E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn
    H.w0 hw _ hL Λ.La hΛ1 v hvac
  rw [hR] at hR0
  have hJ : (0 : ℝ) < Real.sqrt ((((stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup) : ℝ) ^ r) :=
    Real.sqrt_pos.2 (by exact_mod_cast hR0)
  have hsb : IsSB (projA (U.X k) Dc.bas (H.w0 : E) (tens Λ.La (U.X k).Λ) v) := by
    obtain ⟨⟨v', hv'⟩, -, h, -⟩ := TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn _
      H.w0.isIntegral_coe hw _ hL 1 Λ.La hΛ1
    rw [h v hvac.1 v' hv']
    exact isSB_smul _ hv'.1
  have hβa : ‖σ (betaH (Dw := Dw) c Λ)‖ ^ 2 =
      (((stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup) : ℝ) ^ r := by
    rw [← index_Ln Λ hstd, hr, betaH, dite_eq_left hβ]
    exact hβ.choose_spec.2.2 σ
  rw [sum_coeff_rename] at hcore
  have hc2 := fun y => (le_div_iff₀ hJ).2 (hcore y)
  have hB0 := (norm_nonneg _).trans (hc2 0)
  have hC0 : (0 : ℝ) ≤ (d.pd : ℝ) ^ (W.g * n) := by positivity
  have hmeanle := norm_mean_le Dc.hr Dc.idx Dc.sympl x.2 (fun q => algebraMap d.c₂.F ℂ (d.w x0 q))
    (fun q => heisG (U.X k) Dc.bas (Y q) (projA (U.X k) Dc.bas (H.w0 : E) (tens Λ.La (U.X k).Λ) v))
    (fun q => ((heisG_laws E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn).2.2.2 (Y q) _ hsb).1) _ κ hC0 hB0
    (fun q => by
      rw [hg, hr]
      exact ShortVal.Coeff.norm_coeff_le E H Dw l Xo c n d hlev hpd ph ψ x₀ hpin (hr ▸ hrn) x0 q σ₂)
    (fun q => hc2 (Y q))
  have hfin := norm_index_cancellation_le_bound (Nat.cast_pow _ r).symm hR0 (zCard_eq Λ hstd hΛl r) hβa (mul_nonneg hC0 hB0) hmeanle
  have hev' : Formalism.L2.PjFree.toC (evR Xo c f (U.un k x)) = evR d.Xo₂ d.c₂ d.cδ y₂ * v0 := hev
  rw [hev', norm_mul, hunit A₂ y₂, _root_.one_mul, hval, hmap, ← hg]
  simp only [map_mul, map_inv₀, map_natCast, hcomp]
  exact hfin

end GlobalTheory.Dict.ShortPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaRuleLinearInHarmonicPolynomial
section
noncomputable section

namespace GlobalTheory.ShortRuleLinear

section General

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem map_mem_HHa {F F₂ : IntermediateField ℚ ℂ} (h : F = F₂) {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) F}
    (hP : P ∈ HHa Dw.mult n F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) :
    MvPolynomial.map (IntermediateField.equivOfEq h : F →+* F₂) P ∈
      HHa Dw.mult n F₂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
  subst h
  have e : (IntermediateField.equivOfEq (rfl : F = F) : F →+* F) = RingHom.id F := RingHom.ext fun _ => rfl
  rw [e, MvPolynomial.map_id]
  exact hP

theorem eq_sum_of_isShortRule (hC : ChartIndepSt2) (Xo : Moduli Dw l) (c : Coeff l) {n : ℕ} (d : DeltaDat Xo c n)
    (hd : d.IsLev) [StarRing (𝓞 E)] (hn : IsNab d.Xo₂ d.c₂ d.nab₂) (a : (E →+* ℂ) × ℕ → ℕ) (Λ : GenLat E n) (N : ℕ)
    (x0 : Fin n → Dw.La) (hU : Λ.Unimod) (hT : Λ.TrivAt d.l₂.M) (hL : Λ.LevOK N d.l₂.M) (m : ℕ) (cf : Fin m → c.F)
    (Q : Fin m → MvPolynomial (LtN Dw n) c.F) (g : Rul Xo c) (gs : Fin m → Rul Xo c)
    (hQ : ∀ i, Q i ∈ harmL c Λ a) (hg : g ∈ sec Xo c a n) (hgs : ∀ i, gs i ∈ sec Xo c a n)
    (hr : IsShortRule Xo c d Λ N x0 (∑ i, cf i • Q i) g) (hrs : ∀ i, IsShortRule Xo c d Λ N x0 (Q i) (gs i)) :
    g = ∑ i, cf i • gs i := by
  rw [← sub_eq_zero]
  refine GlobalTheory.Frames.ptsDetect_framed E H Dw l Xo c a n _
    (Submodule.sub_mem _ hg (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hgs i))) ?_
  intro k _ _ _ y
  let _ : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have hk : ∀ x : c.F, algebraMap d.c₂.F k (d.eF x) = algebraMap c.F k x := fun x => by
    show algebraMap c.F k (d.eF.symm (d.eF x)) = _
    rw [AlgEquiv.symm_apply_apply]
  obtain ⟨y₂, hy⟩ := hd.2.2.2.2.2.2.1 k hk y
  obtain ⟨v, hv, e⟩ := hr k hk y y₂ hy
  choose u hu eu using fun i => hrs i k hk y y₂ hy
  have hm : MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (∑ i, cf i • Q i) =
      ∑ i, d.eF (cf i) • MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (Q i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
    rfl
  rw [hm] at hv
  have hlin := _root_.GlobalTheory.shortThetaValue_linear hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hn n Λ N hU hT hL a (d.w x0) _ m (fun i => d.eF (cf i))
    (fun i => MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (Q i)) (fun i => map_mem_HHa d.hF.symm (hQ i).1) k y₂ v u hv hu
  let L := evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y
  have hL : ∀ f, L f = evR Xo c f y := fun _ => rfl
  change L (g - ∑ i, cf i • gs i) = 0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, hL, e, hlin, Finset.mul_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hL, eu, hk, Algebra.smul_def]
  ring

end General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem shortRule_linear : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), LawsSh T → ∀ (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La), Λ.Unimod → Λ.TrivAt (T.dδ j w.n).l₂.M → Λ.LevOK N (T.dδ j w.n).l₂.M → ∀ (m : ℕ) (cf : Fin m → T.Q.c.F) (Q : Fin m → MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (g : T.R j) (gs : Fin m → T.R j), (∀ i, Q i ∈ harmL T.Q.c Λ (wtA w)) → g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → (∀ i, gs i ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n) → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 (∑ i, cf i • Q i) g → (∀ i, IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 (Q i) (gs i)) → g = ∑ i, cf i • gs i := by
  intro hC D T _ hS j hj w Λ N x0 hU hT hL m cf Q g gs hQ hg hgs hr hrs
  obtain ⟨_, hn⟩ := hS.dNab j hj w.n
  exact eq_sum_of_isShortRule hC (T.Q.Xo j) T.Q.c (T.dδ j w.n) (hS.dLev j hj w.n) hn (wtA w) Λ N x0 hU hT hL m cf Q g gs
    hQ hg hgs hr hrs

end GlobalTheory.ShortRuleLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGeneratorPointwiseBoundOrthonormalFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ThetaPt

theorem isUnitFr_of_isOrtho {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
    {x : Frame X.Ψ r} (ho : X.IsOrtho x) : IsUnitFr X x := by
  intro τ i

  simp only [dmin, lminor]
  rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp_apply, sgn]
  split_ifs <;> simp

theorem sum_norm_coeff_rename_map {K α β : Type} [Field K] (σ : K →+* ℂ) (e : α ≃ β) (P : MvPolynomial α K) :
    ∑ m ∈ (MvPolynomial.rename e (MvPolynomial.map σ P)).support,
      ‖(MvPolynomial.rename e (MvPolynomial.map σ P)).coeff m‖ = ∑ m ∈ P.support, ‖σ (P.coeff m)‖ := by
  classical
  rw [MvPolynomial.support_rename_of_injective e.injective,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective e.injective h]
  simp only [MvPolynomial.coeff_rename_mapDomain _ e.injective, MvPolynomial.coeff_map]
  rw [MvPolynomial.support_map_of_injective _ σ.injective]

theorem theta_bound_ortho : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab → ∀ (xx : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : Rul Xo c, IsThRule Xo c nab xx P f → ∀ k (x : (U.X k).dom), (U.X k).IsOrtho x.1 → ∀ lam : ℝ, 0 < lam → lam ^ 2 ≤ (U.X k).firstMinimumSq x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ≤ (∑ m ∈ P.support, ‖σ (P.coeff m)‖) * (Real.pi * Real.exp 1 * t * (Formalism.L2.Pj.DF Dw a : ℕ)) ^ (((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (fdeg E * r : ℕ) * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (fdeg E * r * n) := by
  intro hCI E _ _ _ H Dw l Xo c σ r U hG hU hr1 t ht hc a n hDom _ nab hnab xx P hP f hf k x ho lam hlam hla

  have hunit : IsUnitFr (U.X k) x.1 := isUnitFr_of_isOrtho ho
  obtain ⟨W, Dc, A, θ, v, κ, hDe, hWg, hw0, hSD, hmark, hAm, hRead, hth1, hmean, hvac, hprod⟩ :=
    GlobalTheory.Dict.VSetup.exists_setup E H Dw l Xo c σ r U hG hU hr1 a n hDom k x hunit
  let _ : Algebra c.F ℂ := σ.toAlgebra
  have hn : Even n := hDom.2

  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨Yr, hYr⟩ : ∃ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E,
      IsRoots l (U.X k).Λ (W.mark k) l.M Y := by
    exact (DualMark.dual_marking E H Dw l r (U.X k) (U.X k).Λ (W.mark k) _ hSD hmark
      (Complex.isPrimitiveRoot_exp l.M hM.ne')).2.2.2.2 n l.M hM
  set Y := Yr fun b => (Submodule.Quotient.mk (xx b) : LevQ Dw l)
  have hY : ∀ b, (∃ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), a - xx b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ∧
        Y b - ((l.M : E)⁻¹) • W.mark k a ∈ (U.X k).Λ) ∧
        ∃ j : ℕ, ∀ s ∈ l.Mb ^ j, ∃ u ∈ (U.X k).Λ, s • Y b = (2 * l.M) • u := by
    intro b
    obtain ⟨⟨a', ha', hq, hmem⟩, hj⟩ := hYr (fun b => (Submodule.Quotient.mk (xx b) : LevQ Dw l)) b
    exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1 hq, hmem⟩, hj⟩

  have hval := (GlobalTheory.thetaRule_exists_and_eval hCI E H Dw l Xo c nab hnab a n xx P hP).2 f hf ℂ (unC U k x)
  have hdir : ∀ ℓ, letterDir (U.X k) Dc.hr Dc.idx (Dc.eL ℓ) =
      Pi.single ℓ.2.2 (Pi.single (W.e.symm ⟨ℓ.1, ℓ.2.1⟩) 1) := hDe ▸ Dc.dir_eq
  have heq := GlobalTheory.Dict.thVal_eq_thP hCI E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ
    (unC U k x) A Dc.sympl x.2 hSD Dw.p n Dc.hr Dc.eL hU.1 hn hdir nab hnab θ v κ hRead hvac hprod
    (W.mark k) hmark hAm xx Y hY a P hP _ hval

  have hstd : stdL E n ∈ Vset E n 1 := Base.stdL_mem_Vset n 1
  have hint : IsIntegral ℤ ((H.w0 : 𝓞 E) : E) := (H.w0).isIntegral_coe
  have hproj : projA (U.X k) Dc.bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v = v := by
    rw [(GlobalTheory.SW.TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn (H.w0 : E) hint hw0 (U.X k).Λ hSD 1
      (stdL E n) hstd).2.2.1 v hvac.1 v hvac, hvac.2.1, one_smul]

  have hlamL : ∀ u ∈ (U.X k).Λ, u ≠ 0 →
      lam ^ 2 ≤ (hx (U.X k) Dc.bas Dc.idx x.1 (pv (U.X k) Dc.idx x.1 u) (pv (U.X k) Dc.idx x.1 u)).re :=
    fun u hu hne => hla.trans ((GlobalTheory.Dict.hx_ortho E r (U.X k) W.g Dc.bas Dc.idx Dc.sympl x.1 x.2 ho).2.2.1 u hu hne)

  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).IsHomogeneous (DF Dw a) :=
    (((GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous E H Dw l c a n).2 P
      (by unfold harmA at hP; unfold HaO at hP; exact hP.1)).map _).rename_isHomogeneous
  have hb := GlobalTheory.Dict.VacJet.jet_projA_le E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn H.w0 hw0
    (U.X k).Λ hSD (stdL E n) hstd v hvac x.1 x.2 ho t ht (hc k) θ κ hth1 hmean hprod lam hlam hlamL Y
    (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)) (DF Dw a) hhom

  rw [hproj, AddSubgroup.relIndex_self, Nat.cast_one, one_pow, Real.sqrt_one, _root_.mul_one] at hb
  have hsum : ∑ m ∈ (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).support,
      ‖(MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).coeff m‖ =
        ∑ m ∈ P.support, ‖σ (P.coeff m)‖ := sum_norm_coeff_rename_map σ Dc.eL P
  have hgR : ((W.g : ℕ) : ℝ) = ((fdeg E * r : ℕ) : ℝ) := by rw [hWg]
  have hgn : W.g * n = fdeg E * r * n := by rw [hWg]
  rw [hsum, hgR, hgn] at hb
  have hv0 : Formalism.L2.PjFree.toC (evR Xo c f (U.un k x)) = evR Xo c f (unC U k x) := rfl
  rw [hv0, heq]
  exact hb

end GlobalTheory.Dict.ThetaPt
end

