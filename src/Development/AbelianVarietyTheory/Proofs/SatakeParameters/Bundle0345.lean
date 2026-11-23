module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0334
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0330
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0337
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0029
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleMoveScalarPowerOfP
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TwV.Xc.MoveScal

theorem embLL_mem' (D : D7) (z : D.what₂.LL) : D.what₂.embLL z ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral z).map D.what₂.embLL.toRatAlgHom

theorem embT_mem' (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral x).map (TaylorLogMetric.embT D τ).toRatAlgHom

theorem lamC_mul' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  rw [Formalism.L2.Ker.lamC_of_mem lam (mul_mem hx hy), Formalism.L2.Ker.lamC_of_mem lam hx, Formalism.L2.Ker.lamC_of_mem lam hy, ← map_mul]
  rfl

theorem lamC_ne' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (h0 : x ≠ 0) :
    TaylorLogMetric.lamC lam x ≠ 0 := by
  rw [Formalism.L2.Ker.lamC_of_mem lam hx]
  exact (map_ne_zero lam).2 fun h => h0 (congrArg Subtype.val h)

theorem scal_core {Mp Mg ML Mk χk P x y : ℂ} (e1 e1' e2 n2 : ℤ) (hMg : Mg ≠ 0) (hMk : Mk ≠ 0) (hχ : χk ≠ 0)
    (hP : P ≠ 0) :
    Mp * (Mg * ML * Mk)⁻¹ * (P⁻¹ * x) ^ (-e1) * y ^ e1' * ((P⁻¹ * x) ^ e2 * y ^ (-n2))⁻¹ * (Mk * χk⁻¹) *
        (χk * Mg * P ^ (-(e1 + e2))) =
      Mp * ML⁻¹ * x ^ (-e1) * y ^ e1' * (x ^ e2 * y ^ (-n2))⁻¹ := by
  rw [mul_zpow, mul_zpow, inv_zpow', inv_zpow', neg_neg, zpow_neg P (e1 + e2), zpow_add₀ hP, zpow_neg P e2]
  have hA : P ^ e1 ≠ 0 := zpow_ne_zero _ hP
  have hB : P ^ e2 ≠ 0 := zpow_ne_zero _ hP
  generalize P ^ e1 = A at hA ⊢
  generalize P ^ e2 = B at hB ⊢
  generalize x ^ (-e1) = X1
  generalize x ^ e2 = X2
  generalize y ^ e1' = Y1
  generalize y ^ (-n2) = Y2
  field_simp

end GlobalTheory.TwV.Xc.MoveScal


open GlobalTheory.TwV.Xc.MoveScal in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.TwV.Xc.moveBy_scal : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → S.Pair → ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → ∀ La' : (sysS H X std).Lt (j + 1), ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; GlobalTheory.TwU.pPow (sysS H X std) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹)) = (kapG (sysS H X std) ℂ_[D.what₂.places.resChar w] j c γ)⁻¹ * (GlobalTheory.TwU.pPow (sysS H X std) j (c, La) La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, La) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, La)) ((J.fd std).kerN (j + 1) La'))⁻¹))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hSp hPos hPair j hj c La γ g κ hr hLa hMove La' hLa'
  have hγL : ((sysS H X std).Pj j).IsLatTup (((sysS H X std).Lv.lev j c).smul γ La) :=
    (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ γ La).2 hLa
  have hjm : j < (sysS H X std).mm := by rw [(GlobalTheory.TwV.DelB.sysS_ranks S).1]; exact hj
  obtain ⟨hA1, -, -, -, hs1, hf1, -, -⟩ := hPair j hjm (c, La) La' hLa hLa'
  have hker := _root_.GlobalTheory.TwV.Xc.kerN_smul S hD hSp j hj c La γ g κ hr hLa hMove
  obtain ⟨hMgA, hkap⟩ := GlobalTheory.T.eigenvalue_arithmeticElement_at_site S hD hSp hPos j hj c La γ g κ hr hLa hMove (GlobalTheory.T.systemWeights_eq_shifted_character_exponents S hD hSp j hj La'.1)
  obtain ⟨hgU, hpt, -, r, hr_eq, -⟩ := hMove
  have hE := (GlobalTheory.TwV.Xc.eMat_unitary_det D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) (fun x => rfl) _ _ hr
    (gramN D j hj.le) (J.A.crd j hj.le) (J.pins.crd_orth j hj.le)).2 g hgU
  have hchi := GlobalTheory.ChiMove.chi_detId_smulLat D t.χ t.χ_ok ⟨_, hA1.2.2.1⟩ _ hE.1
  rw [hE.2] at hchi
  have hD1 := (hD j hj.le (c, La) hLa).2.2.2
  have hD2 := (hD j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La) hγL).2.2.2
  have hUL : (J.fd std).dt j (c, La) ∈ U1 (sigD D) := hD1 ▸ det_unitary_adelic_point_gram_step_norm_one D j hj.le _
  have hUk : Matrix.GeneralLinearGroup.det κ.1 ∈ U1 (sigD D) :=
    det_unitary_adelic_point_gram_step_norm_one D j hj.le ⟨κ.1, ((((J.St j hj.le).K _).lev.U_eq κ.1).1 κ.2).1⟩
  have hUγ : (J.fd std).dt j (c, ((sysS H X std).Lv.lev j c).smul γ La) ∈ U1 (sigD D) :=
    hD2 ▸ det_unitary_adelic_point_gram_step_norm_one D j hj.le _
  have hUg : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g) ∈ U1 (sigD D) := by
    have e : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g) =
        (J.fd std).dt j (c, ((sysS H X std).Lv.lev j c).smul γ La) * (Matrix.GeneralLinearGroup.det κ.1)⁻¹ *
          ((J.fd std).dt j (c, La))⁻¹ := by
      rw [hD2, hD1, hpt, map_mul, map_mul, mul_inv_cancel_right, mul_inv_cancel_right]
    rw [e]
    exact mul_mem (mul_mem hUγ (inv_mem hUk)) (inv_mem hUL)

  have hmm := S.law.mu_mul j hj
  have hMdt : S.muT (j + 1) ((J.fd std).dt j (c, (((sysS H X std).Lv.lev j c).smul γ La))) = S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) *
      S.muT (j + 1) ((J.fd std).dt j (c, La)) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) := by
    rw [hD2, hpt, map_mul, map_mul, ← hD1, hmm.2 _ (mul_mem hUg hUL) _ hUk, hmm.2 _ hUg _ hUL]
  have hMg := S.law.mu_ne hj hUg
  have hMk := S.law.mu_ne hj hUk
  have hχ : ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hP : (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => (map_ne_zero _).2 (Units.ne_zero (Matrix.GeneralLinearGroup.det g))
  have hcore : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) =
      GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, La) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, La)) ((J.fd std).kerN (j + 1) La'))⁻¹ := by
    simp only [GlobalTheory.TwU.scal0, Base.chiFac]
    rw [hker, hchi, hMdt]
    exact scal_core _ _ _ _ hMg hMk hχ hP
  have hbQ : (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) ∈ TaylorLogMetric.Qbar :=
    mul_mem (mul_mem (hr_eq ▸ embLL_mem' D r) hMgA) (zpow_mem (prod_mem fun τ _ => embT_mem' D τ _) _)
  have hb0 : (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) ≠ 0 := mul_ne_zero (mul_ne_zero hχ hMg) (zpow_ne_zero _ hP)
  have hALQ : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, La) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, La)) ((J.fd std).kerN (j + 1) La'))⁻¹ ∈ TaylorLogMetric.Qbar := mul_mem hs1 (inv_mem hf1)
  have hAγQ : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) ∈ TaylorLogMetric.Qbar := by
    rw [← mul_inv_cancel_right₀ hb0 (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹)), hcore]
    exact mul_mem hALQ (inv_mem hbQ)
  have hp0 : ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ≠ 0 :=
    Nat.cast_ne_zero.2 (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero
  have hpp : GlobalTheory.TwU.pPow (sysS H X std) j (c, La) La' = GlobalTheory.TwU.pPow (sysS H X std) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La)) := by
    unfold GlobalTheory.TwU.pPow
    rw [← zpow_add₀ hp0, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    dsimp only
    ring
  have hq0 : ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La)) ≠ 0 := zpow_ne_zero _ hp0
  have hl0 := lamC_ne' S.lam hbQ hb0
  rw [hkap, hpp, ← hcore, lamC_mul' S.lam hAγQ hbQ]
  field_simp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChartBasisDetNormOne
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem castSt_lb {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : GlobalTheory.TwU.StepCharts C i hi) (β : S.Ch) (T : GlobalTheory.TwU.StepCharts C' i hi) (hT : T = castSt h S) :
    ∃ β' : T.Ch, (T.K β').lev.Lb = (S.K β).lev.Lb := by
  subst hT
  subst h
  exact ⟨β, rfl⟩

theorem uB_det_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j ≤ D.R.m) (a : Lv.comp j) τ, ‖ι (embT D τ (uB J j hj a).1.det)‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι j hj a τ
  have hU := _root_.GlobalTheory.TwV.DelB.detCrdB_unit S hPos ι hι j hj
  have hO := (bAt_orth_lev S j hj a).1
  have e : (uB J j hj a).1.det = (J.A.crd j hj).1.det * (bAt J j hj a).1.det := by
    simp [uB, Matrix.det_mul]
  rw [e]
  cases j with
  | zero =>
    obtain ⟨c⟩ := Formalism.MainNotions.G.KAat.cl_nonempty J.one a
    refine hU ((J.St 0 hj).chOf (J.e0 c)) (bAt J 0 hj a) hO (fun v => ?_) τ
    rw [(J.lev0 _).1]
    exact J.lb0 v
  | succ j =>
    obtain ⟨β, hβ⟩ := castSt_lb (X.onCh j hj) (GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st) ((I.at' j hj).st.eC.symm a).1 _ (J.st j hj)
    refine hU β (bAt J (j + 1) hj a) hO (fun v => ?_) τ
    rw [hβ]
    have h1 := J.lbB j hj ((I.at' j hj).st.eC.symm a).1 v
    rw [J.iw j hj _ v] at h1
    exact h1

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealAtSuccIffDecompositionValues
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem castSt_ofStepIn_read {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (St : GlobalTheory.TwU.StepCharts C' i hi) (hSt : St = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn S))
    (β : S.Ch) (c : {c // S.chOf c = β}) (c' : C'.cls i) (hc' : c' = castCls h i c.1) :
    (St.y c').1 = ((S.K β).y c).1 ∧
    (∀ κ' : (St.K (St.chOf c')).lev.U, ∃ κ : (S.K β).lev.U, κ.1 = κ'.1 ∧
      (((S.K β).lev.chi κ : ℂˣ) : ℂ) = (((St.K (St.chOf c')).lev.chi κ' : ℂˣ) : ℂ)) ∧
    ∀ (φ : C'.cls i → C'.Y i → ℂ) (z : Fr D i hi), φ c' (St.eY.symm z) = trC h i φ c.1 (S.eY.symm z) := by
  subst hSt hc' h
  obtain ⟨c, rfl⟩ := c
  exact ⟨rfl, fun κ' => ⟨κ', rfl, rfl⟩, fun φ z => rfl⟩

theorem nrmR_apply_eq {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (β : S.Ch) (φ : C.cls i → C.Y i → ℂ) (c : {c // S.chOf c = β}) (z : Fr D i hi) :
    nrmR S β φ c z = S.kTw β * (((S.tw β).ch ((S.K β).y c) : ℂ) * detF (cTw D i) z * φ c.1 (S.eY.symm z)) := rfl

end GlobalTheory.TwV.DelA


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.TwV.DelA.realAt_succ_decomp : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ (c : {c // (I.at' j hj).st.chOf c = ((I.at' j hj).st.eC.symm La.1).1}) (κ : ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.U), castCls (X.onCh j hj) (j + 1) c.1 = clsAt X H (j + 1) La.1 La.2 ∧ κ.1 = (d.kap (j + 1) hj La).1 ∧ ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 = (((I.at' j hj).st.K _).y c).1 ∧ ∀ φ V, RealAt d (j + 1) hj h La φ V ↔ ∀ z z' : Fr D (j + 1) hj, IsTr (Formalism.L2.Host.atInf (embT D) (d.gam (j + 1) hj La).1) z' z → evC (gatJ Lv (j + 1)).P ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk (I.at' j hj).st.pos (gramC (gramN D (j + 1) hj) (embT D)) (crdB (embT D) ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).B) V z = ((((I.at' j hj).st.K _).lev.chi κ : ℂˣ) : ℂ) * nrmR (I.at' j hj).st _ (trC (X.onCh j hj) (j + 1) φ) c z') := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj h La hLa
  have hc := clsOf_chart (S := (I.at' j hj).st) (H.core j hj) La.1 La.2 hLa
  have hcls : clsAt X H (j + 1) La.1 La.2 = castCls (X.onCh j hj) (j + 1) (clsOf (S := (I.at' j hj).st) (H.core j hj) La.1 La.2) :=
    clsAt_succ X H j hj La.1 La.2
  obtain ⟨hy, hk, hφ⟩ := GlobalTheory.TwV.DelA.castSt_ofStepIn_read (X.onCh j hj) (I.at' j hj).st (J.St (j + 1) hj) (J.st j hj) _
    ⟨_, hc⟩ _ hcls
  obtain ⟨κ, hκ1, hκχ⟩ := hk (d.kap (j + 1) hj La)
  refine ⟨⟨_, hc⟩, κ, hcls.symm, hκ1, hy, fun φ V => ?_⟩
  have htw := _root_.GlobalTheory.TwV.tw_at_rep S j hj _ ⟨_, hc⟩
  unfold RealAt
  refine forall_congr' fun z => forall_congr' fun z' => imp_congr_right fun _ => ?_
  have hR : d.chi (j + 1) hj La * ((D.chiD ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D (j + 1) *
        dPow (bAt J (j + 1) hj La.1).1 (fun _ => -(cTw D (j + 1))) * detF (cTw D (j + 1)) z' *
        φ (clsAt X H (j + 1) La.1 La.2) ((J.St (j + 1) hj).eY.symm z') =
      ((((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.chi κ : ℂˣ) : ℂ) *
        nrmR (I.at' j hj).st _ (trC (X.onCh j hj) (j + 1) φ) ⟨_, hc⟩ z' := by
    have a1 : d.chi (j + 1) hj La = ((((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.chi κ : ℂˣ) : ℂ) := hκχ.symm
    have a2 : ((D.chiD ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D (j + 1) =
        (((I.at' j hj).st.tw ((I.at' j hj).st.eC.symm La.1).1).ch (((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc⟩) : ℂ) := by
      rw [htw, Units.val_zpow_eq_zpow_val, hcls]
    have a3 : dPow (bAt J (j + 1) hj La.1).1 (fun _ => -(cTw D (j + 1))) = (I.at' j hj).st.kTw ((I.at' j hj).st.eC.symm La.1).1 := rfl
    rw [a1, a2, a3, hφ φ z', GlobalTheory.TwV.DelA.nrmR_apply_eq]
    ring
  simp only [J.pos j hj]
  refine Iff.trans (Eq.congr_right hR) ?_
  exact Iff.rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterUniformizingIdeleMemCoeffField
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc.MuLL

theorem hchar_eq_prod_val {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L)
    (T : Finset (HeightOneSpectrum (𝓞 L))) (b : Neutral.B1.Ideles L) (hb : Formalism.L2.Host.IsFinIdele b)
    (h1 : ∀ P, P ∉ T → (b : AdeleRing (𝓞 L) L).2 P = 1) (hu : ∀ P ∈ T, χ.UnrAt P) :
    ∃ n : HeightOneSpectrum (𝓞 L) → ℤ, χ.1 b = ∏ P ∈ T, χ.val P ^ n P :=
  _root_.GlobalTheory.HeckeFinVal.eq_prod_val_zpow χ T b hb h1 hu

theorem transfer_eq_zero {F E F' E' : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E']
    (iE : E' ≃+* E) (iA : AfE F' E' ≃+* AfE F E) (hrat : ∀ x : E', iA (x ⊗ₜ[F'] 1) = iE x ⊗ₜ[F] 1)
    (hint : ∀ y, iA y ∈ RInt F E ↔ y ∈ RInt F' E')
    (ι : AfE F' E' ≃+* FiniteAdeleRing (𝓞 E') E') (hι : GlobalTheory.TwU.IsAdIso ι)
    (z : AfE F E) (ℓ D : ℕ) (hℓ : 0 < ℓ) (hD : 0 < D)
    (hz : ∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E)
    (P : HeightOneSpectrum (𝓞 E')) (hP : ((ℓ : ℕ) : 𝓞 E') ∈ P.asIdeal) :
    ι (iA.symm z) P = 0 :=
  _root_.GlobalTheory.TwV.Xc.adIso_comp_zero_of_div iE iA hrat hint ι hι z ℓ D hℓ hD hz P hP

theorem exists_div_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 F)) (z : AfE F E) (hz : ∀ w', w' ≠ w → prV (E := E) w' z = 0)
    (ℓ : ℕ) (hℓ : ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal) :
    ∃ D : ℕ, 0 < D ∧ ∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E :=
  GlobalTheory.T.exists_nat_mul_div_pow_mem_integral_finiteAdele w z hz ℓ hℓ

theorem exists_h90_oneOff_preimage_at_splitPlace {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F)
    (hsig : ∀ x, spl (sigR σ (w.adicCompletion F) x) = swapR (w.adicCompletion F) (spl x))
    (π : (AfE F E)ˣ) (hπ : π ∈ U1 σ) (hoff : OneOff w π) :
    ∃ x : (AfE F E)ˣ, h90 σ x = π ∧ OneOff w x :=
  _root_.GlobalTheory.TwV.Xc.Unif.exists_h90_eq_oneOff_of_normOne_at_split_place σ w spl hsig π hπ hoff

theorem exists_nat_mem_coprime {E : Type} [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (P : HeightOneSpectrum (𝓞 E)) (hP : ((p : ℕ) : 𝓞 E) ∉ P.asIdeal) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ ((ℓ : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ Nat.Coprime ℓ p :=
  _root_.GlobalTheory.natCast_mem_heightOneSpectrum_coprime p hp P hP

end GlobalTheory.TwV.Xc.MuLL

namespace GlobalTheory.TwV.Xc.MuLL

open GlobalTheory.TwU (IsAdIso exists_isAdIso)

theorem exists_unitaryOneFiniteAdelic_of_det_normOne (D : D7) (π : (AfE D.host.F D.host.E)ˣ) (hπ : π ∈ U1 (sigD D)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = π := by
  have hd' : (π : AfE D.host.F D.host.E) * sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) π = 1 := by
    have := congrArg Units.val hπ
    simpa [Formalism.L2.DIV.U1, Formalism.L2.DIV.conjId] using this
  refine ⟨⟨Units.map (Matrix.scalar (Fin 1) : AfE D.host.F D.host.E →+* _).toMonoidHom π, ?_⟩, ?_⟩
  · show cT _ _ * _ * _ = _
    ext a b
    fin_cases a; fin_cases b
    simp [cT, Matrix.mul_apply, sigD]
    rw [mul_comm]
    exact hd'
  · ext
    simp

end GlobalTheory.TwV.Xc.MuLL

namespace GlobalTheory.TwV.Xc.MuLL

open GlobalTheory.TwU (IsAdIso exists_isAdIso)

theorem natCast_not_mem_of_coprime {R : Type} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) (a b : ℕ) (hab : Nat.Coprime a b)
    (hb : ((b : ℕ) : R) ∈ I) : ((a : ℕ) : R) ∉ I := by
  intro ha
  obtain ⟨c, d, h⟩ := (Nat.isCoprime_iff_coprime.2 hab : IsCoprime (a : ℤ) (b : ℤ))
  have h' := congrArg (Int.cast : ℤ → R) h
  push_cast at h'
  apply hI
  rw [Ideal.eq_top_iff_one, ← h']
  exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)


set_option maxHeartbeats 4000000 in
theorem mu_mem_LL : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    KIn t → ∀ v π, Formalism.L2.Host.IsUnifAt J v π → ∀ j < D.R.m, ∃ r : D.what₂.LL, D.what₂.embLL r = S.muT (j + 1) π) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hDict _hSpl hK v π hπ j hj
  have hpp : (D.what₂.places.resChar w).Prime := Fact.out
  have hpw0 : (((D.what₂.places.resChar w : ℕ)) : 𝓞 D.host.F) ∈ ((A0 J).pl v).1.asIdeal := ((A0 J).pl v).2
  obtain ⟨x', hx'h, hx'off⟩ := exists_h90_oneOff_preimage_at_splitPlace (sigD D) ((A0 J).pl v).1 ((A0 J).spl v) (J.one.good.sig v) π hπ.1 hπ.2.1
  obtain ⟨y, hy⟩ := exists_unitaryOneFiniteAdelic_of_det_normOne D π hπ.1
  set x : (AfE t.X.F t.X.E)ˣ := Units.map J.A.iA.symm.toRingHom.toMonoidHom x' with hxdef
  have hxx : Units.map J.A.iA.toRingHom.toMonoidHom x = x' := by ext; simp [hxdef]
  have hq : J.A.q x = J.dtU y := J.pins.q_dt x y (by rw [hy, hxx, hx'h])
  have hmu : S.muT (j + 1) π = (((t.O u μ).mt (j + 1) (J.A.q x) : ℂˣ) : ℂ) := by
    rw [← hy, S.law.mu_read j hj y, hq]
  obtain ⟨ι, hι⟩ := exists_isAdIso t.X.F t.X.E
  set b : Neutral.B1.Ideles t.X.E := MulEquiv.prodUnits.symm (1, Units.map ι.toRingHom.toMonoidHom x) with hbdef
  have hb : Formalism.L2.Host.IsFinIdele b := fun _ => rfl
  have hmuTil := J.pins.muTil ι hι ⟨j, hj⟩ b x hb rfl

  have hfin : {P : HeightOneSpectrum (𝓞 t.X.E) | P.asIdeal ∣ Ideal.span {((D.what₂.places.resChar w : ℕ) : 𝓞 t.X.E)}}.Finite :=
    Ideal.finite_factors (by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hpp.ne_zero)
  set T := hfin.toFinset with hT
  have hmemT : ∀ P, P ∈ T ↔ ((D.what₂.places.resChar w : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
    intro P
    rw [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  have h1 : ∀ P, P ∉ T → (b : AdeleRing (𝓞 t.X.E) t.X.E).2 P = 1 := by
    intro P hP
    rw [hmemT] at hP
    obtain ⟨ℓ, hℓ0, hℓP, hcop⟩ := exists_nat_mem_coprime _ hpp P hP
    have hℓw : ((ℓ : ℕ) : 𝓞 D.host.F) ∉ ((A0 J).pl v).1.asIdeal :=
      natCast_not_mem_of_coprime _ ((A0 J).pl v).1.isPrime.ne_top ℓ _ hcop hpw0
    set z : AfE D.host.F D.host.E := (x' : AfE D.host.F D.host.E) - 1 with hzdef
    have hz : ∀ w', w' ≠ ((A0 J).pl v).1 → prV (E := D.host.E) w' z = 0 := by
      intro w' hw'
      rw [hzdef, map_sub, hx'off w' hw', map_one, sub_self]
    obtain ⟨Dd, hDd, hdiv⟩ := exists_div_int _ z hz ℓ hℓw
    have h0 := transfer_eq_zero t.seam.iE J.A.iA J.pins.iA_rat J.pins.iA_int ι hι z ℓ Dd hℓ0 hDd hdiv P hℓP
    have e1 : ((x : (AfE t.X.F t.X.E)ˣ) : AfE t.X.F t.X.E) = J.A.iA.symm z + 1 := by
      rw [hzdef, map_sub, map_one, sub_add_cancel]
      rfl
    have e2 : (b : AdeleRing (𝓞 t.X.E) t.X.E).2 = ι ((x : (AfE t.X.F t.X.E)ˣ) : AfE t.X.F t.X.E) := rfl
    rw [e2, e1, map_add (f := _), map_one]
    show ι (J.A.iA.symm z) P + 1 = 1
    rw [h0, zero_add]
  have hu : ∀ P ∈ T, (t.glob.mu0 ⟨j, hj⟩).UnrAt P := by
    intro P hP
    rw [hmemT] at hP
    refine (J.pins.mu0 ⟨j, hj⟩).unr P fun i hgi => ?_
    have hne : D.what₂.places.resChar w ≠ t.Pr.g i := by
      rw [t.g_rec i]
      exact (GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg).2.2.2 i
    have hcop : Nat.Coprime (t.Pr.g i) (D.what₂.places.resChar w) :=
      (Nat.coprime_primes (t.pr_ok.g_prime i) hpp).2 hne.symm
    exact natCast_not_mem_of_coprime _ P.isPrime.ne_top _ _ hcop hP hgi
  obtain ⟨n, hn⟩ := hchar_eq_prod_val (t.glob.mu0 ⟨j, hj⟩) T b hb h1 hu
  set kU : t.X.Kˣ := ∏ P ∈ T, t.Ch.muVal ⟨j, hj⟩ P ^ n P with hkU
  have hk : Units.map t.seam.σ₀.toMonoidHom kU = (t.glob.mu0 ⟨j, hj⟩).1 b := by
    rw [hn, hkU, map_prod]
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [map_zpow]
    congr 1
    apply Units.ext
    rw [Units.coe_map, ← t.glob_σ]
    refine J.pins.ch.muVal ⟨j, hj⟩ P fun i hgi => ?_
    rw [hmemT] at hP
    have hne : D.what₂.places.resChar w ≠ t.Pr.g i := by
      rw [t.g_rec i]
      exact (GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg).2.2.2 i
    have hcop : Nat.Coprime (t.Pr.g i) (D.what₂.places.resChar w) :=
      (Nat.coprime_primes (t.pr_ok.g_prime i) hpp).2 hne.symm
    exact natCast_not_mem_of_coprime _ P.isPrime.ne_top _ _ hcop hP hgi
  rw [hmu]
  by_cases hμ : μ = D.what₂.mu0
  · obtain ⟨r, hr⟩ := hK (kU : t.X.K)
    refine ⟨r, ?_⟩
    rw [hr, (J.pins.ref hμ).2, hmuTil, ← hk]
    rfl
  · obtain ⟨ξ, hξ, hmt⟩ := J.pins.tw μ hμ rfl
    have e : (t.O u μ).mt (j + 1) = D.muTil (j + 1) * ξ := by
      rw [hmt u]
      exact if_pos (⟨by omega, by omega⟩ : 1 ≤ j + 1 ∧ j + 1 ≤ D.R.m)
    obtain ⟨r, hr⟩ := hK ((kU : t.X.K) * ((t.tup μ : Chr t.X.F t.X.E t.X.K) x : t.X.K))
    refine ⟨r, ?_⟩
    rw [hr, e, MonoidHom.mul_apply, Units.val_mul, hmuTil, hξ x, ← hk, map_mul]
    rfl

end GlobalTheory.TwV.Xc.MuLL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnJointsHoldAllTuples
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AllTuples

theorem joints_all_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp), I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → I.StdC l Z C → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → G.LatTied hT Gi Gl → (∀ a : I.ι, GlobalTheory.TwV.JointsAt t a) ∧ ∀ u, ex.tw.e0 u (I.rec7 l Z).what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  intro B X I hOk hP l Z l0 L hT Gi Gl K Y cX ex t C full g hTw hJ htw hpi hK hRd hpin hC hDt hh hf hchi hLat
  refine ⟨fun a => ?_, fun u => ?_⟩
  · exact _root_.GlobalTheory.TwV.jointsAt_of_jIn t a hLat (fun u =>
      GlobalTheory.T.trueColumn_exists_chainCharts_kernelData_forms I hOk hP l Z l0 L hT Gi Gl K Y cX ex t C full g hTw hJ htw hpi hK hRd hpin hC hDt hh hf hchi u a)
  · rw [htw]
    exact _root_.GlobalTheory.TwU.AtTrue.stepZeroFormIdentification_refTuple_eq_id I hOk hP l Z l0 u

end GlobalTheory.TwU.AllTuples
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedGoodOfSelfDual
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU.UnrTwist

theorem tw_tw_inv {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (μ : Γ →* kˣ) :
    UpperTheory.V.Af.tw (UpperTheory.V.Af.tw r μ) μ⁻¹ = r := by
  ext s i j
  simp [UpperTheory.V.Af.tw_val, smul_smul]

theorem algSat_eq' (n q : ℕ) (B : Multiset ℂˣ) :
    UpperTheory.V.Af.algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [UpperTheory.V.Af.algSat, Multiset.bind_singleton, Multiset.map_map]

end GlobalTheory.RoadU.UnrTwist

end

