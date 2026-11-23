module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import GroundTheory.GlobalFields.Adele.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1717
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqUnitMulPeriodJets
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockPos

theorem fock_jets_eq_unit_mul_period_jets : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0 → ∀ e0 : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 _ _ e0 → ∀ f, IsVacO ψ θ S T sS sT (colLat frS : Set _) (colLat frT : Set _) f → ∃ c : ℂˣ, ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ)) (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 = c * ((k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) e0) := by
  intro D ψ θ S T sS sT frS frT hS hT hcS hcT δ t0 hC hδ ht0 e0 he0 f hf
  obtain ⟨Θ, hΘ, hΘ0, hjet⟩ := _root_.GlobalTheory.FockPos.fock_jets_eq_theta ψ θ S T sS sT frS frT hS hT hcS hcT δ hC hδ f hf
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have he0ne : e0 ≠ 0 := by
    intro h
    have hn := he0.2.2.1
    rw [h] at hn
    have h0 : Formalism.MainNotions.TaylorLogMetric.normSq D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) S.rank T.rank) 0 = 0 := by
      simp [Formalism.MainNotions.TaylorLogMetric.normSq]
    rw [h0] at hn
    exact pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hG D.host.ccK δ t0 hC ht0) hn.symm
  have hK : Formalism.MainNotions.StandardLatticesGL3.KLat D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank)) :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D S.rank, GlobalTheory.NormSum.VacInt.sd_std D T.rank, rfl⟩
  obtain ⟨c, hc⟩ := (GlobalTheory.ThetaLine.theta_line D hG D.host.ccK δ hC S.rank T.rank _ hK).1 Θ hΘ e0 he0.1 he0ne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hΘ0 (by rw [hc, zero_smul])
  refine ⟨Units.mk0 c hc0, fun k => ?_⟩
  rw [hjet k, Units.val_mk0]
  rw [hc, (GlobalTheory.NormSum.applyAt0_minorPol_linear D S.rank T.rank (fun _ => 0) e0 he0.1.1).2.2.1 c]
  ring

end GlobalTheory.FockPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMinorPolZero
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormDictEx.Jets

open Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.AdForm GlobalTheory.AdForm.VacRead GlobalTheory.FockCompare GlobalTheory.MixPer GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk

variable {D : D7}

theorem xiN_differentiable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hgS : S.gram = 1) (hgT : T.gram = 1) (hδ : δ ≠ 0)
    (hsc : sc * ‖δ‖ ^ 2 = 2 * Formalism.L2.Pj.xiR D) (f : WO S T → ℂ) (hf1 : IsThetaFunO ψ S T f)
    (hf2 : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) :
    Differentiable ℂ (xiN θ S T rfl rfl δ sc f) := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨hF, hann⟩ := GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ hσ ψ hψ S T (fun _ => 1) (fun _ => 1) f
    hf1 hf2
  set F : RW T S → ℂ := fun z => f (iotaW σ T S z) with hFdef
  set r : ℝ := sc / 2 with hr
  let L : RW T S →L[ℂ] RW T S := (-δ⁻¹) • ContinuousLinearMap.id ℂ (RW T S)
  have hL : ∀ Z τ i j, L Z τ i j = -(δ⁻¹ * Z τ i j) := fun Z τ i j => by simp [L]
  set E : RW T S → ℂ := fun Z => Complex.exp ((Real.pi * r * ∑ τ, ∑ i, ∑ j, ‖Z τ i j‖ ^ 2 : ℝ) : ℂ) with hE
  have hxi : xiN θ S T rfl rfl δ sc f = fun Z => F (L Z) * E Z := by
    funext Z
    unfold xiN
    have hp : realPt θ (fun τ => Matrix.of fun i j => -(δ⁻¹ * Z τ (Fin.cast rfl i) (Fin.cast rfl j))) =
        iotaW σ T S (L Z) := by
      refine realPt_eq hθ _ _ (by funext i j; exact hσ.fin _) fun τ => ?_
      funext i j
      show θ τ (infPart D (σ fun τ' => L Z τ' i j)) = _
      rw [hσ.comp]
      simp [hL]
    rw [hp, mul_comm]
    congr 2
    show (Real.pi : ℂ) / 2 * ((sc : ℂ) * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Z τ i j)) = _
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hr]; push_cast; ring
  rw [hxi]
  have hdG : ∀ Z Y, fderiv ℝ (fun Z => F (L Z)) Z Y = fderiv ℝ F (L Z) (L Y) := fun Z Y => by
    have h : HasFDerivAt (fun Z => F (L Z)) ((fderiv ℝ F (L Z)).comp (L.restrictScalars ℝ)) Z :=
      (hF (L Z)).hasFDerivAt.comp Z (L.restrictScalars ℝ).hasFDerivAt
    rw [h.fderiv]; rfl
  refine GlobalTheory.FockPos.differentiable_mul_of_cr (fun Z => F (L Z)) E
    (fun Z Y => (2 * Real.pi * r * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) : ℂ))
    (hF.comp (L.restrictScalars ℝ).differentiable) (GlobalTheory.FockPos.gauss_cr r).1 (fun Z Y => ?_)
    (GlobalTheory.FockPos.gauss_cr r).2
  rw [hdG, hdG]
  have hj : GlobalTheory.VacUnique.jO S T (fun _ => 1) (fun _ => 1) (L Y) = L (Complex.I • Y) := by
    rw [L.map_smul]; funext τ; rw [GlobalTheory.VacUnique.jO_apply]
    change Complex.I • ((1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) * Matrix.of (L Y τ) *
      (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) = _
    rw [Matrix.one_mul, Matrix.mul_one]; rfl
  have h := hann (L Z) (L Y)
  rw [hj] at h
  have hdd : δ⁻¹ * starRingEnd ℂ δ⁻¹ = (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_inv, Complex.normSq_eq_norm_sq]
  have hom : ∀ Y' : RW T S, GlobalTheory.VacUnique.omO S T (L Z) (L Y') =
      ∑ τ, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) *
        ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y' τ i j)).re := by
    intro Y'
    rw [GlobalTheory.VacUnique.omO_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    show 2 * (tauE D τ D.host.xi0 * GlobalTheory.VacUnique.hAt S T τ (L Z τ) (L Y' τ)).re = _
    rw [GlobalTheory.FockPos.xi_zero_eq_host τ]
    erw [hAt_one S T hgS hgT τ (L Z τ) (L Y' τ)]
    have hs : ∑ i, ∑ j, L Z τ i j * starRingEnd ℂ (L Y' τ i j) =
        (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y' τ i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hL, hL, ← hdd]
      simp only [map_neg, map_mul]
      ring
    rw [hs]
    congr 2
    ring
  rw [hom, hom] at h
  have hs2 : ∀ τ, (∑ i, ∑ j, Z τ i j * starRingEnd ℂ ((Complex.I • Y) τ i j)) =
      -Complex.I * ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) := fun τ => by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [hs2] at h
  have key := key_sum (Formalism.L2.Pj.xiR D) ((‖δ‖ ^ 2)⁻¹) fun τ => ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j)
  have hrk : Formalism.L2.Pj.xiR D * (‖δ‖ ^ 2)⁻¹ = r :=
    scale_eq _ _ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hδ)) hsc
  rw [hrk] at key
  show _ = -((2 * Real.pi * r * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) : ℂ) * F (L Z))
  linear_combination h + Real.pi * Complex.I * F (L Z) * key +
    2 * Real.pi * r * (∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j)) * F (L Z) * Complex.I_sq

theorem frAt_one {n : ℕ} : GlobalTheory.FockPos.frAt (1 : GL (Fin n) D.host.E) = fun _ => 1 := by
  funext τ
  simp [GlobalTheory.FockPos.frAt]

theorem eq_gauss_mul (θ : InfFam D) (hθ : IsInfFam θ) (S T : HSp D) (δ : ℂ) (sc : ℝ) (hδ : δ ≠ 0)
    (hsc : sc * ‖δ‖ ^ 2 = 2 * Formalism.L2.Pj.xiR D) (f : WO S T → ℂ) (w : WO S T) (hw : w.map (finPart D) = 0) :
    f w = GlobalTheory.FockPos.gaussO θ 1 1 w * xiN θ S T rfl rfl δ sc f ((-δ) • GlobalTheory.FockPos.zCo θ 1 1 w) := by
  have hz : ∀ τ, GlobalTheory.FockPos.zCo θ (1 : GL (Fin S.rank) D.host.E) (1 : GL (Fin T.rank) D.host.E) w τ = compAt θ τ w := by
    intro τ
    simp only [GlobalTheory.FockPos.zCo, frAt_one, inv_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  set y := GlobalTheory.FockPos.zCo θ (1 : GL (Fin S.rank) D.host.E) (1 : GL (Fin T.rank) D.host.E) w with hy
  have hp : realPt θ (fun τ => Matrix.of fun i j => -(δ⁻¹ * ((-δ) • y) τ (Fin.cast rfl i) (Fin.cast rfl j))) = w := by
    refine realPt_eq hθ _ w hw fun τ => ?_
    funext i j
    rw [← hz τ]
    simp only [Matrix.of_apply, Fin.cast_eq_self, Pi.smul_apply, smul_eq_mul]
    field_simp
  unfold xiN
  rw [hp, GlobalTheory.FockPos.gaussO, ← hy, ← mul_assoc, ← Complex.exp_add]
  have hH : HV sc ((-δ) • y) ((-δ) • y) = (sc : ℂ) * (((‖δ‖ ^ 2 : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, ((‖y τ i j‖ ^ 2 : ℝ) : ℂ)) := by
    show (sc : ℂ) * (∑ τ, ∑ i, ∑ j, ((-δ) • y) τ i j * starRingEnd ℂ (((-δ) • y) τ i j)) = _
    congr 1
    simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, norm_neg]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    push_cast; ring
  have hc : (sc : ℂ) * ((‖δ‖ ^ 2 : ℝ) : ℂ) = 2 * (Formalism.L2.Pj.xiR D : ℂ) := by exact_mod_cast hsc
  have h0 : -((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, ((‖y τ i j‖ ^ 2 : ℝ) : ℂ) +
      (Real.pi : ℂ) / 2 * HV sc ((-δ) • y) ((-δ) • y) = 0 := by
    rw [hH, ← mul_assoc (sc : ℂ), hc, Complex.ofReal_mul]
    ring
  rw [h0, Complex.exp_zero, one_mul]

theorem apply_minorPol {a d : ℕ} {n : D.what₂.Tau → ℕ} (U : Tup D a d n)
    (l : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ →ₗ[ℂ] ℂ) (p : ℂ) (G : Formalism.MainNotions.TaylorLogMetric.VC D a d → ℂ)
    (h : ∀ k : Formalism.MainNotions.GL3Theta.Idx D a d →₀ ℕ, l (MvPolynomial.monomial k 1) =
      p ^ (k.sum fun _ e => e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G) :
    l (minorPol D U) = p ^ (a * ∑ τ, n τ) * Formalism.MainNotions.GL3Theta.applyAt0 D (minorPol D U) G := by
  conv_lhs => rw [(minorPol D U).as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum l, Formalism.MainNotions.GL3Theta.applyAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hk := GlobalTheory.RotJets.card_of_mem_support U hα
  rw [Finsupp.card_toMultiset] at hk
  have e : (MvPolynomial.monomial α ((minorPol D U).coeff α) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ) =
      (minorPol D U).coeff α • MvPolynomial.monomial α 1 := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hk' : (α.sum fun _ e => e) = a * ∑ τ, n τ := hk
  rw [e, map_smul, h, GlobalTheory.FockPos.applyAt0_monomial', hk', smul_eq_mul]
  ring

theorem fock_minorPol_zero : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) {a d : ℕ} (hA : A.rank = a) (hB : B.rank = d) (n : D.what₂.Tau → ℕ) (s : ℂ) (sc : ℝ), IsStdChar D ψ (-1) → IsInfFam θ → A.gram = 1 → B.gram = 1 → s ≠ 0 → (∀ τ, sc * ‖s‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) → ∃ c₁ : ℂ, c₁ ≠ 0 ∧ ∀ f : WO A B → ℂ, IsThetaFunO ψ A B f → (∀ τ, IsFockVacAt (heisO ψ A B) θ τ (cplxO 1 1) f) → ∀ T : Tup D a d n, pureTensorL (aPlusAll (heisO ψ A B) θ (fun _ => cplxO 1 1) (fun _ => 1) (fun _ => 1)) f (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D a d => ((k.1, Fin.cast hB.symm k.2.1, Fin.cast hA.symm k.2.2) : FVar D B.rank A.rank)) (minorPol D T)) 0 = c₁ * Formalism.MainNotions.GL3Theta.applyAt0 D (minorPol D T) (GlobalTheory.AdForm.xiN θ A B hA hB s sc f) := by
  intro D ψ θ A B a d hA hB n s sc hψ hθ hgA hgB hs hsc
  subst hA hB
  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hsc' : sc * ‖s‖ ^ 2 = 2 * Formalism.L2.Pj.xiR D := by
    rw [hsc τ₀, GlobalTheory.FockPos.norm_embedding_xi0_eq]
  have hx : 0 < Formalism.L2.Pj.xiR D := by
    unfold Formalism.L2.Pj.xiR
    exact norm_pos_iff.2 ((map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  set p : ℂ := (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) * -s with hp
  have hp0 : p ≠ 0 := by
    refine mul_ne_zero (inv_ne_zero ?_) (neg_ne_zero.2 hs)
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  have hon : ∀ {V : HSp D}, V.gram = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin V.rank) D.host.E).1 *
      V.gram * (1 : GL (Fin V.rank) D.host.E).1 = 1 := by
    intro V hV
    rw [hV]
    simp [Formalism.UG.cT]
  refine ⟨p ^ (A.rank * ∑ τ, n τ), pow_ne_zero _ hp0, fun f hf1 hf2 T => ?_⟩
  have hG := xiN_differentiable ψ θ A B s sc hψ hθ hgA hgB hs hsc' f hf1 hf2
  set G := xiN θ A B rfl rfl s sc f with hGdef
  have hΦ : Differentiable ℂ (fun z : Formalism.MainNotions.TaylorLogMetric.VC D A.rank B.rank => G ((-s) • z)) :=
    hG.comp (differentiable_id.const_smul (-s))
  have hid : (fun k : Formalism.MainNotions.GL3Theta.Idx D A.rank B.rank => ((k.1, Fin.cast (rfl : B.rank = B.rank).symm k.2.1,
      Fin.cast (rfl : A.rank = A.rank).symm k.2.2) : FVar D B.rank A.rank)) = id := by
    funext v; rfl
  rw [hid, MvPolynomial.rename_id, AlgHom.id_apply]
  refine apply_minorPol T ((LinearMap.proj (0 : WO A B)).comp
    (pureTensorO ψ θ A B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f)) p G fun k => ?_
  have h := GlobalTheory.FockPos.fock_monomial_zero_of_on ψ θ A B 1 1 hψ hθ (hon hgA) (hon hgB) f _ hΦ
    (fun w hw => eq_gauss_mul θ hθ A B s sc hs hsc' f w hw) k
  rw [frAt_one, frAt_one, GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.FockPos.taylor_comp_smul' D _ hG] at h
  rw [GlobalTheory.FockPos.applyAt0_monomial']
  refine h.trans ?_
  rw [hp, mul_pow]
  ring

end GlobalTheory.NormDictEx.Jets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumThetaFunctionDerivativeComplexStructur
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section
namespace GlobalTheory.FockLineJ

variable {D : D7}

theorem theta_realAd {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (t : ℝ) :
    θ τ (fstA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E)) = t := by
  have h2 : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm := by
    have : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm = ⇑(GroundTheory.Global.homeomorphMixedSpace D.host.F).symm :=
      funext fun y => by
        rw [Homeomorph.eq_symm_apply]
        exact (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).apply_symm_apply y
    rw [this]
    exact (GroundTheory.Global.homeomorphMixedSpace D.host.F).symm.continuous
  let φ : ℝ →+* ℂ := ((θ τ).comp Algebra.TensorProduct.includeLeftRingHom).comp
    ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm.toRingHom.comp
      (algebraMap ℝ (mixedEmbedding.mixedSpace D.host.F)))
  have hφ : Continuous φ :=
    (hθ τ).2.comp (h2.comp (continuous_algebraMap ℝ (mixedEmbedding.mixedSpace D.host.F)))
  have e : ∀ s, φ s = θ τ (fstA D.host.F (realAd D.host.F s) ⊗ₜ[D.host.F] (1 : D.host.E)) := fun s => rfl
  rw [← e]
  have h1 : φ t = t * φ 1 := GlobalTheory.WeilVacMove.additive_real φ.toAddMonoidHom hφ t
  rw [h1, map_one, mul_one]

theorem realAd_smul_eq (t : ℝ) (a : AE D) :
    realAd D.host.F t • a = (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) * a := by
  rw [Algebra.smul_def]; rfl

theorem finPart_realAd_smul (t : ℝ) (a : AE D) : finPart D (realAd D.host.F t • a) = 0 := by
  rw [realAd_smul_eq, map_mul]
  have : finPart D (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 := by
    show sndA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E 1) = 0
    rw [show sndA D.host.F (realAd D.host.F t) = 0 from rfl, TensorProduct.zero_tmul]
  rw [this, zero_mul]

theorem theta_realAd_smul {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (t : ℝ) (a : AE D) :
    θ τ (infPart D (realAd D.host.F t • a)) = t * θ τ (infPart D a) := by
  rw [realAd_smul_eq, map_mul, map_mul]
  have : infPart D (realAd D.host.F t ⊗ₜ[D.host.F] (1 : D.host.E)) =
      fstA D.host.F (realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [this, theta_realAd hθ]


set_option synthInstance.maxHeartbeats 400000 in
theorem realAd_smul_eq_sum {m n : ℕ} {θ : InfFam D} (hθ : IsInfFam θ) {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (y : Mx D m n)
    (hy : ∀ τ, compAt θ τ y = z τ) (t : ℝ) :
    realAd D.host.F t • y = (∑ τ, lineAt θ τ (z τ)) t := by
  classical
  ext i j
  rw [← sub_eq_zero]
  have hl := fun τ => GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (z τ)
  have hs : ((∑ τ, lineAt θ τ (z τ)) t) i j = ∑ τ, lineAt θ τ (z τ) t i j := by
    generalize (Finset.univ : Finset D.what₂.Tau) = s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [Finset.sum_insert ha, AddMonoidHom.add_apply, Matrix.add_apply, ih]
  refine hσ.ext _ ?_ fun τ' => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sub, hs, map_sum, Matrix.smul_apply, finPart_realAd_smul, zero_sub, neg_eq_zero]
      exact Finset.sum_eq_zero fun τ _ => congrFun (congrFun ((hl τ).2.1 t) i) j
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sub, map_sub, hs, map_sum, map_sum, Matrix.smul_apply, theta_realAd_smul hθ, sub_eq_zero]
      have e1 : θ τ' (infPart D (y i j)) = z τ' i j := congrFun (congrFun (hy τ') i) j
      have e2 : ∀ τ, θ τ' (infPart D (lineAt θ τ (z τ) t i j)) = if τ' = τ then (t : ℂ) * z τ i j else 0 := by
        intro τ
        have h := congrFun (congrFun ((hl τ).2.2 t τ') i) j
        rw [compAt, Matrix.map_apply] at h
        rw [h]
        split_ifs <;> simp
      rw [e1, Finset.sum_congr rfl fun τ _ => e2 τ, Finset.sum_ite_eq]
      simp

theorem dLine_sum {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ι : Type} (s : Finset ι)
    (N : ι → ℝ →+ WO S T) (hN : ∀ i, Continuous (N i)) (hN0 : ∀ i t, (N i t).map (finPart D) = 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Continuous (⇑(∑ i ∈ s, N i) : ℝ → WO S T) ∧ (∀ t, ((∑ i ∈ s, N i) t).map (finPart D) = 0) ∧
      GlobalTheory.WeilVacMove.dLine ψ S T (∑ i ∈ s, N i) f = ∑ i ∈ s, GlobalTheory.WeilVacMove.dLine ψ S T (N i) f := by
  classical
  refine Finset.induction_on s ?_ ?_
  · refine ⟨?_, fun t => ?_, ?_⟩
    · rw [Finset.sum_empty]
      show Continuous fun _ : ℝ => (0 : WO S T)
      exact continuous_const
    · rw [Finset.sum_empty, AddMonoidHom.zero_apply]; ext i j; simp
    · rw [Finset.sum_empty, Finset.sum_empty]
      funext w
      simp [GlobalTheory.WeilVacMove.dLine]
  · intro a s ha ih
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨?_, fun t => ?_, ?_⟩
    · show Continuous fun t => N a t + (∑ x ∈ s, N x) t
      exact (hN a).add h1
    · rw [AddMonoidHom.add_apply]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, map_add]
      have ha := congrFun (congrFun (hN0 a t) i) j
      have hs := congrFun (congrFun (h2 t) i) j
      simpa only [Matrix.map_apply, Matrix.zero_apply, add_zero] using congrArg₂ (· + ·) ha hs
    · rw [GlobalTheory.BiJoinDeriv.dLine_add_line hψ (hN a) (hN0 a) h1 h2 hf, h3]

theorem fock_line_J : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ),
    IsStdChar D ψ (-1) → IsInfFam θ → IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
    ∀ x x' : WO S T, (∀ τ, compAt θ τ x' = cplxO (sS τ) (sT τ) (compAt θ τ x)) → ∀ w : WO S T, ∃ a : ℂ,
      HasDerivAt (fun t : ℝ => heisO ψ S T (realAd D.host.F t • x) f w) a 0 ∧
      HasDerivAt (fun t : ℝ => heisO ψ S T (realAd D.host.F t • x') f w) (Complex.I * a) 0 := by
  intro D ψ θ S T sS sT f hψ hθ hf hvac x x' hx' w
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hl := fun τ (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) => GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  let c : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun τ => compAt θ τ x
  let c' : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun τ => cplxO (sS τ) (sT τ) (c τ)
  obtain ⟨L1, L2, L3⟩ := dLine_sum hψ Finset.univ (fun τ => lineAt θ τ (c τ)) (fun τ => (hl τ _).1)
    (fun τ => (hl τ _).2.1) hf
  obtain ⟨M1, M2, M3⟩ := dLine_sum hψ Finset.univ (fun τ => lineAt θ τ (c' τ)) (fun τ => (hl τ _).1)
    (fun τ => (hl τ _).2.1) hf
  have e : ∀ t, realAd D.host.F t • x = (∑ τ, lineAt θ τ (c τ)) t :=
    realAd_smul_eq_sum hθ hσ c x (fun τ => rfl)
  have e' : ∀ t, realAd D.host.F t • x' = (∑ τ, lineAt θ τ (c' τ)) t :=
    realAd_smul_eq_sum hθ hσ c' x' hx'
  have hd := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ L1 L2 hf).1 w
  have hd' := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ M1 M2 hf).1 w
  refine ⟨GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c τ)) f w, ?_, ?_⟩
  · simp only [e]
    exact hd
  · have key : GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c' τ)) f w =
        Complex.I * GlobalTheory.WeilVacMove.dLine ψ S T (∑ τ, lineAt θ τ (c τ)) f w := by
      rw [L3, M3, Finset.sum_apply, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have h : GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c τ)) f w +
          Complex.I * GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c' τ)) f w = 0 := congrFun (hvac τ (c τ)) w
      linear_combination (-Complex.I) * h + GlobalTheory.WeilVacMove.dLine ψ S T (lineAt θ τ (c' τ)) f w * Complex.I_sq
    simp only [e']
    rw [← key]
    exact hd'

end GlobalTheory.FockLineJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GodementSummableHeightRpowRepresentatives
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem summable_height_rpow_reps : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ T, IsRepsJ σ J X T → ∀ (g : GAd σ J) (e : ℝ), ((n : ℝ) - (r + 1)) < e → Summable fun t : T => h (t.1.1 * g) ^ e := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hD T hT g e he
  obtain ⟨m, Z, J₀, hFr⟩ := GlobalTheory.SphEis.exists_fr_of_isotropic F E σ hD.cm n J hD.herm (r + 1) X Y hD.witt.xx hD.witt.yy hD.witt.xy
  have hinv := (_root_.GlobalTheory.ResidueEisenstein.reps_perm F E σ n J r X Y L a h hD T hT).2.2.1
  have hnn : ∀ x, 0 ≤ h x := by
    intro x
    obtain ⟨p, β, hp, k, hk, rfl⟩ := hD.iwa x
    rw [hD.ht p β hp k hk]
    exact NNReal.coe_nonneg _
  have hS := GlobalTheory.T.summable_height_rpow_parabolicCosets F E σ n J (r + 1) m X Y Z J₀ hFr L a hD.lat hD.iwa (fun x => Real.toNNReal (h x))
    (fun p β hp k hk => by simp only [hD.ht p β hp k hk, Real.toNNReal_coe]) g e (by push_cast; linarith)
  have hXinv : adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    simp only [adMat, ← Matrix.map_mul, hFr.dc, Matrix.map_one _ (map_zero _) (map_one _)]
  have hsc : ∀ p ∈ GlobalTheory.UAut.parFlag σ J X (fun _ => 0), ∃ β : GL (Fin (r + 1)) (AF F ⊗[F] E), ScalesBy σ J X p β := by
    intro p hp
    obtain ⟨⟨B, -, hB⟩, B', -, hB'⟩ := hp
    have hX : adMat F X = adMat F X * (B * B') := by
      calc adMat F X = (matHom _ σ J p).1 * ((matHom _ σ J p⁻¹).1 * adMat F X) := by
            rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mul]
        _ = adMat F X * (B * B') := by rw [hB', ← Matrix.mul_assoc, hB, Matrix.mul_assoc]
    have h1 : B * B' = 1 := by
      calc B * B' = adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * adMat F X * (B * B') := by rw [hXinv, Matrix.one_mul]
        _ = 1 := by rw [Matrix.mul_assoc, ← hX, hXinv]
    have h2 : B' * B = 1 := by
      first | exact mul_eq_one_comm.mp h1 | exact Matrix.mul_eq_one_comm.mp h1 | exact (Matrix.mul_eq_one_comm).1 h1 | exact Matrix.nonsing_inv_mul_cancel_left _ _ h1
    exact ⟨⟨B, B', h1, h2⟩, hB⟩
  let φ : T → GlobalTheory.Eis.Cosets (GlobalTheory.UAut.parFlag σ J X (fun _ => 0)) (ratPts σ J) := fun t =>
    GlobalTheory.AutomorphicL2Unitary.mk _ t.1
  have hrel : ∀ t : T, ∃ γ : ((GlobalTheory.UAut.parFlag σ J X (fun _ => 0)).subgroupOf (ratPts σ J)),
      (γ : ratPts σ J) * (φ t).out = t.1 :=
    fun t => GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 (Quotient.out_eq (φ t))
  have hinj : Function.Injective φ := by
    intro t t' htt
    obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 htt
    have hγP : ((γ : ratPts σ J) : GAd σ J) ∈ GlobalTheory.UAut.parFlag σ J X (fun _ => 0) := Subgroup.mem_subgroupOf.1 γ.2
    obtain ⟨β, hβ⟩ := hsc _ hγP
    refine Subtype.ext ((hT t'.1).unique ⟨t.2, β, ?_⟩ ⟨t'.2, 1, ?_⟩)
    · rw [← eq_mul_inv_of_mul_eq hγ]; exact hβ
    · simp [ScalesBy]
  refine (hS.comp_injective hinj).congr fun t => ?_
  obtain ⟨γ, hγ⟩ := hrel t
  have hγP : ((γ⁻¹ : ratPts σ J) : GAd σ J) ∈ GlobalTheory.UAut.parFlag σ J X (fun _ => 0) :=
    Subgroup.mem_subgroupOf.1 (inv_mem γ.2)
  obtain ⟨β, hβ⟩ := hsc _ hγP
  have hout : ((φ t).out : ratPts σ J) = γ⁻¹ * t.1 := eq_inv_mul_of_mul_eq hγ
  simp only [Function.comp, Real.coe_toNNReal _ (hnn _)]
  rw [hout, Subgroup.coe_mul, mul_assoc]
  refine congrArg (· ^ e) (hinv _ ⟨?_, β, Subgroup.mem_top _, ?_⟩ _)
  · exact SetLike.coe_mem _
  · exact hβ

end GlobalTheory.ResidueEisenstein
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorLocalVanishStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_tensor_local_vanish : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    IsCMExt F E σ → ∀ {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E)
    (JB : Matrix (Fin n) (Fin n) E), (∀ i j, σ (JA j i) = JA i j) → (∀ i j, σ (JB j i) = -JB i j) →
    ∀ (x u : Matrix (Fin m) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), x.map (piW τ) = 0 → u.map (piW (τ.comp σ)) = 0 →
    piW τ (hTens (cA σ) (incM F JA) (dbl (incM F JB)) x u) + piW (τ.comp σ) (hTens (cA σ) (incM F JA) (dbl (incM F JB)) x u) =
      ∑ k, ∑ l, (-(JA.map τ * x.map (piW (τ.comp σ)) * ((dbl JB).map τ)ᵀ)) k l * u.map (piW τ) k l := by
  first | exact @GlobalTheory.DblTrace.trace_pairing_dbl | exact GlobalTheory.DblTrace.trace_pairing_dbl | (intros; apply GlobalTheory.DblTrace.trace_pairing_dbl <;> assumption)
end

