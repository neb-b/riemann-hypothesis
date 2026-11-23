module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1732
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0531
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaUnramified
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaDer

theorem schr_comp_apply {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) (x : κ → R) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' Φ) x =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) * GlobalTheory.WeilM.schr ψ (w + w') Φ x := by
  have hh : ⅟(2 : R) + ⅟(2 : R) = 1 := by rw [← two_mul, mul_invOf_self]
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add, add_assoc]
  simp only [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * hh

theorem exists_equiv {A : Type} [CommRing A] {m k d : ℕ} {G H : Matrix (Fin m) (Fin m) A} (hHG : H * G = 1)
    (hGH : G * H = 1) (e : Fin k ≃ Fin d) :
    ∃ T : Matrix (Fin m) (Fin k) A ≃+ Matrix (Fin d) (Fin m) A,
      (∀ u, T u = uᵀ.submatrix e.symm id * G) ∧ ∀ x, T.symm x = ((x * H)ᵀ).submatrix id e := by
  refine ⟨{ toFun := fun u => uᵀ.submatrix e.symm id * G
            invFun := fun x => ((x * H)ᵀ).submatrix id e
            left_inv := fun u => ?_
            right_inv := fun x => ?_
            map_add' := fun u v => ?_ }, fun u => rfl, fun x => rfl⟩
  · ext i j
    simp [Matrix.mul_assoc, hGH]
  · simp [Matrix.transpose_submatrix, Matrix.submatrix_submatrix, Matrix.mul_assoc, hHG]
  · simp [Matrix.transpose_add, Matrix.submatrix_add, Matrix.add_mul]

private theorem rho_add_twisted_operators {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar R ℂ) (p q : W)
    (Φ : (κ → R) → ℂ) (z : κ → R) :
    co.rho ψ (p + q) Φ z = ψ (-(⅟(2 : R) * B p q)) * co.rho ψ p (co.rho ψ q Φ) z := by
  simp only [GlobalTheory.WeilM.Darboux.rho]
  rw [schr_comp_apply, ← co.form, map_add (f := _), ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel,
    AddChar.map_zero_eq_one, one_mul]

set_option maxHeartbeats 6400000 in
private theorem tendsto_add_smul_punctured_of_differentiableAt {D : D7} {n d m : ℕ} (u₀ : Matrix (Fin n) (Fin d) (AE D)) (e' : Fin d ≃ Fin m)
    (G : Matrix (Fin n) (Fin n) (AE D)) :
    Continuous fun t : ℝ => (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)ᵀ.submatrix e'.symm id * G := by
  have c0 : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F) := GlobalTheory.ThetaLineDeriv.continuous_realAd
  have c1 : Continuous fun t : ℝ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀ := c0.smul continuous_const
  exact (c1.matrix_transpose.matrix_submatrix _ _).matrix_mul continuous_const

private theorem fin_realAd_smul_eq_zero {D : D7} (t : ℝ) (a : AE D) :
    finPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • a) = 0 := by
  rw [Algebra.smul_def, map_mul]
  have h0 : finPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t)) = 0 := by
    show finPart D ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    have hs : sndA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) = 0 := rfl
    simp only [Formalism.L2.Theta.finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, hs,
      TensorProduct.zero_tmul]
  rw [h0, zero_mul]


set_option maxHeartbeats 1600000 in
theorem thO_pure_deriv {D : D7} (S X : HSp D) {d : ℕ} (e : Fin d ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (hBs : Bs.IsGood D.sp.cm.sig)
    (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    (hVJ : Vs.J = -S.gram) (hJW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (hV : ∀ i j, D.sp.cm.sig (Vs.J j i) = Vs.J i j)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (hM : M.IsGood Bs.ψ)
    (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ)
    (u₀ : Matrix (Fin S.rank) (Fin d) (AE D)) (g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d))
    (hact : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ u₀) g g₁)
    (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _) (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    ∃ L : ℝ →+ WO S X, Continuous L ∧ (∀ t, (L t).map (finPart D) = 0) ∧
      GlobalTheory.TripleRead.thO M Bs.ψ S.gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) =
        fun x => deriv (fun t : ℝ => heisO Bs.ψ S X (L t)
          (GlobalTheory.TripleRead.thO M Bs.ψ S.gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) x) 0 := by
  classical
  have hTR : NumberField.IsTotallyReal D.host.F := hBs.cm.1
  have hCh : IsCharAF D.host.F Bs.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hBs.std
  have hdet : IsUnit S.gram.det := isUnit_iff_ne_zero.mpr (gram_det_ne S)
  have hinc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram⁻¹ = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet]
    simp
  have hinc' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet]
    simp
  obtain ⟨T, hT, hTs⟩ := exists_equiv (A := AE D) hinc' hinc e
  have hpt : ∀ x, GlobalTheory.TripleRead.ptO S.gram e x = T.symm x := fun x => (hTs x).symm
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x | ∀ i, x i ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers D.host.F v} 1 :=
    (hvac.and hM.std).mono fun v h => h.1.trans h.2
  have hΦ := GlobalTheory.TensUniq.pure_mem_schA g φ hφ hstd
  have hΦ' := GlobalTheory.TensUniq.pure_mem_schA g₁ φ hφ hstd
  have hd : ∀ z, HasDerivAt (fun t : ℝ => M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ z) 0 :=
    fun z => hact _ (GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφ hstd) z

  have hG : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram)ᵀ := by
    ext i j
    have h1 := hV j i
    rw [hVJ] at h1
    simp only [Matrix.neg_apply, map_neg, neg_inj] at h1
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, inclR, h1]
  have h2 : (⅟(2 : AF D.host.F)) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [show (2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) 2 from (map_ofNat _ 2).symm, ← map_mul]
    norm_num
  have hphase : ∀ (x : WO S X) (q : Matrix (Fin S.rank) (Fin d) (AE D)),
      symplOH S X x (T q) = ⅟(2 : AF D.host.F) * GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (T.symm x) q := by
    intro x q
    conv_lhs => rw [← T.apply_symm_apply x]
    have hh := GlobalTheory.SquareAgree.hTens_transpose_mul (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e.symm
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram) (inclR (F := D.host.F) (AF D.host.F) D.host.xi0) hinc' hG (T.symm x) q
    rw [← hT, ← hT] at hh
    have hs := GlobalTheory.WeilSchrodinger.symp_eq_symplO D S X (X.gramᵀ) (D.host.xi0 • S.gram⁻¹) 1 rfl (by rw [one_smul])
      (T (T.symm x)) (T q)
    simp only [symplOH, ← hs, h2, GlobalTheory.WeilM.symp, one_mul, neg_one_mul, map_neg]
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J = -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram := by
      ext i j
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hVJ]
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J = inclR (F := D.host.F) (AF D.host.F) D.host.xi0 • Matrix.reindex e.symm e.symm (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram)ᵀ := by
      ext i j
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hJW, Matrix.reindex_apply, map_mul]
    have e3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) = inclR (F := D.host.F) (AF D.host.F) D.host.xi0 • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram⁻¹ := by
      ext i j
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, map_mul]
    have e4 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram)ᵀ := by
      ext i j
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [e4, e3, hh, e1, e2, map_neg]

  let ln : ℝ →+ Matrix (Fin S.rank) (Fin d) (AE D) :=
    AddMonoidHom.mk' (fun t => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)
      (fun s t => by simp only [GlobalTheory.ThetaLineDeriv.realAd_add, add_smul])
  refine ⟨T.toAddMonoidHom.comp ln, ?_, ?_, ?_⟩
  · have hfun : (fun t => (T.toAddMonoidHom.comp ln) t) =
        fun t => (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)ᵀ.submatrix e.symm id * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F S.gram :=
      funext fun t => hT _
    show Continuous fun t => (T.toAddMonoidHom.comp ln) t
    rw [hfun]
    exact tendsto_add_smul_punctured_of_differentiableAt u₀ e _
  · intro t
    show (T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)).map (finPart D) = 0
    rw [hT, Matrix.map_mul]
    have hz : ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)ᵀ.submatrix e.symm id).map (finPart D) = 0 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, fin_realAd_smul_eq_zero,
        Matrix.zero_apply]
    rw [hz, Matrix.zero_mul]
  · funext x
    have hfun : (fun t : ℝ => heisO Bs.ψ S X ((T.toAddMonoidHom.comp ln) t)
        (GlobalTheory.TripleRead.thO M Bs.ψ S.gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) x) =
        fun t => GlobalTheory.WeilM.thetaSum D.host.F (M.co.rho Bs.ψ (T.symm x)
          (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ))) := by
      funext t
      show heisO Bs.ψ S X (T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀)) _ x = _
      simp only [heisO, GlobalTheory.TripleRead.thO, hpt, map_add (f := _), T.symm_apply_apply]
      rw [show M.co.rho Bs.ψ (T.symm x + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) =
        fun z => Bs.ψ (-(⅟(2 : AF D.host.F) * GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) (T.symm x)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀))) *
          M.co.rho Bs.ψ (T.symm x) (M.co.rho Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u₀) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) z
        from funext (rho_add_twisted_operators M.co Bs.ψ _ _ _)]
      simp only [GlobalTheory.WeilM.thetaSum]
      rw [tsum_mul_left, ← mul_assoc, ← AddChar.map_add_eq_mul, hphase, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]
    have hder := GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_schr Bs.ψ hTR hCh (M.co.e u₀) hΦ hΦ' (by
      simpa only [GlobalTheory.WeilM.Darboux.rho, map_smul] using hd) (M.co.e (T.symm x))
    rw [hfun]
    simp only [GlobalTheory.WeilM.Darboux.rho, map_smul]
    rw [hder.deriv]
    simp only [GlobalTheory.TripleRead.thO, hpt, GlobalTheory.WeilM.Darboux.rho]

end GlobalTheory.ThetaDer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulOfMapsInlMemS
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.SmallDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem ofMaps_inlS (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) (p : Fin (spW₁ G i j).rank)
    (k : Fin (spV G i j).rank) : ofMaps t e x p (e (.inl k)) = GlobalTheory.BigDat.divG (spW₁ G i j) x.1 k p := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]

theorem ofMaps_inrS (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) (p : Fin (spW₁ G i j).rank)
    (k : Fin (spV₁ G i j).rank) : ofMaps t e x p (e (.inr k)) = cA D (GlobalTheory.BigDat.divG (spV₁ G i j) (-x.2) p k) := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]

theorem ofMaps_genA (t : T) (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spW₁ G i j).rank → D.host.E)
    (r : Fin (spV G i j).rank → D.host.E) :
    ofMaps t e (Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (spW₁ G i j).gram k j'), 0) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) (Sum.elim (a • r) 0 ∘ e.symm)) := by
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inlS t e _ p k).trans ((GlobalTheory.BigDat.divG_gen (spW₁ G i j) β a s r k p).trans ?_)
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, mul_comm]
    rfl
  · refine (ofMaps_inrS t e _ p k).trans ?_
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, neg_zero,
      GlobalTheory.BigDat.divG_zero, Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    exact map_zero _

theorem ofMaps_genB (t : T) (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spV₁ G i j).rank → D.host.E)
    (r : Fin (spW₁ G i j).rank → D.host.E) :
    ofMaps t e (0, Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (negSp (spV₁ G i j)).gram k j')) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star r) (Sum.elim 0 (star (a • star s)) ∘ e.symm)) := by
  have hneg : -(Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (negSp (spV₁ G i j)).gram k j') :
      Matrix _ _ (AE D)) = Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (spV₁ G i j).gram k j') := by
    ext p q
    simp only [Matrix.neg_apply, of_apply, negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_neg,
      TensorProduct.tmul_neg]
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inlS t e _ p k).trans ((congrFun (congrFun (GlobalTheory.BigDat.divG_zero (spW₁ G i j)) k) p).trans ?_)
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl,
      Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    rfl
  · refine (ofMaps_inrS t e _ p k).trans ?_
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, hneg,
      GlobalTheory.BigDat.divG_gen]
    change β ⊗ₜ[D.host.F] star (a * r p * star (s k)) = β ⊗ₜ[D.host.F] (star (r p) * star (a * star (s k)))
    rw [← star_mul']
    congr 2
    ring

theorem smul_ofMaps_inl_memS {t : T} {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} (h : IsDoublyCompatible t i j e Bs Γ X) (v : Pl D.host.F) {x : HomA G t i j}
    (hx : x ∈ latA G t i j) : GlobalTheory.LatVac.liftV v 1 • ofMaps t e (x, 0) ∈ latAtV Γ.V' Γ.W v := by
  refine GlobalTheory.BigDat.map_mem_of_closure ((DistribSMul.toAddMonoidHom (PtS G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps t e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inl _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, r, hr, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V' Γ.W v) (ofMaps_genA t e (pairA _ 0 α) a s r)).mpr
    (GlobalTheory.BigDat.one_smul_gen_mem _ _ v hα (h.2.ge (GlobalTheory.BigDat.star_mem_conjSub hs))
      (h.1.2.1.ge (GlobalTheory.BigDat.pair_mem e (GlobalTheory.BigDat.smul_mem_scLat_of_mem ha hr) (zero_mem _))))

theorem smul_ofMaps_inr_memS {t : T} {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} (h : IsDoublyCompatible t i j e Bs Γ X) (v : Pl D.host.F) {x : HomB G i j}
    (hx : x ∈ latB G i j) : GlobalTheory.LatVac.liftV v 1 • ofMaps t e (0, x) ∈ latAtV Γ.V' Γ.W v := by
  refine GlobalTheory.BigDat.map_mem_of_closure ((DistribSMul.toAddMonoidHom (PtS G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps t e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inr _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, r, hr, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V' Γ.W v) (ofMaps_genB t e (pairA _ 0 α) a s r)).mpr
    (GlobalTheory.BigDat.one_smul_gen_mem _ _ v hα (h.2.ge (GlobalTheory.BigDat.star_mem_conjSub hr))
      (h.1.2.1.ge (GlobalTheory.BigDat.pair_mem e (zero_mem _)
        (GlobalTheory.BigDat.star_mem_conjSub (GlobalTheory.BigDat.smul_mem_scLat_of_mem ha (GlobalTheory.BigDat.star_mem_conjSub hs))))))

theorem latPtS_le_latAtV : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E), GlobalTheory.FlipMatch.IsDoublyCompatible t i j e Bs Γ X →
    ∀ v : Pl D.host.F, ∀ u ∈ GlobalTheory.SmallDat.latPtS t e v, u ∈ latAtV Γ.V' Γ.W v := by
  intro D T L sc G t i j e Bs Γ X h v u hu
  obtain ⟨hat, h1, h2⟩ := hu
  have e1 : GlobalTheory.LatVac.liftV v 1 • u = u := by
    have := hat (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  have e2 : u = ofMaps t e (mapA t e u, 0) + ofMaps t e (0, mapB e u) :=
    ((ofMaps_maps t e u).symm.trans (congrArg (ofMaps t e) (Prod.ext (add_zero _).symm (zero_add _).symm))).trans
      (map_add (maps t e).symm (mapA t e u, 0) (0, mapB e u))
  have e3 := add_mem (smul_ofMaps_inl_memS h v h1) (smul_ofMaps_inr_memS h v h2)
  rwa [← smul_add, ← e2, e1] at e3

end GlobalTheory.SmallDat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormOffIdempotentPartOrthogonalHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.IdemOffOrth

theorem symplO_compl_half : ∀ (D : D7) (S T : HSp D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ w x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → symplO S T ((1 - e - cA D e) • w) x = 0 := by
  intro D S T P e he w x hx
  have h1 : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have h2 : e * cA D e = 0 := he.2
  have c1 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have hz : symplO S T (0 : WO S T) x = 0 := by
    have := GlobalTheory.BigDat.symplO_cA_smul S T (0 : AE D) w x
    rw [map_zero, zero_smul, zero_smul, GlobalTheory.BigDat.symplO_zero_right'] at this
    exact this.symm
  rcases hx with hx | hx
  · have hxe : x = cA D (cA D e) • x := by
      rw [GlobalTheory.DualPairCheck.cA_cA]; exact (GlobalTheory.BigDat.smul_of_isHalf hx).symm
    rw [hxe, GlobalTheory.BigDat.symplO_cA_smul, smul_smul]
    have : cA D e * (1 - e - cA D e) = 0 := by linear_combination -c1 - (mul_comm e (cA D e) ▸ h2 : cA D e * e = 0)
    rw [this, zero_smul]; exact hz
  · rw [← GlobalTheory.BigDat.smul_of_isHalf hx, GlobalTheory.BigDat.symplO_cA_smul, smul_smul]
    have : e * (1 - e - cA D e) = 0 := by linear_combination -h1 - h2
    rw [this, zero_smul]; exact hz

end GlobalTheory.IdemOffOrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaValueSiegelTorusElementLeSobolevSeminormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaValue_siegelTorusElement_le_sobolevSeminorm : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (r : ℕ)
    (Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E) (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf)
    (c : ℝ) (hc : 0 < c) (K₀ : Set (WO M X)) (hK₀ : K₀ ∈ nhds (0 : WO M X)) (hK₀c : IsCompact K₀)
    (μ : Measure (WO (sgn ε M) X)) (𝓕 : Set (WO (sgn ε M) X)) (hμ : IsCovolOne (ratL X (sgn ε M)) μ 𝓕),
    ∃ (k A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO M X → ℂ, IsThetaFunO ψ (sgn ε M) X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ (sgn ε M) X (n • u) Ψ = Ψ) →
      ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a →
        ‖ω (a, 1) Ψ 0‖ ≤ C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Ψ).toReal *
          ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) := by
  first | exact @GlobalTheory.SiegelTorusTheta.torus_bound | exact GlobalTheory.SiegelTorusTheta.torus_bound | (intros; apply GlobalTheory.SiegelTorusTheta.torus_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistedDataOffBaseLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.RowEx.DatTw

open Formalism.L2.Host

theorem not_two_primes {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (h1 : (p : R) ∈ P) (h2 : (q : R) ∈ P) : False := by
  obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]
  have e := congrArg (Int.cast : ℤ → R) huv
  push_cast at e
  rw [← e]
  exact P.add_mem (P.mul_mem_left _ h1) (P.mul_mem_left _ h2)

theorem unrAt_mul {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v)
    (h' : χ'.UnrAt v) : (χ * χ').UnrAt v := fun x hx => by
  change χ.loc v x * χ'.loc v x = 1
  rw [h x hx, h' x hx, one_mul]

theorem unrAt_one {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).UnrAt v := fun _ _ => rfl

variable {R : Ranks} (H : Host R)

theorem unrAt_of_isTwist {S : Set ℕ} (hS : GlobalTheory.EX.DC.q0H H ∈ S) {ψ : HChar H.E} (hψ : Chr.IsTwist H S ψ)
    {v : HeightOneSpectrum (𝓞 H.E)} (hv : ((GlobalTheory.EX.DC.q0H H : ℕ) : 𝓞 H.E) ∈ v.asIdeal) : ψ.UnrAt v := by
  by_contra h
  obtain ⟨-, hpr, -, hnot⟩ := hψ.2.2.2 v h
  by_cases e : Ideal.absNorm v.asIdeal = GlobalTheory.EX.DC.q0H H
  · exact hnot (e ▸ hS)
  · exact not_two_primes v.asIdeal hpr (GlobalTheory.EX.DC.globalTwisting_spec_fact H).1 e (Ideal.absNorm_mem _) hv

theorem not_overP_pde {v : HeightOneSpectrum (𝓞 H.E)} (hv : ((GlobalTheory.EX.DC.q0H H : ℕ) : 𝓞 H.E) ∈ v.asIdeal) :
    ¬ OverP H H.pde v ∧ ¬ OverP H H.pde' v :=
  ⟨fun h => not_two_primes v.asIdeal H.pde_prime (GlobalTheory.EX.DC.globalTwisting_spec_fact H).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' H).1.symm h hv,
    fun h => not_two_primes v.asIdeal H.pde'_prime (GlobalTheory.EX.DC.globalTwisting_spec_fact H).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' H).2.symm h hv⟩

theorem unrAt_of_mem_set {B : Base} {f : Fr B.toPre} {T : TwDat B} {ξ : HChar B.host.E} (h : ξ ∈ T.set f)
    {v : HeightOneSpectrum (𝓞 B.host.E)} (hv : ((GlobalTheory.EX.DC.q0H B.host : ℕ) : 𝓞 B.host.E) ∈ v.asIdeal) : ξ.UnrAt v := by
  have hd := not_overP_pde B.host hv
  have hdel : f.del.UnrAt v := f.isDel.unr v hd.1
  have hdel' : f.del'.UnrAt v := f.isDel'.unr v hd.2
  simp only [TwDat.set, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at h
  rcases h with (rfl | rfl | rfl) | ⟨w, rfl⟩
  · exact unrAt_one v
  · exact hdel
  · exact hdel'
  · unfold TwDat.xiTw
    refine unrAt_mul ?_ (unrAt_of_isTwist B.host ?_ (T.psi_tw w) hv)
    · split_ifs
      · exact hdel'
      · exact hdel
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

end GlobalTheory.RowEx.DatTw

theorem GlobalTheory.RowEx.twisted_data_off_base_level : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok)
    (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), GlobalTheory.RowEx.TwistPlacesOffPrimeQZero z.R.toLevCh ∧ z.R.C = Fr.at (w.st Z) f ∧
      (T.set f).Finite ∧ ∀ t, z.R.xiH t ∈ T.set f := by
  intro B f T w Z hX Wt z
  have hmem : ∀ t, z.R.xiH t ∈ T.set f := fun t => by
    rw [z.lev.xiH t, ← w.xi_range]
    exact ⟨_, rfl⟩
  refine ⟨fun t PP hPP hq => ?_, ?_, ?_, hmem⟩
  · exact (z.lev.is.Q_ram t PP).2 (Or.inl hPP) (GlobalTheory.RowEx.DatTw.unrAt_of_mem_set (hmem t) hq)
  · rw [z.lev.C, w.C_eq]
  · rw [← w.xi_range]
    exact Set.finite_range _
end

