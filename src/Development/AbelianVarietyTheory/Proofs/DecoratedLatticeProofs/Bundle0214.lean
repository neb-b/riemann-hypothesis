module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnnihilationOperatorSchroedingerFunctionsDoubled
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnnAnnih

theorem blockMatrix_swap_mul_top_rows_eq_bottom_rows {n k : ℕ} (M : Matrix (Fin (n + n)) (Fin k) ℂ) :
    (blk4 (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0 * M).submatrix (fun i => finSumFinEquiv (Sum.inl i)) id =
      M.submatrix (fun i => finSumFinEquiv (Sum.inr i)) id := by
  have hM : M = (M.submatrix finSumFinEquiv id).submatrix finSumFinEquiv.symm id := by ext; simp
  rw [hM, blk4, Matrix.submatrix_mul_equiv]
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem row_sub_mul {a b k l : ℕ} (M : Matrix (Fin a) (Fin k) ℂ) (N : Matrix (Fin k) (Fin l) ℂ) (r : Fin b → Fin a) :
    M.submatrix r id * N = (M * N).submatrix r id := by
  ext i j
  simp [Matrix.mul_apply]

variable {D : D7}

theorem qX_mul_stdInv (A : HSp D) (μ : D.host.E) (hμ : IsSkew μ) (s : RealMat (dblSp A)) (hs : IsStdInv A μ s)
    (τ : D.what₂.Tau) :
    (dblDec A).qX.map (tauE D τ) * s τ = ((‖tauE D τ μ‖ : ℂ)⁻¹) • (dblDec A).qY.map (tauE D τ) := by
  obtain ⟨-, hdet, hinv⟩ := _root_.GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ
  have hRT : (Tm A μ)⁻¹ * Tm A μ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hTR : Tm A μ * (Tm A μ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h1 : ((Tm A μ)⁻¹).map (tauE D τ) * (Tm A μ).map (tauE D τ) = 1 := by
    rw [← Matrix.map_mul, hRT, Matrix.map_one _ (tauE D τ).map_zero (tauE D τ).map_one]
  have h2 : (Tm A μ).map (tauE D τ) * ((Tm A μ)⁻¹).map (tauE D τ) = 1 := by
    rw [← Matrix.map_mul, hTR, Matrix.map_one _ (tauE D τ).map_zero (tauE D τ).map_one]
  have hqX : (dblDec A).qX.map (tauE D τ) =
      (((Tm A μ)⁻¹).map (tauE D τ)).submatrix (fun i => finSumFinEquiv (Sum.inl i)) id := by
    rw [hinv]; ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl]
  have hqY : (μ⁻¹ • (dblDec A).qY).map (tauE D τ) =
      (((Tm A μ)⁻¹).map (tauE D τ)).submatrix (fun i => finSumFinEquiv (Sum.inr i)) id := by
    rw [hinv]; ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromRows_apply_inr]
  have hμ0 : tauE D τ μ ≠ 0 := (map_ne_zero (tauE D τ)).2 hμ.1
  have hn0 : (‖tauE D τ μ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hμ0)
  have hsτ : s τ * (Tm A μ).map (tauE D τ) = (Tm A μ).map (tauE D τ) * stdInv A.rank μ τ := hs τ
  have hsR : ((Tm A μ)⁻¹).map (tauE D τ) * s τ = stdInv A.rank μ τ * ((Tm A μ)⁻¹).map (tauE D τ) := by
    calc ((Tm A μ)⁻¹).map (tauE D τ) * s τ
          = ((Tm A μ)⁻¹).map (tauE D τ) * (s τ * ((Tm A μ).map (tauE D τ) * ((Tm A μ)⁻¹).map (tauE D τ))) := by
          rw [h2, Matrix.mul_one]
      _ = ((Tm A μ)⁻¹).map (tauE D τ) * ((Tm A μ).map (tauE D τ) * stdInv A.rank μ τ) *
            ((Tm A μ)⁻¹).map (tauE D τ) := by
          rw [← Matrix.mul_assoc (s τ), hsτ]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hqX, row_sub_mul, hsR, stdInv, Matrix.smul_mul]
  have hb := blockMatrix_swap_mul_top_rows_eq_bottom_rows (((Tm A μ)⁻¹).map (tauE D τ))
  rw [← hqY] at hb
  ext i j
  have hij := congrFun (congrFun hb i) j
  simp only [Matrix.submatrix_apply, Matrix.smul_apply, id] at hij ⊢
  rw [hij]
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
  field_simp

end GlobalTheory.StdUnnAnnih

namespace GlobalTheory.StdUnnAnnih

theorem re_imaginary_mul_neg_I_div_mul {a w : ℂ} (hre : a.re = 0) (him : 0 < a.im) (r : ℝ) :
    (a * (-(Complex.I / (r : ℂ))) * w).re = ‖a‖ / r * w.re := by
  have hn : ‖a‖ = a.im := by
    rw [Complex.norm_def, Complex.normSq_apply, hre, zero_mul, zero_add, Real.sqrt_mul_self him.le]
  have ha : a = (a.im : ℂ) * Complex.I := Complex.ext (by simp [hre]) (by simp)
  rw [hn, ha]
  have : (a.im : ℂ) * Complex.I * (-(Complex.I / (r : ℂ))) = ((a.im / r : ℝ) : ℂ) := by
    push_cast
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (-(a.im : ℂ) * (r : ℂ)⁻¹) * Complex.I_sq
  rw [this, Complex.re_ofReal_mul]
  simp

theorem annih_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ l : D.what₂.Tau → ℝ, (∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖) → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (X : Matrix (Fin B.rank) (Fin A.rank) ℂ), sch ψ A B ν 𝓨 (annih (heisO ψ (dblSp A) B) θ τ (cplxO (s' τ) (sB τ)) (X * (dblDec A).qX.map (tauE D τ)) f) = annS B l sB θ τ X (sch ψ A B ν 𝓨 f) := by
  intro D ψ hψ θ hθ A B ν 𝓨 hcov μ hμ s' sB hs hsB l hl f hf τ X
  have hJ : cplxO (s' τ) (sB τ) (X * (dblDec A).qX.map (tauE D τ)) =
      ((Complex.I / (‖tauE D τ μ‖ : ℂ)) • (sB τ * X)) * (dblDec A).qY.map (tauE D τ) := by
    unfold cplxO
    rw [Matrix.mul_assoc (sB τ), Matrix.mul_assoc X, qX_mul_stdInv A μ hμ s' hs τ, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← Matrix.mul_assoc, div_eq_mul_inv]
  set Y := (Complex.I / (‖tauE D τ μ‖ : ℂ)) • (sB τ * X) with hY
  have hd1 := GlobalTheory.OrientedHeis.theta_dRho (S := dblSp A) (T := B) hθ hψ τ (X * (dblDec A).qX.map (tauE D τ)) hf
  have hd2 := GlobalTheory.OrientedHeis.theta_dRho (S := dblSp A) (T := B) hθ hψ τ (Y * (dblDec A).qY.map (tauE D τ)) hf
  obtain ⟨-, hsm, -, hsmul⟩ := _root_.GlobalTheory.StdUnn.sch_linear D ψ hψ A B ν 𝓨 hcov _ _ hd2 hd2 Complex.I
  obtain ⟨-, -, hadd, -⟩ := _root_.GlobalTheory.StdUnn.sch_linear D ψ hψ A B ν 𝓨 hcov _ _ hd1 hsm 0
  funext x
  rw [annih, hJ, hadd, hsmul, Pi.add_apply, Pi.smul_apply, _root_.GlobalTheory.StdUnn.DiagDeriv.sch_dRho_diag D ψ hψ θ hθ A B ν 𝓨 hcov f hf τ X x,
    _root_.GlobalTheory.StdUnn.sch_dRho_dualHalf D ψ hψ θ hθ A B ν 𝓨 hcov f hf τ Y x]
  unfold annS linF
  congr 1
  obtain ⟨hss, hiso, -⟩ := hsB τ
  have hsG : (sB τ)ᴴ * gramAt D B τ = gramAt D B τ * sB τ := by
    calc (sB τ)ᴴ * gramAt D B τ = (sB τ)ᴴ * gramAt D B τ * (sB τ * sB τ) := by rw [hss, Matrix.mul_one]
      _ = gramAt D B τ * sB τ := by rw [← Matrix.mul_assoc, hiso]
  have htr : Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x) =
      -(Complex.I / (‖tauE D τ μ‖ : ℂ)) * Matrix.trace (Xᴴ * (gramAt D B τ * sB τ) * compAt θ τ x) := by
    rw [hY, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc Xᴴ, hsG]
    congr 1
    simp [Complex.conj_ofReal, div_eq_mul_inv]
  have key : (tauE D τ D.host.xi0 * Matrix.trace (Yᴴ * gramAt D B τ * compAt θ τ x)).re =
      |l τ| * (Matrix.trace (Xᴴ * (gramAt D B τ * sB τ) * compAt θ τ x)).re := by
    rw [htr, ← mul_assoc, re_imaginary_mul_neg_I_div_mul (Formalism.IndefR.Fock.CCR.realPlace_imaginaryGenerator_re_eq_zero D τ) (Formalism.L2.Theta.xi_zero_im_pos D τ), hl τ]
  rw [key, smul_eq_mul]
  push_cast
  linear_combination (-(4 : ℂ) * Real.pi * ((|l τ| : ℝ) : ℂ) *
    ((Matrix.trace (Xᴴ * (gramAt D B τ * sB τ) * compAt θ τ x)).re : ℂ) * sch ψ A B ν 𝓨 f x) * Complex.I_sq

end GlobalTheory.StdUnnAnnih
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChangeTensorConjugationInvolutiveOfInvolution
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.Conj

theorem baseChangeTensorConjugation_involutive_of_involution {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (e : R ⊗[F] E) : sigR R σ (sigR R σ e) = e := by
  induction e using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => simp [sigR, hσ]

theorem infinitePlaceComponent_tensorConjugation {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    compInf F E w (sigR (AF F) σ z) = sigR w.Completion σ (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => simp [compInf, sigR]

theorem mul_eq_conj_mul_of_invertible_cancel {R : Type*} [Ring R] {P Pi F X K : R} (h1 : P * Pi = 1)
    (h : Pi * F * X = (Pi * K * P) * (Pi * F)) : F * X = K * F := by
  have := congrArg (P * ·) h
  simp only [← mul_assoc, h1, one_mul] at this
  rw [this, mul_assoc K P Pi, h1, mul_one]

theorem eq_inv_conj_of_intertwine {R : Type*} [Ring R] {Fi F X K : R} (h1 : Fi * F = 1) (h : F * X = K * F) :
    X = Fi * K * F := by
  rw [mul_assoc, ← h, ← mul_assoc, h1, one_mul]

variable {D : D7}

theorem matHom_chart_conj (A : HSp D) (μ : D.host.E) (κ : GA D (dblSp A) ≃* G D A.rank) (hκ : IsChart A μ κ)
    (Fr : GL (Fin (A.rank + A.rank)) (AE D)) (p : GA D (dblSp A))
    (hp : mt (dblSp A) p * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) = Fr.1) (k : GA D (dblSp A)) :
    GlobalTheory.AdelicU.matHom _ D.sp.cm.sig (Jst D A.rank) (κ (p⁻¹ * k * p)) =
      Fr⁻¹ * GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram k * Fr := by
  set P := GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram p
  set Kk := GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram k
  have hmt : ∀ g, mt (dblSp A) g = (GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram g).1 := fun _ => rfl
  have hT : (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) = (P⁻¹).1 * Fr.1 := by
    rw [← hp, hmt, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have h := hκ (p⁻¹ * k * p)
  have hm : GlobalTheory.AdelicU.matHom (n := A.rank + A.rank) _ D.sp.cm.sig (dblSp A).gram (p⁻¹ * k * p) = P⁻¹ * Kk * P := by
    rw [map_mul, map_mul, map_inv]
  rw [hmt, hm, hT] at h
  change (P⁻¹).1 * Fr.1 * mat (κ (p⁻¹ * k * p)) = (P⁻¹ * Kk * P).1 * ((P⁻¹).1 * Fr.1) at h
  apply Units.ext
  have h2 : Fr.1 * mat (κ (p⁻¹ * k * p)) = Kk.1 * Fr.1 := by
    rw [Units.val_mul, Units.val_mul] at h
    exact mul_eq_conj_mul_of_invertible_cancel (P := P.1) (Units.mul_inv P) h
  change mat (κ (p⁻¹ * k * p)) = _
  rw [Units.val_mul, Units.val_mul]
  exact eq_inv_conj_of_intertwine (Units.inv_mul Fr) h2

theorem mem_KAd_iff_of_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (Q J : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (a b : GL (Fin n) (AF F ⊗[F] E)) (hb : IsLatticeFrame L b)
    (hab : ∀ w, Formalism.UG.bc (compInf F E w) b = Formalism.UG.bc (compInf F E w) a)
    (M M' : GL (Fin (n + n)) (AF F ⊗[F] E)) (u r : (AF F ⊗[F] E)ˣ)
    (hM' : ∀ v i j, compFin F E v (M'.1 i j) ∈ intLoc F E v ∧ compFin F E v ((M'⁻¹).1 i j) ∈ intLoc F E v)
    (hMu : M.1 = (u : AF F ⊗[F] E) • M'.1)
    (hMM : ∀ w, (Formalism.UG.cT (sigR (AF F) σ) M.1 * M.1).map (compInf F E w) = compInf F E w r • 1)
    (k : GAd σ Q) (g : GAd σ J)
    (hg : GlobalTheory.AdelicU.matHom _ σ J g = (blkGL finSumFinEquiv (b, b) * M)⁻¹ * GlobalTheory.AdelicU.matHom _ σ Q k *
      (blkGL finSumFinEquiv (b, b) * M)) :
    k ∈ KAd σ Q L a ↔ g ∈ levelAll σ J (stdLattice E (n + n)) 1 := by
  rw [mem_KAd, mem_levelAll]
  refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)
  · rw [GlobalTheory.Doubling.KFin, stabLoc, stabLoc, Subgroup.mem_comap, Subgroup.mem_comap, matHom_proj, matHom_proj, hg,
      map_mul (Formalism.UG.bc (compFin F E v)), map_mul (Formalism.UG.bc (compFin F E v)) _ (GlobalTheory.AdelicU.matHom _ σ Q k), map_inv]
    exact _root_.GlobalTheory.StdUnn.StabFin.mem_stab_iff F E (n + n) _ _ M M' u (isLatticeFrame_dbl hb) hM' hMu v _
  · have hc : Formalism.UG.cT (sigR w.Completion σ) (Formalism.UG.bc (compInf F E w) M).1 * (Formalism.UG.bc (compInf F E w) M).1 =
        ((Units.map (compInf F E w : AF F ⊗[F] E →* w.Completion ⊗[F] E) r : (w.Completion ⊗[F] E)ˣ) :
          w.Completion ⊗[F] E) • 1 := by
      have h := hMM w
      rw [Matrix.map_mul] at h
      refine Eq.trans ?_ h
      congr 1
      ext i j
      exact (infinitePlaceComponent_tensorConjugation σ w (M.1 j i)).symm
    rw [KArch, mem_stabArch, mem_stabArch, matHom_projArch, matHom_projArch, hg,
      _root_.GlobalTheory.StdUnn.mem_UJ_one_iff_conj_similitude _ _ (baseChangeTensorConjugation_involutive_of_involution _ σ hσ) _ _ _ _ hc]
    simp only [map_mul, map_inv, map_one, bc_blkGL, hab w, inv_one, one_mul, mul_one, mul_inv_rev, mul_assoc]

theorem isConj_of_frame : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (a b : GL (Fin A.rank) (AE D)), IsLatticeFrame (frameLat A) b → (∀ w, Formalism.UG.bc (compInf D.host.F D.host.E w) b = Formalism.UG.bc (compInf D.host.F D.host.E w) a) → ∀ (M M' : GL (Fin (A.rank + A.rank)) (AE D)) (u : (AE D)ˣ), IntGL M' → M.1 = (u : AE D) • M'.1 → (∀ w, (adj M.1 * M.1).map (compInf D.host.F D.host.E w) = compInf D.host.F D.host.E w (2 * u * cA D u) • 1) → ∀ p : siegel A, mt (dblSp A) p * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) = (blkGL finSumFinEquiv (b, b) * M).1 → IsConj A a κ p := by
  intro D A μ _ κ hκ a b hb hab M M' u hM' hMu hMM p hp k
  have h2 : IsUnit (2 : AE D) := by
    have := (IsUnit.mk0 (2 : D.host.E) two_ne_zero).map (incA D)
    rwa [map_ofNat] at this
  have hr : IsUnit (2 * (u : AE D) * cA D u) := (h2.mul u.isUnit).mul (u.isUnit.map (cA D))
  have hg := matHom_chart_conj A μ κ hκ (blkGL finSumFinEquiv (b, b) * M) p hp k
  have hMM' : ∀ w, (Formalism.UG.cT (cA D) M.1 * M.1).map (compInf D.host.F D.host.E w) =
      compInf D.host.F D.host.E w hr.unit • 1 := hMM
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have key := mem_KAd_iff_of_conj (n := A.rank) D.sp.cm.sig hσ (dblSp A).gram (Jst D A.rank) (frameLat A) a b hb hab
    M M' u hr.unit (fun v i j => ⟨hM'.1 i j v, hM'.2 i j v⟩) hMu hMM' k (κ ((p : GA D (dblSp A))⁻¹ * k * p)) hg
  have e : K D A.rank = levelAll D.sp.cm.sig (Jst D A.rank) (stdLattice D.host.E (A.rank + A.rank)) 1 := rfl
  rw [e]
  exact key

end GlobalTheory.StdUnn.Conj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupHaarIsMulRightInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesUnimod

theorem besGrp_isMulRightInvariant : ∀ (D : D7) (V V₀ A L : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L)
    (μ : Measure (besGrp d o)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  intro D V V₀ A L ρ d o μ hμ
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4, j5, j6, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨ν, 𝓝, hν⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D V ρ d.e (isIsoSub_e d)
  obtain ⟨hνH, h𝓝, h𝓝1⟩ := hν
  have hNc : IsClosed (flagN d : Set (GA D V)) := GlobalTheory.Mem.TrueRecord.isClosed_NFlag V (isIsoSub_e d)
  let μA : Measure (GA D A) := Measure.haar
  have hHaar := ((GlobalTheory.MixPer.jacGrp_besGrp_haar D V V₀ A L ρ d o ν 𝓝 ⟨hνH, h𝓝, h𝓝1⟩).2.2 μA inferInstance)
  haveI : LocallyCompactSpace (flagN d) := hNc.locallyCompactSpace
  haveI : SecondCountableTopology (flagN d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hinj : Function.Injective fun γ : NFlagQ V d.e => (⟨γ.1.1, γ.2⟩ : GQ V) :=
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h))
  haveI : Countable (NFlagQ V d.e) := hinj.countable
  haveI : ν.IsMulRightInvariant :=
    GlobalTheory.SemiHaar.rightInv_of_fd (NFlagQ V d.e) ν h𝓝 (by rw [h𝓝1]; exact ENNReal.one_ne_top)
  haveI : μA.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D A μA inferInstance
  have hcA : Continuous (embA d o) := by
    have h1 : Continuous (fun h : GA D A => o.emb (h, 1)) := by
      have := o.continuous_emb
      fun_prop
    exact d.continuous_embed.comp h1
  have hnA : ∀ n ∈ flagN d, ∀ h, embA d o h * n * (embA d o h)⁻¹ ∈ flagN d := fun n hn h =>
    GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D V V₀ ρ d n hn (o.emb (h, 1))
  have hR := GlobalTheory.SemiHaar.semiMeas_rightInv (flagN d) (embA d o) hNc hcA hnA μA ν
  haveI : LocallyCompactSpace (besGrp d o) := by
    obtain ⟨e, -⟩ := GlobalTheory.SemiHaar.exists_homeo (flagN d) (embA d o) hnA hcA (GlobalTheory.BesProj.exists_continuous_proj D V V₀ A L ρ d o)
    exact e.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (besGrp d o) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨κ, k1, k2⟩ : ∃ κ : Measure (besGrp d o), κ.IsHaarMeasure ∧ κ.IsMulRightInvariant := ⟨_, hHaar, hR⟩
  rw [Measure.isMulLeftInvariant_eq_smul μ κ]
  infer_instance

end GlobalTheory.BesUnimod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSplitRealFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesSplit

theorem tens_ext {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (z w : (A × B) ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) w)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) w) : z = w := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [hz z, hz w, h1, h2]

theorem entry_eq {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (φ : R →+* R₁) (ψ : R →+* R₂)
    (hinj : ∀ z w, φ z = φ w → ψ z = ψ w → z = w) {n k m : ℕ} {M N K : Matrix (Fin n) (Fin n) R}
    (hi : M.map φ = N.map φ) (hf : M.map ψ = K.map ψ) (P : Matrix (Fin k) (Fin n) R) (Q : Matrix (Fin n) (Fin m) R)
    (i : Fin k) (j : Fin m) {c : R} (hN : (P * (N * Q)) i j = c) (hK : (P * (K * Q)) i j = c) :
    (P * (M * Q)) i j = c := by
  refine hinj _ _ ?_ ?_
  · have e : (P * (M * Q)).map φ = (P * (N * Q)).map φ := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hi]
    exact (congrFun (congrFun e i) j).trans (congrArg φ hN)
  · have e : (P * (M * Q)).map ψ = (P * (K * Q)).map ψ := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hf]
    exact (congrFun (congrFun e i) j).trans (congrArg ψ hK)

theorem mat_eq {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (φ : R →+* R₁) (ψ : R →+* R₂)
    (hinj : ∀ z w, φ z = φ w → ψ z = ψ w → z = w) {n k m : ℕ} {M N K : Matrix (Fin n) (Fin n) R}
    (hi : M.map φ = N.map φ) (hf : M.map ψ = K.map ψ) (P : Matrix (Fin k) (Fin n) R) (Q : Matrix (Fin n) (Fin m) R)
    {C : Matrix (Fin k) (Fin m) R} (hN : P * (N * Q) = C) (hK : P * (K * Q) = C) : P * (M * Q) = C :=
  Matrix.ext fun i j => entry_eq φ ψ hinj hi hf P Q i j (congrFun (congrFun hN i) j) (congrFun (congrFun hK i) j)

variable {D : D7}

def realPart (D : D7) : AE D →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

def finitePart (D : D7) : AE D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem ext_parts (z w : AE D) (h1 : realPart D z = realPart D w) (h2 : finitePart D z = finitePart D w) : z = w :=
  tens_ext (A := Ainf D.host.F) (B := Af D.host.F) z w h1 h2

theorem map_real_eq {S : HSp D} {x y : GA D S} (h : infHom S x = infHom S y) :
    (Formalism.L2.Theta.mt S x).map (realPart D) = (Formalism.L2.Theta.mt S y).map (realPart D) := congrArg Units.val h

theorem map_finite_eq {S : HSp D} {x y : GA D S} (h : finHom S x = finHom S y) :
    (Formalism.L2.Theta.mt S x).map (finitePart D) = (Formalism.L2.Theta.mt S y).map (finitePart D) := congrArg Units.val h


set_option maxHeartbeats 2000000 in
theorem mem_besGrp_of_parts {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {x y z : GA D S}
    (hi : infHom S x = infHom S y) (hf : finHom S x = finHom S z) (hy : y ∈ besGrp d o) (hz : z ∈ besGrp d o) :
    x ∈ besGrp d o := by
  have key : ∀ g : GA D S, g ∈ besGrp d o ↔ g ∈ jacGrp d ∧
      HMul.hMul d.p0 (HMul.hMul (Formalism.L2.Theta.mt S g) (HMul.hMul d.j0 o.jB)) = o.jB := fun g => by
    have e := Set.ext_iff.1 (GlobalTheory.BesClosed.besGrp_eq_inter d o) g
    rw [← Matrix.mul_assoc (Formalism.L2.Theta.mt S g), ← Matrix.mul_assoc]
    exact e
  have hi' := map_real_eq hi
  have hf' := map_finite_eq hf
  obtain ⟨hy1, hy2⟩ := (key y).1 hy
  obtain ⟨hz1, hz2⟩ := (key z).1 hz
  obtain ⟨hy3, hy4, hy5⟩ := (GlobalTheory.BesClosed.mem_jacGrp_iff_mat d y).1 hy1
  obtain ⟨hz3, hz4, hz5⟩ := (GlobalTheory.BesClosed.mem_jacGrp_iff_mat d z).1 hz1
  refine (key x).2 ⟨(GlobalTheory.BesClosed.mem_jacGrp_iff_mat d x).2 ⟨?_, ?_, fun i j => ⟨fun hji => ?_, ?_⟩⟩, ?_⟩
  · exact mat_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ hy3 hz3
  · exact mat_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ hy4 hz4
  · exact entry_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ i j ((hy5 i j).1 hji) ((hz5 i j).1 hji)
  · exact entry_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ i i (hy5 i j).2 (hz5 i j).2
  · exact mat_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ hy2 hz2

theorem besGrp_split : ∀ (D : D7) (V V₀ A L : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L),
    ∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ besGrp d o → a ∈ besGrp d o ∧ b ∈ besGrp d o := by
  intro D V V₀ A L ρ d o a ha b hb hab
  have ha' : finHom V a = 1 := MonoidHom.mem_ker.1 ha
  have hb' : infHom V b = 1 := MonoidHom.mem_ker.1 hb
  exact ⟨mem_besGrp_of_parts d o (by rw [map_mul, hb', mul_one]) (by rw [ha', map_one]) hab (one_mem _),
    mem_besGrp_of_parts d o (by rw [hb', map_one]) (by rw [map_mul, ha', one_mul]) (one_mem _) hab⟩

end GlobalTheory.BesSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodLinearAndTranslationCombination
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.TrcProof

variable {D : D7}

theorem contAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem contAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem contAut_rTrans {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem contAut_sum {V : HSp D} {I : Type} (s : Finset I) (a : I → ℂ) (f : I → GA D V → ℂ)
    (hf : ∀ i ∈ s, IsContAut V (f i)) : IsContAut V (∑ i ∈ s, a i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ _ _ => by simp, continuous_const⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact contAut_add (contAut_smul (hf i (Finset.mem_insert_self i s)) (a i))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem per_sum_right {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ)
    {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ) {I : Type} (s : Finset I) (a : I → ℂ) (f : I → GA D B.V → ℂ)
    (hf : ∀ i ∈ s, IsContAut B.V (f i)) :
    B.per ψ φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * B.per ψ φ (f i) := by
  have hconv := fun i (hi : i ∈ s) => PerSumProof.conv hψ B (hf i hi) hφ
  simp only [BesLev.per, besPer]
  have e1 : ∀ h n, besFun ψ 1 B.d B.o B.ζ φ (∑ i ∈ s, a i • f i) h n =
      ∑ i ∈ s, a i * besFun ψ 1 B.d B.o B.ζ φ (f i) h n := by
    intro h n
    simp only [besFun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e1]
  have e2 : (fun h => ∫ n in B.vN.𝓝, ∑ i ∈ s, a i * besFun ψ 1 B.d B.o B.ζ φ (f i) h n ∂B.vN.ν) =
      fun h => ∑ i ∈ s, a i * ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ (f i) h n ∂B.vN.ν := by
    funext h
    rw [integral_finsetSum s fun i hi => ((hconv i hi).1 h).const_mul (a i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  rw [e2, integral_finsetSum s fun i hi => (hconv i hi).2.const_mul (a i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end GlobalTheory.SeeSaw.TrcProof

namespace GlobalTheory.SeeSaw

theorem per_linear_trc : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (φ : GA D B.A → ℂ), IsContAut B.A φ → (∀ (I : Type) (s : Finset I) (a : I → ℂ) (f : I → GA D B.V → ℂ), (∀ i ∈ s, IsContAut B.V (f i)) → B.per ψ φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * B.per ψ φ (f i)) ∧ ∀ (e : GA D B.V →₀ ℂ) (f : GA D B.V → ℂ), IsContAut B.V f → IsContAut B.V (trc e f) ∧ B.per ψ φ (trc e f) = ∑ g ∈ e.support, e g * B.per ψ φ (rTrans g f) := by
  intro D ψ hψ ρ B φ hφ
  refine ⟨fun I s a f hf => TrcProof.per_sum_right hψ B hφ s a f hf, fun e f hf => ?_⟩
  have hT : ∀ g ∈ e.support, IsContAut B.V (rTrans g f) := fun g _ => TrcProof.contAut_rTrans g hf
  exact ⟨TrcProof.contAut_sum e.support e (fun g => rTrans g f) hT,
    TrcProof.per_sum_right hψ B hφ e.support e (fun g => rTrans g f) hT⟩

end GlobalTheory.SeeSaw

end
end

