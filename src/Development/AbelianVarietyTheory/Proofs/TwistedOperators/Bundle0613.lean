module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExtendByZeroTrivialDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0606
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsStandardAuxiliaryFramesAllRowGrids
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

section Gen

variable {D : D7} {A B : HSp D} {c σ : ℕ}

theorem isAuxiliaryVectorWittDec_evenFourierJacobiRescale (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ) :
    IsAuxiliaryVectorWittDec d (GlobalTheory.AscInh.rescale (GlobalTheory.RowUnf.jacDec d h) (fun p => (-D.host.xi0) ^ (p.1 + 1))
      fun _ => GlobalTheory.AscInh.xiPow_ne D _) := by
  refine ⟨by omega, ?_, fun p => (star ((-D.host.xi0) ^ (p.1 + 1)))⁻¹, ?_⟩
  · ext i p
    simp only [GlobalTheory.AscInh.rescale, GlobalTheory.RowUnf.jacDec, HermitianOrthogonalExtensionData.iso, colsOf, Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    exact mul_comm _ _
  · ext i p
    simp only [GlobalTheory.AscInh.rescale, GlobalTheory.RowUnf.jacDec, colsOf, Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    exact mul_comm _ _

theorem isAuxiliaryVectorWittDec_oddBesselRescale (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    IsAuxiliaryVectorWittDec d (GlobalTheory.AscInh.rescale (GlobalTheory.RowUnf.besDec d h) (fun p => (-D.host.xi0) ^ (p.1 + 1))
      fun _ => GlobalTheory.AscInh.xiPow_ne D _) := by
  refine ⟨by omega, ?_, fun p => (star ((-D.host.xi0) ^ (p.1 + 1)))⁻¹, ?_⟩
  · ext i p
    simp only [GlobalTheory.AscInh.rescale, GlobalTheory.RowUnf.besDec, HermitianOrthogonalExtensionData.iso, colsOf, Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    exact mul_comm _ _
  · ext i p
    simp only [GlobalTheory.AscInh.rescale, GlobalTheory.RowUnf.besDec, colsOf, Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    exact mul_comm _ _

theorem coreMat_iA (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iA = frameMat B A d.ι := by
  change (Matrix.fromCols (frameMat B A d.ι) (GlobalTheory.RowUnf.midCol d h)).submatrix id (finSumFinEquiv (m := A.rank) (n := 1)).symm *
    (Matrix.fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin 1) (Fin A.rank) D.host.E)).submatrix
      finSumFinEquiv.symm id = _
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.submatrix_id_id]

theorem coreMat_iB (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    (GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB) *ᵥ
      (fun _ => (-D.host.xi0) ^ 0) = fun i => d.a i ⟨σ, by omega⟩ := by
  have e : GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB = GlobalTheory.RowUnf.midCol d h := by
    change (Matrix.fromCols (frameMat B A d.ι) (GlobalTheory.RowUnf.midCol d h)).submatrix id (finSumFinEquiv (m := A.rank) (n := 1)).symm *
      (Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin 1) D.host.E) (1 : Matrix (Fin 1) (Fin 1) D.host.E)).submatrix
        finSumFinEquiv.symm id = _
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add,
      Matrix.submatrix_id_id]
  rw [e]
  funext i
  change ∑ j : Fin 1, GlobalTheory.RowUnf.midCol d h i j * (-D.host.xi0) ^ 0 = _
  rw [Fin.sum_univ_one, pow_zero, mul_one]
  rfl

end Gen

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem auxiliaryFrames_standard : Std (GlobalTheory.AscInh.auxiliaryFrames G) := by
  exact {
    zA := rfl
    zB := by
      funext i
      simp only [GlobalTheory.AscInh.auxiliaryFrames, GlobalTheory.AscInh.lineDec, Matrix.mulVec, dotProduct, pow_zero, mul_one]
      exact Fin.sum_univ_one _
    ζ ρ := by
      funext i
      show (-D.host.xi0) ^ ρ = (-D.host.xi0) ^ ρ * (-D.host.xi0) ^ 0
      rw [pow_zero, mul_one]
    hB ρ h := isAuxiliaryVectorWittDec_oddBesselRescale _ _
    aB ρ h := coreMat_iA _ _
    zB' ρ h := coreMat_iB _ _
    hJ ρ h := isAuxiliaryVectorWittDec_evenFourierJacobiRescale _ _
    aJ ρ h := rfl
  }

theorem exists_std_frames : All fun {_} _ _ _ {G} _ _ => ∃ F : Frames G, Std F :=
  fun _ _ _ _ _ _ _ G _ _ _ => ⟨_, auxiliaryFrames_standard G⟩

end GlobalTheory.AscFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : Vol G)

def lam (σ : ℕ) : Fin σ → D.host.E := fun a => D.host.xi0 ^ (a : ℕ)

theorem lam_ne (σ : ℕ) (a : Fin σ) : lam (D := D) σ a ≠ 0 := pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)

def besDecAt (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) :
    HypDec (G.V (.grid D.R.m j)) (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ :=
  diagDec (rowBes G j (by omega) σ (by omega)) (lam σ) (lam_ne σ)


variable {G t M} in
def volAt (hM : M.Is t) (X : Node) (hX : X.InRange D.R.m) : GlobalTheory.Unf.Vol (G.V X) :=
  ⟨M.ν X, M.fd X, (hM.vtx X hX).haar_fund.1, (hM.vtx X hX).haar_fund.2⟩


variable {t M} in
def besAt (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj)) : BesLev D σ where
  V := G.V (.grid D.R.m j)
  V₀ := GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)
  A := G.V (.top j)
  L := GlobalTheory.SeeSaw.Model.nLine D
  d := besDecAt G j σ hj
  o := GlobalTheory.OrthSumExists.orthDecHsum D _ _
  ζ := fun _ => D.host.xi0 ^ σ
  line := GlobalTheory.SeeSaw.Model.isLineVec_nLine (pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D))
  cpt := cocpt_top G (by omega)
  vA := volAt hM (.top j) (by show j ≤ D.R.m; omega)
  vN := vN


variable {t M} in
def jacAt (hM : M.Is t) (n σ : ℕ) (hn : n + 2 * σ + 1 = D.R.m) : JacLev D σ where
  W := G.V (.grid D.R.m n)
  W₀ := G.V (.top n)
  d := rowJac G n (by omega) σ (by omega)
  cpt := cocpt_top G (by omega)
  v0 := volAt hM (.top n) (by show n ≤ D.R.m; omega)
  vN := (GlobalTheory.Unf.Inhab.nonempty_volN _).some

theorem exists_weilDatum_anisotropicKernelPair {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} (h : IsWeilDatumO ψ V W χV χW om) :
    ∃ om₀ : Om V₀ W₀, IsWeilDatumO ψ V₀ W₀ χV χW om₀ := by
  obtain ⟨om₁, h₁⟩ := (GlobalTheory.Desc.weil_data_descend D ψ V W χV χW om h).1 V₀ ρ dV
  exact (GlobalTheory.Desc.weil_data_descend D ψ V₀ W χV χW om₁ h₁).2 W₀ σ dW


variable {M} in
def stepAt (hM : M.Is t) (j : ℕ) (hj : j + 1 ≤ D.R.m) {V₀ W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec (G.V (.grid D.R.m j)) V₀ ρ)
    (dW : HypDec (G.V (.grid D.R.m (j + 1))) W₀ σ) :
    Step Wl.ψ (G.V (.grid D.R.m j)) V₀ (G.V (.grid D.R.m (j + 1))) W₀ ρ σ where
  χV := G.chrS (.mu t D.R.m j)
  χW := G.chrT (.mu t D.R.m j)
  om := Wl.om (.mu t D.R.m j)
  om₀ := (exists_weilDatum_anisotropicKernelPair dV dW (Wl.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩)).choose
  weil := Wl.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩
  weil₀ := (exists_weilDatum_anisotropicKernelPair dV dW (Wl.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩)).choose_spec
  vW := volAt hM (.grid D.R.m (j + 1)) ⟨le_rfl, hj⟩
  vS := (GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some
  vT := (GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some
  vU := (GlobalTheory.Unf.Inhab.nonempty_volU D _).some

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : Vol G)

theorem link_map {n : ℕ} (σ : ℕ) :
    (-(D.host.xi0 • (1 : Matrix (Fin n) (Fin n) D.host.E))) *ᵥ (fun _ => D.host.xi0 ^ σ) = -fun _ => D.host.xi0 ^ (σ + 1) := by
  rw [neg_mulVec, smul_mulVec, one_mulVec]
  funext i
  simp [pow_succ, mul_comm]

theorem link_norm (L : HSp D) (σ : ℕ) :
    star (fun _ : Fin L.rank => D.host.xi0 ^ (σ + 1)) ⬝ᵥ L.gram *ᵥ (fun _ => D.host.xi0 ^ (σ + 1)) =
      D.host.xi0 * star D.host.xi0 * (star (fun _ : Fin L.rank => D.host.xi0 ^ σ) ⬝ᵥ L.gram *ᵥ (fun _ => D.host.xi0 ^ σ)) := by
  have e : (fun _ : Fin L.rank => D.host.xi0 ^ (σ + 1)) = D.host.xi0 • fun _ => D.host.xi0 ^ σ := by
    funext i
    simp [pow_succ, mul_comm]
  rw [e, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring


variable {G t M} in
def linkAt (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (vN : VolN (besDecAt G j (σ + 1) hj))
    (hj' : j + 1 + 1 + 2 * σ + 2 = D.R.m) (vN' : VolN (besDecAt G (j + 1 + 1) σ hj')) :
    Link (besAt G hM j (σ + 1) hj vN) (besAt G hM (j + 1 + 1) σ hj' vN').L (besAt G hM (j + 1 + 1) σ hj' vN').ζ where
  τ := -(D.host.xi0 • (1 : Matrix (Fin (GlobalTheory.SeeSaw.Model.nLine D).rank) (Fin (GlobalTheory.SeeSaw.Model.nLine D).rank) D.host.E))
  map := link_map σ
  norm := link_norm _ σ

theorem cocpt_last : CoCpt (G.V (.grid D.R.m D.R.m)) := by
  have hm := D.R.two_le_m
  have h := G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ fun j e => by
    injection e with e1
    omega
  refine GlobalTheory.SeeSaw.Inh.coCpt_of_isDefinite h.sigOK fun τ => Or.inl ?_
  rw [h.sig τ, h.rank]
  simp [Node.neg]

def castOm {V : HSp D} {n n' : ℕ} (h : n = n') (om : Om V (G.V (.grid D.R.m n))) : Om V (G.V (.grid D.R.m n')) :=
  Eq.rec (motive := fun k _ => Om V (G.V (.grid D.R.m k))) om h

theorem castOm_weil {ψ : AddChar (AF D.host.F) ℂ} {V : HSp D} {n n' : ℕ} (h : n = n') {χV χW : (AE D)ˣ →* Circle}
    {om : Om V (G.V (.grid D.R.m n))} (hom : IsWeilDatumO ψ V _ χV χW om) :
    IsWeilDatumO ψ V (G.V (.grid D.R.m n')) χV χW (castOm G h om) := by
  subst h
  exact hom

def castSch {V : HSp D} {n n' : ℕ} (h : n = n') (f : WO V (G.V (.grid D.R.m n)) → ℂ) : WO V (G.V (.grid D.R.m n')) → ℂ :=
  Eq.rec (motive := fun k _ => WO V (G.V (.grid D.R.m k)) → ℂ) f h

theorem castSch_theta {ψ : AddChar (AF D.host.F) ℂ} {V : HSp D} {n n' : ℕ} (h : n = n') {f : WO V (G.V (.grid D.R.m n)) → ℂ}
    (hf : IsThetaFunO ψ V _ f) : IsThetaFunO ψ V (G.V (.grid D.R.m n')) (castSch G h f) := by
  subst h
  exact hf


variable {M} in
def lastAt (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : VolN (besDecAt G j 0 hj)) :
    Last Wl.ψ (G.V (.grid D.R.m D.R.m)) (besAt G hM j 0 hj vN) where
  J := jacAt G hM (j + 1) 0 (by omega)
  s := stepAt G Wl t hM j (by omega) (besDecAt G j 0 hj) (rowJac G (j + 1) (by omega) 0 (by omega))
  cptS := GlobalTheory.LastRed.cocpt_zero (rowJac G (j + 1) (by omega) 0 (by omega)) (cocpt_top G (j := j + 1) (by omega))
  cptT := cocpt_last G
  χS := G.chrS (.mu t D.R.m (j + 1))
  χT := G.chrT (.mu t D.R.m (j + 1))
  om := castOm G (show j + 1 + 1 = D.R.m by omega) (Wl.om (.mu t D.R.m (j + 1)))
  weil := castOm_weil G (show j + 1 + 1 = D.R.m by omega) (Wl.om_is (.mu t D.R.m (j + 1)) ⟨le_rfl, by omega⟩)
  vT := volAt hM (.grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩


variable {M} in
noncomputable def chainFrom (hM : M.Is t) : (σ j : ℕ) → (hj : j + 2 * σ + 2 = D.R.m) → (vN : VolN (besDecAt G j σ hj)) →
    Chain Wl.ψ (G.V (.grid D.R.m D.R.m)) σ (besAt G hM j σ hj vN)
  | 0, j, hj, vN => .last (lastAt G Wl t hM j hj vN)
  | σ + 1, j, hj, vN =>
    .step (jacAt G hM (j + 1) (σ + 1) (by omega)) (besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
      (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
        (besDecAt G (j + 1 + 1) σ (by omega)))
      (linkAt hM j σ hj vN (by omega) _) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
      (chainFrom hM σ (j + 1 + 1) (by omega) _)

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : Vol G)

theorem top_idx : 0 + 2 * ((D.R.m - 2) / 2) + 2 = D.R.m := by
  have := D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.m_even
  omega


variable {G t M} in
def topVN (hM : M.Is t) : VolN (besDecAt G 0 ((D.R.m - 2) / 2) top_idx) :=
  volNOf (d := rowBes G 0 (by have := D.R.two_le_m; omega) ((D.R.m - 2) / 2) (by have := top_idx (D := D); omega))
    (nFlag_diag _ (lam _) (lam_ne _)).symm
    (topVolN G M hM.isRow (by have := D.R.two_le_m; omega) (by have := top_idx (D := D); omega))


variable {t M} in
def topLev (hM : M.Is t) : BesLev D ((D.R.m - 2) / 2) := besAt G hM 0 ((D.R.m - 2) / 2) top_idx (topVN hM)


variable {M} in
noncomputable def chain (hM : M.Is t) : Chain Wl.ψ (G.V (.grid D.R.m D.R.m)) ((D.R.m - 2) / 2) (topLev G hM) :=
  chainFrom G Wl t hM _ 0 top_idx (topVN hM)


variable {M} in
noncomputable def dataFrom (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) :
    (σ j : ℕ) → (hj : j + 2 * σ + 2 = D.R.m) → (vN : VolN (besDecAt G j σ hj)) → (chainFrom G Wl t hM σ j hj vN).Data
  | 0, j, hj, _ => (getD t D.R.m D.R.m d j (by omega),
      castSch G (show j + 1 + 1 = D.R.m by omega) (getD t D.R.m D.R.m d (j + 1) (by omega)))
  | σ + 1, j, hj, _ => (getD t D.R.m D.R.m d j (by omega), getD t D.R.m D.R.m d (j + 1) (by omega),
      dataFrom hM d σ (j + 1 + 1) (by omega) _)

def AllTheta (d : PureT G (downPath t D.R.m D.R.m)) : Prop :=
  Path.Fam.All (fun a (f : Sch G a) => IsThetaFunO Wl.ψ (G.pS a.pair) (G.pT a.pair) f) d

variable {M} in
theorem dataFrom_isTheta (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) :
    ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj)),
      (chainFrom G Wl t hM σ j hj vN).IsTheta (dataFrom G Wl t hM d σ j hj vN)
  | 0, j, hj, _ => ⟨getD_all _ t D.R.m D.R.m d hd j (by omega),
      castSch_theta G _ (getD_all _ t D.R.m D.R.m d hd (j + 1) (by omega))⟩
  | σ + 1, j, hj, _ => ⟨getD_all _ t D.R.m D.R.m d hd j (by omega), getD_all _ t D.R.m D.R.m d hd (j + 1) (by omega),
      dataFrom_isTheta hM d hd σ (j + 1 + 1) (by omega) _⟩


variable {M} in
noncomputable def chainData (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) : (chain G Wl t hM).Data :=
  dataFrom G Wl t hM d _ 0 top_idx (topVN hM)


variable {M} in
theorem chainData_isTheta (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) :
    (chain G Wl t hM).IsTheta (chainData G Wl t hM d) :=
  dataFrom_isTheta G Wl t hM d hd _ 0 top_idx (topVN hM)

end GlobalTheory.RowChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierIndexRationalPairValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

namespace GlobalTheory.MovedJet

open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial

theorem substF_one {ι : Type} {N n : ℕ} (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ : ι => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ : ι => (1 : Matrix (Fin n) (Fin n) ℂ)) P = P := by
  have key : GlobalTheory.CompactHowe.substF (fun _ : ι => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ : ι => (1 : Matrix (Fin n) (Fin n) ℂ)) =
      AlgHom.id ℂ (MvPolynomial (ι × Fin N × Fin n) ℂ) := by
    refine algHom_ext fun p => ?_
    rw [GlobalTheory.CompactHowe.substF_X]
    obtain ⟨τ, a, b⟩ := p
    rw [Finset.sum_eq_single a (fun x _ hx => Finset.sum_eq_zero fun y _ => by simp [Matrix.one_apply, hx]) (by simp),
      Finset.sum_eq_single b (fun y _ hy => by simp [Matrix.one_apply, hy]) (by simp)]
    simp
  exact congrArg (fun f => f P) key

theorem mul_conjT_of_unitary {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Matrix.conjTranspose M * M = 1) :
    M * Matrix.conjTranspose M = 1 := Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) |>.1 h

theorem map_conj_mul_conjT {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : M * Matrix.conjTranspose M = 1) :
    M.map (starRingEnd ℂ) * Matrix.conjTranspose (M.map (starRingEnd ℂ)) = 1 := by
  have e := congrArg (fun N : Matrix (Fin n) (Fin n) ℂ => N.map (starRingEnd ℂ)) h
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at e
  convert e using 2
  ext a b
  simp [Matrix.conjTranspose_apply]

end GlobalTheory.MovedJet

namespace GlobalTheory.MovedJet

open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial

theorem conj_invT_of_unitary' {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Matrix.conjTranspose M * M = 1) :
    ((M⁻¹).transpose).map (starRingEnd ℂ) = M := by
  rw [Matrix.inv_eq_left_inv h]
  ext a b
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_conj]

theorem conjT_mul_compAt {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hV : V.gram = 1) (g : GA D V)
    (τ : D.what₂.Tau) :
    Matrix.conjTranspose (compAt θ τ (Formalism.L2.Theta.mt V g)) * compAt θ τ (Formalism.L2.Theta.mt V g) = 1 := by
  have h1 := GlobalTheory.StdUnn.CartanMove.compAt_isom hθ V g τ
  have hg : gramAt D V τ = 1 := by
    unfold gramAt
    rw [hV]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [hg, Matrix.mul_one] at h1
  exact h1

theorem om_pureTensorO_vac {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (g : GA D A)
    (h : GA D WW) (P : MvPolynomial (FVar D WW.rank A.rank) ℂ) :
    IsThetaFunO W.ψ (neg A) WW (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac P) ∧
    (X.ω t).toSgn true ((ofSgn true A).symm g, h)
        (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac P) =
      pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
        ((X.ω t).toSgn true ((ofSgn true A).symm g, h) X.vac)
        (GlobalTheory.CompactHowe.substF (fun τ => (compAt W.θ τ (Formalism.L2.Theta.mt WW h)).map (starRingEnd ℂ))
          (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g)) P) := by
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hom := hI.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hBA : ∀ τ, X.rA.B τ = 1 := fun τ => (hX.std.2.2 τ).2
  have hBW : ∀ τ, X.rW.B τ = 1 := fun τ => (hX.stdW.2.2 τ).2
  have hf : IsThetaFunO W.ψ (neg A) WW X.vac := hI.isVac.2.theta
  have hmt : Formalism.L2.Theta.mt (neg A) ((ofSgn true A).symm g) = Formalism.L2.Theta.mt A g := by
    rw [← GlobalTheory.Grid.mt_ofSgn, MulEquiv.apply_symm_apply]
  set u : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g) with hu
  set v : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt WW h) with hv
  have hop := GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ ((X.ω t).toSgn true) hom hθ
    (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ) X.rA.B (fun τ => X.rA.B τ * u τ) X.rW.s X.rW.s X.rW.B
    (fun τ => X.rW.B τ * v τ) ((ofSgn true A).symm g) h
    (fun τ => by rw [hmt, hsA, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [hsW, Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [hmt, hBA, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hBW, Matrix.mul_one, Matrix.one_mul]) X.vac hf P
  refine ⟨hop.1, ?_⟩
  rw [hop.2]
  have hf' : IsThetaFunO W.ψ (neg A) WW ((X.ω t).toSgn true ((ofSgn true A).symm g, h) X.vac) :=
    hom.om_pres _ _ hf
  have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) := funext fun τ => by rw [hsA]
  have e2 : X.rW.s = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext hsW
  have key := GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D W.ψ W.θ A WW hψ hθ X.rA.B u X.rW.B v _ hf' P
  have hunit : ∀ τ, (((u τ)⁻¹).transpose).map (starRingEnd ℂ) = u τ := fun τ =>
    conj_invT_of_unitary' (conjT_mul_compAt hθ hX.std.1 g τ)
  rw [funext hunit] at key
  rw [e1, e2]
  exact key

end GlobalTheory.MovedJet

namespace GlobalTheory.MovedJet

open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial

theorem isAlgebraic_compAt_of_mem_GQ {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {γ : GA D V}
    (hγ : γ ∈ GQ V) (τ : D.what₂.Tau) (a b : Fin V.rank) :
    IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V γ) a b) := by
  obtain ⟨γ₀, h0⟩ := GlobalTheory.Member.exists_isRat_of_mem_GQ V hγ
  have key : compAt θ τ (Formalism.L2.Theta.mt V γ) a b = tauE D τ (γ₀.1 a b) := by
    unfold compAt Formalism.L2.Theta.mt
    rw [h0]
    exact (hθ τ).1 _
  rw [key]
  have h0 : IsAlgebraic ℚ (γ₀.1 a b) := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (γ₀.1 a b)
  first
    | exact h0.algHom (tauE D τ).toRatAlgHom
    | exact IsAlgebraic.map (tauE D τ).toRatAlgHom h0
    | exact (isAlgebraic_algHom_iff (tauE D τ).toRatAlgHom (tauE D τ).injective).2 h0

theorem isAlgebraic_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (starRingEnd ℂ z) := by
  first
    | exact h.algHom (starRingEnd ℂ).toRatAlgHom
    | exact IsAlgebraic.map (starRingEnd ℂ).toRatAlgHom h
    | exact (isAlgebraic_algHom_iff (starRingEnd ℂ).toRatAlgHom (starRingEnd ℂ).injective).2 h

end GlobalTheory.MovedJet

end
end

