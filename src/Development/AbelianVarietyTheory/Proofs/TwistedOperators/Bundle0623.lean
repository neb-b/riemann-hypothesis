module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0620
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0612
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0610
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0619
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceTuplesOneOrbitModUniformizerPower

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneLessEqTopBesselLevelPeriod
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain.TopPer

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.RowUnf

variable {D : D7} {A B : HSp D} {c : ℕ}

theorem coreMat_iA {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iA = frameMat B A d.ι := by
  refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
  show Matrix.fromCols (frameMat B A d.ι) (midCol d h) *
      Matrix.fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin 1) (Fin A.rank) D.host.E) = _
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem coreMat_iB {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB = midCol d h := by
  refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
  show Matrix.fromCols (frameMat B A d.ι) (midCol d h) *
      Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin 1) D.host.E) (1 : Matrix (Fin 1) (Fin 1) D.host.E) = _
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]

theorem besselDecomposition_vector_eq {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) (a : D.host.E) :
    (besDec d h).i₀ *ᵥ vecB (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)) (fun _ => a) =
      a • (d.besDat (neg_ne_zero.2 one_ne_zero) σ h).z := by
  show coreMat d h *ᵥ (_ *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, coreMat_iB]
  show midCol d h *ᵥ (fun _ : Fin 1 => a) = _
  funext k
  simp [midCol, Matrix.mulVec, dotProduct, HermitianOrthogonalExtensionData.besDat, mul_comm]

theorem ratV_smul' {n : ℕ} (a : D.host.E) (v : Fin n → D.host.E) : ratV (a • v) = incA D a • ratV v := by
  funext i
  simp [ratV]

section Diag

variable {S S₀ : HSp D} {σ : ℕ} (d1 : HypDec S S₀ σ) (l : Fin σ → D.host.E)

theorem diagI_mul (hl : ∀ a, l a ≠ 0) :
    (diagonal fun a => incA D (l a)) ⬝ (diagonal fun a => incA D (l a)⁻¹) = (1 : Mx D σ σ) := by
  rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a
  rw [← map_mul, mul_inv_cancel₀ (hl a), map_one]

theorem diagI_mul' (hl : ∀ a, l a ≠ 0) :
    (diagonal fun a => incA D (l a)⁻¹) ⬝ (diagonal fun a => incA D (l a)) = (1 : Mx D σ σ) := by
  rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a
  rw [← map_mul, inv_mul_cancel₀ (hl a), map_one]

variable (hl : ∀ a, l a ≠ 0)

theorem jX_diag : (diagDec d1 l hl).jX = d1.jX ⬝ diagonal fun a => incA D (l a) := by
  show rat (d1.e * diagonal l) = _
  rw [rat_mul]; congr 1; exact diagonal_map (map_zero _)

theorem pX_diag_jX : (diagDec d1 l hl).pX ⬝ d1.jX = diagonal fun a => incA D (l a)⁻¹ := by
  have e := (diagDec d1 l hl).pX_jX
  rw [jX_diag, ← Matrix.mul_assoc] at e
  calc (diagDec d1 l hl).pX ⬝ d1.jX
        = (diagDec d1 l hl).pX ⬝ d1.jX ⬝ (diagonal fun a => incA D (l a)) ⬝ (diagonal fun a => incA D (l a)⁻¹) := by
          rw [Matrix.mul_assoc ((diagDec d1 l hl).pX ⬝ d1.jX), diagI_mul l hl, Matrix.mul_one]
    _ = _ := by rw [e, Matrix.one_mul]

theorem blockX_diag (n : GA D S) (T : Mx D σ σ) (e1 : mt S n ⬝ d1.jX = d1.jX + d1.jX ⬝ T) :
    blockX (diagDec d1 l hl) n =
      1 + (diagonal fun a => incA D (l a)⁻¹) ⬝ T ⬝ (diagonal fun a => incA D (l a)) := by
  rw [blockX, jX_diag, ← Matrix.mul_assoc (mt S n), e1, Matrix.add_mul, Matrix.mul_add]
  simp only [← Matrix.mul_assoc]
  rw [pX_diag_jX, diagI_mul' l hl]

theorem coefX_diag (n : GA D S) (z z₀ : Fin S₀.rank → D.host.E) (w : Fin S.rank → D.host.E) (a : D.host.E)
    (b : Fin σ → AE D) (hw : d1.i₀ *ᵥ z₀ = w) (hz : d1.i₀ *ᵥ z = a • w)
    (e2 : mt S n *ᵥ ratV w = ratV w + d1.jX *ᵥ b) :
    coefX (diagDec d1 l hl) z n = incA D a • ((diagonal fun a => incA D (l a)⁻¹) *ᵥ b) := by
  have hzs : (diagDec d1 l hl).j0 *ᵥ ratV z = incA D a • ratV w := by
    rw [HypDec.j0, ← ratV_mulVec]
    show ratV (d1.i₀ *ᵥ z) = _
    rw [hz, ratV_smul']
  have hw' : ratV w = (diagDec d1 l hl).j0 *ᵥ ratV z₀ := by
    rw [HypDec.j0, ← ratV_mulVec]
    show ratV w = ratV (d1.i₀ *ᵥ z₀)
    rw [hw]
  rw [coefX, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hzs, Matrix.mulVec_smul, e2, Matrix.mulVec_smul,
    Matrix.mulVec_add, hw', Matrix.mulVec_mulVec, (diagDec d1 l hl).pX_j0, Matrix.zero_mulVec, zero_add,
    Matrix.mulVec_mulVec, pX_diag_jX]

end Diag

theorem incA_inv_mul_pow (i : ℕ) :
    incA D (D.host.xi0 ^ i)⁻¹ * incA D (D.host.xi0 ^ (i + 1)) = incA D D.host.xi0 := by
  rw [← map_mul, pow_succ, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)), one_mul]

theorem up_sum {σ : ℕ} (T : Mx D σ σ) :
    upSum ((diagonal fun a => incA D (lam σ a)⁻¹) ⬝ T ⬝ (diagonal fun a => incA D (lam σ a))) =
      ∑ i : Fin σ, ∑ j : Fin σ, if j.1 = i.1 + 1 then incA D D.host.xi0 * T i j else 0 := by
  simp only [upSum, Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · have e := incA_inv_mul_pow (D := D) i
    rw [show lam (D := D) σ j = D.host.xi0 ^ ((i : ℕ) + 1) by rw [lam, hij],
      show lam (D := D) σ i = D.host.xi0 ^ (i : ℕ) from rfl]
    linear_combination T i j * e
  · rfl

theorem ell_sum {σ : ℕ} (b : Fin σ → AE D) :
    ell D σ ⬝ᵥ (incA D (D.host.xi0 ^ σ) • ((diagonal fun a => incA D (lam σ a)⁻¹) *ᵥ b)) =
      ∑ i : Fin σ, if i.1 + 1 = σ then incA D D.host.xi0 * b i else 0 := by
  simp only [ell, dotProduct, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · have e := incA_inv_mul_pow (D := D) i
    rw [hi] at e
    calc (1 : AE D) * (incA D (D.host.xi0 ^ σ) * (incA D (lam σ i)⁻¹ * b i))
        = (incA D (D.host.xi0 ^ (i : ℕ))⁻¹ * incA D (D.host.xi0 ^ σ)) * b i := by
          rw [one_mul, ← mul_assoc, mul_comm (incA D (D.host.xi0 ^ σ))]; rfl
      _ = incA D D.host.xi0 * b i := by rw [e]
  · exact zero_mul _

theorem simpleSum_lam {σ : ℕ} (T : Mx D σ σ) (b : Fin σ → AE D) :
    upSum (1 + (diagonal fun a => incA D (lam σ a)⁻¹) ⬝ T ⬝ (diagonal fun a => incA D (lam σ a))) +
        ell D σ ⬝ᵥ (incA D (D.host.xi0 ^ σ) • ((diagonal fun a => incA D (lam σ a)⁻¹) *ᵥ b)) =
      GlobalTheory.BesselChar.superSum (fun _ => incA D D.host.xi0) T b := by
  rw [upSum_add, upSum_one, zero_add, up_sum, ell_sum]
  rfl

theorem psiBes_diag (ψ : AddChar (AF D.host.F) ℂ) {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1)
    (n : GA D B) (hn : n ∈ NFlag B ((besDec d h).e * diagonal (lam σ))) :
    psiBes ψ (diagDec (besDec d h) (lam σ) (lam_ne σ)) 1
      (vecB (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ) n =
      besChar ψ (d.besDat (neg_ne_zero.2 one_ne_zero) σ h) n := by
  have hn' : n ∈ NFlag B (besDec d h).e := (nFlag_diag _ (lam σ) (lam_ne σ)) ▸ hn
  obtain ⟨T, b, -, h1, h2⟩ : ∃ (T : Mx D σ σ) (b : Fin σ → AE D), GlobalTheory.BesselChar.StrictUp T ∧
      mt B n ⬝ (besDec d h).jX = (besDec d h).jX + (besDec d h).jX ⬝ T ∧
      mt B n *ᵥ ratV (d.besDat (neg_ne_zero.2 one_ne_zero) σ h).z =
        ratV (d.besDat (neg_ne_zero.2 one_ne_zero) σ h).z + (besDec d h).jX *ᵥ b :=
    GlobalTheory.BesselChar.exists_coords (d.besDat (neg_ne_zero.2 one_ne_zero) σ h) n hn'
  rw [GlobalTheory.BesselChar.besChar_eq ψ _ n T b h1 h2]
  rw [psiBes, simpleSum, blockX_diag _ _ _ n T h1,
    coefX_diag _ _ _ n _ _ _ _ b (by rw [besselDecomposition_vector_eq d h 1, one_smul]) (besselDecomposition_vector_eq d h _) h2,
    simpleSum_lam, map_one, one_mul, psiE]
  rfl

theorem integral_tr {S : HSp D} {N N' : Subgroup (GA D S)} (hN : N = N') (ν : Measure N) (𝓝 : Set N)
    (f : GA D S → ℂ) : ∫ n in trSet hN 𝓝, f n.1 ∂(trMeas hN ν) = ∫ n in 𝓝, f n.1 ∂ν := by
  subst hN
  rfl

end GlobalTheory.RowChain.TopPer

namespace GlobalTheory.RowChain.TopPer

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem embA_top (G : GridData L sc) (h : GA D (G.V (.top 0))) :
    GlobalTheory.MixPer.embA (besDecAt G 0 ((D.R.m - 2) / 2) top_idx) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) h = embTop G h :=
  (embRel_iff _ h _).1 (GlobalTheory.CharLaws.embRel_embA _ _ _ (coreMat_iA _ _).symm h)

end GlobalTheory.RowChain.TopPer

namespace GlobalTheory.RowChain.TopPer

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem embA_topLev (G : GridData L sc) {t : T} {M : GlobalTheory.FunObj.Vol G} (hM : M.Is t) (h : GA D (G.V (.top 0))) :
    GlobalTheory.MixPer.embA (topLev G hM).d (topLev G hM).o h = embTop G h :=
  embA_top G h

theorem psiBes_topLev (G : GridData L sc) {t : T} {M : GlobalTheory.FunObj.Vol G} (hM : M.Is t) (ψ : AddChar (AF D.host.F) ℂ)
    (n : GA D (G.V (.grid D.R.m 0))) (hn : n ∈ flagN (topLev G hM).d) :
    psiBes ψ (topLev G hM).d 1 (vecB (topLev G hM).o (topLev G hM).ζ) n = besChar ψ G.besTop n :=
  psiBes_diag ψ (G.rowDec 0 (by have := D.R.two_le_m; omega)) (by have := top_idx (D := D); omega) n hn

theorem bplus_eq_topLev_per : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T)
    (M : GlobalTheory.FunObj.Vol G) (hM : M.Is t) (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)),
    Bplus Wl M φ F = (GlobalTheory.RowChain.topLev G hM).per Wl.ψ φ F := by
  intro D T L sc G Wl t M hM φ F
  have hN : NFlag (G.V (.grid D.R.m 0)) G.besTop.e = flagN (topLev G hM).d :=
    (nFlag_diag (rowBes G 0 (by have := D.R.two_le_m; omega) ((D.R.m - 2) / 2)
      (by have := top_idx (D := D); omega)).e (lam _) (lam_ne _)).symm
  have hper : (topLev G hM).per Wl.ψ φ F = ∫ h in M.fd (.top 0), ∫ n in trSet hN M.fdN,
      GlobalTheory.MixPer.besFun Wl.ψ 1 (topLev G hM).d (topLev G hM).o (topLev G hM).ζ φ F h n ∂(trMeas hN M.νN) ∂M.ν (.top 0) :=
    rfl
  rw [hper]
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  refine (integral_tr hN M.νN M.fdN fun g => φ h * F (g * embTop G h) * star (besChar Wl.ψ G.besTop g)).symm.trans ?_
  refine integral_congr_ae (ae_of_all _ fun n => ?_)
  show φ h * F (n.1 * embTop G h) * star (besChar Wl.ψ G.besTop n.1) =
    φ h * F ((show GA D (topLev G hM).V from n.1) * GlobalTheory.MixPer.embA (topLev G hM).d (topLev G hM).o h) *
      star (psiBes Wl.ψ (topLev G hM).d 1 (vecB (topLev G hM).o (topLev G hM).ζ) n.1)
  rw [embA_topLev G hM h, psiBes_topLev G hM Wl.ψ n.1 n.2]
  rfl

end GlobalTheory.RowChain.TopPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColAtFirstPt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.TopZeroInv GlobalTheory.TopLevelInv GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroFirst
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem zero_lt_m (D : D7) : 0 < D.R.m := by
  have h2 := D.R.two_le_m
  omega

private theorem inBasis_val_eq_submatrix_conj {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) :
    (inBasis h β w x).val = ((loc w β)⁻¹ * loc w x * loc w β).val.submatrix (Fin.cast h) (Fin.cast h) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

def kapTop0 (S : GridChoice W U) (t : T) (k : FinPt G (.top 0)) (w : Pl D.host.E) :
    GL (Fin (topRank (locGrid G t w) 0)) (Kw w) :=
  inBasis (topRank_eq G t w (Nat.zero_le _)) (S.βp 0) w (finG (G.V (.top 0)) k)

def firstPt (t : T) (g : FinPt G (.top 0)) (x : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :
    ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) :=
  Function.update x ⟨0, zero_lt_m D⟩ (actO _ _ (g : GA D (G.V (.top 0)))⁻¹ 1⁻¹ (x ⟨0, zero_lt_m D⟩))

def datFn {t : T} (d : PureDat G t) : ∀ l : Arr D, WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ
  | .inl j => (d.1 j).fn
  | .inr i => (d.2 i).fn


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem colAt_firstPt (S : GridChoice W U) {t : T} (ht : t ∈ U) (k : FinPt G (.top 0)) {w : Pl D.host.E}
    (hw : w ∈ locPl G t) (x : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :
    S.colAt t w (firstPt t ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) x) =
      Function.update (S.colAt t w x) 0 (S.colAt t w x 0 * (kapTop0 S t k w).val) := by
  funext j
  by_cases hj : j < D.R.m
  · by_cases h0 : j = 0
    · subst h0
      have hu := loc_finE_u_colCoord S ht (X := .top 0) (Nat.zero_le _) hw
      rw [Function.update_self, colAt_eq S t w _ hj, colAt_eq S t w _ hj]
      unfold firstPt
      rw [Function.update_self, frAt_actO_colCoord]
      simp only [inv_one, map_one, mul_one, inv_mul_cancel, Units.val_one, Matrix.one_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, map_mul, map_inv, hu, _root_.inv_inv, _root_.mul_inv_rev, one_mul]
      unfold kapTop0
      rw [inBasis_val_eq_submatrix_conj, submatrix_cast_mul_colCoord]
      simp only [_root_.mul_assoc]
      rfl
    · rw [Function.update_of_ne h0, colAt_eq S t w _ hj, colAt_eq S t w _ hj]
      unfold firstPt
      rw [Function.update_of_ne (fun h => h0 (congrArg Fin.val h))]
  · have h0 : j ≠ 0 := by
      have := zero_lt_m D
      omega
    rw [Function.update_of_ne h0]
    simp only [GridChoice.colAt, dif_neg hj]

end GlobalTheory.TopZeroFirst

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruentPairsFixVacuumWeilDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

open scoped Topology

noncomputable section

namespace GlobalTheory.VacFixPair

theorem om_pow_eq {D : D7} {S V : HSp D} (om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ))
    (g : GA D S × GA D V) (f : WO S V → ℂ) (c : ℂ) (hc : om g f = c • f) : ∀ m : ℕ, om (g ^ m) f = c ^ m • f := by
  intro m
  induction m with
  | zero => rw [pow_zero, pow_zero, map_one, Module.End.one_apply, one_smul]
  | succ m ih =>
    rw [pow_succ, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]


set_option maxHeartbeats 1000000 in
theorem pair_fix_vacO : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → IsWeilDatumO ψ S T χS χT om →
    ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S N k → GlobalTheory.Member.FinCong T N k' → om (k, k') v = v := by
  intro D ψ θ S T sS sT ΛS ΛT v χS χT om hvac hsdS hsdT hcS hcT hW
  have hθ : IsInfFam θ := hvac.2.inf
  have hev := (GlobalTheory.LatNhds.eventually_actO D S T ΛS ΛT hsdS hsdT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hsdS hsdT)).1
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, ∀ x ∈ GfC S, ∀ x' ∈ GfC T, GlobalTheory.Member.FinCong S n.factorial x →
      GlobalTheory.Member.FinCong T n.factorial x' →
      ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        actO S T x x' u ∈
          (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
    by_contra hne
    push_neg at hne
    choose k hk k' hk' hkc hkc' u hu hu' using hne
    have ht : Filter.Tendsto (fun n => ((k n, k' n) : GA D S × GA D T)) Filter.atTop (𝓝 1) :=
      (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk hkc).prodMk_nhds
        (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk' hkc')
    obtain ⟨n, hn⟩ := (ht.eventually hev).exists
    exact hu' n (hn _ (hu n))
  have hscal : ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S n₁.factorial k →
      GlobalTheory.Member.FinCong T n₁.factorial k' → ∃ c : ℂ, ‖c‖ = 1 ∧ om (k, k') v = c • v := by
    intro k hk k' hk' hc hc'
    have hΛ : ∀ u : WO S T, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
        (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO S T
        (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        u = actO S T k k' u₀ := by
      intro u
      constructor
      · intro hu
        refine ⟨actO S T k⁻¹ k'⁻¹ u, hn₁ k⁻¹ (inv_mem hk) k'⁻¹ (inv_mem hk')
          (GlobalTheory.Member.PrincLevel.finCong_inv hc) (GlobalTheory.Member.PrincLevel.finCong_inv hc') u hu, ?_⟩
        have := GlobalTheory.WeilVacMove.actO_inv_actO k⁻¹ k'⁻¹ u
        rw [inv_inv, inv_inv] at this
        exact this.symm
      · rintro ⟨u₀, hu₀, rfl⟩
        exact hn₁ k hk k' hk' hc hc' u₀ hu₀
    have hvac' := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ
      sS sS sT sT _ _ _ _ k k'
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hk τ, Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hk' τ, Matrix.one_mul, Matrix.mul_one]) hΛ v hvac
    exact GlobalTheory.VacUnique.vacUniqueO D ψ θ hvac.1 hθ (Formalism.L2.Fam.ThC.fixSig S) (Formalism.L2.Fam.ThC.fixSig T)
      sS sT (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _) hcS hcT ΛS ΛT
      hsdS hsdT v _ (GlobalTheory.VacFixTarget.isVacO_fixSig hvac) (GlobalTheory.VacFixTarget.isVacO_fixSig hvac')
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have hcont : Continuous fun p : GA D S × GA D T => om p v w₀ := hW.om_cont _ hvac.2.theta w₀
  have key : ∃ n : ℕ, ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S (n₁.factorial * n.factorial) k →
      GlobalTheory.Member.FinCong T (n₁.factorial * n.factorial) k' → om (k, k') v = v := by
    by_contra hne
    push_neg at hne
    choose k hk k' hk' hkc hkc' hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, om (k n ^ m, k' n ^ m) v = c • v ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, -, hc⟩ := hscal (k n) (hk n) (k' n) (hk' n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
        (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc' n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      push_neg at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (by rw [← Prod.pow_mk]; exact om_pow_eq om _ v c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial) from ⟨hk n, hkc n⟩) _
    have hmem' : ∀ n, k' n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup T (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k' n ∈ GlobalTheory.Member.PrincLevel.levelGroup T (n₁.factorial * n.factorial) from ⟨hk' n, hkc' n⟩) _
    have ht : Filter.Tendsto (fun n => ((k n ^ m n, k' n ^ m n) : GA D S × GA D T)) Filter.atTop (𝓝 1) :=
      (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
        (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)).prodMk_nhds
      (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k' n ^ m n) (fun n => (hmem' n).1)
        (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem' n).2))
    have e1 : om (1 : GA D S × GA D T) v w₀ = v w₀ := by
      rw [map_one]
      rfl
    have h2 : Filter.Tendsto (fun n => om (k n ^ m n, k' n ^ m n) v w₀) Filter.atTop (𝓝 (v w₀)) := by
      have := (hcont.tendsto 1).comp ht
      rw [← e1]
      exact this
    have hpos : 0 < ‖v w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    rw [hmc n, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := hc n
    push_neg at this
    nlinarith [norm_nonneg (v w₀)]
  obtain ⟨n, hn⟩ := key
  exact ⟨n₁.factorial * n.factorial, Nat.mul_pos n₁.factorial_pos n.factorial_pos,
    fun k hk k' hk' hc hc' => hn k hk k' hk' hc hc'⟩

end GlobalTheory.VacFixPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBaseIdempotentOfSplitIdempotentSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

namespace GlobalTheory.IdemSumF

theorem exists_idem_below : ∀ {D : D7} {P : Finset (Pl D.host.E)} {e : AE D}, IsIdemSum e P →
    ∃ ε : AF D.host.F, IsIdempotentElem ε ∧ algebraMap (AF D.host.F) (AE D) ε = e + cA D e :=
  fun he => Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_eps he

end GlobalTheory.IdemSumF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLevelElementOffPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.CosetFJ

theorem besselOrbit_at_badPlace_eq_congruenceTranslate : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * σ + 2) 0)) (· = v), ∀ (u : UX D (σ + 1)), ∀ a ∈ (pcFB W F σ h h').A₁, MxOff (· = v) (mt (G.V (.grid (2 * σ + 2) 0)) g⁻¹ ⬝ (xFB F σ h' ⬝ u.1.1) - xFB F σ h' - a) → ∃ k ∈ lev G (.grid (2 * σ + 2) 0), k ∈ grpAt (G.V (.grid (2 * σ + 2) 0)) (· = v) ∧ MxOff (· = v) (mt (G.V (.grid (2 * σ + 2) 0)) k ⬝ xFB F σ h' - mt (G.V (.grid (2 * σ + 2) 0)) g⁻¹ ⬝ (xFB F σ h' ⬝ u.1.1)) := by
  intro D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv g hg u a ha hoff
  obtain ⟨k, _, _, _, _, p, β, ι, ι', s, t, hpv, hidem, hlat, hι, hι', hιι, hX, hΦ, hA⟩ :=
    _root_.GlobalTheory.FrameFB.frame_fb D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  obtain ⟨ha1, ha2⟩ := hA a ha
  subst hpv
  obtain ⟨k₀, hk₀, hoff'⟩ := _root_.GlobalTheory.AscFin.OneOrbitAt.one_orbit D k p _ σ β (xFB F σ h') ι ι' s t (G.pl.depth sc p.v) (G.pl.depth_pos sc _) hι hι' hιι
    hX hΦ g hg u a ha1 ha2 hoff
  have hsd : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.sp.V_is (2 * σ + 2) 0 (by omega) h' (Nat.zero_le _)).sd
  refine ⟨β.gl _, _root_.GlobalTheory.LevFrame.gl_mem_lev D hQ T L μ0 hL sc G W M hM (.grid (2 * σ + 2) 0) hsd p.v hv k p rfl hidem _ β hlat k₀ hk₀, ?_, hoff'⟩
  exact ((GlobalTheory.FrameAt.frame_facts D k p _ _ β).1 _).2 ⟨_, rfl⟩

end GlobalTheory.CosetFJ
end

