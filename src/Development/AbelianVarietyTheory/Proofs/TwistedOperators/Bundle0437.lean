module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0424
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0429
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0087

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutCuspOfMemCusp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Formalism.IndefR.Mult GlobalTheory.Grid

namespace GlobalTheory.FinLift

variable {D : D7}

theorem autCusp_of_mem_cusp (N : Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsAutFun N.V (Φ v) ∧ IsCuspFun N.V (Φ v) := by
  obtain ⟨T, hT, rfl⟩ := Submodule.mem_map.1 hΦ
  replace hT := (GlobalTheory.MultMem.mem_mult_iff D θ N.V N.S N.M ∅ 1 T).1 hT
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
    exact ⟨(GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut f)).toIsAutFun, GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp f)⟩
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact ⟨GlobalTheory.RowLift.isAutFun_add hx.1 hy.1, GlobalTheory.MultMem.isCuspFun_add hx.1 hy.1 hx.2 hy.2⟩

theorem autCusp_sum (V : HSp D) {ι : Type} (s : Finset ι) (φ : ι → GA D V → ℂ) (h : ∀ i ∈ s, IsAutFun V (φ i) ∧ IsCuspFun V (φ i)) :
    IsAutFun V (∑ i ∈ s, φ i) ∧ IsCuspFun V (∑ i ∈ s, φ i) :=
  Finset.sum_induction φ (fun ψ => IsAutFun V ψ ∧ IsCuspFun V ψ)
    (fun a b ha hb => ⟨GlobalTheory.RowLift.isAutFun_add ha.1 hb.1, GlobalTheory.MultMem.isCuspFun_add ha.1 hb.1 ha.2 hb.2⟩)
    ⟨GlobalTheory.RowLift.isAutFun_zero V, fun r C hC μ 𝓕 hμ h𝓕 g => by simp⟩ h

end GlobalTheory.FinLift

namespace GlobalTheory.FinLift

variable {D : D7}

theorem thetaKO_sum {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T)
    {ι : Type} (s : Finset ι) (x : ι → WO S T → ℂ) : thetaKO om g h (∑ i ∈ s, x i) = ∑ i ∈ s, thetaKO om g h (x i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [thetaKO, map_sum, Finset.sum_apply]

theorem lift_finSum {θ : InfFam D} {A B : Node D} {P : Type} {m : A.MeasDat} {n : ℕ}
    (K : Fin n → P → GA D B.V → GA D A.V → ℂ) (It : P → SmT A.M → SmT B.M)
    (hK : ∀ l, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsMult θ m (K l) It) (ps : Fin n → P) {n' : ℕ} (Fs : Fin n' → A.Maps)
    (vs : Fin n' → SmT A.M) (hF : ∀ k, Fs k ∈ A.Cusp θ) :
    (∀ h, IntegrableOn (fun g => (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g) m.fd m.ν) ∧
    IsAutFun B.V (fun h => ∫ g in m.fd, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g ∂m.ν) ∧
    IsCuspFun B.V (fun h => ∫ g in m.fd, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g ∂m.ν) := by
  choose F' h using fun l k => hK l (Fs k) (hF k)
  have hF' := fun l k => (h l k).1
  have hI := fun l k => (h l k).2
  have hsplit : ∀ h g, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g = ∑ l, ∑ k, K l (ps l) h g * Fs k (vs k) g :=
    fun h g => by rw [Finset.sum_mul_sum]
  have hint : ∀ h, IntegrableOn (fun g => (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g) m.fd m.ν := fun h => by
    simp_rw [hsplit]
    exact integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ => (hI l k (ps l) (vs k) h).1
  have heq : (fun h => ∫ g in m.fd, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g ∂m.ν) =
      ∑ l, ∑ k, F' l k (It (ps l) (vs k)) := by
    funext h
    simp_rw [hsplit]
    rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ => (hI l k (ps l) (vs k) h).1]
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_finsetSum _ fun k _ => (hI l k (ps l) (vs k) h).1]
    exact Finset.sum_congr rfl fun k _ => (hI l k (ps l) (vs k) h).2
  rw [heq]
  exact ⟨hint, autCusp_sum B.V _ _ fun l _ => by
    simpa only [Finset.sum_apply] using autCusp_sum B.V _ _ fun k _ => autCusp_of_mem_cusp B θ (hF' l k) _⟩

end GlobalTheory.FinLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepBasePointScaledCoordinates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.FrameZero

theorem vecMul_row {E k ι : Type} [Field E] [Field k] [Fintype ι] {n c : ℕ} (φ : E →+* k) (σ : E →+* E)
    (a : Matrix (Fin n) (Fin c) E) (g : Matrix (Fin n) (Fin n) E) (b : Matrix (Fin n) ι k) (q : Fin c) (m : ι) :
    ((fun i => φ (σ (a i q))) ᵥ* (g.map φ * b)) m = ((Formalism.UG.cT σ a * g).map φ * b) q m := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring
private theorem mulVec_col_eq_single_of_mul_eq_one {k m n : Type} [Field k] [Fintype m] [DecidableEq n] (b : Matrix m n k)
    (b' : Matrix n m k) (hb : b' * b = 1) (j : n) : (b' *ᵥ fun i => b i j) = Pi.single j 1 := by
  funext i
  show ∑ l, b' i l * b l j = _
  rw [← Matrix.mul_apply, hb, Matrix.one_apply, Pi.single_apply]
private theorem cA_incA_eq_incA_sig (D : D7) (x : D.host.E) :
    cA D (incA D x) = incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) x) := rfl
end GlobalTheory.FrameZero

theorem GlobalTheory.FrameZero.xclauses : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank)) (ϖ : 𝒪[k])
    (κ : Fin (2 * (σ + 1) + 1 - 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank),
  p.v = v →
  Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) →
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) →
  Irreducible ϖ →
  Function.Injective κ →
  (∀ r i, β.b i (κ r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i r))) →
  (∀ j, j ∉ Set.range κ → ∀ r, ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram).map
      (fun c => p.pr (incA D c)) * β.b) r j = 0) →
  ∃ s t : Fin (σ + 1) → k, (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) = Pi.single (κ ⟨q.1, by omega⟩) 1) ∧
    (∀ q, t q • ((fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) ᵥ*
    ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩) 1) := by
  unfold GlobalTheory.AscFin.OnStd All
  intro D _ T L μ0 _ sc G _ M _ F hF σ h v _ k _ _ _ _ p β ϖ κ _ _ _ hirr hinj hb hperp
  obtain ⟨h2, he, -⟩ := hF.hJ (σ + 1) h
  have hϖ : (ϖ : k) ≠ 0 := fun h0 => hirr.ne_zero (Subtype.ext h0)
  have hx0 : p.pr (incA D (-D.host.xi0)) ≠ 0 :=
    (map_ne_zero (p.pr.comp (incA D))).mpr (neg_ne_zero.mpr cmHost_imaginaryGenerator_ne_zero)
  have hx1 : p.pr (incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) (-D.host.xi0))) ≠ 0 :=
    (map_ne_zero (p.pr.comp (incA D))).mpr ((map_ne_zero _).mpr (neg_ne_zero.mpr cmHost_imaginaryGenerator_ne_zero))
  have hx : ∀ i (q : Fin (σ + 1)), xZero (F.dJ (σ + 1) h) i q = incA D ((-D.host.xi0) ^ (q.1 + 1) *
      (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i ⟨q.1, by omega⟩) := by
    intro i q
    show incA D ((F.dJ (σ + 1) h).e i q) = _
    rw [he]
    rfl
  refine ⟨fun q => (p.pr (incA D (-D.host.xi0)) ^ (q.1 + 1) *
      ((ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)))⁻¹)⁻¹,
    fun q => (p.pr (incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) (-D.host.xi0))) ^ (q.1 + 1) *
      (ϖ : k) ^ (G.pl.depth sc v * (2 * (σ + 1) - 1 - q.1 + 1)))⁻¹, ?_, ?_⟩
  · intro q
    have hcol : (fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) =
        (p.pr (incA D (-D.host.xi0)) ^ (q.1 + 1) * ((ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)))⁻¹) •
          fun i => β.b i (κ ⟨q.1, by omega⟩) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hb, hx, map_mul, map_mul, map_pow, map_pow, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hϖ)]
    dsimp only
    rw [hcol, Matrix.mulVec_smul, mulVec_col_eq_single_of_mul_eq_one _ _ β.b'b, smul_smul,
      inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero _ hx0) (inv_ne_zero (pow_ne_zero _ hϖ))), one_smul]
  · intro q
    have hrow : (fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) =
        p.pr (incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) (-D.host.xi0))) ^ (q.1 + 1) •
          fun i => (p.pr.comp (incA D)) ((D.sp.cm.sig : D.host.E →+* D.host.E)
            ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i ⟨q.1, by omega⟩)) := by
      funext i
      rw [hx, cA_incA_eq_incA_sig]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, RingHom.comp_apply]
    have key : ∀ r : Fin (2 * (σ + 1) + 1 - 1), ∑ j, p.pr (incA D ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)
          (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram)
            ⟨q.1, by omega⟩ j)) * ((ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) *
          p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a j r))) =
        (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)
          (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram *
          (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a) ⟨q.1, by omega⟩ r)) := by
      intro r
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_mul]
      ring
    have hN : ((fun i => (p.pr.comp (incA D)) ((D.sp.cm.sig : D.host.E →+* D.host.E)
          ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i ⟨q.1, by omega⟩))) ᵥ*
          ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) =
        (ϖ : k) ^ (G.pl.depth sc v * (2 * (σ + 1) - 1 - q.1 + 1)) •
          Pi.single (κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩) 1 := by
      funext m
      refine (GlobalTheory.FrameZero.vecMul_row (p.pr.comp (incA D)) (D.sp.cm.sig : D.host.E →+* D.host.E)
        (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a (G.V (.grid (2 * (σ + 1) + 1) 0)).gram β.b
        ⟨q.1, by omega⟩ m).trans ?_
      by_cases hm : m ∈ Set.range κ
      · obtain ⟨r, rfl⟩ := hm
        rw [Matrix.mul_apply]
        simp only [hb, Matrix.map_apply, RingHom.comp_apply]
        rw [key, (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).gram, antiDiagonalSignGramMatrix]
        split_ifs with h1 h3
        · exfalso
          have h4 := congrArg Fin.val h3
          simp only at h1 h4
          omega
        · have hrv : r.1 = 2 * (σ + 1) - 1 - q.1 := by simp only at h1; omega
          rw [map_one, map_one, mul_one, Pi.smul_apply, Pi.single_apply,
            if_pos (congrArg κ (Fin.ext hrv)), smul_eq_mul, mul_one, hrv]
        · rw [map_zero, map_zero, mul_zero, Pi.smul_apply, Pi.single_apply, if_neg, smul_zero]
          intro hk
          have h4 := congrArg Fin.val (hinj hk)
          simp only at h1 h4
          omega
      · rw [Pi.smul_apply, Pi.single_apply, if_neg (fun e => hm ⟨_, e.symm⟩), smul_zero]
        exact hperp m hm _
    dsimp only
    rw [hrow, Matrix.smul_vecMul, hN, smul_smul, smul_smul, mul_assoc,
      inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero _ hx1) (pow_ne_zero _ hϖ)), one_smul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColMapEqColMapV
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def colMapV (S : GridChoice W U) (t : T) (v : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
    (x : ∀ j, FinPt G (.top j)) : VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (v ⟨j, h⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowMapV (S : GridChoice W U) (v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
    (y : ∀ i, FinPt G (.grid i D.R.m)) : VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then S.Z.scal 1 (.chi i D.R.m : Pair T) •
      fockComp W S.N.frC (.chi i D.R.m : Pair T) (v ⟨i, h⟩) (y i * S.N.u _) (y (i + 1) * S.N.u _) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

def pairV (S : GridChoice W U) (t : T) {δ : Type} (τ : δ →₀ ℂ)
    (c : δ → ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
    (r : δ → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
    (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  τ.sum fun d a => a • (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
    (colMapV S t (c d) x) (rowMapV S (r d) y)

theorem pairPts_eq_pairV (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (x : ∀ j, FinPt G (.top j))
    (y : ∀ i, FinPt G (.grid i D.R.m)) :
    pairPts S τ x y = pairV S t τ (fun d j => S.Z.vec (d.1 j)) (fun d i => S.Z.vec (d.2 i)) x y := rfl

def movedCol (S : GridChoice W U) {t : T} (d : PureDat G t) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1))) :
    ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) → ℂ :=
  Function.update (Function.update (fun j' => S.Z.vec (d.1 j')) ⟨j, by omega⟩
      (W.om (.top t j) (1, (g : GA D (G.V (.top (j + 1))))) (S.Z.vec (d.1 ⟨j, by omega⟩))))
    ⟨j + 1, hj⟩ (W.om (.top t (j + 1)) ((g : GA D (G.V (.top (j + 1)))), 1) (S.Z.vec (d.1 ⟨j + 1, hj⟩)))

end GlobalTheory.ExpansionInvariance

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceLevelOfEmbedding
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevRestrict

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_hatL {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) {Λ : Submodule (𝓞 E) (Fin n → E)}
    {Λ' : Submodule (𝓞 E) (Fin m → E)} (hM : ∀ y ∈ Λ, M *ᵥ y ∈ Λ') :
    ∀ x ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      (M.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨M *ᵥ y, hM y hy, ?_⟩
    funext i
    exact RingHom.map_mulVec _ M y i
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | smul s x _ hx =>
    have := Submodule.smul_mem _ s hx
    rw [Subring.smul_def, ← mulVec_smul] at this
    rw [Subring.smul_def]
    exact this

theorem map_smul {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) {Λ : Submodule (𝓞 E) (Fin n → E)}
    {Λ' : Submodule (𝓞 E) (Fin m → E)} (hM : ∀ y ∈ Λ, M *ᵥ y ∈ Λ') (𝔪 : Ideal (𝓞 E)) :
    ∀ y ∈ 𝔪 • Λ, M *ᵥ y ∈ 𝔪 • Λ' := by
  have : 𝔪 • Λ ≤ (𝔪 • Λ').comap ((Matrix.mulVecLin M).restrictScalars (𝓞 E)) := by
    rw [Submodule.smul_le]
    intro r hr z hz
    show M *ᵥ (r • z) ∈ 𝔪 • Λ'
    rw [mulVec_smul]
    exact Submodule.smul_mem_smul hr (hM z hz)
  exact fun y hy => this hy

theorem map_hatL_smul {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) {Λ : Submodule (𝓞 E) (Fin n → E)}
    {Λ' : Submodule (𝓞 E) (Fin m → E)} (hM : ∀ y ∈ Λ, M *ᵥ y ∈ Λ') (𝔪 : Ideal (𝓞 E)) :
    ∀ x ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ),
      (M.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ') :=
  map_hatL M (map_smul M hM 𝔪)

end General

open GlobalTheory.UnitaryEmbeddingProperties

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

theorem qM_mul_a (d : HermitianOrthogonalExtensionData A B c ε) : qM d * d.a = 0 := by
  rw [qM, Matrix.mul_assoc, d.perp, Matrix.mul_zero]

theorem qM_lat (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ∀ x ∈ d.lat Λ 𝔟, qM d *ᵥ x ∈ Λ := by
  intro x hx
  obtain ⟨y, hy, u, -, rfl⟩ := hx
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, qM_mul, qM_mul_a, one_mulVec, zero_mulVec, add_zero]
  exact hy

theorem frameMat_lat (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ∀ y ∈ Λ, frameMat B A d.ι *ᵥ y ∈ d.lat Λ 𝔟 :=
  fun y hy => ⟨y, hy, 0, fun p => (𝔟 p).zero_mem, by simp⟩


set_option maxHeartbeats 2000000 in
theorem finE_mem_congLev : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (𝔪 : Ideal (𝓞 D.host.E)) (h : GA D A), Lev.finE B (stabilizerEmbedding d h) ∈ congLev D.sp.cm B.gram (d.lat Λ 𝔟) 𝔪 →
      Lev.finE A h ∈ congLev D.sp.cm A.gram Λ 𝔪 := by
  intro D A B c ε d Λ 𝔟 𝔪 h hg
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin B.rank) (Fin A.rank) (Lev.EAf D),
      P = (frameMat B A d.ι).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin A.rank) (Fin B.rank) (Lev.EAf D),
      Q = (qM d).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g, g = Lev.finE B (stabilizerEmbedding d h) := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k, k = Lev.finE A h := ⟨_, rfl⟩
  rw [← hgdef] at hg
  rw [← hkdef]
  have hQP : HMul.hMul Q P = (1 : Matrix (Fin A.rank) (Fin A.rank) (Lev.EAf D)) := by
    rw [hP, hQ]; exact qM_mul_map _ d
  have e : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E),
      (M.map (incA D)).map (GlobalTheory.LevSplit.finSw D) =
        M.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := fun M => by
    ext i j; exact GlobalTheory.LevSplit.finSw_incA _
  have hG : g.1 = ex P Q k.1 := by
    rw [hgdef, hkdef, GlobalTheory.LevSplit.finE_val, GlobalTheory.LevSplit.finE_val, hP, hQ]
    show ((matHom B (stabilizerEmbedding d h)).1).map _ = ex _ _ (((matHom A h).1).map _)
    rw [unitaryEmbedding_matrix_formula, ex_map, e, e]
  have hGP : HMul.hMul g.1 P = HMul.hMul P k.1 := by rw [hG]; exact ex_mul_P P Q hQP _
  have hk : k.1 = HMul.hMul (HMul.hMul Q g.1) P := by
    rw [Matrix.mul_assoc, hGP, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hPl : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, P *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ 𝔟) :=
    by subst hP; exact map_hatL (F := D.host.F) (frameMat B A d.ι) (frameMat_lat d Λ 𝔟)
  have hQl : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ 𝔟), Q *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    by subst hQ; exact map_hatL (F := D.host.F) (qM d) (qM_lat d Λ 𝔟)
  rw [mem_congLev] at hg
  have g2 := hg.2.1
  have g3 := hg.2.2
  rw [mem_congLev]
  refine ⟨?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun x hx => ?_⟩
  · rw [hkdef]; exact GlobalTheory.LevSplit.finE_mem_UA A h
  · rw [hk, ← mulVec_mulVec, ← mulVec_mulVec]; exact hQl _ ((g2 _).1 (hPl x hx))
  · have h1 := hPl _ hx
    rw [mulVec_mulVec, ← hGP, ← mulVec_mulVec] at h1
    have h2 := hQl _ ((g2 _).2 h1)
    rwa [mulVec_mulVec, hQP, one_mulVec] at h2
  · have e2 : k.1 *ᵥ x - x = Q *ᵥ (g.1 *ᵥ (P *ᵥ x) - P *ᵥ x) := by
      rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hQP, one_mulVec, hk]
    rw [e2, hQ]
    exact map_hatL_smul (F := D.host.F) (qM d) (qM_lat d Λ 𝔟) 𝔪 _ (g3 _ (hPl x hx))

end GlobalTheory.LevRestrict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruencesReductionMemSymmetricUnipotentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruences_reduction_mem_symmetricUnipotent : ∀ {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bw bwd : Fin D.R.k → VA (II D)) (ew : EAf D), Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) g e0 f0 z0 bw bwd ew → ∀ (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Bool), IsFrame β (II D).L → LocAt g e0 f0 z0 bw bwd ew β PP w → ∀ (x : (II D).Gf) (M : GL (Fin (Yc D 0).rank) (EAf D)), x ∈ (II D).Kset → (II D).fmat x = M.val → M ∈ St β → K2cong (II D) g e0 z0 bw x → upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP M) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k := by
  first | exact @GlobalTheory.SeeConjGroup.congr_red_mem_unipSym | exact GlobalTheory.SeeConjGroup.congr_red_mem_unipSym | (intros; apply GlobalTheory.SeeConjGroup.congr_red_mem_unipSym <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulCuspIntegrableOnFst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColConv

open GlobalTheory.Grid

theorem measDat_haar_fd {D : D7} {N : Node D} {m : N.MeasDat} {df : Prop} {K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))}
    (h : m.Is df K) : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
  by_cases hd : df
  · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
  · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D} {u : WO S T → ℂ}

theorem thetaKO_mul_cusp_integrableOn_fst (hP : GlobalTheory.Published.CuspRapidDecay) (hω : IsWeilDatumO ψ S T χS χT om)
    (hθ : IsInfFam θ) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) (hu : IsThetaFunO ψ S T u) {y : GA D S → ℂ} (hy : IsAutFunSm θ S y)
    (hc : IsCuspFun S y) (x : GA D T) : IntegrableOn (fun g => thetaKO om g x u * y g) 𝓕 ν := by
  have : BorelSpace (GA D S) := ⟨rfl⟩
  exact (GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hy hc).integrableOn_modGrowth_mul hν h𝓕
    (GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_modGrowth_fst hθ hω hu x)
    (GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hω hu x)
    (GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_continuous_fst hω hu x).measurable.aestronglyMeasurable

theorem measX_haar_fd {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridPre R}
    (hG : G.Is) (j : ℕ) (hj : j ≤ D.R.m) :
    (G.measX j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.Xp j).V) (G.measX j).fd (G.measX j).ν := by
  cases j with
  | zero => exact measDat_haar_fd (hG.meas.P D.R.m le_rfl)
  | succ j => exact measDat_haar_fd (hG.meas.X j hj)

end GlobalTheory.ColConv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CovariantVectorToFunctionFormCoeffMemRangeStatement
section
open Formalism.L2.DIV MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covariantVectorToFunctionForm_coeff_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L] (κ : L →+* ℂ), GlobalTheory.FunObj.ReadOK σ → ∀ (F : VV ℂ σ), (∀ m, AddMonoidAlgebra.coeff F.1 m ∈ Set.range κ) → ∀ m, AddMonoidAlgebra.coeff (GlobalTheory.FunObj.funOf σ F).1 m ∈ Set.range κ := by
  first | exact @GlobalTheory.RowFun.coeff_funOf_mem_range | exact GlobalTheory.RowFun.coeff_funOf_mem_range | (intros; apply GlobalTheory.RowFun.coeff_funOf_mem_range <;> assumption)
end

