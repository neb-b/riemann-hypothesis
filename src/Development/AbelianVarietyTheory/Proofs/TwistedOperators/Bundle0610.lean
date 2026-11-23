module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylKTypeTensorEqContragredientTranslatesSpan
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0591
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0608
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOOneResGCompl
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt resG_compl suppAt_resG isDetAt_detAt resG_one resG_mul actO_actO isHalf_actO)

noncomputable section

namespace GlobalTheory.TopLevelInv

abbrev conjPt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (j : ℕ) (k : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))) :=
  (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem detAt_resG_eq {D : D7} {V : HSp D} {e : AE D} {ε : AF D.host.F} (he2 : e * e = e) (hc : e * cA D e = 0)
    (hε : IsIdempotentElem ε) (halg : algebraMap (AF D.host.F) (AE D) ε = e + cA D e) (g : GA D V) :
    detAt e V (resG V ε g) = detAt e V g := by
  apply Units.ext
  rw [Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he2, Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he2, Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG V hε, halg]
  congr 1
  set I : Ideal (AE D) := Ideal.span {1 - e}
  have h1 : Ideal.Quotient.mk I e = 1 := by
    rw [← (Ideal.Quotient.mk I).map_one, Ideal.Quotient.eq]
    have : e - 1 = (-1) * (1 - e) := by ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have h2 : Ideal.Quotient.mk I (cA D e) = 0 := by
    calc Ideal.Quotient.mk I (cA D e) = Ideal.Quotient.mk I (cA D e) * Ideal.Quotient.mk I e := by rw [h1, mul_one]
      _ = Ideal.Quotient.mk I (cA D e * e) := (map_mul _ _ _).symm
      _ = 0 := by rw [mul_comm, hc, map_zero]
  have key : (Formalism.IndefR.Fin.LevelGroupLemmas.resM (e + cA D e) (mt V g)).map (Ideal.Quotient.mk I) =
      (mt V g).map (Ideal.Quotient.mk I) := by
    ext i j
    simp only [Matrix.map_apply, Formalism.IndefR.Fin.LevelGroupLemmas.resM, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, h1, h2]
    ring
  have hd : Ideal.Quotient.mk I (Formalism.IndefR.Fin.LevelGroupLemmas.resM (e + cA D e) (mt V g)).det = Ideal.Quotient.mk I (mt V g).det := by
    rw [RingHom.map_det, RingHom.map_det]
    exact congrArg Matrix.det key
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hd
  obtain ⟨r, hr⟩ := hd
  linear_combination (-e) * hr + (-r) * he2

theorem detAt_one' {D : D7} {e : AE D} (he2 : e * e = e) (V : HSp D) : detAt e V 1 = 1 := by
  apply Units.ext
  rw [Formalism.IndefR.Fin.LevelGroupLemmas.detAt_val he2, Formalism.IndefR.Fin.LevelGroupLemmas.mt_one', Matrix.det_one, Units.val_one]
  ring

theorem resG_inv_eq {D : D7} {V : HSp D} {ε : AF D.host.F} (hε : IsIdempotentElem ε) (g : GA D V) :
    (resG V ε g)⁻¹ = resG V ε g⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← resG_mul V hε, mul_inv_cancel, resG_one V hε]

theorem actO_one_resG_compl {D : D7} {S T : HSp D} {e : AE D} (he2 : e * e = e) (hc : e * cA D e = 0) {ε : AF D.host.F}
    (hε : IsIdempotentElem ε) (halg : algebraMap (AF D.host.F) (AE D) ε = e + cA D e) (h : GA D T) (x : WO S T)
    (hx : IsHalf e x) : actO S T 1 (resG T (1 - ε) h) x = x := by
  have hann : ∀ i j, algebraMap (AF D.host.F) (AE D) (1 - ε) * x i j = 0 := by
    intro i j
    rw [map_sub, map_one, halg, ← hx i j]
    linear_combination (-(x i j)) * he2 + (-(x i j)) * hc
  rw [Formalism.IndefR.Fin.LevelGroupLemmas.actO_eq, inv_one, Formalism.IndefR.Fin.LevelGroupLemmas.mt_one', Matrix.mul_one,
    Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG T hε.one_sub]
  unfold Formalism.IndefR.Fin.LevelGroupLemmas.resM
  rw [Matrix.add_mul, Matrix.one_mul, add_eq_left]
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [mul_assoc, mul_left_comm, hann l j, mul_zero]

theorem isSBHalf_halfInd {D : D7} {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf e Λ (halfInd e Λ) := by
  refine ⟨fun x hx => ?_, 1, one_pos, fun u hu hu' x => ?_, fun x hx => ?_⟩
  · by_contra h; exact hx (if_neg fun h' => h h'.2)
  · rw [one_smul]
    have h1 : IsHalf e (x + u) ↔ IsHalf e x := forall₂_congr fun i j => by
      rw [Matrix.add_apply, mul_add, hu' i j, add_left_inj]
    exact halfInd_congr (and_congr (AddSubgroup.add_mem_cancel_right _ hu) h1)
  · rw [one_smul]; by_contra h; exact hx (if_neg fun h' => h h'.1)

end GlobalTheory.TopLevelInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CastRealAll
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowReal
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefBase

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem rank_X (ch : Choice R) : (rowSizes D).nC (0 : Fin ((rowSizes D).m + 1)) = D.sp.X'.rank := by
  have h1 := rank_gridM ch.G (i := 0) (Nat.zero_le _)
  have h2 : (ch.G.V (.grid 0 D.R.m)) = (columnBlock R.toLevCh D.R.m).sp := rfl
  rw [h2, colY_m] at h1
  exact h1.symm

def xPt (ch : Choice R) (g : Gc D.what₂.Tau (rowSizes D)) : GA D D.sp.X' :=
  cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) ((kappa ch.W g).2 0)

theorem cast_realAll (θ : InfFam D) (n0 : ℕ) (hn : n0 = D.sp.X'.rank) (v : UG D.what₂.Tau n0) :
    ∀ (X : LSp D) (h : X = ⟨D.sp.X', R.toLevCh.ΛX⟩) (O : D.what₂.Tau → Matrix (Fin X.sp.rank) (Fin X.sp.rank) ℂ)
      (hO : HEq O (onb R.MX)) (e1 : n0 = X.sp.rank),
      cast (congrArg (fun X : LSp D => GA D X.sp) h)
        (realAll θ X.sp (fun τ => O τ * ((castU e1 (v τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) * (O τ)⁻¹)) =
      realAll θ D.sp.X' (fun τ => onb R.MX τ * ((castU hn (v τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) *
        (onb R.MX τ)⁻¹) := by
  intro X h
  subst h
  intro O hO e1
  cases eq_of_heq hO
  rfl

theorem xPt_eq (ch : Choice R) (hO : ch.W.Over R) (h0 : PosOnb ch.W (.grid 0 D.R.m)) (g : Gc D.what₂.Tau (rowSizes D)) :
    xPt ch g = realAll R.θ D.sp.X' (fun τ => GlobalTheory.DefLift.unfr R.MX τ
      ((castU (rank_X ch) (g.2 0 τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ)) := by
  unfold xPt
  have hk : ((kappa ch.W g).2 0 : GA D (columnBlock R.toLevCh D.R.m).sp) =
      realAll ch.W.θ (columnBlock R.toLevCh D.R.m).sp (fun τ => ch.W.onb (.grid 0 D.R.m) τ *
        ((castU (rank_gridM ch.G (i := 0) (Nat.zero_le _)).symm (g.2 0 τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) *
          (ch.W.onb (.grid 0 D.R.m) τ)⁻¹) := by
    exact vtxPt_eq h0 (colU ch.G 0 g)
  rw [hk]
  have e := cast_realAll (R := R) ch.W.θ _ (rank_X ch) (g.2 0) (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh)
    (ch.W.onb (.grid 0 D.R.m)) hO.onbX (rank_gridM ch.G (i := 0) (Nat.zero_le _)).symm
  refine e.trans ?_
  rw [hO.θ]
  congr 1
  funext τ
  unfold GlobalTheory.DefLift.unfr onb
  rw [Matrix.nonsing_inv_nonsing_inv _ (GlobalTheory.DefLift.fr_det R.MX τ)]

end GlobalTheory.CoefBase

namespace GlobalTheory.CoefBase

section Core

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} [DecidableEq D.what₂.Tau]

end Core

section Core2

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} [DecidableEq D.what₂.Tau]

theorem core (M : Formalism.IndefR.Mult.DSModel V S) (θ : InfFam D) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ)
    (hθ : IsInfFam θ) (hp : GlobalTheory.DefLift.AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr) (lam : D.what₂.Tau → ℕ → ℤ)
    (hl : ∀ τ (i : Fin V.rank), (lam τ i : ℝ) = -(Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Fin.rev i)) :
    ∃ A : c.W ≃ₗ[ℂ] weylSub V.rank lam, ∀ (u : UG D.what₂.Tau V.rank) (w : c.W),
      A (c.ρ (realAll θ V (fun τ => GlobalTheory.DefLift.unfr M τ (u τ))) w) = weylRep V.rank lam u (A w) := by
  have hε : ∀ τ, M.ε τ = Formalism.MainNotions.S.allPos V.rank := fun τ => funext fun a => hp τ a
  have m := fun τ => GlobalTheory.CompactModel.model_allPos D V S M τ (hε τ)
  haveI : ∀ τ, FiniteDimensional ℂ (M.H τ) := fun τ => (m τ).1
  obtain ⟨E, hE⟩ := _root_.GlobalTheory.CoefPairTens.pairEquiv_realAll D V S M θ c pr hθ hp hc hpr
  obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.DualWeylTensor.main D.what₂.Tau V.rank M.H M.σ M.lam lam (fun τ => (M.enum τ).1) (fun τ => (m τ).2.2.1) (fun τ => (m τ).2.2.2)
    (fun τ i => by rw [hl τ i, hε τ])
  haveI : FiniteDimensional ℂ (⨂[ℂ] τ, M.H τ) := inferInstance
  haveI : FiniteDimensional ℂ (Module.Dual ℂ (weylSub V.rank lam)) := Module.Finite.equiv Φ.symm
  haveI : FiniteDimensional ℂ (weylSub V.rank lam) := (Module.finite_dual_iff ℂ).1 this
  let ev := Module.evalEquiv ℂ (weylSub V.rank lam)
  refine ⟨(E.trans Φ.dualMap).trans ev.symm, fun u w => ?_⟩
  apply ev.injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  ext φ
  rw [LinearEquiv.dualMap_apply, hE, LinearMap.comp_apply]
  have key : (PiTensorProduct.map fun τ => ((M.σ τ ((u τ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) :
      M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)) (Φ φ) = Φ ((weylRep V.rank lam).dual u⁻¹ φ) := (hΦ u⁻¹ φ).symm
  rw [key]
  obtain ⟨y, hy⟩ := ev.surjective (Φ.dualMap (E w))
  rw [← hy, LinearEquiv.symm_apply_apply]
  have h2 : E w (Φ ((weylRep V.rank lam).dual u⁻¹ φ)) = ev y ((weylRep V.rank lam).dual u⁻¹ φ) := by
    rw [hy]; rfl
  rw [h2]
  show ((weylRep V.rank lam).dual u⁻¹ φ) y = φ (weylRep V.rank lam u y)
  rw [Representation.dual_apply, inv_inv]
  rfl

end Core2

theorem weyl_cast {ι : Type} [Fintype ι] [DecidableEq ι] (n n' : ℕ) (h : n = n') (lam : ι → ℕ → ℤ) :
    ∃ e : weylSub (ι := ι) n lam ≃ₗ[ℂ] weylSub n' lam, ∀ u F,
      e (weylRep n lam u F) = weylRep n' lam (fun τ => castU h (u τ)) (e F) := by
  subst h
  exact ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem cast_inv : ∀ (X Y : LSp D) (h : X = Y) (a : GA D X.sp),
    cast (congrArg (fun X : LSp D => GA D X.sp) h) a⁻¹ = (cast (congrArg (fun X : LSp D => GA D X.sp) h) a)⁻¹ := by
  intro X Y h a
  subst h
  rfl

theorem xPt_inv (ch : Choice R) (g : Gc D.what₂.Tau (rowSizes D)) : xPt ch g⁻¹ = (xPt ch g)⁻¹ := by
  have hk : ((kappa ch.W g⁻¹).2 0 : GA D (columnBlock R.toLevCh D.R.m).sp) =
      ((kappa ch.W g).2 0 : GA D (columnBlock R.toLevCh D.R.m).sp)⁻¹ :=
    congrArg (fun x => x.2 0) (map_inv (kappa ch.W) g)
  exact (congrArg (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh))) hk).trans
    (cast_inv (columnBlock R.toLevCh D.R.m) _ (colY_m R.toLevCh) ((kappa ch.W g).2 0))

theorem coefBase [DecidableEq D.what₂.Tau] (ch : Choice R) (hθ : R.models_inf) (hc : R.models_cX) (hpr : R.models_prX)
    (hO : ch.W.Over R) (h0 : PosOnb ch.W (.grid 0 D.R.m)) :
    ∃ B : Module.Dual ℂ (weylSub ((rowSizes D).nC (0 : Fin ((rowSizes D).m + 1))) (baseWt (rowEntries D ch.sc.cGap))) ≃ₗ[ℂ]
        Module.Dual ℂ R.cX.W,
      ∀ g φ, B ((baseRep (rowEntries D ch.sc.cGap)).dual g φ) =
        B φ ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) ((kappa ch.W g).2 0))⁻¹ := by
  obtain ⟨A0, hA0⟩ := core R.MX R.θ R.cX R.prX hθ (GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) _) hc hpr
    (baseWt (rowEntries D ch.sc.cGap)) (fun τ i => _root_.GlobalTheory.RowReal.hw_basePar_eq_neg_lowK D ch.sc.cGap R.MX τ i)
  obtain ⟨e, he⟩ := weyl_cast (ι := D.what₂.Tau) _ _ (rank_X ch) (baseWt (rowEntries D ch.sc.cGap))
  refine ⟨(A0.trans e.symm).dualMap, fun g φ => ?_⟩
  ext w
  show ((baseRep (rowEntries D ch.sc.cGap)).dual g φ) (e.symm (A0 w)) = φ (e.symm (A0 (R.cX.ρ (xPt ch g)⁻¹ w)))
  rw [← xPt_inv, xPt_eq ch hO h0, hA0, Representation.dual_apply]
  have h1 := he (g⁻¹.2 0) (e.symm (A0 w))
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]
  rfl

end GlobalTheory.CoefBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomDeepPointsFixLatticeStdFirst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.StdFstFix

variable {D : D7}

theorem isHalf_actO {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) {x : WO S T} (hx : IsHalf e x) :
    IsHalf e (actO S T g h x) := by
  have hx' : e • (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = x := Matrix.ext fun i j => hx i j
  have e1 : e • actO S T g h x = actO S T g h x := by
    unfold actO
    conv_rhs => rw [← hx']
    rw [Matrix.mul_smul, Matrix.smul_mul]
  intro i j
  exact congrFun (congrFun e1 i) j

theorem actO_nsmul {S T : HSp D} (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := by
  unfold actO
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem finCong_of_mem_GinfC {V : HSp D} (N : ℕ) {k : GA D V} (hk : k ∈ GinfC V) : GlobalTheory.Member.FinCong V N k := by
  have h1 : finHom V k = finHom V 1 := by rw [map_one]; exact hk
  have := GlobalTheory.Member.PrincLevel.finCong_one V N
  unfold GlobalTheory.Member.FinCong at this ⊢
  rw [h1]
  exact this

end GlobalTheory.StdFstFix

namespace GlobalTheory.StdFstFix


set_option maxHeartbeats 2000000 in
theorem stdFst_fixed : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A), IsOpen (U : Set (GA D A)) ∧ GinfC A ≤ U ∧ ∀ k ∈ U, k ∈ GfC A →
      (∀ u, u ∈ (latO (GlobalTheory.Grid.neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) ↔ actO (GlobalTheory.Grid.neg A) WW ((GlobalTheory.Grid.ofSgn true A).symm k) 1 u ∈ (latO (GlobalTheory.Grid.neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True)) ∧
      ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β
          (actO (GlobalTheory.Grid.neg A) WW ((GlobalTheory.Grid.ofSgn true A).symm k)⁻¹ 1⁻¹ x) =
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β x := by
  intro D T L sc G W i j A A' WW X hX t
  classical
  have hI := hX.is
  have hν : Continuous (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) /
      (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) := (hI.weil' t).hecT.1
  have he := hI.idem t
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hsdS : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := isSelfDualC_neg' hI.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hI.rigW.1
  obtain ⟨M, hM, hB⟩ := GlobalTheory.PlaceDatum.exists_den_frMapO (S := GlobalTheory.Grid.neg A) hsdS.1.fg hsdT.1.fg X.rA.β X.rW.β
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := GlobalTheory.Grid.neg A)
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hsdS)
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hsdT) X.rA.β X.rW.β
  obtain ⟨n, hn, hl, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D _ hν
  obtain ⟨n₀, hn₀, hnI⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ ((n₀ : ℕ) : 𝓞 D.host.E) ∈ X.ideal (locPl G) t :=
    ⟨_, Nat.pos_of_ne_zero fun h => GlobalTheory.ConstRatio.ideal_ne_bot X (locPl G) t (Ideal.absNorm_eq_zero_iff.1 h),
      Ideal.absNorm_mem _⟩
  obtain ⟨c, hc, hcS⟩ : ∃ c : ℕ, 0 < c ∧ ∀ P ∈ locPl G t, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    refine ⟨∏ P ∈ locPl G t, Ideal.absNorm P.asIdeal, Finset.prod_pos fun P _ =>
      Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), fun P hP => ?_⟩
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun P : Pl D.host.E => Ideal.absNorm P.asIdeal) hP
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem P.asIdeal)
  obtain ⟨m, hm⟩ := GlobalTheory.VacTranslate.exists_finCong_mod (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ hsdS hsdT
    (K * (n₀ * (n * c) * M)) (Nat.mul_pos hK (Nat.mul_pos (Nat.mul_pos hn₀ (Nat.mul_pos hn hc)) hM))

  have key : ∀ g ∈ GfC (GlobalTheory.Grid.neg A), GlobalTheory.Member.FinCong (GlobalTheory.Grid.neg A) m.factorial g → ∀ x : WO A WW,
      (IsHalf (X.e t) x ∧ IsIntM (frMapO A WW X.rA.β X.rW.β x) ∧
        ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (X.ideal (locPl G) t) (frMapO A WW X.rA.β X.rW.β x i j)) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) /
                   (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β
                   (actO (GlobalTheory.Grid.neg A) WW g 1 x) =
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) /
          (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β x := by
    intro g hg hgc x hx
    obtain ⟨l, hl', e1⟩ := hm g hg hgc (K • x) (hC x (GlobalTheory.PlaceDatum.infPart_of_half hinf hx.1) hx.2.1)
    have e2 : actO (GlobalTheory.Grid.neg A) WW g 1 x = x + (n₀ * (n * c) * M) • l := by
      have e3 : K • actO (GlobalTheory.Grid.neg A) WW g 1 x = K • (x + (n₀ * (n * c) * M) • l) := by
        rw [← actO_nsmul, e1, smul_add, smul_smul]
      rw [← GlobalTheory.PlaceModel.inv_smul_nsmul (GlobalTheory.Grid.neg A) WW hK (actO (GlobalTheory.Grid.neg A) WW g 1 x), e3,
        GlobalTheory.PlaceModel.inv_smul_nsmul (GlobalTheory.Grid.neg A) WW hK]
    refine StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.stdFst_shift he hnI hl hcS A WW X.rA.β X.rW.β
      (W := fun i j => (M : Lev.EAf D) * frMapO A WW X.rA.β X.rW.β l i j)
      ⟨fun _ => hx.1, fun _ => isHalf_actO g 1 hx.1⟩ (fun i j => hB l hl' i j) fun i j => ?_
    rw [e2, GlobalTheory.PlaceDatum.frMapO_add]
    push_cast
    ring
  refine ⟨(GlobalTheory.VacFixTarget.congGroup (GlobalTheory.Grid.neg A) m.factorial).comap (GlobalTheory.Grid.ofSgn true A).symm.toMonoidHom,
    (GlobalTheory.Grid.continuous_ofSgn_symm true A).isOpen_preimage _
      (GlobalTheory.VacFixTarget.isOpen_congGroup (GlobalTheory.Grid.neg A) m.factorial_pos), fun k hk => ?_, fun k hkU hkf => ?_⟩
  · show GlobalTheory.Member.FinCong (GlobalTheory.Grid.neg A) m.factorial ((GlobalTheory.Grid.ofSgn true A).symm k)
    refine finCong_of_mem_GinfC _ ?_
    rw [GlobalTheory.SgnIdent.mem_GinfC_sgn, MulEquiv.apply_symm_apply]
    exact hk
  · have hκf : (GlobalTheory.Grid.ofSgn true A).symm k ∈ GfC (GlobalTheory.Grid.neg A) := by
      rw [GlobalTheory.SgnIdent.mem_GfC_sgn, MulEquiv.apply_symm_apply]
      exact hkf
    have hκc : GlobalTheory.Member.FinCong (GlobalTheory.Grid.neg A) m.factorial ((GlobalTheory.Grid.ofSgn true A).symm k) := hkU
    refine ⟨fun u => ⟨fun hu => ?_, fun hu => ?_⟩, fun x => ?_⟩
    · obtain ⟨l, hl', e⟩ := hm _ hκf hκc u hu
      rw [e]
      exact add_mem hu (nsmul_mem hl' _)
    · obtain ⟨l, hl', e⟩ := hm _ (inv_mem hκf) (GlobalTheory.Member.PrincLevel.finCong_inv hκc) _ hu
      have e' := GlobalTheory.WeilVacMove.actO_inv_actO ((GlobalTheory.Grid.ofSgn true A).symm k) (1 : GA D WW) u
      rw [inv_one] at e'
      rw [e'] at e
      rw [e]
      exact add_mem hu (nsmul_mem hl' _)
    · rw [inv_one]
      set g := ((GlobalTheory.Grid.ofSgn true A).symm k)⁻¹ with hgdef
      have hg : g ∈ GfC (GlobalTheory.Grid.neg A) := inv_mem hκf
      have hgc : GlobalTheory.Member.FinCong (GlobalTheory.Grid.neg A) m.factorial g := GlobalTheory.Member.PrincLevel.finCong_inv hκc
      by_cases hx : IsHalf (X.e t) x ∧ IsIntM (frMapO A WW X.rA.β X.rW.β x) ∧
          ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (X.ideal (locPl G) t) (frMapO A WW X.rA.β X.rW.β x i j)
      · exact key g hg hgc x hx
      · by_cases hx' : IsHalf (X.e t) (actO (GlobalTheory.Grid.neg A) WW g 1 x) ∧
            IsIntM (frMapO A WW X.rA.β X.rW.β (actO (GlobalTheory.Grid.neg A) WW g 1 x)) ∧
            ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (X.ideal (locPl G) t)
              (frMapO A WW X.rA.β X.rW.β (actO (GlobalTheory.Grid.neg A) WW g 1 x) i j)
        · have h2 := key g⁻¹ (inv_mem hg) (GlobalTheory.Member.PrincLevel.finCong_inv hgc) _ hx'
          have e' := GlobalTheory.WeilVacMove.actO_inv_actO g (1 : GA D WW) x
          rw [inv_one] at e'
          rw [e'] at h2
          exact h2.symm
        · unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
          rw [if_neg hx, if_neg hx']

end GlobalTheory.StdFstFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitaryConjAtPlaceEqDetLatticeBasisComponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem det_val_conj_inv {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (b Y : GL n R) :
    (b⁻¹ * Y * b⁻¹⁻¹).val.det = Y.val.det := by
  rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_right_comm, ← det_mul, inv_inv, Units.inv_mul, det_one, one_mul]

theorem det_val_reGL {k : Type} [Field k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    (g : GL a k) : (GlobalTheory.StepData.reGL e g).val.det = g.val.det :=
  det_reindex_self e g.val

theorem val_loc {D : D7} (w : Pl D.host.E) {n : ℕ} (g : GL (Fin n) (Lev.EAf D)) :
    (GlobalTheory.StdFrames.loc w g).val = g.val.map (GlobalTheory.StdFrames.cpt w) := rfl

theorem val_finG {D : D7} (V : HSp D) (k : GfC V) :
    (finG V k).val = (Formalism.L2.Theta.mt V (k : GA D V)).map (toEAf D) := rfl

theorem det_mt_conj {D : D7} (V : HSp D) (k u : GfC V) :
    (Formalism.L2.Theta.mt V ((u⁻¹ * k * u : GfC V) : GA D V)).det = (Formalism.L2.Theta.mt V (k : GA D V)).det := by
  have h1 : Formalism.L2.Theta.mt V ((u⁻¹ * k * u : GfC V) : GA D V)
      = (matHom V (u : GA D V))⁻¹.val * Formalism.L2.Theta.mt V (k : GA D V) * (matHom V (u : GA D V)).val := by
    simp [Formalism.L2.Theta.mt, map_mul, map_inv]
  rw [h1, det_mul, det_mul, mul_right_comm, ← det_mul, Units.inv_mul, det_one, one_mul]

theorem det_mt_conj_eq_gdet_kapAt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k u : FinPt G (.top (j + 1))) (w : Pl D.host.E), ((Formalism.L2.Theta.mt (G.V (.top (j + 1))) ((u⁻¹ * k * u : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))).map fun z => GlobalTheory.StdFrames.cpt w (toEAf D z)).det = ((gdet (kapAt S t j hj k w) : (Kw w)ˣ) : Kw w) := by
  intro D T L sc G W U S t j hj k u w
  have hfun : (fun z => GlobalTheory.StdFrames.cpt w (toEAf D z)) = ⇑((GlobalTheory.StdFrames.cpt w).comp (toEAf D)) := rfl
  rw [hfun, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_mt_conj, RingHom.comp_apply]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  rw [kapAt, GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, det_val_reGL, val_loc, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    det_val_conj_inv, val_finG, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

end GlobalTheory.TopLevelInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHilbertModelsOfChoiceClaimsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_hilbertModels_of_choiceClaims : GlobalTheory.Published.CuspRapidDecay → LinK → InjK → ConstK → SumOKK → Formula2K → SumRatK → RatioK → ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.RowClaim.HidaSetting large₂ R F → (∃ ch : GlobalTheory.RowTest.Choice R, ch.Is ∧ ch.AtScale CF large₂.sc.b ∧ ch.FieldOK) → GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R := by
  first | exact @GlobalTheory.RowTestFromClaims.rowTestModel_of_claims | exact GlobalTheory.RowTestFromClaims.rowTestModel_of_claims | (intros; apply GlobalTheory.RowTestFromClaims.rowTestModel_of_claims <;> assumption)
end

