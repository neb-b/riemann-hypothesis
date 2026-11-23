module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0105
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedDefiniteKernelEntriesIsAlgebraic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj
open Formalism.L2.Ker MvPolynomial

noncomputable section

namespace GlobalTheory.KernelAlg


open GlobalTheory.ThetaAlgebraic in
theorem coefIn_dict (D : D7) (hI : GlobalTheory.NormSum.Inp D) {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (hC : StandardLatticesGL3.Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t0) {N N' : ℕ} (e0 : TaylorLogMetric.VC D N N' → ℂ)
    (he : StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) t0 (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') e0)
    (Ls : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (κ : ℂ) (hκ : κ ∈ TaylorLogMetric.Qbar) {n : ℕ} (r : Fin n → TaylorLogMetric.Qbar) (s : Fin n → TaylorLogMetric.VC D N N') (k : ℕ) (hk : 0 < k)
    (hs : ∀ i, k • s i ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) Ls Lt) :
    TaylorLogMetric.CoefIn D (fun z => κ * ∑ i, (r i : ℂ) * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (s i)
      (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.La0 D (TaylorLogMetric.tor0 D cc δ) N N') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) Ls Lt) e0) z) TaylorLogMetric.Qbar := by
  obtain ⟨b, κ0, hb, hκ0, rfl⟩ := he
  have hG := hI.g1
  have hU := hI.use1
  have hg := ((good_theta hG hU hC hb ht).iop hG hC hb (StandardLatticesGL3.LaB D (TaylorLogMetric.tor0 D cc δ) b) _
    (la_le cc δ hG hb (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).const_mul hκ0.1
  have hg2 := hg.iop hG hC hb (StandardLatticesGL3.La0 D (TaylorLogMetric.tor0 D cc δ) N N') _ (la_le cc δ hG hb Ls Lt)
  have hT : ∀ i, Good cc δ b (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (s i)
      (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.La0 D (TaylorLogMetric.tor0 D cc δ) N N') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) Ls Lt)
        fun z => κ0 * TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.LaB D (TaylorLogMetric.tor0 D cc δ) b) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
          (StandardLatticesGL3.pullB D (TaylorLogMetric.tor0 D cc δ) b (GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) t0)) z)) := fun i =>
    hg2.transl hG hC hb (sat_of_nsmul hk (la_le cc δ hG hb Ls Lt (hs i)))
  exact ((Good.sum Finset.univ _ fun i _ => (hT i).const_mul (r i).2).const_mul hκ).coefIn

theorem applyAt0_monomial_mem (D : D7) {N N' : ℕ} (m : GL3Theta.Idx D N N' →₀ ℕ) {G : TaylorLogMetric.VC D N N' → ℂ}
    (hG : TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar) : GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) G ∈ TaylorLogMetric.Qbar := by
  classical
  unfold GL3Theta.applyAt0
  refine sum_mem fun α _ => mul_mem (mul_mem ?_ (prod_mem fun _ _ => natCast_mem _ _)) (hG α)
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem opp_isAlgebraic {T : Type} (p : GlobalTheory.ChiGrid.Pair T) {z : ℂ} (hz : IsAlgebraic ℚ z) : IsAlgebraic ℚ (opp p z) :=
  IsAlgebraic.algHom (opp p).toRatAlgHom hz

theorem fvar_fst {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) (p : GlobalTheory.ChiGrid.Pair T)
    (k : DVar D.what₂.Tau (G.V p.small).rank (G.V p.big).rank) : (fvar G p k).1 = k.1 := by
  cases p <;> rfl

theorem kk_isAlgebraic : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → GlobalTheory.NormSum.Inp D → GlobalTheory.SumSize.DictAt ch → ∀ (t : T) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p → WtOK ch.G p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 → d.P = locPl ch.G t → ch.S.Z.HasVec d → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (a : VVIdx (wt ch.G p.big)) (b : VVIdx (wt ch.G p.small)), IsAlgebraic ℚ (ch.S.Z.kk d x y a b) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hS ch hch hInp hDict t p hp hW k d hk hcos hz hP hV x y a b
  obtain ⟨Ls, Lt, κ, n, r, s, hLs, hLt, hκ, hs, -, -, -, hJ⟩ := hDict t p hp k d hk hcos hz hP x y
  set Z := ch.S.Z
  have hF := coefIn_dict D hInp Z.crv Z.pt0 (Z.e0 p) (Z.e0_is p hp).2.2.2.1 Ls Lt κ hκ.1 r s k hk hs
  set FF := (fun z => κ * ∑ i, ((r i : TaylorLogMetric.Qbar) : ℂ) * TaylorLogMetric.U D (TaylorLogMetric.tor0 D D.host.ccK Z.δ) (s i)
      (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D D.host.ccK Z.δ) (StandardLatticesGL3.La0 D (TaylorLogMetric.tor0 D D.host.ccK Z.δ) _ _)
        (TaylorLogMetric.La D (TaylorLogMetric.tor0 D D.host.ccK Z.δ) Ls Lt) (Z.e0 p)) z) with hFF
  set J2 : (DVar D.what₂.Tau (ch.G.V p.small).rank (ch.G.V p.big).rank →₀ ℕ) → ℂ := fun m =>
    opp p (GL3Theta.applyAt0 D (MvPolynomial.monomial (m.mapDomain (fvar ch.G p)) 1) FF) with hJ2
  have hA : ∀ m, IsAlgebraic ℚ (J2 m) := fun m =>
    opp_isAlgebraic p (mem_algebraicClosure_iff.1 (applyAt0_monomial_mem D _ hF))
  set c : D.what₂.Tau → ℂ := fun τ => opp p (period Z.δ τ) with hc
  have hJf : jetTab ch.W ch.S.N.frC p (Z.vec d) (x * ch.S.N.u _) (y * ch.S.N.u _) =
      fun m => (Z.c0 p : ℂ) * ((m.prod fun k e => c k.1 ^ e) * J2 m) := by
    funext m
    rw [hJ m, map_mul]
    congr 2
    rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), map_finsuppProd]
    simp only [map_pow, fvar_fst, hc]
  have hop : ∀ P : Formalism.L2.DIV.VV ℂ (wt ch.G p.small),
      jetOp (wt ch.G p.small) (wt ch.G p.big) (jetTab ch.W ch.S.N.frC p (Z.vec d) (x * ch.S.N.u _) (y * ch.S.N.u _))
        (nuEnd ch.G p) P = ((Z.c0 p : ℂ) * ∏ τ, c τ ^ fockDeg ch.G p τ) • jetOp _ _ J2 (nuEnd ch.G p) P := by
    intro P
    rw [hJf]
    simp only [jetOp, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [_root_.GlobalTheory.JetScale.jetMap_weight_scale, GlobalTheory.T.blockAction_diagonal_coefficientSpace_smul _ _ _ (hW.2 J2 P.1 P.2), smul_smul, map_smul]
    rfl
  simp only [Normal.kk, Normal.kkIn, Normal.kkMap, LinearMap.toMatrix_apply, LinearMap.smul_apply, fockComp]
  rw [hop, map_smul, map_smul]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  have hR := _root_.GlobalTheory.JetAlg.repr_jetOp_isAlgebraic _ _ J2 (nuEnd ch.G p) hA hW.2 a b
  have e : Z.scal 1 p * ((Z.c0 p : ℂ) * ∏ τ, c τ ^ fockDeg ch.G p τ) =
      ∏ τ, opp p ((1 / period Z.δ τ) * period Z.δ τ) ^ fockDeg ch.G p τ := by
    simp only [Normal.scal, Pi.one_apply, hc, map_mul, mul_pow, Finset.prod_mul_distrib]
    rw [mul_mul_mul_comm, Units.inv_mul, one_mul]
  have hK : Z.scal 1 p * ((Z.c0 p : ℂ) * ∏ τ, c τ ^ fockDeg ch.G p τ) ∈ TaylorLogMetric.Qbar := by
    rw [e]
    refine prod_mem fun τ _ => pow_mem ?_ _
    rw [mem_algebraicClosure_iff]
    apply opp_isAlgebraic
    by_cases h : period Z.δ τ = 0
    · simp [h, isAlgebraic_zero]
    · simp [h, isAlgebraic_one]
  rw [← mul_assoc, ← mem_algebraicClosure_iff]
  exact mul_mem hK (mem_algebraicClosure_iff.2 hR)

end GlobalTheory.KernelAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  add_mem' := by
    intro f g hf hg
    obtain ⟨U₁, hU₁, h₁⟩ := hf.level
    obtain ⟨U₂, hU₂, h₂⟩ := hg.level
    refine ⟨fun γ w => ?_, ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun u hu hu0 => ?_⟩, hf.cont.add hg.cont,
      fun k L hL h0 w => (hf.smooth k L hL h0 w).add (hg.smooth k L hL h0 w)⟩
    · simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    · funext w
      have e₁ := congrFun (h₁ u hu.1 hu0) w
      have e₂ := congrFun (h₂ u hu.2 hu0) w
      simp only [heisO, Pi.add_apply] at e₁ e₂ ⊢
      rw [mul_add, e₁, e₂]
  zero_mem' := ⟨fun γ w => by simp, ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun u _ _ => by funext w; simp [heisO]⟩, continuous_const,
    fun k L hL h0 w => contDiff_const⟩
  smul_mem' := by
    intro c f hf
    obtain ⟨U₁, hU₁, h₁⟩ := hf.level
    refine ⟨fun γ w => ?_, ⟨U₁, hU₁, fun u hu hu0 => ?_⟩, hf.cont.const_smul c,
      fun k L hL h0 w => (hf.smooth k L hL h0 w).const_smul c⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf.quasi]; ring
    · funext w
      have e₁ := congrFun (h₁ u hu hu0) w
      simp only [heisO, Pi.smul_apply, smul_eq_mul] at e₁ ⊢
      rw [← e₁]; ring


variable (t : T) in
def positionPair (m : ℕ) : Fin m ⊕ Fin m → Pair T
  | .inl j => .top t j
  | .inr i => .chi i m


variable (G) in
abbrev FactorFn (t : T) (a : Fin D.R.m ⊕ Fin D.R.m) : Type :=
  WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) → ℂ

def vecOf (S : GridChoice W U) {t : T} (d : PureDat G t) : ∀ a, FactorFn G t a
  | .inl j => S.Z.vec (d.1 j)
  | .inr i => S.Z.vec (d.2 i)

def kkV (S : GridChoice W U) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (a : FinPt G p.small) (b : FinPt G p.big) :
    VV ℂ (wt G p.small) →ₗ[ℂ] VV ℂ (wt G p.big) :=
  S.Z.scal 1 p • fockComp W S.N.frC p f (a * S.N.u _) (b * S.N.u _)

def colV (S : GridChoice W U) {t : T} (v : ∀ a, FactorFn G t a) (x : ∀ j, FinPt G (.top j)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then kkV S (.top t j) (v (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowV (S : GridChoice W U) {t : T} (v : ∀ a, FactorFn G t a) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (v (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

def pairFn (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (v : ∀ a, FactorFn G t a) : VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂ (colV S v x) (rowV S v y)

theorem pairPts_eq_sum (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (x : ∀ j, FinPt G (.top j))
    (y : ∀ i, FinPt G (.grid i D.R.m)) : pairPts S τ x y = τ.sum fun d c => c • pairFn S x y (vecOf S d) := rfl

def moved (S : GridChoice W U) (j : ℕ) (k : FinPt G (.grid (j + 1) D.R.m)) : GA D (G.V (.grid (j + 1) D.R.m)) :=
  ((S.N.u (.grid (j + 1) D.R.m))⁻¹ * k * S.N.u (.grid (j + 1) D.R.m) : FinPt G (.grid (j + 1) D.R.m))

def moveV (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) : ∀ a, FactorFn G t a :=
  Function.update
    (Function.update v (.inr ⟨j, by omega⟩)
      (W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (v (.inr ⟨j, by omega⟩)) : FactorFn G t (.inr ⟨j, by omega⟩)))
    (.inr ⟨j + 1, hj⟩)
    (W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (v (.inr ⟨j + 1, hj⟩)) : FactorFn G t (.inr ⟨j + 1, hj⟩))

end GlobalTheory.RowVertexInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvZipFock
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem pathConv_zip_fock (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (hC : CuspStep W M ρ t) {X : Node} :
    ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p → ∀ (φ d : PureT G p), VecAll ρ e p φ d →
      ∀ (P' : PolT G p) (F : Fn G X), IsCuspListed W.θ X F →
      PathConv W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') F ∧
      IsCuspListed W.θ Y (liftP W M p (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') F) := by
  intro Y p
  induction p with
  | nil =>
    intro _ _ _ _ _ _ hF
    exact ⟨trivial, hF⟩
  | snoc a p ih =>
    intro hg φ d hv P' F hF
    have hg' : OnGrid D.R.m t p := fun b hb => hg b (List.mem_append_left [a] hb)
    have ha : IsGridArrow D.R.m t a := hg a (List.mem_append_right p.arrows (List.mem_singleton_self a))
    obtain ⟨h1, h2⟩ := ih hg' φ.1 d.1 hv.1 P'.1 F hF
    obtain ⟨h3, h4⟩ := hC a ha e he φ.2 d.2 hv.2 P'.2 _ h2
    exact ⟨⟨h1, h3⟩, h4⟩

theorem mem_support_tensT {X Y : Node} {p : Path T X Y} (τi : PolT G p →₀ ℂ) (τf : TotT G p) (x : PureT G p)
    (hx : x ∈ (tensT W τi τf).support) :
    ∃ d ∈ τf.support, ∃ P' : PolT G p, x = Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P' := by
  classical
  unfold tensT at hx
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hx)
  obtain ⟨d, hd, hx'⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  exact ⟨d, hd, P, Finset.mem_singleton.1 (Finsupp.support_single_subset hx')⟩

theorem totConv_tensE : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (M : Vol G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → ∀ (τ : TotT G p) (φ : PureT G p → PureT G p), (∀ d ∈ τ.support, GlobalTheory.FlipRun.VecAll ρ e p (φ d) d) → ∀ F : Fn G X, GlobalTheory.FlipRun.IsCuspListed W.θ X F → ∀ Q : GlobalTheory.FlipRun.PolE G →₀ ℂ, TotConv W M p (GlobalTheory.FlipRun.tensE W p Q τ) F := by
  intro D T L sc G W M ρ t e he hC X Y p hg τ φ hv F hF Q x hx
  obtain ⟨d, hd, P', rfl⟩ := mem_support_tensT _ τ x hx
  exact (pathConv_zip_fock M ρ t he hC p hg (φ d) d (hv d hd) P' F hF).1

end GlobalTheory.FlipRun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodsOnLineOfInvLine
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def InvLine (ch : Choice R) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (S : Sizes) (P : ι → Entries S), (∀ τ, (P τ).Good) ∧
    ∃ e : PolCol ch.G × PolRow ch.G → OM P, ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
      IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y,
        ∃ l ∈ invFun (omRep P), ∀ Q, defPer t ch.S.toGridChoice M Q d (colFn ch a) (formTop ch t y) = l (e Q)

theorem periodsOnLine_of_invLine (hL : OneLine) (ch : Choice R) (h : InvLine ch) : PeriodsOnLine ch := by
  obtain ⟨ι, _, _, S, P, hP, e, he⟩ := h
  have : Module.Free ℂ (invFun (omRep P)) := Module.Free.of_divisionRing ℂ _
  obtain ⟨L0, -, hL0⟩ := finrank_eq_one_iff'.1 (hL ι S P hP)
  refine ⟨fun Q => L0.1 (e Q), fun t a hS β hβ M hM τ hτ d hd y => ?_⟩
  obtain ⟨l, hl, hle⟩ := he t a hS β hβ M hM τ hτ d hd y
  obtain ⟨c, hc⟩ := hL0 ⟨l, hl⟩
  refine ⟨c, fun Q => ?_⟩
  have hc' : c • L0.1 = l := congrArg Subtype.val hc
  rw [hle Q, ← hc']
  rfl

end GlobalTheory.RowReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceModelOntoLocal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SymmetricBilinearHalf

variable {D : D7}

theorem sb_zero {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf e Λ 0 :=
  ⟨fun _ h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun _ h => absurd rfl h⟩

theorem sb_smul {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ : Mx D m n → ℂ} (c : ℂ)
    (h : IsSBHalf e Λ Φ) : IsSBHalf e Λ (c • Φ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  have ne : ∀ t, (c • Φ) t ≠ 0 → Φ t ≠ 0 := fun t ht h0 => ht (by rw [Pi.smul_apply, h0, smul_zero])
  exact ⟨fun t ht => h1 t (ne t ht), k, hk, fun u hu hh t => by rw [Pi.smul_apply, Pi.smul_apply, h2 u hu hh t],
    fun t ht => h3 t (ne t ht)⟩

theorem half_nsmul {m n : ℕ} {e : AE D} {u : Mx D m n} (k : ℕ) (h : IsHalf e u) : IsHalf e (k • u) := by
  rw [GlobalTheory.SplitScalar.isHalf_iff] at h ⊢
  rw [smul_comm, h]

theorem sb_add {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ Ψ : Mx D m n → ℂ}
    (h : IsSBHalf e Λ Φ) (h' : IsSBHalf e Λ Ψ) : IsSBHalf e Λ (Φ + Ψ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  obtain ⟨h1', k', hk', h2', h3'⟩ := h'
  have ne : ∀ t, (Φ + Ψ) t ≠ 0 → Φ t ≠ 0 ∨ Ψ t ≠ 0 := fun t ht => by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    exact ht (by rw [Pi.add_apply, hc.1, hc.2, add_zero])
  refine ⟨fun t ht => (ne t ht).elim (h1 t) (h1' t), k * k', Nat.mul_pos hk hk', fun u hu hh t => ?_,
    fun t ht => ?_⟩
  · have e1 : Φ (t + (k * k') • u) = Φ t := by
      rw [mul_smul]; exact h2 _ (Λ.nsmul_mem hu k') (half_nsmul k' hh) t
    have e2 : Ψ (t + (k * k') • u) = Ψ t := by
      rw [mul_comm, mul_smul]; exact h2' _ (Λ.nsmul_mem hu k) (half_nsmul k hh) t
    rw [Pi.add_apply, Pi.add_apply, e1, e2]
  · rcases ne t ht with h | h
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem (h3 t h) k'
    · rw [mul_smul]; exact Λ.nsmul_mem (h3' t h) k

theorem wAt_of_half {m n : ℕ} {p : Place D} {a c : AE D} (hac : a * c = 0) (hs : a + c = idem D p)
    {x : Mx D m n} (hx : IsHalf a x) : wAt p x = x := by
  funext i j
  show idem D p * x i j = x i j
  have := hx i j
  rw [← hs]
  linear_combination (1 - c) * this + (x i j) * hac

theorem placeModel_onto_local : ∀ (D : Formalism.BasicNotions.D7) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥(Formalism.BasicNotions.D7.host D).F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (S T : Formalism.BasicNotions.TH.HSp D) (sS : Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.what₂ D) → Matrix (Fin (Formalism.BasicNotions.HSpace.rank S)) (Fin (Formalism.BasicNotions.HSpace.rank S)) ℂ) (sT : Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.what₂ D) → Matrix (Fin (Formalism.BasicNotions.HSpace.rank T)) (Fin (Formalism.BasicNotions.HSpace.rank T)) ℂ) (ΛS : Submodule (NumberField.RingOfIntegers (Formalism.BasicNotions.D7.host D).E) (Fin (Formalism.BasicNotions.HSpace.rank S) → (Formalism.BasicNotions.D7.host D).E)) (ΛT : Submodule (NumberField.RingOfIntegers (Formalism.BasicNotions.D7.host D).E) (Fin (Formalism.BasicNotions.HSpace.rank T) → (Formalism.BasicNotions.D7.host D).E)) (f₀ : Formalism.IndefR.Datum.WO S T → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.FinPl D) (a : Formalism.L2.Theta.AE D), Formalism.L2.Theta.IsSplitIdem D a → a + (Formalism.L2.Theta.cA D) a = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (Sum.inl v) → (∃ (Tm : (Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ) →ₗ[ℂ] Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ), Formalism.IndefR.Datum.IsPlaceModel ψ (Formalism.IndefR.Datum.symplO S T) (Formalism.IndefR.Datum.heisO ψ S T) a (Formalism.IndefR.Datum.latO S T ↑ΛS ↑ΛT fun (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Formalism.BasicNotions.D7.host D).F)) ↦ True) (1 : ℂ) f₀ Tm) ∧ ∀ (Tm : (Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ) →ₗ[ℂ] Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ), Formalism.IndefR.Datum.IsPlaceModel ψ (Formalism.IndefR.Datum.symplO S T) (Formalism.IndefR.Datum.heisO ψ S T) a (Formalism.IndefR.Datum.latO S T ↑ΛS ↑ΛT fun (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Formalism.BasicNotions.D7.host D).F)) ↦ True) (1 : ℂ) f₀ Tm → (∀ (Φ : Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ), Formalism.IndefR.Datum.IsSBHalf a (Formalism.IndefR.Datum.latO S T ↑ΛS ↑ΛT fun (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Formalism.BasicNotions.D7.host D).F)) ↦ True) Φ → GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsLocal ψ θ S T sS sT ΛS ΛT (Sum.inl v) (Tm Φ)) ∧ ∀ (x : Formalism.IndefR.Datum.WO S T → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsLocal ψ θ S T sS sT ΛS ΛT (Sum.inl v) x → ∃ (Φ : Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ), Formalism.IndefR.Datum.IsSBHalf a (Formalism.IndefR.Datum.latO S T ↑ΛS ↑ΛT fun (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Formalism.BasicNotions.D7.host D).F)) ↦ True) Φ ∧ Tm Φ = x := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ hb v a ha hs
  have h1 : a * a = a := ha.1
  have h2 : a * cA D a = 0 := ha.2.1
  have c1 : cA D a * cA D a = cA D a := by rw [← map_mul, h1]
  have hψ := base_std hb
  have hθ := base_inf hb
  have hS := hb.2.2.1
  have hT := hb.2.2.2.1
  obtain ⟨hgen, hspan⟩ := _root_.GlobalTheory.PlaceTensor.halfWaves_span D ψ S T ΛS ΛT hψ hS hT a h1 h2 (GlobalTheory.PlaceModelSum.infPart_split ha)
  have st := fun f (hf : IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) f) =>
    (_root_.GlobalTheory.PlaceStable.heis_stable D ψ θ S T sS sT ΛS ΛT hψ hθ f hf.1).2 (.inl v) hf
  have l0 := base_isLocal hb (.inl v)
  have lz : IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) 0 := by
    have := (st f₀ l0).2.1 (-1) f₀ l0
    rwa [neg_one_smul, neg_add_cancel] at this
  refine ⟨?_, fun Tm hTm => ⟨fun Φ hΦ => ?_, fun x hx => ?_⟩⟩
  · have ho : GlobalTheory.PlaceModelSum.IsOrthSum a :=
      ⟨Unit, {()}, fun _ => a, fun _ _ => ha, fun _ _ _ _ h => absurd rfl h, by rw [Finset.sum_singleton]⟩
    exact ho.exists_model hψ hS hT h2 hb.2.2.2.2.2.lat
  · refine Submodule.span_induction (p := fun Φ _ => IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) (Tm Φ))
      ?_ ?_ ?_ ?_ (hspan Φ hΦ)
    · rintro _ ⟨x, y, hx, hy, rfl⟩
      rw [(hgen x y hx hy).2 f₀ Tm hTm]
      have e1 := (st f₀ l0).1 x
      rw [wAt_of_half h2 hs hx] at e1
      have e2 := (st _ e1).1 y
      rwa [wAt_of_half ((mul_comm _ _).trans h2) ((add_comm _ _).trans hs) hy] at e2
    · rw [map_zero]; exact lz
    · intro x y _ _ hx hy
      have := (st _ hx).2.1 1 _ hy
      rw [one_smul] at this
      rw [map_add (f := _)]; exact this
    · intro c x _ hx
      have := (st _ hx).2.1 c _ lz
      rw [add_zero] at this
      rw [map_smul]; exact this
  · refine Submodule.span_induction
      (p := fun x _ => ∃ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ ∧ Tm Φ = x)
      ?_ ?_ ?_ ?_ (GlobalTheory.T.localFactor_mem_span_localHeisenbergTranslates D ψ θ S T sS sT ΛS ΛT f₀ hb v x hx)
    · rintro _ ⟨w, rfl⟩
      have hx : IsHalf a (a • w) := by rw [GlobalTheory.SplitScalar.isHalf_iff, smul_smul, h1]
      have hy : IsHalf (cA D a) (cA D a • w) := by rw [GlobalTheory.SplitScalar.isHalf_iff, smul_smul, c1]
      obtain ⟨g1, g2⟩ := hgen _ _ hx hy
      refine ⟨_, sb_smul (ψ (-symplOH S T (cA D a • w) (a • w))) g1, ?_⟩
      rw [map_smul, g2 f₀ Tm hTm, GlobalTheory.SplitScalar.heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel,
        AddChar.map_zero_eq_one, one_smul, ← add_smul, add_comm, hs]
      rfl
    · exact ⟨0, sb_zero _ _, map_zero _⟩
    · rintro _ _ _ _ ⟨Φ, hΦ, rfl⟩ ⟨Ψ, hΨ, rfl⟩
      exact ⟨Φ + Ψ, sb_add hΦ hΨ, map_add _ _ _⟩
    · rintro c _ _ ⟨Φ, hΦ, rfl⟩
      exact ⟨c • Φ, sb_smul c hΦ, map_smul _ _ _⟩

end GlobalTheory.SymmetricBilinearHalf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealActionOnVertexWeightContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RealActCont

theorem realAct_inv_continuous : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (θ : InfFam D), IsInfFam θ →
    ∀ (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (Λ : Module.Dual ℂ (VV ℂ (wt G X))) (w : VV ℂ (wt G X)),
    Continuous fun k : GinfC (G.V X) => Λ (realAct θ fr X ((k : GA D (G.V X))⁻¹) w) := by
  intro D T L sc G θ hθ fr X Λ w
  classical
  obtain ⟨hc, -⟩ := GlobalTheory.CoefModel.realGL_laws hθ (G.V X)
  have hG : ∀ _τ : D.what₂.Tau, (1 : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ).PosDef := fun _ => Matrix.PosDef.one
  let A : GinfC (G.V X) → D.what₂.Tau → GL (Fin (G.V X).rank) ℂ :=
    fun k => invTrK (realIn θ fr X ((k : GA D (G.V X))⁻¹))
  have hA : ∀ τ, Continuous fun k => (A k τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) := by
    intro τ
    have e : ∀ k : GinfC (G.V X), (A k τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) =
        Matrix.transpose ((((frGL fr X τ)⁻¹ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) *
          Formalism.L2.Pj.archM (G.V X) (θ τ) (k : GA D (G.V X)) * (frGL fr X τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ)) := by
      intro k
      simp only [A, map_inv]
      show ((((realIn θ fr X (k : GA D (G.V X)) τ)⁻¹)⁻¹ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ).transpose = _
      rw [inv_inv]
      simp [realIn, MulAut.conj_apply, GlobalTheory.CoefModel.realGL_coe]
    refine Continuous.congr ?_ fun k => (e k).symm
    exact ((continuous_const.mul ((hc τ).comp continuous_subtype_val)).mul continuous_const).matrix_transpose
  have key := GlobalTheory.CoefModel.continuous_rhoH (wt G X) hG A hA (GlobalTheory.CoefModel.toHilb (wt G X) hG w)
  have hΛ : Continuous (Λ ∘ₗ (GlobalTheory.CoefModel.toHilb (wt G X) hG).symm.toLinearMap) :=
    LinearMap.continuous_of_finiteDimensional _
  refine (hΛ.comp key).congr fun k => ?_
  simp only [Function.comp_apply, GlobalTheory.CoefModel.rhoH_toHilb, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

end GlobalTheory.RealActCont
end

