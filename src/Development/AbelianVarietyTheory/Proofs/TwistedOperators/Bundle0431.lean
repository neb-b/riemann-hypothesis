module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFiniteDatumVectorThetaFockVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockRealVec

theorem compAt_central {D : D7} {θ : InfFam D} (τ : D.what₂.Tau) {n : ℕ} (c : AE D) :
    ∃ s : ℂ, compAt θ τ (c • (1 : Matrix (Fin n) (Fin n) (AE D))) = s • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  refine ⟨θ τ (infPart D c), ?_⟩
  ext i j
  by_cases h : i = j
  · subst h; simp [compAt]
  · simp [compAt, h]

theorem vec_theta_fock : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} {N : GlobalTheory.FunObj.Std G U} (Z : GlobalTheory.FunObj.Normal W N) {t : T} {p : GlobalTheory.ChiGrid.Pair T}, GlobalTheory.FunObj.DefPair D.R.m p → ∀ d : GlobalTheory.FunObj.FinDatum G t p, Z.HasVec d → IsThetaFunO W.ψ (G.pS p) (G.pT p) (Z.vec d) ∧ ∀ τ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ τ (cplxO (G.cartS W.cart p τ) (G.onT W.cart p τ)) (Z.vec d) := by
  intro D T L sc G W U N Z t p hp d hv
  obtain ⟨f, hf⟩ := hv
  have hvac := Z.vac_is p hp
  have hψ := hvac.1
  have hV := hvac.2
  have hθ : IsInfFam W.θ := hV.inf
  have hf0 := hV.theta
  have hft : IsThetaFunO W.ψ (G.pS p) (G.pT p) f := GlobalTheory.GalLift.Vec.theta_of_thetaAt hψ hθ hf hf0
  have he : infPart D d.e = 0 := GlobalTheory.PlaceVec.idemSum_infPart d.e_is
  have hfock : ∀ τ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ τ
      (cplxO (G.cartS W.cart p τ) (G.onT W.cart p τ)) f := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ he (GlobalTheory.PlaceVec.infPart_cA he) hf hf0 hft (hV.fock τ)
  have hr : Pair.InRange D.R.m p := by
    have := (DefPair.nodes hp).2
    unfold Pair.InRange
    revert this
    cases p.big <;> simp [DefNode, Node.InRange] <;> omega
  have hW := W.om_is p hr
  have hvec : Z.vec d = W.om p (d.z, 1) f := FinDatum.vec_eq W hf
  rw [hvec]
  refine ⟨hW.om_pres _ _ hft, fun τ z => ?_⟩
  obtain ⟨c, hc⟩ := d.z_cen
  obtain ⟨s, hs⟩ := compAt_central (θ := W.θ) τ (n := (G.pS p).rank) c
  have hS : G.cartS W.cart p τ * compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) d.z) =
      compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) d.z) * G.cartS W.cart p τ := by
    rw [hc, hs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have hc1 : Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p)) = (1 : AE D) • (1 : Matrix _ _ (AE D)) := by
    simp [Formalism.L2.Theta.mt]
  obtain ⟨s', hs'⟩ := compAt_central (θ := W.θ) τ (n := (G.pT p).rank) (1 : AE D)
  have hT : G.onT W.cart p τ * compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p))) =
      compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p))) * G.onT W.cart p τ := by
    rw [hc1, hs', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  obtain ⟨z₀, rfl⟩ : ∃ z₀ : Matrix (Fin (G.pT p).rank) (Fin (G.pS p).rank) ℂ,
      z = compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p))) * z₀ *
        compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) d.z⁻¹) := by
    refine ⟨compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (1 : GA D (G.pT p))⁻¹) * z *
      compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) d.z), ?_⟩
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.mul_one]
  have h0 := congrArg (W.om p (d.z, 1)) (hfock τ z₀)
  rw [GlobalTheory.FockMove.om_annih hW hθ d.z 1 τ hS hT z₀ hft, map_zero] at h0
  exact h0

end GlobalTheory.FockRealVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivRealLineEqSumRealPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer

namespace GlobalTheory.PlaceSum
open GlobalTheory.OrientedHeis GlobalTheory.FockCompare

theorem hD_finset_sum {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (f : G → ℂ) (hf : Sm ι f) {α : Type} (s : Finset α)
    (u : α → R) : hD ι π om (∑ a ∈ s, u a) f = ∑ a ∈ s, hD ι π om (u a) f := by
  funext w
  rw [Finset.sum_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hD_eq_fderiv ι π om f hf, map_sum, ContinuousLinearMap.sum_apply]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]

theorem deriv_heisO_eq_sum_dRho : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ L : ℝ →+ WO S T, Continuous L →
      (∀ t, (L t).map (finPart D) = 0) →
      (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) f w) 0) =
        ∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f := by
  intro D ψ hψ θ hθ S T f hf L hLc hLf
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e1 : (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) f w) 0) =
      hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (L 1)) f :=
    dLine_eq_hD h hψ (L := L) ⟨hLc, hLf⟩ f
  have e2 : ∀ τ, dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f =
      hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1)) f := by
    intro τ
    have hl := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (compAt θ τ (L 1))
    rw [dRho_eq_dLine]
    exact dLine_eq_hD h hψ ⟨hl.1, hl.2.1⟩ f
  have e3 : piW θ T S (L 1) = ∑ τ, piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1) := by
    funext τ' i j
    simp only [Finset.sum_apply]
    have hc : ∀ τ, piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1) τ' i j =
        compAt θ τ' (lineAt θ τ (compAt θ τ (L 1)) 1) i j := fun τ => rfl
    simp only [hc]
    rw [Finset.sum_eq_single τ']
    · rw [(GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ' (compAt θ τ' (L 1))).2.2 1 τ', if_pos rfl, Complex.ofReal_one,
        one_smul]
      rfl
    · intro b _ hb
      rw [(GlobalTheory.WeilVacMove.isLineAt_lineAt hθ b (compAt θ b (L 1))).2.2 1 τ', if_neg (Ne.symm hb)]
      rfl
    · intro hn; exact absurd (Finset.mem_univ τ') hn
  rw [e1, e3, hD_finset_sum _ _ _ f (theta_sm h hf)]
  exact Finset.sum_congr rfl fun τ _ => (e2 τ).symm

end GlobalTheory.PlaceSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceHomLatticeIndexEqLocalComponentIndex
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertHomIdx

open GlobalTheory.FinWeilO

theorem relIndex_map_of_proj {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (A : AddSubgroup X) (φ P : X →+ X) (M : X →+ Y)
    (m : Y →+ Y) (hM : ∀ x, M (φ x) = m (M x)) (hK : ∀ x, M x = 0 → P x = 0) (hPA : ∀ a ∈ A, P a ∈ A)
    (hφ : ∀ a ∈ A, φ a - P (φ a) = a - P a) :
    A.relIndex (A.map φ) = (A.map M).relIndex ((A.map M).map m) := by
  have e1 : (A.map M).map m = (A.map φ).map M := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    exact AddMonoidHom.ext fun x => (hM x).symm
  rw [e1, ← AddSubgroup.relIndex_comap (H := A.map M) M (A.map φ), ← AddSubgroup.inf_relIndex_right A,
    ← AddSubgroup.inf_relIndex_right ((A.map M).comap M)]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  refine ⟨fun h => ⟨⟨x, h.1, rfl⟩, h.2⟩, ?_⟩
  rintro ⟨⟨a, ha, hax⟩, hx⟩
  refine ⟨?_, hx⟩
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : P (a - φ y) = 0 := hK _ (by rw [map_sub, hax, sub_self])
  have h2 : P (φ y) = P a := by rw [map_sub, sub_eq_zero] at h1; exact h1.symm
  have h3 : φ y = (y - P y) + P a := by rw [← hφ y hy, h2]; abel
  rw [h3]
  exact add_mem (sub_mem hy (hPA y hy)) (hPA a ha)

end GlobalTheory.InertHomIdx


open GlobalTheory.FinWeilO in
theorem GlobalTheory.InertHomIdx.idx_latF_moved : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ g : Gv T v, GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v g))) = ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w)).relIndex (((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w)).map (GlobalTheory.InertHomIdx.lmul (locMat D.sp.cm.sig T.gram h g).1)) := by
  intro D S T v w h hi g
  obtain ⟨ε, hns, hp⟩ := GlobalTheory.WeilAtPlace.exists_nonSplit_of_inert hi h
  have hε : IsPlaceIdem D v ε := hns.1
  have hη : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hk : GlobalTheory.WeilParts.SuppPl ε T (embV T v g) := by
    rw [GlobalTheory.PlaceDatum.placeIdem_eq hε hη]
    exact GlobalTheory.PlaceTensor.suppPl_emb T v g
  have hg : GlobalTheory.WeilParts.SuppPl ε S (1 : GA D S) := fun i j => by rw [mt_one, sub_self]; simp
  have hoff := smul_actO (off_smul_mt_place hg) (off_smul_mt_place hk)
  have hmat : (mt T (embV T v g)).map (GlobalTheory.InertHomIdx.compW D w) = (locMat D.sp.cm.sig T.gram h g).1 := by
    have e := finMat_map_compAt D.sp.cm.sig T.gram h (embV T v g)
    rw [proj_emb_self] at e
    exact e
  refine GlobalTheory.InertHomIdx.relIndex_map_of_proj (latF S T (frameLat S) (frameLat T)).toAddSubgroup
    (rhoF S T (1, embV T v g)).toAddMonoidHom (mulF S T (algebraMap (AF D.host.F) (AE D) ε)).toAddMonoidHom
    (GlobalTheory.InertHomIdx.matW S T w) (GlobalTheory.InertHomIdx.lmul (locMat D.sp.cm.sig T.gram h g).1) ?_ ?_ ?_ ?_
  · intro x
    show (actO S T 1 (embV T v g) x).map (GlobalTheory.InertHomIdx.compW D w) = (locMat D.sp.cm.sig T.gram h g).1 * (x : WO S T).map (GlobalTheory.InertHomIdx.compW D w)
    rw [actO, inv_one, mt_one, Matrix.mul_one, Matrix.map_mul, hmat]
  · intro x hx
    refine XF.ext (Matrix.ext fun i j => ?_)
    have h0 : GlobalTheory.InertHomIdx.compW D w ((x : WO S T) i j) = 0 := congrFun (congrFun hx i) j
    show algebraMap (AF D.host.F) (AE D) ε * (x : WO S T) i j = 0
    refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
    · rw [RingHom.map_mul, GlobalTheory.WeilAtPlace.isPrimeIdem_infPart hp, zero_mul, RingHom.map_zero]
    · rw [RingHom.map_mul, finPart_of_isPrimeIdem hp, singleAt_mul, RingHom.map_zero]
      have h1 : compAt D.host.F w (finPart D ((x : WO S T) i j)) = 0 := h0
      rw [h1, mul_zero, ← singleAt_zero]
  · intro a ha
    exact GlobalTheory.PlaceModel.latO_le_top _ (GlobalTheory.PlaceModel.placeIdem_smul_mem hε ha)
  · intro a _
    refine XF.ext ?_
    have := hoff (a : WO S T)
    rw [sub_smul, sub_smul, one_smul, one_smul] at this
    exact this

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DefStep

variable {D : D7}

def finOf (V : HSp D) (g : GA D V) : GfC V := ((GlobalTheory.AdelicSplit.splitEquiv V).symm g).2

def infOf (V : HSp D) (g : GA D V) : GinfC V := ((GlobalTheory.AdelicSplit.splitEquiv V).symm g).1

theorem infOf_mul_finOf (V : HSp D) (g : GA D V) : ((infOf V g : GinfC V) : GA D V) * (finOf V g : GA D V) = g :=
  (GlobalTheory.AdelicSplit.splitEquiv V).apply_symm_apply g

def IsFinReal {V : HSp D} {Wsp : Type} [AddCommGroup Wsp] [Module ℂ Wsp] (ρ : GA D V →* Module.End ℂ Wsp)
    (F : GA D V → ℂ) (Λ : Module.Dual ℂ Wsp) (v : GfC V → Wsp) : Prop :=
  ∀ g, F g = Λ (ρ g⁻¹ (v (finOf V g)))

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def frGL (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (τ : D.what₂.Tau) : GL (Fin (G.V X).rank) ℂ :=
  Formalism.UG.bc (tauE D τ) (fr X)

def realIn (θ : InfFam D) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) :
    GA D (G.V X) →* (D.what₂.Tau → GL (Fin (G.V X).rank) ℂ) :=
  MonoidHom.pi fun τ ↦ (MulAut.conj (frGL fr X τ)⁻¹).toMonoidHom.comp
    ((Pi.evalMonoidHom (fun _ : D.what₂.Tau ↦ GL (Fin (G.V X).rank) ℂ) τ).comp (GlobalTheory.CoefModel.realGL θ (G.V X)))

def realAct (θ : InfFam D) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) :
    GA D (G.V X) →* Module.End ℂ (VV ℂ (wt G X)) :=
  (rhoK (wt G X)).comp (invTrK.comp (realIn θ fr X))

theorem realAct_fin (θ : InfFam D) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) {g : GA D (G.V X)}
    (hg : g ∈ GfC (G.V X)) : realAct θ fr X g = 1 := by
  have h : GlobalTheory.CoefModel.realGL θ (G.V X) g = 1 := by
    funext τ
    show Formalism.UG.bc (θ τ) (infHom (G.V X) g) = 1
    rw [show infHom (G.V X) g = 1 from hg, map_one]
  have h2 : realIn θ fr X g = 1 := by
    funext τ
    simp [realIn, h]
  rw [realAct, MonoidHom.comp_apply, MonoidHom.comp_apply, h2, map_one, map_one]

end GlobalTheory.DefStep

namespace GlobalTheory.DefStep
variable {D : D7}

theorem split_symm_eq (V : HSp D) {g : GA D V} (a : GinfC V) (b : GfC V) (h : (a : GA D V) * b = g) :
    (GlobalTheory.AdelicSplit.splitEquiv V).symm g = (a, b) :=
  (GlobalTheory.AdelicSplit.splitEquiv V).symm_apply_eq.2 h.symm

theorem finOf_fin (V : HSp D) (b : GfC V) : finOf V b = b := by
  rw [finOf, split_symm_eq V 1 b (one_mul _)]

theorem finOf_mul_inf (V : HSp D) (g : GA D V) (k : GinfC V) : finOf V (g * k) = finOf V g := by
  have h : ((infOf V g * k : GinfC V) : GA D V) * (finOf V g : GA D V) = g * k := by
    have hc := GlobalTheory.AdelicSplit.commute_GinfC_GfC V k.2 (finOf V g).2
    conv_rhs => rw [← infOf_mul_finOf V g]
    rw [Subgroup.coe_mul, mul_assoc, hc, ← mul_assoc]
  rw [finOf, split_symm_eq V _ _ h]

theorem finOf_mul_fin (V : HSp D) (g : GA D V) (k : GfC V) : finOf V (g * k) = finOf V g * k := by
  have h : ((infOf V g : GinfC V) : GA D V) * ((finOf V g * k : GfC V) : GA D V) = g * k := by
    rw [Subgroup.coe_mul, ← mul_assoc, infOf_mul_finOf]
  rw [finOf, split_symm_eq V _ _ h]

end GlobalTheory.DefStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunTransportS
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLift

open GlobalTheory.GridJoin

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

structure RowMatchS (ch : Choice R) (G' : GlobalTheory.Grid.GridPre R) : Prop where

  V : ∀ i, i ≤ D.R.m → SameSp (ch.G.V (.grid i 0)) (G'.V i 0).V

  ν : ∀ i, i ≤ D.R.m → HEq (G'.measCol i).ν (ch.M.ν (.grid i 0))

  fd : ∀ i, i ≤ D.R.m → HEq (G'.measCol i).fd (ch.M.fd (.grid i 0))

  ker : ∀ (ρ : ch.G.RealVec) (Φ : ch.G.Datum) (i : Fin D.R.m), ∃ f,
    GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G'.V ((i : ℕ) + 1) 0) (G'.V i 0) f ∧ ∃ p,
      HEq (fun h g => thetaKO (G'.X i 0).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G'.V ((i : ℕ) + 1) 0) (G'.V i 0) f p))
        (fun h g => ch.W.kerA (.right (i : ℕ) 0) (ch.W.datum ρ Φ i) g h)

theorem transport_stepS {A A' B B' : HSp D} (eA : SameSp A' A) (eB : SameSp B' B)
    {ν : Measure (GA D A)} {fd : Set (GA D A)} {ν' : Measure (GA D A')} {fd' : Set (GA D A')}
    (hν : HEq ν ν') (hfd : HEq fd fd') {K : GA D B → GA D A → ℂ} {K' : GA D A' → GA D B' → ℂ}
    (hK : HEq K (fun h g => K' g h)) {φ : GA D A → ℂ} {φ' : GA D A' → ℂ} (hφ : HEq φ φ') {ψ : GA D B → ℂ}
    (hI : ∀ h, IntegrableOn (fun g => K h g * φ g) fd ν) (hE : ∀ h, ∫ g in fd, K h g * φ g ∂ν = ψ h) :
    (∀ h, IntegrableOn (fun g => K' g h * φ' g) fd' ν') ∧ HEq ψ (fun h => ∫ g in fd', K' g h * φ' g ∂ν') := by
  obtain ⟨L, h1, h2, rfl⟩ := eA
  obtain ⟨L', h1', h2', rfl⟩ := eB
  obtain rfl := eq_of_heq hν
  obtain rfl := eq_of_heq hfd
  obtain rfl := eq_of_heq hφ
  obtain rfl := eq_of_heq hK
  exact ⟨hI, heq_of_eq (funext hE).symm⟩

theorem isAutFun_transportS {V V' : HSp D} (e : SameSp V' V) {φ : GA D V → ℂ} {φ' : GA D V' → ℂ} (h : HEq φ φ')
    (hφ : IsAutFun V φ) : IsAutFun V' φ' := by
  obtain ⟨L, h1, h2, rfl⟩ := e
  obtain rfl := eq_of_heq h
  exact ⟨hφ.left, hφ.level, hφ.cont⟩

end GlobalTheory.RowLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMeasDefOfIsTermVol
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

namespace GlobalTheory.RowClaim.TermVolDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

theorem isDefiniteSpace_of_isV {X : LSp D} {ν : ℕ} (h : X.IsV ν 0) : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace X.sp :=
  ⟨h.sigOK, fun τ => Or.inl (by rw [h.sig τ, h.rank, Nat.sub_zero])⟩

theorem isMeasDef_of_isTermVol {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U)
    {μ₀ : T} (hL : L.Is μ₀) (t : T) (Φ : G.Datum) (β : CosFam G t) (M : Vol G) (hM : IsTermVol t S Φ β M) :
    (∀ j (h : j < D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace (G.V (.top j)) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel (G.V (.top j)) (S.levTop t Φ β j h) ∧
      IsMeasDef (G.V (.top j)) (S.levTop t Φ β j h) (M.ν (.top j)) (M.fd (.top j))) ∧
    ∀ i (h : i ≤ D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace (G.V (.grid i D.R.m)) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel (G.V (.grid i D.R.m)) (S.levRow t i h) ∧
      IsMeasDef (G.V (.grid i D.R.m)) (S.levRow t i h) (M.ν (.grid i D.R.m)) (M.fd (.grid i D.R.m)) := by
  refine ⟨fun j h => ⟨?_, S.isCO_levTop W t Φ β h, ?_⟩, fun i h => ⟨?_, S.isCO_levRow W t h, ?_⟩⟩
  · exact isDefiniteSpace_of_isV (node_isV G hL (X := .top j) h.le)
  · have e := hM.1 j h
    unfold Vol.IsAt at e
    rw [if_pos (by simp [Node.neg])] at e
    exact e
  · have hV := node_isV G hL (X := .grid i D.R.m) ⟨h, le_rfl⟩
    have e : Node.neg D.R.m (.grid i D.R.m) = 0 := by simp [Node.neg]
    rw [e] at hV
    exact isDefiniteSpace_of_isV hV
  · have e := hM.2 i h
    unfold Vol.IsAt at e
    rw [if_pos (by simp [Node.neg])] at e
    exact e

end GlobalTheory.RowClaim.TermVolDef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelTowerConvergence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowConvAll

theorem multT_le_empty {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) : MultT θ M J χ ≤ MultT θ M ∅ 1 := by
  intro x hx
  rw [mem_multT] at hx ⊢
  refine Submodule.span_mono ?_ hx
  intro T hT
  exact ⟨hT.aut, hT.cusp, fun v k hk => absurd hk (Set.notMem_empty k), hT.equiv, hT.cont⟩

end GlobalTheory.RowConvAll

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ExpansionInvariance

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def pairPts (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  τ.sum fun d a => a • (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
    (S.colMap d x) (S.rowMap d y)

end GlobalTheory.ExpansionInvariance
end
end

