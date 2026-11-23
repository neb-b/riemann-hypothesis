module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanCoordinateActionSymplectic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorLift
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitDetChr

open GlobalTheory.LFun GlobalTheory.Doubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_inFin (v : Pl (F := F)) (a : Fv F v) : At (evFin F v) (inFin v a) := by
  intro u hu
  have h := GlobalTheory.InertDetChr.at_inFin_one (F := F) v u hu
  rw [smul_eq_mul] at h ⊢
  rw [show a = 1 * a from (one_mul a).symm, inFin_mul, ← mul_assoc, h, zero_mul]

theorem compFin_smul_inclR (v : Pl (F := F)) (a : AF F) (y : E) :
    compFin F E v (a • inclR (F := F) (AF F) y) = evFin F v a ⊗ₜ[F] y := by
  rw [Algebra.smul_def, map_mul, GlobalTheory.InertDetChr.compFin_algebraMap]
  have : compFin F E v (inclR (F := F) (AF F) y) = (1 : Fv F v) ⊗ₜ[F] y := by
    show Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] y) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
  rw [this]
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem comp_mem_latLoc {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)}
    (hz : z ∈ GlobalTheory.InertSph.latAt W v) : compFin F E v ∘ z ∈ latLoc F W.L v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, y, hy, rfl⟩ := hz
    convert tmul_mem_latLoc ha hy using 1
    funext i
    exact compFin_smul_inclR v a (y i)
  | zero =>
    convert zero_mem (latLoc F W.L v) using 1
    funext i; exact map_zero _
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    funext i; exact map_add _ _ _
  | neg x _ hx =>
    convert neg_mem hx using 1
    funext i; exact map_neg _ _

theorem mulVec_mem_latLoc {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (g : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hg : ∀ z ∈ GlobalTheory.InertSph.latAt W v, g *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ∀ y ∈ latLoc F W.L v, (compFin F E v).mapMatrix g *ᵥ y ∈ latLoc F W.L v := by
  intro y hy
  refine latLoc_induction (p := fun y => (compFin F E v).mapMatrix g *ᵥ y ∈ latLoc F W.L v)
    (fun a ha x hx => ?_) (by rw [Matrix.mulVec_zero]; exact zero_mem _)
    (fun _ _ h h' => by rw [Matrix.mulVec_add]; exact add_mem h h')
    (fun _ h => by rw [Matrix.mulVec_neg]; exact neg_mem h) hy
  have hz : (inFin v a • fun i => inclR (F := F) (AF F) (x i)) ∈ GlobalTheory.InertSph.latAt W v :=
    AddSubgroup.subset_closure ⟨inFin v a, at_inFin v a, by rwa [GlobalTheory.InertDetChr.evFin_inFin_self], x, hx, rfl⟩
  have e1 : (fun i => a ⊗ₜ[F] x i) = compFin F E v ∘ (inFin v a • fun i => inclR (F := F) (AF F) (x i)) := by
    funext i
    show _ = compFin F E v (inFin v a • inclR (F := F) (AF F) (x i))
    rw [compFin_smul_inclR, GlobalTheory.InertDetChr.evFin_inFin_self]
  rw [e1]
  have e2 : (compFin F E v).mapMatrix g *ᵥ (compFin F E v ∘ (inFin v a • fun i => inclR (F := F) (AF F) (x i))) =
      compFin F E v ∘ (g *ᵥ (inFin v a • fun i => inclR (F := F) (AF F) (x i))) :=
    funext fun i => (RingHom.map_mulVec (compFin F E v) g _ i).symm
  rw [e2]
  exact comp_mem_latLoc W v (hg _ hz)

theorem det_mem_intLoc {d : ℕ} {L : Submodule (𝓞 E) (Fin d → E)} {v : Pl (F := F)} (P : GL (Fin d) (Fv F v ⊗[F] E))
    (hP : ∀ y : Fin d → Fv F v ⊗[F] E, (∀ i, y i ∈ intLoc F E v) ↔ P.1 *ᵥ y ∈ latLoc F L v)
    (g : GL (Fin d) (Fv F v ⊗[F] E)) (hg : ∀ y ∈ latLoc F L v, g.1 *ᵥ y ∈ latLoc F L v) :
    ((Matrix.GeneralLinearGroup.det g : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v := by
  set Q : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E) := (P⁻¹ * g * P).1 with hQ
  have hent : ∀ i j, Q i j ∈ intLoc F E v := by
    intro i j
    have h1 : P.1 *ᵥ (Pi.single j 1) ∈ latLoc F L v := (hP _).1 (fun k => by
      by_cases e : k = j
      · subst e; simp
      · simp [e])
    have h2 := (hP (Q *ᵥ Pi.single j 1)).2 (by
      rw [hQ, Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, mul_inv_cancel_left, Units.val_mul,
        ← Matrix.mulVec_mulVec]
      exact hg _ h1)
    have := h2 i
    rwa [Matrix.mulVec_single_one, Matrix.col_apply] at this
  let Q' : Matrix (Fin d) (Fin d) (intLoc F E v) := fun i j => ⟨Q i j, hent i j⟩
  have hQ' : (intLoc F E v).subtype.mapMatrix Q' = Q := rfl
  have hdet : Q.det = ((Matrix.GeneralLinearGroup.det g : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
    rw [hQ, ← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_inv,
      mul_comm _ (Matrix.GeneralLinearGroup.det P), ← mul_assoc, mul_inv_cancel, one_mul]
  rw [← hdet, ← hQ', ← RingHom.map_det]
  exact (Matrix.det Q').2

end GlobalTheory.SplitDetChr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VertexLatticeCoordsRationalPointMulEqCoordMatrix
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets

noncomputable section
namespace GlobalTheory.RatMoveLat
open Matrix

theorem mem_globLat_rat {D : D7} {n : ℕ} (a g : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (M : Matrix (Fin n) (Fin n) D.host.E)
    (ha : a.1 = M.map (Formalism.IndefR.Datum.eToEAf D)) (C : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (y : Fin n → D.host.E) :
    M *ᵥ y ∈ Formalism.UG.CS.globLat (a * g) C ↔ y ∈ Formalism.UG.CS.globLat g C := by
  have hv : (fun i => Formalism.IndefR.Datum.eToEAf D ((M *ᵥ y) i)) =
      (a : Matrix (Fin n) (Fin n) (Formalism.IndefR.Lev.EAf D)) *ᵥ fun i => Formalism.IndefR.Datum.eToEAf D (y i) := by
    funext i
    rw [ha]
    exact RingHom.map_mulVec _ _ _ _
  have hw : (((a * g)⁻¹ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) : Matrix (Fin n) (Fin n) (Formalism.IndefR.Lev.EAf D)) *ᵥ
        (fun i => Formalism.IndefR.Datum.eToEAf D ((M *ᵥ y) i)) =
      ((g⁻¹ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) : Matrix (Fin n) (Fin n) (Formalism.IndefR.Lev.EAf D)) *ᵥ
        fun i => Formalism.IndefR.Datum.eToEAf D (y i) := by
    rw [hv, Matrix.mulVec_mulVec, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  unfold Formalism.UG.CS.globLat
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  have he : Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) = Formalism.IndefR.Datum.eToEAf D := rfl
  rw [he, hw]

theorem finG_rat {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (g : GfC V)
    (U : Matrix.unitaryGroup (Fin V.rank) D.host.E) (h : GlobalTheory.RatMoveJets.RatCoord V fr g U) :
    (GlobalTheory.FunObj.finG V g).1 = (fr.1 * U.1 * (fr⁻¹ : GL (Fin V.rank) D.host.E).1).map (Formalism.IndefR.Datum.eToEAf D) := by
  obtain ⟨γ, -, hfin, hmt⟩ := h
  have key : ∀ e : D.host.E, Formalism.IndefR.Lev.swapAE D
      ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) (incA D e)) =
      Formalism.IndefR.Datum.eToEAf D e := by
    intro e
    simp [Formalism.IndefR.Lev.swapAE, Formalism.IndefR.Datum.eToEAf, Formalism.L2.Theta.incA, inclR]
  unfold GlobalTheory.FunObj.finG Formalism.IndefR.Lev.finE
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [← hfin]
  have hm : ((Formalism.L2.Theta.matHom V γ : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) =
      (fr.1 * U.1 * (fr⁻¹ : GL (Fin V.rank) D.host.E).1).map (incA D) := hmt
  unfold Formalism.L2.Theta.finHom
  simp only [Formalism.UG.bc, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, hm,
    Matrix.map_map]
  ext i j
  exact key _

theorem latAt_rat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (r : FinPt G X) (U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E),
    GlobalTheory.RatMoveJets.RatCoord (G.V X) (S.N.fr X) r U → ∀ x : FinPt G X,
      GlobalTheory.SumSize.latAt S X (r * x) = SDLat.smulLat U.1 (GlobalTheory.SumSize.latAt S X x) := by
  intro D T L sc G W S X r U hr x
  have hfr := finG_rat _ _ _ _ hr
  have hU : U.1 * star U.1 = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  have hmv : ∀ v : Fin (G.V X).rank → D.host.E,
      ((S.N.fr X).1 * U.1 * ((S.N.fr X)⁻¹ : GL (Fin (G.V X).rank) D.host.E).1) *ᵥ ((S.N.fr X).1 *ᵥ v) =
        (S.N.fr X).1 *ᵥ (U.1 *ᵥ v) := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hzz : ∀ z : Fin (G.V X).rank → D.host.E, U.1 *ᵥ (star U.1 *ᵥ z) = z := by
    intro z
    rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  ext z
  simp only [GlobalTheory.SumSize.latAt, SDLat.smulLat, Submodule.mem_map, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.toLin'_apply, map_mul]
  constructor
  · intro hz
    refine ⟨star U.1 *ᵥ z, ?_, ?_⟩
    · rw [← mem_globLat_rat _ _ _ hfr, hmv, hzz]
      exact hz
    · exact hzz z
  · rintro ⟨w, hw, rfl⟩
    rw [← hmv, mem_globLat_rat _ _ _ hfr]
    exact hw

end GlobalTheory.RatMoveLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionRealPointFockVectorsScalarColumnAction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.RealColAct

open GlobalTheory.Ker.ColChange

theorem pureTensor_compAt {D : D7} {S T : HSp D} (C : Ctx S T) (h : GA D S) {B : C.Bas} (hB : C.IsB B)
    {f : WO S T → ℂ} (hf : C.IsTh f) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) B f Q =
      C.fvec B f (ColChange.sub C h Q) := by
  have hU : ∀ τ, (compAt C.θ τ (Formalism.L2.Theta.mt S h))⁻¹ = (compAt C.θ τ (Formalism.L2.Theta.mt S h))ᴴ := fun τ =>
    Matrix.inv_eq_left_inv (GlobalTheory.Ker.ColChange.compAt_unitary C h τ)
  have key : ∀ g : WO S T → ℂ, C.IsTh g → ∀ v : FVar D T.rank S.rank,
      aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) B v g =
        ∑ l, (if (v.2.1 : ℕ) < C.X.p0 then conj (compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2)
            else compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2) •
          aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) (fun _ => 1) B (v.1, v.2.1, l) g := by
    rintro g hg ⟨τ, i, j⟩
    have hc : ∀ z : Matrix (Fin T.rank) (Fin S.rank) ℂ, aPlus (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z g =
        ((fockScale D τ : ℂ)⁻¹) • crea (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z g := by
      intro z
      rw [GlobalTheory.Ker.FockAlg.aPlus_eq C]
      unfold crea
      rw [sub_eq_add_neg, neg_smul]
    change aPlus (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) (unitMap (compAt C.θ τ (Formalism.L2.Theta.mt S h)) (B τ) i j) g =
      ∑ l, (if (i : ℕ) < C.X.p0 then conj (compAt C.θ τ (Formalism.L2.Theta.mt S h) l j)
            else compAt C.θ τ (Formalism.L2.Theta.mt S h) l j) •
        aPlus (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) (unitMap 1 (B τ) i l) g
    simp only [hc]
    rw [GlobalTheory.Ker.ColChange.unitMap_expand, GlobalTheory.Ker.ColChange.crea_sum C hg, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [GlobalTheory.Ker.ColChange.crea_smul C hg τ (C.sB B τ) (unitMap 1 (B τ) i l) ((i : ℕ) < C.X.p0)
      (GlobalTheory.Ker.ColChange.sB_unitMap C hB τ i l), hU τ, Matrix.conjTranspose_apply, smul_smul, smul_smul]
    congr 1
    split_ifs <;> simp [Complex.star_def, mul_comm]
  have Lc := fun P : MvPolynomial (FVar D T.rank S.rank) ℂ =>
    GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C B hB (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) f hf P
  have L1 := fun P : MvPolynomial (FVar D T.rank S.rank) ℂ =>
    GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C B hB (fun _ => 1) f hf P
  have hX : ∀ v : FVar D T.rank S.rank, ColChange.sub C h (MvPolynomial.X v) =
      ∑ l, (if (v.2.1 : ℕ) < C.X.p0 then conj (compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2)
          else compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2) • MvPolynomial.X (v.1, v.2.1, l) := fun v =>
    MvPolynomial.aeval_X _ v
  show pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) B f Q =
    pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun _ => 1) B f (ColChange.sub C h Q)
  induction Q using MvPolynomial.induction_on
  next a =>
    have e : (MvPolynomial.C a : MvPolynomial (FVar D T.rank S.rank) ℂ) = a • 1 := by
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [e, map_smul, map_smul, map_smul, map_one (ColChange.sub C h), (Lc 1).2.2.1, (L1 1).2.2.1]
  next p q hp hq =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  next p v hp =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mul_comm p, (Lc p).2.1 v, hp, key _ (L1 (ColChange.sub C h p)).1 v, map_mul, hX, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, map_smul, (L1 (ColChange.sub C h p)).2.1]

theorem om_real_fvec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ B, C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → ∀ h ∈ GinfC S, ∃ c : ℂ, c ≠ 0 ∧ ∀ Q Q' : MvPolynomial (FVar D T.rank S.rank) ℂ, C.toH Q' = Harm.colActHom (GlobalTheory.Ker.ColChange.colU C h) (C.toH Q) → om (h, 1) (C.fvec B f Q) = c • C.fvec B f Q' := by
  intro D S T C om hom B hB f hf hF h hh
  obtain ⟨φ, hφ, hfφ⟩ := GlobalTheory.Ker.exists_test_of_fock D S T C B hB f hf hF
  obtain ⟨c, hc, hcφ⟩ := GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hom h hh 1 (one_mem _) B hB
  have h1 : C.mvB 1 B = B := GlobalTheory.Ker.ONBasis.mvB_fin C B (one_mem _)
  have hom1 : om (h, 1) f = c • f := by rw [hfφ, hcφ φ hφ, h1]
  refine ⟨c, fun h0 => by simp [h0] at hc, fun Q Q' hQ => ?_⟩
  have hQ' : Q' = ColChange.sub C h Q := C.toH_bijective.1 (by
    rw [hQ]; exact (DFunLike.congr_fun (GlobalTheory.Ker.ColChange.toH_sub C h) Q).symm)
  rw [hQ', GlobalTheory.Ker.WeakMove.om_fvec C hom h 1 hf B Q, h1, hom1,
    pureTensor_compAt C h hB (GlobalTheory.Ker.FockAlg.th_smul C c hf) Q]
  exact (GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C B hB (fun _ => 1) f hf (ColChange.sub C h Q)).2.2.2.2.1 c

end GlobalTheory.Ker.RealColAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelCmExtension
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical

namespace GlobalTheory.Twist.SmoothLine

theorem finprod_add_of_at {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) (x z : κ → AF F) (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evI F) z) :
    (∏ᶠ v, φ v fun i => evFin F v ((x + z) i)) = ∏ᶠ v, φ v fun i => evFin F v (x i) := by
  refine finprod_congr fun v => ?_
  have hv : (fun i => evFin F v ((x + z) i)) = fun i => evFin F v (x i) := by
    funext i
    rw [Pi.add_apply, map_add (f := _), GlobalTheory.ThK.EvUniqInf.evFin_eq_zero_of_at z hz v i, add_zero]
  rw [hv]

end GlobalTheory.Twist.SmoothLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepListProdDistinctPlacesPureTensorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_list_prod_distinctPlaces_pureTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd)
    (hv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Wd.J)
    (φ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) → (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) →
    (∀ v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, hv v)) (φ v) (φ₁ v)) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), l.Nodup → ∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      om (1, (l.map hv).prod) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (fun v => if v ∈ l then φ₁ v else φ v) := by
  first | exact @GlobalTheory.PureListAct.om_list_prod_pure | exact GlobalTheory.PureListAct.om_list_prod_pure | (intros; apply GlobalTheory.PureListAct.om_list_prod_pure <;> assumption)
end

