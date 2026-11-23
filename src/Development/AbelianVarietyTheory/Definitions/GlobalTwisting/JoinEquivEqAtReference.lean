module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Formalism.LocalToGlobal.HermitianForms.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0003
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215

@[expose] public section

noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Forms Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie
open NumberField IsDedekindDomain Matrix GlobalTheory.BigTop GlobalTheory.Mem.R3 GlobalTheory.Core.Rk.Top

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Conj

variable {ι : Type} [Fintype ι] {n : ℕ}

def conjFn (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) : Pol ℂ ι n →ₛₗ[starRingEnd ℂ] (Frames G → ℂ) where
  toFun P := fnOf G s G (MvPolynomial.map (starRingEnd ℂ) P)
  map_add' P Q := by rw [map_add (f := _), map_add (f := _)]
  map_smul' c P := by
    rw [← map_smul]
    congr 1
    simp [MvPolynomial.smul_eq_C_mul]

end Conj

variable {D : D7}

abbrev PtX (D : D7) : Type := Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

theorem reGL_symm_mem {F E : Type} [Field F] [CommRing E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] {a b : ℕ}
    (h : a = b) (J : Matrix (Fin a) (Fin a) E) {x} (hx : x ∈ Formalism.UG.UPts σ (J.reindex (finCongr h) (finCongr h)) R) :
    (reGL h _).symm x ∈ Formalism.UG.UPts σ J R := by
  subst h
  exact hx

theorem exists_hasMat (x : PtX D) : ∃ h, HasMat h x.1 := by
  obtain ⟨b, hb⟩ := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig D.sp.X'.gram).surjective
    ⟨_, reGL_symm_mem _ _ (rankP D) _ x.2⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig D.sp.X'.gram
  obtain ⟨k, k1, k2⟩ := h2 1 b.1
  refine ⟨⟨k, (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ b.2⟩⟩, k1, fun i j => ?_⟩
  have e2 := (GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig D.sp.X'.gram b).symm.trans (congrArg Subtype.val hb)
  exact congrArg (fun g : GL _ (Lev.EAf D) => g.1 i j) ((congrArg (Formalism.UG.bc (Lev.swapAE D)) k2).trans e2)

def rowPt (x : PtX D) : Bridge.Gf D.sp.X' := (finHom D.sp.X').rangeRestrict (exists_hasMat x).choose

abbrev lamX (D : D7) : D.what₂.Tau → DomWeight D.sp.X'.rank := fun τ => Bridge.lamRdef (Ptw D) τ

def conjVal (D : D7) : Pol ℂ D.what₂.Tau D.sp.X'.rank →ₛₗ[starRingEnd ℂ] (FrP D → ℂ) :=
  (conjFn (gramC (gramP D) (embT D)) (shiftOf (lamX D))).comp
    (MvPolynomial.rename (Prod.map id (Prod.map (Fin.cast (rankP D)) (Fin.cast (rankP D))))).toLinearMap

def LevIs {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (S : StepLevel D.host.F D.host.E (sigD D) (gramP D) 1 D.R.f bad)
    (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ) : Prop :=
  (∀ h, h ∈ J ↔ ∃ κ : S.U, HasMat h κ.1) ∧ ∀ h (κ : S.U), HasMat h κ.1 → χ h = star ((S.chi κ : ℂˣ) : ℂ)

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def conjForm (co : R.cX.W →ₗ[ℂ] Pol ℂ D.what₂.Tau D.sp.X'.rank) (t : T) (f : A.fam.amb.FR t) : PtX D → FrP D → ℂ :=
  fun x => conjVal D (co (R.B.jR t f (rowPt x)))

variable {R}

end Real

section Point

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

abbrev Coord : Type := p.R.cX.W →ₗ[ℂ] Pol ℂ D.what₂.Tau D.sp.X'.rank

abbrev rowDat (t : p.P.T) : LevDat D.host.E ℂ D.sp.X'.rank := datXP p.R.toRealDat t (p.R.toRealDat.levR p.F.lv2 true)

def rowConj (co : Coord p) (t : p.P.T) (x : Fin (rDim D p.P.A3.A p.P.Ps p.P.ψs t) → D.what₂.LL) : PtX D → FrP D → ℂ :=
  conjForm p.R.toRealDat co t (rowForm p.P.A3.A p.P.Ps p.P.ψs t x)

def JoinAt (co : Coord p) (t : p.P.T) {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) (gramP D) 1 D.R.f bad) {cl : Type} (y : cl → PtX D)
    (rd : D.what₂.Amb (p.P.I.tup t) → cl → FrP D → ℂ) : Prop :=
  LevIs S (levS _ p.R.βX (rowDat p t)) (Lev.levChi _ p.R.βX (rowDat p t)) ∧ ∀ x c, rd (p.P.I.jA t x) c = rowConj p co t x (y c)

variable (Cs : ColsTiedSym D) (tw : SymmetricTwistedColumnsAtPrimes p.Tp Cs ex.tw)

def MtJoinBy (co : Coord p) (e₀ : ∀ u, (D.mem u).P.Mt ≃ₗ[ℂ] D.what₂.Amb D.what₂.mu0)
    (e : ∀ u μ, (D.PTw u μ).Mt ≃ₗ[ℂ] D.what₂.Amb μ) : Prop :=
  (∀ u t (h : p.P.I.tup t = D.what₂.mu0), JoinAt p co t (Cs.forms u).clsP.lev (Cs.forms u).clsP.y fun F =>
    (Cs.forms u).valP.eW ((Cs.forms u).jM ((e₀ u).symm (Eq.rec (motive := fun ν _ => D.what₂.Amb ν) F h)))) ∧
  ∀ u t, Used0 D (p.P.I.tup t) → ∀ h : p.P.I.tup t ≠ D.what₂.mu0,
    JoinAt p co t (tw.pt.cls u _ h).lev (tw.pt.cls u _ h).y fun F => (tw.pt.val u _ h).eW (tw.ptE.jM u _ ((e u _).symm F))




variable {p Cs tw} {co : Coord p} {e₀ e₀' : ∀ u, (D.mem u).P.Mt ≃ₗ[ℂ] D.what₂.Amb D.what₂.mu0}
  {e e' : ∀ u μ, (D.PTw u μ).Mt ≃ₗ[ℂ] D.what₂.Amb μ}

theorem jM_injective (H : Formalism.L2.Rows.EMtTied D Cs tw) (u : D.what₂.Word) : Function.Injective (Cs.forms u).jM :=
  (injective_iff_map_eq_zero _).2 fun F hF => (D.eMt u).map_eq_zero_iff.1 (inner_self_eq_zero.1 (by
    rw [H.mu0 u F F, hF, map_zero]))

theorem jM_injective_tw (H : Formalism.L2.Rows.EMtTied D Cs tw) (u : D.what₂.Word) {μ : D.what₂.Tup} (hμ : μ ≠ D.what₂.mu0) :
    Function.Injective (tw.ptE.jM u μ) :=
  (injective_iff_map_eq_zero _).2 fun F hF => (D.eMtTw u μ).map_eq_zero_iff.1 (inner_self_eq_zero.1 (by
    rw [H.tw u μ hμ F F, hF, map_zero]))

end Point

end GlobalTheory.EX

end
