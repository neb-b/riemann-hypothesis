module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.Pad

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

abbrev Letter : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ)

def letters : List (Letter Dw) :=
  (List.finRange (Fintype.card (E →+* ℂ))).flatMap fun a =>
    (List.finRange (Dw.mult ((Fintype.equivFin (E →+* ℂ)).symm a))).map fun i => ⟨_, i⟩

abbrev Sym (E : Type) [Field E] : Type := (ℕ → Bool) × Option ℝ × (((E →+* ℂ) × ℕ) ⊕ ℕ)

def letterOf : ((E →+* ℂ) × ℕ) ⊕ ℕ → Option (Letter Dw)
  | .inl (τ, k) => if h : k < Dw.mult τ then some ⟨τ, ⟨k, h⟩⟩ else none
  | .inr k => (letters Dw)[k]?


open Classical in
def expo (w : Sym E →₀ ℤ) (x : Letter Dw) : ℤ := w.sum fun a n => if letterOf Dw a.2.2 = some x then n else 0


open Classical in
def parOf (w : Sym E →₀ ℤ) : Option ℝ := if h : w.support.Nonempty then h.choose.2.1 else none

variable {Dw}


open Classical in
def lnStep {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (x : Sp C ⟶ X)
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left)) (p : ℕ) (b : Bool) :
    ((E →+* ℂ) × ℕ) ⊕ ℕ → ℝ
  | .inl (τ, k) => if h : k < Dw.mult τ then Real.log (grNorm t x (lat t p x b) (u τ) ⟨k, h⟩) -
      (if b ∧ τ (H.rt : E) = H.rt0 then vDiff E p * Real.log p else 0) else 0
  | .inr k => if h : k < (letters Dw).length then
      Real.log (grNorm t x (lat t p x b) (fun i => u ((letters Dw).get i).1 ((letters Dw).get i).2) ⟨k, h⟩) else 0

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

def divOf (n : Letter Dw → ℤ) : Y.Y.Dv := ∑ x, n x • Y.gr x.1 x.2

def resP (v : HeightOneSpectrum (𝓞 F)) : ℕ := ringChar (𝓞 F ⧸ v.asIdeal)

def ioOf (p : ℕ) [Fact p.Prime] {v : HeightOneSpectrum (𝓞 F)} (ε : Ext v) : AlgebraicClosure F →+* ℂ_[p] :=
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure F) := Algebra.IsAlgebraic.trans ℚ F _
  haveI : Nonempty (AlgebraicClosure F →+* ℂ_[p]) := ⟨(IsAlgClosed.lift : AlgebraicClosure F →ₐ[ℚ] ℂ_[p]).toRingHom⟩
  Classical.epsilon fun io => ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O


open Classical in
def lgOf (w : Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y) : ℝ :=
  if hp : (resP v).Prime then
    haveI := Fact.mk hp
    let f := (Y.gr_spec (below y.1)).choose_spec.choose
    let t := (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose
    let ψ : Y.Y.X.presheaf.stalk (below y.1) →+* ℂ_[resP v] := (ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom
    Real.log (ε.w (valAt y.1 (((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw w x) *
        (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        w.sum fun a n => (n : ℝ) * lnStep Z.t (spMap ψ ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
          (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2
  else 0

abbrev Mets (C : CxSt F) : Type := ∀ (_ : Option ℝ) (σ : F →+* ℂ) (n : Letter Dw → ℤ), C.Met Y.Y σ (divOf Y n)

def adlOf {C : CxSt F} (hm : Mets Y C) (w : Sym E →₀ ℤ) : Adl C Y.Y where
  D := divOf Y (expo Dw w)
  n := 1
  m σ := hm (parOf w) σ _
  ci := 0
  lg := lgOf Y w


variable (Dw) in
def rootSym (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : ℕ) : Sym E →₀ ℤ :=
  if i < Dw.p then Finsupp.single (a, R, .inl (τ, i)) 1
  else Finsupp.single (a, R, .inl (conjEmb τ, Dw.p + Dw.q - 1 - i)) (-1)

def wholeSym (a : ℕ → Bool) (R : Option ℝ) {g : ℕ} : Fin g ⊕ Fin g → (Sym E →₀ ℤ)
  | .inl k => Finsupp.single (a, R, .inr k) 1
  | .inr k => Finsupp.single (a, R, .inr (Fin.rev k)) (-1)


variable (Dw) in
def detSym (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) : Sym E →₀ ℤ :=
  ∑ i ∈ Finset.range (Dw.p + Dw.q), rootSym Dw a R τ i

def IsFlat (τ : E →+* ℂ) (σ : Y.Y.Fn) : Prop :=
  ∀ y : Y.Y.X, (divOf Y (expo Dw (detSym Dw (fun _ => false) none τ))).GeneratesAt y σ

def IsCoord {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} (p : Sp k ⟶ Y.Y.X) (g : EigFrame Z φ x)
    (n : Letter Dw → ℤ) (σ : Y.Y.Fn) (a : k) : Prop :=
  ∃ (y : Y.Y.X) (ψ : Y.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* Y.Y.X.presheaf.stalk y)
    (f : EigFrame Z φ₁ (stalkPt Y.Y y ≫ Y.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ) (r : Y.Y.X.presheaf.stalk y),
    p = spMap ψ ≫ stalkPt Y.Y y ∧ f.Tri (algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField) Y.f0 t ∧
      f.Tri ψ g t' ∧
      algebraMap (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField r =
        σ * ((∏ z : Letter Dw, t z.1 z.2 ^ n z : Y.Y.Fnˣ) : Y.Y.Fn) ∧
      a = ψ r * ((∏ z : Letter Dw, t' z.1 z.2 ^ (-n z) : kˣ) : k)

def FlagPt.frame {Ω : Type} [Field Ω] (y : FlagPt Z Ω) : EigFrame Z y.fK (y.y ≫ genι Z) :=
  ⟨y.u, y.tan, y.eig, y.basis⟩

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (fl : s.Flag)
  {C : CxSt D.what₂.LL} (hm : ∀ k, Mets (fl.C k) C)

def arIn : ArIn D.what₂.Tau N (D.R.f * N) s.Comp where
  A _ := Sym D.host.E →₀ ℤ
  num k := polar fun w => (adlOf (fl.C k) (hm k) w).arTop
  root a R x _ := rootSym S.Dw a (some R) (DV.tauEmb D x.1) x.2
  whole a R x _ := wholeSym a (some R) x

def setB (κ : Lv A) (B : ℝ) : Finset ℕ :=
  (Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime ∪ (2 * (NumberField.discr D.host.E).natAbs * κ.l.M').primeFactors

def flatSec (k : s.Comp) (τ : D.what₂.Tau) : (fl.C k).Y.Fn := Classical.epsilon (IsFlat (fl.C k) (DV.tauEmb D τ))

def innerPt (k : s.Comp) : (fl.C k).Y.X :=
  Classical.epsilon fun x => IsClosed ({x} : Set (fl.C k).Y.X) ∧ (fl.C k).π x ∉ genBd s.T.Z

def flatSt : FlatSt s where
  sv τ y := Classical.epsilon fun a => ∃ (k : s.Comp) (p : Sp Qb ⟶ (fl.C k).Y.X), p ≫ (fl.C k).π = y.y ∧
    IsCoord (fl.C k) p y.frame (expo S.Dw (detSym S.Dw (fun _ => false) none (DV.tauEmb D τ))) (flatSec s fl k τ) a
  ht B k τ := (adlOf (fl.C k) (hm k) (detSym S.Dw (ArIn.ind (setB κ B)) none (DV.tauEmb D τ))).ht (innerPt s fl k)

def degFrame (k : s.Comp) (τ : D.what₂.Tau) : ℝ :=
  (adlOf (fl.C k) (hm k) (detSym S.Dw (fun _ => false) none (DV.tauEmb D τ))).ht (innerPt s fl k)

def degFlat (k : s.Comp) (τ : D.what₂.Tau) : ℝ :=
  degFrame s fl hm k τ + (S.Dw.q : ℝ) * (Real.log A.H.d -
    Real.log (NumberField.discr D.host.E).natAbs / (Module.finrank ℚ D.host.E : ℝ))

end GlobalTheory.ShFam.Pad
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVecC
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open TopologicalSpace
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open Formalism.L2.Pj (FrPt CAt embK)
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts
open GlobalTheory.AllWt (Psi ptF framesOn LiesOn)
open scoped ComplexOrder

namespace GlobalTheory.TrueCx

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} {Tau : Type}

section Std

variable (X : Data E r) (hj : j ≤ r) (κ : Tau ≃ X.Ψ)

def stdMat (z : Pt Tau j (r - j)) : Frame X.Ψ r := fun τ =>
  (mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (fromBlocks 1 (z (κ.symm τ)) 0 1) : Matrix (Fin r) (Fin r) ℂ)

theorem frameCo_stdMat (z : Pt Tau j (r - j)) (τ : X.Ψ) :
    frameCo X hj (stdMat X hj κ z) τ = fromBlocks 1 (z (κ.symm τ)) 0 1 := by
  show reindex _ _ (_ * (mat (x0F X) τ * _)) = _
  rw [nonsing_inv_mul_cancel_left _ _ (det_x0F X τ).isUnit]
  simp

theorem domPt_stdMat (z : Pt Tau j (r - j)) : domPt X hj κ (stdMat X hj κ z) = z := by
  funext t
  simp [domPt, frameCo_stdMat, moeb_zero]

theorem stdMat_mem (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    stdMat X hj κ z ∈ X.dom := by
  refine ExF.mem_dom_of_gramPos X fun τ => ⟨?_, ?_⟩
  · show (mat (x0F X) τ * _).det ≠ 0
    rw [det_mul, det_reindex_self, det_fromBlocks_zero₂₁]
    simpa using det_x0F X τ
  have h0 := congrArg transpose (isOrth_x0F X τ)
  rw [gram_eq_mul, diagonal_transpose, hp] at h0
  set N : Matrix (Fin j ⊕ Fin (r - j)) (Fin j ⊕ Fin (r - j)) ℂ := fromBlocks 1 (z (κ.symm τ)) 0 1 with hN
  have h1 : reindex (idx hj) (idx hj) (gram τ.1 X.Gm (mat (stdMat X hj κ z) τ))ᵀ = Nᴴ * -Jpq j (r - j) * N := by
    rw [gram_eq_mul, ← reindex_sgn hj, ← h0]
    show reindex _ _ ((mat (x0F X) τ * reindex _ _ N)ᴴ * _ * (mat (x0F X) τ * reindex _ _ N)) = _
    simp only [conjTranspose_mul, reindex_apply, conjTranspose_submatrix, ← submatrix_mul_equiv _ _ _ (idx hj).symm,
      submatrix_submatrix, Equiv.symm_symm, Equiv.self_comp_symm, submatrix_id_id, Matrix.mul_assoc]
  have h2 : (Nᴴ * -Jpq j (r - j) * N).toBlocks₂₂ = hQ (z (κ.symm τ)) := by
    simp [hN, Jpq, fromBlocks_conjTranspose, fromBlocks_neg, fromBlocks_multiply, hQ, sub_eq_neg_add]
  have h3 : X.gramPos (stdMat X hj κ z) τ = ((hQ (z (κ.symm τ))).submatrix (finCongr hp) (finCongr hp))ᵀ := by
    ext a b
    have e : ∀ a : Fin X.p0, (idx hj).symm (Sum.inr (finCongr hp a)) = Fin.castLE X.p0_le a :=
      fun a => Fin.ext (idx_symm_inr hj _)
    rw [← h2, ← h1]
    simp only [transpose_apply, submatrix_apply, toBlocks₂₂, of_apply, reindex_apply, e, Data.gramPos]
  rw [h3]
  exact (PosDef.submatrix (hz (κ.symm τ)) (finCongr hp).injective).transpose


open Classical in
def stdFrame (hp : X.p0 = r - j) (z : Pt Tau j (r - j)) : X.dom :=
  if h : z ∈ DomI Tau j (r - j) then ⟨stdMat X hj κ z, stdMat_mem X hj κ hp h⟩
  else ⟨stdMat X hj κ 0, stdMat_mem X hj κ hp fun _ => zero_mem_hcDom _ _⟩

theorem stdFrame_val (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    (stdFrame X hj κ hp z).1 = stdMat X hj κ z := by rw [stdFrame, dite_eq_left hz]

theorem domPt_stdFrame (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    domPt X hj κ (stdFrame X hj κ hp z).1 = z := by rw [stdFrame_val X hj κ hp hz, domPt_stdMat]

end Std

section Tor

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) (σ : c.F →+* ℂ)

abbrev torC : Scheme.{0} := pullback Y.s (spMap σ)

abbrev torStr : torC Y σ ⟶ Sp ℂ := pullback.snd Y.s (spMap σ)

abbrev torPr : torC Y σ ⟶ Y.X := pullback.fst Y.s (spMap σ)

abbrev TorPts : Type := CxPts (torStr Y σ) (RingHom.id ℂ)

variable {Y σ}

variable (Y)

def ptC (y : FrPt Xo c (CAt σ)) : Sp ℂ ⟶ Xo.XF c := ptF (S := CAt σ) y

def xC (y : FrPt Xo c (CAt σ)) : Sp ℂ ⟶ Xo.X := y.x

theorem ptC_fst (y : FrPt Xo c (CAt σ)) : ptC y ≫ pullback.fst _ _ = xC y := pullback.lift_fst _ _ _

theorem ptC_snd (y : FrPt Xo c (CAt σ)) : ptC y ≫ pullback.snd _ _ = spMap σ := pullback.lift_snd _ _ _

def torPt (y : FrPt Xo c (CAt σ)) : TorPts Y σ :=
  ⟨pullback.lift (ptC y ≫ Y.j) (spMap (RingHom.id ℂ)) (by
      rw [Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
        ← Category.assoc, ptC_snd, ← Spec.map_comp, ← Spec.map_comp]
      rfl), pullback.lift_snd _ _ _⟩

theorem torPt_pr (y : FrPt Xo c (CAt σ)) : (torPt Y y).1 ≫ torPr Y σ = ptC y ≫ Y.j := pullback.lift_fst _ _ _

abbrev LieAt (y : TorPts Y σ) : Type := TanM (y.1 ≫ torPr Y σ) Y.t.G


variable (σ) in
abbrev LieForm : Type := ∀ y : TorPts Y σ, LieAt Y y →ₗ[ℂ] LieAt Y y →ₗ⋆[ℂ] ℂ

def lieEquiv (y : FrPt Xo c (CAt σ)) : TanM (xC y) Xo.univ.t.G ≃ₗ[ℂ] LieAt Y (torPt Y y) :=
  (pushE Y.m0.toSABMap (ptC y) (ptC_fst y)).symm.trans (pushE Y.m (ptC y) (torPt_pr Y y).symm)

end Tor

section Bd

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) {σ : c.F →+* ℂ}

variable (U : Unf Xo c σ r) (hU : IsUnf U) (e : Dw.p = j) (hσ : GoodEmb c σ) (T : Tau ≃ Psi H)


def letter (t : Tau) : Psi H := (letterAt hσ).symm (T t)


variable [Fintype Tau]


variable (B : ∀ k, BdData Tau j (r - j) (gammaU (U.X k) (le_of_isUnf U hU e) (cmEquiv U hU T k)))

variable {Y U hU e hσ T B}

end Bd

section Flat

open GlobalTheory.FlatLine GlobalTheory.AllWt

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {x : ℝ}
  (sig : ∀ (Z : Formalism.L2.Pj.Comp Xo c) (τ : Psi H), FlatSec (fun σ => (U σ).toPj) x Z τ)
  {σ : c.F →+* ℂ} (hU : IsUnf (U σ)) (hσ : GoodEmb c σ) (T : Tau ≃ Psi H)

variable {U sig hU hσ T}

end Flat

end GlobalTheory.TrueCx
end
end

