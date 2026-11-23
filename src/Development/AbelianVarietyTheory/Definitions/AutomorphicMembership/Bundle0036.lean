module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier

namespace GlobalTheory.ShFam

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure EigFrame (Z : Model Xo c β) {R : Type} [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) : Type where
  v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Z.t.G.left)
  tan : ∀ τ i, IsTanAtG Z.t x (v τ i)
  eig : ∀ τ i (a : 𝓞 E), v τ i ≫ (Z.t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ v τ i
  basis : ∀ τ w, IsTanAtG Z.t x w → (∀ a : 𝓞 E, w ≫ (Z.t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ w) →
    ∃! a : Fin (Dw.mult τ) → R, IsCombAtG Z.t x (v τ) a w

def EigFrame.Tri {Z : Model Xo c β} {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') (g : EigFrame Z φ' x')
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ) : Prop :=
  x' = spMap ψ ≫ x ∧ φ' = ψ.comp φ ∧ ∀ τ i, ∃ cf : Fin (Dw.mult τ) → R', cf i = t τ i ∧ (∀ k, i < k → cf k = 0) ∧
    IsCombAtG Z.t x' (fun k => spMap (dualMap ψ) ≫ f.v τ k) cf (g.v τ i)


attribute [local instance] Over.cartesianMonoidalCategory in
open MonObj in
theorem isCombAtG_single {X0 : Scheme.{0}} (t : SAB H X0) {R : Type} [CommRing R] (x : Sp R ⟶ X0) {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j)) (j : Fin m) :
    IsCombAtG t x v (Pi.single j 1) (v j) := by
  have hb : ∀ a : R, spMap (epsMul a) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R)) :=
    fun a => by
      rw [← Spec.map_comp]
      congr 1
      ext r <;> simp [epsMul]
  have h1 : spMap (epsMul (1 : R)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [epsMul]
  have h0 : spMap (epsMul (0 : R)) =
      spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    have e : epsMul (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
      RingHom.ext fun z => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    rw [← Spec.map_comp, e]
    rfl
  let u : Fin m → (tEpsG x ⟶ t.G) := fun i =>
    Over.homMk (spMap (epsMul ((Pi.single j 1 : Fin m → R) i)) ≫ v i) (by
      rw [Category.assoc, (hv i).1, ← Category.assoc, hb]; rfl)
  have hu : ∀ i, i ≠ j → u i = 1 := fun i hi => by
    let p : tEpsG x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R (DualNumber R))) rfl
    rw [← MonObj.comp_one p]
    ext
    show spMap (epsMul ((Pi.single j 1 : Fin m → R) i)) ≫ v i = _
    rw [Pi.single_eq_of_ne hi, h0, Category.assoc, (hv i).2]
    rfl
  refine ⟨u, fun i => rfl, ?_⟩
  have : (List.ofFn u).prod = u j := by
    rw [List.ofFn_eq_map, List.prod_map_eq_pow_single j u fun i hi _ => hu i hi,
      List.count_eq_one_of_mem (List.nodup_finRange m) (List.mem_finRange j), pow_one]
  rw [this]
  show spMap (epsMul ((Pi.single j 1 : Fin m → R) j)) ≫ v j = _
  rw [Pi.single_eq_same, h1, Category.id_comp]

theorem EigFrame.tri_refl {Z : Model Xo c β} {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f : EigFrame Z φ x) : f.Tri (RingHom.id R) f 1 := by
  have h1 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have h2 : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _
  refine ⟨by rw [h2, Category.id_comp], rfl, fun τ i => ⟨Pi.single i 1, by simp,
    fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩⟩
  simp only [h1, Category.id_comp]
  exact isCombAtG_single Z.t x (f.tan τ) i

variable {F : Type} [Field F]

def constF (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) : c.F →+* Y.Fn := (algebraMap F Y.Fn).comp e.symm.toRingHom

def stalkPt (Y : GlobalTheory.ProjVar.Var F) (y : Y.X) : Sp (Y.X.presheaf.stalk y) ⟶ Y.X := Y.X.fromSpecStalk y

def genericPt (Y : GlobalTheory.ProjVar.Var F) : Sp Y.Fn ⟶ Y.X := Y.X.fromSpecStalk (genericPoint Y.X)

structure FlagCpt (Z : Model Xo c β) (e : F ≃+* c.F) : Type where
  Y : GlobalTheory.ProjVar.Var F
  π : Y.X ⟶ gen Z
  π_str : π ≫ genStr Z ≫ spMap e.toRingHom = Y.str

  y0 : letI := (constF e Y).toAlgebra; FrPt Xo c Y.Fn

  f0 : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)
  y0_x : (letI := (constF e Y).toAlgebra; GlobalTheory.AllWt.ptF y0) ≫ Z.jQ = genericPt Y ≫ π

  flagComponentFramedPoint_frame : letI := (constF e Y).toAlgebra; ∀ τ i, ∃ w : Sp (DualNumber Y.Fn) ⟶ Z.oF.t.G.left,
    w ≫ Z.oF.t.G.hom = spMap (algebraMap Y.Fn (DualNumber Y.Fn)) ≫ GlobalTheory.AllWt.ptF y0 ∧
    w ≫ Z.m0.toSABMap.φ = y0.u τ i ∧ w ≫ Z.m.φ = f0.v τ i

  gr : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Dv

  gr_spec : ∀ y : Y.X, ∃ (φ : c.F →+* Y.X.presheaf.stalk y) (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z))
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Fnˣ),
    f.Tri (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f0 t ∧ ∀ τ i, (gr τ i).IsEqn y (t τ i)

  bd : Y.Dv
  bd_eff : Y.Eff bd
  bd_supp : ∀ y : Y.X, y ∈ Y.supp bd ↔ π y ∈ genBd Z
  bd_red : ∀ (y : Y.X) (g : Y.Fnˣ), bd.IsEqn y g → ∀ (f : Y.Fn) (n : ℕ), RegAt y f → RegAt y (f ^ n / g) → RegAt y (f / g)

namespace FlagCpt

variable {Z : Model Xo c β} {e : F ≃+* c.F} (C : FlagCpt Z e)

def Carries {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} (p : Sp k ⟶ C.Y.X) (g : EigFrame Z φ x) : Prop :=
  ∃ (y : C.Y.X) (ψ : C.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* C.Y.X.presheaf.stalk y)
    (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
    p = spMap ψ ≫ stalkPt C.Y y ∧ f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t ∧ f.Tri ψ g t'

def Ybd : C.Y.Cl := C.Y.supp C.bd

def LEx : (Ix Dw → ℤ) →+ C.Y.Dv where
  toFun ex := -∑ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), ex (some x) • C.gr x.1 x.2
  map_zero' := by simp
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib, add_comm]

def Lw (la : GlobalTheory.AllWt.Weight Dw) : C.Y.Dv := C.LEx (GlobalTheory.AllWt.exOf Dw la 0)


end FlagCpt

structure FlagTor (Z : Model Xo c β) (e : F ≃+* c.F) {σ : c.F →+* ℂ} {N : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ N) : Type where
  C : U.Comp → FlagCpt Z e
  dim_eq : ∀ k, (C k).Y.dim = Module.finrank ℚ E / 2 * (N * (N - 1) / 2)
  lifts : ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : c.F →+* k) (x : Sp k ⟶ gen Z), x ≫ genStr Z = spMap φ →
    ∀ g : EigFrame Z φ (x ≫ genι Z), ∃! p : Σ i : U.Comp, (Sp k ⟶ (C i).Y.X), p.2 ≫ (C p.1).π = x ∧ (C p.1).Carries p.2 g
  label : ∀ (i : U.Comp) (x : (U.X i).dom) (s : Sp (CAt σ)),
    (GlobalTheory.AllWt.ptF (U.un i x) ≫ Z.jQ) s ∈ Set.range (C i).π

def keyEx (Dw : Datum H) : Ix Dw → ℤ
  | none => -2
  | some _ => 1

structure KeySec (Xo : Moduli Dw l) (c : Coeff l) : Type where
  ρ : (Rul Xo c)ˣ
  mem : (ρ : Rul Xo c) ∈ GlobalTheory.AllWt.secZ Xo c (keyEx Dw)

def exKey (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Ix Dw → ℤ :=
  fun i => (ex Dw a n i : ℤ) + ((n / 2 : ℕ) : ℤ) * keyEx Dw i

theorem exKey_two_mul (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ) :
    exKey Dw a (2 * m) = GlobalTheory.AllWt.exOf Dw (GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ)) m) 0 := by
  have h : GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ)) (m : ℤ) =
      GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ) + (m : ℤ)) 0 := by
    funext τ j
    simp only [GlobalTheory.AllWt.weightOf]
    split_ifs <;> ring
  rw [h, GlobalTheory.AllWt.exOf_weightOf]
  funext i
  cases i <;> simp [exKey, keyEx, ex, exZ]
  ring

theorem KeySec.pow_mem (κ : KeySec Xo c) (m : ℕ) :
    (κ.ρ : Rul Xo c) ^ m ∈ GlobalTheory.AllWt.secZ Xo c (fun i => (m : ℤ) * keyEx Dw i) := by
  induction m with
  | zero =>
    have h : (fun i => ((0 : ℕ) : ℤ) * keyEx Dw i) = 0 := by funext i; simp
    rw [pow_zero, h]; exact GlobalTheory.AllWt.one_mem_secZ
  | succ m ih =>
    have h : (fun i => ((m + 1 : ℕ) : ℤ) * keyEx Dw i) = (fun i => (m : ℤ) * keyEx Dw i) + keyEx Dw := by
      funext i; simp only [Pi.add_apply]; push_cast; ring
    rw [pow_succ, h]; exact GlobalTheory.AllWt.mul_mem_secZ ih κ.mem

end Free

abbrev FinalTheorems.Flag {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) : Type :=
  FlagTor s.T.Z κ.e (s.U κ.σ₀)

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

abbrev Vecs (Dw : Datum H) {X : Scheme.{0}} (t : SAB H X) (R : Type) [CommRing R] : Type :=
  ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ t.G.left)

def IsFrame {l : Level H} {c : Coeff l} {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (f : c.F →+* R)
    (x : Sp R ⟶ X) (u : Vecs Dw t R) : Prop :=
  (∀ τ i, IsTanAtG t x (u τ i) ∧
    ∀ a : 𝓞 E, u τ i ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ u τ i) ∧
  ∀ τ w, IsTanAtG t x w → (∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ w) →
    ∃! a : Fin (Dw.mult τ) → R, IsCombAtG t x (u τ) a w

def SameFlag (ty : (E →+* ℂ) → Finset ℕ) {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X)
    (u u' : Vecs Dw t R) : Prop :=
  ∀ τ, ∀ k ∈ ty τ, ∀ i : Fin (Dw.mult τ), (i : ℕ) < k →
    ∃ cf : Fin (Dw.mult τ) → R, (∀ j : Fin (Dw.mult τ), k ≤ (j : ℕ) → cf j = 0) ∧ IsCombAtG t x (u τ) cf (u' τ i)

def ProperLE (Dw : Datum H) (ty' ty : (E →+* ℂ) → Finset ℕ) : Prop :=
  ∀ σ, ∀ k ∈ ty' σ, 0 < k → k < Dw.mult σ → k ∈ ty σ

def Vecs.bc {X : Scheme.{0}} {t : SAB H X} {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (u : Vecs Dw t R) :
    Vecs Dw t S := fun τ i => spMap (dualMap φ) ≫ u τ i

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ}

structure Pre (Y : LocalSystem Xo p W) (i₀ : Idx H p) : Type where

  i : Idx H p

  dvd : i₀.l.Dvd i.l

  le : i₀.c.F ≤ i.c.F

  n : ℕ

  I : (PSpace (i.c.V W) n).IdealSheafData

  π : I.subscheme ⟶ (Y i).X

  ty : (E →+* ℂ) → Finset ℕ

  m : ℕ

  U : Fin m → I.subscheme.affineOpens

  alg : ∀ a, i.c.F →+* Γ(I.subscheme, (U a).1)

  fr : ∀ a, Vecs Dw (Y i).t Γ(I.subscheme, (U a).1)

variable {Y : LocalSystem Xo p W} {i₀ : Idx H p}

namespace Pre

variable (Z : Pre Y i₀)

abbrev X : Scheme.{0} := Z.I.subscheme

def s : Z.X ⟶ Sp (Z.i.c.V W) := Z.I.subschemeι ≫ PSpace.str _ Z.n

def chart (a : Fin Z.m) : Sp Γ(Z.X, (Z.U a).1) ⟶ Z.X := (Z.U a).2.fromSpec

def opn : Set Z.X := Z.π ⁻¹' Set.range (Y Z.i).j

def FlagAt {k : Type} [Field k] (w : Sp k ⟶ Z.X) (u : Vecs Dw (Y Z.i).t k) : Prop :=
  ∃ (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k), spMap φ ≫ Z.chart a = w ∧
    IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (w ≫ Z.π) u ∧ SameFlag Z.ty (Y Z.i).t (w ≫ Z.π) ((Z.fr a).bc φ) u

end Pre

structure Mdl (Y : LocalSystem Xo p W) (i₀ : Idx H p) : Type extends Pre Y i₀ where

  π_s : π ≫ (Y i).s = toPre.s

  normal : IsNormalScheme toPre.X

  flat : Flat toPre.s

  dense : Dense toPre.opn

  cover : ⋃ a, ((U a).1 : Set toPre.X) = toPre.opn

  alg_s : ∀ a, toPre.chart a ≫ toPre.s = spMap ((alg a).comp (i.c.V W).subtype)

  smooth : ∀ a, Smooth (toPre.chart a ≫ π)

  frame : ∀ a, IsFrame (Y i).t (alg a) (toPre.chart a ≫ π) (fr a)

  glue : ∀ (k : Type) [Field k] (a a' : Fin m) (φ : Γ(toPre.X, (U a).1) →+* k) (φ' : Γ(toPre.X, (U a').1) →+* k),
    spMap φ ≫ toPre.chart a = spMap φ' ≫ toPre.chart a' →
      SameFlag ty (Y i).t (spMap φ ≫ toPre.chart a ≫ π) ((fr a).bc φ) ((fr a').bc φ')

  bij : ∀ (k : Type) [Field k] (f : i.c.F →+* k) (y : Sp k ⟶ (Xo i.l).XF i.c), y ≫ pullback.snd _ _ = spMap f →
    ∀ u, IsFrame (Y i).t f (y ≫ (Y i).j) u → ∃! w : Sp k ⟶ toPre.X, w ≫ π = y ≫ (Y i).j ∧ toPre.FlagAt w u

namespace Mdl

variable (Z : Mdl Y i₀)

def t : SAB H Z.X := (exists_sab Z.π (Y Z.i).t).choose

def tMap : SABMap Z.t (Y Z.i).t Z.π := (exists_sab Z.π (Y Z.i).t).choose_spec.some

structure Pt : Type where

  C : SCF p

  P : PointsOfFlagModel.PtC (Y Z.i) C

  z : Sp ↥(intO ↥C.S) ⟶ Z.X

  z_π : z ≫ Z.π = P.yt

def Pt.fld {Z : Mdl Y i₀} (y : Z.Pt) : Formalism.MainNotions.ModuliIntegralCharts.CF p := y.C.toCF

def Pt.gen {Z : Mdl Y i₀} (y : Z.Pt) : Sp ↥y.C.S ⟶ Z.X := spMap (intO ↥y.C.S).subtype ≫ y.z

def inQ (x : Z.X) : Prop := CharZero (Z.X.residueField x)

def abP (x : Z.X) : Prop := Z.π x ∈ abLocus (Y Z.i).t.G

def isGenP (x : Z.X) : Prop := ∀ x' : Z.X, x' ⤳ x → x' = x

def Gen : Type := {x : Z.X // ¬ Z.inQ x ∧ ∀ x' : Z.X, ¬ Z.inQ x' → x' ⤳ x → x' = x}

def free (a m : ℕ) : Z.X.Modules :=
  GlobalTheory.twist (GlobalTheory.QCoh.freeModule Z.X (Fin m)) ((GlobalTheory.ProjSpace.On (Z.i.c.V W) Z.n (-(a : ℤ))).pull Z.I.subschemeι)

structure Sh : Type where

  a : ℕ

  m : ℕ

  a' : ℕ

  m' : ℕ

  φ : Z.free a' m' ⟶ Z.free a m

def Sh.toMod {Z : Mdl Y i₀} (F : Z.Sh) : Z.X.Modules := cokernel F.φ


open Classical in
def ofMod (F : Z.X.Modules) : Z.Sh :=
  if h : ∃ S : Z.Sh, Nonempty (S.toMod ≅ F) then h.choose else ⟨0, 0, 0, 0, 0⟩

def Idl : Type := {J : Z.X.IdealSheafData // ∀ x ∈ J.support, x ∉ Z.opn}

def powP (J : Z.Idl) : Prop := ∃ k : ℕ, ∀ U : Z.X.affineOpens, ((p : Γ(Z.X, U.1)) ^ k) ∈ J.1.ideal U

end Mdl

def IsTrans (i i₂ : Idx H p) (τ : (Y i₂).X ⟶ (Y i).X) (mu : SABMap (Y i₂).t (Y i).t τ) : Prop :=
  ∃ (b : i.c.V W →+* i₂.c.V W) (π' : (Y i₂).X ⟶ pullback (Y i).s (spMap b))
    (r : (Xo i₂.l).XF i₂.c ⟶ (Xo i.l).XF i.c), IsIncl b ∧
    π' ≫ pullback.fst _ _ = τ ∧ π' ≫ pullback.snd _ _ = (Y i₂).s ∧ IsFinite π' ∧ (Y i₂).j ≫ τ = r ≫ (Y i).j ∧
    (∀ a, ((Y i₂).oF.eta a ^ (i₂.l.M / i.l.M)).left ≫ (Y i₂).m.φ ≫ mu.φ = r ≫ ((Y i).oF.eta a).left ≫ (Y i).m.φ) ∧
    (∀ a, ((Y i₂).oF.etaA a ^ (i₂.l.A / i.l.A)).left ≫ (Y i₂).m.φ ≫ mu.φ = r ≫ ((Y i).oF.etaA a).left ≫ (Y i).m.φ)

def NatImg (Z₁ Z₂ : Mdl Y i₀) {k : Type} [Field k] (w₁ : Sp k ⟶ Z₁.X) (w₂ : Sp k ⟶ Z₂.X) : Prop :=
  ∃ (τ : (Y Z₁.i).X ⟶ (Y Z₂.i).X) (mu : SABMap (Y Z₁.i).t (Y Z₂.i).t τ) (u : Vecs Dw (Y Z₁.i).t k),
    IsTrans Z₂.i Z₁.i τ mu ∧ w₂ ≫ Z₂.π = w₁ ≫ Z₁.π ≫ τ ∧ Z₁.FlagAt w₁ u ∧ Z₂.FlagAt w₂ (fun σ i => u σ i ≫ mu.φ)

def NatCorr (Z₁ Z₂ : Mdl Y i₀) : Prop := Z₂.i.l.Dvd Z₁.i.l ∧ Z₂.i.c.F ≤ Z₁.i.c.F ∧ ProperLE Dw Z₂.ty Z₁.ty

def IsNatMap (Z₁ Z₂ : Mdl Y i₀) (f : Z₁.X ⟶ Z₂.X) : Prop :=
  NatCorr Z₁ Z₂ ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ Z₁.X), Set.range w ⊆ Z₁.opn → NatImg Z₁ Z₂ w (w ≫ f)

def Corr (Z₁ Z₂ : Mdl Y i₀) : Prop := Z₂.i.l.Dvd Z₁.i.l ∧ Z₂.i.c.F ≤ Z₁.i.c.F ∧ ∀ σ, Z₂.ty σ ⊆ Z₁.ty σ

def IsMap (Z₁ Z₂ : Mdl Y i₀) (f : Z₁.X ⟶ Z₂.X) : Prop :=
  Corr Z₁ Z₂ ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ Z₁.X), Set.range w ⊆ Z₁.opn → NatImg Z₁ Z₂ w (w ≫ f)

def IsNBlow (Z : Mdl Y i₀) (J : Z.Idl) (Z' : Mdl Y i₀) : Prop :=
  Z'.i = Z.i ∧ Z'.ty = Z.ty ∧ ∃ (X' : Scheme.{0}) (b : X' ⟶ Z.X) (ν : Z'.X ⟶ X'),
    ReciprocityTheory.AnForm.R.FinalTheorems.Blowup b J.1 ∧ IsFinite ν ∧ IsMap Z' Z (ν ≫ b)

def IsNatDiag (Z₁ Z₂ Z' : Mdl Y i₀) : Prop :=
  Z'.i = Z₁.i ∧ Z'.ty = Z₁.ty ∧ ∃ (f₁ : Z'.X ⟶ Z₁.X) (f₂ : Z'.X ⟶ Z₂.X), IsMap Z' Z₁ f₁ ∧ IsNatMap Z' Z₂ f₂ ∧
    IsFinite (prod.lift f₁ f₂)

def IsDiag (Z₁ Z₂ Z' : Mdl Y i₀) : Prop :=
  Z'.i = Z₁.i ∧ Z'.ty = Z₁.ty ∧ ∃ (f₁ : Z'.X ⟶ Z₁.X) (f₂ : Z'.X ⟶ Z₂.X), IsMap Z' Z₁ f₁ ∧ IsMap Z' Z₂ f₂ ∧
    IsFinite (prod.lift f₁ f₂)


open Classical in
def blowUp (Z : Mdl Y i₀) (J : Z.Idl) : Mdl Y i₀ := if h : ∃ Z', IsNBlow Z J Z' then h.choose else Z


open Classical in
def natDiagCl (Z₁ Z₂ : Mdl Y i₀) : Mdl Y i₀ := if h : ∃ Z', IsNatDiag Z₁ Z₂ Z' then h.choose else Z₁


open Classical in
def diagCl (Z₁ Z₂ : Mdl Y i₀) : Mdl Y i₀ := if h : ∃ Z', IsDiag Z₁ Z₂ Z' then h.choose else Z₁

theorem NatCorr.refl (Z : Mdl Y i₀) : NatCorr Z Z := ⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl, fun _ _ hk _ _ => hk⟩

def IsLvl (i₀ i : Idx H p) : Option ℕ → Prop
  | none => i = i₀
  | some n => i.l.M = i₀.l.M ∧ i.l.Mb = i₀.l.Mb ∧ i.l.A = i₀.l.A * p ^ n ∧
      i.c.F = i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta i.l.M'}

structure Bases (Y : LocalSystem Xo p W) (i₀ : Idx H p) : Type where

  X : Option ℕ → Mdl Y i₀

  lvl : ∀ b, IsLvl i₀ (X b).i b

  iso : ∀ b, IsIso (X b).π

  ty : ∀ b σ, (X b).ty σ = ∅

end GlobalTheory.LocM
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RSideA
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL]
  {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}


set_option maxHeartbeats 4000000 in
def RSideA (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) : Prop :=
  HEq R'.ψ z.R.ψ ∧ HEq R'.θ z.R.θ ∧ HEq R'.βW z.R.βW ∧ HEq R'.βY z.R.βY ∧ HEq R'.ΛY z.R.ΛY ∧ HEq R'.βV z.R.βV ∧
  HEq R'.ΛV z.R.ΛV ∧ HEq R'.ΛW z.R.ΛW ∧ HEq R'.Pg z.R.Pg ∧ HEq R'.eG z.R.eG ∧ HEq R'.Sb z.R.Sb ∧
  (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (R'.cV i').W (z.R.cV i).W ∧ HEq (R'.cV i').ρ (z.R.cV i).ρ ∧ HEq (R'.cV i').nW (z.R.cV i).nW ∧
    HEq (R'.cV i').iW (z.R.cV i).iW) ∧
  ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ (ok : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).Ok)
      (ok' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).Ok)
      (φ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).EqFun)
      (φ' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).EqFun),
      (∀ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (φ'.1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (φ.1 d).1)) →
      HEq (R'.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).res ok' φ' :))))
        (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok φ :))))


variable (w' Z' hX' T') in
def Kept (Wt' : Set B'.places.Pl) (R : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG : G0 R.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd) : Prop :=
  LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R.eG ∧
    GoodSet (w'.st Z') (px := w'.px) (R.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' Wt' R.mu R.twPl ∧
    IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A ∧
    R.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).lv2 ∧ R.IsInert ∧ R.IsTup ∧ R.AllPlaces ∧
    Keep R.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).lv2 cG ∧
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R.toRealDat

end GlobalTheory.Mem.R3.Rw

end
end

