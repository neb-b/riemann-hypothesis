module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1153

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4

namespace GlobalTheory.Mean4O

section Comb

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

def lnAdl (A : Adl C Y) (σ : F →+* ℂ) (z : Pts Y σ) : ℝ :=
  lnN (A.m σ) (genAt A.D (under z)) z - (A.n : ℕ) * A.ci (InfinitePlace.mk σ)

end Comb

section Base

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag)

def LiesUnder (k : s.Comp) (y : Pt s) (x : (Φ.C k).Y.X) : Prop :=
  ∃ p : Sp Qb ⟶ (Φ.C k).Y.X, p ≫ (Φ.C k).π = y.y ∧ (Φ.C k).Carries p y.frame ∧ below p = x

def baseOn (k : s.Comp) (y : Pt s) : (Φ.C k).Y.X := Classical.epsilon (LiesUnder Φ k y)

abbrev basePt (y : Pt s) : (Φ.C (compPt s y)).Y.X := baseOn Φ (compPt s y) y

variable {Φ}

theorem LiesUnder.compPt_eq {k : s.Comp} {y : Pt s} {x : (Φ.C k).Y.X} (h : LiesUnder Φ k y x) : compPt s y = k := by
  obtain ⟨p, hp, -, -⟩ := h
  let o : Sp Qb := IsLocalRing.closedPoint Qb
  refine (PtComp.existsUnique_onComp s (y.y o)).unique (PtComp.onComp_compPt s y o) ?_
  obtain ⟨z, hz⟩ : ((s.U κ.σ₀).X k).dom.Nonempty := GlobalTheory.OrbitScalar.exists_mem_dom _
  refine ⟨⟨z, hz⟩, fun pt => ?_⟩
  exact (isPreconnected_range (Φ.C k).π.continuous).subset_connectedComponent ⟨p o, by rw [← hp]; rfl⟩
    (Φ.label k ⟨z, hz⟩ pt)


variable (Φ) in
theorem existsUnique_liesUnder (y : Pt s) : ∃! x, LiesUnder Φ (compPt s y) y x := by
  have : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  obtain ⟨⟨k, p⟩, hp, hu⟩ := Φ.lifts Qb y.fK y.y y.y_over y.frame
  obtain rfl : compPt s y = k := LiesUnder.compPt_eq ⟨p, hp.1, hp.2, rfl⟩
  refine ⟨below p, ⟨p, hp.1, hp.2, rfl⟩, ?_⟩
  rintro _ ⟨q, h₁, h₂, rfl⟩
  rw [eq_of_heq (Sigma.mk.inj (hu ⟨_, q⟩ ⟨h₁, h₂⟩)).2]


variable (Φ) in
theorem liesUnder_basePt (y : Pt s) : LiesUnder Φ (compPt s y) y (basePt Φ y) :=
  Classical.epsilon_spec (existsUnique_liesUnder Φ y).exists

end Base

section Roots

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

def rootEx (τ : E →+* ℂ) (i : ℕ) : Letter Dw → ℤ := expo Dw (rootSym Dw (fun _ => false) none τ i)


open Classical in
theorem expo_single (a : Sym E) (n : ℤ) (x : Letter Dw) :
    expo Dw (Finsupp.single a n) x = if letterOf Dw a.2.2 = some x then n else 0 :=
  Finsupp.sum_single_index (by simp)

end Roots

structure MetIn {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) : Type where

  hm : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL)

  h0 : ∀ k σ (n : Letter S.Dw → ℤ), (cxSt D.what₂.LL).Met (Φ.C k).Y σ (divOf (Φ.C k) n)

  r : ∀ k σ, Pts (Φ.C k).Y σ → ℝ

  ab : ∀ k, Adl (cxSt D.what₂.LL) (Φ.C k).Y

  dir : D.what₂.Tau → Fin N → ℝ

  reg : ∀ k σ, (D.what₂.Tau → Fin N → ℝ) → ℝ → Pts (Φ.C k).Y σ → ℝ

structure Setup (D : D7) : Type 1 where

  A : Amb D

  N : ℕ

  j : ℕ
  indef : 1 ≤ j ∧ j < N

  S : Sig A N j

  κ : Lv A

  s : FinalTheorems S κ

  L : CmList A

  Φ : s.Flag
  dim_eq : ∀ k, (Φ.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N

  B : s.Bd L

  fl : s.Comp → D.what₂.Tau → ℂˣ

  Mb : ℝ → (D.what₂.Tau → Fin N → ℝ) → ℚ → ∀ k, Adl (cxSt D.what₂.LL) (Φ.C k).Y

  jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)

  ng : NgPkg

  loc : LocSt D N j ng

  glob : GlobSt fun p => (loc.loc p).Mdl

  adm : AdmSt D N j jC

  met : MetIn Φ

namespace Setup

variable {D : D7} (O : Setup D)

def pad : PadPkg D O.N O.j O.s.Comp O.jC O.ng :=
  padAt O.s O.loc O.glob O.adm (flatSt O.s O.Φ O.met.hm) (arIn O.s O.Φ O.met.hm)

def kit (key : KeySec O.s.Xo O.κ.c) : Kit O.s O.L (cxSt D.what₂.LL) O.jC O.ng :=
  ⟨O.Φ, O.dim_eq, key, O.B, O.fl, O.Mb, O.pad, fun _ => Iff.rfl⟩

def Y : DV.ShimX D.what₂.Tau :=
  shimXOfPkg (O.s.cx O.L O.B O.fl) (O.s.alg O.L (cxSt D.what₂.LL) (cutSt _) (resSt _) O.Φ O.dim_eq O.Mb) O.pad O.indef
    O.κ.primes fun _ hp => Nat.prime_of_mem_primeFactors hp

abbrev var (c : O.s.Comp) : Var D.what₂.LL := (O.Φ.C c).Y

abbrev ex (x : DV.Rt D.what₂.Tau O.N) : Letter O.S.Dw → ℤ := rootEx O.S.Dw (DV.tauEmb D x.1) x.2

def adl0 (c : O.s.Comp) (w : Sym D.host.E →₀ ℤ) : Adl (cxSt D.what₂.LL) (O.var c) :=
  adlOf (O.Φ.C c) (fun _ => O.met.h0 c) w

def htWt {c : O.s.Comp} (ρ : DV.Rt D.what₂.Tau O.N → Adl (cxSt D.what₂.LL) (O.var c)) (u : D.what₂.Tau → Fin O.N → ℝ)
    (z : (O.var c).X) : ℝ := -∑ x, u x.1 x.2 * (ρ x).ht z

def chg (c : O.s.Comp) (R : Option ℝ) (u : D.what₂.Tau → Fin O.N → ℝ) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ) : ℝ :=
  ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 * lnRatio (O.met.hm c R σ (O.ex x)) (O.met.h0 c σ (O.ex x)) z

structure LatModel (P : Finset ℕ) (c : O.s.Comp) : Type 1 where

  V : Cover (O.var c)

  line : Finset ℕ → ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ → HermLB V.p
  line_spec : ∀ Q ⊆ P, ∀ st, (letterOf O.S.Dw st).isSome →
    V.Induces (O.adl0 c (Finsupp.single (ArIn.ind Q, none, st) 1)) (line Q st) 1

  k : ℕ
  k_pos : 0 < k

  amp : HermLB V.p
  amp_spec : V.Induces (O.met.ab c) amp k

namespace LatModel

variable {O} {P : Finset ℕ} {c : O.s.Comp} (W : O.LatModel P c)

end LatModel

end Setup

end GlobalTheory.Mean4O
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

abbrev Fld (Z : Scheme.{0}) : Type := ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)

section General

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ}

def IsTr {S : Type} [CommRing S] (φ : R →+* S) (g : Sp S ⟶ G.left) (v : TanM (𝟙 (Sp R)) G)
    (w : Sp (DualNumber S) ⟶ G.left) : Prop :=
  ∃ g' v' : tEpsG (g ≫ G.hom) ⟶ G, g'.left = spMap (algebraMap S (DualNumber S)) ≫ g ∧
    v'.left = spMap (dualMap φ) ≫ (tv v).left ∧ (g' * v').left = w

def IsInv (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) : Prop :=
  IsField ⊤ dd ∧ ∀ (S : Type) [CommRing S] (φ : R →+* S) (g : Sp S ⟶ G.left) (w : Sp (DualNumber S) ⟶ G.left)
    (O : G.left.Opens) (f : Γ(G.left, O)), g ≫ G.hom = spMap φ → ⊤ ≤ g ⁻¹ᵁ O → IsTr G φ g v w →
      (valR w O f).snd = valR g O (dd O f)

def IsLift (D : R → R) (W : G.left.Opens) (d : Fld G.left) : Prop :=
  IsField W d ∧ ∀ O, O ≤ W → ∀ r, d O (constFn G.hom O r) = constFn G.hom O (D r)

variable {X : Scheme.{0}} (m : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R)

def dlg (δ : Fld G.left) (i i' : L.ι) (O : G.left.Opens) : Γ(G.left, O) :=
  δ O (pbT m (L.g i i').val O) * pbT m (L.g i i')⁻¹.val O

def KSRel (Θ : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ (J : Type) (W : J → G.left.Opens) (j : J → L.ι) (d : J → Fld G.left),
    ⨆ i, W i = ⊤ ∧ (∀ i, W i ≤ m ⁻¹ᵁ L.U (j i)) ∧ (∀ i, IsLift G D (W i) (d i)) ∧
    ∀ i i' O, O ≤ W i ⊓ W i' → ∀ f, d i O f - d i' O f =
      ∑ a, ∑ b, constFn G.hom O (Θ a b) * dlg G m L (dd b) (j i) (j i') O * dd a O f

def op (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R) (d : Fld G.left) {W : G.left.Opens} (p p' : Γ(G.left, W)) (k : ℕ)
    (O : G.left.Opens) (f : Γ(G.left, O)) : Γ(G.left, O) :=
  2 * (k : Γ(G.left, O)) * d O f - ∑ a, ∑ b, constFn G.hom O (Θ a b) * dd a O (dd b O f) +
    2 * ∑ a, constFn G.hom O (u a) * dd a O f + (2 * (k : Γ(G.left, O)) ^ 2 * rsT p O + 2 * (k : Γ(G.left, O)) * rsT p' O) * f

structure Heat where

  Θ : Matrix (Fin n) (Fin n) R
  symm : Θᵀ = Θ

  u : Fin n → R

  J : Type

  W : J → G.left.Opens

  j : J → L.ι

  d : J → Fld G.left

  p : ∀ i, Γ(G.left, W i)

  p' : ∀ i, Γ(G.left, W i)
  cover : ⨆ i, W i = ⊤
  le : ∀ i, W i ≤ m ⁻¹ᵁ L.U (j i)
  lift : ∀ i, IsLift G D (W i) (d i)
  glue : ∀ (k : ℕ) i i' O, O ≤ W i ⊓ W i' → ∀ f,
    op G dd Θ u (d i) (p i) (p' i) k O (pbT m (L.g (j i) (j i')).val O ^ k * f) =
      pbT m (L.g (j i) (j i')).val O ^ k * op G dd Θ u (d i') (p i') (p' i') k O f

abbrev SecM {Y : Scheme.{0}} (m : Y ⟶ X) (L : LB X) (k : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ))

variable {G m L dd D}

def Heat.Acts (h : Heat G m L dd D) (k : ℕ) (τ τ' : SecM m L k) : Prop :=
  ∀ i, rsT (τ'.f fun _ => h.j i) (h.W i) =
    op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) (rsT (τ.f fun _ => h.j i) (h.W i))

end General

def ringOp {Ω : Type} [CommRing Ω] {n : ℕ} (d : Ω → Ω) (dd : Fin n → Ω → Ω) (Θ : Matrix (Fin n) (Fin n) Ω) (u : Fin n → Ω)
    (p p' : Ω) (k : ℕ) (f : Ω) : Ω :=
  2 * (k : Ω) * d f - ∑ a, ∑ b, Θ a b * dd a (dd b f) + 2 * ∑ a, u a * dd a f + (2 * (k : Ω) ^ 2 * p + 2 * (k : Ω) * p') * f

def epsHom {Ω : Type} [CommRing Ω] (δ : Derivation ℤ Ω Ω) : Ω →+* DualNumber Ω where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (δ s)
  map_one' := by ext <;> simp
  map_zero' := by simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [mul_comm]

def IsValue {X Y : Scheme.{0}} {Ω : Type} [CommRing Ω] (m : Y ⟶ X) (L : LB X) (x : Sp Ω ⟶ Y)
    (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ m)) (k : ℕ) (σ : SecM m L k) (s : Ω) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp Ω) (z : Z) (J), Good L z J →
    sval σ (r ≫ x) z J = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom s) * (val g r z J ^ k).val

section Raynaud

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

def IsTerm (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k) : Prop :=
  ∀ (T : Over (Sp R)) (x : T ⟶ Y.H) y J, Good Q.P.L y J →
    sval τ x.left y J = sval σ (x ≫ Y.q).left y J * (val ((Y.Φ T x).s α) (𝟙 _) y J).val

def IsWt (α : Q.X) (V : Y.H.left.Opens) (f : Γ(Y.H.left, V)) : Prop :=
  ∀ (S : Type) [CommRing S] (φ : R →+* S) (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ)
    (a a' : Sp S ⟶ Y.H.left), a = x.left → a' = x'.left → ⊤ ≤ a ⁻¹ᵁ V → ⊤ ≤ a' ⁻¹ᵁ V → x' ≫ Y.q = x ≫ Y.q →
    (∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) →
    valR a' V f = c α * valR a V f

variable {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D)

def IsBasic : Prop :=
  ∀ i, (∃ V : Q.P.A.left.Opens, h.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h.p i) ∧ IsWt Y 0 _ (h.p' i) ∧
    ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f →
      IsWt Y α (Y.q.left ⁻¹ᵁ V) (h.d i _ f)

def TActs (k : ℕ) (α : Q.X) (σ σ' : Q.SecB k α) : Prop :=
  ∃ τ τ', IsTerm Y k α σ τ ∧ IsTerm Y k α σ' τ' ∧ h.Acts k τ τ'


variable (Q) in
def ShiftEq (k : ℕ) (mu α : Q.X) (σ : Q.SecB k α) (σ₁ : Q.SecB k (α + k • mu)) (c : R) (σ₂ : Q.SecB k (α + k • mu)) : Prop :=
  ∀ u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k)), u.IsGen →
    LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left)
      (DegPre.famMult Q (FractionRing R) k mu α) →
    ∀ z J, Good Q.P.L z J →
      sval σ₁ (DegPre.prB Q (FractionRing R)).left z J =
        (val u (𝟙 _) z J).val * sval σ (DegPre.trF Q (FractionRing R) mu ≫ DegPre.prB Q (FractionRing R)).left z J +
          gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c) * sval σ₂ (DegPre.prB Q (FractionRing R)).left z J

def HasDefect (c : ℕ → Q.X → Q.X → R) : Prop :=
  ∀ (k : ℕ) (mu α : Q.X) (σ σ' : Q.SecB k α) (σ₁ σ₁' : Q.SecB k (α + k • mu)), 1 ≤ k →
    ShiftEq Q k mu α σ σ₁ 0 σ₁ → TActs Y h k α σ σ' → TActs Y h k (α + k • mu) σ₁ σ₁' →
      ShiftEq Q k mu α σ' σ₁' (c k mu α) σ₁

end Raynaud

end GlobalTheory.Heat
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsFreeGenOfFormallyEtale
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.TopForm

namespace GlobalTheory.FieldPair.AdjModel

variable {k K : Type} [Field k] [Field K] {c : k →+* K} {n : ℕ}

theorem exists_place {Q : Subring K} (hQ : IsLocModel c Q) {t : Q} (ht : Prime t) :
    ∃ S : Place c, S.IsPrimeOf Q ∧ S.ord (t : K) = 1 ∧
      ∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ord (t : K) = 0 := by
  let c0 := c.codRestrict Q hQ.const_mem
  haveI : IsNoetherianRing Q := by
    letI := c0.toAlgebra
    haveI : Algebra.EssFiniteType k Q := hQ.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing k Q
  haveI : IsFractionRing Q K := by
    refine IsFractionRing.of_field Q K fun z => ?_
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hQ.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, eq_div_of_mul_eq hb0 e⟩
  let p : Ideal Q := Ideal.span {t}
  haveI : p.IsPrime := (Ideal.span_singleton_prime ht.ne_zero).2 ht
  have hp : p.primeCompl ≤ nonZeroDivisors Q := p.primeCompl_le_nonZeroDivisors
  let A : Subalgebra Q K := Localization.subalgebra.ofField K p.primeCompl hp
  haveI hA : IsLocalization p.primeCompl A := Localization.subalgebra.isLocalization_ofField K _ hp
  haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A p
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing p.primeCompl A inferInstance
  have hm : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap Q A t} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p A, Ideal.map_span, Set.image_singleton]
  have ht0 : algebraMap Q A t ≠ 0 := fun e => ht.ne_zero (Subtype.ext (congrArg (fun z : A => (z : K)) e))
  have hnf : ¬ IsField A := fun hf => ht0 (by
    have := IsLocalRing.isField_iff_maximalIdeal_eq.1 hf
    rw [hm] at this
    exact Ideal.span_singleton_eq_bot.1 this)
  haveI : IsDiscreteValuationRing A :=
    ((IsDiscreteValuationRing.TFAE A hnf).out 1 5).2 (show (IsLocalRing.maximalIdeal A).IsPrincipal from ⟨_, hm⟩)
  haveI : IsFractionRing A K := Localization.subalgebra.isFractionRing_ofField K _ hp
  let V : ValuationSubring K :=
    { A.toSubring with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, e⟩ | ⟨a, e⟩
        · exact Or.inl (e ▸ a.2)
        · exact Or.inr (e ▸ a.2) }
  have hc : ∀ a, c a ∈ V := fun a => A.algebraMap_mem (c0 a)
  let S : Place c := ⟨V, hc, ‹IsDiscreteValuationRing A›, by
    have e : c.codRestrict V hc = (algebraMap Q A).comp c0 := rfl
    rw [e]
    exact RingHom.EssFiniteType.comp hQ.essFiniteType
      ((RingHom.essFiniteType_algebraMap (R := Q) (S := A)).2
        (Algebra.EssFiniteType.of_isLocalization A p.primeCompl))⟩
  have hu : ∀ b : Q, b ∉ p → IsUnit (algebraMap Q A b) := fun b hb =>
    IsLocalization.map_units A (⟨b, hb⟩ : p.primeCompl)
  refine ⟨S, ⟨fun q hq => A.algebraMap_mem ⟨q, hq⟩, fun f hf => ?_⟩, ?_, fun P hP hne => ?_⟩
  · obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj p.primeCompl (⟨f, hf⟩ : A)
    exact ⟨a, a.2, b.1, b.1.2, fun h => b.2 (by rw [show b.1 = 0 from Subtype.ext h]; exact p.zero_mem),
      S.ord_eq_zero (u := algebraMap Q A b.1) (hu _ b.2), congrArg Subtype.val e⟩
  · exact S.ord_irreducible (t := algebraMap Q A t)
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hm)
  · by_contra h0
    have htK : (t : K) ≠ 0 := fun e => ht.ne_zero (Subtype.ext e)
    have h1 : 0 ≤ P.ord (t : K) := (P.ord_nonneg_iff htK).2 (hP.1 _ t.2)
    refine hne (ValuationSubring.eq_of_le_of_ne_top P.ring (fun f hf => ?_) S.ring_ne_top)
    obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hP.2 f hf
    have hbp : (⟨b, hb⟩ : Q) ∉ p := fun h => by
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 h
      have hd' : b = t * d := congrArg Subtype.val hd
      have hd0 : (d : K) ≠ 0 := fun h => hb0 (by rw [hd', h, mul_zero])
      have := (P.ord_nonneg_iff hd0).2 (hP.1 _ d.2)
      rw [hd', P.ord_mul htK hd0] at hbo
      omega
    obtain ⟨g, hg⟩ := (hu _ hbp).exists_right_inv
    have hg' : b * (g : K) = 1 := congrArg Subtype.val hg
    have : f = a * g := by rw [← e, mul_assoc, hg', mul_one]
    rw [this]
    exact A.mul_mem (A.algebraMap_mem ⟨a, ha⟩) g.2


end GlobalTheory.FieldPair.AdjModel
end
end

