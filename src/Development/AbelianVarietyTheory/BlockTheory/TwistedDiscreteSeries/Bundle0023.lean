module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ThetaTrace

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

def IsHeckePrime (l : Level H) (P : Ideal (𝓞 E)) (p : ℕ) : Prop :=
  P.IsMaximal ∧ P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ (l.M' : 𝓞 E) ∉ P ∧ p.Prime ∧ (p : 𝓞 E) ∈ P

variable {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def FinAt (P : Ideal (𝓞 E)) (p i : ℕ) : Prop :=
  HkFin (K := c.F) (fun S _ _ => FrPt Xo c S) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)

def TotalAt (P : Ideal (𝓞 E)) (p i : ℕ) : Prop :=
  HkTotal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)
    (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z)

def FunAt (P : Ideal (𝓞 E)) (p i : ℕ) : Prop :=
  HkFun (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
    (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)
    (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z)

def DetectAt (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  PtsDetect (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
    (ex Dw a n)

end Local

def HeckeFinite : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), IsHeckePrime l P p → FinAt Xo c P p i

def HeckeTotal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), IsHeckePrime l P p → TotalAt Xo c P p i

def HeckeSingleValued : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), IsHeckePrime l P p → FunAt Xo c P p i

def PointsDetect : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), DetectAt Xo c a n

def HeckePointLaws : Prop := HeckeFinite ∧ HeckeTotal ∧ HeckeSingleValued ∧ PointsDetect

section Basic₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff {P : Ideal (𝓞 E)} {p : ℕ} :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P p ↔ P.IsMaximal ∧ P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧
      p.Prime ∧ (p : 𝓞 E) ∈ P ∧ ¬ p ∣ l.M' := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime
  constructor
  · rintro ⟨hmax, hsplit, hM, hp, hpP⟩
    refine ⟨hmax, hsplit, hp, hpP, fun hdvd => hM ?_⟩
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.cast_mul]
    exact P.mul_mem_right _ hpP
  · rintro ⟨hmax, hsplit, hp, hpP, hndvd⟩
    refine ⟨hmax, hsplit, fun hM => hmax.ne_top ?_, hp, hpP⟩
    have hcop : IsCoprime (p : ℤ) (l.M' : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd)
    obtain ⟨u, v, huv⟩ := hcop.map (Int.castRingHom (𝓞 E))
    rw [Ideal.eq_top_iff_one, ← huv]
    simp only [eq_intCast, Int.cast_natCast]
    exact P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hM)

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def IsFinExt (T T' : CDVR) (i : T.Fr →+* T'.Fr) : Prop :=
  (letI := i.toAlgebra; FiniteDimensional T.Fr T'.Fr) ∧
    ∃ r : ℕ, 0 < r ∧ ∀ x : T.Fr, vV T'.V (i x) = (r : ℤ) * vV T.V x


variable (H l) in
def IsHeckePrime (𝔓 : Ideal (𝓞 E)) (p : ℕ) : Prop :=
  𝔓.IsMaximal ∧ 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ p.Prime ∧ (p : 𝓞 E) ∈ 𝔓 ∧ ¬ p ∣ l.M'

variable (Xo : Moduli Dw l) (c : Coeff l)

abbrev PtClass : Type 1 := ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop

def goodCls : PtClass Xo c := fun _ _ y => GlobalTheory.GoodPts.Good y

def trivialClassCondition : PtClass Xo c := fun _ _ _ => True

variable {Xo c}

def IsIntegralUpToUnits (cls : PtClass Xo c) (T : CDVR) (io : c.F →+* T.Fr) {Ω : Type} [Field Ω] [Algebra c.F Ω]
    (k : T.Fr →+* Ω) (z : FrPt Xo c Ω) : Prop :=
  ∃ (T' : CDVR) (i : T.Fr →+* T'.Fr), IsFinExt T T' i ∧
    letI := (i.comp io).toAlgebra
    ∃ (j : T'.Fr →ₐ[c.F] Ω), j.toRingHom.comp i = k ∧
      ∃ (y' : IntFr Xo c T' (i.comp io)), y'.IsAlg ∧ cls T' (i.comp io) y' ∧
        ∃ (w : FrPt Xo c Ω) (u : Ix Dw → T'.Vˣ), FrMap j y'.1 w ∧
          FrBor (fun a => Units.map (j.toRingHom.comp (algebraMap T'.V T'.Fr)).toMonoidHom (u a)) w z

variable (Xo c)

def AtHeckePoints (cls : PtClass Xo c)
    (Q : ∀ (_ : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (_ : c.F →+* T.Fr) (Ω : Type) [Field Ω] [Algebra c.F Ω],
      (T.Fr →+* Ω) → FrPt Xo c Ω → Prop) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), IsHeckePrime H l 𝔓 p →
    (p : 𝓞 c.F) ∉ la.asIdeal →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    ∀ y : IntFr Xo c T io, algCls Xo c T io y → cls T io y →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω],
      letI := io.toAlgebra
      ∀ k : T.Fr →ₐ[c.F] Ω, (letI := k.toRingHom.toAlgebra; Algebra.IsAlgebraic T.Fr Ω) →
      ∀ yΩ : FrPt Xo c Ω, FrMap k y.1 yΩ →
      ∀ (C : hkKer (Xo := Xo) 𝔓 p i Ω yΩ) (z : FrPt Xo c Ω),
        hkRelFr 𝔓 p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω yΩ C z → Q la T io Ω k.toRingHom z

def HeckeFrameInt (cls : PtClass Xo c) : Prop :=
  AtHeckePoints Xo c cls fun _ T io _ _ _ k z => IsIntegralUpToUnits cls T io k z

def HeckeValueInt (cls : PtClass Xo c) : Prop :=
  AtHeckePoints Xo c cls fun la T _ _ _ _ k z =>
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n →
        (∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) →
        (k.comp (algebraMap T.V T.Fr)).IsIntegralElem (evR Xo c f z)

def HeckeIntGood : Prop := HeckeFrameInt Xo c (goodCls Xo c) ∧ HeckeValueInt Xo c (goodCls Xo c)

def HeckeIntAll : Prop := HeckeFrameInt Xo c (trivialClassCondition Xo c) ∧ HeckeValueInt Xo c (trivialClassCondition Xo c)

def HeckeInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), HeckeIntGood Xo c ∧ HeckeIntAll Xo c

end GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

open NumberField Matrix
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsONLatBasis (V : HSp D) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) : Prop :=
  (∀ a a', ∑ i, ∑ j, star (b i a) * V.gram i j * b j a' = if a = a' then 1 else 0) ∧
    L0c D V = (Submodule.span (𝓞 D.host.E) (Set.range fun a i => b i a) : Set (Fin V.rank → D.host.E))

def realPt (S T : HSp D) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : WO S T :=
  Matrix.of fun i j => (pairA D.host.F 1 0) ⊗ₜ[D.host.F] X i j

def thetaAt (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (v : WO S T → ℂ) (g : GA D T) (w : WO S T) : ℂ :=
  heisO ψ S T w (om (1, g) v) 0

theorem thetaAt_eq (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (v : WO S T → ℂ) (g : GA D T) (w : WO S T) : thetaAt ψ om v g w = om (1, g) v w := by
  simp [thetaAt, heisO, symplOH, symplO, hO]

section Period

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

def perVec (Wt : UnfAt U k x) (v : Fin r → D.host.E) : Fin Wt.g → ℂ :=
  fun j => perFr (U.X k) x.1 v (relab c σ (Wt.e j).1) (Wt.e j).2

theorem perVec_lat (Wt : UnfAt U k x) (a : (Wt.F.Di (Wt.ik k)).La) :
    perVec Wt (Wt.φ k a : Fin r → D.host.E) = Wt.Pm a := funext fun j => (Wt.pm_eq a j).symm

end Period

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ)
  (hV : T.V ((i : ℕ) + 1) σ = Wc D i)

abbrev dictW : GA D (Wc D i) → Σ k, Frame ((T.U ((i : ℕ) + 1) σ).X k).Ψ D.R.r := castDict hV (T.dict ((i : ℕ) + 1) σ)

abbrev phiW (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) : GA D (Wc D i) → ℂ :=
  castDict hV (T.phiJ ((i : ℕ) + 1) σ a f)

def FramePin : Prop :=
  ∃ (ph : ℂ) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), ‖ph‖ = 1 ∧ IsONLatBasis (Vc D i) b ∧
    ∀ (h : GA D (Wc D i)), ∀ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (dictW T i σ hV) γ h →
      ∀ (hx : (dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1).dom)
        (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩) (Y : UnitAt Wt)
        (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (z : Fin (Vc D i).rank → Fin Wt.g → ℂ),
        (∀ a, z a = perVec Wt fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a) →
        Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (z a) (z a)) *
            thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * h) (realPt (Vc D i) (Wc D i) X) =
          ph * (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) * ∏ a, Y.θ (z a)


omit [Algebra T.Q.c.F D.what₂.LL] in
theorem exists_witness (hL : LawsM T.toCore) (hσ : GoodEmb T.Q.c σ) (h : GA D (Wc D i)) :
    ∃ (hx : (dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1).dom)
      (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩), Nonempty (UnitAt Wt) := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨th, hr, -, hd⟩ := hL.dictU _ hj σ hσ
  have hx := hd.2.2.2.1 (cast (congrArg (GA D) hV.symm) h)
  obtain ⟨Wt⟩ := nonempty_unfAt (hL.unf _ hj σ hσ) _ ⟨_, hx⟩
  exact ⟨hx, Wt, nonempty_unitAt Wt ((hL.muUnit _ hj σ hσ).2.2.2 _)⟩

def GeoHecke (j : ℕ) (𝔓 : Ideal (𝓞 D.host.E)) (p k : ℕ) (s : T.Q.c.F) (f g : T.R j) : Prop :=
  HkRel (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z)
    (fun Ω _ _ _ y => hkKer (Xo := T.Q.Xo j) 𝔓 p k Ω y)
    (fun Ω _ _ _ y C z => hkRelFr 𝔓 p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo j) T.Q.c p) Ω y C z) s f g

def IsUnitaryHeckeOperatorSplitPrimeData (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))) : Prop :=
  Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧ p.Prime ∧ (p : 𝓞 D.host.E) ∈ P.asIdeal ∧ ¬ p ∣ T.Q.l.M' ∧
    k ≤ D.R.r ∧ IsHeckeAt (Wc D i) P k α ∧ Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc

def muAt (P : Formalism.L2.DIV.Pl D.host.E) : ℂ := (((R.C.mu0 i).val P : ℂˣ) : ℂ)

def ReadsAt (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) : Prop :=
  ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
    IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc → ∀ (cq : T.Q.c.F) (f g : T.R ((i : ℕ) + 1)),
      f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA κ) κ.n → g ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA κ) κ.n →
      GeoHecke T ((i : ℕ) + 1) P.asIdeal p k (hkScal T.Q.c cq P.asIdeal k D.R.nV) f g →
      ∀ h, phiW T i σ hV (wtA κ) g h =
        σ cq * (muAt T R i P)⁻¹ ^ k * ∑ a ∈ Rc, phiW T i σ hV (wtA κ) f (h * a)

variable {T R i σ hV}

theorem ReadsAt.modulus {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} (H : ReadsAt T R i σ hV κ) {P : Formalism.L2.DIV.Pl D.host.E} {p k : ℕ}
    {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))} (hs : IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc) {f g : T.R ((i : ℕ) + 1)}
    (hf : f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA κ) κ.n) (hg : g ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA κ) κ.n)
    (hr : GeoHecke T ((i : ℕ) + 1) P.asIdeal p k
      (hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV) f g) (h : GA D (Wc D i)) :
    phiW T i σ hV (wtA κ) g h =
      (muAt T R i P)⁻¹ ^ k * (Nat.card (kP P) : ℂ)⁻¹ ^ (k * D.R.nV / 2) * ∑ a ∈ Rc, phiW T i σ hV (wtA κ) f (h * a) := by
  rw [H P p k α Rc hs _ f g hf hg hr h, map_pow, map_inv₀, map_natCast, mul_comm ((Nat.card (kP P) : ℂ)⁻¹ ^ _)]

end GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.ThetaTrace

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}


variable (l) in
structure IsSplitOff (P : Ideal (𝓞 E)) (p : ℕ) : Prop where
  max : P.IsMaximal
  split : P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤
  prime : p.Prime
  under : (p : 𝓞 E) ∈ P
  off : ¬ p ∣ l.M'

variable (Xo : Moduli Dw l) (c : Coeff l)

def HasTransform (P : Ideal (𝓞 E)) (p i : ℕ) (cq : c.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  HkEx (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
    (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z)
    (ex Dw a n) (hkScal c cq P i n)

def Detects (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  PtsDetect (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (ex Dw a n)

def FinKer (P : Ideal (𝓞 E)) (p i : ℕ) : Prop :=
  HkFin (K := c.F) (fun S _ _ => FrPt Xo c S) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)

def IsTransform (P : Ideal (𝓞 E)) (p i : ℕ) (cq : c.F) (n : ℕ) (f g : Rul Xo c) : Prop :=
  HkRel (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
    (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z)
    (hkScal c cq P i n) f g

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

attribute [local instance 1100] Submodule.module

def cuspIn (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    @Submodule ↥c.F ↥(sec Xo c a n) _ _ (Submodule.module (sec Xo c a n)) := by
  letI : Module ↥c.F ↥(sec Xo c a n) := Submodule.module (sec Xo c a n)
  exact (cusp Xo c U a n).comap (sec Xo c a n).subtype

def KeepsCusp (P : Ideal (𝓞 E)) (p i : ℕ) (cq : c.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ (hE : HasTransform Xo c P p i cq a n) (hD : Detects Xo c a n) (hF : FinKer Xo c P p i),
    HeckeStabW hE hD hF (cuspIn Xo c U a n)

variable {Xo c U} {P : Ideal (𝓞 E)} {p i : ℕ} {cq : c.F} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}

theorem keepsCusp_iff_exists (hE : HasTransform Xo c P p i cq a n) (hD : Detects Xo c a n)
    (hF : FinKer Xo c P p i) : KeepsCusp Xo c U P p i cq a n ↔
      ∀ f ∈ cusp Xo c U a n, ∃ g ∈ cusp Xo c U a n, IsTransform Xo c P p i cq n f g := by
  constructor
  · intro h f hf
    exact ⟨_, h hE hD hF ⟨f, hf.1⟩ hf, hkOp_spec hE hD hF ⟨f, hf.1⟩⟩
  · intro h hE' hD' hF' f hf
    obtain ⟨g, hg, hr⟩ := h f hf
    have e := hkRel_unique hD' (hkOp hE' hD' hF' f).2 hg.1 (hkOp_spec hE' hD' hF' f) hr
    show (hkOp hE' hD' hF' f).1 ∈ cusp Xo c U a n
    rw [e]
    exact hg

end Local

def SecTransform : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ) (cq : c.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
    1 ≤ Dw.p + Dw.q → IsSplitOff l P p → i ≤ Dw.p + Dw.q → Even n → HasTransform Xo c P p i cq a n

def CuspTransform : Prop :=
  ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j →
    ∀ (P : Ideal (𝓞 D.host.E)) (p i : ℕ) (cq : T.Q.c.F) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ),
      IsSplitOff T.Q.l P p → i ≤ D.R.r → Dom a n → KeepsCusp (T.Q.Xo j) T.Q.c (T.U j) P p i cq a n

def HeckeTransform : Prop := SecTransform ∧ CuspTransform

end GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection
end
end

