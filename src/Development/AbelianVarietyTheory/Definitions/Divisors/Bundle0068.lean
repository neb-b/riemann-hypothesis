module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxOrbitSumsOfGaloisClassSums
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsUnitTermZero
section
noncomputable section

open IsLocalRing GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc.PreModel

section
variable {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {A : Type} [CommRing A] [IsLocalRing A]
  (Φ : VPre bar q W A)

theorem low_finite (y : Φ.Y) (P : (Fin s → Φ.X y) → Prop) (j : ℕ) :
    {mu | P mu ∧ ∑ i, qW W (Φ.δ y i) mu < (j : ℤ)}.Finite := by
  obtain ⟨c₀, hc₀, hq⟩ := GlobalTheory.Poinc.QWDom.qW_ge s W Φ.posW
  let D : LinearMap.BilinForm ℤ (Φ.X y) := ∑ i, Φ.δ y i
  have hD : ∀ x, D x x = ∑ i, Φ.δ y i x x := fun x => by simp [D, LinearMap.sum_apply]
  have hDs : ∀ a b, D a b = D b a := fun a b => by
    simp only [D, LinearMap.sum_apply]; exact Finset.sum_congr rfl fun i _ => (Φ.bal y i).1 a b
  have hDp : ∀ x, x ≠ 0 → 0 < D x x := fun x hx => by
    rw [hD]
    obtain ⟨i, hi⟩ := Φ.pos y x hx
    exact lt_of_lt_of_le hi (Finset.single_le_sum (f := fun i => Φ.δ y i x x) (fun i _ => Φ.nonneg y i x) (Finset.mem_univ i))
  refine (Set.Finite.pi' fun _ : Fin s => GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite _ D hDs hDp ⌈(j : ℝ) / c₀⌉).subset ?_
  rintro mu ⟨-, hmu⟩ u
  have h1 : ∀ i, c₀ * ((∑ u, Φ.δ y i (mu u) (mu u) : ℤ) : ℝ) ≤ (qW W (Φ.δ y i) mu : ℝ) := fun i =>
    hq _ (Φ.δ y i) (Φ.bal y i).1 (Φ.nonneg y i) mu
  have h2 : c₀ * ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) ≤ ((∑ i, qW W (Φ.δ y i) mu : ℤ) : ℝ) := by
    have : ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) = ∑ i, ((∑ u, Φ.δ y i (mu u) (mu u) : ℤ) : ℝ) := by
      simp only [hD]; push_cast; exact Finset.sum_comm
    rw [this, Finset.mul_sum]; push_cast
    exact Finset.sum_le_sum fun i _ => by exact_mod_cast h1 i
  have h3 : (D (mu u) (mu u) : ℝ) ≤ ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) := by
    exact_mod_cast Finset.single_le_sum (f := fun u => D (mu u) (mu u)) (fun u _ => by
      by_cases h : mu u = 0
      · simp [h]
      · exact (hDp _ h).le) (Finset.mem_univ u)
  have h4 : ((∑ i, qW W (Φ.δ y i) mu : ℤ) : ℝ) < j := by exact_mod_cast hmu
  have h5 : (D (mu u) (mu u) : ℝ) ≤ (j : ℝ) / c₀ := by
    rw [le_div_iff₀' hc₀]; nlinarith
  show D (mu u) (mu u) ≤ ⌈(j : ℝ) / c₀⌉
  exact_mod_cast h5.trans (Int.le_ceil _)

end

end GlobalTheory.Poinc.PreModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TInj

section From

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W) (ω : W →+* V)
  {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (D : DegPre V)
  (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (β₂ : (G2 D.P.A).left ⟶ (G2 T.B).left)
  (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull β₂))

def From : Prop :=
  IsGrpPullback D.P.A T.B (spMap ω) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (D.c a).left ≫ β = spMap ω ≫ (T.c₀ ((n : ℤ) • e a)).left) ∧
    ∀ a b, ∃ k : (FractionRing V)ˣ,
      (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e b)) ∧
      ∀ z J J', Good T.M.L z J → Good D.P.L z J' →
        val (D.tau a b) (𝟙 _) z J' = gm (𝟙 (TK V).left) z ⊤ (unitOn k) *
          (lamVal w (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left z J J' *
            val (T.τ₀ ((n : ℤ) • e a) ((n : ℤ) • e b)) ((TK V).hom ≫ spMap ω) z J)

def TautPt (F : Type) [Field F] [Algebra (FractionRing V) F] (a : Fin T.r → ℤ) (g : GtPtF D F) : Prop :=
  g.b.left ≫ β = (TF (R := V) F).hom ≫ spMap ω ≫ (T.c₀ a).left ∧
    ∀ χ, ∃ k : Fˣ, (k : F) = ∏ i, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (s i)) ^ ε i (e χ) a ∧
      ∀ z J J', Good T.M.L z J → Good D.P.L z J' →
        val (g.s χ) (𝟙 _) z J' = gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn k) *
          (lamVal w (lift (DegPre.cF D F χ) g.b).left z J J' *
            val (T.τ₀ ((n : ℤ) • e χ) a) ((TF (R := V) F).hom ≫ spMap ω) z J)

end From

section Tr

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

def Ext (f : R →+* V) {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F]
    (j : F₀ →+* F) : Prop :=
  ∀ r, j (algebraMap (FractionRing R) F₀ (algebraMap R (FractionRing R) r)) =
    algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (f r))

def Tr (f : R →+* V) {D₀ : DegPre R} {D : DegPre V} (hD : IsPullDeg f D₀ D) {F₀ F : Type} [Field F₀]
    [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F) (g₀ : GtPtF D₀ F₀) (g : GtPtF D F) :
    Prop :=
  letI : Algebra (FractionRing R) F := (j.comp (algebraMap (FractionRing R) F₀)).toAlgebra
  ∃ g₁ : GtPtF D₀ F, (g₁.b.left = spMap j ≫ g₀.b.left ∧
    ∀ χ, LB.Gen.Corr D₀.P.L _ _ _ _ (g₁.s χ) (LB.pullGen D₀.P.L _ _ (g₀.s χ) (spMap j))) ∧ IsPullGtF f hD F g₁ g

end Tr

def OverPt {X : Scheme.{0}} {h n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre h n ζ sX) {S : Scheme.{0}}
    (A : PolAV S) (y : S ⟶ X) (α : A.A.left ⟶ c.A.left) : Prop :=
  IsGrpPullback A.A c.A y α ∧ ∃ α₂ : (G2 A.A).left ⟶ (G2 c.A).left, IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (c.P.pull α₂)

def Match {V : Type} [CommRing V] [IsDomain V] (D₁ D₂ : DegPre V) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F]
    [Algebra (FractionRing V) F] : Prop :=
  IsMonHom b ∧ IsIso b ∧
    LBIso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ D₂.P.A D₂.P.L).pull
      (lift (fst D₁.P.A D₁.P.A ≫ b) (snd D₁.P.A D₁.P.A ≫ b) : G2 D₁.P.A ⟶ G2 D₂.P.A).left) ∧
    (∀ χ, ∃ u : LB.Gen (CmpLB D₁ D₂ b (φ.symm.toAddMonoidHom χ) χ), Nrm u) ∧
    ∀ (y : D₁.X) (g : GtPtF D₁ F), GtPtF.IsIota y g →
      ∃ g' : GtPtF D₂ F, Act D₁ D₂ b φ.symm.toAddMonoidHom g g' ∧ GtPtF.IsIota (φ y) g'

def QImg {V : Type} [CommRing V] [IsDomain V] {D₁ D₂ : DegPre V} (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) {F : Type} [Field F]
    [Algebra (FractionRing V) F] {k : ℕ} (p₁ : QkPt D₁ F k) (p₂ : QkPt D₂ F k) : Prop :=
  ∃ p' : QkPt D₂ F k, p'.y = φ p₁.y ∧ Act D₁ D₂ b φ.symm.toAddMonoidHom p₁.g p'.g ∧ QkPt.Equiv D₂ F p' p₂

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

section Point

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

def curvEv (G : V n → Matrix r r ℂ) (v : V n) : Matrix r r (Ev n) := (curvPoly G v).map (MvPolynomial.aeval sym)

def powAt (G : V n → Matrix r r ℂ) (v : V n) (k : ℕ) : Ev n := (curvEv G v ^ k).trace

def transAt (G G' : V n → Matrix r r ℂ) (v : V n) (k : ℕ) : Alt n :=
  ∑ a, ∑ i ∈ Finset.range k, ((curvEv G v ^ i *
    (conn G v (coordVec a) - conn G' v (coordVec a)).map (algebraMap ℂ (Ev n)) * curvEv G' v ^ (k - 1 - i)).trace : Ev n) * dz a

end Point

section Minors

variable {s : ℕ}

def leadMinor (G : Matrix (Fin s) (Fin s) ℂ) (j : ℕ) : ℂ :=
  (G.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) Subtype.val).det

def grD (G : Matrix (Fin s) (Fin s) ℂ) (i : Fin s) : ℝ := (leadMinor G (i + 1)).re / (leadMinor G i).re

def ldPart (G : Matrix (Fin s) (Fin s) ℂ) : Matrix (Fin s) (Fin s) ℂ := Matrix.of fun i j =>
  (G.submatrix (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val).det / leadMinor G j

end Minors

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {r : Type} [Fintype r] [DecidableEq r]

def HolUnitAt (T : M → Matrix r r ℂ) (y : M) : Prop :=
  IsUnit (T y).det ∧ ∀ i, y ∈ (A.e i).source → ∀ a b,
    ∀ᶠ v in 𝓝 (A.e i y), DifferentiableAt ℂ (fun u => T ((A.e i).symm u) a b) v

def SmoothUnitAt (G : M → Matrix r r ℂ) (y : M) : Prop :=
  IsUnit (G y).det ∧ ∀ i, y ∈ (A.e i).source → ∀ᶠ v in 𝓝 (A.e i y), MContDiffAt ∞ (fun u => G ((A.e i).symm u)) v

structure IsGramPair (G G' : M → M → Matrix r r ℂ) : Prop where

  smooth : ∀ y, SmoothUnitAt A (G y) y ∧ SmoothUnitAt A (G' y) y

  trans : ∀ y, ∀ᶠ z in 𝓝 y, ∃ T K K' : M → Matrix r r ℂ, HolUnitAt A T z ∧ HolUnitAt A K z ∧ HolUnitAt A K' z ∧
    ∀ᶠ w in 𝓝 z, G z w = T w * G y w * (K w)ᴴ ∧ G' z w = T w * G' y w * (K' w)ᴴ

def powFld (G : M → M → Matrix r r ℂ) (k : ℕ) (x : A.Pt) : Ev n := powAt (fun v => G x.pt (x.ch.symm v)) x.crd k

def chernFld (G : M → M → Matrix r r ℂ) (j : ℕ) (x : A.Pt) : Ev n := A.chern (G x.pt) j x

def transFld (G G' : M → M → Matrix r r ℂ) (k : ℕ) : A.Fld := fun x =>
  transAt (fun v => G x.pt (x.ch.symm v)) (fun v => G' x.pt (x.ch.symm v)) x.crd k

def DbarCoh (w w' : A.Pt → Ev n) : Prop :=
  A.IsForm (LineForm.fld A w) ∧ A.IsForm (LineForm.fld A w') ∧ A.dbar (LineForm.fld A w) = 0 ∧
    A.dbar (LineForm.fld A w') = 0 ∧ ∃ u, A.IsForm u ∧ LineForm.fld A w - LineForm.fld A w' = A.dbar u

end Manifold

section Variety

variable {F : Type} [Field F] {ι : Type} {m k : ι → ℕ} {X Y : Var F} {σ : F →+* ℂ}

def atlas (X : Var F) (σ : F →+* ℂ) : HolAtlas (CxPts X.str σ) X.dim where
  ι := AlgChart X.str σ X.dim
  e c := c.e
  cover y := have := X.smooth_str; AlgChart.exists_mem_source y
  holo c c' := c.holo_trans c'

structure IsMetricFr (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) : Prop where

  posDef : ∀ y, ∀ A ∈ E.S (under y), ∀ τ, (H A y τ).PosDef

  smooth : ∀ y, ∀ A ∈ E.S (under y), ∀ τ i j, CInfAt (fun z => (H A z τ i j).re) y ∧ CInfAt (fun z => (H A z τ i j).im) y

  trans : ∀ y, ∀ A ∈ E.S (under y), ∀ A' ∈ E.S (under y), ∀ τ,
    H A' y τ = (A' * A⁻¹).map (ratVal · y) τ * H A y τ * ((A' * A⁻¹).map (ratVal · y) τ)ᴴ

theorem isMetricFr_of_isMetricOn {E : Fr (ratOf X) m 0} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}
    (h : IsMetricOn E ⊤ H) : IsMetricFr E H :=
  ⟨fun y => h.posDef y mem_ptsIn_top, fun y => h.smooth y mem_ptsIn_top, fun y => h.trans y mem_ptsIn_top⟩

variable (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)

def gramAt (τ : ι) (y z : CxPts X.str σ) : Matrix (Fin (m τ)) (Fin (m τ)) ℂ := H (E.nonempty (under y)).choose z τ

def chernF (x : ι × ℕ) : (atlas X σ).Pt → Ev X.dim := chernFld (atlas X σ) (gramAt E H x.1) x.2

def grF (x : Root m) (p : (atlas X σ).Pt) : Ev X.dim :=
  ofValues (ddc (fun v => -Real.log (grD (gramAt E H x.1 p.pt (p.ch.symm v)) x.2)) p.crd)

def c1W {L : LB X.X} (ψ : Weight X.str σ L) (p : (atlas X σ).Pt) : Ev X.dim :=
  ofValues (ddc (fun v => ψ.φ (pick ψ.isLB p.pt) (p.ch.symm v)) p.crd)

def ptMap (σ : F →+* ℂ) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str) : CxPts Y.str σ → CxPts X.str σ := PtsOver.map f hf _

def pullGram (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str) (B : Mat m Y.Fn) (z : CxPts Y.str σ) : Mat m ℂ :=
  fun τ => (B * (Mat.map (E.nonempty (under (ptMap σ f hf z))).choose φ)⁻¹).map (ratVal · z) τ *
    H (E.nonempty (under (ptMap σ f hf z))).choose (ptMap σ f hf z) τ *
    ((B * (Mat.map (E.nonempty (under (ptMap σ f hf z))).choose φ)⁻¹).map (ratVal · z) τ)ᴴ

end Variety

section Inhabitants

end Inhabitants

end GlobalTheory.ChernCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

variable {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def ThAt (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ) {N : ℕ} (f : F.X ⟶ PSpace (cycAway n) N) : Prop :=
  P.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) ∧ rig.IsGen ∧ Odd m ∧ 3 ≤ m ∧ IsUnit (m : cycAway n) ∧
    N + 1 = m ^ (4 * (8 * g)) ∧ f ≫ PSpace.str (cycAway n) N = F.s ∧ ThMap P.A P.L rig m (𝟙 F.X) f ∧ IsE8 W

def QFin {X Y : Scheme.{0}} (f : X ⟶ Y) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ f = x ≫ f}

def SymE {S : ThetaSys o Ω} (ρ : S.Real) (m : ℕ) {N : ℕ} (e : Fin N → Ω) : Prop :=
  N = m ^ (4 * S.g) ∧ (m : Ω) ≠ 0 ∧ SymAt ρ.P.A ρ.P.L ρ.rig m (spMap S.R.val.toRingHom ≫ 𝟙 (Sp S.R))
    (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ S.R.val.toRingHom) e

def SysAt (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) : Prop :=
  β.Finite ∧ Function.Injective β ∧ S.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W ρ.P u ∧
    u ≫ F.s = spMap (algebraMap o S.R) ≫ spMap β

def LevAt (β : cycAway n →+* o) {S : ThetaSys o Ω} (u : Sp S.R ⟶ F.X) (Y : RatModel o Ω) (q : Y.Z ⟶ F.X) : Prop :=
  Geo.Tor.IsNormalScheme Y.Z ∧ IsFinite q ∧ Surjective q ∧ q ≫ F.s = Y.s ≫ spMap β ∧
    Y.pt ≫ q = spMap S.R.val.toRingHom ≫ u

def OpenAt (β : cycAway n →+* o) {S : ThetaSys o Ω} (u : Sp S.R ⟶ F.X) (M : RatModel o Ω) (U : M.Z.Opens)
    (c : U.toScheme ⟶ F.X) : Prop :=
  (U : Set M.Z).Nonempty ∧ IsFinite c ∧ Surjective c ∧ c ≫ F.s = U.ι ≫ M.s ≫ spMap β ∧
    ∀ x : Sp Ω ⟶ U.toScheme, x ≫ U.ι = M.pt → x ≫ c = spMap S.R.val.toRingHom ≫ u

def MinorAt (S : ThetaSys o Ω) (X M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) : Prop :=
  X.IsNm S.th ∧ IsProjOver X.s ∧ Geo.Tor.IsNormalScheme X.Z ∧ S.Over₀ M U₀ ∧ S.IsEE M U₀ EE ∧ X.IsHom M (AlgHom.id o Ω) f ∧
    (Xab : Set X.Z) = {x | S.TT X x = ⊥} ∧ IsIso (f ∣_ Xab)

def SameScale (M : RatModel o Ω) {I J : Type} (a : I → Ω) (b : J → Ω) (D : ℕ) : Prop :=
  ∀ z i, M.Div a i z → ∃ j, M.Div b j z ∧ a i ^ D / b j ∈ M.O z ∧ b j / a i ^ D ∈ M.O z

end GlobalTheory.SiegTh

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SymAtOfThList
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.Ex.OneGen GlobalTheory.ThetaPtMove
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.Model

theorem polFib_self {R : Type} [CommRing R] (P : PolAV (Sp R)) : PolFib P.A P.L P.g (𝟙 _) := by
  exact ⟨P, 𝟙 _, rfl, @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl P.A) (inferInstanceAs (IsMonHom (𝟙 P.A))),
    LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (GlobalTheory.PolBaseChange.lbIso_refl P.isLB)⟩

end GlobalTheory.UMin.Model
end
end

