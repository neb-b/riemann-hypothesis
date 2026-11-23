module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelTor

def cycAway (n : ℕ) : Subring ℂ := Subring.closure {zeta n, (n : ℂ)⁻¹}

def zetaAway (n : ℕ) : cycAway n := ⟨zeta n, Subring.subset_closure (Or.inl rfl)⟩

theorem isUnit_natCast {n : ℕ} (hn : n ≠ 0) : IsUnit (n : cycAway n) :=
  IsUnit.of_mul_eq_one ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
    (Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0)))

theorem isPrimitiveRoot_map {n : ℕ} (hn : n ≠ 0) {K : Type} [Field K] (β : cycAway n →+* K) :
    IsPrimitiveRoot (β (zetaAway n)) n := by
  have h₁ : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn) Subtype.val_injective
  have : NeZero (n : K) := ⟨by simpa using ((isUnit_natCast hn).map β).ne_zero⟩
  have h₂ := (h₁.isRoot_cyclotomic (Nat.pos_of_ne_zero hn)).map (f := β)
  rwa [Polynomial.map_cyclotomic, Polynomial.isRoot_cyclotomic_iff] at h₂

def cycBase {n : ℕ} (hn : n ≠ 0) : TBase (cycAway n) n where
  ζ := Units.ofPowEqOne (zetaAway n) n (Subtype.ext (Complex.isPrimitiveRoot_exp n hn).pow_eq_one) hn
  unit := isUnit_natCast hn
  prim _ _ β := isPrimitiveRoot_map hn β

theorem cycBase_ζ {n : ℕ} (hn : n ≠ 0) : ((cycBase hn).ζ : cycAway n) = zetaAway n := rfl

section Param

variable {o R : Type} [CommRing o] [CommRing R] [IsLocalRing R] {m : ℕ}

def IsRelParam (b : o →+* R) (t : Fin m → R) : Prop :=
  (∀ i, t i ∈ maximalIdeal R) ∧ ∀ c : Fin m → R,
    ∑ i, c i * t i ∈ maximalIdeal R ^ 2 ⊔ ((maximalIdeal R).comap b).map b → ∀ i, c i ∈ maximalIdeal R

theorem IsRelParam.mem_of_mem_sq {b : o →+* R} {t : Fin m → R} (h : IsRelParam b t) (c : Fin m → R)
    (hc : ∑ i, c i * t i ∈ maximalIdeal R ^ 2) (i : Fin m) : c i ∈ maximalIdeal R :=
  h.2 c (Ideal.mem_sup_left hc) i

end Param

section Charts

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S)
  {G : Over S} [GrpObj G] (e : F.univ.A.left ⟶ G.left)

def IsUnifOf {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (ξ : Sp R ⟶ S) {G' : Over (Sp R)} [GrpObj G']
    [IsCommMonObj G'] (π : G'.left ⟶ G.left) {D : DegData R I} {A : PolAV (Sp (FractionRing R))} (U : Unif I D A G') : Prop :=
  IsGrpPullback G' G ξ π ∧
    ∃ (y : Sp (FractionRing R) ⟶ F.X) (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
      y ≫ j = jK R ≫ ξ ∧ IsGrpPullback A.A F.univ.A y α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧
        U.gen.hom.left ≫ α ≫ e = pullback.fst G'.hom (jK R) ≫ π

def HasChart [IsOpenImmersion j] (φ : InvFun ℤ) (BD : EffCartierData S) (d : ℕ) (x : S) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : IsRegularLocalRing R) (b : o →+* R) (ξ : Sp R ⟶ S) (m : ℕ) (t : Fin m → R)
    (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : Fin m → R')
    (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G.left) (D : DegData R' (maximalIdeal R'))
    (A : PolAV (Sp (FractionRing R'))) (U : Unif (maximalIdeal R') D A G') (γ : Fin m → LinearMap.BilinForm ℤ D.toPre.X)
    (a : Fin m → ℕ),
    (IsAdicComplete (maximalIdeal R) R ∧ ξ ≫ s = spMap b ∧ ξ (closedPoint R) = x ∧
      IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
      ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified) ∧
    (IsRelParam b t ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, t i} ∧
      ∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ i, t i ∉ p.asIdeal) ∧
    (AdmBase R' (maximalIdeal R') ∧ CharZero R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ ∀ i, r i ^ 2 = ρ (t i)) ∧
    (IsUnifOf F j e (spMap ρ ≫ ξ) π U ∧ Module.finrank ℤ D.toPre.X ≤ g ∧ IsCone id φ γ ∧
      IsMonomial D.toPre r fun i => (2 * n : ℤ) • γ i) ∧
    (∀ i, (a i : ℝ) = d * φ.evalZ ((n : ℤ) • γ i)) ∧ idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, t i ^ a i}

variable {F s j e}

end Charts

abbrev hodge {S : Scheme.{0}} (G : Over S) [GrpObj G] (g : ℕ) : LB S := GlobalTheory.VB.det (GlobalTheory.LieVB.omega G) g

theorem isLB_hodge {S : Scheme.{0}} (G : Over S) [GrpObj G] (g : ℕ) [QuasiSeparated G.hom]
    [SmoothOfRelativeDimension g G.hom] : (hodge G g).IsLB := (GlobalTheory.LieVB.isVB_omega G g).isLB_det

end GlobalTheory.SiegelTor

namespace GlobalTheory.Published

open GlobalTheory.SiegelTor

def SiegelToroidalIntegral : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∃ φ : InvFun ℤ, IsPolFan id g φ ∧ ∀ n : ℕ, 3 ≤ n → Odd n →
    ∃ (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) (_ : IsOpenImmersion j)
      (G : Over S) (_ : GrpObj G) (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ),
      IsProjOver s ∧ SmoothOfRelativeDimension (g * (g + 1) / 2) s ∧ j ≫ s = F.s ∧
      (∀ x : S, x ∈ closure (Set.range j ∩ s ⁻¹' {s x})) ∧
      IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧ IsGrpPullback F.univ.A G j e ∧ abLocus G = Set.range j ∧
      1 ≤ d ∧ (∀ x : S, HasChart F s j e φ BD d x) ∧
      1 ≤ N ∧ IsGenerated (lbPow (hodge G g) N) ∧
      ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB (CechPic.tens (lbPow (hodge G g) (N * k)) (CechPic.dual BD.lb))

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
section
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.MumfordChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def HasChartOf (φ : InvFun (𝓞 E)) (Z : Model Xo c β) (BD : EffCartierData Z.X) (d : ℕ) (x : gen Z) : Prop :=
  ∃ (k : Type) (_ : Field k) (m e : ℕ) (ξ : Sp (ChartRing k m e) ⟶ gen Z) (t : SAB H (Sp (ChartRing k m e)))
    (P : PELUnif (maximalIdeal (ChartRing k m e)) t) (γ : Fin m → levelForms H l.M' P.D.toPre.X)
    (δ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X) (a : Fin m → ℕ),
    ξ (closedPoint _) = x ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
    (FinalTheorems.stalkId (genBdIdeal Z) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom =
      Ideal.span {∏ i, bdParam k m e i} ∧
    (∀ p : Sp (ChartRing k m e), ξ p ∈ genBd Z ↔ ∏ i, bdParam k m e i ∈ p.asIdeal) ∧
    Nonempty (SABMap t Z.t (ξ ≫ genι Z)) ∧
    IsMonomial P.D.toPre (bdParam k m e) (fun i => γ i) ∧
    Module.finrank (𝓞 E) P.D.toPre.X ≤ min D.p D.q ∧
    IsCone H.bar φ δ ∧ (∀ i, (γ i : LinearMap.BilinForm ℤ P.D.toPre.X) = (l.M' : ℤ) • δ i) ∧
    (∀ i, (a i : ℝ) = d * φ.evalZ (γ i : LinearMap.BilinForm ℤ P.D.toPre.X)) ∧
    idlAlong BD.idealSheaf (ξ ≫ genι Z) = Ideal.span {∏ i, bdParam k m e i ^ a i}

variable {φ : InvFun (𝓞 E)} {Z : Model Xo c β} {BD : EffCartierData Z.X} {d : ℕ} {x : gen Z}

theorem level_ne_zero (l : Geo.Tor.Level H) : l.M' ≠ 0 :=
  (Nat.lcm_pos (by have := l.three_le; omega) l.A_pos).ne'

theorem HasChartOf.hasChart (h : HasChartOf φ Z BD d x) : HasChart Z x := by
  obtain ⟨k, _, m, e, ξ, t, P, γ, δ, a, hx, h₁, h₂, h₃, h₄, h₅, -, h₆, h₇, -⟩ := h
  exact ⟨k, _, m, e, ξ, t, P, γ, hx, h₁, h₂, h₃, h₄, h₅, h₆.isPartOfBasis_level (level_ne_zero l) h₇⟩

end GlobalTheory.MumfordChart

namespace GlobalTheory.Published

def ToroidalChartsForFan : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ →
      ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l),
        ∃ (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (d k : ℕ), 1 ≤ d ∧ 1 ≤ k ∧
          SmoothOfRelativeDimension Dw.dim (genStr Y) ∧ FinalTheorems.Snc (genBdIdeal Y) ∧
          (∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G) ∧
          (∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChartOf φ Y BD d x) ∧
          ((GlobalTheory.FlagMod.detOm Y).IsLB → GlobalTheory.IsAmpleLB (GlobalTheory.TorRef.polOf Y k BD))

namespace ToroidalChartsForFan

theorem toroidalCharts (h : ToroidalChartsForFan)
    (hφ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ),
      ∃ φ : InvFun (𝓞 E), IsPolFan H.bar q φ ∧ NoSelfInt H.bar q φ) : ToroidalCharts := by
  intro E _ _ _ H Dw hr l Xo c
  obtain ⟨φ, h₁, h₂⟩ := hφ E H (min Dw.p Dw.q)
  obtain ⟨Y, BD, d, k, -, -, h₃, h₄, -, h₅, -⟩ := h E H Dw hr φ h₁ h₂ l Xo c
  exact ⟨Y, h₃, h₄, fun x hx => (h₅ x hx).hasChart⟩

end ToroidalChartsForFan

end GlobalTheory.Published
end
end

