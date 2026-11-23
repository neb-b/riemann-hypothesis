module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle0001

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM

abbrev HomExtDvr : Prop := LN.HomExtSt

theorem homExtDvr_iff : HomExtDvr ↔
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K]
      (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G',
        IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f :=
  Iff.rfl

def logOm (E : Type) [Field E] [NumberField E] {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) : ℂ :=
  (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / NumberField.rootDiscr E) : ℝ) -
    deriv χ.LFunction 1 / χ.LFunction 1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def EllMap {R R' : Type} [CommRing R] [CommRing R'] {ω : R} {ω' : R'} (C' : Ell H R' ω') (C : Ell H R ω)
    (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left) : Prop :=
  f ω = ω' ∧ IsPolFibre f C.P C'.P φ ∧ IsVecOver f φ C.v C'.v ∧
    ∀ a, (C'.act.act a).left ≫ φ = φ ≫ (C.act.act a).left

def Ell.IsPrincipalAt {R : Type} [CommRing R] {ω : R} (C : Ell H R ω) (σ : R →+* ℂ) : Prop :=
  ∀ (Q : Out.PolAV (Sp ℂ)) (φ : Q.A.left ⟶ C.P.A.left), IsPolFibre σ C.P Q φ → ∀ u : HolUnif Q.A Q.L Q.g,
    ∃ c : ℂ, c ≠ 0 ∧ PureType.IsQuadLattice u.Λ H.d c

def Ell.HasPeriod {M : Type} [Field M] [NumberField M] {ω : 𝓞 M} (C : Ell H (𝓞 M) ω) (x : ℝ) : Prop :=
  ∃ n : (M →+* ℂ) → ℝ, (∀ s, 0 < n s ∧ ∀ r, IsLieNormSq C.P C.v (s.comp (algebraMap (𝓞 M) M)) r ↔ r = n s) ∧
    -meanLog M n = x

def IsFam {R : Type} [CommRing R] {ω : R} (C : Ell H R ω) (T : PAT H (Sp R)) {D : Datum H}
    (h : D.La → D.La → OK H) (L : Submodule (𝓞 E) D.La) (φ : L → (C.P.A ⟶ T.t.G)) : Prop :=
  (∀ a, Serre.IsLinearHom C.act (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) (φ a)) ∧
    (∀ a b, φ (a + b) = φ a * φ b) ∧ (∀ (s : 𝓞 E) a, φ (s • a) = φ a ≫ T.t.act.act s) ∧
    ∀ a b : L, LamEq T.t.PP.L (φ a) (φ b) C.P.L (C.act.act (h a b)) (𝟙 C.P.A)

def OntoAt {S : Scheme.{0}} {I : Type} {B : I → Over S} {A : Over S} [GrpObj A] (φ : ∀ i, B i ⟶ A) {k : Type} [Field k]
    (t : Sp k ⟶ S) : Prop :=
  ∀ y : Over.mk t ⟶ A, ∃ (n : ℕ) (i : Fin n → I) (x : ∀ m, Over.mk t ⟶ B (i m)),
    y = (List.ofFn fun m => x m ≫ φ (i m)).prod

def IsExp {R : Type} [CommRing R] (T : PAT H (Sp R)) (σ : R →+* ℂ) (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (Pe : D.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk (spMap σ) ⟶ T.t.G)) : Prop :=
  IsPeriod D ty Pe ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧
    (∀ z, e z = 1 ↔ z ∈ Pe.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ T.t.act.act a) ∧
    ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
      Out.WeilIs T.t.G T.t.PP.L k (e ((k : ℂ)⁻¹ • Pe a)) (e ((k : ℂ)⁻¹ • Pe b)) (unitOn c)

structure CMLat {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)
    (p q : ℕ) where
  D₁ : Bool → Datum H
  sigP : (D₁ true).p = 1 ∧ (D₁ true).q = 0
  sigM : (D₁ false).p = 0 ∧ (D₁ false).q = 1
  f : ∀ j : Fin p ⊕ Fin q, (D₁ j.isLeft).La →ₗ[𝓞 E] D.La
  pure : ∀ (j : Fin p ⊕ Fin q) a, f j a ∈ PureType.lat hP (if j.isLeft then H.rt0 else -H.rt0)
  hh : Fin p ⊕ Fin q → 𝓞 E
  form : ∀ j a b, D.EF (f j a) (f j b) = (D₁ j.isLeft).EF (hh j • a) b
  span : ∃ n : ℕ, 0 < n ∧ ∀ a : D.La, ∃ x : ∀ j : Fin p ⊕ Fin q, (D₁ j.isLeft).La, n • a = ∑ j, f j (x j)

variable {K : Type} [Field K] [NumberField K]

def GenFib.key {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) (hg : 1 ≤ F.P₀.g) (rig : LB.Gen (F.P₀.L.pull (eSec F.P₀.A)))
    (hr : rig.IsGen) (th : F.P₀.L.Sec)
    (hth : ∀ s : Sp K, ∃ x : F.P₀.A.left, F.P₀.A.hom x = s ∧ x ∈ Out.nonzeroLocus th) : KeyIn K :=
  ⟨F.P₀, hg, rig, hr, th, hth, F.v, F.basis⟩

def IsThetaDeg (x : KeyIn K) (δ : ℝ) : Prop :=
  ∃ (oa : HeightOneSpectrum (𝓞 K) → ℤ) (nth : (K →+* ℂ) → ℝ),
    (∀ 𝔭, ∃ (a : K) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyPow.IsLocalModel x 𝔭 a M ∧
      𝔭.valuation K a = WithZero.exp (-oa 𝔭)) ∧
    (∀ σ : K →+* ℂ, ∃ (x' : KeyIn ℂ) (nη : ℝ), KeyPB x' x σ ∧ KeyPow.IsArchNorm x' (nth σ) nη) ∧
    (Function.support oa).Finite ∧
    δ = (∑ᶠ 𝔭, (oa 𝔭 : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) + (1 / 2) * ∑ σ, Real.log (nth σ)) / Module.finrank ℚ K

namespace CMLat

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} {hP : IsPeriod D ty Pe} {p q : ℕ}

theorem exists_smul_eq_smul {D₁ : Datum H} (h : Module.finrank (𝓞 E) D₁.La = 1) {a : D₁.La} (ha : a ≠ 0) (b : D₁.La) :
    ∃ r s : 𝓞 E, r ≠ 0 ∧ r • b = s • a := by
  have := D₁.fin
  have := D₁.proj
  have hn : ¬ LinearIndependent (𝓞 E) ![a, b] := fun hi => by
    have := hi.fintype_card_le_finrank
    simp [h] at this
  rw [LinearIndependent.pair_iff] at hn
  push Not at hn
  obtain ⟨s, r, e, hne⟩ := hn
  refine ⟨r, -s, fun hr => ?_, by rw [neg_smul]; exact eq_neg_of_add_eq_zero_right e⟩
  rw [hr, zero_smul, add_zero, smul_eq_zero] at e
  exact hne (e.resolve_right ha) hr

end CMLat

end GlobalTheory.CM
end
