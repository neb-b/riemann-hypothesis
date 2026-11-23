module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
section
noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def wSub (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ) : Submodule D.O D.La :=
  Submodule.span D.O {z | ∃ c ∈ w0 ^ r, ∃ z' : D.La, z = algebraMap (𝓞 D.F) D.O c • z'}

abbrev LevGrp (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ) : Type :=
  (D.La ⧸ wSub D w0 r) ≃ₗ[D.O] (D.La ⧸ wSub D w0 r)

def IsEtPlace (b : Base D R) (w0 : Ideal (𝓞 D.F)) : Prop :=
  w0.IsMaximal ∧ (p : 𝓞 D.F) ∈ w0 ∧ (∀ i, Ideal.span ((b.t i) '' (w0 : Set (𝓞 D.F))) = ⊤) ∧
    ∀ (k : Type) [Field k] [CharP k p] (β : R →+* k) (φ : 𝓞 D.F →+* k), RingHom.ker φ = w0 → φ D.ω = β b.ρ

def IsEtLev {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ)
    (lv : D.La → (𝟙_ (Over S) ⟶ o.A)) : Prop :=
  (∀ x y, lv (x + y) = lv x * lv y) ∧ (∀ (c : D.O) x, lv (c • x) = lv x ≫ o.act.act c) ∧
    (∀ x ∈ wSub D w0 r, lv x = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      (∀ y, toUnit (Over.mk x) ≫ lv y = 1 → y ∈ wSub D w0 r) ∧
      ∀ g : Over.mk x ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
        ∃ y, toUnit (Over.mk x) ≫ lv y = g

structure EtModel (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ) where
  X : Scheme.{0}
  s : X ⟶ Sp R
  univ : Obj b N s
  lv : D.La → (𝟙_ (Over X) ⟶ univ.A)
  isLev : IsEtLev univ w0 r lv
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp R) (o : Obj b N s') (l : D.La → (𝟙_ (Over S) ⟶ o.A)),
    IsEtLev o w0 r l → ∃! f : S ⟶ X, f ≫ s = s' ∧ ∃ m : ObjMap o univ f, ∀ y, (l y).left ≫ m.φ = f ≫ (lv y).left

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsPull
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory.Katz

namespace GlobalTheory.KatzF

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ} {σ : Type}


variable (k) in
def sig : Fr p k →+* Fr p k := (WittVector.FractionRing.frobenius p k : Fr p k →+* Fr p k)

def powX (R : Type) [CommRing R] (σ : Type) (n : ℕ) : σ → MvPowerSeries σ R := fun i => X i ^ n

def frobS (f : MvPowerSeries (Fin d) (Fr p k)) : MvPowerSeries (Fin d) (Fr p k) :=
  subst (powX (Fr p k) (Fin d) p) (MvPowerSeries.map (sig p k) f)

def IsF {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) (F : Mod p h → Mod p h) : Prop :=
  ∀ f : quasiLog p h, ∃ g : quasiLog p h, g.1 = frobS p f.1 ∧
    F (Submodule.Quotient.mk f) = Submodule.Quotient.mk g

def IsPull {e : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} {ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k}
    (hμ : IsLaw μ) (hν : IsLaw ν) (φ : Fin e → MvPowerSeries (Fin d) k) (m : Mod p hν → Mod p hμ) : Prop :=
  ∀ f : quasiLog p hν, ∃ g : quasiLog p hμ, g.1 = subst (fun j => Katz.lift p (φ j)) f.1 ∧
    m (Submodule.Quotient.mk f) = Submodule.Quotient.mk g

end GlobalTheory.KatzF
end
end

