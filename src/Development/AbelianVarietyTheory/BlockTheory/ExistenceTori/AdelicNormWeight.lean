module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain
open scoped TensorProduct

section Adelic

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

abbrev Plc : Type := HeightOneSpectrum (𝓞 (maximalRealSubfield E))

abbrev AdF : Type := FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)

def AdE : Type := AdF E ⊗[maximalRealSubfield E] E

instance : CommRing (AdE E) := inferInstanceAs (CommRing (AdF E ⊗[maximalRealSubfield E] E))

def adConj : (AdF E ⊗[maximalRealSubfield E] E) →ₐ[maximalRealSubfield E] (AdF E ⊗[maximalRealSubfield E] E) :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (IsCMField.complexConj E).toAlgHom

theorem adConj_adConj (x : AdF E ⊗[maximalRealSubfield E] E) : adConj E (adConj E x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [adConj]
  | add x y hx hy => simp [hx, hy]

instance : StarRing (AdE E) where
  star x := adConj E x
  star_involutive x := adConj_adConj E x
  star_mul x y := by
    show adConj E (x * y) = adConj E y * adConj E x
    rw [mul_comm (adConj E y)]
    exact map_mul (adConj E) x y
  star_add x y := map_add (adConj E) x y

def diagE : E →+* AdE E :=
  (Algebra.TensorProduct.includeRight (R := maximalRealSubfield E) (A := AdF E) (B := E)).toRingHom

def inclF : AdF E →+* AdE E :=
  Algebra.TensorProduct.includeLeftRingHom (R := maximalRealSubfield E) (A := AdF E) (B := E)


variable {E} in
def compF (v : Plc E) : AdF E →ₐ[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E) where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl


variable {E} in
def compE (v : Plc E) : AdE E →+* (v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) :=
  (Algebra.TensorProduct.map (compF v) (AlgHom.id (maximalRealSubfield E) E)).toRingHom

def intAd : Subring (AdE E) :=
  Subring.closure ((inclF E '' {a | ∀ v : Plc E, a v ∈ v.adicCompletionIntegers (maximalRealSubfield E)}) ∪
    Set.range fun o : 𝓞 E => diagE E (o : E))

abbrev UA (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) (AdE E)

variable {E} {n : ℕ}

def ptsIn (n : ℕ) (R : Subring (AdE E)) : Subgroup (UA E n) where
  carrier := {k | (∀ a b, k.1 a b ∈ R) ∧ ∀ a b, (k⁻¹).1 a b ∈ R}
  one_mem' := by
    have : ∀ a b : Fin n, (1 : UA E n).1 a b ∈ R := fun a b => by
      show (1 : Matrix (Fin n) (Fin n) (AdE E)) a b ∈ R
      rw [Matrix.one_apply]
      split_ifs
      exacts [R.one_mem, R.zero_mem]
    exact ⟨this, by rw [inv_one]; exact this⟩
  mul_mem' := by
    have key : ∀ x y : UA E n, (∀ a b, x.1 a b ∈ R) → (∀ a b, y.1 a b ∈ R) → ∀ a b, (x * y).1 a b ∈ R :=
      fun x y hx hy a b => by
        show (x.1 * y.1) a b ∈ R
        rw [Matrix.mul_apply]
        exact R.sum_mem fun j _ => R.mul_mem (hx a j) (hy j b)
    intro x y hx hy
    exact ⟨key x y hx.1 hy.1, by rw [mul_inv_rev]; exact key _ _ hy.2 hx.2⟩
  inv_mem' := fun {x} hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩


variable (E) in
def ratPts (n : ℕ) : Subgroup (UA E n) := ptsIn n (diagE E).range


variable (E) in
def maxCpt (n : ℕ) : Subgroup (UA E n) := ptsIn n (intAd E)

def IsLevelGrp (J : Subgroup (UA E n)) : Prop :=
  J ≤ maxCpt E n ∧
  (∃ m : ℕ, m ≠ 0 ∧ ∀ k ∈ maxCpt E n,
    (∀ a b, ∃ u ∈ intAd E, (k.1 - 1) a b = (m : AdE E) * u) → k ∈ J) ∧
  ∀ k : UA E n, (∀ v : Plc E, ∃ j ∈ J, ∀ a b, compE v (k.1 a b) = compE v (j.1 a b)) → k ∈ J

def TrivOn (S : Finset (Plc E)) (h : UA E n) : Prop :=
  ∀ v ∈ S, ∀ a b, compE v (h.1 a b) = compE v ((1 : Matrix (Fin n) (Fin n) (AdE E)) a b)

def stab (J : Subgroup (UA E n)) (h : UA E n) : Subgroup (UA E n) :=
  ratPts E n ⊓ J.comap (MulAut.conj h⁻¹).toMonoidHom


end Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

abbrev ConjQ (Dw : Datum H) (l : Level H) : Type := Dw.La ⧸ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)

def fourierSum {n : ℕ} (ph : (Fin n → ConjQ Dw l) → c.F) : (Fin n → LevQ Dw l) → c.F :=
  fun q => ∑ᶠ x : Fin n → ConjQ Dw l, ph x * zetaM c ^ (-pairL (l := l) (fun b => qRep (x b)) (fun b => levRep (q b)))

def FixesDatum {n : ℕ} (J : Subgroup (UA E n)) (ph : (Fin n → ConjQ Dw l) → c.F) : Prop :=
  ∀ k ∈ J, ∀ κ : Fin n → Fin n → 𝓞 E,
    (∀ a b, ∃ u ∈ intAd E, star (k.1 a b) - diagE E (κ a b : E) = (l.M : AdE E) * u) →
      ∀ x, ph (fun a => ∑ b, κ a b • x b) = ph x




end GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
