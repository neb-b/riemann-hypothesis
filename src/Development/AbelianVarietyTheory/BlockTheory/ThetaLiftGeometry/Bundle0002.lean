module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.FourierColumnIndicator
section
open NumberField IsDedekindDomain MeasureTheory
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator

def Zmu (K : Type) [Field K] (g : ℕ) : Subalgebra ℤ K := Algebra.adjoin ℤ {ζ : K | ζ ^ (g * (g - 1)) = 1}

section Notions

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

def FnModAt (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b))
    (Φ : HomE E a b → K) : Prop :=
  (∀ x, Φ x ≠ 0 → x ∈ homAt {P} N N') ∧
  (∀ x z, z ∈ homAt {P} N N' → Φ (x + (qOf P : E) • z) = Φ x) ∧
  ∀ x, Φ x ∈ Zmu K (qOf P)

abbrev FnMod (P : HeightOneSpectrum (𝓞 E)) {a b : ℕ} (Φ : HomE E a b → K) : Prop :=
  FnModAt P (stdLat E a) (stdLat E b) Φ

def ColFn (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (f : Sp E n → K) : Prop :=
  (∀ y, f y ≠ 0 → (qOf P : E) • y ∈ stdAt E n P) ∧
  (∀ y z, z ∈ stdAt E n P → f (y + z) = f y) ∧
  ∀ y, f y ∈ Zmu K (qOf P)

def InDual (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (ξ : Sp E n →ₗ[E] E) : Prop := ∀ y ∈ stdAt E n P, IntAt P (ξ y)

def DualFn (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (F : (Sp E n →ₗ[E] E) → K) : Prop :=
  (∀ ξ, F ξ ≠ 0 → InDual P ξ) ∧
  (∀ ξ ξ', InDual P ξ' → F (ξ + (qOf P : E) • ξ') = F ξ) ∧
  ∀ ξ, F ξ ∈ Zmu K (qOf P)


open Classical in
theorem colFn_indicator (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (y₀ : Sp E n) (h₀ : (qOf P : E) • y₀ ∈ stdAt E n P) :
    ColFn P (fun y => if y - y₀ ∈ stdAt E n P then (1 : K) else 0) := by
  refine ⟨fun y hy => ?_, fun y z hz => ?_, fun y => ?_⟩
  · have h : y - y₀ ∈ stdAt E n P := by
      by_contra h
      exact hy (if_neg h)
    have h1 : (qOf P : E) • (y - y₀) ∈ stdAt E n P := by
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem h _
    have h2 := add_mem h1 h₀
    rwa [← smul_add, sub_add_cancel] at h2
  · have h1 : y + z - y₀ = (y - y₀) + z := by abel
    simp only [h1, Submodule.add_mem_iff_left _ hz]
  · dsimp only
    split_ifs
    · exact one_mem _
    · exact zero_mem _

end Notions

section Padic

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

end Padic

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def restrX {E : Type} [Field E] {n' c' n c : ℕ} (x : HomE E (n' + c') (n + c)) : HomE E n' n :=
  LinearMap.funLeft E E (Fin.castAdd c) ∘ₗ x ∘ₗ Loc.inX E n' c'

def colX {E : Type} [Field E] {n' c' n c : ℕ} (x : HomE E (n' + c') (n + c)) : Sp E n :=
  LinearMap.funLeft E E (Fin.castAdd c) (x (Loc.eN E (n' + c') n'))

def fhat {n : ℕ} (P : rowSG Pr sel mu) (f : Sp X.E n → X.K) (η : Sp X.E n →ₗ[X.E] X.E) : X.K :=
  ∑ y ∈ Fintype.piFinset fun _ : Fin n => LocE.valsQ X.E (qOf P.1) 1 0, f y * ftY sel mu cst P η y

def topDatum (m2 : ℕ) (P : rowSG Pr sel mu) (f : Sp X.E (R.N (m2 + 1)) → X.K) (x : HomE X.E (R.N (m2 + 1)) (R.N R.m)) : X.K :=
  PhiTop Ch mu cst.sharp m2 P.1 (prXp X.E R ∘ₗ x ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
    fhat sel mu cst P f (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ x)

def facPen {u : Pr.Word} (m2 : ℕ) (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1))
    (Y : Set (Sp X.E (R.N (m2 + 1)))) (P : rowSG Pr sel mu) (x : HomE X.E (R.N m2) (R.N (m2 + 1))) : X.K :=
  PsiAt Ch sel mu cst m2 P (L.h m2 al P) (inFr (frsF sel mu p₀ P) (frsF sel mu p P) x) ((frsF sel mu p P).symm (repY Y))

def facTop {u : Pr.Word} (m2 : ℕ) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (d : RowPt Pr R sel mu)
    (P : rowSG Pr sel mu) (x : HomE X.E (R.N (m2 + 1)) (R.N R.m)) : X.K :=
  PhiTop Ch mu cst.sharp m2 P.1 ((d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap ∘ₗ
      LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
    ftY sel mu cst P ((((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ • atNL X.E (R.N R.m) (R.N R.m - 1)) ∘ₗ x ∘ₗ (frsF sel mu p P).toLinearMap)
      ((frsF sel mu p P).symm (repY Y))

def SplitAt (m2 : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R m2) : Prop :=
  (∀ x, omPhi Ch sel mu cst m2 P hal 1 x = PsiAt Ch sel mu cst m2 P hal (restrX x) (colX x)) ∧
  ∃ (ι : Type) (_ : Fintype ι) (Ψ : ι → HomE X.E (R.N m2) (R.N (m2 + 1)) → X.K) (f : ι → Sp X.E (R.N (m2 + 1)) → X.K),
    (∀ a, FnMod P.1 (Ψ a)) ∧ (∀ a, ColFn P.1 (f a)) ∧
    ∀ x₀ y, PsiAt Ch sel mu cst m2 P hal x₀ y = ∑ a, Ψ a x₀ * f a y

end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.LatticeFramesPrimeToLevel
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Neutral.B1
open scoped Matrix

section Adelic

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

abbrev Ad : Type := FiniteAdeleRing (𝓞 H.E) H.E

end Adelic

section abelian₂

variable {l : ℕ} [Fact l.Prime] (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[l])

end abelian₂

abbrev Reps (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) : Type :=
  ∀ i, (D.chTw u μ).cls i → GL (Fin (D.R.N i)) (Ad D.host)

abbrev Frames (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) : Type :=
  ∀ i, (D.chTw u μ).Y i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts
end
end

