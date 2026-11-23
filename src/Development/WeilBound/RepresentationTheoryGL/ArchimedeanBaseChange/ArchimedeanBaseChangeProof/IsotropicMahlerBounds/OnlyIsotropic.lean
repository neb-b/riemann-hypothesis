module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.VeryCuspZero

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open scoped Pointwise

namespace PositivityTheory.Rg.BcB

def logAbs {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (u : Ad E) : ℝ :=
  ∑ v, Real.log (‖cV v u‖ ^ 2) + ∑ᶠ w, Real.log ‖cW w u‖

def DegBasis : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n k : ℕ) (x : GA E n)
  (M : Matrix (Fin n) (Fin k) E), LinearIndependent E Mᵀ → degM x M = deg x (Submodule.span E (Set.range Mᵀ))

def DegSubmod : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (x : GA E n)
  (W W' : Submodule E (Fin n → E)), deg x W + deg x W' ≤ deg x (W ⊓ W') + deg x (W ⊔ W')

def DegMove : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ), ∃ C : ℝ, ∀ (x : GA E n)
  (g : GL (Fin n) E) (W : Submodule E (Fin n → E)),
    deg x W - C * (1 + logSize (x⁻¹ * ratGL E n g * x)) ≤ deg x (img g W)

def DegBdd : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ),
  (∀ x : GA E n, BddAbove (Set.range (deg x))) ∧ ∀ W : Submodule E (Fin n → E), Continuous fun x : GA E n => deg x W

def DegRat : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (x : GA E n)
  (g : GL (Fin n) E) (W : Submodule E (Fin n → E)), deg (ratGL E n g * x) (img g W) = deg x W

def DegAdelic : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n k : ℕ) (x t : GA E n) (s : GA E k)
  (M : Matrix (Fin n) (Fin k) E), LinearIndependent E Mᵀ →
    t.val * M.map (algebraMap E (Ad E)) = M.map (algebraMap E (Ad E)) * s.val →
    degM (t * x) M = degM x M + logAbs s.val.det

def DegPairing : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ C : ℝ, ∀ (x : GA E n)
  (d : GL (Fin n) E),
    (∀ W : Submodule E (Fin n → E), img (nrm d) W = W →
      deg x W ≤ deg x (W ⊓ perpD (conjE E) d W) + C * (1 + logSize (twConj (thetaA E n) x (ratGL E n d)))) ∧
    |deg x ⊤| ≤ C * (1 + logSize (twConj (thetaA E n) x (ratGL E n d)))

def Mahler : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (τ : ℝ),
  IsClosed (cutSet E n τ) ∧ (∀ g x, ratGL E n g * x ∈ cutSet E n τ ↔ x ∈ cutSet E n τ) ∧
    ∃ C : Set (GA E n), IsCompact C ∧ cutSet E n τ ⊆ ((ratGL E n).range : Set (GA E n)) * C

def SizeBasic : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
  (∀ C : Set (GA E n), IsCompact C → ∃ r, ∀ g ∈ C, logSize g ≤ r) ∧ (∀ g : GA E n, 0 ≤ logSize g) ∧
    (∀ g : GA E n, logSize (thetaA E n g) = logSize g) ∧
    ∃ c : ℝ, ∀ g h : GA E n, logSize (g * h) ≤ logSize g + logSize h + c

def OnlyStable : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ C : ℝ, ∀ (τ : ℝ) (x : GA E n)
  (d : GL (Fin n) E), C * (1 + logSize (twConj (thetaA E n) x (ratGL E n d))) ≤ τ →
    (x ∈ cutSet E n τ ↔ ∀ W : Submodule E (Fin n → E), img (nrm d) W = W → deg x W ≤ prof n τ (Module.finrank E W))

def OnlyIsotropic : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ C : ℝ, ∀ (τ : ℝ) (x : GA E n)
  (d : GL (Fin n) E), C * (1 + logSize (twConj (thetaA E n) x (ratGL E n d))) ≤ τ →
    (x ∈ cutSet E n τ ↔ ∀ W : Submodule E (Fin n → E), img (nrm d) W = W → W ≤ perpD (conjE E) d W →
      deg x W ≤ prof n τ (Module.finrank E W))

def sdot {m : ℕ} (e : Fin m → SignType) (a : Fin m → ℝ) : ℝ := ∑ i, (e i : ℝ) * a i

def SLe {m : ℕ} (e e' : Fin m → SignType) : Prop := ∀ i, e i ≠ 0 → e' i = e i

def sMeet {m : ℕ} (e e' : Fin m → SignType) : Fin m → SignType := fun i => if e i = e' i then e i else 0

def sJoin {m : ℕ} (e e' : Fin m → SignType) : Fin m → SignType :=
  fun i => if e i = 0 then e' i else if e' i = 0 ∨ e' i = e i then e i else 0

def PosFam {m : ℕ} (y : (Fin m → SignType) → ℝ) : Prop := y 0 = 0 ∧ ∀ e e', y (sMeet e e') + y (sJoin e e') ≤ y e + y e'


open Classical in
def gamOn {m : ℕ} (S : Finset (Fin m → SignType) → Prop) (y : (Fin m → SignType) → ℝ) (a : Fin m → ℝ) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Finset (Fin m → SignType))).filter
      (fun s : Finset (Fin m → SignType) => 0 ∉ s ∧ IsChain SLe (↑s : Set (Fin m → SignType)) ∧ S s),
    (-1 : ℝ) ^ s.card * ∏ e ∈ s, if y e < sdot e a then (1 : ℝ) else 0

def gam {m : ℕ} (y : (Fin m → SignType) → ℝ) (a : Fin m → ℝ) : ℝ := gamOn (fun _ => True) y a

def ChainSum : Prop := ∀ m : ℕ,
  (∀ (y : (Fin m → SignType) → ℝ) a, PosFam y → gam y a = Set.indicator {a | ∀ e, sdot e a ≤ y e} 1 a) ∧
  (∀ (y : (Fin m → SignType) → ℝ) (M : ℝ) a, (∀ e, |y e| ≤ M) → gam y a ≠ 0 → ∀ i, |a i| ≤ 2 * M) ∧
  (∀ y : (Fin m → SignType) → ℝ, Measurable (gam y)) ∧
  (∀ (y : (Fin m → SignType) → ℝ) a b, gam (fun e => y e + sdot e b) (a + b) = gam y a) ∧
  ∀ (y y' : (Fin m → SignType) → ℝ) e s t a, (∀ e', SLe e e' ∨ SLe e' e → y e' = y' e') →
    gam (Function.update y e s) a - gam (Function.update y e t) a =
      gam (Function.update y' e s) a - gam (Function.update y' e t) a

def LocVanish : Prop := ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
  (μ : Measure (GL (Fin n) ℂ)) [μ.IsHaarMeasure] (f u : GL (Fin n) ℂ → ℂ) (d : GL (Fin n) ℂ)
  (μd : Measure (twCent (thetaR (starRingEnd ℂ) n) d)) [μd.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ)),
    Continuous f → HasCompactSupport f → VeryCusp f → (d * thetaR (starRingEnd ℂ) n d).val.charpoly.Separable →
    W₁ ≠ ⊥ → W₁ ≤ W₂ → perpD (starRingEnd ℂ) d W₁ = W₂ → perpD (starRingEnd ℂ) d W₂ = W₁ → Measurable u →
    (∀ C, IsCompact C → ∃ B : ℝ, ∀ x ∈ C, ‖u x‖ ≤ B) →
    (∀ x k, thetaR (starRingEnd ℂ) n k = k → u (x * k) = u x) →
    (∀ t ∈ twCent (thetaR (starRingEnd ℂ) n) d, ∀ x, u (t * x) = u x) →
    (∀ m : GL (Fin n) ℂ, m.val - 1 ∈ nilrad W₁ W₂ → ∀ x, u (m * x) = u x) →
    quotIntegral μ (twCent (thetaR (starRingEnd ℂ) n) d) μd
      (fun x => f (twConj (thetaR (starRingEnd ℂ) n) x d) * u x) = 0

def cutTerm {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} [MeasurableSpace (GA E n)] (μ : Measure (GA E n))
    (τ : ℝ) (φ : GA E n → ℂ) (d : GL (Fin n) E) : ℂ :=
  quotIntegral μ (ratCent d) Measure.count fun x => chiT τ x * φ (twConj (thetaA E n) x (ratGL E n d))

def Unfold : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) [MeasurableSpace (GA E n)]
  [BorelSpace (GA E n)] (μ : Measure (GA E n)) [μ.IsHaarMeasure] (F : Set (GA E n)) (τ : ℝ) (φ : GA E n → ℂ),
    IsFundamentalDomain (ratGL E n).range F μ → IsTest φ →
    (Function.support fun c : TwClass E n => cutTerm μ τ φ (Quot.out c)).Finite ∧
      cutTr μ F τ φ = ∑ᶠ c : TwClass E n, cutTerm μ τ φ (Quot.out c)

def EllTerm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ C : ℝ, ∀ (τ : ℝ) (x : GA E n)
  (d : GL (Fin n) E), IsRegEll d → C * (1 + logSize (twConj (thetaA E n) x (ratGL E n d))) ≤ τ → x ∈ cutSet E n τ

def ClassVanish : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Nontrivial (InfinitePlace E)] (n : ℕ),
  ∃ C : ℝ, ∀ [MeasurableSpace (GA E n)] [BorelSpace (GA E n)] (μ : Measure (GA E n)) [μ.IsHaarMeasure] (τ r : ℝ)
    (φ : GA E n → ℂ) (d : GL (Fin n) E), IsTest φ → SizeLE φ r → (∀ v, VCAt v φ) → C * (1 + r) ≤ τ →
    IsRegD d → ¬ IsRegEll d → cutTerm μ τ φ d = 0

def orbTerm2 {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} [MeasurableSpace (GA E a)]
    [MeasurableSpace (GA E b)] (μ₁ : Measure (GA E a)) (μ₂ : Measure (GA E b)) (φ : GA E a × GA E b → ℂ)
    (d₁ : GL (Fin a) E) (d₂ : GL (Fin b) E) : ℂ :=
  quotIntegral (μ₁.prod μ₂) ((ratCent d₁).prod (ratCent d₂)) Measure.count fun x =>
    φ (twConj (thetaA E a) x.1 (ratGL E a d₁), twConj (thetaA E b) x.2 (ratGL E b d₂))

def ellSum2 {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} [MeasurableSpace (GA E a)]
    [MeasurableSpace (GA E b)] (μ₁ : Measure (GA E a)) (μ₂ : Measure (GA E b)) (φ : GA E a × GA E b → ℂ) : ℂ :=
  ∑ᶠ (c : TwClass E a × TwClass E b) (_ : IsRegEll (Quot.out c.1) ∧ IsRegEll (Quot.out c.2)),
    orbTerm2 μ₁ μ₂ φ (Quot.out c.1) (Quot.out c.2)

structure IsTest2 {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (φ : GA E a × GA E b → ℂ) (r : ℝ) :
    Prop where
  cont : Continuous φ
  supp : HasCompactSupport φ
  size : ∀ g, φ g ≠ 0 → logSize g.1 ≤ r ∧ logSize g.2 ≤ r
  test₁ : ∀ g₂, IsTest (fun g => φ (g, g₂)) ∧ RegSupp (fun g => φ (g, g₂)) ∧ ∀ v, VCAt v fun g => φ (g, g₂)
  test₂ : ∀ g₁, IsTest (fun g => φ (g₁, g)) ∧ RegSupp (fun g => φ (g₁, g)) ∧ ∀ v, VCAt v fun g => φ (g₁, g)

end PositivityTheory.Rg.BcB

end
