module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GlobalTheory
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.RunFinOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PeakTraceBound

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelRep
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

abbrev LF (a b : ℕ) (w : Pl E) : Type := GLw a w × GLw b w → ℂ

def lfStar {w : Pl E} (f : LF a b w) : LF a b w := fun y => starRingEnd ℂ (f y⁻¹)

structure LM (κ : Pl E → Type) (a b : ℕ) where
  m : ∀ w, κ w → κ w → LF a b w
  s : ∀ w : Pl E, LF a b w
  t : ∀ w : Pl E, LF a b w

namespace LM

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)] (P : Finset (Pl E))

def ent (L : LM κ a b) (x y : ∀ w : P, κ w) (w : Pl E) : LF a b w := if h : w ∈ P then L.m w (x ⟨w, h⟩) (y ⟨w, h⟩) else L.s w

def Ok (L : LM κ a b) : Prop := (∀ x y, IsTestP (L.ent P x y)) ∧ IsTestP L.t

def mul (L L' : LM κ a b) : LM κ a b :=
  ⟨fun w x y => ∑ z, mconv (L.m w x z) (L'.m w z y), fun w => mconv (L.s w) (L'.s w), fun w => mconv (L.t w) (L'.t w)⟩

def adj (L : LM κ a b) : LM κ a b := ⟨fun w x y => lfStar (L.m w y x), fun w => lfStar (L.s w), fun w => lfStar (L.t w)⟩

def tr (L : LM κ a b) (N : ∀ w, κ w → κ w → ℂ) (w : Pl E) : LF a b w :=
  if w ∈ P then ∑ x, ∑ y, N w y x • L.m w x y else L.s w

end LM

def Block.vol (B : Block E) : ℂ := (B.ν.real ((Kf E B.a).prod (Kf E B.b) : Subgroup (Hf E B.a B.b)) : ℝ)

section

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)] (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w)

def fm (L : LM κ B.a B.b) : Matrix B.κ B.κ (Hf E B.a B.b → ℂ) := fun x y h => B.vol⁻¹ * finFn S (L.ent P (e x) (e y)) L.t h

def tenN (N : ∀ w, κ w → κ w → ℂ) : Matrix B.κ B.κ ℂ := fun x y => ∏ w : P, N w (e x w) (e y w)

end

def rt {κ : Type} (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E) (ψ : Matrix κ κ (Hf E a b → ℂ)) : Matrix κ κ (Hf E a b → ℂ) :=
  fun x y h => ψ x y (h * (ratF E a u₁, ratF E b u₂)⁻¹)

def PT.arch {B : Block E} (t : PT B) (Ta : Ops B.Ma) (Tb : Ops B.Mb) (v : InfinitePlace E) (y : G B.a × G B.b) : ℂ :=
  phiOf (B.Ma v) (Ta v) (t.ka v) y.1 * phiOf (B.Mb v) (Tb v) (t.kb v) y.2

def IntHint : Prop := ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  (ν : Measure Γ) [ν.IsHaarMeasure] (K U : Subgroup Γ) (f : Γ → ℂ), IsOpen (K : Set Γ) → IsCompact (K : Set Γ) →
  IsOpen (U : Set Γ) → HasCompactSupport f → (∀ u ∈ U, ∀ x, f (x * u) = f x) → ν.IsMulRightInvariant →
  ∫ x, f x ∂ν = (ν.real K : ℂ) * hint K f

def HintProd : Prop := ∀ (ι Γ : Type) [Group Γ] (Hl : ι → Type) [∀ i, Group (Hl i)] [∀ i, TopologicalSpace (Hl i)]
  [∀ i, IsTopologicalGroup (Hl i)] (p : ∀ i, Γ →* Hl i) (K : Subgroup Γ) (KH U : ∀ i, Subgroup (Hl i)) (f : ∀ i, Hl i → ℂ),
  (∀ x y : Γ, (∀ i, p i x = p i y) → x = y) → (∀ y : ∀ i, Hl i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : Γ, ∀ i, p i x = y i) →
  (∀ x : Γ, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : Γ, x ∈ K ↔ ∀ i, p i x ∈ KH i) →
  (∀ i, IsCompact (KH i : Set (Hl i)) ∧ IsOpen (KH i : Set (Hl i)) ∧ IsOpen (U i : Set (Hl i)) ∧ HasCompactSupport (f i) ∧
    ∀ u ∈ U i, ∀ x, f i (x * u) = f i x) →
  (∀ᶠ i in cofinite, f i = (KH i : Set (Hl i)).indicator 1) →
  hint K (fun x => ∏ᶠ i, f i (p i x)) = ∏ᶠ i, hint (KH i) (f i)

abbrev Slot (S : Set (Pl E)) : Type := {w // w ∈ S} ⊕ {w // w ∈ S ∧ IsSplitAt w}

def Slot.pl {S : Set (Pl E)} : Slot S → Pl E := Sum.elim Subtype.val Subtype.val

def Slot.cp {S : Set (Pl E)} (a b : ℕ) : ∀ i : Slot S, Gf E a b → GLw a i.pl × GLw b i.pl
  | .inl w => atW w.1
  | .inr w => fun y => atW w.1 (thP E a b y)

def Slots : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (S : Set (Pl E)), IsSection S →
  (∀ (i : Slot S) x y, i.cp a b (x * y) = i.cp a b x * i.cp a b y) ∧ (∀ i : Slot S, Continuous (i.cp a b)) ∧
  (∀ x y : Gf E a b, (∀ i : Slot S, i.cp a b x = i.cp a b y) → x = y) ∧
  (∀ y : ∀ i : Slot S, GLw a i.pl × GLw b i.pl, (∀ᶠ i in cofinite, y i ∈ K2 a b i.pl) → ∃ x, ∀ i : Slot S, i.cp a b x = y i) ∧
  (∀ x, ∀ᶠ i : Slot S in cofinite, i.cp a b x ∈ K2 a b i.pl) ∧
  (∀ x, x ∈ (Kf E a).prod (Kf E b) ↔ ∀ i : Slot S, i.cp a b x ∈ K2 a b i.pl) ∧
  ∀ C : ∀ i : Slot S, Set (GLw a i.pl × GLw b i.pl), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = K2 a b i.pl) →
    IsCompact {x : Gf E a b | ∀ i : Slot S, i.cp a b x ∈ C i}

def FinConv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (S : Set (Pl E)), IsSection S →
  B.vol ≠ 0 ∧ ∀ φ₁ φ₂ : ∀ w : Pl E, LF B.a B.b w, IsTestP φ₁ → IsTestP φ₂ →
    HasCompactSupport (finFn S φ₁ φ₂) ∧
    (∃ U : Subgroup (Hf E B.a B.b), IsOpen (U : Set (Hf E B.a B.b)) ∧
      ∀ u ∈ U, ∀ h, finFn S φ₁ φ₂ (u * h) = finFn S φ₁ φ₂ h ∧ finFn S φ₁ φ₂ (h * u) = finFn S φ₁ φ₂ h) ∧
    ∀ φ₁' φ₂' : ∀ w : Pl E, LF B.a B.b w, IsTestP φ₁' → IsTestP φ₂' →
      IsTestP (fun w => mconv (φ₁ w) (φ₁' w)) ∧ IsTestP (fun w => mconv (φ₂ w) (φ₂' w)) ∧
      ∀ g, ∫ h, finFn S φ₁ φ₂ h * finFn S φ₁' φ₂' (h⁻¹ * g) ∂B.ν =
        B.vol * finFn S (fun w => mconv (φ₁ w) (φ₁' w)) (fun w => mconv (φ₂ w) (φ₂' w)) g

def FmAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E))
  (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), IsSection S → (↑P : Set (Pl E)) ⊆ S →
  ∀ L L' : LM κ B.a B.b, L.Ok P → L'.Ok P →
    IsFinM (fm S P B e L) ∧ (L.mul L').Ok P ∧ mulF B.ν (fm S P B e L) (fm S P B e L') = fm S P B e (L.mul L') ∧
      L.adj.Ok P ∧ adjF (fm S P B e L) = fm S P B e L.adj

def FmTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E))
  (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), (↑P : Set (Pl E)) ⊆ S → (∀ w ∈ P, Nonempty (κ w)) →
  ∀ (L : LM κ B.a B.b) (N : ∀ w, κ w → κ w → ℂ), L.Ok P → IsTestP (L.tr P N) ∧
    ∀ h, ∑ x, ∑ y, fm S P B e L x y h * tenN P B e N y x = B.vol⁻¹ * finFn S (L.tr P N) L.t h

def RtAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (u₁ : GL (Fin B.a) E) (u₂ : GL (Fin B.b) E),
  (∀ ψ ψ' : Matrix B.κ B.κ (Hf E B.a B.b → ℂ), mulF B.ν ψ (rt u₁ u₂ ψ') = rt u₁ u₂ (mulF B.ν ψ ψ')) ∧
  (∀ t : PT B, t.Ok → ∃ r, PT.Ok { t with ψ := rt u₁ u₂ t.ψ, r := r }) ∧
  ∀ ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ), IsFinM ψ → ∃ r, 0 ≤ r ∧
    ∀ x y h, ψ x y h ≠ 0 → logSize (finGL E B.a h.1) ≤ r ∧ logSize (finGL E B.b h.2) ≤ r

def lmWd {κ : Pl E → Type} [∀ w, Fintype (κ w)] {B : Block E} (Lo : PT B → LM κ B.a B.b) (w : List (BGen B))
    (L₀ : LM κ B.a B.b) : LM κ B.a B.b := w.foldr (fun g L => Sum.elim (fun _ => L) (fun s => (Lo s).mul L) g) L₀

def AdelRep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E))
  (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w), IsSection S → (↑P : Set (Pl E)) ⊆ S → (∀ w ∈ P, Nonempty (κ w)) →
  ∀ (u₁ : GL (Fin B.a) E) (u₂ : GL (Fin B.b) E) (Ta : Ops B.Ma) (Tb : Ops B.Mb) (N : ∀ w, κ w → κ w → ℂ)
    (Lo : PT B → LM κ B.a B.b) (w : List (BGen B)) (t₀ : PT B) (L₀ : LM κ B.a B.b),
    (∀ s, Sum.inr s ∈ w → (Lo s).Ok P ∧ s.ψ = fm S P B e (Lo s)) → L₀.Ok P → t₀.ψ = rt u₁ u₂ (fm S P B e L₀) →
    (lmWd Lo w L₀).Ok P ∧ (BGen.wd w t₀).ψ = rt u₁ u₂ (fm S P B e (lmWd Lo w L₀)) ∧
      trM (BGen.wd w t₀).Φ (opM Ta Tb (tenN P B e N)) =
        B.vol⁻¹ • adel S u₁ u₂ ((BGen.wd w t₀).arch Ta Tb) ((lmWd Lo w L₀).tr P N) (lmWd Lo w L₀).t

def VCAll (B : Block E) (Ta : Ops B.Ma) (Tb : Ops B.Mb) : Prop :=
  (∀ v k val T, IsMult B.μa (B.Ma v) k val T → VeryCusp (phiOf (B.Ma v) (Ta v) k)) ∧
    ∀ v k val T, IsMult B.μb (B.Mb v) k val T → VeryCusp (phiOf (B.Mb v) (Tb v) k)

def RegOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (S : Set (Pl E)) (u₁ : GL (Fin a) E)
  (u₂ : GL (Fin b) E), IsTransl u₁ → IsTransl u₂ → ∀ φ₁ φ₂ : ∀ w : Pl E, LF a b w, IsTestP φ₁ → IsTestP φ₂ →
  (∃ w ∈ S, ¬ IsSplitAt w ∧ RegAt2 a b w (φ₁ w)) →
  (∀ d x h₂, finFn S φ₁ φ₂ ((gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E a) x (ratGL E a d)), h₂) * (ratF E a u₁, ratF E b u₂)⁻¹) ≠ 0 →
    IsRegD d) ∧
  ∀ d x h₁, finFn S φ₁ φ₂ ((h₁, gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E b) x (ratGL E b d))) * (ratF E a u₁, ratF E b u₂)⁻¹) ≠ 0 →
    IsRegD d

def PTTest : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E), ∃ c : ℝ, 0 ≤ c ∧
  ∀ (κ : Pl E → Type) [∀ w, Fintype (κ w)] (S : Set (Pl E)) (P : Finset (Pl E)) (e : B.κ ≃ ∀ w : P, κ w), IsSection S →
  (↑P : Set (Pl E)) ⊆ S → (∀ w ∈ P, Nonempty (κ w)) → ∀ (u₁ : GL (Fin B.a) E) (u₂ : GL (Fin B.b) E), IsTransl u₁ → IsTransl u₂ →
  ∀ (Ta : Ops B.Ma) (Tb : Ops B.Mb) (N : ∀ w, κ w → κ w → ℂ) (t : PT B) (L : LM κ B.a B.b), VCAll B Ta Tb → t.Ok → L.Ok P →
    t.ψ = rt u₁ u₂ (fm S P B e L) → (∃ w ∈ S, ¬ IsSplitAt w ∧ RegAt2 B.a B.b w (L.tr P N w)) →
    D4.IsTest2J (trM t.Φ (opM Ta Tb (tenN P B e N))) (c * (1 + t.T) + t.r)

def EllLin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Nontrivial (InfinitePlace E)] (a b : ℕ)
  [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] [MeasurableSpace (GA E b)] [BorelSpace (GA E b)]
  (μ₁ : Measure (GA E a)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E b)) [μ₂.IsHaarMeasure] (J : Type) (s : Finset J) (c : J → ℂ)
  (φ : J → GA E a × GA E b → ℂ) (r : ℝ), 0 ≤ r → (∀ j ∈ s, D4.IsTest2J (φ j) r) →
    ellSum2 μ₁ μ₂ (∑ j ∈ s, c j • φ j) = ∑ j ∈ s, c j * ellSum2 μ₁ μ₂ (φ j)

def GrowthAt (B : Block E) [MeasurableSpace (GA E B.a)] [MeasurableSpace (GA E B.b)] (μ₁ : Measure (GA E B.a))
    (μ₂ : Measure (GA E B.b)) : Prop :=
  ∀ (Φ₁ Φ₂ : Matrix B.I B.I (H E B.a B.b → ℂ)) (T₁ T₂ : B.Hb →L[ℂ] B.Hb) (M : Matrix B.I B.I ℂ) (r₀ r₁ : ℝ), IsTestM Φ₁ →
    IsTestM Φ₂ → IsROp B.D Φ₁ T₁ → IsROp B.D Φ₂ T₂ → 0 ≤ r₀ → 0 ≤ r₁ → ∃ (C : ℝ) (N : ℕ), ∀ (k : ℕ) (U : B.Hb →L[ℂ] B.Hb)
      (Φ : Matrix B.I B.I (H E B.a B.b → ℂ)), IsTestM Φ → IsROp B.D Φ (T₁ * U * T₂) →
      D4.IsTest2J (trM Φ M) (r₀ + k * r₁) → ‖ellSum2 μ₁ μ₂ (trM Φ M)‖ ≤ C * (1 + k) ^ N * ‖U‖

def BlockEllipticGrowth : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Nontrivial (InfinitePlace E)] (B : Block E)
  [MeasurableSpace (GA E B.a)] [BorelSpace (GA E B.a)] [MeasurableSpace (GA E B.b)] [BorelSpace (GA E B.b)]
  (μ₁ : Measure (GA E B.a)) [μ₁.IsHaarMeasure] (μ₂ : Measure (GA E B.b)) [μ₂.IsHaarMeasure], GrowthAt B μ₁ μ₂ →
  ∀ (M : Matrix B.I B.I ℂ) (t₁ t₂ : PT B) (J : Type) [Fintype J] (c : J → ℂ) (w : J → List (BGen B)) (c₀ : ℝ), 0 ≤ c₀ →
    t₁.Ok → t₂.Ok → (∀ j, ∀ g ∈ w j, g.Ok) →
    ∃ (C : ℝ) (N : ℕ), ∀ k : ℕ,
      (∀ f : Fin k → J, ∀ t, t = BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂ →
        D4.IsTest2J (trM t.Φ M) (c₀ * (1 + t.T) + t.r)) →
      ‖∑ f : Fin k → J, (∏ i, c (f i)) * BGen.sc (List.ofFn fun i => w (f i)).flatten *
          ellSum2 μ₁ μ₂ (trM (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).Φ M)‖ ≤
        C * (1 + k) ^ N * ‖(∑ j, c j • ((w j).map BGen.op).prod) ^ k‖

end PositivityTheory.Rg.BcB.F

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdjKer0
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG
open PositivityTheory.RgTw (Mat G)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

def OpNeOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E), 1 ≤ B.a + B.b → Nontrivial B.Hb →
  ∀ t : PT B, t.Ok → t.op ≠ 1

def AdjKer0 : Prop := ∀ (n : ℕ) (μ : Measure (G n)), μ.IsHaarMeasure → ∀ (M : KMod n) (g : ℝ → ℝ) (T : ℝ)
  (k : Mat n → (M.V →L[ℂ] M.V)), IsBump g T → IsKer μ M [] g k →
    IsKer μ M [] g (haveI := FiniteDimensional.complete ℂ M.V; fun y => ContinuousLinearMap.adjoint (k y⁻¹))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E}

def PT.pw (t : PT B) (m : ℕ) : PT B := BGen.wd (List.replicate m (Sum.inr t)) t

def PT.adj' (t : PT B) : PT B := { t.adj with va := t.va, vb := t.vb }

def PT.sq (t : PT B) (m : ℕ) : PT B := (t.adj'.pw m).mul (t.pw m)

def SqOk : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (t : PT B) (g : ℝ → ℝ) (m : ℕ), t.Ok →
  IsBump g t.T → (∀ v, IsKer B.μa (B.Ma v) [] g (t.ka v) ∧ ∀ χ, t.va v χ = coshT g (cas χ)) →
  (∀ v, IsKer B.μb (B.Mb v) [] g (t.kb v) ∧ ∀ χ, t.vb v χ = coshT g (cas χ)) →
  (t.pw m).Ok ∧ (t.pw m).op = t.op ^ (m + 1) ∧ (t.sq m).Ok ∧ (t.sq m).op = star (t.op ^ (m + 1)) * t.op ^ (m + 1) ∧
    (∀ χa χb, (t.sq m).val χa χb = t.val χa χb ^ (2 * (m + 1))) ∧
    (t.sq m).ψ = mulF B.ν (t.adj'.pw m).ψ (t.pw m).ψ

end PositivityTheory.Rg.BcB.F

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

abbrev lp (P : Pre E n) (w : Pl E) := locProd P.h w (P.σ · w)

def SmVec {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V) : Prop :=
  ∃ U : Subgroup G, IsOpen (U : Set G) ∧ x ∈ fixed ρ U

def Sep {G V X : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G V) (S : Submodule ℂ V) (τ : Representation ℂ G X) : Prop :=
  (∀ g, ∀ x ∈ S, ρ g x ∈ S) ∧ ∃ (J : Type) (L : J → V →ₗ[ℂ] X),
    (∀ j g, ∀ x ∈ S, SmVec ρ x → L j (ρ g x) = τ g (L j x)) ∧ ∀ x ∈ S, SmVec ρ x → (∀ j, L j x = 0) → x = 0

def LeafMod : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)) (w : Pl E)
  (σ : SmIrr (GLw N w)), IsDiscrete V → IsLocCompGL V w σ → Sep ((finRep E N).comp (locGL E N w)) V σ.ρ

def NodeMod : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ) (t₁ : Tr E r) (t₂ : Tr E s) (w : Pl E)
  (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ₁ : Representation ℂ (GLw r w) X)
  (τ₂ : Representation ℂ (GLw s w) Y), Sep ((finRep E r).comp (locGL E r w)) t₁.space τ₁ →
  Sep ((finRep E s).comp (locGL E s w)) t₂.space τ₂ →
  Sep ((finRep E (r + s)).comp (locGL E (r + s) w)) (Tr.node t₁ t₂).space
    (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.extTensor τ₁ τ₂))

def JoinMod : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (χ₁ χ₂ : HChar E)
  (Pa : Pre E a) (Pb : Pre E b) (D : Pre E n) (w : Pl E), IsJoin χ₁ χ₂ Pa Pb D →
  Nonempty ((lp D w).Equiv (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h)
    (GlobalTheory.SmGL.extTensor (twRep (lp Pa w) ((χ₁.loc w).comp GeneralLinearGroup.det))
      (twRep (lp Pb w) ((χ₂.loc w).comp GeneralLinearGroup.det)))))

def TreeMod : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (P : Pre E N) (w : Pl E),
  t.Good → t.Untw → TreeParts t P → Sep ((finRep E N).comp (locGL E N w)) t.space (lp P w)

def ReadMod : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (s₁ : Tr E a) (s₂ : Tr E b)
  (Pa : Pre E a) (Pb : Pre E b) (w : Pl E), s₁.Good → s₂.Good → s₁.Untw → s₂.Untw → TreeParts s₁ Pa → TreeParts s₂ Pb →
  Sep (pairRt a b w) (pairSpace s₁.space s₂.space) (GlobalTheory.SmGL.extTensor (lp Pa w) (lp Pb w))

def TreeModOf : Prop := LeafMod → NodeMod → JoinMod → TreeMod

def ReadModOf : Prop := TreeMod → ReadMod

def TreeSatOf : Prop := TreeMod → TreeSat

end PositivityTheory.Rg.BcB.F.RS

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEx
section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5

namespace PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def TOut (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (HeightOneSpectrum (𝓞 E)))
    (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
    (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) (D : Pre E n) : Prop :=
  Base π D ∧ (∀ w ∈ S, IsSplitAt w → D.SplitAt π w) ∧ (∀ w ∈ T, IsUnramU π w → ¬ IsSplitAt w → InertAt π D w) ∧
    (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D.h w (D.σ · w)) (K w)) ∧ ∀ i, HasKType (W (D.N i)) (D.V i)

structure Setup (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (HeightOneSpectrum (𝓞 E)))
    (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
    (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) where
  A : Type
  [cr : CommRing A]
  [sr : StarRing A]
  [al : Algebra ℂ A]
  [sm : StarModule ℂ A]
  ι : Type
  [ft : Fintype ι]
  [ne : Nonempty ι]
  H : ι → Type
  [ng : ∀ s, NormedAddCommGroup (H s)]
  [ip : ∀ s, InnerProductSpace ℂ (H s)]
  [cs : ∀ s, CompleteSpace (H s)]
  R : ∀ s, A →⋆ₐ[ℂ] (H s →L[ℂ] H s)
  β : ∀ s, H s →L[ℂ] H s
  m : ℕ
  V : Type
  [ag : AddCommGroup V]
  [md : Module ℂ V]
  [fd : FiniteDimensional ℂ V]
  ρ : A →ₐ[ℂ] Module.End ℂ V
  u : Module.End ℂ V
  p : A →⋆ₐ[ℂ] ℂ
  a₀ : A
  pa₀ : p a₀ ≠ 0
  comm : ∀ s g, Commute (β s) (R s g)
  commU : ∀ g, Commute u (ρ g)
  bound : ∀ g ∈ Ideal.span {a₀}, ∃ (C : ℝ) (N j : ℕ), ∀ᶠ k : ℕ in Filter.atTop,
    ‖LinearMap.trace ℂ V ((u * ρ g) ^ k)‖ ≤ C * (1 + k) ^ N *
      Finset.univ.sup' Finset.univ_nonempty (fun s => ‖(β s ^ m * R s g) ^ (k - j)‖)
  eig : ∃ v : V, v ≠ 0 ∧ u v = v ∧ ∀ g, ρ g v = p g • v
  read : ∀ (s : ι) (χ : StarAlgebra.adjoin ℂ (Set.range (R s) ∪ {star (β s ^ m) * β s ^ m}) →⋆ₐ[ℂ] ℂ),
    (∀ x, ‖χ x‖ ≤ ‖(x : H s →L[ℂ] H s)‖) →
    (∀ g, χ ⟨R s g, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨g, rfl⟩)⟩ = p g) →
    χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0 → ∃ D : Pre E n, TOut π S T K W D

def SetupEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
      (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)), IsLevel K ∧ (∀ N, FiniteDimensional ℂ (W N)) ∧
      ∀ T : Finset (HeightOneSpectrum (𝓞 E)), Nonempty (Setup π S T K W)

theorem runT_of (h1 : PeakTraceBound) (h2 : SetupEx) : RunT := by
  intro E _ _ _ hE n hn π hπ S hS
  obtain ⟨K, W, hK, hW, hX⟩ := h2 E hE n hn π hπ S hS
  refine ⟨K, W, hK, hW, fun T => ?_⟩
  obtain ⟨X⟩ := hX T
  letI := X.cr; letI := X.sr; letI := X.al; letI := X.sm; letI := X.ft; letI := X.ne; letI := X.ng; letI := X.ip
  letI := X.cs; letI := X.ag; letI := X.md; letI := X.fd
  obtain ⟨s, χ, h1', h2', h3'⟩ := h1 X.A X.ι X.H X.R X.β X.m X.V X.ρ X.u X.p X.a₀ X.comm X.commU X.pa₀ X.bound X.eig
  exact X.read s χ h1' h2' h3'

end PositivityTheory.Rg.BcB.F

end
end

