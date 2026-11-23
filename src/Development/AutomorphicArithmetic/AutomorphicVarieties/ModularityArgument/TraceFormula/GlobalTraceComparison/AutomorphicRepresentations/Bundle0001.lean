module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.TwTrSum
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ThetaFixedGlobalOfTraceInputs

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelG borelF borelA borelH

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def kI (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Kinf E n →* GA E n := (infGL E n).comp Unitary.toUnits

def TypeF (K : Subgroup (GL (Fin n) (Af E))) (W : Submodule ℂ (Kinf E n → ℂ)) (f : GA E n → ℂ) : Prop :=
  (∀ u ∈ K, ∀ g, f (g * finGL E n u) = f g) ∧ ∀ g, (fun k : Kinf E n => f (g * kI E n k)) ∈ W

def LeftType (K : Subgroup (GL (Fin n) (Af E))) (W : Submodule ℂ (Kinf E n → ℂ)) (φ : H E n 0 → ℂ) : Prop :=
  (∀ u ∈ K, ∀ y : H E n 0, φ ((finGL E n u, 1) * y) = φ y) ∧ ∀ y : H E n 0, (fun k : Kinf E n => φ (((kI E n k)⁻¹, 1) * y)) ∈ W

def RInv {Γ : Type} [Group Γ] (W : Submodule ℂ (Γ → ℂ)) : Prop := ∀ f ∈ W, ∀ k, (fun x => f (x * k)) ∈ W

def cvF (μ : Measure (H E n 0)) (φ : H E n 0 → ℂ) (u : ℝ → ℂ) (f : GA E n → ℂ) (x : GA E n) : ℂ :=
  ∫ y, φ y * u (ldet y) * f (x * y.1) ∂μ

def Slab (D : Dom E n 0) (f : GA E n → ℂ) : Prop :=
  Continuous f ∧ (∀ γ g, f (ratGL E n γ * g) = f g) ∧ (∀ t g, f (splitCentre E n t * g) = f g) ∧
    ∀ u : ℝ → ℂ, Continuous u → HasCompactSupport u → MemLp (fun x : H E n 0 => f x.1 * u (ldet x)) 2 D.ν

def prW (D : Dom E n 0) (u : ℝ → ℂ) (a b : GA E n → ℂ) : ℂ := ∫ x, starRingEnd ℂ (a x.1) * b x.1 * u (ldet x) ∂D.ν

def InS (D : Dom E n 0) (π : CuspSub E n) (f : GA E n → ℂ) : Prop :=
  ∀ u : ℝ → ℂ, Continuous u → HasCompactSupport u → ∃ v ∈ piSp D π Unit,
    (v () : H E n 0 → ℂ) =ᵐ[D.ν] fun x => f x.1 * u (ldet x)

end Defs

def TensType : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (μa : Measure (G n)) (μb : Measure (G 0)),
  μa.IsHaarMeasure → μb.IsHaarMeasure →
  ∀ (Ma : Mods E n) (Mb : Mods E 0) (κ : Type) (ka : Kers Ma) (kb : Kers Mb) va vb (R : ℝ) (ψ : Matrix κ κ (Hf E n 0 → ℂ))
    (U : Subgroup (Hf E n 0)), IsMults μa ka va R → IsMults μb kb vb R → IsFinM ψ → IsOpen (U : Set (Hf E n 0)) →
    (∀ x y, ∀ u ∈ U, ∀ h, ψ x y (u * h) = ψ x y h) → ∀ i j, IsTestH (tens ka kb ψ i j) ∧
      ∃ (K : Subgroup (GL (Fin n) (Af E))) (W : Submodule ℂ (Kinf E n → ℂ)), IsOpen (K : Set (GL (Fin n) (Af E))) ∧
        IsCompact (K : Set (GL (Fin n) (Af E))) ∧ FiniteDimensional ℂ W ∧ RInv W ∧ LeftType K W (tens ka kb ψ i j)

def DetZero : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
  (∀ k : Kinf E n, logAbs (kI E n k).val.det = 0) ∧ ∀ K : Subgroup (GL (Fin n) (Af E)), IsCompact (K : Set (GL (Fin n) (Af E))) →
    ∀ k ∈ K, logAbs (finGL E n k).val.det = 0

def CvType : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Dom E n 0) (K : Subgroup (GL (Fin n) (Af E)))
  (W : Submodule ℂ (Kinf E n → ℂ)) (φ : H E n 0 → ℂ) (u : ℝ → ℂ) (f : GA E n → ℂ), IsCompact (K : Set (GL (Fin n) (Af E))) →
    FiniteDimensional ℂ W → IsTestH φ → LeftType K W φ → Continuous u → Continuous f → TypeF K W (cvF D.μ φ u f)

def CvIn : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ ψ ∈ π.V, Slab D ψ.1 ∧ ∀ (φ : H E n 0 → ℂ) (u : ℝ → ℂ), IsTestH φ → Continuous u →
    Slab D (cvF D.μ φ u ψ.1) ∧ InS D π (cvF D.μ φ u ψ.1) ∧ InS D π ψ.1

def WtInd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (a b : GA E n → ℂ),
  Slab D a → Slab D b → ∀ u : ℝ → ℂ, Continuous u → HasCompactSupport u →
    Integrable (fun x : H E n 0 => starRingEnd ℂ (a x.1) * b x.1 * u (ldet x)) D.ν ∧
    (∀ w : ℝ → ℂ, Continuous w → HasCompactSupport w → ∫ s, w s = 1 → prW D u a b = (∫ s, u s) * prW D w a b) ∧
    ∀ g : GA E n, logAbs g.val.det = 0 → Slab D (fun x => a (x * g)) ∧ prW D u (fun x => a (x * g)) (fun x => b (x * g)) = prW D u a b

def OrthZero : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ f : GA E n → ℂ, Slab D f → InS D π f →
    (∀ ψ ∈ π.V, ∀ u : ℝ → ℂ, Continuous u → HasCompactSupport u → prW D u ψ.1 f = 0) → f = 0

def FormEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ D : Dom E n 0,
  ∃ (F : Submodule ℂ (GA E n → ℂ)) (B : F →ₗ⋆[ℂ] F →ₗ[ℂ] ℂ), (∀ f, f ∈ F ↔ Slab D f) ∧
    (∀ a b, starRingEnd ℂ (B a b) = B b a) ∧ (∀ a, a ≠ 0 → 0 < (B a a).re) ∧
    (∀ (a b : F) (u : ℝ → ℂ), Continuous u → HasCompactSupport u → prW D u a b = (∫ s, u s) * B a b) ∧
    ∀ g : GA E n, logAbs g.val.det = 0 → ∀ a : F, (fun x => a.1 (x * g)) ∈ F ∧
      ∀ a' b b' : F, (∀ x, a'.1 x = a.1 (x * g)) → (∀ x, b'.1 x = b.1 (x * g)) → B a' b' = B a b

def AbsType : Prop := ∀ (Γ F : Type) [Group Γ] [AddCommGroup F] [Module ℂ F] (R : Representation ℂ Γ F) (B : F →ₗ⋆[ℂ] F →ₗ[ℂ] ℂ)
  (W : Submodule ℂ (Γ → ℂ)) (V Y : Submodule ℂ F) (z : F), (∀ a b, starRingEnd ℂ (B a b) = B b a) → (∀ a, a ≠ 0 → 0 < (B a a).re) →
    (∀ k a b, B (R k a) (R k b) = B a b) → RInv W → (∀ k, ∀ v ∈ V, R k v ∈ V) →
    (∀ v ∈ V, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => R k v))) → FiniteDimensional ℂ Y →
    (∀ v ∈ V, (∀ l : F →ₗ[ℂ] ℂ, (fun k => l (R k v)) ∈ W) → v ∈ Y) →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => R k z)) → (∀ l : F →ₗ[ℂ] ℂ, (fun k => l (R k z)) ∈ W) →
    ∃ y ∈ V, y ∈ Y ∧ ∀ v ∈ V, B v (z - y) = 0

def TypeIn : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ (K : Subgroup (GL (Fin n) (Af E))) (W : Submodule ℂ (Kinf E n → ℂ)), IsOpen (K : Set (GL (Fin n) (Af E))) →
    IsCompact (K : Set (GL (Fin n) (Af E))) → FiniteDimensional ℂ W → RInv W →
    ∀ f : GA E n → ℂ, Slab D f → InS D π f → TypeF K W f → ∃ ψ ∈ π.V, ψ.1 = f

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelG borelF borelA borelH

def Lv {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) :
    Module.End ℂ V := levOp ρ K K f LinearMap.id

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev GF (E : Type) [Field E] [NumberField E] (n : ℕ) : Type := GL (Fin n) (Af E)

def jw (n : ℕ) (w : Pl E) : Bool → (GLw n w →* GF E n)
  | false => locGL E n w
  | true => (thF E n).comp (locGL E n w)

def qw (n : ℕ) (w : Pl E) : Bool → (GF E n →* GLw n w)
  | false => GeneralLinearGroup.map (pLoc E w)
  | true => (GeneralLinearGroup.map (pLoc E w) : GF E n →* GLw n w).comp (thF E n)

def Sl (S : Set (Pl E)) (i : Pl E × Bool) : Prop := i.1 ∈ S ∧ (i.2 = true → IsSplitAt i.1)

def Good (Z : Finset (Pl E)) (N : ∀ w : Pl E, Subgroup (GLw n w)) : Prop :=
  ∀ w, IsOpen (N w : Set (GLw n w)) ∧ N w ≤ KGL w (n := n) ∧ (∀ k ∈ KGL w (n := n), ∀ x ∈ N w, k * x * k⁻¹ ∈ N w) ∧ (w ∉ Z → N w = KGL w (n := n))

def Lev (S : Set (Pl E)) (N : ∀ w : Pl E, Subgroup (GLw n w)) : Subgroup (GF E n) :=
  ⨅ i : {i : Pl E × Bool // Sl S i}, (N i.1.1).comap (qw n i.1.1 i.1.2)

def pf (S : Set (Pl E)) (F : ∀ w : Pl E, Bool → GLw n w → ℂ) (g : GF E n) : ℂ :=
  ∏ᶠ w ∈ S, F w false (qw n w false g) * if IsSplitAt w then F w true (qw n w true g) else 1

def Fam (S : Set (Pl E)) (N : ∀ w : Pl E, Subgroup (GLw n w)) (I : Finset (Pl E × Bool)) (F : ∀ w : Pl E, Bool → GLw n w → ℂ) : Prop :=
  (∀ i ∈ I, Sl S i ∧ IsHecke (N i.1) (F i.1 i.2)) ∧ ∀ i, Sl S i → i ∉ I → F i.1 i.2 = (N i.1 : Set (GLw n i.1)).indicator 1

def rw' (n : ℕ) (w : Pl E) (b : Bool) : Representation ℂ (GLw n w) (Sm E n) := (finRep E n).comp (jw n w b)

def Lw (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (b : Bool) (f : GLw n w → ℂ) : Module.End ℂ (Sm E n) := Lv (rw' n w b) (N w) f

structure Yd (π : CuspSub E n) (K : Subgroup (GF E n)) where
  Y : Submodule ℂ (Sm E n)
  r : (GF E n → ℂ) → Module.End ℂ Y
  A : Module.End ℂ Y
  le : Y ≤ π.V
  fd : FiniteDimensional ℂ Y
  ne : Y ≠ ⊥
  fix : Y ≤ fixed (finRep E n) K
  act : ∀ h, IsHecke K h → ∀ y : Y, (r h y : Sm E n) = Lv (finRep E n) K h y
  simple : ∀ W : Submodule ℂ Y, (∀ h, IsHecke K h → ∀ y ∈ W, r h y ∈ W) → W = ⊥ ∨ W = ⊤
  sq : A * A = 1
  tw : ∀ h, IsHecke K h → A * r h = r (fun g => h (thF E n g)) * A

def two (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w) (w : Pl E) : Bool → GLw n w → ℂ
  | false => fun g => φ₁ w (g, 1)
  | true => fun g => φ₂ w (g, 1)

end Defs

def ForLev (P : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), Set (Pl E) → Finset (Pl E) →
    (∀ w : Pl E, Subgroup (GLw n w)) → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (Z : Finset (Pl E)) (N : ∀ w : Pl E, Subgroup (GLw n w)),
    IsSection S → SplitIn S Z → Good Z N → P E n S Z N

def SlotBasic : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S →
  (∀ g, thF E n (thF E n g) = g) ∧ Continuous (thF E n) ∧
  (∀ (w : Pl E) b, Continuous (jw n w b) ∧ Continuous (qw n w b) ∧ (∀ a, qw n w b (jw n w b a) = a) ∧
    ∀ a c, qw n w b c = 1 → Commute (jw n w b a) c) ∧
  (∀ i k, Sl S i → Sl S k → i ≠ k → ∀ a, qw n k.1 k.2 (jw n i.1 i.2 a) = 1) ∧
  (∀ g : GF E n, {i : Pl E × Bool | qw n i.1 i.2 g ∉ KGL i.1 (n := n)}.Finite) ∧
  (∀ w : Pl E, ¬ IsSplitAt w → ∀ g, qw n w true g ∈ KGL w (n := n) ↔ qw n w false g ∈ KGL w (n := n)) ∧
  ∀ g : GF E n, g ∈ Lev S (fun w => KGL w (n := n)) ↔ g ∈ Kf E n

def LevTop : Prop := ForLev fun E _ _ _ n S _ N => IsOpen (Lev S N : Set (GF E n)) ∧ IsCompact (Lev S N : Set (GF E n)) ∧
  (∀ k ∈ Lev S N, thF E n k ∈ Lev S N) ∧ ∀ k ∈ Kf E n, ∀ x ∈ Lev S N, k * x * k⁻¹ ∈ Lev S N

def TranslF : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : GL (Fin n) E), IsTransl u →
  (∀ g, thF E n g = ratF E n u * thetaF E n g * (ratF E n u)⁻¹) ∧ thF E n (ratF E n u) = (ratF E n u)⁻¹ ∧
    ∃ k ∈ Kf E n, ∀ g : GF E n, ratF E n u * g * (ratF E n u)⁻¹ = k * g * k⁻¹

def LevFix : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : CuspSub E n) (S : Set (Pl E)) (Z : Finset (Pl E)),
  IsSection S → SplitIn S Z → (∀ w, Off Z w → ∃ B, (CG.mk π).HasSat w B) →
    ∃ N : ∀ w : Pl E, Subgroup (GLw n w), Good Z N ∧ ∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ k ∈ Lev S N, finRep E n k ψ = ψ

def JointFix : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : CuspSub E n) (P : Finset (Pl E)),
  (∀ w ∈ P, ∃ B, (CG.mk π).HasSat w B) → ∀ U : Subgroup (GF E n), (∀ k ∈ U, ∀ w ∈ P, qw n w false k = 1) →
    (∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ k ∈ U, finRep E n k ψ = ψ) →
    ∃ ψ ∈ π.V, ψ ≠ 0 ∧ (∀ k ∈ U, finRep E n k ψ = ψ) ∧ ∀ w ∈ P, ψ ∈ fixed (rw' n w false) (KGL w (n := n))

def LcLevel : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Z : Finset (Pl E))
  (N₀ : ∀ w : Pl E, Subgroup (GLw n w)), Good Z N₀ → ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w,
    (∀ w ∈ Z, Lc (K2 n 0 w) (φ₁ w) ∧ Lc (K2 n 0 w) (φ₂ w)) →
    ∃ N, Good Z N ∧ (∀ w, N w ≤ N₀ w) ∧ ∀ w ∈ Z, ∀ b, IsHecke (N w) (two φ₁ φ₂ w b)

def HeckeSum : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (K : Subgroup (GF E n)),
  IsOpen (K : Set (GF E n)) → IsCompact (K : Set (GF E n)) → ∀ (μf : Measure (GF E n)), μf.IsHaarMeasure → ∀ h, IsHecke K h →
    ∀ y ∈ fixed (finRep E n) K, heckeOp μf h y.1 = fun x => ((μf K).toReal : ℂ) * (Lv (finRep E n) K h y).1 x

def LvShift : Prop := ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ u : G,
    (∀ x, x ∈ K ↔ u * x * u⁻¹ ∈ K) → ∀ h, IsHecke K h →
      IsHecke K (fun g => h (g * u⁻¹)) ∧ IsHecke K (fun g => h (u⁻¹ * g)) ∧ IsHecke K ((K : Set G).indicator 1) ∧
      ∀ y ∈ fixed ρ K, ρ u y ∈ fixed ρ K ∧ Lv ρ K (fun g => h (g * u⁻¹)) y = Lv ρ K h (ρ u y) ∧
        Lv ρ K (fun g => h (u⁻¹ * g)) y = ρ u (Lv ρ K h y) ∧ Lv ρ K ((K : Set G).indicator 1) y = y

def ToYd : Prop := ForLev fun E _ _ _ n S _ N => ∀ (π : CuspSub E n) (u : GL (Fin n) E), IsTransl u →
  (∀ k ∈ Lev S N, thetaF E n k ∈ Lev S N) ∧
  ∀ (μf : Measure (GF E n)), μf.IsHaarMeasure → ∀ (Y : Submodule ℂ (Sm E n)) (ρ : (GF E n → ℂ) → Module.End ℂ Y) (A : Module.End ℂ Y),
    Y ≤ π.V → FiniteDimensional ℂ Y → Y ≠ ⊥ → (∀ y ∈ Y, ∀ k ∈ Lev S N, finRep E n k y = y) → IsHeckeAct μf (Lev S N) Y ρ →
    (∀ W : Submodule ℂ Y, (∀ h, IsHeckeF (Lev S N) h → ∀ y ∈ W, ρ h y ∈ W) → W = ⊥ ∨ W = ⊤) → A * A = 1 →
    (∀ h, IsHeckeF (Lev S N) h → A * ρ h = ρ (fun g => h (thetaF E n g)) * A) →
    ∃ (y : Yd π (Lev S N)) (v : ℂ), v ≠ 0 ∧ ∀ h, IsHecke (Lev S N) h → IsHeckeF (Lev S N) (fun g => h (g * (ratF E n u)⁻¹)) ∧
      LinearMap.trace ℂ Y (ρ (fun g => h (g * (ratF E n u)⁻¹)) * A) = v * LinearMap.trace ℂ y.Y (y.r h * y.A)

def AbsStep : Prop := ∀ (G A V : Type) [Group G] [Group A] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
  (N : Subgroup A) (j : A →* G) (q : G →* A) (f : A → ℂ) (h h₁ : G → ℂ), (∀ a, q (j a) = a) → (∀ a c, q c = 1 → Commute (j a) c) →
    (∀ a ∈ N, j a ∈ K) → (∀ k ∈ K, q k ∈ N) → (∀ g, h g = f (q g) * h₁ ((j (q g))⁻¹ * g)) → (∀ g, h₁ g ≠ 0 → q g ∈ N) →
    (∀ k ∈ K, ∀ g, h₁ (k * g) = h₁ g ∧ h₁ (g * k) = h₁ g) → (∀ a ∈ N, ∀ x, f (x * a) = f x) →
    (Function.support fun c : A ⧸ N => f c.out).Finite → (Function.support fun c : G ⧸ K => h₁ c.out).Finite →
    ∀ y ∈ fixed ρ K, Lv ρ K h y = Lv (ρ.comp j) N f (Lv ρ K h₁ y)

def PfHecke : Prop := ForLev fun _ _ _ _ _ S _ N => ∀ I F, Fam S N I F → IsHecke (Lev S N) (pf S F)

def ProdOp : Prop := ForLev fun E _ _ _ n S _ N => ∀ I F, Fam S N I F → ∀ y ∈ fixed (finRep E n) (Lev S N),
  Lv (finRep E n) (Lev S N) (pf S F) y = (I.toList.map fun i => Lw N i.1 i.2 (F i.1 i.2)).prod y

def GenLoc : Prop := ForLev fun E _ _ _ n S _ N => ∀ W : Submodule ℂ (Sm E n), W ≤ fixed (finRep E n) (Lev S N) →
  (∀ i, Sl S i → ∀ f, IsHecke (N i.1) f → ∀ y ∈ W, Lw N i.1 i.2 f y ∈ W) →
    ∀ h, IsHecke (Lev S N) h → ∀ y ∈ W, Lv (finRep E n) (Lev S N) h y ∈ W

def LocComm : Prop := ForLev fun E _ _ _ n S _ N => ∀ i, Sl S i → ∀ f, IsHecke (N i.1) f →
  (∀ y ∈ fixed (finRep E n) (Lev S N), y ∈ fixed (rw' n i.1 i.2) (N i.1) ∧ Lw N i.1 i.2 f y ∈ fixed (finRep E n) (Lev S N)) ∧
    ∀ k, Sl S k → i ≠ k → ∀ g, IsHecke (N k.1) g → Commute (Lw N i.1 i.2 f) (Lw N k.1 k.2 g)

def SphOp : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (V : Type) [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GLw n w) V) (f g : GLw n w → ℂ), IsHecke (KGL w (n := n)) f → IsHecke (KGL w (n := n)) g →
    ∀ x ∈ fixed ρ (KGL w (n := n)), Lv ρ (KGL w (n := n)) f (Lv ρ (KGL w (n := n)) g x) = Lv ρ (KGL w (n := n)) g (Lv ρ (KGL w (n := n)) f x)

def YLoc : Prop := ForLev fun _ _ _ _ _ S _ N => ∀ π (y : Yd π (Lev S N)) i, Sl S i → ∀ f, IsHecke (N i.1) f →
  ∀ x ∈ y.Y, Lw N i.1 i.2 f x ∈ y.Y

def ZSimple : Prop := ForLev fun _ _ _ _ _ S Z N => ∀ π (y : Yd π (Lev S N)), ∀ W ≤ y.Y,
  (∀ w ∈ Z, ∀ b f, IsHecke (N w) f → ∀ x ∈ W, Lw N w b f x ∈ W) → W = ⊥ ∨ W = y.Y

def YSwap : Prop := ForLev fun E _ _ _ n S Z N => ∀ π (y : Yd π (Lev S N)), ∀ w ∈ Z, ∀ f, IsHecke (N w) f → ∀ x x' : y.Y,
  (x' : Sm E n) = Lw N w false f x → (y.A x' : Sm E n) = Lw N w true f (y.A x)

def Isot : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : CuspSub E n) (w : Pl E) (τ : SmIrr (GLw n w)),
  π.IsLocComp w τ → ∀ N : Subgroup (GLw n w), IsOpen (N : Set (GLw n w)) → N ≤ KGL w (n := n) →
    ∀ p : FreeAlgebra ℂ (GLw n w → ℂ), (∀ x ∈ fixed τ.ρ N, FreeAlgebra.lift ℂ (Lv τ.ρ N) p x = 0) →
      ∀ y ∈ π.V, y ∈ fixed (rw' n w false) N → FreeAlgebra.lift ℂ (Lv (rw' n w false) N) p y = 0

def SimpleFix : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (τ : SmIrr (GLw n w))
  (N : Subgroup (GLw n w)), IsOpen (N : Set (GLw n w)) → N ≤ KGL w (n := n) →
    (∀ f, IsHecke N f → ∀ x ∈ fixed τ.ρ N, Lv τ.ρ N f x ∈ fixed τ.ρ N) ∧
    ∀ W ≤ fixed τ.ρ N, (∀ f, IsHecke N f → ∀ x ∈ W, Lv τ.ρ N f x ∈ W) → W = ⊥ ∨ W = fixed τ.ρ N

def TraceForm : Prop := ∀ (J M Y : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] [Nontrivial M] [AddCommGroup Y] [Module ℂ Y]
  (α : J → Module.End ℂ M) (a : J → Module.End ℂ Y) (C : Module.End ℂ Y),
    (∀ W : Submodule ℂ M, (∀ f, ∀ x ∈ W, α f x ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∀ p, FreeAlgebra.lift ℂ α p = 0 → FreeAlgebra.lift ℂ a p = 0) →
    (∀ p p', LinearMap.trace ℂ Y (FreeAlgebra.lift ℂ a p * FreeAlgebra.lift ℂ a p' * C) =
      LinearMap.trace ℂ Y (FreeAlgebra.lift ℂ a p' * FreeAlgebra.lift ℂ a p * C)) →
    ∀ p, (Module.finrank ℂ M : ℂ) * LinearMap.trace ℂ Y (FreeAlgebra.lift ℂ a p * C) =
      LinearMap.trace ℂ M (FreeAlgebra.lift ℂ α p) * LinearMap.trace ℂ Y C

def AbsCore : Prop := ∀ (I : Type) [Fintype I] (J M : I → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
  [∀ i, FiniteDimensional ℂ (M i)] (Y : Type) [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y] [Nontrivial Y]
  (α : ∀ i, J i → Module.End ℂ (M i)) (a b : ∀ i, J i → Module.End ℂ Y) (A : Module.End ℂ Y),
    (∀ i, ∀ W : Submodule ℂ (M i), (∀ f, ∀ x ∈ W, α i f x ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∀ i p, FreeAlgebra.lift ℂ (α i) p = 0 → FreeAlgebra.lift ℂ (a i) p = 0) →
    (∀ i k, i ≠ k → ∀ f g, Commute (a i f) (a k g)) → (∀ i k f g, Commute (a i f) (b k g)) →
    A * A = 1 → (∀ i f, A * a i f = b i f * A) →
    (∀ W : Submodule ℂ Y, (∀ i f, ∀ x ∈ W, a i f x ∈ W ∧ b i f x ∈ W) → W = ⊥ ∨ W = ⊤) →
    ∃ d : ℂ, d ≠ 0 ∧ ∀ f g : ∀ i, J i,
      LinearMap.trace ℂ Y (((Finset.univ : Finset I).toList.map fun i => a i (f i) * b i (g i)).prod * A) =
        d * ∏ i, LinearMap.trace ℂ (M i) (α i (f i) * α i (g i))

def ZTr : Prop := ForLev fun E _ _ _ n S Z N => ∀ π (y : Yd π (Lev S N)) (τ : ∀ w : Pl E, SmIrr (GLw n w)),
  (∀ w ∈ Z, π.IsLocComp w (τ w)) → (∀ w ∈ Z, fixed (τ w).ρ (N w) ≠ ⊥) ∧ ∃ d : ℂ, d ≠ 0 ∧ ∀ F, Fam S N (Z ×ˢ Finset.univ) F →
    LinearMap.trace ℂ y.Y (y.r (pf S F) * y.A) =
      d * ∏ w ∈ Z, GlobalTheory.BCT.trOn (fixed (τ w).ρ (N w)) (Lv (τ w).ρ (N w) (F w false) * Lv (τ w).ρ (N w) (F w true))

def SeenTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w → ∀ (τ : SmIrr (GLw n w))
  (N : Subgroup (GLw n w)), IsOpen (N : Set (GLw n w)) → N ≤ KGL w (n := n) → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w,
    (∀ b, IsHecke N (two φ₁ φ₂ w b)) →
      GlobalTheory.BCT.trOn (fixed τ.ρ N) (Lv τ.ρ N (two φ₁ φ₂ w false) * Lv τ.ρ N (two φ₁ φ₂ w true)) =
        c * trc τ.ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1)

def Ex2Act : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (e : Ex (Fin (n + 1) × Fin (0 + 1))),
  IsHecke (KGL w (n := n)) (fun g => fn2 n 0 w e (g, 1)) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLw n w) V)
    (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → Lv ρ (KGL w (n := n)) (fun g => fn2 n 0 w e (g, 1)) x = ev2 n 0 w e B 0 • x

def SatAll : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : CuspSub E n) (w : Pl E) (B : Multiset ℂˣ),
  ∀ y ∈ π.V, y ≠ 0 → ((CG.mk π).HasSat w B → y ∈ fixed (rw' n w false) (KGL w (n := n)) → IsSatVecGL w (rw' n w false) y B) ∧
    ((CG.mk π).HasSat (cPl w) B → y ∈ fixed (rw' n w true) (KGL w (n := n)) → IsSatVecGL w (rw' n w true) y (inv B))

def TTr : Prop := ForLev fun E _ _ _ n S Z N => ∀ π (y : Yd π (Lev S N)) (B : Pl E → Multiset ℂˣ),
  (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) → ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) →
    ∀ T : Finset (Pl E), Disjoint T Z → ∀ e₁ e₂, TEv S T e₂ →
      IsHecke (Lev S N) (pf S (two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂))) ∧
      Fam S N (Z ×ˢ Finset.univ) (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂)) ∧
      y.r (pf S (two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂))) = val T e₁ e₂ B 0 • y.r (pf S (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂)))

def LevelTr : Prop := ForLev fun E _ _ _ n S Z N => ∀ π (y : Yd π (Lev S N)) (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)),
  (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) → (∀ w ∈ Z, π.IsLocComp w (τ w)) →
    (∃ φ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ N' ≤ N w, ∀ b, IsHecke N' (two φ φ w b)) ∧
      (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ φ w (g, 1)) ≠ 0) ∧
    ∃ d : ℂ, d ≠ 0 ∧ ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) →
      ∀ T : Finset (Pl E), Disjoint T Z → ∀ e₁ e₂, TEv S T e₂ →
        IsHecke (Lev S N) (fun g => finFn S (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂) (g, 1)) ∧
        LinearMap.trace ℂ y.Y (y.r (fun g => finFn S (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂) (g, 1)) * y.A) =
          d * (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0

def WtEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : CuspSub E n), (CG.mk π).IsRegAlg →
  ∃ lamE : (E →+* ℂ) → DomWeight n, ∀ φ, π.HasInfChar φ (infOfWeight (lamE φ))

def TwUniq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (μ : Measure (H E n 0)) (π : CuspSub E n)
  (φ : H E n 0 → ℂ) (t t' : ℂ), IsTwTr μ π φ t → IsTwTr μ π φ t' → t = t'

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

