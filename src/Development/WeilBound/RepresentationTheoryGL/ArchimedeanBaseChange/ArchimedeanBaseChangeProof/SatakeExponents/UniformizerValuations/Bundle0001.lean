module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.EigInert
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Eig

def EigInert : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
    ∀ (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (q : ℕ) (σ : SmIrr (UL n w)) (α : Fin (n / 2) → ℂˣ),
    IsWitt n w b → IsUnifAt ϖ → IsUnramInv (ϖ : w.adicCompletion E) (cj w) q → IsAdmissible σ.ρ →
    SatUL b (ϖ : w.adicCompletion E) q σ α →
    ∃ β : Fin (n / 2) → ℂˣ, GlobalTheory.LGrp.WeylConjU α β ∧ (∀ i j : Fin (n / 2), i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖) ∧
      (∀ i, 1 ≤ ‖(β i : ℂ)‖) ∧ ∃ y ∈ fixed σ.ρ (iwU n w b), y ≠ 0 ∧ ∀ l : Fin (n / 2) → ℤ, Cone l →
        levOp σ.ρ (KL n w) (iwU n w b) (fU n w b ϖ l) LinearMap.id y =
          ((((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ * dlt n w l * pw β l) • y

def AbsEig : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (α : Fin (n / 2) → ℂˣ),
    IsUnramInv ϖ σ q → IsAdmissible ρ → ρ.IsIrreducible → GlobalTheory.LFun.HasSatU ϖ q ρ α →
    ∃ β : Fin (n / 2) → ℂˣ, GlobalTheory.LGrp.WeylConjU α β ∧ (∀ i j : Fin (n / 2), i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖) ∧
      (∀ i, 1 ≤ ‖(β i : ℂ)‖) ∧ ∃ y : fixed ρ (PositivityTheory.SphericalProduct.IwU σ n), y ≠ 0 ∧
        ∀ t : GU σ n, PositivityTheory.SphericalProduct.IsDiagM (t : GL (Fin n) L) → PositivityTheory.SphericalProduct.IsStrictDom (t : GL (Fin n) L) →
          ∀ U : Module.End ℂ (fixed ρ (PositivityTheory.SphericalProduct.IwU σ n)), PositivityTheory.Lbc.IsHeckeOpG ρ (PositivityTheory.SphericalProduct.IwU σ n) (t : GU σ n) U →
            U y = chiDeltaU q (fun i => (β i : ℂ)) t • y

def HeckeSum : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), IsSmooth ρ → ∀ (K J : Subgroup G), IsOpen (J : Set G) → IsCompact (K : Set G) → J ≤ K →
    ∀ (t : G) (U : Module.End ℂ (fixed ρ J)), PositivityTheory.Lbc.IsHeckeOpG ρ J t U → ∀ y : fixed ρ J,
      levOp ρ K J (fun g => if ∃ x ∈ J, ∃ z ∈ J, g = x * t * z then 1 else 0) LinearMap.id (y : V) =
        (((J.relIndex K : ℕ) : ℂ)⁻¹ * (((J.map (MulAut.conj t).toMonoidHom).relIndex J : ℕ) : ℂ)) • ((U y : fixed ρ J) : V)

def IndexU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q → ∀ (l : Fin (n / 2) → ℤ), Cone l → ∀ t : GU σ n,
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => ϖ ^ wexp n l i) →
      (((PositivityTheory.SphericalProduct.IwU σ n).map (MulAut.conj t).toMonoidHom).relIndex (PositivityTheory.SphericalProduct.IwU σ n) : ℤ) =
        (q : ℤ) ^ (2 * ∑ i : Fin (n / 2), (((n : ℤ) - 1 - 2 * (i : ℕ)) * l i)).toNat

def EigInertOf : Prop := AbsEig → HeckeSum → IndexU → EigInert

end PositivityTheory.Rg.BcB.F.Eig

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcN.F2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

def phi3 (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (x y : GLw n w) (m : GLw a w × GLw b w) : ℂ :=
  absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) *
    hint (intMat a b w) fun X => f (x⁻¹ * blk h w m (Multiplicative.toAdd X) * y)

def gconv {w : Pl E} (f₁ f₂ : GLw n w → ℂ) (y : GLw n w) : ℂ := hint (GlobalTheory.LFun.KGL w (n := n)) fun z => f₁ z * f₂ (z⁻¹ * y)

def mconv {w : Pl E} (u₁ u₂ : GLw a w × GLw b w → ℂ) (m : GLw a w × GLw b w) : ℂ :=
  hint ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) fun m' => u₁ m' * u₂ (m'⁻¹ * m)

def leviOf (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)) : Set (GLw a w × GLw b w) := {m | blk h w m 0 ∈ K'}


variable (E) in
def LocOpUniformizer : Prop :=
  ∀ (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) →
    K' ≤ GlobalTheory.LFun.KGL w (n := n) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') →
    ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') →
    (∀ f : GLw n w → ℂ, IsHk K' f → ∀ x ∈ X, ∀ y ∈ X,
      IsLocallyConstant (phi3 h w f x y) ∧ HasCompactSupport (phi3 h w f x y) ∧
      ∀ k₁ ∈ leviOf h w K', ∀ k₂ ∈ leviOf h w K', ∀ m, phi3 h w f x y (k₁ * m * k₂) = phi3 h w f x y m) ∧
    (∀ f : GLw n w → ℂ, IsHk K' f → ∀ m, ct h w f m = ((X.card : ℂ))⁻¹ * ∑ x ∈ X, phi3 h w f x x m) ∧
    (∀ f₁ f₂ : GLw n w → ℂ, IsHk K' f₁ → IsHk K' f₂ → ∀ x ∈ X, ∀ z ∈ X, ∀ m,
      phi3 h w (gconv f₁ f₂) x z m = ((X.card : ℂ))⁻¹ * ∑ y ∈ X, mconv (phi3 h w f₁ x y) (phi3 h w f₂ y z) m) ∧
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GLw a w × GLw b w) W),
      ∀ (f : GLw n w → ℂ), IsHk K' f → ∀ u ∈ fixed (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K', ∀ x ∈ X,
        ∀ lw : W →ₗ[ℂ] ℂ, lw ((hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u).1.1 x) =
          ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)))
            fun m => phi3 h w f x y m * lw (ρ m (u.1.1 y))

end PositivityTheory.Rg.BcN.F2
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Eig

def diagOp {ι : Type} {d : ℕ} (blk : Fin d → ι) (c : ι → ℂ) : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
  LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 (Matrix.diagonal fun j => c (blk j)))

def UModel : Prop := ∀ (ι B : Type) [Fintype ι] [Fintype B] (X : ι → B → Type) [∀ i w, AddCommGroup (X i w)]
  [∀ i w, Module ℂ (X i w)] [∀ i w, FiniteDimensional ℂ (X i w)] (L : ∀ i w, Module.End ℂ (X i w)),
  ∃ (d : ℕ) (blk : Fin d → ι) (u : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)),
    (∀ c, Commute u (diagOp blk c)) ∧
    (∀ (c : ι → ℂ) (k : ℕ), LinearMap.trace ℂ _ ((u ^ k * diagOp blk c : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :
      EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) = ∑ i, c i * ∏ w, LinearMap.trace ℂ _ (L i w ^ k)) ∧
    ∀ i₀, (∀ w, ∃ y, y ≠ 0 ∧ L i₀ w y = y) → ∃ v, v ≠ 0 ∧ u v = v ∧ ∀ c, diagOp blk c v = c i₀ • v

def DiagAlg : Prop := ∀ (ι : Type) (d : ℕ) (blk : Fin d → ι) (c c' : ι → ℂ) (z : ℂ),
  diagOp blk (c * c') = diagOp blk c * diagOp blk c' ∧ diagOp blk (c + c') = diagOp blk c + diagOp blk c' ∧
    diagOp blk (fun _ => z) = z • 1 ∧ star (diagOp blk c) = diagOp blk (star c)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def locOp {w : Pl E} (σ : SmIrr (UL n w)) (K' : Subgroup (UL n w)) (f : UL n w → ℂ) : Module.End ℂ (fixed σ.ρ K') :=
  if h : ∀ v ∈ fixed σ.ρ K', levOp σ.ρ (KL n w) K' f LinearMap.id v ∈ fixed σ.ρ K' then
    (levOp σ.ρ (KL n w) K' f LinearMap.id).restrict h else 0

def lconv {w : Pl E} (f₁ f₂ : UL n w → ℂ) (y : UL n w) : ℂ := hint (KL n w) fun z => f₁ z * f₂ (z⁻¹ * y)

def lstar {w : Pl E} (f : UL n w → ℂ) (y : UL n w) : ℂ := starRingEnd ℂ (f y⁻¹)

def LocAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (σ : SmIrr (UL n w))
  (K' : Subgroup (UL n w)), IsLevel (MonoidHom.id _) (KL n w) K' → ∀ f₁ f₂ : UL n w → ℂ, IsHecke K' f₁ → IsHecke K' f₂ →
    twTr σ.ρ (KL n w) K' f₁ LinearMap.id = LinearMap.trace ℂ _ (locOp σ K' f₁) ∧
    (∀ v : fixed σ.ρ K', (locOp σ K' f₁ v).1 = levOp σ.ρ (KL n w) K' f₁ LinearMap.id v.1) ∧
    IsHecke K' (lconv f₁ f₂) ∧ IsHecke K' (lstar f₁) ∧ locOp σ K' (lconv f₁ f₂) = locOp σ K' f₁ * locOp σ K' f₂ ∧
    (∀ z : ℂ, locOp σ K' (f₁ + z • f₂) = locOp σ K' f₁ + z • locOp σ K' f₂) ∧
    IsHecke K' ((K' : Set (UL n w)).indicator fun _ => ((K'.relIndex (KL n w) : ℕ) : ℂ)) ∧
    locOp σ K' ((K' : Set (UL n w)).indicator fun _ => ((K'.relIndex (KL n w) : ℕ) : ℂ)) = 1

def SphOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ) (w : Pl E)
  (σ : SmIrr (UL n w)), fixed σ.ρ (KL n w) ≠ ⊥ → FiniteDimensional ℂ (fixed σ.ρ (KL n w)) →
    Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1

def CompUnit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ (w : Pl E) (σ : SmIrr (UL n w)), IsCompU π w σ → GlobalTheory.SmGL.IsUnitarisable σ.ρ

def IsCong {w : Pl E} (m : ℕ) (K' : Subgroup (UL n w)) : Prop :=
  ∀ k, k ∈ K' ↔ k ∈ KL n w ∧ ∀ i j, Valued.v ((k.1.val - 1) i j) ≤ WithZero.exp (-(m : ℤ))

def LevelEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)),
  IsAutRepU π → ∀ S : Set (Pl E), IsSection S → ∀ (R : Finset (Pl E)) (M : ℕ),
    ∃ (K₀ : ∀ w : Pl E, Subgroup (UL n w)) (m : ℕ), M ≤ m ∧ 1 ≤ m ∧ IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K₀ ∧
      (∀ w, IsUnramU π w → w ∉ R → K₀ w = KL n w) ∧ (∀ w, ¬ IsUnramU π w ∨ w ∈ R → IsCong m (K₀ w)) ∧
      ∀ K' : ∀ w : Pl E, Subgroup (UL n w), (∀ w, K' w ≤ K₀ w) → HasLevel S π K'

def SplitDict : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w →
  ∀ σ : SmIrr (UL n w), ∃ (P : SmIrr (GLw n w)) (T : σ.V ≃ₗ[ℂ] P.V), (∀ (x : UL n w) y, T (σ.ρ x y) = P.ρ x.1 (T y)) ∧
    (∀ π : Submodule ℂ (UA E n → ℂ), IsCompU π w σ → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ) ∧
    ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → ∀ e : GLw n w → ℂ,
      PositivityTheory.Rg.BcN.F2.IsHk (K'.map (UL n w).subtype) e → IsHecke K' (fun x => e x.1) ∧ ∀ y ∈ fixed σ.ρ K',
        T y ∈ fixed P.ρ (K'.map (UL n w).subtype) ∧
        T (levOp σ.ρ (KL n w) K' (fun x => ((K'.relIndex (KL n w) : ℕ) : ℂ) * e x.1) LinearMap.id y) =
          PositivityTheory.Rg.BcN.F2.hk P.ρ (K'.map (UL n w).subtype) e (T y)

def SpecTrace : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (B : Finset (Pl E)),
  (↑B : Set (Pl E)) ⊆ S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
  (∀ w ∈ S, w ∉ B → K' w = KL n w) → ∀ (ι : Type) [Fintype ι] (σ : ι → ∀ w : Pl E, SmIrr (UL n w)),
  (∀ i, ∀ w ∈ S, FiniteDimensional ℂ (fixed (σ i w).ρ (K' w))) →
  (∀ i, ∀ w ∈ S, w ∉ B → Module.finrank ℂ (fixed (σ i w).ρ (KL n w)) = 1) → ∀ g : ∀ w : Pl E, UL n w → ℂ,
    ∃ (d : ℕ) (blk : Fin d → ι) (u : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)),
      (∀ c, Commute u (diagOp blk c)) ∧
      (∀ (k : ℕ) f, IsTest (KL n) K' f → (∀ i, ∀ w ∈ B, locOp (σ i w) (K' w) (f w) = locOp (σ i w) (K' w) (g w) ^ k) →
        ∑ i, ∏ᶠ w ∈ S, twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id =
          LinearMap.trace ℂ _ ((u ^ k * diagOp blk fun i => ∏ᶠ w ∈ S \ ↑B, twTr (σ i w).ρ (KL n w) (KL n w) (f w) LinearMap.id :
            EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d))) ∧
      ∀ i₀, (∀ w ∈ B, ∃ y, y ≠ 0 ∧ locOp (σ i₀ w) (K' w) (g w) y = y) → ∃ v, v ≠ 0 ∧ u v = v ∧ ∀ c, diagOp blk c v = c i₀ • v

end PositivityTheory.Rg.BcB.F.Eig

end
end

