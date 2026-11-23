module

public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.HarderNarasimhan.DegSupermodZ
public import Mathlib
public import Formalism.CorankShare.StatementFR

@[expose] public section

-- bundled from Formalism.HarderNarasimhan.DefsPl
section
open Module NumberField

noncomputable section

namespace Formalism.HN

def placePart {P ι : Type*} [Fintype P] [Fintype ι] (v : P) :
    Submodule ℝ (EuclideanSpace ℝ (P × ι × Fin 2)) :=
  ⨅ (p : P × ι × Fin 2) (_ : p.1 ≠ v), LinearMap.ker (EuclideanSpace.proj p : EuclideanSpace ℝ (P × ι × Fin 2) →L[ℝ] ℝ).toLinearMap

def PlaceSplit : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ N : Submodule (𝓞 K) V, N.FG →
      Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
        (⨆ v, Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set _) ⊓ placePart v) ∧
      ∀ v, Module.finrank ℝ
        (Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓
          placePart v : Submodule ℝ _) = 2 * rkK N

def GramBlock : Prop :=
  ∀ (P E E' ι : Type) [Fintype P] [DecidableEq P] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    (Ev : P → Submodule ℝ E) (Ev' : P → Submodule ℝ E') (T : E →ₗ[ℝ] E') (c : P → ℝ)
    (W : Submodule ℝ E) (u : ι → E),
    (∀ v w, v ≠ w → ∀ x ∈ Ev v, ∀ y ∈ Ev w, inner ℝ x y = 0) →
    (∀ v w, v ≠ w → ∀ x ∈ Ev' v, ∀ y ∈ Ev' w, inner ℝ x y = 0) →
    (∀ v, 0 ≤ c v) → (∀ v, ∀ x ∈ Ev v, T x ∈ Ev' v ∧ ‖T x‖ ≤ c v * ‖x‖) →
    W = (⨆ v, W ⊓ Ev v) → LinearIndependent ℝ u → Submodule.span ℝ (Set.range u) = W →
    (Matrix.gram ℝ (fun i => T (u i))).det ≤
        (∏ v, c v ^ (2 * Module.finrank ℝ (W ⊓ Ev v : Submodule ℝ E))) * (Matrix.gram ℝ u).det ∧
      ((∀ v, ∀ x ∈ Ev v, ∀ y ∈ Ev v, inner ℝ (T x) (T y) = c v ^ 2 * inner ℝ x y) →
        (Matrix.gram ℝ (fun i => T (u i))).det =
          (∏ v, c v ^ (2 * Module.finrank ℝ (W ⊓ Ev v : Submodule ℝ E))) * (Matrix.gram ℝ u).det)

end Formalism.HN
end
end

-- bundled from Formalism.HarderNarasimhan.QuotRealize
section
open Module NumberField

noncomputable section

namespace Formalism.HN

section Dual

variable {K V ι : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

def dualLat (A : Submodule (𝓞 K) V) : Submodule (𝓞 K) (Module.Dual K V) where
  carrier := {f | ∀ x ∈ A, f x ∈ Set.range (algebraMap (𝓞 K) K)}
  zero_mem' := fun x _ => ⟨0, by simp⟩
  add_mem' := by
    rintro f g hf hg x hx
    obtain ⟨a, ha⟩ := hf x hx
    obtain ⟨c, hc⟩ := hg x hx
    exact ⟨a + c, by simp [ha, hc]⟩
  smul_mem' := by
    rintro r f hf x hx
    obtain ⟨a, ha⟩ := hf x hx
    exact ⟨r * a, by simp [ha, Algebra.smul_def]⟩

def dualFrame (X : InfinitePlace K → Matrix ι ι ℂ) : InfinitePlace K → Matrix ι ι ℂ :=
  fun v => ((X v).transpose)⁻¹

end Dual

def Rerealize : Prop :=
  ∀ (K V ι V'' κ : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V''] [Module K V''] [Module (𝓞 K) V''] [IsScalarTower (𝓞 K) K V'']
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b'' : Basis κ K V'') (X'' : InfinitePlace K → Matrix κ κ ℂ) (ψ : V →ₗ[K] V''),
    (∀ v, IsUnit (X v).det) → (∀ v, IsUnit (X'' v).det) → Function.Injective ψ →
    (∀ v x, Formalism.HermitianLatticesTheory.normAt b'' X'' v (ψ x) = Formalism.HermitianLatticesTheory.normAt b X v x) →
    ∀ A : Submodule (𝓞 K) V, A.FG →
      ht b'' X'' (A.map (ψ.restrictScalars (𝓞 K))) = ht b X A ∧
      size b'' X'' (A.map (ψ.restrictScalars (𝓞 K))) = size b X A ∧
      slope (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K))) =
        slope (Formalism.HermitianLatticesTheory.realize b X) A ∧
      muMax (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K))) =
        muMax (Formalism.HermitianLatticesTheory.realize b X) A ∧
      muMin (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K))) =
        muMin (Formalism.HermitianLatticesTheory.realize b X) A ∧
      leastSize b'' X'' (A.map (ψ.restrictScalars (𝓞 K))) = leastSize b X A ∧
      largestSize b'' X'' (A.map (ψ.restrictScalars (𝓞 K))) = largestSize b X A

def QuotRealize : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ A S : Submodule (𝓞 K) V, A.FG → IsSat (Formalism.HermitianLatticesTheory.realize b X) A S →
      ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ)
        (b'' : Basis κ K (V ⧸ Submodule.span K (S : Set V)))
        (X'' : InfinitePlace K → Matrix κ κ ℂ),
        (∀ v, IsUnit (X'' v).det) ∧
        (∀ v (x : V), Formalism.HermitianLatticesTheory.normAt b'' X'' v ((Submodule.span K (S : Set V)).mkQ x) =
          ‖(Submodule.span ℂ ((fun y => (WithLp.equiv 2 (ι → ℂ)).symm
              (Formalism.HermitianLatticesTheory.fcoord b X v y)) '' (Submodule.span K (S : Set V) : Set V)))ᗮ.starProjection
            ((WithLp.equiv 2 (ι → ℂ)).symm (Formalism.HermitianLatticesTheory.fcoord b X v x))‖) ∧
        ∀ N : Submodule (𝓞 K) V, S ≤ N → N ≤ A →
          htQ b X N S = ht b'' X''
            (N.map ((Submodule.span K (S : Set V)).mkQ.restrictScalars (𝓞 K))) ∧
          sizeQ b X N S = size b'' X''
            (N.map ((Submodule.span K (S : Set V)).mkQ.restrictScalars (𝓞 K)))

def DualPl : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ A : Submodule (𝓞 K) V, A.FG → Submodule.span K (A : Set V) = ⊤ →
      (dualLat A).FG ∧ Submodule.span K (dualLat A : Set (Module.Dual K V)) = ⊤ ∧
      ht b.dualBasis (dualFrame X) (dualLat A) = (ht b X A)⁻¹ ∧
      size b.dualBasis (dualFrame X) (dualLat A) = (size b X A)⁻¹ ∧
      leastSize b.dualBasis (dualFrame X) (dualLat A) = (largestSize b X A)⁻¹ ∧
      largestSize b.dualBasis (dualFrame X) (dualLat A) = (leastSize b X A)⁻¹ ∧
      (dualLat (dualLat A)).comap ((Module.Dual.eval K V).restrictScalars (𝓞 K)) = A

end Formalism.HN
end
end

-- bundled from Formalism.HarderNarasimhan.StatementFrameF
section
open Module NumberField Formalism.CorankShareLayerCake.FR

noncomputable section

namespace Formalism.HN

def FrameLA1 : Prop :=
  ∀ (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (B : ∀ i, V i →ₗ[ℂ] H) (c : ι → ℝ) (Nτ : ∀ i, Submodule ℂ (V i)) (e η ε : ℝ),
    (∀ i, 0 < c i) →
    0 < ∑ i, finrank ℂ (V i) →
    (∑ i, hs2 (frK (c i) (B i) - LinearMap.id)) ≤ e * ∑ i, (finrank ℂ (V i) : ℝ) →
    0 ≤ e → e ≤ 1 / 4 → 0 ≤ η →
    (LinearMap.trace ℂ H (frQ c B ∘ₗ frQ c B)).re
      ≤ (1 + η) * (LinearMap.trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) →
    (∑ i, ((finrank ℂ (V i) : ℝ) - finrank ℂ (Nτ i))) ≤ ε * ∑ i, (finrank ℂ (V i) : ℝ) →
    (finrank ℂ (⨆ i, (Nτ i).map (B i))ᗮ : ℝ)
      ≤ (η + 4 * ε + 4 * Real.sqrt e) * (finrank ℂ H : ℝ)

def TheoremF : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ) (s u HH e η δ : ℝ),
    (∀ w, IsUnit (X' w).det) → (∀ i w, IsUnit (X i w).det) → (∀ i, IsUnit (Y i).det) →
    IsUnit Y'.det →
    cc.FG → Submodule.span K (cc : Set W) = ⊤ →
    (∀ i, (N i).FG) → (∀ i, Submodule.span K (N i : Set (V i)) = ⊤) →
    0 < ∑ i, Fintype.card (ι i) → (∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc) →
    (∀ i, B i ≠ 0 → htMap (b i) (X i) b' X' (B i) ≤ h i) →
    s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - h i) →
    0 ≤ u → (∀ i, muMaxDef (b i) (X i) (N i) - h i ≤ s + u) →
    s - muMinDef b' X' cc ≤ HH → 0 ≤ HH →
    0 ≤ δ → δ < 1 → (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ) →
    (∀ i (k : κ) (j : ι i),
      Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j) →
    (∀ i, 0 < γ i) →
    (∑ i, hs2 (frK (γ i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ) →
    0 ≤ e → e ≤ 1 / 4 →
    (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ γ (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
         frQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ) →
    0 ≤ η →
    s - Real.log (Fintype.card I : ℝ) -
        (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u) + (η + 4 * Real.sqrt e) * HH) ≤ muDef b' X' cc

def TheoremFSharp : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ) (s u HH e η δ : ℝ),
    (∀ w, IsUnit (X' w).det) → (∀ i w, IsUnit (X i w).det) → (∀ i, IsUnit (Y i).det) →
    IsUnit Y'.det →
    cc.FG → Submodule.span K (cc : Set W) = ⊤ →
    (∀ i, (N i).FG) → (∀ i, Submodule.span K (N i : Set (V i)) = ⊤) →
    0 < ∑ i, Fintype.card (ι i) → (∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc) →
    (∀ i, B i ≠ 0 → htMap (b i) (X i) b' X' (B i) ≤ h i) →
    s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - h i) →
    0 ≤ u → (∀ i, muMaxDef (b i) (X i) (N i) - h i ≤ s + u) →
    s - muMinDef b' X' cc ≤ HH → 0 ≤ HH →
    0 ≤ δ → δ < 1 → (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ) →
    (∀ i (k : κ) (j : ι i),
      Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j) →
    (∀ i, 0 < γ i) →
    (∑ i, hs2 (frK (γ i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ) →
    0 ≤ e → e ≤ 1 / 4 →
    (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ γ (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
         frQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ) →
    0 ≤ η →
    s - (1 - δ)⁻¹ * (4 * u * Real.log (1 + HH / u) + (η + 4 * Real.sqrt e) * HH) ≤ muDef b' X' cc

end Formalism.HN
end
end

-- bundled from Formalism.HarderNarasimhan.StatementMod
section
open Module NumberField

noncomputable section

namespace Formalism.HN

def IdealScale : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K), I ≠ 0 →
    ∀ M : Submodule (𝓞 K) V, M.FG → M ≠ ⊥ →
      (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M).FG ∧
      muDef b X (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M) =
        muDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) ∧
      muMaxDef b X (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M) =
        muMaxDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) ∧
      muMinDef b X (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M) =
        muMinDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ)

def IndexMu : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ M N : Submodule (𝓞 K) V, M.FG → N ≤ M → N ≠ ⊥ → rkK N = rkK M →
      muDef b X N = muDef b X M -
        2 * Real.log (N.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) /
          ((Module.finrank ℚ K : ℝ) * (rkK M : ℝ)) ∧
      muMaxDef b X N ≤ muMaxDef b X M

end Formalism.HN
end
end

