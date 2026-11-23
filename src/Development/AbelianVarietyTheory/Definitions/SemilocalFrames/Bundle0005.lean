module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
section
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
namespace GlobalTheory.DegAsm
variable {K V W : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
  {H : HermSpace K V} {r : ℕ}

def SameGr (F G : FlagD H r) : Prop := ∀ a : Fin (r + 1), G.e a - F.e a ∈ F.Xa a.val

def Adapt (F F' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) : Prop := N.𝔡 = 𝔡 ∧ SameGr F N.F ∧ SameGr F' N.F'

def omI (F F' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (Λ : Submodule (𝓞 K) V) : ℝ :=
  sInf ((fun N : NF H r => N.om Λ) '' {N | Adapt F F' 𝔡 N})

def pairM (F F' : FlagD H r) (j : ℕ) : Fin (r + 1) → Fin (r + 1) → K :=
  fun a b => if a.val < j ∧ b.val < j then H.B (F.e a) (F'.e b) else 0

def lab (F F' : FlagD H r) (j : ℕ) : ℕ → K := fun l => if h : l ≤ j ∧ l ≤ r + 1 then Dl F F' l h.2 else 0

def IsEmb (F : FlagD H r) (HW : HermSpace K W) (e : W →ₗ[K] V) : Prop :=
  (∀ x y, H.B (e x) (e y) = HW.B x y) ∧
    ∀ v : V, (∀ a : Fin (r + 1), H.B (F.e a) v = 0) ↔ v ∈ LinearMap.range e ⊔ F.X

def lat0 (F : FlagD H r) (e : W →ₗ[K] V) (Λ : Submodule (𝓞 K) V) : Submodule (𝓞 K) W :=
  (Λ ⊔ rs (𝓞 K) F.X).comap (e.restrictScalars (𝓞 K))

def datOf (F F' : FlagD H r) (e : W →ₗ[K] V) (g : ℕ) (Λ : Submodule (𝓞 K) V) :
    Submodule (𝓞 K) W × Submodule (𝓞 K) (W × W) :=
  ((flagPairDefinitePartLattice F' F Λ ⊔ rs (𝓞 K) F.X).comap (e.restrictScalars (𝓞 K)),
    (iotaGraph F F' Λ (g : 𝓞 K) ⊔ (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X)).comap ((e.prodMap e).restrictScalars (𝓞 K)))

def IsH (F F' : FlagD H r) (e : W →ₗ[K] V) (γ : V ≃ₗ[K] V) (h : W ≃ₗ[K] W) : Prop :=
  ∀ w : W, ∃ y ∈ wSp F F', y - e (h w) ∈ F.X ∧ y - γ (e w) ∈ F'.X

def FrEqv (F : FlagD H r) (Λ : Submodule (𝓞 K) V) (G G' : FlagD H r) : Prop :=
  ∃ n : V ≃ₗ[K] V, F.InN (n : V →ₗ[K] V) ∧ n • Λ = Λ ∧ ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val

def datBd (K : Type) [Field K] [NumberField K] [StarRing K] (k r : ℕ) (Del Db NT x : ℝ) : ℝ :=
  (Del / x) ^ ((k : ℝ) / 2) *
    (8 ^ (r + 1) * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) ^ 2 * Del ^ (3 * cf K + 6) * NT ^ 2 * (Db * Del * NT) ^ (10000 * (r + 1) ^ 3))

theorem adapt_self (N : NF H r) : Adapt N.F N.F' N.𝔡 N :=
  ⟨rfl, fun a => by simp, fun a => by simp⟩
end GlobalTheory.DegAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PairBdNonneg
section
noncomputable section
open NumberField GlobalTheory.DegCnt
namespace GlobalTheory.DegAsm

def pairBd (K : Type) [Field K] [NumberField K] (k g j T x x' : ℕ) : ℝ :=
  let f : ℕ := Formalism.HermitianLatticesTheory.fDeg K
  let Mb : ℝ := (20 * (f : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * (f : ℝ) * (6 + cf K))
  let D₀ : ℝ := (T : ℝ) ^ (2 * f)
  let Y : ℝ := (x : ℝ) * x' * D₀ ^ 2
  ((x : ℝ) * x') ^ ((k : ℝ) / 2) * Y ^ (6 * (j : ℝ) + 10 + 4 * cf K) *
    (1 + Mb * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ f *
        (∑ s ∈ Finset.Ico 1 k, ((32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * Y ^ 7) ^ s) +
      ((2 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * D₀ * x * x') ^ k)

open NumberField in
private lemma vInv_nonneg' (K : Type) [Field K] [NumberField K] :
    0 ≤ _root_.Formalism.HermitianLatticesTheory.vInv K := by
  unfold _root_.Formalism.HermitianLatticesTheory.vInv
  positivity


open NumberField in
theorem _root_.GlobalTheory.DegAsm.pairBd_nonneg (K : Type) [Field K] [NumberField K]
    (k g j T x x' : ℕ) : 0 ≤ _root_.GlobalTheory.DegAsm.pairBd K k g j T x x' := by
  have hv := vInv_nonneg' K
  unfold _root_.GlobalTheory.DegAsm.pairBd
  dsimp only
  have hMb : 0 ≤ (20 * ((_root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) * (2 * _root_.Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^
      (2 * ((_root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) * (6 + _root_.GlobalTheory.DegCnt.cf K)) :=
    Real.rpow_nonneg (by positivity) _
  have hY : 0 ≤ (x : ℝ) * x' * ((T : ℝ) ^ (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K)) ^ 2 := by positivity
  have hxx : 0 ≤ (x : ℝ) * x' := by positivity
  refine mul_nonneg (mul_nonneg (Real.rpow_nonneg hxx _) (Real.rpow_nonneg hY _)) ?_
  refine add_nonneg (add_nonneg zero_le_one (mul_nonneg (mul_nonneg hMb (by positivity)) ?_))
    (by positivity)
  exact Finset.sum_nonneg fun s _ => by positivity

end GlobalTheory.DegAsm
end
end

