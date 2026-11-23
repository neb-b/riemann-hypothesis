module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0004
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0009
public import Formalism.PeriodIntegrals.Bundle0002
public import Formalism.PeriodIntegrals.Bundle0001
public import Formalism.PeriodIntegrals.UpqRep

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.SelfDualOfDiff
section
noncomputable section
open NumberField

namespace PI.KerIso

def SplitOfJacobi : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) (d p : ℕ) (s : K),
    d % 8 = 7 → s * s = -(d : K) → cj (algebraMap K E s) = -algebraMap K E s → p.Prime →
    (p = 2 ∨ jacobiSym (-(d : ℤ)) p = 1) → SplitsAt K cj p

end PI.KerIso
end
end

-- bundled from Formalism.PeriodIntegrals.SigmaStarEx
section
open Classical

namespace PI

def SigmaStarEx : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 →
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
      ∀ ω ∈ lat2 w₁ w₂, ∀ z, U1 (lat2 w₁ w₂) ω G z = (if ω / 2 ∈ lat2 w₁ w₂ then 1 else -1) * G z

end PI
end

-- bundled from Formalism.PeriodIntegrals.SigmaStarUniq
section
open Classical

namespace PI

def SigmaStarUniq : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 → ∀ G G' : ℂ → ℂ,
    (Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
      ∀ ω ∈ lat2 w₁ w₂, ∀ z, U1 (lat2 w₁ w₂) ω G z = (if ω / 2 ∈ lat2 w₁ w₂ then 1 else -1) * G z) →
    (Differentiable ℂ G' ∧ deriv G' 0 = 1 ∧ (∀ z, G' (-z) = -G' z) ∧
      ∀ ω ∈ lat2 w₁ w₂, ∀ z, U1 (lat2 w₁ w₂) ω G' z = (if ω / 2 ∈ lat2 w₁ w₂ then 1 else -1) * G' z) →
    G = G'

end PI
end

-- bundled from Formalism.PeriodIntegrals.SwSand
section
noncomputable section

open Matrix MeasureTheory Filter Topology Classical
open scoped ENNReal NNReal

namespace PI.SwSand

open PI.SwBig

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

abbrev Mt (k r : ℕ) := Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ

def realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Fin m × Fin m × Bool → ℝ :=
  fun p => if p.2.2 then (X p.1 p.2.1).im else (X p.1 p.2.1).re

def unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ⟨x (i, j, false), x (i, j, true)⟩

def lieOf {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ S}

def lieE {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Submodule ℝ (EuclideanSpace ℝ (Fin m × Fin m × Bool)) :=
  Submodule.span ℝ ((fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf S)

variable {k r : ℕ}

def dg (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℕ :=
  if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k

def Fil (p : ℕ) (X : Mat k r) : Prop := ∀ i j, dg k r j < dg k r i + p → X i j = 0

theorem Fil.add {p : ℕ} {X Y : Mat k r} (hX : Fil p X) (hY : Fil p Y) : Fil p (X + Y) := by
  unfold PI.SwSand.Fil at hX hY ⊢
  intro i j h
  rw [Matrix.add_apply, hX i j h, hY i j h, add_zero]

theorem Fil.smul {p : ℕ} {X : Mat k r} (c : ℂ) (hX : Fil p X) : Fil p (c • X) := by
  unfold PI.SwSand.Fil at hX ⊢
  intro i j h
  rw [Matrix.smul_apply, hX i j h, smul_zero]

theorem Fil.zero (p : ℕ) : Fil p (0 : Mat k r) := by
  unfold PI.SwSand.Fil
  intro i j _
  exact Matrix.zero_apply i j

def adjH (X : Mat k r) : Mat k r := Hpk k r * Xᴴ * Hpk k r

theorem adjH_add (X Y : Mat k r) : adjH (X + Y) = adjH X + adjH Y := by
  simp only [adjH, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem adjH_smul (c : ℂ) (X : Mat k r) : adjH (c • X) = star c • adjH X := by
  simp only [adjH, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

def lieN (k r : ℕ) : Set (Mat k r) := {X | Fil 1 X ∧ adjH X + X = 0}

theorem lieN_smul {X : Mat k r} (hX : X ∈ lieN k r) (t : ℝ) : ((t : ℂ) • X) ∈ lieN k r := by
  obtain ⟨h1, h2⟩ := hX
  show Fil 1 ((t : ℂ) • X) ∧ adjH ((t : ℂ) • X) + (t : ℂ) • X = 0
  refine ⟨h1.smul _, ?_⟩
  rw [adjH_smul, Complex.star_def, Complex.conj_ofReal, ← smul_add, h2, smul_zero]

theorem lieN_add {X Y : Mat k r} (hX : X ∈ lieN k r) (hY : Y ∈ lieN k r) : X + Y ∈ lieN k r := by
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  show Fil 1 (X + Y) ∧ adjH (X + Y) + (X + Y) = 0
  refine ⟨hX1.add hY1, ?_⟩
  rw [adjH_add, add_add_add_comm, hX2, hY2, add_zero]

theorem zero_mem_lieN : (0 : Mat k r) ∈ lieN k r := by
  show Fil 1 (0 : PI.SwBig.Mat k r) ∧ adjH (0 : PI.SwBig.Mat k r) + 0 = 0
  exact ⟨PI.SwSand.Fil.zero 1, by simp [adjH]⟩

def lieNS (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := lieN k r
  add_mem' := lieN_add
  zero_mem' := zero_mem_lieN
  smul_mem' := fun c X hX => by
    show c • X ∈ lieN k r
    rw [← Complex.coe_smul]; exact lieN_smul hX c

def RL : Mat k r →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) where
  toFun X := (WithLp.equiv 2 _).symm (realifyFun X)
  map_add' X Y := by
    ext p
    rcases p with ⟨i, j, b⟩
    cases b <;> simp [realifyFun]
  map_smul' c X := by
    ext p
    rcases p with ⟨i, j, b⟩
    cases b <;> simp [realifyFun]

def expBall (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (ρ : ℝ) : Set (Mt k r) :=
  (fun x : lieE S =>
      fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) '' Metric.ball 0 ρ

def gBall (k r : ℕ) (ρ : ℝ) : Set (Mt k r) := expBall (k := k) (r := r) (UH (Hpk k r)) ρ

def rhoS (k r : ℕ) (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (x : Mt k r) : ℝ≥0∞ :=
  ⨅ (Y : lieE S)
    (_ : (fun i j => NormedSpace.exp (unrealify (Y : EuclideanSpace ℝ _)) i j : Mt k r) = x),
    (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)

def Qf (k r : ℕ) (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r) : ℝ≥0∞ :=
  rhoS k r (Nset k r) n ^ 2 + ENNReal.ofReal (2 * ∑ a, ‖c a - 1‖ ^ 2) + rhoS k r (UWb k r) m ^ 2 +
    rhoS k r (Nset k r) n' ^ 2

def Psi (k r : ℕ) (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r) : Mt k r :=
  fun i j => (w0B k r * (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹)) i j

def Sandwich : Prop :=
  ∀ (k r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
    ∀ (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r), Matrix.of n ∈ Nset k r → Matrix.of m ∈ UWb k r →
      Matrix.of n' ∈ Nset k r →
      (Psi k r n c m n' ∈ gBall k r ρ → Qf k r n c m n' < ENNReal.ofReal (((1 + ε) * ρ) ^ 2)) ∧
      (Qf k r n c m n' < ENNReal.ofReal (((1 - ε) * ρ) ^ 2) → Psi k r n c m n' ∈ gBall k r ρ)

def Mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

def uH (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | adjH X + X = 0}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_ofPred_eq] at *
    rw [adjH_add, show adjH X + adjH Y + (X + Y) = (adjH X + X) + (adjH Y + Y) by abel, hX, hY, add_zero]
  zero_mem' := by simp [adjH]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_ofPred_eq] at *
    rw [← Complex.coe_smul, adjH_smul, Complex.star_def, Complex.conj_ofReal, ← smul_add, hX, smul_zero]

def uWb (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | adjH X + X = 0 ∧ ∀ i j, ¬ (Mid k r i ∧ Mid k r j) → X i j = 0}
  add_mem' := by
    intro X Y hX hY
    refine ⟨(uH k r).add_mem hX.1 hY.1, fun i j h => ?_⟩
    simp [hX.2 i j h, hY.2 i j h]
  zero_mem' := ⟨(uH k r).zero_mem, fun i j _ => rfl⟩
  smul_mem' := by
    intro c X hX
    refine ⟨(uH k r).smul_mem c hX.1, fun i j h => ?_⟩
    simp [hX.2 i j h]

def Vs (k r : ℕ) : Submodule ℝ (Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) :=
  (lieNS k r).prod ((⊤ : Submodule ℝ (Fin r → ℂ)).prod ((uWb k r).prod (lieNS k r)))

def LieG : Prop := ∀ k r : ℕ, lieE (UH (Hpk k r)) = (uH k r).map RL

def LieWb : Prop := ∀ k r : ℕ, (∀ Z ∈ uWb k r, NormedSpace.exp Z ∈ UWb k r) ∧
  lieE (UWb k r) = (uWb k r).map RL

def LIso : Prop := ∀ k r : ℕ, (∀ v ∈ Vs k r, Lm k r v ∈ uH k r) ∧ (∀ Y ∈ uH k r, ∃ v ∈ Vs k r, Lm k r v = Y) ∧
  ∀ v ∈ Vs k r, ‖RL (Lm k r v)‖ ^ 2 = ‖RL v.1‖ ^ 2 + 2 * ∑ a, ‖v.2.1 a‖ ^ 2 + ‖RL v.2.2.1‖ ^ 2 + ‖RL v.2.2.2‖ ^ 2

def LieEN : Prop := ∀ k r : ℕ, lieE (Nset k r) = (lieNS k r).map RL

def ExpN : Prop := ∀ (k r : ℕ) (X : Mat k r), X ∈ lieN k r → NormedSpace.exp X ∈ Nset k r

def SandwichOf : Prop :=
  LieG → LieWb → GaussUniq → PhiForm → BigCellG → PhiDeriv → LIso → LongWeylElementSquare → LieEN → ExpN → Sandwich

end PI.SwSand
end
end

-- bundled from Formalism.PeriodIntegrals.SymDist
section
open Matrix

noncomputable section

namespace PI

def symD {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : ℝ :=
  sInf {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
    ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X ∧
    t = Real.sqrt (Formalism.REAL.hs X)}

def SymDist : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g k : Formalism.REAL.UJ ε), symD ε (g * k) ≤ symD ε g + symD ε k

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryApproxFin
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFin

def UnitaryApproxFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ e, σ (σ e) = e) → (∃ θ, σ θ ≠ θ) → PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J → IsUnit J.det →
    ∀ (T : Finset (HeightOneSpectrum (𝓞 F)))
      (g : (v : HeightOneSpectrum (𝓞 F)) → GL n (E ⊗[F] v.adicCompletion F)),
      (∀ v ∈ T, g v ∈ PI.UnitaryApproxDefs.UPts σ J (v.adicCompletion F)) → ∀ D : 𝓞 F, D ≠ 0 →
    ∃ γ ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J, ∀ v ∈ T, ∀ i j,
      ∃ s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (v.adicCompletion F) (PI.UnitaryApproxDefs.intOE E) (v.adicCompletionIntegers F).toSubring,
        ((g v : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) i j -
            PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) ((γ : Matrix n n E) i j) =
          PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (D : F)) * s

end PI.UnitaryApproxFin
end
end

-- bundled from Formalism.PeriodIntegrals.W2pair
section
noncomputable section

namespace PI

def WfEndDefs.W2pair (p : ℕ) [Fact p.Prime] : Set (ℂ_[p] × ℂ_[p]) :=
  closure (Subring.closure {x : ℂ_[p] × ℂ_[p] | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)} :
    Set (ℂ_[p] × ℂ_[p]))

def mulBy {p : ℕ} [Fact p.Prime] {σ : Type*} (l ex : PowerSeries ℂ_[p]) (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex

def PairW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ α ∈ WfEndDefs.W2pair p, α.1 ∈ Wp p

def WfEnd : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex : PowerSeries ℂ_[p]),
    W.a₁ ∈ Wp p → W.a₂ ∈ Wp p → W.a₃ ∈ Wp p → W.a₄ ∈ Wp p → W.a₆ ∈ Wp p → AddIntG.IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (AddIntG.flog W wq) = PowerSeries.X →
    ∀ c : ℂ_[p], InWf c →
      IntegralMv (mulBy (AddIntG.flog W wq) ex c (MvPowerSeries.X ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralW (mulBy (AddIntG.flog W wq) ex c (MvPowerSeries.X ()) : MvPowerSeries Unit ℂ_[p])

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.WeylForK
section
noncomputable section

namespace PI

open PI.UpqRep

def nPl {N : ℕ} (ε : Fin N → Bool) : ℕ := (Finset.univ.filter (fun a => ε a = true)).card

def nMi {N : ℕ} (ε : Fin N → Bool) : ℕ := (Finset.univ.filter (fun a => ε a = false)).card

def WeylForK : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Kset ε) σ → IsKTypeOf ε σ Λ S →
    (Module.finrank ℂ S : ℝ) =
      (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
        ((Λ + rhoC ε) a - (Λ + rhoC ε) b)) /
      ((∏ i ∈ Finset.range (nPl ε), (i.factorial : ℝ)) * ∏ i ∈ Finset.range (nMi ε), (i.factorial : ℝ))

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.WfRing
section
namespace PI

def WfRing : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g : MvPowerSeries σ ℂ_[p]), CoefWf f → CoefWf g →
    CoefWf (f + g) ∧ CoefWf (f - g) ∧ CoefWf (f * g) ∧ ∀ c : ℂ_[p], InWf c → CoefWf (MvPowerSeries.C c * f)

end PI
end

-- bundled from Formalism.PeriodIntegrals.WfSubst
section
namespace PI

def SubstSub : Prop :=
  ∀ (A : Type) [CommRing A] (S : Subring A) (σ : Type) (f : PowerSeries A) (a : MvPowerSeries σ A),
    (∀ n, PowerSeries.coeff n f ∈ S) → (∀ n, MvPowerSeries.coeff n a ∈ S) →
    MvPowerSeries.constantCoeff a = 0 → ∀ n, MvPowerSeries.coeff n (PowerSeries.subst a f) ∈ S

def WfSubst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
    CoefWf f → CoefWf a → MvPowerSeries.constantCoeff a = 0 → CoefWf (PowerSeries.subst a f)

end PI
end

