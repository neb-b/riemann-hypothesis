module

public import Formalism.PeriodIntegrals.Bundle0004
public import Mathlib
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
public import Formalism.PeriodIntegrals.Bundle0007
public import Formalism.PeriodIntegrals.Bundle0005
public import Formalism.PeriodIntegrals.Bundle0001
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.PeriodIntegrals.Bundle0002
public import Formalism.PeriodIntegrals.Bundle0006

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.AreaLat
section
open Classical

namespace PI

def AreaLat : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 →
    area (lat2 w₁ w₂) = |((starRingEnd ℂ) w₁ * w₂).im| ∧
    ∀ a ∈ lat2 w₁ w₂, ∀ b ∈ lat2 w₁ w₂, ∃ n : ℤ, ((starRingEnd ℂ) a * b).im = n * ((starRingEnd ℂ) w₁ * w₂).im

end PI
end

-- bundled from Formalism.PeriodIntegrals.BallQuotLen
section
namespace PI

open Formalism.MainNotions.Gaps.EtaleWeightGaps

def BallQuotLen : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [IsReduced A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A]
    (ϖ : O), Irreducible ϖ → Module.Finite O ↥(As O A) → ∀ [∀ ζ : Pts O A, IsDVRAt ζ],
    ∀ (V : Type) [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower K A V] [Module O V]
      [IsScalarTower O A V] (e : V), IsGen (A := A) e → ∀ (c : Pts O A → ℤ) (m : Pts O A → ℕ),
      Module.length O (↥(ballO ϖ e (fun ζ => c ζ + m ζ)) ⧸
          (ballO ϖ e c).comap (ballO ϖ e (fun ζ => c ζ + m ζ)).subtype) =
        ((∑ᶠ ζ : Pts O A, m ζ * fdeg ζ : ℕ) : ℕ∞)

end PI
end

-- bundled from Formalism.PeriodIntegrals.DiscrNe
section
open Classical

namespace PI

def DiscrNe : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 → discr (lat2 w₁ w₂) ≠ 0

end PI
end

-- bundled from Formalism.PeriodIntegrals.EfRankSum
section
namespace PI

open Formalism.MainNotions.Gaps.EtaleWeightGaps

def EfRankSum : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [IsReduced A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A]
    (ϖ : O), Irreducible ϖ → Module.Finite O ↥(As O A) → ∀ [∀ ζ : Pts O A, IsDVRAt ζ],
    Finite (Pts O A) ∧ (∑ᶠ ζ : Pts O A, ep ϖ ζ * fdeg ζ) = Module.finrank K A

end PI
end

-- bundled from Formalism.PeriodIntegrals.FinOrdAd
section
noncomputable section

namespace PI

open NumberField IsDedekindDomain TensorProduct Matrix ComplexOrder

section UnitaryGroups

variable {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι]

def cT (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

def IsHerm (σ : A →+* A) (J : Matrix ι ι A) : Prop := cT σ J = J

def hform (σ : A →+* A) (J : Matrix ι ι A) (x y : ι → A) : A :=
  ∑ i, ∑ j, σ (x i) * J i j * y j

theorem cT_mul (σ : A →+* A) {m p q : Type} [Fintype p] (M : Matrix m p A) (N : Matrix p q A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one (σ : A →+* A) : cT σ (1 : Matrix ι ι A) = 1 := by
  simp [cT]

def UJ (σ : A →+* A) (J : Matrix ι ι A) : Subgroup (GL ι A) where
  carrier := {g | cT σ (g : Matrix ι ι A) * J * (g : Matrix ι ι A) = J}
  one_mem' := by simp [cT_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc cT σ ((a : Matrix ι ι A) * (b : Matrix ι ι A)) * J * ((a : Matrix ι ι A) * (b : Matrix ι ι A))
        = cT σ (b : Matrix ι ι A) * (cT σ (a : Matrix ι ι A) * J * (a : Matrix ι ι A)) *
            (b : Matrix ι ι A) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc cT σ ((g⁻¹ : GL ι A) : Matrix ι ι A) * J * ((g⁻¹ : GL ι A) : Matrix ι ι A)
        = cT σ ((g⁻¹ : GL ι A) : Matrix ι ι A) * (cT σ (g : Matrix ι ι A) * J * (g : Matrix ι ι A))
            * ((g⁻¹ : GL ι A) : Matrix ι ι A) := by rw [hg]
      _ = cT σ ((g : Matrix ι ι A) * ((g⁻¹ : GL ι A) : Matrix ι ι A)) * J
            * ((g : Matrix ι ι A) * ((g⁻¹ : GL ι A) : Matrix ι ι A)) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]

def bc {B : Type} [CommRing B] (φ : A →+* B) : GL ι A →* GL ι B :=
  Units.map (RingHom.mapMatrix φ).toMonoidHom

end UnitaryGroups

section Points

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {ι : Type} [Fintype ι] [DecidableEq ι]

def sigR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →+* E ⊗[F] R :=
  (Algebra.TensorProduct.map σ (AlgHom.id F R)).toRingHom

def inclE (R : Type) [CommRing R] [Algebra F R] : E →+* E ⊗[F] R :=
  Algebra.TensorProduct.includeLeftRingHom

def UPts (σ : E →ₐ[F] E) (J : Matrix ι ι E) (R : Type) [CommRing R] [Algebra F R] :
    Subgroup (GL ι (E ⊗[F] R)) := UJ (sigR σ R) (J.map (inclE (F := F) R))

def IsDef (σ : E →ₐ[F] E) (J : Matrix ι ι E) : Prop :=
  ∀ ι' : F →+* ℝ,
    (∀ x : ι → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x ∧ 0 < ι' a) ∨
    (∀ x : ι → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x ∧ ι' a < 0)

@[reducible] def tensTop (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (E ⊗[F] R) :=
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  moduleTopology R (E ⊗[F] R)

end Points

def FinOrdAd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  (∀ φ : F →+* ℂ, ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ)) →
  ∀ (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E), IsHerm (σ : E →+* E) J → IsDef σ J →
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  ∀ U : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    U ≤ UPts σ J (FiniteAdeleRing (𝓞 F) F) →
    IsCompact (U : Set (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) →
  ∀ y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F),
  ∀ γ ∈ UJ (σ : E →+* E) J,
    bc (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) γ ∈ U.map (MulAut.conj y).toMonoidHom →
    IsOfFinOrder γ

def DefPosDef : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  (∀ φ : F →+* ℂ, ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ)) →
  ∀ (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E), 0 < k → IsHerm (σ : E →+* E) J → IsDef σ J →
    (∀ (φ : E →+* ℂ) (x : E), φ (σ x) = (starRingEnd ℂ) (φ x)) ∧
    (∀ φ : E →+* ℂ, (J.map φ).PosDef ∨ (-(J.map φ)).PosDef)

def TensCpctDen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  ∀ C : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F), IsCompact C →
    ∃ N : ℕ, 0 < N ∧ ∀ e : E, inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) e ∈ C → IsIntegral ℤ ((N : E) * e)

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.HCMult
section
noncomputable section

namespace PI

open PI.UpqRep

def HCMult : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S →
      FiniteDimensional ℂ (eqImg (fun k : KG ε => σ (toMK k)) S)

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.IdealLattice
section
open NumberField

namespace PI

def IdealLattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ), Module.finrank ℚ K = 2 → IsEmpty (K →+* ℝ) →
    ∀ (cc : Ideal (𝓞 K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 →
      (∃ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 ∧
        AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ (c : K)} = AddSubgroup.closure {w₁, w₂}) ∧
      area (AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ (c : K)}) =
        ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)| / 2

end PI
end

-- bundled from Formalism.PeriodIntegrals.InvSerSub
section
namespace PI

def InvSerSub : Prop :=
  ∀ (K : Type) [Field K] (S : Subring K) (l ex : PowerSeries K),
    (∀ n, PowerSeries.coeff n l ∈ S) → PowerSeries.constantCoeff l = 0 → PowerSeries.coeff 1 l = 1 →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X → ∀ n, PowerSeries.coeff n ex ∈ S

def WfLogL : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    W.a₁ ∈ Wp p → W.a₂ ∈ Wp p → W.a₃ ∈ Wp p → W.a₄ ∈ Wp p → W.a₆ ∈ Wp p → AddIntG.IsWq W wq →
    CoefWf (AddIntG.flog W wq)

def WfLog : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex : PowerSeries ℂ_[p]),
    W.a₁ ∈ Wp p → W.a₂ ∈ Wp p → W.a₃ ∈ Wp p → W.a₄ ∈ Wp p → W.a₆ ∈ Wp p → AddIntG.IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (AddIntG.flog W wq) = PowerSeries.X →
    CoefWf (AddIntG.flog W wq) ∧ CoefWf ex

end PI
end

-- bundled from Formalism.PeriodIntegrals.IsLowUnitH
section
open MeasureTheory Matrix Finset Topology
open scoped InnerProductSpace ContDiff ComplexOrder

noncomputable section

namespace PI.UpqRep

def rdM {m : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (X : Matrix (Fin m) (Fin m) ℂ)
    (f : Matrix (Fin m) (Fin m) ℂ → V) : Matrix (Fin m) (Fin m) ℂ → V :=
  fun g => deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

section KF

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsKFin {n : ℕ} (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧ IsKStableOn ε σ S

end KF

def thetaJ {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  -(Jm ε * Xᴴ * Jm ε)

def reJ {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (X + thetaJ ε X)

def imJ {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (-(Complex.I / 2)) • (X - thetaJ ε X)

def rdC {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => rdM (reJ ε X) f g + Complex.I * rdM (imJ ε X) f g

def rdCWord {n : ℕ} (ε : Fin n → Bool) :
    List (Matrix (Fin n) (Fin n) ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ) → Matrix (Fin n) (Fin n) ℂ → ℂ
  | [], f => f
  | X :: w, f => rdC ε X (rdCWord ε w f)

def gelfandOp {n : ℕ} (ε : Fin n → Bool) (k : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => ∑ a : Fin (k + 1) → Fin n,
    rdCWord ε (List.ofFn fun i : Fin (k + 1) => Matrix.single (a i) (a (finRotate (k + 1) i)) (1 : ℂ)) f g

def IsEquiv {n : ℕ} {H' H : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ε : Fin n → Bool) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ U : H' ≃ₗᵢ[ℂ] H, ∀ g ∈ UJset ε, ∀ v : H', U (σ' g v) = σ g (U v)

section Eig

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def Eig (ε : Fin n → Bool) (c : ℕ → ℂ) (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ x y : H, ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
    (∀ g ∈ UJset ε, F g = ⟪x, Ψ g y⟫_ℂ) ∧ ∀ (k : ℕ), ∀ g ∈ UJset ε, gelfandOp ε k F g = c k * F g

end Eig

def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩

def wI (k r : ℕ) (j : Fin (k + 1)) : Fin (2 * r + k + 1) := ⟨r + j.val, by omega⟩

def esI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩

def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ := Pi.single i 1

def herm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star w ⬝ᵥ (H *ᵥ v)

def inWb (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → v i = 0

def Tz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : ℝ := -(herm (Hpk k r) z z).re

def UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ z = z}

def blockW (k r : ℕ) (h : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  fun i j =>
    if hi : r ≤ i.val ∧ i.val < r + k then
      (if hj : r ≤ j.val ∧ j.val < r + k then h ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ else 0)
    else (if i = j then 1 else 0)

def IsFrameW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
      g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ (((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) = z

section Second

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsHCTypeW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ g, IsFrameW k r z g ∧ IsHCTypeU k u (fun h => π (g * blockW k r h * g⁻¹))

def InLieHpk (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  Xᴴ * Hpk k r + Hpk k r * X = 0

def dsig (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : H) : H :=
  deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) 0

def dsigW (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) :
    List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) → H → H
  | [], v => v
  | X :: w, v => dsig σ X (dsigW σ w v)

def IsLowUnitH (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  ∃ P, IsCayleyU k r ε P ∧ IsLowUnit ε lam (fun g => σ (P⁻¹ * g * P)) w

end Second

end PI.UpqRep

end
end

-- bundled from Formalism.PeriodIntegrals.KFinSmooth
section
noncomputable section

namespace PI

open PI.UpqRep

def KFinSmooth : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDSHpk k r ε lam σ →
    ∀ v : H, IsKFinHpk (k := k) (r := r) σ v → v ∈ smoothVecs (k := k) (r := r) σ

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.MinkowskiQ
section
namespace PI

def MinkowskiBoundQ : Prop :=
  ∀ (N : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℚ)), Finite G →
    Nat.card G ∣ minkowskiM N

end PI
end

-- bundled from Formalism.PeriodIntegrals.QuotSetU
section
open MeasureTheory Matrix

noncomputable section

namespace PI

namespace QuotSetU

def herm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star w ⬝ᵥ (H *ᵥ v)

def UH {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) : Set (Matrix ι ι ℂ) :=
  {g | gᴴ * H * g = H}

def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩

def esI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩

def Hpk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if i.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if r ≤ i.val ∧ i.val ≤ r + k ∧ i = j then (if i.val = r + k then -1 else 1)
  else 0

def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ := Pi.single i 1

def inWb (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → v i = 0

def Tz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : ℝ := -(herm (Hpk k r) z z).re

def Nset (k r : ℕ) : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      g i (eI k r a) = if i = eI k r a then 1 else 0) ∧
    (∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      g i j = if i = j then 1 else 0)}

def UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ z = z}

def Sset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {s | ∃ h ∈ UWset k r z, ∃ m ∈ Nset k r, s = h * m}

end QuotSetU


open QuotSetU in
def QuotSetU : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    IsMatGroup (UH (Hpk k r)) ∧ IsMatGroup (Sset k r z) ∧ Sset k r z ⊆ UH (Hpk k r) ∧
    (∀ μG : Measure (MtM (2 * r + k + 1)), IsHaarOnM (UH (Hpk k r)) μG → IsRightInvM (UH (Hpk k r)) μG) ∧
    (∀ μS : Measure (MtM (2 * r + k + 1)), IsHaarOnM (Sset k r z) μS → IsRightInvM (Sset k r z) μS)

end PI

end
end

