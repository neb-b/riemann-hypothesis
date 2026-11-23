module

public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.HasSecondLogDeriv

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.ChordSecondLogDeriv
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

def IsogenyReduce : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (s2 : K) (ι : Type) [Fintype ι]
    (c : ι → K) (al : K), al ≠ 0 →
    (IsogenyFormula e s2 c al ↔
      mvExp ((2 * ((Fintype.card ι : K) + 1)) • lam e s2 - (2 : K) • PowerSeries.rescale al (lam e s2))
        = ∏ P, wpShift e (c P))

def IsogenyIff : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (s2 : K) (ι : Type) [Fintype ι]
    (neg : ι → ι) (c : ι → K) (w : ι → PowerSeries K) (al : K), al ≠ 0 →
    IsEndoZ e neg c w al →
    (IsogenyFormula e s2 c al ↔ (al ^ 2 - ((Fintype.card ι : K) + 1)) * s2 = ∑ P, c P)

def IsogenyIffBar : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (s2 : K) (ι : Type) [Fintype ι]
    (neg : ι → ι) (xP : ι → K) (c0 : K) (w : ι → PowerSeries K) (al albar : K), al ≠ 0 →
    al * albar = (Fintype.card ι : K) + 1 →
    IsEndoZ e neg (fun P => xP P + c0) w al →
    (IsogenyFormula e s2 (fun P => xP P + c0) al ↔
      al * (al - albar) * s2 = ∑ P, (xP P + c0))

end Formalism.L2.Th1.C
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.IntBinomScalar
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

def MvExpLaws : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (σ : Type),
    mvExp (0 : MvPowerSeries σ K) = 1 ∧
    (∀ f : MvPowerSeries σ K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (mvExp f) = 1) ∧
    (∀ f g : MvPowerSeries σ K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff g = 0 → mvExp (f + g) = mvExp f * mvExp g) ∧
    (∀ f g : MvPowerSeries σ K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff g = 0 → mvExp f = mvExp g → f = g)

def MvExpSubst : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (σ : Type) (f : PowerSeries K) (a : MvPowerSeries σ K),
    PowerSeries.constantCoeff f = 0 → MvPowerSeries.constantCoeff a = 0 →
      PowerSeries.subst a (mvExp f : PowerSeries K) = mvExp (PowerSeries.subst a f)

def LGSubgroup : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type),
    LG R (0 : MvPowerSeries σ K) ∧
    (∀ f g : MvPowerSeries σ K, LG R f → LG R g → LG R (f + g)) ∧
    (∀ f : MvPowerSeries σ K, LG R f → LG R (-f))

def LGBinom : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type) (z : K), IsBinomScalar R z →
    ∀ f : MvPowerSeries σ K, LG R f → LG R (z • f)

def LGHalf : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type), (2 : K)⁻¹ ∈ R →
    ∀ f : MvPowerSeries σ K, LG R (f + f) → LG R f

def IntBinomScalar : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (n : ℤ), IsBinomScalar R (n : K)

def LGSubst : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (f : PowerSeries K), LG R f →
    ∀ (σ : Type) (a : MvPowerSeries σ K), IsPt R a → LG R (PowerSeries.subst a f)

def LGSubstMv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type) [Finite σ]
    (f : MvPowerSeries σ K), LG R f →
    ∀ (τ : Type) (a : σ → MvPowerSeries τ K), (∀ s, IsPt R (a s)) → LG R (MvPowerSeries.subst a f)

def IntSubst : Prop :=
  ∀ (K : Type) [Field K] (R : Subring K) (f : PowerSeries K), IntPS R f →
    ∀ (σ : Type) (a : MvPowerSeries σ K), IsPt R a → IntMv R (PowerSeries.subst a f)

def LGDeriv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type) (f : MvPowerSeries σ K),
    LG R f → ∀ i : σ, IntMv R (MvPowerSeries.pderiv (R := K) i f)

end Formalism.L2.Th1.C
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.IsotropicVanish
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

section Defs4

variable {K : Type} [Field K]

def flin {σ : Type} (l linv : PowerSeries K) {n : Type} [Fintype n] (c : n → K)
    (u : n → MvPowerSeries σ K) : MvPowerSeries σ K :=
  PowerSeries.subst (∑ j, MvPowerSeries.C (c j) * PowerSeries.subst (u j) l) linv

def EndInt (R : Subring K) (l linv : PowerSeries K) (a : K) : Prop := IntPS R (mulBy l linv a)

def Frame (R : Subring K) (l linv ph : PowerSeries K) : Prop :=
  IsLogPair l linv ∧ FGInt R l linv ∧ PowerSeries.constantCoeff ph = 0

variable [CharZero K]

def PhNormAt (R : Subring K) (l linv ph : PowerSeries K) (a b : K) : Prop :=
  Cong R (PowerSeries.subst (mulBy l linv a) ph) ((a * b) • ph)

def AdjAt (R : Subring K) (l linv ph : PowerSeries K) (a b : K) : Prop :=
  ∀ (σ : Type) (x y : MvPowerSeries σ K), IsPt R x → IsPt R y →
    Cong R (be0 l linv ph (fmul l linv a x) y) (be0 l linv ph x (fmul l linv b y))

def F1 (R : Subring K) (l linv ph : PowerSeries K) : Prop :=
  ∀ (σ : Type) (x x' y : MvPowerSeries σ K), IsPt R x → IsPt R x' → IsPt R y →
    Cong R (be0 l linv ph (fadd l linv x x') y) (be0 l linv ph x y + be0 l linv ph x' y)

def ZLinAt (R : Subring K) (l linv ph : PowerSeries K) (z : K) : Prop :=
  ∀ (σ : Type) (x y : MvPowerSeries σ K), IsPt R x → IsPt R y →
    Cong R (be0 l linv ph x (fmul l linv z y)) (z • be0 l linv ph x y)

end Defs4

def PtClosure : Prop :=
  ∀ (K : Type) [Field K] (R : Subring K) (l linv : PowerSeries K),
    IsLogPair l linv → FGInt R l linv →
    (∀ (σ : Type) (x y : MvPowerSeries σ K), IsPt R x → IsPt R y → IsPt R (fadd l linv x y)) ∧
    (∀ a : K, EndInt R l linv a → ∀ (σ : Type) (x : MvPowerSeries σ K), IsPt R x →
      IsPt R (fmul l linv a x)) ∧
    EndInt R l linv 0 ∧ EndInt R l linv 1 ∧ EndInt R l linv (-1) ∧
    (∀ a b : K, EndInt R l linv a → EndInt R l linv b → EndInt R l linv (a + b)) ∧
    (∀ a b : K, EndInt R l linv a → EndInt R l linv b → EndInt R l linv (a * b))

def AdjFromNorm : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K) (a b : K),
    Frame R l linv ph → a ≠ 0 → EndInt R l linv a → EndInt R l linv a⁻¹ → EndInt R l linv b →
    PhNormAt R l linv ph a b → ZLinAt R l linv ph (a * b) → AdjAt R l linv ph a b

def AdjAdd : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K) (a b a' b' : K),
    Frame R l linv ph → F1 R l linv ph →
    EndInt R l linv a → EndInt R l linv b → EndInt R l linv a' → EndInt R l linv b' →
    AdjAt R l linv ph a b → AdjAt R l linv ph a' b' → AdjAt R l linv ph (a + a') (b + b')

def NormAdjAll : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, EndInt R l linv (τ α)) →
    (∀ z : O, star z = z → IsBinomScalar R (τ z)) →
    (∀ z : O, star z = z → ZLinAt R l linv ph (τ z)) →
    F1 R l linv ph → (2 : K)⁻¹ ∈ R → IsUnit (2 : O) →
    (∀ α : O, ∃ u v : Oˣ, α = u + v) →
    (∀ α : Oˣ, PhNormAt R l linv ph (τ α) (τ (star (α : O)))) →
    ∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α)) ∧ AdjAt R l linv ph (τ α) (τ (star α))

def UnitaryInv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, EndInt R l linv (τ α)) →
    (∀ z : O, star z = z → IsBinomScalar R (τ z)) →
    F1 R l linv ph →
    (∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α))) →
    (∀ α : O, AdjAt R l linv ph (τ α) (τ (star α))) →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (δ : Matrix n n O), δ.conjTranspose * δ = 1 →
    ∀ (σ : Type) (u : n → MvPowerSeries σ K), (∀ j, IsPt R (u j)) →
      Cong R (∑ i, PowerSeries.subst (flin l linv (fun j => τ (δ i j)) u) ph)
        (∑ j, PowerSeries.subst (u j) ph)

def HyperbolicSum : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, EndInt R l linv (τ α)) →
    (∀ z : O, star z = z → IsBinomScalar R (τ z)) →
    F1 R l linv ph →
    (∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α))) →
    (∀ α : O, AdjAt R l linv ph (τ α) (τ (star α))) →
    ∀ (n ι : Type) [Fintype n] [Fintype ι] [DecidableEq ι] (f f' : ι → n → O),
    (∀ e e', ∑ i, star (f e i) * f e' i = 0) → (∀ e e', ∑ i, star (f' e i) * f' e' i = 0) →
    (∀ e e', ∑ i, star (f e i) * f' e' i = if e = e' then 1 else 0) →
    ∀ (σ : Type) (t t' : ι → MvPowerSeries σ K), (∀ e, IsPt R (t e)) → (∀ e, IsPt R (t' e)) →
      Cong R
        (∑ i, PowerSeries.subst
          (flin l linv (Sum.elim (fun e => τ (f e i)) (fun e => τ (f' e i))) (Sum.elim t t')) ph)
        (∑ e, be0 l linv ph (t e) (t' e))

end Formalism.L2.Th1.C
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.VeluIntegral
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

def veluXs {K : Type} [Field K] {ι : Type} [Fintype ι] (A : PowerSeries K) (xs : ι → PowerSeries K)
    (xP : ι → K) (r : K) : PowerSeries K :=
  A + PowerSeries.X ^ 2 * (∑ P, (xs P - PowerSeries.C (xP P)) - PowerSeries.C r)

def VeluXFromZ : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e l linv A : PowerSeries K) (c0 : K) (ι : Type) [Fintype ι]
    (neg : ι → ι) (xP : ι → K) (w xs : ι → PowerSeries K) (al : K),
    IsLogPair l linv → XIsWp e l A c0 → IsEndoZ e neg (fun P => xP P + c0) w al →
    (∀ P, PowerSeries.subst l (w P) = xs P + PowerSeries.C c0) →
    PowerSeries.C (al ^ 2) * PowerSeries.subst (mulBy l linv al) A * PowerSeries.X ^ 2 =
      (mulBy l linv al) ^ 2 * veluXs A xs xP ((al ^ 2 - 1) * c0)

def IsogenyU : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (s2 : K) (l linv ph A : PowerSeries K)
    (c0 : K) (ι : Type) [Fintype ι] (xP : ι → K) (al : K),
    IsLogPair l linv → IsPh e s2 l ph → XIsWp e l A c0 →
    IsogenyFormula e s2 (fun P => xP P + c0) al →
    (mulBy l linv al) ^ 2 * mvExp (-((2 : K) • PowerSeries.subst (mulBy l linv al) ph))
        * PowerSeries.X ^ (2 * Fintype.card ι) =
      PowerSeries.C (al ^ 2) * PowerSeries.X ^ (2 * (Fintype.card ι + 1))
        * mvExp (-((2 * ((Fintype.card ι : K) + 1)) • ph))
        * ∏ P, (A - PowerSeries.C (xP P) * PowerSeries.X ^ 2)

def PhNormUnit : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (e : PowerSeries K) (s2 : K)
    (l linv ph A : PowerSeries K) (c0 : K) (ι : Type) [Fintype ι] (xP : ι → K) (al : K),
    IsLogPair l linv → IsPh e s2 l ph → XIsWp e l A c0 →
    IsogenyFormula e s2 (fun P => xP P + c0) al →
    IsOneUnit R A → (∀ P, xP P ∈ R) → al ∈ R → al⁻¹ ∈ R → al ≠ 0 → (2 : K)⁻¹ ∈ R →
    IntPS R (mulBy l linv al) →
    Cong R (PowerSeries.subst (mulBy l linv al) ph) (((Fintype.card ι : K) + 1) • ph)

end Formalism.L2.Th1.C
end
end

