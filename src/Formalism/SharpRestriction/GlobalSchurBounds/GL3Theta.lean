module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.GL3Theta

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions.TaylorLogMetric

def Wp (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  (Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1}).topologicalClosure

def InWf {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ∃ k : ℕ, (p : ℂ_[p]) ^ k * x ∈ Wp p

def IntegralW {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ Wp p

def CoefWf {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, InWf (MvPowerSeries.coeff n F)

def logMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * MvPowerSeries.coeff α ((F - 1) ^ n) / (n : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

def SimeqW {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralW (expMv (f - g))

def tauK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : D.host.K) : ℂ_[p] :=
  lamC lam (D.host.φ₀ (a : D.host.E))

def tauKc (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : D.host.K) : ℂ_[p] :=
  lamC lam (D.host.φ₀ (D.host.conj (a : D.host.E)))

def OKp (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : Set (ℂ_[p] × ℂ_[p]) :=
  closure (Set.range fun a : 𝓞 D.host.K => (tauK D lam (a : D.host.K), tauKc D lam (a : D.host.K)))

def hP {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] (x y : ι → ℂ_[p] × ℂ_[p]) : ℂ_[p] × ℂ_[p] :=
  ∑ k, x k * (y k).swap

def IsModelU {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) : Prop :=
  let W := C • wModel lam Λ
  IsIntP W.a₁ ∧ IsIntP W.a₂ ∧ IsIntP W.a₃ ∧ IsIntP W.a₄ ∧ IsIntP W.a₆ ∧ ‖W.Δ‖ = 1

theorem IsModel.toU {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]} {Λ : AddSubgroup ℂ}
    {C : WeierstrassCurve.VariableChange ℂ_[p]} (h : IsModel lam Λ C) : IsModelU lam Λ C := by
  obtain ⟨h1, h2, h3, h4, h6, hd⟩ := h
  show IsIntP _ ∧ IsIntP _ ∧ IsIntP _ ∧ IsIntP _ ∧ IsIntP _ ∧ ‖_‖ = 1
  exact ⟨h1, h2, h3, h4, h6, by first | rw [hd, norm_one] | simp [hd]⟩

def ModelOverW {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) : Prop :=
  let W := C • wModel lam Λ
  W.a₁ ∈ Wp p ∧ W.a₂ ∈ Wp p ∧ W.a₃ ∈ Wp p ∧ W.a₄ ∈ Wp p ∧ W.a₆ ∈ Wp p

structure G1 (p : ℕ) [Fact p.Prime] where
  lam : Qbar →+* ℂ_[p]
  abelian₂ : AddSubgroup ℂ
  C : WeierstrassCurve.VariableChange ℂ_[p]
  wq : PowerSeries ℂ_[p]
  ex : PowerSeries ℂ_[p]

namespace G1

variable {p : ℕ} [Fact p.Prime] (g : G1 p)

def W : WeierstrassCurve ℂ_[p] := g.C • wModel g.lam g.abelian₂

def l : PowerSeries ℂ_[p] := flog g.W g.wq

def Ok : Prop :=
  IsModelU g.lam g.abelian₂ g.C ∧ IsWq g.W g.wq ∧
    PowerSeries.constantCoeff g.ex = 0 ∧ PowerSeries.subst g.ex g.l = PowerSeries.X

def ph : PowerSeries ℂ_[p] := -logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)

variable {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a g.l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x g.ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := g.pt (g.lg a + g.lg b)

def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := g.pt (g.lg a - g.lg b)

def mulBy (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  g.pt (MvPowerSeries.C c * g.lg a)

def lin {ι : Type*} [Fintype ι] (c : ι → ℂ_[p]) (a : ι → MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries σ ℂ_[p] :=
  g.pt (∑ j, MvPowerSeries.C (c j) * g.lg (a j))

def phAt (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a g.ph

def be (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  g.phAt (g.add a b) - g.phAt a - g.phAt b

end G1

def At (D : D7) {p : ℕ} [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p) : Prop :=
  IsCurveIdeal D cc ∧ Nat.Coprime (Ideal.absNorm cc) p ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧
    g.abelian₂ = lamOf D cc δ ∧ g.Ok

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

def SplitK (D : D7) (p : ℕ) : Prop := jacobiSym (-(D.host.d : ℤ)) p = 1

def InertK (D : D7) (p : ℕ) : Prop := jacobiSym (-(D.host.d : ℤ)) p = -1

def modelEx (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ),
    IsCurveIdeal D cc → Nat.Coprime (Ideal.absNorm cc) p → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    (∃ C, IsModelU lam (lamOf D cc δ) C) ∧
    (5 ≤ p → InertK D p → ∃ C, IsModelU lam (lamOf D cc δ) C ∧ ModelOverW lam (lamOf D cc δ) C) ∧
    ∀ C, IsModelU lam (lamOf D cc δ) C → ‖((C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1

def cube2 (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    Simeq (g.phAt (g.add (Xv 0) (Xv 1)) + g.phAt (g.sub (Xv 0) (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (2 * g.phAt (Xv 0) + 2 * g.phAt (Xv 1))

def cube3 (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) + g.phAt (g.sub (Xv 0) (Xv 1)) +
        g.phAt (g.sub (Xv 1) (Xv 2)) + g.phAt (g.sub (Xv 2) (Xv 0)) : MvPowerSeries (Fin 3) ℂ_[p])
      (3 * (g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2)))

def cube (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) - g.phAt (g.add (Xv 0) (Xv 1)) -
        g.phAt (g.add (Xv 1) (Xv 2)) - g.phAt (g.add (Xv 2) (Xv 0)) +
        g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0

def beBiadd (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) ∧
    Simeq (g.be (Xv 0) (g.add (Xv 1) (Xv 2)) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 1) + g.be (Xv 0) (Xv 2))

def addInt (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ∧
    (ModelOverW g.lam g.abelian₂ g.C → IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))

def endInt (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    ∀ α ∈ OKp D g.lam, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])

def phNorm (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    ∀ α ∈ OKp D g.lam,
      Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))

def beConj (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    ∀ α ∈ OKp D g.lam,
      Simeq (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))

def splitZero (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    SplitK D p →
      Simeq (g.be (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) 0 ∧
      Simeq (g.phAt (Xv ()) : MvPowerSeries Unit ℂ_[p]) 0

def ser1 {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (G : ℂ → ℂ) : PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => lamC lam (iteratedDeriv n G 0 / (n.factorial : ℂ))

def G1.atU {p : ℕ} [Fact p.Prime] (g : G1 p) (G : ℂ → ℂ) : PowerSeries ℂ_[p] :=
  PowerSeries.subst (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * g.l)
    (ser1 g.lam G)

def Tors1 (p : ℕ) (Λ : AddSubgroup ℂ) (t : ℂ) : Prop :=
  t ∉ Λ ∧ ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * t ∈ Λ

def transl (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    ∀ t : ℂ, Tors1 p g.abelian₂ t →
      IntegralMv ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * g.atU (U1 g.abelian₂ t (sgStar g.abelian₂))) ∧
      ‖PowerSeries.constantCoeff (g.atU (U1 g.abelian₂ t (sgStar g.abelian₂)))‖ = 1

def IsTwoTorsionPointUnkilled (D : D7) (Λ : AddSubgroup ℂ) (t : ℂ) : Prop :=
  2 * t ∈ Λ ∧ ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * t ∉ Λ ∧
    ((1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * t ∉ Λ

def th0 (Λ : AddSubgroup ℂ) (t0 : ℂ) : ℂ → ℂ :=
  fun z => U1 Λ t0 (sgStar Λ) z / U1 Λ t0 (sgStar Λ) 0

def atTwo (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 2), At D cc δ g →
    ∀ t0 : ℂ, IsTwoTorsionPointUnkilled D g.abelian₂ t0 →
      Simeq (-logMv (g.atU (th0 g.abelian₂ t0)) : MvPowerSeries Unit ℂ_[2]) 0 ∧
      ∀ t : ℂ, Tors1 2 g.abelian₂ t → IntegralMv (g.atU (U1 g.abelian₂ t (th0 g.abelian₂ t0))) ∧
        ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ n, ‖PowerSeries.coeff n (g.atU (U1 g.abelian₂ t (th0 g.abelian₂ t0)))‖ ≤ ρ

def G1.jetPh {p : ℕ} [Fact p.Prime] (g : G1 p) (i : ℕ) : ℂ_[p] :=
  (i.factorial : ℂ_[p]) * PowerSeries.coeff i (PowerSeries.subst g.ex g.ph : PowerSeries ℂ_[p])

def jetsPh (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    (∀ i, i ≠ 2 → IsIntP (g.jetPh i)) ∧
    (∀ α ∈ OKp D g.lam, IsIntP ((α.1 - α.2) * g.jetPh 2)) ∧
    (p ≠ D.host.d → IsIntP (g.jetPh 2)) ∧
    (p = D.host.d → ‖g.jetPh 2‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2))

def G1.PhOn {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι : Type*} [Fintype κ] [Fintype ι]
    (b : ι → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries ι ℂ_[p] :=
  ∑ k, g.phAt (g.lin (fun e => (b e k).1) (fun e => Xv e))

abbrev Idx (D : D7) (N N' : ℕ) : Type := D.what₂.Tau × Fin N' × Fin N

def phW (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C → CoefWf g.ph

def readW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : MvPowerSeries σ ℂ_[p]), CoefWf f → Simeq f 0 → SimeqW f 0

def logF (p : ℕ) [Fact p.Prime] : PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => ∑ j ∈ Finset.range (n + 1), if n = p ^ (2 * j) then ((p : ℂ_[p]) ^ j)⁻¹ else 0

def beW (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C →
    CoefWf (g.be (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ∧
    SimeqW (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) ∧
    SimeqW (g.be (Xv 0) (g.add (Xv 1) (Xv 2)) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 1) + g.be (Xv 0) (Xv 2)) ∧
    ∀ α ∈ OKp D g.lam,
      SimeqW (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))

def W2pair (p : ℕ) [Fact p.Prime] : Set (ℂ_[p] × ℂ_[p]) :=
  closure (Subring.closure {x : ℂ_[p] × ℂ_[p] | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)} :
    Set (ℂ_[p] × ℂ_[p]))

def okpInert (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 → InertK D p → OKp D lam = W2pair p

def PowRat (D : D7) (t : D.Dt) (h : ℕ) (z : letI := D.host.cmStar; unitary D.host.E) : Prop :=
  0 < h ∧ ∃ k ∈ D.UO, t ^ h = D.e1Dt z * k

def chiVal (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (t : D.Dt) (h : ℕ) (z : unitary D.host.E), PowRat D t h z →
    ((D.chiD t : ℂˣ) : ℂ) ^ h = ∏ τ, (embT D τ (z : D.host.E))⁻¹ ∧
    ‖lamC lam ((D.chiD t : ℂˣ) : ℂ)‖ ^ h = ∏ τ, ‖lamC lam (embT D τ (z : D.host.E))‖⁻¹

def PowRatAll (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ t : D.Dt, ∃ (h : ℕ) (z : unitary D.host.E), PowRat D t h z

def NormOnePowerPrincipal (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ 𝔞 : IdE D, N1 D 𝔞 → ∃ (h : ℕ) (z : unitary D.host.E), 0 < h ∧
    𝔞 ^ h = Submodule.span (𝓞 D.host.E) {(z : D.host.E)}

theorem idl_pow {D : D7} {idl : D.Dt ⧸ D.UO → IdE D} (hm : ∀ x y, idl (x * y) = idl x * idl y)
    (x : D.Dt ⧸ D.UO) : ∀ n : ℕ, idl (x ^ (n + 1)) = idl x ^ (n + 1)
  | 0 => by simp
  | n + 1 => by rw [pow_succ, hm, idl_pow hm x n, ← pow_succ]

theorem powRatAll_of (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) (h : RelDetPinned D idl) (hn : NormOnePowerPrincipal D) :
    PowRatAll D := by
  obtain ⟨hinj, hN1, hm, hz, -⟩ := h
  intro t
  obtain ⟨n, z, hn, hnz⟩ := hn (idl (QuotientGroup.mk t)) ((hN1 _).2 ⟨_, rfl⟩)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hq : (QuotientGroup.mk (D.e1Dt z) : D.Dt ⧸ D.UO) = QuotientGroup.mk (t ^ (m + 1)) := by
    apply hinj
    rw [hz, ← hnz, QuotientGroup.mk_pow, idl_pow hm]
  refine ⟨m + 1, z, ?_⟩
  unfold PowRat
  exact ⟨hn, (D.e1Dt z)⁻¹ * t ^ (m + 1), QuotientGroup.eq.mp hq, (mul_inv_cancel_left _ _).symm⟩

def rhoOf (D : D7) (mt : ℕ → D.Dt →* ℂˣ) (i : ℕ) : D.Dt →* ℂˣ :=
  (mt (i + 1))⁻¹ * D.chiD ^ (-(((D.R.N (i + 1)) / 2 : ℕ) : ℤ))

def rhoOf' (D : D7) (mt : ℕ → D.Dt →* ℂˣ) (i : ℕ) : D.Dt →* ℂˣ :=
  mt (i + 1) * D.chiD ^ ((((D.R.N i) / 2 : ℕ) : ℤ))

def CarriesTupleCharacters (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ)
    (dt : ∀ i, C.cls i → D.Dt) : Prop :=
  ∀ i < D.R.m, (∀ c, C.rhoDet i c = ((rhoOf D mt i (dt i c) : ℂˣ) : ℂ)) ∧
    ∀ c, C.rhoDet' i c = ((rhoOf' D mt i (dt (i + 1) c) : ℂˣ) : ℂ)

def Mod1E (x : ℂ) : Prop := ∃ hx : x ∈ Qbar, ∀ ρ : Qbar →+* ℂ, ‖ρ ⟨x, hx⟩‖ = 1

def rhoThreeOf (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ) : Prop :=
  letI := D.host.cmStar
  ∀ i < D.R.m,
    (∀ (t : D.Dt) (h : ℕ) (z : unitary D.host.E), PowRat D t h z →
      Mod1E ((rhoOf D mt i t : ℂˣ) : ℂ) ∧ Mod1E ((rhoOf' D mt i t : ℂˣ) : ℂ)) ∧
    (∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ rhoOf D mt i k ^ n = 1 ∧ rhoOf' D mt i k ^ n = 1) ∧
    (∀ z : unitary D.host.E,
      ((rhoOf D mt i (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (-C.sSharp i τ) ∧
      ((rhoOf' D mt i (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (C.sDiv i τ))

theorem lift_eqC (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ)
    (dt : ∀ i, C.cls i → D.Dt) (h : CarriesTupleCharacters D C mt dt) (i : ℕ) (hi : i < D.R.m) (φ : C.cls i → C.Y i → ℂ)
    (c' : C.cls (i + 1)) :
    C.K i φ c' = ∑ c, (((Nat.card (C.stab i c) : ℕ) : ℂ)⁻¹) •
      ((((rhoOf D mt i (dt i c) : ℂˣ) : ℂ) * ((rhoOf' D mt i (dt (i + 1) c') : ℂˣ) : ℂ)) •
        C.divDe i (C.unf i c c' (C.sharp i (φ c)))) := by
  obtain ⟨h1, h2⟩ := h i hi
  simp only [Formalism.BasicNotions.ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM, Formalism.BasicNotions.ColumnChain.Kmap, Formalism.BasicNotions.ColumnChain.wt,
    LinearMap.smul_apply, LinearMap.comp_apply, h1, h2]

def applyAt0 (D : D7) {N N' : ℕ} (P : MvPolynomial (Idx D N N') ℂ) (G : VC D N N' → ℂ) : ℂ :=
  ∑ α ∈ P.support, AddMonoidAlgebra.coeff P α * (α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α

abbrev FrV (D : D7) (N : ℕ) : Type := D.what₂.Tau × Fin N × Fin N

def evFr (D : D7) {N : ℕ} (Q : MvPolynomial (FrV D N) ℂ) (y : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  MvPolynomial.eval (fun k : FrV D N => y k.1 k.2.1 k.2.2) Q

def polD (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (FrV D N) ℂ)
    (y' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) : MvPolynomial (Idx D N N') ℂ :=
  MvPolynomial.aeval (fun k : FrV D N => ∑ b : Fin N',
    MvPolynomial.C (s k.1 * (if h : (k.2.2 : ℕ) < N' then y' k.1 b ⟨k.2.2, h⟩ else 0)) *
      MvPolynomial.X ((k.1, b, k.2.1) : Idx D N N')) Q

def IsKer (D : D7) (T : Tor D) (e : FamE D) (S : Finset ℕ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (Θ : VC D N N' → ℂ) : Prop :=
  ∃ (n : ℕ) (r : Fin n → ℂ) (t : Fin n → VC D N N'),
    (∀ k, r k ∈ Qbar) ∧
    (∀ k (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ∉ S → ‖lamC lam (r k)‖ ≤ 1) ∧
    (∀ k, ∃ a : ℕ, 0 < a ∧ (∀ q : ℕ, q.Prime → q ∣ a → q ∈ S) ∧ a • t k ∈ La D T L L') ∧
    Θ = fun z => ∑ k, r k * U D T (t k) (e N N' L L') z

structure LiftObj (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) where
  mt : ℕ → D.Dt →* ℂˣ
  L0 : ∀ i, (letI := D.host.cmStar; SDLat D.host.E (D.R.N i))
  lattice_integral_coordinates : ∀ i (x : Fin (D.R.N i) → D.host.E), x ∈ (L0 i).1 ↔ ∀ k, IsIntegral ℤ (x k)
  lat : ∀ i, C.cls i → (letI := D.host.cmStar; SDLat D.host.E (D.R.N i))
  dt : ∀ i, C.cls i → D.Dt
  dt_lat : ∀ i c, (QuotientGroup.mk (dt i c) : D.Dt ⧸ D.UO) = D.relDet (D.R.N i) (L0 i) (lat i c)
  c13 : CarriesTupleCharacters D C mt dt
  frm : ∀ i, C.Y i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ
  frm_inj : ∀ i ≤ D.R.m, Function.Injective (frm i)
  frm_range : ∀ i ≤ D.R.m, ∀ f : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ,
    (∃ y, frm i y = f) ↔ ∀ τ, (f τ).det ≠ 0
  frm_de : ∀ i ≤ D.R.m, ∀ y τ, C.de i y τ = (frm i y τ).det
  dgen : D.what₂.Tau → ℂ
  dgen_gen : ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M), (∀ τ x, embT D τ x ∈ M) ∧ ∀ τ, ∃ s : M, (s : ℂ) = dgen τ ∧
    ellT D M τ = Submodule.span (𝓞 M) {s}
  S : Finset ℕ
  Th : ∀ i, C.cls i → C.cls (i + 1) → VC D (D.R.N i) (D.R.N (i + 1)) → ℂ

def liftTie (D : D7) (T : Tor D) (e : FamE D) {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)}
    (O : LiftObj D C) (i : ℕ) : Prop :=
  (∀ c c', IsKer D T e O.S (O.lat i c).1 (O.lat (i + 1) c').1 (O.Th i c c')) ∧
  ∀ c c' (Q : MvPolynomial (FrV D (D.R.N i)) ℂ) (y' : C.Y (i + 1)),
    C.unf i c c' (fun y => evFr D Q (O.frm i y)) y' =
      applyAt0 D (polD D O.dgen Q (O.frm (i + 1) y')) (O.Th i c c')

def LiftObj.IsMem {D : D7} {u : D.what₂.Word} (O : LiftObj D (D.mem u).C) : Prop :=
  letI := D.host.cmStar
  O.mt = D.muTil ∧ (∀ i c, O.dt i c = D.detCls u i c) ∧
  ∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧
    (π : D.host.E) * D.host.conj (π : D.host.E) = ((D.mem u).A.T : D.host.E) ∧
    ∀ i, i ≤ D.R.m → ∃ co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E),
      (∀ x y, stdH D.host.E (D.R.N i) (co x) (co y) = (D.sp.X i).hT x y) ∧
      (∀ y, co y ∈ (O.L0 i).1 ↔ y ∈ (D.sp.X i).L0) ∧
      ∀ (c : (D.mem u).C.cls i) y, co y ∈ (O.lat i c).1 ↔
        ∃ a ∈ D.clsLat u i c, ∃ b ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c),
          y = a + D.host.conj (π : D.host.E) • b

def repExS (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (n : ℕ), 0 < n → ∀ (N : ℕ) (L L₀ : SDLat D.host.E N),
    ∃ γ : Matrix.unitaryGroup (Fin N) D.host.E,
      EqAt D n (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L.1) L₀.1

def rhoValOf (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ) : Prop :=
  letI := D.host.cmStar
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (t : D.Dt) (h : ℕ) (z : unitary D.host.E), PowRat D t h z →
    ∀ i < D.R.m,
      ‖lamC lam ((rhoOf D mt i t : ℂˣ) : ℂ)‖ ^ h = ∏ τ, ‖lamC lam (embT D τ (z : D.host.E))‖ ^ (-C.sSharp i τ) ∧
      ‖lamC lam ((rhoOf' D mt i t : ℂˣ) : ℂ)‖ ^ h = ∏ τ, ‖lamC lam (embT D τ (z : D.host.E))‖ ^ (C.sDiv i τ)

def nrmId (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (𝔞 : IdE D) : ℝ :=
  sSup ((fun x : D.host.E => ‖lamC lam (embT D τ x)‖) '' (𝔞 : Set D.host.E))

def brRhoOf (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ) : Prop :=
  ∀ idl : D.Dt ⧸ D.UO → IdE D, RelDetPinned D idl →
    ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (t : D.Dt),
      ‖lamC lam ((D.chiD t : ℂˣ) : ℂ)‖ = ∏ τ, (nrmId D lam τ (idl (QuotientGroup.mk t)))⁻¹ ∧
      ∀ i < D.R.m,
        ‖lamC lam ((rhoOf D mt i t : ℂˣ) : ℂ)‖ = ∏ τ, nrmId D lam τ (idl (QuotientGroup.mk t)) ^ (-C.sSharp i τ) ∧
        ‖lamC lam ((rhoOf' D mt i t : ℂˣ) : ℂ)‖ = ∏ τ, nrmId D lam τ (idl (QuotientGroup.mk t)) ^ (C.sDiv i τ)


open IsDedekindDomain in
abbrev EP (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) : Type := P.adicCompletion D.host.E


open IsDedekindDomain in
def SplitP (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∃ a b : 𝓞 D.host.E, (b : D.host.E) = D.host.conj (a : D.host.E) ∧ a ∈ P.asIdeal ∧ b ∉ P.asIdeal


open IsDedekindDomain in
def EqOff (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {N : ℕ}
    (L L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  ∃ m : ℕ, ∀ a b : 𝓞 D.host.E, (b : D.host.E) = D.host.conj (a : D.host.E) → a ∈ P.asIdeal ^ m →
    (∀ x ∈ L, (a * b) • x ∈ L₀) ∧ ∀ x ∈ L₀, (a * b) • x ∈ L


open IsDedekindDomain in
def EqOffSplit (D : D7) {N : ℕ} (L L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  ∃ a : 𝓞 D.host.E, a ≠ 0 ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), a ∈ Q.asIdeal → SplitP D Q) ∧
    (∀ x ∈ L, a • x ∈ L₀) ∧ ∀ x ∈ L₀, a • x ∈ L


open IsDedekindDomain in
def YP (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    AddSubgroup (Matrix (Fin N') (Fin N) (EP D P)) :=
  ((YYl D L L').toAddSubgroup.map
    ((algebraMap D.host.E (EP D P)).toAddMonoidHom.mapMatrix)).topologicalClosure


open IsDedekindDomain in
def volP {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {N N' : ℕ}
    (Y₀ Y₁ : AddSubgroup (Matrix (Fin N') (Fin N) (EP D P))) : ℝ :=
  ((Y₀.addSubgroupOf Y₁).index : ℝ) / ((Y₁.addSubgroupOf Y₀).index : ℝ)


open IsDedekindDomain in
def modelXi (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (N N' : ℕ) (L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L₀' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L₀ L₀' →
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), SplitP D P →
    ∀ th ∈ Th D (tor0 D cc δ) L₀ L₀',
    ∃ Xi : (Matrix (Fin N') (Fin N) (EP D P) → ℂ) →ₗ[ℂ] (VC D N N' → ℂ),
      Xi (Set.indicator (YP D P L₀ L₀' : Set (Matrix (Fin N') (Fin N) (EP D P))) 1) = th ∧
      ∀ L L', admitted D N N' L L' → EqOff D P L L₀ → EqOff D P L' L₀' →
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₀ L₀') (La D (tor0 D cc δ) L L') th =
          fun z => (((Real.sqrt (volP (YP D P L₀ L₀') (YP D P L L')))⁻¹ : ℝ) : ℂ) *
            Xi (Set.indicator (YP D P L L' : Set (Matrix (Fin N') (Fin N) (EP D P))) 1) z

def movesCompose (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (N N' : ℕ) (L₁ L₂ L₃ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L₁' L₂' L₃' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' → admitted D N N' L₃ L₃' →
      EqOffSplit D L₁ L₂ → EqOffSplit D L₂ L₃ → EqOffSplit D L₁' L₂' → EqOffSplit D L₂' L₃' →
      ∀ th ∈ Th D (tor0 D cc δ) L₁ L₁',
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₂ L₂') (La D (tor0 D cc δ) L₃ L₃')
            (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') (La D (tor0 D cc δ) L₂ L₂') th) =
          Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') (La D (tor0 D cc δ) L₃ L₃') th

def admJ (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    IsIntegral ℤ (1728 * g2 (lamOf D cc δ) ^ 3)

def InducedCMType (D : D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (a : D.host.K), embT D τ (a : D.host.E) = D.host.φ₀ (a : D.host.E)

def HostFieldConditions (D : D7) : Prop := TaylorLogMetric.adm1 D

def kerComb (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (S : Finset ℕ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (Θ : VC D N N' → ℂ), admitted D N N' L L' →
    IsKer D (tor0 D cc δ) e S L L' Θ →
    ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ∉ S → IsComb D (tor0 D cc δ) e lam L L' (pSer D lam Θ)

def hf1 (Λ : AddSubgroup ℂ) (z w : ℂ) : ℂ := z * (starRingEnd ℂ) w / (area Λ : ℂ)

def al1 (d : ℕ) (Λ : AddSubgroup ℂ) (x : ℂ) : ℂ := (-1 : ℂ) ^ (round (Real.sqrt d / 2 * (hf1 Λ x x).re))

def IsTheta0 (d : ℕ) (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : Prop :=
  Differentiable ℂ G ∧ (∀ x ∈ Λ, ∀ z, al1 d Λ x * U1 Λ x G z = G z) ∧ G 0 = 1

def normSq1 (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : ℝ :=
  let Fd : Set ℂ := Classical.epsilon (fun Fd => MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume)
  ⨍ z in Fd, ‖G z‖ ^ 2 * Real.exp (-Real.pi * (hf1 Λ z z).re)

end Formalism.MainNotions.GL3Theta
