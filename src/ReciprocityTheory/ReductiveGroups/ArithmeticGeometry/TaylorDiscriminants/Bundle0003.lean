module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

section Defs

variable {k : Type} [CommRing k] {d : ℕ}

def dLin (φ : Pt k 1 d) : Matrix (Fin d) (Fin d) k :=
  fun i j => coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ i)

def transF (F : Fin d → PS k 2 d) (φ φi : Pt k 1 d) : Fin d → PS k 2 d :=
  fun i => ev (n := 2) ![addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))] (φi i)

def IsInvPair (φ φi : Pt k 1 d) : Prop :=
  (∀ i, constantCoeff (φ i) = 0) ∧ (∀ i, constantCoeff (φi i) = 0) ∧
    comp1 φ φi = pt k (n := 1) d 0 ∧ comp1 φi φ = pt k (n := 1) d 0

def colM {ι : Type} [Finite ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) (b : Fin n) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun l => m (l, b)

end Defs

def LogSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d), ∃ ℓ : Pt k 1 d,
    (∀ i, constantCoeff (ℓ i) = 0) ∧ dLin ℓ = 1 ∧
    comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1)

def LogDerivSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (ℓ : Pt k 1 d),
    (∀ i, constantCoeff (ℓ i) = 0) → dLin ℓ = 1 →
    comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) →
    ∀ (u : Fin d → k) (g : PS k 1 d),
      Dof G.F u (ev (n := 1) ![ℓ] g) = ev (n := 1) ![ℓ] (∑ j, C (u j) * pderiv ((0 : Fin 1), j) g)

def ConstSt : Prop :=
  ∀ (k : Type) [CommRing k] (d : ℕ) (φ : Pt k 1 d), (∀ i, constantCoeff (φ i) = 0) →
    ∀ g : PS k 1 d, constantCoeff (ev (n := 1) ![φ] g) = constantCoeff g

def TransPolySt : Prop :=
  ∀ (k : Type) [CommRing k] (d : ℕ) (F : Fin d → PS k 2 d), (∀ i, constantCoeff (F i) = 0) →
    (∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (F i) = (X ((0 : Fin 1), i) : PS k 1 d)) →
    ∀ φ φi : Pt k 1 d, IsInvPair φ φi →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → k) (P : MvPolynomial ι k) (g : PS k 1 d),
      DpolyOf (transF F φ φi) u P (ev (n := 1) ![φ] g) =
        ev (n := 1) ![φ] (DpolyOf F (fun l => (dLin φ).mulVec (u l)) P g)

def GaugeTransSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B B' : FB k d O)
    (φ φi : Pt k 1 d) (lam : PS k 2 d), IsInvPair φ φi →
    ev (n := 1) ![0, pt k (n := 1) d 0] lam = 0 → ev (n := 1) ![pt k (n := 1) d 0, 0] lam = 0 →
    (∀ i, B'.G.F i = transF B.G.F φ φi i) →
    (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) →
    B'.ph1 = ev (n := 3) ![comp1 φ (pt k (n := 3) d 0), comp1 φ (pt k (n := 3) d 1),
        comp1 φ (pt k (n := 3) d 2)] B.ph1 *
      FB.expS k (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] lam +
        ev (n := 3) ![pt k (n := 3) d 1, pt k (n := 3) d 2] lam -
        ev (n := 3) ![addOf B'.G.F (pt k (n := 3) d 0) (pt k (n := 3) d 1), pt k (n := 3) d 2] lam) →
    B'.ph2 = ev (n := 3) ![comp1 φ (pt k (n := 3) d 0), comp1 φ (pt k (n := 3) d 1),
        comp1 φ (pt k (n := 3) d 2)] B.ph2 *
      FB.expS k (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1] lam +
        ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] lam -
        ev (n := 3) ![pt k (n := 3) d 0, addOf B'.G.F (pt k (n := 3) d 1) (pt k (n := 3) d 2)] lam) →
    B'.sy = ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] B.sy *
      FB.expS k (ev (n := 2) ![pt k (n := 2) d 1, pt k (n := 2) d 0] lam - lam) →
    (∀ a, B'.ad a = ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] (B.ad a) *
      FB.expS k (ev (n := 2) ![comp1 (B'.A.act a) (pt k (n := 2) d 0), pt k (n := 2) d 1] lam -
        ev (n := 2) ![pt k (n := 2) d 0, comp1 (B'.A.act (star a)) (pt k (n := 2) d 1)] lam)) →
    ∀ h : PS k 2 d, B.IsCanonGauge k h →
      B'.IsCanonGauge k (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam)

def NabTransSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B B' : FB k d O)
    (φ φi : Pt k 1 d) (lam : PS k 2 d), IsInvPair φ φi →
    ev (n := 1) ![0, pt k (n := 1) d 0] lam = 0 → ev (n := 1) ![pt k (n := 1) d 0, 0] lam = 0 →
    (∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (B.G.F i) = (X ((0 : Fin 1), i) : PS k 1 d)) →
    (∀ i, B'.G.F i = transF B.G.F φ φi i) →
    (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) →
    ∀ h : PS k 2 d, ev (n := 1) ![0, pt k (n := 1) d 0] h = 0 →
    ∀ (w0 : O) (m : ℕ) (f : PS k 1 d) (ι : Type) [Fintype ι] (u : ι → Fin d → k) (P : MvPolynomial ι k),
      B'.nabVal k (ev (n := 2) ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) w0 m
          (ev (n := 1) ![φ] f * FB.expS k (-((m : k) •
            ev (n := 1) ![pt k (n := 1) d 0, comp1 (B'.actK k w0) (pt k (n := 1) d 0)] lam))) u P =
        B.nabVal k h w0 m f (fun l => (dLin φ).mulVec (u l)) P

def GaugeIndependenceColumns : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O]
    [IsReduced O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h h' : PS k 2 d),
    B.IsCanonGauge k h → B.IsCanonGauge k h' → ∀ (w0 : O) (mm n : ℕ) (ι : Type) [Fintype ι]
    (u : ι → Fin d → k) (P : MvPolynomial (ι × Fin n) k),
    secondOrder k (fun p q : ι × Fin n => if p.2 = q.2 then
      dotProduct (u p.1) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u q.1))) +
        dotProduct (u q.1) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u p.1))) else 0) P = 0 →
    ∀ f : Fin n → PS k 1 d,
      ∑ mo ∈ P.support, P.coeff mo *
          ∏ b, B.nabVal k h w0 mm (f b) u (MvPolynomial.monomial (colM mo b) 1) =
        ∑ mo ∈ P.support, P.coeff mo *
          ∏ b, B.nabVal k h' w0 mm (f b) u (MvPolynomial.monomial (colM mo b) 1)

def HarmSecondSt : Prop :=
  ∀ (k : Type) [CommRing k] (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop),
    (∀ τ, cc (cc τ) = τ) → (∀ τ, isX τ ∨ isX (cc τ)) →
    ∀ (n : ℕ) (c : (Σ τ : T, Fin (r τ)) → (Σ τ : T, Fin (r τ)) → k),
    (∀ l l' : Σ τ : T, Fin (r τ), l'.1 ≠ cc l.1 → c l l' = 0) →
    ∀ P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k,
      (∀ τ, isX τ → ∀ (i : Fin (r τ)) (i' : Fin (r (cc τ))),
        ∑ b : Fin n, MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : T, Fin (r τ))), b)
          (MvPolynomial.pderiv (((⟨cc τ, i'⟩ : Σ τ : T, Fin (r τ))), b) P) = 0) →
      secondOrder k (fun p q : (Σ τ : T, Fin (r τ)) × Fin n => if p.2 = q.2 then c p.1 q.1 else 0) P = 0

end ReciprocityTheory.ChartRestriction.G.TB
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.EigenLift
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

def BetaSesqSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k] (B : FB R d O) (a : O) (ξ η : (Fin d → k) × (Fin d → k)),
    betaH k (OactH k B a ξ) η = betaH k ξ (OactH k B (star a) η)

def EigenOrthSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k] (B : FB R d O) (χ χ' : O → k) (ξ η : (Fin d → k) × (Fin d → k)),
    (∀ a, OactH k B a ξ = χ a • ξ) → (∀ a, OactH k B a η = χ' a • η) →
    (∃ a, IsUnit (χ a - χ' (star a))) → betaH k ξ η = 0

end ReciprocityTheory.ChartRestriction.G.TB
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GaugeExp
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

def expSecond (k : Type) [CommRing k] [Algebra ℚ k] {ι : Type} [Fintype ι] (c : ι → ι → k) (t : k) (N : ℕ)
    (Q : MvPolynomial ι k) : MvPolynomial ι k :=
  ∑ i ∈ Finset.range (N + 1), (t ^ i * algebraMap ℚ k (1 / (Nat.factorial i : ℚ))) • (secondOrder k c)^[i] Q

def GaugeExpSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k] (B : FB R d O) (h h' : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k h' →
    ∀ (w0 : O) (m : ℕ) {ι : Type} [Fintype ι] (u : ι → Fin d → k) (Q : MvPolynomial ι k) (f : PS k 1 d),
      B.nabVal k h' w0 m f u Q =
        B.nabVal k h w0 m f u (expSecond k (fun l l' =>
          dotProduct (u l) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l'))) +
          dotProduct (u l') ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l))))
          ((m : k) * algebraMap ℚ k (1 / 2)) Q.totalDegree Q)

end ReciprocityTheory.ChartRestriction.G.TB
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GermSC
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

def ordNabla (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι : Type} [Fintype ι] (s : ι → Bool)
    (ξ : ι → (Fin d → k) × (Fin d → k)) (P : MvPolynomial ι k) (G : AA k d) : AA k d :=
  ∑ n ∈ P.support, C (P.coeff n) *
    ((Finset.univ : Finset ι).toList.filter (fun l => s l)).foldr
      (fun l g => (nabla k B h m (ξ l).1 (ξ l).2)^[n l] g)
      (((Finset.univ : Finset ι).toList.filter (fun l => !s l)).foldr
        (fun l g => (nabla k B h m (ξ l).1 (ξ l).2)^[n l] g) G)

def pairMin {ι π : Type} [Fintype ι] [Fintype π] [DecidableEq π] (c : ι → π) (s : ι → Bool) (n : ι →₀ ℕ) : ℕ :=
  ∑ q : π, min (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), n l)
    (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), n l)

def OppositePairVanishing {ι π : Type} (c : ι → π) (s : ι → Bool) (A A' : ι → (Fin d → k) × (Fin d → k)) : Prop :=
  ∀ l l', ¬ (c l = c l' ∧ s l ≠ s l') → betaH k (A l) (A' l') = 0

def SCSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k], IsRQ (R := R) k → ∀ (J : Submodule R k), (1 : k) ∈ J →
    ∀ (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w0 : O), w0 + star w0 = 1 → ∀ (m : ℕ)
    (ι π : Type) [Fintype ι] [Fintype π] [DecidableEq π] (c : ι → π) (s : ι → Bool)
    (ξh : ι → (Fin d → k) × (Fin d → k)) (ψ : ι → Fin d → k),
    (∀ l, ξh l ∈ Hset (R := R) k h) → (∀ l i, ψ l i ∈ J) →
    OppositePairVanishing k c s ξh ξh → OppositePairVanishing k c s (fun l => (0, ψ l)) ξh → OppositePairVanishing k c s ξh (fun l => (0, ψ l)) →
    ∀ (P : MvPolynomial ι k), (∀ n, P.coeff n ∈ (algebraMap R k).range) →
    ∀ (e : ℕ), (∀ n ∈ P.support, pairMin c s n ≤ e) →
    ∀ f : PS k 1 d, IntAA (R := R) k f →
      constantCoeff (ordNabla k B h m s (fun l => ξh l + (0, ψ l)) P
        (liftX k (FB.expS k ((m : k) • B.hL k h w0) * f))) ∈ J ^ e

end ReciprocityTheory.ChartRestriction.G.TB
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.KillAdd
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

variable {k : Type} [CommRing k] {d n : ℕ}

def dAdd (u : Fin d → k) (b : Fin n) (G : PS k n d) : PS k n d :=
  ∑ j : Fin d, C (u j) * MvPowerSeries.pderiv (b, j) G

def polyAdd {ι : Type} [Fintype ι] (u : ι → Fin d → k) (P : MvPolynomial (ι × Fin n) k) (G : PS k n d) :
    PS k n d :=
  ∑ m ∈ P.support, C (P.coeff m) *
    (Finset.univ : Finset (ι × Fin n)).toList.foldr (fun p g => (dAdd (u p.1) p.2)^[m p] g) G

def quadCol (β : Matrix (Fin d) (Fin d) k) : PS k n d :=
  ∑ b : Fin n, ∑ i : Fin d, ∑ j : Fin d, C (β i j) * X (b, i) * X (b, j)

def KillAddSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d n : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin d → k)
    (β : Matrix (Fin d) (Fin d) k) (P : MvPolynomial (ι × Fin n) k),
    secondOrder k (fun p p' : ι × Fin n => if p.2 = p'.2 then
      dotProduct (u p.1) (β.mulVec (u p'.1)) + dotProduct (u p'.1) (β.mulVec (u p.1)) else 0) P = 0 →
    ∀ (m : k) (g : PS k n d),
      constantCoeff (polyAdd u P (FB.expS k (m • quadCol (n := n) β) * g)) = constantCoeff (polyAdd u P g)

end ReciprocityTheory.ChartRestriction.G.TB
end
end

