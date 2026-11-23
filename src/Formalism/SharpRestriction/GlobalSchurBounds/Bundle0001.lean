module

public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.Chosen
section
noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

section AtRecord

variable {D : D7} (L : SizeData₂ D)

def GamL : ℝ := Real.exp (L.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L)

def ThickSetLowerBound (_L : SizeData₂ D) : Prop := D.host.secondSet_card_lower_bound

def ChTT_at : Prop :=
  L.sc.delta1 * D.R.n / 2 ≤ (D.host.TT.card : ℝ) ∧ (D.host.TT.card : ℝ) ≤ 2 * L.sc.delta1 * D.R.n


open Classical in
def largeOrderResiduePrimes : Finset ℕ :=
  (Finset.range ⌈L.sc.X'⌉₊).filter (fun p =>
    p.Prime ∧ G.IsResidueClassZero D p ∧ L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (G.hP D p) : ℝ))

variable {L}


open Classical in
def badTops (X : G.Inst D L) (p : ℕ) : Finset (G.HH D) :=
  D.host.TT.filter (fun t => ¬ G.Good X p (X.bs (G.stepP D p) t))

def ChBad_at (X : G.Inst D L) (Cb : ℝ) : Prop :=
  ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p * ((badTops X p).card : ℝ) ≤
    4 * (Cb * L.sc.x ^ (-2 : ℝ)) * L.sc.delta1 * D.R.n * ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p

def BoundsAtX (x eps C : ℝ) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), GlobalTheoryTheory.Induces χ f M →
    ‖GlobalTheoryTheory.gChi χ x‖ ≤ x ^ ((1 : ℝ) / 2 + eps) ∧ ‖GlobalTheoryTheory.logDerivativeAtOne χ‖ ≤ C * Real.log x

def ChQD_at (D : D7) (x eps C : ℝ) : Prop :=
  BoundsAtX x eps C (GlobalTheoryTheory.psDir D.host.q) (8 * D.host.q * D.host.d) ∧
  BoundsAtX x eps C (GlobalTheoryTheory.chDir D.host.d) (8 * D.host.q * D.host.d) ∧
  BoundsAtX x eps C (fun a => GlobalTheoryTheory.chDir D.host.d a * GlobalTheoryTheory.psDir D.host.q a) (8 * D.host.q * D.host.d)

def ChThin_at (D : D7) (x eps c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), GlobalTheoryTheory.IsCharED D χ →
    ∀ y : ℝ, Real.exp (x ^ (eps / 3)) / 3 ≤ y → ‖GlobalTheoryTheory.gChi χ y‖ ≤ y * Real.exp (-(c * x ^ (eps / 8)))

variable (L)

def ChProviso_at (C0 : ℝ) : Prop :=
  ∀ u, C0⁻¹ ≤ (D.duS u : ℝ) * GamL L ^ 2 / D.what₂.Dstar ∧ (D.duS u : ℝ) * GamL L ^ 2 / D.what₂.Dstar ≤ C0

def ChCode_at (C0 CH : ℝ) : Prop :=
  C0 * GamL L ^ 2 * L.sc.x ^ CH ≤ (Fintype.card D.what₂.Word : ℝ)

end AtRecord

section Family

variable {eps : ℝ} (Fm : FamP eps)

def ThickSetEventually : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ThickSetLowerBound (Fm.L x i)

def ChosenTT : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChTT_at (Fm.L x i)

def ChosenBad (Cb : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChBad_at (Fm.Gx x i) Cb

def ChosenQD (C5 : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChQD_at (Fm.D x i) x eps C5

def ChosenThin (c6 : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChThin_at (Fm.D x i) x eps c6

def ChosenProviso (C0 : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChProviso_at (Fm.L x i) C0

def ChosenCode (C0 CH : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChCode_at (Fm.L x i) C0 CH

def Chosen (CH C0 C5 c6 Cb : ℝ) : Prop :=
  ThickSetEventually Fm ∧ ChosenTT Fm ∧ ChosenBad Fm Cb ∧ ChosenQD Fm C5 ∧ ChosenThin Fm c6 ∧
    ChosenProviso Fm C0 ∧ ChosenCode Fm C0 CH

def ChosenE (C0 CH : ℝ) : Prop :=
  ∃ C5 c6 Cb : ℝ, 0 < C5 ∧ 0 < c6 ∧ 0 < Cb ∧ Chosen Fm CH C0 C5 c6 Cb

end Family

end Formalism.MainNotions

end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot34

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def thetaS {n : ℕ} (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (S : Set (Fin n → Fin M → E))
    (h : HA (AF F) σ J) : ℂ :=
  ∑' X : S, Φ (actTup (AF F) (HA.mat (AF F) σ J h⁻¹) (ratTup (AF F) (X : Fin n → Fin M → E)))

def SWa1 : Prop :=
  AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 => μ 𝓕 < ⊤

end Ext

def ForAllCM (P : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (_σ : E →ₐ[F] E) (M : ℕ) (_J : Matrix (Fin M) (Fin M) E), Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
      P F E σ M J

section Data

open Formalism.BasicNotions

theorem isCMExt_D (D : D7) :
    letI := D.host.cmStar; IsCMExt D.host.F D.host.E D.sp.cm.sig := by
  let _ := D.host.cmStar
  exact ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, fun τ x => D.sp.cm.cmUnram.2.1 τ x⟩

end Data

end Formalism.MainNotions.UnusedSlot34
end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
section
noncomputable section

namespace Formalism.MainNotions.ShortIntervalPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory NumberField Filter Topology MeasureTheory

def Li (X : ℝ) : ℝ := ∫ t in (2 : ℝ)..X, 1 / Real.log t

def rhoErr (C c B X : ℝ) : ℝ :=
  C * Real.exp (-(c * Real.log X / Real.log B)) + C * Real.exp (-(c * Real.sqrt (Real.log X)))

section RayClass

variable (K0 : Type) [Field K0] [NumberField K0]

def CoprimeTo (qq I : Ideal (𝓞 K0)) : Prop := I ≠ ⊥ ∧ I ⊔ qq = ⊤

def RayRel (qq I J : Ideal (𝓞 K0)) : Prop :=
  ∃ a b : 𝓞 K0, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ qq ∧ b - 1 ∈ qq ∧
    (∀ σ : K0 →+* ℝ, 0 < σ (a : K0) ∧ 0 < σ (b : K0)) ∧
    Ideal.span {a} * I = Ideal.span {b} * J

def Bmod (qq : Ideal (𝓞 K0)) : ℝ := 4 * |(discr K0 : ℝ)| * (Ideal.absNorm qq : ℝ)

def nDeg1 (qq I0 : Ideal (𝓞 K0)) (X h : ℝ) : ℕ :=
  Set.ncard {P : Ideal (𝓞 K0) | P.IsPrime ∧ CoprimeTo K0 qq P ∧ RayRel K0 qq P I0 ∧
    (Ideal.absNorm P).Prime ∧ X < (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ X * (1 + h)}

def ShortIntervalLowerBound (cQ C0 Cr cr c1 c2 : ℝ) : Prop :=
  ∀ qq : Ideal (𝓞 K0), qq ≠ ⊥ → ∀ X : ℝ, Bmod K0 qq ^ C0 ≤ X →
    (∀ (be : ℝ) (th : ℤ), (th = -1 ∨ th = 0 ∨ th = 1) → 1 / 2 ≤ be → be < 1 →
      cQ / (Bmod K0 qq ^ 2 * Real.log (Bmod K0 qq)) ≤ 1 - be →
      c1 * Bmod K0 qq ^ (-5 : ℝ) * X / Real.log X ≤ Li X - (th : ℝ) * Li (X ^ be)) ∧
    (∀ I0, CoprimeTo K0 qq I0 → ∀ h : ℝ, rhoErr Cr cr (Bmod K0 qq) X ≤ h / 100 → h ≤ 1 →
      Bmod K0 qq ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) →
      c2 * h * Bmod K0 qq ^ (-6 : ℝ) * X / Real.log X ≤ (nDeg1 K0 qq I0 X h : ℝ))

end RayClass

def NormOneMod (D : D7) (M g : ℕ) : Prop :=
  ∃ π ρ : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧ (ρ : D.host.E) ∈ D.host.K ∧
    (π : D.host.E) - 1 = (M : D.host.E) * ρ ∧
    (π : D.host.E) * D.host.conj (π : D.host.E) = (g : D.host.E)

def SplitsCompletely (D : D7) (p : ℕ) : Prop :=
  (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E

abbrev ZPt : Type := Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ

def zOrd {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

def ZerosBelow {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ DirichletCharacter.LFunction χ ρ = 0}

def ZerosNear {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ DirichletCharacter.LFunction χ ρ = 0}

def adm6 (_D : D7) (C1 c : ℝ) : Prop :=
  (∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset ZPt,
    (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧
      DirichletCharacter.LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) →
    ((∑ p ∈ T, analyticOrderNatAt (DirichletCharacter.LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤
      C1 * Q ^ ((1 : ℝ) / 4)) ∧
  (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N → ∀ ρ : ℂ,
    DirichletCharacter.LFunction χ ρ = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re →
    IsRealChar χ ∧ ρ.im = 0 ∧ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ = 1 ∧
      ∀ ρ' : ℂ, DirichletCharacter.LFunction χ ρ' = 0 →
        1 - c / Real.log (max (N : ℝ) (N * |ρ'.im|)) ≤ ρ'.re → ρ' = ρ) ∧
  (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3))

def adm7 (_D : D7) (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T : ℝ, 2 ≤ T → T ≤ u →
      (ZerosBelow χ T).Finite ∧
      ‖psi0 χ u + ∑ᶠ ρ ∈ ZerosBelow χ T, (zOrd χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
        C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) +
          ∑ᶠ ρ ∈ ZerosBelow χ 1, (zOrd χ ρ : ℝ) / ‖ρ‖)

def adm11 (_D : D7) (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ t : ℝ,
    (ZerosNear χ t).Finite ∧
    ∑ᶠ ρ ∈ ZerosNear χ t, (zOrd χ ρ : ℝ) ≤ C * Real.log (N * (|t| + 2))

theorem factorsThrough_inv {N : ℕ} {χ : DirichletCharacter ℂ N} {d : ℕ}
    (h : χ.FactorsThrough d) : χ⁻¹.FactorsThrough d := by
  obtain ⟨hd, χ₀, hχ⟩ := h
  exact ⟨hd, χ₀⁻¹, by rw [hχ, map_inv]⟩

theorem isPrimitive_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive) :
    χ⁻¹.IsPrimitive := by
  unfold DirichletCharacter.IsPrimitive DirichletCharacter.conductor at *
  have hs : χ⁻¹.conductorSet = χ.conductorSet := by
    ext d
    rw [DirichletCharacter.mem_conductorSet_iff, DirichletCharacter.mem_conductorSet_iff]
    exact ⟨fun h' => by simpa using factorsThrough_inv h', factorsThrough_inv⟩
  rw [hs]
  exact h

theorem zero_symm {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hz : DirichletCharacter.LFunction χ ρ = 0) :
    DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 := by
  have hprim := isPrimitive_inv hχ
  have hρ0 : ρ ≠ 0 := fun h => by
    rw [h] at h0
    simp at h0
  have h1ρ : (1 - ρ) ≠ 0 := fun h => by
    have e := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at e
    linarith
  have hg : DirichletCharacter.gammaFactor χ ρ ≠ 0 := by
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact Complex.Gammaℝ_ne_zero_of_re_pos h0
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, Complex.one_re]; linarith)
  have hc : DirichletCharacter.completedLFunction χ ρ = 0 := by
    have e := DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ := χ) ρ (Or.inl hρ0)
    rw [hz, eq_comm, div_eq_zero_iff] at e
    exact e.resolve_right hg
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ := χ⁻¹) (1 - ρ) (Or.inl h1ρ),
    hprim.completedLFunction_one_sub ρ, inv_inv, hc]
  simp


def GoodAll (Q : ℝ) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ f M → GoodFor Q χ

def BoundsII (x eps C : ℝ) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ f M →
    ‖gChi χ x‖ ≤ x ^ ((1 : ℝ) / 2 + eps) ∧ ‖logDerivativeAtOne χ‖ ≤ C * Real.log x

def ChoiceOfModulusAndDiscriminant (n : ℕ) (x eps C : ℝ) (q d : ℕ) : Prop :=
  q.Prime ∧ q % 8 = 3 ∧ Real.sqrt (X1 x eps) < q ∧ (q : ℝ) ≤ X1 x eps ∧
  d.Prime ∧ d % 16 = 7 ∧ Real.sqrt (X2 x eps) < d ∧ (d : ℝ) ≤ X2 x eps ∧
  kronSym (-(d : ℤ)) q = 1 ∧ (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (eps / 5) → kronSym (-(d : ℤ)) p = 1) ∧

  GoodAll (8 * X1 x eps) (psDir q) (8 * q * d) ∧
  GoodAll (8 * X1 x eps) (fun a => chi8 a * psDir q a) (8 * q * d) ∧
  GoodAll (8 * X1 x eps * X2 x eps) (chDir d) (8 * q * d) ∧
  GoodAll (8 * X1 x eps * X2 x eps) (fun a => chi8 a * chDir d a) (8 * q * d) ∧
  GoodAll (8 * X1 x eps * X2 x eps) (fun a => chDir d a * psDir q a) (8 * q * d) ∧
  GoodAll (8 * X1 x eps * X2 x eps) (fun a => chi8 a * chDir d a * psDir q a) (8 * q * d) ∧

  BoundsII x eps C (psDir q) (8 * q * d) ∧ BoundsII x eps C (chDir d) (8 * q * d) ∧
  BoundsII x eps C (fun a => chDir d a * psDir q a) (8 * q * d) ∧

  Real.log (4 * n * q * d) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2

def PairAt (Y eps : ℝ) (q d : ℕ) : Prop :=
  q.Prime ∧ q % 8 = 3 ∧ Real.sqrt (X1 Y eps) < q ∧ (q : ℝ) ≤ X1 Y eps ∧
  d.Prime ∧ d % 16 = 7 ∧ Real.sqrt (X2 Y eps) < d ∧ (d : ℝ) ≤ X2 Y eps ∧
  kronSym (-(d : ℤ)) q = 1 ∧ (∀ p : ℕ, p.Prime → (p : ℝ) ≤ Y ^ (eps / 5) → kronSym (-(d : ℤ)) p = 1)

def PropTwoSixBoxHypothesis (D : D7) (x eps : ℝ) : Prop :=
  (∃ Y : ℝ, 1 < Y ∧ Y ≤ x ∧ BoxE D Y eps) ∧ Real.log (NE D) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2

def PropTwoSixThinScales (D : D7) (x eps c : ℝ) : Prop :=
  PropTwoSixBoxHypothesis D x eps →
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), IsCharED D χ →
    ∀ y : ℝ, Real.exp (x ^ (eps / 3)) / 3 ≤ y → ‖gChi χ y‖ ≤ y * Real.exp (-(c * x ^ (eps / 8)))

section Family

variable {eps : ℝ}

def FamilySixthHypothesis (Fm : FamP eps) : Prop :=
  ∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧ ∀ x > 1, ∀ i : Fm.Ix x, adm6 (Fm.D x i) C1 c
def adm7F (Fm : FamP eps) : Prop := ∃ C : ℝ, 0 < C ∧ ∀ x > 1, ∀ i : Fm.Ix x, adm7 (Fm.D x i) C
def ComplementTwoFamily (Fm : FamP eps) : Prop := ∃ C : ℝ, 0 < C ∧ ∀ x > 1, ∀ i : Fm.Ix x, adm11 (Fm.D x i) C

def FamilyPropTwoSixCongruenceForm (Fm : FamP eps) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, PropTwoSixThinScales (Fm.D x i) x eps c

end Family

end Formalism.MainNotions.ShortIntervalPrimes

end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
section
noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions Finset
open scoped Pointwise ComplexConjugate

open Classical

abbrev Chr (D : D7) : Type := D.R.GG →* ℂˣ

def sgnC : ℤˣ →* ℂˣ := Units.map (Int.castRingHom ℂ).toMonoidHom

abbrev chC (D : D7) : Chr D := D.R.chC

def psC (D : D7) : Chr D := sgnC.comp D.R.chQ

def Unram (D : D7) (p : ℕ) : Prop := p.Prime ∧ ¬ ((p : ℤ) ∣ discr D.host.E)

def InertK (D : D7) (p : ℕ) : Prop :=
  p.Prime ∧ (D.host.cls p = PrimeClass.signal ∨ D.host.cls p = PrimeClass.inertClass)

def Reads (D : D7) (ψ : Chr D) (χ : Σ N : ℕ+, DirichletCharacter ℂ N) : Prop :=
  χ.2.IsPrimitive ∧ ∀ p : ℕ, Unram D p → χ.2 (p : ZMod χ.1) = ((ψ (frob D p) : ℂˣ) : ℂ)

def prim (D : D7) (ψ : Chr D) : Σ N : ℕ+, DirichletCharacter ℂ N :=
  if h : ∃ χ, Reads D ψ χ then h.choose else ⟨1, 1⟩

def Gc (D : D7) (ψ : Chr D) (y : ℝ) : ℂ := gChi (prim D ψ).2 y

def Lp (D : D7) (ψ : Chr D) : ℂ := logDerivativeAtOne (prim D ψ).2

def iner (D : D7) : D.R.GG := (sgc0, 1)

def askP (D : D7) (a : ℝ) (w : D.R.GG → ℝ) (τ : D.R.GG) (p : ℕ) : ℝ :=
  ∑' i : ℕ, if 1 ≤ i ∧ frob D p ^ i ∉ D.R.Psi then
    max (a / (p : ℝ) ^ i - w (rho D τ (frob D p ^ i))) 0 else 0

def gD (D : D7) (i : ℕ) : D.R.GG :=
  if frob D D.host.d ^ i ∉ D.R.Psi then frob D D.host.d ^ i else frob D D.host.d ^ i * iner D

def askD (D : D7) (a : ℝ) (w : D.R.GG → ℝ) (τ : D.R.GG) : ℝ :=
  ∑' i : ℕ, if 1 ≤ i then max (a / (D.host.d : ℝ) ^ i - w (rho D τ (gD D i))) 0 else 0

def ASKjt (D : D7) (a : ℝ) (w : D.R.GG → ℝ) (τ : D.R.GG) : ℝ :=
  (∑' p : ℕ, if InertK D p then 2 * Real.log p * askP D a w τ p else 0) +
    Real.log D.host.d * askD D a w τ

def adm5 (D : D7) (s : Scale) (c : ℝ) : Prop :=
  ∀ ψ : Chr D, ∀ y : ℝ, s.X' / 3 ≤ y → ‖Gc D ψ y‖ ≤ y * Real.exp (-(c * s.x ^ (s.eps / 8)))

def adm10 (D : D7) : Prop := ∀ ψ : Chr D, ∃ χ, Reads D ψ χ

def SizesAt (D : D7) (s : Scale) (δ : ℝ) : Prop :=
  s.x ^ (2 + 8 * s.eps - δ) ≤ (D.R.n : ℝ) ∧ (D.R.n : ℝ) ≤ s.x ^ (2 + 8 * s.eps + δ) ∧
  (s.x * s.delta1) ^ ((1 : ℝ) / 2 - δ) ≤ (D.R.m : ℝ) ∧
    (D.R.m : ℝ) ≤ (s.x * s.delta1) ^ ((1 : ℝ) / 2 + δ) ∧
  s.x ^ ((9 : ℝ) / 2 + 10 * s.eps - δ) ≤ (D.R.k : ℝ) ∧
    (D.R.k : ℝ) ≤ s.x ^ ((9 : ℝ) / 2 + 10 * s.eps + δ)

end Formalism.MainNotions.ZetaZeroFreeRegion

end
end

