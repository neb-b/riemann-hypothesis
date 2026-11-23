module

public import Mathlib
public import Formalism.QuotientMetricDivisors.StatementK
public import Formalism.QuotientMetricDivisors.RatHermLcvTwist
public import Formalism.QuotientMetricDivisors.Bundle0003
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.QuotientMetricDivisors.Bundle0002
public import Formalism.QuotientMetricDivisors.Bundle0004

@[expose] public section

-- bundled from Formalism.QuotientMetricDivisors.ScalarLiftLowerBoundFull
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.DivisionValues

def DivIneqRecord : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (muC mu0 Fo hu hP mlam logT : ℝ) (hK : J → ℝ) (aT : Pl → ℝ) (phν nν fa : J → Pl → ℝ)
    (x eps L b a rd La B0 Nc m f k N S tt η w'' b' lam0 C0 ce : ℝ)
    (Lpass Eb e6 eP logOm : ℝ) (eK pq : J → ℝ) (w eE δ : J → Pl → ℝ),
    muC ≤ mu0 + Lpass →
    mu0 ≤ ∑ j, ∑ ρ, pq j * w j ρ * logOm + 2 * Fo + Eb →
    hu = hP + ∑ j, hK j - mlam →
    (∀ j, hK j ≤ ∑ ρ, (phν j ρ - nν j ρ * logOm) + eK j) →
    ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, aT t * logT) + eP →
    (∀ j ρ, phν j ρ - fa j ρ ≤ (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ) else 0) + eE j ρ) →
    (∀ j ρ, nν j ρ = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ) →
    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →
    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →
    B0 = f * m * b * x ^ eps → 0 ≤ Nc →
    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →
    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ tt → 0 ≤ η →
    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →
    (∀ j, |pq j - k| ≤ m) → |logOm| ≤ La →
    m * lam0 ≤ b → N ^ 2 ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (tt + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →

    1 ≤ C0 → C0 ≤ ce →
    Lpass ≤ 1 + C0 * (m * lam0) →
    Eb ≤ ce * m * (x ^ eps * B0 + (Real.log x) ^ 2 * Nc) →
    (∀ j, eK j ≤ C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (tt + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (tt + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, (m * (Formalism.LatticeIndexTer.ph (aT t) - aT t * logOm) - aT t * logT) +
        ((50 * C0 + 10) * ((TT.card : ℝ) * a * La) +
          60 * ce * (m * (x ^ eps * B0 + (Real.log x) ^ 2 * Nc)))

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.TheoremDivIneqRowsShift
section
open Finset

noncomputable section

namespace Formalism.DivisionValues

def RowsStepEShift : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (n : ℕ) (aT : Pl → ℕ) (w wr : J → Pl → ℕ) (ν ap : J → Pl → Multiset ℕ) (fa : J → Pl → ℝ)
    (a rd La k N S Sc t η m b' cs C1 C0 : ℝ),

    La = Real.log (a * rd) → 1 ≤ La → k = (n : ℝ) + 2 → k ≤ N → 0 ≤ b' → 0 ≤ cs → 0 ≤ S →

    2 ≤ C1 → cs + 1 ≤ C1 → 2 * Sc ≤ C1 * S → C1 + cs ≤ C0 →

    (∀ j ρ, wr j ρ ≤ w j ρ) → (∀ j ρ, (w j ρ : ℝ) - (wr j ρ : ℝ) ≤ cs * N) →

    (∀ j ρ, (w j ρ : ℝ) + Sc ≤ a * rd) → m * (t + 1) * η ≤ a * rd → 0 ≤ m * (t + 1) * η →
    (∀ j, ∀ ρ ∈ TT, (aT ρ : ℝ) + (w j ρ : ℝ) ≤ a * rd) →

    (∀ j ρ, logFactRows (ap j ρ) ≤ fa j ρ) →

    (∀ j, ∀ ρ, ρ ∉ TT →
      IsRowsOff (n + 1) (wr j ρ) Sc (m * (t + 1) * η) (cs * N) (ν j ρ) (ap j ρ)) →
    (∀ j, ∀ ρ ∈ TT,
      IsRowsTop n (aT ρ) (wr j ρ) Sc (m * (t + 1) * η) (cs * N) (ν j ρ) (ap j ρ)) →
    ∃ eE δ : J → Pl → ℝ,
      (∀ j ρ, phRows (ν j ρ) - fa j ρ ≤
        (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ : ℝ) else 0) + eE j ρ) ∧
      (∀ j ρ, ((ν j ρ).sum : ℝ) = (if ρ ∈ TT then (aT ρ : ℝ) else 0) + k * (w j ρ : ℝ) + δ j ρ) ∧
      (∀ j ρ, eE j ρ ≤ C0 * ((w j ρ : ℝ) + S + N ^ 2 + m * (t + 1) * η) * La) ∧
      (∀ j ρ, |δ j ρ| ≤
        C0 * ((w j ρ : ℝ) + k * (N + S) + m * (t + 1) * η + (if ρ ∈ TT then k * b' else 0)))

def originRow (k t j w u i : ℝ) : ℝ :=
  (u + w) - ((k + (j - 1) * (t + 1)) + (k + j * (t + 1)) + 1 - 2 * i) / 2

def originBig (k m t j w v i : ℝ) : ℝ :=
  (v + w) - (((k - 1 + m) + t) + 1 - 2 * i) / 2 - ((k - 1 + j) - (m - j)) / 2

def RowsOriginOff : Prop :=
  ∀ (n j t w s wr : ℕ) (m Sc Bl sh : ℝ) (u : Fin (n + 2) → ℝ) (v : Fin (n + 1) → ℝ)
    (νr : Fin (n + 2) → ℕ) (ar : Fin (n + 1) → ℕ) (blk sm : Multiset ℕ),
    1 ≤ j → (s : ℝ) = (((n : ℝ) + 2) + (2 * (j : ℝ) - 1) * ((t : ℝ) + 1)) / 2 → wr + s = w →
    (∀ i, (νr i : ℝ) = originRow ((n : ℝ) + 2) t j w (u i) ((i : ℕ) + 1)) →
    (∀ i, (ar i : ℝ) = originBig ((n : ℝ) + 2) m t j w (v i) ((i : ℕ) + 1)) →
    (∀ i : Fin (n + 1), v i < u i.castSucc ∧ u i.succ < v i) →
    0 ≤ u (Fin.last (n + 1)) + (((n : ℝ) + 2) - 1) / 2 → u 0 - (((n : ℝ) + 2) - 1) / 2 ≤ Sc →
    ((j : ℝ) - 1) * (t : ℝ) ≤ sh → (blk.sum : ℝ) ≤ Bl →
      IsRowsOff (n + 1) wr Sc Bl sh (Finset.univ.val.map νr + blk) (Finset.univ.val.map ar + sm)

def RowsOriginTop : Prop :=
  ∀ (n j t w s wr aT bT : ℕ) (m Sc Bl sh : ℝ) (u : Fin (n + 2) → ℝ) (v : Fin (n + 1) → ℝ)
    (νr : Fin (n + 2) → ℕ) (ar : Fin (n + 1) → ℕ) (blk sm : Multiset ℕ),
    1 ≤ j → (s : ℝ) = (((n : ℝ) + 2) + (2 * (j : ℝ) - 1) * ((t : ℝ) + 1)) / 2 → wr + s = w →
    (∀ i, (νr i : ℝ) = originRow ((n : ℝ) + 2) t j w (u i) ((i : ℕ) + 1)) →
    (∀ i, (ar i : ℝ) = originBig ((n : ℝ) + 2) m t j w (v i) ((i : ℕ) + 1)) →
    (∀ i : Fin (n + 1), v i < u i.castSucc ∧ u i.succ < v i) →
    u 0 = (aT : ℝ) + (((n : ℝ) + 2) - 1) / 2 → u (Fin.last (n + 1)) = -(bT : ℝ) - (((n : ℝ) + 2) - 1) / 2 →
    0 ≤ v (Fin.last n) + (((n : ℝ) + 2) - 2) / 2 → v 0 - (((n : ℝ) + 2) - 2) / 2 ≤ Sc →
    ((j : ℝ) - 1) * (t : ℝ) ≤ sh → (blk.sum : ℝ) ≤ Bl →
      IsRowsTop n aT wr Sc Bl sh (Finset.univ.val.map νr + blk) (Finset.univ.val.map ar + sm)

def RowsStepEOrigin : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (n t : ℕ) (jj s : J → ℕ) (aT bT : Pl → ℕ) (w : J → Pl → ℕ)
    (u : Pl → Fin (n + 2) → ℝ) (v : Pl → Fin (n + 1) → ℝ)
    (νr : J → Pl → Fin (n + 2) → ℕ) (ar : J → Pl → Fin (n + 1) → ℕ) (blk sm : J → Pl → Multiset ℕ)
    (ν ap : J → Pl → Multiset ℕ) (fa : J → Pl → ℝ)
    (a rd La k N S Sc η m b' C1 C0 : ℝ),

    La = Real.log (a * rd) → 1 ≤ La → k = (n : ℝ) + 2 → 0 ≤ m → k + m * ((t : ℝ) + 1) ≤ N →
    0 ≤ b' → 0 ≤ S →

    2 ≤ C1 → 2 * Sc ≤ C1 * S → C1 + 1 ≤ C0 →

    (∀ j, 1 ≤ jj j) → (∀ j, (jj j : ℝ) ≤ m) →
    (∀ j, (s j : ℝ) = (k + (2 * (jj j : ℝ) - 1) * ((t : ℝ) + 1)) / 2) → (∀ j ρ, s j ≤ w j ρ) →

    (∀ j ρ, (w j ρ : ℝ) + Sc ≤ a * rd) → m * ((t : ℝ) + 1) * η ≤ a * rd → 0 ≤ m * ((t : ℝ) + 1) * η →
    (∀ j, ∀ ρ ∈ TT, (aT ρ : ℝ) + (w j ρ : ℝ) ≤ a * rd) →

    (∀ j ρ, logFactRows (ap j ρ) ≤ fa j ρ) →

    (∀ j ρ, ν j ρ = Finset.univ.val.map (νr j ρ) + blk j ρ) →
    (∀ j ρ, ap j ρ = Finset.univ.val.map (ar j ρ) + sm j ρ) →
    (∀ j ρ i, (νr j ρ i : ℝ) = originRow k t (jj j) (w j ρ) (u ρ i) ((i : ℕ) + 1)) →
    (∀ j ρ i, (ar j ρ i : ℝ) = originBig k m t (jj j) (w j ρ) (v ρ i) ((i : ℕ) + 1)) →
    (∀ j ρ, ((blk j ρ).sum : ℝ) ≤ m * ((t : ℝ) + 1) * η) →

    (∀ ρ, ∀ i : Fin (n + 1), v ρ i < u ρ i.castSucc ∧ u ρ i.succ < v ρ i) →
    (∀ ρ, ρ ∉ TT → 0 ≤ u ρ (Fin.last (n + 1)) + (k - 1) / 2 ∧ u ρ 0 - (k - 1) / 2 ≤ Sc) →
    (∀ ρ ∈ TT, u ρ 0 = (aT ρ : ℝ) + (k - 1) / 2 ∧ u ρ (Fin.last (n + 1)) = -(bT ρ : ℝ) - (k - 1) / 2 ∧
      0 ≤ v ρ (Fin.last n) + (k - 2) / 2 ∧ v ρ 0 - (k - 2) / 2 ≤ Sc) →
    ∃ eE δ : J → Pl → ℝ,
      (∀ j ρ, phRows (ν j ρ) - fa j ρ ≤
        (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (aT ρ : ℝ) else 0) + eE j ρ) ∧
      (∀ j ρ, ((ν j ρ).sum : ℝ) = (if ρ ∈ TT then (aT ρ : ℝ) else 0) + k * (w j ρ : ℝ) + δ j ρ) ∧
      (∀ j ρ, eE j ρ ≤ C0 * ((w j ρ : ℝ) + S + N ^ 2 + m * ((t : ℝ) + 1) * η) * La) ∧
      (∀ j ρ, |δ j ρ| ≤
        C0 * ((w j ρ : ℝ) + k * (N + S) + m * ((t : ℝ) + 1) * η + (if ρ ∈ TT then k * b' else 0)))

end Formalism.DivisionValues
end
end

