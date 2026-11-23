module

public import Mathlib
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalRingCardinality.Bundle0002
public import Formalism.LocalRingCardinality.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalRingCardinality.DataDIVDefs
section
noncomputable section

namespace Formalism.BasicNotions.DV

open Formalism.BasicNotions NumberField IsDedekindDomain

def MramL (D : D7) (u : D.what₂.Word) : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V :=
  ((D.fm u).lat 0).L.comap ((D.nuIn u).restrictScalars (𝓞 D.what₂.LL))

def ur (D : D7) (w : D.what₂.places.Pl) (y : ℝ) : ℝ := (D.what₂.places.ramIdx w : ℝ) * y

def Iu (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL :=
  ∏ w ∈ L.supp, ((D.plEq w).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^
    (-(⌊ur D w (L.sg u w)⌋))

def NprimeDef (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u, (D.div.Nu u).L = Submodule.span (𝓞 D.what₂.LL)
    {x | ∃ a ∈ Iu D L u, ∃ y ∈ L.NuLat u, x = (a : D.what₂.LL) • y}

def RRDef (D : D7) : Prop :=
  ∀ x : D.div.RR.V, x ∈ D.div.RR.L ↔ ∀ w : D.what₂.places.Pl, ∃ d : 𝓞 D.what₂.LL,
    d ∉ (D.plEq w).asIdeal ∧
    d • x ∈ Submodule.span (𝓞 D.what₂.LL) {y | D.jEE y ∈ D.what₂.RRset (D.what₂.muAt w)}

def LocLe {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (k : ℕ) (A B : Submodule (𝓞 K) V) : Prop :=
  ∀ x ∈ A, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ (w.asIdeal ^ k) • B

def LocEq {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : Prop :=
  LocLe w 0 A B ∧ LocLe w 0 B A

def lenLoc {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : ℕ∞ :=
  letI : w.asIdeal.IsPrime := w.isPrime
  Module.length (Localization.AtPrime w.asIdeal)
    (LocalizedModule w.asIdeal.primeCompl (↥B ⧸ A.comap B.subtype))

def InertK (D : D7) (p : ℕ) : Prop :=
  D.host.cls p = PrimeClass.signal ∨ D.host.cls p = PrimeClass.inertClass

def NuDef (D : D7) (L : SizeData₂ D) : Prop :=
  (∀ u w, D.what₂.places.resChar w ≠ (D.mem u).A.T → LocLe (D.plEq w) 0 (L.NuLat u) (MramL D u)) ∧
  (∀ u w, D.what₂.places.resChar w ≠ (D.mem u).A.T →
    (D.what₂.places.resChar w ∈ L.drop ∨ ¬ InertK D (D.what₂.places.resChar w)) →
      LocEq (D.plEq w) (L.NuLat u) (MramL D u)) ∧
  (∀ u w, ∀ l : ℕ, lenLoc (D.plEq w) (L.NuLat u) (MramL D u) = l →
    (l : ℝ) = (L.lenMN u w : ℝ) * (D.what₂.places.ramIdx w : ℝ))

def meanE (D : D7) (g : (D.what₂.LL →+* ℂ) → ℝ) : ℝ :=
  (∑ σ, g σ) / (Module.finrank ℚ D.what₂.LL : ℝ)

def wSz (D : D7) (j : ℕ) (ρ : D.what₂.Tau) : ℝ :=
  if h : 1 ≤ j ∧ j ≤ D.R.m then (((D.hc ρ).e ⟨j - 1, by omega⟩ : ℚ) : ℝ) else 0

def srcPar (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) : ℚ :=
  if h : i < D.R.k then (D.hcW u τ).u ⟨i, h⟩
  else
    if hb : (i - D.R.k) / (D.R.t + 1) < D.R.m then
      -(D.hcW u τ).e ⟨(i - D.R.k) / (D.R.t + 1), hb⟩ +
        ((D.R.t : ℚ) + 2 - 2 * (((i - D.R.k) % (D.R.t + 1) + 1 : ℕ) : ℚ)) / 2
    else 0

def nuRow (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℝ :=
  ((srcPar D u τ i : ℚ) : ℝ) + wSz D j τ -
    (((D.R.N (j - 1) : ℝ) + D.R.N j - 1 - 2 * (i : ℝ)) / 2)

def kerPlace (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) : ℝ :=
  (∑ i ∈ Finset.range (D.R.N (j - 1)), phF (nuRow D u j τ i)) -
    (∑ i ∈ Finset.range (D.R.N (j - 1)), nuRow D u j τ i) * L.logOm

def SZbP (D : D7) (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) : ℝ :=
  -(∑ t : D.host.TT, (L.aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ)) +
    C * ((D.host.TT.card : ℝ) * L.sc.b' * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * ((D.R.m : ℝ) * L.etaSz + L.Sc) * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2) * L.La

end Formalism.BasicNotions.DV

namespace Formalism.BasicNotions

open Formalism.MainNotions.G

end Formalism.BasicNotions

end
end

-- bundled from Formalism.LocalRingCardinality.DataParamsT
section
noncomputable section

namespace Formalism.BasicNotions

open NumberField LevelStarExponents

def logdE (D : D7) : ℝ := Real.log |((discr D.host.E : ℤ) : ℝ)|

def zBase {D : D7} (L : SizeData₂ D) : ℝ := (D.R.f : ℝ) * (D.R.r : ℝ) * L.sc.L

structure ParamsT (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) : Type where

  TO : ℕ

  nWn : ℕ

  nP : ℕ

  PP : ℝ

  Dp : ℕ

  s : ℕ

  CP : ℝ
  one_le_CP : 1 ≤ CP

  eP : ℝ
  eP_ge : 12 ≤ eP

  Cp : ℝ
  Cp_ge : 1 ≤ Cp

  Cb : ℝ
  Cb_nonneg : 0 ≤ Cb

  cTO : ℝ

  ChT : ℝ
  ChT_ge : 1 ≤ ChT

  CbN : ℝ
  CbN_ge : 1 ≤ CbN

  PP_eq : PP = CP * zBase L ^ eP

  Dp_eq : Dp = D.R.f * D.R.r.choose 2

  PP_poly : PP ≤ L.sc.x ^ L.Ct
  Dp_poly : (Dp : ℝ) ≤ L.sc.x ^ L.Ct
  TO_poly : (TO : ℝ) ≤ L.sc.x ^ L.Ct

  nW_win : nW L P.CnW ≤ (nWn : ℝ) ∧ (nWn : ℝ) < nW L P.CnW + 8
  nW_dvd : 8 ∣ nWn

  PP_nW : (2 * (D.R.f : ℝ) * D.R.m) ^ 4 * (nWn : ℝ) ≤ PP

  nW_le : (nWn : ℝ) ≤ PP

  nW_lo : D.R.f * D.R.r * (D.R.r + 1) ≤ nWn ∧ (D.R.k - 1) * D.R.f + 2 * D.R.r ≤ nWn ∧ nP ≤ nWn

  split : D.R.r + D.R.t = nP + TO * nWn
  nP_eq : nP = 8 * D.R.f * D.R.r + 4

  TO_eq : TO = ⌈L.sc.x ^ cTO⌉₊

  TO_ge : PP ^ 4 * (Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ Cp / ((D.R.m : ℝ) * L.de2) ≤ (TO : ℝ)

  TO_PP : (TO : ℝ) * PP * L.sc.x ^ Cb ≤ L.sc.b

  TO_nW : (Dp + 2) * nWn + 2 * D.R.r ≤ TO

  TO_40 : 40 * (Dp + 2) ≤ TO

  TO_11D2 : 11 * Dp ^ 2 ≤ TO

  order_ge_rank_bound : D.R.r + 2 * (2 * 5 ^ 4 * D.R.r) * (Dp + 1) ≤ TO

  TO_PP' : (TO : ℝ) * PP ≤ L.sc.b ^ (1 / 2 : ℝ)

  precision_cube_order_sq_le : PP ^ 3 * (TO : ℝ) ^ 2 * L.sc.x ^ Cb ≤ L.sc.b

  precision_cube_order_sq_le_sqrt : PP ^ 3 * (TO : ℝ) ^ 2 ≤ L.sc.b ^ (1 / 2 : ℝ)

  TO_Dk : (Dp : ℝ) * D.R.k / D.R.m ≤ (TO : ℝ)

  Del_TO : ((TO : ℝ)) ^ 2 ≤ ((D.s.Del : ℚ) : ℝ)

  Del_gap : ((TO : ℝ) + Dp + 2) * ((TO : ℝ) + Dp + 2 + 2 * (D.R.N D.R.m : ℝ)) ≤ ((D.s.Del : ℚ) : ℝ)

  heightBound_ge_order_sq : 4 * (TO : ℝ) ^ 2 + 2 * D.R.t ≤ h0 L

  heightBound_ge_precision_degree : PP * Dp * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) * TO ≤ h0 L

  heightBound_ge_precision_cubic : PP * ((D.R.f : ℝ) * D.R.m * D.R.k) ^ 3 * D.R.k / D.R.m ≤ h0 L

  heightBound_ge_order_product : ChT * TO * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * Dp * PP ≤ h0 L

  log_bound_le_sqrt : (TO : ℝ) * (Dp : ℝ) ^ 2 * Real.log L.sc.b * L.sc.x ^ Cb ≤ L.sc.b

  TD2' : (TO : ℝ) * (Dp : ℝ) ^ 2 * Real.log L.sc.b ≤ L.sc.b ^ (1 / 2 : ℝ)

  b_ge : CbN * (D.R.r : ℝ) * D.R.m * D.R.k * PP ^ 2 * (Dp : ℝ) ^ 3 ≤ L.sc.b

  s_odd : Odd s
  s_lo : D.R.r + 5 < s
  s_hi : s ≤ D.R.r + 7

theorem ParamsT.Cp_nonneg {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : 0 ≤ T.Cp :=
  le_trans zero_le_one T.Cp_ge

theorem ParamsT.nW_40 {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : 40 ≤ T.nWn := by
  have hf : 2 ≤ D.R.f := by
    have := D.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hr : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have h3 : 2 * 6 * (6 + 1) ≤ D.R.f * D.R.r * (D.R.r + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul hf hr) (by omega)
  exact le_trans (by norm_num) (le_trans h3 T.nW_lo.1)

theorem ParamsT.nW_even {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : Even T.nWn :=
  (even_iff_two_dvd.2 (Dvd.dvd.trans (by norm_num) T.nW_dvd))

theorem ParamsT.nP_ge {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    8 * D.R.f * D.R.r + 4 ≤ T.nP := T.nP_eq.ge

theorem ParamsT.four_dvd_nP {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : 4 ∣ T.nP := by
  rw [T.nP_eq]; exact ⟨2 * D.R.f * D.R.r + 1, by ring⟩

theorem ParamsT.even_nP₂ {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : Even T.nP :=
  even_iff_two_dvd.2 (Dvd.dvd.trans (by norm_num) T.four_dvd_nP)

theorem ParamsT.PP_pos {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P)
    (hZ : 0 < zBase L) : 0 < T.PP := by
  rw [T.PP_eq]; have := T.one_le_CP; positivity

end Formalism.BasicNotions

end
end

-- bundled from Formalism.LocalRingCardinality.DataTies
section
open MeasureTheory Matrix Formalism.MainNotions.S

noncomputable section

namespace Formalism.BasicNotions

def cdScaleTie (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      ((D.s.cdScale n ε : ENNReal) • Formalism.REAL.muG ε) A =
        D.cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}

def dsigTie (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)) (d : ℝ),
    IsDS (epsSH D.R) (lamSH D.R (D.hc τ)) σ →
    IsFdeg ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) σ d → d = D.dsig τ

def TwCoverPair (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥D.LL0),
    ((p : ℕ) : NumberField.RingOfIntegers ↥D.LL0) ∈ w.asIdeal →
    (∃ w' : D.what₂.places.Pl, D.what₂.muAt w' ≠ D.what₂.mu0 ∧
      ∀ x : NumberField.RingOfIntegers ↥D.LL0, x ∈ w.asIdeal ↔ 0 < D.what₂.places.val w' ((x : ↥D.LL0) : D.what₂.LL)) →
    ∃ i, D.ntw.l i = p ∧
      ((∀ x : NumberField.RingOfIntegers ↥D.LL0, x ∈ w.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
          algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : ↥D.LL0)) ∨
       (∀ x : NumberField.RingOfIntegers ↥D.LL0, x ∈ w.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
          algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0b i (x : ↥D.LL0)))

structure Ties (D : D7) : Prop where
  cdScale_tie : cdScaleTie D
  dsig_tie : dsigTie D

  bu_def : Rows.BuDefQ D.what₂

  tw_cover : TwCoverPair D

  baseField_isGalois : IsGalois ℚ ↥D.LL0

  ft_occ : ∀ π, (∃ σ, D.what₂.ft σ = π) ∨ ∃ σ, D.what₂.ft0 σ = π

def GoodFTAll (D : Formalism.BasicNotions.D7) : Prop := ∀ σ, D.nd.goodRow σ

end Formalism.BasicNotions

end
end

