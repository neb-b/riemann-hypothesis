module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
public import Formalism.LandauZeroFreeBounds.Statement
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsBranchingCoordinatesIff
section
noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

variable {D : D7} {u : D.what₂.Word}

structure Pend (X : Ch D u) where

  br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ)

  coM : D.what₂.places.Pl → X.fm.clsP → ((X.C.Y D.R.m → ℂ) →ₗ[ℂ]
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)

  coP : D.what₂.places.Pl → (X.P.Wrow →ₗ[ℂ] (X.fm.clsP →
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))

  coM_mem : ∀ w c, ∀ φ ∈ X.fm.Fi D.R.m, coM w c (φ (X.fm.til c)) ∈ CSpan (X.fm.lam D.R.m)

  coM_inj : ∀ w c, ∀ φ ∈ X.fm.Fi D.R.m, coM w c (φ (X.fm.til c)) = 0 → φ (X.fm.til c) = 0

  coP_mem : ∀ w, ∀ z ∈ X.fm.ptC, ∀ c, coP w z c ∈ CSpan X.fm.sg

  coP_inj : ∀ w, ∀ z ∈ X.fm.ptC, coP w z = 0 → z = 0

  Pt_eq : ∀ w, ∀ φ ∈ X.fm.Fi D.R.m, ∀ c,
    coP w (Pt X φ) c = blk (fun τ => br τ) (coM w c (φ (X.fm.til c)))

  lat_co : ∀ w, ∀ x ∈ X.fm.S D.R.m w, ∀ c,
    coM w c (X.fm.emb D.R.m x (X.fm.til c)) ∈ IntSpan D w (X.fm.lam D.R.m)

  pt_co : ∀ w, ∀ z ∈ X.fm.ptC, (∃ y ∈ X.fm.SP w, X.fm.ptEmb y = z) ↔ ∀ c, coP w z c ∈ IntSpan D w X.fm.sg

  gP : D.what₂.places.Pl → X.fm.clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ

  ipV_co : ∀ w c, ∀ φ ∈ X.fm.Fi D.R.m, (X.fm.ipV D.R.m (X.fm.til c) (φ (X.fm.til c)) (φ (X.fm.til c))).re =
    (nfAll (X.fm.lam D.R.m)
      (blk (fun τ => sqAct ℂ _ (lamTr X τ) (gFull X (gP w c τ))) (coM w c (φ (X.fm.til c))))
      (blk (fun τ => sqAct ℂ _ (lamTr X τ) (gFull X (gP w c τ))) (coM w c (φ (X.fm.til c))))).re

  re_petersson_self_eq_sum_coord : ∀ w, ∀ z ∈ X.fm.ptC, (X.fm.ipP z z).re = ∑ c, ((Nat.card (X.fm.stabilizer₂ c) : ℝ))⁻¹ *
    (nfAll X.fm.sg (blk (fun τ => sqAct ℂ _ (sgTr X τ) (gP w c τ)) (coP w z c))
      (blk (fun τ => sqAct ℂ _ (sgTr X τ) (gP w c τ)) (coP w z c))).re

  beOn_eq : ∀ τ, X.fm.beOn τ = opNorm X τ (br τ)

  interlace : X.fm.SgInterlace

variable {X : Ch D u}

def ArchimedeanSignatureMatching (P : Pend X) : Prop :=
  ∀ τ, Formalism.MainNotions.PrimeDegreeVariant.IsBr (Nm_succ D.R) (lamTr X τ) (sgTr X τ) (P.br τ)

theorem delSq_lamTr (X : Ch D u) (R : Type) [CommRing R] (τ : D.what₂.Tau) :
    delSq R _ (lamTr X τ) = delSq R _ (X.fm.lam D.R.m τ) := by
  unfold lamTr delSq
  rw [Formalism.MainNotions.product_first_zeroth_parts.natW_wSh]

theorem degZ_tr (X : Ch D u) (τ : D.what₂.Tau) : Formalism.MainNotions.PrimeDegreeVariant.degZ (lamTr X τ) (sgTr X τ) = X.fm.deg τ := by
  unfold Formalism.MainNotions.PrimeDegreeVariant.degZ lamTr sgTr
  unfold Formalism.BasicNotions.MemberForms.deg
  unfold Formalism.MainNotions.PrimeDegreeVariant.wsum wSh cTw
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN := Nm_succ D.R
  have hc : ((D.R.N D.R.m - 1 : ℕ) : ℤ) = (D.R.N D.R.m : ℤ) - 1 := by omega
  rw [hc]
  ring

theorem fockF_self_eq {σ : Type} (f : MvPolynomial σ ℂ) : Formalism.REAL.fockF f f =
    ((∑ m ∈ f.support, Complex.normSq (f.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
  unfold Formalism.REAL.fockF
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hc : f.coeff m * star (f.coeff m) = ((Complex.normSq (f.coeff m) : ℝ) : ℂ) := Complex.mul_conj _
  rw [hc, Complex.ofReal_mul, Complex.ofReal_natCast]

theorem fockF_self_pos {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : 0 < (Formalism.REAL.fockF f f).re := by
  rw [fockF_self_eq, Complex.ofReal_re]
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hf
  refine Finset.sum_pos (fun n hn => ?_) ⟨m, MvPolynomial.mem_support_iff.mpr hm⟩
  have h1 : f.coeff n ≠ 0 := MvPolynomial.mem_support_iff.mp hn
  have h2 : 0 < Complex.normSq (f.coeff n) := Complex.normSq_pos.mpr h1
  have h3 : (0 : ℝ) < ((∏ k ∈ n.support, (n k).factorial : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun k _ => Nat.factorial_pos _)
  exact mul_pos h2 h3

end GlobalTheory.LvT
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
section
noncomputable section

namespace GlobalTheory.NT

open Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory NumberField IsDedekindDomain ArithmeticFunction
open Formalism.HermitianLattices.GL2PrimeSums (Li PP)

def RayField : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L),
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 → UnramIn L 𝔭) ∧
      Subgroup.closure {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 ∧ IsFrob L 𝔭 σ} = ⊤ ∧
      ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 →
        ((∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = 1) ↔
          ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I * Ideal.span {β} = Ideal.span {α})

end GlobalTheory.NT

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
section
noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField

def Std (C : FC) : Prop :=
  C.Fixed ∧ C.Cc = 2 ∧ C.P.CLw = 11 * 405 ∧ C.P.Cj0 = 405 ∧ C.P.cw = 9 / 10 ∧ C.P.CYL = 9 ∧ C.P.CccK = 1 ∧
    C.T.Cp = 1 ∧ C.T.eP = 12 ∧ C.T.cTO = 377 ∧ C.CTu = 25 ∧ C.P.CetaF = 6 ∧ 1 ≤ C.P.Cpde ∧ 1000 ≤ C.T.CP ∧
    (∀ c ∈ C.cMid C.P.CF, 1 ≤ c) ∧ ∀ c ∈ C.cLast, 1 ≤ c

def TOv (s : Scale) : ℕ := ⌈s.x ^ (377 : ℝ)⌉₊

def nWv (R : Ranks) (s : Scale) : ℕ :=
  8 * ⌈10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8⌉₊

def h0v (s : Scale) (ch : ℝ) : ℕ := 2 * ⌈s.x ^ ch⌉₊

def Delv (s : Scale) (cD : ℝ) : ℕ := ⌈s.x ^ cD⌉₊

def Lwv (s : Scale) : ℕ := 10 * ⌈(405 : ℝ) * Real.log s.x⌉₊ + 2 * ⌈30 / s.eps⌉₊ + 22

def RankVal (s : Scale) (R : Ranks) : Prop :=
  (s.x ^ (2 + 8 * s.eps) ≤ (R.n : ℝ) ∧ (R.n : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps)) ∧
  (Real.sqrt (s.x * s.delta1) ≤ (R.m : ℝ) ∧ (R.m : ℝ) ≤ 2 * Real.sqrt (s.x * s.delta1)) ∧
  (s.x ^ (9 / 2 + 10 * s.eps) ≤ (R.k : ℝ) ∧ (R.k : ℝ) ≤ 2 * s.x ^ (9 / 2 + 10 * s.eps)) ∧
  R.r + R.t = 8 * R.f * R.r + 4 + TOv s * nWv R s

namespace RankVal

variable {s : Scale} {R : Ranks}

theorem n_lo (h : RankVal s R) : s.x ^ (2 + 8 * s.eps) ≤ (R.n : ℝ) := h.1.1
theorem n_up (h : RankVal s R) : (R.n : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps) := h.1.2

theorem n_le (h : RankVal s R) : (R.n : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps + s.eps / 100) := by
  have h2 : s.x ^ (2 + 8 * s.eps) ≤ s.x ^ (2 + 8 * s.eps + s.eps / 100) :=
    Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith [s.eps_pos])
  linarith [h.n_up]

theorem n_le_of_o (h : RankVal s R) {C : ℝ} (hC : (R.o : ℝ) ≤ C) : (R.n : ℝ) ≤ 2 * C * s.x ^ (2 + 8 * s.eps) := by
  have h0 : 0 < R.o := by
    rcases Nat.eq_zero_or_pos R.o with h0 | h0
    · have h1 := R.toFrame.ord_le_o_mul_two_pow
      have h2 := R.toFrame.ord_pos
      rw [h0] at h1
      omega
    · exact h0
  have h1 : (1 : ℝ) ≤ C := le_trans (by exact_mod_cast h0) hC
  have h2 : 0 ≤ s.x ^ (2 + 8 * s.eps) := Real.rpow_nonneg (by linarith [s.one_lt_alt]) _
  nlinarith [h.n_up]

theorem n_le' (h : RankVal s R) : (R.n : ℝ) ≤ 2 * s.x ^ ((9 : ℝ) / 4) := by
  have := s.eps_lt
  have h2 : s.x ^ (2 + 8 * s.eps + s.eps / 100) ≤ s.x ^ ((9 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith)
  linarith [h.n_le]

end RankVal

def PairWin (s : Scale) (Y : ℝ) : Prop := s.x ^ (1 / s.J) ≤ Y ∧ Y ≤ s.x

def PairRow (Y eps : ℝ) {R : Ranks} (H : Host R) : Prop :=
  H.q.Prime ∧ H.q % 8 = 3 ∧ Real.sqrt (GlobalTheoryTheory.X1 Y eps) < H.q ∧ (H.q : ℝ) ≤ GlobalTheoryTheory.X1 Y eps ∧
  H.d.Prime ∧ H.d % 16 = 7 ∧ Real.sqrt (GlobalTheoryTheory.X2 Y eps) < H.d ∧ (H.d : ℝ) ≤ GlobalTheoryTheory.X2 Y eps ∧
  GlobalTheoryTheory.kronSym (-(H.d : ℤ)) H.q = 1 ∧
  (∀ p : ℕ, p.Prime → (p : ℝ) ≤ Y ^ (eps / 5) → GlobalTheoryTheory.kronSym (-(H.d : ℤ)) p = 1) ∧
  Real.log (H.QS * H.q * H.d) ≤ 2 * Y ^ (eps / 5) * Real.log Y ^ 2

def HostConst (s : Scale) (C8 : ℝ) {R : Ranks} (H : Host R) : Prop :=
  s.J ≤ C8 ∧ (R.o : ℝ) ≤ C8 ∧ (H.QS : ℝ) ≤ C8 * R.n

def HostVal (s : Scale) (C8 : ℝ) {R : Ranks} (H : Host R) : Prop :=
  (∃ Y : ℝ, PairWin s Y ∧ PairRow Y s.eps H) ∧
  (s.delta1 * R.n / 2 ≤ (H.TT.card : ℝ) ∧ (H.TT.card : ℝ) ≤ 2 * s.delta1 * R.n) ∧
  s.x ^ (-s.eps) * R.n ≤ (H.T2.card : ℝ) ∧
  ((H.pde : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C8 ∧ (H.pde' : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C8) ∧
  (∀ i, ((R.k : ℝ) * s.b) ^ 8 ≤ (H.g i : ℝ) ∧ (H.g i : ℝ) ≤ 2 * ((R.k : ℝ) * s.b) ^ 8) ∧
  H.Lw = Lwv s ∧ H.ccK = ⊤ ∧ ⌊s.x ^ (s.ez / 5)⌋₊ ≤ H.splitBound ∧ HostConst s C8 H

def HostArith {R : Ranks} (H : Host R) : Prop :=
  (∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E)) ∧
  (∀ i, H.g i % (H.QS * H.q * H.d) = 1) ∧
  ((Ideal.primesOver (Ideal.span {(H.pde : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E ∧
    (Ideal.primesOver (Ideal.span {(H.pde' : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E) ∧
  ∀ p ∈ H.levelPrimes, H.cls p = .splitK

def HCVal (s : Scale) (cD ch : ℝ) {R : Ranks} (H : Host R) {Tau : Type} [Fintype Tau]
    (eTau : Tau → R.GG) (hc : Tau → HCParam R) (bT : H.TT → ℤ) : Prop :=
  (∀ τ (i : Fin (R.k - 1)), (hc τ).v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (Delv s cD : ℚ))) ∧
  (∀ τ (hk : 0 < R.k), eTau τ ∉ H.topPlaces →
    (hc τ).u ⟨0, hk⟩ = ((R.k - 2 : ℕ) : ℚ) * (4 * (Delv s cD : ℚ)) + (R.k : ℚ) * (4 * (Delv s cD : ℚ)) + 1 / 2 ∧
    (hc τ).u ⟨R.k - 1, by omega⟩ = -1 / 2) ∧
  (∃ b1 : Tau → ℤ,
    (∀ τ (j : Fin R.m), (hc τ).b j = (b1 τ : ℚ) + (j.1 : ℚ) * (h0v s ch : ℚ) ∧
      (hc τ).e j = (hc τ).b j + (h0v s ch : ℚ) / 2) ∧
    (∀ τ (t : H.TT), eTau τ = R.tau1 t → b1 τ = bT t + ⌊s.b' / s.x⌋) ∧
    (∀ τ, eTau τ ∈ H.thickPlaces → ⌈s.b⌉ ≤ b1 τ ∧ b1 τ < ⌈s.b⌉ + (NumberField.Units.torsionOrder H.E : ℤ)) ∧
    (∀ τ, H.IsThin (eTau τ) → b1 τ = ⌈s.w'' R.n⌉)) ∧
  ∀ j : Fin R.m, UpperTheory.MUQ (fun τ => H.emb (eTau τ)) (fun τ => (hc τ).e j)

structure Val (C : FC) (cD ch : ℝ) {D : D7} (L : SizeData₂ D) : Prop where
  ranks : RankVal L.sc D.R
  host : HostVal L.sc C.P.Cpde D.host
  hc : HCVal L.sc cD ch D.host (fun τ => (D.eTau τ : D.R.GG)) D.hc L.bT
  dlog : |L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps
  Del_eq : D.s.Del = (Delv L.sc cD : ℚ)
  eta_eq : L.etaSz = (D.R.m : ℝ) * (h0v L.sc ch : ℝ)
  La_eq : L.LaG = G.La C.GK L.sc
  bT_le : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ)
  logFiveDepth_eq : L.j0 = ⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊
  Ct_eq : L.Ct = C.Ct
  Cc_eq : L.Cc = C.Cc
  CGam_eq : L.CGam = C.CGam
  secondConstant_eq : D.host.CT2 = C.CT2
  words : Fintype.card D.what₂.Word = ⌈3 * GamL L ^ 2 * L.sc.x ^ C.P.CF⌉₊
  etaF_eq : D.div.etaF = 6 * L.sc.x ^ (-C.P.CF)

def SzRow (P : FC → ∀ D : D7, SizeData₂ D → Prop) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∀ C : FC, Std C → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ x0 : ℝ,
    ∀ (D : D7) (L : SizeData₂ D), L.sc.eps = eps → x0 ≤ L.sc.x → Val C cD ch L → P C D L

theorem PairWin.one_lt {s : Scale} {Y : ℝ} (h : PairWin s Y) : 1 < Y :=
  (Real.one_lt_rpow s.one_lt_alt (one_div_pos.2 (lt_of_lt_of_le one_pos s.one_le_J))).trans_le h.1

theorem PairWin.rpow_ez_le {s : Scale} {Y : ℝ} (h : PairWin s Y) {c : ℝ} (hc : 0 < c) :
    s.x ^ (s.ez / c) ≤ Y ^ (s.eps / c) := by
  have hx : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have e : s.ez / c = 1 / s.J * (s.eps / c) := by unfold Scale.ez; ring
  rw [e, Real.rpow_mul hx.le]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) h.1 (div_nonneg s.eps_pos.le hc.le)

theorem PairWin.rpow_le {s : Scale} {Y : ℝ} (h : PairWin s Y) {a : ℝ} (ha : 0 ≤ a) : Y ^ a ≤ s.x ^ a :=
  Real.rpow_le_rpow (by linarith [h.one_lt]) h.2 ha

theorem PairWin.log_le {s : Scale} {Y : ℝ} (h : PairWin s Y) : Real.log Y ≤ Real.log s.x :=
  Real.log_le_log (by linarith [h.one_lt]) h.2

theorem PairWin.log_div_le {s : Scale} {Y : ℝ} (h : PairWin s Y) : Real.log s.x / s.J ≤ Real.log Y := by
  have hx : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have h1 := Real.log_le_log (Real.rpow_pos_of_pos hx _) h.1
  rw [Real.log_rpow hx] at h1
  calc Real.log s.x / s.J = 1 / s.J * Real.log s.x := by ring
    _ ≤ _ := h1

theorem PairWin.rpow_inv_le {s : Scale} {Y C : ℝ} (h : PairWin s Y) (hJ : s.J ≤ C) : s.x ^ (1 / C) ≤ Y :=
  (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le
    (one_div_le_one_div_of_le (lt_of_lt_of_le one_pos s.one_le_J) hJ)).trans h.1

theorem PairWin.z_log_sq_le {s : Scale} {Y : ℝ} (h : PairWin s Y) :
    Y ^ (s.eps / 5) * Real.log Y ^ 2 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
  have h0 : 0 ≤ Real.log Y := Real.log_nonneg h.one_lt.le
  have h1 := h.rpow_le (a := s.eps / 5) (by linarith [s.eps_pos])
  exact mul_le_mul h1 (pow_le_pow_left₀ h0 h.log_le 2) (sq_nonneg _)
    (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _)

namespace HostVal

variable {s : Scale} {C8 : ℝ} {R : Ranks} {H : Host R}

theorem split_tie (h : HostVal s C8 H) : ⌊s.x ^ (s.ez / 5)⌋₊ ≤ H.splitBound := h.2.2.2.2.2.2.2.1

theorem J_le (h : HostVal s C8 H) : s.J ≤ C8 := h.2.2.2.2.2.2.2.2.1

theorem o_le (h : HostVal s C8 H) : (R.o : ℝ) ≤ C8 := h.2.2.2.2.2.2.2.2.2.1

theorem QS_le (h : HostVal s C8 H) : (H.QS : ℝ) ≤ C8 * R.n := h.2.2.2.2.2.2.2.2.2.2

theorem one_le (h : HostVal s C8 H) : 1 ≤ C8 := s.one_le_J.trans h.J_le

theorem eps_div_le_ez (h : HostVal s C8 H) : s.eps / C8 ≤ s.ez :=
  div_le_div_of_nonneg_left s.eps_pos.le (lt_of_lt_of_le one_pos s.one_le_J) h.J_le

theorem log_cond_le (h : HostVal s C8 H) :
    Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
  obtain ⟨Y, hY, hr⟩ := h.1
  have := hY.z_log_sq_le
  linarith [hr.2.2.2.2.2.2.2.2.2.2]

theorem mono (h : HostVal s C8 H) {C8' : ℝ} (hC : C8 ≤ C8') : HostVal s C8' H := by
  have hN : (1 : ℝ) ≤ (H.QS : ℝ) * H.q * H.d := by
    have : 0 < H.QS * H.q * H.d := Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.1.pos) H.hyp.2.1.pos
    exact_mod_cast this
  have m := Real.rpow_le_rpow_of_exponent_le hN hC
  obtain ⟨a, b, c, ⟨d1, d2⟩, e, f, g, i, j1, j2, j3⟩ := h
  exact ⟨a, b, c, ⟨d1.trans m, d2.trans m⟩, e, f, g, i, j1.trans hC, j2.trans hC,
    j3.trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _))⟩

end HostVal

end GlobalTheory.EX

end
end

