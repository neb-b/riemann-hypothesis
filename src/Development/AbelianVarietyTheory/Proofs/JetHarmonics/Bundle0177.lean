module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0116
public import Formalism.HermitianCurvature.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0149
public import Formalism.HermitianCurvature.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0185
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0278
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.XiExistsOfBesselXiIntegrable
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelFormCutoffTendstoBelow
public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IteratedDerivBddOfEventuallyConst
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0088
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0274
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WithRightAction

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLocalSectionBounds
section
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

namespace GlobalTheory

theorem pointwiseBound_at_place_of_locBessel : ThmBpDS → ∀ Ch : ℝ, ∃ C₄ Cg₀ : ℝ, 0 ≤ C₄ ∧ ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∃ (U U' : ℕ → ℝ) (p : KB.Pl ⟨D.R.k, D.R.rS, Tz D.R.k D.R.rS L.z, Tz D.R.k D.R.rS L.z', U, U'⟩ L.Wp L.Wq) (n₀ : ℕ), IsStdOf L μsec p.T.base ∧ n₀ ≤ 30 * (D.R.rS + 1) ^ 2 + 6 ∧ TBB.ThmBpAt p f b C₄ n₀ (2 * (D.R.rS + 1)) := by
  classical
  intro hT Ch
  obtain ⟨C₄, G₀, hC₄, h⟩ := hT Ch 2 (by norm_num)
  refine ⟨C₄, G₀, hC₄, fun Cg hCg D L lam0 f μsec ka b hL hg hf hsec => ?_⟩
  obtain ⟨-, hε, -, -, -, hS, -⟩ := hL
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨U, U', p, hU, hstd⟩ :=
    _root_.GlobalTheory.exists_place_of_locBessel D.R.k D.R.rS L μsec lam0 (by omega) hk hsec hS.2.1 hS.2.2.1
  have hu : (fun i : Fin D.R.k => U (i.val + 1)) = L.u := funext fun i => (hU i).1
  have hu' : (fun i : Fin D.R.k => U' (i.val + 1)) = L.u' := funext fun i => (hU i).2
  have he : L.ε = PI.BesselPeriodGGP.eps48 D.R.k D.R.rS := by
    rw [hε]; funext i; rfl
  obtain ⟨v1, v2, -⟩ := GlobalTheory.upqRep_vocabulary_agree D.R.k D.R.rS L.Hs L.σ L.ε L.lam
  have hone : (1 : B.Mat D.R.k D.R.rS) ∈ UH (Hpk D.R.k D.R.rS) := by simp [UH]
  refine ⟨U, U', p, if ∀ i ∈ Finset.Icc 1 D.R.k, U i = U' i then 30 * (D.R.rS + 1) ^ 2 + 6 else 0, hstd,
    by split_ifs <;> omega, ?_⟩
  refine h Cg hCg ⟨D.R.k, D.R.rS, Tz D.R.k D.R.rS L.z, Tz D.R.k D.R.rS L.z', U, U'⟩ L.Wp L.Wq p lam0 L.lam ka b _ _
    ⟨L.Hs, L.σ⟩ f ?_ hg ?_ ?_ (fun e => if_pos e) (fun e => if_neg e) ?_ ?_
  · show StdHyp Ch Cg D.R.k D.R.rS _ lam0 (fun i : Fin D.R.k => U (i.val + 1))
      (fun i : Fin D.R.k => U' (i.val + 1)) _ _ ka b
    rw [hu, hu', ← he]
    exact hS
  · show BranchingSupport.Rep.IsDS (k := D.R.k) (r := D.R.rS) ⟨L.Hs, L.σ⟩ (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) L.lam
    rw [← he]
    exact ⟨L.hlam, v1.1 L.hσ⟩
  · obtain ⟨P, Q, hQ, hP, hfe⟩ := hf
    exact ⟨1, hone, 1, hone, P, Q, fun w => (v2 _).1 (hQ w), fun x => (v2 _).1 (hP x), fun g => by
      simpa using hfe g⟩
  · show 3 * (D.R.rS + 1) ≤ 2 * (2 * (D.R.rS + 1))
    omega
  · show ((2 * (D.R.rS + 1) : ℕ) : ℝ) ≤ 2 * ((D.R.rS : ℝ) + 1) ^ 2
    have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    push_cast
    nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqIntegralInnerTopVectors
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory

theorem beta_word_cutF_eq_integral_inner_tv :
    P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) ((D.cutF p.T.base χ f ε₁)) w) (D.cutF p.T.base χ f ε₂) = ∫ c, inner ℂ (tv p (D.cutF p.T.base χ f ε₂) w c) (tv p (D.cutF p.T.base χ f ε₁) w c) := by
  intro hA Cb
  obtain ⟨C₁, h₁⟩ := _root_.GlobalTheory.LevelZeroApprox.beta_approx
  obtain ⟨C₂, h₂⟩ := _root_.GlobalTheory.TopVec.tv_approx_tendsto_L2 hA Cb
  refine ⟨max C₁ C₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ A N w hD hχ hf hCC hth hw hlen ε₁ ε₂ hε₁ hε₂
  have hmono : ∀ Cc : ℝ, Cc ≤ max C₁ C₂ →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    intro Cc hC
    refine le_trans ?_ hth
    gcongr
  have hL := (h₁ P.k P.r Wp Wq p.T.base (M.sgn P p.l0) w χ f A N hχ hf hCC (hmono _ (le_max_left _ _)) hlen
    ε₁ ε₂ hε₁ hε₂).1
  obtain ⟨a₁, b₁, c₁⟩ := h₂ Wp Wq P p f χ A N w hD hχ hf hCC (hmono _ (le_max_right _ _)) hw hlen ε₁ hε₁
  obtain ⟨a₂, b₂, c₂⟩ := h₂ Wp Wq P p f χ A N w hD hχ hf hCC (hmono _ (le_max_right _ _)) hw hlen ε₂ hε₂
  have hR := tendsto_integral_inner_of_tendsto_eLpNorm_two _ _ _ _ _ _ _ a₁ a₂ b₁ b₂ c₁ c₂
  refine tendsto_nhds_unique hL (hR.congr fun n => ?_)
  have hc : ∀ ε : ℝ, 0 < ε → KB.CptCoef p.T.base (fun g : B.Mat P.k P.r =>
      ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) •
        D.cutF p.T.base χ f ε g) := fun ε hε =>
    Formalism.FourierDecayAlt.P.PBE.cutCpt P p.T.base f χ ε
      (fun (n : ℕ) (g : B.Mat P.k P.r) =>
        ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ))
      hχ hε hf (fun _ _ => rfl) n
  exact (_root_.GlobalTheory.TopVecPol.beta_eq_integral_inner_tv hA Wp Wq P p Cb _ _ w hD (hc ε₁ hε₁) (hc ε₂ hε₂) hw).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LimPosOfLimEvTOfCompactPositivity
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.QuantumDeterminants NumberField MeasureTheory Filter Topology
open scoped ComplexOrder

namespace GlobalTheory.LevelZeroLimit

noncomputable section

theorem limPos_of_compactPositivity (hΞ : B.XiExists) (hA : P5.ThmPActualCpt) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) (Y : Finset ℝ) (N : ℕ) : LimPos p F Y N := by
  intro w hw _
  have hh : D.IsLocPt ([] : C.LPt) 0 := ⟨by simp, rfl⟩
  rw [PBL.rr_eq_form p F 0 (Nat.zero_le _) w [] [] hh hh]
  have h := GlobalTheory.WeightedFormPos.formPosCpt_of_xiExists hΞ hA Wp Wq P p 0 (Nat.zero_le _) w hw.1 _
    (fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F 0 (Nat.zero_le _) w [] hh hF e)
  simpa using (Complex.le_def.1 h).1

theorem limPos_of_limEvT_of_compactPositivity (hΞ : B.XiExists) (hA : P5.ThmPActualCpt) (Cb : ℝ) :
    ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ)
    (A : ℝ) (N : ℕ) (Y : Finset ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    LimEvT p χ F Y N → LimPos p F Y N := by
  obtain ⟨Cc, hCc⟩ := GlobalTheory.GivenXi.levelForm_cutoff_tendsto hΞ Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p F χ A N Y hDD hχ hF hFA hth hEv w hw hN
  have hcut : ∀ ε : ℝ, 0 < ε → 0 ≤ (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re := by
    intro ε hε
    obtain ⟨hcpt, hlim⟩ := hCc Wp Wq P p F χ ε A N (cutN P.k P.r) hDD hχ hε hF hFA hth (fun _ _ => rfl)
    have hT := (Complex.continuous_re.tendsto _).comp (hlim 0 w hw.1 hN [] [])
    exact ge_of_tendsto hT
      (Eventually.of_forall fun n => limPos_of_compactPositivity hΞ hA p (hcpt n) Y N w hw hN)
  exact ge_of_tendsto (hEv w hw hN) (eventually_nhdsWithin_of_forall fun ε hε => hcut ε hε)

theorem limE_of_limEvT_of_xiExists (hΞ : B.XiExists) :
    P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ nn : ℝ → ℝ) (A : ℝ) (N : ℕ) (Y : Finset ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → (∀ y, 0 ≤ nn y) → B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → LimEvT p χ F Y N → LimBd p nn F Y N → LimE p nn χ F Y N := by
  intro hA Cb
  obtain ⟨Cc, hCc⟩ := limPos_of_limEvT_of_compactPositivity hΞ hA Cb
  exact ⟨Cc, fun Wp Wq _ _ _ _ _ _ P p F χ nn A N Y hDD hχ hnn hF hFA hth hEv hBd =>
    limE_of_partsT p nn χ F Y N hnn hEv (hCc Wp Wq P p F χ A N Y hDD hχ hF hFA hth hEv) hBd⟩

end

end GlobalTheory.LevelZeroLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityDominated
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem dom_pow_le (G : ℝ) (hG : 0 < G) (m q : ℕ) (h : m ≤ q) : G ^ m ≤ 1 + G ^ q := by
  rcases le_total G 1 with h1 | h1
  · have := pow_le_one₀ (n := m) hG.le h1
    have := pow_pos hG q
    linarith
  · have := pow_le_pow_right₀ h1 h
    linarith

theorem dom_real_bound {ι κ : Type} [Fintype ι] [Fintype κ] (E Ct n D G C S C' : ℝ) (L a p₀ : ℕ)
    (u : ι → ℝ) (v : κ → ℝ) (hCt : 0 ≤ Ct) (hn : 0 ≤ n) (hD : 0 < D) (hG : 0 < G) (hC : 0 ≤ C)
    (hS0 : 0 ≤ S) (hS : S ≤ C' * G ^ p₀) (hu0 : ∀ e, 0 ≤ u e) (hv0 : ∀ t, 0 ≤ v t)
    (hL : L * (1 + 2 * a) ≤ 2 * p₀)
    (hu : ∀ e, u e ≤ C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * S * ∑ t, v t)
    (hE : E ≤ Ct * n * (D ^ 2 / G) ^ L * ∑ e, u e ^ 2) :
    E ≤ (Ct * Fintype.card ι * (C * C') ^ 2 * Fintype.card κ) *
      ∑ t, (n * v t ^ 2 + n * ((G ^ p₀) ^ 2 * v t ^ 2)) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hL
  have hT0 : 0 ≤ ∑ t, v t := Finset.sum_nonneg fun t _ => hv0 t
  have hT : (∑ t, v t) ^ 2 ≤ Fintype.card κ * ∑ t, v t ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset κ)) (f := v)
  have hV0 : 0 ≤ ∑ t, v t ^ 2 := Finset.sum_nonneg fun t _ => sq_nonneg _
  have h1 : ∑ e, u e ^ 2 ≤ Fintype.card ι * (C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * (C' * G ^ p₀) * ∑ t, v t) ^ 2 := by
    have : ∀ e ∈ (Finset.univ : Finset ι),
        u e ^ 2 ≤ (C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * (C' * G ^ p₀) * ∑ t, v t) ^ 2 := by
      intro e _
      refine pow_le_pow_left₀ (hu0 e) ((hu e).trans ?_) 2
      gcongr
    simpa using Finset.sum_le_card_nsmul _ _ _ this
  have h2 : (D ^ 2 / G) ^ L * ((D⁻¹ ^ L * G⁻¹ ^ (a * L)) * G ^ p₀) ^ 2 = G ^ m := by
    have e : (G ^ p₀) ^ 2 = G ^ L * (G ^ (a * L)) ^ 2 * G ^ m := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      rw [mul_comm p₀ 2, hm]; ring
    rw [mul_pow, e, div_pow, inv_pow, inv_pow, ← pow_mul D 2 L, mul_comm 2 L, pow_mul D L 2]
    have := pow_pos hD L
    have := pow_pos hG L
    have := pow_pos hG (a * L)
    field_simp
  have h3 : G ^ m ≤ 1 + (G ^ p₀) ^ 2 := by
    rw [← pow_mul]
    exact dom_pow_le G hG _ _ (by omega)
  have h4 : ∑ t, (n * v t ^ 2 + n * ((G ^ p₀) ^ 2 * v t ^ 2)) = n * (1 + (G ^ p₀) ^ 2) * ∑ t, v t ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  calc E ≤ Ct * n * (D ^ 2 / G) ^ L * ∑ e, u e ^ 2 := hE
    _ ≤ Ct * n * (D ^ 2 / G) ^ L *
        (Fintype.card ι * (C * (D⁻¹ ^ L * G⁻¹ ^ (a * L)) * (C' * G ^ p₀) * ∑ t, v t) ^ 2) := by gcongr
    _ = Ct * n * Fintype.card ι * (C * C') ^ 2 *
        ((D ^ 2 / G) ^ L * ((D⁻¹ ^ L * G⁻¹ ^ (a * L)) * G ^ p₀) ^ 2) * (∑ t, v t) ^ 2 := by ring
    _ ≤ Ct * n * Fintype.card ι * (C * C') ^ 2 * (1 + (G ^ p₀) ^ 2) * (Fintype.card κ * ∑ t, v t ^ 2) := by
        rw [h2]; gcongr
    _ = _ := by rw [h4]; ring

theorem dom_thr (Cc r k : ℝ) (N L : ℝ) (hCc : 8 ≤ Cc) (hr : 0 ≤ r) (hk : 0 ≤ k) (hL : L ≤ N) (hN : 0 ≤ N) :
    L * (8 * (r + 1) * (2 * r + k + 1)) ≤ Cc * (r + 1) ^ 4 * (N * (2 * r + k + 1) ^ 2) := by
  have h1 : r + 1 ≤ (r + 1) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have h2 : 2 * r + k + 1 ≤ (2 * r + k + 1) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  calc L * (8 * (r + 1) * (2 * r + k + 1)) ≤ N * (Cc * (r + 1) ^ 4 * (2 * r + k + 1) ^ 2) := by
        have : 0 ≤ Cc := by linarith
        gcongr
    _ = _ := by ring

theorem top_density_dominated : GlobalTheory.HCXi.BesselXiIntegrable → ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ) (w : List C.Letter), C6.IsCut0 χ → KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) → N * (1 + 2 * a P.r) ≤ 2 * p₀ → KB.CutWord P p.l0 w → w.length ≤ N → (∀ ε : ℝ, 0 < ε → AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f) (P.r + 1) w (TBB.bigPt P.r c)) volume) ∧ ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ ε : ℝ, 0 < ε → ∀ c₀ : Fin (P.r + 1) → ℂ, ‖(fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f) (P.r + 1) w (TBB.bigPt P.r c)) c₀‖ ≤ h c₀ := by
  intro hXi a ha Cb
  obtain ⟨C1, h1⟩ := _root_.GlobalTheory.HatNF.wordBound_decay a ha Cb
  obtain ⟨C2, h2⟩ := _root_.GlobalTheory.HatNF.EmptyWordL2.integrable_density_nil hXi
  refine ⟨max C1 (max C2 8), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ N w hχ hDD hf hfA hth hN hw hwN
  have hc1 : C1 ≤ max C1 (max C2 8) := le_max_left _ _
  have hc2 : C2 ≤ max C1 (max C2 8) := (le_max_left _ _).trans (le_max_right _ _)
  have hc8 : 8 ≤ max C1 (max C2 8) := (le_max_right _ _).trans (le_max_right _ _)
  generalize max C1 (max C2 8) = Cc at hth hc1 hc2 hc8
  obtain ⟨C, J, Θs, hC, hpoly, hb⟩ := h1 Wp Wq P p N w hDD hw hwN
  obtain ⟨hcut, C', hC', hld⟩ := ld_cut_pow χ p₀ J hχ
  obtain ⟨Ct, hCt, htop⟩ := GlobalTheory.TopDensityBound.top_density_le Wp Wq P p w
  constructor
  · intro ε hε
    have hs := (GlobalTheory.HatNF.mulG_ckOn_inCC Wp Wq P p.T.base p₀ 0 _ f A₀ (hcut ε hε) hf (hfA 0)).1
    have hm := GlobalTheory.TopVec.aestronglyMeasurable_tv Wp Wq P p Cb _ w hDD hw hs
    simp only [GlobalTheory.TopVec.Ew_eq_norm_tv_sq]
    exact hm.norm.pow 2
  have hth1 : C1 * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      A₀ - (2 * (P.r : ℝ) + 2) * p₀ := by
    refine le_trans ?_ (hth.trans (le_of_eq (by push_cast; ring)))
    gcongr
  set d : ℝ := ((w.length * (8 * (P.r + 1) * (2 * P.r + P.k + 1)) : ℕ) : ℝ) with hd
  have hth2 : C2 * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤ A₀ - d - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by
    have e1 := dom_thr Cc P.r P.k N w.length hc8 (by positivity) (by positivity) (by exact_mod_cast hwN) (by positivity)
    have e2 : C2 * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 ≤
        Cc * ((P.r : ℝ) + 1) ^ 4 * (2 * (P.r : ℝ) + P.k + 1) ^ 3 := by gcongr
    have e3 : d = (w.length : ℝ) * (8 * ((P.r : ℝ) + 1) * (2 * (P.r : ℝ) + P.k + 1)) := by
      rw [hd]; push_cast; ring
    rw [mul_add] at hth
    linarith
  have hΘ : ∀ t : Fin Θs.length, B.CkOn ⊤ (B.GV P.k P.r) (B.opApply Θs[t.1] f) ∧
      ∀ m : ℕ, B.InCC (A₀ - d) m (B.opApply Θs[t.1] f) := fun t =>
    Formalism.FourierDecayAlt.P.CutMP.class_lower_decay_holds P.k P.r Wp Wq _ d A₀ (by positivity)
      ((polyOp_ok P.k P.r Wp Wq _ _ _ (hpoly _ (List.getElem_mem t.2))).2.1 d le_rfl) f hf hfA
  refine ⟨fun c => (Ct * Fintype.card (Ix (Fin w.length)) * (C * ((J + 1) * C')) ^ 2 * Fintype.card (Fin Θs.length)) *
    ∑ t : Fin Θs.length, (TBB.Ew p (fun _ => 1) (B.opApply Θs[t.1] f) (P.r + 1) [] (TBB.bigPt P.r c) +
      TBB.Ew p (fun _ => 1) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • B.opApply Θs[t.1] f g)
        (P.r + 1) [] (TBB.bigPt P.r c)), ?_, ?_⟩
  · refine Integrable.const_mul (integrable_finsetSum _ fun t _ => Integrable.add ?_ ?_) _
    · refine h2 Wp Wq P p _ (A₀ - d) (hΘ t).1 (hΘ t).2 (hth2.trans ?_)
      have : (0 : ℝ) ≤ (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by positivity
      linarith
    · exact h2 Wp Wq P p _ _ (Formalism.FourierDecayAlt.P.CutBP.ckOn_Gpow_smul _ _ p₀ (hΘ t).1)
        (Formalism.FourierDecayAlt.P.CutBP.inCC_Gpow_smul _ _ p₀ (hΘ t).2) hth2
  intro ε hε c
  beta_reduce
  by_cases hc : (∀ l, c l ≠ 0) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
  swap
  · rw [(htop _ c).1 hc, norm_zero]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ =>
      add_nonneg (Formalism.FourierDecayAlt.P.TBBx4.ew_nonneg _ _ _) (Formalism.FourierDecayAlt.P.TBBx4.ew_nonneg _ _ _))
  obtain ⟨hc0, hG⟩ := hc
  obtain ⟨hn, -, hE⟩ := (htop (mulG p.T.base (fun y => χ (y / ε) * y ^ p₀) f) c).2 hc0 hG
  have hGp : ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      p.V (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • F g) (TBB.bigPt P.r c) =
        ((TBB.Gp p (TBB.bigPt P.r c) ^ p₀ : ℝ) : ℂ) • p.V F (TBB.bigPt P.r c) := by
    intro F
    by_cases hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1)
    · exact Formalism.FourierDecayAlt.P.TBBx4.vec_Gpow p F p₀ hl hG
    · rw [Formalism.FourierDecayAlt.P.TBBx4.V_zero p _ (fun h => hl h.1), Formalism.FourierDecayAlt.P.TBBx4.V_zero p _ (fun h => hl h.1), smul_zero]
  simp only [fun H => ((htop H c).2 hc0 hG).2.1, hGp, Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq]
  rw [Real.norm_eq_abs]
  refine dom_real_bound _ Ct _ ‖∏ l, c l‖ _ C
    (∑ j ∈ Finset.range (J + 1), |LE.ld j (fun y => χ (y / ε) * y ^ p₀) (TBB.Gp p (TBB.bigPt P.r c))|) _
    w.length (a P.r) p₀ _ (fun t : Fin Θs.length => ‖B.hsVec (p.V (B.opApply Θs[t.1] f) (TBB.bigPt P.r c))‖)
    hCt hn (norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun l _ => hc0 l)) hG hC
    (Finset.sum_nonneg fun _ _ => abs_nonneg _) ?_ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    ((Nat.mul_le_mul_right _ hwN).trans hN) ?_ hE
  · have := Finset.sum_le_card_nsmul (Finset.range (J + 1)) _ _ fun j hj =>
      hld ε _ hε hG j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    simpa [mul_assoc] using this
  · intro e
    have := hb _ f ⟨p₀, A₀, hcut ε hε, hf, hfA, hth1⟩ e c hc0 hG
    rwa [← Fin.sum_univ_fun_getElem] at this

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerShiftedPlacesExistProof
section
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutBP2

namespace GlobalTheory.wignerShiftedPlacesExist_proof

theorem gap_one {P : M.Par} (h : P.OK) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) :
    P.u' (i + 1) + 1 ≤ P.u' i := by
  have hg := h.gap i hi
  unfold M.Par.lo M.Par.hi at hg
  have h1 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
  have h2 := min_le_right (P.u i) (P.u' i)
  linarith

theorem gap_nat {P : M.Par} (h : P.OK) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) :
    ∃ N : ℕ, P.u' i - P.u' (i + 1) = (N : ℝ) + 1 := by
  have h1 := gap_one h i hi
  rw [Finset.mem_Icc] at hi
  obtain ⟨a, ha⟩ := h.int_u' i (Finset.mem_Icc.2 ⟨hi.1, by omega⟩)
  obtain ⟨c, hc⟩ := h.int_u' (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have h2 : ((0 : ℤ) : ℝ) ≤ ((a - c - 1 : ℤ) : ℝ) := by push_cast; linarith
  have h3 : (0 : ℤ) ≤ a - c - 1 := by exact_mod_cast h2
  refine ⟨(a - c - 1).toNat, ?_⟩
  have h4 : (((a - c - 1).toNat : ℤ) : ℝ) = ((a - c - 1 : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg h3]
  push_cast at h4
  linarith

theorem ok_plus {P : M.Par} (h : P.OK) (l n₀ : ℕ) (he : ∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i)
    (hg : 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1)) :
    (shP P P.u (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)))).OK := by
  have hn : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine ⟨h.k_pos, h.T_pos, h.T'_pos, h.int_u, ?_, ?_⟩
  · intro i hi
    obtain ⟨a, ha⟩ := h.int_u' i hi
    change ∃ n : ℤ, Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)) i - P.u 1 = n
    by_cases hil : i = l + 1
    · subst hil
      refine ⟨a + n₀, ?_⟩
      rw [Function.update_self]; push_cast; linarith
    · exact ⟨a, by rw [Function.update_of_ne hil]; exact ha⟩
  · intro i hi
    have h1 := gap_one h i hi
    change i ∈ Finset.Icc 1 (P.k - 1) at hi
    rw [Finset.mem_Icc] at hi
    have e1 := he i (Finset.mem_Icc.2 ⟨hi.1, by omega⟩)
    have e2 := he (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    change max (P.u (i + 1)) (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)) (i + 1)) + 1 / 2 ≤
      min (P.u i) (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ)) i) - 1 / 2
    rw [e1, e2]
    by_cases ha : i = l
    · subst ha
      rw [Function.update_self, Function.update_of_ne (by omega), min_self, max_eq_right (by linarith)]
      linarith
    · rw [Function.update_of_ne (show i + 1 ≠ l + 1 by omega), max_self]
      by_cases hb : i = l + 1
      · subst hb
        rw [Function.update_self, min_eq_left (by linarith)]
        linarith
      · rw [Function.update_of_ne hb, min_self]
        linarith

theorem ok_minus {P : M.Par} (h : P.OK) (l n₀ : ℕ) (he : ∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i)
    (hg : 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1)) :
    (shP P P.u (Function.update P.u' l (P.u' l - (n₀ : ℝ)))).OK := by
  have hn : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine ⟨h.k_pos, h.T_pos, h.T'_pos, h.int_u, ?_, ?_⟩
  · intro i hi
    obtain ⟨a, ha⟩ := h.int_u' i hi
    change ∃ n : ℤ, Function.update P.u' l (P.u' l - (n₀ : ℝ)) i - P.u 1 = n
    by_cases hil : i = l
    · subst hil
      refine ⟨a - n₀, ?_⟩
      rw [Function.update_self]; push_cast; linarith
    · exact ⟨a, by rw [Function.update_of_ne hil]; exact ha⟩
  · intro i hi
    have h1 := gap_one h i hi
    change i ∈ Finset.Icc 1 (P.k - 1) at hi
    rw [Finset.mem_Icc] at hi
    have e1 := he i (Finset.mem_Icc.2 ⟨hi.1, by omega⟩)
    have e2 := he (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    change max (P.u (i + 1)) (Function.update P.u' l (P.u' l - (n₀ : ℝ)) (i + 1)) + 1 / 2 ≤
      min (P.u i) (Function.update P.u' l (P.u' l - (n₀ : ℝ)) i) - 1 / 2
    rw [e1, e2]
    by_cases ha : i = l
    · subst ha
      rw [Function.update_self, Function.update_of_ne (by omega), max_self, min_eq_right (by linarith)]
      linarith
    · rw [Function.update_of_ne ha, min_self]
      by_cases hb : i + 1 = l
      · subst hb
        rw [Function.update_self, max_eq_left (by linarith)]
        linarith
      · rw [Function.update_of_ne hb, max_self]
        linarith

theorem shiftExists_of (hA : GlobalTheory.WigSh.AmapsShExists) : GlobalTheory.WigSh.ShiftExists := by
  obtain ⟨c₃, hc⟩ := hA
  obtain ⟨Cb, hCb, hS⟩ := GlobalTheory.WithRightAction.exists_place_other_right_type
  refine ⟨c₃, Cb, hCb, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p l n₀ lp lm b he hl1 hl2 hg hb hn hb1 hp1 hp2 hm1 hm2
  obtain ⟨hOK, hz, hz', hT, hT', hπ, hπ'⟩ := p.hP
  obtain ⟨Wqp, i1, i2, i3, Wqm, j1, j2, j3, πp, πm, -, -, htp, htm, -⟩ :=
    GlobalTheory.WigSh.exists_shifted_types_lower_bound Wq P.k P.r p.T.base.z' p.T.base.π' P.u' l n₀ b hz'
      (by rw [hT']; exact hOK.T'_pos) hπ' (gap_nat hOK) hl1 hl2 hg hb hn hb1
  obtain ⟨pp, a1, a2, a3, a4, -, a6, a7, a8⟩ := hS P Wp Wq Wqp p P.u
    (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ))) πp lp
    ⟨ok_plus hOK l n₀ he hg, hz, hz', hT, hT', hπ, htp⟩ hp1 hp2
  obtain ⟨pm, b1, b2, b3, b4, -, b6, b7, b8⟩ := hS P Wp Wq Wqm p P.u
    (Function.update P.u' l (P.u' l - (n₀ : ℝ))) πm lm
    ⟨ok_minus hOK l n₀ he hg, hz, hz', hT, hT', hπ, htm⟩ hm1 hm2
  obtain ⟨Ap, Am, ApPt, AmPt, c1, c2, c3, c4⟩ := hc P Wp Wq Wqp Wqm P.u
    (Function.update P.u' (l + 1) (P.u' (l + 1) + (n₀ : ℝ))) P.u (Function.update P.u' l (P.u' l - (n₀ : ℝ)))
    p pp pm l n₀ b a2 a3 b2 b3 (fun h _ => congrFun a4 h) (fun h _ => congrFun b4 h) a6 a7 b6 b7 hl1 hl2 hg hb hn hb1
    (fun i _ => by
      by_cases h : i = l + 1
      · subst h; simp
      · rw [Function.update_of_ne h, if_neg h])
    (fun i _ => by
      by_cases h : i = l
      · subst h; simp
      · rw [Function.update_of_ne h, if_neg h])
  exact ⟨Wqp, i1, i2, i3, Wqm, j1, j2, j3, pp, pm, Ap, Am, ApPt, AmPt, a1, b1, a2, a3, a4, b2, b3, b4, a8, b8,
    c1, c2, c3, c4⟩

theorem shiftExists : GlobalTheory.WigSh.ShiftExists := shiftExists_of _root_.GlobalTheory.WigSh.amapsShExists

end GlobalTheory.wignerShiftedPlacesExist_proof
end

