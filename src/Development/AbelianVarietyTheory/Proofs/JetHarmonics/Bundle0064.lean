module

public import Mathlib
public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StarStartConjugationIdentity
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPolyDegPrW
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

theorem isPolyDeg_prW {N : ℕ} (k r d : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (v : Matrix (Fin N) (Fin N) ℂ → Fin (2 * r + k + 1) → ℂ) (hv : ∀ i, U.IsPolyDeg d (fun g => v g i))
    (i : Fin (2 * r + k + 1)) : U.IsPolyDeg d (fun g => D.prW k r z (v g) i) := by
  have hb : ∀ j : Fin (2 * r + k + 1),
      U.IsPolyDeg d (fun g => if r ≤ j.val ∧ j.val ≤ r + k then v g j else 0) := by
    intro j
    by_cases h : r ≤ j.val ∧ j.val ≤ r + k
    · simpa only [if_pos h] using hv j
    · simpa only [if_neg h] using pd_const (N := N) 0 d
  unfold D.prW
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  refine pd_sub (hb i) (pd_mono (show d + 0 + 0 ≤ d by omega)
    (pd_mul (pd_mul ?_ (pd_const _ 0)) (pd_const _ 0)))
  unfold herm
  simp only [dotProduct, mulVec]
  refine pd_sum _ fun a _ => pd_mono (show 0 + d ≤ d by omega) (pd_mul (pd_const _ 0) ?_)
  exact pd_sum _ fun b _ => pd_mono (show 0 + d ≤ d by omega) (pd_mul (pd_const _ 0) (hb b))

theorem omg_isPolyDeg : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (i : Fin (2 * r + k + 1)),
    Formalism.FourierDecayAlt.U.IsPolyDeg (r + 1) (fun g : Mx k r => GlobalTheory.WigSh.omg k r z z' g i) := by
  intro k r z z' i
  unfold omg
  refine isPolyDeg_prW k r (r + 1) z' (fun g => (Hpk k r * gᴴ * Hpk k r) *ᵥ
    ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a) (fun q => ?_) i
  simp only [dotProduct, mulVec]
  refine pd_sum _ fun s _ => pd_mono (show 1 + r ≤ r + 1 by omega) (pd_mul (P.TLC.omp_inv_pd q s) ?_)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact pd_sum _ fun a _ => pd_mono (show r + 0 ≤ r by omega)
    (pd_mul (P.TLC.omp_adj_pd z z' (Fin.last r) a) (pd_const _ 0))

end GlobalTheory.WigSh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MarginArithClosing
section
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory

theorem margin_arith_closing : ∀ Cc C₀ : ℝ, 0 ≤ C₀ → ∃ Cg₀ : ℝ, 0 ≤ Cg₀ ∧ ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ (k r n₀ p₀ : ℕ) (h d : ℝ), 1 ≤ k → n₀ ≤ 30 * (r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((r : ℝ) + 1) ^ 2 → Cg * (((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) ≤ h → 0 ≤ d → (Cc * ((r : ℝ) + 1) ^ 4 * (((3 * (r + 1) : ℕ) : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ (ThreeDimData.aOf r (h / 2) - 1) - (((2 * r + 2) * p₀ + n₀ * (r + 1) : ℕ) : ℝ)) ∧ d + (((2 * r + 2) * p₀ + n₀ * (r + 1) : ℕ) : ℝ) ≤ max (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ 3) (200 * d) / 2 - 1 ∧ (((r + 1) * (2 * p₀ + n₀) + (r + 1) * (r + 2) : ℕ) : ℝ) ≤ (C₀ + 10) * ((2 * r + 2 : ℕ) : ℝ) ^ 3 := by
  intro Cc C₀ hC₀
  have habs : 0 ≤ |Cc| := abs_nonneg _
  have hle : Cc ≤ |Cc| := le_abs_self _
  refine ⟨|Cc| + C₀ + 40, by linarith, ?_⟩
  intro Cg hCg k r n₀ p₀ h d hk hn hp hh hd
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn' : (n₀ : ℝ) ≤ 30 * ((r : ℝ) + 1) ^ 2 + 6 := by exact_mod_cast hn
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  unfold ThreeDimData.aOf
  push_cast at hh ⊢
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (r : ℝ) + 1 := ⟨_, rfl⟩
  have hrR : (r : ℝ) = R - 1 := by linarith
  have e1 : 2 * (r : ℝ) + 2 = 2 * R := by linarith
  have e2 : (r : ℝ) + 2 = R + 1 := by linarith
  rw [e1] at hh ⊢
  rw [e2]
  rw [← hR] at hh hn' hp ⊢
  have hR1 : 1 ≤ R := by linarith
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 2 * (r : ℝ) + k + 1 := ⟨_, rfl⟩
  rw [← hN] at hh ⊢
  have hN2 : 2 ≤ N := by linarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 3 * R * N ^ 2 + N ^ 3 := ⟨_, rfl⟩
  rw [← hQ] at hh ⊢
  have hQ1 : 2 ≤ Q := by
    have h1 : 0 ≤ 3 * R * N ^ 2 := by positivity
    have h2 : (2 : ℝ) ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ (by norm_num) hN2 3
    linarith
  have hR0 : 0 < R := by linarith
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR1
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR1
  have hR23 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR1 (by norm_num)
  have hR13 : R ≤ R ^ 3 := by
    have := pow_le_pow_right₀ hR1 (show 1 ≤ 3 by norm_num)
    simpa using this
  have hR34 : R ^ 3 ≤ R ^ 4 := pow_le_pow_right₀ hR1 (by norm_num)
  have hA : R * p₀ ≤ C₀ * R ^ 3 := by
    have := mul_le_mul_of_nonneg_left hp hR0.le
    calc R * p₀ ≤ R * (C₀ * R ^ 2) := this
      _ = C₀ * R ^ 3 := by ring
  have hB : R * n₀ ≤ 36 * R ^ 3 := by
    have := mul_le_mul_of_nonneg_left hn' hR0.le
    calc R * n₀ ≤ R * (30 * R ^ 2 + 6) := this
      _ = 30 * R ^ 3 + 6 * R := by ring
      _ ≤ _ := by linarith
  have hC3 : 0 ≤ C₀ * R ^ 3 := by positivity
  have hCg0 : 0 ≤ Cg := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have hs : 0 < Real.sqrt (2 * R) := Real.sqrt_pos.mpr (by linarith)
    have hpow : (2 * R) ^ ((9 : ℝ) / 2) = (2 * R) ^ 4 * Real.sqrt (2 * R) := by
      rw [Real.sqrt_eq_rpow, show (9 : ℝ) / 2 = ((4 : ℕ) : ℝ) + 1 / 2 by norm_num,
        Real.rpow_add (by linarith), Real.rpow_natCast]
    rw [hpow] at hh
    have h1 : Cg * (R ^ 4 * Q) ≤ h / 2 / (8 * Real.sqrt (2 * R)) := by
      rw [le_div_iff₀ (by positivity)]
      have : Cg * (R ^ 4 * Q) * (8 * Real.sqrt (2 * R))
          = Cg * ((2 * R) ^ 4 * Real.sqrt (2 * R) * Q) / 2 := by ring
      rw [this]
      linarith
    have hX : 2 * R ^ 3 ≤ R ^ 4 * Q := by
      have : R ^ 4 * 2 ≤ R ^ 4 * Q := mul_le_mul_of_nonneg_left hQ1 (by positivity)
      linarith
    have hX0 : 0 ≤ R ^ 4 * Q := by linarith
    have h2 : (|Cc| + C₀ + 40) * (R ^ 4 * Q) ≤ Cg * (R ^ 4 * Q) :=
      mul_le_mul_of_nonneg_right hCg hX0
    have h3 : Cc * (R ^ 4 * Q) ≤ |Cc| * (R ^ 4 * Q) := mul_le_mul_of_nonneg_right hle hX0
    have h4 : C₀ * (2 * R ^ 3) ≤ C₀ * (R ^ 4 * Q) := mul_le_mul_of_nonneg_left hX hC₀
    nlinarith
  · have h1 := le_max_left (Cg * (2 * R) ^ 3) (200 * d)
    have h2 := le_max_right (Cg * (2 * R) ^ 3) (200 * d)
    have h3 : (C₀ + 40) * R ^ 3 ≤ Cg * R ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h4 : Cg * (2 * R) ^ 3 = 8 * (Cg * R ^ 3) := by ring
    nlinarith
  · nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsPassGenerators
section
namespace GlobalTheory.HatNF.GenMinus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD Formalism.FourierDecayAlt.P.MAx3.H Formalism.FourierDecayAlt.P.MAx3.K

noncomputable section

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {P : M.Par}

omit [Algebra ℂ A] [StarModule ℂ A] in
theorem star_listProd (l : List A) : star l.prod = (l.map star).reverse.prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.prod_cons, star_mul, ih, List.prod_append]

omit [StarModule ℂ A] in
theorem mem_span (d : Q.NFData P A) {b X : A} (hb : b ∈ bmon d) (hX : X ∈ hats d.L) :
    b * X ∈ nfSpan d (hats d.L) 0 0 1 := by
  unfold nfSpan
  refine Submodule.subset_span ⟨b, hb, [X], rfl, ?_⟩
  simp [hX]

omit [StarModule ℂ A] in
theorem kap_comm (d : Q.NFData P A) (h : HatHyp d) (f : M.Ty P → ℂ) (y : ℂ) :
    Commute (d.κ f) (d.L.Ahatv y) ∧ Commute (d.κ f) (d.L.R0v y) := by
  obtain ⟨-, -, hR, -, -, -, hk⟩ := h
  have hf : ∀ g ∈ d.L.fns, Commute (d.κ f) g := fun g hg => hR.2.1 f g (Or.inl hg)
  have hn : Commute (d.κ f) d.L.nabs := hR.2.1 f _ (Or.inr (by simp))
  have hpb : ∀ l, Commute (d.κ f) (d.L.pb l) := fun l => hk f _ (by simp [TL.siteOps])
  obtain ⟨hA, hB⟩ := Formalism.FourierDecayAlt.P.MAx3.Q.comm_Tvprod d.L (d.κ f) hpb (fun l => hf _ (m_cb d.L l))
    (fun l => hf _ (m_cbi d.L l)) y
  have hA' : Commute (d.κ f) (d.L.Avr y) := hA
  have hB' : Commute (d.κ f) (d.L.Bvr y) := hB
  have hDr : Commute (d.κ f) d.L.Dr := Commute.list_prod_right _ _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact hf _ (m_c d.L l)
  have hDrb : Commute (d.κ f) d.L.Drb := Commute.list_prod_right _ _ fun x hx => by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact hf _ (m_cb d.L l)
  have hm : Commute (d.κ f) (d.L.m0 y) :=
    hn.neg_right.sub_right ((Algebra.commutes _ _).symm |> fun h : Commute (d.κ f) (algebraMap ℂ A (y - 1/2)) =>
      h.mul_right ((hf _ (m_ζ d.L)).mul_right (hf _ (m_GGi d.L))))
  exact ⟨hDrb.mul_right hA', (hDr.mul_right (hf _ (m_GG d.L))).mul_right ((hm.mul_right hA').add_right hB')⟩

omit [StarModule ℂ A] in
theorem ss_rule (d : Q.NFData P A) (h : HatHyp d) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ) :
    d.L.Ahatv Y * ssn d i = ssn d i * d.L.Ahatv (Y - 1) ∧ d.L.R0v Y * ssn d i = ssn d i * d.L.R0v (Y - 1) := by
  obtain ⟨-, -, hR, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 i hi
  have hc := hR.2.2.1 i
  have h := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L (d.SS i) 0 (fun x hx => (hc x (Or.inl (Or.inl hx))).symm)
    (fun l => (hc _ (Or.inl (Or.inr ⟨l, rfl⟩))).symm) (fun l => (hc _ (Or.inr ⟨l, rfl⟩)).symm) h1 h2
    (fun x _ => by simp) (fun l => by simp) (fun l => by simp) (by simp) (by simp) Y
  exact ⟨h.2.2.1, h.2.2.2.1⟩

theorem sss_rule (d : Q.NFData P A) (h : HatHyp d) (i : ℕ) (hi : i ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ) :
    d.L.Ahatv Y * star (ssn d i) = star (ssn d i) * d.L.Ahatv (Y + 1) ∧
      d.L.R0v Y * star (ssn d i) = star (ssn d i) * d.L.R0v (Y + 1) := by
  obtain ⟨-, hS, hR, sp, sc, sci, -⟩ := h
  obtain ⟨h1, h2⟩ := hR.2.2.2.2.1 i hi
  have hc := hR.2.2.1 i
  obtain ⟨sz, szb, szi, szbi, sg, sgi⟩ := Formalism.FourierDecayAlt.P.TLA.M2.star_fns d.L hS
  have sn : star d.L.nab = d.L.nabs := hS.2.1
  have sns : star d.L.nabs = d.L.nab := by rw [← sn, star_star]
  have scb : ∀ l, star (d.L.cb l) = d.L.c l := fun l => by rw [← sc, star_star]
  have scbi : ∀ l, star (d.L.cbi l) = d.L.ci l := fun l => by rw [← sci, star_star]
  have spb : ∀ l, star (d.L.pb l) = -d.L.p l := fun l => by
    rw [← star_star (d.L.p l), sp, star_neg, neg_neg]
  have sf : ∀ x ∈ d.L.fns, star x ∈ d.L.fns := by
    intro x hx
    simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl))
    · rw [sc]; exact m_cb d.L l
    · rw [sci]; exact m_cbi d.L l
    · rw [scb]; exact m_c d.L l
    · rw [scbi]; exact m_ci d.L l
    · rw [sz]; exact m_ζb d.L
    · rw [szi]; exact m_ζbi d.L
    · rw [szb]; exact m_ζ d.L
    · rw [szbi]; exact m_ζi d.L
    · rw [sg]; exact m_GG d.L
    · rw [sgi]; exact m_GGi d.L
  have hf : ∀ x ∈ d.L.fns, Commute (star (d.SS i)) x := fun x hx => by
    have := (hc _ (Or.inl (Or.inl (sf x hx)))).star_star
    rwa [star_star] at this
  have hp : ∀ l, Commute (star (d.SS i)) (d.L.p l) := fun l => by
    have := (hc _ (Or.inr ⟨l, rfl⟩)).star_star
    rw [spb] at this
    exact Commute.neg_right_iff.1 this
  have hpb : ∀ l, Commute (star (d.SS i)) (d.L.pb l) := fun l => by
    have := (hc _ (Or.inl (Or.inr ⟨l, rfl⟩))).star_star
    rw [sp] at this
    exact Commute.neg_right_iff.1 this
  have c1 : star (d.SS i) * (d.L.GGi * d.L.ζb) = d.L.ζb * d.L.GGi * star (d.SS i) := by
    rw [((hf _ (m_GGi d.L)).mul_right (hf _ (m_ζb d.L))).eq, d.L.fns_comm _ (m_GGi d.L) _ (m_ζb d.L)]
  have c2 : star (d.SS i) * (d.L.GGi * d.L.ζ) = d.L.ζ * d.L.GGi * star (d.SS i) := by
    rw [((hf _ (m_GGi d.L)).mul_right (hf _ (m_ζ d.L))).eq, d.L.fns_comm _ (m_GGi d.L) _ (m_ζ d.L)]
  have k1 : d.L.nab * star (d.SS i) = star (d.SS i) * d.L.nab + d.L.ζb * d.L.GGi * star (d.SS i) := by
    have := congrArg star h2
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, sns, sz, sgi] at this
    rw [← c1, this]; abel
  have k2 : d.L.nabs * star (d.SS i) = star (d.SS i) * d.L.nabs + d.L.ζ * d.L.GGi * star (d.SS i) := by
    have := congrArg star h1
    rw [star_mul, star_sub, star_mul, star_mul, star_mul, sn, szb, sgi] at this
    rw [← c2, this]; abel
  have sDrb : star d.L.Drb = d.L.Dr := by
    unfold LevelData.Drb LevelData.Dr
    rw [star_listProd, List.map_ofFn]
    have : (star ∘ d.L.cb) = d.L.c := funext scb
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (m_c d.L l)
  have sDri : star d.L.Dri = d.L.Drbi := by
    unfold LevelData.Dri LevelData.Drbi
    rw [star_listProd, List.map_ofFn]
    have : (star ∘ d.L.ci) = d.L.cbi := funext sci
    rw [this, rev_prod d.L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact memF d.L (m_cbi d.L l)
  have e : star (ssn d i) = star (d.SS i) * (d.L.Dr * d.L.Drbi) := by
    rw [ssn, star_mul, star_mul, sDrb, sDri, cl_comm d.L (memDrbi d.L) (memDr d.L)]
  have h := Formalism.FourierDecayAlt.P.intertwinerConjugation _ P.r d.L 0 (star (d.SS i)) (fun x _ => by simp) (fun l => by simp)
    (fun l => by simp) (by simp) (by simp) (fun x hx => (hf x hx).symm) (fun l => (hp l).symm)
    (fun l => (hpb l).symm) k1 k2 Y
  rw [e]
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

end

theorem minus_hats_pass_generators :
    ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d →
      ∀ b ∈ bset d, ∀ y : ℂ,
        d.L.Ahatv y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0v y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  intro P A _ _ _ _ d h b hb y
  have gen : ∀ {x}, x ∈ bset d → x ∈ bmon d := fun h => Submonoid.subset_closure h
  have mDD : d.L.D * d.L.Dbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mDbD : d.L.Db * d.L.Di ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζi : d.L.ζi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζbi : d.L.ζbi ∈ bmon d := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have hdrv : d.L.Dr * d.L.Dbi ∈ bmon d := by
    rw [drv_eq]; exact Submonoid.mul_mem _ mDD mζi
  have sA : ∀ {x}, x ∈ bmon d → ∀ y, x * d.L.Ahatv y ∈ nfSpan d (hats d.L) 0 0 1 := fun hx y =>
    mem_span d hx (Or.inl (Or.inr ⟨y, rfl⟩))
  have sR : ∀ {x}, x ∈ bmon d → ∀ y, x * d.L.R0v y ∈ nfSpan d (hats d.L) 0 0 1 := fun hx y =>
    mem_span d hx (Or.inr ⟨y, rfl⟩)
  have hInv := Formalism.FourierDecayAlt.P.inverseCommutators _ P.r d.L y
  have hb' := gen hb
  rcases hb with (((hb | ⟨f, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · rw [← hInv.2.2.2.2.2.1, ← hInv.2.2.2.2.2.2.1]
      exact ⟨sA hb' _, sR hb' _⟩
    · rw [← hInv.2.2.1, vgen_ζbi_R]
      refine ⟨sA hb' _, Submodule.add_mem _ (sR hb' _) ?_⟩
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (sA mDD _))
        (Submodule.smul_mem _ _ (sA (Submonoid.mul_mem _ (Submonoid.mul_mem _ mζi mζbi) mDD) _))
    · rw [vgen_DD_A, vgen_DD_R]
      exact ⟨sA hb' _, Submodule.add_mem _ (sR hb' _) (Submodule.smul_mem _ _ (sA (Submonoid.mul_mem _ mDD hdrv) _))⟩
    · rw [vgen_DbD_A, vgen_DbD_R]
      exact ⟨sA hb' _, Submodule.add_mem _ (sR hb' _) (Submodule.smul_mem _ _ (sA (Submonoid.mul_mem _ mDbD hdrv) _))⟩
  · rw [← (kap_comm d h f y).1.eq, ← (kap_comm d h f y).2.eq]
    exact ⟨sA hb' _, sR hb' _⟩
  · have := ss_rule d h i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) y
    rw [this.1, this.2]
    exact ⟨sA hb' _, sR hb' _⟩
  · have := sss_rule d h i (Finset.mem_Icc.2 (Set.mem_Icc.1 hi)) y
    simp only [] at hb' ⊢
    rw [this.1, this.2]
    exact ⟨sA hb' _, sR hb' _⟩

end GlobalTheory.HatNF.GenMinus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsTaylorCoeffLeibnizRule
section
namespace GlobalTheory.HatNF.TaylorMinus

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

def Dg (L : LevelData A r) (Y : ℂ) (D : ℕ) (Z : ℂ → A) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (x : ι → A), (∀ i, d i ≤ D) ∧
    (∀ s : ℂ, Z (Y - s) = ∑ i, s ^ d i • x i) ∧
    ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = ∑ i, m (q + d i) * x i

variable {L : LevelData A r} {Y : ℂ}

theorem Dg.mono {D E : ℕ} {Z : ℂ → A} (h : Dg L Y D Z) (hDE : D ≤ E) : Dg L Y E Z := by
  obtain ⟨ι, hι, d, x, hd, h1, h2⟩ := h
  exact ⟨ι, hι, d, x, fun i => (hd i).trans hDE, h1, h2⟩

theorem Dg.add {D : ℕ} {Z W : ℂ → A} (h : Dg L Y D Z) (h' : Dg L Y D W) :
    Dg L Y D (fun y => Z y + W y) := by
  obtain ⟨ι, _, d, x, hd, hs, hm⟩ := h
  obtain ⟨κ, _, e, w, he, hs', hm'⟩ := h'
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim d e, Sum.elim x w, ?_, fun s => ?_, fun m hmr q => ?_⟩
  · rintro (i | j)
    exacts [hd i, he j]
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hs, hs']
  · simp only [add_mul, hm m hmr q, hm' m hmr q, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem Dg.mul {D E : ℕ} {Z W : ℂ → A} (h : Dg L Y D Z) (h' : Dg L Y E W) :
    Dg L Y (D + E) (fun y => Z y * W y) := by
  obtain ⟨ι, _, d, x, hd, hs, hm⟩ := h
  obtain ⟨κ, _, e, w, he, hs', hm'⟩ := h'
  refine ⟨ι × κ, inferInstance, fun p => d p.1 + e p.2, fun p => x p.1 * w p.2,
    fun p => Nat.add_le_add (hd p.1) (he p.2), fun s => ?_, fun m hmr q => ?_⟩
  · dsimp only
    rw [hs, hs', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, pow_add]
  · dsimp only
    rw [mul_assoc, hm' m hmr q, Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hm m hmr (q + e j), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, show q + e j + d i = q + (d i + e j) by omega]

theorem dg_const (f : A) (hf : ∀ m : ℕ → A, MulRel L m → ∀ q, Commute f (m q)) :
    Dg L Y 0 (fun _ => f) := ⟨Unit, inferInstance, fun _ => 0, fun _ => f, fun _ => le_rfl, fun s => by simp,
    fun m hm q => by simp [(hf m hm q).eq]⟩

theorem dg_lin (Z : ℂ → A) (u : A) (h1 : ∀ s, Z (Y - s) = Z Y + s • u)
    (h2 : ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = m q * Z Y + m (q + 1) * u) : Dg L Y 1 Z := ⟨Fin 2, inferInstance, ![0, 1], ![Z Y, u], by intro i; fin_cases i <;> simp,
    fun s => by simp [Fin.sum_univ_two, h1], fun m hm q => by simp [Fin.sum_univ_two, h2 m hm q]⟩

theorem Dg.out {D : ℕ} {Z : ℂ → A} (h : Dg L Y D Z) :
    ∃ X : ℕ → A, (∀ s : ℂ, Z (Y - s) = ∑ j ∈ Finset.range (D + 1), s ^ j • X j) ∧
      ∀ m : ℕ → A, MulRel L m → ∀ q, Z Y * m q = ∑ j ∈ Finset.range (D + 1), m (q + j) * X j := by
  obtain ⟨ι, _, d, x, hd, h1, h2⟩ := h
  have hmap : ∀ i ∈ (Finset.univ : Finset ι), d i ∈ Finset.range (D + 1) :=
    fun i _ => Finset.mem_range.2 (Nat.lt_succ_of_le (hd i))
  refine ⟨fun j => ∑ i ∈ Finset.univ.filter (fun i => d i = j), x i, fun s => ?_, fun m hm q => ?_⟩
  · rw [h1, ← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  · rw [h2 m hm q, ← Finset.sum_fiberwise_of_maps_to hmap]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]

theorem comm_c {m : ℕ → A} (hm : MulRel L m) (q : ℕ) (l : Fin r) : Commute (L.c l) (m q) := (hm q).1 _ (by simp [LevelData.fns])

theorem comm_cb {m : ℕ → A} (hm : MulRel L m) (q : ℕ) (l : Fin r) : Commute (L.cb l) (m q) := (hm q).1 _ (by simp [LevelData.fns])

theorem comm_cbi {m : ℕ → A} (hm : MulRel L m) (q : ℕ) (l : Fin r) : Commute (L.cbi l) (m q) := (hm q).1 _ (by simp [LevelData.fns])

theorem comm_GG {m : ℕ → A} (hm : MulRel L m) (q : ℕ) : Commute L.GG (m q) := (hm q).1 _ (by simp [LevelData.fns])

theorem comm_zG {m : ℕ → A} (hm : MulRel L m) (q : ℕ) : Commute (L.ζ * L.GGi) (m q) := ((hm q).1 _ (by simp [LevelData.fns])).mul_left ((hm q).1 _ (by simp [LevelData.fns]))

theorem comm_prod {g : Fin r → A} {a : A} (h : ∀ l, Commute (g l) a) : Commute (List.ofFn g).prod a := Commute.list_prod_left _ _ fun x hx => by
    simp only [List.mem_ofFn] at hx
    obtain ⟨l, rfl⟩ := hx
    exact h l

theorem dg_Tvl (l : Fin r) (i j : Fin 2) : Dg L Y 1 (fun y => L.Tvl y l i j) := by
  fin_cases i <;> fin_cases j
  · show Dg L Y 1 (fun y => algebraMap ℂ A y - L.pb l)
    refine dg_lin _ (-1) (fun s => ?_) (fun m hm q => ?_)
    · rw [map_sub, smul_neg, Algebra.smul_def, mul_one]
      abel
    · rw [sub_mul, mul_sub, ((hm q).2.2.1 l), Algebra.commutes, mul_neg, mul_one]
      abel
  · show Dg L Y 1 (fun _ => -L.cb l)
    exact (dg_const _ fun m hm q => (comm_cb hm q l).neg_left).mono zero_le_one
  · show Dg L Y 1 (fun _ => L.cbi l)
    exact (dg_const _ fun m hm q => comm_cbi hm q l).mono zero_le_one
  · show Dg L Y 1 (fun _ => (0 : A))
    exact (dg_const _ fun m hm q => Commute.zero_left _).mono zero_le_one

theorem dg_list (ls : List (Fin r)) (i j : Fin 2) :
    Dg L Y ls.length (fun y => (ls.map (L.Tvl y)).prod i j) := by
  induction ls generalizing i j with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.length_nil]
    exact dg_const _ fun m hm q => by
      rw [Matrix.one_apply]
      split_ifs <;> simp
  | cons l ls ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two, List.length_cons]
    exact (Dg.add ((dg_Tvl l i 0).mul (ih 0 j)) ((dg_Tvl l i 1).mul (ih 1 j))).mono (by omega)

theorem dg_Tvprod (i j : Fin 2) : Dg L Y r (fun y => L.Tvprod y i j) := by
  have h := dg_list (L := L) (Y := Y) (List.ofFn (fun l : Fin r => l)).reverse i j
  rw [List.length_reverse, List.length_ofFn] at h
  have e : (fun y => L.Tvprod y i j) =
      fun y => (((List.ofFn (fun l : Fin r => l)).reverse).map (L.Tvl y)).prod i j := by
    funext y
    simp only [LevelData.Tvprod, List.map_reverse, List.map_ofFn]
    rfl
  rw [e]
  exact h

theorem backwardTaylorDegree_one_mirrorLetter : Dg L Y 1 L.m0 := by
  show Dg L Y 1 (fun y => -L.nabs - algebraMap ℂ A (y - 1 / 2) * (L.ζ * L.GGi))
  refine dg_lin _ (L.ζ * L.GGi) (fun s => ?_) (fun m hm q => ?_)
  · rw [show Y - s - 1 / 2 = (Y - 1 / 2) - s by ring, map_sub, sub_mul, Algebra.smul_def]
    abel
  · have e1 := (hm q).2.2.2.2
    have c1 := (comm_zG hm q).eq
    have c2 := (comm_zG hm (q + 1)).eq
    have c3 := Algebra.commutes (R := ℂ) (Y - 1 / 2) (m q)
    have e0 : (-L.nabs - algebraMap ℂ A (Y - 1 / 2) * (L.ζ * L.GGi)) * m q =
        -(L.nabs * m q) - algebraMap ℂ A (Y - 1 / 2) * (L.ζ * L.GGi * m q) := by noncomm_ring
    rw [e0, e1, c1, ← mul_assoc (algebraMap ℂ A (Y - 1 / 2)) (m q) (L.ζ * L.GGi), c3, c2]
    noncomm_ring

theorem dg_Ahatv : Dg L Y (r + 1) L.Ahatv := by
  have hc : Dg L Y 0 (fun _ => L.Drb) := dg_const _ fun m hm q => comm_prod fun l => comm_cb hm q l
  exact (hc.mul (dg_Tvprod 0 0)).mono (by omega)

theorem backwardTaylorDegree_minusHatR : Dg L Y (r + 1) L.R0v := by
  have hc : Dg L Y 0 (fun _ => L.Dr * L.GG) :=
    dg_const _ fun m hm q => (comm_prod fun l => comm_c hm q l).mul_left (comm_GG hm q)
  have hA : Dg L Y r (fun y => L.Avr y) := dg_Tvprod 0 0
  have hB : Dg L Y (1 + r) (fun y => L.Bvr y) := (dg_Tvprod 1 0).mono (by omega)
  exact (hc.mul ((backwardTaylorDegree_one_mirrorLetter.mul hA).add hB)).mono (by omega)

theorem taylor_minus : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahatv (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0v (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahatv Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0v Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  intro A _ _ r L Y
  obtain ⟨Xa, ha1, ha2⟩ := (dg_Ahatv (L := L) (Y := Y)).out
  obtain ⟨Xr, hr1, hr2⟩ := (backwardTaylorDegree_minusHatR (L := L) (Y := Y)).out
  exact ⟨Xa, Xr, ha1, hr1, fun m hm q => ⟨ha2 m hm q, hr2 m hm q⟩⟩

end GlobalTheory.HatNF.TaylorMinus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.VecPolyMemSpanValuesStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_values_of_vector_polynomial : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (Z : ℂ → V) (X : ℕ → V) (ν : Fin n → ℂ), Function.Injective ν → (∀ s : ℂ, Z s = ∑ j ∈ Finset.range n, s ^ j • X j) → (∀ j, j < n → X j ∈ Submodule.span ℂ (Set.range fun i => Z (ν i))) ∧ ∀ s : ℂ, Z s ∈ Submodule.span ℂ (Set.range fun i => Z (ν i)) := by
  first | exact @GlobalTheory.vecPoly_mem_span_values | exact GlobalTheory.vecPoly_mem_span_values | (intros; apply GlobalTheory.vecPoly_mem_span_values <;> assumption)
end

