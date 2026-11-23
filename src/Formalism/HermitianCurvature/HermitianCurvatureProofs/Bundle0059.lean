module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.Bundle0008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0055
public import Lemmata.GeneralBFactSecondTerForm.Imports
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0041
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDomainMeasurable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFApxDomThQ
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutBP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

theorem ccleQ_nonneg {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {F : B.Mat k r → E} {b : ℝ} (h : B.CCle A m F b) : 0 ≤ b := by
  obtain ⟨g, hg⟩ : ∃ g, g ∈ B.GV k r := ⟨1, by simp [B.GV, Formalism.QuantumDeterminants.UH]⟩
  have h1 := h.2 [] [] (by simp) (by simp) (by simp) g hg
  have h2 : 0 ≤ B.gN g ^ A * ‖B.dLR [] [] F g‖ :=
    mul_nonneg (Real.rpow_nonneg (gN_pos hg).le _) (norm_nonneg _)
  linarith

theorem ccleQ_mono_c {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {F : B.Mat k r → E} {b b' : ℝ} (h : B.CCle A m F b) (hb : b ≤ b') : B.CCle A m F b' := ⟨h.1, fun u v hu hv hl g hg => (h.2 u v hu hv hl g hg).trans hb⟩

private theorem le_foldr_max_zero_of_mem : ∀ (l : List ℕ), ∀ x ∈ l, x ≤ l.foldr max 0 := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons y t ih =>
    intro x hx
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih x h) (le_max_right _ _)

theorem word_le_opOrder {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) :
    ∀ T ∈ Θ, T.word.length ≤ B.opOrder Θ := by
  intro T hT
  unfold B.opOrder
  exact le_foldr_max_zero_of_mem _ _ (List.mem_map_of_mem hT)

theorem jdCCLowerQ {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) (d A : ℝ)
    (hd : 0 ≤ d) (hG : CutMP.GlobCoef Θ d) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ), B.CkOn ⊤ (B.GV k r) F →
      B.CCle A (m + B.opOrder Θ) F b → B.CCle (A - d) m (B.opApply Θ F) (K * b) := by
  have _hd := hd
  set o := B.opOrder Θ with ho
  have hO : IsOpen (∅ : Set (B.Mat k r)) := isOpen_empty
  have hcov : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) ∨ g ∈ B.GV k r := fun g hg => Or.inr hg

  have hterm : ∀ T ∈ Θ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ),
      B.CCle A (m + o) F b → B.CCle (A - d) m (ap T.coef (B.Rw T.word F)) (K * b) := by
    intro T hT
    obtain ⟨hc1, -, hcb⟩ := hG T hT
    obtain ⟨C, hC⟩ := hcb m
    set s : ℂ := (((T.word.map nz).prod : ℝ) : ℂ) with hs
    refine ⟨2 ^ m * (|C| * ‖s‖), by positivity, fun F b hF => ?_⟩
    have hb0 : 0 ≤ b := ccleQ_nonneg hF
    have hlen : T.word.length ≤ o := word_le_opOrder Θ T hT
    have hF1 : B.CCle A (m + (T.word.map nrm).length) F b :=
      CCle_mono_m (by simp; omega) hF
    have hunit : ∀ X ∈ T.word.map nrm, unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
      exact nrm_unit (T.word_lie Y hY)
    have hR : B.CCle A m (B.Rw T.word F) (‖s‖ * b) := by
      rw [Rw_scale]
      exact CCle_smul s (CCle_Rw hunit hF1)
    have hR' : B.CCle (A - d + d) m (B.Rw T.word F) (‖s‖ * b) := by rw [sub_add_cancel]; exact hR
    have hP := prodBound hO hcov (sCkOn_mono le_top hc1)
      (fun u v hu hv hl g hg _ => (hC u v hu hv hl g hg).1) hR' (fun g _ hg => by simp at hg)
    refine ccleQ_mono_c hP (le_of_eq ?_)
    rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) hb0)]
    ring

  have hsum : ∀ L : List (B.DTerm k r Wp Wq), (∀ T ∈ L, T ∈ Θ) → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ), B.CCle A (m + o) F b →
        B.CCle (A - d) m (fun g => (L.map fun T => ap T.coef (B.Rw T.word F) g).sum) (K * b) := by
    intro L
    induction L with
    | nil =>
      intro _
      refine ⟨0, le_rfl, fun F b _ => ?_⟩
      simpa using (CCle_zero : B.CCle (A - d) m (fun _ : B.Mat k r => (0 : Wq →L[ℂ] Wp)) 0)
    | cons T L ih =>
      intro hL
      obtain ⟨K₁, hK₁, h₁⟩ := hterm T (hL T (by simp))
      obtain ⟨K₂, hK₂, h₂⟩ := ih fun S hS => hL S (by simp [hS])
      refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, fun F b hF => ?_⟩
      have h := CCle_add (h₁ F b hF) (h₂ F b hF)
      have e : (K₁ + K₂) * b = K₁ * b + K₂ * b := by ring
      rw [e]
      simpa using h
  obtain ⟨K, hK, hKb⟩ := hsum Θ fun T hT => hT
  refine ⟨K, hK, fun F b _ hF => ?_⟩
  have hop : B.opApply Θ F = fun g => (Θ.map fun T => ap T.coef (B.Rw T.word F) g).sum := rfl
  rw [hop]
  exact hKb F b hF

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameThresholdBoundHolds
section
namespace Formalism.FourierDecayAlt.P.PBD

open Formalism.FourierDecayAlt

def FrameThresholdBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) (w : ι),
    0 < G.g → 0 < G.lenI → 28 * Real.exp 1 ≤ C →
    (∀ one, 0 ≤ J.supA G de de' T T' l one w) →
    (∀ (b s : ℕ) (Q cg : ℝ), 1 ≤ b → 0 ≤ Q → Q ≤ Real.exp 1 → 0 ≤ cg →
      cg ≤ (28 * G.N / G.lenI) ^ (2 * (b - 1) + s) →
      (2 * Real.pi / G.g) ^ (-(S6.nuBlock G.r b s)) * Q * cg *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w ≤
        J.thrS G C de de' T T' l b (s + 1) w) ∧
    (∀ (b : ℕ) (Q cg : ℝ), 1 ≤ b → 0 ≤ Q → Q ≤ Real.exp 1 → 0 ≤ cg →
      cg ≤ (28 * G.N / G.lenI) ^ (2 * (b - 1)) →
      √((2 * Real.pi / G.g) ^ (-(2 * S6.nuBlock G.r b ((G.r : ℤ) + 2 - b))) * Q * cg *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹) ≤
        J.thrP G C de de' T T' l b w)

theorem pow_bound (C x : ℝ) (n : ℕ) (hx : 0 ≤ x) (hC : 28 * Real.exp 1 ≤ C) :
    Real.exp 1 * (28 * x) ^ n ≤ C * (C * x) ^ n := by
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hC28 : (28 : ℝ) ≤ C := by nlinarith
  have heC : Real.exp 1 ≤ C := by nlinarith
  have hpow : (28 * x) ^ n ≤ (C * x) ^ n := pow_le_pow_left₀ (by positivity) (by nlinarith) n
  exact mul_le_mul heC hpow (by positivity) (by linarith)

theorem frame_threshold_bound : FrameThresholdBound := by
  intro ι _ G C de de' T T' l w hg hI hC hA
  have hN : 0 ≤ G.N := by unfold Sz.Glob.N; positivity
  have hkg : 0 < 2 * Real.pi / G.g := by positivity
  have key : ∀ (n : ℕ) (Q cg : ℝ), 0 ≤ Q → Q ≤ Real.exp 1 → 0 ≤ cg → cg ≤ (28 * G.N / G.lenI) ^ n →
      Q * cg ≤ C * (C * (G.N / G.lenI)) ^ n := by
    intro n Q cg h0 h1 h2 h3
    have hx : 0 ≤ G.N / G.lenI := div_nonneg hN hI.le
    rw [mul_div_assoc] at h3
    calc Q * cg ≤ Real.exp 1 * (28 * (G.N / G.lenI)) ^ n := mul_le_mul h1 h3 h2 (by positivity)
      _ ≤ C * (C * (G.N / G.lenI)) ^ n := pow_bound C _ n hx hC
  refine ⟨fun b s Q cg hb h0 h1 h2 h3 => ?_, fun b Q cg hb h0 h1 h2 h3 => ?_⟩
  · have hA' := hA (decide (b = 1 ∧ s + 1 = 1))
    have hk := key (2 * (b - 1) + s) Q cg h0 h1 h2 h3
    have hz : (2 * Real.pi / G.g) ^ (-(S6.nuBlock G.r b s)) =
        (2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hkg.ne']
      congr 1
      unfold S6.nuBlock
      omega
    have hn : 2 * (b - 1) + (s + 1) - 1 = 2 * (b - 1) + s := by omega
    unfold J.thrS Sz.lamThreshold Sz.Glob.m
    rw [hn, hz, show C * (2 * Real.pi / G.g) * G.N / G.lenI = (C * (G.N / G.lenI)) * (2 * Real.pi / G.g) by ring,
      mul_pow]
    have hP : 0 ≤ (2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
        J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w := mul_nonneg (by positivity) hA'
    calc (2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ * Q * cg *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w
        = ((2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w) * (Q * cg) := by ring
      _ ≤ ((2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w) * (C * (C * (G.N / G.lenI)) ^ (2 * (b - 1) + s)) :=
          mul_le_mul_of_nonneg_left hk hP
      _ = C * (((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ * J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w) *
          ((C * (G.N / G.lenI)) ^ (2 * (b - 1) + s) * (2 * Real.pi / G.g) ^ (2 * (b - 1) + s)) := by ring
  · have hA' := hA false
    have hk := key (2 * (b - 1)) Q cg h0 h1 h2 h3
    have hz : (2 * Real.pi / G.g) ^ (-(2 * S6.nuBlock G.r b ((G.r : ℤ) + 2 - b))) =
        (2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hkg.ne']
      congr 1
      unfold S6.nuBlock
      omega
    unfold J.thrP Sz.lamPrimeSq Sz.Glob.m
    apply Real.sqrt_le_sqrt
    rw [hz, show C * G.N / G.lenI = C * (G.N / G.lenI) by ring]
    have hP : 0 ≤ (2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
        J.supA G de de' T T' l false w * (√(T * T'))⁻¹ := mul_nonneg (mul_nonneg (by positivity) hA') (by positivity)
    calc (2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ * Q * cg *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹
        = ((2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹) * (Q * cg) := by ring
      _ ≤ ((2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹) * (C * (C * (G.N / G.lenI)) ^ (2 * (b - 1))) :=
          mul_le_mul_of_nonneg_left hk hP
      _ = C * (((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ * J.supA G de de' T T' l false w) *
          (2 * Real.pi / G.g) ^ (2 * b - 1) * (√(T * T'))⁻¹ * (C * (G.N / G.lenI)) ^ (2 * (b - 1)) := by ring

end Formalism.FourierDecayAlt.P.PBD

theorem Formalism.FourierDecayAlt.P.frame_threshold_bound_holds : Formalism.FourierDecayAlt.P.PBD.FrameThresholdBound := Formalism.FourierDecayAlt.P.PBD.frame_threshold_bound
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HighestWeightPolynomials
section
open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.HighestWeightPolynomials

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem map_eq_of_cpol {n : ℕ} (m m' : Fin n → ℂ) (h : ∀ w, cpol m w = cpol m' w) :
    Multiset.map m univ.val = Multiset.map m' univ.val := by
  have key : ∀ (f : Fin n → ℂ) (w : ℂ), cpol f w = Polynomial.eval w
      ((Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Multiset.map (fun j => - f j) univ.val)).prod) := by
    intro f w
    rw [Multiset.map_map, Polynomial.eval_multiset_prod, Multiset.map_map]
    simp [cpol, Finset.prod, Function.comp_def]
  have hp : (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Multiset.map (fun j => - m j) univ.val)).prod =
      (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Multiset.map (fun j => - m' j) univ.val)).prod :=
    Polynomial.funext (fun w => by rw [← key, ← key, h])
  have hr := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  have h2 := congrArg (Multiset.map (fun z : ℂ => -z)) hr
  simpa [Multiset.map_map, Function.comp_def] using h2

theorem sdec_re {n : ℕ} {m : Fin n → ℂ} (hm : SDec m) : StrictAnti fun a => (m a).re := by
  intro a b hab
  obtain ⟨N, hN⟩ := hm a b hab
  have h := congrArg Complex.re hN
  simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re] at h
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  show (m b).re < (m a).re
  linarith

theorem sdec_inj {n : ℕ} {m : Fin n → ℂ} (hm : SDec m) : Function.Injective m := by
  intro a b hab
  exact (sdec_re hm).injective (congrArg Complex.re hab)

theorem sdec_shift {n : ℕ} {ν : Fin n → ℂ} (h : ∀ a b : Fin n, a < b → ∃ N : ℕ, ν a - ν b = (N : ℂ)) :
    SDec fun k => ν k - ((k : ℕ) : ℂ) := by
  intro a b hab
  obtain ⟨N, hN⟩ := h a b hab
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (Fin.lt_def.1 hab)
  refine ⟨N + d, ?_⟩
  have h1 : ν a = ν b + N := by rw [← hN]; ring
  show ν a - ((a : ℕ) : ℂ) - (ν b - ((b : ℕ) : ℂ)) = _
  rw [hd, h1]
  push_cast
  ring

theorem sdec_shf {n : ℕ} (β : ℂ) {M : Fin n → ℤ} (hM : StrictAnti M) : SDec (shf β M) := by
  intro a b hab
  have h := hM hab
  refine ⟨(M a - M b - 1).toNat, ?_⟩
  have h1 : (((M a - M b - 1).toNat : ℤ) : ℂ) = ((M a - M b - 1 : ℤ) : ℂ) := by
    rw [Int.toNat_of_nonneg (by omega)]
  rw [Int.cast_natCast] at h1
  rw [h1]
  simp only [shf]
  push_cast
  ring

theorem hval_shift {n : ℕ} (ν : Fin n → ℂ) (a b : Fin n) :
    hval (fun c => ν c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) =
      hval ν + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  unfold hval
  have h : ∀ c : Fin n, ((n : ℝ) - ((c : ℕ) : ℝ)) *
      (ν c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℂ).re =
      ((n : ℝ) - ((c : ℕ) : ℝ)) * (ν c).re + (if c = a then ((n : ℝ) - ((c : ℕ) : ℝ)) else 0) -
        (if c = b then ((n : ℝ) - ((c : ℕ) : ℝ)) else 0) := by
    intro c
    split_ifs <;> simp <;> ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

section mod

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem indep_char {ι : Type*} (C : ℂ → Module.End ℂ V) (χ : ι → ℂ → ℂ) (hχ : Function.Injective χ)
    (p : ι → Submodule ℂ V) (hp : ∀ i v, v ∈ p i ↔ ∀ w, C w v = χ i w • v) : iSupIndep p := by
  first | exact Bl.general_b_fact_second_ter_form.goal1 .. | (apply Bl.general_b_fact_second_ter_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_ter_form.goal1 <;> assumption)

theorem hw_cpol {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {m ν : Fin n → ℂ} {v : V} (hE : GlRel E)
    (hv : v ∈ CapSp E m) (hv0 : v ≠ 0) (hw : IsHW E ν v) (w : ℂ) :
    cpol m w = cpol (fun k => ν k - ((k : ℕ) : ℂ)) w := by
  have h1 := quantumDetHighestWeight_holds V n E ν v hE hw w
  rw [mem_CapSp.1 hv w] at h1
  have h2 := smul_left_injective ℂ hv0 h1
  rw [h2]
  unfold cpol
  refine Finset.prod_congr rfl fun k _ => ?_
  ring

end mod

end Formalism.FourierDecayAlt.P.HighestWeightPolynomials

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr HighestWeightPolynomials

theorem separating_polynomials : Qr.SepPoly := by
  intro n m m' h hm'
  have hmap := map_eq_of_cpol m m' h
  have hnd : (Multiset.map m univ.val).Nodup := by
    rw [hmap]
    exact Multiset.Nodup.map (sdec_inj hm') univ.nodup
  refine ⟨fun a b hab => Multiset.inj_on_of_nodup_map hnd a (Finset.mem_univ a) b (Finset.mem_univ b) hab, ?_⟩
  intro hm
  have hmem : ∀ a, ∃ b, m' b = m a := by
    intro a
    have h1 : m a ∈ Multiset.map m univ.val := Multiset.mem_map_of_mem m (Finset.mem_univ a)
    rw [hmap, Multiset.mem_map] at h1
    obtain ⟨b, _, hb⟩ := h1
    exact ⟨b, hb⟩
  have hmem' : ∀ a, ∃ b, m b = m' a := by
    intro a
    have h1 : m' a ∈ Multiset.map m' univ.val := Multiset.mem_map_of_mem m' (Finset.mem_univ a)
    rw [← hmap, Multiset.mem_map] at h1
    obtain ⟨b, _, hb⟩ := h1
    exact ⟨b, hb⟩
  have hr : (fun a => (m a).re) = fun a => (m' a).re := by
    rw [← StrictAnti.range_inj (sdec_re hm) (sdec_re hm')]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := hmem a
      exact ⟨b, by simp only [hb]⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := hmem' a
      exact ⟨b, by simp only [hb]⟩
  funext a
  obtain ⟨b, hb⟩ := hmem a
  have h1 : (m' b).re = (m' a).re := by rw [hb]; exact congrFun hr a
  rw [← hb, (sdec_re hm').injective h1]

theorem capelli_stabilizer : Qr.CapStab := by
  intro V _ _ n E m hE
  refine ⟨fun a b v hv => ?_, fun X hX v hv => ?_⟩
  · rw [mem_CapSp] at hv ⊢
    intro w
    have h := qDetCentral_of quantumMinorRowSkew_holds quantumMinorColSkew_holds (Module.End ℂ V) n E hE w a b
    have h2 := LinearMap.congr_fun h v
    simp only [Module.End.mul_apply] at h2
    rw [h2, hv w, map_smul]
  · rw [mem_CapSp] at hv ⊢
    intro w
    have h : Commute X (qdet E w) := QuantumMinorCommutation.commute_qminor E id id w X (fun s s' => hX _ _)
    have h2 := LinearMap.congr_fun h.eq v
    simp only [Module.End.mul_apply] at h2
    rw [← h2, hv w, map_smul]

theorem qr_capSing_of (hD : Qr.SingDom) (hX : Qr.ExistsSingMax) : Qr.CapSing := by
  intro V _ _ _ n E m hE hne
  obtain ⟨ν, v, hv, hv0, hw, _⟩ := hX V n E hE (CapSp E m) (capelli_stabilizer V n E m hE).1 hne
  refine ⟨(separating_polynomials n m _ (hw_cpol hE hv hv0 hw) (sdec_shift (hD V n E ν v hE hw hv0))).1, ?_⟩
  intro hm ν' v' hv' hv0' hw' j
  have h := (separating_polynomials n m _ (hw_cpol hE hv' hv0' hw') (sdec_shift (hD V n E ν' v' hE hw' hv0'))).2 hm
  have h2 : m j = ν' j - ((j : ℕ) : ℂ) := congrFun h j
  rw [h2]
  ring

theorem qr_topWeightSing_of (hX : Qr.ExistsSingMax) (hS : Qr.CapSing) : Qr.TopWeightSing := by
  intro V _ _ _ n E m hE hm x hx hw
  refine ⟨hw, fun a b hab => ?_⟩
  by_contra hne
  have hstab := (capelli_stabilizer V n E m hE).1
  have hx' : E a b x ∈ CapSp E m := hstab a b x hx
  have hbot : CapSp E m ≠ ⊥ := fun h => hne (by rw [h] at hx'; exact (Submodule.mem_bot ℂ).1 hx')
  obtain ⟨ν, v, hv, hv0, hhw, hmax⟩ := hX V n E hE (CapSp E m) hstab hbot
  have hν := (hS V n E m hE hbot).2 hm ν v hv hv0 hhw
  have hwt : ∀ c, E c c (E a b x) = (ν c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) • E a b x := by
    intro c
    have h := LinearMap.congr_fun (hE c c a b) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [hw c, map_smul, sub_eq_iff_eq_add] at h
    rw [h, hν c]
    by_cases h1 : c = a
    · subst h1
      have h2 : ¬ (b = c) := fun h => (ne_of_gt hab) h
      have h3 : ¬ (c = b) := fun h => h2 h.symm
      simp only [if_true, if_neg h2, if_neg h3, LinearMap.zero_apply]
      module
    · by_cases h2 : b = c
      · subst h2
        simp only [if_true, if_neg h1, LinearMap.zero_apply]
        module
      · have h3 : ¬ (c = b) := fun h => h2 h.symm
        simp only [if_neg h1, if_neg h2, if_neg h3, LinearMap.zero_apply]
        module
  have h := hmax _ (E a b x) hx' hne hwt
  rw [hval_shift] at h
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := Nat.cast_lt.2 (Fin.lt_def.1 hab)
  linarith

theorem capelli_independence : Qr.CapIndep := by
  intro V _ _ n E β
  refine indep_char (qdet E) (fun M : {M : Fin n → ℤ // StrictAnti M} => cpol (shf β M.1)) ?_ _
    (fun M v => mem_CapSp)
  intro M M' h
  have h1 := (separating_polynomials n (shf β M.1) (shf β M'.1) (fun w => congrFun h w) (sdec_shf β M'.2)).2
    (sdec_shf β M.2)
  apply Subtype.ext
  funext j
  have h2 := congrFun h1 j
  simp only [shf, add_right_inj] at h2
  exact_mod_cast h2

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.JfJqSmoothOfNnMaj
section
noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem jf_jDom_of_nnMaj : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj → Formalism.FourierDecayAlt.JF.JDom := fun h =>
  Formalism.FourierDecayAlt.P.JFxDs2.jDom_of_parts Formalism.FourierDecayAlt.P.JFxDs3.bessel_domain_measurable (Formalism.FourierDecayAlt.P.JFxDs2.jDomBound_of_nnMaj h)

theorem jf_jConv_of_nnMaj : Formalism.FourierDecayAlt.P.JFxDs2.NNMaj → Formalism.FourierDecayAlt.JF.JConv := fun h =>
  Formalism.FourierDecayAlt.P.JFxDs1.jConv_of_jDom (jf_jDom_of_nnMaj h)

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostDensOfParts
section
namespace Formalism.FourierDecayAlt.P.PBJ

open MeasureTheory Formalism.FourierDecayAlt

def KCls {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Ψ : G.Mat n → V) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ HasCompactSupport Ψ ∧ ∀ Z ∈ tsupport Ψ, G.detM Z ≠ 0

def FubTop : Prop :=
  ∀ (β : ℂ) (p s : ℕ) (σ : Equiv.Perm (Fin (p + s))) (d : Fin (p + s) → ℂ) (σh : Equiv.Perm (Fin p))
    (dh : Fin p → ℂ) (σb : Equiv.Perm (Fin s)) (db : Fin s → ℂ) (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] (Ψ : G.Mat (p + s) → V),
    (∀ i, dh i ≠ 0) → (∀ i, db i ≠ 0) → U.hMat σ d = U.blk2 (U.hMat σh dh) 0 0 (U.hMat σb db) → KCls Ψ →
    U.PhiTop (p := p + s) (s := 0) β σ d Ψ (fun x => x.elim0) =
      U.PhiTop (p := s) (s := 0) β σb db (U.PhiTop (p := p) (s := s) β σh dh Ψ) (fun x => x.elim0)

def FreezeLast : Prop :=
  ∀ (β : ℂ) (p : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (Ψ : G.Mat (p + 1) → V), KCls Ψ → ∀ c : ℂ, c ≠ 0 →
    ∃ Ψc : G.Mat p → V, KCls Ψc ∧ ∀ (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) →
      U.PhiTop (p := p) (s := 1) β σ d Ψ (fun _ _ => c) = U.PhiTop (p := p) (s := 0) β σ d Ψc (fun x => x.elim0)

def OmLongTop : Prop :=
  ∀ β : ℂ, β ≠ 0 → ∀ n : ℕ, ∃ κ : ℂ, κ ≠ 0 ∧
    ∀ (σ : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → ℂ) (z : ℂ) (V : Type) [NormedAddCommGroup V]
      [NormedSpace ℂ V] [CompleteSpace V] (Φ : G.Mat (n + 1) → V),
      z ≠ 0 → U.hMat σ d = G.ptLong (n + 1) z →
      G.OmLong β n Φ z = κ • U.PhiTop (p := n + 1) (s := 0) β σ d Φ (fun x => x.elim0)

def OmBlockTop : Prop :=
  ∀ β : ℂ, β ≠ 0 → ∀ n : ℕ, ∃ κ : ℂ, κ ≠ 0 ∧
    ∀ (σ : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → ℂ) (t c : ℂ) (V : Type) [NormedAddCommGroup V]
      [NormedSpace ℂ V] [CompleteSpace V] (Φ : G.Mat (n + 1) → V),
      t ≠ 0 → c ≠ 0 → U.hMat σ d = G.ptBlock n t c →
      G.OmBlock β n Φ t c = κ • U.PhiTop (p := n + 1) (s := 0) β σ d Φ (fun x => x.elim0)

def KloostDensOfParts : Prop := FubTop → FreezeLast → OmLongTop → OmBlockTop → KB.KloostDens

end Formalism.FourierDecayAlt.P.PBJ
end

