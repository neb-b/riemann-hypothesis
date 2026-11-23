module

public import Mathlib
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CurvNormNonneg
section
noncomputable section

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open scoped ComplexOrder ContDiff

namespace GlobalTheory.HodgeDomain

section Norms

variable {ι n : Type} [Fintype ι] [Fintype n]

def nsq (M : ι → Matrix n n ℂ) (v : ι → n → ℂ) : ℝ := ∑ τ, (star (v τ) ⬝ᵥ M τ *ᵥ v τ).re

theorem nsq_pos {M : ι → Matrix n n ℂ} (hM : ∀ τ, (M τ).PosDef) {v : ι → n → ℂ} (hv : v ≠ 0) : 0 < nsq M v := by
  obtain ⟨τ, hτ⟩ := Function.ne_iff.mp hv
  have hnn : ∀ σ, 0 ≤ (star (v σ) ⬝ᵥ M σ *ᵥ v σ).re := fun σ =>
    (Complex.nonneg_iff.mp ((hM σ).posSemidef.dotProduct_mulVec_nonneg (v σ))).1
  have hp : 0 < (star (v τ) ⬝ᵥ M τ *ᵥ v τ).re :=
    (Complex.pos_iff.mp ((hM τ).dotProduct_mulVec_pos hτ)).1
  unfold nsq
  exact Finset.sum_pos' (fun σ _ => hnn σ) ⟨τ, Finset.mem_univ _, hp⟩

theorem nsq_smul (M : ι → Matrix n n ℂ) (t : ℝ) (v : ι → n → ℂ) : nsq M (t • v) = t ^ 2 * nsq M v := by
  simp only [nsq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Pi.smul_apply, star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
  ring

theorem nsq_zero (M : ι → Matrix n n ℂ) : nsq M 0 = 0 := by simp [nsq]

theorem continuous_nsq (M : ι → Matrix n n ℂ) : Continuous (nsq M) := by
  unfold nsq
  refine continuous_finsetSum _ fun τ _ => Complex.continuous_re.comp ?_
  exact ((continuous_apply τ).star).dotProduct (continuous_const.matrix_mulVec (continuous_apply τ))

theorem exists_bounds {M : ι → Matrix n n ℂ} (hM : ∀ τ, (M τ).PosDef) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ v, a * ‖v‖ ^ 2 ≤ nsq M v ∧ nsq M v ≤ b * ‖v‖ ^ 2 := by
  have hc := continuous_nsq M
  have hpos : ∀ v ∈ Metric.sphere (0 : ι → n → ℂ) 1, 0 < nsq M v := by
    intro v hv
    refine nsq_pos hM ?_
    rintro rfl
    simp at hv
  have hom : ∀ v : ι → n → ℂ, v ≠ 0 → nsq M v = ‖v‖ ^ 2 * nsq M (‖v‖⁻¹ • v) := by
    intro v hv
    rw [nsq_smul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_pow, one_mul]
  have mem : ∀ v : ι → n → ℂ, v ≠ 0 → ‖v‖⁻¹ • v ∈ Metric.sphere (0 : ι → n → ℂ) 1 := by
    intro v hv
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  rcases (Metric.sphere (0 : ι → n → ℂ) 1).eq_empty_or_nonempty with hE | hne
  · refine ⟨1, 1, one_pos, one_pos, fun v => ?_⟩
    have hv : v = 0 := by
      by_contra hv
      have h1 := mem v hv
      rw [hE] at h1
      exact h1
    subst hv
    simp [nsq_zero]
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : ι → n → ℂ) 1).exists_isMinOn hne hc.continuousOn
    obtain ⟨w, -, hmax⟩ := (isCompact_sphere (0 : ι → n → ℂ) 1).exists_isMaxOn hne hc.continuousOn
    refine ⟨nsq M u, max (nsq M w) 1, hpos u hu, lt_of_lt_of_le one_pos (le_max_right _ _), fun v => ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp [nsq_zero]
    · rw [hom v hv]
      have h1 := isMinOn_iff.mp hmin _ (mem v hv)
      have h2 := isMaxOn_iff.mp hmax _ (mem v hv)
      have hn : 0 ≤ ‖v‖ ^ 2 := by positivity
      constructor
      · rw [mul_comm (nsq M u)]
        exact mul_le_mul_of_nonneg_left h1 hn
      · rw [mul_comm (max _ _)]
        exact mul_le_mul_of_nonneg_left (h2.trans (le_max_left _ _)) hn

def ratios (h h0 : ι → Matrix n n ℂ) : Set ℝ := {t | ∃ v, v ≠ 0 ∧ t = nsq h v / nsq h0 v}

def eigLo (h h0 : ι → Matrix n n ℂ) : ℝ := sInf (ratios h h0)

def eigUp (h h0 : ι → Matrix n n ℂ) : ℝ := sSup (ratios h h0)

variable {h h0 : ι → Matrix n n ℂ}

theorem ratios_nonempty [Nonempty ι] [Nonempty n] : (ratios h h0).Nonempty := by
  refine ⟨_, fun _ _ => 1, ?_, rfl⟩
  intro hv0
  have h1 := congrFun (congrFun hv0 (Classical.arbitrary ι)) (Classical.arbitrary n)
  simp at h1

theorem ratios_bounds (hh : ∀ τ, (h τ).PosDef) (hh0 : ∀ τ, (h0 τ).PosDef) :
    ∃ a b : ℝ, 0 < a ∧ ∀ t ∈ ratios h h0, a ≤ t ∧ t ≤ b := by
  obtain ⟨a1, b1, ha1, hb1, H1⟩ := exists_bounds hh
  obtain ⟨a0, b0, ha0, hb0, H0⟩ := exists_bounds hh0
  refine ⟨a1 / b0, b1 / a0, div_pos ha1 hb0, ?_⟩
  rintro t ⟨v, hv, rfl⟩
  have hp0 : 0 < nsq h0 v := nsq_pos hh0 hv
  obtain ⟨l1, u1⟩ := H1 v
  obtain ⟨l0, u0⟩ := H0 v
  constructor
  · rw [div_le_div_iff₀ hb0 hp0]
    nlinarith [mul_le_mul_of_nonneg_left u0 ha1.le, mul_le_mul_of_nonneg_left l1 hb0.le]
  · rw [div_le_div_iff₀ hp0 ha0]
    nlinarith [mul_le_mul_of_nonneg_left u1 ha0.le, mul_le_mul_of_nonneg_left l0 hb1.le]

theorem eigLo_pos [Nonempty ι] [Nonempty n] (hh : ∀ τ, (h τ).PosDef) (hh0 : ∀ τ, (h0 τ).PosDef) :
    0 < eigLo h h0 ∧ eigLo h h0 ≤ eigUp h h0 := by
  obtain ⟨a, b, ha, hab⟩ := ratios_bounds hh hh0
  have hne : (ratios h h0).Nonempty := ratios_nonempty
  have hbb : BddBelow (ratios h h0) := ⟨a, fun t ht => (hab t ht).1⟩
  have hba : BddAbove (ratios h h0) := ⟨b, fun t ht => (hab t ht).2⟩
  unfold eigLo eigUp
  exact ⟨lt_of_lt_of_le ha (le_csInf hne fun t ht => (hab t ht).1), csInf_le_csSup hne hbb hba⟩

end Norms

section Calculus

variable {ι : Type} [Fintype ι] {p q : ℕ}

abbrev Pt (ι : Type) (p q : ℕ) : Type := ι → Matrix (Fin p) (Fin q) ℂ

def dR (f : Pt ι p q → ℂ) (z ξ : Pt ι p q) : ℂ := fderiv ℝ (fun v => f (unflat v)) (flat z) (flat ξ)

def dHol (f : Pt ι p q → ℂ) (z ξ : Pt ι p q) : ℂ := (dR f z ξ - Complex.I * dR f z (Complex.I • ξ)) / 2

def dAnti (f : Pt ι p q → ℂ) (z η : Pt ι p q) : ℂ := (dR f z η + Complex.I * dR f z (Complex.I • η)) / 2

def ddc (f : Pt ι p q → ℝ) (z ξ : Pt ι p q) : ℝ :=
  (dHol (fun w => dAnti (fun u => (f u : ℂ)) w ξ) z ξ).re / Real.pi

def SmoothOn (f : Pt ι p q → ℂ) : Prop := ContDiffOn ℝ ∞ (fun v => f (unflat v)) (DomFlat ι p q)

variable {n : Type} [Fintype n] [DecidableEq n]

def connMat (M : Pt ι p q → ι → Matrix n n ℂ) (z ξ : Pt ι p q) (τ : ι) : Matrix n n ℂ :=
  (M z τ)⁻¹ * Matrix.of fun a b => dHol (fun w => M w τ a b) z ξ

def curvMat (M : Pt ι p q → ι → Matrix n n ℂ) (z ξ η : Pt ι p q) (τ : ι) : Matrix n n ℂ :=
  Matrix.of fun a b => -dAnti (fun w => connMat M w ξ τ a b) z η

def connNorm (h h0 : Pt ι p q → ι → Matrix n n ℂ) (β : Pt ι p q → Pt ι p q → ℝ) (z : Pt ι p q) : ℝ :=
  sSup {t | ∃ ξ v, β z ξ ≤ 1 ∧ nsq (h0 z) v ≤ 1 ∧
    t = Real.sqrt (nsq (h0 z) fun τ => (connMat h z ξ τ - connMat h0 z ξ τ) *ᵥ v τ)}

def curvNorm (h : Pt ι p q → ι → Matrix n n ℂ) (β : Pt ι p q → Pt ι p q → ℝ) (z : Pt ι p q) : ℝ :=
  sSup {t | ∃ ξ η v, β z ξ ≤ 1 ∧ β z η ≤ 1 ∧ nsq (h z) v ≤ 1 ∧
    t = Real.sqrt (nsq (h z) fun τ => curvMat h z ξ η τ *ᵥ v τ)}

end Calculus

section Boundary

variable {ι : Type} [Fintype ι] {p q : ℕ}

structure BdData (ι : Type) [Fintype ι] (p q : ℕ) (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)) where

  m : ℕ

  nrm : Fin m → Pt ι p q → ℝ
  nrm_pos : ∀ i, ∀ z ∈ DomI ι p q, 0 < nrm i z
  nrm_le : ∀ i, ∀ z ∈ DomI ι p q, nrm i z ≤ 1
  nrm_smooth : ∀ i, SmoothOn fun z => (nrm i z : ℂ)
  nrm_inv : ∀ i, ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, nrm i (moebI γ z) = nrm i z

  kae : Pt ι p q → Pt ι p q →ₗ[ℂ] Pt ι p q →ₗ⋆[ℂ] ℂ
  kae_herm : ∀ z ∈ DomI ι p q, ∀ ξ η, kae z η ξ = starRingEnd ℂ (kae z ξ η)
  kae_pos : ∀ z ∈ DomI ι p q, ∀ ξ, ξ ≠ 0 → 0 < (kae z ξ ξ).re
  kae_smooth : ∀ ξ η, SmoothOn fun z => kae z ξ η
  kae_inv : ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, ∀ ξ η,
    kae (moebI γ z) (fun τ => tanAct (γ τ) (z τ) (ξ τ)) (fun τ => tanAct (γ τ) (z τ) (η τ)) = kae z ξ η

  cst : ℝ
  cst_pos : 0 < cst
  cst_small : ∀ i, ∀ z ∈ DomI ι p q, ∀ ξ,
    2 * m * cst * |ddc (fun w => Real.exp 1 - Real.log (nrm i w ^ 2)) z ξ| ≤ Real.exp 1 * (kae z ξ ξ).re

  metW : Pt ι p q → ι → Matrix (Fin p) (Fin p) ℂ

  metOm : Pt ι p q → ι → Matrix (Fin q) (Fin q) ℂ
  metW_pos : ∀ z ∈ DomI ι p q, ∀ τ, (metW z τ).PosDef
  metOm_pos : ∀ z ∈ DomI ι p q, ∀ τ, (metOm z τ).PosDef
  metW_smooth : ∀ τ a b, SmoothOn fun z => metW z τ a b
  metOm_smooth : ∀ τ a b, SmoothOn fun z => metOm z τ a b
  metW_inv : ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, ∀ τ,
    (jW (γ τ) (z τ))ᴴ * metW (moebI γ z) τ * jW (γ τ) (z τ) = metW z τ
  metOm_inv : ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, ∀ τ,
    (kapQ (γ τ) (z τ))ᴴ * metOm (moebI γ z) τ * kapQ (γ τ) (z τ) = metOm z τ

def hodgeI (c : ι → ℝ) (z : Pt ι p q) (τ : ι) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := hodge (c τ) (z τ)

namespace BdData

variable {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (B : BdData ι p q Γ)

def ri (i : Fin B.m) (z : Pt ι p q) : ℝ := Real.exp 1 - Real.log (B.nrm i z ^ 2)

def r (z : Pt ι p q) : ℝ := Real.exp 1 - Real.log ((∏ i, B.nrm i z) ^ 2)

def beta (z ξ : Pt ι p q) : ℝ := (B.kae z ξ ξ).re - B.cst * ∑ i, ddc (fun w => Real.log (B.ri i w)) z ξ

def met (z : Pt ι p q) (τ : ι) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := blkMet (B.metW z τ) (B.metOm z τ)

theorem exp_le_r {z : Pt ι p q} (hz : z ∈ DomI ι p q) : Real.exp 1 ≤ B.r z := by
  unfold r
  have h0 : 0 ≤ ∏ i, B.nrm i z := Finset.prod_nonneg fun i _ => (B.nrm_pos i z hz).le
  have h1 : ∏ i, B.nrm i z ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (B.nrm_pos i z hz).le) fun i _ => B.nrm_le i z hz
  have h3 : Real.log ((∏ i, B.nrm i z) ^ 2) ≤ 0 := Real.log_nonpos (by positivity) (pow_le_one₀ h0 h1)
  linarith

theorem met_posDef {z : Pt ι p q} (hz : z ∈ DomI ι p q) (τ : ι) : (B.met z τ).PosDef := by
  unfold met
  exact blkMet_posDef (B.metW_pos z hz τ) (B.metOm_pos z hz τ)

end BdData

def detNorm (c : ι → ℝ) (s : ℂ) (z : Pt ι p q) (τ : ι) : ℝ := ‖s‖ * Real.sqrt (hodgeI c z τ).det.re

def onQuot {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (f : Pt ι p q → ℝ) (x : XCc ι p q Γ) : ℝ :=
  f (Quot.out x : DomI ι p q)

end Boundary

end GlobalTheory.HodgeDomain
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
section
noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure PreX (B : Pre) where
  piG : Fin 2 → 𝓞 B.host.E
  piG_K : ∀ i, (piG i : B.host.E) ∈ B.host.K
  piG_norm : ∀ i, (piG i : B.host.E) * B.host.conj (piG i : B.host.E) = (B.host.g i : B.host.E)
  piG_cong : ∀ i, ((B.host.QS * B.host.q * B.host.d : ℕ) : 𝓞 B.host.E) ∣ piG i - 1
  piT : B.Word → 𝓞 B.host.E
  piT_K : ∀ u, (piT u : B.host.E) ∈ B.host.K
  piT_norm : ∀ u, (piT u : B.host.E) * B.host.conj (piT u : B.host.E) = (B.T u : B.host.E)
  piT_cong : ∀ u, ((B.host.QS * B.host.q * B.host.d * (B.host.g 0 * B.host.g 1) ^ 2 : ℕ) : 𝓞 B.host.E) ∣ piT u - 1
  pde_split : (Ideal.primesOver (Ideal.span {(B.host.pde : ℤ)}) (𝓞 B.host.E)).ncard = Module.finrank ℚ B.host.E ∧
    (Ideal.primesOver (Ideal.span {(B.host.pde' : ℤ)}) (𝓞 B.host.E)).ncard = Module.finrank ℚ B.host.E
  ccK_top : B.host.ccK = ⊤
  e_even : ∀ j : Fin B.R.m, UpperTheory.MUQ (fun τ : Tau B.R => B.host.emb (τ : B.R.GG)) (fun τ => (B.hc τ).e j)

  hcW_inj : Function.Injective B.hcW

  a : ℝ
  g_big : ∀ i, 2 * B.R.f * B.R.k < B.host.g i - 1
  T_gt : ∀ u, 4 * a < (B.T u : ℝ)
  a_gt : ((2 * B.R.f * B.R.N B.R.m + 1 : ℕ) : ℝ) < 4 * a
  spread_le : ∀ u j, j ≤ B.R.m → ∀ τ, ((Formalism.BasicNotions.Examples₂.lamOf (B.hcW u τ) j).spread : ℝ) ≤ 2 * a

def Base.tauLL (B : Base) (τ : Tau B.R) : B.host.E →+* B.LL :=
  B.embE.comp (B.host.sigmaOf (τ : B.R.GG) : B.host.E →+* B.host.E)

end GlobalTheory.Mem

end
end

