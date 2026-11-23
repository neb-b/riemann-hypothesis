module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Formalism.HarderNarasimhan.ShiftInvariance

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutoffComputesBesselQuotientIntegral
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.CutQuot

section Abstract

variable {X : Type*} [MeasurableSpace X] {T : X → X → X} {G R : Set X} {μG μR ν : Measure X}

theorem null_of_stable (hR : ∀ᵐ s ∂μR, s ∈ R) (h0 : μR ≠ 0)
    (hW : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (T s x) ∂μR) ∂ν)
    {B : Set X} (hB : MeasurableSet B) (hst : ∀ s ∈ R, ∀ x ∈ B, T s x ∈ B) (hn : μG B = 0) : ν B = 0 := by
  have h1 := hW (B.indicator 1) (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB, hn] at h1
  have h2 : ∫⁻ x, B.indicator (fun _ => μR Set.univ) x ∂ν ≤
      ∫⁻ x, (∫⁻ s, B.indicator (1 : X → ℝ≥0∞) (T s x) ∂μR) ∂ν := by
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, ← lintegral_one]
      refine le_of_eq (lintegral_congr_ae ?_)
      filter_upwards [hR] with s hs
      rw [Set.indicator_of_mem (hst s hs x hx)]; rfl
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  rw [← h1, lintegral_indicator_const hB, nonpos_iff_eq_zero, mul_eq_zero] at h2
  exact h2.resolve_left (by simpa using h0)

theorem exists_cut [SigmaFinite μG] [SFinite μR] (hT : Measurable (Function.uncurry T))
    (hR : ∀ᵐ s ∂μR, s ∈ R) (h0 : μR ≠ 0)
    (hW : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (T s x) ∂μR) ∂ν)
    (hG : ∀ᵐ x ∂ν, x ∈ G)
    (hinv : ∀ ρ ∈ R, ∀ x, ∀ f : X → ℝ≥0∞, Measurable f →
      ∫⁻ s, f (T s (T ρ x)) ∂μR = ∫⁻ s, f (T s x) ∂μR) :
    ∃ φ : X → ℝ≥0∞, Measurable φ ∧ (∀ x, ∫⁻ ρ, φ (T ρ x) ∂μR ≤ 1) ∧
      ∀ F : X → ℝ≥0∞, Measurable F → (∀ ρ ∈ R, ∀ x ∈ G, F (T ρ x) = F x) →
        ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  obtain ⟨g, hg0, hgm, hgi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  set ψ : X → ℝ≥0∞ := fun x => (g x : ℝ≥0∞) with hψ
  have hψm : Measurable ψ := hgm.coe_nnreal_ennreal
  have hTx : ∀ x, Measurable fun s => T s x := fun x => hT.comp (measurable_id.prodMk measurable_const)
  set I : X → ℝ≥0∞ := fun x => ∫⁻ s, ψ (T s x) ∂μR with hI
  have hIm : Measurable I := Measurable.lintegral_prod_left (f := fun s x => ψ (T s x)) (hψm.comp hT)
  have hI0 : ∀ x, I x ≠ 0 := by
    intro x hx
    have h := (lintegral_eq_zero_iff (hψm.comp (hTx x))).1 hx
    apply h0
    rw [← ae_eq_bot, ← Filter.eventually_false_iff_eq_bot]
    filter_upwards [h] with s hs
    have := hg0 (T s x)
    simp [hψ] at hs
    exact this.ne' hs
  have hIfin : ∀ᵐ x ∂ν, I x < ∞ := by
    refine ae_lt_top hIm ?_
    rw [← hW ψ hψm]
    exact (hgi.trans ENNReal.one_lt_top).ne
  have key : ∀ x, ∫⁻ ρ, ψ (T ρ x) * (I (T ρ x))⁻¹ ∂μR = I x * (I x)⁻¹ := by
    intro x
    rw [show I x * (I x)⁻¹ = ∫⁻ ρ, ψ (T ρ x) * (I x)⁻¹ ∂μR from
      (lintegral_mul_const (I x)⁻¹ (f := fun s => ψ (T s x)) (hψm.comp (hTx x))).symm]
    refine lintegral_congr_ae ?_
    filter_upwards [hR] with s hs
    have : I (T s x) = I x := hinv s hs x ψ hψm
    rw [this]
  have hφm : Measurable fun x => ψ x * (I x)⁻¹ := hψm.mul hIm.inv
  refine ⟨fun x => ψ x * (I x)⁻¹, hφm, fun x => ?_, fun F hF hFi => ?_⟩
  · rw [key]; exact ENNReal.mul_inv_le_one _
  · show _ = ∫⁻ x, ψ x * (I x)⁻¹ * F x ∂μG
    rw [hW (fun x => ψ x * (I x)⁻¹ * F x) (hφm.mul hF)]
    refine lintegral_congr_ae ?_
    filter_upwards [hG, hIfin] with x hx hx'
    have h1 : ∫⁻ s, ψ (T s x) * (I (T s x))⁻¹ * F (T s x) ∂μR =
        ∫⁻ s, ψ (T s x) * (I (T s x))⁻¹ * F x ∂μR := by
      refine lintegral_congr_ae ?_
      filter_upwards [hR] with s hs
      rw [hFi s hs x hx]
    rw [h1, lintegral_mul_const (F x) (f := fun s => ψ (T s x) * (I (T s x))⁻¹) (hφm.comp (hTx x)), key,
      ENNReal.mul_inv_cancel (hI0 x) hx'.ne, one_mul]

end Abstract

theorem mul_mem_iff {k r : ℕ} {s : Mat k r} (hs : s ∈ GG k r) (x : Mat k r) :
    s * x ∈ GG k r ↔ x ∈ GG k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  have : (s * x)ᴴ * Hpk k r * (s * x) = xᴴ * Hpk k r * x := by
    rw [conjTranspose_mul]
    conv_rhs => rw [← hs']
    simp only [Matrix.mul_assoc]
  show (s * x)ᴴ * Hpk k r * (s * x) = Hpk k r ↔ xᴴ * Hpk k r * x = Hpk k r
  rw [this]

theorem measurable_G (k r : ℕ) : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  refine IsClosed.measurableSet ?_
  have h : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  exact isClosed_eq (f := fun x : Mt k r => (Matrix.of x : Mat k r)ᴴ * Hpk k r * Matrix.of x)
    ((h.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h) continuous_const

theorem continuous_act (k r : ℕ) :
    Continuous (Function.uncurry fun s x : Mt k r => lmulM (Matrix.of s) x) := by
  have h : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  exact (h.comp continuous_fst).matrix_mul (h.comp continuous_snd)

theorem cut_quotient : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → ν {x | Matrix.of x ∉ GG k r} = 0 ∧ (∀ A : Set (Mt k r), MeasurableSet A → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → (lmulM ρ x ∈ A ↔ x ∈ A)) → μG A = 0 → ν A = 0) ∧ ∃ φ, SubCut (GG k r) μR φ ∧ ∀ F : Mt k r → ℝ≥0∞, Measurable F → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → F (lmulM ρ x) = F x) → ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  intro k r R μG μR ν hR hG hμ hU hW
  haveI := hG.1
  haveI := hμ.1
  set T : Mt k r → Mt k r → Mt k r := fun s x => lmulM (Matrix.of s) x with hT
  have hTm : Measurable (Function.uncurry T) := (continuous_act k r).measurable
  have hae : ∀ᵐ s ∂μR, s ∈ {x : Mt k r | Matrix.of x ∈ R} := hμ.2.2.1
  have hW' : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (T s x) ∂μR) ∂ν := hW
  have hmem : ∀ s : Mt k r, Matrix.of s ∈ R → ∀ x : Mt k r,
      (Matrix.of (T s x) ∈ GG k r ↔ Matrix.of x ∈ GG k r) := fun s hs x =>
    mul_mem_iff (hR.1 hs) (Matrix.of x)
  have h1 : ν {x | Matrix.of x ∉ GG k r} = 0 :=
    null_of_stable hae hμ.2.1 hW' (measurable_G k r).compl
      (fun s hs x hx h => hx ((hmem s hs x).1 h)) hG.2.2.1
  have h1' : ∀ᵐ x ∂ν, x ∈ {x : Mt k r | Matrix.of x ∈ GG k r} := h1
  refine ⟨h1, fun A hA hst hn => ?_, ?_⟩
  · have h2 : ν (A ∩ {x : Mt k r | Matrix.of x ∈ GG k r}) = 0 :=
      null_of_stable hae hμ.2.1 hW' (hA.inter (measurable_G k r))
        (fun s hs x hx => ⟨(hst _ hs x hx.2).2 hx.1, (hmem s hs x).2 hx.2⟩)
        (measure_mono_null Set.inter_subset_left hn)
    refine measure_mono_null (fun x hx => ?_) (measure_union_null h2 h1)
    by_cases h : Matrix.of x ∈ GG k r
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  · obtain ⟨φ, hφ, hle, hF⟩ := exists_cut hTm hae hμ.2.1 hW' h1' (by
      intro ρ hρ x f hf
      have hTx : Measurable fun s => T s x := hTm.comp (measurable_id.prodMk measurable_const)
      have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
      have hr : Measurable (rmulM (k := k) (r := r) (Matrix.of ρ)) :=
        by
        have hc' : Continuous (rmulM (k := k) (r := r) (Matrix.of ρ)) := hc.matrix_mul continuous_const
        exact hc'.measurable
      conv_rhs => rw [← hU.1 (Matrix.of ρ) hρ]
      rw [lintegral_map (f := fun s => f (T s x)) (hf.comp hTx) hr]
      refine lintegral_congr fun s => congrArg f ?_
      exact (Matrix.mul_assoc (Matrix.of s) (Matrix.of ρ) (Matrix.of x)).symm)
    exact ⟨φ, ⟨hφ, fun x _ => hle x⟩, fun F hFm hFi => hF F hFm fun ρ hρ x hx => hFi _ hρ x hx⟩

end GlobalTheory.Amp.CutQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DFactsHolds
section
open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Count.Cartan

noncomputable section

namespace GlobalTheory.Dec

theorem dOp_fin_zero (g : Matrix (Fin 0) (Fin 0) ℂ) : dOp g = 0 := by

  rw [Subsingleton.elim g 0]
  simp [GlobalTheory.Count.dOp]

private theorem isHermitian_of_inP {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Formalism.REAL.inP ε X) : X.IsHermitian := by
  have hX' : Formalism.REAL.inG ε X ∧ X * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := hX
  have hG : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX'.1
  have h1 : Xᴴ * Formalism.REAL.Jm ε = X * Formalism.REAL.Jm ε := by
    rw [hX'.2]
    exact eq_neg_of_add_eq_zero_left hG
  have h2 := congrArg (· * Formalism.REAL.Jm ε) h1
  simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one] at h2
  exact h2

private theorem isUnit_of_inUJ_flag_measures' {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) : IsUnit g := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have h : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Formalism.REAL.Jm_mul_self]
  exact (Matrix.isUnit_iff_isUnit_det g).mpr (Matrix.isUnit_det_of_left_inverse h)

private theorem dOp_one' {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) :
    dOp (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  have hP : Formalism.REAL.inP ε 0 := by simp [Formalism.REAL.inP, Formalism.REAL.inG]
  obtain ⟨h0, h1, -⟩ := GlobalTheory.Count.Cartan.dOp_bounds hn (Matrix.unitaryGroup (Fin n) ℂ).one_mem hP
  have hs0 : Formalism.REAL.hs (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [Formalism.REAL.hs]
  simp only [NormedSpace.exp_zero, Matrix.mul_one] at h0 h1
  rw [hs0, Real.sqrt_zero] at h1
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hle : dOp (1 : Matrix (Fin n) (Fin n) ℂ) ≤ 0 := by
    by_contra h
    have := mul_pos hs2 (lt_of_not_ge h)
    linarith
  exact le_antisymm hle h0

theorem dFacts_holds : DFacts := by
  intro n ε
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    refine ⟨fun g _ => ⟨by rw [dOp_fin_zero], by rw [dOp_fin_zero, dOp_fin_zero],
      fun g' _ => by rw [dOp_fin_zero, dOp_fin_zero, dOp_fin_zero, add_zero],
      fun k₁ _ k₂ _ => by rw [dOp_fin_zero, dOp_fin_zero]⟩,
      GlobalTheory.Count.Cartan.continuousOn_dOp ε, fun k hk X hX => ⟨?_, ?_, ?_⟩⟩
    · exact GlobalTheory.Count.Cartan.dHS_polar hk.1 (isHermitian_of_inP hX)
    · rw [dOp_fin_zero, mul_zero]
      exact Real.sqrt_nonneg _
    · rw [dOp_fin_zero, mul_zero]
      simp [Formalism.REAL.hs]
  · refine ⟨fun g hg => ?_, GlobalTheory.Count.Cartan.continuousOn_dOp ε, fun k hk X hX => ?_⟩
    · have hgU : Formalism.REAL.inUJ ε g := hg
      have hu := isUnit_of_inUJ_flag_measures' hgU
      refine ⟨?_, GlobalTheory.Count.Cartan.dOp_inv hgU,
        fun g' hg' => GlobalTheory.Count.Cartan.dOp_mul_le hn hu (isUnit_of_inUJ_flag_measures' hg'),
        fun k₁ hk₁ k₂ hk₂ => GlobalTheory.Count.Cartan.dOp_unitary hk₁.1 hk₂.1 g⟩

      have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hu
      have hinv : IsUnit g⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hu
      have h := GlobalTheory.Count.Cartan.dOp_mul_le hn hu hinv
      rw [Matrix.mul_nonsing_inv g hdet, dOp_one' hn ε, GlobalTheory.Count.Cartan.dOp_inv hgU] at h
      linarith
    · obtain ⟨-, h1, h2⟩ := GlobalTheory.Count.Cartan.dOp_bounds hn hk.1 hX
      exact ⟨GlobalTheory.Count.Cartan.dHS_polar hk.1 (isHermitian_of_inP hX), h1, h2⟩

end GlobalTheory.Dec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerTail
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.DerTail

theorem tri_add (a b : ℕ) : (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + b * (b - 1) / 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, Nat.triangle_succ, Nat.triangle_succ, ih]
    ring

variable {g : ℕ} [Fact g.Prime]

theorem entN_tl (m : ℕ) {n : ℕ} (M : Mt g n) {a b : ℕ} (ha : a < m) (hb : b < m) :
    entN (tl m M) a b = entN M a b := by
  rw [entN, dite_eq_left ⟨ha, hb⟩]; rfl

theorem entN_fin {n : ℕ} (M : Mt g n) (a b : Fin n) : entN M a b = M a b := by
  rw [entN, dite_eq_left ⟨a.2, b.2⟩]

theorem inR_iff (i : ℕ) {n : ℕ} (M : Mt g n) :
    InR i M ↔ ∀ a : ℕ, i ≤ a → a < n → (∀ b, b < a → entN M a b = 0) ∧ entN M a a = 1 := by
  constructor
  · rintro ⟨h1, h2⟩ a hia han
    refine ⟨fun b hb => ?_, ?_⟩
    · by_cases hbi : b < i
      · have := h1 ⟨a, han⟩ ⟨b, by omega⟩ hbi hia
        exact (entN_fin M ⟨a, han⟩ ⟨b, by omega⟩).trans this
      · have := (h2 ⟨a - i, by omega⟩ ⟨b - i, by omega⟩).1 (by simp only [Fin.mk_lt_mk]; omega)
        simp only [br] at this
        rwa [show i + (a - i) = a by omega, show i + (b - i) = b by omega] at this
    · have := (h2 ⟨a - i, by omega⟩ ⟨a - i, by omega⟩).2 rfl
      simp only [br] at this
      rwa [show i + (a - i) = a by omega] at this
  · intro h
    refine ⟨fun a b hb ha => ?_, fun a b => ⟨fun hab => ?_, fun hab => ?_⟩⟩
    · exact (entN_fin M a b).symm.trans ((h a ha a.2).1 b (by omega))
    · have := a.2
      have hab' : (b : ℕ) < a := hab
      exact (h (i + a) (by omega) (by omega)).1 (i + b) (by omega)
    · subst hab
      have := a.2
      exact (h (i + a) (by omega) (by omega)).2

theorem inR_split {i m n : ℕ} (him : i ≤ m) (hmn : m ≤ n) (M : Mt g n) :
    InR i M ↔ InR m M ∧ InR i (tl m M) := by
  simp only [inR_iff]
  constructor
  · intro h
    refine ⟨fun a ha han => h a (by omega) han, fun a ha ham => ⟨fun b hb => ?_, ?_⟩⟩
    · rw [entN_tl m M ham (by omega)]
      exact (h a ha (by omega)).1 b hb
    · rw [entN_tl m M ham ham]
      exact (h a ha (by omega)).2
  · rintro ⟨h1, h2⟩ a ha han
    by_cases ham : a < m
    · refine ⟨fun b hb => ?_, ?_⟩
      · rw [← entN_tl m M ham (by omega)]
        exact (h2 a ha ham).1 b hb
      · rw [← entN_tl m M ham ham]
        exact (h2 a ha ham).2
    · exact h1 a (by omega) han

theorem tl_tl {i m n : ℕ} (him : i ≤ m) (M : Mt g n) : tl i (tl m M) = tl i M := by
  funext a b
  have := a.2
  have := b.2
  exact entN_tl m M (by omega) (by omega)

theorem supFrom_split {i m n : ℕ} (him : i < m) (hmn : m ≤ n) (M : Mt g n) :
    supFrom i M = supFrom (m - 1) M + supFrom i (tl m M) := by
  unfold supFrom
  rw [add_comm, ← Finset.sum_Ico_consecutive _ (show i ≤ m - 1 by omega) (show m - 1 ≤ n - 1 by omega)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  exact (entN_tl m M (by omega) (by omega)).symm

theorem der_tail : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i m n : ℕ) (F : Gn g n → ℂ),
    i < m → m ≤ n → der ψ i (tail ψ m F) = der ψ i F := by
  intro g _ ψ i m n F him hmn
  funext h
  rw [_root_.GlobalTheory.GLm.der_eq_sum g ψ i m _ h him.le, _root_.GlobalTheory.GLm.der_eq_sum g ψ i n _ h (by omega)]
  have he : i * (n - i) + (n - i) * (n - i - 1) / 2 =
      (i * (m - i) + (m - i) * (m - i - 1) / 2) + (m * (n - m) + (n - m) * (n - m - 1) / 2) := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le him.le
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [show i + a + b - i = a + b by omega, show i + a - i = a by omega, show i + a + b - (i + a) = b by omega,
      tri_add]
    ring
  rw [he, pow_add _ _ (m * (n - m) + (n - m) * (n - m - 1) / 2), mul_inv _ ((g : ℂ) ^ (m * (n - m) + (n - m) * (n - m - 1) / 2)),
    mul_assoc]
  congr 1
  unfold tail
  set c : ℂ := ((g : ℂ) ^ (m * (n - m) + (n - m) * (n - m - 1) / 2))⁻¹
  have h1 : ∀ p : Gn g m, (if InR i (p : Mt g m) ∧ tl i (p : Mt g m) = (h : Mt g i) then
      (c * ∑ x : Gn g n, if InR m (x : Mt g n) ∧ tl m (x : Mt g n) = (p : Mt g m) then
        F x * (ψ (supFrom (m - 1) (x : Mt g n)))⁻¹ else 0) * (ψ (supFrom i (p : Mt g m)))⁻¹ else 0) =
      c * ∑ x : Gn g n, if tl m (x : Mt g n) = (p : Mt g m) then
        (if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then
          F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0) else 0 := by
    intro p
    split_ifs with hp
    · rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : tl m (x : Mt g n) = (p : Mt g m)
      · rw [if_pos hx]
        rw [← hx] at hp
        rw [tl_tl him.le] at hp
        rw [inR_split him.le hmn (x : Mt g n), supFrom_split him hmn (x : Mt g n), AddChar.map_add_eq_mul, mul_inv,
          ← hx]
        by_cases hR : InR m (x : Mt g n)
        · rw [if_pos ⟨hR, rfl⟩, if_pos ⟨⟨hR, hp.1⟩, hp.2⟩, mul_assoc]
        · rw [if_neg (fun hh => hR hh.1), if_neg (fun hh => hR hh.1.1), zero_mul]
      · rw [if_neg hx, if_neg (fun hh => hx hh.2), zero_mul]
    · symm
      apply mul_eq_zero_of_right
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : tl m (x : Mt g n) = (p : Mt g m)
      · rw [if_pos hx, if_neg]
        rintro ⟨ha, hb⟩
        apply hp
        rw [← hx, tl_tl him.le]
        exact ⟨((inR_split him.le hmn _).1 ha).2, hb⟩
      · rw [if_neg hx]
  rw [Finset.sum_congr rfl fun p _ => h1 p, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i)
  · have hu : IsUnit (tl m (x : Mt g n)) :=
      ((_root_.GlobalTheory.GLm.ParBasic.par_basic g m (n - m) n (by omega)).2.2.1 x ((inR_split him.le hmn _).1 hx.1).1.1).1
    obtain ⟨p, hp⟩ := hu
    rw [Finset.sum_eq_single p]
    · rw [if_pos hp.symm]
    · intro q _ hq
      rw [if_neg]
      intro hh
      exact hq (Units.ext (hp.trans hh).symm)
    · intro hh
      exact absurd (Finset.mem_univ p) hh
  · simp [hx]

end GlobalTheory.GLm.DerTail
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKStableOfMemLowKSub
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory

theorem exists_kStable_of_mem_lowKSub (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (hw : w ∈ lowKSub ε lam σ) :
    ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ IsKStableOn ε σ S ∧ w ∈ S := by
  classical
  obtain ⟨s, hs, hws⟩ := Submodule.mem_sSup_iff_exists_finset.1 hw
  refine ⟨⨆ i ∈ s, i, ?_, ?_, hws⟩
  · have hfg : (⨆ i ∈ s, i).FG := by
      refine Submodule.fg_biSup s (fun i => i) (fun i hi => ?_)
      obtain ⟨hfin, -⟩ := hs hi
      exact (Submodule.fg_iff_finiteDimensional i).2 hfin
    exact (Submodule.fg_iff_finiteDimensional _).1 hfg
  · intro g hg v hv
    have hle : (⨆ i ∈ s, i) ≤ (⨆ i ∈ s, i).comap ((σ g : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      refine iSup₂_le fun i hi => ?_
      obtain ⟨-, hstab, -⟩ := hs hi
      intro x hx
      exact (le_iSup₂ (f := fun j (_ : j ∈ s) => j) i hi) (hstab g hg x hx)
    exact hle hv

theorem isKFin_of_mem_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H), w ∈ lowKSub ε lam σ → IsKFin ε σ w := by
  intro n ε lam H _ _ σ w hw
  obtain ⟨S, hfin, hstab, hwS⟩ := exists_kStable_of_mem_lowKSub n ε lam H σ w hw
  exact ⟨S, hfin, hwS, hstab⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasisReTraceMulConjTranspose
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

noncomputable def matrixEntriesEuclideanReal (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] PiLp 2 (fun _ : Fin n × Fin n => ℂ) where
  toFun X := WithLp.toLp 2 (fun p => X p.1 p.2)
  invFun v := Matrix.of fun i j => v.ofLp (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem inner_matrixEntriesEuclideanReal (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    inner ℝ (matrixEntriesEuclideanReal n Y) (matrixEntriesEuclideanReal n X)
      = ((X * Yᴴ).trace).re := by
  change inner ℝ (WithLp.toLp 2 (fun p : Fin n × Fin n => Y p.1 p.2))
      (WithLp.toLp 2 (fun p : Fin n × Fin n => X p.1 p.2)) = _
  rw [PiLp.inner_apply]
  simp only [WithLp.ofLp_toLp, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.inner, mul_comm]

theorem exists_orthonormal_basis_re_trace_mul_conjTranspose (n : ℕ)
    (U : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ),
      (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ LinearIndependent ℝ E ∧
        U = Submodule.span ℝ (Set.range E) := by
  classical
  set e := matrixEntriesEuclideanReal n
  set V : Submodule ℝ (PiLp 2 (fun _ : Fin n × Fin n => ℂ)) := U.map e.toLinearMap
  let b := stdOrthonormalBasis ℝ V
  refine ⟨Module.finrank ℝ V, fun i => e.symm (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ)), ?_, ?_, ?_⟩
  · intro i k
    have h := inner_matrixEntriesEuclideanReal n (e.symm (b i)) (e.symm (b k))
    simp only [e, LinearEquiv.apply_symm_apply] at h
    rw [← h, ← Submodule.coe_inner, orthonormal_iff_ite.mp b.orthonormal k i]
    by_cases hik : i = k
    · subst hik; simp
    · simp [hik, Ne.symm hik]
  · have hb : LinearIndependent ℝ (fun i => (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ))) :=
      b.orthonormal.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
    exact hb.map' e.symm.toLinearMap e.symm.ker
  · symm
    have hrange : Set.range (fun i => e.symm (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ)))
        = e.symm.toLinearMap '' (V.subtype '' Set.range b) := by
      ext x; simp [Set.mem_image, Set.mem_range]
    have hspan : Submodule.span ℝ (Set.range b) = ⊤ := by
      simpa [OrthonormalBasis.coe_toBasis] using b.toBasis.span_eq
    rw [hrange, Submodule.span_image, Submodule.span_image, hspan, Submodule.map_subtype_top]
    ext x
    simp [V]

end GlobalTheory
end

