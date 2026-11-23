module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

def Zr (k r : ℕ) (g : Mat k r) : Matrix (Fin r) (Fin r) ℂ := fun a b => g (esI k r a) (eI k r b)

def BlockAnti {r : ℕ} (β : Fin r → ℕ) (Z : Matrix (Fin r) (Fin r) ℂ) : Prop :=
  Monotone β ∧ Z.det ≠ 0 ∧ (∀ a b, Z a b ≠ 0 → β a = β b) ∧
    ∀ a b a' b', Z a b ≠ 0 → Z a' b' ≠ 0 → β a = β a' → ‖Z a b‖ = ‖Z a' b'‖ ∧ (a = a' → b = b') ∧ (a < a' → b' < b)

def IsNormal (k r : ℕ) (β : Fin r → ℕ) (g : Mat k r) : Prop :=
  g ∈ GG k r ∧ (∀ a : Fin r, g⁻¹ *ᵥ bvec (eI k r a) ∈ Xst k r ∧ g *ᵥ bvec (eI k r a) ∈ Xst k r) ∧ BlockAnti β (Zr k r g)

def lebR (k r : ℕ) (β : Fin r → ℕ) : Measure (Mt k r) :=
  (volume : Measure (UTin β → ℂ)).map fun x => Matrix.of.symm (uEmb k r (upperIn β x))

def NormR (k r : ℕ) (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)) : Prop :=
  ∃ n₁ ∈ Nset k r, ∃ n₂ ∈ Nset k r, ∃ (g₀ : Mat k r) (β : Fin r → ℕ), IsNormal k r β g₀ ∧ γ = n₁ * g₀ * n₂ ∧
    μR = (ENNReal.ofReal s • lebR k r β).map (conjM n₂⁻¹)

def muProd {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) :=
  (μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2

def OneSide {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (ψ : Mat k r → ℂ) (μG μW μN νS : Measure (Mt k r))
    (Φ : Mat k r → Wp) (c : ℝ) : Prop :=
  inWb k r z ∧ 0 < Tz k r z ∧ Nontrivial Wp ∧ IsURepOn (UWset k r z) π ∧ IsIrredOn (UWset k r z) π ∧
    IsHaarOn (GG k r) μG ∧ IsHaarOn (UWset k r z) μW ∧ μW Set.univ = 1 ∧ IsHaarOn (Nset k r) μN ∧
    IsQuotMeas μG (muProd μW μN) νS ∧ (∀ n ∈ Nset k r, ‖ψ n‖ = 1) ∧ IsSPsiEquiv z ψ π Φ ∧ ContinuousOn Φ (GG k r) ∧
    0 < c ∧ l2SG νS Φ = ENNReal.ofReal (c * Module.finrank ℂ Wp)

def MomBd {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] (z : Fin (2 * r + k + 1) → ℂ) (νS : Measure (Mt k r))
    (Φ : Mat k r → Wp) (q : ℕ) (H₁ : ℝ) : Prop :=
  ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal (lA k r z (Matrix.of x) a ^ (2 * q)) * (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤
    ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ

def absBd (k r : ℕ) (H₁ De D : ℝ) : ℝ :=
  (4 * r : ℝ) ^ (44 * r ^ 3) * H₁ ^ (24 * r ^ 3) * De ^ (14 * r ^ 2) *
    (8 * Real.pi * Real.exp 1 / k) ^ (r * (k - 2 - r)) * (D ^ (k - 2 - r))⁻¹

end GlobalTheory.Amp
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CmHalfIntegralGeneratorMemAlgebraicClosure
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Model

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.Amp.Model.det_upper {r : ℕ} (x : _root_.GlobalTheory.Amp.UT r → ℂ) :
    (_root_.GlobalTheory.Amp.upper x).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_eq_one fun i _ => by simp [_root_.GlobalTheory.Amp.upper]
  · intro i j hij
    simp only [id] at hij
    have h1 : ¬ i < j := not_lt.mpr hij.le
    simp [_root_.GlobalTheory.Amp.upper, h1, hij.ne']

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.Amp.Model.cont_uEmb (k r : ℕ) :
    Continuous fun x : _root_.GlobalTheory.Amp.UT r → ℂ =>
      _root_.GlobalTheory.Amp.uEmb k r (_root_.GlobalTheory.Amp.upper x) := by
  have hup : Continuous fun x : _root_.GlobalTheory.Amp.UT r → ℂ =>
      _root_.GlobalTheory.Amp.upper x := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    unfold _root_.GlobalTheory.Amp.upper
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
    · exact continuous_const
  have hinv : ∀ x : _root_.GlobalTheory.Amp.UT r → ℂ,
      (_root_.GlobalTheory.Amp.upper x)⁻¹ = (_root_.GlobalTheory.Amp.upper x).adjugate := by
    intro x; rw [Matrix.inv_def, _root_.GlobalTheory.Amp.Model.det_upper]; simp
  have hc : Continuous fun x : _root_.GlobalTheory.Amp.UT r → ℂ =>
      (_root_.GlobalTheory.Amp.upper x)⁻¹ := by
    simp_rw [hinv]; exact hup.matrix_adjugate
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold _root_.GlobalTheory.Amp.uEmb
  split_ifs
  · exact (continuous_apply_apply _ _).comp hup
  · exact ((continuous_apply_apply _ _).comp hc).star
  · exact continuous_const
  · exact continuous_const

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.Amp.Model.cont_pOf (k r : ℕ) :
    Continuous (_root_.GlobalTheory.Amp.pOf k r) := by
  have herm : ∀ {f g : _root_.GlobalTheory.Amp.PPar k r → Fin (k + 1) → ℂ},
      Continuous f → Continuous g → Continuous fun q => _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hb k) (f q) (g q) :=
    fun hf hg => (_root_.Formalism.FourierDecayAlt.P.B2x5.continuous_herm (_root_.Formalism.QuantumDeterminants.Hb k)).comp (hf.prodMk hg)
  have hB : ∀ a, Continuous fun q : _root_.GlobalTheory.Amp.PPar k r => q.1 a :=
    fun a => (continuous_apply a).comp continuous_fst
  have hS : ∀ a b, Continuous fun q : _root_.GlobalTheory.Amp.PPar k r =>
      _root_.GlobalTheory.Amp.skewM q.2.1 q.2.2 a b := by
    intro a b
    unfold _root_.GlobalTheory.Amp.skewM
    split_ifs
    · exact (continuous_apply _).comp (continuous_fst.comp continuous_snd)
    · exact ((continuous_apply _).comp (continuous_fst.comp continuous_snd)).star.neg
    · exact (Complex.continuous_ofReal.comp
        ((continuous_apply _).comp (continuous_snd.comp continuous_snd))).mul continuous_const
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold _root_.GlobalTheory.Amp.pOf _root_.GlobalTheory.Amp.pEl
  split_ifs
  · exact continuous_const
  · exact (herm continuous_const (hB _)).neg
  · exact (continuous_apply _).comp (hB _)
  · exact (hS _ _).sub ((herm (hB _) (hB _)).div_const _)
  · exact continuous_const

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.Amp.Model.cont_lebN_map (k r : ℕ) :
    Continuous fun q : (_root_.GlobalTheory.Amp.UT r → ℂ) × _root_.GlobalTheory.Amp.PPar k r =>
      (Matrix.of.symm (_root_.GlobalTheory.Amp.uEmb k r (_root_.GlobalTheory.Amp.upper q.1) *
        _root_.GlobalTheory.Amp.pOf k r q.2) : _root_.Formalism.QuantumDeterminants.Mt k r) := by
  exact ((_root_.GlobalTheory.Amp.Model.cont_uEmb k r).comp continuous_fst).matrix_mul
    ((_root_.GlobalTheory.Amp.Model.cont_pOf k r).comp continuous_snd)

end GlobalTheory.Amp.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
section
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas

open Formalism.MainNotions.S GlobalTheory.Count

def flagAt (I : AutInst) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (v : InfinitePlace I.F) :
    Fin (a + 1) → Submodule ℂ (Fin I.n → ℂ) :=
  fun i => Submodule.span ℂ ((fun y : Fin I.n → I.E => (I.P v)⁻¹ *ᵥ fun l => I.φ v (y l)) '' (S i : Set _))

def IsSatFlag (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) {a : ℕ} (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  S 0 = ⊥ ∧ Monotone S ∧ (∀ i : Fin a, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i) ∧
    (∀ i, ∀ y, y ∈ S i ↔ y ∈ Λ ∧ y ∈ Submodule.span I.E (S i : Set (Fin I.n → I.E))) ∧
    ∀ x ∈ S (Fin.last a), ∀ y ∈ S (Fin.last a), Formalism.UG.hform (starRingEnd I.E) I.J x y = 0

def IsGaugeAll (I : AutInst) (c : InfinitePlace I.F → ℝ) : Prop := ∀ v, IsGauge (I.ε v) (c v)

def cIw (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : ℝ :=
  (2 : ℝ) ^ (-((dimN (p + q) j : ℝ) / 2)) * (volU p * volU q) /
    ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) * volU (p - ∑ i, j i) * volU (q - ∑ i, j i))

def rankFac (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ) : ℝ :=
  (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ((M : ℝ) - 1 / 2)) * Formalism.HermitianLatticesTheory.lValEta E M

end GlobalTheory.FlagMeas
end
end

