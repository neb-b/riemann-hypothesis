module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieEntriesUnipotentBesselNCharacterization
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeField
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOrbitOpNormIntegralFiniteOnCompactRegular
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.OrbNorm

theorem continuous_opn {n : ℕ} : Continuous (opn : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold opn
  have h : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) g) :=
    LinearMap.continuous_of_finiteDimensional
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toLinearMap)
  exact continuous_norm.comp h

theorem opn_pos {k r : ℕ} {g : Mat k r} (hg : g ∈ GG k r) : 0 < opn g := by
  rcases (opn_nonneg g).lt_or_eq with h | h
  · exact h
  exfalso
  have h0 : g = 0 := by
    have h1 : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 * r + k + 1)) g = 0 := by
      rw [← norm_eq_zero]; exact h.symm
    simpa using h1
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [h0] at hg'
  have hH : Hpk k r = 0 := by simpa using hg'.symm
  have hr : r < 2 * r + k + 1 := by omega
  have hent : Hpk k r ⟨r, hr⟩ ⟨r, hr⟩ = 0 := by rw [hH]; rfl
  simp only [Hpk] at hent
  split_ifs at hent
  all_goals first
    | exact absurd ⟨le_refl r, Nat.le_add_right r k, trivial⟩ ‹¬(r ≤ r ∧ r ≤ r + k ∧ True)›
    | norm_num at hent

theorem integrable_of_normInt {k r : ℕ} {μ : Measure (Mt k r)} {A : ℝ} (h : normInt μ A < ⊤) :
    Integrable (fun x : Mt k r => opn (Matrix.of x) ^ (-A)) μ := by
  have hm : Measurable (fun x : Mt k r => opn (Matrix.of x) ^ (-A)) :=
    ((continuous_opn.comp (continuous_id : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)))).measurable).pow_const _
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (opn_nonneg _) _)]
  exact h

theorem rpow_le {a a' x C0 A : ℝ} {M : ℕ} (ha : 0 < a) (ha' : 0 < a') (hx : 0 ≤ x) (hC : 0 < C0)
    (hA : 0 ≤ A) (h : max a a' ≤ C0 * x ^ M) :
    x ^ (-(2 * M * A)) ≤ C0 ^ (2 * A) * (a ^ (-A) * a' ^ (-A)) := by
  have hy : 0 < x ^ M := by
    have h1 : 0 < max a a' := lt_max_of_lt_left ha
    exact pos_of_mul_pos_right (lt_of_lt_of_le h1 h) hC.le
  have hCy : 0 < C0 * x ^ M := mul_pos hC hy
  have hx' : x ^ (-(2 * M * A)) = (x ^ M) ^ (-(2 * A)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    congr 1
    ring
  have h1 : (C0 * x ^ M) ^ (-A) ≤ a ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos ha (le_trans (le_max_left _ _) h) (by linarith)
  have h2 : (C0 * x ^ M) ^ (-A) ≤ a' ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos ha' (le_trans (le_max_right _ _) h) (by linarith)
  have key : C0 ^ (2 * A) * ((C0 * x ^ M) ^ (-A) * (C0 * x ^ M) ^ (-A)) = (x ^ M) ^ (-(2 * A)) := by
    rw [← Real.rpow_add hCy, Real.mul_rpow hC.le hy.le, ← mul_assoc, ← Real.rpow_add hC]
    have e1 : 2 * A + (-A + -A) = 0 := by ring
    have e2 : -A + -A = -(2 * A) := by ring
    rw [e1, e2, Real.rpow_zero, one_mul]
  rw [hx', ← key]
  exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (Real.rpow_nonneg hCy.le _) (Real.rpow_nonneg ha.le _))
    (Real.rpow_nonneg hC.le _)

theorem orbNormInt_lt_top : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μS μS' : Measure (Mt k r)) (b : ℝ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsHaarOn (Sset k r z) μS → IsHaarOn (Sset k r z') μS' → 2 * ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) * (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) < b → IsCompact C → C ⊆ Greg k r z z' → (∀ γ ∈ C, orbNormInt μS μS' b γ < ⊤) ∧ ∃ F : Mt k r × Mt k r → ℝ, Integrable F (μS.prod μS') ∧ ∀ γ ∈ C, ∀ p : Mt k r × Mt k r, Matrix.of p.1 ∈ Sset k r z → Matrix.of p.2 ∈ Sset k r z' → opn (Matrix.of (act2 γ p)) ^ (-b) ≤ F p := by
  intro k r z z' μS μS' b C hz hz' hT hT' hS hS' hb hC hCr
  obtain ⟨C0, hC0, hbd⟩ := _root_.GlobalTheory.SgInf.PolyProper.poly_proper k r z z' C hz hz' hT hT' hC hCr
  obtain ⟨-, -, -, hSS, -⟩ := _root_.GlobalTheory.SgInf.closedSub_groups k r z hz hT
  obtain ⟨-, -, -, hSS', -⟩ := _root_.GlobalTheory.SgInf.closedSub_groups k r z' hz' hT'
  set M : ℕ := 2 * (r ^ 2 + r + 1) with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
  have hMpos : (0 : ℝ) < 2 * (M : ℝ) := by linarith
  set A : ℝ := b / (2 * (M : ℝ)) with hA
  have hA2 : 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < A := by
    rw [hA, lt_div_iff₀ hMpos]
    linarith
  have hA0 : 0 ≤ A := le_of_lt (lt_of_le_of_lt (by positivity) hA2)
  have hbA : b = 2 * (M : ℝ) * A := by
    rw [hA]
    field_simp
  have hi := integrable_of_normInt (_root_.GlobalTheory.SgGrowth.normInt_lt_top k r (Sset k r z) μS A hSS hS hA2)
  have hi' := integrable_of_normInt (_root_.GlobalTheory.SgGrowth.normInt_lt_top k r (Sset k r z') μS' A hSS' hS' hA2)
  have : SigmaFinite μS := hS.1
  have : SigmaFinite μS' := hS'.1
  let F : Mt k r × Mt k r → ℝ := fun p =>
    C0 ^ (2 * A) * (opn (Matrix.of p.1) ^ (-A) * opn (Matrix.of p.2) ^ (-A))
  have hF : Integrable F (μS.prod μS') := (hi.mul_prod hi').const_mul _
  have hbound : ∀ γ ∈ C, ∀ p : Mt k r × Mt k r, Matrix.of p.1 ∈ Sset k r z → Matrix.of p.2 ∈ Sset k r z' →
      opn (Matrix.of (act2 γ p)) ^ (-b) ≤ F p := by
    intro γ hγ p h1 h2
    have hg1 := opn_pos (hSS.1 h1)
    have hg2 := opn_pos (hSS'.1 h2)
    have hmax := hbd γ hγ _ h1 _ h2
    rw [hbA]
    exact rpow_le hg1 hg2 (opn_nonneg _) (by linarith) hA0 hmax
  refine ⟨fun γ hγ => ?_, F, hF, hbound⟩
  have e1 : ∀ᵐ p ∂(μS.prod μS'), Matrix.of p.1 ∈ Sset k r z := by
    rw [ae_iff]
    refine measure_mono_null (t := {x : Mt k r | Matrix.of x ∉ Sset k r z} ×ˢ Set.univ)
      (fun p hp => ⟨hp, trivial⟩) ?_
    rw [Measure.prod_prod, hS.2.2.1, zero_mul]
  have e2 : ∀ᵐ p ∂(μS.prod μS'), Matrix.of p.2 ∈ Sset k r z' := by
    rw [ae_iff]
    refine measure_mono_null (t := Set.univ ×ˢ {x : Mt k r | Matrix.of x ∉ Sset k r z'})
      (fun p hp => ⟨trivial, hp⟩) ?_
    rw [Measure.prod_prod, hS'.2.2.1, mul_zero]
  calc orbNormInt μS μS' b γ ≤ ∫⁻ p, ENNReal.ofReal (F p) ∂(μS.prod μS') := by
        unfold orbNormInt
        apply lintegral_mono_ae
        filter_upwards [e1, e2] with p h1 h2
        exact ENNReal.ofReal_le_ofReal (hbound γ hγ p h1 h2)
    _ < ⊤ := hF.lintegral_lt_top

end GlobalTheory.SgInf.OrbNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellChartDifferentialSurjectiveSkew
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens.Onto

open Formalism.QuantumDeterminants.GBasic

lemma wC_eq (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    wC k r i j = if j = sig k r i then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  have hs := sig_val k r i
  unfold wC bigCell esI
  simp only [Fin.ext_iff, Matrix.one_apply, star_one, inv_one]
  split_ifs at * <;> first | rfl | (exfalso; omega)

lemma conj_apply (k r : ℕ) (M : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (wC k r * M * wC k r) i j = M (sig k r i) (sig k r j) := by
  simp only [Matrix.mul_apply, wC_eq k r i, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [wC_eq, eq_sig_iff k r j, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

lemma skew_apply (k r : ℕ) (M : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (Mᴴ * Hpk k r + Hpk k r * M) i j =
      star (M (sig k r j) i) * sgn k r j + sgn k r i * M (sig k r i) j := by
  simp only [Matrix.add_apply, Matrix.mul_apply, conjTranspose_apply, Hpk_eq k r i, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Hpk_eq, eq_sig_iff k r j, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sgn_sig]

lemma skew_iff (k r : ℕ) (M : Mat k r) :
    Mᴴ * Hpk k r + Hpk k r * M = 0 ↔
      ∀ i j, star (M (sig k r j) i) * sgn k r j + sgn k r i * M (sig k r i) j = 0 := by
  rw [← Matrix.ext_iff]
  simp only [skew_apply, Matrix.zero_apply]

lemma lev_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : lev k r (sig k r i) + lev k r i = 2 * r := by
  have hi := i.isLt
  have hs := sig_val k r i
  unfold lev
  split_ifs at * <;> omega

lemma unre {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, realifyFun]

lemma exists_N (k r : ℕ) (M : Mat k r) (h : Mᴴ * Hpk k r + Hpk k r * M = 0) :
    ∃ X : lieE (Nset k r), um X = Matrix.of fun i j => if lev k r i < lev k r j then M i j else 0 := by
  refine ⟨⟨(WithLp.equiv 2 _).symm (realifyFun
    (Matrix.of fun i j => if lev k r i < lev k r j then M i j else 0)), ?_⟩, unre _⟩
  rw [(_root_.GlobalTheory.CellDens.LieN.lieE_Nset k r _).1, unre]
  refine ⟨?_, fun i j hij => by simp [not_lt.2 hij]⟩
  rw [skew_iff] at h ⊢
  intro i j
  have h1 := lev_sig k r i
  have h2 := lev_sig k r j
  simp only [Matrix.of_apply]
  by_cases c : lev k r (sig k r j) < lev k r i
  · rw [if_pos c, if_pos (by omega)]; exact h i j
  · rw [if_neg c, if_neg (by omega)]; simp

lemma exists_lieElement_middleBlockPart (k r : ℕ) (M : Mat k r) (h : Mᴴ * Hpk k r + Hpk k r * M = 0) :
    ∃ Y : lieE (Formalism.FourierDecayAlt.B2.UWb k r), um Y = Matrix.of fun i j =>
      if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then M i j else 0 := by
  refine ⟨⟨(WithLp.equiv 2 _).symm (realifyFun (Matrix.of fun i j =>
      if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then M i j else 0)), ?_⟩, unre _⟩
  rw [(_root_.GlobalTheory.CellLieAlg.lie_entries k r _).2.1, unre]
  refine ⟨?_, fun i j hij => by simp only [Matrix.of_apply, if_neg hij]⟩
  rw [skew_iff] at h ⊢
  intro i j
  have h1 := sig_val k r i
  have h2 := sig_val k r j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Matrix.of_apply]
  by_cases c : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
  · rw [if_pos (by split_ifs at h1 h2 <;> omega), if_pos (by split_ifs at h1 h2 <;> omega)]
    exact h i j
  · rw [if_neg (by split_ifs at h1 h2 <;> omega), if_neg (by split_ifs at h1 h2 <;> omega)]
    simp

theorem dchart_onto : ∀ (k r : ℕ) (Z : Mat k r), Zᴴ * Hpk k r + Hpk k r * Z = 0 →
    ∃ v : EE k r, dchart k r v = Z := by
  intro k r Z hZ
  have hZ' := (skew_iff k r Z).1 hZ
  obtain ⟨X', hX'⟩ := exists_N k r Z hZ
  obtain ⟨Y, hY⟩ := exists_lieElement_middleBlockPart k r Z hZ
  obtain ⟨X, hX⟩ := exists_N k r (Matrix.of fun i j => -Z (sig k r i) (sig k r j)) (by
    rw [skew_iff]
    intro i j
    have := hZ' (sig k r i) (sig k r j)
    simp only [sig_sig, sgn_sig] at this
    simp only [Matrix.of_apply, sig_sig, star_neg]
    linear_combination -this)
  refine ⟨((X, X'), (fun a => Z (eI k r a) (eI k r a), Y)), ?_⟩
  ext i j
  have h1 := lev_sig k r i
  have h2 := lev_sig k r j
  have hi := i.isLt
  have hj := j.isLt
  simp only [dchart, Matrix.add_apply, Matrix.neg_apply, conj_apply, hX, hX', hY, Matrix.of_apply,
    sig_sig, torD, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp only [lt_irrefl, if_false, if_true, neg_zero, zero_add, add_zero, and_self]
    by_cases c : i.val < r
    · rw [dite_eq_left c, if_neg (by omega), add_zero]; rfl
    · rw [dite_eq_right c]
      by_cases c' : r + k < i.val
      · rw [dite_eq_left c', if_neg (by omega), add_zero]
        have e : eI k r ⟨2 * r + k - i.val, by omega⟩ = sig k r i :=
          Fin.ext (by rw [sig_hi k r i c']; rfl)
        rw [e]
        have := hZ' (sig k r i) i
        rw [sgn_sig, sig_sig] at this
        have hs : sgn k r i = 1 := by unfold sgn; rw [if_neg (by omega)]
        rw [hs] at this
        linear_combination -this
      · rw [dite_eq_right c', if_pos (by omega), zero_add]
  · rw [if_neg hij, add_zero]
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have l1 : lev k r i = if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k := rfl
    have l2 : lev k r j = if j.val < r then j.val else if j.val ≤ r + k then r else j.val - k := rfl
    rcases lt_trichotomy (lev k r i) (lev k r j) with c | c | c
    · rw [if_neg (by omega), if_neg (by split_ifs at l1 l2 <;> omega), if_pos c]; simp
    · rw [if_neg (by omega), if_pos (by split_ifs at l1 l2 <;> omega), if_neg (by omega)]; simp
    · rw [if_pos (by omega), if_neg (by split_ifs at l1 l2 <;> omega), if_neg (by omega)]; simp

end GlobalTheory.CellDens.Onto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockDiagonalWithIdentityGLEqOneIff
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

noncomputable section

namespace GlobalTheory.GLm.GGSum

variable {g : ℕ} [Fact g.Prime]

def dirac (g n : ℕ) [Fact g.Prime] : Gn g n → ℂ := fun x => if x = 1 then 1 else 0

theorem tri_add (a b : ℕ) : (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + (a * b + b * (b - 1) / 2) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc a b 1, Nat.triangle_succ, Nat.triangle_succ, ih]; ring

theorem conj_eq_one {G : Type} [Group G] (p x : G) : p * x * p⁻¹ = 1 ↔ x = 1 := by
  constructor
  · intro h
    have : x = p⁻¹ * (p * x * p⁻¹) * p := by group
    rw [this, h]; group
  · rintro rfl; group

theorem dirac_class (n : ℕ) : IsClass (dirac g n) := by
  intro x y
  simp only [dirac, conj_eq_one]

theorem gg_class (ψ : AddChar (ZMod g) ℂ) (n : ℕ) : IsClass (gg ψ n) := by
  intro x z
  unfold gg
  congr 1
  refine (Fintype.sum_equiv (Equiv.mulLeft z) _ _ ?_).symm
  intro y
  have : (z * y)⁻¹ * (z * x * z⁻¹) * (z * y) = y⁻¹ * x * y := by group
  simp only [Equiv.coe_mulLeft, this]

theorem wh_dirac (ψ : AddChar (ZMod g) ℂ) (n : ℕ) :
    wh ψ (dirac g n) = ((g : ℂ) ^ (n * (n - 1) / 2))⁻¹ := by
  rw [← (_root_.GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField g n 0 0 ψ).2.1]
  simp [wh, tr, dirac]

theorem wh_mul_left (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => c * f x) = c * wh ψ f := by
  simp only [wh, tr, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem wh_sum (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (s : Finset ℕ) (f : ℕ → Gn g n → ℂ) :
    wh ψ (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, wh ψ (f i) := by
  simp only [wh, tr, Finset.mul_sum]
  exact Finset.sum_comm

theorem wh_hc (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (a b n : ℕ) (hn : n = a + b) (α : Gn g a → ℂ)
    (β : Gn g b → ℂ) (hα : IsClass α) (hβ : IsClass β) : wh ψ (hc a b α β n) = wh ψ α * wh ψ β := by
  unfold hc
  rw [_root_.GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ a b n hn _ (fun y x z => by simp only [hα x z]) (fun x y z => by simp only [hβ y z])]
  simp only [wh_mul_left]
  rw [mul_comm, ← wh_mul_left]
  simp only [mul_comm]

theorem entN_one (n a b : ℕ) (ha : a < n) (hb : b < n) : entN (1 : Mt g n) a b = if a = b then 1 else 0 := by
  simp [entN, ha, hb, Matrix.one_apply]

theorem tl_one (i n : ℕ) (hi : i ≤ n) : tl i (1 : Mt g n) = 1 := by
  ext a b
  rw [tl, entN_one n a b (by omega) (by omega), Matrix.one_apply]
  simp [Fin.ext_iff]

theorem inR_one (i n : ℕ) (hi : i ≤ n) : InR i (1 : Mt g n) := by
  refine ⟨fun a b h1 h2 => Matrix.one_apply_ne (fun h => by subst h; omega), fun a b => ?_⟩
  have ha := a.2
  have hb := b.2
  rw [br, entN_one n _ _ (by omega) (by omega)]
  refine ⟨fun h => if_neg ?_, fun h => if_pos (by rw [h])⟩
  have : (b : ℕ) < a := h
  omega

theorem supFrom_one (i n : ℕ) : supFrom i (1 : Mt g n) = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  rw [entN_one n _ _ (by omega) (by omega), if_neg (by omega)]

theorem der_dirac (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (hi : i ≤ n) :
    der ψ i (dirac g n) =
      fun h => ((g : ℂ) ^ (i * (n - i) + (n - i) * (n - i - 1) / 2))⁻¹ * dirac g i h := by
  funext h
  rw [_root_.GlobalTheory.GLm.der_eq_sum g ψ i n _ h hi]
  congr 1
  rw [Finset.sum_eq_single (1 : Gn g n)]
  · have e : ((1 : Mt g i) = (h : Mt g i)) ↔ h = 1 :=
      ⟨fun e => Units.ext e.symm, fun e => by rw [e]; rfl⟩
    simp only [Units.val_one, inR_one i n hi, tl_one i n hi, supFrom_one, dirac, true_and, e]
    simp
  · intro x _ hx
    simp [dirac, hx]
  · simp

def dM {k : ℕ} (h : Mt g k) : Mt g (k + 1) :=
  fun i j => if (i : ℕ) < k ∧ (j : ℕ) < k then entN h i j else (1 : Mt g (k + 1)) i j

theorem dM_cc {k : ℕ} (h : Mt g k) (i j : Fin k) : dM h i.castSucc j.castSucc = h i j := by
  simp [dM, entN]

theorem dM_lc {k : ℕ} (h : Mt g k) (j : Fin k) : dM h (Fin.last k) j.castSucc = 0 := by
  simp [dM, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']

theorem dM_cl {k : ℕ} (h : Mt g k) (j : Fin k) : dM h j.castSucc (Fin.last k) = 0 := by
  simp [dM, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne]

theorem dM_ll {k : ℕ} (h : Mt g k) : dM h (Fin.last k) (Fin.last k) = 1 := by
  simp [dM]

theorem dM_mul {k : ℕ} (h h' : Mt g k) : dM h * dM h' = dM (h * h') := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, dM_cc, dM_lc, dM_cl, dM_ll]

theorem dM_one (k : ℕ) : dM (1 : Mt g k) = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [dM_cc, dM_lc, dM_cl, dM_ll, Matrix.one_apply, (Fin.castSucc_lt_last _).ne, (Fin.castSucc_lt_last _).ne']

theorem blockDiagonalWithIdentityGL_eq_one_iff {k : ℕ} (h : Gn g k) : diag1 h (k + 1) = 1 ↔ h = 1 := by
  have hu : IsUnit (dM (h : Mt g k)) :=
    ⟨⟨dM (h : Mt g k), dM ((h⁻¹ : Gn g k) : Mt g k), by rw [dM_mul, Units.mul_inv, dM_one],
      by rw [dM_mul, Units.inv_mul, dM_one]⟩, rfl⟩
  have hc : ((diag1 h (k + 1) : Gn g (k + 1)) : Mt g (k + 1)) = dM (h : Mt g k) := by
    change ((toG (dM (h : Mt g k)) : Gn g (k + 1)) : Mt g (k + 1)) = _
    rw [toG, dite_eq_left hu]; rfl
  constructor
  · intro e
    rw [e] at hc
    apply Units.ext
    ext i j
    rw [← dM_cc (h : Mt g k) i j, ← hc]
    simp [Matrix.one_apply]
  · intro e
    apply Units.ext
    rw [hc, e]
    exact dM_one k

theorem sum_wh_gg : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ k : ℕ,
    ∑ j ∈ Finset.range (k + 1), wh ψ (gg ψ j) = (g : ℂ) ^ k := by
  intro g hg ψ hψ k
  have hg0 : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hg.out.ne_zero
  have h1 : dirac g k = fun h => ∑ i ∈ Finset.range (k + 1),
      hc i (k - i) (der ψ i (dirac g (k + 1))) (gg ψ (k - i)) k h := by
    funext h
    rw [← _root_.GlobalTheory.GLm.mirClass_diag1_eq_sum g ψ hψ k _ (fun p x _ _ => dirac_class _ x p) h]
    simp only [dirac, blockDiagonalWithIdentityGL_eq_one_iff]
  have h2 := wh_dirac ψ k
  rw [h1, wh_sum] at h2
  have h3 : ∀ i ∈ Finset.range (k + 1),
      wh ψ (hc i (k - i) (der ψ i (dirac g (k + 1))) (gg ψ (k - i)) k) =
        ((g : ℂ) ^ (k * (k - 1) / 2 + k))⁻¹ * wh ψ (gg ψ (k + 1 - 1 - i)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [der_dirac ψ i (k + 1) hi.le, wh_hc ψ hψ i (k - i) k (by omega) _ _
      (fun x y => by simp only [dirac_class i x y]) (gg_class ψ _), wh_mul_left, wh_dirac, ← mul_inv, ← pow_add,
      add_comm _ (i * (i - 1) / 2), ← tri_add, Nat.add_sub_cancel' hi.le, Nat.triangle_succ]
    rfl
  rw [Finset.sum_congr rfl h3, ← Finset.mul_sum, Finset.sum_range_reflect (fun j => wh ψ (gg ψ j)), pow_add] at h2
  field_simp at h2
  exact h2

end GlobalTheory.GLm.GGSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnBlocksSpanFlagOfBlockTriangular
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem exists_sum_mulVec_of_triangular {n a : ℕ} {j : Fin a → ℕ} (A B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (hp : ∀ k i, i < k → p k i = 0)
    (hA : ∀ i, A i = ∑ k, B k * p k i) (l : Fin (a + 1)) (u : ∀ i, Fin (j i) → ℂ)
    (hu : ∀ i : Fin a, ¬ i.castSucc < l → u i = 0) :
    ∃ v : ∀ i, Fin (j i) → ℂ, (∀ i : Fin a, ¬ i.castSucc < l → v i = 0) ∧
      ∑ i, A i *ᵥ u i = ∑ i, B i *ᵥ v i := by
  refine ⟨fun k => ∑ i, p k i *ᵥ u i, ?_, ?_⟩
  · intro k hk
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hik : i < k
    · rw [hp k i hik, Matrix.zero_mulVec]
    · have hki : k ≤ i := not_lt.mp hik
      have hi : ¬ i.castSucc < l := fun hi =>
        hk (lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.mpr hki) hi)
      rw [hu i hi, Matrix.mulVec_zero]
  · simp_rw [hA, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sum]
    exact Finset.sum_comm

theorem spansFlag_of_triangular (n a : ℕ) (j : Fin a → ℕ) (A B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (p q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ))
    (hpq : ∀ k i, i < k → p k i = 0 ∧ q k i = 0) (hA : ∀ i, A i = ∑ k, B k * p k i)
    (hB : ∀ i, B i = ∑ k, A k * q k i) (h : SpansFlag A W) : SpansFlag B W := by
  intro k y
  rw [h k y]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact exists_sum_mulVec_of_triangular A B p (fun k i hik => (hpq k i hik).1) hA k u hu
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨w, hw, he⟩ :=
      exists_sum_mulVec_of_triangular B A q (fun k i hik => (hpq k i hik).2) hB k v hv
    exact ⟨w, hw, he⟩

end GlobalTheory.LeviIso
end

