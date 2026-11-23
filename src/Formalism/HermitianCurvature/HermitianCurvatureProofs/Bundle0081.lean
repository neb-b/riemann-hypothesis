module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0077
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtCvs
section
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def fct (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 2) → ℕ) (g : Mat k r) (l : Fin (r + 2)) : ℂ :=
  (Dmin k r z z' g l)⁻¹ ^ a l * (star (Dmin k r z z' g l))⁻¹ ^ b l

lemma monoM_eq (D : RealPlaceData k r Wp Wq) (a b : Fin (r + 2) → ℕ) (c : ℕ) (g : Mat k r) :
    C6.monoM D a b c g = (∏ l, fct D.z D.z' a b g l) * ((Gf k r D.z D.z' g : ℝ) : ℂ)⁻¹ ^ c := rfl

lemma prod_update_a (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 2) → ℕ) (g : Mat k r) (l : Fin (r + 2)) :
    (∏ j ∈ Finset.univ.erase l, fct z z' a b g j) *
      ((Dmin k r z z' g l)⁻¹ ^ (a l + 1) * (star (Dmin k r z z' g l))⁻¹ ^ b l) =
      ∏ j, fct z z' (a + Pi.single l 1) b g j := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ l)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    have hjl : j ≠ l := Finset.ne_of_mem_erase hj
    simp [fct, Pi.single_apply, hjl]
  · simp [fct]

lemma prod_update_b (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 2) → ℕ) (g : Mat k r) (l : Fin (r + 2)) :
    (∏ j ∈ Finset.univ.erase l, fct z z' a b g j) *
      ((Dmin k r z z' g l)⁻¹ ^ a l * (star (Dmin k r z z' g l))⁻¹ ^ (b l + 1)) =
      ∏ j, fct z z' a (b + Pi.single l 1) g j := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ l)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    have hjl : j ≠ l := Finset.ne_of_mem_erase hj
    simp [fct, Pi.single_apply, hjl]
  · simp [fct]

theorem hasDerivAt_cvs (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X g : Mat k r) (t : CT k r nf)
    (hnz : ∀ l, (t.a l ≠ 0 ∨ t.b l ≠ 0) → Dmin k r D.z D.z' g l ≠ 0)
    (hG : t.c ≠ 0 → ((Gf k r D.z D.z' g : ℝ) : ℂ) ≠ 0) :
    HasDerivAt (fun s => cvs D t (crv (false, X) g s)) (((dscal D X t).map fun t' => cvs D t' g).sum) 0 := by

  have hF : ∀ l ∈ (Finset.univ : Finset (Fin (r + 2))), HasDerivAt (fun s => fct D.z D.z' t.a t.b (crv (false, X) g s) l)
      ((-(t.a l : ℂ) * eval (vars g) (dP X (qDl D.z D.z' l)) * (Dmin k r D.z D.z' g l)⁻¹ ^ (t.a l + 1)) *
          (star (Dmin k r D.z D.z' g l))⁻¹ ^ t.b l +
        (Dmin k r D.z D.z' g l)⁻¹ ^ t.a l *
          (-(t.b l : ℂ) * eval (vars g) (dP X (qDbl D.z D.z' l)) * (star (Dmin k r D.z D.z' g l))⁻¹ ^ (t.b l + 1)))
      0 := by
    intro l _
    have ha : t.a l = 0 ∨ Dmin k r D.z D.z' (crv (false, X) g 0) l ≠ 0 := by
      rw [crv_zero]; by_cases h : t.a l = 0
      · exact Or.inl h
      · exact Or.inr (hnz l (Or.inl h))
    have hb : t.b l = 0 ∨ star (Dmin k r D.z D.z' (crv (false, X) g 0) l) ≠ 0 := by
      rw [crv_zero]; by_cases h : t.b l = 0
      · exact Or.inl h
      · exact Or.inr (star_ne_zero.2 (hnz l (Or.inr h)))
    have h1 := hasDerivAt_invpow' (hasDerivAt_polyD X g D.z D.z' l) ha
    have h2 := hasDerivAt_invpow' (hasDerivAt_polyDb X g D.z D.z' l) hb
    have := h1.fun_mul h2
    simpa only [fct, crv_zero] using this
  have hprod := HasDerivAt.fun_finsetProd hF
  have hGd := hasDerivAt_invpow' (hasDerivAt_polyG X g D.z D.z') (a := t.c) (by
    rw [crv_zero]; by_cases h : t.c = 0
    · exact Or.inl h
    · exact Or.inr (hG h))
  have hP := hasDerivAt_poly X g t.q
  have hall := hP.fun_mul (hprod.fun_mul hGd)
  have hfun : (fun s => cvs D t (crv (false, X) g s)) = fun s => eval (vars (crv (false, X) g s)) t.q *
      ((∏ l ∈ Finset.univ, fct D.z D.z' t.a t.b (crv (false, X) g s) l) * ((Gf k r D.z D.z' (crv (false, X) g s) : ℝ) : ℂ)⁻¹ ^ t.c) := by
    funext s; simp [cvs, monoM_eq]
  rw [hfun]
  refine hall.congr_deriv ?_

  simp only [crv_zero]
  set P0 := eval (vars g) t.q
  set G0 := ((Gf k r D.z D.z' g : ℝ) : ℂ)
  set dG := eval (vars g) (dP X (qGf D.z D.z'))
  have hsum : ∑ l ∈ (Finset.univ : Finset (Fin (r + 2))), (∏ j ∈ Finset.univ.erase l, fct D.z D.z' t.a t.b g j) •
      ((-(t.a l : ℂ) * eval (vars g) (dP X (qDl D.z D.z' l)) * (Dmin k r D.z D.z' g l)⁻¹ ^ (t.a l + 1)) *
          (star (Dmin k r D.z D.z' g l))⁻¹ ^ t.b l +
        (Dmin k r D.z D.z' g l)⁻¹ ^ t.a l *
          (-(t.b l : ℂ) * eval (vars g) (dP X (qDbl D.z D.z' l)) * (star (Dmin k r D.z D.z' g l))⁻¹ ^ (t.b l + 1))) =
      ∑ l, (-(t.a l : ℂ) * eval (vars g) (dP X (qDl D.z D.z' l)) * ∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j) +
      ∑ l, (-(t.b l : ℂ) * eval (vars g) (dP X (qDbl D.z D.z' l)) * ∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [← prod_update_a, ← prod_update_b, smul_eq_mul]
    ring
  have hcq : cvs D { t with q := dP X t.q } g =
      eval (vars g) (dP X t.q) * ((∏ l, fct D.z D.z' t.a t.b g l) * G0⁻¹ ^ t.c) := by
    simp [cvs, monoM_eq, G0]
  have hca : ∀ l, cvs D (if t.a l = 0 then { t with q := 0 } else
      { t with q := C (-(t.a l : ℂ)) * t.q * dP X (qDl D.z D.z' l), a := t.a + Pi.single l 1 }) g =
      -(t.a l : ℂ) * P0 * eval (vars g) (dP X (qDl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j) * G0⁻¹ ^ t.c) := by
    intro l
    split_ifs with h
    · simp [cvs, h]
    · simp [cvs, monoM_eq, P0, G0]; try ring
  have hcb : ∀ l, cvs D (if t.b l = 0 then { t with q := 0 } else
      { t with q := C (-(t.b l : ℂ)) * t.q * dP X (qDbl D.z D.z' l), b := t.b + Pi.single l 1 }) g =
      -(t.b l : ℂ) * P0 * eval (vars g) (dP X (qDbl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j) * G0⁻¹ ^ t.c) := by
    intro l
    split_ifs with h
    · simp [cvs, h]
    · simp [cvs, monoM_eq, P0, G0]; try ring
  have hcc : cvs D (if t.c = 0 then { t with q := 0 } else
      { t with q := C (-(t.c : ℂ)) * t.q * dP X (qGf D.z D.z'), c := t.c + 1 }) g =
      -(t.c : ℂ) * P0 * dG * ((∏ l, fct D.z D.z' t.a t.b g l) * G0⁻¹ ^ (t.c + 1)) := by
    split_ifs with h
    · simp [cvs, h]
    · simp [cvs, monoM_eq, P0, G0, dG]; try ring
  have hlist : ((dscal D X t).map fun t' => cvs D t' g).sum =
      eval (vars g) (dP X t.q) * ((∏ l, fct D.z D.z' t.a t.b g l) * G0⁻¹ ^ t.c) +
      ∑ l, (-(t.a l : ℂ) * P0 * eval (vars g) (dP X (qDl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j) * G0⁻¹ ^ t.c)) +
      ∑ l, (-(t.b l : ℂ) * P0 * eval (vars g) (dP X (qDbl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j) * G0⁻¹ ^ t.c)) +
      (-(t.c : ℂ) * P0 * dG * ((∏ l, fct D.z D.z' t.a t.b g l) * G0⁻¹ ^ (t.c + 1))) := by
    simp only [dscal, List.map_append, List.map_cons, List.map_nil, List.map_ofFn, List.sum_append,
      List.sum_cons, List.sum_nil, List.sum_ofFn, add_zero, Function.comp_def, hcq, hca, hcb, hcc]
    try ring
  rw [hlist, hsum]
  have eA : P0 * (∑ l, (-(t.a l : ℂ) * eval (vars g) (dP X (qDl D.z D.z' l)) *
      ∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j)) * G0⁻¹ ^ t.c =
      ∑ l, (-(t.a l : ℂ) * P0 * eval (vars g) (dP X (qDl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' (t.a + Pi.single l 1) t.b g j) * G0⁻¹ ^ t.c)) := by
    rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro l _; ring
  have eB : P0 * (∑ l, (-(t.b l : ℂ) * eval (vars g) (dP X (qDbl D.z D.z' l)) *
      ∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j)) * G0⁻¹ ^ t.c =
      ∑ l, (-(t.b l : ℂ) * P0 * eval (vars g) (dP X (qDbl D.z D.z' l)) *
        ((∏ j, fct D.z D.z' t.a (t.b + Pi.single l 1) g j) * G0⁻¹ ^ t.c)) := by
    rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro l _; ring
  linear_combination eA + eB

end Formalism.FourierDecayAlt.P.MinorPolynomials
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLpBzOfSup
section
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace ENNReal

noncomputable section

open Classical

section ss2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem memLp_bz_of_sup {s : ℕ} (hs : s ≠ 0) {β : ℂ} (hβ : β ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1)
    (ut : ℂ → ℂ → H) (bt : ℂ → H) (SS : ℝ) (memU : ∀ x : ℂ, x ≠ 0 → MemLp (ut x) 2 volume)
    (sup : ∀ x : ℂ, x ≠ 0 → ∫ D, ‖ut x D‖ ^ 2 ≤ SS) (hbt : StronglyMeasurable bt)
    (hloc : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖bz s bt z‖ ^ 2) K)
    (germ : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 →
      ∀ᵐ D, D ∈ K → ‖ut x D - mainD s β ε bt x D‖ ≤ C * ‖x‖⁻¹) :
    MemLp (bz s bt) 2 volume ∧ ∫ z, ‖bz s bt z‖ ^ 2 ≤ SS := by
  have hSS : 0 ≤ SS := (integral_nonneg fun D => sq_nonneg ‖ut 1 D‖).trans (sup 1 one_ne_zero)
  have hε0 : ε ≠ 0 := by
    intro h; rw [h, norm_zero] at hε; exact zero_ne_one hε
  let K : ℕ → Set ℂ := fun n => {z : ℂ | ε⁻¹ * z ^ s ∈ ann n}
  have hKc : ∀ n, IsCompact (K n) := fun n => isCompact_preimage_pow hs hε (isCompact_ann n)
  have hK0 : ∀ n, (0 : ℂ) ∉ K n := fun n => zero_notMem_preimage_pow hs ε (zero_notMem_ann n)
  have hKm : ∀ n, MeasurableSet (K n) := fun n => (hKc n).isClosed.measurableSet
  have hbm : StronglyMeasurable (bz s bt) := stronglyMeasurable_bz s hbt
  have hmem : ∀ n, MemLp ((K n).indicator (bz s bt)) 2 volume := fun n =>
    memLp_indicator_bz hbt (hKm n) (hloc _ (hKc n) (hK0 n))
  have hbound : ∀ n, ∫ z, ‖(K n).indicator (bz s bt) z‖ ^ 2 ≤ SS := fun n => by
    obtain ⟨C, hC⟩ := germ (ann n) (isCompact_ann n) (zero_notMem_ann n)
    exact integral_bz_Q_le hs hβ hε ut bt SS memU sup hbt (ann n) (isCompact_ann n)
      (hloc _ (hKc n) (hK0 n)) C hC
  let g : ℕ → ℂ → ℝ≥0∞ := fun n z => ENNReal.ofReal (‖(K n).indicator (bz s bt) z‖ ^ 2)
  have hgm : ∀ n, Measurable (g n) := fun n =>
    ENNReal.measurable_ofReal.comp (((hbm.indicator (hKm n)).norm.measurable).pow_const 2)
  have hKmono : Monotone K := fun m n hmn z hz => ann_mono hmn hz
  have hgmono : Monotone g := by
    intro m n hmn z
    apply ENNReal.ofReal_le_ofReal
    by_cases hz : z ∈ K m
    · simp only [Set.indicator_of_mem hz, Set.indicator_of_mem (hKmono hmn hz), le_refl]
    · rw [Set.indicator_of_notMem hz, norm_zero, zero_pow two_ne_zero]
      positivity
  have hgn : ∀ n, ∫⁻ z, g n z ≤ ENNReal.ofReal SS := fun n => by
    have hi : Integrable (fun z => ‖(K n).indicator (bz s bt) z‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm (hmem n).aestronglyMeasurable).1 (hmem n)
    show ∫⁻ z, ENNReal.ofReal (‖(K n).indicator (bz s bt) z‖ ^ 2) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun z => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hsup : (fun z => ENNReal.ofReal (‖bz s bt z‖ ^ 2)) =ᵐ[volume] fun z => ⨆ n, g n z := by
    have h0 : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [h0] with z hz
    have hw : ε⁻¹ * z ^ s ≠ 0 := mul_ne_zero (inv_ne_zero hε0) (pow_ne_zero _ hz)
    obtain ⟨n, hn⟩ := exists_mem_ann hw
    apply le_antisymm
    · refine le_iSup_of_le n (le_of_eq ?_)
      show ENNReal.ofReal (‖bz s bt z‖ ^ 2) = ENNReal.ofReal (‖(K n).indicator (bz s bt) z‖ ^ 2)
      rw [Set.indicator_of_mem (show z ∈ K n from hn)]
    · refine iSup_le fun m => ENNReal.ofReal_le_ofReal ?_
      by_cases hzm : z ∈ K m
      · simp only [Set.indicator_of_mem hzm, le_refl]
      · rw [Set.indicator_of_notMem hzm, norm_zero, zero_pow two_ne_zero]
        positivity
  have hlin : ∫⁻ z, ENNReal.ofReal (‖bz s bt z‖ ^ 2) ≤ ENNReal.ofReal SS := by
    rw [lintegral_congr_ae hsup, lintegral_iSup hgm hgmono]
    exact iSup_le hgn
  have hint : Integrable (fun z => ‖bz s bt z‖ ^ 2) := by
    refine ⟨(hbm.norm.measurable.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq_norm hbm.aestronglyMeasurable).2 hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _)
    (hbm.norm.measurable.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hSS hlin

end ss2

end

end Formalism.FourierDecayAlt.P.PBK
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedR
section
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.NFRadRedR

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def LocLog : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∃ O : Set (Q.Mx k r), IsOpen O ∧ (1 : Q.Mx k r) ∈ O ∧ ∃ Λ : Q.Mx k r → Q.Mx k r, ContDiffOn ℝ ∞ Λ O ∧
      ∀ g ∈ O, g ∈ UWset k r z → InLieW k r z (Λ g) ∧ NormedSpace.exp (Λ g) = g

variable {k r : ℕ}

def lieW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Submodule ℝ (Q.Mx k r) where
  carrier := {X | InLieW k r z X}
  zero_mem' := ⟨⟨by simp, fun a _ => ⟨by simp, by simp⟩⟩, by simp⟩
  add_mem' := by
    rintro X Y ⟨⟨hX1, hX2⟩, hX3⟩ ⟨⟨hY1, hY2⟩, hY3⟩
    refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
    · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
        show Xᴴ * Hpk k r + Yᴴ * Hpk k r + (Hpk k r * X + Hpk k r * Y) =
          (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) by abel, hX1, hY1, add_zero]
    · rw [Matrix.add_mulVec, (hX2 a ha).1, (hY2 a ha).1, add_zero]
    · rw [Matrix.add_mulVec, (hX2 a ha).2, (hY2 a ha).2, add_zero]
    · rw [Matrix.add_mulVec, hX3, hY3, add_zero]
  smul_mem' := by
    rintro c X ⟨⟨hX1, hX2⟩, hX3⟩
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
    · rw [Matrix.conjTranspose_smul]
      simp only [RCLike.star_def, RCLike.conj_ofReal]
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX1, smul_zero]
    · rw [Matrix.smul_mulVec, (hX2 a ha).1, smul_zero]
    · rw [Matrix.smul_mulVec, (hX2 a ha).2, smul_zero]
    · rw [Matrix.smul_mulVec, hX3, smul_zero]

def dOpL {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (hπ : Qr.IsRepW k r z π) :
    lieW k r z →ₗ[ℝ] (Wp →L[ℂ] Wp) where
  toFun X := dOp π (X : Q.Mx k r)
  map_add' X Y := (P.differential_operator_linear Wp k r z π hπ X Y X.2 Y.2).1
  map_smul' s X := by
    have h := (P.differential_operator_linear Wp k r z π hπ X X X.2 X.2).2 s
    show dOp π (s • (X : Q.Mx k r)) = s • dOp π (X : Q.Mx k r)
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact h

private lemma rep_exp_smul_eq_exp_dOp {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)} (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) {X : Q.Mx k r} (hX : InLieW k r z X) (t : ℝ) :
    π (NormedSpace.exp ((t : ℂ) • X)) = NormedSpace.exp (t • dOp π X) := by
  set A := dOp π X with hA
  set f : ℝ → (Wp →L[ℂ] Wp) := fun s => π (NormedSpace.exp ((s : ℂ) • X)) with hf
  have hmul : ∀ s u : ℝ, f (s + u) = f s * f u := by
    intro s u
    simp only [hf]
    rw [show ((s + u : ℝ) : ℂ) • X = (s : ℂ) • X + (u : ℂ) • X by push_cast; rw [add_smul],
      Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _),
      hπ.2 _ (exp_uw hX s) _ (exp_uw hX u), ContinuousLinearMap.mul_def]
  have h0 : HasDerivAt f A 0 := dOp_hasDeriv hπ hc hX
  have hd : ∀ s, HasDerivAt f (f s * A) s := by
    intro s
    have h2 : HasDerivAt (fun u => f s * f u) (f s * A) (s - s) := by
      rw [sub_self]
      exact h0.const_mul (f s)
    have h1 : HasDerivAt (fun u => f s * f (u - s)) (f s * A) s := HasDerivAt.comp_sub_const s s h2
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    show f u = f s * f (u - s)
    rw [← hmul]
    congr 1
    ring
  have hg : ∀ s, HasDerivAt (fun u => f u * NormedSpace.exp (u • -A)) 0 s := by
    intro s
    have := (hd s).mul (hasDerivAt_exp_smul_const (-A) s)
    have hcomm : Commute A (NormedSpace.exp (s • -A)) :=
      ((Commute.refl A).neg_right.smul_right s).exp_right
    have h0' : f s * A * NormedSpace.exp (s • -A) + f s * (NormedSpace.exp (s • -A) * -A) = 0 := by
      rw [mul_assoc, hcomm.eq, mul_neg, mul_neg, add_neg_cancel]
    exact this.congr_deriv h0'
  have hconst : ∀ s, f s * NormedSpace.exp (s • -A) = 1 := by
    intro s
    have hdiff : Differentiable ℝ (fun u => f u * NormedSpace.exp (u • -A)) := fun u => (hg u).differentiableAt
    have := is_const_of_deriv_eq_zero hdiff (fun u => (hg u).deriv) s 0
    rw [this]
    simp only [hf, zero_smul, Complex.ofReal_zero, NormedSpace.exp_zero, mul_one, hπ.1]
  have hk : ∀ s, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A)) 0 s := by
    intro s
    have := (hasDerivAt_exp_smul_const (-A) s).mul (hasDerivAt_exp_smul_const A s)
    have hcomm2 : Commute A (NormedSpace.exp (s • A)) := ((Commute.refl A).smul_right s).exp_right
    have h0' : NormedSpace.exp (s • -A) * -A * NormedSpace.exp (s • A) +
        NormedSpace.exp (s • -A) * (NormedSpace.exp (s • A) * A) = 0 := by
      rw [mul_assoc, neg_mul, hcomm2.eq, mul_neg, neg_add_cancel]
    exact this.congr_deriv h0'
  have hinv : NormedSpace.exp (t • -A) * NormedSpace.exp (t • A) = 1 := by
    have hdiff : Differentiable ℝ (fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A)) :=
      fun u => (hk u).differentiableAt
    have := is_const_of_deriv_eq_zero hdiff (fun u => (hk u).deriv) t 0
    rw [this]
    simp only [zero_smul, NormedSpace.exp_zero, mul_one]
  calc f t = f t * (NormedSpace.exp (t • -A) * NormedSpace.exp (t • A)) := by rw [hinv, mul_one]
    _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hconst t, one_mul]

private lemma contDiff_exp_hermitian_curvature {A : Type} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    ContDiff ℝ ∞ (NormedSpace.exp : A → A) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  exact (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt

theorem repSmooth_of (hLL : LocLog) : NFRadRedS.RepSmooth := by
  unfold NFRadRedS.RepSmooth
  intro Wp _ _ _ k r z π hz hTz hπ hc h₀ hh₀
  obtain ⟨O, hO, h1O, Λ, hΛ, hΛe⟩ := hLL k r z hz hTz
  have hrep : Qr.IsRepW k r z π := ⟨hπ, hc⟩
  have hdetH : IsUnit (Hpk k r).det := by
    have h := congrArg Matrix.det (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r)
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
  have hdet0 : IsUnit h₀.det := ((Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) hdetH).2.2 h₀ hh₀.1).1
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (lieW k r z)
  let T : Q.Mx k r →ₗ[ℝ] (Wp →L[ℂ] Wp) := (dOpL z π hrep).comp (Submodule.linearProjOfIsCompl _ q hq)
  have hT1 : ∀ Y, InLieW k r z Y → T Y = dOp π Y := by
    intro Y hY
    have hp := Submodule.linearProjOfIsCompl_apply_left hq ⟨Y, hY⟩
    show dOpL z π hrep (Submodule.linearProjOfIsCompl _ q hq Y) = dOp π Y
    rw [show Submodule.linearProjOfIsCompl _ q hq Y = ⟨Y, hY⟩ from hp]
    rfl
  let Tc := LinearMap.toContinuousLinearMap T
  let Lm : Q.Mx k r →ₗ[ℝ] Q.Mx k r :=
    { toFun := fun h => h₀⁻¹ * h
      map_add' := fun a b => Matrix.mul_add _ _ _
      map_smul' := fun c a => by simp [Matrix.mul_smul] }
  let Lc := LinearMap.toContinuousLinearMap Lm
  have hV : IsOpen {h : Q.Mx k r | h₀⁻¹ * h ∈ O} := hO.preimage Lc.continuous
  refine ⟨{h : Q.Mx k r | h₀⁻¹ * h ∈ O}, hV, ?_, fun h => π h₀ * NormedSpace.exp (Tc (Λ (h₀⁻¹ * h))), ?_, ?_⟩
  · show h₀⁻¹ * h₀ ∈ O
    rw [Matrix.nonsing_inv_mul h₀ hdet0]
    exact h1O
  · have h1 : ContDiffOn ℝ ∞ (fun h => Λ (Lc h)) {h : Q.Mx k r | h₀⁻¹ * h ∈ O} :=
      hΛ.comp Lc.contDiff.contDiffOn (fun h hh => hh)
    exact contDiffOn_const.mul (contDiff_exp_hermitian_curvature.comp_contDiffOn (Tc.contDiff.comp_contDiffOn h1))
  · intro h hV' hU
    have hg : h₀⁻¹ * h ∈ UWset k r z := Formalism.QuantumDeterminants.WeylGroupFacts.uw_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh₀) hU
    obtain ⟨hlie, hexp⟩ := hΛe _ hV' hg
    have hpi := rep_exp_smul_eq_exp_dOp hπ hc hlie 1
    simp only [Complex.ofReal_one, one_smul] at hpi
    rw [hexp] at hpi
    calc π h = π (h₀ * (h₀⁻¹ * h)) := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv h₀ hdet0, Matrix.one_mul]
      _ = (π h₀).comp (π (h₀⁻¹ * h)) := hπ.2 _ hh₀ _ hg
      _ = π h₀ * NormedSpace.exp (Tc (Λ (h₀⁻¹ * h))) := by
          rw [ContinuousLinearMap.mul_def, hpi,
            show Tc (Λ (h₀⁻¹ * h)) = dOp π (Λ (h₀⁻¹ * h)) from hT1 _ hlie]

end Formalism.FourierDecayAlt.P.NFRadRedR

namespace Formalism.FourierDecayAlt.P

theorem representation_smooth_of_log : NFRadRedR.LocLog → NFRadRedS.RepSmooth := fun h => NFRadRedR.repSmooth_of h

end Formalism.FourierDecayAlt.P
end
end

