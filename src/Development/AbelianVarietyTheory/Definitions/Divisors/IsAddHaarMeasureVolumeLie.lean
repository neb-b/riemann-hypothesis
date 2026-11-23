module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped ContDiff

namespace GlobalTheory.JSW

def schur (n : ℕ) (l : Fin n → ℕ) : MvPolynomial (Fin n) ℤ :=
  Matrix.det (Matrix.of fun i j : Fin n =>
    if ((l i : ℤ) - i + j) < 0 then 0 else MvPolynomial.hsymm (Fin n) ℤ (((l i : ℤ) - i + j).toNat))

def schurAt {n : ℕ} (l : Fin n → ℕ) (α : Fin n → ℂ) : ℂ := MvPolynomial.eval₂ (Int.castRingHom ℂ) α (schur n l)

def sphW (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (l : Fin n → ℕ) : ℂ :=
  if Antitone l then
    (q : ℂ) ^ (-(∑ i : Fin n, (((n : ℂ) - 1 - 2 * (i : ℕ)) * (l i : ℂ))) / 2) * schurAt l α
  else 0

theorem schur_zero (n : ℕ) : schur n (fun _ => 0) = 1 := by
  rw [schur, Matrix.det_of_upperTriangular]
  · simp
  · intro i j h
    have h' : (j : ℕ) < i := h
    rw [Matrix.of_apply, if_pos (by push_cast; omega)]

theorem sphW_of_not_antitone (q : ℕ) {n : ℕ} (α : Fin n → ℂ) {l : Fin n → ℕ} (h : ¬ Antitone l) : sphW q α l = 0 :=
  if_neg h

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

open GlobalTheory.CuspRep


omit [_root_.NumberField.IsTotallyComplex E] in
instance isAddHaarMeasure_volume_lie : Measure.IsAddHaarMeasure (volume : Measure (Lie E a)) :=
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Fin a → Cinf E)) := Measure.pi.isAddHaarMeasure _
  Measure.pi.isAddHaarMeasure _

def smoothInf (f : Lie E a → ℂ) (φ : GA E a → ℂ) (g : GA E a) : ℂ := ∫ x, f x * chart φ g x

def IsTestInf (f : Lie E a → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ invSet E a

def smoothSpan (π : CuspSub E a) : Submodule ℂ (GA E a → ℂ) :=
  Submodule.span ℂ {F | ∃ (f : Lie E a → ℂ) (φ : Sm E a), IsTestInf f ∧ φ ∈ π.V ∧ F = smoothInf f φ.1}



omit [_root_.NumberField.IsTotallyComplex E] in
theorem exists_isTestInf {y : Lie E a} (hy : y ∈ invSet E a) {U : Set (Lie E a)} (hU : U ∈ nhds y) :
    ∃ ρ : Lie E a → ℝ, IsTestInf (fun x => (ρ x : ℂ)) ∧ tsupport ρ ⊆ U ∧ (∀ x, ρ x ∈ Set.Icc (0 : ℝ) 1) ∧ ρ y = 1 := by
  obtain ⟨f, h1, h2, h3, h4, h5⟩ := exists_contDiff_tsupport_subset (n := ⊤) (s := invSet E a ∩ U) (x := y)
    (Filter.inter_mem (isOpen_invSet.mem_nhds hy) hU)
  refine ⟨f, ⟨Complex.ofRealCLM.contDiff.comp h3, h2.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp), ?_⟩,
    h1.trans Set.inter_subset_right, fun x => h4 ⟨x, rfl⟩, h5⟩
  exact (tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) (by simp) f).trans (h1.trans Set.inter_subset_left)

theorem smoothInf_rt_fin (f : Lie E a → ℂ) (φ : GA E a → ℂ) (k : GL (Fin a) (Af E)) (g : GA E a) :
    smoothInf f (fun x => φ (x * finGL E a k)) g = smoothInf f φ (g * finGL E a k) := by
  simp only [smoothInf, chart_rt_fin]

end GlobalTheory.JSW
