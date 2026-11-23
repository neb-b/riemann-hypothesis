module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.QuadSymbol

namespace GlobalTheory.QuadSymbol.Model

section Quad
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)]

open NumberField IsDedekindDomain in
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)] in
theorem _root_.GlobalTheory.QuadSymbol.Model.isQuadratic :
    Algebra.IsQuadraticExtension K (QuadraticAlgebra K d 0) :=
  ⟨QuadraticAlgebra.finrank_eq_two d 0⟩

open NumberField IsDedekindDomain in
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)] in
theorem _root_.GlobalTheory.QuadSymbol.Model.numberField [NumberField K] :
    NumberField (QuadraticAlgebra K d 0) := by
  haveI : Module.Finite ℚ (QuadraticAlgebra K d 0) := Module.Finite.trans K _
  exact ⟨⟩


open NumberField IsDedekindDomain in
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)] in
theorem _root_.GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt {A : Type} [CommRing A] [Algebra K A] {x : Aˣ} :
    x ∈ _root_.GlobalTheory.QuadSymbol.normGroup K (QuadraticAlgebra K d 0) A ↔
      ∃ a b : A, (x : A) = a ^ 2 - algebraMap K A d * b ^ 2 := by
  refine _root_.GlobalTheory.QuadSymbol.mem_normGroup_iff_form (QuadraticAlgebra.basis d 0) ?_ ?_
  · ext <;> simp [QuadraticAlgebra.basis] <;> rfl
  · ext <;> simp [QuadraticAlgebra.basis]

end Quad

section Real
variable {K : Type} [Field K] [Fact (∀ r : K, r ^ 2 ≠ -1 + 0 * r)]


open NumberField IsDedekindDomain in
variable {K : Type} [Field K] [Fact (∀ r : K, r ^ 2 ≠ -1 + 0 * r)] in
theorem _root_.GlobalTheory.QuadSymbol.Model.eta_real_place (w : InfinitePlace K) (hw : w.IsReal) :
    _root_.GlobalTheory.QuadSymbol.eta K (QuadraticAlgebra K (-1) 0) w.Completion
      (_root_.GlobalTheory.QuadSymbol.infDiag K (-1) w) = -1 := by
  rw [_root_.GlobalTheory.QuadSymbol.eta_eq_neg_one_iff, _root_.GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt]
  rintro ⟨a, b, h⟩
  have h' : (-1 : w.Completion) = a ^ 2 + b ^ 2 := by
    rw [map_neg, map_one] at h
    simpa [_root_.GlobalTheory.QuadSymbol.infDiag, _root_.GlobalTheory.QuadSymbol.toUnits, sub_eq_add_neg] using h
  have := congrArg (InfinitePlace.Completion.ringEquivRealOfIsReal hw) h'
  simp only [map_neg, map_one, map_add (f := _), map_pow] at this
  nlinarith [sq_nonneg (InfinitePlace.Completion.ringEquivRealOfIsReal hw a),
    sq_nonneg (InfinitePlace.Completion.ringEquivRealOfIsReal hw b)]

end Real

section Tower
variable {F K : Type} [Field F] [Field K] [Algebra F K] (d : F)

end Tower

end GlobalTheory.QuadSymbol.Model

end
