module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualWeylModuleInvRationalPointEqConjCharAt
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Bundle0001

@[expose] public section

noncomputable section

open NumberField Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

theorem weylat_weylChar_eq_gtChar {n : ℕ} (l : DomWeight n) (γ : Fin n → ℂ) (h0 : ∀ i, γ i ≠ 0)
    (hinj : Function.Injective γ) :
    PositivityTheory.RgBcC.weylChar l.w γ = ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar n l.w γ := by
  have hA : (Matrix.of fun i j : Fin n => γ i ^ (l.w j + ((n - 1 - (j : ℕ) : ℕ) : ℤ))).det =
      ReciprocityTheory.ChartRestriction.TR.Weyl.alt n (l.w + ReciprocityTheory.ChartRestriction.TR.Weyl.delta n) γ := by
    unfold ReciprocityTheory.ChartRestriction.TR.Weyl.alt
    congr 1
    ext i j
    simp only [Matrix.of_apply, Pi.add_apply, ReciprocityTheory.ChartRestriction.TR.Weyl.delta]
    congr 1
    have := j.isLt
    omega
  have hV : (Matrix.of fun i j : Fin n => γ i ^ (n - 1 - (j : ℕ))).det =
      ReciprocityTheory.ChartRestriction.TR.Weyl.alt n (0 + ReciprocityTheory.ChartRestriction.TR.Weyl.delta n) γ := by
    unfold ReciprocityTheory.ChartRestriction.TR.Weyl.alt
    congr 1
    ext i j
    simp only [Matrix.of_apply, Pi.add_apply, Pi.zero_apply, zero_add, ReciprocityTheory.ChartRestriction.TR.Weyl.delta]
    rw [← zpow_natCast]
    congr 1
    have := j.isLt
    omega
  have h1 := ReciprocityTheory.ChartRestriction.TR.Weyl.weylGT ℂ n l.w l.anti γ h0
  have h2 := ReciprocityTheory.ChartRestriction.TR.Weyl.weylGT ℂ n 0 antitone_const γ h0
  have hzero : ∀ (m : ℕ) (t : Fin m → ℂ), ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar m 0 t = 1 := by
    intro m
    induction m with
    | zero => intro t; simp [ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar]
    | succ m ih =>
      intro t
      have h : ReciprocityTheory.ChartRestriction.TR.Weyl.interl (0 : Fin (m + 1) → ℤ) = {(0 : Fin m → ℤ)} := by
        ext mu
        simp only [ReciprocityTheory.ChartRestriction.TR.Weyl.interl, Fintype.mem_piFinset,
          Pi.zero_apply, Finset.Icc_self, Finset.mem_singleton]
        exact ⟨fun h => funext h, fun h i => congrFun h i⟩
      rw [ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar, h, Finset.sum_singleton, ih]
      simp [ReciprocityTheory.ChartRestriction.TR.Weyl.wsum]
  rw [hzero, mul_one] at h2
  have hw : ReciprocityTheory.ChartRestriction.TR.Weyl.wden n γ ≠ 0 := by
    unfold ReciprocityTheory.ChartRestriction.TR.Weyl.wden
    refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
    split_ifs with h
    · exact sub_ne_zero.2 fun e => (ne_of_lt h) (hinj e)
    · exact one_ne_zero
  unfold PositivityTheory.RgBcC.weylChar
  rw [hA, hV, ← h1, ← h2, mul_div_cancel_left₀ _ hw]

theorem weylAt_holds : WeylAt := by
  intro n l γ h0 hinj
  let D : GL (Fin n) ℂ := Formalism.BasicNotions.diagGL ℂ n fun i => Units.mk0 _ (h0 i)
  have hD : (D : Matrix (Fin n) (Fin n) ℂ) = diagonal γ := by
    change diagonal (fun a => ((Units.mk0 _ (h0 a) : ℂˣ) : ℂ)) = _
    simp only [Units.val_mk0]
  have hex : ∃ g : GL (Fin n) ℂ, g.val.charpoly = (diagonal γ).charpoly := ⟨D, by rw [hD]⟩
  unfold chAt
  rw [dite_eq_left hex, GlobalTheory.ContraChar.trace_sqRep_eq_of_charpoly_eq l _ D (hex.choose_spec.trans (by rw [hD])),
    GlobalTheory.ContraChar.trace_sqRep_diag l D γ hD, weylat_weylChar_eq_gtChar l γ h0 hinj]

end PositivityTheory.Rg.BcB.G8

end
