module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.NefModelVolumes.ChowFormOfIntegralVersion
section
open MvPolynomial

namespace ChowFormCompatibility

theorem chow_form_of_integral_version : ∀ (k : Type) [Field k] (N e d : ℕ) (I : Ideal (MvPolynomial (Fin N) k)) (f : MvPolynomial (Fin (e + 1) × Fin N) k), GlobalTheory.ChowHt.IsChowFormInt I e d f → GroundTheory.Heights₂.Heights.IsChowForm I (e + 1) f := by
  intro k _ N e d I f h
  refine ⟨h.ne_zero, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · exact h.dvd_of_forall_aeval_eq_zero fun u hu => hg u ((h.zero_iff u).1 hu)
  · rintro ⟨a, rfl⟩ u hu
    rw [map_mul, (h.zero_iff u).2 hu, zero_mul]

end ChowFormCompatibility
end

-- bundled from Development.WeilBound.CoreStatements.NefModelVolumes.ChowFormUniqueUpToConstant
section
open MvPolynomial

namespace ChowFormCompatibility

theorem chow_form_unique_up_to_constant : ∀ (k : Type) [Field k] (N B : ℕ) (I : Ideal (MvPolynomial (Fin N) k)) (f g : MvPolynomial (Fin B × Fin N) k), GroundTheory.Heights₂.Heights.IsChowForm I B f → GroundTheory.Heights₂.Heights.IsChowForm I B g → ∃ c : k, c ≠ 0 ∧ g = C c * f := by
  intro k _ N B I f g hf hg
  have hfg : f ∣ g := (hf.2 g).1 ((hg.2 g).2 dvd_rfl)
  have hgf : g ∣ f := (hg.2 f).1 ((hf.2 f).2 dvd_rfl)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hfg hgf
  obtain ⟨c, hc, hcu⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 u.isUnit
  refine ⟨c, hc.ne_zero, ?_⟩
  rw [← hu, hcu, mul_comm]

end ChowFormCompatibility
end

-- bundled from Development.WeilBound.CoreStatements.NefModelVolumes.HyperplaneSectionDivCycle
section
open MvPolynomial

namespace ChowFormCompatibility

theorem projCycle_eq_fundCycle {k : Type} [Field k] {N : ℕ} (J : Ideal (MvPolynomial (Fin N) k)) :
    GlobalTheory.ChowHt.projCycle J = GroundTheory.Heights₂.Heights.fundCycle J := by
  ext Q
  rw [GroundTheory.Heights₂.Heights.fundCycle, Finsupp.onFinset_apply]
  by_cases hQ : Q ∈ GroundTheory.Heights₂.Heights.relComps J
  · haveI hp : Q.IsPrime := hQ.1.1.1
    have h1 := GlobalTheory.ChowHt.cast_projCycle_apply (J := J) (Q := Q) hQ
    rw [if_pos hQ, GroundTheory.Heights₂.Heights.localMult, dite_eq_left hp]
    have h2 := congrArg ENat.toNat h1
    rw [ENat.toNat_coe] at h2
    exact h2
  · rw [if_neg hQ]
    exact GlobalTheory.ChowHt.projCycle_apply_of_notMem hQ

theorem hyperplane_section_divCycle : ∀ (k : Type) [Field k] (N B : ℕ) (P : Ideal (MvPolynomial (Fin N) k)) (u : Fin N → k) (f : MvPolynomial (Fin (B + 1) × Fin N) k), GlobalTheory.ChowHt.hyperplaneSection P u = GroundTheory.Heights₂.Heights.divCycle P u ∧ GlobalTheory.ChowHt.fixFirstBlock u f = GroundTheory.Heights₂.Heights.specFirst f u := by
  intro k _ N B P u f
  refine ⟨projCycle_eq_fundCycle _, ?_⟩
  have h : (fun p : Fin (B + 1) × Fin N =>
      (Fin.cons (fun j => C (u j)) (fun b j => X (b, j)) :
        Fin (B + 1) → Fin N → MvPolynomial (Fin B × Fin N) k) p.1 p.2) =
      GroundTheory.Heights₂.Heights.specFirstVar u := by
    funext ⟨b, j⟩
    induction b using Fin.cases with
    | zero => rfl
    | succ b => rfl
  rw [GlobalTheory.ChowHt.fixFirstBlock, h]
  rfl

end ChowFormCompatibility
end

