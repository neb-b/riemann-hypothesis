module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Algebra.Module.ZLattice.Covolume

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.T8m
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Metric

namespace Formalism.L2.SG.Pf.Tau

theorem t8m : MinkowskiFirstTheorem := by
  intro d hd
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (by rw [hfr]; omega)
  set v1 : ℝ := (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal with hv1_def
  have hv1ne : volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hv1pos : 0 < v1 :=
    ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' hv1ne
  refine ⟨4 / v1 ^ ((2 : ℝ) / d), by positivity, ?_⟩
  intro L _ _
  let b := Module.Free.chooseBasis ℤ L
  have hF := ZLattice.isAddFundamentalDomain b (volume : Measure (EuclideanSpace ℝ (Fin d)))
  set F := ZSpan.fundamentalDomain (Module.Basis.ofZLatticeBasis ℝ L b) with hF_def
  have hcov : ZLattice.covolume L = volume.real F := ZLattice.covolume_eq_measure_fundamentalDomain L volume hF
  have hcov0 : 0 ≤ ZLattice.covolume L := by rw [hcov]; exact measureReal_nonneg
  have hFfin : volume F ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  set r : ℝ := 2 * (ZLattice.covolume L / v1) ^ ((1 : ℝ) / d) with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hq0 : 0 ≤ ZLattice.covolume L / v1 := by positivity
  have key : ∀ t : ℝ, 0 ≤ t → (t ^ ((1 : ℝ) / d)) ^ d = t := fun t ht => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht, one_div_mul_cancel hdpos.ne', Real.rpow_one]
  have key2 : ∀ t : ℝ, 0 ≤ t → (t ^ ((1 : ℝ) / d)) ^ 2 = t ^ ((2 : ℝ) / d) := fun t ht => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    congr 1
    push_cast
    ring
  have hrd : r ^ d = 2 ^ d * (ZLattice.covolume L / v1) := by
    rw [hr_def, mul_pow, key _ hq0]
  have hvol : volume F * 2 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d))
      ≤ volume (closedBall (0 : EuclideanSpace ℝ (Fin d)) r) := by
    rw [Measure.addHaar_closedBall volume 0 hr0, hfr, hrd, ← ENNReal.ofReal_toReal hv1ne, ← hv1_def,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_toReal hFfin]
    have : (volume F).toReal = ZLattice.covolume L := by rw [hcov]; rfl
    have e : (2 : ℝ) ^ d * (ZLattice.covolume L / v1) * v1 = ZLattice.covolume L * 2 ^ d := by
      field_simp
    rw [this, e, ENNReal.ofReal_mul hcov0, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat]
  haveI hcL : Countable L := Countable.of_equiv _ b.repr.toEquiv.symm
  haveI : Countable L.toAddSubgroup := hcL
  haveI : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := L.toAddSubgroup) hF (fun y hy => by simpa using hy) (convex_closedBall _ _)
    (isCompact_closedBall _ _) hvol
  refine ⟨x, x.2, fun h => hx0 (Subtype.ext h), ?_⟩
  have hxr : ‖(x : EuclideanSpace ℝ (Fin d))‖ ≤ r := by simpa using hxs
  calc ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxr 2
    _ = 4 / v1 ^ ((2 : ℝ) / d) * ZLattice.covolume L ^ ((2 : ℝ) / d) := by
      rw [hr_def, mul_pow, key2 _ hq0, Real.div_rpow hcov0 hv1pos.le]
      ring
  exact le_rfl

end Formalism.L2.SG.Pf.Tau
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.ThirdEstimateOfFirstTwo
section
set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem exists_ne_zero_mem_L (I : AutInst) (hn : 1 ≤ I.n) : ∃ l ∈ I.L, l ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have h := I.L_span
  have h0 : Submodule.span I.E (I.L : Set (Fin I.n → I.E)) = ⊥ := by
    rw [Submodule.span_eq_bot]
    exact hcon
  rw [h0] at h
  haveI : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
  exact bot_ne_top h

theorem third_estimate_of_first_two (h0 : LatticeCommensurable) (h1 : LatticeFinitelyGenerated) : SubmoduleExists := by
  intro I hn x
  obtain ⟨m, hm1, _, hLm⟩ := h0 I x
  obtain ⟨M, _, hM⟩ := h1 I x
  obtain ⟨l, hlL, hl0⟩ := exists_ne_zero_mem_L I hn
  have hml : ((m : I.E) • l) ∈ (M : Set (Fin I.n → I.E)) := by
    rw [hM]
    exact hLm l hlL
  have hm0 : ((m : I.E) • l) ≠ 0 := smul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hl0
  obtain ⟨t, htM, hspan, hli⟩ := exists_linearIndependent I.E (M : Set (Fin I.n → I.E))
  have htfin : t.Finite := hli.setFinite
  have hne : t.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Submodule.span_empty] at hspan
    have h2 : ((m : I.E) • l) ∈ Submodule.span I.E (M : Set (Fin I.n → I.E)) := Submodule.subset_span hml
    rw [← hspan] at h2
    exact hm0 ((Submodule.mem_bot _).mp h2)
  haveI := htfin.fintype
  let e := (Fintype.equivFin t).symm
  refine ⟨⟨Fintype.card t, ?_, fun a => (e a : Fin I.n → I.E), ?_, M, ?_, ?_, ?_⟩⟩
  · exact Fintype.card_pos_iff.mpr hne.to_subtype
  · exact hli.comp _ e.injective
  · exact hM.le
  · intro a
    exact htM (e a).2
  · intro v hv
    have hr : Set.range (fun a => (e a : Fin I.n → I.E)) = t := by
      ext v
      constructor
      · rintro ⟨a, rfl⟩
        exact (e a).2
      · intro hv
        exact ⟨e.symm ⟨v, hv⟩, by simp⟩
    rw [hr, hspan]
    exact Submodule.subset_span hv

end Formalism.L2.SG.Pf.Tau
end
end

