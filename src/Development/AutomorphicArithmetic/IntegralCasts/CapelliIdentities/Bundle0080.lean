module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.LocalRingCardinality.DataArith
public import Formalism.LocalRingCardinality.DataForms

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DecompositionAlmostEverywhere
section
open scoped IntermediateField Algebra TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
attribute [local instance] Formalism.L2.Theta.IsVolMeasG._proof_2 Formalism.L2.Theta.IsVolMeasG._proof_1 Formalism.L2.Theta.IsDsig._proof_2 Formalism.L2.Theta.IsVolMeasG._proof_3

theorem UpperTheory.Reformulated.B.DecompositionAlmostEverywhere.decomp_AE :
    ∀ {D : Formalism.BasicNotions.D7},
    (↥D.host.F)[D.host.sqrtMinusD] = ⊤ →
      ∀ (z : Formalism.L2.Theta.AE D),
        ∃ (p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) (q : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F),
          z =
            (Algebra.algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) (Formalism.L2.Theta.AE D) :
                  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F → Formalism.L2.Theta.AE D)
                p +
              (Algebra.algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) (Formalism.L2.Theta.AE D) :
                    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F → Formalism.L2.Theta.AE D)
                  q *
                (Formalism.L2.Theta.incA D : D.host.E → TensorProduct (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) D.host.E)
                  D.host.sqrtMinusD := by
  intro D h z
  have hz : z ∈ Algebra.adjoin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) {Formalism.L2.Theta.incA D D.host.sqrtMinusD} := by
    have := Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) _ h
    exact (Set.image_singleton ▸ this).ge Algebra.mem_top
  have hs : Formalism.L2.Theta.incA D D.host.sqrtMinusD ^ 2 = -(D.host.d : Formalism.L2.Theta.AE D) := by
    rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD, D.host.sqd_sq, map_neg, map_natCast]
  induction hz using Algebra.adjoin_induction with
  | mem x hx => exact ⟨0, 1, by rw [map_zero, map_one, zero_add, one_mul]; exact hx⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy => obtain ⟨⟨a, b, rfl⟩, c, e, rfl⟩ := And.intro hx hy; exact ⟨a + c, b + e, by rw [map_add (f := _), map_add (f := _)]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨⟨a, b, rfl⟩, c, e, rfl⟩ := And.intro hx hy
    exact ⟨a * c - D.host.d * (b * e), a * e + b * c, by
      simp only [map_add (f := _), map_sub, map_mul, map_natCast]; linear_combination (algebraMap _ _ b * algebraMap _ _ e) * hs⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Pc
section
theorem UpperTheory.Reformulated.B.DivisibilityWeightConstant.exists_int_smul_mem :
    ∀ {D : Formalism.BasicNotions.D7} {u : D.what₂.Word} (i : ℕ) (x : Formalism.MainNotions.product_first_zeroth_parts.Vl D u i),
    ∃ (r : NumberField.RingOfIntegers D.what₂.LL),
      r ≠ (0 : NumberField.RingOfIntegers D.what₂.LL) ∧
        r • x ∈
          ((D.fm u).lat
              i).L := by
  intro D u i x
  have hx : x ∈ Submodule.span D.what₂.LL (((D.fm u).lat i).L : Set ((D.fm u).lat i).V) := by
    rw [((D.fm u).lat_good i).2.2]
    exact Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.what₂.LL)) D.what₂.LL _ _ hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, nonZeroDivisors.ne_zero t.2, ht⟩
end

