module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerDiagonalBlockAsGLMemIntegralGeneralLinear
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0082
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanLogPeriodConjugatesEqChowlaSelberg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterTransferInvariantPairing
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeTransfer

theorem transfer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ t : ℕ, Fintype.card D' = Fintype.card D + t → ∀ (ξ μS μT : kˣ →* ℂˣ), IsTame ξ → IsUnram (μS * ξ⁻¹) → IsUnram (μT * ξ⁻¹) → ∀ (W : Submodule ℂ (Matrix (A ⊕ D') (A ⊕ D) k → ℂ)) (hW : ∀ g h, ∀ u ∈ W, omTwo μS μT g h u ∈ W) (hΦ : datum ξ⁻¹ ∈ W) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (A ⊕ D) k) X) (x : X) (B : Multiset ℂˣ), IsGen ρ ξ ϖ B x → ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (GL (A ⊕ D') k) X') (b : W →ₗ[ℂ] X →ₗ[ℂ] X'), (∀ g h (u : W) y, b ⟨omTwo μS μT g h u, hW g h u u.2⟩ (ρ g y) = ρ' h (b u y)) → IsGen ρ' ξ ϖ (B.map (· * (μS ϖ * (μT ϖ)⁻¹)) + segL ϖ (μS ϖ) t) (b ⟨datum ξ⁻¹, hΦ⟩ x) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ t hD' ξ μS μT hξ hS hT W hW hΦ X _ _ ρ x B hx X' _ _ ρ' b hb
  have hξi : IsTame ξ⁻¹ := fun y hy => by rw [MonoidHom.inv_apply, hξ y hy, inv_one]
  have hρ1 : ∀ y : X, ρ 1 y = y := fun y => by rw [map_one, Module.End.one_apply]
  obtain ⟨hx1, hx2, hx3⟩ := hx
  refine ⟨?_, ?_, fun s => ?_⟩
  · intro j hj d hd
    have h1 := hb 1 j ⟨datum ξ⁻¹, hΦ⟩ x
    rw [hρ1] at h1
    rw [← h1]
    have e : (⟨omTwo μS μT 1 j (datum ξ⁻¹), hW 1 j _ hΦ⟩ : W) = (ξ d : ℂ) • (⟨datum ξ⁻¹, hΦ⟩ : W) :=
      Subtype.ext (GlobalTheory.DatumEigenLeft.omTwo_datum_inv k A D D' ξ μS μT hξ hS j hj d hd)
    rw [e, map_smul, LinearMap.smul_apply]
  · simp [segL, hx2, hD']

  · intro R' d' hR'
    obtain ⟨hr1, hr2⟩ := GlobalTheory.ParHeckeReps.exists_reps_both k A D
    obtain ⟨-, hr2'⟩ := GlobalTheory.ParHeckeReps.exists_reps_both k A D'
    choose RR dd hRR using hr1
    choose RK hRK using hr2
    obtain ⟨RK', hRK'⟩ := hr2' (torusElt k D' ϖ (indic s))
    have hsn : ∀ n : ℕ, ∃ s : Finset D, n ≤ Fintype.card D → s.card = n := fun n => by
      by_cases h : n ≤ Fintype.card D
      · obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset D)) (by simpa using h)
        exact ⟨s, fun _ => hs⟩
      · exact ⟨∅, fun h' => absurd h' h⟩
    choose sn hsn using hsn
    have hq : (0 : ℝ) < (resCard k : ℝ) := by
      have : 0 < Nat.card 𝓀[k] := Nat.card_pos
      unfold resCard; exact_mod_cast this
    have hsq : ((Real.sqrt (resCard k) : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.2 hq).ne'
    set Φw : W := ⟨datum ξ⁻¹, hΦ⟩ with hΦw
    set C : ℂ := (μS ϖ : ℂ) ^ s.card * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (s.card * (Fintype.card A + Fintype.card D)) with hC
    set cn : ℕ → ℂ := fun n => if n ≤ s.card then ((resCard k ^ (n * (t - (s.card - n))) * Formalism.L2.Col.gaussBin (resCard k) t (s.card - n) : ℕ) : ℂ) else 0 with hcn
    set den : ℕ → ℂ := fun n => (μT ϖ : ℂ) ^ n * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (n * (Fintype.card A + Fintype.card D')) with hden
    have hden0 : ∀ n, den n ≠ 0 := fun n => mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (pow_ne_zero _ hsq)
    have key : ∑ j ∈ R', (((ξ (d' j))⁻¹ : ℂˣ) : ℂ) • (⟨omTwo μS μT 1 (j * mtor ϖ (indic s)) (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W) =
        C • ∑ n ∈ Finset.range (Fintype.card D + 1), (cn n * (den n)⁻¹) •
            ∑ j ∈ RR (mtor ϖ (-indic (sn n))), (ξ (dd (mtor ϖ (-indic (sn n))) j) : ℂ) •
              (⟨omTwo μS μT (j * mtor ϖ (-indic (sn n))) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W) := by
      apply Subtype.ext
      funext y
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hT1 := GlobalTheory.ParHeckeTarget.sum_reps_datum_eq k A D D' ϖ hϖ ξ⁻¹ hξi s R' d' hR' RK' hRK' y
      have hU := GlobalTheory.ParHecke.heckeIdentity_integral k D D' ϖ hϖ t hD' s RK' hRK' sn (fun n => RK (torusElt k D ϖ (-indic (sn n))))
        (fun n hn => ⟨hsn n hn, hRK _⟩) (schur y)
      have hL : ∑ j ∈ R', (((ξ (d' j))⁻¹ : ℂˣ) : ℂ) * omTwo μS μT 1 (j * mtor ϖ (indic s)) (datum ξ⁻¹) y =
          C * (datum ξ⁻¹ y * ∑ g ∈ RK', intInd (((g⁻¹ : GL D' k)).1 * schur y)) := by
        have e2 : datum ξ⁻¹ y * ∑ g ∈ RK', intInd (((g⁻¹ : GL D' k)).1 * schur y) =
            ∑ g ∈ RK', liftS ξ⁻¹ (fun z => intInd ((g⁻¹).1 * z)) y := by
          rw [Finset.mul_sum]; rfl
        rw [e2, ← hT1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [GlobalTheory.TorusLeft.omTwo_torusLeft k A D D' ϖ hϖ ξ μS μT hS s j (hR'.1 j hj).1]
        simp only [MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hC]
        field_simp
      have hR : ∀ n ∈ Finset.range (Fintype.card D + 1),
          (cn n * (den n)⁻¹) * ∑ j ∈ RR (mtor ϖ (-indic (sn n))), (ξ (dd (mtor ϖ (-indic (sn n))) j) : ℂ) *
              omTwo μS μT (j * mtor ϖ (-indic (sn n))) 1 (datum ξ⁻¹) y =
            cn n * (datum ξ⁻¹ y * ∑ g ∈ RK (torusElt k D ϖ (-indic (sn n))), intInd (schur y * g.1)) := by
        intro n hn
        have hc := hsn n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))
        have e2 : datum ξ⁻¹ y * ∑ g ∈ RK (torusElt k D ϖ (-indic (sn n))), intInd (schur y * g.1) =
            ∑ g ∈ RK (torusElt k D ϖ (-indic (sn n))), liftS ξ⁻¹ (fun z => intInd (z * g.1)) y := by
          rw [Finset.mul_sum]; rfl
        rw [e2, ← GlobalTheory.ParHeckeSource.sum_reps_datum_eq k A D D' ϖ hϖ ξ⁻¹ hξi (sn n) _ _ (hRR _) _ (hRK _) y, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [GlobalTheory.TorusRightScalar.torusRight k A D D' ϖ hϖ ξ μS μT hT (sn n) j ((hRR _).1 j hj).1, hc]
        have := hden0 n
        simp only [MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hden] at this ⊢
        field_simp
      rw [hL, hU, Finset.sum_congr rfl hR]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    have lhs : ∑ j ∈ R', (((ξ (d' j))⁻¹ : ℂˣ) : ℂ) • ρ' (j * mtor ϖ (indic s)) (b Φw x) =
        b (∑ j ∈ R', (((ξ (d' j))⁻¹ : ℂˣ) : ℂ) • (⟨omTwo μS μT 1 (j * mtor ϖ (indic s)) (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W)) x := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, LinearMap.smul_apply, ← hb 1 _ Φw x, hρ1]
    have e4 : ∀ n ∈ Finset.range (Fintype.card D + 1),
        b ((cn n * (den n)⁻¹) • ∑ j ∈ RR (mtor ϖ (-indic (sn n))), (ξ (dd (mtor ϖ (-indic (sn n))) j) : ℂ) •
              (⟨omTwo μS μT (j * mtor ϖ (-indic (sn n))) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W)) x =
          (cn n * (den n)⁻¹ * genVal (resCard k) (Fintype.card A) (Fintype.card D) B n) • b Φw x := by
      intro n hn
      have hc := hsn n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply]
      simp_rw [map_smul, LinearMap.smul_apply]
      rw [GlobalTheory.ParHeckeTransfer.sum_eq_genVal k A D D' ϖ ξ μS μT hξ hT W hW hΦ X ρ x B ⟨hx1, hx2, hx3⟩ X' ρ' b hb (sn n) _ _ (hRR _), hc, smul_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [lhs, key, map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply, Finset.sum_congr rfl e4,
      ← Finset.sum_smul, smul_smul]
    congr 1
    have hN := GlobalTheory.ParHecke.StringEig.genVal_add_segL k ϖ hϖ (Fintype.card A) (Fintype.card D) t s.card B (μS ϖ) (μT ϖ) hx2
      (by rw [← hD']; exact Finset.card_le_univ s)
    rw [show Fintype.card D' = Fintype.card D + t from hD']
    rw [hN, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hC, hcn, hden, hD']
    ring

end GlobalTheory.ParHeckeTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanLogCovolumeConjugateLatticesEq
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.MeanLogArea

theorem mean_log_area : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) / (Module.finrank ℚ M : ℝ) = Real.log Real.pi + ClassMeanPeriods.classMeanValue D := by
  intro D cc δ M _ t hS
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hmean := GlobalTheory.PeriodMean.mean_log_period D (GlobalTheory.InducedType.induced_type D).1 cc δ hc M
    hM.2.1 hM.2.2
  have hpos : ∀ ρ : M →ₐ[ℚ] ℂ, 0 < area (lamConj M ρ (lamOf D cc δ)) :=
    fun ρ => GlobalTheory.Glob.area_lamConj_pos hc hM ρ
  have hcard : (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) = (Module.finrank ℚ M : ℝ) := by
    exact_mod_cast AlgHom.card ℚ M ℂ
  have hn : (Module.finrank ℚ M : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := M)).ne'
  have hsplit : (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) =
      (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)) / Real.pi)) +
        (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) * Real.log Real.pi := by
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Real.log_div (hpos ρ).ne' Real.pi_pos.ne']
    ring
  rw [hsplit, add_div, hcard, mul_div_cancel_left₀ _ hn]
  unfold ClassMeanPeriods.classMeanValue
  rw [hmean]
  ring

end GlobalTheory.MeanLogArea
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnn
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

variable {D : D7}

open Matrix

theorem Tm_row_sub (A : HSp D) (μ : D.host.E) (a : Fin A.rank) :
    (fun k => Tm A μ (finSumFinEquiv (Sum.inl a)) k - Tm A μ (finSumFinEquiv (Sum.inr a)) k) =
      Pi.single (finSumFinEquiv (Sum.inr a)) μ := by
  funext k
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
  simp only [Pi.single_apply, EmbeddingLike.apply_eq_iff_eq]
  rcases s with j | j
  · simp only [Tm, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, GlobalTheory.Core.Rk.SWLaw.dblDec,
      GlobalTheory.Core.Rk.SWLaw.stackRows, fromRows_apply_inl, fromRows_apply_inr, sub_self, reduceCtorEq, if_false]
  · simp only [Tm, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, GlobalTheory.Core.Rk.SWLaw.dblDec,
      GlobalTheory.Core.Rk.SWLaw.stackRows, Matrix.smul_apply, fromRows_apply_inl, fromRows_apply_inr, Matrix.neg_apply,
      Matrix.one_apply, Sum.inr.injEq, smul_eq_mul]
    by_cases h : j = a
    · subst h
      simp only [if_true]
      have h2 : (2 : D.host.E) ≠ 0 := two_ne_zero
      field_simp
      ring
    · simp [h, Ne.symm h]

end GlobalTheory.StdUnn

namespace GlobalTheory.StdUnn

variable {D : D7}

open Matrix

theorem rat_Tm_mulVec_sub (A : HSp D) (μ : D.host.E) (w : Fin (A.rank + A.rank) → AE D) (a : Fin A.rank) :
    (rat (Tm A μ) *ᵥ w) (finSumFinEquiv (Sum.inl a)) - (rat (Tm A μ) *ᵥ w) (finSumFinEquiv (Sum.inr a)) =
      incA D μ * w (finSumFinEquiv (Sum.inr a)) := by
  have hrow := Tm_row_sub A μ a
  calc _ = ∑ k, incA D ((Pi.single (finSumFinEquiv (Sum.inr a)) μ : Fin (A.rank + A.rank) → D.host.E) k) * w k := by
        rw [mulVec, mulVec, dotProduct, dotProduct, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hk : Tm A μ (finSumFinEquiv (Sum.inl a)) k - Tm A μ (finSumFinEquiv (Sum.inr a)) k =
            (Pi.single (finSumFinEquiv (Sum.inr a)) μ : Fin (A.rank + A.rank) → D.host.E) k := congrFun hrow k
        rw [← hk, map_sub, sub_mul]
        rfl
    _ = _ := by
        rw [Finset.sum_eq_single (finSumFinEquiv (Sum.inr a)) (fun k _ hk => by rw [Pi.single_eq_of_ne hk, map_zero, zero_mul])
          (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same]

theorem rat_Tm_mulVec_mem_diagSub_iff (A : HSp D) {μ : D.host.E} (hμ : IsSkew μ) (w : Fin (A.rank + A.rank) → AE D) :
    rat (Tm A μ) *ᵥ w ∈ diagSub (AE D) finSumFinEquiv ↔ w ∈ upperHalf D A.rank := by
  have hu : IsUnit (incA D μ) := (isUnit_iff_ne_zero.2 hμ.1).map _
  simp only [diagSub, upperHalf, LinearMap.mem_eqLocus, LinearMap.mem_ker, funext_iff, LinearMap.funLeft_apply,
    Function.comp_apply, Pi.zero_apply]
  exact forall_congr' fun a => by rw [← sub_eq_zero, rat_Tm_mulVec_sub, hu.mul_right_eq_zero]

theorem exists_rat_Tm_mulVec_eq (A : HSp D) {μ : D.host.E} (hμ : IsSkew μ) (v : Fin (A.rank + A.rank) → AE D)
    (hv : v ∈ diagSub (AE D) finSumFinEquiv) : ∃ w ∈ upperHalf D A.rank, rat (Tm A μ) *ᵥ w = v := by
  have hG : IsUnit A.gram.det := (gram_det_ne A).isUnit
  let x : Fin A.rank → AE D := fun a => v (finSumFinEquiv (Sum.inl a))
  let w : Fin (A.rank + A.rank) → AE D := fun k => Sum.elim (rat A.gram *ᵥ x) 0 (finSumFinEquiv.symm k)
  have hw : w ∈ upperHalf D A.rank := by
    simp only [upperHalf, LinearMap.mem_ker, funext_iff, LinearMap.funLeft_apply, Function.comp_apply,
      Pi.zero_apply, w, Equiv.symm_apply_apply, Sum.elim_inr, implies_true]
  have hv' : ∀ a, v (finSumFinEquiv (Sum.inl a)) = v (finSumFinEquiv (Sum.inr a)) := by
    simpa only [diagSub, LinearMap.mem_eqLocus, funext_iff, LinearMap.funLeft_apply, Function.comp_apply] using hv
  have hl : ∀ a, (rat (Tm A μ) *ᵥ w) (finSumFinEquiv (Sum.inl a)) = x a := fun a => by
    have h1 : rat (A.gram⁻¹) * rat A.gram = (1 : Mx D A.rank A.rank) := by
      rw [rat, rat, ← Matrix.map_mul, nonsing_inv_mul _ hG, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 := congrFun (congrArg (· *ᵥ x) h1) a
    simp only [← mulVec_mulVec, one_mulVec] at h2
    rw [← h2, mulVec, dotProduct, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
    simp only [w, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero, mulVec, dotProduct, rat, map_apply, Tm, submatrix_apply, id,
      fromCols_apply_inl, GlobalTheory.Core.Rk.SWLaw.dblDec, GlobalTheory.Core.Rk.SWLaw.stackRows, fromRows_apply_inl]
  refine ⟨w, hw, funext fun k => ?_⟩
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
  rcases s with a | a
  · exact hl a
  · have h3 := (rat_Tm_mulVec_mem_diagSub_iff A hμ w).2 hw
    simp only [diagSub, LinearMap.mem_eqLocus, funext_iff, LinearMap.funLeft_apply, Function.comp_apply] at h3
    rw [← h3 a, hl a, ← hv' a]

theorem mem_siegel_iff_chart_mem_P : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ →
    ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ g, g ∈ siegel A ↔ κ g ∈ P D A.rank := by
  intro D A μ hμ κ hκ g
  have hT : ∀ w, rat (Tm A μ) *ᵥ (mat (κ g) *ᵥ w) = mt (dblSp A) g *ᵥ (rat (Tm A μ) *ᵥ w) := fun w => by
    rw [mulVec_mulVec, mulVec_mulVec, hκ g]
  have hP : κ g ∈ P D A.rank ↔ ∀ w, w ∈ upperHalf D A.rank ↔ mat (κ g) *ᵥ w ∈ upperHalf D A.rank := Iff.rfl
  have hS : g ∈ siegel A ↔ ∀ v, v ∈ diagSub (AE D) finSumFinEquiv ↔
      mt (dblSp A) g *ᵥ v ∈ diagSub (AE D) finSumFinEquiv := Iff.rfl
  rw [hP]
  constructor
  · intro h w
    rw [← rat_Tm_mulVec_mem_diagSub_iff A hμ, ← rat_Tm_mulVec_mem_diagSub_iff A hμ, hT]
    exact hS.1 h _
  · intro h
    refine Subgroup.mem_comap.2 (mem_stabGL_diagSub.2 (keepsDiag_of_mulVec fun v hv => ?_))
    obtain ⟨w, hw, rfl⟩ := exists_rat_Tm_mulVec_eq A hμ v hv
    change mt (dblSp A) g *ᵥ _ ∈ _
    rw [← hT, rat_Tm_mulVec_mem_diagSub_iff A hμ]
    exact (h w).1 hw

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeStabilizerIffScaledFrameConj
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.StabFin

section General

variable {A R n : Type} [CommRing A] [CommRing R] [Algebra R A] [Fintype n] [DecidableEq n]

theorem mem_stab_conj {L S : Submodule R (n → A)} {b : GL n A} (h : ∀ y, y ∈ S ↔ b.1 *ᵥ y ∈ L) (x : GL n A) :
    x ∈ Formalism.UG.stabGL L ↔ b⁻¹ * x * b ∈ Formalism.UG.stabGL S := by
  have key : ∀ y, (b⁻¹ * x * b).1 *ᵥ y ∈ S ↔ x.1 *ᵥ (b.1 *ᵥ y) ∈ L := fun y => by
    rw [h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel, one_mul]
  constructor
  · intro hx y
    rw [key, h]
    exact hx _
  · intro hx y
    have h1 := hx ((b⁻¹).1 *ᵥ y)
    rw [key, h, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1
    exact h1


omit [CommRing R] [Algebra R A] in
theorem conj_eq_of_smul {m m' : GL n A} {w : A} (h : m.1 = w • m'.1) (z : GL n A) :
    m⁻¹ * z * m = m'⁻¹ * z * m' := by
  have hc : m * m'⁻¹ * z = z * (m * m'⁻¹) := by
    apply Units.ext
    have e : (m * m'⁻¹).1 = w • (1 : Matrix n n A) := by
      rw [Units.val_mul, h, Matrix.smul_mul, Units.mul_inv]
    rw [Units.val_mul _ z, Units.val_mul z, e, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  calc m⁻¹ * z * m = m⁻¹ * (z * (m * m'⁻¹)) * m' := by group
    _ = m⁻¹ * (m * m'⁻¹ * z) * m' := by rw [hc]
    _ = m'⁻¹ * z * m' := by group

end General

theorem mem_stab_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} {m : GL (Fin N) (Fv F v ⊗[F] E)} (h : ∀ i j, m.1 i j ∈ intLoc F E v)
    (h' : ∀ i j, (m⁻¹).1 i j ∈ intLoc F E v) : m ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
  have key : ∀ (M : Matrix (Fin N) (Fin N) (Fv F v ⊗[F] E)), (∀ i j, M i j ∈ intLoc F E v) →
      ∀ y, y ∈ latLoc F (stdLattice E N) v → M *ᵥ y ∈ latLoc F (stdLattice E N) v := fun M hM y hy =>
    mem_latLoc_stdLattice.2 fun i => show ∑ j, M i j * y j ∈ _ from
      sum_mem fun j _ => mul_mem (hM i j) (mem_latLoc_stdLattice.1 hy j)
  intro y
  refine ⟨key _ h y, fun hy => ?_⟩
  have h1 := key _ h' _ hy
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h1

theorem mem_stab_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)) (b M M' : GL (Fin N) (AF F ⊗[F] E)) (u : (AF F ⊗[F] E)ˣ), IsLatticeFrame Λ b → (∀ v i j, compFin F E v (M'.1 i j) ∈ intLoc F E v ∧ compFin F E v ((M'⁻¹).1 i j) ∈ intLoc F E v) → M.1 = (u : AF F ⊗[F] E) • M'.1 → ∀ (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin N) (Fv F v ⊗[F] E)), x ∈ Formalism.UG.stabGL (latLoc F Λ v) ↔ (Formalism.UG.bc (compFin F E v) (b * M))⁻¹ * x * Formalism.UG.bc (compFin F E v) (b * M) ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
  intro F E _ _ _ _ _ N Λ b M M' u hb hM' hM v x
  have hs : Formalism.UG.bc (compFin F E v) M' ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
    refine mem_stab_std (fun i j => (hM' v i j).1) (fun i j => ?_)
    rw [← map_inv]
    exact (hM' v i j).2
  have he : (Formalism.UG.bc (compFin F E v) M).1 =
      compFin F E v (u : AF F ⊗[F] E) • (Formalism.UG.bc (compFin F E v) M').1 := by
    ext i j
    change compFin F E v (M.1 i j) = compFin F E v (u : AF F ⊗[F] E) * compFin F E v (M'.1 i j)
    rw [hM, ← map_mul]
    rfl
  rw [mem_stab_conj (S := latLoc F (stdLattice E N) v) (b := Formalism.UG.bc (compFin F E v) b)
    (fun y => mem_latLoc_stdLattice.trans (hb v y)) x, map_mul, mul_inv_rev]
  set β := Formalism.UG.bc (compFin F E v) b
  have e : (Formalism.UG.bc (compFin F E v) M)⁻¹ * β⁻¹ * x * (β * Formalism.UG.bc (compFin F E v) M) =
      (Formalism.UG.bc (compFin F E v) M)⁻¹ * (β⁻¹ * x * β) * Formalism.UG.bc (compFin F E v) M := by group
  rw [e, conj_eq_of_smul he, Subgroup.mul_mem_cancel_right _ hs, Subgroup.mul_mem_cancel_left _ (inv_mem hs)]

end GlobalTheory.StdUnn.StabFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemUnitaryStandardIffConjSimilitude
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem mem_UJ_one_iff_conj_similitude :
    ∀ (R : Type) [CommRing R] (σ : R →+* R), (∀ x, σ (σ x) = x) → ∀ (N : ℕ) (M y : GL (Fin N) R) (r : Rˣ), Formalism.UG.cT σ M.1 * M.1 = (r : R) • 1 → (y ∈ Formalism.UG.UJ σ (1 : Matrix (Fin N) (Fin N) R) ↔ M⁻¹ * y * M ∈ Formalism.UG.UJ σ (1 : Matrix (Fin N) (Fin N) R)) := by
  intro R _ σ _ N M y r hM
  have hAB : M.1 * (M⁻¹).1 = 1 := Units.mul_inv M
  have hBA : (M⁻¹).1 * M.1 = 1 := Units.inv_mul M
  have h1 : Formalism.UG.cT σ M.1 = (r : R) • (M⁻¹).1 := by
    calc Formalism.UG.cT σ M.1 = Formalism.UG.cT σ M.1 * M.1 * (M⁻¹).1 := by
          rw [Matrix.mul_assoc, hAB, Matrix.mul_one]
      _ = (r : R) • (M⁻¹).1 := by rw [hM, Matrix.smul_mul, Matrix.one_mul]
  have h2 : (r : R) • (Formalism.UG.cT σ (M⁻¹).1 * (M⁻¹).1) = 1 := by
    rw [← Matrix.mul_smul, ← h1, ← Formalism.UG.cT_mul, hAB, Formalism.UG.cT_one]
  have key : Formalism.UG.cT σ (M⁻¹ * y * M).1 * 1 * (M⁻¹ * y * M).1
      = (M⁻¹).1 * (Formalism.UG.cT σ y.1 * 1 * y.1) * M.1 := by
    rw [Units.val_mul, Units.val_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, h1]
    calc (r : R) • (M⁻¹).1 * (Formalism.UG.cT σ y.1 * Formalism.UG.cT σ (M⁻¹).1) * 1 * ((M⁻¹).1 * y.1 * M.1)
        = (M⁻¹).1 * (Formalism.UG.cT σ y.1 * ((r : R) • (Formalism.UG.cT σ (M⁻¹).1 * (M⁻¹).1)) * y.1) * M.1 := by
          simp only [Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
      _ = _ := by rw [h2]
  show Formalism.UG.cT σ y.1 * 1 * y.1 = 1 ↔
    Formalism.UG.cT σ (M⁻¹ * y * M).1 * 1 * (M⁻¹ * y * M).1 = 1
  rw [key]
  constructor
  · intro h
    rw [h, Matrix.mul_one, hBA]
  · intro h
    calc Formalism.UG.cT σ y.1 * 1 * y.1
        = (M.1 * (M⁻¹).1) * (Formalism.UG.cT σ y.1 * 1 * y.1) * (M.1 * (M⁻¹).1) := by
          simp only [hAB, Matrix.one_mul, Matrix.mul_one]
      _ = M.1 * ((M⁻¹).1 * (Formalism.UG.cT σ y.1 * 1 * y.1) * M.1) * (M⁻¹).1 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, Matrix.mul_one, hAB]

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicityMapValueKFiniteMemCuspForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.ChainOnto.RealData.multiplicityMap_value_kFinite_mem_cuspForms : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D), V.SigOK → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ cA : GlobalTheory.Mem.Th.CptF V, GlobalTheory.Cusp.IsCartanFrame V cA ∧ (∀ τ, IsCartanInv (gramAt D V τ) (cart M τ)) ∧ (∀ τ, cA τ * cart M τ = Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * cA τ) ∧ ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ U ∈ Mult θ M J χ, ∀ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) → U v ∈ GlobalTheory.Cusp.A0 θ V cA := by
  intro D θ hθ V hV S M
  refine ⟨GlobalTheory.ChainOnto.RealData.sortedFrame M hV, GlobalTheory.ChainOnto.RealData.isCartanFrame_sortedFrame M hV,
    fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart M τ, fun τ => GlobalTheory.ChainOnto.RealData.sortedFrame_cart M hV τ, ?_⟩
  intro J χ U hU v hv
  induction hU using Submodule.span_induction with
  | mem T hT =>
    exact GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨hT.aut v, hT.cusp v⟩,
      GlobalTheory.ChainOnto.RealData.isKFinite_value θ hθ M hV hT v hv⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact (GlobalTheory.Cusp.A0 θ V _).smul_mem a hx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealRepresentationMovesRieszVectorFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem piU_rieszJ : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (s : X.B.I.Ginf), s ∈ Hinf X u → ∀ z z' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _), Formalism.L2.Forms.IsTr (Formalism.L2.SG.ColDict.sTil X tr.wt s) z z' → X.piU u s (rieszJ tr z) = rieszJ tr z' := by
  intro D X u F tr s hs z z' hz
  have hrep := X.piU_rep u
  have hS := hinf_le_sinf X u s hs
  have hSi := hinf_le_sinf X u _ ((Hinf X u).inv_mem hs)
  refine ext_inner_left ℂ fun η => ?_
  have hη : X.piU u s (X.piU u s⁻¹ η) = η := by
    rw [← ContinuousLinearMap.mul_apply, ← hrep.2.1 _ hS _ hSi, mul_inv_cancel, hrep.1]
    rfl
  rw [← hη, hrep.2.2.1 s hS, inner_rieszJ, inner_rieszJ, tr.J_eqv s hs _ z' z hz]

end GlobalTheory.Core.Mi
end

