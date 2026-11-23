module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMuLineNormEq
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HSClosing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqZeroOfSecTraceMulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualCurvePoint
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagRatioTrdeg
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0010

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ChartVel
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {d : ℕ}

def IsChartVel (M : CxModel P d) (e : OpenPartialHomeomorph M.Xc (Fin d → ℂ)) (z w : (Σ k, ι k) → ℂ)
    (v : Fin d → ℂ) : Prop :=
  ∃ γ : ℂ → (Σ k, ι k) → ℂ, γ 0 = z ∧ HasDerivAt γ w 0 ∧
    (∀ᶠ s in 𝓝 (0 : ℂ), DifferentiableAt ℂ γ s ∧ γ s ∈ mcPts P) ∧
    HasDerivAt (fun s => e (M.proj (γ s))) v 0

namespace Line

open GroundTheory.Heights₂.Heights (CP)

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ContDiffAtSqrtQuotNormSq
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped Matrix ComplexOrder

namespace MuWeightChartSmooth

section Calculus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞} {x : F}

theorem contDiffAt_det {m : Type*} [Fintype m] [DecidableEq m] {M : F → Matrix m m ℂ}
    (hM : ∀ i j, ContDiffAt ℝ n (fun w => M w i j) x) : ContDiffAt ℝ n (fun w => (M w).det) x := by
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hM _ _)

theorem contDiffAt_star {f : F → ℂ} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun w => star (f w)) x :=
  (Complex.conjCLE.contDiff.contDiffAt).comp x hf

theorem contDiffAt_zpow_of_ne {f : F → ℝ} (hf : ContDiffAt ℝ n f x) (h0 : f x ≠ 0) (m : ℤ) :
    ContDiffAt ℝ n (fun w => f w ^ m) x := by
  rcases m with m | m
  · simpa using hf.pow m
  · simp only [zpow_negSucc]
    exact (hf.pow (m + 1)).fun_inv (pow_ne_zero _ h0)

theorem contDiffAt_sandwich {m : Type*} [Fintype m] {A B : F → Matrix m m ℂ}
    (hA : ∀ i j, ContDiffAt ℝ n (fun w => A w i j) x) (hB : ∀ i j, ContDiffAt ℝ n (fun w => B w i j) x)
    (i j : m) : ContDiffAt ℝ n (fun w => ((A w)ᴴ * B w * A w) i j) x := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact ContDiffAt.sum fun k _ =>
    (ContDiffAt.sum fun l _ => (contDiffAt_star (hA l i)).mul (hB l k)).mul (hA k j)

end Calculus

section Chart

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]


end Chart

end MuWeightChartSmooth

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.GenMat0FrEqMap
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem genMat0Fr_eq_map (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (τ : Ψ) :
    genMat0Fr F Ψ n j τ = (algebraMap (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n)).mapMatrix
      (Matrix.of fun (p q : Fin n) => if (p : ℕ) < j ∧ j ≤ (q : ℕ) then 0 else
        (X (τ, p, q) : MvPolynomial (Ψ × Fin n × Fin n) F)) := by
  ext p q
  simp only [genMat0Fr, genMatFr, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem GenLeadMinor0NeZero.full : GenLeadMinor0NeZero.Statement := by
  intro F _ Ψ n j τ a
  rw [genMat0Fr_eq_map, ← leadMinor_map]
  refine (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n))).2 ?_
  intro h0
  have h1 := congrArg (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)) h0
  rw [leadMinor_map, map_zero] at h1
  have hP : (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)).mapMatrix
      (Matrix.of fun (p q : Fin n) => if (p : ℕ) < j ∧ j ≤ (q : ℕ) then 0 else
        (X (τ, p, q) : MvPolynomial (Ψ × Fin n × Fin n) F)) = 1 := by
    ext p q
    by_cases hc : (p : ℕ) < j ∧ j ≤ (q : ℕ)
    · have hpq : p ≠ q := by
        rintro rfl
        obtain ⟨hc₁, hc₂⟩ := hc
        omega
      simp [hc, hpq]
    · simp [hc, Matrix.one_apply]
  rw [hP, leadMinor_one] at h1
  exact one_ne_zero h1

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.MCoordIdealGenericPointEq
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentDataEquivalence

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Boundary

theorem mcPts_torus {B : Ideal (MRing ι)} (hB : IsMultiHomogIdeal B) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts B)
    {c : K → ℂ} (hc : ∀ k, c k ≠ 0) : torusSmul c z ∈ mcPts B := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  obtain ⟨S, hS, rfl⟩ := hB
  induction hf using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨a, ha⟩ := hS s hs
    rw [eval_map]
    unfold torusSmul
    rw [IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint.eval₂_smul_homog s a ha, ← eval_map, hz.2 s (Ideal.subset_span hs),
      mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), eval_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_eq_mul, map_mul, eval_mul, hx, mul_zero]

end Boundary

section Ample

end Ample

end GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentDataEquivalence
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagArithVar
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter GroundTheory.Heights₂.Heights.CoordinateConeArithVar

namespace FlagArithVar

variable (Ψ : Type) (N : ℕ)

theorem yFl_eq (q : FlBlock Ψ N) (A : FlIdx Ψ N q) :
    yFl Ψ N ⟨q, A⟩ = ((genMatFr ℚ Ψ N q.1).submatrix (Fin.castLE (step_le q.2)) A.1).det := by
  rw [yFl, RingHom.map_det]
  congr 1

def leadIdx (q : FlBlock Ψ N) : FlIdx Ψ N q := ⟨Fin.castLE (step_le q.2), Fin.strictMono_castLE _⟩

theorem yFl_lead (q : FlBlock Ψ N) : yFl Ψ N ⟨q, leadIdx Ψ N q⟩ = GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor (genMatFr ℚ Ψ N q.1) q.2 := by
  rw [yFl_eq, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor, pivotMinor]
  congr 2
  funext c
  apply Fin.ext
  have := c.isLt
  simp only [leadIdx, Fin.val_castLE, pivotCols]
  split_ifs with h
  · rfl
  · simp only [Fin.val_castLE]; omega

theorem yFl_eq_flagMinor (q : FlBlock Ψ N) (A : FlIdx Ψ N q) :
    yFl Ψ N ⟨q, A⟩ = flagMinor (genMatFr ℚ Ψ N q.1) q.2
      ⟨Finset.univ.image A.1, by rw [Finset.card_image_of_injective _ A.2.injective, Finset.card_fin]⟩ := by
  rw [yFl_eq, flagMinor]
  congr 2
  exact Finset.orderEmbOfFin_unique _ (fun x => Finset.mem_image_of_mem _ (Finset.mem_univ x)) A.2

theorem flagMinor_eq_yFl (τ : Ψ) (i : Fin (N - 1)) (S : PluckerBlocks N N i) :
    flagMinor (genMatFr ℚ Ψ N τ) i S = yFl Ψ N ⟨(τ, i), ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩ := by
  rw [yFl_eq, flagMinor]

theorem coneRatios_eq : coneRatios (yFl Ψ N) (leadIdx Ψ N) = Set.range (flagMinorRatio ℚ Ψ N) := by
  ext x
  constructor
  · rintro ⟨⟨q, A⟩, rfl⟩
    refine ⟨(q.1, ⟨q.2, ⟨Finset.univ.image A.1,
      by rw [Finset.card_image_of_injective _ A.2.injective, Finset.card_fin]⟩⟩), ?_⟩
    show flagMinor _ _ _ / GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor _ _ = yFl Ψ N ⟨q, A⟩ / yFl Ψ N ⟨q, leadIdx Ψ N q⟩
    rw [yFl_lead, yFl_eq_flagMinor]
  · rintro ⟨⟨τ, i, S⟩, rfl⟩
    refine ⟨⟨(τ, i), ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩, ?_⟩
    show yFl Ψ N _ / yFl Ψ N ⟨(τ, i), leadIdx Ψ N (τ, i)⟩ = flagMinor _ _ _ / GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor _ _
    rw [yFl_lead, flagMinor_eq_yFl]

theorem toSubfield_adjoin_rat {E : Type} [Field E] [Algebra ℚ E] (s : Set E) :
    (IntermediateField.adjoin ℚ s).toSubfield = Subfield.closure s := by
  rw [IntermediateField.adjoin_toSubfield]
  refine le_antisymm (Subfield.closure_le.2 (Set.union_subset ?_ Subfield.subset_closure))
    (Subfield.closure_mono Set.subset_union_right)
  rintro _ ⟨q, rfl⟩
  rw [eq_ratCast]
  exact SubfieldClass.ratCast_mem _ q

theorem trdeg_int_adjoin {E : Type} [Field E] [Algebra ℚ E] (s : Set E) :
    Algebra.trdeg ℤ (IntermediateField.adjoin ℚ s) = Algebra.trdeg ℤ (Subfield.closure s) := by
  rw [← (RingEquiv.subfieldCongr (toSubfield_adjoin_rat s)).toIntAlgEquiv.trdeg_eq]
  exact AlgEquiv.trdeg_eq (RingEquiv.refl _).toIntAlgEquiv

theorem trdeg_int_eq_rat {L : Type} [Field L] (I : Algebra ℚ L) :
    Algebra.trdeg ℤ L = @Algebra.trdeg ℚ L _ _ I := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  have : FaithfulSMul ℤ ℚ := (faithfulSMul_iff_algebraMap_injective ℤ ℚ).mpr Int.cast_injective
  have : FaithfulSMul ℚ L := (faithfulSMul_iff_algebraMap_injective ℚ L).mpr (algebraMap ℚ L).injective
  rw [← trdeg_add_eq ℤ ℚ (A := L), trdeg_eq_zero, zero_add]

theorem trdeg_closure_of_rat {E : Type} [Field E] {iQ : Algebra ℚ E} (s : Set E) {c : Cardinal}
    (h : @Algebra.trdeg ℚ (IntermediateField.adjoin ℚ s) _ _ (IntermediateField.adjoin ℚ s).algebra' = c) :
    Algebra.trdeg ℤ (Subfield.closure s) = c := by
  rw [← trdeg_int_adjoin, trdeg_int_eq_rat (IntermediateField.adjoin ℚ s).algebra']
  exact h

end FlagArithVar


open FlagArithVar in
theorem FlagArithVar.proof : FlagArithVar.Statement := by
  intro Ψ _ _ _ N hN
  have hc : ∀ q, yFl Ψ N ⟨q, leadIdx Ψ N q⟩ ≠ 0 := fun q => by
    rw [yFl_lead]; exact GenLeadMinorNeZero.full ℚ Ψ N q.1 q.2
  have hK : Nonempty (FlBlock Ψ N) := ⟨(Classical.arbitrary Ψ, ⟨0, by omega⟩)⟩
  have hhor : IsHorizontal (PFl Ψ N) := horizontal (yFl Ψ N)
  refine ⟨hK, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal (yFl Ψ N), relevant (yFl Ψ N) _ hc⟩, hhor, ?_⟩
  have htr := ConeTrdeg.full _ (FlIdx Ψ N) (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField (yFl Ψ N) (leadIdx Ψ N))
    (ratioPtL (yFl Ψ N) (leadIdx Ψ N)) (birational (yFl Ψ N) _ hc)
    (fun k ↦ ⟨leadIdx Ψ N k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL (yFl Ψ N) _ hc]; exact hhor)
  have hL : Algebra.trdeg ℤ (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField (yFl Ψ N) (leadIdx Ψ N)) = ((dimFl Ψ N : ℕ) : Cardinal) := by
    have h := trdeg_closure_of_rat _ (FlagRatioTrdeg.full ℚ Ψ N)
    rw [GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField, coneRatios_eq, trdeg_int_adjoin]
    exact h
  rw [mCoordIdeal_ratioPtL (yFl Ψ N) _ hc, hL] at htr
  have : (PFl Ψ N).IsPrime := RingHom.ker_isPrime _
  have hA := IntDomainDim.full (MRing (FlIdx Ψ N) ⧸ PFl Ψ N) (algebraMap_injective _ hhor)
  rw [hA]
  unfold PFl
  rw [htr, ← Nat.cast_add, Cardinal.toENat_nat]
  push_cast
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagRatioTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem HodgeFlagRatioTrdeg.proof (h₂ : HodgeFlagRatioFieldEq.Statement) (h₃ : HodgeFlagMinorTrdeg.Statement) :
    HodgeFlagRatioTrdeg.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B c hc
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  let cX : ∀ k, ι k := fun k => c (Sum.inl k)
  have hyX : ∀ p : Σ k, ι k, Pl.flagGenericPoint B ⟨Sum.inl p.1, p.2⟩ = algebraMap Ω Pl.ΩY (D.y p) :=
    fun p => PlueckerData.ofΩ_eq Pl _
  have hcX : ∀ k, D.y ⟨k, cX k⟩ ≠ 0 := fun k h => hc (Sum.inl k) (by
    rw [hyX ⟨k, cX k⟩, h, map_zero])

  have hbase : Set.range (algebraMap Ω Pl.ΩY) ⊆ Subfield.closure (coneRatios (Pl.flagGenericPoint B) c) := by
    have hle : Subfield.map (algebraMap Ω Pl.ΩY) (Subfield.closure (coneRatios D.y cX)) ≤
        Subfield.closure (coneRatios (Pl.flagGenericPoint B) c) := by
      rw [Subfield.map_le_iff_le_comap, Subfield.closure_le]
      rintro _ ⟨p, rfl⟩
      refine Subfield.subset_closure ⟨⟨Sum.inl p.1, p.2⟩, ?_⟩
      show Pl.flagGenericPoint B ⟨Sum.inl p.1, p.2⟩ / Pl.flagGenericPoint B ⟨Sum.inl p.1, cX p.1⟩ =
        algebraMap Ω Pl.ΩY (D.y p / D.y ⟨p.1, cX p.1⟩)
      rw [map_div₀, hyX p, hyX ⟨p.1, cX p.1⟩]
    rintro _ ⟨x, rfl⟩
    refine hle ⟨x, ?_, rfl⟩
    rw [BirationalRatioClosure.full K ι Ω D.y cX D.birational hcX]
    trivial
  set Ef := IntermediateField.adjoin Ω (coneRatios (Pl.flagGenericPoint B) c)
  have hsub : Ef.toSubfield = Subfield.closure (coneRatios (Pl.flagGenericPoint B) c) := by
    rw [IntermediateField.adjoin_toSubfield]
    exact le_antisymm (Subfield.closure_le.2 (Set.union_subset hbase Subfield.subset_closure))
      (Subfield.closure_mono Set.subset_union_right)
  have e : Subfield.closure (coneRatios (Pl.flagGenericPoint B) c) ≃+* Ef :=
    (RingEquiv.subfieldCongr hsub).symm.trans (RingEquiv.refl Ef)
  have hE : Algebra.trdeg ℤ (Subfield.closure (coneRatios (Pl.flagGenericPoint B) c)) = Algebra.trdeg ℤ Ef :=
    (AlgEquiv.ofRingEquiv (f := e) fun x => by rw [eq_intCast, eq_intCast, map_intCast]).trdeg_eq
  rw [hE]
  have : FaithfulSMul ℤ Ω := (faithfulSMul_iff_algebraMap_injective ℤ Ω).mpr Int.cast_injective
  have : FaithfulSMul Ω Ef := (faithfulSMul_iff_algebraMap_injective Ω Ef).mpr (algebraMap Ω Ef).injective
  rw [← trdeg_add_eq ℤ Ω (A := Ef), FnFieldTrdeg.full K ι Ω D.y D.n D.birational D.arith,
    ← (IntermediateField.equivOfEq (h₂ II Ψ K ι Ω E D Pl H B c hc)).symm.trdeg_eq,
    h₃ Ω Ψ D.N D.j D.j_le_N]
  rw [← Nat.cast_add]
  rfl

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagSpan
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem HodgeFlagSpan.full : HodgeFlagSpan.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B τ i
  classical
  let Be : Module.Basis (Fin D.N) Ω (E τ) := Module.Basis.mk (B.e_indep τ) (B.e_span τ).ge
  have hcoe : ⇑Be = B.e τ := Module.Basis.coe_mk _ _

  have hgen : Submodule.span Ω (Set.range (Pl.gen τ i)) = ⊤ := by
    choose cX hcX using D.arith.2.1.2.2
    have hy : ∀ k, D.y ⟨k, cX k⟩ ≠ 0 := by
      intro k h0
      apply hcX k
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
    have hseg : segreCoord D.y cX ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
    obtain ⟨M, f, cc, -, -, hsum, hPr⟩ := Pl.generates τ i cX hseg
    have hM : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h | h
      · subst h
        simp at hsum
      · exact h
    obtain ⟨b, -, hspan, hA⟩ := hPr ⟨0, hM⟩
    have hli : LinearIndependent Ω b :=
      linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
        (by rw [Module.finrank_eq_card_basis Be])
    let Bb : Module.Basis (Fin D.N) Ω (E τ) := Module.Basis.mk hli hspan.ge
    have hBb : ⇑Bb = b := Module.Basis.coe_mk _ _
    refine PlueckerSpan.span_eq_top_of_dual Bb (Pl.gen τ i) fun A hA0 => ?_
    obtain ⟨a, -, ha⟩ := hA A hA0
    refine ⟨fun m => a m * chartMono D.y cX (-Pl.bdeg τ i), fun A' hA' => ?_⟩
    rw [← ha A' hA', hBb]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring

  let P : Module.Dual Ω (⋀[Ω]^((i : ℕ) + 1) (E τ)) →ₗ[Ω] Pl.ΩY :=
    { toFun := fun φ => ∑ c : Fin ((i : ℕ) + 1) → Fin D.N,
        (∏ a, Pl.gvar0 τ (headIdx (step_le i) a) (c a)) *
          algebraMap Ω Pl.ΩY (φ (exteriorPower.ιMulti Ω _ (B.e τ ∘ c)))
      map_add' := fun φ ψ => by
        simp only [LinearMap.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
      map_smul' := fun x φ => by
        simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring }
  have hPpl : ∀ m, P (Pl.gen τ i m) = Pl.pluecker0 B τ i m := by
    intro m
    simp only [P, LinearMap.coe_mk, AddHom.coe_mk, PlueckerData.pluecker0, PlueckerData.ofΩ_eq]

  have hPexp : ∀ φ, P φ = ∑ T : Set.powersetCard (Fin D.N) ((i : ℕ) + 1),
      algebraMap Ω Pl.ΩY (φ (Be.exteriorPower _ T)) *
        flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i ⟨(T : Finset (Fin D.N)), Set.powersetCard.card_eq T⟩ := by
    intro φ
    have h := PlueckerSpan.sum_prod_mul_apply_eq (R := Pl.ΩY) Be
      (Matrix.of fun a b => Pl.gvar0 τ (headIdx (step_le i) a) b) φ
    rw [hcoe] at h
    exact h.trans (Finset.sum_congr rfl fun T _ => rfl)

  have hrange : LinearMap.range P =
      Submodule.span Ω (Set.range (flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i)) := by
    apply le_antisymm
    · rintro _ ⟨φ, rfl⟩
      rw [hPexp]
      refine Submodule.sum_mem _ fun T _ => ?_
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨S, rfl⟩
      let T : Set.powersetCard (Fin D.N) ((i : ℕ) + 1) := ⟨S.1, Set.powersetCard.mem_iff.2 S.2⟩
      refine ⟨(Be.exteriorPower _).coord T, ?_⟩
      rw [hPexp, Finset.sum_eq_single T]
      · rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, map_one, one_mul]
      · intro T' _ hT'
        rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne (Ne.symm hT'),
          map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ T) h

  have hpl : Set.range (Pl.pluecker0 B τ i) = P '' Set.range (Pl.gen τ i) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun m => (hPpl m).symm)
  rw [hpl, ← Submodule.map_span, hgen, Submodule.map_top, hrange]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

