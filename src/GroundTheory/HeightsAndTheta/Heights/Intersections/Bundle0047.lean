module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0046
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocLength
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

theorem SemilocLength.proof (h₁ : SemilocLengthSum.Statement) (h₂ : FibreDivSupp.Statement)
    (h₃ : regularityDehomogenization_holds.Statement) : SemilocLength.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s t α W E hv hP' y hPn hs ht hsP hW htW hy hE
  have := hP'.2.1.1
  have hfib := h₂ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW
  obtain ⟨-, N, hN, hsum⟩ := h₁ K ι K' ι' κ v P' n s t α W E hv hP' y hPn hs ht hsP hW htW hy
    (fun W' hW' hsW' => hE W' ((hfib W').1 ⟨hW', hsW'⟩).1 ((hfib W').1 ⟨hW', hsW'⟩).2)
  refine ⟨N, hN, hsum.trans (finsum_mem_congr (Set.ext fun W' => hfib W') fun W' hW' => ?_)⟩
  obtain ⟨hW'd, hW'i⟩ := hW'
  have hs' : rename v s ∉ P' := hsP
  have ht' : rename v t ∉ W' := fun h => htW (hW'i ▸ h)
  have hy' : fracMapZ v P' y * algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))
      (Ideal.Quotient.mk P' (rename v t)) =
      algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' (rename v s)) := by
    rw [← fracMapZ_algebraMap, ← fracMapZ_algebraMap, ← map_mul, hy]
  rw [(h₃ K' ι' P' (rename v s) (rename v t) (Function.extend κ α 0) W' (fracMapZ v P' y) hP'.2.1
    (rename_isMultiHomog hv hs) hs' hW'd (rename_isMultiHomog hv ht) ht' hy').2]

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PSemilocRank
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem SemilocRank.proof (hDim : FibreDimStatement) (hAdj : SemilocRankAdjoin.Statement) :
    SemilocRank.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G J s α W hv hP' hZ hJ hs hsP hW
  have hrel : ∀ k', ∃ i, (X ⟨k', i⟩ : MRing ι') ∉ P' := hP'.2.1.2.2
  choose i' hi' using hrel
  have hfib : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) 0 := hDim K ι K' ι' κ v P' (n + 1) 0 G hv hP' hZ
  have hz : ∀ k : FibreBlock κ, G.x' ⟨k.1, i' k.1⟩ ≠ 0 := by
    intro k h0
    apply hi' k.1
    rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
    exact h0
  have hj : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) (fun k => i' k.1) := by
    intro k hk
    apply hz k
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X] at hk
    exact hk
  rw [hJ.1 _ Fin.elim0 _ hfib hj, hAdj K ι K' ι' κ v P' n G s α W i' hv hP' hZ hs hsP hW hi']
  congr 1
  exact (ChartRankAdjoin.proof (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩)
    (fun k => i' k.1) hz hfib.1.2.1).symm

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PValCentreZ
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo regularityEmbedding_holds

noncomputable section

theorem ValCentreZ.proof : ValCentreZ.Statement := by
  intro K _ ι _ P hP
  have := hP.1
  intro R
  classical
  set L := FractionRing (MRing ι ⧸ P)
  have hX0 : ∀ {f : MRing ι}, f ∉ P → toFrac P f ≠ 0 := fun hf h => hf (toFrac_eq_zero.mp h)

  have hj : ∀ k, ∃ i, (X ⟨k, i⟩ : MRing ι) ∉ P ∧
      ∀ i', R.valuation (toFrac P (X ⟨k, i'⟩)) ≤ R.valuation (toFrac P (X ⟨k, i⟩)) := by
    intro k
    obtain ⟨i₀, hi₀⟩ := hP.2.2 k
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => (X ⟨k, i⟩ : MRing ι) ∉ P)
      (fun i => R.valuation (toFrac P (X ⟨k, i⟩))) ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩⟩
    refine ⟨i, (Finset.mem_filter.mp hi).2, fun i' => ?_⟩
    by_cases hi' : (X ⟨k, i'⟩ : MRing ι) ∈ P
    · rw [toFrac_eq_zero.mpr hi', map_zero]; exact zero_le
    · exact hmax i' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩)
  choose j hjP hjmax using hj
  choose r hr using fun p : Σ k, ι k =>
    exists_funField_mul_eq (P := P) (isMultiHomog_X_single p.1 p.2) (isMultiHomog_X_single p.1 (j p.1)) (hjP p.1)

  have hrle : ∀ p, R.valuation (r p : L) ≤ 1 := by
    intro p
    have hvj : R.valuation (toFrac P (X ⟨p.1, j p.1⟩)) ≠ 0 := by
      rw [Ne, Valuation.zero_iff]; exact hX0 (hjP p.1)
    have h := congrArg R.valuation (hr p)
    rw [map_mul] at h
    have hle : R.valuation (r p : L) * R.valuation (toFrac P (X ⟨p.1, j p.1⟩)) ≤
        1 * R.valuation (toFrac P (X ⟨p.1, j p.1⟩)) := by
      rw [one_mul]; exact (le_of_eq h).trans (hjmax p.1 p.2)
    exact le_of_mul_le_mul_right hle (zero_lt_iff.mpr hvj)

  have hmem : ∀ g, (chartHom r g : L) ∈ R := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => rw [chartHom_coe, eval₂Hom_C, eq_intCast]; exact intCast_mem R a
    | add f g hf hg => rw [map_add (f := _), Subring.coe_add]; exact add_mem hf hg
    | mul_X f p hf =>
      rw [map_mul, Subring.coe_mul]
      refine mul_mem hf ?_
      rw [← R.valuation_le_one_iff]
      simpa [chartHom] using hrle p

  obtain ⟨E, _, ψE, hψE⟩ : ∃ (E : Type) (_ : Field E) (ψE : MRing ι →+* E),
      ∀ g, ψE g = 0 ↔ R.valuation (chartHom r g : L) < 1 := by
    refine ⟨IsLocalRing.ResidueField R, inferInstance,
      (IsLocalRing.residue R).comp (((funField P).subtype.comp (chartHom r)).codRestrict R hmem), fun g => ?_⟩
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff,
      ValuationSubring.mem_nonunits_iff]
    exact Iff.rfl

  have hform : ∀ (g : MRing ι) (a : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a →
      (g ∈ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) ↔ R.valuation (chartHom r g : L) < 1) := by
    intro g a hg
    rw [RingHom.mem_ker, RegularityFunctionFieldNumber.specMap_form ψE ∅ hg, ← hψE, mul_eq_zero, MvPolynomial.C_eq_zero]
    refine or_iff_right (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ ?_)
    simp [RegularityFunctionFieldNumber.cS, MvPolynomial.X_ne_zero]
  have hPW : P ≤ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) := by
    obtain ⟨S, hS, hPS⟩ := hP.2.1
    refine hPS.le.trans (Ideal.span_le.mpr fun g hg => ?_)
    obtain ⟨a, ha⟩ := hS g hg
    have hgP : g ∈ P := hPS ▸ Ideal.subset_span hg
    rw [SetLike.mem_coe, hform g a ha]
    have h1 := chartHom_mul j r hr ha
    rw [toFrac_eq_zero.mpr hgP] at h1
    rw [(mul_eq_zero.mp h1).resolve_right (toFrac_prod_ne_zero j hjP a), map_zero]
    exact zero_lt_one
  refine ⟨RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅),
    ⟨RingHom.ker_isPrime _, RegularityValuationCentre.ker_isMultiHomogIdeal ψE, fun k => ⟨j k, ?_⟩⟩, hPW, ?_⟩
  ·
    have hrj : (r ⟨k, j k⟩ : L) = 1 :=
      mul_right_cancel₀ (hX0 (hjP k)) ((hr ⟨k, j k⟩).trans (one_mul _).symm)
    rw [hform _ _ (isMultiHomog_X_single k (j k))]
    have hXr : chartHom r (X ⟨k, j k⟩) = r ⟨k, j k⟩ := eval₂Hom_X' _ _ _
    rw [hXr, hrj, Valuation.map_one]
    exact lt_irrefl 1
  ·
    intro b f g hf hg hgW
    have hM := toFrac_prod_ne_zero j hjP b
    have e : toFrac P f / toFrac P g = (chartHom r f : L) / (chartHom r g : L) := by
      rw [← chartHom_mul j r hr hf, ← chartHom_mul j r hr hg, mul_div_mul_right _ _ hM]
    have hvg : R.valuation (chartHom r g : L) = 1 :=
      le_antisymm ((R.valuation_le_one_iff _).mpr (hmem g)) (not_lt.mp fun h => hgW ((hform g b hg).mpr h))
    change toFrac P f / toFrac P g ∈ R ∧
      (f ∈ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) ↔ toFrac P f / toFrac P g ∈ R.nonunits)
    rw [e, ValuationSubring.mem_nonunits_iff, map_div₀, hvg, div_one, hform f b hf]
    refine ⟨(R.valuation_le_one_iff _).mp ?_, Iff.rfl⟩
    rw [map_div₀, hvg, div_one]
    exact (R.valuation_le_one_iff _).mpr (hmem f)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PWWArithVar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

theorem mCoordIdeal_eq_ker_multiConeMap {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Φ : Type} [Field Φ] (c : (Σ k, ι k) → Φ) : mCoordIdeal c = RingHom.ker (T.multiConeMap c) := by
  have h : (mConeMap c : MRing ι →+* MvPolynomial K Φ) = T.multiConeMap c :=
    MvPolynomial.ringHom_ext (fun r => by simp [T.multiConeMap, mConeMap])
      (fun p => by simp [T.multiConeMap, mConeMap])
  rw [mCoordIdeal, ← h]
  rfl

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocRankFrac
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def SemilocRankFrac.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (s : MRing ι) (α : K → ℕ) (W : Ideal (MRing ι)) (i' : ∀ k', ι' k')
    (hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)) [Algebra ℚ G.Φ'],
    IsArithVar (imageZ v P') (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s α → s ∉ imageZ v P' →
    W ∈ divSupp (imageZ v P') s → (∀ k', (X ⟨k', i' k'⟩ : MRing ι') ∉ P') →
    haveI := hP'.2.1.1
    letI := (locToSemiloc hv P' W).toAlgebra
    Module.finrank (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) =
      IntermediateField.relfinrank
        (IntermediateField.adjoin ℚ
          (Set.range ((fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩) ∘ v)))
        (IntermediateField.adjoin ℚ (Set.range fun q : Σ k', ι' k' => G.x' q / G.x' ⟨q.1, i' q.1⟩))

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ThmIExistsFamily
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace ThmIExists

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem hermLine_ext {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

theorem tensor_right_comm (A B C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    (A.tensor B).tensor C = (A.tensor C).tensor B :=
  hermLine_ext (add_right_comm _ _ _) (funext fun _ => mul_right_comm _ _ _)

theorem tensor_tensor_comm (A B C D : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    (A.tensor B).tensor (C.tensor D) = (A.tensor C).tensor (B.tensor D) :=
  hermLine_ext (add_add_add_comm _ _ _ _) (funext fun _ => mul_mul_mul_comm _ _ _ _)

theorem smooth_tensor {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  hA.mul hB

def segreLine (m : ℕ) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι :=
  HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun _ => (m : ℤ))

theorem segreLine_a (m : ℕ) : (segreLine m : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι).a = fun _ => (m : ℤ) := rfl

theorem isSmoothHerm_segreLine (m : ℕ) : IsSmoothHerm (segreLine m : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) := by
  have hfun : (segreLine m : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι).h =
      fun z => ∏ k, Real.sqrt (∑ i : ι k, ‖z ⟨k, i⟩‖ ^ 2) ^ m := by
    funext z
    simp only [segreLine, HermLine.ofMetrics, fsMetric, zpow_natCast, EuclideanSpace.norm_eq]
  unfold IsSmoothHerm
  rw [hfun]
  refine contDiffOn_prod fun k _ => (ContDiffOn.sqrt ?_ fun z hz => ?_).pow m
  · exact (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, ι k))).contDiffOn
  · obtain ⟨i, hi⟩ := hz k
    exact (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩).ne'

theorem exists_form {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (b : K → ℕ) :
    ∃ s : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s b ∧ s ∉ P := by
  classical
  have hrel := hP.2.1.2.2
  have hpr : P.IsPrime := hP.2.1.1
  refine ⟨ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow (fun k => (hrel k).choose) b,
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_xpow _ _, fun h => ?_⟩
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow, Ideal.IsPrime.prod_mem_iff] at h
  obtain ⟨k, _, hk⟩ := h
  exact (hrel k).choose_spec (hpr.mem_of_pow_mem _ hk)


open Classical in
def secOf (P : Ideal (MRing ι)) (b : K → ℕ) : MRing ι :=
  if h : ∃ s : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s b ∧ s ∉ P then h.choose else 0

theorem secOf_spec {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (b : K → ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (secOf P b) b ∧ secOf P b ∉ P := by
  have h := exists_form hP b
  rw [secOf, dite_eq_left h]
  exact h.choose_spec

theorem sec_mul {P : Ideal (MRing ι)} (hpr : P.IsPrime) {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {s t : MRing ι}
    (hs : IsSectionOn P A s) (ht : IsSectionOn P B t) : IsSectionOn P (A.tensor B) (s * t) := by
  obtain ⟨a, ha, has, hsP⟩ := hs
  obtain ⟨b, hb, hbt, htP⟩ := ht
  refine ⟨a + b, fun k => ?_, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul has hbt, fun h => ?_⟩
  · simp [HermLine.tensor, ha, hb]
  · rcases hpr.mem_or_mem h with h | h
    exacts [hsP h, htP h]

theorem sec_congr {P : Ideal (MRing ι)} {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {s : MRing ι} (h : A = B)
    (hs : IsSectionOn P A s) : IsSectionOn P B s := h ▸ hs

def shift (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : ℕ := ∑ k, (A.a k).natAbs

def upDeg (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : K → ℕ := fun k => (A.a k + shift A).toNat

theorem upDeg_cast (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (k : K) : ((upDeg A k : ℕ) : ℤ) = A.a k + shift A := by
  rw [upDeg, Int.toNat_of_nonneg]
  have h1 : (A.a k).natAbs ≤ shift A :=
    Finset.single_le_sum (f := fun k => (A.a k).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have h2 : -((A.a k).natAbs : ℤ) ≤ A.a k := by
    rw [Int.natCast_natAbs]; exact neg_abs_le _
  omega

theorem isSectionOn_up {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    IsSectionOn P (A.tensor (segreLine (shift A))) (secOf P (upDeg A)) :=
  ⟨upDeg A, fun _ => by simp [HermLine.tensor, segreLine_a, upDeg_cast], (secOf_spec hP _).1,
    (secOf_spec hP _).2⟩

theorem isSectionOn_segre {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (m : ℕ) :
    IsSectionOn P (segreLine m) (secOf P fun _ => m) :=
  ⟨fun _ => m, fun _ => rfl, (secOf_spec hP _).1, (secOf_spec hP _).2⟩

def lift {n : ℕ} (J : Ideal (MRing ι) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ) :
    Ideal (MRing ι) → (m : ℕ) → (Fin m → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ :=
  fun W m L => if h : m = n then J W (L ∘ Fin.cast h.symm) else 0

theorem lift_self {n : ℕ} (J : Ideal (MRing ι) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ) (W : Ideal (MRing ι))
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : lift J W n L = J W L := by
  simp only [lift]
  rfl

theorem recR_congr {I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ} {n : ℕ}
    (h : ∀ W L, I W n L = J W n L) (P : Ideal (MRing ι)) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (s : MRing ι) : recR I P L A s = recR J P L A s := by
  unfold recR
  simp only [h]

def step {n : ℕ} (J : Ideal (MRing ι) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ) (P : Ideal (MRing ι))
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : ℝ :=
  recR (lift J) P L (A.tensor (segreLine (shift A))) (secOf P (upDeg A)) -
    recR (lift J) P L (segreLine (shift A)) (secOf P fun _ => shift A)

def fam : (n : ℕ) → Ideal (MRing ι) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun P L => step (fam n) P (Fin.init L) (L (Fin.last n))

def famI : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ := fun P n L => fam n P L

theorem famI_snoc (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) :
    famI P (n + 1) (Fin.snoc L A) =
      recR famI P L (A.tensor (segreLine (shift A))) (secOf P (upDeg A)) -
        recR famI P L (segreLine (shift A)) (secOf P fun _ => shift A) := by
  have hc : ∀ (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι), recR (lift (fam n)) P L B s = recR famI P L B s :=
    fun B s => recR_congr (fun W L' => lift_self (fam n) W L') P L B s
  have hs : famI P (n + 1) (Fin.snoc L A) = step (fam n) P L A := by
    simp only [famI, fam, Fin.init_snoc, Fin.snoc_last]
  rw [hs, step, hc, hc]

def LastAddAt (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ) (n : ℕ) : Prop :=
  ∀ (P : Ideal (MRing ι)) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    I P (n + 1) (Fin.snoc L (A.tensor B)) = I P (n + 1) (Fin.snoc L A) + I P (n + 1) (Fin.snoc L B)

def WDAt (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ) (n : ℕ) : Prop :=
  ∀ (P : Ideal (MRing ι)) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s t : MRing ι),
    IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm B →
    IsSectionOn P B s → IsSectionOn P B t → recR I P L B s = recR I P L B t

section Steps

variable (hMul : RMulStatement) {n : ℕ} (hwd : WDAt (famI (ι := ι)) n)
include hMul hwd

theorem famI_eq_diff {P : Ideal (MRing ι)} (hP : IsArithVar P (n + 1)) {L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hL : ∀ j, IsSmoothHerm (L j)) {A C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (hC : IsSmoothHerm C)
    {t c : MRing ι} (ht : IsSectionOn P (A.tensor C) t) (hc : IsSectionOn P C c) :
    famI P (n + 1) (Fin.snoc L A) = recR famI P L (A.tensor C) t - recR famI P L C c := by
  have hpr : P.IsPrime := hP.2.1.1
  set H : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := segreLine (shift A)
  have hH : IsSmoothHerm H := isSmoothHerm_segreLine _
  have hu := isSectionOn_segre hP (shift A)
  have ht0 := isSectionOn_up hP A
  have e1 := hMul K ι famI P n L (A.tensor H) C _ _ hP hL (smooth_tensor hA hH) hC ht0 hc
  have e2 := hMul K ι famI P n L (A.tensor C) H _ _ hP hL (smooth_tensor hA hC) hH ht hu
  have e3 : recR famI P L ((A.tensor H).tensor C) (secOf P (upDeg A) * c) =
      recR famI P L ((A.tensor C).tensor H) (t * secOf P fun _ => shift A) := by
    rw [tensor_right_comm A H C]
    exact hwd P L _ _ _ hP hL (smooth_tensor (smooth_tensor hA hC) hH)
      (sec_congr (tensor_right_comm A H C) (sec_mul hpr ht0 hc)) (sec_mul hpr ht hu)
  rw [famI_snoc]
  linarith

theorem hasRAt_famI : HasRAt (famI (ι := ι)) n := by
  intro P L A s hP hL hA hs
  have hpr : P.IsPrime := hP.2.1.1
  have hH : IsSmoothHerm (segreLine (shift A) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) := isSmoothHerm_segreLine _
  have hu := isSectionOn_segre hP (shift A)
  rw [famI_eq_diff hMul hwd hP hL hA hH (sec_mul hpr hs hu) hu,
    hMul K ι famI P n L A _ s _ hP hL hA hH hs hu]
  ring

theorem lastAddAt_famI : LastAddAt (famI (ι := ι)) n := by
  intro P L A B hP hL hA hB
  have hpr : P.IsPrime := hP.2.1.1
  set Ha : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := segreLine (shift A)
  set Hb : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := segreLine (shift B)
  have hHa : IsSmoothHerm Ha := isSmoothHerm_segreLine _
  have hHb : IsSmoothHerm Hb := isSmoothHerm_segreLine _
  have hua := isSectionOn_segre hP (shift A)
  have hub := isSectionOn_segre hP (shift B)
  have hta := isSectionOn_up hP A
  have htb := isSectionOn_up hP B
  have htab : IsSectionOn P ((A.tensor B).tensor (Ha.tensor Hb))
      (secOf P (upDeg A) * secOf P (upDeg B)) :=
    sec_congr (tensor_tensor_comm A Ha B Hb) (sec_mul hpr hta htb)
  rw [famI_eq_diff hMul hwd hP hL (smooth_tensor hA hB) (smooth_tensor hHa hHb) htab (sec_mul hpr hua hub),
    famI_eq_diff hMul hwd hP hL hA hHa hta hua, famI_eq_diff hMul hwd hP hL hB hHb htb hub,
    tensor_tensor_comm A B Ha Hb,
    hMul K ι famI P n L _ _ _ _ hP hL (smooth_tensor hA hHa) (smooth_tensor hB hHb) hta htb,
    hMul K ι famI P n L _ _ _ _ hP hL hHa hHb hua hub]
  ring

end Steps

theorem wdAt_zero (hD1 : RegularityIndependence.Statement) : WDAt (famI (ι := ι)) 0 := by
  intro P L B s t hP _ _ hs ht
  have hL : L = Fin.elim0 := funext fun j => j.elim0
  subst hL
  exact hD1 K ι famI P B s t hP hs ht

theorem all_dims (hD1 : RegularityIndependence.Statement) (hMul : RMulStatement)
    (hstep : ∀ n, HasRAt (famI (ι := ι)) n → LastAddAt (famI (ι := ι)) n → WDAt (famI (ι := ι)) (n + 1))
    (n : ℕ) : WDAt (famI (ι := ι)) n ∧ HasRAt (famI (ι := ι)) n ∧ LastAddAt (famI (ι := ι)) n := by
  induction n with
  | zero =>
    have h0 := wdAt_zero (ι := ι) hD1
    exact ⟨h0, hasRAt_famI hMul h0, lastAddAt_famI hMul h0⟩
  | succ n ih =>
    have h1 := hstep n ih.2.1 ih.2.2
    exact ⟨h1, hasRAt_famI hMul h1, lastAddAt_famI hMul h1⟩

theorem isRFamily_famI (hD1 : RegularityIndependence.Statement) (hMul : RMulStatement)
    (hstep : ∀ n, HasRAt (famI (ι := ι)) n → LastAddAt (famI (ι := ι)) n → WDAt (famI (ι := ι)) (n + 1)) :
    IsRFamily (famI (ι := ι)) :=
  ⟨fun P n L A B hP hL hA hB => (all_dims hD1 hMul hstep n).2.2 P L A B hP hL hA hB,
    fun P n L A s a hP hL hA ha hs hsP =>
      (all_dims hD1 hMul hstep n).2.1 P L A s hP hL hA ⟨a, ha, hs, hsP⟩⟩

end ThmIExists

end

end GroundTheory.Heights₂.Heights.Inter
end

