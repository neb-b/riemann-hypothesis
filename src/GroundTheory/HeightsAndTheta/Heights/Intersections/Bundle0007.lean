module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace ChartRankAdjoin

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] (z : (Σ k, ι k) → Φ') (j : ∀ k, ι k)

def affCoord : (Σ k, ι k) → Φ' := fun q => z q / z ⟨q.1, j q.1⟩

variable {z j}

theorem aeval_monomial_mul (hz : ∀ k, z ⟨k, j k⟩ ≠ 0) (m : (Σ k, ι k) →₀ ℕ) :
    aeval (affCoord z j) (monomial m (1 : Φ)) *
        ∏ k, z ⟨k, j k⟩ ^ (Finsupp.weight (NumbersDVR.blockWeight ι) m k) =
      aeval z (monomial m (1 : Φ)) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m m' hm hm' =>
    rw [← mul_one (1 : Φ), ← monomial_mul, map_mul, map_mul, map_add (f := _), ← hm, ← hm']
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  | single p n =>
    rw [← X_pow_eq_monomial, map_pow, map_pow, Finsupp.weight_single,
      Fintype.prod_eq_single p.1 (fun k hk => by simp [NumbersDVR.blockWeight, hk])]
    simp only [affCoord, aeval_X, NumbersDVR.blockWeight, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one, div_pow]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ (hz p.1))]

theorem aeval_mul_of_isMultiHomog [∀ k, Fintype (ι k)] (hz : ∀ k, z ⟨k, j k⟩ ≠ 0) {h : MRingOver Φ ι} {a : K → ℕ}
    (hh : IsMultiHomog h a) : aeval (affCoord z j) h * ∏ k, z ⟨k, j k⟩ ^ a k = aeval z h := by
  have hw := (Bridge.isMultiHomog_iff h a).mpr hh
  conv_rhs => rw [h.as_sum]
  conv_lhs => rw [h.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw' : Finsupp.weight (NumbersDVR.blockWeight ι) m = a := hw (mem_support_iff.mp hm)
  have hmon : monomial m (AddMonoidAlgebra.coeff h m) = AddMonoidAlgebra.coeff h m • monomial m (1 : Φ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmon, map_smul, map_smul, smul_mul_assoc, ← hw', aeval_monomial_mul hz]

theorem chartIdeal_eq_ker [∀ k, Fintype (ι k)] (hz : ∀ k, z ⟨k, j k⟩ ≠ 0)
    (hP : IsMultiHomogIdeal (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ'))) :
    chartIdeal (RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ')) j =
      RingHom.ker (aeval (affCoord z j) : MRingOver Φ ι →ₐ[Φ] Φ') := by
  have hprod : ∀ a : K → ℕ, ∏ k, z ⟨k, j k⟩ ^ a k ≠ 0 :=
    fun a => Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)
  have hunit : Ideal.span (Set.range fun k => (X ⟨k, j k⟩ : MRingOver Φ ι) - 1) ≤
      RingHom.ker (aeval (affCoord z j) : MRingOver Φ ι →ₐ[Φ] Φ') := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, aeval_X, affCoord]
    rw [div_self (hz k), sub_self]
  refine le_antisymm (sup_le ?_ hunit) fun f hf => ?_
  · obtain ⟨S, hS, hPS⟩ := hP
    rw [hPS, Ideal.span_le]
    intro s hs
    obtain ⟨a, ha⟩ := hS s hs
    have hsP : s ∈ RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ') := by
      rw [hPS]; exact Ideal.subset_span hs
    have h1 := aeval_mul_of_isMultiHomog hz ha
    rw [RingHom.mem_ker.mp hsP] at h1
    exact RingHom.mem_ker.mpr ((mul_eq_zero.mp h1).resolve_right (hprod a))
  · obtain ⟨N, hN⟩ := NumbersDVR.IntNumPoint.exists_homog_congr j f
    obtain ⟨h, hh, hc⟩ := hN N le_rfl
    have hfh : f - h ∈ NumbersDVR.IntNumPoint.chartUnitIdeal (F := Φ) j := Ideal.Quotient.eq.mp hc
    have h0 : aeval (affCoord z j) h = 0 := by
      have := RingHom.mem_ker.mp (hunit hfh)
      rwa [map_sub, RingHom.mem_ker.mp hf, zero_sub, neg_eq_zero] at this
    have hhP : h ∈ RingHom.ker (aeval z : MRingOver Φ ι →ₐ[Φ] Φ') := by
      rw [RingHom.mem_ker, ← aeval_mul_of_isMultiHomog hz ((Bridge.isMultiHomog_iff h N).mp hh), h0,
        zero_mul]
    have : f = (f - h) + h := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_right hfh) (Ideal.mem_sup_left hhP)

end ChartRankAdjoin

theorem ChartRankAdjoin.proof : ChartRankAdjoin.Statement := by
  classical
  intro K _ ι _ Φ Φ' _ _ _ z j hz hP
  have hker := ChartRankAdjoin.chartIdeal_eq_ker hz hP
  have e : (fun q : Σ k, ι k => z q / z ⟨q.1, j q.1⟩) = ChartRankAdjoin.affCoord z j := rfl
  rw [e, ptDeg, hker,
    (Ideal.quotientKerEquivRange (aeval (ChartRankAdjoin.affCoord z j) :
      MRingOver Φ ι →ₐ[Φ] Φ')).toLinearEquiv.finrank_eq, aeval_range,
    ← IntermediateField.finrank_eq_finrank_subalgebra]
  by_cases halg : ∀ q, IsAlgebraic Φ (ChartRankAdjoin.affCoord z j q)
  · rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (by rintro _ ⟨q, rfl⟩; exact halg q)]
  · push Not at halg
    obtain ⟨q, hq⟩ := halg
    have hinf : ∀ B : Subalgebra Φ Φ', ChartRankAdjoin.affCoord z j q ∈ B → ¬ Module.Finite Φ B :=
      fun B hB hfin => hq ((IsAlgebraic.of_finite Φ (⟨_, hB⟩ : B)).algHom B.val)
    have h1 : ChartRankAdjoin.affCoord z j q ∈ Algebra.adjoin Φ (Set.range (ChartRankAdjoin.affCoord z j)) :=
      Algebra.subset_adjoin ⟨q, rfl⟩
    have h2 : ChartRankAdjoin.affCoord z j q ∈
        (IntermediateField.adjoin Φ (Set.range (ChartRankAdjoin.affCoord z j))).toSubalgebra :=
      IntermediateField.subset_adjoin Φ _ ⟨q, rfl⟩
    rw [Module.finrank_of_not_finite (hinf _ h1), Module.finrank_of_not_finite (hinf _ h2)]

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.POrbitCompNonvanish
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem OrbitCompNonvanish.isHomogeneous_blkWt {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    P.IsHomogeneous (weightedHomogeneousSubmodule ℤ (blkWt (ι := ι))) := by
  obtain ⟨S, hS, rfl⟩ := hP
  apply Ideal.homogeneous_span
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  refine ⟨Finsupp.equivFunOnFinite.symm a, (mem_weightedHomogeneousSubmodule ℤ _ _ _).mpr ?_⟩
  intro m hm
  ext k
  rw [weight_blkWt_apply, ha m (mem_support_iff.mpr hm) k]
  simp

theorem OrbitCompNonvanish.isMultiHomog_component (E : MRing ι) (δ : K →₀ ℕ) :
    IsMultiHomog (weightedHomogeneousComponent (blkWt (ι := ι)) δ E) δ := by
  intro m hm k
  have h := weightedHomogeneousComponent_isWeightedHomogeneous (w := blkWt (ι := ι)) δ E
    (mem_support_iff.mp hm)
  rw [← weight_blkWt_apply, h]

theorem OrbitCompNonvanish.proof : OrbitCompNonvanish.Statement := by
  intro K _ ι _ P E hP hE
  classical
  have hPh := OrbitCompNonvanish.isHomogeneous_blkWt hP
  obtain ⟨δ, hδ⟩ : ∃ δ, weightedHomogeneousComponent (blkWt (ι := ι)) δ E ∉ P := by
    by_contra h
    push Not at h
    exact hE ((mem_iff_weightedHomogeneousComponent_mem ℤ _ hPh E).mpr h)
  refine ⟨_, δ, OrbitCompNonvanish.isMultiHomog_component E δ, hδ, fun z hz => ?_⟩

  let comp : (K →₀ ℕ) → MRing ι := fun b => weightedHomogeneousComponent (blkWt (ι := ι)) b E
  let lam : (K →₀ ℕ) → ℂ := fun b => eval z (map (Int.castRingHom ℂ) (comp b))
  have hfin := weightedHomogeneousComponent_finsupp (w := blkWt (ι := ι)) E
  let T : Finset (K →₀ ℕ) := insert δ hfin.toFinset
  have hsum : ∑ b ∈ T, comp b = E := by
    rw [← Finset.sum_subset (Finset.subset_insert δ hfin.toFinset), ← finsum_eq_sum _ hfin]
    · exact sum_weightedHomogeneousComponent _ E
    · intro b _ hb
      by_contra hne
      exact hb (hfin.mem_toFinset.mpr hne)
  let Q : MvPolynomial K ℂ := ∑ b ∈ T, monomial b (lam b)
  have hQ : ∀ c : K → ℂ, eval c Q = eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) E) := by
    intro c
    conv_rhs => rw [← hsum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Q, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [eval_smul_homog (comp b) b (OrbitCompNonvanish.isMultiHomog_component E b) c z, eval_monomial,
      Finsupp.prod_fintype _ _ (by simp)]
    ring
  have hQ0 : Q ≠ 0 := by
    intro h0
    have hc := congrArg (AddMonoidAlgebra.coeff · δ) h0
    simp only [Q, coeff_sum, coeff_monomial, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] at hc
    rw [Finset.sum_ite_eq' T δ] at hc
    simp only [show δ ∈ T from Finset.mem_insert_self _ _, ↓reduceIte] at hc
    exact hz hc
  by_contra hno
  push Not at hno
  apply hQ0
  refine funext_set (fun _ => ({0}ᶜ : Set ℂ)) (fun _ => (Set.finite_singleton 0).infinite_compl)
    fun x hx => ?_
  rw [hQ, map_zero]
  exact hno x fun k => hx k (Set.mem_univ k)

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]



def IsClosedPt (Q : Ideal (MRing ι)) : Prop :=
  IsMultiProjPrime Q ∧ ringKrullDim (MRing ι ⧸ Q) = ((Fintype.card K : ℕ) : WithBot ℕ∞)

def HasRAt (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (n : ℕ) : Prop :=
  ∀ (P : Ideal (MRing ι)) (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s →
    I P (n + 1) (Fin.snoc L A) = recR I P L A s

end Objects

section TheoremI

def ThmIExists.Statement : Prop := ExistsStatement

def ThmIUnique.Statement : Prop := UniqueStatement

def ThmISymm.Statement : Prop := SymmStatement

def SpecIntHeightFormula.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    (A : HermLine ι) (s : MRing ι),
    IsArithVar P 1 → IsSmoothHerm A → IsSectionOn P A s →
    recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s =
      vertR P (Fin.elim0 : Fin 0 → HermLine ι) s - arInt P s A (Fin.elim0 : Fin 0 → HermLine ι)

def RegularityIndependence.Statement : Prop := DimensionOneRationalSectionIndependence

def Swap.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι),
    HasRAt I n → IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm A' →
    IsSectionOn P A s → IsSectionOn P A' s' → (∀ W, W ∈ divSupp P s → W ∉ divSupp P s') →
    recR I P (Fin.snoc L A') A s = recR I P (Fin.snoc L A) A' s'

end TheoremI

section Consequences

def InductiveIntersectionFormula.Statement : Prop := VerticalStatement

def Conservation.Statement : Prop := ConservationStatement

def RatR.Statement : Prop := RatRStatement

end Consequences

section PF

def PushforwardProjectivePoint.Statement : Prop := ContractStatement

def PushforwardArithIntersection.Statement : Prop := GenDegStatement

def PushforwardProjLineFlag.Statement : Prop := PFStatement

end PF

section Inhabitants

theorem isMultiHomog_Xc (n : ℕ) (i : Fin n) : IsMultiHomog (Xc n i) (fun _ => 1) := by
  intro m hm k
  obtain ⟨⟩ := k
  have hm' : m ∈ (X (⟨(), i⟩ : (_ : Unit) × Fin n) : MRing (PBlk n)).support := hm
  rw [support_X, Finset.mem_singleton] at hm'
  subst hm'
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hb (sigma_mk_injective h).symm
  · simp

theorem isSectionOn_Xc (n : ℕ) (i : Fin n) : IsSectionOn ⊥ (fsLine n) (Xc n i) :=
  ⟨fun _ => 1, fun _ => rfl, isMultiHomog_Xc n i, by
    rw [Submodule.mem_bot]
    exact X_ne_zero _⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLineFibre
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def LineFibreBlocks.Statement : Prop :=
  ∀ (F : Type) [Field F] (K₀ : Type) [Fintype K₀] (ι₀ : K₀ → Type) [∀ k, Fintype (ι₀ k)] (k₀ : K₀)
    (Q : Ideal (MRingOver F ι₀)) (J : IFamily F ι₀),
    (∀ k, k = k₀) → IsProjVarF Q 1 →
    (∃ S : Set (MRingOver F ι₀), (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧ Q = Ideal.span S) →
    IsFieldIntersection J → ∀ m : K₀ → ℤ, J Q 1 ![m] = m k₀

end GroundTheory.Heights₂.Heights.Inter
end
end

