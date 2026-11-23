module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ArithDegree
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertIncrement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace HilbertIncrement

variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

theorem weight_intWeight (e : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (intWeight (ι := ι)) e =
      fun k => ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) := by
  funext k
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Nat.cast_sum, Nat.cast_mul, intWeight, unitDeg, blockWeight]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : k = v.1 <;> simp [h]

theorem isWeightedHomogeneous_intWeight_iff {f : MRing ι F} {a : K → ℕ} :
    IsWeightedHomogeneous (intWeight (ι := ι)) f (fun k => (a k : ℤ)) ↔
      IsWeightedHomogeneous (blockWeight ι) f a := by
  constructor
  · intro h e he
    funext k
    have e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = (a k : ℤ) := by
      have := congrFun (h he) k
      rw [weight_intWeight] at this
      exact this
    exact_mod_cast e1
  · intro h e he
    rw [weight_intWeight, h he]

theorem ringPiece_natCast (a : K → ℕ) :
    ringPiece (F := F) (ι := ι) (fun k => (a k : ℤ)) =
      weightedHomogeneousSubmodule F (blockWeight ι) a := by
  ext f
  simp only [ringPiece, mem_weightedHomogeneousSubmodule]
  exact isWeightedHomogeneous_intWeight_iff

theorem component_intWeight_mem {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J)
    {f : MRing ι F} (hf : f ∈ J) (m : K → ℤ) :
    weightedHomogeneousComponent (intWeight (ι := ι)) m f ∈ J := by
  classical
  by_cases hm : ∀ k, 0 ≤ m k
  · have e : weightedHomogeneousComponent (intWeight (ι := ι)) m f =
        weightedHomogeneousComponent (blockWeight ι) (fun k => (m k).toNat) f := by
      ext e
      rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent, weight_intWeight]
      have hiff : ((fun k => ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ)) = m) ↔
          Finsupp.weight (blockWeight ι) e = fun k => (m k).toNat := by
        constructor
        · intro h
          funext k
          have e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k := congrFun h k
          have := hm k
          show _ = (m k).toNat
          omega
        · intro h
          funext k
          have e1 : Finsupp.weight (blockWeight ι) e k = (m k).toNat := congrFun h k
          have := hm k
          show ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k
          omega
      simp only [hiff]
    rw [e]
    exact hJ f hf _
  · push Not at hm
    obtain ⟨k, hk⟩ := hm
    have e : weightedHomogeneousComponent (intWeight (ι := ι)) m f = 0 := by
      ext e
      rw [coeff_weightedHomogeneousComponent, weight_intWeight]
      split_ifs with h
      · have e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k := congrFun h k
        omega
      · rfl
    rw [e]
    exact J.zero_mem

theorem isMultiHomogIdeal_sup_X {q : Ideal (MRing ι F)} (hq : IsMultiHomogIdeal q)
    (v : Σ k, ι k) : IsMultiHomogIdeal (q ⊔ Ideal.span {(X v : MRing ι F)}) := by
  classical
  intro f hf n
  obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have hX : IsMultiHomog (X v : MRing ι F) (blockWeight ι v) :=
    isWeightedHomogeneous_X F (blockWeight ι) v
  rw [map_add (f := _), GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide.component_mul_form hX t n]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (hq p hp n)) ?_
  split_ifs
  · exact Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩)
  · exact zero_mem _

def quotPiece (J : Ideal (MRing ι F)) (m : K → ℤ) : Submodule F (MRing ι F ⧸ J) :=
  (ringPiece m).map (Ideal.Quotient.mkₐ F J).toLinearMap

theorem quotPiece_natCast (J : Ideal (MRing ι F)) (a : K → ℕ) :
    quotPiece J (fun k => (a k : ℤ)) = gradedPiece J a := by
  rw [quotPiece, gradedPiece, ringPiece_natCast]

theorem isMultigrading_quotPiece [Fintype K] {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J) :
    IsMultigrading ι (MRing ι F ⧸ J) (quotPiece J) := by
  refine ⟨?_, ?_⟩
  · classical
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
      intro s v hv hsum m hm
      have hex : ∀ i ∈ s, ∃ y ∈ ringPiece (F := F) (ι := ι) i,
          (Ideal.Quotient.mkₐ F J).toLinearMap y = v i := fun i hi => Submodule.mem_map.mp (hv i hi)
      choose! x hx hxv using hex
      have hy : (∑ i ∈ s, x i) ∈ J := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
        rw [← hsum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← hxv i hi]
        rfl
      have hc := component_intWeight_mem hJ hy m
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at hc
      have hcs : (∑ i ∈ s, weightedHomogeneousComponent (intWeight (ι := ι)) m (x i)) = x m := by
        rw [Finset.sum_eq_single m]
        · rw [weightedHomogeneousComponent_of_mem (hx m hm), ite_eq_left rfl]
        · intro j hj hjm
          rw [weightedHomogeneousComponent_of_mem (hx j hj), ite_eq_right (Ne.symm hjm)]
        · intro h
          exact absurd hm h
      rw [hcs] at hc
      rw [← hxv m hm]
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hc
    · show (⨆ m, (ringPiece (F := F) (ι := ι) m).map (Ideal.Quotient.mkₐ F J).toLinearMap) = ⊤
      rw [← Submodule.map_iSup]
      show Submodule.map _ (⨆ i, weightedHomogeneousSubmodule F (intWeight (ι := ι)) i) = ⊤
      rw [(weightedDecomposition F (intWeight (ι := ι))).isInternal.submodule_iSup_eq_top,
        Submodule.map_top, LinearMap.range_eq_top]
      exact Ideal.Quotient.mkₐ_surjective F J
  · intro v m x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    have hmul : (X v : MRing ι F) * y ∈ ringPiece (m + unitDeg v.1) := by
      change IsWeightedHomogeneous (intWeight (ι := ι)) y m at hy
      change IsWeightedHomogeneous (intWeight (ι := ι)) (X v * y) (m + unitDeg v.1)
      rw [add_comm m (unitDeg v.1)]
      exact (isWeightedHomogeneous_X F (intWeight (ι := ι)) v).mul hy
    exact Submodule.mem_map.mpr ⟨_, hmul, rfl⟩

theorem proof (hrec : IntersectionRecursion.Statement.{u}) : HilbertIncrement.Statement.{u} := by
  intro d hmod F _ K _ _ ι _ q hq hdim b
  obtain ⟨i, hi⟩ := hq.relevant b
  have hJ : IsMultiHomogIdeal (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) :=
    isMultiHomogIdeal_sup_X hq.multiHomog ⟨b, i⟩
  obtain ⟨hstep, hsupp⟩ :=
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.HilbertIncrement.closed.{u} F K ι (d + 1) q b i hq
      hdim (by omega) hi
  obtain ⟨a₀, C, hbd⟩ := hmod F K ι (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}))
    (quotPiece _) (isMultigrading_quotPiece hJ) (fun W hW hann => by
      rw [Ideal.annihilator_quotient] at hann
      simpa using hsupp W hW hann)
  refine ⟨a₀, C, fun a ha => ?_⟩
  have h1 : hilbFn q (fun k => (a k : ℤ)) - hilbFn q ((fun k => (a k : ℤ)) - unitDeg b) =
      (Module.finrank F (quotPiece (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})
        fun k => (a k : ℤ)) : ℤ) := by
    rw [show unitDeg b = Pi.single b 1 from rfl, hstep, hilbFn,
      ite_eq_left (fun k => Nat.cast_nonneg _), quotPiece_natCast]
    have ha' : (fun k => ((a k : ℤ)).toNat) = a := funext fun k => by omega
    rw [ha']
  have h2 : intNum F q (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ)) =
      topCycleNum F ι (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})) d
        (fun _ => fun k => (a k : ℤ)) := by
    rw [hrec F K ι q d hq hdim b i hi]
    unfold topCycleNum
    refine finsum_congr fun W => ?_
    have hann : Module.annihilator (MRing ι F)
        (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})) =
        q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} := Ideal.annihilator_quotient
    by_cases hc : IsMultiProjPrime W ∧ q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W ∧
        ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)
    · rw [dite_eq_left hc, dite_eq_left (by rw [hann]; exact hc)]
      rfl
    · rw [dite_eq_right hc, dite_eq_right (by rw [hann]; exact hc)]
  rw [h1, h2]
  simpa using hbd a ha

end HilbertIncrement

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt MeasureTheory Module Filter
  Topology Asymptotics Matrix
open scoped ComplexOrder

noncomputable section

section Had

variable {K : Type*} [Field K] [NumberField K]

def fibreNorm (E : HermitianBundle K) (σ : K →+* ℂ) (x : Fibre σ E.carrier) : ℝ :=
  ‖FibreSpace.equiv E.metric σ x‖

abbrev bundleRank (E : HermitianBundle K) : ℕ := Module.finrank (𝓞 K) E.carrier


structure BoundedInjection (E' E : HermitianBundle K) (A : (K →+* ℂ) → ℝ) where

  toLinearMap : E'.carrier →ₗ[𝓞 K] E.carrier
  injective : Function.Injective toLinearMap
  norm_le : ∀ (σ : K →+* ℂ) (x : Fibre σ E'.carrier),
    fibreNorm E σ (toLinearMap.lTensor (ComplexAt σ) x) ≤ A σ * fibreNorm E' σ x

structure ShortFamily (E : HermitianBundle K) (lam : (K →+* ℂ) → ℝ) where

  vec : Fin (bundleRank E) → E.carrier
  linearIndependent : LinearIndependent (𝓞 K) vec
  norm_le : ∀ (σ : K →+* ℂ) (i : Fin (bundleRank E)),
    fibreNorm E σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] vec i) ≤ lam σ

end Had

section HadExamples

variable (K : Type*) [Field K] [NumberField K]

theorem fibreNorm_standard_single (n : ℕ) (σ : K →+* ℂ) (i : Fin n) :
    fibreNorm (HermitianBundle.standard K n) σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] Pi.single i 1) = 1 := by
  have h := norm_fibreVec_sq (HermitianMetric.standard K (Fin n)) σ (Pi.single i 1)
  rw [HermitianMetric.standard_inner_single, Complex.one_re] at h
  have h0 := norm_nonneg (fibreVec (HermitianMetric.standard K (Fin n)) σ (Pi.single i 1))
  have h1 : ‖fibreVec (HermitianMetric.standard K (Fin n)) σ (Pi.single i 1)‖ = 1 := by
    nlinarith [sq_nonneg (‖fibreVec (HermitianMetric.standard K (Fin n)) σ (Pi.single i 1)‖ - 1)]
  exact h1

theorem bundleRank_standard (n : ℕ) : bundleRank (HermitianBundle.standard K n) = n :=
  Module.finrank_fin_fun (𝓞 K)

def ShortFamily.standard (n : ℕ) : ShortFamily (HermitianBundle.standard K n) (fun _ ↦ 1) where
  vec i := (Pi.basisFun (𝓞 K) (Fin n) (Fin.cast (bundleRank_standard K n) i) : Fin n → 𝓞 K)
  linearIndependent :=
    (Pi.basisFun (𝓞 K) (Fin n)).linearIndependent.comp _ (Fin.cast_injective _)
  norm_le σ i := by
    rw [Pi.basisFun_apply]
    exact (fibreNorm_standard_single K n σ _).le


variable {K} in
def BoundedInjection.id (E : HermitianBundle K) : BoundedInjection E E (fun _ ↦ 1) where
  toLinearMap := LinearMap.id
  injective := Function.injective_id
  norm_le σ x := by rw [LinearMap.lTensor_id, LinearMap.id_apply, one_mul]

end HadExamples

def LogDetDerivative.Statement : Prop :=
  ∀ (m : ℕ) (G G' : ℝ → Matrix (Fin m) (Fin m) ℂ), (∀ t, (G t).PosDef) →
    (∀ t i j, HasDerivAt (fun s ↦ G s i j) (G' t i j) t) →
    ∀ t, HasDerivAt (fun s ↦ -(1 / 2) * Real.log (G s).det.re)
      (-(1 / 2) * ((G t)⁻¹ * G' t).trace.re) t

def GridSum.Statement : Prop :=
  ∀ D i : ℕ, i ≤ D →
    (fun n : ℕ ↦ (∑ a ∈ Finset.range n,
        (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ (D - i) / ((i.factorial : ℝ) * ((D - i).factorial : ℝ))) -
      (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ D

def unitBallVolume (R : ℕ) : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin R)) 1)).toReal

structure ShortLatticeBasis {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (La : Submodule ℤ V) (c : ℝ) where

  vec : Fin (Module.finrank ℝ V) → V
  mem : ∀ i, vec i ∈ La
  linearIndependent : LinearIndependent ℝ vec
  norm_le : ∀ i, ‖vec i‖ ≤ c

def LatticeCount.Statement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (La : Submodule ℤ V) [DiscreteTopology La]
    [IsZLattice ℝ La] (c b : ℝ), ShortLatticeBasis La c → 0 ≤ b →
      {x : V | x ∈ La ∧ ‖x‖ ≤ b}.Finite ∧
      ({x : V | x ∈ La ∧ ‖x‖ ≤ b}.ncard : ℝ) * ZLattice.covolume La ≤
        unitBallVolume (Module.finrank ℝ V) *
          (b + (Module.finrank ℝ V : ℝ) * c) ^ Module.finrank ℝ V

def SmallBallVolume.Statement : Prop := ∀ R : ℕ, unitBallVolume R ≤ 6

def MinkowskiCount.Statement : Prop :=
  (∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (La : Submodule ℤ V) [DiscreteTopology La]
    [IsZLattice ℝ La] (ρ : ℝ), 0 < ρ →
      Real.log (unitBallVolume (Module.finrank ℝ V)) +
          (Module.finrank ℝ V : ℝ) * Real.log (ρ / 2) - Real.log (ZLattice.covolume La) ≤
        Real.log ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ)) ∧
  ∀ R : ℕ, (2 / Real.sqrt R) ^ R ≤ unitBallVolume R

def Packing.Statement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (La : Submodule ℤ V) [Module.Finite ℤ La]
    (S : Finset V) (b : ℝ), 0 ≤ b → (∀ s ∈ S, s ∈ La) → (∀ s ∈ S, ‖s‖ ≤ 1) →
    (∀ s ∈ S, ∀ t ∈ S, s ≠ t → Real.exp (-b) ≤ ‖s - t‖) →
      Real.log S.card ≤ Module.finrank ℤ La * (b + Real.log 3)

section LatticeExamples

end LatticeExamples

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

