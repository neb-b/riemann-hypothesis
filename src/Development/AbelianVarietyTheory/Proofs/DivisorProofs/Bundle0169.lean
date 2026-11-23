module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0102
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0078
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0104

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatIntOfIsIntegral
section
open GlobalTheory.LKTorus

namespace GlobalTheory

lemma LKTorus.rat_int_of_isIntegral {q : ℚ} (h : IsIntegral ℤ q) : ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨n, by simpa using hn⟩

theorem LKTorus.simT_integral_finite (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L)
    (hc : ∀ (τ : L →+* ℂ) (x : L), τ (c x) = (starRingEnd ℂ) (τ x)) :
    {x : Lˣ | x ∈ simT ℚ c ∧ IsIntegral ℤ (x : L) ∧ IsIntegral ℤ ((x⁻¹ : Lˣ) : L)}.Finite := by
  have hF := NumberField.Embeddings.finite_of_norm_le L ℂ 1
  refine (hF.preimage (Set.injOn_of_injective Units.val_injective)).subset ?_
  rintro x ⟨⟨t, ht⟩, hx, hxi⟩
  have hinv : x⁻¹ ∈ simT ℚ c := (simT ℚ c).inv_mem ⟨t, ht⟩
  obtain ⟨t', ht'⟩ := hinv
  have hcint : ∀ y : L, IsIntegral ℤ y → IsIntegral ℤ (c y) := fun y hy =>
    hy.map (c.toRingHom.toIntAlgHom)
  have hinj : Function.Injective (algebraMap ℚ L) := (algebraMap ℚ L).injective
  have htI : IsIntegral ℤ ((t : ℚ)) := by
    rw [← isIntegral_algebraMap_iff (B := L), ← ht]
    exact hx.mul (hcint _ hx)
  have ht'I : IsIntegral ℤ ((t' : ℚ)) := by
    rw [← isIntegral_algebraMap_iff (B := L), ← ht']
    exact hxi.mul (hcint _ hxi)
  obtain ⟨n, hn⟩ := LKTorus.rat_int_of_isIntegral htI
  obtain ⟨m, hm⟩ := LKTorus.rat_int_of_isIntegral ht'I
  have hprod : (t : ℚ) * t' = 1 := by
    apply hinj
    rw [map_mul, ← ht, ← ht', map_one]
    have h1 : ((x⁻¹ : Lˣ) : L) * (x : L) = 1 := by simp
    calc (x : L) * c x * (((x⁻¹ : Lˣ) : L) * c ((x⁻¹ : Lˣ) : L))
        = (((x⁻¹ : Lˣ) : L) * (x : L)) * c (((x⁻¹ : Lˣ) : L) * (x : L)) := by rw [map_mul]; ring
      _ = 1 := by rw [h1, map_one, one_mul]
  have hnm : n * m = 1 := by
    have : ((n * m : ℤ) : ℚ) = 1 := by push_cast; rw [hn, hm, hprod]
    exact_mod_cast this
  refine ⟨hx, fun τ => ?_⟩
  have hτ : ((‖τ x‖ ^ 2 : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
    have e := congrArg τ ht
    rw [map_mul, hc, Complex.mul_conj, Complex.normSq_eq_norm_sq, eq_ratCast, map_ratCast, ← hn] at e
    rw [e]; push_cast; rfl
  have hτ' : ‖τ x‖ ^ 2 = (n : ℝ) := by exact_mod_cast hτ
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hnm with h | h
  · rw [h] at hτ'
    have h0 : 0 ≤ ‖τ x‖ := norm_nonneg _
    push_cast at hτ'
    nlinarith
  · rw [h] at hτ'
    push_cast at hτ'
    nlinarith [sq_nonneg ‖τ x‖]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatrixEigenspaceImageSpannedRational
section
open NumberField

namespace GlobalTheory.RationalSpan


open Classical in
theorem expand {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ} {s : Type}
    (b : Module.Basis s K L) (v : Fin n → L) :
    v = ∑ j ∈ Finset.univ.biUnion (fun i => (b.repr (v i)).support),
      b j • (fun i => algebraMap K L (b.repr (v i) j)) := by
  funext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  conv_lhs => rw [← b.linearCombination_repr (v i)]
  rw [Finsupp.linearCombination_apply]
  rw [Finsupp.sum_of_support_subset _ (s := Finset.univ.biUnion (fun i => (b.repr (v i)).support))]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Algebra.smul_def, mul_comm]
  · intro j hj
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩
  · intro j _
    simp

theorem repr_coord {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ} {s : Type}
    (b : Module.Basis s K L) (a : Fin n → K) (y : Fin n → L) (j : s) :
    b.repr (∑ k, algebraMap K L (a k) * y k) j = ∑ k, a k * b.repr (y k) j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [← Algebra.smul_def, map_sum, Finsupp.finsetSum_apply]

theorem map_mulVec_comp {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    (M.map (algebraMap K L)).mulVec (fun i => algebraMap K L (x i)) =
      fun i => algebraMap K L (M.mulVec x i) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap K L) M x i).symm

end GlobalTheory.RationalSpan

theorem GlobalTheory.rational_eigen_image_span : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K) (lam : ι → K) (e : Matrix (Fin n) (Fin n) K), (∀ y : Fin n → L, (∀ p, ((A p).map (algebraMap K L)).mulVec y = algebraMap K L (lam p) • y) ↔ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' {x : Fin n → K | ∀ p, (A p).mulVec x = lam p • x})) ∧ ∀ y : Fin n → L, y ∈ LinearMap.range (e.map (algebraMap K L)).mulVecLin ↔ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (LinearMap.range e.mulVecLin : Set (Fin n → K))) := by
  intro K L _ _ _ n ι A lam e
  classical
  let b := Module.Basis.ofVectorSpace K L
  let f := algebraMap K L
  refine ⟨fun y => ⟨fun h => ?_, fun h => ?_⟩, fun y => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [GlobalTheory.RationalSpan.expand b y]
    refine Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩))
    intro p
    funext i
    have h1 := congrArg (fun z => b.repr z j) (congrFun (h p) i)
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [GlobalTheory.RationalSpan.repr_coord] at h1
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [h1, ← Algebra.smul_def]
    simp
  · let W : Submodule L (Fin n → L) :=
      { carrier := {y | ∀ p, ((A p).map f).mulVec y = f (lam p) • y}
        add_mem' := by
          intro a c ha hc p
          simp only [Set.mem_setOf_eq] at *
          rw [Matrix.mulVec_add, ha p, hc p, smul_add]
        zero_mem' := by
          intro p
          simp
        smul_mem' := by
          intro c a ha p
          simp only [Set.mem_setOf_eq] at *
          rw [Matrix.mulVec_smul, ha p, smul_comm] }
    have hle : Submodule.span L ((fun x i => f (x i)) '' {x : Fin n → K | ∀ p, (A p).mulVec x = lam p • x}) ≤ W := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩ p
      rw [GlobalTheory.RationalSpan.map_mulVec_comp, hx p]
      funext i
      simp [f, Algebra.smul_def]
    exact hle h
  · obtain ⟨z, rfl⟩ := h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GlobalTheory.RationalSpan.expand b z, map_sum]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    rw [map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.mulVec (fun i => b.repr (z i) j), ⟨_, rfl⟩, ?_⟩)
    rw [Matrix.mulVecLin_apply, GlobalTheory.RationalSpan.map_mulVec_comp]
  · have hle : Submodule.span L ((fun x i => f (x i)) '' (LinearMap.range e.mulVecLin : Set (Fin n → K))) ≤ LinearMap.range (e.map f).mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨x, ⟨w, rfl⟩, rfl⟩
      exact ⟨fun i => f (w i), by rw [Matrix.mulVecLin_apply, GlobalTheory.RationalSpan.map_mulVec_comp]; rfl⟩
    exact hle h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealIndependentSkewMatrices
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem linearIndependent_of_skew_of_real : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {r n : ℕ} (G : Matrix (Fin r) (Fin r) E), G.det ≠ 0 →
    ∀ e : Fin n → Matrix (Fin r) (Fin r) E, (∀ i, (e i)ᵀ * G + G * (e i).map cc = 0) →
    LinearIndependent (maximalRealSubfield E) e → LinearIndependent E e := by
  intro E _ _ _ r n G hG e he hF
  have cc_mul' : ∀ x y : E, cc (x * y) = cc x * cc y := fun x y => map_mul (IsCMField.complexConj E) x y
  have cc_add' : ∀ x y : E, cc (x + y) = cc x + cc y := fun x y => map_add (IsCMField.complexConj E) x y
  have cc_cc' : ∀ x : E, cc (cc x) = x := fun x => IsCMField.complexConj_apply_apply E x

  have hmap : ∀ g : Fin n → E, (∑ i, g i • e i).map cc = ∑ i, cc (g i) • (e i).map cc := by
    intro g
    ext a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.sum_apply, cc, map_sum]
  have hinj : ∀ M : Matrix (Fin r) (Fin r) E, Mᵀ * G = 0 → M = 0 := by
    intro M hM
    have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
    have h0 : Mᵀ = 0 := by
      have := congrArg (· * G⁻¹) hM
      simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv G hu] using this
    simpa using congrArg Matrix.transpose h0
  have key : ∀ g : Fin n → E, ∑ i, g i • e i = 0 → ∑ i, cc (g i) • e i = 0 := by
    intro g hg
    apply hinj
    have h2 : G * (∑ i, g i • e i).map cc = 0 := by
      rw [hg]
      ext a b
      simp [Matrix.mul_apply, cc]
    rw [hmap, Finset.mul_sum] at h2
    have h3 : (∑ i, cc (g i) • e i)ᵀ * G = - ∑ i, G * (cc (g i) • (e i).map cc) := by
      rw [Matrix.transpose_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_neg]
      congr 1
      exact eq_neg_of_add_eq_zero_left (he i)
    rw [h3, h2, neg_zero]

  have real : ∀ g : Fin n → E, (∀ i, cc (g i) = g i) → ∑ i, g i • e i = 0 → ∀ i, g i = 0 := by
    intro g hc hg i
    have hm : ∀ i, g i ∈ maximalRealSubfield E := fun i =>
      (IsCMField.complexConj_eq_self_iff E _).mp (hc i)
    have := Fintype.linearIndependent_iff.mp hF (fun i => ⟨g i, hm i⟩) hg i
    simpa using congrArg (Subtype.val) this
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one E)
  have hx' : cc x ≠ x := hx

  have sum_real : ∀ g : Fin n → E, ∑ i, g i • e i = 0 → ∀ i, g i + cc (g i) = 0 := by
    intro g hg
    apply real
    · intro i
      rw [cc_add', cc_cc', add_comm]
    · simp only [add_smul, Finset.sum_add_distrib, hg, key g hg, add_zero]
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 := sum_real g hg i
  have hxg : ∑ i, (x * g i) • e i = 0 := by
    simp only [mul_smul, ← Finset.smul_sum, hg, smul_zero]
  have h2 := sum_real (fun i => x * g i) hxg i
  simp only [cc_mul'] at h2
  have h3 : cc (g i) = - g i := eq_neg_of_add_eq_zero_right h1
  rw [h3] at h2
  have h4 : (x - cc x) * g i = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hx'
  · exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexInfConjEqFinprodRestrictedProductStatement
section
open Filter
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_inf_conj_eq_finprod_restrictedProduct : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (K T C : Subgroup G) (KH TH CH : ∀ i, Subgroup (H i)) (g : G), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) → (∀ x, x ∈ C ↔ x ∈ T ∧ ∀ i, p i x ∈ CH i) → (∀ i, CH i ≤ TH i) → (∀ i, TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom ≤ CH i ∧ (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) ≠ 0) → (∀ᶠ i in cofinite, CH i ≤ KH i) → (T ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex C = ∏ᶠ i, (TH i ⊓ (KH i).map (MulAut.conj (p i g)).toMonoidHom).relIndex (CH i) := by
  first | exact @GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product | exact GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product | (intros; apply GlobalTheory.relIndex_inf_conj_eq_finprod_of_restricted_product <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
section
noncomputable section

open NumberField nonZeroDivisors

namespace GlobalTheory.LipschitzTR

variable (F : Type) [Field F] [NumberField F]

abbrev RSp := EuclideanSpace ℝ (F →+* ℝ)

def remb : F →+ RSp F where
  toFun a := WithLp.toLp 2 (fun τ : F →+* ℝ => τ a)
  map_zero' := by ext τ; simp
  map_add' a b := by ext τ; simp

variable {F}

@[simp] theorem remb_apply (a : F) (τ : F →+* ℝ) : remb F a τ = τ a := rfl

def latOf (N : FractionalIdeal (𝓞 F)⁰ F) : Submodule ℤ (RSp F) :=
  Submodule.map (remb F).toIntLinearMap ((N : Submodule (𝓞 F) F).restrictScalars ℤ)

theorem mem_latOf (N : FractionalIdeal (𝓞 F)⁰ F) (x : RSp F) :
    x ∈ latOf N ↔ ∃ a ∈ N, remb F a = x := by
  simp [latOf]

def phi1 (k : ℕ) (w : ℂ) (t : ℝ) : ℂ :=
  if 0 < (SignType.sign w.im : ℝ) * t then
    ((|t| ^ (k - 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t * w)
  else 0

def Phi (k : ℕ) (z : (F →+* ℝ) → ℂ) (ξ : RSp F) : ℂ :=
  ∏ τ : F →+* ℝ, phi1 k (z τ) (ξ τ)

end GlobalTheory.LipschitzTR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepNeZero
section
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.SlopeTestRemainingChoices.EisFibre

variable {F : Type} [Field F] [NumberField F]

def NzElt (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : Type :=
  {b : F // b ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧ b ≠ 0}

def unitRel (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : Setoid (NzElt 𝔟) where
  r p q := ∃ ε : (𝓞 F)ˣ, q.1 = ((ε : 𝓞 F) : F) * p.1
  iseqv :=
    { refl := fun _ => ⟨1, by simp⟩
      symm := fun {p q} ⟨ε, h⟩ => ⟨ε⁻¹, by rw [h, ← mul_assoc, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.unit_inv_mul, one_mul]⟩
      trans := fun {p q r} ⟨ε, h⟩ ⟨ε', h'⟩ => ⟨ε' * ε, by rw [h', h, ← mul_assoc]; simp⟩ }

def NzCls (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : Type := Quotient (unitRel 𝔟)

def rep {𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} (β : NzCls 𝔟) : F := (Quotient.out β : NzElt 𝔟).1

theorem rep_mem {𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} (β : NzCls 𝔟) : rep β ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) :=
  (Quotient.out β : NzElt 𝔟).2.1

theorem rep_ne_zero {𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} (β : NzCls 𝔟) : rep β ≠ 0 :=
  (Quotient.out β : NzElt 𝔟).2.2

def posCone (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (b : F) : Type :=
  {ν : F // ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ τ : F →+* ℝ, 0 < τ (ν * b)}

end GlobalTheory.SlopeTestRemainingChoices.EisFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentativeParametricIntegralContinuousFamily
section
open MeasureTheory
open scoped ContDiff

namespace GlobalTheory.LocRep

theorem rep_parametric_integral : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ι : K → G → ℂ), (∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) → (∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) → ∀ (T : Type) [TopologicalSpace T] [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [IsLocallyFiniteMeasure ν] (Q : Set T) (w : T → K) (φ : T → G → ℂ), IsCompact Q → Continuous w → Continuous (Function.uncurry φ) → (∀ t, ι (w t) =ᵐ[μ] φ t) → (Continuous fun x => ∫ t in Q, φ t x ∂ν) ∧ ι (∫ t in Q, w t ∂ν) =ᵐ[μ] fun x => ∫ t in Q, φ t x ∂ν := by
  intro G _ _ _ _ _ _ _ _ μ _ K _ _ _ ι hloc hlin T _ _ _ _ _ ν _ Q w φ hQ hw hφ hrep
  have hcont : Continuous fun x => ∫ t in Q, φ t x ∂ν :=
    continuous_parametric_integral_of_continuous (f := fun x t => φ t x)
      (hφ.comp continuous_swap) hQ
  refine ⟨hcont, rep_of_pairing hloc hcont.locallyIntegrable fun C hC => ?_⟩
  obtain ⟨Λ, hΛ⟩ := exists_pairing hloc hlin hC
  have hwi : IntegrableOn w Q ν := hw.continuousOn.integrableOn_compact hQ
  have hint : Integrable (Function.uncurry φ) ((ν.restrict Q).prod (μ.restrict C)) := by
    rw [Measure.prod_restrict]
    exact hφ.continuousOn.integrableOn_compact (hQ.prod hC)
  rw [← hΛ, ← Λ.integral_comp_comm hwi, ← integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [hΛ]
  exact integral_congr_ae (ae_restrict_of_ae (hrep t))

end GlobalTheory.LocRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsKillIdeal
section
noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PtClosed

def killIdeal {A : Type} [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop) :
    Ideal A where
  carrier := {a | ∀ (R' : Type) [CommRing R'] (f : A →+* R'), Q R' f → f a = 0}
  add_mem' {a b} ha hb R' _ f hf := by rw [map_add (f := _), ha R' f hf, hb R' f hf, add_zero]
  zero_mem' R' _ f _ := map_zero f
  smul_mem' c a ha R' _ f hf := by rw [smul_eq_mul, map_mul, ha R' f hf, mul_zero]

def Represents {A : Type} [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop)
    (J : Ideal A) : Prop :=
  ∀ (R' : Type) [CommRing R'] (f : A →+* R'), Q R' f ↔ J ≤ RingHom.ker f

def ptQ {S : Scheme.{0}} (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop) (V : S.Opens)
    (hV : IsAffineOpen V) : ∀ (R' : Type) [CommRing R'], (Γ(S, V) →+* R') → Prop :=
  fun R' _ f ↦ P R' (spMap f ≫ hV.fromSpec)

theorem killIdeal_eq {A : Type} [CommRing A]
    {Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop} {J : Ideal A} (h : Represents Q J) :
    killIdeal Q = J := by
  apply le_antisymm
  · intro a ha
    have := ha (A ⧸ J) (Ideal.Quotient.mk J) ((h _ _).2 (by simp [Ideal.mk_ker]))
    simpa [Ideal.Quotient.eq_zero_iff_mem] using this
  · intro a ha R' _ f hf
    exact (h R' f).1 hf ha

theorem represents_killIdeal {A : Type} [CommRing A]
    {Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop} {J : Ideal A} (h : Represents Q J) :
    Represents Q (killIdeal Q) := by
  rw [killIdeal_eq h]; exact h

theorem represents_restrict : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop)
  (U W : S.Opens) (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U) (J : Ideal Γ(S, U)),
  Represents (ptQ P U hU) J → Represents (ptQ P W hW) (J.map (S.presheaf.map (homOfLE h).op).hom) := by
  intro S P U W hU hW h J hJ R' _ f
  have e : spMap f ≫ hW.fromSpec =
      spMap (f.comp (S.presheaf.map (homOfLE h).op).hom) ≫ hU.fromSpec := by
    rw [← hU.map_fromSpec hW (homOfLE h).op]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom]
  show P R' (spMap f ≫ hW.fromSpec) ↔ _
  rw [e, Ideal.map_le_iff_le_comap, RingHom.comap_ker]
  exact hJ R' _

end GlobalTheory.PtClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldAtPrimeIsSepClosedOfFiniteTypeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueField_atPrime_isSepClosed_of_finiteType : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B] (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) := by
  first | (exact @GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType) | (exact GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType) | (intros; apply GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendOfIsIntegralIsAlgClosedStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_extend_of_isIntegral_of_isAlgClosed : ∀ (A C K : Type) [CommRing A] [CommRing C] [Algebra A C] [Algebra.IsIntegral A C] [Field K] [IsAlgClosed K] (h : A →+* K), RingHom.ker (algebraMap A C) ≤ RingHom.ker h → ∃ ψ : C →+* K, ψ.comp (algebraMap A C) = h := by
  first | exact @GlobalTheory.ringHom_extend_of_isIntegral_isAlgClosed | exact GlobalTheory.ringHom_extend_of_isIntegral_isAlgClosed | (intros; apply GlobalTheory.ringHom_extend_of_isIntegral_isAlgClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOfIntegersTraceMulLeftNondegenerateStatement
section
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringOfIntegers_eq_zero_of_trace_mulLeft_eq_zero : ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K), (∀ y : 𝓞 K, LinearMap.trace ℤ (𝓞 K) (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0 := by
  first | (exact @GlobalTheory.ringOfIntegers_trace_mulLeft_nondegenerate) | (exact GlobalTheory.ringOfIntegers_trace_mulLeft_nondegenerate) | (intros; apply GlobalTheory.ringOfIntegers_trace_mulLeft_nondegenerate  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeTheoreticallyDominantOfGermInjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schemeTheoreticallyDominant_of_germ_injective : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens),
    (∀ (U : X.Opens) (V : T.Opens), IsAffineOpen U → IsAffineOpen V → U ≤ p ⁻¹ᵁ V →
      ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) → b = 0) →
    IsSchemeTheoreticallyDominant W.ι := by
  first | exact @GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine | exact GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine | (intros; apply GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine <;> assumption)
end

