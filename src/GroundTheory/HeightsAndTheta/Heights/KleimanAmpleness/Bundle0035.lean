module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertPrime
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedNumberPolynomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedFiltration
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiltrationHilbSum
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPositive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace HilbertPositive

theorem hilbertPrime : HilbertSamuel.HilbertPrime.Statement.{u} :=
  HilbertSamuel.HilbertPrime.proof HilbertSamuel.HilbertDimZero.proof
    (HilbertSamuel.HilbertIncrement.proof HilbertSamuel.IntersectionRecursion.proof)
    (HilbertSamuel.MixedNumberPolynomial.proof
      (HilbertSamuel.MultigradedHilbertPolynomial.proof HilbertSamuel.EventualPolynomial.proof))
    (HilbertSamuel.ModulesFromPrimes.proof HilbertSamuel.MultigradedFiltration.proof
      HilbertSamuel.FiltrationHilbSum.proof HilbertSamuel.DegLTGrowth.proof)

theorem mixedNumber : HilbertSamuel.MixedNumberPolynomial.Statement.{u} :=
  HilbertSamuel.MixedNumberPolynomial.proof
    (HilbertSamuel.MultigradedHilbertPolynomial.proof HilbertSamuel.EventualPolynomial.proof)

def blockEquiv (N : ℕ) : (Σ _ : Unit, Fin (N + 1)) ≃ Fin (N + 1) where
  toFun v := v.2
  invFun i := ⟨(), i⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

theorem weight_blockWeight_one (d : (Σ _ : Unit, Fin (N + 1)) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) d = fun _ => d.degree := by
  funext u
  rw [Finsupp.weight_apply, Finsupp.degree, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [NumbersDVR.blockWeight]

theorem isWeightedHomogeneous_iff (p : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k) (n : ℕ) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) p (fun _ => n) ↔
      p.IsHomogeneous n := by
  constructor
  · intro h d hd
    have h1 : d.degree = n := congrFun ((weight_blockWeight_one d).symm.trans (h hd)) ()
    rw [← h1, Finsupp.degree_eq_weight_one]
    rfl
  · intro h d hd
    rw [weight_blockWeight_one]
    funext _
    rw [Finsupp.degree_eq_weight_one]
    exact h hd

theorem ringKrullDim_primeOfOne (y : Fin (N + 1) → Ω) :
    ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y) =
      ringKrullDim (Poly k N ⧸ primeOf (S := k) y) := by
  let f : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ≃+* Poly k N :=
    (renameEquiv k (blockEquiv N)).toRingEquiv
  have hc : primeOfOne (S := k) y = (primeOf (S := k) y).comap f.toRingHom :=
    Ideal.ext fun _ => Iff.rfl
  have h : primeOf (S := k) y = (primeOfOne (S := k) y).map f.toRingHom := by
    rw [hc, Ideal.map_comap_of_surjective f.toRingHom f.surjective]
  exact ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ f h)

theorem ne_zero_of_isSubvar {y : Fin (N + 1) → Ω} {e : ℕ} (h : IsSubvar y (primeOf (S := k) y) e) :
    y ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  intro hy
  apply hi
  rw [mem_primeOf_of_isHomogeneous y (isHomogeneous_X k i), aeval_X, hy, Pi.zero_apply]

theorem finrank_piece_eq_hilbFn (y : Fin (N + 1) → Ω) (n : ℕ) :
    (Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℤ) =
      NumbersDVR.hilbFn (primeOfOne (S := k) y) (fun _ => (n : ℤ)) := by
  classical
  rw [NumbersDVR.hilbFn, if_pos (fun _ => Int.natCast_nonneg n)]
  simp only [Int.toNat_natCast]
  congr 1
  set V := weightedHomogeneousSubmodule k (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1)))
    (fun _ : Unit => n) with hV
  let f₁ : V →ₗ[k] NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y :=
    (Ideal.Quotient.mkₐ k (primeOfOne (S := k) y)).toLinearMap ∘ₗ V.subtype
  let f₂ : V →ₗ[k] Ω :=
    (aeval (fun v : Σ _ : Unit, Fin (N + 1) => y v.2)).toLinearMap ∘ₗ V.subtype
  have hhom : ∀ v ∈ V, (oneBlock (S := k) (N := N) v).IsHomogeneous n := fun v hv =>
    ((isWeightedHomogeneous_iff v n).mp ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hv)).rename_isHomogeneous
  have heval : ∀ v, aeval y (oneBlock (S := k) (N := N) v) = aeval (fun w : Σ _ : Unit, Fin (N + 1) => y w.2) v :=
    fun v => by rw [oneBlock, aeval_rename]; rfl
  have hr₁ : LinearMap.range f₁ = NumbersDVR.gradedPiece (primeOfOne (S := k) y) (fun _ => n) := by
    rw [NumbersDVR.gradedPiece, LinearMap.range_comp, Submodule.range_subtype]
  have hr₂ : LinearMap.range f₂ = (coordGraded k y).piece (n : ℤ) := by
    apply le_antisymm
    · rintro _ ⟨⟨v, hv⟩, rfl⟩
      refine Submodule.subset_span ⟨oneBlock (S := k) (N := N) v, n, hhom v hv, rfl, ?_⟩
      exact (heval v).symm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨g, e, hg, he, rfl⟩
      have he' : e = n := by exact_mod_cast he
      subst he'
      refine ⟨⟨rename (blockEquiv N).symm g, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
        ((isWeightedHomogeneous_iff _ e).mpr (hg.rename_isHomogeneous))⟩, ?_⟩
      change aeval (fun v : Σ _ : Unit, Fin (N + 1) => y v.2) (rename (blockEquiv N).symm g) = aeval y g
      rw [aeval_rename]
      rfl
  have hker : LinearMap.ker f₁ = LinearMap.ker f₂ := by
    ext ⟨v, hv⟩
    simp only [LinearMap.mem_ker, f₁, f₂, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    change oneBlock (S := k) (N := N) v ∈ primeOf (S := k) y ↔ _
    rw [mem_primeOf_of_isHomogeneous y (hhom v hv), heval]
  have e₁ := ((f₁.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hker)).trans
    f₂.quotKerEquivRange).finrank_eq
  rw [hr₁, hr₂] at e₁
  exact e₁.symm

end HilbertPositive


open HilbertPositive in
theorem HilbertPositive.proof (hPos : ProjDegreePositive.Statement.{u})
    (hSec : TwistSections.Statement.{u, w}) : HilbertPositive.Statement.{u, w} := by
  intro k _ Ω _ _ N y e he hW
  have hy : y ≠ 0 := ne_zero_of_isSubvar hW
  have hq : NumbersDVR.IsMultiProjPrime (primeOfOne (S := k) y) := isMultiProjPrime_primeOfOne y hy
  have hdim : ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y) =
      ((e + 1 : ℕ) : WithBot ℕ∞) := by
    rw [ringKrullDim_primeOfOne]
    exact hW.dim
  refine ⟨?_, hPos k (Fin (N + 1)) _ e hq hdim, hSec k Ω N y hy⟩
  have hdim' : ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y) =
      ((e + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
    simpa using hdim
  obtain ⟨a₀, C, hC⟩ := hilbertPrime e k Unit (fun _ => Fin (N + 1)) _ hq hdim'
  have hadd := (mixedNumber k Unit (fun _ => Fin (N + 1)) _ e hq hdim').2
  have hhom : ∀ n : ℕ, NumbersDVR.intNum k (primeOfOne (S := k) y)
      (fun _ : Fin e => fun _ : Unit => (n : ℤ)) = (n : ℤ) ^ e *
        NumbersDVR.intNum k (primeOfOne (S := k) y) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) := by
    intro n
    have := HilbertSamuel.RankOfSections.const_nsmul
      (fun bs => NumbersDVR.intNum k (primeOfOne (S := k) y) bs) hadd n (fun _ : Unit => (1 : ℤ))
    have e' : (n • fun _ : Unit => (1 : ℤ)) = fun _ : Unit => (n : ℤ) := by
      funext u
      simp
    rw [e'] at this
    exact this
  refine ⟨|C| * 2 ^ (e - 1), ?_⟩
  filter_upwards [eventually_ge_atTop (max a₀ 1)] with n hn
  have h := hC (fun _ => n) (fun _ => le_of_max_le_left hn)
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  rw [hhom n, ← finrank_piece_eq_hilbFn] at h
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hpow : ((n : ℝ) + 1) ^ ((e : ℝ) - 1) ≤ 2 ^ (e - 1) * (n : ℝ) ^ (e - 1) := by
    rw [show (e : ℝ) - 1 = ((e - 1 : ℕ) : ℝ) by rw [Nat.cast_sub he]; simp, Real.rpow_natCast,
      ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  calc |(Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℝ) -
        (NumbersDVR.intNum k (primeOfOne (S := k) y) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) : ℝ) *
          (n : ℝ) ^ e / (e.factorial : ℝ)|
      = |(((Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℤ)) : ℝ) -
          (((n : ℤ) ^ e * NumbersDVR.intNum k (primeOfOne (S := k) y)
            (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) : ℤ) : ℝ) / (e.factorial : ℝ)| := by
        push_cast
        ring_nf
    _ ≤ C * ((n : ℝ) + 1) ^ ((e : ℝ) - 1) := h
    _ ≤ |C| * ((n : ℝ) + 1) ^ ((e : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 ^ (e - 1) * (n : ℝ) ^ (e - 1)) := mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
    _ = |C| * 2 ^ (e - 1) * (n : ℝ) ^ (e - 1) := by ring

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeBadFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

theorem KHFreeBadFinite.full : KHFreeBadFinite.Statement := by
  intro K _ ι _ e
  refine (Set.Finite.pi (t := fun p : (Σ k, ι k) => Set.Icc (-|e p.1|) |e p.1|)
    (fun p => Set.finite_Icc _ _)).subset ?_
  rintro a ⟨hsum, hneg⟩ ⟨k, i⟩ -
  show a ⟨k, i⟩ ∈ Set.Icc (-|e k|) |e k|
  rw [Set.mem_Icc, ← abs_le]
  have hs : ∑ j, a ⟨k, j⟩ = e k := congrFun hsum k
  rcases hneg k with h | h
  · have hnn : ∀ j, 0 ≤ a ⟨k, j⟩ := by
      intro j
      by_contra hj
      have hj2 : a ⟨k, j⟩ < 0 := lt_of_not_ge hj
      have hj' : j ∈ negSet a k := by simp [negSet, hj2]
      rw [h] at hj'
      simp at hj'
    have h1 : a ⟨k, i⟩ ≤ ∑ j, a ⟨k, j⟩ :=
      Finset.single_le_sum (f := fun j => a ⟨k, j⟩) (fun j _ => hnn j) (Finset.mem_univ i)
    rw [abs_of_nonneg (hnn i)]
    linarith [le_abs_self (e k)]
  · have hng : ∀ j, a ⟨k, j⟩ < 0 := by
      intro j
      have hj : j ∈ negSet a k := by rw [h]; exact Finset.mem_univ j
      simpa [negSet] using hj
    have h1 : -a ⟨k, i⟩ ≤ ∑ j, -a ⟨k, j⟩ :=
      Finset.single_le_sum (f := fun j => -a ⟨k, j⟩) (fun j _ => by linarith [hng j])
        (Finset.mem_univ i)
    rw [Finset.sum_neg_distrib] at h1
    rw [abs_of_neg (hng i)]
    linarith [neg_abs_le (e k)]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeDecomp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

namespace KHFreeDecomp

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cellMon_monomial {I : ∀ k, Finset (ι k)} {t : MRingOver S ι} (ht : t ∈ KH.cellMon S I) :
    ∃ u : (Σ k, ι k) →₀ ℕ, t = monomial u 1 ∧ ∀ q ∈ u.support, q.2 ∈ I q.1 := by
  classical
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    refine ⟨Finsupp.single ⟨k, i⟩ 1, rfl, fun q hq => ?_⟩
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hq)]
    exact hi
  | one => exact ⟨0, by rw [← C_1, C_apply], by simp⟩
  | mul f g _ _ hf hg =>
    obtain ⟨u, rfl, hu⟩ := hf
    obtain ⟨v, rfl, hv⟩ := hg
    refine ⟨u + v, by rw [monomial_mul, one_mul], fun q hq => ?_⟩
    rcases Finset.mem_union.mp (Finsupp.support_add hq) with h | h
    · exact hu q h
    · exact hv q h

section Frac

variable {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

def overDen (T : Submonoid (MRingOver S ι)) (t : T) : M →ₗ[S] LocalizedModule T M where
  toFun m := LocalizedModule.mk m t
  map_add' x y := by
    simp only [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_add]
  map_smul' s m := by
    rw [RingHom.id_apply, LocalizedModule.smul'_mk]

theorem overDen_apply (T : Submonoid (MRingOver S ι)) (t : T) (m : M) :
    overDen T t m = LocalizedModule.mk m t := rfl

end Frac

theorem quot_mk_smul (s : S) (p : MRingOver S ι) :
    Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (s • p) = s • Ideal.Quotient.mk ⊥ p := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap]

theorem mk_monomial_eq (I : ∀ k, Finset (ι k)) (u v : (Σ k, ι k) →₀ ℕ) (hu : ∀ q ∈ u.support, q.2 ∈ I q.1)
    (ht : (monomial u (1 : S) : MRingOver S ι) ∈ KH.cellMon S I) :
    LocalizedModule.mk (Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (monomial v 1)) ⟨monomial u 1, ht⟩ =
      monoFrac S I (fun q => (v q : ℤ) - u q) := by
  classical
  have hneg : ∀ k, negSet (fun q => (v q : ℤ) - u q) k ⊆ I k := by
    intro k i hi
    simp only [negSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hu ⟨k, i⟩ (Finsupp.mem_support_iff.mpr (by omega))
  have hexp : negExp (fun q => (v q : ℤ) - u q) + v = u + posExp (fun q => (v q : ℤ) - u q) := by
    ext q
    simp only [Finsupp.add_apply, posExp, negExp, Finsupp.coe_equivFunOnFinite_symm]
    omega
  rw [monoFrac, dite_eq_left hneg, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    monomial_mul, mul_one]
  rw [hexp]

theorem locPart_le (I : ∀ k, Finset (ι k)) (c d : K → ℤ) :
    KH.locPart ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) (KH.cellMon S I) c ≤
      Submodule.span S (monoFrac S I '' {a | blockSum a = c + d}) := by
  classical
  rcases subsingleton_or_nontrivial S with hS | hS
  · intro x _
    have hx : x = 0 := by rw [← one_smul S x, Subsingleton.elim (1 : S) 0, zero_smul]
    rw [hx]
    exact zero_mem _
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, ⟨t, ht⟩, b, htb, hm, rfl⟩
  obtain ⟨u, rfl, huI⟩ := cellMon_monomial ht
  have hub : ∀ k, ∑ i, u ⟨k, i⟩ = b k := by
    intro k
    refine htb u ?_ k
    rw [support_monomial, if_neg one_ne_zero]
    exact Finset.mem_singleton_self u
  have hle : KH.quotPart S (⊥ : Ideal (MRingOver S ι)) ((c + fun k => (b k : ℤ)) + d) ≤
      (Submodule.span S (monoFrac S I '' {a | blockSum a = c + d})).comap
        (overDen (KH.cellMon S I) ⟨monomial u 1, ht⟩) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, ⟨hpos, hp⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have hsum : p = ∑ v ∈ p.support, AddMonoidAlgebra.coeff p v • (monomial v 1 : MRingOver S ι) := by
      conv_lhs => rw [p.as_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [smul_monomial, smul_eq_mul, mul_one]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    rw [quot_mk_smul, map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun q => (v q : ℤ) - u q, ?_, ?_⟩)
    · have hv' := hp v hv
      show blockSum _ = c + d
      funext k
      simp only [blockSum, Finset.sum_sub_distrib]
      have h1 : ∑ i, ((v ⟨k, i⟩ : ℕ) : ℤ) = ((((c + fun k => (b k : ℤ)) + d) k).toNat : ℤ) := by
        exact_mod_cast hv' k
      have h2 : ∑ i, ((u ⟨k, i⟩ : ℕ) : ℤ) = b k := by exact_mod_cast hub k
      have h3 := hpos k
      simp only [Pi.add_apply] at h1 h3 ⊢
      omega
    · rw [overDen_apply, mk_monomial_eq I u v huI ht]
  exact hle hm

theorem embed_apply_cell [LinearOrder K] [∀ k, LinearOrder (ι k)] (a : (Σ k, ι k) → ℤ) (n : ℕ)
    (F : KH.Cell K ι n → S) (I : KH.Cell K ι n) :
    embed S a n (fun J => F J.1) I = F I • monoFrac S I.1 a := by
  classical
  unfold embed
  rw [LinearMap.pi_apply]
  split_ifs with h
  · rfl
  · rw [LinearMap.zero_apply, monoFrac, dite_eq_right h, smul_zero]

end KHFreeDecomp


open KHFreeDecomp in
theorem KHFreeDecomp.full : KHFreeDecomp.Statement := by
  intro S _ K _ _ ι _ _ c d n φ hφ
  classical
  have hI : ∀ I : KH.Cell K ι n, ∃ l : ((Σ k, ι k) → ℤ) →₀ S,
      l ∈ Finsupp.supported S S {a | blockSum a = c + d} ∧
        Finsupp.linearCombination S (monoFrac S I.1) l = φ I := by
    intro I
    have hx : φ I ∈ KH.locPart ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d))
        (KH.cellMon S I.1) c := hφ I (Set.mem_univ _)
    exact (Finsupp.mem_span_image_iff_linearCombination S).mp (locPart_le I.1 c d hx)
  choose l hl hlφ using hI
  let _ : Fintype (KH.Cell K ι n) := by unfold KH.Cell; infer_instance
  refine ⟨Finset.univ.biUnion fun I => (l I).support, fun a J => l J.1 a, ?_, ?_⟩
  · intro a ha
    obtain ⟨I, -, haI⟩ := Finset.mem_biUnion.mp ha
    exact hl I haI
  · funext I
    rw [Finset.sum_apply, ← hlφ I, Finsupp.linearCombination_apply, Finsupp.sum]
    beta_reduce
    refine (Finset.sum_subset (s₁ := (l I).support) (s₂ := Finset.univ.biUnion fun I => (l I).support)
      (f := fun a => l I a • monoFrac S I.1 a) (fun a ha => Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ _, ha⟩) ?_).trans
      (Finset.sum_congr rfl fun a _ => (embed_apply_cell a n (fun J => l J a) I).symm)
    intro a _ ha
    rw [Finsupp.mem_support_iff, not_not] at ha
    rw [ha, zero_smul]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreJoin
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver GeneratesOver)

def segreJoin {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) :
    (Σ k, Sum.elim (fun _ : Unit => ∀ k, ι k) ι k) → Ω :=
  IndefiniteRowSideFullHecke.Kleiman2.joinVec (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (NumbersDVR.segreVec y)) y

def SegreBase.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S (segreJoin y) (Sum.inl ()) ∧
      (∀ β : K → ℤ, secOver S (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) = secOver S y β) ∧
      ∀ (β : K → ℤ) (n : ℕ) (η : Fin n → Ω),
        GeneratesOver S (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) η ↔ GeneratesOver S y β η

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

