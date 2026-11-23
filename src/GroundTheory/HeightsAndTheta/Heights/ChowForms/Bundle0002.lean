module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PLinearFormPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem linearForm_coeff_single {F : Type} [Field F] {n : ℕ} (a : Fin n → F) (i : Fin n) :
    (∑ m, X m * C (a m) : MvPolynomial (Fin n) F).coeff (Finsupp.single i 1) = a i := by
  classical
  rw [coeff_sum, Finset.sum_eq_single i]
  · rw [mul_comm, coeff_C_mul, coeff_X]
    simp
  · intro j _ hji
    rw [mul_comm, coeff_C_mul, coeff_X, if_neg, mul_zero]
    intro h
    exact hji ((Finsupp.single_left_inj one_ne_zero).mp h)
  · simp

theorem LinearFormPrime.proof : LinearFormPrime.Statement := by
  intro F _ n a ha
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  refine Irreducible.prime (irreducible_of_totalDegree_eq_one ?_ ?_)
  · apply le_antisymm
    · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m _ => ?_)
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X, totalDegree_C]
    · have hs : Finsupp.single i 1 ∈ (∑ m, X m * C (a m) : MvPolynomial (Fin n) F).support := by
        rw [mem_support_iff, linearForm_coeff_single]
        exact hi
      simpa using le_totalDegree hs
  · intro x hx
    have h := hx (Finsupp.single i 1)
    rw [linearForm_coeff_single] at h
    refine isUnit_iff_ne_zero.mpr ?_
    rintro rfl
    exact hi (zero_dvd_iff.mp h)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PMapDvdDescent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem MapDvdDescent.proof : MapDvdDescent.Statement := by
  classical
  intro K Ω _ _ _ σ f g ⟨G, hG⟩
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K Ω)
    (LinearMap.ker_eq_bot.mpr (algebraMap K Ω).injective)
  have hπa : ∀ a : K, π (algebraMap K Ω a) = a := fun a => by
    simpa using LinearMap.congr_fun hπ a
  have hπm : ∀ (a : K) (y : Ω), π (algebraMap K Ω a * y) = a * π y := fun a y => by
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

  let Φ : MvPolynomial σ K := ∑ s ∈ G.support, monomial s (π (AddMonoidAlgebra.coeff G s))
  have hΦ : ∀ s, AddMonoidAlgebra.coeff Φ s = π (AddMonoidAlgebra.coeff G s) := fun s => by
    simp only [Φ, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.mp h, map_zero]
  refine ⟨Φ, ?_⟩
  ext s
  have h1 := congrArg (fun P => π (AddMonoidAlgebra.coeff P s)) hG
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_map, hπa, coeff_mul, map_sum, hπm] at h1
  rw [h1, coeff_mul]
  exact Finset.sum_congr rfl fun x _ => by rw [hΦ]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PNormFormDvd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem NormFormDvd.proof (h₁ : NormFormEmbeddings.Statement) (h₂ : LinearFormPrime.Statement)
    (h₃ : MapDvdDescent.Statement) : NormFormDvd.Statement := by
  intro K L _ _ _ _ _ _ n η t P hgen ht hdvd
  classical
  apply h₃ K (AlgebraicClosure K) (Fin n)
  rw [h₁ K L (AlgebraicClosure K) n η]
  set θ : (L →ₐ[K] AlgebraicClosure K) → MvPolynomial (Fin n) (AlgebraicClosure K) :=
    fun σ => ∑ m, X m * C (σ (η m)) with hθ

  have hev : ∀ σ, eval (fun m => algebraMap K (AlgebraicClosure K) (t m)) (θ σ) = 1 := by
    intro σ
    have h := congrArg σ ht
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_one, Algebra.smul_def, map_mul, AlgHom.commutes] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [hθ, map_sum, mul_comm] using h

  have hcoord : ∀ σ m, eval (Pi.single m 1) (θ σ) = σ (η m) := by
    intro σ m
    simp [hθ, Pi.single_apply]
  have hprime : ∀ σ, Prime (θ σ) := by
    intro σ
    refine h₂ (AlgebraicClosure K) n (fun m => σ (η m)) ?_
    intro h0
    have h := hev σ
    have hz : θ σ = 0 := by simp only [hθ]; simp [funext_iff] at h0; simp [h0]
    rw [hz, map_zero] at h
    exact zero_ne_one h
  have hdiv : ∀ σ, θ σ ∣ map (algebraMap K (AlgebraicClosure K)) P := by
    intro σ
    obtain ⟨Q, hQ⟩ := hdvd
    refine ⟨map (σ : L →+* AlgebraicClosure K) Q, ?_⟩
    have h := congrArg (map (σ : L →+* AlgebraicClosure K)) hQ
    rw [map_map, AlgHom.comp_algebraMap, map_mul] at h
    rw [h]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hθ, map_sum]
  have hinj : ∀ a b, θ a ∣ θ b → a = b := by
    intro a b hab
    obtain ⟨u, hu⟩ := (hprime a).associated_of_dvd (hprime b) hab
    obtain ⟨c, -, hc⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
    rw [hc] at hu
    have h1 := congrArg (eval (fun m => algebraMap K (AlgebraicClosure K) (t m))) hu
    rw [eval_mul, hev, hev, eval_C, one_mul] at h1
    rw [h1, C_1, mul_one] at hu
    refine AlgHom.ext_of_adjoin_eq_top hgen ?_
    rintro _ ⟨m, rfl⟩
    rw [← hcoord a m, ← hcoord b m, hu]
  have key : ∀ s : Finset (L →ₐ[K] AlgebraicClosure K),
      ∏ σ ∈ s, θ σ ∣ map (algebraMap K (AlgebraicClosure K)) P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      obtain ⟨R, hR⟩ := ih
      have h := hdiv a
      rw [hR] at h
      rcases (hprime a).dvd_or_dvd h with h' | h'
      · exfalso
        obtain ⟨b, hb, hab⟩ := ((hprime a).dvd_finsetProd_iff _).1 h'
        exact ha (by rw [hinj a b hab]; exact hb)
      · obtain ⟨S, hS⟩ := h'
        exact ⟨S, by rw [hR, hS]; ring⟩
  exact key Finset.univ

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PNormFormEmbeddings
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem NormFormEmbeddings.proof (h : NormFormEval.Statement) : NormFormEmbeddings.Statement := by
  intro K L Ω _ _ _ _ _ _ _ _ _ n η
  have hs : ∀ _ : Fin n, (Set.range (algebraMap K Ω)).Infinite :=
    fun _ => Set.infinite_range_of_injective (algebraMap K Ω).injective
  refine MvPolynomial.funext_set (fun _ => Set.range (algebraMap K Ω)) hs ?_
  intro x hx
  choose u hu using fun m => hx m (Set.mem_univ m)
  obtain rfl : x = algebraMap K Ω ∘ u := funext fun m => (hu m).symm
  have hl : eval (algebraMap K Ω ∘ u) (map (algebraMap K Ω) (normForm K L η)) =
      algebraMap K Ω (eval u (normForm K L η)) := by
    rw [eval_map]
    change _ = algebraMap K Ω (eval₂ (RingHom.id K) u (normForm K L η))
    rw [eval₂_comp_left]
    rfl
  rw [hl, h K L n η u, Algebra.norm_eq_prod_embeddings]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_prod, map_sum, map_mul, eval_X, eval_C, Function.comp_apply]
  refine Finset.prod_congr rfl fun σ _ => Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, Algebra.smul_def]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PNormFormEval
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem NormFormEval.proof : NormFormEval.Statement := by
  intro R S _ _ _ _ _ n η u
  classical
  rw [Algebra.norm_eq_matrix_det (Module.Free.chooseBasis R S)]
  unfold normForm
  rw [RingHom.map_det]
  congr 1
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PNormOfDividedForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open scoped nonZeroDivisors

noncomputable section

namespace NormOfDividedForm

variable {O B K L : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B] [Field K] [Field L] [Algebra O K]
  [IsFractionRing O K] [Algebra B L] [Algebra K L] [Algebra O L] [IsScalarTower O K L] [IsScalarTower O B L]
  [IsLocalization (Algebra.algebraMapSubmonoid B O⁰) L]


omit [IsDomain O] [IsFractionRing O K] [IsLocalization (Algebra.algebraMapSubmonoid B O⁰) L] in
theorem algebraMap_sum_smul {n : ℕ} (η : Fin n → B) (v : Fin n → O) :
    algebraMap B L (∑ m, v m • η m) = ∑ m, algebraMap O K (v m) • algebraMap B L (η m) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Algebra.smul_def, map_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← IsScalarTower.algebraMap_apply O B L, IsScalarTower.algebraMap_apply O K L]

theorem adjoin_range_eq_top {n : ℕ} (η : Fin n → B) (hgen : Algebra.adjoin O (Set.range η) = ⊤) :
    Algebra.adjoin K (Set.range fun m => algebraMap B L (η m)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid B O⁰) x
  obtain ⟨a, ha, has⟩ := s.2
  have hle : (Algebra.adjoin O (Set.range η)).map (IsScalarTower.toAlgHom O B L) ≤
      (Algebra.adjoin K (Set.range fun m => algebraMap B L (η m))).restrictScalars O := by
    rw [AlgHom.map_adjoin, Algebra.adjoin_le_iff]
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars, IsScalarTower.coe_toAlgHom']
    exact Algebra.subset_adjoin ⟨m, rfl⟩
  have hb : algebraMap B L b ∈ Algebra.adjoin K (Set.range fun m => algebraMap B L (η m)) :=
    hle (Subalgebra.mem_map.2 ⟨b, by rw [hgen]; trivial, IsScalarTower.toAlgHom_apply O B L b⟩)
  have ha0 : algebraMap O K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (nonZeroDivisors.ne_zero ha)
  have hs : IsLocalization.mk' L b s = (algebraMap O K a)⁻¹ • algebraMap B L b := by
    rw [eq_inv_smul_iff₀ ha0, Algebra.smul_def, ← IsScalarTower.algebraMap_apply O K L,
      IsScalarTower.algebraMap_apply O B L, has]
    exact IsLocalization.mk'_spec' L b s
  change IsLocalization.mk' L b s ∈ _
  rw [hs]
  exact Subalgebra.smul_mem _ hb _


omit [IsDomain O] in
theorem algebraMap_det_mulLeft [Module.Free O B] [Module.Finite O B] [FiniteDimensional K L]
    (hEval : NormFormEval.Statement) {n : ℕ} (η : Fin n → B) (v : Fin n → O) :
    algebraMap O K (LinearMap.det (LinearMap.mulLeft O (∑ m, v m • η m))) =
      eval (fun m => algebraMap O K (v m)) (normForm K L fun m => algebraMap B L (η m)) := by
  rw [hEval K L n _ _]
  change algebraMap O K (Algebra.norm O _) = _
  rw [← Algebra.norm_localization O O⁰ (Sₘ := L), algebraMap_sum_smul (K := K)]

end NormOfDividedForm


open NormOfDividedForm in
theorem NormOfDividedForm.proof (hEval : NormFormEval.Statement) (hDvd : NormFormDvd.Statement)
    (hPrime : PrimeMapFractionRing.Statement) : NormOfDividedForm.Statement := by
  intro O B _ _ _ _ _ _ _ _ n η t P hgen ht hP hdvd u
  let K := FractionRing O
  let L := FractionRing B
  let _ : Algebra K L := FractionRing.liftAlgebra O L
  have : IsScalarTower O K L := FractionRing.isScalarTower_liftAlgebra O L
  have : FiniteDimensional K L := .of_isLocalization O B O⁰
  have : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hOB : Function.Injective (algebraMap O B) := FaithfulSMul.algebraMap_injective O B
  have hOK : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  let ηL : Fin n → L := fun m => algebraMap B L (η m)
  let tK : Fin n → K := fun m => algebraMap O K (t m)
  have htL : ∑ m, tK m • ηL m = 1 := by
    rw [← algebraMap_sum_smul, ht, map_one]

  have hdvdL : (∑ m, X m * C (ηL m)) ∣ map (algebraMap K L) (map (algebraMap O K) P) := by
    have h := _root_.map_dvd (MvPolynomial.map (algebraMap B L)) hdvd
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq O K L, ← map_map, map_sum] at h
    simpa only [map_mul, map_X, map_C] using h

  have hnc : ∀ a : O, P ≠ C a := by
    rintro a rfl
    obtain ⟨g, hg⟩ := hdvd
    have h := congrArg (eval 0) hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_C, eval_C, map_mul, map_sum, eval_X, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h
    exact hP.ne_zero (by rw [(map_eq_zero_iff _ hOB).1 h, map_zero])

  obtain ⟨c, hc⟩ := hDvd K L n ηL tK _ (adjoin_range_eq_top η hgen) htL hdvdL
  have hNt : eval tK (normForm K L ηL) = 1 := by
    rw [hEval K L n ηL, htL, map_one]
  have hN0 : ¬ IsUnit (normForm K L ηL) := by
    intro h
    have h0 := h.map (eval (0 : Fin n → K))
    rw [hEval K L n ηL] at h0
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, Algebra.norm_zero] at h0
    exact not_isUnit_zero h0
  have hcu : IsUnit c := ((hPrime O K n P hP hnc).irreducible.isUnit_or_isUnit hc).resolve_left hN0
  obtain ⟨c₀, -, rfl⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 hcu
  have hev : ∀ v : Fin n → O, eval (fun m => algebraMap O K (v m)) (map (algebraMap O K) P) =
      algebraMap O K (eval v P) := fun v => by
    rw [eval_map]
    exact (eval₂_comp_left (algebraMap O K) (RingHom.id O) v P).symm
  have hct : c₀ = algebraMap O K (eval t P) := by
    have h := congrArg (eval tK) hc
    rw [map_mul, hNt, eval_C, one_mul] at h
    rw [← h, hev]
  apply hOK
  have h := congrArg (eval (fun m => algebraMap O K (u m))) hc
  rw [map_mul, eval_C, hct, hev] at h
  rw [map_mul, algebraMap_det_mulLeft (L := L) hEval η u, h, mul_comm]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PPrimeMapFractionRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem PrimeMapFractionRing.proof : PrimeMapFractionRing.Statement := by
  intro O K _ _ _ _ _ n P hP hnc
  classical
  set M : Submonoid (MvPolynomial (Fin n) O) := (nonZeroDivisors O).map (C (σ := Fin n))
  have : IsLocalization M (MvPolynomial (Fin n) K) :=
    MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors O) K

  have hprime : (Ideal.span {P}).IsPrime := (Ideal.span_singleton_prime hP.ne_zero).mpr hP
  have hdisj : Disjoint (M : Set (MvPolynomial (Fin n) O)) ↑(Ideal.span {P}) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hmem
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hCa : (C a : MvPolynomial (Fin n) O) ≠ 0 := by simpa using ha0
    have hdvd : P ∣ C a := Ideal.mem_span_singleton.mp hmem
    have hdeg : P.totalDegree = 0 := by
      have := totalDegree_le_of_dvd_of_isDomain hdvd hCa
      rw [totalDegree_C] at this
      omega
    exact hnc _ (totalDegree_eq_zero_iff_eq_C.mp hdeg)
  have hmap := IsLocalization.isPrime_of_isPrime_disjoint M (MvPolynomial (Fin n) K) _ hprime hdisj
  rw [Ideal.map_span, Set.image_singleton, MvPolynomial.algebraMap_def] at hmap

  have hinj : Function.Injective (map (σ := Fin n) (algebraMap O K)) :=
    map_injective _ (IsFractionRing.injective O K)
  have hne : map (algebraMap O K) P ≠ 0 := by
    intro h
    exact hP.ne_zero (hinj (by rw [h, map_zero]))
  exact (Ideal.span_singleton_prime hne).mp hmap

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsLocalMultOrd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def LocalMultOrd.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (I W : Ideal A) (x : A)
    [(W.map (Ideal.Quotient.mk I)).IsPrime], W ∈ (I ⊔ Ideal.span {x}).minimalPrimes →
      ((localMult (I ⊔ Ideal.span {x}) W : ℕ) : ℕ∞) =
        Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk I)))
          (algebraMap _ _ (Ideal.Quotient.mk I x))

section Inhabitants

open MvPolynomial

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

