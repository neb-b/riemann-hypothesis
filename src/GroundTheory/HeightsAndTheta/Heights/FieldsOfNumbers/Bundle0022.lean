module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsMChart
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace MChartTrdeg

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem chartMonomial_isMultiHomog (u : ∀ k, ι k) (b : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) u b) b := by
  have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, u k⟩)
    (fun k _ => (isWeightedHomogeneous_X F _ _).pow (b k))
  have hb : ∑ k, b k • blockWeight ι ⟨k, u k⟩ = b := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  unfold IsMultiHomog chartMonomial
  rwa [hb] at h

variable (P : Ideal (MRing ι F)) [P.IsPrime]


omit [Fintype K] [DecidableEq K] [P.IsPrime] in
theorem map_eq_zero_iff (f : MRing ι F) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) = 0 ↔ f ∈ P := by
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]


omit [DecidableEq K] [P.IsPrime] in
theorem map_chartMonomial (u : ∀ k, ι k) (b : K → ℕ) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (chartMonomial u b)) =
      ∏ k, algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
        (Ideal.Quotient.mk P (X ⟨k, u k⟩)) ^ b k := by
  simp [chartMonomial, map_prod, map_pow]


omit [DecidableEq K] in
theorem map_chartMonomial_ne_zero (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P)
    (b : K → ℕ) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P (chartMonomial u b)) ≠ 0 := by
  rw [map_chartMonomial]
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ fun h => hu k ((map_eq_zero_iff P _).1 h)

theorem algebraicIndependent (hH : MChartHomog.Statement.{u}) (hP : IsMultiHomogIdeal P)
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    AlgebraicIndependent (chartMap P u).range (fun k => algebraMap (MRing ι F ⧸ P)
      (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X ⟨k, u k⟩))) := by
  classical
  set L := FractionRing (MRing ι F ⧸ P)
  set φ : MRing ι F →+* L := (algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P) with hφ
  have hφapp : ∀ f, φ f = algebraMap (MRing ι F ⧸ P) L (Ideal.Quotient.mk P f) := fun _ => rfl
  rw [algebraicIndependent_iff]
  intro p hp

  have hq : ∀ m, ∃ q, chartMap P u q = ((p.coeff m : (chartMap P u).range) : L) := fun m => (p.coeff m).2
  choose q hq using hq
  choose b h hhom heq using fun m => hH F K ι u (q m)
  have hval : ∀ m, φ (h m) = ((p.coeff m : (chartMap P u).range) : L) * φ (chartMonomial u (b m)) := by
    intro m
    have := heq m P hu
    rw [hq m, eq_div_iff (map_chartMonomial_ne_zero P u hu _)] at this
    rw [hφapp, hφapp]
    exact this.symm
  set s := p.support
  set N : K → ℕ := ∑ m ∈ s, b m
  have hbN : ∀ m ∈ s, ∀ k, b m k ≤ N k := fun m hm =>
    Finset.single_le_sum (f := b) (fun _ _ _ => Nat.zero_le _) hm
  set c : (K →₀ ℕ) → K → ℕ := fun m => N - b m + ⇑m
  have hbc : ∀ m ∈ s, b m + c m = N + ⇑m := by
    intro m hm
    funext k
    have := hbN m hm k
    simp only [c, Pi.add_apply, Pi.sub_apply]
    omega

  set G := ∑ m ∈ s, h m * chartMonomial u (c m)
  have hG : G ∈ P := by
    rw [← map_eq_zero_iff, ← hφapp]
    have hp' := hp
    rw [aeval_def, eval₂_eq'] at hp'
    calc φ G = ∑ m ∈ s, φ (chartMonomial u N) * (algebraMap (chartMap P u).range L (p.coeff m) *
          ∏ k, algebraMap (MRing ι F ⧸ P) L (Ideal.Quotient.mk P (X ⟨k, u k⟩)) ^ m k) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [G, map_sum, map_mul, hval]
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [hφapp (chartMonomial u (b m)), hφapp (chartMonomial u (c m)), hφapp (chartMonomial u N),
            map_chartMonomial, map_chartMonomial, map_chartMonomial]
          have e : ∀ x : K → L, (∏ k, x k ^ b m k) * (∏ k, x k ^ c m k) =
              (∏ k, x k ^ N k) * ∏ k, x k ^ m k := by
            intro x
            rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun k _ => ?_
            rw [← pow_add, ← pow_add]
            exact congrArg (x k ^ ·) (congrFun (hbc m hm) k)
          rw [mul_assoc, e, mul_left_comm]
          rfl
      _ = 0 := by rw [← Finset.mul_sum, hp', mul_zero]

  have hhomt : ∀ m ∈ s, IsMultiHomog (h m * chartMonomial u (c m)) (N + ⇑m) := by
    intro m hm
    unfold IsMultiHomog
    rw [← hbc m hm]
    exact IsWeightedHomogeneous.mul (hhom m) (chartMonomial_isMultiHomog u (c m))
  have hcomp : ∀ m ∈ s,
      weightedHomogeneousComponent (blockWeight ι) (N + ⇑m) G = h m * chartMonomial u (c m) := by
    intro m hm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [G, map_sum]
    rw [Finset.sum_eq_single m]
    · exact IsWeightedHomogeneous.weightedHomogeneousComponent_same (hhomt m hm)
    · intro m' hm' hne
      exact IsWeightedHomogeneous.weightedHomogeneousComponent_ne (N + ⇑m) (hhomt m' hm')
        fun e => hne (DFunLike.coe_injective (add_left_cancel e)).symm
    · intro hms
      exact absurd hm hms

  have hzero : ∀ m ∈ s, p.coeff m = 0 := by
    intro m hm
    have hmem : h m * chartMonomial u (c m) ∈ P := hcomp m hm ▸ hP G hG (N + ⇑m)
    have hcm : chartMonomial u (c m) ∉ P := fun h' =>
      map_chartMonomial_ne_zero P u hu (c m) ((map_eq_zero_iff P _).2 h')
    have hh : h m ∈ P := (Ideal.IsPrime.mem_or_mem ‹_› hmem).resolve_right hcm
    have h2 := hval m
    rw [hφapp, (map_eq_zero_iff P _).2 hh, eq_comm, mul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact Subtype.ext h2
    · exact absurd h2 (map_chartMonomial_ne_zero P u hu (b m))
  ext m
  by_contra hne
  exact hne (by simpa using hzero m (mem_support_iff.2 (by simpa using hne)))


omit [Fintype K] [DecidableEq K] in
theorem isAlgebraic_adjoin (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    Algebra.IsAlgebraic (Algebra.adjoin (chartMap P u).range (Set.range fun k =>
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X ⟨k, u k⟩))))
      (FractionRing (MRing ι F ⧸ P)) := by
  set_option synthInstance.maxHeartbeats 200000 in
    set R := MRing ι F ⧸ P
    set L := FractionRing R
    set A₀ := (chartMap P u).range
    set S' := Algebra.adjoin A₀ (Set.range fun k => algebraMap R L (Ideal.Quotient.mk P (X ⟨k, u k⟩)))
    have hξS : ∀ v, algebraMap R L (Ideal.Quotient.mk P (X v)) ∈ S' := by
      intro v
      have hr : chartMap P u (X v) ∈ A₀ := AlgHom.mem_range_self _ _
      have hne : algebraMap R L (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩)) ≠ 0 :=
        fun h => hu v.1 ((map_eq_zero_iff P _).1 h)
      have e : algebraMap R L (Ideal.Quotient.mk P (X v)) =
          chartMap P u (X v) * algebraMap R L (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩)) := by
        simp only [chartMap, aeval_X]
        exact (div_mul_cancel₀ _ hne).symm
      rw [e]
      exact S'.mul_mem (S'.algebraMap_mem (⟨_, hr⟩ : A₀)) (Algebra.subset_adjoin ⟨v.1, rfl⟩)
    have hRS : ∀ r : R, algebraMap R L r ∈ S' := by
      intro r
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
      induction f using MvPolynomial.induction_on with
      | C c =>
        rw [show (Ideal.Quotient.mk P (C c) : R) = algebraMap F R c from rfl,
          ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F A₀ L]
        exact S'.algebraMap_mem _
      | add f g hf hg => rw [map_add (f := _), map_add (f := _)]; exact S'.add_mem hf hg
      | mul_X f i hf => rw [map_mul, map_mul]; exact S'.mul_mem hf (hξS i)
    let _ : CommRing S' := Subalgebra.toCommRing S'
    refine ⟨fun x => ?_⟩
    obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hd0 : algebraMap R L d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    refine ⟨Polynomial.C (⟨_, hRS d⟩ : S') * Polynomial.X - Polynomial.C (⟨_, hRS a⟩ : S'),
      fun h => hd0 ?_, ?_⟩
    · have := congrArg (fun p : Polynomial S' => p.coeff 1) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, ↓reduceIte,
        one_ne_zero, Polynomial.coeff_zero] at this
      have h' := congrArg Subtype.val this
      simp only [Subalgebra.coe_zero, sub_zero] at h'
      exact h'
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      show algebraMap R L d * (algebraMap R L a / algebraMap R L d) - algebraMap R L a = 0
      rw [mul_comm, div_mul_cancel₀ _ hd0, sub_self]

end MChartTrdeg

theorem MChartTrdeg.proof (hH : MChartHomog.Statement.{u}) : MChartTrdeg.Statement.{u} := by
  intro F _ K _ _ ι _ P _ hP u hu
  set R := MRing ι F ⧸ P
  set L := FractionRing R
  set A₀ := (chartMap P u).range
  have hb : IsTranscendenceBasis A₀ (fun k => algebraMap R L (Ideal.Quotient.mk P (X ⟨k, u k⟩))) :=
    (MChartTrdeg.algebraicIndependent P hH hP u hu).isTranscendenceBasis_iff_isAlgebraic.mpr
      (MChartTrdeg.isAlgebraic_adjoin P u hu)
  have h1 : Algebra.trdeg A₀ L = Fintype.card K := by
    simpa using hb.lift_cardinalMk_eq_trdeg.symm
  have : FaithfulSMul A₀ L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  have : FaithfulSMul F A₀ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F A₀).injective
  rw [show Algebra.trdeg F (MRing ι F ⧸ chartIdeal P u) = Algebra.trdeg F A₀ from
      (Ideal.quotientKerEquivRange (chartMap P u)).trdeg_eq, ← h1, trdeg_add_eq F A₀ (A := L),
    GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := F) (A := R) L]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem module_finite_of_forall_mem_span {A A' B L : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing A'] [CommRing B] [Algebra A B] [CommRing L] [Algebra A' L] (φ : A →+* A')
    (hφ : Function.Surjective φ) (ψ : B →+* L) (hψ : Function.Injective ψ)
    (hcomm : ∀ a b, ψ (algebraMap A B a * b) = algebraMap A' L (φ a) * ψ b) (s : Finset L)
    (h : ∀ b, ψ b ∈ Submodule.span A' (s : Set L)) : Module.Finite A B := by
  let _ : Algebra A L := ((algebraMap A' L).comp φ).toAlgebra
  have hspan : ∀ x ∈ Submodule.span A' (s : Set L), x ∈ Submodule.span A (s : Set L) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add _ _ _ _ hy hz => exact add_mem hy hz
    | smul a' y _ hy =>
      obtain ⟨a, rfl⟩ := hφ a'
      have e : φ a • y = a • y := by rw [Algebra.smul_def, Algebra.smul_def]; rfl
      rw [e]
      exact Submodule.smul_mem _ a hy
  let f : B →ₗ[A] L :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := fun a b => by rw [Algebra.smul_def, hcomm]; rfl }
  have : IsNoetherian A (Submodule.span A (s : Set L)) :=
    isNoetherian_span_of_finite A s.finite_toSet
  exact Module.Finite.of_injective (f.codRestrict _ fun b => hspan _ (h b))
    fun b c hbc => hψ (congrArg Subtype.val hbc)

theorem SemilocalFinite.proof (h1 : SemilocalIntegral.Statement.{u})
    (h2 : LocalIntegralClosureFinite.Statement.{u}) (h3 : DegZeroLocNoetherian.Statement.{u}) :
    SemilocalFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hd' hd W hW hdW hle
  have := hP'.isPrime
  set A := degZeroLoc (contractPrime j P') {W}
  set B := degZeroLoc P' (fibrePrimes j P' W)
  set A' := A.map (contractFracMap j P')
  have : IsNoetherianRing A :=
    h3 F K (fun k => ι' (j k)) _ (isMultiProjPrime_contractPrime _ _ hP') W hW hle
  have hint : Algebra.IsIntegral A B := h1 F K K' j ι' P' hP' n hd' hd W hW hdW hle
  obtain ⟨s, -, hs⟩ := h2 F K K' j ι' P' hP' (hd.trans hd'.symm) W hW hle
  let φA : A →+* A' := (((contractFracMap j P').comp A.val).codRestrict A'
    (fun a => Subalgebra.mem_map.mpr ⟨a, a.2, rfl⟩)).toRingHom
  have hφA : Function.Surjective φA := fun a' => by
    obtain ⟨a, ha, hae⟩ := Subalgebra.mem_map.mp a'.2
    exact ⟨⟨a, ha⟩, Subtype.ext hae⟩
  refine module_finite_of_forall_mem_span φA hφA B.val.toRingHom Subtype.val_injective
    (fun _ _ => rfl) s fun b => ?_
  exact hs _ (mem_homFracDegZero_of_mem_degZeroLoc P' _ _ b.2)
    (IsIntegral.map_of_comp_eq φA B.val.toRingHom (RingHom.ext fun _ => rfl) (hint.isIntegral b))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLengthSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


set_option synthInstance.maxHeartbeats 400000 in
theorem SemilocalLengthSum.proof (h1 : FibreFinite.Statement.{u})
    (h2 : SemilocalFiniteRank.Statement.{u}) (h3 : DegZeroLocalRing.Statement.{u})
    (h4 : FiniteAlgebraLengthSum.Statement.{u}) (h5 : SemilocalMaxIdeals.Statement.{u}) :
    SemilocalLengthSum.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn c a h ha hh haP W hW hWn hPW hhW d hd α hα β hβ
  have := hP'.isPrime
  have hfin := h1 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  refine ⟨hfin, ?_⟩
  have := (h2 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW).1
  have := (h3 F K (fun k => ι' (j k)) (contractPrime j P') (isMultiProjPrime_contractPrime j ι' hP')
    W hW hPW).1.2
  obtain ⟨𝔪, h𝔪, hinj, hcov, hloc⟩ := h5 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  let : Fintype (fibrePrimes j P' W) := hfin.fintype
  let alg : ∀ W' : fibrePrimes j P' W,
      Algebra (degZeroLoc P' (fibrePrimes j P' W)) (degZeroLoc P' {W'.1}) :=
    fun W' => degZeroLoc.algebraOfSubset P' (Set.singleton_subset_iff.mpr W'.2)
  rw [h4 _ _ _ 𝔪 h𝔪 hinj hcov (fun W' => degZeroLoc P' {W'.1}) (fun W' => (hloc W').1) α,
    Finset.sum_filter, Finset.sum_subtype hfin.toFinset (fun _ => Set.Finite.mem_toFinset hfin)]
  refine Finset.sum_congr rfl fun W' _ => ?_
  obtain ⟨hW'p, -, hW'c⟩ := W'.2
  have := hW'p.isPrime
  have hb : algebraMap _ (degZeroLoc P' {W'.1}) (algebraMap (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W)) α) = β W'.1 :=
    Subtype.ext (hβ W'.1 W'.2).symm
  rw [hb, (hloc W').2, ← hd W'.1 hW'p hW'c]
  split_ifs with haW'
  · rfl
  rw [Ring.ord_of_isUnit, zero_mul]
  have hne : ∀ g, g ∉ contractPrime j P' → algebraMap (MRing ι' F ⧸ P')
      (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' (rename (blockIncl j ι') g)) ≠ 0 :=
    fun g hg => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hg
  have hhP : h ∉ contractPrime j P' := fun hm => hhW (hPW hm)
  refine IsUnit.of_mul_eq_one ⟨_, div_mem_degZeroLoc P' {W'.1} (isMultiHomog_rename j ι' hh)
    (isMultiHomog_rename j ι' ha) haP (fun W'' hW'' => (Set.mem_singleton_iff.mp hW'') ▸ haW')⟩ ?_
  apply Subtype.ext
  change (β W'.1 : FractionRing (MRing ι' F ⧸ P')) * _ = 1
  rw [hβ W'.1 W'.2, hα, map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]
  have := hne h hhP
  have := hne a haP
  field_simp

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalMaxIdeals
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted

noncomputable section

universe u


set_option synthInstance.maxHeartbeats 400000 in
theorem SemilocalMaxIdeals.proof (h1 : FibreFinite.Statement.{u}) (h2 : FibreRelDim.Statement.{u})
    (h3 : FibreNonempty.Statement.{u}) (h4 : DegZeroLocUnits.Statement.{u})
    (h5 : DegZeroLocSeparate.Statement.{u}) (h6 : DegZeroLocLocalize.Statement.{u})
    (h7 : SemilocalResidueLength.Statement.{u}) : SemilocalMaxIdeals.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W hW hWn hPW
  have := hP'.isPrime
  have hfin := h1 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  have h𝒲 : ∀ W' ∈ fibrePrimes j P' W, IsMultiProjPrime W' ∧ P' ≤ W' :=
    fun W' hW' => ⟨hW'.1, hW'.2.1⟩

  have hanti : ∀ W₁ ∈ fibrePrimes j P' W, ∀ W₂ ∈ fibrePrimes j P' W, W₁ ≤ W₂ → W₁ = W₂ := by
    intro W₁ h₁ W₂ h₂ hle
    by_contra hne
    have := h₁.1.isPrime
    have := h₂.1.isPrime
    obtain ⟨f, hf₂, hf₁⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
    have hd := ringKrullDim_add_one_le hle hf₁ hf₂
    obtain ⟨D₁, -, hD₁⟩ := exists_ringKrullDim_eq
      (fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal h₁.1.multiHomog T hq) h₁.1.relevant
    obtain ⟨D₂, -, hD₂⟩ := exists_ringKrullDim_eq
      (fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal h₂.1.multiHomog T hq) h₂.1.relevant
    have e₁ := h2 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW W₁ h₁
    have e₂ := h2 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW W₂ h₂
    rw [relDim_eq_int hD₁, natCast_withBot_withTop] at e₁
    rw [relDim_eq_int hD₂, natCast_withBot_withTop] at e₂
    rw [hD₁, hD₂] at hd
    have e₁' : (D₁ : ℤ) - Fintype.card K' = n := by exact_mod_cast e₁
    have e₂' : (D₂ : ℤ) - Fintype.card K' = n := by exact_mod_cast e₂
    have hd' : D₂ + 1 ≤ D₁ := by exact_mod_cast hd
    omega

  choose 𝔪 h𝔪 hlen using h7 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  let : Fintype (fibrePrimes j P' W) := hfin.fintype
  have hprime : ∀ W' : fibrePrimes j P' W, (𝔪 W'.1 W'.2).IsPrime := by
    intro W'
    refine ⟨fun htop => (h𝔪 W'.1 W'.2 1).mp (htop ▸ Submodule.mem_top)
      ⟨1, Subalgebra.one_mem _, by simp⟩, fun {x y} hxy => ?_⟩
    by_contra hc
    rw [not_or, h𝔪, h𝔪, not_not, not_not] at hc
    obtain ⟨⟨a, ha, hxa⟩, ⟨b, hb, hyb⟩⟩ := hc
    exact (h𝔪 W'.1 W'.2 _).mp hxy ⟨a * b, Subalgebra.mul_mem _ ha hb, by
      rw [Subalgebra.coe_mul, mul_mul_mul_comm, hxa, hyb, one_mul]⟩

  have hsep : ∀ W₁ W₂ : fibrePrimes j P' W, W₁ ≠ W₂ → ¬ 𝔪 W₁.1 W₁.2 ≤ 𝔪 W₂.1 W₂.2 := by
    intro W₁ W₂ hne hle
    obtain ⟨x, hx, hx₁, hx₂⟩ := h5 F K' ι' P' hP' _ hfin h𝒲 W₁.1 W₁.2 W₂.1 W₂.2
      (fun h => hne (Subtype.ext (hanti _ W₁.2 _ W₂.2 h)))
    exact (h𝔪 W₂.1 W₂.2 ⟨x, hx⟩).mp (hle ((h𝔪 W₁.1 W₁.2 ⟨x, hx⟩).mpr hx₁)) hx₂

  have hne := h3 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  have hcov : ∀ M : Ideal (degZeroLoc P' (fibrePrimes j P' W)), M.IsMaximal →
      ∃ W' : fibrePrimes j P' W, M = 𝔪 W'.1 W'.2 := by
    intro M hM
    let 𝔫 : fibrePrimes j P' W → Ideal (degZeroLoc P' (fibrePrimes j P' W)) := fun W' => 𝔪 W'.1 W'.2
    have hsub : (M : Set (degZeroLoc P' (fibrePrimes j P' W))) ⊆
        ⋃ W' ∈ ((Finset.univ : Finset (fibrePrimes j P' W)) : Set (fibrePrimes j P' W)),
          ((𝔫 W' : Ideal (degZeroLoc P' (fibrePrimes j P' W))) : Set _) := by
      intro x hx
      have hnu : ¬ IsUnit x := fun hu => hM.ne_top (M.eq_top_of_isUnit_mem hx hu)
      have : ¬ ∀ W' ∈ fibrePrimes j P' W, ∃ y ∈ degZeroLoc P' {W'},
          (x : FractionRing (MRing ι' F ⧸ P')) * y = 1 := by
        rw [← h4 F K' ι' P' hP' _ hne h𝒲 x x.2]
        rintro ⟨y, hy, hxy⟩
        exact hnu (IsUnit.of_mul_eq_one ⟨y, hy⟩ (Subtype.ext hxy))
      push Not at this
      obtain ⟨W', hW', hx'⟩ := this
      refine Set.mem_iUnion₂.mpr ⟨⟨W', hW'⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      exact (h𝔪 W' hW' x).mpr (fun ⟨y, hy, hxy⟩ => hx' y hy hxy)
    obtain ⟨W', -, hle⟩ := (Ideal.subset_union_prime (f := 𝔫) ⟨hne.some, hne.some_mem⟩
      ⟨hne.some, hne.some_mem⟩ (fun W' _ _ _ => hprime W')).mp hsub
    exact ⟨W', hM.eq_of_le (hprime W').ne_top hle⟩
  have hmax : ∀ W' : fibrePrimes j P' W, (𝔪 W'.1 W'.2).IsMaximal := by
    intro W'
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (hprime W').ne_top
    obtain ⟨W'', rfl⟩ := hcov M hM
    by_cases h : W' = W''
    · subst h
      exact hM
    · exact absurd hle (hsep W' W'' h)
  refine ⟨fun W' => 𝔪 W'.1 W'.2, hmax, fun W₁ W₂ he => ?_, hcov, fun W' => ⟨?_, hlen W'.1 W'.2⟩⟩
  · by_contra h
    exact hsep W₁ W₂ h (le_of_eq he)

  let := degZeroLoc.algebraOfSubset P' (Set.singleton_subset_iff.mpr W'.2)
  refine (isLocalization_iff _ _).mpr ⟨fun s => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · have hs := s.2
    rw [Ideal.mem_primeCompl_iff, h𝔪, not_not] at hs
    obtain ⟨t, ht, hst⟩ := hs
    exact IsUnit.of_mul_eq_one ⟨t, ht⟩ (Subtype.ext hst)
  · obtain ⟨b, hb, s, hs, ⟨t, ht, hst⟩, hzs⟩ := h6 F K' ι' P' hP' _ hfin h𝒲 W'.1 W'.2 z z.2
    refine ⟨(⟨b, hb⟩, ⟨⟨s, hs⟩, ?_⟩), Subtype.ext hzs⟩
    rw [Ideal.mem_primeCompl_iff, h𝔪, not_not]
    exact ⟨t, ht, hst⟩
  · refine ⟨1, ?_⟩
    have h' := congrArg Subtype.val hxy
    have hxy' : x = y := Subtype.ext h'
    rw [hxy']

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

