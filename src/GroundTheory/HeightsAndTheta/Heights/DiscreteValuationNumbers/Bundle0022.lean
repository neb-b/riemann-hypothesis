module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Theta.Capelli.CompleteHomogeneous
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConeTrdegFnField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcMap mcIdeal fnField)

noncomputable section

theorem ConeTrdegFnField.trdeg_eq_of_le_of_isAlgebraic {O B : Type} [CommRing O] [IsDomain O] [CommRing B]
    [IsDomain B] [Algebra O B] (hinj : Function.Injective (algebraMap O B)) {S T : Subalgebra O B}
    (hST : S ≤ T) (halg : ∀ t ∈ T, IsAlgebraic S t) : Algebra.trdeg O S = Algebra.trdeg O T := by
  let _ : Algebra S T := (Subalgebra.inclusion hST).toRingHom.toAlgebra
  have _ : IsScalarTower O S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : FaithfulSMul O S :=
    (faithfulSMul_iff_algebraMap_injective O S).2 fun a b h => hinj (congrArg Subtype.val h)
  have _ : FaithfulSMul S T :=
    (faithfulSMul_iff_algebraMap_injective S T).2 (Subalgebra.inclusion_injective hST)
  let f : T →ₐ[S] B := { T.val.toRingHom with commutes' := fun _ => rfl }
  have _ : Algebra.IsAlgebraic S T :=
    ⟨fun t => (isAlgebraic_algHom_iff f Subtype.val_injective).1 (halg t t.2)⟩
  have h := trdeg_add_eq O S (A := T)
  rw [trdeg_eq_zero (R := S) (A := T), add_zero] at h
  exact h

section Cone

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} {ι : K → Type}

theorem ConeTrdegFnField.mem_fnField_of_mem_adjoin (y : (Σ k, ι k) → Ω) {a : Ω}
    (ha : a ∈ Algebra.adjoin O (fnField O y : Set Ω)) : a ∈ fnField O y := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact hx
  | algebraMap r => exact Subfield.subset_closure (Or.inl ⟨r, rfl⟩)
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

def ConeTrdegFnField.coneMap (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    MvPolynomial K (Algebra.adjoin O (fnField O y : Set Ω)) →ₐ[O] MvPolynomial K Ω :=
  ((aeval fun k => C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω).restrictScalars O).comp
    (MvPolynomial.mapAlgHom (Algebra.adjoin O (fnField O y : Set Ω)).val)

theorem ConeTrdegFnField.coneMap_C (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (a : Algebra.adjoin O (fnField O y : Set Ω)) :
    ConeTrdegFnField.coneMap y c (C a) = C (a : Ω) := by
  simp [ConeTrdegFnField.coneMap]

theorem ConeTrdegFnField.coneMap_X (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (k : K) :
    ConeTrdegFnField.coneMap (O := O) y c (X k) = C (y ⟨k, c k⟩) * X k := by
  simp [ConeTrdegFnField.coneMap]

theorem ConeTrdegFnField.mcMap_X (y : (Σ k, ι k) → Ω) (p : Σ k, ι k) :
    mcMap O y (X p) = C (y p) * X p.1 := by
  simp [mcMap]

theorem ConeTrdegFnField.coneMap_injective (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Function.Injective (ConeTrdegFnField.coneMap (O := O) y c) := by
  let ψ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (y ⟨k, c k⟩) * X k
  let ψ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (y ⟨k, c k⟩)⁻¹ * X k
  have hinv : ψ'.comp ψ = AlgHom.id Ω _ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp only [ψ, ψ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, AlgHom.id_apply,
      MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (hc k), map_one, one_mul]
  have hψ : Function.Injective ψ := Function.LeftInverse.injective (g := ψ') fun p => by
    rw [← AlgHom.comp_apply, hinv, AlgHom.id_apply]
  exact hψ.comp (MvPolynomial.map_injective _ Subtype.val_injective)

end Cone

theorem ConeTrdegFnField.proof : ConeTrdegFnField.Statement := by
  intro O _ _ Ω _ _ hinj K _ ι _ y hy
  choose c hc using hy
  set F₀ := Algebra.adjoin O (fnField O y : Set Ω)
  have hF : ∀ w ∈ fnField O y, w ∈ F₀ := fun w hw => Algebra.subset_adjoin hw
  have hu : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ F₀ := fun p =>
    hF _ (Subfield.subset_closure (Or.inr ⟨⟨p.1, (p.2, c p.1)⟩, rfl⟩))

  let ρ : MRingOver O ι →ₐ[O] MvPolynomial K F₀ := aeval fun p => C (⟨_, hu p⟩ : F₀) * X p.1
  have hfac : mcMap O y = (ConeTrdegFnField.coneMap (O := O) y c).comp ρ := by
    refine MvPolynomial.algHom_ext fun p => ?_
    rw [ConeTrdegFnField.mcMap_X, AlgHom.comp_apply, aeval_X, map_mul, ConeTrdegFnField.coneMap_C,
      ConeTrdegFnField.coneMap_X, ← mul_assoc, ← map_mul]
    simp only [div_mul_cancel₀ _ (hc p.1)]
  set R := (mcMap O y).range
  have hle : R ≤ (ConeTrdegFnField.coneMap (O := O) y c).range := by
    show (mcMap O y).range ≤ _
    rw [hfac]; exact AlgHom.range_comp_le_range _ _
  have hXR : ∀ p : Σ k, ι k, (C (y p) * X p.1 : MvPolynomial K Ω) ∈ R := fun p =>
    ⟨X p, ConeTrdegFnField.mcMap_X y p⟩

  have halgC : ∀ w ∈ fnField O y, IsAlgebraic R (C w : MvPolynomial K Ω) := by
    intro w hw
    induction hw using Subfield.closure_induction with
    | mem x hx =>
      rcases hx with ⟨r, rfl⟩ | ⟨q, rfl⟩
      · have e : (C (algebraMap O Ω r) : MvPolynomial K Ω) = algebraMap O (MvPolynomial K Ω) r := by
          rw [MvPolynomial.algebraMap_apply]
        rw [e]
        exact isAlgebraic_algebraMap (⟨_, R.algebraMap_mem r⟩ : R)
      · dsimp only
        by_cases h0 : y ⟨q.1, q.2.2⟩ = 0
        · rw [h0, div_zero, map_zero]; exact isAlgebraic_zero
        · refine IsAlgebraic.of_mul (y := C (y ⟨q.1, q.2.2⟩) * X q.1)
            (mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (C_ne_zero.2 h0) (X_ne_zero _)))
            (isAlgebraic_algebraMap (⟨_, hXR ⟨q.1, q.2.2⟩⟩ : R)) ?_
          have e : (C (y ⟨q.1, q.2.2⟩) * X q.1 : MvPolynomial K Ω) * C (y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩) =
              C (y ⟨q.1, q.2.1⟩) * X q.1 := by
            rw [mul_comm, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ h0]
          rw [e]
          exact isAlgebraic_algebraMap (⟨_, hXR ⟨q.1, q.2.1⟩⟩ : R)
    | one => rw [map_one]; exact isAlgebraic_one
    | add x z _ _ hx hz => rw [map_add (f := _)]; exact hx.add hz
    | neg x _ hx => rw [map_neg]; exact hx.neg
    | inv x _ hx =>
      by_cases h0 : x = 0
      · rw [h0, inv_zero, map_zero]; exact isAlgebraic_zero
      · refine IsAlgebraic.of_mul (y := C x) (mem_nonZeroDivisors_of_ne_zero (C_ne_zero.2 h0)) hx ?_
        rw [← map_mul, mul_inv_cancel₀ h0, map_one]; exact isAlgebraic_one
    | mul x z _ _ hx hz => rw [map_mul]; exact hx.mul hz
  have halg : ∀ t ∈ (ConeTrdegFnField.coneMap (O := O) y c).range, IsAlgebraic R t := by
    rintro _ ⟨q, rfl⟩
    change IsAlgebraic R (ConeTrdegFnField.coneMap (O := O) y c q)
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [ConeTrdegFnField.coneMap_C]
      exact halgC a (ConeTrdegFnField.mem_fnField_of_mem_adjoin y a.2)
    | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
    | mul_X p k hp =>
      rw [map_mul, ConeTrdegFnField.coneMap_X]
      exact hp.mul (isAlgebraic_algebraMap (⟨_, hXR ⟨k, c k⟩⟩ : R))
  have hinjP : Function.Injective (algebraMap O (MvPolynomial K Ω)) := by
    rw [IsScalarTower.algebraMap_eq O Ω (MvPolynomial K Ω)]
    exact (C_injective K Ω).comp hinj
  have h1 : Algebra.trdeg O (MRingOver O ι ⧸ mcIdeal O y) = Algebra.trdeg O R :=
    (Ideal.quotientKerEquivRange (mcMap O y)).trdeg_eq
  have h2 : Algebra.trdeg O (ConeTrdegFnField.coneMap (O := O) y c).range = Algebra.trdeg O (MvPolynomial K F₀) :=
    (AlgEquiv.ofInjective (ConeTrdegFnField.coneMap (O := O) y c)
      (ConeTrdegFnField.coneMap_injective y c hc)).trdeg_eq.symm
  have _ : FaithfulSMul O F₀ :=
    (faithfulSMul_iff_algebraMap_injective O F₀).2 fun a b h => hinj (congrArg Subtype.val h)
  have _ : FaithfulSMul F₀ (MvPolynomial K F₀) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (C_injective K _)
  have h3 : Algebra.trdeg O (MvPolynomial K F₀) = Algebra.trdeg O F₀ + Fintype.card K := by
    rw [← trdeg_add_eq O F₀ (A := MvPolynomial K F₀), MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id,
      Cardinal.mk_fintype]
  rw [h1, ConeTrdegFnField.trdeg_eq_of_le_of_isAlgebraic hinjP hle halg, h2, h3]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivisorIdealCycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section General

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem idealCycle_eq_of_mul_mem {J J' U : Ideal (MRing ι R)} {s t : MRing ι R} (hs : s ∉ U)
    (ht : t ∉ U) (hsJ : ∀ x ∈ J, s * x ∈ J') (htJ : ∀ x ∈ J', t * x ∈ J) :
    idealCycle J U = idealCycle J' U := by
  unfold idealCycle
  by_cases h : U ∈ J.minimalPrimes ∧ IsRelevant U
  · have h' : U ∈ J'.minimalPrimes ∧ IsRelevant U :=
      ⟨mem_minimalPrimes_of_mul_mem hs ht hsJ htJ h.1, h.2⟩
    rw [dite_eq_left h, dite_eq_left h']
    have : U.IsPrime := h.1.1.1
    unfold multAt
    rw [length_localized_eq_of_mul_mem hs ht hsJ htJ]
  · have h' : ¬ (U ∈ J'.minimalPrimes ∧ IsRelevant U) := fun h' =>
      h ⟨mem_minimalPrimes_of_mul_mem ht hs htJ hsJ h'.1, h'.2⟩
    rw [dite_eq_right h, dite_eq_right h']

theorem divCycle_eq_zero_of_not_mem {W U : Ideal (MRing ι R)} {x : MRing ι R} (hx : x ∉ U) :
    divCycle W x U = 0 := by
  unfold divCycle
  rw [dite_eq_right]
  rintro ⟨h, -⟩
  exact hx (h.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))

end General

theorem DivisorIdealCycle.proof : DivisorIdealCycle.Statement.{u} := by
  intro R _ _ K _ _ ι _ P W f g u v hP hW hPW hg hloc hu hv huv
  funext U
  by_cases hU : U.IsPrime ∧ W ≤ U ∧ IsRelevant U
  · obtain ⟨hUp, hWU, hUrel⟩ := hU
    obtain ⟨u', v', hu'U, hloc'⟩ := hloc U hUp hWU hUrel
    have hu'W : u' ∉ W := fun h => hu'U (hWU h)
    have h1U : (1 : MRing ι R) ∉ U := (Ideal.ne_top_iff_one U).mp hUp.ne_top

    have hcross : u * v' - u' * v ∈ P := by
      have hmem : (u * v' - u' * v) * g ∈ P := by
        rw [show (u * v' - u' * v) * g = u' * (u * f - v * g) - u * (u' * f - v' * g) by ring]
        exact P.sub_mem (P.mul_mem_left _ huv) (P.mul_mem_left _ hloc')
      exact (hP.mem_or_mem hmem).resolve_right hg
    have hv'W : v' ∉ W := by
      intro h
      have hmem : u' * v ∈ W := by
        rw [show u' * v = u * v' - (u * v' - u' * v) by ring]
        exact W.sub_mem (W.mul_mem_left u h) (hPW hcross)
      exact (hW.mem_or_mem hmem).elim hu'W hv

    have hmul := congrFun (DivCycleMul.proof R K ι W u' v hW hu'W hv) U
    have hmul' := congrFun (DivCycleMul.proof R K ι W u v' hW hu hv'W) U
    have heq : divCycle W (u' * v) U = divCycle W (u * v') U :=
      divCycle_eq_of_mul_sub_mem (P := W) (W := U) (u := 1) (v := 1) h1U h1U (by
        rw [show 1 * (u' * v) - 1 * (u * v') = -(u * v' - u' * v) by ring]
        exact W.neg_mem (hPW hcross))
    have hu'0 : divCycle W u' U = 0 := divCycle_eq_zero_of_not_mem hu'U
    simp only [Pi.add_apply] at hmul hmul'

    have hv'D : v' ∈ divisorIdeal P f g := by
      rw [divisorIdeal, Submodule.mem_colon_singleton, smul_eq_mul,
        show v' * g = u' * f - (u' * f - v' * g) by ring]
      exact Submodule.sub_mem _
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)))
        (Ideal.mem_sup_left hloc')
    have hsJ : ∀ x ∈ W ⊔ Ideal.span {v'}, 1 * x ∈ W ⊔ divisorIdeal P f g := by
      intro x hx
      rw [one_mul]
      exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr hv'D) W hx
    have htJ : ∀ x ∈ W ⊔ divisorIdeal P f g, u' * x ∈ W ⊔ Ideal.span {v'} := by
      intro x hx
      obtain ⟨w, hw, d, hd, rfl⟩ := Submodule.mem_sup.mp hx
      rw [divisorIdeal, Submodule.mem_colon_singleton, smul_eq_mul] at hd
      obtain ⟨p, hp, r, hr, hpr⟩ := Submodule.mem_sup.mp hd
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      have h1 : (u' * d - a * v') * g ∈ P := by
        have e : (u' * d - a * v') * g = u' * p + a * (u' * f - v' * g) := by
          calc (u' * d - a * v') * g = u' * (d * g) - a * v' * g := by ring
            _ = u' * p + a * (u' * f - v' * g) := by rw [← hpr]; ring
        rw [e]
        exact P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ hloc')
      have h2 : u' * d - a * v' ∈ P := (hP.mem_or_mem h1).resolve_right hg
      rw [show u' * (w + d) = (u' * w + (u' * d - a * v')) + a * v' by ring]
      exact Submodule.add_mem_sup (W.add_mem (W.mul_mem_left _ hw) (hPW h2))
        (Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩)
    have hR : idealCycle (W ⊔ divisorIdeal P f g) U = divCycle W v' U := by
      rw [divCycle_eq_idealCycle]
      exact (idealCycle_eq_of_mul_mem h1U hu'U hsJ htJ).symm
    rw [hR]
    show divCycle W v U - divCycle W u U = divCycle W v' U
    omega
  · have hcomp : ∀ J : Ideal (MRing ι R), W ≤ J → ¬ (U ∈ J.minimalPrimes ∧ IsRelevant U) := by
      rintro J hWJ ⟨h, hrel⟩
      exact hU ⟨h.1.1, hWJ.trans h.1.2, hrel⟩
    show divCycle W v U - divCycle W u U = idealCycle (W ⊔ divisorIdeal P f g) U
    unfold divCycle idealCycle
    rw [dite_eq_right (hcomp _ le_sup_left), dite_eq_right (hcomp _ le_sup_left), dite_eq_right (hcomp _ le_sup_left),
      sub_self]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPointIdealMultiProj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace PointIdealMultiProj

variable {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L]
  {K : Type*} [DecidableEq K] {ι : K → Type*}

def coneWeight (K : Type*) [DecidableEq K] : K → K → ℕ := fun k => Pi.single k 1

theorem coneMap_monomial_isWeightedHomogeneous (z : (Σ k, ι k) → L) (d : (Σ k, ι k) →₀ ℕ) (a : F) :
    IsWeightedHomogeneous (coneWeight K) (pointConeMap F z (monomial d a))
      (Finsupp.weight (blockWeight ι) d) := by
  rw [pointConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, Finsupp.weight_apply, Finsupp.prod,
    Finsupp.sum]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
  exact ((isWeightedHomogeneous_X (R := L) (coneWeight K) p.1).C_mul (z p)).pow (d p)

theorem coneMap_component (z : (Σ k, ι k) → L) (b : K → ℕ) (f : MRing ι F) :
    weightedHomogeneousComponent (coneWeight K) b (pointConeMap F z f) =
      pointConeMap F z (weightedHomogeneousComponent (blockWeight ι) b f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 := coneMap_monomial_isWeightedHomogeneous (K := K) (F := F) z d a
    have h2 : IsWeightedHomogeneous (blockWeight ι) (monomial d a : MRing ι F)
        (Finsupp.weight (blockWeight ι) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : b = Finsupp.weight (blockWeight ι) d
    · subst h
      rw [h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]
    · rw [h1.weightedHomogeneousComponent_ne _ h, h2.weightedHomogeneousComponent_ne _ h, map_zero]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]

theorem proof : PointIdealMultiProj.Statement := by
  intro F _ L _ _ K _ ι z hz
  refine ⟨?_, ?_, ?_⟩
  · exact RingHom.ker_isPrime _
  · intro f hf b
    rw [pointIdeal, RingHom.mem_ker] at hf ⊢
    have := coneMap_component (F := F) z b f
    rw [show (pointConeMap F z) f = 0 from hf, map_zero] at this
    exact this.symm
  · intro k
    obtain ⟨i, hi⟩ := hz k
    refine ⟨i, ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    change pointConeMap F z (X ⟨k, i⟩) ≠ 0
    rw [pointConeMap, aeval_X]
    exact mul_ne_zero (by simpa using hi) (X_ne_zero _)

end PointIdealMultiProj

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSymmetricSpanHsymm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial Finset

namespace SymmetricSpanHsymm

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem sum_esymm_mul_hsymm_int {k : ℕ} (hk : k ≠ 0) :
    ∑ s ∈ range (k + 1), (-1) ^ s * esymm σ ℤ s * hsymm σ ℤ (k - s) = 0 := by
  apply map_injective (Int.castRingHom ℂ) Int.cast_injective
  apply MvPolynomial.funext
  intro x
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_esymm, map_hsymm, map_zero]
  simp [GroundTheory.Heights₂.Theta.SymmFun.sum_esymm_mul_hsymm x k, hk]

theorem esymm_mem_adjoin (k : ℕ) :
    esymm σ ℤ k ∈ Algebra.adjoin ℤ (Set.range (hsymm σ ℤ)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  set A := Algebra.adjoin ℤ (Set.range (hsymm σ ℤ))
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [esymm_zero]; exact one_mem A
  have h := sum_esymm_mul_hsymm_int (σ := σ) hk.ne'
  rw [sum_range_succ, Nat.sub_self, hsymm_zero, mul_one] at h
  have h2 : ((-1 : MvPolynomial σ ℤ) ^ k) * (-1) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  have he : esymm σ ℤ k =
      -((-1) ^ k * ∑ s ∈ range k, (-1) ^ s * esymm σ ℤ s * hsymm σ ℤ (k - s)) := by
    linear_combination (-1 : MvPolynomial σ ℤ) ^ k * h - esymm σ ℤ k * h2
  have hm1 : ∀ j : ℕ, (-1 : MvPolynomial σ ℤ) ^ j ∈ A := fun j => pow_mem (neg_mem (one_mem A)) j
  rw [he]
  refine neg_mem (mul_mem (hm1 k) (sum_mem fun s hs => mul_mem (mul_mem (hm1 s)
    (ih s (mem_range.mp hs))) (Algebra.subset_adjoin ⟨k - s, rfl⟩)))


omit [Fintype σ] [DecidableEq σ] in
theorem isHomogeneous_prod_map_X (t : Multiset σ) :
    ((t.map (X : σ → MvPolynomial σ ℤ)).prod).IsHomogeneous (Multiset.card t) := by
  induction t using Multiset.induction_on with
  | empty => simpa using isHomogeneous_one σ ℤ
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm]
    exact (isHomogeneous_X ℤ a).mul ih

theorem isHomogeneous_hsymm_int (a : ℕ) : (hsymm σ ℤ a).IsHomogeneous a := by
  unfold hsymm
  refine IsHomogeneous.sum _ _ _ fun s _ => ?_
  have := isHomogeneous_prod_map_X (σ := σ) s.1
  rwa [s.2] at this

theorem isHomogeneous_prod_map_hsymm (t : Multiset ℕ) :
    ((t.map (hsymm σ ℤ)).prod).IsHomogeneous t.sum := by
  induction t using Multiset.induction_on with
  | empty => simpa using isHomogeneous_one σ ℤ
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact (isHomogeneous_hsymm_int a).mul ih

theorem isHomogeneous_hsymmPart {n : ℕ} (μ : n.Partition) : (hsymmPart σ ℤ μ).IsHomogeneous n := by
  have := isHomogeneous_prod_map_hsymm (σ := σ) μ.parts
  rwa [μ.parts_sum] at this

theorem exists_hsymmPart_of_mem_closure {x : MvPolynomial σ ℤ}
    (hx : x ∈ Submonoid.closure (Set.range (hsymm σ ℤ))) :
    ∃ (n : ℕ) (μ : n.Partition), x = hsymmPart σ ℤ μ := by
  induction hx using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact ⟨a, .indiscrete a, (hsymmPart_indiscrete σ ℤ a).symm⟩
  | one => exact ⟨0, .indiscrete 0, (hsymmPart_zero σ ℤ).symm⟩
  | mul y z _ _ hy hz =>
    obtain ⟨n, μ, rfl⟩ := hy
    obtain ⟨n', ν, rfl⟩ := hz
    refine ⟨n + n', ⟨μ.parts + ν.parts, fun {i} hi => ?_, ?_⟩, ?_⟩
    · rcases Multiset.mem_add.mp hi with h | h
      exacts [μ.parts_pos h, ν.parts_pos h]
    · rw [Multiset.sum_add, μ.parts_sum, ν.parts_sum]
    · simp only [hsymmPart, Multiset.map_add (f := _), Multiset.prod_add]

theorem proof : SymmetricSpanHsymm.Statement := by
  intro N m G hG hsym
  set S := Submodule.span ℤ (Set.range fun μ : m.Partition => hsymmPart (Fin N) ℤ μ)
  have hA : G ∈ Algebra.adjoin ℤ (Set.range (hsymm (Fin N) ℤ)) := by
    obtain ⟨p, hp⟩ := esymmAlgHom_fin_surjective ℤ (le_refl N) ⟨G, hsym⟩
    have hG' : G = aeval (fun i : Fin N => esymm (Fin N) ℤ (i + 1)) p := by
      rw [← esymmAlgHom_apply, hp]
    rw [hG']
    clear hp hG'
    induction p using MvPolynomial.induction_on with
    | C r => rw [aeval_C]; exact Subalgebra.algebraMap_mem _ r
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp => rw [map_mul, aeval_X]; exact mul_mem hp (esymm_mem_adjoin _)
  have hspan : G ∈ Submodule.span ℤ
      (Submonoid.closure (Set.range (hsymm (Fin N) ℤ)) : Set (MvPolynomial (Fin N) ℤ)) := by
    rw [← Algebra.adjoin_eq_span, Subalgebra.mem_toSubmodule]
    exact hA
  have hle : Submodule.span ℤ
      (Submonoid.closure (Set.range (hsymm (Fin N) ℤ)) : Set (MvPolynomial (Fin N) ℤ)) ≤
      S.comap (homogeneousComponent m) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨n, μ, rfl⟩ := exists_hsymmPart_of_mem_closure hx
    show homogeneousComponent m (hsymmPart (Fin N) ℤ μ) ∈ S
    rw [homogeneousComponent_of_mem (isHomogeneous_hsymmPart μ)]
    split_ifs with h
    · subst h; exact Submodule.subset_span ⟨μ, rfl⟩
    · exact zero_mem S
  have := hle hspan
  rwa [Submodule.mem_comap, homogeneousComponent_eq_self hG] at this

end SymmetricSpanHsymm

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinDivCycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx)

def JoinDivCycle.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)) (f : MRing ι R),
    ReciprocityTheory.ChartRestriction.G.Geo.divCycle (P.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx) f) =
      Finsupp.mapDomain (Ideal.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

