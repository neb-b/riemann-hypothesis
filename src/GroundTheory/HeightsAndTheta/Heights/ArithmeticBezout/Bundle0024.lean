module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartNormAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartNormAlgClosed

section Chart

variable {F : Type} [Field F] {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
  (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime]

theorem algebraMap_tower (x : MvPolynomial (Fin e × Fin n) F) :
    algebraMap (Localization.AtPrime p) (ChartLoc I t e p) (algebraMap _ _ x) =
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap _ (ChartInc I t e) x) := by
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem chartX_C (c : F) :
    chartX I t e (C c) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C c) := by
  show Ideal.Quotient.mk _ (rename Sum.inl (C c)) = Ideal.Quotient.mk _ (rename Sum.inr (C c))
  simp only [rename_C]

theorem algebraMap_localization_C (c : F) :
    algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p) (C c) =
      algebraMap F (Localization.AtPrime p) c := by
  rw [IsScalarTower.algebraMap_apply F (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p),
    MvPolynomial.algebraMap_eq]

theorem chartLin_eq_sum (u : Fin n → F) :
    algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u) =
      ∑ m, algebraMap F (Localization.AtPrime p) (u m) •
        algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [chartLin, linForm, map_sum, map_mul, Algebra.smul_def]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← algebraMap_localization_C p, algebraMap_tower, chartX_C]

theorem chartLin_self : chartLin I t e t = 1 := by
  have h : chartX I t e (linForm t - 1) = 0 := by
    exact (Ideal.Quotient.eq_zero_iff_mem (I := chartIncIdeal I t e)).mpr
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))))
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h

theorem adjoin_eq_top :
    Algebra.adjoin (Localization.AtPrime p)
        (Set.range fun m => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m))) = ⊤ := by
  set A := Algebra.adjoin (Localization.AtPrime p)
    (Set.range fun m => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)))
  have hS : ∀ x : MvPolynomial (Fin e × Fin n) F,
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap _ (ChartInc I t e) x) ∈ A := by
    intro x
    rw [← algebraMap_tower]
    exact Subalgebra.algebraMap_mem A _
  let π : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* ChartInc I t e := Ideal.Quotient.mk (chartIncIdeal I t e)
  have hSig : ∀ y : MvPolynomial (Fin n ⊕ Fin e × Fin n) F,
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (π y) ∈ A := by
    intro y
    induction y using MvPolynomial.induction_on with
    | C a =>
      have h : π (C a) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C a) := by
        show _ = Ideal.Quotient.mk _ (rename Sum.inr (C a))
        rw [rename_C]
        rfl
      rw [h]
      exact hS _
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem ha hb
    | mul_X a v ha =>
      rw [map_mul, map_mul]
      refine mul_mem ha ?_
      rcases v with m | im
      · refine Algebra.subset_adjoin ⟨m, ?_⟩
        show algebraMap (ChartInc I t e) (ChartLoc I t e p)
          ((Ideal.Quotient.mk (chartIncIdeal I t e) (rename Sum.inl (X m)) : ChartInc I t e)) = _
        rw [rename_X]
        rfl
      · have h : π (X (Sum.inr im)) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (X im) := by
          show _ = Ideal.Quotient.mk _ (rename Sum.inr (X im))
          rw [rename_X]
          rfl
        rw [h]
        exact hS _
  rw [eq_top_iff]
  intro z _
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl) z
  obtain ⟨s₀, hs₀, hs⟩ := s.2
  obtain ⟨y, rfl⟩ : ∃ y, π y = x := Ideal.Quotient.mk_surjective x
  set w := algebraMap (Localization.AtPrime p) (ChartLoc I t e p)
    (IsLocalization.mk' (Localization.AtPrime p) (1 : MvPolynomial (Fin e × Fin n) F) ⟨s₀, hs₀⟩)
  have hw : algebraMap (ChartInc I t e) (ChartLoc I t e p) (s : ChartInc I t e) * w = 1 := by
    rw [← hs, ← algebraMap_tower, ← map_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one,
      IsLocalization.mk'_self, map_one]
  have hz : IsLocalization.mk' (ChartLoc I t e p) (π y) s =
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (π y) * w := by
    rw [IsLocalization.mk'_eq_iff_eq_mul, mul_assoc, mul_comm w, hw, mul_one]
  show IsLocalization.mk' (ChartLoc I t e p) (π y) s ∈ A
  rw [hz]
  exact mul_mem (hSig y) (Subalgebra.algebraMap_mem A _)

end Chart

theorem eval_map_firstGroup {F : Type} [Field F] {n e : ℕ} (p : Ideal (MvPolynomial (Fin e × Fin n) F))
    [p.IsPrime] (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F) :
    eval (fun m => algebraMap F (Localization.AtPrime p) (u m))
        (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) (firstGroup f)) =
      algebraMap _ (Localization.AtPrime p) (specFirst f u) := by
  rw [eval_map]
  simp only [firstGroup, specFirst]
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, bind₁_C_right, MvPolynomial.algebraMap_apply, eval₂_C, MvPolynomial.algebraMap_eq]
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), eval₂_add, ha, hb, map_add (f := _)]
  | mul_X a ij ha =>
    rw [map_mul, map_mul, eval₂_mul, ha, map_mul, aeval_X, bind₁_X_right]
    congr 1
    obtain ⟨i, m⟩ := ij
    cases i using Fin.cases with
    | zero => simp [specFirstVar, algebraMap_localization_C]
    | succ i => simp [specFirstVar]

end ChartNormAlgClosed


open ChartNormAlgClosed in
theorem ChartNormAlgClosed.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : LocalizationPrimeDVR.Statement) (h₄ : ChartFinite.Statement) (h₅ : ChartLocDomain.Statement)
    (h₆ : ChartFirstGroupPrime.Statement) (h₇ : ChartFirstGroupDvd.Statement)
    (h₈ : NormOfDividedFormSep.Statement) (h₉ : ChartFracSeparable.Statement) :
    ChartNormAlgClosed.Statement := by
  intro F _ _ n e I f t p _ hI hf hp hft u
  have htI : linForm t ∉ I := by
    intro h
    have hmem := h₂ F n e I I f t hf le_rfl h
    rw [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem
    exact hft (hmem ▸ p.zero_mem)
  obtain ⟨hdom, hinj, -⟩ := h₅ F n e I f t p hI hf htI
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₄ F n e I f t p hI hf hft
  have : IsPrincipalIdealRing (Localization.AtPrime p) := by
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · have hfield : IsField (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F))) := by
        rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal,
          Ideal.map_bot]
      let := hfield.toField
      infer_instance
    · have := h₃ _ q _ hq rfl
      infer_instance
  have : Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc I t e p) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hinj
  have : Module.Free (Localization.AtPrime p) (ChartLoc I t e p) := Module.free_of_finite_type_torsion_free'
  have hsum : ∑ m, algebraMap F (Localization.AtPrime p) (t m) •
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)) = 1 := by
    rw [← chartLin_eq_sum, chartLin_self, map_one]
  have hcomp : (algebraMap (ChartInc I t e) (ChartLoc I t e p)).comp
      (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) =
      (algebraMap (Localization.AtPrime p) (ChartLoc I t e p)).comp
        (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) :=
    RingHom.ext fun x => (algebraMap_tower I t p x).symm
  have hdvd := map_dvd (MvPolynomial.map (algebraMap (ChartInc I t e) (ChartLoc I t e p)))
    (h₇ F n e I f t hI hf htI)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_X, map_C, map_map, hcomp] at hdvd
  rw [← map_map] at hdvd
  have : Infinite F := IsAlgClosed.instInfinite
  have : Infinite (Localization.AtPrime p) :=
    Infinite.of_injective _ (algebraMap F (Localization.AtPrime p)).injective
  have key := h₈ (Localization.AtPrime p) (ChartLoc I t e p) n _ _ _ ?sep (adjoin_eq_top I t p) hsum
    (h₆ F n e I f p hI hf) hdvd (fun m => algebraMap F (Localization.AtPrime p) (u m))
  case sep =>
    let _ := FractionRing.liftAlgebra (Localization.AtPrime p) (FractionRing (ChartLoc I t e p))
    exact @h₉ F _ _ n e I f t p _ _ _ _ _ OreLocalization.instAlgebra Localization.isLocalization _ Localization.isLocalization _ _
      (FractionRing.isScalarTower_liftAlgebra _ _) _ hI hf htI
  rw [eval_map_firstGroup, eval_map_firstGroup, ← chartLin_eq_sum] at key
  exact key

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSecRankSpecialize
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SecRankSpecialize

open Vertical

def secMap {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {n e : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) :
    SecAlg Q y →ₐ[R] SecAlg (Q.map (MvPolynomial.map (algebraMap R S))) (algebraMap R S ∘ y) :=
  Ideal.quotientMapₐ _ (MvPolynomial.mapAlgHom (Algebra.ofId R S))
    (by rw [SecAlgFieldChange.secIdeal_map]; exact Ideal.le_comap_map)

theorem secMap_mk {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {n e : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) (p : MvPolynomial (Fin n) R) :
    secMap S Q y (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) p) := rfl

theorem mem_maximalIdeal_smul_of_secMap_eq_zero {R : Type*} [CommRing R] [IsLocalRing R]
    (κ : Type*) [Field κ] [Algebra R κ] (hsurj : Function.Surjective (algebraMap R κ)) {n e : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) (x : SecAlg Q y)
    (hx : secMap κ Q y x = 0) :
    x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (SecAlg Q y)) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hker : RingHom.ker (algebraMap R κ) = IsLocalRing.maximalIdeal R := by
    have := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact IsLocalRing.eq_maximalIdeal this
  have hp : p ∈ secIdeal Q y ⊔ Ideal.map C (IsLocalRing.maximalIdeal R) := by
    rw [secMap_mk, Ideal.Quotient.eq_zero_iff_mem, SecAlgFieldChange.secIdeal_map,
      ← Ideal.mem_comap,
      Ideal.comap_map_of_surjective _ (MvPolynomial.map_surjective _ hsurj),
      ← RingHom.ker_eq_comap_bot, MvPolynomial.ker_map, hker] at hx
    exact hx
  have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk (secIdeal Q y)) hp
  rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_map] at hm
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
  have he : (Ideal.Quotient.mk (secIdeal Q y)).comp C = algebraMap R (SecAlg Q y) :=
    RingHom.ext fun _ => rfl
  rwa [he] at hm

end SecRankSpecialize


open SecRankSpecialize in
theorem SecRankSpecialize.proof : SecRankSpecialize.Statement := by
  intro R K κ _ _ _ _ _ _ _ _ n e Q y hsurj hfin
  classical
  let ρ := secMap κ Q y
  let ι := secMap K Q y
  have hρ : Function.Surjective ρ := by
    intro z
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective _ hsurj q
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  have : Module.Finite R
      (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y)) :=
    Module.Finite.of_surjective ρ.toLinearMap hρ
  have : Module.Finite κ
      (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y)) :=
    Module.Finite.of_restrictScalars_finite R κ _
  let v := Module.finBasis κ
    (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y))
  choose b hb using fun i => hρ (v i)

  have htop : Submodule.span R (Set.range b) = ⊤ := by
    refine top_unique (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson _) ?_)
    intro x _
    choose r hr using fun i => hsurj (v.repr (ρ x) i)
    have hsum : ∑ i, r i • ρ (b i) = ρ x := by
      conv_rhs => rw [← v.sum_repr (ρ x)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb, ← hr i, algebraMap_smul]
    have hz : ρ (x - ∑ i, r i • b i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum]
      simp only [map_smul]
      rw [hsum, sub_self]
    have hm := mem_maximalIdeal_smul_of_secMap_eq_zero κ hsurj Q y _ hz
    have hx : x = ∑ i, r i • b i + (x - ∑ i, r i • b i) := by abel
    rw [hx]
    exact Submodule.add_mem_sup
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) hm

  have hB : ∀ x, ι x ∈ Submodule.span K (Set.range fun i => ι (b i)) := by
    intro x
    have hx : x ∈ Submodule.span R (Set.range b) := htop ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add u w _ _ hu hw => rw [map_add (f := _)]; exact Submodule.add_mem _ hu hw
    | smul c u _ hu => rw [map_smul, ← algebraMap_smul K]; exact Submodule.smul_mem _ _ hu
  have hspan : Submodule.span K (Set.range fun i => ι (b i)) = ⊤ := by
    refine eq_top_iff.mpr fun z hz => ?_
    clear hz
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction p using MvPolynomial.induction_on' with
    | monomial u a =>
      have hmon : (Ideal.Quotient.mk _ (monomial u a) :
          Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R K))) (algebraMap R K ∘ y)) =
          a • ι (Ideal.Quotient.mk _ (monomial u 1)) := by
        rw [secMap_mk, MvPolynomial.map_monomial, map_one, ← Ideal.Quotient.mkₐ_eq_mk K,
          ← map_smul, smul_monomial, smul_eq_mul, mul_one]
      rw [hmon]
      exact Submodule.smul_mem _ _ (hB _)
    | add p q hp hq => rw [map_add (f := _)]; exact Submodule.add_mem _ hp hq
  calc Module.finrank K
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R K))) (algebraMap R K ∘ y))
        = Module.finrank K (Submodule.span K (Set.range fun i => ι (b i))) := by
          rw [hspan, finrank_top]
      _ ≤ Fintype.card (Fin (Module.finrank κ
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y)))) :=
          finrank_range_le_card _
      _ = _ := Fintype.card_fin _

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsFormsThroughPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def FormsThroughPoint.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)), IsProjPrime Q →
    ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≤ ((k : ℕ) : WithBot ℕ∞) →
    ∀ x : Fin n → AlgebraicClosure F, x ≠ 0 → (∃ q ∈ Q, aeval x q ≠ 0) →
      ∃ u : Fin k × Fin n → AlgebraicClosure F, (∀ i, ∑ j, u (i, j) * x j = 0) ∧ u ∉ incidence Q k

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncIdealNeBotDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def IncIdealNeBotDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)), IsProjPrime Q →
    incIdeal Q k ≠ ⊥ → ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≤ ((k : ℕ) : WithBot ℕ∞)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsThroughPointIncIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ThroughPointIncIdeal.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)) (x c : Fin n → AlgebraicClosure F),
    ∑ j, c j * x j = 1 →
    (∀ u : Fin k × Fin n → AlgebraicClosure F, (∀ i, ∑ j, u (i, j) * x j = 0) → u ∈ incidence Q k) →
      ∀ g ∈ incIdeal Q k, aeval (genSubst (k := k) x c) g = 0

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

