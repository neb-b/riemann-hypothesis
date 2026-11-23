module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.FiberCardHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGF
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S IsDedekindDomain
open Classical ValuativeRel

def piO {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E) (ϖ : 𝒪[F]) : L.O :=
  ⟨algebraMap F E ϖ, (L.O_def _).2 (by
    rw [show algebraMap F E (ϖ : F) = algebraMap 𝒪[F] E ϖ from
      (IsScalarTower.algebraMap_apply 𝒪[F] F E ϖ).symm]
    exact isIntegral_algebraMap)⟩

def FLocO : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E), IsNonarchimedeanLocalField F → CharZero F →
    (∀ x : E, x ≠ 0 → IsUnit x) → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      (∀ x ∈ L.O, (¬ ∃ z ∈ L.O, x = algebraMap F E ϖ * z) → ∃ y ∈ L.O, x * y = 1) ∧
      (∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ L.O) ∧
      (∀ x ∈ L.O, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u)

def FResField : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E), IsNonarchimedeanLocalField F → CharZero F →
    (∀ x : E, x ≠ 0 → IsUnit x) → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      (Ideal.span {piO L ϖ}).IsMaximal ∧
      Nat.card (L.O ⧸ Ideal.span {piO L ϖ}) = Nat.card 𝓀[F] ^ 2 ∧
      ∀ x y : L.O, (y : E) = L.cj x →
        Ideal.Quotient.mk (Ideal.span {piO L ϖ}) y =
          Ideal.Quotient.mk (Ideal.span {piO L ϖ}) x ^ Nat.card 𝓀[F]

def FLatBasis : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E), IsNonarchimedeanLocalField F →
    CharZero F → (∀ x : E, x ≠ 0 → IsUnit x) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ →
      ∃ b : Fin (Module.finrank E V) → V, (∀ k, b k ∈ Λ) ∧ LinearIndependent E b ∧
        (∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧ x = ∑ k, c k • b k) ∧
        ∃ Q : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E, (∀ k l, Q k l ∈ M.L.O) ∧
          Q * Matrix.of (fun k l => H.h (b k) (b l)) = 1

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGS
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

def SplitCount : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    (∃ e : E ≃ₐ[F] F × F, ∀ x, e (M.L.cj x) = (e x).swap) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E), (∀ a b, G₀ a b ∈ M.L.O) →
        (∀ a b, G₀ b a = M.L.cj (G₀ a b)) → (∃ y ∈ M.L.O, G₀.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
        ∃ (Ph : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) 𝓀[F])
          (Gm : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝓀[F]),
          IsUnit Ph.det ∧ Gm.rank = Fintype.card ι ∧
          H.dens ϖ Λ G₀ * (Nat.card 𝓀[F] : ℝ) ^
              ((2 * Module.finrank E V * Fintype.card ι : ℤ) - (Fintype.card ι : ℤ) ^ 2) =
            (Formalism.L2.SG.DensExact.countSplit 𝓀[F] (Module.finrank E V) (Fintype.card ι) Ph Gm : ℝ)

def OSplit : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E), IsNonarchimedeanLocalField F →
    ∀ (e : E ≃ₐ[F] F × F) (x : E), x ∈ L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]

def IsSplitCoord {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} (e : E ≃ₐ[F] F × F)
    {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) {n : ℕ}
    (π : V ≃+ (Fin n → F) × (Fin n → F)) (Ph : Matrix (Fin n) (Fin n) 𝒪[F]) : Prop :=
  (∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2)) ∧
  (∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) ∧
  IsUnit Ph.det ∧
  ∀ x y : V, e (H.h x y) =
    (∑ k, ∑ l, (π x).1 k * (Ph k l : F) * (π y).2 l, ∑ k, ∑ l, (π y).1 k * (Ph k l : F) * (π x).2 l)

def CoordData : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    ∀ (e : E ≃ₐ[F] F × F), (∀ x, e (M.L.cj x) = (e x).swap) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ →
      ∃ (π : V ≃+ (Fin (Module.finrank E V) → F) × (Fin (Module.finrank E V) → F))
        (Ph : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) 𝒪[F]), IsSplitCoord e H Λ π Ph

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.EichLApply
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def InW (D : Formalism.BasicNotions.D7) (y : (VS D).V) : Prop :=
  (∀ a, (VS D).hT (D.sp.hypE a) y = 0) ∧ (∀ a, (VS D).hT (D.sp.hypF a) y = 0) ∧ (VS D).hT D.sp.zm y = 0

theorem hT_star (D : Formalism.BasicNotions.D7) (x y : (VS D).V) : star ((VS D).hT x y) = (VS D).hT y x := by
  have h := (VS D).herm
  first
  | exact h x y
  | exact h.eq x y
  | simpa using h x y
  | simpa using h.eq x y

theorem T_ne (D : Formalism.BasicNotions.D7) : (D.sp.T : D.host.E) ≠ 0 := by
  have h := D.sp.T_prime.ne_zero
  exact_mod_cast h

theorem hZE (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT D.sp.zm (D.sp.hypE i) = 0 := by exact (D.sp.hyp_orthz i).1
theorem hZF (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT D.sp.zm (D.sp.hypF i) = 0 := by exact (D.sp.hyp_orthz i).2
theorem hEZ (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT (D.sp.hypE i) D.sp.zm = 0 := by
  rw [← hT_star D D.sp.zm (D.sp.hypE i), hZE, star_zero]
theorem hFZ (D : Formalism.BasicNotions.D7) (i : Fin D.R.rS) : (VS D).hT (D.sp.hypF i) D.sp.zm = 0 := by
  rw [← hT_star D D.sp.zm (D.sp.hypF i), hZF, star_zero]

def pWL (D : Formalism.BasicNotions.D7) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id - ∑ a, ((VS D).hT (D.sp.hypF a)).smulRight (D.sp.hypE a)
    - ∑ a, ((VS D).hT (D.sp.hypE a)).smulRight (D.sp.hypF a)
    + ((D.sp.T : D.host.E)⁻¹) • ((VS D).hT D.sp.zm).smulRight D.sp.zm

theorem pW_eq (D : Formalism.BasicNotions.D7) (v : (VS D).V) : pW D v = pWL D v := by
  simp only [pW, pWL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, smul_smul, div_eq_inv_mul]

theorem pW_sub (D : Formalism.BasicNotions.D7) (u v : (VS D).V) : pW D (u - v) = pW D u - pW D v := by simp only [pW_eq, map_sub]

private theorem hT_hypF_hypE (D : Formalism.BasicNotions.D7) (a i : Fin D.R.rS) :
    (VS D).hT (D.sp.hypF a) (D.sp.hypE i) = if a = i then 1 else 0 := by
  rw [← hT_star D (D.sp.hypE i) (D.sp.hypF a), D.sp.hyp_ef i a]
  by_cases h : a = i
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem inW_pW (D : Formalism.BasicNotions.D7) (v : (VS D).V) : InW D (pW D v) := by
  have hT0 := T_ne D
  unfold InW
  refine ⟨fun b => ?_, fun b => ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [pW, map_sum, D.sp.hyp_ee, D.sp.hyp_ef, hEZ, mul_ite, Finset.sum_ite_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [pW, map_sum, hT_hypF_hypE, D.sp.hyp_ff, hFZ, mul_ite, Finset.sum_ite_eq']
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [pW, map_sum, hZE, hZF, D.sp.zm_norm, div_mul_cancel₀, hT0]

def eichL (D : Formalism.BasicNotions.D7) (e y : (VS D).V) (c : D.host.E) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id + ((VS D).hT e).smulRight y - ((VS D).hT y).smulRight e + c • ((VS D).hT e).smulRight e

theorem eichL_apply (D : Formalism.BasicNotions.D7) (e y : (VS D).V) (c : D.host.E) (v : (VS D).V) :
    eichL D e y c v = v + (VS D).hT e v • y - (VS D).hT y v • e + (c * (VS D).hT e v) • e := by
  simp only [eichL, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply, smul_smul]

theorem eich_inv (D : Formalism.BasicNotions.D7) {e y : (VS D).V} {c : D.host.E} (he : (VS D).hT e e = 0)
    (hey : (VS D).hT e y = 0) (hye : (VS D).hT y e = 0) (hc : c + c + (VS D).hT y y = 0) (v : (VS D).V) :
    eichL D e (-y) c (eichL D e y c v) = v := by
  have h1 : (VS D).hT e (eichL D e y c v) = (VS D).hT e v := by
    simp [eichL_apply, he, hey]
  have h2 : (VS D).hT y (eichL D e y c v) = (VS D).hT y v + (VS D).hT e v * (VS D).hT y y := by
    simp [eichL_apply, hye] <;> ring
  have hc' : (VS D).hT e v * (c + c + (VS D).hT y y) = 0 := by rw [hc, mul_zero]
  rw [eichL_apply D e (-y) c (eichL D e y c v), h1]
  simp only [map_neg, LinearMap.neg_apply, h2]
  rw [eichL_apply D e y c v]
  linear_combination (norm := module) hc' • e

theorem eich_isom (D : Formalism.BasicNotions.D7) {e y : (VS D).V} {c : D.host.E} (he : (VS D).hT e e = 0)
    (hey : (VS D).hT e y = 0) (hye : (VS D).hT y e = 0) (hc : c + star c + (VS D).hT y y = 0)
    (u v : (VS D).V) : (VS D).hT (eichL D e y c u) (eichL D e y c v) = (VS D).hT u v := by
  have hE : ∀ w, (VS D).hT e (eichL D e y c w) = (VS D).hT e w := fun w => by
    simp [eichL_apply, he, hey]
  have hY : ∀ w, (VS D).hT y (eichL D e y c w) = (VS D).hT y w + (VS D).hT e w * (VS D).hT y y := fun w => by
    simp [eichL_apply, hye] <;> ring
  have hU : ∀ w, (VS D).hT u (eichL D e y c w) = (VS D).hT u w + (VS D).hT e w * star ((VS D).hT y u)
      - (VS D).hT y w * star ((VS D).hT e u) + c * (VS D).hT e w * star ((VS D).hT e u) := fun w => by
    rw [hT_star D y u, hT_star D e u]
    simp [eichL_apply] <;> ring
  rw [eichL_apply D e y c u]
  simp only [map_add (f := _), map_sub, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hE, hY, hU, starRingEnd_apply, star_mul']
  linear_combination (star ((VS D).hT e u) * (VS D).hT e v) * hc

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.EulerFactorTwo
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S

theorem locE_isUnit_or_exists_algEquiv_prod_swap {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) :
    (∀ x : E, x ≠ 0 → IsUnit x) ∨ ∃ e : E ≃ₐ[F] F × F, ∀ x, e (L.cj x) = (e x).swap := by
  classical
  have hrank := L.rank
  have : Module.Free F E := L.free
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [hrank]; norm_num)
  have : IsReduced E := L.reduced
  by_cases hfield : ∀ x : E, x ≠ 0 → IsUnit x
  · exact Or.inl hfield
  right
  obtain ⟨x, hx⟩ := not_forall.1 hfield
  have hx0 : x ≠ 0 := fun heq => hx (fun hne => (hne heq).elim)
  have hxu : ¬ IsUnit x := fun hu => hx (fun _ => hu)
  have hfix : ∀ y : E, L.cj y = y → ∃ a : F, algebraMap F E a = y := fun y hy => (L.cj_fix y).1 hy
  obtain ⟨a, ha⟩ := hfix (x * L.cj x) (by rw [map_mul, L.cj_cj, mul_comm])
  have hN : x * L.cj x = 0 := by
    by_contra hne
    apply hxu
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact hne ha.symm
    refine IsUnit.of_mul_eq_one (L.cj x * algebraMap F E a⁻¹) ?_
    rw [← mul_assoc, ← ha, ← map_mul, mul_inv_cancel₀ ha0, map_one]
  obtain ⟨t, ht⟩ := hfix (x + L.cj x) (by rw [map_add (f := _), L.cj_cj, add_comm])
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at ht
    have hc : L.cj x = -x := by linear_combination -ht
    have hsq : x ^ 2 = 0 := by
      rw [hc] at hN
      linear_combination -hN
    exact hx0 (IsReduced.eq_zero x ⟨2, hsq⟩)
  have hcu : L.cj (algebraMap F E t⁻¹) = algebraMap F E t⁻¹ := L.cj.commutes _
  have hpq : x * algebraMap F E t⁻¹ + L.cj x * algebraMap F E t⁻¹ = 1 := by
    rw [← add_mul, ← ht, ← map_mul, mul_inv_cancel₀ ht0, map_one]
  set p := x * algebraMap F E t⁻¹ with hp
  set q := L.cj x * algebraMap F E t⁻¹ with hq
  have hpq0 : p * q = 0 := by
    rw [hp, hq]
    linear_combination (algebraMap F E t⁻¹ * algebraMap F E t⁻¹) * hN
  have hqp : q * p = 0 := by rw [mul_comm]; exact hpq0
  have hcp : L.cj p = q := by rw [hp, hq, map_mul, hcu]
  have hcq : L.cj q = p := by rw [hp, hq, map_mul, hcu, L.cj_cj]
  have hpp : p * p = p := by
    have h : p * (p + q) = p := by rw [hpq, mul_one]
    linear_combination h - hpq0
  have hqq : q * q = q := by
    have h : (p + q) * q = q := by rw [hpq, one_mul]
    linear_combination h - hpq0
  have hp0 : p ≠ 0 := by
    intro h
    have h1 : q = 1 := by rw [← hpq, h, zero_add]
    apply one_ne_zero (α := E)
    rw [← h1, ← hcp, h, map_zero]
  have hq0 : q ≠ 0 := by
    intro h
    have h1 : p = 1 := by rw [← hpq, h, add_zero]
    apply one_ne_zero (α := E)
    rw [← h1, ← hcq, h, map_zero]
  let g : (F × F) →ₐ[F] E :=
    { toFun := fun z => z.1 • p + z.2 • q
      map_one' := by simp [hpq]
      map_mul' := fun z w => by
        simp only [Prod.fst_mul, Prod.snd_mul, Algebra.smul_def, map_mul]
        linear_combination (-(algebraMap F E z.1 * algebraMap F E w.1)) * hpp -
          (algebraMap F E z.2 * algebraMap F E w.2) * hqq -
          (algebraMap F E z.1 * algebraMap F E w.2 + algebraMap F E z.2 * algebraMap F E w.1) * hpq0
      map_zero' := by simp
      map_add' := fun z w => by
        simp only [Prod.fst_add, Prod.snd_add, add_smul]
        abel
      commutes' := fun r => by
        simp only [Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        rw [← smul_add, hpq, Algebra.algebraMap_eq_smul_one] }
  have ginj : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    have hz' : z.1 • p + z.2 • q = 0 := hz
    have h1 : z.1 • p = 0 := by
      have h := congrArg (· * p) hz'
      simp only [add_mul, smul_mul_assoc, hpp, hqp, smul_zero, add_zero, zero_mul] at h
      exact h
    have h2 : z.2 • q = 0 := by
      have h := congrArg (· * q) hz'
      simp only [add_mul, smul_mul_assoc, hqq, hpq0, smul_zero, zero_add, zero_mul] at h
      exact h
    rw [smul_eq_zero] at h1 h2
    exact Prod.ext (h1.resolve_right hp0) (h2.resolve_right hq0)
  have gsurj : Function.Surjective g := by
    have hdim : Module.finrank F (F × F) = Module.finrank F E := by
      rw [Module.finrank_prod, Module.finrank_self, hrank]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := g.toLinearMap)).1 ginj
  let e0 := AlgEquiv.ofBijective g ⟨ginj, gsurj⟩
  refine ⟨e0.symm, fun y => ?_⟩
  obtain ⟨z, rfl⟩ := gsurj y
  have hez : e0.symm (g z) = z := e0.symm_apply_apply z
  have hcz : L.cj (g z) = g z.swap := by
    show L.cj (z.1 • p + z.2 • q) = z.2 • p + z.1 • q
    rw [map_add (f := _), map_smul, map_smul, hcp, hcq, add_comm]
  rw [hcz, hez]
  exact e0.symm_apply_apply z.swap

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDeltaC
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.DeltaC

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S.Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem mem_of_isIntegral_fp (L : LocAt F E sig p) {s : L.Fp} (hs : IsIntegral 𝒪[L.Fp] s) : s ∈ 𝒪[L.Fp] := by
  exact (Valuation.integer.integers (ValuativeRel.valuation L.Fp)).mem_of_integral hs

theorem trace_mem (L : LocAt F E sig p) {y : L.Ep} (hy : y ∈ L.O) : Algebra.trace L.Fp L.Ep y ∈ 𝒪[L.Fp] := by
  haveI := L.free
  haveI := PI.ProdFormulaE.Base.finite L
  let b : Module.Basis (Fin 2) L.Fp L.Ep := Module.finBasisOfFinrankEq L.Fp L.Ep L.rank
  exact mem_of_isIntegral_fp L (DeltaB.trace_isIntegral_rank2 b ((L.O_def y).mp hy))

end PI.UnitaryGroupMassFormula.CntFormula.DeltaC
end
end

