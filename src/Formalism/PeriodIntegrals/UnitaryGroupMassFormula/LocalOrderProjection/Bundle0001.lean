module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalOrderProjection.LocOProjOf

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalOrderProjection.IsFieldOfNonsq
section
noncomputable section

open ValuativeRel
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.OProj

section Fld

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem isField_of_nonsq [CharZero F] (L : LocE F E) (θ : E) (hc : L.cj θ = -θ) (D : F)
    (hD0 : D ≠ 0) (hD : θ * θ = algebraMap F E D) (hns : ¬ ∃ s : F, s * s = D) : IsField E := by
  have := SlopeTestRemainingChoices.nontrivial_E L
  have hinj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  have h2D : (2 * D : F) ≠ 0 := mul_ne_zero two_ne_zero hD0
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {x} hx => ?_⟩
  obtain ⟨n, hn⟩ := SlopeTestRemainingChoices.nm_ex L x
  by_cases hn0 : n = 0
  · exfalso
    obtain ⟨t, c, -, -, hdec⟩ := SlopeTestRemainingChoices.decomp L θ hc D hD x
    have hcjx : algebraMap F E (2 * D) * L.cj x = algebraMap F E (D * t) - algebraMap F E c * θ := by
      have h := congrArg L.cj hdec
      simp only [map_add (f := _), map_mul, AlgEquiv.commutes, hc] at h
      simp only [map_mul]
      linear_combination h
    have hprod : (algebraMap F E (D * t)) ^ 2 - (algebraMap F E c) ^ 2 * algebraMap F E D = 0 := by
      have h0 : (algebraMap F E (2 * D) * x) * (algebraMap F E (2 * D) * L.cj x) = 0 := by
        rw [mul_mul_mul_comm, ← hn, hn0, map_zero, mul_zero]
      rw [hdec, hcjx] at h0
      linear_combination h0 + (algebraMap F E c) ^ 2 * hD
    have hF : (D * t) ^ 2 - c ^ 2 * D = 0 := by
      apply hinj
      rw [map_zero, ← hprod]
      simp only [map_sub, map_pow, map_mul]
    by_cases hc0 : c = 0
    · rw [hc0] at hF hdec
      have hsq : (D * t) ^ 2 = 0 := by linear_combination hF
      have hDt : D * t = 0 := (pow_eq_zero_iff two_ne_zero).mp hsq
      rw [hDt, map_zero, zero_mul, add_zero] at hdec
      have hu : IsUnit (algebraMap F E (2 * D)) := (IsUnit.mk0 _ h2D).map _
      exact hx (hu.mul_right_eq_zero.mp hdec)
    · apply hns
      refine ⟨D * t / c, ?_⟩
      rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hc0 hc0)]
      linear_combination hF
  · refine ⟨L.cj x * algebraMap F E n⁻¹, ?_⟩
    rw [← mul_assoc, ← hn, ← map_mul, mul_inv_cancel₀ hn0, map_one]

end Fld

theorem nonSqCase : NonSqCase := by
  intro F _ _ _ E _ _ _ _ M hOK θ _ hθc D hD0 hθD hns W _ _ P hP
  have := hOK.loc
  have := hOK.char0
  have hE : IsField E := isField_of_nonsq M.L θ hθc (D : F) hD0 hθD hns
  let _ : Field E := hE.toField
  have := M.L.free
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ M.L.rank
  have hO : (integralClosure 𝒪[F] E).toSubring = M.L.O := by
    ext x
    rw [M.L.O_def]
    rfl
  have : IsDedekindDomain (integralClosure 𝒪[F] E) := integralClosure.isDedekindDomain 𝒪[F] F E
  set C := integralClosure 𝒪[F] E with hC
  have : Module.IsTorsionFree 𝒪[F] C := .of_smul_eq_zero fun r c h => by
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      have h' : ((r • c : C) : E) = 0 := by rw [h]; rfl
      rw [Subalgebra.coe_smul, Algebra.smul_def, mul_eq_zero] at h'
      have hr' : algebraMap 𝒪[F] E r ≠ 0 := by
        rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]
        refine (map_ne_zero _).mpr fun h0 => hr (Subtype.ext h0)
      exact Subtype.ext (h'.resolve_left hr')
  have hfinP : {I : Ideal C | I.IsPrime}.Finite := by
    have hm := IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal 𝒪[F]) C
    refine (hm.insert ⊥).subset fun I hI => ?_
    by_cases hI0 : I = ⊥
    · exact Or.inl hI0
    · right
      have hI : I.IsPrime := hI
      have hne : I.under 𝒪[F] ≠ ⊥ := fun h => hI0 (Ideal.eq_bot_of_comap_eq_bot h)
      have hmax : (I.under 𝒪[F]).IsMaximal := (Ideal.IsPrime.under 𝒪[F] I).isMaximal hne
      refine ⟨hI, ⟨(IsLocalRing.eq_maximalIdeal hmax).symm⟩⟩
  have : IsPrincipalIdealRing C := IsPrincipalIdealRing.of_finite_primes hfinP
  let e : C ≃+* M.L.O := RingEquiv.subringCongr hO
  have : IsPrincipalIdealRing M.L.O := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  have : Module.Finite M.L.O P := Module.Finite.iff_fg.mpr hP
  have : Module.IsTorsionFree M.L.O P := .of_smul_eq_zero fun r p h => by
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      have h' : ((r : E) • (p : W)) = 0 := by
        have h2 : r • (p : W) = 0 := by
          have := congrArg Subtype.val h
          simpa using this
        exact h2
      have hr' : (r : E) ≠ 0 := fun h0 => hr (Subtype.ext h0)
      exact Subtype.ext ((smul_eq_zero.mp h').resolve_left hr')
  infer_instance

end PI.LocHerm.OProj
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalOrderProjection.ProjOfFreeIdem
section
noncomputable section

open ValuativeRel
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.OProj

section Abstract

variable {A R Q : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup Q] [Module R Q]

theorem proj_of_free_idem [Module A Q] [IsScalarTower A R Q] [Module.Free A Q] (e : R)
    (he : ∀ x : R, ∃ a : A, x * e = algebraMap A R a * e) (hQ : ∀ q : Q, e • q = q) :
    Module.Projective R Q := by
  classical
  let b := Module.Free.chooseBasis A Q
  let f : A → R := fun a => algebraMap A R a * e
  have hf0 : f 0 = 0 := by simp [f]
  have hfa : ∀ a c, f (a + c) = f a + f c := by intro a c; simp [f, add_mul]
  have hact : ∀ (x : R) (q : Q), ∃ a : A, x • q = a • q ∧ x * e = algebraMap A R a * e := by
    intro x q
    obtain ⟨a, ha⟩ := he x
    refine ⟨a, ?_, ha⟩
    calc x • q = x • (e • q) := by rw [hQ]
      _ = (x * e) • q := by rw [mul_smul]
      _ = (algebraMap A R a * e) • q := by rw [ha]
      _ = algebraMap A R a • (e • q) := by rw [mul_smul]
      _ = a • q := by rw [hQ, algebraMap_smul]
  have hfc : ∀ (i : Module.Free.ChooseBasisIndex A Q) (c : A), f c • b i = c • b i := by
    intro i c
    simp only [f]
    rw [mul_smul, hQ, algebraMap_smul]
  let s : Q →ₗ[R] (Module.Free.ChooseBasisIndex A Q →₀ R) :=
    { toFun := fun q => Finsupp.mapRange f hf0 (b.repr q)
      map_add' := fun q q' => by
        rw [map_add (f := _)]; exact Finsupp.mapRange_add hfa _ _
      map_smul' := fun x q => by
        obtain ⟨a, h1, h2⟩ := hact x q
        ext i
        rw [h1, LinearEquiv.map_smul]
        simp only [RingHom.id_apply, Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul, f,
          map_mul]
        rw [show x * (algebraMap A R ((b.repr q) i) * e)
            = algebraMap A R ((b.repr q) i) * (x * e) by ring, h2]
        ring }
  let π : (Module.Free.ChooseBasisIndex A Q →₀ R) →ₗ[R] Q :=
    Finsupp.linearCombination R (fun i => b i)
  refine Module.Projective.of_split s π (LinearMap.ext fun q => ?_)
  show Finsupp.linearCombination R (fun i => b i) (Finsupp.mapRange f hf0 (b.repr q)) = q
  rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by intro i; simp)]
  simp only [hfc]
  rw [← Finsupp.linearCombination_apply]
  exact b.linearCombination_repr q


variable (A) in
theorem proj_of_idem [IsDomain A] [IsPrincipalIdealRing A] [Module.Finite R Q] (e : R)
    (he : ∀ x : R, ∃ a : A, x * e = algebraMap A R a * e) (hQ : ∀ q : Q, e • q = q)
    (htf : ∀ (a : A) (q : Q), a ≠ 0 → algebraMap A R a • q = 0 → q = 0) :
    Module.Projective R Q := by
  let _ : Module A Q := Module.compHom Q (algebraMap A R)
  have : IsScalarTower A R Q := ⟨fun a x q => by
    show (a • x) • q = algebraMap A R a • (x • q)
    rw [Algebra.smul_def, mul_smul]⟩
  have : Module.Finite A Q := by
    obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R Q
    let g' : (Fin n → A) →ₗ[A] Q :=
      (g.restrictScalars A).comp (LinearMap.compLeft (Algebra.linearMap A R) (Fin n))
    refine Module.Finite.of_surjective g' fun q => ?_
    obtain ⟨r, rfl⟩ := hg q
    choose a ha using fun j => he (r j)
    refine ⟨a, ?_⟩
    have h1 : (e • r : Fin n → R) = e • (fun j => algebraMap A R (a j)) := by
      funext j
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_comm, ha j, mul_comm]
    show g (fun j => algebraMap A R (a j)) = g r
    rw [← hQ (g r), ← map_smul, h1, map_smul, hQ]
  have : Module.IsTorsionFree A Q := Module.IsTorsionFree.of_smul_eq_zero fun a q h => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr (htf a q ha h)
  have : Module.Free A Q := Module.free_of_finite_type_torsion_free'
  exact proj_of_free_idem e he hQ


variable (A) in
theorem proj_of_two_idem [IsDomain A] [IsPrincipalIdealRing A] [Module.Finite R Q] (e : R)
    (hee : e * e = e)
    (he : ∀ x : R, ∃ a : A, x * e = algebraMap A R a * e)
    (he' : ∀ x : R, ∃ a : A, x * (1 - e) = algebraMap A R a * (1 - e))
    (htf : ∀ (a : A) (q : Q), a ≠ 0 → algebraMap A R a • q = 0 → q = 0) :
    Module.Projective R Q := by
  have key : ∀ f : R, f * f = f → (∀ x : R, ∃ a : A, x * f = algebraMap A R a * f) →
      Module.Projective R (LinearMap.range (f • LinearMap.id : Q →ₗ[R] Q)) := by
    intro f hff hf
    refine proj_of_idem A f hf ?_ ?_
    · rintro ⟨_, q, rfl⟩
      apply Subtype.ext
      show f • (f • LinearMap.id : Q →ₗ[R] Q) q = (f • LinearMap.id : Q →ₗ[R] Q) q
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, hff]
    · rintro a ⟨w, hw⟩ ha h
      apply Subtype.ext
      exact htf a w ha (congrArg Subtype.val h)
  have := key e hee he
  have := key (1 - e) (by linear_combination hee) he'
  refine Module.Projective.of_split
    (LinearMap.prod (e • LinearMap.id : Q →ₗ[R] Q).rangeRestrict
      ((1 - e) • LinearMap.id : Q →ₗ[R] Q).rangeRestrict)
    ((LinearMap.range (e • LinearMap.id : Q →ₗ[R] Q)).subtype.coprod
      (LinearMap.range ((1 - e) • LinearMap.id : Q →ₗ[R] Q)).subtype)
    (LinearMap.ext fun q => ?_)
  change (e • LinearMap.id : Q →ₗ[R] Q) q + ((1 - e) • LinearMap.id : Q →ₗ[R] Q) q = q
  simp only [LinearMap.smul_apply, LinearMap.id_apply, ← add_smul, add_sub_cancel, one_smul]

end Abstract

section Concrete

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_mul_idem (L : LocE F E) (f : E) (hf : f ∈ L.O) (hff : f * f = f)
    (hcj : L.cj f = 1 - f) (x : E) (hx : x ∈ L.O) :
    ∃ a : 𝒪[F], x * f = algebraMap F E a * f := by
  have := PI.LocHerm.SlopeTestRemainingChoices.nontrivial_E L
  obtain ⟨a, ha⟩ := PI.LocHerm.SlopeTestRemainingChoices.tr_ex L (x * f)
  have hmem : algebraMap F E a ∈ L.O := by
    rw [ha]
    exact L.O.add_mem (L.O.mul_mem hx hf) (PI.LocHerm.SlopeTestRemainingChoices.cj_mem_O L _ (L.O.mul_mem hx hf))
  refine ⟨⟨a, PI.LocHerm.SlopeTestRemainingChoices.mem_OF_of_mem_O L a hmem⟩, ?_⟩
  show x * f = algebraMap F E a * f
  rw [ha, map_mul, hcj]
  linear_combination (L.cj x - x) * hff

theorem exists_idem [CharZero F] (L : LocE F E) (θ : E) (hc : L.cj θ = -θ) (D : F)
    (hD : θ * θ = algebraMap F E D) (s : F) (hs : s * s = D) (hD0 : D ≠ 0) :
    ∃ e : E, e ∈ L.O ∧ e * e = e ∧ L.cj e = 1 - e := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hD0 (by rw [← hs, mul_zero])
  obtain ⟨c, hc2'⟩ : ∃ c : F, c * 2 = 1 := ⟨2⁻¹, inv_mul_cancel₀ two_ne_zero⟩
  obtain ⟨t, ht'⟩ : ∃ t : F, t * t * D = 1 := ⟨s⁻¹, by
    rw [← hs]; field_simp⟩
  have hc2 : algebraMap F E c * 2 = 1 := by
    rw [← map_ofNat (algebraMap F E) 2, ← map_mul, hc2', map_one]
  have ht : algebraMap F E t * algebraMap F E t * algebraMap F E D = 1 := by
    rw [← map_mul, ← map_mul, ht', map_one]
  refine ⟨algebraMap F E c * (1 + algebraMap F E t * θ), ?_, ?_, ?_⟩
  · refine PI.LocHerm.SlopeTestRemainingChoices.mem_O_of_quad L _ 1 0 ?_
    rw [show ((1 : 𝒪[F]) : F) = 1 from rfl, show ((0 : 𝒪[F]) : F) = 0 from rfl, map_one,
      map_zero]
    linear_combination algebraMap F E c ^ 2 * algebraMap F E t ^ 2 * hD
      + algebraMap F E c ^ 2 * ht + (1 + algebraMap F E t * θ) * algebraMap F E c * hc2
  · linear_combination algebraMap F E c ^ 2 * algebraMap F E t ^ 2 * hD
      + algebraMap F E c ^ 2 * ht + (1 + algebraMap F E t * θ) * algebraMap F E c * hc2
  · rw [map_mul, map_add (f := _), map_one, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hc]
    linear_combination hc2

theorem sqCase : SqCase := by
  intro F _ _ _ E _ _ _ _ M hM θ hθ hc D hD0 hD hs
  obtain ⟨s, hs⟩ := hs
  intro W _ _ P hP
  have := hM.loc
  have := hM.char0
  obtain ⟨e, heO, hee, hcj⟩ := exists_idem M.L θ hc D hD s hs hD0
  let _ : Algebra 𝒪[F] M.L.O :=
    ((algebraMap 𝒪[F] E).codRestrict M.L.O
      (fun a => PI.LocHerm.SlopeTestRemainingChoices.algebraMap_mem_O M.L a)).toAlgebra
  have _ : Module.Finite M.L.O P := Module.Finite.iff_fg.mpr hP
  have h1O : 1 - e ∈ M.L.O := M.L.O.sub_mem M.L.O.one_mem heO
  have hcj' : M.L.cj (1 - e) = 1 - (1 - e) := by
    rw [map_sub, map_one, hcj]
  refine proj_of_two_idem 𝒪[F] (⟨e, heO⟩ : M.L.O) (Subtype.ext hee) ?_ ?_ ?_
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := exists_mul_idem M.L e heO hee hcj x hx
    exact ⟨a, Subtype.ext ha⟩
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := exists_mul_idem M.L (1 - e) h1O (by linear_combination hee) hcj' x hx
    exact ⟨a, Subtype.ext ha⟩
  · intro a q ha h
    have ha' : (a : F) ≠ 0 := fun h0 => ha (Subtype.ext h0)
    have h1 : algebraMap F E (a : F) • (q : W) = 0 := congrArg Subtype.val h
    apply Subtype.ext
    calc (q : W) = algebraMap F E ((a : F)⁻¹ * a) • (q : W) := by
          rw [inv_mul_cancel₀ ha', map_one, one_smul]
      _ = algebraMap F E (a : F)⁻¹ • (algebraMap F E (a : F) • (q : W)) := by
          rw [map_mul, mul_smul]
      _ = 0 := by rw [h1, smul_zero]

end Concrete

end PI.LocHerm.OProj
end
end

