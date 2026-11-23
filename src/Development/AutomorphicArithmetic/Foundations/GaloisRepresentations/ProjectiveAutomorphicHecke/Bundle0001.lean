module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExtEig
section
open Module

universe u v

noncomputable section

namespace UpperTheory.Gal.CertificateRingHomMap

open GlobalTheory.LKDef.HeckeTraceForms

section

variable {Γ H A Z V J : Type} [Group Γ] [Group H] [Group A] [Group Z] [AddCommGroup V] [Module ℂ V]

private theorem rop_add (r : H →₀ ℂ) (Φ Ψ : H → V) : rop r (Φ + Ψ) = rop r Φ + rop r Ψ := by
  funext g
  simp [rop, Finsupp.sum, Finset.sum_add_distrib, smul_add]

private theorem rop_smul (r : H →₀ ℂ) (a : ℂ) (Φ : H → V) : rop r (a • Φ) = a • rop r Φ := by
  funext g
  simp only [rop, Finsupp.sum, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun u _ => smul_comm _ _ _

private def eigForms (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (r : J → H →₀ ℂ) (θ : J → ℂ) :
    Submodule ℂ (H → V) where
  carrier := {Φ | Φ ∈ forms ι K ξ ∧ ∀ j, rop (r j) Φ = θ j • Φ}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨add_mem ha hb, fun j => by rw [rop_add, ha', hb', smul_add]⟩
  zero_mem' := ⟨zero_mem _, fun j => by
    have := rop_smul (r j) (0 : ℂ) (0 : H → V)
    simpa using this⟩
  smul_mem' := by
    rintro a b ⟨hb, hb'⟩
    exact ⟨Submodule.smul_mem _ a hb, fun j => by rw [rop_smul, hb', smul_comm]⟩

end

end UpperTheory.Gal.CertificateRingHomMap

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExtZero
section
open Module
universe u v

namespace UpperTheory.Gal.CertificateRingHomMap

open GlobalTheory.LKDef.HeckeTraceForms

section
variable {Γ H A V : Type} [Group Γ] [Group H] [Group A] [AddCommGroup V] [Module ℂ V]
  {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V} {c : H →* A} {φ : H → V}

private theorem key (hφ : KerForm ι K ξ c φ) {γ γ' : Γ} {u u' k k' : H} (hu : c u = 1) (hu' : c u' = 1)
    (hk : k ∈ K) (hk' : k' ∈ K) (h : ι γ * u * k = ι γ' * u' * k') : ξ γ (φ u) = ξ γ' (φ u') := by
  obtain ⟨h1, h2, h3⟩ := hφ
  set δ := γ'⁻¹ * γ with hδ
  have hκ : k * k'⁻¹ ∈ K := K.mul_mem hk (K.inv_mem hk')
  have hu'eq : u' = ι δ * u * (k * k'⁻¹) := by
    have e1 : ι γ' * u' = ι γ * u * k * k'⁻¹ := by
      rw [h]
      group
    rw [hδ, map_mul, map_inv]
    calc u' = (ι γ')⁻¹ * (ι γ' * u') := by group
      _ = (ι γ')⁻¹ * ι γ * u * (k * k'⁻¹) := by
        rw [e1]
        group
  have hc : c (ι δ) * c (k * k'⁻¹) = 1 := by
    have e2 := congrArg c hu'eq
    rw [map_mul, map_mul, hu, hu', mul_one] at e2
    exact e2.symm
  have hcκ : c (k * k'⁻¹) = 1 := by
    apply h1 δ⁻¹ _ hκ
    rw [map_inv, map_inv, eq_inv_of_mul_eq_one_right hc]
  have hcδ : c (ι δ) = 1 := by
    rw [hcκ, mul_one] at hc
    exact hc
  rw [hu'eq, h3 _ hκ _ hcκ (by rw [map_mul, hcδ, hu, one_mul]), h2 δ u hcδ hu]
  rw [← Module.End.mul_apply, ← map_mul, hδ, mul_inv_cancel_left]

open Classical in
private noncomputable def ext0 (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (c : H →* A) (φ : H → V) (g : H) : V :=
  if h : ∃ x : Γ × H × H, c x.2.1 = 1 ∧ x.2.2 ∈ K ∧ g = ι x.1 * x.2.1 * x.2.2 then
    ξ h.choose.1 (φ h.choose.2.1) else 0

private theorem extension_by_zero_double_coset (hφ : KerForm ι K ξ c φ) {γ : Γ} {u k : H} (hu : c u = 1) (hk : k ∈ K) :
    ext0 ι K ξ c φ (ι γ * u * k) = ξ γ (φ u) := by
  have h : ∃ x : Γ × H × H, c x.2.1 = 1 ∧ x.2.2 ∈ K ∧ ι γ * u * k = ι x.1 * x.2.1 * x.2.2 :=
    ⟨(γ, u, k), hu, hk, rfl⟩
  unfold ext0
  rw [dite_eq_left h]
  obtain ⟨s1, s2, s3⟩ := h.choose_spec
  exact key hφ s1 hu s2 hk s3.symm

private theorem extension_by_zero_outside_support {g : H} (h : ¬ ∃ γ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ * u * k) :
    ext0 ι K ξ c φ g = 0 := by
  unfold ext0
  rw [dite_eq_right]
  rintro ⟨x, hx1, hx2, hx3⟩
  exact h ⟨x.1, x.2.1, x.2.2, hx1, hx2, hx3⟩

end

theorem pExtZero_holds : ExtZero := by
  intro Γ H A V _ _ _ _ _ ι K ξ c φ hφ
  refine ⟨ext0 ι K ξ c φ, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro γ g
    by_cases hg : ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ₀ * u * k
    · obtain ⟨γ₀, u, k, hu, hk, rfl⟩ := hg
      have e : ι γ * (ι γ₀ * u * k) = ι (γ * γ₀) * u * k := by rw [map_mul]; group
      rw [e, extension_by_zero_double_coset hφ hu hk, extension_by_zero_double_coset hφ hu hk, map_mul]; rfl
    · have hg' : ¬ ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ ι γ * g = ι γ₀ * u * k := by
        rintro ⟨γ₀, u, k, hu, hk, e⟩
        refine hg ⟨γ⁻¹ * γ₀, u, k, hu, hk, ?_⟩
        rw [map_mul, map_inv]
        calc g = (ι γ)⁻¹ * (ι γ * g) := by group
          _ = (ι γ)⁻¹ * ι γ₀ * u * k := by rw [e]; group
      rw [extension_by_zero_outside_support hg, extension_by_zero_outside_support hg', map_zero]
  · intro k₁ hk₁ g
    by_cases hg : ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ₀ * u * k
    · obtain ⟨γ₀, u, k, hu, hk, rfl⟩ := hg
      have e : ι γ₀ * u * k * k₁ = ι γ₀ * u * (k * k₁) := by group
      rw [e, extension_by_zero_double_coset hφ hu (K.mul_mem hk hk₁), extension_by_zero_double_coset hφ hu hk]
    · have hg' : ¬ ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g * k₁ = ι γ₀ * u * k := by
        rintro ⟨γ₀, u, k, hu, hk, e⟩
        refine hg ⟨γ₀, u, k * k₁⁻¹, hu, K.mul_mem hk (K.inv_mem hk₁), ?_⟩
        calc g = g * k₁ * k₁⁻¹ := by group
          _ = ι γ₀ * u * (k * k₁⁻¹) := by rw [e]; group
      rw [extension_by_zero_outside_support hg, extension_by_zero_outside_support hg']
  · intro u hu
    have := extension_by_zero_double_coset (γ := 1) hφ hu K.one_mem
    simpa using this
  · intro g hg
    by_contra h
    exact hg (extension_by_zero_outside_support h)

end UpperTheory.Gal.CertificateRingHomMap
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PProjOne
section
open Module
universe u v

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem monoidAlgebra_lift_freeMonoid_eq_wop {F A J : Type*} [Field F] [Ring A] [Algebra F A] (T : J → A)
    (t : MonoidAlgebra F (FreeMonoid J)) :
    MonoidAlgebra.lift F A (FreeMonoid J) (FreeMonoid.lift T) t =
      wop T (t.coeff.equivMapDomain FreeMonoid.toListEquiv) := by
  simp only [MonoidAlgebra.lift_apply, wop, Finsupp.sum_equivMapDomain, FreeMonoid.lift_apply]
  rfl

private theorem algHom_wop_eq_wop_comp {F A B J : Type*} [Field F] [Ring A] [Algebra F A] [Ring B]
    [Algebra F B] (φ : A →ₐ[F] B) (T : J → A) (t : List J →₀ F) :
    φ (wop T t) = wop (fun j => φ (T j)) t := by
  unfold wop
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, map_sum, map_smul, map_list_prod, List.map_map]
  rfl

private theorem exists_idempotent_aeval_nilpotent_sub_of_isIntegral {F D : Type*} [Field F] [CommRing D] [Algebra F D] (x : D)
    (hx : IsIntegral F x) (c : F) :
    ∃ q : Polynomial F, q.eval c = 1 ∧ IsIdempotentElem (Polynomial.aeval x q) ∧
      ∃ N, (x - algebraMap F D c) ^ N * Polynomial.aeval x q = 0 := by
  obtain ⟨r, hm, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly F x)
    (minpoly.ne_zero hx) c
  set k := Polynomial.rootMultiplicity c (minpoly F x)
  have hcop : IsCoprime ((Polynomial.X - Polynomial.C c) ^ (k + 1)) r :=
    ((Polynomial.irreducible_X_sub_C c).coprime_iff_not_dvd.mpr hndvd).pow_left
  obtain ⟨a, b, hab⟩ := hcop
  have h0 : Polynomial.aeval x (minpoly F x) = 0 := minpoly.aeval F x
  refine ⟨b * r, ?_, ?_, k + 1, ?_⟩
  · have := congrArg (Polynomial.eval c) hab
    simpa using this
  · have hid : (b * r) * (b * r) = b * r - a * b * (Polynomial.X - Polynomial.C c) * minpoly F x := by
      rw [hm]
      linear_combination (b * r) * hab
    unfold IsIdempotentElem
    rw [← map_mul, hid]
    simp only [map_sub, map_mul, h0, mul_zero, sub_zero]
  · have hz : (Polynomial.X - Polynomial.C c) ^ (k + 1) * (b * r) =
        b * (Polynomial.X - Polynomial.C c) * minpoly F x := by
      rw [hm]; ring
    have := congrArg (Polynomial.aeval x) hz
    simpa [h0] using this

theorem pProjOne_holds : ProjOne.{u} := by
  intro F _ A _ _ _ J T hT θ
  classical
  let gen : J → F × A := fun j => (θ j, T j)
  let D := Algebra.adjoin F (Set.range gen)
  have hcomm : ∀ a ∈ Set.range gen, ∀ b ∈ Set.range gen, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact Prod.ext (mul_comm _ _) (hT i j)
  have hDcomm : IsMulCommutative D :=
    Algebra.isMulCommutative_adjoin F fun a ha b hb _ => hcomm a ha b hb
  let : CommRing D := { D.toRing with mul_comm := hDcomm.is_comm.comm }
  have : Module.Finite F D := inferInstanceAs (Module.Finite F (Subalgebra.toSubmodule D))
  let χ : D →ₐ[F] F := (AlgHom.fst F F A).comp D.val
  let b := Module.finBasis F D
  choose q hq1 hq2 N hN using fun i => exists_idempotent_aeval_nilpotent_sub_of_isIntegral (b i) (IsIntegral.of_finite F (b i)) (χ (b i))
  let z : D := ∏ i, Polynomial.aeval (b i) (q i)
  have hzid : IsIdempotentElem z := by
    unfold IsIdempotentElem
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hq2 i)
  have hzχ : χ z = 1 := by
    rw [map_prod]
    apply Finset.prod_eq_one
    intro i _
    rw [← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval, hq1]
  have hnil : ∀ d : D, IsNilpotent ((d - algebraMap F D (χ d)) * z) := by
    let L : D →ₗ[F] D := LinearMap.mulRight F z ∘ₗ (LinearMap.id - (Algebra.linearMap F D) ∘ₗ χ.toLinearMap)
    have hL : ∀ d, L d = (d - algebraMap F D (χ d)) * z := fun d => rfl
    let S := ((nilradical D).restrictScalars F).comap L
    have hb : ∀ i, b i ∈ S := by
      intro i
      show L (b i) ∈ nilradical D
      rw [hL]
      have hsplit : z = Polynomial.aeval (b i) (q i) *
          ∏ j ∈ Finset.univ.erase i, Polynomial.aeval (b j) (q j) :=
        (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
      rw [hsplit, ← mul_assoc]
      apply Ideal.mul_mem_right
      rw [mem_nilradical]
      refine ⟨N i + 1, ?_⟩
      rw [mul_pow, (hq2 i).pow_succ_eq, pow_succ', mul_assoc, hN i, mul_zero]
    have hS : S = ⊤ := by
      rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hb i
    intro d
    have hd : d ∈ S := hS ▸ Submodule.mem_top
    rw [← mem_nilradical, ← hL]
    exact hd
  let Ψ := MonoidAlgebra.lift F (F × A) (FreeMonoid J) (FreeMonoid.lift gen)
  have hD : D ≤ Ψ.range := by
    apply Algebra.adjoin_le
    rintro _ ⟨j, rfl⟩
    exact ⟨MonoidAlgebra.of F _ (FreeMonoid.of j), by simp [Ψ]⟩
  obtain ⟨t, ht⟩ := hD z.2
  have ht' : MonoidAlgebra.lift F (F × A) (FreeMonoid J) (FreeMonoid.lift gen) t = z := ht
  let coeff := t.coeff.equivMapDomain FreeMonoid.toListEquiv
  have hwθ : wop θ coeff = (z : F × A).1 := by
    have h1 := algHom_wop_eq_wop_comp (AlgHom.fst F F A) gen coeff
    rw [← monoidAlgebra_lift_freeMonoid_eq_wop, ht'] at h1
    exact h1.symm
  have hwT : wop T coeff = (z : F × A).2 := by
    have h1 := algHom_wop_eq_wop_comp (AlgHom.snd F F A) gen coeff
    rw [← monoidAlgebra_lift_freeMonoid_eq_wop, ht'] at h1
    exact h1.symm
  refine ⟨coeff, ?_, ?_, ?_⟩
  · rw [hwθ]
    exact hzχ
  · rw [hwT]
    unfold IsIdempotentElem
    have h1 := congrArg (fun x : D => (x : F × A).2) hzid
    simpa using h1
  · intro j
    let d : D := ⟨gen j, Algebra.subset_adjoin ⟨j, rfl⟩⟩
    obtain ⟨M, hM⟩ := hnil d
    refine ⟨M + 1, ?_⟩
    have h2 : (d - algebraMap F D (θ j)) ^ (M + 1) * z = 0 := by
      have h3 : ((d - algebraMap F D (χ d)) * z) ^ (M + 1) = 0 := by
        rw [pow_succ, hM, zero_mul]
      rw [mul_pow, hzid.pow_succ_eq] at h3
      exact h3
    have h4 := congrArg ((AlgHom.snd F F A).comp D.val) h2
    rw [hwT]
    simpa [d, gen] using h4

end UpperTheory.Gal.CertificateRingHomMap
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PProjTrace
section
open Module
universe u v

theorem UpperTheory.Gal.CertificateRingHomMap.pProjTrace_holds :
    UpperTheory.Gal.CertificateRingHomMap.ProjTrace.{u} := by
  intro F _ W _ _ _ U p u hp h
  set q : W →ₗ[F] U := LinearMap.codRestrict U p hp.map_mem with hq
  have h1 : u * p = U.subtype ∘ₗ ((LinearMap.restrict u h) ∘ₗ q) := by
    ext x
    simp [q, LinearMap.restrict_apply]
  have h2 : q ∘ₗ U.subtype = LinearMap.id := by
    ext x
    simp [q, hp.map_id x x.2]
  rw [h1, LinearMap.trace_comp_comm', LinearMap.comp_assoc, h2, LinearMap.comp_id]
end

