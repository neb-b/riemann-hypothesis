module

public import Mathlib
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0851
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.IwInvT
section
noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.IwahoriUnit
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

variable {G : Type} [Group G]

private def cfun (K : Subgroup G) : Submodule ℂ (G → ℂ) where
  carrier := {f | (∀ g, ∀ b ∈ K, f (g * b) = f g) ∧ ∃ S : Finset G, ∀ g, f g ≠ 0 → ∃ s ∈ S, ∃ b ∈ K, g = s * b}
  zero_mem' := ⟨fun _ _ _ => rfl, ∅, fun _ h => (h rfl).elim⟩
  add_mem' := by
    rintro f f' ⟨hf, S, hS⟩ ⟨hf', S', hS'⟩
    refine ⟨fun g b hb => by simp [hf g b hb, hf' g b hb], S ∪ S', fun g hg => ?_⟩
    by_cases h : f g = 0
    · obtain ⟨s, hs, e⟩ := hS' g (by simpa [h] using hg)
      exact ⟨s, Finset.mem_union_right _ hs, e⟩
    · obtain ⟨s, hs, e⟩ := hS g h
      exact ⟨s, Finset.mem_union_left _ hs, e⟩
  smul_mem' := by
    rintro c f ⟨hf, S, hS⟩
    exact ⟨fun g b hb => by simp [hf g b hb], S, fun g hg => hS g fun h => hg (by simp [h])⟩

private def lrep (K : Subgroup G) : Representation ℂ G (cfun K) where
  toFun x :=
    { toFun := fun f => ⟨fun g => f.1 (x⁻¹ * g), fun g b hb => (congrArg f.1 (mul_assoc _ _ _).symm).trans (f.2.1 _ b hb), by
        obtain ⟨S, hS⟩ := f.2.2
        refine ⟨S.image (x * ·), fun g hg => ?_⟩
        obtain ⟨s, hs, b, hb, e⟩ := hS _ hg
        exact ⟨x * s, Finset.mem_image_of_mem _ hs, b, hb, by rw [mul_assoc, ← e, mul_inv_cancel_left]⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := LinearMap.ext fun f => Subtype.ext (funext fun g => by simp)
  map_mul' x y := LinearMap.ext fun f => Subtype.ext (funext fun g => by simp [mul_assoc])

private theorem exists_conv_inv (K : Subgroup G) (hK : IsCommensurated K) (t : G) (hfin : ∀ x, (cosets K x).Finite)
    (T : fixed (lrep K) K ≃ₗ[ℂ] fixed (lrep K) K) (hT : ∀ v, (T v : cfun K) = ∑ᶠ q ∈ cosets K t, lrep K q.out v) :
    ∃ φ ∈ Hecke ℂ K, conv K φ (dosetInd ℂ K t) = dosetInd ℂ K 1 := by
  have toH : ∀ v : fixed (lrep K) K, v.1.1 ∈ Hecke ℂ K := fun v => by
    refine ⟨fun a b g => ?_, ?_⟩
    · have h := congrFun (congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 v.2 a⁻¹ (inv_mem a.2))) g
      rw [v.1.2.1 _ b b.2]
      simpa [lrep] using h
    · obtain ⟨S, hS⟩ := v.1.2.2
      refine ⟨S, fun g hg => ?_⟩
      obtain ⟨s, hs, b, hb, e⟩ := hS g hg
      exact ⟨s, hs, 1, ⟨b, hb⟩, by simpa using e⟩
  have ofH : ∀ f ∈ Hecke ℂ K, ∃ v : fixed (lrep K) K, v.1.1 = f := fun f hf => by
    obtain ⟨h1, S, hS⟩ := hf
    refine ⟨⟨⟨f, fun g b hb => by simpa using h1 1 ⟨b, hb⟩ g, S.biUnion fun s => (hfin s).toFinset.image Quotient.out, fun g hg => ?_⟩,
      GlobalTheory.LGrp.mem_fixed.2 fun a ha => Subtype.ext (funext fun g => ?_)⟩, rfl⟩
    · obtain ⟨s, hs, a, b, e⟩ := hS g hg
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
      refine ⟨(g : G ⧸ K).out, Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image_of_mem _ ((hfin s).mem_toFinset.2
        ⟨g, DoubleCoset.mem_doubleCoset.2 ⟨a, a.2, b, b.2, e⟩, rfl⟩)⟩, k⁻¹, inv_mem k.2, by rw [hk]; simp⟩
    · simpa [lrep] using h1 ⟨a⁻¹, inv_mem ha⟩ 1 g
  have hTc : ∀ v, (T v).1.1 = conv K (dosetInd ℂ K t) v.1.1 := fun v => by
    funext g
    rw [hT, finsum_mem_eq_finite_toFinset_sum _ (hfin t), Submodule.coe_sum, Finset.sum_apply, conv,
      finsum_eq_sum_of_support_subset (s := (hfin t).toFinset)]
    · refine Finset.sum_congr rfl fun q hq => ?_
      obtain ⟨y, hy, rfl⟩ := (hfin t).mem_toFinset.1 hq
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K y
      obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 hy
      have : (y : G ⧸ K).out ∈ DoubleCoset.doubleCoset t (K : Set G) K :=
        DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b * k, mul_mem hb k.2, by rw [hk, e, mul_assoc]⟩
      rw [dosetInd, Set.indicator_of_mem this, Pi.one_apply, one_mul]
      rfl
    · intro q hq
      have h : dosetInd ℂ K t q.out ≠ 0 := left_ne_zero_of_mul hq
      exact Finset.mem_coe.2 ((hfin t).mem_toFinset.2 ⟨q.out, Set.mem_of_indicator_ne_zero h, q.out_eq'⟩)
  have ht := Final.DosetIndMem G K ℂ t
  have h1 := Final.DosetIndMem G K ℂ 1
  obtain ⟨e, he⟩ := ofH _ h1
  have hφ := toH (T.symm e)
  have h2 : conv K (dosetInd ℂ K t) (T.symm e).1.1 = dosetInd ℂ K 1 := by rw [← hTc, T.apply_symm_apply, he]
  refine ⟨_, hφ, ?_⟩
  obtain ⟨u, hu⟩ := ofH _ (Final.HeckeConvMem G K ℂ hK _ hφ _ ht)
  rw [← hu, ← he]
  congr 2
  apply T.injective
  refine Subtype.ext (Subtype.ext ?_)
  rw [hTc, hTc, hu, he, ← Final.HeckeAssoc G K ℂ hK _ ht _ hφ _ ht, h2,
    (Final.HeckeUnit G K ℂ _ ht).1, (Final.HeckeUnit G K ℂ _ ht).2]

private theorem comm_of_fin (K : Subgroup G) (hfin : ∀ x, (cosets K x).Finite) : IsCommensurated K := by
  intro g
  have h := hfin g
  rw [cosets_eq_orbit] at h
  have e : (K.map (MulAut.conj g).toMonoidHom).subgroupOf K = MulAction.stabilizer K (g : G ⧸ K) := by
    ext k
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.mem_map_equiv]
    show _ ↔ ((k.1 * g : G) : G ⧸ K) = g
    rw [eq_comm, QuotientGroup.eq]
    simp [mul_assoc]
  rw [Subgroup.relIndex, e, MulAction.index_stabilizer]
  exact ((Set.ncard_pos h).2 ⟨_, MulAction.mem_orbit_self _⟩).ne'


open ValuativeRel GlobalTheory.SmGL GlobalTheory.GLDoubling in
theorem iwInvT (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ)
    (hϖ : valuation k (ϖ : k) = uniformizer k) (ν : Fin n → ℤ) (hν : Antitone ν) :
    ∃ φ ∈ Hecke ℂ (iwahori k (Fin n)), conv (iwahori k (Fin n)) φ (dosetInd ℂ (iwahori k (Fin n)) (torusElt k (Fin n) ϖ ν)) =
      dosetInd ℂ (iwahori k (Fin n)) 1 := by
  obtain ⟨-, T, hT, -⟩ := exists_equiv_doubleCoset k n ϖ hϖ ν hν ℂ _ (lrep (iwahori k (Fin n)))
  exact exists_conv_inv _ (comm_of_fin _ finite_cosets) _ finite_cosets T hT

end UpperTheory.Gal.CertificateRingHomMap
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PTracePow
section
open Module
universe u v

theorem UpperTheory.Gal.CertificateRingHomMap.pTracePow_holds :
    UpperTheory.Gal.CertificateRingHomMap.TracePow.{u} := by
  intro F _ _ W _ _ _ q s hq hq0 hqs hinj j₀
  by_contra hcon
  push_neg at hcon
  have hU : ∀ x ∈ LinearMap.range q, s x ∈ LinearMap.range q := by
    rintro _ ⟨y, rfl⟩
    refine ⟨s y, ?_⟩
    have := LinearMap.congr_fun hqs.eq y
    simpa [Module.End.mul_apply] using this
  have hUp : ∀ j : ℕ, ∀ x ∈ LinearMap.range q, (s ^ j) x ∈ LinearMap.range q := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply]
      exact hU _ (ih x hx)
  set t : Module.End F (LinearMap.range q) := s.restrict hU with ht
  have hres : ∀ j : ℕ, (s ^ j).restrict (hUp j) = t ^ j := by
    intro j
    induction j with
    | zero => ext x; simp
    | succ n ih =>
      ext x
      rw [pow_succ' t, Module.End.mul_apply, ← ih]
      simp [LinearMap.restrict_apply, pow_succ', Module.End.mul_apply, ht]
  have hproj : LinearMap.IsProj (LinearMap.range q) q := by
    refine ⟨fun x => ⟨x, rfl⟩, ?_⟩
    rintro _ ⟨y, rfl⟩
    have := LinearMap.congr_fun hq.eq y
    simpa [Module.End.mul_apply] using this
  set a : ℕ → F := fun j => LinearMap.trace F (LinearMap.range q) (t ^ j) with ha
  have htr : ∀ j, LinearMap.trace F W (q * s ^ j) = a j := by
    intro j
    rw [LinearMap.trace_mul_comm, pProjTrace_holds F W _ q (s ^ j) hproj (hUp j), hres j]
  have hzero : ∀ j, j₀ ≤ j → a j = 0 := fun j hj => by rw [← htr j]; exact hcon j hj
  have htinj : Function.Injective t := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, y, rfl⟩ hx
    have h1 : s (q y) = 0 := by
      have := congrArg Subtype.val hx
      simpa [ht, LinearMap.restrict_apply] using this
    exact Subtype.ext (by simpa using hinj y h1)
  set P := minpoly F t with hP
  have hc0 : P.coeff 0 ≠ 0 := LinearMap.minpoly_coeff_zero_of_injective htinj
  have hrec : ∀ j, ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * a (k + j) = 0 := by
    intro j
    have h0 : Polynomial.aeval t P = 0 := minpoly.aeval F t
    rw [Polynomial.aeval_eq_sum_range] at h0
    have h1 := congrArg (fun f => LinearMap.trace F (LinearMap.range q) (f * t ^ j)) h0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_mul, map_sum, zero_mul, map_zero, smul_mul_assoc, map_smul,
      ← pow_add, smul_eq_mul] at h1
    simpa [ha] using h1
  have hall : ∀ n j, j₀ ≤ j + n → a j = 0 := by
    intro n
    induction n with
    | zero => intro j hj; exact hzero j (by simpa using hj)
    | succ n ih =>
      intro j hj
      have h := hrec j
      rw [Finset.sum_range_succ'] at h
      have hs : ∑ k ∈ Finset.range P.natDegree, P.coeff (k + 1) * a (k + 1 + j) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [ih (k + 1 + j) (by omega), mul_zero]
      rw [hs, zero_add, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left hc0
  have ha0 : a 0 = 0 := hall j₀ 0 (by omega)
  have hne : LinearMap.range q ≠ ⊥ := fun h => hq0 (LinearMap.range_eq_bot.mp h)
  have hpos : Module.finrank F (LinearMap.range q) ≠ 0 :=
    fun h => hne (Submodule.finrank_eq_zero.mp h)
  simp only [ha, pow_zero, LinearMap.trace_one] at ha0
  exact (Nat.cast_ne_zero.mpr hpos) ha0
end

