module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1079
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpehInfMapSubEqSumTwists
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.DefiniteBC.spehInf_map_sub_eq_sum_twists : ∀ (d : ℕ) (m : Multiset ℂ) (F : ℂ),
  ∑ k : Fin d, m.map (fun z => F + (((d : ℂ) - 1) / 2 - (k : ℕ)) - z) = (spehInf d m).map (fun z => F - z) := by
  intro d m F
  have hL : ∀ (f : ℕ → Multiset ℂ) (n : ℕ), ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
    intro f n
    induction n with
    | zero => simp
    | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => m.map (fun z => F + (((d : ℂ) - 1) / 2 - (k : ℕ)) - z)) d]
  unfold spehInf
  rw [hL]
  have hM := map_sum (Multiset.mapAddMonoidHom (fun z : ℂ => F - z))
    (fun k : ℕ => m.map (fun x => x + (((d : ℂ) - 1) / 2 - k))) (Finset.range d)
  simp only [Multiset.mapAddMonoidHom_apply] at hM
  rw [hM]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [Function.comp_apply]
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpehPartIsRun
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalDef.RunPart

open GlobalTheory.DefiniteBC

theorem map_le_spehInf (d k : ℕ) (hk : k < d) (m : Multiset ℂ) :
    m.map (· + (((d : ℂ) - 1) / 2 - k)) ≤ spehInf d m := by
  unfold spehInf
  exact List.le_sum_of_mem (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)

theorem mem_infOfWeight {n : ℕ} (lam : DomWeight n) (x : ℂ) (hx : x ∈ infOfWeight lam) :
    ∃ j < n, x = (wAt lam j : ℂ) + (((n : ℂ) - 1) / 2 - (j : ℕ)) := by
  unfold infOfWeight at hx
  obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
  refine ⟨k, k.2, ?_⟩
  simp [wAt, k.2]

theorem entry_of_run {n t : ℕ} (lam : DomWeight n) (p : ℕ) (hn : n < 2 * t) (hrun : IsRunAt lam p t)
    (d : ℕ) (m : Multiset ℂ) (hle : spehInf d m ≤ infOfWeight lam) (htd : t ≤ d) (z : ℂ) (hz : z ∈ m) :
    d = t ∧ z = (wAt lam p : ℂ) + ((n : ℂ) - 1) / 2 - (p : ℕ) - ((t : ℂ) - 1) / 2 := by
  obtain ⟨hpt, hconst, hleft, hright⟩ := hrun
  have hval : ∀ k < d, ∃ j < n,
      z + (((d : ℂ) - 1) / 2 - k) = (wAt lam j : ℂ) + (((n : ℂ) - 1) / 2 - (j : ℕ)) := fun k hk =>
    mem_infOfWeight lam _ (Multiset.mem_of_le hle
      (Multiset.mem_of_le (map_le_spehInf d k hk m) (Multiset.mem_map_of_mem _ hz)))
  have ht0 : 0 < t := by omega
  obtain ⟨j0, hj0, e0⟩ := hval 0 (by omega)
  set c : ℤ := wAt lam j0 - j0 with hc
  have hvalc : ∀ k < d, ∃ j < n, wAt lam j - (j : ℤ) = c - k := by
    intro k hk
    obtain ⟨j, hj, e⟩ := hval k hk
    refine ⟨j, hj, ?_⟩
    have : ((wAt lam j - (j : ℤ) : ℤ) : ℂ) = ((c - k : ℤ) : ℂ) := by
      rw [hc]; push_cast
      push_cast at e0 e
      linear_combination e0 - e
    exact_mod_cast this
  have hmono : ∀ i j, i ≤ j → j < n → wAt lam j ≤ wAt lam i := by
    intro i j hij hj
    simp only [wAt, hj, dif_pos, show i < n by omega]
    exact lam.anti (Fin.mk_le_mk.2 hij)
  have hB := fun (c' : ℤ) (h : ∀ i < t, ∃ j < n, wAt lam j - j = c' - i) =>
    GlobalTheory.block_is_the_run n p t (wAt lam) c' hmono hpt (by omega) (by omega) hconst hleft hright h
  have hcp : c = wAt lam p - p := hB c fun i hi => hvalc i (by omega)
  have hdt : d = t := by
    by_contra hne
    have := hB (c - 1) fun i hi => by
      obtain ⟨j, hj, e⟩ := hvalc (i + 1) (by omega)
      exact ⟨j, hj, by push_cast at e; linarith⟩
    omega
  refine ⟨hdt, ?_⟩
  have hc' : (c : ℂ) = (wAt lam p : ℂ) - (p : ℕ) := by rw [hcp]; push_cast; ring
  have : (c : ℂ) = (wAt lam j0 : ℂ) - (j0 : ℕ) := by rw [hc]; push_cast; ring
  subst hdt
  push_cast at e0
  linear_combination e0 - this + hc'

end GlobalTheory.GalDef.RunPart


open GlobalTheory.GalDef.RunPart in
theorem GlobalTheory.GalDef.spehPart_is_run : ∀ (n t : ℕ) (lam : DomWeight n) (p : ℕ), n < 2 * t → GlobalTheory.GalDef.IsRunAt lam p t →
  ∀ (c : ℕ) (d : Fin c → ℕ) (M : Fin c → Multiset ℂ), (∀ i, 1 ≤ d i) → (∀ i, M i ≠ 0) →
    ∑ i, spehInf (d i) (M i) = infOfWeight lam →
    ∀ i, t ≤ d i → d i = t ∧
      M i = {(GlobalTheory.GalDef.wAt lam p : ℂ) + ((n : ℂ) - 1) / 2 - (p : ℕ) - ((t : ℂ) - 1) / 2} ∧ ∀ j, j ≠ i → d j < t := by
  intro n t lam p hn hrun c d M hd hM hsum i hti
  have hle : ∀ j, spehInf (d j) (M j) ≤ infOfWeight lam := fun j => by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun j => spehInf (d j) (M j)) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ j)
  obtain ⟨z, hz⟩ := Multiset.exists_mem_of_ne_zero (hM i)
  obtain ⟨hdi, hzv⟩ := entry_of_run lam p hn hrun (d i) (M i) (hle i) hti z hz
  set v : ℂ := (wAt lam p : ℂ) + ((n : ℂ) - 1) / 2 - (p : ℕ) - ((t : ℂ) - 1) / 2 with hv
  have hall : ∀ z' ∈ M i, z' = v := fun z' hz' => (entry_of_run lam p hn hrun (d i) (M i) (hle i) hti z' hz').2
  have hnd : ∀ j, (spehInf (d j) (M j)).Nodup := fun j =>
    Multiset.nodup_of_le (hle j) (nodup_infOfWeight lam)
  refine ⟨hdi, ?_, ?_⟩
  · have hnodup : (M i).Nodup :=
      (Multiset.nodup_of_le (map_le_spehInf (d i) 0 (by omega) (M i)) (hnd i)).of_map _
    rw [Multiset.eq_replicate.2 ⟨rfl, hall⟩] at hnodup ⊢
    have hc1 : Multiset.card (M i) ≤ 1 := by
      by_contra h
      push_neg at h
      obtain ⟨k, hk⟩ : ∃ k, Multiset.card (M i) = k + 2 := ⟨Multiset.card (M i) - 2, by omega⟩
      rw [hk, Multiset.replicate_succ, Multiset.replicate_succ, Multiset.nodup_cons] at hnodup
      exact hnodup.1 (Multiset.mem_cons_self _ _)
    have hc0 : Multiset.card (M i) ≠ 0 := fun h => hM i (Multiset.card_eq_zero.1 h)
    rw [show Multiset.card (M i) = 1 by omega, Multiset.replicate_one]
  · intro j hji
    by_contra hlt
    push_neg at hlt
    obtain ⟨z', hz'⟩ := Multiset.exists_mem_of_ne_zero (hM j)
    obtain ⟨hdj, hz'v⟩ := entry_of_run lam p hn hrun (d j) (M j) (hle j) hlt z' hz'
    have ht0 : 0 < t := by omega
    have hmem : ∀ k, 0 < d k → ∀ w ∈ M k, w + (((d k : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) ∈ spehInf (d k) (M k) :=
      fun k hk w hw => Multiset.mem_of_le (map_le_spehInf (d k) 0 hk (M k)) (Multiset.mem_map_of_mem _ hw)
    have hpair : spehInf (d i) (M i) + spehInf (d j) (M j) ≤ infOfWeight lam := by
      rw [← hsum]
      calc spehInf (d i) (M i) + spehInf (d j) (M j) = ∑ k ∈ {i, j}, spehInf (d k) (M k) :=
            (Finset.sum_pair (f := fun k => spehInf (d k) (M k)) hji.symm).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hdis := (Multiset.nodup_add.1 (Multiset.nodup_of_le hpair (nodup_infOfWeight lam))).2.2
    have h1 := hmem i (by omega) z hz
    have h2 := hmem j (by omega) z' hz'
    rw [hdi, hzv] at h1
    rw [hdj, hz'v] at h2
    rw [hdi, hdj] at hdis
    exact Multiset.disjoint_left.1 hdis h1 h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToQMemMaximalIdealIff
section
set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.GraphLocal

open GlobalTheory.FieldPair

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

def placeAlg (E : Place (algebraMap ℂ K)) : Subalgebra ℂ K :=
  { E.ring.toSubring with algebraMap_mem' := E.const_mem }

theorem mem_placeAlg {E : Place (algebraMap ℂ K)} {e : K} : e ∈ placeAlg E ↔ e ∈ E.ring :=
  Iff.rfl


variable (κ') in
def tensMap (A : Subalgebra ℂ K) : A ⊗[ℂ] κ' →ₐ[ℂ] K ⊗[ℂ] κ' :=
  Algebra.TensorProduct.map A.val (AlgHom.id ℂ κ')

theorem tensMap_injective (A : Subalgebra ℂ K) : Function.Injective (tensMap κ' A) := by
  have e : ⇑(tensMap κ' A) = ⇑(LinearMap.rTensor κ' A.val.toLinearMap) := by
    funext w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  rw [e]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

def tens (A : Subalgebra ℂ K) : Subalgebra ℂ (K ⊗[ℂ] κ') := (tensMap κ' A).range

def tensEquiv (A : Subalgebra ℂ K) : A ⊗[ℂ] κ' ≃ₐ[ℂ] tens (κ' := κ') A :=
  AlgEquiv.ofInjective _ (tensMap_injective A)

@[simp] theorem coe_tensEquiv (A : Subalgebra ℂ K) (w : A ⊗[ℂ] κ') :
    (tensEquiv A w : K ⊗[ℂ] κ') = tensMap κ' A w := rfl

theorem tmul_mem {A : Subalgebra ℂ K} {e : K} (he : e ∈ A) (b : κ') :
    e ⊗ₜ[ℂ] b ∈ tens (κ' := κ') A :=
  ⟨⟨e, he⟩ ⊗ₜ b, rfl⟩

variable {κ : Type} [Field κ] [Algebra ℂ κ]

def graphIdeal (E : Place (algebraMap ℂ K)) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') :
    Ideal (tens (κ' := κ') (placeAlg E)) :=
  Ideal.span ({b | ∃ e : K, 0 < E.ord e ∧ (b : K ⊗[ℂ] κ') = e ⊗ₜ 1} ∪
    {b | ∃ a : R, (b : K ⊗[ℂ] κ') = (a : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π a)})

def gens (E : Place (algebraMap ℂ K)) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ')
    (hR : E.Contains R) (t : E.ring) {k : ℕ} (z : Fin k → R) :
    Fin (k + 1) → tens (κ' := κ') (placeAlg E) :=
  Fin.cons ⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩ fun i =>
    ⟨(z i : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π (z i)),
      sub_mem (tmul_mem (hR _ (z i).2) 1) (tmul_mem (one_mem (placeAlg E)) _)⟩

variable {L : Type} [Field L] [Algebra (K ⊗[ℂ] κ') L]

theorem one_notMem {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [h𝔭 : 𝔭.IsPrime] :
    (1 : tens (κ' := κ') A) ∉ 𝔭 :=
  (Ideal.ne_top_iff_one 𝔭).1 h𝔭.ne_top

def locAt {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime] : Subring L where
  carrier := {x | ∃ a s : tens (κ' := κ') A, s ∉ 𝔭 ∧
    x * algebraMap (K ⊗[ℂ] κ') L s = algebraMap (K ⊗[ℂ] κ') L a}
  mul_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨a', s', hs', hy⟩
    refine ⟨a * a', s * s', fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs hs', ?_⟩
    simp only [Subalgebra.coe_mul, map_mul]
    rw [← hx, ← hy]
    ring
  one_mem' := ⟨1, 1, one_notMem 𝔭, by simp⟩
  add_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨a', s', hs', hy⟩
    refine ⟨a * s' + a' * s, s * s', fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs hs', ?_⟩
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, map_mul, map_add (f := _)]
    rw [← hx, ← hy]
    ring
  zero_mem' := ⟨0, 1, one_notMem 𝔭, by simp⟩
  neg_mem' := by
    rintro x ⟨a, s, hs, hx⟩
    refine ⟨-a, s, hs, ?_⟩
    simp only [Subalgebra.coe_neg, map_neg]
    rw [← hx]
    ring

def toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime] :
    tens (κ' := κ') A →+* locAt (L := L) 𝔭 where
  toFun b := ⟨algebraMap (K ⊗[ℂ] κ') L b, b, 1, one_notMem 𝔭, by simp⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp] theorem coe_toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (b : tens (κ' := κ') A) : (toQ (L := L) 𝔭 b : L) = algebraMap (K ⊗[ℂ] κ') L b := rfl

theorem exists_mul_toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (x : locAt (L := L) 𝔭) : ∃ a s : tens (κ' := κ') A, s ∉ 𝔭 ∧ x * toQ 𝔭 s = toQ 𝔭 a := by
  obtain ⟨x, a, s, hs, hx⟩ := x
  exact ⟨a, s, hs, Subtype.ext hx⟩

section Inj

variable {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
  (hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L))
include hinj

theorem algebraMap_ne_zero {b : tens (κ' := κ') A} (hb : b ≠ 0) :
    algebraMap (K ⊗[ℂ] κ') L b ≠ 0 := fun h =>
  hb (Subtype.ext (hinj (h.trans (map_zero _).symm)))

theorem isUnit_toQ {b : tens (κ' := κ') A} (hb : b ∉ 𝔭) : IsUnit (toQ (L := L) 𝔭 b) := by
  have hb0 : algebraMap (K ⊗[ℂ] κ') L b ≠ 0 :=
    algebraMap_ne_zero hinj fun h => hb (h ▸ 𝔭.zero_mem)
  refine IsUnit.of_mul_eq_one (b := ⟨(algebraMap (K ⊗[ℂ] κ') L b)⁻¹, 1, b, hb, by simp [hb0]⟩)
    (Subtype.ext ?_)
  simp [hb0]

theorem isLocalRing_locAt : IsLocalRing (locAt (L := L) 𝔭) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨a, s, hs, hx⟩ := exists_mul_toQ 𝔭 x
  by_cases ha : a ∈ 𝔭
  · right
    have hsa : s - a ∉ 𝔭 := fun h => hs (by simpa using add_mem h ha)
    refine isUnit_of_mul_isUnit_left (y := toQ 𝔭 s) ?_
    rw [sub_mul, one_mul, hx, ← map_sub]
    exact isUnit_toQ 𝔭 hinj hsa
  · left
    refine isUnit_of_mul_isUnit_left (y := toQ 𝔭 s) ?_
    rw [hx]
    exact isUnit_toQ 𝔭 hinj ha

theorem isUnit_toQ_iff {b : tens (κ' := κ') A} : IsUnit (toQ (L := L) 𝔭 b) ↔ b ∉ 𝔭 := by
  refine ⟨fun h hb => ?_, isUnit_toQ 𝔭 hinj⟩
  obtain ⟨y, hy⟩ := h.exists_right_inv
  obtain ⟨a, s, hs, e⟩ := exists_mul_toQ 𝔭 y
  have e2 : toQ (L := L) 𝔭 (b * a) = toQ 𝔭 s := by
    rw [map_mul, ← e, ← mul_assoc, hy, one_mul]
  have e3 : b * a = s := Subtype.ext (hinj (congrArg Subtype.val e2))
  exact hs (e3 ▸ 𝔭.mul_mem_right a hb)

theorem toQ_mem_maximalIdeal_iff [IsLocalRing (locAt (L := L) 𝔭)] {b : tens (κ' := κ') A} :
    toQ (L := L) 𝔭 b ∈ IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) ↔ b ∈ 𝔭 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_toQ_iff 𝔭 hinj, not_not]

theorem map_le_maximalIdeal [IsLocalRing (locAt (L := L) 𝔭)] :
    𝔭.map (toQ (L := L) 𝔭) ≤ IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) :=
  Ideal.map_le_iff_le_comap.2 fun _ hb => (toQ_mem_maximalIdeal_iff 𝔭 hinj).2 hb

end Inj

end GlobalTheory.GraphLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceFormLinearIsometryEqMulNormOneTorus
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.IsomMulTorus

open GlobalTheory.UnitLemma

theorem trace_inv {K : UQ} (B : InvAlg K) (w : B.A) :
    Algebra.trace K.E B.A (B.σ w) = K.c (Algebra.trace K.E B.A w) := by
  have h := Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) w
  rw [h, RingEquiv.apply_symm_apply]

theorem isom_eq_mul : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (u β : B.A), B.σ β = β * ((-1) ^ n * u) → Algebra.adjoin K.E {u} = ⊤ → (∀ y, (∀ z, B.herm β y z = 0) → y = 0) → ∀ f : B.A →ₗ[K.E] B.A, Function.Surjective f → (∀ y z, B.herm β (f y) (f z) = B.herm β y z) → ∃ a : B.Aˣ, a ∈ B.T ∧ ∀ y, f y = (a : B.A) * y := by
  intro K B n u β hβ hadj hnd f hf hiso

  have hsub : ∀ a b z : B.A, B.herm β (a - b) z = B.herm β a z - B.herm β b z := by
    intro a b z; unfold InvAlg.herm; rw [mul_sub, sub_mul, map_sub]

  have hsym : ∀ y z : B.A, K.c (B.herm β z y) = B.herm β (((-1) ^ n * u) * y) z := by
    intro y z
    unfold InvAlg.herm
    rw [← trace_inv, map_mul B.σ, map_mul B.σ, B.σ_σ, hβ]
    congr 1; ring

  have ht : ∀ y, f (((-1) ^ n * u) * y) = ((-1) ^ n * u) * f y := by
    intro y
    have h0 : ∀ z, B.herm β (((-1) ^ n * u) * f y - f (((-1) ^ n * u) * y)) z = 0 := by
      intro z
      obtain ⟨w, rfl⟩ := hf z
      rw [hsub, ← hsym, hiso, hiso, hsym, sub_self]
    exact (sub_eq_zero.mp (hnd _ h0)).symm

  have hsgn : ((-1 : B.A) ^ n) = algebraMap K.E B.A ((-1) ^ n) := by simp
  have hsq : ((-1 : B.A) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  have hu : ∀ y, f (u * y) = u * f y := by
    intro y
    have e1 : u * y = (-1) ^ n * (((-1) ^ n * u) * y) := by
      rw [← mul_assoc, ← mul_assoc, hsq, one_mul]
    have e2 : u * f y = (-1) ^ n * (((-1) ^ n * u) * f y) := by
      rw [← mul_assoc, ← mul_assoc, hsq, one_mul]
    have hm : ∀ x, f ((-1) ^ n * x) = (-1) ^ n * f x := by
      intro x; rw [hsgn, ← Algebra.smul_def, map_smul, Algebra.smul_def]
    rw [e1, e2, hm, ht]

  let S : Subalgebra K.E B.A :=
    { carrier := {x | ∀ y, f (x * y) = x * f y}
      mul_mem' := by
        intro a b ha hb y
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [mul_assoc, ha, hb, mul_assoc]
      add_mem' := by
        intro a b ha hb y
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [add_mul, map_add (f := _), ha, hb, add_mul]
      algebraMap_mem' := by
        intro e y
        show f (algebraMap K.E B.A e * y) = algebraMap K.E B.A e * f y
        rw [← Algebra.smul_def, ← Algebra.smul_def, map_smul] }
  have hS : ∀ x, ∀ y, f (x * y) = x * f y := by
    intro x
    have h1 : Algebra.adjoin K.E {u} ≤ S := Algebra.adjoin_le (by
      intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact hu)
    rw [hadj] at h1
    exact h1 (Algebra.mem_top : x ∈ (⊤ : Subalgebra K.E B.A))
  have hf1 : ∀ y, f y = y * f 1 := by
    intro y; rw [← hS y 1, mul_one]
  obtain ⟨z, hz⟩ := hf 1
  have hz1 : f 1 * z = 1 := by rw [mul_comm, ← hf1, hz]
  let a : B.Aˣ := ⟨f 1, z, hz1, by rw [mul_comm]; exact hz1⟩
  refine ⟨a, ?_, fun y => by rw [hf1 y, mul_comm]⟩
  show (f 1) * B.σ (f 1) = 1
  have h0 : ∀ w, B.herm β (f 1 * B.σ (f 1) - 1) w = 0 := by
    intro w
    have e : B.herm β (f 1 * B.σ (f 1)) w = B.herm β (f 1) (f w) := by
      rw [hf1 w]; unfold InvAlg.herm; rw [map_mul B.σ]; congr 1; ring
    rw [hsub, e, hiso, sub_self]
  exact sub_eq_zero.mp (hnd _ h0)

end GlobalTheory.IsomMulTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffComplexEqZeroOfCutoffZero
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem mixTop_position_zero {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ : EndValuedForm11Coeffs n r) (j : Fin n) :
    mixTop (intersection_update_fsHerm_neg_one K₁ 0 K₀ j) = 0 := by
  unfold mixTop
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun π _ =>
    Finset.sum_eq_zero fun u _ => mul_eq_zero_of_right _ ?_)
  refine Matrix.det_eq_zero_of_row_eq_zero j fun b => ?_
  simp [intersection_update_fsHerm_neg_one]

theorem cutForm_eq_zero {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ}
    (G₀ G₁ : V n → Matrix r r ℂ) {v : V n} (hρ : ρ =ᶠ[𝓝 v] (fun _ => 0)) :
    cutForm ρ G₀ G₁ v = 0 := by
  have h : dbar (fun x => (ρ x : ℂ)) v = dbar (fun _ : V n => (0 : ℂ)) v :=
    dbar_congr (hρ.mono fun x hx => by simp [hx])
  funext a b
  simp [cutForm, h]

theorem corrC_eq_zero_of_eventuallyEq_zero {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ}
    (G₀ G₁ : V n → Matrix r r ℂ) {v : V n} (hρ : ρ =ᶠ[𝓝 v] (fun _ => 0)) : corrC ρ G₀ G₁ v = 0 := by
  unfold corrC
  rw [cutForm_eq_zero G₀ G₁ hρ]
  exact Finset.sum_eq_zero fun j _ => mixTop_position_zero _ _ j

end GlobalTheory.GoodTop
end

