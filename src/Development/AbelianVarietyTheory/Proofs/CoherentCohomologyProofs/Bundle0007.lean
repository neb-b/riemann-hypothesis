module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemSaturatedOrderIsoSubspaceSpanSymmApply
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
section
open Module

namespace GlobalTheory

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_isCompl_of_projective_quotient (N : Submodule R M) [Module.Projective R (M ⧸ N)] :
    ∃ N' : Submodule R M, IsCompl N N' := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hs' (y : M ⧸ N) : N.mkQ (s y) = y := LinearMap.congr_fun hs y
  refine ⟨LinearMap.range s, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro _ hx ⟨y, rfl⟩
    have hy : y = 0 := by
      rw [← hs' y, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    rw [hy, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.2 ⟨x - s (N.mkQ x), ?_, s (N.mkQ x), ⟨_, rfl⟩, sub_add_cancel _ _⟩
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hs', sub_self]

theorem finite_of_isCompl [Module.Finite R M] {N N' : Submodule R M} (h : IsCompl N N') :
    Module.Finite R N :=
  Module.Finite.equiv (Submodule.quotientEquivOfIsCompl N' N h.symm)

end General

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {M : Type*} [AddCommGroup M] [Module R M]


end Dedekind

section PID

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {M : Type*} [AddCommGroup M] [Module R M]

end PID

section Valuation

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  {M : Type*} [AddCommGroup M] [Module R M]


variable (R M) in
theorem free_of_finite_of_isTorsionFree_of_valuationRing [Module.Finite R M]
    [Module.IsTorsionFree R M] : Module.Free R M :=
  haveI : Module.Flat R M := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 ‹_›)
  Module.free_of_flat_of_isLocalRing

theorem IsSaturatedSubmodule.free_quotient_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Free R (M ⧸ N) :=
  haveI := h.isTorsionFree_quotient
  free_of_finite_of_isTorsionFree_of_valuationRing (R := R) (M := M ⧸ N)

theorem IsSaturatedSubmodule.exists_isCompl_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : ∃ N' : Submodule R M, IsCompl N N' :=
  haveI := h.free_quotient_of_valuationRing
  exists_isCompl_of_projective_quotient N

theorem IsSaturatedSubmodule.finite_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Finite R N :=
  let ⟨_, h'⟩ := h.exists_isCompl_of_valuationRing
  finite_of_isCompl h'

theorem IsSaturatedSubmodule.free_of_valuationRing [Module.Finite R M] [Module.IsTorsionFree R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Free R N :=
  haveI := h.finite_of_valuationRing
  free_of_finite_of_isTorsionFree_of_valuationRing (R := R) (M := N)

end Valuation

universe u

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableIffOfLeOfLe
section
namespace GlobalTheory

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

section Chain

theorem relLength_eq_add_of_le {A B C : Submodule R V} (hCB : C ≤ B) (hBA : B ≤ A) :
    relLength A C = relLength A B + relLength B C := by
  have hle : C.submoduleOf A ≤ B.submoduleOf A := Submodule.comap_mono hCB
  have hex := Module.length_eq_add_of_exact (LinearMap.ker (Submodule.factor hle)).subtype
    (Submodule.factor hle) (Submodule.injective_subtype _) (Submodule.factor_surjective hle)
    (LinearMap.exact_subtype_ker_map _)
  have hker : LinearMap.ker (Submodule.factor hle) =
      (B.submoduleOf A).map (C.submoduleOf A).mkQ := by
    rw [Submodule.factor, Submodule.ker_mapQ, Submodule.comap_id]
  rw [hker, ← relLength_eq_length_map_mkQ, relLength_submoduleOf hBA] at hex
  rw [add_comm]
  exact hex

theorem relLength_inf_eq_add (A B C : Submodule R V) :
    relLength A (B ⊓ C) = relLength A B + relLength (A ⊓ B) C := by
  have h := relLength_eq_add_of_le (A := A) (B := A ⊓ B) (C := A ⊓ B ⊓ C) inf_le_left inf_le_left
  rwa [relLength_inf_right, relLength_inf_right, inf_assoc, relLength_inf_right] at h

theorem relLength_le_add (A B C : Submodule R V) :
    relLength A C ≤ relLength A B + relLength B C :=
  calc relLength A C ≤ relLength A (B ⊓ C) := relLength_anti_right A inf_le_right
    _ = relLength A B + relLength (A ⊓ B) C := relLength_inf_eq_add A B C
    _ ≤ relLength A B + relLength B C := by
      gcongr
      exact inf_le_right

theorem relLength_inf_le_add (A B C : Submodule R V) :
    relLength A (B ⊓ C) ≤ relLength A B + relLength A C := by
  rw [relLength_inf_eq_add]
  gcongr
  exact inf_le_left

theorem relLength_ne_top_trans {A B C : Submodule R V} (hAB : relLength A B ≠ ⊤)
    (hBC : relLength B C ≠ ⊤) : relLength A C ≠ ⊤ :=
  ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hAB, hBC⟩) (relLength_le_add A B C)

theorem relLength_inf_ne_top_iff {A B C : Submodule R V} :
    relLength A (B ⊓ C) ≠ ⊤ ↔ relLength A B ≠ ⊤ ∧ relLength A C ≠ ⊤ :=
  ⟨fun h => ⟨ne_top_of_le_ne_top h (relLength_anti_right A inf_le_left),
      ne_top_of_le_ne_top h (relLength_anti_right A inf_le_right)⟩,
    fun h => ne_top_of_le_ne_top (WithTop.add_ne_top.mpr h) (relLength_inf_le_add A B C)⟩

end Chain

section Commensurable

variable {A A' B B' C : Submodule R V}

@[trans] theorem LengthCommensurable.trans (hAB : LengthCommensurable A B)
    (hBC : LengthCommensurable B C) : LengthCommensurable A C :=
  ⟨relLength_ne_top_trans hAB.1 hBC.1, relLength_ne_top_trans hBC.2 hAB.2⟩

theorem lengthCommensurable_iff_of_le_of_le (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable A C ↔ LengthCommensurable A B ∧ LengthCommensurable B C := by
  rw [lengthCommensurable_iff_of_ge hCB, lengthCommensurable_iff_of_ge hBA,
    lengthCommensurable_iff_of_ge (hCB.trans hBA), relLength_eq_add_of_le hCB hBA]
  exact WithTop.add_ne_top

namespace LengthCommensurable

theorem of_between_left (h : LengthCommensurable A C) (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable A B :=
  ((lengthCommensurable_iff_of_le_of_le hCB hBA).mp h).1

theorem of_between_right (h : LengthCommensurable A C) (hCB : C ≤ B) (hBA : B ≤ A) :
    LengthCommensurable B C :=
  ((lengthCommensurable_iff_of_le_of_le hCB hBA).mp h).2

theorem inf_right (hAB : LengthCommensurable A B) (hAC : LengthCommensurable A C) :
    LengthCommensurable A (B ⊓ C) :=
  ⟨relLength_inf_ne_top_iff.mpr ⟨hAB.1, hAC.1⟩,
    ne_top_of_le_ne_top hAB.2 (relLength_mono_left inf_le_left A)⟩

theorem toNat_relLength_eq_add_of_le (h : LengthCommensurable A C) (hCB : C ≤ B) (hBA : B ≤ A) :
    (relLength A C).toNat = (relLength A B).toNat + (relLength B C).toNat := by
  rw [relLength_eq_add_of_le hCB hBA,
    ENat.toNat_add (h.of_between_left hCB hBA).1 (h.of_between_right hCB hBA).1]

theorem signedLength_eq_toNat_sub_of_le {D : Submodule R V} (h : LengthCommensurable A B)
    (hAD : LengthCommensurable A D) (hDA : D ≤ A) (hDB : D ≤ B) :
    signedLength A B = ((relLength A D).toNat : ℤ) - ((relLength B D).toNat : ℤ) := by
  have hBD : LengthCommensurable B D := h.symm.trans hAD
  have h₁ := hAD.toNat_relLength_eq_add_of_le (B := A ⊓ B) (le_inf hDA hDB) inf_le_left
  have h₂ := hBD.toNat_relLength_eq_add_of_le (B := A ⊓ B) (le_inf hDA hDB) inf_le_right
  rw [relLength_inf_right] at h₁
  rw [relLength_inf_right'] at h₂
  rw [h₁, h₂, signedLength]
  push_cast
  ring

theorem signedLength_eq_add (hAB : LengthCommensurable A B) (hBC : LengthCommensurable B C) :
    signedLength A C = signedLength A B + signedLength B C := by
  have hAC := hAB.trans hBC
  have hAD : LengthCommensurable A (A ⊓ B ⊓ C) := ((refl A).inf_right hAB).inf_right hAC
  have hA : A ⊓ B ⊓ C ≤ A := inf_le_left.trans inf_le_left
  have hB : A ⊓ B ⊓ C ≤ B := inf_le_left.trans inf_le_right
  have hC : A ⊓ B ⊓ C ≤ C := inf_le_right
  rw [hAB.signedLength_eq_toNat_sub_of_le hAD hA hB, hAC.signedLength_eq_toNat_sub_of_le hAD hA hC,
    hBC.signedLength_eq_toNat_sub_of_le (hAB.symm.trans hAD) hB hC]
  ring

end LengthCommensurable

end Commensurable

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthLocalizedModuleEqZeroOfNotAnnihilatorLe
section
open IsDedekindDomain Function

namespace GlobalTheory

section General

variable {R : Type*} [CommRing R]

theorem isFiniteLength_of_isTorsion [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {X : Type*} [AddCommGroup X] [Module R X] [Module.Finite R X] (hX : Module.IsTorsion R X) :
    IsFiniteLength R X := by
  obtain ⟨r, hr, hr0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hX
  have hr' : Module.IsTorsionBySet R X (Ideal.span {r}) := by
    rw [Module.isTorsionBySet_span_singleton_iff]
    exact fun x ↦ Submodule.mem_annihilator.mp hr x trivial
  letI := hr'.module
  haveI : Module.Finite (R ⧸ Ideal.span {r}) X := Module.Finite.of_restrictScalars_finite R _ _
  haveI : IsArtinian R (R ⧸ Ideal.span {r}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (isFiniteLength_quotient_span_singleton R hr0)).2
  haveI : IsArtinianRing (R ⧸ Ideal.span {r}) := isArtinian_of_tower R inferInstance
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance,
    isArtinian_of_surjective_algebraMap (R := R ⧸ Ideal.span {r}) Ideal.Quotient.mk_surjective⟩

section Submodules

variable (T : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization T S]

variable {V : Type*} [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

end Submodules

end General

section Dedekind

variable {O : Type*} [CommRing O] [IsDedekindDomain O]

section Torsion

variable {X : Type*} [AddCommGroup X] [Module O X] [Module.Finite O X]

variable [Ring.HasFiniteQuotients O]

variable [Module.Free ℤ O]

end Torsion

section Lattices

variable [Ring.HasFiniteQuotients O] [Module.Free ℤ O]

end Lattices

end Dedekind

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotientMaximalIdealPowSmulTop
section
open Pointwise

namespace GlobalTheory

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem nonempty_quotient_smul_top_equiv_pi {ι : Type*} [Finite ι] (b : Module.Basis ι R M)
    (a : R) :
    Nonempty ((M ⧸ (a • ⊤ : Submodule R M)) ≃ₗ[R] (ι → R ⧸ Ideal.span {a})) := by
  let g : M →ₗ[R] (ι → R ⧸ Ideal.span {a}) :=
    LinearMap.pi fun i => (Ideal.span {a} : Ideal R).mkQ ∘ₗ b.coord i
  have hg : ∀ x i, g x i = Ideal.Quotient.mk (Ideal.span {a}) (b.repr x i) := fun _ _ => rfl
  have hs : Function.Surjective g := by
    intro y
    choose c hc using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨b.equivFun.symm c, funext fun i => ?_⟩
    rw [hg, ← hc i, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hk : (a • ⊤ : Submodule R M) = LinearMap.ker g := by
    ext x
    rw [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_ker, funext_iff]
    simp only [hg, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, -, rfl⟩ i
      exact ⟨b.repr y i, by simp [mul_comm]⟩
    · intro h
      choose c hc using h
      refine ⟨b.equivFun.symm c, trivial, b.equivFun.injective (funext fun i => ?_)⟩
      rw [map_smul, LinearEquiv.apply_symm_apply, b.equivFun_apply, ← hc i, Pi.smul_apply,
        smul_eq_mul, mul_comm]
  exact ⟨Submodule.quotEquivOfEq _ _ hk ≪≫ₗ g.quotKerEquivOfSurjective hs⟩

theorem length_quotient_smul_top_of_free [Nontrivial R] [Module.Free R M] [Module.Finite R M]
    (a : R) :
    Module.length R (M ⧸ (a • ⊤ : Submodule R M)) =
      Module.length R (R ⧸ Ideal.span {a}) * (Module.finrank R M : ℕ∞) := by
  rw [(nonempty_quotient_smul_top_equiv_pi (Module.finBasis R M) a).some.length_eq,
    Module.length_pi, mul_comm]
  simp

theorem submoduleOf_smul_self (A : Submodule R M) (a : R) :
    (a • A).submoduleOf A = (a • ⊤ : Submodule R A) := by
  ext x
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, trivial, Subtype.ext h⟩
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, y.2, rfl⟩

theorem relLength_smul_self_eq_length (A : Submodule R M) (a : R) :
    relLength A (a • A) = Module.length R (A ⧸ (a • ⊤ : Submodule R A)) := by
  rw [relLength_def, submoduleOf_smul_self]

end General

section DVR

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem length_quotient_span_singleton_dvr (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = addVal R a :=
  Ring.ord_eq_addVal a

theorem addVal_irreducible_pow {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) :
    addVal R (ϖ ^ e) = e := by
  rw [addVal_pow, addVal_uniformizer hϖ, nsmul_one]

section Free

variable (M : Type*) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

theorem length_quotient_smul_top_dvr (a : R) :
    Module.length R (M ⧸ (a • ⊤ : Submodule R M)) = addVal R a * (Module.finrank R M : ℕ∞) := by
  rw [length_quotient_smul_top_of_free, length_quotient_span_singleton_dvr]

end Free

variable {V : Type*} [AddCommGroup V] [Module R V] [Module.IsTorsionFree R V]
  {A : Submodule R V}

theorem relLength_smul_self (hA : A.FG) (a : R) :
    relLength A (a • A) = addVal R a * (Module.finrank R A : ℕ∞) := by
  have : Module.Finite R A := Module.Finite.iff_fg.mpr hA
  rw [relLength_smul_self_eq_length, length_quotient_smul_top_dvr]

theorem relLength_smul_self_of_addVal_eq (hA : A.FG) {a : R} {n : ℕ} (hn : addVal R a = n) :
    relLength A (a • A) = ((n * Module.finrank R A : ℕ) : ℕ∞) := by
  rw [relLength_smul_self hA, hn, Nat.cast_mul]

theorem relLength_irreducible_pow_smul_self (hA : A.FG) {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) :
    relLength A (ϖ ^ e • A) = ((e * Module.finrank R A : ℕ) : ℕ∞) :=
  relLength_smul_self_of_addVal_eq hA (addVal_irreducible_pow hϖ e)

theorem relLength_smul_self_ne_top (hA : A.FG) {a : R} (ha : a ≠ 0) :
    relLength A (a • A) ≠ ⊤ := by
  rw [relLength_smul_self hA]
  exact WithTop.mul_ne_top (addVal_eq_top_iff.not.mpr ha) (ENat.coe_ne_top _)

theorem lengthCommensurable_smul_self (hA : A.FG) {a : R} (ha : a ≠ 0) :
    LengthCommensurable A (a • A) :=
  (lengthCommensurable_iff_of_ge (Submodule.smul_le_self_of_tower a A)).mpr
    (relLength_smul_self_ne_top hA ha)

theorem signedLength_smul_self_of_addVal_eq (hA : A.FG) {a : R} {n : ℕ} (hn : addVal R a = n) :
    signedLength A (a • A) = (n : ℤ) * (Module.finrank R A : ℤ) := by
  have ha : a ≠ 0 := addVal_eq_top_iff.not.mp (hn ▸ ENat.coe_ne_top n)
  rw [← Nat.cast_mul, (lengthCommensurable_smul_self hA ha).signedLength_eq_natCast_iff_of_ge
    (Submodule.smul_le_self_of_tower a A), relLength_smul_self_of_addVal_eq hA hn]

theorem signedLength_smul_self (hA : A.FG) {a : R} (ha : a ≠ 0) :
    signedLength A (a • A) = ((addVal R a).toNat : ℤ) * (Module.finrank R A : ℤ) :=
  signedLength_smul_self_of_addVal_eq hA (ENat.coe_toNat (addVal_eq_top_iff.not.mpr ha)).symm

end DVR

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelLengthSpanEqAddValDet
section
namespace GlobalTheory.RelativeLengthSpanDet

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] in
theorem addVal_prod (s : Finset ι) (c : ι → R) :
    addVal R (∏ i ∈ s, c i) = ∑ i ∈ s, addVal R (c i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, addVal_mul, ih]

theorem length_self_eq_top : Module.length R R = ⊤ := by
  by_contra h
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at h
  have : IsArtinianRing R := h.2
  exact IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)

theorem length_coker_of_det_eq_zero (P : Matrix ι ι R) (h : P.det = 0) :
    Module.length R ((ι → R) ⧸ LinearMap.range P.mulVecLin) = ⊤ := by
  obtain ⟨w, hw, hwP⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
  have hk' : w k ≠ 0 := hk
  let g : R →ₗ[R] (ι → R) ⧸ LinearMap.range P.mulVecLin :=
    (LinearMap.range P.mulVecLin).mkQ ∘ₗ LinearMap.single R (fun _ : ι => R) k
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    have hr' : (Pi.single k r : ι → R) ∈ LinearMap.range P.mulVecLin :=
      (Submodule.Quotient.mk_eq_zero _).mp hr
    obtain ⟨x, hx⟩ := hr'
    have h1 : w ⬝ᵥ P.mulVec x = 0 := by
      rw [Matrix.dotProduct_mulVec, hwP, zero_dotProduct]
    rw [Matrix.mulVecLin_apply] at hx
    rw [hx, dotProduct_single] at h1
    exact (mul_eq_zero.mp h1).resolve_left hk'
  exact top_le_iff.mp (length_self_eq_top (R := R) ▸ Module.length_le_of_injective g hg)

theorem length_coker_of_injective {M : Type*} [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  have hr : Module.finrank R (LinearMap.range f) = Module.finrank R M :=
    LinearMap.finrank_range_of_inj hf
  set c := Submodule.smithNormalFormCoeffs b hr with hc
  set bt := Submodule.smithNormalFormTopBasis b hr with hbt
  set bb := Submodule.smithNormalFormBotBasis b hr with hbb
  have hdef : ∀ i, (bb i : M) = c i • bt i := Submodule.smithNormalFormBotBasis_def b hr
  have h1 : Module.length R (M ⧸ LinearMap.range f) = ∑ i, addVal R (c i) := by
    rw [(Submodule.quotientEquivPiSpan _ b hr).length_eq, Module.length_pi_of_fintype]
    exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (c i)
  have h2 := LinearMap.associated_det_comp_equiv (LinearMap.range f).subtype
    (LinearEquiv.ofInjective f hf) (bt.equiv bb (Equiv.refl ι))
  have h3 : (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf : M →ₗ[R] _) = f := by
    ext x
    rfl
  have h4 : LinearMap.det ((LinearMap.range f).subtype ∘ₗ
      (bt.equiv bb (Equiv.refl ι) : M →ₗ[R] LinearMap.range f)) = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix bt, ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Equiv.refl_apply, Submodule.subtype_apply, hdef, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, Matrix.diagonal_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  rw [h3, h4] at h2
  rw [h1, (addVal_eq_iff_associated _ _).mpr h2, addVal_prod]

theorem length_coker (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ LinearMap.range P.mulVecLin) = addVal R P.det := by
  by_cases h : P.det = 0
  · rw [length_coker_of_det_eq_zero P h, h, addVal_zero]
  · have hinj : Function.Injective P.mulVecLin := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      by_contra hx0
      exact h (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx0, hx⟩)
    rw [length_coker_of_injective (Pi.basisFun R ι) _ hinj, ← Matrix.toLin'_apply',
      LinearMap.det_toLin']

end GlobalTheory.RelativeLengthSpanDet
end

