module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroAlgebraMapEqMulOfFormallyUnramifiedA
section
open Algebra

namespace GlobalTheory

theorem exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified :
    ∀ (P D : Type) [CommRing P] [IsDomain P] [CommRing D] [IsDomain D] [Algebra P D]
      [Algebra.FiniteType P D] [Algebra.FormallyUnramified P D] (f : D), f ≠ 0 →
      ∃ Q : P, Q ≠ 0 ∧ ∃ d : D, algebraMap P D Q = f * d := by
  intro P D _ _ _ _ _ _ _ f hf
  by_cases hinj : Function.Injective (algebraMap P D)
  swap
  · rw [injective_iff_map_eq_zero] at hinj
    push_neg at hinj
    obtain ⟨Q, hQ, hQ0⟩ := hinj
    exact ⟨Q, hQ0, 0, by rw [hQ, mul_zero]⟩
  let M := nonZeroDivisors P
  let K := FractionRing P
  let S := Algebra.algebraMapSubmonoid D M
  let L := Localization S
  letI : Algebra K L := localizationAlgebra M D
  haveI : IsScalarTower P K L := inferInstance
  have hS : S ≤ nonZeroDivisors D := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hq))
  haveI : IsDomain L := IsLocalization.isDomain_localization hS
  have hDL : Function.Injective (algebraMap D L) := IsLocalization.injective L hS
  haveI : IsLocalization (M.map (algebraMap P D)) L := inferInstanceAs (IsLocalization S L)
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.localization_map M (S := D)
  haveI : Algebra.EssFiniteType D L := Algebra.EssFiniteType.of_isLocalization L S
  haveI : Algebra.EssFiniteType P L := Algebra.EssFiniteType.comp P D L
  haveI : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp P K L
  haveI : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L
  have hint : IsIntegral K (algebraMap D L f) := Algebra.IsIntegral.isIntegral _
  have hne : algebraMap D L f ≠ 0 := (map_ne_zero_iff _ hDL).2 hf
  obtain ⟨u, hu⟩ := hint.isUnit hne
  have hy : algebraMap D L f * ↑u⁻¹ = 1 := by rw [← hu]; exact u.mul_inv
  obtain ⟨⟨d, s⟩, hds⟩ := IsLocalization.surj S (↑u⁻¹ : L)
  obtain ⟨q, hq, hqs⟩ := s.2
  refine ⟨q, nonZeroDivisors.ne_zero hq, d, ?_⟩
  apply hDL
  simp only at hds
  rw [map_mul, ← hds, ← mul_assoc, hy, one_mul, hqs]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfRankEq
section
namespace GlobalTheory.SemisimpleCount

variable {Rg : Type} [Ring Rg] [Algebra ℂ Rg]

def killed (I : Set Rg) (M : Type) [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] : Submodule ℂ M where
  carrier := {m | ∀ x ∈ I, x • m = 0}
  add_mem' := fun ha hb x hx => by rw [smul_add, ha x hx, hb x hx, add_zero]
  zero_mem' := fun x _ => smul_zero x
  smul_mem' := fun c m hm x hx => by rw [smul_comm, hm x hx, smul_zero]

section
variable (I : Set Rg) {M N : Type} [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N]

theorem mem_killed {m : M} : m ∈ killed I M ↔ ∀ x ∈ I, x • m = 0 := Iff.rfl

theorem map_mem_killed {A B : Type} [AddCommGroup A] [Module Rg A] [AddCommGroup B] [Module Rg B]
    (f : A →ₗ[Rg] B) {a : A} (ha : ∀ x ∈ I, x • a = 0) : ∀ x ∈ I, x • f a = 0 := by
  intro x hx
  rw [← map_smul, ha x hx, map_zero]

theorem rank_killed_le (f : M →ₗ[Rg] N) (hf : Function.Injective f) :
    Module.rank ℂ (killed I M) ≤ Module.rank ℂ (killed I N) := by
  refine LinearMap.rank_le_of_injective
    ((f.restrictScalars ℂ).restrict (p := killed I M) (q := killed I N)
      (fun m hm => map_mem_killed I f hm)) ?_
  intro a b hab
  exact Subtype.ext (hf (congrArg Subtype.val hab))

theorem rank_killed_congr (e : M ≃ₗ[Rg] N) :
    Module.rank ℂ (killed I M) = Module.rank ℂ (killed I N) :=
  le_antisymm (rank_killed_le I e.toLinearMap e.injective)
    (rank_killed_le I e.symm.toLinearMap e.symm.injective)

theorem rank_killed_prod :
    Module.rank ℂ (killed I (M × N)) =
      Module.rank ℂ (killed I M) + Module.rank ℂ (killed I N) := by
  have h : killed I (M × N) = (killed I M).prod (killed I N) := by
    ext ⟨a, b⟩
    simp only [mem_killed, Submodule.mem_prod, Prod.smul_mk, Prod.mk_eq_zero]
    exact ⟨fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩,
      fun h x hx => ⟨h.1 x hx, h.2 x hx⟩⟩
  rw [h, ← rank_prod']
  refine LinearEquiv.rank_eq
    { toFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), p.1.2, p.2.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem rank_killed_compl {U V : Submodule Rg M} (h : IsCompl U V) :
    Module.rank ℂ (killed I M) = Module.rank ℂ (killed I U) + Module.rank ℂ (killed I V) := by
  rw [← rank_killed_congr I (Submodule.prodEquivOfIsCompl U V h), rank_killed_prod]

variable {S : Type} [AddCommGroup S] [Module Rg S]

theorem rank_hom_le (f : M →ₗ[Rg] N) (hf : Function.Injective f) :
    Module.rank ℂ (S →ₗ[Rg] M) ≤ Module.rank ℂ (S →ₗ[Rg] N) := by
  refine LinearMap.rank_le_of_injective
    { toFun := fun g => f.comp g
      map_add' := fun a b => by ext; simp
      map_smul' := fun c a => by
        ext s
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
        exact (f.restrictScalars ℂ).map_smul c (a s) } ?_
  intro a b hab
  ext s
  exact hf (LinearMap.congr_fun hab s)

theorem rank_hom_congr (e : M ≃ₗ[Rg] N) :
    Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S →ₗ[Rg] N) :=
  le_antisymm (rank_hom_le e.toLinearMap e.injective)
    (rank_hom_le e.symm.toLinearMap e.symm.injective)

theorem rank_hom_compl {U V : Submodule Rg M} (h : IsCompl U V) :
    Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S →ₗ[Rg] U) + Module.rank ℂ (S →ₗ[Rg] V) := by
  rw [← rank_hom_congr (Submodule.prodEquivOfIsCompl U V h), ← rank_prod']
  exact (LinearMap.prodEquiv ℂ).rank_eq.symm

theorem rank_hom_congr_left {S' : Type} [AddCommGroup S'] [Module Rg S'] (e : S ≃ₗ[Rg] S') :
    Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S' →ₗ[Rg] M) :=
  LinearEquiv.rank_eq
    { toFun := fun g => g.comp e.symm.toLinearMap
      invFun := fun g => g.comp e.toLinearMap
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun g => by ext; simp
      right_inv := fun g => by ext; simp }

theorem injective_of_ne_zero {A : Type} [AddCommGroup A] [Module Rg A] [IsSimpleModule Rg S]
    {f : S →ₗ[Rg] A} (hf : f ≠ 0) : Function.Injective f :=
  (LinearMap.injective_or_eq_zero f).resolve_right hf

theorem rank_hom_le_killed [IsSimpleModule Rg S] {s : S} (hs : s ≠ 0) (hI : ∀ x ∈ I, x • s = 0) :
    Module.rank ℂ (S →ₗ[Rg] M) ≤ Module.rank ℂ (killed I M) := by
  refine LinearMap.rank_le_of_injective
    { toFun := fun g => ⟨g s, map_mem_killed I g hI⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl } ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h
  have h0 : a s = 0 := congrArg Subtype.val ha
  exact hs (injective_of_ne_zero h (h0.trans (map_zero a).symm))

theorem exists_ne_zero_of_rank_eq {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] (h : Module.rank ℂ A = Module.rank ℂ B) {a : A} (ha : a ≠ 0) :
    ∃ b : B, b ≠ 0 := by
  by_contra hb
  push_neg at hb
  exact ha (rank_zero_iff_forall_zero.1 (h.trans (rank_zero_iff_forall_zero.2 hb)) a)

theorem exists_simple {A : Type} [AddCommGroup A] [Module Rg A] [IsSemisimpleModule Rg A]
    {a : A} (ha : a ≠ 0) (hI : ∀ x ∈ I, x • a = 0) :
    ∃ U : Submodule Rg A, IsSimpleModule Rg U ∧ ∃ u : U, u ≠ 0 ∧ ∀ x ∈ I, x • u = 0 := by
  have hj : a ∉ Module.jacobson Rg A := by
    rw [IsSemisimpleModule.jacobson_eq_bot]
    simpa using ha
  simp only [Module.jacobson, Submodule.mem_sInf, not_forall] at hj
  obtain ⟨P, hP, haP⟩ := hj
  obtain ⟨U, hU⟩ := exists_isCompl P
  have e := Submodule.quotientEquivOfIsCompl P U hU
  haveI : IsSimpleModule Rg (A ⧸ P) := isSimpleModule_iff_isCoatom.2 hP
  refine ⟨U, IsSimpleModule.congr e.symm, e (P.mkQ a), ?_, ?_⟩
  · simpa using haP
  · exact map_mem_killed I (e.toLinearMap.comp P.mkQ) hI

end

theorem rank_killed_eq (I : Set Rg) (n : ℕ) :
    ∀ (M N : Type) [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N]
    [IsSemisimpleModule Rg M] [IsSemisimpleModule Rg N],
    Module.rank ℂ (killed I M) = n →
    (∀ (S : Type) [AddCommGroup S] [Module Rg S] [IsSimpleModule Rg S] (s : S), s ≠ 0 →
      (∀ x ∈ I, x • s = 0) → Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S →ₗ[Rg] N)) →
    Module.rank ℂ (killed I N) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M N _ _ _ _ _ _ _ _ _ _ hn H
  have sub_ne : ∀ {A : Type} [AddCommGroup A] [Module Rg A] (U : Submodule Rg A) (u : U),
      u ≠ 0 → U.subtype ≠ 0 := by
    intro A _ _ U u hu h
    exact hu (Subtype.ext (LinearMap.congr_fun h u))
  by_cases h0 : ∀ m : killed I M, m = 0
  · rw [← hn, rank_zero_iff_forall_zero.2 h0, rank_zero_iff_forall_zero]
    intro a
    by_contra ha
    obtain ⟨U, hU, u, hu, hI⟩ := exists_simple I (a := a.1) (fun h => ha (Subtype.ext h)) a.2
    obtain ⟨f, hf⟩ := exists_ne_zero_of_rank_eq (H U u hu hI).symm (sub_ne U u hu)
    have h1 : f u = 0 := congrArg Subtype.val (h0 ⟨f u, map_mem_killed I f hI⟩)
    exact hu (injective_of_ne_zero hf (h1.trans (map_zero f).symm))
  · push_neg at h0
    obtain ⟨a, ha⟩ := h0
    obtain ⟨U, hU, u, hu, hI⟩ := exists_simple I (a := a.1) (fun h => ha (Subtype.ext h)) a.2
    obtain ⟨f, hf⟩ := exists_ne_zero_of_rank_eq (H U u hu hI) (sub_ne U u hu)
    have e : U ≃ₗ[Rg] LinearMap.range f := LinearEquiv.ofInjective f (injective_of_ne_zero hf)
    obtain ⟨M', hM'⟩ := exists_isCompl U
    obtain ⟨N', hN'⟩ := exists_isCompl (LinearMap.range f)
    have hM := rank_killed_compl I hM'
    rw [hn] at hM
    have hUf : Module.rank ℂ (killed I U) < Cardinal.aleph0 :=
      lt_of_le_of_lt (hM ▸ le_self_add) (Cardinal.natCast_lt_aleph0 (n := n))
    have hMf : Module.rank ℂ (killed I M') < Cardinal.aleph0 :=
      lt_of_le_of_lt (hM ▸ le_add_self) (Cardinal.natCast_lt_aleph0 (n := n))
    obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.1 hUf
    obtain ⟨l, hl⟩ := Cardinal.lt_aleph0.1 hMf
    have hk0 : k ≠ 0 := by
      rintro rfl
      have := rank_zero_iff_forall_zero.1 (hk.trans Nat.cast_zero) ⟨u, hI⟩
      exact hu (congrArg Subtype.val this)
    have hkl : n = k + l := by
      rw [hk, hl] at hM
      exact_mod_cast hM
    have hN := ih l (by omega) M' N' hl (by
      intro S _ _ _ s hs hsI
      have h := H S s hs hsI
      rw [rank_hom_compl hM', rank_hom_compl hN', ← rank_hom_congr e] at h
      have hfin : Module.rank ℂ (S →ₗ[Rg] U) < Cardinal.aleph0 :=
        lt_of_le_of_lt (rank_hom_le_killed I hs hsI) hUf
      exact Cardinal.eq_of_add_eq_add_left h hfin)
    rw [rank_killed_compl I hN', ← rank_killed_congr I e, hk, hN, hkl, Nat.cast_add]

theorem finrank_killed_eq : ∀ (Rg : Type) [Ring Rg] [Algebra ℂ Rg] (M N : Type) [AddCommGroup M] [Module ℂ M] [Module Rg M] [IsScalarTower ℂ Rg M] [SMulCommClass Rg ℂ M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N] [SMulCommClass Rg ℂ N] (I : Set Rg) (FM : Submodule ℂ M) (FN : Submodule ℂ N), IsSemisimpleModule Rg M → IsSemisimpleModule Rg N → (∀ m, m ∈ FM ↔ ∀ x ∈ I, x • m = 0) → (∀ n, n ∈ FN ↔ ∀ x ∈ I, x • n = 0) → FiniteDimensional ℂ FM → FiniteDimensional ℂ FN → (∀ U : Submodule Rg M, IsSimpleModule Rg U → (∃ u ∈ U, u ≠ 0 ∧ u ∈ FM) → Module.rank ℂ (U →ₗ[Rg] M) = Module.rank ℂ (U →ₗ[Rg] N)) → (∀ U : Submodule Rg N, IsSimpleModule Rg U → (∃ u ∈ U, u ≠ 0 ∧ u ∈ FN) → Module.rank ℂ (U →ₗ[Rg] M) = Module.rank ℂ (U →ₗ[Rg] N)) → Module.finrank ℂ FM = Module.finrank ℂ FN := by
  intro Rg _ _ M N _ _ _ _ _ _ _ _ _ _ I FM FN hM hN hFM hFN fM fN HM HN
  obtain rfl : FM = killed I M := Submodule.ext hFM
  obtain rfl : FN = killed I N := Submodule.ext hFN
  have key := rank_killed_eq I (Module.finrank ℂ (killed I M)) M N
    (Module.finrank_eq_rank ℂ _).symm (by
      intro S _ _ _ s hs hI
      by_cases h1 : ∃ f : S →ₗ[Rg] M, f ≠ 0
      · obtain ⟨f, hf⟩ := h1
        have hi := injective_of_ne_zero hf
        have e : S ≃ₗ[Rg] LinearMap.range f := LinearEquiv.ofInjective f hi
        rw [rank_hom_congr_left e, rank_hom_congr_left e]
        exact HM _ (IsSimpleModule.congr e.symm) ⟨f s, ⟨s, rfl⟩,
          fun h => hs (hi (h.trans (map_zero f).symm)), map_mem_killed I f hI⟩
      by_cases h2 : ∃ f : S →ₗ[Rg] N, f ≠ 0
      · obtain ⟨f, hf⟩ := h2
        have hi := injective_of_ne_zero hf
        have e : S ≃ₗ[Rg] LinearMap.range f := LinearEquiv.ofInjective f hi
        rw [rank_hom_congr_left e, rank_hom_congr_left e]
        exact HN _ (IsSimpleModule.congr e.symm) ⟨f s, ⟨s, rfl⟩,
          fun h => hs (hi (h.trans (map_zero f).symm)), map_mem_killed I f hI⟩
      push_neg at h1 h2
      rw [rank_zero_iff_forall_zero.2 h1, rank_zero_iff_forall_zero.2 h2])
  exact (Module.finrank_eq_of_rank_eq key).symm

end GlobalTheory.SemisimpleCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroSmulMem
section
namespace GlobalTheory.NonzeroScalarMultipleMembership

theorem exists_ne_zero_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {L : Submodule (NumberField.RingOfIntegers K) V} {x : V}
    (hx : x ∈ Submodule.span K (L : Set V)) :
    ∃ a : NumberField.RingOfIntegers K, a ≠ 0 ∧ a • x ∈ L := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ hay
    · rw [mul_smul]; exact L.smul_mem _ hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap (NumberField.RingOfIntegers K) K q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have h : (a * q) • (c • y) = p • (a • y) := by
      rw [← algebraMap_smul K (a * q), ← algebraMap_smul K p, ← algebraMap_smul K a,
        smul_smul, smul_smul, ← hpq, map_mul]
      congr 1
      field_simp
    rw [h]
    exact L.smul_mem _ hay

end GlobalTheory.NonzeroScalarMultipleMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroSmulMemOfMemSpan
section
namespace GlobalTheory.NonzeroScalarInSpan

theorem exists_ne_zero_smul_mem_of_mem_span {R K V : Type} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (N : Submodule R V) {x : V}
    (hx : x ∈ Submodule.span K (↑N : Set V)) : ∃ a : R, a ≠ 0 ∧ a • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact N.smul_mem b hay
    · rw [mul_smul]
      exact N.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors R) c
    have hq : (q : R) ≠ 0 := nonZeroDivisors.coe_ne_zero q
    refine ⟨a * q, mul_ne_zero ha hq, ?_⟩
    have h1 : (q : R) • c • y = p • y := by
      rw [← algebraMap_smul K (q : R), smul_smul, mul_comm]
      simp only at hpq
      rw [hpq, algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact N.smul_mem p hay

end GlobalTheory.NonzeroScalarInSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroSmulMemSpan
section
namespace GlobalTheory.NonzeroMultipleInSpan

open NumberField

theorem exists_ne_zero_smul_mem_span {LL : Type} [Field LL] [NumberField LL] {n : ℕ}
    (T : Set (Fin n → LL)) :
    ∀ x ∈ Submodule.span LL T, ∃ d : 𝓞 LL, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 LL) T := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using Submodule.subset_span hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : (a * b) • (y + z) = b • (a • y) + a • (b • z) := by
      rw [smul_add, ← mul_smul, ← mul_smul, mul_comm b a]
    rw [h]
    exact Submodule.add_mem _ (Submodule.smul_mem _ b hay) (Submodule.smul_mem _ a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 LL)) c
    refine ⟨(q : 𝓞 LL) * a, mul_ne_zero (nonZeroDivisors.ne_zero q.2) ha, ?_⟩
    have h : ((q : 𝓞 LL) * a) • (c • y) = p • (a • y) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      simp only at hpq
      rw [← hpq]
      ring
    rw [h]
    exact Submodule.smul_mem _ p hay

end GlobalTheory.NonzeroMultipleInSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRank
section
open Matrix

namespace GlobalTheory

theorem exists_rows_linearIndependent_of_le_rank {K m n : Type} [Field K] [Fintype m] [Fintype n]
    (ρ : ℕ) (M : Matrix m n K) (h : ρ ≤ M.rank) :
    ∃ S : Fin ρ → m, LinearIndependent K (M.submatrix S id).row := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K M.row
  haveI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hκ : Fintype.card κ = M.rank := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row]
  have hle : Fintype.card (Fin ρ) ≤ Fintype.card κ := by rw [hκ, Fintype.card_fin]; exact h
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hle
  exact ⟨a ∘ f, hli.comp f f.injective⟩

theorem exists_submatrix_det_ne_zero_of_le_rank :
    ∀ (k : Type) [Field k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
      (ρ : ℕ) (Y : Matrix A D k), ρ ≤ Y.rank → ∃ S : Fin ρ → A, ∃ τ : Fin ρ → D,
        (Y.submatrix S τ).det ≠ 0 := by
  intro k _ A D _ _ _ _ ρ Y h
  obtain ⟨S, hS⟩ := exists_rows_linearIndependent_of_le_rank ρ Y h
  have hZ : (Y.submatrix S id).rank = ρ := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hS, Fintype.card_fin]
  have hZt : ρ ≤ (Y.submatrix S id)ᵀ.rank := by rw [Matrix.rank_transpose, hZ]
  obtain ⟨τ, hτ⟩ := exists_rows_linearIndependent_of_le_rank ρ (Y.submatrix S id)ᵀ hZt
  refine ⟨S, τ, ?_⟩
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hτ)
  have e : (Y.submatrix S id)ᵀ.submatrix τ id = (Y.submatrix S τ)ᵀ := by ext i j; rfl
  rw [e, Matrix.det_transpose] at hu
  exact hu.ne_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneTmulEq
section
namespace GlobalTheory.OneTensorExistence

open TensorProduct

theorem exists_one_tmul_eq (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ]
    [Algebra A Λ] (z : TensorProduct A (IsLocalRing.ResidueField A) Λ) :
    ∃ y : Λ, (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] y = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul k l =>
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective k
    refine ⟨a • l, ?_⟩
    rw [← TensorProduct.smul_tmul, ← IsLocalRing.ResidueField.algebraMap_eq,
      Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact ⟨u + v, TensorProduct.tmul_add _ _ _⟩

end GlobalTheory.OneTensorExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosMulExtendIntLinearForm
section
namespace GlobalTheory

theorem exists_pos_mul_extend_int_linearForm (F : Type) [AddCommGroup F] [Module.Free ℤ F]
    [Module.Finite ℤ F] (P : Submodule ℤ F) (f : P →ₗ[ℤ] ℤ) :
    ∃ c : ℤ, 0 < c ∧ ∃ lam : F →ₗ[ℤ] ℤ, ∀ x : P, lam x = c * f x := by
  classical
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible ℚ).extension_property P.subtype
    P.injective_subtype ((Algebra.linearMap ℤ ℚ).comp f)
  let b := Module.Free.chooseBasis ℤ F
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (S := ℚ) (fun i => g (b i))
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose n hn using hint
  let lam : F →ₗ[ℤ] ℤ := b.constr ℤ n
  have key : (Algebra.linearMap ℤ ℚ).comp lam = d • g := by
    refine b.ext fun i => ?_
    simpa [lam] using hn i
  refine ⟨d * d, mul_self_pos.mpr hd0, d • lam, fun x => ?_⟩
  have h1 := LinearMap.congr_fun key x
  have h2 := LinearMap.congr_fun hg x
  simp at h1 h2
  rw [h2] at h1
  have h3 : lam x = d * f x := by exact_mod_cast h1
  simp [h3, mul_assoc]

end GlobalTheory
end

