module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.InnerConj
public import GroundTheory.LocalFields.Integers
public import GroundTheory.LocalFields.LubinTateTorsion

@[expose] public section

-- bundled from GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.ConjAction
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G) [N.Normal]

theorem cohomologyConj_one (n : ℕ) : cohomologyConj A N n 1 = 𝟙 _ :=
  cohomologyMapAlong_eq_id _ _ (by ext s; simp)
    (fun a => by change A.ρ 1 a = a; simp) n

theorem cohomologyConj_mul (n : ℕ) (g h : G) :
    cohomologyConj A N n (g * h) = cohomologyConj A N n h ≫ cohomologyConj A N n g := by
  rw [cohomologyConj, cohomologyConj, cohomologyConj, ← cohomologyMapAlong_comp]
  refine cohomologyMapAlong_congr _ _ _ _ ?_ (fun a => ?_) n
  · ext s
    simp only [GroundTheory.GroupCoh.coe_conjHom_apply, MonoidHom.coe_comp, Function.comp_apply]
    group
  · change A.ρ (g * h) a = A.ρ g (A.ρ h a)
    rw [map_mul]
    rfl

theorem cohomologyConj_mul_apply (n : ℕ) (g h : G) (x : cohomology (Rep.res N.subtype A) n) :
    (cohomologyConj A N n (g * h)).hom x =
      (cohomologyConj A N n g).hom ((cohomologyConj A N n h).hom x) := by
  rw [cohomologyConj_mul]
  rfl

theorem cohomologyConj_naturality {B : Rep.{u} k G} [IsDiscreteRep B] (f : A ⟶ B) (n : ℕ) (g : G) :
    cohomologyMap ((Rep.resFunctor N.subtype).map f) n ≫ cohomologyConj B N n g =
      cohomologyConj A N n g ≫ cohomologyMap ((Rep.resFunctor N.subtype).map f) n := by
  rw [← cohomologyMapAlong_id_eq_cohomologyMap, cohomologyConj, cohomologyConj,
    ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  refine cohomologyMapAlong_congr _ _ _ _ (by ext s; simp) (fun a => ?_) n
  exact (Rep.hom_comm_apply f g a).symm

noncomputable def conjShortComplexMor (S : ShortComplex (Rep.{u} k G)) (g : G) :
    (S.map (Rep.resFunctor N.subtype)).map (Rep.resFunctor (GroundTheory.GroupCoh.conjHom N g)) ⟶
      S.map (Rep.resFunctor N.subtype) where
  τ₁ := GroundTheory.GroupCoh.conjMor S.X₁ N g
  τ₂ := GroundTheory.GroupCoh.conjMor S.X₂ N g
  τ₃ := GroundTheory.GroupCoh.conjMor S.X₃ N g
  comm₁₂ := by
    ext a
    exact (Rep.hom_comm_apply S.f g a)
  comm₂₃ := by
    ext a
    exact (Rep.hom_comm_apply S.g g a)

theorem δ_comp_cohomologyConj {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁]
    [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] (hS : S.ShortExact) (i j : ℕ) (hij : i + 1 = j)
    (g : G) :
    δ (shortExact_map_res N hS) i j hij ≫ cohomologyConj S.X₁ N j g =
      cohomologyConj S.X₃ N i g ≫ δ (shortExact_map_res N hS) i j hij :=
  δ_comp_cohomologyMapAlong (GroundTheory.GroupCoh.conjHom N g) (continuous_conjHom N g)
    (conjShortComplexMor N S g) _ _ i j hij

section CompactSubgroup

variable [CompactSpace N]

theorem cohomologyConj_of_mem (n : ℕ) {m : G} (hm : m ∈ N) : cohomologyConj A N n m = 𝟙 _ := by
  rw [← cohomologyInnerConj_eq_id (Γ := N) n (Rep.res N.subtype A) ⟨m, hm⟩]
  exact cohomologyMapAlong_congr _ _ _ _ (by ext s; simp) (fun a => rfl) n

theorem cohomologyConj_eq_of_mk_eq (n : ℕ) {g h : G} (hgh : (g : G ⧸ N) = h) :
    cohomologyConj A N n g = cohomologyConj A N n h := by
  have hm : g⁻¹ * h ∈ N := QuotientGroup.eq.1 hgh
  have : h = g * (g⁻¹ * h) := by group
  rw [this, cohomologyConj_mul, cohomologyConj_of_mem A N n hm, Category.id_comp]

noncomputable def cohomologyConjRep (n : ℕ) :
    Representation k (G ⧸ N) (cohomology (Rep.res N.subtype A) n) where
  toFun q := (cohomologyConj A N n q.out).hom
  map_one' := by
    rw [cohomologyConj_eq_of_mk_eq A N n (h := 1) (by rw [QuotientGroup.out_eq']; rfl),
      cohomologyConj_one]
    rfl
  map_mul' q r := by
    rw [cohomologyConj_eq_of_mk_eq A N n (h := q.out * r.out)
      (by rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq',
        QuotientGroup.out_eq']), cohomologyConj_mul]
    rfl

theorem cohomologyConjRep_mk (n : ℕ) (g : G) (x : cohomology (Rep.res N.subtype A) n) :
    cohomologyConjRep A N n (g : G ⧸ N) x = (cohomologyConj A N n g).hom x := by
  change (cohomologyConj A N n (g : G ⧸ N).out).hom x = _
  rw [cohomologyConj_eq_of_mk_eq A N n (QuotientGroup.out_eq' (g : G ⧸ N))]

theorem mem_cohomologyConjInvariants_iff (n : ℕ) (x : cohomology (Rep.res N.subtype A) n) :
    x ∈ cohomologyConjInvariants A N n ↔ x ∈ (cohomologyConjRep A N n).invariants := by
  refine ⟨fun hx q => ?_, fun hx g => ?_⟩
  · induction q using QuotientGroup.induction_on with
    | H g => rw [cohomologyConjRep_mk]; exact hx g
  · rw [← cohomologyConjRep_mk]
    exact hx _

end CompactSubgroup

section CompactGroup

variable [CompactSpace G]

theorem cohomologyRes_comp_cohomologyConj (n : ℕ) (g : G) :
    cohomologyRes A N n ≫ cohomologyConj A N n g = cohomologyRes A N n := by
  conv_rhs => rw [← Category.id_comp (cohomologyRes A N n), ← cohomologyInnerConj_eq_id n A g]
  rw [cohomologyRes, cohomologyConj, cohomologyInnerConj, ← cohomologyMapAlong_comp,
    ← cohomologyMapAlong_comp]
  exact cohomologyMapAlong_congr _ _ _ _ (by ext s; simp) (fun a => rfl) n

theorem cohomologyRes_apply_mem_cohomologyConjInvariants (n : ℕ) (x : cohomology A n) :
    (cohomologyRes A N n).hom x ∈ cohomologyConjInvariants A N n := fun g => by
  rw [← ModuleCat.comp_apply, cohomologyRes_comp_cohomologyConj]

end CompactGroup

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open GroundTheory.LocalField ValuativeRel

section Integers

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem card_quotient_span_eq_one_of_isUnit {a : 𝒪[K]} (ha : IsUnit a) :
    Nat.card (𝒪[K] ⧸ Ideal.span {a}) = 1 := by
  rw [Ideal.span_singleton_eq_top.2 ha]
  have : Subsingleton (𝒪[K] ⧸ (⊤ : Ideal 𝒪[K])) := Ideal.Quotient.subsingleton_iff.2 rfl
  exact Nat.card_unique

theorem card_quotient_span_mul {a b : 𝒪[K]} (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.card (𝒪[K] ⧸ Ideal.span {a * b}) =
      Nat.card (𝒪[K] ⧸ Ideal.span {a}) * Nat.card (𝒪[K] ⧸ Ideal.span {b}) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨i, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  obtain ⟨j, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hπ
  have key : ∀ (v : 𝒪[K]ˣ) (n : ℕ), Ideal.span {(v : 𝒪[K]) * π ^ n} = Ideal.span {π ^ n} :=
    fun v n => Ideal.span_singleton_mul_left_unit v.isUnit _
  have hab : (u : 𝒪[K]) * π ^ i * ((w : 𝒪[K]) * π ^ j) =
      ((u * w : 𝒪[K]ˣ) : 𝒪[K]) * π ^ (i + j) := by
    push_cast
    ring
  rw [hab, key, key, key, FormalGroup.card_quotient_span_pow hπ, FormalGroup.card_quotient_span_pow hπ,
    FormalGroup.card_quotient_span_pow hπ, pow_add]


omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem natCast_integer_ne_zero {m : ℕ} (hm : (m : K) ≠ 0) : (m : 𝒪[K]) ≠ 0 := by
  intro h
  apply hm
  have := congrArg (fun x : 𝒪[K] => (x : K)) h
  simpa using this

theorem card_quotient_span_natCast_mul {m n : ℕ} (hm : (m : K) ≠ 0) (hn : (n : K) ≠ 0) :
    Nat.card (𝒪[K] ⧸ Ideal.span {((m * n : ℕ) : 𝒪[K])}) =
      Nat.card (𝒪[K] ⧸ Ideal.span {(m : 𝒪[K])}) * Nat.card (𝒪[K] ⧸ Ideal.span {(n : 𝒪[K])}) := by
  rw [Nat.cast_mul]
  exact card_quotient_span_mul (natCast_integer_ne_zero hm) (natCast_integer_ne_zero hn)

theorem card_quotient_span_natCast_pow {m : ℕ} (hm : (m : K) ≠ 0) (d : ℕ) :
    Nat.card (𝒪[K] ⧸ Ideal.span {((m ^ d : ℕ) : 𝒪[K])}) =
      Nat.card (𝒪[K] ⧸ Ideal.span {(m : 𝒪[K])}) ^ d := by
  induction d with
  | zero =>
    rw [pow_zero, pow_zero, Nat.cast_one]
    exact card_quotient_span_eq_one_of_isUnit isUnit_one
  | succ d ih =>
    have hmd : ((m ^ d : ℕ) : K) ≠ 0 := by
      rw [Nat.cast_pow]
      exact pow_ne_zero _ hm
    rw [pow_succ, card_quotient_span_natCast_mul hmd hm, ih, pow_succ]

theorem card_quotient_span_natCast_eq_one {m : ℕ} (hm : (m : 𝓀[K]) ≠ 0) :
    Nat.card (𝒪[K] ⧸ Ideal.span {(m : 𝒪[K])}) = 1 := by
  apply card_quotient_span_eq_one_of_isUnit
  by_contra h
  apply hm
  rw [← map_natCast (IsLocalRing.residue 𝒪[K]), IsLocalRing.residue_eq_zero_iff]
  exact (IsLocalRing.mem_maximalIdeal _).2 h

end Integers

section Extension

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L]

theorem card_quotient_span_natCast_finiteExtension (m : ℕ) :
    Nat.card (𝒪[L] ⧸ Ideal.span {(m : 𝒪[L])}) =
      Nat.card (𝒪[K] ⧸ Ideal.span {(m : 𝒪[K])}) ^ Module.finrank K L := by
  classical
  let ι := Module.Free.ChooseBasisIndex 𝒪[K] 𝒪[L]
  let b : Module.Basis ι 𝒪[K] 𝒪[L] := Module.Free.chooseBasis 𝒪[K] 𝒪[L]
  let I : Ideal 𝒪[K] := Ideal.span {(m : 𝒪[K])}
  let ψ : 𝒪[L] →ₗ[𝒪[K]] (ι → 𝒪[K] ⧸ I) :=
    LinearMap.pi fun i => I.mkQ ∘ₗ (LinearMap.proj i ∘ₗ b.equivFun.toLinearMap)
  have hψ : ∀ x i, ψ x i = Submodule.Quotient.mk (b.equivFun x i) := fun _ _ => rfl
  have hsmul : ∀ y : 𝒪[L], (m : 𝒪[K]) • y = (m : 𝒪[L]) * y := fun y => by
    rw [Algebra.smul_def, map_natCast]
  have hsurj : Function.Surjective ψ := by
    intro v
    refine ⟨b.equivFun.symm fun i => Quotient.out (v i), ?_⟩
    funext i
    rw [hψ, LinearEquiv.apply_symm_apply]
    exact Quotient.out_eq (v i)
  have hker : LinearMap.ker ψ = (Ideal.span {(m : 𝒪[L])}).restrictScalars 𝒪[K] := by
    ext x
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
    constructor
    · intro hx
      have hc : ∀ i, ∃ c : 𝒪[K], c * (m : 𝒪[K]) = b.equivFun x i := fun i => by
        have := congrFun hx i
        rw [hψ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
        exact Ideal.mem_span_singleton'.1 this
      choose c hc using hc
      refine ⟨b.equivFun.symm c, ?_⟩
      rw [mul_comm, ← hsmul]
      apply b.equivFun.injective
      rw [map_smul, LinearEquiv.apply_symm_apply]
      funext i
      rw [Pi.smul_apply, smul_eq_mul, ← hc i, mul_comm]
    · rintro ⟨a, rfl⟩
      funext i
      rw [hψ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, mul_comm, ← hsmul, map_smul,
        Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have e1 : (𝒪[L] ⧸ (Ideal.span {(m : 𝒪[L])}).restrictScalars 𝒪[K]) ≃ₗ[𝒪[K]] (ι → 𝒪[K] ⧸ I) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (ψ.quotKerEquivOfSurjective hsurj)
  have e2 := Submodule.Quotient.restrictScalarsEquiv 𝒪[K] (Ideal.span {(m : 𝒪[L])})
  rw [← Nat.card_congr e2.toEquiv, Nat.card_congr e1.toEquiv, Nat.card_fun,
    ← Module.finrank_eq_nat_card_basis b, finrank_integer]

end Extension

section Groups

theorem exists_card_eq_prime_pow_of_nsmul {A : Type*} [AddCommGroup A] [Finite A] {l : ℕ}
    [Fact l.Prime] (h : ∀ a : A, l • a = 0) : ∃ d, Nat.card A = l ^ d := by
  have hP : IsPGroup l (Multiplicative A) := fun x => ⟨1, by
    rw [pow_one]
    exact congrArg Multiplicative.ofAdd (h (Multiplicative.toAdd x))⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  exact ⟨n, hn⟩

theorem exists_ne_zero_forall_mem_eq {k G : Type*} [CommRing k] [Group G] {l : ℕ} [Fact l.Prime]
    (M : Rep k G) [Finite M] [Nontrivial M] (hl : ∀ m : M, l • m = 0) (W T : Subgroup G)
    (hT : ∀ g ∈ T, ∀ m : M, M.ρ g m = m) (hW : ∀ g ∈ W, ∃ n : ℕ, g ^ l ^ n ∈ T) :
    ∃ m : M, m ≠ 0 ∧ ∀ g ∈ W, M.ρ g m = m := by
  let H := W.map (Representation.asGroupHom M.ρ)
  have hH : IsPGroup l H := by
    rintro ⟨_, g, hg, rfl⟩
    obtain ⟨n, hn⟩ := hW g hg
    refine ⟨n, Subtype.ext (Units.ext (LinearMap.ext fun a => ?_))⟩
    simp only [SubmonoidClass.coe_pow, Subgroup.coe_one, Units.val_one, Module.End.one_apply]
    rw [← map_pow, Representation.asGroupHom_apply, hT _ hn]
  obtain ⟨d, hd⟩ := exists_card_eq_prime_pow_of_nsmul hl
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h1 := (Finite.one_lt_card_iff_nontrivial (α := M)).2 inferInstance
    rw [hd, pow_zero] at h1
    exact lt_irrefl _ h1
  have hcard : l ∣ Nat.card M := hd ▸ dvd_pow_self l hd0
  have h0 : (0 : M) ∈ MulAction.fixedPoints H M := fun h => by
    show (h : (M →ₗ[k] M)ˣ) • (0 : M) = 0
    exact smul_zero _
  obtain ⟨b, hb, hb0⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point M hcard h0
  exact ⟨b, hb0.symm, fun g hg => hb ⟨_, g, hg, rfl⟩⟩

end Groups

end GroundTheory.ProfCoh
end

