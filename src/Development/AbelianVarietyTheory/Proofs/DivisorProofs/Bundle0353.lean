module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilRepresentationHeisenberg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyLongExactFirstOfInjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LesFirst

section
variable {R : Type} [CommRing R]

theorem ofHom_comp_comp {K L M I : Cx R} (φ : K ⟶ L) (ψ : L ⟶ M) {n : ℤ} (z : Cochain M I n) :
    (Cochain.ofHom φ).comp ((Cochain.ofHom ψ).comp z (zero_add n)) (zero_add n) =
      (Cochain.ofHom (φ ≫ ψ)).comp z (zero_add n) := by
  ext p q hpq; simp

theorem δ_ofHom_comp' {K L I : Cx R} (φ : K ⟶ L) {n m : ℤ} (z : Cochain L I n) :
    δ n m ((Cochain.ofHom φ).comp z (zero_add n)) = (Cochain.ofHom φ).comp (δ n m z) (zero_add m) := by
  by_cases h : n + 1 = m
  · rw [δ_comp _ _ (zero_add n) 1 m m h (zero_add 1) h]; simp
  · simp [δ_shape _ _ h]

theorem cpull_mk {K L I : Cx R} (φ : K ⟶ L) {n : ℤ} (z : Cocycle L I n) :
    cpull φ I n (CohomologyClass.mk z) = CohomologyClass.mk (zcomp (Cocycle.ofHom φ) z (zero_add n)) := rfl

theorem cpull_comp {K L M I : Cx R} (φ : K ⟶ L) (ψ : L ⟶ M) (n : ℤ) (x : CohomologyClass M I n) :
    cpull φ I n (cpull ψ I n x) = cpull (φ ≫ ψ) I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  exact congrArg CohomologyClass.mk (Cocycle.ext (ofHom_comp_comp φ ψ x.1))

theorem cpull_zero' {K L I : Cx R} (n : ℤ) (x : CohomologyClass L I n) :
    cpull (0 : K ⟶ L) I n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpull_mk, ← CohomologyClass.mk_zero]
  exact congrArg CohomologyClass.mk (Cocycle.ext (by simp [zcomp]))

variable {I : Cx R} (S : ShortComplex (Cx R))

def Snake {n : ℤ} (a : Cochain S.X₁ I n) (c : Cochain S.X₃ I (n + 1)) : Prop :=
  ∃ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = a ∧
    (Cochain.ofHom S.g).comp c (zero_add (n + 1)) = δ n (n + 1) b

theorem fg_zero {n : ℤ} (e : Cochain S.X₃ I n) :
    (Cochain.ofHom S.f).comp ((Cochain.ofHom S.g).comp e (zero_add n)) (zero_add n) = 0 := by
  rw [ofHom_comp_comp, S.zero]; simp

theorem snake_add {n : ℤ} {a a' : Cochain S.X₁ I n} {c c' : Cochain S.X₃ I (n + 1)}
    (h : Snake S a c) (h' : Snake S a' c') : Snake S (a + a') (c + c') := by
  obtain ⟨b, hb, hc⟩ := h; obtain ⟨b', hb', hc'⟩ := h'
  exact ⟨b + b', by rw [Cochain.comp_add, hb, hb'], by rw [Cochain.comp_add, hc, hc', δ_add]⟩

theorem snake_sub {n : ℤ} {a a' : Cochain S.X₁ I n} {c c' : Cochain S.X₃ I (n + 1)}
    (h : Snake S a c) (h' : Snake S a' c') : Snake S (a - a') (c - c') := by
  obtain ⟨b, hb, hc⟩ := h; obtain ⟨b', hb', hc'⟩ := h'
  exact ⟨b - b', by rw [Cochain.comp_sub, hb, hb'], by rw [Cochain.comp_sub, hc, hc', δ_sub]⟩

variable (hI : ∀ n, Injective (I.X n)) (hS : S.ShortExact)
include hI hS

theorem snake_exists {n : ℤ} (a : Cocycle S.X₁ I n) : ∃ c : Cocycle S.X₃ I (n + 1), Snake S a.1 c.1 := by
  have L := cochain_shortExact_of_injective R I hI S hS
  obtain ⟨b, hb⟩ := (L n).1 a.1
  have h1 : (Cochain.ofHom S.f).comp (δ n (n + 1) b) (zero_add (n + 1)) = 0 := by
    rw [← δ_ofHom_comp', hb]; exact a.δ_eq_zero (n + 1)
  obtain ⟨c, hc⟩ := (L (n + 1)).2.1 _ h1
  have h2 : δ (n + 1) (n + 1 + 1) c = 0 := by
    apply (L (n + 1 + 1)).2.2
    rw [← δ_ofHom_comp', hc, δ_δ]
  exact ⟨Cocycle.mk c (n + 1 + 1) rfl h2, b, hb, hc⟩

theorem snake_bdry {n m : ℤ} (hm : m + 1 = n) {a : Cochain S.X₁ I n} {c : Cochain S.X₃ I (n + 1)}
    (h : Snake S a c) (β : Cochain S.X₁ I m) (hβ : δ m n β = a) :
    ∃ e : Cochain S.X₃ I n, δ n (n + 1) e = c := by
  have L := cochain_shortExact_of_injective R I hI S hS
  obtain ⟨b, hb, hc⟩ := h
  obtain ⟨β₂, hβ₂⟩ := (L m).1 β
  have h1 : (Cochain.ofHom S.f).comp (b - δ m n β₂) (zero_add n) = 0 := by
    rw [Cochain.comp_sub, ← δ_ofHom_comp', hβ₂, hβ, hb, sub_self]
  obtain ⟨e, he⟩ := (L n).2.1 _ h1
  refine ⟨e, ?_⟩
  rw [← sub_eq_zero]
  apply (L (n + 1)).2.2
  rw [Cochain.comp_sub, ← δ_ofHom_comp', he, hc, δ_sub, δ_δ, sub_zero, sub_self]

theorem snake_unique {n : ℤ} {a : Cochain S.X₁ I n} {c c' : Cocycle S.X₃ I (n + 1)}
    (h : Snake S a c.1) (h' : Snake S a c'.1) :
    CohomologyClass.mk c = CohomologyClass.mk c' := by
  have h0 := snake_sub S h h'
  rw [sub_self] at h0
  obtain ⟨e, he⟩ := snake_bdry S hI hS (sub_add_cancel n 1) h0 0 (by simp)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ n rfl]
  exact ⟨e, by rw [he]; rfl⟩

def conn0 (n : ℤ) (a : Cocycle S.X₁ I n) : CohomologyClass S.X₃ I (n + 1) :=
  CohomologyClass.mk (Classical.choose (snake_exists S hI hS a))

theorem etaleSnakeConnectingOnCocycles_eq {n : ℤ} (a : Cocycle S.X₁ I n) (c : Cocycle S.X₃ I (n + 1)) (h : Snake S a.1 c.1) :
    conn0 S hI hS n a = CohomologyClass.mk c :=
  snake_unique S hI hS (Classical.choose_spec (snake_exists S hI hS a)) h

def conn (n : ℤ) : CohomologyClass S.X₁ I n →+ CohomologyClass S.X₃ I (n + 1) :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (conn0 S hI hS n) (fun a a' => by
      obtain ⟨c, hc⟩ := snake_exists S hI hS a
      obtain ⟨c', hc'⟩ := snake_exists S hI hS a'
      rw [etaleSnakeConnectingOnCocycles_eq S hI hS a c hc, etaleSnakeConnectingOnCocycles_eq S hI hS a' c' hc',
        etaleSnakeConnectingOnCocycles_eq S hI hS (a + a') (c + c') (snake_add S hc hc'), CohomologyClass.mk_add]))
    (by
      intro a ha
      rw [mem_coboundaries_iff a (n - 1) (sub_add_cancel n 1)] at ha
      obtain ⟨β, hβ⟩ := ha
      obtain ⟨c, hc⟩ := snake_exists S hI hS a
      obtain ⟨e, he⟩ := snake_bdry S hI hS (sub_add_cancel n 1) hc β hβ
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, etaleSnakeConnectingOnCocycles_eq S hI hS a c hc,
        CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl]
      exact ⟨e, he⟩)

end

end GlobalTheory.EtC.LesFirst

namespace GlobalTheory.EtC


open LesFirst in
theorem longExact_first_of_injective :
    ∀ (R : Type) [CommRing R] (I : Cx R), (∀ n, Injective (I.X n)) → ∃ d : ∀ (S : ShortComplex (Cx R)), S.ShortExact → ∀ n : ℤ, CohomologyClass S.X₁ I n →+ CohomologyClass S.X₃ I (n + 1), (∀ (S : ShortComplex (Cx R)) (hS : S.ShortExact) n, Function.Exact (cpull S.g I n) (cpull S.f I n) ∧ Function.Exact (cpull S.f I n) (d S hS n) ∧ Function.Exact (d S hS n) (cpull S.g I (n + 1))) ∧ ∀ (S S' : ShortComplex (Cx R)) (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') n x, cpull φ.τ₃ I (n + 1) (d S' hS' n x) = d S hS n (cpull φ.τ₁ I n x) := by
  intro R _ I hI
  refine ⟨fun S hS n => conn S hI hS n, fun S hS n => ⟨?_, ?_, ?_⟩, ?_⟩
  · have L := cochain_shortExact_of_injective R I hI S hS
    intro y
    constructor
    · intro hy
      obtain ⟨y, rfl⟩ := y.mk_surjective
      rw [cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (sub_add_cancel n 1)] at hy
      obtain ⟨β, hβ⟩ := hy
      obtain ⟨β₂, hβ₂⟩ := (L (n - 1)).1 β
      have h1 : (Cochain.ofHom S.f).comp (y.1 - δ (n - 1) n β₂) (zero_add n) = 0 := by
        rw [Cochain.comp_sub, ← δ_ofHom_comp', hβ₂, hβ]; exact sub_self _
      obtain ⟨c, hc⟩ := (L n).2.1 _ h1
      have h2 : δ n (n + 1) c = 0 := by
        apply (L (n + 1)).2.2
        rw [← δ_ofHom_comp', hc, δ_sub, δ_δ, y.δ_eq_zero, sub_zero]
      refine ⟨CohomologyClass.mk (Cocycle.mk c (n + 1) rfl h2), ?_⟩
      rw [cpull_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ (n - 1) (sub_add_cancel n 1)]
      refine ⟨-β₂, ?_⟩
      rw [δ_neg]
      change -(δ (n - 1) n β₂) = (Cochain.ofHom S.g).comp c (zero_add n) - y.1
      rw [hc]; abel
    · rintro ⟨x, rfl⟩
      rw [cpull_comp, S.zero, cpull_zero']
  · intro y
    constructor
    · intro hy
      obtain ⟨a, rfl⟩ := y.mk_surjective
      obtain ⟨c, b, hb, hc⟩ := snake_exists S hI hS a
      change conn0 S hI hS n a = 0 at hy
      rw [etaleSnakeConnectingOnCocycles_eq S hI hS a c ⟨b, hb, hc⟩, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ n rfl] at hy
      obtain ⟨e, he⟩ := hy
      have h : δ n (n + 1) (b - (Cochain.ofHom S.g).comp e (zero_add n)) = 0 := by
        rw [δ_sub, δ_ofHom_comp', he, ← hc, sub_self]
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl h), ?_⟩
      rw [cpull_mk]
      refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
      change (Cochain.ofHom S.f).comp (b - (Cochain.ofHom S.g).comp e (zero_add n)) (zero_add n) = a.1
      rw [Cochain.comp_sub, fg_zero, sub_zero, hb]
    · rintro ⟨x, rfl⟩
      obtain ⟨b, rfl⟩ := x.mk_surjective
      change conn0 S hI hS n _ = 0
      rw [etaleSnakeConnectingOnCocycles_eq S hI hS _ 0 ⟨b.1, rfl, by simp⟩, CohomologyClass.mk_zero]
  · intro z
    constructor
    · intro hz
      obtain ⟨c, rfl⟩ := z.mk_surjective
      rw [cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl] at hz
      obtain ⟨β, hβ⟩ := hz
      have h : δ n (n + 1) ((Cochain.ofHom S.f).comp β (zero_add n)) = 0 := by
        rw [δ_ofHom_comp', hβ]; exact fg_zero S c.1
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl h), ?_⟩
      exact etaleSnakeConnectingOnCocycles_eq S hI hS _ c ⟨β, rfl, hβ.symm⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := x.mk_surjective
      obtain ⟨c, hs⟩ := snake_exists S hI hS a
      change cpull S.g I (n + 1) (conn0 S hI hS n a) = 0
      rw [etaleSnakeConnectingOnCocycles_eq S hI hS a c hs, cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl]
      obtain ⟨b, hb, hc⟩ := hs
      exact ⟨b, hc.symm⟩
  · intro S S' hS hS' φ n x
    obtain ⟨a, rfl⟩ := x.mk_surjective
    obtain ⟨c, b, hb, hc⟩ := snake_exists S' hI hS' a
    change cpull φ.τ₃ I (n + 1) (conn0 S' hI hS' n a) = conn0 S hI hS n _
    rw [etaleSnakeConnectingOnCocycles_eq S' hI hS' a c ⟨b, hb, hc⟩, cpull_mk,
      etaleSnakeConnectingOnCocycles_eq S hI hS _ _ ⟨(Cochain.ofHom φ.τ₂).comp b (zero_add n), ?_, ?_⟩]
    · change _ = (Cochain.ofHom φ.τ₁).comp a.1 (zero_add n)
      rw [ofHom_comp_comp, ← φ.comm₁₂, ← ofHom_comp_comp, hb]
    · change (Cochain.ofHom S.g).comp ((Cochain.ofHom φ.τ₃).comp c.1 (zero_add (n + 1))) (zero_add (n + 1)) = _
      rw [ofHom_comp_comp, ← φ.comm₂₃, ← ofHom_comp_comp, hc, δ_ofHom_comp']

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorial
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ZcFun

variable {R : Type} [CommRing R]

theorem cpull_id (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpull (𝟙 K) I n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem cpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem cpull_cpush {K L I J : Cx R} (f : K ⟶ L) (g : I ⟶ J) (n : ℤ) (x : CohomologyClass L I n) :
    cpull f J n (cpush L g n x) = cpush K g n (cpull f I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem cpull_homotopy {K L : Cx R} {f g : K ⟶ L} (h : Homotopy f g) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    cpull f I n x = cpull g I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g h
  change CohomologyClass.mk _ = CohomologyClass.mk _
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • z.comp x.1 (by omega), ?_⟩
  rw [δ_units_smul, δ_comp z x.1 (by omega) 0 (n + 1) n (by omega) (by omega) (by omega)]
  simp [zcomp, hz, Cochain.add_comp, smul_smul]

theorem main : ∀ (R : Type) [CommRing R] , (∀ (K I : Cx R) (n : ℤ) x, cpull (𝟙 K) I n x = x ∧ cpush K (𝟙 I) n x = x) ∧ (∀ {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) x, cpull (f ≫ g) I n x = cpull f I n (cpull g I n x)) ∧ (∀ (K : Cx R) {I J M : Cx R} (f : I ⟶ J) (g : J ⟶ M) (n : ℤ) x, cpush K (f ≫ g) n x = cpush K g n (cpush K f n x)) ∧ (∀ {K L I J : Cx R} (f : K ⟶ L) (g : I ⟶ J) (n : ℤ) x, cpull f J n (cpush L g n x) = cpush K g n (cpull f I n x)) ∧ (∀ {K L : Cx R} (f g : K ⟶ L), Nonempty (Homotopy f g) → ∀ (I : Cx R) (n : ℤ), cpull f I n = cpull g I n ∧ cpush I f n = cpush I g n) := by
  intro R _
  refine ⟨fun K I n x => ⟨cpull_id K I n x, InjResCmp.cpush_id K I n x⟩, fun f g I n x => cpull_comp f g I n x,
    fun K _ _ _ f g n x => InjResCmp.cpush_comp K f g n x, fun f g n x => cpull_cpush f g n x, ?_⟩
  rintro K L f g ⟨h⟩ I n
  exact ⟨AddMonoidHom.ext fun x => cpull_homotopy h I n x, AddMonoidHom.ext fun x => InjResCmp.cpush_homotopy I h n x⟩

end GlobalTheory.EtC.ZcFun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureFiniteTypeOfCharZero
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem integralClosure_finiteType_of_charZero :
    ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K]
      [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F),
      AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F],
      A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K),
      B = (integralClosure A K).restrictScalars k → Algebra.FiniteType k B := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB
  subst hB

  have e : MvPolynomial (Fin d) k ≃ₐ[k] A := by
    subst hA; exact hu.aevalEquiv
  have hAft : Algebra.FiniteType k A := Algebra.FiniteType.equiv inferInstance e
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  have : Algebra.IsSeparable F K := inferInstance
  set_option synthInstance.maxHeartbeats 200000 in
  have : Module.Finite A (integralClosure A K) := IsIntegralClosure.finite A F K (integralClosure A K)
  have : Algebra.FiniteType A (integralClosure A K) := inferInstance
  have : Algebra.FiniteType k (integralClosure A K) := Algebra.FiniteType.trans hAft this
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightEqOneOfLiesOver
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem integralClosure_height_eq_one_of_liesOver : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (A : Subalgebra k F) [IsFractionRing A F] (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1 := by
  intro k F K _ _ _ _ _ _ _ _ A _ B hB p hp hp1 Q hQ hlo

  have hmem : ∀ a : A, algebraMap F K (a : F) ∈ B := by
    intro a
    rw [hB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (R := A) (A := K) (x := a)
  let f : A →+* B := ((algebraMap F K).comp A.val.toRingHom).codRestrict B hmem
  letI : Algebra A B := f.toAlgebra
  have hf : ∀ a : A, ((algebraMap A B a : B) : K) = algebraMap F K (a : F) := fun _ => rfl

  let φ : B →ₐ[A] K :=
    { toRingHom := B.val.toRingHom
      commutes' := fun a => rfl }
  have hint : Algebra.IsIntegral A B := by
    refine ⟨fun b => ?_⟩
    have key : ∀ x : K, x ∈ B → x ∈ integralClosure A K := by
      intro x hx
      rw [hB, Subalgebra.mem_restrictScalars] at hx
      exact hx
    have hb : (b : K) ∈ integralClosure A K := key b b.2
    rw [← isIntegral_algHom_iff φ Subtype.val_injective]
    exact hb

  have hcomap : Q.comap (algebraMap A B) = p := by
    ext a
    exact hlo a (algebraMap A B a) (hf a)
  haveI := hp
  haveI := hQ
  have hpne : p ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hp1
  apply le_antisymm
  · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by rfl, Ideal.height_le_iff]
    intro Q' hQ' hlt
    haveI := hQ'
    by_contra hge
    have hQ'ne : Q' ≠ ⊥ := by
      intro h
      apply hge
      rw [h, Ideal.height_bot]
      norm_num
    have h1 : Q'.comap (algebraMap A B) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot A hQ'ne
    have h2 : Q'.comap (algebraMap A B) < p := hcomap ▸ Ideal.IsIntegral.comap_lt_comap hlt
    haveI : (Q'.comap (algebraMap A B)).IsPrime := Ideal.comap_isPrime _ _
    have h3 := Ideal.height_add_one_le_of_lt_of_isPrime h2
    have h4 : 1 ≤ (Q'.comap (algebraMap A B)).height := by
      rw [Order.one_le_iff_pos, pos_iff_ne_zero]
      exact fun h => h1 (Ideal.height_eq_zero_iff_eq_bot.mp h)
    rw [hp1] at h3
    have : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add h4 le_rfl).trans h3
    norm_num at this
  · rw [Order.one_le_iff_pos, pos_iff_ne_zero]
    intro h
    rw [Ideal.height_eq_zero_iff_eq_bot] at h
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
    have : algebraMap A B a ∈ Q := by rw [← Ideal.mem_comap, hcomap]; exact ha
    rw [h, Ideal.mem_bot] at this
    apply ha0
    have := congrArg (fun x : B => (x : K)) this
    simp only [hf, ZeroMemClass.coe_zero] at this
    exact Subtype.ext ((algebraMap F K).injective (this.trans (map_zero _).symm))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightOneUniformizerRamificationA
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem exists_localUniformizer_and_order {B : Type} [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [IsIntegrallyClosed B] (Q : Ideal B) [Q.IsPrime] (hQ : Q.height = 1)
    (x : B) (hx0 : x ≠ 0) (hxQ : x ∈ Q) :
    ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧
      (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ r * x = a * s ^ e) := by
  let L := Localization.AtPrime Q
  haveI : IsDiscreteValuationRing L := isDiscreteValuationRing_of_height_eq_one Q hQ L
  have hle : Q.primeCompl ≤ nonZeroDivisors B := Q.primeCompl_le_nonZeroDivisors
  have hinj : Function.Injective (algebraMap B L) := IsLocalization.injective L hle
  have hcomap : (IsLocalRing.maximalIdeal L).comap (algebraMap B L) = Q :=
    IsLocalization.AtPrime.under_maximalIdeal L Q
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible L
  obtain ⟨⟨s, r0⟩, hs⟩ := IsLocalization.surj Q.primeCompl ϖ
  simp only at hs
  have hu0 : IsUnit (algebraMap B L r0) := IsLocalization.map_units L r0
  have hsirr : Irreducible (algebraMap B L s) := by
    rw [← hs]; exact (irreducible_mul_isUnit hu0).mpr hϖ
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hsirr
  have hsQ : s ∈ Q := by
    rw [← hcomap, Ideal.mem_comap, hmax]; exact Ideal.subset_span rfl
  refine ⟨s, ?_⟩
  have hxL : algebraMap B L x ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap B L)]; exact fun h => hx0 (hinj h)
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxL hsirr
  have hxm : algebraMap B L x ∈ IsLocalRing.maximalIdeal L := by
    rw [← Ideal.mem_comap, hcomap]; exact hxQ
  refine ⟨n, ?_, hsQ, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h, pow_zero, mul_one] at hw
      exact (IsLocalRing.mem_maximalIdeal _).mp hxm (hw ▸ w.isUnit)
    · exact h
  · intro y hy
    have hym : algebraMap B L y ∈ Ideal.span {algebraMap B L s} := by
      rw [← hmax, ← Ideal.mem_comap, hcomap]; exact hy
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hym
    obtain ⟨⟨c, r⟩, hcr⟩ := IsLocalization.surj Q.primeCompl z
    simp only at hcr
    refine ⟨c, r, r.2, hinj ?_⟩
    rw [map_mul, map_mul, ← hz, ← hcr]; ring
  · obtain ⟨⟨a, r⟩, har⟩ := IsLocalization.surj Q.primeCompl (w : L)
    simp only at har
    have hau : IsUnit (algebraMap B L a) := by
      rw [← har]; exact w.isUnit.mul (IsLocalization.map_units L r)
    refine ⟨a, r, ?_, r.2, hinj ?_⟩
    · intro haQ
      have : algebraMap B L a ∈ IsLocalRing.maximalIdeal L := by
        rw [← Ideal.mem_comap, hcomap]; exact haQ
      exact (IsLocalRing.mem_maximalIdeal _).mp this hau
    · rw [map_mul, map_mul, map_pow, ← har, hw]; ring

theorem integralClosure_height_one_uniformizer_ramification :
    ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → ∀ t : A, Irreducible t → p = Ideal.span {t} → ∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧ (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB p _ t ht hpt Q _ hQ hlie
  have hN : IsNoetherianRing A := by
    subst hA
    exact isNoetherianRing_of_ringEquiv _ hu.aevalEquiv.toRingEquiv
  have hI : IsIntegrallyClosed A := by
    subst hA
    have : IsIntegrallyClosed (MvPolynomial (Fin d) k) :=
      UniqueFactorizationMonoid.instIsIntegrallyClosed
    exact IsIntegrallyClosed.of_equiv hu.aevalEquiv.toRingEquiv
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  subst hB
  have hNB : IsNoetherianRing (integralClosure A K) := by
    letI : IsNoetherianRing A := hN
    letI : IsIntegrallyClosed A := hI
    exact integralClosure.isNoetherianRing (A := A) (K := F) (L := K)
  have hIB : IsIntegrallyClosed (integralClosure A K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension F
  haveI : IsNoetherianRing ((integralClosure A K).restrictScalars k) := hNB
  haveI : IsIntegrallyClosed ((integralClosure A K).restrictScalars k) := hIB
  have hmem : algebraMap F K (t : F) ∈ (integralClosure A K).restrictScalars k := by
    rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (x := t)
  let x : (integralClosure A K).restrictScalars k := ⟨_, hmem⟩
  have hxQ : x ∈ Q := (hlie t x rfl).mpr (hpt ▸ Ideal.subset_span rfl)
  have hx0 : x ≠ 0 := by
    intro h
    have h' : algebraMap F K (t : F) = 0 := congrArg Subtype.val h
    rw [map_eq_zero_iff _ (algebraMap F K).injective, ZeroMemClass.coe_eq_zero] at h'
    exact ht.ne_zero h'
  obtain ⟨s, e, he, hs, hgen, a, r, ha, hr, hrx⟩ := exists_localUniformizer_and_order Q hQ x hx0 hxQ
  refine ⟨s, e, he, hs, hgen, a, r, ha, hr, ?_⟩
  have := congrArg Subtype.val hrx
  simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerFixesOfLocalVacuumStatement
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_fixes_of_local_vacuum' : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X) (T : M →ₗ[ℂ] M), (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = e) → ∀ P : X →ₗ[R] X, (∀ x y, γ (P x) y = γ x (P y)) → (∀ a ∈ A, P a ∈ A) → (∀ x, φ (x - P x) = x - P x) → ∀ m : M, (∀ a ∈ A, W (P a) m = m) → T m = m := by
  first | exact @GlobalTheory.FinWeil.intertwiner_fixes_of_local_vacuum | exact GlobalTheory.FinWeil.intertwiner_fixes_of_local_vacuum | (intros; apply GlobalTheory.FinWeil.intertwiner_fixes_of_local_vacuum <;> assumption)
end

