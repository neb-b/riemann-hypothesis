module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverLen
section
namespace Formalism.L2.NCov

open Module

section

variable {R R' M M' : Type*} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R' M']

theorem length_eq_of_bijective (φ : R ≃+* R') (f : M →ₛₗ[(φ : R →+* R')] M') (hf : Function.Bijective f) :
    Module.length R' M' = Module.length R M := by
  letI := RingHomInvPair.of_ringEquiv φ
  letI := RingHomInvPair.symm (φ : R →+* R') (φ.symm : R' →+* R)
  let e : M ≃ₛₗ[(φ : R →+* R')] M' := LinearEquiv.ofBijective f hf
  rw [Module.length_eq_height, Module.length_eq_height,
    ← Order.height_orderIso (Submodule.orderIsoMapComap e) ⊤, OrderIso.map_top]

private theorem length_quotient_eq_of_bijective_semilinear (φ : R ≃+* R') (f : M →ₛₗ[(φ : R →+* R')] M')
    (hf : Function.Bijective f) (q : Submodule R M) (q' : Submodule R' M')
    (h : ∀ x, f x ∈ q' ↔ x ∈ q) :
    Module.length R' (M' ⧸ q') = Module.length R (M ⧸ q) := by
  let g : (M ⧸ q) →ₛₗ[(φ : R →+* R')] (M' ⧸ q') := q.mapQ q' f (fun x hx => (h x).2 hx)
  refine length_eq_of_bijective φ g ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective q y
    have hy' : (Submodule.Quotient.mk (f a) : M' ⧸ q') = 0 := hy
    rw [Submodule.Quotient.mk_eq_zero] at hy'
    rw [Submodule.Quotient.mk_eq_zero]
    exact (h a).1 hy'
  · intro y
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective q' y
    obtain ⟨a, rfl⟩ := hf.2 b
    exact ⟨Submodule.Quotient.mk a, rfl⟩

theorem length_quot_map (φ : R ≃+* R') (f : M →ₛₗ[(φ : R →+* R')] M') (hf : Function.Injective f)
    (p q : Submodule R M) :
    haveI := RingHomInvPair.of_ringEquiv φ
    Module.length R' (↥(p.map f) ⧸ (q.map f).comap (p.map f).subtype) =
      Module.length R (↥p ⧸ q.comap p.subtype) := by
  letI := RingHomInvPair.of_ringEquiv φ
  let g : ↥p →ₛₗ[(φ : R →+* R')] ↥(p.map f) :=
    { toFun := fun x => ⟨f x, Submodule.mem_map_of_mem x.2⟩
      map_add' := fun x y => Subtype.ext (map_add f (x : M) (y : M))
      map_smul' := fun r x => Subtype.ext (f.map_smulₛₗ r (x : M)) }
  refine length_quotient_eq_of_bijective_semilinear φ g ⟨?_, ?_⟩ _ _ ?_
  · intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  · intro x
    show f x ∈ q.map f ↔ (x : M) ∈ q
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx
      rw [← hf hyx]
      exact hy
    · intro hx
      exact Submodule.mem_map_of_mem hx

theorem length_quot_natCast (φ : R ≃+* R') (n : ℕ) :
    Module.length R' (R' ⧸ Ideal.span {(n : R')}) = Module.length R (R ⧸ Ideal.span {(n : R)}) := by
  let F : R →ₛₗ[(φ : R →+* R')] R' :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun r x => by simp only [smul_eq_mul, map_mul, RingEquiv.coe_toRingHom] }
  refine length_quotient_eq_of_bijective_semilinear φ F φ.bijective _ _ ?_
  intro x
  show φ x ∈ Ideal.span {(n : R')} ↔ x ∈ Ideal.span {(n : R)}
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨φ.symm c, by apply φ.injective; simp [hc]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨φ c, by simp⟩

end

end Formalism.L2.NCov
end

-- bundled from Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverPoly
section
namespace Formalism.L2.NCov

open Module

variable {K₁ K₂ V₁ V₂ : Type*} [Field K₁] [Field K₂] [AddCommGroup V₁] [Module K₁ V₁] [AddCommGroup V₂]
  [Module K₂ V₂]

theorem repr_transport (σ : K₁ →+* K₂) (ι : V₁ →ₛₗ[σ] V₂) {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n K₁ V₁) (hli : LinearIndependent K₂ (ι ∘ b))
    (hsp : Submodule.span K₂ (Set.range (ι ∘ b)) = ⊤) (x : V₁) (r : n) :
    (Module.Basis.mk hli hsp.ge).repr (ι x) r = σ (b.repr x r) := by
  have hx : ι x = ∑ i, σ (b.repr x i) • (Module.Basis.mk hli hsp.ge) i := by
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.mk_apply, Function.comp_apply]
    first
      | exact LinearMap.map_smulₛₗ ι (b.repr x i) (b i)
      | exact map_smulₛₗ ι (b.repr x i) (b i)
      | simp
  rw [hx, Module.Basis.repr_sum_self]

theorem charpoly_transport_basis [Module.Finite K₁ V₁] [Module.Finite K₂ V₂] (σ : K₁ →+* K₂) (ι : V₁ →ₛₗ[σ] V₂) {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n K₁ V₁) (hli : LinearIndependent K₂ (ι ∘ b))
    (hsp : Submodule.span K₂ (Set.range (ι ∘ b)) = ⊤) (A₁ : Module.End K₁ V₁) (A₂ : Module.End K₂ V₂)
    (h : ∀ a, A₂ (ι (b a)) = ι (A₁ (b a))) :
    A₂.charpoly = A₁.charpoly.map σ := by
  have hM : LinearMap.toMatrix (Module.Basis.mk hli hsp.ge) (Module.Basis.mk hli hsp.ge) A₂ =
      (LinearMap.toMatrix b b A₁).map σ := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
      Module.Basis.mk_apply, Function.comp_apply, h j, repr_transport σ ι b hli hsp]
  rw [← LinearMap.charpoly_toMatrix A₂ (Module.Basis.mk hli hsp.ge), hM, Matrix.charpoly_map,
    LinearMap.charpoly_toMatrix]

theorem charpoly_transport [Module.Finite K₁ V₁] [Module.Finite K₂ V₂] (σ : K₁ →+* K₂) (ι : V₁ →ₛₗ[σ] V₂) {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n K₁ V₁) (hli : LinearIndependent K₂ (ι ∘ b))
    (hsp : Submodule.span K₂ (Set.range (ι ∘ b)) = ⊤) (A₁ : Module.End K₁ V₁) (A₂ : Module.End K₂ V₂)
    (h : ∀ x, A₂ (ι x) = ι (A₁ x)) :
    A₂.charpoly = A₁.charpoly.map σ :=
  charpoly_transport_basis σ ι b hli hsp A₁ A₂ fun a => h (b a)

end Formalism.L2.NCov
end

-- bundled from Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverVal
section
namespace Formalism.L2.NCov

open Polynomial

section Val

variable {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))

theorem nonneg_of_isIntegral {y : F} (hy : IsIntegral ℤ y) : 0 ≤ v y := by

  let w := AddValuation.toValuation v
  have h1 : IsIntegral w.integer y := IsIntegral.tower_top hy
  have h2 := (Valuation.integer.integers w).mem_of_integral h1
  exact h2

theorem withTop_add_pos {x y : WithTop ℤ} (hx : 0 ≤ x) (hy : 0 < y) : 0 < x + y := by
  induction x using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    induction y using WithTop.recTopCoe with
    | top => simp
    | coe b =>
      norm_cast at hx hy ⊢
      omega

theorem val_prime_eq_zero {l p : ℕ} (hl : l.Prime) (hp : p.Prime) (hne : p ≠ l) (hvl : 0 < v (l : F)) :
    v (p : F) = 0 := by
  have hI : ∀ a : ℤ, 0 ≤ v (a : F) := fun a =>
    nonneg_of_isIntegral v (by simpa using (isIntegral_algebraMap (R := ℤ) (A := F) (x := a)))
  have hp0 : 0 ≤ v (p : F) := by simpa using hI p

  have hcop : IsCoprime (p : ℤ) (l : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hl).mpr hne)
  obtain ⟨a, b, hab⟩ := hcop
  have hF : (a : F) * (p : F) + (b : F) * (l : F) = 1 := by
    have := congrArg (fun z : ℤ => (z : F)) hab
    push_cast at this
    exact this
  by_contra hne0
  have hpos : 0 < v (p : F) := lt_of_le_of_ne hp0 (Ne.symm hne0)
  have h1 : 0 < v ((a : F) * (p : F)) := by
    rw [AddValuation.map_mul]; exact withTop_add_pos (hI a) hpos
  have h2 : 0 < v ((b : F) * (l : F)) := by
    rw [AddValuation.map_mul]; exact withTop_add_pos (hI b) hvl
  have h3 := lt_of_lt_of_le (lt_min h1 h2) (v.map_add _ _)
  rw [hF, AddValuation.map_one] at h3
  exact lt_irrefl _ h3

end Val

section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem mem_range_of_isRoot (P : (FractionRing O)[X]) (hm : P.Monic)
    (hc : ∀ i, P.coeff i ∈ (algebraMap O (FractionRing O)).range) {μ : FractionRing O} (hμ : P.IsRoot μ) :
    μ ∈ (algebraMap O (FractionRing O)).range := by
  have hlift : P ∈ Polynomial.lifts (algebraMap O (FractionRing O)) :=
    (Polynomial.lifts_iff_coeff_lifts P).mpr (fun n => hc n)
  obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hm
  have hint : IsIntegral O μ := ⟨Q, hQm, by rw [← Polynomial.eval_map, hQ]; exact hμ⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨y, hy⟩

end DVR

section Away

variable {R : Type*} [CommRing R]

variable {q : R}

end Away

end Formalism.L2.NCov
end

