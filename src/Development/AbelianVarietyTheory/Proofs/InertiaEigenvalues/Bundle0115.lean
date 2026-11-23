module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0006
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfSeparable
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.PairClass

theorem exists_aeval_eq_of_separable {F A : Type} [Field F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (a : A) (hs : (LinearMap.mulLeft F a).charpoly.Separable) (y : A) :
    ∃ q : F[X], y = aeval a q := by
  obtain ⟨w, hw⟩ := Formalism.IrreducibleCountingLemmas.Z.base_change_cyclic_vector F A (LinearMap.mulLeft F a) hs
  have key : ∀ (p : F[X]) (z : A), aeval (LinearMap.mulLeft F a) p z = aeval a p * z := by
    intro p z
    have h1 : aeval (Algebra.lmul F A a) p = Algebra.lmul F A (aeval a p) :=
      aeval_algHom_apply (Algebra.lmul F A) a p
    have h2 : Algebra.lmul F A a = LinearMap.mulLeft F a := rfl
    rw [← h2, h1]
    rfl
  obtain ⟨p1, hp1⟩ := hw 1
  obtain ⟨p2, hp2⟩ := hw (w * w)
  obtain ⟨p3, hp3⟩ := hw y
  rw [key] at hp1 hp2 hp3
  have hw2 : w = aeval a p2 := by
    calc w = w * w * aeval a p1 := by rw [mul_assoc, mul_comm w (aeval a p1), hp1, mul_one]
      _ = aeval a p2 * (aeval a p1 * w) := by rw [← hp2]; ring
      _ = aeval a p2 := by rw [hp1, mul_one]
  exact ⟨p3 * p2, by rw [← hp3, map_mul, hw2]⟩

theorem aeval_mulLeft_apply {F A : Type} [Field F] [CommRing A] [Algebra F A] (a : A) (p : F[X]) (z : A) :
    aeval (LinearMap.mulLeft F a) p z = aeval a p * z := by
  have h1 : aeval (Algebra.lmul F A a) p = Algebra.lmul F A (aeval a p) :=
    aeval_algHom_apply (Algebra.lmul F A) a p
  have h2 : Algebra.lmul F A a = LinearMap.mulLeft F a := rfl
  rw [← h2, h1]
  rfl

theorem trace_nondeg (F A : Type) [Field F] [CharZero F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (a : A) (hs : (LinearMap.mulLeft F a).charpoly.Separable) (x : A)
    (hx : ∀ y, Algebra.trace F A (x * y) = 0) : x = 0 := by
  classical
  let b := Module.finBasis F A
  have hM : IsNilpotent (Algebra.leftMulMatrix b x) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [pow_succ', hx]
  obtain ⟨k, hk⟩ := hM
  have hxk : x ^ k = 0 := by
    rw [← map_pow] at hk
    exact Algebra.leftMulMatrix_injective b (by rw [hk, map_zero])
  obtain ⟨q, rfl⟩ := exists_aeval_eq_of_separable a hs x
  obtain ⟨e₀, -, he⟩ := Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq (LinearMap.mulLeft F a) hs _ dvd_rfl
  have h1 : (LinearMap.mulLeft F a).charpoly ∣ q ^ (k + 1) :=
    he _ (by rw [aeval_mulLeft_apply, map_pow, pow_succ, hxk, zero_mul, zero_mul])
  obtain ⟨r, hr⟩ := (Squarefree.dvd_pow_iff_dvd hs.squarefree (Nat.succ_ne_zero k)).1 h1
  have h3 : aeval (LinearMap.mulLeft F a) q = 0 := by
    rw [hr, map_mul, LinearMap.aeval_self_charpoly, zero_mul]
  have h4 := LinearMap.congr_fun h3 1
  rwa [aeval_mulLeft_apply, mul_one] at h4

theorem trace_σ (K : UQ) (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
  classical
  have σsm : ∀ (r : K.E) (y : B.A), B.σ (r • y) = K.c r • B.σ y := by
    intro r y
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  let b := Module.finBasis K.E B.A
  have hσsum : ∀ y : B.A, B.σ y = ∑ i, K.c (b.repr y i) • B.σ (b i) := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [σsm]
  have hli : LinearIndependent K.E (fun i => B.σ (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro r hr i
    have h1 := congrArg B.σ hr
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h1
    simp only [σsm, B.σ_σ] at h1
    have h2 := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ h1 i
    have := congrArg K.c h2
    rwa [K.c_c, map_zero] at this
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range fun i => B.σ (b i)) := by
    intro y _
    rw [← B.σ_σ y, hσsum (B.σ y)]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = B.σ (b i) := fun i => Module.Basis.mk_apply hli hsp i
  have hrepr : ∀ (y : B.A) (i), b'.repr (B.σ y) i = K.c (b.repr y i) := by
    intro y i
    have : B.σ y = ∑ j, K.c (b.repr y j) • b' j := by
      rw [hσsum y]; simp only [hb']
    rw [this, b'.repr_sum_self]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hb', ← map_mul, hrepr]

theorem exists_degreeLT_equiv (F V : Type) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (f : V →ₗ[F] V) (P : F[X]) (hP : f.charpoly = P) (hs : P.Separable) :
    ∃ (e₀ : V) (ψ : degreeLT F P.natDegree ≃ₗ[F] V), ∀ p, ψ p = aeval f (p : F[X]) e₀ := by
  subst hP
  obtain ⟨e₀, -, he⟩ := Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq f hs f.charpoly dvd_rfl
  let ψ : degreeLT F f.charpoly.natDegree →ₗ[F] V :=
    ((LinearMap.applyₗ e₀) ∘ₗ (aeval f).toLinearMap) ∘ₗ (degreeLT F _).subtype
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    have h1 : f.charpoly ∣ (q : F[X]) := he _ hq
    have h2 : (q : F[X]).degree < f.charpoly.degree := by
      rw [degree_eq_natDegree f.charpoly_monic.ne_zero]
      exact mem_degreeLT.1 q.2
    exact Subtype.ext (eq_zero_of_dvd_of_degree_lt h1 h2)
  have : FiniteDimensional F (degreeLT F f.charpoly.natDegree) :=
    (degreeLTEquiv F _).symm.finiteDimensional
  have hdim : Module.finrank F (degreeLT F f.charpoly.natDegree) = Module.finrank F V := by
    rw [(degreeLTEquiv F _).finrank_eq, Module.finrank_fin_fun, LinearMap.charpoly_natDegree]
  exact ⟨e₀, LinearMap.linearEquivOfInjective ψ hinj hdim, fun p => rfl⟩

theorem exists_intertwine (F V W : Type) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] (f : V →ₗ[F] V) (g : W →ₗ[F] W)
    (hs : f.charpoly.Separable) (he : f.charpoly = g.charpoly) : ∃ e : V ≃ₗ[F] W, ∀ v, e (f v) = g (e v) := by
  set P := f.charpoly with hPdef
  have hP : P.Monic := f.charpoly_monic
  obtain ⟨e₁, ψ₁, hψ₁⟩ := exists_degreeLT_equiv F V f P rfl hs
  obtain ⟨e₂, ψ₂, hψ₂⟩ := exists_degreeLT_equiv F W g P he.symm hs
  refine ⟨ψ₁.symm.trans ψ₂, fun v => ?_⟩
  obtain ⟨p, rfl⟩ := ψ₁.surjective v
  have hm : (X * (p : F[X])) %ₘ P ∈ degreeLT F P.natDegree := by
    rw [mem_degreeLT, ← degree_eq_natDegree hP.ne_zero]
    exact degree_modByMonic_lt _ hP
  have h1 : f (ψ₁ p) = ψ₁ ⟨_, hm⟩ := by
    rw [hψ₁, hψ₁, aeval_modByMonic_eq_self_of_root (LinearMap.aeval_self_charpoly f), map_mul, aeval_X,
      Module.End.mul_apply]
  have h2 : ψ₂ ⟨_, hm⟩ = g (ψ₂ p) := by
    rw [hψ₂, hψ₂, aeval_modByMonic_eq_self_of_root (show aeval g P = 0 by rw [he]; exact LinearMap.aeval_self_charpoly g),
      map_mul, aeval_X, Module.End.mul_apply]
  rw [h1, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, h2, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

theorem exists_herm_model : ∀ (K : UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V] [Module.Finite K.E V] (h : V → V → K.E), (∀ x y z, h (x + y) z = h x z + h y z) → (∀ (c : K.E) x z, h (c • x) z = c * h x z) → (∀ x y, h y x = K.c (h x y)) → (∀ y, (∀ z, h y z = 0) → y = 0) → ∀ (B : InvAlg K) (g : V →ₗ[K.E] V), B.P.Separable → g.charpoly = B.P → ((B.g * B.σ B.g = 1 ∧ ∀ y z, h (g y) (g z) = h y z) ∨ (B.σ B.g = B.g ∧ ∀ y z, h (g y) z = h y (g z))) → ∃ (x : B.Aˣ) (e : B.A ≃ₗ[K.E] V), B.σ (x : B.A) = x ∧ (∀ y, e (B.g * y) = g (e y)) ∧ ∀ y z, h (e y) (e z) = B.herm x y z := by
  intro K V _ _ _ _ _ h hadd hsm hherm hnd B g hsep hchar hcase
  have hsep' : (LinearMap.mulLeft K.E B.g).charpoly.Separable := hsep
  obtain ⟨e, he⟩ := exists_intertwine K.E B.A V (LinearMap.mulLeft K.E B.g) g hsep hchar.symm
  have he' : ∀ y, e (B.g * y) = g (e y) := fun y => he y
  have hadd2 : ∀ x y z, h x (y + z) = h x y + h x z := by
    intro x y z
    rw [hherm (y + z) x, hadd, map_add (f := _), ← hherm y x, ← hherm z x]
  have hsm2 : ∀ (c : K.E) x z, h x (c • z) = K.c c * h x z := by
    intro c x z
    rw [hherm (c • z) x, hsm, map_mul, ← hherm z x]
  let S : B.A → Prop := fun a => ∀ y z, h (e (a * y)) (e z) = h (e y) (e (B.σ a * z))
  have Salg : ∀ c : K.E, S (algebraMap K.E B.A c) := by
    intro c y z
    rw [B.σ_alg, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul, hsm, hsm2, K.c_c]
  have Sg : S B.g := by
    intro y z
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hz : z = B.g * (B.σ B.g * z) := by rw [← mul_assoc, h1, one_mul]
      conv_lhs => rw [hz]
      rw [he', he', h2]
    · rw [h1, he', he', h2]
  have Sadd : ∀ a b, S a → S b → S (a + b) := by
    intro a b ha hb y z
    rw [add_mul, map_add (f := _), hadd, ha, hb, map_add (f := _), add_mul, map_add (f := _), hadd2]
  have Smul : ∀ a b, S a → S b → S (a * b) := by
    intro a b ha hb y z
    rw [mul_assoc, ha, hb, show B.σ b * (B.σ a * z) = B.σ (a * b) * z by rw [map_mul B.σ]; ring]
  have Spoly : ∀ q : K.E[X], S (aeval B.g q) := by
    intro q
    induction q using Polynomial.induction_on with
    | C c => rw [aeval_C]; exact Salg c
    | add p q hp hq => rw [map_add (f := _)]; exact Sadd _ _ hp hq
    | monomial n c ih =>
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]; exact Smul _ _ ih Sg
  have Sall : ∀ a, S a := by
    intro a
    obtain ⟨q, rfl⟩ := exists_aeval_eq_of_separable B.g hsep' a
    exact Spoly q

  let φ : Module.Dual K.E B.A :=
    { toFun := fun y => h (e y) (e 1)
      map_add' := fun y z => by rw [map_add (f := _), hadd]
      map_smul' := fun c y => by rw [map_smul, hsm]; rfl }
  have hinj : Function.Injective (Algebra.traceForm K.E B.A) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact trace_nondeg K.E B.A B.g hsep' x fun y => by
      have := LinearMap.congr_fun hx y
      rwa [Algebra.traceForm_apply] at this
  have hsurj : Function.Surjective (Algebra.traceForm K.E B.A) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨x, hx⟩ := hsurj φ
  have hxy : ∀ y, Algebra.trace K.E B.A (x * y) = h (e y) (e 1) := fun y => by
    rw [← Algebra.traceForm_apply, hx]; rfl
  have hrep : ∀ y z, h (e y) (e z) = Algebra.trace K.E B.A (x * y * B.σ z) := by
    intro y z
    have := Sall (B.σ z) y 1
    rw [B.σ_σ, mul_one] at this
    rw [← this, ← hxy]
    congr 1
    ring
  have hfix : B.σ x = x := by
    have h0 := trace_nondeg K.E B.A B.g hsep' (B.σ x - x) fun y => by
      have h1 : Algebra.trace K.E B.A (B.σ x * y) = K.c (Algebra.trace K.E B.A (x * B.σ y)) := by
        rw [← trace_σ, map_mul B.σ x (B.σ y), B.σ_σ]
      have h2 : Algebra.trace K.E B.A (x * B.σ y) = h (e 1) (e y) := by
        rw [hrep]; ring_nf
      rw [sub_mul, map_sub, h1, h2, hherm (e y) (e 1), K.c_c, hxy, sub_self]
    exact sub_eq_zero.1 h0
  have hunit : IsUnit x := by
    have hi : Function.Injective (LinearMap.mulLeft K.E x) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      have hy' : x * y = 0 := hy
      apply e.injective
      rw [map_zero]
      apply hnd
      intro v
      rw [← e.apply_symm_apply v, hrep, hy', zero_mul, map_zero]
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hi) 1
    exact IsUnit.of_mul_eq_one y hy
  exact ⟨hunit.unit, e, hfix, he', fun y z => hrep y z⟩

end GlobalTheory.UnitLemma.PairClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraMapSubEqSumConjugates
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace GlobalTheory

theorem exists_algebraMap_sub_eq_sum_conjugates : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (y : Ω), ∃ (e : E) (s : Finset Ω), (∀ x ∈ s, x ≠ y ∧ ∃ σ : G E Ω, σ y = x) ∧ algebraMap E Ω e - y = ∑ x ∈ s, x := by
  intro E Ω _ _ _ _ _ y
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : Normal E Ω := IsAlgClosure.normal E Ω
  have hy : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  set p := minpoly E y with hp
  set q := p.map (algebraMap E Ω) with hq
  have hirr : Irreducible p := minpoly.irreducible hy
  have hmon : p.Monic := minpoly.monic hy
  have hsep : q.Separable := Polynomial.Separable.map (Algebra.IsSeparable.isSeparable E y : p.Separable)
  have hnd : q.roots.Nodup := nodup_roots hsep
  have hspl : q.Splits := IsAlgClosed.splits q
  have hsum : q.nextCoeff = -q.roots.sum := hspl.nextCoeff_eq_neg_sum_roots_of_monic (hmon.map _)
  have hq0 : q ≠ 0 := (hmon.map _).ne_zero
  have hyr : y ∈ q.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot, eval_map_algebraMap]
    exact minpoly.aeval E y
  refine ⟨-p.nextCoeff, q.roots.toFinset.erase y, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxy, hxr⟩ := Finset.mem_erase.mp hx
    refine ⟨hxy, ?_⟩
    have hax : aeval x p = 0 := by
      rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot, eval_map_algebraMap] at hxr
      exact hxr
    have hmx : p = minpoly E x := minpoly.eq_of_irreducible_of_monic hirr hax hmon
    have horb : x ∈ MulAction.orbit (G E Ω) y :=
      (Normal.minpoly_eq_iff_mem_orbit (F := E) Ω).mp (by rw [← hmx])
    obtain ⟨σ, hσ⟩ := horb
    exact ⟨σ, hσ⟩
  · rw [Finset.sum_erase_eq_sub hyr, Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnd, Multiset.map_id', map_neg, ← nextCoeff_map_eq, ← hq, hsum, neg_neg]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEigenvectorOfTraceEqAddCharacter
section
namespace GlobalTheory

private lemma exists_char_augmentation_zero_acting_as_one {K Γ V : Type} [Field K] [Group Γ]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K Γ V)
    (χ : Γ →* Kˣ) (hs : ρ.IsSemisimpleRepresentation)
    (hno : ∀ v : V, (∀ g, ρ g v = ((χ g : Kˣ) : K) • v) → v = 0) :
    ∃ x : MonoidAlgebra K Γ, MonoidAlgebra.lift K K Γ ((Units.coeHom K).comp χ) x = 0 ∧
      ρ.asAlgebraHom x = 1 := by
  set ε := MonoidAlgebra.lift K K Γ ((Units.coeHom K).comp χ) with hε
  have hsm : IsSemisimpleModule (MonoidAlgebra K Γ) ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp hs
  let b := Module.finBasis K V
  let m : Fin (Module.finrank K V) → ρ.asModule := fun i => ρ.asModuleEquiv.symm (b i)
  let P : Submodule (MonoidAlgebra K Γ) (Fin (Module.finrank K V) → ρ.asModule) :=
    Submodule.map (LinearMap.toSpanSingleton (MonoidAlgebra K Γ) _ m)
      (RingHom.ker (ε : MonoidAlgebra K Γ →+* K))
  obtain ⟨C, hC⟩ := exists_isCompl P
  have hm : m ∈ P ⊔ C := by rw [hC.sup_eq_top]; trivial
  obtain ⟨p, hp, c, hc, hpc⟩ := Submodule.mem_sup.mp hm
  have hkill : ∀ x, ε x = 0 → x • c = 0 := by
    intro x hx
    have h1 : x • c ∈ P := by
      have : x • c = x • m - x • p := by rw [← hpc, smul_add, add_sub_cancel_left]
      rw [this]
      exact P.sub_mem (Submodule.mem_map.mpr ⟨x, RingHom.mem_ker.mpr hx,
        LinearMap.toSpanSingleton_apply _ _ _ _⟩) (P.smul_mem x hp)
    have h2 : x • c ∈ P ⊓ C := Submodule.mem_inf.mpr ⟨h1, C.smul_mem x hc⟩
    rwa [hC.inf_eq_bot, Submodule.mem_bot] at h2
  have hc0 : c = 0 := by
    funext i
    have hv := hno (ρ.asModuleEquiv (c i)) fun g => by
      have h := congrFun (hkill (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 ((χ g : Kˣ) : K))
        (by simp [hε, MonoidAlgebra.lift_single])) i
      change ρ.asModuleEquiv.symm (ρ.asAlgebraHom _ (ρ.asModuleEquiv (c i))) = 0 at h
      rw [LinearEquiv.map_eq_zero_iff, map_sub, Representation.asAlgebraHom_single,
        Representation.asAlgebraHom_single, one_smul, map_one, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
      exact h
    simpa using hv
  rw [hc0, add_zero] at hpc
  obtain ⟨y, hy, hym⟩ := Submodule.mem_map.mp (show m ∈ P from hpc ▸ hp)
  refine ⟨y, RingHom.mem_ker.mp hy, b.ext fun i => ?_⟩
  have h := congrFun hym i
  change ρ.asModuleEquiv.symm (ρ.asAlgebraHom y (ρ.asModuleEquiv (ρ.asModuleEquiv.symm (b i)))) =
    ρ.asModuleEquiv.symm (b i) at h
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_eq, LinearEquiv.apply_symm_apply] at h
  simpa using h

private lemma false_of_trace_pow_eq_card_add_one_sub {L ι : Type} [Field L] [CharZero L] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι L) (h : ∀ n : ℕ, (M ^ n).trace = ((Fintype.card ι : L) + 1) - 0 ^ n) :
    False := by
  set D : L := (Fintype.card ι : L) + 1 with hD
  have hD0 : D ≠ 0 := by rw [hD]; exact Nat.cast_add_one_ne_zero _
  have hpoly : ∀ f : Polynomial L, (Polynomial.aeval M f).trace = D * f.eval 1 - f.eval 0 := by
    intro f
    induction f using Polynomial.induction_on' with
    | add f g hf hg => simp only [map_add (f := _), Matrix.trace_add, hf, hg, Polynomial.eval_add]; ring
    | monomial n a =>
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        Matrix.trace_smul, h n, Polynomial.eval_monomial, Polynomial.eval_monomial, one_pow,
        smul_eq_mul]
      ring
  set p := M.charpoly with hp
  have hvan : ∀ g : Polynomial L, D * (g * p).eval 1 - (g * p).eval 0 = 0 := by
    intro g
    rw [← hpoly, map_mul, hp, Matrix.aeval_self_charpoly, mul_zero, Matrix.trace_zero]
  have hp1 : p.eval 1 = 0 := by
    have := hvan Polynomial.X
    simp only [Polynomial.eval_mul, Polynomial.eval_X, one_mul, zero_mul, sub_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hD0
  have hp0 : p.eval 0 = 0 := by
    have := hvan 1
    simpa [hp1] using this
  have hpne : p ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpne 1
  set b := p.rootMultiplicity 1
  have hb : 0 < b := (Polynomial.rootMultiplicity_pos hpne).mpr hp1
  have hcop : IsCoprime ((Polynomial.X - Polynomial.C (1 : L)) ^ b) q :=
    ((Polynomial.irreducible_X_sub_C (1 : L)).coprime_iff_not_dvd.mpr hq).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have hq0 : q.eval 0 = 0 := by
    have := hp0
    rw [hpq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at this
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ (by norm_num))
  have he1 : (v * q).eval 1 = 1 := by
    have := congrArg (Polynomial.eval 1) huv
    simpa [Polynomial.eval_mul, zero_pow hb.ne'] using this
  have he0 : (v * q).eval 0 = 0 := by simp [Polynomial.eval_mul, hq0]
  have hidem : (v * q) * (v * q) = v * q - (u * v) * p := by
    rw [hpq]; linear_combination (v * q) * huv
  set E := Polynomial.aeval M (v * q) with hE
  have hEE : E * E = E := by
    rw [hE, ← map_mul, hidem, map_sub, map_mul (Polynomial.aeval M) (u * v) p, hp,
      Matrix.aeval_self_charpoly, mul_zero, sub_zero]
  have htrE : E.trace = D := by rw [hE, hpoly, he1, he0]; ring
  have hid : IsIdempotentElem (Matrix.toLin' E) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hEE]
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  rw [LinearMap.trace_eq_matrix_trace L (Pi.basisFun L ι), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin', htrE, hD] at htr
  have hle := Submodule.finrank_le (LinearMap.range (Matrix.toLin' E))
  rw [Module.finrank_fintype_fun_eq_card] at hle
  have : Fintype.card ι + 1 = Module.finrank L (LinearMap.range (Matrix.toLin' E)) := by
    exact_mod_cast htr
  omega

theorem _root_.GlobalTheory.exists_eigenvector_of_trace_eq_add_character :
    ∀ (K L Γ V ι : Type) [Field K] [Field L] [CharZero L] [Group Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype ι] [DecidableEq ι] (φ : K →+* L) (ρ : Representation K Γ V) (σ : Γ →* Matrix ι ι L) (χ : Γ →* Kˣ), ρ.IsSemisimpleRepresentation → (∀ g, φ (LinearMap.trace K V (ρ g)) = (σ g).trace + φ ((χ g : Kˣ) : K)) → ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = ((χ g : Kˣ) : K) • v := by
  intro K L Γ V ι _ _ _ _ _ _ _ _ _ φ ρ σ χ hs htr
  by_contra hcon
  push_neg at hcon
  have hno : ∀ v : V, (∀ g, ρ g v = ((χ g : Kˣ) : K) • v) → v = 0 := fun v hv => by
    by_contra h0
    obtain ⟨g, hg⟩ := hcon v h0
    exact hg (hv g)
  obtain ⟨x, hx, hρx⟩ := exists_char_augmentation_zero_acting_as_one ρ χ hs hno
  let S : MonoidAlgebra K Γ →+* Matrix ι ι L :=
    MonoidAlgebra.liftNCRingHom ((Matrix.scalar ι).comp φ) σ
      (fun _ _ => Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)
  have hkey : ∀ z : MonoidAlgebra K Γ, φ (LinearMap.trace K V (ρ.asAlgebraHom z)) =
      (S z).trace + φ (MonoidAlgebra.lift K K Γ ((Units.coeHom K).comp χ) z) := by
    intro z
    refine MonoidAlgebra.induction_linear z ?_ ?_ ?_
    · simp
    · intro f g hf hg
      simp only [map_add (f := _), Matrix.trace_add, hf, hg]; ring
    · intro g r
      rw [Representation.asAlgebraHom_single, map_smul, smul_eq_mul, map_mul, htr g]
      have hS : S (MonoidAlgebra.single g r) = Matrix.scalar ι (φ r) * σ g := by
        simp [S, MonoidAlgebra.liftNCRingHom, MonoidAlgebra.liftNC_single]
      rw [hS]
      rw [MonoidAlgebra.lift_single, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
        Matrix.trace_smul, smul_eq_mul, smul_eq_mul, map_mul]
      simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply]
      ring
  have hdim := htr 1
  rw [map_one ρ, LinearMap.trace_one, map_natCast, map_one σ, Matrix.trace_one, map_one χ,
    Units.val_one, map_one φ] at hdim
  have hpow : ∀ n : ℕ, ((S x) ^ n).trace = ((Fintype.card ι : L) + 1) - 0 ^ n := by
    intro n
    have h1 := hkey (x ^ n)
    rw [map_pow, hρx, one_pow, LinearMap.trace_one, map_natCast, map_pow, map_pow, hx] at h1
    have h0 : φ ((0 : K) ^ n) = (0 : L) ^ n := by rw [map_pow, map_zero]
    linear_combination hdim - h1 - h0
  exact false_of_trace_pow_eq_card_add_one_sub (S x) hpow

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingLeFiniteIndexWeilSubgroup
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilOpenFin

theorem exists_finset_fix_le : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ (σ : G E Ω) (s : Finset Ω), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ s, (σ ^ m) x = x) → (∀ k : ℕ, 0 < k → ∃ ζ : Ω, ∀ σ : Weil h, (σ : G E Ω) ζ = ζ → (k : ℤ) ∣ deg σ) → (∀ M : Subgroup (Ine (F := E) A), IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M) → ∀ H : Subgroup (Weil h), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∃ s : Finset Ω, ∀ σ : Weil h, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ H := by
  intro E Ω _ _ _ _ _ A w h h1 h2 h3 H hH hopen
  classical

  have hfix : ∀ (g : G E Ω) (t : Finset Ω), (∀ x ∈ t, g x = x) → ∀ n : ℤ, ∀ x ∈ t, (g ^ n) x = x := by
    intro g t hg n x hx
    have hm : g ∈ MulAction.stabilizer (G E Ω) x := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact hg x hx
    have := (MulAction.mem_stabilizer_iff).mp (Subgroup.zpow_mem _ hm n)
    rwa [AlgEquiv.smul_def] at this
  obtain ⟨s₁, hs₁⟩ := h3 (H.comap (ineIncl h)) hopen
  let φ : Weil h := frob h
  obtain ⟨m, hm0, hm⟩ := h1 (φ : G E Ω) s₁
  have hN : H.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  set k : ℕ := m * H.normalCore.index with hk
  have hk0 : 0 < k := Nat.mul_pos hm0 (Nat.pos_of_ne_zero hN)
  let ψ : Weil h := φ ^ k
  have hψH : ψ ∈ H := by
    apply Subgroup.normalCore_le
    show φ ^ (m * H.normalCore.index) ∈ H.normalCore
    rw [pow_mul]; exact Subgroup.pow_index_mem _ _
  have hψdeg : deg ψ = k := by simp [ψ, φ]
  have hψfix : ∀ x ∈ s₁, (ψ : G E Ω) x = x := by
    intro x hx
    have := hfix _ s₁ hm (H.normalCore.index : ℤ) x hx
    simpa [ψ, φ, hk, pow_mul] using this
  obtain ⟨ζ, hζ⟩ := h2 k hk0
  refine ⟨insert ζ s₁, fun τ hτ => ?_⟩
  obtain ⟨i, hi⟩ := hζ τ (hτ ζ (Finset.mem_insert_self _ _))
  let ρ : Weil h := τ * ψ ^ (-i)
  have hρdeg : deg ρ = 0 := by
    simp only [ρ, deg_mul, deg_zpow, hψdeg, hi]; ring
  have hρIne : (ρ : G E Ω) ∈ Ine (F := E) A := deg_eq_zero_iff.mp hρdeg
  have hρfix : ∀ x ∈ s₁, (ρ : G E Ω) x = x := by
    intro x hx
    have e1 := hfix _ s₁ hψfix (-i) x hx
    show ((τ : G E Ω) * ((ψ ^ (-i) : Weil h) : G E Ω)) x = x
    rw [AlgEquiv.mul_apply, Subgroup.coe_zpow, e1]
    exact hτ x (Finset.mem_insert_of_mem hx)
  have hρM := hs₁ ⟨ρ, hρIne⟩ hρfix
  have hρH : ρ ∈ H := by
    have : ineIncl h ⟨ρ, hρIne⟩ ∈ H := hρM
    exact this
  have : τ = ρ * ψ ^ i := by simp [ρ]
  rw [this]
  exact H.mul_mem hρH (H.zpow_mem hψH i)

end GlobalTheory.WeilOpenFin
end

