module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeInfSubspaceBaseChangeDvr
section
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

namespace GlobalTheory.LatticeInterBaseChange

end GlobalTheory.LatticeInterBaseChange

namespace GlobalTheory.LatticeInterBaseChange

end GlobalTheory.LatticeInterBaseChange

namespace GlobalTheory.LatticeInterBaseChange

open NumberField IsDedekindDomain Module in
private theorem exists_functional_comp_eq {K F : Type} [Field K] [Field F] (e : K →+* F)
    {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module F V']
    (iV : V →ₛₗ[e] V') {ι : Type} (b : Basis ι K V)
    (hli : LinearIndependent F (fun a => iV (b a))) (φ : V →ₗ[K] K) :
    ∃ ψ : V' →ₗ[F] F, ∀ v, ψ (iV v) = e (φ v) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Basis.span hli).constr F (fun a => e (φ (b a))))
  let f₁ : V →ₛₗ[e] F := g.comp iV
  let f₂ : V →ₛₗ[e] F :=
    { toFun := fun v => e (φ v)
      map_add' := fun v w => by simp
      map_smul' := fun t v => by simp }
  have hf : f₁ = f₂ := by
    refine b.ext fun a => ?_
    have h := LinearMap.congr_fun hg (Basis.span hli a)
    rw [Basis.constr_basis, LinearMap.comp_apply, Submodule.subtype_apply, Basis.span_apply] at h
    exact h
  exact ⟨g, fun v => LinearMap.congr_fun hf v⟩

open NumberField IsDedekindDomain Module in
private theorem exists_integral_inverse_coefficients {K : Type} [Field K] [NumberField K] {n : ℕ}
    (c : Fin n → K) :
    ∃ β : Fin n → K, (∀ j k, ∃ r : 𝓞 K, (r : K) = β j * c k) ∧
      ∀ k, c k * ∑ j, β j * c j = c k := by
  classical
  by_cases hc : ∀ k, c k = 0
  · exact ⟨0, fun j k => ⟨0, by simp⟩, fun k => by simp [hc k]⟩
  push_neg at hc
  obtain ⟨k₀, hk₀⟩ := hc
  let I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    FractionalIdeal.spanFinset (𝓞 K) Finset.univ c
  have hIc : (I : Submodule (𝓞 K) K) = Submodule.span (𝓞 K) (Set.range c) := by
    change Submodule.span (𝓞 K) (c '' ((Finset.univ : Finset (Fin n)) : Set (Fin n))) = _
    rw [Finset.coe_univ, Set.image_univ]
  have hI : I ≠ 0 := by
    intro h
    exact hk₀ ((FractionalIdeal.spanFinset_eq_zero.1 h) k₀ (Finset.mem_univ _))
  have h1 : (1 : K) ∈ (I : Submodule (𝓞 K) K) *
      ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hI]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  have key : ∃ β : Fin n → K,
      (∀ j, β j ∈ ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K)) ∧
        (1 : K) = ∑ j, β j * c j := by
    refine Submodule.mul_induction_on (C := fun z => ∃ β : Fin n → K,
      (∀ j, β j ∈ ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K)) ∧
        z = ∑ j, β j * c j) h1 ?_ ?_
    · intro m hm y hy
      rw [hIc, Submodule.mem_span_range_iff_exists_fun] at hm
      obtain ⟨r, rfl⟩ := hm
      refine ⟨fun j => r j • y, fun j => Submodule.smul_mem _ (r j) hy, ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Algebra.smul_def]
      ring
    · rintro x y ⟨β, hβ, rfl⟩ ⟨β', hβ', rfl⟩
      exact ⟨β + β', fun j => add_mem (hβ j) (hβ' j),
        by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]⟩
  obtain ⟨β, hβI, hβ1⟩ := key
  refine ⟨β, fun j k => ?_, fun k => by rw [← hβ1, mul_one]⟩
  have hck : c k ∈ I := by
    rw [← FractionalIdeal.mem_coe, hIc]
    exact Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1
    ((FractionalIdeal.mem_inv_iff hI).1 (FractionalIdeal.mem_coe.1 (hβI j)) (c k) hck)
  exact ⟨r, hr⟩

open NumberField IsDedekindDomain Module in
private theorem mem_span_image_inf_ker {K F R : Type} [Field K] [NumberField K] [Field F]
    [CommRing R] [Algebra R F] (e : K →+* F) {V V' : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module F V'] [Module R V']
    [IsScalarTower R F V'] (iV : V →ₛₗ[e] V')
    (he : ∀ a : 𝓞 K, e (a : K) ∈ (algebraMap R F).range) (φ : V →ₗ[K] K) (ψ : V' →ₗ[F] F)
    (hψ : ∀ v, ψ (iV v) = e (φ v)) (A : Submodule (𝓞 K) V) {x : V'}
    (hx : x ∈ Submodule.span R (iV '' (A : Set V))) (h0 : ψ x = 0) :
    x ∈ Submodule.span R
      (iV '' ((A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V)) := by
  obtain ⟨n, r, g, hxg⟩ := Submodule.mem_span_set'.1 hx
  choose a ha hag using fun i => (g i).2
  obtain ⟨β, hβint, hβ⟩ := exists_integral_inverse_coefficients (fun i => φ (a i))
  choose ρ hρ using hβint
  beta_reduce at hρ hβ
  have hρs : ∀ j k, (ρ j k) • a j = (β j * φ (a k)) • a j := by
    intro j k
    rw [← hρ j k, ← algebraMap_smul K (ρ j k) (a j)]
  let w : Fin n → V := fun k => a k - ∑ j, (ρ j k) • a j
  have hwA : ∀ k, w k ∈ A := fun k =>
    sub_mem (ha k) (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (ha j))
  have hwφ : ∀ k, φ (w k) = 0 := by
    intro k
    have h := hβ k
    rw [Finset.mul_sum] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [w, map_sub, map_sum, hρs, map_smul, smul_eq_mul]
    rw [sub_eq_zero]
    conv_lhs => rw [← h]
    exact Finset.sum_congr rfl fun j _ => by ring
  have key : ∑ k, algebraMap R F (r k) * e (φ (a k)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h0, ← hxg, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hag k, ← algebraMap_smul F (r k) (iV (a k)), LinearMap.map_smul, smul_eq_mul, hψ]
  have hiw : ∀ k, iV (w k) = iV (a k) - ∑ j, (e (β j) * e (φ (a k))) • iV (a j) := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [w, map_sub, map_sum, hρs, LinearMap.map_smulₛₗ, map_mul]
  have hx' : x = ∑ k, r k • iV (w k) := by
    simp only [hiw, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum]
    have h2 : ∑ k, ∑ j, r k • (e (β j) * e (φ (a k))) • iV (a j) = 0 := by
      have h3 : ∀ k j, r k • (e (β j) * e (φ (a k))) • iV (a j) =
          (e (β j) * (algebraMap R F (r k) * e (φ (a k)))) • iV (a j) := by
        intro k j
        rw [← algebraMap_smul F (r k), smul_smul]
        congr 1
        ring
      simp only [h3]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.sum_smul, ← Finset.mul_sum, key, mul_zero, zero_smul]
    rw [h2, sub_zero, ← hxg]
    exact Finset.sum_congr rfl fun k _ => by rw [hag k]
  rw [hx']
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨w k, Submodule.mem_inf.2 ⟨hwA k, LinearMap.mem_ker.2 (hwφ k)⟩, rfl⟩)


open NumberField IsDedekindDomain Module in
theorem _root_.GlobalTheory.LatticeInterBaseChange.span_inf_baseChange : ∀ (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V') (ι : Type) (b : Basis ι K V), LinearIndependent (FractionRing O) (fun a => iV (b a)) → (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) → ∀ (A : Submodule (𝓞 K) V) (U : Submodule K V), Submodule.span O (iV '' ((A ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V)) = Submodule.span O (iV '' (A : Set V)) ⊓ (Submodule.span (FractionRing O) (iV '' (U : Set V))).restrictScalars O := by
  intro K _ _ O _ _ _ e V V' _ _ _ _ _ _ _ _ _ iV ι b hli he A U
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    exact Submodule.mem_inf.2 ⟨Submodule.subset_span ⟨v, (Submodule.mem_inf.1 hv).1, rfl⟩,
      Submodule.subset_span ⟨v, (Submodule.mem_inf.1 hv).2, rfl⟩⟩
  · intro x hx
    obtain ⟨hxA, hxU⟩ := Submodule.mem_inf.1 hx
    classical
    let bQ := Module.finBasis K (V ⧸ U)
    let f : Fin (Module.finrank K (V ⧸ U)) → V →ₗ[K] K := fun j => (bQ.coord j).comp U.mkQ
    have hU : ∀ v, v ∈ U ↔ ∀ j, f j v = 0 := by
      intro v
      simp only [f, LinearMap.comp_apply, Basis.coord_apply, Submodule.mkQ_apply]
      constructor
      · intro h j
        rw [(Submodule.Quotient.mk_eq_zero U).2 h, map_zero, Finsupp.zero_apply]
      · intro h
        exact (Submodule.Quotient.mk_eq_zero U).1
          ((LinearEquiv.map_eq_zero_iff bQ.repr).1 (Finsupp.ext h))
    choose ψ hψ using fun j => exists_functional_comp_eq e iV b hli (f j)
    have hψx : ∀ j, ψ j x = 0 := by
      intro j
      have hle : Submodule.span (FractionRing O) (iV '' (U : Set V)) ≤ LinearMap.ker (ψ j) := by
        rw [Submodule.span_le]
        rintro _ ⟨v, hv, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, hψ, (hU v).1 hv j, map_zero]
      exact hle hxU
    have claim : ∀ s : Finset (Fin (Module.finrank K (V ⧸ U))), ∀ (A' : Submodule (𝓞 K) V) (y : V'),
        y ∈ Submodule.span O (iV '' (A' : Set V)) → (∀ j ∈ s, ψ j y = 0) →
        y ∈ Submodule.span O (iV '' ((A' ⊓ ⨅ j ∈ s, (LinearMap.ker (f j)).restrictScalars (𝓞 K) :
          Submodule (𝓞 K) V) : Set V)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro A' y hy _
        simpa using hy
      | insert j s hj ih =>
        intro A' y hy h0
        have h1 := mem_span_image_inf_ker e iV he (f j) (ψ j) (hψ j) A' hy
          (h0 j (Finset.mem_insert_self j s))
        have h2 := ih _ y h1 fun i hi => h0 i (Finset.mem_insert_of_mem hi)
        refine Submodule.span_mono (Set.image_mono ?_) h2
        intro v hv
        simp only [SetLike.mem_coe, Submodule.mem_inf, Submodule.mem_iInf,
          Submodule.restrictScalars_mem, LinearMap.mem_ker, Finset.mem_insert] at hv ⊢
        refine ⟨hv.1.1, fun i hi => ?_⟩
        rcases hi with rfl | hi
        · exact hv.1.2
        · exact hv.2 i hi
    have hfin := claim Finset.univ A x hxA fun j _ => hψx j
    refine Submodule.span_mono (Set.image_mono ?_) hfin
    intro v hv
    simp only [SetLike.mem_coe, Submodule.mem_inf, Submodule.mem_iInf,
      Submodule.restrictScalars_mem, LinearMap.mem_ker, Finset.mem_univ, forall_const] at hv ⊢
    exact ⟨hv.1, (hU v).2 hv.2⟩

end GlobalTheory.LatticeInterBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeProjectionBaseChangeDvrComm
section
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

namespace GlobalTheory

theorem projection_span_extend_scalars
    (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] [AddCommGroup V'] [Module (FractionRing O) V']
    [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V') (ι : Type) (b : Basis ι K V) :
    LinearIndependent (FractionRing O) (fun a => iV (b a)) →
    (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) →
    ∀ (A : Submodule (𝓞 K) V) (U U' : Submodule K V), IsCompl U U' →
    Submodule.span O (iV '' ((U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K)) :
        Submodule (𝓞 K) V) : Set V)) =
      (Submodule.span (FractionRing O) (iV '' (U : Set V))).restrictScalars O ⊓
        (Submodule.span O (iV '' (A : Set V)) ⊔
          (Submodule.span (FractionRing O) (iV '' (U' : Set V))).restrictScalars O) := by
  intro hli _ A U U' hUU'
  set F := FractionRing O

  let p : V →ₗ[K] V := U.subtype ∘ₗ U.projectionOnto U' hUU'
  have hpU : ∀ u ∈ U, p u = u := fun u hu => by
    have h := Submodule.projectionOnto_apply_left hUU' ⟨u, hu⟩
    show ((U.projectionOnto U' hUU') ((⟨u, hu⟩ : U) : V) : V) = u
    rw [h]
  have hpU' : ∀ u ∈ U', p u = 0 := fun u hu => by
    have h := Submodule.projectionOnto_apply_right hUU' ⟨u, hu⟩
    show ((U.projectionOnto U' hUU') ((⟨u, hu⟩ : U') : V) : V) = 0
    rw [h]; rfl
  have hpmem : ∀ v, p v ∈ U := fun v => by simp [p]
  have hdec : ∀ v, ∃ u ∈ U, ∃ u' ∈ U', u + u' = v := fun v => by
    have : v ∈ U ⊔ U' := by rw [hUU'.sup_eq_top]; trivial
    exact Submodule.mem_sup.mp this
  have hpdiff : ∀ v, p v - v ∈ U' := fun v => by
    obtain ⟨u, hu, u', hu', rfl⟩ := hdec v
    rw [map_add (f := _), hpU u hu, hpU' u' hu', add_zero]
    simpa using U'.neg_mem hu'

  let W : Submodule F V' := Submodule.span F (Set.range fun a => iV (b a))
  let f : W →ₗ[F] V' := (Basis.span hli).constr F (fun a => iV (p (b a)))
  obtain ⟨q, hq⟩ := LinearMap.exists_extend f
  have hqi : ∀ v, q (iV v) = iV (p v) := by
    have : (q.comp iV : V →ₛₗ[e] V') = iV.comp p := by
      refine b.ext fun a => ?_
      have hmem : iV (b a) ∈ W := Submodule.subset_span ⟨a, rfl⟩
      have h1 : q (iV (b a)) = f ⟨iV (b a), hmem⟩ := by
        rw [← hq]; rfl
      have h2 : (⟨iV (b a), hmem⟩ : W) = Basis.span hli a := by
        rw [Basis.span_apply]
      simp only [LinearMap.comp_apply]
      rw [h1, h2, Basis.constr_basis]
    intro v
    exact congrArg (fun g => g v) this
  have hqU : ∀ x ∈ Submodule.span F (iV '' (U : Set V)), q x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hy
      rw [hqi, hpU u hu]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  have hqU' : ∀ x ∈ Submodule.span F (iV '' (U' : Set V)), q x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hy
      rw [hqi, hpU' u hu, map_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem] at hw
    obtain ⟨hwU, hwA⟩ := hw
    obtain ⟨a, ha, u', hu', rfl⟩ := Submodule.mem_sup.mp hwA
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact Submodule.subset_span ⟨_, hwU, rfl⟩
    · rw [map_add (f := _)]
      refine Submodule.add_mem_sup (Submodule.subset_span ⟨a, ha, rfl⟩) ?_
      exact Submodule.subset_span ⟨u', hu', rfl⟩
  · intro x hx
    obtain ⟨hxU, hxs⟩ := Submodule.mem_inf.mp hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxs
    have hxq : q (y + z) = y + z := hqU _ hxU
    rw [map_add (f := _), hqU' z hz, add_zero] at hxq
    rw [← hxq]
    have hmap : q y ∈ Submodule.map (q.restrictScalars O) (Submodule.span O (iV '' (A : Set V))) :=
      ⟨y, hy, rfl⟩
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨p a, ?_, (hqi a).symm⟩
    simp only [SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem]
    refine ⟨hpmem a, ?_⟩
    have : p a = a + (p a - a) := by abel
    rw [this]
    exact Submodule.add_mem_sup ha (hpdiff a)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxFrobeniusOrbitLengthDiffBoundsZmod
section
open PowerSeries GlobalTheory.BK Function Finset

namespace GlobalTheory.BK.OrbitBound

variable {e : ℕ} (u : ZMod e)

theorem iter_mul (n : ℕ) (x : ZMod e) : (fun y => u * y)^[n] x = u ^ n * x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply, ih, pow_succ, mul_assoc]

noncomputable def orb (x : ZMod e) : Finset (ZMod e) :=
  (range (minimalPeriod (fun y => u * y) x)).image fun k => u ^ k * x

variable {a : ℕ} (ha : 0 < a) (hu : u ^ a = 1)
include ha hu

theorem mp_pos (x : ZMod e) : 0 < minimalPeriod (fun y => u * y) x :=
  IsPeriodicPt.minimalPeriod_pos ha (by
    change (fun y => u * y)^[a] x = x
    rw [iter_mul, hu, one_mul])

theorem pow_mp_mul (x : ZMod e) : u ^ minimalPeriod (fun y => u * y) x * x = x := by
  rw [← iter_mul]; exact iterate_minimalPeriod

theorem pow_mp_mul_mul (x : ZMod e) (k : ℕ) :
    u ^ (minimalPeriod (fun y => u * y) x * k) * x = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, mul_assoc, pow_mp_mul u ha hu x, ih]

theorem mp_sub_dvd (x y : ZMod e) : minimalPeriod (fun z => u * z) (x - y) ∣
    minimalPeriod (fun z => u * z) x * minimalPeriod (fun z => u * z) y := by
  apply IsPeriodicPt.minimalPeriod_dvd
  change (fun z => u * z)^[_] (x - y) = x - y
  rw [iter_mul, mul_sub, pow_mp_mul_mul u ha hu x, mul_comm (minimalPeriod _ x),
    pow_mp_mul_mul u ha hu y]

theorem mp_sub_pow_dvd (x : ZMod e) (k : ℕ) : minimalPeriod (fun z => u * z) (x - u ^ k * x) ∣
    minimalPeriod (fun z => u * z) x := by
  apply IsPeriodicPt.minimalPeriod_dvd
  change (fun z => u * z)^[_] (x - u ^ k * x) = x - u ^ k * x
  rw [iter_mul, mul_sub, mul_left_comm, pow_mp_mul u ha hu x]

theorem isUnit_u : IsUnit u :=
  have h : u * u ^ (a - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel ha, hu]
  ⟨⟨u, u ^ (a - 1), h, by rw [mul_comm]; exact h⟩, rfl⟩

theorem card_orb (x : ZMod e) : (orb u x).card = minimalPeriod (fun y => u * y) x := by
  rw [orb, card_image_of_injOn, card_range]
  rw [coe_range]
  intro i hi j hj h
  refine iterate_injOn_Iio_minimalPeriod hi hj ?_
  simp only [iter_mul]
  exact h

theorem mem_orb (x : ZMod e) (n : ℕ) : u ^ n * x ∈ orb u x := by
  refine mem_image.2 ⟨n % minimalPeriod (fun y => u * y) x, mem_range.2 (Nat.mod_lt _ (mp_pos u ha hu x)), ?_⟩
  show u ^ (n % _) * x = u ^ n * x
  rw [← iter_mul, ← iter_mul]
  exact iterate_mod_minimalPeriod_eq

omit ha hu in
theorem orb_subset {Sig : Finset (ZMod e)} (hcl : ∀ c ∈ Sig, u * c ∈ Sig) {x : ZMod e}
    (hx : x ∈ Sig) : orb u x ⊆ Sig := by
  have key : ∀ k : ℕ, u ^ k * x ∈ Sig := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih => rw [pow_succ', mul_assoc]; exact hcl _ ih
  intro z hz
  obtain ⟨k, -, rfl⟩ := mem_image.1 hz
  exact key k

theorem four_mp_le (Sig : Finset (ZMod e)) (N : ℕ) (hcl : ∀ c ∈ Sig, u * c ∈ Sig) (h0 : (0 : ZMod e) ∈ Sig)
    (hN : Sig.card ≤ N) (h2 : 2 ≤ N) {x y : ZMod e} (hx : x ∈ Sig) (hy : y ∈ Sig) :
    4 * minimalPeriod (fun z => u * z) (x - y) ≤ N ^ 2 := by
  classical
  by_cases hyo : y ∈ orb u x
  · obtain ⟨k, -, rfl⟩ := mem_image.1 hyo
    have hle := Nat.le_of_dvd (mp_pos u ha hu x) (mp_sub_pow_dvd u ha hu x k)
    by_cases hx0 : x = 0
    · have h1 : minimalPeriod (fun y => u * y) x = 1 :=
        minimalPeriod_eq_one_iff_isFixedPt.2 (by simp [IsFixedPt, hx0])
      nlinarith
    · have hn0 : (0 : ZMod e) ∉ orb u x := by
        intro h
        obtain ⟨j, -, hj⟩ := mem_image.1 h
        exact hx0 (((isUnit_u u ha hu).pow j).mul_right_eq_zero.1 hj)
      have hsub : insert 0 (orb u x) ⊆ Sig := insert_subset h0 (orb_subset u hcl hx)
      have hc := card_le_card hsub
      rw [card_insert_of_notMem hn0, card_orb u ha hu] at hc
      nlinarith
  · have hdisj : Disjoint (orb u x) (orb u y) := by
      rw [disjoint_left]
      intro z hz1 hz2
      obtain ⟨i, -, rfl⟩ := mem_image.1 hz1
      obtain ⟨j, hj, hji⟩ := mem_image.1 hz2
      apply hyo
      have hy' : y = u ^ (minimalPeriod (fun z => u * z) y - j + i) * x := by
        rw [pow_add, mul_assoc, ← hji, ← mul_assoc, ← pow_add,
          Nat.sub_add_cancel (le_of_lt (mem_range.1 hj)), pow_mp_mul u ha hu y]
      rw [hy']
      exact mem_orb u ha hu x _
    have hsub : orb u x ∪ orb u y ⊆ Sig := union_subset (orb_subset u hcl hx) (orb_subset u hcl hy)
    have hc := card_le_card hsub
    rw [card_union_of_disjoint hdisj, card_orb u ha hu, card_orb u ha hu] at hc
    have hle := Nat.le_of_dvd (Nat.mul_pos (mp_pos u ha hu x) (mp_pos u ha hu y)) (mp_sub_dvd u ha hu x y)
    set m1 := minimalPeriod (fun z => u * z) x
    set m2 := minimalPeriod (fun z => u * z) y
    have h4 : 4 * (m1 * m2) ≤ (m1 + m2) ^ 2 := by
      zify; nlinarith [sq_nonneg ((m1 : ℤ) - m2)]
    have h5 : (m1 + m2) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (hc.trans hN) 2
    omega

end GlobalTheory.BK.OrbitBound

namespace GlobalTheory.BK


open OrbitBound in
theorem maxPeriod_bounds : ∀ (l e a : ℕ), l.Prime → 1 ≤ a → e + 1 = l ^ a → ∀ (Sig : Finset (ZMod e)) (N : ℕ),
    (∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig) → (0 : ZMod e) ∈ Sig → Sig.card ≤ N → 2 ≤ N →
    1 ≤ maxPeriod l Sig ∧ 4 * maxPeriod l Sig ≤ N ^ 2 ∧ ∀ c ∈ Sig, frobPeriod l c ≤ maxPeriod l Sig := by
  intro l e a _ ha hea Sig N hcl h0 hN h2
  have hu : (l : ZMod e) ^ a = 1 := by
    rw [← Nat.cast_pow, ← hea]
    push_cast
    rw [ZMod.natCast_self, zero_add]
  have h00 : ((0 : ZMod e), (0 : ZMod e)) ∈ Sig ×ˢ Sig := mem_product.2 ⟨h0, h0⟩
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (Nat.succ_le_of_lt (mp_pos (l : ZMod e) ha hu ((0 : ZMod e) - 0)))
      (Finset.le_sup (f := fun p : ZMod e × ZMod e => frobPeriod l (p.1 - p.2)) h00)
  · obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup (Sig ×ˢ Sig) ⟨_, h00⟩
      (fun p : ZMod e × ZMod e => frobPeriod l (p.1 - p.2))
    unfold maxPeriod
    rw [hpe]
    exact four_mp_le (l : ZMod e) ha hu Sig N hcl h0 hN h2 (mem_product.1 hp).1 (mem_product.1 hp).2
  · intro c hc
    have := Finset.le_sup (f := fun p : ZMod e × ZMod e => frobPeriod l (p.1 - p.2))
      (mem_product.2 ⟨hc, h0⟩ : (c, (0 : ZMod e)) ∈ Sig ×ˢ Sig)
    simp only [sub_zero] at this
    exact this

end GlobalTheory.BK
end

