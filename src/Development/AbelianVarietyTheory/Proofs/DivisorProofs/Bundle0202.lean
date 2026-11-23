module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0147
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDual
section
open ReciprocityTheory.PGsh GlobalTheory.FGDepth

namespace GlobalTheory.FrameDual

open Matrix Finset

variable {C : Type} [Field C]

def intSubring (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {x | IsIntV v x}
  zero_mem' := by simp [IsIntV]
  one_mem' := by simp [IsIntV]
  add_mem' := by
    intro x y hx hy
    exact le_trans (le_min hx hy) (v.map_add x y)
  mul_mem' := by
    intro x y hx hy
    show 0 ≤ v (x * y)
    rw [v.map_mul]; exact add_nonneg hx hy
  neg_mem' := by
    intro x hx
    show 0 ≤ v (-x)
    rw [v.map_neg]; exact hx

theorem adjugate_int (v : AddValuation C (WithTop ℝ)) {n : ℕ} (M : Matrix (Fin n) (Fin n) C)
    (hM : ∀ a b, IsIntV v (M a b)) (a b : Fin n) : IsIntV v (M.adjugate a b) := by
  let M' : Matrix (Fin n) (Fin n) (intSubring v) := Matrix.of fun a b => ⟨M a b, hM a b⟩
  have hMM : (intSubring v).subtype.mapMatrix M' = M := by
    ext a b; rfl
  have := RingHom.map_adjugate (intSubring v).subtype M'
  rw [hMM] at this
  rw [← this]
  exact (M'.adjugate a b).2

theorem frameDual (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (i d : ℕ)
    (u : Fin i → Fin d → C) (hu : IsSatFrame v u) :
    ∃ l : Fin i → Fin d → C, (∀ a e, IsIntV v (l a e)) ∧
      ∀ a a', ∑ e, l a e * u a' e = if a = a' then 1 else 0 := by
  obtain ⟨hint, r, hr⟩ := hu
  set M : Matrix (Fin i) (Fin i) C := Matrix.of fun a b => u a (r b) with hMdef
  have hdet0 : M.det ≠ 0 := by
    intro h; rw [h, v.map_zero] at hr; exact WithTop.top_ne_coe hr
  have hdetU : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet0
  have hinvdet : IsIntV v (M.det)⁻¹ := by
    show 0 ≤ v (M.det)⁻¹
    rw [v.map_inv, hr, neg_zero]
  have hNint : ∀ a b, IsIntV v (M⁻¹ a b) := by
    intro a b
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    exact (intSubring v).mul_mem hinvdet (adjugate_int v M (fun a b => hint _ _) a b)
  refine ⟨fun a e => ∑ b, if r b = e then M⁻¹ b a else 0, ?_, ?_⟩
  · intro a e
    exact (intSubring v).sum_mem fun b _ => by
      split_ifs
      · exact hNint b a
      · exact (intSubring v).zero_mem
  · intro a a'
    have hMN := Matrix.mul_nonsing_inv M hdetU
    have h1 := congrFun (congrFun hMN a') a
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    calc ∑ e, (∑ b, if r b = e then M⁻¹ b a else 0) * u a' e
        = ∑ e, ∑ b, if r b = e then u a' (r b) * M⁻¹ b a else 0 := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          split_ifs with h
          · rw [h, mul_comm]
          · rw [zero_mul]
      _ = ∑ b, ∑ e, if r b = e then u a' (r b) * M⁻¹ b a else 0 := Finset.sum_comm
      _ = ∑ b, M a' b * M⁻¹ b a := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_ite_eq]; simp [hMdef]
      _ = if a = a' then 1 else 0 := by
          rw [h1]; exact if_congr eq_comm rfl rfl

end GlobalTheory.FrameDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisComparisonMapInjectiveOfFlat
section
open scoped TensorProduct

theorem GlobalTheory.GoodEtale.galMap_injective_of_flat : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] [Module.Flat R O]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) := by
  intro A R C O _ _ _ _ _ _ _ _ G _ _ _ act T hT a ha n x y hxy htf σ
  set b := algebraMap R C (algebraMap A R a) with hb
  have key : ∀ c : C, ∑ i, T (y i * c) • x i = b * c := by
    intro c
    have h1 : ∀ i, T (y i * c) • x i = ∑ g, x i * act g (y i) * act g c := by
      intro i; rw [Algebra.smul_def, hT, mul_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul, mul_assoc]
    simp_rw [h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hxy]
    simp
  let L := LinearMap.lTensor O (LinearMap.mulLeft R b)
  have hL : Function.Injective L := by
    apply Module.Flat.lTensor_preserves_injective_linearMap
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    exact htf a ha c (by rw [Algebra.smul_def]; simpa using hc)
  let Φ : (G → O) → O ⊗[R] C := fun f => ∑ i, (∑ g, σ (act g (y i)) * f g) ⊗ₜ x i
  have hΦ : ∀ m, Φ (GlobalTheory.GoodEtale.galMap act σ m) = L m := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp [Φ]
    | tmul o c =>
      simp only [Φ, GlobalTheory.GoodEtale.galMap_tmul, L, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply]
      have h2 : ∀ i, (∑ g, σ (act g (y i)) * (o * σ (act g c))) = T (y i * c) • o := by
        intro i
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Algebra.smul_def, ← σ.commutes, hT, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_mul, map_mul]; ring
      simp_rw [h2, ← key, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
    | add m m' hm hm' =>
      rw [map_add (f := _), map_add (f := _), ← hm, ← hm']
      simp only [Φ, Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.add_tmul]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro m hm
  apply hL
  rw [← hΦ, hm, map_zero]
  simp [Φ]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentSemilinearBijective
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem semilinear_pow_smul {F F' V : Type} [Field F] [Field F'] [Algebra F F'] [AddCommGroup V]
    [Module F' V] [Module F V] (s : F' ≃ₐ[F] F') (T : Module.End F V)
    (hT : ∀ (c : F') (v : V), T (c • v) = s c • T v) (m : ℕ) (c : F') (v : V) :
    (T ^ m) (c • v) = (s ^ m) c • (T ^ m) v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, ih, hT, AlgEquiv.mul_apply, Module.End.mul_apply]

theorem pow_apply_of_mem_ker_sub_one {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) (u : V) (hu : u ∈ LinearMap.ker (T - 1)) (m : ℕ) : (T ^ m) u = u := by
  have h1 : T u = u := by
    have h := LinearMap.mem_ker.mp hu
    rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Module.End.mul_apply, h1, ih]

theorem algebraMap_trace_eq_sum_pow {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']
    (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (x : F') :
    algebraMap F F' (Algebra.trace F F' x) = ∑ j : Fin (Module.finrank F F'), (s ^ (j : ℕ)) x := by
  classical
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : FiniteDimensional F F' := Module.Finite.of_finite
  rw [trace_eq_sum_automorphisms]
  have hord : orderOf s = Module.finrank F F' := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hs, IsGalois.card_aut_eq_finrank]
  have hinj : Function.Injective (fun j : Fin (Module.finrank F F') => s ^ (j : ℕ)) := by
    intro i j hij
    simp only at hij
    rw [pow_inj_mod, hord, Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at hij
    exact Fin.ext hij
  have hbij : Function.Bijective (fun j : Fin (Module.finrank F F') => s ^ (j : ℕ)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hinj, by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]⟩
  exact (Fintype.sum_bijective _ hbij _ _ (fun j => rfl)).symm

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem galoisDescent_semilinear_bijective : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (V : Type) [AddCommGroup V] [Module F' V] [Module F V] [IsScalarTower F F' V] (T : Module.End F V), (∀ (c : F') (v : V), T (c • v) = s c • T v) → T ^ Module.finrank F F' = 1 → ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι F F'), Function.Bijective (fun v : ι → LinearMap.ker (T - 1) => ∑ i, b i • (v i : V)) := by
  intro F F' _ _ _ _ s hs V _ _ _ _ T hT hTn ι _ b
  classical
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : FiniteDimensional F F' := Module.Finite.of_finite
  set n := Module.finrank F F' with hn
  have hnd := traceForm_nondegenerate F F'
  set d := (Algebra.traceForm F F').dualBasis hnd b with hd
  have hdb : ∀ i j, Algebra.trace F F' (d i * b j) = if j = i then 1 else 0 := fun i j => by
    have h := LinearMap.BilinForm.apply_dualBasis_left hnd b i j
    simpa [Algebra.traceForm_apply] using h
  have key1 : ∀ i j, ∑ k : Fin n, (s ^ (k : ℕ)) (d i) * (s ^ (k : ℕ)) (b j) =
      if i = j then 1 else 0 := by
    intro i j
    have h := algebraMap_trace_eq_sum_pow s hs (d i * b j)
    simp only [map_mul] at h
    rw [← h, hdb]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hTk : ∀ (k : ℕ) (c : F') (v : V), (T ^ k) (c • v) = (s ^ k) c • (T ^ k) v :=
    semilinear_pow_smul s T hT
  have hfix : ∀ (u : LinearMap.ker (T - 1)) (k : ℕ), (T ^ k) (u : V) = u :=
    fun u k => pow_apply_of_mem_ker_sub_one T u u.2 k
  have hn0 : 0 < n := Module.finrank_pos
  have hcard : Fintype.card ι = n := (Module.finrank_eq_card_basis b).symm
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let A : Matrix (Fin n) ι F' := fun k j => (s ^ (k : ℕ)) (b j)
  let B : Matrix ι (Fin n) F' := fun i k => (s ^ (k : ℕ)) (d i)
  have hBA : B * A = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact key1 i j
  have hAB : A * B = 1 := (Matrix.mul_eq_one_comm_of_equiv e.symm).mpr hBA
  let k0 : Fin n := ⟨0, hn0⟩
  have key2 : ∀ l : Fin n, ∑ i, b i * (s ^ (l : ℕ)) (d i) = if k0 = l then 1 else 0 := by
    intro l
    have h := congrFun (congrFun hAB k0) l
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa [A, B, k0] using h
  constructor
  · intro v w hvw
    simp only at hvw
    have hk : ∀ k : ℕ, ∑ i, (s ^ k) (b i) • (v i : V) = ∑ i, (s ^ k) (b i) • (w i : V) := by
      intro k
      have h := congrArg (T ^ k) hvw
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sum, hTk, hfix] using h
    have expand : ∀ (u : ι → LinearMap.ker (T - 1)) (j : ι), (u j : V) =
        ∑ k : Fin n, (s ^ (k : ℕ)) (d j) • ∑ i, (s ^ (k : ℕ)) (b i) • (u i : V) := by
      intro u j
      simp_rw [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, key1]
      simp [ite_smul]
    funext j
    apply Subtype.ext
    rw [expand v j, expand w j]
    simp_rw [hk]
  · intro w
    let Q : V → V := fun u => ∑ k : Fin n, (T ^ (k : ℕ)) u
    have hQ : ∀ u, Q u ∈ LinearMap.ker (T - 1) := by
      intro u
      simp only [Q]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, map_sum]
      rw [Fin.sum_univ_eq_sum_range (fun k => T ((T ^ k) u)),
        Fin.sum_univ_eq_sum_range (fun k => (T ^ k) u)]
      have hs1 : ∀ k : ℕ, T ((T ^ k) u) = (T ^ (k + 1)) u := fun k => by
        rw [pow_succ', Module.End.mul_apply]
      simp_rw [hs1]
      have h1 := Finset.sum_range_succ' (fun k => (T ^ k) u) n
      have h2 := Finset.sum_range_succ (fun k => (T ^ k) u) n
      rw [h2, hTn, pow_zero] at h1
      exact (add_right_cancel h1).symm
    refine ⟨fun i => ⟨Q (d i • w), hQ _⟩, ?_⟩
    simp only [Q, hTk, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, key2]
    simp [ite_smul, k0]

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisElementDvdOfFormallyUnramified
section
open scoped TensorProduct

namespace GlobalTheory.GoodEtale

theorem galElt_dvd_of_unramified : ∀ (R C O : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O]
    [Algebra.FormallyUnramified O (O ⊗[R] C)] [Algebra.EssFiniteType O (O ⊗[R] C)]
    (G : Type) [Group G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (b : R) (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C b else 0) →
    ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) →
    ∀ h : G, ∃ m' : O ⊗[R] C, GlobalTheory.GoodEtale.galElt act σ x y h = algebraMap R O b • m' := by
  intro R C O _ _ _ _ _ _ _ G _ _ act b n x y hxy σ hinj h
  obtain ⟨t, ht1, ht2⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := O) (S := O ⊗[R] C)).mp inferInstance
  let τ : O ⊗[R] C →ₐ[O] O := (Pi.evalAlgHom O (fun _ : G => O) h).comp (galMap act σ)
  let ψ : (O ⊗[R] C) ⊗[O] (O ⊗[R] C) →ₐ[O] O ⊗[R] C :=
    Algebra.TensorProduct.lift (AlgHom.id O _) ((Algebra.ofId O (O ⊗[R] C)).comp τ) (fun _ _ => Commute.all _ _)
  have hψ : ∀ a c, ψ (a ⊗ₜ c) = a * algebraMap O (O ⊗[R] C) (τ c) := by
    intro a c; simp [ψ]
  set e := ψ t with he

  have hi : ∀ s, s * e = algebraMap O (O ⊗[R] C) (τ s) * e := by
    intro s
    have := congrArg ψ (ht1 s)
    rw [map_mul, map_sub, hψ, hψ, map_zero] at this
    simp only [map_one, one_mul, mul_one] at this
    rw [← he] at this
    rw [sub_mul, sub_eq_zero] at this
    exact this.symm

  have hii : τ e = 1 := by
    have hcomp : τ.comp ψ = τ.comp (Algebra.TensorProduct.lmul' O) := by
      apply Algebra.TensorProduct.ext'
      intro a c
      simp only [AlgHom.comp_apply, hψ, map_mul, AlgHom.commutes, Algebra.TensorProduct.lmul'_apply_tmul]
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
    have := congrArg (fun f => f t) hcomp
    simp only [AlgHom.comp_apply] at this
    rw [he, this, ht2, map_one]

  have hfix : galElt act σ x y h * e = galElt act σ x y h := by
    apply hinj
    rw [map_mul, galMap_galElt act σ x y b hxy h]
    funext g
    by_cases hg : g = h
    · subst hg
      have : galMap act σ e g = τ e := rfl
      simp [this, hii]
    · simp [Pi.single_apply, hg]
  refine ⟨e, ?_⟩
  rw [← hfix]
  simp only [galElt, Finset.sum_mul]
  have hterm : ∀ i, σ (x i) ⊗ₜ[R] act h⁻¹ (y i) * e = algebraMap O (O ⊗[R] C) (σ (x i) * σ (y i)) * e := by
    intro i
    have hsplit : σ (x i) ⊗ₜ[R] act h⁻¹ (y i) = algebraMap O (O ⊗[R] C) (σ (x i)) * ((1 : O) ⊗ₜ[R] act h⁻¹ (y i)) := by
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hsplit, mul_assoc, hi, ← mul_assoc, ← map_mul]
    congr 3
    have : τ ((1 : O) ⊗ₜ[R] act h⁻¹ (y i)) = σ (act h (act h⁻¹ (y i))) := by
      simp [τ, galMap_tmul]
    rw [this]
    congr 2
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [hterm, ← Finset.sum_mul, ← map_sum, ← map_mul, ← map_sum]
  have h1 := hxy 1
  simp only [map_one, AlgEquiv.one_apply, if_true] at h1
  rw [h1, AlgHom.commutes, Algebra.smul_def]

end GlobalTheory.GoodEtale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLBasicProperties
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.NrmBasic

section General

variable {G Γ : Type} [Group G] [Group Γ] (φ : Γ →* MulAut G) (s : Γ)

theorem nrmG_zero (δ : G) : nrmG φ s 0 δ = 1 := by
  simp [nrmG]

theorem nrmG_succ (l : ℕ) (δ : G) : nrmG φ s (l + 1) δ = nrmG φ s l δ * φ (s ^ l) δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem nrmG_twConj (l : ℕ) (δ y : G) :
    nrmG φ s l (y⁻¹ * δ * φ s y) = y⁻¹ * nrmG φ s l δ * φ (s ^ l) y := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, nrmG_succ, ih]
    have h1 : φ (s ^ l) (y⁻¹ * δ * φ s y) = (φ (s ^ l) y)⁻¹ * φ (s ^ l) δ * φ (s ^ (l + 1)) y := by
      rw [map_mul, map_mul, map_inv, pow_succ, map_mul, MulAut.mul_apply]
    rw [h1]
    group

theorem mul_map_nrmG (l : ℕ) (δ : G) :
    δ * φ s (nrmG φ s l δ) = nrmG φ s l δ * φ (s ^ l) δ := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, map_mul, ← mul_assoc, ih, pow_succ', map_mul, MulAut.mul_apply]

theorem nrmG_mul (l : ℕ) (δ ε : G) (h : ∀ i j : ℕ, Commute (φ (s ^ i) δ) (φ (s ^ j) ε)) :
    nrmG φ s l (δ * ε) = nrmG φ s l δ * nrmG φ s l ε := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, nrmG_succ, nrmG_succ, ih, map_mul]
    have hc : Commute (nrmG φ s l ε) (φ (s ^ l) δ) := by
      unfold nrmG
      apply Commute.list_prod_left
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact (h l i).symm
    rw [mul_assoc, mul_assoc, ← mul_assoc (nrmG φ s l ε), hc.eq, mul_assoc]

end General

section Fields

variable {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']

theorem pow_finrank_eq_one (s : F' ≃ₐ[F] F') : s ^ Module.finrank F F' = 1 := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  rw [← IsGalois.card_aut_eq_finrank]
  exact pow_card_eq_one'

theorem fixed_iff (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (x : F') :
    s x = x ↔ x ∈ Set.range (algebraMap F F') := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  constructor
  · intro hx
    rw [← IntermediateField.mem_bot, ← IsGalois.fixedField_top, IntermediateField.mem_fixedField_iff]
    intro t _
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hs t)
    have h1 : ∀ m : ℕ, (s ^ m) x = x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
    have h2 : ∀ m : ℕ, (s⁻¹ ^ m) x = x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, AlgEquiv.mul_apply]
        have : s⁻¹ x = x := by
          conv_lhs => rw [← hx]
          exact s.symm_apply_apply x
        rw [this, ih]
    cases k with
    | ofNat m => simpa using h1 m
    | negSucc m => rw [zpow_negSucc, ← inv_pow]; exact h2 (m + 1)
  · rintro ⟨a, rfl⟩
    exact s.commutes a

end Fields

theorem main : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ n : ℕ, (∀ x : GL (Fin n) F', galAct F F' n s x = x ↔ ∃ y, incl F F' n y = x) ∧ Function.Injective (incl F F' n) ∧ (∀ δ y : GL (Fin n) F', nrm s (y⁻¹ * δ * galAct F F' n s y) = y⁻¹ * nrm s δ * y) ∧ (∀ δ : GL (Fin n) F', δ * galAct F F' n s (nrm s δ) = nrm s δ * δ) ∧ ∀ δ ε : GL (Fin n) F', (∀ t u : F' ≃ₐ[F] F', Commute (galAct F F' n t δ) (galAct F F' n u ε)) → nrm s (δ * ε) = nrm s δ * nrm s ε := by
  intro F F' _ _ _ _ s hs n
  have hl := pow_finrank_eq_one s
  have hinj : Function.Injective (algebraMap F F') := (algebraMap F F').injective
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have he : ∀ i j, s ((x : Matrix (Fin n) (Fin n) F') i j) = (x : Matrix (Fin n) (Fin n) F') i j := by
        intro i j
        have := congrArg (fun z : GL (Fin n) F' => (z : Matrix (Fin n) (Fin n) F') i j) hx
        simpa [galAct_apply, gal] using this
      choose M0 hM using fun i j => (fixed_iff s hs _).1 (he i j)
      let M : Matrix (Fin n) (Fin n) F := Matrix.of M0
      have hdet : (algebraMap F F') (M.det) = (x : Matrix (Fin n) (Fin n) F').det := by
        rw [RingHom.map_det]
        congr 1
        ext i j
        exact hM i j
      have hu : IsUnit M := by
        rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
        intro h0
        have : (x : Matrix (Fin n) (Fin n) F').det = 0 := by rw [← hdet, h0, map_zero]
        exact (Matrix.GeneralLinearGroup.det_ne_zero x) this
      refine ⟨hu.unit, ?_⟩
      ext i j
      simp [incl, gal, M, hM]
    · rintro ⟨y, rfl⟩
      ext i j
      simp [galAct_apply, gal, incl]
  · intro a b hab
    ext i j
    have := congrArg (fun z : GL (Fin n) F' => (z : Matrix (Fin n) (Fin n) F') i j) hab
    exact hinj (by simpa [incl, gal] using this)
  · intro δ y
    unfold nrm
    rw [nrmG_twConj, hl, map_one, MulAut.one_apply]
  · intro δ
    unfold nrm
    rw [mul_map_nrmG, hl, map_one, MulAut.one_apply]
  · intro δ ε h
    unfold nrm
    exact nrmG_mul _ _ _ _ _ fun i j => h _ _

end GlobalTheory.Shin.NrmBasic

end
end

