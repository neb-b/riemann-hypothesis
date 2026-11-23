module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteOfFinite
section
open IsLocalRing TensorProduct

namespace GlobalTheory.AdicCompleteFinite

theorem isPrecomplete_of_finite {R M : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨x, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r m =>
    obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I R r
    refine ⟨a • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion I R) a (AdicCompletion.of I M m)).symm
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩

theorem isPrecomplete_of_pow_le {S : Type} [CommRing S] {I J : Ideal S} (hIJ : I ≤ J) {k : ℕ}
    (hk : J ^ k ≤ I) [h : IsPrecomplete I S] : IsPrecomplete J S := by
  have hk' : J ^ (k + 1) ≤ I := (Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk
  refine ⟨fun f hf => ?_⟩
  have hg : ∀ {m n : ℕ}, m ≤ n →
      f ((k + 1) * m) ≡ f ((k + 1) * n) [SMOD (I ^ m • ⊤ : Submodule S S)] := by
    intro m n hmn
    refine (hf (Nat.mul_le_mul_left (k + 1) hmn)).mono ?_
    refine Submodule.smul_mono_left ?_
    rw [pow_mul]
    exact Ideal.pow_right_mono hk' m
  obtain ⟨L, hL⟩ := IsPrecomplete.prec h (f := fun n => f ((k + 1) * n)) hg
  refine ⟨L, fun n => ?_⟩
  refine (hf (Nat.le_mul_of_pos_left n (Nat.succ_pos k))).trans ?_
  exact (hL n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n))

theorem isAdicComplete_of_finite (R S : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [CommRing S] [IsLocalRing S] [Algebra R S]
    [Module.Finite R S] : IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
  haveI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hcomap : (maximalIdeal S).comap (algebraMap R S) = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal S))
  have hle : (maximalIdeal R).map (algebraMap R S) ≤ maximalIdeal S :=
    Ideal.map_le_iff_le_comap.mpr hcomap.ge
  have hrad : maximalIdeal S ≤ ((maximalIdeal R).map (algebraMap R S)).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hP, hprime⟩
    have h1 : maximalIdeal R ≤ P.comap (algebraMap R S) := Ideal.map_le_iff_le_comap.mp hP
    have h2 : P.comap (algebraMap R S) = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ hprime.ne_top) h1).symm
    have h3 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R S)
        (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) P
        (h2 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h3).ge
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  haveI : IsPrecomplete (maximalIdeal R) S := isPrecomplete_of_finite _
  haveI : IsPrecomplete ((maximalIdeal R).map (algebraMap R S)) S :=
    IsPrecomplete.map_algebraMap_iff.mpr this
  haveI : IsPrecomplete (maximalIdeal S) S := isPrecomplete_of_pow_le hle hk
  exact {}

end GlobalTheory.AdicCompleteFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeLatticeOfBasisAfterExtension
section
open TensorProduct

namespace GlobalTheory

theorem isBaseChange_subtype_of_basis_after_extension : ∀ (S A EE O W RW D Y : Type) [CommRing S] [CommRing A] [CommRing EE] [CommRing O] [CommRing W] [CommRing RW] [Algebra O A] [Algebra A EE] [Algebra O EE] [IsScalarTower O A EE] [Algebra O RW] [AddCommGroup D] [Module EE D] [Module A D] [IsScalarTower A EE D] [AddCommGroup Y] [Module RW Y] (a : S →+* A) (ι : EE →ₐ[O] RW) (c : W →+* RW) (jD : D →+ Y), Function.Injective ι → (∀ e, IsUnit (ι e) → IsUnit e) → (∀ (e : EE) (x : D), jD (e • x) = ι e • jD x) → (∀ s, ι (algebraMap A EE (a s)) ∈ Set.range c) → ∀ (d r : ℕ) (o : Fin d → O), (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j) → Nonempty (Module.Basis (Fin r) EE D) → ∀ (q : ℕ) (x : Fin q → D), q = d * r → (∀ y : Y, ∃! w : Fin q → W, y = ∑ i, c (w i) • jD (x i)) → ∀ N : Submodule A D, (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → IsBaseChange EE N.subtype := by
  intro S A EE O W RW D Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a ι c jD hinj hunit hjD ha d r o ho
    ⟨b⟩ q x hq huniq N hN
  classical
  subst hq
  have hxN : ∀ i, x i ∈ N := by
    intro i
    refine (hN _).2 ⟨Pi.single i 1, ?_⟩
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  have hjsum : ∀ e : Fin (d * r) → EE, ∀ v : Fin (d * r) → D,
      jD (∑ i, e i • v i) = ∑ i, ι (e i) • jD (v i) := by
    intro e v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hjD _ _

  have hspan : ∀ y : D, y ∈ Submodule.span EE (Set.range x) := by
    choose e' he' hdec using ho
    choose w' hw' using he'
    let u : Fin (d * r) → D := fun l =>
      algebraMap O EE (o (finProdFinEquiv.symm l).1) • b (finProdFinEquiv.symm l).2
    let C' : Matrix (Fin (d * r)) (Fin (d * r)) EE := fun i l =>
      e' (b.repr (x i) (finProdFinEquiv.symm l).2) (finProdFinEquiv.symm l).1
    let C : Matrix (Fin (d * r)) (Fin (d * r)) W := fun i l =>
      w' (b.repr (x i) (finProdFinEquiv.symm l).2) (finProdFinEquiv.symm l).1
    have hCC : ∀ i l, c (C i l) = ι (C' i l) := fun i l => hw' _ _
    have hx : ∀ i, x i = ∑ l, C' i l • u l := by
      intro i
      rw [← finProdFinEquiv.sum_comp]
      simp only [C', u, Equiv.symm_apply_apply]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      conv_lhs => rw [← b.sum_repr (x i)]
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [hdec (b.repr (x i) k)]
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, Algebra.smul_def, mul_comm]
    choose B hB using fun l => (huniq (jD (u l))).exists
    have hCB : C * Matrix.of B = 1 := by
      ext i m
      have h1 : jD (x i) = ∑ m, c ((C * Matrix.of B) i m) • jD (x m) := by
        conv_lhs => rw [hx i, hjsum]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_smul, Matrix.of_apply]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hB l, Finset.smul_sum, ← hCC]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [smul_smul]
      have h2 : jD (x i) = ∑ m, c ((1 : Matrix _ _ W) i m) • jD (x m) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [Matrix.one_apply_ne hj.symm]
        · simp
      exact congrFun ((huniq _).unique h1 h2) m
    have hdetC : IsUnit C.det := Matrix.isUnit_det_of_right_inverse hCB
    have hdetC' : IsUnit C'.det := by
      apply hunit
      have h1 : ι C'.det = c C.det := by
        rw [RingHom.map_det, AlgHom.map_det]
        congr 1
        ext i l
        simp [hCC]
      rw [h1]
      exact hdetC.map c
    have hu : ∀ l, u l ∈ Submodule.span EE (Set.range x) := by
      intro l
      have h1 : u l = ∑ i, C'⁻¹ l i • x i := by
        have h2 : ∑ i, C'⁻¹ l i • x i = ∑ m, (C'⁻¹ * C') l m • u m := by
          simp only [Matrix.mul_apply, Finset.sum_smul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hx i, Finset.smul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [smul_smul]
        rw [h2, Matrix.nonsing_inv_mul _ hdetC', Finset.sum_eq_single l]
        · simp
        · intro j _ hj
          simp [Matrix.one_apply_ne hj.symm]
        · simp
      rw [h1]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hb : ∀ k, b k ∈ Submodule.span EE (Set.range x) := by
      intro k
      have h1 : b k = ∑ j, e' 1 j • u (finProdFinEquiv (j, k)) := by
        conv_lhs => rw [← one_smul EE (b k), hdec 1, Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [u, Equiv.symm_apply_apply]
        rw [smul_smul, Algebra.smul_def, mul_comm]
      rw [h1]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hu _)
    intro y
    rw [← b.sum_repr y]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hb k)

  have hnf : ∀ t : EE ⊗[A] N, ∃ e : Fin (d * r) → EE, (∀ i, ι (e i) ∈ c.range) ∧
      t = ∑ i, e i ⊗ₜ[A] (⟨x i, hxN i⟩ : N) := by
    let P : AddSubmonoid (EE ⊗[A] N) :=
      { carrier := {t | ∃ e : Fin (d * r) → EE, (∀ i, ι (e i) ∈ c.range) ∧
          t = ∑ i, e i ⊗ₜ[A] (⟨x i, hxN i⟩ : N)}
        zero_mem' := ⟨0, fun i => by simp, by simp⟩
        add_mem' := by
          rintro _ _ ⟨e₁, h₁, rfl⟩ ⟨e₂, h₂, rfl⟩
          refine ⟨e₁ + e₂, fun i => ?_, ?_⟩
          · rw [Pi.add_apply, map_add (f := _)]
            exact add_mem (h₁ i) (h₂ i)
          · simp [TensorProduct.add_tmul, Finset.sum_add_distrib] }
    have hP : ∀ (e : EE) (n : N), ι e ∈ c.range → e ⊗ₜ[A] n ∈ P := by
      intro e n he
      obtain ⟨s, hs⟩ := (hN n).1 n.2
      have hn : n = ∑ i, a (s i) • (⟨x i, hxN i⟩ : N) := by
        apply Subtype.ext
        rw [hs]
        simp
      refine ⟨fun i => a (s i) • e, fun i => ?_, ?_⟩
      · beta_reduce
        rw [Algebra.smul_def, map_mul]
        exact mul_mem (ha (s i)) he
      · rw [hn, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [TensorProduct.smul_tmul]
    intro t
    change t ∈ P
    induction t using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add _ _ h₁ h₂ => exact add_mem h₁ h₂
    | tmul e n =>
      obtain ⟨e', he', hdec⟩ := ho e
      rw [hdec, TensorProduct.sum_tmul]
      refine sum_mem fun j _ => ?_
      rw [← algebraMap_smul A (o j) (e' j), TensorProduct.smul_tmul]
      exact hP _ _ (he' j)
  have hbij : Function.Bijective (N.subtype.liftBaseChange EE) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro t ht
      obtain ⟨e, he, rfl⟩ := hnf t
      choose w hw using he
      have h1 : ∑ i, e i • x i = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [map_sum, LinearMap.liftBaseChange_tmul] using ht
      have h2 : (0 : Y) = ∑ i, c (w i) • jD (x i) := by
        simp only [hw]
        rw [← hjsum, h1, map_zero]
      have h3 : (0 : Y) = ∑ i, c ((0 : Fin (d * r) → W) i) • jD (x i) := by simp
      have h4 : w = 0 := (huniq 0).unique h2 h3
      have h5 : ∀ i, e i = 0 := by
        intro i
        apply hinj
        rw [← hw, h4]
        simp
      simp [h5]
    · rw [← LinearMap.range_eq_top, eq_top_iff]
      intro y _
      refine Submodule.span_le.2 ?_ (hspan y)
      rintro _ ⟨i, rfl⟩
      exact ⟨1 ⊗ₜ[A] (⟨x i, hxN i⟩ : N), by simp [LinearMap.liftBaseChange_tmul]⟩
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hbij) fun n => ?_
  simp [LinearMap.liftBaseChange_tmul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleOfAnisotropicFormHighestWeight
section
namespace GlobalTheory.DownLift

theorem abstract_irreducible_of_highestWeight (V : Type) [AddCommGroup V] [Module ℂ V]
    (U : Submodule ℂ V) (hfin : FiniteDimensional ℂ U) (J : Type) (E : J → Module.End ℂ V)
    (st : J → J) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (Hw : V → Prop)
    (hU : ∀ j, ∀ x ∈ U, E j x ∈ U) (han : ∀ x ∈ U, B x x = 0 → x = 0)
    (hadj : ∀ j x y, B (E j x) y = B x (E (st j) y)) (hst : ∀ j, st (st j) = j)
    (hex : ∀ T : Submodule ℂ V, T ≤ U → T ≠ ⊥ → (∀ j, ∀ x ∈ T, E j x ∈ T) →
      ∃ x ∈ T, x ≠ 0 ∧ Hw x)
    (hprop : ∀ x y, x ∈ U → y ∈ U → Hw x → Hw y → x ≠ 0 → ∃ c : ℂ, y = c • x)
    (S : Submodule ℂ V) (hSU : S ≤ U) (hS : S ≠ ⊥) (hSE : ∀ j, ∀ x ∈ S, E j x ∈ S) :
    S = U := by
  classical
  let P : Submodule ℂ V := U ⊓ ⨅ s : S, LinearMap.ker (B (s : V))
  have hP : ∀ y, y ∈ P ↔ y ∈ U ∧ ∀ s ∈ S, B s y = 0 := by
    intro y
    simp [P, Submodule.mem_iInf]
  have hPbot : P = ⊥ := by
    by_contra hne
    have hPE : ∀ j, ∀ x ∈ P, E j x ∈ P := by
      intro j y hy
      rw [hP] at hy ⊢
      refine ⟨hU j y hy.1, fun s hs => ?_⟩
      have h := hadj (st j) s y
      rw [hst] at h
      rw [← h]
      exact hy.2 _ (hSE _ _ hs)
    obtain ⟨y, hyP, hy0, hyw⟩ := hex P inf_le_left hne hPE
    obtain ⟨x, hxS, hx0, hxw⟩ := hex S hSU hS hSE
    rw [hP] at hyP
    obtain ⟨c, hc⟩ := hprop x y (hSU hxS) hyP.1 hxw hyw hx0
    have hyS : y ∈ S := hc ▸ S.smul_mem c hxS
    exact hy0 (han y hyP.1 (hyP.2 y hyS))
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSU
  let b := Module.finBasis ℂ S
  let φ : U →ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    LinearMap.pi fun i => (B (b i : V)).comp U.subtype
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    have hy' : ∀ i, B (b i : V) (y : V) = 0 := fun i => congrFun (LinearMap.mem_ker.mp hy) i
    have hyP : (y : V) ∈ P := by
      rw [hP]
      refine ⟨y.2, fun s hs => ?_⟩
      have h := congrArg (fun z : S => (z : V)) (b.sum_repr ⟨s, hs⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy', smul_zero]
    rw [hPbot, Submodule.mem_bot] at hyP
    rw [Submodule.mem_bot]
    exact Subtype.ext hyP
  have hle := LinearMap.finrank_le_finrank_of_injective hφ
  rw [Module.finrank_fin_fun] at hle
  exact Submodule.eq_of_le_of_finrank_le hSU hle

end GlobalTheory.DownLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNilpotentResidueToMatrixMulLeft
section
open Polynomial

namespace GlobalTheory

theorem isNilpotent_residue_toMatrix_mulLeft : ∀ (R S : Type) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S] (n : ℕ) (b : Module.Basis (Fin n) R S) (t : S), t ∈ IsLocalRing.maximalIdeal S → IsNilpotent ((LinearMap.toMatrix b b (LinearMap.mulLeft R t)).map (IsLocalRing.residue R)) := by
  intro R S _ _ _ _ _ n b t ht
  let φ : S →ₐ[R] Matrix (Fin n) (Fin n) R :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lmul R S)
  have hφ : ∀ s, φ s = LinearMap.toMatrix b b (LinearMap.mulLeft R s) := by
    intro s; ext i j
    simp [φ, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  set N := LinearMap.toMatrix b b (LinearMap.mulLeft R t) with hN
  set Nb := N.map (IsLocalRing.residue R) with hNb
  have hcp : Nb.charpoly ≠ 0 := (Matrix.charpoly_monic Nb).ne_zero
  obtain ⟨hb, hfac, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Nb.charpoly hcp 0
  have h0 : hb.eval 0 ≠ 0 := by
    intro h; apply hndvd; rw [dvd_iff_isRoot]; exact h
  obtain ⟨h, rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue R)
    IsLocalRing.residue_surjective hb
  have hu0 : IsUnit (h.coeff 0) := by
    by_contra hc
    apply h0
    rw [← coeff_zero_eq_eval_zero, coeff_map]
    exact (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 hc)
  obtain ⟨q, hq⟩ := X_dvd_sub_C (p := h)
  have hsplit : aeval t h = algebraMap R S (h.coeff 0) + t * aeval t q := by
    have : h = C (h.coeff 0) + X * q := by rw [← hq]; ring
    conv_lhs => rw [this]
    simp
  have hut : IsUnit (aeval t h) := by
    rw [hsplit]
    by_contra hc
    have h1 : algebraMap R S (h.coeff 0) + t * aeval t q ∈ IsLocalRing.maximalIdeal S :=
      (IsLocalRing.mem_maximalIdeal _).2 hc
    have h2 : t * aeval t q ∈ IsLocalRing.maximalIdeal S :=
      Ideal.mul_mem_right _ _ ht
    have h3 : algebraMap R S (h.coeff 0) ∈ IsLocalRing.maximalIdeal S := by
      have := Ideal.sub_mem _ h1 h2
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _).1 h3 (hu0.map (algebraMap R S))
  have huN : IsUnit (aeval N h) := by
    have := hut.map φ
    rwa [← Polynomial.aeval_algHom_apply, hφ] at this
  have hmap : (IsLocalRing.residue R).mapMatrix (aeval N h) = aeval Nb (h.map (IsLocalRing.residue R)) := by
    rw [aeval_def, aeval_def, hom_eval₂, eval₂_map]
    congr 1
    ext r i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply]
    split_ifs <;> simp
  have huNb : IsUnit (aeval Nb (h.map (IsLocalRing.residue R))) := by
    rw [← hmap]; exact huN.map _
  have hCH := Matrix.aeval_self_charpoly Nb
  rw [hfac, C_0, sub_zero, map_mul, map_pow, aeval_X] at hCH
  exact ⟨_, (huNb.mul_left_eq_zero).1 hCH⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTotallyComplexOfPrimitiveRootThreeLe
section
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem isTotallyComplex_of_primitiveRoot (K : Type) [Field K] [NumberField K] (ζ : K) (m : ℕ)
    (hζ : IsPrimitiveRoot ζ m) (hm : 3 ≤ m) : NumberField.IsTotallyComplex K := by
  rw [NumberField.isTotallyComplex_iff]
  intro v
  by_contra hc
  have hr : v.IsReal := InfinitePlace.not_isComplex_iff_isReal.mp hc
  set ψ : K →+* ℝ := InfinitePlace.embedding_of_isReal hr
  have hψ : IsPrimitiveRoot (ψ ζ) m := hζ.map_of_injective ψ.injective
  have hm0 : m ≠ 0 := by omega
  have h1 : ψ ζ ^ m = 1 := hψ.pow_eq_one
  have h2 : ψ ζ ^ 2 = 1 := by
    rcases (pow_eq_one_iff_of_ne_zero hm0).mp h1 with h | ⟨h, _⟩ <;> rw [h] <;> norm_num
  have h3 : ψ (ζ ^ 2) = ψ 1 := by rw [map_pow, h2, map_one]
  have h4 : ζ ^ 2 = 1 := ψ.injective h3
  have h5 : m ∣ 2 := hζ.pow_eq_one_iff_dvd 2 |>.mp h4
  have := Nat.le_of_dvd (by norm_num) h5
  omega

theorem tcroot : ∀ (K : Type) [Field K] [NumberField K] (ζ : K) (m : ℕ), IsPrimitiveRoot ζ m → 3 ≤ m →
    NumberField.IsTotallyComplex K :=
  fun K _ _ ζ m hζ hm => isTotallyComplex_of_primitiveRoot K ζ m hζ hm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KroneckerTransposeMulVec
section
noncomputable section

open Matrix

namespace GlobalTheory.PMon

variable {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def vecM {S : Type*} (X : Matrix a b S) : a × b → S := fun p => X p.1 p.2

def homUnit (A : GL a R) (B : GL b R) : GL (a × b) R where
  val := Matrix.kroneckerMap (· * ·) (A : Matrix a a R) ((B⁻¹ : GL b R) : Matrix b b R)ᵀ
  inv := Matrix.kroneckerMap (· * ·) ((A⁻¹ : GL a R) : Matrix a a R) (B : Matrix b b R)ᵀ
  val_inv := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul]
    simp [Matrix.one_kronecker_one]
  inv_val := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul]
    simp [Matrix.one_kronecker_one]

theorem homUnit_val (A : GL a R) (B : GL b R) :
    ((homUnit A B : GL (a × b) R) : Matrix (a × b) (a × b) R) =
      Matrix.kroneckerMap (· * ·) (A : Matrix a a R) ((B⁻¹ : GL b R) : Matrix b b R)ᵀ := rfl

theorem kronecker_transpose_mulVec {S : Type*} [CommRing S] (A : Matrix a a S) (C : Matrix b b S) (X : Matrix a b S) :
    (Matrix.kroneckerMap (· * ·) A Cᵀ).mulVec (vecM X) = vecM (A * X * C) := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [vecM, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
  ring

theorem homUnit_mulVec {S : Type*} [CommRing S] (f : R →+* S) (A : GL a R) (B : GL b R) (X : Matrix a b S) :
    (((homUnit A B : GL (a × b) R) : Matrix (a × b) (a × b) R).map f).mulVec (vecM X) =
      vecM ((A : Matrix a a R).map f * X * ((B⁻¹ : GL b R) : Matrix b b R).map f) := by
  rw [homUnit_val, ← kronecker_transpose_mulVec]
  congr 1
  ext p q
  simp [Matrix.kroneckerMap_apply]

def homRep {G : Type*} [Group G] (ρ₁ : G →* GL a R) (ρ₂ : G →* GL b R) : G →* GL (a × b) R where
  toFun g := homUnit (ρ₁ g) (ρ₂ g)
  map_one' := by
    ext1
    simp [homUnit_val, Matrix.one_kronecker_one]
  map_mul' g h := by
    ext1
    show ((homUnit (ρ₁ (g * h)) (ρ₂ (g * h)) : GL (a × b) R) : Matrix _ _ R) = ((homUnit (ρ₁ g) (ρ₂ g) : GL (a × b) R) : Matrix (a × b) (a × b) R) * ((homUnit (ρ₁ h) (ρ₂ h) : GL (a × b) R) : Matrix (a × b) (a × b) R)
    rw [homUnit_val, homUnit_val, homUnit_val, map_mul, map_mul, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_kronecker_mul]

theorem homRep_apply {G : Type*} [Group G] (ρ₁ : G →* GL a R) (ρ₂ : G →* GL b R) (g : G) :
    homRep ρ₁ ρ₂ g = homUnit (ρ₁ g) (ρ₂ g) := rfl

def extCoc {G : Type*} [Group G] (ρ₂ : G →* GL b R) (c : G → Matrix a b R) (g : G) : a × b → R :=
  vecM (c g * (((ρ₂ g)⁻¹ : GL b R) : Matrix b b R))

theorem vecM_injective {S : Type*} : Function.Injective (vecM : Matrix a b S → a × b → S) := by
  intro X Y h
  ext i j
  exact congrFun h (i, j)

end GlobalTheory.PMon
end
end

