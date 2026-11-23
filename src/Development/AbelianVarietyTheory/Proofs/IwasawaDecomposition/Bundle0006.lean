module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratorSqEqOfSqMemZpowers
section
namespace GlobalTheory

theorem exists_generator_sq_eq_of_sq_mem_zpowers :
    ∀ (p : ℕ), p.Prime → ∀ a : (ZMod p)ˣ,
      (∀ b : (ZMod p)ˣ, b ^ 2 ∈ Subgroup.zpowers (a ^ 2)) →
      ∃ γ : (ZMod p)ˣ, Subgroup.zpowers γ = ⊤ ∧ γ ^ 2 = a ^ 2 := by
  intro p hp a ha
  have := Fact.mk hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hgn : orderOf g = Nat.card (ZMod p)ˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hn0 : 0 < Nat.card (ZMod p)ˣ := Nat.card_pos
  have gen : ∀ γ : (ZMod p)ˣ, orderOf γ = Nat.card (ZMod p)ˣ → Subgroup.zpowers γ = ⊤ :=
    fun γ h => Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, h])
  have hdn : orderOf a ∣ Nat.card (ZMod p)ˣ := orderOf_dvd_natCard a
  have hd0 : 0 < orderOf a := orderOf_pos a
  have key : orderOf (g ^ 2) ∣ orderOf (a ^ 2) := orderOf_dvd_of_mem_zpowers (ha g)
  rw [orderOf_pow' g two_ne_zero, orderOf_pow' a two_ne_zero, hgn] at key
  generalize Nat.card (ZMod p)ˣ = n at *
  generalize hd : orderOf a = d at *
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hn_odd
  · rcases Nat.even_or_odd d with ⟨e, he⟩ | hd_odd
    · refine ⟨a, gen a ?_, rfl⟩
      have h1 : n.gcd 2 = 2 := Nat.gcd_eq_right ⟨m, by omega⟩
      have h2 : d.gcd 2 = 2 := Nat.gcd_eq_right ⟨e, by omega⟩
      rw [h1, h2, show n / 2 = m by omega, show d / 2 = e by omega] at key
      have h3 : e ∣ m := by
        rw [he, hm, ← two_mul, ← two_mul] at hdn
        exact Nat.dvd_of_mul_dvd_mul_left two_pos hdn
      have := Nat.dvd_antisymm key h3
      omega
    · have hcop : d.Coprime 2 := Nat.coprime_two_right.mpr hd_odd
      have h1 : n.gcd 2 = 2 := Nat.gcd_eq_right ⟨m, by omega⟩
      rw [h1, hcop.gcd_eq_one, Nat.div_one, show n / 2 = m by omega] at key
      have h3 : d ∣ m := hcop.dvd_of_dvd_mul_left (by rw [hm] at hdn; rwa [two_mul])
      have hdm : d = m := Nat.dvd_antisymm h3 key
      have hgm : orderOf (g ^ m) = 2 := by
        have := orderOf_pow_orderOf_div (x := g) (by omega) (show 2 ∣ orderOf g from ⟨m, by omega⟩)
        rwa [show orderOf g / 2 = m by omega] at this
      refine ⟨a * g ^ m, gen _ ?_, ?_⟩
      · rw [(Commute.all a (g ^ m)).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hd, hgm]; exact hcop), hgm, hd]
        omega
      · have hg1 : g ^ n = 1 := hgn ▸ pow_orderOf_eq_one g
        rw [mul_pow, ← pow_mul, show m * 2 = n by omega, hg1, mul_one]
  · have hd_odd : Odd d := hn_odd.of_dvd_nat hdn
    refine ⟨a, gen a ?_, rfl⟩
    rw [(Nat.coprime_two_right.mpr hn_odd).gcd_eq_one, (Nat.coprime_two_right.mpr hd_odd).gcd_eq_one,
      Nat.div_one, Nat.div_one] at key
    rw [hd]
    exact Nat.dvd_antisymm hdn key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveAdicCompletionMapOfFinite
section
open IsLocalRing

namespace GlobalTheory

theorem adicCompletion_evalₐ_of_val {R : Type} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    {n : ℕ} (d : R) (hd : x.val n = Submodule.Quotient.mk d) :
    AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) d := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), AdicCompletion.eval_apply]
  erw [hd]
  rfl

theorem adicCompletion_val_of_le {R : Type} [CommRing R] (I : Ideal R) (x : AdicCompletion I R)
    {m n : ℕ} (hmn : m ≤ n) (d : R) (hd : x.val n = Submodule.Quotient.mk d) :
    x.val m = Submodule.Quotient.mk d := by
  rw [← x.prop hmn, hd]
  rfl

theorem adicCompletion_injective_ringHom_of_finite
    (D N : Type) [CommRing D] [CommRing N] [IsNoetherianRing D] [Algebra D N]
    [Module.Finite D N] (hinj : Function.Injective (algebraMap D N)) (J : Ideal D) :
    ∃ f : AdicCompletion J D →+* AdicCompletion (J.map (algebraMap D N)) N,
      Function.Injective f := by
  set φ := algebraMap D N with hφ
  have hle : ∀ n : ℕ, J ^ n ≤ ((J.map φ) ^ n).comap φ := fun n => by
    rw [← Ideal.map_pow]; exact Ideal.le_comap_map
  let g : (n : ℕ) → AdicCompletion J D →+* N ⧸ (J.map φ) ^ n := fun n =>
    (Ideal.quotientMap ((J.map φ) ^ n) φ (hle n)).comp (AdicCompletion.evalₐ J n).toRingHom
  have hg : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow (J.map φ) hmn).comp (g n) = g m := by
    intro m n hmn
    ext x
    obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    have hn := adicCompletion_evalₐ_of_val J x d hd.symm
    have hm := adicCompletion_evalₐ_of_val J x d (adicCompletion_val_of_le J x hmn d hd.symm)
    simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hn, hm,
      Ideal.quotientMap_mk]
    rfl
  refine ⟨AdicCompletion.liftRingHom _ g hg, ?_⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hmap := AdicCompletion.map_injective J (f := Algebra.linearMap D N) hinj
  apply hmap
  rw [map_zero]
  apply AdicCompletion.ext
  intro n
  obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  have h1 := adicCompletion_evalₐ_of_val J x d hd.symm
  have h2 := congrArg (AdicCompletion.evalₐ (J.map φ) n) hx
  rw [AdicCompletion.evalₐ_liftRingHom, map_zero] at h2
  simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1,
    Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at h2
  rw [AdicCompletion.map_val_apply]
  erw [← hd]
  rw [LinearMap.reduceModIdeal_apply]
  refine ((Submodule.Quotient.mk_eq_zero _).2 ?_).trans rfl
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
  exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsotropicDualOfSkewMatrix
section
open Matrix

namespace GlobalTheory

theorem exists_isotropic_dual_of_skew {V : Type*} [AddCommGroup V] [Module ℚ V] {g : ℕ}
    (B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (ε ψ : Fin g → V) (hB : ∀ x y, B x y = -B y x)
    (hε : ∀ i j, B (ε i) (ε j) = 0)
    (hψ : ∀ i j, B (ψ j) (ε i) = if i = j then 1 else 0) :
    ∃ φ : Fin g → V, (∀ i j, B (φ i) (φ j) = 0) ∧
      (∀ i j, B (φ j) (ε i) = if i = j then 1 else 0) ∧
      ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by
  classical
  have h1 : ∀ k l, B (ψ l) (ε k) = if k = l then 1 else 0 := fun k l => hψ k l
  have h2 : ∀ k l, B (ε k) (ψ l) = -(if k = l then 1 else 0) := fun k l => by
    rw [hB, h1]
  refine ⟨fun j => ψ j + ∑ k, (B (ψ j) (ψ k) / 2) • ε k, ?_, ?_, ?_⟩
  · intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hε, h1, h2, mul_zero,
      Finset.sum_const_zero, add_zero, mul_ite, mul_one, mul_neg, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith [hB (ψ i) (ψ j)]
  · intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hε, h1, mul_zero,
      Finset.sum_const_zero, add_zero]
  · intro j
    simp only [add_sub_cancel_left]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem exists_isotropic_dual_of_skew_matrix (r g : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ)
    (ε ψ : Fin g → Fin r → ℚ) (hM : Mqᵀ = -Mq) (hε : ∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0)
    (hψ : ∀ i j, ψ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) :
    ∃ φ : Fin g → Fin r → ℚ, (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) ∧
      (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) ∧
      ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by
  obtain ⟨φ, h₁, h₂, h₃⟩ := exists_isotropic_dual_of_skew (Matrix.toLinearMap₂' ℚ Mq) ε ψ
    (fun x y => by
      simp only [Matrix.toLinearMap₂'_apply']
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM, Matrix.neg_mulVec,
        neg_dotProduct, dotProduct_comm])
    (fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using hε i j)
    (fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using hψ i j)
  exact ⟨φ, fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using h₁ i j,
    fun i j => by simpa only [Matrix.toLinearMap₂'_apply'] using h₂ i j, h₃⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLagrangianContainingIsotropicRat
section
open Matrix

namespace GlobalTheory

open Module

theorem exists_lagrangian_containing_isotropic_rat : ∀ (g r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (I : Submodule ℚ (Fin r → ℚ)), r = 2 * g → Mqᵀ = -Mq → Mq.det ≠ 0 → (∀ x ∈ I, ∀ y ∈ I, x ⬝ᵥ Mq *ᵥ y = 0) → ∃ L : Submodule ℚ (Fin r → ℚ), I ≤ L ∧ (∀ x ∈ L, ∀ y ∈ L, x ⬝ᵥ Mq *ᵥ y = 0) ∧ Module.finrank ℚ L = g := by
  classical
  intro g r M I hr hskew hdet hI
  set B : LinearMap.BilinForm ℚ (Fin r → ℚ) := Matrix.toBilin' M with hBdef
  have hB : ∀ v w, B v w = v ⬝ᵥ M *ᵥ w := fun v w => by
    simp [hBdef, Matrix.toBilin'_apply']
  have hskewB : ∀ v w, B v w = - B w v := by
    intro v w
    rw [hB, hB, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hskew, Matrix.neg_mulVec,
      neg_dotProduct, dotProduct_comm]
  have hBalt : ∀ v, B v v = 0 := fun v => by have := hskewB v v; linarith
  have hnd : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' M hdet
  have hIB : ∀ x ∈ I, ∀ y ∈ I, B x y = 0 := fun x hx y hy => by rw [hB]; exact hI x hx y hy
  let P : ℕ → Prop := fun n => ∃ L : Submodule ℚ (Fin r → ℚ), I ≤ L ∧
    (∀ x ∈ L, ∀ y ∈ L, B x y = 0) ∧ finrank ℚ L = n
  have PI : P (finrank ℚ I) := ⟨I, le_rfl, hIB, rfl⟩
  have hIr : finrank ℚ I ≤ r := by simpa using Submodule.finrank_le I
  obtain ⟨L, hIL, hLiso, hLdim⟩ : P (Nat.findGreatest P r) := Nat.findGreatest_spec hIr PI
  have hmax : ∀ v, (∀ l ∈ L, B v l = 0) → v ∈ L := by
    intro v hvL
    by_contra hv
    have hlt : L < L ⊔ Submodule.span ℚ {v} := lt_of_le_of_ne le_sup_left (fun h => hv (by
      rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
    have hiso : ∀ x ∈ L ⊔ Submodule.span ℚ {v}, ∀ y ∈ L ⊔ Submodule.span ℚ {v}, B x y = 0 := by
      intro x hx y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hb'
      have h1 := hLiso a ha a' ha'
      have h2 := hvL a' ha'
      have h3 : B a v = 0 := by rw [hskewB, hvL a ha, neg_zero]
      have h4 := hBalt v
      simp [map_add (f := _), map_smul, h1, h2, h3, h4]
    have hP : P (finrank ℚ ↥(L ⊔ Submodule.span ℚ {v})) :=
      ⟨_, hIL.trans le_sup_left, hiso, rfl⟩
    have h5 := Nat.le_findGreatest (by simpa using Submodule.finrank_le (L ⊔ Submodule.span ℚ {v})) hP
    have h6 := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hLo : B.orthogonal L = L := by
    apply le_antisymm
    · intro x hx
      exact hmax x (fun l hl => by rw [hskewB, hx l hl, neg_zero])
    · intro x hx l hl
      exact hLiso l hl x hx
  have hdim := LinearMap.BilinForm.finrank_orthogonal hnd L
  rw [hLo] at hdim
  have hV : finrank ℚ (Fin r → ℚ) = r := by simp
  rw [hV] at hdim
  have hLr : finrank ℚ L ≤ r := by simpa using Submodule.finrank_le L
  refine ⟨L, hIL, fun x hx y hy => by rw [← hB]; exact hLiso x hx y hy, ?_⟩
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLimitSeries
section
namespace GlobalTheory.LimitSeriesPowSmul

theorem mem_pow_smul_top_iff {R : Type} [CommRing R] (p : R) (n : ℕ) (x : R) :
    x ∈ ((Ideal.span {p}) ^ n • (⊤ : Submodule R R)) ↔ p ^ n ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem exists_limit_series {R : Type} [CommRing R] (p : R) [IsPrecomplete (Ideal.span {p}) R]
    (f : ℕ → R) : ∃ (L : R), ∀ (k : ℕ), p ^ k ∣ ∑ i ∈ Finset.range k, p ^ i * f i - L := by
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p})
    (fun k => ∑ i ∈ Finset.range k, p ^ i * f i) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_pow_smul_top_iff, ← Finset.sum_range_add_sum_Ico _ hmn,
        sub_add_cancel_left, dvd_neg]
      refine Finset.dvd_sum fun i hi => ?_
      exact Dvd.dvd.mul_right (pow_dvd_pow p (Finset.mem_Ico.mp hi).1) _)
  exact ⟨L, fun k => (mem_pow_smul_top_iff p k _).mp ((SModEq.sub_mem).mp (hL k))⟩

theorem target : ∀ {R : Type} [inst : CommRing R] (p : R) [IsPrecomplete (Ideal.span {p}) R]
    (f : ℕ → R), ∃ (L : R), ∀ (k : ℕ), p ^ k ∣ ∑ i ∈ Finset.range k, p ^ i * f i - L :=
  by
  intro R _ p _ f
  exact exists_limit_series p f

end GlobalTheory.LimitSeriesPowSmul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinearMapOfGram
section
namespace GlobalTheory.GramLinearMap

theorem gram_comb {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
    {P' : Type} [AddCommGroup P'] [Module ℂ P'] {B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ} {U : Type}
    (f : U → P) (f' : U → P') {c d : ℂ}
    (h : ∀ u v : U, B (f u) (f v) * c = d * B' (f' u) (f' v)) (x y : U →₀ ℂ) :
    B (Finsupp.linearCombination ℂ f x) (Finsupp.linearCombination ℂ f y) * c =
      d * B' (Finsupp.linearCombination ℂ f' x) (Finsupp.linearCombination ℂ f' y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add (f := _), LinearMap.add_apply, add_mul, mul_add, h₁, h₂]
  | single u a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add (f := _), add_mul, mul_add, h₁, h₂]
    | single v b =>
      simp only [Finsupp.linearCombination_single, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, RingHom.id_apply]
      linear_combination (b * (starRingEnd ℂ) a) * h u v

theorem exists_linearMap_of_gram {P : Type} [AddCommGroup P] [Module ℂ P]
    {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
    {P' : Type} [AddCommGroup P'] [Module ℂ P'] {B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ} {U : Type}
    (f : U → P) (f' : U → P') (hB : ∀ y : P, B y y = 0 → y = 0) {c d : ℂ} (hc : c ≠ 0)
    (h : ∀ u v : U, B (f u) (f v) * c = d * B' (f' u) (f' v)) :
    ∃ ψ : P' →ₗ[ℂ] P, ∀ u : U, ψ (f' u) = f u := by
  set T := Finsupp.linearCombination ℂ f with hT
  set T' := Finsupp.linearCombination ℂ f' with hT'
  have hker : ∀ x, T' x = 0 → T x = 0 := by
    intro x hx
    apply hB
    have := gram_comb f f' h x x
    rw [← hT, ← hT', hx] at this
    simpa [hc] using this
  obtain ⟨g, hg⟩ := T'.rangeRestrict.exists_rightInverse_of_surjective T'.range_rangeRestrict
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend (T ∘ₗ g)
  refine ⟨ψ, fun u => ?_⟩
  have h1 : T' (Finsupp.single u 1) = f' u := by simp [hT']
  have h2 : T (Finsupp.single u 1) = f u := by simp [hT]
  let z : LinearMap.range T' := ⟨f' u, _, h1⟩
  have h3 : ψ (f' u) = T (g z) := LinearMap.congr_fun hψ z
  have h4 : T' (g z) = f' u := congrArg Subtype.val (LinearMap.congr_fun hg z)
  have h5 : T (g z - Finsupp.single u 1) = 0 := hker _ (by rw [map_sub, h4, h1, sub_self])
  rw [map_sub, sub_eq_zero] at h5
  rw [h3, h5, h2]

end GlobalTheory.GramLinearMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMatrixBasisLatticeUpToDenominatorNotMem
section
set_option autoImplicit false
noncomputable section

open NumberField IsDedekindDomain Matrix Module
open scoped BigOperators nonZeroDivisors

namespace GlobalTheory.LatticeLocBasis

theorem exists_basis_up_to_fintype {O A E : Type} [CommRing O] [CommRing A] [IsDomain A] [Field E] [Algebra O A]
    [Algebra A E] [Algebra O E] [IsScalarTower O A E] (S : Submonoid O) [IsLocalization S A] [IsFractionRing A E]
    [IsPrincipalIdealRing A] {n : Type} [Fintype n] (L : Submodule O (n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (n → E)) = ⊤) :
    ∃ (s : S) (b : n → n → E), LinearIndependent E b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, (s : O) • w ∈ Submodule.span O (Set.range b) := by
  classical
  set M : Submodule A (n → E) := Submodule.span A (L : Set (n → E)) with hM
  have : Submodule.IsFullLattice E M :=
    { toIsLattice := Submodule.IsLattice.of_fg E <| by
        obtain ⟨s, hs⟩ := hfg
        refine ⟨s, ?_⟩
        rw [hM, ← hs, Submodule.span_span_of_tower]
      span_eq_top := by rw [hM, Submodule.span_span_of_tower, hsp] }
  have hrk : Module.finrank A M = Fintype.card n := by
    simpa using ((Submodule.IsFullLattice.finrank_eq E M).trans (Module.finrank_fintype_fun_eq_card E))
  have := Submodule.IsLattice.free E M
  have := Submodule.IsLattice.finite E M
  let c : Basis n A M := (Module.finBasisOfFinrankEq A M hrk).reindex (Fintype.equivFin n).symm
  have hc : ∀ i, ∃ t : S, (t : O) • (c i : n → E) ∈ L := fun i => by
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span S A (L : Set (n → E)) _ (c i).2
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using hc
  let u : n → Aˣ := fun i => (IsLocalization.map_units A (t i)).unit
  let c' : Basis n A M := c.unitsSMul u
  have hc' : ∀ i, (c' i : n → E) = (t i : O) • (c i : n → E) := fun i => by
    simp only [c', Basis.unitsSMul_apply, u, Units.smul_def, IsUnit.unit_spec, algebraMap_smul,
      Submodule.coe_smul_of_tower]
  let b : n → n → E := fun i => (c' i : n → E)
  have hli : LinearIndependent E b := by
    have h : b = c'.extendOfIsFullLattice E := funext fun i => by simp [b]
    rw [h]
    exact (c'.extendOfIsFullLattice E).linearIndependent
  have hspanA : Submodule.span A (Set.range b) = M := by
    have : Set.range b = M.subtype '' Set.range c' := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, c'.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hw : ∀ w ∈ L, ∃ r : S, (r : O) • w ∈ Submodule.span O (Set.range b) := fun w hw => by
    obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span S A (Set.range b) w
      (hspanA ▸ Submodule.subset_span hw)
    exact ⟨r, hr⟩
  obtain ⟨G, hG⟩ := hfg
  choose! r hr using hw
  refine ⟨∏ x ∈ G, r x, b, hli, fun i => by simpa only [b, hc'] using ht i, fun w hw => ?_⟩
  rw [← hG] at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    have hy' : y ∈ G := hy
    rw [← Finset.prod_erase_mul G r hy', Submonoid.coe_mul, mul_smul]
    exact Submodule.smul_mem _ _ (hr y (hG ▸ Submodule.subset_span hy))
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy

theorem exists_matrix_up_to_notMem : ∀ (K : Type) [Field K] [NumberField K] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule (𝓞 K) (n → K)) (𝔭 : HeightOneSpectrum (𝓞 K)), L.FG → Submodule.span K (L : Set (n → K)) = ⊤ → ∃ g : Matrix n n K, IsUnit g.det ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ x ∈ L, ∀ i, (t : K) * (g⁻¹ *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ j, (t : K) • (fun i => g i j) ∈ L := by
  intro K _ _ n _ _ L 𝔭 hfg hsp
  have hp := 𝔭.isPrime
  have hS : 𝔭.asIdeal.primeCompl ≤ (𝓞 K)⁰ := Ideal.primeCompl_le_nonZeroDivisors _
  let A := Localization.subalgebra K 𝔭.asIdeal.primeCompl hS
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) 𝔭.ne_bot A
  obtain ⟨⟨s, hs⟩, b, hli, hb, hw⟩ := exists_basis_up_to_fintype (A := A) 𝔭.asIdeal.primeCompl L hfg hsp
  let g : Matrix n n K := Matrix.of fun i j => b j i
  have hcol : g.col = b := by funext j i; rfl
  have hunit : IsUnit g := Matrix.linearIndependent_cols_iff_isUnit.1 (hcol ▸ hli)
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det _).1 hunit
  refine ⟨g, hdet, s, hs, ?_, ?_⟩
  · intro x hx i
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hw x hx)
    have hg : g *ᵥ (fun i => algebraMap (𝓞 K) K (a i)) = (s : K) • x := by
      have : (s : K) • x = s • x := algebraMap_smul K s x
      rw [this]
      change _ = ((⟨s, hs⟩ : 𝔭.asIdeal.primeCompl) : 𝓞 K) • x
      rw [← ha]
      funext i
      simp only [Matrix.mulVec, dotProduct, g, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    have h2 : (s : K) • (g⁻¹ *ᵥ x) = fun i => algebraMap (𝓞 K) K (a i) := by
      rw [← Matrix.mulVec_smul, ← hg, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
    exact ⟨a i, (congrFun h2 i).symm⟩
  · intro j
    have : (s : K) • (fun i => g i j) = s • b j := algebraMap_smul K s (b j)
    rw [this]
    exact L.smul_mem _ (hb j)

end GlobalTheory.LatticeLocBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulEqInteger
section
namespace GlobalTheory.MulEqIntegerExists

open NumberField

theorem exists_mul_eq_integer {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ a b : RingOfIntegers E, b ≠ 0 ∧ (algebraMap (RingOfIntegers E) E b) * c
      = algebraMap (RingOfIntegers E) E a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨a, b, hb0, ?_⟩
  have : algebraMap (RingOfIntegers E) E b ≠ 0 :=
    fun h => hb0 (IsFractionRing.injective (RingOfIntegers E) E (by rw [h, map_zero]))
  rw [mul_div_assoc', mul_div_cancel_left₀ _ this]

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ ν : RingOfIntegers E, ν ≠ 0 ∧ ν • y ∈ L := by
  have hy : y ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL]; trivial
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem b hax
    · rw [mul_smul]; exact L.smul_mem a hbz
  | smul c x _ hx =>
    obtain ⟨ν, hν, hνx⟩ := hx
    obtain ⟨a, b, hb, hab⟩ := exists_mul_eq_integer c
    refine ⟨b * ν, mul_ne_zero hb hν, ?_⟩
    have h : (b * ν) • (c • x) = a • (ν • x) := by
      rw [← algebraMap_smul E (b * ν), ← algebraMap_smul E a, ← algebraMap_smul E ν,
        smul_smul, smul_smul, map_mul, ← hab]
      congr 1
      ring
    rw [h]
    exact L.smul_mem a hνx

end GlobalTheory.MulEqIntegerExists
end

