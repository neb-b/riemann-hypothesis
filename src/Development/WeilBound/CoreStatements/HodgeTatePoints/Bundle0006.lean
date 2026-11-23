module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsMinorNeZero
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

namespace PositivityTheory.HtPt.Gf

theorem minor_mul_upper {B : Type} [CommRing B] {N i : ℕ} (hi : i ≤ N) (g U : Matrix (Fin N) (Fin N) B)
    (J : Fin i → Fin N) (hU : ∀ a b, b < a → U a b = 0) :
    ((g * U).submatrix J (Fin.castLE hi)).det =
      (g.submatrix J (Fin.castLE hi)).det * ∏ l : Fin i, U (Fin.castLE hi l) (Fin.castLE hi l) := by
  have h : (g * U).submatrix J (Fin.castLE hi) =
      g.submatrix J (Fin.castLE hi) * U.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (Fin i)).map (Fin.castLEEmb hi))) ?_,
      Finset.sum_map]
    · rfl
    · intro k _ hk
      have hki : i ≤ (k : ℕ) := by
        by_contra hlt
        push_neg at hlt
        exact hk (Finset.mem_map.2 ⟨⟨k, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      have hlt : Fin.castLE hi b < k := by
        rw [Fin.lt_def, Fin.coe_castLE]
        omega
      rw [hU k (Fin.castLE hi b) hlt, mul_zero]
  have hT : (U.submatrix (Fin.castLE hi) (Fin.castLE hi)).IsUpperTriangular := by
    intro a b hab
    have hab' : Fin.castLE hi b < Fin.castLE hi a := by
      rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
      exact hab
    exact hU _ _ hab'
  rw [h, Matrix.det_mul, Matrix.det_of_upperTriangular hT]
  rfl

private theorem cb_lemma {B : Type} [CommRing B] {i N : ℕ} (A : Matrix (Fin i) (Fin N) B)
    (C : Matrix (Fin N) (Fin i) B) :
    (A * C).det = ∑ p : Fin i → Fin N, (∏ a, A a (p a)) * (C.submatrix p id).det := by
  have key : ∀ p : Fin i → Fin N, (C.submatrix p id).det =
      ∑ σ : Equiv.Perm (Fin i), Equiv.Perm.sign σ • ∏ a, C (p a) (σ a) := by
    intro p
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  simp_rw [key]
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [Matrix.transpose_apply, Matrix.mul_apply]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.smul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, mul_smul_comm]

private theorem matAct_of_span_residue_spans {B : Type} [CommRing B] {N i : ℕ} (hi : i ≤ N) (g : Matrix (Fin N) (Fin N) B)
    (hg : IsUnit g.det) :
    Ideal.span (Set.range fun J : Fin i → Fin N => (g.submatrix J (Fin.castLE hi)).det) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : g⁻¹.submatrix (Fin.castLE hi) id * g.submatrix id (Fin.castLE hi) = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.nonsing_inv_mul g hg]
    exact Matrix.submatrix_one _ (Fin.castLE_injective hi)
  have h2 := cb_lemma (g⁻¹.submatrix (Fin.castLE hi) id) (g.submatrix id (Fin.castLE hi))
  rw [h1, Matrix.det_one] at h2
  rw [h2]
  exact Ideal.sum_mem _ fun p _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨p, rfl⟩)

theorem lead_minor : ∀ (B : Type) [CommRing B] (N i : ℕ) (hi : i ≤ N), (∀ (g U : Matrix (Fin N) (Fin N) B) (J : Fin i → Fin N), (∀ a b, b < a → U a b = 0) → ((g * U).submatrix J (Fin.castLE hi)).det = (g.submatrix J (Fin.castLE hi)).det * ∏ l : Fin i, U (Fin.castLE hi l) (Fin.castLE hi l)) ∧ ∀ g : Matrix (Fin N) (Fin N) B, IsUnit g.det → Ideal.span (Set.range fun J : Fin i → Fin N => (g.submatrix J (Fin.castLE hi)).det) = ⊤ := by
  intro B _ N i hi
  exact ⟨fun g U J hU => minor_mul_upper hi g U J hU, fun g hg => matAct_of_span_residue_spans hi g hg⟩

theorem abel_nat (lam x : ℕ → ℝ) (n : ℕ) (hl : ∀ i, i + 1 ≤ n → lam (i + 1) ≤ lam i)
    (hx : ∀ i, i ≤ n → 0 ≤ ∑ l ∈ Finset.range i, x l) :
    lam n * ∑ l ∈ Finset.range (n + 1), x l ≤ ∑ l ∈ Finset.range (n + 1), lam l * x l := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun j hj => hl j (by omega)) (fun j hj => hx j (by omega))
    have hs := hx (n + 1) le_rfl
    have hln := hl n le_rfl
    rw [Finset.sum_range_succ x (n + 1), Finset.sum_range_succ (fun l => lam l * x l) (n + 1)]
    nlinarith [mul_nonneg (sub_nonneg.2 hln) hs]

theorem abel_sum : ∀ (N : ℕ) (lam x : Fin N → ℝ), (∀ i j, i ≤ j → lam j ≤ lam i) → (∀ i : ℕ, i ≤ N → 0 ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin N => (l : ℕ) < i), x l) → ∑ l, x l = 0 → 0 ≤ ∑ l, lam l * x l := by
  intro N lam x hl hx hsum
  cases N with
  | zero => simp
  | succ n =>
    obtain ⟨x', hx'⟩ : ∃ f : ℕ → ℝ, ∀ l : Fin (n + 1), f l = x l :=
      ⟨fun k => if h : k < n + 1 then x ⟨k, h⟩ else 0, fun l => by simp [l.isLt]⟩
    obtain ⟨lam', hlam'⟩ : ∃ f : ℕ → ℝ, ∀ l : Fin (n + 1), f l = lam l :=
      ⟨fun k => if h : k < n + 1 then lam ⟨k, h⟩ else 0, fun l => by simp [l.isLt]⟩
    have hsx : ∀ i, i ≤ n + 1 → ∑ l ∈ Finset.range i, x' l =
        ∑ l ∈ Finset.univ.filter (fun l : Fin (n + 1) => (l : ℕ) < i), x l := by
      intro i hi
      have e : ∀ l : Fin (n + 1), (if (l : ℕ) < i then x l else 0) =
          (fun k => if k < i then x' k else 0) (l : ℕ) := by
        intro l
        simp only [hx']
      rw [Finset.sum_filter, Finset.sum_congr rfl (fun l _ => e l),
        Fin.sum_univ_eq_sum_range (fun k => if k < i then x' k else 0), ← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_range, Finset.mem_filter]
      omega
    have htot : ∑ l ∈ Finset.range (n + 1), x' l = 0 := by
      rw [← Fin.sum_univ_eq_sum_range x' (n + 1)]
      simp only [hx']
      exact hsum
    have hprod : ∑ l ∈ Finset.range (n + 1), lam' l * x' l = ∑ l, lam l * x l := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => lam' k * x' k) (n + 1)]
      simp only [hx', hlam']
    have hl' : ∀ i, i + 1 ≤ n → lam' (i + 1) ≤ lam' i := by
      intro i hi
      have h1 := hlam' ⟨i + 1, by omega⟩
      have h2 := hlam' ⟨i, by omega⟩
      simp only at h1 h2
      rw [h1, h2]
      exact hl _ _ (Fin.mk_le_mk.2 (by omega))
    have hx'' : ∀ i, i ≤ n → 0 ≤ ∑ l ∈ Finset.range i, x' l := by
      intro i hi
      rw [hsx i (by omega)]
      exact hx i (by omega)
    have key := abel_nat lam' x' n hl' hx''
    rw [htot, hprod, mul_zero] at key
    exact key

end PositivityTheory.HtPt.Gf
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.ExtTensor
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace PositivityTheory.HtPt.Mh

theorem ind_id : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → indOrder (MonoidHom.id T) A = A := by
  intro R _ T _ A hA
  ext f
  refine ⟨fun h => ?_, fun h t => Twhopf.translate_mem R T A hA f h t⟩
  have := h 1
  simpa using this

theorem ext_tensor : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (A : Subalgebra R (T → R)), IsHopfOrder A → (∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A) → IsHopfOrder (extOrder (algebraMap R R') A) ∧ ∃ e : R' ⊗[R] A ≃ₐ[R'] extOrder (algebraMap R R') A, ∀ (a : A) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t) := by
  intro R _ _ T _ _ R' _ _ _ A hA ⟨d, hd, hdA⟩
  classical
  cases nonempty_fintype T
  have := hA.finite
  have := hA.projective
  let c : A →ₐ[R] (T → R') :=
    AlgHom.pi fun t => (Algebra.ofId R R').comp (evalAt A t)
  let L : R' ⊗[R] A →ₐ[R'] (T → R') :=
    Algebra.TensorProduct.lift (Algebra.ofId R' (T → R')) c (fun _ _ => Commute.all _ _)
  have hL : ∀ (r : R') (a : A) (t : T), L (r ⊗ₜ a) t = r * algebraMap R R' (a.1 t) := fun r a t => rfl
  let m : T → A := fun t => ⟨_, hdA (Pi.single t 1)⟩
  let M : (T → R') →ₗ[R'] R' ⊗[R] A :=
    ∑ t, (LinearMap.proj t : (T → R') →ₗ[R'] R').smulRight ((1 : R') ⊗ₜ[R] m t)
  have hM : ∀ x, M (L x) = algebraMap R R' d • x := by
    intro x
    induction x with
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]
    | tmul r a =>
      have e : ∑ t, a.1 t • m t = d • a := by
        apply Subtype.ext
        funext s
        simp [m, Pi.single_apply, Finset.sum_apply, mul_comm]
      have e2 : ∀ t, (r * algebraMap R R' (a.1 t)) • ((1 : R') ⊗ₜ[R] m t) = r ⊗ₜ[R] (a.1 t • m t) := by
        intro t
        rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, smul_eq_mul, mul_one, Algebra.smul_def, mul_comm]
      simp only [M, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply, hL, e2]
      rw [← TensorProduct.tmul_sum, e, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', algebraMap_smul]
  have hinj : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h := hM x
    rw [hx, map_zero] at h
    exact (smul_eq_zero_iff_right hd).1 h.symm
  have hrange : L.range = extOrder (algebraMap R R') A := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x with
      | add x y hx hy => exact (map_add L.toRingHom x y).symm ▸ add_mem hx hy
      | tmul r a =>
        exact (extOrder (algebraMap R R') A).smul_mem (OrderApi.comp_mem_extOrder (algebraMap R R') a.2) r
    · refine Algebra.adjoin_le ?_
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨(1 : R') ⊗ₜ ⟨f, hf⟩, funext fun t => (hL _ _ t).trans (one_mul _)⟩
  let e : R' ⊗[R] A ≃ₐ[R'] extOrder (algebraMap R R') A :=
    (AlgEquiv.ofInjective L hinj).trans (Subalgebra.equivOfEq _ _ hrange)
  refine ⟨⟨Module.Finite.equiv e.toLinearEquiv, Module.Projective.of_equiv e.toLinearEquiv,
    ⟨algebraMap R R' d, hd, fun g => ?_⟩, fun g hg => ?_, fun g hg => ?_⟩,
    e, fun a t => (hL 1 a t).trans (one_mul _)⟩
  · rw [← hrange]
    refine ⟨M g, funext fun s => ?_⟩
    change L (M g) s = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [M, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply, map_sum, map_smul,
      Finset.sum_apply, Pi.smul_apply, hL, m]
    simp [Pi.single_apply, apply_ite, mul_comm]
  · rw [Htat.ext_span] at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨f, hf, rfl⟩ := hg
      have key : ∀ n ∈ prodSpan A, (fun z => algebraMap R R' (n z)) ∈ prodSpan (extOrder (algebraMap R R') A) := by
        intro n hn
        induction hn using Submodule.span_induction with
        | mem n hn =>
          obtain ⟨a, ha, b, hb, rfl⟩ := hn
          simpa using OrderApi.mul_mem_prodSpan (OrderApi.comp_mem_extOrder (algebraMap R R') ha)
            (OrderApi.comp_mem_extOrder (algebraMap R R') hb)
        | zero =>
          convert Submodule.zero_mem (prodSpan (extOrder (algebraMap R R') A)) using 1
          ext z; simp
        | add x y _ _ hx hy =>
          convert Submodule.add_mem _ hx hy using 1
          ext z; simp
        | smul r x _ hx =>
          convert Submodule.smul_mem _ (algebraMap R R' r) hx using 1
          ext z; simp
      exact key _ (hA.comul f hf)
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul r x _ hx => exact Submodule.smul_mem _ r hx
  · rw [Htat.ext_span] at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨f, hf, rfl⟩ := hg
      exact OrderApi.comp_mem_extOrder (algebraMap R R') (hA.inv f hf)
    | zero => exact Subalgebra.zero_mem _
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | smul r x _ hx => exact Subalgebra.smul_mem _ hx r

end PositivityTheory.HtPt.Mh
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GhModelAlg
section
noncomputable section

namespace PositivityTheory.HtPt.Gh

open Module NumberField GlobalTheory.CompanionTheory.Ar

theorem mem_eig {R V O : Type} [CommRing R] [AddCommGroup V] [Module R V] [CommRing O]
    {ρ : O →+* Module.End R V} {χ : O →+* R} {x : V} :
    x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ ↔ ∀ a, ρ a x = χ a • x := by
  simp [GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem exists_lift {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K] (χ : 𝓞 E →+* K) :
    ∃ σ : E →+* K, ∀ a : 𝓞 E, σ (a : E) = χ a := by
  have hinj : Function.Injective χ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [eq_bot_iff]
    intro n hn
    have : (n : K) = 0 := by simpa using hn
    exact_mod_cast this
  exact ⟨IsFractionRing.lift hinj, fun a => IsFractionRing.lift_algebraMap hinj a⟩

theorem exists_int_proj (E : Type) [Field E] [NumberField E] :
    ∃ (m : ℤ) (a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E), m ≠ 0 ∧
      ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (ρ : 𝓞 E →+* Module.End K V)
        (χ : 𝓞 E →+* K),
        (∀ x, ∑ k, χ (a k) • ρ (RingOfIntegers.basis E k) x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ) ∧
        ∀ x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ, ∑ k, χ (a k) • ρ (RingOfIntegers.basis E k) x = (m : K) • x := by
  obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ)
    (fun q : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      (integralBasis E).repr (HT.dualInt E q.1) q.2)
  choose n hn using hm
  have ha : ∀ k, ((∑ j, n (k, j) • RingOfIntegers.basis E j : 𝓞 E) : E) = ((m : ℤ) : E) * HT.dualInt E k := by
    intro k
    conv_rhs => rw [← (integralBasis E).sum_repr (HT.dualInt E k)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingOfIntegers.coe_eq_algebraMap, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := hn (k, j)
    simp only [eq_intCast, zsmul_eq_mul] at h
    rw [map_zsmul, ← integralBasis_apply, ← Int.cast_smul_eq_zsmul ℚ, h, mul_smul, Int.cast_smul_eq_zsmul,
      zsmul_eq_mul]
  refine ⟨m, fun k => ∑ j, n (k, j) • RingOfIntegers.basis E j, nonZeroDivisors.coe_ne_zero m, ?_⟩
  intro K V _ _ _ _ ρ χ
  obtain ⟨σ, hσ⟩ := exists_lift χ
  have he : ∀ x, x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ ↔ x ∈ HT.eigSp ρ σ := fun x => by
    rw [mem_eig, HT.LatBasic.mem_eigSp]; simp only [hσ]
  have hT : ∀ x, ∑ k, χ (∑ j, n (k, j) • RingOfIntegers.basis E j) • ρ (RingOfIntegers.basis E k) x =
      ((m : ℤ) : K) • HT.eigProj ρ σ x := fun x => by
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hσ, ha, map_mul, map_intCast]
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [hT]
    exact Submodule.smul_mem _ _ ((he _).2 (HT.LatBasic.eigProj_mem ρ σ x))
  · rw [hT, HT.LatBasic.eigProj_of_mem ((he _).1 hx)]

theorem exists_predual {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {r : ℕ}
    (b : Fin r → Module.Dual K V) (hli : LinearIndependent K b) (hsp : Submodule.span K (Set.range b) = ⊤) :
    ∃ f : Fin r → V, (∀ i j, b i (f j) = if i = j then 1 else 0) ∧ ∀ e, e = ∑ j, b j e • f j := by
  let B : Basis (Fin r) K (Module.Dual K V) := Basis.mk hli hsp.ge
  let F := B.dualBasis.map (Module.evalEquiv K V).symm
  refine ⟨F, fun i j => ?_, fun e => ?_⟩
  · have : b i = B i := by simp [B]
    rw [this]
    simp only [F, Basis.map_apply, Module.apply_evalEquiv_symm_apply, Basis.dualBasis_apply_self]
  · conv_lhs => rw [← F.sum_repr e]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp [F, B, Basis.dualBasis_repr]

theorem alg_main {E : Type} [Field E] [NumberField E] {Ω C R A A' : Type} [Field Ω] [Field C] [CharZero C]
    [CommRing R] [Algebra R C] [CommRing A] [CommRing A'] {Li EC : Type} [AddCommGroup Li] [Module Ω Li]
    [AddCommGroup EC] [Module C EC] [Module R EC] [IsScalarTower R C EC]
    (k : A →+* A') (g : A' →+* Ω) (hg : Function.Injective g) (ψ : A' →+* C) (φ : A →+* R)
    (hψ : ∀ a, ψ (k a) = algebraMap R C (φ a)) {n : ℕ} (β : Basis (Fin n) Ω Li) (γ : Basis (Fin n) C EC)
    (Val : Li → EC → Prop)
    (hVal : ∀ e x, Val e x ↔ ∃ c : Fin n → A', e = ∑ i, g (c i) • β i ∧ x = ∑ i, ψ (c i) • γ i)
    (ρ : 𝓞 E →+* Module.End Ω Li) (ρC : 𝓞 E →+* Module.End C EC) (χ : 𝓞 E →+* Ω) (σ : 𝓞 E →+* R)
    (hχ : ∀ a, ∃ s, g (k s) = χ a ∧ φ s = σ a) (hact : ∀ a e x, Val e x → Val (ρ a e) (ρC a x))
    (L W : Set Li) {r : ℕ} (w : Fin r → Module.Dual Ω Li) (f : Fin r → Li) (hβ : ∀ i, β i ∈ L)
    (hwL : ∀ j, ∀ e ∈ L, ∃ a, g (k a) = w j e) (hf : ∀ j, f j ∈ W)
    (hW : ∀ e ∈ W, e ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ ∧ ∀ j, ∃ a, g (k a) = w j e)
    (hexp : ∀ e ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ, e = ∑ j, w j e • f j) (hfv : ∀ j, ∃ x, Val (f j) x)
    (κ : Ω) (κz : R) (hκ : ∃ s, g (k s) = κ ∧ φ s = κz) (hκW : ∀ e ∈ W, κ • e ∈ L) :
    Submodule.span R {x | ∃ e ∈ L, Val e x} ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap R C).comp σ)).restrictScalars R ≤
        Submodule.span R {x | ∃ e ∈ W, Val e x} ∧
      (∀ x ∈ Submodule.span R {x | ∃ e ∈ W, Val e x}, κz • x ∈ Submodule.span R {x | ∃ e ∈ L, Val e x} ⊓
        (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap R C).comp σ)).restrictScalars R) ∧
      (Submodule.span R {x | ∃ e ∈ W, Val e x}).FG := by
  classical
  haveI : CharZero A' := ψ.charZero
  haveI : CharZero Ω := charZero_of_injective_ringHom hg
  have vuniq : ∀ e x x', Val e x → Val e x' → x = x' := by
    intro e x x' h h'
    obtain ⟨c, h1, rfl⟩ := (hVal _ _).1 h
    obtain ⟨c', h2, rfl⟩ := (hVal _ _).1 h'
    have : c = c' := funext fun i => hg (by
      have := congrArg (fun y => β.repr y i) (h1.symm.trans h2)
      simpa [Finsupp.single_apply] using this)
    rw [this]
  have vzero : Val 0 0 := (hVal _ _).2 ⟨0, by simp, by simp⟩
  have vadd : ∀ e x e' x', Val e x → Val e' x' → Val (e + e') (x + x') := by
    intro e x e' x' h h'
    obtain ⟨c, rfl, rfl⟩ := (hVal _ _).1 h
    obtain ⟨c', rfl, rfl⟩ := (hVal _ _).1 h'
    exact (hVal _ _).2 ⟨c + c', by simp [add_smul, Finset.sum_add_distrib],
      by simp [add_smul, Finset.sum_add_distrib]⟩
  have vsmul : ∀ (a : A') e x, Val e x → Val (g a • e) (ψ a • x) := by
    intro a e x h
    obtain ⟨c, rfl, rfl⟩ := (hVal _ _).1 h
    exact (hVal _ _).2 ⟨fun i => a * c i, by simp [mul_smul, Finset.smul_sum], by simp [mul_smul, Finset.smul_sum]⟩
  have vsum : ∀ {I : Type} (s : Finset I) (e : I → Li) (x : I → EC), (∀ i, Val (e i) (x i)) →
      Val (∑ i ∈ s, e i) (∑ i ∈ s, x i) := by
    intro I s e x h
    induction s using Finset.induction_on with
    | empty => simpa using vzero
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact vadd _ _ _ _ (h i) ih
  have vbas : ∀ i, Val (β i) (γ i) := fun i => (hVal _ _).2 ⟨Pi.single i 1, by
    rw [Finset.sum_eq_single i] <;> simp +contextual, by rw [Finset.sum_eq_single i] <;> simp +contextual⟩
  have vchi : ∀ a e x, Val e x → Val (χ a • e) (((algebraMap R C).comp σ) a • x) := by
    intro a e x h
    obtain ⟨s, h1, h2⟩ := hχ a
    have := vsmul (k s) e x h
    rwa [h1, hψ, h2] at this
  have veig : ∀ e x, Val e x → e ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ →
      x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap R C).comp σ) := by
    intro e x h he
    refine mem_eig.2 fun a => vuniq _ _ _ (hact a e x h) ?_
    rw [mem_eig.1 he]
    exact vchi a e x h
  choose t ht using fun j i => hwL j (β i) (hβ i)
  choose xf hxf using hfv
  let wC : Fin r → Module.Dual C EC := fun j => γ.constr C fun i => ψ (k (t j i))
  have hwC : ∀ j e x, Val e x → ∃ c, g c = w j e ∧ ψ c = wC j x := by
    intro j e x h
    obtain ⟨c, rfl, rfl⟩ := (hVal _ _).1 h
    exact ⟨∑ i, c i * k (t j i), by simp [ht], by simp [wC]⟩
  have hwR : ∀ j e x, Val e x → (∃ a, g (k a) = w j e) → ∃ o, algebraMap R C o = wC j x := by
    rintro j e x h ⟨a, ha⟩
    obtain ⟨c, h1, h2⟩ := hwC j e x h
    exact ⟨φ a, by rw [← hψ, hg (ha.trans h1.symm), h2]⟩
  have hP : ∀ e x, Val e x → e ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρ χ → x = ∑ j, wC j x • xf j := by
    intro e x h he
    choose c h1 h2 using fun j => hwC j e x h
    refine vuniq _ _ _ h ?_
    have := vsum Finset.univ _ _ fun j => vsmul (c j) _ _ (hxf j)
    simp only [h1, h2] at this
    rwa [← hexp e he] at this
  have hPC : ∀ x ∈ GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap R C).comp σ), x = ∑ j, wC j x • xf j := by
    obtain ⟨m, a, hm, hT⟩ := exists_int_proj E
    let T : EC →ₗ[C] EC := ∑ q, ((algebraMap R C).comp σ) (a q) • ρC (RingOfIntegers.basis E q)
    have hTa : ∀ x, T x = ∑ q, ((algebraMap R C).comp σ) (a q) • ρC (RingOfIntegers.basis E q) x := fun x => by
      simp only [T, LinearMap.sum_apply, LinearMap.smul_apply]
    let P : EC →ₗ[C] EC := ∑ j, (wC j).smulRight (xf j)
    have hPa : ∀ x, P x = ∑ j, wC j x • xf j := fun x => by
      simp only [P, LinearMap.sum_apply, LinearMap.smulRight_apply]
    have hPT : P ∘ₗ T = T := γ.ext fun i => by
      rw [LinearMap.comp_apply, hPa]
      refine (hP _ _ ?_ ((hT Ω Li ρ χ).1 (β i))).symm
      rw [hTa]
      exact vsum _ _ _ fun q => vchi _ _ _ (hact _ _ _ (vbas i))
    intro x hx
    have h1 := LinearMap.congr_fun hPT x
    rw [LinearMap.comp_apply, hTa, (hT C EC ρC _).2 x hx, map_smul] at h1
    rw [← hPa]
    exact (smul_right_injective EC (Int.cast_ne_zero.2 hm) h1).symm
  have hcomb : ∀ x, x = ∑ j, wC j x • xf j → (∀ j, ∃ o, algebraMap R C o = wC j x) →
      x ∈ Submodule.span R (Set.range xf) := by
    intro x h1 h2
    choose o ho using h2
    rw [h1]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← ho, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hWz : Submodule.span R {x | ∃ e ∈ W, Val e x} = Submodule.span R (Set.range xf) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro x ⟨e, he, h⟩
      exact hcomb x (hP e x h (hW e he).1) fun j => hwR j e x h ((hW e he).2 j)
    · rintro _ ⟨j, rfl⟩
      exact ⟨f j, hf j, hxf j⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨hx1, hx2⟩
    rw [hWz]
    refine hcomb x (hPC x hx2) fun j => ?_
    clear hx2
    induction hx1 using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he, h⟩ := hx
      exact hwR j e x h (hwL j e he)
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨o, ho⟩ := hx
      obtain ⟨o', ho'⟩ := hy
      exact ⟨o + o', by rw [map_add (f := _), map_add (f := _), ho, ho']⟩
    | smul c x _ hx =>
      obtain ⟨o, ho⟩ := hx
      exact ⟨c * o, by rw [map_mul, ho, ← algebraMap_smul C c x, map_smul, smul_eq_mul]⟩
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he, h⟩ := hx
      obtain ⟨s, h1, h2⟩ := hκ
      have := vsmul (k s) e x h
      rw [h1, hψ, h2, algebraMap_smul] at this
      exact ⟨Submodule.subset_span ⟨_, hκW e he, this⟩,
        Submodule.smul_mem ((GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap R C).comp σ)).restrictScalars R) κz
          (veig e x h (hW e he).1)⟩
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx
  · rw [hWz]
    exact Submodule.fg_span (Set.finite_range _)

end PositivityTheory.HtPt.Gh
end
end

