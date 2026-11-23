module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthKerCokerLsmulQuotientSpanSwap
section
namespace GlobalTheory.ASwap

variable {A : Type} [CommRing A] [IsDomain A]

noncomputable def mulMap (a b c : A) (hc : a * b = c) :
    (A ⧸ Ideal.span {a}) →ₗ[A] (A ⧸ Ideal.span {c}) :=
  Submodule.mapQ (Ideal.span {a}) (Ideal.span {c}) (LinearMap.lsmul A A b) (by
    intro x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [Submodule.mem_comap, LinearMap.lsmul_apply, smul_eq_mul]
    exact Submodule.mem_span_singleton.mpr ⟨r, by rw [← hc]; ring⟩)

lemma mulMap_mk (a b c : A) (hc : a * b = c) (x : A) :
    mulMap a b c hc (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (b * x) := rfl

lemma mulMap_injective (a b c : A) (hb : b ≠ 0) (hc : a * b = c) :
    Function.Injective (mulMap a b c hc) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    change mulMap a b c hc (Ideal.Quotient.mk _ x) = 0 at hq
    rw [mulMap_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hq
    obtain ⟨r, hr⟩ := hq
    change Ideal.Quotient.mk _ x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨r, ?_⟩
    apply mul_left_cancel₀ hb
    rw [← hr, ← hc]; ring

lemma map_mulMap_ker (a b c : A) (hc : a * b = c) :
    (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)).map (mulMap a b c hc) =
      Submodule.map (Submodule.mkQ (Ideal.span {c})) (Ideal.span {a} ⊓ Ideal.span {b} : Submodule A A) := by
  ext z
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.lsmul_apply, Submodule.mem_inf]
  constructor
  · rintro ⟨q, hq, rfl⟩
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      refine ⟨b * x, ⟨?_, ?_⟩, rfl⟩
      · have hq' : Ideal.Quotient.mk (Ideal.span {a}) (b * x) = 0 := hq
        exact Ideal.Quotient.eq_zero_iff_mem.mp hq'
      · exact Ideal.mem_span_singleton'.mpr ⟨x, mul_comm _ _⟩
  · rintro ⟨t, ⟨hta, htb⟩, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp htb
    refine ⟨Ideal.Quotient.mk _ x, ?_, ?_⟩
    · change Ideal.Quotient.mk (Ideal.span {a}) (b * x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, mul_comm]; exact hta
    · change Ideal.Quotient.mk _ (b * x) = Ideal.Quotient.mk _ (x * b)
      rw [mul_comm]

noncomputable def kerEquiv (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) ≃ₗ[A]
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a) :=
  (Submodule.equivMapOfInjective _ (mulMap_injective a b (a * b) hb rfl) _).trans
    ((LinearEquiv.ofEq _ _ (by
        rw [map_mulMap_ker, map_mulMap_ker b a (a * b) (mul_comm b a), inf_comm])).trans
      (Submodule.equivMapOfInjective _ (mulMap_injective b a (a * b) ha (mul_comm b a)) _).symm)

lemma range_lsmul_eq (a b : A) :
    LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) =
      Submodule.map (Submodule.mkQ (Ideal.span {a})) (Ideal.span {b} : Submodule A A) := by
  ext z
  simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.mem_map]
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Submodule.Quotient.induction_on with
    | H x => exact ⟨x * b, Ideal.mem_span_singleton'.mpr ⟨x, rfl⟩, by
        change Ideal.Quotient.mk _ (x * b) = Ideal.Quotient.mk _ (b * x); rw [mul_comm]⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp ht
    exact ⟨Ideal.Quotient.mk _ x, by
        change Ideal.Quotient.mk _ (b * x) = Ideal.Quotient.mk _ (x * b); rw [mul_comm]⟩

noncomputable def cokerEquiv (a b : A) :
    ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≃ₗ[A]
      A ⧸ (Ideal.span {a} ⊔ Ideal.span {b} : Submodule A A) :=
  (Submodule.quotEquivOfEq _ _ (range_lsmul_eq a b)).trans
    (Submodule.quotientQuotientEquivQuotientSup _ _)

end GlobalTheory.ASwap

theorem GlobalTheory.kernel_cokernel_length_swap :
    ∀ (A : Type) [CommRing A] [IsDomain A] (a b : A), a ≠ 0 → b ≠ 0 → Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧ Module.length A ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) = Module.length A ((A ⧸ Ideal.span {b}) ⧸ LinearMap.range (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  intro A _ _ a b ha hb
  refine ⟨(GlobalTheory.ASwap.kerEquiv a b ha hb).length_eq, ?_⟩
  exact ((GlobalTheory.ASwap.cokerEquiv a b).trans ((Submodule.quotEquivOfEq _ _ (sup_comm _ _)).trans
    (GlobalTheory.ASwap.cokerEquiv b a).symm)).length_eq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModMaximalSkew
section
open scoped Matrix

namespace GlobalTheory

theorem lift_mod_maximal_skew : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ Z₀ : Matrix (Fin n) (Fin n) O, (∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O) →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ ∀ i j, Z i j - Z₀ i j ∈ IsLocalRing.maximalIdeal O := by
  intro O _ _ c hc h2 n J hJ hdet Z₀ hZ
  obtain ⟨u, hu⟩ : ∃ u : O, u * 2 = 1 := ⟨h2.unit⁻¹.val, h2.val_inv_mul⟩
  have hcu : c u = u := by
    have h1 : c u * 2 = 1 := by
      have := congrArg c hu
      simpa [map_mul, map_ofNat] using this
    calc c u = c u * (u * 2) := by rw [hu, mul_one]
      _ = (c u * 2) * u := by ring
      _ = u := by rw [h1, one_mul]
  set E := Z₀ᵀ * J + J * Z₀.map c with hE
  have hJc : (J.map c)ᵀ = J := by
    ext i j; simp [Matrix.transpose_apply, Matrix.map_apply, hJ]
  have hEc : (E.map c)ᵀ = E := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hE, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add (f := _), map_sum, map_mul, hc, hJ]
    rw [add_comm]
    congr 1 <;> refine Finset.sum_congr rfl (fun k _ => ?_) <;> ring
  have hJinv : J * ((J⁻¹).map c)ᵀ = 1 := by
    calc J * ((J⁻¹).map c)ᵀ = (J.map c)ᵀ * ((J⁻¹).map c)ᵀ := by rw [hJc]
      _ = ((J⁻¹).map c * J.map c)ᵀ := by rw [Matrix.transpose_mul]
      _ = ((J⁻¹ * J).map c)ᵀ := by rw [Matrix.map_mul]
      _ = 1 := by rw [Matrix.nonsing_inv_mul J hdet, Matrix.map_one c c.map_zero c.map_one, Matrix.transpose_one]
  set D := (u • (E * J⁻¹))ᵀ with hD
  have hDT : Dᵀ * J = u • E := by
    rw [hD, Matrix.transpose_transpose, Matrix.smul_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul J hdet, Matrix.mul_one]
  have hDmap : D.map c = u • (((J⁻¹).map c)ᵀ * (E.map c)ᵀ) := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hD]
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, map_sum, map_mul, hcu]
  have hDc : J * D.map c = u • E := by
    rw [hDmap, Matrix.mul_smul, ← Matrix.mul_assoc, hJinv, Matrix.one_mul, hEc]
  refine ⟨Z₀ - D, ?_, ?_⟩
  · have hmap : (Z₀ - D).map c = Z₀.map c - D.map c := by
      ext i j; simp [Matrix.map_apply]
    rw [Matrix.transpose_sub, Matrix.sub_mul, hmap, Matrix.mul_sub, hDT, hDc]
    have : E - u • E - u • E = 0 := by
      rw [sub_sub, ← add_smul, ← two_mul, mul_comm, hu, one_smul, sub_self]
    rw [← this, hE]; abel
  · intro i j
    have : (Z₀ - D) i j - Z₀ i j = -(u * ∑ k, E j k * J⁻¹ k i) := by
      simp [hD, Matrix.transpose_apply, Matrix.mul_apply, Matrix.smul_apply, mul_comm]
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.sum_mem _ (fun k _ => Ideal.mul_mem_right _ _ (hZ j k))))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndepOnPowOfIsDomainTensorPurelyInseparabl
section
open scoped TensorProduct

namespace GlobalTheory

theorem linearIndepOn_pow_of_isDomain_tensor_purelyInseparable (k B : Type) [Field k] [CommRing B]
    [IsDomain B] [Algebra k B] (p : ℕ) (hp : p.Prime) (hk : CharP k p)
    (hdom : ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K →
      IsPurelyInseparable k K → IsDomain (K ⊗[k] B))
    (s : Finset (FractionRing B)) (hs : LinearIndepOn k _root_.id (s : Set (FractionRing B))) :
    LinearIndepOn k (· ^ p) (s : Set (FractionRing B)) := by
  classical
  haveI : ExpChar k p := ExpChar.prime hp
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors B) s
  have hb : ∀ x : (s : Set (FractionRing B)), ∃ b : B,
      algebraMap B (FractionRing B) b = (d : B) • (x : FractionRing B) := fun x => hd x x.2
  choose b hb using hb
  have hinj := IsFractionRing.injective B (FractionRing B)
  have hd0 : algebraMap B (FractionRing B) (d : B) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  let φ := IsScalarTower.toAlgHom k B (FractionRing B)
  have hφ : ∀ x, φ x = algebraMap B (FractionRing B) x := fun _ => rfl
  have hb' : ∀ x, φ (b x) = algebraMap B (FractionRing B) (d : B) * (x : FractionRing B) := by
    intro x; rw [hφ, hb, Algebra.smul_def]

  have hbli : LinearIndependent k b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    refine Fintype.linearIndependent_iff.1 hs g ?_ i
    have h2 : φ (∑ j, g j • b j) = 0 := by rw [hg, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hb'] at h2
    rw [Finset.sum_congr rfl fun j _ => (mul_smul_comm (g j) _ _).symm, ← Finset.mul_sum] at h2
    exact (mul_eq_zero.1 h2).resolve_left hd0
  unfold LinearIndepOn
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hcB : ∑ j, c j • b j ^ p = 0 := by
    apply hinj
    rw [map_zero, ← hφ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_pow, hb', mul_pow]
    rw [Finset.sum_congr rfl fun j _ => (mul_smul_comm (c j) _ _).symm, ← Finset.mul_sum]
    simp only [] at hc
    rw [hc, mul_zero]

  have hroot : ∀ j, ∃ y : AlgebraicClosure k, y ^ p = algebraMap k (AlgebraicClosure k) (c j) :=
    fun j => IsAlgClosed.exists_pow_nat_eq _ hp.pos
  choose y hy using hroot
  let K := IntermediateField.adjoin k (Set.range y)
  haveI hfin : FiniteDimensional k K :=
    IntermediateField.finiteDimensional_adjoin fun z _ => Algebra.IsIntegral.isIntegral z
  have hpi : IsPurelyInseparable k K := by
    refine (IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem k (AlgebraicClosure k) p).2 ?_
    rintro z ⟨j, rfl⟩
    exact ⟨1, by rw [pow_one, hy]; exact ⟨c j, rfl⟩⟩
  haveI := hdom K hfin hpi
  haveI : CharP (K ⊗[k] B) p :=
    charP_of_injective_algebraMap (algebraMap k (K ⊗[k] B)).injective p
  haveI : ExpChar (K ⊗[k] B) p := ExpChar.prime hp
  let y' := fun j => (⟨y j, IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩⟩ : K)
  have hy' : ∀ j, y' j ^ p = algebraMap k K (c j) := by
    intro j; apply Subtype.ext; simp [y', hy]
  have hz : (∑ j, y' j ⊗ₜ[k] b j) ^ p = 0 := by
    rw [sum_pow_char]
    simp only [Algebra.TensorProduct.tmul_pow, hy', Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, ← TensorProduct.tmul_sum, hcB, TensorProduct.tmul_zero]
  have hz0 : ∑ j, y' j • ((1 : K) ⊗ₜ[k] b j) = 0 := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact pow_eq_zero_iff hp.ne_zero |>.1 hz
  have hli := Module.Flat.linearIndependent_one_tmul (S := K) hbli
  have hyi : y' i = 0 := Fintype.linearIndependent_iff.1 hli y' hz0 i
  have : algebraMap k (AlgebraicClosure k) (c i) = 0 := by
    rw [← hy]
    have : y i = 0 := congrArg Subtype.val hyi
    rw [this, zero_pow hp.ne_zero]
  exact (map_eq_zero_iff _ (algebraMap k (AlgebraicClosure k)).injective).1 this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentComplexMap
section
open Matrix

namespace GlobalTheory

theorem linearIndependent_real_map_of_fieldEmb {E : Type} [Field E] {r n : ℕ} (τ : E →+* ℂ)
    (e : Fin n → Matrix (Fin r) (Fin r) E) (he : LinearIndependent E e) :
    LinearIndependent ℝ (fun i => (e i).map τ) := by
  letI : Algebra E ℂ := τ.toAlgebra
  have h1 : LinearIndependent ℂ (fun i => (1 : ℂ) ⊗ₜ[E] e i) :=
    Module.Flat.linearIndependent_one_tmul he
  let j := (matrixEquivTensor (Fin r) E ℂ).symm
  have hc : ∀ (c : ℂ) (x : TensorProduct E ℂ (Matrix (Fin r) (Fin r) E)),
      j (c • x) = c • j x := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a M =>
      rw [TensorProduct.smul_tmul', smul_eq_mul]
      simp only [j, matrixEquivTensor_apply_symm, mul_smul]
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  have h2 : LinearIndependent ℂ (j.toRingEquiv.toAddEquiv.toAddMonoidHom ∘
      fun i => (1 : ℂ) ⊗ₜ[E] e i) :=
    h1.map_of_injective_injective id _ (fun _ h => h)
      (fun m hm => by simpa using hm) (fun c x => hc c x)
  have h3 : (j.toRingEquiv.toAddEquiv.toAddMonoidHom ∘ fun i => (1 : ℂ) ⊗ₜ[E] e i) =
      fun i => (e i).map τ := by
    funext i
    simp only [Function.comp_apply]
    show j ((1 : ℂ) ⊗ₜ[E] e i) = _
    simp only [j, matrixEquivTensor_apply_symm, one_smul]
    rfl
  rw [h3] at h2
  exact h2.restrict_scalars' ℝ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentKaehlerDOfAlgebraicIndependent
section
set_option autoImplicit false

open scoped TensorProduct
open KaehlerDifferential

namespace GlobalTheory.BertiniAlg

theorem linearIndependent_D_of_algebraicIndependent (k κ : Type) [Field k] [CharZero k] [Field κ]
    [Algebra k κ] [Algebra.EssFiniteType k κ] {σ : Type} (t : σ → κ)
    (ht : AlgebraicIndependent k t) :
    LinearIndependent κ (fun s => KaehlerDifferential.D k κ (t s)) := by
  let P := MvPolynomial σ k
  let φ : P →ₐ[k] κ := MvPolynomial.aeval t
  have hφ : Function.Injective φ := ht
  algebraize [φ.toRingHom]
  have : IsScalarTower k P κ := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  let K := FractionRing P
  have hinj : Function.Injective (algebraMap P κ) := hφ
  let : Algebra K κ := (IsFractionRing.lift (K := K) hinj).toAlgebra
  have : IsScalarTower P K κ := IsScalarTower.of_algebraMap_eq fun a =>
    (IsFractionRing.lift_algebraMap (K := K) hinj a).symm
  have : IsScalarTower k K κ := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k P K, ← IsScalarTower.algebraMap_apply P K κ,
      ← IsScalarTower.algebraMap_apply]
  have : Algebra.EssFiniteType K κ := .of_comp k K κ
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have : Algebra.FormallySmooth K κ := Algebra.FormallySmooth.of_perfectField
  have : Algebra.FormallyEtale P K := .of_isLocalization (nonZeroDivisors P)
  have : Algebra.FormallySmooth P κ := .comp P K κ
  have hH : Subsingleton (Algebra.H1Cotangent P κ) := Algebra.FormallySmooth.subsingleton_h1Cotangent
  have hinjm : Function.Injective (mapBaseChange k P κ) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k P κ x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  let b := (mvPolynomialBasis k σ).baseChange κ
  have h := b.linearIndependent.map' (mapBaseChange k P κ) (LinearMap.ker_eq_bot.2 hinjm)
  have hX (s : σ) : algebraMap P κ (MvPolynomial.X s) = t s := MvPolynomial.aeval_X t s
  have e : (fun s => KaehlerDifferential.D k κ (t s)) = mapBaseChange k P κ ∘ b := by
    funext s
    simp only [Function.comp_apply, b, Module.Basis.baseChange_apply, mvPolynomialBasis_apply]
    erw [mapBaseChange_tmul, one_smul, map_D, hX]
  rw [e]
  exact h

end GlobalTheory.BertiniAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentOfDistinctValuationLike
section
open Filter Topology

namespace GlobalTheory

theorem linearIndependent_of_distinct_valuationLike :
    ∀ (C V Γ ι : Type) [Field C] [AddCommGroup V] [Module C V] [LinearOrder Γ] (ν : V → Γ),
      (∀ (c : C) (u : V), c ≠ 0 → ν (c • u) = ν u) →
      (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u < ν v → u + v ≠ 0 ∧ ν (u + v) = ν u) →
      ∀ f : ι → V, (∀ i, f i ≠ 0) → Function.Injective (fun i => ν (f i)) →
        LinearIndependent C f := by
  intro C V Γ ι _ _ _ _ ν hsm hadd f hf hinj
  classical
  have key : ∀ (g : ι → C) (s : Finset ι), s.Nonempty → (∀ i ∈ s, g i ≠ 0) →
      (∑ i ∈ s, g i • f i) ≠ 0 ∧ ∃ j ∈ s, ν (∑ i ∈ s, g i • f i) = ν (f j) := by
    intro g s
    induction s using Finset.induction_on with
    | empty => intro h; exact absurd h Finset.not_nonempty_empty
    | @insert a s ha ih =>
      intro _ hg
      have hga : g a ≠ 0 := hg a (Finset.mem_insert_self a s)
      have hx : g a • f a ≠ 0 := smul_ne_zero hga (hf a)
      have hνx : ν (g a • f a) = ν (f a) := hsm _ _ hga
      rw [Finset.sum_insert ha]
      rcases s.eq_empty_or_nonempty with hs | hs
      · subst hs
        simp only [Finset.sum_empty, add_zero]
        exact ⟨hx, a, Finset.mem_insert_self a _, hνx⟩
      · obtain ⟨hy, j, hj, hνy⟩ := ih hs (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        have hne : ν (f a) ≠ ν (f j) := by
          intro h
          have : a = j := hinj h
          exact ha (this ▸ hj)
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · obtain ⟨h1, h2⟩ := hadd _ _ hx hy (by rw [hνx, hνy]; exact hlt)
          exact ⟨h1, a, Finset.mem_insert_self a s, by rw [h2, hνx]⟩
        · obtain ⟨h1, h2⟩ := hadd _ _ hy hx (by rw [hνx, hνy]; exact hlt)
          refine ⟨by rw [add_comm]; exact h1, j, Finset.mem_insert_of_mem hj, ?_⟩
          rw [add_comm, h2, hνy]
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  have hsum' : ∑ k ∈ s.filter (fun k => g k ≠ 0), g k • f k = 0 := by
    rw [Finset.sum_filter_of_ne]
    · exact hsum
    · intro x _ hx h
      apply hx
      simp [h]
  have hne : (s.filter (fun k => g k ≠ 0)).Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi, hgi⟩⟩
  exact (key g _ hne (fun j hj => (Finset.mem_filter.1 hj).2)).1 hsum'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralComplexInvPowAddNormSq
section
open Set Filter Topology MeasureTheory

namespace GlobalTheory.RadialIntegral

lemma hasDerivAt_prim (m : ℕ) (a : ℝ) (ha : 0 < a) (r : ℝ) :
    HasDerivAt (fun r : ℝ => -(((a + r ^ 2) ^ (m + 1))⁻¹ / (2 * (m + 1))))
      (r * ((a + r ^ 2) ^ (m + 2))⁻¹) r := by
  have hp : 0 < a + r ^ 2 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => a + r ^ 2) (2 * r) r := by
    simpa using ((hasDerivAt_pow 2 r).const_add a)
  have h2 := ((((h1.pow (m + 1)).inv (pow_ne_zero _ hp.ne')).div_const (2 * ((m : ℝ) + 1))).neg)
  refine h2.congr_deriv ?_
  simp only [Pi.pow_apply, Nat.add_sub_cancel]
  have : (m : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma tendsto_prim (m : ℕ) (a : ℝ) :
    Tendsto (fun r : ℝ => -(((a + r ^ 2) ^ (m + 1))⁻¹ / (2 * (m + 1)))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => a + r ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun r : ℝ => (a + r ^ 2) ^ (m + 1)) atTop atTop :=
    (tendsto_pow_atTop (Nat.succ_ne_zero m)).comp h1
  simpa using ((h2.inv_tendsto_atTop).div_const (2 * ((m : ℝ) + 1))).neg

lemma radial (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * ((a + r ^ 2) ^ (m + 2))⁻¹)
      = ENNReal.ofReal ((a ^ (m + 1))⁻¹ / (2 * (m + 1))) := by
  have hpos : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r * ((a + r ^ 2) ^ (m + 2))⁻¹ := fun r hr => by
    have : (0 : ℝ) < r := hr
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg' (a := 0)
    (fun r _ => hasDerivAt_prim m a ha r) hpos (tendsto_prim m a)
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (fun r _ => hasDerivAt_prim m a ha r) hpos (tendsto_prim m a)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpos)), hval]
  simp

theorem lintegral_inv_pow_add_norm_sq (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((a + ‖z‖ ^ 2) ^ (m + 2))⁻¹)
      = ENNReal.ofReal (Real.pi / ((m + 1) * a ^ (m + 1))) := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have h : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
        ENNReal.ofReal (((a + ‖Complex.polarCoord.symm p‖ ^ 2) ^ (m + 2))⁻¹)
      = ∫⁻ p in polarCoord.target,
        ENNReal.ofReal (p.1 * ((a + p.1 ^ 2) ^ (m + 2))⁻¹) * (fun _ : ℝ => (1 : ENNReal)) p.2 := by
    refine setLIntegral_congr_fun polarCoord.open_target.measurableSet (fun p hp => ?_)
    have h0 : 0 < p.1 := hp.1
    simp only [Complex.norm_polarCoord_symm, sq_abs, smul_eq_mul, mul_one]
    rw [ENNReal.ofReal_mul h0.le]
  rw [h, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (r * ((a + r ^ 2) ^ (m + 2))⁻¹))
      (g := fun _ : ℝ => (1 : ENNReal)) (by fun_prop) (by fun_prop), radial m a ha]
  simp only [lintegral_const, one_mul, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
    Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

end GlobalTheory.RadialIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDensitiesBoundedAlmostAll
section
namespace GlobalTheory

theorem finite_maximal_ideals_containing (B : Type) [CommRing B] [IsDedekindDomain B] (f : B)
    (hf : f ≠ 0) : {P : Ideal B | P.IsMaximal ∧ f ∈ P}.Finite := by
  have hI : Ideal.span {f} ≠ (0 : Ideal B) := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact hf
  have hfin := Ideal.finite_factors hI
  apply (hfin.image (fun v : IsDedekindDomain.HeightOneSpectrum B => v.asIdeal)).subset
  rintro P ⟨hmax, hfP⟩
  have hne : P ≠ ⊥ := by
    rintro rfl
    exact hf ((Submodule.mem_bot B).mp hfP)
  refine ⟨⟨P, hmax.isPrime, hne⟩, ?_, rfl⟩
  show P ∣ Ideal.span {f}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hfP

theorem finite_maximal_ideals_containing' : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B),
    f ≠ 0 → {P : Ideal B | P.IsMaximal ∧ f ∈ P}.Finite :=
  fun B _ _ f hf => finite_maximal_ideals_containing B f hf

end GlobalTheory
end

