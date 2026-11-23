module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotOneSubIdempotentEqMul
section
open scoped TensorProduct
universe u

namespace GlobalTheory

theorem finrank_quot_one_sub_idem_eq_mul : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (φ : A →ₐ[k] k) (e : A), IsIdempotentElem e → φ e = 1 → (∀ a, φ a = 0 → IsNilpotent (e * a)) → ∀ (H : Type u) [AddCommGroup H] [Module A H] [Module k H] [IsScalarTower k A H] [FiniteDimensional k H] [Module.Projective A H], Module.finrank k (H ⧸ (Ideal.span {1 - e} • ⊤ : Submodule A H)) = Module.finrank k (H ⧸ (RingHom.ker φ • ⊤ : Submodule A H)) * Module.finrank k (A ⧸ Ideal.span {1 - e}) := by
  intro k _ A _ _ _ φ e he hφe hnil H _ _ _ _ _ _
  have : Module.Finite A H := Module.Finite.of_restrictScalars_finite k A H
  set I : Ideal A := Ideal.span {1 - e} with hI
  have hIφ : ∀ a ∈ I, φ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [hφe]
  have hItop : I ≠ ⊤ := by
    intro h
    have := hIφ 1 (h ▸ Submodule.mem_top)
    simp at this
  let B := A ⧸ I
  have : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hItop
  have hloc : IsLocalRing B := by
    apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    have key : ∀ x : A, φ x ≠ 0 → IsUnit (Ideal.Quotient.mk I x) := by
      intro x hx
      have he1 : Ideal.Quotient.mk I e = 1 := by
        rw [eq_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk I), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span rfl
      set a := x - algebraMap k A (φ x) with ha
      have hφa : φ a = 0 := by simp [ha]
      have hxa : x = algebraMap k A (φ x) + a := by simp [ha]
      rw [hxa, map_add (f := _)]
      have hn : IsNilpotent (Ideal.Quotient.mk I a) := by
        have : Ideal.Quotient.mk I a = Ideal.Quotient.mk I (e * a) := by rw [map_mul, he1, one_mul]
        rw [this]; exact (hnil a hφa).map _
      apply hn.isUnit_add_left_of_commute _ (Commute.all _ _)
      have : IsUnit (algebraMap k B (φ x)) := (isUnit_iff_ne_zero.mpr hx).map _
      simpa [Ideal.Quotient.mk_algebraMap] using this
    intro b
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    by_cases hx : φ x = 0
    · right
      rw [← map_one (Ideal.Quotient.mk I), ← map_sub]
      exact key _ (by simp [hx])
    · left; exact key x hx
  let T := B ⊗[A] H
  have : Module.Free B T := Module.free_of_flat_of_isLocalRing

  have h3 : Module.finrank k (H ⧸ (I • ⊤ : Submodule A H)) = Module.finrank B T * Module.finrank k B := by
    let b := Module.Free.chooseBasis B T
    let e1 : T ≃ₗ[A] H ⧸ (I • ⊤ : Submodule A H) := TensorProduct.quotTensorEquivQuotSMul H I
    let e3 : (H ⧸ (I • ⊤ : Submodule A H)) ≃ₗ[A] (Module.Free.ChooseBasisIndex B T → B) :=
      e1.symm.trans (b.equivFun.restrictScalars A)
    rw [(e3.restrictScalars k).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Module.finrank_eq_card_chooseBasisIndex (R := B) (M := T)]
  have h4 : Module.finrank k (H ⧸ (RingHom.ker φ • ⊤ : Submodule A H)) = Module.finrank B T := by
    have hsurj : Function.Surjective φ := fun c => ⟨algebraMap k A c, φ.commutes c⟩
    let φB : B →ₐ[k] k := Ideal.Quotient.liftₐ I φ hIφ
    letI : Algebra A k := φ.toRingHom.toAlgebra
    letI : Algebra B k := φB.toRingHom.toAlgebra
    haveI : IsScalarTower A B k := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    haveI : IsScalarTower k A k := IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
    let f := Ideal.quotientKerAlgEquivOfSurjective hsurj
    let g : (A ⧸ RingHom.ker φ) ≃ₗ[A] k :=
      { f.toLinearEquiv with
        map_smul' := by
          intro a x
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
          change f (Ideal.Quotient.mk _ (a * y)) = φ a * f (Ideal.Quotient.mk _ y)
          simp [f, Ideal.quotientKerAlgEquivOfSurjective_apply] }
    let e6 : (k ⊗[A] H) ≃ₗ[A] H ⧸ (RingHom.ker φ • ⊤ : Submodule A H) :=
      (LinearEquiv.rTensor H g.symm).trans (TensorProduct.quotTensorEquivQuotSMul H (RingHom.ker φ))
    rw [← (e6.restrictScalars k).finrank_eq,
      ← (TensorProduct.AlgebraTensorModule.cancelBaseChange A B k k H).finrank_eq,
      Module.finrank_baseChange]
  rw [h3, h4]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeMapIdempotentEqRankAtStalk
section
open Matrix TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdemRankStalk

theorem finrank_range_baseChange_eq {R S M : Type} [CommRing R] [Field S] [Algebra R S]
    [AddCommGroup M] [Module R M] (e : M →ₗ[R] M) (he : e ∘ₗ e = e) :
    Module.finrank S (LinearMap.range (e.baseChange S)) =
      Module.finrank S (S ⊗[R] LinearMap.range e) := by
  let r : M →ₗ[R] LinearMap.range e := e.rangeRestrict
  let i : LinearMap.range e →ₗ[R] M := (LinearMap.range e).subtype
  have hri : r ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨y, hy⟩ := x.2
    change e x.1 = x.1
    rw [← hy]
    exact LinearMap.congr_fun he y
  have hir : e = i ∘ₗ r := LinearMap.ext fun _ => rfl
  have hS : r.baseChange S ∘ₗ i.baseChange S = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hri, LinearMap.baseChange_id]
  have hsurj : Function.Surjective (r.baseChange S) := fun x =>
    ⟨i.baseChange S x, LinearMap.congr_fun hS x⟩
  have hinj : Function.Injective (i.baseChange S) := fun x y hxy => by
    have := congrArg (r.baseChange S) hxy
    rwa [← LinearMap.comp_apply, hS, ← LinearMap.comp_apply, hS] at this
  have h2 : e.baseChange S = i.baseChange S ∘ₗ r.baseChange S := by
    rw [← LinearMap.baseChange_comp, ← hir]
  rw [h2, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hsurj),
    LinearMap.finrank_range_of_inj hinj]

theorem finrank_range_map_eq_rankAtStalk (A : Type) [CommRing A] (n : ℕ)
    (P : Matrix (Fin n) (Fin n) A) (hP : P * P = P) (k : Type) [Field k] (g : A →+* k) :
    Module.finrank k (LinearMap.range (P.map g).mulVecLin) =
      Module.rankAtStalk (LinearMap.range P.mulVecLin)
        (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum A) := by
  letI : Algebra A k := g.toAlgebra
  set e : (Fin n → A) →ₗ[A] (Fin n → A) := P.mulVecLin with he_def
  have he : e ∘ₗ e = e := by
    rw [he_def, ← Matrix.mulVecLin_mul, hP]

  let r : (Fin n → A) →ₗ[A] LinearMap.range e := e.rangeRestrict
  let i : LinearMap.range e →ₗ[A] (Fin n → A) := (LinearMap.range e).subtype
  have hri : r ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨y, hy⟩ := x.2
    change e x.1 = x.1
    rw [← hy]
    exact LinearMap.congr_fun he y
  haveI : Module.Projective A (LinearMap.range e) := Module.Projective.of_split i r hri

  have hst := Module.rankAtStalk_baseChange (R := A) (M := LinearMap.range e) (S := k) ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free] at hst
  have hcomap : PrimeSpectrum.comap (algebraMap A k) (⊥ : PrimeSpectrum k) =
      (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum A) := by
    ext x
    change x ∈ Ideal.comap (algebraMap A k) (⊥ : Ideal k) ↔ x ∈ RingHom.ker g
    rw [Ideal.mem_comap, Ideal.mem_bot, RingHom.mem_ker]
    rfl
  rw [hcomap] at hst
  rw [← hst, ← finrank_range_baseChange_eq e he]

  let Φ : k ⊗[A] (Fin n → A) ≃ₗ[k] (Fin n → k) := TensorProduct.piScalarRight A k k (Fin n)
  have hΦ : ∀ x, Φ (e.baseChange k x) = (P.map g).mulVecLin (Φ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v =>
      ext j
      simp [Φ, e, TensorProduct.piScalarRight_apply, Matrix.mulVec, dotProduct,
        Finset.mul_sum, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hrange : LinearMap.range (P.map g).mulVecLin =
      (LinearMap.range (e.baseChange k)).map (Φ : k ⊗[A] (Fin n → A) →ₗ[k] (Fin n → k)) := by
    have hc : (P.map g).mulVecLin ∘ₗ (Φ : k ⊗[A] (Fin n → A) →ₗ[k] (Fin n → k)) =
        (Φ : k ⊗[A] (Fin n → A) →ₗ[k] (Fin n → k)) ∘ₗ e.baseChange k :=
      LinearMap.ext fun x => (hΦ x).symm
    rw [← LinearMap.range_comp, ← hc, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range Φ)]
  rw [hrange, LinearEquiv.finrank_map_eq]
  rfl

end GlobalTheory.IdemRankStalk
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankZmodTensorHomologyZeroOfNoPTorsion
section
open CategoryTheory Limits

namespace GlobalTheory

theorem exists_torsion_eq_prime_smul_of_noPTorsion {M : Type*} [AddCommGroup M] (p : ℕ)
    [hp : Fact p.Prime] (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) (t : M)
    (ht : t ∈ Submodule.torsion ℤ M) :
    ∃ s ∈ Submodule.torsion ℤ M, t = (p : ℤ) • s := by
  obtain ⟨⟨a, ha⟩, hat⟩ := (Submodule.mem_torsion_iff t).1 ht
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  change a • t = 0 at hat
  set n := a.natAbs with hn
  have hn0 : n ≠ 0 := Int.natAbs_ne_zero.2 ha0
  have hnt : (n : ℤ) • t = 0 := by
    rcases Int.natAbs_eq a with h | h
    · rw [← h]; exact hat
    · have : a = -(n : ℤ) := h
      rw [this, neg_smul, neg_eq_zero] at hat; exact hat
  have hpow : ∀ k : ℕ, ∀ y : M, ((p : ℤ) ^ k) • y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      rw [pow_succ, mul_smul] at hy
      exact hM y (ih _ hy)
  set k := n.factorization p
  set m := n / p ^ k
  have hnm : p ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hmt : (m : ℤ) • t = 0 := by
    apply hpow k
    rw [← mul_smul]
    have : ((p : ℤ) ^ k * (m : ℤ)) = (n : ℤ) := by exact_mod_cast hnm
    rw [this, hnt]
  have hndvd : ¬ p ∣ m := Nat.not_dvd_ordCompl hp.out hn0
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hndvd
  have hic : IsCoprime (p : ℤ) (m : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd_natCast_natCast] using hcop
  obtain ⟨u, v, huv⟩ := hic
  refine ⟨u • t, Submodule.smul_mem _ _ ht, ?_⟩
  calc t = ((u * p + v * m : ℤ)) • t := by rw [huv, one_smul]
    _ = (p : ℤ) • (u • t) := by
      rw [add_smul, mul_smul, mul_smul, hmt, smul_zero, add_zero, smul_comm]

theorem subsingleton_zmod_tensor_torsion {M : Type*} [AddCommGroup M] (p : ℕ) [Fact p.Prime]
    (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Subsingleton (TensorProduct ℤ (ZMod p) (Submodule.torsion ℤ M)) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul c t =>
    obtain ⟨s, hs, hts⟩ := exists_torsion_eq_prime_smul_of_noPTorsion p hM t.1 t.2
    have : t = (p : ℤ) • (⟨s, hs⟩ : Submodule.torsion ℤ M) := Subtype.ext hts
    rw [this, ← TensorProduct.smul_tmul]
    have hc : (p : ℤ) • c = 0 := by
      rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
    rw [hc, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem finrank_zmod_tensor_eq_finrank_of_noPTorsion (M : Type*) [AddCommGroup M] [inst : Module ℤ M]
    [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime] (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) M) = Module.finrank ℤ M := by
  obtain rfl : inst = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  set T := Submodule.torsion ℤ M
  haveI : Module.Free ℤ (M ⧸ T) := Module.free_of_finite_type_torsion_free'
  haveI := subsingleton_zmod_tensor_torsion p hM
  let g := LinearMap.baseChange (ZMod p) T.mkQ
  have hg : ⇑g = ⇑(LinearMap.lTensor (ZMod p) T.mkQ) := LinearMap.baseChange_eq_ltensor _
  have hex := lTensor_exact (ZMod p) (LinearMap.exact_subtype_mkQ T) (Submodule.mkQ_surjective T)
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : LinearMap.lTensor (ZMod p) T.mkQ y = 0 := by rw [← hg]; exact hy
    obtain ⟨z, rfl⟩ := (hex y).1 hy'
    rw [Subsingleton.elim z 0, map_zero]
  have hsurj : Function.Surjective g := by
    rw [hg]; exact LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective T)
  rw [(LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_baseChange,
    finrank_quotient_eq_of_le_torsion le_rfl]

theorem finrank_zmod_tensor_homology_zero :
    ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime],
      (∀ (x : C.X 0), (p : ℤ) • x = 0 → x = 0) → Module.Finite ℤ (C.homology 0) →
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology 0)) =
        Module.finrank ℤ (C.homology 0) := by
  intro C p _ hC _
  let f : C.homology 0 ⟶ C.X 0 := C.isoHomologyπ₀.inv ≫ C.iCycles 0
  have hinj : Function.Injective (ConcreteCategory.hom f) :=
    (ModuleCat.mono_iff_injective f).1 inferInstance
  apply finrank_zmod_tensor_eq_finrank_of_noPTorsion
  intro x hx
  apply hinj
  rw [map_zero]
  apply hC
  rw [← map_zsmul, hx, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsetMemRangeLocalizationAwayOfDvd
section
namespace GlobalTheory

theorem finset_mem_range_of_away_dvd (R : Type) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime]
    (F : Finset (Localization.AtPrime 𝔭)) :
    ∃ s ∉ 𝔭, ∀ (c : R), s ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭,
      κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) →
        ∀ x ∈ F, x ∈ κ.range := by
  classical
  choose p hp using fun x : Localization.AtPrime 𝔭 =>
    IsLocalization.mk'_surjective 𝔭.primeCompl x
  let sx : Localization.AtPrime 𝔭 → 𝔭.primeCompl := fun x => (p x).2
  refine ⟨((∏ x ∈ F, sx x : 𝔭.primeCompl) : R), (∏ x ∈ F, sx x).2, ?_⟩
  intro c hc κ hκ x hx
  have hdvd : ((sx x : 𝔭.primeCompl) : R) ∣ c := by
    refine dvd_trans ?_ hc
    rw [Submonoid.coe_finsetProd]
    exact Finset.dvd_prod_of_mem (fun y => ((sx y : 𝔭.primeCompl) : R)) hx
  obtain ⟨m, hm⟩ := hdvd
  have hκa : ∀ r : R, κ (algebraMap R (Localization.Away c) r) =
      algebraMap R (Localization.AtPrime 𝔭) r := fun r => by
    rw [← RingHom.comp_apply, hκ]
  refine ⟨algebraMap R _ (p x).1 * algebraMap R _ m * IsLocalization.Away.invSelf c, ?_⟩
  have hinv : algebraMap R (Localization.AtPrime 𝔭) c *
      κ (IsLocalization.Away.invSelf (S := Localization.Away c) c) = 1 := by
    rw [← hκa, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  refine (?_ : _ = IsLocalization.mk' (Localization.AtPrime 𝔭) (p x).1 (p x).2).trans (hp x)
  rw [IsLocalization.eq_mk'_iff_mul_eq, map_mul, map_mul, hκa, hκa]
  calc algebraMap R (Localization.AtPrime 𝔭) (p x).1 * algebraMap R _ m *
        κ (IsLocalization.Away.invSelf c) * algebraMap R _ ((p x).2 : R)
      = algebraMap R (Localization.AtPrime 𝔭) (p x).1 *
        (algebraMap R _ (((p x).2 : R) * m) * κ (IsLocalization.Away.invSelf c)) := by
        rw [map_mul]; ring
    _ = algebraMap R (Localization.AtPrime 𝔭) (p x).1 := by
        rw [← hm, hinv, mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumCompEqFinsumCardFiberMul
section
open scoped Pointwise

namespace GlobalTheory

theorem finsum_comp_eq_finsum_natCard_fiber_mul {X Y : Type} (π : X → Y) (h : Y → ℂ)
    (hf : (∀ y, h y ≠ 0 → (π ⁻¹' {y}).Finite) ∨ (∀ y, h y ≠ 0 → Nat.card (π ⁻¹' {y}) = 0)) :
    ∑ᶠ x, h (π x) = ∑ᶠ y, (Nat.card (π ⁻¹' {y}) : ℂ) * h y := by
  classical
  by_cases hfin : (Function.support (h ∘ π)).Finite
  · set S := hfin.toFinset with hS
    have hmemS : ∀ x, x ∈ S ↔ h (π x) ≠ 0 := by
      intro x
      simp [hS]
    have hL : ∑ᶠ x, h (π x) = ∑ x ∈ S, h (π x) := by
      apply finsum_eq_sum_of_support_subset
      intro x hx
      exact (hmemS x).2 hx
    have hR : ∑ᶠ y, (Nat.card (π ⁻¹' {y}) : ℂ) * h y
        = ∑ y ∈ S.image π, (Nat.card (π ⁻¹' {y}) : ℂ) * h y := by
      apply finsum_eq_sum_of_support_subset
      intro y hy
      rw [Function.mem_support] at hy
      have h1 : h y ≠ 0 := right_ne_zero_of_mul hy
      have h2 : Nat.card (π ⁻¹' {y}) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hy
      obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.mp h2).1
      have hxy : π x = y := hx
      rw [Finset.coe_image]
      refine ⟨x, ?_, hxy⟩
      rw [Finset.mem_coe, hmemS, hxy]
      exact h1
    rw [hL, hR, ← Finset.sum_fiberwise_of_maps_to (g := π) (t := S.image π)
      (fun x hx => Finset.mem_image_of_mem π hx)]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hy
    have hne : h (π x₀) ≠ 0 := (hmemS x₀).1 hx₀
    have hfib : π ⁻¹' {π x₀} = ↑(S.filter (fun x => π x = π x₀)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_filter, Set.mem_ofPred_eq]
      constructor
      · intro hx
        refine ⟨?_, hx⟩
        rw [hmemS, hx]
        exact hne
      · exact fun hx => hx.2
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
      Finset.sum_const, nsmul_eq_mul, hfib, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  · rw [finsum_of_infinite_support (f := fun x => h (π x)) hfin]
    symm
    rcases hf with hf | hf
    · apply finsum_of_infinite_support
      intro hR
      apply hfin
      refine (hR.preimage' (f := π) ?_).subset ?_
      · intro y hy
        exact hf y (right_ne_zero_of_mul hy)
      · intro x hx
        simp only [Function.mem_support, Function.comp_apply] at hx
        simp only [Set.mem_preimage, Function.mem_support]
        have hfinx : Finite (π ⁻¹' {π x}) := (hf (π x) hx).to_subtype
        have hnx : Nonempty (π ⁻¹' {π x}) := ⟨⟨x, rfl⟩⟩
        have hc : Nat.card (π ⁻¹' {π x}) ≠ 0 := Nat.card_ne_zero.mpr ⟨hnx, hfinx⟩
        exact mul_ne_zero (by exact_mod_cast hc) hx
    · have hz : (fun y => (Nat.card (π ⁻¹' {y}) : ℂ) * h y) = fun _ => 0 := by
        funext y
        by_cases hy : h y = 0
        · simp [hy]
        · simp [hf y hy]
      rw [hz, finsum_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumFiberwiseOfFiniteSupportComplex
section
namespace GlobalTheory

theorem finsum_fiberwise_of_finite_support {A B : Type} (ρ : A → B) (f : A → ℂ)
    (hf : (Function.support f).Finite) :
    ∑ᶠ a, f a = ∑ᶠ b, ∑ᶠ a : {a // ρ a = b}, f a.1 := by
  classical
  set S := hf.toFinset with hS
  have hsupp : Function.support f ⊆ (S : Set A) := by simp [hS]
  have hinner : ∀ b, (∑ᶠ a : {a // ρ a = b}, f a.1) = ∑ a ∈ S with ρ a = b, f a := by
    intro b
    rw [finsum_subtype_eq_finsum_cond (fun a => ρ a = b)]
    have : (fun a => ∑ᶠ (_ : ρ a = b), f a) = fun a => if ρ a = b then f a else 0 := by
      funext a; exact finsum_eq_if
    rw [this, finsum_eq_sum_of_support_subset _ (s := S), Finset.sum_filter]
    intro a ha
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at ha
    obtain ⟨_, h⟩ := ha
    exact hsupp h
  simp_rw [hinner]
  rw [finsum_eq_sum_of_support_subset f hsupp,
    finsum_eq_sum_of_support_subset _ (s := S.image ρ)]
  · exact (Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem ρ ha) f).symm
  · intro b hb
    rw [Function.mem_support] at hb
    obtain ⟨a, ha, hab⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
    rw [Finset.mem_filter] at ha
    rw [Finset.coe_image]
    exact ⟨a, ha.1, ha.2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitFibreSwap
section
open scoped BigOperators

namespace GlobalTheory
namespace OrbitFibre

open MulAction Function

theorem finsum_sigma_iter {ι : Type} {κ : ι → Type} (f : (Σ i, κ i) → ℂ)
    (hf : (support f).Finite) : ∑ᶠ p, f p = ∑ᶠ i, ∑ᶠ k, f ⟨i, k⟩ := by
  classical
  set s := hf.toFinset with hs
  let t : Finset ι := s.image Sigma.fst
  let u : ∀ i, Finset (κ i) := fun i => s.preimage (Sigma.mk i) sigma_mk_injective.injOn
  have hsub : s ⊆ t.sigma u := by
    intro p hp
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_image_of_mem _ hp, by simpa [u] using hp⟩
  rw [finsum_eq_sum f hf, ← hs, Finset.sum_subset hsub ?_, Finset.sum_sigma]
  · rw [finsum_eq_sum_of_support_subset _ (s := t) ?_]
    · apply Finset.sum_congr rfl
      intro i _
      rw [finsum_eq_sum_of_support_subset _ (s := u i)]
      intro k hk
      simpa [u, hs] using hk
    · intro i hi
      rw [Function.mem_support] at hi
      by_contra hit
      apply hi
      have : ∀ k, f ⟨i, k⟩ = 0 := by
        intro k
        by_contra hk
        apply hit
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨i, k⟩, by simpa [hs] using hk, rfl⟩)
      simp [this]
  · intro p _ hp
    simpa [hs] using hp

variable {Γ A B J : Type} [Group Γ] [MulAction Γ A] [MulAction Γ B]


end OrbitFibre

end GlobalTheory
end

