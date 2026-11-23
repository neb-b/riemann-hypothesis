module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqMultipleOfStandardLattice
section
open IsDedekindDomain NumberField Matrix

namespace GlobalTheory.LatticeBetweenMultiples

lemma one_add_mulVec_mem {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (S : AddSubgroup (Fin n → v.adicCompletion F))
    (hGL : ∀ x : GL (Fin n) (v.adicCompletion F), (∀ i j, x.1 i j ∈ v.adicCompletionIntegers F) →
      (∀ i j, (x⁻¹).1 i j ∈ v.adicCompletionIntegers F) → ∀ w ∈ S, x.1.mulVec w ∈ S)
    (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) (hN : N * N = 0)
    (hNi : ∀ i j, N i j ∈ v.adicCompletionIntegers F) {w : Fin n → v.adicCompletion F}
    (hw : w ∈ S) : (1 + N).mulVec w ∈ S := by
  have h1 : (1 + N) * (1 - N) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hN, sub_zero, sub_add_cancel]
  have h2 : (1 - N) * (1 + N) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hN, add_zero, add_sub_cancel_right]
  have h1m : ∀ i j, (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈
      v.adicCompletionIntegers F := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hp : ∀ i j, (1 + N) i j ∈ v.adicCompletionIntegers F := by
    intro i j; rw [Matrix.add_apply]; exact add_mem (h1m i j) (hNi i j)
  have hm : ∀ i j, (1 - N) i j ∈ v.adicCompletionIntegers F := by
    intro i j; rw [Matrix.sub_apply]; exact sub_mem (h1m i j) (hNi i j)
  exact hGL ⟨1 + N, 1 - N, h1, h2⟩ hp hm w hw

theorem eq_multiple_of_standard_lattice : ∀ {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (S : AddSubgroup (Fin n → v.adicCompletion F)),
    (∀ o ∈ v.adicCompletionIntegers F, ∀ w ∈ S, o • w ∈ S) →
    (∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w : Fin n → v.adicCompletion F,
      (∀ i, w i ∈ v.adicCompletionIntegers F) → t • w ∈ S) →
    (∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w ∈ S, ∀ i, t * w i ∈ v.adicCompletionIntegers F) →
    (∀ x : GL (Fin n) (v.adicCompletion F), (∀ i j, x.1 i j ∈ v.adicCompletionIntegers F) →
      (∀ i j, (x⁻¹).1 i j ∈ v.adicCompletionIntegers F) → ∀ w ∈ S, x.1.mulVec w ∈ S) →
    ∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w, w ∈ S ↔ ∀ i, t * w i ∈ v.adicCompletionIntegers F := by
  intro F _ _ v n S hO ⟨tl, htl0, htl⟩ ⟨tu, htu0, htu⟩ hGL
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, one_ne_zero, fun w => ?_⟩
    have hw : w = 0 := Subsingleton.elim _ _
    subst hw
    exact ⟨fun _ i => i.elim0, fun _ => S.zero_mem⟩
  have memO : ∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 :=
    fun x => Iff.rfl

  have hbd : ∀ w ∈ S, ∀ i, Valued.v (w i) ≤ (Valued.v tu)⁻¹ := by
    intro w hw i
    have h := (memO _).1 (htu w hw i)
    rw [map_mul] at h
    have hu : Valued.v tu ≠ 0 := (Valuation.ne_zero_iff _).2 htu0
    calc Valued.v (w i) = (Valued.v tu)⁻¹ * (Valued.v tu * Valued.v (w i)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hu, one_mul]
      _ ≤ (Valued.v tu)⁻¹ * 1 := by gcongr
      _ = (Valued.v tu)⁻¹ := mul_one _
  let P : ℤ → Prop := fun k => ∃ w ∈ S, ∃ i, Valued.v (w i) =
    ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  obtain ⟨mB, hmB⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = (Valued.v tu)⁻¹ :=
    WithZero.ne_zero_iff_exists.1 (inv_ne_zero ((Valuation.ne_zero_iff _).2 htu0))
  have hPb : ∃ b : ℤ, ∀ z, P z → z ≤ b := by
    refine ⟨Multiplicative.toAdd mB, fun z ⟨w, hw, i, hz⟩ => ?_⟩
    have h := hbd w hw i
    rw [hz, ← hmB, WithZero.coe_le_coe] at h
    exact Multiplicative.ofAdd_le.1 (by simpa using h)
  let i₀' : Fin n := ⟨0, hn⟩
  have hPn : ∃ z, P z := by
    have hmem : tl • (fun _ => (1 : v.adicCompletion F)) ∈ S := htl _ (fun _ => one_mem _)
    obtain ⟨m, hm⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = Valued.v tl :=
      WithZero.ne_zero_iff_exists.1 ((Valuation.ne_zero_iff _).2 htl0)
    refine ⟨Multiplicative.toAdd m, _, hmem, i₀', ?_⟩
    simp [← hm]
  obtain ⟨lb, ⟨w₀, hw₀, i₀, hc⟩, hlb⟩ := Int.exists_greatest_of_bdd hPb hPn
  set c := w₀ i₀ with hcdef
  have hvc : Valued.v c ≠ 0 := by rw [hc]; exact WithZero.coe_ne_zero
  have hc0 : c ≠ 0 := fun h => hvc (by rw [h, map_zero])
  have hmax : ∀ w ∈ S, ∀ i, Valued.v (w i) ≤ Valued.v c := by
    intro w hw i
    by_cases h0 : w i = 0
    · rw [h0, map_zero]; exact zero_le'
    obtain ⟨m, hm⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = Valued.v (w i) :=
      WithZero.ne_zero_iff_exists.1 ((Valuation.ne_zero_iff _).2 h0)
    have hk := hlb (Multiplicative.toAdd m) ⟨w, hw, i, by simp [← hm]⟩
    rw [← hm, hc, WithZero.coe_le_coe]
    exact Multiplicative.toAdd_le.1 (by simpa using hk)
  have hint : ∀ w ∈ S, ∀ i, c⁻¹ * w i ∈ v.adicCompletionIntegers F := by
    intro w hw i
    rw [memO, map_mul, map_inv₀]
    calc (Valued.v c)⁻¹ * Valued.v (w i) ≤ (Valued.v c)⁻¹ * Valued.v c :=
          by gcongr; exact hmax w hw i
      _ = 1 := inv_mul_cancel₀ hvc

  have hsingle0 : Pi.single i₀ c ∈ S := by
    let N : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
      fun a b => if b = i₀ ∧ a ≠ i₀ then -(c⁻¹ * w₀ a) else 0
    have hN : N * N = 0 := by
      funext a b
      simp only [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      by_cases hm : m = i₀ <;> simp [N, hm]
    have hNi : ∀ i j, N i j ∈ v.adicCompletionIntegers F := by
      intro i j
      simp only [N]
      split_ifs
      · exact neg_mem (hint w₀ hw₀ i)
      · exact zero_mem _
    have h := one_add_mulVec_mem v S hGL N hN hNi hw₀
    convert h using 1
    funext a
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
    by_cases ha : a = i₀
    · subst ha
      simp [N, Matrix.mulVec, dotProduct, hcdef]
    · simp [N, Matrix.mulVec, dotProduct, ha, Pi.single_apply, ← hcdef]
      field_simp
      ring
  have hsingle : ∀ j, Pi.single j c ∈ S := by
    intro j
    by_cases hj : j = i₀
    · subst hj; exact hsingle0
    let N : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
      fun a b => if a = j ∧ b = i₀ then 1 else 0
    have hN : N * N = 0 := by
      funext a b
      simp only [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      by_cases hm : m = i₀
      · subst hm; simp [N, Ne.symm hj]
      · simp [N, hm]
    have hNi : ∀ i k, N i k ∈ v.adicCompletionIntegers F := by
      intro i k
      simp only [N]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h := one_add_mulVec_mem v S hGL N hN hNi hsingle0
    have heq : (1 + N).mulVec (Pi.single i₀ c) = Pi.single i₀ c + Pi.single j c := by
      funext a
      rw [Matrix.add_mulVec, Matrix.one_mulVec]
      simp [N, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [heq] at h
    simpa using S.sub_mem h hsingle0
  refine ⟨c⁻¹, inv_ne_zero hc0, fun w => ⟨fun hw i => hint w hw i, fun hw => ?_⟩⟩
  have hsum : w = ∑ j, (c⁻¹ * w j) • Pi.single j c := by
    funext a
    rw [Finset.sum_apply, Finset.sum_eq_single a]
    · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      field_simp
    · intro b _ hb
      simp [Pi.single_apply, Ne.symm hb]
    · simp
  rw [hsum]
  exact S.sum_mem (fun j _ => hO _ (hw j) _ (hsingle j))

end GlobalTheory.LatticeBetweenMultiples
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallResidueFieldFunctional
section
namespace GlobalTheory

theorem eq_zero_of_forall_residueField_functional (A M : Type) [CommRing A] [IsReduced A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M] (x : M)
    (hx : ∀ (p : Ideal A) [p.IsPrime] (l : M →ₗ[A] p.ResidueField), l x = 0) : x = 0 := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  have hg : g x = 0 := by
    funext i
    have hmem : g x i ∈ nilradical A := by
      rw [nilradical_eq_sInf, Ideal.mem_sInf]
      intro (p : Ideal A) (hp : p.IsPrime)
      have h := hx p ((Algebra.linearMap A p.ResidueField) ∘ₗ (LinearMap.proj i) ∘ₗ g)
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
        Function.eval, Algebra.linearMap_apply] at h
      have h' : g x i ∈ RingHom.ker (algebraMap A p.ResidueField) := h
      rwa [Ideal.ker_algebraMap_residueField] at h'
    exact (mem_nilradical.mp hmem).eq_zero
  have := congrArg (fun y => f y) hg
  simpa [← LinearMap.comp_apply, hfg] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfIntertwineOfIsCoprimeCharpoly
section
namespace GlobalTheory.IntertwinerCoprimeCharpoly

open Polynomial

theorem pow_intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C) (n : ℕ) :
    C * A ^ n = B ^ n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc]

theorem aeval_intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C) (p : K[X]) :
    C * aeval A p = aeval B p * C := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), Matrix.mul_add, Matrix.add_mul, hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, pow_intertwine A B C h n]

theorem eq_zero_of_intertwine_of_isCoprime_charpoly {K : Type} [Field K] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K)
    (hcop : IsCoprime (Matrix.charpoly A) (Matrix.charpoly B)) (h : C * A = B * C) :
    C = (0 : Matrix (Fin b) (Fin a) K) := by
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : aeval B (u * A.charpoly + v * B.charpoly) = 1 := by rw [huv, map_one]
  rw [map_add (f := _), map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero] at h1
  have h2 : aeval B A.charpoly * C = 0 := by
    rw [← aeval_intertwine A B C h, Matrix.aeval_self_charpoly, Matrix.mul_zero]
  calc C = 1 * C := (Matrix.one_mul C).symm
    _ = (aeval B u * aeval B A.charpoly) * C := by rw [h1]
    _ = aeval B u * (aeval B A.charpoly * C) := Matrix.mul_assoc _ _ _
    _ = 0 := by rw [h2, Matrix.mul_zero]

theorem main : ∀ {K : Type} [inst : Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K),
    IsCoprime (Matrix.charpoly A) (Matrix.charpoly B) → C * A = B * C →
      C = (0 : Matrix (Fin b) (Fin a) K) :=
  fun A B C hcop h => eq_zero_of_intertwine_of_isCoprime_charpoly A B C hcop h

end GlobalTheory.IntertwinerCoprimeCharpoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssEtaleLocalLeOfDirected
section
open IsLocalRing

namespace GlobalTheory

theorem essEtaleLocal_le_of_directed :
  ∀ (R T : Type) [CommRing R] [CommRing T] [Algebra R T] (U : Subalgebra R T) (μ : Type) [Preorder μ] [IsDirected μ (· ≤ ·)] [Nonempty μ] (V : μ → Subalgebra R T), Monotone V → (∀ x ∈ U, ∃ m, x ∈ V m) → (∀ m, ∀ x ∈ V m, ∀ y ∈ U, x * y = 1 → ∃ z ∈ V m, x * z = 1) → ∀ (W : Subalgebra R T), W ≤ U → (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] W)) → ∃ m, W ≤ V m := by
  classical
  intro R T _ _ _ U μ _ _ _ V hmono hcov hloc W hWU hW
  obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hW
  let L := Localization.AtPrime q
  let φ : A →ₐ[R] T := W.val.comp (e.toAlgHom.comp (IsScalarTower.toAlgHom R A L))
  have hφW : ∀ a, φ a ∈ W := fun a => (e (algebraMap A L a)).2
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R A).FG)
  choose f hf using fun a : A => hcov (φ a) (hWU (hφW a))
  obtain ⟨M, hM⟩ := (s.image f).exists_le
  have hrange : ∀ a, φ a ∈ V M := by
    have hle : (⊤ : Subalgebra R A) ≤ (V M).comap φ := by
      rw [← hs]
      refine Algebra.adjoin_le ?_
      intro a ha
      exact hmono (hM _ (Finset.mem_image_of_mem f ha)) (hf a)
    intro a
    exact hle Algebra.mem_top
  refine ⟨M, fun w hw => ?_⟩
  obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective q.primeCompl (e.symm ⟨w, hw⟩)
  set y : T := ((e (IsLocalization.mk' L (1 : A) t) : W) : T) with hy
  have hyU : y ∈ U := hWU (e _).2
  have hxy : φ t * y = 1 := by
    have h1 : algebraMap A L t * IsLocalization.mk' L (1:A) t = 1 := by
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self']
    have h2 : ((e (algebraMap A L t * IsLocalization.mk' L (1:A) t) : W) : T) = 1 := by
      rw [h1, map_one]; rfl
    rw [map_mul, Subalgebra.coe_mul] at h2
    exact h2
  obtain ⟨z, hzV, hz⟩ := hloc M (φ t) (hrange t) y hyU hxy
  have hzy : z = y := by
    calc z = (y * φ t) * z := by rw [mul_comm y, hxy, one_mul]
      _ = y * (φ t * z) := by ring
      _ = y := by rw [hz, mul_one]
  have hw' : w = φ a * y := by
    have h1 : (⟨w, hw⟩ : W) = e (IsLocalization.mk' L a t) := by
      change IsLocalization.mk' L a t = _ at hat
      rw [hat, AlgEquiv.apply_symm_apply]
    have h2 : IsLocalization.mk' L a t = algebraMap A L a * IsLocalization.mk' L (1:A) t := by
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one]
    have h3 : w = ((e (IsLocalization.mk' L a t) : W) : T) := congrArg Subtype.val h1
    rw [h3, h2, map_mul, Subalgebra.coe_mul]
    rfl
  rw [hw', ← hzy]
  exact (V M).mul_mem (hrange a) hzV

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAdjoinBaseChangeImage
section
open TensorProduct

namespace GlobalTheory

theorem etale_adjoin_baseChange_image (R S B : Type) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B] (A₀ : Subalgebra R S)
    (B₀ : Type) [CommRing B₀] [Algebra A₀ B₀] [Algebra.Etale A₀ B₀] (e : B ≃ₐ[S] S ⊗[A₀] B₀)
    (S' : Subalgebra R S) (h : A₀ ≤ S') :
    ∃ (_ : Algebra S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))))
      (_ : IsScalarTower R S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))),
      Algebra.Etale S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))) := by
  set C := Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))) with hC
  letI : Algebra A₀ S' := (Subalgebra.inclusion h).toRingHom.toAlgebra
  let ι : S' →ₐ[A₀] S :=
    { toRingHom := S'.val.toRingHom
      commutes' := fun _ => rfl }
  let Φ : S' ⊗[A₀] B₀ →ₐ[A₀] S ⊗[A₀] B₀ := Algebra.TensorProduct.map ι (AlgHom.id A₀ B₀)
  let Ψ : S' ⊗[A₀] B₀ →+* B := (e.symm : S ⊗[A₀] B₀ →+* B).comp Φ.toRingHom
  haveI : Module.Flat A₀ B₀ := inferInstance
  have hΦ : Function.Injective Φ := by
    have hl : (Φ.toLinearMap : S' ⊗[A₀] B₀ →ₗ[A₀] S ⊗[A₀] B₀) = LinearMap.rTensor B₀ ι.toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      rfl
    have : Function.Injective (LinearMap.rTensor B₀ ι.toLinearMap) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b hab => Subtype.ext hab)
    rw [← hl] at this
    exact this
  have hΨ : Function.Injective Ψ := e.symm.injective.comp hΦ
  have htmul : ∀ (s : S') (b : B₀), Ψ (s ⊗ₜ b) = algebraMap S B s * e.symm (1 ⊗ₜ b) := by
    intro s b
    have : ((s : S) ⊗ₜ[A₀] b : S ⊗[A₀] B₀) = algebraMap S (S ⊗[A₀] B₀) s * (1 ⊗ₜ b) := by
      simp [Algebra.TensorProduct.algebraMap_apply]
    show e.symm ((s : S) ⊗ₜ[A₀] b) = _
    rw [this, map_mul, AlgEquiv.commutes]
  have h1 : e.symm ((1 : S) ⊗ₜ[A₀] (1 : B₀)) = 1 := by
    rw [← Algebra.TensorProduct.one_def, map_one]
  have hsub : ∀ x, Ψ x ∈ C := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s b =>
      rw [htmul]
      exact C.mul_mem (Algebra.subset_adjoin (Or.inl ⟨s, s.2, rfl⟩))
        (Algebra.subset_adjoin (Or.inr ⟨b, rfl⟩))
    | add x y hx hy => rw [map_add (f := _)]; exact C.add_mem hx hy
  have hsurj : (C : Set B) ⊆ Set.range Ψ := by
    have := Algebra.adjoin_eq_ring_closure (R := R)
      ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))
    intro y hy
    have hy' : y ∈ (C.toSubring) := hy
    rw [hC, this] at hy'
    have hle : Subring.closure (Set.range (algebraMap R B) ∪
        ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))
        ≤ Ψ.range := by
      rw [Subring.closure_le]
      rintro z (⟨r, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨b, rfl⟩)
      · refine ⟨(algebraMap R S' r) ⊗ₜ 1, ?_⟩
        rw [htmul, h1, mul_one, IsScalarTower.algebraMap_apply R S B]
        rfl
      · refine ⟨(⟨s, hs⟩ : S') ⊗ₜ 1, ?_⟩
        rw [htmul, h1, mul_one]
      · refine ⟨1 ⊗ₜ b, ?_⟩
        rw [htmul]; simp
    exact hle hy'
  let f : S' ⊗[A₀] B₀ →+* C := Ψ.codRestrict C.toSubring hsub
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => hΨ (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hsurj hy
    exact ⟨x, rfl⟩
  let eqv : S' ⊗[A₀] B₀ ≃+* C := RingEquiv.ofBijective f hf
  letI alg : Algebra S' C := (f.comp (algebraMap S' (S' ⊗[A₀] B₀))).toAlgebra
  have tower : IsScalarTower R S' C := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    apply Subtype.ext
    show algebraMap R B r = Ψ (algebraMap S' (S' ⊗[A₀] B₀) (algebraMap R S' r))
    rw [Algebra.TensorProduct.algebraMap_apply, htmul, h1, mul_one,
      IsScalarTower.algebraMap_apply R S B]
    rfl
  refine ⟨alg, tower, ?_⟩
  let eA : S' ⊗[A₀] B₀ ≃ₐ[S'] C := AlgEquiv.ofRingEquiv (f := eqv) (fun _ => rfl)
  haveI : Algebra.Etale S' (S' ⊗[A₀] B₀) := Algebra.Etale.baseChange A₀ B₀ S'
  exact Algebra.Etale.of_equiv eA

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAdjoinRootXPowSubC
section
open IsLocalRing Polynomial

namespace GlobalTheory

theorem etale_adjoinRoot_X_pow_sub_C : ∀ (R : Type) [CommRing R] (n : ℕ) (u : R), IsUnit (n : R) →
    IsUnit u → Algebra.Etale R (AdjoinRoot (Polynomial.X ^ n - Polynomial.C u : Polynomial R)) := by
  intro R _ n u hn hu
  set f : R[X] := X ^ n - C u with hfdef
  have key : f.Monic ∧ IsUnit (AdjoinRoot.mk f (derivative f)) := by
    by_cases hn0 : n = 0
    · subst hn0
      have h01 : (0 : R) = 1 := isUnit_zero_iff.1 (by simpa using hn)
      have : Subsingleton R := subsingleton_of_zero_eq_one h01
      have : Subsingleton (AdjoinRoot f) := (AdjoinRoot.of f).codomain_trivial
      exact ⟨Subsingleton.elim _ _, isUnit_of_subsingleton _⟩
    have hm : f.Monic := monic_X_pow_sub_C _ hn0
    have h1 : AdjoinRoot.root f ^ n = algebraMap R _ u := by
      have := AdjoinRoot.eval₂_root f
      simpa [hfdef, sub_eq_zero] using this
    have hr : IsUnit (AdjoinRoot.root f) :=
      (isUnit_pow_iff hn0).1 (h1 ▸ hu.map _)
    refine ⟨hm, ?_⟩
    have e : AdjoinRoot.mk f (derivative f) = algebraMap R _ (n : R) * AdjoinRoot.root f ^ (n - 1) := by
      simp [hfdef, derivative_X_pow, AdjoinRoot.algebraMap_eq]
    rw [e]
    exact (hn.map _).mul (hr.pow _)
  obtain ⟨hm, h⟩ := key
  let P : StandardEtalePair R := ⟨f, hm, derivative f, 1, 0, 1, by simp⟩
  exact .of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ (Localization.Away (AdjoinRoot.mk f (derivative f))) _
      h).symm.restrictScalars R))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFractionFieldOfEtaleHeightOne
section
open IsLocalRing

namespace GlobalTheory

theorem etale_fractionField_of_etale_height_one :
    ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A]
      [Algebra R A], ¬ IsField R →
      (∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
      Algebra.Etale (Localization.AtPrime (⊥ : Ideal R))
        (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) A) := by
  intro R A _ _ _ _ _ _ hR h

  have hm : maximalIdeal R ≠ ⊥ := fun hm => hR ((isField_iff_maximalIdeal_eq).mpr hm)
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨P, hPmin, -⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem _).mpr hxm)
  haveI hP : P.IsPrime := hPmin.1.1
  have hxP : x ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hPmin.1.2
  have hPne : P ≠ ⊥ := fun e => hx0 (by simpa [e] using hxP)
  haveI : (Ideal.span {x}).IsPrincipal := ⟨⟨x, rfl⟩⟩
  have h1 : P.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hPmin)
    (Order.one_le_iff_ne_zero.mpr (fun e => hPne (Ideal.height_eq_zero_iff_eq_bot.mp e)))
  haveI := h P h1
  set K := Localization.AtPrime (⊥ : Ideal R)
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap R K y) := by
    intro y
    have hy : (y : R) ∈ (⊥ : Ideal R).primeCompl := by
      intro hb
      have hb' : (y : R) = 0 := Ideal.mem_bot.mp hb
      exact y.2 (by rw [hb']; exact P.zero_mem)
    exact IsLocalization.map_units K (⟨y, hy⟩ : (⊥ : Ideal R).primeCompl)
  letI : Algebra (Localization.AtPrime P) K :=
    (IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) hunit).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) K :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      change _ = IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) hunit _
      rw [IsLocalization.lift_eq])
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P) K K A)

end GlobalTheory
end

