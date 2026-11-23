module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMulTorsMemLatticeIff
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem nsmul_zmod_eq_zero_iff_dvd (N : ℕ) [NeZero N] (M : ℕ) (a : ZMod N) :
    M • a = 0 ↔ N ∣ M * a.val := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]

theorem natCast_mul_tors_mem_lattice_iff :
    ∀ (N : ℕ) [NeZero N] (τ : ℍ) (M : ℕ) (x : Fin 2 → ZMod N),
      (M : ℂ) * tors N τ x ∈ (tauPair τ).lattice ↔ M • x = 0 := by
  intro N _ τ M x
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hx : M • x = 0 ↔ N ∣ M * (x 0).val ∧ N ∣ M * (x 1).val := by
    rw [← nsmul_zmod_eq_zero_iff_dvd, ← nsmul_zmod_eq_zero_iff_dvd, funext_iff, Fin.forall_fin_two]
    rfl
  have hm : ∀ z : ℂ, z ∈ (tauPair τ).lattice ↔ ∃ m n : ℤ, m * (τ : ℂ) + n = z := by
    intro z
    rw [PeriodPair.mem_lattice]; simp [tauPair]
  rw [hx, hm]
  constructor
  · rintro ⟨m, n, h⟩
    have h1 : ((N * m - M * (x 0).val : ℤ) : ℂ) * (τ : ℂ) + ((N * n - M * (x 1).val : ℤ) : ℂ) = 0 := by
      unfold tors at h
      field_simp at h
      push_cast
      linear_combination h
    have him := congrArg Complex.im h1
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero,
      Complex.zero_im, UpperHalfPlane.coe_im, mul_eq_zero, τ.im_pos.ne', or_false, Int.cast_eq_zero] at him
    rw [him, Int.cast_zero, zero_mul, zero_add, Int.cast_eq_zero] at h1
    constructor
    · rw [← Int.natCast_dvd_natCast]
      exact ⟨m, by push_cast at him ⊢; linear_combination -him⟩
    · rw [← Int.natCast_dvd_natCast]
      exact ⟨n, by push_cast at h1 ⊢; linear_combination -h1⟩
  · rintro ⟨⟨m, hm0⟩, ⟨n, hn0⟩⟩
    refine ⟨m, n, ?_⟩
    have a : (M : ℂ) * ((x 0).val : ℂ) = N * m := by exact_mod_cast hm0
    have b : (M : ℂ) * ((x 1).val : ℂ) = N * n := by exact_mod_cast hn0
    unfold tors
    field_simp
    push_cast
    linear_combination -(τ : ℂ) * a - b

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMulEsymmRootsPow
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem map_range_mul_of_periodic {β : Type} (g : ℕ → β) (e : ℕ) (hg : ∀ i, g (e + i) = g i) (m : ℕ) :
    (Multiset.range (e * m)).map g = m • (Multiset.range e).map g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, add_comm (e * m), Multiset.range_add, Multiset.map_add (f := _), Multiset.map_map,
      succ_nsmul', ← ih]
    congr 1
    exact Multiset.map_congr rfl fun i _ => hg i

theorem roots_pow_eq_map_range {F : Type} [Field F] [Finite F] (f : F[X]) (m : ℕ) (hf : f.Monic)
    (hi : Irreducible f) (α : AlgebraicClosure F)
    (hα : α ∈ ((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots) :
    ((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots =
      (Multiset.range (f ^ m).natDegree).map fun i => α ^ Nat.card F ^ i := by
  rw [Polynomial.map_pow, roots_pow] at hα ⊢
  have h1 := Multiset.mem_of_mem_nsmul hα
  have h2 : aeval α f = 0 := by
    rw [← eval_map_algebraMap]
    exact (mem_roots'.1 h1).2
  have h3 : f = minpoly F α := minpoly.eq_of_irreducible_of_monic hi h2 hf
  have hper := (minpoly_natDegree_dvd_iff_pow α _).1 dvd_rfl
  rw [natDegree_pow, mul_comm, h3, roots_minpoly_eq_map_range, map_range_mul_of_periodic]
  intro i
  simp only [pow_add, pow_mul, hper]

theorem natDegree_mul_esymm_roots_pow : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (f : F[X]) (m k s : ℕ), f.Monic → Irreducible f → ((f ^ m).natDegree : ℂ) * (((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).esymm s = ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s, rootSum θ (k * ∑ i ∈ I, Nat.card F ^ i) (f ^ m) := by
  intro F _ _ θ f m k s hf hi
  set R := ((f ^ m).map (algebraMap F (AlgebraicClosure F))).roots with hR
  have hcard : R.card = (f ^ m).natDegree := by
    rw [hR, IsAlgClosed.card_roots_eq_natDegree, natDegree_map]
  have key : ∀ α ∈ R, (R.map fun α => θ α ^ k).esymm s =
      ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s,
        θ α ^ (k * ∑ i ∈ I, Nat.card F ^ i) := by
    intro α hα
    have h := roots_pow_eq_map_range f m hf hi α hα
    rw [← hR] at h
    conv_lhs => rw [h]
    rw [Multiset.map_map, ← Finset.range_val, Finset.esymm_map_val]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp, map_pow, ← pow_mul, mul_comm]
  have h2 : (R.map fun _ => (R.map fun α => θ α ^ k).esymm s).sum =
      (R.map fun α => ∑ I ∈ (Finset.range (f ^ m).natDegree).powersetCard s,
        θ α ^ (k * ∑ i ∈ I, Nat.card F ^ i)).sum := by
    rw [Multiset.map_congr rfl key]
  rw [Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul] at h2
  rw [h2, Multiset.sum_map_sum]
  rfl

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyEquivOfCardHom
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.HomCount

theorem card_ker_eq (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X]
    [AddCommGroup M] [Module R M] (Y : Submodule R X) :
    Nat.card {f : X →ₗ[R] M // LinearMap.ker f = Y}
      = Nat.card {g : (X ⧸ Y) →ₗ[R] M // LinearMap.ker g = ⊥} := by
  refine Nat.card_congr
    { toFun := fun f => ⟨Y.liftQ f.1 f.2.ge, Submodule.ker_liftQ_eq_bot _ _ _ f.2.le⟩
      invFun := fun g => ⟨g.1 ∘ₗ Y.mkQ, by
        rw [LinearMap.ker_comp, g.2]
        exact Y.ker_mkQ⟩
      left_inv := fun f => Subtype.ext (Y.liftQ_mkQ _ _)
      right_inv := fun g => Subtype.ext ?_ }
  apply Submodule.linearMap_qext
  exact Y.liftQ_mkQ _ _

theorem finite_hom (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X] [Finite X]
    [AddCommGroup M] [Module R M] [Finite M] : Finite (X →ₗ[R] M) :=
  Finite.of_injective (fun f : X →ₗ[R] M => (f : X → M)) DFunLike.coe_injective

theorem card_hom_eq_sum (R : Type) [Ring R] (X M : Type) [AddCommGroup X] [Module R X] [Finite X]
    [AddCommGroup M] [Module R M] [Finite M] [Fintype (Submodule R X)] :
    Nat.card (X →ₗ[R] M)
      = ∑ Y : Submodule R X, Nat.card {f : X →ₗ[R] M // LinearMap.ker f = Y} := by
  haveI := finite_hom R X M
  rw [← Nat.card_sigma]
  exact Nat.card_congr (Equiv.sigmaFiberEquiv (fun f : X →ₗ[R] M => LinearMap.ker f)).symm

theorem card_inj_eq (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M]
    [AddCommGroup N] [Module R N] [Finite N]
    (h : ∀ (X : Type) [AddCommGroup X] [Module R X] [Finite X],
      Nat.card (X →ₗ[R] M) = Nat.card (X →ₗ[R] N)) (n : ℕ) :
    ∀ (X : Type) [AddCommGroup X] [Module R X] [Finite X], Nat.card X = n →
      Nat.card {f : X →ₗ[R] M // LinearMap.ker f = ⊥}
        = Nat.card {f : X →ₗ[R] N // LinearMap.ker f = ⊥} := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ _ hX
    haveI : Finite (Submodule R X) :=
      Finite.of_injective (fun Y : Submodule R X => (Y : Set X)) SetLike.coe_injective
    letI : Fintype (Submodule R X) := Fintype.ofFinite _
    have h1 := h X
    rw [card_hom_eq_sum, card_hom_eq_sum,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (⊥ : Submodule R X)),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (⊥ : Submodule R X))] at h1
    have h2 : ∑ Y ∈ Finset.univ.erase (⊥ : Submodule R X),
          Nat.card {f : X →ₗ[R] M // LinearMap.ker f = Y}
        = ∑ Y ∈ Finset.univ.erase (⊥ : Submodule R X),
          Nat.card {f : X →ₗ[R] N // LinearMap.ker f = Y} := by
      refine Finset.sum_congr rfl fun Y hY => ?_
      have hY' : Y ≠ ⊥ := Finset.ne_of_mem_erase hY
      rw [card_ker_eq R X M, card_ker_eq R X N]
      haveI : Finite (X ⧸ Y) := Finite.of_surjective _ Y.mkQ_surjective
      refine ih (Nat.card (X ⧸ Y)) ?_ (X ⧸ Y) rfl
      rw [← hX]
      refine lt_of_le_of_ne (Nat.card_le_card_of_surjective _ Y.mkQ_surjective) fun he => hY' ?_
      have hb : Function.Bijective Y.mkQ :=
        (Function.Surjective.bijective_of_nat_card_le Y.mkQ_surjective he.ge)
      rw [← Y.ker_mkQ]
      exact LinearMap.ker_eq_bot.2 hb.1
    omega

theorem nonempty_equiv_of_card_hom :
    ∀ (R : Type) [Ring R] (M N : Type) [AddCommGroup M] [Module R M] [Finite M] [AddCommGroup N] [Module R N] [Finite N], (∀ (X : Type) [AddCommGroup X] [Module R X] [Finite X], Nat.card (X →ₗ[R] M) = Nat.card (X →ₗ[R] N)) → Nonempty (M ≃ₗ[R] N) := by
  intro R _ M N _ _ _ _ _ _ h
  haveI := finite_hom R M M
  haveI := finite_hom R N N
  have h1 := card_inj_eq R M N h _ M rfl
  have h2 := card_inj_eq R M N h _ N rfl
  haveI : Nonempty {f : M →ₗ[R] M // LinearMap.ker f = ⊥} := ⟨⟨LinearMap.id, LinearMap.ker_id⟩⟩
  haveI : Nonempty {f : N →ₗ[R] N // LinearMap.ker f = ⊥} := ⟨⟨LinearMap.id, LinearMap.ker_id⟩⟩
  have p1 : 0 < Nat.card {f : M →ₗ[R] N // LinearMap.ker f = ⊥} := h1 ▸ Nat.card_pos
  have p2 : 0 < Nat.card {f : N →ₗ[R] M // LinearMap.ker f = ⊥} := h2 ▸ Nat.card_pos
  obtain ⟨⟨f, hf⟩⟩ := (Nat.card_pos_iff.1 p1).1
  obtain ⟨⟨g, hg⟩⟩ := (Nat.card_pos_iff.1 p2).1
  rw [LinearMap.ker_eq_bot] at hf hg
  have hb : Function.Bijective f :=
    hf.bijective_of_nat_card_le (Nat.card_le_card_of_injective _ hg)
  exact ⟨LinearEquiv.ofBijective f hb⟩

end GlobalTheory.HomCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaussianConvolutionSeriesCoefficientLeIntegrStatement
section
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_gaussianConvolutionSeriesCoefficient_le_integral : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 ≤ b → 0 ≤ c → ∀ (h : SchwartzMap E ℂ) (j : ℕ),
    ‖GlobalTheory.ConvSeries.coef b c (⇑h) j‖ ≤ ∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j := by
  first | exact @GlobalTheory.ConvSeries.norm_coef_le_integral | exact GlobalTheory.ConvSeries.norm_coef_le_integral | (intros; apply GlobalTheory.ConvSeries.norm_coef_le_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivPdLe
section
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SliceTaylor

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_padL_le {κ κ' : Type} [Fintype κ] [Fintype κ'] (h : κ → V) :
    ‖(padL (κ' := κ') h : κ ⊕ κ' → V)‖ ≤ ‖h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  cases i with
  | inl i => simpa [padL] using norm_le_pi_norm h i
  | inr j => simp [padL]

theorem norm_inrL_le (κ κ' : Type) [Fintype κ] [Fintype κ'] :
    ‖(inrL (V := V) κ κ')‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  cases i with
  | inl i => simp [inrL]
  | inr j => simpa [inrL] using norm_le_pi_norm y j

theorem norm_le_norm_elim_add {κ κ' : Type} [Fintype κ] [Fintype κ'] (x h : κ → V) (y : κ' → V) (s : ℝ) :
    ‖y‖ ≤ ‖(Sum.elim x y : κ ⊕ κ' → V) + s • padL h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have := norm_le_pi_norm ((Sum.elim x y : κ ⊕ κ' → V) + s • padL h) (Sum.inr j)
  simp only [Pi.add_apply, Pi.smul_apply, padL, Sum.elim_inr, Pi.zero_apply, smul_zero, add_zero] at this
  exact this

theorem norm_iteratedFDeriv_pd_le {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a : X) (g : SchwartzMap X ℂ) (n : ℕ) (w : X) :
    ‖iteratedFDeriv ℝ n (pd a g) w‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ (n + 1) g w‖ := by
  have e1 : (⇑(pd a g)) = fun y => fderiv ℝ g y a := by funext y; exact pd_apply a g y
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
    g.smooth'.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
  have e : iteratedFDeriv ℝ n (pd a g) w = fderiv ℝ (iteratedFDeriv ℝ n g) w a := by
    ext m
    rw [e1, ← GlobalTheory.SchwartzTranslate.fderiv_iteratedFDeriv_apply_comm a n g g.smooth']
    have := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => X) ℂ m).hasFDerivAt.comp
      w (hd w).hasFDerivAt).fderiv
    have e2 : (fun y => iteratedFDeriv ℝ n g y m) =
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => X) ℂ m) ∘ iteratedFDeriv ℝ n g := rfl
    rw [e2, this]
    rfl
  rw [e, ← norm_fderiv_iteratedFDeriv, mul_comm]
  exact (fderiv ℝ (iteratedFDeriv ℝ n g) w).le_opNorm a

theorem elim_add_padL {κ κ' : Type} [Fintype κ] [Fintype κ'] (x h : κ → V) (y : κ' → V) :
    (Sum.elim (x + h) y : κ ⊕ κ' → V) = Sum.elim x y + padL h := by
  funext i
  cases i with
  | inl i => simp [padL]
  | inr j => simp [padL]

theorem seminorm_slice_taylor_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (k n : ℕ) (x h : κ → V) :
    SchwartzMap.seminorm ℂ k n (sliceR f (x + h) - sliceR f x - sliceR (pd (padL (κ' := κ') h) f) x) ≤
      ‖h‖ ^ 2 * SchwartzMap.seminorm ℂ k (n + 2) f := by
  set a : κ ⊕ κ' → V := padL (κ' := κ') h with ha
  set f1 := pd a f with hf1
  set f2 := pd a f1 with hf2
  set M := ‖h‖ ^ 2 * SchwartzMap.seminorm ℂ k (n + 2) f with hM
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun y => ?_
  have hnn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have c0 : ContDiff ℝ ∞ f := f.smooth'
  have c1 : ContDiff ℝ ∞ f1 := f1.smooth'
  have e1 : (fun z => fderiv ℝ f z a) = ⇑f1 := by funext z; exact (pd_apply a f z).symm
  have e2 : (fun z => fderiv ℝ f1 z a) = ⇑f2 := by funext z; exact (pd_apply a f1 z).symm
  set G : (κ ⊕ κ' → V) → ℂ := fun w => f (w + a) - f w - f1 w with hG
  have cG : ContDiff ℝ ∞ G :=
    ((c0.comp (contDiff_id.add contDiff_const)).sub c0).sub c1
  set c : κ ⊕ κ' → V := Sum.elim x 0 with hc
  have efun : ⇑(sliceR f (x + h) - sliceR f x - sliceR f1 x)
      = (fun u => G (u + c)) ∘ ⇑(inrL (V := V) κ κ') := by
    funext y'
    have hy : (Sum.elim x y' : κ ⊕ κ' → V) = inrL κ κ' y' + c := by
      rw [add_comm]; exact congrFun (elim_eq_add x) y'
    simp only [SchwartzMap.sub_apply, sliceR_apply, Function.comp_apply, hG, ← hy,
      elim_add_padL, ha]
  have cGc : ContDiff ℝ ∞ (fun u => G (u + c)) := cG.comp (contDiff_id.add contDiff_const)
  have eit : iteratedFDeriv ℝ n ⇑(sliceR f (x + h) - sliceR f x - sliceR f1 x) y
      = (iteratedFDeriv ℝ n f (Sum.elim x y + a) - iteratedFDeriv ℝ n f (Sum.elim x y)
          - iteratedFDeriv ℝ n f1 (Sum.elim x y)).compContinuousLinearMap
          (fun _ => inrL (V := V) κ κ') := by
    have hy : inrL (V := V) κ κ' y + c = Sum.elim x y := by
      rw [add_comm]; exact (congrFun (elim_eq_add x) y).symm
    rw [efun, ContinuousLinearMap.iteratedFDeriv_comp_right _ cGc _ hnn, iteratedFDeriv_comp_add_right, hy]
    congr 1
    have ct : ContDiff ℝ ∞ (fun z => f (z + a)) := c0.comp (contDiff_id.add contDiff_const)
    change iteratedFDeriv ℝ n (((fun z => f (z + a)) - ⇑f) - ⇑f1) _ = _
    rw [iteratedFDeriv_sub_apply (f := (fun z => f (z + a)) - ⇑f) (g := ⇑f1) ((ct.sub c0).of_le hnn).contDiffAt (c1.of_le hnn).contDiffAt,
      iteratedFDeriv_sub_apply (ct.of_le hnn).contDiffAt (c0.of_le hnn).contDiffAt,
      iteratedFDeriv_comp_add_right]
  rw [eit]
  set z : κ ⊕ κ' → V := Sum.elim x y with hz
  have key := GlobalTheory.SchwartzTranslate.taylor_two (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f (z + s • a))
    (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f1 (z + s • a))
    (fun s : ℝ => ‖y‖ ^ k • iteratedFDeriv ℝ n f2 (z + s • a))
    (fun s => by
      have := GlobalTheory.SchwartzTranslate.hasDerivAt_iteratedFDeriv_line a n f c0 z s
      rw [e1] at this
      exact this.const_smul (‖y‖ ^ k))
    (fun s => by
      have := GlobalTheory.SchwartzTranslate.hasDerivAt_iteratedFDeriv_line a n f1 c1 z s
      rw [e2] at this
      exact this.const_smul (‖y‖ ^ k))
    M
    (fun s _ => by
      set w := z + s • a
      have hyw : ‖y‖ ≤ ‖w‖ := norm_le_norm_elim_add x h y s
      have b1 := norm_iteratedFDeriv_pd_le a f1 n w
      have b2 := norm_iteratedFDeriv_pd_le a f (n + 1) w
      have hah : ‖a‖ ≤ ‖h‖ := norm_padL_le h
      have hS := SchwartzMap.le_seminorm ℂ k (n + 2) f w
      have hb : ‖iteratedFDeriv ℝ n f2 w‖ ≤ ‖h‖ ^ 2 * ‖iteratedFDeriv ℝ (n + 2) f w‖ := by
        calc ‖iteratedFDeriv ℝ n f2 w‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ (n + 1) f1 w‖ := b1
          _ ≤ ‖a‖ * (‖a‖ * ‖iteratedFDeriv ℝ (n + 1 + 1) f w‖) := by gcongr
          _ ≤ ‖h‖ * (‖h‖ * ‖iteratedFDeriv ℝ (n + 2) f w‖) := by gcongr
          _ = _ := by ring
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n f2 w‖
          ≤ ‖w‖ ^ k * (‖h‖ ^ 2 * ‖iteratedFDeriv ℝ (n + 2) f w‖) := by gcongr
        _ = ‖h‖ ^ 2 * (‖w‖ ^ k * ‖iteratedFDeriv ℝ (n + 2) f w‖) := by ring
        _ ≤ M := by rw [hM]; gcongr) 1 (by simp)
  simp only [zero_smul, add_zero, one_smul, one_pow, mul_one] at key
  rw [← smul_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)] at key
  calc ‖y‖ ^ k * ‖(iteratedFDeriv ℝ n f (z + a) - iteratedFDeriv ℝ n f z - iteratedFDeriv ℝ n f1 z).compContinuousLinearMap
          (fun _ => inrL (V := V) κ κ')‖
      ≤ ‖y‖ ^ k * ‖iteratedFDeriv ℝ n f (z + a) - iteratedFDeriv ℝ n f z - iteratedFDeriv ℝ n f1 z‖ := by
        gcongr
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        refine mul_le_of_le_one_right (norm_nonneg _) ?_
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => norm_inrL_le κ κ')
    _ ≤ M := key

end GlobalTheory.SliceTaylor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeLintegralRayIteratedFDeriv
section
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem norm_le_lintegral_ray_iteratedFDeriv
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (G : E → F) (m : ℕ) (x v : E)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hdec : ∀ j ≤ m, Tendsto (fun t : ℝ => iteratedFDeriv ℝ j G (x + t • v)) atTop (𝓝 0)) :
    ENNReal.ofReal ‖G x‖ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
      (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by
  set L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v with hL
  have hLt : ∀ t : ℝ, L t = t • v := fun t => by simp [hL]
  set Gx : E → F := fun z => G (x + z) with hGx
  have hGx' : ContDiff ℝ (⊤ : ℕ∞) Gx := hG.comp (contDiff_const.add contDiff_id)
  set h : ℝ → F := Gx ∘ L with hh
  have hhs : ContDiff ℝ (⊤ : ℕ∞) h := hGx'.comp L.contDiff
  have key : ∀ (j : ℕ) (t : ℝ),
      iteratedDeriv j h t = iteratedFDeriv ℝ j G (x + t • v) (fun _ => v) := by
    intro j t
    rw [iteratedDeriv_eq_iteratedFDeriv, hh,
      L.iteratedFDeriv_comp_right hGx' t (by exact_mod_cast le_top),
      ContinuousMultilinearMap.compContinuousLinearMap_apply, hGx,
      iteratedFDeriv_comp_add_left, hLt]
    simp [hLt]
  have bound : ∀ (j : ℕ) (t : ℝ),
      ‖iteratedDeriv j h t‖ ≤ ‖iteratedFDeriv ℝ j G (x + t • v)‖ * ‖v‖ ^ j := by
    intro j t
    rw [key]
    refine ((iteratedFDeriv ℝ j G (x + t • v)).le_opNorm _).trans (le_of_eq ?_)
    simp [Finset.prod_const]
  have hdec' : ∀ j ≤ m, Tendsto (iteratedDeriv j h) atTop (𝓝 0) := by
    intro j hj
    refine squeeze_zero_norm (fun t => bound j t) ?_
    have := ((hdec j hj).norm).mul_const (‖v‖ ^ j)
    simpa using this
  have h0 : h 0 = G x := by simp [hh, hGx, hLt]
  have main := GlobalTheory.T.norm_le_lintegral_taylor_tail_iteratedDeriv h m hhs hdec'
  rw [h0] at main
  refine main.trans (lintegral_mono_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ha : 0 ≤ t ^ m / (m.factorial : ℝ) := by
    have : (0:ℝ) < t := ht
    positivity
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul ha]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ ha)
  rw [mul_comm]
  exact bound (m + 1) t

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
section
open scoped TensorProduct
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginCut

def IsZTorsor (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) : Prop :=
  Module.Finite B D ∧ Module.Projective B D ∧ Module.FaithfullyFlat B D ∧
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)))

def originIdeal (T : Type) [CommRing T] [IsLocalRing T] : Ideal (Polynomial T) :=
  (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ⊔ Ideal.span {Polynomial.X}

end GlobalTheory.KeyOriginCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiEigenSublatticeFreeEqDifferentScaledStatement
section
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piEigenSublattice_free_eq_differentScaled : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (r : ℕ) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin r → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a r) τ = GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.flatLattice (r := r) a τ (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ) := by
  first | exact @GlobalTheory.EigenSubFree.main | exact GlobalTheory.EigenSubFree.main | (intros; apply GlobalTheory.EigenSubFree.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolUnitNeZero
section
noncomputable section

open Matrix

namespace GlobalTheory.ZarhinFam

def polUnit (d : ℕ) : ord d :=
  ⟨single (Sum.inl 0) (Sum.inr 0) 1, fun i j => by simp [single]⟩

@[simp] theorem polUnit_coe (d : ℕ) :
    ((polUnit d : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) = single (Sum.inl 0) (Sum.inr 0) 1 :=
  rfl

end GlobalTheory.ZarhinFam
end
end

