module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0283
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0257
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterSemidirectOrbitCrossTerms
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0284
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsManyBoundedByPow
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.PolesOfT

open Polynomial

variable {k F : Type} [Field k] [Field F] [Algebra k F]

abbrev Mx (t : F) (v : Place k F) : WithZero (Multiplicative ℤ) := max 1 (v.1 t)

theorem one_le_Mx (t : F) (v : Place k F) : 1 ≤ Mx t v := le_max_left _ _

theorem val_aeval_le (t : F) (p : k[X]) (v : Place k F) :
    v.1 (aeval t p) ≤ Mx t v ^ p.natDegree := by
  rw [aeval_eq_sum_range]
  refine v.1.map_sum_le fun i hi => ?_
  rw [Algebra.smul_def, map_mul, map_pow]
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hc : v.1 (algebraMap k F (p.coeff i)) ≤ 1 := by
    by_cases h : p.coeff i = 0
    · simp [h]
    · exact (v.2.2 _ h).le
  calc v.1 (algebraMap k F (p.coeff i)) * v.1 t ^ i ≤ 1 * Mx t v ^ i :=
        mul_le_mul' hc (pow_le_pow_left₀ zero_le' (le_max_right _ _) i)
    _ = Mx t v ^ i := one_mul _
    _ ≤ Mx t v ^ p.natDegree := pow_le_pow_right₀ (one_le_Mx t v) hi'

theorem val_le_of_monic (t y : F) (P : F[X]) (hP : P.Monic) (hy : P.eval y = 0) (c : ℕ)
    (v : Place k F) (hc : ∀ i < P.natDegree, v.1 (P.coeff i) ≤ Mx t v ^ c) :
    v.1 y ≤ Mx t v ^ c := by
  by_contra hlt
  push_neg at hlt
  have hM : 1 ≤ Mx t v ^ c := one_le_pow₀ (one_le_Mx t v)
  have hy1 : 1 < v.1 y := lt_of_le_of_lt hM hlt
  have hy0 : v.1 y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy1)
  rw [hP.as_sum, eval_add, eval_pow, eval_X, Polynomial.eval_finsetSum] at hy
  have heq := eq_neg_of_add_eq_zero_left hy
  have hlt2 : v.1 (∑ i ∈ Finset.range P.natDegree, (C (P.coeff i) * X ^ i).eval y) <
      v.1 y ^ P.natDegree := by
    refine v.1.map_sum_lt (pow_ne_zero _ hy0) fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [eval_mul, eval_C, eval_pow, eval_X, map_mul, map_pow]
    calc v.1 (P.coeff i) * v.1 y ^ i ≤ Mx t v ^ c * v.1 y ^ i := mul_le_mul' (hc i hi') le_rfl
      _ < v.1 y * v.1 y ^ i := mul_lt_mul_of_pos_right hlt (pow_pos (lt_trans zero_lt_one hy1) _)
      _ = v.1 y ^ (i + 1) := (pow_succ' _ _).symm
      _ ≤ v.1 y ^ P.natDegree := pow_le_pow_right₀ hy1.le hi'
  have h3 : v.1 (y ^ P.natDegree) = v.1 (∑ i ∈ Finset.range P.natDegree, (C (P.coeff i) * X ^ i).eval y) := by
    rw [heq, Valuation.map_neg]
  rw [map_pow] at h3
  rw [← h3] at hlt2
  exact lt_irrefl _ hlt2

end GlobalTheory.Nef.PolesOfT

namespace GlobalTheory.Nef.PolesOfT

open Polynomial

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem exists_mul_bdd (t y : F) (hy : IsAlgebraic k⟮t⟯ y) :
    ∃ q : k[X], aeval t q ≠ 0 ∧ ∃ c : ℕ, ∀ v : Place k F, v.1 (aeval t q * y) ≤ Mx t v ^ c := by
  classical
  obtain ⟨p, hp0, hpy⟩ := hy
  set A : Subalgebra k F := (aeval t : k[X] →ₐ[k] F).range with hA
  set P : F[X] := p.map (algebraMap k⟮t⟯ F) with hPdef
  have hP0 : P ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap k⟮t⟯ F).injective).mpr hp0
  have hPy : P.eval y = 0 := by rw [hPdef, eval_map, ← aeval_def]; exact hpy
  have hcoef : ∀ i, ∃ s : k[X], aeval t s ≠ 0 ∧ aeval t s * P.coeff i ∈ A := by
    intro i
    rw [hPdef, coeff_map]
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff k (p.coeff i : F)).mp (p.coeff i).2
    by_cases hs : aeval t s = 0
    · refine ⟨1, by simp, ?_⟩
      have : algebraMap k⟮t⟯ F (p.coeff i) = 0 := by
        change (p.coeff i : F) = 0
        rw [hrs, hs, div_zero]
      rw [this, mul_zero]; exact A.zero_mem
    · refine ⟨s, hs, ?_⟩
      change aeval t s * (p.coeff i : F) ∈ A
      rw [hrs, mul_div_cancel₀ _ hs]
      exact ⟨r, rfl⟩
  choose s hs0 hsA using hcoef
  set D : F := ∏ i ∈ Finset.range (P.natDegree + 1), aeval t (s i) with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hs0 i
  set Q : F[X] := C D * P with hQdef
  have hQA : ∀ i, Q.coeff i ∈ A := by
    intro i
    rw [hQdef, coeff_C_mul]
    by_cases hi : i ∈ Finset.range (P.natDegree + 1)
    · rw [hD, ← Finset.prod_erase_mul _ _ hi, mul_assoc]
      refine A.mul_mem (A.prod_mem fun j _ => ⟨s j, rfl⟩) (hsA i)
    · have : P.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by
        simp only [Finset.mem_range, not_lt] at hi; omega)
      rw [this, mul_zero]; exact A.zero_mem
  have hQ0 : Q ≠ 0 := mul_ne_zero (C_ne_zero.mpr hD0) hP0
  have hQy : Q.eval y = 0 := by rw [hQdef, eval_mul, hPy, mul_zero]
  set R : F[X] := integralNormalization Q with hRdef
  have hRmon : R.Monic := monic_integralNormalization hQ0
  have hRy : R.eval (Q.leadingCoeff * y) = 0 :=
    integralNormalization_eval₂_eq_zero (RingHom.id F) hQy (fun x hx => hx)
  have hRA : ∀ i, R.coeff i ∈ A := by
    intro i
    rw [hRdef, integralNormalization_coeff]
    split_ifs
    · exact A.one_mem
    · exact A.mul_mem (hQA i) (A.pow_mem (hQA _) _)
  choose pr hpr using hRA
  obtain ⟨q, hq⟩ := hQA Q.natDegree
  have hq' : aeval t q = Q.leadingCoeff := hq
  refine ⟨q, by rw [hq']; exact leadingCoeff_ne_zero.mpr hQ0,
    (Finset.range R.natDegree).sup fun i => (pr i).natDegree, fun v => ?_⟩
  rw [hq']
  refine val_le_of_monic t _ R hRmon hRy _ v fun i hi => ?_
  have h1 : R.coeff i = aeval t (pr i) := (hpr i).symm
  rw [h1]
  exact (val_aeval_le t (pr i) v).trans
    (pow_le_pow_right₀ (one_le_Mx t v) (Finset.le_sup (f := fun i => (pr i).natDegree) (Finset.mem_range.mpr hi)))

end GlobalTheory.Nef.PolesOfT

namespace GlobalTheory.Nef

open Polynomial PolesOfT

theorem exists_many_bounded_by_pow : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ t : F, Transcendental k t → ∃ c : ℕ, ∀ N : ℕ, ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ ((N : ℤ) - c) * Module.finrank k⟮t⟯ F ≤ n ∧ ∀ (i : Fin n) (v : Place k F), v.1 (f i) ≤ max 1 (v.1 t) ^ N := by
  intro k F _ _ _ _ _ _ t ht
  by_cases hfin : FiniteDimensional k⟮t⟯ F
  swap
  · refine ⟨0, fun N => ⟨0, Fin.elim0, linearIndependent_empty_type, ?_, fun i => i.elim0⟩⟩
    rw [Module.finrank_of_infinite_dimensional hfin]; simp
  set d := Module.finrank k⟮t⟯ F with hd
  let b := Module.finBasis k⟮t⟯ F
  have halg : ∀ j, IsAlgebraic k⟮t⟯ (b j) := fun j => Algebra.IsAlgebraic.isAlgebraic _
  choose q hq0 cj hcj using fun j => exists_mul_bdd t (b j) (halg j)
  refine ⟨Finset.univ.sup cj, fun N => ?_⟩
  set c := Finset.univ.sup cj with hc
  set L := N - c with hL
  let w : Fin d → k⟮t⟯ := fun j => aeval (IntermediateField.AdjoinSimple.gen k t) (q j)
  have hw : ∀ j, algebraMap k⟮t⟯ F (w j) = aeval t (q j) := fun j => by
    simp only [w]; rw [← aeval_algebraMap_apply, IntermediateField.AdjoinSimple.algebraMap_gen]
  have hw0 : ∀ j, w j ≠ 0 := fun j h => hq0 j (by rw [← hw j, h, map_zero])
  let y : Fin d → F := fun j => aeval t (q j) * b j
  have hyli : LinearIndependent k⟮t⟯ y := by
    have := b.linearIndependent.units_smul (fun j => Units.mk0 (w j) (hw0 j))
    convert this using 1
    funext j
    simp [y, Algebra.smul_def, hw]
  have hpowF : LinearIndependent k (fun n : ℕ => t ^ n) := by
    have h1 := (Polynomial.basisMonomials k).linearIndependent.map' (aeval t).toLinearMap
      (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp ht))
    have heq : (fun n : ℕ => t ^ n) = (aeval t).toLinearMap ∘ Polynomial.basisMonomials k := by
      funext n
      simp [Polynomial.coe_basisMonomials]
    rw [heq]
    exact h1
  have hpow : LinearIndependent k (fun i : Fin L => (IntermediateField.AdjoinSimple.gen k t) ^ (i : ℕ)) := by
    have heq : (IsScalarTower.toAlgHom k k⟮t⟯ F).toLinearMap ∘
        (fun i : Fin L => (IntermediateField.AdjoinSimple.gen k t) ^ (i : ℕ)) =
        (fun n : ℕ => t ^ n) ∘ (fun i : Fin L => (i : ℕ)) := by
      funext i
      simp
    apply LinearIndependent.of_comp (IsScalarTower.toAlgHom k k⟮t⟯ F).toLinearMap
    rw [heq]
    exact hpowF.comp _ Fin.val_injective
  have hprod := linearIndependent_smul hpow hyli
  refine ⟨L * d, fun i => (fun p : Fin L × Fin d => (IntermediateField.AdjoinSimple.gen k t) ^ (p.1 : ℕ) • y p.2)
    (finProdFinEquiv.symm i), hprod.comp _ finProdFinEquiv.symm.injective, ?_, ?_⟩
  · push_cast
    have h1 : ((N : ℤ) - c) ≤ (L : ℤ) := by omega
    exact mul_le_mul_of_nonneg_right h1 (Int.natCast_nonneg _)
  · intro i v
    dsimp only
    generalize finProdFinEquiv.symm i = p
    obtain ⟨a, j⟩ := p
    have hsm : (IntermediateField.AdjoinSimple.gen k t) ^ (a : ℕ) • y j = t ^ (a : ℕ) * (aeval t (q j) * b j) := by
      rw [Algebra.smul_def, map_pow, IntermediateField.AdjoinSimple.algebraMap_gen]
    dsimp only
    rw [hsm, map_mul, map_pow]
    have ha : (a : ℕ) + c ≤ N := by have := a.2; omega
    calc v.1 t ^ (a : ℕ) * v.1 (aeval t (q j) * b j) ≤ Mx t v ^ (a : ℕ) * Mx t v ^ c :=
          mul_le_mul' (pow_le_pow_left₀ zero_le' (le_max_right _ _) _)
            ((hcj j v).trans (pow_le_pow_right₀ (one_le_Mx t v) (Finset.le_sup (Finset.mem_univ j))))
      _ = Mx t v ^ ((a : ℕ) + c) := (pow_add _ _ _).symm
      _ ≤ max 1 (v.1 t) ^ N := pow_le_pow_right₀ (one_le_Mx t v) ha

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqZeroOfSmulEqZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.ZModFlat

open scoped TensorProduct

theorem exists_mul_eq_zero_of_smul_eq_zero (q : ℕ) [NeZero q] (M : Type 1) [AddCommGroup M]
    [Module (ULift.{1} (ZMod q)) M]
    (hdiv : ∀ d e : ℕ, d * e = q → ∀ x : M, d • x = 0 → ∃ y : M, x = e • y)
    (a : ULift.{1} (ZMod q)) (y : M) (hy : a • y = 0) :
    ∃ e : ℕ, (e : ULift.{1} (ZMod q)) * a = 0 ∧ ∃ z : M, y = e • z := by
  set n := a.down.val with hn
  have ha : a = (n : ULift.{1} (ZMod q)) := by
    apply ULift.down_injective
    rw [ULift.down_natCast, hn, ZMod.natCast_zmod_val]
  have hq : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    ext; simp
  have hgq : Nat.gcd n q ∣ q := Nat.gcd_dvd_right n q
  have hgn : Nat.gcd n q ∣ n := Nat.gcd_dvd_left n q
  refine ⟨q / Nat.gcd n q, ?_, ?_⟩
  · rw [ha, ← Nat.cast_mul]
    have : q ∣ q / Nat.gcd n q * n := by
      have h := Nat.mul_dvd_mul (dvd_refl (q / Nat.gcd n q)) hgn
      rwa [Nat.div_mul_cancel hgq] at h
    obtain ⟨m, hm⟩ := this
    rw [hm, Nat.cast_mul, hq, zero_mul]
  · apply hdiv (Nat.gcd n q) (q / Nat.gcd n q) (Nat.mul_div_cancel' hgq)
    have h1 : n • y = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), ← ha, hy]
    have h2 : q • y = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), hq, zero_smul]
    have hb : ((Nat.gcd n q : ℕ) : ℤ) = n * Nat.gcdA n q + q * Nat.gcdB n q :=
      Nat.gcd_eq_gcd_ab n q
    have h3 : ((n : ℤ) * Nat.gcdA n q) • y = 0 := by
      rw [mul_comm, mul_smul, natCast_zsmul, h1, smul_zero]
    have h4 : ((q : ℤ) * Nat.gcdB n q) • y = 0 := by
      rw [mul_comm, mul_smul, natCast_zsmul, h2, smul_zero]
    rw [← natCast_zsmul, hb, add_smul, h3, h4, add_zero]

theorem flat_of_divisibility : ∀ (q : ℕ) [NeZero q] (M : Type 1) [AddCommGroup M]
    [Module (ULift.{1} (ZMod q)) M],
    (∀ d e : ℕ, d * e = q → ∀ x : M, d • x = 0 → ∃ y : M, x = e • y) →
      Module.Flat (ULift.{1} (ZMod q)) M := by
  intro q _ M _ _ hdiv
  haveI : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
    IsPrincipalIdealRing.of_surjective
      ((ULift.ringEquiv (R := ZMod q)).symm.toRingHom.comp (Int.castRingHom (ZMod q)))
      (by
        intro x
        obtain ⟨z, hz⟩ := ZMod.intCast_surjective x.down
        exact ⟨z, by apply ULift.down_injective; simpa using hz⟩)
  rw [Module.Flat.iff_rTensor_injective']
  intro J
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal J).principal
  let b : J := ⟨a, by rw [ha]; exact Submodule.mem_span_singleton_self a⟩
  have hall : ∀ t : J ⊗[ULift.{1} (ZMod q)] M, ∃ y : M, t = b ⊗ₜ y := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul r x =>
      have hr : (r : ULift.{1} (ZMod q)) ∈ Submodule.span (ULift.{1} (ZMod q)) {a} := ha ▸ r.2
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hr
      refine ⟨c • x, ?_⟩
      rw [← TensorProduct.smul_tmul]
      congr 1
      ext
      simp [b, ← hc]
    | add s t hs ht =>
      obtain ⟨y1, rfl⟩ := hs
      obtain ⟨y2, rfl⟩ := ht
      exact ⟨y1 + y2, (TensorProduct.tmul_add _ _ _).symm⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨y, rfl⟩ := hall t
  have hy : a • y = 0 := by
    have := congrArg (TensorProduct.lid (ULift.{1} (ZMod q)) M) ht
    simpa [b] using this
  obtain ⟨e, he, z, rfl⟩ := exists_mul_eq_zero_of_smul_eq_zero q M hdiv a y hy
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), ← TensorProduct.smul_tmul]
  have : ((e : ULift.{1} (ZMod q))) • b = 0 := by
    ext
    simp [b, he]
  rw [this, TensorProduct.zero_tmul]

end GlobalTheory.ZModFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroLinearCombinationMemCommonKernel
section
open GlobalTheory.Nef

namespace GlobalTheory

theorem exists_ne_zero_comb_mem_ker :
    ∀ (k F ι : Type) [Field k] [Field F] [Algebra k F] (n m : ℕ) (f : Fin m → F),
  LinearIndependent k f → ∀ (S : Finset ι) (N : ι → ℕ) (ψ : ∀ v, (Fin n → F) →ₗ[k] (Fin (N v) → k)),
    ∑ v ∈ S, N v < n * m → ∃ c : Fin n → Fin m → k, (fun i => ∑ j, c i j • f j) ≠ 0 ∧
      ∀ v ∈ S, ψ v (fun i => ∑ j, c i j • f j) = 0 := by
  intro k F ι _ _ _ n m f hf S N ψ hlt
  let T : (Fin n → Fin m → k) →ₗ[k] (Fin n → F) :=
    { toFun := fun c i => ∑ j, c i j • f j
      map_add' := by
        intro a b; funext i; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a; funext i; simp [Finset.smul_sum, smul_smul] }
  have hT : ∀ c, T c = fun i => ∑ j, c i j • f j := fun c => rfl
  let Ψ : (Fin n → Fin m → k) →ₗ[k] ((v : S) → Fin (N v) → k) :=
    LinearMap.pi fun v => (ψ v).comp T
  have hlt' : Module.finrank k ((v : S) → Fin (N v) → k) < Module.finrank k (Fin n → Fin m → k) := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_fin_fun]
    rw [Finset.sum_coe_sort S (fun v => N v), Module.finrank_pi_fintype]
    simpa [Module.finrank_fin_fun] using hlt
  have hk : LinearMap.ker Ψ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hlt'
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hk
  refine ⟨c, ?_, ?_⟩
  · intro h0
    apply hc0
    funext i j
    have hi : ∑ j, c i j • f j = 0 := congrFun h0 i
    exact Fintype.linearIndependent_iff.1 hf (c i) hi j
  · intro v hv
    have := congrFun (LinearMap.mem_ker.1 hc) ⟨v, hv⟩
    simpa [Ψ, hT] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupPeriodicStatement
section
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openSubgroup_periodic : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {ι : Type} (L : ι → AddSubgroup X), (∀ i, IsOpen (L i : Set X)) → (∀ W ∈ 𝓝 (0 : X), ∃ i, (L i : Set X) ⊆ W) → ∀ f ∈ GlobalTheory.WeilM.SB X, ∃ i, ∀ Y, ∀ C ∈ L i, f (Y + C) = f Y := by
  first | exact @GlobalTheory.WeilM.SB.exists_periodic | exact GlobalTheory.WeilM.SB.exists_periodic | (intros; apply GlobalTheory.WeilM.SB.exists_periodic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointAlgClosureResidueFieldOfIntegralSurje
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem exists_ringHom_algClosure_residueField_of_isIntegral (A B : Type) [CommRing A]
    [IsLocalRing A] [CommRing B] (φ : A →+* B) (hφ : φ.IsIntegral) (P : Ideal B) [P.IsPrime]
    (hP : P.comap φ = IsLocalRing.maximalIdeal A) :
    ∃ ψ : B →+* AlgebraicClosure (IsLocalRing.ResidueField A),
      ψ.comp φ = algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)) := by
  letI : Algebra A B := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hφ⟩
  haveI : P.LiesOver (IsLocalRing.maximalIdeal A) := ⟨hP.symm⟩
  letI : Algebra (IsLocalRing.ResidueField A) (B ⧸ P) :=
    Ideal.Quotient.algebraOfLiesOver P (IsLocalRing.maximalIdeal A)
  haveI : IsScalarTower A (IsLocalRing.ResidueField A) (B ⧸ P) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral A (B ⧸ P) := inferInstance
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField A) (B ⧸ P) :=
    Algebra.IsIntegral.tower_top (R := A)
  let l : (B ⧸ P) →ₐ[IsLocalRing.ResidueField A] AlgebraicClosure (IsLocalRing.ResidueField A) :=
    IsAlgClosed.lift
  refine ⟨l.toRingHom.comp (Ideal.Quotient.mk P), ?_⟩
  ext a
  have h := l.commutes (algebraMap A (IsLocalRing.ResidueField A) a)
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
  exact h

theorem exists_point_algClosure_residueField_of_isIntegralHom :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)),
    IsIntegralHom g → Surjective g → ∃ s : Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField A))) ⟶ Y,
    s ≫ g = Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)))) := by
  intro A _ _ Y g hi hs
  haveI : IsAffine Y := isAffine_of_isAffineHom g
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ g)
  have h1 : IsIntegralHom (Spec.map φ) := by rw [hφ]; infer_instance
  have h2 : Surjective (Spec.map φ) := by rw [hφ]; infer_instance
  have h3 : φ.hom.IsIntegral := IsIntegralHom.SpecMap_iff.mp h1
  obtain ⟨P, hP⟩ := h2.surj (IsLocalRing.closedPoint A)
  have hP' : (PrimeSpectrum.asIdeal P).comap φ.hom = IsLocalRing.maximalIdeal A :=
    congrArg PrimeSpectrum.asIdeal hP
  haveI := PrimeSpectrum.isPrime P
  obtain ⟨ψ, hψ⟩ := exists_ringHom_algClosure_residueField_of_isIntegral A Γ(Y, ⊤) φ.hom h3
    (PrimeSpectrum.asIdeal P) hP'
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ Y.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp, ← hψ]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreservesFilteredColimitsIsoOnFiniteTypeStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_preservesFilteredColimits_iso_on_finiteType : ∀ (𝒜 : Type 2) [Category.{1} 𝒜] [HasColimitsOfSize.{1, 1} 𝒜] (M : CommRingCat.{0} ⥤ 𝒜), ∃ (N : CommRingCat.{0} ⥤ 𝒜) (ε : N ⟶ M), PreservesFilteredColimitsOfSize.{0, 0} N ∧ ∀ A : CommRingCat.{0}, Algebra.FiniteType ℤ A → IsIso (ε.app A) := by
  first
  | exact @GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso
  | exact GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso
  | (intros; apply GlobalTheory.FinExt.exists_preservesFilteredColimits_isIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterSemidirectOrbitCrossTermsStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_virtualCharacter_semidirect_orbit_cross_terms : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ a b : G → ℂ, a ∈ Virt ℂ ℂ G → b ∈ Virt ℂ ℂ G → ∃ Z ∈ Virt ℂ ℂ (G ⋊[φ] Γ), (∀ g, Z (inl g) = ∏ t : Γ, (a (φ t g) + b (φ t g)) - ∏ t : Γ, a (φ t g) - ∏ t : Γ, b (φ t g)) ∧ ∀ δ, Z (inl δ * inr s) = 0 := by
  first | (exact @GlobalTheory.CrossOrbit.cross_terms_induced) | (exact GlobalTheory.CrossOrbit.cross_terms_induced) | (intros; apply GlobalTheory.CrossOrbit.cross_terms_induced <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterTwistedHarishChandraInductStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_virtualCharacter_twistedHarishChandraInductionGL : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (a b n : ℕ), n = a + b → ∀ X ∈ Virt ℂ ℂ (GHat F F' a), ∃ Z ∈ Virt ℂ ℂ (GHat F F' n), ∀ (t : F' ≃ₐ[F] F') (δ : GL (Fin n) F'), Z (inl δ * inr t) = hcTw (t : F' →+* F') a b (fun d => X (inl d * inr t)) (fun _ => 1) n δ := by
  first | (exact @GlobalTheory.Shin.HatInd.hat_ind) | (exact GlobalTheory.Shin.HatInd.hat_ind) | (intros; apply GlobalTheory.Shin.HatInd.hat_ind <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteLengthCokerOfEtalePuncturedSpectrumStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteLength_coker_of_etale_punctured_spectrum : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] (A B : Type) [CommRing A] [Algebra R A] [Module.Finite R A] [CommRing B] [Algebra R B] [Module.Finite R B], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) B)) → ∀ ψ : A →ₐ[R] B, Function.Injective ψ → (∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range) → ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ ψ.range := by
  first | (exact @GlobalTheory.EtaleCoker.main) | (exact GlobalTheory.EtaleCoker.main) | (intros; apply GlobalTheory.EtaleCoker.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeFieldStrictlyHenselian
section
open GlobalTheory.EtC

namespace GlobalTheory

theorem field_finiteType_algClosed_SH : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B], IsField B → SH B := by
  intro k B _ _ _ _ _ hB
  letI : Field B := hB.toField
  haveI : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
  have hbk : Function.Bijective (algebraMap k B) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsAlgClosed B := IsAlgClosed.of_ringEquiv k B
    (RingEquiv.ofBijective (algebraMap k B) hbk)
  refine ⟨Field.henselian B, ?_⟩
  have hbij : Function.Bijective (IsLocalRing.residue B) :=
    ⟨(IsLocalRing.residue B).injective, Ideal.Quotient.mk_surjective⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField B) :=
    IsAlgClosed.of_ringEquiv B _ (RingEquiv.ofBijective _ hbij)
  exact IsSepClosed.of_isAlgClosed _

end GlobalTheory
end

