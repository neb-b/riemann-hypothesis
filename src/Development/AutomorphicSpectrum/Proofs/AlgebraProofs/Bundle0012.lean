module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0007
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussSumValuationTeichmuller
section
open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem val_one_sub_pow_le {K : Type} [Field K] (v : Valuation K NNReal) {x : K} (hx : v x = 1)
    (i : ℕ) : v (1 - x ^ i) ≤ v (1 - x) := by
  have h : 1 - x ^ i = (1 - x) * ∑ j ∈ Finset.range i, x ^ j := (mul_neg_geom_sum x i).symm
  rw [h, map_mul]
  refine mul_le_of_le_one_right' ?_
  exact v.map_sum_le (fun j _ => by rw [map_pow, hx, one_pow])

theorem val_eq_one_of_pow_eq_one {K : Type} [Field K] (v : Valuation K NNReal) {x : K} {n : ℕ}
    (hn : n ≠ 0) (hx : x ^ n = 1) : v x = 1 := by
  have h : v x ^ n = 1 := by rw [← map_pow, hx, map_one]
  exact (pow_left_inj₀ zero_le zero_le_one hn).mp (by simpa using h)

theorem val_sub_one_pow {K : Type} [Field K] (v : Valuation K NNReal) (p : ℕ) [Fact p.Prime]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) : v (ζ - 1) ^ (p - 1) = v (p : K) := by
  have hp : p.Prime := Fact.out
  have hprod : (p : K) = ∏ μ ∈ primitiveRoots p K, (1 - μ) := by
    rw [← Polynomial.eval_one_cyclotomic_prime (R := K) (p := p),
      Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod]
    simp
  have hval : ∀ μ ∈ primitiveRoots p K, v (1 - μ) = v (1 - ζ) := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ p := (mem_primitiveRoots hp.pos).mp hμ
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    obtain ⟨j, -, hj⟩ := hμ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
    refine le_antisymm (val_one_sub_pow_le v (val_eq_one_of_pow_eq_one v hp.ne_zero
      hζ.pow_eq_one) i) ?_
    conv_lhs => rw [← hj]
    exact val_one_sub_pow_le v (val_eq_one_of_pow_eq_one v hp.ne_zero hμ'.pow_eq_one) j
  rw [hprod, map_prod, Finset.prod_congr rfl hval, Finset.prod_const, hζ.card_primitiveRoots,
    Nat.totient_prime hp, Valuation.map_sub_swap]

theorem exists_mulShift_eq {F K : Type} [Field F] [Fintype F] [Field K] (ψ₀ ψ : AddChar F K)
    (h₀ : ψ₀ ≠ 1) : ∃ c, ψ = AddChar.mulShift ψ₀ c :=
  _root_.UpperTheory.Reformulated.B.Yde4.main ψ₀ ψ h₀

def ltOneIdeal {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) : Ideal R where
  carrier := {r | v (algebraMap R C r) < 1}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add (f := _)] at *
    exact v.map_add_lt ha hb
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one c)) hx

theorem mem_ltOneIdeal {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) (r : R) :
    r ∈ ltOneIdeal v R hv ↔ v (algebraMap R C r) < 1 := Iff.rfl

theorem ltOneIdeal_isPrime {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) : (ltOneIdeal v R hv).IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · have h1 : (1 : R) ∈ ltOneIdeal v R hv := h ▸ Submodule.mem_top
    rw [mem_ltOneIdeal] at h1
    simp at h1
  · rw [mem_ltOneIdeal, map_mul, map_mul] at hab
    by_contra hcon
    push Not at hcon
    simp only [mem_ltOneIdeal, not_lt] at hcon
    have ha : v (algebraMap R C a) = 1 := le_antisymm (hv.map_le_one a) hcon.1
    have hb : v (algebraMap R C b) = 1 := le_antisymm (hv.map_le_one b) hcon.2
    simp [ha, hb] at hab

theorem gauss_value : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → Fintype.card F ≠ 2 → ∀ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) → ∀ ψ : AddChar F C, ψ ≠ 1 → v (∑ a, algebraMap R C (σ⁻¹ a) * ψ a) ^ (p - 1) = v (p : C) := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hcard hF σ hσ ψ hψ
  have hpp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)
  haveI hprime : (ltOneIdeal v R hv).IsPrime := ltOneIdeal_isPrime v R hv

  have hpm : (p : R) ∈ ltOneIdeal v R hv := by
    rw [mem_ltOneIdeal, map_natCast]; exact hp
  have hspan : Ideal.span {(p : R)} ≤ ltOneIdeal v R hv :=
    (Ideal.span_singleton_le_iff_mem _).mpr hpm
  let ι : F →+* R ⧸ ltOneIdeal v R hv :=
    { toFun := fun a => Ideal.Quotient.mk _ (σ a)
      map_one' := by simp
      map_mul' := fun a b => by simp
      map_zero' := by simp [MulChar.map_zero]
      map_add' := fun a b => by
        rw [← map_add (f := _), Ideal.Quotient.eq]
        have := hspan (hσ a b)
        rwa [sub_sub] at this }

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  have hvζ : v ζ = 1 := val_eq_one_of_pow_eq_one v hpp.ne_zero hζ.pow_eq_one
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hvζ.le
  have hzp : z ^ p = 1 := hv.hom_inj (by rw [map_pow, hζ.pow_eq_one, map_one])
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  obtain ⟨y, hym, hy⟩ := ReciprocityTheory.PGsh.gaussCongruence p F R (ltOneIdeal v R hv) ι σ z hF hzp
    (fun a => rfl)

  let ψ₀ : AddChar F C := (AddChar.zmodChar p hζ.pow_eq_one).compAddMonoidHom
    (Algebra.trace (ZMod p) F).toAddMonoidHom
  have hψ₀ : ∀ a, ψ₀ a = algebraMap R C z ^ (Algebra.trace (ZMod p) F a).val := fun a => rfl
  have hψ₀1 : ψ₀ ≠ 1 := by
    haveI : Module.Finite (ZMod p) F := Module.Finite.of_finite
    obtain ⟨b, hb⟩ := Algebra.trace_surjective (ZMod p) F 1
    intro h
    have h1 : ψ₀ b = 1 := by rw [h]; simp
    rw [hψ₀] at h1
    have hb0 : (Algebra.trace (ZMod p) F b).val ≠ 0 := by
      rw [hb, Ne, ZMod.val_eq_zero]
      exact one_ne_zero
    exact hζ.pow_ne_one_of_pos_of_lt hb0 (ZMod.val_lt _) h1
  obtain ⟨c, rfl⟩ := exists_mulShift_eq ψ₀ ψ hψ₀1
  have hc : c ≠ 0 := by
    rintro rfl
    exact hψ (AddChar.mulShift_zero _)
  have hσc : σ c * σ⁻¹ c = 1 := by
    rw [MulChar.inv_apply', ← map_mul, mul_inv_cancel₀ hc, map_one]
  have hsum : ∑ a, algebraMap R C (σ⁻¹ a) * AddChar.mulShift ψ₀ c a =
      algebraMap R C (σ c) * ∑ b, algebraMap R C (σ⁻¹ b) * ψ₀ b := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft₀ c hc) _ _ (fun a => ?_)
    simp only [Equiv.mulLeft₀_apply, AddChar.mulShift_apply, map_mul, ← mul_assoc]
    rw [← map_mul, hσc, map_one, one_mul]
  have hvσ : v (algebraMap R C (σ c)) = 1 := by
    have h1 : v (algebraMap R C (σ c)) * v (algebraMap R C (σ⁻¹ c)) = 1 := by
      rw [← map_mul, ← map_mul, hσc, map_one, map_one]
    refine le_antisymm (hv.map_le_one _) ?_
    calc (1 : NNReal) = v (algebraMap R C (σ c)) * v (algebraMap R C (σ⁻¹ c)) := h1.symm
      _ ≤ v (algebraMap R C (σ c)) := mul_le_of_le_one_right' (hv.map_le_one _)
  have hG : ∑ b, algebraMap R C (σ⁻¹ b) * ψ₀ b =
      (algebraMap R C z - 1) * (algebraMap R C y - 1) := by
    have := congrArg (algebraMap R C) hy
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, map_sub, map_one] at this
    rw [← this]
    exact Finset.sum_congr rfl fun a _ => by rw [hψ₀]
  have hvy : v (algebraMap R C y - 1) = 1 := by
    have h : v (algebraMap R C y) < v (1 : C) := by
      rw [map_one]; exact hym
    rw [Valuation.map_sub_swap, Valuation.map_sub_eq_of_lt_left v h, map_one]
  rw [hsum, hG, map_mul, map_mul, hvσ, hvy, one_mul, mul_one]
  exact val_sub_one_pow v p hζ

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocFreeMapMkQIff
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem locFree_map_equiv (R : Subalgebra o Ω) {E E' : Type} [AddCommGroup E] [Module Ω E]
    [AddCommGroup E'] [Module Ω E'] (e : E ≃ₗ[Ω] E') {r : ℕ} {L : AddSubgroup E}
    (h : LocFree R r L) : LocFree R r (L.map e.toLinearMap.toAddMonoidHom) := by
  obtain ⟨hst, k, f, c, hf, hc, hs, hl⟩ := h
  refine ⟨?_, k, f, c, hf, hc, hs, fun l => ?_⟩
  · rintro a ha _ ⟨x, hx, rfl⟩
    exact ⟨a • x, hst a ha x hx, by simp⟩
  · obtain ⟨b, hb, hsp, hiff⟩ := hl l
    refine ⟨fun q => e (b q), hb.map' e.toLinearMap (LinearEquiv.ker e), ?_, fun v => ?_⟩
    · have : Set.range (fun q => e (b q)) = e.toLinearMap '' Set.range b := by
        rw [← Set.range_comp]; rfl
      rw [this, ← Submodule.map_span, hsp, Submodule.map_top, LinearMap.range_eq_top]
      exact e.surjective
    · have key : ∀ n : ℕ, f l ^ n • v ∈ L.map e.toLinearMap.toAddMonoidHom ↔
          f l ^ n • e.symm v ∈ L := by
        intro n
        constructor
        · rintro ⟨x, hx, hxe⟩
          have : x = f l ^ n • e.symm v := by
            apply e.injective
            rw [map_smul, e.apply_symm_apply]
            exact hxe
          rwa [← this]
        · intro hx
          exact ⟨_, hx, by simp⟩
      simp only [key]
      rw [hiff (e.symm v)]
      constructor
      · rintro ⟨a, ha, hv⟩
        refine ⟨a, ha, ?_⟩
        have := congrArg e hv
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [map_sum] using this
      · rintro ⟨a, ha, hv⟩
        refine ⟨a, ha, ?_⟩
        rw [hv]
        set_option synthInstance.maxHeartbeats 100000 in
          simp [map_sum]

theorem mem_stdLat (R : Subalgebra o Ω) {ι : Type} {v : ι → Ω} :
    v ∈ stdLat R ι ↔ ∀ j, v j ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem locFree_stdLat (R : Subalgebra o Ω) (m : ℕ) : LocFree R m (stdLat R (Fin m)) := by
  classical
  refine ⟨fun a ha e he => ?_, 1, fun _ => 1, fun _ => 1, fun _ => R.one_mem, fun _ => R.one_mem,
    by simp, fun _ => ?_⟩
  · rw [mem_stdLat] at he ⊢
    intro j
    simpa using R.mul_mem ha (he j)
  · refine ⟨fun q => (Pi.basisFun Ω (Fin m)) q, (Pi.basisFun Ω (Fin m)).linearIndependent,
      (Pi.basisFun Ω (Fin m)).span_eq, fun e => ?_⟩
    have hsum : ∀ a : Fin m → Ω, (∑ q, a q • (Pi.basisFun Ω (Fin m)) q) = a := by
      intro a
      simpa using (Pi.basisFun Ω (Fin m)).sum_repr a
    constructor
    · rintro ⟨_, hn⟩
      simp only [one_pow, one_smul] at hn
      exact ⟨e, fun q => ⟨0, by simpa using (mem_stdLat R).1 hn q⟩, (hsum e).symm⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨0, ?_⟩
      rw [hsum, pow_zero, one_smul, mem_stdLat]
      intro q
      obtain ⟨n, hn⟩ := ha q
      simpa using hn

theorem locFree_divLat (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] {c : Ω}
    (hc : c ≠ 0) {r : ℕ} {L : AddSubgroup E} (h : LocFree R r L) : LocFree R r (divLat c L) := by
  have := locFree_map_equiv R (LinearEquiv.smulOfNeZero Ω E c⁻¹ (inv_ne_zero hc)) h
  convert this using 1
  ext v
  constructor
  · intro hv
    exact ⟨c • v, hv, by simp [smul_smul, hc]⟩
  · rintro ⟨x, hx, rfl⟩
    show c • (c⁻¹ • x) ∈ L
    simpa [smul_smul, hc] using hx

theorem locFree_map_mkQ_iff (R : Subalgebra o Ω) {E E₂ : Type} [AddCommGroup E] [Module Ω E]
    [AddCommGroup E₂] [Module Ω E₂] (q : E →ₗ[Ω] E₂) (hq : Function.Surjective q) {r : ℕ}
    (L : AddSubgroup E) :
    LocFree R r (L.map (LinearMap.ker q).mkQ.toAddMonoidHom) ↔ LocFree R r (L.map q.toAddMonoidHom) := by
  let e := q.quotKerEquivOfSurjective hq
  have h1 : (L.map (LinearMap.ker q).mkQ.toAddMonoidHom).map e.toLinearMap.toAddMonoidHom =
      L.map q.toAddMonoidHom := by
    rw [AddSubgroup.map_map]
    congr 1
  constructor
  · intro h
    rw [← h1]
    exact locFree_map_equiv R e h
  · intro h
    have h2 : (L.map q.toAddMonoidHom).map e.symm.toLinearMap.toAddMonoidHom =
        L.map (LinearMap.ker q).mkQ.toAddMonoidHom := by
      rw [← h1, AddSubgroup.map_map]
      ext v
      simp
    rw [← h2]
    exact locFree_map_equiv R e.symm h

theorem isBaseChange_bcMap (Ω C : Type) [Field Ω] [Field C] [Algebra Ω C] (ι : Type) [Finite ι] :
    IsBaseChange C (bcMap Ω C ι) := by
  have := Fintype.ofFinite ι
  have h := IsBaseChange.pi (S := C) (fun _ : ι => Algebra.linearMap Ω C)
    (fun _ => IsBaseChange.linearMap Ω C)
  exact h

theorem span_bcMap_annSub (Ω C : Type) [Field Ω] [Field C] [Algebra Ω C] (n i : ℕ) :
    Submodule.span C (bcMap Ω C (Fin n) '' (annSub Ω n i : Set (Fin n → Ω))) = annSub C n i := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    simp only [annSub, SetLike.mem_coe, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot] at hv ⊢
    intro j hj
    simp [bcMap, hv j hj]
  · intro v hv
    simp only [annSub, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot] at hv
    have : v = ∑ j, v j • bcMap Ω C (Fin n) (if (j : ℕ) < i then 0 else Pi.single j 1) := by
      ext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single k]
      · by_cases hk : (k : ℕ) < i
        · simp [hk, hv k hk, bcMap]
        · simp [hk, bcMap]
      · intro j _ hjk
        by_cases hj : (j : ℕ) < i
        · simp [hj, bcMap]
        · simp [hj, bcMap, Pi.single_apply, hjk.symm]
      · simp
    rw [this]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
    simp only [annSub, SetLike.mem_coe, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot]
    intro k hk
    by_cases hj : (j : ℕ) < i
    · simp [hj]
    · have : k ≠ j := by rintro rfl; exact hj hk
      simp [hj, Pi.single_apply, this]

theorem spanOver_swap {C V Z Vc Zc : Type} [Field C] [Algebra o C] (RC : Subalgebra o C)
    [AddCommGroup V] [AddCommGroup Z] [AddCommGroup Vc] [AddCommGroup Zc]
    [Module C Vc] [Module C Zc] (b : V → Vc) (b' : Z → Zc) (Γ : AddSubgroup (Z × V)) :
    spanOver RC (Prod.map b b' '' (Γ.map (AddEquiv.prodComm (M := Z) (N := V)).toAddMonoidHom : AddSubgroup (V × Z))) =
      (spanOver RC (Prod.map b' b '' Γ)).map (AddEquiv.prodComm (M := Zc) (N := Vc)).toAddMonoidHom := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, _, ⟨_, ⟨⟨z, v⟩, hzv, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a • (b' z, b v), ⟨a, ha, _, ⟨(z, v), hzv, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, ha, _, ⟨⟨z, v⟩, hzv, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, _, ⟨_, ⟨(z, v), hzv, rfl⟩, rfl⟩, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeOfShortExact
section
open GlobalTheory.CompanionTheory.Ar.Num TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel

theorem isBaseChange_of_split {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M₁ M M₂ E₁ E E₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M] [Module R M]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup E₁] [Module R E₁] [Module S E₁]
    [IsScalarTower R S E₁] [AddCommGroup E] [Module R E] [Module S E] [IsScalarTower R S E]
    [AddCommGroup E₂] [Module R E₂] [Module S E₂] [IsScalarTower R S E₂]
    (j : M₁ →ₗ[R] M) (p : M →ₗ[R] M₁) (π : M →ₗ[R] M₂) (s : M₂ →ₗ[R] M)
    (hpj : p ∘ₗ j = LinearMap.id) (hsum : j ∘ₗ p + s ∘ₗ π = LinearMap.id)
    (f₁ : M₁ →ₗ[R] E₁) (f : M →ₗ[R] E) (f₂ : M₂ →ₗ[R] E₂)
    (i : E₁ →ₗ[S] E) (q : E →ₗ[S] E₂) (hi : Function.Injective i) (hqi : ∀ x, q (i x) = 0)
    (h₁ : ∀ x, i (f₁ x) = f (j x)) (h₂ : ∀ x, q (f x) = f₂ (π x))
    (hf : IsBaseChange S f) (hf₂ : IsBaseChange S f₂) : IsBaseChange S f₁ := by
  let φ : S ⊗[R] M₁ →ₗ[S] E₁ := LinearMap.liftBaseChange S f₁
  have c₁ : ∀ t, i (φ t) = hf.equiv (j.baseChange S t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [φ, IsBaseChange.equiv_tmul, h₁]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have c₂ : ∀ t, q (hf.equiv t) = hf₂.equiv (π.baseChange S t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [IsBaseChange.equiv_tmul, h₂]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have c₃ : ∀ t, p.baseChange S (j.baseChange S t) = t := by
    intro t
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hpj, LinearMap.baseChange_id]
    rfl
  have c₄ : ∀ t, j.baseChange S (p.baseChange S t) + s.baseChange S (π.baseChange S t) = t := by
    intro t
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_comp, ← LinearMap.add_apply, ← LinearMap.baseChange_add, hsum,
      LinearMap.baseChange_id]
    rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    have : j.baseChange S a = j.baseChange S b := by
      apply hf.equiv.injective
      rw [← c₁, ← c₁, hab]
    rw [← c₃ a, this, c₃]
  have hsurj : Function.Surjective φ := by
    intro e
    obtain ⟨t, ht⟩ := hf.equiv.surjective (i e)
    have h0 : π.baseChange S t = 0 := by
      apply hf₂.equiv.injective
      rw [← c₂, ht, hqi, map_zero]
    refine ⟨p.baseChange S t, hi ?_⟩
    have := c₄ t
    rw [h0, map_zero, add_zero] at this
    rw [c₁, this, ht]
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩) (by
    intro x
    show φ (1 ⊗ₜ[R] x) = f₁ x
    rw [LinearMap.liftBaseChange_tmul, one_smul])

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₁ E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] [AddCommGroup E₂] [Module Ω E₂] (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂), Function.Injective i → Function.Surjective q → LinearMap.range i = LinearMap.ker q → ∀ (L : AddSubgroup E) (r₁ r₂ : ℕ), LocFree R (r₁ + r₂) L → LocFree R r₂ (L.map q.toAddMonoidHom) → LocFree R r₁ (L.comap i.toAddMonoidHom) := by
  intro o Ω _ _ _ R E E₁ E₂ _ _ _ _ _ _ i q hi hq hex L r₁ r₂ hL hL₂
  let M : Submodule R E :=
    { L with smul_mem' := fun a e he => hL.1 a a.2 e he }
  let M₁ : Submodule R E₁ := M.comap (i.restrictScalars R)
  let M₂ : Submodule R E₂ := M.map (q.restrictScalars R)
  obtain ⟨hfin, hproj, hrk, hbc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main R (r₁ + r₂) M hL
  obtain ⟨hfin₂, hproj₂, hrk₂, hbc₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main R r₂ M₂ hL₂
  have hqi : ∀ x, q (i x) = 0 := fun x => by
    rw [← LinearMap.mem_ker, ← hex]; exact LinearMap.mem_range_self i x
  let j : M₁ →ₗ[R] M := (i.restrictScalars R).restrict (fun x hx => hx)
  let π : M →ₗ[R] M₂ := (q.restrictScalars R).restrict (fun x hx => ⟨x, hx, rfl⟩)
  have hπ : Function.Surjective π := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hj : Function.Injective j := by
    intro a b hab
    exact Subtype.ext (hi (congrArg Subtype.val hab))
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hmem : ∀ x : M, (LinearMap.id - s ∘ₗ π : M →ₗ[R] M) x ∈ LinearMap.range j := by
    intro x
    have h0 : π (x - s (π x)) = 0 := by
      have := LinearMap.congr_fun hs (π x)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
      rw [map_sub, this, sub_self]
    have h1 : ((x - s (π x) : M) : E) ∈ LinearMap.range i := by
      rw [hex]; exact congrArg Subtype.val h0
    obtain ⟨y, hy⟩ := h1
    refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
    show i y ∈ M
    rw [hy]; exact (x - s (π x) : M).2
  let p : M →ₗ[R] M₁ := (LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ π : M →ₗ[R] M) hmem
  have hjp : ∀ x, j (p x) = x - s (π x) := by
    intro x
    exact congrArg Subtype.val ((LinearEquiv.ofInjective j hj).apply_symm_apply
      (LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ π : M →ₗ[R] M) hmem x))
  have hπj : ∀ x, π (j x) = 0 := fun x => Subtype.ext (hqi x)
  have hpj : p ∘ₗ j = LinearMap.id := by
    ext1 x
    apply hj
    rw [LinearMap.comp_apply, hjp, hπj, map_zero, sub_zero, LinearMap.id_apply]
  have hsum : j ∘ₗ p + s ∘ₗ π = LinearMap.id := by
    ext1 x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hjp, LinearMap.id_apply, sub_add_cancel]
  have hbc₁ : IsBaseChange Ω M₁.subtype :=
    isBaseChange_of_split j p π s hpj hsum M₁.subtype M.subtype M₂.subtype i q hi hqi
      (fun _ => rfl) (fun _ => rfl) hbc hbc₂
  have hfin₁ : Module.Finite R M₁ :=
    Module.Finite.of_surjective p (fun x => ⟨j x, LinearMap.congr_fun hpj x⟩)
  have hproj₁ : Module.Projective R M₁ := Module.Projective.of_split j p hpj
  have : Module.Finite Ω E := Module.Finite.equiv hbc.equiv
  have hrk₁ : Module.finrank Ω E₁ = r₁ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker q
    rw [LinearMap.range_eq_top.2 hq, finrank_top, ← hex, LinearMap.finrank_range_of_inj hi,
      hrk, hrk₂] at h1
    omega
  exact _root_.GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.locFree_of_projective R r₁ M₁ hfin₁ hproj₁ hrk₁ hbc₁

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SymplecticPeriodMatrixIntegralityStatement
section
open scoped Matrix TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_period_matrix_integrality : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (g : ℕ) (Ht Bt : Matrix (Fin g) (Fin g ⊕ Fin g) R) (E : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R) (cp : R), cp ≠ 0 → Eᵀ = -E → IsUnit E.det → Btᵀ * Ht - Htᵀ * Bt = cp • E → let φ := algebraMap R C; let intg : (Fin g → C) → Prop := fun w => ∀ k, v (w k) ≤ 1; let hb : Matrix (Fin g ⊕ Fin g) (Fin g) C := ((Eᵀ)⁻¹ * Htᵀ).map φ; v (φ (Matrix.fromRows Ht Bt).det) = v (φ cp) ^ g ∧ (∀ x : Fin g ⊕ Fin g → C, ((Ht.map φ) *ᵥ x = 0 ∧ intg ((Bt.map φ) *ᵥ x)) ↔ ∃ w, intg w ∧ x = (φ cp)⁻¹ • (hb *ᵥ w)) ∧ (∀ w, intg w → ∃ x : Fin g ⊕ Fin g → C, (Ht.map φ) *ᵥ x = w ∧ (Bt.map φ) *ᵥ x = 0) ∧ (∀ l : Fin g ⊕ Fin g → R, cp • l ∈ Submodule.span R (Set.range fun k => Matrix.fromRows Ht Bt k)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.gp_mat_lattice | exact GlobalTheory.CompanionTheory.Ar.GR.gp_mat_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.gp_mat_lattice <;> assumption)
end

