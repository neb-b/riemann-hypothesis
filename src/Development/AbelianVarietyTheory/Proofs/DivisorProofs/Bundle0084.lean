module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanHeisenbergTranslatesOfVacuum
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.HeisVacuum

theorem mem_span_translates_vacuum (X M : Type) [AddCommGroup X] [AddCommGroup M] [Module ℂ M]
    (β : X → X → ℂ) (ρ : X → M →ₗ[ℂ] M) (Λ : AddSubgroup X) (e : M)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1) (h0 : ∀ v, ρ 0 v = v)
    (hρ : ∀ x y v, ρ x (ρ y v) = β x y • ρ (x + y) v)
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ a ∈ Λ, β x a ^ 2 = 1)
    (hdiv : ∀ N : ℕ, 0 < N → ∀ x : X, ∃ y : X, N • y = x)
    (hfin : ∀ N : ℕ, 0 < N → ∃ R : Set X, R.Finite ∧ ∀ t ∈ Λ, ∃ r ∈ R, ∃ u ∈ Λ, t = r + N • u)
    (he : e ≠ 0) (hε : ∀ u ∈ Λ, ∃ ε : ℂ, ρ u e = ε • e) (h2 : ∀ u ∈ Λ, ρ (2 • u) e = e)
    (hvac : ∀ v : M, (∀ u ∈ Λ, ∀ ε : ℂ, ρ u e = ε • e → ρ u v = ε • v) → ∃ c : ℂ, v = c • e)
    (v : M) (hv : ∃ N : ℕ, 0 < N ∧ ∀ u ∈ Λ, ρ (N • u) v = v) :
    v ∈ Submodule.span ℂ (Set.range fun x => ρ x e) := by
  classical
  obtain ⟨N, hN, hv⟩ := hv
  have hsym : ∀ x y, β x y * β y x = 1 := by
    intro x y
    have := hd (x + y)
    rw [hl, hr, hr, hd, hd] at this
    simpa using this
  have hne : ∀ x y, β x y ≠ 0 := fun x y => left_ne_zero_of_mul_eq_one (hsym x y)
  have hz1 : ∀ y, β 0 y = 1 := by
    intro y
    have := hl 0 0 y
    rw [add_zero] at this
    exact (mul_eq_left₀ (hne 0 y)).1 this.symm
  have hz2 : ∀ y, β y 0 = 1 := by
    intro y
    have := hsym y 0
    rwa [hz1, mul_one] at this
  have hp1 : ∀ (n : ℕ) x y, β (n • x) y = β x y ^ n := by
    intro n x y
    induction n with
    | zero => simp [hz1]
    | succ n ih => rw [succ_nsmul, hl, ih, pow_succ]
  have hp2 : ∀ (n : ℕ) x y, β x (n • y) = β x y ^ n := by
    intro n x y
    induction n with
    | zero => simp [hz2]
    | succ n ih => rw [succ_nsmul, hr, ih, pow_succ]
  have hcomm : ∀ x y w, ρ x (ρ y w) = β x y ^ 2 • ρ y (ρ x w) := by
    intro x y w
    rw [hρ, hρ, smul_smul, add_comm y x, pow_two, mul_assoc, hsym, mul_one]
  have hinv : ∀ t w, ρ t (ρ (-t) w) = w := by
    intro t w
    have := hr t t (-t)
    rw [add_neg_cancel, hz2, hd, one_mul] at this
    rw [hρ, add_neg_cancel, h0, ← this, one_smul]
  choose! ε hε using hε
  have huniq : ∀ u ∈ Λ, ∀ c : ℂ, ρ u e = c • e → c = ε u := by
    intro u hu c hc
    rw [hε u hu] at hc
    exact (smul_left_injective ℂ he hc).symm
  have hεne : ∀ u ∈ Λ, ε u ≠ 0 := by
    intro u hu h
    have := hinv (-u) e
    rw [neg_neg, hε u hu, h, zero_smul, map_zero] at this
    exact he this.symm
  have hεmul : ∀ u ∈ Λ, ∀ u' ∈ Λ, ε u * ε u' = β u u' * ε (u + u') := by
    intro u hu u' hu'
    have := hρ u u' e
    rw [hε u' hu', map_smul, hε u hu, hε _ (Λ.add_mem hu hu'), smul_smul, smul_smul, mul_comm] at this
    exact smul_left_injective ℂ he this
  let A : Λ → M → M := fun u w => (ε u)⁻¹ • ρ u w
  have hA : ∀ (u u' : Λ) w, A u (A u' w) = A (u + u') w := by
    intro u u' w
    simp only [A, map_smul, hρ, smul_smul, AddSubgroup.coe_add]
    congr 1
    have h1 := hεmul u u.2 u' u'.2
    have h3 := hεne u u.2
    have h4 := hεne u' u'.2
    have h5 := hεne _ (Λ.add_mem u.2 u'.2)
    field_simp
    rw [h1, mul_comm]
  have hA0 : ∀ w, A 0 w = w := by
    intro w
    have : (1 : ℂ) = ε 0 := huniq 0 Λ.zero_mem 1 (by rw [h0, one_smul])
    simp [A, h0, ← this]
  set K : ℕ := 2 * N with hK
  have hKpos : 0 < K := by omega
  have hεK : ∀ u ∈ Λ, ε (K • u) = 1 := by
    intro u hu
    refine (huniq _ (Λ.nsmul_mem hu K) 1 ?_).symm
    rw [one_smul, hK, mul_comm, mul_nsmul]
    exact h2 _ (Λ.nsmul_mem hu N)
  have hvK : ∀ u ∈ Λ, ρ (K • u) v = v := by
    intro u hu
    rw [hK, mul_nsmul]
    exact hv _ (Λ.nsmul_mem hu 2)
  let H : AddSubgroup Λ := (nsmulAddMonoidHom K : Λ →+ Λ).range
  have hQ : Finite (Λ ⧸ H) := by
    obtain ⟨R, hR, hR'⟩ := hfin K hKpos
    have : Finite {x : Λ // (x : X) ∈ R} := by
      have : Finite R := hR
      exact Finite.of_injective (fun x : {x : Λ // (x : X) ∈ R} => (⟨x.1, x.2⟩ : R))
        (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : R => (z : X)) h)))
    refine Finite.of_surjective (fun x : {x : Λ // (x : X) ∈ R} => (QuotientAddGroup.mk x.1 : Λ ⧸ H)) ?_
    intro q
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, hr, u, hu, htu⟩ := hR' t t.2
    have hrΛ : r ∈ Λ := by
      have : r = t - K • u := by rw [htu]; abel
      rw [this]
      exact Λ.sub_mem t.2 (Λ.nsmul_mem hu K)
    refine ⟨⟨⟨r, hrΛ⟩, hr⟩, ?_⟩
    refine QuotientAddGroup.eq.2 ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    simp [htu]
  have := Fintype.ofFinite (Λ ⧸ H)
  have hwell : ∀ w, (∀ u ∈ Λ, ρ (K • u) w = w) → ∀ x y : Λ,
      (QuotientAddGroup.mk x : Λ ⧸ H) = QuotientAddGroup.mk y → A x w = A y w := by
    intro w hw x y hxy
    obtain ⟨u, hu⟩ := QuotientAddGroup.eq.1 hxy
    have h1 : y = x + K • u := by
      have : K • u = -x + y := hu
      rw [this]; abel
    have h3 : A (K • u) w = w := by
      simp only [A, AddSubgroup.coe_nsmul, hεK u u.2, hw u u.2, inv_one, one_smul]
    rw [h1, ← hA, h3]
  have hAsum : ∀ (u : Λ) (f : Λ ⧸ H → M), A u (∑ q, f q) = ∑ q, A u (f q) := by
    intro u f
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [A, map_sum, Finset.smul_sum]
  have hP : ∀ w, (∀ u ∈ Λ, ρ (K • u) w = w) → ∃ c : ℂ, (∑ q : Λ ⧸ H, A q.out w) = c • e := by
    intro w hw
    apply hvac
    intro u hu c hc
    rw [huniq u hu c hc]
    have h1 : A ⟨u, hu⟩ (∑ q : Λ ⧸ H, A q.out w) = ∑ q : Λ ⧸ H, A q.out w := by
      rw [hAsum]
      refine Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk ⟨u, hu⟩ : Λ ⧸ H)) _ _ ?_
      intro q
      rw [hA]
      apply hwell w hw
      simp
    conv_rhs => rw [← h1]
    simp only [A, smul_smul, mul_inv_cancel₀ (hεne u hu), one_smul]
  let Tg : AddSubgroup X := Λ.comap (nsmulAddMonoidHom K : X →+ X)
  have hTg : ∀ t, t ∈ Tg ↔ K • t ∈ Λ := fun t => Iff.rfl
  let S := Submodule.span ℂ (Set.range fun x => ρ x e)
  have hmem : ∀ t ∈ Tg, (∑ q : Λ ⧸ H, β t (q.out : Λ) ^ 2 • A q.out v) ∈ S := by
    intro t ht
    obtain ⟨c, hc⟩ := hP (ρ (-t) v) (by
      intro u hu
      rw [hcomm, hvK u hu, hp1, ← hp2, (hΛ u).1 hu _ ((hTg _).1 (Tg.neg_mem ht)), one_smul])
    have h1 := congrArg (ρ t) hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_smul] at h1
    have h3 : c • ρ t e ∈ S := S.smul_mem c (Submodule.subset_span ⟨t, rfl⟩)
    rw [← h1] at h3
    convert h3 using 2 with q
    simp only [A, map_smul]
    rw [hcomm t, hinv, smul_comm]
  let χ : Λ ⧸ H → (Multiplicative Tg →* ℂ) := fun q =>
    { toFun := fun t => β (t.toAdd : Tg) (q.out : Λ) ^ 2
      map_one' := by simp [hz1]
      map_mul' := by intro a b; simp [hl, mul_pow] }
  have hχ : Function.Injective χ := by
    intro q q' h
    have h1 : ∀ t ∈ Tg, β t (q.out : Λ) ^ 2 = β t (q'.out : Λ) ^ 2 := fun t ht =>
      DFunLike.congr_fun h (Multiplicative.ofAdd ⟨t, ht⟩)
    obtain ⟨y, hy⟩ := hdiv K hKpos (-((q.out : Λ) : X) + (q'.out : Λ))
    have hyΛ : y ∈ Λ := by
      rw [hΛ]
      intro a ha
      obtain ⟨t, rfl⟩ := hdiv K hKpos a
      have h3 := h1 t ha
      have h4 : ((q'.out : Λ) : X) = (q.out : Λ) + K • y := by rw [hy]; abel
      rw [h4, hr, mul_pow, hp2, ← hp1 K] at h3
      have h5 : β (K • t) y ^ 2 = 1 :=
        (mul_eq_left₀ (pow_ne_zero 2 (hne _ _))).1 h3.symm
      have h6 := congrArg (· ^ 2) (hsym y (K • t))
      simpa [mul_pow, h5] using h6
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
    exact QuotientAddGroup.eq.2 ⟨⟨y, hyΛ⟩, Subtype.ext (by simpa using hy)⟩
  have hli : LinearIndependent ℂ (fun q => (χ q : Multiplicative Tg → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative Tg) ℂ).comp χ hχ
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have h1 := Fintype.linearIndependent_iff.1 hli (fun q => φ (S.mkQ (A q.out v))) (by
    funext t
    have h3 := (Submodule.Quotient.mk_eq_zero S).2 (hmem _ (t.toAdd).2)
    have h4 := congrArg φ h3
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Submodule.mkQ_apply, map_sum, map_sum, map_zero] at h4
    simp only [map_smul, smul_eq_mul] at h4
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← h4]
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _) 0
  have h3 : A (0 : Λ ⧸ H).out v = v := by
    rw [hwell v hvK _ 0 (by simp), hA0]
  simpa [h3] using h1

end GlobalTheory.HeisVacuum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubfieldOfBilinFormBasisMonomials
section
namespace GlobalTheory

theorem mem_subfield_of_zpow_mem {K : Type} [Field K] (k₀ : Subfield K) [IsAlgClosed k₀]
    (u : Kˣ) (m : ℤ) (hm : m ≠ 0) (h : ((u ^ m : Kˣ) : K) ∈ k₀) : (u : K) ∈ k₀ := by
  have h1 : (u : K) ^ m.natAbs ∈ k₀ := by
    rw [Units.val_zpow_eq_zpow_val] at h
    rcases Int.natAbs_eq m with h2 | h2
    · rw [h2, zpow_natCast] at h; exact h
    · rw [h2, zpow_neg, zpow_natCast] at h
      simpa using k₀.inv_mem h
  have hint : IsIntegral k₀ (u : K) := by
    apply IsIntegral.of_pow (Int.natAbs_pos.mpr hm)
    exact isIntegral_algebraMap (R := k₀) (x := ⟨_, h1⟩)
  obtain ⟨y, hy⟩ := minpoly.mem_range_of_degree_eq_one k₀ (u : K)
    (IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible hint))
  rw [← hy]
  exact y.2

def monomialExponents {I : Type} [Fintype I] {K : Type} [Field K] (k₀ : Subfield K)
    (t : I → Kˣ) : Submodule ℤ (I → ℤ) :=
  AddSubgroup.toIntSubmodule
  { carrier := {v | ((∏ k, t k ^ v k : Kˣ) : K) ∈ k₀}
    zero_mem' := by simp [k₀.one_mem]
    add_mem' := by
      intro a b ha hb
      simp only [Set.mem_setOf_eq, Pi.add_apply, zpow_add, Finset.prod_mul_distrib,
        Units.val_mul] at *
      exact k₀.mul_mem ha hb
    neg_mem' := by
      intro a ha
      simp only [Set.mem_setOf_eq, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib,
        Units.val_inv_eq_inv_val] at *
      exact k₀.inv_mem ha }

theorem mem_monomialExponents {I : Type} [Fintype I] {K : Type} [Field K] (k₀ : Subfield K)
    (t : I → Kˣ) (v : I → ℤ) :
    v ∈ monomialExponents k₀ t ↔ ((∏ k, t k ^ v k : Kˣ) : K) ∈ k₀ := Iff.rfl

theorem mem_monomialExponents_of_smul {I : Type} [Fintype I] {K : Type} [Field K]
    (k₀ : Subfield K) [IsAlgClosed k₀] (t : I → Kˣ) (v : I → ℤ) (m : ℤ) (hm : m ≠ 0)
    (h : m • v ∈ monomialExponents k₀ t) : v ∈ monomialExponents k₀ t := by
  rw [mem_monomialExponents] at h ⊢
  apply mem_subfield_of_zpow_mem k₀ _ m hm
  convert h using 2
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem mem_subfield_of_bilinForm_monomials :
    ∀ (X : Type) [AddCommGroup X] (S : Submodule ℤ (LinearMap.BilinForm ℤ X)) (I : Type) [Fintype I]
    (ε : Module.Basis I ℤ S) (K : Type) [Field K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (n : ℤ), n ≠ 0 →
    ∀ (t : I → Kˣ), (∀ a b : X, ((∏ k, t k ^ (n * (ε k : LinearMap.BilinForm ℤ X) a b) : Kˣ) : K) ∈ k₀) →
    ∀ k, (t k : K) ∈ k₀ := by
  intro X _ S I _ ε K _ k₀ hk n hn t h k
  classical
  set P := monomialExponents k₀ t with hP
  have hv : ∀ a b : X, (fun k => (ε k : LinearMap.BilinForm ℤ X) a b) ∈ P := fun a b =>
    mem_monomialExponents_of_smul k₀ t _ n hn (h a b)
  haveI : NoZeroSMulDivisors ℤ ((I → ℤ) ⧸ P) := by
    refine ⟨fun {c x} hx => ?_⟩
    obtain ⟨v, rfl⟩ := P.mkQ_surjective x
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [← map_smul] at hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx ⊢
      exact mem_monomialExponents_of_smul k₀ t v c hc hx
  haveI : Module.Free ℤ ((I → ℤ) ⧸ P) := Module.free_of_finite_type_torsion_free'
  have key : P.mkQ (Pi.single k 1) = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff ℤ]
    intro φ
    have hz : ∑ j, φ (P.mkQ (Pi.single j 1)) • ε j = 0 := by
      apply Subtype.ext
      ext a b
      have h0 : φ (P.mkQ (fun k => (ε k : LinearMap.BilinForm ℤ X) a b)) = 0 := by
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).mpr (hv a b), map_zero]
      have h1 : (fun k => (ε k : LinearMap.BilinForm ℤ X) a b)
          = ∑ j, (ε j : LinearMap.BilinForm ℤ X) a b • (Pi.single j 1 : I → ℤ) := by
        funext i
        simp [Finset.sum_apply, Pi.single_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h1, map_sum, map_sum] at h0
      simp only [map_smul, smul_eq_mul] at h0
      simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, LinearMap.zero_apply]
      rw [← h0]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact Fintype.linearIndependent_iff.mp ε.linearIndependent _ hz k
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hP, mem_monomialExponents] at key
  convert key using 2
  rw [Finset.prod_eq_single k]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportQuotientIff
section
open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory.QuotientSupportBaseChange

theorem mem_support_baseChange {R A M : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (p : PrimeSpectrum A) :
    p ∈ Module.support A (A ⊗[R] M) ↔
      PrimeSpectrum.comap (algebraMap R A) p ∈ Module.support R M := by

  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  let Kp := p.asIdeal.ResidueField
  let Kq := (PrimeSpectrum.comap (algebraMap R A) p).asIdeal.ResidueField
  have hq : (PrimeSpectrum.comap (algebraMap R A) p).asIdeal = p.asIdeal.comap (algebraMap R A) := rfl
  let _ : Algebra Kq Kp :=
    (Ideal.ResidueField.map (PrimeSpectrum.comap (algebraMap R A) p).asIdeal p.asIdeal (algebraMap R A) hq).toAlgebra
  have : IsScalarTower R Kq Kp := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R Kp r = Ideal.ResidueField.map (PrimeSpectrum.comap (algebraMap R A) p).asIdeal
      p.asIdeal (algebraMap R A) hq (algebraMap R Kq r)
    rw [Ideal.ResidueField.map_algebraMap]
    exact IsScalarTower.algebraMap_apply R A Kp r
  rw [(AlgebraTensorModule.cancelBaseChange R A Kp Kp M).nontrivial_congr,
    ← (AlgebraTensorModule.cancelBaseChange R Kq Kp Kp M).nontrivial_congr]
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right Kq Kp

theorem nonempty_quotient_equiv {R A M N ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₗ[R] N) (hf : IsBaseChange A f) (s : ι → M) :
    Nonempty ((A ⊗[R] (M ⧸ Submodule.span R (Set.range s))) ≃ₗ[A]
      N ⧸ Submodule.span A (Set.range fun i => f (s i))) := by

  let n := Submodule.span R (Set.range s)
  let e₀ := AlgebraTensorModule.tensorQuotientEquiv (R := R) A R A n
  have hmap : (LinearMap.range (AlgebraTensorModule.lTensor A A (n.subtype.restrictScalars R))).map
      (hf.equiv : A ⊗[R] M →ₗ[A] N) = Submodule.span A (Set.range fun i => f (s i)) := by
    change (n.baseChange A).map (hf.equiv : A ⊗[R] M →ₗ[A] N) = _
    rw [Submodule.baseChange_span, Submodule.map_span]
    congr 1
    ext x
    simp [IsBaseChange.equiv_tmul]
  exact ⟨e₀.trans (Submodule.Quotient.equiv _ _ hf.equiv hmap)⟩

theorem mem_support_quotient_iff (R S R' S' : CommRingCat.{0}) (qa : R ⟶ S) (ba : R ⟶ R')
    (ga : S ⟶ S') (qa' : R' ⟶ S') (h : IsPushout qa ba ga qa') (hfin : qa.hom.Finite)
    {ι : Type} (s : ι → S) (p : PrimeSpectrum R') :
    ((letI := qa'.hom.toAlgebra; p ∈ Module.support R'
        (S' ⧸ Submodule.span R' (Set.range (fun i => ga.hom (s i))))) ↔
      (letI := qa.hom.toAlgebra; PrimeSpectrum.comap ba.hom p ∈ Module.support R
        (S ⧸ Submodule.span R (Set.range s)))) := by
  let _ : Algebra R R' := ba.hom.toAlgebra
  let _ : Algebra R S := qa.hom.toAlgebra
  let _ : Algebra R' S' := qa'.hom.toAlgebra
  let _ : Algebra S S' := ga.hom.toAlgebra
  let _ : Algebra R S' := (qa ≫ ga).hom.toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun r => by
    change (qa ≫ ga).hom r = qa'.hom (ba.hom r)
    rw [h.w]
    rfl
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun r => rfl
  have hpo : Algebra.IsPushout R R' S S' := CommRingCat.isPushout_iff_isPushout.mp h.flip
  have : Module.Finite R S := hfin

  obtain ⟨e⟩ : Nonempty ((R' ⊗[R] (S ⧸ Submodule.span R (Set.range s))) ≃ₗ[R']
      S' ⧸ Submodule.span R' (Set.range fun i => ga.hom (s i))) :=
    nonempty_quotient_equiv _ hpo.out s
  have key : p ∈ Module.support R' (S' ⧸ Submodule.span R' (Set.range fun i => ga.hom (s i))) ↔
      PrimeSpectrum.comap ba.hom p ∈ Module.support R (S ⧸ Submodule.span R (Set.range s)) := by
    rw [← e.support_eq]
    exact mem_support_baseChange p
  exact key

end GlobalTheory.QuotientSupportBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicCoeffNatDegreeSubEqMulCmConj
section
open NumberField Polynomial

namespace GlobalTheory

theorem coeff_natDegree_sub_eq_of_roots_norm_one (Q : ℂ[X]) (hQ : Q.Monic)
    (hroots : ∀ z ∈ Q.roots, ‖z‖ = 1) :
    ∀ i ≤ Q.natDegree, Q.coeff (Q.natDegree - i) = Q.coeff 0 * starRingEnd ℂ (Q.coeff i) := by
  intro i hi
  set s := Q.roots with hs
  have hprod : (s.map fun z => X - C z).prod = Q := by
    have h := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := Q) IsAlgClosed.card_roots_eq_natDegree
    rwa [hQ.leadingCoeff, C_1, one_mul] at h
  have hrevX : ∀ z ∈ s, (X - C z : ℂ[X]).reverse = C (-z) * (X - C (starRingEnd ℂ z)) := by
    intro z hz
    have hz1 : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hroots z hz]; simp
    rw [sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X, ← one_mul (X : ℂ[X]), reverse_mul_X, ← C_1, reverse_C]
    rw [mul_sub, ← C_mul, neg_mul, hz1]
    simp only [C_1, C_neg, one_mul, pow_one]
    ring
  have hrev : Q.reverse = C (Q.coeff 0) * Q.map (starRingEnd ℂ) := by
    have key : ∀ t : Multiset ℂ, (∀ z ∈ t, (X - C z : ℂ[X]).reverse = C (-z) * (X - C (starRingEnd ℂ z))) →
        (t.map fun z => X - C z).prod.reverse
          = (t.map fun z => C (-z) * (X - C (starRingEnd ℂ z))).prod := by
      intro t
      induction t using Multiset.induction_on with
      | empty => intro _; simpa using reverse_C (1 : ℂ)
      | cons a t ih =>
        intro h
        rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons,
          reverse_mul_of_domain, ih (fun z hz => h z (Multiset.mem_cons_of_mem hz)),
          h a (Multiset.mem_cons_self a t)]
    conv_lhs => rw [← hprod]
    rw [key s hrevX, Multiset.prod_map_mul]
    conv_rhs => rw [← hprod]
    congr 1
    · rw [coeff_zero_multiset_prod, Multiset.map_map, map_multiset_prod, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro z _
      simp
    · rw [Polynomial.map_multiset_prod, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro z _
      simp
  have h1 := congrArg (fun p => p.coeff i) hrev
  simp only [coeff_reverse, coeff_C_mul, coeff_map] at h1
  rwa [revAt_le hi] at h1

theorem monic_coeff_natDegree_sub_eq_mul_complexConj :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Polynomial E),
    P.Monic → P.natDegree = n → (∀ (τ : E →+* ℂ), ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) →
    ∀ i ≤ n, P.coeff (n - i) = P.coeff 0 * IsCMField.complexConj E (P.coeff i) := by
  intro E _ _ _ n P hP hn hroots i hi
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  have hQ : (P.map τ).Monic := hP.map τ
  have hdeg : (P.map τ).natDegree = n := by rw [hP.natDegree_map, hn]
  have h := coeff_natDegree_sub_eq_of_roots_norm_one (P.map τ) hQ (hroots τ) i (hdeg ▸ hi)
  rw [hdeg, coeff_map, coeff_map, coeff_map, ← IsCMField.complexEmbedding_complexConj E τ,
    ← map_mul] at h
  exact τ.injective h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastNotMemOfCoprime
section
universe u_1

namespace GlobalTheory.CoprimeNatNotMem

theorem natCast_not_mem_of_coprime {Rg : Type u_1} [CommRing Rg] {P : Ideal Rg} (hP : P ≠ ⊤)
    {p n : ℕ} (h : Nat.Coprime p n) (hp : (p : Rg) ∈ P) : (n : Rg) ∉ P := by
  intro hn

  obtain ⟨u, v, huv⟩ : IsCoprime (p : Rg) (n : Rg) := by
    have hz : IsCoprime (p : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.mpr h
    simpa using hz.map (Int.castRingHom Rg)
  apply hP
  rw [Ideal.eq_top_iff_one, ← huv]
  exact P.add_mem (P.mul_mem_left u hp) (P.mul_mem_left v hn)

end GlobalTheory.CoprimeNatNotMem
end

