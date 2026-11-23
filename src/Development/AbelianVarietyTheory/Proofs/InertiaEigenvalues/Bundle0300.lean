module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import GroundTheory.LocalFields.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0283

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTameInertiaElementAtAuxiliaryPrime
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.TwSys.InertiaElt

open Filter Topology

theorem exists_coprime_dvd_mul_pow (m : ℕ) (o : ℕ) (ho : o ≠ 0) : ∃ t K : ℕ, Nat.Coprime t m ∧ o ∣ t * m ^ K := by
  induction o using Nat.recOnMul with
  | zero => exact absurd rfl ho
  | one => exact ⟨1, 0, Nat.coprime_one_left m, one_dvd _⟩
  | prime p hp =>
    by_cases h : p ∣ m
    · exact ⟨1, 1, Nat.coprime_one_left m, by simpa using h⟩
    · exact ⟨p, 0, (Nat.Prime.coprime_iff_not_dvd hp).2 h, by simp⟩
  | mul a b iha ihb =>
    obtain ⟨t, K, ht, hK⟩ := iha (left_ne_zero_of_mul ho)
    obtain ⟨t', K', ht', hK'⟩ := ihb (right_ne_zero_of_mul ho)
    refine ⟨t * t', K + K', Nat.Coprime.mul_left ht ht', ?_⟩
    have : t * t' * m ^ (K + K') = (t * m ^ K) * (t' * m ^ K') := by ring
    rw [this]
    exact mul_dvd_mul hK hK'

theorem exists_limit_pow {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (σ : Γ) (m : ℕ) : ∃ z : Γ, (∀ I : Subgroup Γ, IsClosed (I : Set Γ) → σ ∈ I → z ∈ I) ∧
      (∀ U : Subgroup Γ, IsOpen (U : Set Γ) → ∃ k : ℕ, z⁻¹ * σ ^ (m ^ k) ∈ U) ∧
      ∀ U : Subgroup Γ, IsOpen (U : Set Γ) → U.Normal → ∃ n : ℕ, Nat.Coprime n m ∧ z ^ n ∈ U := by
  obtain ⟨z, hz⟩ : ∃ z : Γ, MapClusterPt z atTop (fun k : ℕ => σ ^ (m ^ k)) :=
    exists_clusterPt_of_compactSpace (map (fun k : ℕ => σ ^ (m ^ k)) atTop)
  have key : ∀ U : Subgroup Γ, IsOpen (U : Set Γ) → ∃ᶠ k : ℕ in atTop, z⁻¹ * σ ^ (m ^ k) ∈ U := by
    intro U hU
    have ho : IsOpen ((fun x : Γ => z⁻¹ * x) ⁻¹' (U : Set Γ)) := hU.preimage (by fun_prop)
    exact hz.frequently (p := fun x => z⁻¹ * x ∈ U) (ho.mem_nhds (by simp))
  refine ⟨z, fun I hI hσ => ?_, fun U hU => (key U hU).exists, fun U hU hN => ?_⟩
  · exact hI.mem_of_mapClusterPt hz (Eventually.of_forall fun k => I.pow_mem hσ _)
  · have : Finite (Γ ⧸ U) := U.quotient_finite_of_isOpen hU
    obtain ⟨t, K, ht, hK⟩ := exists_coprime_dvd_mul_pow m (orderOf (QuotientGroup.mk' U σ)) (orderOf_pos _).ne'
    obtain ⟨k, hk, hmem⟩ := frequently_atTop.1 (key U hU) K
    refine ⟨t, ht, ?_⟩
    have e : QuotientGroup.mk' U z = QuotientGroup.mk' U σ ^ (m ^ k) := by
      rw [← map_pow]
      exact QuotientGroup.eq.2 hmem
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' U (z ^ t) = 1
    rw [map_pow, e, ← pow_mul, ← orderOf_dvd_iff_pow_eq_one]
    refine hK.trans ?_
    rw [mul_comm]
    exact Nat.mul_dvd_mul_right (pow_dvd_pow m hk) t

theorem isUnit_sub_one {O : Type*} [CommRing O] [IsDomain O] {n : ℕ} {ζ : O} (hn : IsUnit (n : O))
    (h : IsPrimitiveRoot ζ n) (h1 : 1 < n) : IsUnit (ζ - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 + 1 := ⟨n - 2, by omega⟩
  have e := h.prod_one_sub_pow_eq_order
  rw [Finset.prod_range_succ'] at e
  have hu : IsUnit (1 - ζ ^ (0 + 1)) := by
    refine isUnit_of_mul_isUnit_right (x := ∏ j ∈ Finset.range k, (1 - ζ ^ (j + 1 + 1))) ?_
    rw [e]
    exact_mod_cast hn
  rw [← neg_sub]
  simpa using hu.neg

theorem exists_place_mem (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 E) := by
    intro h
    have h2 : IsUnit (Algebra.norm ℤ ((p : ℕ) : 𝓞 E)) := h.map _
    have e : Algebra.norm ℤ ((p : ℕ) : 𝓞 E) = (p : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      rw [← Algebra.norm_algebraMap]
      simp
    rw [e, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h2
    exact hp.one_lt.ne' h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 E)}) (by
    rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : ((p : ℕ) : 𝓞 E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hmem))

end GlobalTheory.TwSys.InertiaElt


open GlobalTheory.TwSys.InertiaElt in
theorem GlobalTheory.TwSys.exists_tameInertiaElementAtAuxiliaryPrime : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
    (i : X.Tw), ∃ z, IsTameInertiaElementAtTwistPrime X i z := by
  intro D N X i
  have hl : (X.l i).Prime := (X.lPrime i).out
  obtain ⟨v, hv⟩ : ∃ v, v ∈ X.pD i := by
    have hp : (if X.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
      split_ifs
      · exact D.host.pde'_prime
      · exact D.host.pde_prime
    obtain ⟨v, hv⟩ := exists_place_mem D.host.E hp
    refine ⟨v, ?_⟩
    rw [← Finset.mem_coe, X.pD_eq i]
    exact hv
  obtain ⟨A, hA⟩ := exists_isPlaceOver N.Om v

  obtain ⟨p, hp, hp15, hp2, hpl⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ 15 ∧ p ≠ 2 ∧ p ≠ X.l i := by
    by_cases h : X.l i = 3
    · exact ⟨5, by norm_num, by norm_num, by norm_num, by omega⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, fun h' => h h'.symm⟩
  have : Fact p.Prime := ⟨hp⟩
  have hcard := X.delta_15 i v hv A hA
  have : Finite ((Ine (F := D.host.E) A).map (X.delta i)) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨⟨y, hy⟩, hyo⟩ := exists_prime_orderOf_dvd_card' (G := (Ine (F := D.host.E) A).map (X.delta i)) p
    (by rw [hcard]; exact hp15)
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hy
  have hord : orderOf (X.delta i σ) = p := by
    rw [← hyo, ← Subgroup.orderOf_coe]
  obtain ⟨z, hz1, hz2, hz3⟩ := exists_limit_pow σ (X.l i * Ideal.absNorm v.asIdeal)
  refine ⟨z, v, hv, A, hA, hz1 _ (isClosed_Ine A) hσ, ?_, hz3⟩
  obtain ⟨k, hk⟩ := hz2 _ (X.delta_open i)
  have hz : X.delta i z = X.delta i σ ^ ((X.l i * Ideal.absNorm v.asIdeal) ^ k) := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, inv_mul_eq_one] at hk
    exact hk
  have hpl' : Nat.Coprime p (X.l i) := (Nat.coprime_primes hp hl).2 hpl
  have hpq : Nat.Coprime p (Ideal.absNorm v.asIdeal) := by
    refine Nat.Coprime.coprime_dvd_left hp15 ?_
    have := X.delta_tame i v hv
    rw [Nat.Coprime, Nat.gcd_rec, this]
    norm_num
  have hprim : IsPrimitiveRoot (X.delta i σ) p := hord ▸ IsPrimitiveRoot.orderOf _
  have hcop : Nat.Coprime ((X.l i * Ideal.absNorm v.asIdeal) ^ k * 2) p :=
    Nat.Coprime.symm (Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (Nat.Coprime.mul_right hpl' hpq))
      ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have hprim2 : IsPrimitiveRoot (((X.delta i z : (X.O0 i)ˣ) : X.O0 i) ^ 2) p := by
    have := hprim.pow_of_coprime _ hcop
    rw [pow_mul, ← hz] at this
    rw [← Units.val_pow_eq_pow_val]
    exact IsPrimitiveRoot.coe_units_iff.2 this
  refine isUnit_sub_one ?_ hprim2 hp.one_lt
  have hlnu : ¬ IsUnit ((X.l i : ℕ) : X.O0 i) := by
    intro h
    have h2 := h.map (algebraMap (X.O0 i) (X.O i))
    rw [map_natCast] at h2
    exact X.O_l i h2
  have hc : IsCoprime ((p : ℕ) : X.O0 i) ((X.l i : ℕ) : X.O0 i) := hpl'.cast
  obtain ⟨a, b, hab⟩ := hc
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (hab ▸ isUnit_one) with h | h
  · exact isUnit_of_mul_isUnit_right h
  · exact absurd (isUnit_of_mul_isUnit_right h) hlnu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceMemMaximalIdealPowOfDifferentExponent
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_mem_maximalIdeal_pow_eq_trace_of_le_differentExponent :
    ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (n : ℕ), (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) * n ≤ differentExponent F M → ∀ z : 𝒪[M], ∃ w ∈ 𝓂[F] ^ n, ((w : 𝒪[F]) : F) = Algebra.trace F M (z : M) := by
  intro F M _ _ _ _ _ _ _ _ _ _ _ _ n hn z
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hϖ0 : (ϖ : F) ≠ 0 := by
    have : ϖ ≠ 0 := hϖ.ne_zero
    exact_mod_cast this
  set I : Ideal 𝒪[M] := Ideal.span {algebraMap 𝒪[F] 𝒪[M] (ϖ ^ n)} with hI
  have hImap : I = (𝓂[F] ^ n).map (algebraMap 𝒪[F] 𝒪[M]) := by
    rw [hI, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton]
  have hIeq : I = 𝓂[M] ^ ((_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation M))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) * n) := by
    rw [hImap, Ideal.map_pow, map_maximalIdeal, pow_mul]
  have hle : differentIdeal 𝒪[F] 𝒪[M] ≤ I := by
    rw [differentIdeal_eq_maximalIdeal_pow, hIeq]
    exact Ideal.pow_le_pow_right hn
  have hIne : I ≠ ⊥ := by
    rw [hI, ne_eq, Ideal.span_singleton_eq_bot]
    intro h
    have : ((algebraMap 𝒪[F] 𝒪[M] (ϖ ^ n) : 𝒪[M]) : M) = 0 := by rw [h]; rfl
    rw [coe_algebraMap_integer] at this
    rw [SubmonoidClass.coe_pow, map_pow] at this
    exact pow_ne_zero n ((_root_.map_ne_zero _).mpr hϖ0) this
  have key := (differentialIdeal_le_iff (K := F) (L := M) hIne).mp hle
  set x : M := algebraMap F M ((ϖ : F) ^ n) with hx
  have hx0 : x ≠ 0 := by
    rw [hx]; exact (_root_.map_ne_zero _).mpr (pow_ne_zero _ hϖ0)
  have hIfrac : ((I : FractionalIdeal (nonZeroDivisors 𝒪[M]) M)) = FractionalIdeal.spanSingleton (nonZeroDivisors 𝒪[M]) x := by
    rw [hI, FractionalIdeal.coeIdeal_span_singleton]
    congr 1
  have hmem : x⁻¹ * (z : M) ∈ (((I⁻¹ : FractionalIdeal (nonZeroDivisors 𝒪[M]) M) : Submodule 𝒪[M] M)) := by
    rw [hIfrac, FractionalIdeal.spanSingleton_inv, FractionalIdeal.mem_coe,
      FractionalIdeal.mem_spanSingleton]
    exact ⟨z, by rw [Algebra.smul_def, mul_comm]; rfl⟩
  have htr : Algebra.trace F M (x⁻¹ * (z : M)) ∈ (1 : Submodule 𝒪[F] F) :=
    key ⟨_, hmem, rfl⟩
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp htr
  refine ⟨ϖ ^ n * a, Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ) n), ?_⟩
  have hz : (z : M) = x * (x⁻¹ * (z : M)) := by rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
  rw [hz, hx, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  simp only [Subring.coe_mul, SubmonoidClass.coe_pow]
  rw [← ha]
  rfl

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueUnramifiedIntegersCoordsBasis
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS

noncomputable section

namespace GlobalTheory.PrismSplit

theorem isUnit_sub_of_pow_eq_one {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {m : ℕ}
    (hm0 : 0 < m) (hm : IsUnit (m : O)) {a b : O} (ha : a ^ m = 1) (hb : b ^ m = 1) (h : a ≠ b) :
    IsUnit (a - b) := by
  by_contra hn
  have h1 := (Commute.all a b).geom_sum₂_mul m
  rw [ha, hb, sub_self] at h1
  have h2 := (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr h)
  have h3 : IsLocalRing.residue O a = IsLocalRing.residue O b := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hn
  have h4 := congrArg (IsLocalRing.residue O) h2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, h3, map_zero] at h4
  rw [geom_sum₂_self] at h4
  have hbu : IsUnit b := IsUnit.of_pow_eq_one hb hm0.ne'
  have h5 : IsUnit ((m : IsLocalRing.ResidueField O) * IsLocalRing.residue O b ^ (m - 1)) := by
    refine IsUnit.mul ?_ ((hbu.map _).pow _)
    simpa using hm.map (IsLocalRing.residue O)
  exact h5.ne_zero h4

theorem existsUnique_of_separated {R W O ι : Type} [CommRing R] [Nontrivial R] [CommRing W]
    [CommRing O] [Algebra R W] [Algebra R O] [Fintype ι] [Module.Free R W] [Module.Finite R W]
    (hr : Module.finrank R W = Fintype.card ι) (φ : ι → (W →ₐ[R] O))
    (hs : ∀ i j, i ≠ j → ∃ w, IsUnit (φ i w - φ j w)) {d : ℕ} (o : Module.Basis (Fin d) R O)
    (y : ι → O) : ∃! c : Fin d → W, ∀ k, y k = ∑ i, o i * φ k (c i) := by
  classical
  let F : (Fin d → W) →ₗ[R] (ι → O) :=
    { toFun := fun c k => ∑ i, o i * φ k (c i)
      map_add' := fun c c' => by
        funext k; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        funext k; simp [Finset.smul_sum] }
  let Φ : O ⊗[R] W →ₐ[O] (ι → O) :=
    Algebra.TensorProduct.lift (Algebra.ofId O (ι → O)) (AlgHom.pi φ)
      (fun _ _ => Commute.all _ _)
  have hΦ : ∀ (a : O) (w : W) (k : ι), Φ (a ⊗ₜ w) k = a * φ k w := by
    intro a w k
    simp [Φ]
  have h1 : ∀ t, Φ t ∈ LinearMap.range F := by
    intro t
    induction t with
    | add s t hs ht => rw [map_add]; exact add_mem hs ht
    | tmul a w =>
      refine ⟨fun i => o.repr a i • w, ?_⟩
      funext k
      rw [hΦ]
      conv_rhs => rw [← o.sum_repr a]
      rw [Finset.sum_mul]
      simp [F]
  have h2 : ∀ i, Pi.single i (1 : O) ∈ Φ.range := by
    intro i
    choose w hw using hs i
    have : (Pi.single i (1 : O) : ι → O) = ∏ j : {j // i ≠ j}, (((hw j.1 j.2).unit⁻¹ : Oˣ) : O) •
        (Φ (1 ⊗ₜ w j.1 j.2) - algebraMap O (ι → O) (φ j.1 (w j.1 j.2))) := by
      funext k
      rw [Finset.prod_apply]
      by_cases hk : i = k
      · subst hk
        rw [Pi.single_eq_same, eq_comm]
        refine Finset.prod_eq_one fun j _ => ?_
        simp [hΦ]
      · rw [Pi.single_eq_of_ne (Ne.symm hk), eq_comm]
        refine Finset.prod_eq_zero (Finset.mem_univ ⟨k, hk⟩) ?_
        simp [hΦ]
    rw [this]
    refine Subalgebra.prod_mem _ fun j _ => Subalgebra.smul_mem _ (sub_mem (AlgHom.mem_range_self Φ _) ?_) _
    exact Subalgebra.algebraMap_mem _ _
  have h3 : Function.Surjective F := by
    intro y
    have : y ∈ Φ.range := by
      rw [← Finset.univ_sum_single y]
      refine sum_mem fun i _ => ?_
      have : (Pi.single i (y i) : ι → O) = y i • (Pi.single i (1 : O) : ι → O) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this]
      exact Subalgebra.smul_mem _ (h2 i) _
    obtain ⟨t, rfl⟩ := this
    exact h1 t
  have : Module.Free R O := Module.Free.of_basis o
  have : Module.Finite R O := Module.Finite.of_basis o
  have e : (Fin d → W) ≃ₗ[R] (ι → O) := LinearEquiv.ofFinrankEq _ _ (by
    simp [Module.finrank_pi_fintype, hr, Module.finrank_eq_card_basis o, mul_comm])
  have h4 : Function.Injective F :=
    OrzechProperty.injective_of_surjective_of_injective e.toLinearMap F e.injective h3
  obtain ⟨c, hc⟩ := h3 y
  refine ⟨c, fun k => (congrFun hc k).symm, fun c' hc' => h4 ?_⟩
  rw [hc]
  exact funext fun k => (hc' k).symm

theorem exists_root_ne {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
    {e e' : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1} (h : e ≠ e') :
    ∃ (ω : ↥(K0 K)) (m : ℕ), 0 < m ∧ ¬ l ∣ m ∧ ω ^ m = 1 ∧ e ω ≠ e' ω := by
  by_contra hn
  push Not at hn
  apply h
  ext1 x
  obtain ⟨a, ha⟩ := NormedField.exists_lt_norm ℚ_[l] ‖(x : Om l)‖
  have ha0 : 0 < ‖a‖ := (norm_nonneg _).trans_lt ha
  have ha1 : a ≠ 0 := norm_pos_iff.mp ha0
  obtain ⟨n, z, ω, hω, hx⟩ := GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K
    (algebraMap ℚ_[l] (Om l) a⁻¹ * x) (algebraMap ℚ_[l] ↥(K0 K) a⁻¹ * x).2 (by
      rw [← Algebra.smul_def, norm_smul, norm_inv, inv_mul_le_iff₀ ha0, mul_one]
      exact ha.le)
  have hx' : algebraMap ℚ_[l] ↥(K0 K) a⁻¹ * x =
      ∑ i, algebraMap ℚ_[l] ↥(K0 K) (z i : ℚ_[l]) * (⟨ω i, (hω i).1⟩ : ↥(K0 K)) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact hx
  have : e (algebraMap ℚ_[l] ↥(K0 K) a⁻¹ * x) = e' (algebraMap ℚ_[l] ↥(K0 K) a⁻¹ * x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx', map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨m, hm, hl, h1⟩ := (hω i).2
    rw [map_mul, map_mul, e.commutes, e'.commutes, hn _ m hm hl (Subtype.ext (by simpa using h1))]
  rw [map_mul, map_mul, e.commutes, e'.commutes] at this
  exact mul_left_cancel₀ ((_root_.map_ne_zero _).mpr (inv_ne_zero ha1)) this

theorem isUnit_natCast {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] {m : ℕ}
    (hl : ¬ l ∣ m) : IsUnit (m : O) := by
  have hu : IsUnit (m : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hl ?_)
    have := (PadicInt.norm_int_lt_one_iff_dvd (p := l) (m : ℤ)).mp (by simpa using h)
    exact_mod_cast this
  simpa using hu.map (algebraMap ℤ_[l] O)

theorem exists_isUnit_sub {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
    {e e' : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1} (h : e ≠ e') : ∃ w, IsUnit (embW e w - embW e' w) := by
  obtain ⟨_, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨ω, m, hm, hl, h1, hne⟩ := exists_root_ne h
  have hi : IsIntegral ℤ_[l] ω := IsIntegral.of_pow hm (by rw [h1]; exact isIntegral_one)
  have hp : ∀ f : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1, embW f ⟨ω, hi⟩ ^ m = 1 := by
    intro f
    apply Subtype.ext
    change f ω ^ m = 1
    rw [← map_pow, h1, map_one]
  exact ⟨⟨ω, hi⟩, isUnit_sub_of_pow_eq_one hm (isUnit_natCast _ hl) (hp e) (hp e')
    fun h => hne (congrArg Subtype.val h)⟩

theorem existsUnique_coords : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (emb : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)), Function.Injective emb → ∀ (d : ℕ) (o : Module.Basis (Fin d) ℤ_[l] ↥(OL LL)) (y : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)), ∃! c : Fin d → WK K, ∀ k, y k = ∑ i, o i * embW (emb k) (c i) := by
  intro l _ K LL emb hemb d o y
  have hfd : FiniteDimensional ℚ_[l] ↥(K0 K) := (unr K).2
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨_, -, -, -, hfree, hfin, -⟩ := GlobalTheory.Per.integers_completeDVR l (unr K)
  have : Module.IsTorsionFree ℤ_[l] ↥(K0 K) := by
    rw [Module.isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥(K0 K)]
    exact (algebraMap ℚ_[l] ↥(K0 K)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  refine existsUnique_of_separated ?_ (fun k => embW (emb k)) ?_ o y
  · rw [ZMod.card]
    exact IsIntegralClosure.rank ℤ_[l] ℚ_[l] ↥(K0 K) (integralClosure ℤ_[l] ↥(K0 K))
  · exact fun i j hij => exists_isUnit_sub (hemb.ne hij)

end GlobalTheory.PrismSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobFixedLatticeConditionSmulOfFrobeniusFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

theorem latC_smul_of_fr_fixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (a : n → P.R.B) (e : ↥(MaximalUnramifiedExtension l)), fr l r e = e → LatC P U x y a → LatC P U x y (e • a) := by
  intro l _ P r n _ _ U x y a e he h
  obtain ⟨h1, h2⟩ := h
  have hsm : ∀ i, (e • a) i = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * a i := fun i => by
    rw [Pi.smul_apply, Algebra.smul_def]
  have hev : ∀ (m : ℕ) (b : P.R.B), ev P m (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * b) = kd P (fr l m e) * ev P m b := by
    intro m b
    rw [← evHom_apply, map_mul, evHom_apply, evHom_apply, ev_kur]
  refine ⟨fun i => ?_, fun m => ?_⟩
  · rw [hsm]
    have key : ∀ k : ℕ, P.φB^[k] (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B e * a i) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l k e) * P.φB^[k] (a i) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', ih, map_mul, Function.iterate_succ_apply', phiB_algebraMap, add_comm, fr_add, fr_one]
    rw [key, he, h1]
  · obtain ⟨w, hw, hw'⟩ := h2 m
    refine ⟨fun i => kd P (fr l m e) * w i, fun i => Fil_mul_left (kd_mem_Fil P _) (hw i), ?_⟩
    funext i
    rw [hsm, hev]
    have := congrFun hw' i
    rw [this]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PMon.ResR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusTensorCrisToSemistableCommStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusTensor_crisToSemistable_comm : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (w : V ⊗[ℚ_[l]] P.R.B), phiV P ℚ_[l] V (crisIncl P ℚ_[l] V w) = crisIncl P ℚ_[l] V (φVB (P.PD K) (LL := ℚ_[l]) (V := V) w) := by
  first | exact @GlobalTheory.PMon.phiV_crisIncl_comm | exact GlobalTheory.PMon.phiV_crisIncl_comm | (intros; apply GlobalTheory.PMon.phiV_crisIncl_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittCompletePiAdicModEll
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

section Generic

variable {A R : Type} [CommRing A] [CommRing R] {ι : A →+* R} {p : ℕ} {t : R}

theorem Near.map_of_fixed (g : R →+* R) (hg : ∀ a, ∃ b, ι b = g (ι a)) (ht : g t = t) {m : ℕ}
    {x : R} (hx : Near ι p t m x) : Near ι p t m (g x) := by
  obtain ⟨a, r, rfl⟩ := hx
  obtain ⟨b, hb⟩ := hg a
  exact ⟨b, g r, by rw [map_add (f := _), map_mul, map_mul, map_pow, map_natCast, ht, hb]⟩

theorem fixed_complete_generic {G : Type} (H : Set G) (act : G → (R →+* R)) (S : Subring R)
    (hS : ∀ x, x ∈ S ↔ ∀ g ∈ H, act g x = x) {τ : A} (hτ : ι τ = t)
    (hg : ∀ g a, ∃ b, ι b = act g (ι a))
    (hsep : ∀ x : R, (∀ m, Near ι p t m x) → ∃ r, x = (p : R) * r)
    (hcomp : ∀ (k : ℕ) (f : ℕ → R), (∀ i, Near ι p t (i + k) (f i)) →
      ∃ x, ∀ m, Near ι p t (m + k) (x - ∑ i ∈ Finset.range m, f i))
    (hlift : ∀ x : R, (∀ g ∈ H, ∃ r, act g x - x = (p : R) * r) →
      ∃ y ∈ S, ∃ r, y - x = (p : R) * r)
    (ht : t ∈ S) (k : ℕ) (f : ℕ → R) (hf : ∀ i, f i ∈ S) (hn : ∀ i, Near ι p t (i + k) (f i)) :
    ∃ x ∈ S, ∀ m, Near ι p t (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  obtain ⟨x, hx⟩ := hcomp k f hn
  obtain ⟨y, hy, r, hr⟩ := hlift x fun g hgH => hsep _ fun m => by
    have h1 : act g (∑ i ∈ Finset.range m, f i) = ∑ i ∈ Finset.range m, f i :=
      (hS _).1 (S.sum_mem fun i _ => hf i) g hgH
    have h2 := (Near.map_of_fixed (act g) (hg g) ((hS _).1 ht g hgH) (hx m)).sub (hx m)
    rw [map_sub, h1, sub_sub_sub_cancel_right] at h2
    exact h2.mono hτ (Nat.le_add_right m k)
  refine ⟨y, hy, fun m => ?_⟩
  have h3 := (Near.of_mul (ι := ι) (p := p) (t := t) (m + k) r).add (hx m)
  rw [← hr, sub_add_sub_cancel] at h3
  exact h3

end Generic

theorem fixSub_nearPi_complete : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) (H : Set (GQ l)), piR AI LL s ∈ fixSub AI LL H → ∀ (k : ℕ) (f : ℕ → RW LL), (∀ i, f i ∈ fixSub AI LL H) → (∀ i, NearPi AI LL s (i + k) (f i)) → ∃ x ∈ fixSub AI LL H, ∀ m, NearPi AI LL s (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  intro l _ P AI LL s H
  exact fixed_complete_generic H (fun g => (AI.gRW LL g : RW LL →+* RW LL)) (fixSub AI LL H)
    (fun _ => mem_fixSub) (τ := (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piW AI s) rfl
    (fun g a => ⟨GlobalTheory.Cyc.Decomp.gRA AI LL g a, GlobalTheory.Cyc.Decomp.inclR_gRA AI LL g a⟩)
    (_root_.GlobalTheory.Decompl.nearPi_sep_complete l P AI LL s).1 (_root_.GlobalTheory.Decompl.nearPi_sep_complete l P AI LL s).2 (GlobalTheory.T.exists_galois_fixed_lift_of_fixed_mod_prime l P AI LL H)

end GlobalTheory.Decompl
end

