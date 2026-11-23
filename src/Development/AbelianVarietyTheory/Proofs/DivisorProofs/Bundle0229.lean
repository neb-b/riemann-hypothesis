module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0180
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0206
public import ReciprocityTheory.Chebotarev.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0200
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0002
public import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePointPropertyOfLeKerAppStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affinePointProperty_of_le_ker_app : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
     (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x) →
  (∀ (V : S.Opens) (hV : IsAffineOpen V), Represents (ptQ P V hV) (killIdeal (ptQ P V hV))) →
  ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S),
    (∀ (V : S.Opens) (hV : IsAffineOpen V), killIdeal (ptQ P V hV) ≤ RingHom.ker (x.app V).hom) → P R' x := by
  first | (exact @GlobalTheory.PtClosed.of_le_ker_app) | (exact GlobalTheory.PtClosed.of_le_ker_app) | (intros; apply GlobalTheory.PtClosed.of_le_ker_app  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomEqMulPowOfEqLocalizationAway
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem algHom_eq_mul_pow_of_eq_localizationAway :
    ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FiniteType R' A] (χ₁ χ₂ : A →ₐ[R'] S) (g : S),
    (∀ x, algebraMap S (Localization.Away g) (χ₁ x) = algebraMap S (Localization.Away g) (χ₂ x)) →
    ∃ N : ℕ, ∀ x, g ^ N * χ₁ x = g ^ N * χ₂ x := by
  intro R' A S _ _ _ _ _ _ χ₁ χ₂ g h
  have key : ∀ x, ∃ n : ℕ, g ^ n * χ₁ x = g ^ n * χ₂ x := by
    intro x
    obtain ⟨⟨c, hc⟩, hcx⟩ :=
      (IsLocalization.eq_iff_exists (Submonoid.powers g) (Localization.Away g)).1 (h x)
    obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 hc
    exact ⟨n, hcx⟩
  choose n hn using key
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R' A).FG)
  refine ⟨∑ x ∈ s, n x, fun x => ?_⟩
  set N := ∑ x ∈ s, n x
  have hx : x ∈ Algebra.adjoin R' (s : Set A) := by rw [hs]; exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem x hxs =>
    have hle : n x ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hxs
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, mul_assoc, hn x]
  | algebraMap r => rw [AlgHom.commutes, AlgHom.commutes]
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), mul_add, mul_add, hx, hy]
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul]
    calc g ^ N * (χ₁ x * χ₁ y) = χ₁ x * (g ^ N * χ₁ y) := by ring
      _ = χ₁ x * (g ^ N * χ₂ y) := by rw [hy]
      _ = (g ^ N * χ₁ x) * χ₂ y := by ring
      _ = (g ^ N * χ₂ x) * χ₂ y := by rw [hx]
      _ = g ^ N * (χ₂ x * χ₂ y) := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomQuotientSpanPowEqOfEtaleLowStatement
section
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algHom_quotient_span_pow_eq_of_etaleLow : ∀ (A R C : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing C] [Algebra R C] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    GlobalTheory.GoodEtale.EtaleLow A R C →
    ∀ (n : ℕ) (f f' : C →ₐ[R] R ⧸ Ideal.span {t} ^ n),
      (∀ c : C, f c - f' c ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {t} ^ n) t}) → f = f' := by
  first | (exact @GlobalTheory.GoodEtaleSection.algHom_quot_eq_of_etaleLow) | (exact GlobalTheory.GoodEtaleSection.algHom_quot_eq_of_etaleLow) | (intros; apply GlobalTheory.GoodEtaleSection.algHom_quot_eq_of_etaleLow  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraNormRatGaussianExtensionOfPair
section
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.GaussExt

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

theorem X_sq_add_one_ne_zero : (X ^ 2 + 1 : F[X]) ≠ 0 := Monic.ne_zero (by monicity!)

theorem natDegree_X_sq_add_one : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!

def basisOneI : Module.Basis (Fin 2) F (Ext F) :=
  (AdjoinRoot.powerBasis (X_sq_add_one_ne_zero F)).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis_dim, natDegree_X_sq_add_one]))

theorem basisOneI_apply (j : Fin 2) : basisOneI F j = ii F ^ (j : ℕ) := by
  simp [basisOneI, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen, ii]

theorem basisOneI_zero : basisOneI F 0 = 1 := by simp [basisOneI_apply]
theorem basisOneI_one : basisOneI F 1 = ii F := by simp [basisOneI_apply]

theorem gEmb_eq (a b : F) : gEmb F (a, b) = a • basisOneI F 0 + b • basisOneI F 1 := by
  simp [gEmb, basisOneI_zero, basisOneI_one, Algebra.smul_def]

theorem gEmb_mul_ii (a b : F) : gEmb F (a, b) * ii F = (-b) • basisOneI F 0 + a • basisOneI F 1 := by
  simp only [gEmb, basisOneI_zero, basisOneI_one, Algebra.smul_def, map_neg]
  linear_combination (algebraMap F (Ext F) b) * ii_sq F

theorem norm_gEmb_F (a b : F) : Algebra.norm F (gEmb F (a, b)) = a ^ 2 + b ^ 2 := by
  rw [Algebra.norm_eq_matrix_det (basisOneI F), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply']
  rw [basisOneI_zero, mul_one, basisOneI_one, gEmb_mul_ii, gEmb_eq]
  simp [Module.Basis.repr_self, Finsupp.single_apply]
  ring

theorem norm_gEmb (a b : F) :
    ((Algebra.norm ℚ (gEmb F (a, b)) : ℚ) : ℝ) = ∏ τ : F →+* ℝ, ((τ a) ^ 2 + (τ b) ^ 2) := by
  rw [← Algebra.norm_norm (S := F), norm_gEmb_F]
  have h := prod_emb (F := F) (a ^ 2 + b ^ 2)
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, ← h, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp

end GlobalTheory.GaussExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorOfDirectedEssentiallyEtaleUnion
section
open IsLocalRing

namespace GlobalTheory

set_option synthInstance.maxHeartbeats 400000 in
theorem ann_of_directed_essEtale : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] (C : ι → Subalgebra R B), Monotone C → (∀ b : B, ∃ i, b ∈ C i) → (∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (Q.comap ((C i).val : C i →ₐ[R] B))))) → ∀ i, ∀ c ∈ C i, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C i, s ∉ Q ∧ s * c = 0 := by
  intro R B _ _ _ Q _ ι _ _ C hmono hcov hess i c hc t ht htc
  obtain ⟨j, hj⟩ := hcov t
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have hck : c ∈ C k := hmono hik hc
  have htk : t ∈ C k := hmono hjk hj
  set Qi := Q.comap ((C i).val : C i →ₐ[R] B) with hQi
  set Qk := Q.comap ((C k).val : C k →ₐ[R] B) with hQk
  let f : C i →+* C k := (Subalgebra.inclusion (hmono hik)).toRingHom
  have hf : Qi = Qk.comap f := by ext x; rfl
  let g : Localization.AtPrime Qi →+* Localization.AtPrime Qk := Localization.localRingHom Qi Qk f hf
  letI : Algebra (Localization.AtPrime Qi) (Localization.AtPrime Qk) := g.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime Qi) (Localization.AtPrime Qk) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    change algebraMap R (Localization.AtPrime Qk) r = g (algebraMap R (Localization.AtPrime Qi) r)
    rw [IsScalarTower.algebraMap_apply R (C i) (Localization.AtPrime Qi), IsScalarTower.algebraMap_apply R (C k) (Localization.AtPrime Qk)]
    simp only [g, Localization.localRingHom_to_map]
    congr 1
  haveI : Module.Flat (Localization.AtPrime Qi) (Localization.AtPrime Qk) :=
    _root_.GlobalTheory.flat_of_essEtale R _ _ (hess i) (hess k)
  haveI : IsLocalHom (algebraMap (Localization.AtPrime Qi) (Localization.AtPrime Qk)) :=
    (inferInstance : IsLocalHom g)
  haveI : Module.FaithfullyFlat (Localization.AtPrime Qi) (Localization.AtPrime Qk) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj := RingHom.FaithfullyFlat.injective (RingHom.faithfullyFlat_algebraMap_iff.mpr this)
  have h0 : algebraMap (C k) (Localization.AtPrime Qk) ⟨c, hck⟩ = 0 := by
    rw [IsLocalization.map_eq_zero_iff Qk.primeCompl]
    refine ⟨⟨⟨t, htk⟩, ht⟩, ?_⟩
    exact Subtype.ext htc
  have h1 : algebraMap (C i) (Localization.AtPrime Qi) ⟨c, hc⟩ = 0 := by
    apply hinj
    rw [map_zero]
    change g _ = 0
    simp only [g, Localization.localRingHom_to_map]
    exact h0
  rw [IsLocalization.map_eq_zero_iff Qi.primeCompl] at h1
  obtain ⟨⟨⟨s, hs⟩, hsQ⟩, hsc⟩ := h1
  exact ⟨s, hs, hsQ, congrArg Subtype.val hsc⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorQuotientSmulTopOfFree
section
open IsLocalRing RingTheory.Sequence Pointwise

namespace GlobalTheory.AnnRegSeq

theorem free_of_maximalIdeal_eq_bot {B M : Type} [CommRing B] [IsLocalRing B] [AddCommGroup M]
    [Module B M] (hm : maximalIdeal B = ⊥) : Module.Free B M := by
  have hF : IsField B := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm
  letI := hF.toField
  exact Module.Free.of_divisionRing B M

theorem maximalIdeal_eq_bot_of_le_sq {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (h : maximalIdeal B ≤ maximalIdeal B ^ 2) : maximalIdeal B = ⊥ :=
  Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal B) (maximalIdeal B)
    (maximalIdeal B).fg_of_isNoetherianRing (by rwa [smul_eq_mul, ← pow_two])
    (maximalIdeal_le_jacobson ⊥)

theorem exists_isSMulRegular_notMem_sq {B M : Type} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (hass : maximalIdeal B ∉ associatedPrimes B M) (hsq : ¬ maximalIdeal B ≤ maximalIdeal B ^ 2) :
    ∃ x ∈ maximalIdeal B, x ∉ maximalIdeal B ^ 2 ∧ IsSMulRegular M x := by
  by_contra hcon
  push_neg at hcon
  have hsub : ((maximalIdeal B : Ideal B) : Set B) ⊆
      ⋃ p ∈ insert (maximalIdeal B ^ 2) (associatedPrimes B M), (id p : Set B) := by
    intro z hz
    rw [Set.biUnion_insert]
    by_cases h2 : z ∈ maximalIdeal B ^ 2
    · exact Or.inl h2
    · right
      have : z ∈ ({r : B | IsSMulRegular M r}ᶜ) := hcon z hz h2
      rwa [← biUnion_associatedPrimes_eq_compl_regular B M] at this
  obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime_finite ((associatedPrimes.finite B M).insert _)
    (f := id) (maximalIdeal B ^ 2) (maximalIdeal B ^ 2) (fun i hi h1 _ => by
      rcases hi with rfl | hi
      · exact absurd rfl h1
      · exact hi.isPrime)).mp hsub
  rcases hp with rfl | hp
  · exact hsq hle
  · have : p = maximalIdeal B := le_antisymm (le_maximalIdeal hp.isPrime.ne_top) hle
    exact hass (this ▸ hp)

theorem free_of_free_quotient {B M : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [AddCommGroup M] [Module B M] [Module.Finite B M] {x : B} (hx : x ∈ maximalIdeal B)
    (reg : IsSMulRegular M x)
    [Module.Free (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M))] :
    Module.Free B M := by
  set I : Ideal B := Ideal.span {x} with hI
  set P : Submodule B M := I • ⊤ with hP
  have hIj : I ≤ (⊥ : Ideal B).jacobson := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact maximalIdeal_le_jacobson _ hx
  haveI : IsLocalRing (B ⧸ I) :=
    ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hx
  haveI : Module.Finite (B ⧸ I) (M ⧸ P) := Module.Finite.of_restrictScalars_finite B _ _
  let b := Module.finBasis (B ⧸ I) (M ⧸ P)
  set r := Module.finrank (B ⧸ I) (M ⧸ P)
  choose v hv using fun i => Submodule.Quotient.mk_surjective P (b i)
  let φ : (Fin r → B) →ₗ[B] M := Fintype.linearCombination B v
  have hφ : ∀ c, φ c = ∑ i, c i • v i := fun c => by simp [φ, Fintype.linearCombination_apply]
  have hmk : ∀ c : Fin r → B, (Submodule.Quotient.mk (φ c) : M ⧸ P) =
      ∑ i, Ideal.Quotient.mk I (c i) • b i := by
    intro c
    rw [hφ]
    change Submodule.mkQ P (∑ i, c i • v i) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, hv i, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have hsurj : LinearMap.range φ = ⊤ := by
    refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hIj ?_)
    intro m _
    choose c' hc' using fun i => Ideal.Quotient.mk_surjective (b.repr (Submodule.Quotient.mk m) i)
    have h1 : (Submodule.Quotient.mk (φ c') : M ⧸ P) = Submodule.Quotient.mk m := by
      rw [hmk]
      simp only [hc']
      exact b.sum_repr _
    rw [Submodule.Quotient.eq] at h1
    have h2 : m = φ c' - (φ c' - m) := by abel
    rw [h2]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨c', rfl⟩) (Submodule.mem_sup_right h1)
  have hker : LinearMap.ker φ = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I _ (IsNoetherian.noetherian _) ?_ hIj
    intro k hk
    rw [LinearMap.mem_ker] at hk
    have h0 : ∑ i, Ideal.Quotient.mk I (k i) • b i = 0 := by
      rw [← hmk, hk]
      rfl
    have hki : ∀ i, k i ∈ I := fun i =>
      Ideal.Quotient.eq_zero_iff_mem.mp ((Fintype.linearIndependent_iff.mp b.linearIndependent) _ h0 i)
    choose k' hk' using fun i => Ideal.mem_span_singleton'.mp (hki i)
    have hkx : k = x • k' := by
      ext i
      simp [← hk' i, mul_comm]
    have hk'ker : k' ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker]
      apply reg
      show x • φ k' = x • 0
      rw [smul_zero, ← map_smul, ← hkx, hk]
    rw [hkx]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hk'ker
  exact Module.Free.of_equiv (LinearEquiv.ofBijective φ
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hsurj⟩)

theorem free_of_modDepthGE (n : ℕ) : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (M : Type) [AddCommGroup M] [Module B M] [Module.Finite B M],
    ReciprocityTheory.CA.ModDepthGE B M n → (maximalIdeal B).spanFinrank ≤ n → Module.Free B M := by
  induction n with
  | zero =>
    intro B _ _ _ M _ _ _ _ hsp
    exact free_of_maximalIdeal_eq_bot ((Submodule.spanFinrank_eq_zero_iff_eq_bot
      (maximalIdeal B).fg_of_isNoetherianRing).mp (by omega))
  | succ n ih =>
    intro B _ _ _ M _ _ _ hd hsp
    by_cases hsq : maximalIdeal B ≤ maximalIdeal B ^ 2
    · exact free_of_maximalIdeal_eq_bot (maximalIdeal_eq_bot_of_le_sq hsq)
    obtain ⟨rs, hlen, hmem, hreg⟩ := hd
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    have hy : y ∈ maximalIdeal B := hmem y (by simp)
    have hass := ReciprocityTheory.CA.max_not_mem_ass_of_reg hy ((isRegular_cons_iff M y ys).mp hreg).1
    obtain ⟨x, hx, hx2, hxreg⟩ := exists_isSMulRegular_notMem_sq hass hsq
    have hd' := ReciprocityTheory.CA.ModDepthGE.quotSMulTop hx hxreg ⟨y :: ys, hlen, hmem, hreg⟩
    haveI : IsLocalRing (B ⧸ Ideal.span {x}) :=
      ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hx
    haveI : Module.Finite (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) :=
      Module.Finite.of_restrictScalars_finite B _ _
    have hsp' : (maximalIdeal (B ⧸ Ideal.span {x})).spanFinrank ≤ n := by
      have h1 :=
        ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le B hx hx2
      rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at h1
      omega
    have hd'' : ReciprocityTheory.CA.ModDepthGE (B ⧸ Ideal.span {x})
        (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) n := by
      obtain ⟨zs, hzl, hzm, hzr⟩ := hd'
      let e : QuotSMulTop x M ≃ₗ[B] M ⧸ Ideal.span {x} • (⊤ : Submodule B M) :=
        Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul x ⊤).symm
      refine ⟨zs.map (Ideal.Quotient.mk _), by simp [hzl], ?_, ?_⟩
      · intro r hr
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hr
        exact ReciprocityTheory.CA.mk_mem_maximalIdeal_quot _ (hzm z hz)
      · rw [← Ideal.Quotient.algebraMap_eq]
        exact (ReciprocityTheory.CA.isRegular_map_algebraMap_iff' zs).mpr ((e.isRegular_congr zs).mp hzr)
    haveI := ih (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) hd'' hsp'
    exact free_of_free_quotient hx hxreg

end GlobalTheory.AnnRegSeq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapEqOfRed
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue.Red

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]; exact Spec.map_id _

theorem away_ext {R T : Type} [CommRing R] [CommRing T] (a : R) (φ ψ : Localization.Away a →+* T)
    (h : φ.comp (algebraMap R _) = ψ.comp (algebraMap R _)) : φ = ψ :=
  IsLocalization.ringHom_ext (Submonoid.powers a) h

theorem isUnit_of_away {R T : Type} [CommRing R] [CommRing T] [Algebra R T] (a : R)
    (ρ : Localization.Away a →+* T) (hρ : ρ.comp (algebraMap R _) = algebraMap R T) :
    IsUnit (algebraMap R T a) := by
  rw [← hρ]; exact (IsLocalization.Away.algebraMap_isUnit a).map ρ

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

abbrev redI (π : R →+* R₀) (S : Type) [CommRing S] [Algebra R S] : Ideal S :=
  (RingHom.ker π).map (algebraMap R S)

def redPsi (π : R →+* R₀) (hπ : Function.Surjective π) (S : Type) [CommRing S] [Algebra R S] :
    R₀ →+* S ⧸ redI π S :=
  π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
    ⟨(Ideal.Quotient.mk (redI π S)).comp (algebraMap R S), fun x hx => by
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hx⟩

theorem redPsi_comp (π : R →+* R₀) (hπ : Function.Surjective π) (S : Type) [CommRing S]
    [Algebra R S] : (redPsi π hπ S).comp π = (Ideal.Quotient.mk (redI π S)).comp (algebraMap R S) :=
  RingHom.liftOfRightInverse_comp _ _ _ _

theorem ker_mk_sq (π : R →+* R₀) (h : RingHom.ker π ^ 2 = ⊥) (S : Type) [CommRing S]
    [Algebra R S] : RingHom.ker (Ideal.Quotient.mk (redI π S)) ^ 2 = ⊥ := by
  rw [Ideal.mk_ker, ← Ideal.map_pow, h, Ideal.map_bot]

def IsRed (π : R →+* R₀) (hπ : Function.Surjective π) {Y : Scheme.{0}} (g₀ : Sp R₀ ⟶ Y)
    (S : Type) [CommRing S] [Algebra R S] (u : Sp S ⟶ Y) : Prop :=
  spMap (Ideal.Quotient.mk (redI π S)) ≫ u = spMap (redPsi π hπ S) ≫ g₀

theorem IsRed.eq {π : R →+* R₀} {hπ : Function.Surjective π} {Y : Scheme.{0}} {g₀ : Sp R₀ ⟶ Y}
    {S : Type} [CommRing S] [Algebra R S] {u v : Sp S ⟶ Y} (hu : IsRed π hπ g₀ S u)
    (hv : IsRed π hπ g₀ S v) :
    spMap (Ideal.Quotient.mk (redI π S)) ≫ u = spMap (Ideal.Quotient.mk (redI π S)) ≫ v :=
  hu.trans hv.symm

theorem isRed_of_away (π : R →+* R₀) (hπ : Function.Surjective π) {Y : Scheme.{0}}
    (g₀ : Sp R₀ ⟶ Y) (a : R) (u : Sp (Localization.Away a) ⟶ Y)
    (hu : spMap (Localization.awayMap π a) ≫ u =
      spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀)
    (S : Type) [CommRing S] [Algebra R S] (ρ : Localization.Away a →+* S)
    (hρ : ρ.comp (algebraMap R _) = algebraMap R S) : IsRed π hπ g₀ S (spMap ρ ≫ u) := by
  have hunit : IsUnit (redPsi π hπ S (π a)) := by
    have e : redPsi π hπ S (π a) = Ideal.Quotient.mk (redI π S) (algebraMap R S a) := by
      rw [← RingHom.comp_apply (redPsi π hπ S) π, redPsi_comp, RingHom.comp_apply]
    rw [e]; exact (isUnit_of_away a ρ hρ).map _
  let lam := IsLocalization.Away.lift (S := Localization.Away (π a)) (π a) hunit
  have key : (Ideal.Quotient.mk (redI π S)).comp ρ = lam.comp (Localization.awayMap π a) := by
    apply away_ext a
    rw [RingHom.comp_assoc, hρ, RingHom.comp_assoc]
    have e1 : (Localization.awayMap π a).comp (algebraMap R (Localization.Away a)) =
        (algebraMap R₀ (Localization.Away (π a))).comp π := IsLocalization.map_comp _
    rw [e1, ← RingHom.comp_assoc, IsLocalization.Away.lift_comp, redPsi_comp]
  unfold IsRed
  rw [← Category.assoc, ← spMap_comp, key, spMap_comp, Category.assoc, hu, ← Category.assoc,
    ← spMap_comp, IsLocalization.Away.lift_comp]

theorem isRed_self (π : R →+* R₀) (hπ : Function.Surjective π) {Y : Scheme.{0}}
    (g₀ : Sp R₀ ⟶ Y) (a : R) (u : Sp (Localization.Away a) ⟶ Y)
    (hu : spMap (Localization.awayMap π a) ≫ u =
      spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀) :
    IsRed π hπ g₀ (Localization.Away a) u := by
  have := isRed_of_away π hπ g₀ a u hu (Localization.Away a) (RingHom.id _) rfl
  rwa [spMap_id, Category.id_comp] at this

theorem isRed_comp (π : R →+* R₀) (hπ : Function.Surjective π) {Y : Scheme.{0}}
    (g₀ : Sp R₀ ⟶ Y) {S S' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
    (σ : S →+* S') (hσ : σ.comp (algebraMap R S) = algebraMap R S') {u : Sp S ⟶ Y}
    (hu : IsRed π hπ g₀ S u) : IsRed π hπ g₀ S' (spMap σ ≫ u) := by
  have hle : redI π S ≤ (redI π S').comap σ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap, ← RingHom.comp_apply σ, hσ]
    exact Ideal.mem_map_of_mem _ hx
  have h1 : (Ideal.Quotient.mk (redI π S')).comp σ =
      (Ideal.quotientMap (redI π S') σ hle).comp (Ideal.Quotient.mk (redI π S)) :=
    (Ideal.quotientMap_comp_mk hle).symm
  have h2 : (Ideal.quotientMap (redI π S') σ hle).comp (redPsi π hπ S) = redPsi π hπ S' := by
    apply RingHom.ext; intro y; obtain ⟨x, rfl⟩ := hπ y
    rw [RingHom.comp_apply, ← RingHom.comp_apply (redPsi π hπ S), redPsi_comp,
      ← RingHom.comp_apply (redPsi π hπ S'), redPsi_comp, RingHom.comp_apply, RingHom.comp_apply,
      Ideal.quotientMap_mk, ← RingHom.comp_apply σ, hσ]
  unfold IsRed at *
  rw [← Category.assoc, ← spMap_comp, h1, spMap_comp, Category.assoc, hu, ← Category.assoc,
    ← spMap_comp, h2]

theorem awayMap_eq_of_red (π : R →+* R₀) {Y : Scheme.{0}} (a : R)
    (u v : Sp (Localization.Away a) ⟶ Y)
    (h : spMap (Ideal.Quotient.mk (redI π (Localization.Away a))) ≫ u =
      spMap (Ideal.Quotient.mk (redI π (Localization.Away a))) ≫ v) :
    spMap (Localization.awayMap π a) ≫ u = spMap (Localization.awayMap π a) ≫ v := by
  have H : ∀ x ∈ redI π (Localization.Away a), Localization.awayMap π a x = 0 := by
    intro x hx
    have hle : redI π (Localization.Away a) ≤ RingHom.ker (Localization.awayMap π a) := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply,
        show (Localization.awayMap π a).comp (algebraMap R (Localization.Away a)) =
          (algebraMap R₀ (Localization.Away (π a))).comp π from IsLocalization.map_comp _,
        RingHom.comp_apply, RingHom.mem_ker.1 hy, map_zero]
    exact hle hx
  have e : Localization.awayMap π a =
      (Ideal.Quotient.lift _ (Localization.awayMap π a) H).comp (Ideal.Quotient.mk _) := by
    ext x; simp
  rw [e, spMap_comp, Category.assoc, Category.assoc, h]

end GlobalTheory.SecGlue.Red
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisQuotientTensorBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_quotient_tensor_base_change : ∀ (A B C R : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] [CommRing R] [Algebra A R] {r : ℕ} (v : Fin r → B) (J : Ideal (C ⊗[A] B)) (ψ : C →ₐ[A] R), LinearIndependent C (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k)) → Submodule.span C (Set.range (fun k => Ideal.Quotient.mk J ((1 : C) ⊗ₜ[A] v k))) = ⊤ → LinearIndependent R (fun k => Ideal.Quotient.mk (J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B))) ((1 : R) ⊗ₜ[A] v k)) ∧ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (J.map (Algebra.TensorProduct.map ψ (AlgHom.id A B))) ((1 : R) ⊗ₜ[A] v k))) = ⊤ := by
  first | (exact @GlobalTheory.quotient_basis_baseChange) | (exact GlobalTheory.quotient_basis_baseChange) | (intros; apply GlobalTheory.quotient_basis_baseChange  <;> assumption)
end

