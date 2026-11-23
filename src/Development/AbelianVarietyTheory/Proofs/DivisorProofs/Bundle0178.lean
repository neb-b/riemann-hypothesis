module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarRamificationIdxEqOne
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

open IsLocalRing in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
open Polynomial in
private lemma maximalIdeal_eq_span_of_kummer_tower (A W : Type) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing W] [IsLocalRing W] (Φ : A →+* W) (ϖ : A) (u : Aˣ) (m k : ℕ)
    (hϖ : Irreducible ϖ) (hm : IsUnit (m : A)) (hk : 0 < k) (y τ : W) (hy : y ^ m = Φ u)
    (hτ : τ ^ k = Φ ϖ * y) (hτm : τ ∈ maximalIdeal W) (hτnz : τ ∈ nonZeroDivisors W)
    (hfrac : ∀ w : W, ∃ x z, x ∈ Subring.closure (Set.range Φ ∪ {τ}) ∧
      z ∈ Subring.closure (Set.range Φ ∪ {τ}) ∧ z ∈ nonZeroDivisors W ∧ z * w = x) :
    maximalIdeal W = Ideal.span {τ} := by
  obtain ⟨gB, hgB_of, hgB_root⟩ : ∃ gB : AdjoinRoot (X ^ m - C (u : A)) →+* W,
      (∀ a, gB (AdjoinRoot.of _ a) = Φ a) ∧ gB (AdjoinRoot.root _) = y :=
    ⟨AdjoinRoot.lift Φ y (by simp [hy]), fun a => AdjoinRoot.lift_of _, AdjoinRoot.lift_root _⟩
  obtain ⟨g, hg_of, hg_root⟩ : ∃ g : AdjoinRoot (X ^ k - C (AdjoinRoot.of (X ^ m - C (u : A)) ϖ *
        AdjoinRoot.root (X ^ m - C (u : A)))) →+* W,
      (∀ b, g (AdjoinRoot.of _ b) = gB b) ∧ g (AdjoinRoot.root _) = τ :=
    ⟨AdjoinRoot.lift gB τ (by simp [hgB_of, hgB_root, hτ]), fun b => AdjoinRoot.lift_of _,
      AdjoinRoot.lift_root _⟩
  haveI hn : (Ideal.comap g (maximalIdeal W)).IsPrime := Ideal.comap_isPrime g (maximalIdeal W)
  have hTn : AdjoinRoot.root (X ^ k - C (AdjoinRoot.of (X ^ m - C (u : A)) ϖ *
      AdjoinRoot.root (X ^ m - C (u : A)))) ∈ Ideal.comap g (maximalIdeal W) := by
    rw [Ideal.mem_comap, hg_root]
    exact hτm
  have hmaxV := _root_.GlobalTheory.maximalIdeal_localization_eq_span_of_reduced_artinian _ _ (_root_.GlobalTheory.kummerUnit_quotRoot_isReduced A ϖ u m k hϖ hm hk)
    (_root_.GlobalTheory.T.isArtinianRing_kummerAdjoinRoot_quotient_root A ϖ u m k hϖ hm hk) _ hTn
  haveI : IsNoetherianRing (AdjoinRoot (X ^ k - C (AdjoinRoot.of (X ^ m - C (u : A)) ϖ *
      AdjoinRoot.root (X ^ m - C (u : A))))) := inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime (Ideal.comap g (maximalIdeal W))) :=
    IsLocalization.isNoetherianRing (Ideal.comap g (maximalIdeal W)).primeCompl _ inferInstance
  have hunit : ∀ s : (Ideal.comap g (maximalIdeal W)).primeCompl, IsUnit (g s) := by
    intro s
    by_contra h
    exact s.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hlift := fun r => IsLocalization.lift_eq (M := (Ideal.comap g (maximalIdeal W)).primeCompl)
    (S := Localization.AtPrime (Ideal.comap g (maximalIdeal W))) hunit r
  obtain ⟨φ, hφ⟩ : ∃ φ : Localization.AtPrime (Ideal.comap g (maximalIdeal W)) →+* W,
      ∀ r, φ (algebraMap _ _ r) = g r := ⟨IsLocalization.lift hunit, hlift⟩
  have key := _root_.GlobalTheory.maximalIdeal_eq_span_map_of_fractions (Localization.AtPrime (Ideal.comap g (maximalIdeal W))) W φ _ hmaxV (by rw [hφ, hg_root]; exact hτm)
    (by rw [hφ, hg_root]; exact hτnz) ?_
  · rw [key, hφ, hg_root]
  intro w
  obtain ⟨x, z, hx, hz, hznz, hzw⟩ := hfrac w
  have hle : Subring.closure (Set.range Φ ∪ {τ}) ≤ φ.range := by
    rw [Subring.closure_le]
    refine Set.union_subset ?_ ?_
    · rintro _ ⟨a, rfl⟩
      exact ⟨algebraMap _ _ (AdjoinRoot.of _ (AdjoinRoot.of _ a)), by rw [hφ, hg_of, hgB_of]⟩
    · rintro _ rfl
      exact ⟨algebraMap _ _ (AdjoinRoot.root _), by rw [hφ, hg_root]⟩
  obtain ⟨x', rfl⟩ := hle hx
  obtain ⟨z', rfl⟩ := hle hz
  exact ⟨x', z', hznz, hzw⟩


open IsLocalRing in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.abhyankar_ramificationIdx_eq_one : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ e) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    Q.ramificationIdx D = 1 := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ ⟨ψ⟩ hπ he hdiv _ _ _ Q _
  haveI : Q.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  haveI : IsDedekindDomain (integralClosure S L) := integralClosure.isDedekindDomain S K L
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      simp at he
    · exact h
  obtain ⟨ht, htnz⟩ := _root_.GlobalTheory.AbhyankarRootUnit.root_mem_maximalIdeal_and_mem_nonZeroDivisors S K L π e D ψ hπ he0 Q
  have hte : (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π))) ^ e = algebraMap S D π := by
    apply ψ.injective
    rw [map_pow, AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
    have h := AdjoinRoot.eval₂_root (Polynomial.X ^ e - Polynomial.C π)
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
    rw [sub_eq_zero.1 h]
    rfl
  have htQ : algebraMap D (integralClosure D (TensorProduct S D L))
      (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π))) ∈ Q := by
    rw [IsScalarTower.algebraMap_apply D (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)] at ht
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).1 ht
  have hπO : algebraMap S (integralClosure S L) π ≠ 0 := by
    intro h
    have h1 : algebraMap S L π = 0 := by
      rw [IsScalarTower.algebraMap_apply S (integralClosure S L) L, h, map_zero]
    rw [IsScalarTower.algebraMap_apply S K L, map_eq_zero_iff _ (algebraMap K L).injective,
      IsFractionRing.to_map_eq_zero_iff] at h1
    exact hπ.ne_zero h1
  have hπP : algebraMap S (integralClosure S L) π ∈
      Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q := by
    rw [Ideal.mem_comap]
    have hpow : _root_.GlobalTheory.AbhyankarLocal.toNorm S L D (algebraMap S (integralClosure S L) π) =
        (algebraMap D (integralClosure D (TensorProduct S D L))
          (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π)))) ^ e := by
      apply Subtype.ext
      rw [_root_.GlobalTheory.AbhyankarLocal.toNorm_coe, ← map_pow, hte]
      change (1 : D) ⊗ₜ[S] (algebraMap S L π) = algebraMap D (TensorProduct S D L) (algebraMap S D π)
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one π,
        Algebra.algebraMap_eq_smul_one π, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.algebraMap_self, RingHom.id_apply]
    rw [hpow]
    exact Ideal.pow_mem_of_mem Q htQ e he0
  haveI hPmax : (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance ?_
    intro h
    rw [h] at hπP
    exact hπO hπP
  obtain ⟨ϖ, hϖ, u, hu⟩ := _root_.GlobalTheory.pi_eq_pow_ramificationIdx_mul_unit S K L π e D
    (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q) hπ hπP
  obtain ⟨k, hk⟩ := hdiv _ hPmax
  obtain ⟨y, hym, hyk⟩ := _root_.GlobalTheory.AbhyankarLocal.exists_kummer_element S K L π e D ψ hπ he0 Q _ k ϖ u hk.symm hu
  have hP0 : Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q ≠ ⊥ := by
    intro h
    rw [h] at hπP
    exact hπO hπP
  haveI : IsDiscreteValuationRing
      (Localization.AtPrime (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q)) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure S L) hP0 _
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      omega
    · exact h
  have hmu : IsUnit (((Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q).ramificationIdx S : ℕ) :
      Localization.AtPrime (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q)) := by
    have h := he.map (algebraMap S
      (Localization.AtPrime (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q)))
    rw [map_natCast, hk, Nat.cast_mul] at h
    exact isUnit_of_mul_isUnit_left h
  have hmax := maximalIdeal_eq_span_of_kummer_tower _ (Localization.AtPrime Q)
    (_root_.GlobalTheory.AbhyankarLocal.locHom Q) ϖ u _ k hϖ hmu hk0 y _ hym hyk ht htnz
    (_root_.GlobalTheory.AbhyankarLocal.exists_frac_closure S K L π e D ψ hπ he0 Q)
  have hunder : Ideal.under D Q = maximalIdeal D := by
    refine IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance ?_)
    intro h
    have h1 : ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π)) ∈ Ideal.under D Q := htQ
    rw [h, Ideal.mem_bot] at h1
    rw [h1, map_zero] at htnz
    exact zero_notMem_nonZeroDivisors htnz
  have hmapmax : Ideal.map (algebraMap D (Localization.AtPrime Q)) (Ideal.under D Q) =
      maximalIdeal (Localization.AtPrime Q) := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro d hd
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply D (integralClosure D (TensorProduct S D L))
        (Localization.AtPrime Q)]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).2 hd
    · rw [hmax, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ htQ
  rw [Ideal.ramificationIdx_def, hmapmax,
    Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.2 (IsLocalRing.maximalIdeal.isMaximal _).out)]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqProd
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwoExp

variable {F : Type} [Field F] [NumberField F]

theorem phi_zero (w : ℂ) : phi 0 w = w⁻¹ ^ 2 := by
  simp [phi]

theorem hTrans_zero_neg (ν y : ℝ) : hTrans 0 ν (-y) = hTrans 0 (-ν) y := by
  unfold hTrans
  conv_lhs => rw [← MeasureTheory.integral_neg_eq_self]
  congr 1; funext t
  simp only [phi_zero, ofReal_neg]
  congr 1
  · rw [show -(t : ℂ) + -(y : ℂ) * I = -((t : ℂ) + (y : ℂ) * I) by ring, inv_neg, neg_sq]
  · congr 1; ring

theorem emb_nonempty [IsTotallyReal F] : Nonempty (Emb F) := by
  have : Nonempty (F →+* ℂ) := by
    rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]
    exact Module.finrank_pos
  obtain ⟨φ⟩ := this
  exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩

theorem abs_norm_eq_prod [IsTotallyReal F] (ν : F) :
    ((|(Algebra.norm ℚ ν : ℝ)| : ℝ) : ℂ) = ∏ τ : Emb F, ((|τ ν| : ℝ) : ℂ) := by
  have h := prod_emb ν
  have h' : ((Algebra.norm ℚ ν : ℚ) : ℝ) = ∏ τ : Emb F, τ ν := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_prod, h]; push_cast; rfl
  rw [h', Finset.abs_prod, Complex.ofReal_prod]

end GlobalTheory.HeckeTwoExp

namespace GlobalTheory.HeckeTwoExp

variable {F : Type} [Field F] [NumberField F]

def toQ (𝔞 𝔟 : Frac F) : (Σ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
    {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)}) → Quotient (qRel 𝔞 𝔟) :=
  fun s => Quotient.mk _ ⟨(s.2.1.1, s.1.out.1), s.2.1.2.1, s.1.out.2.1, s.2.2⟩

theorem toQ_injective (𝔞 𝔟 : Frac F) : Function.Injective (toQ 𝔞 𝔟) := by
  rintro ⟨c, ν⟩ ⟨c', ν'⟩ h
  obtain ⟨ε, h1, h2⟩ := Quotient.exact h
  dsimp only at h1 h2
  have hc : c = c' := by
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound ⟨ε, h2⟩
  subst hc
  have hne : c.out.1 ≠ 0 := c.out.2.2
  have hε : ((ε : 𝓞 F) : F) = 1 := by
    have h3 : (((ε : 𝓞 F) : F) - 1) * c.out.1 = 0 := by linear_combination -h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hne)
  have hε' : (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
    have := unit_inv_mul ε; rw [hε, mul_one] at this; exact this
  rw [hε', one_mul] at h1
  have : ν = ν' := Subtype.ext (Subtype.ext h1.symm)
  subst this
  rfl

theorem toQ_surjective [IsTotallyReal F] (𝔞 𝔟 : Frac F) : Function.Surjective (toQ 𝔞 𝔟) := by
  intro q
  induction q using Quotient.inductionOn with
  | h p => ?_
  obtain ⟨⟨ν, b⟩, hν, hb, hpos⟩ := p
  obtain ⟨τ₀⟩ := emb_nonempty (F := F)
  have hνb : ν * b ≠ 0 := by
    intro h0; have := hpos τ₀; rw [h0, map_zero] at this; exact lt_irrefl _ this
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hνb
  have hν0 : ν ≠ 0 := left_ne_zero_of_mul hνb
  set c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) := Quotient.mk _ ⟨b, hb, hb0⟩ with hcdef
  obtain ⟨ε, hε⟩ := Quotient.exact (Quotient.out_eq c : Quotient.mk _ c.out = Quotient.mk _ ⟨b, hb, hb0⟩)
  dsimp only at hε
  have hmem : ((ε : 𝓞 F) : F) * ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by
    have := Submodule.smul_mem (𝔞 : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule (ε : 𝓞 F) hν
    rw [Algebra.smul_def] at this
    exact this
  have hne : ((ε : 𝓞 F) : F) * ν ≠ 0 := by
    refine mul_ne_zero ?_ hν0
    intro h0
    have := unit_inv_mul ε; rw [h0, mul_zero] at this; exact zero_ne_one this
  have hprod : ((ε : 𝓞 F) : F) * ν * c.out.1 = ν * b := by rw [hε]; ring
  refine ⟨⟨c, ⟨⟨((ε : 𝓞 F) : F) * ν, hmem, hne⟩, fun τ => by rw [hprod]; exact hpos τ⟩⟩, ?_⟩
  apply Quotient.sound
  refine ⟨ε, ?_, hε⟩
  show ν = _ * (((ε : 𝓞 F) : F) * ν)
  rw [← mul_assoc, unit_inv_mul, one_mul]

theorem tsum_qClass_eq [IsTotallyReal F] (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (hS : Summable (qClass 𝔞 𝔟 2 z)) :
    ∑' c, qClass 𝔞 𝔟 2 z c = ∑' c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F),
        if ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1) then qTerm 𝔞 2 z (ν.1, c.out.1) else 0 := by
  set e := Equiv.ofBijective (toQ 𝔞 𝔟) ⟨toQ_injective 𝔞 𝔟, toQ_surjective 𝔞 𝔟⟩ with he
  have hS' : Summable (qClass 𝔞 𝔟 2 z ∘ e) := e.summable_iff.2 hS
  have h1 : ∑' c, qClass 𝔞 𝔟 2 z c = ∑' p, qClass 𝔞 𝔟 2 z (e p) := (e.tsum_eq _).symm
  have h2 : ∑' p, qClass 𝔞 𝔟 2 z (e p) = ∑' c, ∑' ν, qClass 𝔞 𝔟 2 z (e ⟨c, ν⟩) := hS'.tsum_sigma
  rw [h1, h2]
  refine tsum_congr fun c => ?_
  have h3 := tsum_subtype {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) | ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)}
    (fun ν => qTerm 𝔞 2 z (ν.1, c.out.1))
  have h4 : ∀ ν : {ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) // ∀ τ : Emb F, 0 < τ (ν.1 * c.out.1)},
      qClass 𝔞 𝔟 2 z (e ⟨c, ν⟩) = qTerm 𝔞 2 z (ν.1.1, c.out.1) := fun ν => by
    rw [he]; exact qClass_mk 𝔞 𝔟 2 z _
  rw [tsum_congr h4]
  refine h3.trans (tsum_congr fun ν => ?_)
  rw [Set.indicator_apply]
  rfl

end GlobalTheory.HeckeTwoExp

namespace GlobalTheory.HeckeTwoExp

variable {F : Type} [Field F] [NumberField F]

theorem kFac_zero_mul : kFac (F := F) 0 * (-4 * (Real.pi : ℂ) ^ 2) ^ Fintype.card (Emb F) = 1 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * (-4 * (Real.pi : ℂ) ^ 2) = 1 := by
    rw [inv_pow, mul_pow, mul_pow, I_sq]
    field_simp
    ring
  unfold kFac
  simp only [mul_zero, cpow_zero, mul_one, Finset.prod_const, Finset.card_univ]
  rw [← mul_pow, h1, one_pow]

theorem dF_pos : 0 < dF F := abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero F))

theorem nrm_ne_zero (𝔞 : Frac F) : nrm 𝔞 ≠ 0 := by
  unfold nrm
  rw [Rat.cast_ne_zero, Ne, FractionalIdeal.absNorm_eq_zero_iff]
  exact 𝔞.ne_zero

end GlobalTheory.HeckeTwoExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceClosedUnderConjReflection
section
namespace AdelicReflection
section

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicReflect

def conjNeg {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  let g : SchwartzMap E ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (ContinuousLinearEquiv.neg ℝ) f
  { toFun := fun y => starRingEnd ℂ (g y)
    smooth' := Complex.conjCLE.contDiff.comp g.smooth'
    decay' := by
      intro k n
      obtain ⟨C, hC⟩ := g.decay' k n
      refine ⟨C, fun x => ?_⟩
      have e : (fun y => starRingEnd ℂ (g y)) = Complex.conjLIE ∘ g := rfl
      rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
      exact hC x }

theorem conjNeg_mem_SB {X : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X] {g : X → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB X) : (fun y => starRingEnd ℂ (g (-y))) ∈ GlobalTheory.WeilM.SB X := by
  obtain ⟨hlc, hcs⟩ := hg
  refine ⟨(hlc.comp_continuous continuous_neg).comp (starRingEnd ℂ), ?_⟩
  exact (hcs.comp_homeomorph (Homeomorph.neg X)).comp_left (g := starRingEnd ℂ) (map_zero _)

theorem conj_pureA_neg (F : Type) [Field F] [NumberField F] {κ : Type}
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → AdeleRing (𝓞 F) F) :
    starRingEnd ℂ (GlobalTheory.WeilM.pureA F f g (-x)) =
      GlobalTheory.WeilM.pureA F (fun y => starRingEnd ℂ (f (-y))) (fun y => starRingEnd ℂ (g (-y))) x := by
  simp only [GlobalTheory.WeilM.pureA, map_mul]
  congr 3
  funext i
  rw [Pi.neg_apply, Pi.neg_apply, ← map_neg]
  rfl

theorem schA_conj_neg : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ κ _ φ hφ
  unfold GlobalTheory.WeilM.schA at hφ ⊢
  induction hφ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    refine Submodule.subset_span ⟨conjNeg f, fun y => starRingEnd ℂ (g (-y)), conjNeg_mem_SB hg, ?_⟩
    funext x
    rw [conj_pureA_neg]
    congr 1
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext x
    simp
  | add a b _ _ ha hb =>
    convert Submodule.add_mem _ ha hb using 1
    funext x
    simp only [Pi.add_apply, map_add]
  | smul c a _ ha =>
    convert Submodule.smul_mem _ (starRingEnd ℂ c) ha using 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]

end GlobalTheory.CompanionTheory.AdelicReflect

end

end

end AdelicReflection
section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ κ _ φ hφ
  exact AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect.schA_conj_neg F κ φ hφ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinConjInPar
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem adjoin_conj_inPar : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] (a n : ℕ) (γ y₀ : GL (Fin n) F) (δ : GL (Fin n) F'), (δ : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} → InPar a (y₀⁻¹ * γ * y₀) → InPar a ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) := by
  intro F F' _ _ _ a n γ y₀ δ hδ hγ

  let T : Subalgebra F' (Matrix (Fin n) (Fin n) F') :=
    { carrier := {M | ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0}
      mul_mem' := by
        intro M N hM hN i j hj hi
        simp only [Set.mem_setOf_eq] at hM hN
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : (k : ℕ) < a
        · rw [hM i k hk hi, zero_mul]
        · rw [hN k j hj (not_lt.1 hk), mul_zero]
      add_mem' := by
        intro M N hM hN i j hj hi
        simp only [Set.mem_setOf_eq] at hM hN
        rw [Matrix.add_apply, hM i j hj hi, hN i j hj hi, add_zero]
      algebraMap_mem' := by
        intro r i j hj hi
        have hij : i ≠ j := by
          intro h; subst h; omega
        simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply_ne hij] }
  let c : GL (Fin n) F' := incl F F' n y₀
  have key : ∀ (M : Matrix (Fin n) (Fin n) F') (hM : M ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')}),
      ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * M * (c : Matrix (Fin n) (Fin n) F') ∈ T := by
    intro M hM
    induction hM using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      have e : ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * (c : Matrix (Fin n) (Fin n) F')
          = ((incl F F' n (y₀⁻¹ * γ * y₀) : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') := by
        simp only [c, map_mul, map_inv, Units.val_mul]
      rw [e]
      intro i j hj hi
      simp only [incl, gal, Matrix.GeneralLinearGroup.map_apply]
      rw [hγ i j hj hi, map_zero]
    | algebraMap r =>
      have e : ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * algebraMap F' (Matrix (Fin n) (Fin n) F') r * (c : Matrix (Fin n) (Fin n) F')
          = algebraMap F' (Matrix (Fin n) (Fin n) F') r := by
        rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.inv_mul]
      rw [e]; exact T.algebraMap_mem r
    | add x y _ _ hx hy =>
      rw [mul_add, add_mul]; exact T.add_mem hx hy
    | mul x y _ _ hx hy =>
      have e : ((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * (x * y) * (c : Matrix (Fin n) (Fin n) F')
          = (((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * x * (c : Matrix (Fin n) (Fin n) F')) *
            (((c⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * y * (c : Matrix (Fin n) (Fin n) F')) := by
        simp only [mul_assoc, Units.mul_inv_cancel_left]
      rw [e]; exact T.mul_mem hx hy
  intro i j hj hi
  have := key _ hδ i j hj hi
  simpa [c, Units.val_mul] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinHomExtendOfDenominatorStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_adjoin_algHom_of_mul_mem_of_map_ne_zero : ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S), ψ h ≠ 0 → ∀ T : Set F, (∀ x ∈ T, (h : F) * x ∈ S) → Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by
  first | exact @GlobalTheory.adjoin_hom_extend_of_denominator | exact GlobalTheory.adjoin_hom_extend_of_denominator | (intros; apply GlobalTheory.adjoin_hom_extend_of_denominator <;> assumption)
end

