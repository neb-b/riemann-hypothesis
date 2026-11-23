module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.DiscrMulIntegral
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix

theorem discr_mul_integral {K : Type} [Field K] [NumberField K] (z : K)
    (hz : ∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (z * a) = n) :
    IsIntegral ℤ ((NumberField.discr K : K) * z) := by
  classical
  have hne : (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K))

  have hz1 : z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have h1ne : (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := by
      rw [← FractionalIdeal.coeIdeal_top]
      exact FractionalIdeal.coeIdeal_ne_zero.mpr top_ne_bot
    rw [FractionalIdeal.mem_dual h1ne]
    intro a ha
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨n, hn⟩ := hz a'
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hn.symm

  set N : ℕ := Ideal.absNorm (differentIdeal ℤ (𝓞 K)) with hN
  have hNmem : (N : K) ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨(N : 𝓞 K), Ideal.absNorm_mem _, by simp⟩
  have hprod : z * (N : K) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have h := FractionalIdeal.mul_mem_mul hz1 hNmem
    have hdual : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹ := by
      rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]
    rwa [hdual, inv_mul_cancel₀ hne] at h
  obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).mp hprod
  have hint : IsIntegral ℤ (z * (N : K)) := by
    rw [← hx]; exact RingOfIntegers.isIntegral_coe x
  have hNd : N = (NumberField.discr K).natAbs := NumberField.absNorm_differentIdeal K (𝓞 K)
  rcases Int.natAbs_eq (NumberField.discr K) with h | h
  · rw [h, ← hNd, Int.cast_natCast, mul_comm]; exact hint
  · rw [h, ← hNd, Int.cast_neg, Int.cast_natCast, neg_mul, mul_comm]; exact hint.neg

end Formalism.L2.Pj.FundamentalDomainD5
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.DotSelfEqSqNorm
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open Matrix

theorem dot_self_eq_sq_norm {N : ℕ} (v : Fin N → ℝ) :
    v ⬝ᵥ v = ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm v‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp [dotProduct, sq]

theorem cover_round {N : ℕ} (b : Fin N → Fin N → ℝ) (hb : LinearIndependent ℝ b) (ℓ : ℝ)
    (hℓ : ∀ j, b j ⬝ᵥ b j ≤ ℓ ^ 2) (w : Fin N → ℝ) :
    ∃ n : Fin N → ℤ, (w - ∑ j, (n j : ℝ) • b j) ⬝ᵥ (w - ∑ j, (n j : ℝ) • b j) ≤ ((N : ℝ) * ℓ / 2) ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨0, by simp [dotProduct]⟩
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hcard : Fintype.card (Fin N) = Module.finrank ℝ (Fin N → ℝ) := by simp
  let B := basisOfLinearIndependentOfCardEqFinrank hb hcard
  have hB : ∀ j, B j = b j := fun j => by simp [B]
  set c := B.repr w with hcdef
  refine ⟨fun j => round (c j), ?_⟩
  have hw : w = ∑ j, c j • b j := by
    conv_lhs => rw [← B.sum_repr w]
    simp only [hB, hcdef]

  have hdiff : w - ∑ j, ((round (c j) : ℤ) : ℝ) • b j = ∑ j, (c j - round (c j)) • b j := by
    conv_lhs => rw [hw]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [sub_smul]
  have hbj : ∀ j, ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (b j)‖ ≤ |ℓ| := by
    intro j
    have h := hℓ j
    rw [dot_self_eq_sq_norm, ← sq_abs ℓ] at h
    by_contra hc
    push_neg at hc
    nlinarith [abs_nonneg ℓ]
  have hnorm : ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (∑ j, (c j - round (c j)) • b j)‖ ≤
      (N : ℝ) * |ℓ| / 2 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    calc ‖∑ j, (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm ((c j - round (c j)) • b j)‖
        ≤ ∑ j, ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm ((c j - round (c j)) • b j)‖ :=
          norm_sum_le _ _
      _ = ∑ j, |c j - round (c j)| * ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (b j)‖ := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [LinearEquiv.map_smul, norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ _j : Fin N, (1 / 2) * |ℓ| :=
          Finset.sum_le_sum (fun j _ =>
            mul_le_mul (abs_sub_round _) (hbj j) (norm_nonneg _) (by norm_num))
      _ = (N : ℝ) * |ℓ| / 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  rw [hdiff, dot_self_eq_sq_norm]
  calc ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (∑ j, (c j - round (c j)) • b j)‖ ^ 2
      ≤ ((N : ℝ) * |ℓ| / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = ((N : ℝ) * ℓ / 2) ^ 2 := by
      rw [div_pow, mul_pow, sq_abs, ← mul_pow, ← div_pow]

end Formalism.L2.Pj.FundamentalDomainD5
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ExistsBasisIn
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

theorem exists_basis_in {K : Type} [Field K] {r : ℕ} (S : Set (Fin r → K))
    (hS : Submodule.span K S = ⊤) :
    ∃ v : Fin r → Fin r → K, (∀ j, v j ∈ S) ∧ LinearIndependent K v := by
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent K S
  have htop : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin r → K)) := by
    rw [Subtype.range_coe, hspan, hS]
  let B := Module.Basis.mk hli htop
  let e := B.indexEquiv (Pi.basisFun K (Fin r))
  refine ⟨fun j => (e.symm j : Fin r → K), fun j => hbS (e.symm j).2, ?_⟩
  exact hli.comp e.symm e.symm.injective

end Formalism.L2.Pj.FundamentalDomainD5
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinrankCmType
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix
open scoped ComplexConjugate

lemma conj_conj_emb {K : Type} [Field K] (φ : K →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
  star_star φ

def cmEquiv {K : Type} [Field K] {ι : Type} (σ : ι → K →+* ℂ) (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) :
    ι ⊕ ι ≃ (K →+* ℂ) :=
  Equiv.ofBijective (Sum.elim σ fun i => ComplexEmbedding.conjugate (σ i)) (by
    constructor
    · rintro (i | i) (j | j) h
      · exact congrArg Sum.inl (hinj h)
      · exfalso
        have h1 : ∃ i', σ i' = σ i := ⟨i, rfl⟩
        exact (hcm (σ i)).1 h1 ⟨j, by
          have := congrArg ComplexEmbedding.conjugate h
          simp only [Sum.elim_inl, Sum.elim_inr] at this
          rw [this, conj_conj_emb]⟩
      · exfalso
        have h1 : ∃ i', σ i' = σ j := ⟨j, rfl⟩
        exact (hcm (σ j)).1 h1 ⟨i, by
          have := congrArg ComplexEmbedding.conjugate h
          simp only [Sum.elim_inl, Sum.elim_inr] at this
          rw [← this, conj_conj_emb]⟩
      · have := congrArg ComplexEmbedding.conjugate h
        simp only [Sum.elim_inr, conj_conj_emb] at this
        exact congrArg Sum.inr (hinj this)
    · intro τ
      by_cases h : ∃ i, σ i = τ
      · obtain ⟨i, hi⟩ := h
        exact ⟨Sum.inl i, hi⟩
      · have h2 : ∃ i, σ i = ComplexEmbedding.conjugate τ := by
          by_contra h3
          exact h ((hcm τ).2 h3)
        obtain ⟨i, hi⟩ := h2
        refine ⟨Sum.inr i, ?_⟩
        simp only [Sum.elim_inr, hi, conj_conj_emb])

theorem sum_re_cmType {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (σ : ι → K →+* ℂ)
    (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) (z : K) :
    ∑ i, (σ i z).re = (1 / 2 : ℝ) * ((Algebra.trace ℚ K z : ℚ) : ℝ) := by
  have h1 : (algebraMap ℚ ℂ) (Algebra.trace ℚ K z) = ∑ τ : K →+* ℂ, τ z := by
    rw [trace_eq_sum_embeddings ℂ (x := z)]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)).symm _ _ (fun _ => rfl)
  have h2 : ∑ τ : K →+* ℂ, τ z = ∑ i, σ i z + ∑ i, conj (σ i z) := by
    rw [← Equiv.sum_comp (cmEquiv σ hinj hcm), Fintype.sum_sum_type]
    rfl
  have h3 := congrArg Complex.re (h1.trans h2)
  simp only [Complex.add_re, Complex.re_sum, Complex.conj_re] at h3
  have h4 : ((algebraMap ℚ ℂ) (Algebra.trace ℚ K z)).re = ((Algebra.trace ℚ K z : ℚ) : ℝ) := by
    simp
  rw [h4] at h3
  linarith

theorem finrank_cmType {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (σ : ι → K →+* ℂ)
    (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) :
    Module.finrank ℚ K = 2 * Fintype.card ι := by
  rw [← NumberField.Embeddings.card K ℂ, ← Fintype.card_congr (cmEquiv σ hinj hcm), Fintype.card_sum]
  ring

end Formalism.L2.Pj.FundamentalDomainD5
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.LatticeZbasis
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix

theorem lattice_zbasis {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hfg : L.FG) (hspan : Submodule.span K (L : Set (Fin r → K)) = ⊤) :
    ∃ e : Fin (Module.finrank ℚ K * r) → (Fin r → K), (∀ j, e j ∈ L) ∧ LinearIndependent ℚ e ∧
      ∀ v ∈ L, ∃ n : Fin (Module.finrank ℚ K * r) → ℤ, v = ∑ j, (n j : ℚ) • e j := by
  classical
  haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 K) L
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  set b := Module.Free.chooseBasis ℤ L
  set f : Module.Free.ChooseBasisIndex ℤ L → (Fin r → K) := fun j => (b j : Fin r → K) with hf
  have hfZ : LinearIndependent ℤ f :=
    b.linearIndependent.map' (L.subtype.restrictScalars ℤ) (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hfQ : LinearIndependent ℚ f := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hfZ
  have hrep : ∀ v ∈ L, ∃ c : Module.Free.ChooseBasisIndex ℤ L → ℤ, v = ∑ j, (c j : ℚ) • f j := by
    intro v hv
    refine ⟨fun j => b.repr ⟨v, hv⟩ j, ?_⟩
    have h' := congrArg (fun z : L => (z : Fin r → K)) (b.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
    conv_lhs => rw [← h']
    exact Finset.sum_congr rfl fun j _ => (Int.cast_smul_eq_zsmul ℚ _ _).symm
  have hS : ∀ v ∈ L, v ∈ Submodule.span ℚ (Set.range f) := by
    intro v hv
    obtain ⟨c, hc⟩ := hrep v hv
    rw [hc]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hKL : ∀ v ∈ L, ∀ k : K, k • v ∈ Submodule.span ℚ (Set.range f) := by
    intro v hv k
    have halg : IsAlgebraic ℤ k :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic k)
    obtain ⟨y, hy0, hyi⟩ := halg.exists_integral_multiple
    have hmem : ((⟨y • k, hyi⟩ : 𝓞 K)) • v ∈ L := L.smul_mem _ hv
    have hyK : (y : K) ≠ 0 := by exact_mod_cast hy0
    have heq : k • v = ((y : ℚ)⁻¹) • ((⟨y • k, hyi⟩ : 𝓞 K) • v) := by
      rw [algebra_compatible_smul K ((y : ℚ)⁻¹), algebra_compatible_smul K (⟨y • k, hyi⟩ : 𝓞 K), smul_smul]
      congr 1
      simp only [map_inv₀, map_intCast, zsmul_eq_mul]
      show k = (y : K)⁻¹ * ((y : K) * k)
      field_simp
    rw [heq]
    exact Submodule.smul_mem _ _ (hS _ hmem)
  have htop : ⊤ ≤ Submodule.span ℚ (Set.range f) := by
    intro x _
    have hx : x ∈ Submodule.span K (L : Set (Fin r → K)) := hspan ▸ Submodule.mem_top
    have key : ∀ z ∈ Submodule.span K (L : Set (Fin r → K)), ∀ k : K, k • z ∈ Submodule.span ℚ (Set.range f) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem v hv => exact hKL v hv
      | zero => intro k; rw [smul_zero]; exact Submodule.zero_mem _
      | add a c _ _ ha hc => intro k; rw [smul_add]; exact Submodule.add_mem _ (ha k) (hc k)
      | smul c a _ ha => intro k; rw [smul_smul]; exact ha (k * c)
    simpa using key x hx 1
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Module.finrank ℚ K * r := by
    rw [← Module.finrank_eq_card_basis (Module.Basis.mk hfQ htop), Module.finrank_pi_fintype]
    simp [mul_comm]
  let eqv := Fintype.equivFinOfCardEq hcard
  refine ⟨f ∘ eqv.symm, fun j => (b (eqv.symm j)).2, hfQ.comp _ eqv.symm.injective, fun v hv => ?_⟩
  obtain ⟨c, hc⟩ := hrep v hv
  refine ⟨c ∘ eqv.symm, ?_⟩
  rw [hc]
  exact (Fintype.sum_equiv eqv.symm _ _ (fun j => rfl)).symm

end Formalism.L2.Pj.FundamentalDomainD5
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.RhoDotSelf
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open Matrix ComplexConjugate

variable {ι : Type} [Fintype ι] {r N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2)

def rho (w : ι → Fin r → ℂ) : Fin N → ℝ := fun k =>
  if (eqv k).2.2 = 0 then (w (eqv k).1 (eqv k).2.1).re else (w (eqv k).1 (eqv k).2.1).im

theorem rho_add (w w' : ι → Fin r → ℂ) : rho eqv (w + w') = rho eqv w + rho eqv w' := by
  funext k
  simp only [rho, Pi.add_apply]
  split_ifs <;> simp

theorem rho_sub (w w' : ι → Fin r → ℂ) : rho eqv (w - w') = rho eqv w - rho eqv w' := by
  funext k
  simp only [rho, Pi.sub_apply]
  split_ifs <;> simp

theorem rho_smul (c : ℝ) (w : ι → Fin r → ℂ) : rho eqv ((c : ℂ) • w) = c • rho eqv w := by
  funext k
  simp only [rho, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem rho_zero : rho eqv (0 : ι → Fin r → ℂ) = 0 := by
  funext k
  simp [rho]

theorem rho_sum {κ : Type} (s : Finset κ) (w : κ → ι → Fin r → ℂ) :
    rho eqv (∑ j ∈ s, w j) = ∑ j ∈ s, rho eqv (w j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rho_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, rho_add, ih]

theorem rho_dot (w w' : ι → Fin r → ℂ) :
    rho eqv w ⬝ᵥ rho eqv w' = ∑ i, ∑ a, (conj (w i a) * w' i a).re := by
  unfold dotProduct
  rw [← eqv.symm.sum_comp]
  simp only [rho, Equiv.apply_symm_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [Complex.mul_re]

theorem rho_dot_self (w : ι → Fin r → ℂ) : rho eqv w ⬝ᵥ rho eqv w = ∑ i, ∑ a, ‖w i a‖ ^ 2 := by
  rw [rho_dot]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  ring

end Formalism.L2.Pj.FundamentalDomainD5
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.TieLDB
section
namespace Formalism.L2.Pj.QAt.TieLDB

open Module

variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]
  {V : Type*} [AddCommGroup V] [Module A V] [Module (Localization.AtPrime p) V]
  [IsScalarTower A (Localization.AtPrime p) V]

theorem smul_comm' (s : A) (o : Localization.AtPrime p) (v : V) : s • (o • v) = o • (s • v) := by
  rw [← smul_assoc, Algebra.smul_def, mul_comm, mul_smul, algebraMap_smul]

theorem exists_smul_mem (G : Submodule A V) {x : V}
    (hx : x ∈ Submodule.span (Localization.AtPrime p) (G : Set V)) :
    ∃ s ∈ p.primeCompl, s • x ∈ G := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, p.primeCompl.one_mem, by rw [smul_zero]; exact G.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, p.primeCompl.mul_mem hs ht, ?_⟩
    have e1 : (s * t) • x = t • (s • x) := by rw [mul_comm, mul_smul]
    have e2 : (s * t) • y = s • (t • y) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact add_mem (G.smul_mem t hsx) (G.smul_mem s hty)
  | smul o x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨⟨a, s'⟩, hos⟩ := IsLocalization.mk'_surjective p.primeCompl o
    refine ⟨s' * s, p.primeCompl.mul_mem s'.2 hs, ?_⟩
    have h1 : (s' : A) • o = algebraMap A (Localization.AtPrime p) a := by
      rw [← hos, Algebra.smul_def, mul_comm, IsLocalization.mk'_spec]
    rw [mul_smul, smul_comm' p s o x, ← smul_assoc, h1, algebraMap_smul]
    exact G.smul_mem a hsx

theorem span_inf_eq (M : Submodule A V) (W : Submodule (Localization.AtPrime p) V) :
    Submodule.span (Localization.AtPrime p) ((M ⊓ W.restrictScalars A : Submodule A V) : Set V) =
      Submodule.span (Localization.AtPrime p) (M : Set V) ⊓ W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact ⟨Submodule.subset_span hx.1, hx.2⟩
  · rintro x ⟨hxM, hxW⟩
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem p M hxM
    have hu := IsLocalization.map_units (Localization.AtPrime p) (⟨s, hs⟩ : p.primeCompl)
    have hmem : s • x ∈ Submodule.span (Localization.AtPrime p)
        ((M ⊓ W.restrictScalars A : Submodule A V) : Set V) :=
      Submodule.subset_span ⟨hsx, W.smul_of_tower_mem s hxW⟩
    have hx : x = hu.unit⁻¹ • (s • x) := by
      rw [← algebraMap_smul (Localization.AtPrime p) s x]
      change x = hu.unit⁻¹ • (hu.unit • x)
      rw [inv_smul_smul]
    rw [hx]
    exact Submodule.smul_of_tower_mem _ _ hmem

variable (H G : Submodule A V)

def inc : H →ₗ[A] Submodule.span (Localization.AtPrime p) (H : Set V) where
  toFun h := ⟨h, Submodule.subset_span h.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def locMap :
    H ⧸ G.comap H.subtype →ₗ[A] ↥(Submodule.span (Localization.AtPrime p) (H : Set V)) ⧸
      (Submodule.span (Localization.AtPrime p) (G : Set V)).comap
        (Submodule.span (Localization.AtPrime p) (H : Set V)).subtype :=
  (G.comap H.subtype).liftQ
    (((((Submodule.span (Localization.AtPrime p) (G : Set V)).comap
      (Submodule.span (Localization.AtPrime p) (H : Set V)).subtype).mkQ).restrictScalars A) ∘ₗ
        inc p H) (by
      intro h hh
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span hh)

theorem locMap_mk (h : H) :
    locMap p H G (Submodule.Quotient.mk h) = Submodule.Quotient.mk (inc p H h) := rfl

theorem isLocalizedModule : IsLocalizedModule p.primeCompl (locMap p H G) := by
  constructor
  · intro s
    rw [Module.End.isUnit_iff]
    have hu := IsLocalization.map_units (Localization.AtPrime p) s
    constructor
    · intro z1 z2 h
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
        ← algebraMap_smul (Localization.AtPrime p) (s : A) z1,
        ← algebraMap_smul (Localization.AtPrime p) (s : A) z2] at h
      exact hu.smul_left_cancel.1 h
    · intro z
      refine ⟨hu.unit⁻¹ • z, ?_⟩
      rw [Module.algebraMap_end_apply, ← algebraMap_smul (Localization.AtPrime p) (s : A)]
      change hu.unit • hu.unit⁻¹ • z = z
      rw [smul_inv_smul]
  · intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem p H hx
    refine ⟨(Submodule.Quotient.mk ⟨s • x, hsx⟩, ⟨s, hs⟩), ?_⟩
    rw [locMap_mk]
    rfl
  · intro x₁ x₂ h
    obtain ⟨h1, rfl⟩ := Submodule.Quotient.mk_surjective _ x₁
    obtain ⟨h2, rfl⟩ := Submodule.Quotient.mk_surjective _ x₂
    rw [locMap_mk, locMap_mk, Submodule.Quotient.eq] at h
    have h' : (h1 : V) - h2 ∈ Submodule.span (Localization.AtPrime p) (G : Set V) := h
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem p G h'
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    change (s • (h1 : V)) - s • (h2 : V) ∈ G
    rw [← smul_sub]
    exact hsx

theorem length_localized_eq {P : Type*} [AddCommGroup P] [Module A P]
    (e : P ≃ₗ[A] H ⧸ G.comap H.subtype) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl P) =
      Module.length (Localization.AtPrime p)
        (↥(Submodule.span (Localization.AtPrime p) (H : Set V)) ⧸
          (Submodule.span (Localization.AtPrime p) (G : Set V)).comap
            (Submodule.span (Localization.AtPrime p) (H : Set V)).subtype) := by
  have := isLocalizedModule p H G
  have : IsLocalizedModule p.primeCompl (locMap p H G ∘ₗ e.toLinearMap) := inferInstance
  exact ((IsLocalizedModule.iso p.primeCompl (locMap p H G ∘ₗ e.toLinearMap)).extendScalarsOfIsLocalization
    p.primeCompl (Localization.AtPrime p)).length_eq

end Formalism.L2.Pj.QAt.TieLDB
end

