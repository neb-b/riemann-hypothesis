module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0001
public import Formalism.PairingDivisors.PairingDivisorProofs.SumValuationNat
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MfactLeFactorialPow
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem mfact_le_factorial_pow : ∀ (n : ℕ) (ν : Fin n → ℕ) (R : ℕ), (∀ i, ν i ≤ R) → ∀ mo : Fin n × Fin n →₀ ℕ, (∀ t, ∑ a, mo (a, t) = ν t) → mfact mo ≤ (R.factorial) ^ n := by
  intro n ν R hR mo hmo
  have h : mfact mo = ∏ t : Fin n, ∏ a : Fin n, (mo (a, t)).factorial := by
    change (mo.prod fun _ k => k.factorial) = _
    rw [Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type_right]
  rw [h]
  calc ∏ t : Fin n, ∏ a : Fin n, (mo (a, t)).factorial ≤ ∏ _t : Fin n, R.factorial := by
        refine Finset.prod_le_prod' fun t _ => ?_
        refine le_trans (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum Finset.univ fun a => mo (a, t))) ?_
        rw [hmo t]
        exact Nat.factorial_le (hR t)
    _ = R.factorial ^ n := by simp

end GlobalTheory.TestLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecInjectiveMapOfLinearIndependent
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem mulVec_injective_map_of_linearIndependent {K L : Type} [Field K] [Field L] (σ : K →+* L) {d j : ℕ}
    (e : Fin j → Fin d → K) (he : LinearIndependent K e) :
    Function.Injective (((Matrix.of e)ᵀ).map σ).mulVec := by
  letI : Algebra K L := σ.toAlgebra
  rw [Matrix.mulVec_injective_iff]
  have h := (linearIndependent_algebraMap_comp_iff (S := L) (v := e)).2 he
  exact h

theorem gram_eq_conjTranspose_mul {K : Type} [Field K] [NumberField K] [StarRing K] {d j : ℕ}
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) (e : Fin j → Fin d → K) :
    gram X v e = ((X v)⁻¹ * ((Matrix.of e)ᵀ).map v.embedding)ᴴ * ((X v)⁻¹ * ((Matrix.of e)ᵀ).map v.embedding) := by
  ext a b
  simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.of_apply]
  rw [Matrix.mul_apply]
  rfl

theorem gramR_ne_zero_and_gram_posDef : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (d j : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), IsMetric H X → ∀ e : Fin j → Fin d → K, LinearIndependent K e → gramR H e ≠ 0 ∧ ∀ v, (gram X v e).PosDef := by
  intro K _ _ _ _ v0 hv0 d j H X hX e he
  have hpos : ∀ v, (gram X v e).PosDef := by
    intro v
    rw [gram_eq_conjTranspose_mul]
    refine Matrix.PosDef.conjTranspose_mul_self _ ?_
    have h1 : Function.Injective ((X v)⁻¹).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ (hX v).1))
    have h2 := mulVec_injective_map_of_linearIndependent v.embedding e he
    intro x y hxy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hxy
    exact h2 (h1 hxy)
  refine ⟨?_, hpos⟩
  have key : v0.embedding (gramR H e) = (gram X v0 e).det := by
    unfold gramR
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    set σ := v0.embedding
    have hM : H.map σ = ((X v0)⁻¹).conjTranspose * (X v0)⁻¹ := (hX v0).2.symm
    ext a b
    rw [Matrix.map_apply, Matrix.of_apply, RingHom.map_dotProduct]
    have hmv : (⇑σ ∘ (H *ᵥ e b)) = H.map σ *ᵥ (⇑σ ∘ e b) :=
      funext fun i => RingHom.map_mulVec σ _ _ i
    have hs : (⇑σ ∘ star (e a)) = star (⇑σ ∘ e a) := by
      funext i
      simp only [Function.comp_apply, Pi.star_apply]
      rw [← starRingEnd_apply]
      exact hv0 (e a i)
    rw [hmv, hs, hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.of_apply]
    rfl
  intro h0
  rw [h0, map_zero] at key
  exact (hpos v0).det_pos.ne key

end GlobalTheory.TestLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegLogLeLcvOfIntegralForm
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem vw_gramR_locBasis_ge {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
    (Γ : Matrix (Fin d) (Fin d) K) (s : ℕ) (hs : 0 < s) (L : Submodule (𝓞 K) (Fin d → K))
    (hint : ∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ Γ *ᵥ y) ∈ (algebraMap (𝓞 K) K).range)
    (w : HeightOneSpectrum (𝓞 K)) (f : Fin d → Fin d → K) (hf : IsLocBasis L w f)
    (hG : gramR Γ f ≠ 0) : 0 ≤ (d : ℤ) * vw w (s : K) + vw w (gramR Γ f) := by
  classical
  have hmem : ∀ a, ∃ t ∈ ReductionFirst.Tw w, t • f a ∈ L := by
    intro a
    have h1 : f a ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Submodule.span (𝓞 K) (Set.range f)) :=
      ⟨1, (Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal).one_mem, by
        rw [one_smul]; exact Submodule.subset_span ⟨a, rfl⟩⟩
    rw [hf.2] at h1
    obtain ⟨t, ht, h⟩ := h1
    exact ⟨t, ReductionFirst.hcompl_le_Tw w ht, h⟩
  choose t ht htL using hmem
  have hT : (∏ a, t a) ∈ ReductionFirst.Tw w := Submonoid.prod_mem _ fun a _ => ht a
  have hTL : ∀ a, (∏ b, t b) • f a ∈ L := by
    intro a
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a), mul_smul]
    exact L.smul_mem _ (htL a)
  obtain ⟨T, hTdef⟩ : ∃ T, T = ∏ a, t a := ⟨_, rfl⟩
  rw [← hTdef] at hT
  simp only [← hTdef] at hTL
  choose Q hQ using fun a b => hint _ (hTL a) _ (hTL b)
  have hmap : (Matrix.of Q).map (algebraMap (𝓞 K) K) =
      ((s : K) * (((cO K T : 𝓞 K) : K) * (T : K))) •
        (Matrix.of fun a b => star (f a) ⬝ᵥ Γ.mulVec (f b)) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hQ a b, ReductionFirst.smul_coe, ReductionFirst.smul_coe, star_smul, Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_smul, ReductionFirst.cO_coe, smul_eq_mul, smul_eq_mul]
    ring
  have hdet : algebraMap (𝓞 K) K (Matrix.of Q).det =
      ((s : K) * (((cO K T : 𝓞 K) : K) * (T : K))) ^ d * gramR Γ f := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_smul, Fintype.card_fin]
    rfl
  have hnn : 0 ≤ vw w (((s : K) * (((cO K T : 𝓞 K) : K) * (T : K))) ^ d * gramR Γ f) := by
    rw [← hdet]; exact ReductionFirst.vw_int_nonneg w _
  have hT0 := ReductionFirst.Tw_ne_zero hT
  have hT0' := ReductionFirst.Tw_ne_zero (ReductionFirst.cO_mem_Tw hT)
  have hs0 : (s : K) ≠ 0 := by exact_mod_cast hs.ne'
  rw [ReductionFirst.vw_mul w (pow_ne_zero _ (mul_ne_zero hs0 (mul_ne_zero hT0' hT0))) hG, ReductionFirst.vw_pow,
    ReductionFirst.vw_mul w hs0 (mul_ne_zero hT0' hT0), ReductionFirst.vw_mul w hT0' hT0, ReductionFirst.vw_unit w T hT.1,
    ReductionFirst.vw_unit w _ hT.2] at hnn
  simpa using hnn

theorem neg_log_le_lcv_of_integral_form :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (d : ℕ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) → ∀ (Γ : Matrix (Fin d) (Fin d) K) (s : ℕ), 0 < s → Γ.det ≠ 0 → (∏ v : InfinitePlace K, ‖v.embedding Γ.det‖ ≤ ∏ v : InfinitePlace K, (gram X v (fun i => (Pi.single i 1 : Fin d → K))).det.re) → ∀ L : Submodule (𝓞 K) (Fin d → K), Submodule.IsFullLattice K L → (∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ Γ *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → -((d : ℝ) * Real.log s) ≤ lcv X L := by
  intro K _ _ _ _ d X hX Γ s hs hΓ hle L hL hint
  classical
  have hli : LinearIndependent K (fun i => (Pi.single i 1 : Fin d → K)) := by
    have : (fun i => (Pi.single i 1 : Fin d → K)) = ⇑(Pi.basisFun K (Fin d)) := by
      funext i; simp [Pi.basisFun_apply]
    rw [this]
    exact (Pi.basisFun K (Fin d)).linearIndependent
  obtain ⟨hfin, hlcv⟩ := covolume_via_basis K d X hX L hL _ hli
  obtain ⟨hGfin, hGpf⟩ := prod_formula' K _ hΓ
  obtain ⟨hsfin, hspf⟩ := Formalism.PairingDivisionLocalBalance.sum_valuation_nat K s
  obtain ⟨I, hI⟩ : ∃ I : HeightOneSpectrum (𝓞 K) → ℝ, I = fun w => lw w *
      (idx w (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin d → K)))) L : ℝ) :=
    ⟨_, rfl⟩
  rw [← hI] at hfin hlcv

  have hpos : ∀ v : InfinitePlace K,
      0 < (gram X v (fun i => (Pi.single i 1 : Fin d → K))).det.re := by
    intro v
    rw [Rb.gramStd]
    exact (Rb.pos_real (Rb.metMat_posDef X v (hX v)).det_pos).2
  have hpos' : ∀ v : InfinitePlace K, 0 < ‖v.embedding Γ.det‖ := fun v =>
    norm_pos_iff.mpr ((map_ne_zero _).mpr hΓ)
  have hmean : ∑ v : InfinitePlace K, Real.log ‖v.embedding Γ.det‖ ≤
      ∑ v, Real.log (gram X v (fun i => (Pi.single i 1 : Fin d → K))).det.re := by
    rw [← Real.log_prod (fun v _ => (hpos' v).ne'), ← Real.log_prod (fun v _ => (hpos v).ne')]
    exact Real.log_le_log (Finset.prod_pos fun v _ => hpos' v) hle
  have hinf : ∑ᶠ w, lw w * (vw w Γ.det : ℝ) ≤ (2 / (Module.finrank ℚ K : ℝ)) *
      ∑ v, Real.log (gram X v (fun i => (Pi.single i 1 : Fin d → K))).det.re := by
    rw [← hGpf]
    exact mul_le_mul_of_nonneg_left hmean (by positivity)

  have hloc : ∀ w : HeightOneSpectrum (𝓞 K),
      0 ≤ (d : ℝ) * (lw w * (vw w (s : K) : ℝ)) + lw w * (vw w Γ.det : ℝ) + I w + I (conjPl w) := by
    intro w
    obtain ⟨hmul, hstar, hlw, -, -, -, -⟩ := valuation_basic_properties K w
    obtain ⟨f, hf⟩ := semilocal_basis_exists K d L hL w
    let γ : Matrix (Fin d) (Fin d) K := Matrix.of fun k i => f i k
    have hew : (fun i => ∑ k, γ k i • (Pi.single k (1 : K) : Fin d → K)) = f := by
      funext i j
      simp [γ, Finset.sum_apply, Pi.single_apply]
    have hdet : γ.det ≠ 0 := by
      have hu : IsUnit (Matrix.of f) := Matrix.linearIndependent_rows_iff_isUnit.mp hf.1
      have : γ = (Matrix.of f)ᵀ := by ext k i; rfl
      rw [this, Matrix.det_transpose]
      exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
    have hlb : IsLocBasis L w (fun i => ∑ k, γ k i • (Pi.single k (1 : K) : Fin d → K)) := by
      rw [hew]; exact hf
    obtain ⟨hi1, hi2⟩ := index_change_formula K d L hL.toIsLattice _ hli w γ hlb
    have hgc : gramR Γ f = star γ.det * γ.det * Γ.det := by
      rw [← hew, ← Rb.gramR_std Γ]
      exact gram_matrix_change K d d _ _ γ
    have hG : gramR Γ f ≠ 0 := by
      rw [hgc]; exact mul_ne_zero (mul_ne_zero (star_ne_zero.mpr hdet) hdet) hΓ
    have h := vw_gramR_locBasis_ge Γ s hs L hint w f hf hG
    rw [hgc, hmul _ _ (mul_ne_zero (star_ne_zero.mpr hdet) hdet) hΓ,
      hmul _ _ (star_ne_zero.mpr hdet) hdet, hstar] at h
    have h' : (0 : ℝ) ≤ (d : ℝ) * (vw w (s : K) : ℝ) +
        ((vw (conjPl w) γ.det : ℝ) + (vw w γ.det : ℝ) + (vw w Γ.det : ℝ)) := by exact_mod_cast h
    have hl0 : 0 ≤ lw w := div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
    have := mul_nonneg hl0 h'
    rw [hI]
    simp only
    rw [hi1, hi2, hlw]
    linarith
  have hinj : Function.Injective (conjPl : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K)) :=
    fun a b h => by rw [← ValuationRepresentative.conjPl_conjPl a, h, ValuationRepresentative.conjPl_conjPl b]
  have hfc : (Function.support fun w => I (conjPl w)).Finite := hfin.preimage hinj.injOn
  have hsfin' : (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      (d : ℝ) * (lw w * (vw w (s : K) : ℝ))).Finite :=
    hsfin.subset (Function.support_mul_subset_right _ _)
  have h12 := (hsfin'.union hGfin).subset (Function.support_add _ _)
  have h123 := (h12.union hfin).subset (Function.support_add _ _)
  have htot := finsum_nonneg hloc
  rw [finsum_add_distrib h123 hfc, finsum_add_distrib h12 hfin, finsum_add_distrib hsfin' hGfin,
    finite_sum_conjugation K I, ← mul_finsum' _ _ hsfin, hspf] at htot
  rw [hlcv]
  linarith

end GlobalTheory.TestLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthogonalSumCoefficientLatticeIsLatticeAndDual
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.SumLat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}

def valEquiv (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam) : (Fin N → K) ≃ₗ[K] (C → VV K lam) :=
  LinearEquiv.ofBijective (LinearMap.pi fun c => valAt lam e c) (Model.valAt_bijective lam e)

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
theorem _root_.GlobalTheory.TestLat.SumLat.idx_nonempty (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) : Nonempty (_root_.Formalism.L2.DIV.VVIdx lam) := by
  have hne : (_root_.Formalism.L2.Col.extV ℚ lam : _root_.Formalism.L2.DIV.VV ℚ lam) ≠ 0 := by
    intro h
    apply _root_.Formalism.L2.Col.evV_extV_ne_zero (E := ℚ) (fun _ => RingHom.id ℚ) (1 : Matrix (Fin n) (Fin n) ℚ) lam
      (Rat.castHom ℂ)
      (⟨fun _ => 1, fun _ => by simp⟩ : {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det})
    rw [h]
    exact map_zero _
  haveI : Nontrivial (_root_.Formalism.L2.DIV.VV ℚ lam) := nontrivial_of_ne _ _ hne
  exact (_root_.Formalism.L2.DIV.bVV ℚ lam).index_nonempty

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
theorem _root_.GlobalTheory.TestLat.SumLat.isLattice_sumLat [Finite C] (lam : ι → _root_.Formalism.BasicNotions.DomWeight n)
    (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam)
    (T : C → Submodule (𝓞 K) (_root_.Formalism.L2.DIV.VV K lam)) (hT : ∀ c, Submodule.IsLattice K (T c)) :
    Submodule.IsLattice K (_root_.GlobalTheory.TestLat.sumLat lam e T) := by
  classical
  haveI := Fintype.ofFinite C
  set f := _root_.GlobalTheory.TestLat.SumLat.valEquiv (K := K) lam e with hf
  let g : C → _root_.Formalism.L2.DIV.VV K lam →ₗ[K] (Fin N → K) := fun c =>
    f.symm.toLinearMap ∘ₗ LinearMap.single K (fun _ : C => _root_.Formalism.L2.DIV.VV K lam) c
  have hval : ∀ c c' t, _root_.GlobalTheory.TestLat.valAt lam e c' (g c t) = (Pi.single c t : C → _root_.Formalism.L2.DIV.VV K lam) c' := by
    intro c c' t
    have h := congrFun (f.apply_symm_apply (Pi.single c t : C → _root_.Formalism.L2.DIV.VV K lam)) c'
    exact h
  have hsum : ∀ u, ∑ c, g c (_root_.GlobalTheory.TestLat.valAt lam e c u) = u := by
    intro u
    apply f.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have h : ∀ c, f (g c (_root_.GlobalTheory.TestLat.valAt lam e c u)) =
        Pi.single c (_root_.GlobalTheory.TestLat.valAt lam e c u) := fun c => f.apply_symm_apply _
    simp only [h]
    exact Finset.univ_sum_single (fun c => _root_.GlobalTheory.TestLat.valAt lam e c u)
  set L : Submodule (𝓞 K) (Fin N → K) := ⨆ c, (T c).map ((g c).restrictScalars (𝓞 K)) with hL
  have hP : _root_.GlobalTheory.TestLat.sumLat lam e T = L := by
    apply le_antisymm
    · intro u hu
      rw [_root_.GlobalTheory.TestLat.Model.mem_sumLat] at hu
      rw [← hsum u]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.mem_iSup_of_mem c (Submodule.mem_map_of_mem (hu c))
    · rw [hL, iSup_le_iff]
      intro c
      rw [Submodule.map_le_iff_le_comap]
      intro t ht
      rw [Submodule.mem_comap, _root_.GlobalTheory.TestLat.Model.mem_sumLat]
      intro c'
      rw [LinearMap.restrictScalars_apply, hval]
      by_cases hc : c' = c
      · subst hc
        rw [Pi.single_eq_same]
        exact ht
      · rw [Pi.single_eq_of_ne hc]
        exact zero_mem _
  have key : ∀ c, ∀ t ∈ Submodule.span K (T c : Set (_root_.Formalism.L2.DIV.VV K lam)),
      g c t ∈ Submodule.span K (L : Set (Fin N → K)) := by
    intro c t ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span (Submodule.mem_iSup_of_mem c (Submodule.mem_map_of_mem hx))
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ a hx
  rw [hP]
  refine ⟨Submodule.fg_iSup _ fun c => ((hT c).fg).map _, ?_⟩
  intro s hs hli
  exact (LinearIndependent.iff_fractionRing _ _).mp hli

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
theorem _root_.GlobalTheory.TestLat.SumLat.sumLat_lattice_dual : ∀ (K : Type) [Field K] [NumberField K]
    [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (C : Type) [Nonempty C]
    (N : ℕ) (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam) (T : C → Submodule (𝓞 K) (_root_.Formalism.L2.DIV.VV K lam)),
    (∀ c, Submodule.IsLattice K (T c)) → Submodule.IsLattice K (_root_.GlobalTheory.TestLat.sumLat lam e T) ∧
      0 < N ∧ ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, (G τ)ᴴ = G τ) →
        _root_.Formalism.L2.DIV.hdualFr (_root_.GlobalTheory.TestLat.sumGram lam e G) (_root_.GlobalTheory.TestLat.sumLat lam e T) =
          _root_.GlobalTheory.TestLat.sumLat lam e fun c => _root_.Formalism.HermitianLatticesTheory.dual (_root_.Formalism.L2.DIV.pairK lam G) (T c) := by
  intro K _ _ _ ι _ n lam C _ N e T hT
  classical
  obtain ⟨i₀⟩ := _root_.GlobalTheory.TestLat.SumLat.idx_nonempty lam
  haveI : Finite (C × _root_.Formalism.L2.DIV.VVIdx lam) := Finite.of_equiv _ e
  haveI : Finite C :=
    Finite.of_surjective (fun p : C × _root_.Formalism.L2.DIV.VVIdx lam => p.1) (fun c => ⟨(c, i₀), rfl⟩)
  haveI : Fintype C := Fintype.ofFinite C
  refine ⟨_root_.GlobalTheory.TestLat.SumLat.isLattice_sumLat lam e T hT, ?_, ?_⟩
  · obtain ⟨c₀⟩ := (inferInstance : Nonempty C)
    refine Nat.pos_of_ne_zero fun h => ?_
    subst h
    exact (e.symm (c₀, i₀)).elim0
  · intro G _
    ext x
    rw [_root_.GlobalTheory.TestLat.Model.mem_sumLat]
    have hmemD : ∀ L : Submodule (𝓞 K) (Fin N → K), x ∈ _root_.Formalism.L2.DIV.hdualFr (_root_.GlobalTheory.TestLat.sumGram lam e G) L ↔
        ∀ y ∈ L, star y ⬝ᵥ _root_.GlobalTheory.TestLat.sumGram lam e G *ᵥ x ∈ (1 : Submodule (𝓞 K) K) :=
      fun _ => Iff.rfl
    have hmemV : ∀ (c : C) (v : _root_.Formalism.L2.DIV.VV K lam), v ∈ _root_.Formalism.HermitianLatticesTheory.dual (_root_.Formalism.L2.DIV.pairK lam G) (T c) ↔
        ∀ z ∈ T c, _root_.Formalism.L2.DIV.pairK lam G z v ∈ (1 : Submodule (𝓞 K) K) := by
      intro c v
      unfold _root_.Formalism.HermitianLatticesTheory.dual _root_.Formalism.E.hdual
      simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    rw [hmemD]
    simp_rw [_root_.GlobalTheory.TestLat.Model.sumGram_form, hmemV]
    constructor
    · intro h c z hz
      set y := (_root_.GlobalTheory.TestLat.SumLat.valEquiv (K := K) lam e).symm (Pi.single c z : C → _root_.Formalism.L2.DIV.VV K lam) with hydef
      have hy : ∀ c', _root_.GlobalTheory.TestLat.valAt lam e c' y = (Pi.single c z : C → _root_.Formalism.L2.DIV.VV K lam) c' := by
        intro c'
        have h' := congrFun
          ((_root_.GlobalTheory.TestLat.SumLat.valEquiv (K := K) lam e).apply_symm_apply (Pi.single c z : C → _root_.Formalism.L2.DIV.VV K lam)) c'
        exact h'
      have hyL : y ∈ _root_.GlobalTheory.TestLat.sumLat lam e T := by
        rw [_root_.GlobalTheory.TestLat.Model.mem_sumLat]
        intro c'
        rw [hy]
        by_cases hc : c' = c
        · subst hc
          rw [Pi.single_eq_same]
          exact hz
        · rw [Pi.single_eq_of_ne hc]
          exact zero_mem _
      have hsum := h y hyL
      rwa [Finset.sum_eq_single c
        (fun c' _ hc => by rw [hy, Pi.single_eq_of_ne hc, map_zero, LinearMap.zero_apply])
        (by simp), hy, Pi.single_eq_same] at hsum
    · intro h y hy
      rw [_root_.GlobalTheory.TestLat.Model.mem_sumLat] at hy
      exact Submodule.sum_mem _ fun c _ => h c _ (hy c)

end GlobalTheory.TestLat.SumLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReciprocityLargeLevel
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem reciprocity_large_level : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K), ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  intro Ω _ _ _ ε T f
  obtain ⟨a, b, hb, hab⟩ := T.io_surj f
  have hbK : T.io b ≠ 0 := by
    intro h
    exact hb (T.io_inj (by rw [h, map_zero]))
  have hf : f = T.io a / T.io b := by
    rw [eq_div_iff hbK, hab]
  obtain ⟨Na, wa, hNa, hLa⟩ := ((_root_.GlobalTheory.FN.mem_ring_iff_inR ε.range).1 a).1 a.2
  obtain ⟨Nb, wb, hNb, hLb⟩ := ((_root_.GlobalTheory.FN.mem_ring_iff_inR ε.range).1 b).1 b.2
  refine ⟨Na * Nb, Nat.mul_pos hNa hNb, ?_⟩
  intro N hN hdiv s d hs γ γ' hc
  have hLa' : Lv ε.range N wa a :=
    _root_.GlobalTheory.FN.lv_mono ε.range Na N wa wa a hN (dvd_trans (dvd_mul_right Na Nb) hdiv) le_rfl hLa
  have hLb' : Lv ε.range N wb b :=
    _root_.GlobalTheory.FN.lv_mono ε.range Nb N wb wb b hN (dvd_trans (dvd_mul_left Nb Na) hdiv) le_rfl hLb
  have ra := _root_.GlobalTheory.FN.gal_sl_io_of_cong Ω ε T a N wa hN hLa' s d hs γ γ' hc
  have rb := _root_.GlobalTheory.FN.gal_sl_io_of_cong Ω ε T b N wb hN hLb' s d hs γ γ' hc
  rw [hf, map_div₀, map_div₀, map_div₀, map_div₀, ra, rb]

end GlobalTheory.FN
end

