module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0062
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0005
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0086
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomCharpolyForms
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0077
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0093
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0087

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComponentResFibreSum
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ComponentResBridge

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (Res logH)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
  (R : Res ι W e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

set_option linter.unusedSectionVars false

theorem isMultiHomogIdeal_of_mem_minimalPrimes {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    IsMultiHomogIdeal W := by
  have hPCh : IsMultiHomogIdeal (P.map (MvPolynomial.map (Int.castRingHom ℂ))) := by
    obtain ⟨T, hT, hPT⟩ := hP.2.1.2.1
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' T, ?_, by rw [hPT, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hT f hf
    exact ⟨a, fun d hd k => ha d (MvPolynomial.support_map_subset _ _ hd) k⟩
  exact (GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff W).mp
    (GroundTheory.Heights₂.Heights.NumbersDVR.MinimalPrimeMultiHomog.proof ℂ K ι _ W
      ((GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff _).mpr hPCh) hW)

end ComponentResBridge

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M ComponentResBridge

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComponentsMeetNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem ComponentsMeetNull.proof (hA : ChartDimLt.Statement) (hB : ChartRatioImageNull.Statement) :
    ComponentsMeetNull.Statement := by
  classical
  intro K _ ι _ P e Ψ S hP _ hS
  set PC : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC

  have hdimW : ∀ W ∈ PC.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ W) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    set PQ : Ideal (MvPolynomial (Σ k, ι k) ℚ) := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hPQ
    have hvar := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
    have : PQ.IsPrime := hvar.1.isPrime
    have hext : ReciprocityTheory.AnForm.R.extC PQ = PC := by
      rw [ReciprocityTheory.AnForm.R.extC, hPQ, hPC, Ideal.map_map]
      congr 1
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun q => ?_)
      · simp only [RingHom.comp_apply, MvPolynomial.map_C]
        congr 1
      · simp
    intro W hW
    rw [← hext] at hW
    rw [ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC PQ W hW]
    exact hvar.2

  have hPCh : IsMultiHomogIdeal PC := by
    obtain ⟨T, hT, hPT⟩ := hP.2.1.2.1
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' T, ?_, by rw [hPC, hPT, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hT f hf
    exact ⟨a, fun d hd k => ha d (MvPolynomial.support_map_subset _ _ hd) k⟩
  have hWh : ∀ W ∈ PC.minimalPrimes, IsMultiHomogIdeal W := fun W hW =>
    (GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff W).mp
      (GroundTheory.Heights₂.Heights.NumbersDVR.MinimalPrimeMultiHomog.proof ℂ K ι PC W
        ((GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff PC).mpr hPCh) hW)
  have hsuph : ∀ W ∈ PC.minimalPrimes, ∀ W' ∈ PC.minimalPrimes, IsMultiHomogIdeal (W ⊔ W') := by
    intro W hW W' hW'
    obtain ⟨T, hT, rfl⟩ := hWh W hW
    obtain ⟨T', hT', rfl⟩ := hWh W' hW'
    exact ⟨T ∪ T', fun f hf => hf.elim (hT f) (hT' f), (Ideal.span_union T T').symm⟩

  have hsup : ∀ W ∈ PC.minimalPrimes, ∀ W' ∈ PC.minimalPrimes, W ≠ W' →
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ W')) < ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro W hW W' hW' hne
    have : W.IsPrime := hW.1.1
    obtain ⟨g, hgW', hgW⟩ : ∃ g ∈ W', g ∉ W := by
      by_contra hcon
      push_neg at hcon
      exact hne (le_antisymm (hW.2 hW'.1 hcon) hcon)
    have hg0 : Ideal.Quotient.mk W g ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hg0)
    have eqv : ((MvPolynomial (Σ k, ι k) ℂ ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W g}) ≃+*
        MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ Ideal.span {g}) :=
      (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
        (DoubleQuot.quotQuotEquivQuotSup W (Ideal.span {g}))
    rw [ringKrullDim_eq_of_ringEquiv eqv, hdimW W hW] at h1
    have hle : W ⊔ Ideal.span {g} ≤ W ⊔ W' :=
      sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr hgW') W
    have h2 := ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)
    generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ Ideal.span {g})) = a at h1 h2
    generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ W')) = b at h2 ⊢
    refine lt_of_le_of_lt h2 ?_
    induction a using WithBot.recBotCoe with
    | bot => exact WithBot.bot_lt_coe _
    | coe a =>
      induction a using ENat.recTopCoe with
      | top => exact absurd h1 (by exact_mod_cast (show ¬ ((⊤ : ℕ∞) + 1 ≤ ((e + Fintype.card K : ℕ) : ℕ∞)) by simp))
      | coe a =>
        have : a + 1 ≤ e + Fintype.card K := by exact_mod_cast h1
        exact_mod_cast (show a < e + Fintype.card K by omega)

  refine measure_mono_null (t := ⋃ W ∈ (S : Set _), ⋃ W' ∈ (S : Set _), ⋃ (_ : W ≠ W'), ⋃ p : (k : K) → ι k,
      {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ (ReciprocityTheory.AnForm.R.chartIdeal (W ⊔ W') p), Ψ (segre z) 0 ≠ 0 ∧
        (Fin.cons 1 y : Fin (e + 1) → ℂ) = (Ψ (segre z) 0)⁻¹ • Ψ (segre z)}) ?_ ?_
  · rintro y ⟨z, hz, hzy, W, hWS, W', hW'S, hne, hzW, hzW'⟩
    choose p hp using hz.1
    simp only [Set.mem_iUnion, Finset.mem_coe]
    refine ⟨W, hWS, W', hW'S, hne, p, ReciprocityTheory.AnForm.R.affCoord p z, ?_, ?_⟩
    · have hcone : z ∈ ReciprocityTheory.AnForm.R.conePts (W ⊔ W') := by
        refine ⟨hz.1, fun f hf => ?_⟩
        have hker : W ⊔ W' ≤ RingHom.ker (eval z) := sup_le
          (fun f hf => RingHom.mem_ker.mpr (by simpa [MvPolynomial.coe_aeval_eq_eval] using hzW f hf))
          (fun f hf => RingHom.mem_ker.mpr (by simpa [MvPolynomial.coe_aeval_eq_eval] using hzW' f hf))
        exact RingHom.mem_ker.mp (hker hf)
      have h := (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal
        (hsuph W (hS W hWS) W' (hS W' hW'S)) p z hp).1 hcone
      intro f hf
      have hf' := h f hf
      rwa [← MvPolynomial.coe_aeval_eq_eval] at hf'
    · have hc : (∏ k, z ⟨k, p k⟩)⁻¹ ≠ 0 := inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => hp k)
      have hseg : segre (ReciprocityTheory.AnForm.R.affCoord p z) = (∏ k, z ⟨k, p k⟩)⁻¹ • segre z := by
        funext i
        simp only [segre, ReciprocityTheory.AnForm.R.affCoord, Pi.smul_apply, smul_eq_mul, Finset.prod_div_distrib]
        rw [div_eq_inv_mul]
      have hΨ : Ψ (segre (ReciprocityTheory.AnForm.R.affCoord p z)) =
          (∏ k, z ⟨k, p k⟩)⁻¹ • (Fin.cons 1 y : Fin (e + 1) → ℂ) := by
        rw [hseg, map_smul, hzy]
      rw [hΨ, Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one, smul_smul, inv_mul_cancel₀ hc, one_smul]
      exact ⟨hc, rfl⟩
  · refine (measure_biUnion_null_iff S.countable_toSet).2 fun W hW => ?_
    refine (measure_biUnion_null_iff S.countable_toSet).2 fun W' hW' => ?_
    refine measure_iUnion_null fun hne => measure_iUnion_null fun p => ?_
    exact hB K ι _ e Ψ (hA K ι (W ⊔ W') e p (hsuph W (hS W hW) W' (hS W' hW'))
      (hsup W (hS W hW) W' (hS W' hW') hne))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomNormPIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

namespace DehomNormPIntegral

theorem padicValRat_nonneg_of_mem {p : ℕ} [Fact p.Prime] {q : ℚ}
    (hq : q ∈ (Rat.padicValuation p).valuationSubring) : 0 ≤ padicValRat p q := by
  rw [Valuation.mem_valuationSubring_iff, Rat.padicValuation_le_one_iff] at hq
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hq]
  simp

theorem inv_natCast_mem {p : ℕ} [Fact p.Prime] {M : ℕ} (hM : ¬ p ∣ M) :
    ((M : ℚ)⁻¹) ∈ (Rat.padicValuation p).valuationSubring := by
  have hM0 : M ≠ 0 := fun h => hM (h ▸ dvd_zero p)
  rw [Valuation.mem_valuationSubring_iff, Rat.padicValuation_le_one_iff, Rat.inv_natCast_den, if_neg hM0]
  exact hM

theorem mem_range_map_iff {τ : Type*} (V : Subring ℚ) (F : MvPolynomial τ ℚ) :
    F ∈ (map V.subtype).range ↔ ∀ ν, F.coeff ν ∈ V := by
  classical
  constructor
  · rintro ⟨F', rfl⟩ ν
    rw [coeff_map]
    exact (F'.coeff ν).2
  · intro h
    refine ⟨∑ ν ∈ F.support, monomial ν ⟨F.coeff ν, h ν⟩, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_monomial]
    exact F.support_sum_monomial_coeff

theorem isIntegral_of_le_range {R Ω : Type*} [CommRing R] [CommRing Ω] [Algebra R Ω] (B : Subalgebra ℤ Ω)
    (hB : ∀ b ∈ B, ∃ r, algebraMap R Ω r = b) {x : Ω} (hx : IsIntegral B x) : IsIntegral R x := by
  obtain ⟨Q, hQm, hQ⟩ := hx
  have hl : Q.map (algebraMap B Ω) ∈ Polynomial.lifts (algebraMap R Ω) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    rw [Polynomial.coeff_map]
    exact hB _ (Q.coeff k).2
  obtain ⟨Q', hQ', -, hQ'm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hQm.map _)
  refine ⟨Q', hQ'm, ?_⟩
  rw [← Polynomial.eval_map, hQ', Polynomial.eval_map]
  exact hQ

theorem coeff_mem_of_dehom_coeff_mem {Ω : Type} [Field Ω] [CharZero Ω] {D : ℕ} {l : Fin (D + 1) → Ω}
    (hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0)
    (j : Fin (D + 1)) {N : ℕ} {F : MvPolynomial (Fin (D + 1)) ℚ} (hF : F.IsHomogeneous N) (V : Subring ℚ)
    (hG : ∀ ν, (PullFormsGeneric.dehom j F).coeff ν ∈ V) (μ : Fin (D + 1) →₀ ℕ) : F.coeff μ ∈ V := by
  classical
  have hl := DehomCharpolyForms.ne_zero_of_generic hgen
  have hlj := hl j
  set H := rename Subtype.val (PullFormsGeneric.dehom j F) with hHdef
  set N2 := max N H.totalDegree with hN2
  have hHW : H ∈ (map V.subtype).range := by
    obtain ⟨G', hG'⟩ := (mem_range_map_iff V _).mpr hG
    exact ⟨rename Subtype.val G', by rw [map_rename, hG']⟩
  have hK : DehomCharpolyForms.homog j N2 H = X j ^ (N2 - N) * F := by
    have hF2 : (X j ^ (N2 - N) * F).IsHomogeneous N2 := by
      have := (isHomogeneous_X_pow (R := ℚ) j (N2 - N)).mul hF
      rwa [Nat.sub_add_cancel (le_max_left _ _)] at this
    refine sub_eq_zero.mp (hgen N2 _ ((DehomCharpolyForms.isHomogeneous_homog j N2 H).sub hF2) ?_)
    have hfun : (fun i => if h : i = j then (1 : Ω) else ((fun i => l i / l j) ∘ (Subtype.val : {i // i ≠ j} → Fin (D + 1))) ⟨i, h⟩) =
        fun i => l i / l j := by
      funext i
      split_ifs with h
      · subst h
        exact (div_self (hl _)).symm
      · rfl
    have hval : aeval (fun i => l i / l j) H = aeval (fun i => l i / l j) F := by
      rw [hHdef, aeval_rename, PullFormsGeneric.aeval_dehom, hfun]
    rw [map_sub, DehomCharpolyForms.aeval_homog l j hlj H (le_max_right _ _), hval,
      DehomCharpolyForms.aeval_div_of_isHomogeneous l j hF, map_mul, map_pow, aeval_X, sub_eq_zero]
    have : l j ^ N2 = l j ^ (N2 - N) * l j ^ N := by rw [← pow_add, Nat.sub_add_cancel (le_max_left _ _)]
    rw [this, inv_pow]
    field_simp
  have hKW : X j ^ (N2 - N) * F ∈ (map V.subtype).range := by
    rw [← hK, DehomCharpolyForms.homog]
    refine Subring.sum_mem _ fun e _ => Subring.mul_mem _ ⟨X j ^ (N2 - e), by simp⟩ ?_
    rw [mem_range_map_iff]
    intro ν
    rw [coeff_homogeneousComponent]
    split_ifs
    · exact (mem_range_map_iff V H).mp hHW ν
    · exact V.zero_mem
  have h1 : AddMonoidAlgebra.coeff (X j ^ (N2 - N) * F) (μ + Finsupp.single j (N2 - N)) = AddMonoidAlgebra.coeff F μ := by
    rw [X_pow_eq_monomial, mul_comm, coeff_mul_monomial, mul_one]
  rw [← h1]
  exact (mem_range_map_iff V _).mp hKW _

end DehomNormPIntegral


open DehomCharpolyForms DehomNormPIntegral in
theorem DehomNormPIntegral.proof : DehomNormPIntegral.Statement := by
  intro Ω _ _ D l P _ hP hgen p hp M hM j m u hu c hchom hcp μ
  classical
  have := Fact.mk hp
  have hl := ne_zero_of_generic hgen
  set n := Module.finrank P Ω with hn
  set f := LinearMap.charpoly (Algebra.lmul P Ω u) with hf

  have h0 : algebraMap P Ω (f.coeff 0) = aeval (fun i => l i / l j) (c n) := by
    have := congrArg (fun g => _root_.AddMonoidAlgebra.coeff (M := ℕ) g 0) hcp
    simp only [Polynomial.coeff_map, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at this
    rw [this, Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      have : b < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) hbn
      rw [if_neg (by omega)]
    · intro h
      simp at h

  have hdet := LinearMap.det_eq_sign_charpoly_coeff (Algebra.lmul P Ω u)
  rw [← Algebra.norm_apply, ← hf] at hdet
  have hc0 : f.coeff 0 = (-1) ^ n * Algebra.norm P u := by
    rw [hdet, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

  let V := (Rat.padicValuation p).valuationSubring
  let σ := {i // i ≠ j}
  have hmemP : ∀ i, l i / l j ∈ P := fun i => hP ▸ IntermediateField.subset_adjoin ℚ _ ⟨i, j, hl j, rfl⟩
  let tP : σ → P := fun i => ⟨l i / l j, hmemP i⟩
  let ω : σ → Ω := fun i => l i / l j
  let _ : Algebra (MvPolynomial σ V) (MvPolynomial σ ℚ) := MvPolynomial.algebraMvPolynomial
  let ψP : MvPolynomial σ V →+* P :=
    (aeval tP : MvPolynomial σ ℚ →ₐ[ℚ] P).toRingHom.comp (algebraMap (MvPolynomial σ V) (MvPolynomial σ ℚ))
  let _ : Algebra (MvPolynomial σ V) P := ψP.toAlgebra
  let _ : Algebra (MvPolynomial σ V) Ω := (P.val.toRingHom.comp ψP).toAlgebra
  have _ : IsScalarTower (MvPolynomial σ V) P Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let fA : MvPolynomial σ ℚ →ₐ[MvPolynomial σ V] Ω :=
    { (aeval ω : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toRingHom with
      commutes' := fun r => by
        show aeval ω _ = P.val (aeval tP _)
        exact (DFunLike.congr_fun (comp_aeval (f := tP) P.val) _).symm }
  have hfA : ∀ G, fA G = aeval ω G := fun _ => rfl
  have hinj : Function.Injective fA := by
    intro a b hab
    exact injective_chart hgen j (by rw [← hfA, ← hfA]; exact hab)
  have halg : ∀ r, algebraMap (MvPolynomial σ V) Ω r =
      aeval ω (map (algebraMap V ℚ) r) := fun r => ((fA.commutes r).symm.trans (hfA _)).trans rfl

  have hB : ∀ b ∈ Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => l i / l j)),
      ∃ r, algebraMap (MvPolynomial σ V) Ω r = b := by
    intro b hb
    have hle : Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => l i / l j)) ≤
        ((Algebra.ofId (MvPolynomial σ V) Ω).range).restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      rintro _ (rfl | ⟨i, rfl⟩)
      · refine ⟨C ⟨(M : ℚ)⁻¹, inv_natCast_mem hM⟩, ?_⟩
        show algebraMap _ Ω _ = _
        rw [halg]
        simp
      · by_cases h : i = j
        · subst h
          refine ⟨1, ?_⟩
          show algebraMap _ Ω _ = _
          rw [map_one]
          exact (div_self (hl i)).symm
        · refine ⟨X ⟨i, h⟩, ?_⟩
          show algebraMap _ Ω _ = _
          rw [halg]
          simp [ω]
    obtain ⟨r, hr⟩ := hle hb
    exact ⟨r, hr⟩
  have hu' : IsIntegral (MvPolynomial σ V) u := isIntegral_of_le_range _ hB ((mem_integralClosure_iff _ _).mp hu)
  have hN : IsIntegral (MvPolynomial σ V) (algebraMap P Ω (Algebra.norm P u)) :=
    (Algebra.isIntegral_norm P hu').algebraMap
  have hx : IsIntegral (MvPolynomial σ V) (aeval (fun i => l i / l j) (c n)) := by
    rw [← h0, hc0, map_mul, map_pow, map_neg, map_one]
    exact (isIntegral_one.neg.pow n).mul hN

  have hdeh : aeval ω (PullFormsGeneric.dehom j (c n)) = aeval (fun i => l i / l j) (c n) := by
    rw [PullFormsGeneric.aeval_dehom]
    refine congrArg (fun g => aeval g (c n)) (funext fun i => ?_)
    split_ifs with h
    · subst h
      exact (div_self (hl _)).symm
    · rfl
  have hG : IsIntegral (MvPolynomial σ V) (PullFormsGeneric.dehom j (c n)) :=
    (isIntegral_algHom_iff fA hinj).mp (by rw [hfA, hdeh]; exact hx)
  have hGc : ∀ ν, (PullFormsGeneric.dehom j (c n)).coeff ν ∈ V.toSubring := by
    intro ν
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (MvPolynomial.isIntegral_iff_isIntegral_coeff.mp hG ν)
    rw [← hy]
    exact y.2
  exact padicValRat_nonneg_of_mem (coeff_mem_of_dehom_coeff_mem hgen j (hchom) V.toSubring hGc μ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormDehomIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

namespace FibreNormDehomIntegral

theorem den_eq_one_of_padicValRat_nonneg {a : ℚ} (h : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p a) : a.den = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have := Fact.mk hp
  have hnum : ¬ (p : ℤ) ∣ a.num := by
    intro hn
    have h1 : p ∣ Nat.gcd a.num.natAbs a.den := Nat.dvd_gcd (Int.ofNat_dvd_left.mp hn) hpd
    rw [a.reduced.gcd_eq_one] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have h0 := h p hp
  rw [padicValRat, padicValInt.eq_zero_of_not_dvd hnum] at h0
  have h2 : 1 ≤ multiplicity p a.den := one_le_multiplicity_of_dvd a.den_ne_zero hpd
  omega

end FibreNormDehomIntegral


open FibreNormDehomIntegral in
theorem FibreNormDehomIntegral.proof (hF : FibreNormBadPrimesFinite.Statement)
    (hG : FibreNormGoodPrimeIntegral.Statement) (hB : FibreNormPrimeBound.Statement) :
    FibreNormDehomIntegral.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L q hV hBir he hL hz
  have hSf := hF K ι Ω y D e L hV hBir he hL hz
  set T := hSf.toFinset with hT
  choose! C hC using hB K ι Ω y D e L q hV hBir he hL hz
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => ((Set.Finite.mem_toFinset hSf).mp hp).1
  set M₀ : ℕ := ∏ p ∈ T, p ^ C p with hM
  have hM0 : M₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hTp p hp).ne_zero
  refine ⟨M₀, Nat.one_le_iff_ne_zero.mpr hM0, ?_⟩
  intro τ s hs j c hc

  have hcoef : ∀ m, (((M₀ : ℚ) ^ τ) * (c (Module.finrank (pullField y L) Ω)).coeff m).den = 1 := by
    intro m
    by_cases ha : (c (Module.finrank (pullField y L) Ω)).coeff m = 0
    · rw [ha, mul_zero]; rfl
    refine den_eq_one_of_padicValRat_nonneg fun p hp => ?_
    have := Fact.mk hp
    have hMq : ((M₀ : ℚ) ^ τ) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hM0)
    rw [padicValRat.mul hMq ha, padicValRat.pow, padicValRat.of_nat]
    by_cases hpT : p ∈ T
    · have hle : C p ≤ multiplicity p M₀ :=
        (multiplicity_dvd_iff_le hM0).mp (Finset.dvd_prod_of_mem (fun p => p ^ C p) hpT)
      have hb := hC p hp τ s hs j c hc m
      have hle' : ((C p * τ : ℕ) : ℤ) ≤ (τ : ℤ) * (multiplicity p M₀ : ℤ) := by
        push_cast
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (by positivity)
      linarith
    · have hgood : ¬ HasCommonZeroModP y L p hp := fun h =>
        hpT ((Set.Finite.mem_toFinset hSf).mpr ⟨hp, h⟩)
      have hg := hG K ι Ω y D e L q hV hBir he hL hz p hp hgood τ s hs j c hc m
      have : (0 : ℤ) ≤ (τ : ℤ) * (multiplicity p M₀ : ℤ) := by positivity
      linarith

  have hmem : ((M₀ : ℚ) ^ τ) • c (Module.finrank (pullField y L) Ω) ∈
      Set.range (map (Int.castRingHom ℚ) : MvPolynomial (Fin (D + 1)) ℤ → MvPolynomial (Fin (D + 1)) ℚ) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.mp ha
    refine ⟨(((M₀ : ℚ) ^ τ) * (c (Module.finrank (pullField y L) Ω)).coeff m).num, ?_⟩
    rw [coeff_smul, smul_eq_mul, eq_intCast]
    exact Rat.coe_int_num_of_den_eq_one (hcoef m)
  obtain ⟨F, hF'⟩ := hmem
  exact ⟨F, hF'⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGenPtTransc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameGenPtTransc.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    ∀ G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
        (graphIdeal (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))),
      Transcendental (Algebra.adjoin ℤ (Set.range fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩))
        (G.x' ⟨Sum.inr (), (0 : Fin (D + 1))⟩)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

