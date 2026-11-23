module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0548
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0593
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestLast
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.SzTau

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), d.Prime → 4 < d → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → IsTauOf Λ c τ → Ω ^ 12 = latDisc Λ → (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ ∧ Sz l lam 0 (jT τ) ∧ ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N), ¬ l ∣ M → M • x = 0 → x ≠ 0 → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else if l = d then 1 / 2 else 0) ((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N x τ) / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2) := by
  intro l hl lam d Λ c Ω τ hd h4 hΛ hτ hΩ
  obtain ⟨hst, him⟩ := _root_.GlobalTheory.IntLatMul.main d Λ hd.pos hΛ
  refine ⟨GlobalTheory.QFam.pow_twelve_eq_DD Λ c τ hτ Ω hΩ, ?_, ?_⟩
  · refine (_root_.GlobalTheory.SzRules.main l lam).1 1 (jT τ) hl.out.not_dvd_one ?_
    rw [Nat.cast_one, one_mul]
    exact _root_.GlobalTheory.JInt.main Λ c τ _ hτ hst him
  · intro N _ M x hM hx hx0
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.WpFam.TauVal.main Λ c Ω τ hτ
    rw [add_div, h1, (h2 N x).1, ← add_div]
    have hh := (_root_.GlobalTheory.WpFam.homogeneity_of_isTauOf Λ c τ hτ).1
    refine _root_.GlobalTheory.CMSize.main l lam d Λ Ω _ M hd h4 hst hΩ hM ?_ ?_
    · rw [hh, (GlobalTheory.WpFam.TorsMem.main N τ).2.2.1 x]
      exact hx0
    · rw [mul_left_comm, hh]
      exact (GlobalTheory.WpFam.natCast_mul_tors_mem_lattice_iff N τ M x).2 hx

end GlobalTheory.SzTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideBis
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Charts

theorem glue : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ f : ∀ k, Hol (K.W k), (∀ k k' (h : K.le 0 k' k), Charts.sh h (f k) = f k') → ∃ G : Tot I g → ℂ, AnalyticOnNhd ℂ G {p | p.1 ∈ F.V} ∧ (∀ k, ∀ p ∈ K.W k, (f k).fn p = G p) ∧ (∀ (l : Λ) (q : Hol F.V), (∀ k k' (h : K.le l k' k), Charts.sh h (f k) = f k' + K.cst k' q) → ∀ p : Tot I g, p.1 ∈ F.V → G (F.shift l p) = G p + q.fn p.1) ∧ ((∀ k a, dw a (f k) = 0) → ∀ z ∈ F.V, ∀ w, G (z, w) = G (z, 0)) := by
  intro I _ g Λ _ F K hK f hf
  classical
  have indep : ∀ k₁ k₂ p, p ∈ K.W k₁ → p ∈ K.W k₂ → (f k₁).fn p = (f k₂).fn p := by
    intro k₁ k₂ p h₁ h₂
    obtain ⟨k, hk, hl₁, hl₂⟩ := hK.2 0 k₁ k₂ p h₁ (by rw [F.shift_zero]; exact h₂)
    have e₁ := Charts.fn_sh hl₁ (f k₁) hk
    have e₂ := Charts.fn_sh hl₂ (f k₂) hk
    rw [hf k₁ k hl₁, F.shift_zero] at e₁
    rw [hf k₂ k hl₂, F.shift_zero] at e₂
    rw [← e₁, ← e₂]
  let G : Tot I g → ℂ := fun p ↦ if h : ∃ k, p ∈ K.W k then (f h.choose).fn p else 0
  have hG : ∀ k, ∀ p ∈ K.W k, (f k).fn p = G p := by
    intro k p hp
    have h : ∃ k, p ∈ K.W k := ⟨k, hp⟩
    simp only [G, dif_pos h]
    exact indep _ _ _ hp h.choose_spec
  have hGev : ∀ k, ∀ p ∈ K.W k, G =ᶠ[𝓝 p] (f k).fn := fun k p hp ↦ by
    filter_upwards [(K.W k).isOpen.mem_nhds hp] with q hq using (hG k q hq).symm
  refine ⟨G, ?_, hG, ?_, ?_⟩
  · intro p hp
    obtain ⟨k, hk⟩ := hK.1 p hp
    exact ((f k).analytic p hk).congr (hGev k p hk).symm
  · intro l q hq p hp
    obtain ⟨k₁, h₁⟩ := hK.1 p hp
    obtain ⟨k₂, h₂⟩ := hK.1 (F.shift l p) hp
    obtain ⟨k, hk, -, hl⟩ := hK.2 l k₁ k₂ p h₁ h₂
    have e := congrArg (fun u ↦ Hol.fn u p) (hq k₂ k hl)
    rw [Charts.fn_sh hl _ hk, Hol.fn_add _ _ hk, Charts.fn_cst K k q hk] at e
    rw [← hG k₂ _ h₂, ← hG k p hk, e]
  · intro h0 z hz w
    have hder : ∀ w' : Fin g → ℂ, HasFDerivAt (fun u ↦ G (z, u)) (0 : (Fin g → ℂ) →L[ℂ] ℂ) w' := by
      intro w'
      obtain ⟨k, hk⟩ := hK.1 (z, w') hz
      have hfd : HasFDerivAt (fun u : Fin g → ℂ ↦ ((z, u) : Tot I g))
          (ContinuousLinearMap.inr ℂ (I → ℂ) (Fin g → ℂ)) w' :=
        (hasFDerivAt_const z w').prodMk (hasFDerivAt_id w')
      have hGd : HasFDerivAt G (fderiv ℂ (f k).fn (z, w')) (z, w') := by
        rw [← (hGev k _ hk).fderiv_eq]
        exact (((f k).analytic _ hk).differentiableAt.congr_of_eventuallyEq (hGev k _ hk)).hasFDerivAt
      have hL : (fderiv ℂ (f k).fn (z, w')).comp (ContinuousLinearMap.inr ℂ (I → ℂ) (Fin g → ℂ)) = 0 := by
        have hs : ∀ a : Fin g, fderiv ℂ (f k).fn (z, w') ((0, Pi.single a 1) : Tot I g) = 0 := by
          intro a
          have := Hol.fn_der ((0, Pi.single a 1) : Tot I g) (f k) hk
          rw [show Hol.der _ (f k) = dw a (f k) from rfl, h0 k a, ← Hol.ev_apply _ hk, map_zero] at this
          exact this.symm
        refine ContinuousLinearMap.ext fun v ↦ ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Finset.univ_sum_single v, map_sum, ContinuousLinearMap.zero_apply]
        refine Finset.sum_eq_zero fun a _ ↦ ?_
        have e : Pi.single a (v a) = v a • (Pi.single a 1 : Fin g → ℂ) := by
          rw [← Pi.single_smul]; simp
        rw [e, map_smul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hs a, smul_zero]
      have := hGd.comp w' hfd
      rw [hL] at this
      exact this
    exact is_const_of_fderiv_eq_zero (fun w' ↦ (hder w').differentiableAt) (fun w' ↦ (hder w').fderiv) w 0

end GlobalTheory.AnPer.Charts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoboundaryRepresentativeCocycleRules
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem map_inj_of_inj {σ O E : Type} [CommRing O] [CommRing E] (ι : O →+* E)
    (hι : Function.Injective ι) : Function.Injective (map ι : MvPowerSeries σ O → MvPowerSeries σ E) := by
  intro a b h
  ext α
  apply hι
  rw [← coeff_map, ← coeff_map, h]

theorem integral_cob_defect_rules : ∀ (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → Function.Injective (algebraMap O E) → ∀ (f : MvPowerSeries (Fin d) E) (κ : MvPowerSeries (Fin d ⊕ Fin d) O), map (algebraMap O E) κ = cob1 (up E μ) f → IsCoc μ κ ∧ (constantCoeff f = 0 → constantCoeff κ = 0) ∧ ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), map (algebraMap O E) s = defect μ n f → cob1 μ s = (n : O) • κ - pull2 (nmul μ n) κ ∧ ∀ (m : ℕ) (t u : MvPowerSeries (Fin d) O), map (algebraMap O E) t = defect μ m f → map (algebraMap O E) u = defect μ (m * n) f → u = (m : O) • s + subst (nmul μ n) t := by
  intro O E _ _ _ d μ hμ hι f κ hκ
  set ι := algebraMap O E with hιdef
  have inj2 := map_inj_of_inj (σ := Fin d ⊕ Fin d) ι hι
  have inj3 := map_inj_of_inj (σ := Fin d ⊕ (Fin d ⊕ Fin d)) ι hι
  have inj1 := map_inj_of_inj (σ := Fin d) ι hι
  obtain ⟨hlawE, hnm⟩ := _root_.GlobalTheory.isLaw_map_nmul O d μ hμ E ι
  obtain ⟨hcob1, hcob2, hswap, -, hpull⟩ := _root_.GlobalTheory.Katz.map_cob_swap_pull O d μ hμ.const E ι
  have hupμ : up E μ = fun i => map ι (μ i) := rfl
  have hconstE : ∀ i, constantCoeff (up E μ i) = 0 := hlawE.const
  have hcocE := (GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt E d (up E μ) hconstE f).2.2.2.2.2 hlawE
  have hsmul : ∀ {σ : Type} (k : ℕ) (g : MvPowerSeries σ O), map ι ((k : O) • g) = (k : E) • map ι g := by
    intro σ k g
    ext α
    simp [coeff_map, map_natCast]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · apply inj3
    rw [hcob2, ← hupμ, hκ, hcocE.1, map_zero]
  · apply inj2
    rw [hswap, hκ, hcocE.2]
  · intro hf
    apply hι
    have h1 : ι (constantCoeff κ) = constantCoeff (map ι κ) := by
      rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
    rw [h1, hκ, map_zero]
    unfold cob1 inL inR
    rw [map_sub, map_sub, GlobalTheory.Katz.SubstCalc.constantCoeff_subst_of_zero hconstE,
      GlobalTheory.Katz.SubstCalc.constantCoeff_subst_of_zero (fun i => constantCoeff_X _),
      GlobalTheory.Katz.SubstCalc.constantCoeff_subst_of_zero (fun i => constantCoeff_X _), hf]
    simp
  · intro n s hs
    have hnc : ∀ i, constantCoeff (nmul μ n i) = 0 := fun i => (hnm n i).1
    have hupn : up E (nmul μ n) = fun i => map ι (nmul μ n i) := rfl
    obtain ⟨hpl, hsb⟩ := hpull (nmul μ n) hnc
    obtain ⟨hd1, -⟩ := _root_.GlobalTheory.QLog.cob1_defect_and_defect_mul_of_isLaw O E d μ hμ f 0 n
    refine ⟨?_, ?_⟩
    · apply inj2
      rw [hcob1, ← hupμ, hs, hd1, map_sub, hsmul, hpl, hκ, ← hupn]
    · intro m t u ht hu
      obtain ⟨-, hd2⟩ := _root_.GlobalTheory.QLog.cob1_defect_and_defect_mul_of_isLaw O E d μ hμ f m n
      apply inj1
      rw [hu, hd2, map_add (f := _), hsmul, hsb, ← hupn, hs, ht]

end GlobalTheory.QLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNarrowRayClassLFunctionMulPrimeWideIndicator
section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory

theorem isRayL_mul_prime_wideInd {F : Type} [Field F] [NumberField F] (𝔪 𝔭 : Ideal (𝓞 F)) (hmax : 𝔭.IsMaximal) (hp : 𝔭 ≠ ⊥)
    (hpm : 𝔭 ⊔ 𝔪 = ⊤) (C : ClassGroup (𝓞 F)) (Z Z' : ℂ → ℂ) (hZ : IsRayL 𝔪 (wideInd C) Z)
    (hZ' : IsRayL 𝔪 (wideInd (C * (cls 𝔭)⁻¹)) Z') :
    IsRayL (𝔪 * 𝔭) (wideInd C) (fun s => Z s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) := by
  have hN : ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hp)
  refine ⟨?_, ?_⟩
  · refine hZ.1.sub (DifferentiableOn.mul (fun s _ => ?_) hZ'.1)
    exact ((differentiableAt_id.neg).const_cpow (Or.inl hN)).differentiableWithinAt
  intro s hs
  classical
  set S : Set (Ideal (𝓞 F)) := {I | CoprimeTo F 𝔪 I} with hSdef
  set A : Set (Ideal (𝓞 F)) := {I | CoprimeTo F (𝔪 * 𝔭) I} with hAdef
  set B : Set (Ideal (𝓞 F)) := {I | CoprimeTo F 𝔪 I ∧ ¬ CoprimeTo F (𝔪 * 𝔭) I} with hBdef
  let g : ClassGroup (𝓞 F) → Ideal (𝓞 F) → ℂ := fun D I => (wideInd D I : ℂ) * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)
  have h1 : HasSum (S.indicator (g C)) (Z s) := (hasSum_subtype_iff_indicator (s := S)).mp (hZ.2 s hs)
  have h2 : HasSum (S.indicator (g (C * (cls 𝔭)⁻¹))) (Z' s) :=
    (hasSum_subtype_iff_indicator (s := S)).mp (hZ'.2 s hs)
  have hAS : ∀ I, CoprimeTo F (𝔪 * 𝔭) I → CoprimeTo F 𝔪 I := fun I h =>
    ⟨h.1, eq_top_iff.mpr (h.2.symm.le.trans (sup_le_sup_left Ideal.mul_le_left _))⟩
  have hsplit : S.indicator (g C) = A.indicator (g C) + B.indicator (g C) := by
    funext I
    simp only [Pi.add_apply, Set.indicator, hSdef, hAdef, hBdef, Set.mem_setOf_eq]
    by_cases hA : CoprimeTo F (𝔪 * 𝔭) I
    · simp [hA, hAS I hA]
    · by_cases hS : CoprimeTo F 𝔪 I <;> simp [hA, hS]

  have hmulS : ∀ J, CoprimeTo F 𝔪 J → 𝔭 * J ∈ B := by
    intro J hJ
    refine ⟨⟨mul_ne_zero hp hJ.1, ?_⟩, fun h => ?_⟩
    · rw [sup_comm, Ideal.sup_mul_eq_of_coprime_left (by rwa [sup_comm]), sup_comm]; exact hJ.2
    · have : 𝔭 * J ⊔ 𝔭 = 𝔭 := sup_eq_right.mpr Ideal.mul_le_left
      have htop : 𝔭 * J ⊔ 𝔭 = ⊤ := eq_top_iff.mpr (h.2.symm.le.trans (sup_le_sup_left Ideal.mul_le_right _))
      exact hmax.ne_top (this.symm.trans htop)
  have hnot : ∀ J, ¬ CoprimeTo F 𝔪 J → 𝔭 * J ∉ B := by
    intro J hJ hB
    apply hJ
    refine ⟨fun h0 => hB.1.1 (by simp [h0]), eq_top_iff.mpr (hB.1.2.symm.le.trans (sup_le_sup_right Ideal.mul_le_right _))⟩
  have hB_range : ∀ I ∈ B, ∃ J, 𝔭 * J = I := by
    intro I hI
    have hItop : I ⊔ 𝔭 ≠ ⊤ := by
      intro h
      apply hI.2
      refine ⟨hI.1.1, ?_⟩
      rw [Ideal.sup_mul_eq_of_coprime_right h]; exact hI.1.2
    have hle : I ≤ 𝔭 := le_sup_left.trans (hmax.eq_of_le hItop le_sup_right).ge
    obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
    exact ⟨J, hJ.symm⟩
  have hinj : Function.Injective (fun J : Ideal (𝓞 F) => 𝔭 * J) := fun J J' h => mul_left_cancel₀ hp h
  have hcomp : (B.indicator (g C)) ∘ (fun J => 𝔭 * J) =
      fun J => ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * S.indicator (g (C * (cls 𝔭)⁻¹)) J := by
    funext J
    simp only [Function.comp_apply]
    by_cases hJ : CoprimeTo F 𝔪 J
    · rw [Set.indicator_of_mem (hmulS J hJ), Set.indicator_of_mem (show J ∈ S from hJ)]
      simp only [g, wideInd]
      rw [cls_mul hp hJ.1, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      have : (cls 𝔭 * cls J = C) ↔ (cls J = C * (cls 𝔭)⁻¹) := by
        rw [eq_mul_inv_iff_mul_eq, mul_comm]
      by_cases hc : cls J = C * (cls 𝔭)⁻¹
      · simp [hc, this.mpr hc]
      · simp [hc, mt this.mp hc]
    · rw [Set.indicator_of_notMem (hnot J hJ), Set.indicator_of_notMem (show J ∉ S from hJ), mul_zero]
  have h3 : HasSum (B.indicator (g C)) (((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) := by
    rw [← hinj.hasSum_iff (fun I hI => ?_), hcomp]
    · exact h2.mul_left _
    · by_contra hne
      obtain ⟨J, rfl⟩ := hB_range I (Set.mem_of_indicator_ne_zero hne)
      exact hI ⟨J, rfl⟩
  have h4 : HasSum (A.indicator (g C)) (Z s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) := by
    have := h1.sub h3
    rw [hsplit] at this
    have e : (fun b => (A.indicator (g C) + B.indicator (g C)) b - B.indicator (g C) b) = A.indicator (g C) := by
      funext I; simp
    rwa [e] at this
  exact (hasSum_subtype_iff_indicator (s := A)).mpr h4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfNilpotentDividedPowersIdeal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem isNilpotent_of_isDPNilpotent : ∀ {D : Type} [CommRing D] [Algebra ℂ D] {J : Ideal D}
    (dl : DividedPowers J), IsNilDP dl → IsNilpotent J := by
  intro D _ _ J dl hdl
  obtain ⟨N, h⟩ := hdl
  have h0 : ∀ l : List D, (∀ b ∈ l, b ∈ J) → N ≤ l.length → l.prod = 0 := by
    intro l hl hN
    have k := h (l.map fun b ↦ (1, b)) (by simpa using hl)
      (by simpa [List.map_map, Function.comp_def] using hN)
    rw [List.map_map] at k
    have e : l.map ((fun p : ℕ × D ↦ dl.dpow p.1 p.2) ∘ fun b ↦ (1, b)) = l.map id :=
      List.map_congr_left fun b hb ↦ dl.dpow_one (hl b hb)
    rwa [e, List.map_id] at k
  have key : ∀ n : ℕ, ∀ x ∈ J ^ n, ∀ l : List D, (∀ b ∈ l, b ∈ J) →
      N ≤ n + l.length → x * l.prod = 0 := by
    intro n
    induction n with
    | zero => intro x _ l hl hN; rw [h0 l hl (by simpa using hN), mul_zero]
    | succ n ih =>
      intro x hx l hl hN
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_)
        fun a b ha hb ↦ by rw [add_mul, ha, hb, add_zero]
      have := ih a ha (b :: l) (by simpa using ⟨hb, hl⟩) (by simp; omega)
      rwa [List.prod_cons, ← _root_.mul_assoc] at this
  refine ⟨N, eq_bot_iff.2 fun x hx ↦ ?_⟩
  simpa using key N x hx [] (by simp) (by simp)

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParameterTaylorExpansionHomApplyOfParamOnly
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem isTay_apply_of_fn_eq_param : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (f : (I → ℂ) → ℂ), (∀ p ∈ W, h.fn p = f p.1) → ρ h = GlobalTheory.PeriodFamily.taylor N t f ⊗ₜ[ℂ] 1 := by
  intro I _ _ g R _ _ N t W W₀ h0 ρ hρ h f hf
  apply GlobalTheory.tensor_hol_ext_of_values W₀ R
  intro p hp
  have e1 := hρ h p hp
  have e2 : (fun z : I → ℂ ↦ h.fn (z, p.2)) =ᶠ[𝓝 0] f := by
    have hc : Continuous (fun z : I → ℂ ↦ ((z, p.2) : Tot I g)) := continuous_id.prodMk continuous_const
    have hm : ∀ᶠ z in 𝓝 (0 : I → ℂ), ((z, p.2) : Tot I g) ∈ W :=
      hc.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds (h0 p hp))
    filter_upwards [hm] with z hz using hf _ hz
  have e3 := (GlobalTheory.PeriodFamily.taylor_formal_properties (D := R) N t).2.2.2.1 _ _ e2
  change evT R p hp (ρ h) = evT R p hp (GlobalTheory.PeriodFamily.taylor N t f ⊗ₜ[ℂ] (1 : Hol W₀))
  rw [e1, e3]
  simp [evT, Algebra.TensorProduct.lift_tmul]

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParameterTaylorExpansionHomFibreDerivation
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer

variable {I : Type} [Fintype I] [DecidableEq I] {g : ℕ}

def slTayCoef {W : Opens (Tot I g)} (h : Hol W) (k : ℕ) (s : Fin k → I) (p : Tot Empty g) : ℂ :=
  (k.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ k (fun z ↦ h.fn (z, p.2)) 0 fun b ↦ Pi.single (s b) 1

theorem slTayCoef_analytic {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (h : Hol W) (k : ℕ) (s : Fin k → I) :
    AnalyticOnNhd ℂ (slTayCoef h k s) W₀ := fun p hp ↦ by
  have hA : AnalyticAt ℂ h.fn ((0 : I → ℂ), p.2) := h.analytic _ (hW p hp)
  have hG := (analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k (fun b ↦ Pi.single (s b) 1) hA).1
  exact analyticAt_const.mul (hG.comp analyticAt_snd)

def slTayHol {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (h : Hol W) (k : ℕ) (s : Fin k → I) : Hol W₀ :=
  Hol.mk (slTayCoef h k s) (slTayCoef_analytic hW h k s)

theorem isTay_expand {R : Type} [CommRing R] [Algebra ℂ R] {N : ℕ} {t : I → R} {W : Opens (Tot I g)}
    {W₀ : Opens (Tot Empty g)} (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W)
    {ρ : Hol W →+* R ⊗[ℂ] Hol W₀} (hρ : IsTay N t ρ) (h : Hol W) :
    ρ h = ∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → I, (∏ b, t (s b)) ⊗ₜ[ℂ] slTayHol hW h k s := by
  refine tensor_hol_ext_of_values W₀ R _ _ fun p hp ↦ ?_
  have e := hρ h p hp
  change evT R p hp (ρ h) = evT R p hp _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  unfold GlobalTheory.PeriodFamily.taylor
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Hol.ev_apply, slTayHol, Hol.fn_mk _ _ hp,
    Algebra.smul_def, mul_comm]
  rfl

theorem dw_slTayHol {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (a : Fin g) (h : Hol W) (k : ℕ) (s : Fin k → I) :
    dw a (slTayHol hW h k s) = slTayHol hW (dw a h) k s := by
  refine Hol.ext_fn fun p hp ↦ ?_
  have hA : AnalyticAt ℂ h.fn ((0 : I → ℂ), p.2) := h.analytic _ (hW p hp)
  obtain ⟨hG, hD⟩ := analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k (fun b ↦ Pi.single (s b) 1) hA
  have e1 : slTayCoef h k s = (fun w : Fin g → ℂ ↦ (k.factorial : ℂ)⁻¹ *
      iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 fun b ↦ Pi.single (s b) 1) ∘ Prod.snd := rfl
  have hG' : DifferentiableAt ℂ (fun w : Fin g → ℂ ↦ (k.factorial : ℂ)⁻¹ *
      iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 fun b ↦ Pi.single (s b) 1) p.2 :=
    hG.differentiableAt.const_mul _
  have hev : (fun z : I → ℂ ↦ fderiv ℂ h.fn (z, p.2) ((0 : I → ℂ), Pi.single a 1)) =ᶠ[𝓝 0]
      fun z ↦ (dw a h).fn (z, p.2) := by
    have hc : Continuous fun z : I → ℂ ↦ ((z, p.2) : Tot I g) := continuous_id.prodMk continuous_const
    filter_upwards [hc.continuousAt.eventually_mem (W.isOpen.mem_nhds (hW p hp))] with z hz
    rw [dw, Hol.fn_der _ _ hz]
  rw [slTayHol, slTayHol, Hol.fn_mk _ _ hp, dw, Hol.fn_der _ _ hp,
    Hol.fderiv_fn_congr _ (F := slTayCoef h k s) (fun q hq ↦ Hol.fn_mk _ _ hq) hp, e1,
    fderiv_comp p hG' differentiableAt_snd, fderiv_snd,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', fderiv_const_mul hG.differentiableAt,
    ContinuousLinearMap.smul_apply, hD, smul_eq_mul]
  unfold slTayCoef
  congr 1
  exact (Filter.EventuallyEq.iteratedFDeriv ℂ hev k).eq_of_nhds ▸ rfl

theorem isTay_dw_lTensor : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type}
    [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)),
    (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) →
    ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (a : Fin g) (h : Hol W),
      ρ (dw a h) = LinearMap.lTensor R (dw (W := W₀) a).toLinearMap (ρ h) := by
  intro I _ _ g R _ _ N t W W₀ hW ρ hρ a h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [isTay_expand hW hρ (dw a h), isTay_expand hW hρ h, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [LinearMap.lTensor_tmul, ← dw_slTayHol hW a h k s]
  rfl

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveTensorOfFibreProjectiveStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_tensor_of_fibre_projective' : ∀ (C k B : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Field k] [CommRing B] (σ : C →+* k), Function.Surjective σ → ∀ (H V : Type 1) [AddCommGroup H] [Module C H] [AddCommGroup V] [Module k V] (ρ : B →+* Module.End C H) (ρ' : B →+* Module.End k V) (f : H →ₛₗ[σ] V), Module.Finite C H → Module.Projective C H → Function.Surjective f → (∀ h, f h = 0 → h ∈ RingHom.ker σ • (⊤ : Submodule C H)) → (∀ x h, f (ρ x h) = ρ' x (f h)) → (letI := GlobalTheory.HTSummand.tensorModOf ρ'; Module.Projective (k ⊗[ℤ] B) V) → letI := GlobalTheory.HTSummand.tensorModOf ρ; Module.Projective (C ⊗[ℤ] B) H := by
  first | exact @GlobalTheory.HTSummand.projective_tensor_of_fibre_projective | exact GlobalTheory.HTSummand.projective_tensor_of_fibre_projective | (intros; apply GlobalTheory.HTSummand.projective_tensor_of_fibre_projective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependentStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_spec_twist_independent : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) → ∀ n i j : ℤ, Nonempty (Ht q (sp A) n i ≃+ Ht q (sp A) n j) := by
  first | (exact @GlobalTheory.EtC.untwist) | (exact GlobalTheory.EtC.untwist) | (intros; apply GlobalTheory.EtC.untwist  <;> assumption)
end

