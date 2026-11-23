module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianPairingIntegralContDiffNeZeroDiag

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompFinIdemSum

variable {D : D7}

theorem compFin_tensAt_ne {u v : HeightOneSpectrum (𝓞 D.host.F)} (h : u ≠ v)
    (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    compFin D.host.F D.host.E u (GlobalTheory.EmbChart.tensAt D.host.E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    rw [GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]
    have h0 : evFin D.host.F u (pairA D.host.F 0 (singleFin v a)) = 0 := evalV_singleFin_ne h a
    have h1 : compFin D.host.F D.host.E u (pairA D.host.F 0 (singleFin v a) ⊗ₜ[D.host.F] x) =
        evFin D.host.F u (pairA D.host.F 0 (singleFin v a)) ⊗ₜ[D.host.F] x :=
      Algebra.TensorProduct.map_tmul ..
    rw [h1, h0, TensorProduct.zero_tmul]
  | add y z hy hz => simp only [map_add (f := _), hy, hz, add_zero]


set_option maxHeartbeats 1000000 in
open Classical in
theorem compFin_add_cA_eq_one : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ PP ∈ Z,
    compFin D.host.F D.host.E ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (e + cA D e) = 1 := by
  intro D Z e he PP hPP
  classical
  obtain ⟨⟨es, hes, rfl⟩, hcc⟩ := he
  obtain ⟨v0, τ0, -, hPP0⟩ := GlobalTheory.SplitIdemDict.exists_emb (hes PP hPP)
  have hu : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v0 := by rw [hPP0]; exact splitPrime_under τ0
  rw [hu]
  have key : ∀ Q ∈ Z, compFin D.host.F D.host.E v0 (es Q) =
      (if Q = PP then splitIdem (isCMExt_host D) τ0 else 0) +
        (if Q = splitPrime (τ0.comp D.sp.cm.sig) then 1 - splitIdem (isCMExt_host D) τ0 else 0) := by
    intro Q hQ
    obtain ⟨v, τ, hI, hQτ⟩ := GlobalTheory.SplitIdemDict.exists_emb (hes Q hQ)
    have hQv : Q.under (𝓞 D.host.F) = v := by rw [hQτ]; exact splitPrime_under τ
    rw [GlobalTheory.SplitIdemDict.eq_idem hI, GlobalTheory.EmbChart.idem]
    by_cases hv : v = v0
    · subst hv
      rcases eq_or_eq_comp_conj (isCMExt_host D) τ0 τ with h | h <;> rw [h] at hQτ ⊢
      · rw [if_pos (hQτ.trans hPP0.symm), if_neg (by rw [hQτ]; exact (splitPrime_comp_ne (isCMExt_host D) τ0).symm),
          add_zero]
        exact GlobalTheory.EmbChart.compFin_tensAt _ _
      · rw [if_neg (by rw [hQτ, hPP0]; exact splitPrime_comp_ne (isCMExt_host D) τ0), if_pos hQτ, zero_add,
          GlobalTheory.EmbChart.compFin_tensAt, splitIdem_comp]
    · have h1 : Q ≠ PP := fun h => hv (by rw [← hQv, h, hu])
      have h2 : Q ≠ splitPrime (τ0.comp D.sp.cm.sig) := fun h => hv (by rw [← hQv, h]; exact splitPrime_under _)
      rw [if_neg h1, if_neg h2, add_zero]
      exact compFin_tensAt_ne (Ne.symm hv) _
  have hsum : compFin D.host.F D.host.E v0 (∑ Q ∈ Z, es Q) = splitIdem (isCMExt_host D) τ0 +
      (if splitPrime (τ0.comp D.sp.cm.sig) ∈ Z then 1 - splitIdem (isCMExt_host D) τ0 else 0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_congr rfl key]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos hPP]
  have hc : compFin D.host.F D.host.E v0 (cA D (∑ Q ∈ Z, es Q)) =
      sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v0 (∑ Q ∈ Z, es Q)) :=
    (GlobalTheory.SplitIdemDict.compFin_cA _).symm
  have h1 : ∀ a : Fv D.host.F v0 ⊗[D.host.F] D.host.E, a + (1 - a) = 1 := fun a => by abel
  rw [map_add (f := _), hc, hsum]
  by_cases hP' : splitPrime (τ0.comp D.sp.cm.sig) ∈ Z
  · exfalso
    have hz := congrArg (compFin D.host.F D.host.E v0) hcc
    rw [map_mul, hc, hsum, if_pos hP', h1, map_one, mul_one, map_zero] at hz
    have h3 := congrArg (fun y => splitProj τ0 y) hz
    simp only [map_one, map_zero] at h3
    exact one_ne_zero h3
  · rw [if_neg hP', add_zero, sigR_splitIdem, h1]

end GlobalTheory.CompFinIdemSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoundedAutomorphicRightTranslationUnitarisableBo
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct

namespace GlobalTheory.FinZeta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {V : HSp D} {ν : Measure (GA D V)} {𝓕 : Set (GA D V)}

private theorem zero_one_mem_gammaSet_one (f : bddAut V) : Continuous (f : GA D V → ℂ) ∧
    (∀ γ ∈ GQ V, ∀ g, (f : GA D V → ℂ) (γ * g) = (f : GA D V → ℂ) g) ∧
    ∃ C : ℝ, ∀ g, ‖(f : GA D V → ℂ) g‖ ≤ C := f.2

private theorem integrableOn_fundamentalDomain_of_bounded {E : Type} [NormedAddCommGroup E] (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) {φ : GA D V → E} (hφ : Continuous φ) (C : ℝ)
    (hC : ∀ g, ‖φ g‖ ≤ C) : IntegrableOn φ 𝓕 ν := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.1
  haveI := hT.2.2.2.1
  exact Measure.integrableOn_of_bounded
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V ν 𝓕 hν h𝓕).ne hφ.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

theorem integrableOn_mul_conj_bddAut (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (f f₂ : bddAut V) :
    IntegrableOn (fun g => (f : GA D V → ℂ) g * starRingEnd ℂ ((f₂ : GA D V → ℂ) g)) 𝓕 ν := by
  obtain ⟨hc, -, C, hC⟩ := zero_one_mem_gammaSet_one f
  obtain ⟨hc₂, -, C₂, hC₂⟩ := zero_one_mem_gammaSet_one f₂
  refine integrableOn_fundamentalDomain_of_bounded hν h𝓕 (hc.mul (Complex.continuous_conj.comp hc₂)) (C * C₂) fun g => ?_
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hC g) (hC₂ g) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))

theorem exists_form_bddAut (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) :
    ∃ B : bddAut V →ₗ[ℂ] bddAut V →ₛₗ[starRingEnd ℂ] ℂ, ∀ f f₂, B f f₂ = l2 ν 𝓕 (f : GA D V → ℂ) f₂ := by
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun f f₂ : bddAut V => l2 ν 𝓕 (f : GA D V → ℂ) f₂) ?_ ?_ ?_ ?_, fun f f₂ => rfl⟩
  · intro a b c
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (integrableOn_mul_conj_bddAut hν h𝓕 a c) (integrableOn_mul_conj_bddAut hν h𝓕 b c)
  · intro c a b
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, mul_assoc]
    exact integral_const_mul c _
  · intro a b c
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_add, Pi.add_apply, map_add (f := _), mul_add]
    exact integral_add (integrableOn_mul_conj_bddAut hν h𝓕 a b) (integrableOn_mul_conj_bddAut hν h𝓕 a c)
  · intro c a b
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring

theorem petersson_self_re_pos_of_ne_zero (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (f : bddAut V) (hf : f ≠ 0) :
    0 < (l2 ν 𝓕 (f : GA D V → ℂ) f).re := by
  haveI := hν
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := hT.2.2.2.2.2.2
  obtain ⟨hc, hi, C, hC⟩ := zero_one_mem_gammaSet_one f
  have key : l2 ν 𝓕 (f : GA D V → ℂ) f =
      ((∫ x in 𝓕, Complex.normSq ((f : GA D V → ℂ) x) ∂ν : ℝ) : ℂ) := by
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Complex.mul_conj]
    exact integral_ofReal
  rw [key, Complex.ofReal_re]
  have hint : IntegrableOn (fun x => Complex.normSq ((f : GA D V → ℂ) x)) 𝓕 ν :=
    integrableOn_fundamentalDomain_of_bounded hν h𝓕 (Complex.continuous_normSq.comp hc) (C * C) fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, sq]
      exact mul_le_mul (hC g) (hC g) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => Complex.normSq_nonneg _) hint]
  set U : Set (GA D V) := {x | (f : GA D V → ℂ) x ≠ 0} with hUdef
  have hsupp : Function.support (fun x => Complex.normSq ((f : GA D V → ℂ) x)) = U := by
    ext x
    simp [U, Complex.normSq_eq_zero]
  rw [hsupp]
  have hU : IsOpen U := isOpen_ne_fun hc continuous_const
  have hne : U.Nonempty := by
    by_contra hE
    rw [Set.not_nonempty_iff_eq_empty] at hE
    apply hf
    apply Subtype.ext
    funext x
    by_contra hx
    have hx' : x ∈ U := hx
    rw [hE] at hx'
    exact hx'
  refine pos_iff_ne_zero.2 fun h0 => (hU.measure_pos ν hne).ne' ?_
  have hsub : U ⊆ {x | ¬ ∃ γ : GQ V, γ • x ∈ 𝓕} ∪
      ⋃ γ : GQ V, (fun x => (γ : GA D V) * x) ⁻¹' (U ∩ 𝓕) := by
    intro x hx
    by_cases hx' : ∃ γ : GQ V, γ • x ∈ 𝓕
    · obtain ⟨γ, hγ⟩ := hx'
      refine Or.inr (Set.mem_iUnion.2 ⟨γ, ?_, hγ⟩)
      show (f : GA D V → ℂ) ((γ : GA D V) * x) ≠ 0
      rw [hi γ γ.2]
      exact hx
    · exact Or.inl hx'
  refine measure_mono_null hsub (measure_union_null (ae_iff.1 h𝓕.ae_covers) ?_)
  refine measure_iUnion_null fun γ => ?_
  rw [measure_preimage_mul]
  exact h0

theorem petersson_bounded_automorphic_right_translation_invariant (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (g : GA D V) (f f₂ : bddAut V) :
    l2 ν 𝓕 (bddRep V g f : GA D V → ℂ) (bddRep V g f₂ : GA D V → ℂ) = l2 ν 𝓕 (f : GA D V → ℂ) f₂ := by
  haveI := hν
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := hT.2.2.2.2.2.2
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V ν hν).1
  obtain ⟨-, hi, -⟩ := zero_one_mem_gammaSet_one f
  obtain ⟨-, hi₂, -⟩ := zero_one_mem_gammaSet_one f₂
  rw [coe_bddRep, coe_bddRep]
  simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, rTr]
  exact GlobalTheory.setIntegral_fundamentalDomain_mul_right h𝓕 g
    (fun x => (f : GA D V → ℂ) x * starRingEnd ℂ ((f₂ : GA D V → ℂ) x))
    fun γ hγ x => by simp only [hi γ hγ, hi₂ γ hγ]

end

theorem bddRep_unitarisable_and_bounded : ∀ (D : D7) (V : HSp D), IsUnitarisable (bddRep V) ∧ ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν → ∀ f₂ : bddAut V, ∃ ℓ : bddAut V →ₗ[ℂ] ℂ, (∀ f : bddAut V, ℓ f = l2 ν 𝓕 (f : GA D V → ℂ) f₂) ∧ ∀ f : bddAut V, ∃ C : ℝ, ∀ g, ‖ℓ (bddRep V g f)‖ ≤ C := by
  intro D V
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.1
  haveI := hT.2.1
  haveI := hT.2.2.1
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  refine ⟨?_, fun ν 𝓕 hν h𝓕 f₂ => ?_⟩
  · have hH : (Measure.haar : Measure (GA D V)).IsHaarMeasure := inferInstance
    obtain ⟨𝓕, h𝓕⟩ :=
      (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V Measure.haar hH).2
    obtain ⟨B, hB⟩ := exists_form_bddAut hH h𝓕
    unfold IsUnitarisable
    refine ⟨B, fun v w => ?_, fun v hv => ?_, fun g v w => ?_⟩
    · rw [hB, hB]
      simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet]
      rw [← integral_conj]
      congr 1
      funext x
      rw [map_mul, Complex.conj_conj, mul_comm]
    · rw [hB]
      exact petersson_self_re_pos_of_ne_zero hH h𝓕 v hv
    · rw [hB, hB]
      exact petersson_bounded_automorphic_right_translation_invariant hH h𝓕 g v w
  · obtain ⟨B, hB⟩ := exists_form_bddAut hν h𝓕
    refine ⟨{ toFun := fun f => B f f₂, map_add' := fun a b => by simp, map_smul' := fun c a => by simp },
      fun f => hB f f₂, fun f => ?_⟩
    obtain ⟨-, -, C, hC⟩ := zero_one_mem_gammaSet_one f
    obtain ⟨-, -, C₂, hC₂⟩ := zero_one_mem_gammaSet_one f₂
    have hfin := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V ν 𝓕 hν h𝓕
    refine ⟨C * C₂ * (ν 𝓕).toReal, fun g => ?_⟩
    show ‖B (bddRep V g f) f₂‖ ≤ _
    rw [hB, coe_bddRep]
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, rTr]
    refine norm_setIntegral_le_of_norm_le_const hfin fun x _ => ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC _) (hC₂ _) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))

end GlobalTheory.FinZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardMulFinrankSubgroupEigenspaceOfTraceVanishesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_mul_finrank_subgroupEigenspace_of_trace_vanishes : ∀ (G M : Type) [Group G] [Finite G] [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M) (P : Subgroup G) (χ : P →* ℂˣ), (∀ g ∈ P, g ≠ 1 → LinearMap.trace ℂ M (ρ g) = 0) → Nat.card P * Module.finrank ℂ (eig ρ P fun g => ((χ g : ℂˣ) : ℂ)) = Module.finrank ℂ M := by
  first | exact @GlobalTheory.DefFree.card_mul_finrank_eig | exact GlobalTheory.DefFree.card_mul_finrank_eig | (intros; apply GlobalTheory.DefFree.card_mul_finrank_eig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassTermConvergesOfLintegralUnfoldingEq
section
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

namespace GlobalTheory.ClassTerm

theorem hasClassInt_of_lintegral_eq : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H), γ ∈ Γ → ∀ (μ : Measure H) (𝓕 : Set H) (ν : Measure (Quot (cent γ))) (a : ℝ≥0∞), a < ⊤ → (∀ G : H → ℝ≥0∞, Measurable G → ∫⁻ x in 𝓕, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) ∂μ = a * ∫⁻ q, G (q.out⁻¹ * γ * q.out) ∂ν) → ∀ (f : H → ℂ) (c : ℂ), Continuous f → HasCompactSupport f → Integrable (fun q : Quot (cent γ) => f (q.out⁻¹ * γ * q.out)) ν → ∫ q, f (q.out⁻¹ * γ * q.out) ∂ν = c → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt Γ μ 𝓕 γ f (a.toReal * c) := by
  intro H _ _ _ _ _ _ _ _ Γ _ γ hγ μ 𝓕 ν a ha hL f c hf hfc hint hc
  classical
  have hmemΓ : ∀ δ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, δ ∈ Γ := by
    rintro _ ⟨g, hg, rfl⟩
    exact mul_mem (mul_mem (inv_mem hg) hγ) hg
  let ι : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ → Γ := fun δ => ⟨δ, hmemΓ _ δ.2⟩
  have hι : Function.Injective ι := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  haveI : Countable (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ) := hι.countable
  have hcont : ∀ δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, Continuous fun x : H => x⁻¹ * (δ : H) * x := fun δ => by
    fun_prop
  have hfm : Measurable f := hf.measurable
  have hfs : StronglyMeasurable f := hf.stronglyMeasurable

  have hfin : ∀ x, (Function.support fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ => f (x⁻¹ * δ * x)).Finite := by
    intro x
    have hC : IsCompact ((fun z => x * z * x⁻¹) '' tsupport f) := hfc.isCompact.image (by fun_prop)
    refine ((finite_mem_compact (Γ := Γ) hC).preimage hι.injOn).subset ?_
    intro δ hδ
    refine ⟨x⁻¹ * δ * x, subset_tsupport f hδ, ?_⟩
    show x * (x⁻¹ * (δ : H) * x) * x⁻¹ = δ
    group
  have hsum : ∀ x, Summable fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ => f (x⁻¹ * δ * x) := fun x =>
    summable_of_hasFiniteSupport (hfin x)

  have hem : Measurable (fun q : Quot (cent γ) => q.out⁻¹ * γ * q.out) := by
    have hli : LeftInv (cent γ) (fun x : H => x⁻¹ * γ * x) := by
      intro t ht x
      have hcomm : γ * t = t * γ := Subgroup.mem_centralizer_iff.1 ht γ (Set.mem_singleton γ)
      have h1 : t⁻¹ * γ * t = γ := by rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
      calc (t * x)⁻¹ * γ * (t * x) = x⁻¹ * (t⁻¹ * γ * t) * x := by group
        _ = x⁻¹ * γ * x := by rw [h1]
    exact measurable_descend hli (by fun_prop : Continuous fun x : H => x⁻¹ * γ * x).measurable
  set m1 : Measure H := Measure.sum fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ =>
    (μ.restrict 𝓕).map (fun x => x⁻¹ * (δ : H) * x) with hm1
  set m2 : Measure H := a • ν.map (fun q : Quot (cent γ) => q.out⁻¹ * γ * q.out) with hm2
  have hm12 : m1 = m2 := Measure.ext_of_lintegral _ fun G hG => by
    rw [hm1, hm2, lintegral_sum_measure, lintegral_smul_measure, lintegral_map hG hem,
      tsum_congr (fun δ => lintegral_map hG (hcont δ).measurable), smul_eq_mul, ← hL G hG]
    exact (lintegral_tsum (f := fun (δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ) x => G (x⁻¹ * (δ : H) * x))
      (fun δ => (hG.comp (hcont δ).measurable).aemeasurable)).symm
  have hint2 : Integrable f (ν.map fun q : Quot (cent γ) => q.out⁻¹ * γ * q.out) :=
    (integrable_map_measure hfs.aestronglyMeasurable hem.aemeasurable).2 hint
  have hintm2 : Integrable f m2 := hint2.smul_measure ha.ne
  have hintm1 : Integrable f m1 := hm12 ▸ hintm2
  have hval2 : ∫ x, f x ∂m2 = (a.toReal : ℂ) * c := by
    rw [hm2, integral_smul_measure, integral_map hem.aemeasurable hfs.aestronglyMeasurable, hc, Complex.real_smul]
  have hval1 : ∫ x, f x ∂m1 = ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, ∫ x in 𝓕, f (x⁻¹ * δ * x) ∂μ := by
    rw [hm1, integral_sum_measure (hm1 ▸ hintm1)]
    exact tsum_congr fun δ => integral_map (hcont δ).measurable.aemeasurable hfs.aestronglyMeasurable
  have hfinL : ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, ∫⁻ x in 𝓕, ‖f (x⁻¹ * δ * x)‖ₑ ∂μ ≠ ∞ := by
    have h := hintm1.hasFiniteIntegral
    change ∫⁻ x, ‖f x‖ₑ ∂m1 < ∞ at h
    rw [hm1, lintegral_sum_measure] at h
    refine ne_of_lt (lt_of_eq_of_lt (tsum_congr fun δ => ?_) h)
    exact (lintegral_map hfm.enorm (hcont δ).measurable).symm
  have hKm : Measurable (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel Γ γ f) :=
    measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ)))
      (f := fun (s : Finset (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ)) x => ∑ δ ∈ s, f (x⁻¹ * (δ : H) * x))
      (fun s => Finset.measurable_sum s fun δ _ => hfm.comp (hcont δ).measurable)
      (tendsto_pi_nhds.2 fun x => (hsum x).hasSum)
  refine ⟨hsum, ⟨hKm.aestronglyMeasurable, ?_⟩, ?_⟩
  · change ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel Γ γ f x‖ₑ ∂μ.restrict 𝓕 < ∞
    calc ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel Γ γ f x‖ₑ ∂μ.restrict 𝓕
        ≤ ∫⁻ x, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, ‖f (x⁻¹ * δ * x)‖ₑ ∂μ.restrict 𝓕 :=
          lintegral_mono fun x => enorm_tsum_le_tsum_enorm
      _ = ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, ∫⁻ x in 𝓕, ‖f (x⁻¹ * δ * x)‖ₑ ∂μ :=
          lintegral_tsum (fun δ => (hfm.comp (hcont δ).measurable).enorm.aemeasurable)
      _ < ∞ := hfinL.lt_top
  · show ∫ x in 𝓕, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, f (x⁻¹ * δ * x) ∂μ = _
    rw [integral_tsum (f := fun (δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ) x => f (x⁻¹ * (δ : H) * x)) (fun δ => (hfm.comp (hcont δ).measurable).aestronglyMeasurable) hfinL, ← hval1, hm12, hval2]

end GlobalTheory.ClassTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjLocalTwistedLFactorRatioInertEqZetaSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

theorem conj_LvTw_div_dLoc_inert : ∀ (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w) → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 → (B w).map star = B w → (m w : ℂ) = (-1) ^ D.R.nV → quadSign D v = -1 → starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) = eulerFac (B w) (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.t + 1))⁻¹) * ∏ j ∈ Finset.range D.R.r, (1 - (-(qV D.host.F v : ℂ)) ^ j * (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.r + D.R.t))⁻¹)) := by
  intro D B m v w hv hq hB hm hs
  set q : ℕ := Ideal.absNorm v.asIdeal with hqdef
  have hqV : qV D.host.F v = q := rfl
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (GlobalTheory.LFun.one_lt_absNorm v).ne_bot
  have hstar : ((star (m w) : ℂˣ) : ℂ) = (-1) ^ D.R.nV := by
    rw [Units.coe_star, hm]; simp
  have hinv : ((m w : ℂ))⁻¹ = (-1) ^ D.R.nV := by rw [hm, ← inv_pow, inv_neg, inv_one]
  have hnp : npow v (-(2 * ((1 + (D.R.t : ℂ)) / 2))) = ((q : ℂ) ^ (D.R.t + 1))⁻¹ := by
    rw [npow, show -(2 * ((1 + (D.R.t : ℂ)) / 2)) = -((D.R.t + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.cpow_neg, Complex.cpow_natCast]
  rw [LvTw_inert B m hv hq, hnp, hinv, hstar, hqV, map_div₀, Complex.conj_ofReal]
  have hx : starRingEnd ℂ ((-1 : ℂ) ^ D.R.nV * ((q : ℂ) ^ (D.R.t + 1))⁻¹) =
      (-1 : ℂ) ^ D.R.nV * ((q : ℂ) ^ (D.R.t + 1))⁻¹ := by simp
  have hconjE : starRingEnd ℂ (eulerFac (B w) ((-1 : ℂ) ^ D.R.nV * ((q : ℂ) ^ (D.R.t + 1))⁻¹)) =
      eulerFac (B w) ((-1 : ℂ) ^ D.R.nV * ((q : ℂ) ^ (D.R.t + 1))⁻¹) := by
    conv_rhs => rw [← hB]
    simp only [eulerFac, eulerPoly, map_inv₀, map_multiset_prod, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, map_sub, map_one, map_mul, Units.coe_star, hx]
    rfl
  rw [hconjE, div_eq_mul_inv]
  congr 1
  have hqt : ∀ i : ℕ, quadTerm D v i = (-1 : ℝ) ^ i / (q : ℝ) ^ i := by
    intro i; rw [quadTerm, hs]
  have hd : ((dLoc D v : ℝ) : ℂ)⁻¹ = ∏ i ∈ Finset.Ioc D.R.t (D.R.r + D.R.t), (1 - (-1 : ℂ) ^ i / (q : ℂ) ^ i) := by
    rw [dLoc, Complex.ofReal_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr (by rfl) fun i _ => ?_
    rw [Complex.ofReal_inv, inv_inv, hqt]
    push_cast; ring
  rw [hd]
  have key : ∀ a j : ℕ, (-1 : ℂ) ^ a / (q : ℂ) ^ a = (-(q : ℂ)) ^ j * ((-1 : ℂ) ^ (a + j) * ((q : ℂ) ^ (a + j))⁻¹) := by
    intro a j
    calc (-1 : ℂ) ^ a / (q : ℂ) ^ a = ((-1 : ℂ) ^ j * (-1) ^ j) * ((-1 : ℂ) ^ a / (q : ℂ) ^ a) * ((q : ℂ) ^ j * ((q : ℂ) ^ j)⁻¹) := by
          rw [← mul_pow, neg_one_mul, neg_neg, one_pow, mul_inv_cancel₀ (pow_ne_zero _ hq0)]; ring
      _ = _ := by rw [neg_pow, pow_add, pow_add, mul_inv]; ring
  refine Finset.prod_nbij' (fun i => D.R.r + D.R.t - i) (fun j => D.R.r + D.R.t - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi; rw [Finset.mem_Ioc] at hi; rw [Finset.mem_range]; omega
  · intro j hj; rw [Finset.mem_range] at hj; rw [Finset.mem_Ioc]; omega
  · intro i hi; rw [Finset.mem_Ioc] at hi; omega
  · intro j hj; rw [Finset.mem_range] at hj; omega
  · intro i hi
    have hi' := Finset.mem_Ioc.1 hi
    have e : D.R.nV = i + (D.R.r + D.R.t - i) := by show D.R.r + D.R.t = _; omega
    rw [e, key i (D.R.r + D.R.t - i), ← e]
    show _ = 1 - _ * (_ * ((q : ℂ) ^ (D.R.r + D.R.t))⁻¹)
    rfl

end GlobalTheory.FinZeta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffContinuousOneParameterFiniteDimensionalLStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_continuous_oneParameter_finiteDimensional_linear : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (A : ℝ → W →ₗ[ℝ] W),
    (∀ w, Continuous fun t => A t w) → (∀ s t, A (s + t) = (A s).comp (A t)) → A 0 = LinearMap.id →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => LinearMap.toContinuousLinearMap (A t)) := by
  first | exact @GlobalTheory.contDiff_toCLM_of_continuous_oneParameter | exact GlobalTheory.contDiff_toCLM_of_continuous_oneParameter | (intros; apply GlobalTheory.contDiff_toCLM_of_continuous_oneParameter <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffOfContinuousQuasiMultiplicativeSmoothDefStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_of_continuous_quasiMultiplicative_smoothDefect : ∀ (c : ℝ → ℂ) (E : ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ)), Continuous c → c 0 ≠ 0 → IsOpen U → (∀ s, (s, 0) ∈ U) →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) U → (∀ p ∈ U, c (p.1 + p.2) = c p.1 * c p.2 * E p.1 p.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c := by
  first | exact @GlobalTheory.FuncEqSmooth.contDiff_of_func_eq | exact GlobalTheory.FuncEqSmooth.contDiff_of_func_eq | (intros; apply GlobalTheory.FuncEqSmooth.contDiff_of_func_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianPairingIntegralContDiffNeZeroDiagStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianPairingIntegral_contDiff_ne_zero_diag : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ),
    (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) →
    (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => ∫ x, Complex.exp (M p.1 x x) * starRingEnd ℂ (Complex.exp (M p.2 x x)) ∂μ) ∧
    ∀ u, ∫ x, Complex.exp (M u x x) * starRingEnd ℂ (Complex.exp (M u x x)) ∂μ ≠ 0 := by
  first | exact @GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero | exact GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero | (intros; apply GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero <;> assumption)
end

