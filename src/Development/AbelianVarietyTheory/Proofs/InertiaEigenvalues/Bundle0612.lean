module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValApplySubLtOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerRightRegularRepSubEqIntervalIntegralDerivat
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.AutomorphicL2Unitary

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G}
  [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

theorem coeFn_right_translate {φ : G → ℂ} (h : MemL2Quotient Γ μ φ) (g : G) :
    R Γ μ g h.toL2 =ᵐ[quotMeasure Γ μ] fun q => φ (sec Γ q * g) := by
  rw [right_translate_toL2]
  refine (h.mul_right g).coeFn_toL2.trans (Filter.Eventually.of_forall fun q => ?_)
  have := (h.1.mul_right g).descend_mk (sec Γ q)
  rwa [mk_sec] at this

theorem inner_right_translate_integral {φ : G → ℂ} (h : MemL2Quotient Γ μ φ) (g : G) (H : L2 Γ μ) :
    inner ℂ H (R Γ μ g h.toL2) = ∫ q, starRingEnd ℂ (H q) * φ (sec Γ q * g) ∂quotMeasure Γ μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_right_translate h g] with q e
  simp [e, mul_comm]

theorem inner_R_sub_eq_intervalIntegral :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → c 0 = 1 → ∀ {f f' : G → ℂ} (hf : MemL2Quotient Γ μ f) (hf' : MemL2Quotient Γ μ f'), Continuous f' → (∀ x t, HasDerivAt (fun s => f (x * c s)) (f' (x * c t)) t) → ∀ (H : L2 Γ μ) (t : ℝ), Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s)) ((volume.restrict (Set.uIoc 0 t)).prod (quotMeasure Γ μ)) → inner ℂ H (R Γ μ (c t) hf.toL2) - inner ℂ H hf.toL2 = ∫ s in (0 : ℝ)..t, inner ℂ H (R Γ μ (c s) hf'.toL2) := by
  intro G _ _ _ _ _ _ _ Γ _ μ _ _ _ c hc h0 f f' hf hf' hcf hd H t hint
  have ftc : ∀ x, ∫ s in (0 : ℝ)..t, f' (x * c s) = f (x * c t) - f (x * 1) := fun x => by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd x s)
      ((hcf.comp (continuous_const.mul hc)).intervalIntegrable _ _), h0]
  haveI : SigmaFinite μ := inferInstance
  haveI : SigmaFinite (quotMeasure Γ μ) :=
    SigmaFinite.of_map _ (measurePreserving_sec (Γ := Γ) (μ := μ)).measurable.aemeasurable
      (by rw [(measurePreserving_sec (Γ := Γ) (μ := μ)).map_eq]; infer_instance)
  simp only [inner_right_translate_integral hf']
  rw [MeasureTheory.intervalIntegral_integral_swap hint, ← inner_sub_right, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have e1 := coeFn_right_translate hf 1
  rw [map_one, ContinuousLinearMap.one_apply] at e1
  filter_upwards [coeFn_right_translate hf (c t), e1, Lp.coeFn_sub (R Γ μ (c t) hf.toL2) hf.toL2] with q a b e
  rw [intervalIntegral.integral_const_mul, ftc, e, Pi.sub_apply, a, b]
  simp [mul_comm]

end GlobalTheory.AutomorphicL2Unitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableConjMulTranslatePath
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory

theorem integrable_conj_mul_translate_path {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G)
    [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μ] (c : ℝ → G) (hc : Continuous c) {f' : G → ℂ} (hf' : MemL2Quotient Γ μ f')
    (_hcont : Continuous f') (H : L2 Γ μ) (t : ℝ) :
    Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s))
      ((volume.restrict (Set.uIoc 0 t)).prod (quotMeasure Γ μ)) := by
  haveI : SigmaFinite μ := inferInstance
  haveI : SigmaFinite (quotMeasure Γ μ) :=
    SigmaFinite.of_map _ (measurePreserving_sec (Γ := Γ) (μ := μ)).measurable.aemeasurable
      (by rw [measurePreserving_sec.map_eq]; infer_instance)
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ, Set.uIoc]; exact measure_Ioc_lt_top⟩
  have hm : Measurable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => rmul Γ (c s) q) :=
    measurable_rmul_uncurry.comp (measurable_snd.prodMk (hc.measurable.comp measurable_fst))
  have hp := (MeasurePreserving.id (volume.restrict (Set.uIoc (0 : ℝ) t))).skew_product
    (μc := quotMeasure Γ μ) (μd := quotMeasure Γ μ) hm
    (Filter.Eventually.of_forall fun s => (measurePreserving_rmul (c s)).map_eq)
  have h1 := ((Lp.memLp H).star).comp_snd (volume.restrict (Set.uIoc (0 : ℝ) t))
  have h2 := (hf'.2.comp_snd (volume.restrict (Set.uIoc (0 : ℝ) t))).comp_measurePreserving hp
  refine (h1.integrable_mul h2).congr (Filter.Eventually.of_forall fun p => ?_)
  have e : descend Γ f' (rmul Γ (c p.1) p.2) = f' (sec Γ p.2 * c p.1) := by
    rw [← hf'.1.descend_mk, ← rmul_mk, mk_sec]
  change star (H p.2) * descend Γ f' (rmul Γ (c p.1) p.2) = _
  rw [e]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvQPowNygaardExtComesFromBaseFieldStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_Q_pow_nygaard_ext_comes_from_base_field : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (m : ℕ) (y' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)), y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m) → ∃ y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m), ((F l).E K s LL h).tie.jD T y = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') := by
  first | exact @GlobalTheory.NL.TransitionThirdCase.main | exact GlobalTheory.NL.TransitionThirdCase.main | (intros; apply GlobalTheory.NL.TransitionThirdCase.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDoubleCosetOfSmallerLevelSameLocal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isDC_of_smaller_level_same_local {G : Type} [Group G] (J J' Lc : Subgroup G) (x : G) (A : Finset G)
    (hJJ : J' ≤ J) (hLc : J ⊓ Lc ≤ J')
    (hdec : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ y ∈ Lc, Commute k₂ y)
    (hx : x ∈ Lc) (hA : ∀ a ∈ A, a ∈ Lc) (hDC : Bridge.IsDC J x A) : Bridge.IsDC J' x A := by
  obtain ⟨h1, h2⟩ := hDC
  refine ⟨fun a ha => ?_, fun g hg => ?_⟩
  · obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩, rfl⟩ := h1 a ha
    obtain ⟨k₁, hk₁J, k₂, hk₂J, hk₁L, rfl, hk₂c⟩ := hdec k hk
    obtain ⟨k₁', hk₁'J, k₂', hk₂'J, hk₁'L, rfl, -⟩ := hdec k' hk'
    have e : k₁ * k₂ * x * (k₁' * k₂') = k₁ * x * k₁' * (k₂ * k₂') := by
      have c1 : k₂ * x = x * k₂ := (hk₂c x hx).eq
      have c2 : k₂ * k₁' = k₁' * k₂ := (hk₂c k₁' hk₁'L).eq
      calc k₁ * k₂ * x * (k₁' * k₂') = k₁ * (k₂ * x) * k₁' * k₂' := by group
        _ = k₁ * x * (k₂ * k₁') * k₂' := by rw [c1]; group
        _ = k₁ * x * (k₁' * k₂) * k₂' := by rw [c2]
        _ = k₁ * x * k₁' * (k₂ * k₂') := by group
    have haL := hA _ ha
    have hprodL : k₂ * k₂' ∈ Lc := by
      have : k₂ * k₂' = (k₁ * x * k₁')⁻¹ * (k₁ * k₂ * x * (k₁' * k₂')) := by rw [e]; group
      rw [this]
      exact Lc.mul_mem (Lc.inv_mem (Lc.mul_mem (Lc.mul_mem hk₁L hx) hk₁'L)) haL
    have hprod : k₂ * k₂' ∈ J' := hLc ⟨J.mul_mem hk₂J hk₂'J, hprodL⟩
    have hk₁ : k₁ ∈ J' := hLc ⟨hk₁J, hk₁L⟩
    have hk₁' : k₁' ∈ J' := hLc ⟨hk₁'J, hk₁'L⟩
    refine ⟨⟨k₁, hk₁⟩, ⟨k₁' * (k₂ * k₂'), J'.mul_mem hk₁' hprod⟩, ?_⟩
    simp only
    rw [e]; group
  · obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩, rfl⟩ := hg
    obtain ⟨k₁, hk₁J, k₂, hk₂J, hk₁L, rfl, hk₂c⟩ := hdec k (hJJ hk)
    have hk₁ : k₁ ∈ J' := hLc ⟨hk₁J, hk₁L⟩
    have hk₂ : k₂ ∈ J' := by
      have : k₂ = k₁⁻¹ * (k₁ * k₂) := by group
      rw [this]; exact J'.mul_mem (J'.inv_mem hk₁) hk
    obtain ⟨a, ⟨haA, haJ⟩, -⟩ := h2 (k₁ * x) ⟨⟨k₁, hk₁J⟩, 1, by simp⟩
    have haL : a⁻¹ * (k₁ * x) ∈ Lc := Lc.mul_mem (Lc.inv_mem (hA a haA)) (Lc.mul_mem hk₁L hx)
    have haJ' : a⁻¹ * (k₁ * x) ∈ J' := hLc ⟨haJ, haL⟩
    have c1 : k₂ * x = x * k₂ := (hk₂c x hx).eq
    refine ⟨a, ⟨haA, ?_⟩, ?_⟩
    · have : a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * (k₁ * x) * (k₂ * k') := by
        calc a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * k₁ * (k₂ * x) * k' := by group
          _ = a⁻¹ * (k₁ * x) * (k₂ * k') := by rw [c1]; group
      rw [this]
      exact J'.mul_mem haJ' (J'.mul_mem hk₂ hk')
    · rintro b ⟨hbA, hbJ'⟩
      have hgJ : ∃ m₁ m₂ : J, k₁ * k₂ * x * k' = (m₁ : G) * x * m₂ :=
        ⟨⟨k₁ * k₂, hJJ hk⟩, ⟨k', hJJ hk'⟩, rfl⟩
      obtain ⟨c, -, hc⟩ := h2 _ hgJ
      have haJg : a⁻¹ * (k₁ * k₂ * x * k') ∈ J := by
        have : a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * (k₁ * x) * (k₂ * k') := by
          calc a⁻¹ * (k₁ * k₂ * x * k') = a⁻¹ * k₁ * (k₂ * x) * k' := by group
            _ = a⁻¹ * (k₁ * x) * (k₂ * k') := by rw [c1]; group
        rw [this]; exact J.mul_mem haJ (J.mul_mem hk₂J (hJJ hk'))
      rw [hc b ⟨hbA, hJJ hbJ'⟩, hc a ⟨haA, haJg⟩]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotentiallySemistableOfSemistableRestrict
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem isPst_resTo_iff_padic {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K K' : FinExt l} (hK : K.1 ≤ K'.1)
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) :
    IsPst P (resTo ρ hK) ↔ IsPst P ρ := by
  let e : DpstUr P (resTo ρ hK) ≃ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ :=
    { toFun := fun x =>
        toUr P ρ ⟨((toUr P _).symm x).1, (Dpst_resTo P ρ hK).le ((toUr P _).symm x).2⟩
      invFun := fun x =>
        toUr P _ ⟨((toUr P ρ).symm x).1, (Dpst_resTo P ρ hK).ge ((toUr P ρ).symm x).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [IsPst, IsPst, e.rank_eq]

theorem finrank_le_finrank_DpstUr_of_isSst {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] (hS : IsSst P ρ) :
    finrank ℚ_[l] V ≤ finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) := by
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  let val : DpstUr P ρ →+ V ⊗[ℚ_[l]] Bst P :=
    (Dpst P ρ).subtype.toAddMonoidHom.comp (toUr P ρ).symm.toAddMonoidHom
  have hSD : Dst P ρ ≤ Dpst P ρ := fun s hs => (mem_Dpst P ρ).mpr ⟨K, fun g _ => (mem_Dst P ρ).mp hs g⟩
  obtain ⟨b, hbS, hsp, hli⟩ := exists_linearIndependent ↥(MaximalUnramifiedExtension l) {y : DpstUr P ρ | val y ∈ Dst P ρ}
  haveI : Finite ↥b := hli.finite
  letI : Fintype ↥b := Fintype.ofFinite _
  have hspan : ∀ y : DpstUr P ρ, y ∈ Submodule.span ↥(MaximalUnramifiedExtension l) b → ∃ c : ↥b → ↥(MaximalUnramifiedExtension l),
      ∑ i, c i • (i : DpstUr P ρ) = y := fun y hy => by
    rw [← Submodule.mem_span_range_iff_exists_fun, Subtype.range_coe]; exact hy
  let inc : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) := IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)
  let f : (↥b → ↥(K0 K)) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P :=
    { toFun := fun c => ∑ i, mulV P ℚ_[l] V (inc (c i)) (val i)
      map_add' := fun c c' => by simp [Finset.sum_add_distrib]
      map_smul' := fun q c => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => mulV_padic_smul P _ V q (inc (c i)) (val i) }
  have hle : Dst P ρ ≤ LinearMap.range f := by
    intro s hs
    obtain ⟨c, hc⟩ := hspan (toUr P ρ ⟨s, hSD hs⟩) (hsp ▸ Submodule.subset_span hs)
    have hfix : ∀ i, (c i : Om l) ∈ K.1 := fun i => mem_of_GK_fixed fun g => by
      have := semilinear_coord_fixed hli (fun a => ⟨_, galois_mem_Kur g a⟩)
        (actD P ρ g).toAddMonoidHom
        (fun a y => LinearMap.congr_fun (actD_mulD P ρ g a _ rfl) y)
        (fun j => Subtype.ext ((mem_Dst P ρ).mp (hbS j.2) g)) c
        (by rw [hc]; exact Subtype.ext ((mem_Dst P ρ).mp hs g)) i
      exact congrArg Subtype.val this
    refine ⟨fun i => ⟨c i, hfix i, (c i).2⟩, ?_⟩
    have := congrArg val hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    exact this
  have h1 : finrank ℚ_[l] ↥(Dst P ρ) ≤ Fintype.card ↥b * finrank ℚ_[l] ↥(K0 K) := by
    refine (Submodule.finrank_mono hle).trans ((LinearMap.finrank_range_le f).trans ?_)
    simp [Module.finrank_pi_fintype]
  have h2 : finrank ℚ_[l] ↥(Dst P ρ) = finrank ℚ_[l] V * finrank ℚ_[l] ↥(K0 K) := by
    rw [show finrank ℚ_[l] ↥(Dst P ρ) = _ from hS, mul_comm]
  have h3 : finrank ℚ_[l] V ≤ Fintype.card ↥b :=
    Nat.le_of_mul_le_mul_right (h2 ▸ h1) Module.finrank_pos
  exact h3.trans hli.fintype_card_le_finrank

theorem isPst_of_isSst_resTo : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K K' : FinExt l) (hK : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P (resTo ρ hK) → IsPst P ρ := by
  intro l _ P AI T K K' hK V _ _ _ ρ hS
  obtain ⟨hdom, hreg, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  have hup := GlobalTheory.PstRank.rank_DpstUr_le P hdom hreg (resTo ρ hK)
  haveI : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (resTo ρ hK)) :=
    Module.rank_lt_aleph0_iff.mp (hup.trans_lt Cardinal.natCast_lt_aleph0)
  rw [← isPst_resTo_iff_padic P hK ρ, GlobalTheory.Pst.isPst_iff]
  refine ⟨inferInstance, le_antisymm ?_ (finrank_le_finrank_DpstUr_of_isSst P _ hS)⟩
  rw [← finrank_eq_rank] at hup
  exact_mod_cast hup

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueTiedOfIsToricElt
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.HeckeGal GlobalTheory.ToricDenom
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (lamF upIdele)

namespace GlobalTheory.ToricRational

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

def RatioConj : Prop :=
  ∀ (R : Ranks) (H : Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : HChar H.E),
    IsHostDatum H φ s κ 𝔣 χ →
    ∀ (Ω : Type) [Field Ω] [Algebra H.K Ω] [IsAlgClosure H.K Ω] (j : Ω →+* ℂ) (τ₀ : I),
    (∀ x : H.K, j (algebraMap H.K Ω x) = φ τ₀ x) →
    ∀ art : Ideles H.K →* Gab H.K Ω, IsGlobalArtin art →
    ∀ T₀ : ℂ, IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀ → T₀ ≠ 0 →
    ∀ Q : Finset (HeightOneSpectrum (OF H.E)), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → Finite (PicO (condQ 𝔣 Q)) →
    ∀ T : PicO (condQ 𝔣 Q) → ℂ, (∀ q, IsClassTerm φ s κ (condQ 𝔣 Q) χ q.out (T q)) →
    ∃ ρ : (PicO (condQ 𝔣 Q) →* Ωˣ) → Ω,
      (∀ ψ, j (ρ ψ) = (∑ᶠ q, (j (ψ q))⁻¹ * T q) / T₀) ∧
      ∀ g : G H.K Ω, (∀ (x : Ω) (τ : I) (y : H.E), j x = φ τ y → g x = x) → (∀ (x : Ω) (y : (Af H.E)ˣ), j x = lamF s χ y → g x = x) →
        ∀ t : (Af H.K)ˣ, art (finIdele H.K t) = toAb H.K Ω g⁻¹ → ∀ ψ : PicO (condQ 𝔣 Q) →* Ωˣ,
          g (ρ ψ) = (g (ψ (QuotientGroup.mk (upIdele H.K H.E t))))⁻¹ * ρ ((Units.map g.toRingEquiv.toMonoidHom).comp ψ)

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def setTh (th : ∀ i Q, X.abelian₂ i → X.RCG i Q → FractionRing (X.O i)) : NTw D.R D.host D.what₂ D.LL0 N :=
  { X with th := th }

variable {X}

theorem toBar_algebraMap (i : X.Tw) (a : X.O0 i) :
    toBar X i (algebraMap (X.O0 i) _ a) = algebraMap (X.O i) (Kbar X i) (algebraMap (X.O0 i) (X.O i) a) := by
  rw [toBar, RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  rfl

end GlobalTheory.ToricRational
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergFactorConjTendstoOneNeZero
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.JSW

theorem locL_conj_tendsto_one_and_ne_zero : ∀ (q : ℕ) (A B : Multiset ℂˣ), 1 < q → (∀ α ∈ A, ‖(α : ℂ)‖ ^ 2 < (q : ℝ)) →
    (∀ β ∈ B, ‖(β : ℂ)‖ ^ 2 < (q : ℝ)) →
    Tendsto (fun x : ℝ => locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1)
      (𝓝 (locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1)) ∧
    locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1 ≠ 0 := by
  intro q A B hq hA hB
  set B' := B.map (Units.map (starRingEnd ℂ).toMonoidHom) with hB'
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqr : (1 : ℝ) < q := by exact_mod_cast hq

  have key : ∀ p ∈ A ×ˢ B', (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(1 : ℂ))) ≠ 0 := by
    intro p hp
    rw [Multiset.mem_product] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [hB', Multiset.mem_map] at h2
    obtain ⟨β, hβ, hpe⟩ := h2
    rw [← hpe]
    have ha := hA _ h1
    have hb := hB _ hβ
    have hnb : ‖((Units.map (starRingEnd ℂ).toMonoidHom β : ℂˣ) : ℂ)‖ = ‖(β : ℂ)‖ := by
      simp [Units.coe_map]
    have hprod : ‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖ < q := by
      have h0 : 0 ≤ ‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖ := by positivity
      by_contra hc
      push_neg at hc
      have : (q : ℝ) * q ≤ (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) * (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) :=
        mul_le_mul hc hc (by positivity) h0
      have h3 : (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) * (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) = ‖(p.1 : ℂ)‖ ^ 2 * ‖(β : ℂ)‖ ^ 2 := by ring
      have h4 : ‖(p.1 : ℂ)‖ ^ 2 * ‖(β : ℂ)‖ ^ 2 < (q : ℝ) * q :=
        mul_lt_mul'' ha hb (by positivity) (by positivity)
      linarith
    intro h0
    have hz : (p.1 : ℂ) * ((Units.map (starRingEnd ℂ).toMonoidHom β : ℂˣ) : ℂ) * (q : ℂ) ^ (-(1 : ℂ)) = 1 := by
      linear_combination -h0
    have hn := congrArg norm hz
    rw [Complex.cpow_neg_one, norm_mul, norm_mul, hnb, norm_inv, Complex.norm_natCast, norm_one] at hn
    have hqpos : (0 : ℝ) < q := by linarith
    rw [mul_inv_eq_one₀ hqpos.ne'] at hn
    linarith
  constructor
  · have hc : ∀ p ∈ A ×ˢ B', Tendsto (fun x : ℝ => (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(x : ℂ)))⁻¹) (𝓝[>] 1)
        (𝓝 ((1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-((1 : ℝ) : ℂ)))⁻¹)) := by
      intro p hp
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      apply ContinuousAt.tendsto
      apply ContinuousAt.inv₀
      · apply ContinuousAt.sub continuousAt_const
        apply ContinuousAt.mul continuousAt_const
        apply ContinuousAt.const_cpow
        · exact (Complex.continuous_ofReal.neg).continuousAt
        · exact Or.inl hq0
      · simpa using key p hp
    have := tendsto_multiset_prod (A ×ˢ B') hc
    simpa [locL] using this
  · unfold locL
    apply Multiset.prod_ne_zero
    rw [Multiset.mem_map]
    rintro ⟨p, hp, h⟩
    exact inv_ne_zero (key p hp) h
end GlobalTheory.JSW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletionFiltrationIffDeRhamFiltrationStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completionFiltration_iff_deRhamFiltration : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl) (j : ℤ), GlobalTheory.BKGal.JumpDR.InEhat ↥(OL LL) ↥LL.1 l e j (GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1)) ↔ ∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (s k)) (X (jB (toBcris (thetaW a LL) ϖ P (m k)))) ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) j := by
  first | exact @GlobalTheory.BKGal.JumpDR.inEhat_iff_filV | exact GlobalTheory.BKGal.JumpDR.inEhat_iff_filV | (intros; apply GlobalTheory.BKGal.JumpDR.inEhat_iff_filV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormProdSatakeParametersUnitaryEqOne
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.RSNonvan

theorem norm_prod_sat_eq_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ : CG E a)
    (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), σ.IsUnitary → σ.HasSat w B → ‖((B.prod : ℂˣ) : ℂ)‖ = 1 := by
  intro E _ _ _ a σ w B hu hB
  obtain ⟨ω, hωu, hω⟩ := hu
  induction σ using Quotient.inductionOn with | _ π => ?_
  change GlobalTheory.LFun.HasSatGL w (π.locRep w) B at hB
  change π.HasCentChar ω at hω
  obtain ⟨x, hx⟩ := hB.exists_vec
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  have hϖ0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  let u : (w.adicCompletion E)ˣ := Units.mk0 ϖ hϖ0
  let S : GL (Fin a) (w.adicCompletion E) := Matrix.GeneralLinearGroup.scalar (Fin a) u
  let K := GlobalTheory.LFun.KGL w (n := a)
  have hS : ((S : GL (Fin a) (w.adicCompletion E)) : Matrix (Fin a) (Fin a) (w.adicCompletion E)) = diagJ a ϖ a := by
    ext i j
    simp [S, u, diagJ, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]
  have hT : Tj ℂ a (Ov E w) ϖ a = dosetInd ℂ K S := by
    unfold Tj dosetInd
    congr 1
    ext g
    simp only [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    refine exists_congr fun y => and_congr_right fun _ => exists_congr fun z => and_congr_right fun _ => ?_
    rw [Units.ext_iff, Units.val_mul, Units.val_mul, hS]
  have hc : ∀ g ∈ DoubleCoset.doubleCoset S (K : Set _) K, ∃! γ, γ ∈ ({S} : Finset _) ∧ γ⁻¹ * g ∈ K := by
    intro g hg
    obtain ⟨y, hy, z, hz, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    refine ⟨S, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    have e : S⁻¹ * (y * S * z) = y * z := by
      rw [show y * S = S * y from (scalar_comm u y).symm]; group
    rw [e]
    exact K.mul_mem hy hz
  have hR : ∀ γ ∈ ({S} : Finset _), γ ∈ DoubleCoset.doubleCoset S (K : Set _) K := by
    intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, 1, K.one_mem, by group⟩
  have h1 := hx.2.2.2 ϖ hϖ a le_rfl
  rw [hT, GlobalTheory.LFun.heckeVec_dosetInd hx.2.1 hR hc, Finset.sum_singleton] at h1
  have h2 : π.locRep w S x = ((ω.1 (finId E (Units.map (corner (sLoc E w)) u)) : ℂˣ) : ℂ) • x := by
    have e : locGL E a w S = Matrix.GeneralLinearGroup.scalar (Fin a) (Units.map (corner (sLoc E w)) u) :=
      cornerGL_scalar (sLoc E w) u
    change π.finPart (locGL E a w S) x = _
    rw [e]
    exact hω _ x
  rw [h2] at h1
  have h3 := smul_left_injective ℂ hx.1 h1
  have hcard : (B.map fun b : ℂˣ => (b : ℂ)).card = a := by rw [Multiset.card_map]; exact hx.2.2.1
  have h4 : GlobalTheory.LFun.satEig (qV E w) a B a = ((B.prod : ℂˣ) : ℂ) := by
    rw [GlobalTheory.LFun.satEig, sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul, Multiset.esymm, ← hcard,
      Multiset.powersetCard_self, Multiset.map_singleton, Multiset.sum_singleton]
    exact (map_multiset_prod (Units.coeHom ℂ) B).symm
  rw [← h4, ← h3]
  exact hωu _

end GlobalTheory.RSNonvan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfLocalFilteredHypotheses
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem theoremB_of_admitted_inputs :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ (C CR CA CB CK Ckap : ℝ), (320 : ℝ) ≤ C → CrystallineLiftingBounds.adm22 D HW F → CrystallineLiftingBounds.adm23 D HW F →
      Formalism.MainNotions.N.LetterConditionGlobal D HW F → ArcLiftingSetup.Stmt D HW F Cm C CR CA CB CK Ckap :=
  fun D HW F Cm C CR CA CB CK Ckap hC a22 a23 c4 =>
    Formalism.MainNotions.N.Ln17.frobenius_statement_of_fontaine D HW F Cm C CR CA CB CK Ckap hC a22 a23 c4

end GlobalTheory
end

