module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0244
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsCompat

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedIntegersStableSubgroupEqDoubleOrthogonal
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

namespace GlobalTheory.LatticeDual

theorem exists_integral_form_separating {R K : Type} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [Field K] [Algebra R K] [IsFractionRing R K] {κ : Type} [Fintype κ]
    (M : Submodule R (κ → K)) (hM : M.FG) (z : K) (hz : z ∉ (algebraMap R K).range)
    (t : κ → K) (ht : t ∉ M) :
    ∃ y : κ → K, (∀ s ∈ M, s ⬝ᵥ y ∈ (algebraMap R K).range) ∧ t ⬝ᵥ y ∉ (algebraMap R K).range := by
  classical
  haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hM
  haveI : Module.Free R M := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R M
  let ι := Module.Free.ChooseBasisIndex R M
  let a : ι → (κ → K) := fun i => (b i : κ → K)
  have hliR : LinearIndependent R a := b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent K a := (LinearIndependent.iff_fractionRing R K).mp hliR
  let B := Module.Basis.sumExtend hli
  have hfin : Finite (ι ⊕ Module.Basis.sumExtendIndex hli) := Module.Finite.finite_basis B
  have : Finite (Module.Basis.sumExtendIndex hli) :=
    Finite.of_injective (Sum.inr : _ → ι ⊕ _) Sum.inr_injective
  have : Fintype (Module.Basis.sumExtendIndex hli) := Fintype.ofFinite _
  have hB : ∀ i, B (Sum.inl i) = a i := by
    intro i
    simp only [B, Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.coe_extend,
      Equiv.symm_symm, Equiv.trans_apply, Equiv.sumCongr_apply]
    rfl

  have key : ∀ f : (κ → K) →ₗ[K] K, (∀ i, f (a i) ∈ (algebraMap R K).range) →
      ∀ s ∈ M, f s ∈ (algebraMap R K).range := by
    intro f hf s hs
    have hs' : s = ∑ i, b.repr ⟨s, hs⟩ i • a i := by
      have := congrArg Subtype.val (b.sum_repr ⟨s, hs⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs', map_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [f.map_smul_of_tower]
    obtain ⟨r, hr⟩ := hf i
    exact ⟨b.repr ⟨s, hs⟩ i * r, by rw [map_mul, hr, Algebra.smul_def]⟩

  have dot : ∀ f : (κ → K) →ₗ[K] K, ∃ y : κ → K, ∀ x, x ⬝ᵥ y = f x := by
    intro f
    refine ⟨fun k => f (fun j => if k = j then 1 else 0), fun x => ?_⟩
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    simp [dotProduct, smul_eq_mul]
  suffices h : ∃ f : (κ → K) →ₗ[K] K, (∀ i, f (a i) ∈ (algebraMap R K).range) ∧
      f t ∉ (algebraMap R K).range by
    obtain ⟨f, hf, hft⟩ := h
    obtain ⟨y, hy⟩ := dot f
    exact ⟨y, fun s hs => (hy s).symm ▸ key f hf s hs, (hy t).symm ▸ hft⟩
  by_cases h1 : ∃ i, B.repr t (Sum.inl i) ∉ (algebraMap R K).range
  · obtain ⟨i, hi⟩ := h1
    refine ⟨B.coord (Sum.inl i), fun i' => ?_, by simpa using hi⟩
    rw [← hB, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩
  by_cases h2 : ∃ j, B.repr t (Sum.inr j) ≠ 0
  · obtain ⟨j, hj⟩ := h2
    refine ⟨(z / B.repr t (Sum.inr j)) • B.coord (Sum.inr j), fun i => ?_, ?_⟩
    · rw [LinearMap.smul_apply, ← hB, Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply, if_neg Sum.inl_ne_inr, smul_zero]
      exact ⟨0, map_zero _⟩
    · rw [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul, div_mul_cancel₀ _ hj]
      exact hz
  push_neg at h1 h2
  choose c hc using h1
  exfalso
  apply ht
  have htc : t = ∑ i, c i • a i := by
    conv_lhs => rw [← B.sum_repr t]
    rw [Fintype.sum_sum_type]
    simp [h2, hB, ← hc, algebraMap_smul]
  rw [htc]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2

end GlobalTheory.LatticeDual

namespace GlobalTheory.LatticeDual

theorem mem_of_mem_doubleOrth : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ₀ : AddChar (Fv F v) ℂ),
    (∀ x : Fv F v, (∀ y ∈ HeightOneSpectrum.adicCompletionIntegers F v, ψ₀ (x * y) = 1) ↔ x ∈ HeightOneSpectrum.adicCompletionIntegers F v) →
    ∀ A : AddSubgroup (κ → Fv F v), (∀ c ∈ HeightOneSpectrum.adicCompletionIntegers F v, ∀ t ∈ A, c • t ∈ A) →
    (∃ c : Fv F v, c ≠ 0 ∧ ∀ t ∈ A, ∀ k, c * t k ∈ HeightOneSpectrum.adicCompletionIntegers F v) →
    ∀ t : κ → Fv F v, (∀ y : κ → Fv F v, (∀ s ∈ A, ψ₀ (s ⬝ᵥ y) = 1) → ψ₀ (t ⬝ᵥ y) = 1) → t ∈ A := by
  intro F _ _ v κ _ ψ₀ hψ A hA hbd t ht
  classical
  let O := HeightOneSpectrum.adicCompletionIntegers F v
  have hrange : ∀ x : Fv F v, x ∈ (algebraMap O (Fv F v)).range ↔ x ∈ O :=
    fun x => ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hψO : ∀ x ∈ O, ψ₀ x = 1 := fun x hx => by
    simpa using (hψ 1).mpr (one_mem _) x hx

  let M : Submodule O (κ → Fv F v) :=
    { carrier := A
      add_mem' := fun h h' => A.add_mem h h'
      zero_mem' := A.zero_mem
      smul_mem' := fun c x hx => hA _ c.2 x hx }
  obtain ⟨c, hc0, hc⟩ := hbd

  let N : Submodule O (κ → Fv F v) :=
    Submodule.span O (Set.range fun k : κ => c⁻¹ • (Pi.single k 1 : κ → Fv F v))
  have hN : N.FG := Submodule.fg_span (Set.finite_range _)
  have hMN : M ≤ N := by
    intro s hs
    have hs' : s = ∑ k, (⟨c * s k, hc s hs k⟩ : O) • (c⁻¹ • (Pi.single k 1 : κ → Fv F v)) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
      show s j = c * s j * c⁻¹
      rw [mul_comm c, mul_inv_cancel_right₀ hc0]
    rw [hs']
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hMfg : M.FG := by
    haveI := isNoetherian_of_fg_of_noetherian N hN
    have h1 : (M.comap N.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map N.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hMN] at h2

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : (ϖ : Fv F v) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hz : (ϖ : Fv F v)⁻¹ ∉ (algebraMap O (Fv F v)).range := by
    rw [hrange]
    intro h
    apply hϖ.not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, h⟩, Subtype.ext ?_⟩
    simp [hϖ0]
  by_contra htA
  obtain ⟨y', hyA, hyt⟩ := exists_integral_form_separating M hMfg _ hz t htA
  simp only [hrange] at hyA hyt
  obtain ⟨b, hb, hbψ⟩ : ∃ b ∈ O, ψ₀ ((t ⬝ᵥ y') * b) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hyt ((hψ _).mp h)
  apply hbψ
  have := ht (b • y') (fun s hs => by
    rw [dotProduct_smul, smul_eq_mul, mul_comm]
    exact hψO _ (mul_mem (hyA s hs) hb))
  rwa [dotProduct_smul, smul_eq_mul, mul_comm] at this

end GlobalTheory.LatticeDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxProductDiagonalFunctionalNeZero
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open MeasureTheory

noncomputable section

namespace GlobalTheory.DiagTens

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

theorem finprod_indicator {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (y : κ → FiniteAdeleRing (𝓞 F) F) :
    (∏ᶠ w : Pl (F := F), Set.indicator {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} (1 : (κ → Fv F w) → ℂ)
      (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (y i))) =
    (Set.univ.pi fun _ : κ => {x : FiniteAdeleRing (𝓞 F) F | ∀ w : Pl (F := F), x w ∈ w.adicCompletionIntegers F}).indicator
      (fun _ => (1 : ℂ)) y := by
  by_cases h : ∀ i (w : Pl (F := F)), y i w ∈ w.adicCompletionIntegers F
  · rw [Set.indicator_of_mem (show y ∈ (Set.univ.pi fun _ : κ => {x : FiniteAdeleRing (𝓞 F) F | ∀ w : Pl (F := F), x w ∈ w.adicCompletionIntegers F}) from Set.mem_univ_pi.2 fun i => h i)]
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    rw [Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (y i)) ∈
      {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from fun i => h i w)]
    rfl
  · rw [Set.indicator_of_notMem (show y ∉ (Set.univ.pi fun _ : κ => {x : FiniteAdeleRing (𝓞 F) F | ∀ w : Pl (F := F), x w ∈ w.adicCompletionIntegers F}) from fun hy => h fun i => Set.mem_univ_pi.1 hy i)]
    push_neg at h
    obtain ⟨i₀, w₀, hw₀⟩ := h
    have hfin : (Function.mulSupport fun w : Pl F => Set.indicator
        {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} (1 : (κ → Fv F w) → ℂ)
        (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (y i))).Finite := by
      have hx : ∀ᶠ w in Filter.cofinite, ∀ i, (y i) w ∈ w.adicCompletionIntegers F := by
        rw [Filter.eventually_all]
        intro i
        exact (y i).2
      refine Set.Finite.subset (Filter.eventually_cofinite.1 hx) ?_
      intro w hw hw'
      apply hw
      show Set.indicator _ _ _ = _
      rw [Set.indicator_of_mem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (y i)) ∈
        {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from hw')]
      rfl
    refine finprod_eq_zero _ w₀ ?_ hfin
    exact Set.indicator_of_notMem (show (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w₀ (y i)) ∉
      {x : κ → Fv F w₀ | ∀ i, x i ∈ w₀.adicCompletionIntegers F} from fun hy => hw₀ (hy i₀)) _

theorem lDiag_box_tens_ne : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl (F := F)), ∃ φ₀ ∈ SB (κ → Fv F v), boxFun φ₀ φ₀ ∈ SB (κ ⊕ κ → Fv F v) ∧
    ∃ R R' : (κ → AF F) → ℂ, (∀ φ ∈ SB (κ → Fv F v), Rest (evFin F v) φ R ∧ Rest (evFin F v) φ R') ∧
      GlobalTheory.DiagForm.lDiag F κ (boxFun (tens (evFin F v) φ₀ R) (tens (evFin F v) φ₀ R')) ≠ 0 := by
  intro F _ _ κ _ v
  classical
  obtain ⟨hO, hK⟩ := PI.IntAdCpctOpenWork.main F
  set O := {x : FiniteAdeleRing (𝓞 F) F | ∀ w : HeightOneSpectrum (𝓞 F), x w ∈ w.adicCompletionIntegers F} with hOdef
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hc : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : SInf F κ := hc.toSchwartzMap hd
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  let φs : ∀ w : Pl (F := F), (κ → Fv F w) → ℂ := fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
  have hstd : ∀ᶠ w in Filter.cofinite, φs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φs hstd
  have hRest : ∀ φ ∈ SB (κ → Fv F v), Rest (evFin F v) φ r := fun φ hφ => ⟨hr, by
    rw [hrt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v φ hstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w⟩
  have h0 : φs v ∈ SB (κ → Fv F v) := GlobalTheory.StdVacuum.indicator_mem_SB v
  refine ⟨φs v, h0, ?_, r, r, fun φ hφ => ⟨hRest φ hφ, hRest φ hφ⟩, ?_⟩
  · have e : boxFun (φs v) (φs v) = Set.indicator {x : κ ⊕ κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      funext x
      simp only [boxFun, φs, Set.indicator_apply, Set.mem_setOf_eq, Function.comp_apply, Sum.forall, Pi.one_apply]
      split_ifs <;> simp_all
    rw [e]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
  · set V : Set (GlobalTheory.DiagForm.Vf F κ) := Set.univ.pi fun _ => O with hVdef
    set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := V.indicator fun _ => (1 : ℂ) with hgdef
    have hΦ : tens (evFin F v) (φs v) r = pureA F f g := by
      rw [hrt, Function.update_eq_self]
      funext x
      show f _ * _ = f _ * _
      congr 1
      exact finprod_indicator _
    have hΦs : tens (evFin F v) (φs v) r ∈ schA F κ := (hRest _ h0).2
    have hbox := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ hΦs _ hΦs
    have hint := GlobalTheory.DiagForm.integrable_resD hbox
    have hres : GlobalTheory.DiagForm.resD F κ (boxFun (tens (evFin F v) (φs v) r) (tens (evFin F v) (φs v) r)) =
        fun p => ((b (GlobalTheory.DiagForm.eI F κ p.1) * b (GlobalTheory.DiagForm.eI F κ p.1) : ℝ) : ℂ) * (g p.2 * g p.2) := by
      rw [hΦ]
      funext p
      show pureA F f g _ * pureA F f g _ = _
      have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((GlobalTheory.DiagForm.glue p) i).1) =
          GlobalTheory.DiagForm.eI F κ p.1 := by
        funext i
        exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
      have e2 : (fun i => ((GlobalTheory.DiagForm.glue p) i).2) = p.2 := rfl
      simp only [pureA, Function.comp_def, Sum.elim_inl, Sum.elim_inr]
      rw [e1, e2, hf]
      push_cast
      ring
    rw [GlobalTheory.DiagForm.lDiag, LinearMap.comp_apply, GlobalTheory.DiagForm.Lext_apply _ hint, hres, GlobalTheory.DiagForm.mu,
      integral_prod_mul (fun u => ((b (GlobalTheory.DiagForm.eI F κ u) * b (GlobalTheory.DiagForm.eI F κ u) : ℝ) : ℂ))
        (fun y => g y * g y)]
    have h0O : (0 : FiniteAdeleRing (𝓞 F) F) ∈ O := fun w => (w.adicCompletionIntegers F).zero_mem
    have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hO
    have hVc : IsCompact V := isCompact_univ_pi fun _ => hK
    have hgg : (fun y => g y * g y) = V.indicator fun _ => (1 : ℂ) := by
      funext y
      simp only [hgdef, Set.indicator_apply]
      split_ifs <;> simp
    have hc2 : (∫ y, g y * g y ∂(Measure.addHaar : Measure (GlobalTheory.DiagForm.Vf F κ))) ≠ 0 := by
      rw [hgg, integral_indicator_const _ hVo.measurableSet]
      have hpos : 0 < (Measure.addHaar : Measure (GlobalTheory.DiagForm.Vf F κ)) V := hVo.measure_pos _ ⟨0, fun i _ => h0O⟩
      have hfin : (Measure.addHaar : Measure (GlobalTheory.DiagForm.Vf F κ)) V < ⊤ := hVc.measure_lt_top
      have : 0 < (Measure.addHaar : Measure (GlobalTheory.DiagForm.Vf F κ)).real V := ENNReal.toReal_pos hpos.ne' hfin.ne
      simpa using this.ne'
    have hc1 : (∫ u, ((b (GlobalTheory.DiagForm.eI F κ u) * b (GlobalTheory.DiagForm.eI F κ u) : ℝ) : ℂ)
        ∂(volume : Measure (GlobalTheory.DiagForm.Vi F κ))) ≠ 0 := by
      rw [integral_complex_ofReal]
      have hcs1 : HasCompactSupport fun u : GlobalTheory.DiagForm.Vi F κ => b (GlobalTheory.DiagForm.eI F κ u) :=
        b.hasCompactSupport.comp_homeomorph (GlobalTheory.DiagForm.eI F κ).toHomeomorph
      have hcs : HasCompactSupport fun u : GlobalTheory.DiagForm.Vi F κ =>
          b (GlobalTheory.DiagForm.eI F κ u) * b (GlobalTheory.DiagForm.eI F κ u) := hcs1.mul_right
      have hcont : Continuous fun u : GlobalTheory.DiagForm.Vi F κ =>
          b (GlobalTheory.DiagForm.eI F κ u) * b (GlobalTheory.DiagForm.eI F κ u) :=
        (b.continuous.comp (GlobalTheory.DiagForm.eI F κ).continuous).mul (b.continuous.comp (GlobalTheory.DiagForm.eI F κ).continuous)
      have hpos := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
        (μ := (volume : Measure (GlobalTheory.DiagForm.Vi F κ))) (x := 0) hcs (fun u => mul_nonneg b.nonneg b.nonneg) (by
          simp only [map_zero]
          rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
          norm_num)
      exact_mod_cast hpos.ne'
    exact mul_ne_zero hc1 hc2

end GlobalTheory.DiagTens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeilRepresentationThird
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne


set_option maxHeartbeats 1000000 in
theorem integral_theta_chi {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (hL : ∀ k, k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β L ↔ k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β (Lev.flag1L L))
    (χ' : (levEnv S β L).J →* ℂˣ)
    {f : Bridge.Gf S → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J χ')
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ (levEnv S β L).J, ∀ w,
      om (k, 1) (Λ w) = ((χ' ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : IsMeasDef S (Formalism.L2.DIV.lev D.sp.cm S.gram β L) ν 𝓕)
    (J' : Subgroup (Bridge.Gf S)) (Cl : Type) [Fintype Cl] (h : Cl → GA D S) (hle : J' ≤ (levEnv S β L).J)
    (hN : J'.relIndex (levEnv S β L).J ≠ 0) (hy : Bridge.IsReps (Bridge.ratF S) J' (fun k => fin S (h k)))
    (hh : ∀ k, h k ∈ GfC S) (g : GA D T) :
    ∫ x in 𝓕, thetaKO om x g (Λ (c.ext f x)) ∂ν = ∑ k, ((J'.relIndex (levEnv S β L).J : ℕ) : ℂ)⁻¹ *
      ((Nat.card (Bridge.stab (Bridge.ratF S) J' (fin S (h k))) : ℕ) : ℂ)⁻¹ * thetaKO om (h k) g (Λ (f (fin S (h k)))) := by
  rw [GlobalTheory.ClsInt.integral_eq_classSum_of_le D S β L ν 𝓕 hp hs hν hL J' Cl h hle hN hy hh
    (fun x => thetaKO om x g (Λ (c.ext f x))) ?_ ?_]
  · exact Finset.sum_congr rfl fun k _ => by rw [ext_fin c hc f (hh k)]
  · intro γ hγ x
    have e : (γ * x, g) = ((γ, 1) : GA D S × GA D T) * (x, g) := by rw [Prod.mk_mul_mk, one_mul]
    simp only [thetaKO]
    rw [GlobalTheory.ThetaIntegrand.ext_invariant c hf γ hγ, e, map_mul]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ (hΛ _))
  · intro u hu x
    refine (GlobalTheory.LiftUnfold.exists_fin_mul_real S u).elim fun k hk0 => hk0.2.elim fun a ha0 => ?_
    have hk := hk0.1
    have ha := ha0.1
    have e := ha0.2.2
    have hk' : fin S k ∈ (levEnv S β L).J := by rw [e]; exact hu
    have h1 : c.ρ k⁻¹ = 1 := hc.1 _ (inv_mem hk)
    have h2 : (finHom S).rangeRestrict a = 1 := Subtype.ext (MonoidHom.mem_ker.1 ha)
    have h3 := GlobalTheory.LiftUnfold.form_right (Bridge.ratF S) c.coef.ρ hf ⟨fin S k, hk'⟩
    have h4 := GlobalTheory.LiftUnfold.integrand_right om c.ρ (finHom S).rangeRestrict Λ f u k a ha0.2.1 (χ' ⟨fin S k, hk'⟩)
      h1 h2 h3 (hΛk k hk hk') (hΛa a ha) x g
    exact congrFun h4 0

end GlobalTheory.GalOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharSupportedIdeleEqLocalAbsValue
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ModuLocal

theorem infComp_eq_one {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {u : (AF F)ˣ}
    (hu : At (evFin F v) ((u : AF F) - 1)) (w : NumberField.InfinitePlace F) : (u : AF F).1 w = 1 := by
  have h := hu (pairA F 1 0) (by change evalV F v 0 = 0; exact map_zero _)
  have h' : (1 : Ainf F) * ((u : AF F).1 - 1) = 0 := congrArg Prod.fst h
  rw [one_mul, sub_eq_zero] at h'
  rw [h']
  rfl

theorem finComp_eq_one {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {u : (AF F)ˣ}
    (hu : At (evFin F v) ((u : AF F) - 1)) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    (u : AF F).2 w = 1 := by
  have h := hu (pairA F 0 (GlobalTheory.AdelicU.singleFin w 1))
    (by change evalV F v (GlobalTheory.AdelicU.singleFin w 1) = 0; exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hw) 1)
  have h2 : GlobalTheory.AdelicU.singleFin w 1 * ((u : AF F).2 - 1) = 0 := congrArg Prod.snd h
  have h' := congrArg (evalV F w) h2
  rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul, map_sub, map_zero, sub_eq_zero] at h'
  rw [← (map_one (evalV F w) : evalV F w 1 = 1)]
  exact h'

end GlobalTheory.ModuLocal

theorem GlobalTheory.ModuLocal.distribHaarChar_eq_nabs_of_at : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (u : (AF F)ˣ), At (evFin F v) ((u : AF F) - 1) →
    ((MeasureTheory.distribHaarChar (AF F) u : NNReal) : ℝ) = GlobalTheory.SplitWeil.nabs (Fv F v) (Units.map (evFin F v : AF F →* Fv F v) u) := by
  intro F _ _ v u hu
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing F u, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have hinf : (∏ w : NumberField.InfinitePlace F, ‖(u : AF F).1 w‖ ^ w.mult) = 1 :=
    Finset.prod_eq_one fun w _ => by rw [GlobalTheory.ModuLocal.infComp_eq_one hu w, norm_one, one_pow]
  have hfin : (∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖(u : AF F).2 w‖) = ‖(u : AF F).2 v‖ :=
    finprod_eq_single _ v fun w hw => by rw [GlobalTheory.ModuLocal.finComp_eq_one hu hw, norm_one]
  have hloc := ((GlobalTheory.CompletionNorm.norm_nabs_valuation F v).1 (Units.map (evFin F v : AF F →* Fv F v) u)).1
  refine (congrArg₂ (· * ·) hinf hfin).trans ?_
  rw [one_mul]
  exact hloc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceMul
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.AdelicTraceNondeg

theorem trace_one_tmul {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R]
    [Algebra F R] (e : E) : Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem eq_zero_of_trace_mul {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [CommRing R]
    [Algebra F R] (m : R ⊗[F] E) (h : ∀ z : R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (m * z) = 0) : m = 0 := by
  let b := Module.finBasis F E
  let d := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b
  let bA := Algebra.TensorProduct.basis R b
  have key : ∀ j, bA.repr m j = 0 := by
    intro j
    have hj := h ((1 : R) ⊗ₜ[F] d j)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← bA.sum_repr m, Finset.sum_mul, map_sum] at hj
    rw [← hj, Finset.sum_eq_single j]
    · rw [Algebra.TensorProduct.basis_apply, smul_mul_assoc, map_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        trace_one_tmul, smul_eq_mul]
      have := (Algebra.traceForm F E).apply_dualBasis_left (traceForm_nondegenerate F E) b j j
      rw [Algebra.traceForm_apply, mul_comm] at this
      rw [this]; simp
    · intro i _ hij
      rw [Algebra.TensorProduct.basis_apply, smul_mul_assoc, map_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        trace_one_tmul, smul_eq_mul]
      have := (Algebra.traceForm F E).apply_dualBasis_left (traceForm_nondegenerate F E) b j i
      rw [Algebra.traceForm_apply, mul_comm] at this
      rw [this, if_neg hij, map_zero, mul_zero]
    · intro hj'; exact absurd (Finset.mem_univ j) hj'
  exact bA.repr.injective (by ext j; simp [key j])

theorem trace_pairing_nondeg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ψ : AddChar (AF F) ℂ),
    IsStd ψ → ∀ m : AEF F E, m ≠ 0 → ∃ z : AEF F E, ψ (Algebra.trace (AF F) (AEF F E) (m * z)) ≠ 1 := by
  intro F E _ _ _ _ _ ψ hψ m hm
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Algebra.IsSeparable F E := Algebra.IsAlgebraic.isSeparable_of_perfectField
  by_contra hne
  push_neg at hne
  apply hm
  refine eq_zero_of_trace_mul m fun z => ?_
  apply GlobalTheory.DiagNonvan.eq_zero_of_psi_mul hψ
  intro y
  have e1 : Algebra.trace (AF F) (AEF F E) (m * z) * y = Algebra.trace (AF F) (AEF F E) (m * (y • z)) := by
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  rw [e1]
  exact hne _

end GlobalTheory.AdelicTraceNondeg
end
end

