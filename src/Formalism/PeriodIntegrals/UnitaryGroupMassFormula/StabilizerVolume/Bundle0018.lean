module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoNuFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SdDual

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVDx
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

theorem gramR_add_sub {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x W : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J (x + W) - gramR R σ J x - gramR R σ J W = gramB R σ J x W := by
  funext i j
  simp only [Matrix.sub_apply, gramR, gramB, Pi.add_apply, hR_add_left, hR_add_right]
  ring

theorem gramB_add_right {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x W W' : Fin n → Fin M → R ⊗[F] E) :
    gramB R σ J x (W + W') = gramB R σ J x W + gramB R σ J x W' := by
  funext i j
  simp only [Matrix.add_apply, gramB, Pi.add_apply, hR_add_left, hR_add_right]
  ring

theorem dxOpen_of (h : SecGram) : DxOpen := by
  intro F E _ _ _ _ _ σ hσ M J hJ hdet a _h1 _h2 v d b x hx
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) (Fv F v ⊗[F] E)
  have : IsReduced (Fv F v ⊗[F] E) := isReduced_tens_field F E (Fv F v)
  have hss : IsSemisimpleRing (Fv F v ⊗[F] E) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  obtain ⟨q, hq⟩ := h F E σ hσ M J hJ hdet (Fv F v) hss a x hx
  set T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) → (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun S j k => ∑ i', (algebraMap F (Fv F v ⊗[F] E) (1 / 2) * S i' j) * q k i' with hT
  have hTc : Continuous T := by
    refine continuous_pi fun j => continuous_pi fun k => continuous_finsetSum _ fun i' _ => ?_
    exact (continuous_const.mul (continuous_id.matrix_elem i' j)).mul continuous_const
  have hT0 : T 0 = 0 := by
    funext j k
    simp [hT]
  set L := latSub b v a M with hL
  have hLo : IsOpen (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    (PositiveNearLattice.isClopen_latV b v a M).isOpen
  set Dx : (Fin a → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ a := fun W =>
    gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x - gramH (Fv F v) σ hσ J hJ W
    with hDx
  have hDB : ∀ W, (Dx W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = gramB (Fv F v) σ J x W := by
    intro W
    rw [← gramR_add_sub]
    rfl
  have hDadd : ∀ W W', Dx (W + W') = Dx W + Dx W' := by
    intro W W'
    apply Subtype.ext
    rw [AddSubgroup.coe_add, hDB, hDB, hDB, gramB_add_right]
  have hDT : ∀ S : HermR (Fv F v) σ a, Dx (T S) = S := by
    intro S
    apply Subtype.ext
    rw [hDB]
    exact hq S.1 S.2
  show IsOpen (Dx '' (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)))
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨l, hl, rfl⟩
  have hU : IsOpen {S : HermR (Fv F v) σ a | T ((S - Dx l : HermR (Fv F v) σ a) :
      Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ L} :=
    hLo.preimage (hTc.comp (continuous_subtype_val.comp (continuous_id.sub continuous_const)))
  refine Filter.mem_of_superset (hU.mem_nhds ?_) ?_
  · show T ((Dx l - Dx l : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ L
    rw [sub_self, AddSubgroup.coe_zero, hT0]
    exact L.zero_mem
  · intro S hS
    refine ⟨l + T ((S - Dx l : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)),
      L.add_mem hl hS, ?_⟩
    rw [hDadd, hDT]
    abel

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVTop
section
namespace PI.VolStabS

theorem densV_of_gram (hF : GramFilt) : DensV :=
  densV_of_filt henselCount_holds cosDens_holds tensAll_holds hF

end PI.VolStabS
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FiniteOnCompacts
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology
open scoped TensorProduct

namespace RestrictedProductFiber

theorem finite_on_compacts {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [OpensMeasurableSpace V] [LocallyCompactSpace V] [T2Space V] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure V) (f : V → Y) (ι : X → Y) (U : Set V) (hU : IsOpen U)
    (ν : Measure X) (B : Set X) (fib : X → Measure V) (h : IsFibreFamily μ f ι U ν B fib)
    (b : X) (hb : b ∈ B) (hC : IsClosed (f ⁻¹' {ι b})) (hCU : f ⁻¹' {ι b} ⊆ U) :
    IsFiniteMeasureOnCompacts (fib b) := by
  refine ⟨fun K hK => ?_⟩
  have hK' : IsCompact (K ∩ f ⁻¹' {ι b}) := hK.inter_right hC
  obtain ⟨φ, h1, hφc, hφU, _h01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK' hU (Set.inter_subset_right.trans hCU)
  have hint : Integrable φ (fib b) :=
    (h.2.2 φ φ.continuous hφc hφU).1 b hb
  have hnull : fib b (f ⁻¹' {ι b} ∩ U)ᶜ = 0 := h.1 b
  have hM : fib b (K ∩ f ⁻¹' {ι b}) ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂(fib b) := by
    have hm : AEMeasurable (fun x => ENNReal.ofReal (φ x)) (fib b) :=
      (ENNReal.continuous_ofReal.comp φ.continuous).measurable.aemeasurable
    calc fib b (K ∩ f ⁻¹' {ι b}) ≤ fib b {x | 1 ≤ ENNReal.ofReal (φ x)} := by
          refine measure_mono fun x hx => ?_
          simp only [Set.mem_ofPred_eq, h1 hx, Pi.one_apply, ENNReal.ofReal_one, le_refl]
      _ = 1 * fib b {x | 1 ≤ ENNReal.ofReal (φ x)} := (one_mul _).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂(fib b) := mul_meas_ge_le_lintegral₀ hm 1
  calc fib b K ≤ fib b ((K ∩ f ⁻¹' {ι b}) ∪ (f ⁻¹' {ι b} ∩ U)ᶜ) := by
        refine measure_mono fun x hx => ?_
        by_cases hx2 : x ∈ f ⁻¹' {ι b} ∩ U
        · exact Or.inl ⟨hx, hx2.1⟩
        · exact Or.inr hx2
    _ ≤ fib b (K ∩ f ⁻¹' {ι b}) + fib b (f ⁻¹' {ι b} ∩ U)ᶜ := measure_union_le _ _
    _ = fib b (K ∩ f ⁻¹' {ι b}) := by rw [hnull, add_zero]
    _ < ⊤ := lt_of_le_of_lt hM hint.lintegral_lt_top

theorem fib_props {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] (hTF : TensFacts F E σ M J a R)
    (T : Matrix (Fin a) (Fin a) E) (hT : ∀ i j, σ (T j i) = T i j) (hdet : T.det ≠ 0)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    (fib : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E))
    (h : IsFibreFamily μ (gramR R σ J) Subtype.val
      {X | LinearIndependent (R ⊗[F] E) X} ν Set.univ fib) :
    SigmaFinite (fib (hermOf R σ T hT)) ∧
    ∀ Φ : (Fin a → Fin M → R ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable Φ (fib (hermOf R σ T hT)) := by
  obtain ⟨h1, h2, h3, _h4, h5, _h6, h7⟩ := hTF
  have : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have : T2Space (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → R ⊗[F] E))
  have hC : IsClosed (gramR R σ J ⁻¹' {((hermOf R σ T hT : HermR R σ a) :
      Matrix (Fin a) (Fin a) (R ⊗[F] E))}) := isClosed_singleton.preimage h5
  have hCU : gramR R σ J ⁻¹' {((hermOf R σ T hT : HermR R σ a) :
      Matrix (Fin a) (Fin a) (R ⊗[F] E))} ⊆ {X | LinearIndependent (R ⊗[F] E) X} := by
    intro X hX
    have hX' : gramR R σ J X = ((hermOf R σ T hT : HermR R σ a) :
        Matrix (Fin a) (Fin a) (R ⊗[F] E)) := hX
    have hu := isUnit_det_hermOf R σ T hT hdet
    rw [← hX'] at hu
    exact linIndep_of_isUnit_det R σ J X hu
  have hfin := finite_on_compacts μ (gramR R σ J) Subtype.val _ h7 ν Set.univ fib h
    (hermOf R σ T hT) (Set.mem_univ _) hC hCU
  have : SigmaCompactSpace (Fin a → Fin M → R ⊗[F] E) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  exact ⟨inferInstance, fun Φ hc hs => hc.integrable_of_hasCompactSupport hs⟩

end RestrictedProductFiber

theorem rpFib_holds : RPFib := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨hI, hV⟩ := tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  refine ⟨fun μ ν fib h => RestrictedProductFiber.fib_props σ J a (Ainf F) hI _ hT hdet μ ν fib h,
    fun v μ ν fib h => RestrictedProductFiber.fib_props σ J a (Fv F v) (hV v) _ hT hdet μ ν fib h⟩

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensSt
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter
open scoped TensorProduct

def qV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (Nat.card (𝓞 F ⧸ v.asIdeal) : ℝ)

def QvSum : Prop := ∀ (F : Type) [Field F] [NumberField F],
  Summable fun v : HeightOneSpectrum (𝓞 F) => (qV v)⁻¹ ^ 2

def ArchPos : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∃ Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φinf ∧ HasCompactSupport Φinf ∧
      ∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)) ≠ 0

def LocPos : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
    IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ∃ Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φv ∧
      ∫ X, Φv X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) ≠ 0

def DensAA : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ C : ℝ,
    ∀ᶠ v in cofinite,
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
    IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ‖∫ X, (latV b v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) - 1‖ ≤
      C * (qV v)⁻¹ ^ 2

theorem nuNeZero_of_dens (hA : ArchPos) (hL : LocPos) (hD : DensAA) (hQ : QvSum) : NuNeZero := by
  classical
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν h0
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨⟨μinf, hμinf⟩, a1⟩ := hν.2
  obtain ⟨⟨νinf, hνinf⟩, a2⟩ := a1 μinf hμinf
  obtain ⟨⟨μv, hμv⟩, a3⟩ := a2 νinf hνinf
  obtain ⟨⟨νv, hνv⟩, a4⟩ := a3 μv hμv
  obtain ⟨⟨fibInf, hfi⟩, a5⟩ := a4 νv hνv
  obtain ⟨⟨fibV, hfv⟩, a6⟩ := a5 fibInf hfi
  let b := Module.finBasis F E
  obtain ⟨C, hC⟩ := hD F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ _ b
  obtain ⟨Φinf, hcΦ, hcs, hIinf⟩ :=
    hA F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf fibInf hfi
  have hpos := fun v => hL F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v)
    (νv v) (hνv v) (fibV v) (hfv v)
  choose Φp hΦpSB hΦp using hpos
  let I : HeightOneSpectrum (𝓞 F) → ℂ := fun v =>
    ∫ X, (latV b v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 F) => C * (qV v)⁻¹ ^ 2 := (hQ F).mul_left C
  have hsmall : ∀ᶠ v in cofinite, C * (qV v)⁻¹ ^ 2 < 1 :=
    hsum.tendsto_cofinite_zero.eventually (gt_mem_nhds one_pos)
  let good : HeightOneSpectrum (𝓞 F) → Prop := fun v =>
    ‖I v - 1‖ ≤ C * (qV v)⁻¹ ^ 2 ∧ C * (qV v)⁻¹ ^ 2 < 1
  have hgood : ∀ᶠ v in cofinite, good v := by
    filter_upwards [hC, hsmall] with v hv1 hv2
    exact ⟨hv1 (μv v) (hμv v) (νv v) (hνv v) (fibV v) (hfv v), hv2⟩
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ := fun v =>
    if good v then (latV b v).indicator 1 else Φp v
  let Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ := fun Y => ∏ᶠ v, Φv v (projV v Y)
  let Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ := fun X => Φinf (projInf X) * Φf (projFin X)
  have hSB : ∀ v, IsSB (Φv v) := fun v => by
    by_cases h : good v
    · rw [show Φv v = (latV b v).indicator 1 from if_pos h]
      exact PositiveNearLattice.isSB_latV b v a M
    · rw [show Φv v = Φp v from if_neg h]
      exact hΦpSB v
  have hpure : IsPureFin b Φf Φv := by
    refine ⟨hSB, ?_, fun _ => rfl⟩
    filter_upwards [hgood] with v hv
    exact if_pos hv
  obtain ⟨-, -, heq⟩ := a6 fibV hfv _ b Φ Φinf Φf Φv hcΦ hcs hpure (fun _ => rfl)
  rw [h0, integral_zero_measure] at heq
  let Jv : HeightOneSpectrum (𝓞 F) → ℂ := fun v =>
    ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))
  have hJ0 : ∀ v, Jv v ≠ 0 := fun v => by
    by_cases h : good v
    · have e : Jv v = I v := by
        simp only [Jv, I, Φv, if_pos h]
      rw [e]
      intro hI
      have := h.1
      rw [hI, zero_sub, norm_neg, norm_one] at this
      linarith [h.2]
    · have e : Jv v = ∫ X, Φp v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) := by
        simp only [Jv, Φv, if_neg h]
      rw [e]
      exact hΦp v
  have hJs : Summable fun v => ‖Jv v - 1‖ := by
    refine Summable.of_norm_bounded_eventually hsum ?_
    filter_upwards [hgood] with v hv
    have e : Jv v = I v := by
      simp only [Jv, I, Φv, if_pos hv]
    rw [e, norm_norm]
    exact hv.1
  have hne : ∏' v, (1 + (Jv v - 1)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (fun v => by rw [add_sub_cancel]; exact hJ0 v) hJs
  simp only [add_sub_cancel] at hne
  exact mul_ne_zero hIinf hne heq.symm

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolB
section
noncomputable section

namespace PI.VolStabS

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

theorem hform_single {A : Type} [CommRing A] {M : ℕ} (s : A →+* A) (Am : Matrix (Fin M) (Fin M) A)
    (i j : Fin M) (x y : A) :
    Formalism.UG.hform s Am (Pi.single i x) (Pi.single j y) = s x * Am i j * y := by
  unfold Formalism.UG.hform
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      simp [hj']
    · simp
  · intro i' _ hi'
    simp [hi']
  · simp

def gG (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a : ℕ) :
    Matrix (Fin a × Fin M × Fin d) (Fin a × Fin M × Fin d) F :=
  fun q q' => if q.1 = q'.1 then Algebra.trace F E (σ (b q.2.2) * J q.2.1 q'.2.1 * b q'.2.2) else 0

def cT {a M : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    Fin a × Fin M × Fin d → Fv F v :=
  fun q => crd b (Fv F v) (Y q.1 q.2.1) q.2.2

variable [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))

theorem BR_eT (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (q q' : Fin a × Fin M × Fin d) :
    BR (Fv F v) σ J (eT v b q) (eT v b q') = algebraMap F (Fv F v) (gG b σ J a q q') := by
  obtain ⟨p, i, k⟩ := q
  obtain ⟨p', j, l⟩ := q'
  simp only [BR, eT]
  rw [Finset.sum_eq_single p (fun p'' _ h => by simp [Pi.single_apply, h, hR, Formalism.UG.hform])
    (by simp)]
  simp only [Pi.single_eq_same, gG]
  by_cases hp : p = p'
  · subst hp
    simp only [Pi.single_eq_same, if_true, hR, hform_single, JR, Matrix.map_apply]
    have e : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] b k) * inclR (Fv F v) (J i j) *
        ((1 : Fv F v) ⊗ₜ[F] b l) = (1 : Fv F v) ⊗ₜ[F] (σ (b k) * J i j * b l) := by
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR, Algebra.TensorProduct.tmul_mul_tmul]
    rw [e, trace_one_tmul]
  · have hp' : p' ≠ p := fun h => hp h.symm
    simp [Pi.single_apply, hp, hR, Formalism.UG.hform]

theorem BR_eT_left (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (q : Fin a × Fin M × Fin d) (Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J (eT v b q) Y =
      ((gG b σ J a).map (algebraMap F (Fv F v))).mulVec (cT b v Y) q := by
  have h := congrFun (congrArg (phiL (a := a) v b σ J) (sum_eT v b Y)) q
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  change BR (Fv F v) σ J (eT v b q) Y = _
  have h2 : phiL (a := a) v b σ J Y q = BR (Fv F v) σ J (eT v b q) Y := rfl
  rw [← h2, h]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, cT]
  refine Finset.sum_congr rfl fun q' _ => ?_
  have h3 : phiL (a := a) v b σ J (eT v b q') q = BR (Fv F v) σ J (eT v b q) (eT v b q') := rfl
  rw [h3, BR_eT, mul_comm]

theorem BR_eq_sum (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    BR (Fv F v) σ J X Y =
      ∑ q, cT b v X q * ((gG b σ J a).map (algebraMap F (Fv F v))).mulVec (cT b v Y) q := by
  rw [BR_expand v b σ J X Y]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [BR_eT_left]
  rfl

theorem cT_surj {a M : ℕ} (c : Fin a × Fin M × Fin d → Fv F v) :
    ∃ Y : Fin a → Fin M → Fv F v ⊗[F] E, cT b v Y = c := by
  refine ⟨fun p i => (Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm
    (fun k => c (p, i, k)), ?_⟩
  funext q
  obtain ⟨p, i, k⟩ := q
  simp only [cT, crd]
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem mem_latV_iff {a M : ℕ} (Y : Fin a → Fin M → Fv F v ⊗[F] E) :
    Y ∈ latV (M := M) (n := a) b v ↔ ∀ q, cT b v Y q ∈ v.adicCompletionIntegers F := by
  constructor
  · intro h q
    exact h q.1 q.2.1 q.2.2
  · intro h p i k
    exact h (p, i, k)

theorem mulVec_int {ι : Type} [Fintype ι] (A : Matrix ι ι F)
    (hA : ∀ i j, algebraMap F (Fv F v) (A i j) ∈ v.adicCompletionIntegers F)
    (w : ι → Fv F v) (hw : ∀ i, w i ∈ v.adicCompletionIntegers F) (i : ι) :
    (A.map (algebraMap F (Fv F v))).mulVec w i ∈ v.adicCompletionIntegers F := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact sum_mem fun j _ => mul_mem (hA i j) (hw j)


include v in
theorem det_gG [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) : (gG b σ J a).det ≠ 0 := by
  classical
  intro h0
  set G := (gG b σ J a).map (algebraMap F (Fv F v)) with hG
  have hdet : G.det = 0 := by
    rw [hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  obtain ⟨Y, hY⟩ := cT_surj b v (a := a) (M := M) w
  have hY0 : Y = 0 := by
    apply nondeg_BR v σ hσ J hJ Y
    intro X
    rw [BR_eq_sum, hY, hw]
    simp
  apply hw0
  rw [← hY, hY0]
  funext q
  simp [cT, crd]

theorem ev_dual [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) :
    ∀ᶠ v in cofinite, {Y | ∀ X ∈ latV (M := M) (n := a) b v,
      BR (Fv F v) σ J X Y ∈ v.adicCompletionIntegers F} = latV (M := M) (n := a) b v := by
  classical
  filter_upwards [ev_int_all (fun q : (Fin a × Fin M × Fin d) × (Fin a × Fin M × Fin d) =>
      gG b σ J a q.1 q.2),
    ev_int_all (fun q : (Fin a × Fin M × Fin d) × (Fin a × Fin M × Fin d) =>
      (gG b σ J a)⁻¹ q.1 q.2)] with v h1 h2
  have hdet := det_gG b v σ hσ J hJ (a := a)
  set g := gG b σ J a with hg
  ext Y
  constructor
  · intro hY
    rw [Set.mem_setOf_eq] at hY
    rw [mem_latV_iff]
    have hw : ∀ q, (g.map (algebraMap F (Fv F v))).mulVec (cT b v Y) q ∈
        v.adicCompletionIntegers F := by
      intro q
      rw [← BR_eT_left]
      exact hY _ (eT_mem v b q)
    have hinv : (g⁻¹.map (algebraMap F (Fv F v))).mulVec
        ((g.map (algebraMap F (Fv F v))).mulVec (cT b v Y)) = cT b v Y := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul g (isUnit_iff_ne_zero.2 hdet), Matrix.map_one _ (map_zero _)
        (map_one _), Matrix.one_mulVec]
    intro q
    rw [← hinv]
    exact mulVec_int v g⁻¹ (fun i j => h2 (i, j)) _ hw q
  · intro hY
    rw [Set.mem_setOf_eq]
    intro X hX
    rw [BR_eq_sum]
    rw [mem_latV_iff] at hX hY
    exact sum_mem fun q _ => mul_mem (hX q) (mulVec_int v g (fun i j => h1 (i, j)) _ hY q)

end VolAAW

end PI.VolStabS
end
end

