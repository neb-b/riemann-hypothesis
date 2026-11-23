module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensGen
section
noncomputable section

namespace PI.VolStabSW.DensGen

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {U : Set V} {ν : Measure X} {B : Set X}
  {fib : X → Measure V}

theorem ae_fib (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X}
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (b : X) :
    ∀ᵐ v ∂(fib b), f' v = b := by
  have h := hfib.1 b
  rw [ae_iff]
  refine measure_mono_null ?_ h
  intro v hv hmem
  exact hv (hι (by rw [← hff' v]; exact hmem.1))

theorem fib_set_nonneg [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (hρ0 : ∀ v, 0 ≤ ρ v) (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
  classical
  obtain ⟨hint, hGc⟩ := hfib.2.2 ρ hρc hρs hρU
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hS'm : MeasurableSet (f' ⁻¹' S) := (hS.isClosed.preimage hf').measurableSet
  have hρm : Measurable fun v => ENNReal.ofReal (ρ v) := hρc.measurable.ennreal_ofReal
  have hmain : ∫⁻ v in f' ⁻¹' S, ENNReal.ofReal (ρ v) ∂μ =
      ∫⁻ b in S, ∫⁻ v, ENNReal.ofReal (ρ v) ∂(fib b) ∂ν := by
    have key := hfib.2.1 ((f' ⁻¹' S).indicator fun v => ENNReal.ofReal (ρ v)) (hρm.indicator hS'm)
    have hsupp : Function.support ((f' ⁻¹' S).indicator fun v => ENNReal.ofReal (ρ v)) ⊆ U := by
      intro v hv
      apply hρU
      apply subset_tsupport
      intro h0
      apply hv
      simp [Set.indicator, h0]
    rw [setLIntegral_eq_of_support_subset hsupp, lintegral_indicator hS'm] at key
    rw [key, ← lintegral_indicator hSm]
    apply lintegral_congr
    intro b
    have hae := ae_fib hfib hff' hι b
    by_cases hb : b ∈ S
    · rw [Set.indicator_apply, if_pos hb]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with v hv
      have hv' : v ∈ f' ⁻¹' S := by
        show f' v ∈ S
        rw [hv]
        exact hb
      rw [Set.indicator_apply, if_pos hv']
    · rw [Set.indicator_apply, if_neg hb]
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [hae] with v hv
      have hv' : v ∉ f' ⁻¹' S := by
        show f' v ∉ S
        rw [hv]
        exact hb
      rw [Set.indicator_apply, if_neg hv']
  have hG0 : ∀ b, 0 ≤ ∫ v, ρ v ∂(fib b) := fun b => integral_nonneg hρ0
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hρ0) hρc.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hG0)
      ((hGc.mono hSB).aestronglyMeasurable hSm), hmain]
  congr 1
  refine lintegral_congr_ae ((ae_restrict_iff' hSm).mpr (Filter.Eventually.of_forall fun b hb => ?_))
  exact (ofReal_integral_eq_lintegral_ofReal (hint b (hSB hb)) (Filter.Eventually.of_forall hρ0)).symm

theorem fib_set [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (hfib : IsFibreFamily μ f ι U ν B fib) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι)
    (ρ : V → ℝ) (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρU : tsupport ρ ⊆ U)
    (S : Set X) (hS : IsCompact S) (hSB : S ⊆ B) :
    ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
  set ρp : V → ℝ := fun v => max (ρ v) 0 with hρpdef
  set ρn : V → ℝ := fun v => max (-ρ v) 0 with hρndef
  have hρeq : ρ = fun v => ρp v - ρn v :=
    funext fun v => (max_zero_sub_max_neg_zero_eq_self (ρ v)).symm
  have hcp : Continuous ρp := hρc.max continuous_const
  have hcn : Continuous ρn := hρc.neg.max continuous_const
  have hsp : HasCompactSupport ρp := hρs.comp_left (g := fun x : ℝ => max x 0) (by simp)
  have hsn : HasCompactSupport ρn := hρs.neg.comp_left (g := fun x : ℝ => max x 0) (by simp)
  have hup : tsupport ρp ⊆ U := (tsupport_comp_subset (g := fun x : ℝ => max x 0) (by simp) ρ).trans hρU
  have hun : tsupport ρn ⊆ U := by
    refine (tsupport_comp_subset (g := fun x : ℝ => max x 0) (by simp) (-ρ)).trans ?_
    rw [tsupport_neg]
    exact hρU
  have hp := fib_set_nonneg hfib hf' hff' hι ρp hcp hsp hup (fun v => le_max_right _ _) S hS hSB
  have hn := fib_set_nonneg hfib hf' hff' hι ρn hcn hsn hun (fun v => le_max_right _ _) S hS hSB
  have hip : Integrable ρp μ := hcp.integrable_of_hasCompactSupport hsp
  have hin : Integrable ρn μ := hcn.integrable_of_hasCompactSupport hsn
  obtain ⟨hintp, hGp⟩ := hfib.2.2 ρp hcp hsp hup
  obtain ⟨hintn, hGn⟩ := hfib.2.2 ρn hcn hsn hun
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  calc ∫ v in f' ⁻¹' S, ρ v ∂μ = ∫ v in f' ⁻¹' S, ρp v ∂μ - ∫ v in f' ⁻¹' S, ρn v ∂μ := by
        rw [hρeq]
        exact integral_sub hip.integrableOn hin.integrableOn
    _ = ∫ b in S, (∫ v, ρp v ∂(fib b)) ∂ν - ∫ b in S, (∫ v, ρn v ∂(fib b)) ∂ν := by rw [hp, hn]
    _ = ∫ b in S, ((∫ v, ρp v ∂(fib b)) - ∫ v, ρn v ∂(fib b)) ∂ν :=
        (integral_sub ((hGp.mono hSB).integrableOn_compact hS)
          ((hGn.mono hSB).integrableOn_compact hS)).symm
    _ = ∫ b in S, (∫ v, ρ v ∂(fib b)) ∂ν := by
        refine setIntegral_congr_fun hSm (fun b hb => ?_)
        rw [hρeq]
        exact (integral_sub (hintp b (hSB hb)) (hintn b (hSB hb))).symm

theorem eq_zero_of_setIntegral [LocallyCompactSpace X] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] (D : X → ℝ) (W : Set X) (b0 : X) (hW : W ∈ 𝓝 b0)
    (hD : ContinuousOn D W) (h0 : ∀ S, IsCompact S → S ⊆ W → ∫ b in S, D b ∂ν = 0) :
    D b0 = 0 := by
  by_contra hne
  have hpos : 0 < D b0 * D b0 := mul_self_pos.mpr hne
  have hcont : ContinuousAt (fun b => D b0 * D b) b0 :=
    continuousAt_const.mul (hD.continuousAt hW)
  have hev : ∀ᶠ b in 𝓝 b0, D b0 * D b0 / 2 < D b0 * D b :=
    hcont.eventually (lt_mem_nhds (by linarith))
  obtain ⟨K, hK, hKsub, hKc⟩ := local_compact_nhds (Filter.inter_mem hW hev)
  have hKW : K ⊆ W := fun x hx => (hKsub hx).1
  have h0K := h0 K hKc hKW
  have hKpos : 0 < ν K := Measure.measure_pos_of_mem_nhds ν hK
  have hKfin : ν K < ⊤ := hKc.measure_lt_top
  have hint : IntegrableOn D K ν := (hD.mono hKW).integrableOn_compact hKc
  have hle : ∫ b in K, D b0 * D b0 / 2 ∂ν ≤ ∫ b in K, D b0 * D b ∂ν :=
    setIntegral_mono_on (integrableOn_const hKfin.ne) (hint.const_mul (D b0))
      hKc.isClosed.measurableSet (fun b hb => le_of_lt (hKsub hb).2)
  rw [integral_const_mul, h0K, mul_zero, setIntegral_const, smul_eq_mul] at hle
  have hr : 0 < ν.real K := ENNReal.toReal_pos hKpos.ne' hKfin.ne
  have : 0 < ν.real K * (D b0 * D b0 / 2) := mul_pos hr (by linarith)
  linarith

end PI.VolStabSW.DensGen
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibOfTens
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct

def DensAll {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (U : Set V) :
    Prop :=
  ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, g b ∂ν

def FibOfDens : Prop :=
  ∀ (V X Y : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [LocallyCompactSpace V]
    [T2Space V] [SecondCountableTopology V] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] [T2Space Y] (μ : Measure V) (ν : Measure X),
    IsFiniteMeasureOnCompacts μ → IsFiniteMeasureOnCompacts ν → ν.IsOpenPosMeasure →
    ∀ (f : V → Y) (ι : X → Y) (U : Set V), Continuous f → IsClosedEmbedding ι →
      (∀ v, f v ∈ Set.range ι) → IsOpen U → DensAll μ f ι ν U →
      ∃ fib : X → Measure V, IsFibreFamily μ f ι U ν Set.univ fib

def TensFacts (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] : Prop :=
  LocallyCompactSpace (R ⊗[F] E) ∧ T2Space (R ⊗[F] E) ∧ SecondCountableTopology (R ⊗[F] E) ∧
    IsClosed (HermR R σ a : Set (Matrix (Fin a) (Fin a) (R ⊗[F] E))) ∧
    Continuous (gramR R σ J (n := a)) ∧ (∀ X, gramR R σ J (n := a) X ∈ HermR R σ a) ∧
    IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}

theorem fib_of_tens {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} {a : ℕ} {R : Type} [CommRing R] [Algebra F R]
    [TopologicalSpace R] (hG : FibOfDens) (hT : TensFacts F E σ M J a R)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (hD : DensAll μ (gramR R σ J) Subtype.val ν {X | LinearIndependent (R ⊗[F] E) X}) :
    ∃ fib : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E),
      IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
        Set.univ fib := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hT
  have : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR R σ a) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → R ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → R ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → R ⊗[F] E))
  have : LocallyCompactSpace (HermR R σ a) := h4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (HermR R σ a) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  exact hG _ _ _ μ ν inferInstance inferInstance inferInstance _ _ _ h5
    h4.isClosedEmbedding_subtypeVal (fun X => ⟨⟨_, h6 X⟩, rfl⟩) h7 hD

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.PosNear
section
noncomputable section

namespace PI.VolStabSW

namespace PositiveNearLattice

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) (k : Fin d) : R :=
  (Algebra.TensorProduct.basis R b).repr y k

theorem crd_map {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
    (f : R →ₐ[F] S) (y : R ⊗[F] E) (k : Fin d) :
    crd b S (Algebra.TensorProduct.map f (AlgHom.id F E) y) k = f (crd b R y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp [crd]
  | tmul r e =>
    simp [crd, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul]
  | add x y hx hy =>
    simp only [crd] at hx hy ⊢
    rw [map_add (f := _), map_add (f := _), Finsupp.add_apply, hx, hy, map_add (f := _), Finsupp.add_apply, map_add (f := _)]

theorem crd_incl (R : Type) [CommRing R] [Algebra F R] (x : E) (k : Fin d) :
    crd b R (inclR R x) k = algebraMap F R (b.repr x k) := by
  simp [crd, inclR, Algebra.TensorProduct.basis_repr_tmul]

theorem eq_sum_crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) :
    y = ∑ i, crd b R y i • ((1 : R) ⊗ₜ[F] b i) := by
  have := (Algebra.TensorProduct.basis R b).sum_repr y
  simp only [Algebra.TensorProduct.basis_apply] at this
  exact this.symm

variable [FiniteDimensional F E]

theorem continuous_crd (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (k : Fin d) : Continuous (fun y : R ⊗[F] E => crd b R y k) :=
  IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis R b).coord k)

include b in
theorem continuous_map_tens {R S : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing S] [Algebra F S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →ₐ[F] S) (hf : Continuous f) :
    Continuous (Algebra.TensorProduct.map f (AlgHom.id F E)) := by
  have e : (⇑(Algebra.TensorProduct.map f (AlgHom.id F E))) =
      fun y => ∑ k, f (crd b R y k) • ((1 : S) ⊗ₜ[F] b k) := by
    funext y
    rw [eq_sum_crd b S (Algebra.TensorProduct.map f (AlgHom.id F E) y)]
    simp only [crd_map]
  rw [e]
  refine continuous_finsetSum _ fun k _ => ?_
  exact continuous_smul.comp ((hf.comp (continuous_crd b R k)).prodMk continuous_const)

end Coord

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

theorem isClosed_int : IsClosed (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).isClosed

theorem isClopen_latV (a M : ℕ) : IsClopen (latV (M := M) (n := a) b v) := by
  have hc : ∀ (x : Fin a) (i : Fin M) (k : Fin d),
      Continuous (fun Y : Fin a → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) :=
    fun x i k => (continuous_crd b (Fv F v) k).comp ((continuous_apply i).comp (continuous_apply x))
  have e : latV (M := M) (n := a) b v = ⋂ x, ⋂ i, ⋂ k,
      (fun Y : Fin a → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) ⁻¹'
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    ext Y
    simp [latV, crd]
  rw [e]
  refine ⟨isClosed_iInter fun x => isClosed_iInter fun i => isClosed_iInter fun k =>
    (isClosed_int v).preimage (hc x i k), isOpen_iInter_of_finite fun x =>
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k =>
    (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).preimage (hc x i k)⟩

theorem isCompact_latV (a M : ℕ) : IsCompact (latV (M := M) (n := a) b v) := by
  let L : (Fin a → Fin M → Fin d → Fv F v) → (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun c x i => ∑ k, c x i k • ((1 : Fv F v) ⊗ₜ[F] b k)
  have hL : Continuous L := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk
        continuous_const)
  let K : Set (Fin a → Fin M → Fin d → Fv F v) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v
  refine (hK.image hL).of_isClosed_subset (isClopen_latV b v a M).isClosed ?_
  intro Y hY
  refine ⟨fun x i k => crd b (Fv F v) (Y x i) k, ?_, ?_⟩
  · simp only [K, Set.mem_pi, Set.mem_univ, true_implies]
    intro x i k
    exact hY x i k
  · funext x i
    exact (eq_sum_crd b (Fv F v) (Y x i)).symm

end Loc

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

variable [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)



end Main

end PositiveNearLattice

open PositiveNearLattice
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Unimod
section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal

section Gen

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

end Gen

section Spec

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.AdicCompletionValuation NumberField
open scoped TensorProduct

theorem um_countable_HFinIn (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    Countable (HFinIn (AF F) σ J) := by
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have : Countable (Matrix (Fin M) (Fin M) E) := inferInstanceAs (Countable (Fin M → Fin M → E))
  have : Countable (GL (Fin M) E) :=
    Function.Injective.countable (f := fun u : GL (Fin M) E => (u : Matrix (Fin M) (Fin M) E))
      (fun _ _ h => Units.ext h)
  have hx : ∀ x : HFinIn (AF F) σ J, ∃ u : GL (Fin M) E,
      Formalism.UG.bc (inclR (AF F)) u = ((x : HR (AF F) σ J) : GL (Fin M) (AF F ⊗[F] E)) := by
    intro x
    have h : ((x : HR (AF F) σ J) : GL (Fin M) (AF F ⊗[F] E)) ∈ HFin (AF F) σ J :=
      Subgroup.mem_subgroupOf.1 x.2
    unfold HFin at h
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 h
    exact ⟨u, hu⟩
  refine Function.Injective.countable (f := fun x => (hx x).choose) ?_
  intro x y hxy
  have h1 := (hx x).choose_spec
  have h2 := (hx y).choose_spec
  simp only at hxy
  rw [hxy] at h1
  exact Subtype.ext (Subtype.ext (h1.symm.trans h2))

end Spec

end PI.VolStabSW
end
end

