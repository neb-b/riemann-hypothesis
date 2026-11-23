module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0018
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpInj
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0015
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensMuF
section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

def BetaSym : Prop := ∀ {D : D7} (X : HidaSetting D) (x y : EuclideanSpace ℝ (KapI X)), betaI X x y = betaI X y x


open Classical in
def MatND : Prop := ∀ {D : D7} (X : HidaSetting D), (matI X).det ≠ 0

section
variable {D : D7} (X : HidaSetting D)


open Classical in
def Alin : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X) :=
  ((EuclideanSpace.equiv (KapI X) ℝ).toLinearEquiv.symm : (KapI X → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) ∘ₗ
    Matrix.toLin' (matI X) ∘ₗ
    ((EuclideanSpace.equiv (KapI X) ℝ).toLinearEquiv.symm.symm : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] (KapI X → ℝ))

open Classical in
theorem det_Alin : LinearMap.det (Alin X) = (matI X).det := by
  rw [Alin, LinearMap.det_conj, LinearMap.det_toLin']

theorem inner_Alin (x y : EuclideanSpace ℝ (KapI X)) : ⟪x, Alin X y⟫ = betaI X x y := by
  classical
  rw [betaI_expand]
  simp only [Alin, PiLp.inner_apply, LinearMap.coe_comp, Function.comp_apply, Matrix.toLin'_apply,
    LinearEquiv.coe_coe]
  simp
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct]
  have hy : ∀ j, (EuclideanSpace.equiv (KapI X) ℝ) y j = y j := fun j => rfl
  simp only [hy]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end


end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibNear
section
namespace PI.AprimeInfW

theorem unitsOpenTens : UnitsOpenTens := fun X => isOpen_units_tens X

theorem fibOrbAt_of_compact (hC : MassDataMassesW.HinfCompact) : FibOrbAt :=
  fibOrbAt_of unitsOpenTens fibAllT_holds hC

end PI.AprimeInfW
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpDens
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

def phi0 {D : D7} (X : HidaSetting D) {ι η : Type}
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (L₁ : EuclideanSpace ℝ η →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ))
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) : X.B.I.Ginf :=
  (fun v => expU (X.B.I.ε v) (L p.1 v)) * (fun v => expU (X.B.I.ε v) (L₁ p.2 v))

def GinfDens : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η] L L₁,
    @StdCtx D X u' hb c S ι η _ _ L L₁ → ∃ r : ℝ, 0 < r ∧ ∃ d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ,
      ContinuousAt d 0 ∧ d 0 = Formalism.MainNotions.S.AutInst.gaugeU X.B.I ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r, MeasurableSet A →
        MeasurableSet (phi0 X L L₁ '' A) ∧
        Formalism.L2.SG.ProjRows.muInf X.B.I (phi0 X L L₁ '' A) = ∫⁻ p in A, ENNReal.ofReal (d p)

theorem grpDens_of (hG : GinfDens) (hU : UnimodInf) : GrpDens := by
  intro D X u' hb c S ι η _ _ L L₁ ctx
  obtain ⟨ψ, hT, μinf, νinf, fibInf, hP⟩ := ctx.1
  obtain ⟨hb', FdN, FdN', u, hX⟩ := hP.1
  have hGt : X.measG.μGinf = (Formalism.L2.SG.ProjRows.muInf X.B.I).map (X.toInf hb) := hX.1.2.1
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have : SecondCountableTopology (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  have : PolishSpace X.B.I.Ginf := PI.AprimeInfA.polish_of_lcsc _
  have hemb : MeasurableEmbedding (X.toInf hb) :=
    (MassDataMassesW.continuous_toInf X hb).measurableEmbedding (toInf_injective X hb)
  obtain ⟨r, hr, d, hdc, hd0, hd⟩ := hG X u' hb c S L L₁ ctx
  refine ⟨r, hr, d, hdc, hd0, fun A hA hAm => ?_⟩
  obtain ⟨hmeas, heq⟩ := hd A hA hAm
  set k := X.toInf hb c with hk
  set B' := X.toInf hb '' (phi0 X L L₁ '' A) with hB'
  have hB'm : MeasurableSet B' := hemb.measurableSet_image.2 hmeas
  have hpt : ∀ p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η,
      kap0 X hb c L p.1 * chiOf X hb c L₁ p.2 = k * X.toInf hb (phi0 X L L₁ p) * k⁻¹ := by
    intro p
    unfold kap0 chiOf phi0
    change toInfHom X hb _ * toInfHom X hb _ = toInfHom X hb c * toInfHom X hb _ * (toInfHom X hb c)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    group
  have himg : (fun p => kap0 X hb c L p.1 * chiOf X hb c L₁ p.2) '' A =
      (fun g => k⁻¹ * g * k) ⁻¹' B' := by
    ext g
    constructor
    · rintro ⟨p, hp, rfl⟩
      show k⁻¹ * (kap0 X hb c L p.1 * chiOf X hb c L₁ p.2) * k ∈ B'
      rw [hpt p]
      exact ⟨phi0 X L L₁ p, ⟨p, hp, rfl⟩, by group⟩
    · rintro ⟨y, ⟨p, hp, rfl⟩, hy⟩
      refine ⟨p, hp, ?_⟩
      show kap0 X hb c L p.1 * chiOf X hb c L₁ p.2 = g
      rw [hpt p, hy]
      group
  have hinv : X.measG.μGinf ((fun g => k⁻¹ * g * k) ⁻¹' B') = X.measG.μGinf B' := by
    have hpm : MeasurableSet ((fun g => k⁻¹ * g * k) ⁻¹' B') :=
      ((continuous_const.mul continuous_id).mul continuous_const).measurable hB'm
    calc X.measG.μGinf ((fun g => k⁻¹ * g * k) ⁻¹' B')
        = ∫⁻ g, B'.indicator 1 (k⁻¹ * g * k) ∂X.measG.μGinf := by
          rw [← lintegral_indicator_one hpm]
          rfl
      _ = ∫⁻ g, B'.indicator 1 (k⁻¹ * g) ∂X.measG.μGinf := by
          have := hU X u' ψ hT μinf νinf fibInf hP (fun x => B'.indicator 1 (k⁻¹ * x)) k
          simpa [mul_assoc] using this
      _ = ∫⁻ g, B'.indicator 1 g ∂X.measG.μGinf :=
          lintegral_mul_left_eq_self (fun g => B'.indicator (1 : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J → ENNReal) g) k⁻¹
      _ = X.measG.μGinf B' := lintegral_indicator_one hB'm
  rw [himg, hinv, hGt, hemb.map_apply, hB', (toInf_injective X hb).preimage_image, heq]

def PlaceCharts : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) hb c S {ι η : Type} [Fintype ι] [Fintype η]
    L L₁, @StdCtx D X u' hb c S ι η _ _ L L₁ →
    ∃ (α β : NumberField.InfinitePlace X.B.I.F → Type) (_ : ∀ v, Fintype (α v)) (_ : ∀ v, Fintype (β v))
      (Φ : ∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v) → Formalism.REAL.UJ (X.B.I.ε v))
      (Dv : ∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v) → ℝ)
      (U : ∀ v, Set (EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v)))
      (T : (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) ≃ᵐ (∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v)))
      (r : ℝ),
      (∀ v, MeasurableSet (U v)) ∧ (∀ v, Continuous (Φ v)) ∧ (∀ v, Set.InjOn (Φ v) (U v)) ∧
      (∀ v, Measurable (Dv v)) ∧ (∀ v z, 0 ≤ Dv v z) ∧
      (∀ v, ∀ A ⊆ U v, MeasurableSet A →
        Formalism.REAL.muG (X.B.I.ε v) (Φ v '' A) = ∫⁻ z in A, ENNReal.ofReal (Dv v z)) ∧
      MeasurePreserving T volume (Measure.pi fun v => volume) ∧ Continuous T ∧ 0 < r ∧
      (∀ p ∈ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r, T p ∈ Set.univ.pi U) ∧
      (∀ p ∈ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r, phi0 X L L₁ p = fun v => Φ v (T p v)) ∧
      ContinuousAt (fun z : ∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v) => ∏ v, Dv v (z v)) (T 0) ∧
      ∏ v, Dv v (T 0 v) = Formalism.MainNotions.S.AutInst.gaugeU X.B.I

theorem ginfDens_of (h : PlaceCharts) : GinfDens := by
  intro D X u' hb c S ι η _ _ L L₁ ctx
  obtain ⟨α, β, hα, hβ, Φ, Dv, U, T, r, hUm, hΦc, hΦi, hDm, hD0, hdens, hT, hTc, hr, hTU, hphi, hcont, hval⟩ :=
    h X u' hb c S L L₁ ctx
  have : PolishSpace X.B.I.Ginf := PI.AprimeInfA.polish_of_lcsc _
  refine ⟨r, hr, fun p => ∏ v, Dv v (T p v), ?_, hval, fun A hA hAm => ?_⟩
  · exact ContinuousAt.comp (g := fun z : ∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v) => ∏ v, Dv v (z v)) hcont
      hTc.continuousAt
  have himg : phi0 X L L₁ '' A = (fun z v => Φ v (z v)) '' (T '' A) := by
    rw [Set.image_image]
    exact Set.image_congr fun p hp => hphi p (hA hp)
  have hTA : MeasurableSet (T '' A) := T.measurableSet_image.2 hAm
  have hTAU : T '' A ⊆ Set.univ.pi U := by
    rintro _ ⟨p, hp, rfl⟩
    exact hTU p (hA hp)
  have hinj : Set.InjOn (fun z : ∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) (Set.univ.pi U) := by
    intro z hz z' hz' he
    funext v
    exact hΦi v (hz v (Set.mem_univ v)) (hz' v (Set.mem_univ v)) (congr_fun he v)
  have hcΦ : Continuous (fun z : ∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) :=
    continuous_pi fun v => (hΦc v).comp (continuous_apply v)
  have hmeas : MeasurableSet ((fun z : ∀ v, EuclideanSpace ℝ (α v) × EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) '' (T '' A)) :=
    hTA.image_of_continuousOn_injOn hcΦ.continuousOn (hinj.mono hTAU)
  refine ⟨himg ▸ hmeas, ?_⟩
  rw [himg, Formalism.L2.SG.ProjRows.muInf,
    PI.AprimeInfG.pi_chart_dens (fun v => Formalism.REAL.muG (X.B.I.ε v)) (fun _ => volume) Φ
      (fun v => (hΦc v).measurable) U hUm hΦi Dv hDm hdens (T '' A) hTAU hTA hmeas,
    ← hT.setLIntegral_comp_emb T.measurableEmbedding]
  refine lintegral_congr fun p => ?_
  rw [ENNReal.ofReal_prod_of_nonneg fun v _ => hD0 v _]

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.StdConjExOfWitt
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
  Formalism.L2.SG.Measures
open scoped TensorProduct Matrix

theorem theta_lin_indep {F E : Type} [Field F] [Field E] [Algebra F E] (φ : E →+* ℂ) (σ : E →+* E)
    (hσφ : ∀ a, φ (σ a) = starRingEnd ℂ (φ a)) (hfix : ∀ a, σ a = a → a ∈ Set.range (algebraMap F E))
    (b : Module.Basis (Fin 2) F E) (r : Fin 2 → ℝ) (h : (r 0 : ℂ) * φ (b 0) + (r 1 : ℂ) * φ (b 1) = 0) :
    r 0 = 0 ∧ r 1 = 0 := by
  have hb0 : b 0 ≠ 0 := b.ne_zero 0
  have hφ0 : φ (b 0) ≠ 0 := (map_ne_zero φ).2 hb0
  have hr1 : r 1 = 0 := by
    by_contra hr
    have hr' : (r 1 : ℂ) ≠ 0 := by exact_mod_cast hr
    set γ := b 1 / b 0 with hγ
    have hφγ : φ γ = ((-(r 0 / r 1) : ℝ) : ℂ) := by
      rw [hγ, map_div₀, div_eq_iff hφ0]
      push_cast
      field_simp
      first | linear_combination h | linear_combination -h | linear_combination (↑(r 1) : ℂ)⁻¹ * h
    have hσγ : σ γ = γ := by
      apply φ.injective
      rw [hσφ, hφγ, Complex.conj_ofReal]
    obtain ⟨a, ha⟩ := hfix γ hσγ
    have h1 : b 1 = a • b 0 := by
      rw [Algebra.smul_def, ha, hγ, div_mul_cancel₀ _ hb0]
    exact absurd h1 (by
      intro e
      have hli := b.linearIndependent
      rw [Fintype.linearIndependent_iff] at hli
      have := hli (fun i => if i = 0 then a else -1) (by
        rw [Fin.sum_univ_two]
        simp [e])
      simpa using this 1)
  refine ⟨?_, hr1⟩
  rw [hr1] at h
  simp only [Complex.ofReal_zero, zero_mul, add_zero, mul_eq_zero, hφ0, or_false] at h
  exact_mod_cast h

theorem thetaInf_tmul {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (c : Ainf X.B.I.F) (e : X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (c ⊗ₜ[X.B.I.F] e) = PI.AprimeInfU.evInf X v c * X.B.I.φ v e := by
  simp only [PI.AprimeInfU.thetaInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul]
  rfl

theorem thetaInf_inj {D : D7} (X : HidaSetting D) (y : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)
    (h : ∀ v, PI.AprimeInfU.thetaInf X v y = 0) : y = 0 := by
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  let b : Module.Basis (Fin 2) X.B.I.F X.B.I.E := Module.finBasisOfFinrankEq X.B.I.F X.B.I.E X.B.I.cm.deg2
  let B := Algebra.TensorProduct.basis (Ainf X.B.I.F) b
  have hy : y = ∑ i, B.repr y i ⊗ₜ[X.B.I.F] b i := by
    conv_lhs => rw [← B.sum_repr y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hc : ∀ i, B.repr y i = 0 := by
    intro i
    change (B.repr y i : (v : InfinitePlace X.B.I.F) → v.Completion) = 0
    funext v
    have hvr : v.IsReal := IsTotallyReal.isReal v
    have hv := h v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, map_sum, Fin.sum_univ_two, thetaInf_tmul, thetaInf_tmul] at hv
    have hev : ∀ c : Ainf X.B.I.F, PI.AprimeInfU.evInf X v c =
        ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hvr
          ((c : (w : InfinitePlace X.B.I.F) → w.Completion) v) : ℝ) : ℂ) := by
      intro c
      rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
      rfl
    rw [hev, hev] at hv
    have key := theta_lin_indep (X.B.I.φ v) (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E)
      (fun a => X.B.I.cm.cmUnram.2.1 (X.B.I.φ v) a)
      (fun a ha => RingHom.mem_range.1 ((X.B.I.cm.fixed a).1 ha)) b
      (fun i => InfinitePlace.Completion.extensionEmbeddingOfIsReal hvr
        ((B.repr y i : (w : InfinitePlace X.B.I.F) → w.Completion) v)) hv
    have hz : InfinitePlace.Completion.extensionEmbeddingOfIsReal hvr
        ((B.repr y i : (w : InfinitePlace X.B.I.F) → w.Completion) v) = 0 := by
      fin_cases i
      · exact key.1
      · exact key.2
    exact (map_eq_zero_iff _ (InfinitePlace.Completion.extensionEmbeddingOfIsReal hvr).injective).1 hz
  rw [hy]
  simp [hc]

theorem thetaInf_inclR {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (e : X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (inclR (Ainf X.B.I.F) e) = X.B.I.φ v e := by
  rw [show inclR (Ainf X.B.I.F) e = (1 : Ainf X.B.I.F) ⊗ₜ[X.B.I.F] e from rfl, thetaInf_tmul, map_one, one_mul]

theorem uMat_toInf {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x : X.B.I.Ginf)
    (v : InfinitePlace X.B.I.F) :
    uMat (x v) = (X.B.I.P v)⁻¹ * (((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (X.toInf hb x) :
      GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))).map (PI.AprimeInfU.thetaInf X v) *
      X.B.I.P v := by
  have e : uMat (x v) = ofHAInf X.B.I (toHA X.B.I hb (x, 1)) v := ((toHA_isBridge X.B.I hb) (x, 1)).1 v
  rw [e]
  unfold ofHAInf
  congr 2
  ext i j
  simp only [Matrix.map_apply, PI.AprimeInfU.thetaV_eq]
  rfl

theorem stabInfV_holds : StabInfV := by
  intro D X u' hb x
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  set Mm : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :=
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (X.toInf hb x) : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) with hMm
  have hPu : ∀ v, IsUnit (X.B.I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hmap : ∀ v, Mm.map (PI.AprimeInfU.thetaInf X v) = X.B.I.P v * uMat (x v) * (X.B.I.P v)⁻¹ := by
    intro v
    rw [uMat_toInf X hb x v, ← hMm]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hPu v), Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hPu v), Matrix.mul_one]
  have hvec : ∀ v b i, PI.AprimeInfU.thetaInf X v ((Mm *ᵥ Y0 X u' b) i) =
      ((Mm.map (PI.AprimeInfU.thetaInf X v)) *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j)) i := by
    intro v b i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show Y0 X u' b j = inclR (Ainf X.B.I.F) (tupH (frameOf X u') b j) from rfl, thetaInf_inclR]
  have hY0 : ∀ v b i, PI.AprimeInfU.thetaInf X v (Y0 X u' b i) = X.B.I.φ v (tupH (frameOf X u') b i) := by
    intro v b i
    rw [show Y0 X u' b i = inclR (Ainf X.B.I.F) (tupH (frameOf X u') b i) from rfl, thetaInf_inclR]
  have hsmul : X.toInf hb x • Y0 X u' = fun b => Mm *ᵥ Y0 X u' b := rfl
  rw [MulAction.mem_stabilizer_iff, hsmul]
  constructor
  · intro hfix v b
    have h1 : (Mm.map (PI.AprimeInfU.thetaInf X v)) *ᵥ (fun j => X.B.I.φ v (tupH (frameOf X u') b j)) =
        fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
      funext i
      rw [← hvec, ← hY0]
      exact congrArg (PI.AprimeInfU.thetaInf X v) (congrFun (congrFun hfix b) i)
    rw [hmap] at h1
    unfold wV
    have h2 := congrArg (fun z => (X.B.I.P v)⁻¹ *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hPu v), Matrix.one_mul] at h2
    rw [Matrix.mulVec_mulVec]
    exact h2
  · intro hw
    funext b i
    have h0 : Mm *ᵥ Y0 X u' b - Y0 X u' b = 0 := by
      funext i'
      refine thetaInf_inj X _ fun v => ?_
      rw [Pi.sub_apply, map_sub, hvec, hY0, hmap, sub_eq_zero]
      have hv := hw v b
      unfold wV at hv
      calc ((X.B.I.P v * uMat (x v) * (X.B.I.P v)⁻¹) *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j)) i'
          = (X.B.I.P v *ᵥ (uMat (x v) *ᵥ ((X.B.I.P v)⁻¹ *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j)))) i' := by
            simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = (X.B.I.P v *ᵥ ((X.B.I.P v)⁻¹ *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j))) i' := by rw [hv]
        _ = X.B.I.φ v (tupH (frameOf X u') b i') := by
            rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hPu v), Matrix.one_mulVec]
    exact sub_eq_zero.1 (congrFun h0 i)

theorem stdConjEx_of_witt (h : WittBlock) : StdConjEx := stdConjEx_of stabInfV_holds h

end PI.AprimeInfW
end
end

