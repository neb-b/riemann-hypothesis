module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpInj
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpHaarW
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

def UstdSub {n : ℕ} (ε : Fin n → Bool) (S : Finset (Fin n)) : Subgroup (Formalism.REAL.UJ ε) where
  carrier := {g | InStd S g}
  one_mem' := by
    intro i _ j
    show (1 : Matrix (Fin n) (Fin n) ℂ) j i = _
    rw [Matrix.one_apply]
  mul_mem' := by
    intro g h hg hh i hi j
    have e : (((g * h : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
          ((h : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := rfl
    show (((g * h : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) j i = _
    rw [e, Matrix.mul_apply]
    simp_rw [hh i hi]
    simp [hg i hi j]
  inv_mem' := by
    intro g hg i hi j
    have e : ((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ))⁻¹ := rfl
    have h1 : (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
        ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 := Units.inv_mul _
    have h2 := congrFun (congrFun h1 j) i
    rw [Matrix.mul_apply] at h2
    simp_rw [hg i hi] at h2
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.one_apply] at h2
    show ((((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) j i = _
    rw [e, h2]

def BlockHaarV : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (S : Finset (Fin n)) (k : ℕ), S.card = k →
    (∀ i ∈ S, ε i = true) → Formalism.MainNotions.S.Gauge.GaugeDens ε →
    ∃ (β : Type) (_ : Fintype β) (L₁ : EuclideanSpace ℝ β →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
      (P₁ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ β) (ν : Measure (UstdSub ε S)) (r : ℝ)
      (e : EuclideanSpace ℝ β → ℝ) (hmem : ∀ y, expU ε (L₁ y) ∈ UstdSub ε S),
      (∀ z, P₁ (L₁ z) = z) ∧ (∀ M, InBlock ε S M → L₁ (P₁ M) = M) ∧ (∀ z, InBlock ε S (L₁ z)) ∧
      (∀ z, frob (L₁ z) = ‖z‖ ^ 2) ∧
      ν.IsMulLeftInvariant ∧ IsFiniteMeasure ν ∧ ν Set.univ ≠ 0 ∧ 0 < r ∧ Measurable e ∧ (∀ z, 0 ≤ e z) ∧
      ContinuousAt e 0 ∧ 0 < e 0 ∧ (ν Set.univ).toReal / e 0 = Formalism.MainNotions.S.UnitaryVolumeMass.volU k ∧
      Continuous (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) ∧
      Set.InjOn (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) (ball 0 r) ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ β) r, MeasurableSet A →
        ν ((fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) '' A) = ∫⁻ y in A, ENNReal.ofReal (e y)

theorem grpHaarH_of (hBH : BlockHaarV) : GrpHaarH := by
  intro D X u' hb c S ι η _ _ L L₁ ctx hS
  obtain ⟨⟨ψ', hT, μinf, νinf, fibInf, hP⟩, hc, hL, hB⟩ := ctx
  have hgd : ∀ v, Formalism.MainNotions.S.Gauge.GaugeDens (X.B.I.ε v) := hP.2.2.2.1
  choose β hβ L1 P1 ν r e hmem h1 h2 h3 h4 hνL hνF hν0 hr hem hen hec he0 hrat hcont hinj hdens using
    fun v => hBH X.B.I.n (X.B.I.ε v) (S v) D.R.k (hc.1 v).1 (hc.1 v).2 (hgd v)
  letI : ∀ v, Fintype (β v) := hβ
  have hUJ : ∀ v, SecondCountableTopology (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => Formalism.REAL.instSecondCountableUJ _ _
  have : ∀ v, SecondCountableTopology (UstdSub (X.B.I.ε v) (S v)) := fun v =>
    TopologicalSpace.Subtype.secondCountableTopology ((UstdSub (X.B.I.ε v) (S v) : Set (Formalism.REAL.UJ (X.B.I.ε v))))
  have : ∀ v, OpensMeasurableSpace (UstdSub (X.B.I.ε v) (S v)) := fun v => inferInstance
  have : OpensMeasurableSpace (∀ v, UstdSub (X.B.I.ε v) (S v)) := Pi.opensMeasurableSpace
  have : ∀ v, IsFiniteMeasure (ν v) := hνF
  have : ∀ v, (ν v).IsMulLeftInvariant := hνL
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have : SecondCountableTopology (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  obtain ⟨hTyb, hTyn⟩ := coord_facts L₁ (fun v M => InBlock (X.B.I.ε v) (S v) M) L1 P1 h1 h2 h3 h4
    (fun y v => hB.1 y v) (fun y => hB.2.1 y) (fun M hM => hB.2.2 M hM)
  set Ty : EuclideanSpace ℝ η →ₗ[ℝ] (∀ v, EuclideanSpace ℝ (β v)) :=
    LinearMap.pi fun v => (P1 v).comp ((LinearMap.proj v).comp L₁) with hTyd
  have hTym := PI.AprimeInfG.measurePreserving_of_normSq Ty hTyb hTyn
  let Tye : EuclideanSpace ℝ η ≃ᵐ (∀ v, EuclideanSpace ℝ (β v)) :=
    (LinearEquiv.ofBijective Ty hTyb).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hTye : MeasurePreserving Tye volume (Measure.pi fun _ => volume) := hTym
  have hTyv : ∀ y v, L1 v (Ty y v) = L₁ y v := fun y v => h2 v _ (hB.1 y v)

  let ψf : (∀ v, UstdSub (X.B.I.ε v) (S v)) →
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') :=
    fun g => ⟨X.toInf hb (c * (fun v => ((g v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) * c⁻¹),
      (hc.2 _).2 fun v => (g v).2⟩
  let ψm : (∀ v, UstdSub (X.B.I.ε v) (S v)) →ₙ*
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') :=
    { toFun := ψf
      map_mul' := fun g h => by
        apply Subtype.ext
        show toInfHom X hb _ = toInfHom X hb _ * toInfHom X hb _
        rw [← map_mul]
        congr 1
        have : (fun v => (((g * h) v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) =
            (fun v => ((g v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) *
              (fun v => ((h v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) := funext fun v => rfl
        rw [this]
        group }
  have hψc : Continuous ψm := by
    apply Continuous.subtype_mk
    exact (MassDataMassesW.continuous_toInf X hb).comp ((continuous_const.mul (continuous_pi fun v =>
      continuous_subtype_val.comp (continuous_apply v))).mul continuous_const)
  have hψi : Function.Injective ψm := by
    intro g h he
    have e1 := toInf_injective X hb (congrArg Subtype.val he)
    have e2 : (fun v => ((g v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) =
        (fun v => ((h v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) := by simpa using e1
    funext v
    exact Subtype.ext (congrFun e2 v)
  have hψs : Function.Surjective ψm := by
    intro hh
    obtain ⟨s, hs⟩ := PI.AprimeInfU.toInf_surjective X hb MassDataMassesW.splitIso_holds
      (hh : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    have hmemS : X.toInf hb (c * (c⁻¹ * s * c) * c⁻¹) ∈
        MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') := by
      rw [show c * (c⁻¹ * s * c) * c⁻¹ = s by group, hs]
      exact hh.2
    have hstd := (hc.2 _).1 hmemS
    refine ⟨fun v => ⟨(c⁻¹ * s * c) v, hstd v⟩, Subtype.ext ?_⟩
    show X.toInf hb (c * (c⁻¹ * s * c) * c⁻¹) = hh
    rw [show c * (c⁻¹ * s * c) * c⁻¹ = s by group, hs]

  let Φ : ∀ v, EuclideanSpace ℝ (β v) → UstdSub (X.B.I.ε v) (S v) :=
    fun v z => ⟨expU (X.B.I.ε v) (L1 v z), hmem v z⟩
  have hχ : ∀ y, (⟨chiOf X hb c L₁ y, hS y⟩ :
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u')) =
      ψm (fun v => Φ v (Ty y v)) := by
    intro y
    apply Subtype.ext
    show chiOf X hb c L₁ y = X.toInf hb (c * (fun v => expU (X.B.I.ε v) (L1 v (Ty y v))) * c⁻¹)
    unfold chiOf
    simp_rw [hTyv]
  set rr := (insert 1 (Finset.univ.image r)).min' ⟨1, Finset.mem_insert_self _ _⟩ with hrr
  have hrr0 : 0 < rr := by
    have hm := Finset.min'_mem (insert 1 (Finset.univ.image r)) ⟨1, Finset.mem_insert_self _ _⟩
    rcases Finset.mem_insert.1 hm with e' | e'
    · rw [hrr, e']; norm_num
    · obtain ⟨v, -, hv⟩ := Finset.mem_image.1 e'
      rw [hrr, ← hv]; exact hr v
  have hrrv : ∀ v, rr ≤ r v := fun v =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem r (Finset.mem_univ v)))
  have hTyle : ∀ y v, ‖Ty y v‖ ≤ ‖y‖ := by
    intro y v
    have : ‖Ty y v‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [← hTyn y]
      exact Finset.single_le_sum (f := fun v => ‖Ty y v‖ ^ 2) (fun v _ => sq_nonneg _) (Finset.mem_univ v)
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  have hT0 : ∀ v, Ty 0 v = 0 := fun v => by simp
  have hνu : (Measure.pi ν).map ψm Set.univ = ∏ v, ν v Set.univ := by
    rw [Measure.map_apply hψc.measurable MeasurableSet.univ, Set.preimage_univ, Measure.pi_univ]
  refine ⟨(Measure.pi ν).map ψm, rr, fun y => ∏ v, e v (Ty y v),
    isMulLeftInvariant_map ψm hψc.measurable hψs, inferInstance, ?_, ?_, hrr0, ?_, ?_, ?_, ?_⟩
  · rw [hνu]
    exact Finset.prod_ne_zero_iff.2 fun v _ => hν0 v
  · rw [hνu]
    exact ENNReal.prod_ne_top fun v _ => measure_ne_top _ _
  · refine tendsto_finsetProd _ fun v _ => ?_
    have hv : ContinuousAt (fun y : EuclideanSpace ℝ η => Ty y v) 0 :=
      ((continuous_apply v).comp Ty.continuous_of_finiteDimensional).continuousAt
    have hd : ContinuousAt (e v) (Ty 0 v) := by rw [hT0 v]; exact hec v
    have hdv := ContinuousAt.comp (f := fun y : EuclideanSpace ℝ η => Ty y v) hd hv
    exact hdv
  · simp only [hT0]
    exact Finset.prod_pos fun v _ => he0 v
  · rw [hνu, ENNReal.toReal_prod]
    simp only [hT0]
    rw [← Finset.prod_div_distrib]
    simp only [hrat, Finset.prod_const, Finset.card_univ]
  · intro s hs hsr
    have hB' : Ty '' ball 0 s ⊆ Set.univ.pi fun v => ball 0 (r v) := by
      rintro _ ⟨y, hy, rfl⟩ v -
      exact mem_ball_zero_iff.2 (((hTyle y v).trans_lt (mem_ball_zero_iff.1 hy)).trans_le (hsr.trans (hrrv v)))
    have hΦc : Continuous (fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) :=
      continuous_pi fun v => (hcont v).comp (continuous_apply v)
    have hΦi : Set.InjOn (fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v))
        (Set.univ.pi fun v => ball 0 (r v)) := by
      intro z hz z' hz' he'
      funext v
      exact hinj v (hz v (Set.mem_univ v)) (hz' v (Set.mem_univ v)) (congr_fun he' v)
    have hTA : MeasurableSet (Tye '' ball 0 s) := Tye.measurableSet_image.2 measurableSet_ball
    have hAi : MeasurableSet ((fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) '' (Tye '' ball 0 s)) :=
      hTA.image_of_continuousOn_injOn hΦc.continuousOn (hΦi.mono hB')
    have himg : (fun y => (⟨chiOf X hb c L₁ y, hS y⟩ :
        MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))) '' ball 0 s =
        ψm '' ((fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) '' (Tye '' ball 0 s)) := by
      rw [Set.image_image, Set.image_image]
      exact Set.image_congr fun y _ => hχ y
    have hmeasH : MeasurableSet (ψm '' ((fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) ''
        (Tye '' ball 0 s))) := by
      have e3 : ψm '' ((fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) '' (Tye '' ball 0 s)) =
          (fun y => ψm (fun v => Φ v (Ty y v))) '' ball 0 s := by
        rw [Set.image_image, Set.image_image]
        rfl
      rw [e3]
      refine measurableSet_ball.image_of_continuousOn_injOn ?_ ?_
      · exact (hψc.comp (hΦc.comp Ty.continuous_of_finiteDimensional)).continuousOn
      · intro y hy y' hy' he'
        have e4 := hψi he'
        have e5 : Ty y = Ty y' := hΦi (hB' ⟨y, hy, rfl⟩) (hB' ⟨y', hy', rfl⟩) e4
        exact hTyb.1 e5
    rw [himg, Measure.map_apply hψc.measurable hmeasH, hψi.preimage_image,
      PI.AprimeInfG.pi_chart_dens ν (fun _ => volume) Φ (fun v => (hcont v).measurable) (fun v => ball 0 (r v))
        (fun v => measurableSet_ball) hinj e hem hdens (Tye '' ball 0 s) hB' hTA hAi,
      ← hTye.setLIntegral_comp_emb Tye.measurableEmbedding]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_prod_of_nonneg fun v _ => hen v _]
    rfl

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MatNDHHolds
section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

theorem no_kernel {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (μ : Measure W) (χ : W → W → ℂ) (hμ : SelfDual μ χ)
    (hadd : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hT : ST.TestExP μ χ) (t : W) (ht0 : t ≠ 0)
    (ht : ∀ y, χ t y = 1) : False := by
  haveI := hμ.1
  obtain ⟨Φ, hc, hs, hI, z, hz⟩ := hT

  have htr : ∀ y, ∫ x, Φ (x - t) * χ x y ∂μ = ∫ x, Φ x * χ x y ∂μ := by
    intro y
    have := integral_sub_right_eq_self (μ := μ) (fun x => Φ x * χ (x + t) y) t
    simp only [sub_add_cancel] at this
    rw [this]
    congr 1; funext x
    rw [hadd, ht, mul_one]
  have hc' : Continuous fun x => Φ (x - t) := hc.comp (continuous_id.sub continuous_const)
  have hs' : HasCompactSupport fun x => Φ (x - t) := hs.comp_homeomorph (Homeomorph.subRight t)
  have hper : ∀ w, Φ (w - t) = Φ w := by
    intro w
    have h1 := hμ.2 (fun x => Φ (x - t)) hc' hs' (by simp only [htr]; exact hI) (-w)
    have h2 := hμ.2 Φ hc hs hI (-w)
    simp only [htr, neg_neg] at h1 h2
    rw [← h1, h2]
  have hpern : ∀ n : ℕ, ∀ w, Φ (w - n • t) = Φ w := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih => intro w; rw [succ_nsmul, ← sub_sub, hper, ih]
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  apply hz
  have htpos : 0 < ‖t‖ := norm_pos_iff.2 ht0
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖-z‖) / ‖t‖)
  rw [← hpern n (-z)]
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hb := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at hb
  have h1 : ‖(n : ℝ) • t‖ ≤ ‖-z - n • t‖ + ‖-z‖ := by
    have := norm_sub_le (-z) (-z - n • t)
    simp only [sub_sub_cancel] at this
    rw [← Nat.cast_smul_eq_nsmul ℝ] at this ⊢
    linarith [norm_sub_rev (-z) (-z - (n : ℝ) • t)]
  rw [norm_smul, Real.norm_natCast] at h1
  have h2 : (R + ‖-z‖) < n * ‖t‖ := by rwa [div_lt_iff₀ htpos] at hn
  linarith


open Classical in
def MatNDH : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    (matI X).det ≠ 0

theorem matNDH_holds : MatNDH := by
  classical
  intro D X u' ψ hT μinf νinf fibInf hP hdet0
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hS := hP.2.2.1
  have hpc := continuous_psiInfP ψ hS
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
  let t : EuclideanSpace ℝ (KapI X) := (EuclideanSpace.equiv (KapI X) ℝ).symm v
  have ht0 : t ≠ 0 := by
    intro h
    apply hv0
    have := congrArg (EuclideanSpace.equiv (KapI X) ℝ) h
    simpa [t] using this
  have hAt : Alin X t = 0 := by
    simp [Alin, t, Matrix.toLin'_apply]
    exact hv
  have hβ : ∀ y, betaI X t y = 0 := by
    intro y
    rw [betaSym_holds, ← inner_Alin, hAt, inner_zero_right]
  have hμ : SelfDual μinf (fun x y : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y)) :=
    hP.2.2.2.2.1
  have hμ' := selfDual_transport μinf _ (tupCoord X) (tupCoord_add X) hμ
  haveI := hμ'.1
  have hadd : ∀ x x' y : EuclideanSpace ℝ (KapI X), (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y))) (x + x') y = (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y))) x y * (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y))) x' y := by
    intro x x' y
    simp only [tupCoord_symm_add, BR_add_leftP, psiInf_addP]
  have hB : ST.IsBichar (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm x) ((tupCoord X).symm y))) :=
    { addL := hadd
      addR := fun x y y' => by simp only [tupCoord_symm_add, BR_add_rightP, psiInf_addP]
      norm1 := fun x y => norm_psiInfP ψ hS _
      contL := fun y => hpc.comp ((continuous_BR_leftP X _).comp (tupCoord X).symm.continuous)
      contR := fun x => hpc.comp ((continuous_BR_rightP X _).comp (tupCoord X).symm.continuous) }
  have hTest := ST.testEx_bichar (μinf.map (tupCoord X)) hB
  refine no_kernel (μinf.map (tupCoord X)) _ hμ' hadd hTest t ht0 fun y => ?_
  rw [psiInf_eq ψ hS]
  beta_reduce
  have : (∑ w : InfinitePlace X.B.I.F, (InfinitePlace.Completion.extensionEmbedding w
      (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ((tupCoord X).symm t) ((tupCoord X).symm y) w)).re) = 0 := hβ y
  simp only [this]
  simp

open Classical in
theorem densMu_holds : DensMu := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hdet : IsUnit (LinearMap.det (Alin X)) := by
    rw [det_Alin]; exact isUnit_iff_ne_zero.2 (matNDH_holds X u' ψ hT μinf νinf fibInf hP)
  let A : EuclideanSpace ℝ (KapI X) ≃L[ℝ] EuclideanSpace ℝ (KapI X) := (LinearMap.equivOfIsUnitDet hdet).toContinuousLinearEquiv
  have hAapp : ∀ y, A y = Alin X y := fun y => by simp [A, LinearMap.equivOfIsUnitDet_apply]
  have hAl : (A : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) = Alin X := LinearMap.ext hAapp
  have hAd : LinearMap.det (A : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) = (matI X).det := by
    rw [hAl, det_Alin]
  have hsym : ∀ x y, ⟪x, A y⟫ = ⟪A x, y⟫ := by
    intro x y
    rw [hAapp, hAapp, inner_Alin, real_inner_comm, inner_Alin, betaSym_holds]
  have hν := FSD.selfDual_lin A hsym
  rw [hAd] at hν

  have hμ : SelfDual μinf (fun x y : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y)) :=
    hP.2.2.2.2.1
  have hμ' := selfDual_transport μinf _ (tupCoord X) (tupCoord_add X) hμ
  have hχ : (fun x y : EuclideanSpace ℝ (KapI X) => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
      ((tupCoord X).symm x) ((tupCoord X).symm y))) = fun x y => ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) := by
    funext x y
    rw [hAapp, inner_Alin, psiInf_eq ψ hP.2.2.1, Real.fourierChar_apply]
    simp only [betaI]
    push_cast
    ring_nf
  rw [hχ] at hμ'
  haveI := hν.1
  have hB : ST.IsBichar (fun x y : EuclideanSpace ℝ (KapI X) => ((𝐞 ⟪x, A y⟫ : Circle) : ℂ)) :=
    { addL := fun x x' y => by simp only [inner_add_left, AddChar.map_add_eq_mul, Circle.coe_mul]
      addR := fun x y y' => by simp only [map_add (f := _), inner_add_right, AddChar.map_add_eq_mul, Circle.coe_mul]
      norm1 := fun x y => Circle.norm_coe _
      contL := fun y => (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        (continuous_id.inner continuous_const)
      contR := fun x => (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        (continuous_const.inner A.continuous) }
  obtain ⟨Φ, hc, hs, hI, z, hz⟩ := ST.testEx_bichar (ENNReal.ofReal (Real.sqrt |(matI X).det|) • (volume : Measure (EuclideanSpace ℝ (KapI X)))) hB
  exact SelfDual.eq_of_test hν hμ' Φ hc hs hI z hz

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PerpPosV
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.PoincareInHH.Cut
open scoped InnerProductSpace ComplexConjugate
open Matrix Finset

namespace PI.AprimeInfW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem wV_idx {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (v : InfinitePlace X.B.I.F)
    (b : Fin (D.R.rS + 1 + D.R.rS)) : wV X u' v b = rv X.B.I v (X.crd (wF X u' b)) := by
  unfold wV rv
  rw [tupH_eq]

theorem perpPosV : PerpPosV := by
  intro D X u' ψ hT μinf νinf fibInf hP v z hz hzo
  by_contra hle
  push_neg at hle
  have hzo' : ∀ b, hJ (X.B.I.ε v) (wV X u' v b) z = 0 := hzo
  have he : ∀ a : Fin D.R.rS, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) z = 0 := by
    intro a
    have := hzo' (Fin.castAdd D.R.rS (Fin.castSucc a))
    rwa [wV_idx, wF, Fin.append_left, Fin.snoc_castSucc] at this
  have hf : ∀ a : Fin D.R.rS, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) z = 0 := by
    intro a
    have := hzo' (Fin.natAdd (D.R.rS + 1) a)
    rwa [wV_idx, wF, Fin.append_right] at this
  have hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u')) z = 0 := by
    have := hzo' (Fin.castAdd D.R.rS (Fin.last D.R.rS))
    rwa [wV_idx, wF, Fin.append_left, Fin.snoc_last] at this
  let nv : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ := fun j =>
    if h : j.1 < D.R.rS then rv X.B.I v (X.eR ⟨j.1, h⟩) - rv X.B.I v (X.fR ⟨j.1, h⟩) else rv X.B.I v (X.zR u')
  have hb := card_le_of_orth' (X.B.I.ε v) (D.R.rS + 1) nv z ?_ ?_ ?_ hle hz
  · rw [card_eps_false X v] at hb
    omega
  · intro j k hjk
    simp only [nv]
    split_ifs with hj hk hk
    · rw [hJ_sub_left, hJ_sub_right, hJ_sub_right]
      simp only [HidaSetting.eR, HidaSetting.fR, hJ_crd, X.ee, X.ff, X.ef, hT_f_e]
      have hne : (⟨k.1, hk⟩ : Fin D.R.rS) ≠ ⟨j.1, hj⟩ := fun h => hjk (Fin.ext (by simpa using (congrArg Fin.val h).symm))
      have hne' : (⟨j.1, hj⟩ : Fin D.R.rS) ≠ ⟨k.1, hk⟩ := fun h => hne h.symm
      simp [hne, hne']
    · rw [hJ_sub_left]
      simp only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, hJ_crd, (X.zu_orth u' _).1, (X.zu_orth u' _).2]
      simp
    · rw [hJ_sub_right]
      have h1 := hJ_crd X v (X.zu u') (X.eX ⟨k.1, hk⟩)
      have h2 := hJ_crd X v (X.zu u') (X.fY ⟨k.1, hk⟩)
      have e1 : (VS D).hT (X.zu u') (X.eX ⟨k.1, hk⟩) = 0 := by
        rw [← (VS D).herm.eq, (X.zu_orth u' _).1]; simp
      have e2 : (VS D).hT (X.zu u') (X.fY ⟨k.1, hk⟩) = 0 := by
        rw [← (VS D).herm.eq, (X.zu_orth u' _).2]; simp
      simp only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, h1, h2, e1, e2, map_zero, sub_zero]
    · exfalso; apply hjk; ext; omega
  · intro j
    simp only [nv]
    split_ifs with hj
    · rw [hJ_sub_left, hJ_sub_right, hJ_sub_right]
      simp only [HidaSetting.eR, HidaSetting.fR, hJ_crd, X.ee, X.ff, X.ef, hT_f_e, if_true, map_zero, map_one]
      norm_num
    · simp only [HidaSetting.zR, hJ_crd, X.zu_norm, map_neg, map_natCast]
      simp only [Complex.neg_re, Complex.natCast_re, Left.neg_neg_iff]
      exact_mod_cast (D.mem u').A.T_prime.pos
  · intro j
    simp only [nv]
    split_ifs with hj
    · rw [hJ_sub_left, he, hf, sub_zero]
    · exact hzz

end PI.AprimeInfW
end
end

