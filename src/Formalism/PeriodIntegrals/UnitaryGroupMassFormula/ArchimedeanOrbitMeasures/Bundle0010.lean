module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushLF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0009

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstSm
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem kPos_holds : KPos := by
  intro D X u' ψ hT μinf νinf fibInf hH
  have hg : 0 < Formalism.MainNotions.S.AutInst.gaugeU X.B.I := by
    unfold Formalism.MainNotions.S.AutInst.gaugeU
    exact Finset.prod_pos fun v _ => (hH.2.2.2.1 v).2
  have hv : 0 < Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k := by
    unfold Formalism.MainNotions.S.UnitaryVolumeMass.volU
    exact Finset.prod_pos fun i _ => by positivity
  have ht : 0 < Tw u' := by
    unfold Tw
    exact_mod_cast (D.mem u').A.T_prime.pos
  unfold KVal
  exact mul_pos (mul_pos hg (pow_pos hv _)) (zpow_pos ht _)

theorem orbMeas_holds : OrbMeas := fun X u' => measurable_orbM X u'

section Herm

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

def sigLin (σ : E →ₐ[F] E) : (R ⊗[F] E) →ₗ[R] (R ⊗[F] E) where
  toFun := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ
  map_add' := map_add _
  map_smul' r x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) :=
  IsModuleTopology.continuous_of_linearMap (sigLin R σ)

theorem isClosed_hermR [T2Space (R ⊗[F] E)] (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed ((HermR R σ n : AddSubgroup (Matrix (Fin n) (Fin n) (R ⊗[F] E))) :
      Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  have : ((HermR R σ n : AddSubgroup (Matrix (Fin n) (Fin n) (R ⊗[F] E))) :
      Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      ⋂ a, ⋂ b, {S : Matrix (Fin n) (Fin n) (R ⊗[F] E) | Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (S b a) = S a b} := by
    ext S; simp [HermR]
  rw [this]
  refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ ?_
  · exact (continuous_sigR R σ).comp ((continuous_apply a).comp (continuous_apply b))
  · exact (continuous_apply b).comp (continuous_apply a)

end Herm

theorem hermLF_holds : HermLF := by
  intro D X u' ψ hT μinf νinf fibInf hH
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : νinf.IsAddHaarMeasure := hH.2.2.2.2.2.1.1
  have : LocallyCompactSpace (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)))
  have : LocallyCompactSpace (HmI X) :=
    (isClosed_hermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨K, hK, hKc⟩ := exists_compact_mem_nhds (TI X u' hT)
  exact ⟨K, hKc, hK.measure_lt_top⟩

theorem continuous_gramI {D : D7} (X : HidaSetting D) :
    Continuous (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J :
      TupI X → Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hs := continuous_sigR (Ainf X.B.I.F) X.B.I.cm.sig
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [gramR, hR, Formalism.UG.hform]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((hs.comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul
    ((continuous_apply j).comp (continuous_apply b))

theorem gramMeas_holds : GramMeas := by
  intro D X S hS
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hS' : MeasurableSet[(borel (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))).comap Subtype.val] S := by
    rw [← borel_comap]; exact hS
  obtain ⟨A, hA, rfl⟩ := hS'
  rw [Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype, Set.preimage_inter]
  have hg : @Measurable (TupI X) (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) _ (borel _) (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := by
    let _ : MeasurableSpace (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) := borel _
    have : BorelSpace (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) := ⟨rfl⟩
    exact (continuous_gramI X).measurable
  have hC : MeasurableSet[borel (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))]
      ((HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) : AddSubgroup _) : Set _) :=
    MeasurableSet.of_compl (MeasurableSpace.measurableSet_generateFrom
      (isClosed_hermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)).isOpen_compl)
  exact (hg hA).inter (hg hC)

theorem constTest_of_polar (hP : PolarLoc) (hC : PushCont) : ConstTest :=
  constTest_of gramMeas_holds orbMeas_holds kPos_holds hP hC hermLF_holds

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbMSectMul
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem mem_H_iff (h : GI X) :
    h ∈ Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') ↔
      h • ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u')) = ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u')) :=
  MulAction.mem_stabilizer_iff

theorem orbM_sect_mul (y : TupI X) (hy : ∃ g : GI X, orbM X u' g = y)
    (h : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) :
    orbM X u' (sect X u' y * (h : GI X)) = y := by
  have e1 := sect_spec X u' y hy
  unfold orbM at e1 ⊢
  rw [mul_smul, (mem_H_iff X u' h).1 h.2, e1]

theorem sect_smul (g : GI X) (y : TupI X) (hy : ∃ t : GI X, orbM X u' t = y) :
    ∃ h0 : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u'),
      sect X u' (g • y) = g * sect X u' y * (h0 : GI X) := by
  set Y := ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u')) with hY
  have e1 : sect X u' y • Y = y := sect_spec X u' y hy
  obtain ⟨t, ht⟩ := hy
  have e2 : sect X u' (g • y) • Y = g • y :=
    sect_spec X u' _ ⟨g * t, by rw [← ht]; exact mul_smul g t Y⟩
  set a := sect X u' y with ha
  set b := sect X u' (g • y) with hb
  refine ⟨⟨(g * a)⁻¹ * b, ?_⟩, ?_⟩
  · rw [mem_H_iff, mul_smul, e2]
    rw [← e1, show g • a • Y = (g * a) • Y from (mul_smul g a Y).symm, inv_smul_smul]
  · simp only [mul_inv_cancel_left]

theorem muH_preimage (μ : Measure (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')))
    [μ.IsMulLeftInvariant] (hne : μ ≠ 0)
    (h0 : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u'))
    (S : Set (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u'))) (hS : MeasurableSet S) :
    μ ((fun h => h0 * h) ⁻¹' S) = μ S := by
  have hm : μ.map (fun h => h0 * h) = μ := map_mul_left_eq_self μ h0
  haveI : IsModuleTopology (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :=
    IsModuleTopology.isTopologicalRing (Ainf X.B.I.F) _
  haveI : IsTopologicalGroup (GI X) := by
    have h {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
        (S : Subgroup G) : IsTopologicalGroup S := inferInstance
    exact h (HR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
  haveI : BorelSpace (GI X) := ⟨rfl⟩
  haveI : BorelSpace (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) := inferInstance
  have ha : AEMeasurable (fun h => h0 * h) μ :=
    (measurable_const_mul h0).aemeasurable
  rw [← Measure.map_apply_of_aemeasurable ha hS, hm]

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushSupp
section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem hR_eq (x y : Fin M → R ⊗[F] E) :
    hR R σ J x y = ((fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (x i)) ⬝ᵥ (JR R J *ᵥ y)) := by
  simp only [hR, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sigR_mulVec (G : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (x : Fin M → R ⊗[F] E) :
    (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ ((G *ᵥ x) i)) = (G.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ)) *ᵥ (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (x i)) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem hR_smul (g : HA R σ J) (x y : Fin M → R ⊗[F] E) :
    hR R σ J ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
      ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y) = hR R σ J x y := by
  have hg : ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ))ᵀ * JR R J *
      (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := g.2
  rw [hR_eq, hR_eq, sigR_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hg]

theorem gramR_smul {m : ℕ} (g : HA R σ J) (Y : Fin m → Fin M → R ⊗[F] E) :
    gramR R σ J (g • Y) = gramR R σ J Y := by
  funext a b
  exact hR_smul R σ J g (Y a) (Y b)

theorem gramR_ratTup {m : ℕ} (Y : Fin m → Fin M → E) :
    gramR R σ J (ratTup R Y) = (gramE σ J Y).map (inclR R) := by
  funext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp [gramR, gramE, hR, hE, Formalism.UG.hform, ratTup, JR, inclR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, map_sum, map_mul]

def hLin (x : Fin M → R ⊗[F] E) : (Fin M → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun := hR R σ J x
  map_add' y z := by
    simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem linIndep_of_isUnit_det {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (h : IsUnit (gramR R σ J X).det) :
    LinearIndependent (R ⊗[F] E) X := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : (gramR R σ J X).mulVec g = 0 := by
    funext a
    have e := map_sum (hLin R σ J (X a)) (fun b => g b • X b) Finset.univ
    rw [hg, map_zero] at e
    simp only [map_smul, smul_eq_mul] at e
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [e]
    exact Finset.sum_congr rfl fun b _ => by simp only [hLin, LinearMap.coe_mk, gramR]; exact mul_comm _ _
  have h2 : g = 0 := by
    have := congrArg (fun v => (gramR R σ J X)⁻¹.mulVec v) h1
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  intro a; rw [h2]; rfl

theorem continuous_sigRP [FiniteDimensional F E] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) := by
  have h : ∀ x : R ⊗[F] E, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ x = (σ.toLinearMap.baseChange R) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ : R ⊗[F] E → R ⊗[F] E) = (σ.toLinearMap.baseChange R) := funext h
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _

theorem continuous_gramRP [FiniteDimensional F E] [TopologicalSpace R] [IsTopologicalRing R] {m : ℕ} :
    Continuous (gramR R σ J : (Fin m → Fin M → R ⊗[F] E) → Matrix (Fin m) (Fin m) (R ⊗[F] E)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  show Continuous fun Y : Fin m → Fin M → R ⊗[F] E => ∑ i, ∑ j, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (Y a i) * JR R J i j * Y b j
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (((continuous_sigRP R σ).comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul
      ((continuous_apply j).comp (continuous_apply b))

end Alg

def DetNZ : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0

theorem orbM_mem {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (hd : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :
    orbM X u' g ∈ FbI X u' hT := by
  have e : gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (orbM X u' g) =
      ((TI X u' hT : HermR _ _ _) : Matrix _ _ _) := by
    rw [orbM, gramR_smul, gramR_ratTup]
    rfl
  refine ⟨e, ?_⟩
  apply linIndep_of_isUnit_det (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  rw [e]
  have e2 := RingHom.map_det (inclR (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F))
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')))
  rw [RingHom.mapMatrix_apply] at e2
  show IsUnit ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Ainf X.B.I.F))).det
  rw [← e2]
  exact (isUnit_iff_ne_zero.2 hd).map _

theorem measurableSet_FbI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) : MeasurableSet (FbI X u' hT) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  exact (isClosed_singleton.preimage (continuous_gramRP (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)).measurableSet.inter
    (isOpen_IndI X).measurableSet

theorem pushSupp_of (hD : DetNZ) : ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    X.measG.μGinf.map (orbM X u') (FbI X u' hT)ᶜ = 0 := by
  intro D X u' ψ hT μinf νinf fibInf hP
  rw [Measure.map_apply (measurable_orbM X u') (measurableSet_FbI X u' hT).compl]
  have : orbM X u' ⁻¹' (FbI X u' hT)ᶜ = ∅ := by
    ext g
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
    exact orbM_mem X u' hT (hD X u' ψ hT μinf νinf fibInf hP) g
  rw [this, measure_empty]

def PushLFin : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    LFI X (X.measG.μGinf.map (orbM X u'))

theorem lfPush_of (hD : DetNZ) (hL : PushLFin) : LFPush := by
  intro D X u' ψ hT μinf νinf fibInf hP
  exact ⟨pushSupp_of hD X u' ψ hT μinf νinf fibInf hP, hL X u' ψ hT μinf νinf fibInf hP⟩

end PI.AprimeInfW
end
end

