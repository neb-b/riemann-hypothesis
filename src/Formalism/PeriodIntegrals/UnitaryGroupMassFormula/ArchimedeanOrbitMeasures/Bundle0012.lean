module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.EqZeroOfSetIntegral
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ConstY
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem frame_independent_at_infinity : FrameIndependentAtInfinity := by
  intro D X u' ψ hT μinf νinf fibInf hH
  have h := (orbM_mem X u' hT (detNZ_holds X u' ψ hT μinf νinf fibInf hH) 1).2
  have h2 : orbM X u' 1 = Y0 X u' := one_smul _ _
  rwa [h2] at h

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibInv
section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

def SdInvG : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, μinf.map (fun y => g • y) = μinf

section Herm

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

theorem isClosed_HermRP (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  have : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      ⋂ a, ⋂ b, {S | Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (S b a) = S a b} := by
    ext S; simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]; exact Iff.rfl
  rw [this]
  exact isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_eq ((continuous_sigRP R σ).comp ((continuous_apply a).comp (continuous_apply b)))
      ((continuous_apply b).comp (continuous_apply a))

end Herm

section Gram

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_invP (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul r e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem gramR_memP (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (X : Fin n → Fin M → R ⊗[F] E) : gramR R σ J X ∈ HermR R σ n := by
  intro a b
  have hJR : ∀ i j, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (JR R J i j) = JR R J j i := by
    intro i j; simp [JR, inclR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hJ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramR, hR, Formalism.UG.hform, map_sum, map_mul, sigR_invP R σ hσ, hJR]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Gram

theorem sig_invI {D : D7} (X : HidaSetting D) (x : X.B.I.E) : X.B.I.cm.sig (X.B.I.cm.sig x) = x :=
  star_star x

theorem J_hermI {D : D7} (X : HidaSetting D) (i j : Fin X.B.I.n) : X.B.I.cm.sig (X.B.I.J j i) = X.B.I.J i j :=
  congrFun (congrFun X.B.I.J_herm i) j

def gramHI {D : D7} (X : HidaSetting D) (y : TupI X) : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) :=
  ⟨gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y,
    gramR_memP (Ainf X.B.I.F) X.B.I.cm.sig (sig_invI X) X.B.I.J (J_hermI X) y⟩

theorem continuous_gramHI {D : D7} (X : HidaSetting D) : Continuous (gramHI X) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  exact (continuous_gramRP (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J).subtype_mk _

def smulH {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : TupI X ≃ₜ TupI X where
  toFun y := g • y
  invFun y := g⁻¹ • y
  left_inv y := inv_smul_smul g y
  right_inv y := smul_inv_smul g y
  continuous_toFun := continuous_smul_tupI X g
  continuous_invFun := continuous_smul_tupI X g⁻¹

theorem indI_smul {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (y : TupI X)
    (hy : y ∈ IndI X) : g • y ∈ IndI X := by
  have hinj : Function.Injective (Matrix.mulVecLin
      ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))) := by
    intro x x' h
    have h2 := congrArg (fun v => (((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g)⁻¹ : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) *ᵥ v) h
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using h2
  exact LinearIndependent.map' hy _ (LinearMap.ker_eq_bot.2 hinj)

theorem indI_smul_iff {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (y : TupI X) :
    g • y ∈ IndI X ↔ y ∈ IndI X :=
  ⟨fun h => by simpa using indI_smul X g⁻¹ _ h, indI_smul X g y⟩

theorem gramR_smulI {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (y : TupI X) :
    gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (g • y) = gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J y :=
  gramR_smul (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g y

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HaarUniqInfHolds
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem haarUniqInf_holds : HaarUniqInf := by
  intro D X u' ψ hT μinf νinf fibInf hP m hinv hfin
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : SecondCountableTopology (GI X) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  haveI : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  haveI : IsFiniteMeasureOnCompacts m := ⟨fun K hK => hfin K hK⟩
  haveI : m.IsMulLeftInvariant := ⟨fun g => hinv g⟩
  refine ⟨(Measure.haarScalarFactor m X.measG.μGinf : ENNReal), ENNReal.coe_ne_top, ?_⟩
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul m X.measG.μGinf]
  ext s hs
  simp [Measure.smul_apply]

def WittInf : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → FbI X u' hT ⊆ Set.range (orbM X u')

theorem regI_of (hW : WittInf) : RegI := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : SecondCountableTopology (GI X) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  haveI : BorelSpace (TupI X) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  have hc : Continuous (orbM X u') :=
    PI.AprimeInfT.continuous_orbit (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J _
  have hd := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  refine ⟨hc.measurable, fun g => ?_, fun g => (continuous_const_mul g).measurable, fun t =>
    ((continuous_const_mul t).comp continuous_subtype_val).measurable, fun C hC =>
    ⟨hC.isClosed.measurableSet, hC.image hc, (hC.image hc).isClosed.measurableSet⟩,
    hW X u' ψ hT μinf νinf fibInf hP, ?_⟩
  · have hmat : Continuous (fun _ : TupI X =>
        ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E))) := continuous_const
    have : Continuous (fun y : TupI X => g • y) := by
      show Continuous (fun y : TupI X => actTup (Ainf X.B.I.F) (HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g) y)
      unfold actTup
      exact continuous_pi fun i => hmat.matrix_mulVec ((continuous_apply i))
    exact this.measurable
  · rintro _ ⟨g, rfl⟩
    exact (orbM_mem X u' hT hd g).2

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SqChartCore
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

theorem sq_coord_pi {X : Type} [AddCommGroup X] [TopologicalSpace X] {k : ℕ}
    (e : X ≃ₜ (Fin k → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) (κ : Type) [Fintype κ] :
    ∃ (n : ℕ) (e' : (κ → X) ≃ₜ (Fin n → ℝ)), ∀ x y, e' (x + y) = e' x + e' y := by
  let e1 : (κ → X) ≃ₜ (κ → Fin k → ℝ) := Homeomorph.piCongrRight fun _ => e
  have h1 : ∀ x y, e1 (x + y) = e1 x + e1 y := by
    intro x y; funext i; exact he (x i) (y i)
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := κ → Fin k → ℝ)
    (F := Fin (Module.finrank ℝ (κ → Fin k → ℝ)) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e1.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e1 (x + y)) = L (e1 x) + L (e1 y)
  rw [h1, map_add (f := _)]

theorem sq_coord_Ainf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ (k : ℕ) (e : Ainf F ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  let e1 : Ainf F ≃ₜ (InfinitePlace F → ℝ) :=
    Homeomorph.piCongrRight fun v =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).toHomeomorph
  have h1 : ∀ x y, e1 (x + y) = e1 x + e1 y := by
    intro x y; funext v
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).map_add _ _
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := InfinitePlace F → ℝ)
    (F := Fin (Module.finrank ℝ (InfinitePlace F → ℝ)) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e1.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e1 (x + y)) = L (e1 x) + L (e1 y)
  rw [h1, map_add (f := _)]

theorem sq_coord_tens (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] :
    ∃ (k : ℕ) (e : Ainf F ⊗[F] E ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  classical
  let R := Ainf F
  let b := Module.Free.chooseBasis R (R ⊗[F] E)
  let eL : (R ⊗[F] E) ≃ₗ[R] (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) := b.equivFun
  let e0 : R ⊗[F] E ≃ₜ (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) :=
    { toEquiv := eL.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap eL.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap }
  obtain ⟨k0, eA, hA⟩ := sq_coord_Ainf F
  obtain ⟨k, e1, h1⟩ := sq_coord_pi eA hA (Module.Free.ChooseBasisIndex R (R ⊗[F] E))
  refine ⟨k, e0.trans e1, fun x y => ?_⟩
  show e1 (e0 (x + y)) = e1 (e0 x) + e1 (e0 y)
  rw [show e0 (x + y) = e0 x + e0 y from eL.map_add x y, h1]

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem sq_sig_inv (hσ : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sq_gramR_mat {m : ℕ} (Y : Matrix (Fin m) (Fin M) (R ⊗[F] E)) (K : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    (hK : K = JR R J) : gramR R σ J Y = Y.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) * K * Yᵀ := by
  subst hK
  ext b d
  simp only [gramR, hR, Formalism.UG.hform, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem sq_gramR_rmul {m : ℕ} (a : Matrix (Fin m) (Fin m) (R ⊗[F] E)) (Y : Matrix (Fin m) (Fin M) (R ⊗[F] E)) :
    gramR R σ J (fun b i => ∑ c, a c b * Y c i) = Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) a * gramR R σ J Y * a := by
  have hY : (fun b i => ∑ c, a c b * Y c i) = aᵀ * Y := by
    ext b i; simp [Matrix.mul_apply]
  rw [hY, sq_gramR_mat R σ J _ (JR R J) rfl, sq_gramR_mat R σ J Y (JR R J) rfl]
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_map,
    Matrix.mul_assoc]

end Gen

theorem sq_chart_core {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M m : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin m → Fin M → E) (hT : ∀ i j, σ (gramE σ J Y j i) = gramE σ J Y i j) (hdet : (gramE σ J Y).det ≠ 0)
    {N : ℕ} (e : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) :
    ∃ (Ω : Set (HermR (Ainf F) σ m)) (a : HermR (Ainf F) σ m → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)),
      Ω ∈ 𝓝 (hermOf (Ainf F) σ (gramE σ J Y) hT) ∧ a (hermOf (Ainf F) σ (gramE σ J Y) hT) = 1 ∧
      ContinuousAt a (hermOf (Ainf F) σ (gramE σ J Y) hT) ∧
      ∀ T ∈ Ω, gramR (Ainf F) σ J (fun b i => ∑ c, a T c b * ratTup (Ainf F) Y c i) = (T : Matrix _ _ _) := by
  classical
  set G := gramE σ J Y with hG
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hdet
  set Tm : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) := G.map (inclR (Ainf F)) with hTm
  set Ti : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) := G⁻¹.map (inclR (Ainf F)) with hTi
  have hTTi : Tm * Ti = 1 := by
    rw [hTm, hTi, ← Matrix.map_mul, Matrix.mul_nonsing_inv G hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hTiT : Ti * Tm = 1 := by
    rw [hTm, hTi, ← Matrix.map_mul, Matrix.nonsing_inv_mul G hu, Matrix.map_one _ (map_zero _) (map_one _)]
  set c : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) :=
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf F) σ) with hc
  have hsig := sq_sig_inv (Ainf F) σ hσ
  have hcc : ∀ P, c (c P) = P := by intro P; ext i j; simp [hc, Formalism.UG.cT, hsig]
  have hcadd : ∀ P Q, c (P + Q) = c P + c Q := by intro P Q; ext i j; simp [hc, Formalism.UG.cT]
  have hcsub : ∀ P Q, c (P - Q) = c P - c Q := by intro P Q; ext i j; simp [hc, Formalism.UG.cT]
  have hcmul : ∀ P Q, c (P * Q) = c Q * c P := fun P Q => Formalism.UG.cT_mul _ P Q
  have hc1 : c 1 = 1 := Formalism.UG.cT_one _
  have hcT : c Tm = Tm := by
    ext i j
    simp only [hc, Formalism.UG.cT, hTm, Matrix.transpose_apply, Matrix.map_apply]
    rw [← hT i j]
    simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR]
  have hcTi : c Ti * Tm = 1 := by
    calc c Ti * Tm = c Ti * c Tm := by rw [hcT]
      _ = c (Tm * Ti) := (hcmul Tm Ti).symm
      _ = 1 := by rw [hTTi, hc1]
  have hcont_c : Continuous c := by
    show Continuous fun P : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) => (P.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf F) σ))ᵀ
    exact (continuous_id.matrix_map (continuous_sigRP (Ainf F) σ)).matrix_transpose
  set Bq : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) →
      Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) := fun h k => c (Ti * h) * Tm * (Ti * k) with hBq
  set Lq : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) :=
    fun h => h - c h with hLq
  have hD : ∀ u, Bq Tm u + Bq u Tm + Lq u = u + u := by
    intro u
    simp only [hBq, hLq]
    rw [hTiT, hc1, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc Tm Ti u, hTTi, Matrix.one_mul, hcmul Ti u,
      Matrix.mul_assoc (c u) (c Ti) Tm, hcTi, Matrix.mul_one]
    abel
  obtain ⟨g, hgc, hg0, hgev⟩ := exists_local_solve e he Bq
    (by intro x x' y; simp only [hBq, Matrix.mul_add, hcadd, Matrix.add_mul])
    (by intro x y y'; simp only [hBq, Matrix.mul_add])
    (((hcont_c.comp (continuous_const.matrix_mul continuous_fst)).matrix_mul continuous_const).matrix_mul
      (continuous_const.matrix_mul continuous_snd))
    Lq (by intro x y; simp only [hLq, hcadd]; abel) (continuous_id.sub hcont_c) Tm hD
  have hy0 : Bq Tm Tm + Lq Tm = Tm := by
    simp only [hBq, hLq]
    rw [hTiT, hc1, Matrix.one_mul, Matrix.mul_one, hcT, sub_self, add_zero]
  rw [hy0] at hgc hg0 hgev
  refine ⟨Subtype.val ⁻¹' {y | Bq (g y) (g y) + Lq (g y) = y}, fun T => Ti * g T.val, ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.continuousAt.preimage_mem_nhds hgev
  · show Ti * g Tm = 1
    rw [hg0, hTiT]
  · exact (continuous_const.matrix_mul continuous_id).continuousAt.comp
      (ContinuousAt.comp_of_eq hgc continuous_subtype_val.continuousAt rfl)
  · intro T hT'
    have hT'' : Bq (g T.val) (g T.val) + Lq (g T.val) = T.val := hT'
    show gramR (Ainf F) σ J (fun b i => ∑ c, (Ti * g T.val) c b * ratTup (Ainf F) Y c i) = T.val
    rw [sq_gramR_rmul (Ainf F) σ J (Ti * g T.val) (ratTup (Ainf F) Y), gramR_ratTup]
    set h := g T.val
    have hP : c (Bq h h) = Bq h h := by
      simp only [hBq]
      rw [hcmul (c (Ti * h) * Tm) (Ti * h), hcmul (c (Ti * h)) Tm, hcc, hcT, Matrix.mul_assoc]
    have hTh : c T.val = T.val := by
      ext i j
      exact T.2 i j
    have hLL : c (Lq h) = -(Lq h) := by
      simp only [hLq]
      rw [hcsub, hcc]
      abel
    have h2 : Lq h + Lq h = 0 := by
      have e1 := congrArg c hT''
      rw [hcadd, hP, hLL, hTh] at e1
      have e2 := add_left_cancel (hT''.trans e1.symm)
      exact eq_neg_iff_add_eq_zero.mp e2
    have h0 : Lq h = 0 := by
      calc Lq h = ((1 / 2 : F) * 2) • Lq h := by norm_num
        _ = (1 / 2 : F) • (Lq h + Lq h) := by rw [mul_smul, two_smul]
        _ = 0 := by rw [h2, smul_zero]
    rw [h0, add_zero] at hT''
    exact hT''

theorem sqChart_holds : SqChart := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  haveI : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  obtain ⟨k, eK, hK⟩ := sq_coord_tens X.B.I.F X.B.I.E
  obtain ⟨k1, e1, h1⟩ := sq_coord_pi eK hK (Fin (D.R.rS + 1 + D.R.rS))
  obtain ⟨N, eM, hM⟩ := sq_coord_pi e1 h1 (Fin (D.R.rS + 1 + D.R.rS))
  obtain ⟨Ω, a, h1', h2', h3', h4'⟩ := sq_chart_core X.B.I.cm.sig hσ X.B.I.J (tupH (frameOf X u')) hT hdet eM hM
  exact ⟨Ω, a, h1', h2', h3', fun T hT' => h4' T hT'⟩

end PI.AprimeInfW
end
end

