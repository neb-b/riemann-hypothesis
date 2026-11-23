module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDualC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipCT
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem topFacts (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    IsTopologicalGroup (UA σ J) ∧ LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.t2Space
  have hcA : Continuous (cA (F := F) σ) := by
    exact IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul
      (hv.matrix_map hcA))) continuous_const
  exact ⟨inferInstance, hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology, inferInstance⟩

theorem mat_mul' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_inv_mul' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  show (g.1⁻¹ * g.1 : GL (Fin n) (AE F E)).1 = 1
  simp

theorem isClosed_line {d : ℕ} (x : Fin d → E) :
    IsClosed (Set.range fun a : AE F E => a • incV F x) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  by_cases hx : x = 0
  · subst hx
    have h0 : incV F (0 : Fin d → E) = 0 := by ext i; simp [incV]
    have : (Set.range fun a : AE F E => a • incV F (0 : Fin d → E)) = {0} := by
      ext v; simp [h0, eq_comm]
    rw [this]; exact isClosed_singleton
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    set c : AE F E := inclR (F := F) (AF F) (x i)⁻¹
    have hxc : inclR (F := F) (AF F) (x i) * c = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hi, map_one]
    have : (Set.range fun a : AE F E => a • incV F x) = {v | v = (v i * c) • incV F x} := by
      ext v
      simp only [Set.mem_range, Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, rfl⟩
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul, incV]
        rw [mul_assoc, hxc, mul_one]
      · intro h; exact ⟨_, h.symm⟩
    rw [this]
    exact isClosed_eq continuous_id (((continuous_apply i).mul continuous_const).smul continuous_const)


variable (σ) in
def unipSet {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Subgroup (UA σ W.J) where
  carrier := {u | mat u *ᵥ incV F H'.x = incV F H'.x ∧
    ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x}
  one_mem' := by
    refine ⟨by simp [mat], fun z => ⟨0, by simp [mat]⟩⟩
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨by rw [mat_mul', ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    obtain ⟨b, hb⟩ := hv2 z
    refine ⟨a + b, ?_⟩
    rw [mat_mul', ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, Matrix.mulVec_smul, hu1, ha, add_smul, add_assoc]
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    have h1 : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      conv_lhs => rw [← hu1]
      rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
    refine ⟨h1, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    refine ⟨-a, ?_⟩
    have h2 : mat u⁻¹ *ᵥ (mat u *ᵥ (incM F H'.ι *ᵥ z)) = incM F H'.ι *ᵥ z := by
      rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, h1] at h2
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq]; exact h2

theorem unip_eq {d d₁ : ℕ} (σ : E →ₐ[F] E) (W : Spc F E d) (H' : Plane E d d₁) : unip σ W H' = unipSet σ W H' :=
  le_antisymm ((Subgroup.closure_le _).2 fun _ h => h) fun _ h => Subgroup.subset_closure h

theorem isClosed_unip {d d₁ : ℕ} (σ : E →ₐ[F] E) (W : Spc F E d) (H' : Plane E d d₁) :
    IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  have hm : Continuous fun g : UA σ W.J => mat g := Units.continuous_val.comp continuous_subtype_val
  rw [unip_eq]
  have hS : ((unipSet σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) = {u | mat u *ᵥ incV F H'.x = incV F H'.x} ∩
      ⋂ z, {u : UA σ W.J | ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} := by
    ext u; simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]; rfl
  rw [hS]
  refine (isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const).inter (isClosed_iInter fun z => ?_)
  have : {u : UA σ W.J | ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} =
      (fun u : UA σ W.J => mat u *ᵥ (incM F H'.ι *ᵥ z) - incM F H'.ι *ᵥ z) ⁻¹' Set.range fun a : AE F E => a • incV F H'.x := by
    ext u; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range]
    exact exists_congr fun a => by rw [eq_sub_iff_add_eq', eq_comm]
  rw [this]
  exact (isClosed_line H'.x).preimage ((hm.matrix_mulVec continuous_const).sub continuous_const)

theorem countable_ratU {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun g : GL (Fin n) E => (g.1, g.inv)) fun g h hgh => Units.ext (congrArg Prod.fst hgh)
  have hr : Set.Countable (((Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range :
      Subgroup (GL (Fin n) (AE F E))) : Set (GL (Fin n) (AE F E))) := by
    rw [MonoidHom.coe_range]; exact Set.countable_range _
  haveI := hr.to_subtype
  exact Function.Injective.countable (f := fun g : ratU σ J => (⟨g.1.1, g.2⟩ : (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range))
    fun g h hgh => by
      apply Subtype.ext; apply Subtype.ext
      simpa using congrArg Subtype.val hgh

end GlobalTheory.UnipCT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqOfRealUnitaryConj
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal Matrix

namespace GlobalTheory.CovolConj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mass_le (X : Data E r) {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0) (h1 : IsOrth X x1)
    {F0 F1 : Set (V (nd X))} (hF0 : IsFundSet X x0 F0) (hF1 : IsFundSet X x1 F1) :
    muF X x0 F0 ≤ muF X x1 F1 := by
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hM : MeasInvStatement (E := E) := measInv_holds
  have hle := GlobalTheory.Unfold.lintegral_fundSet_inter_le hM r X x0 x1 h0 h1 F0 hF0 (fun _ => 1)
    measurable_const (fun _ _ _ _ _ _ => rfl) F1 hF1.1 hF1.2.1
  simp only [setLIntegral_one] at hle
  refine le_trans (le_of_eq ?_) hle
  let S : Set (Frame X.Ψ r) :=
    ⋃ γ : X.Γ, (fun x => lact (γ.1)⁻¹ x) ⁻¹' GlobalTheory.Unfold.satFrames X x1 F1
  have hS : MeasurableSet S := MeasurableSet.iUnion fun γ =>
    (GlobalTheory.Unfold.continuous_lact X _).measurable (GlobalTheory.Unfold.measurableSet_satFrames X h1 hF1.1 hF1.2.1)
  have hSiff : ∀ x, x ∈ S ↔ ∃ y ∈ F1, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
      x = lact γ (rmul (cpt X x1 y) b) := by
    intro x
    simp only [S, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨γ, y, hy, b, hb, h⟩
      refine ⟨y, hy, γ.1, γ.2, b, hb, ?_⟩
      rw [← h, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]
    · rintro ⟨y, hy, γ, hγ, b, hb, h⟩
      exact ⟨⟨γ, hγ⟩, y, hy, b, hb, by rw [h, FundSetPf.lact_inv]⟩
  have hSB : ∀ x, ∀ b ∈ Bor X.Ψ r, rmul x b ∈ S ↔ x ∈ S := by
    intro x b hb
    simp only [S, Set.mem_iUnion, Set.mem_preimage, FundSetPf.lact_rmul,
      GlobalTheory.Unfold.rmul_mem_satFrames_iff X x1 F1 _ hb]
  have hI := hM r X x0 x1 h0 h1 (Sᶜ.indicator fun _ => 1) (measurable_const.indicator hS.compl)
    (fun x _ b hb => by simp only [Set.indicator, Set.mem_compl_iff, hSB x b hb])
  have hc : ∀ x : Frame X.Ψ r, ∫⁻ z, (Sᶜ.indicator fun _ => (1 : ℝ≥0∞)) (cpt X x z) ∂muF X x =
      muF X x (cpt X x ⁻¹' Sᶜ) := by
    intro x
    rw [← lintegral_indicator_one ((FundSetPf.cont_cpt X x).measurable hS.compl)]
    rfl
  rw [hc, hc] at hI
  have hz1 : muF X x1 (cpt X x1 ⁻¹' Sᶜ) = 0 := by
    have : ∀ᵐ z ∂muF X x1, cpt X x1 z ∈ S := by
      filter_upwards [hF1.2.2.2] with z hz using (hSiff _).2 hz
    exact this
  have hz0 : ∀ᵐ z ∂muF X x0, cpt X x0 z ∈ S := hI.trans hz1
  refine measure_congr ?_
  filter_upwards [hz0] with z hz
  exact ⟨fun h => ⟨h, (hSiff _).1 hz⟩, fun h => h.1⟩

theorem mass_eq (X : Data E r) {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0) (h1 : IsOrth X x1)
    {F0 F1 : Set (V (nd X))} (hF0 : IsFundSet X x0 F0) (hF1 : IsFundSet X x1 F1) :
    muF X x0 F0 = muF X x1 F1 :=
  le_antisymm (mass_le X h0 h1 hF0 hF1) (mass_le X h1 h0 hF1 hF0)

omit [IsCMField E] [NumberField E] in
theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [IsCMField E] [NumberField E] in
theorem gram_mul {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} {u : Matrix (Fin r) (Fin r) ℂ}
    (hu : gram τ G u = G.map τ) (x : Matrix (Fin r) (Fin r) ℂ) : gram τ G (u * x) = gram τ G x := by
  rw [gram_eq] at hu
  rw [gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_assoc]

omit [IsCMField E] [NumberField E] in
theorem det_ne {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0)
    {u : Matrix (Fin r) (Fin r) ℂ} (hu : gram τ G u = G.map τ) : u.det ≠ 0 := by
  intro h
  rw [gram_eq] at hu
  have h2 := congrArg Matrix.det hu
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul] at h2
  have h3 : τ G.det = (G.map τ).det := RingHom.map_det τ G
  exact hG ((map_eq_zero τ).1 (h3.trans h2.symm))

noncomputable def umul {Ψ : Finset (E →+* ℂ)} (u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (x : Frame Ψ r) : Frame Ψ r :=
  fun τ => (u τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)

section

variable (X : Data E r) {u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}

omit [IsCMField E] [NumberField E] in
theorem umul_rmul {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) :
    umul u (rmul x b) = rmul (umul u x) b := by
  funext τ
  exact (Matrix.mul_assoc (u τ.1) (mat x τ) (mat b τ)).symm

theorem cpt_umul (x0 : Frame X.Ψ r) (z : V (nd X)) :
    cpt X (umul u x0) z = umul u (cpt X x0 z) := (umul_rmul _ _).symm

theorem gram_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (umul u x) τ) = gram τ.1 X.Gm (mat x τ) :=
  gram_mul (hu τ.1 τ.2) _

theorem umul_mem_dom (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) (x : Frame X.Ψ r) :
    umul u x ∈ X.dom ↔ x ∈ X.dom := by
  refine forall_congr' fun τ => and_congr ?_ ?_
  · have : mat (umul u x) τ = u τ.1 * mat x τ := rfl
    rw [this, Matrix.det_mul]
    exact ⟨right_ne_zero_of_mul, mul_ne_zero (det_ne X.Gm_det (hu τ.1 τ.2))⟩
  · simp only [dmin, gram_umul X hu]

theorem umul_inj (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) {x y : Frame X.Ψ r}
    (h : umul u x = umul u y) : x = y := by
  funext τ
  have h1 : u τ.1 * mat x τ = u τ.1 * mat y τ := congrFun h τ
  have hd : IsUnit (u τ.1).det := isUnit_iff_ne_zero.mpr (det_ne X.Gm_det (hu τ.1 τ.2))
  have := congrArg (fun M => (u τ.1)⁻¹ * M) h1
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hd] at this
  exact this

theorem umul_lact {γ γ' : GL (Fin r) E}
    (h : ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) (x : Frame X.Ψ r) :
    umul u (lact γ x) = lact γ' (umul u x) := by
  funext τ
  show u τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    (γ' : Matrix (Fin r) (Fin r) E).map τ.1 * (u τ.1 * mat x τ)
  rw [← Matrix.mul_assoc, h τ.1 τ.2, Matrix.mul_assoc]

theorem isOrth_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) {x0 : Frame X.Ψ r}
    (ho : IsOrth X x0) : IsOrth X (umul u x0) := fun τ => by
  rw [gram_umul X hu]; exact ho τ

theorem OmF_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) (x0 : Frame X.Ψ r) :
    OmF X (umul u x0) = OmF X x0 := by
  ext z
  show cpt X (umul u x0) z ∈ X.dom ↔ cpt X x0 z ∈ X.dom
  rw [cpt_umul, umul_mem_dom X hu]

theorem muF_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) (x0 : Frame X.Ψ r) :
    muF X (umul u x0) = muF X x0 := by
  have h2 : densF X (umul u x0) = densF X x0 := by
    funext z
    simp only [densF, dmin, cpt_umul, gram_umul X hu]
  simp only [muF, OmF_umul X hu, h2]

theorem fundSet_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ)
    (Γ' : Subgroup (GL (Fin r) E))
    (h1 : ∀ γ ∈ X.Γ, ∃ γ' ∈ Γ', ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ)
    (h2 : ∀ γ' ∈ Γ', ∃ γ ∈ X.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ)
    {x0 : Frame X.Ψ r} {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) :
    MeasurableSet FF ∧ FF ⊆ OmF X (umul u x0) ∧
    (∀ z ∈ FF, ∀ z' ∈ FF, ∀ γ ∈ Γ', ∀ b ∈ Bor X.Ψ r,
      cpt X (umul u x0) z' = lact γ (rmul (cpt X (umul u x0) z) b) → z = z') ∧
    ∀ᵐ z ∂muF X (umul u x0), ∃ z' ∈ FF, ∃ γ ∈ Γ', ∃ b ∈ Bor X.Ψ r,
      cpt X (umul u x0) z = lact γ (rmul (cpt X (umul u x0) z') b) := by
  refine ⟨hF.1, by rw [OmF_umul X hu]; exact hF.2.1, ?_, ?_⟩
  · intro z hz z' hz' γ' hγ' b hb h
    obtain ⟨γ, hγ, hc⟩ := h2 γ' hγ'
    rw [cpt_umul, cpt_umul, ← umul_rmul, ← umul_lact X hc] at h
    exact hF.2.2.1 z hz z' hz' γ hγ b hb (umul_inj X hu h)
  · rw [muF_umul X hu]
    filter_upwards [hF.2.2.2] with z hz
    obtain ⟨z', hz', γ, hγ, b, hb, h⟩ := hz
    obtain ⟨γ', hγ', hc⟩ := h1 γ hγ
    refine ⟨z', hz', γ', hγ', b, hb, ?_⟩
    rw [cpt_umul, cpt_umul, ← umul_rmul, ← umul_lact X hc, h]

end

theorem muF_eq_of_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (hΨ : X'.Ψ = X.Ψ) (u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (x0 : Frame X.Ψ r) (x0' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))), X'.Gm = X.Gm → X'.p0 = X.p0 → (∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) → (∀ γ ∈ X.Γ, ∃ γ' ∈ X'.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ = (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) → (∀ γ' ∈ X'.Γ, ∃ γ ∈ X.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ = (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) → IsOrth X x0 → IsOrth X' x0' → IsFundSet X x0 FF → IsFundSet X' x0' FF' → muF X x0 FF = muF X' x0' FF' := by
  intro E _ _ _ r X X' hΨ u x0 x0' FF FF' hG hp hu h1 h2 ho ho' hF hF'
  have k1 := isOrth_umul X hu ho
  have k2 := fundSet_umul X hu X'.Γ h1 h2 hF
  rw [← muF_umul X hu x0]
  have k3 := fun (y : Frame X'.Ψ r) (F : Set (V (nd X'))) (hy : IsOrth X' y) (hF0 : IsFundSet X' y F) =>
    mass_eq X' hy ho' hF0 hF'
  cases X
  cases X'
  dsimp only at hΨ hG hp
  subst hΨ hG hp
  exact k3 (umul u x0) FF k1 k2

end GlobalTheory.CovolConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRepPairedWithItself
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.GKPair

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem map_inv_map_star {B : Multiset ℂˣ} (h : B.map star = B.map (·⁻¹)) : (B.map (·⁻¹)).map star = B := by
  have e : (B.map (·⁻¹)).map star = (B.map star).map (·⁻¹) := by
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun u _ => ?_
    exact Units.ext (by simp)
  rw [e, h, Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id B]
  exact Multiset.map_congr rfl fun u _ => inv_inv u

theorem paired_of_form (π : CuspSub E a) (L : π.V ≃ₗ⋆[ℂ] π.V)
    (hL : ∀ o ψ, L (π.op (invTOp o) ψ) = π.op o (L ψ)) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ)
    (hpos : ∀ φ, φ ≠ 0 → 0 < (H φ φ).re)
    (hfin : ∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ)
    (hcpt : ∀ k φ ψ, H (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = H φ ψ)
    (hlie : ∀ X φ ψ, H (π.op (.lie X) φ) ψ + H φ (π.op (.lie X) ψ) = 0) :
    Paired π π invTOp := by
  let B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ := (H.comp L.toLinearMap).flip
  have hB : ∀ φ ψ, B φ ψ = H (L ψ) φ := fun _ _ => rfl
  have h0 : ∀ φ, H φ φ = 0 → φ = 0 := fun φ h => by
    by_contra hφ
    have := hpos φ hφ
    rw [h, Complex.zero_re] at this
    exact lt_irrefl _ this
  refine ⟨B, fun φ h => h0 φ ?_, fun ψ h => ?_, fun k φ ψ => ?_, fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · have := h (L.symm φ)
    rwa [hB, LinearEquiv.apply_symm_apply] at this
  · have := h (L ψ)
    rw [hB] at this
    exact (map_eq_zero_iff L L.injective).1 (h0 _ this)
  · rw [hB, hB, hL, hfin]
  · rw [hB, hB, hL, hcpt]
  · rw [hB, hB, hL, add_comm]
    exact hlie X (L ψ) φ

theorem paired_invTOp (hJS : GlobalTheory.Published.JacquetShalikaRigidity) (hB : GlobalTheory.Published.CuspFormsBoundedGL)
    (hA : GlobalTheory.Published.AutomorphicFormsFiniteGL) (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ha : 1 ≤ a) (π : CuspSub E a) (hπ : GlobalTheory.DiscSpec.IsNormalised π) : Paired π π invTOp := by
  obtain ⟨H, hH, hpos, hfin, hcpt, hlie⟩ := _root_.GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian hB E a π hπ
  obtain ⟨π₂, J, hJ⟩ := _root_.GlobalTheory.exists_conj_cuspSub E a (UpperTheory.V.TC.dual π)
  have hsat : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk π₂).HasSat w B ∧ (CG.mk π).HasSat w B := by
    refine (_root_.GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hA E a π).mono fun w ⟨B, hBw⟩ => ⟨B, ?_, hBw⟩
    have h1 := UpperTheory.V.TC.hasSatGL_dual hBw
    have h2 := _root_.GlobalTheory.LFun.hasSatGL_of_conjIntertwiner E w a _ _ ((UpperTheory.V.TC.dual π).locRep w) (π₂.locRep w) J
      (fun g x => by rw [CuspSub.locRep_eq, CuspSub.locRep_eq, hJ]) _ h1
    have h3 := _root_.GlobalTheory.CuspRep.UnitaryParam.map_star_eq_map_inv_of_form E a π H hH hpos hfin w B hBw
    rw [map_inv_map_star h3] at h2
    exact h2
  have e := hJS.strong_multiplicity_one ha (CG.mk π₂) (CG.mk π) hsat
  obtain ⟨T, hT⟩ : CuspSub.Iso π₂ π := Quotient.exact e
  let L : π.V ≃ₗ⋆[ℂ] π.V := ((UpperTheory.V.TC.toDual π).trans J).trans T
  refine paired_of_form π L (fun o ψ => ?_) H hpos hfin hcpt hlie
  change T (J (UpperTheory.V.TC.toDual π (π.op (invTOp o) ψ))) = π.op o (T (J (UpperTheory.V.TC.toDual π ψ)))
  rw [← UpperTheory.V.TC.op_toDual, hJ, hT]

end GlobalTheory.GKPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalPointEqMapRational
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.BCT.LocVal

theorem cj_algebraMap {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (hw : ¬ IsSplitAt w) (x : E) :
    cj w (algebraMap E (w.adicCompletion E) x) = algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x) := by
  have key : ∀ u : Pl E, u = w → ∀ f : u.adicCompletion E →+* w.adicCompletion E, Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
      ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
        ∀ k : E, s (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k) := by
    intro u hu f hf hk
    subst hu
    exact ⟨f, hf, hk⟩
  have hex := key _ ((GlobalTheory.ConjAtPlace.conjSrc_eq_iff w).2 hw) (GlobalTheory.CuspRep.conjLoc ((IsCMField.complexConj E).toRingEquiv) w)
    (GlobalTheory.CuspRep.conjLoc_spec _ w).1 (GlobalTheory.CuspRep.conjLoc_spec _ w).2.1
  unfold cj
  rw [dite_eq_left hex]
  exact hex.choose_spec.2 x

theorem map_mem_UL {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (γ : UE E n) (w : Pl E) :
    Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ : GL (Fin n) E) ∈ UL n w := by
  unfold UL
  split_ifs with hw
  · exact Subgroup.mem_top _
  · have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ : GL (Fin n) E).val * 1 * (γ : GL (Fin n) E).val = 1 :=
      γ.2
    change cT (cj w) ((algebraMap E (w.adicCompletion E)).mapMatrix (γ : GL (Fin n) E).val) * 1 *
      (algebraMap E (w.adicCompletion E)).mapMatrix (γ : GL (Fin n) E).val = 1
    have e : cT (cj w) ((algebraMap E (w.adicCompletion E)).mapMatrix (γ : GL (Fin n) E).val) =
        (algebraMap E (w.adicCompletion E)).mapMatrix
          (cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ : GL (Fin n) E).val) := by
      ext i j
      simp [cT, Matrix.map_apply, cj_algebraMap w hw]
    rw [e, Matrix.mul_one, ← map_mul, ← Matrix.mul_one (cT _ _), hγ, map_one]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E),
    ((locPt w γ : UL n w) : GLw n w) = Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ : GL (Fin n) E) := by
  intro E _ _ _ _ n γ w
  unfold locPt toSub
  rw [dite_eq_left (map_mem_UL γ w)]

end GlobalTheory.BCT.LocVal
end
end

