module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0010
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0025
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0057
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0016

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.HaarMeasureTripleProductDecomposition
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP

theorem UpperTheory.haarMeasure_triple_product_decomposition :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B C : Subgroup G), IsClosed (A : Set G) → IsClosed (B : Set G) → IsClosed (C : Set G) → ∀ (j : A × B × C ≃ₜ* G) (μ : Measure G), μ.IsHaarMeasure → ∀ (μA : Measure A) (μB : Measure B) (μC : Measure C), μA.IsHaarMeasure → μB.IsHaarMeasure → μC.IsHaarMeasure → ∀ f : G → ℂ, Integrable f μ → Integrable (fun y => f (j y)) (μA.prod (μB.prod μC)) ∧ ∃ c : ℝ, ∫ y, f (j y) ∂(μA.prod (μB.prod μC)) = c * ∫ g, f g ∂μ := by
  intro G _ _ _ _ _ _ _ _ A B C hA hB hC j μ hμ μA μB μC hμA hμB hμC f hf
  haveI : LocallyCompactSpace A := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace C := hC.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : (μB.prod μC).IsHaarMeasure := Measure.prod.instIsHaarMeasure μB μC
  haveI : SigmaFinite (μB.prod μC) := inferInstance
  haveI : MeasurableMul (B × C) := inferInstance
  haveI hPH : (μA.prod (μB.prod μC)).IsHaarMeasure :=
    Measure.prod.instIsHaarMeasure μA (μB.prod μC)
  set P : Measure (A × B × C) := μA.prod (μB.prod μC) with hP
  have hme : MeasurableEmbedding j := j.toHomeomorph.measurableEmbedding
  haveI hmap : (Measure.map j P).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map P j
  have hk : Measure.map j P = Measure.haarScalarFactor (Measure.map j P) μ • μ :=
    Measure.isMulLeftInvariant_eq_smul _ _
  set k : ℝ≥0 := Measure.haarScalarFactor (Measure.map j P) μ with hkdef
  have hfm : Integrable f (Measure.map j P) := by
    rw [hk]; exact hf.smul_measure (by simp)
  refine ⟨?_, (k : ℝ), ?_⟩
  · exact (hme.integrable_map_iff).1 hfm
  · have h1 : ∫ g, f g ∂(Measure.map j P) = ∫ y, f (j y) ∂P := hme.integral_map f
    rw [← h1, hk, integral_smul_nnreal_measure]
    simp [NNReal.smul_def]
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.MatrixCoefficientBoundedByValueAtOne
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP

namespace UpperTheory.MatrixCoefficientBound

open scoped Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G}

private theorem sq_shift (hD : IsFundamentalDomain Γ D μ) {f : G → ℝ} (hi : ∀ γ ∈ Γ, ∀ y, f (γ * y) = f y) (g : G) :
    ∫ y in D, f (y * g) ∂μ = ∫ y in D, f y ∂μ :=
  _root_.UpperTheory.Reformulated.B.Qk59.sq_shift hD hi g

private theorem coef_le (hfin : μ D < ⊤) (hD : IsFundamentalDomain Γ D μ) {φ : G → ℂ} (hc : Continuous φ)
    (hi : ∀ γ ∈ Γ, ∀ y, φ (γ * y) = φ y) {C : ℝ} (hC : ∀ y, ‖φ y‖ ≤ C) (g : G) :
    ‖∫ y in D, φ (y * g) * star (φ y) ∂μ‖ ≤ ∫ y in D, ‖φ y‖ ^ 2 ∂μ := by
  have hb : ∀ {ψ : G → ℂ}, Continuous ψ → (∀ y, ‖ψ y‖ ≤ C) → IntegrableOn (fun y => ‖ψ y‖ ^ 2) D μ := fun {ψ} h1 h2 =>
    Measure.integrableOn_of_bounded (M := C ^ 2) hfin.ne (h1.norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (h2 y) 2)
  have hcg : Continuous fun y => φ (y * g) := hc.comp (continuous_mul_const g)
  have i1 := hb hcg fun y => hC _
  have i2 := hb hc hC
  have e := sq_shift (μ := μ) hD (f := fun y => ‖φ y‖ ^ 2) (fun γ hγ y => by simp only [hi γ hγ y]) g
  calc ‖∫ y in D, φ (y * g) * star (φ y) ∂μ‖ ≤ ∫ y in D, ‖φ (y * g) * star (φ y)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in D, (‖φ (y * g)‖ ^ 2 + ‖φ y‖ ^ 2) / 2 ∂μ := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) ((i1.add i2).div_const 2) (Eventually.of_forall fun y => ?_)
      simp only [norm_mul, norm_star]
      nlinarith [sq_nonneg (‖φ (y * g)‖ - ‖φ y‖)]
    _ = ∫ y in D, ‖φ y‖ ^ 2 ∂μ := by
      rw [integral_div, integral_add i1 i2, e]
      ring

end UpperTheory.MatrixCoefficientBound

theorem UpperTheory.matrix_coefficient_bounded_by_value_at_one :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}, Cpt σ X.J → M.μ.IsHaarMeasure → IsFundamentalDomain (ratU σ X.J) M.dom M.μ → ∀ {φ : UA σ X.J → ℂ}, IsFn φ → φ ≠ 0 → ∃ r : ℝ, 0 < r ∧ mc M φ 1 = r ∧ ∀ g, ‖mc M φ g‖ ≤ r := by
  intro F E _ _ _ _ _ σ n d X W M hK hμ hD φ hφ h0
  haveI := hK.cnt
  haveI := hK.right M.μ hμ
  obtain ⟨C, hC⟩ := hK.bdd hφ.1 hφ.2
  have e1 : mc M φ 1 = ((∫ y in M.dom, ‖φ y‖ ^ 2 ∂M.μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp only [mc, pet, mul_one]
    exact integral_congr_ae (Eventually.of_forall fun y => by simpa using Complex.mul_conj' (φ y))
  have hp : (∫ y in M.dom, ‖φ y‖ ^ 2 ∂M.μ) ≠ 0 := fun h => h0 <| hK.eq_zero hμ hD hφ.1 hφ.2 (by
    have : pet M.μ M.dom φ φ = mc M φ 1 := by simp [mc]
    rw [this, e1, h]; simp)
  refine ⟨_, lt_of_le_of_ne (integral_nonneg fun y => by positivity) hp.symm, e1, fun g => ?_⟩
  exact UpperTheory.MatrixCoefficientBound.coef_le (hK.fin M.μ M.dom hμ hD) hD hφ.1 hφ.2 hC g
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.UnitaryAdelicMemOfLocalGroupsNearOne
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP

private theorem prj_of_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} {v : Pl (F := F)} {g : UA σ X.J} (hg : OffAt v g) : Euler.prj v g = 1 := by
  have h : PositivityTheory.ThKG.Loc.idem F v • (mat g - 1) = 0 := Matrix.ext fun i j => Bad.idem_off (by
    have := congrFun₂ hg i j
    rw [Matrix.map_apply] at this
    simp [this, Matrix.one_apply, apply_ite (compFin F E v)])
  refine Subtype.ext (Units.ext ?_)
  show Euler.cut (PositivityTheory.ThKG.Loc.idem F v) (mat g) = 1
  rw [← sub_eq_zero, Euler.cut_sub, h]

theorem UpperTheory.unitaryAdelic_mem_of_localGroups_near_one :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} (S : Finset (Pl (F := F))) (H : Pl (F := F) → Subgroup (UA σ X.J)), (∀ v ∈ S, ∃ O : Set (UA σ X.J), IsOpen O ∧ 1 ∈ O ∧ ∀ g ∈ locGrp σ X v, g ∈ O → g ∈ H v) → (∀ b ∈ gAt σ X S, ∃ c : Pl (F := F) → UA σ X.J, (∀ v, c v ∈ locGrp σ X v) ∧ (∀ v ∈ S, OffAt v ((c v)⁻¹ * b)) ∧ ∀ H : Subgroup (UA σ X.J), (∀ v ∈ S, c v ∈ H) → b ∈ H) → IsOpen {b : gAt σ X S | b.1 ∈ ⨆ v ∈ S, H v} := by
  intro F E _ _ _ _ _ σ n X S H hO hb
  choose! O hOo h1 hOH using hO
  let K : Subgroup (gAt σ X S) := (⨆ v ∈ S, H v).subgroupOf (gAt σ X S)
  have hK : IsOpen (K : Set (gAt σ X S)) := by
    refine Subgroup.isOpen_of_mem_nhds K (g := 1) ?_
    let U : Set (gAt σ X S) := ⋂ v ∈ S, (fun b : gAt σ X S => Euler.prj v b.1) ⁻¹' O v
    have oU : IsOpen U := isOpen_biInter_finset fun v hv =>
      (hOo v hv).preimage (Euler.cont_prj.comp continuous_subtype_val)
    have mU : (1 : gAt σ X S) ∈ U := by
      refine Set.mem_iInter₂.2 fun v hv => ?_
      show Euler.prj v (1 : UA σ X.J) ∈ O v
      rw [map_one]
      exact h1 v hv
    refine Filter.mem_of_superset (oU.mem_nhds mU) fun b hbU => ?_
    obtain ⟨c, hc, hoff, hlast⟩ := hb b.1 b.2
    refine Subgroup.mem_subgroupOf.2 (hlast _ fun v hv => ?_)
    have e : Euler.prj v b.1 = c v := by
      have := prj_of_off (hoff v hv)
      rw [map_mul, map_inv, Euler.mem_loc.1 (hc v), inv_mul_eq_one] at this
      exact this.symm
    have hm : c v ∈ O v := e ▸ (Set.mem_iInter₂.1 hbU v hv)
    exact (le_iSup₂_of_le v hv le_rfl : H v ≤ ⨆ v ∈ S, H v) (hOH v hv _ (hc v) hm)
  exact hK
end

