module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.FinOneOneMem
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finOne_one_mem : finOne F • (1 : AE F E) ∈ intHat F E := by
  refine AddSubgroup.subset_closure ⟨finOne F, ?_, fun v => ?_, 1, ?_⟩
  · show InfiniteAdeleRing.ringEquiv_mixedSpace F (finOne F).1 = 0
    rw [show (finOne F).1 = 0 from rfl, map_zero]
  · rw [show evFin F v (finOne F) = 1 from map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)]
    exact one_mem _
  · simp

theorem int_blk {N n : ℕ} (h : n + 1 = N) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :
    (∀ u v, finOne F • blk h M 1 u v ∈ intHat F E) ↔ ∀ u v, finOne F • M u v ∈ intHat F E := by
  constructor
  · intro H u v
    have := H (Sum.map (em0 h) (em0 h) u) (Sum.map (em0 h) (em0 h) v)
    rwa [blk_map_apply] at this
  · intro H u v
    rw [blk_apply]
    generalize eB h u = x
    generalize eB h v = y
    rcases x with x | x <;> rcases y with y | y
    · exact H x y
    · simp
    · simp
    · simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      split_ifs
      · exact finOne_one_mem
      · simp

theorem kStd : KStd := by
  intro F E _ _ _ _ _ σ d n h Y b j hb hj
  have hX : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => eq_blk h _ _ (hj.2.1 g) (hj.2.2 g)
  intro k
  rw [Subgroup.mem_comap, d.ok.stdK (j k)]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, ← map_inv, hX]
  refine and_congr (forall_congr' fun w => ?_) (and_congr (int_blk h _) (int_blk h _))
  rw [blk_map _ _ _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _), blk_conjTranspose,
    Matrix.conjTranspose_one, blk_mul, Matrix.one_mul, blk_eq_one_iff]

end PositivityTheory.SiegelWeilFormula.Ald

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.JEx
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem jEx : JEx := by
  intro F E _ _ _ _ _ σ d n h Y b ε e1 e2
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (G2 σ Y) := Subgroup.instIsTopologicalGroupSubtypeMem _
  let j : G2 σ Y →* d.G := (jHom d h b).codRestrict _ (jHom_mem d h b ε e1 e2)
  have hfr : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => by
    rw [inFrame_eq]
    show incM F (d.b⁻¹).1 * (jHom d h b g).1 * incM F d.b.1 = _
    rw [jHom_val]
    simp only [← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, incM_inv_mul, Matrix.mul_one]
  refine ⟨j, ?_, fun g => by rw [hfr]; exact blk_sub h _ _, fun g => by rw [hfr]; exact blk_out h _⟩
  have h1 : Continuous fun g : G2 σ Y => g.1.1 := Units.continuous_val.comp continuous_subtype_val
  have hv : Continuous fun g : G2 σ Y => (jHom d h b g).1 := by
    simp only [jHom_val, inFrame_eq]
    exact (continuous_const.matrix_mul ((((continuous_const.matrix_mul h1).matrix_mul continuous_const).matrix_fromBlocks
      continuous_const continuous_const continuous_const).matrix_submatrix _ _)).matrix_mul continuous_const
  have hc : Continuous (jHom d h (Y := Y) b) := by
    refine Units.continuous_iff.2 ⟨hv, ?_⟩
    have e : (fun g : G2 σ Y => ((jHom d h b g)⁻¹ : GL _ _).1) = fun g : G2 σ Y => (jHom d h b g⁻¹).1 :=
      funext fun g => by rw [map_inv]
    rw [e]
    exact hv.comp continuous_inv
  exact hc.subtype_mk _

end PositivityTheory.SiegelWeilFormula.Ald

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SliceFacts
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F : Type} [Field F] [NumberField F]

theorem projHom {κ : Type} [Fintype κ] {G : Type} [Group G]
    (c : G → ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (hp : ∀ g, ∀ φ ∈ schA F κ, c g φ ∈ schA F κ)
    (h1 : ∀ φ ∈ schA F κ, c 1 φ = φ) (hm : ∀ g h, ∀ φ ∈ schA F κ, c (g * h) φ = c g (c h φ)) :
    ∃ om : G →* Module.End ℂ ((κ → AF F) → ℂ), ∀ g, ∀ φ ∈ schA F κ, om g φ = c g φ := by
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl (schA F κ)
  set P : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) := (schA F κ).subtype ∘ₗ (schA F κ).projectionOnto T hT with hPdef
  have hPS : ∀ x, P x ∈ schA F κ := fun x => Submodule.coe_mem _
  have hPid : ∀ x ∈ schA F κ, P x = x := fun x hx => by
    rw [hPdef, LinearMap.comp_apply, Submodule.linearProjOfIsCompl_apply_left hT ⟨x, hx⟩]
    rfl
  have hPP : ∀ x, P (x - P x) = 0 := fun x => by
    rw [map_sub, hPid _ (hPS x), sub_self]
  refine ⟨{ toFun := fun g => c g ∘ₗ P + (LinearMap.id - P), map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · refine LinearMap.ext fun x => ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      h1 _ (hPS x), Module.End.one_apply]
    abel
  · intro g k
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      Module.End.mul_apply, map_add, hPP, hPid _ (hp k _ (hPS x)), add_zero, hm g k _ (hPS x), map_zero]
    abel
  · intro g φ hφ
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, hPid φ hφ, sub_self, add_zero]

def slice0 (κ' κ'' : Type) : ((κ' ⊕ κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ) where
  toFun Ψ x' := Ψ (Sum.elim x' 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def SliceFacts : Prop := ∀ (F : Type) [Field F] [NumberField F] (κ' κ'' : Type) [Fintype κ'] [Fintype κ''],
  (∀ Ψ ∈ schA F (κ' ⊕ κ''), slice0 κ' κ'' Ψ ∈ schA F κ') ∧
  (∀ l ∈ (adeleClass F).adm κ', l ∘ₗ slice0 κ' κ'' ∈ (adeleClass F).adm (κ' ⊕ κ'')) ∧
  (∃ φ₀ ∈ schA F κ'', φ₀ 0 = 1 ∧ ∀ μ'' : @Measure (κ'' → AF F) (borel _),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ'' → ∫⁻ x, ‖φ₀ x‖ₑ ^ 2 ∂μ'' ≠ 0 ∧ ∫⁻ x, ‖φ₀ x‖ₑ ^ 2 ∂μ'' ≠ ⊤) ∧
  ∀ (μ' : @Measure (κ' → AF F) (borel _)) (μ'' : @Measure (κ'' → AF F) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ' → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ'' →
    ∃ μ : @Measure (κ' ⊕ κ'' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
      ∀ φ' ∈ schA F κ', ∀ φ'' ∈ schA F κ'', ∫⁻ x, ‖boxFun φ' φ'' x‖ₑ ^ 2 ∂μ = (∫⁻ x, ‖φ' x‖ₑ ^ 2 ∂μ') * ∫⁻ x, ‖φ'' x‖ₑ ^ 2 ∂μ''

end PositivityTheory.SiegelWeilFormula.Ald

end
end

