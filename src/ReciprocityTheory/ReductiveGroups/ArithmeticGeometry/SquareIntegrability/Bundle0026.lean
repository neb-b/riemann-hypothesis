module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PaThDiffLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PointNormSqNonnegQuotient

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColEmpty
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

theorem colTorus (hx : Ext.All) (hA : PropAStatement) (hS : GSupStatement) : ColTorusStatement := by
  obtain ⟨hP, hGT, -⟩ := hx
  intro E _ _ _ X DF P I hI c hc σ x0 u hx0 hu n hn hun hc6
  exact ct_core hP hGT hA hS hI c hc σ x0 u hx0 hu n hn hun hc6

theorem colAbel (hx : Ext.All) (hA : PropAStatement) (hS : GSupStatement) : ColAbelStatement := by
  obtain ⟨hP, hGT, -⟩ := hx
  intro E _ _ _ X DF P I hI c hc σ ξ _ hξ1 hξI
  exact cab_core hP hGT hA hS hI c hc σ ξ hξ1 hξI

theorem colEmpty (hx : Ext.All) (hA : PropAStatement) (hS : GSupStatement) : ColEmptyStatement := by
  obtain ⟨hP, hGT, -⟩ := hx
  intro E _ _ _ X DF P I hI
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hM : 0 ≤ M1 (E := E) P.m := by
    unfold M1 PT.rd
    positivity
  have hu0 : IsU I (0 : Vsp X.dim) 0 := ⟨Submodule.zero_mem _, fun a _ => by simp [Hf]⟩
  obtain ⟨s', hs', ζ, hζ, hd, hl⟩ := ct_core hP hGT hA hS hI 0 (Nat.zero_le _) σ 0 0
    (Submodule.zero_mem _) hu0 1 le_rfl (by norm_num)
    (fun y _ uy _ => by simpa using mul_nonneg hM (sq_nonneg ‖uy‖))
  have h0 := hd Fin.elim0 (fun k => k.elim0)
  simp only [d1, iteratedFDeriv_zero_apply, pow_zero, Finset.univ_eq_empty, Finset.prod_empty,
    mul_one] at h0
  refine ⟨s', hs', ?_, by simpa using hl⟩
  have h1 := norm_sub_norm_le ζ (s' 0)
  rw [norm_sub_rev] at h1
  have h2 := epsilon_le_half P
  linarith

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.CubeSplit
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

theorem cube_split {α β : Type} [Fintype α] [Fintype β] (f : (α ⊕ β → ℝ) → ENNReal)
    (hf : Measurable f) :
    ∫⁻ x in cubeIco (α ⊕ β), f x =
      ∫⁻ y in cubeIco β, ∫⁻ t in cubeIco α, f (fun k => Sum.elim t y k) := by
  have hmp := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : α ⊕ β => ℝ)
  rw [← hmp.setLIntegral_comp_preimage_emb
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : α ⊕ β => ℝ)).symm.measurableEmbedding]
  have hpre : (MeasurableEquiv.sumPiEquivProdPi (fun _ : α ⊕ β => ℝ)).symm ⁻¹' cubeIco (α ⊕ β) =
      cubeIco α ×ˢ cubeIco β := by
    ext ⟨t, y⟩
    simp [cubeIco, MeasurableEquiv.coe_sumPiEquivProdPi_symm, Sum.forall]
  rw [hpre, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm]
  · rfl
  · exact (hf.comp (MeasurableEquiv.sumPiEquivProdPi _).symm.measurable).aemeasurable

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

def What (hI : IsSplit P I) (hP : Ext.PackingCount) (a : Fin (Module.finrank ℝ (IR I)) → ℝ)
    (r : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ) : Vsp X.dim :=
  ∑ j, a j • cp hI j + ∑ l, r l • cpp hI hP l

theorem uc_rsmul (c : ℝ) (v : Vsp X.dim) : uc (IR I) (c • v) = c • uc (IR I) v := by
  simp only [uc, z, Hf_rsmul_l, Complex.im_ofReal_mul, Finset.smul_sum, mul_smul]

theorem uc_sum {ι : Type} (F : Finset ι) (f : ι → Vsp X.dim) :
    uc (IR I) (∑ i ∈ F, f i) = ∑ i ∈ F, uc (IR I) (f i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using uc_rsmul (I := I) (0 : ℝ) (0 : Vsp X.dim)
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, uc_add, ih]

theorem uc_What (hI : IsSplit P I) (hP : Ext.PackingCount) (a r) :
    uc (IR I) (What hI hP a r) = ∑ j, a j • uc (IR I) (cp hI j) := by
  have h0 : ∀ l, uc (IR I) (cpp hI hP l) = 0 := fun l => uc_Ip (cpp_mem hI hP l)
  simp only [What, uc_add, uc_sum, uc_rsmul, h0, smul_zero, Finset.sum_const_zero, add_zero]

theorem wmap_What (hI : IsSplit P I) (hP : Ext.PackingCount) (a r) :
    wmap (IR I) (What hI hP a r) = wmap (IR I) (∑ j, a j • cp hI j) + (bB hI hP).equivFun.symm r := by
  rw [What, map_add (f := _)]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Module.Basis.equivFun_symm_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ContinuousLinearMap.map_smul_of_tower, cpp_wmap]

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end

