module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoWA
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JTransMA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JTransMB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0006

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurW
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace SchurWAux

theorem fdeg_eq_finrank {G : Type*} [MeasurableSpace G] (μ : Measure G) [IsProbabilityMeasure μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [Nontrivial H]
    (ρ : G → (H →L[ℂ] H)) (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖) (d : ℝ) (hd : 0 < d)
    (h : ∀ v w v' w' : H, Integrable (fun g => ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ g v'⟫_ℂ) μ ∧
      ∫ g, ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) :
    (d : ℂ) = (Module.finrank ℂ H : ℂ) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  set b := stdOrthonormalBasis ℂ H
  have hpt : ∀ g, ∑ i, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    have e1 : ∀ i, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ = ⟪ρ g v, b i⟫_ℂ * ⟪b i, ρ g v⟫_ℂ := by
      intro i
      rw [mul_comm]
      congr 1
      exact inner_conj_symm _ _
    simp_rw [e1]
    rw [b.sum_inner_mul_inner, inner_self_eq_norm_sq_to_K, hiso]
    push_cast
    rfl
  have hbi : ∀ i, ⟪b i, b i⟫_ℂ = 1 := by
    intro i
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  have hL : ∫ g, ∑ i, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ ∂μ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hpt]
    simp
  rw [MeasureTheory.integral_finsetSum _ (fun i _ => (h v (b i) v (b i)).1)] at hL
  have e2 : ∀ i, ∫ g, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ ∂μ = ((‖v‖ ^ 2 : ℝ) : ℂ) / (d : ℂ) := by
    intro i
    rw [(h v (b i) v (b i)).2, hbi, mul_one, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  simp_rw [e2] at hL
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hL
  have hv2 : ((‖v‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < ‖v‖ := norm_pos_iff.mpr hv
    exact_mod_cast (pow_pos this 2).ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [mul_div_assoc', div_eq_iff hd'] at hL
  exact (mul_right_cancel₀ hv2 (by rw [hL]; ring)).symm

end SchurWAux

theorem stSchurW (h : UnitaryGroupStructuralFacts) : StSchurW := by
  obtain ⟨hB2, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCpt, -, -, -, hHI, -, -, -, hCW, -⟩ := hB2
  intro k r Wp _ _ _ D hD v w v' w'
  rcases subsingleton_or_nontrivial Wp with hW | hW
  · rw [Subsingleton.elim w 0]
    simp
  have hU : IsClosedSubgroup (UWset k r D.z) := hCW k r D.z
  have hμ := D.haarW
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  let μ : Measure (MatrixSubsetMeasurability.SG hU) := MatrixSubsetMeasurability.nu hU D.μW
  have : μ.IsMulLeftInvariant := MatrixSubsetMeasurability.nu_left hμ
  have : μ.IsInvInvariant := MatrixSubsetMeasurability.nu_inv hHI hμ
  have hE := MatrixSubsetMeasurability.me_val hU
  have hcpt : IsCompact (Set.univ : Set (MatrixSubsetMeasurability.SG hU)) := by
    have hind : Topology.IsInducing (fun g : MatrixSubsetMeasurability.SG hU => g.1) := Topology.IsInducing.subtypeVal
    have hr : Set.range (fun g : MatrixSubsetMeasurability.SG hU => g.1) = {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r D.z} :=
      Subtype.range_coe_subtype
    rw [hind.isCompact_iff, Set.image_univ, hr]
    exact hCpt k r D.z D.z_mem D.T_pos
  have hν1 : μ Set.univ = 1 := by
    have e : ((MatrixSubsetMeasurability.nu hU D.μW).map (fun g : MatrixSubsetMeasurability.SG hU => g.1)) Set.univ = D.μW Set.univ := by
      rw [MatrixSubsetMeasurability.map_nu hμ]
    rw [Measure.map_apply hE.measurable MeasurableSet.univ, Set.preimage_univ] at e
    exact e.trans hD.mass
  have : IsProbabilityMeasure μ := ⟨hν1⟩
  have : μ.IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact _ hcpt (by rw [hν1]; exact one_ne_zero)
  let ρ : MatrixSubsetMeasurability.SG hU → (Wp →L[ℂ] Wp) := fun g => D.π (MatrixSubsetMeasurability.mat g)
  have h1 : ρ 1 = 1 := D.π_rep.1
  have hρm : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b) := fun a b => D.π_rep.2 _ a.2 _ b.2
  have hiso : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => D.π_unitary _ g.2 v
  have hcont : ∀ v, Continuous fun g => ρ g v := fun v =>
    (D.π_cont.comp_continuous MatrixSubsetMeasurability.continuous_mat MatrixSubsetMeasurability.mat_mem).clm_apply continuous_const
  have hsq : ∀ v w : Wp, MemLp (fun g => ⟪w, ρ g v⟫_ℂ) 2 μ := by
    intro v w
    refine MemLp.of_bound (continuous_const.inner (hcont v)).aestronglyMeasurable (‖w‖ * ‖v‖)
      (ae_of_all _ fun g => ?_)
    exact (norm_inner_le_norm _ _).trans (le_of_eq (by rw [hiso]))
  have hirr : ∀ S : Submodule ℂ Wp, IsClosed (S : Set Wp) → (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤ :=
    fun S hS hst => hD.irr S hS fun g hg v hv => hst (MatrixSubsetMeasurability.mk hU g hg) v hv
  have hSq : Formalism.MainNotions.BridgeCSchur.SqRep μ ρ := ⟨h1, hρm, hiso, hcont, hsq⟩
  obtain ⟨d, hd, hrel⟩ := Formalism.MainNotions.BridgeCSchur.schur_orth hSq hirr
  have hdn := SchurWAux.fdeg_eq_finrank μ ρ hiso d hd hrel
  rw [← MatrixSubsetMeasurability.map_nu (hU := hU) hμ, hE.integral_map, ← hdn]
  exact (hrel v w v' w').2

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JTransM
section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stTransM (h : UnitaryGroupStructuralFacts) : StTransM := by
  obtain ⟨hB2, -, -, -, hUWb, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCG, -⟩ := hB2
  intro k r Wp _ _ _ D X _ _ γ hγ y hy
  have hG := hCG k r
  have hEG : embWb k r γ ∈ GV k r := by
    have hmem : embWb k r γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγ.1, rfl⟩
    exact hmem.1
  have hE := hG.unit _ hEG
  set E := embWb k r γ with hEdef
  have hEiG : E⁻¹ ∈ GV k r := hG.inv_mem _ hEG
  have hc : ∀ B : Mat k r, E⁻¹ * (E * B) = B := fun B => Matrix.nonsing_inv_mul_cancel_left E B hE
  have hEE : ∀ v, E⁻¹ *ᵥ (E *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hE, Matrix.one_mulVec]
  have hEfix : ∀ j, ¬ InvGrp.isW k r j → E *ᵥ bvec j = bvec j := fun j hj =>
    InvGrp.embWb_fix_offW γ _ (InvGrp.bvec_offW j hj)
  have hEifix : ∀ j, ¬ InvGrp.isW k r j → E⁻¹ *ᵥ bvec j = bvec j := fun j hj =>
    InvGrp.embWb_inv_fix_offW hE _ (InvGrp.bvec_offW j hj)
  have hwl : ¬ InvGrp.isW k r (wI k r (Fin.last k)) → False := fun h => h ⟨by simp [wI], by simp [wI]⟩
  set b := bvec (wI k r (Fin.last k)) with hbdef
  have hs0 : ((Real.sqrt (Tz k r D.z) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr D.T_pos).ne'
  have hzE : D.z = ((Real.sqrt (Tz k r D.z) : ℝ) : ℂ) • (E *ᵥ b) := by
    rw [hγ.2, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hs0, one_smul]

  set x := E⁻¹ * y * E with hxdef
  have hxG : x ∈ GV k r := hG.mul_mem _ (hG.mul_mem _ hEiG _ hy.1) _ hEG
  have hxv : ∀ v, x *ᵥ v = E⁻¹ *ᵥ (y *ᵥ (E *ᵥ v)) := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hxe : ∀ a : Fin r, x *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ x *ᵥ bvec (esI k r a) = bvec (esI k r a) := by
    intro a
    constructor
    · rw [hxv, hEfix _ (InvGrp.not_isW_eI a), (hy.2.1 a).1, hEifix _ (InvGrp.not_isW_eI a)]
    · rw [hxv, hEfix _ (InvGrp.not_isW_esI a), (hy.2.1 a).2, hEifix _ (InvGrp.not_isW_esI a)]
  have hxl : x *ᵥ b = b := by
    rw [hxv, hγ.2, Matrix.mulVec_smul, hy.2.2, ← hγ.2, hEE]
  have hxeq := TransM.eq_Qm x hxG hxe hxl
  set m := x.submatrix (Subtype.val : {i // TransM.pK k r i} → _) Subtype.val with hmdef
  have hm : mᴴ * m = 1 := TransM.unitary_of_Qm m (hxeq ▸ hxG)
  have hw : ∀ s : {i // TransM.pK k r i}, conj (bvec (wI k r 0) s.1) = bvec (wI k r 0) s.1 := by
    intro s
    simp only [bvec, Pi.single_apply]
    split_ifs <;> simp
  obtain ⟨U, hU1, hUw, hUc⟩ := TransM.exists_transpose_mat m hm (fun s => bvec (wI k r 0) s.1) hw
  set PU := TransM.Qm U 1 with hPUdef
  have hPUG : PU ∈ GV k r := TransM.Qm_mem_UH U hU1
  have hPUs : TransM.Qm Uᴴ 1 * PU = 1 := by
    rw [hPUdef, TransM.Qm_mul, hU1, Matrix.one_mul, TransM.Qm_one]
  have hPUs' : PU * TransM.Qm Uᴴ 1 = 1 := by
    rw [hPUdef, TransM.Qm_mul, mul_eq_one_comm.mp hU1, Matrix.one_mul, TransM.Qm_one]
  have hkey : x.map (starRingEnd ℂ) * PU * x = PU := by
    rw [hxeq, TransM.Qm_map, hPUdef, TransM.Qm_mul, TransM.Qm_mul, hUc]
    simp
  have hyx : y = E * x * E⁻¹ := by
    rw [hxdef]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left E _ hE, Matrix.mul_nonsing_inv _ hE, Matrix.mul_one]
  have hnotK : ∀ j, ¬ InvGrp.isW k r j → ¬ TransM.pK k r j := fun j hj hK =>
    hj ⟨hK.1, by have := hK.2; omega⟩
  have hnotKl : ¬ TransM.pK k r (wI k r (Fin.last k)) := fun hK => by
    have := hK.2; simp [wI] at this
  refine ⟨E * PU * E⁻¹, ⟨⟨hG.mul_mem _ (hG.mul_mem _ hEG _ hPUG) _ hEiG, fun a => ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hEifix _ (InvGrp.not_isW_eI a),
      TransM.Qm_fix_off U _ (hnotK _ (InvGrp.not_isW_eI a)), hEfix _ (InvGrp.not_isW_eI a)]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hEifix _ (InvGrp.not_isW_esI a),
      TransM.Qm_fix_off U _ (hnotK _ (InvGrp.not_isW_esI a)), hEfix _ (InvGrp.not_isW_esI a)]
  · conv_lhs => rw [hzE]
    rw [Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hEE, TransM.Qm_fix_off U _ hnotKl, ← hzE]
  · show (E * PU * E⁻¹) *ᵥ (E *ᵥ bvec (wI k r 0)) = E *ᵥ bvec (wI k r 0)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hEE, TransM.Qm_fix_vec U _ hUw]
  · have hinv : (E * PU * E⁻¹)⁻¹ = E * TransM.Qm Uᴴ 1 * E⁻¹ := by
      apply Matrix.inv_eq_left_inv
      simp only [Matrix.mul_assoc, hc]
      rw [← Matrix.mul_assoc (TransM.Qm Uᴴ 1) PU, hPUs, Matrix.one_mul, Matrix.mul_nonsing_inv _ hE]
    have hgb : gbar k r γ y = E * x.map (starRingEnd ℂ) * E⁻¹ := rfl
    show (gbar k r γ y)⁻¹ = _
    rw [hinv, hgb]
    apply Matrix.inv_eq_right_inv
    rw [hyx]
    simp only [Matrix.mul_assoc, hc]
    rw [← Matrix.mul_assoc (x.map (starRingEnd ℂ)) PU, ← Matrix.mul_assoc (x.map (starRingEnd ℂ) * PU) x, hkey,
      ← Matrix.mul_assoc PU, hPUs', Matrix.one_mul, Matrix.mul_nonsing_inv _ hE]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.LabApply
section
open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.SymA

variable {k r : ℕ}

lemma cont_lmul (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finsetSum _ fun l _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply l))

def sandM (A B : Mat k r) (x : Mt k r) : Mt k r := A * Matrix.of x * B

lemma cont_sand (A B : Mat k r) : Continuous (sandM (k := k) (r := r) A B) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [sandM, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finsetSum _ fun m _ => (continuous_finsetSum _ fun l _ =>
    continuous_const.mul ((continuous_apply m).comp (continuous_apply l))).mul continuous_const

def gb (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (x : Mt k r) : Mt k r := fun i j => gbar k r γ (Matrix.of x) i j

lemma cont_gb (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Continuous (gb (k := k) (r := r) γ) := by
  have h1 := cont_sand (k := k) (r := r) (embWb k r γ)⁻¹ (embWb k r γ)
  have h2 : Continuous (fun x : Mt k r => (fun i j => starRingEnd ℂ (sandM (embWb k r γ)⁻¹ (embWb k r γ) x i j) :
      Mt k r)) :=
    continuous_pi fun i => continuous_pi fun j =>
      Complex.continuous_conj.comp ((continuous_apply j).comp ((continuous_apply i).comp h1))
  exact (cont_sand (k := k) (r := r) (embWb k r γ) (embWb k r γ)⁻¹).comp h2

def mEquiv {α : Type*} [MeasurableSpace α] (f g : α → α) (hf : Measurable f) (hg : Measurable g)
    (h1 : Function.LeftInverse g f) (h2 : Function.RightInverse g f) : α ≃ᵐ α :=
  { toFun := f, invFun := g, left_inv := h1, right_inv := h2, measurable_toFun := hf, measurable_invFun := hg }

lemma sfin {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

def Sab (a b : Mat k r) (p : SS k r) : SS k r :=
  ((lmulM a p.1.1, conjM a p.1.2), (lmulM b p.2.1, conjM b p.2.2))

lemma meas_Sab (a b : Mat k r) : Measurable (Sab (k := k) (r := r) a b) :=
  (((cont_lmul a).measurable.comp (measurable_fst.comp measurable_fst)).prodMk
    ((cont_sand a a⁻¹).measurable.comp (measurable_snd.comp measurable_fst))).prodMk
    (((cont_lmul b).measurable.comp (measurable_fst.comp measurable_snd)).prodMk
    ((cont_sand b b⁻¹).measurable.comp (measurable_snd.comp measurable_snd)))

lemma Sab_inv {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det) (p : SS k r) :
    Sab a⁻¹ b⁻¹ (Sab a b p) = p := by
  have l : ∀ c : Mat k r, IsUnit c.det → ∀ x : Mt k r, lmulM c⁻¹ (lmulM c x) = x := by
    intro c hc x
    exact Matrix.nonsing_inv_mul_cancel_left (A := c) (Matrix.of x) hc
  have m : ∀ c : Mat k r, IsUnit c.det → ∀ x : Mt k r, conjM c⁻¹ (conjM c x) = x := by
    intro c hc x
    show c⁻¹ * (c * Matrix.of x * c⁻¹) * c⁻¹⁻¹ = Matrix.of x
    rw [Matrix.nonsing_inv_nonsing_inv _ hc]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hc, Matrix.nonsing_inv_mul _ hc,
      Matrix.mul_one]
  simp only [Sab, l a ha, l b hb, m a ha, m b hb]

lemma emb_Sab {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det) : MeasurableEmbedding (Sab a b) := by
  have ha' : IsUnit a⁻¹.det := Matrix.isUnit_nonsing_inv_det _ ha
  have hb' : IsUnit b⁻¹.det := Matrix.isUnit_nonsing_inv_det _ hb
  refine (mEquiv (Sab a b) (Sab a⁻¹ b⁻¹) (meas_Sab a b) (meas_Sab _ _) (Sab_inv ha hb) ?_).measurableEmbedding
  intro p
  have := Sab_inv ha' hb' p
  rwa [Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.nonsing_inv_nonsing_inv _ hb] at this

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

lemma mp_Sab (D : RealPlaceData k r Wp Wq) (hCI : ConjInv D) {a b : Mat k r} (ha : a ∈ UWset k r D.z)
    (hb : b ∈ UWset k r D.z') : MeasurePreserving (Sab a b) D.μSS D.μSS := by
  have := sfin D.haarW; have := sfin D.haarN; have := sfin D.haarW'
  have m1 : MeasurePreserving (lmulM a) D.μW D.μW := ⟨(cont_lmul a).measurable, D.haarW.left a ha⟩
  have m2 : MeasurePreserving (conjM a) D.μN D.μN := ⟨(cont_sand a a⁻¹).measurable, hCI a (Or.inl ha)⟩
  have m3 : MeasurePreserving (lmulM b) D.μW' D.μW' := ⟨(cont_lmul b).measurable, D.haarW'.left b hb⟩
  have m4 : MeasurePreserving (conjM b) D.μN D.μN := ⟨(cont_sand b b⁻¹).measurable, hCI b (Or.inr hb)⟩
  exact (m1.prod m2).prod (m3.prod m4)

lemma ae_in (D : RealPlaceData k r Wp Wq) : ∀ᵐ p ∂D.μSS, D.inSS p := by
  have := sfin D.haarW; have := sfin D.haarN; have := sfin D.haarW'
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ UWset k r D.z := ae_iff.2 (measure_mono_null (fun x hx => hx) D.haarW.conc)
  have hN : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Nset k r := ae_iff.2 (measure_mono_null (fun x hx => hx) D.haarN.conc)
  have hW' : ∀ᵐ x ∂D.μW', Matrix.of x ∈ UWset k r D.z' :=
    ae_iff.2 (measure_mono_null (fun x hx => hx) D.haarW'.conc)
  have A1 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.1 ∈ UWset k r D.z :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae hW)
  have A2 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  have A3 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.1 ∈ UWset k r D.z' :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae hW')
  have A4 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  filter_upwards [A1, A2, A3, A4] with p h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩

section lie

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def piLIE (z : Fin (2 * r + k + 1) → ℂ) (π : Mat k r → (V →L[ℂ] V)) (hrep : IsCRepOn (UWset k r z) π)
    (hu : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) (a : Mat k r) (ha : a ∈ UWset k r z) : V ≃ₗᵢ[ℂ] V where
  toLinearEquiv := LinearEquiv.ofLinear (π a).toLinearMap (π a⁻¹).toLinearMap
    (LinearMap.ext fun v => by
      change ((π a).comp (π a⁻¹)) v = v
      rw [← hrep.2 a ha _ (uw_inv ha), Matrix.mul_nonsing_inv _ (isUnit_of_uh ha.1), hrep.1]
      rfl)
    (LinearMap.ext fun v => by
      change ((π a⁻¹).comp (π a)) v = v
      rw [← hrep.2 _ (uw_inv ha) a ha, Matrix.nonsing_inv_mul _ (isUnit_of_uh ha.1), hrep.1]
      rfl)
  norm_map' := hu a ha

end lie

def ph (D : RealPlaceData k r Wp Wq) (p : SS k r) : ℂ :=
  psi k r D.z cStd (Matrix.of p.1.2) * star (psi k r D.z' cStd (Matrix.of p.2.2))

lemma JF_eq (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    JF D F g = ∫ p, ph D p • rho D p F g ∂D.μSS := rfl

lemma ph_Sab (D : RealPlaceData k r Wp Wq) {a b : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z')
    (p : SS k r) : ph D (Sab a b p) = ph D p := by
  show psi k r D.z cStd (a * Matrix.of p.1.2 * a⁻¹) * star (psi k r D.z' cStd (b * Matrix.of p.2.2 * b⁻¹)) = _
  rw [psi_conj _ ha, psi_conj _ hb]
  rfl

lemma sgs_Sab {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det) (p : SS k r) (g : Mat k r) :
    sgs (Sab a b p) g = sgs p (a⁻¹ * g * b) := by
  show (a * Matrix.of p.1.1)⁻¹ * (a * Matrix.of p.1.2 * a⁻¹)⁻¹ * g * (b * Matrix.of p.2.2 * b⁻¹) *
      (b * Matrix.of p.2.1) = (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (a⁻¹ * g * b) * Matrix.of p.2.2 *
      Matrix.of p.2.1
  simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul_cancel_left _ _ ha, Matrix.nonsing_inv_mul_cancel_left _ _ hb]

lemma rho_Sab (D : RealPlaceData k r Wp Wq) {a b : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z')
    {p : SS k r} (hp : D.inSS p) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    rho D (Sab a b p) F g = (D.π a).comp ((rho D p F (a⁻¹ * g * b)).comp (D.π' b⁻¹)) := by
  show (D.π (a * Matrix.of p.1.1)).comp ((F (sgs (Sab a b p) g)).comp (D.π' (b * Matrix.of p.2.1)⁻¹)) = _
  rw [sgs_Sab (isUnit_of_uh ha.1) (isUnit_of_uh hb.1), D.π_rep.2 a ha _ hp.1, Matrix.mul_inv_rev,
    D.π'_rep.2 _ (uw_inv hp.2.2.1) _ (uw_inv hb)]
  simp only [rho, ContinuousLinearMap.comp_assoc]

def Lab (D : RealPlaceData k r Wp Wq) {a b : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z') :
    (Wq →L[ℂ] Wp) ≃L[ℂ] (Wq →L[ℂ] Wp) :=
  ContinuousLinearEquiv.arrowCongr (piLIE D.z' D.π' D.π'_rep D.π'_unitary b hb).toContinuousLinearEquiv
    (piLIE D.z D.π D.π_rep D.π_unitary a ha).toContinuousLinearEquiv

lemma Lab_apply (D : RealPlaceData k r Wp Wq) {a b : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z')
    (X : Wq →L[ℂ] Wp) : Lab D ha hb X = (D.π a).comp (X.comp (D.π' b⁻¹)) :=
  ContinuousLinearMap.ext fun _ => rfl

lemma norm_Lab (D : RealPlaceData k r Wp Wq) {a b : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z')
    (X : Wq →L[ℂ] Wp) : ‖Lab D ha hb X‖ = ‖X‖ := by
  have e : Lab D ha hb X = ((piLIE D.z D.π D.π_rep D.π_unitary a ha : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp).comp
      (X.comp ((piLIE D.z' D.π' D.π'_rep D.π'_unitary b hb).symm : Wq →L[ℂ] Wq)) :=
    ContinuousLinearMap.ext fun _ => rfl
  rw [e, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

lemma J_equiv (D : RealPlaceData k r Wp Wq) (hCI : ConjInv D) {a b : Mat k r} (ha : a ∈ UWset k r D.z)
    (hb : b ∈ UWset k r D.z') (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    JF D F g = Lab D ha hb (JF D F (a⁻¹ * g * b)) := by
  rw [JF_eq, JF_eq, ← (mp_Sab D hCI ha hb).integral_comp (emb_Sab (isUnit_of_uh ha.1) (isUnit_of_uh hb.1)),
    ← ContinuousLinearEquiv.integral_comp_comm]
  refine integral_congr_ae ?_
  filter_upwards [ae_in D] with p hp
  rw [ph_Sab D ha hb, rho_Sab D ha hb hp, map_smul, Lab_apply]

lemma E_equiv (D : RealPlaceData k r Wp Wq) (hCI : ConjInv D) {a b : Mat k r} (ha : a ∈ UWset k r D.z)
    (hb : b ∈ UWset k r D.z') (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    ∫⁻ p, ‖rho D p F g‖ₑ ∂D.μSS = ∫⁻ p, ‖rho D p F (a⁻¹ * g * b)‖ₑ ∂D.μSS := by
  rw [← (mp_Sab D hCI ha hb).lintegral_comp_emb (emb_Sab (isUnit_of_uh ha.1) (isUnit_of_uh hb.1))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_in D] with p hp
  have h := norm_Lab D ha hb (rho D p F (a⁻¹ * g * b))
  rw [Lab_apply] at h
  rw [rho_Sab D ha hb hp, enorm_eq_nnnorm, enorm_eq_nnnorm,
    show ‖(D.π a).comp ((rho D p F (a⁻¹ * g * b)).comp (D.π' b⁻¹))‖₊ = ‖rho D p F (a⁻¹ * g * b)‖₊ from NNReal.eq h]

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymB
end
end

