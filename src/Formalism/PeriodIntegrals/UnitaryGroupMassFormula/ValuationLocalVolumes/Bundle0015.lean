module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0009

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.AbsVDetBigL
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolV

open Formalism.L2.SG.Pf.NcVal Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem absV_pow (x : Fv F v) (n : ℕ) : absV v (x ^ n) = absV v x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, VolOrdW.absV_one]
  | succ n ih => rw [pow_succ, VolOrdW.absV_mul, ih, pow_succ]

theorem meas_image (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → Fv F v ⊗[F] E))
    [μ.IsAddHaarMeasure] (f : (ι → Fv F v ⊗[F] E) →ₗ[Fv F v] (ι → Fv F v ⊗[F] E))
    (hf : LinearMap.det f ≠ 0) (S : Set (ι → Fv F v ⊗[F] E)) (hS : MeasurableSet S) :
    μ (f '' S) = ENNReal.ofReal (absV v (LinearMap.det f)) * μ S := by
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.locallyCompact_Fv v
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  let b := Module.finBasis (Fv F v) (Fv F v ⊗[F] E)
  let eR : (Fv F v ⊗[F] E) ≃L[Fv F v] (Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    { b.equivFun with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eR.toHomeomorph.secondCountableTopology
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (ι → Fv F v ⊗[F] E) := Pi.borelSpace
  let e0 : (ι → Fv F v ⊗[F] E) ≃ₗ[Fv F v]
      (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    (LinearEquiv.piCongrRight fun _ : ι => b.equivFun).trans
      (LinearEquiv.curry (Fv F v) (Fv F v) ι (Fin _)).symm
  let eV : (ι → Fv F v ⊗[F] E) ≃L[Fv F v]
      (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    { e0 with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }
  have hLM := PI.NglqJacSplitW.linModulusV_of
    (PI.NglqJacSplitW.linModulus_of PI.NglqJacSplitW.diagonal_one_jacobian)
  rw [hLM (Fv F v) (ι → Fv F v ⊗[F] E) (ι × Fin _) ⟨eV⟩ f hf μ inferInstance S hS,
    PI.UnitaryGroupMassFormula.LocJacTyp.BM.modF_Fv v _ hf]
  rfl

section Big

variable (r : ℕ)

def famL (g : Fv F v) (θ : Fv F v ⊗[F] E) (p : Fin (r + 1) × Fin (r + 1)) :
    (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) :=
  if p.1 < p.2 then g • LinearMap.id else if p.1 = p.2 then aL v g θ else LinearMap.id

def bigL (g : Fv F v) (θ : Fv F v ⊗[F] E) :
    (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  LinearMap.pi fun p => (famL v r g θ p).comp (LinearMap.proj p)

theorem det_famL_mul (hfin : Module.finrank F E = 2) (g : Fv F v) (θ Δ : Fv F v ⊗[F] E)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0)
    (hΔ0 : Δ ≠ 0) (p : Fin (r + 1) × Fin (r + 1)) :
    LinearMap.det (famL v r g θ p) * LinearMap.det (famL v r g θ p.swap) = g ^ 2 := by
  have hr : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hfin
  have hs : LinearMap.det (g • (LinearMap.id : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E))) = g ^ 2 := by
    rw [LinearMap.det_smul, LinearMap.det_id, hr, mul_one]
  have ha := det_aL v hfin g θ Δ hθ hΔ hΔ0
  obtain ⟨i, j⟩ := p
  simp only [Prod.swap_prod_mk]
  rcases lt_trichotomy i j with h | h | h
  · have h1 : ¬ j < i := not_lt.2 h.le
    have h2 : j ≠ i := h.ne'
    simp only [famL, if_pos h, if_neg h1, if_neg h2, hs, LinearMap.det_id, mul_one]
  · subst h
    simp only [famL, lt_irrefl, if_false, if_true, ha, sq]
  · have h1 : ¬ i < j := not_lt.2 h.le
    have h2 : i ≠ j := h.ne'
    simp only [famL, if_pos h, if_neg h1, if_neg h2, hs, LinearMap.det_id, one_mul]

theorem det_bigL_sq (hfin : Module.finrank F E = 2) (g : Fv F v) (θ Δ : Fv F v ⊗[F] E)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0)
    (hΔ0 : Δ ≠ 0) : LinearMap.det (bigL v r g θ) ^ 2 = (g ^ 2) ^ ((r + 1) ^ 2) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [bigL, LinearMap.det_pi, sq]
  have e : ∏ p : Fin (r + 1) × Fin (r + 1), LinearMap.det (famL v r g θ p.swap) =
      ∏ p : Fin (r + 1) × Fin (r + 1), LinearMap.det (famL v r g θ p) :=
    Fintype.prod_equiv (Equiv.prodComm _ _) _ _ (fun _ => rfl)
  conv_lhs => arg 2; rw [← e]
  rw [← Finset.prod_mul_distrib]
  simp only [det_famL_mul v r hfin g θ Δ hθ hΔ hΔ0, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, sq]

theorem absV_det_bigL (hfin : Module.finrank F E = 2) {g : ℕ} (hg0 : g ≠ 0)
    (hg : absV v (g : Fv F v) = (g : ℝ)⁻¹) (θ Δ : Fv F v ⊗[F] E)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0)
    (hΔ0 : Δ ≠ 0) :
    LinearMap.det (bigL v r (g : Fv F v) θ) ≠ 0 ∧
      absV v (LinearMap.det (bigL v r (g : Fv F v) θ)) = (g : ℝ)⁻¹ ^ ((r + 1) ^ 2) := by
  have hgv : (g : Fv F v) ≠ 0 := VolTU.natCast_ne_zero v hg0
  have h2 := det_bigL_sq v r hfin (g : Fv F v) θ Δ hθ hΔ hΔ0
  have hD : LinearMap.det (bigL v r (g : Fv F v) θ) ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at h2
    exact (pow_ne_zero _ (pow_ne_zero _ hgv)) h2.symm
  refine ⟨hD, ?_⟩
  have h3 := congrArg (absV v) h2
  rw [absV_pow, absV_pow, absV_pow, hg] at h3
  have hpos := (VolOrdW.absV_pos v hD).le
  have hgpos : (0 : ℝ) ≤ (g : ℝ)⁻¹ ^ ((r + 1) ^ 2) := by positivity
  refine (pow_left_inj₀ hpos hgpos two_ne_zero).1 ?_
  rw [h3, ← pow_mul, ← pow_mul, mul_comm]

end Big

end Formalism.L2.SG.Pf.NcVal.VolV
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.BaseLatticeLeSecondIsotropic
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

def OmVDdLoc : Prop :=
  ∀ (v : PlX X) (a : Fin D.R.rS),
    (∀ x ∈ (aaD D a)⁻¹, sc (E := X.B.I.E) v (alp v D.R.rS a.castSucc) *
      inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) ∈ OEv (E := X.B.I.E) v) ∧
    (∀ x ∈ aaD D a, sc (E := X.B.I.E) v (alp v D.R.rS a.castSucc)⁻¹ *
      inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) ∈ OEv (E := X.B.I.E) v)

def Pm (v : PlX X) (c : Fv X.B.I.F v) (w : (VS D).V) : Submodule (𝓞 D.host.E) (VS D).V where
  carrier := {y | sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((VS D).hT w y)) ∈
    OEv (E := X.B.I.E) v}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero, mul_zero]; exact Submodule.zero_mem _
  add_mem' := by
    intro y y' hy hy'
    simp only [Set.mem_ofPred_eq, map_add (f := _), mul_add] at *
    exact Submodule.add_mem _ hy hy'
  smul_mem' := by
    intro o y hy
    simp only [Set.mem_ofPred_eq] at *
    rw [← algebraMap_smul D.host.E o y, map_smul, smul_eq_mul, map_mul, map_mul, mul_left_comm]
    exact oev_mul v (incl_mem v (⟨X.ιE.symm (o : D.host.E),
      (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom⟩ : 𝓞 X.B.I.E)) hy

theorem pm_iff (v : PlX X) (c : Fv X.B.I.F v) (w y : (VS D).V) : y ∈ Pm X v c w ↔
    sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((VS D).hT w y)) ∈ OEv (E := X.B.I.E) v :=
  Iff.rfl

theorem pm_zero (v : PlX X) (c : Fv X.B.I.F v) (w y : (VS D).V) (h : (VS D).hT w y = 0) : y ∈ Pm X v c w := by
  rw [pm_iff, h, map_zero, map_zero, mul_zero]; exact Submodule.zero_mem _

theorem hT_smul_right (w y : (VS D).V) (x : D.host.E) : (VS D).hT w (x • y) = x * (VS D).hT w y := by
  rw [map_smul, smul_eq_mul]

theorem base_lattice_le_first_isotropic (hD : OmVDdLoc X) (v : PlX X) (a : Fin D.R.rS) :
    (VS D).L0 ≤ Pm X v (alp v D.R.rS a.castSucc) (X.eX a) := by
  rw [X.Lam_split]
  refine sup_le (sup_le ?_ ?_) ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, x, _, rfl⟩
    exact pm_zero X v _ _ _ (by rw [hT_smul_right, X.ee, mul_zero])
  · intro y hy
    exact pm_zero X v _ _ _ (X.Lb_perp y hy a).1
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, x, hx, rfl⟩
    refine (pm_iff X v _ _ _).2 ?_
    rw [hT_smul_right, X.ef]
    by_cases hab : a = b
    · subst hab; rw [if_pos rfl, mul_one]; exact (hD v a).1 x hx
    · rw [if_neg hab, mul_zero, map_zero, map_zero, mul_zero]; exact Submodule.zero_mem _

theorem base_lattice_le_second_isotropic (hD : OmVDdLoc X) (v : PlX X) (a : Fin D.R.rS) :
    (VS D).L0 ≤ Pm X v (alp v D.R.rS a.castSucc)⁻¹ (X.fY a) := by
  rw [X.Lam_split]
  refine sup_le (sup_le ?_ ?_) ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, x, hx, rfl⟩
    refine (pm_iff X v _ _ _).2 ?_
    rw [hT_smul_right, ← (VS D).herm.eq (X.eX b) (X.fY a), X.ef]
    by_cases hab : b = a
    · subst hab; rw [if_pos rfl, map_one, mul_one]; exact (hD v b).2 x hx
    · rw [if_neg hab, map_zero, mul_zero, map_zero, map_zero, mul_zero]; exact Submodule.zero_mem _
  · intro y hy
    exact pm_zero X v _ _ _ (X.Lb_perp y hy a).2
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, x, _, rfl⟩
    exact pm_zero X v _ _ _ (by rw [hT_smul_right, X.ff, mul_zero])

theorem crd_of_L (l : Fin X.B.I.n → X.B.I.E) (hl : l ∈ X.B.I.L) :
    ∃ y ∈ (VS D).L0, crdOf X.B.I X.ιE X.bas y = l := by
  refine ⟨∑ i, X.ιE (l i) • X.bas i, (X.L_eq l).1 hl, ?_⟩
  funext j
  have h : X.bas.repr (∑ i, X.ιE (l i) • X.bas i) j = X.ιE (l j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [crdOf]
  rw [h, RingEquiv.symm_apply_apply]

theorem hform_star (l x : Fin X.B.I.n → X.B.I.E) :
    star (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l x) = Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x l := by
  have herm_entry : ∀ i j, star (X.B.I.J i j) = X.B.I.J j i := fun i j => by
    have := congrFun (congrFun X.B.I.J_herm j) i
    simpa [Formalism.UG.IsHerm, Formalism.UG.cT, starRingEnd_apply] using this
  unfold Formalism.UG.hform
  rw [Finset.sum_comm, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [starRingEnd_apply, star_mul, star_star]
  rw [herm_entry]
  ring

theorem pair_mem (v : PlX X) (s : Fv X.B.I.F v) (w : (VS D).V) (l : Fin X.B.I.n → X.B.I.E) (hl : l ∈ X.B.I.L)
    (hP : (VS D).L0 ≤ Pm X v s w) :
    hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) l)
      (sc (E := X.B.I.E) v s • ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas w)) ∈ OEv (E := X.B.I.E) v := by
  obtain ⟨y, hy, rfl⟩ := crd_of_L X l hl
  rw [hR_smulE_right]
  have h1 : hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas y))
      (ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas w)) =
      inclR (F := X.B.I.F) (Fv X.B.I.F v) (hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas y) (crdOf X.B.I X.ιE X.bas w)) :=
    hR_ratTup (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J ![crdOf X.B.I X.ιE X.bas y, crdOf X.B.I X.ιE X.bas w] 0 1
  have h2 : hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas y) (crdOf X.B.I X.ιE X.bas w) =
      X.B.I.cm.sig (X.ιE.symm ((VS D).hT w y)) := by
    rw [← hE_crdOf]
    exact (hform_star X _ _).symm
  rw [h1, h2, ← sigR_inclR]
  have hsc : sc (E := X.B.I.E) v s = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv X.B.I.F v) X.B.I.cm.sig (sc (E := X.B.I.E) v s) :=
    (sigR_tmul_one (Fv X.B.I.F v) X.B.I.cm.sig s).symm
  rw [hsc, ← map_mul]
  exact sigR_oev X.B.I.cm.sig v ((pm_iff X v s w y).1 (hP hy))

theorem yTup_eq (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) :
    yTup X u' v i = sc (E := X.B.I.E) v (scl X v i) •
      ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas (hv X u' i)) := by
  rw [← tupH_eq]; rfl

theorem omVMemEF_of (hD : OmVDdLoc X) : OmVMemEF X u' := by
  intro v i hi
  have hpair : ∀ l ∈ X.B.I.L, hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) l)
      (yTup X u' v i) ∈ OEv (E := X.B.I.E) v := by
    intro l hl
    rw [yTup_eq]
    refine Fin.addCases (fun j hj => ?_) (fun b _ => ?_) i hi
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨a, rfl⟩ | rfl
      · have hs : scl X v (Fin.castAdd D.R.rS a.castSucc) = alp v D.R.rS a.castSucc := by
          simp only [scl, Fin.append_left]
        have hw : hv X u' (Fin.castAdd D.R.rS a.castSucc) = X.eX a := by
          simp only [hv, Fin.append_left, Fin.snoc_castSucc]
        rw [hs, hw]
        exact pair_mem X v _ _ l hl (base_lattice_le_first_isotropic X hD v a)
      · exact absurd rfl hj
    · have hs : scl X v (Fin.natAdd (D.R.rS + 1) b) = (alp v D.R.rS b.castSucc)⁻¹ := by
        simp only [scl, Fin.append_right]
      have hw : hv X u' (Fin.natAdd (D.R.rS + 1) b) = X.fY b := by
        simp only [hv, Fin.append_right]
      rw [hs, hw]
      exact pair_mem X v _ _ l hl (base_lattice_le_second_isotropic X hD v b)
  refine ((omVSD_of X (omVSDBwd_holds X)) v _).2 fun x hx => ?_
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact hpair l hl
  | zero => rw [OmW.hR_zero_left]; exact Submodule.zero_mem _
  | add x x' _ _ h1 h2 => rw [OmW.hR_add_left]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    change hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J ((c : Fv X.B.I.F v) • x) _ ∈ _
    rw [OmW.hR_smul_left]; exact oev_smul v h

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixCorankOne
section
noncomputable section

namespace PI.OmVg

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Matrix PI.OmLocU Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

theorem natCast_val_lt {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t : ℕ)
    (ht : ((t : 𝓞 F)) ∈ v.asIdeal) : Valued.v ((t : ℕ) : Fv F v) < 1 := by
  have h1 : ((t : ℕ) : Fv F v) = algebraMap (𝓞 F) (Fv F v) (t : 𝓞 F) := by simp
  rw [h1]
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (t : 𝓞 F)).trans_lt ?_
  erw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).2 ht

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem localGramMatrixFrame_apply (v : PlX X) (a b : Fin (D.R.rS + 1 + D.R.rS)) :
    localGramMatrixFrame X u' v a b = inclR (Fv X.B.I.F v) (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) a b) := rfl

theorem negT_mem (v : PlX X) (hv : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) {ϖ : Fv X.B.I.F v}
    (hϖ : IsUnif v ϖ) : inclR (Fv X.B.I.F v) (-((Tw u' : ℕ) : X.B.I.E)) ∈ PO (E := X.B.I.E) v ϖ := by
  obtain ⟨h0, -, -⟩ := unif_spec v ϖ hϖ
  have hm := natCast_div_mem v (Tw u') hv hϖ
  refine ⟨sc (E := X.B.I.E) v (-(((Tw u' : ℕ) : Fv X.B.I.F v) * ϖ⁻¹)), ?_, ?_⟩
  · simpa using sc_mul_mem_oEv v (neg_mem hm) (Orb.oSub (E := X.B.I.E) v).1
  · rw [sc_mul]
    have e : ϖ * -(((Tw u' : ℕ) : Fv X.B.I.F v) * ϖ⁻¹) = -((Tw u' : ℕ) : Fv X.B.I.F v) := by field_simp
    rw [e, show sc (E := X.B.I.E) v (-((Tw u' : ℕ) : Fv X.B.I.F v)) =
      algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (-((Tw u' : ℕ) : Fv X.B.I.F v)) from rfl,
      map_neg, map_neg, map_natCast, map_natCast]

theorem local_gram_matrix_corank_one (v : PlX X) (hv : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) {ϖ : Fv X.B.I.F v}
    (hϖ : IsUnif v ϖ) : GramCor v ϖ (localGramMatrixFrame X u' v) := by
  have hN := negT_mem X u' v hv hϖ
  have h0 : (0 : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ∈ PO (E := X.B.I.E) v ϖ :=
    ⟨0, Orb.oev_zero v, by rw [mul_zero]⟩
  refine ⟨iz, fun j => ?_, fun j => ?_, ?_⟩
  · rw [localGramMatrixFrame_apply, gramE_apply, piv_iz]
    split_ifs with h
    · rw [cD_iz]; exact hN
    · rw [map_zero]; exact h0
  · rw [localGramMatrixFrame_apply, gramE_apply]
    split_ifs with h
    · rw [eq_iz_of_piv h, cD_iz]; exact hN
    · rw [map_zero]; exact h0
  · set P := (Function.Involutive.toPerm _ (piv_invol D.R.rS)).permMatrix X.B.I.E with hPdef
    have hM : localGramMatrixFrame X u' v + Matrix.single iz iz 1 = (diagonal (diagonalShiftOneMinus X u') * P).map (inclR (Fv X.B.I.F v)) := by
      ext a b
      rw [Matrix.add_apply, localGramMatrixFrame_apply, gramE_apply, Matrix.map_apply, diagonal_mul, Matrix.single_apply]
      simp only [hPdef, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
        Option.some.injEq, Function.Involutive.coe_toPerm]
      by_cases ha : a = iz
      · subst ha
        rw [piv_iz]
        by_cases hb : iz = b
        · subst hb
          rw [cD_iz]
          simp [diagonalShiftOneMinus, iz]
          ring
        · simp [hb]
      · have hav : a.val ≠ D.R.rS := fun e => ha (Fin.ext e)
        have h1 : ¬ (iz = a ∧ iz = b) := fun h => ha h.1.symm
        simp [cD, diagonalShiftOneMinus, hav, h1]
    obtain ⟨s, hs, hPd⟩ : ∃ s : ℤ, s * s = 1 ∧ P.det = (s : X.B.I.E) :=
      ⟨((Equiv.Perm.sign (Function.Involutive.toPerm _ (piv_invol D.R.rS)) : ℤˣ) : ℤ),
        by rw [← Units.val_mul, Int.units_mul_self, Units.val_one], by rw [hPdef, det_permutation]⟩
    have hdet : (localGramMatrixFrame X u' v + Matrix.single iz iz 1).det =
        inclR (Fv X.B.I.F v) ((1 - ((Tw u' : ℕ) : X.B.I.E)) * (s : X.B.I.E)) := by
      rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_mul, det_diagonal, prod_diagonalShiftOneMinus, hPd]
    set t : Fv X.B.I.F v := 1 - ((Tw u' : ℕ) : Fv X.B.I.F v) with htdef
    have hv1 : Valued.v t = 1 := Valuation.map_one_sub_of_lt _ (natCast_val_lt v _ hv)
    have ht0 : t ≠ 0 := fun h => by rw [h, map_zero] at hv1; exact zero_ne_one hv1
    have hti : t⁻¹ ∈ v.adicCompletionIntegers X.B.I.F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1, inv_one]
    refine ⟨sc (E := X.B.I.E) v t⁻¹ * inclR (Fv X.B.I.F v) (((s : 𝓞 X.B.I.E)) : X.B.I.E),
      sc_mul_mem_oEv v hti (inclR_mem_OEv X v _), ?_⟩
    rw [hdet]
    have e1 : inclR (Fv X.B.I.F v) (1 - ((Tw u' : ℕ) : X.B.I.E)) = sc (E := X.B.I.E) v t := by
      rw [htdef, show sc (E := X.B.I.E) v (1 - ((Tw u' : ℕ) : Fv X.B.I.F v)) =
        algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (1 - ((Tw u' : ℕ) : Fv X.B.I.F v)) from rfl,
        map_sub, map_sub, map_one, map_one, map_natCast, map_natCast]
    have e2 : (((s : 𝓞 X.B.I.E)) : X.B.I.E) = (s : X.B.I.E) := by simp
    rw [e2, map_mul, e1]
    calc sc (E := X.B.I.E) v t * inclR (Fv X.B.I.F v) (s : X.B.I.E) *
          (sc (E := X.B.I.E) v t⁻¹ * inclR (Fv X.B.I.F v) (s : X.B.I.E))
        = (sc (E := X.B.I.E) v t * sc (E := X.B.I.E) v t⁻¹) * inclR (Fv X.B.I.F v) ((s : X.B.I.E) * s) := by
          rw [map_mul]; ring
      _ = 1 := by
          rw [sc_mul, mul_inv_cancel₀ ht0, sc_one, ← Int.cast_mul, hs, Int.cast_one, map_one, mul_one]

end PI.OmVg
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfRedX
section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVBadT_of_red (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hExt : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ExtP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hLI : ∀ v : PlX X, LeftInvO X.B.I.cm.sig X.B.I.J ψ v (n := X.B.I.n) (D.R.rS + 1 + D.R.rS))
    (hRed : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      RedP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hFI : FFInertB) (hFS : FFSplitB) :
    OmVBadT X u' ψ :=
  omVBadT_of_std_lat_gram X u' ψ hStd hLat hGram hExt hLI (fun v hv => clsP_of _ _ _ _ _ _ _ (hRed v hv) hFI hFS)

end PI.OmVd
end
end

