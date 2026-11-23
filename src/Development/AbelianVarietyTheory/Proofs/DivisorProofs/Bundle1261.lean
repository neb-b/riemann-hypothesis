module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0085
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonCharacterDetEqOneInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertDetChr

open GlobalTheory.LFun GlobalTheory.Doubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_det_sub_one {n : ℕ} (v : Pl (F := F)) (t : GL (Fin n) (AE F E))
    (ht : At (evFin F v) ((t : Matrix (Fin n) (Fin n) (AE F E)) - 1)) :
    At (evFin F v) (((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) - 1) := by
  intro u hu
  have h := ht u hu
  set c := algebraMap (AF F) (AE F E) u with hc
  let I : Ideal (AE F E) := (Submodule.span (AE F E) {c}).annihilator
  have hmem : ∀ x : AE F E, x ∈ I ↔ c * x = 0 := fun x => by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_comm]
  have hent : ∀ i j, (t : Matrix (Fin n) (Fin n) (AE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j ∈ I :=
    fun i j => by
      rw [hmem]
      have := congrFun (congrFun h i) j
      simpa [Matrix.sub_apply, Algebra.smul_def, hc] using this
  have hq : (Ideal.Quotient.mk I).mapMatrix (t : Matrix (Fin n) (Fin n) (AE F E)) =
      (Ideal.Quotient.mk I).mapMatrix (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    ext i j
    exact Ideal.Quotient.eq.2 (hent i j)
  have hd := congrArg Matrix.det hq
  rw [← RingHom.map_det, ← RingHom.map_det, Matrix.det_one] at hd
  have := (hmem _).1 (Ideal.Quotient.eq.1 hd)
  rw [Algebra.smul_def, Matrix.GeneralLinearGroup.val_det_apply]
  exact this

theorem compFin_algebraMap (u : Pl (F := F)) (a : AF F) :
    compFin F E u (algebraMap (AF F) (AE F E) a) = algebraMap (Fv F u) (Fv F u ⊗[F] E) (evFin F u a) := by
  simp [compFin, Algebra.TensorProduct.algebraMap_apply]

theorem compInf_algebraMap (w : InfinitePlace F) (a : AF F) :
    compInf F E w (algebraMap (AF F) (AE F E) a) = algebraMap w.Completion (w.Completion ⊗[F] E) (evInf F w a) := by
  simp [compInf, Algebra.TensorProduct.algebraMap_apply]

theorem evFin_inFin_self (v : Pl (F := F)) (x : Fv F v) : evFin F v (inFin v x) = x :=
  evalV_singleFin_self v x

theorem evFin_inFin_ne {u v : Pl (F := F)} (h : u ≠ v) (x : Fv F v) : evFin F u (inFin v x) = 0 :=
  evalV_singleFin_ne h x

theorem evInf_inFin (w : InfinitePlace F) (v : Pl (F := F)) (x : Fv F v) : evInf F w (inFin v x) = 0 := by
  show GlobalTheory.AutFunCompare.evW w 0 = 0
  exact map_zero _

theorem at_inFin_one (v : Pl (F := F)) : At (evFin F v) (inFin v (1 : Fv F v)) := by
  intro u hu
  rw [smul_eq_mul]
  refine Prod.ext (mul_zero _) (af_ext fun u' => ?_)
  show evalV F u' (u.2 * singleFin v 1) = evalV F u' 0
  rw [map_mul, map_zero]
  by_cases e : u' = v
  · subst e
    exact mul_eq_zero_of_left hu _
  · rw [evalV_singleFin_ne e, mul_zero]

theorem eq_ideleAt {v : Pl (F := F)} {z : (AE F E)ˣ} (hz : At (evFin F v) ((z : AE F E) - 1)) :
    z = ideleAt F E v (unitFin F E v z) := by
  set e : AF F := inFin v 1
  have key := hz (1 - e) (by rw [map_sub, map_one, evFin_inFin_self, sub_self])
  rw [Algebra.smul_def] at key
  refine idele_ext (fun w => ?_) (fun u => ?_)
  · rw [unitInf_ideleAt]
    refine Units.ext ?_
    have := congrArg (compInf F E w) key
    rw [map_mul, compInf_algebraMap, map_sub, map_one, evInf_inFin, sub_zero, map_one, one_mul, map_zero, map_sub,
      map_one, sub_eq_zero] at this
    exact this
  · by_cases huv : u = v
    · subst huv
      rw [unitFin_ideleAt_self]
    · rw [unitFin_ideleAt_ne huv]
      refine Units.ext ?_
      have := congrArg (compFin F E u) key
      rw [map_mul, compFin_algebraMap, map_sub, map_one, evFin_inFin_ne huv, sub_zero, map_one, one_mul, map_zero,
        map_sub, map_one, sub_eq_zero] at this
      exact this

section Lat

variable {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v)

def piW' : AE F E →+* w.adicCompletion E := (toCompl h).comp (compFin F E v)

theorem piW'_algebraMap (a : AF F) : piW' h (algebraMap (AF F) (AE F E) a) = complMap h (evFin F v a) := by
  rw [piW', RingHom.comp_apply, compFin_algebraMap, Algebra.TensorProduct.algebraMap_apply, toCompl_tmul]
  simp

theorem piW'_inclR (y : E) : piW' h (inclR (F := F) (AF F) y) = algebraMap E _ y := by
  rw [piW', RingHom.comp_apply]
  have : compFin F E v (inclR (F := F) (AF F) y) = (1 : Fv F v) ⊗ₜ[F] y := by
    show Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] y) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
  rw [this, toCompl_tmul, map_one, one_mul]

theorem comp_mem_latAt {d : ℕ} (W : Spc F E d) {z : Fin d → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt W v) :
    piW' h ∘ z ∈ latAt w W.L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, y, hy, rfl⟩ := hz
    have e : piW' h ∘ (a • fun i => inclR (F := F) (AF F) (y i)) =
        (⟨complMap h (evFin F v a), complMap_mem h ha⟩ : Formalism.UG.Ov E w) •
          (fun i => algebraMap E (w.adicCompletion E) (y i)) := by
      funext i
      show piW' h (a • inclR (F := F) (AF F) (y i)) = _
      rw [Algebra.smul_def, map_mul, piW'_algebraMap, piW'_inclR]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
  | zero =>
    convert zero_mem (latAt w W.L) using 1
    funext i; exact map_zero _
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    funext i; exact map_add _ _ _
  | neg x _ hx =>
    convert neg_mem hx using 1
    funext i; exact map_neg _ _

theorem lift_mem_latAt {d : ℕ} (W : Spc F E d) {y : Fin d → E} (hy : y ∈ W.L) :
    (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt W v ∧
      piW' h ∘ (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i)) =
        fun i => algebraMap E (w.adicCompletion E) (y i) := by
  refine ⟨AddSubgroup.subset_closure ⟨_, at_inFin_one v, ?_, y, hy, rfl⟩, ?_⟩
  · rw [evFin_inFin_self]; exact one_mem _
  · funext i
    show piW' h (inFin v (1 : Fv F v) • inclR (F := F) (AF F) (y i)) = _
    rw [Algebra.smul_def, map_mul, piW'_algebraMap, piW'_inclR, evFin_inFin_self, map_one, one_mul]

theorem mulVec_mem_latAt {d : ℕ} (W : Spc F E d) (g : Matrix (Fin d) (Fin d) (AE F E))
    (hg : ∀ z ∈ GlobalTheory.InertSph.latAt W v, g *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ∀ z ∈ latAt w W.L, (piW' h).mapMatrix g *ᵥ z ∈ latAt w W.L := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨h1, h2⟩ := lift_mem_latAt h W hy
    show (piW' h).mapMatrix g *ᵥ (fun i => algebraMap E (w.adicCompletion E) (y i)) ∈ _
    rw [← h2]
    have e : (piW' h).mapMatrix g *ᵥ (piW' h ∘ (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i))) =
        piW' h ∘ (g *ᵥ (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i))) :=
      funext fun i => (RingHom.map_mulVec (piW' h) g _ i).symm
    rw [e]
    exact comp_mem_latAt h W (hg _ h1)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have e : (piW' h).mapMatrix g *ᵥ (c • x) = c • ((piW' h).mapMatrix g *ᵥ x) := by
      funext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Subring.smul_def, mul_left_comm]
    rw [e]
    exact Submodule.smul_mem _ _ hx

theorem valued_eq_one_of_isUnit {c : Formalism.UG.Ov E w} (hc : IsUnit c) : Valued.v (c : w.adicCompletion E) = 1 := by
  obtain ⟨c', hc'⟩ := hc.exists_right_inv
  have h1 : Valued.v (c : w.adicCompletion E) ≤ 1 := c.2
  have h2 : Valued.v (c' : w.adicCompletion E) ≤ 1 := c'.2
  have h3 : Valued.v (c : w.adicCompletion E) * Valued.v (c' : w.adicCompletion E) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, hc']; simp
  refine le_antisymm h1 ?_
  calc (1 : _) = _ := h3.symm
    _ ≤ Valued.v (c : w.adicCompletion E) := mul_le_of_le_one_right' h2

theorem valued_det_eq_one (hw : Formalism.UG.IsInertAt F E v w) {d : ℕ} (W : Spc F E d) (hL : W.L.IsFullLattice E)
    (t : GL (Fin d) (AE F E))
    (ht : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    Valued.v (piW' h (t : Matrix (Fin d) (Fin d) (AE F E)).det) = 1 := by
  set T : GL (Fin d) (w.adicCompletion E) := Formalism.UG.bc (piW' h) t with hT
  have hT1 : (T : Matrix (Fin d) (Fin d) (w.adicCompletion E)) = (piW' h).mapMatrix (t : Matrix _ _ _) := rfl
  have hT2 : ((T⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) =
      (piW' h).mapMatrix ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix _ _ _) := by
    rw [hT, ← map_inv]; rfl
  have hstab : ∀ z, z ∈ latAt w W.L ↔ (T : Matrix _ _ _) *ᵥ z ∈ latAt w W.L := fun z => by
    refine ⟨fun hz => hT1 ▸ mulVec_mem_latAt h W _ (fun z hz => (ht z hz).1) z hz, fun hz => ?_⟩
    have := mulVec_mem_latAt h W _ (fun z hz => (ht z hz).2) _ hz
    rwa [← hT2, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  obtain ⟨a, ha⟩ := InertChart.exists_isFrameAt hw hL.fg
    (Submodule.IsFullLattice.span_eq_top (self := hL))
  obtain ⟨m, hm⟩ := ((InertChart.isFrameAt_mul ha (one_mem _)).2 T).1 hstab
  have hdet : Matrix.GeneralLinearGroup.det (a⁻¹ * T * a) = Matrix.GeneralLinearGroup.det T := by
    rw [map_mul, map_mul, map_inv, mul_comm _ (Matrix.GeneralLinearGroup.det a), ← mul_assoc, mul_inv_cancel, one_mul]
  have e2 : (piW' h (t : Matrix (Fin d) (Fin d) (AE F E)).det) =
      ((Matrix.GeneralLinearGroup.det T : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hT1, RingHom.map_det]
  rw [e2, ← hdet, ← hm, Matrix.GeneralLinearGroup.val_det_apply]
  have e3 : ((Formalism.UG.bc (Formalism.UG.Ov E w).subtype m : GL (Fin d) (w.adicCompletion E)) :
      Matrix (Fin d) (Fin d) (w.adicCompletion E)).det = ((m.val.det : Formalism.UG.Ov E w) : w.adicCompletion E) := by
    show ((Formalism.UG.Ov E w).subtype.mapMatrix m.val).det = _
    rw [← RingHom.map_det]; rfl
  rw [e3]
  exact valued_eq_one_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit m))

end Lat

end GlobalTheory.InertDetChr

theorem GlobalTheory.InertDetChr.alpha_det_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      X.α (Matrix.GeneralLinearGroup.det t) = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw hvT t ht
  obtain ⟨ht1, ht2⟩ := ht
  have h : w.under (𝓞 F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
  have e1 := GlobalTheory.InertDetChr.eq_ideleAt (GlobalTheory.InertDetChr.at_det_sub_one v t ht1)
  rw [e1, GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw]
  have hunr : GlobalTheory.LFun.UnrAt X.α w := hTr.chars.unrα w (by
    show ¬ (w.under (𝓞 F) ∈ (X.T : Set (Pl (F := F))))
    rw [h]; exact_mod_cast hvT)
  have hv1 := GlobalTheory.InertDetChr.valued_det_eq_one h hw G.W hTr.geo.hW.lat t ht2
  set y : (w.adicCompletion E)ˣ :=
    Units.map (toCompl h).toMonoidHom (GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t)) with hy
  have hyv : (y : w.adicCompletion E) =
      GlobalTheory.InertDetChr.piW' h ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)).det) := by
    rw [hy, Units.coe_map, GlobalTheory.InertDetChr.piW', RingHom.comp_apply, ← Matrix.GeneralLinearGroup.val_det_apply]
    rfl
  have hu : Formalism.L2.Host.IsUnitAt w y := by
    unfold Formalism.L2.Host.IsUnitAt
    rw [hyv]; exact hv1
  have hu2 := hunr y hu
  have hu' : ((Circle.toUnits (X.α (GlobalTheory.LFun.locIdele F w y)) : ℂˣ) : ℂ) = 1 := congrArg Units.val hu2
  rw [Circle.toUnits_apply, Units.val_mk0] at hu'
  exact Circle.ext (by simpa using hu')
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermModerateGrowth
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.AutGrowth

namespace GlobalTheory.ConstTermGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_pInf_alt : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_mapInf : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_alt)

theorem continuous_mapFin : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_mul_left_le {Ω : Set (GL (Fin a) (Cinf E))} (hΩ : IsCompact Ω) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c ∈ Ω, ∀ y : GL (Fin a) (Cinf E), height (c * y) ≤ B * height y := by
  have c1 : Continuous fun u : GL (Fin a) (Cinf E) => toL u.val :=
    (Units.continuous_val : Continuous fun u : GL (Fin a) (Cinf E) => u.val)
  have c2 : Continuous fun u : GL (Fin a) (Cinf E) => toL (u⁻¹).val :=
    (Units.continuous_coe_inv : Continuous fun u : GL (Fin a) (Cinf E) => (u⁻¹).val)
  obtain ⟨M1, h1⟩ := hΩ.exists_bound_of_continuousOn c1.continuousOn
  obtain ⟨M2, h2⟩ := hΩ.exists_bound_of_continuousOn c2.continuousOn
  have M0 : (0 : ℝ) ≤ max 0 (max M1 M2) := le_max_left _ _
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  refine ⟨1 + a * max 0 (max M1 M2), by positivity, fun c hc y => ?_⟩
  have m1 : ‖toL c.val‖ ≤ max 0 (max M1 M2) := (h1 c hc).trans ((le_max_left _ _).trans (le_max_right _ _))
  have m2 : ‖toL (c⁻¹).val‖ ≤ max 0 (max M1 M2) := (h2 c hc).trans ((le_max_right _ _).trans (le_max_right _ _))
  have e2 : ((c * y)⁻¹ : GL (Fin a) (Cinf E)).val = (y⁻¹).val * (c⁻¹).val := by
    rw [_root_.mul_inv_rev]; rfl
  have p1 := norm_toL_mul_le c.val y.val
  have p2 := norm_toL_mul_le (y⁻¹).val (c⁻¹).val
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have q1 : (a : ℝ) * (‖toL c.val‖ * ‖toL y.val‖) ≤ a * max 0 (max M1 M2) * ‖toL y.val‖ := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right m1 n1) ha
  have q2 : (a : ℝ) * (‖toL (y⁻¹).val‖ * ‖toL (c⁻¹).val‖) ≤ a * max 0 (max M1 M2) * ‖toL (y⁻¹).val‖ := by
    calc (a : ℝ) * (‖toL (y⁻¹).val‖ * ‖toL (c⁻¹).val‖) ≤ a * (‖toL (y⁻¹).val‖ * max 0 (max M1 M2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m2 n2) ha
      _ = _ := by ring
  have aM : (0 : ℝ) ≤ a * max 0 (max M1 M2) := by positivity
  unfold height
  rw [show toL (c * y).val = toL (c.val * y.val) from rfl, e2]
  nlinarith

theorem uniform_growth (φ : Sm E a) (hopen : IsOpen {k | finRep E a k φ = φ})
    (hgr : ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N)
    {Ω : Set (GA E a)} (hΩ : IsCompact Ω) :
    ∃ (C : ℝ) (N : ℕ), ∀ h ∈ Ω, ∀ y, ‖φ.1 (h * infGL E a y)‖ ≤ C * height y ^ N := by
  have hS : ∀ s : GL (Fin a) (Af E), finRep E a s φ = φ → ∀ x, φ.1 (x * finGL E a s) = φ.1 x := fun s hs x => by
    have := congrFun (congrArg Subtype.val hs) x
    exact this
  have hU : ∀ t : GL (Fin a) (Af E), IsOpen ((fun k => t⁻¹ * k) ⁻¹' {k | finRep E a k φ = φ}) := fun t =>
    hopen.preimage (continuous_const.mul continuous_id)
  have hKf : IsCompact (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E) '' Ω) := hΩ.image continuous_mapFin
  obtain ⟨T, hT⟩ := hKf.elim_finite_subcover (fun t => (fun k => t⁻¹ * k) ⁻¹' {k | finRep E a k φ = φ}) hU
    (fun k _ => Set.mem_iUnion.2 ⟨k, by
      change finRep E a (k⁻¹ * k) φ = φ
      rw [inv_mul_cancel, map_one]; rfl⟩)
  choose C N hCN using hgr
  obtain ⟨B, hB0, hB⟩ := height_mul_left_le (hΩ.image (continuous_mapInf (E := E) (a := a)))
  refine ⟨∑ t ∈ T, |C (finGL E a t)| * B ^ N (finGL E a t), ∑ t ∈ T, N (finGL E a t), fun h hh y => ?_⟩
  obtain ⟨t, htT, hkt⟩ := Set.mem_iUnion₂.1 (hT ⟨h, hh, rfl⟩)
  have e : h * infGL E a y = finGL E a t * infGL E a (Matrix.GeneralLinearGroup.map (pInf E) h * y) *
      finGL E a (t⁻¹ * Matrix.GeneralLinearGroup.map (pFin E) h) := by
    apply ga_ext
    · simp only [map_mul, pInf_infGL, pInf_finGL, one_mul, mul_one]
    · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul, mul_one, mul_inv_cancel_left]
  rw [e, hS _ hkt]
  have hcy := hB _ ⟨h, hh, rfl⟩ y
  have h0 := one_le_height (Matrix.GeneralLinearGroup.map (pInf E) h * y)
  have hy := one_le_height y
  calc ‖φ.1 (finGL E a t * infGL E a (Matrix.GeneralLinearGroup.map (pInf E) h * y))‖
      ≤ C (finGL E a t) * height (Matrix.GeneralLinearGroup.map (pInf E) h * y) ^ N (finGL E a t) := hCN _ _
    _ ≤ |C (finGL E a t)| * (B * height y) ^ N (finGL E a t) :=
        mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (by linarith) hcy _) (pow_nonneg (by linarith) _) (abs_nonneg _)
    _ = |C (finGL E a t)| * B ^ N (finGL E a t) * height y ^ N (finGL E a t) := by ring
    _ ≤ |C (finGL E a t)| * B ^ N (finGL E a t) * height y ^ (∑ t ∈ T, N (finGL E a t)) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy
          (Finset.single_le_sum (f := fun t => N (finGL E a t)) (fun _ _ => Nat.zero_le _) htT))
          (mul_nonneg (abs_nonneg _) (pow_nonneg hB0 _))
    _ ≤ (∑ t ∈ T, |C (finGL E a t)| * B ^ N (finGL E a t)) * height y ^ (∑ t ∈ T, N (finGL E a t)) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun t => |C (finGL E a t)| * B ^ N (finGL E a t))
          (fun _ _ => mul_nonneg (abs_nonneg _) (pow_nonneg hB0 _)) htT) (pow_nonneg (by linarith) _)

theorem norm_constTerm_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N) →
    ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖∫ x in 𝓕, φ.1 (unip x * (g * infGL E a y)) ∂μ‖ ≤ C * height y ^ N := by
  intro E _ _ _ a r _ _ μ 𝓕 _ _ h1 φ hleft hopen hgr g
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  have hc : Continuous fun x : BlockIx a r → Ad E => unip x * g :=
    GlobalTheory.CuspRep.CuspidalL2GL.continuous_unip.mul continuous_const
  obtain ⟨C, N, hC⟩ := uniform_growth φ hopen hgr (hK.image hc)
  refine ⟨C, N, fun y => ?_⟩
  have hb : ∀ x : BlockIx a r → Ad E, ‖φ.1 (unip x * (g * infGL E a y))‖ ≤ C * height y ^ N := by
    intro x
    obtain ⟨γ, ⟨z, rfl⟩, hγ⟩ := hcov x
    have hu : unip ((AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) z) =
        ratGL E a (unip z) := unip_algebraMap z
    have e : φ.1 (unip (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r) z + x) * g *
        infGL E a y) = φ.1 (unip x * (g * infGL E a y)) := by
      rw [unip_add, hu]
      simp only [mul_assoc]
      exact hleft _ _
    rw [← e]
    exact hC _ ⟨_, hγ, rfl⟩ y
  have hfin : μ 𝓕 < ⊤ := by rw [h1]; exact ENNReal.one_lt_top
  calc _ ≤ C * height y ^ N * (μ 𝓕).toReal := norm_setIntegral_le_of_norm_le_const hfin (fun x _ => hb x)
    _ = C * height y ^ N := by rw [h1]; simp

end GlobalTheory.ConstTermGrowth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsIndependentGoodEmbedding
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PhiIndep


open ReciprocityTheory.ChartRestriction.G.FD in
theorem bchar_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt Ψ r) {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : bchar la b ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  have ht : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  have hd := (hb τ).1
  rw [Matrix.det_of_upperTriangular ht] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)


open ReciprocityTheory.ChartRestriction.G.FD in
theorem indep_along {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp G : Type}
    (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : G → Σ k, Frame (X k).Ψ r)
    (honto : ∀ k, ∀ x ∈ (X k).dom, ∃ g, ∃ γ ∈ (X k).Γ, ∃ b ∈ Bor (X k).Ψ r, dict g = ⟨k, rmul (lact γ x) b⟩)
    (hχ : ∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) (ν : G → ℂ) (hν : ∀ g, ν g ≠ 0)
    {m : ℕ} (P : Fin m → FDSec X) (hS : ∀ i k, (X k).IsSec (la k) (P i k)) (h0 : ∀ i, P i ∈ offZero X)
    (hP : LinearIndependent ℂ P) (φ : Fin m → G → ℂ) (hφ : ∀ i g, φ i g = ν g * P i (dict g).1 (dict g).2) :
    LinearIndependent ℂ φ := by
  rw [Fintype.linearIndependent_iff] at hP ⊢
  intro c hc
  refine hP c ?_
  funext k x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  by_cases hx : x ∈ (X k).dom
  · obtain ⟨g, γ, hγ, b, hb, hg⟩ := honto k x hx
    have h := congrFun hc g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hφ] at h
    have hγx : lact γ x ∈ (X k).dom := dom_lact (X k) hx ((X k).Γ_stab γ hγ)
    have e : ∀ i, P i (dict g).1 (dict g).2 = bchar (la k) b * P i k x := by
      intro i
      rw [hg]
      show P i k (rmul (lact γ x) b) = _
      rw [(hS i k).2.1 _ hγx b hb, (hS i k).2.2 γ hγ x hx, hχ k γ hγ, one_mul]
    apply mul_left_cancel₀ (mul_ne_zero (hν g) (bchar_ne_zero (la k) hb))
    rw [mul_zero, Finset.mul_sum, ← h]
    exact Finset.sum_congr rfl fun i _ => by rw [e i]; ring
  · exact Finset.sum_eq_zero fun i _ => by rw [h0 i k x hx, mul_zero]


set_option maxHeartbeats 1000000 in
theorem phiJ_indep (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hd : Dom a n) (m : ℕ) (b : Fin m → T.R j)
    (hs : ∀ k, b k ∈ sec (T.Q.Xo j) T.Q.c a n) (hb : LinearIndependent T.Q.c.F b) :
    LinearIndependent ℂ fun k => T.phiJ j σ a (b k) := by
  obtain ⟨th, hr, -, hD⟩ := h.dictU j hj σ hσ
  have hI := GlobalTheory.rdIndep_of_lawsM D T.toCore h.toLawsM j hj σ hσ a n hd m b hs hb
  have hl : ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  refine indep_along (T.U j σ).X (laU (T.U j σ) a n) (T.dict j σ) hD.2.2.2.2.1 (h.chiTriv j hj σ hσ a n hd)
    (fun g => ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) * (T.cE j σ (T.dict j σ g).1 * T.mu j σ g)) ?_
    (fun k => rdU (T.U j σ) (b k)) (fun i k => (h.unf j hj σ hσ).2.2.2.2.1 a n hd _ (hs i) k)
    (fun i => rdU_mem_offZero _ _) hI _ ?_
  · intro g
    refine mul_ne_zero hl (mul_ne_zero ?_ ?_)
    · exact norm_ne_zero_iff.1 (by rw [h.cUnit j hj σ hσ]; exact one_ne_zero)
    · exact norm_ne_zero_iff.1 (by rw [(h.muUnit j hj σ hσ).2.1]; exact one_ne_zero)
  · intro i g
    simp only [CoreJ.phiJ, Pi.smul_apply, smul_eq_mul, adel_muPin]
    ring

theorem phiC_indep_of (D : D7) (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {m : ℕ} (b : Fin m → T.R j)
    (H : LinearIndependent ℂ fun k => T.phiJ j σ a (b k)) :
    LinearIndependent ℂ fun k => phiC T hV a (b k) := by
  subst hV
  exact H


set_option maxHeartbeats 1000000 in
theorem phiC_indep : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)) := by
  intro D T κ h i σ hσ hV m b hb
  refine phiC_indep_of D T hV _ (fun k => (b k : T.R ((i : ℕ) + 1))) ?_
  exact phiJ_indep D T h _ (inR i) σ hσ _ (κ i).n (dom_wtA (κ i)) m _
    (fun k => cusp_le_sec _ _ _ _ _ (b k).2)
    (hb.map' (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n).subtype (Submodule.ker_subtype _))

end GlobalTheory.PhiIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledHermitianSpaceFrameOfFrameStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_hermitian_space_frame_of_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (P Q R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ),
    Framed τ JA JB a b A C → Framed τ JA (dbl JB) a b A (fun w => dblM (C w)) := by
  first | exact @GlobalTheory.RealLift.Dbl.framed_dbl | exact GlobalTheory.RealLift.Dbl.framed_dbl | (intros; apply GlobalTheory.RealLift.Dbl.framed_dbl <;> assumption)
end

