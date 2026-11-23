module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually

@[expose] public section

noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct ENNReal NNReal
open NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.RestrMeas
attribute [-instance] Formalism.BasicNotions.Examples₂.instIsEmptyClsEmptyColumnChain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

instance locallyCompactSpace_finPts : LocallyCompactSpace (finPts σ J) := (isClosed_finPts σ J).locallyCompactSpace

def archFinEquiv : GAd σ J ≃ₜ* (∀ w, GArch σ J w) × GFin σ J where
  toFun g := (fun w => projArch σ J w g, projFin σ J g)
  invFun p := ofInf σ J (embArchPi σ J p.1) * ofFin σ J p.2
  left_inv g := GAd_ext σ J (fun w => by simp) fun v => by simp
  right_inv p := Prod.ext (funext fun w => by simp) (by simp)
  map_mul' g h := Prod.ext (funext fun w => by simp) (by simp)
  continuous_toFun := (continuous_pi (continuous_projArch σ J)).prodMk (continuous_projFin σ J)
  continuous_invFun := ((continuous_ofInf σ J).comp ((continuous_embArchPi σ J).comp continuous_fst)).mul
    ((continuous_ofFin σ J).comp continuous_snd)

theorem archFinEquiv_symm_apply (p : (∀ w, GArch σ J w) × GFin σ J) :
    (archFinEquiv σ J).symm p = ofInf σ J (embArchPi σ J p.1) * ofFin σ J p.2 := rfl

def finPtsEquiv : GFin σ J ≃ₜ* finPts σ J where
  toFun y := ⟨ofFin σ J y, mem_finPts.2 (projInf_ofFin σ J y)⟩
  invFun g := projFin σ J g
  left_inv := projFin_ofFin σ J
  right_inv g := Subtype.ext (ext_inf_fin σ J (by simp [mem_finPts.1 g.2]) (by simp))
  map_mul' g h := Subtype.ext (map_mul (ofFin σ J) g h)
  continuous_toFun := (continuous_ofFin σ J).subtype_mk _
  continuous_invFun := (continuous_projFin σ J).comp continuous_subtype_val

theorem finPtsEquiv_apply (y : GFin σ J) : (finPtsEquiv σ J y : GAd σ J) = ofFin σ J y := rfl

variable (L : Submodule (𝓞 E) (Fin n → E))

def IsRestrictedProd (μa : ∀ w, Measure (GArch σ J w)) (μf : ∀ v, Measure (GLoc σ J v)) (μ : Measure (GAd σ J)) :
    Prop := IsHaarProd (projArch σ J) (proj σ J) (stabLoc σ J L) μa μf μ

def IsRestrictedProdFin (μf : ∀ v, Measure (GLoc σ J v)) (μ : Measure (GFin σ J)) : Prop :=
  IsHaarProdFin (projFinLoc σ J) (stabLoc σ J L) μf μ

def IsRestrictedProdFinPts (μf : ∀ v, Measure (GLoc σ J v)) (μ : Measure (finPts σ J)) : Prop :=
  IsHaarProdFin (fun v => (proj σ J v).comp (finPts σ J).subtype) (stabLoc σ J L) μf μ

section Unfold

omit [NumberField E]

variable {σ J L} {S : Finset (HeightOneSpectrum (𝓞 F))} {μa : ∀ w, Measure (GArch σ J w)}
  {μf : ∀ v, Measure (GLoc σ J v)} {νf : ∀ v : {v // v ∉ S}, Measure (GLoc σ J v)}

theorem isRestrictedProd_iff {μ : Measure (GAd σ J)} : IsRestrictedProd σ J L μa μf μ ↔
    (∀ w, (μa w).IsHaarMeasure) ∧ (∀ v, (μf v).IsHaarMeasure) ∧ μ.IsHaarMeasure ∧
    (∀ᶠ v in cofinite, μf v (stabLoc σ J L v) = 1) ∧
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∉ S, μf v (stabLoc σ J L v) = 1) →
      ∀ (A : ∀ w, Set (GArch σ J w)) (B : ∀ v, Set (GLoc σ J v)),
        (∀ w, MeasurableSet (A w)) → (∀ v ∈ S, MeasurableSet (B v)) →
        μ {g | (∀ w, projArch σ J w g ∈ A w) ∧ (∀ v ∈ S, proj σ J v g ∈ B v) ∧
          ∀ v ∉ S, proj σ J v g ∈ stabLoc σ J L v} = (∏ w, μa w (A w)) * ∏ v ∈ S, μf v (B v) := Iff.rfl

theorem isRestrictedProdFin_iff {μ : Measure (GFin σ J)} : IsRestrictedProdFin σ J L μf μ ↔
    (∀ v, (μf v).IsHaarMeasure) ∧ μ.IsHaarMeasure ∧ (∀ᶠ v in cofinite, μf v (stabLoc σ J L v) = 1) ∧
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∉ S, μf v (stabLoc σ J L v) = 1) →
      ∀ B : ∀ v, Set (GLoc σ J v), (∀ v ∈ S, MeasurableSet (B v)) →
        μ {g | (∀ v ∈ S, projFinLoc σ J v g ∈ B v) ∧ ∀ v ∉ S, projFinLoc σ J v g ∈ stabLoc σ J L v} =
          ∏ v ∈ S, μf v (B v) := isHaarProdFin_iff

theorem isRestrictedProdFinPts_iff {μ : Measure (finPts σ J)} : IsRestrictedProdFinPts σ J L μf μ ↔
    (∀ v, (μf v).IsHaarMeasure) ∧ μ.IsHaarMeasure ∧ (∀ᶠ v in cofinite, μf v (stabLoc σ J L v) = 1) ∧
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∉ S, μf v (stabLoc σ J L v) = 1) →
      ∀ B : ∀ v, Set (GLoc σ J v), (∀ v ∈ S, MeasurableSet (B v)) →
        μ {g | (∀ v ∈ S, proj σ J v g ∈ B v) ∧ ∀ v ∉ S, proj σ J v g ∈ stabLoc σ J L v} =
          ∏ v ∈ S, μf v (B v) := isHaarProdFin_iff

theorem IsRestrictedProd.haar_arch {μ : Measure (GAd σ J)} (h : IsRestrictedProd σ J L μa μf μ) (w : InfinitePlace F) :
    (μa w).IsHaarMeasure := (isRestrictedProd_iff.1 h).1 w

theorem IsRestrictedProd.haar_loc {μ : Measure (GAd σ J)} (h : IsRestrictedProd σ J L μa μf μ)
    (v : HeightOneSpectrum (𝓞 F)) : (μf v).IsHaarMeasure := (isRestrictedProd_iff.1 h).2.1 v

theorem IsRestrictedProd.haar {μ : Measure (GAd σ J)} (h : IsRestrictedProd σ J L μa μf μ) : μ.IsHaarMeasure := (isRestrictedProd_iff.1 h).2.2.1

theorem IsRestrictedProd.isCylProd {μ : Measure (GAd σ J)} (h : IsRestrictedProd σ J L μa μf μ) :
    IsCylProd (fun w => projArch σ J w) (fun v => proj σ J v) (fun v => (stabLoc σ J L v : Set (GLoc σ J v)))
      μa μf μ := by
  unfold IsRestrictedProd IsHaarProd at h
  exact h.2.2.2

theorem IsRestrictedProd.eventually_eq_one {μ : Measure (GAd σ J)} (h : IsRestrictedProd σ J L μa μf μ) :
    ∀ᶠ v in cofinite, μf v (stabLoc σ J L v) = 1 := (isRestrictedProd_iff.1 h).2.2.2.1

theorem isHaarProd_iff_isRestrProd {X W V : Type} {Ya : W → Type} {Yf : V → Type} [Group X] [∀ w, Group (Ya w)]
    [∀ v, Group (Yf v)] [TopologicalSpace X] [∀ w, TopologicalSpace (Ya w)] [∀ v, TopologicalSpace (Yf v)] [Fintype W]
    [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)] {pa : ∀ w, X →* Ya w}
    {pf : ∀ v, X →* Yf v} {K : ∀ v, Subgroup (Yf v)} {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)}
    {μ : Measure X} : IsHaarProd pa pf K μa μf μ ↔ IsRestrProd pa pf K μa μf μ := by
  unfold IsHaarProd IsCylProd
  constructor
  · rintro ⟨ha, hf, hμ, h1, hc⟩
    exact ⟨ha, hf, h1, hμ, hc⟩
  · intro h
    exact ⟨h.haar_inf, h.haar_fin, h.haar, h.vol_one, h.measure_cyl⟩

theorem isRestrictedProd_iff_isProdMeasure {μ : Measure (GAd σ J)} :
    IsRestrictedProd σ J L μa μf μ ↔ IsProdMeasure σ J L μa μf μ := isHaarProd_iff_isRestrProd

end Unfold

variable [Submodule.IsFullLattice E L]

theorem restrGroup_GFin : RestrMeas.IsRestrGroup (noArch (GFin σ J)) (projFinLoc σ J) (stabLoc σ J L) := by
  refine
    { continuous_pa := fun w => w.elim
      continuous_pf := continuous_projFinLoc σ J
      isOpen_K := isOpen_stabLoc σ J L
      isCompact_K := isCompact_stabLoc σ J L
      ext := fun _ _ _ h => GFin_ext σ J h
      eventually_mem := eventually_projFinLoc_mem_stabLoc σ J L
      exists_eq := fun _ y hy => ?_
      isOpen_level := ?_
      isCompact_level := fun _ _ => ?_ }
  · obtain ⟨g, hg, -⟩ := existsUnique_projFinLoc_eq σ J L y hy
    exact ⟨g, fun w => w.elim, hg⟩
  · have e : {x : GFin σ J | ∀ v, projFinLoc σ J v x ∈ stabLoc σ J L v} =
        (levelOffFin σ J L ∅ : Set (GFin σ J)) := by
      ext x
      simp [mem_levelOffFin]
    rw [e]
    exact isOpen_levelOffFin_empty σ J L
  · exact isCompact_of_ext (isCompact_levelOffFin σ J L ∅) fun x => by simp [mem_levelOffFin]

theorem restrGroup_GAd : RestrMeas.IsRestrGroup (projArch σ J) (proj σ J) (stabLoc σ J L) := by
  refine
    { continuous_pa := continuous_projArch σ J
      continuous_pf := continuous_proj σ J
      isOpen_K := isOpen_stabLoc σ J L
      isCompact_K := isCompact_stabLoc σ J L
      ext := fun _ _ ha hf => GAd_ext σ J ha hf
      eventually_mem := eventually_proj_mem_stabLoc σ J L
      exists_eq := fun a y hy => ?_
      isOpen_level := ?_
      isCompact_level := fun C hC => ?_ }
  · obtain ⟨g, hg, -⟩ := existsUnique_projFinLoc_eq σ J L y hy
    refine ⟨ofInf σ J (embArchPi σ J a) * ofFin σ J g, fun w => ?_, fun v => ?_⟩
    · simp
    · simp [hg]
  · have e : {x : GAd σ J | ∀ v, proj σ J v x ∈ stabLoc σ J L v} = (levelOpen σ J L : Set (GAd σ J)) := by
      ext x
      simp [mem_levelOpen]
    rw [e]
    exact isOpen_levelOpen σ J L
  · exact isCompact_of_ext ((isRestrGroup_GAd σ J L).isCompact_cyl ∅ C (fun _ => ∅) hC (by simp))
      fun x => by simp [GlobalTheory.AdelicU.cyl]

theorem restrGroup_finPts :
    RestrMeas.IsRestrGroup (noArch (finPts σ J)) (fun v => (proj σ J v).comp (finPts σ J).subtype) (stabLoc σ J L) := by
  set_option synthInstance.maxHeartbeats 200000 in
  have h := (restrGroup_GAd σ J L).subgroup (i := (Empty.elim : Empty → InfinitePlace F)) (j := id)
    (fun a => a.elim) Function.injective_id (finPts σ J) fun x => by simp [mem_finPts_iff_forall]
  exact h.noArch

section Exist

variable (S : Finset (HeightOneSpectrum (𝓞 F))) (μa : ∀ w, Measure (GArch σ J w)) (μf : ∀ v, Measure (GLoc σ J v))
  (νf : ∀ v : {v // v ∉ S}, Measure (GLoc σ J v)) [∀ w, (μa w).IsHaarMeasure] [∀ v, (μf v).IsHaarMeasure]
  [∀ v, (νf v).IsHaarMeasure]

theorem existsUnique_isRestrictedProd (h : ∀ᶠ v in cofinite, μf v (stabLoc σ J L v) = 1) :
    ∃! μ, IsRestrictedProd σ J L μa μf μ := (restrGroup_GAd σ J L).existsUnique_isHaarProd μa μf h

theorem existsUnique_isRestrictedProdFin (h : ∀ᶠ v in cofinite, μf v (stabLoc σ J L v) = 1) :
    ∃! μ, IsRestrictedProdFin σ J L μf μ := (restrGroup_GFin σ J L).existsUnique_isHaarProd (fun w => w.elim) μf (ha := fun w => w.elim) h

theorem existsUnique_isRestrictedProdFinPts (h : ∀ᶠ v in cofinite, μf v (stabLoc σ J L v) = 1) :
    ∃! μ, IsRestrictedProdFinPts σ J L μf μ := (restrGroup_finPts σ J L).existsUnique_isHaarProd (fun w => w.elim) μf (ha := fun w => w.elim) h

end Exist

theorem exists_isRestrictedProd : ∃ μ, IsRestrictedProd σ J L (fun _ => haar) (haarLoc σ J L) μ := (existsUnique_isRestrictedProd σ J L (fun _ => haar) (haarLoc σ J L)
    (Filter.Eventually.of_forall fun v => haarLoc_stabLoc σ J L v)).exists

section Api

variable {σ J L} {S : Finset (HeightOneSpectrum (𝓞 F))} {μa : ∀ w, Measure (GArch σ J w)}
  {μf : ∀ v, Measure (GLoc σ J v)} {νf : ∀ v : {v // v ∉ S}, Measure (GLoc σ J v)} {μ μ' : Measure (GAd σ J)}

theorem IsRestrictedProd.unique (h : IsRestrictedProd σ J L μa μf μ) (h' : IsRestrictedProd σ J L μa μf μ') :
    μ = μ' := IsHaarProd.unique (isOpen_stabLoc σ J L) (isCompact_stabLoc σ J L) h h'

section Indep

variable (L' : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L']

end Indep

theorem IsRestrictedProd.smul_arch [DecidableEq (InfinitePlace F)] (h : IsRestrictedProd σ J L μa μf μ)
    (w : InfinitePlace F) {x : ℝ≥0} (hx : x ≠ 0) :
    IsRestrictedProd σ J L (Function.update μa w (x • μa w)) μf (x • μ) := isRestrictedProd_iff_isProdMeasure.2
    (IsRestrProd.smul_inf (isRestrictedProd_iff_isProdMeasure.1 h) w hx)

theorem IsRestrictedProd.measure_level (h : IsRestrictedProd σ J L μa μf μ) {A : ∀ w, Set (GArch σ J w)}
    (hA : ∀ w, MeasurableSet (A w)) :
    μ {g | (∀ w, projArch σ J w g ∈ A w) ∧ g ∈ levelOpen σ J L} =
      (∏ w, μa w (A w)) * ∏ᶠ v, μf v (stabLoc σ J L v) := by
  have e : {g | (∀ w, projArch σ J w g ∈ A w) ∧ g ∈ levelOpen σ J L} =
      {g | (∀ w, projArch σ J w g ∈ A w) ∧ ∀ v, proj σ J v g ∈ stabLoc σ J L v} :=
    Set.ext fun g => and_congr Iff.rfl mem_levelOpen
  rw [e]
  exact h.isCylProd.measure_level (fun v => (isOpen_stabLoc σ J L v).measurableSet) hA

theorem IsRestrictedProdFin.measure_level {ν : Measure (GFin σ J)} (h : IsRestrictedProdFin σ J L μf ν) :
    ν (levelOffFin σ J L ∅) = ∏ᶠ v, μf v (stabLoc σ J L v) := by
  unfold IsRestrictedProdFin IsHaarProdFin IsHaarProd at h
  have hm := h.2.2.2.measure_level (fun v => (isOpen_stabLoc σ J L v).measurableSet) (A := fun w => w.elim)
    (fun w => w.elim)
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul] at hm
  rw [← hm]
  congr 1
  ext g
  simp [mem_levelOffFin]

theorem map_map_symm {X Y : Type} [Group X] [Group Y] [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X]
    [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] (e : X ≃ₜ* Y) (m : Measure Y) :
    (m.map e.symm).map e = m := by
  have h1 : Measurable (e : X → Y) := e.continuous.measurable
  have h2 : Measurable (e.symm : Y → X) := e.symm.continuous.measurable
  rw [Measure.map_map h1 h2]
  have hid : (e ∘ e.symm) = id := funext fun y => e.apply_symm_apply y
  rw [hid, Measure.map_id]


omit [Submodule.IsFullLattice E L] in
theorem IsRestrictedProdFin.prod [∀ w, (μa w).IsHaarMeasure] {ν : Measure (GFin σ J)}
    (h : IsRestrictedProdFin σ J L μf ν) :
    IsRestrictedProd σ J L μa μf (((Measure.pi μa).prod ν).map (archFinEquiv σ J).symm) := by
  unfold IsRestrictedProdFin at h
  unfold IsRestrictedProd
  refine IsHaarProdFin.prod_arch h (archFinEquiv σ J).symm (fun w p => ?_) (fun v p => ?_)
  · rw [archFinEquiv_symm_apply]
    simp
  · rw [archFinEquiv_symm_apply]
    simp

theorem IsRestrictedProd.map_archFin (h : IsRestrictedProd σ J L μa μf μ) {ν : Measure (GFin σ J)}
    (h' : IsRestrictedProdFin σ J L μf ν) : μ.map (archFinEquiv σ J) = (Measure.pi μa).prod ν := by
  have := h.haar_arch
  rw [h.unique (IsRestrictedProdFin.prod h')]
  exact map_map_symm (archFinEquiv σ J) _


omit [Submodule.IsFullLattice E L] in
theorem IsRestrictedProdFin.map_finPts {ν : Measure (GFin σ J)} (h : IsRestrictedProdFin σ J L μf ν) :
    IsRestrictedProdFinPts σ J L μf (ν.map (finPtsEquiv σ J)) := by
  unfold IsRestrictedProdFin IsHaarProdFin at h
  unfold IsRestrictedProdFinPts IsHaarProdFin
  refine IsHaarProd.map h (finPtsEquiv σ J) (fun w _ => w.elim) (fun v y => ?_)
  show proj σ J v (finPtsEquiv σ J y : GAd σ J) = projFinLoc σ J v y
  rw [finPtsEquiv_apply, proj_ofFin]

end Api

end GlobalTheory.AdelicU

end
