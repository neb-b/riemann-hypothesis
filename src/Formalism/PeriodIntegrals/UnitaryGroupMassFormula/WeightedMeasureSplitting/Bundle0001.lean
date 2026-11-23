module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.SplTApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousTensMap
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures NumberField Topology
open scoped TensorProduct

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def crd (R : Type) [CommRing R] [Algebra F R] : R ⊗[F] E ≃ₗ[R] (Fin d → R) :=
  (Algebra.TensorProduct.basis R b).equivFun

theorem crd_tensMap {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (φ : R →ₐ[F] R') (x : R ⊗[F] E) : crd b R' (tensMap φ x) = fun i => φ (crd b R x i) := by
  induction x using TensorProduct.induction_on with
  | zero => funext i; simp
  | tmul a e =>
    funext i
    simp [crd, tensMap, Algebra.TensorProduct.basis_repr_tmul, map_mul, AlgHom.commutes]
  | add x y hx hy =>
    funext i
    have h1 := congrFun hx i
    have h2 := congrFun hy i
    simp only [map_add (f := _), Pi.add_apply] at h1 h2 ⊢
    rw [h1, h2]

variable [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

def crdH : R ⊗[F] E ≃ₜ (Fin d → R) where
  toEquiv := (crd b R).toEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap (crd b R).toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap (crd b R).symm.toLinearMap

theorem crdH_apply (x : R ⊗[F] E) : crdH b R x = crd b R x := rfl

theorem continuous_tensMap {R' : Type} [CommRing R'] [Algebra F R'] [TopologicalSpace R']
    [IsTopologicalRing R'] (φ : R →ₐ[F] R') (hφ : Continuous φ) :
    Continuous (tensMap (E := E) φ) := by
  have h : (tensMap (E := E) φ : R ⊗[F] E → R' ⊗[F] E) =
      (crdH (Module.finBasis F E) R').symm ∘ (fun c i => φ (c i)) ∘ crdH (Module.finBasis F E) R := by
    funext x
    apply (crdH (Module.finBasis F E) R').injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply, crdH_apply]
    exact crd_tensMap (Module.finBasis F E) φ x
  rw [h]
  exact (crdH (Module.finBasis F E) R').symm.continuous.comp
    ((continuous_pi fun i => hφ.comp (continuous_apply i)).comp (crdH (Module.finBasis F E) R).continuous)

end Coord

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem continuous_fstA : Continuous (fstA F) := continuous_fst

theorem continuous_sndA : Continuous (sndA F) := continuous_snd

def splInv (y : (Ainf F ⊗[F] E) × (Af F ⊗[F] E)) : AF F ⊗[F] E :=
  (crd (Module.finBasis F E) (AF F)).symm
    (fun i => ((crd (Module.finBasis F E) (Ainf F) y.1 i, crd (Module.finBasis F E) (Af F) y.2 i) : AF F))

theorem crd_AF (x : AF F ⊗[F] E) (i : Fin (Module.finrank F E)) :
    crd (Module.finBasis F E) (AF F) x i =
      ((crd (Module.finBasis F E) (Ainf F) (splT x).1 i, crd (Module.finBasis F E) (Af F) (splT x).2 i) : AF F) := by
  rw [splT_apply, crd_tensMap, crd_tensMap]
  rfl

theorem crd_splInv (y : (Ainf F ⊗[F] E) × (Af F ⊗[F] E)) :
    crd (Module.finBasis F E) (AF F) (splInv y) =
      fun i => ((crd (Module.finBasis F E) (Ainf F) y.1 i, crd (Module.finBasis F E) (Af F) y.2 i) : AF F) :=
  LinearEquiv.apply_symm_apply _ _

theorem splT_splInv (y : (Ainf F ⊗[F] E) × (Af F ⊗[F] E)) : splT (splInv y) = y := by
  obtain ⟨y₁, y₂⟩ := y
  rw [splT_apply]
  refine Prod.ext ?_ ?_
  · apply (crd (Module.finBasis F E) (Ainf F)).injective
    rw [crd_tensMap, crd_splInv]
    rfl
  · apply (crd (Module.finBasis F E) (Af F)).injective
    rw [crd_tensMap, crd_splInv]
    rfl

theorem splInv_splT (x : AF F ⊗[F] E) : splInv (splT x) = x := by
  apply (crd (Module.finBasis F E) (AF F)).injective
  rw [crd_splInv]
  funext i
  exact (crd_AF x i).symm

def splR : AF F ⊗[F] E ≃+* (Ainf F ⊗[F] E) × (Af F ⊗[F] E) where
  toFun := splT
  invFun := splInv
  left_inv := splInv_splT
  right_inv := splT_splInv
  map_mul' := map_mul splT
  map_add' := map_add splT

theorem splR_apply (x : AF F ⊗[F] E) : splR x = splT x := rfl

theorem splT_bijective : Function.Bijective (splT (F := F) (E := E)) := splR.bijective

theorem continuous_splT : Continuous (splT (F := F) (E := E)) := by
  show Continuous fun x => (tensMap (E := E) (fstA F) x, tensMap (E := E) (sndA F) x)
  exact (continuous_tensMap (AF F) _ continuous_fstA).prodMk
    (continuous_tensMap (AF F) _ continuous_sndA)

theorem continuous_splInv : Continuous (splInv (F := F) (E := E)) := by
  have h : (splInv (F := F) (E := E)) = (crdH (Module.finBasis F E) (AF F)).symm ∘
      (fun y : (Ainf F ⊗[F] E) × (Af F ⊗[F] E) => fun i =>
        ((crdH (Module.finBasis F E) (Ainf F) y.1 i, crdH (Module.finBasis F E) (Af F) y.2 i) : AF F)) := by
    funext y
    rfl
  rw [h]
  refine (crdH (Module.finBasis F E) (AF F)).symm.continuous.comp (continuous_pi fun i => ?_)
  exact ((continuous_apply i).comp ((crdH _ (Ainf F)).continuous.comp continuous_fst)).prodMk
    ((continuous_apply i).comp ((crdH _ (Af F)).continuous.comp continuous_snd))

def splH : AF F ⊗[F] E ≃ₜ (Ainf F ⊗[F] E) × (Af F ⊗[F] E) where
  toEquiv := splR.toEquiv
  continuous_toFun := continuous_splT
  continuous_invFun := continuous_splInv

end Split

end PI.UnitaryGroupMassFormula.MeasWCore
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.MemSpanRIffSplit
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField
open scoped TensorProduct

namespace Memb

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R') {n : ℕ}

def mapV : (Fin n → R ⊗[F] E) →+ (Fin n → R' ⊗[F] E) :=
  (tensMap (E := E) φ).toAddMonoidHom.compLeft (Fin n)

@[simp] theorem mapV_apply (x : Fin n → R ⊗[F] E) (i : Fin n) :
    mapV (E := E) φ x i = tensMap (E := E) φ (x i) := rfl

theorem mapV_smul (c : R ⊗[F] E) (x : Fin n → R ⊗[F] E) :
    mapV (E := E) φ (c • x) = tensMap (E := E) φ c • mapV (E := E) φ x := by
  funext i
  simp [map_mul]

theorem mapV_ratV (v : Fin n → E) : mapV (E := E) φ (ratV (F := F) R v) = ratV (F := F) R' v := by
  funext i
  simp [ratV, tensMap_inclR]

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

theorem lin_haMap (g : HA R σ J) (x : Fin n → R ⊗[F] E) :
    lin R' σ J (haMap σ J φ g) (mapV (E := E) φ x) = mapV (E := E) φ (lin R σ J g x) := by
  funext i
  change Matrix.mulVec (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map
      (tensMap (E := E) φ)) (fun j => tensMap (E := E) φ (x j)) i =
    tensMap (E := E) φ (Matrix.mulVec ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (R ⊗[F] E)) x i)
  rw [RingHom.map_mulVec]
  rfl

theorem mapV_mem_spanR {m : ℕ} (Y : Fin m → Fin n → E) (s : Set (Fin m)) (x : Fin n → R ⊗[F] E)
    (hx : x ∈ spanR (F := F) R Y s) : mapV (E := E) φ x ∈ spanR (F := F) R' Y s := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    rw [mapV_ratV]
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mapV_smul]; exact Submodule.smul_mem _ _ hx

theorem hR_mapV (x y : Fin n → R ⊗[F] E) :
    hR R' σ J (mapV (E := E) φ x) (mapV (E := E) φ y) = tensMap (E := E) φ (hR R σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, map_sum, map_mul, mapV_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : tensMap (E := E) φ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (x i)) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R' σ (tensMap (E := E) φ (x i)) := by
    have := congrArg (fun f : R ⊗[F] E →+* R' ⊗[F] E => f (x i)) (tensMap_sigR (E := E) φ σ)
    simpa using this
  rw [h1]
  simp [JR, tensMap_inclR]

theorem hR_zero_right (x : Fin n → R ⊗[F] E) : hR R σ J x 0 = 0 := by
  simp [hR, Formalism.UG.hform]

end Gen

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem eq_iff_split (hinj : Function.Injective (splT (F := F) (E := E)))
    (w u : Fin n → AF F ⊗[F] E) :
    w = u ↔ mapV (E := E) (fstA F) w = mapV (E := E) (fstA F) u ∧
      mapV (E := E) (sndA F) w = mapV (E := E) (sndA F) u := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    funext i
    apply hinj
    rw [splT_apply, splT_apply]
    exact Prod.ext (congrFun h1 i) (congrFun h2 i)

theorem exists_split (hsurj : Function.Surjective (splT (F := F) (E := E)))
    (y₁ : Fin n → Ainf F ⊗[F] E) (y₂ : Fin n → Af F ⊗[F] E) :
    ∃ v : Fin n → AF F ⊗[F] E, mapV (E := E) (fstA F) v = y₁ ∧ mapV (E := E) (sndA F) v = y₂ := by
  choose v hv using fun i => hsurj (y₁ i, y₂ i)
  refine ⟨v, funext fun i => ?_, funext fun i => ?_⟩
  · exact congrArg Prod.fst (hv i)
  · exact congrArg Prod.snd (hv i)

theorem mem_spanR_of_split (hbij : Function.Bijective (splT (F := F) (E := E))) {m : ℕ}
    (Y : Fin m → Fin n → E) (s : Set (Fin m)) (w : Fin n → AF F ⊗[F] E)
    (h1 : mapV (E := E) (fstA F) w ∈ spanR (F := F) (Ainf F) Y s)
    (h2 : mapV (E := E) (sndA F) w ∈ spanR (F := F) (Af F) Y s) :
    w ∈ spanR (F := F) (AF F) Y s := by
  classical
  simp only [spanR, Set.image_eq_range] at h1 h2 ⊢
  rw [Submodule.mem_span_range_iff_exists_fun] at h1 h2
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  choose c hc using fun a => hbij.2 (c1 a, c2 a)
  have hw : w = ∑ a, c a • ratV (F := F) (AF F) (Y a) := by
    rw [eq_iff_split hbij.1]
    constructor
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [← hc1, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mapV_smul, mapV_ratV]
      congr 1
      exact (congrArg Prod.fst (hc a)).symm
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [← hc2, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mapV_smul, mapV_ratV]
      congr 1
      exact (congrArg Prod.snd (hc a)).symm
  rw [hw, Submodule.mem_span_range_iff_exists_fun]
  exact ⟨c, rfl⟩

theorem mem_spanR_iff_split (hbij : Function.Bijective (splT (F := F) (E := E))) {m : ℕ}
    (Y : Fin m → Fin n → E) (s : Set (Fin m)) (w : Fin n → AF F ⊗[F] E) :
    w ∈ spanR (F := F) (AF F) Y s ↔ mapV (E := E) (fstA F) w ∈ spanR (F := F) (Ainf F) Y s ∧
      mapV (E := E) (sndA F) w ∈ spanR (F := F) (Af F) Y s :=
  ⟨fun h => ⟨mapV_mem_spanR _ Y s w h, mapV_mem_spanR _ Y s w h⟩,
    fun h => mem_spanR_of_split hbij Y s w h.1 h.2⟩

end Split

end Memb

open Memb

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

theorem splitA_injective (hinj : Function.Injective (splT (F := F) (E := E))) :
    Function.Injective (splitA σ J) := by
  intro g g' h
  have h1 : haMap σ J (fstA F) g = haMap σ J (fstA F) g' := congrArg Prod.fst h
  have h2 : haMap σ J (sndA F) g = haMap σ J (sndA F) g' := congrArg Prod.snd h
  have hm : HA.mat (AF F) σ J g = HA.mat (AF F) σ J g' := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    apply hinj
    rw [splT_apply, splT_apply]
    refine Prod.ext ?_ ?_
    · exact congrArg (fun k => ((HA.mat (Ainf F) σ J k : GL (Fin n) (Ainf F ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j) h1
    · exact congrArg (fun k => ((HA.mat (Af F) σ J k : GL (Fin n) (Af F ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) h2
  exact Subtype.ext hm

theorem mem_Hsub_iff (hinj : Function.Injective (splT (F := F) (E := E))) {r : ℕ} (P : Frame E n r)
    (g : HA (AF F) σ J) :
    g ∈ Hsub (AF F) σ J P ↔ haMap σ J (fstA F) g ∈ Hsub (Ainf F) σ J P ∧
      haMap σ J (sndA F) g ∈ Hsub (Af F) σ J P := by
  unfold Hsub
  rw [mem_stabT, mem_stabT, mem_stabT]
  constructor
  · intro h
    refine ⟨fun b => ?_, fun b => ?_⟩
    · rw [← mapV_ratV (fstA F), lin_haMap, h b]
    · rw [← mapV_ratV (sndA F), lin_haMap, h b]
  · rintro ⟨h1, h2⟩ b
    rw [eq_iff_split hinj]
    constructor
    · rw [← lin_haMap, mapV_ratV]
      exact h1 b
    · rw [← lin_haMap, mapV_ratV]
      exact h2 b

theorem mem_Nsub_iff (hbij : Function.Bijective (splT (F := F) (E := E))) {r : ℕ} (P : Frame E n r)
    (g : HA (AF F) σ J) :
    g ∈ Nsub (AF F) σ J P ↔ haMap σ J (fstA F) g ∈ Nsub (Ainf F) σ J P ∧
      haMap σ J (sndA F) g ∈ Nsub (Af F) σ J P := by
  have hdiff : ∀ {R' : Type} [CommRing R'] [Algebra F R'] (φ : AF F →ₐ[F] R') (v : Fin n → AF F ⊗[F] E),
      mapV (E := E) φ (lin (AF F) σ J g v - v) =
        lin R' σ J (haMap σ J φ g) (mapV (E := E) φ v) - mapV (E := E) φ v := by
    intro R' _ _ φ v
    rw [map_sub, lin_haMap]
  have hperp : ∀ {R' : Type} [CommRing R'] [Algebra F R'] (φ : AF F →ₐ[F] R') (v : Fin n → AF F ⊗[F] E),
      InXperp (AF F) σ J P v → InXperp R' σ J P (mapV (E := E) φ v) := by
    intro R' _ _ φ v hv a
    rw [← mapV_ratV φ, hR_mapV, hv a, map_zero]
  change (UniC (AF F) σ J P.e g ∧ ∀ v, InXperp (AF F) σ J P v →
      lin (AF F) σ J g v - v ∈ spanR (F := F) (AF F) P.e Set.univ) ↔
    (UniC (Ainf F) σ J P.e (haMap σ J (fstA F) g) ∧ ∀ v, InXperp (Ainf F) σ J P v →
      lin (Ainf F) σ J (haMap σ J (fstA F) g) v - v ∈ spanR (F := F) (Ainf F) P.e Set.univ) ∧
    (UniC (Af F) σ J P.e (haMap σ J (sndA F) g) ∧ ∀ v, InXperp (Af F) σ J P v →
      lin (Af F) σ J (haMap σ J (sndA F) g) v - v ∈ spanR (F := F) (Af F) P.e Set.univ)
  have huni : UniC (AF F) σ J P.e g ↔ UniC (Ainf F) σ J P.e (haMap σ J (fstA F) g) ∧
      UniC (Af F) σ J P.e (haMap σ J (sndA F) g) := by
    unfold UniC
    constructor
    · intro h
      refine ⟨fun b => ?_, fun b => ?_⟩
      · have := mapV_mem_spanR (E := E) (fstA F) P.e _ _ (h b)
        rwa [hdiff, mapV_ratV] at this
      · have := mapV_mem_spanR (E := E) (sndA F) P.e _ _ (h b)
        rwa [hdiff, mapV_ratV] at this
    · rintro ⟨h1, h2⟩ b
      rw [mem_spanR_iff_split hbij, hdiff, hdiff, mapV_ratV, mapV_ratV]
      exact ⟨h1 b, h2 b⟩
  rw [huni]
  constructor
  · rintro ⟨⟨hu1, hu2⟩, hX⟩
    refine ⟨⟨hu1, fun v₁ hv₁ => ?_⟩, ⟨hu2, fun v₂ hv₂ => ?_⟩⟩
    · obtain ⟨v, hv1, hv2⟩ := exists_split hbij.2 v₁ 0
      have hv : InXperp (AF F) σ J P v := by
        intro a
        apply hbij.1
        rw [map_zero, splT_apply, ← hR_mapV, ← hR_mapV, mapV_ratV, mapV_ratV, hv1, hv2,
          hR_zero_right, hv₁ a]
        rfl
      have := mapV_mem_spanR (E := E) (fstA F) P.e _ _ (hX v hv)
      rwa [hdiff, hv1] at this
    · obtain ⟨v, hv1, hv2⟩ := exists_split hbij.2 0 v₂
      have hv : InXperp (AF F) σ J P v := by
        intro a
        apply hbij.1
        rw [map_zero, splT_apply, ← hR_mapV, ← hR_mapV, mapV_ratV, mapV_ratV, hv1, hv2,
          hR_zero_right, hv₂ a]
        rfl
      have := mapV_mem_spanR (E := E) (sndA F) P.e _ _ (hX v hv)
      rwa [hdiff, hv2] at this
  · rintro ⟨⟨hu1, hX1⟩, ⟨hu2, hX2⟩⟩
    refine ⟨⟨hu1, hu2⟩, fun v hv => ?_⟩
    rw [mem_spanR_iff_split hbij, hdiff, hdiff]
    exact ⟨hX1 _ (hperp _ v hv), hX2 _ (hperp _ v hv)⟩

end PI.UnitaryGroupMassFormula.MeasWCore
end
end

