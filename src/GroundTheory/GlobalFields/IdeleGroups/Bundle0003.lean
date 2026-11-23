module

public import Mathlib
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr
public import GroundTheory.GlobalFields.IdeleGroups.Restricted
public import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap

@[expose] public section

-- bundled from GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles
section
namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Topology
open scoped NumberField.AdeleRing

noncomputable section

namespace AdeleBaseChange

section Ext

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem adeleRingHom_ext {R : Type*} [Semiring R] {f g : 𝔸[L] →+* R}
    (hL : ∀ l : L, f (algebraMap L 𝔸[L] l) = g (algebraMap L 𝔸[L] l))
    (hK : ∀ a : 𝔸[K], f (adeleMap K L a) = g (adeleMap K L a)) : f = g := by
  ext y
  obtain ⟨t, rfl⟩ := (adeleTensorEquiv K L).surjective y
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [adeleTensorEquiv_tmul, map_mul, map_mul, hL, hK]
  | add s t hs ht => rw [map_add (f := _), map_add (f := _), map_add (f := _), hs, ht]

theorem adeleTensorEquiv_symm_algebraMap (l : L) :
    (adeleTensorEquiv K L).symm (algebraMap L 𝔸[L] l) = l ⊗ₜ 1 := by
  rw [AlgEquiv.symm_apply_eq, adeleTensorEquiv_tmul, map_one, mul_one]

theorem adeleTensorEquiv_symm_adeleMap (a : 𝔸[K]) :
    (adeleTensorEquiv K L).symm (adeleMap K L a) = 1 ⊗ₜ a := by
  rw [AlgEquiv.symm_apply_eq, adeleTensorEquiv_tmul, map_one, one_mul]

end Ext

section Transport

variable {L L' L'' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Field L'']
  [NumberField L'']

def adeleRingEquiv (τ : L ≃+* L') : 𝔸[L] ≃+* 𝔸[L'] :=
  ((adeleTensorEquiv ℚ L).symm.toRingEquiv.trans
    (Algebra.TensorProduct.congr τ.toRatAlgEquiv (AlgEquiv.refl : 𝔸[ℚ] ≃ₐ[ℚ] 𝔸[ℚ])).toRingEquiv).trans
    (adeleTensorEquiv ℚ L').toRingEquiv

@[simp]
theorem adeleRingEquiv_algebraMap (τ : L ≃+* L') (l : L) :
    adeleRingEquiv τ (algebraMap L 𝔸[L] l) = algebraMap L' 𝔸[L'] (τ l) := by
  change adeleTensorEquiv ℚ L' (Algebra.TensorProduct.congr τ.toRatAlgEquiv AlgEquiv.refl
    ((adeleTensorEquiv ℚ L).symm (algebraMap L 𝔸[L] l))) = _
  rw [adeleTensorEquiv_symm_algebraMap, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    adeleTensorEquiv_tmul]
  simp

@[simp]
theorem adeleRingEquiv_adeleMap_rat (τ : L ≃+* L') (a : 𝔸[ℚ]) :
    adeleRingEquiv τ (adeleMap ℚ L a) = adeleMap ℚ L' a := by
  change adeleTensorEquiv ℚ L' (Algebra.TensorProduct.congr τ.toRatAlgEquiv AlgEquiv.refl
    ((adeleTensorEquiv ℚ L).symm (adeleMap ℚ L a))) = _
  rw [adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul]
  simp

theorem adeleRingHom_ext_rat {R : Type*} [Semiring R] {f g : 𝔸[L] →+* R}
    (hL : ∀ l : L, f (algebraMap L 𝔸[L] l) = g (algebraMap L 𝔸[L] l))
    (hQ : ∀ a : 𝔸[ℚ], f (adeleMap ℚ L a) = g (adeleMap ℚ L a)) : f = g :=
  adeleRingHom_ext hL hQ

@[simp]
theorem adeleRingEquiv_refl : adeleRingEquiv (RingEquiv.refl L) = RingEquiv.refl 𝔸[L] := by
  apply RingEquiv.toRingHom_injective
  refine adeleRingHom_ext_rat (fun l ↦ ?_) (fun a ↦ ?_)
  · exact adeleRingEquiv_algebraMap _ l
  · exact adeleRingEquiv_adeleMap_rat _ a

theorem adeleRingEquiv_trans (τ : L ≃+* L') (τ' : L' ≃+* L'') :
    adeleRingEquiv (τ.trans τ') = (adeleRingEquiv τ).trans (adeleRingEquiv τ') := by
  apply RingEquiv.toRingHom_injective
  refine adeleRingHom_ext_rat (fun l ↦ ?_) (fun a ↦ ?_)
  · change adeleRingEquiv (τ.trans τ') _ = adeleRingEquiv τ' (adeleRingEquiv τ _)
    rw [adeleRingEquiv_algebraMap, adeleRingEquiv_algebraMap, adeleRingEquiv_algebraMap]
    rfl
  · change adeleRingEquiv (τ.trans τ') _ = adeleRingEquiv τ' (adeleRingEquiv τ _)
    rw [adeleRingEquiv_adeleMap_rat, adeleRingEquiv_adeleMap_rat, adeleRingEquiv_adeleMap_rat]

theorem adeleRingEquiv_symm (τ : L ≃+* L') :
    adeleRingEquiv τ.symm = (adeleRingEquiv τ).symm := by
  ext x
  apply (adeleRingEquiv τ).injective
  rw [RingEquiv.apply_symm_apply, ← RingEquiv.trans_apply, ← adeleRingEquiv_trans,
    RingEquiv.symm_trans_self, adeleRingEquiv_refl, RingEquiv.refl_apply]

theorem continuous_adeleRingEquiv (τ : L ≃+* L') : Continuous (adeleRingEquiv τ) := by
  have : IsModuleTopology 𝔸[ℚ] 𝔸[L] := isModuleTopology_adeleRing
  let f : 𝔸[L] →ₗ[𝔸[ℚ]] 𝔸[L'] :=
    { toFun := adeleRingEquiv τ
      map_add' := map_add _
      map_smul' := fun c x ↦ by
        simp only [Algebra.smul_def, algebraMap_adeleRing, map_mul, adeleRingEquiv_adeleMap_rat,
          RingHom.id_apply] }
  exact IsModuleTopology.continuous_of_linearMap f

end Transport

section Relative

variable {K L L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field L']
  [NumberField L'] [Algebra K L] [Algebra K L']

@[simp]
theorem adeleRingEquiv_adeleMap (τ : L ≃ₐ[K] L') (a : 𝔸[K]) :
    adeleRingEquiv (τ : L ≃+* L') (adeleMap K L a) = adeleMap K L' a := by
  have h : ((adeleRingEquiv (τ : L ≃+* L')).toRingHom.comp (adeleMap K L) : 𝔸[K] →+* 𝔸[L']) =
      adeleMap K L' := by
    refine adeleRingHom_ext_rat (fun k ↦ ?_) (fun a ↦ ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, adeleMap_algebraMap, adeleRingEquiv_algebraMap]
      simp
    · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, adeleMap_adeleMap, adeleRingEquiv_adeleMap_rat]
  exact congrArg (fun f : 𝔸[K] →+* 𝔸[L'] ↦ f a) h


variable (K) in
def adeleAlgEquiv (τ : L ≃ₐ[K] L') : 𝔸[L] ≃ₐ[𝔸[K]] 𝔸[L'] :=
  AlgEquiv.ofRingEquiv (f := adeleRingEquiv (τ : L ≃+* L')) fun a ↦ adeleRingEquiv_adeleMap τ a

theorem norm_adeleRingEquiv (τ : L ≃ₐ[K] L') (x : 𝔸[L]) :
    Algebra.norm 𝔸[K] (adeleRingEquiv (τ : L ≃+* L') x) = Algebra.norm 𝔸[K] x :=
  Algebra.norm_eq_of_algEquiv (adeleAlgEquiv K τ) x

end Relative

end AdeleBaseChange

open AdeleBaseChange

section Idele

variable {L L' L'' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Field L'']
  [NumberField L'']

def ideleEquiv (τ : L ≃+* L') : IdeleGroup L ≃ₜ* IdeleGroup L' where
  toMulEquiv := Units.mapEquiv (adeleRingEquiv τ).toMulEquiv
  continuous_toFun := Continuous.units_map (adeleRingEquiv τ).toMonoidHom (continuous_adeleRingEquiv τ)
  continuous_invFun := by
    have h := Continuous.units_map (adeleRingEquiv τ.symm).toMonoidHom
      (continuous_adeleRingEquiv τ.symm)
    rw [adeleRingEquiv_symm] at h
    exact h

@[simp]
theorem coe_ideleEquiv (τ : L ≃+* L') (x : IdeleGroup L) :
    ((ideleEquiv τ x : IdeleGroup L') : 𝔸[L']) = adeleRingEquiv τ (x : 𝔸[L]) :=
  rfl

@[simp]
theorem ideleEquiv_refl (x : IdeleGroup L) : ideleEquiv (RingEquiv.refl L) x = x :=
  Units.ext (by rw [coe_ideleEquiv, adeleRingEquiv_refl, RingEquiv.refl_apply])

theorem ideleEquiv_trans (τ : L ≃+* L') (τ' : L' ≃+* L'') (x : IdeleGroup L) :
    ideleEquiv (τ.trans τ') x = ideleEquiv τ' (ideleEquiv τ x) :=
  Units.ext (by rw [coe_ideleEquiv, coe_ideleEquiv, coe_ideleEquiv, adeleRingEquiv_trans,
    RingEquiv.trans_apply])

@[simp]
theorem ideleEquiv_diagonal (τ : L ≃+* L') (l : Lˣ) :
    ideleEquiv τ (IdeleGroup.diagonal L l) =
      IdeleGroup.diagonal L' (Units.map (τ : L →* L') l) :=
  Units.ext (adeleRingEquiv_algebraMap τ (l : L))

theorem map_range_diagonal (τ : L ≃+* L') :
    (IdeleGroup.diagonal L).range.map (ideleEquiv τ).toMulEquiv.toMonoidHom =
      (IdeleGroup.diagonal L').range := by
  ext y
  constructor
  · rintro ⟨_, ⟨l, rfl⟩, rfl⟩
    exact ⟨_, (ideleEquiv_diagonal τ l).symm⟩
  · rintro ⟨l', rfl⟩
    refine ⟨IdeleGroup.diagonal L (Units.map (τ.symm : L' →* L) l'), ⟨_, rfl⟩, ?_⟩
    change ideleEquiv τ _ = _
    rw [ideleEquiv_diagonal]
    congr 1
    ext
    simp

def ideleClassEquiv (τ : L ≃+* L') : IdeleClassGroup L ≃ₜ* IdeleClassGroup L' where
  toMulEquiv := QuotientGroup.congr _ _ (ideleEquiv τ).toMulEquiv (map_range_diagonal τ)
  continuous_toFun := by
    refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    exact (IdeleClassGroup.continuous_mk L').comp (ideleEquiv τ).continuous
  continuous_invFun := by
    refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    exact (IdeleClassGroup.continuous_mk L).comp (ideleEquiv τ).symm.continuous

@[simp]
theorem ideleClassEquiv_mk (τ : L ≃+* L') (x : IdeleGroup L) :
    ideleClassEquiv τ (IdeleClassGroup.mk L x) = IdeleClassGroup.mk L' (ideleEquiv τ x) :=
  rfl

@[simp]
theorem ideleClassEquiv_refl (c : IdeleClassGroup L) : ideleClassEquiv (RingEquiv.refl L) c = c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  rw [ideleClassEquiv_mk, ideleEquiv_refl]

theorem ideleClassEquiv_trans (τ : L ≃+* L') (τ' : L' ≃+* L'') (c : IdeleClassGroup L) :
    ideleClassEquiv (τ.trans τ') c = ideleClassEquiv τ' (ideleClassEquiv τ c) := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  rw [ideleClassEquiv_mk, ideleClassEquiv_mk, ideleClassEquiv_mk, ideleEquiv_trans]

end Idele

section Relative

variable {K L L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field L']
  [NumberField L'] [Algebra K L] [Algebra K L']

@[simp]
theorem ideleNorm_ideleEquiv (τ : L ≃ₐ[K] L') (x : IdeleGroup L) :
    ideleNorm K L' (ideleEquiv (τ : L ≃+* L') x) = ideleNorm K L x :=
  Units.ext (norm_adeleRingEquiv τ (x : 𝔸[L]))

@[simp]
theorem ideleClassNorm_ideleClassEquiv (τ : L ≃ₐ[K] L') (c : IdeleClassGroup L) :
    ideleClassNorm K L' (ideleClassEquiv (τ : L ≃+* L') c) = ideleClassNorm K L c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  rw [ideleClassEquiv_mk, ideleClassNorm_mk, ideleClassNorm_mk, ideleNorm_ideleEquiv]

end Relative

end

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.IdeleGroups.LocalNorms
section
namespace GroundTheory.Global

open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing NumberField.LiesOver

noncomputable section

namespace IdeleNorm

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]

def finiteLocalNorm (v : HeightOneSpectrum (𝓞 K)) :
    ((w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) →* (v.adicCompletion K)ˣ where
  toFun y := ∏ w, Units.map (Algebra.norm (v.adicCompletion K) :
    w.1.adicCompletion L →* v.adicCompletion K) (y w)
  map_one' := by simp
  map_mul' y z := by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]


variable {L} in
theorem coe_finiteLocalNorm (v : HeightOneSpectrum (𝓞 K))
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    ((finiteLocalNorm L v y : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      ∏ w, Algebra.norm (v.adicCompletion K) (y w : w.1.adicCompletion L) := by
  simp [finiteLocalNorm, Units.coe_prod]

def integerUnitsOver (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup ((w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :=
  Subgroup.pi Set.univ fun w ↦ (Submonoid.ofClass (w.1.adicCompletionIntegers L)).units


omit [NumberField K] in
variable {L} in
theorem mem_integerUnitsOver {v : HeightOneSpectrum (𝓞 K)}
    {y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ} :
    y ∈ integerUnitsOver L v ↔
      ∀ w, y w ∈ (Submonoid.ofClass (w.1.adicCompletionIntegers L)).units := by
  simp [integerUnitsOver, Subgroup.mem_pi]


open scoped Classical in
def infiniteLocalNorm (v : InfinitePlace K) :
    ((w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ) →* (v.Completion)ˣ where
  toFun y := ∏ w : v.placesOver L, Units.map (Algebra.norm v.Completion :
    (w : InfinitePlace L).Completion →* v.Completion) (y w)
  map_one' := by simp
  map_mul' y z := by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]


omit [NumberField K] in
open scoped Classical in
variable {L} in
theorem coe_infiniteLocalNorm (v : InfinitePlace K)
    (y : (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ) :
    ((infiniteLocalNorm L v y : (v.Completion)ˣ) : v.Completion) =
      ∏ w : v.placesOver L, Algebra.norm v.Completion (y w : (w : InfinitePlace L).Completion) := by
  simp [infiniteLocalNorm, Units.coe_prod]

variable {L}

theorem finiteProj_ideleNorm (y : IdeleGroup L) (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup.finiteProj v (ideleNorm K L y) =
      finiteLocalNorm L v (fun w ↦ IdeleGroup.finiteProj w.1 y) := by
  apply Units.ext
  simpa only [IdeleGroup.coe_finiteProj, coe_finiteLocalNorm] using ideleNorm_snd y v

theorem infiniteProj_ideleNorm (y : IdeleGroup L) (v : InfinitePlace K) :
    IdeleGroup.infiniteProj v (ideleNorm K L y) =
      infiniteLocalNorm L v (fun w ↦ IdeleGroup.infiniteProj (w : InfinitePlace L) y) := by
  classical
  apply Units.ext
  simpa only [IdeleGroup.coe_infiniteProj, coe_infiniteLocalNorm] using ideleNorm_fst y v

theorem eventually_finiteProj_mem (y : IdeleGroup L) :
    ∀ᶠ w in cofinite,
      IdeleGroup.finiteProj w y ∈ (Submonoid.ofClass (w.adicCompletionIntegers L)).units := by
  refine (IdeleGroup.prodRestrictedEquiv L y).2.2.mono fun w hw ↦ ?_
  have e : IdeleGroup.finiteProj w y = (IdeleGroup.prodRestrictedEquiv L y).2 w :=
    Units.ext (by simp)
  rw [e]
  exact hw


omit [NumberField K] [NumberField L] in
variable (K) in
theorem eventually_forall_placesOver {P : HeightOneSpectrum (𝓞 L) → Prop}
    (h : ∀ᶠ w in cofinite, P w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ∀ w : PlacesOver L v, P w.1 := by
  rw [eventually_cofinite] at h ⊢
  refine (h.image (below (K := K))).subset fun v hv ↦ ?_
  simp only [Set.mem_ofPred_eq, not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.1, hw, HeightOneSpectrum.ext w.2.over.symm⟩


omit [NumberField K] in
theorem placesOver_congr (yf : ∀ v : HeightOneSpectrum (𝓞 K),
      (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    {v v' : HeightOneSpectrum (𝓞 K)} (h : v' = v) (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal) (hw' : w.asIdeal.LiesOver v'.asIdeal) :
    yf v' ⟨w, hw'⟩ = yf v ⟨w, hw⟩ := by
  subst h
  rfl


omit [NumberField K] [NumberField L] in
theorem infinitePlacesOver_congr (yi : ∀ v : InfinitePlace K,
      (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ)
    {v v' : InfinitePlace K} (h : v' = v) (w : InfinitePlace L)
    (hw : w ∈ v.placesOver L) (hw' : w ∈ v'.placesOver L) :
    yi v' ⟨w, hw'⟩ = yi v ⟨w, hw⟩ := by
  subst h
  rfl

def glue (yf : ∀ v : HeightOneSpectrum (𝓞 K), (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    (hyf : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v)
    (yi : ∀ v : InfinitePlace K, (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ) :
    IdeleGroup L := by
  have hbelow : Tendsto (below (K := K) (L := L)) cofinite cofinite := by
    refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v ↦ ?_
    refine ((Set.finite_range (Subtype.val : PlacesOver L v → HeightOneSpectrum (𝓞 L))).subset
      fun w hw ↦ ?_).to_subtype
    exact ⟨⟨w, ⟨congrArg HeightOneSpectrum.asIdeal hw.symm⟩⟩, rfl⟩
  exact (IdeleGroup.prodRestrictedEquiv L).symm
    (MulEquiv.piUnits.symm fun w : InfinitePlace L ↦
        yi (w.comap (algebraMap K L)) ⟨w, (inferInstance : w.LiesOver (w.comap (algebraMap K L)))⟩,
      ⟨fun w ↦ yf (below (K := K) w) ⟨w, ⟨rfl⟩⟩,
        (hbelow.eventually hyf).mono fun w hw ↦
          mem_integerUnitsOver.1 hw ⟨w, ⟨rfl⟩⟩⟩)

theorem glue_snd (yf : ∀ v : HeightOneSpectrum (𝓞 K),
      (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    (hyf : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v)
    (yi : ∀ v : InfinitePlace K, (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) :
    ((glue yf hyf yi : 𝔸[L]).2 w.1) = (yf v w : w.1.adicCompletion L) := by
  rw [← IdeleGroup.prodRestrictedEquiv_apply_snd, glue, ContinuousMulEquiv.apply_symm_apply]
  exact congrArg Units.val (placesOver_congr yf (HeightOneSpectrum.ext w.2.over.symm) w.1 w.2 _)

theorem glue_fst (yf : ∀ v : HeightOneSpectrum (𝓞 K),
      (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    (hyf : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v)
    (yi : ∀ v : InfinitePlace K, (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ)
    (v : InfinitePlace K) (w : v.placesOver L) :
    ((glue yf hyf yi : 𝔸[L]).1 w) = (yi v w : (w : InfinitePlace L).Completion) := by
  rw [← IdeleGroup.prodRestrictedEquiv_apply_fst, glue, ContinuousMulEquiv.apply_symm_apply]
  have := infinitePlacesOver_congr yi (InfinitePlace.LiesOver.comap_eq (w : InfinitePlace L) v)
    (w : InfinitePlace L) w.2
    (inferInstance : (w : InfinitePlace L).LiesOver ((w : InfinitePlace L).comap (algebraMap K L)))
  exact congrArg Units.val this

theorem ideleNorm_glue (yf : ∀ v : HeightOneSpectrum (𝓞 K),
      (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    (hyf : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v)
    (yi : ∀ v : InfinitePlace K, (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ)
    {x : IdeleGroup K} (hf : ∀ v, finiteLocalNorm L v (yf v) = IdeleGroup.finiteProj v x)
    (hi : ∀ v, infiniteLocalNorm L v (yi v) = IdeleGroup.infiniteProj v x) :
    ideleNorm K L (glue yf hyf yi) = x := by
  classical
  apply Units.ext
  refine Prod.ext (funext fun v ↦ ?_) (FiniteAdeleRing.ext (K := K) fun v ↦ ?_)
  · rw [ideleNorm_fst, ← IdeleGroup.coe_infiniteProj, ← hi v, coe_infiniteLocalNorm]
    exact Finset.prod_congr rfl fun w _ ↦ by rw [glue_fst]
  · rw [ideleNorm_snd, ← IdeleGroup.coe_finiteProj, ← hf v, coe_finiteLocalNorm]
    exact Finset.prod_congr rfl fun w _ ↦ by rw [glue_snd]

theorem mem_range_ideleNorm (x : IdeleGroup K)
    (hfin : ∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range)
    (hinf : ∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range)
    (hint : ∀ᶠ v in cofinite,
      IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v)) :
    x ∈ (ideleNorm K L).range := by
  classical
  let yf : ∀ v : HeightOneSpectrum (𝓞 K), (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ :=
    fun v ↦ if h : IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v)
      then (Subgroup.mem_map.1 h).choose else (MonoidHom.mem_range.1 (hfin v)).choose
  have hyf_int : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v := hint.mono fun v h ↦ by
    simp only [yf, dif_pos h]
    exact (Subgroup.mem_map.1 h).choose_spec.1
  have hyf : ∀ v, finiteLocalNorm L v (yf v) = IdeleGroup.finiteProj v x := by
    intro v
    by_cases h : IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v)
    · simp only [yf, dif_pos h]
      exact (Subgroup.mem_map.1 h).choose_spec.2
    · simp only [yf, dif_neg h]
      exact (MonoidHom.mem_range.1 (hfin v)).choose_spec
  exact ⟨glue yf hyf_int (fun v ↦ (MonoidHom.mem_range.1 (hinf v)).choose),
    ideleNorm_glue _ _ _ hyf fun v ↦ (MonoidHom.mem_range.1 (hinf v)).choose_spec⟩

theorem mem_range_ideleNorm_iff (x : IdeleGroup K) :
    x ∈ (ideleNorm K L).range ↔
      (∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range) ∧
      (∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range) ∧
      ∀ᶠ v in cofinite,
        IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v) := by
  refine ⟨?_, fun ⟨h1, h2, h3⟩ ↦ mem_range_ideleNorm x h1 h2 h3⟩
  rintro ⟨y, rfl⟩
  refine ⟨fun v ↦ ⟨_, (finiteProj_ideleNorm y v).symm⟩,
    fun v ↦ ⟨_, (infiniteProj_ideleNorm y v).symm⟩, ?_⟩
  refine (eventually_forall_placesOver K (eventually_finiteProj_mem y)).mono fun v hv ↦ ?_
  exact ⟨_, mem_integerUnitsOver.2 hv, (finiteProj_ideleNorm y v).symm⟩

end IdeleNorm

end

end GroundTheory.Global
end

