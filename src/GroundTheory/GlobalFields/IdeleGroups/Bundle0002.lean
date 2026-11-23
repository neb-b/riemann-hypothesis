module

public import Mathlib
public import GroundTheory.GlobalFields.IdeleGroups.Bundle0001
public import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace

@[expose] public section

-- bundled from GroundTheory.GlobalFields.IdeleGroups.IndexFormula
section
namespace GroundTheory.Global

open NumberField IsDedekindDomain

section GroupLemma

variable {G C : Type*} [Group G] [Group C]

theorem index_map_mul_relIndex_ker {f : G →* C} (hf : Function.Surjective f) (W : Subgroup G)
    [W.Normal] : (W.map f).index * W.relIndex f.ker = W.index := by
  rw [Subgroup.index_map, f.range_eq_top_of_surjective hf, Subgroup.index_top, mul_one,
    ← Subgroup.relIndex_sup_left, mul_comm, Subgroup.relIndex_mul_index le_sup_left]

end GroupLemma

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

variable (S : Set (HeightOneSpectrum (𝓞 K)))

theorem index_comap_sUnitsToSIdeles (W : Subgroup (sIdeles S)) :
    (W.comap (sUnitsToSIdeles S)).index = W.relIndex (sIdelesToIdeleClassGroup S).ker := by
  rw [Subgroup.index_comap, range_sUnitsToSIdeles]

theorem index_map_mul_index_comap (h : (diagonal K).range ⊔ sIdeles S = ⊤)
    (W : Subgroup (sIdeles S)) :
    (W.map (sIdelesToIdeleClassGroup S)).index * (W.comap (sUnitsToSIdeles S)).index =
      W.index := by
  rw [index_comap_sUnitsToSIdeles]
  exact index_map_mul_relIndex_ker ((sIdelesToIdeleClassGroup_surjective_iff S).2 h) W

end IdeleGroup

end

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.IdeleGroups.LocalConditionIndex
section
namespace GroundTheory.Global

open NumberField IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem map_range_powMonoidHom {G H : Type*} [CommGroup G] [CommGroup H] (e : G ≃* H) (n : ℕ) :
    (powMonoidHom n : G →* G).range.map (e : G →* H) = (powMonoidHom n : H →* H).range := by
  ext y
  simp only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, by simp [map_pow]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e.symm x ^ n, ⟨e.symm x, rfl⟩, by simp [map_pow]⟩

theorem index_range_powMonoidHom_of_mulEquiv {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) :
    (powMonoidHom n : G →* G).range.index = (powMonoidHom n : H →* H).range.index := by
  rw [← map_range_powMonoidHom e n, Subgroup.index_map_equiv]


omit [NumberField K] in
open Classical in
theorem index_range_powMonoidHom_infinitePlaceCompletion (w : InfinitePlace K) {n : ℕ}
    (hn : n ≠ 0) :
    letI : Decidable (w.IsReal ∧ Even n) := Classical.propDecidable _
    (powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range.index =
      if w.IsReal ∧ Even n then 2 else 1 := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [index_range_powMonoidHom_of_mulEquiv
      (Units.mapEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMulEquiv) n,
      index_range_powMonoidHom_real hn]
    by_cases he : Even n <;> simp [hw, he]
  · rw [index_range_powMonoidHom_of_mulEquiv
      (Units.mapEquiv (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).toMulEquiv) n,
      index_range_powMonoidHom_complex hn]
    have hw' : ¬w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hw
    simp [hw']

namespace IdeleGroup

@[simp]
theorem finiteProj_infiniteEmbedding (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K)
    (x : (w.Completion)ˣ) : finiteProj v (infiniteEmbedding w x) = 1 :=
  Units.ext rfl

@[simp]
theorem infiniteProj_finiteEmbedding (w : InfinitePlace K) (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : infiniteProj w (finiteEmbedding v x) = 1 :=
  Units.ext rfl

theorem infiniteEmbedding_mem_standardOpenSubgroup (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    infiniteEmbedding w x ∈ standardOpenSubgroup K := by
  rw [mem_standardOpenSubgroup]
  intro v
  rw [← map_inv]
  simp only [coe_infiniteEmbedding]
  exact ⟨one_mem _, one_mem _⟩

def localSubgroup (S T : Set (HeightOneSpectrum (𝓞 K)))
    (H : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
    (H' : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ) : Subgroup (IdeleGroup K) where
  carrier := {x | (∀ v ∈ S, finiteProj v x ∈ H v) ∧ (∀ w, infiniteProj w x ∈ H' w) ∧
    ∀ v ∉ S ∪ T, ord v x = 0}
  one_mem' := ⟨fun v _ ↦ by rw [map_one]; exact one_mem _, fun w ↦ by rw [map_one]; exact one_mem _,
    fun v _ ↦ ord_one v⟩
  mul_mem' {x y} hx hy := ⟨fun v hv ↦ by rw [map_mul]; exact mul_mem (hx.1 v hv) (hy.1 v hv),
    fun w ↦ by rw [map_mul]; exact mul_mem (hx.2.1 w) (hy.2.1 w),
    fun v hv ↦ by rw [ord_mul, hx.2.2 v hv, hy.2.2 v hv, add_zero]⟩
  inv_mem' {x} hx := ⟨fun v hv ↦ by rw [map_inv]; exact inv_mem (hx.1 v hv),
    fun w ↦ by rw [map_inv]; exact inv_mem (hx.2.1 w),
    fun v hv ↦ by rw [ord_inv, hx.2.2 v hv, neg_zero]⟩

variable (S T : Set (HeightOneSpectrum (𝓞 K)))
  (H : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
  (H' : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ)

theorem mem_localSubgroup {x : IdeleGroup K} :
    x ∈ localSubgroup S T H H' ↔ (∀ v ∈ S, finiteProj v x ∈ H v) ∧
      (∀ w, infiniteProj w x ∈ H' w) ∧ ∀ v ∉ S ∪ T, ord v x = 0 :=
  Iff.rfl

theorem localSubgroup_le_sIdeles : localSubgroup S T H H' ≤ sIdeles (S ∪ T) :=
  fun _ hx ↦ hx.2.2

def localQuotientMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T) →*
      (∀ v : S, (v.1.adicCompletion K)ˣ ⧸ H v.1) × (∀ w : InfinitePlace K, (w.Completion)ˣ ⧸ H' w) :=
  MonoidHom.prod
    (MonoidHom.pi fun v ↦ (QuotientGroup.mk' (H v.1)).comp ((finiteProj v.1).comp (sIdeles _).subtype))
    (MonoidHom.pi fun w ↦ (QuotientGroup.mk' (H' w)).comp ((infiniteProj w).comp (sIdeles _).subtype))

theorem ker_localQuotientMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (localQuotientMap T H H' S).ker =
      (localSubgroup S T H H').subgroupOf (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_localSubgroup]
  simp only [localQuotientMap, MonoidHom.prod_apply, Prod.mk_eq_one, funext_iff, Pi.one_apply,
    MonoidHom.pi_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.coe_subtype, Subtype.forall, Finset.mem_coe]
  exact ⟨fun h ↦ ⟨h.1, h.2, x.2⟩, fun h ↦ ⟨h.1, h.2.1⟩⟩

theorem localQuotientMap_surjective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective (localQuotientMap T H H' S) := by
  classical
  rintro ⟨a, b⟩
  choose α hα using fun v : S ↦ QuotientGroup.mk_surjective (a v)
  choose β hβ using fun w ↦ QuotientGroup.mk_surjective (b w)
  let x : IdeleGroup K := (∏ v : S, finiteEmbedding v.1 (α v)) * ∏ w, infiniteEmbedding w (β w)
  have hx : x ∈ sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T) := by
    refine mul_mem (prod_mem fun v _ ↦ ?_) (prod_mem fun w _ ↦ ?_)
    · intro u hu
      exact ord_finiteEmbedding_of_ne (fun h ↦ hu (Or.inl (by rw [h]; exact Finset.mem_coe.2 v.2))) _
    · exact standardOpenSubgroup_le_sIdeles _ (infiniteEmbedding_mem_standardOpenSubgroup w _)
  have hfin : ∀ v : S, finiteProj v.1 x = α v := by
    intro v
    simp only [x, map_mul, map_prod, finiteProj_infiniteEmbedding, Finset.prod_const_one, mul_one]
    rw [Finset.prod_eq_single v (fun u _ hu ↦
      finiteProj_finiteEmbedding_of_ne (fun h ↦ hu (Subtype.ext h.symm)) _) (by simp),
      finiteProj_finiteEmbedding]
  have hinf : ∀ w : InfinitePlace K, infiniteProj w x = β w := by
    intro w
    simp only [x, map_mul, map_prod, infiniteProj_finiteEmbedding, Finset.prod_const_one, one_mul]
    rw [Finset.prod_eq_single w (fun u _ hu ↦
      infiniteProj_infiniteEmbedding_of_ne (fun h ↦ hu h.symm) _) (by simp),
      infiniteProj_infiniteEmbedding]
  refine ⟨⟨x, hx⟩, Prod.ext (funext fun v ↦ ?_) (funext fun w ↦ ?_)⟩
  · exact (congrArg (QuotientGroup.mk (s := H v.1)) (hfin v)).trans (hα v)
  · exact (congrArg (QuotientGroup.mk (s := H' w)) (hinf w)).trans (hβ w)

theorem relIndex_localSubgroup (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (localSubgroup S T H H').relIndex (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) =
      (∏ v ∈ S, (H v).index) * ∏ w : InfinitePlace K, (H' w).index := by
  have hk := Subgroup.index_ker (G' := (∀ v : S, (v.1.adicCompletion K)ˣ ⧸ H v.1) ×
    (∀ w : InfinitePlace K, (w.Completion)ˣ ⧸ H' w)) (localQuotientMap T H H' S)
  rw [Subgroup.relIndex, ← ker_localQuotientMap, hk,
    MonoidHom.range_eq_top_of_surjective _ (localQuotientMap_surjective T H H' S),
    Subgroup.card_top, Nat.card_prod, Nat.card_pi, Nat.card_pi, ← Finset.prod_coe_sort S]
  rfl

def powerSubgroup (n : ℕ) (S T : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup K) :=
  localSubgroup S T (fun v ↦ (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range)
    (fun w ↦ (powMonoidHom n : (w.Completion)ˣ →* _).range)

theorem powerSubgroup_le_sIdeles (n : ℕ) : powerSubgroup n S T ≤ sIdeles (S ∪ T) :=
  localSubgroup_le_sIdeles S T _ _

theorem relIndex_powerSubgroup (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (powerSubgroup n S T).relIndex (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) =
      (∏ v ∈ S, (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range.index) *
        ∏ w : InfinitePlace K, (powMonoidHom n : (w.Completion)ˣ →* _).range.index :=
  relIndex_localSubgroup T _ _ S

theorem relIndex_powerSubgroup_empty (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (powerSubgroup n S ∅).relIndex (sIdeles (S : Set (HeightOneSpectrum (𝓞 K)))) =
      (∏ v ∈ S, (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range.index) *
        ∏ w : InfinitePlace K, (powMonoidHom n : (w.Completion)ˣ →* _).range.index := by
  have h := relIndex_powerSubgroup (K := K) ∅ n S
  rwa [Set.union_empty] at h

end IdeleGroup

end

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.IdeleGroups.Rational
section
namespace GroundTheory.Global

open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing

noncomputable section

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

namespace RationalIdeles

open IdeleGroup

theorem isReal_infinitePlace (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

def realEquiv : InfiniteAdeleRing ℚ ≃+* ℝ :=
  (RingEquiv.piUnique fun w : InfinitePlace ℚ ↦ w.Completion).trans
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_infinitePlace default))

theorem realEquiv_apply (x : InfiniteAdeleRing ℚ) :
    realEquiv x = InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (isReal_infinitePlace default) (x default) :=
  rfl

theorem continuous_realEquiv : Continuous realEquiv :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous.comp
    (continuous_apply _)

theorem continuous_realEquiv_symm : Continuous realEquiv.symm := by
  exact continuous_equiv_symm_of_eq realEquiv.toEquiv
    ((Homeomorph.piUnique fun w : InfinitePlace ℚ ↦ w.Completion).trans
      (InfinitePlace.Completion.isometryEquivRealOfIsReal
        (isReal_infinitePlace default)).toHomeomorph)
    fun _ ↦ rfl

def realUnitsEquiv : (InfiniteAdeleRing ℚ)ˣ ≃ₜ* ℝˣ :=
  unitsContinuousMulEquiv realEquiv.toMulEquiv continuous_realEquiv continuous_realEquiv_symm

def realPart : IdeleGroup ℚ →* ℝˣ :=
  realUnitsEquiv.toMulEquiv.toMonoidHom.comp (toInfinite ℚ)

theorem coe_realPart (x : IdeleGroup ℚ) : (realPart x : ℝ) = realEquiv (x : 𝔸[ℚ]).1 :=
  rfl

theorem continuous_realPart : Continuous realPart :=
  realUnitsEquiv.continuous.comp (continuous_toInfinite ℚ)

@[simp]
theorem realPart_diagonal (a : ℚˣ) : (realPart (diagonal ℚ a) : ℝ) = a := by
  rw [coe_realPart, coe_diagonal]
  exact eq_ratCast (realEquiv.toRingHom.comp (algebraMap ℚ (InfiniteAdeleRing ℚ))) a

theorem realPart_ofIntegerUnits (a : (InfiniteAdeleRing ℚ)ˣ)
    (u : Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) :
    realPart (ofIntegerUnits a u) = realUnitsEquiv a :=
  rfl

def positiveSubgroup : Subgroup (IdeleGroup ℚ) :=
  standardOpenSubgroup ℚ ⊓ (Units.posSubgroup ℝ).comap realPart

theorem mem_positiveSubgroup {x : IdeleGroup ℚ} :
    x ∈ positiveSubgroup ↔ x ∈ standardOpenSubgroup ℚ ∧ 0 < (realPart x : ℝ) := by
  rw [positiveSubgroup, Subgroup.mem_inf, Subgroup.mem_comap, Units.mem_posSubgroup]

theorem isOpen_positiveSubgroup : IsOpen (positiveSubgroup : Set (IdeleGroup ℚ)) := by
  have h : (positiveSubgroup : Set (IdeleGroup ℚ)) =
      (standardOpenSubgroup ℚ : Set (IdeleGroup ℚ)) ∩ {x | 0 < (realPart x : ℝ)} := by
    ext x
    exact mem_positiveSubgroup
  rw [h]
  exact (isOpen_standardOpenSubgroup ℚ).inter
    (isOpen_lt continuous_const (Units.continuous_val.comp continuous_realPart))

theorem diagonal_mem_standardOpenSubgroup_iff (a : ℚˣ) :
    diagonal ℚ a ∈ standardOpenSubgroup ℚ ↔ (a : ℚ) = 1 ∨ (a : ℚ) = -1 := by
  rw [← ker_toFractionalIdeal, MonoidHom.mem_ker, toFractionalIdeal_diagonal,
    toPrincipalIdeal_eq_iff, Units.val_one, ← FractionalIdeal.spanSingleton_one,
    FractionalIdeal.spanSingleton_eq_spanSingleton]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : ((z : 𝓞 ℚ) : ℚ) * a = 1 := by
      rw [Units.smul_def, Algebra.smul_def] at hz
      exact hz
    rcases Rat.RingOfIntegers.isUnit_iff.1 z.isUnit with h | h
    · left
      rwa [h, one_mul] at hz'
    · right
      rwa [h, neg_one_mul, neg_eq_iff_eq_neg] at hz'
  · rintro (h | h)
    · exact ⟨1, by rw [one_smul, h]⟩
    · exact ⟨-1, by rw [Units.neg_smul, one_smul, h, neg_neg]⟩

theorem positiveSubgroup_inf_diagonal_range : positiveSubgroup ⊓ (diagonal ℚ).range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, a, rfl⟩
  obtain ⟨h1, h2⟩ := mem_positiveSubgroup.1 hx
  rw [realPart_diagonal] at h2
  rw [Subgroup.mem_bot]
  rcases (diagonal_mem_standardOpenSubgroup_iff a).1 h1 with h | h
  · rw [show a = 1 from Units.ext h, map_one]
  · rw [h] at h2
    norm_num at h2

theorem subsingleton_classGroup : Subsingleton (ClassGroup (𝓞 ℚ)) := by
  have h := Rat.classNumber_eq
  rw [NumberField.classNumber] at h
  exact Fintype.card_le_one_iff_subsingleton.1 h.le

theorem positiveSubgroup_sup_diagonal_range : positiveSubgroup ⊔ (diagonal ℚ).range = ⊤ := by
  have htop : (diagonal ℚ).range ⊔ standardOpenSubgroup ℚ = ⊤ := by
    rw [← IdeleGroup.ker_toClassGroup, eq_top_iff]
    intro x _
    have := subsingleton_classGroup
    exact Subsingleton.elim _ _
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ (diagonal ℚ).range ⊔ standardOpenSubgroup ℚ := htop ▸ Subgroup.mem_top x
  obtain ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩ := Subgroup.mem_sup.1 hx
  rcases lt_or_gt_of_ne (realPart u).ne_zero with hneg | hpos
  · have hm : diagonal ℚ (-1) ∈ standardOpenSubgroup ℚ :=
      (diagonal_mem_standardOpenSubgroup_iff (-1)).2 (Or.inr (by simp))
    have hp : diagonal ℚ (-1) * u ∈ positiveSubgroup := by
      refine mem_positiveSubgroup.2 ⟨mul_mem hm hu, ?_⟩
      rw [map_mul, Units.val_mul, realPart_diagonal]
      push_cast
      linarith
    refine Subgroup.mem_sup.2 ⟨_, hp, diagonal ℚ (-a), ⟨-a, rfl⟩, ?_⟩
    rw [mul_right_comm, ← map_mul, neg_one_mul, neg_neg]
  · exact Subgroup.mem_sup.2 ⟨u, mem_positiveSubgroup.2 ⟨hu, hpos⟩, diagonal ℚ a, ⟨a, rfl⟩,
      mul_comm _ _⟩

def positiveSubgroupEquivIdeleClassGroup : positiveSubgroup ≃ₜ* IdeleClassGroup ℚ :=
  openSubgroupEquivQuotient _ _ isOpen_positiveSubgroup positiveSubgroup_inf_diagonal_range
    positiveSubgroup_sup_diagonal_range

@[simp]
theorem positiveSubgroupEquivIdeleClassGroup_apply (x : positiveSubgroup) :
    positiveSubgroupEquivIdeleClassGroup x = IdeleClassGroup.mk ℚ x :=
  rfl

def positiveSubgroupEquiv : positiveSubgroup ≃ₜ* Units.posSubgroup ℝ ×
    Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ where
  toFun x := (⟨realPart x, (Units.mem_posSubgroup _).2 (mem_positiveSubgroup.1 x.2).2⟩,
    (standardOpenSubgroupEquiv (K := ℚ) ⟨x, (mem_positiveSubgroup.1 x.2).1⟩).2)
  invFun p := ⟨ofIntegerUnits (realUnitsEquiv.symm p.1) p.2, mem_positiveSubgroup.2
    ⟨ofIntegerUnits_mem _ _, by
      rw [realPart_ofIntegerUnits, ContinuousMulEquiv.apply_symm_apply]
      exact (Units.mem_posSubgroup _).1 p.1.2⟩⟩
  left_inv x := by
    have h : realUnitsEquiv.symm (realPart x) = toInfinite ℚ x :=
      realUnitsEquiv.symm_apply_apply _
    apply Subtype.ext
    change ofIntegerUnits (realUnitsEquiv.symm (realPart x)) _ = (x : IdeleGroup ℚ)
    rw [h]
    exact Units.ext (Prod.ext rfl (Subtype.ext (funext fun _ ↦ rfl)))
  right_inv p := Prod.ext (Subtype.ext (realUnitsEquiv.apply_symm_apply _))
    (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  map_mul' x y := Prod.ext (Subtype.ext (map_mul realPart (x : IdeleGroup ℚ) y))
    (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  continuous_toFun := by
    exact ((continuous_realPart.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp ((standardOpenSubgroupEquiv (K := ℚ)).continuous.comp
        (continuous_subtype_val.subtype_mk _)))
  continuous_invFun := by
    exact (continuous_subtype_val.comp ((standardOpenSubgroupEquiv (K := ℚ)).symm.continuous.comp
      ((realUnitsEquiv.symm.continuous.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd))).subtype_mk _

def integersRingEquiv :
    (Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) ≃+* Π p : Nat.Primes, ℤ_[p] :=
  (RingEquiv.piCongrRight fun v ↦
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv).trans
    (RingEquiv.piCongrLeft (fun p : Nat.Primes ↦ ℤ_[p]) Rat.HeightOneSpectrum.primesEquiv)

def integersHomeomorph :
    (Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) ≃ₜ Π p : Nat.Primes, ℤ_[p] :=
  (Homeomorph.piCongrRight fun v ↦
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph).trans
    (Homeomorph.piCongrLeft (Y := fun p : Nat.Primes ↦ ℤ_[p]) Rat.HeightOneSpectrum.primesEquiv)

theorem integersRingEquiv_eq_integersHomeomorph (x : Π v : HeightOneSpectrum (𝓞 ℚ),
    v.adicCompletionIntegers ℚ) : integersRingEquiv x = integersHomeomorph x :=
  rfl

theorem continuous_integersRingEquiv : Continuous integersRingEquiv :=
  integersHomeomorph.continuous.congr fun x ↦ (integersRingEquiv_eq_integersHomeomorph x).symm

theorem continuous_integersRingEquiv_symm : Continuous integersRingEquiv.symm := by
  exact continuous_equiv_symm_of_eq integersRingEquiv.toEquiv integersHomeomorph
    integersRingEquiv_eq_integersHomeomorph

def integerUnitsEquiv :
    (Π v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ)ˣ) ≃ₜ*
      (Π p : Nat.Primes, ℤ_[p])ˣ :=
  ContinuousMulEquiv.piUnits.symm.trans
    (unitsContinuousMulEquiv integersRingEquiv.toMulEquiv continuous_integersRingEquiv
      continuous_integersRingEquiv_symm)

def mulMap : ℚˣ × positiveSubgroup →* IdeleGroup ℚ :=
  (diagonal ℚ).coprod positiveSubgroup.subtype

theorem mulMap_apply (p : ℚˣ × positiveSubgroup) :
    mulMap p = diagonal ℚ p.1 * (p.2 : IdeleGroup ℚ) :=
  rfl

theorem mulMap_bijective : Function.Bijective mulMap := by
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨a, u⟩ h
    have h' : diagonal ℚ a * (u : IdeleGroup ℚ) = 1 := h
    have hu : (u : IdeleGroup ℚ)⁻¹ ∈ positiveSubgroup ⊓ (diagonal ℚ).range :=
      ⟨positiveSubgroup.inv_mem u.2, a, eq_inv_of_mul_eq_one_left h'⟩
    rw [positiveSubgroup_inf_diagonal_range, Subgroup.mem_bot, inv_eq_one] at hu
    have ha : diagonal ℚ a = 1 := by rwa [hu, mul_one] at h'
    exact Prod.ext (diagonal_injective ℚ (ha.trans (map_one _).symm)) (Subtype.ext hu)
  · intro x
    have hx : x ∈ positiveSubgroup ⊔ (diagonal ℚ).range :=
      positiveSubgroup_sup_diagonal_range ▸ Subgroup.mem_top x
    obtain ⟨u, hu, _, ⟨a, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hx
    exact ⟨(a, ⟨u, hu⟩), mul_comm _ _⟩

def ideleClassGroupEquiv : IdeleClassGroup ℚ ≃ₜ* Units.posSubgroup ℝ × (Π p : Nat.Primes, ℤ_[p])ˣ :=
  positiveSubgroupEquivIdeleClassGroup.symm.trans (positiveSubgroupEquiv.trans
    (continuousMulEquivProdCongr (ContinuousMulEquiv.refl _) integerUnitsEquiv))

theorem ideleClassGroupEquiv_mk (x : positiveSubgroup) :
    ideleClassGroupEquiv (IdeleClassGroup.mk ℚ x) =
      (⟨realPart x, (Units.mem_posSubgroup _).2 (mem_positiveSubgroup.1 x.2).2⟩,
        integerUnitsEquiv (positiveSubgroupEquiv x).2) := by
  simp only [ideleClassGroupEquiv, ContinuousMulEquiv.trans_apply]
  rw [← positiveSubgroupEquivIdeleClassGroup_apply, ContinuousMulEquiv.symm_apply_apply]
  rfl

end RationalIdeles

end

end GroundTheory.Global
end

