module

public import Mathlib
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup

@[expose] public section

-- bundled from GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups
section
namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

def sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (IdeleGroup K) where
  carrier := {x | ∀ v ∉ S, ord v x = 0}
  one_mem' v _ := ord_one v
  mul_mem' {x y} hx hy v hv := by rw [ord_mul, hx v hv, hy v hv, add_zero]
  inv_mem' {x} hx v hv := by rw [ord_inv, hx v hv, neg_zero]

variable (S : Set (HeightOneSpectrum (𝓞 K)))

theorem mem_sIdeles {x : IdeleGroup K} : x ∈ sIdeles S ↔ ∀ v ∉ S, ord v x = 0 :=
  Iff.rfl

theorem mem_sIdeles_iff {x : IdeleGroup K} :
    x ∈ sIdeles S ↔ ∀ v ∉ S, (x : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K ∧
      ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K := by
  simp only [mem_sIdeles, ord_eq_zero_iff]

theorem standardOpenSubgroup_le_sIdeles : standardOpenSubgroup K ≤ sIdeles S :=
  fun _ hx v _ ↦ mem_standardOpenSubgroup_iff_ord.1 hx v

theorem sIdeles_mono {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    sIdeles S ≤ sIdeles T :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (h hvS)

theorem neg_log_eq_zero_iff {y : ℤᵐ⁰} (hy : y ≠ 0) : -log y = 0 ↔ y = 1 := by
  rw [neg_eq_zero]
  constructor
  · intro h
    rw [← exp_log hy, h, exp_zero]
  · rintro rfl
    exact log_one

theorem diagonal_mem_sIdeles_iff (a : Kˣ) : diagonal K a ∈ sIdeles S ↔ a ∈ S.unit K := by
  have ha : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (a : K) ≠ 0 := fun v ↦
    (Valuation.ne_zero_iff _).2 a.ne_zero
  simp only [mem_sIdeles, ord_diagonal, neg_log_eq_zero_iff (ha _)]
  rfl

theorem exists_diagonal_mul_of_sup_eq_top (h : (diagonal K).range ⊔ sIdeles S = ⊤)
    (x : IdeleGroup K) : ∃ a : Kˣ, ∃ s ∈ sIdeles S, diagonal K a * s = x := by
  have hx : x ∈ (diagonal K).range ⊔ sIdeles S := h ▸ Subgroup.mem_top x
  obtain ⟨_, ⟨a, rfl⟩, s, hs, hx⟩ := Subgroup.mem_sup.1 hx
  exact ⟨a, s, hs, hx⟩

theorem sup_sIdeles_eq_top_of_subset {S T : Set (HeightOneSpectrum (𝓞 K))} (hST : S ⊆ T)
    (h : (diagonal K).range ⊔ sIdeles S = ⊤) : (diagonal K).range ⊔ sIdeles T = ⊤ :=
  eq_top_iff.2 (h.symm.le.trans (sup_le_sup_left (sIdeles_mono hST) _))

theorem exists_finset_sup_sIdeles_eq_top :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤ := by
  classical
  choose x hx using toClassGroup_surjective (K := K)
  let S : Finset (HeightOneSpectrum (𝓞 K)) := Finset.univ.biUnion fun c ↦
    (Filter.eventually_cofinite.1 (eventually_ord_eq_zero (x c))).toFinset
  have hxS : ∀ c, x c ∈ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) := by
    intro c v hv
    by_contra h
    exact hv (Finset.mem_biUnion.2 ⟨c, Finset.mem_univ c, Set.Finite.mem_toFinset _ |>.2 h⟩)
  refine ⟨S, eq_top_iff.2 fun y _ ↦ ?_⟩
  have hker : y * (x (toClassGroup y))⁻¹ ∈ (toClassGroup (K := K)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx, mul_inv_cancel]
  rw [ker_toClassGroup] at hker
  have h := mul_mem (sup_le_sup_left (standardOpenSubgroup_le_sIdeles _) _ hker)
    (Subgroup.mem_sup_right (hxS (toClassGroup y)))
  rwa [inv_mul_cancel_right] at h

def sUnitsToSIdeles : S.unit K →* sIdeles S :=
  ((diagonal K).comp (S.unit K).subtype).codRestrict (sIdeles S) fun a ↦
    (diagonal_mem_sIdeles_iff S a).2 a.2

@[simp]
theorem coe_sUnitsToSIdeles (a : S.unit K) :
    (sUnitsToSIdeles S a : IdeleGroup K) = diagonal K a :=
  rfl

def sIdelesToIdeleClassGroup : sIdeles S →* IdeleClassGroup K :=
  (IdeleClassGroup.mk K).comp (sIdeles S).subtype

@[simp]
theorem sIdelesToIdeleClassGroup_apply (s : sIdeles S) :
    sIdelesToIdeleClassGroup S s = IdeleClassGroup.mk K s :=
  rfl

theorem sUnitsToSIdeles_injective : Function.Injective (sUnitsToSIdeles S) := fun _ _ h ↦
  Subtype.ext (diagonal_injective K (congrArg Subtype.val h))

theorem range_sUnitsToSIdeles :
    (sUnitsToSIdeles S).range = (sIdelesToIdeleClassGroup S).ker := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    rw [MonoidHom.mem_ker, sIdelesToIdeleClassGroup_apply, coe_sUnitsToSIdeles]
    exact IdeleClassGroup.mk_diagonal K a
  · intro hy
    rw [MonoidHom.mem_ker, sIdelesToIdeleClassGroup_apply, ← MonoidHom.mem_ker,
      IdeleClassGroup.ker_mk] at hy
    obtain ⟨a, ha⟩ := hy
    have haS : a ∈ S.unit K := (diagonal_mem_sIdeles_iff S a).1 (ha ▸ y.2)
    exact ⟨⟨a, haS⟩, Subtype.ext ha⟩

theorem sIdelesToIdeleClassGroup_surjective_iff :
    Function.Surjective (sIdelesToIdeleClassGroup S) ↔ (diagonal K).range ⊔ sIdeles S = ⊤ := by
  constructor
  · intro h
    refine eq_top_iff.2 fun y _ ↦ ?_
    obtain ⟨s, hs⟩ := h (IdeleClassGroup.mk K y)
    rw [sIdelesToIdeleClassGroup_apply] at hs
    have hr : (s : IdeleGroup K)⁻¹ * y ∈ (diagonal K).range := by
      rw [← IdeleClassGroup.ker_mk, MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
    have h' := mul_mem (Subgroup.mem_sup_right (S := (diagonal K).range) s.2)
      (Subgroup.mem_sup_left (T := sIdeles S) hr)
    rwa [mul_inv_cancel_left] at h'
  · intro h c
    obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective K c
    obtain ⟨a, s, hs, rfl⟩ := exists_diagonal_mul_of_sup_eq_top S h y
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [sIdelesToIdeleClassGroup_apply, map_mul, IdeleClassGroup.mk_diagonal]
    exact (one_mul (IdeleClassGroup.mk K s)).symm

theorem sUnits_sIdeles_exact (h : (diagonal K).range ⊔ sIdeles S = ⊤) :
    Function.Injective (sUnitsToSIdeles S) ∧
      (sUnitsToSIdeles S).range = (sIdelesToIdeleClassGroup S).ker ∧
      Function.Surjective (sIdelesToIdeleClassGroup S) :=
  ⟨sUnitsToSIdeles_injective S, range_sUnitsToSIdeles S,
    (sIdelesToIdeleClassGroup_surjective_iff S).2 h⟩

end IdeleGroup

end

end GroundTheory.Global
end

-- bundled from GroundTheory.GlobalFields.IdeleGroups.StandardOpenEquiv
section
namespace GroundTheory.Global

open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing

noncomputable section

theorem continuous_equiv_symm_of_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ Y) (h : X ≃ₜ Y) (he : ∀ x, e x = h x) : Continuous e.symm :=
  h.symm.continuous.congr fun y ↦ e.injective (by rw [e.apply_symm_apply, he, h.apply_symm_apply])

def unitsContinuousMulEquiv {A B : Type*} [Monoid A] [Monoid B] [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃* B) (h₁ : Continuous e) (h₂ : Continuous e.symm) :
    Aˣ ≃ₜ* Bˣ where
  toMulEquiv := Units.mapEquiv e
  continuous_toFun := Units.continuous_map (f := e.toMonoidHom) h₁
  continuous_invFun := Units.continuous_map (f := e.symm.toMonoidHom) h₂

def continuousMulEquivProdCongr {A B C D : Type*} [Monoid A] [Monoid B] [Monoid C] [Monoid D]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    (e₁ : A ≃ₜ* B) (e₂ : C ≃ₜ* D) : A × C ≃ₜ* B × D where
  toMulEquiv := MulEquiv.prodCongr e₁.toMulEquiv e₂.toMulEquiv
  continuous_toFun := by
    exact (e₁.continuous.comp continuous_fst).prodMk (e₂.continuous.comp continuous_snd)
  continuous_invFun := by
    exact (e₁.symm.continuous.comp continuous_fst).prodMk (e₂.symm.continuous.comp continuous_snd)

def openSubgroupEquivQuotient {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H N : Subgroup G) (hH : IsOpen (H : Set G)) (hinf : H ⊓ N = ⊥)
    (hsup : H ⊔ N = ⊤) : H ≃ₜ* G ⧸ N :=
  let f : H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have h2 : (h : G) ∈ H ⊓ N := ⟨h.2, (QuotientGroup.eq_one_iff _).1 hh⟩
    rw [hinf, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hg : g ∈ H ⊔ N := hsup ▸ Subgroup.mem_top g
    obtain ⟨h, hh, n, hn, rfl⟩ := Subgroup.mem_sup.1 hg
    refine ⟨⟨h, hh⟩, ?_⟩
    show ((h : G) : G ⧸ N) = ((h * n : G) : G ⧸ N)
    exact QuotientGroup.eq.2 (by rwa [inv_mul_cancel_left])
  let e : H ≃* G ⧸ N := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have hc : Continuous e := QuotientGroup.continuous_mk.comp continuous_subtype_val
  have ho : IsOpenMap e := QuotientGroup.isOpenMap_coe.comp hH.isOpenMap_subtype_val
  { toMulEquiv := e
    continuous_toFun := hc
    continuous_invFun := (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous }

namespace IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

def localIntegerUnit (v : HeightOneSpectrum (𝓞 K)) (x : standardOpenSubgroup K) :
    (v.adicCompletionIntegers K)ˣ where
  val := ⟨((x : IdeleGroup K) : 𝔸[K]).2 v, ((mem_standardOpenSubgroup K).1 x.2 v).1⟩
  inv := ⟨(((x : IdeleGroup K)⁻¹ : IdeleGroup K) : 𝔸[K]).2 v,
    ((mem_standardOpenSubgroup K).1 x.2 v).2⟩
  val_inv := Subtype.ext (congrArg (fun y : 𝔸[K] ↦ y.2 v) (x : IdeleGroup K).mul_inv)
  inv_val := Subtype.ext (congrArg (fun y : 𝔸[K] ↦ y.2 v) (x : IdeleGroup K).inv_mul)

theorem continuous_localIntegerUnit (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (localIntegerUnit (K := K) v) := by
  rw [Units.continuous_iff]
  constructor
  · exact ((Units.continuous_val.comp (continuous_finiteProj v)).comp
      continuous_subtype_val).subtype_mk _
  · exact ((Units.continuous_coe_inv.comp (continuous_finiteProj v)).comp
      continuous_subtype_val).subtype_mk _

def ofIntegerUnits (a : (InfiniteAdeleRing K)ˣ)
    (u : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) : IdeleGroup K where
  val := ((a : InfiniteAdeleRing K),
    _root_.RestrictedProduct.structureMap _ _ _ fun v ↦ (u v : v.adicCompletionIntegers K))
  inv := (((a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
    _root_.RestrictedProduct.structureMap _ _ _ fun v ↦ ((u v)⁻¹ : (v.adicCompletionIntegers K)ˣ))
  val_inv := Prod.ext a.mul_inv (Subtype.ext (funext fun v ↦ congrArg Subtype.val (u v).mul_inv))
  inv_val := Prod.ext a.inv_mul (Subtype.ext (funext fun v ↦ congrArg Subtype.val (u v).inv_mul))

theorem ofIntegerUnits_mem (a : (InfiniteAdeleRing K)ˣ)
    (u : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) :
    ofIntegerUnits a u ∈ standardOpenSubgroup K :=
  (mem_standardOpenSubgroup K).2 fun v ↦
    ⟨(u v : v.adicCompletionIntegers K).2, (((u v)⁻¹ : (v.adicCompletionIntegers K)ˣ) :
      v.adicCompletionIntegers K).2⟩

theorem continuous_ofIntegerUnits :
    Continuous (fun p : (InfiniteAdeleRing K)ˣ ×
        (Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) ↦
      ofIntegerUnits p.1 p.2) := by
  rw [Units.continuous_iff]
  constructor
  · exact (Units.continuous_val.comp continuous_fst).prodMk
      (_root_.RestrictedProduct.isEmbedding_structureMap.continuous.comp
        (continuous_pi fun v ↦ Units.continuous_val.comp ((continuous_apply v).comp continuous_snd)))
  · exact (Units.continuous_coe_inv.comp continuous_fst).prodMk
      (_root_.RestrictedProduct.isEmbedding_structureMap.continuous.comp
        (continuous_pi fun v ↦
          Units.continuous_coe_inv.comp ((continuous_apply v).comp continuous_snd)))


variable (K) in
def standardOpenSubgroupEquiv :
    standardOpenSubgroup K ≃ₜ* (InfiniteAdeleRing K)ˣ ×
      Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ where
  toFun x := (toInfinite K (x : IdeleGroup K), fun v ↦ localIntegerUnit v x)
  invFun p := ⟨ofIntegerUnits p.1 p.2, ofIntegerUnits_mem p.1 p.2⟩
  left_inv _ := Subtype.ext (Units.ext (Prod.ext rfl (Subtype.ext (funext fun _ ↦ rfl))))
  right_inv _ := Prod.ext (Units.ext rfl) (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  map_mul' x y := Prod.ext (map_mul (toInfinite K) (x : IdeleGroup K) y)
    (funext fun _ ↦ Units.ext (Subtype.ext rfl))
  continuous_toFun := ((continuous_toInfinite K).comp continuous_subtype_val).prodMk
    (continuous_pi fun v ↦ continuous_localIntegerUnit v)
  continuous_invFun := continuous_ofIntegerUnits.subtype_mk _

end IdeleGroup

end

end GroundTheory.Global
end

