module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsExtensionAffine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.SectionsDescent

open GlobalTheory.FieldBaseChange

def rs {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

theorem rs_rs {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (x : Γ(X, U)) :
    rs k (rs h x) = rs (k.trans h) x := by
  unfold rs
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem rs_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)) : rs h x = x := by
  show (X.presheaf.map (𝟙 _)).hom _ = _
  rw [CategoryTheory.Functor.map_id]; rfl

theorem pre_mono {X Y : Scheme.{0}} (φ : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) : φ ⁻¹ᵁ V ≤ φ ⁻¹ᵁ U :=
  fun _ hy => h hy

theorem app_rs {X Y : Scheme.{0}} (φ : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (φ.app V).hom (rs h x) = rs (pre_mono φ h) ((φ.app U).hom x) :=
  congrArg (fun q => q.hom x) (φ.naturality (homOfLE h).op)

theorem rs_constHom {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    rs h (constHom p U a) = constHom p V a := rs_rs le_top h _

theorem ext_cover {X : Scheme.{0}} {U : X.Opens} {J : Type} (V : J → X.Opens) (hV : ∀ i, V i ≤ U)
    (hc : U ≤ iSup V) {s t : Γ(X, U)} (h : ∀ i, rs (hV i) s = rs (hV i) t) : s = t :=
  X.sheaf.eq_of_locally_eq' V U (fun i => homOfLE (hV i)) hc s t h

theorem le_iSup_affine {X : Scheme.{0}} (U : X.Opens) :
    U ≤ ⨆ V : {V : X.Opens // IsAffineOpen V ∧ V ≤ U}, V.1 := fun x hx => by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hVU⟩, hxV⟩

theorem ext_affine {X : Scheme.{0}} {U : X.Opens} {s t : Γ(X, U)}
    (h : ∀ (V : X.Opens) (_ : IsAffineOpen V) (hV : V ≤ U), rs hV s = rs hV t) : s = t :=
  ext_cover (fun V : {V : X.Opens // IsAffineOpen V ∧ V ≤ U} => V.1) (fun V => V.2.2) (le_iSup_affine U)
    fun V => h V.1 V.2.1 V.2.2

theorem glue_affine {X : Scheme.{0}} (U : X.Opens)
    (f : ∀ (V : X.Opens), IsAffineOpen V → V ≤ U → Γ(X, V))
    (hf : ∀ V W hV hW (hVU : V ≤ U) (h : W ≤ V), rs h (f V hV hVU) = f W hW (h.trans hVU)) :
    ∃ y : Γ(X, U), ∀ V hV (h : V ≤ U), rs h y = f V hV h := by
  obtain ⟨y, hy, -⟩ := X.sheaf.existsUnique_gluing'
    (fun V : {V : X.Opens // IsAffineOpen V ∧ V ≤ U} => V.1) U (fun V => homOfLE V.2.2) (le_iSup_affine U)
    (fun V => f V.1 V.2.1 V.2.2) (fun V V' => by
      refine ext_affine (X := X) (U := V.1 ⊓ V'.1) fun W hW h => ?_
      refine (rs_rs inf_le_left h _).trans (Eq.trans ?_ (rs_rs inf_le_right h _).symm)
      rw [hf _ _ _ hW, hf _ _ _ hW])
  exact ⟨y, fun V hV h => hy ⟨V, hV, h⟩⟩

section Field

variable {K F : Type} [Field K] [Field F] [Algebra K F] {Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of K)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom (algebraMap K F))))

theorem isExtension_affine {U : Y.Opens} (hU : IsAffineOpen U) :
    IsExtension (pullFn H.w (le_refl (p ⁻¹ᵁ U))) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := p ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have po' : IsPushout (CommRingCat.ofHom (constHom π U)) (CommRingCat.ofHom (algebraMap K F)) (p.app U)
      (CommRingCat.ofHom (constHom π' (p ⁻¹ᵁ U))) := by
    refine po.of_iso (Scheme.ΓSpecIso (.of K)) (Iso.refl _) (Scheme.ΓSpecIso (.of F)) (Iso.refl _) ?_ ?_ ?_ ?_
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
  let : Algebra (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) := (p.app U).hom.toAlgebra
  let : Algebra K (FnOver π' (p ⁻¹ᵁ U)) := ((constHom π' (p ⁻¹ᵁ U)).comp (algebraMap K F)).toAlgebra
  have : IsScalarTower K F (FnOver π' (p ⁻¹ᵁ U)) := .of_algebraMap_eq fun r ↦ rfl
  have : IsScalarTower K (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) :=
    .of_algebraMap_eq fun r ↦ (congrArg (fun q => q.hom r) po'.w).symm
  have : Algebra.IsPushout K F (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) :=
    (CommRingCat.isPushout_iff_isPushout.mp po').symm
  exact isExtension_of_isPushout _ fun x => rs_self _ _

theorem coord_mul_rs {V W : Y.Opens} (hV : IsAffineOpen V) (h : W ≤ V) {ℓ : F →ₗ[K] K}
    {Λ : FnOver π' (p ⁻¹ᵁ V) →+ FnOver π V} {Λ' : FnOver π' (p ⁻¹ᵁ W) →+ FnOver π W}
    (hΛ : IsCoord (pullFn H.w (le_refl (p ⁻¹ᵁ V))) ℓ Λ) (hΛ' : IsCoord (pullFn H.w (le_refl (p ⁻¹ᵁ W))) ℓ Λ')
    (u : Γ(Y, W)) (x : Γ(Y', p ⁻¹ᵁ V)) :
    Λ' ((p.app W).hom u * rs (pre_mono p h) x) = u * rs h (Λ x) :=
  IsCoord.natural (isExtension_affine H hV).span hΛ hΛ'
    (LinearMap.mulLeft K (show FnOver π W from u) ∘ₗ resFn π h)
    (LinearMap.mulLeft F (show FnOver π' (p ⁻¹ᵁ W) from (p.app W).hom u) ∘ₗ
      resFn π' (pre_mono p h))
    (fun v => by
      show (p.app W).hom u * rs _ (rs _ ((p.app V).hom v)) = rs _ ((p.app W).hom (u * rs h v))
      rw [rs_self, rs_self, map_mul]
      exact congrArg _ (app_rs p h v).symm) x

theorem exists_coord {ℓ : F →ₗ[K] K}
    (Λ : ∀ V : Y.Opens, IsAffineOpen V → FnOver π' (p ⁻¹ᵁ V) →+ FnOver π V)
    (hΛ : ∀ V hV, IsCoord (pullFn H.w (le_refl (p ⁻¹ᵁ V))) ℓ (Λ V hV)) (U : Y.Opens) (x : Γ(Y', p ⁻¹ᵁ U)) :
    ∃ y : Γ(Y, U), ∀ V hV (h : V ≤ U), rs h y = Λ V hV (rs (pre_mono p h) x) :=
  glue_affine U _ fun V W hV hW hVU h => by
    have := coord_mul_rs H hV h (hΛ V hV) (hΛ W hW) 1 (rs (pre_mono p hVU) x)
    rw [map_one, _root_.one_mul, _root_.one_mul, rs_rs] at this
    exact this.symm

theorem pre_le_chart (M : LB Y) (p : Y' ⟶ Y) (j : PUnit → M.ι) : p ⁻¹ᵁ M.U (j PUnit.unit) ≤ (M.pull p).U j :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy

def loc {M : LB Y} (t : (M.pull p).Sec) (j : M.ι) : Γ(Y', p ⁻¹ᵁ M.U j) :=
  rs (pre_le_chart M p fun _ => j) (t.f fun _ => j)

theorem sec_compat {M : LB Y} (s : M.Sec) (i j : M.ι) {W : Y.Opens} (hi : W ≤ M.U i) (hj : W ≤ M.U j) :
    rs hi (s.f i) = rs (le_inf hi hj) (M.g i j : Γ(Y, M.U i ⊓ M.U j)) * rs hj (s.f j) := by
  have := congrArg (rs (le_inf hi hj)) (s.compat i j)
  rw [map_mul] at this
  exact (rs_rs inf_le_left _ _).symm.trans (this.trans (congrArg _ (rs_rs inf_le_right _ _)))

theorem loc_compat {M : LB Y} (t : (M.pull p).Sec) (i j : M.ι) {W : Y.Opens} (hi : W ≤ M.U i)
    (hj : W ≤ M.U j) :
    rs (pre_mono p hi) (loc t i) =
      (p.app W).hom (rs (le_inf hi hj) (M.g i j : Γ(Y, M.U i ⊓ M.U j))) * rs (pre_mono p hj) (loc t j) := by
  unfold loc
  rw [rs_rs, rs_rs, sec_compat t (fun _ => i) (fun _ => j) ((pre_mono p hi).trans (pre_le_chart M p fun _ => i))
    ((pre_mono p hj).trans (pre_le_chart M p fun _ => j)), app_rs]
  congr 1
  have e : ((M.pull p).g (fun _ => i) (fun _ => j) : Γ(Y', (M.pull p).U (fun _ => i) ⊓ (M.pull p).U fun _ => j)) =
      rs (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) (fun _ => i) PUnit.unit))
        (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) (fun _ => j) PUnit.unit)))
        ((p.app (M.U i ⊓ M.U j)).hom (M.g i j : Γ(Y, M.U i ⊓ M.U j))) := by
    have key : ∀ {G : Type} [CommGroup G] (u : G), ∏ _k : PUnit.{1}, u ^ (1 : ℤ) = u := fun u => by simp
    exact congrArg Units.val (key _)
  rw [e]
  exact rs_rs _ _ _

theorem exists_coord_sec {ℓ : F →ₗ[K] K}
    (Λ : ∀ V : Y.Opens, IsAffineOpen V → FnOver π' (p ⁻¹ᵁ V) →+ FnOver π V)
    (hΛ : ∀ V hV, IsCoord (pullFn H.w (le_refl (p ⁻¹ᵁ V))) ℓ (Λ V hV)) {M : LB Y} (t : (M.pull p).Sec) :
    ∃ s : M.Sec, ∀ j V hV (h : V ≤ M.U j), rs h (s.f j) = Λ V hV (rs (pre_mono p h) (loc t j)) := by
  choose y hy using fun j => exists_coord H Λ hΛ (M.U j) (loc t j)
  refine ⟨⟨y, fun i j => ext_affine fun W hW h => ?_⟩, hy⟩
  have hi : W ≤ M.U i := h.trans inf_le_left
  have hj : W ≤ M.U j := h.trans inf_le_right
  rw [map_mul]
  refine (rs_rs inf_le_left h _).trans (Eq.trans ?_ (congrArg _ (rs_rs inf_le_right h _).symm))
  have := coord_mul_rs H hW le_rfl (hΛ W hW) (hΛ W hW) (rs h (M.g i j : Γ(Y, M.U i ⊓ M.U j)))
    (rs (pre_mono p hj) (loc t j))
  rw [rs_self] at this
  rw [hy i W hW hi, hy j W hW hj, loc_compat t i j hi hj]
  exact this.trans (congrArg _ (rs_self _ _))

include H in
theorem exists_sum_sec [CompactSpace Y] {M : LB Y} (hM : M.IsLB) (t : (M.pull p).Sec) :
    ∃ (J : Type) (S : Finset J) (c : J → F) (s : J → M.Sec), ∀ j : M.ι,
      loc t j = ∑ a ∈ S, constHom π' _ (c a) * (p.app _).hom ((s a).f j) := by
  classical
  let b := Module.Basis.ofVectorSpace K F
  choose Λ hΛ using fun a V (hV : IsAffineOpen V) => (isExtension_affine H hV).coord (b.coord a)
  choose s hs using fun a => exists_coord_sec H (Λ a) (hΛ a) t
  choose S hS hS' using fun j V (hV : IsAffineOpen V) (h : V ≤ M.U j) =>
    exists_expansion b (isExtension_affine H hV).span (fun a => hΛ a V hV) (rs (pre_mono p h) (loc t j))
  have hc : ∀ y : Y, ∃ (j : M.ι) (V : Y.Opens), IsAffineOpen V ∧ V ≤ M.U j ∧ y ∈ V := fun y => by
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ y))
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.1 (le_iSup_affine _ hj)
    exact ⟨j, V.1, V.2.1, V.2.2, hV⟩
  choose J V hV hVJ hy using hc
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y : Y => (V y : Set Y)) (fun y => (V y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩)
  let S₀ := T.biUnion fun y => S (J y) (V y) (hV y) (hVJ y)
  have z : ∀ a ∉ S₀, ∀ j, (s a).f j = 0 := fun a ha j => by
    refine ext_cover (fun y : T => M.U j ⊓ V y) (fun _ => inf_le_left) (fun x hx => ?_) fun y => ?_
    · obtain ⟨y, hyT, hxy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hyT⟩, hx, hxy⟩
    · have z₀ : rs (hVJ y) ((s a).f (J y)) = 0 := (hs a _ _ (hV y) (hVJ y)).trans
        (hS _ _ _ _ a fun h => ha (Finset.mem_biUnion.2 ⟨y, y.2, h⟩))
      rw [sec_compat (s a) j (J y) inf_le_left (inf_le_right.trans (hVJ y)),
        ← rs_rs (hVJ y) inf_le_right, z₀, map_zero, map_zero, mul_zero]
  refine ⟨_, S₀, b, s, fun j => ?_⟩
  refine ext_cover (fun W : {W : Y.Opens // IsAffineOpen W ∧ W ≤ M.U j} => p ⁻¹ᵁ W.1)
    (fun W => pre_mono p W.2.2) (fun x hx => ?_) fun W => ?_
  · obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 (le_iSup_affine (M.U j) (show p x ∈ M.U j from hx))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨W, hW⟩
  · obtain ⟨W, hW, h⟩ := W
    have e : ∀ a, rs (pre_mono p h) (constHom π' _ (b a) * (p.app _).hom ((s a).f j)) =
        constHom π' (p ⁻¹ᵁ W) (b a) *
          rs le_rfl ((p.app W).hom (Λ a W hW (rs (pre_mono p h) (loc t j)))) := fun a => by
      rw [map_mul, rs_constHom, ← app_rs p h, hs a j W hW h, rs_self]
    have e' : rs (pre_mono p h) (loc t j) = ∑ a ∈ S j W hW h ∪ S₀, constHom π' (p ⁻¹ᵁ W) (b a) *
          rs le_rfl ((p.app W).hom (Λ a W hW (rs (pre_mono p h) (loc t j)))) :=
      hS' j W hW h (S j W hW h ∪ S₀) Finset.subset_union_left
    refine e'.trans ((Finset.sum_congr rfl fun a _ => (e a).symm).trans
      ((Finset.sum_subset Finset.subset_union_right fun a _ ha => ?_).symm.trans (map_sum _ _ _).symm))
    rw [z a ha, map_zero, mul_zero, map_zero]

end Field

theorem main : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) [QuasiCompact p₀] [QuasiSeparated p₀] (M : LB X₀), M.IsLB → IsPullback φ p p₀ (spMap i) → ∀ t : (M.pull φ).Sec, ∃ (n : ℕ) (c : Fin n → K) (s : Fin n → M.Sec), ∀ j : PUnit → M.ι, ∀ h : (M.pull φ).U j ≤ φ ⁻¹ᵁ M.U (j PUnit.unit), t.f j = ∑ a, constFn p _ (c a) * (φ.appLE _ _ h).hom ((s a).f (j PUnit.unit)) := by
  intro K₀ K _ _ i X₀ X p₀ p φ _ _ M hM H t
  let := i.toAlgebra
  have : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace p₀
  obtain ⟨J, S, c, s, e⟩ := exists_sum_sec (K := K₀) (F := K) H hM t
  refine ⟨S.card, fun a => c (S.equivFin.symm a), fun a => s (S.equivFin.symm a), fun j h => ?_⟩
  have e₁ : t.f j = rs h (loc t (j PUnit.unit)) := ((rs_rs _ _ _).trans (rs_self _ _)).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e₁, e, map_sum, ← Finset.sum_coe_sort, ← S.equivFin.symm.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, rs_constHom]
  rfl

end GlobalTheory.SectionsDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoThickeningMapOfModEps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.ThickeningIso

theorem bijective_of_mod_eps {K B C D : Type} [Field K] [CommRing B] [CommRing C] [CommRing D]
    (a : DualNumber K →+* B) (φ : B →+* C) (p : C →+* D) (hf : (φ.comp a).Flat)
    (hs : Function.Surjective (p.comp φ))
    (hB : RingHom.ker (p.comp φ) = (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).map a)
    (hC : RingHom.ker p = (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).map (φ.comp a)) :
    Function.Bijective φ := by
  have hk : RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom = Ideal.span {DualNumber.eps} := by
    ext x
    rw [Ideal.mem_span_singleton', RingHom.mem_ker]
    constructor
    · intro hx
      have hx' : x.fst = 0 := hx
      exact ⟨TrivSqZeroExt.inl x.snd, by ext <;> simp [hx']⟩
    · rintro ⟨y, rfl⟩
      change (y * DualNumber.eps).fst = 0
      simp
  have hB' : ∀ b, p (φ b) = 0 → ∃ b', b = b' * a DualNumber.eps := fun b hb => by
    have : b ∈ RingHom.ker (p.comp φ) := hb
    rw [hB, hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at this
    obtain ⟨b', h⟩ := this
    exact ⟨b', h.symm⟩
  have hC' : ∀ c, p c = 0 → ∃ c', c = c' * φ (a DualNumber.eps) := fun c hc => by
    have : c ∈ RingHom.ker p := hc
    rw [hC, hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at this
    obtain ⟨b', h⟩ := this
    exact ⟨b', h.symm⟩
  have he : a DualNumber.eps * a DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hfl : ∀ c, c * φ (a DualNumber.eps) = 0 → p c = 0 := fun c hc => by
    let _ : Algebra (DualNumber K) C := (φ.comp a).toAlgebra
    have : Module.Flat (DualNumber K) C := hf
    obtain ⟨k, m, y, h1, h2⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (R := DualNumber K) (M := C) (f := fun _ : Unit => DualNumber.eps) (x := fun _ => c) (by
        rw [Fintype.sum_unique, Algebra.smul_def, _root_.mul_comm]; exact hc)
    rw [← RingHom.mem_ker, show c = _ from h1 (), hC]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    have h3 := congrArg TrivSqZeroExt.snd (h2 j)
    change (m () j).fst = 0
    simpa using h3
  have h1 : ∀ c, ∃ b c', c = φ b + c' * φ (a DualNumber.eps) := fun c => by
    obtain ⟨b, hb⟩ := hs (p c)
    obtain ⟨c', h⟩ := hC' (c - φ b) (by rw [map_sub, ← hb]; exact sub_self _)
    exact ⟨b, c', by rw [← h]; ring⟩
  refine ⟨(injective_iff_map_eq_zero φ).2 fun b hb => ?_, fun c => ?_⟩
  · obtain ⟨b', rfl⟩ := hB' b (by rw [hb, map_zero])
    obtain ⟨b'', rfl⟩ := hB' b' (hfl _ (by rw [← map_mul, hb]))
    rw [_root_.mul_assoc, he, mul_zero]
  · obtain ⟨b, c', rfl⟩ := h1 c
    obtain ⟨b', c'', rfl⟩ := h1 c'
    refine ⟨b + b' * a DualNumber.eps, ?_⟩
    rw [add_mul, _root_.mul_assoc, ← map_mul φ (a _), he]
    simp

theorem ker_appTop {A C : CommRingCat.{0}} {β : A ⟶ C} (hβ : Function.Surjective β) {Y Z : Scheme.{0}}
    {f : Y ⟶ Spec A} {i : Z ⟶ Y} {f' : Z ⟶ Spec C} (h : IsPullback i f' f (Spec.map β)) [IsAffine Y] :
    RingHom.ker i.appTop.hom =
      (RingHom.ker β.hom).map ((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom := by
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) (isAffineOpen_top _))
  have hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appTop) β i.appTop
      ((Scheme.ΓSpecIso C).inv ≫ f'.appTop) := by
    refine hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    · rw [← Scheme.ΓSpecIso_naturality]
      congr 1
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact PrimeSection.ker_eq_map_of_isPushout hpo' hβ

theorem surjective_fst (K : Type) [Field K] :
    Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩

theorem isIso_of_isAffine_of_isIso_appTop {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [IsIso f.appTop] : IsIso f :=
  (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map f.appTop)))

theorem isIso_of_isAffine {K : Type} [Field K] {Y Y' Z' : Scheme.{0}} [IsAffine Z'] {q : Y ⟶ Sp K}
    {π' : Z' ⟶ Sp (DualNumber K)} {j : Y ⟶ Y'} {e : Y' ⟶ Z'}
    (h : IsPullback j q (e ≫ π') (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (h' : IsPullback (j ≫ e) q π' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (hf : Flat (e ≫ π')) : IsIso e := by
  have hs := surjective_fst K
  have h1 : IsClosedImmersion (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    IsClosedImmersion.spec_of_surjective _ hs
  have h2 : IsClosedImmersion (j ≫ e) := MorphismProperty.of_isPullback h'.flip h1
  have hY : IsAffine Y := isAffine_of_isAffineHom (j ≫ e)
  have hY' : IsAffine Y' := by
    refine AffineThickening.isAffine_of_isPullback_of_sq_eq_bot
      (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs ?_ h
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    have : (x * y : DualNumber K) = 0 := by ext <;> simp [hx', hy']
    exact this
  suffices hh : IsIso e.appTop from isIso_of_isAffine_of_isIso_appTop e
  rw [ConcreteCategory.isIso_iff_bijective]
  have k := ker_appTop (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs h
  have k' := ker_appTop (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs h'
  have hfl : ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ (e ≫ π').appTop).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (.of_bijective (ConcreteCategory.bijective_of_isIso _))
      ((HasRingHomProperty.iff_of_isAffine (P := @Flat)).1 hf)
  have hsur : Function.Surjective (j ≫ e).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (j ≫ e)).2
  rw [Scheme.Hom.comp_appTop] at k k' hfl hsur
  exact bijective_of_mod_eps
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ π'.appTop).hom e.appTop.hom j.appTop.hom
    hfl hsur k' k

theorem isIso_of_mod_eps : ∀ (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (π' : Z' ⟶ Sp (DualNumber ℂ)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  rintro Y Y' Z' q _ π' j _ e h h' hf rfl rfl
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _
    (iSup_affineOpens_eq_top Z')).mpr fun U => ?_
  have : IsAffine U.1 := U.2
  have p1 := (isPullback_morphismRestrict j (e ⁻¹ᵁ U.1))
  have p2 := (isPullback_morphismRestrict e U.1)
  have hw : e ∣_ U.1 ≫ U.1.ι ≫ π' = (e ⁻¹ᵁ U.1).ι ≫ e ≫ π' := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  refine isIso_of_isAffine (K := ℂ) (π' := U.1.ι ≫ π') (j := j ∣_ (e ⁻¹ᵁ U.1))
    (q := (j ⁻¹ᵁ (e ⁻¹ᵁ U.1)).ι ≫ q) ?_ ?_ ?_
  · rw [hw]
    exact p1.paste_vert h
  · exact (p1.paste_horiz p2).paste_vert h'
  · rw [hw]; infer_instance

end GlobalTheory.ThickeningIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FieldBaseChange

theorem flat_spMap {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) : Flat (spMap i) := by
  rw [Flat.SpecMap_iff]
  letI := i.toAlgebra
  exact (inferInstance : Module.Flat K₀ K)

theorem surjective_spMap {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) : Surjective (spMap i) := by
  have : Subsingleton (Sp K₀) := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
  have : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  exact ⟨fun y => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩

section General

variable {U S : Scheme.{0}} (j : U ⟶ S)

theorem pullback_map_left_fst {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback j).map a).left ≫ pullback.fst Y.hom j = pullback.fst X.hom j ≫ a.left :=
  pullback.lift_fst _ _ _

theorem pullback_map_injective [Flat j] [Surjective j] (X Y : Over S) :
    Function.Injective ((Over.pullback j).map : (X ⟶ Y) → _) := fun f g h => by
  have : Epi (pullback.fst X.hom j) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  rw [← cancel_epi (pullback.fst X.hom j), ← pullback_map_left_fst, ← pullback_map_left_fst, h]

theorem isMonHom_of_pullback [Flat j] [Surjective j] {G H : Over S} [MonObj G] [MonObj H] (f : G ⟶ H)
    (hf : IsMonHom ((Over.pullback j).map f)) : IsMonHom f := by
  constructor
  · apply pullback_map_injective j
    have h := hf.one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi] at h
    rw [Functor.map_comp, h]
  · apply pullback_map_injective j
    have h := hf.mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Functor.LaxMonoidal.μ_natural_assoc, Category.assoc,
      cancel_epi] at h
    rw [Functor.map_comp, Functor.map_comp, h]


variable {j} in
theorem isMonHom_iff_of_isGrpPullback [Flat j] [Surjective j] {G H : Over S} [GrpObj G] [GrpObj H]
    {G' H' : Over U} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hG : IsGrpPullback G' G j φ) (hH : IsGrpPullback H' H j ψ) (f' : G' ⟶ H') (f : G ⟶ H)
    (hf : φ ≫ f.left = f'.left ≫ ψ) : IsMonHom f' ↔ IsMonHom f := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G j) hG
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hH (isGrpPullback_pullback H j)
  have e : (Over.pullback j).map f = a.hom ≫ f' ≫ b.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [pullback_map_left_fst, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', ← hf,
        ← Category.assoc, ha']
    · exact (Over.w _).trans (Over.w _).symm
  constructor
  · intro h
    exact isMonHom_of_pullback j f (by rw [e]; infer_instance)
  · intro h
    have e' : f' = a.inv ≫ (Over.pullback j).map f ≫ b.inv := by simp [e]
    rw [e']
    infer_instance

end General

theorem epi_and_isMonHom_iff : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K), (∀ (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀), IsPullback φ p p₀ (spMap i) → Epi φ ∧ Flat φ ∧ Surjective φ ∧ IsAffineHom φ ∧ ∀ U : X₀.Opens, Function.Injective (φ.app U).hom) ∧ ∀ (A₀ B₀ : Over (Sp K₀)) (A B : Over (Sp K)) [GrpObj A₀] [GrpObj B₀] [GrpObj A] [GrpObj B] (φ : A.left ⟶ A₀.left) (ψ : B.left ⟶ B₀.left) (f₀ : A₀ ⟶ B₀) (f : A ⟶ B), IsGrpPullback A A₀ (spMap i) φ → IsGrpPullback B B₀ (spMap i) ψ → φ ≫ f₀.left = f.left ≫ ψ → (IsMonHom f ↔ IsMonHom f₀) := by
  intro K₀ K _ _ i
  have := flat_spMap i
  have := surjective_spMap i
  refine ⟨fun X₀ X p₀ p φ h => ?_, fun A₀ B₀ A B _ _ _ _ φ ψ f₀ f hA hB hf =>
    isMonHom_iff_of_isGrpPullback hA hB f f₀ hf⟩
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip ‹_›
  have : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹_›
  have : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  exact ⟨Flat.epi_of_flat_of_surjective φ, ‹_›, ‹_›, ‹_›, fun U => GlobalTheory.FunDescent.app_injective φ U⟩

end GlobalTheory.FieldBaseChange
end
end

