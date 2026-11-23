module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0153
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.InfNormConjugateInvariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConjPt

open _root_.GlobalTheory.CompanionTheory.Ar (dualMap)

variable {S : Scheme.{0}} {R : Type} [CommRing R]

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : B →+* C) (b : A →+* B) :
    spMap a ≫ spMap b = spMap (a.comp b) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_spMap_assoc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : B →+* C) (b : A →+* B)
    {T : Scheme.{0}} (g : Sp A ⟶ T) : spMap a ≫ spMap b ≫ g = spMap (a.comp b) ≫ g := by
  rw [← Category.assoc, spMap_spMap]

theorem spMap_idR (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ :=
  Spec.map_id (CommRingCat.of A)

theorem algebraMap_dual (a : R) : algebraMap R (DualNumber R) a = TrivSqZeroExt.inl a := rfl

theorem dualMap_comp_algebraMap (f : R →+* R) :
    (dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R (DualNumber R)).comp f := by
  ext a <;> simp [dualMap, algebraMap_dual]

theorem dualMap_comp_epsMul (f : R →+* R) (c : R) :
    (dualMap f).comp (epsMul c) = (epsMul (f c)).comp (dualMap f) := by
  ext a <;> simp [dualMap, epsMul, algebraMap_dual]

theorem fst_comp_dualMap (f : R →+* R) :
    (TrivSqZeroExt.fstHom R R R).toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  ext a <;> simp [dualMap, algebraMap_dual]

theorem dualMap_comp_dualMap (f : R →+* R) (hf : ∀ a, f (f a) = a) :
    (dualMap f).comp (dualMap f) = RingHom.id _ := by
  ext a <;> simp [dualMap, hf, algebraMap_dual]

def trM (f : R →+* R) {x x' : Sp R ⟶ S} (hx : x' = spMap f ≫ x) : epsAt x' ⟶ epsAt x :=
  Over.homMk (spMap (dualMap f)) (by
    subst hx
    change spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) ≫ x =
      spMap (algebraMap R (DualNumber R)) ≫ spMap f ≫ x
    rw [spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_algebraMap])

def tr (f : R →+* R) {x x' : Sp R ⟶ S} (hx : x' = spMap f ≫ x) {G : Over S} (v : epsAt x ⟶ G) : epsAt x' ⟶ G :=
  trM f hx ≫ v

theorem tr_left (f : R →+* R) {x x' : Sp R ⟶ S} (hx : x' = spMap f ≫ x) {G : Over S} (v : epsAt x ⟶ G) :
    (tr f hx v).left = spMap (dualMap f) ≫ v.left := rfl

variable {G : Over S} [GrpObj G] {x x' : Sp R ⟶ S}

theorem tr_mul (f : R →+* R) (hx : x' = spMap f ≫ x) (a b : epsAt x ⟶ G) :
    tr f hx (a * b) = tr f hx a * tr f hx b :=
  MonObj.comp_mul _ _ _

theorem tr_one (f : R →+* R) (hx : x' = spMap f ≫ x) : tr f hx (1 : epsAt x ⟶ G) = 1 := by
  rw [tr, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (trM f hx ≫ toUnit _) (toUnit _)]

def trHom (f : R →+* R) (hx : x' = spMap f ≫ x) : (epsAt x ⟶ G) →* (epsAt x' ⟶ G) where
  toFun := tr f hx
  map_one' := tr_one f hx
  map_mul' := tr_mul f hx

theorem tr_prod (f : R →+* R) (hx : x' = spMap f ≫ x) {n : ℕ} (u : Fin n → (epsAt x ⟶ G)) :
    tr f hx (List.ofFn u).prod = (List.ofFn fun i => tr f hx (u i)).prod := by
  have := map_list_prod (trHom (G := G) f hx) (List.ofFn u)
  rw [List.map_ofFn] at this
  exact this

theorem isTanAt_tr (f : R →+* R) (hx : x' = spMap f ≫ x) {v : epsAt x ⟶ G} (h : IsTanAt G x v) :
    IsTanAt G x' (tr f hx v) := by
  have h1 : (1 : Over.mk x' ⟶ G) = (Over.homMk (spMap f) hx.symm : Over.mk x' ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ G) := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
  unfold IsTanAt at h ⊢
  rw [h1, Over.comp_left, ← h, tr_left]
  change spMap _ ≫ spMap (dualMap f) ≫ v.left = spMap f ≫ spMap _ ≫ v.left
  rw [spMap_spMap_assoc, spMap_spMap_assoc, fst_comp_dualMap]

theorem isEigVec_tr {O : Type} [CommRing O] (act : OAct O G) (f : R →+* R) (hx : x' = spMap f ≫ x) {τ : O →+* R}
    {v : epsAt x ⟶ G} (h : IsEigVec act x τ v) : IsEigVec act x' (f.comp τ) (tr f hx v) := by
  refine ⟨isTanAt_tr f hx h.1, fun a => ?_⟩
  have h2 : (tr f hx v ≫ act.act a).left = spMap (dualMap f) ≫ (v ≫ act.act a).left := by
    rw [tr, Category.assoc]; rfl
  rw [h2, h.2 a, tr_left, spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_epsMul]

theorem isComb_tr (f : R →+* R) (hx : x' = spMap f ≫ x) {n : ℕ} {c : Fin n → R} {v : Fin n → (epsAt x ⟶ G)}
    {w : epsAt x ⟶ G} (h : IsComb c v w) : IsComb (fun i => f (c i)) (fun i => tr f hx (v i)) (tr f hx w) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => tr f hx (u i), fun i => ?_, tr_prod f hx u⟩
  rw [tr_left, hu, tr_left, spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_epsMul]

theorem back (f : R →+* R) (hf : ∀ a, f (f a) = a) (hx : x' = spMap f ≫ x) : x = spMap f ≫ x' := by
  have : f.comp f = RingHom.id R := RingHom.ext hf
  rw [hx, spMap_spMap_assoc, this, spMap_idR, Category.id_comp]

theorem tr_tr (f : R →+* R) (hf : ∀ a, f (f a) = a) (hx : x' = spMap f ≫ x) (hx' : x = spMap f ≫ x')
    (v : epsAt x ⟶ G) : tr f hx' (tr f hx v) = v := by
  apply Over.OverMorphism.ext
  rw [tr_left, tr_left, spMap_spMap_assoc, dualMap_comp_dualMap f hf, spMap_idR, Category.id_comp]

theorem isEigFrame_tr {O : Type} [CommRing O] (act : OAct O G) (f : R →+* R) (hf : ∀ a, f (f a) = a)
    (hx : x' = spMap f ≫ x) {τ : O →+* R} {n : ℕ} {v : Fin n → (epsAt x ⟶ G)} (h : IsEigFrame act x τ v) :
    IsEigFrame act x' (f.comp τ) (fun i => tr f hx (v i)) := by
  have hx' := back f hf hx
  refine ⟨fun i => isEigVec_tr act f hx (h.1 i), fun w hw => ?_⟩
  have hw0 : IsEigVec act x τ (tr f hx' w) := by
    have := isEigVec_tr act f hx' hw
    have e : f.comp (f.comp τ) = τ := RingHom.ext fun a => hf _
    rwa [e] at this
  obtain ⟨c, hc, hu⟩ := h.2 _ hw0
  refine ⟨fun i => f (c i), ?_, fun c' hc' => ?_⟩
  · have := isComb_tr f hx hc
    rwa [tr_tr f hf hx' hx] at this
  · have h3 := isComb_tr f hx' hc'
    simp only [tr_tr f hf hx hx'] at h3
    have h4 := hu _ h3
    funext i
    rw [← h4]
    exact (hf _).symm

end GlobalTheory.CompanionTheory.Ar.Flat.ConjPt

namespace GlobalTheory.CompanionTheory.Ar.Flat


open ConjPt in
theorem hasInfNorm_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (s : c.F →+* ℂ) (t : ℝ), IsLineFn U τ φ → HasInfNorm U τ φ s t → HasInfNorm U τ φ ((starRingEnd ℂ).comp s) t := by
  intro E _ _ _ H D l Xo c U τ φ s t hl hs y v w Γ Δ hfr hΓ hΔ
  have hcc : ∀ z : ℂ, (starRingEnd ℂ) ((starRingEnd ℂ) z) = z := fun z => Complex.conj_conj z
  obtain ⟨h1, h2, h3, h4⟩ := hfr
  have hy : under (spMap (starRingEnd ℂ) ≫ y) = spMap (starRingEnd ℂ) ≫ under y := Category.assoc _ _ _
  have hcomp : ∀ {A : Type} [CommRing A] (g : A →+* ℂ), (starRingEnd ℂ).comp ((starRingEnd ℂ).comp g) = g :=
    fun g => RingHom.ext fun a => hcc _
  let v' : Vecs (spMap (starRingEnd ℂ) ≫ y) D.p := fun i => tr (starRingEnd ℂ) hy (v i)
  let w' : Vecs (spMap (starRingEnd ℂ) ≫ y) D.q := fun i => tr (starRingEnd ℂ) hy (w i)
  have hfr' : IsFramed U τ s (spMap (starRingEnd ℂ) ≫ y) v' w' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, h1, spMap_spMap, hcomp]
    · rintro _ ⟨a, rfl⟩
      exact h2 ⟨(spMap (starRingEnd ℂ)) a, by simp⟩
    · have := isEigFrame_tr Xo.univ.t.act (starRingEnd ℂ) hcc hy h3
      have e : (starRingEnd ℂ).comp (((starRingEnd ℂ).comp s).comp (tauIn c τ)) = s.comp (tauIn c τ) :=
        RingHom.ext fun a => hcc _
      rwa [e] at this
    · have := isEigFrame_tr Xo.univ.t.act (starRingEnd ℂ) hcc hy h4
      have e : (starRingEnd ℂ).comp (((starRingEnd ℂ).comp s).comp (tauIn c (ComplexEmbedding.conjugate τ))) =
          s.comp (tauIn c (ComplexEmbedding.conjugate τ)) := RingHom.ext fun a => hcc _
      rwa [e] at this
  have hΓ' := _root_.GlobalTheory.CompanionTheory.Ar.Flat.isHodgeGram_conj _ Xo.univ.t.G Xo.univ.t.PP.L (under y) _ _ v v' Γ hy (fun a => tr_left _ hy _) hΓ
  have hΔ' := _root_.GlobalTheory.CompanionTheory.Ar.Flat.isHodgeGram_conj _ Xo.univ.t.G Xo.univ.t.PP.L (under y) _ _ w w' Δ hy (fun a => tr_left _ hy _) hΔ
  have hnat := hl.nat ℂ ℂ (starRingEnd ℂ) ((starRingEnd ℂ).comp s) y v w (spMap (starRingEnd ℂ) ≫ y) v' w'
    ⟨h1, h2, h3, h4⟩ rfl (fun i => tr_left _ hy _) (fun i => tr_left _ hy _)
  have hm := hs _ v' w' _ _ hfr' hΓ' hΔ'
  have hdet : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ), ‖(M.map star).det‖ = ‖M.det‖ := by
    intro n M
    have : (M.map star).det = (starRingEnd ℂ) M.det := by
      rw [RingHom.map_det]; rfl
    rw [this, RCLike.norm_conj]
  rw [hnat, RCLike.norm_conj, hdet, hdet] at hm
  exact hm

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalIndexFrameLogDet
section
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

theorem place_eq_zpow_ordE (v : FinitePlace L) {x : L} (hx : x ≠ 0) :
    v x = ((Ideal.absNorm v.maximalIdeal.asIdeal : ℕ) : ℝ) ^ (-Formalism.L2.Ker.ordE v.maximalIdeal x) := by
  have hw : IsDedekindDomain.HeightOneSpectrum.valuation L v.maximalIdeal x ≠ 0 := by
    rwa [ne_eq, Valuation.zero_iff]
  rw [← NumberField.FinitePlace.norm_embedding_eq, NumberField.FinitePlace.norm_embedding,
    NumberField.HeightOneSpectrum.adicAbv_def]
  unfold Formalism.L2.Ker.ordE
  rw [neg_neg]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, IsDedekindDomain.HeightOneSpectrum.valuation L v.maximalIdeal x = WithZero.exp k :=
    ⟨_, (WithZero.exp_log hw).symm⟩
  rw [hk, WithZero.log_exp, WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero)]
  simp [WithZero.exp, WithZero.log]

theorem relIndex_map_of_integral (v : FinitePlace L) (S : Matrix (Fin n) (Fin n) L)
    (hS : ∀ i j, v (S i j) ≤ 1) (hdet : S.det ≠ 0) (f : (Fin n → L) →+ (Fin n → L))
    (hf : ∀ x, f x = S *ᵥ x) (Λ : AddSubgroup (Fin n → L)) (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, v (x i) ≤ 1) :
    Λ.map f ≤ Λ ∧ (((Λ.map f).relIndex Λ : ℕ) : ℝ) = (v S.det)⁻¹ := by
  have hint : ∀ a : L, v a ≤ 1 ↔ Formalism.L2.Col.IntAt v.maximalIdeal a := fun a => by
    rw [place_le_one_iff, GlobalTheory.CharValCompare.intAt_iff]
  have hle : Λ.map f ≤ Λ := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hz
    rw [hΛ] at hy ⊢
    intro i
    rw [hf]
    show v (∑ j, S i j * y j) ≤ 1
    exact place_sum_le_one v _ _ (fun j _ => place_mul_le_one v (hS i j) (hy j))
  refine ⟨hle, ?_⟩
  have key := GlobalTheory.IdxDet.relIndex_mulVec L (Fin n) v.maximalIdeal S Λ (Λ.map f) hdet
    (fun x => by rw [hΛ]; exact forall_congr' fun i => hint (x i))
    (fun x => by
      rw [AddSubgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, hf y⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, hf y⟩)
    hle
  rw [place_eq_zpow_ordE v hdet, _root_.zpow_neg, inv_inv]
  have key' := congrArg (fun q : ℚ => (q : ℝ)) key
  push_cast at key'
  exact key'

theorem gIdx_locAt_frame (L : Type) [Field L] [NumberField L] (n : ℕ) (v : FinitePlace L)
    (T : Matrix (Fin n) (Fin n) L) (hdet : T.det ≠ 0) :
    gIdx (locAt v (frame T)).toAddSubgroup
      (locAt v (frame (1 : Matrix (Fin n) (Fin n) L))).toAddSubgroup = Real.log (v T.det) := by
  set Λ := (locAt v (frame (1 : Matrix (Fin n) (Fin n) L))).toAddSubgroup with hΛdef
  have hΛ : ∀ x, x ∈ Λ ↔ ∀ i, v (x i) ≤ 1 := fun x => mem_locAt_frame_one
  obtain ⟨M, hM⟩ : ∃ M : (Fin n → L) →+ (Fin n → L), ∀ x, M x = T *ᵥ x :=
    ⟨(Matrix.mulVecLin T).toAddMonoidHom, fun x => rfl⟩
  have hTΛ : (locAt v (frame T)).toAddSubgroup = Λ.map M := by
    ext x
    rw [Submodule.mem_toAddSubgroup, mem_locAt_frame, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (hΛ y).2 hy, hM y⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, (hΛ y).1 hy, hM y⟩
  have hMinj : Function.Injective M := by
    intro x y hxy
    rw [hM, hM] at hxy
    have h := congrArg (fun z => T⁻¹ *ᵥ z) hxy
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr hdet)] using h
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (NumberField.RingOfIntegers L))
    (Finset.univ : Finset (Fin n × Fin n)) (fun p => T p.1 p.2)
  set c : L := algebraMap (NumberField.RingOfIntegers L) L b with hcdef
  have hc0 : c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hcv : v c ≤ 1 := place_int_le_one v b
  have hcT : ∀ i j, v ((c • T) i j) ≤ 1 := by
    intro i j
    obtain ⟨r, hr⟩ := hb (i, j) (Finset.mem_univ _)
    rw [Matrix.smul_apply]
    have : c • T i j = algebraMap (NumberField.RingOfIntegers L) L r := by
      rw [hr, smul_eq_mul, Algebra.smul_def]
      all_goals rfl
    rw [this]
    exact place_int_le_one v r
  have hcI : ∀ i j, v ((c • (1 : Matrix (Fin n) (Fin n) L)) i j) ≤ 1 := by
    intro i j
    rw [Matrix.smul_apply, Matrix.one_apply]
    split_ifs
    · simpa using hcv
    · simpa using place_int_le_one v 0
  obtain ⟨a, ha⟩ : ∃ a : (Fin n → L) →+ (Fin n → L), ∀ x, a x = c • x :=
    ⟨DistribSMul.toAddMonoidHom _ c, fun x => rfl⟩
  have hdetI : (c • (1 : Matrix (Fin n) (Fin n) L)).det = c ^ n := by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have hdetT : (c • T).det = c ^ n * T.det := by
    rw [Matrix.det_smul, Fintype.card_fin]
  have hcn : c ^ n ≠ 0 := pow_ne_zero _ hc0
  have h1 := relIndex_map_of_integral v (c • (1 : Matrix (Fin n) (Fin n) L)) hcI
    (by rw [hdetI]; exact hcn) a (fun x => by rw [ha]; ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply]) Λ hΛ
  have h2 := relIndex_map_of_integral v (c • T) hcT (by rw [hdetT]; exact mul_ne_zero hcn hdet) (a.comp M)
    (fun x => by
      rw [AddMonoidHom.comp_apply, ha, hM]
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]) Λ hΛ
  have hpos : ∀ y : L, y ≠ 0 → 0 < v y := fun y hy => NumberField.FinitePlace.pos_iff.mpr hy
  have hr1 : (Λ.map a).relIndex Λ ≠ 0 := by
    intro h0
    have := h1.2
    rw [h0, Nat.cast_zero, hdetI] at this
    exact (inv_pos.mpr (hpos _ hcn)).ne' this.symm
  have hr2 : (Λ.map (a.comp M)).relIndex Λ ≠ 0 := by
    intro h0
    have := h2.2
    rw [h0, Nat.cast_zero, hdetT] at this
    exact (inv_pos.mpr (hpos _ (mul_ne_zero hcn hdet))).ne' this.symm
  rw [hTΛ, gIdx_frac Λ M a hMinj (fun x => by rw [ha, hM, hM, ha, Matrix.mulVec_smul]) h1.1 hr1 h2.1 hr2,
    h1.2, h2.2, hdetI, hdetT, Real.log_inv, Real.log_inv]
  have hm : v (c ^ n * T.det) = v (c ^ n) * v T.det := by
    rw [NumberField.FinitePlace.coe_apply, NumberField.FinitePlace.coe_apply,
      NumberField.FinitePlace.coe_apply, map_mul]
  rw [hm, Real.log_mul (hpos _ hcn).ne' (hpos _ hdet).ne']
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
end

