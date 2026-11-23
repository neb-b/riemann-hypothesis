module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomOfLinearScalingHermForm
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingSmul
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompConstMulMemHolSub
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompRat

theorem const_of_idem_on {Y : Type} [TopologicalSpace Y] {s : Set Y} (hs : IsPreconnected s) {g : Y → ℂ}
    (hg : ContinuousOn g s) (hi : ∀ x ∈ s, g x * g x = g x) : ∃ w : ℂ, ∀ x ∈ s, g x = w := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · exact ⟨0, fun _ h => h.elim⟩
  refine ⟨g x0, fun x hx => ?_⟩
  have hfin : (g '' s).Finite := by
    refine (Set.toFinite ({0, 1} : Set ℂ)).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    have h := hi y hy
    have : g y * (g y - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  exact hs.constant_of_mapsTo hfin.isDiscrete hg (Set.mapsTo_image g s) hx hx0

theorem rdU_mul_apply' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (f f' : Rul Xo c) (k : U.Comp) (x : Frame (U.X k).Ψ r) :
    rdU U (f * f') k x = rdU U f k x * rdU U f' k x := by
  by_cases h : x ∈ (U.X k).dom
  · have e1 : ∀ g : Rul Xo c, rdU U g k x = toC (evR Xo c g (U.un k ⟨x, h⟩)) := fun g => dif_pos h
    rw [e1, e1, e1]
    exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f f' (U.un k ⟨x, h⟩)
  · rw [rdU_mem_offZero U _ k x h, rdU_mem_offZero U f k x h, zero_mul]

end GlobalTheory.CompRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompMulMemHolSub
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompRat

theorem compMul_mem_holSub {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (w : Comp → ℂ) {P : FDSec X}
    (hP : P ∈ holSub X la) : (fun k x => w k * P k x) ∈ holSub X la := by
  unfold holSub at hP
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
    exact holCusp_mem_holSub X la fun k =>
      (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 (w k) (Q k) (hQ k)
  | zero =>
    have : (fun k x => w k * (0 : FDSec X) k x) = (0 : FDSec X) := by
      funext k x; simp
    rw [this]; exact Submodule.zero_mem _
  | add Q R _ _ hQ hR =>
    have : (fun k x => w k * (Q + R) k x) =
        ((fun k x => w k * Q k x) + (fun k x => w k * R k x) : FDSec X) := by
      funext k x; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ hQ hR
  | smul a Q _ hQ =>
    have : (fun k x => w k * (a • Q) k x) = (a • (fun k x => w k * Q k x) : FDSec X) := by
      funext k x; simp [mul_left_comm]
    rw [this]; exact Submodule.smul_mem _ _ hQ

theorem holSub_compMul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (w : Comp → ℂ) (P : FDSec X), (P ∈ holSub X la → (fun k x => w k * P k x) ∈ holSub X la) ∧ (P ∈ holSub0 X la → (fun k x => w k * P k x) ∈ holSub0 X la) := by
  intro E _ _ _ r Comp X la w P
  refine ⟨compMul_mem_holSub X la w, fun h => ⟨compMul_mem_holSub X la w h.1, fun k x hx => ?_⟩⟩
  have h0 : P k x = 0 := h.2 k x hx
  show w k * P k x = 0
  rw [h0, mul_zero]

end GlobalTheory.CompRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsChartEigenframe
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ModuliChart

theorem exists_sec_of_secOn {X X' S S' : Scheme.{0}} {p : X ⟶ S} {p' : X' ⟶ S'} {t : S' ⟶ S} {F : X' ⟶ X}
    (hF : IsPullback F p' p t) {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull F))
    {V : S.Opens} (hV : ∀ y, t y ∈ V) {θ : ∀ i, Γ(X, p ⁻¹ᵁ V ⊓ L.U i)} (hθ : θ ∈ secOn L (p ⁻¹ᵁ V))
    (hne : ∀ y ∈ V, ∃ (g : X) (i : L.ι), p g = y ∧ g ∈ X.basicOpen (θ i)) :
    ∃ th : L'.Sec, ∀ y : S', ∃ x : X', p' x = y ∧ x ∈ Out.nonzeroLocus th := by
  obtain ⟨w, hw⟩ := hw
  have hFV : ∀ y : X', p (F y) ∈ V := fun y => by
    rw [← Scheme.Hom.comp_apply, hF.w, Scheme.Hom.comp_apply]; exact hV _
  have le : ∀ j, F ⁻¹ᵁ L.U j ≤ F ⁻¹ᵁ (p ⁻¹ᵁ V ⊓ L.U j) := fun j y hy => ⟨hFV y, hy⟩
  have val : ∀ (y : X') j, F y ∈ L.U j → gs (𝟙 X') y _ ((F.appLE _ _ (le j)).hom (θ j)) =
      (F.stalkMap y).hom (gs (𝟙 X) (F y) _ (θ j)) := fun y j h => by
    rw [gs_appLE F _ _ (le j) (𝟙 X') y h, Category.id_comp, gs_stalkMap F y _ (le j h)]
  obtain ⟨th, hth⟩ := sec_down ((isGen_iff w).1 hw) hL hL' (fun j => (F.appLE _ _ (le j)).hom (θ j))
    fun y j j' h h' => by
      rw [val y j h, val y j' h', LBGerm.gs_secOn hθ (F y) j j' (hFV y) h h', map_mul]
      congr 1
      have := PushInv.gm_comp F (𝟙 X) y (L.U j ⊓ L.U j') ⟨h, h'⟩ (L.g j j')
      rw [Category.comp_id] at this
      exact this.symm
  refine ⟨th, fun y => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := hne (t y) (hV y)
  obtain ⟨x, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback hF g y hg
  obtain rfl : F x = g := h₁
  obtain ⟨k, hk⟩ := exists_chart hL' x
  have hm : F x ∈ p ⁻¹ᵁ V ⊓ L.U i := X.basicOpen_le _ hi
  refine ⟨x, h₂, (SectionBaseChange.mem_nonzeroLocus th _).2 ⟨k, hk, ?_⟩⟩
  have e := hth _ (𝟙 _) x i k hm.2 hk
  rw [val x i hm.2] at e
  have hu : IsUnit (gs (𝟙 X) (F x) _ (θ i)) := by
    rw [gs_eq (𝟙 X) (F x) _ hm]
    exact (X.mem_basicOpen _ _ hm).1 hi
  exact isUnit_of_mul_isUnit_right (e ▸ hu.map (F.stalkMap x).hom)

theorem exists_away_point {R : Type} [CommRing R] (p : PrimeSpectrum R) {r : R} (hr : r ∉ p.asIdeal) :
    ∃ q : PrimeSpectrum (Localization.Away r), spMap (algebraMap R (Localization.Away r)) q = p := by
  have h : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  exact h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_pull {B : Type} [CommRing B] {b : Base l B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} (s' : S' ⟶ Sp B)
    (f : S' ⟶ S) (h : f ≫ s = s') (o : Obj D l b s) : ∃ o' : Obj D l b s', Nonempty (ObjMap o' o f) :=
  ObjPull.objPull_of_pol pol_pull E H D l B B b b (RingHom.id B) S S' s s' f rfl rfl
    (h.trans ((Category.comp_id _).symm.trans (congrArg (s' ≫ ·) (Spec.map_id _).symm))) o

theorem objMap_comp {B : Type} [CommRing B] {b : Base l B} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    {s'' : S'' ⟶ Sp B} {o : Obj D l b s} {o' : Obj D l b s'} {o'' : Obj D l b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (m' : ObjMap o'' o' f') (m : ObjMap o' o f) : Nonempty (ObjMap o'' o (f' ≫ f)) := by
  obtain ⟨n, -⟩ := ((ObjMaps.id_comp_cancel E H D l B B B b b b S S' S'' s s' s'' o o' o'').2 f f' m).1 m'
  exact ⟨n⟩

theorem exists_eigen_chart (c : Coeff l) {g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H D.p D.q ty)
    {R : Type} [CommRing R] (j : c.F →+* R)
    (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (p : Sp R) :
    ∃ (R' : Type) (_ : CommRing R') (f : R →+* R')
      (o' : Obj D l (baseKA l) (spMap (f.comp j) ≫ spMap (IntermediateField.inclusion c.le).toRingHom))
      (v : Fin g → (epsR R' ⟶ o'.t.G)), IsOpenImmersion (spMap f) ∧ p ∈ Set.range (spMap f) ∧
      Nonempty (ObjMap o' o (spMap f)) ∧ IsLieBasis v ∧
      ∀ i a, (v i ≫ o'.t.act.act a).left =
        spMap (epsScaleR (f.comp j ⟨ty i (a : E), c.conj (ty i) a⟩)) ≫ (v i).left := by
  obtain ⟨r, hr, v₀, hv₀⟩ := LieLoc.lie_locally_free R o.t.G _ (ObjDim.smoothOfRelativeDimension o) p
  obtain ⟨p₁, hp₁⟩ := exists_away_point p hr
  let R₁ := Localization.Away r
  let f₁ : R →+* R₁ := algebraMap R R₁
  obtain ⟨o₁, ⟨m₁⟩⟩ := exists_pull
    (spMap (f₁.comp j) ≫ spMap (IntermediateField.inclusion c.le).toRingHom) (spMap f₁)
    (by rw [spMap_comp j f₁, Category.assoc]) o
  obtain ⟨e, he, -⟩ := grpPullback_iso m₁.cart (isGrpPullback_pullback o.t.G (spMap f₁))
  have hv₁ : IsLieBasis (fun i => v₀ i ≫ e.inv) := Chart.isLieBasis_iso e (by
    simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using hv₀)
  obtain ⟨r', hr', Hv⟩ := exists_isLieBasis_eigen E H D l c g ty hty R₁ (f₁.comp j) o₁ _ _ hv₁ p₁
  obtain ⟨p₂, hp₂⟩ := exists_away_point p₁ hr'
  let R₂ := Localization.Away r'
  let f₂ : R₁ →+* R₂ := algebraMap R₁ R₂
  obtain ⟨o₂, ⟨m₂⟩⟩ := exists_pull
    (spMap ((f₂.comp f₁).comp j) ≫ spMap (IntermediateField.inclusion c.le).toRingHom) (spMap f₂)
    (by rw [RingHom.comp_assoc, spMap_comp (f₁.comp j) f₂, Category.assoc]) o₁
  obtain ⟨v, hv, hev⟩ := Hv o₂.t ⟨m₂.toSABMap⟩
  have i₁ : IsOpenImmersion (spMap f₁) := inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))))
  have i₂ : IsOpenImmersion (spMap f₂) := inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap R₁ (Localization.Away r')))))
  refine ⟨R₂, inferInstance, f₂.comp f₁, o₂, v, ?_, ?_, ?_, hv, hev⟩
  · rw [spMap_comp f₁ f₂]; infer_instance
  · refine ⟨p₂, ?_⟩
    rw [spMap_comp f₁ f₂]
    exact (congrArg (spMap f₁) hp₂).trans hp₁
  · rw [spMap_comp f₁ f₂]; exact objMap_comp m₂ m₁

theorem exists_chart_eigenframe : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → ∀ x : Xo.XF c, ∃ (R : Type) (_ : CommRing R) (_ : Algebra c.F R) (jR : Sp R ⟶ Xo.XF c) (o : Obj D l (baseKA l) (spMap (algebraMap c.F R) ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (v : Fin g → (epsR R ⟶ o.t.G)) (th : o.t.PP.L.Sec), Algebra.FiniteType c.F R ∧ IsReduced R ∧ IsOpenImmersion jR ∧ x ∈ Set.range jR ∧ jR ≫ pullback.snd _ _ = spMap (algebraMap c.F R) ∧ Nonempty (ObjMap o Xo.univ (jR ≫ pullback.fst _ _)) ∧ IsLieBasis v ∧ (∀ i a, (v i ≫ o.t.act.act a).left = spMap (epsScaleR (algebraMap c.F R ⟨ty i (a : E), c.conj (ty i) a⟩)) ≫ (v i).left) ∧ (∀ y : Sp R, ∃ x : o.t.G.left, o.t.G.hom x = y ∧ x ∈ Out.nonzeroLocus th) ∧ (∀ s : o.t.PP.L.Sec, ∃! a : R, ∀ i, s.f i = constFn o.t.G.hom _ a * th.f i) := by
  intro hS E _ _ _ H D l Xo c g ty hty x
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  let π : Xo.XF c ⟶ Xo.X := pullback.fst _ _
  let σ : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  have hσ : Smooth σ := inferInstanceAs (Smooth (pullback.snd Xo.s _))
  have hred : AlgebraicGeometry.IsReduced (Xo.XF c) :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ σ hσ).1
  obtain ⟨V, hV, θ, hθ, -, hne⟩ := PushInv.pushInvertible hS Xo.X (Obj.toPolAV Xo.univ) (π x)
  obtain ⟨B, j₀, hj₀, ⟨p, hp⟩, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := Xo.XF c) (x := x) (U := π ⁻¹ᵁ V) hV
  let j : c.F →+* B := (Spec.preimage (j₀ ≫ σ)).hom
  have hj : j₀ ≫ σ = spMap j := (Spec.map_preimage (j₀ ≫ σ)).symm
  obtain ⟨o₀, ⟨m₀⟩⟩ := exists_pull (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom) (j₀ ≫ π)
    (by rw [← hj, Category.assoc, Category.assoc]; exact congrArg (j₀ ≫ ·) pullback.condition) Xo.univ
  obtain ⟨R, _, f, o, v, hf, ⟨q, hq⟩, ⟨m₁⟩, hv, hev⟩ := exists_eigen_chart c hty j o₀ p
  obtain ⟨m⟩ := objMap_comp m₁ m₀
  let jR : Sp R ⟶ Xo.XF c := spMap f ≫ j₀
  have hjR : IsOpenImmersion jR := IsOpenImmersion.comp (spMap f) j₀
  have hs : jR ≫ σ = spMap (f.comp j) := by
    rw [spMap_comp j f, ← hj]; exact Category.assoc _ _ _
  have hL : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨th, hth⟩ := exists_sec_of_secOn m.cart.1 Xo.univ.t.PP.isLB o.t.PP.isLB hL (V := V)
    (fun y => hsub ⟨spMap f y, rfl⟩) hθ hne
  letI : Algebra c.F R := (f.comp j).toAlgebra
  refine ⟨R, inferInstance, inferInstance, jR, o, v, th, ?_, ?_, hjR, ⟨q, ?_⟩, hs, ?_, hv, hev, hth,
    SectionBaseChange.generates hS (Obj.toPolAV Xo.univ) m.cart.1 o.t.PP.isLB hL th hth⟩
  · have h : LocallyOfFiniteType (spMap (f.comp j)) := by rw [← hs]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := CommRingCat.ofHom (f.comp j))).1 h
  · have h : AlgebraicGeometry.IsReduced (Sp R) := isReduced_of_isOpenImmersion jR
    exact (affine_isReduced_iff (CommRingCat.of R)).1 h
  · exact (congrArg j₀ hq).trans hp
  · have e : jR ≫ π = spMap f ≫ j₀ ≫ π := Category.assoc _ _ _
    exact (congrArg (fun u => Nonempty (ObjMap o Xo.univ u)) e).mpr ⟨m⟩

end GlobalTheory.ModuliChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmEndomorphismCommConjugation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CurveEndo

theorem scale_dual (f : ℂ →+* ℂ) (c : ℂ) :
    spMap (Chart.dualMapR f) ≫ spMap (epsScaleR c) = spMap (epsScaleR (f c)) ≫ spMap (Chart.dualMapR f) := by
  rw [spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  ext a <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_symm_dual (τ : ℂ ≃+* ℂ) :
    spMap (Chart.dualMapR (τ.symm : ℂ →+* ℂ)) ≫ spMap (Chart.dualMapR (τ : ℂ →+* ℂ)) = 𝟙 _ := by
  rw [spMap_comp_spMap]
  refine Eq.trans ?_ (Spec.map_id (CommRingCat.of (DualNumber ℂ)))
  congr 1
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem left_eq_scale {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (he : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) {w : Fin g → ℂ} {v v' : epsR ℂ ⟶ A} (α : ℂ) (hv : IsTangent v)
    (hw : u.IsDiff w v) (hv' : IsTangent v') (hw' : u.IsDiff (α • w) v') :
    v'.left = spMap (epsScaleR α) ≫ v.left := by
  have hx := (LieMultiple.isLieComb_one_iff_comp α v _).2 rfl
  have hxt : IsTangent (Chart.spMap (Chart.scaleD α) ≫ v) :=
    (Chart.isTan_iff _).1 (Chart.isTan_scale α ((Chart.isTan_iff _).2 hv))
  rw [(he (α • w)).unique ⟨hv', hw'⟩ ⟨hxt, CMNormIdentity.isDiff_of_isLieComb u hw α hx⟩]
  exact (LieMultiple.isLieComb_one_iff α v _).1 hx

theorem comm_of_fixed (P : Out.PolAV (Sp ℂ)) (hg : P.g = 1) (u : HolUnif P.A P.L P.g)
    (hd : ∀ v, IsTangent v → ∃! w, u.IsDiff w v) (he : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)
    (W : P.A ⟶ P.A) [IsMonHom W] (α : ℂ) (hW : ∀ z, u.ex (α • z) = u.ex z ≫ W)
    (τ : ℂ ≃+* ℂ) (hτ : τ α = α) (io : P.A.left ⟶ P.A.left) (h : IsGrpPullback P.A P.A (spMap (τ : ℂ →+* ℂ)) io) :
    W.left ≫ io = io ≫ W.left := by
  obtain ⟨W', hW', e⟩ := HomDescent.exists_isMonHom_pull h h W
  obtain ⟨v, ⟨hv, dv⟩, -⟩ := he (fun _ => 1)
  obtain ⟨v', hv', -⟩ := existsUnique_isVecOver h.1 v
  have tv' := hv'.isTangent h hv
  unfold IsVecOver at hv'
  obtain ⟨w', dw', -⟩ := hd v' tv'
  have h1 : (v ≫ W).left = spMap (epsScaleR α) ≫ v.left :=
    left_eq_scale u he α hv dv (HomLinear.isTangent_comp W hv)
      (HomLinear.isDiff_comp u u W (α • LinearMap.id) hW hv dv)
  have h2 : (v' ≫ W').left = spMap (epsScaleR α) ≫ v'.left := by
    refine h.1.hom_ext ?_ ?_
    · rw [Over.comp_left, Category.assoc, e, ← Category.assoc, hv', Category.assoc, ← Over.comp_left, h1,
        ← Category.assoc, scale_dual, Category.assoc, Category.assoc, hv']
      simp [hτ]
    · rw [Over.w, Category.assoc, Over.w]
      refine Eq.trans ?_ (spMap_comp_spMap _ _).symm
      show spMap _ = spMap _
      congr 1
      ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have hne : w' ≠ 0 := by
    rintro rfl
    have h3 := left_eq_scale u he 0 tv' dw' tv' (by rwa [zero_smul])
    have h4 : v.left = spMap (epsScaleR 0) ≫ v.left := by
      have h5 : spMap (Chart.dualMapR (τ : ℂ →+* ℂ)) ≫ v.left =
          spMap (Chart.dualMapR (τ : ℂ →+* ℂ)) ≫ spMap (epsScaleR 0) ≫ v.left := by
        rw [← Category.assoc, scale_dual, map_zero, Category.assoc, ← hv', ← Category.assoc, ← h3]
      have h6 := congrArg (spMap (Chart.dualMapR (τ.symm : ℂ →+* ℂ)) ≫ ·) h5
      simpa only [← Category.assoc, dual_symm_dual, Category.id_comp] using h6
    have h7 := (hd v hv).unique dv
      (CMNormIdentity.isDiff_of_isLieComb u dv 0 ((LieMultiple.isLieComb_one_iff 0 v v).2 h4))
    simpa using congrFun h7 ⟨0, by omega⟩
  obtain ⟨F, hF, -, hT, hu⟩ := HomLinear.exists_linear_of_isMonHom P.A P.A P.isAb P.isAb P.L P.L _ _ u u hd he W' hW'
  obtain ⟨tf, df⟩ := hT w' v' tv' dw'
  have h8 : F w' = α • w' := (hd _ tf).unique df
    (CMNormIdentity.isDiff_of_isLieComb u dw' α ((LieMultiple.isLieComb_one_iff α v' _).2 h2))
  have h9 : ∀ z, F z = α • z := fun z => by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have hz : z = (z i / w' i) • w' := by
      funext j
      have : j = i := Fin.ext (by have := j.2; have := i.2; omega)
      rw [this, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hi]
    rw [hz, map_smul, h8, smul_comm]
  rw [← e, ← hu W fun z => by rw [h9, hW]]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem cmHost_rootComplex_eq_pm_sqrt (H : Host E) : H.rt0 = Complex.I * Real.sqrt H.d ∨ H.rt0 = -(Complex.I * Real.sqrt H.d) := by
  rw [← sq_eq_sq_iff_eq_or_eq_neg, H.sqrt_neg_disc_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
    Real.sq_sqrt (by positivity)]
  simp

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h <;> rw [h] <;> simp

theorem mem_lattice (C : Curve H) (z : Fin C.P.g → ℂ) : z ∈ C.u.Λ ↔ ∃ a, z = fun _ => C.c * wC H a := by
  rw [C.lat z]
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h
  · exact ⟨fun ⟨m, n, e⟩ => ⟨(m, n), by rw [e, wC, h]⟩, fun ⟨a, e⟩ => ⟨a.1, a.2, by rw [e, wC, h]⟩⟩
  · refine ⟨fun ⟨m, n, e⟩ => ⟨(m + n, -n), ?_⟩, fun ⟨a, e⟩ => ⟨a.1 + a.2, -a.2, ?_⟩⟩
    · rw [e, wC, h]
      funext _
      push_cast
      ring
    · rw [e, wC, h]
      funext _
      push_cast
      ring

theorem exists_norm (H : Host E) : ∃ n : ℕ, (1 + H.d : ℂ) = 4 * n := by
  have := H.d_mod
  refine ⟨(1 + H.d) / 4, ?_⟩
  exact_mod_cast (by omega : 1 + H.d = 4 * ((1 + H.d) / 4))

theorem exists_endo_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∃ W : C.P.A ⟶ C.P.A, IsMonHom W ∧ (∀ z, C.pt z ≫ W.left = C.pt (wC H (0, 1) * z)) ∧ (∀ z z', C.pt z = C.pt z' ↔ ∃ a, z - z' = wC H a) ∧ (∀ x : Sp ℂ ⟶ C.P.A.left, x ≫ C.P.A.hom = 𝟙 _ → ∃ z, C.pt z = x) ∧ ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ io : C.P.A.left ⟶ C.P.A.left, IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → W.left ≫ io = io ≫ W.left := by
  intro E _ _ _ H C
  obtain ⟨Hm, χ, Ef, hA, hd, he, hθ, -⟩ := C.theta
  obtain ⟨n, hn⟩ := exists_norm H
  have hsq := H.sqrt_neg_disc_sq
  have hα : wC H (0, 1) = (1 + H.rt0) / 2 := by simp [wC]
  obtain ⟨W, hW, hF⟩ := exists_hom_of_linear_scaling_hermForm C.P C.P C.u C.u Hm χ Hm χ hA hA
    (fun k => (hθ k).2) (fun k => (hθ k).1) (wC H (0, 1) • LinearMap.id) n
    (fun l hl => by
      obtain ⟨a, rfl⟩ := (mem_lattice C l).1 hl
      refine (mem_lattice C _).2 ⟨(-(n * a.2), a.1 + a.2), ?_⟩
      funext _
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, wC]
      push_cast
      linear_combination (C.c * a.2 / 4) * hsq - (C.c * a.2 / 4) * hn)
    (fun x y => by
      have e : wC H (0, 1) * starRingEnd ℂ (wC H (0, 1)) = n := by
        rw [hα, map_div₀, map_add (f := _), rt0_conj_neg_ne_zero, map_one, map_ofNat]
        linear_combination (-1 / 4 : ℂ) * hsq + (1 / 4 : ℂ) * hn
      simp only [LinearMap.smul_apply, LinearMap.id_apply, hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct,
        dotProduct_smul, smul_eq_mul]
      rw [← e, ← _root_.mul_assoc, _root_.mul_comm (wC H (0, 1))]
      rfl)
  refine ⟨W, hW, fun z => ?_, fun z z' => ?_, fun x hx => ?_, fun τ hτ io h => ?_⟩
  · unfold Curve.pt
    rw [← Over.comp_left, ← hF]
    congr 2
    ext i
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · have e := C.u.ex_add (fun _ => C.c * (z - z')) (fun _ => C.c * z')
    have e' : ((fun _ => C.c * (z - z')) + fun _ => C.c * z' : Fin C.P.g → ℂ) = fun _ => C.c * z := by
      funext _
      simp only [Pi.add_apply]
      ring
    rw [e'] at e
    have e₁ : C.pt z = C.pt z' ↔ C.u.ex (fun _ => C.c * z) = C.u.ex (fun _ => C.c * z') :=
      ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (fun t => t.left) h⟩
    rw [e₁, e, mul_eq_right, C.u.ker, mem_lattice]
    refine exists_congr fun a => ⟨fun h => ?_, fun h => by rw [h]⟩
    exact mul_left_cancel₀ C.c_ne (congrFun h ⟨0, by rw [C.g_eq]; omega⟩)
  · obtain ⟨z, hz⟩ := C.u.ex_onto (Over.homMk x hx)
    have hg := C.g_eq
    refine ⟨z ⟨0, by omega⟩ / C.c, ?_⟩
    have : (fun _ => C.c * (z ⟨0, by omega⟩ / C.c)) = z := by
      funext j
      rw [mul_div_cancel₀ _ C.c_ne]
      congr 1
      exact Fin.ext (by have := j.2; simp only; omega)
    unfold Curve.pt
    rw [this, hz]
    rfl
  · refine comm_of_fixed C.P C.g_eq C.u hd he W (wC H (0, 1)) hF τ ?_ io h
    rw [hα, map_div₀, map_add (f := _), hτ, map_one, map_ofNat]

end GlobalTheory.CurveEndo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalGeneratorStableBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem exists_away_lift {X : Scheme.{0}} {S R : Type} [CommRing S] [CommRing R]
    (x : Spec (CommRingCat.of S) ⟶ X) (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (p : Spec (CommRingCat.of S)) (hp : x p ∈ Set.range j) :
    ∃ g : S, g ∉ p.asIdeal ∧ ∃ φ : R →+* Localization.Away g,
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) ≫ x =
        Spec.map (CommRingCat.ofHom φ) ≫ j := by
  have hopen : IsOpen ((fun q : PrimeSpectrum S => x q) ⁻¹' Set.range j) :=
    j.isOpenEmbedding.isOpen_range.preimage x.continuous
  obtain ⟨_, ⟨g, rfl⟩, hg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := p) hp hopen
  refine ⟨g, hg, ?_⟩
  have hr : Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) ≫ x) ⊆
      Set.range j := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply]
    apply hsub
    have : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) q ∈
        Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := ⟨q, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at this
    exact this
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j _ hr)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem exists_local_generator : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (p : Sp S), ∃ g : S, g ∉ p.asIdeal ∧ ∃ θ : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x)), ∀ (T : Type) [CommRing T] (ψ : Localization.Away g →+* T) (x' : Sp T ⟶ Xo.X) (θ' : LB.Sec (PPx x')), x' = spMap ψ ≫ spMap (algebraMap S (Localization.Away g)) ≫ x → SecBC ψ 1 _ x' θ θ' → SecGen x' θ' ∧ SecNZ x' θ' := by
  intro hB E _ _ _ H Dw l Xo S _ x p
  obtain ⟨R, _, _, j, θ₀, hj, hz, hnz⟩ := _root_.GlobalTheory.PushLoc.exists_secNZ hB E H Dw l Xo (x p)
  obtain ⟨g, hg, φ, hφ⟩ := exists_away_lift x j p hz
  have hφ' : spMap (algebraMap S (Localization.Away g)) ≫ x = spMap φ ≫ j := hφ
  obtain ⟨θ, hθ, -⟩ := _root_.GlobalTheory.Frames.SecPull.existsUnique_secBC E H Dw l Xo R (Localization.Away g) φ 1 j _ hφ' θ₀
  refine ⟨g, hg, θ, ?_⟩
  intro T _ ψ x' θ' hx' hbc
  have h1 : SecBC (ψ.comp φ) 1 j x' θ₀ θ' :=
    ((_root_.GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo R (Localization.Away g) T φ ψ j _ x' hφ' hx').1 1 θ₀ θ θ' hθ).1 hbc
  have hx'' : x' = spMap (ψ.comp φ) ≫ j := by
    rw [hx', hφ', ← Category.assoc]
    congr 1
    exact (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)).symm
  exact ⟨_root_.GlobalTheory.FrameGenerator.secGen_of_secNZ_baseChange hB E H Dw l Xo R j θ₀ hnz T (ψ.comp φ) x' θ' hx'' h1,
    fun p' => (_root_.GlobalTheory.Frames.secBC_nonvanishing_iff E H Dw l Xo R T (ψ.comp φ) j x' hx'' θ₀ θ' h1 p').2 (hnz _)⟩

end GlobalTheory.Frames
end

