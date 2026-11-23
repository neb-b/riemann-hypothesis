module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace FinitePresFibreFlat

open TensorProduct IsLocalRing FiniteFibreFlat

section Algebra

theorem free_of_flat_reduction {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    [Module.FinitePresentation A M] (p : Ideal R) (hp : p.map (algebraMap R A) ≤ maximalIdeal A)
    [Module.Flat (A ⧸ p.map (algebraMap R A)) ((A ⧸ p.map (algebraMap R A)) ⊗[A] M)] :
    Module.Free A M := by
  set I := p.map (algebraMap R A) with hI
  have hrel : LocalFlat.RelationsLift I M :=
    LocalFlat.relationsLift_of_flat (C := A ⧸ I) Ideal.Quotient.mk_surjective Ideal.mk_ker
      (TensorProduct.mk A (A ⧸ I) M 1) (TensorProduct.mk_surjective A M (A ⧸ I)
        Ideal.Quotient.mk_surjective) (LinearMap.ker_tensorProductMk M)
  apply Module.free_of_maximalIdeal_rTensor_injective
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj, injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hrel (maximalIdeal A) (maximalIdeal A).subtype x (by rw [hx]; simp)
  let e := Submodule.comapSubtypeEquivOfLe hp
  have hy : I.subtype.lTensor M (e.toLinearMap.lTensor M y) = 0 := by
    rw [← hx, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
    rfl
  rw [map_eq_zero_iff _ (lTensor_map_injective p)] at hy
  have : y = 0 := (LinearEquiv.lTensor M e).injective (hy.trans (map_zero _).symm)
  rw [this, map_zero]

theorem flat_of_flat_fibres {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Module.FinitePresentation A B]
    [Module.Flat R B]
    (H : ∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C),
      (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) :
    Module.Flat A B := by
  refine Module.flat_of_isLocalized_maximal A B (fun P _ => Localization.AtPrime P ⊗[A] B)
    (fun P _ => TensorProduct.mk A (Localization.AtPrime P) B 1) fun P _ => ?_
  let A' := Localization.AtPrime P
  let p : Ideal R := (maximalIdeal A').comap (algebraMap R A')
  let I := p.map (algebraMap R A')
  have h1 : Module.Flat R (B ⊗[A] A') := Module.Flat.trans R B (B ⊗[A] A')
  have h2 : Module.Flat R (A' ⊗[A] B) :=
    Module.Flat.of_linearEquiv
      ((Algebra.TensorProduct.comm A A' B).restrictScalars R).toLinearEquiv
  have h3 : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A] B) := by
    let ψ : R →+* A' ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap R A')
    have hψ₁ : p ≤ RingHom.ker ψ := fun r hr =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
    have hψ₂ : p.primeCompl ≤ (IsUnit.submonoid (A' ⧸ I)).comap ψ := by
      intro r hr
      have : IsUnit (algebraMap R A' r) := by
        by_contra h
        exact hr h
      exact this.map (Ideal.Quotient.mk I)
    refine H p.ResidueField (A' ⧸ I) (algebraMap R _) (Ideal.ResidueField.lift p ψ hψ₁ hψ₂) ?_
    ext r
    exact (Ideal.ResidueField.lift_algebraMap p ψ hψ₁ hψ₂ r).symm
  have h4 : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A'] (A' ⊗[A] B)) :=
    Module.Flat.of_linearEquiv
      (AlgebraTensorModule.cancelBaseChange A A' (A' ⧸ I) (A' ⧸ I) B)
  have h5 : Module.Free A' (A' ⊗[A] B) :=
    free_of_flat_reduction p Ideal.map_comap_le
  have h6 : Module.Flat A' (A' ⊗[A] B) := Module.Flat.of_free
  exact Module.Flat.trans A A' (A' ⊗[A] B)

end Algebra

open FibreFlat

set_option backward.isDefEq.respectTransparency false in
theorem flat_of_flatOver_fields {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S)
    (hY : LocallyOfFinitePresentation g) (h0 : LocallyOfFinitePresentation (f ≫ g))
    (h1 : Flat (f ≫ g)) (h2 : IsFinite f)
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) :
    Flat f := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  · refine IsZariskiLocalAtTarget.of_openCover (S.affineCover.pullback₁ g) fun i => ?_
    let u := S.affineCover.f i
    have sq := IsPullback.of_hasPullback f (pullback.fst g u)
    have sq' := IsPullback.of_hasPullback g u
    refine this (pullback.snd f (pullback.fst g u)) (pullback.snd g u)
      inferInstance (MorphismProperty.of_isPullback (sq.paste_vert sq') h0)
      (MorphismProperty.of_isPullback (sq.paste_vert sq') h1) inferInstance
      (fun k _ t => flatOver_of_comp_base (u := u) ?_) ⟨_, rfl⟩
    rw [← pullback.condition]
    exact (H k _).target sq
  obtain ⟨R, rfl⟩ := hS
  wlog hA : ∃ A, Y = Spec A generalizing X Y
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    exact this (pullback.snd f (Y.affineCover.f i)) inferInstance (Y.affineCover.f i ≫ g)
      inferInstance (by rw [e]; infer_instance) (by rw [e]; infer_instance)
      (fun k _ t => (H k t).target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hA
  wlog hX : ∃ B, X = Spec B generalizing X
  · haveI hX' : IsAffine X := isAffine_of_isAffineHom f
    rw [← MorphismProperty.cancel_left_of_respectsIso @Flat X.isoSpec.inv]
    exact this (X.isoSpec.inv ≫ f) inferInstance (by rw [Category.assoc]; infer_instance)
      (by rw [Category.assoc]; infer_instance)
      (fun k _ t => (H k t).source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1 h0
  rw [Flat.SpecMap_iff] at h1 ⊢
  rw [IsFinite.SpecMap_iff] at h2
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hY h0
  letI : Algebra R A := g.hom.toAlgebra
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra R B := (g ≫ f).hom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Flat R B := h1
  haveI : Module.Finite A B := h2
  haveI : Algebra.FinitePresentation R A := hY
  haveI : Algebra.FinitePresentation R B := h0
  haveI : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R A B
  haveI : Module.FinitePresentation A B :=
    Module.FinitePresentation.of_finite_of_finitePresentation A B
  refine flat_of_flat_fibres (R := R) (A := A) (B := B) fun k C _ _ _ t h e => ?_
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)
  have := H k (Spec.map (CommRingCat.ofHom t)) _ _ _ (Spec.map (CommRingCat.ofHom h)) sq.flip
    (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      exact e)
  rw [Flat.SpecMap_iff] at this
  exact RingHom.flat_algebraMap_iff.mp this

end FinitePresFibreFlat

theorem flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres :
    ∀ (S : Scheme.{0}) (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFinitePresentation X.hom → LocallyOfFinitePresentation Y.hom → IsFinite f.left → (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S), Flat ((Over.pullback t).map f).left) → Flat f.left := by
  intro S X Y f h1 h0 h2 h3 H
  refine FinitePresFibreFlat.flat_of_flatOver_fields f.left Y.hom h2 (by rwa [Over.w])
    (by rwa [Over.w]) h3 fun k _ t => ?_
  exact FiniteFibreFlat.flatOver_descend
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
    (FibreFlat.flatOver_of_pullback f _ (H _ _))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELPull

theorem lbIso_pull {X Y Y' : Scheme.{0}} {A : LB Y} {L : LB X} {φ : Y ⟶ X} (H : LBIso A (L.pull φ)) (h : Y' ⟶ Y)
    {F : Y' ⟶ X} (e : F = h ≫ φ) : LBIso (A.pull h) (L.pull F) :=
  H.chartPull (chartPullPull A h h rfl)
    (chartPullSame L (fun _ : PUnit => F) (fun _ : PUnit => φ) (fun _ => 1) h fun _ => e)

theorem isPEL_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s) (t' : TObj g k J b s') (τ : SAB H S), f ≫ s = s' → TMap t' t f → IsPEL D a bas ρ t τ → ∃ τ' : SAB H S', IsPEL D a bas ρ t' τ' := by
  intro E _ _ _ H D g k J a bas o _ b ρ S S' s s' f t t' τ hs ⟨ψ, hψ, hψL, hpt, hact⟩ ⟨φ, hφ, hφL, hφa, hgeom⟩
  obtain ⟨τ', ⟨m⟩⟩ : ∃ τ' : SAB H S', Nonempty (SABMap τ' τ f) := by
    have hC := Out.CubePf.cubePull
    have hsemi : IsSemiAbelian ((Over.pullback f).obj τ.G) := by
      refine { comm := ?_, smooth := ?_, separated := ?_, quasiCompact := ?_, geomConnected := ?_, fibres := ?_ }
      · have := τ.semi.comm
        infer_instance
      · have := τ.semi.smooth
        change Smooth (pullback.snd τ.G.hom f)
        infer_instance
      · have := τ.semi.separated
        change IsSeparated (pullback.snd τ.G.hom f)
        infer_instance
      · have := τ.semi.quasiCompact
        change QuasiCompact (pullback.snd τ.G.hom f)
        infer_instance
      · have := τ.semi.geomConnected
        change GeometricallyConnected (pullback.snd τ.G.hom f)
        infer_instance
      · intro Ω _ _ q
        obtain ⟨A⟩ := τ.semi.fibres Ω (q ≫ f)
        exact ⟨torusExtOfIso (pullCompIso q f τ.G) A⟩
    have hp : ∃ (PP' : RigLB ((Over.pullback f).obj τ.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
        (m : SABMap ⟨(Over.pullback f).obj τ.G, hsemi, OAct.pullback f τ.G τ.act, PP', cub,
          sym, adj, prim⟩ τ f), m.φ = pullback.fst τ.G.hom f := by
      have h := isGrpPullback_pullback τ.G f
      obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC S S' τ.G _ (cubeMapOf h) τ.PP τ.cub
      have hact : ∀ a, ((OAct.pullback f τ.G τ.act).act a).left ≫ pullback.fst τ.G.hom f =
          pullback.fst τ.G.hom f ≫ (τ.act.act a).left := fun a => pullback.lift_fst _ _ _
      have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj τ.G) a,
          pushPt h.1.w (x ≫ (OAct.pullback f τ.G τ.act).act a) = pushPt h.1.w x ≫ τ.act.act a := fun x a =>
        Over.OverMorphism.ext (by
          show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
          rw [Category.assoc, hact, Category.assoc])
      refine ⟨(cubeMapOf h).rigLB τ.PP hL hr, c', hs τ.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
      · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj τ.G) ((Over.pullback f).obj τ.G)))
          (pushPt h.1.w (snd ((Over.pullback f).obj τ.G) ((Over.pullback f).obj τ.G)))
        refine LBIso.chartPull (chartPullLinComb τ.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
          (chartPullLinComb τ.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (τ.adj a)
        · fin_cases i
          · exact (pa _ a).trans (by simp [U])
          · simp [U]
        · fin_cases i
          · simp [U]
          · exact (pa _ _).trans (by simp [U])
      · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj τ.G))
        refine LBIso.chartPull (chartPullPull τ.PP.L _ U.left (Category.id_comp _))
          (chartPullLinComb τ.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) τ.prim
        fin_cases i
        · simp [U]
        · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
    obtain ⟨_, _, _, _, _, m, -⟩ := hp
    exact ⟨_, ⟨m⟩⟩
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)

  have hL : LBIso τ'.PP.L (τ.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hc : IsGrpPullback τ'.G t.A f (m.cm.F ≫ φ.hom.left) :=
    (IsGrpPullback.comp m.cart (isGrpPullback_of_iso φ)).congr (Category.comp_id f) rfl
  obtain ⟨e, he, heF⟩ := grpPullback_iso hc hψ
  refine ⟨τ', e, he, ?_, fun j => ?_, fun K _ _ _ x β hx => ?_⟩
  · exact (hL.trans τ'.PP.isLB (pull_isLB τ.PP.isLB _) (pull_isLB t.isLB _) (lbIso_pull hφL m.cm.F rfl)).trans
      τ'.PP.isLB (pull_isLB t.isLB _) (pull_isLB t'.isLB _) (lbIso_pull hψL e.hom.left heF.symm).symm
  · apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · have h₁ : (τ.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (t.act j).left :=
        congrArg (fun z => z.left) (hφa j)
      have h₂ : (τ'.act.act (a j)).left ≫ m.cm.F = m.cm.F ≫ (τ.act.act (a j)).left := m.act _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, heF, hact, ← Category.assoc, h₂,
        Category.assoc, h₁, ← Category.assoc, ← heF, Category.assoc]
    · rw [Over.w, Over.w]
  · obtain ⟨hdet, I, hI, hA⟩ := hgeom K (x ≫ f) β (by rw [Category.assoc, hs, hx])
    refine ⟨fun σ => ?_, GlobalTheory.ObjPull.tateMove (GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)) (fun c y => ?_)
      (fun n y y' c hc => ?_) I, hI, fun i => ?_⟩
    · rw [GlobalTheory.LiePull.lieMult_pull _ S S' τ.G τ'.G f m.cm.F τ.act τ'.act m.cart m.act K x σ,
        GlobalTheory.LiePull.lieMult_pull _ S S' τ.G τ'.G f m.cm.F τ.act τ'.act m.cart m.act K x σ]
      exact hdet σ
    · apply Over.OverMorphism.ext
      show (y.left ≫ _) ≫ _ = (y.left ≫ _) ≫ _
      rw [Category.assoc, m.act, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' τ.G τ'.G f m.cm.F τ.PP.L τ'.PP.L τ.PP.isLB τ'.PP.isLB m.cart hL
        (Over.mk x) n y y' _ _ _ rfl rfl).2 hc
    · apply Over.OverMorphism.ext
      apply hψ.1.hom_ext
      · have h₁ : (I.ev k (bas (Pi.single i 1))).left ≫ φ.hom.left = (x ≫ f) ≫ (t.pt i).left :=
          congrArg (fun z => z.left) (hA i)
        have h₂ := GlobalTheory.ObjPull.pushEquiv_symm_left m.cart (Over.mk x) (I.ev k (bas (Pi.single i 1)))
        show (((GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)).symm (I.ev k (bas (Pi.single i 1)))).left ≫ e.hom.left) ≫ ψ =
          (x ≫ (t'.pt i).left) ≫ ψ
        rw [Category.assoc, heF, Category.assoc, hpt]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ.hom.left) h₂).trans (h₁.trans (Category.assoc _ _ _)))
      · rw [Over.w, Over.w]

end GlobalTheory.PELPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerMatrixLinearInDerivation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Lin

section
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} {u : HolUnif A₀ L₀ g} {X : Scheme.{0}}
  {R : Type} [CommRing R] {p : X ⟶ Sp R} {m : A₀.left ⟶ X}

theorem ksRel_add {D D' : R → ℂ} {Θ Θ' : Matrix (Fin g) (Fin g) ℂ}
    {s s' : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ}
    (h : KSRel u p m D Θ s) (h' : KSRel u p m D' Θ' s') :
    KSRel u p m (fun r => D r + D' r) (Θ + Θ') (fun z W f => s z W f + s' z W f) := by
  refine { der := ?_, base := ?_, hol := ?_, per := ?_ }
  · intro z
    refine { add := ?_, mul := ?_, res := ?_ }
    · intro W hW f f'
      simp only [(h.der z).add W hW, (h'.der z).add W hW]
      ring
    · intro W hW f f'
      simp only [(h.der z).mul W hW, (h'.der z).mul W hW]
      ring
    · intro W W' hle hW' f
      simp only [(h.der z).res W W' hle hW', (h'.der z).res W W' hle hW']
  · intro z r
    simp only [h.base, h'.base]
  · intro W f
    exact (h.hol W f).add (h'.hol W f)
  · intro l W f z hz
    simp only [h.per l W f z hz, h'.per l W f z hz, Matrix.add_mulVec, map_add (f := _)]
    ring

theorem ksRel_smul (c : ℂ) {D : R → ℂ} {Θ : Matrix (Fin g) (Fin g) ℂ}
    {s : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ} (h : KSRel u p m D Θ s) :
    KSRel u p m (fun r => c * D r) (c • Θ) (fun z W f => c * s z W f) := by
  refine { der := ?_, base := ?_, hol := ?_, per := ?_ }
  · intro z
    refine { add := ?_, mul := ?_, res := ?_ }
    · intro W hW f f'
      simp only [(h.der z).add W hW]
      ring
    · intro W hW f f'
      simp only [(h.der z).mul W hW]
      ring
    · intro W W' hle hW' f
      simp only [(h.der z).res W W' hle hW']
  · intro z r
    simp only [h.base]
  · intro W f
    exact (h.hol W f).const_mul c
  · intro l W f z hz
    simp only [h.per l W f z hz, Matrix.smul_mulVec, map_smul, smul_eq_mul]
    ring
end

theorem ks_linear : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (o R : Type) [CommRing o] [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap (algebraMap R ℂ)) → ∃ κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin P₀.g) (Fin P₀.g) ℂ, ∀ D : Derivation o R ℂ, ∃ s, KSRel u p m (fun r => D r) (κ D) s := by
  intro P₀ u Hm χ hG o R _ _ _ _ _ _ X p m hs hpb
  have hder : ∀ D : Derivation o R ℂ, IsDer (algebraMap R ℂ) (fun r => D r) := fun D =>
    ⟨fun a b => D.map_add a b, fun a b => by
      show D (a * b) = _
      rw [D.leibniz, Algebra.smul_def, Algebra.smul_def]⟩
  have hex : ∀ D : Derivation o R ℂ, ∃ Θ s, KSRel u p m (fun r => D r) Θ s := fun D =>
    _root_.GlobalTheory.KS.Exist.exists_ksRel P₀ u Hm χ hG R (algebraMap R ℂ) X p m hs hpb _ (hder D)
  choose Θ s hΘ using hex
  have huniq : ∀ (D : Derivation o R ℂ) Θ' s', KSRel u p m (fun r => D r) Θ' s' → Θ D = Θ' :=
    fun D Θ' s' h => GlobalTheory.KS.Uniq.ks_unique P₀ u Hm χ hG R (algebraMap R ℂ) X p m hs hpb _ _ _ _ _ (hΘ D) h
  refine ⟨{ toFun := Θ, map_add' := ?_, map_smul' := ?_ }, fun D => ⟨s D, hΘ D⟩⟩
  · intro D D'
    apply huniq (D + D')
    have e : (fun r => (D + D') r) = fun r => D r + D' r := funext (add_apply D D')
    rw [e]
    exact ksRel_add (hΘ D) (hΘ D')
  · intro c D
    rw [RingHom.id_apply]
    apply huniq (c • D)
    have e : (fun r => (c • D) r) = fun r => c * D r := funext fun r => by
      rw [smul_apply, smul_eq_mul]
    rw [e]
    exact ksRel_smul c (hΘ D)

end GlobalTheory.KS.Lin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PreconnectedSpacePtsOfIsIntegral
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Topology Filter

namespace GlobalTheory.OpenSubgroupPts

open GlobalTheory.Points

theorem isPreconnected_affineOpen {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p]
    {U : Y.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsPreconnected {x : Pts p | ⊤ ≤ x.1 ⁻¹ᵁ U} := by
  have key : ∀ {R : CommRingCat.{0}} [IsDomain R] (q : Spec R ⟶ Sp ℂ) [LocallyOfFiniteType q],
      PreconnectedSpace (Pts q) := by
    intro R _ q hft
    obtain ⟨φ, rfl⟩ := Spec.map_surjective q
    let _ := φ.hom.toAlgebra
    have : Algebra.FiniteType ℂ R := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hft
    exact FiniteClasses.preconnectedSpace_pts R
  have := key (hU.fromSpec ≫ p)
  have h := isPreconnected_range (PtsOver.continuous_map (C := ℂ) hU.fromSpec (q := p) rfl (𝟙 _))
  rw [PtsOver.range_map, range_comp_of_isOpenImmersion, hU.opensRange_fromSpec] at h
  exact h

theorem preconnectedSpace_pts_of_isIntegral {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp ℂ)
    [LocallyOfFiniteType p] : PreconnectedSpace (Pts p) := by
  refine ⟨isPreconnected_of_forall_pair fun x _ y _ => ?_⟩
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_le x.1 (le_preimage_top _)
  obtain ⟨V, hV, hy, -⟩ := exists_isAffineOpen_le y.1 (le_preimage_top _)
  have hx' := (le_preimage_iff x.1 U).1 hx
  have hy' := (le_preimage_iff y.1 V).1 hy
  have : Nonempty U := ⟨⟨_, hx'⟩⟩
  have : Nonempty V := ⟨⟨_, hy'⟩⟩
  obtain ⟨z, hz, hzm⟩ := ComplexPoints.exists_point_mem p (Z := (U : Set Y) ∩ V)
    (U.isOpen.inter V.isOpen).isLocallyClosed
    (nonempty_preirreducible_inter U.isOpen V.isOpen ⟨_, hx'⟩ ⟨_, hy'⟩)
  exact ⟨_, Set.subset_univ _, Or.inl hx, Or.inr hy, IsPreconnected.union (⟨z, hz⟩ : Pts p)
    ((le_preimage_iff z U).2 (hzm _).1) ((le_preimage_iff z V).2 (hzm _).2)
    (isPreconnected_affineOpen p hU) (isPreconnected_affineOpen p hV)⟩

theorem subgroup_eq_top_of_nhds_one :
    ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (x : Sp ℂ ⟶ X) (H : Subgroup (Over.mk x ⟶ G)) (U : G.left.Opens) (κ : Type) [Fintype κ] (f : κ → Γ(G.left, U)) (O : Set (κ → ℂ)), Smooth G.hom → GeometricallyConnected G.hom → IsOpen O → ⊤ ≤ (show Sp ℂ ⟶ G.left from (1 : Over.mk x ⟶ G).left) ⁻¹ᵁ U → (fun j => valAt' (1 : Over.mk x ⟶ G).left U (f j)) ∈ O → (∀ a : Over.mk x ⟶ G, ⊤ ≤ (show Sp ℂ ⟶ G.left from a.left) ⁻¹ᵁ U → (fun j => valAt' a.left U (f j)) ∈ O → a ∈ H) → H = ⊤ := by
  intro X G _ x H U κ _ f O hs hc hO h1 h1O hH
  let p := pullback.snd G.hom x
  have : IsIntegral (pullback G.hom x) :=
    isIntegral_of_isPullback_of_smooth (IsPullback.of_hasPullback G.hom x)
  have := preconnectedSpace_pts_of_isIntegral p
  let Y : Over X := Over.mk (p ≫ x)
  let π : Y ⟶ G := Over.homMk (pullback.fst G.hom x) pullback.condition
  let s : Y ⟶ Over.mk x := Over.homMk p rfl
  let inc : Pts p → (Over.mk x ⟶ Y) := fun y => Over.homMk y.1 (by
    show y.1 ≫ p ≫ x = x
    rw [← Category.assoc, y.2, Category.id_comp])
  have hin : ∀ y, inc y ≫ s = 𝟙 _ := fun y => Over.OverMorphism.ext y.2
  have hsurj : ∀ a : Over.mk x ⟶ G, ∃ y, inc y ≫ π = a := fun a =>
    ⟨⟨pullback.lift a.left (𝟙 _) ((Over.w a).trans (Category.id_comp x).symm), pullback.lift_snd _ _ _⟩,
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  have hopen : IsOpen {z : Sp ℂ ⟶ G.left | ⊤ ≤ z ⁻¹ᵁ U ∧ (fun j => valAt' z U (f j)) ∈ O} :=
    (continuousOn_pi.2 fun j => continuousOn_valR (C := ℂ) (f j)).isOpen_inter_preimage
      (isOpen_setOf_le_preimage U) hO
  have hl : IsLocallyConstant fun y : Pts p => inc y ≫ π ∈ H := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y₀
    let τ : Y ⟶ G := (s ≫ (inc y₀ ≫ π)⁻¹) * π
    have hτ : ∀ y, inc y ≫ τ = (inc y₀ ≫ π)⁻¹ * (inc y ≫ π) := fun y => by
      rw [MonObj.comp_mul, ← Category.assoc, hin, Category.id_comp]
    have hcont : Continuous fun y : Pts p => (show Sp ℂ ⟶ G.left from (inc y ≫ τ).left) :=
      (continuous_comp (C := ℂ) (X := pullback G.hom x) τ.left).comp continuous_subtype_val
    have hN := (hopen.preimage hcont).mem_nhds (x := y₀) (by
      simp only [Set.mem_preimage, hτ, inv_mul_cancel]
      exact ⟨h1, h1O⟩)
    filter_upwards [hN] with y hy
    have h := hH _ hy.1 hy.2
    rw [hτ] at h
    have h' := H.mul_mem_cancel_right (y := inc y₀ ≫ π) h
    rw [mul_inv_cancel_left] at h'
    exact propext h'
  rw [eq_top_iff]
  intro a _
  obtain ⟨y, rfl⟩ := hsurj a
  obtain ⟨y₁, hy₁⟩ := hsurj 1
  have h := hl.apply_eq_of_preconnectedSpace y y₁
  simp only [hy₁] at h
  rw [h]
  exact H.one_mem

end GlobalTheory.OpenSubgroupPts
end

