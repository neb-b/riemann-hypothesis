module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0716
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0158
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0480

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreSectionsInjectiveFlatIntegral
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem genFib_preimage_eq_top {S : Scheme.{0}} (F : Type) [Field F] (gp : Sp F ⟶ S) [IsDominant gp]
    (W : S.Opens) (hW : (W : Set S).Nonempty) : gp ⁻¹ᵁ W = ⊤ := by
  obtain ⟨q, hq⟩ := gp.denseRange.exists_mem_open W.isOpen hW
  refine top_unique fun z _ => ?_
  have : z = q := Subsingleton.elim (α := PrimeSpectrum F) z q
  subst this
  exact hq

theorem genFib_appLE_injective {S : Scheme.{0}} [IsIntegral S] (F : Type) [Field F] (gp : Sp F ⟶ S)
    [IsDominant gp] (W : S.Opens) (e : (⊤ : (Sp F).Opens) ≤ gp ⁻¹ᵁ W) :
    Function.Injective (gp.appLE W ⊤ e).hom := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  have h1 : (Sp F).basicOpen (gp.appLE W ⊤ e r) = ⊥ := by rw [hr]; simp
  have h2 : S.basicOpen r = ⊥ := by
    by_contra hne
    have hne' : (S.basicOpen r : Set S).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hne (by ext1; simpa using h)
    have h3 := genFib_preimage_eq_top F gp _ hne'
    have h4 : (Sp F).basicOpen (gp.appLE W ⊤ e r) = ⊤ := by
      rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen, h3]
      simp
    rw [h4] at h1
    have : (⊤ : (Sp F).Opens) ≠ ⊥ := by
      intro h
      have hm : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F) ∈ ((⊤ : (Sp F).Opens) : Set (Sp F)) := trivial
      rw [h] at hm
      exact hm
    exact this h1
  exact (basicOpen_eq_bot_iff r).mp h2

theorem genFib_pushout_inl_injective {A B C : CommRingCat.{0}} (φ : A ⟶ B) (ψ : A ⟶ C) (hφ : φ.hom.Flat)
    (hψ : Function.Injective ψ.hom) : Function.Injective (pushout.inl φ ψ).hom := by
  algebraize [φ.hom, ψ.hom]
  have h' : IsPushout φ ψ (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom) :=
    CommRingCat.isPushout_tensorProduct A B C
  have e := h'.inl_isoPushout_inv
  have hinj : Function.Injective (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := C)) :=
    Algebra.TensorProduct.includeLeft_injective hψ
  intro x y hxy
  apply hinj
  have := congrArg (fun z => h'.isoPushout.inv.hom z) hxy
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, e] at this
  exact this

theorem genFib_affine_injective {S X Y : Scheme.{0}} (F : Type) [Field F] (f : X ⟶ S) (gp : Sp F ⟶ S)
    (a : Y ⟶ X) (t : Y ⟶ Sp F) (H : IsPullback a t f gp) [Flat f] [IsIntegral S] [IsDominant gp]
    {W : S.Opens} (hW : IsAffineOpen W) (hWne : (W : Set S).Nonempty) {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ W) : Function.Injective (a.appLE V (a ⁻¹ᵁ V) le_rfl).hom := by
  have hT : (⊤ : (Sp F).Opens) ≤ gp ⁻¹ᵁ W := (genFib_preimage_eq_top F gp W hWne).ge
  have hUY : a ⁻¹ᵁ V = a ⁻¹ᵁ V ⊓ t ⁻¹ᵁ ⊤ := by simp
  have hiso := isIso_pushoutSection_of_isAffineOpen H hT e hUY hW (isAffineOpen_top _) hV
  have hfac : a.appLE V (a ⁻¹ᵁ V) le_rfl = pushout.inl _ _ ≫ pushoutSection H hT e hUY := by
    exact (pushout.inl_desc _ _ _).symm
  rw [hfac, CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso (pushoutSection H hT e hUY)).1.comp
    (genFib_pushout_inl_injective _ _ (f.flat_appLE hW hV e) (genFib_appLE_injective F gp W hT))

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem genFib_app_injective : ∀ {S X Y : Scheme.{0}} (F : Type) [Field F] (f : X ⟶ S) (gp : Sp F ⟶ S)
    (a : Y ⟶ X) (t : Y ⟶ Sp F), IsPullback a t f gp → Flat f → IsIntegral S → IsDominant gp →
    ∀ U : X.Opens, Function.Injective (a.app U).hom := by
  intro S X Y F _ f gp a t H hf hS hd U
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  refine X.IsSheaf.section_ext (s := x) (t := 0) fun z hz => ?_
  obtain ⟨W, hW, hzW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show f z ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨V, hV, hzV, hVle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show z ∈ U ⊓ f ⁻¹ᵁ W from ⟨hz, hzW⟩)
  have hVU : V ≤ U := hVle.trans inf_le_left
  have e : V ≤ f ⁻¹ᵁ W := hVle.trans inf_le_right
  refine ⟨V, hVU, hzV, ?_⟩
  rw [map_zero]
  apply genFib_affine_injective F f gp a t H hW ⟨f z, hzW⟩ hV e
  rw [map_zero, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE, CommRingCat.comp_apply,
    hx, map_zero]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTateLevelConditionDescendsGaloisCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.GeomDesc

theorem diag_comp {X Y : Scheme.{0}} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (G2 A).left ⟶ (G2 A₀).left} (sq : IsSquare φ φ₂) :
    (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left := by
  apply pullback.hom_ext
  · have h1 := sq.1
    have e1 : (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A) (𝟙 A))
    have e2 : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (fst A₀ A₀).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 A₀) (𝟙 A₀))
    show _ ≫ (fst A₀ A₀).left = _ ≫ (fst A₀ A₀).left
    rw [Category.assoc, h1, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]
  · have h2 := sq.2
    have e1 : (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A) (𝟙 A))
    have e2 : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (snd A₀ A₀).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 A₀) (𝟙 A₀))
    show _ ≫ (snd A₀ A₀).left = _ ≫ (snd A₀ A₀).left
    rw [Category.assoc, h2, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]

theorem diag_lbIso {X Y : Scheme.{0}} {A : Over X} [GrpObj A] {A₀ : Over Y} [GrpObj A₀] {φ : A.left ⟶ A₀.left}
    {φ₂ : (G2 A).left ⟶ (G2 A₀).left} (sq : IsSquare φ φ₂) {P : LB (G2 A).left} {P₀ : LB (G2 A₀).left}
    (hP : P.IsLB) (hP₀ : P₀.IsLB) (pol : LBIso P (P₀.pull φ₂)) :
    LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) := by
  have h₁ : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) (P₀.pull (φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left)) :=
    MapComp.lbIso_pull_comp pol _ (diag_comp sq).symm
  have h₂ : LBIso ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) (P₀.pull (φ ≫ (lift (𝟙 A₀) (𝟙 A₀)).left)) :=
    MapComp.lbIso_pull_comp (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hP₀ _)) φ rfl
  exact LBIso.trans (pull_isLB hP _) (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP₀ _) _) h₁ h₂.symm

end GlobalTheory.UPel.HT.GeomDesc


open GlobalTheory.UPel.HT.GeomDesc in
theorem GlobalTheory.UPel.HT.geom_descends_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀) (N : ℕ) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (eta : D.La → (𝟙_ (Over X) ⟶ A)) (eta₀ : D.La → (𝟙_ (Over Y) ⟶ A₀)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ y, (eta y).left ≫ φ = π ≫ (eta₀ y).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∃ I : TateIsoO D k (Over.mk x ⟶ A₀) (fun c g => g ≫ act₀.act c) (fun n g g' z => Out.WeilIs A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta₀ y = I.ev N y) := by
  intro p _ D R _ b X Y π sY Ga _ ρ A _ _ A₀ _ _ φ act act₀ N φ₂ P P₀ eta eta₀ hG hA hA₀ gp hact sq hP hP₀ pol heta hgeom k _ _ x β hx
  have := hG.etale
  have := hG.onto
  obtain ⟨y, rfl⟩ := GlobalTheory.ObjDesc.exists_geomPt_lift π k x
  obtain ⟨I, hI⟩ := hgeom k y β (by rw [← Category.assoc, hx])
  have iso := diag_lbIso sq hP hP₀ pol
  refine ⟨GlobalTheory.UPel.HT.TateIsoO.transport (GlobalTheory.ObjPull.pushEquiv gp (Over.mk y)) (fun c g => ?_)
    (fun n g g' c hc => ?_) I, fun a => ?_⟩
  · apply Over.OverMorphism.ext
    show (g ≫ act.act c).left ≫ φ = (GlobalTheory.ObjPull.pushEquiv gp (Over.mk y) g ≫ act₀.act c).left
    rw [Over.comp_left, Over.comp_left, Category.assoc, hact c, GlobalTheory.ObjPull.pushEquiv_left, Category.assoc]
  · exact (GlobalTheory.weilIs_grpPullback_of_comm Y X A₀ A π φ _ _ (pull_isLB hP₀ _) (pull_isLB hP _) gp iso
      (Over.mk y) n g g' _ _ _ (GlobalTheory.ObjPull.pushEquiv_left gp (Over.mk y) g)
      (GlobalTheory.ObjPull.pushEquiv_left gp (Over.mk y) g')).1 hc
  · rw [GlobalTheory.UPel.HT.TateIsoO.transport_ev, ← hI a]
    apply Over.OverMorphism.ext
    rw [GlobalTheory.ObjPull.pushEquiv_left]
    show (toUnit (Over.mk (y ≫ π)) ≫ eta₀ a).left = (toUnit (Over.mk y) ≫ eta a).left ≫ φ
    rw [Over.comp_left, Over.comp_left, Category.assoc, heta a, ← Category.assoc]
    congr 1

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermPullbackRestrictEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem germPullback_restrict_eq {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) {U V : X.Opens} (hle : V ≤ U) (h : f z ∈ V)
    (a : Γ(X, U)) : gs f z V (resG X hle a) = gs f z U a := gs_res f z hle h a


open GlobalTheory.ProjSpace in
theorem secRatio_isTermOf_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (k : ℕ) (b₀ b : D.SecB k 0) (τ₀ τ : SecK D.P.L Y.q.left k), IsTermOf Y b₀ τ₀ → IsTermOf Y b τ → ∀ (W : Y.H.left.Opens) (h₁ : W ≤ Y.q.left ⁻¹ᵁ nonzeroLocus b₀) (h₂ : W ≤ nonzeroLocus τ₀), (Y.q.left.appLE (nonzeroLocus b₀) W h₁).hom (GlobalTheory.ProjSpace.secRatio b₀ b) = resG Y.H.left h₂ (GlobalTheory.ProjSpace.secRatio τ₀ τ) := by
  intro R _ _ D Y k b₀ b τ₀ τ h₀ h W h₁ h₂
  apply fn_ext
  intro y hy
  rw [gs_appLE Y.q.left (nonzeroLocus b₀) W h₁ (𝟙 _) y hy, Category.id_comp,
    germPullback_restrict_eq (𝟙 Y.H.left) y h₂ hy]
  choose J hJ using fun ψ : Y.H.left ⟶ D.P.A.left => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart D.P.isLB (ψ y)
  have hG : Good D.P.L y J := hJ
  have e := h Y.H (𝟙 _) y J hG
  have e₀ := h₀ Y.H (𝟙 _) y J hG
  rw [Category.id_comp] at e e₀

  have hqy : Y.q.left y ∈ nonzeroLocus b₀ ⊓ LB.wchart D.P.L (D.famφB 0) (fun κ => J (Y.q.left ≫ D.famφB 0 κ)) :=
    ⟨h₁ hy, hG.mem (D.famφB 0) Y.q.left⟩
  have sb := congrArg (gs Y.q.left y _) (secRatio_on b₀ b (fun κ => J (Y.q.left ≫ D.famφB 0 κ))
    (W := nonzeroLocus b₀ ⊓ LB.wchart D.P.L (D.famφB 0) (fun κ => J (Y.q.left ≫ D.famφB 0 κ))) inf_le_left inf_le_right)
  rw [gs_mul _ y _ hqy] at sb
  erw [germPullback_restrict_eq _ y _ hqy, germPullback_restrict_eq _ y _ hqy, germPullback_restrict_eq _ y _ hqy] at sb

  have hyτ : (𝟙 Y.H.left) y ∈ nonzeroLocus τ₀ ⊓ LB.wchart D.P.L (fun _ : Fin 1 => Y.q.left) (fun _ : Fin 1 => J (𝟙 Y.H.left ≫ Y.q.left)) :=
    ⟨h₂ hy, hG.mem (fun _ : Fin 1 => Y.q.left) (𝟙 Y.H.left)⟩
  have sτ := congrArg (gs (𝟙 Y.H.left) y _) (secRatio_on τ₀ τ (fun _ : Fin 1 => J (𝟙 Y.H.left ≫ Y.q.left))
    (W := nonzeroLocus τ₀ ⊓ LB.wchart D.P.L (fun _ : Fin 1 => Y.q.left) (fun _ : Fin 1 => J (𝟙 Y.H.left ≫ Y.q.left))) inf_le_left inf_le_right)
  rw [gs_mul _ y _ hyτ] at sτ
  erw [germPullback_restrict_eq _ y _ hyτ, germPullback_restrict_eq _ y _ hyτ, germPullback_restrict_eq _ y _ hyτ] at sτ
  have hu : IsUnit (sval τ₀ (𝟙 Y.H.left) y J) :=
    (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs τ₀ (𝟙 Y.H.left) y hyτ.2).1 hyτ.1
  change sval τ (𝟙 Y.H.left) y J = _ * sval τ₀ (𝟙 Y.H.left) y J at sτ
  change sval b Y.q.left y J = _ * sval b₀ Y.q.left y J at sb
  change sval τ (𝟙 Y.H.left) y J = _ at e
  change sval τ₀ (𝟙 Y.H.left) y J = _ at e₀
  refine hu.mul_right_cancel ?_
  rw [← sτ, e, sb, e₀]
  exact (_root_.mul_assoc _ _ _).symm
end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueProjectiveSpaceMapsOfAgreeGeometricPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGlue

theorem hom_ext_of_geometric {Z P S : Scheme.{0}} [IsReduced Z] (q : P ⟶ S) [IsSeparated q] (a b : Z ⟶ P)
    (hq : a ≫ q = b ≫ q)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ Z), y ≫ a = y ≫ b) : a = b := by
  let T : Z → Scheme.{0} := fun z => Sp (AlgebraicClosure (Z.residueField z))
  let pt : ∀ z, T z ⟶ Z := fun z =>
    spMap (algebraMap (Z.residueField z) (AlgebraicClosure (Z.residueField z))) ≫ Z.fromSpecResidueField z
  let m : (∐ T) ⟶ Z := Sigma.desc pt
  have hs : Function.Surjective m.base := by
    intro z
    refine ⟨(Sigma.ι T z).base default, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
    simp only [pt, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have : IsDominant m := ⟨hs.denseRange⟩
  refine ext_of_isDominant_of_isSeparated q hq m ?_
  refine Sigma.hom_ext _ _ fun z => ?_
  simp only [m, Sigma.ι_desc_assoc]
  exact h _ (pt z)

theorem glue_geom : ∀ (o : Type) [CommRing o] (n : ℕ) (X : Scheme.{0}) [IsReduced X] (s : X ⟶ Sp o) (I : Type)
    (W : I → X.Opens) (f : ∀ i, (W i).toScheme ⟶ PSpace o n), (⨆ i, W i) = ⊤ →
    (∀ i, f i ≫ PSpace.str o n = (W i).ι ≫ s) →
    (∀ i j (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ (W i).toScheme) (y' : Sp K ⟶ (W j).toScheme),
      y ≫ (W i).ι = y' ≫ (W j).ι → y ≫ f i = y' ≫ f j) →
    ∃ g : X ⟶ PSpace o n, g ≫ PSpace.str o n = s ∧ ∀ i, (W i).ι ≫ g = f i := by
  intro o _ n X _ s I W f hW hf hg
  have : IsSeparated (PSpace.str o n) := by
    have := isProper_str o n
    infer_instance
  let 𝒰 := X.openCoverOfIsOpenCover W hW
  have hc : ∀ a b, pullback.fst (W a).ι (W b).ι ≫ f a = pullback.snd (W a).ι (W b).ι ≫ f b := by
    intro a b
    have : IsReduced (pullback (W a).ι (W b).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ (W a).ι)
    refine hom_ext_of_geometric (PSpace.str o n) _ _ ?_ fun K _ _ y => ?_
    · rw [Category.assoc, Category.assoc, hf, hf, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc]
      exact hg a b K _ _ (by rw [Category.assoc, Category.assoc, pullback.condition])
  have he : ∀ a, (W a).ι ≫ 𝒰.glueMorphisms f hc = f a := fun a => 𝒰.ι_glueMorphisms f hc a
  refine ⟨𝒰.glueMorphisms f hc, 𝒰.hom_ext _ _ fun (a : I) => ?_, he⟩
  change (W a).ι ≫ _ = (W a).ι ≫ _
  rw [← Category.assoc, he, hf]

end GlobalTheory.ThetaGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckExistenceClosedSubschemesSeparated
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem subsingleton_idealSheafData_of_isEmpty (W : Scheme.{0}) [IsEmpty W] :
    Subsingleton W.IdealSheafData := by
  constructor
  intro a b
  apply Scheme.IdealSheafData.ext
  funext U
  exact Subsingleton.elim _ _

theorem alg_of_isEmpty {R : Type} [CommRing R] {W : Scheme.{0}} [IsEmpty W]
    (f : W ⟶ Spec (CommRingCat.of R)) (I : Ideal R) : Alg f I := by
  have := subsingleton_idealSheafData_of_isEmpty W
  intro t _ hp
  exact ⟨t 0, hp 0, fun _ => Subsingleton.elim _ _⟩

theorem alg_of_isSeparated : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f →
      QuasiCompact f → Alg f I := by
  intro R _ _ I hI W₀ f₀ hsep hlft hqc
  have : IsLocallyNoetherian W₀ := LocallyOfFiniteType.isLocallyNoetherian f₀
  have : CompactSpace W₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  have : AlgebraicGeometry.IsNoetherian W₀ := {}
  suffices H : ∀ Z : TopologicalSpace.Closeds W₀, ∀ (W : Scheme.{0}) (i : W ⟶ W₀), IsClosedImmersion i →
      Set.range i ⊆ (Z : Set W₀) → Alg (i ≫ f₀) I by
    simpa using H ⊤ W₀ (𝟙 _) inferInstance (by simp)
  intro Z
  induction Z using WellFoundedLT.induction with
  | _ Z ih =>
  intro W i hi hZ
  have hsep' : IsSeparated (i ≫ f₀) := inferInstance
  have hlft' : LocallyOfFiniteType (i ≫ f₀) := inferInstance
  have hqc' : QuasiCompact (i ≫ f₀) := inferInstance
  by_cases hW : Nonempty W
  · obtain ⟨W', P, π, q, s, U, hπ, hU, hiso, hs, hq, hcomm⟩ :=
      _root_.GlobalTheory.FormalAlg.exists_isProper_isImmersion_isProjOver R W (i ≫ f₀) hsep' hlft' hqc' hW
    have hA : Alg (π ≫ i ≫ f₀) I := by
      rw [← hcomm]
      exact _root_.GlobalTheory.FormalAlg.alg_of_isImmersion_isProjOver R I hI W' P q s hs hq
    let K := Scheme.IdealSheafData.vanishingIdeal
      (⟨(U : Set W)ᶜ, U.isOpen.isClosed_compl⟩ : TopologicalSpace.Closeds W)
    have hK : ((K.support : Set W)) = (U : Set W)ᶜ := Scheme.IdealSheafData.coe_support_vanishingIdeal _
    refine _root_.GlobalTheory.FormalAlg.alg_of_modification R I W (i ≫ f₀) hsep' hlft' hqc' W' π U hπ hiso K ?_ hA ?_
    · intro x hx
      by_contra hxU
      apply hx
      rw [← SetLike.mem_coe, hK]
      exact hxU
    · intro k
      let Z' : TopologicalSpace.Closeds W₀ :=
        ⟨i '' (U : Set W)ᶜ, i.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
      have hlt : Z' < Z := by
        refine lt_of_le_of_ne ?_ ?_
        · rintro y ⟨x, _, rfl⟩
          exact hZ ⟨x, rfl⟩
        · intro heq
          obtain ⟨u, hu⟩ := hU
          have h1 : i u ∈ (Z : Set W₀) := hZ ⟨u, rfl⟩
          rw [← heq] at h1
          obtain ⟨x, hx, hxu⟩ := h1
          exact hx (i.isClosedEmbedding.injective hxu ▸ hu)
      have h2 := ih Z' hlt _ ((K ^ k).subschemeι ≫ i) inferInstance (by
        rintro _ ⟨x, rfl⟩
        refine ⟨(K ^ k).subschemeι x, ?_, rfl⟩
        have hsub : ((K ^ k).support : Set W) ⊆ (U : Set W)ᶜ := by
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · rw [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]
            intro y hy
            exact hy.elim
          · rw [Scheme.IdealSheafData.support_pow _ _ hk.ne', hK]
        apply hsub
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨x, rfl⟩)
      rwa [Category.assoc] at h2
  · have : IsEmpty W := not_nonempty_iff.1 hW
    exact alg_of_isEmpty _ I

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueIntegralGermFramePowerCharZeroStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.PowGerm GlobalTheory.PtTie GlobalTheory.RefSum
open GlobalTheory.ThetaLeast

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_value_integral_germ_frame_power_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), CharZero (IsLocalRing.ResidueField T.V) → letI := io.toAlgebra; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n k k' : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f → ∃ f' : PS T.Fr n (chD C.ch), IsIntPS T f' ∧ nabValN C.ch.B T.Fr C.ch.h H.w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) = nabValN C.ch.B T.Fr C.ch.h H.w0 k' f' (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
  first | exact @GlobalTheory.FramePower.exists_nabValN_eq_of_harmonic | exact GlobalTheory.FramePower.exists_nabValN_eq_of_harmonic | (intros; apply GlobalTheory.FramePower.exists_nabValN_eq_of_harmonic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetAddDirection
section
set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem jet_add_dir_of_hasLevel : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F →
    ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t v : ℂ) (κ : Emb F → ℕ), 0 < τ.im →
    jet (2 * s) L κ τ (c + v) t = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco (2 * s) (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i)) * jet (2 * s) L μ τ c t := by
  intro hE F _ _ _ hf s N L hs hN hL τ c t v κ hτ
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel F N L hN hL
  obtain ⟨Z, a, -, ha⟩ := _root_.GlobalTheory.HilbFam.exists_isCoef hE F hf 𝔞 𝔟 s hs
  exact _root_.GlobalTheory.HilbFam.jet_split_add F (2 * s) 𝔞 𝔟 _ a x τ c t v κ (even_two_mul s) ha hτ

end GlobalTheory.HilbFam
end
end

