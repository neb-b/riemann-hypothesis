module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1959
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1931
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BorelWeilFlagModelDetInverseIsAmpleLocal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

noncomputable section

namespace GlobalTheory.FlagPlucker


open GlobalTheory.FlagMod Formalism.L2.Pj in
theorem isAmpleLB_LL_flagModel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagModel Y) (z : Y.X), ∃ V : Y.X.Opens, z ∈ V ∧ IsAffineOpen V ∧ IsAmpleLB ((X.F.LL (fun ix => ix.elim 0 fun p => (Dw.mult p.1 : ℤ) - ((p.2 : ℕ) : ℤ))).pull (X.π ⁻¹ᵁ V).ι) := by
  intro E _ _ _ H Dw l Xo c Y X z
  have hprop : IsProper X.π := X.proper
  by_cases hz : z ∈ Set.range X.π.base
  · obtain ⟨y, rfl⟩ := hz
    obtain ⟨k0, hk0⟩ := TopologicalSpace.Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ y))
    have hzM : X.π y ∈ (X.F.M k0).U := X.F.le k0 hk0
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVM⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open
      (show X.π y ∈ ((X.F.M k0).U : Set Y.X) from hzM) (X.F.M k0).U.isOpen
    refine ⟨V, hzV, hV, ?_⟩
    have hg : ⊤ ≤ ((X.π ⁻¹ᵁ V).ι ≫ X.π) ⁻¹ᵁ (X.F.M k0).toMChart.U := fun p _ => hVM (by
      show X.π ((X.π ⁻¹ᵁ V).ι p) ∈ V
      have : (X.π ⁻¹ᵁ V).ι p ∈ X.π ⁻¹ᵁ V := by
        have h := Scheme.Opens.range_ι (X.π ⁻¹ᵁ V)
        exact (h.le ⟨p, rfl⟩ : _)
      exact this)
    have hf : IsProper ((X.π ∣_ V) ≫ hV.isoSpec.hom) := inferInstance
    choose t ht using fun (p : Σ σ : E →+* ℂ, Fin (Dw.mult σ)) (q : Fin (plkNum (X.F.M k0).toMChart p.2 + 1)) =>
      GlobalTheory.T.pluckerMinors_sections_inverseDetFlagBundle X.F (X.F.M k0).toMChart (X.π ⁻¹ᵁ V).ι hg p.1 p.2 q
    have hnz : ∀ p, ⨆ q, nonzeroLocus (t p q) = ⊤ := fun p =>
      _root_.GlobalTheory.FlagPlucker.iSup_nonzeroLocus_plk X.F (X.F.M k0).toMChart (X.π ⁻¹ᵁ V).ι hg p.1 p.2 (t p) (ht p)
    refine isAmpleLB_of_finite_fibres Γ(Y.X, V) _ ((X.π ∣_ V) ≫ hV.isoSpec.hom) hf (Σ σ : E →+* ℂ, Fin (Dw.mult σ))
      (fun p => (X.F.LL (ind p.1 p.2)).pull (X.π ⁻¹ᵁ V).ι) (fun p => LB.isLB_pull (X.F.isLB_LL _) _)
      (fun p => plkNum (X.F.M k0).toMChart p.2) t hnz ?_ (fun _ => 1) (fun _ => le_rfl) _
      (LB.isLB_pull (X.F.isLB_LL _) _) ?_
    · intro K _ _ a
      have hfin := X.fin K (a ≫ (X.π ⁻¹ᵁ V).ι)
      refine (hfin.preimage (f := fun a' : Sp K ⟶ _ => a' ≫ (X.π ⁻¹ᵁ V).ι)
        fun b _ b' _ e => (cancel_mono _).1 e).subset ?_
      rintro a' ⟨h1, h2⟩
      have e : (X.π ⁻¹ᵁ V).ι ≫ X.π = ((X.π ∣_ V) ≫ hV.isoSpec.hom) ≫ hV.fromSpec := by
        rw [← hV.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]
      have hx : a ≫ (X.π ⁻¹ᵁ V).ι ≫ X.π = a' ≫ (X.π ⁻¹ᵁ V).ι ≫ X.π := by
        rw [e]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ hV.fromSpec) h1.symm).trans (Category.assoc _ _ _))
      exact _root_.GlobalTheory.FlagPlucker.Sep.step_eq_of_toProj_eq X.F (X.F.M k0).toMChart (X.π ⁻¹ᵁ V).ι hg (fun σ m => t ⟨σ, m⟩)
        (fun σ m => ht ⟨σ, m⟩) (fun σ m => hnz ⟨σ, m⟩) _ K a a' hx (fun σ m => (h2 ⟨σ, m⟩).symm)
    · have he : (fun ix : Ix Dw => ix.elim 0 fun p => (Dw.mult p.1 : ℤ) - ((p.2 : ℕ) : ℤ)) =
          ∑ p : Σ σ : E →+* ℂ, Fin (Dw.mult σ), ind p.1 p.2 := by
        funext ix
        rcases ix with _ | ⟨σ, i⟩
        · simp [ind]
        · rw [Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single σ]
          · simp only [ind, Option.elim, true_and]
            rw [Finset.sum_boole]
            have : (Finset.univ.filter fun m : Fin (Dw.mult σ) => (i : ℕ) ≤ m) = Finset.Ici i := by
              ext m; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici, Fin.le_def]
            simp only [this, Fin.card_Ici]
            push_cast [Nat.cast_sub i.2.le]
            ring
          · intro σ' _ h
            refine Finset.sum_eq_zero fun m _ => ?_
            simp [ind, Ne.symm h]
          · simp
      have h2 : ∀ p : Σ σ : E →+* ℂ, Fin (Dw.mult σ),
          1 • CechPic.cls ((X.F.LL (ind p.1 p.2)).pull (X.π ⁻¹ᵁ V).ι) (LB.isLB_pull (X.F.isLB_LL _) _) =
            CechPic.pull (X.π ⁻¹ᵁ V).ι (CechPic.cls (X.F.LL (ind p.1 p.2)) (X.F.isLB_LL _)) :=
        fun p => one_smul _ _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [CechPic.cls_pull (X.F.isLB_LL _), Finset.sum_congr rfl fun p _ => h2 p, ← map_sum,
        ← GlobalTheory.T.cechPicardClass_gradedTensorBundle_finset_sum X.F Finset.univ (fun p : Σ σ : E →+* ℂ, Fin (Dw.mult σ) => ind p.1 p.2)]
      congr 2
      exact congrArg _ he
  · have hcl : IsClosed (Set.range X.π.base) := X.π.isClosedMap.isClosed_range
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVc⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open
      (show z ∈ (Set.range X.π.base)ᶜ from hz) hcl.isOpen_compl
    refine ⟨V, hzV, hV, ?_⟩
    haveI : IsEmpty (X.π ⁻¹ᵁ V).toScheme := ⟨fun p => hVc p.2 ⟨p.1, rfl⟩⟩
    haveI : IsAffine (X.π ⁻¹ᵁ V).toScheme := isAffine_of_isEmpty
    exact isAmpleLB_of_isAffine (LB.isLB_pull (X.F.isLB_LL _) _)

end GlobalTheory.FlagPlucker

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryComponentStalkRegularBoundaryIdealProdPa
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

theorem GlobalTheory.LogKSDiv.boundary_germ_snc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1), x ∉ (j₀ TF.Y Z).opensRange → IsRegularLocalRing ((X₀ TF.Y Z).presheaf.stalk x) ∧ ∃ (n : ℕ) (f : Fin n → (X₀ TF.Y Z).presheaf.stalk x) (J : Finset (Fin n)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp ((X₀ TF.Y Z).presheaf.stalk x) n f ∧ J.Nonempty ∧ Ideal.map (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx) ((Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U) = Ideal.span {∏ i ∈ J, f i} := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hx hnot
  classical
  obtain ⟨hreg, V, hyV, n, f', J, hrsp, hV⟩ := TF.snc ((barComp TF.Y Z).ι x)
  let φ : TF.Y.X.presheaf.stalk ((barComp TF.Y Z).ι x) ≃+* (X₀ TF.Y Z).presheaf.stalk x :=
    (asIso ((barComp TF.Y Z).ι.stalkMap x)).commRingCatIsoToRingEquiv
  have hφ : ∀ a, φ a = ((barComp TF.Y Z).ι.stalkMap x).hom a := fun _ => rfl
  refine ⟨IsRegularLocalRing.of_ringEquiv φ, n, fun i => φ (TF.Y.X.presheaf.germ V.1 _ hyV (f' i)), J, ?_, ?_, ?_⟩
  · obtain ⟨hspan, hdim⟩ := hrsp
    refine ⟨?_, hdim.trans (ringKrullDim_eq_of_ringEquiv φ)⟩
    have hr : Set.range (fun i => φ (TF.Y.X.presheaf.germ V.1 _ hyV (f' i))) =
        φ '' Set.range (fun i => TF.Y.X.presheaf.germ V.1 _ hyV (f' i)) := Set.range_comp _ _
    rw [hr, ← Ideal.map_span, hspan]
    exact (IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv φ))
  · rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hnot
    rw [Finset.prod_empty, Ideal.span_singleton_one] at hV
    have hst : ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (LogKS.boundary TF.Y) ((barComp TF.Y Z).ι x) = ⊤ := by
      rw [ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ V _ hyV, hV, Ideal.map_top]
    have hns := (ReciprocityTheory.AnForm.R.mem_support_iff_stalkId (LogKS.boundary TF.Y) ((barComp TF.Y Z).ι x)).not.mpr
      (not_not.mpr hst)
    rw [LogKS.boundary, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hns
    have hin : (barComp TF.Y Z).ι x ∈ LogKS.interior TF.Y := by
      simpa using hns
    rw [LogKS.interior] at hin
    obtain ⟨z, hz⟩ := hin
    have hzB : z ∈ TF.Y.j ⁻¹ᵁ barComp TF.Y Z := by
      show TF.Y.j z ∈ barComp TF.Y Z
      rw [hz]; first | exact x.2 | simp | exact (barComp TF.Y Z).range_ι.le ⟨x, rfl⟩
    refine ⟨⟨z, hzB⟩, (barComp TF.Y Z).ι.isOpenEmbedding.injective ?_⟩
    have h2 := congrArg (fun f => f.base ⟨z, hzB⟩) (j₀_ι TF.Y Z)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2
    first | exact h2.trans hz | (refine Eq.trans ?_ hz; exact h2) | (rw [Scheme.Hom.comp_apply] at h2; exact h2.trans hz)
  · have e1 : Ideal.map (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx)
        ((Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U) =
        Ideal.map φ.toRingHom (Ideal.map (TF.Y.X.presheaf.germ U.1 _ hx).hom
          ((Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U)) := by
      rw [Ideal.map_map]
      congr 1
      ext r
      simp only [GlobalTheory.LogKSDiv.stalkHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hφ]
      rw [Scheme.Hom.germ_stalkMap_apply]
    have hVb : (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal V =
        Ideal.span {∏ i ∈ J, f' i} := hV
    rw [e1, ← ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ U _ hx, ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ V _ hyV, hVb,
      Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_prod]
    rw [map_prod]
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardEqZeroOfTrivialOnDisjointCover
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PicDisj

open TopologicalSpace

theorem map_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) = gm f y U a := by
  refine Units.ext ?_
  rw [gm, gm, dite_eq_left h, dite_eq_left (show (𝟙 X : X ⟶ X) (f y) ∈ U from h)]
  exact Scheme.Hom.germ_stalkMap_apply f U y h a.val

theorem gm_image {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) (V : Y.Opens) (h : y ∈ V) (a : Γ(Y, V)ˣ) :
    gm f y (f ''ᵁ V) (Units.map (f.appIso V).inv.hom.toMonoidHom a) = gm (𝟙 Y) y V a := by
  refine Units.ext ?_
  have h' : f y ∈ f ''ᵁ V := ⟨y, h, rfl⟩
  rw [gm, gm, dite_eq_left h', dite_eq_left (show (𝟙 Y : Y ⟶ Y) y ∈ V from h)]
  change (Y.presheaf.germ (f ⁻¹ᵁ (f ''ᵁ V)) y h').hom (((f.appIso V).inv ≫ f.app (f ''ᵁ V)).hom a.val) =
    (Y.presheaf.germ V y h).hom a.val
  rw [Scheme.Hom.appIso_inv_app]
  exact Y.presheaf.germ_res_apply _ y _ _

theorem exists_gen_of_rel {Y : Scheme.{0}} {N : LB Y} (hN : N.IsLB) (P : N.ι → ∀ y : Y, (Y.presheaf.stalk y)ˣ → Prop)
    (loc : ∀ p, ∀ y ∈ N.U p, ∃ W : Y.Opens, W ≤ N.U p ∧ y ∈ W ∧ ∃ s : Γ(Y, W)ˣ, ∀ y' ∈ W, P p y' (gm (𝟙 Y) y' W s))
    (cmp : ∀ p q y u u', y ∈ N.U p → y ∈ N.U q → P p y u → P q y u' → u = gm (𝟙 Y) y _ (N.g p q) * u') :
    ∃ t : N.Gen, t.IsGen := by
  have uniq : ∀ p y u u', y ∈ N.U p → P p y u → P p y u' → u = u' := fun p y u u' hy h h' => by
    have e := gm_cocycle hN (𝟙 Y) y hy hy hy
    rw [cmp p p y u u' hy hy h h', mul_eq_left.1 e, _root_.one_mul]
  have key : ∀ p, ∃ a : Γ(Y, N.U p)ˣ, ∀ y ∈ N.U p, P p y (gm (𝟙 Y) y _ a) := fun p => by
    choose W hW hy s hs using fun y : (N.U p : Set Y) => loc p y.1 y.2
    have cp : ∀ k l, res (inf_le_left : W k ⊓ W l ≤ W k) (s k) = res inf_le_right (s l) := fun k l =>
      unit_ext fun y h => by
        rw [gm_res _ y _ h, gm_res _ y _ h]
        exact uniq p y _ _ (hW k h.1) (hs k y h.1) (hs l y h.2)
    have hc : N.U p ≤ iSup W := fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hy _⟩
    obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' W (N.U p) (fun k => homOfLE (hW k)) hc (fun k => (s k).val)
      fun k l => congrArg Units.val (cp k l)
    have hu : IsUnit (M := Γ(Y, N.U p)) b := Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => by
      have := (s ⟨x, hx⟩).isUnit.map (Y.presheaf.germ _ x (hy ⟨x, hx⟩)).hom
      rw [← hb] at this
      exact (Y.presheaf.germ_res_apply (homOfLE (hW ⟨x, hx⟩)) x (hy ⟨x, hx⟩) b) ▸ this
    refine ⟨hu.unit, fun y h => ?_⟩
    have e : res (hW ⟨y, h⟩) hu.unit = s ⟨y, h⟩ := Units.ext (hb _)
    rw [← gm_res _ y (hW ⟨y, h⟩) (hy ⟨y, h⟩), e]
    exact hs _ y (hy _)
  choose a ha using key
  exact ⟨⟨a⟩, (isGen_iff_germ _).2 fun y i j hi hj => cmp i j y _ _ hi hj (ha i y hi) (ha j y hj)⟩

theorem eq_zero_of_pull_eq_zero : ∀ {Y : Scheme.{0}} {κ : Type} [Finite κ] {Z : κ → Scheme.{0}} (f : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (f i)], (⨆ i, (f i).opensRange = ⊤) → (Pairwise fun i i' => Disjoint (f i).opensRange (f i').opensRange) → ∀ d : Pic Y, (∀ i, GlobalTheory.CechPic.pull (f i) d = 0) → d = 0 := by
  intro Y κ _ Z f _ hcov hdis d hd
  obtain ⟨L, hL, rfl⟩ := cls_surj d
  choose t ht using fun i => (cls_eq_zero_iff (pull_isLB hL (f i))).1 (hd i)
  have surj : ∀ y : Y, ∃ i z, f i z = y := fun y => by
    have : y ∈ ⨆ i, (f i).opensRange := by rw [hcov]; trivial
    obtain ⟨i, z, hz⟩ := Opens.mem_iSup.1 this
    exact ⟨i, z, hz⟩
  refine (cls_eq_zero_iff hL).2 (exists_gen_of_rel hL (fun p y u => ∀ i (z : Z i) (u' : (Y.presheaf.stalk (f i z))ˣ),
    f i z = y → HEq u' u → Units.map ((f i).stalkMap z).hom.toMonoidHom u' =
      gm (𝟙 _) z ((L.pull (f i)).U fun _ => p) ((t i).s fun _ => p)) ?_ ?_)
  · intro p y hy
    obtain ⟨i, z, rfl⟩ := surj y
    refine ⟨f i ''ᵁ ((L.pull (f i)).U fun _ => p), ?_, ⟨z, mem_pull.2 hy, rfl⟩,
      Units.map ((f i).appIso _).inv.hom.toMonoidHom ((t i).s fun _ => p), ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact mem_pull.1 hw
    · rintro y' ⟨w, hw, hy'⟩ j z' u' rfl hu
      obtain rfl : i = j := by
        by_contra hne
        have hm : f j z' ∈ (f i).opensRange ⊓ (f j).opensRange := ⟨⟨w, hy'⟩, ⟨z', rfl⟩⟩
        rw [(hdis hne).eq_bot] at hm
        exact hm
      obtain rfl : w = z' := (f i).isOpenEmbedding.injective hy'
      rw [eq_of_heq hu, map_gm (f i) w _ (show f i w ∈ f i ''ᵁ ((L.pull (f i)).U fun _ => p) from ⟨w, hw, rfl⟩), gm_image _ _ _ hw]
  · intro p q y u u' hp hq h h'
    obtain ⟨i, z, rfl⟩ := surj y
    apply Units.map_injective (f := ((f i).stalkMap z).hom.toMonoidHom)
      (ConcreteCategory.bijective_of_isIso ((f i).stalkMap z)).1
    rw [map_mul, h i z u rfl HEq.rfl, h' i z u' rfl HEq.rfl, map_gm (f i) z (L.U p ⊓ L.U q) ⟨hp, hq⟩,
      (isGen_iff_germ _).1 (ht i) z (fun _ => p) (fun _ => q) (mem_pull.2 hp) (mem_pull.2 hq),
      gm_pull_g L (f i) (𝟙 _) z _ _ (mem_pull.2 hp) (mem_pull.2 hq), Category.id_comp]

end GlobalTheory.PicDisj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardEqZeroOfTwoOpenCoverUnitsSplit
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CechPic

open TopologicalSpace

theorem exists_units_of_gen_restrict {Z : Scheme.{0}} (L : LB Z) (O : Z.Opens) (t : LB.Gen (L.pull O.ι))
    (ht : t.IsGen) : ∃ b : ∀ i, Γ(Z, L.U i ⊓ O)ˣ, ∀ (i j : L.ι) (x : Z), x ∈ L.U i → x ∈ L.U j → x ∈ O →
      gm (𝟙 Z) x (L.U i ⊓ O) (b i) = gm (𝟙 Z) x (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 Z) x (L.U j ⊓ O) (b j) := by
  choose c hc using fun i : L.ι => exists_ext_unit O.ι ((L.pull O.ι).U (fun _ => i)) (t.s (fun _ => i))
  have le : ∀ i, L.U i ⊓ O ≤ O.ι ''ᵁ ((L.pull O.ι).U (fun _ => i)) := by
    intro i x hx
    have m : (⟨x, hx.2⟩ : O.toScheme) ∈ (L.pull O.ι).U (fun _ => i) := mem_pull.2 hx.1
    exact ⟨⟨x, hx.2⟩, m, rfl⟩
  refine ⟨fun i => res (le i) (c i), fun i j x hi hj hx => ?_⟩
  let z : O.toScheme := ⟨x, hx⟩
  have mi : z ∈ (L.pull O.ι).U (fun _ => i) := mem_pull.2 hi
  have mj : z ∈ (L.pull O.ι).U (fun _ => j) := mem_pull.2 hj
  have hW : O.ι z ∈ L.U i ⊓ L.U j ⊓ O := ⟨⟨hi, hj⟩, hx⟩
  have hWi : O.ι z ∈ L.U i ⊓ O := ⟨hi, hx⟩
  have hWj : O.ι z ∈ L.U j ⊓ O := ⟨hj, hx⟩
  have hWij : O.ι z ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  have l₁ : L.U i ⊓ L.U j ⊓ O ≤ L.U i ⊓ L.U j := inf_le_left
  have l₂ : L.U i ⊓ L.U j ⊓ O ≤ L.U j ⊓ O := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have key := gm_inj O.ι z (U := L.U i ⊓ O) (U' := L.U i ⊓ L.U j ⊓ O) hWi hW
    (a := res (le i) (c i)) (b := res l₁ (L.g i j) * res l₂ (res (le j) (c j))) (by
      rw [map_mul, gm_res O.ι z l₁ hW, gm_res O.ι z l₂ hW, gm_res O.ι z (le j) hWj, gm_res O.ι z (le i) hWi]
      have e₁ := hc i O.toScheme (𝟙 _) z mi
      have e₂ := hc j O.toScheme (𝟙 _) z mj
      rw [Category.id_comp] at e₁ e₂
      rw [e₁, e₂, (isGen_iff_germ t).1 ht z _ _ mi mj, gm_pull_g L O.ι (𝟙 _) z _ _ mi mj, Category.id_comp])
  rw [map_mul, gm_res (𝟙 Z) (O.ι z) l₁ hW, gm_res (𝟙 Z) (O.ι z) l₂ hW] at key
  exact key

theorem eq_zero_of_pull_eq_zero_of_units_split : ∀ (Z : Scheme.{0}) (O O' : Z.Opens), O ⊔ O' = ⊤ →
    (∀ F : Γ(Z, O ⊓ O')ˣ, ∃ (u : Γ(Z, O)ˣ) (u' : Γ(Z, O')ˣ),
      F = res (inf_le_left : O ⊓ O' ≤ O) u * res (inf_le_right : O ⊓ O' ≤ O') u') →
    ∀ c : Pic Z, GlobalTheory.CechPic.pull O.ι c = 0 → GlobalTheory.CechPic.pull O'.ι c = 0 → c = 0 := by
  intro Z O O' hcov hsplit c hc hc'
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  rw [← cls_pull hL O.ι (pull_isLB hL O.ι)] at hc
  rw [← cls_pull hL O'.ι (pull_isLB hL O'.ι)] at hc'
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff _).1 hc
  obtain ⟨t', ht'⟩ := (cls_eq_zero_iff _).1 hc'
  obtain ⟨b, hb⟩ := exists_units_of_gen_restrict L O t ht
  obtain ⟨b', hb'⟩ := exists_units_of_gen_restrict L O' t' ht'
  have key₁ : ∀ {G : Type} [CommGroup G] (a x y : G), a * x * (a * y)⁻¹ = x * y⁻¹ := fun a x y => by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
  have key₂ : ∀ {G : Type} [CommGroup G] (a x y : G), a * x * y * x⁻¹ = a * y := fun a x y => by
    rw [mul_right_comm, mul_inv_cancel_right]

  let W : L.ι → Z.Opens := fun i => L.U i ⊓ (O ⊓ O')
  have lw : ∀ i, W i ≤ L.U i ⊓ O := fun i => inf_le_inf_left _ inf_le_left
  have lw' : ∀ i, W i ≤ L.U i ⊓ O' := fun i => inf_le_inf_left _ inf_le_right
  let q : ∀ i, Γ(Z, W i)ˣ := fun i => res (lw i) (b i) * (res (lw' i) (b' i))⁻¹
  have gq : ∀ i x, x ∈ W i → gm (𝟙 Z) x (W i) (q i) =
      gm (𝟙 Z) x (L.U i ⊓ O) (b i) * (gm (𝟙 Z) x (L.U i ⊓ O') (b' i))⁻¹ := fun i x hx => by
    simp only [q, map_mul, map_inv, gm_res (𝟙 Z) x (lw i) hx, gm_res (𝟙 Z) x (lw' i) hx]
  obtain ⟨F, hF⟩ := glue_unit (O ⊓ O') W (fun i => inf_le_right) (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hL x
      exact Opens.mem_iSup.2 ⟨i, hi, hx⟩) q (fun i j x hx => by
      rw [gq i x hx.1, gq j x hx.2, hb i j x hx.1.1 hx.2.1 hx.1.2.1, hb' i j x hx.1.1 hx.2.1 hx.1.2.2, key₁])
  obtain ⟨u, u', hu⟩ := hsplit F

  have gF : ∀ i x, x ∈ W i → gm (𝟙 Z) x (L.U i ⊓ O) (b i) =
      gm (𝟙 Z) x (L.U i ⊓ O') (b' i) * gm (𝟙 Z) x O u * gm (𝟙 Z) x O' u' := fun i x hx => by
    have e := congrArg (gm (𝟙 Z) x (W i)) (hF i)
    rw [gm_res (𝟙 Z) x _ hx, gq i x hx, hu, map_mul, gm_res (𝟙 Z) x _ hx.2, gm_res (𝟙 Z) x _ hx.2] at e
    rw [(mul_inv_eq_iff_eq_mul).1 e.symm]
    ac_rfl

  have loc : ∀ i, ∃ s : Γ(Z, L.U i)ˣ,
      (∀ y, y ∈ L.U i → y ∈ O → gm (𝟙 Z) y (L.U i) s = gm (𝟙 Z) y (L.U i ⊓ O) (b i) * (gm (𝟙 Z) y O u)⁻¹) ∧
      (∀ y, y ∈ L.U i → y ∈ O' → gm (𝟙 Z) y (L.U i) s = gm (𝟙 Z) y (L.U i ⊓ O') (b' i) * gm (𝟙 Z) y O' u') := by
    intro i
    let V : Bool → Z.Opens := fun β => Bool.rec (L.U i ⊓ O') (L.U i ⊓ O) β
    let v : ∀ β, Γ(Z, V β)ˣ := fun β => Bool.rec (motive := fun β => Γ(Z, V β)ˣ)
      (b' i * res (inf_le_right : L.U i ⊓ O' ≤ O') u') (b i * (res (inf_le_right : L.U i ⊓ O ≤ O) u)⁻¹) β
    have hV : ∀ β, V β ≤ L.U i := fun β => by cases β <;> exact inf_le_left
    have g₁ : ∀ y, y ∈ L.U i ⊓ O → gm (𝟙 Z) y (V true) (v true) =
        gm (𝟙 Z) y (L.U i ⊓ O) (b i) * (gm (𝟙 Z) y O u)⁻¹ := fun y hy => by
      show gm (𝟙 Z) y (L.U i ⊓ O) (b i * (res (inf_le_right : L.U i ⊓ O ≤ O) u)⁻¹) = _
      rw [map_mul, map_inv, gm_res (𝟙 Z) y _ hy]
    have g₀ : ∀ y, y ∈ L.U i ⊓ O' → gm (𝟙 Z) y (V false) (v false) =
        gm (𝟙 Z) y (L.U i ⊓ O') (b' i) * gm (𝟙 Z) y O' u' := fun y hy => by
      show gm (𝟙 Z) y (L.U i ⊓ O') (b' i * res (inf_le_right : L.U i ⊓ O' ≤ O') u') = _
      rw [map_mul, gm_res (𝟙 Z) y _ hy]
    obtain ⟨s, hs⟩ := glue_unit (L.U i) V hV (fun y hy => by
        have h : y ∈ O ⊔ O' := hcov ▸ (trivial : y ∈ (⊤ : Z.Opens))
        rcases Opens.mem_sup.1 h with h | h
        · exact Opens.mem_iSup.2 ⟨true, hy, h⟩
        · exact Opens.mem_iSup.2 ⟨false, hy, h⟩) v (fun β β₂ y hy => by
        cases β <;> cases β₂
        · rfl
        · rw [g₀ y hy.1, g₁ y hy.2, gF i y ⟨hy.1.1, hy.2.2, hy.1.2⟩, key₂]
        · rw [g₁ y hy.1, g₀ y hy.2, gF i y ⟨hy.1.1, hy.1.2, hy.2.2⟩, key₂]
        · rfl)
    refine ⟨s, fun y hi ho => ?_, fun y hi ho => ?_⟩
    · have e := congrArg (gm (𝟙 Z) y (V true)) (hs true)
      rw [gm_res (𝟙 Z) y (hV true) (show y ∈ L.U i ⊓ O from ⟨hi, ho⟩)] at e
      exact e.trans (g₁ y ⟨hi, ho⟩)
    · have e := congrArg (gm (𝟙 Z) y (V false)) (hs false)
      rw [gm_res (𝟙 Z) y (hV false) (show y ∈ L.U i ⊓ O' from ⟨hi, ho⟩)] at e
      exact e.trans (g₀ y ⟨hi, ho⟩)
  choose s hs using loc
  refine (cls_eq_zero_iff hL).2 ⟨⟨s⟩, (isGen_iff_germ _).2 fun y i j hi hj => ?_⟩
  have h : y ∈ O ⊔ O' := hcov ▸ (trivial : y ∈ (⊤ : Z.Opens))
  rcases Opens.mem_sup.1 h with h | h
  · show gm (𝟙 Z) y (L.U i) (s i) = _ * gm (𝟙 Z) y (L.U j) (s j)
    rw [(hs i).1 y hi h, (hs j).1 y hj h, hb i j y hi hj h, _root_.mul_assoc]
  · show gm (𝟙 Z) y (L.U i) (s i) = _ * gm (𝟙 Z) y (L.U j) (s j)
    rw [(hs i).2 y hi h, (hs j).2 y hj h, hb' i j y hi hj h, _root_.mul_assoc]

end GlobalTheory.CechPic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFrameChangeDiagonalUnitsIntegralFrame
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntFrameDiag

theorem integralFrame_transport : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (x : Sp T.V ⟶ Y.X) (x' : Sp T.Fr ⟶ Y.X) (e : spMap (algebraMap T.V T.Fr) ≫ x = x'), Function.Injective (GlobalTheory.FlagMod.tanPull (G := Y.t.G) (algebraMap T.V T.Fr) e) → ∀ (G : SAB H (Sp T.V)) (ψ : SABMap G Y.t x) (τ : E →+* ℂ) (ub : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb ub a w) → ∃ ub' : Fin (Dw.mult τ) → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G, (∀ i, (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (ub' i)).left = (ub i).left ≫ ψ.φ) ∧ ∀ v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G, GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e v ∈ GlobalTheory.FlagMod.eigLie c x' τ → ∃ a : Fin (Dw.mult τ) → T.V, ∑ i, a i • ub' i = v := by
  intro E _ _ _ H Dw l Xo c O _ β Y T io
  letI := io.toAlgebra
  intro x x' e hinj G ψ τ ub hT hS
  choose ub' hub' using fun i => GlobalTheory.T.exists_modelTangent_of_pullback_tangent x G ψ (ub i) (hT i)
  refine ⟨ub', hub', fun v hv => ?_⟩
  obtain ⟨w, hw, hvw⟩ := _root_.GlobalTheory.TanLiftPull.exists_isTan_lift x G ψ v
  obtain ⟨a, ha, -⟩ := hS w hw (GlobalTheory.T.isEigenvector_integral_of_tangentPullback_mem T io x x' e hinj G ψ τ w v hvw hv)
  exact ⟨a, _root_.GlobalTheory.TanComb.tanComb x G ψ ub ub' a w v hub' hvw ha⟩

theorem diag_unit_of_intFr : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y' : IntFr Xo c T io) (z : Sp T.V ⟶ X.YY), (X.ptY y'.1 = Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ z) → ∀ (k : X.F.J), ⊤ ≤ z ⁻¹ᵁ X.F.U k → ∀ (hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), (X.F.ChartFr k (X.pt y'.1 ≫ X.inc) hz Q) → (FrBor t Q y'.1) → ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)), ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = (t (some ⟨σ, i⟩) : T.Fr) := by
  intro E _ _ _ H Dw l Xo c Y X T io
  letI := io.toAlgebra
  intro y' z hz0 k hzk hz Q t hQ ht σ i
  have hφ : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  have hl : X.F.Lies (spMap (algebraMap T.V T.Fr) ≫ z) y'.1 := by
    rw [← show X.ptY y'.1 = spMap (algebraMap T.V T.Fr) ≫ z from hz0]
    exact X.lies_ptY y'.1
  have e : spMap (algebraMap T.V T.Fr) ≫ z ≫ X.π = GlobalTheory.FlagMod.frX y'.1 ≫ Y.j := by
    rw [← Category.assoc]; exact hl.1
  obtain ⟨-, G, t', m1, m2, ⟨ub, hT, -, hS, hU⟩, -⟩ := y'.2
  obtain ⟨ψ, ρ, h1, h2, h3⟩ := GlobalTheory.T.exists_semiAbelianMap_model_of_integralFramedPoint Y T io y'.1 (z ≫ X.π) e G t' m1 m2
  have hx : ⊤ ≤ (z ≫ X.π) ⁻¹ᵁ (X.F.M k).toMChart.U := X.F.inM hzk rfl
  have hx' : ⊤ ≤ (GlobalTheory.FlagMod.frX y'.1 ≫ Y.j) ⁻¹ᵁ (X.F.M k).toMChart.U :=
    e ▸ GlobalTheory.FlagMod.le_preimage_comp _ hx
  have hinj : Function.Injective (GlobalTheory.FlagMod.tanPull (G := Y.t.G) (algebraMap T.V T.Fr) e) := by
    intro u u' huu
    obtain ⟨cv, rfl⟩ := (GlobalTheory.FlagMod.vec (X.F.M k).toMChart _ hx).surjective u
    obtain ⟨cv', rfl⟩ := (GlobalTheory.FlagMod.vec (X.F.M k).toMChart _ hx).surjective u'
    rw [GlobalTheory.FlagMod.tanPull_vec _ _ e hx hx', GlobalTheory.FlagMod.tanPull_vec _ _ e hx hx'] at huu
    have := (GlobalTheory.FlagMod.vec (X.F.M k).toMChart _ hx').injective huu
    congr 1
    funext j
    exact hφ (congrFun this j)
  obtain ⟨ub', hl', hsp⟩ := integralFrame_transport T io (z ≫ X.π) _ e hinj G ψ σ (ub σ) (hT σ) (hS σ)
  have hub : ∀ j, GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e (ub' j) = GlobalTheory.FlagMod.frVec Y y'.1 rfl σ j := by
    intro j
    obtain ⟨u', hu1, hu2⟩ := hU σ j
    exact GlobalTheory.T.frameVector_eq_integralFrameTangent_on_model T io y'.1 (z ≫ X.π) e G t' m1 m2 ψ ρ h1 h2 h3 σ j (ub σ j) u' hu1 hu2 (ub' j) (hl' j)
  have key : ∀ (w : Sp T.Fr ⟶ X.YY) (_ : w = spMap (algebraMap T.V T.Fr) ≫ z) (hzw : ⊤ ≤ w ⁻¹ᵁ X.F.U k),
      X.F.ChartFr k w hzw Q → X.F.ChartFr k (spMap (algebraMap T.V T.Fr) ≫ z) (GlobalTheory.FlagMod.le_preimage_comp _ hzk) Q := by
    rintro _ rfl _ h
    exact h
  have hQ' := key _ ((X.pt_inc _).trans hz0) hz hQ
  exact (X.top.diag_unit (algebraMap T.V T.Fr) hφ z hzk hl e σ ub' hub hsp hQ' ht).2 i

end GlobalTheory.IntFrameDiag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceSectionIntersectionNumberEqBaseStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleSpace_section_intersectionNumber_eq_base : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ (y : Fin Y.dim → CartierDiv W.Z) (e : Fin Y.dim → Y.Dv), (∀ i, IsPull W.p₁ (y i) (e i) ∨ IsPull W.p₂ (y i) (e i)) → letI := algebraΓOfHom (W.p₁ ≫ Y.str); interNumRed F (⟨closure {W.δ (genericPoint Y.X)}, isClosed_closure⟩ : Closeds W.Z) (fun i => toLB (y i)) = Y.inter e := by
  first | exact @GlobalTheory.FlagPush.interNumRed_section | exact GlobalTheory.FlagPush.interNumRed_section | (intros; apply GlobalTheory.FlagPush.interNumRed_section <;> assumption)
end

