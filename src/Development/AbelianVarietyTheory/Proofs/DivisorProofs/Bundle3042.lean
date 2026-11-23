module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTripleProductMapLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3028
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedSectionOffClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open CubeCarried

theorem exists_secOver_of_gen {X : Scheme.{0}} (L : LB X) (W : X.Opens) (g : W.toScheme ⟶ X) (hg : g = W.ι)
    (t : LB.Gen (L.pull g)) (ht : t.IsGen) :
    ∃ s : ∀ k, Γ(X, W ⊓ L.U k), IsSecOver L W s ∧
      (∀ (z : X) (k : L.ι), z ∈ W → z ∈ L.U k → IsUnit (gs (𝟙 X) z (W ⊓ L.U k) (s k))) ∧
      ∀ (f : X ⟶ X) (w : LB.Iso L (L.pull f)), W ≤ f ⁻¹ᵁ W →
        (∀ (Z : Scheme.{0}) (r r' : Z ⟶ W) (z : Z) (j k : L.ι), r' ≫ W.ι = (r ≫ W.ι) ≫ f →
          g (r' z) ∈ L.U j → g (r z) ∈ L.U k →
          gm r' z ((L.pull g).U (fun _ => j)) (t.s (fun _ => j)) =
            gw w (r ≫ g) z j k * gm r z ((L.pull g).U (fun _ => k)) (t.s (fun _ => k))) →
        SecCarriedOver L W s f w := by
  subst hg
  obtain ⟨s, hs⟩ := exists_sec_of_gen L W t
  have inj : ∀ z : W.toScheme, Function.Injective (W.ι.stalkMap z).hom := fun z =>
    (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap z)).1
  have v : ∀ (z : W.toScheme) (k : L.ι), W.ι z ∈ L.U k →
      (W.ι.stalkMap z).hom (gs (𝟙 X) (W.ι z) (W ⊓ L.U k) (s k)) =
        (gm (𝟙 _) z ((L.pull W.ι).U (fun _ => k)) (t.s (fun _ => k))).val := fun z k hk => by
    rw [← gs_eq_map_gs W.ι z _ (show W.ι z ∈ W ⊓ L.U k from ⟨z.2, hk⟩), ← hs _ (𝟙 _) z k hk, Category.id_comp]
  refine ⟨s, fun z k k' hz hk hk' => ?_, fun z k hz hk => ?_, fun f w hf H z j k hz hfz hk hj => ?_⟩
  · obtain ⟨z, rfl⟩ : ∃ z' : W.toScheme, W.ι z' = z := ⟨⟨z, hz⟩, rfl⟩
    apply inj z
    rw [map_mul, v z k hk, v z k' hk', ← gm_val_map W.ι z (L.U k ⊓ L.U k') ⟨hk, hk'⟩, ← Units.val_mul]
    congr 1
    refine (gen_trans ht (𝟙 _) z (j := fun _ => k) (j' := fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')).trans ?_
    rw [trF, Fintype.prod_unique, zpow_one, Category.id_comp]
    rfl
  · obtain ⟨z, rfl⟩ : ∃ z' : W.toScheme, W.ι z' = z := ⟨⟨z, hz⟩, rfl⟩
    refine (isUnit_map_iff (W.ι.stalkMap z).hom _).1 ?_
    rw [v z k hk]
    exact Units.isUnit _
  · obtain ⟨z, rfl⟩ : ∃ z' : W.toScheme, W.ι z' = z := ⟨⟨z, hz⟩, rfl⟩
    apply inj z
    have hr : f.resLE W W hf ≫ W.ι = (𝟙 _ ≫ W.ι) ≫ f := by simp
    have hj' : W.ι (f.resLE W W hf z) ∈ L.U j := by
      rw [← Scheme.Hom.comp_apply, hr]; exact hj
    have e := congrArg Units.val (H _ (𝟙 _) (f.resLE W W hf) z j k hr hj' hk)
    rw [← hs _ _ z j hj', hr, Category.id_comp, Units.val_mul] at e
    rw [map_mul, v z k hk, ← CubeCarried.gs_comp W.ι f z (W ⊓ L.U j) ⟨hfz, hj⟩, e]
    exact congrArg₂ (· * ·) (gm_val_map W.ι z ((L.pull f).U (fun _ => j) ⊓ L.U k) ⟨mem_pull.2 hj, hk⟩ _) rfl


set_option maxHeartbeats 1000000 in
theorem exists_carried_sec_off_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ s : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k), IsSecOver U'.LG.L (β ⁻¹ᵁ V) s ∧ (∀ (z : G'.left) (k : U'.LG.L.ι), β z = y → z ∈ U'.LG.L.U k → IsUnit (gs (𝟙 G'.left) z (β ⁻¹ᵁ V ⊓ U'.LG.L.U k) (s k))) ∧ ∀ σ : Gal ρ, ∃ (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ ∧ ∃ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h ∧ SecCarriedOver U'.LG.L (β ⁻¹ᵁ V) s _ (Classical.choose hP.lg) := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact y hy
  obtain ⟨θ, hθ, O, hO, hnz⟩ := _root_.GlobalTheory.Mum.exists_carried_sec_nz_near_closed R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact
  have := hB.1.1
  have hfin : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).2 hF.2.2
  have hβf : IsFinite β := MorphismProperty.of_isPullback (P := @IsFinite) hβ.1.flip hfin
  let O' : G.left.Opens := ⟨farSet β θ, isOpen_farSet β β.isClosedMap θ⟩
  have hO' : ∃ g ∈ O', G.hom g = closedPoint R := by
    obtain ⟨g, hg, hgc⟩ := hO
    refine ⟨g, fun g' hg' => ?_, hgc⟩
    subst hg'
    exact hnz g' hg hgc
  obtain ⟨p, q, c, h⟩ := OffClosed.exists_ten R hB.1.2.2.2 G hS O' hO' y hy
  let V : G.left.Opens := ⟨⋂ f ∈ {f | f ∈ cubeTen (𝟙 G) p q c}, ((f.left ⁻¹ᵁ O' : G.left.Opens) : Set G.left),
    (List.finite_toSet _).isOpen_biInter fun f _ => (f.left ⁻¹ᵁ O').isOpen⟩
  have hyV : y ∈ V := Set.mem_iInter₂.2 h
  refine ⟨V, hyV, ?_⟩
  obtain ⟨hl, hm⟩ := grpPullback_points_lift_mul_inv _ _ (spMap ρ) G G' β hβ G' G β hβ.1.w
  obtain ⟨a', ha⟩ := hl p
  obtain ⟨b', hb⟩ := hl q
  obtain ⟨c', hc⟩ := hl c
  have h1 : (𝟙 G' : G' ⟶ G').left ≫ β = β ≫ (𝟙 G : G ⟶ G).left := by simp
  have mul := fun u v u' v' hu hv => (hm u v u' v' hu hv).1
  have inv := fun u u' hu => (hm u u u' u' hu hu).2
  have hten : ∀ f' ∈ cubeTen (𝟙 G') a' b' c', ∃ f ∈ cubeTen (𝟙 G) p q c, f'.left ≫ β = β ≫ f.left := by
    intro f' hf
    simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ ha)⟩
    · exact ⟨_, by simp [cubeTen], ha⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ ha⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hb⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 hc⟩
    · exact ⟨_, by simp [cubeTen], mul _ _ _ _ h1 (inv _ _ (mul _ _ _ _ hb hc))⟩
    · exact ⟨_, by simp [cubeTen], hb⟩
    · exact ⟨_, by simp [cubeTen], hc⟩
    · exact ⟨_, by simp [cubeTen], inv _ _ (mul _ _ _ _ hb hc)⟩
  choose hd bc hbc hP hov using a.unif
  let F : Gal ρ → (G'.left ⟶ G'.left) := fun σ => (bc σ).hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))
  have hFa : ∀ σ, F σ = a.act σ := hbc
  have hFc : ∀ σ, IsGrpPullback G' G' (spMap (Gal.hom σ)) (F σ) := fun σ => (hFa σ).symm ▸ a.cart σ
  have hFβ : ∀ σ, F σ ≫ β = β := fun σ => by rw [hFa, hact]
  let w : ∀ σ, LB.Iso U'.LG.L (U'.LG.L.pull (F σ)) := fun σ => Classical.choose (hP σ).lg
  have hw : ∀ σ, (w σ).IsGen := fun σ => (Classical.choose_spec (hP σ).lg).1
  have hrig : ∀ σ, PMaps (w σ) (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) U'.LG.rig U'.LG.rig
      (spMap (Gal.hom σ)) := fun σ => by
    obtain ⟨he, hr, -⟩ := (Classical.choose_spec (hP σ).lg).2
    exact (maps_iff (w σ) _ (fun _ => eSec G') _ U'.LG.rig U'.LG.rig (spMap (Gal.hom σ)) _
      (rigPull_le (F σ) (spMap (Gal.hom σ)) he U'.LG.L) (fun _ => rfl)).1 hr
  have comm : ∀ (u : G ⟶ G) (u' : G' ⟶ G'), u'.left ≫ β = β ≫ u.left → ∀ σ, u'.left ≫ F σ = F σ ≫ u'.left := by
    intro u u' hu σ
    have e₁ := hFβ σ
    have e₂ := (hFc σ).1.w
    generalize F σ = f at e₁ e₂ ⊢
    apply hβ.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, hu, ← Category.assoc, e₁]
    · rw [Category.assoc, Category.assoc, Over.w, e₂, ← Category.assoc, Over.w]
  obtain ⟨t, ht, hcar⟩ := exists_gen_carried U'.cubG hFc w hrig
    (fun σ => pmaps_cub R' _ D' A' G' U'.toUnifPre (hFc σ) (w σ) (hw σ)) θ
    (fun σ => hθ σ (hd σ) (bc σ) (hbc σ) (hP σ) (hov σ)) G' F (fun σ => (hFc σ).1.w) (𝟙 G') a' b' c'
    (comm _ _ h1) (comm _ _ ha) (comm _ _ hb) (comm _ _ hc) (β ⁻¹ᵁ V) (by
      intro f' hf' g hg
      obtain ⟨f, hf, e⟩ := hten f' hf'
      have h2 : f.left (β g) ∈ farSet β θ := Set.mem_iInter₂.1 hg f hf
      refine h2 (f'.left g) ?_
      rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply])
  obtain ⟨s, hs, hu, hcs⟩ := exists_secOver_of_gen U'.LG.L (β ⁻¹ᵁ V) _ (by simp) t ht
  refine ⟨s, hs, fun z k hz hk => hu z k (show β z ∈ V from hz ▸ hyV) hk, fun σ =>
    ⟨hd σ, bc σ, hbc σ, hP σ, hov σ, hcs (F σ) (w σ) (fun z hz => ?_) (hcar σ)⟩⟩
  show (F σ ≫ β) z ∈ V
  rw [hFβ]
  exact hz

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommutatorPairingValueHeckePoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeWeilLift

open GlobalTheory.CechPic

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB (A ⊗ A).left} (hL : L.IsLB)

def qc {T : Over S} (a b : T ⟶ A) : Pic T.left := pull (lift a b).left (cls L hL)

theorem pull_eq_qc {T : Over S} (f : T ⟶ A ⊗ A) :
    pull f.left (cls L hL) = qc hL (f ≫ fst A A) (f ≫ snd A A) := by
  unfold qc; rw [lift_comp_fst_snd]

omit [IsCommMonObj A] in
theorem translPt_fst {T : Over S} (x : T ⟶ A ⊗ A) :
    Out.translPt (A ⊗ A) x ≫ fst A A = (fst T (A ⊗ A) ≫ x ≫ fst A A) * (snd T (A ⊗ A) ≫ fst A A) := by
  have e : Out.translPt (A ⊗ A) x = (fst T (A ⊗ A) ≫ x) * snd T (A ⊗ A) := rfl
  rw [e, MonObj.mul_comp, Category.assoc]

omit [IsCommMonObj A] in
theorem translPt_snd {T : Over S} (x : T ⟶ A ⊗ A) :
    Out.translPt (A ⊗ A) x ≫ snd A A = (fst T (A ⊗ A) ≫ x ≫ snd A A) * (snd T (A ⊗ A) ≫ snd A A) := by
  have e : Out.translPt (A ⊗ A) x = (fst T (A ⊗ A) ≫ x) * snd T (A ⊗ A) := rfl
  rw [e, MonObj.mul_comp, Category.assoc]

variable {hL}


include hL in
theorem exists_theta_left
    (hB : ∀ (T : Over S) (x x' y : T ⟶ A), qc hL (x * x') y = qc hL x y + qc hL x' y)
    {T : Over S} (t : T ⟶ 𝟙_ (Over S)) (h : 𝟙_ (Over S) ⟶ A)
    (ht : ∃ u : (L.pull (lift (toUnit A ≫ h) (𝟙 A)).left).Gen, u.IsGen) :
    ∃ θ : Out.ThetaGrp (A ⊗ A) L 1 T, θ.pt = t ≫ lift h 1 := by
  have z : pull (lift (toUnit A ≫ h) (𝟙 A)).left (cls L hL) = 0 := by
    rw [← cls_pull hL _ (pull_isLB hL _)]; exact (cls_eq_zero_iff _).2 ht
  set b := snd T (A ⊗ A) ≫ snd A A
  have e1 : fst T (A ⊗ A) ≫ (t ≫ lift h 1) ≫ fst A A = b ≫ toUnit A ≫ h := by
    rw [Category.assoc, lift_fst, ← Category.assoc, ← Category.assoc,
      toUnit_unique (fst T (A ⊗ A) ≫ t) (b ≫ toUnit A)]
  have e2 : fst T (A ⊗ A) ≫ (t ≫ lift h 1) ≫ snd A A = 1 := by
    rw [Category.assoc, lift_snd, MonObj.comp_one, MonObj.comp_one]
  have e3 : qc hL (b ≫ toUnit A ≫ h) b = 0 := by
    unfold qc
    rw [show lift (b ≫ toUnit A ≫ h) b = b ≫ lift (toUnit A ≫ h) (𝟙 A) by
      rw [comp_lift, Category.comp_id], Over.comp_left, pull_comp, z, map_zero]
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (Out.thetaLB (A ⊗ A) L 1 (t ≫ lift h 1)), u.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
    rw [cls_linComb hL, Fin.sum_univ_two]
    show (1 : ℤ) • pull (snd T (A ⊗ A)).left _ + (-1 : ℤ) • pull (Out.translPt (A ⊗ A) (t ≫ lift h 1)).left _ = 0
    rw [pull_eq_qc, pull_eq_qc, translPt_fst, translPt_snd, e1, e2, _root_.one_mul, hB, e3]
    simp
  exact ⟨⟨_, u, hu⟩, rfl⟩


include hL in
theorem exists_theta_right
    (hB' : ∀ (T : Over S) (x y y' : T ⟶ A), qc hL x (y * y') = qc hL x y + qc hL x y')
    {T : Over S} (t : T ⟶ 𝟙_ (Over S)) (h : 𝟙_ (Over S) ⟶ A)
    (ht : ∃ u : (L.pull (lift (𝟙 A) (toUnit A ≫ h)).left).Gen, u.IsGen) :
    ∃ θ : Out.ThetaGrp (A ⊗ A) L 1 T, θ.pt = t ≫ lift 1 h := by
  have z : pull (lift (𝟙 A) (toUnit A ≫ h)).left (cls L hL) = 0 := by
    rw [← cls_pull hL _ (pull_isLB hL _)]; exact (cls_eq_zero_iff _).2 ht
  set a := snd T (A ⊗ A) ≫ fst A A
  have e1 : fst T (A ⊗ A) ≫ (t ≫ lift 1 h) ≫ snd A A = a ≫ toUnit A ≫ h := by
    rw [Category.assoc, lift_snd, ← Category.assoc, ← Category.assoc,
      toUnit_unique (fst T (A ⊗ A) ≫ t) (a ≫ toUnit A)]
  have e2 : fst T (A ⊗ A) ≫ (t ≫ lift 1 h) ≫ fst A A = 1 := by
    rw [Category.assoc, lift_fst, MonObj.comp_one, MonObj.comp_one]
  have e3 : qc hL a (a ≫ toUnit A ≫ h) = 0 := by
    unfold qc
    rw [show lift a (a ≫ toUnit A ≫ h) = a ≫ lift (𝟙 A) (toUnit A ≫ h) by
      rw [comp_lift, Category.comp_id], Over.comp_left, pull_comp, z, map_zero]
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (Out.thetaLB (A ⊗ A) L 1 (t ≫ lift 1 h)), u.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
    rw [cls_linComb hL, Fin.sum_univ_two]
    show (1 : ℤ) • pull (snd T (A ⊗ A)).left _ + (-1 : ℤ) • pull (Out.translPt (A ⊗ A) (t ≫ lift 1 h)).left _ = 0
    rw [pull_eq_qc, pull_eq_qc, translPt_fst, translPt_snd, e1, e2, _root_.one_mul, hB', e3]
    simp
  exact ⟨⟨_, u, hu⟩, rfl⟩

end General

end GlobalTheory.HeckeWeilLift

namespace GlobalTheory.HeckeWeilLift

open GlobalTheory.CechPic GlobalTheory.DiagPairing

theorem exists_weilIs_hecke : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∃ u : Γ((𝟙_ (Over S)).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) u := by
  intro p _ D R _ b g c k N hc hk hN hNp hsim hsurj hdiv S s o h₁ hh₁ h₂ hh₂
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ o.A), pc o.isLB (x * x') y = pc o.isLB x y + pc o.isLB x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), pc o.isLB x (y * y') = pc o.isLB x y + pc o.isLB x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hcls : cls _ hQ = (k ^ 2 / c) • cls o.P o.isLB := by
    refine (cls_linComb o.isLB (K := Fin (k ^ 2 / c)) (fun _ => 𝟙 _) (fun _ => 1) hQ).trans ?_
    simp [pull_id]
  have hQB : ∀ (T : Over S) (x x' y : T ⟶ o.A), qc hQ (x * x') y = qc hQ x y + qc hQ x' y :=
    fun T x x' y => by
      unfold qc
      rw [hcls, map_nsmul, map_nsmul, map_nsmul]
      exact (congrArg _ (hB T x x' y)).trans (smul_add _ _ _)
  have hQB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), qc hQ x (y * y') = qc hQ x y + qc hQ x y' :=
    fun T x y y' => by
      unfold qc
      rw [hcls, map_nsmul, map_nsmul, map_nsmul]
      exact (congrArg _ (hB' T x y y')).trans (smul_add _ _ _)
  obtain ⟨t₁, -⟩ := GlobalTheory.T.heckeSections_linearSimilitude_mem_kernel_polarisation p D R b g c k N hc hk hN hNp hsim hsurj hdiv S s o h₁ hh₁
  obtain ⟨-, t₂⟩ := GlobalTheory.T.heckeSections_linearSimilitude_mem_kernel_polarisation p D R b g c k N hc hk hN hNp hsim hsurj hdiv S s o h₂ hh₂
  have hA2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  exact CommutatorPairing.exists_weilIs hG hA2 hQ
    (fun _ => ⟨⊤, trivial, exists_theta_left hQB (Out.overResι ⊤) h₁ t₁⟩)
    (fun _ => ⟨⊤, trivial, exists_theta_right hQB' (Out.overResι ⊤) h₂ t₂⟩)

end GlobalTheory.HeckeWeilLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVROfFiniteEtaleBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open TensorProduct

namespace GlobalTheory.HenselLift

theorem exists_dvr_of_finite_etale : ∀ (A R V : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (ρ : A →+* R) (ψ : A →+* V), IsLocalHom ρ → ρ.Finite → ρ.Etale → IsCN V → IsDiscreteValuationRing V → IsLocalHom ψ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (κ : R →+* V'), IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp ρ = f.comp ψ := by
  intro A R V _ _ _ _ _ _ _ ρ ψ hρl hρf hρe hV hdvr hψ
  letI := ρ.toAlgebra
  letI := ψ.toAlgebra
  obtain ⟨hnoeth, hic, hcpl, hchar⟩ := hV
  haveI : Algebra.Etale A R := hρe
  haveI : Module.Finite A R := hρf
  haveI : IsLocalHom (algebraMap A R) := hρl
  haveI : IsLocalHom (algebraMap A V) := hψ
  haveI : Algebra.Etale V (V ⊗[A] R) := Algebra.Etale.baseChange A R V
  haveI : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  haveI : Nontrivial (V ⊗[A] R) := Module.FaithfullyFlat.rTensor_nontrivial A R V
  obtain ⟨q, hq⟩ := Ideal.exists_maximal (V ⊗[A] R)
  haveI : HenselianLocalRing V := GlobalTheory.henselianLocalRing_of_isAdicComplete V
  obtain ⟨e, he, H⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian V q
  haveI := GlobalTheory.isLocalRing_quotient_one_sub he q H
  haveI : IsLocalization.Away e (V ⊗[A] R ⧸ Ideal.span {1 - e}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem he
  haveI : Algebra.Etale (V ⊗[A] R) (V ⊗[A] R ⧸ Ideal.span {1 - e}) :=
    Algebra.Etale.of_isLocalizationAway e
  haveI : Algebra.Etale V (V ⊗[A] R ⧸ Ideal.span {1 - e}) :=
    Algebra.Etale.comp V (V ⊗[A] R) _
  haveI : Module.Finite V (V ⊗[A] R ⧸ Ideal.span {1 - e}) :=
    Module.Finite.trans (V ⊗[A] R) _
  have hfl : IsLocalHom (algebraMap V (V ⊗[A] R ⧸ Ideal.span {1 - e})) := by
    refine ((local_hom_tfae _).out 1 5).2 ?_
    have := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := V)
      (maximalIdeal (V ⊗[A] R ⧸ Ideal.span {1 - e}))
    exact IsLocalRing.eq_maximalIdeal this
  haveI := hfl
  obtain ⟨hdom, hdvr', -, hff, -⟩ :=
    GlobalTheory.isDiscreteValuationRing_of_etale_of_isLocalHom V (V ⊗[A] R ⧸ Ideal.span {1 - e})
  have hinj : Function.Injective (algebraMap V (V ⊗[A] R ⧸ Ideal.span {1 - e})) :=
    FaithfulSMul.algebraMap_injective _ _
  haveI : IsNoetherianRing V := hnoeth
  haveI : IsAdicComplete (maximalIdeal V) V := hcpl
  haveI : CharZero V := hchar
  obtain ⟨-, hcpl'⟩ := GlobalTheory.isLocalHom_and_isAdicComplete_of_finite_dvr V
    (V ⊗[A] R ⧸ Ideal.span {1 - e}) inferInstance hinj
  have hcomm : ((Ideal.Quotient.mk (Ideal.span {1 - e})).comp
      (Algebra.TensorProduct.includeRight.toRingHom)).comp ρ =
      (algebraMap V (V ⊗[A] R ⧸ Ideal.span {1 - e})).comp ψ := by
    ext a
    show Ideal.Quotient.mk _ ((1 : V) ⊗ₜ[A] ρ a) = Ideal.Quotient.mk _ (ψ a ⊗ₜ[A] (1 : R))
    rw [show ρ a = a • (1 : R) from Algebra.algebraMap_eq_smul_one a,
      show ψ a = a • (1 : V) from Algebra.algebraMap_eq_smul_one a, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  refine ⟨V ⊗[A] R ⧸ Ideal.span {1 - e}, inferInstance, hdom, inferInstance,
    algebraMap V _, (Ideal.Quotient.mk _).comp (Algebra.TensorProduct.includeRight.toRingHom),
    ⟨?_, inferInstance, hcpl', charZero_of_injective_algebraMap hinj⟩, hdvr', hinj,
    RingHom.finite_algebraMap.2 inferInstance, inferInstance, ?_, ?_⟩
  · exact isNoetherian_of_tower V inferInstance
  · refine ((local_hom_tfae _).out 1 5).2 ?_
    have hA : Ideal.comap (algebraMap A R) (Ideal.comap ((Ideal.Quotient.mk (Ideal.span {1 - e})).comp
        (Algebra.TensorProduct.includeRight.toRingHom)) (maximalIdeal _)) = maximalIdeal A := by
      have h1 : Ideal.comap (algebraMap V (V ⊗[A] R ⧸ Ideal.span {1 - e})) (maximalIdeal _) =
          maximalIdeal V := ((local_hom_tfae _).out 1 5).1 hfl
      have h2 : Ideal.comap ψ (maximalIdeal V) = maximalIdeal A := ((local_hom_tfae _).out 1 5).1 hψ
      change Ideal.comap ρ _ = _
      rw [Ideal.comap_comap, hcomm, ← Ideal.comap_comap, h1, h2]
    have hA' : (Ideal.comap (algebraMap A R) (Ideal.comap ((Ideal.Quotient.mk (Ideal.span {1 - e})).comp
        (Algebra.TensorProduct.includeRight.toRingHom)) (maximalIdeal _))).IsMaximal := by
      rw [hA]; exact maximalIdeal.isMaximal A
    have hm := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) _ hA'
    exact IsLocalRing.eq_maximalIdeal hm
  · exact hcomm

end GlobalTheory.HenselLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNatMulFiniteAdeleAwayPIntegral
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DenAway

open IsDedekindDomain

theorem isIntAf_algebraMap_inv_prime (p : ℕ) [Fact p.Prime] : IsIntAf (algebraMap ℚ (AfP p) (p : ℚ)⁻¹) := by
  intro v
  rw [AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.1.valuation ℚ (algebraMap ℤ ℚ (p : ℤ)) = 1 := by
    refine le_antisymm (v.1.valuation_le_one _) (not_lt.1 fun h => v.2 ?_)
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem] at h
    have hm : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp Fact.out).irreducible
    exact (hm.eq_of_le v.1.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm
  have h2 : Valued.v (algebraMap ℚ (v.1.adicCompletion ℚ) (p : ℚ)⁻¹) = v.1.valuation ℚ (p : ℚ)⁻¹ :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 _
  rw [h2, map_inv₀]
  simp only [eq_intCast, Int.cast_natCast] at h1
  rw [h1, inv_one]

theorem exists_coprime_nat_adele : ∀ (p : ℕ) [Fact p.Prime] (a : AfP p),
    ∃ j : ℕ, 0 < j ∧ j.Coprime p ∧ IsIntAf ((j : AfP p) * a) := by
  intro p _ a
  obtain ⟨n, hn, hna⟩ := exists_nat_adele a
  obtain ⟨e, j, hj, hnj⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p (Fact.out : p.Prime).ne_one
  have hj0 : 0 < j := Nat.pos_of_ne_zero fun h => hj (h ▸ dvd_zero p)
  refine ⟨j, hj0, ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hj).symm, ?_⟩
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have e1 : (j : AfP p) * a = algebraMap ℚ (AfP p) ((p : ℚ)⁻¹ ^ e) * ((n : AfP p) * a) := by
    rw [hnj, Nat.cast_mul, Nat.cast_pow, ← _root_.mul_assoc, ← _root_.mul_assoc]
    congr 1
    rw [← map_natCast (algebraMap ℚ (AfP p)) p, ← map_pow, ← map_mul, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero _ hp), map_one, _root_.one_mul]
  rw [e1]
  intro v
  rw [map_mul, map_pow]
  exact mul_mem (pow_mem (isIntAf_algebraMap_inv_prime p v) e) (hna v)

end GlobalTheory.DenAway
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeeperPointIntegralClosureStalkStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deeperPoint_integralClosure_stalk : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra; ∃ (z₂ : 𝔗.X₂.M.Z) (j₂ : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ →+* 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.p z₂ = z₁ ∧ (∀ b, 𝔗.X₂.M.stalkHom z₂ (j₂ b) = b) ∧ ((maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂).IsMaximal ∧ (∀ x : 𝔗.X₂.Ω₁, (∀ w, 𝔗.p w = z₁ → x ∈ 𝔗.X₂.M.O w) → x ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁) ∧ (∀ σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁, (∀ b b' : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, (b' : 𝔗.X₂.Ω₁) = σ b → (j₂ b ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂) ↔ j₂ b' ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂))) → ∃ σ₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ ≃+* 𝔗.X₂.M.Z.presheaf.stalk z₂, ∀ x, 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = σ (𝔗.X₂.M.stalkHom z₂ x)) ∧ ∀ (V : Type) [CommRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (V' : Type) [CommRing V'] (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective ev → Function.Injective io → 𝔗.Ext ev io ev₂ → Function.Injective ev₂ := by
  first | exact @GlobalTheory.GSep.Tower.exists_point_integralClosure_stalk | exact GlobalTheory.GSep.Tower.exists_point_integralClosure_stalk | (intros; apply GlobalTheory.GSep.Tower.exists_point_integralClosure_stalk <;> assumption)
end

