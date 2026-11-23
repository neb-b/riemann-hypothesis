module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorDescendedBundleNearClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2592
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2298
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameBundleNearClosedPointFiniteEtaleExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum


set_option maxHeartbeats 1000000 in
theorem exists_carried_frame_upstairs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (θ : U'.LG.L.Sec), (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → SecCarried U'.LG.L θ _ (Classical.choose hP.lg)) → ∀ O : G.left.Opens, (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g' : G'.left, β g' ∈ O → G.hom (β g') = closedPoint R → g' ∈ secNz θ) → ∀ y : G.left, IsClosed ({y} : Set G.left) → G.hom y = closedPoint R → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ₁ : R →+* R₁), FinExt ρ₁ ∧ ρ₁.Etale ∧ ∃ V₀ : G.left.Opens, y ∈ V₀ ∧ ∃ τ : ∀ k : U'.LG.L.ι, Γ(pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀) ⊓ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ U'.LG.L.U k)ˣ, FrameAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ ∧ (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → ∀ f' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), f' ≫ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ≫ a.act σ → f' ≫ (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) → FrameCarriedAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ _ (Classical.choose hP.lg) f') := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact θ hθ O hO hOθ y hyc hy
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have hN : IsNoetherianRing R := hR.1
  have hI : IsIntegrallyClosed R := hR.2.2.1
  have := hS.smooth
  have hρf : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff (CommRingCat.ofHom ρ)).2 hF.2.2
  have hβf : IsFinite β := MorphismProperty.of_isPullback hβ.1.flip hρf
  have hgi : GeometricallyIrreducible G.hom :=
    ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun Ω _ s => _root_.GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ G hS Ω s⟩
  have s₂ : Smooth (G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom G.hom ≫ G.hom))
  have i₂ : GeometricallyIrreducible (G ⊗ G).hom := GeometricallyIrreducible.comp (pullback.fst G.hom G.hom) G.hom
  have s₃ : Smooth (G ⊗ G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom (G ⊗ G).hom ≫ G.hom))
  have i₃ : GeometricallyIrreducible (G ⊗ G ⊗ G).hom :=
    GeometricallyIrreducible.comp (pullback.fst G.hom (G ⊗ G).hom) G.hom
  let O' : G.left.Opens := ⟨farSet β θ, isOpen_farSet β β.isClosedMap θ⟩
  obtain ⟨g, hgO, hg⟩ := hO
  have hgO' : g ∈ O' := fun g' e => by
    subst e
    exact hOθ g' hgO hg
  have hfin : IsFinite (G.left.fromSpecResidueField y ≫ G.hom) :=
    ClosedPt.isFinite_fromSpec G.hom y hyc (by rw [hy]; exact isClosed_singleton_closedPoint R)
  obtain ⟨N, hN₁, hN₂⟩ := ClosedPt.exists_open_good G.hom (G ⊗ G ⊗ G).hom y (ClosedPt.ten G)
    (fun f => f.left ⁻¹ᵁ O') fun f hf => by
      obtain ⟨q, h₁, h₂⟩ := ClosedPt.ten_meets G y g (hy.trans hg.symm) f hf
      exact ⟨q, show f.left q ∈ O' from h₁ ▸ hgO', h₂⟩
  rw [hy] at hN₁
  obtain ⟨R₁, _, _, _, ρ₁, t, hρ₁, het, ht, htN⟩ := _root_.GlobalTheory.Mum.exists_finEtale_section_of_smooth R hR (G ⊗ G ⊗ G) s₃ N hN₁
  have hρ₁f : IsFinite (spMap ρ₁) := (IsFinite.SpecMap_iff (CommRingCat.ofHom ρ₁)).2 hρ₁.2.2
  let m : pullback G.hom (spMap ρ₁) ⟶ pullback G.hom (G ⊗ G ⊗ G).hom :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ t) (by rw [Category.assoc, ht]; exact pullback.condition)
  have m₁ : m ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have m₂ : m ≫ pullback.snd _ _ = pullback.snd _ _ ≫ t := pullback.lift_snd _ _ _
  have hU : IsOpen {p | ∀ f ∈ ClosedPt.ten G, f.left (m p) ∈ O'} := by
    have : {p | ∀ f ∈ ClosedPt.ten G, f.left (m p) ∈ O'} =
        ⋂ f ∈ {f | f ∈ ClosedPt.ten G}, m ⁻¹' (f.left ⁻¹' O') := by ext; simp
    rw [this]
    exact (List.finite_toSet _).isOpen_biInter fun f _ => (O'.isOpen.preimage f.left.continuous).preimage m.continuous
  let V : G.left.Opens := ⟨_, ((pullback.fst G.hom (spMap ρ₁)).isClosedMap _ hU.isClosed_compl).isOpen_compl⟩
  have hyV : y ∈ V := by
    rintro ⟨p, hp, hpy⟩
    refine hp (hN₂ (m p) ?_ ?_)
    · rw [← Scheme.Hom.comp_apply, m₁, hpy]
    · rw [← Scheme.Hom.comp_apply, m₂, Scheme.Hom.comp_apply]
      exact htN ⟨_, rfl⟩
  have hgood : ∀ p : (pullback G.hom (spMap ρ₁) : Scheme.{0}), pullback.fst G.hom (spMap ρ₁) p ∈ V →
      ∀ f ∈ ClosedPt.ten G, f.left (m p) ∈ O' := fun p hp => by
    by_contra h
    exact hp ⟨p, h, rfl⟩
  let q := pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)
  let s := pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)
  have hqs : (q ≫ β) ≫ G.hom = s ≫ spMap ρ₁ := by
    rw [Category.assoc, hβ.1.w]; exact pullback.condition
  let n' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback G.hom (spMap ρ₁) := pullback.lift (q ≫ β) s hqs
  have n₁ : n' ≫ pullback.fst _ _ = q ≫ β := pullback.lift_fst _ _ _
  have n₂ : n' ≫ pullback.snd _ _ = s := pullback.lift_snd _ _ _
  let ζ : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ (G ⊗ G ⊗ G ⊗ G).left := n' ≫ m
  let T : Over (Sp R') := Over.mk (q ≫ G'.hom)
  have hζ : ζ ≫ (fst G (G ⊗ G ⊗ G)).left = q ≫ β := by
    change (n' ≫ m) ≫ pullback.fst G.hom (G ⊗ G ⊗ G).hom = _
    rw [Category.assoc, m₁, n₁]
  have hw : ζ ≫ (G ⊗ G ⊗ G ⊗ G).hom = T.hom ≫ spMap ρ := by
    rw [← Over.w (fst G (G ⊗ G ⊗ G)), ← Category.assoc, hζ, Category.assoc, hβ.1.w]
    exact (Category.assoc _ _ _).symm
  obtain ⟨hl, hm⟩ := _root_.GlobalTheory.Mum.grpPullback_points_lift_mul_inv (Sp R) (Sp R') (spMap ρ) G G' β hβ T (G ⊗ G ⊗ G ⊗ G) ζ hw
  obtain ⟨a₁, ha⟩ := hl (snd _ _ ≫ fst _ _)
  obtain ⟨b₁, hb⟩ := hl (snd _ _ ≫ snd _ _ ≫ fst _ _)
  obtain ⟨c₁, hc₁⟩ := hl (snd _ _ ≫ snd _ _ ≫ snd _ _)
  let x : T ⟶ G' := Over.homMk q rfl
  have hx : x.left ≫ β = ζ ≫ (fst G _).left := hζ.symm
  have mu := fun u v u' v' h₁ h₂ => (hm u v u' v' h₁ h₂).1
  have iv := fun u u' h₁ => (hm u u u' u' h₁ h₁).2
  have key : ∀ f' ∈ cubeTen x a₁ b₁ c₁, ∃ f ∈ ClosedPt.ten G, f'.left ≫ β = ζ ≫ f.left := by
    intro f hf
    simp only [cubeTen, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx ha⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx (iv _ _ ha)⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], ha⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], iv _ _ ha⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx hb⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx hc₁⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], mu _ _ _ _ hx (iv _ _ (mu _ _ _ _ hb hc₁))⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], hb⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], hc₁⟩
    · exact ⟨_, by simp [ClosedPt.ten, cubeTen], iv _ _ (mu _ _ _ _ hb hc₁)⟩
  have hten : ∀ g ∈ cubeTen x a₁ b₁ c₁, q ⁻¹ᵁ (β ⁻¹ᵁ V) ≤ g.left ⁻¹ᵁ secNz θ := by
    intro g' hg' z hz
    obtain ⟨f, hf, e⟩ := key g' hg'
    have hzV : pullback.fst G.hom (spMap ρ₁) (n' z) ∈ V := by
      rw [← Scheme.Hom.comp_apply, n₁, Scheme.Hom.comp_apply]; exact hz
    have h1 := hgood (n' z) hzV f hf
    refine h1 (g'.left z) ?_
    have e' := congrArg (fun φ => φ z) e
    simp only [Scheme.Hom.comp_apply] at e'
    exact e'
  obtain ⟨τ, hτ, hcar⟩ := GlobalTheory.T.exists_carriedFrame_theoremOfCube G' U'.LG U'.cubG θ T x a₁ b₁ c₁ (q ⁻¹ᵁ (β ⁻¹ᵁ V)) hten
  refine ⟨R₁, inferInstance, inferInstance, inferInstance, ρ₁, hρ₁, het, V, hyV, τ, hτ, ?_⟩
  intro σ h bc hbc hP hPO f' hf'q hf's
  have hc : IsGrpPullback G' G' (specOf (Gal.hom σ)) (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) :=
    hbc ▸ a.cart σ
  have hrc := GlobalTheory.T.rigidifiedGaloisLinearisation_carries_rigidification_cube R hB R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hact σ h bc hbc hP
  have hTw : f' ≫ T.hom = T.hom ≫ spMap (Gal.hom σ) := by
    change f' ≫ q ≫ G'.hom = (q ≫ G'.hom) ≫ _
    rw [← Category.assoc, hf'q, Category.assoc, (a.cart σ).1.w, Category.assoc]
  have hfn : f' ≫ n' = n' := by
    apply pullback.hom_ext
    · rw [Category.assoc, n₁, ← Category.assoc, hf'q, Category.assoc, hact]
    · rw [Category.assoc, n₂, hf's]
  have hfζ : f' ≫ ζ = ζ := by
    change f' ≫ n' ≫ m = n' ≫ m
    rw [← Category.assoc, hfn]
  have lift_eq : ∀ (u₁ : T ⟶ G') (u : G ⊗ G ⊗ G ⊗ G ⟶ G), u₁.left ≫ β = ζ ≫ u.left →
      u₁.left ≫ (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) = f' ≫ u₁.left := by
    intro u₁ u hu
    rw [hbc]
    apply hβ.1.hom_ext
    · rw [Category.assoc, hact, hu, Category.assoc f', hu, ← Category.assoc, hfζ]
    · have e₁ : u₁.left ≫ G'.hom = T.hom := Over.w u₁
      rw [Category.assoc, (a.cart σ).1.w, ← Category.assoc, e₁, Category.assoc, e₁, hTw]
  exact hcar (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) (specOf (Gal.hom σ)) hc
    (Classical.choose hP.lg) (Classical.choose_spec hP.lg).1 hrc.1 (hrc.2 hc) (hθ σ h bc hbc hP hPO) f' hTw
    (by rw [hbc]; exact hf'q.symm) (lift_eq a₁ _ ha) (lift_eq b₁ _ hb) (lift_eq c₁ _ hc₁)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingBoxProductOfRestrictedIsos
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdBoxIso

section Ext

variable {B B₁ B₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂}

theorem gm_ext_g {Z : Scheme.{0}} (ψ : Z ⟶ B) (z : Z) (a₁ a₁' : M₁.ι) (a₂ a₂' : M₂.ι)
    (h₁ : b₁ (ψ z) ∈ M₁.U a₁) (h₁' : b₁ (ψ z) ∈ M₁.U a₁') (h₂ : b₂ (ψ z) ∈ M₂.U a₂) (h₂' : b₂ (ψ z) ∈ M₂.U a₂') :
    gm ψ z ((extLB M₁ M₂ b₁ b₂).U (extIdx a₁ a₂) ⊓ (extLB M₁ M₂ b₁ b₂).U (extIdx a₁' a₂'))
        ((extLB M₁ M₂ b₁ b₂).g (extIdx a₁ a₂) (extIdx a₁' a₂')) =
      gm (ψ ≫ b₁) z _ (M₁.g a₁ a₁') * gm (ψ ≫ b₂) z _ (M₂.g a₂ a₂') := by
  have hm : ψ z ∈ (extLB M₁ M₂ b₁ b₂).U (extIdx a₁ a₂) ⊓ (extLB M₁ M₂ b₁ b₂).U (extIdx a₁' a₂') :=
    ⟨mem_extIdx h₁ h₂, mem_extIdx h₁' h₂'⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res ψ z _ hm _).trans ?_) ((gm_res ψ z _ hm _).trans ?_))
  · exact gm_pull_g M₁ b₁ ψ z (fun _ => a₁) (fun _ => a₁') (mem_pull.2 h₁) (mem_pull.2 h₁')
  · exact gm_pull_g M₂ b₂ ψ z (fun _ => a₂) (fun _ => a₂') (mem_pull.2 h₂) (mem_pull.2 h₂')

theorem gm_ext_change {w : LB.Iso M (extLB M₁ M₂ b₁ b₂)} (hw : w.IsGen) {Z : Scheme.{0}} (ψ : Z ⟶ B) (z : Z)
    (a₁ a₁' : M₁.ι) (a₂ a₂' : M₂.ι) (j j' : M.ι)
    (h₁ : b₁ (ψ z) ∈ M₁.U a₁) (h₁' : b₁ (ψ z) ∈ M₁.U a₁') (h₂ : b₂ (ψ z) ∈ M₂.U a₂) (h₂' : b₂ (ψ z) ∈ M₂.U a₂')
    (hj : ψ z ∈ M.U j) (hj' : ψ z ∈ M.U j') :
    gm ψ z _ (w.s (extIdx a₁ a₂, j)) =
      gm (ψ ≫ b₁) z _ (M₁.g a₁ a₁') * gm (ψ ≫ b₂) z _ (M₂.g a₂ a₂') * (gm ψ z _ (M.g j j'))⁻¹ *
        gm ψ z _ (w.s (extIdx a₁' a₂', j')) := by
  have hm : ψ z ∈ (LB.div (extLB M₁ M₂ b₁ b₂) M).U (extIdx a₁ a₂, j) ⊓
      (LB.div (extLB M₁ M₂ b₁ b₂) M).U (extIdx a₁' a₂', j') :=
    ⟨⟨mem_extIdx h₁ h₂, hj⟩, mem_extIdx h₁' h₂', hj'⟩
  have e := congrArg (gm ψ z _) (hw (extIdx a₁ a₂, j) (extIdx a₁' a₂', j'))
  have e' := (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div M (extLB M₁ M₂ b₁ b₂) ψ z _ _ hm) (gm_res ψ z _ hm _))))
  rw [gm_ext_g ψ z a₁ a₁' a₂ a₂' h₁ h₁' h₂ h₂'] at e'
  exact e'

end Ext

end GlobalTheory.ProdBoxIso

namespace GlobalTheory.ProdBoxIso

section Sq

variable {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁}
  {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p₁ : T₁ ⟶ B₁}
  {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂}

noncomputable def germ (p : T ⟶ B) (f : T ⟶ G) (h₁ : T ⟶ T₁) (h₂ : T ⟶ T₂) (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂))
    (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁))
    (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)) {Z : Scheme.{0}} (r : Z ⟶ T) (z : Z) (jM : M.ι) (jL : L.ι)
    (a₁ : M₁.ι) (a₂ : M₂.ι) (n₁ : L₁.ι) (n₂ : L₂.ι) : (Z.presheaf.stalk z)ˣ :=
  (gm (r ≫ p) z _ (wM.s (extIdx a₁ a₂, jM)))⁻¹ * gw we₁ (r ≫ h₁) z a₁ (fun _ => n₁) *
    gw we₂ (r ≫ h₂) z a₂ (fun _ => n₂) * gm (r ≫ f) z _ (wL.s (extIdx n₁ n₂, jL))

variable {p : T ⟶ B} {f : T ⟶ G} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂}

theorem germ_change (eM₁ : p ≫ b₁ = h₁ ≫ p₁) (eM₂ : p ≫ b₂ = h₂ ≫ p₂) (eL₁ : f ≫ g₁ = h₁ ≫ f₁)
    (eL₂ : f ≫ g₂ = h₂ ≫ f₂) {wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)} {wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)}
    {we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)} {we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)} (hwM : wM.IsGen)
    (hwL : wL.IsGen) (hw₁ : PGen we₁) (hw₂ : PGen we₂) {Z : Scheme.{0}} (r : Z ⟶ T) (z : Z)
    (jM jM' : M.ι) (jL jL' : L.ι) (a₁ a₁' : M₁.ι) (a₂ a₂' : M₂.ι) (n₁ n₁' : L₁.ι) (n₂ n₂' : L₂.ι)
    (cM : p (r z) ∈ M.U jM) (cM' : p (r z) ∈ M.U jM') (cL : f (r z) ∈ L.U jL) (cL' : f (r z) ∈ L.U jL')
    (c₁ : b₁ (p (r z)) ∈ M₁.U a₁) (c₁' : b₁ (p (r z)) ∈ M₁.U a₁')
    (c₂ : b₂ (p (r z)) ∈ M₂.U a₂) (c₂' : b₂ (p (r z)) ∈ M₂.U a₂')
    (d₁ : g₁ (f (r z)) ∈ L₁.U n₁) (d₁' : g₁ (f (r z)) ∈ L₁.U n₁')
    (d₂ : g₂ (f (r z)) ∈ L₂.U n₂) (d₂' : g₂ (f (r z)) ∈ L₂.U n₂') :
    germ p f h₁ h₂ wM wL we₁ we₂ r z jM jL a₁ a₂ n₁ n₂ =
      gm (r ≫ p) z _ (M.g jM jM') * (gm (r ≫ f) z _ (L.g jL jL'))⁻¹ *
        germ p f h₁ h₂ wM wL we₁ we₂ r z jM' jL' a₁' a₂' n₁' n₂' := by
  have q₁ : p₁ (h₁ (r z)) = b₁ (p (r z)) := congrArg (fun g => g (r z)) eM₁.symm
  have q₂ : p₂ (h₂ (r z)) = b₂ (p (r z)) := congrArg (fun g => g (r z)) eM₂.symm
  have k₁ : f₁ (h₁ (r z)) = g₁ (f (r z)) := congrArg (fun g => g (r z)) eL₁.symm
  have k₂ : f₂ (h₂ (r z)) = g₂ (f (r z)) := congrArg (fun g => g (r z)) eL₂.symm
  have A := gm_ext_change hwM (r ≫ p) z a₁ a₁' a₂ a₂' jM jM' c₁ c₁' c₂ c₂' cM cM'
  have C := gm_ext_change hwL (r ≫ f) z n₁ n₁' n₂ n₂' jL jL' d₁ d₁' d₂ d₂' cL cL'
  have W₁ := hw₁ Z (r ≫ h₁) z a₁ a₁' (fun _ => n₁) (fun _ => n₁') (q₁ ▸ c₁) (q₁ ▸ c₁')
    (mem_pull.2 (k₁ ▸ d₁)) (mem_pull.2 (k₁ ▸ d₁'))
  have W₂ := hw₂ Z (r ≫ h₂) z a₂ a₂' (fun _ => n₂) (fun _ => n₂') (q₂ ▸ c₂) (q₂ ▸ c₂')
    (mem_pull.2 (k₂ ▸ d₂)) (mem_pull.2 (k₂ ▸ d₂'))
  rw [gm_pull_g L₁ f₁ (r ≫ h₁) z (fun _ => n₁) (fun _ => n₁') (mem_pull.2 (k₁ ▸ d₁)) (mem_pull.2 (k₁ ▸ d₁')),
    Category.assoc, Category.assoc, ← eM₁, ← eL₁] at W₁
  rw [gm_pull_g L₂ f₂ (r ≫ h₂) z (fun _ => n₂) (fun _ => n₂') (mem_pull.2 (k₂ ▸ d₂)) (mem_pull.2 (k₂ ▸ d₂')),
    Category.assoc, Category.assoc, ← eM₂, ← eL₂] at W₂
  rw [Category.assoc, Category.assoc] at A C
  unfold germ
  rw [A, C, W₁, W₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Sq

end GlobalTheory.ProdBoxIso

namespace GlobalTheory.ProdBoxIso

section Glue

variable {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁}
  {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p₁ : T₁ ⟶ B₁}
  {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂}

theorem exists_unit (hM : M.IsLB) (hM₁ : M₁.IsLB) (hM₂ : M₂.IsLB) (hL : L.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB)
    (eM₁ : p ≫ b₁ = h₁ ≫ p₁) (eM₂ : p ≫ b₂ = h₂ ≫ p₂) (eL₁ : f ≫ g₁ = h₁ ≫ f₁)
    (eL₂ : f ≫ g₂ = h₂ ≫ f₂) {wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)} {wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)}
    {we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)} {we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)} (hwM : wM.IsGen)
    (hwL : wL.IsGen) (hw₁ : PGen we₁) (hw₂ : PGen we₂) (jM : M.ι) (jL : L.ι) :
    ∃ s : Γ(T, (M.pull p).U (fun _ => jM) ⊓ (L.pull f).U (fun _ => jL))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) (a₁ : M₁.ι) (a₂ : M₂.ι) (n₁ : L₁.ι) (n₂ : L₂.ι),
        p (r z) ∈ M.U jM → f (r z) ∈ L.U jL → b₁ (p (r z)) ∈ M₁.U a₁ → b₂ (p (r z)) ∈ M₂.U a₂ →
        g₁ (f (r z)) ∈ L₁.U n₁ → g₂ (f (r z)) ∈ L₂.U n₂ →
        gm r z _ s = germ p f h₁ h₂ wM wL we₁ we₂ r z jM jL a₁ a₂ n₁ n₂ := by
  have q₁ : ∀ x, p₁ (h₁ x) = b₁ (p x) := fun x => congrArg (fun g => g x) eM₁.symm
  have q₂ : ∀ x, p₂ (h₂ x) = b₂ (p x) := fun x => congrArg (fun g => g x) eM₂.symm
  have k₁ : ∀ x, f₁ (h₁ x) = g₁ (f x) := fun x => congrArg (fun g => g x) eL₁.symm
  have k₂ : ∀ x, f₂ (h₂ x) = g₂ (f x) := fun x => congrArg (fun g => g x) eL₂.symm
  obtain ⟨W, hW⟩ : ∃ W : M₁.ι × M₂.ι × L₁.ι × L₂.ι → T.Opens, ∀ a x, x ∈ W a ↔
      (p x ∈ M.U jM ∧ f x ∈ L.U jL) ∧ (b₁ (p x) ∈ M₁.U a.1 ∧ b₂ (p x) ∈ M₂.U a.2.1) ∧
        (g₁ (f x) ∈ L₁.U a.2.2.1 ∧ g₂ (f x) ∈ L₂.U a.2.2.2) :=
    ⟨fun a => (p ⁻¹ᵁ M.U jM ⊓ f ⁻¹ᵁ L.U jL) ⊓ ((p ⁻¹ᵁ (b₁ ⁻¹ᵁ M₁.U a.1) ⊓ p ⁻¹ᵁ (b₂ ⁻¹ᵁ M₂.U a.2.1)) ⊓
      (f ⁻¹ᵁ (g₁ ⁻¹ᵁ L₁.U a.2.2.1) ⊓ f ⁻¹ᵁ (g₂ ⁻¹ᵁ L₂.U a.2.2.2))), fun _ _ => Iff.rfl⟩
  have l₀ : ∀ a, W a ≤ (M.pull p).U (fun _ => jM) ⊓ (L.pull f).U (fun _ => jL) := fun a x hx =>
    ⟨mem_pull.2 ((hW a x).1 hx).1.1, mem_pull.2 ((hW a x).1 hx).1.2⟩
  have lM : ∀ a, W a ≤ p ⁻¹ᵁ ((LB.div (extLB M₁ M₂ b₁ b₂) M).U (extIdx a.1 a.2.1, jM)) := fun a x hx =>
    ⟨mem_extIdx ((hW a x).1 hx).2.1.1 ((hW a x).1 hx).2.1.2, ((hW a x).1 hx).1.1⟩
  have lL : ∀ a, W a ≤ f ⁻¹ᵁ ((LB.div (extLB L₁ L₂ g₁ g₂) L).U (extIdx a.2.2.1 a.2.2.2, jL)) := fun a x hx =>
    ⟨mem_extIdx ((hW a x).1 hx).2.2.1 ((hW a x).1 hx).2.2.2, ((hW a x).1 hx).1.2⟩
  have l₁ : ∀ a, W a ≤ h₁ ⁻¹ᵁ ((LB.div (M₁.pull p₁) (L₁.pull f₁)).U (fun _ => a.1, fun _ => a.2.2.1)) :=
    fun a x hx => ⟨mem_pull.2 ((q₁ x).symm ▸ ((hW a x).1 hx).2.1.1),
      mem_pull.2 ((k₁ x).symm ▸ ((hW a x).1 hx).2.2.1)⟩
  have l₂ : ∀ a, W a ≤ h₂ ⁻¹ᵁ ((LB.div (M₂.pull p₂) (L₂.pull f₂)).U (fun _ => a.2.1, fun _ => a.2.2.2)) :=
    fun a x hx => ⟨mem_pull.2 ((q₂ x).symm ▸ ((hW a x).1 hx).2.1.2),
      mem_pull.2 ((k₂ x).symm ▸ ((hW a x).1 hx).2.2.2)⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ a, Γ(T, W a)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) a, r z ∈ W a →
      gm r z (W a) (u a) = germ p f h₁ h₂ wM wL we₁ we₂ r z jM jL a.1 a.2.1 a.2.2.1 a.2.2.2 :=
    ⟨fun a => (res (lM a) (pullU p _ (wM.s (extIdx a.1 a.2.1, jM))))⁻¹ *
        res (l₁ a) (pullU h₁ _ (we₁.s (fun _ => a.1, fun _ => a.2.2.1))) *
        res (l₂ a) (pullU h₂ _ (we₂.s (fun _ => a.2.1, fun _ => a.2.2.2))) *
        res (lL a) (pullU f _ (wL.s (extIdx a.2.2.1 a.2.2.2, jL))),
      fun Z r z a hz => by
        simp only [map_mul, map_inv]
        rw [gm_res r z (lM a) hz, gm_pull r p z _ (lM a hz), gm_res r z (l₁ a) hz, gm_pull r h₁ z _ (l₁ a hz),
          gm_res r z (l₂ a) hz, gm_pull r h₂ z _ (l₂ a hz), gm_res r z (lL a) hz, gm_pull r f z _ (lL a hz)]
        rfl⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      obtain ⟨a₁, ha₁⟩ := exists_chart hM₁ (b₁ (p x))
      obtain ⟨a₂, ha₂⟩ := exists_chart hM₂ (b₂ (p x))
      obtain ⟨n₁, hn₁⟩ := exists_chart hL₁ (g₁ (f x))
      obtain ⟨n₂, hn₂⟩ := exists_chart hL₂ (g₂ (f x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a₁, a₂, n₁, n₂),
        (hW _ x).2 ⟨⟨mem_pull.1 hx.1, mem_pull.1 hx.2⟩, ⟨ha₁, ha₂⟩, ⟨hn₁, hn₂⟩⟩⟩) u
    (fun a a' x hx => by
      have i := (hW a x).1 hx.1
      have i' := (hW a' x).1 hx.2
      have k := germ_change eM₁ eM₂ eL₁ eL₂ hwM hwL hw₁ hw₂ (𝟙 T) x jM jM jL jL a.1 a'.1 a.2.1 a'.2.1
        a.2.2.1 a'.2.2.1 a.2.2.2 a'.2.2.2 i.1.1 i.1.1 i.1.2 i.1.2 i.2.1.1 i'.2.1.1 i.2.1.2 i'.2.1.2
        i.2.2.1 i'.2.2.1 i.2.2.2 i'.2.2.2
      rw [gm_self hM (𝟙 T ≫ p) x i.1.1, gm_self hL (𝟙 T ≫ f) x i.1.2, inv_one, _root_.one_mul,
        _root_.one_mul] at k
      exact (hu _ (𝟙 T) x a hx.1).trans (k.trans (hu _ (𝟙 T) x a' hx.2).symm))
  refine ⟨s, fun Z r z a₁ a₂ n₁ n₂ cM cL c₁ c₂ d₁ d₂ => ?_⟩
  have hz := (hW (a₁, a₂, n₁, n₂) (r z)).2 ⟨⟨cM, cL⟩, ⟨c₁, c₂⟩, ⟨d₁, d₂⟩⟩
  exact (gm_res r z (l₀ _) hz s).symm.trans ((congrArg (gm r z (W _)) (hs _)).trans (hu Z r z _ hz))

end Glue

end GlobalTheory.ProdBoxIso

namespace GlobalTheory.ProdBoxIso

theorem exists_wiso : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → wM.IsGen → wL.IsGen → we₁.IsGen → we₂.IsGen → ∃ we : LB.Iso (L.pull f) (M.pull p), we.IsGen ∧ BoxSq wM wL we we₁ we₂ h₁ h₂ := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂
    hM hM₁ hM₂ hL hL₁ hL₂ eM₁ eM₂ eL₁ eL₂ hwM hwL hw₁ hw₂
  rw [isGen_iff] at hw₁ hw₂
  choose s hs using exists_unit (h₁ := h₁) (h₂ := h₂) hM hM₁ hM₂ hL hL₁ hL₂ eM₁ eM₂ eL₁ eL₂ hwM hwL hw₁ hw₂
  refine ⟨⟨fun q => s (q.1 PUnit.unit) (q.2 PUnit.unit)⟩, (isGen_iff _).2 ?_, ?_⟩
  · intro Z r z j j' k k' a₂ b₂' a₄ b₄
    obtain ⟨a₁, ha₁⟩ := exists_chart hM₁ (b₁ (p (r z)))
    obtain ⟨a₂', ha₂⟩ := exists_chart hM₂ (b₂ (p (r z)))
    obtain ⟨n₁, hn₁⟩ := exists_chart hL₁ (g₁ (f (r z)))
    obtain ⟨n₂, hn₂⟩ := exists_chart hL₂ (g₂ (f (r z)))
    have a₄' : f (r z) ∈ L.U (k PUnit.unit) := mem_pull.1 a₄
    have b₄' : f (r z) ∈ L.U (k' PUnit.unit) := mem_pull.1 b₄
    have c := germ_change eM₁ eM₂ eL₁ eL₂ hwM hwL hw₁ hw₂ r z j j' (k PUnit.unit) (k' PUnit.unit) a₁ a₁ a₂' a₂'
      n₁ n₁ n₂ n₂ a₂ b₂' a₄' b₄' ha₁ ha₁ ha₂ ha₂ hn₁ hn₁ hn₂ hn₂
    rw [← hs j _ Z r z a₁ a₂' n₁ n₂ a₂ a₄' ha₁ ha₂ hn₁ hn₂, ← hs j' _ Z r z a₁ a₂' n₁ n₂ b₂' b₄' ha₁ ha₂ hn₁ hn₂] at c
    rw [gm_pull_g L f r z k k' a₄ b₄]
    exact c
  · intro Z r z J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
    have e := hs (J (r ≫ p)) (N (r ≫ f)) Z r z (J₁ ((r ≫ p) ≫ b₁)) (J₂ ((r ≫ p) ≫ b₂)) (N₁ ((r ≫ f) ≫ g₁))
      (N₂ ((r ≫ f) ≫ g₂)) (hJ _) (hN _) (hJ₁ _) (hJ₂ _) (hN₁ _) (hN₂ _)
    show om wM z J₁ J₂ J (r ≫ p) * gm r z _ (s (J (r ≫ p)) (N (r ≫ f))) = _
    rw [e]
    unfold germ om
    simp only [_root_.mul_assoc, mul_inv_cancel_left]

end GlobalTheory.ProdBoxIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeometricallyIntegralImageOfHomStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometricallyIntegral_image_of_hom : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), ∃ (Z : Over (Sp K)) (p : A.X ⟶ Z) (i : Z ⟶ B.X), p ≫ i = f.hom ∧ Surjective p.left ∧ IsClosedImmersion i.left ∧ GeometricallyIntegral Z.hom := by
  first | (exact @GlobalTheory.AV.AbVar.exists_image_geometricallyIntegral) | (exact GlobalTheory.AV.AbVar.exists_image_geometricallyIntegral) | (intros; apply GlobalTheory.AV.AbVar.exists_image_geometricallyIntegral  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermLineBundlePairPullbackDominant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

open GlobalTheory.TrueGeo.SmallSec

theorem pair_pull : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (Y : Scheme.{0})
    [IsIntegral Y] (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X →
    ∀ P : Pair p, ∃ (Q : Pair q) (e : X.functionField →+* Y.functionField), Q.L = P.L.pull π hπ ∧
      Q.A = P.A.pull π hπ ∧ ∀ (a b : ℤ), ∀ f ∈ P.H a b, e f ∈ Q.H a b ∧ ∀ (σ : k →+* ℂ) (y : CxPts q σ),
        Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map π hπ _ y) f := by
  intro k _ X _ p Y _ q π hπ hgen P
  subst hπ
  have hη : π (genericPoint Y) ⤳ genericPoint X := hgen ▸ specializes_rfl
  let Q : Pair (π ≫ p) :=
    ⟨P.L.pull π rfl, P.A.pull π rfl, _, _, MultPull.isRatSec_pull_map π hη P.hr,
      MultPull.isRatSec_pull_map π hη P.hr'⟩
  have hloc : ∀ (a b : ℤ) (f : X.functionField) (i : Q.L.B.ι) (j : Q.A.B.ι),
      Q.loc a b (fnMap π hη f) i j = fnMap π hη (P.loc a b f (i PUnit.unit) (j PUnit.unit)) := by
    intro a b f i j
    simp only [Pair.loc, map_mul, map_zpow₀]
    rfl
  have hmem : ∀ (a b : ℤ), ∀ f ∈ P.H a b, fnMap π hη f ∈ Q.H a b := by
    intro a b f hf x i j hi hj
    rw [hloc]
    exact FrameGlue.Pull.regAt_fnMap π hη
      (hf (π x) (i PUnit.unit) (j PUnit.unit) (Set.mem_iInter.1 hi PUnit.unit) (Set.mem_iInter.1 hj PUnit.unit))
  refine ⟨Q, fnMap π hη, rfl, rfl, fun a b f hf => ⟨hmem a b f hf, fun σ y => ?_⟩⟩
  let z := Points.PtsOver.map π (rfl : π ≫ p = π ≫ p) (spMap σ) y
  set i0 := pick (P.L.φ σ).isLB z
  set j0 := pick (P.A.φ σ).isLB z
  have hi0 : z ∈ ptsIn p σ (P.L.B.U i0) := mem_pick _ z
  have hj0 : z ∈ ptsIn p σ (P.A.B.U j0) := mem_pick _ z
  have hi : y ∈ ptsIn (π ≫ p) σ (Q.L.B.U fun _ => i0) :=
    mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 hi0)
  have hj : y ∈ ptsIn (π ≫ p) σ (Q.A.B.U fun _ => j0) :=
    mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 hj0)
  have hreg : RegAt (under z) (P.loc a b f i0 j0) :=
    hf (under z) i0 j0 (mem_ptsIn.1 hi0) (mem_ptsIn.1 hj0)
  have hval : ratVal (fnMap π hη (P.loc a b f i0 j0)) y = ratVal (P.loc a b f i0 j0) z := by
    show ratVal (fnMap π hη (P.loc a b f i0 j0)) y = ratVal (P.loc a b f i0 j0)
      (Points.PtsOver.map π (rfl : π ≫ p = π ≫ p) (spMap σ) y)
    rw [ratVal_eq_valAt y (FrameGlue.Pull.regAt_fnMap π hη hreg), valAt_fnMap π hη _ hreg,
      ratVal_eq_valAt _ hreg]
    rfl
  rw [GlobalTheory.VolBr.nu_eq k Y (π ≫ p) Q a b _ (hmem a b f hf) σ y _ _ hi hj,
    GlobalTheory.VolBr.nu_eq k X p P a b f hf σ z i0 j0 hi0 hj0]
  erw [hloc a b f (fun _ => i0) (fun _ => j0), hval]
  erw [(P.L.φ σ).pull_φ π rfl (fun _ => i0) y, (P.A.φ σ).pull_φ π rfl (fun _ => j0) y]

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeFiltrationToPDivOmegaLinearMap
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.PtExt.exists_hodge_to_omega : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (G : PDivGroup p R) (t : GlobalTheory.PDivGroup.TorsionTower G A),
    ∃ ψ : PrimitiveSubmodule A →ₗ[R] G.omega,
      ∀ c : PrimitiveSubmodule A, GlobalTheory.PtExt.IsCan t c.1 (G.rigOfOmega (ψ c)) := by
  intro p _ R _ N hN A _ hA G t
  obtain ⟨L, hL⟩ := GlobalTheory.PtExt.exists_canMap R A p G t hA
  have hinj := GlobalTheory.PDivGroup.rigOfOmega_injective_of_pow p R N hN G
  have hmem : ∀ c : PrimitiveSubmodule A, (L ∘ₗ (PrimitiveSubmodule A).subtype) c ∈ LinearMap.range G.rigOfOmega := by
    intro c
    have hc : c.1.1 ∈ F1 (A.hom ≫ 𝟙 _) := c.2
    rw [hodgeFiltration_eq_range] at hc
    obtain ⟨β, hβ⟩ := hc
    have hβp : Form.cl _ β ∈ primDR A := hβ ▸ c.1.2
    obtain ⟨w, -, hw⟩ := GlobalTheory.PtExt.isCan_form R A p G t β hβp
    have hcc : (⟨_, hβp⟩ : primDR A) = c.1 := Subtype.ext hβ
    rw [hcc] at hw
    exact ⟨w, ((hL _ _).1 hw).symm⟩
  refine ⟨(LinearEquiv.ofInjective G.rigOfOmega hinj).symm ∘ₗ
    (L ∘ₗ (PrimitiveSubmodule A).subtype).codRestrict (LinearMap.range G.rigOfOmega) hmem, fun c ↦ ?_⟩
  rw [hL]
  exact (LinearEquiv.ofInjective_symm_apply G.rigOfOmega (h := hinj)
    ((L ∘ₗ (PrimitiveSubmodule A).subtype).codRestrict (LinearMap.range G.rigOfOmega) hmem c)).symm
end

