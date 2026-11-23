module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionSecondScalarDeterminedOfNonzero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Modif.eq_comp_gp {R : Type} [CommRing R] [IsDomain R] (M : Modif R) {F : Type} [Field F]
    (ψ : FractionRing R →+* F) (x : Sp F ⟶ M.S) (hx : x ≫ M.π = spMap ψ ≫ jK R) : x = spMap ψ ≫ M.gp := by
  have := M.integral
  have hd := M.dominant
  let pt : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  obtain ⟨B, e₀, hoi, P, hP⟩ : ∃ (B : CommRingCat) (e₀ : Spec B ⟶ M.S), IsOpenImmersion e₀ ∧ ∃ P, e₀ P = x pt :=
    ⟨_, M.S.affineCover.f (M.S.affineCover.idx (x pt)), M.S.affineCover.map_prop _, M.S.affineCover.covers (x pt)⟩
  have hsub : Set.range M.gp ⊆ Set.range e₀ := by
    obtain ⟨a, ha⟩ := hd.denseRange.exists_mem_open e₀.isOpenEmbedding.isOpen_range ⟨e₀ P, P, rfl⟩
    rintro _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x a]
  have hsub' : Set.range x ⊆ Set.range e₀ := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y pt]
    exact ⟨P, hP⟩
  obtain ⟨g', hfac⟩ : ∃ g', g' ≫ e₀ = M.gp := ⟨_, IsOpenImmersion.lift_fac e₀ M.gp hsub⟩
  obtain ⟨x', hfx⟩ : ∃ x', x' ≫ e₀ = x := ⟨_, IsOpenImmersion.lift_fac e₀ x hsub'⟩
  obtain ⟨g, rfl⟩ := Spec.map_surjective g'
  obtain ⟨g₁, rfl⟩ := Spec.map_surjective x'
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (e₀ ≫ M.π)
  have hcomp : ρ ≫ g = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, ← Category.assoc, hfac, M.gp_π]
  have hcomp₁ : ρ ≫ g₁ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ CommRingCat.ofHom ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, ← Category.assoc, hfx, hx, Spec.map_comp]
  have hc : ∀ r, g.hom (ρ.hom r) = algebraMap R (FractionRing R) r := fun r => congrArg (fun f => f.hom r) hcomp
  have hc₁ : ∀ r, g₁.hom (ρ.hom r) = ψ (algebraMap R (FractionRing R) r) := fun r => congrArg (fun f => f.hom r) hcomp₁
  have hden : DenseRange (Spec.map g) := by
    rw [denseRange_iff_closure_range, e₀.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      ← Set.range_comp]
    have : (e₀ ∘ Spec.map g) = M.gp := by funext x; rw [← hfac]; rfl
    rw [this, hd.denseRange.closure_range, Set.preimage_univ]
  have hinj : Function.Injective g.hom := by
    have h2 := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g.hom).1 hden
    have hr := (affine_isReduced_iff _).1 (isReduced_of_isOpenImmersion e₀)
    rw [nilradical_eq_zero] at h2
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h2)
  have key : g₁ = g ≫ CommRingCat.ofHom ψ := by
    ext b
    show g₁.hom b = ψ (g.hom b)
    obtain ⟨a, s, hs, hxs⟩ := IsFractionRing.div_surjective (A := R) (g.hom b)
    have hs0 : algebraMap R (FractionRing R) s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have h0 : ρ.hom s * b = ρ.hom a := hinj (by rw [map_mul, hc, hc, ← hxs, mul_div_cancel₀ _ hs0])
    have h1 := congrArg g₁.hom h0
    rw [map_mul, hc₁, hc₁] at h1
    rw [← hxs, map_div₀, ← h1, mul_div_cancel_left₀ _ ((map_ne_zero ψ).2 hs0)]
  rw [← hfx, ← hfac, key, Spec.map_comp, Category.assoc]

theorem PullB.unique {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X} {b : D.SecB k (hD.xe x)}
    {b₁ b₂ : D'.SecB k x} (H₁ : PullB hD x b b₁) (H₂ : PullB hD x b b₂) : b₁ = b₂ := by
  refine DVR.SecOps.sec_ext fun q => fn_ext fun y hy => ?_
  choose p hp using fun κ => exists_chart D.P.isLB ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (D'.famφB x κ y))
  have e₁ := H₁ _ (𝟙 _) y p q hp (Set.mem_iInter.1 hy)
  have e₂ := H₂ _ (𝟙 _) y p q hp (Set.mem_iInter.1 hy)
  exact (Units.mul_right_inj _).1 (e₁.symm.trans e₂)

theorem PullB.eq_zero {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    (hφ : Function.Injective φ) {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {k : ℕ} {x : D'.X}
    {b : D.SecB k (hD.xe x)} {b' : D'.SecB k x} (H : PullB hD x b b') (h : ∀ q, b'.f q = 0) (p) : b.f p = 0 := by
  have : IsDominant (specOf φ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hφ]; exact bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (specOf φ)
  have : Smooth D.P.A.hom := D.P.isAb.smooth
  have : IsSchemeTheoreticallyDominant (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (pull_grp hD).1.flip
  have : QuasiCompact (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (pull_grp hD).1.flip inferInstance
  apply (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)).app_injective
  rw [map_zero]
  refine fn_ext fun y hy => ?_
  choose q hq using fun κ => exists_chart D'.P.isLB (D'.famφB x κ y)
  have e := H _ (𝟙 _) y p q (fun κ => by
    have a := Set.mem_iInter.1 hy κ
    exact (congrArg (fun m => m y ∈ D.P.L.U (p κ)) (ExpGTrans.famφB_pull hD x κ)).mpr a) hq
  have e' := e.trans ((congrArg _ ((congrArg (gs _ y _) (h q)).trans (DVR.hr_gs_zero _ _ _))).trans (mul_zero _))
  exact (gs_pull _ _ y _ hy _).trans (e'.trans (DVR.hr_gs_zero _ _ _).symm)

theorem expands_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) :
    U.Expands k DVR.SecOps.secZero 0 := by
  refine ⟨1, one_ne_zero, DVR.SecOps.secZero, fun _ => DVR.SecOps.secZero, fun j₁ j₂ _ => ?_, fun α j₁ j₂ _ => ?_,
    fun e => ⟨∅, fun α _ j => map_zero _, fun p j₁ jf jt _ _ => ?_⟩⟩
  · exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
  · exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
  · exact ((congrArg _ ((congrArg _ (map_zero _)).trans (map_zero _))).trans (mul_zero _)).trans (Finset.sum_empty).symm

theorem IntFam.f_eq_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {k : ℕ} (F : IntFam I D k)
    (h : F.F = 0) (x : D.X) (q) : (F.f x).f q = 0 := by
  have h₀ : GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) x) (DegPre.famε k) (F.F.s x)
      (D.famφB x) (DegPre.famε k) DVR.SecOps.secZero (DegPre.prB D (FractionRing R)).left 1 := by
    rw [h]
    intro j₁ j₂ _
    exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
  exact (IntegralExpansion.secIsMul_of_secScal D.P.isLB D.P.A.hom (a := 1) (IntegralExpansion.prB_app_injective D) h₀
    (by rw [Over.w (DegPre.prB D (FractionRing R))]; exact F.ext x) q).trans (mul_zero _)

theorem IntFam.eq_zero_of_two_scalars {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Sp (FractionRing W))} {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k : ℕ} (hk : 1 ≤ k)
    (F : IntFam I D.toPre k) {σ₁ σ₂ : H0 U.LG.L k} (e₁ : ∀ e, U.ExpandsAt e k σ₁ F.f) (e₂ : ∀ e, U.ExpandsAt e k σ₂ F.f)
    {b b' : W} (hb : b ≠ b') (H : ∀ y J, Good U.LG.L y J → ∃ u : ((pullback G.hom (jK W)).presheaf.stalk y)ˣ,
      gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b) * u.val * sval σ₁ (pullback.fst G.hom (jK W)) y J =
        gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b') * u.val * sval σ₂ (pullback.fst G.hom (jK W)) y J) :
    F.F = 0 := by
  have res : ∀ σ : H0 U.LG.L k, (∀ e, U.ExpandsAt e k σ F.f) → ∃ s : U.SecK k, U.Expands k s F.F ∧
      ∀ y J, Good U.LG.L y J → sval σ (pullback.fst G.hom (jK W)) y J = sval s (𝟙 _) y J := fun σ e => by
    obtain ⟨s, hs⟩ := UnifBaseChange.exists_secScal_one U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ))
      (pullback.fst G.hom (jK W)) (fun _ => pullback.fst G.hom (jK W)) (funext fun _ => (Category.comp_id _).symm) σ
    refine ⟨s, ⟨1, one_ne_zero, σ, F.f, ?_, F.ext, e⟩, fun y J hJ => ?_⟩
    · rw [UnifBaseChange.scal_one]; exact hs
    · have v := DVR.hr_secScal_sval hs (𝟙 _) y hJ
      rwa [Category.id_comp, gs_eq _ y ⊤ trivial, map_one, map_one, _root_.one_mul] at v
  obtain ⟨s₁, x₁, v₁⟩ := res σ₁ e₁
  obtain ⟨s₂, x₂, v₂⟩ := res σ₂ e₂
  obtain rfl : s₁ = s₂ := ((U.expand k hk).2 F.F).unique x₁ x₂
  have hz : s₁ = DVR.SecOps.secZero := by
    refine DVR.SecOps.sec_ext (sec_ext_val U.LG.isLB fun y J hJ => ?_)
    obtain ⟨u, e⟩ := H y J hJ
    rw [v₁ y J hJ, v₂ y J hJ, ← sub_eq_zero, ← sub_mul, ← sub_mul] at e
    have hu : IsUnit (gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom (b - b'))) := by
      rw [GenericCross.gs_scal, pullback.condition]
      exact GenericCross.isUnit_cst _ y (sub_ne_zero.2 hb)
    have hs : gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom (b - b')) =
        gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b) - gs (pullback.fst G.hom (jK W)) y ⊤ (scal G.hom b') := by
      simp only [gs_eq _ y ⊤ trivial, scal, map_sub]
    rw [hs] at hu
    exact ((hu.mul u.isUnit).mul_right_eq_zero.1 e).trans (DVR.hr_gs_zero _ _ _).symm
  rw [hz] at x₁
  exact ((U.expand k hk).1 _).unique x₁ (expands_zero U.toUnifPre k)

theorem exists_fractionRing_square {R W : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] (φ : R →+* W) (h : Function.Injective φ) :
    ∃ ψ : FractionRing R →+* FractionRing W, jK W ≫ spMap φ = spMap ψ ≫ jK R := by
  have hi : Function.Injective ((algebraMap W (FractionRing W)).comp φ) := (IsFractionRing.injective W _).comp h
  have h₀ : (algebraMap W (FractionRing W)).comp φ = (IsFractionRing.lift hi).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun r => by rw [RingHom.comp_apply (IsFractionRing.lift hi), IsFractionRing.lift_algebraMap]
  refine ⟨IsFractionRing.lift hi, ?_⟩
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← h₀]

theorem Trait.exists_generic_map {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) :
    ∃ p' : pullback T.G.hom (jK W) ⟶ C.A.A.left, pullback.fst T.G.hom (jK W) ≫ T.β = p' ≫ C.α := by
  obtain ⟨ψ, h₀⟩ := exists_fractionRing_square T.φ T.inj
  have hψ : jK W ≫ T.ξ = spMap ψ ≫ C.gp := C.toModif.eq_comp_gp ψ _ (by rw [Category.assoc, T.ξ_π, h₀])
  have w₁ : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
  have w₂ : pullback.fst T.G.hom (jK W) ≫ T.G.hom = pullback.snd T.G.hom (jK W) ≫ jK W := pullback.condition
  have w₃ : (pullback.fst T.G.hom (jK W) ≫ T.β) ≫ C.G.hom = (pullback.snd T.G.hom (jK W) ≫ spMap ψ) ≫ C.gp := by
    rw [Category.assoc, w₁, reassoc_of% w₂, hψ, Category.assoc]
  have hp : IsPullback C.α C.A.A.hom C.G.hom C.gp := C.α_cart.1
  exact ⟨hp.lift _ _ w₃, (hp.lift_fst _ _ w₃).symm⟩

theorem Trait.exp_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k), (∃ α j, (F.f α).f j ≠ 0) → ∀ a b b' : W, a ≠ 0 → T.Exp a b s F → T.Exp a b' s F → b = b' := by
  intro R _ _ _ hR D C W _ _ _ T k hk s F hF a b b' _ h₁ h₂
  obtain ⟨α, j, hne⟩ := hF
  obtain ⟨σ₁, ⟨σ₁', f₁, c₁, p₁, e₁⟩, g₁⟩ := h₁
  obtain ⟨σ₂, ⟨σ₂', f₂, c₂, p₂, e₂⟩, g₂⟩ := h₂
  by_contra hb
  apply hne
  obtain ⟨F', hF'⟩ := exists_intFam_pull R hR D W T.φ T.D' T.hD T.inj T.loc k F
  rw [show f₁ = F'.f from funext fun x => (p₁ x).unique (hF' x)] at e₁
  rw [show f₂ = F'.f from funext fun x => (p₂ x).unique (hF' x)] at e₂
  obtain ⟨p', hp'⟩ := T.exists_generic_map
  have h₀ : F'.F = 0 := F'.eq_zero_of_two_scalars T.U hk e₁ e₂ hb fun y J' hJ' => by
    choose J hJ using fun χ : pullback T.G.hom (jK W) ⟶ C.G.left => exists_chart C.P.L.isLB (χ y)
    exact ⟨_, (c₁ _ _ y J J' hJ hJ').symm.trans ((g₁ _ _ p' hp' y J hJ).trans
      ((g₂ _ _ p' hp' y J hJ).symm.trans (c₂ _ _ y J J' hJ hJ')))⟩
  obtain ⟨x, rfl⟩ := T.hD.xe.surjective α
  exact (hF' x).eq_zero T.inj (F'.f_eq_zero h₀ x) j

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorizationThroughFiniteModification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem finite_modif_eq_gp : ∀ (R : Type) [CommRing R] [IsDomain R] (M M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h →
    M'.gp ≫ h = M.gp → ∀ (Z : Scheme.{0}) (a : Z ⟶ M'.S) (c : Z ⟶ Sp (FractionRing R)), a ≫ h = c ≫ M.gp →
    a = c ≫ M'.gp := by
  intro R _ _ M M' h hh e Z a c hac
  haveI := M'.integral
  have cA : ∀ {X Y W : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ W) (x : Γ(W, ⊤)),
      (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := fun f g x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  have hsub : Subsingleton (Sp (FractionRing R)) := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  let pt : Sp (FractionRing R) := (default : PrimeSpectrum (FractionRing R))
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.S) (U := ⊤) (x := M.gp pt) trivial
  have hgU : ∀ y : Sp (FractionRing R), M.gp y ∈ U := fun y => by rwa [Subsingleton.elim y pt]
  have hV : IsAffineOpen (h ⁻¹ᵁ U) := hU.preimage h
  have ha : Set.range a ⊆ Set.range (h ⁻¹ᵁ U).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show h (a z) ∈ U
    rw [← Scheme.Hom.comp_apply, hac, Scheme.Hom.comp_apply]; exact hgU _
  have hg : Set.range M'.gp ⊆ Set.range (h ⁻¹ᵁ U).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show h (M'.gp z) ∈ U
    rw [← Scheme.Hom.comp_apply, e]; exact hgU _
  obtain ⟨a₀, fa⟩ : ∃ a₀, a₀ ≫ (h ⁻¹ᵁ U).ι = a := ⟨_, IsOpenImmersion.lift_fac _ _ ha⟩
  obtain ⟨g₀, fg⟩ : ∃ g₀, g₀ ≫ (h ⁻¹ᵁ U).ι = M'.gp := ⟨_, IsOpenImmersion.lift_fac _ _ hg⟩
  suffices key : a₀ = c ≫ g₀ by rw [← fa, key, Category.assoc, fg]
  haveI : IsAffine (h ⁻¹ᵁ U) := hV
  have hq1 : a₀ ≫ ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π) = c ≫ jK R := by
    rw [reassoc_of% fa, reassoc_of% hac, M.gp_π]
  have hq2 : g₀ ≫ ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π) = jK R := by
    rw [reassoc_of% fg, reassoc_of% e, M.gp_π]
  have hinj : Function.Injective g₀.appTop.hom := by
    haveI : IsDominant (g₀ ≫ (h ⁻¹ᵁ U).ι) := by rw [fg]; exact M'.dominant
    haveI : IsDominant g₀ := IsDominant.of_comp_of_isOpenImmersion g₀ (h ⁻¹ᵁ U).ι
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx0
    apply eq_zero_of_basicOpen_eq_bot
    by_contra hne
    obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    obtain ⟨z, hz⟩ := g₀.denseRange.exists_mem_open (Scheme.basicOpen _ x).isOpen ⟨y, hy⟩
    have hz' : z ∈ g₀ ⁻¹ᵁ Scheme.basicOpen _ x := hz
    have hx0' : (ConcreteCategory.hom (g₀.app ⊤)) x = 0 := hx0
    rw [Scheme.preimage_basicOpen, hx0', Scheme.basicOpen_zero] at hz'
    exact hz'
  have hfrac : ∀ x : Γ(Sp (FractionRing R), ⊤), ∃ r t : Γ(Sp R, ⊤),
      IsUnit ((jK R).appTop.hom t) ∧ x * (jK R).appTop.hom t = (jK R).appTop.hom r := by
    intro x
    have nat : ∀ s, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((jK R).appTop.hom s) =
        algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s) := fun s =>
      congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom :=
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.injective
    obtain ⟨r', t', ht', hx'⟩ := IsFractionRing.div_surjective (A := R)
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom x)
    have ht0 : algebraMap R (FractionRing R) t' ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht'
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r', (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t', ?_, ?_⟩
    · have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
          ((jK R).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t'))) := by
        rw [nat]; simpa using ht0
      have := hu.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
      simpa using this
    · apply inj
      rw [map_mul, nat, nat]
      have hi : ∀ s, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom s) = s :=
        fun s => congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id
      rw [hi, hi, ← hx']
      exact div_mul_cancel₀ _ ht0
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop]
  ext b
  obtain ⟨r, t, ht, hx⟩ := hfrac (g₀.appTop.hom b)
  have e1 : b * ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π).appTop.hom t = ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π).appTop.hom r := by
    apply hinj
    rw [map_mul, ← cA, ← cA, hq2, hx]
  have e2 := congrArg a₀.appTop.hom e1
  rw [map_mul, ← cA, ← cA, hq1, cA, cA, ← hx, map_mul] at e2
  exact (IsUnit.mul_left_inj (ht.map c.appTop.hom)).1 e2

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGeneratedSubringLocalisedBasicOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem closure_pow_lift {L L' : Type*} [CommRing L] [CommRing L'] (ρ : L →+* L') (C : Subring L) (u : L)
    (hu : u ∈ C) (G : Set L') (hG : ∀ g ∈ G, ∃ k : ℕ, ∃ w ∈ C, ρ w = ρ u ^ k * g) :
    ∀ z ∈ Subring.closure G, ∃ k : ℕ, ∃ w ∈ C, ρ w = ρ u ^ k * z := by
  intro z hz
  induction hz using Subring.closure_induction with
  | mem g hg => exact hG g hg
  | zero => exact ⟨0, 0, C.zero_mem, by simp⟩
  | one => exact ⟨0, 1, C.one_mem, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨k, w, hw, e⟩ := ha
    obtain ⟨l, v, hv, e'⟩ := hb
    refine ⟨k + l, u ^ l * w + u ^ k * v,
      C.add_mem (C.mul_mem (C.pow_mem hu _) hw) (C.mul_mem (C.pow_mem hu _) hv), ?_⟩
    rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, e, e']
    ring
  | neg a _ ha =>
    obtain ⟨k, w, hw, e⟩ := ha
    exact ⟨k, -w, C.neg_mem hw, by rw [map_neg, e]; ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨k, w, hw, e⟩ := ha
    obtain ⟨l, v, hv, e'⟩ := hb
    refine ⟨k + l, w * v, C.mul_mem hw hv, ?_⟩
    rw [map_mul, e, e']
    ring

theorem exists_pow_mul_res {S : Scheme.{0}} {U : S.Opens} (hc : IsCompact (U : Set S))
    (hq : IsQuasiSeparated (U : Set S)) (g : Γ(S, U)) (U' : S.Opens) (hle : U' ≤ U) (hU' : U' = S.basicOpen g)
    (a : Γ(S, U')) : ∃ (k : ℕ) (b : Γ(S, U)), (S.presheaf.map (homOfLE hle).op).hom b =
      (S.presheaf.map (homOfLE hle).op).hom g ^ k * a := by
  subst hU'
  letI := (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom.toAlgebra
  have := isLocalization_basicOpen_of_qcqs hc hq g
  obtain ⟨⟨y, ⟨_, k, rfl⟩⟩, hy⟩ := IsLocalization.surj (Submonoid.powers g) a
  refine ⟨k, y, ?_⟩
  rw [← map_pow, mul_comm]
  simpa [RingHom.algebraMap_toAlgebra] using hy.symm

theorem presheaf_map_bijective_of_eq {X : Scheme.{0}} {A B : X.Opens} (h : B ≤ A) (e : A = B) :
    Function.Bijective (X.presheaf.map (homOfLE h).op).hom := by
  subst e
  have : homOfLE h = 𝟙 A := Subsingleton.elim _ _
  simpa [this] using Function.bijective_id

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem finFam_basicOpen_loc : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (W : S.Opens), IsAffineOpen W → ∀ (f : Γ(S, W))
    (x : Γ(Sp K, gp ⁻¹ᵁ S.basicOpen f)), x ∈ finFam gp V t (S.basicOpen f) →
    ∃ (k : ℕ) (y : Γ(Sp K, gp ⁻¹ᵁ W)), y ∈ finFam gp V t W ∧
      resK gp (S.basicOpen_le f) y = resK gp (S.basicOpen_le f) ((gp.app W).hom f) ^ k * x := by
  intro S K _ gp _ r V t W hW f x hx
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let p : Sp K := (IsLocalRing.closedPoint K : PrimeSpectrum K)
  have pre : ∀ U U' : S.Opens, (gp.base p ∈ U ↔ gp.base p ∈ U') → gp ⁻¹ᵁ U = gp ⁻¹ᵁ U' := by
    intro U U' h
    ext q
    rw [Subsingleton.elim q p]
    exact h
  have bij : ∀ {U U' : S.Opens} (h : U' ≤ U), (gp.base p ∈ U ↔ gp.base p ∈ U') →
      Function.Bijective (resK gp h) := fun h e => presheaf_map_bijective_of_eq _ (pre _ _ e)
  by_cases hs : gp.base p ∈ S.basicOpen f
  swap
  · have e : gp ⁻¹ᵁ S.basicOpen f = ⊥ := by
      ext q
      rw [Subsingleton.elim q p]
      exact ⟨fun h => (hs h).elim, fun h => by simp at h⟩
    haveI : Subsingleton Γ(Sp K, gp ⁻¹ᵁ S.basicOpen f) := by rw [e]; infer_instance
    exact ⟨0, 0, Subring.zero_mem _, Subsingleton.elim _ _⟩
  have hsW : gp.base p ∈ W := S.basicOpen_le f hs
  haveI : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hNW : TopologicalSpace.NoetherianSpace (W : Set S) := noetherianSpace_of_isAffineOpen W hW
  have hcpt : ∀ T ⊆ (W : Set S), IsCompact T := (TopologicalSpace.noetherianSpace_set_iff _).mp hNW
  have hle : ∀ i, S.basicOpen f ⊓ V i ≤ W ⊓ V i := fun i => inf_le_inf_right _ (S.basicOpen_le f)
  rw [mem_finFam] at hx
  have step : ∀ i, ∃ k : ℕ, ∃ w ∈ Subring.closure (Set.range (gp.app (W ⊓ V i)).hom ∪
      resK gp (inf_le_right : W ⊓ V i ≤ V i) '' (t i : Set _)),
      resK gp (hle i) w = resK gp (hle i) (resK gp (inf_le_left : W ⊓ V i ≤ W) ((gp.app W).hom f)) ^ k *
        resK gp (inf_le_left : S.basicOpen f ⊓ V i ≤ S.basicOpen f) x := by
    intro i
    refine closure_pow_lift _ _ _ ?_ _ ?_ _ (hx i)
    · rw [resK_app]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    rintro _ (⟨a, rfl⟩ | ⟨c, hc, rfl⟩)
    · have hU' : S.basicOpen f ⊓ V i =
          S.basicOpen ((S.presheaf.map (homOfLE (inf_le_left : W ⊓ V i ≤ W)).op).hom f) := by
        rw [Scheme.basicOpen_res]
        exact le_antisymm (le_inf (le_inf (inf_le_left.trans (S.basicOpen_le f)) inf_le_right) inf_le_left)
          (le_inf inf_le_right (inf_le_left.trans inf_le_right))
      have hWi : (↑(W ⊓ V i) : Set S) ⊆ W := fun z hz => hz.1
      obtain ⟨k, b, e⟩ := exists_pow_mul_res (hcpt _ hWi)
        (fun A B hA _ _ hB _ _ => hcpt _ ((Set.inter_subset_left.trans hA).trans hWi)) _ _ (hle i) hU' a
      refine ⟨k, (gp.app (W ⊓ V i)).hom b, Subring.subset_closure (Or.inl ⟨_, rfl⟩), ?_⟩
      rw [resK_app, resK_app, resK_app, e, map_mul, map_pow, ← CommRingCat.comp_apply]
    · refine ⟨0, resK gp (inf_le_right : W ⊓ V i ≤ V i) c, Subring.subset_closure (Or.inr ⟨c, hc, rfl⟩), ?_⟩
      rw [pow_zero, _root_.one_mul, resK_resK]
  choose k w hw e using step
  let N := Finset.univ.sup k
  obtain ⟨y, hy⟩ := (bij (S.basicOpen_le f) ⟨fun _ => hs, fun _ => hsW⟩).2
    (resK gp (S.basicOpen_le f) ((gp.app W).hom f) ^ N * x)
  refine ⟨N, y, ?_, hy⟩
  rw [mem_finFam]
  intro i
  have hki : k i ≤ N := Finset.le_sup (Finset.mem_univ i)
  have hmem : resK gp (inf_le_left : W ⊓ V i ≤ W) ((gp.app W).hom f) ^ (N - k i) * w i ∈
      Subring.closure (Set.range (gp.app (W ⊓ V i)).hom ∪
        resK gp (inf_le_right : W ⊓ V i ≤ V i) '' (t i : Set _)) := by
    refine Subring.mul_mem _ (Subring.pow_mem _ ?_ _) (hw i)
    rw [resK_app]
    exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
  have inj := (bij (hle i) (by simp [hs, hsW])).1
  convert hmem using 1
  apply inj
  rw [map_mul, map_pow, e i, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hki, resK_resK, resK_resK,
    ← resK_resK gp (S.basicOpen_le f) (inf_le_left : S.basicOpen f ⊓ V i ≤ S.basicOpen f), hy, map_mul, map_pow,
    resK_resK]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIntegerRingActionsPrincipallyPolarised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.FinAct

theorem finite_oActs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)), letI := H.starRing;
    Set.Finite {act : 𝓞 E → (P.A ⟶ P.A) | ∃ ρ : P.OAct (𝓞 E), ∀ a, ρ.act a = act a} := by
  intro E _ _ _ H K _ _ _ P
  letI := H.starRing
  have h₂ := GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion.2
  choose cn hcn using GlobalTheory.exists_starNormLE_of_isCMField E (fun a => H.bar_eq a)
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
  set g := P.g
  set M := 4 ^ g * g.factorial * (2 * s.sup cn) + 1 with hM
  have hM1 : 1 ≤ M := Nat.le_add_left _ _
  have key : ∀ c, c ≤ s.sup cn → 4 ^ g * g.factorial * (2 * c) < M ^ 2 := fun c hc =>
    calc 4 ^ g * g.factorial * (2 * c) ≤ 4 ^ g * g.factorial * (2 * s.sup cn) := by gcongr
      _ < M := Nat.lt_succ_self _
      _ ≤ M ^ 2 := Nat.le_self_pow two_ne_zero _
  have hK : (M : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let T := {x : baseOver (Sp K) ⟶ P.A // x ^ M = 1}
  haveI : Finite T := GlobalTheory.AbTorsionFinite.finite_torsion K P.A P.isAb M hM1
  classical
  let F : (𝓞 E → (P.A ⟶ P.A)) → (s → T → Option T) := fun act a x =>
    if h : (x.1 ≫ act a) ^ M = 1 then some ⟨_, h⟩ else none
  refine Set.Finite.of_finite_image (f := F) (Set.toFinite _) ?_
  rintro act₁ ⟨ρ₁, h₁⟩ act₂ ⟨ρ₂, h₂'⟩ hF
  have tor : ∀ (ρ : P.OAct (𝓞 E)) (a : 𝓞 E) (x : T), (x.1 ≫ ρ.act a) ^ M = 1 := fun ρ a x => by
    have := ρ.hom a
    have e := map_pow (IsMonHom.monoidHom (ρ.act a) (baseOver (Sp K))) x.1 M
    rw [x.2, map_one] at e
    exact e.symm
  have onS : ∀ a ∈ s, ρ₁.act a = ρ₂.act a := fun a ha => by
    have := h₂ g (cn a) M (key _ (Finset.le_sup ha)) K hK P P rfl rfl (Iso.refl _)
      (ThetaPtDet.isPolIso_refl P) (𝓞 E) ρ₁ ρ₂ a (hcn a) fun y hy => by
        have e := congrFun (congrFun hF ⟨a, ha⟩) ⟨y, hy⟩
        simp only [F, h₁, h₂'] at e
        rw [dite_eq_left (h₁ a ▸ tor ρ₁ a ⟨y, hy⟩), dite_eq_left (h₂' a ▸ tor ρ₂ a ⟨y, hy⟩)] at e
        have e' := congrArg Subtype.val (Option.some_injective _ e)
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, h₁, h₂']
        exact e'
    simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using this
  have add₁ : ∀ a b, ρ₁.act (a + b) = ρ₁.act a * ρ₁.act b := ρ₁.map_add
  have add₂ : ∀ a b, ρ₂.act (a + b) = ρ₂.act a * ρ₂.act b := ρ₂.map_add
  let f₁ : 𝓞 E →+ Additive (P.A ⟶ P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (ρ₁.act a))
    fun a b => by rw [add₁]; rfl
  let f₂ : 𝓞 E →+ Additive (P.A ⟶ P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (ρ₂.act a))
    fun a b => by rw [add₂]; rfl
  have hf : f₁ = f₂ := AddMonoidHom.eq_of_eqOn_dense (s := (s : Set (𝓞 E)))
    (by rw [← Submodule.span_int_eq_addSubgroupClosure, hs]; rfl) fun a ha =>
      congrArg Additive.ofMul (onS a ha)
  funext a
  rw [← h₁, ← h₂']
  exact Additive.ofMul.injective (DFunLike.congr_fun hf a)

end GlobalTheory.UMin.FinAct
end
end

