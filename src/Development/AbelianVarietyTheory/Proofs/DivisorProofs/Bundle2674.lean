module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIsIffPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2503
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2610
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsOneTraitWeilPairingBijection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LabTorsTrait

open GlobalTheory.ArcPull GlobalTheory.Mum.Recog

theorem labTors_of_oneTrait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A),
    OneTrait D.toPre A lab → ∀ k : ℕ, 1 ≤ k → LabTors D.toPre A k (lab k) := by
  intro R _ _ _ hR D A lab hT k hk
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em, hW, iφ, _, hG, ha, c, H⟩ := hT
  have := hR.2
  have : CharZero W := (RingHom.charZero_iff iφ).1 inferInstance
  have := hW.1
  have := hW.2.2
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hB' := D'.tau_bimult
  have c' : Compat φ (Kb W) := c
  obtain ⟨f', hf'⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws W (maximalIdeal W) bW D' A' G' hG U' (Kb W) k hk
  obtain ⟨ε, hε, iε, oε, wε⟩ := exists_ptHom ha c' em
  have e : ∀ p, f' (tr hD c' em hB' p) = ε (lab k p) := fun p => by
    obtain ⟨p₁, h₁, h₂, h₃⟩ := (lies_iff hD c' em hB' p (tr hD c' em hB' p)).2 rfl
    exact ((hf'.1 _ _).1 (H k hk p p₁ _ _ h₁ h₂ h₃ ((hε _ _).1 rfl))).symm
  have pw : ∀ x : TFK (R := R) (Kb R) ⟶ A.A, ε x ^ k = 1 ↔ x ^ k = 1 := fun x => by
    rw [← map_pow, ← map_one ε, iε.eq_iff]
  have hp : ∀ p, lab k p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U'.ext
    rw [← pw, ← e]
    exact (((hf'.1 _ _).2 rfl) w hw).1
  refine ⟨fun y hy => ?_, hp, fun p q => ?_, fun p q r h => ?_, fun p q z => ?_⟩
  · obtain ⟨p', hp'⟩ := hf'.2.1 (ε y) ((pw y).2 hy)
    obtain ⟨p, rfl⟩ := (tr_bij hD c' em hB' hk).2 p'
    exact ⟨p, iε (by rw [← e, hp'])⟩
  · rw [← iε.eq_iff, ← e, ← e, hf'.2.2.1, tr_equiv]
  · apply iε
    rw [map_mul, ← e, ← e, ← e]
    exact hf'.2.2.2.1 _ _ _ ((tr_add hD c' em hB' p q r).2 h)
  · rw [← tr_weil hD c' em hB' hk p q z, wε k _ _ (hp p) (hp q) z, ← e, ← e]
    exact hf'.2.2.2.2 _ _ (Units.map em.toRingHom.toMonoidHom z)

end GlobalTheory.Mum.LabTorsTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionProductOverThickeningOfSumData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

noncomputable section

namespace GlobalTheory.ProdTorusExt

section Torus

variable {S : Scheme.{0}} {X X' X'' : Type} [AddCommGroup X] [AddCommGroup X'] [AddCommGroup X'']

theorem torusMap_comp' (a : X →+ X') (b : X'' →+ X) :
    GlobalTheory.SplitTorusPow.torusMap S a ≫ GlobalTheory.SplitTorusPow.torusMap S b = GlobalTheory.SplitTorusPow.torusMap S (a.comp b) := by
  apply (GlobalTheory.splitTorusPointsEquiv S X'' _).injective
  conv_rhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S (a.comp b))]
  conv_lhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S a)]
  rw [Category.assoc, ← Category.assoc (𝟙 _), GlobalTheory.SplitTorusPow.points_comp_torusMap,
    GlobalTheory.SplitTorusPow.points_comp_torusMap, GlobalTheory.SplitTorusPow.points_comp_torusMap]
  rfl

theorem torusMap_id' : GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.id X) = 𝟙 _ := by
  apply (GlobalTheory.splitTorusPointsEquiv S X _).injective
  conv_lhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.id X))]
  rw [GlobalTheory.SplitTorusPow.points_comp_torusMap]
  rfl

theorem isIso_lift_torusMap {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂] (E : X ≃+ X₁ × X₂) :
    IsIso (lift (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inl X₁ X₂)))
      (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inr X₁ X₂)))) := by
  haveI := GlobalTheory.SemiProd.torus_prod_iso S X₁ X₂
  have e : lift (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inl X₁ X₂)))
      (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inr X₁ X₂))) =
      GlobalTheory.SplitTorusPow.torusMap S E.symm.toAddMonoidHom ≫
        lift (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
          (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂)) := by
    rw [comp_lift, torusMap_comp', torusMap_comp']
  haveI : IsIso (GlobalTheory.SplitTorusPow.torusMap S E.symm.toAddMonoidHom) :=
    ⟨GlobalTheory.SplitTorusPow.torusMap S E.toAddMonoidHom, by
      rw [torusMap_comp', show E.symm.toAddMonoidHom.comp E.toAddMonoidHom = AddMonoidHom.id X from by ext; simp,
        torusMap_id'], by
      rw [torusMap_comp', show E.toAddMonoidHom.comp E.symm.toAddMonoidHom = AddMonoidHom.id (X₁ × X₂) from by
        ext <;> simp, torusMap_id']⟩
  rw [e]
  infer_instance

end Torus

end GlobalTheory.ProdTorusExt

namespace GlobalTheory.ProdTorusExt

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∃ (q : thickObj R I e (G₁ ⊗ G₂) ⟶ thickObj R I e D.P.A) (i : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ thickObj R I e (G₁ ⊗ G₂)), IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsMonHom i ∧ IsPullback i (toUnit _) q (η[thickObj R I e D.P.A]) ∧ q ≫ (Over.pullback (thick R I e)).map p₁ = ((Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ g₁.q ∧ q ≫ (Over.pullback (thick R I e)).map p₂ = ((Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ g₂.q ∧ (∀ h : D₁.X → D.X, (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) → ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.X, TorusHomOf h τ ∧ i ≫ ((Over.pullback (thick R I e)).map (fst G₁ G₂)) = τ ≫ g₁.i) ∧ (∀ h : D₂.X → D.X, (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) → ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.X, TorusHomOf h τ ∧ i ≫ ((Over.pullback (thick R I e)).map (snd G₁ G₂)) = τ ≫ g₂.i) := by
  intro R _ _ I e D D₁ D₂ p₁ p₂ q₁ q₂ G₁ G₂ _ _ _ _ g₁ g₂ hD
  let F := Over.pullback (thick R I e)
  let S₀ := Sp (R ⧸ I ^ (e + 1))
  haveI := hD.hom₁
  haveI := hD.hom₂
  haveI := g₁.q_hom
  haveI := g₂.q_hom
  haveI := g₁.i_hom
  haveI := g₂.i_hom
  let E : D.X ≃+ D₁.X × D₂.X := AddEquiv.ofBijective (q₁.prod q₂) hD.xsum
  let j₁ : D₁.X →+ D.X := E.symm.toAddMonoidHom.comp (AddMonoidHom.inl D₁.X D₂.X)
  let j₂ : D₂.X →+ D.X := E.symm.toAddMonoidHom.comp (AddMonoidHom.inr D₁.X D₂.X)
  let τ₁ := GlobalTheory.SplitTorusPow.torusMap S₀ j₁
  let τ₂ := GlobalTheory.SplitTorusPow.torusMap S₀ j₂
  have hτmon {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (φ : X →+ X') :
      IsMonHom (GlobalTheory.SplitTorusPow.torusMap S₀ φ) := by
    refine ⟨?_, ?_⟩
    · have h : (1 : 𝟙_ (Over S₀) ⟶ splitTorus S₀ X') ≫
          GlobalTheory.SplitTorusPow.torusMap S₀ φ = 1 := by
        apply (GlobalTheory.splitTorusPointsEquiv S₀ X _).injective
        rw [GlobalTheory.SplitTorusPow.points_comp_torusMap, map_one, map_one, MonoidHom.one_comp]
      simpa [Hom.one_def] using h
    · have h {Z : Over S₀} (a b : Z ⟶ splitTorus S₀ X') :
          (a * b) ≫ GlobalTheory.SplitTorusPow.torusMap S₀ φ =
            (a ≫ GlobalTheory.SplitTorusPow.torusMap S₀ φ) *
              (b ≫ GlobalTheory.SplitTorusPow.torusMap S₀ φ) := by
        apply (GlobalTheory.splitTorusPointsEquiv S₀ X Z).injective
        rw [map_mul, GlobalTheory.SplitTorusPow.points_comp_torusMap,
          GlobalTheory.SplitTorusPow.points_comp_torusMap,
          GlobalTheory.SplitTorusPow.points_comp_torusMap, map_mul, MonoidHom.mul_comp]
      simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp] using
        h (fst (splitTorus S₀ X') (splitTorus S₀ X')) (snd _ _)
  haveI : IsMonHom τ₁ := hτmon j₁
  haveI : IsMonHom τ₂ := hτmon j₂
  haveI hτ : IsIso (lift τ₁ τ₂) := isIso_lift_torusMap E

  haveI hG : IsIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) :=
    isIso_prodComparison_of_preservesLimit_pair F G₁ G₂
  haveI := hD.lim
  have eB : lift (F.map p₁) (F.map p₂) = F.map (lift p₁ p₂) ≫ Functor.OplaxMonoidal.δ F D₁.P.A D₂.P.A :=
    (Functor.OplaxMonoidal.lift_δ F p₁ p₂).symm
  haveI hB : IsIso (lift (F.map p₁) (F.map p₂)) := by rw [eB]; infer_instance
  haveI : IsMonHom (inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))) :=
    inferInstanceAs (IsMonHom (asIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))).inv)
  haveI : IsMonHom (inv (lift (F.map p₁) (F.map p₂))) :=
    inferInstanceAs (IsMonHom (asIso (lift (F.map p₁) (F.map p₂))).inv)
  let q := lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)) ≫ (g₁.q ⊗ₘ g₂.q) ≫ inv (lift (F.map p₁) (F.map p₂))
  let i := lift τ₁ τ₂ ≫ (g₁.i ⊗ₘ g₂.i) ≫ inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))
  have hP : ∀ (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange],
      P g₁.q.left → P g₂.q.left → P q.left := by
    intro P _ _ h₁ h₂
    haveI : IsIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))))
    haveI : IsIso (inv (lift (F.map p₁) (F.map p₂))).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (inv (lift (F.map p₁) (F.map p₂)))))
    rw [Over.comp_left, Over.comp_left]
    exact P.comp_mem _ _ (P.of_isIso _)
      (P.comp_mem _ _ (GlobalTheory.SemiProd.tensorHom_prop _ P _ _ _ _ _ _ h₁ h₂) (P.of_isIso _))
  have hq₁ : q ≫ F.map p₁ = F.map (fst G₁ G₂) ≫ g₁.q := by
    have : inv (lift (F.map p₁) (F.map p₂)) ≫ F.map p₁ = fst _ _ := by
      rw [IsIso.inv_comp_eq, lift_fst]
    rw [Category.assoc, Category.assoc, this, tensorHom_fst, lift_fst_assoc]
  have hq₂ : q ≫ F.map p₂ = F.map (snd G₁ G₂) ≫ g₂.q := by
    have : inv (lift (F.map p₁) (F.map p₂)) ≫ F.map p₂ = snd _ _ := by
      rw [IsIso.inv_comp_eq, lift_snd]
    rw [Category.assoc, Category.assoc, this, tensorHom_snd, lift_snd_assoc]
  have hi₁ : i ≫ F.map (fst G₁ G₂) = τ₁ ≫ g₁.i := by
    have : inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) ≫ F.map (fst G₁ G₂) = fst _ _ := by
      rw [IsIso.inv_comp_eq, lift_fst]
    rw [Category.assoc, Category.assoc, this, tensorHom_fst, lift_fst_assoc]
  have hi₂ : i ≫ F.map (snd G₁ G₂) = τ₂ ≫ g₂.i := by
    have : inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) ≫ F.map (snd G₁ G₂) = snd _ _ := by
      rw [IsIso.inv_comp_eq, lift_snd]
    rw [Category.assoc, Category.assoc, this, tensorHom_snd, lift_snd_assoc]

  have key := GlobalTheory.SemiProd.kernel_tensor _ _ _ _ _ _ _ g₁.i g₂.i g₁.q g₂.q g₁.isKernel g₂.isKernel
  have hK : IsPullback i (toUnit _) q (η[thickObj R I e D.P.A]) := by
    refine IsPullback.of_iso key (asIso (lift τ₁ τ₂)).symm
      (asIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))).symm (Iso.refl _)
      (asIso (lift (F.map p₁) (F.map p₂))).symm ?_ ?_ ?_ ?_
    · simp only [i, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
    · exact toUnit_unique _ _
    · simp only [q, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
    · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv]
      rw [IsIso.comp_inv_eq, IsMonHom.one_hom]

  have hE₁ : ∀ h : D₁.X → D.X, (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) → h = j₁ := by
    intro h h₁ h₂
    funext y
    apply E.injective
    change (q₁.prod q₂) (h y) = E (E.symm (y, 0))
    rw [AddEquiv.apply_symm_apply]
    exact Prod.ext (h₁ y) (h₂ y)
  have hE₂ : ∀ h : D₂.X → D.X, (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) → h = j₂ := by
    intro h h₁ h₂
    funext y
    apply E.injective
    change (q₁.prod q₂) (h y) = E (E.symm (0, y))
    rw [AddEquiv.apply_symm_apply]
    exact Prod.ext (h₁ y) (h₂ y)
  refine ⟨q, i, inferInstance, hP @Flat g₁.q_flat g₂.q_flat, hP @Surjective g₁.q_surj g₂.q_surj,
    hP @IsAffineHom g₁.q_affine g₂.q_affine, inferInstance, hK, hq₁, hq₂, fun h h₁ h₂ => ?_, fun h h₁ h₂ => ?_⟩
  · refine ⟨τ₁, ?_, hi₁⟩
    rw [hE₁ h h₁ h₂]
    exact GlobalTheory.MumProd.torusHomOf_torusMap j₁
  · refine ⟨τ₂, ?_, hi₂⟩
    rw [hE₂ h h₁ h₂]
    exact GlobalTheory.MumProd.torusHomOf_torusMap j₂

end GlobalTheory.ProdTorusExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageFinitePlacesUnramifiedOrSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StageRam

private theorem pow_apply' {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (x) : (χ ^ a).1 x = χ.1 x ^ a := by
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

private theorem loc_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) :
    (χ ^ a).loc v x = χ.loc v x ^ a :=
  pow_apply' χ a _

private theorem locK_pow {E : Type} [Field E] [NumberField E] (χ : HChar E) (a : ℕ) (v x) :
    (χ ^ a).locK v x = χ.locK v x ^ a :=
  pow_apply' χ a _

private theorem unrAt_pow {E : Type} [Field E] [NumberField E] {χ : HChar E} {v} (h : χ.UnrAt v) (a : ℕ) :
    (χ ^ a).UnrAt v :=
  fun x hx => by rw [loc_pow, h x hx, one_pow]

private theorem chrEq_pow {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (a : ℕ) :
    ChrEq (c ^ a) (χ ^ a) := by
  refine ⟨⟨?_, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · have : ((c ^ a : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => c x ^ a := by
      funext x; simp
    rw [this]
    exact h.1.1.pow a
  · have h1 := h.1.2 x
    simp only [MonoidHom.pow_apply, h1, one_pow]
  · rw [MonoidHom.pow_apply, locK_pow, Units.val_pow_eq_pow_val, ← h.2 P e he k x hx]
    exact map_pow Circle.coeHom _ _

private theorem not_nonSplitAt_of_emb {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : ¬ GlobalTheory.WeilParts.NonSplitAt D v ε := by
  intro h
  refine h.2 ⟨GlobalTheory.EmbChart.idem τ, GlobalTheory.EmbChart.isSplitIdem_idem τ, ?_⟩
  have he : ε = GlobalTheory.EmbChart.atPlace v 1 := by
    obtain ⟨α, rfl, h1, h0⟩ := hε
    rw [GlobalTheory.EmbChart.atPlace_apply]
    congr 1
    refine FiniteAdeleRing.ext _ fun u => ?_
    change evalV D.host.F u α = evalV D.host.F u (GlobalTheory.AdelicU.singleFin v 1)
    by_cases e : u = v
    · subst e; rw [GlobalTheory.AdelicU.evalV_singleFin_self, h1]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e, h0 u e]
  rw [he, GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel]; rfl

private theorem levelLe_one_of_unrAt {L : Type} [Field L] [NumberField L] {χ : HChar L} {w : HeightOneSpectrum (𝓞 L)}
    (h : χ.UnrAt w) : χ.LevelLe w 1 :=
  fun x hx _ => h x hx

private theorem natCast_mem_of_card {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h : Nat.card (𝓞 E ⧸ P.asIdeal) = ℓ) : (ℓ : 𝓞 E) ∈ P.asIdeal := by
  have : Finite (𝓞 E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (h ▸ hℓ.ne_zero)
  letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)
  have h0 : ((Fintype.card (𝓞 E ⧸ P.asIdeal) : ℕ) : 𝓞 E ⧸ P.asIdeal) = 0 := Nat.cast_card_eq_zero _
  rw [← Nat.card_eq_fintype_card, h] at h0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h0


open Classical in
theorem _root_.GlobalTheory.T.towerStage_finitePlaces_unramified_or_split : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧ GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∨ (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∧ ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro W i j p q A A' WW X _ t v e he
  have hm1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have hm2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  have hα : ChrEq (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (alphaH Lc t i j) :=
    GlobalTheory.TwistChr.chrEq_mul (GlobalTheory.TwistChr.chrEq_mul (hL.mu0 j) (hL.xi t)) (chrEq_pow hL.eta _)
  have hβ : ChrEq (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (betaH G i j) :=
    GlobalTheory.TwistChr.chrEq_mul (G.ch.chi_eq _ hm1 hm2) (chrEq_pow hL.eta _)
  have hν : ChrEq (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)))
      (nuH G t i j) := by
    rw [mul_div_mul_right_eq_div]
    exact chrEq_nu G t i j hL
  have hmu : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ∉ S1 D → (Lc.C.mu0 j).UnrAt P :=
    fun P hP => (Lc.C.isMu0 j).unr _ fun k hk => hP (by
      have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
        rw [map_natCast]; exact hk
      refine (S1_mem_OmF D).2 ?_
      fin_cases k
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
  have hxi : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      (∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ P.under (𝓞 D.host.F)) → (Lc.xiH t).UnrAt P := fun P hP => by
    by_contra hc
    rcases (hL.Q_ram t P).1 hc with h | ⟨PP', h, hc'⟩
    · exact hP P h rfl
    · exact hP PP' h (GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc')
  have hchi : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ∉ G.pl.S0 →
      (G.ch.chiH (D.R.m - i)).UnrAt P := fun P hP => G.ch.unr _ hm1 hm2 P hP
  have heta : ∀ P : HeightOneSpectrum (𝓞 D.host.E), (Lc.C.eta ^ (rankV D i j % 2)).UnrAt P :=
    fun P => unrAt_pow (Lc.C.isEta.unr P) _
  by_cases hS : v ∈ G.pl.S0 ∨ ∃ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
  · right
    obtain ⟨w, hw, hwv⟩ : ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v := by
      rcases hS with h | ⟨PP, hP, hPv⟩
      · exact ⟨G.pl.w v, Finset.mem_union_left _ (Finset.mem_image_of_mem _ h), G.pl.under_w h⟩
      · exact ⟨PP, Finset.mem_union_right _ hP, hPv⟩
    have hns : ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
      obtain ⟨τ⟩ := GlobalTheory.LocPlSplit.locPl_split hL t w hw
      rw [hwv] at τ
      exact not_nonSplitAt_of_emb he τ
    refine ⟨hns, fun hu => ?_, ?_⟩
    · have key : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → (nuH G t i j).UnrAt P :=
        fun P hP => (GlobalTheory.LFun.unrAt_iff_of_chrEq hν P).1 (GlobalTheory.UnrOverPlace.unrAt_of_unramAt D _ v e he hu P hP)
      by_cases h0 : v = G.pl.v0
      · subst h0
        exact GlobalTheory.RowTest.squareNuHeckeCharacter_not_unramified_at_chosenPlace hL G t i j (key _ (G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))))
      · by_cases h1 : v ∈ S1 D
        · have hv : v ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inr h1)
          have hwv' := G.pl.under_w hv
          apply (G.ch.lev1 _ hm1 hm2 (G.pl.w v) (by rw [hwv']; exact h1)).2
          have ee : G.ch.chiH (D.R.m - i) = Lc.C.mu0 j * Lc.xiH t / nuH G t i j := by
            rw [nuH, div_div_cancel]
          rw [ee, div_eq_mul_inv]
          exact HChar.LevelLe.mul (HChar.LevelLe.mul ((Lc.C.isMu0 j).tame _) (hL.xi_tame t _))
            (HChar.LevelLe.inv (levelLe_one_of_unrAt (key _ hwv')))
        · obtain ⟨PP, hP, hPv⟩ := hS.resolve_left fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim h0 h1
          apply (hL.Q_ram t PP).2 (Or.inl hP)
          have ee : Lc.xiH t = nuH G t i j * G.ch.chiH (D.R.m - i) / Lc.C.mu0 j := by
            rw [nuH, div_mul_cancel, mul_div_cancel_left]
          rw [ee, div_eq_mul_inv]
          exact ((key PP hPv).mul (hchi PP (by rw [hPv]; exact fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim h0 h1))).mul
            (hmu PP (by rw [hPv]; exact h1)).inv
    · by_cases h0 : v = G.pl.v0
      · subst h0
        exact GlobalTheory.DifferentAtBasePlace.not_dvd_different G
      · by_cases h1 : v ∈ S1 D
        · exact GlobalTheory.DiffSOne.not_dvd_differentIdeal large₂ hR v h1
        · obtain ⟨PP, hP, hPv⟩ := hS.resolve_left fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim h0 h1
          obtain ⟨⟨ℓ, hℓ, hcard, hℓ2, -⟩, -⟩ := hL.Q_pl t PP hP
          have hℓP : ((ℓ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := natCast_mem_of_card hℓ hcard
          have hle : v.asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ PP.asIdeal := by
            rw [← hPv]
            exact Ideal.map_comap_le
          refine GlobalTheory.SplitUnram.not_dvd_different hℓ v ?_ ?_
          · rw [← hPv]
            show algebraMap _ (𝓞 D.host.E) _ ∈ PP.asIdeal
            rw [map_natCast]; exact hℓP
          · intro hv2
            have h' := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) hv2
            rw [Ideal.map_pow, map_natCast] at h'
            exact hℓ2 (Ideal.pow_right_mono hle 2 h')
  · left
    push_neg at hS
    obtain ⟨hS0, hQ⟩ := hS
    have hS1 : v ∉ S1 D := fun h => hS0 (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
    refine ⟨GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D _ _ hα v e he fun P hP => ?_, GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D _ _ hβ v e he fun P hP => ?_⟩
    · exact ((hmu P (by rw [hP]; exact hS1)).mul (hxi P fun PP hPP h => hQ PP hPP (h.trans hP))).mul (heta P)
    · exact (hchi P (by rw [hP]; exact hS0)).mul (heta P)

end GlobalTheory.StageRam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRelationCocycleInTranslation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem GlobalTheory.TwFam.trel_cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (ν mu β₀ β₁ β₂ : D.toPre.X) (s₀ : SecT D.toPre a n j β₀) (s₁ : SecT D.toPre a n j β₁) (s₂ : SecT D.toPre a n j β₂), β₁ = β₀ + shift h h' n j ν → β₂ = β₁ + shift h h' n j mu → TRel h ν s₀ s₁ → TRel h (ν + mu) s₀ s₂ → TRel h mu s₁ s₂ := by
  intro R _ _ _ hR D a a' h h' hE n j ν mu β₀ β₁ β₂ s₀ s₁ s₂ h₁ h₂ hν hνμ
  have hL := D.toPre.P.isLB
  obtain ⟨u₀, hu₀⟩ := _root_.GlobalTheory.TwFam.Gen0.main R hR D a a' h h' hE n j ν β₀ β₁ h₁
  obtain ⟨⟨u₁, hu₁⟩, -, -⟩ := GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator R hR D a h hE.1 hE.2.2.2.1 n j ν β₀ β₁ u₀ hu₀
  intro u hu Z x z J hJ
  have hc : (DegPre.trF D.toPre (FractionRing R) mu).left ≫ (DegPre.trF D.toPre (FractionRing R) ν).left =
      (DegPre.trF D.toPre (FractionRing R) (ν + mu)).left := by
    rw [← Over.comp_left, ReciprocityTheory.ChartRestriction.G.DVR.UUA.trF_add, add_comm]
  have FE : FormEq (Sum.elim (dφ D.toPre a mu β₁ β₂) (fun k => (DegPre.trF D.toPre (FractionRing R) mu).left ≫ dφ D.toPre a ν β₀ β₁ k))
      (Sum.elim (dε n j) (dε n j)) (dφ D.toPre a (ν + mu) β₀ β₂) (dε n j) := by
    intro U _ g
    simp only [dφ, dε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, ← Category.assoc, hc]
    simp only [zpow_neg, Finset.prod_inv_distrib, Category.assoc]
    group
  obtain ⟨w, hw, hwv⟩ := exists_gen hL FE _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ u _ hu.1
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ u₁ hu₁.1 _))
  have hwf : IsFac D.toPre a h n j (ν + mu) β₀ β₂ w := by
    refine ⟨hw, fun z' J' hJ' => ?_⟩
    rw [hwv _ _ z' J' hJ', val_mul hJ', val_pull hJ', hu.2 z' J' hJ', GlobalTheory.T.normalisedTwistedFactor_value_at_latticePoint R hR D a a' h h' hE n j ν mu β₀ β₁ h₁ u₁ hu₁ z' J' hJ']
    rw [mul_comm]
    exact inv_mul_cancel_right _ _
  have e1 := hν u₁ hu₁ Z (x ≫ (DegPre.trF D.toPre (FractionRing R) mu).left) z J hJ
  have e2 := hνμ w hwf Z x z J hJ
  rw [hwv _ _ z J hJ, val_mul hJ, val_pull hJ, ← hc] at e2
  simp only [Category.assoc] at e1 e2 ⊢
  rw [e2, e1, Units.val_mul]
  ring
end

