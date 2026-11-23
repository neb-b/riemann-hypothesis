module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPositiveDefiniteQuadraticFormEndomorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoRefinementsSamePolarised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumCmp.SamePolIso
variable {R : Type} [CommRing R] [IsDomain R]

theorem grp_iso {B Q : Over (Sp R)} [GrpObj B] [GrpObj Q] {β : B.left ⟶ Q.left}
    (h : IsGrpPullback B Q (spMap (RingHom.id R)) β) : ∃ f : B ≅ Q, f.hom.left = β ∧ IsMonHom f.hom := by
  have hs : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  have h1 := h.1
  rw [hs] at h1
  have : IsIso β := h1.isIso_fst_of_isIso
  let f : B ⟶ Q := Over.homMk β (by simpa using h1.w)
  have : IsIso ((Over.forget (Sp R)).map f) := (inferInstance : IsIso β)
  have : IsIso f := isIso_of_reflects_iso f (Over.forget _)
  refine ⟨asIso f, rfl, isMonHom_of_mul _ fun T x y => ?_⟩
  let ρ : Over.mk (T.hom ≫ spMap (RingHom.id R)) ⟶ T := Over.homMk (𝟙 T.left) (by simp [hs])
  have e := h.2 T x y (ρ ≫ x ≫ f) (ρ ≫ y ≫ f) (by simp [ρ, f]) (by simp [ρ, f])
  apply Over.OverMorphism.ext
  rw [← MonObj.comp_mul] at e
  simpa [ρ, f] using e.symm

theorem gw_congr {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    {f f' : Y ⟶ X'} (hf : f = f') (y : Y) {j j' : L.ι} (hj : j = j') {k k' : L'.ι} (hk : k = k') :
    gw w f y j k = gw w f' y j' k' := by
  subst hf hj hk; rfl

theorem exists_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D : DegPre R), SamePol D₀ D →
  ∃ (β : D₀.P.A ≅ D.P.A) (xe : D₀.X ≃+ D.X), IsMonHom β.hom ∧ (∀ χ, D₀.c χ ≫ β.hom = D.c (xe χ)) ∧
    ∃ wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L)
        ((abelian₂ D.P.A D.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) : G2 D₀.P.A ⟶ G2 D.P.A).left),
      wΛ.IsGen ∧
      ∀ (a a' : D₀.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι)
        (J' : ((TK R).left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D.P.L z J → Good D₀.P.L z J' →
        val (D₀.tau a a') (𝟙 _) z J' =
          GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z J J' *
            val (D.tau (xe a) (xe a')) (𝟙 _) z J := by
  intro R _ _ D₀ D h
  obtain ⟨Q, e₀, e, ⟨β₀, β₂₀, w₀, p₀, s₀, g₀, c₀, t₀⟩, ⟨β₁, β₂₁, w₁, p₁, s₁, g₁, c₁, t₁⟩⟩ := h
  have hs : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  obtain ⟨f₀, hf₀, m₀⟩ := grp_iso p₀
  obtain ⟨f₁, hf₁, m₁⟩ := grp_iso p₁
  have cc₀ : ∀ a, D₀.c a ≫ f₀.hom = Q.c (e₀ a) := fun a => Over.OverMorphism.ext (by
    rw [Over.comp_left, hf₀, c₀ a, hs, Category.id_comp])
  have cc₁ : ∀ a, D.c a ≫ f₁.hom = Q.c (e a) := fun a => Over.OverMorphism.ext (by
    rw [Over.comp_left, hf₁, c₁ a, hs, Category.id_comp])
  have ea : ∀ x, e ((e₀.trans e.symm) x) = e₀ x := fun x => by simp
  have hcβ : ∀ χ, D₀.c χ ≫ (f₀ ≪≫ f₁.symm).hom = D.c ((e₀.trans e.symm) χ) := fun χ => by
    rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, cc₀, Iso.comp_inv_eq, cc₁, ea]
  have hF : (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) :
      G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁ = β₂₀ := by
    apply pullback.hom_ext
    · change _ ≫ β₂₁ ≫ (fst Q.B Q.B).left = β₂₀ ≫ (fst Q.B Q.B).left
      rw [s₁.1, s₀.1, ← Category.assoc, ← Over.comp_left, lift_fst, ← hf₁, ← hf₀, ← Over.comp_left, ← Over.comp_left]
      simp
    · change _ ≫ β₂₁ ≫ (snd Q.B Q.B).left = β₂₀ ≫ (snd Q.B Q.B).left
      rw [s₁.2, s₀.2, ← Category.assoc, ← Over.comp_left, lift_snd, ← hf₁, ← hf₀, ← Over.comp_left, ← Over.comp_left]
      simp

  subst hF
  have hLQ : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ Q.M.isLB _ _
  have hLD : (abelian₂ D.P.A D.P.L).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  have hLD₀ : (abelian₂ D₀.P.A D₀.P.L).IsLB := DVR.linComb_isLB _ D₀.P.isLB _ _
  obtain ⟨wΛ, T⟩ := exists_cancel hLQ w₁ w₀ ((isGen_iff _).1 g₁) ((isGen_iff _).1 g₀) hLD hLD₀
  refine ⟨f₀ ≪≫ f₁.symm, e₀.trans e.symm, ?_, hcβ, wΛ,
    (isGen_iff _).2 (T.pgen_cancel hLQ ((isGen_iff _).1 g₁) ((isGen_iff _).1 g₀)), ?_⟩
  · show IsMonHom (f₀.hom ≫ f₁.inv)
    infer_instance
  intro a a' z J J' hJ hJ'
  choose d hd using fun χ : (TK R).left ⟶ Q.B.left => exists_chart Q.M.isLB (χ z)
  have hκ : 𝟙 (TK R).left ≫ jK R = jK R ≫ spMap (RingHom.id R) := by rw [hs]; simp
  have A₀ := t₀ (𝟙 _) hκ a a' z d J' hd hJ'
  have A₁ := t₁ (𝟙 _) hκ ((e₀.trans e.symm) a) ((e₀.trans e.symm) a') z d J hd hJ
  rw [ea, ea] at A₁
  have hP : (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left = (lift (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a)) (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a'))).left := by
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc, Category.assoc, hcβ, hcβ]
  have m₁ : β₂₁ ((lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z)) ∈ (abelian₂ Q.B Q.M.L).U
      (fun I => d ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ ((lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁) ≫ (psum Q.B (x2 Q.B) I.down).left)) := by
    have := Good.mem (L := Q.M.L) hd (fun I : ULift (Finset (Fin 2)) => (psum Q.B (x2 Q.B) I.down).left) ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁)
    simp only [Category.assoc] at this ⊢
    exact this
  have m₂ : (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z) ∈ (abelian₂ D.P.A D.P.L).U (fun I => J ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ (psum D.P.A (x2 D.P.A) I.down).left)) := by
    have := Good.mem (L := D.P.L) hJ (fun I : ULift (Finset (Fin 2)) => (psum D.P.A (x2 D.P.A) I.down).left) ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left)
    simp only [Category.assoc] at this
    exact this
  have m₃ : (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z ∈ (abelian₂ D₀.P.A D₀.P.L).U (fun I => J' ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (psum D₀.P.A (x2 D₀.P.A) I.down).left)) :=
    Good.mem (L := D₀.P.L) hJ' (fun I : ULift (Finset (Fin 2)) => (psum D₀.P.A (x2 D₀.P.A) I.down).left) (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left
  have key := T _ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z _ _ _ m₁ m₂ m₃
  have k₁ : gw w₁ ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left) z (fun I => d ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ ((lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ β₂₁) ≫ (psum Q.B (x2 Q.B) I.down).left))
      (fun I => J ((lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left ≫ (lift (fst D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) (snd D₀.P.A D₀.P.A ≫ (f₀ ≪≫ f₁.symm).hom) : G2 D₀.P.A ⟶ G2 D.P.A).left ≫ (psum D.P.A (x2 D.P.A) I.down).left)) =
      GlobalTheory.PolDeg.lamVal w₁ (lift (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a))
        (toUnit (TK R) ≫ D.c ((e₀.trans e.symm) a'))).left z d J :=
    gw_congr w₁ hP z (funext fun I => by rw [← hP]; simp only [Category.assoc])
      (funext fun I => by rw [← hP]; simp only [Category.assoc])
  rw [k₁] at key
  rw [A₀, A₁]
  change gw w₀ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z _ _ * _ = gw wΛ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z _ _ * _
  rw [key, _root_.mul_assoc, _root_.mul_left_comm]
end GlobalTheory.MumCmp.SamePolIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExtEmb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem exists_labels_finExt_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁), FinExt ρ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (hD : IsPullDeg ρ D.toPre D₁.toPre) (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left), IsFib ρ A A₁ a → ∃ (_ : Algebra (FractionRing R) (Kb R₁)) (em : Kb R →ₐ[FractionRing R] Kb R₁) (lab₁ : Labels D₁.toPre A₁), (∀ r, algebraMap (FractionRing R) (Kb R₁) (algebraMap R _ r) = algebraMap (FractionRing R₁) (Kb R₁) (algebraMap R₁ _ (ρ r))) ∧ OneTrait D₁.toPre A₁ lab₁ ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre (Kb R) k) (p₁ : QkPt D.toPre (Kb R₁) k) (p' : QkPt D₁.toPre (Kb R₁) k), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF ρ hD (Kb R₁) p₁.g p'.g → (lab₁ k p').left ≫ a = spMap em.toRingHom ≫ (lab k p).left := by
  intro R _ _ _ hR D A lab hT R₁ _ _ _ ρ hρ D₁ hD A₁ a ⟨ga, hga, gpa, la⟩
  obtain ⟨W₀, _, _, _, φ₀, G, _, _, D₀, A₀, U₀, h₀, a₀, _, em₀, hW₀, i₀, l₀, hG, ⟨g₀, hg₀, gp₀, lb₀⟩, c₀, H₀⟩ := hT
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have hGF := hL.globalFns
  have := hR.2
  have hB := D.tau_bimult
  obtain rfl := eq_fracMap hρ.2.1 hga
  obtain rfl := eq_fracMap i₀ hg₀
  letI : Algebra (FractionRing R) (Kb R₁) := ((algebraMap (FractionRing R₁) (Kb R₁)).comp (fracMap hρ.2.1)).toAlgebra
  have c' : Compat ρ (Kb R₁) := fun r => congrArg (algebraMap (FractionRing R₁) (Kb R₁)) (hga r)

  obtain ⟨W, _, _, _, io, φ, hW, iio, lio, lφ, hc⟩ :=
    GlobalTheory.LocExt.exists_cDvr_ext_of_finite R R₁ ρ hρ.2.1 hρ.2.2 W₀ hW₀ φ₀ l₀
  have iφ : Function.Injective φ := by
    letI := ρ.toAlgebra
    haveI : Module.Finite R R₁ := hρ.2.2
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := R) ?_
    change Ideal.comap ρ (RingHom.ker φ) = ⊥
    rw [RingHom.comap_ker, hc, ← RingHom.injective_iff_ker_eq_bot]
    exact iio.comp i₀
  have := hW₀.1
  have := hW₀.2.2
  have := hW.1
  have b₀ : AdmBase W₀ (maximalIdeal W₀) := ⟨inferInstance, inferInstance, inferInstance, hW₀.2.1⟩
  have b₁ : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨D₂, h₁, A₂, U₂, b, hP, gpb, lb, hb⟩ := exists_pull_fib hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    b₀ b₁ io iio (map_maximalIdeal_le io) hG U₀
  obtain ⟨hc₀, T₀⟩ := exists_comp i₀ iio h₀ h₁
  obtain ⟨h', T'⟩ : ∃ h' : IsPullDeg φ D₁.toPre D₂.toPre, Tower hD h' hc₀ := by
    revert hc₀
    rw [← hc]
    exact fun hc₀ _ => exists_cancel hρ.2.1 iφ hD hc₀
  have fr : (fracMap iφ).comp (fracMap hρ.2.1) = (fracMap iio).comp (fracMap i₀) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => by
      simp only [RingHom.comp_apply, fracMap_algebraMap]
      exact congrArg _ (RingHom.congr_fun hc r))
  obtain ⟨a₁, e₁, gp₁, lb₁⟩ := exists_fib_cancel (g' := spMap (fracMap iφ))
    ((Geo.Tor.spMap_comp _ _).symm.trans ((congrArg spMap fr).trans (Geo.Tor.spMap_comp _ _))) gpa la gp₀ lb₀ gpb lb
  letI : Algebra (FractionRing R₁) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp (fracMap iφ)).toAlgebra
  letI : Algebra (FractionRing W₀) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp (fracMap iio)).toAlgebra
  letI : Algebra (FractionRing R) (Kb W) :=
    ((algebraMap (FractionRing W) (Kb W)).comp ((fracMap iφ).comp (fracMap hρ.2.1))).toAlgebra
  have cφ : Compat φ (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (fracMap_algebraMap iφ r)
  have cio : Compat io (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (fracMap_algebraMap iio r)
  have cρ : Compat ρ (Kb W) := fun r =>
    congrArg (fun t => algebraMap (FractionRing W) (Kb W) (fracMap iφ t)) (fracMap_algebraMap hρ.2.1 r)
  have cc : Compat (io.comp φ₀) (Kb W) := fun r => (cρ r).trans ((cφ _).trans
    (congrArg (fun t => algebraMap (FractionRing W) (Kb W) (algebraMap W _ t)) (RingHom.congr_fun hc r)))
  have cφ₀ : Compat φ₀ (Kb W) := fun r => (cc r).trans (cio _).symm
  obtain ⟨em⟩ := nonempty_lift (FractionRing R₁) (Kb W)
  obtain ⟨j⟩ := nonempty_lift (FractionRing W₀) (Kb W)
  let emR : Kb R₁ →ₐ[FractionRing R] Kb W := ⟨em.toRingHom, fun t => em.commutes (fracMap hρ.2.1 t)⟩
  have a₀K : algebraMap (FractionRing R) (Kb W₀) = (algebraMap (FractionRing W₀) (Kb W₀)).comp (fracMap i₀) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c₀ r).trans
      (congrArg (algebraMap (FractionRing W₀) (Kb W₀)) (fracMap_algebraMap i₀ r).symm))
  let jR : Kb W₀ →ₐ[FractionRing R] Kb W := ⟨j.toRingHom, fun t => by
    rw [a₀K]
    exact (j.commutes (fracMap i₀ t)).trans
      (congrArg (algebraMap (FractionRing W) (Kb W)) (RingHom.congr_fun fr t).symm)⟩

  obtain ⟨em'⟩ := nonempty_lift (FractionRing R) (Kb R₁)
  letI : Algebra (Kb R) (Kb W) := (emR.comp em').toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) (Kb W) :=
    IsScalarTower.of_algebraMap_eq fun x => ((emR.comp em').commutes x).symm
  let emK : Kb R →ₐ[FractionRing R] Kb R₁ := em'.comp ((jR.comp em₀).restrictNormal (Kb R))
  have hK : (emR.comp emK).toRingHom = (jR.comp em₀).toRingHom :=
    RingHom.ext fun x => (jR.comp em₀).restrictNormal_commutes (Kb R) x

  have ex : ∀ (k : ℕ) (p' : QkPt D₁.toPre (Kb R₁) k), ∃ x : TFK (R := R₁) (Kb R₁) ⟶ A₁.A, 1 ≤ k →
      ∃ (p : QkPt D.toPre (Kb R) k) (p₁ : QkPt D.toPre (Kb R₁) k), QkExt emK.toRingHom p p₁ ∧ p'.y = hD.xe.symm p₁.y ∧
        IsPullGtF ρ hD (Kb R₁) p₁.g p'.g ∧ x.left ≫ a = spMap emK.toRingHom ≫ (lab k p).left := by
    intro k p'
    by_cases hk : 1 ≤ k
    · obtain ⟨p₁, hy, hg⟩ := qkPullExists hGF R R₁ ρ D.toPre D₁.toPre hD (Kb R₁) c' k p'
      obtain ⟨p, hp⟩ := exists_of_ext hB emK hk p₁
      obtain ⟨x, hx⟩ := exists_lift_pt gpa.1 emK.toRingHom emK.comp_algebraMap (lab k p)
      exact ⟨x, fun _ => ⟨p, p₁, hp, hy, hg, hx⟩⟩
    · exact ⟨η[A₁.A] |> fun e => toUnit _ ≫ e, fun h => absurd h hk⟩
  choose lab₁ hlab₁ using ex
  refine ⟨inferInstance, emK, lab₁, c', ?_, ?_⟩
  ·
    refine ⟨W, _, inferInstance, inferInstance, φ, (Over.pullback (specOf io)).obj G, inferInstance, inferInstance, D₂, A₂,
      U₂, h', a₁, inferInstance, em, hW, iφ, lφ, IsSemiAbelian.pullback _ G hG,
      ⟨fracMap iφ, fracMap_algebraMap iφ, gp₁, lb₁⟩, cφ, ?_⟩
    intro k hk p' p₁' p'' x₁ y₁ y₂ y₃ y₄
    obtain ⟨p, p₁, z₁, z₂, z₃, z₄⟩ := hlab₁ k p' hk
    obtain ⟨r, hr⟩ := exists_ext hB emR p₁
    have r₁ : IsPullGtF ρ hD (Kb W) r.g p₁'.g := isPullGtF_ext hD cρ em.toRingHom em.comp_algebraMap z₃ hr y₁
    have r₂ := T'.isPullGtF cc r₁ y₃
    have hq : QkExt (jR.comp em₀).toRingHom p r := by
      rw [← hK]
      exact qkExt_trans z₁ hr
    have key : spMap (emR.comp emK).toRingHom ≫ (lab k p).left = spMap (jR.comp em₀).toRingHom ≫ (lab k p).left := by
      rw [hK]
    obtain ⟨q₁, hq₁⟩ := exists_ext hB em₀ p
    obtain ⟨r', hr'⟩ := exists_ext hB jR q₁
    obtain rfl : r = r' := ext_unique hB (jR.comp em₀) hq (qkExt_trans hq₁ hr')
    let q₀ := pullQk h₀ hGF c₀ hB D₀.tau_bimult q₁
    obtain ⟨x₀, hx₀⟩ := exists_lift_pt gp₀.1 em₀.toRingHom (em₀.comp_algebraMap.trans a₀K) (lab k p)
    have t₀ := H₀ k hk p q₁ q₀ x₀ hq₁ rfl (isPullGtF_pullGt h₀ hGF c₀ _) hx₀
    obtain ⟨⟨q₀', hq₀'⟩, hx, hgal⟩ := GlobalTheory.UT.Cl.galois_holds W₀ _ b₀ D₀ A₀ G hG U₀ _ (Kb W) j k hk q₀
    obtain ⟨x₀', hx₀'⟩ := hx x₀
    have t₁ := (hgal q₀' x₀ x₀' hq₀' hx₀').1 t₀
    have s₁ : IsPullGtF φ₀ h₀ (Kb W) r.g q₀'.g :=
      isPullGtF_ext h₀ cφ₀ j.toRingHom j.comp_algebraMap (isPullGtF_pullGt h₀ hGF c₀ _) hr' hq₀'
    have s₂ := isPullGtF_pullGt h₁ hGF cio q₀'.g
    rw [← pullGt_unique hc₀ cc r₂ (T₀.isPullGtF cc s₁ s₂)] at s₂
    have ey : p''.y = h₁.xe.symm q₀'.y := by
      apply hc₀.xe.injective
      have u₁ : hc₀.xe p''.y = r.y := by
        rw [← T'.xe_eq, y₂, AddEquiv.apply_symm_apply, y₁.1, z₂, AddEquiv.apply_symm_apply, hr.1]
      rw [u₁, ← T₀.xe_eq, AddEquiv.apply_symm_apply, hq₀'.1, hr'.1]
      exact (h₀.xe.apply_symm_apply _).symm
    have ex₁ : x₁.left ≫ b = x₀'.left := by
      apply gp₀.1.hom_ext
      · rw [Category.assoc, ← e₁, ← Category.assoc, y₄, Category.assoc, z₄, hx₀', Category.assoc, hx₀, ← Category.assoc,
          ← Category.assoc, ← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp]
        exact key
      · rw [Category.assoc, gpb.1.w, ← Category.assoc, Over.w x₁, Over.w x₀']
        exact (Geo.Tor.spMap_comp _ _).symm
    refine h5.qkBaseChange W₀ W _ _ b₀ b₁ io D₀ A₀ G U₀ _ (Iso.refl _) (by show IsMonHom (𝟙 _); infer_instance) A₂ D₂ h₁
      U₂ hP (Kb W) cio k hk q₀' x₀' p'' x₁ ey s₂ ?_ t₁
    rw [hb, ← Category.assoc, ex₁]
  ·
    intro k hk p p₁ p' e₁' e₂' e₃'
    obtain ⟨q, q₁, z₁, z₂, z₃, z₄⟩ := hlab₁ k p' hk
    obtain rfl : q₁ = p₁ := qk_ext (hD.xe.symm.injective (by rw [← z₂]; exact e₂')) (pullGt_unique' hD z₃ e₃')
    obtain rfl := qkExt_inj hB emK z₁ e₁'
    exact z₄

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGaloisDescentAbelianVarietyFinit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem spMap_mul_aut {K' : Type} [Field K'] (a b : K' ≃+* K') :
    spMap ((a * b : K' ≃+* K') : K' →+* K') = spMap (a : K' →+* K') ≫ spMap (b : K' →+* K') := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem lbIso_pull_comp_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a b : X ⟶ X)
    (ha : LBIso L (L.pull a)) (hb : LBIso L (L.pull b)) : LBIso L (L.pull (a ≫ b)) :=
  LBIso.trans hL (pull_isLB hL a) (pull_isLB hL _) ha
    (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L a a rfl) (chartPullSame L _ (fun _ => b) _ a fun _ => rfl) hb)

theorem exists_lb_descent_of_finite_aut : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp K')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap i) φ → ∀ L' : LB A'.left, L'.IsLB → (∀ g, ∃ ψ : A'.left ⟶ A'.left, ψ ≫ φ = φ ∧ ψ ≫ A'.hom = A'.hom ≫ spMap (s g).toRingHom ∧ LBIso L' (L'.pull ψ)) → ∃ L : LB A.left, L.IsLB ∧ LBIso L' (L.pull φ) := by
  intro K K' _ _ i hfin Γ _ s hs hfix A _ A' _ φ hA hp L' hL' hinv
  letI : Algebra K K' := i.toAlgebra
  obtain ⟨hgal, hgen⟩ := GlobalTheory.T.isGalois_of_finite_fixed_automorphisms K K' i hfin Γ s hs hfix
  haveI : FiniteDimensional K K' := hfin
  have hc0 := GlobalTheory.ZM.DwModel.isGaloisCover_field K K'
  have hfixσ : ∀ σ : K' ≃ₐ[K] K', ∀ x, (σ : K' ≃+* K') (i x) = i x := fun σ x => σ.commutes x
  have hσi : ∀ σ : K' ≃ₐ[K] K', spMap (σ : K' →+* K') ≫ spMap i = spMap i := fun σ => by
    simp only [spMap, ← Spec.map_comp]
    congr 1
    ext x
    exact σ.commutes x
  have hw : ∀ σ : K' ≃ₐ[K] K', (A'.hom ≫ spMap (σ : K' →+* K')) ≫ spMap i = φ ≫ A.hom := fun σ => by
    rw [Category.assoc, hσi σ, hp.1.w]
  let t : (K' ≃ₐ[K] K') → (A'.left ⟶ A'.left) := fun σ =>
    hp.1.lift φ (A'.hom ≫ spMap (σ : K' →+* K')) (hw σ).symm
  have ht1 : ∀ σ, t σ ≫ φ = φ := fun σ => hp.1.lift_fst _ _ _
  have ht2 : ∀ σ, t σ ≫ A'.hom = A'.hom ≫ spMap (σ : K' →+* K') := fun σ => hp.1.lift_snd _ _ _
  have hGC : GlobalTheory.ZM.IsGaloisCover (K' ≃ₐ[K] K') t φ :=
    hc0.of_isPullback (u := A'.hom) (v := A.hom) hp.1.flip (fun a => ht2 a) ht1

  have hQ : ∀ τ ∈ Submonoid.closure (Set.range s), ∃ ψ : A'.left ⟶ A'.left, ψ ≫ φ = φ ∧
      ψ ≫ A'.hom = A'.hom ≫ spMap (τ : K' →+* K') ∧ LBIso L' (L'.pull ψ) := by
    intro τ hτ
    induction hτ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hinv g
    | one =>
      refine ⟨𝟙 _, Category.id_comp _, ?_, ?_⟩
      · rw [Category.id_comp]
        have : ((1 : K' ≃+* K') : K' →+* K') = RingHom.id K' := rfl
        rw [this]
        exact (Category.comp_id _).symm.trans (by simp [spMap])
      · exact LBIso.symm (lbIso_of_chartPull (chartPullPull L' (𝟙 _)) hL')
    | mul x y _ _ hx hy =>
      obtain ⟨ψ₁, a1, b1, c1⟩ := hx
      obtain ⟨ψ₂, a2, b2, c2⟩ := hy
      refine ⟨ψ₁ ≫ ψ₂, by rw [Category.assoc, a2, a1], ?_, lbIso_pull_comp_self hL' _ _ c1 c2⟩
      rw [Category.assoc, b2, ← Category.assoc, b1, Category.assoc, spMap_mul_aut]
  have hall : ∀ σ : K' ≃ₐ[K] K', LBIso L' (L'.pull (t σ)) := fun σ => by
    obtain ⟨ψ, a1, b1, c1⟩ := hQ (σ : K' ≃+* K') (hgen _ (hfixσ σ))
    have : ψ = t σ := hp.1.hom_ext (by rw [a1, ht1]) (by rw [b1, ht2]; rfl)
    exact this ▸ c1
  have hA' : IsAbelianScheme A' := by
    have := hA.comm
    have hcomm : IsCommMonObj A' := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hp.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hp.2 T x y (pushPt hp.1.w x) (pushPt hp.1.w y) rfl rfl,
        ← hp.2 T y x (pushPt hp.1.w y) (pushPt hp.1.w x) rfl rfl, _root_.mul_comm]
    exact { comm := hcomm
            smooth := MorphismProperty.of_isPullback (P := @Smooth) hp.1 hA.smooth
            proper := MorphismProperty.of_isPullback (P := @IsProper) hp.1 hA.proper
            geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) hp.1 hA.geomConnected }
  have hsurj : Function.Surjective A'.hom.appTop.hom := (GlobalTheory.globalFns_holds (Sp K') A' hA').2
  let e : Sp K' ⟶ A'.left := hp.1.lift (spMap i ≫ eSec A) (𝟙 _) (by
    rw [Category.id_comp, Category.assoc, show eSec A ≫ A.hom = 𝟙 _ from Over.w η[A]]; exact Category.comp_id _)
  have he : e ≫ A'.hom = 𝟙 _ := hp.1.lift_snd _ _ _
  have heθ : ∀ σ : K' ≃ₐ[K] K', e ≫ t σ = spMap (σ : K' →+* K') ≫ e := fun σ => by
    refine hp.1.hom_ext ?_ ?_
    · rw [Category.assoc, ht1, Category.assoc, hp.1.lift_fst, ← Category.assoc, hσi σ]
    · rw [Category.assoc, ht2, ← Category.assoc, he, Category.assoc, he]
      simp
  obtain ⟨u, hu, hcoc⟩ := GlobalTheory.T.exists_linearisation_invariant_rigidified_bundle (Sp K') A'.left A'.hom e he hsurj L' hL'
    (GlobalTheory.SS.HtForm.gen_field _ (pull_isLB hL' e)) (K' ≃ₐ[K] K') t (fun σ => spMap (σ : K' →+* K'))
    (fun a c => hGC.mul a c) (fun a c => hc0.mul a c) heθ hall
  exact GlobalTheory.LinDescent.exists_descent_of_isGaloisCover _ _ φ _ t L' hGC hL' u hu hcoc

end GlobalTheory.Mum.GenDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompPullbackIdValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.IsoPullIdComp

theorem exists_comp_val : ∀ {Y X₀ X : Scheme.{0}} {A : LB Y} {L₀ : LB X₀} {M : LB X} {K₀ K : Type} [Fintype K₀] [Fintype K] (φ₀ : K₀ → (Y ⟶ X₀)) (ε₀ : K₀ → ℤ) (φ : K → (Y ⟶ X)) (ε : K → ℤ), A.IsLB → L₀.IsLB → M.IsLB → ∀ (u : LB.Iso A (LB.LinComb L₀ φ₀ ε₀)), u.IsGen → ∀ (v : LB.Iso (LB.LinComb L₀ φ₀ ε₀) ((LB.LinComb M φ ε).pull (𝟙 Y))), v.IsGen → ∃ w : LB.Iso A (LB.LinComb M φ ε), w.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J₀ : (Z ⟶ X₀) → L₀.ι) (a : A.ι), q z ∈ A.U a → Good M z J → Good L₀ z J₀ → gm q z _ (w.s (fun k => J (q ≫ φ k), a)) = gm q z _ (u.s (fun k => J₀ (q ≫ φ₀ k), a)) * GlobalTheory.Mum.Two.isoVal v q z J J₀ := by
  intro Y X₀ X A L₀ M K₀ K _ _ φ₀ ε₀ φ ε hA hL₀ hM u hu v hv
  have eu := GlobalTheory.LinCombComp.gm_iso_linComb φ₀ ε₀ u hu
  have ev : ∀ (y : Y) (j j' : K → M.ι) (j₀ j₀' : K₀ → L₀.ι), y ∈ LB.wchart M φ j → y ∈ LB.wchart L₀ φ₀ j₀ →
      y ∈ LB.wchart M φ j' → y ∈ LB.wchart L₀ φ₀ j₀' →
      gm (𝟙 Y) y ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
          (v.s (fun _ => j, j₀)) =
        (trF φ ε (𝟙 Y) y j j' * (trF φ₀ ε₀ (𝟙 Y) y j₀ j₀')⁻¹) *
          gm (𝟙 Y) y ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j', j₀'))
            (v.s (fun _ => j', j₀')) := by
    intro y j j' j₀ j₀' h h0 h' h0'
    have hp : (𝟙 Y : Y ⟶ Y) y ∈
        (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀) := ⟨mem_pull.2 h, h0⟩
    have hq : (𝟙 Y : Y ⟶ Y) y ∈
        (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j', j₀') := ⟨mem_pull.2 h', h0'⟩
    have e1 := GlobalTheory.LinCombComp.gm_gen hv (𝟙 Y) y hp hq
    rw [GlobalTheory.Mum.Two.gm_div_pull (𝟙 Y) y _ _ hp hq, Category.comp_id] at e1
    exact e1
  have glue : ∀ (j : K → M.ι) (a : A.ι), ∃ s : Γ(Y, LB.wchart M φ j ⊓ A.U a)ˣ,
      ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K₀ → L₀.ι), q z ∈ LB.wchart M φ j → q z ∈ A.U a →
        q z ∈ LB.wchart L₀ φ₀ j₀ →
        gm q z (LB.wchart M φ j ⊓ A.U a) s =
          gm q z ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
              (v.s (fun _ => j, j₀)) *
            gm q z (LB.wchart L₀ φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) := by
    intro j a
    obtain ⟨W, hW⟩ : ∃ W : (K₀ → L₀.ι) → Y.Opens, ∀ j₀, W j₀ = LB.wchart M φ j ⊓ A.U a ⊓ LB.wchart L₀ φ₀ j₀ :=
      ⟨_, fun _ => rfl⟩
    have memW : ∀ y j₀, y ∈ W j₀ ↔ (y ∈ LB.wchart M φ j ∧ y ∈ A.U a) ∧ y ∈ LB.wchart L₀ φ₀ j₀ := fun y j₀ => by
      rw [hW]; exact Iff.rfl
    have l₀ : ∀ j₀, W j₀ ≤ LB.wchart M φ j ⊓ A.U a := fun j₀ y hy => ((memW y j₀).1 hy).1
    have l₁ : ∀ j₀, W j₀ ≤ (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀) :=
      fun j₀ y hy => ⟨mem_pull.2 ((memW y j₀).1 hy).1.1, ((memW y j₀).1 hy).2⟩
    have l₂ : ∀ j₀, W j₀ ≤ LB.wchart L₀ φ₀ j₀ ⊓ A.U a := fun j₀ y hy =>
      ⟨((memW y j₀).1 hy).2, ((memW y j₀).1 hy).1.2⟩
    obtain ⟨uu, hu'⟩ : ∃ uu : ∀ j₀, Γ(Y, W j₀)ˣ, ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K₀ → L₀.ι),
        q z ∈ W j₀ → gm q z (W j₀) (uu j₀) =
          gm q z ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
              (v.s (fun _ => j, j₀)) *
            gm q z (LB.wchart L₀ φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) :=
      ⟨fun j₀ => res (l₁ j₀) (v.s (fun _ => j, j₀)) * res (l₂ j₀) (u.s (j₀, a)), fun Z' q z j₀ h =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res q z (l₁ j₀) h _) (gm_res q z (l₂ j₀) h _))⟩
    obtain ⟨s, hs⟩ := glue_unit (LB.wchart M φ j ⊓ A.U a) W l₀ (fun y hy => by
        choose j₀ hj₀ using fun k => exists_chart hL₀ (φ₀ k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j₀, (memW y j₀).2 ⟨hy, Set.mem_iInter.2 hj₀⟩⟩) uu
      (fun j₀ j₀' y hy => by
        obtain ⟨⟨h1, ha⟩, h0⟩ := (memW y j₀).1 hy.1
        obtain ⟨-, h0'⟩ := (memW y j₀').1 hy.2
        refine (hu' Y (𝟙 Y) y j₀ hy.1).trans (Eq.trans ?_ (hu' Y (𝟙 Y) y j₀' hy.2).symm)
        rw [ev y j j j₀ j₀' h1 h0 h1 h0', eu y j₀ j₀' a a h0 ha h0' ha,
          GlobalTheory.LinCombComp.trF_self hM φ ε (𝟙 Y) y j h1, gm_self hA (𝟙 Y) y ha]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
    refine ⟨s, fun Z' q z j₀ h1 ha h0 => ?_⟩
    have hy : q z ∈ W j₀ := (memW _ j₀).2 ⟨⟨h1, ha⟩, h0⟩
    exact (gm_res q z (l₀ j₀) hy s).symm.trans ((congrArg (gm q z (W j₀)) (hs j₀)).trans (hu' Z' q z j₀ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, fun p p' => unit_ext fun y hy => ?_, fun Z q z J J₀ a ha hJ hJ₀ => ?_⟩
  · obtain ⟨⟨h1, ha⟩, h1', ha'⟩ := hy
    choose j₀ hj₀ using fun k => exists_chart hL₀ (φ₀ k y)
    have h0 : y ∈ LB.wchart L₀ φ₀ j₀ := Set.mem_iInter.2 hj₀
    have key : gm (𝟙 Y) y (LB.wchart M φ p.1 ⊓ A.U p.2) (s p.1 p.2) =
        (trF φ ε (𝟙 Y) y p.1 p'.1 * (gm (𝟙 Y) y (A.U p.2 ⊓ A.U p'.2) (A.g p.2 p'.2))⁻¹) *
          gm (𝟙 Y) y (LB.wchart M φ p'.1 ⊓ A.U p'.2) (s p'.1 p'.2) := by
      rw [hs p.1 p.2 Y (𝟙 Y) y j₀ h1 ha h0, hs p'.1 p'.2 Y (𝟙 Y) y j₀ h1' ha' h0,
        ev y p.1 p'.1 j₀ j₀ h1 h0 h1' h0, eu y j₀ j₀ p.2 p'.2 h0 ha h0 ha',
        GlobalTheory.LinCombComp.trF_self hL₀ φ₀ ε₀ (𝟙 Y) y j₀ h0]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel
    have hm : y ∈ (LB.div (LB.LinComb M φ ε) A).U p ⊓ (LB.div (LB.LinComb M φ ε) A).U p' :=
      ⟨⟨h1, ha⟩, h1', ha'⟩
    have ed := (GlobalTheory.LinCombComp.gm_div _ _ (𝟙 Y) y p p' hm.1 hm.2).trans
      (congrArg (· * _) (gm_linComb M φ ε (𝟙 Y) y p.1 p'.1 h1 h1'))
    exact (gm_res _ y _ hm _).trans (key.trans ((congrArg₂ (· * ·) ed.symm (gm_res _ y _ hm _).symm).trans
      (map_mul _ _ _).symm))
  · refine (hs _ a Z q z (fun k => J₀ (q ≫ φ₀ k)) (hJ.mem φ q) ha (hJ₀.mem φ₀ q)).trans
      ((mul_comm _ _).trans (congrArg _ ?_))
    have e : ∀ b b', b = b' → gm q z _ (v.s b) = gm q z _ (v.s b') := by rintro _ _ rfl; rfl
    exact e _ _ (Prod.ext (funext fun _ => funext fun k => by simp only [Category.id_comp]) rfl)

end GlobalTheory.IsoPullIdComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreimageOfLocalPreimagesInjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_preimage_of_local_preimages_injective : ∀ {X Y : Scheme.{0}} (a : Y ⟶ X), (∀ U : X.Opens, Function.Injective (a.app U).hom) → ∀ (V : X.Opens) {B : Type} (W : B → X.Opens), V ≤ ⨆ b, W b → ∀ (x : Γ(Y, a ⁻¹ᵁ V)), (∀ b, ∃ y : Γ(X, V ⊓ W b), (a.app (V ⊓ W b)).hom y = (Y.presheaf.map (homOfLE (extLI_preimage_mono a (inf_le_left : V ⊓ W b ≤ V))).op).hom x) → ∃ y : Γ(X, V), (a.app V).hom y = x := by
  first | exact @GlobalTheory.Mum.imgLoc_exists | exact GlobalTheory.Mum.imgLoc_exists | (intros; apply GlobalTheory.Mum.imgLoc_exists <;> assumption)
end

