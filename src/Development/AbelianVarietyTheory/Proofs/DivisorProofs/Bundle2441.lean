module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedBimultiplicativeGeneratorLambdaInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTrivialisationOfBalancedBimultiplicativ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2239
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2074
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2359
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelLevelStructureMumfordFamilyTautologi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem lbIso_pull_both {X X' Y Z : Scheme.{0}} {L : LB X} {M : LB X'} {a : Y ⟶ X} {b : Y ⟶ X'}
    (h : LBIso (L.pull a) (M.pull b)) (j : Z ⟶ Y) {a' : Z ⟶ X} {b' : Z ⟶ X'} (ea : a' = j ≫ a) (eb : b' = j ≫ b) :
    LBIso (L.pull a') (M.pull b') :=
  LBIso.chartPull (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => ea)
    (Geo.Tor.chartPullSame M _ (fun _ => b) _ j fun _ => eb) h

theorem isSquare_eq {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ φ' : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ' b) (e : φ = φ') : a = b := by
  subst e
  apply pullback.hom_ext
  · exact ha.1.trans hb.1.symm
  · exact ha.2.trans hb.2.symm


set_option backward.isDefEq.respectTransparency false in
theorem IsMumPol.exists_isMumfordFam {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {R : Type} [CommRing R]
    [IsDomain R] [IsLocalRing R] {Q : Data R} {G₁ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] {P : LB (G2 G₁).left}
    (h : IsMumPol Q G₁ P) {T : Scheme.{0}} {i : T ⟶ Sp R} {l : Sp (FractionRing R) ⟶ T} (hl : l ≫ i = jK R)
    {A₀ : Over T} [GrpObj A₀] [IsCommMonObj A₀] {P₀ : LB (G2 A₀).left} (hP₀ : P₀.IsLB)
    {a : A₀.left ⟶ G₁.left} {a₂ : (G2 A₀).left ⟶ (G2 G₁).left} (ha : IsGrpPullback A₀ G₁ i a) (ha₂ : IsSquare a a₂)
    (hPa : LBIso P₀ (P.pull a₂)) {yU : T ⟶ F.X} {φ : A₀.left ⟶ F.univ.A.left} {φ₂ : (G2 A₀).left ⟶ (G2 F.univ.A).left}
    (hφ : IsGrpPullback A₀ F.univ.A yU φ) (hφ₂ : IsSquare φ φ₂) (hPφ : LBIso P₀ (F.univ.P.pull φ₂)) :
    ∃ α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left, IsGenFibre F (l ≫ yU) α₁ ∧ IsMumfordFam F (l ≫ yU) α₁ Q := by
  obtain ⟨hR, hpos, -, hbi, hU⟩ := h
  have w : pullback.fst G₁.hom (jK R) ≫ G₁.hom = (pullback.snd G₁.hom (jK R) ≫ l) ≫ i := by
    rw [Category.assoc, hl, pullback.condition]
  obtain ⟨ω, ω₁, ω₂⟩ : ∃ ω : pullback G₁.hom (jK R) ⟶ A₀.left, ω ≫ a = pullback.fst G₁.hom (jK R) ∧
      ω ≫ A₀.hom = pullback.snd G₁.hom (jK R) ≫ l := ⟨ha.1.lift _ _ w, ha.1.lift_fst _ _ w, ha.1.lift_snd _ _ w⟩
  have h₁ := isGrpPullback_pullback G₁ (jK R)
  have hω : IsGrpPullback ((Over.pullback (jK R)).obj G₁) A₀ l ω := ha.cancel (h₁.congr hl.symm ω₁.symm) ω₂
  refine ⟨ω ≫ φ, hω.comp hφ, hR, hpos, fun R' _ _ _ ρ hR' hρ hf D ε hD => ?_⟩
  obtain ⟨G', _, _, π, π₂, A, U, hπ, hπ₂, hL⟩ := hU R' ρ hR' hρ hf D ε hD
  obtain ⟨κ, hκ⟩ := exists_genericMap hρ
  letI := A.isAb.comm
  have w' : (pullback.fst G'.hom (jK R') ≫ π) ≫ G₁.hom = (pullback.snd G'.hom (jK R') ≫ κ) ≫ jK R := by
    rw [Category.assoc, hπ.1.w, Category.assoc, hκ, pullback.condition_assoc]
  obtain ⟨πK, p₁, p₂⟩ : ∃ πK : pullback G'.hom (jK R') ⟶ pullback G₁.hom (jK R),
      πK ≫ pullback.fst G₁.hom (jK R) = pullback.fst G'.hom (jK R') ≫ π ∧
      πK ≫ pullback.snd G₁.hom (jK R) = pullback.snd G'.hom (jK R') ≫ κ :=
    ⟨pullback.lift _ _ w', pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have h₂ := isGrpPullback_pullback G' (jK R')
  have hπK : IsGrpPullback ((Over.pullback (jK R')).obj G') ((Over.pullback (jK R)).obj G₁) κ πK :=
    h₁.cancel ((h₂.comp hπ).congr hκ.symm p₁.symm) p₂
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have hi := isGrpPullback_of_iso U.gen.symm
  have e₁ : U.gen.hom.left ≫ U.gen.symm.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.symm_hom, U.gen.hom_inv_id, Over.id_left]
  have e₂ : U.gen.symm.hom.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.symm_hom, U.gen.inv_hom_id, Over.id_left]
  have hβ := hi.comp (hπK.comp hω)
  have hδ := hi.comp h₂
  obtain ⟨β₂, hβ₂⟩ : ∃ β₂, IsSquare _ β₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hβ.1.w⟩
  obtain ⟨δ₂, hδ₂⟩ : ∃ δ₂, IsSquare _ δ₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hδ.1.w⟩
  have r : LBIso A.L (U.LG.L.pull (U.gen.symm.hom.left ≫ pullback.fst G'.hom (jK R'))) :=
    LBIso.trans A.isLB (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _)
      (LBIso.chartPull (chartPullId A.L) (Geo.Tor.chartPullPull A.L (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl A.isLB))
      (lbIso_pull_both U.ext U.gen.symm.hom.left e₂.symm rfl)
  have l₁ := GlobalTheory.LamPull.lbIso_lam_pull hδ U.LG.isLB A.isLB r hδ₂
  have i₁ : (abelian₂ G' U.LG.L).IsLB := DVR.linComb_isLB _ U.LG.isLB _ _
  have i₀ : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have e₃ : β₂ ≫ a₂ = δ₂ ≫ π₂ := isSquare_eq (isSquare_comp hβ₂ ha₂) (isSquare_comp hδ₂ hπ₂) (by
    simp only [Category.assoc]
    rw [ω₁, p₁])
  have l₂ := lbIso_pull_comp hL δ₂ e₃
  have l₃ := (lbIso_pull_comp hPa β₂ rfl).symm
  have l₄ := lbIso_pull_comp hPφ β₂ rfl
  refine ⟨G', inferInstance, inferInstance, π, A, U, hπ, κ, πK, (U.gen.symm.hom.left ≫ πK ≫ ω) ≫ φ, β₂ ≫ φ₂, hκ, p₁,
    (hβ.comp hφ).congr (by simp only [Category.id_comp, Category.assoc]) rfl, isSquare_comp hβ₂ hφ₂,
    LBIso.trans i₀ (pull_isLB i₁ _) (pull_isLB F.univ.isLB _) l₁
      (LBIso.trans (pull_isLB i₁ _) (pull_isLB hbi.1 _) (pull_isLB F.univ.isLB _) l₂
        (LBIso.trans (pull_isLB hbi.1 _) (pull_isLB hP₀ _) (pull_isLB F.univ.isLB _) l₃ l₄)), ?_⟩
  simp only [Category.assoc]
  rw [← Category.assoc, e₁, Category.id_comp]

theorem dense_generic_away {o R : Type} [CommRing o] [CommRing R] [IsDomain R] {b : o →+* R} (hb : Function.Injective b)
    {f : R} (hf : f ≠ 0) :
    Dense {x : Sp (Localization.Away f) | (spMap ((algebraMap R (Localization.Away f)).comp b) x).asIdeal = ⊥} := by
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have hinj : Function.Injective ((algebraMap R (Localization.Away f)).comp b) :=
    (IsLocalization.injective (Localization.Away f) hle).comp hb
  let p : PrimeSpectrum (Localization.Away f) := ⟨⊥, Ideal.isPrime_bot⟩
  have hp : Dense ({p} : Set (PrimeSpectrum (Localization.Away f))) := by
    rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
    simp [p]
  refine Dense.mono ?_ hp
  rintro x rfl
  exact (RingHom.injective_iff_ker_eq_bot _).1 hinj


set_option backward.isDefEq.respectTransparency false in
theorem Taut.exists_isFam_of_siegPre : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → ∀ c : SiegPre g n (zetaAway n) (spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b)), c.Principal → (∃ (a : c.A.left ⟶ G₁.left) (a₂ : (G2 c.A).left ⟶ (G2 G₁).left), IsGrpPullback c.A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂)) → ∃ (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (yU : Sp (Localization.Away (∏ k, C.t k)) ⟶ F.X) (l : Localization.Away (∏ k, C.t k) →+* FractionRing C.R), C.IsFam F G₁ y α₁ ∧ SiegPB c F.univ yU ∧ l.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))) = algebraMap C.R (FractionRing C.R) ∧ y = spMap l ≫ yU := by
  intro g n φ hn _ F C G₁ _ _ P hM hab c hc ⟨a, a₂, ha, ha₂, hPa⟩
  obtain ⟨-, -, hinj, -, hrel, -⟩ := Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  have hf : ∏ k, C.t k ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ne_zero_of_isRelParam hrel i
  haveI : IsDomain (Localization.Away (∏ k, C.t k)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  obtain ⟨yU, hs, hPB⟩ := F.rep _ _ c inferInstance (dense_generic_away hinj hf) hc
  have hu : IsUnit (algebraMap C.R (FractionRing C.R) (∏ k, C.t k)) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective C.R _)).2 hf)
  let l : Localization.Away (∏ k, C.t k) →+* FractionRing C.R := IsLocalization.Away.lift _ hu
  have hl : l.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))) = algebraMap C.R (FractionRing C.R) :=
    IsLocalization.Away.lift_comp _ hu
  have hl' : spMap l ≫ spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) = jK C.R := by
    rw [← Geo.Tor.spMap_comp, hl]
  obtain ⟨ψ, ψ₂, h₁, h₂, h₃, h₄⟩ := hPB
  obtain ⟨α₁, hα, hF⟩ := hM.exists_isMumfordFam F hl' c.isLB ha ha₂ hPa h₁ h₂ h₃
  refine ⟨spMap l ≫ yU, α₁, yU, l, ⟨hM.2.2.1, hab, hα, hF, ?_⟩, ⟨ψ, ψ₂, h₁, h₂, h₃, h₄⟩, hl, rfl⟩
  rw [Category.assoc, hs, Geo.Tor.spMap_comp, ← Category.assoc, hl']

end GlobalTheory.TChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

def TwistSum (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam)
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ) {C : Type} (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V)
    (sg : ℤˣ) (c : C) (τ : X₁.S.Gam) (e : ℕ) : Prop :=
  ∀ zt h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) →
    X₁.M.stalkHom z₁ h = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) * X₁.S.th (lab c + τ) / X₁.S.th x₀ →
    ∀ wt : (Fin 8 → X) → ZMod (X₁.S.r * X₁.S.N), (∀ a mu, 𝔪.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a) →
      SumI (maximalIdeal V) (fun mu => ev zt ^ (wt mu).val * T mu c) (ev h)

def TwistAtEach (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam)
    (sg : ℤˣ) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
    (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type)
    (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T →
    ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ e : ℕ, TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e

theorem exists_stalk_zeta (X₁ : Setup F W i) (z₁ : X₁.M.Z) (a : X₁.o₁) :
    ∃ s : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ a := by
  obtain ⟨s, hs⟩ := (X₁.M.stalkEquiv z₁).surjective ⟨algebraMap X₁.o₁ X₁.Ω₁ a, Subalgebra.algebraMap_mem _ a⟩
  exact ⟨s, by rw [← RatModel.coe_stalkEquiv, hs]⟩

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricBalancedGeneratorPsiZeroLocalRing
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UTau0

theorem exists_symmetric_balanced_generator_psi_zero_localRing : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ : DegPre R) (O : Type) [CommRing O]
    [StarRing O] [Module O D₀.X] [Module.Projective O D₀.X] [Module.Finite O D₀.X] (onB : D₀.P.OAct O),
    (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) → ∀ w0 : O, w0 + star w0 = 1 →
    (∃ u : LB.Gen (LB.LinComb D₀.P.L (K := Fin 4) ![(padd D₀.P.A (𝟙 _) (onB.act w0)).left, 𝟙 D₀.P.A.left,
        (onB.act w0).left, (toUnit D₀.P.A ≫ η[D₀.P.A]).left] ![1, -2, -1, 2]),
      u.IsGen ∧ LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (eSec D₀.P.A)) (LB.oneGen D₀.P.L)) →
    ∃ (ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => ptK (D₀.c y)) (fun _ => -1)))
      (h : ∀ y, (ψ y).IsGen),
      letI : Module O ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).X := ‹Module O D₀.X›
      ∃ oa : ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).OAct O, oa.onB = onB ∧
        ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).PsiEven ∧
        ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).TauBimult ∧
        TraceFormTwistIso ({ D₀ with psi := ψ, psi_gen := h } : DegPre R) oa w0 ∧
        ∀ y, PsiUnitOn ({ D₀ with psi := ψ, psi_gen := h } : DegPre R) y Set.univ := by
  intro R _ _ _ D₀ O _ _ _ _ _ onB hlin w0 hw ⟨uw, huw, huw0⟩
  have cadd : ∀ y y' : D₀.X, D₀.c (y + y') = D₀.c y * D₀.c y' := fun y y' => D₀.c_add y y'
  obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.UBalA.exists_balTau R D₀.P.A D₀.P.isAb ⟨D₀.P.L, D₀.rig, D₀.P.isLB, D₀.rig_gen⟩ D₀.cub O onB.toRingAct
    onB.rosati D₀.X D₀.c cadd hlin
  obtain ⟨τ', hτ', hτs⟩ := _root_.GlobalTheory.SymTau.symm_of_bal R D₀.P.A D₀.P.isAb ⟨D₀.P.L, D₀.rig, D₀.P.isLB, D₀.rig_gen⟩ D₀.cub O
    onB.toRingAct onB.rosati D₀.X D₀.c cadd hlin w0 hw τ hτ
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_psi_generators_degenerationLaws_symmetricBalanced R D₀ O onB hlin w0 hw uw huw huw0 τ' hτ' hτs
  obtain ⟨h, rest⟩ := GlobalTheory.T.degenerationPreData_laws_of_generator_values R D₀ O onB hlin w0 uw huw huw0 ψ hψ
  exact ⟨_, h, rest⟩

end GlobalTheory.UTau0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricPolarisationFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg.SymPol

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem inv_comm (h : IsGrpPullback G' G f φ) : (ι[G']).left ≫ φ = φ ≫ (ι[G]).left := by
  have e := congrArg (fun z => z.left) (map_inv (pushHom h G') (𝟙 G'))
  rw [Hom.inv_def, Hom.inv_def, Category.id_comp] at e
  refine Eq.trans e ?_
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem exists_half (h : IsGrpPullback G' G f φ) (a : 𝟙_ (Over S) ⟶ G) (b : Over.mk f ⟶ G) (hb : b ^ 2 = toUnit _ ≫ a) :
    ∃ b' : 𝟙_ (Over S') ⟶ G',
      ((toUnit G' ≫ b' ^ 2) * 𝟙 G').left ≫ φ = φ ≫ ((toUnit G ≫ a) * 𝟙 G).left := by
  have w : b.left ≫ G.hom = 𝟙 S' ≫ f := (Over.w b).trans (Category.id_comp _).symm
  let b' : 𝟙_ (Over S') ⟶ G' := Over.homMk (h.1.lift _ _ w) (h.1.lift_snd _ _ _)
  have hb' : b'.left ≫ φ = b.left := h.1.lift_fst _ _ _
  let j : Over.mk (G'.hom ≫ f) ⟶ Over.mk f := Over.homMk G'.hom rfl
  have hu : (toUnit G').left = G'.hom := (Category.comp_id _).symm.trans (Over.w (toUnit G'))
  have e₁ : pushHom h G' (toUnit G' ≫ b') = j ≫ b := Over.OverMorphism.ext (by
    show ((toUnit G').left ≫ b'.left) ≫ φ = G'.hom ≫ b.left
    rw [Category.assoc, hb', hu])
  have e₂ : pushHom h G' ((toUnit G' ≫ b' ^ 2) * 𝟙 G') = pushHom h G' (𝟙 G') ≫ ((toUnit G ≫ a) * 𝟙 G) := by
    rw [map_mul, MonObj.comp_pow, map_pow, e₁, ← MonObj.comp_pow, hb, MonObj.comp_mul, Category.comp_id,
      ← Category.assoc, ← Category.assoc, toUnit_unique (j ≫ toUnit _) (pushHom h G' (𝟙 G') ≫ toUnit G)]
  refine ⟨b', (congrArg (fun z => z.left) e₂).trans ?_⟩
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem exists_gen_theta_pull [IsCommMonObj G] [IsCommMonObj G'] (h : IsGrpPullback G' G f φ) {L : LB G.left}
    (ht : ∃ t : LB.Gen (Theta G L), t.IsGen) : ∃ t : LB.Gen (Theta G' (L.pull φ)), t.IsGen := by
  obtain ⟨t, ht⟩ := ht
  exact gen_chartPull (chartPullLinComb L φ _ _ _ (cubeMapOf h).F3 fun I => (cubeMapOf h).psum_comm I.down) t ht

end GlobalTheory.PolDeg.SymPol


open GlobalTheory.PolDeg.SymPol GlobalTheory.CechPic in
theorem GlobalTheory.PolDeg.exists_symmetric_pol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R), IsCN R → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ IsGrpPullback P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) := by
  intro R _ _ _ Q hR
  haveI := hR.1
  have hM := Q.M.isLB
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  obtain ⟨a, ha⟩ := GlobalTheory.T.primitive_bundle_eq_translate_ample_noetherian_local R Q.B Q.g Q.M.L _ Q.isAb Q.smoothDim hM Q.ample Q.ktriv hΘ
    (LB.isLB_linComb hM _ _) (GlobalTheory.T.exists_generator_mumfordBundle_inv_pullback_primitive R Q.B Q.M Q.cub Q.isAb)
  have ea := (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb hM _ _)).2 ha
  rw [cls_linComb hM, cls_linComb hM, Fin.sum_univ_two, Fin.sum_univ_two] at ea
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, add_left_inj] at ea
  obtain ⟨R', _, _, _, ρ, b, hR', hinj, hfin, hloc, hb⟩ := _root_.GlobalTheory.HalfPt.exists_half_point R Q.B a hR Q.isAb
  haveI := hR'.1
  have h := isGrpPullback_pullback Q.B (spMap ρ)
  have hA : IsAbelianScheme ((Over.pullback (spMap ρ)).obj Q.B) := by
    have := Q.isAb.comm
    have hc : IsCommMonObj ((Over.pullback (spMap ρ)).obj Q.B) := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) h.1 Q.isAb.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 Q.isAb.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 Q.isAb.geomConnected⟩
  haveI := hA.comm
  obtain ⟨b', hb'⟩ := exists_half h a b hb
  have hM' := pull_isLB hM (pullback.fst Q.B.hom (spMap ρ))
  have hid := (cls_eq_iff hM' hM').1 rfl
  obtain ⟨w, hw⟩ := id hid
  obtain ⟨L, hL, hrig, hsym, hamp, hK, hΛ⟩ := _root_.GlobalTheory.SymTranslate.exists_sym_translate R' _ _ b' hA hM'
    (relAmple_pull h.1 hM hM' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) Q.ample)
    (kTriv_pull h hM hM' ((isGen_iff w).1 hw) Q.ktriv) (exists_gen_theta_pull h hΘ)
    ((cls_eq_iff (pull_isLB hM' _) (pull_isLB hM' _)).1 (by
      rw [cls_pull hM', cls_pull hM', cls_pull hM, ← pull_comp, ← pull_comp, inv_comm h, hb', pull_comp, pull_comp, ea]))
  obtain ⟨β₂, hβ₂⟩ := SiegPull.exists_isSquare h.1.w
  exact ⟨R', _, _, _, ρ,
    { A := (Over.pullback (spMap ρ)).obj Q.B, isAb := hA, g := Q.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 Q.smoothDim
      L := L, isLB := hL, rigid := hrig, sym := hsym, ample := hamp, ktriv := hK }, _, β₂, hR', hinj, hfin, hloc, h, hβ₂,
    LBIso.trans (LB.isLB_linComb hL _ _) (LB.isLB_linComb hM' _ _) (pull_isLB (LB.isLB_linComb hM _ _) _) hΛ
      (SiegPull.lbIso_lam_pull h hid hβ₂)⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAfterFiniteExtensionBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLevel_after_finiteExtension_base : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))), (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → ∀ m : ℕ, 1 ≤ m → IsUnit (m : R) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left) (ζ : R₁ˣ) (_ : ReciprocityTheory.ChartRestriction.G.Out.Level A₁ m (unitOn (Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ))), FinExt ρ ∧ IsFib ρ A A₁ a ∧ A₁.g = A.g ∧ (letI := A₁.isAb.comm; GlobalTheory.ZH.HypS A₁.A A₁.L) := by
  first | exact @GlobalTheory.MumLevel.exists_level_finExt | exact GlobalTheory.MumLevel.exists_level_finExt | (intros; apply GlobalTheory.MumLevel.exists_level_finExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTrivialisationPowerLatticePoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.tensPsi_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (A' : Over (Spec (CommRingCat.of R))) [GrpObj A'] (L' : LB A'.left), L'.IsLB → ∀ (pr : Fin r → (A' ⟶ D.P.A)) (w : LB.Iso L' (LB.LinComb D.P.L (tensφ pr) (tensε W))), w.IsGen → ∀ (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A') (y : Fin r → D.X), (∀ i, x ≫ pr i = D.c (y i)) → ∃ ψ : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => ptK x) (fun _ => -1)), ψ.IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ A'.left) → L'.ι), Good D.P.L z J → Good L' z J' → val ψ (𝟙 _) z J' = gm (ptK x) z _ (w.s (fun k => J (ptK x ≫ tensφ pr k), J' (ptK x))) * ∏ i, ∏ j, val (D.tau (y i) (y j)) (𝟙 _) z J ^ W i j := by
  intro R _ _ D r W A' _ L' hL pr w hw x y hx
  exact GlobalTheory.Mum.TraitWit.exists_psi D W hL pr hw (toUnit (TK R) ≫ x) y (fun i => by rw [Category.assoc, hx])
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTermNonzeroClosed
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_term_nonzero_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (Y : Ext D.toPre), ∃ (b : D.toPre.SecB 1 0) (τ : SecK D.toPre.P.L Y.q.left 1)
      (y : Y.H.left), IsTermOf Y b τ ∧ Y.H.hom y = closedPoint R ∧ y ∈ nonzeroLocus τ := by
  intro R _ _ _ hB D Y
  haveI : IsNoetherianRing R := hB.1.1
  obtain ⟨-, -, hsurj, -, hterm⟩ := _root_.GlobalTheory.Mum.ext_smooth_affine_surj_terms R D.toPre Y
  obtain ⟨th, x, hx, hn⟩ :=
    GlobalTheory.ThetaSectionTest.exists_nonzero_closed GlobalTheory.abelianSchemeLaws_all.1.secBaseChange D.toPre
  obtain ⟨τ, hτ⟩ := hterm 1 0 th
  obtain ⟨y, rfl⟩ := Y.q.left.surjective x
  refine ⟨th, τ, y, hτ, ?_, ?_⟩
  · rw [← hx, ← Scheme.Hom.comp_apply, Over.w]
  · obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' D.toPre.P.isLB y
    have e := hτ Y.H (𝟙 _) y J hJ
    have hu : IsUnit (sval th (𝟙 Y.H ≫ Y.q).left y J) := by
      rw [Category.id_comp]
      exact GlobalTheory.ThetaUnit.isUnit_sval th _ y hn hJ
    have hτu : IsUnit (sval τ (𝟙 Y.H : Y.H ⟶ Y.H).left y J) := by
      rw [e]; exact hu.mul (Units.isUnit _)
    rw [Over.id_left] at hτu
    exact (GlobalTheory.SectionBaseChange.mem_nonzeroLocus τ _).2
      ⟨_, hJ.mem (fun _ : Fin 1 => Y.q.left) (𝟙 Y.H.left),
        (GlobalTheory.ThetaUnit.isUnit_gs_iff _ y _ (hJ.mem (fun _ : Fin 1 => Y.q.left) (𝟙 Y.H.left)) _).1 hτu⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantMSqTorsionAlgClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin

theorem exists_thG_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (θ : SecAt G L x) (p : Over.mk x ⟶ G), Odd m → (m : K) ≠ 0 → PolFib G L g x → p ^ (m ^ 2) = 1 → ∃ c : K, ThG G L ρ m θ p (GlobalTheory.ZH.fn c) := by
  intro S G _ _ L ρ hL hρ g m K _ _ x θ p hm hK hP hpm
  obtain ⟨P, α, -, hp, w, hw⟩ := hP
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ρ', hρ', hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk x).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk x).hom = (baseOver (Sp K)).hom ≫ x := rfl
  have hi : inv τ = 𝟙 (Sp K) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨q, hq, hqm⟩ := exists_torsion_down hp τ hτ p hpm
  obtain ⟨v, hv⟩ := ThetaPtExist.exists_isThetaPt hLaw K P m hm hK (fun _ : Unit => q) (fun _ => hqm)
  let c' : K := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (v ())
  have hvc : v = fun _ => GlobalTheory.Ex.fnOf c' := funext fun u =>
    ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply (v u)).symm
  rw [hvc] at hv
  obtain ⟨thP, hg, hth⟩ := exists_gen_thG_of_isThetaPt K P ρ' hρ' m Unit (fun _ => q) (fun _ => c') (fun _ => hqm) hv
  obtain ⟨th, hrel⟩ := GlobalTheory.ThetaPtMove.exists_secRel_up hp τ hτ hw hL hL₁ thP
  have hgen := ThetaPtUp.isGenSec_up hp τ hτ hw hL hL₁ hrel hg
  have up := ThG.up hp τ hτ hw hL hL₁ hr hq hpm hrel (hth ())
  rw [hi] at up
  obtain ⟨r, hr'⟩ := hgen θ
  have e₁ : SecM.ofSec G θ = r • SecM.ofSec G th := Subtype.ext (funext hr')
  have q' := ThG.smul hL e₁ up
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (show Γ(Sp K, ⊤) from r) * c', ?_⟩
  convert q' using 1
  simp [GlobalTheory.ZH.fn, GlobalTheory.Ex.fnOf, c']

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThickenedGroupEndomorphismTorusCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thickenedGroup_endomorphism_torusCoordinates : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X), (∀ χ, D.c (h' χ) = D.c χ ≫ a') → ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) → ∃ F, IsCoordEnd g a a' h' u F := by
  first | exact @GlobalTheory.Mum.EndThick.exists_isCoordEnd | exact GlobalTheory.Mum.EndThick.exists_isCoordEnd | (intros; apply GlobalTheory.Mum.EndThick.exists_isCoordEnd <;> assumption)
end

