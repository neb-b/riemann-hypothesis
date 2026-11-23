module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2245
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPresentationsSamePolarisationLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.LowSame

open GlobalTheory.SiegLev GlobalTheory.CechPic GlobalTheory.AmpleRigid GlobalTheory.SiegRigid

theorem eq_of_cls_lev {h n : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B}
    (c : SiegPre h n ζ s) (hζ : IsUnit ζ) (hnB : IsUnit (n : B)) (hn : 3 ≤ n) (hc : c.Principal)
    {A' : Over S'} [GrpObj A'] (hab' : IsAbelianScheme A') (f : S' ⟶ S) (φ φ' : A'.left ⟶ c.A.left)
    (g : IsGrpPullback A' c.A f φ) (g' : IsGrpPullback A' c.A f φ')
    (hcl : pull φ (cls c.diag (pull_isLB c.isLB _)) = pull φ' (cls c.diag (pull_isLB c.isLB _)))
    (lv : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ A'))
    (l : ∀ a, (lv a).left ≫ φ = f ≫ (c.lev a).left) (l' : ∀ a, (lv a).left ≫ φ' = f ≫ (c.lev a).left) :
    φ = φ' := by
  obtain ⟨σ, hσ, e⟩ := exists_aut g g'
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 A' hab' σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫ S'.fromSpecResidueField t
    have hp := isGrpPullback_pullback A' j
    have := hab'.smooth
    have := hab'.proper
    have := hab'.geomConnected
    have := hab'.comm
    have hab : IsAbelianScheme ((Over.pullback j).obj A') :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd A'.hom j); infer_instance
        proper := by change IsProper (pullback.snd A'.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd A'.hom j); infer_instance }
    have hNK : (n : K) ≠ 0 := by
      have hu := hnB.map (Spec.preimage ((j ≫ f) ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have e' := eq_of_field (pull_isLB c.isLB _) hc.1 hab (hp.comp g) (hp.comp g')
      (by rw [pull_comp, pull_comp]; exact congrArg _ hcl) hn hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ n = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion hζ c g lv l l' Ω (x ≫ j) _ hy₁
        rw [← Category.assoc, ← Category.assoc]
        exact e₁
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · apply g'.1.hom_ext
      · rw [Category.assoc, e]
        exact e'
      · rw [Category.assoc, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

end GlobalTheory.LowSame

namespace GlobalTheory.LowSame

open GlobalTheory.SiegelPullComp

theorem eq_of_presentations : ∀ {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F' : SFam h n ζ), 3 ≤ n → IsUnit ζ → IsUnit (n : o) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (A : Over (Sp V)) [GrpObj A] [IsCommMonObj A] (t₁ t₂ : Sp V ⟶ F'.X) (a₁ a₂ : A.left ⟶ F'.univ.A.left) (aa₁ aa₂ : (G2 A).left ⟶ (G2 F'.univ.A).left), IsGrpPullback A F'.univ.A t₁ a₁ → IsGrpPullback A F'.univ.A t₂ a₂ → IsSquare a₁ aa₁ → IsSquare a₂ aa₂ → LBIso (F'.univ.P.pull aa₁) (F'.univ.P.pull aa₂) → t₁ ≫ F'.s = t₂ ≫ F'.s → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F], (∀ l, ∃ x : TF (R := V) F ⟶ A, x.left ≫ a₁ = (TF (R := V) F).hom ≫ t₁ ≫ (F'.univ.lev l).left ∧ x.left ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (F'.univ.lev l).left) → t₁ = t₂ ∧ a₁ = a₂ := by
  intro o _ ζ h n F' hn hζ hno V _ _ _ A _ _ t₁ t₂ a₁ a₂ aa₁ aa₂ ha₁ ha₂ sq₁ sq₂ hP hs F _ _ hlev
  let c' := GlobalTheory.LowChart.siegPull F'.univ t₁ (t₁ ≫ F'.s) rfl
  have m₁ : SiegPB c' F'.univ t₁ := GlobalTheory.LowChart.siegPB_siegPull _ _ _ _
  obtain ⟨pφ, pφ₂, gp, psq, pw, pl⟩ := id m₁
  let F₀ : c'.A.left ⟶ A.left := ha₁.1.lift pφ c'.A.hom gp.1.w
  have hF : F₀ ≫ a₁ = pφ := ha₁.1.lift_fst _ _ _
  have hFw : F₀ ≫ A.hom = c'.A.hom ≫ 𝟙 _ := (ha₁.1.lift_snd _ _ _).trans (Category.comp_id _).symm
  have hF₀ : IsGrpPullback c'.A A (𝟙 _) F₀ :=
    ha₁.cancel (gp.congr (Category.id_comp _).symm hF.symm) hFw
  have gφ : IsGrpPullback c'.A F'.univ.A t₂ (F₀ ≫ a₂) := (hF₀.comp ha₂).congr (Category.id_comp _) rfl
  let U : Over.mk ((c'.A ⊗ c'.A).hom ≫ 𝟙 _) ⟶ A ⊗ A :=
    lift (pushPt hFw (fst c'.A c'.A)) (pushPt hFw (snd c'.A c'.A))
  let F₂ : (c'.A ⊗ c'.A).left ⟶ (A ⊗ A).left := U.left
  have h₁ : F₂ ≫ (fst A A).left = (fst c'.A c'.A).left ≫ F₀ :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c'.A c'.A)) (pushPt hFw (snd c'.A c'.A)))
  have h₂ : F₂ ≫ (snd A A).left = (snd c'.A c'.A).left ≫ F₀ :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c'.A c'.A)) (pushPt hFw (snd c'.A c'.A)))
  have h₃ : F₂ ≫ aa₁ = pφ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst F'.univ.A F'.univ.A).left = _ ≫ (fst F'.univ.A F'.univ.A).left
      rw [Category.assoc, sq₁.1, ← Category.assoc, h₁, Category.assoc, hF, psq.1]
    · show (_ ≫ _) ≫ (snd F'.univ.A F'.univ.A).left = _ ≫ (snd F'.univ.A F'.univ.A).left
      rw [Category.assoc, sq₁.2, ← Category.assoc, h₂, Category.assoc, hF, psq.2]
  have sq : IsSquare (F₀ ≫ a₂) (F₂ ≫ aa₂) :=
    ⟨by rw [Category.assoc, sq₂.1, ← Category.assoc, h₁, Category.assoc],
     by rw [Category.assoc, sq₂.2, ← Category.assoc, h₂, Category.assoc]⟩
  have hU := F'.univ.isLB
  have iso : LBIso c'.P (F'.univ.P.pull (F₂ ≫ aa₂)) := by
    rw [← h₃] at pw
    refine pw.trans c'.isLB (pull_isLB hU _) (pull_isLB hU _) ?_
    refine (iso_pull_pull hU aa₁ F₂).symm.trans (pull_isLB hU _) (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) ?_
    refine (iso_pull F₂ hP).trans (pull_isLB (pull_isLB hU _) _) (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) ?_
    exact iso_pull_pull hU aa₂ F₂
  have lev : ∀ a, (c'.lev a).left ≫ (F₀ ≫ a₂) = t₂ ≫ (F'.univ.lev a).left := by
    intro a
    have hσ : ((c'.lev a).left ≫ F₀) ≫ A.hom = 𝟙 _ := by
      rw [Category.assoc, hFw, Category.comp_id]
      exact Over.w (c'.lev a)
    have hσ₁ : ((c'.lev a).left ≫ F₀) ≫ a₁ = t₁ ≫ (F'.univ.lev a).left := by
      rw [Category.assoc, hF]; exact pl a
    obtain ⟨x, hx₁, hx₂⟩ := hlev a
    have hx : x.left = (TF (R := V) F).hom ≫ (c'.lev a).left ≫ F₀ := by
      apply ha₁.1.hom_ext
      · rw [hx₁, Category.assoc, hσ₁]
      · rw [Over.w x, Category.assoc, hσ]
        exact (Category.comp_id _).symm
    have := F'.univ.ab.proper
    have : IsReduced (𝟙_ (Over (Sp V))).left := (inferInstance : IsReduced (Sp V))
    have := ReciprocityTheory.ChartRestriction.G.DVR.GC.isDominant_jFR (V := V) F
    refine ext_of_isDominant_of_isSeparated F'.univ.A.hom ?_ (DegPre.jFR (R := V) F) ?_
    · rw [Category.assoc, Category.assoc, ha₂.1.w, ← Category.assoc, ← Category.assoc, hσ, Category.id_comp,
        Category.assoc, Over.w (F'.univ.lev a)]
      rfl
    · rw [← Category.assoc]
      show ((TF (R := V) F).hom ≫ (c'.lev a).left ≫ F₀) ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (F'.univ.lev a).left
      rw [← hx]
      exact hx₂
  have m₂ : SiegPB c' F'.univ t₂ := ⟨F₀ ≫ a₂, F₂ ≫ aa₂, gφ, sq, iso, lev⟩
  have ht : t₁ = t₂ := F'.inj V t₁ t₂ (t₁ ≫ F'.s) c' hs m₁ m₂
  subst ht
  refine ⟨rfl, ?_⟩
  have hcl := (GlobalTheory.SiegRigid.pull_cls_diag psq pw).trans (GlobalTheory.SiegRigid.pull_cls_diag sq iso).symm
  have e := eq_of_cls_lev F'.univ hζ hno hn F'.princ c'.ab t₁ pφ (F₀ ≫ a₂) gp gφ hcl c'.lev pl lev
  have : IsIso F₀ := hF₀.1.isIso_fst_of_isIso
  rw [← hF] at e
  exact (cancel_epi F₀).1 e

end GlobalTheory.LowSame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSameGenericProjectiveCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegCrd

theorem eq_of_generic_pCrd : ∀ (o : Type) [CommRing o] (n : ℕ) (X : Scheme.{0}) [IsIntegral X] [IsReduced X] (s : X ⟶ Sp o) (h h' : X ⟶ PSpace o n) (K : Type) [Field K] (x : Sp K ⟶ X) (c : Fin (n + 1) → K), h ≫ PSpace.str o n = s → h' ≫ PSpace.str o n = s → Set.range x = {genericPoint X} → PCrd (x ≫ h) c → PCrd (x ≫ h') c → h = h' := by
  intro o _ n X _ _ s h h' K _ x c hs hs' hx hc hc'
  have : IsSeparated (PSpace.str o n) := by
    have := isProper_str o n
    infer_instance
  have hd : IsDominant x := by
    refine ⟨?_⟩
    change Dense (Set.range x.base)
    have e : Set.range x.base = {genericPoint X} := hx
    rw [e, dense_iff_closure_eq]
    exact genericPoint_closure X
  have he : x ≫ h = x ≫ h' :=
    CrdUniq.eq_of_pCrd (by rw [Category.assoc, Category.assoc, hs, hs']) hc hc'
  exact ext_of_isDominant_of_isSeparated (PSpace.str o n) (hs.trans hs'.symm) x he

end GlobalTheory.SiegCrd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfTorusHomOfZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

section SlopeTestRemainingChoices

variable {S T : Scheme.{0}} (f : T ⟶ S)

theorem pullback_prod_hom_ext {X Y : Over S} {W : Over T}
    {u v : W ⟶ (Over.pullback f).obj (X ⊗ Y)}
    (h₁ : u ≫ (Over.pullback f).map (fst X Y) = v ≫ (Over.pullback f).map (fst X Y))
    (h₂ : u ≫ (Over.pullback f).map (snd X Y) = v ≫ (Over.pullback f).map (snd X Y)) : u = v :=
  BinaryFan.IsLimit.hom_ext ((isLimitMapConeBinaryFanEquiv (Over.pullback f) _ _)
    (isLimitOfPreserves (Over.pullback f) (tensorProductIsBinaryProduct X Y))) h₁ h₂

theorem pullback_map_one {X G : Over S} [MonObj G] :
    (Over.pullback f).map (1 : X ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, Functor.map_comp]
  change _ = toUnit _ ≫ Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map η[G]
  rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (Functor.OplaxMonoidal.η (Over.pullback f))]
  exact toUnit_unique _ _

end SlopeTestRemainingChoices

end GlobalTheory.MumProd

namespace GlobalTheory.MumProd

section Torus

variable {S : Scheme.{0}} {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂]

theorem torusHomOf_iff_appTop' (h : X₂ → X₁) (t : splitTorus S X₁ ⟶ splitTorus S X₂) : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X₂ χ).val = (charUnit S X₁ (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X₂ χ)) : Γ((splitTorus S X₁).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X₂ χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem torusHomOf_unique {h : X₂ → X₁} {t t' : splitTorus S X₁ ⟶ splitTorus S X₂}
    (ht : TorusHomOf h t) (ht' : TorusHomOf h t') : t = t' := by
  refine (GlobalTheory.splitTorusPointsEquiv S X₂ _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.splitTorusPointsEquiv_val, (torusHomOf_iff_appTop' _ _).1 ht,
    (torusHomOf_iff_appTop' _ _).1 ht']

theorem eq_one_of_torusHomOf_zero {t : splitTorus S X₁ ⟶ splitTorus S X₂}
    (ht : TorusHomOf (fun _ => (0 : X₁)) t) : t = 1 := by
  refine (GlobalTheory.splitTorusPointsEquiv S X₂ _).injective ?_
  rw [map_one]
  refine MonoidHom.ext fun χ => Units.ext ?_
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  have k : ∀ χ : X₂, (GlobalTheory.splitTorusPointsEquiv S X₂ _ t (Multiplicative.ofAdd χ)).val =
      (charUnit S X₁ 0).val := fun χ => by
    rw [GlobalTheory.splitTorusPointsEquiv_val, (torusHomOf_iff_appTop' _ _).1 ht]
  rw [k χ, ← k 0, ofAdd_zero, map_one]
  rfl

theorem torusHomOf_torusMap (q : X₂ →+ X₁) : TorusHomOf q (GlobalTheory.SplitTorusPow.torusMap S q) :=
  (torusHomOf_iff_appTop' _ _).2 fun χ => GlobalTheory.SplitTorusPow.torusMap_char q χ

end Torus

end GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem IsProdUnif.linHom_inl : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → ∀ (i₁ : D₁.toPre.P.A ⟶ D.toPre.P.A), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.toPre.P.A] → LinHom U₁ U i₁ q₁ (lift (𝟙 G₁) 1) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hD hU i₁ hi₁ hi₂
  have h1 : IsMonHom (1 : G₁ ⟶ G₂) := inferInstanceAs (IsMonHom (toUnit G₁ ≫ η[G₂]))
  have hi₂' : i₁ ≫ p₂ = 1 := hi₂.trans Hom.one_def.symm
  have hlim := hD.lim
  refine ⟨inferInstance, fun e => ?_, fun e => ?_⟩
  ·
    have := (U₂.gt e).q_hom
    rw [← cancel_mono ((Over.pullback (thick R I e)).map (lift p₁ p₂))]
    refine pullback_prod_hom_ext _ ?_ ?_
    · simp only [Category.assoc, ← Functor.map_comp, lift_fst]
      rw [hU.q_pr₁ e, ← Category.assoc, ← Functor.map_comp, lift_fst, hi₁, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    · simp only [Category.assoc, ← Functor.map_comp, lift_snd]
      rw [hU.q_pr₂ e, ← Category.assoc, ← Functor.map_comp, lift_snd, hi₂', pullback_map_one,
        pullback_map_one, MonObj.one_comp, MonObj.comp_one]
  ·
    have := (U₂.gt e).i_hom
    let E := Equiv.ofBijective _ hD.xsum
    let j₁ : D₁.toPre.X → D.toPre.X := fun y => E.symm (y, 0)
    let j₂ : D₂.toPre.X → D.toPre.X := fun y => E.symm (0, y)
    have hj₁ : ∀ y, q₁ (j₁ y) = y ∧ q₂ (j₁ y) = 0 := fun y => by
      have := E.apply_symm_apply (y, 0)
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    have hj₂ : ∀ y, q₁ (j₂ y) = 0 ∧ q₂ (j₂ y) = y := fun y => by
      have := E.apply_symm_apply (0, y)
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    obtain ⟨t₁, ht₁, hf⟩ := hU.i_pr₁ e j₁ (fun y => (hj₁ y).1) (fun y => (hj₁ y).2)
    obtain ⟨t₂, ht₂, hs⟩ := hU.i_pr₂ e j₂ (fun y => (hj₂ y).1) (fun y => (hj₂ y).2)
    let t := GlobalTheory.SplitTorusPow.torusMap (Sp (R ⧸ I ^ (e + 1))) q₁
    have ht : TorusHomOf q₁ t := torusHomOf_torusMap q₁
    have e₁ : t ≫ t₁ = 𝟙 _ := by
      have k := ht.comp ht₁
      simp only [fun y => (hj₁ y).1] at k
      exact torusHomOf_unique k (TorusHomOf.id _)
    have e₂ : t ≫ t₂ = 1 := by
      have k := ht.comp ht₂
      simp only [fun y => (hj₂ y).1] at k
      exact eq_one_of_torusHomOf_zero k
    refine ⟨t, ht, pullback_prod_hom_ext _ ?_ ?_⟩
    · rw [Category.assoc, Category.assoc, ← Functor.map_comp, lift_fst, CategoryTheory.Functor.map_id, hf,
        ← Category.assoc, e₁, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, Category.assoc, ← Functor.map_comp, lift_snd, hs, ← Category.assoc, e₂,
        pullback_map_one, MonObj.one_comp, MonObj.comp_one]

end GlobalTheory.MumProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivMapOfTorMatch
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

theorem equivMap_of_torMatch : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), Function.Injective g → ∀ ρ, TorMatch U U' g β ρ → EquivMap U U' β ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV G' _ _ hG' D' A' U' g β hg ρ h
  intro f f' hf hf' hc m m' hm hm' y
  have hkV : ∀ k : ℕ, IsUnit (k : R) → IsUnit (k : V) := fun k hk => by
    simpa using hk.map g
  have hkR : ∀ k : ℕ, IsUnit (k : R) → IsUnit (k : R) := fun _ hk => hk
  have t := GlobalTheory.Poinc.TorEnd.torMatch_of_endChar R hR G hG D A U f hf m hm
  have t' := GlobalTheory.Poinc.TorEnd.torMatch_of_endChar V hV G' hG' D' A' U' f' hf' m' hm'
  have c₁ := torMatch_comp R hR G hG D A U R hR G hG D A U (RingHom.id R) f.left V hV G' hG' D' A' U' g β hg hkR m ρ t h
  have c₂ := torMatch_comp R hR G hG D A U V hV G' hG' D' A' U' g β V hV G' hG' D' A' U' (RingHom.id V) f'.left
    Function.injective_id hkV ρ m' h t'
  rw [RingHom.comp_id] at c₁
  rw [RingHom.id_comp, hc] at c₂
  have e := torMatch_unique R hR G hG D A U V hV G' hG' D' A' U' g (β ≫ f.left) hg _ _ c₁ c₂
  exact DFunLike.congr_fun e y

end GlobalTheory.Poinc.Eq8
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesDescendAlongProperMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem etale_coord_descend : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∃ V : U.left.Opens, x ∈ V ∧ Etale (V.ι ≫ τ) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ b) (V.ι ≫ U.hom) π := by
  intro R _ _ _ hR S X π U a b g τ c hπ hs hΓ hlft hsep ha haV hτ hc1 hc2 hc x hx hxc hmono hsurj
  have hq := _root_.GlobalTheory.Mum.isolated_in_coordinate_fibre R hR S X π U a b g τ c hπ hs hΓ hlft hsep ha haV hτ hc1 hc2 hc x hx hxc hmono hsurj
  obtain ⟨T, h, W, p, hfl, hpW, hpx, hW⟩ := _root_.GlobalTheory.Mum.exists_flat_chart_etale_of_quasiFiniteAt R hR S X π U a b g τ c hπ hs hΓ hlft hsep ha haV hτ hc1 hc2 hc x hx hxc hmono hsurj hq
  obtain ⟨V, hxV, hV⟩ := _root_.GlobalTheory.EtaleAtDescent.etale_nhds_of_flat_baseChange R hR U g τ hlft hτ T h hfl W p hpW hW
  rw [hpx] at hxV
  exact _root_.GlobalTheory.Mum.EtalePull.main R hR S X π U a b g τ c hπ hs hΓ hlft hsep ha haV hτ hc1 hc2 hc x hx hxc hmono hsurj V hxV hV

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumNullFamilyCompleteLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum.AdicSum


open Classical in
theorem sum_sub_sum_mem {R : Type} [CommRing R] (J : Ideal R) {X : Type} (v : X → R)
    (S T : Finset X) (hS : ∀ α ∉ S, v α ∈ J) (hT : ∀ α ∉ T, v α ∈ J) :
    ∑ α ∈ S, v α - ∑ α ∈ T, v α ∈ J := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff (s₁ := T) (s₂ := S)]
  exact J.sub_mem (J.sum_mem fun α hα => hT α (Finset.mem_sdiff.1 hα).2)
    (J.sum_mem fun α hα => hS α (Finset.mem_sdiff.1 hα).2)

theorem exists_adic_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (X : Type) (v : X → R), (∀ e : ℕ, {α | v α ∉ maximalIdeal R ^ (e + 1)}.Finite) →
    ∃ s : R, ∀ (e : ℕ) (S : Finset X), (∀ α ∉ S, v α ∈ maximalIdeal R ^ (e + 1)) →
      s - ∑ α ∈ S, v α ∈ maximalIdeal R ^ (e + 1) := by
  intro R _ _ _ hR X v hfin
  have hC : IsAdicComplete (maximalIdeal R) R := hR.1.2.2.2
  have hfin' : ∀ n : ℕ, {α | v α ∉ maximalIdeal R ^ n}.Finite := fun n =>
    (hfin n).subset fun α (hα : v α ∉ maximalIdeal R ^ n) (h : v α ∈ maximalIdeal R ^ (n + 1)) =>
      hα (Ideal.pow_le_pow_right (Nat.le_succ n) h)
  let F : ℕ → Finset X := fun n => (hfin' n).toFinset
  have hF : ∀ n, ∀ α ∉ F n, v α ∈ maximalIdeal R ^ n := by
    intro n α hα
    by_contra h
    exact hα ((hfin' n).mem_toFinset.2 h)
  let f : ℕ → R := fun n => ∑ α ∈ F n, v α
  have hsm : ∀ n : ℕ, maximalIdeal R ^ n • (⊤ : Submodule R R) = maximalIdeal R ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  obtain ⟨L, hL⟩ := (hC.toIsPrecomplete).prec (f := f) (by
    intro m n hmn
    rw [SModEq.sub_mem, hsm]
    exact sum_sub_sum_mem (maximalIdeal R ^ m) v (F m) (F n) (hF m)
      fun α hα => Ideal.pow_le_pow_right hmn (hF n α hα))
  refine ⟨L, fun e S hS => ?_⟩
  have h1 : f (e + 1) - L ∈ maximalIdeal R ^ (e + 1) := by
    have := hL (e + 1)
    rwa [SModEq.sub_mem, hsm] at this
  have h2 := sum_sub_sum_mem (maximalIdeal R ^ (e + 1)) v (F (e + 1)) S (hF (e + 1)) hS
  have : L - ∑ α ∈ S, v α = (f (e + 1) - ∑ α ∈ S, v α) - (f (e + 1) - L) := by ring
  rw [this]
  exact Ideal.sub_mem _ h2 h1

end GlobalTheory.Mum.AdicSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdNoetherianIntegrallyClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ZH.RatModel.exists_isAffineOpen_noetherian_integrallyClosed : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω), Geo.Tor.IsNormalScheme M.Z → ∀ (V : M.Z.Opens) (z : M.Z), z ∈ V → ∃ W : M.Z.Opens, IsAffineOpen W ∧ z ∈ W ∧ W ≤ V ∧ IsNoetherianRing (M.ringOn W) ∧ IsIntegrallyClosed (M.ringOn W) := by
  intro k Ω _ _ _ _ M hn V z hz
  obtain ⟨W, hW, hzW, hWV⟩ := exists_isAffineOpen_mem_and_subset (U := V) hz
  have hWV' : W ≤ V := hWV
  have hne : ((W : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hzW⟩
  refine ⟨W, hW, hzW, hWV', ?_, ?_⟩
  · have h1 : (M.s.appLE ⊤ W le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType M.s M.lft ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
    have h4 := h1.comp h2
    letI := ((M.s.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
    haveI : Algebra.FiniteType k Γ(M.Z, W) := h4
    haveI : IsNoetherianRing Γ(M.Z, W) := Algebra.FiniteType.isNoetherianRing k _
    exact isNoetherianRing_of_ringEquiv _ (M.sectionsEquiv W hne)
  · haveI := GlobalTheory.ZH.RatModel.isFractionRing_ringOn hW hne
    refine (isIntegrallyClosed_iff Ω).2 fun {x} hx => ?_
    have hmem : x ∈ M.ringOn W := GlobalTheory.ZH.RatModel.mem_ringOn.2 fun z' hz' => by
      haveI := GlobalTheory.ZH.RatModel.isIntegrallyClosed_O hn z'
      have hle := GlobalTheory.ZH.RatModel.ringOn_le_O (M := M) hz'
      letI : Algebra (M.ringOn W) (M.O z') := (Subalgebra.inclusion hle).toRingHom.toAlgebra
      haveI : IsScalarTower (M.ringOn W) (M.O z') Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have hx' : IsIntegral (M.O z') x := hx.tower_top
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx'
      rw [← hy]
      exact y.2
    exact ⟨⟨x, hmem⟩, rfl⟩
end

