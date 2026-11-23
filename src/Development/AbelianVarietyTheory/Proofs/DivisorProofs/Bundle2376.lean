module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultiplicityAndRankTensorDataLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricOfGaloisPullbackUniformisationBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SymDesc

open GlobalTheory.CechPic

theorem exists_gen_of_invariant {X Y Y' : Scheme.{0}} {K : Type} [Fintype K] {L : LB X} (hL : L.IsLB) (π : Y' ⟶ Y)
    {Γ₀ : Type} (act : Γ₀ → (Y' ⟶ Y')) (hact : ∀ σ, act σ ≫ π = π)
    (H : ∀ V : Y.Opens, Function.Injective (π.app V).hom ∧ ∀ u : Γ(Y', π ⁻¹ᵁ V),
      (∀ σ (h : π ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (π ⁻¹ᵁ V)), ((act σ).appLE _ _ h).hom u = u) → u ∈ Set.range (π.app V).hom)
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : LB.Gen (LB.LinComb L (fun k => π ≫ φ k) ε)) (hu : u.IsGen)
    (h : ∀ σ (z : Y') (J), Good L z J → val u (act σ) z J = val u (𝟙 Y') z J) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have le : ∀ j : K → L.ι, π ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => π ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have inv : ∀ (j : K → L.ι) σ (h₁ : π ⁻¹ᵁ LB.wchart L φ j ≤ act σ ⁻¹ᵁ (π ⁻¹ᵁ LB.wchart L φ j)),
      ((act σ).appLE _ _ h₁).hom (res (le j) (u.s j)).val = (res (le j) (u.s j)).val := by
    intro j σ h₁
    refine fn_ext fun z hz => ?_
    have hz' : act σ z ∈ π ⁻¹ᵁ LB.wchart L φ j := h₁ hz
    have e₀ : gs (𝟙 Y') z _ (((act σ).appLE _ _ h₁).hom (res (le j) (u.s j)).val) =
        gs (act σ) z _ (res (le j) (u.s j)).val := by
      have := (gs_res (𝟙 Y') z h₁ hz (((act σ).app _).hom (res (le j) (u.s j)).val)).trans
        (gs_pull (𝟙 Y') (act σ) z _ hz' _)
      rw [Category.id_comp] at this
      exact this
    rw [e₀, gs_unit (act σ) z _ hz', gs_unit (𝟙 Y') _ _ hz]
    choose I hI using fun χ : Y' ⟶ X => exists_chart hL (χ z)
    have c₁ := gen_trans hu (act σ) z (le j hz') (Good.mem hI _ (act σ))
    have c₂ := gen_trans hu (𝟙 Y') z (le j hz) (Good.mem hI _ (𝟙 Y'))
    have c₃ : trF (fun k => π ≫ φ k) ε (act σ) z j (fun k => I (act σ ≫ π ≫ φ k)) =
        trF (fun k => π ≫ φ k) ε (𝟙 Y') z j (fun k => I (𝟙 Y' ≫ π ≫ φ k)) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      have : act σ ≫ π ≫ φ k = 𝟙 Y' ≫ π ≫ φ k := by rw [reassoc_of% hact σ, Category.id_comp]
      show gm (act σ ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (act σ ≫ π ≫ φ k))) (L.g (j k) (I (act σ ≫ π ≫ φ k))) ^ _ =
        gm (𝟙 Y' ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (𝟙 Y' ≫ π ≫ φ k))) (L.g (j k) (I (𝟙 Y' ≫ π ≫ φ k))) ^ _
      rw [this]
    exact congrArg Units.val ((gm_res (act σ) z (le j) hz' _).trans
      ((c₁.trans ((congrArg₂ (· * ·) c₃ (h σ z I hI)).trans c₂.symm)).trans
        (gm_res (𝟙 Y') z (le j) hz _).symm))
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Y, LB.wchart L φ j)ˣ, pullU π _ a = res (le j) (u.s j) := by
    intro j
    obtain ⟨a, ha⟩ := (H _).2 _ (inv j)
    obtain ⟨b, hb⟩ := (H _).2 (res (le j) (u.s j))⁻¹.val (fun σ h₁ => by
      refine (Units.mul_left_inj (res (le j) (u.s j))).1 ?_
      rw [Units.inv_mul]
      conv_lhs => rw [← inv j σ h₁]
      rw [← map_mul, Units.inv_mul, map_one])
    have ab : a * b = 1 := (H _).1 (by rw [map_mul, ha, hb, Units.mul_inv, map_one])
    exact ⟨⟨a, b, ab, (mul_comm b a).trans ab⟩, Units.ext ha⟩
  choose a ha using desc
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z), π (r y) ∈ LB.wchart L φ j →
      gm (r ≫ π) y (LB.wchart L φ j) (a j) = gm r y (LB.wchart L (fun k => π ≫ φ k) j) (u.s j) := by
    intro j Z r y hy
    exact (gm_pull r π y _ hy _).symm.trans ((congrArg (gm r y _) (ha j)).trans (gm_res r y (le j) hy _))
  refine ⟨⟨a⟩, fun j j' => Units.ext ((H (LB.wchart L φ j ⊓ LB.wchart L φ j')).1 ?_)⟩
  refine congrArg Units.val (unit_ext (a := pullU π _ _) (b := pullU π _ _) fun y hy => ?_)
  have hy' : π y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
  refine (gm_pull (𝟙 Y') π y _ hy' _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') π y _ hy' _).symm)
  refine ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
    (gen_trans hu (𝟙 Y') y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L φ ε (𝟙 Y' ≫ π) y j j' hy'.1 hy'.2).trans ?_)
    ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans (hv j' _ _ y hy'.2)))
  simp only [trF, Category.id_comp]

theorem isSymmetric_of_exists_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (ht : t.IsGen) :
    L.IsSymmetric := by
  have e₂ : eSec G ≫ (ι[G]).left = eSec G := by
    rw [eSec, ← Over.comp_left, GrpObj.one_inv]
  have hi : LBIso L.L (L.L.pull (ι[G]).left) := by
    refine gen_chartPull (h := 𝟙 G.left) ⟨fun p => ![p.1 PUnit.unit, p.2], ?_, ?_⟩ t ht
    · intro p y hy
      exact Set.mem_iInter.2 fun k => by
        fin_cases k
        · exact mem_pull.1 hy.1
        · exact hy.2
    · intro y p q hp hq
      have hp1 := mem_pull.1 hp.1
      have hq1 := mem_pull.1 hq.1
      have hm : ∀ (p : (L.L.pull (ι[G]).left).ι × L.L.ι),
          y ∈ (LB.div (L.L.pull (ι[G]).left) L.L).U p →
          y ∈ LB.wchart L.L ![(ι[G]).left, 𝟙 G.left] ![p.1 PUnit.unit, p.2] := by
        intro p hp
        exact Set.mem_iInter.2 fun k => by
          fin_cases k
          · exact mem_pull.1 hp.1
          · exact hp.2
      refine (gm_div L.L (L.L.pull (ι[G]).left) (𝟙 _) y p q ⟨hp, hq⟩).trans ?_
      rw [gm_pull_g L.L (ι[G]).left (𝟙 _) y p.1 q.1 hp.1 hq.1]
      refine Eq.trans ?_ (gm_linComb L.L ![(ι[G]).left, 𝟙 G.left] ![1, -1] (𝟙 _) y _ _ (hm p hp) (hm q hq)).symm
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        zpow_one, zpow_neg, Category.id_comp]
      rfl
  have he : eSec G ≫ (ι[G]).left = 𝟙 _ ≫ eSec G := e₂.trans (Category.id_comp _).symm
  exact ⟨he, Unif.RigidifyIso.exists_rigidified_iso S S (𝟙 S) G G _ he L L hi⟩

theorem exists_sym_pull {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f β) {L : LB G.left} (hL : L.IsLB)
    {L' : LB G'.left} (hL' : L'.IsLB) (hiso : LBIso L' (L.pull β))
    (s : LB.Gen (LB.LinComb L' (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1])) (hs : s.IsGen)
    (hr : LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ s (eSec G')) (LB.oneGen L')) :
    ∃ u : LB.Gen (LB.LinComb L (fun k : Fin 2 => β ≫ ![(ι[G]).left, 𝟙 G.left] k) ![1, -1]), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S')).left) (z : Z) (I), Good L z I → val u (r ≫ eSec G') z I = 1 := by
  obtain ⟨w, hw⟩ := hiso
  have hp := (isGen_iff w).1 hw
  have hι : (ι[G']).left ≫ β = β ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom gp G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine e.trans ?_
    show (𝟙 _ ≫ β) ≫ _ = _
    rw [Category.id_comp]
  have e₁ : eSec G' ≫ (ι[G']).left = eSec G' := by
    rw [eSec, ← Over.comp_left, GrpObj.one_inv]
  have hc : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ β = β ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up hp hL hL' s hs
  obtain ⟨u, hu, vu⟩ := exists_gen hL (φ' := fun k : Fin 2 => β ≫ ![(ι[G]).left, 𝟙 G.left] k) (ε' := ![1, -1])
    (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ (![1, -1] : Fin 2 → ℤ) k) (hc k)) t₁ ht₁
  refine ⟨u, hu, fun Z r z I hI => ?_⟩
  choose J hJ using fun χ : Z ⟶ G'.left => exists_chart hL' (χ z)
  rw [vu Z _ z I hI, val_of t₁ _ z I (fun k => I (((r ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] k) ≫ β))
    (fun k => congrArg I (Category.assoc _ _ _).symm)]
  refine (v₁ Z (r ≫ eSec G') z _ _ (Set.mem_iInter.2 fun k => hI (((r ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] k) ≫ β))
    (Good.mem hJ _ _)).trans ?_
  have h1 : val s (r ≫ eSec G') z J = 1 :=
    (val_pull hJ s (eSec G') r).symm.trans ((val_corr hJ hr r).trans (val_one _))
  refine (congrArg₂ (· * ·) ?_ h1).trans (_root_.mul_one 1)
  have k : ∀ (V : Type) [CommGroup V] (q : (Z ⟶ G'.left) → V),
      ∏ k : Fin 2, q ((r ≫ eSec G') ≫ ![(ι[G']).left, 𝟙 G'.left] k) ^ (![1, -1] : Fin 2 → ℤ) k = 1 := by
    intro V _ q
    simp [Fin.prod_univ_two, e₁]
  exact k _ (fun q => gw w q z (I (q ≫ β)) (J q))

end GlobalTheory.Mum.SymDesc

namespace GlobalTheory.Mum

open SymDesc

theorem isSymmetric_of_pull_iso_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∀ (L : LB G.left) (hL : L.IsLB), LBIso U'.LG.L (L.pull β) → ∀ (rig : LB.Gen (L.pull (eSec G))) (hr : rig.IsGen), RigLB.IsSymmetric (⟨L, rig, hL, hr⟩ : RigLB G) := by
  intro R _ _ _ _ R' _ _ _ ρ hρ hg D D' hD A' G' _ _ _ U' a G _ _ β hG gp hβ L hL hiso rig hr
  obtain ⟨u, hu, h1⟩ := exists_sym_pull gp hL U'.LG.isLB hiso U'.symG U'.symG_gen U'.symG_rig
  have := U'.smooth
  have := hG.smooth
  have hsurj : Function.Surjective (pullback.snd G'.hom (jK R')).appTop.hom := by
    have hw : U'.gen.hom.left ≫ A'.A.hom = pullback.snd G'.hom (jK R') := Over.w U'.gen.hom
    have : IsIso U'.gen.hom.left := ((Over.forget _).mapIso U'.gen).isIso_hom
    have : IsIso U'.gen.hom.left.appTop := inferInstanceAs (IsIso (U'.gen.hom.left.app ⊤))
    rw [← hw]
    exact surj_comp (ConcreteCategory.bijective_of_isIso U'.gen.hom.left.appTop).2
      (GlobalTheory.SemiRigid.globalFns _ _ A'.isAb).2
  have he : eSec G' ≫ G'.hom = 𝟙 _ := Over.w η[G']
  obtain ⟨t, ht⟩ := exists_gen_of_invariant hL β a.act hβ
    (_root_.GlobalTheory.Mum.InvFun.invariant_functions R R' ρ hρ hg _ _ G.hom G'.hom β inferInstance gp.1 a.act hβ fun σ => (a.cart σ).1.w)
    _ _ u hu fun σ z J hJ => by
      have key := GlobalTheory.ValueForm.gen_unique_of_injective hL (φ := fun k : Fin 2 => a.act σ ≫ β ≫ ![(ι[G]).left, 𝟙 G.left] k)
        (fun V _ q => Finset.prod_congr rfl fun k _ => by
          dsimp only
          rw [reassoc_of% hβ σ])
        (pullback.fst G'.hom (jK R')) (GlobalTheory.ValueForm.app_generic_injective _) (pullback.snd _ _)
        (pullback.lift (jK R' ≫ eSec G') (𝟙 _) (by
          rw [Category.id_comp]
          exact (Category.assoc _ _ _).trans ((congrArg (jK R' ≫ ·) he).trans (Category.comp_id _))))
        (pullback.lift_snd _ _ _) hsurj (DVR.pullGen_isGen _ _ _ _ hu (a.act σ)) hu (fun y I hI => by
          rw [pullback.lift_fst]
          refine (val_pull hI _ _ _).trans (Eq.trans ?_ (h1 _ (jK R') y I hI).symm)
          have e : (jK R' ≫ eSec G') ≫ a.act σ = (jK R' ≫ (cubeMapOf (a.cart σ)).e) ≫ eSec G' :=
            (Category.assoc _ _ _).trans ((congrArg (jK R' ≫ ·) (cubeMapOf (a.cart σ)).e_comm).trans
              (Category.assoc _ _ _).symm)
          exact (congrArg (fun q => val u q y I) e).trans (h1 _ _ y I hI)) _ (𝟙 _) z J hJ
      have k₂ := (val_pull hJ u (a.act σ) (𝟙 _)).symm.trans key
      rwa [Category.id_comp] at k₂
  exact isSymmetric_of_exists_gen _ t ht

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranslateOfTangentVectorFibreToGroupScheme
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

section

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_mul_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {m : G'.left ⟶ G.left} (hm : IsGrpPullback G' G f m) (T : Over S') (x y : T ⟶ G')
    (s : T.left ⟶ S) (hs : s = T.hom ≫ f) :
    ∃ x₀ y₀ : Over.mk s ⟶ G, x₀.left = x.left ≫ m ∧ y₀.left = y.left ≫ m ∧ (x₀ * y₀).left = (x * y).left ≫ m := by
  subst hs
  have e : ∀ z : T ⟶ G', (z.left ≫ m) ≫ G.hom = T.hom ≫ f := fun z ↦ by
    rw [Category.assoc, hm.1.w, ← Category.assoc, Over.w z]
  exact ⟨Over.homMk (x.left ≫ m) (e x), Over.homMk (y.left ≫ m) (e y), rfl, rfl, hm.2 T x y _ _ rfl rfl⟩

end

theorem IsTransl.isTranslate_comp : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) {K : Type} [Field K] (x0 : Sp K ⟶ X) (A : Over (Sp K)) [GrpObj A] (m : A.left ⟶ t.G.left) (hm : IsGrpPullback A t.G x0 m) {R : Type} [CommRing R] (ψ : R →+* K) (v : Sp (DualNumber R) ⟶ t.G.left) (u : epsR K ⟶ A) (hu : u.left ≫ m = spMap (dualMap ψ) ≫ v) {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) (w : Sp (DualNumber B) ⟶ A.left) (hw : IsTransl φ x u w), LogKS.IsTranslate t (φ.comp ψ) (x ≫ m) v (w ≫ m) := by
  intro E _ _ _ H X t K _ x0 A _ m hm R _ ψ v u hu B _ φ x hx w hw
  obtain ⟨x₁, v₁, a, b, rfl⟩ := hw
  have sc : ∀ {P Q T : Type} [CommRing P] [CommRing Q] [CommRing T] (f : P →+* Q) (g : Q →+* T),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g ↦ by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have dc : (dualMap φ).comp (dualMap ψ) = dualMap (φ.comp ψ) :=
    RingHom.ext fun c ↦ by ext <;> simp [dualMap]
  obtain ⟨x₀, y₀, h₁, h₂, h₃⟩ := exists_mul_of_isGrpPullback hm _ x₁ v₁
    (spMap (algebraMap B (DualNumber B)) ≫ (x ≫ m) ≫ t.G.hom) (by
      change _ = spMap ((algebraMap B (DualNumber B)).comp φ) ≫ x0
      rw [Category.assoc, hm.1.w, ← Category.assoc x, hx, ← Category.assoc, sc])
  refine ⟨x₀, y₀, ?_, ?_, h₃⟩
  · rw [h₁, a]; exact Category.assoc _ _ _
  · rw [h₂, b, ← dc, ← sc (dualMap ψ) (dualMap φ)]
    refine (Category.assoc _ _ _).trans ?_
    rw [hu]; exact (Category.assoc (spMap (dualMap φ)) (spMap (dualMap ψ)) v).symm

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfBasicOpenTop
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.RescaleLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem isUnit_of_basicOpen_top {Y : Scheme.{0}} (s : Γ(Y, ⊤)) (h : Y.basicOpen s = ⊤) : IsUnit s :=
  Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => (Y.mem_basicOpen _ x hx).1 (h.ge hx)

abbrev fnSp (A : Type) [CommRing A] : A →+* Γ(Sp A, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem appTop_comp_spMap {R₀ A : Type} [CommRing R₀] [CommRing A] (α : R₀ →+* A) {Z : Scheme.{0}}
    (s : Z ⟶ Sp A) (r : R₀) : (s ≫ spMap α).appTop.hom (fnSp R₀ r) = s.appTop.hom (fnSp A (α r)) := by
  have nat := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom α))
  rw [Scheme.Hom.comp_appTop]
  exact congrArg s.appTop.hom nat.symm

def fnOn {R₀ : Type} [CommRing R₀] (W : (Sp R₀).Opens) : R₀ →+* Γ(W.toScheme, ⊤) :=
  W.ι.appTop.hom.comp (fnSp R₀)

theorem appTop_fnOn {R₀ A : Type} [CommRing R₀] [CommRing A] (W : (Sp R₀).Opens) (α : R₀ →+* A) {Z : Scheme.{0}}
    (t : Z ⟶ W.toScheme) (s : Z ⟶ Sp A) (h : t ≫ W.ι = s ≫ spMap α) (r : R₀) :
    t.appTop.hom (fnOn W r) = s.appTop.hom (fnSp A (α r)) := by
  have e : t.appTop.hom (fnOn W r) = (t ≫ W.ι).appTop.hom (fnSp R₀ r) := by
    rw [Scheme.Hom.comp_appTop]; rfl
  rw [e, h, appTop_comp_spMap]

theorem gm_fnOn {R₀ A : Type} [CommRing R₀] [CommRing A] (W : (Sp R₀).Opens) (α : R₀ →+* A) {Z : Scheme.{0}}
    (t : Z ⟶ W.toScheme) (s : Z ⟶ Sp A) (h : t ≫ W.ι = s ≫ spMap α) (r : R₀) (u : Γ(W.toScheme, ⊤)ˣ) (v : Aˣ)
    (hu : (u : Γ(W.toScheme, ⊤)) = fnOn W r) (hv : (v : A) = α r) (z : Z) :
    gm t z ⊤ u = gm s z ⊤ (unitOn v) := by
  rw [GlobalTheory.UU.gm_top t, GlobalTheory.UU.gm_top s]
  congr 1
  apply Units.ext
  show t.appTop.hom (u : Γ(W.toScheme, ⊤)) = s.appTop.hom (fnSp A (v : A))
  rw [hu, hv, appTop_fnOn W α t s h r]

theorem isUnit_fnOn {R₀ : Type} [CommRing R₀] (f r : R₀) (N : ℕ) (hr : r ∣ f ^ N) :
    IsUnit (fnOn ((Sp R₀).basicOpen (fnSp R₀ f)) r) := by
  set W := (Sp R₀).basicOpen (fnSp R₀ f)
  have hf : IsUnit (fnOn W f) := isUnit_of_basicOpen_top _ (by
    have e := Scheme.preimage_basicOpen W.ι (fnSp R₀ f)
    rw [Scheme.Opens.ι_preimage_self] at e
    exact e.symm)
  exact isUnit_of_dvd_unit (map_dvd (fnOn W) hr |>.trans (by rw [map_pow])) (hf.pow N)

end GlobalTheory.RescaleLift

namespace GlobalTheory.RescaleLift

theorem exists_psiOn_rescale {R₀ : Type} [CommRing R₀] [IsDomain R₀] (D₁ : DegPre R₀) (κ₀ : D₁.X → (FractionRing R₀)ˣ)
    {W W' : (Sp R₀).Opens} (ψ : PsiOn D₁ W) (hle : W' ≤ W) (u : D₁.X → Γ(W'.toScheme, ⊤)ˣ) (r : D₁.X → R₀)
    (hu : ∀ y, (u y : Γ(W'.toScheme, ⊤)) = fnOn W' (r y)) (hr : ∀ y, algebraMap R₀ (FractionRing R₀) (r y) = κ₀ y) :
    ∃ ψW : PsiOn (GlobalTheory.PolDeg.rescale D₁ κ₀) W', ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J,
      Good D₁.P.L z J → val (ψW.psi y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ (Sp R₀).homOfLE hle) z J := by
  let m : W'.toScheme ⟶ W.toScheme := (Sp R₀).homOfLE hle
  have hm : m ≫ W.ι = W'.ι := Scheme.homOfLE_ι _ _
  have hφ : ∀ y : D₁.X, m ≫ (toUnit (TW W) ≫ D₁.c y).left = (toUnit (TW W') ≫ D₁.c y).left := fun y => by
    show m ≫ W.ι ≫ (D₁.c y).left = W'.ι ≫ (D₁.c y).left
    rw [← Category.assoc, hm]
  choose b hb vb using fun y : D₁.X => exists_gen D₁.P.isLB (K' := PUnit)
    (φ' := fun _ => (toUnit (TW W') ≫ D₁.c y).left) (ε' := fun _ => -1)
    (fun U _ k => Finset.prod_congr rfl fun _ _ => congrArg (fun q => k q ^ (-1 : ℤ)) (hφ y))
    (GlobalTheory.UU.scaleGen (u y) (LB.pullGen D₁.P.L _ _ (ψ.psi y) m))
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ.psi_gen y) m))
  have ev : ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J, Good D₁.P.L z J →
      val (b y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ m) z J := fun y Z t z J hJ =>
    (vb y Z t z J hJ).trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)))
  refine ⟨{ psi := b, psi_gen := hb, psi_eq := fun y => corr_of_val D₁.P.isLB fun z J hJ => ?_ }, ev⟩
  refine (val_pull hJ _ _ _).trans ((ev y _ z J hJ).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  refine (congrArg₂ (· * ·) ?_ ?_).trans (GlobalTheory.UU.val_scaleGen (unitOn (κ₀ y)) (D₁.psi y) _ hJ).symm
  · refine gm_fnOn W' (algebraMap R₀ (FractionRing R₀)) _ _ ?_ (r y) _ _ (hu y) (hr y).symm z
    rw [Category.id_comp, Category.id_comp, morphismRestrict_ι]
  · refine GlobalTheory.ArcSpecialise.psiOn_generic ψ y _ _ ?_ hJ
    rw [Category.assoc, hm, Category.id_comp, Category.id_comp, morphismRestrict_ι]

end GlobalTheory.RescaleLift

namespace GlobalTheory.RescaleLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

end GlobalTheory.RescaleLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTraitScalarGenericFibreNonfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem unit_nonfield : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ¬ IsField R → ∀ b : W, b ≠ 0 → ∀ z : Z, IsUnit (gs p z ⊤ (scal T.G.hom b)) := by
  intro R _ _ _ D C W _ _ _ T Z p p' hpp hR b hb z

  have hw : p ≫ T.G.hom ≫ spMap T.φ = p' ≫ C.A.A.hom ≫ jK R := by
    rw [← T.ξ_π, ← C.gp_π, ← Category.assoc T.G.hom, ← T.cart.1.w, ← Category.assoc C.A.A.hom, ← C.α_cart.1.w]
    simp only [← Category.assoc]; rw [hpp]
  have hpt := congrArg (fun g => (g z).asIdeal) hw
  simp only [Scheme.Hom.comp_apply] at hpt
  set P := ((p ≫ T.G.hom) z) with hP
  have hc : P.asIdeal.comap T.φ = ⊥ := by
    have e1 : (spMap T.φ ((T.G.hom) (p z))).asIdeal = P.asIdeal.comap T.φ := by
      rw [hP, Scheme.Hom.comp_apply]; rfl
    rw [← e1, hpt]
    have e2 : ((jK R) ((C.A.A.hom) (p' z))).asIdeal = ((C.A.A.hom) (p' z)).asIdeal.comap (algebraMap R (FractionRing R)) := rfl
    rw [e2]
    have hbot : ((C.A.A.hom) (p' z)).asIdeal = ⊥ := by
      have := ((C.A.A.hom) (p' z)).isPrime
      exact Ideal.eq_bot_of_prime _
    rw [hbot]
    exact (Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R)))
  have hdvr : IsDiscreteValuationRing W := T.cdvr.1
  have hPbot : P.asIdeal = ⊥ := by
    by_contra hne
    have hmax : P.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal P.isPrime hne
    have hm : P.asIdeal = maximalIdeal W := IsLocalRing.eq_maximalIdeal hmax
    have hRm : maximalIdeal R ≠ ⊥ := fun h => hR ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hRm
    have hl := T.loc
    have hφr : T.φ r ∈ P.asIdeal := by
      rw [hm]
      exact (IsLocalRing.mem_maximalIdeal _).2 fun hu => (IsLocalRing.mem_maximalIdeal _).1 hr (isUnit_of_map_unit T.φ r hu)
    have : r ∈ P.asIdeal.comap T.φ := hφr
    rw [hc] at this
    exact hr0 ((Submodule.mem_bot R).1 this)
  have hmem : (p ≫ T.G.hom) z ∈ (Sp W).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b) := by
    rw [basicOpen_eq_of_affine]
    show b ∉ ((p ≫ T.G.hom) z).asIdeal
    rw [← hP, hPbot]; exact fun h => hb ((Submodule.mem_bot W).1 h)
  have hpull : gs p z ⊤ (scal T.G.hom b) = gs (p ≫ T.G.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b) :=
    gs_pull p T.G.hom z ⊤ trivial _
  rw [hpull, gs_eq _ z ⊤ trivial]
  have hz : z ∈ Z.basicOpen (((p ≫ T.G.hom).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b)) := by
    rw [← Scheme.preimage_basicOpen]; exact hmem
  exact (Scheme.mem_basicOpen Z _ z (by trivial)).1 hz

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabTors
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def LabTors {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (k : ℕ)
    (x : QkPt D (Kb R) k → (TFK (R := R) (Kb R) ⟶ A.A)) : Prop :=
  (∀ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ k = 1 → ∃ p, x p = y) ∧ (∀ p, x p ^ k = 1) ∧
    (∀ p p', x p = x p' ↔ QkPt.Equiv D (Kb R) p p') ∧
    (∀ p p' p'', QkAdd p p' p'' → x p'' = x p * x p') ∧
    ∀ p p' (z : (Kb R)ˣ), WeilQkIs D (Kb R) k p p' z ↔ WeilIs A.A A.L k (x p) (x p') (unitOn z)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultiplicityAndRankTensorDataLatticeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieMultiplicity_and_rank_tensorData_lattice : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ s : ℕ, r = s * Module.finrank ℚ E → Module.finrank (𝓞 E) D'.toPre.X = s * Module.finrank ℤ D.toPre.X ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (τ : 𝓞 E →+* F), LieMult (letI := H.starRing; ofRingAct o.onB.toRingAct) (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))) τ (s * D.toPre.P.g) := by
  first | exact @GlobalTheory.Mum.lieMult_tens | exact GlobalTheory.Mum.lieMult_tens | (intros; apply GlobalTheory.Mum.lieMult_tens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisGenericUnitaryUniforStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleSymmetryHypothesis_generic_unitary_uniformised : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif I t), (letI := P.A.isAb.comm; GlobalTheory.ZH.HypS P.A.A P.A.L) := by
  first | exact @GlobalTheory.UTraitHyp.hypS_generic | exact GlobalTheory.UTraitHyp.hypS_generic | (intros; apply GlobalTheory.UTraitHyp.hypS_generic <;> assumption)
end

