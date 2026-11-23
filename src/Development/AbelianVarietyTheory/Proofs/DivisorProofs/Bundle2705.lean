module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionMapWelldefinedAdditiveCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianFieldPointEqEighthPowerUniversalPullb
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.FieldPt

theorem of_factor {g n : ℕ} {o : Type} [CommRing o] {ζ : o} (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ)
    {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω}
    {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) {C : Over (Sp S.R)} [GrpObj C] (pr : Fin 8 → (ρ.P.A ⟶ C))
    (V : M.Z.Opens) (v : V.toScheme ⟶ F.X) {T₀ : Scheme.{0}} (ξ : T₀ ⟶ V.toScheme)
    (cO : SiegPre g n ζ ((ξ ≫ v) ≫ F.s)) (prO : Fin 8 → ((Over.pullback (ξ ≫ V.ι)).obj FinalForm.G ⟶ cO.A))
    (hpbO : SiegPB cO F.univ (ξ ≫ v)) (hmonO : ∀ a, IsMonHom (prO a))
    (hunivO : ∀ (T' : Over T₀) (y : Fin 8 → (T' ⟶ cO.A)), ∃! x : T' ⟶ (Over.pullback (ξ ≫ V.ι)).obj FinalForm.G,
      ∀ a, x ≫ prO a = y a)
    (hLO : LBIso (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (ξ ≫ V.ι)))
      (LB.LinComb cO.P (K := Fin 8 × Fin 8) (fun ab => (lift (prO ab.1) (prO ab.2)).left) (fun ab => W ab.1 ab.2)))
    (hmatO : ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G), MatOn FinalForm pr a b f → MatEnd prO a b ((Over.pullback (ξ ≫ V.ι)).map f))
    {K : Type} [Field K] (t : Sp K ⟶ V.toScheme) (t' : Sp K ⟶ T₀) (ht : t' ≫ ξ = t)
    (B : Over (Sp K)) [GrpObj B] (φB : B.left ⟶ FinalForm.G.left) (hB : IsGrpPullback B FinalForm.G (t ≫ V.ι) φB) :
    ∃ (c' : SiegPre g n ζ ((t ≫ v) ≫ F.s)) (pr' : Fin 8 → (B ⟶ c'.A)), SiegPB c' F.univ (t ≫ v) ∧
      (∀ a, IsMonHom (pr' a)) ∧ (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c'.A)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr' a = y a) ∧
      (∀ L' : LB B.left, L'.IsLB → LBIso L' (FinalForm.L.L.pull φB) → LBIso L' (LB.LinComb c'.P (K := Fin 8 × Fin 8)
        (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2))) ∧
      ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (fB : B ⟶ B), MatOn FinalForm pr a b f → fB.left ≫ φB = φB ≫ f.left →
        MatEnd pr' a b fB := by
  subst ht
  have hB' : IsGrpPullback B FinalForm.G (t' ≫ (ξ ≫ V.ι)) φB := hB.congr (Category.assoc _ _ _) rfl
  have hφ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (ξ ≫ V.ι) t' hB'
  have hφ'f : pullback.lift φB (B.hom ≫ t') (by rw [hB'.1.w, Category.assoc]) ≫ pullback.fst FinalForm.G.hom (ξ ≫ V.ι) = φB :=
    pullback.lift_fst _ _ _
  have hφ's : pullback.lift φB (B.hom ≫ t') (by rw [hB'.1.w, Category.assoc]) ≫ pullback.snd FinalForm.G.hom (ξ ≫ V.ι) =
      B.hom ≫ t' := pullback.lift_snd _ _ _
  generalize pullback.lift φB (B.hom ≫ t') (by rw [hB'.1.w, Category.assoc]) = φ' at hφ hφ'f hφ's
  have hid : spMap (RingHom.id o) = 𝟙 (Sp o) := Spec.map_id _
  obtain ⟨c', hc'⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n o o ζ ζ (RingHom.id o) _ (Sp K)
    ((ξ ≫ v) ≫ F.s) (((t' ≫ ξ) ≫ v) ≫ F.s) t' rfl (by rw [hid, Category.comp_id]; simp only [Category.assoc])).1 cO
  have hcomp := GlobalTheory.SiegelPullComp.pb_comp hpbO hc'
  rw [← Category.assoc] at hcomp
  obtain ⟨χ, χ₂, hχ, hsq, hP, -⟩ := hc'
  obtain ⟨pr', hpr', hmon', huniv'⟩ := GlobalTheory.GrpPullPow.pr_pull prO hφ hχ hmonO hunivO
  refine ⟨c', pr', hcomp, hmon', huniv', ?_, ?_⟩
  · intro L' hL' hiso
    have hL := FinalForm.L.isLB
    have e1 : LBIso (FinalForm.L.L.pull φB) ((FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (ξ ≫ V.ι))).pull φ') := by
      rw [← hφ'f]
      exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame FinalForm.L.L _ _ _ φ' fun _ => rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (ξ ≫ V.ι))) φ' φ' rfl)
        ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso _, ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen (pull_isLB hL _)⟩
    have e2 := LBIso.trans hL' (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) hiso e1
    exact GlobalTheory.Poinc.Eq8.lbIso_eighth_pull cO.P c'.P _ L' prO pr' W cO.isLB c'.isLB (pull_isLB hL _) hL' hsq hP hpr'
      e2 hLO
  · intro a b f fB hf hfB
    refine GlobalTheory.MatEndPull.matEnd_pull prO pr' a b _ fB hφ hχ hpr' ?_ (hmatO a b f hf)
    apply pullback.hom_ext
    · have e : ((Over.pullback (ξ ≫ V.ι)).map f).left ≫ pullback.fst FinalForm.G.hom (ξ ≫ V.ι) =
          pullback.fst FinalForm.G.hom (ξ ≫ V.ι) ≫ f.left := pullback.lift_fst _ _ _
      rw [Category.assoc, Category.assoc, hφ'f, e, ← Category.assoc, hφ'f, hfB]
    · have w1 : ((Over.pullback (ξ ≫ V.ι)).map f).left ≫ pullback.snd FinalForm.G.hom (ξ ≫ V.ι) =
          pullback.snd FinalForm.G.hom (ξ ≫ V.ι) := pullback.lift_snd _ _ _
      rw [Category.assoc, Category.assoc, hφ's, w1, hφ's, ← Category.assoc, Over.w fB]

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (K : Type) [Field K] (t : Sp K ⟶ V.toScheme) (B : Over (Sp K)) [GrpObj B] (φB : B.left ⟶ FinalForm.G.left), IsGrpPullback B FinalForm.G (t ≫ V.ι) φB → ∃ (c' : SiegPre g n ζ ((t ≫ v) ≫ F.s)) (pr' : Fin 8 → (B ⟶ c'.A)), SiegPB c' F.univ (t ≫ v) ∧ (∀ a, IsMonHom (pr' a)) ∧ (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c'.A)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr' a = y a) ∧ (∀ L' : LB B.left, L'.IsLB → LBIso L' (FinalForm.L.L.pull φB) → LBIso L' (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2))) ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (fB : B ⟶ B), MatOn FinalForm pr a b f → fB.left ≫ φB = φB ≫ f.left → MatEnd pr' a b fB := by
  intro g n o _ ζ F W o' Ω _ _ _ _ S ρ u c pr hS M U₀ EE FinalForm hO V v hv K _ t B _ φB hB
  obtain ⟨cO, prO, hpbO, hmonO, hunivO, hLO, hmatO⟩ := GlobalTheory.T.eighth_power_universal_object_at_model_stalk g n o ζ F W o' Ω S ρ u c pr hS M U₀ EE FinalForm hO V v hv
    (t (IsLocalRing.closedPoint K))
  exact of_factor F W FinalForm pr V v _ cO prO hpbO hmonO hunivO hLO hmatO t _
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk t) B φB hB

end GlobalTheory.Poinc.Eq8.FieldPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomTorsionCompatiblePeriodsLattices
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two
open GlobalTheory.TorusExt

theorem periods_of_key : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → ∀ E E' : EndU U₁.toUnifPre, LBIso (cubeLB G₁ ![fst G₁ G₁ ≫ E.aG, snd G₁ G₁] U₁.LG.L) (cubeLB G₁ ![fst G₁ G₁, snd G₁ G₁ ≫ E'.aG] U₁.LG.L) → LBIso (cubeLB A₂.A ![fst A₁.A A₁.A ≫ c, snd A₁.A A₁.A ≫ c] A₂.L) (cubeLB A₁.A ![fst A₁.A A₁.A ≫ E.aA, snd A₁.A A₁.A ≫ 𝟙 A₁.A] A₁.L) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], Key U₁.toUnifPre U₂.toUnifPre c b h F → ∃ φ : D₁.toPre.X →+ D₂.toPre.X, (∀ (y : D₁.toPre.X) (g : GtPtF D₁.toPre F), GtPtF.IsIota y g → ∃ g' : GtPtF D₂.toPre F, Act D₁.toPre D₂.toPre b h g g' ∧ GtPtF.IsIota (φ y) g') ∧ ∀ y, h (φ y) = E.h y := by
  intro R _ _ _ I hA D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ hG₁ hG₂ U₁ U₂ a c b h hc hgen hlin hco E E' hE hW F _ _ _ hkey
  have hL := GlobalTheory.firstFiveLaws
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  letI := gtGroup D₁.toPre F
  letI := gtGroup D₂.toPre F
  letI : ∀ (D : DegPre R), AddCommGroup (GtPtF D F) := fun D => gtGroup D F
  let iota : ∀ {D : DegPre R}, D.TauBimult → D.X →+ GtPtF D F := fun {D} hB =>
    letI := gtGroup D F
    AddMonoidHom.mk' (fun x => (exists_iota (F := F) hB x).choose) fun x x' => by
      obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x).choose_spec
      obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x').choose_spec
      obtain ⟨b'', v''⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB (x + x')).choose_spec
      refine (isAdd_iff_eq _ _ _).1 ((isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', cPoint_add], fun χ y J hJ => ?_⟩)
      have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
      rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
      exact tau_mul (𝟙 (TF (R := R) F)) hJ hB x x' χ
  have isIota_iff_eq : ∀ {D : DegPre R} (hB : D.TauBimult) (x : D.X) (g : GtPtF D F), GtPtF.IsIota x g ↔ g = iota hB x := by
    intro D hB x g
    exact ⟨fun h => isIota_unique h (exists_iota (F := F) hB x).choose_spec,
      fun h => h ▸ (exists_iota (F := F) hB x).choose_spec⟩
  have qk_nsmul : ∀ {D : DegPre R} (hB : D.TauBimult) {k : ℕ} (p : QkPt D F k), k • p.g = iota hB p.y := by
    intro D hB k p
    obtain ⟨h, h₁, h₂⟩ := p.eq
    exact ((isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((isIota_iff_eq hB _ _).1 h₂)
  let qkMk : ∀ {D : DegPre R} (hB : D.TauBimult) {k : ℕ} (y : D.X) (g : GtPtF D F), k • g = iota hB y → QkPt D F k :=
    fun {D} hB {k} y g h => ⟨y, g, k • g, (isNsmul_iff_eq _ _ _).2 rfl, (isIota_iff_eq hB _ _).2 h⟩
  have hB₁ := D₁.tau_bimult
  have hB₂ := D₂.tau_bimult
  have inj₂ := GlobalTheory.IotaInj.main hL R I hA D₂ F
  have dv₁ := (gt_onto_divisible_kernel hL R I hA D₁ F).2.1

  obtain ⟨ex, ad, tor⟩ := _root_.GlobalTheory.Mum.Two.act_two_hom R D₁.toPre D₂.toPre b h hlin.2.1 (fun χ => (hco χ).imp fun _ hu => hu.1) F
  choose mf hmf hmu using ex
  let m : GtPtF D₁.toPre F →+ GtPtF D₂.toPre F := AddMonoidHom.mk' mf fun x x' => (isAdd_iff_eq _ _ _).1
    (ad x x' (x + x') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (hmf x) (hmf x') (hmf _))
  have hm : ∀ x x', Act D₁.toPre D₂.toPre b h x x' ↔ x' = m x := fun x x' => ⟨hmu x x', fun e => e ▸ hmf x⟩

  have push : ∀ k : ℕ, 1 ≤ k → ∀ f₁ f₂, Tors U₁.toUnifPre F k f₁ → Tors U₂.toUnifPre F k f₂ → ∀ p : QkPt D₁.toPre F k,
      ∃ p' : QkPt D₂.toPre F k, p'.g = m p.g ∧ f₂ p' = f₁ p ≫ c ∧ GtPtF.IsIota p'.y (m (iota hB₁ p.y)) := by
    intro k hk f₁ f₂ hf₁ hf₂ p
    obtain ⟨p', e₁, e₂⟩ := hkey k hk p (f₁ p) ((hf₁.1 _ _).2 rfl) (m p.g) ((hm _ _).2 rfl)
    refine ⟨p', e₁, ((hf₂.1 _ _).1 e₂).symm, (isIota_iff_eq hB₂ _ _).2 ?_⟩
    rw [← qk_nsmul hB₂ p', e₁, ← map_nsmul, qk_nsmul hB₁ p]
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hA D₁ A₁ G₁ hG₁ U₁ F 1 le_rfl
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hA D₂ A₂ G₂ hG₂ U₂ F 1 le_rfl
  have ex₁ : ∀ y, ∃ y', GtPtF.IsIota y' (m (iota hB₁ y)) := fun y => by
    obtain ⟨p', -, -, hp'⟩ := push 1 le_rfl f₁ f₂ hf₁ hf₂ (qkMk hB₁ y (iota hB₁ y) (one_smul _ _))
    exact ⟨p'.y, hp'⟩
  choose φ₀ hφ₀ using ex₁
  let φ : D₁.toPre.X →+ D₂.toPre.X := AddMonoidHom.mk' φ₀ fun y y' => inj₂ _ _ _ (hφ₀ (y + y'))
    ((isIota_iff_eq hB₂ _ _).2 (by
      rw [map_add (f := _), map_add (f := _), map_add (f := _), ← (isIota_iff_eq hB₂ _ _).1 (hφ₀ y), ← (isIota_iff_eq hB₂ _ _).1 (hφ₀ y')]))
  have hφ : ∀ y, GtPtF.IsIota (φ y) (m (iota hB₁ y)) := hφ₀
  refine ⟨φ, fun y g hg => ⟨m g, (hm _ _).2 rfl, ?_⟩, fun y => ?_⟩
  · rw [(isIota_iff_eq hB₁ _ _).1 hg]; exact hφ y
  refine GlobalTheory.KeyIota.eq_of_torsion_chars (F := F) fun k hk t ht => ?_
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hA D₁ A₁ G₁ hG₁ U₁ F k hk
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.TorsionIso.torsion_eq hL R I hA D₂ A₂ G₂ hG₂ U₂ F k hk
  have wp₁ := _root_.GlobalTheory.weilQk_existsUnique hL R I hA D₁ F k hk
  have wp₂ := _root_.GlobalTheory.weilQk_existsUnique hL R I hA D₂ F k hk
  have torp : ∀ p : QkPt D₁.toPre F k, f₁ p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U₁.toUnifPre.ext
    exact ((hf₁.1 p _).2 rfl w hw).1

  obtain ⟨gk, hgk⟩ := dv₁ k hk (iota hB₁ y)
  let p : QkPt D₁.toPre F k := ⟨y, gk, _, hgk, (isIota_iff_eq hB₁ _ _).2 rfl⟩
  obtain ⟨p', -, hpp', hp'⟩ := push k hk f₁ f₂ hf₁ hf₂ p
  have hyp' : p'.y = φ y := inj₂ _ _ _ hp' (hφ y)

  have h0 : k • torusPt D₁.toPre F (Additive.ofMul t) = iota hB₁ 0 := by
    rw [← map_nsmul, ← ofMul_pow, ht, ofMul_one, map_zero, map_zero]
  let q : QkPt D₁.toPre F k := qkMk hB₁ 0 (torusPt D₁.toPre F (Additive.ofMul t)) h0
  have hq : IsTor t q.g := (isTor_iff _ _).2 (isTorusPtF_torusPt t)
  obtain ⟨q', hqg, hqq', hq'i⟩ := push k hk f₁ f₂ hf₁ hf₂ q
  have hq'0 : q'.y = 0 := inj₂ _ _ _ hq'i ((isIota_iff_eq hB₂ _ _).2 (by
    show m (iota hB₁ 0) = iota hB₂ 0
    simp only [map_zero]))
  have hq'tor : IsTor (t.comp (AddMonoidHom.toMultiplicative h)) q'.g := tor t q.g q'.g hq ((hm _ _).2 hqg)

  have ec := _root_.GlobalTheory.EndCalc.end_calculus hL R I hA D₁ A₁ G₁ hG₁ U₁ F E E E
  have adE := ec.2.1
  choose aEf haE huE using ec.1
  let aE : GtPtF D₁.toPre F →+ GtPtF D₁.toPre F := AddMonoidHom.mk' aEf fun x x' => (isAdd_iff_eq _ _ _).1
    (adE x x' (x + x') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (haE x) (haE x') (haE _))
  have hqE0 : k • aE q.g = iota hB₁ 0 := by
    rw [← map_nsmul]
    show aE (k • torusPt D₁.toPre F (Additive.ofMul t)) = _
    simp only [h0, map_zero]
  let qE : QkPt D₁.toPre F k := qkMk hB₁ 0 (aE q.g) hqE0
  have hqEtor : IsTor (t.comp (AddMonoidHom.toMultiplicative E.h)) qE.g := ec.2.2.1 t q.g qE.g hq (haE q.g)
  have hFu := (GlobalTheory.UT.functorial_of_unif R I hA D₁ A₁ G₁ hG₁ U₁).2 E E' hE
  have hqE : f₁ qE = f₁ q ≫ E.aA := ((hf₁.1 _ _).1 ((hFu.2 F).2.2 k hk q qE (f₁ q)
    (by show (0 : D₁.toPre.X) = E'.h 0; rw [map_zero]) (haE q.g) ((hf₁.1 _ _).2 rfl))).symm

  have w₁ := (hf₁.2.2.2.2 _ _ _).1 ((wp₁ qE p).2 (t.comp (AddMonoidHom.toMultiplicative E.h)) rfl hqEtor)
  rw [hqE, ← Category.comp_id (f₁ p)] at w₁
  have w₂ := (_root_.GlobalTheory.Mum.Two.weilIs_iff_of_lbIso _ A₁ A₂ A₁ c c E.aA (𝟙 _) hc hc E.homA inferInstance hW F _ k (f₁ q) (f₁ p)
    (torp q) (torp p) _).2 w₁
  rw [← hqq', ← hpp'] at w₂
  have w₃ := (hf₂.2.2.2.2 _ _ _).2 w₂
  have e := (wp₂ q' p').1.unique w₃ ((wp₂ q' p').2 _ hq'0 hq'tor)
  rw [hyp'] at e
  exact e.symm

end GlobalTheory.Mum.Two
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameDomain
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.SiegelTheta

theorem transp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : GAd σ ((1 : E) • J.map σ)) :
    ∃ a' : UA σ J, (a' : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = HA.mat (AF F) σ ((1 : E) • J.map σ) a := by
  have e := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ (c := (1 : E)) one_ne_zero
  refine ⟨⟨HA.mat (AF F) σ ((1 : E) • J.map σ) a, ?_⟩, rfl⟩
  have : HA.mat (AF F) σ ((1 : E) • J.map σ) a ∈ HR (AF F) σ ((1 : E) • J.map σ) := a.2
  rw [← e] at this
  exact this

theorem ht_bdd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) {C₀ K : Set (GAd σ J)} (hC₀ : IsCompact C₀) (hK : IsCompact K) :
    ∃ B : ℝ, ∀ x ∈ C₀, ∀ k ∈ K, (heightGL F (HA.mat (AF F) σ J (x * k)) : ℝ) ≤ B := by
  have hc : Continuous fun q : GAd σ J × GAd σ J => (heightGL F (HA.mat (AF F) σ J (q.1 * q.2)) : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp (continuous_subtype_val.comp (continuous_mul : Continuous fun p : GAd σ J × GAd σ J => p.1 * p.2)))
  obtain ⟨B, hB⟩ := ((hC₀.prod hK).image hc).bddAbove
  exact ⟨B, fun x hx k hk => hB ⟨(x, k), ⟨hx, hk⟩, rfl⟩⟩

end GlobalTheory.SiegelTheta

namespace GlobalTheory.SiegelTheta

theorem theta_le_seminorm_height_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ) (hP : IsPair B M χX χW om r s r' s') (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∀ (Ω C₀ : Set (GAd σ ((1 : E) • X.J.map σ))) (K : Subgroup (GAd σ ((1 : E) • X.J.map σ))) (c : ℝ),
      IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GAd σ ((1 : E) • X.J.map σ))) → 0 < c →
      (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        a⁻¹ * p * a ∈ C₀) →
      ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ (N : ℕ) (C : ℝ) (T : Finset (ℕ × ℕ)),
        ∀ (f : SInf F (Fin n × Fin d)) (h : UA σ W.J) (g : UA σ X.J), ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
          GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ k ∈ K,
          g.1 = HA.mat (AF F) σ ((1 : E) • X.J.map σ) (p * a * k) →
          ‖theta om (pureA F f φ) g h‖ ≤
            C * (T.sup (schwartzSeminormFamily ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)) f *
              (ht h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hfr Ω C₀ K c hΩ hC₀ hK hc hconj φ hφ
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hP.base.cm
  obtain ⟨Bd, hBd⟩ := ht_bdd ((1 : E) • X.J.map σ) hC₀ hK
  let I := {q : UA σ W.J × UA σ X.J × GAd σ ((1 : E) • X.J.map σ) × (Fin r₀ → ℝ) × GAd σ ((1 : E) • X.J.map σ) ×
      GAd σ ((1 : E) • X.J.map σ) // q.2.2.1 ∈ Ω ∧ q.2.2.2.1 ∈ GlobalTheory.SiegelSet.cone r₀ c ∧
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf q.2.2.2.1 q.2.2.2.2.1 ∧ q.2.2.2.2.2 ∈ K ∧
      (q.2.1 : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) (q.2.2.1 * q.2.2.2.2.1 * q.2.2.2.2.2)}
  have hT := fun q : I => _root_.GlobalTheory.ThetaKernelCont.theta_pureA_clm F E σ B n d X W M χX χW om r s r' s' hP φ hφ q.1.2.1 q.1.1
  choose T hT using hT
  let P : I → ℝ := fun q => ∏ i, q.1.2.2.2.1 i ^ (Module.finrank ℚ F * d)
  have hP0 : ∀ q : I, 0 < P q := fun q => Finset.prod_pos fun i _ => pow_pos (q.2.2.1.1 i) _
  have hpt : ∀ f : SchwartzMap (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ, ∃ (N : ℕ) (C : ℝ), ∀ q : I,
      ‖((P q)⁻¹ • T q) f‖ ≤ C * (ht q.1.1 : ℝ) ^ N := by
    intro f
    obtain ⟨C₁, k₁, h₁⟩ := GlobalTheory.T.siegel_set_witt_frame_schwartz_bound F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hfr c hc (pureA F f φ)
      (Submodule.subset_span ⟨f, φ, hφ, rfl⟩)
    refine ⟨k₁, |C₁| * (max Bd 0) ^ k₁, fun q => ?_⟩
    obtain ⟨⟨h, g, p, t, a, k⟩, hp, htc, ha, hk, hg⟩ := q
    obtain ⟨a', ha'⟩ := transp hσ X.J a
    have hy : ((a'⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)) =
        HA.mat (AF F) σ ((1 : E) • X.J.map σ) ((a⁻¹ * p * a) * k) := by
      have : (a⁻¹ * p * a) * k = a⁻¹ * (p * a * k) := by group
      rw [this]
      change (a' : GL (Fin n) (AE F E))⁻¹ * (g : GL (Fin n) (AE F E)) = _
      rw [ha', hg]
      rfl
    have hty : (ht (a'⁻¹ * g) : ℝ) ≤ max Bd 0 := by
      refine le_trans ?_ (le_max_left _ _)
      show (heightGL F ((a'⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)) : ℝ) ≤ Bd
      rw [hy]
      exact hBd _ (hconj p hp t htc a ha) k hk
    have hb := h₁ t htc a ha a' ha' (a'⁻¹ * g) h
    rw [mul_inv_cancel_left] at hb
    have hPq : 0 < ∏ i, t i ^ (Module.finrank ℚ F * d) := Finset.prod_pos fun i _ => pow_pos (htc.1 i) _
    show ‖((∏ i, t i ^ (Module.finrank ℚ F * d))⁻¹ • T _) f‖ ≤ _
    rw [ContinuousLinearMap.smul_apply, ← hT, norm_smul, Real.norm_of_nonneg (inv_pos.2 hPq).le]
    have h0 : (0 : ℝ) ≤ (ht h : ℝ) := NNReal.coe_nonneg _
    have hy0 : (0 : ℝ) ≤ (ht (a'⁻¹ * g) : ℝ) := NNReal.coe_nonneg _
    calc (∏ i, t i ^ (Module.finrank ℚ F * d))⁻¹ * ‖theta om (pureA F f φ) g h‖
        ≤ (∏ i, t i ^ (Module.finrank ℚ F * d))⁻¹ * (C₁ * ((ht (a'⁻¹ * g) : ℝ) * ht h) ^ k₁ *
            ∏ i, t i ^ (Module.finrank ℚ F * d)) := mul_le_mul_of_nonneg_left hb (inv_pos.2 hPq).le
      _ = C₁ * ((ht (a'⁻¹ * g) : ℝ) * ht h) ^ k₁ := by field_simp
      _ ≤ |C₁| * ((max Bd 0) * ht h) ^ k₁ :=
          mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (mul_nonneg hy0 h0) (mul_le_mul_of_nonneg_right hty h0) _)
            (pow_nonneg (mul_nonneg hy0 h0) _) (abs_nonneg _)
      _ = |C₁| * (max Bd 0) ^ k₁ * (ht h : ℝ) ^ k₁ := by rw [mul_pow]; ring
  obtain ⟨N, C, S, hN⟩ := _root_.GlobalTheory.schwartz_family_uniform_bound (Fin n × Fin d → mixedEmbedding.mixedSpace F) I (fun q => (P q)⁻¹ • T q)
    (fun q => (ht q.1.1 : ℝ)) (fun q => NNReal.coe_nonneg _) hpt
  refine ⟨N, C, S, fun f h g p hp t htc a ha k hk hg => ?_⟩
  let q : I := ⟨(h, g, p, t, a, k), hp, htc, ha, hk, hg⟩
  have e1 : theta om (pureA F f φ) g h = P q • ((P q)⁻¹ • T q f) := by
    rw [smul_smul, mul_inv_cancel₀ (hP0 q).ne', one_smul]
    exact hT q f
  have e2 := hN q f
  simp only [ContinuousLinearMap.smul_apply] at e2
  rw [e1, norm_smul, Real.norm_of_nonneg (hP0 q).le]
  calc P q * ‖(P q)⁻¹ • T q f‖ ≤ P q * (C * (S.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N) :=
        mul_le_mul_of_nonneg_left e2 (hP0 q).le
    _ = _ := by ring

end GlobalTheory.SiegelTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlas
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory

theorem formCalculus : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n),
    A.IsForm 1 ∧ (∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α + β) ∧ A.IsForm (α * β) ∧ A.IsForm (c • α) ∧
      A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) ∧ A.del (α + β) = A.del α + A.del β ∧ A.dbar (α + β) = A.dbar α + A.dbar β ∧
      A.del (c • α) = c • A.del α ∧ A.dbar (c • α) = c • A.dbar α) ∧
    (∀ (w : A.Pt → Ev n) (β : A.Fld), A.IsForm (fld A w) → A.IsForm β →
      A.del (fld A w * β) = A.del (fld A w) * β + fld A w * A.del β ∧ A.dbar (fld A w * β) = A.dbar (fld A w) * β + fld A w * A.dbar β) ∧
    (∀ (ι : Type) (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ), (∀ i, A.IsForm (fld A (w i))) → A.IsForm (evalF A w P) ∧
      ((∀ i, A.del (fld A (w i)) = 0) → A.del (evalF A w P) = 0) ∧ ((∀ i, A.dbar (fld A (w i)) = 0) → A.dbar (evalF A w P) = 0)) ∧
    ∀ (M' : Type) [TopologicalSpace M'] (n' : ℕ) (A' : HolAtlas M' n') (f : M' → M), A.IsHolo A' f →
      A.pullback A' f 1 = 1 ∧ ∀ (c : ℂ) (α β : A.Fld), A.pullback A' f (α + β) = A.pullback A' f α + A.pullback A' f β ∧
        A.pullback A' f (α * β) = A.pullback A' f α * A.pullback A' f β ∧ A.pullback A' f (c • α) = c • A.pullback A' f α ∧
        (A.IsForm α → A'.IsForm (A.pullback A' f α) ∧ A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧
          A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α)) := by
  intro M _ n A
  refine ⟨(_root_.GlobalTheory.CxForm.HolAtlas.isForm_algebra M n A).1, fun c α β hα hβ => ?_, fun w β hw hβ => GlobalTheory.T.del_dbar_leibniz_evenForm_mul M n A w β hw hβ, fun ι w P hw => ?_,
    fun M' _ n' A' f hf => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (_root_.GlobalTheory.CxForm.HolAtlas.isForm_algebra M n A).2 c α β hα hβ
    obtain ⟨d1, d2⟩ := _root_.GlobalTheory.CxForm.isForm_del_dbar M n A α hα
    obtain ⟨e1, e2, e3, e4⟩ := (_root_.GlobalTheory.CxForm.HolAtlas.del_dbar_linear M n A).2 c α β hα hβ
    exact ⟨h1, h2, h3, d1, d2, e1, e2, e3, e4⟩
  · induction P using MvPolynomial.induction_on with
    | C r =>
      have e : evalF A w (C r) = ((r : ℂ) • (1 : A.Fld)) := by
        funext x
        simp [evalF, fld, Algebra.algebraMap_eq_smul_one]
        first | rfl | exact Subalgebra.coe_smul _ _ _ | (rw [SetLike.val_smul]; simp) | simp [Subalgebra.coe_algebraMap]
      have h1 := (_root_.GlobalTheory.CxForm.HolAtlas.isForm_algebra M n A).1
      have hf := ((_root_.GlobalTheory.CxForm.HolAtlas.isForm_algebra M n A).2 (r : ℂ) 1 1 h1 h1).2.2
      obtain ⟨⟨z1, z2⟩, hl⟩ := _root_.GlobalTheory.CxForm.HolAtlas.del_dbar_linear M n A
      obtain ⟨-, -, s1, s2⟩ := hl (r : ℂ) 1 1 h1 h1
      rw [e]
      exact ⟨hf, fun _ => by rw [s1, z1, smul_zero], fun _ => by rw [s2, z2, smul_zero]⟩
    | add p q hp hq =>
      have e : evalF A w (p + q) = evalF A w p + evalF A w q := by
        funext x
        simp [evalF, fld]
      obtain ⟨hp1, hp2, hp3⟩ := hp
      obtain ⟨hq1, hq2, hq3⟩ := hq
      obtain ⟨a1, -, -⟩ := (_root_.GlobalTheory.CxForm.HolAtlas.isForm_algebra M n A).2 1 _ _ hp1 hq1
      obtain ⟨l1, l2, -, -⟩ := (_root_.GlobalTheory.CxForm.HolAtlas.del_dbar_linear M n A).2 1 _ _ hp1 hq1
      rw [e]
      exact ⟨a1, fun h => by rw [l1, hp2 h, hq2 h, add_zero], fun h => by rw [l2, hp3 h, hq3 h, add_zero]⟩
    | mul_X p i hp =>
      have e : evalF A w (p * X i) = evalF A w p * fld A (w i) := by
        funext x
        simp [evalF, fld]
      obtain ⟨hp1, hp2, hp3⟩ := hp
      obtain ⟨-, a2, -⟩ := (_root_.GlobalTheory.CxForm.HolAtlas.isForm_algebra M n A).2 1 _ _ hp1 (hw i)
      obtain ⟨b1, b2⟩ := GlobalTheory.T.del_dbar_leibniz_evenForm_mul M n A (fun x => aeval (fun i => w i x) (p.map (algebraMap ℝ ℂ))) (fld A (w i)) hp1 (hw i)
      rw [e]
      refine ⟨a2, fun h => ?_, fun h => ?_⟩
      · change A.del (fld A _ * fld A (w i)) = 0
        rw [b1]
        change A.del (evalF A w p) * _ + _ = 0
        rw [hp2 h, h i, zero_mul, mul_zero, add_zero]
      · change A.dbar (fld A _ * fld A (w i)) = 0
        rw [b2]
        change A.dbar (evalF A w p) * _ + _ = 0
        rw [hp3 h, h i, zero_mul, mul_zero, add_zero]
  · refine ⟨funext fun x => map_one _, fun c α β => ⟨funext fun x => map_add _ _ _, funext fun x => map_mul _ _ _,
      funext fun x => map_smul (pull _) c _, fun hα => ?_⟩⟩
    obtain ⟨d1, d2⟩ := _root_.GlobalTheory.CxForm.isForm_del_dbar M n A α hα
    exact ⟨_root_.GlobalTheory.PullbackForm.isForm_pullback M M' n n' A A' f α hf hα, _root_.GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback M M' n n' A A' f α hf hα d1 d2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentValuePullbackCrystallineFormDualNumbers
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ParPt

theorem tanVal_pullForm_ofModule : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) (A' : Over (Sp R')) (φ : A'.left ⟶ A.left) (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (v : epsR R' ⟶ A') (hy : (v.left ≫ φ) ≫ A.hom ≫ 𝟙 (Sp R) = spMap (algebraMap R (DualNumber R'))) (f : Form (A.hom ≫ 𝟙 (Sp R))), tanVal v (m.pullForm f) = TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val (v.left ≫ φ) hy f.1) := by
  intro R R' _ _ _ A A' φ m v hy f
  let E := SqExt.ofModule R R' R'
  let E' := SqExt.dual R'
  have hy' := pt_w v
  have hc : ∀ r : R, RingHom.id (DualNumber R') (algebraMap R (DualNumber R') r) =
      algebraMap R' (DualNumber R') (algebraMap R R' r) := fun r =>
    IsScalarTower.algebraMap_apply R R' (DualNumber R') r
  have e₀ : spMap (RingHom.id R') ≫ spMap (E.π : E.C →+* E.B) ≫ v.left ≫ φ =
      (spMap (E'.π : E'.C →+* E'.B) ≫ v.left) ≫ φ := by
    rw [Category.assoc, ← Category.assoc, ← Cris.spMap_comp]
    rfl
  have e : spMap (RingHom.id (DualNumber R')) ≫ v.left ≫ φ = v.left ≫ φ := by
    rw [Cris.spMap_id, Category.id_comp]
  let Φ : E.thick _ (E.red_w hy) ⟶ m.obj (E'.thick _ (E'.red_w hy')) :=
    { φ := { RingHom.id (DualNumber R') with commutes' := hc }
      φ₀ := RingHom.id R'
      comm := fun b => rfl
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun a ha => ha
      pt := e₀ }
  let a : Thick.triv E.C _ hy ⟶ m.obj (Thick.triv E'.C _ hy') :=
    Thick.trivHom { RingHom.id (DualNumber R') with commutes' := hc } e
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hy')) :=
    Thick.trivHom { RingHom.id R' with commutes' := fun _ => rfl } e₀
  have k1 := Form.ev_sq f a (m.functor.map (E'.idHom hy')) (E.idHom hy) Φ rfl rfl fun _ => rfl
  have k2 := Form.ev_sq f b (m.functor.map (E'.secHom (E'.red_w hy') E'.i E'.π_i))
    (E.secHom (E.red_w hy) E.i E.π_i) Φ rfl rfl fun c => rfl
  have k : E'.val v.left hy' (m.pullForm f).1 = E.val (v.left ≫ φ) hy f.1 :=
    (congrArg₂ (fun u v : E'.C => u - v) k2 k1).trans
      (add_sub_add_right_eq_sub (G := E'.C) _ _ _)
  rw [tanVal_apply]
  exact congrArg (TrivSqZeroExt.snd (R := R')) k

end GlobalTheory.ParPt
end
end

