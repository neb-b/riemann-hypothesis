module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SiegPairPBNonempty
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3050
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLevelStructureAtGeometricPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleLevelStructure_at_geometricPoint : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ l : D.La → (Over.mk x ⟶ o.A), IsEtLevOver o w0 r l := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.exists_etLevOver_geomPt) | (exact GlobalTheory.UPel.HT.EtLev.exists_etLevOver_geomPt) | (intros; apply GlobalTheory.UPel.HT.EtLev.exists_etLevOver_geomPt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepPrincipalSiegelAdjointOrderAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActSieg

section Pull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
  {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem one_left (h : IsGrpPullback A' A f φ) : (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  have e : (1 : A' ⟶ A').left ≫ φ = (1 : Over.mk (A'.hom ≫ f) ⟶ A).left :=
    congrArg (fun q => q.left) (map_one (pushHom h A'))
  rw [e, Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left,
    ← Category.assoc, h.1.w]
  rfl

theorem lift_one_id (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (1 : A' ⟶ A') (𝟙 A')
    (Z := A) φ (1 : A ⟶ A) (𝟙 A) (by exact (Category.id_comp _).trans (one_left h)) (by simp)
  exact (Category.id_comp _).symm.trans this

theorem lift_id_one (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (1 : A ⟶ A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (𝟙 A') (1 : A' ⟶ A')
    (Z := A) φ (𝟙 A) (1 : A ⟶ A) (by simp) (by exact (Category.id_comp _).trans (one_left h))
  exact (Category.id_comp _).symm.trans this

theorem lift_swap (sq : IsSquare φ φ₂) :
    (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd A A) (fst A A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (A ⊗ A).hom)) (T' := A' ⊗ A') (𝟙 _) (snd A' A') (fst A' A')
    (Z := A ⊗ A) φ₂ (snd A A) (fst A A) (by exact (Category.id_comp _).trans sq.2.symm)
    (by exact (Category.id_comp _).trans sq.1.symm)
  exact (Category.id_comp _).symm.trans this

end Pull

section Obj

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B}

def onPull (c : SiegPre h M ζ s) (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ c.A.left)
    (φ₂ : (A' ⊗ A').left ⟶ (c.A ⊗ c.A).left) (pb : IsGrpPullback A' c.A f φ) (sq : IsSquare φ φ₂) :
    SiegPre h M ζ (f ≫ s) :=
  haveI : IsCommMonObj A' := (GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab pb).comm
  { A := A'
    ab := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab pb
    P := c.P.pull φ₂
    isLB := pull_isLB c.isLB φ₂
    rig₁ := by
      obtain ⟨t, ht⟩ := c.rig₁
      exact gen_chartPull (chartPullLinComb c.P φ₂ _ _ _ φ fun _ => lift_one_id pb sq) t ht
    rig₂ := by
      obtain ⟨t, ht⟩ := c.rig₂
      exact gen_chartPull (chartPullLinComb c.P φ₂ _ _ _ φ fun _ => lift_id_one pb sq) t ht
    symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P _ _ rfl) (chartPullLinComb c.P _ _ _ _ φ₂ fun _ => lift_swap sq) c.symm
    lev := fun a => GlobalTheory.SiegelPull.secPull pb (c.lev a)
    lev_add := fun a b => GlobalTheory.SiegelPull.push_injective pb _ (by
      rw [map_mul, GlobalTheory.SiegelPull.push_secPull', GlobalTheory.SiegelPull.push_secPull', GlobalTheory.SiegelPull.push_secPull', c.lev_add, MonObj.comp_mul])
    lev_tors := fun a => GlobalTheory.SiegelPull.push_injective pb _ (by
      rw [map_pow, map_one, GlobalTheory.SiegelPull.push_secPull', ← MonObj.comp_pow, c.lev_tors, MonObj.comp_one])
    geom := fun k _ _ x β z hx hz => by
      obtain ⟨g₁, g₂, g₃⟩ := c.geom k (x ≫ f) β z (by rw [Category.assoc]; exact hx) hz
      refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
      · rw [← (GlobalTheory.SiegelPull.push_injective pb (Over.mk x)).eq_iff, GlobalTheory.SiegelPull.push_secPull, map_one]
        rfl
      · obtain ⟨a, ha⟩ := g₂ (pushHom pb (Over.mk x) g) (by
          have := congrArg (pushHom pb (Over.mk x)) hg
          rw [map_pow, map_one] at this
          exact this)
        exact ⟨a, GlobalTheory.SiegelPull.push_injective pb _ ((GlobalTheory.SiegelPull.push_secPull pb _ _).trans ha)⟩
      · exact (weilIs_grpPullback_of_comm S S' c.A A' f φ _ _ (pull_isLB c.isLB _)
          (pull_isLB (pull_isLB c.isLB φ₂) _) pb
          (GlobalTheory.SiegelPull.diag_iso sq (ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ (pull_isLB c.isLB φ₂))) (Over.mk x) M _ _ _ _ _
          (congrArg (fun q => q.left) (GlobalTheory.SiegelPull.push_secPull pb (c.lev a) (Over.mk x)).symm)
          (congrArg (fun q => q.left) (GlobalTheory.SiegelPull.push_secPull pb (c.lev b) (Over.mk x)).symm)).2 (g₃ a b) }

theorem onPull_lev (c : SiegPre h M ζ s) (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ c.A.left)
    (φ₂ : (A' ⊗ A').left ⟶ (c.A ⊗ c.A).left) (pb : IsGrpPullback A' c.A f φ) (sq : IsSquare φ φ₂)
    (a : Fin h ⊕ Fin h → ℤ) : ((onPull c A' φ φ₂ pb sq).lev a).left ≫ φ = f ≫ (c.lev a).left :=
  GlobalTheory.SiegelPull.secPull_left pb _

theorem onPull_siegPB (c : SiegPre h M ζ s) (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ c.A.left)
    (φ₂ : (A' ⊗ A').left ⟶ (c.A ⊗ c.A).left) (pb : IsGrpPullback A' c.A f φ) (sq : IsSquare φ φ₂) :
    SiegPB (onPull c A' φ φ₂ pb sq) c f :=
  ⟨φ, φ₂, pb, sq, ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ (pull_isLB c.isLB φ₂), onPull_lev c A' φ φ₂ pb sq⟩

end Obj

theorem adj_of_lbIso {S : Scheme.{0}} {A : Over S} [GrpObj A] {O : Type} [Ring O] {P Q : LB (A ⊗ A).left}
    (hP : P.IsLB) (hQ : Q.IsLB) (e : LBIso P Q) {bar : O → O} {act : O → (A ⟶ A)} (h : Adj A P bar act) :
    Adj A Q bar act := by
  intro a
  have ha := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).2 (h a)
  have he := (GlobalTheory.CechPic.cls_eq_iff hP hQ).2 e
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hQ _) (pull_isLB hQ _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hQ, ← he]
  exact ha

theorem exists_rep : ∀ (h' M : ℕ), 1 ≤ h' → 3 ≤ M → Odd M → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (eO : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range eO) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d₀ → ∑ i, ∑ j, W i j • (eO j * bar (eO i)) = (d₀ : O) → ∃ (H : Scheme.{0}) (sH : H ⟶ Sp (cycAway M)) (zH : SiegPre h' M (zetaAway M) sH) (actH : O → (zH.A ⟶ zH.A)), zH.Principal ∧ IsRAct zH.A actH ∧ Adj zH.A zH.P bar actH ∧ IsQProjOver sH ∧ IsLocallyNoetherian H ∧ ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), z.Principal → IsRAct z.A act → Adj z.A z.P bar act → ∃! g : S ⟶ H, g ≫ sH = t ∧ ActPB z act zH actH g := by
  intro h' M hh hM hodd O _ bar r eO W d₀ hbar hspan hW hd hsum
  have hM0 : M ≠ 0 := by omega
  obtain ⟨F⟩ := exists_sFam_cycAway h' M hh hM hodd
  haveI : IsDedekindDomain (cycAway M) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway M
  haveI : IsLocallyNoetherian F.X := GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth (cycAway M) F.X F.s F.qproj
  obtain ⟨R, hRf, -⟩ := GlobalTheory.T.adjointActions_order_finite_unramified_scheme F.X F.univ.A F.univ.P F.univ.ab F.univ.isLB F.univ.rig₁ F.univ.rig₂
    F.univ.symm F.princ.1 O bar r eO W d₀ hbar hspan hW hd hsum
  have hq : IsQProjOver (R.π ≫ F.s) :=
    GlobalTheory.isQProjOver_comp_of_isFinite_noetherian (cycAway M) R.H F.X R.π F.s hRf F.qproj
  have hzH : SiegPB (onPull F.univ R.AH R.φ R.φ₂ R.pb R.sq) F.univ R.π := onPull_siegPB F.univ R.AH R.φ R.φ₂ R.pb R.sq
  refine ⟨R.H, R.π ≫ F.s, onPull F.univ R.AH R.φ R.φ₂ R.pb R.sq, R.act,
    (GlobalTheory.siegPre_pullback h' M (cycAway M) (zetaAway M) F.X R.H F.s (R.π ≫ F.s) R.π F.univ rfl).2 _ hzH F.princ,
    R.isAct, R.adj, hq, GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth (cycAway M) R.H _ hq, ?_⟩
  intro S t z act hz hact hadj
  obtain ⟨f, ⟨hfs, ⟨φz, φ₂z, pbz, sqz, isoz, levz⟩⟩, hfu⟩ := _root_.GlobalTheory.SiegFamAll.existsUnique_classify h' M hh hM hodd F S t z hz
  have hadj' : Adj z.A (F.univ.P.pull φ₂z) bar act := adj_of_lbIso z.isLB (pull_isLB F.univ.isLB _) isoz hadj
  obtain ⟨g, ⟨hgπ, ψ, hψ, hψφ, hψa⟩, hgu⟩ := R.rep S f z.A φz φ₂z act pbz sqz hact hadj'
  have sqψ := GlobalTheory.LamPull.exists_isSquare hψ.1.w
  have e₂ := GlobalTheory.LamPull.isSquare_unique (GlobalTheory.TChart.AbPol.isSquare_comp sqψ R.sq) (by rw [hψφ]; exact sqz)
  have iso : LBIso z.P ((F.univ.P.pull R.φ₂).pull
      (lift (pushPt hψ.1.w (fst z.A z.A)) (pushPt hψ.1.w (snd z.A z.A))).left) := by
    refine (GlobalTheory.CechPic.cls_eq_iff z.isLB (pull_isLB (pull_isLB F.univ.isLB _) _)).1 ?_
    rw [(GlobalTheory.CechPic.cls_eq_iff z.isLB (pull_isLB F.univ.isLB _)).2 isoz, ← e₂, GlobalTheory.CechPic.cls_pull F.univ.isLB,
      GlobalTheory.CechPic.cls_pull (pull_isLB F.univ.isLB _), GlobalTheory.CechPic.cls_pull F.univ.isLB, GlobalTheory.CechPic.pull_comp]
  have hlev : ∀ a, (z.lev a).left ≫ ψ = g ≫ ((onPull F.univ R.AH R.φ R.φ₂ R.pb R.sq).lev a).left := fun a => by
    apply R.pb.1.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg ((z.lev a).left ≫ ·) hψφ).trans ((levz a).trans
        ((congrArg (· ≫ (F.univ.lev a).left) hgπ.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (g ≫ ·) (onPull_lev F.univ R.AH R.φ R.φ₂ R.pb R.sq a).symm).trans (Category.assoc _ _ _).symm)))))
    · exact ((Category.assoc _ _ _).trans ((congrArg _ hψ.1.w).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ g) (Over.w (z.lev a)))))).trans ((Category.id_comp g).trans ((Category.comp_id g).symm.trans
        ((congrArg (g ≫ ·) (Over.w ((onPull F.univ R.AH R.φ R.φ₂ R.pb R.sq).lev a)).symm).trans
        (Category.assoc _ _ _).symm)))
  refine ⟨g, ⟨by rw [← Category.assoc, hgπ, hfs], ψ, _, hψ, sqψ, iso, hlev, hψa⟩, ?_⟩
  rintro g' ⟨hg's, ψ', ψ₂', hψ', sqψ', iso', hlev', hact'⟩
  have hlev'' : ∀ a, (z.lev a).left ≫ ψ' ≫ R.φ = (g' ≫ R.π) ≫ (F.univ.lev a).left := fun a => by
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ R.φ) (hlev' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (g' ≫ ·) (onPull_lev F.univ R.AH R.φ R.φ₂ R.pb R.sq a)).trans (Category.assoc _ _ _).symm)))
  have iso'' : LBIso z.P (F.univ.P.pull (ψ₂' ≫ R.φ₂)) :=
    GlobalTheory.TChart.AbLevel.lbIso_comp F.univ.isLB (pull_isLB F.univ.isLB _) z.isLB
      (ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ (pull_isLB F.univ.isLB R.φ₂)) iso'
  have hf' : g' ≫ R.π = f := hfu _ ⟨by rw [Category.assoc]; exact hg's,
    ψ' ≫ R.φ, ψ₂' ≫ R.φ₂, hψ'.comp R.pb, GlobalTheory.TChart.AbPol.isSquare_comp sqψ' R.sq, iso'', hlev''⟩
  have s' : GlobalTheory.SiegLev.SRelBy z F.univ 1 1 f (ψ' ≫ R.φ) :=
    ⟨(hψ'.comp R.pb).congr hf' rfl, ⟨ψ₂' ≫ R.φ₂, GlobalTheory.TChart.AbPol.isSquare_comp sqψ' R.sq, iso''⟩,
      fun a => by simpa only [pow_one, hf'] using hlev'' a⟩
  have s : GlobalTheory.SiegLev.SRelBy z F.univ 1 1 f φz :=
    ⟨pbz, ⟨φ₂z, sqz, isoz⟩, fun a => by simpa only [pow_one] using levz a⟩
  have hφeq : ψ' ≫ R.φ = φz := GlobalTheory.SiegRigid.eq_of_sRelBy h' M M 1 (cycAway M) (cycAway M) (cycBase hM0)
    (zetaAway M) F.X S F.s t F.univ z f _ _ hM hodd F.princ s' s
  exact hgu g' ⟨hf', ψ', hψ', hφeq, hact'⟩

end GlobalTheory.ActSieg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleChartUnitaryBoundaryPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

theorem uPre_of_boundary {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (hpq : 1 ≤ Dw.p + Dw.q)
    (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) (hns : NoSelfInt H.bar (min Dw.p Dw.q) φ)
    {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData)
    {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S)
    (hP : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD) (hS : SepB Xo c φ j)
    (x : S) (hx : x ∉ Set.range j) : UPre Xo c φ j BD d x :=
  GlobalTheory.T.exists_tripleChart_unitary_boundary_pointRigid Xo c φ hpq hφ hns zs i OZ N d J π j BD hP hS x hx

end GlobalTheory.UChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_closed_immersion_genModel_to_fibre : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (R' : Type) [CommRing R'] [Algebra ℚ R'] (φ : R →+* R') (gb : GBase D.toG R'), gb.ρ = φ b.ρ → (∀ i, gb.t i = φ.comp (b.t i)) → ∀ (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (X : GenModel gb N), ∃ j : X.X ⟶ pullback M.s (spMap φ), IsOpenImmersion j ∧ IsClosedImmersion j ∧ j ≫ pullback.snd _ _ = X.s ∧ IsGPull X.univ M.univ (j ≫ pullback.fst _ _) := by
  first | (exact @GlobalTheory.UPel.HT.GenCmp.genModel_eq_genericFibre) | (exact GlobalTheory.UPel.HT.GenCmp.genModel_eq_genericFibre) | (intros; apply GlobalTheory.UPel.HT.GenCmp.genModel_eq_genericFibre  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelToroidalIntegralHolds
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem siegelToroidalIntegral_holds : GlobalTheory.Published.SiegelToroidalIntegral :=
  _root_.GlobalTheory.siegelToroidalIntegral_of_polCharts _root_.GlobalTheory.SiegJoin.siegelToroidalPolCharts

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem RepFam.smoothOfRelativeDimension : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → SmoothOfRelativeDimension (D.a * (D.n - 1)) F.s := by
  intro p _ D R _ _ b N hN hNp F hq
  have hlft : LocallyOfFiniteType F.s := by
    obtain ⟨M, i, hi, hqc, hi'⟩ := hq
    have := isProper_str R M
    rw [← hi']
    infer_instance
  have hsm : Smooth F.s := by
    refine _root_.GlobalTheory.SmoothCrit.smooth_of_artinian_lift R F.X F.s hlft ?_
    intro C C₀ _ _ _ _ π hπ hker t x₀ hx
    obtain ⟨β, rfl⟩ : ∃ β : R →+* C, t = spMap β :=
      ⟨(Spec.preimage t).hom, by simp [spMap]⟩
    have hcomp : spMap π ≫ spMap β = spMap (π.comp β) := by
      simp [spMap, ← Spec.map_comp]
    have hs₀ : x₀ ≫ F.s = spMap (π.comp β) := by rw [hx, hcomp]
    obtain ⟨o₀, ⟨m₀⟩⟩ := _root_.GlobalTheory.UPel.HT.BaseChange.exists_objMap p D R b N _ _ F.s _ F.univ x₀ hs₀
    obtain ⟨o', ⟨m'⟩⟩ := GlobalTheory.T.harrisTaylor_formally_smooth_squareZero_lift p D R b N hN hNp C C₀ π β hπ (by rw [← hker, pow_two]) o₀
    obtain ⟨x, ⟨hxs, ⟨mx⟩⟩, -⟩ := F.rep (Sp C) (spMap β) o'
    obtain ⟨mc⟩ := _root_.GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ o₀ o' F.univ (spMap π) x m' mx
    refine ⟨x, ?_, hxs⟩
    exact (F.rep (Sp C₀) (spMap (π.comp β)) o₀).unique
      ⟨by rw [Category.assoc, hxs, hcomp], ⟨mc⟩⟩ ⟨hs₀, ⟨m₀⟩⟩
  exact _root_.GlobalTheory.SmoothDimTangent.smoothOfRelativeDimension_of_universal_tangent R F.X F.s _ hsm (GlobalTheory.T.exists_universal_tangent_harrisTaylor_representingFamily p D R b N hN hNp F hq hsm)

end GlobalTheory.UPel.HT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToroidalSeparationOfBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoincTop

theorem uPoinStX_sep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ →
    ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∃ (Z : Scheme.{0}) (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z)
      (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : Xo.XF c ⟶ S)
      (BD : EffCartierData S), UPoinOnX Xo c φ zs i OZ N d J π j BD ∧ GlobalTheory.UChart.SepB Xo c φ j := by
  intro E _ _ _ H Dw hpq φ hφ hns l Xo c
  obtain ⟨C⟩ := _root_.GlobalTheory.UPoinc.uMinSt_holds E H Dw hpq l Xo c
  obtain ⟨d, J₀, hd, hJ₀, hval₀⟩ := _root_.GlobalTheory.UPoinc.uIdealSt_holds E H Dw hpq φ hφ l Xo c C
  haveI := C.ded
  haveI := C.iF_open
  have hgen := _root_.GlobalTheory.GenFibNormal.genericFibre_normal_projective_ample C.o c.F C.b C.inj C.Z C.z C.OZ C.proj C.normal C.OZ_lb C.OZ_ample
  obtain ⟨hprojZ, hnormZ, hOZlb, hOZamp⟩ := hgen
  let Z := pullback C.z (spMap C.b)
  let fZ : Z ⟶ C.Z := pullback.fst C.z (spMap C.b)
  let J : Z.IdealSheafData := J₀.comap fZ
  let W : Z.Opens := C.iF.opensRange
  have hWset : (W : Set Z) = Set.range C.iF := by simp [W]
  have hJ : ∀ x ∈ J.support, x ∉ Set.range C.iF := by
    intro x hx hxr
    rw [Scheme.IdealSheafData.support_comap] at hx
    obtain ⟨y, rfl⟩ := hxr
    exact hJ₀ _ hx ⟨y, rfl⟩
  have hval : UValOn Xo c C.iF φ J d := by
    intro W' _ _ _ hW ϖ hϖ χ y hy t tK htK hK P be hbe hmono
    obtain ⟨n, hn, hid⟩ := hval₀ W' hW ϖ hϖ (χ ≫ fZ) y
      (by rw [UCompact.i, ← Category.assoc, hy, Category.assoc]) t tK htK hK P be hbe hmono
    exact ⟨n, hn, by rw [GlobalTheory.PullAlong.idlAlong_comap_eq]; exact hid⟩
  obtain ⟨S, π, BD, hbl, hpS, hprop, hBD, hiso, hdS⟩ :=
    GlobalTheory.NormBlowupField.exists_normBl c.F Z (pullback.snd C.z (spMap C.b)) hprojZ hnormZ J W (by rw [hWset]; exact C.iF_dense)
      (fun x hx hxW => hJ x hx (by have h : x ∈ (W : Set Z) := hxW; rwa [hWset] at h))
  haveI := hiso
  let A : Xo.XF c ⟶ (π ⁻¹ᵁ W).toScheme := C.iF.isoOpensRange.hom ≫ inv (π ∣_ W)
  let j : Xo.XF c ⟶ S := A ≫ (π ⁻¹ᵁ W).ι
  have hjπ : j ≫ π = C.iF := by
    simp only [j, A, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    simp [W]
  have hrj : Set.range j = π ⁻¹' Set.range C.iF := by
    have hA : Function.Surjective A := A.surjective
    change Set.range ((π ⁻¹ᵁ W).ι ∘ A) = _
    rw [Set.range_comp, hA.range_eq, Set.image_univ, Scheme.Opens.range_ι, ← hWset]
    rfl
  have hjo : IsOpenImmersion j := inferInstance
  refine ⟨Z, pullback.snd C.z (spMap C.b), C.iF, C.OZ.pull fZ, C.N, d, J, S, π, j, BD, ⟨⟨hprojZ, hnormZ, C.iF_open,
    C.iF_dense, C.iF_over, hOZlb, hOZamp⟩, ⟨C.N_pos, ?_⟩, ?_, ⟨hd, hJ, hval⟩, ⟨hbl, hpS, hjo, ?_, hjπ, hrj.symm, hBD, ?_⟩, ?_⟩, ?_⟩
  · intro Y f hf hY
    have h := C.omega Y f hf hY
    exact LBIso.trans (pull_isLB hOZlb f) (pull_isLB C.OZ_lb _) (LB.isLB_linComb hY _ _)
      (LBIso.symm (GlobalTheory.FibreNef.lbIso_pull_comp C.OZ_lb fZ f)) h
  · intro R _ _ _ hR t hP y hy σ hσ
    obtain ⟨ξ₀, h₁, h₂⟩ := C.ext R hR t hP y hy (σ ≫ spMap C.b) (by rw [← Category.assoc, hσ, Category.assoc])
    refine ⟨pullback.lift ξ₀ σ (by rw [h₂]), ?_, pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]; exact h₁
    · simp only [Category.assoc, pullback.lift_snd, C.iF_over]; exact hσ
  · rw [hrj, ← hWset]; exact hdS
  · intro W' _ _ _ hW ϖ hϖ χ y hy t tK htK hK P be hbe hmono
    obtain ⟨n, hn, hid⟩ := hval W' hW ϖ hϖ (χ ≫ π) y (by rw [← Category.assoc, ← hy, Category.assoc, hjπ])
      t tK htK hK P be hbe hmono
    exact ⟨n, hn, by rw [hBD, GlobalTheory.PullAlong.idlAlong_comap_eq]; exact hid⟩
  · obtain ⟨S₀, π₀, ν, U, hb, hνπ, hfin, -⟩ := hbl.2
    obtain ⟨T₀, hT⟩ := GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup c.F Z S₀ S (pullback.snd C.z (spMap C.b)) J π₀ ν BD hprojZ hb hfin
      (by rw [hνπ]; exact hBD) (C.OZ.pull fZ) hOZamp
    refine ⟨T₀, fun k hk => ?_⟩
    have h := hT k hk
    rwa [hνπ] at h
  · exact GlobalTheory.T.separation_normalizedBlowup_unitaryCompactification E H Dw hpq φ hφ hns l Xo c C d J₀ hd hJ₀ hval₀ S π j hbl hprop hjπ hjo hrj.symm

theorem uStB : GlobalTheory.UChart.UStB := uPoinStX_sep

end GlobalTheory.UPoincTop
end
end

