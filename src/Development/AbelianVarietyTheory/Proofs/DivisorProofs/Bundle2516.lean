module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1941
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0396
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSectionOfOpenImmersionSpec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.LocSecOfImm

theorem bij_appLE {X Y : Scheme.{0}} (q : X ⟶ Y) [IsOpenImmersion q] (U : Y.Opens) (hU : U ≤ q.opensRange)
    (V : X.Opens) (h : V ≤ q ⁻¹ᵁ U) (h' : q ⁻¹ᵁ U ≤ V) : Function.Bijective (q.appLE U V h).hom := by
  obtain rfl : V = q ⁻¹ᵁ U := le_antisymm h h'
  have := q.isIso_app U hU
  rw [Scheme.Hom.appLE_eq_app]
  exact ConcreteCategory.bijective_of_isIso (q.app U)

theorem appLE_res {X Y : Scheme.{0}} (q : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (h : U' ≤ U) (e : V ≤ q ⁻¹ᵁ U')
    (e' : V ≤ q ⁻¹ᵁ U) (a : Γ(Y, U)) : (q.appLE U' V e).hom (resG Y h a) = (q.appLE U V e').hom a :=
  congrArg (fun φ => CommRingCat.Hom.hom φ a) (q.map_appLE e (homOfLE h).op)

theorem res_appLE {X Y : Scheme.{0}} (q : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (h : V' ≤ V) (e : V ≤ q ⁻¹ᵁ U)
    (e' : V' ≤ q ⁻¹ᵁ U) (a : Γ(Y, U)) : resG X h ((q.appLE U V e).hom a) = (q.appLE U V' e').hom a :=
  congrArg (fun φ => CommRingCat.Hom.hom φ a) (q.appLE_map e (homOfLE h).op)

theorem appLE_appLE {X Y Z : Scheme.{0}} (p : X ⟶ Y) (q : Y ⟶ Z) (r : X ⟶ Z) (hr : p ≫ q = r) {U : Z.Opens}
    {V : Y.Opens} {W : X.Opens} (e₁ : V ≤ q ⁻¹ᵁ U) (e₂ : W ≤ p ⁻¹ᵁ V) (e₃ : W ≤ r ⁻¹ᵁ U) (a : Γ(Z, U)) :
    (p.appLE V W e₂).hom ((q.appLE U V e₁).hom a) = (r.appLE U W e₃).hom a := by
  subst hr
  exact congrArg (fun φ => CommRingCat.Hom.hom φ a) (Scheme.Hom.appLE_comp_appLE p q U V W e₁ e₂)

theorem valF_ne_zero_of_le {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : X.Opens} (a : Γ(X, U))
    (hle : ⊤ ≤ x ⁻¹ᵁ X.basicOpen a) : valF x U a ≠ 0 := by
  have h : ⊤ ≤ x ⁻¹ᵁ U := hle.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le a))
  have e1 := Scheme.basicOpen_appLE x ⊤ U h a
  rw [top_inf_eq] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a) = (x.appLE U ⊤ h).hom a := by
    rw [valF, dite_eq_left h]
    exact (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _
  have e3 : x ⁻¹ᵁ X.basicOpen a =
      (Sp F).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a)) := by
    rw [e2]; exact e1.symm
  intro h0
  rw [e3, h0, map_zero, Scheme.basicOpen_zero] at hle
  exact hle (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)

theorem exists_point {X Y : Scheme.{0}} {K : Type} [Field K] [IsAlgClosed K] (π : X ⟶ Y) [LocallyOfFiniteType π]
    (x : Sp K ⟶ Y) (O : X.Opens) (p : X) (hp : p ∈ O) (hx : π p = x (IsLocalRing.closedPoint K)) :
    ∃ g : Sp K ⟶ X, g ≫ π = x ∧ ⊤ ≤ g ⁻¹ᵁ O := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (IsLocalRing.closedPoint K) hx
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨c, hcO, hc'⟩ := nonempty_inter_closedPoints (Z := (pullback.fst π x ⁻¹ᵁ O : Set _))
    ⟨z, show pullback.fst π x z ∈ O from hz ▸ hp⟩ (pullback.fst π x ⁻¹ᵁ O).isOpen.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc ≫ pullback.fst π x, ?_, fun a _ => ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · show pullback.fst π x (pointOfClosedPoint (pullback.snd π x) c hc a) ∈ O
    rw [pointOfClosedPoint_apply]
    exact hcO

theorem exists_locSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (R : Type) [CommRing R] (χ : Sp R ⟶ S) [IsOpenImmersion χ] (σ : SecAt G L χ), LocallyOfFiniteType G.hom → (∀ s : Sp R, ∃ z : (Over.mk χ ⊗ G).left, (fst (Over.mk χ) G).left z = s ∧ z ∈ nonzeroLocus σ) → ∃ s : LocSec G L χ.opensRange, IsLocSec s ∧ (∀ (K : Type) [Field K] (i : R →+* K), GenIs (spMap i ≫ χ) s (SecM.ofSec G (SecAt.pull G L σ i))) ∧ FibNz s χ.opensRange := by
  intro S G _ L R _ χ _ σ hft hnz
  let q : (Over.mk χ ⊗ G).left ⟶ G.left := (snd (Over.mk χ) G).left
  have hq : IsOpenImmersion q := inferInstanceAs (IsOpenImmersion (pullback.snd χ G.hom))
  have ew : q ≫ G.hom = (fst (Over.mk χ) G).left ≫ χ :=
    (Over.w (snd (Over.mk χ) G)).trans (Over.w (fst (Over.mk χ) G)).symm
  have hN : ∀ y, G.hom (q y) ∈ χ.opensRange := fun y => by
    rw [← Scheme.Hom.comp_apply, ew, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hrange : G.hom ⁻¹ᵁ χ.opensRange ≤ q.opensRange := fun y hy =>
    (Scheme.Pullback.range_snd χ G.hom).ge hy
  have hle : ∀ j : Fin 1 → L.ι, (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U j ≤
      q ⁻¹ᵁ (L.U (j 0) ⊓ G.hom ⁻¹ᵁ χ.opensRange) := fun j y hy => ⟨Set.mem_iInter.1 hy 0, hN y⟩
  have hbij : ∀ i : L.ι, Function.Bijective (q.appLE (L.U i ⊓ G.hom ⁻¹ᵁ χ.opensRange)
      ((LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U fun _ => i) (hle fun _ => i)).hom := fun i =>
    bij_appLE q _ (inf_le_right.trans hrange) _ _ fun y hy => Set.mem_iInter.2 fun _ => hy.1
  choose s hs using fun i : L.ι => (hbij i).2 (σ.f fun _ => i)
  have hs' : ∀ j : Fin 1 → L.ι, (q.appLE _ _ (hle j)).hom (s (j 0)) = σ.f j := fun j => by
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    exact hs i
  refine ⟨s, fun i j => ?_, fun K _ i => ⟨?_, funext fun j => ?_⟩, fun K _ _ x hx => ?_⟩
  · have hV : (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U (fun _ => i) ⊓ (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ)).U (fun _ => j) ≤
        q ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ G.hom ⁻¹ᵁ χ.opensRange) := fun y hy =>
      ⟨⟨Set.mem_iInter.1 hy.1 0, Set.mem_iInter.1 hy.2 0⟩, hN y⟩
    refine (bij_appLE q _ (inf_le_right.trans hrange) _ hV fun y hy =>
      ⟨Set.mem_iInter.2 fun _ => hy.1.1, Set.mem_iInter.2 fun _ => hy.1.2⟩).1 ?_
    have hc := σ.compat (fun _ => i) (fun _ => j)
    rw [← hs i, ← hs j] at hc
    rw [map_mul]
    refine (appLE_res q _ _ (inf_le_left.trans (hle fun _ => i)) _).trans
      (((res_appLE q _ _ _ _).symm.trans hc).trans (congrArg₂ (· * ·) ?_ ?_))
    · refine Eq.trans ?_ (appLE_res q _ _ (hV.trans (Scheme.Hom.preimage_mono _ inf_le_left)) _).symm
      simp only [LPow, LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
      rfl
    · exact (res_appLE q _ _ (inf_le_right.trans (hle fun _ => j)) _).trans (appLE_res q _ _ _ _).symm
  · rintro _ ⟨y, rfl⟩
    exact ⟨spMap i y, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · show genPull _ s j = (SecAt.pull G L σ i).f j
    unfold genPull SecAt.pull VVRank.pullS VVRank.pullTo
    dsimp only
    rw [← hs' j]
    exact (appLE_appLE _ q _ (VVRank.whisker_snd_left G _) _ _ _ _).symm
  · obtain ⟨s₀, hs₀⟩ : x (IsLocalRing.closedPoint K) ∈ χ.opensRange := hx ⟨_, rfl⟩
    obtain ⟨z, hz, hz'⟩ := hnz s₀
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
    rw [← hs' j] at hj
    have hb := ((Scheme.basicOpen_appLE q _ _ (hle j) (s (j 0))).le hj).2
    obtain ⟨y, hy, hy'⟩ := exists_point G.hom x (G.left.basicOpen (s (j 0))) (q z) hb (by
      rw [← Scheme.Hom.comp_apply, ew, Scheme.Hom.comp_apply, hz]
      exact hs₀)
    refine ⟨y, j 0, hy, ?_, valF_ne_zero_of_le _ hy'⟩
    rintro _ ⟨a, rfl⟩
    exact G.left.basicOpen_le (s (j 0)) (hy' (Set.mem_univ a))

end GlobalTheory.UMin.LocSecOfImm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalThetaConstantsLocalisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.ThLocal
open GlobalTheory.ThetaPtMove GlobalTheory.ThetaPtExist

theorem sec_eq {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem exists_local : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (θ : SecAt G L x) (R₁ : Type) [CommRing R₁] [Algebra R R₁] [IsNoetherianRing R₁] (N : ℕ) (q : Fin N → (Over.mk (spMap (algebraMap R R₁) ≫ x) ⟶ G)), Odd m → IsUnit (m : R) → PolFib G L g x → (∀ a, q a ^ (m ^ 2) = 1) → ∀ p : Ideal R₁, p.IsPrime → ∃ f ∉ p, ∃ c : Fin N → Localization.Away f, ∀ (K : Type) [Field K] (j : Localization.Away f →+* K) (a : Fin N) (pt : Over.mk (spMap ((j.comp (algebraMap R₁ (Localization.Away f))).comp (algebraMap R R₁)) ≫ x) ⟶ G), pt.left = spMap (j.comp (algebraMap R₁ (Localization.Away f))) ≫ (q a).left → ThG G L ρ m (SecAt.pull G L θ ((j.comp (algebraMap R₁ (Localization.Away f))).comp (algebraMap R R₁))) pt (fn (j (c a))) := by
  intro S G _ _ L ρ hL hρ g m R _ _ x θ R₁ _ _ _ N q hm hmu hP hq p hp
  obtain ⟨P, α, -, hpb, w, hw⟩ := hP
  have hL₁ := P.isLB
  haveI := P.isAb.comm
  obtain ⟨ρ₁, hρ₁, hr⟩ := exists_rigidificationPullbackCompatibleIso hpb hw hL hL₁ hρ
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have cg := GlobalTheory.AbLaw.CubeAssembly.cube_gen
  have neg := GlobalTheory.exists_gen_negLB hG
  obtain ⟨α₀, hα₀⟩ := (GlobalTheory.MulPull.mulPull_of_cube_of_symm cg neg).1 (Sp R) P m
  have sym := (GlobalTheory.symLift_odd hG (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube cg).1).2.2 neg).1
  let T : Over (Sp R) := Over.mk (spMap (algebraMap R R₁))
  let T₁ : Over S := Over.mk (spMap (algebraMap R R₁) ≫ x)
  have hτ₁ : 𝟙 T.left ≫ T₁.hom = T.hom ≫ x := Category.id_comp _
  choose y hy hym using fun a => exists_torsion_down hpb (𝟙 T.left) (T₀ := T₁) hτ₁ (q a) (hq a)
  let pt₀ : T.left := (⟨p, hp⟩ : PrimeSpectrum R₁)
  choose V hV U hU using fun a => (sym (Sp R) P (m ^ 2) hm.pow T (y a) (hym a)).1 pt₀
  have hO : IsOpen (⋂ a, ((V a : T.left.Opens) : Set T.left)) := isOpen_iInter_of_finite fun a => (V a).2
  obtain ⟨_, ⟨f, rfl⟩, hf, hfO⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show pt₀ ∈ ⋂ a, ((V a : T.left.Opens) : Set T.left) from Set.mem_iInter.2 hV) hO
  refine ⟨f, hf, ?_⟩
  let Lf := Localization.Away f
  let af : R₁ →+* Lf := algebraMap R₁ Lf
  let i_f : R →+* Lf := af.comp (algebraMap R R₁)
  let Tf : Over (Sp R) := Over.mk (spMap i_f)
  let β : Tf ⟶ T := Over.homMk (spMap af) (by
    show spMap af ≫ spMap (algebraMap R R₁) = spMap (af.comp (algebraMap R R₁))
    exact (spMap_comp _ _).symm)
  have hrange : ∀ a, Set.range (spMap af) ⊆ Set.range (V a).ι := by
    intro a
    rintro _ ⟨p', rfl⟩
    rw [Scheme.Opens.range_ι]
    exact Set.mem_iInter.1 (hfO ((PrimeSpectrum.localization_away_comap_range Lf f).le ⟨p', rfl⟩)) a
  have hsym : ∀ a, ∃ θ' : ThetaGrp P.A P.L ((m : ℤ) ^ 2) Tf,
      SymLift P.A P.L ((m : ℤ) ^ 2) (m ^ 2) (β ≫ y a) θ' := by
    intro a
    let u := IsOpenImmersion.lift (V a).ι (spMap af) (hrange a)
    have hu : u ≫ (V a).ι = spMap af := IsOpenImmersion.lift_fac _ _ _
    let r : Tf ⟶ overRes (V a) := Over.homMk u (by
      show u ≫ (V a).ι ≫ T.hom = Tf.hom
      rw [← Category.assoc, hu]
      exact Over.w β)
    obtain ⟨θ', h'⟩ := GlobalLift.exists_symLift_pull hL₁ r (hU a)
    have e : r ≫ overResι (V a) = β := Over.OverMorphism.ext hu
    rw [← Category.assoc, e] at h'
    rw [← Nat.cast_pow]
    exact ⟨θ', h'⟩
  let T₀ : Over S := Over.mk (spMap i_f ≫ x)
  have hτ : 𝟙 Tf.left ≫ T₀.hom = Tf.hom ≫ x := Category.id_comp _
  obtain ⟨th, hth⟩ := exists_secRel hpb (𝟙 Tf.left) (T₀ := T₀) hτ hw hL hL₁ (SecAt.pull G L θ i_f)
  have e₁ : (snd Tf P.A).left ≫ (mulA P.A m).left = (snd Tf P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨αf, hαf, -⟩ := exists_gen hL₁ (φ' := ![(snd Tf P.A).left, (snd Tf P.A ^ m).left]) (ε' := ![(m : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((m : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd Tf P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨τf, hτf, -⟩ := exists_gen hL₁ (φ' := fun _ : Fin 1 => (1 : Tf ⟶ P.A).left) (ε' := fun _ => (m : ℤ) ^ 2)
    (fun U _ f => by
      rw [Fintype.prod_unique, Fin.prod_univ_one]
      exact congrArg₂ (fun q n => f q ^ n) rfl (by simp))
    (GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) ρ₁ (toUnit Tf).left) (m ^ 2))
    (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hρ₁ _) _)
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL₁ (mulT P.A Tf m) (snd Tf P.A ^ m) (lift_snd _ _)
    ((m : ℤ) ^ 2) 1 αf hαf th
  choose Uf hUf using hsym
  choose s₂ hs₂ using fun a => ThetaPtExist.exists_isTwistPull hL₁ (translT P.A (Uf a).pt) (translPt P.A (Uf a).pt)
    (lift_snd _ _) ((m : ℤ) ^ 2) ((m : ℤ) ^ 2) (Uf a).φ (Uf a).isGen s₁
  choose wv hwv using fun a => ThetaPtExist.exists_isValueAt hL₁ (s₂ a) 1 τf hτf
  have hyf : ∀ a, (β ≫ y a) ^ (m ^ 2) = 1 := fun a => by rw [← MonObj.comp_pow, hym a, MonObj.comp_one]
  obtain ⟨e, he⟩ := exists_thG hL₁ hρ₁ m ((m : ℤ) ^ 2) (Nat.cast_pow m 2).symm hyf (th := th) (α := αf)
    hαf hτf hs₁ hUf hs₂ hwv
  refine ⟨fun a => (Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a), ?_⟩
  intro K _ j a pt hpt
  clear hUf hs₂ hwv hs₁ sym hU hV hfO hO cg neg hG hrange
  let ξ : T₀ ⟶ T₁ := Over.homMk (spMap af) (by
    show spMap af ≫ spMap (algebraMap R R₁) ≫ x = spMap (af.comp (algebraMap R R₁)) ≫ x
    rw [← Category.assoc, ← spMap_comp])
  have hx₀ : 𝟙 Tf.left ≫ (ξ ≫ q a).left = (β ≫ y a).left ≫ α := by
    have h := hy a
    rw [Category.id_comp] at h
    rw [Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, ← h]
    rfl
  have hn₀ : (ξ ≫ q a) ^ (m ^ 2) = 1 := by rw [← MonObj.comp_pow, hq a, MonObj.comp_one]
  have up := ThG.up hpb (T := Tf) (T₀ := T₀) (𝟙 Tf.left) hτ hw hL hL₁ hr hx₀ hn₀ hth (he a)
  let δ : Over.mk (spMap ((j.comp af).comp (algebraMap R R₁)) ≫ x) ⟶ T₀ := Over.homMk (spMap j) (by
    show spMap j ≫ spMap (af.comp (algebraMap R R₁)) ≫ x = spMap ((j.comp af).comp (algebraMap R R₁)) ≫ x
    rw [← Category.assoc, ← spMap_comp])
  have down := ThPull.thG_pull hL hρ δ up
  have ept : pt = δ ≫ ξ ≫ q a := by
    refine Over.OverMorphism.ext ?_
    rw [hpt, Over.comp_left, Over.comp_left, ← Category.assoc]
    exact congrArg (· ≫ (q a).left) (spMap_comp af j)
  have eθ : SecAt.pull G L θ ((j.comp af).comp (algebraMap R R₁)) = VVRank.pullS G _ δ (SecAt.pull G L θ i_f) := by
    unfold SecAt.pull
    rw [pullS_comp G hL]
    congr 1
    refine Over.OverMorphism.ext ?_
    exact spMap_comp i_f j
  have ec : δ.left.appTop.hom ((inv (𝟙 Tf.left)).appTop.hom ((e : Γ(Tf.left, ⊤)) * wv a)) =
      fn (j ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a))) := by
    have h1 : (inv (𝟙 Tf.left)).appTop.hom ((e : Γ(Tf.left, ⊤)) * wv a) =
        fn ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a)) := by
      simp only [IsIso.inv_id, Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply]
      exact ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom_inv_id_apply _).symm
    rw [h1]
    exact (congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a)))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm
  rw [ept, eθ, ← ec]
  exact down

end GlobalTheory.UMin.ThLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerDivisorToroidalComponent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open TopForm

theorem exists_logKS_div : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (K : CanonLB (s₀ TF.Y Z) Dw.dim) (D' : CartierDiv (X₀ TF.Y Z)) (r : K.bundle.ι → (X₀ TF.Y Z).functionFieldˣ), Presents D' K.bundle r → ∀ (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ → ∀ D : CartierDiv (X₀ TF.Y Z), (∀ x : X₀ TF.Y Z, ∃ (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ ∧ (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) ∧ (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (fun k => spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) (A τ i) (f₀.v τ i)) ∧ D.IsEqn x (∏ τ, d τ ^ (-(if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p)))) → ∃ h : (X₀ TF.Y Z).functionField, ∀ x : X₀ TF.Y Z, ∃ g g' : (X₀ TF.Y Z).functionFieldˣ, D.IsEqn x g ∧ D'.IsEqn x g' ∧ RegAt x (h * (g : (X₀ TF.Y Z).functionField) / (g' : (X₀ TF.Y Z).functionField)) ∧ (UnitAt x (h * (g : (X₀ TF.Y Z).functionField) / (g' : (X₀ TF.Y Z).functionField)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  intro E _ _ _ H Dw l Xo c TF Z hpq hfn _ _ K D' r hr φ₀ f₀ hφ₀ D hD
  obtain ⟨D₀, hD₀⟩ := GlobalTheory.T.exists_logKodairaSpencer_genericEigenFrame E H Dw l Xo c TF Z hpq hfn φ₀ f₀ hφ₀
  obtain ⟨i₀, hi₀⟩ := exists_chart K.isLB (genericPoint (X₀ TF.Y Z))
  set T₀ := GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D₀ with hT₀
  refine ⟨(r i₀ : (X₀ TF.Y Z).functionField) * T₀ (formOf _ hi₀ (K.om i₀)), fun x => ?_⟩
  obtain ⟨φ, f, A, d, hφ, hd, hA, hDx⟩ := hD x
  obtain ⟨Dx, hDxKS, hloc⟩ := GlobalTheory.T.exists_logKodairaSpencer_local_eigenFrame E H Dw l Xo c TF Z hpq hfn x φ f hφ
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.logKodairaSpencer_wedge_frameChange E H Dw l Xo c TF Z hpq hfn _ _ D₀ Dx A d hD₀ hDxKS hA hd
  obtain ⟨i, hi⟩ := exists_chart K.isLB x
  refine ⟨_, r i, hDx, hr.isEqn i x hi, ?_⟩
  have hgi : genericPoint (X₀ TF.Y Z) ∈ K.bundle.U i := gen_mem hi
  have key : (r i₀ : (X₀ TF.Y Z).functionField) * T₀ (formOf _ hi₀ (K.om i₀)) =
      r i * T₀ (formOf _ hgi (K.om i)) := by
    have e1 := formOf_eq_ratio_smul hi₀ hgi (K.isFrame i₀) (K.isFrame i)
    have e2 := hr.isRatSec i₀ i (GlobalTheory.Cartier.memInf hi₀ hgi)
    rw [K.g_eq_ratio] at e2
    rw [e1, map_smul, smul_eq_mul, e2]
    ring
  have e : (r i₀ : (X₀ TF.Y Z).functionField) * T₀ (formOf _ hi₀ (K.om i₀)) *
      ((∏ τ, d τ ^ (-(if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p)) : (X₀ TF.Y Z).functionFieldˣ) :
        (X₀ TF.Y Z).functionField) / (r i : (X₀ TF.Y Z).functionField) =
      u * GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) Dx (formOf _ hgi (K.om i)) := by
    rw [key, hu']
    have h1 : ((∏ τ, d τ ^ (if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p) : (X₀ TF.Y Z).functionFieldˣ) :
        (X₀ TF.Y Z).functionField) * ((∏ τ, d τ ^ (-(if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p)) :
          (X₀ TF.Y Z).functionFieldˣ) : (X₀ TF.Y Z).functionField) = 1 := by
      rw [← Units.val_mul, ← Finset.prod_mul_distrib]
      simp [← zpow_add]
    have h2 := (r i).ne_zero
    have h3 : ∀ (ri P Q a b : (X₀ TF.Y Z).functionField), ri ≠ 0 → P * Q = 1 →
        ri * (a * P * b) * Q / ri = a * b := fun ri P Q a b hri hPQ => by
      calc ri * (a * P * b) * Q / ri = (a * b * (P * Q)) * (ri / ri) := by ring
        _ = a * b := by rw [hPQ, div_self hri]; ring
    exact h3 _ _ _ _ _ h2 h1
  obtain ⟨hreg, hunit⟩ := hloc (K.bundle.U i) (K.om i) (K.isFrame i) hi
  have hu1 : UnitAt x u := by
    rcases hu with rfl | rfl
    · exact unitAt_one x
    · exact ⟨-1, isUnit_one.neg, by simp⟩
  rw [e]
  refine ⟨hu1.regAt.mul hreg, ⟨fun h => hunit.1 ?_, fun h => hu1.mul (hunit.2 h)⟩⟩
  have := hu1.inv.mul h
  rwa [← mul_assoc, inv_mul_cancel₀ hu1.ne_zero, one_mul] at this

end GlobalTheory.LogKSDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogResolutionProjectiveOfPrincipalisation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogResProj

theorem exists_logResolution : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ T : Closeds X, genericPoint X ∉ T → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X), SmoothOfRelativeDimension D (π ≫ p) ∧ IsProjOver (π ≫ p) ∧ topologicalKrullDim Y = D ∧ π (genericPoint Y) = genericPoint X ∧ π.residueDegree (genericPoint Y) = 1 ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (⟨π ⁻¹' (T : Set X), T.isClosed.preimage π.continuous⟩ : Closeds Y)) := by
  intro hP F _ _ X _ p D hp hdim T hT
  obtain ⟨W', s, U, hW', hsm, hpr, hU, hiso⟩ := WeakRes.weak_resolution hP F X p D hp hdim
  have := hW'
  have g₁ := GlobalTheory.Published.generic_of_isIso_restrict s U hU
  let T' : Closeds W' := ⟨s ⁻¹' (T : Set X), T.isClosed.preimage s.continuous⟩
  let I : W'.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal T'
  have hIs : I.support = T' := by
    ext1; exact Scheme.IdealSheafData.coe_support_vanishingIdeal T'
  have hgW : genericPoint W' ∉ (T' : Set W') := by
    show s (genericPoint W') ∉ (T : Set X)
    rw [g₁.1]; exact hT
  have hI : I ≠ ⊥ := by
    intro h
    apply hgW
    have : I.support = ⊤ := by rw [h]; simp
    rw [← hIs, this]; trivial
  obtain ⟨Y, s', hY, hsm', hpr', -, hiso', -, hsnc⟩ := hP F D W' (s ≫ p) hW' hsm hpr I hI
  have := hY
  have hne : ((I.support.compl : W'.Opens) : Set W').Nonempty := ⟨genericPoint W', by
    show genericPoint W' ∉ (I.support : Set W'); rw [hIs]; exact hgW⟩
  have g₂ := GlobalTheory.Published.generic_of_isIso_restrict s' _ hne
  have hpL : LocallyOfFiniteType p := by
    obtain ⟨N, i, hi, rfl⟩ := hp
    have := isProper_str F N
    infer_instance
  have : Smooth (s ≫ p) := by haveI := hsm; exact SmoothOfRelativeDimension.smooth D _
  have : Smooth (s' ≫ s ≫ p) := by haveI := hsm'; exact SmoothOfRelativeDimension.smooth D _
  have hd₁ := GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict F X W' p (s ≫ p) s hpL inferInstance rfl U hU hiso
  have hd₂ := GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict F W' Y (s ≫ p) (s' ≫ s ≫ p) s' inferInstance
    inferInstance rfl _ hne hiso'
  refine ⟨Y, hY, s' ≫ s, by simpa using hsm', by simpa using hpr', by rw [hd₂, hd₁, hdim], ?_, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, g₂.1, g₁.1]
  · rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp, g₂.2, g₂.1, g₁.2, mul_one]
  · have hE : (I.comap s').support = ⟨(s' ≫ s) ⁻¹' (T : Set X), T.isClosed.preimage (s' ≫ s).continuous⟩ := by
      ext1
      rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, hIs]
      ext y; simp [T']
    rw [← hE]; exact hsnc

end GlobalTheory.LogResProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoCompCartesianHomValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle

namespace GlobalTheory.TautPull

theorem lamIso_comp_exists : ∀ {S S' S₁ : Scheme.{0}} {B : Over S₁} {G : Over S} {G' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {M : LB B.left} {L : LB G.left} {L' : LB G'.left} {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f φ) {β₂ : (G2 G).left ⟶ (G2 B).left}, M.IsLB → L.IsLB → L'.IsLB → ∀ (w : LB.Iso (abelian₂ G L) ((abelian₂ B M).pull β₂)) (v : LB.Iso L' (L.pull φ)), w.IsGen → v.IsGen → ∃ w'' : LB.Iso (abelian₂ G' L') ((abelian₂ B M).pull (sqOf gp ≫ β₂)), w''.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 G').left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J₁ : (Z ⟶ G.left) → L.ι) (J' : (Z ⟶ G'.left) → L'.ι), Good M z J → Good L z J₁ → Good L' z J' → lamVal w'' p z J J' = lamVal w (p ≫ sqOf gp) z J J₁ * ∏ I, gw v (p ≫ lamφ G' I) z (J₁ ((p ≫ lamφ G' I) ≫ φ)) (J' (p ≫ lamφ G' I)) ^ lamε I := by
  intro S S' S₁ B G G' _ _ _ _ _ _ M L L' f φ gp β₂ hM hL hL' w v hw hv
  have hΛB : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have hΛ : (abelian₂ G L).IsLB := DVR.linComb_isLB _ hL _ _
  have hΛ' : (abelian₂ G' L').IsLB := DVR.linComb_isLB _ hL' _ _
  obtain ⟨w'', T⟩ := exists_comp hΛ w (lamIso gp v) ((isGen_iff _).1 hw)
    (pgen_lamIso gp v ((isGen_iff v).1 hv)) hΛB hΛ'
  refine ⟨w'', (isGen_iff _).2 (T.pgen_comp hΛ ((isGen_iff _).1 hw)
    (pgen_lamIso gp v ((isGen_iff v).1 hv))), ?_⟩
  intro Z p z J J₁ J' hJ hJ₁ hJ'
  have t := T Z p z (fun I => J (p ≫ (sqOf gp ≫ β₂) ≫ lamφ B I))
    (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ G I)) (fun I => J' (p ≫ lamφ G' I))
    (Set.mem_iInter.2 fun I => hJ (p ≫ (sqOf gp ≫ β₂) ≫ lamφ B I))
    (Set.mem_iInter.2 fun I => hJ₁ ((p ≫ sqOf gp) ≫ lamφ G I))
    (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ G' I))
  refine t.trans (congrArg₂ (· * ·) ?_ ?_)
  · show _ = gw w (p ≫ sqOf gp) z (fun I => J ((p ≫ sqOf gp) ≫ β₂ ≫ lamφ B I))
      (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ G I))
    simp only [Category.assoc]
  · rw [gw_lamIso gp v p z _ _ (fun I => by
      have := hJ₁ ((p ≫ sqOf gp) ≫ lamφ G I)
      rw [Category.assoc, sqOf_lamφ, ← Category.assoc] at this ⊢
      exact this) (fun I => hJ' (p ≫ lamφ G' I))]
    refine Finset.prod_congr rfl fun I _ => ?_
    rw [Category.assoc, sqOf_lamφ, ← Category.assoc]

end GlobalTheory.TautPull
end

