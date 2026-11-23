module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0130
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointEndomorphismImageEqMovedGtPoint
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToFSurjectiveFractionRing
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0124
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem allSixLaws : Laws ∧ Laws2 ∧ Laws3 ∧ Laws4 ∧ Laws5 ∧ Laws6 :=
  ⟨abelianSchemeLaws_all.1, abelianSchemeLaws_all.2,
    furtherLaws_of_laws abelianSchemeLaws_all.1 twistBaseChange⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EndomorphismTorusExtensionPeriodOfAdjoint
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.KeyIota
open GlobalTheory.TorusExt

theorem eq_of_torsion_chars {X F : Type} [AddCommGroup X] [Module.Free ℤ X] [Field F] [IsAlgClosed F] [CharZero F]
    {a b : X} (h : ∀ k : ℕ, 1 ≤ k → ∀ t : Multiplicative X →* Fˣ, t ^ k = 1 →
      t (Multiplicative.ofAdd a) = t (Multiplicative.ofAdd b)) : a = b := by
  by_contra hne
  have hd : a - b ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℤ hd
  let k : ℕ := (φ (a - b)).natAbs + 1
  haveI : NeZero k := ⟨Nat.succ_ne_zero _⟩
  haveI : NeZero (k : F) := ⟨Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F k
  let u : Fˣ := (hζ.isUnit (NeZero.ne k)).unit
  have hu : IsPrimitiveRoot u k := hζ.isUnit_unit (NeZero.ne k)
  let t : Multiplicative X →* Fˣ := (zpowersHom Fˣ u).comp (AddMonoidHom.toMultiplicative φ.toAddMonoidHom)
  have ht : ∀ x, t (Multiplicative.ofAdd x) = u ^ φ x := fun _ => rfl
  have h1 := h k (Nat.succ_le_succ (Nat.zero_le _)) t (MonoidHom.ext fun x => by
    show t (Multiplicative.ofAdd x.toAdd) ^ k = 1
    rw [ht, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu.pow_eq_one, one_zpow])
  rw [ht, ht] at h1
  have h2 : u ^ φ (a - b) = 1 := by rw [map_sub, zpow_sub, h1, mul_inv_cancel]
  have h3 := Int.natCast_dvd.1 ((hu.zpow_eq_one_iff_dvd _).1 h2)
  have h4 := Nat.le_of_dvd (Int.natAbs_pos.2 hφ) h3
  omega

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem weilQkIs_swap {k : ℕ} {p p' : QkPt D F k} {z : Fˣ} (h : WeilQkIs D F k p p' z) :
    WeilQkIs D F k p' p (z⁻¹ : Fˣ) := by
  intro w' w hw' hw s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄ α j
  have e := h w w' hw hw' s s₃ s₄ s₁ s₂ h₃ h₄ h₁ h₂ α j
  rw [e, ← _root_.mul_assoc]
  have : ∀ W, DegPre.constBF D F ((z⁻¹ : Fˣ) : F) W * DegPre.constBF D F (z : F) W = 1 := fun W => by
    unfold DegPre.constBF
    rw [← map_mul, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one, map_one]
  rw [this, _root_.one_mul]

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ E E' : EndU U.toUnifPre, Function.Injective E.h → Function.Injective E'.h → LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → ∀ y (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (E'.h y) g' := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U E E' hE hE' hadj y g g' hg hgg'
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  haveI : CharZero (FractionRing V) := charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing V) F).injective
  letI := gtGroup D.toPre F
  have hB := D.tau_bimult
  have inj := GlobalTheory.IotaInj.main hL V _ hA D F
  have dv := (gt_onto_divisible_kernel hL V _ hA D F).2.1
  have ec := _root_.GlobalTheory.EndCalc.end_calculus hL V _ hA D A G hG U F
  have key := _root_.GlobalTheory.UT.EndTors.main hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U
  have ros := (_root_.GlobalTheory.UT.rosatiAdj_and_c_linear_of_endU hL V _ hA D A G hG U E E' hadj).1

  have act : ∀ e : EndU U.toUnifPre, ∃ a : GtPtF D.toPre F →+ GtPtF D.toPre F, ∀ x x', e.Act x x' ↔ x' = a x := by
    intro e
    obtain ⟨ex, ad, -⟩ := ec e e e
    choose a ha hu using ex
    exact ⟨AddMonoidHom.mk' a fun x x' => (isAdd_iff_eq _ _ _).1
      (ad x x' (x + x') _ _ _ ((isAdd_iff_eq _ _ _).2 rfl) (ha x) (ha x') (ha _)),
      fun x x' => ⟨hu x x', fun h => h ▸ ha x⟩⟩
  obtain ⟨a, ha⟩ := act E
  obtain ⟨a', ha'⟩ := act E'
  have hy : g = iota hB F y := (isIota_iff_eq hB _ _).1 hg
  have hg' : g' = a g := (ha _ _).1 hgg'

  have div : ∀ k : ℕ, 1 ≤ k → ∀ f, Tors U.toUnifPre F k f → ∃ p p' : QkPt D.toPre F k, p.y = y ∧
      f p' = f p ≫ E.aA ∧ GtPtF.IsIota p'.y g' := by
    intro k hk f hf
    obtain ⟨gk, hgk⟩ := dv k hk g
    let p : QkPt D.toPre F k := ⟨y, gk, g, hgk, hg⟩
    obtain ⟨p', e₁, e₂⟩ := key E hE k hk p (f p) ((hf.1 _ _).2 rfl) (a gk) ((ha _ _).2 rfl)
    refine ⟨p, p', rfl, ((hf.1 _ _).1 e₂).symm, (isIota_iff_eq hB _ _).2 ?_⟩
    rw [← qk_nsmul hB p', e₁, ← map_nsmul, hg', (isNsmul_iff_eq _ _ _).1 hgk]
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F 1 le_rfl
  obtain ⟨-, p₁, -, -, hp₁⟩ := div 1 le_rfl f₁ hf₁
  suffices hs : p₁.y = E'.h y from hs ▸ hp₁
  refine eq_of_torsion_chars (F := F) fun k hk t ht => ?_
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F k hk
  obtain ⟨p, p', hp, hpp', hp'⟩ := div k hk f hf
  have wp := _root_.GlobalTheory.weilQk_existsUnique hL V _ hA D F k hk
  rw [inj _ _ _ hp₁ hp', ← hp]
  have tor : ∀ p : QkPt D.toPre F k, f p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U.toUnifPre.ext
    exact ((hf.1 p _).2 rfl w hw).1
  have h0 : k • torusPt D.toPre F (Additive.ofMul t) = 0 := by
    rw [← map_nsmul, ← ofMul_pow, ht, ofMul_one, map_zero]
  let q : QkPt D.toPre F k := qkMk hB 0 (torusPt D.toPre F (Additive.ofMul t)) (h0.trans (map_zero _).symm)
  have hq : IsTor t q.g := by
    apply (isTor_iff _ _).2
    simpa [q] using (isTorusPtF_torusPt t)
  obtain ⟨q', e₁, e₂⟩ := key E' hE' k hk q (f q) ((hf.1 _ _).2 rfl) (a' q.g) ((ha' _ _).2 rfl)
  have hq' : IsTor (t.comp (AddMonoidHom.toMultiplicative E'.h)) q'.g :=
    (ec E' E' E').2.2.1 t q.g q'.g hq ((ha' _ _).2 e₁)
  have hq0 : q'.y = 0 := by
    refine inj _ _ (0 : GtPtF D.toPre F) ((isIota_iff_eq hB _ _).2 ?_) ((isIota_iff_eq hB _ _).2 (map_zero _).symm)
    rw [← qk_nsmul hB q', e₁, ← map_nsmul]
    simpa [q] using ((congrArg a' h0).trans (map_zero _)).symm
  have w₁ := (hf.2.2.2.2 _ _ _).1 (weilQkIs_swap ((wp q p').2 t (by simp [q]) hq))
  rw [hpp', weilIs_comp_iff_of_rosatiAdj hL _ A E.aA E'.aA E.homA E'.homA ros F _ k _ _ (tor p) (tor q),
    (hf.1 _ _).1 e₂] at w₁
  have w₂ := weilQkIs_swap ((hf.2.2.2.2 _ _ _).2 w₁)
  rw [inv_inv] at w₂
  exact (wp q' p).1.unique w₂ ((wp q' p).2 _ hq0 hq')

end GlobalTheory.KeyIota
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueLineGen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PhiOperatorCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms GlobalTheory.IndefiniteRowSideFullHecke.TranslatedLineGenerators
open GlobalTheory.GtPointsCompare (castGen pairEquiv ptEquiv rel_iff)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
variable {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns


theorem phiRel_total (hB : D.TauBimult) (q : QkPt D F k)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q.g.b) (DegPre.lineε k))} (hw : w.IsGen) (s : Fam D F k) :
    ∃ s', PhiRel D F k q w s s' :=
  (exists_phi hG q w hw hB s).imp fun _ h => (phiRel_iff hG q w hw _ _).2 h

theorem phiRel_transfer (hB : D.TauBimult) {q q' : QkPt D F k} (he : QkPt.Equiv D F q q')
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q.g.b) (DegPre.lineε k))} (hw : w.IsGen) :
    ∃ w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q'.g.b) (DegPre.lineε k)), w'.IsGen ∧
      ∀ s s', PhiRel D F k q w s s' ↔ PhiRel D F k q' w' s s' := by
  obtain ⟨w', hw', h⟩ := UT.PhiProj.phiRel_of_equiv hG he hw
  refine ⟨w', hw', fun s s' => ⟨h s s', fun H => ?_⟩⟩
  obtain ⟨r, hr⟩ := phiRel_total hB q hw s
  exact ThetaTranslate.phiRel_unique hG q' hw' (h s r hr) H ▸ hr

theorem weilQkIs_of_equiv (hB : D.TauBimult) {p p' q q' : QkPt D F k} (h : QkPt.Equiv D F p q)
    (h' : QkPt.Equiv D F p' q') {ζ : F} (H : WeilQkIs D F k p p' ζ) : WeilQkIs D F k q q' ζ := by
  intro w w' hw hw' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄
  obtain ⟨v, hv, e⟩ := phiRel_transfer hB (TorusExt.equiv_symm hB h) hw
  obtain ⟨v', hv', e'⟩ := phiRel_transfer hB (TorusExt.equiv_symm hB h') hw'
  exact H v v' hv hv' s s₁ s₂ s₃ s₄ ((e' _ _).1 h₁) ((e _ _).1 h₂) ((e _ _).1 h₃) ((e' _ _).1 h₄)

variable {P : PolAV (Spec (CommRingCat.of (FractionRing R)))} {E : SecA F P k → Fam D F k → Prop}

section Unif

variable {I : Ideal R} {Dd : DegData R I} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif I Dd P G)

end Unif

end GlobalTheory.PhiOperatorCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfFlatOfClosedPoint
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PrimitiveOverValuationRing
open GlobalTheory.CechPic

theorem pull_eq_zero_of_mem {Y Z : Scheme.{0}} (W : Y.Opens) (r : Z ⟶ Y) (hr : ∀ z, r z ∈ W) {c : CechPic.Pic Y}
    (h : CechPic.pull W.ι c = 0) : CechPic.pull r c = 0 := by
  have e := IsOpenImmersion.lift_fac W.ι r (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hr z)
  rw [← e, pull_comp, h, map_zero]

theorem cls_pair {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a b : Y ⟶ X)
    (h : (LB.LinComb L (K := Fin 2) ![a, b] ![1, -1]).IsLB) :
    cls _ h = CechPic.pull a (cls L hL) - CechPic.pull b (cls L hL) := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [Fin.sum_univ_two, sub_eq_add_neg]
  exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)

section Points

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {L O : LB B.left}

theorem triv_iff (hL : L.IsLB) (hO : O.IsLB) {T : Over S} (x : T ⟶ B) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ B).left) :
    Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull r) ↔
      CechPic.pull r (CechPic.pull ((fst T B ≫ x) * snd T B).left (cls L hL) - CechPic.pull (snd T B).left (cls L hL) -
        CechPic.pull (snd T B).left (cls O hO)) = 0 := by
  have h₁ : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  have h₂ := pull_isLB hO (snd T B).left
  have hM := LB.isLB_div h₁ h₂
  refine (cls_eq_zero_iff (pull_isLB hM r)).symm.trans ?_
  rw [cls_pull hM, cls_div h₁ h₂, cls_pull hO]
  exact Iff.of_eq (congrArg (fun q => CechPic.pull r (q - _) = 0) (cls_pair hL _ _ h₁))

theorem inK_mul_inv (hL : L.IsLB) (hO : O.IsLB) {T : Over S} (x y : T ⟶ B)
    (hx : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι))
    (hy : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L y) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) :
    InK B L (x * y⁻¹) := by
  intro p
  obtain ⟨U, hU, h₁⟩ := hx p
  obtain ⟨U', hU', h₂⟩ := hy p
  refine ⟨U ⊓ U', ⟨hU, hU'⟩, ?_⟩
  have hD : (translDiff B L (x * y⁻¹)).IsLB := LB.isLB_linComb hL _ _
  let τ : T ⊗ B ⟶ T ⊗ B := lift (fst T B) ((fst T B ≫ y⁻¹) * snd T B)
  have k₁ : τ ≫ fst T B = fst T B := lift_fst _ _
  have k₂ : ∀ z : T ⟶ B, τ ≫ ((fst T B ≫ z) * snd T B) = (fst T B ≫ (z * y⁻¹)) * snd T B := fun z => by
    rw [MonObj.comp_mul, lift_snd, ← Category.assoc, k₁, MonObj.comp_mul, _root_.mul_assoc]
  have m : ∀ z, (fst T B).left ((((fst T B).left ⁻¹ᵁ (U ⊓ U')).ι ≫ τ.left) z) ∈ U ⊓ U' := fun z => by
    have e := congrArg (fun q : T ⊗ B ⟶ T => q.left z.1) k₁
    exact (congrArg (· ∈ U ⊓ U') e).mpr z.2
  have a₁ := pull_eq_zero_of_mem _ _ (fun z => (m z).1) ((triv_iff hL hO x _).1 h₁)
  have a₂ := pull_eq_zero_of_mem _ _ (fun z => (m z).2) ((triv_iff hL hO y _).1 h₂)
  have a := congrArg₂ (· - ·) a₁ a₂
  simp only [← map_sub, sub_sub_sub_cancel_right, sub_zero] at a
  rw [pull_comp, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, k₂, k₂, mul_inv_cancel,
    MonObj.comp_one, _root_.one_mul] at a
  refine (cls_eq_zero_iff (pull_isLB hD _)).1 ?_
  rw [cls_pull hD]
  exact (congrArg _ (cls_pair hL _ _ hD)).trans a

end Points

theorem exists_geometric_point (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {O : LB P.A.left} (hO : O.IsLB)
    (hu : ∃ u : LB.Gen (abelian₂ P.A O), u.IsGen) (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) :
    ∃ x : Over.mk f ⟶ P.A, Triv (LB.div (translDiff P.A P.L x) (O.pull (snd (Over.mk f) P.A).left)) := by
  obtain ⟨P', g, hg, -, hm, ht⟩ := hL.polBaseChange S _ f P
  have hc : CechPic.pull g (cls P.L P.isLB) = cls P'.L P'.isLB := (cls_eq_iff (pull_isLB P.isLB g) P'.isLB).2 ht
  have hO' := pull_isLB hO g
  have one : ∀ T : Over (Spec (CommRingCat.of K)), toBase hg.w (1 : T ⟶ P'.A) = 1 := fun T => by
    have := hm T 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have lamO : lam (cls O hO) (fst P.A P.A) (snd P.A P.A) = 0 :=
    (cls_cube_two hO _ _ (LB.isLB_linComb hO _ _)).symm.trans ((cls_eq_zero_iff _).2 hu)
  have lamO' : lam (cls _ hO') (fst P'.A P'.A) (snd P'.A P'.A) = 0 := by
    have e := congrArg (CechPic.pull (lift (toBase hg.w (fst P'.A P'.A)) (toBase hg.w (snd P'.A P'.A))).left) lamO
    rw [pull_lam, lift_fst, lift_snd, map_zero, lam, ← hm, ← one] at e
    rw [cls_pull hO, lam, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp]
    exact e
  obtain ⟨x', hx'⟩ := GlobalTheory.T.exists_point_primitiveBundle_eq_translate_ppav hL K P' (O.pull g) hO'
    ((cls_eq_zero_iff (LB.isLB_linComb hO' _ _)).1 ((cls_cube_two hO' _ _ (LB.isLB_linComb hO' _ _)).trans lamO'))
  have e := ((cls_eq_iff hO' (LB.isLB_linComb P'.isLB _ _)).2 hx').trans (cls_pair P'.isLB _ _ _)
  let T : Over S := Over.mk f
  have wx : x'.left ≫ P'.A.hom = 𝟙 _ := Over.w x'
  let x : T ⟶ P.A := Over.homMk (x'.left ≫ g) (by
    show (x'.left ≫ g) ≫ P.A.hom = f
    rw [Category.assoc, hg.w, ← Category.assoc, wx]
    exact Category.id_comp _)
  have w : (snd T P.A).left ≫ P.A.hom = (fst T P.A).left ≫ f := (Over.w (snd T P.A)).trans (Over.w (fst T P.A)).symm
  let T' : Over (Spec (CommRingCat.of K)) := Over.mk (Y := (T ⊗ P.A).left) (fst T P.A).left
  let h : T' ⟶ P'.A := Over.homMk (hg.lift (snd T P.A).left (fst T P.A).left w) (hg.lift_snd _ _ _)
  have hh : h.left ≫ g = (snd T P.A).left := hg.lift_fst _ _ _
  let u : Over.mk (T'.hom ≫ f) ⟶ T ⊗ P.A := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Over.w (fst T P.A)).symm)
  have b₁ : u ≫ snd T P.A = toBase hg.w h := Over.OverMorphism.ext ((Category.id_comp _).trans hh.symm)
  have b₂ : u ≫ fst T P.A ≫ x = toBase hg.w (toUnit T' ≫ x') := by
    refine Over.OverMorphism.ext ((Category.id_comp _).trans ?_)
    have : (toUnit T').left = (fst T P.A).left := (Category.comp_id _).symm.trans (Over.w (toUnit T'))
    show (fst T P.A).left ≫ x'.left ≫ g = ((toUnit T').left ≫ x'.left) ≫ g
    rw [this]
    exact (Category.assoc _ _ _).symm
  have b : h.left ≫ ((toUnit P'.A ≫ x') * 𝟙 P'.A).left ≫ g = ((fst T P.A ≫ x) * snd T P.A).left := by
    have b₃ : toBase hg.w (h ≫ ((toUnit P'.A ≫ x') * 𝟙 P'.A)) = u ≫ ((fst T P.A ≫ x) * snd T P.A) := by
      rw [MonObj.comp_mul, MonObj.comp_mul, b₁, b₂, ← hm, Category.comp_id, ← Category.assoc, comp_toUnit]
    exact (Category.assoc _ _ _).symm.trans ((congrArg CommaMorphism.left b₃).trans (Category.id_comp _))
  have e' := congrArg (CechPic.pull h.left) e
  rw [cls_pull hO, ← hc, pull_id, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, Category.assoc, b, hh] at e'
  have h₁ : (translDiff P.A P.L x).IsLB := LB.isLB_linComb P.isLB _ _
  have h₂ := pull_isLB hO (snd T P.A).left
  refine ⟨x, (cls_eq_zero_iff (LB.isLB_div h₁ h₂)).1 ?_⟩
  rw [cls_div h₁ h₂, sub_eq_zero]
  exact (cls_pair P.isLB _ _ h₁).trans e'.symm

theorem isIso_of_flat_of_closedPoint {V : Type} [CommRing V] [IsLocalRing V] [_root_.IsReduced V] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of V)) [IsClosedImmersion q] [Flat q] (h : X) (hh : q h = IsLocalRing.closedPoint V) :
    IsIso q := by
  have : Surjective q := ⟨fun s => by
    obtain ⟨y, -, hy⟩ := Flat.generalizingMap q (a := h) (b := s) (by
      rw [hh]; exact IsLocalRing.specializes_closedPoint s)
    exact ⟨y, hy⟩⟩
  exact isIso_of_isClosedImmersion_of_surjective q

theorem exists_section_translate : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (P : PolAV (Spec (CommRingCat.of V))) (O : LB P.A.left), O.IsLB → (∃ u : LB.Gen (abelian₂ P.A O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ P.A, LBIso O (LB.LinComb P.L (K := Fin 2) ![((toUnit P.A ≫ x) * 𝟙 P.A).left, 𝟙 P.A.left] ![1, -1]) := by
  intro hL V _ _ _ P O hO hu
  have proj : IsProjBy P.A.hom := by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V P.A P.L P.isLB).1 P.ample
    exact ⟨_, isLB_pw P.isLB _, n, s, hs⟩
  obtain ⟨H, j, hj, hH⟩ := _root_.GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hL.globalFns V P.A P.isAb proj P.L O P.isLB hO
  have fin : IsFinite H.hom := GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hL.globalFns V P.A P.isAb P.L O P.isLB hO
    P.ample H j hj hH
  obtain ⟨r, hr⟩ := P.rigid
  obtain ⟨c⟩ := (hL.cube _ P ⟨P.L, r, P.isLB, hr⟩ rfl).1
  have flat : Flat H.hom := _root_.GlobalTheory.StabFlat.flat_of_isFinite hL.globalFns V P.A P.isAb proj ⟨P.L, r, P.isLB, hr⟩ c O hO hu H j hj hH fin
  have mono : Mono H.hom := ⟨fun {Z} a b e => by
    let a' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk a e
    let b' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk b rfl
    have := (inK_mul_inv P.isLB hO (a' ≫ j) (b' ≫ j) ((hH _ _).2 ⟨_, rfl⟩) ((hH _ _).2 ⟨_, rfl⟩)).eq_one P.ktriv
    rw [mul_inv_eq_one] at this
    exact (cancel_mono j.left).1 (congrArg CommaMorphism.left this)⟩
  have : IsClosedImmersion H.hom := (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨fin, mono⟩
  let K : Type := AlgebraicClosure (IsLocalRing.ResidueField V)
  let φ : V →+* K := (algebraMap (IsLocalRing.ResidueField V) K).comp (IsLocalRing.residue V)
  have : IsLocalHom φ := RingHom.isLocalHom_comp _ _
  obtain ⟨x₀, hx₀⟩ := exists_geometric_point hL P hO hu K (Spec.map (CommRingCat.ofHom φ))
  obtain ⟨y, -⟩ := (hH _ x₀).1 fun p => ⟨⊤, trivial, by
    have hM := LB.isLB_div (show (translDiff P.A P.L x₀).IsLB from LB.isLB_linComb P.isLB _ _)
      (pull_isLB hO (snd _ P.A).left)
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ?_
    rw [cls_pull hM, (cls_eq_zero_iff hM).2 hx₀, map_zero]⟩
  have : IsIso H.hom := isIso_of_flat_of_closedPoint H.hom (y.left (IsLocalRing.closedPoint K))
    ((congrArg (fun q => q (IsLocalRing.closedPoint K)) (Over.w y)).trans (IsLocalRing.comap_closedPoint φ))
  let σ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ H := Over.homMk (inv H.hom) (IsIso.inv_hom_id _)
  obtain ⟨U, hU, ht⟩ := (hH _ (σ ≫ j)).2 ⟨σ, rfl⟩ (IsLocalRing.closedPoint V)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  have e := pull_eq_zero_of_mem ((fst _ P.A).left ⁻¹ᵁ ⊤) (lift (toUnit P.A) (𝟙 P.A)).left (fun _ => trivial)
    ((triv_iff P.isLB hO (σ ≫ j) _).1 ht)
  rw [map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul,
    lift_snd, lift_fst_assoc, sub_eq_zero, Over.id_left, pull_id (cls O hO)] at e
  exact ⟨σ ≫ j, (cls_eq_iff hO (LB.isLB_linComb P.isLB _ _)).1 (e.symm.trans (cls_pair P.isLB _ _ _).symm)⟩

end GlobalTheory.PrimitiveOverValuationRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KernelFiniteFlatHolds
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.kernelFiniteFlat_holds : _root_.GlobalTheory.Published.KernelFiniteFlatSt :=
  _root_.GlobalTheory.KernelFlat.kernelFiniteFlat _root_.GlobalTheory.abelianSchemeLaws_all.1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkInjectiveClosed
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionMapInj


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.TorsionMapInj.qkToAk_injective_closed : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.QkToAkInjSt :=
  _root_.GlobalTheory.TorsionMapInj.qkToAk_injective _root_.GlobalTheory.abelianSchemeLaws_all.1 _root_.GlobalTheory.abelianSchemeLaws_all.2

end GlobalTheory.TorsionMapInj
end

