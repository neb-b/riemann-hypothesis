module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2298
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularOverlatticeRiemannForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2311
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackPeriodConstantsSymmetric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart.SwapIso

open GlobalTheory.LamBiext GlobalTheory.LamRigid

variable {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B]
  [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B']


variable (B') in
abbrev sw2 : Fin 2 → ((G2 B').left ⟶ (G2 B').left) :=
  ![(lift (fst B' B') (snd B' B')).left, (lift (snd B' B') (fst B' B')).left]

theorem lift_comp_squareFactorIdentity_eq_lift {T : Over S'} (a b : T ⟶ B') : (lift a b).left ≫ sw2 B' 0 = (lift a b).left := by
  show (lift a b).left ≫ (lift (fst B' B') (snd B' B')).left = _
  rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]

theorem lift_comp_squareFactorSwap_eq_lift_swap {T : Over S'} (a b : T ⟶ B') : (lift a b).left ≫ sw2 B' 1 = (lift b a).left := by
  show (lift a b).left ≫ (lift (snd B' B') (fst B' B')).left = _
  rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]

theorem formEq_sw {f : S' ⟶ S} {β : B'.left ⟶ B.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (hβ : IsGrpPullback B' B f β) (hsq : IsSquare β β₂) :
    FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (flatφ (lamφ B) fun k => sw2 B' k ≫ β₂) (flatε lamε ![1, -1]) := by
  have hw₀ : β ≫ B.hom = B'.hom ≫ f := hβ.1.w
  have β₂_lift : ∀ {T₀ : Over S'} (a b : T₀ ⟶ B'),
      (lift a b).left ≫ β₂ = (lift (toBase hw₀ a) (toBase hw₀ b)).left := fun a b => square_over_hom_ext
    (by rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]; rfl)
    (by rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]; rfl)
  intro U _ h
  rw [GlobalTheory.LamBiext.prod_flat, Fin.prod_univ_two, Fintype.prod_empty]
  show 1 = (∏ i, h (((lift (fst B' B') (snd B' B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (1 : ℤ) *
    (∏ i, h (((lift (snd B' B') (fst B' B')).left ≫ β₂) ≫ lamφ B i) ^ lamε i) ^ (-1 : ℤ)
  rw [β₂_lift, β₂_lift, GlobalTheory.LamBiext.prod_lam, GlobalTheory.LamBiext.prod_lam, _root_.mul_comm (toBase hw₀ (snd B' B'))]
  apply Additive.ofMul.injective
  simp only [zpow_neg, zpow_one, ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem exists_gen_sw {f : S' ⟶ S} {β : B'.left ⟶ B.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (hβ : IsGrpPullback B' B f β) (hsq : IsSquare β β₂) {M : LB B.left} (hM : M.IsLB) :
    ∃ t : LB.Gen (LB.LinComb (abelian₂ B M) (fun k => sw2 B' k ≫ β₂) ![1, -1]), t.IsGen ∧
      ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z : Z) (J : (Z ⟶ B.left) → M.ι), Good M z J →
        val (L := abelian₂ B M) t r z (ind B J) = 1 := by
  obtain ⟨g, hg, hv⟩ := exists_gen hM (formEq_sw hβ hsq) (LB.oneGen M) (oneGen_isGen _)
  refine ⟨GlobalTheory.LamBiext.nest M (lamφ B) lamε (fun k => sw2 B' k ≫ β₂) ![1, -1] g, nest_isGen hg,
    fun r z J hJ => ?_⟩
  refine (val_nest hg r (good_ind hJ) hJ).trans ?_
  simp only [adj_ind hM hJ, one_zpow, Finset.prod_const_one, _root_.one_mul]
  exact (hv _ r z J hJ).trans (val_one r)

end GlobalTheory.TChart.SwapIso

namespace GlobalTheory.TChart.SwapIso

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.Mum.Two

variable {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B]
  [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B']

theorem isoVal_swap (hB' : IsAbelianScheme B') {M : LB B.left} {M₁ : LB B₁.left} (hM : M.IsLB) (hM₁ : M₁.IsLB)
    {f : S' ⟶ S} {f₁ : S' ⟶ S₁} {β : B'.left ⟶ B.left} {β₁ : B'.left ⟶ B₁.left}
    {β₂ : (G2 B').left ⟶ (G2 B).left} {β₂' : (G2 B').left ⟶ (G2 B₁).left}
    (hβ : IsGrpPullback B' B f β) (hβ₁ : IsGrpPullback B' B₁ f₁ β₁) (hsq : IsSquare β β₂) (hsq₁ : IsSquare β₁ β₂')
    (w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂')) (hw : w.IsGen) {T : Over S'} (x y : T ⟶ B')
    (z : T.left) (J : (T.left ⟶ B₁.left) → M₁.ι) (J' : (T.left ⟶ B.left) → M.ι) (hJ : Good M₁ z J)
    (hJ' : Good M z J') :
    isoVal w (lift x y).left z J J' = isoVal w (lift y x).left z J J' := by
  have hG := GlobalTheory.globalFns_holds
  have hL : (abelian₂ B₁ M₁).IsLB := DVR.linComb_isLB _ hM₁ _ _
  have hL' : ((abelian₂ B M).pull β₂).IsLB := DVR.linComb_isLB _ (DVR.linComb_isLB _ hM _ _) _ _
  obtain ⟨t, ht, hvt⟩ := exists_gen_sw hβ₁ hsq₁ hM₁
  obtain ⟨g, hg, hvg⟩ := exists_gen_sw hβ hsq hM
  let c := chartPullLinComb (abelian₂ B M) β₂ (sw2 B') (fun k => sw2 B' k ≫ β₂) ![1, -1] (𝟙 _)
    (fun k => (Category.id_comp _).symm)
  have ha : (cGen c g).IsGen := cGen_isGen c hg
  have good_P : ∀ {Z : Scheme.{0}} {z₀ : Z} {J₀ : (Z ⟶ B.left) → M.ι}, Good M z₀ J₀ →
      Good ((abelian₂ B M).pull β₂) z₀ (fun q _ => ind B J₀ (q ≫ β₂)) :=
    fun hJ₀ q => mem_pull.2 (good_ind hJ₀ (q ≫ β₂))
  have Fa : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z₀ : Z) (J₀ : (Z ⟶ B.left) → M.ι), Good M z₀ J₀ →
      val (cGen c g) r z₀ (fun q _ => ind B J₀ (q ≫ β₂)) = 1 := by
    intro Z r z₀ J₀ hJ₀
    rw [← hvg r z₀ J₀ hJ₀, val_of g r z₀ (ind B J₀) (fun k => ind B J₀ ((r ≫ sw2 B' k) ≫ β₂))
      (fun k => by rw [Category.assoc])]
    exact gm_res r z₀ _ ((good_P hJ₀).mem _ r) _
  have gw_iso : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (φ : (G2 B').left ⟶ (G2 B').left) (z₀ : Z)
      (J₀ : (Z ⟶ B₁.left) → M₁.ι) (J₀' : (Z ⟶ B.left) → M.ι),
      gw w (r ≫ φ) z₀ (ind B₁ J₀ (r ≫ φ ≫ β₂')) (fun _ => ind B J₀' ((r ≫ φ) ≫ β₂)) =
        isoVal w (r ≫ φ) z₀ J₀ J₀' := by
    intro Z r φ z₀ J₀ J₀'
    have e₁ : ind B₁ J₀ (r ≫ φ ≫ β₂') = fun I => J₀ ((r ≫ φ) ≫ β₂' ≫ (psum B₁ (x2 B₁) I.down).left) :=
      funext fun I => congrArg J₀ (by simp only [Category.assoc])
    have e₂ : ind B J₀' ((r ≫ φ) ≫ β₂) = fun I => J₀' ((r ≫ φ) ≫ β₂ ≫ (psum B (x2 B) I.down).left) :=
      funext fun I => congrArg J₀' (by simp only [Category.assoc])
    rw [e₁, e₂]; rfl
  have Fp : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G2 B').left) (z₀ : Z) (J₀ : (Z ⟶ B₁.left) → M₁.ι)
      (J₀' : (Z ⟶ B.left) → M.ι),
      pw w (sw2 B') ![1, -1] r z₀ (fun k => ind B₁ J₀ (r ≫ sw2 B' k ≫ β₂'))
        (fun k => (fun (q : Z ⟶ (G2 B').left) (_ : PUnit) => ind B J₀' (q ≫ β₂)) (r ≫ sw2 B' k)) =
        isoVal w (r ≫ sw2 B' 0) z₀ J₀ J₀' * (isoVal w (r ≫ sw2 B' 1) z₀ J₀ J₀')⁻¹ := by
    intro Z r z₀ J₀ J₀'
    unfold pw
    rw [Fin.prod_univ_two]
    rw [gw_iso r (sw2 B' 0) z₀ J₀ J₀', gw_iso r (sw2 B' 1) z₀ J₀ J₀']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zpow_one, zpow_neg]
  have he2 : (lift (1 : 𝟙_ (Over S') ⟶ B') 1).left ≫ (snd B' B').left ≫ B'.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift (1 : 𝟙_ (Over S') ⟶ B') 1)
  have E := rigid_pw w hw hL hL' (sw2 B') ![1, -1] ha ht _ _ he2
    (surj_comp (surj_snd hG hB' _) (hG _ _ hB').2) (fun y₀ => by
      obtain ⟨J₁, hJ₁⟩ := GlobalTheory.UU.exists_good_pt hM₁ y₀
      obtain ⟨J₁', hJ₁'⟩ := GlobalTheory.UU.exists_good_pt hM y₀
      refine ⟨ind B₁ J₁, fun q _ => ind B J₁' (q ≫ β₂), good_ind hJ₁, good_P hJ₁', ?_⟩
      rw [hvt _ y₀ J₁ hJ₁, Fp, Fa _ y₀ J₁' hJ₁', lift_comp_squareFactorIdentity_eq_lift, lift_comp_squareFactorSwap_eq_lift_swap, mul_inv_cancel, _root_.mul_one])
    T.left (lift x y).left z (ind B₁ J) (fun q _ => ind B J' (q ≫ β₂)) (good_ind hJ) (good_P hJ')
  rw [hvt _ z J hJ, Fp, Fa _ z J' hJ', lift_comp_squareFactorIdentity_eq_lift, lift_comp_squareFactorSwap_eq_lift_swap, _root_.mul_one] at E
  exact mul_inv_eq_one.1 E.symm

end GlobalTheory.TChart.SwapIso

namespace GlobalTheory.TChart

theorem periodConst_symm : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → IsNormIso w₁ → ∀ a b, q a b = q b a := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' hV hVd hV₁ hV₁d hf₁ hfin hloc hκ hpb hpb' hsq hsq'
    x hx w₁ q hgen hper hnorm a b
  have hAb : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback D.toPre.P.isAb hpb
  obtain ⟨κK, hκK⟩ : ∃ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁ := by
    have hi : Function.Injective ((algebraMap V₁ (FractionRing V₁)).comp f₁) :=
      (IsFractionRing.injective V₁ (FractionRing V₁)).comp hf₁
    obtain ⟨g, eg⟩ : ∃ g : FractionRing V →+* FractionRing V₁,
        g.comp (algebraMap V (FractionRing V)) = (algebraMap V₁ (FractionRing V₁)).comp f₁ :=
      ⟨IsLocalization.lift (M := nonZeroDivisors V) (g := (algebraMap V₁ (FractionRing V₁)).comp f₁) fun y =>
        IsUnit.mk0 _ ((map_ne_zero_iff _ hi).2 (nonZeroDivisors.coe_ne_zero y)), IsLocalization.lift_comp _⟩
    refine ⟨spMap g, ?_⟩
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, eg]
  let z : (TK V₁).left := (⊥ : PrimeSpectrum (FractionRing V₁))
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt L.T.M.isLB z
  obtain ⟨J', hJ'⟩ := GlobalTheory.UU.exists_good_pt D.toPre.P.isLB z
  have h₁ := hper κK hκK a b z J J' hJ hJ'
  have h₂ := hper κK hκK b a z J J' hJ hJ'
  rw [GlobalTheory.Mum.RosatiSymmetry.val_tau_symm D.toPre hJ' κK,
    val_corr hJ (corr_of_val L.T.M.isLB (L.T.τ₀_symm ((n : ℤ) • b) ((n : ℤ) • a))),
    GlobalTheory.TChart.SwapIso.isoVal_swap hAb D.toPre.P.isLB L.T.M.isLB hpb hpb' hsq hsq' w₁ hgen
      (toUnit (TK V₁) ≫ x b) (toUnit (TK V₁) ≫ x a) z J J' hJ hJ'] at h₂
  have hq := mul_right_cancel (h₁.symm.trans h₂)
  have hs : Subsingleton (TK V₁).left := (inferInstance : Subsingleton (PrimeSpectrum (FractionRing V₁)))
  have eu : unitOn (q a b) = unitOn (q b a) := unit_ext fun y _ => by rw [Subsingleton.elim y z]; exact hq
  exact Units.map_injective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V₁))).inv).1 eu

end GlobalTheory.TChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.MultPull

open GlobalTheory.TrueGeo.SmallSec GlobalTheory.FrameGlue.Pull

theorem isRatSec_pull_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
    (hη : j (genericPoint Y) ⤳ genericPoint X) {L : LB X} {r : L.ι → X.functionFieldˣ}
    (hr : IsRatSec L r) :
    IsRatSec (L.pull j) fun c => Units.map (fnMap j hη).toMonoidHom (r (c PUnit.unit)) := by
  intro c c' h
  have l : (L.pull j).U c ⊓ (L.pull j).U c' ≤ j ⁻¹ᵁ (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have h₁ : genericPoint Y ∈ j ⁻¹ᵁ (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)) := l h
  have h₀ : genericPoint X ∈ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    (genericPoint_specializes _).mem_open (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)).isOpen h₁
  have e : (L.pull j).g c c' = res l (pullU j _ (L.g (c PUnit.unit) (c' PUnit.unit))) := by
    change ∏ _k : PUnit, _ = _
    exact (Fintype.prod_unique _).trans (zpow_one _)
  change fnMap j hη (r (c PUnit.unit) : X.functionField) =
    fnOf _ h ((L.pull j).g c c' : Γ(Y, (L.pull j).U c ⊓ (L.pull j).U c')) *
      fnMap j hη (r (c' PUnit.unit) : X.functionField)
  rw [hr _ _ h₀, map_mul, fnMap_fnOf j hη h₀ h₁, e]
  first
    | exact congrArg (· * _) (fnOf_resG l h _)
    | exact congrArg (· * _) (fnOf_resG l h _).symm

theorem ord_fnMap {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (j : Y ⟶ X) (hη : j (genericPoint Y) ⤳ genericPoint X) (y : Y)
    [IsIso (j.stalkMap y)] (f : X.functionField) :
    Scheme.ord (fnMap j hη f) y = Scheme.ord f (j y) := by
  let e : X.presheaf.stalk (j y) ≃+* Y.presheaf.stalk y :=
    (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
  have he (a : X.presheaf.stalk (j y)) : e a = j.stalkMap y a := rfl
  have hc : Order.coheight y = Order.coheight (j y) := by
    have := ringKrullDim_eq_of_ringEquiv e
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at this
    exact_mod_cast this.symm
  by_cases hz : Order.coheight (j y) = 1
  swap
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one (hc ▸ hz), Scheme.ord_eq_zero_of_coheight_neq_one hz]
  have hz' : Order.coheight y = 1 := hc.trans hz
  have key (a : X.presheaf.stalk (j y)) (ha : a ≠ 0) :
      Scheme.ord (fnMap j hη (algebraMap _ X.functionField a)) y =
        Scheme.ord (algebraMap _ X.functionField a) (j y) := by
    have ha' : j.stalkMap y a ≠ 0 := by rw [← he]; exact (map_ne_zero_iff _ e.injective).2 ha
    rw [fnMap_algebraMap, ord_algebraMap hz' ha', ord_algebraMap hz ha, ← he]
    exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) (ord_map_ringEquiv e a)
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (j y)) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap _ X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hf (by rw [← hab, map_zero, zero_div])
  have hfb : f * algebraMap _ X.functionField b = algebraMap _ X.functionField a := by
    rw [← hab, div_mul_cancel₀ _ hb']
  have h₁ := Scheme.ord_mul (x := j y) hf hb'
  have hfm : fnMap j hη f ≠ 0 := (map_ne_zero_iff _ (fnMap j hη).injective).2 hf
  have hbm : fnMap j hη (algebraMap _ X.functionField b) ≠ 0 :=
    (map_ne_zero_iff _ (fnMap j hη).injective).2 hb'
  have h₂ := Scheme.ord_mul (x := y) hfm hbm
  rw [← map_mul, hfb] at h₂
  rw [hfb] at h₁
  rw [key a ha0, key b hb0] at h₂
  omega

end GlobalTheory.MultPull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RechartAtUnitaryClassicalTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Points GlobalTheory.ZM GlobalTheory.SiegelTor

namespace GlobalTheory.UPoinc

theorem rechart_at_uClassical_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (U : X.M.Z.Opens) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U → (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) ∈ U → spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ → X.M.ringOn U ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) ∧ ∃ y₁ : ratHull (X.M.ringOn U) →+* PadicAlgCl p, (∀ a : X.M.ringOn U, y₁ (toRat _ a) = X.M.val (gPt p ≫ ct.y) a) ∧ spMap y₁ ≫ u' = spMap ct.ι ≫ ct.T.y ∧ ∀ a : X.o₁, ‖y₁ (toRat _ (algebraMap X.o₁ (X.M.ringOn U) a))‖ ≤ 1 := by
  intro E _ _ _ H Dw hpq l Xo cf C X p _ z ct U u' hU hwU hu'
  haveI := X.ar.char
  set w := (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) with hw
  have hne : (U : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  have hle : X.M.ringOn U ≤ X.M.O w := RatModel.ringOn_le_O hwU
  have hsp : ∀ w', (gPt p ≫ ct.y) w' ⤳ w := fun w' => by
    rw [Subsingleton.elim w' (closedPoint (PadicAlgCl p))]
  let y₀ : X.M.ringOn U →+* PadicAlgCl p :=
    (RatModel.valHomOf (gPt p ≫ ct.y) w hsp).comp (Subalgebra.inclusion hle).toRingHom
  have hy₀ : ∀ a : X.M.ringOn U, y₀ a = X.M.val (gPt p ≫ ct.y) a := fun a => rfl
  obtain ⟨y₁, hy₁, -⟩ := existsUnique_ratLift (X.M.ringOn U) (K := PadicAlgCl p)
    (fun n hn => IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)) y₀
  have hy₁' : ∀ a : X.M.ringOn U, y₁ (toRat _ a) = y₀ a := fun a => RingHom.congr_fun hy₁ a
  let e : Sp (X.M.ringOn U) ⟶ X.M.Z :=
    Spec.map (CommRingCat.ofHom (X.M.sectionsEquiv U hne).toRingHom) ≫ hU.fromSpec
  have he : ∀ {K : Type} [CommRing K] (φ : X.M.ringOn U →+* K), ⊤ ≤ (spMap φ ≫ e) ⁻¹ᵁ U ∧
      ∀ f, valR (spMap φ ≫ e) U f = φ (X.M.sectionsEquiv U hne f) := by
    intro K _ φ
    have e2 : spMap φ ≫ e = Spec.map (CommRingCat.ofHom (φ.comp (X.M.sectionsEquiv U hne).toRingHom)) ≫
        hU.fromSpec := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    rw [e2]
    have hx := le_preimage_specMap_fromSpec hU (CommRingCat.ofHom (φ.comp (X.M.sectionsEquiv U hne).toRingHom))
    refine ⟨hx, fun f => ?_⟩
    rw [valR_eq _ U hx, valMap_specMap_fromSpec]
    rfl
  have hyU : ⊤ ≤ (gPt p ≫ ct.y) ⁻¹ᵁ U := (le_preimage_iff _ U).2 hwU
  have ha : spMap y₀ ≫ e = gPt p ≫ ct.y := by
    refine ext_of_valR hU (he y₀).1 hyU fun f => ?_
    rw [(he y₀).2, hy₀, RatModel.coe_sectionsEquiv, RatModel.val_valF ((top_le_preimage_iff _ _).1 hyU)]
    rfl
  have hgen : spMap (X.M.ringOn U).val.toRingHom ≫ e = X.M.pt := by
    refine ext_of_valR hU (he _).1 (X.M.top_le_preimage_pt hne) fun f => ?_
    rw [(he _).2]
    exact (RatModel.coe_sectionsEquiv U hne f).trans (valF_eq_valR _ _ _)
  have hdom : IsDominant (spMap (ratHull (X.M.ringOn U)).val.toRingHom) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)⟩
  haveI : IsProper C.z := ThetaDescent.isProper_of_isProjOver C.proj
  have hgen2 : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ ((spMap (toRat _) ≫ e) ≫ X.π) =
      spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ (u' ≫ C.i) := by
    rw [← Category.assoc, ← Category.assoc, spMap_val_toRat, hgen, X.comp, ← Category.assoc _ u' C.i, hu']
    simp only [USetup.uΩ, Category.assoc]
  have hb : (spMap (toRat _) ≫ e) ≫ X.π = u' ≫ C.i :=
    ext_of_isDominant_of_isSeparated C.z
      (ext_of_isDominant (spMap (ratHull (X.M.ringOn U)).val.toRingHom) (by
        simp only [← Category.assoc] at hgen2 ⊢; rw [hgen2]))
      (spMap (ratHull (X.M.ringOn U)).val.toRingHom) hgen2
  haveI := C.isPreimmersion_i
  have hy01 : spMap y₁ ≫ spMap (toRat (X.M.ringOn U)) = spMap y₀ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hy₁]
  have hpt' : spMap y₁ ≫ u' = spMap ct.ι ≫ ct.T.y := by
    rw [← cancel_mono C.i, Category.assoc, ← hb, ← Category.assoc, ← Category.assoc, hy01, ha, Category.assoc,
      ct.comm, Category.assoc]
  let τ := Spec.preimage (ct.y ≫ X.M.s)
  have hσ : (gPt p ≫ ct.y) ≫ X.M.s = spMap ((OO p).subtype.comp τ.hom) := by
    rw [Category.assoc, ← Spec.map_preimage (ct.y ≫ X.M.s), ← Spec.map_comp]; rfl
  refine ⟨hle, y₁, fun a => (hy₁' a).trans (hy₀ a), hpt', fun a => ?_⟩
  rw [hy₁', hy₀]
  show ‖X.M.val (gPt p ≫ ct.y) (algebraMap X.o₁ X.Ω₁ a)‖ ≤ 1
  rw [RatModel.val_algebraMap hσ a]
  exact (mem_OO_iff _).1 (τ.hom a).2

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfAffineNonzeroLocusAbelianSchemeNoether
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AffineLocusAmple

theorem relAmple_of_affine_nonzeroLocus : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ s : LB.Sec M, IsAffineOpen (Out.nonzeroLocus s) → (∀ p : Sp R, ∃ x ∈ Out.nonzeroLocus s, A.hom x = p) → Out.RelAmple A M := by
  intro R _ _ A _ hA M hM s hV hs
  have := hA.proper
  have := hA.smooth
  refine GlobalTheory.ProperFinite.relAmple_of_geometricFibres A hM fun K _ _ y => ?_
  obtain ⟨n, a, ha⟩ := _root_.GlobalTheory.FibreCover.cover_geometric_fibre (Sp R) A hA _ K y fun z => hs (y z)
  have : IsAffine (Over.mk y).left := inferInstanceAs (IsAffine (Sp K))
  have h := _root_.GlobalTheory.isAmpleLB_pull_fst_of_translates R A hA M hM _ _ rfl hV ⟨M, hM, s, rfl, rfl⟩ (Over.mk y) n a ha
    fun i => GlobalTheory.cechPic_sp_field_eq_zero K _
  exact h

end GlobalTheory.AffineLocusAmple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfAppellHumbert
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LefschetzAmple

theorem relAmple_of_isAH : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → Out.RelAmple A M := by
  intro g A _ hA M u Hm χ hM hAH
  have hint : ∀ l ∈ u.Λ, ∀ l' ∈ u.Λ, ∃ n : ℤ, (hermForm Hm l l').im = n := by
    intro l hl l' hl'
    have h1 := GlobalTheory.LatticeHom.semicharacter_add u hM hAH ⟨l, hl⟩ ⟨l', hl'⟩
    have h2 := GlobalTheory.LatticeHom.semicharacter_add u hM hAH ⟨l', hl'⟩ ⟨l, hl⟩
    rw [add_comm] at h2
    have hsw := GlobalTheory.LatticeHom.hermForm_swap_of_isHermitian hAH.1 l l'
    have him : (hermForm Hm l' l).im = -(hermForm Hm l l').im := by
      rw [hsw, Complex.conj_im]
    have hne : χ ⟨l, hl⟩ * χ ⟨l', hl'⟩ ≠ 0 := by
      refine mul_ne_zero ?_ ?_ <;> refine norm_ne_zero_iff.1 ?_ <;> rw [hAH.2.2.1] <;> norm_num
    have h3 : Complex.exp (Real.pi * Complex.I * (hermForm Hm l l').im) =
        Complex.exp (Real.pi * Complex.I * (hermForm Hm l' l).im) := by
      refine mul_left_cancel₀ hne ?_
      rw [← h1, h2]
      ring
    rw [him] at h3
    have h4 : Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm l l').im) = 1 := by
      have e : (2 * Real.pi * Complex.I * (hermForm Hm l l').im : ℂ) =
          Real.pi * Complex.I * (hermForm Hm l l').im - Real.pi * Complex.I * ((-(hermForm Hm l l').im : ℝ) : ℂ) := by
        push_cast; ring
      rw [e, Complex.exp_sub, h3, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h4
    refine ⟨n, ?_⟩
    have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := mul_right_cancel₀ hπ (by rw [← hn]; ring : ((hermForm Hm l l').im : ℂ) * (2 * Real.pi * Complex.I) = n * (2 * Real.pi * Complex.I))
    exact_mod_cast this
  obtain ⟨Λ₁, Ef, N, hle, hd1, hf1, hEf, hbij, hN, hNΛ⟩ := _root_.GlobalTheory.Overlattice.exists_unimodular_overlattice g u.Λ Hm u.discrete u.full hAH.1 hAH.2.1 hint
  obtain ⟨P, uB, χB, hg, hΛB, hAHB, -, -⟩ :=
    GlobalTheory.principalTorus_algebraic g Λ₁ Hm Ef hd1 hf1 hAH.1 hAH.2.1 hEf hbij
  have hle' : u.Λ ≤ uB.Λ := hΛB ▸ hle
  have hNΛ' : ∀ x ∈ uB.Λ, N • x ∈ u.Λ := hΛB ▸ hNΛ
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.SemicharShift.exists_shift_of_semichar g u.Λ uB.Λ Hm χ χB hle' u.discrete u.full hAH.1 hAH.2.1 hAH.2.2.1 hAHB.2.2.1
    (GlobalTheory.LatticeHom.semicharacter_add u hM hAH) (GlobalTheory.LatticeHom.semicharacter_add uB P.isLB hAHB)
  obtain ⟨ψ, hψ, hψex, hcov⟩ := _root_.GlobalTheory.ThetaShift.exists_morphism_affine_cover g A hA M u Hm χ hM hAH (fun θ => _root_.GlobalTheory.ThetaGAGA.exists_isFnPow g A hA M u Hm χ hM hAH 4 θ)
    P uB χB hle' a hg hAHB ha
  have hψa : IsAffineHom ψ := _root_.GlobalTheory.LiftAffine.isAffineHom_of_lift g A hA P.A P.isAb M P.L u uB a N hN hle' hNΛ' ψ hψ hψex
  have : IsProper A.hom := hA.proper
  exact (GlobalTheory.FrameCompare.relAmple_iff A.hom hM).2 inferInstance fun x => by
    obtain ⟨s, V, hx, hV, hs⟩ := hcov x
    exact ⟨4, s, by norm_num, hx, hs ▸ hV.preimage ψ⟩

end GlobalTheory.LefschetzAmple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedIdentificationsGenericFibreAgreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidified_identifications_generic_fibre_agree : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∀ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w → PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) → ∀ (Z : Scheme.{0}) (f : Z ⟶ E.P.A.left) (z : Z) (j : D₂.P.L.ι) (i : D₃.P.L.ι) (k : E.P.L.ι) (l : D₁.P.L.ι), GlobalTheory.PsiEvenPull.proj q₂ (f z) ∈ D₂.P.L.U j → κ (f z) ∈ D₃.P.L.U i → f z ∈ E.P.L.U k → GlobalTheory.PsiEvenPull.proj q₁ (f z) ∈ D₁.P.L.U l → gw w (f ≫ κ) z j i * (gw p.w (f ≫ κ) z l i)⁻¹ = gw q₂.w f z j k * (gw q₁.w f z l k)⁻¹ := by
  first | exact @GlobalTheory.GenEqual.genequal | exact GlobalTheory.GenEqual.genequal | (intros; apply GlobalTheory.GenEqual.genequal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiStarMulKillsPointOfTrivialPairingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosati_star_mul_kills_point_of_trivial_pairing : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (O : Type) [Ring O] [StarRing O] (oA : P.OAct O) (e f : O) (H : Over (Sp K)) (a : H ⟶ P.A) (r : P.A ⟶ H), r ≫ a = oA.act e → ∀ (T : Over (Sp K)) (y : T ⟶ P.A), (∃ t : LB.Gen (letI := P.isAb.comm; (abelian₂ P.A P.L).pull (lift (snd H T ≫ y) (fst H T ≫ a ≫ oA.act f) : H ⊗ T ⟶ G2 P.A).left), t.IsGen) → y ≫ oA.act (star e * star f) = toUnit T ≫ η[P.A] := by
  first | exact @GlobalTheory.Mum.kill_of_lam_triv | exact GlobalTheory.Mum.kill_of_lam_triv | (intros; apply GlobalTheory.Mum.kill_of_lam_triv <;> assumption)
end

