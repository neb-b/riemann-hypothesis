module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLbOfGeneratedSystem
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0129
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationValuesIntOfAdmissibleBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsEqDegenerationSeries
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxCosetCriterion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0166
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleOfThickenings
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBAlgLocal

open GlobalTheory.MorAlg GlobalTheory.LBAlg

theorem exists_veryAmpleBy_of_isPullback {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R')} {φ : X' ⟶ X} (g : R →+* R')
    (h : IsPullback φ f' f (Spec.map (CommRingCat.ofHom g))) {H : LB X} (hH : H.IsLB) {m : ℕ}
    {σ : Fin (m + 1) → LB.Sec H} (hσ : VeryAmpleBy f H σ) :
    ∃ σ' : Fin (m + 1) → LB.Sec (H.pull φ), VeryAmpleBy f' (H.pull φ) σ' := by
  obtain ⟨σ₀, w₀, hw₀, c₀⟩ := exists_isPull φ hH σ
  refine ⟨σ₀, GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H m σ hH hσ _ g _ _ φ h.w ?_ _ w₀ _
    (pull_isLB hH _) hw₀ c₀⟩
  have e : pullback.lift φ f' h.w = h.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  rw [e]
  infer_instance

theorem exists_lineBundle_of_thickenings : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∃ M : LB B.left, M.IsLB ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro R _ _ _ I hI hcomp Y β hβ B b hB hfl hb hc N v hN
  obtain ⟨H, hH, m, σ, hσ⟩ := id hB
  have hL : ∀ e, (H.pull (b e)).IsLB := fun e => pull_isLB hH _
  choose σ' hva using fun e =>
    exists_veryAmpleBy_of_isPullback (Ideal.Quotient.mk (I ^ (e + 1))) (hb e) hH hσ
  have hI' : I ^ (0 + 1) ≠ ⊤ := by simpa using hI
  have : Nontrivial (R ⧸ I ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hI'
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (R ⧸ I ^ (0 + 1))
  let _ := Ideal.Quotient.field 𝔪
  have hπ := IsPullback.of_hasPullback (Y 0).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪)))
  generalize pullback.snd (Y 0).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪))) = f₀ at hπ
  generalize pullback.fst (Y 0).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪))) = π at hπ
  obtain ⟨σ₀, hσ₀⟩ := exists_veryAmpleBy_of_isPullback (Ideal.Quotient.mk 𝔪) hπ (hL 0) (hva 0)
  obtain ⟨t₁, ht₁⟩ := GlobalTheory.AbLaw.serre_h1Zero_and_sections_polynomial.1 _ _ _ _ _ _ (pull_isLB (hL 0) π) hσ₀ ((N 0).pull π) (pull_isLB (hN 0).1 π)
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.TwistGen.twist_generated _ _ _ _ _ _ (hL 0) (hva 0) (N 0) (hN 0).1
  obtain ⟨t, h₁, h₂⟩ : ∃ t, t₁ ≤ t ∧ t₂ ≤ t := ⟨max t₁ t₂, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨n, u, hu⟩ := ht₂ t h₂
  have hT : ∀ e, (tw (N e) (H.pull (b e)) t).IsLB := fun e => isLB_tw (hN e).1 (hL e) t
  have hv' : ∀ e, LBIso (tw (N e) (H.pull (b e)) t) ((tw (N (e + 1)) (H.pull (b (e + 1))) t).pull (β e)) :=
    fun e => LBIso.trans (hT e) (isLB_tw (pull_isLB (hN (e + 1)).1 _) (hL e) t) (pull_isLB (hT (e + 1)) _)
      (lbIso_tw_congr (hL e) t ⟨v e, (hN e).2⟩)
      (LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullSame H _ _ _ (β e) fun _ => (hc e).symm) t) (Geo.Tor.chartPullPull _ _ _ rfl)
        (lbIso_self (hT (e + 1))))
  choose v' hv' using hv'
  have hflY : ∀ e, Flat (Y e).hom := fun e => MorphismProperty.of_isPullback (P := @Flat) (hb e) hfl
  have hP : ∀ e, IsProjBy (Y e).hom := fun e => ⟨_, hL e, m, σ' e, hva e⟩
  obtain ⟨w₀, hw₀⟩ : LBIso (tw ((N 0).pull π) ((H.pull (b 0)).pull π) t) ((tw (N 0) (H.pull (b 0)) t).pull π) :=
    LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl) t)
      (Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_self (hT 0))
  choose s hs0 hs using fun j => GlobalTheory.SecLifts.exists_compatible_sections_local R I hI Y β hβ hflY hP
    (fun e => tw (N e) (H.pull (b e)) t) v' (fun e => ⟨hT e, hv' e⟩) _ (Ideal.Quotient.mk 𝔪)
    Ideal.Quotient.mk_surjective _ π f₀ hπ _ w₀ (isLB_tw (pull_isLB (hN 0).1 π) (pull_isLB (hL 0) π) t) hw₀
    (ht₁ t h₁) (u j)
  obtain ⟨M, hM, hNM⟩ := GlobalTheory.GenSystem.exists_lb_of_generated_system R I hI hcomp Y β hβ B b hB hfl hb hc
    (fun e => tw (N e) (H.pull (b e)) t) v' (fun e => ⟨hT e, hv' e⟩) n (fun e j => s j e) (fun e j => hs j e)
    (by simpa only [hs0] using hu)
  have hM' : (tw M H (-t)).IsLB := isLB_tw hM hH _
  refine ⟨tw M H (-t), hM', fun e => ?_⟩
  have hO' : (tw (M.pull (b e)) (H.pull (b e)) (-t)).IsLB := isLB_tw (pull_isLB hM _) (hL e) _
  exact LBIso.trans (hN e).1 hO' (pull_isLB hM' _)
    (LBIso.trans (hN e).1 (isLB_tw (hT e) (hL e) _) hO' (lbIso_tw_tw (hN e).1 (hL e) t)
      (lbIso_tw_congr (hL e) (-t) (hNM e)))
    (LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl) (-t))
      (Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_self hM'))

end GlobalTheory.LBAlgLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.PerpTorus
open GlobalTheory.ZH.TorusPerp GlobalTheory.TorusExt

theorem exists_form {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) {X : Type} [AddCommGroup X]
    (yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range) (hs : Function.Surjective yy)
    (a : S.Gam) (ha : a ∈ S.perp yy.ker) :
    ∃ m : X →+ ZMod (S.r * S.N), ∀ b α, yy b = QuotientAddGroup.mk α → m α = eStd S.g _ a b := by
  choose σ hσ using fun α : X => hs (QuotientAddGroup.mk α)
  have ind : ∀ b b' : S.Gam, yy b = yy b' → eStd S.g _ a b = eStd S.g _ a b' := by
    intro b b' e
    have h0 : eStd S.g _ a (b - b') = 0 := ha _ (by rw [AddMonoidHom.mem_ker, map_sub, e, sub_self])
    rw [← sub_add_cancel b b', eStd_add_right, h0, zero_add]
  refine ⟨AddMonoidHom.mk' (fun α => eStd S.g _ a (σ α)) fun α β => ?_, fun b α e => ind _ _ ((hσ α).trans e.symm)⟩
  rw [← eStd_add_right]
  exact ind _ _ (by rw [map_add (f := _), hσ, hσ, hσ, QuotientAddGroup.mk_add])


attribute [local instance] gtGroup in
theorem exists_torus_point : LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (g : u.Geom) (a : S.Gam) (ha : a ∈ S.perp l.yy.ker), ∃ (q : QkPt u.D.toPre (PadicAlgCl p) S.N) (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) S.N q (g.pt (S.r • a)) ∧ ∀ χ, (τ (Multiplicative.ofAdd χ) : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζN ^ (l.wt χ ⟨a, ha⟩).val)) := by
  intro hL hT o Ω _ _ _ hA S ρ p _ y₀ u l g a ha
  have hG := hL.1.globalFns
  have hN := S.N_ge
  have hr := S.r_pos
  have hn : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : IsDomain o := hA.inj.isDomain _
  have : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have hadm : AdmBase u.V (maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hB := u.D.tau_bimult
  obtain ⟨f, f₁, f₂, -, -, f₅⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hn.pos

  have hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) := S.prim.pow (pow_pos hn.pos 2) (pow_two _)
  let ω : (PadicAlgCl p)ˣ := Units.map (y₀.comp (algebraMap o S.R)).toMonoidHom (hζ.isUnit hn.ne).unit
  have hωv : (ω : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N))) := rfl
  have hω : IsPrimitiveRoot ω (S.r * S.N) := by
    have : NeZero ((S.r * S.N : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.2 hn.ne⟩
    rw [← IsPrimitiveRoot.coe_units_iff, ← Polynomial.isRoot_cyclotomic_iff,
      ← Polynomial.map_cyclotomic _ (y₀.comp (algebraMap o S.R))]
    exact (hζ.isRoot_cyclotomic hn.pos).map (y₀.comp (algebraMap o S.R))

  let pt : Multiplicative S.Gam →* (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) :=
    MonoidHom.mk' (fun a => g.pt a.toAdd) fun _ _ => g.pt_add _ _
  have pt_nsmul : ∀ (n : ℕ) b, g.pt (n • b) = g.pt b ^ n := fun n b => map_pow pt (Multiplicative.ofAdd b) n
  have onto : ∀ b, ∃ q, f q = g.pt b := fun b => f₂ _ (by
    rw [← pt_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self, zero_smul]
    exact map_one pt)
  obtain ⟨m, hm⟩ := exists_form S l.yy l.yy_onto a ha
  let τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ :=
    (AddChar.zmodChar (S.r * S.N) hω.pow_eq_one).toMonoidHom.comp m.toMultiplicative
  have hτ : ∀ α, τ (Multiplicative.ofAdd α) = ω ^ (m α).val := fun _ => rfl
  have hτ1 : τ ^ (S.r * S.N) = 1 := MonoidHom.ext fun α => by
    show (ω ^ (m α.toAdd).val) ^ (S.r * S.N) = 1
    rw [pow_right_comm, hω.pow_eq_one, one_pow]
  obtain ⟨q, hq, hqτ⟩ := exists_qkPt_tor (F := PadicAlgCl p) hB τ hτ1
  obtain ⟨q₁, hq₁, hq₁τ⟩ := exists_qkPt_tor (F := PadicAlgCl p) (k := S.N) hB (τ ^ S.r) (by rw [← pow_mul, hτ1])
  have hq1 : f q ^ (S.r * S.N) = 1 := by
    obtain ⟨w, hw⟩ := u.U.ext
    exact ((f₁ _ _).2 rfl w hw).1
  obtain ⟨a', ha', -⟩ := g.pt_bij (f q) hq1
  have haa : a' = a := by
    rw [← sub_eq_zero]
    refine eq_zero_of_eStd _ _ _ fun b => ?_
    obtain ⟨q', hq'⟩ := onto b
    have w₁ := (f₅ q q' _).1 (weilQkIs_tor hG q q' hq hqτ)
    rw [← ha', hq'] at w₁
    have w₂ := g.weil a' b (ω ^ (eStd S.g _ a' b).val) (by
      rw [Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, ← pow_mul])
    have e₁ := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG u.A.isAb u.A.isLB w₂ w₁)
    rw [hτ] at e₁
    have e₂ := ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₁)
    rw [hm b _ (l.yy_eq b q' _ ((f₁ _ _).2 hq'.symm) (g.pt_over b))] at e₂
    have e₃ := eStd_add_left S.g _ (a' - a) a b
    rw [sub_add_cancel, e₂] at e₃
    exact left_eq_add.1 (e₃.trans (add_comm _ _))
  subst haa
  refine ⟨q₁, τ ^ S.r, hq₁, hq₁τ, ?_, fun χ => ?_⟩
  · rw [pt_nsmul]
    refine (_root_.GlobalTheory.LevelCompat.qkToAkU_level hL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N S.r (S.r * S.N) (by omega) hr
      (mul_comm _ _) q₁ q _).2 (hq₁.trans hq.symm) ((isNsmul_iff_eq _ _ _).2 ?_) ((f₁ _ _).2 ha')
    rw [(isTorusPtF_iff_eq _ _).1 ((isTor_iff _ _).1 hq₁τ), (isTorusPtF_iff_eq _ _).1 ((isTor_iff _ _).1 hqτ),
      ofMul_pow, map_nsmul]
  · obtain ⟨b, hb⟩ := l.yy_onto (QuotientAddGroup.mk χ)
    have z : S.ζN ^ S.N = 1 := by
      rw [ThetaSys.ζN, ← pow_mul, ← S.prim.pow_eq_one]
      congr 1
      ring
    have z' : S.ζN = (S.ζ ^ (S.r * S.N)) ^ S.r := by
      rw [ThetaSys.ζN, ← pow_mul]
      congr 1
      ring
    rw [l.wt_eq b χ hb, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, ← pow_eq_pow_mod _ z,
      MonoidHom.pow_apply, hτ, hm b χ hb, z', pow_right_comm, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hωv,
      ← map_pow, ← map_pow, ← map_pow, ← map_pow]

end GlobalTheory.ZH.PerpTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FromGtOfMemUnitGrp
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.UnitGrp
open GlobalTheory.TorusExt
attribute [local instance] gtGroup

theorem fromGt_of_mem_unitGrp : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ k : ℕ, Odd k → IsUnit (k : V) → ∀ x ∈ unitGrp v ρ th k, FromGt U.toUnifPre k x := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP k hk hu x hx
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hB := D.tau_bimult
  obtain ⟨f, f₁, -, f₃, f₄, -⟩ := _root_.GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F k hk.pos
  obtain ⟨f', f₁', f₂', -⟩ := _root_.GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F (k ^ 2) (pow_pos hk.pos 2)
  have ua := (_root_.GlobalTheory.UT.ThetaConstVal.main hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ hE hP k hk hu).1
  have add : ∀ p p', f (qkAdd hB p p') = f p * f p' := fun p p' => f₄ _ _ _ (qkAdd_qkAdd hB p p')
  have f0 : f (qkZero hB F k) = 1 := by
    have e := add (qkZero hB F k) (qkZero hB F k)
    rw [show qkAdd hB (qkZero hB F k) (qkZero hB F k) = qkZero hB F k from qk_ext (add_zero _) (add_zero _)] at e
    exact mul_eq_left.1 e.symm
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨x, t, c, hx, hT, hc0, rfl⟩ := hy
    obtain ⟨q, rfl⟩ := f₂' x hx
    have hq := (f₁' q _).2 rfl
    obtain ⟨z, hz⟩ := (ua q _ t c hq hT).2 hc0
    let p : QkPt D.toPre F k := qkMk hB q.y (k • q.g) (by rw [← mul_smul, ← pow_two, qk_nsmul hB])
    have hp := (_root_.GlobalTheory.LevelCompat.qkToAkU_level hL V _ hA D A G hG U F k k (k ^ 2) hk.pos hk.pos (pow_two k) p q (f' q)).2 rfl
      ((isNsmul_iff_eq _ _ _).2 rfl) hq
    refine ⟨qkShift hB p (-z), ?_, (f₁ _ _).2 (((f₁ _ _).1 hp).trans ((f₃ _ _).2 (equiv_qkShift hB p (-z))))⟩
    show q.y + k • (-z) = 0
    rw [hz, smul_neg, add_neg_cancel]
  | one => exact ⟨qkZero hB F k, rfl, (f₁ _ _).2 f0.symm⟩
  | mul a b _ _ ha hb =>
    obtain ⟨p, py, hp⟩ := ha
    obtain ⟨p', py', hp'⟩ := hb
    refine ⟨qkAdd hB p p', ?_, (f₁ _ _).2 ?_⟩
    · show p.y + p'.y = 0
      rw [py, py', add_zero]
    · rw [add, (f₁ _ _).1 hp, (f₁ _ _).1 hp']
  | inv a _ ha =>
    obtain ⟨p, py, hp⟩ := ha
    refine ⟨qkNeg hB p, ?_, (f₁ _ _).2 ?_⟩
    · show -p.y = 0
      rw [py, neg_zero]
    · have e := add (qkNeg hB p) p
      rw [show qkAdd hB (qkNeg hB p) p = qkZero hB F k from qk_ext (neg_add_cancel _) (neg_add_cancel _), f0] at e
      rw [(f₁ _ _).1 hp]
      exact (eq_inv_of_mul_eq_one_left e.symm).symm

end GlobalTheory.OneBasis.UnitGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfThetaUnitInEveryCoset
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.CosetGood

theorem subsingleton_of_forall_hom {X : Type} [AddCommGroup X] [Module.Free ℤ X] {n : ℕ} (hn : n.Prime)
    (h : ∀ (l : X →+ ZMod n) (y : X), l y = 0) : Subsingleton X := by
  haveI : Fact n.Prime := ⟨hn⟩
  let b := Module.Free.chooseBasis ℤ X
  haveI : IsEmpty (Module.Free.ChooseBasisIndex ℤ X) := ⟨fun i => by
    have := h ((Int.castAddHom (ZMod n)).comp (b.coord i).toAddMonoidHom) (b i)
    simp at this⟩
  exact b.repr.toEquiv.subsingleton

theorem subsingleton_of_labels {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [IsAlgClosed C] (N : NumD C) (Q : QuadraticMap ℤ N.X ℝ) (hQ : N.Int Q) {n g j : ℕ} (hn : n.Prime) (ho : Odd n)
    (h1 : ‖(n : C)‖ = 1) (hT : N.Tors n g) (hj : 2 ≤ j) {La : Type} [AddCommGroup La]
    (r : N.QT ((n ^ j) ^ 2) → La → Prop) (tot : ∀ a, ∃ q, r q a) (cot : ∀ q, ∃ a, r q a)
    (mul : ∀ q q' a a', r q a → r q' a' → r (q * q') (a + a')) (inj : ∀ q q' a, r q a → r q' a → N.QEq q q')
    (v : La → C) (hv : ∀ q : La → N.QT ((n ^ j) ^ 2), (∀ a, r (q a) a) → ∃ c : C, ∀ a, v a = c * N.tx (n ^ j) (q a))
    (hle : ∀ a, ‖v a‖ ≤ 1) (hco : ∀ a, ∃ h, ‖v (a + n ^ (j - 1) • h)‖ = 1) : Subsingleton N.X := by
  classical
  obtain ⟨hA, hB, -⟩ := _root_.GlobalTheory.tx_coset_criterion C N Q hQ n g hn ho h1 hT j (by omega)
  obtain ⟨q₀, -, -, hq₀⟩ := hB 1 rfl
  obtain ⟨a₀, ha₀⟩ := cot (1 * q₀)
  have tot' : ∀ a, ∃ q, r q a ∧ (a = a₀ → q = 1 * q₀) := fun a => by
    by_cases e : a = a₀
    · exact ⟨_, e ▸ ha₀, fun _ => rfl⟩
    · obtain ⟨q, hq⟩ := tot a
      exact ⟨q, hq, fun e' => absurd e' e⟩
  choose q hq hq' using tot'
  obtain ⟨c, hc⟩ := hv q hq
  have c1 : ‖c‖ ≤ 1 := by
    have := hle a₀
    rwa [hc, hq' a₀ rfl, norm_mul, hq₀, _root_.mul_one] at this
  have hu : ∀ a, ‖v a‖ = 1 → ‖N.tx (n ^ j) (q a)‖ = 1 := fun a ha => by
    rw [hc, norm_mul] at ha
    have := (hA (q a)).1
    nlinarith [norm_nonneg c, norm_nonneg (N.tx (n ^ j) (q a))]
  refine subsingleton_of_forall_hom hn fun l y => ?_
  have hl : ∀ (i : ℕ) (z : N.X), i ≠ 0 → l (n ^ i • z) = 0 := fun i z hi => by
    rw [map_nsmul, nsmul_eq_mul, Nat.cast_pow, ZMod.natCast_self, zero_pow hi, zero_mul]
  have he : ∀ p p' : N.QT ((n ^ j) ^ 2), N.QEq p p' → l p'.1.1.toAdd = l p.1.1.toAdd := by
    rintro p p' ⟨z, hz, -⟩
    rw [hz, map_add (f := _), show (n ^ j) ^ 2 • z = n ^ (j * 2) • z by rw [pow_mul], hl _ _ (by omega), add_zero]
  let Y : La →+ ZMod n := AddMonoidHom.mk' (fun a => l (q a).1.1.toAdd) fun a a' =>
    (he _ _ (inj _ _ _ (mul _ _ _ _ (hq a) (hq a')) (hq (a + a')))).trans (map_add l _ _)
  have hY : ∀ a, Y a = 0 := fun a => by
    obtain ⟨h, hh⟩ := hco a
    obtain ⟨z, hz⟩ := (hA _).2 (hu _ hh)
    have e : Y (a + n ^ (j - 1) • h) = 0 := (congrArg l hz).trans (hl _ _ (by omega))
    rwa [map_add, map_nsmul, nsmul_eq_mul, Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega), zero_mul,
      add_zero] at e
  have hn0 : (n : C) ≠ 0 := fun e => by rw [e, norm_zero] at h1; exact zero_ne_one h1
  have hs := (_root_.GlobalTheory.Ex.QStr.qStructure C N n g hn0 hT (j * 2)).2.2.1 y
  rw [pow_mul] at hs
  obtain ⟨p, rfl⟩ := hs
  obtain ⟨a, ha⟩ := cot p
  exact (he _ _ (inj _ _ _ (hq a) ha)).trans (hY a)

theorem exists_unitBall (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ S : ValuationSubring C, ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 :=
  ⟨(NormedField.valuation (K := C)).valuationSubring, fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    rfl⟩

theorem subsingleton_lattice (hV : HV) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
    (o : Full D C) (M : Mdl o) {n j : ℕ} (hn : n.Prime) (ho : Odd n) (h1 : ‖(n : C)‖ = 1) (hj : 2 ≤ j) (v : D.La → C)
    (hv : o.Theta (n ^ j) v) (hle : ∀ x, ‖v x‖ ≤ 1) (hco : ∀ x, ∃ h, ‖v (x + n ^ (j - 1) • h)‖ = 1) :
    Subsingleton M.P.D.toPre.X := by
  letI := H.starRing
  have hL : Laws := hV.1.1
  have hL2 : Laws2 := hV.1.2.1
  obtain ⟨hdvr, hcomp, hchar⟩ := (GlobalTheory.LN.cDvr_iff M.W).1 M.cdv
  have hR : AdmBase M.W (IsLocalRing.maximalIdeal M.W) := ⟨inferInstance, inferInstance, inferInstance, hcomp⟩
  have hev := M.P.D.psi_even
  have hbi := M.P.D.tau_bimult
  obtain ⟨S, hS⟩ := exists_unitBall C
  obtain ⟨N, ν, hν⟩ := GlobalTheory.ValuesExist.exists_integral_values hL M.W M.P.D.toPre hev hbi C S
    fun r => (hS _).2 (M.ext.1 r)
  have hI : ν.IntN := ⟨S, hS, hν⟩
  obtain ⟨Q, hQ⟩ := _root_.GlobalTheory.Ex.IntVal.main M.W _ hR M.P.D C M.ext N ν hI
  have hT := _root_.GlobalTheory.ValuesTorsion.tors_of_integral hL hL2 (_root_.GlobalTheory.ThetaInValues.brUth_of_laws hL) M.W M.P.D.toPre hev hbi C
    ⟨M.ext.1, fun r hr => M.ext.2 r (bot_le (a := IsLocalRing.maximalIdeal M.W) hr)⟩ N ν hI n hn ho h1
  obtain ⟨g₁, g₂, g₃, -, g₅⟩ := _root_.GlobalTheory.Ex.GtValues.points_correspond M.W M.P.D.toPre hev hbi C N ν
  have hk : 0 < (n ^ j) ^ 2 := pow_pos (pow_pos hn.pos _) _
  obtain ⟨g₆, g₇, g₈⟩ := g₅ ((n ^ j) ^ 2)
  obtain ⟨f, f₁, f₂, f₃, f₄, -⟩ := _root_.GlobalTheory.TorsionIso.torsion_eq hV.1 M.W _ hR M.P.D M.P.A M.t.G M.t.semi M.P.U C _ hk
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback M.cart (𝟙 (Sp C)) (jFK (R := M.W) C) (Category.id_comp _).symm
  let x : D.La → (TFK (R := M.W) C ⟶ M.P.A.A) := fun a => e (o.I.ev ((n ^ j) ^ 2) a)
  have hp : ∀ a, o.I.ev ((n ^ j) ^ 2) a ^ (n ^ j) ^ 2 = 1 := fun a => (o.I.onto _ hk _).2 ⟨a, rfl⟩
  have hx : ∀ a, x a ^ (n ^ j) ^ 2 = 1 := fun a => (map_pow e _ _).symm.trans ((congrArg e (hp a)).trans (map_one e))
  have hv' : IsThetaPt M.P.A (n ^ j) x fun a => fnOf (v a) := by
    have key : ∀ (s : Sp C ⟶ (TK M.W).left) (_ : s = 𝟙 _ ≫ jFK (R := M.W) C) (y : D.La → (Over.mk s ⟶ M.P.A.A)),
        (∀ a, (y a).left = (o.I.ev ((n ^ j) ^ 2) a).left ≫ M.φ) → IsThetaPt M.P.A (n ^ j) y fun a => fnOf (v a) := by
      rintro s rfl y hy
      exact (ThetaPtUp.isThetaPt_iff (T := baseOver (Sp C)) M.cart M.lb hy hp _).1 hv
    exact key _ (Category.id_comp _).symm x fun a => he _
  have hm : ((n ^ j : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.2 (pow_pos hn.pos _).ne'
  obtain ⟨-, c₂, c₃, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL C _ M.P.A (jFK (R := M.W) C) (n ^ j) ho.pow hm D.La x hx
  haveI := subsingleton_of_labels N Q hQ hn ho h1 hT hj (fun q a => ∃ p, ν.QPt p q ∧ f p = x a) (fun a => ?_)
    (fun q => ?_) ?_ ?_ v (fun q hq => ?_) hle hco
  · exact ν.eX.symm.toEquiv.subsingleton
  · obtain ⟨p, hp⟩ := f₂ _ (hx a)
    obtain ⟨q, hq, -⟩ := g₆ p
    exact ⟨q, p, hq, hp⟩
  · obtain ⟨p, hp⟩ := g₇ q
    obtain ⟨w, hw⟩ := M.P.U.toUnifPre.ext
    have h₀ : f p ^ (n ^ j) ^ 2 = 1 := ((f₁ p (f p)).2 rfl w hw).1
    obtain ⟨a, ha⟩ := (o.I.onto _ hk (e.symm (f p))).1
      ((map_pow e.symm _ _).symm.trans ((congrArg e.symm h₀).trans (map_one e.symm)))
    exact ⟨a, p, hp, ((congrArg e ha).trans (e.apply_symm_apply _)).symm⟩
  · rintro q q' a a' ⟨p, hp, e₁⟩ ⟨p', hp', e₂⟩
    obtain ⟨p'', hp''⟩ := g₇ (q * q')
    refine ⟨p'', hp'', (f₄ p p' p'' ⟨p'', ?_, (g₃ _ _ _ _ _ _ hp.2 hp'.2 hp''.2).2 rfl, qk_equiv_refl hbi _⟩).trans ?_⟩
    · rw [← hp''.1, ← hp.1, ← hp'.1, ← map_add (f := _)]; rfl
    · rw [e₁, e₂]
      exact ((congrArg e (o.I.add _ a a')).trans (map_mul e _ _)).symm
  · rintro q q' a ⟨p, hp, e₁⟩ ⟨p', hp', e₂⟩
    exact (g₈ p p' q q' hp hp').1 ((f₃ p p').1 (e₁.trans e₂.symm))
  · choose p hp hp' using hq
    have ht := _root_.GlobalTheory.Ex.ThetaSeries.theta_const_eq_series hV _root_.GlobalTheory.Ex.GtValues.points_correspond (_root_.GlobalTheory.Ex.brFam hL hL2) M.W _ M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext
      N ν (n ^ j) ho.pow D.La p q x (fun a => (f₁ _ _).2 (hp' a).symm) hp
    obtain ⟨c, hc⟩ := (c₂ 1 _ v ((c₃ _).1 ht)).1 ((c₃ _).1 hv')
    exact ⟨c, fun a => congrFun hc a⟩

theorem isProper_of_unit_in_cosets : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (n j : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → 2 ≤ j → ∀ v, o.Theta (n ^ j) v → (∀ x, ‖v x‖ ≤ 1) → (∀ x, ∃ h, ‖v (x + n ^ (j - 1) • h)‖ = 1) → IsProper M.t.G.hom := by
  intro hV _ _ _ _ _ _ E _ _ _ H D C _ _ _ _ _ o M n j hn ho h1 hj v hv hle hco
  obtain ⟨hdvr, hcomp, hchar⟩ := (GlobalTheory.LN.cDvr_iff M.W).1 M.cdv
  exact (isAbelianScheme_of_unif_of_subsingleton hV.1.1 hV.1.2.1 M.W hcomp M.P.D M.P.A M.t.G M.t.semi M.P.U
    (subsingleton_lattice hV o M hn ho h1 hj v hv hle hco)).proper

end GlobalTheory.CosetGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PelTrivialisationIsUnitOnAbelianLocus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

theorem psiUnitOn_abLocus_pel : Laws → Laws2 → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), P.TorsionIso → IsOpen (abLocus t.G) → ∀ y, PsiUnitOn P.D.toPre y (abLocus t.G) :=
  fun h1 h2 h3 h4 h5 _ _ _ _ _ R _ _ _ I hA t P _ ho y =>
    _root_.GlobalTheory.PsiAbelian.psiUnitOn_abLocus h1 h2 h3 h4 h5 R I hA P.D P.A t.G t.semi P.U ho y

end GlobalTheory
end

