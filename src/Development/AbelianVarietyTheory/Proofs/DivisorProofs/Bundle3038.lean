module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2601
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2499
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2946
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingDiagonalZarhinBundleEqZetaPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleRigidifiedSymmetric

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralCompactificationExistsViaTheta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMinTop

theorem exists_baseRing_away (F : IntermediateField ℚ ℂ) (hF : FiniteDimensional ℚ F) (N : ℤ) (hN : N ≠ 0) :
    ∃ (o : Type) (_ : CommRing o) (b : o →+* F), Function.Injective b ∧ IsDedekindDomain o ∧ Algebra.FiniteType ℤ o ∧
      IsUnit (N : o) ∧ ∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a := by
  haveI : NumberField F := ⟨⟩
  have h3 : (N : 𝓞 F) ≠ 0 := by exact_mod_cast hN
  have hM : Submonoid.powers (N : 𝓞 F) ≤ nonZeroDivisors (𝓞 F) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors h3
  have hg : ∀ y : Submonoid.powers (N : 𝓞 F), IsUnit (algebraMap (𝓞 F) F y) := fun y =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2
      (nonZeroDivisors.ne_zero (hM y.2)))
  let o := Localization.Away (N : 𝓞 F)
  let b : o →+* F := IsLocalization.lift (M := Submonoid.powers (N : 𝓞 F)) hg
  have hb : ∀ a : 𝓞 F, b (algebraMap (𝓞 F) o a) = algebraMap (𝓞 F) F a := fun a =>
    IsLocalization.lift_eq (M := Submonoid.powers (N : 𝓞 F)) hg a
  haveI : IsDomain o := IsLocalization.isDomain_localization hM
  refine ⟨o, inferInstance, b, ?_, IsLocalization.isDedekindDomain (𝓞 F) hM o, ?_, ?_, ?_⟩
  · rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [(IsLocalization.injective o hM).eq_iff, (IsFractionRing.injective (𝓞 F) F).eq_iff]
  · have : Algebra.FiniteType (𝓞 F) o :=
      IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (N : 𝓞 F)) o
    exact @Algebra.FiniteType.trans ℤ (𝓞 F) o _ _ _ _ (Ring.toIntAlgebra o) _ _ inferInstance this
  · simpa only [map_intCast] using IsLocalization.Away.algebraMap_isUnit (S := o) (N : 𝓞 F)
  · intro x
    obtain ⟨⟨a, d⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 F)) x
    refine ⟨algebraMap (𝓞 F) o a, algebraMap (𝓞 F) o d, ?_, ?_⟩
    · rw [hb]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 (nonZeroDivisors.ne_zero d.2)
    · rw [hb, hb]; exact h

theorem integral_normal_model_dense : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n), Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → ∃ (Z : Scheme.{0}) (p : Z ⟶ PSpace o n) (iF : X ⟶ pullback (p ≫ PSpace.str o n) (spMap b)), IsFinite p ∧ Geo.Tor.IsNormalScheme Z ∧ IsOpenImmersion iF ∧ Dense (Set.range iF) ∧ iF ≫ pullback.snd _ _ = s ∧ iF ≫ pullback.fst _ _ ≫ p = f ∧ Dense (Set.range (iF ≫ pullback.fst _ _)) := by
  intro o F _ _ _ _ _ _ b n X s f hb hfr hX hsep hlft hqc hcomm hfin
  haveI : IsProper (PSpace.str o n) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str o n
  haveI : QuasiCompact (f ≫ PSpace.str o n) := by rw [hcomm]; infer_instance
  haveI : QuasiSeparated (f ≫ PSpace.str o n) := by rw [hcomm]; infer_instance
  haveI : QuasiCompact f := QuasiCompact.of_comp f (PSpace.str o n)
  haveI : QuasiSeparated f := QuasiSeparated.of_comp f (PSpace.str o n)
  have hw : f.toNormalization ≫ (f.fromNormalization ≫ PSpace.str o n) = s ≫ spMap b := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hcomm]
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.ThetaFin.isFinite_fromNormalization_and_normal o F b n X s f hb hfr hX hsep hlft hqc hcomm hfin
  obtain ⟨h3, h4⟩ := _root_.GlobalTheory.UMin.isOpenImmersion_dense_genericFibre_normalization o F b n X s f hb hfr hX hsep hlft hqc hcomm hfin
    (pullback.lift _ _ hw) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  refine ⟨f.normalization, f.fromNormalization, pullback.lift _ _ hw, h1, h2, h3, h4,
    pullback.lift_snd _ _ _, ?_, ?_⟩
  · rw [pullback.lift_fst_assoc, Scheme.Hom.toNormalization_fromNormalization]
  · rw [pullback.lift_fst]
    exact f.toNormalization.denseRange

end GlobalTheory.UMinTop

namespace GlobalTheory


set_option maxHeartbeats 1000000 in
theorem umin_theta_compactification_exists : UMinSt := by
  have h_dim := @GlobalTheory.UMin.polFib_univ
  have h_xf := _root_.GlobalTheory.UMin.xF_props
  have h_map_gen := _root_.GlobalTheory.UMin.ThetaMapGen.main
  have h_qf := _root_.GlobalTheory.UMin.QF.finite_fibre_thMap
  have h_zb := GlobalTheory.UMinTop.integral_normal_model_dense
  have h_zb_amp := @GlobalTheory.FiniteOverPSpace.isProjOver_and_isAmpleLB
  have h_zb_lift := GlobalTheory.T.finite_morphism_valuative_lifting_normal_domain
  have h_ext_P := _root_.GlobalTheory.UMin.ExtP.extend_theta
  have h_thint_P := _root_.GlobalTheory.UMin.thetaInt_hasDiv
  have h_om_P := _root_.GlobalTheory.ThetaPullback.theta_pull_O1_pow
  intro E _ _ _ H Dw _ l Xo c
  have hM'0 : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hd0 : H.d ≠ 0 := H.d_prime.ne_zero
  have hD0 : NumberField.discr E ≠ 0 := NumberField.discr_ne_zero E
  obtain ⟨o, _, b, hb, hded, hft, hNu, hfr⟩ := GlobalTheory.UMinTop.exists_baseRing_away c.F c.fin
    (3 * (l.M' : ℤ) * (H.d : ℤ) * NumberField.discr E) (by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) hD0 <;> exact_mod_cast ‹_›)
  have hNu' : IsUnit ((3 : o) * (l.M' : o) * (H.d : o) * ((NumberField.discr E : ℤ) : o)) := by
    simpa [Int.cast_mul] using hNu
  have h3 : IsUnit (3 : o) := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hNu'))
  have hM'u : IsUnit (l.M' : o) := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hNu'))
  have hdu : IsUnit (H.d : o) := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hNu')
  have hDu : IsUnit ((NumberField.discr E : ℤ) : o) := isUnit_of_mul_isUnit_right hNu'
  haveI := hded
  haveI := hft
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 81 ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)).factorial < 3 ^ j * 81 := by
    refine ⟨81 ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)).factorial, ?_⟩
    exact lt_of_lt_of_le (Nat.lt_pow_self (by norm_num : 1 < 3)) (Nat.le_mul_of_pos_right _ (by norm_num))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n + 1 = (3 ^ j * 81) ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) :=
    ⟨_, Nat.succ_pred_eq_of_pos (by positivity)⟩
  have hodd : Odd (3 ^ j * 81) := (Odd.pow (by decide)).mul (by decide)
  have h3m : 3 ≤ 3 ^ j * 81 := le_trans (by norm_num) (Nat.le_mul_of_pos_left 81 (by positivity))
  have hu : IsUnit ((3 ^ j * 81 : ℕ) : o) := by
    have : ((3 ^ j * 81 : ℕ) : o) = 3 ^ (j + 4) := by push_cast; ring
    rw [this]; exact h3.pow _
  obtain ⟨hN, hno, hch, hsep, hlft, hqc⟩ := h_xf E H Dw l Xo c
  obtain ⟨f, hf, hT⟩ := h_map_gen Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB Xo.univ.t.PP.rigGen
    _ _ n o (Xo.XF c) (pullback.snd _ _ ≫ spMap b) (pullback.fst _ _) hodd h3m hu hn hN hno hch
    (fun R _ x => h_dim E H Dw l Xo c R _)
  obtain ⟨Z, p, iF, hp, hZ, hio, hd, hs, hif, hdense⟩ := h_zb o c.F b n (Xo.XF c) (pullback.snd _ _) f hb hfr hN hsep hlft hqc hf
    (h_qf E H Dw l Xo c o j n f hj hn hT)
  have hD : 1 ≤ (n + 1).factorial := Nat.factorial_pos _
  obtain ⟨hpr, hlb, ham, hpull⟩ := h_zb_amp o n (8 * (n + 1).factorial) Z p (by omega) hp
  refine ⟨{ o := o, b := b, inj := hb, frac := ?_, ded := hded, ft := hft, unit_level := hM'u, unit_d := hdu,
            unit_discr := hDu, Z := Z, z := p ≫ PSpace.str o n, proj := hpr, normal := GlobalTheory.IsNormalScheme.of_pred hZ,
            iF := iF, iF_open := hio, iF_dense := hd, iF_over := hs, i_dense := hdense, OZ := _, OZ_lb := hlb, OZ_ample := ham,
            N := 4 * (n + 1).factorial * (n + 1).factorial, N_pos := Nat.mul_pos (by omega) hD,
            omega := ?_, ext := ?_, thetaInt := ?_ }⟩
  · intro x
    obtain ⟨a, d, hbd, e⟩ := hfr x
    exact ⟨a, d, eq_div_of_mul_eq hbd e⟩
  · intro Y g hg hY
    have e₂ := h_om_P E H Dw l Xo c o _ n f hodd h3m hu hn hT Y ((g ≫ pullback.fst _ _) ≫ p)
      (by rw [Category.assoc, reassoc_of% hg, hif]) hY
    exact LBIso.trans (pull_isLB hlb _)
      (isLB_lbPow (pull_isLB (ProjSpace.O1_isLB o n) _) _) (isLB_lbPow hY _) (hpull _ (g ≫ pullback.fst _ _)) e₂
  · intro R _ _ _ hR t ht y hy σ hσ
    obtain ⟨ξ₀, h₁, h₂⟩ := h_ext_P E H Dw l Xo c o _ n f hodd h3m hu hn hT b hf R hR t ht y hy σ hσ
    haveI := hR.1.2.2.1
    obtain ⟨ξ, h₃, h₄⟩ := h_zb_lift R Z _ p ξ₀ (y ≫ iF ≫ pullback.fst _ _) hp (by simp only [Category.assoc, hif, h₁])
    exact ⟨ξ, h₃, by rw [reassoc_of% h₄, h₂]⟩
  · intro o' Ω _ _ _ _ S ρ u hu' _ M π hM hπ
    exact h_thint_P E H Dw l Xo c o _ n f hodd h3m hu hn hT o' Ω S ρ u hu' M (π ≫ p) (@GlobalTheory.IsNormalScheme.pred _ hM)
      (by rw [reassoc_of% hπ]; simp only [Category.assoc, hif])

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUniformisationGenericFibreIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
noncomputable section

namespace GlobalTheory.USepGen

theorem genfib_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (yK : X₁.S.R →+* FractionRing V) (x' : Sp (FractionRing V) ⟶ Sp (ratHull X₁.S.R)), x' ≫ spMap (toRat X₁.S.R) = spMap yK → GenOf Xo c (x' ≫ u) t → ∃ φ : P.A.A.left ⟶ X₁.ρ.P.A.left, IsGrpPullback P.A.A X₁.ρ.P.A (spMap yK) φ ∧ LBIso P.A.L (X₁.ρ.P.L.pull φ) ∧ ∀ a, (letI := H.starRing; (P.oA.act (H.bar a)).left) ≫ φ = φ ≫ (act a).left := by
  intro E _ _ _ H Dw _ l Xo c C X₁ act u π hL V _ _ _ _ t P yK x' hx' hgen
  obtain ⟨-, ⟨G, iG, α, β, hα, hβ, hLab, hf⟩, -, -⟩ := hL
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := hgen
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  have gpA : IsGrpPullback P.A.A t.G (jK V) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V)) :=
    ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK V))).congr
      (Category.id_comp _) rfl
  have w₁ : (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V)) ≫ t.G.hom = (P.A.A.hom ≫ 𝟙 _) ≫ jK V := by
    rw [gpA.1.w, Category.comp_id]
  let κ : P.A.A.left ⟶ tK.G.left := m₁.cart.1.lift _ _ w₁
  have hκ₁ : κ ≫ m₁.φ = P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V) := m₁.cart.1.lift_fst _ _ _
  have hκ₂ : κ ≫ tK.G.hom = P.A.A.hom ≫ 𝟙 _ := m₁.cart.1.lift_snd _ _ _
  have gκ : IsGrpPullback P.A.A tK.G (𝟙 _) κ :=
    m₁.cart.cancel (gpA.congr (Category.id_comp _).symm hκ₁.symm) hκ₂
  have w₂ : m₂.φ ≫ Xo.univ.t.G.hom = (tK.G.hom ≫ x') ≫ u ≫ pullback.fst _ _ := by
    rw [m₂.cart.1.w]; simp only [Category.assoc]
  let lam : tK.G.left ⟶ G.left := hβ.1.lift _ _ w₂
  have hl₁ : lam ≫ β = m₂.φ := hβ.1.lift_fst _ _ _
  have hl₂ : lam ≫ G.hom = tK.G.hom ≫ x' := hβ.1.lift_snd _ _ _
  have gl : IsGrpPullback tK.G G x' lam :=
    hβ.cancel (m₂.cart.congr (Category.assoc _ _ _) hl₁.symm) hl₂
  refine ⟨κ ≫ lam ≫ α, (gκ.comp (gl.comp hα)).congr (by rw [Category.id_comp, hx']) rfl, ?_, ?_⟩
  · have hA := P.A.isLB
    have hT := t.PP.isLB
    have hK := tK.PP.isLB
    have hU := Xo.univ.t.PP.isLB
    have hP := X₁.ρ.P.isLB
    obtain ⟨w, hw⟩ := P.U.ext
    have hc : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id]; rfl
    have e₁ : LBIso (P.A.L.pull (𝟙 _)) (P.U.LG.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V))) :=
      GlobalTheory.GenSpread.lbIso_pull_comp P.U.gen.inv.left hc.symm rfl ⟨w, hw⟩
    rw [P.bundle, ← hκ₁] at e₁
    have e₀ : LBIso P.A.L (P.A.L.pull (𝟙 _)) := GlobalTheory.SiegelPullComp.iso_pull_id hA
    obtain ⟨w₁, hw₁, -⟩ := m₁.lin
    obtain ⟨w₂, hw₂, -⟩ := m₂.lin
    have e₂ : LBIso (tK.PP.L.pull κ) (t.PP.L.pull (κ ≫ m₁.φ)) :=
      GlobalTheory.GenSpread.lbIso_pull_of_lbIso ⟨w₁, hw₁⟩ κ rfl
    have e₃ : LBIso (tK.PP.L.pull κ) (Xo.univ.t.PP.L.pull (κ ≫ m₂.φ)) :=
      GlobalTheory.GenSpread.lbIso_pull_of_lbIso ⟨w₂, hw₂⟩ κ rfl
    have e₄ : LBIso (X₁.ρ.P.L.pull (κ ≫ lam ≫ α)) (Xo.univ.t.PP.L.pull (κ ≫ m₂.φ)) :=
      GlobalTheory.GenSpread.lbIso_pull_comp (κ ≫ lam) (Category.assoc _ _ _).symm
        (by rw [← hl₁, Category.assoc]) hLab
    refine LBIso.trans hA (pull_isLB hA _) (pull_isLB hP _) e₀ ?_
    refine LBIso.trans (pull_isLB hA _) (pull_isLB hT _) (pull_isLB hP _) e₁ ?_
    refine LBIso.trans (pull_isLB hT _) (pull_isLB hK _) (pull_isLB hP _) e₂.symm ?_
    refine LBIso.trans (pull_isLB hK _) (pull_isLB hU _) (pull_isLB hP _) e₃ ?_
    exact e₄.symm
  · intro a
    obtain ⟨f, hfα, hfβ⟩ := hf a
    letI := H.starRing
    have hext := P.lin.ext (H.bar a)
    have hg : (P.oA.act (H.bar a)).left ≫ P.U.gen.inv.left =
        P.U.gen.inv.left ≫ ((Over.pullback (jK V)).map (t.act.act (H.bar a))).left := by
      have : P.oA.act (H.bar a) ≫ P.U.gen.inv =
          P.U.gen.inv ≫ (Over.pullback (jK V)).map (t.act.act (H.bar a)) := by
        rw [Iso.eq_inv_comp, ← Category.assoc, ← hext, Category.assoc, Iso.hom_inv_id, Category.comp_id]; rfl
      rw [← Over.comp_left, this, Over.comp_left]
    have s₁ : (P.oA.act (H.bar a)).left ≫ κ = κ ≫ (tK.act.act (H.bar a)).left := by
      apply m₁.cart.1.hom_ext
      · rw [Category.assoc, hκ₁, Category.assoc, m₁.act, ← Category.assoc κ, hκ₁, ← Category.assoc, hg,
          Category.assoc, Category.assoc]
        congr 1
        exact pullback.lift_fst _ _ _
      · rw [Category.assoc, hκ₂, Category.assoc, Over.w, hκ₂, ← Category.assoc, Over.w]
    have s₂ : (tK.act.act (H.bar a)).left ≫ lam = lam ≫ f.left := by
      apply hβ.1.hom_ext
      · simp only [Category.assoc, hfβ]
        rw [hl₁, ← Category.assoc lam β, hl₁]
        exact m₂.act _
      · rw [Category.assoc, hl₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hl₂]
    rw [← Category.assoc, s₁, Category.assoc, ← Category.assoc _ lam, s₂, Category.assoc, hfα]
    simp only [Category.assoc]

end GlobalTheory.USepGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValGaloisConjugateExtensionEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep
open GlobalTheory.Points GlobalTheory.ZH GlobalTheory.Poinc.Sep.GalVal

theorem val_galois_conj : ∀ {I : Type} {X₁ : GlobalTheory.GSep.GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : GlobalTheory.GSep.Tower X₁ act) {z₂ : 𝔗.X₂.M.Z} {V' : Type} [CommRing V'] [IsDomain V'] (ev₂ ev₂' : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → GlobalTheory.GSep.RegAt 𝔗.X₂ z₂ ev₂ → GlobalTheory.GSep.RegAt 𝔗.X₂ z₂ ev₂' → ∀ a : 𝔗.X₂.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) a = 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.sR σ a) := by

  intro I X₁ act 𝔗 z₂ V' _ _ ev₂ ev₂' σ h1 h2 hr hr' a
  have ha := hr' a a.2
  obtain ⟨x, d, hxd, hd, hu⟩ := exists_mul_eq_stalkHom (specializes_jK ev₂' _) ha
  obtain ⟨x', hx'⟩ := h2 x
  obtain ⟨d', hd'⟩ := h2 d
  have ex := h1 x x' hx'
  have ed := h1 d d' hd'
  have hsp' := RatModel.specializes_of_range_eq
    (RatModel.range_eq_singleton (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (IsLocalRing.closedPoint _))
  have hsp := RatModel.specializes_of_range_eq
    (RatModel.range_eq_singleton (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (IsLocalRing.closedPoint _))
  have e1 := RatModel.val_mul hsp' ha hd
  rw [hxd, val_stalkHom, val_stalkHom] at e1
  have hne := (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton _ _) ⟨_, hd⟩).2 hu
  rw [val_stalkHom] at hne
  have hb := hr _ (𝔗.sR σ a).2
  have hd'' := RatModel.O_le_of_specializes (specializes_jK ev₂ (IsLocalRing.closedPoint _))
    (𝔗.X₂.M.stalkEquiv z₂ d').2
  have e2 := RatModel.val_mul hsp hb hd''
  have key : σ (a : 𝔗.X₂.Ω₁) * 𝔗.X₂.M.stalkHom z₂ d' = 𝔗.X₂.M.stalkHom z₂ x' := by
    rw [hd', hx', ← map_mul, hxd]
  rw [RatModel.coe_stalkEquiv, 𝔗.sR_eq, key, val_stalkHom, val_stalkHom, ← ed, ← ex] at e2
  rw [𝔗.sR_eq]
  exact mul_right_cancel₀ hne (e1.symm.trans e2)

end GlobalTheory.GSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalSymbolZeroOfBracketPreserving
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

def GlobalTheory.HeatSym.derOfFun {F : Type} [Field F] (d : F → F) (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = x * d y + y * d x) : Derivation ℤ F F :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' d hadd)) fun x y => by
    simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.mk'_apply, smul_eq_mul]
    exact hmul x y

theorem GlobalTheory.HeatSym.derOfFun_apply {F : Type} [Field F] (d : F → F) (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = x * d y + y * d x) (x : F) : GlobalTheory.HeatSym.derOfFun d hadd hmul x = d x := rfl

theorem GlobalTheory.HeatSym.vertical_symbol_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (δ₀ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Λ : Matrix (Fin n) (Fin n) (FractionRing Ω)), Λᵀ = Λ → (∀ r, δ₀ ((algebraMap Ω (FractionRing Ω)) (φ r)) = 0) → (∀ (k : ℕ), 1 ≤ k → ∀ b c : FractionRing Ω, GlobalTheory.HeatSym.VS φ t.PP.L x' g k b → GlobalTheory.HeatSym.VS φ t.PP.L x' g k c → GlobalTheory.HeatSym.VS φ t.PP.L x' g (3 * k) ((k : FractionRing Ω) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b))) → Λ = 0 := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hloc n v' D Ω _ _ _ φ x' δ dd' hcomp hx' hinv hδ hval
    hsep g hg δL hδL δ₀ Λ hΛ hδ₀ hbr

  obtain ⟨ψ, ξ, hψ, hξ, hξ', hξsep⟩ := _root_.GlobalTheory.UnifGenPoint.main E H R t P m tt gam hmon htt hloc n v' D Ω φ x' δ dd'
    hcomp hx' hinv hδ hval hsep g hg δL hδL
  obtain ⟨v, dd, hinv₂, hval₂⟩ := _root_.GlobalTheory.GenFields.main E H R t P m tt gam hmon htt hloc n v' D Ω φ x' δ dd'
    hcomp hx' hinv hδ hval hsep g hg δL hδL ψ ξ hψ hξ hξ' hξsep
  obtain ⟨j₀, q, hj₀, hq, hVS⟩ := _root_.GlobalTheory.HeatSym.vs_iff_generic E H R t P m tt gam hmon htt hloc n v' D Ω φ x' δ dd'
    hcomp hx' hinv hδ hval hsep g hg δL hδL ψ ξ hψ hξ hξ' hξsep

  have hker : ∀ D' : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      (∀ r, D' (algebraMap Ω (FractionRing Ω) (φ r)) = 0) → ∀ s, D' (ψ s) = 0 := by
    intro D' hD' s
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective R s
    rw [map_div₀, hψ, hψ, Derivation.leibniz_div, hD', hD']
    simp
  have hδL₀ : ∀ a r, δL a (algebraMap Ω (FractionRing Ω) (φ r)) = 0 := by
    intro a r
    rw [hδL, hδ, map_zero]

  have hadd : ∀ x y : FractionRing Ω,
      (δ₀ (x + y) - ∑ a, ∑ e, Λ a e * δL a q / q * δL e (x + y)) =
        (δ₀ x - ∑ a, ∑ e, Λ a e * δL a q / q * δL e x) + (δ₀ y - ∑ a, ∑ e, Λ a e * δL a q / q * δL e y) := by
    intro x y
    have : ∑ a, ∑ e, Λ a e * δL a q / q * δL e (x + y) =
        ∑ a, ∑ e, Λ a e * δL a q / q * δL e x + ∑ a, ∑ e, Λ a e * δL a q / q * δL e y := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_add (f := _), mul_add]
    rw [map_add (f := _), this]
    ring
  have hmul : ∀ x y : FractionRing Ω,
      (δ₀ (x * y) - ∑ a, ∑ e, Λ a e * δL a q / q * δL e (x * y)) =
        x * (δ₀ y - ∑ a, ∑ e, Λ a e * δL a q / q * δL e y) + y * (δ₀ x - ∑ a, ∑ e, Λ a e * δL a q / q * δL e x) := by
    intro x y
    have : ∑ a, ∑ e, Λ a e * δL a q / q * δL e (x * y) =
        x * ∑ a, ∑ e, Λ a e * δL a q / q * δL e y + y * ∑ a, ∑ e, Λ a e * δL a q / q * δL e x := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, this]
    ring
  let δ₁ := GlobalTheory.HeatSym.derOfFun (fun x => δ₀ x - ∑ a, ∑ e, Λ a e * δL a q / q * δL e x) hadd hmul
  have hδ₁ : ∀ x, δ₁ x = δ₀ x - ∑ a, ∑ e, Λ a e * δL a q / q * δL e x := fun x =>
    GlobalTheory.HeatSym.derOfFun_apply _ hadd hmul x
  have hδ₁ψ : ∀ r, δ₁ (ψ r) = 0 := by
    intro r
    rw [hδ₁, hker δ₀ hδ₀ r]
    simp [hker (δL _) (hδL₀ _) r]
  have : CharZero R := algebraRat.charZero R
  have : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))

  let δL' := fun a : Fin n =>
    GlobalTheory.HeatSym.derOfFun (δL a) (fun x y => map_add _ x y)
      (fun x y => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul])
  have hδL' : ∀ a x, δL' a x = δL a x := fun a x => GlobalTheory.HeatSym.derOfFun_apply _ _ _ x
  have hval₃ : ∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δL' a (valR ξ O f) := by
    intro a O f h
    rw [hδL']
    exact hval₂ a O f h

  refine _root_.GlobalTheory.Heat.gc_symbol_vanishes (FractionRing R) P.A n v dd hinv₂ (FractionRing Ω) ψ ξ hξ hξsep δL' hval₃ j₀ hj₀ δ₁ Λ hΛ
    hδ₁ψ ?_
  intro k hk σ τ
  have hb := (hVS k _ hk).2 ⟨σ, rfl⟩
  have hc := (hVS k _ hk).2 ⟨τ, rfl⟩
  have h3 := hbr k hk _ _ hb hc
  rw [_root_.GlobalTheory.Heat.bracket_symbol_rescale_twist Ω n δ₀ δL Λ q _ _ k hq] at h3
  obtain ⟨ρ, hρ⟩ := (hVS (3 * k) _ (by omega)).1 h3
  refine ⟨ρ, ?_⟩
  rintro b c rfl rfl
  simp only [hδ₁, hδL']
  exact mul_left_cancel₀ (pow_ne_zero _ hq) hρ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingDiagonalZarhinBundleEqZetaPowStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_diagonal_zarhinBundle_eq_zeta_pow : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : cycAway M →+* k) (z : kˣ), x ≫ t = spMap β → (z : k) = β (zetaAway M) → ∀ a b : Fin 8 → (Fin h ⊕ Fin h → ℤ), Out.WeilIs (GlobalTheory.ZarhinFam.Zob c.A B) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left) M (GlobalTheory.ZarhinFam.mkZ c.A B (fun i => toUnit (Over.mk x) ≫ c.lev (a (Fin.castAdd 4 i))) (fun j => toUnit (Over.mk x) ≫ c.lev (a (Fin.natAdd 4 j)) ≫ la)) (GlobalTheory.ZarhinFam.mkZ c.A B (fun i => toUnit (Over.mk x) ≫ c.lev (b (Fin.castAdd 4 i))) (fun j => toUnit (Over.mk x) ≫ c.lev (b (Fin.natAdd 4 j)) ≫ la)) (unitOn (z ^ (2 * GlobalTheory.ZarhinFam.formZ d h a b))) := by
  first | (exact @GlobalTheory.ZarhinWeil.weilIs_formZ) | (exact GlobalTheory.ZarhinWeil.weilIs_formZ) | (intros; apply GlobalTheory.ZarhinWeil.weilIs_formZ  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.YKThNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep

theorem GMem.yK_th_ne_zero : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 x₀ hd h0
  obtain ⟨c, -, h⟩ := GlobalTheory.ZH.GoodOut.exists_th_notMem GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 X₁.ρ
    ⟨RingHom.ker 𝔪.yK, RingHom.ker_isPrime 𝔪.yK⟩ 0
  refine h (RingHom.mem_ker.2 ?_)
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd' := hd.of_specializes
    (ξ := (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) (sp _)
  have hs : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have e := RatModel.val_mul hs (hd'.2 (0 + c)) (𝔪.reg _ (X₁.S.th_mem x₀))
  rw [div_mul_cancel₀ _ hd.1] at e
  rw [𝔪.yK_eq] at h0 ⊢
  exact e.trans ((congrArg (_ * ·) h0).trans (mul_zero _))

end GlobalTheory.GSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleRigidifiedSymmetricStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinBundle_rigidified_symmetric : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (1 : (GlobalTheory.ZarhinFam.Zob c.A B) ⟶ (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (1 : (GlobalTheory.ZarhinFam.Zob c.A B) ⟶ (GlobalTheory.ZarhinFam.Zob c.A B))).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.Zob c.A B)) (fst (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.Zob c.A B))).left) := by
  first | (exact @GlobalTheory.ZarhinFam.Rig.zarhinBundle_rigidified_symmetric₂) | (exact GlobalTheory.ZarhinFam.Rig.zarhinBundle_rigidified_symmetric₂) | (intros; apply GlobalTheory.ZarhinFam.Rig.zarhinBundle_rigidified_symmetric₂  <;> assumption)
end

