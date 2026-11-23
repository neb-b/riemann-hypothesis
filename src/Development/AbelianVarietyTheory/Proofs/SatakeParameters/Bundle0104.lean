module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0091
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0012
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SubstitutionOfVariables
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatDual

theorem lamHat_eq_hat {D : D7} (V : HSp D) :
    LamHat V = GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
  have : (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext v
    rw [SetLike.mem_coe, GlobalTheory.Member.mem_latC, Module.Basis.equivFun_symm_apply]
    rfl
  rw [this]
  rfl

theorem integralTensorAdeles_eq_adelicCompletion_one (D : D7) :
    intAE D = GlobalTheory.AdLat.hat1 D.host.F
      ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) := by
  unfold intAE GlobalTheory.AdLat.hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, (FractionalIdeal.mem_one_iff _).2 ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
    exact ⟨a, ha, x, rfl⟩

theorem hR_eq_hermA {D : D7} (V : HSp D)
    (z y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    hR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram z y =
      GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y z := by
  unfold hR Formalism.UG.hform GlobalTheory.AdLat.hermA
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm, mul_comm (sigR _ _ _), ← mul_assoc]
  rfl

theorem smul_mem_lamHat {D : D7} (V : HSp D) :
    ∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V := by
  intro a ha y hy
  rw [lamHat_eq_hat] at hy ⊢
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨s, hs, o, rfl⟩ := ha
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨s * t, fun v => mul_mem (hs v) (ht v), o • x,
        (GlobalTheory.Member.latC V).smul_mem o hx, ?_⟩
      funext i
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    | zero =>
      simp only [Pi.zero_apply, mul_zero]
      exact zero_mem _
    | add u w _ _ hu hw =>
      simp only [Pi.add_apply, mul_add]
      exact add_mem hu hw
    | neg u _ hu =>
      simp only [Pi.neg_apply, mul_neg]
      exact neg_mem hu
  | zero =>
    simp only [zero_mul]
    exact zero_mem _
  | add u w _ _ hu hw =>
    simp only [add_mul]
    exact add_mem hu hw
  | neg u _ hu =>
    simp only [neg_mul]
    exact neg_mem hu

theorem lamHat_selfDual_and_module : ∀ {D : D7} (V : HSp D), (∀ y, y ∈ LamHat V ↔ ∀ z ∈ LamHat V, hR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram z y ∈ intAE D) ∧ (∀ a ∈ intAE D, ∀ y ∈ LamHat V, (fun i => a * y i) ∈ LamHat V) := by
  intro D V
  refine ⟨fun y => ?_, smul_mem_lamHat V⟩
  obtain ⟨-, -, hfg, hspan, hcc, -, -, hG, hdet, -, hL⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := GlobalTheory.AdLat.hat_selfDual D.host.F D.host.E V.rank (GlobalTheory.Member.latC V) (GlobalTheory.Member.cF D)
    V.gram.transpose 1 hfg hspan hcc hG hdet one_ne_zero hL
  rw [← integralTensorAdeles_eq_adelicCompletion_one, ← lamHat_eq_hat] at key
  simp only [hR_eq_hermA]
  constructor
  · intro hy z hz
    rw [lamHat_eq_hat] at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hz
      have h1 : (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) ∈ intAE D :=
        AddSubgroup.subset_closure ⟨t, ht, 1, rfl⟩
      have h2 := (key _).2 (smul_mem_lamHat V _ h1 y hy) x hx
      convert h2 using 1
      unfold GlobalTheory.AdLat.hermA
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have e : GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (t ⊗ₜ[D.host.F] x b) =
          (t ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E)) *
            GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (GlobalTheory.AdLat.fv D.host.F x b) := by
        simp [GlobalTheory.AdLat.sg, GlobalTheory.AdLat.fv]
      rw [e]
      ring
    | zero =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y 0 = 0 := by simp [GlobalTheory.AdLat.hermA]
      rw [this]; exact zero_mem _
    | add u w _ _ hu hw =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (u + w) =
          GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u +
            GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y w := by
        simp only [GlobalTheory.AdLat.hermA, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
      rw [this]; exact add_mem hu hw
    | neg u _ hu =>
      have : GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y (-u) =
          -GlobalTheory.AdLat.hermA (GlobalTheory.Member.cF D) V.gram.transpose y u := by
        simp only [GlobalTheory.AdLat.hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]
      rw [this]; exact neg_mem hu
  · intro h
    refine (key y).1 fun x hx => h _ ?_
    rw [lamHat_eq_hat]
    exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩

end GlobalTheory.LatDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.TameIwahori

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsIwVec {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (θ : Fin n → kˣ →* ℂˣ)
    (π : Representation ℂ (GL (Fin n) k) V) (v : V) : Prop :=
  (∀ h ∈ KO k (Fin n), (∀ i j, j < i → valuation k (h.val i j) < 1) →
    (∀ i, valuation k (h.val i i - 1) < 1) → π h v = v) ∧
  ∀ t ∈ torusO k (Fin n), π (diagT k (Fin n) t) v = (GlobalTheory.SmGL.torusChar θ t : ℂ) • v

end GlobalTheory.TameIwahori
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPullbackFromSpecAppPreimage
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh

set_option autoImplicit false

namespace GlobalTheory.HodgeCoh
open GlobalTheory.CechDR

theorem isPullback_fromSpec_app_preimage {X Y : Scheme.{0}} (π : X ⟶ Y) {W : Y.Opens}
    (hW : IsAffineOpen W) (hV : IsAffineOpen (π ⁻¹ᵁ W)) :
    IsPullback hV.fromSpec (Spec.map (π.app W)) π hW.fromSpec := by
  refine (IsOpenImmersion.isPullback (Spec.map (π.app W)) hV.fromSpec hW.fromSpec π ?_ ?_).flip
  · rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec π hW hV le_rfl]
  · rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec]

end GlobalTheory.HodgeCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst

theorem StLat.not_frac (l : ℕ) [Fact l.Prime] (Co : Core l) (ϖ : Per.Fl l)
    (hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l)) (u : Per.BdRp l) (hu : IsLogP (beta ϖ) u) (x y : Per.Bcris l)
    (hx : Co.ι x ≠ 0) : Co.ι y ≠ Co.ι x * algebraMap (Per.BdRp l) (Per.BdR l) u := by
  intro h
  obtain ⟨hdom, hdvr, hmax, hmaxθ, -, hfilt, hfr⟩ := BdRDVR.core_dvr l Co
  have hker := _root_.GlobalTheory.Pst.StLat.ker_localizedTheta_eq_span_beta l ϖ hϖ
  have hfil := _root_.GlobalTheory.Pst.StLat.filtration_eq_span_pow l Co ϖ hker
  have hinjD : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := IsFractionRing.injective _ _
  have hβ0 : betaD ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field (Per.BdRp l)
    rw [hmax, ← pow_one (Co.j Co.t), ← hfilt 1, hfil 1, h0, pow_one, Ideal.span_singleton_eq_bot]
  have hsep : ∀ z : Per.BdRp l, (∀ n : ℕ, betaD ϖ ^ n ∣ z) → z = 0 := by
    intro z hz
    have hne : Ideal.span {betaD ϖ} ≠ ⊤ := by
      rw [← pow_one (betaD ϖ), ← hfil 1, hfilt 1, pow_one, ← hmax]
      exact (IsLocalRing.maximalIdeal.isMaximal (Per.BdRp l)).ne_top
    have h1 : z ∈ ⨅ n : ℕ, Ideal.span {betaD ϖ} ^ n := by
      refine (Submodule.mem_iInf _).2 fun n => ?_
      rw [Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton.2 (hz n)
    rwa [Ideal.iInf_pow_eq_bot_of_isDomain _ hne, Ideal.mem_bot] at h1
  obtain ⟨r, ax, hax⟩ := bcris_eq_acris_localization_periodT_alt l Co x
  obtain ⟨r', ay, hay⟩ := bcris_eq_acris_localization_periodT_alt l Co y
  set tt := algebraMap (Per.Acris l) (Per.Bcris l) Co.t with htt
  have e1 : algebraMap (Per.Acris l) (Per.Bcris l) (ax * Co.t ^ r') = x * tt ^ (r + r') := by
    rw [map_mul, map_pow, ← hax, pow_add]; ring
  have e2 : algebraMap (Per.Acris l) (Per.Bcris l) (ay * Co.t ^ r) = y * tt ^ (r + r') := by
    rw [map_mul, map_pow, ← hay, pow_add]; ring
  have e3 : Co.j (ay * Co.t ^ r) = Co.j (ax * Co.t ^ r') * u := by
    apply hinjD
    rw [map_mul (algebraMap (Per.BdRp l) (Per.BdR l)), ← Co.ι_j, ← Co.ι_j, e1, e2, map_mul Co.ι, map_mul Co.ι, h]
    ring
  have hA := _root_.GlobalTheory.Pst.StLat.acris_mem_clos l Co.j Co.j_cris ϖ (_root_.GlobalTheory.Pst.StLat.acris0_le_sa l ϖ hϖ) hfil
  have hz := GlobalTheory.T.eq_zero_of_mem_clos_of_pow_mul_mul_mem_clos l (Fact.out : l.Prime) (isUnit_l_BdRp l) (betaD ϖ) hβ0 hsep (Sg ϖ)
    (_root_.GlobalTheory.Pst.StLat.BetaDiv.Sg_div_betaD_pow l ϖ hϖ hker hfil) (_root_.GlobalTheory.Pst.StLat.betaD_dvd_of_res l ϖ hker hfil) u
    (_root_.GlobalTheory.Pst.StLat.log_trunc_pow l ϖ hker hfil u hu) (Co.j (ax * Co.t ^ r')) 0 (hA _) (by
      rw [pow_zero, one_mul, ← e3]; exact hA _)
  have hz2 : Co.ι (x * tt ^ (r + r')) = 0 := by
    rw [← e1, Co.ι_j, hz, map_zero]
  have htne : Co.ι tt ≠ 0 := by
    rw [htt, Co.ι_j]
    intro h0
    have h3 : Co.j Co.t = 0 := hinjD (h0.trans (map_zero _).symm)
    apply IsDiscreteValuationRing.not_a_field (Per.BdRp l)
    rw [hmax, h3, Ideal.span_singleton_eq_bot]
  haveI : IsDomain (Per.BdR l) := IsFractionRing.isDomain (Per.BdRp l)
  rw [map_mul, map_pow] at hz2
  exact mul_ne_zero hx (pow_ne_zero _ htne) hz2

theorem StLat.kummer_not_frac : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (b b' : P.R.B), b ≠ 0 →
  ¬ ∀ g ∈ GK K, b * P.actQ g b' - P.actQ g b * b' = b * P.actQ g b * ((kummer P g : ℚ_[l]) • P.tB) := by
  intro l _ P AI T K b b' hb h
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T (botExt l)
  obtain ⟨x, y, hx, hxy⟩ := _root_.GlobalTheory.Pst.NoLog.exists_full_frac l P K b b' hb h
  obtain ⟨Co, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨ϖ, hr⟩ := exists_tilt (lRoot l) (lRoot_succ l) l (lRoot_zero l)
  have hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l) := Subtype.ext (by
    have := hr 0
    rw [lRoot_zero, map_natCast] at this
    exact this.trans (SubringClass.coe_natCast _ _).symm)
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.Pst.LogExist.exists_isLogP l (beta ϖ) (by
    rw [_root_.GlobalTheory.Pst.StLat.ker_localizedTheta_eq_span_beta l ϖ hϖ]; exact Ideal.mem_span_singleton_self _)
  have hg := _root_.GlobalTheory.Pst.StLat.gal_log l P Co hC.ζ ϖ hr hϖ u hu
  letI : Field P.R.BdR := (GlobalTheory.RegularRing.isField_of_tied T).toField
  set U := T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) u) with hUdef
  have hct : ∀ g : GQ l, T.eD (P.ιB ((kummer P g : ℚ_[l]) • P.tB)) =
      algebraMap (Per.BdRp l) (Per.BdR l)
        (Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t)) := by
    intro g
    rw [hC.ι, Algebra.smul_def, map_mul, T.zB, hC.t, ← Co.ι_j]
    simp only [Core.tB, GlobalTheory.RingIface.zB_alg, map_mul]
  have hU : ∀ g : GQ l, P.actQdR g U = U + P.ιB ((kummer P g : ℚ_[l]) • P.tB) := by
    intro g
    apply T.eD.injective
    rw [T.actD, hUdef, RingEquiv.apply_symm_apply, map_add (f := _), RingEquiv.apply_symm_apply, hct]
    rw [show Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) u) =
      algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g u) from
        GlobalTheory.RingIface.sigD_alg l g u, hg, map_add]
  have hcomm : ∀ (g : GQ l) (z : P.R.B), P.ιB (P.actQ g z) = P.actQdR g (P.ιB z) := by
    intro g z
    have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ z
    rwa [P.PD_ι, P.PD_actB, P.PD_ι, P.PD_actdR] at this
  have hX : P.ιB x ≠ 0 := fun h0 => hx ((P.PD (botExt l)).ι_inj (by rw [P.PD_ι, h0, map_zero]))
  have hgX : ∀ g : GQ l, P.actQdR g (P.ιB x) ≠ 0 := fun g h0 =>
    hX ((P.actQdR g).injective (h0.trans (map_zero _).symm))
  have hW : ∀ g : GQ l, P.actQdR g (P.ιB y * (P.ιB x)⁻¹ - U) = P.ιB y * (P.ιB x)⁻¹ - U := by
    intro g
    have h1 := congrArg P.ιB (hxy g)
    simp only [map_sub, map_mul, hcomm] at h1
    rw [map_sub, map_mul, map_inv₀, hU]
    have hx1 := mul_inv_cancel₀ hX
    have hx2 := mul_inv_cancel₀ (hgX g)
    linear_combination ((P.ιB x)⁻¹ * (P.actQdR g (P.ιB x))⁻¹) * h1
      - (P.actQdR g (P.ιB y) * (P.actQdR g (P.ιB x))⁻¹) * hx1 + (P.ιB y * (P.ιB x)⁻¹) * hx2
      + (P.ιB ((kummer P g : ℚ_[l]) • P.tB) * P.actQdR g (P.ιB x) * (P.actQdR g (P.ιB x))⁻¹) * hx1
      + P.ιB ((kummer P g : ℚ_[l]) • P.tB) * hx2
  obtain ⟨c, hc⟩ := (P.PD (botExt l)).invdR (P.ιB y * (P.ιB x)⁻¹ - U) fun g => by
    rw [P.PD_actdR]; exact hW g
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 c.2
  have hca : algebraMap ↥(botExt l).1 P.R.BdR c = algebraMap ℚ_[l] P.R.BdR a := by
    have e : c = algebraMap ℚ_[l] ↥(botExt l).1 a := Subtype.ext ha.symm
    rw [e, ← IsScalarTower.algebraMap_apply]
  rw [hca] at hc
  have hY : P.ιB (y - a • x) = P.ιB x * U := by
    rw [map_sub, map_smul, Algebra.smul_def]
    have hx1 := mul_inv_cancel₀ hX
    linear_combination (-P.ιB x) * hc - P.ιB y * hx1
  apply StLat.not_frac l Co ϖ hϖ u hu (T.eB x) (T.eB (y - a • x))
  · rw [← hC.ι]
    exact fun h0 => hX (T.eD.injective (h0.trans (map_zero _).symm))
  · rw [← hC.ι, ← hC.ι, hY, map_mul, hUdef, RingEquiv.apply_symm_apply]

theorem stRegular : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    IsDomain (Bst P) ∧
    (∀ (K : FinExt l) (b b' : Bst P), b ≠ 0 →
      (∀ g : ↥(GK K), b * actSt P (g : GQ l) b' = actSt P (g : GQ l) b * b') →
      ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b) ∧
    (∀ (K : FinExt l) (b : Bst P), b ≠ 0 →
      (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) b = algebraMap ℚ_[l] (Bst P) x * b) → IsUnit b) := by
  intro l _ P AI ⟨T⟩
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T (botExt l)
  obtain ⟨Co, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have hinj : Co.TensorInj := GlobalTheory.Published.FontaineBcris_holds.tensorInj Co
  have hreg : Co.Regular := GlobalTheory.Published.FontaineBcris_holds.regular Co
  refine ⟨inferInstance, fun K b b' hb h => ?_, fun K b hb h => ?_⟩
  · haveI : CharZero P.R.B := by
      have := (algebraMap ℚ_[l] P.R.B).injective
      exact charZero_of_injective_algebraMap this
    have hA : ∀ (g : GQ l) (p : Bst P), actSt P g p = (p.map ((P.actQ g).toRingEquiv : P.R.B →+* P.R.B)).comp (X + C ((kummer P g : ℚ_[l]) • P.tB)) :=
      fun g p => stHom_apply P (P.actQ g) _ p
    obtain ⟨d, d', hd, e, hf⟩ := GlobalTheory.T.twistedShift_fixed_ratio_const_domain (fun g : ↥(GK K) => (P.actQ (g : GQ l)).toRingEquiv)
      (fun g => (kummer P (g : GQ l) : ℚ_[l]) • P.tB)
      (fun d d' hd hh => StLat.kummer_not_frac l P AI T K d d' hd fun g hg => hh ⟨g, hg⟩) b' b hb (fun g => by
        rw [← hA, ← hA]; exact h g)
    obtain ⟨c, hc⟩ := GlobalTheory.RegularRing.fracInv hC hinj K d d' hd fun g => by
      rw [P.PD_actB, P.PD_actB]; exact hf g
    refine ⟨⟨c, c.2.2⟩, c.2.1, ?_⟩
    have hd' : (C d : Bst P) ≠ 0 := C_ne_zero.2 hd
    apply mul_left_cancel₀ hd'
    have hK0 : algebraMap ↥(K0 K) P.R.B c = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨c, c.2.2⟩ := rfl
    rw [e, hc, Polynomial.algebraMap_apply, C_mul, hK0]
    ring
  · have hK : ∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB :=
      GlobalTheory.Pst.NoLog.kummer_not_coboundary l P AI T K
    exact _root_.GlobalTheory.Pst.StLine.isUnit_of_stable_line l P K hK (GlobalTheory.RegularRing.lineUnit hC hreg K) b hb h

end GlobalTheory.Pst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Lev.IsBaseFrame V β Λ N → (∀ k ∈ Formalism.IndefR.Lev.levG V β L, ∃ n : ℕ, 0 < n ∧ Formalism.IndefR.Lev.levChi V β L k ^ n = 1) ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → (∀ g, SuppF V f g → (g ∈ Formalism.IndefR.Lev.levG V β L ↔ g ∈ KsphC V ∅)) ∧ (∀ g ∈ Formalism.IndefR.Lev.levG V β L, SuppF V f g → Formalism.IndefR.Lev.levChi V β L g = 1) ∧ ∀ k ∈ Formalism.IndefR.Lev.levG V β L, ∃ k₁ ∈ Formalism.IndefR.Lev.levG V β L, ∃ k₂ ∈ Formalism.IndefR.Lev.levG V β L, SuppF V f k₁ ∧ SuppF V (1 - f) k₂ ∧ k = k₁ * k₂ := by
  first | exact @GlobalTheory.LevSplit.lev_split | exact GlobalTheory.LevSplit.lev_split | (intros; apply GlobalTheory.LevSplit.lev_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LowCoefficientsOfParameterCoefficients
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU

private def LowZero {ι K : Type} [Field K] (a : ℕ) (f : MvPowerSeries ι K) : Prop :=
  ∀ m : ι →₀ ℕ, m.degree < a → MvPowerSeries.coeff m f = 0

private theorem lowZero_mul {ι K : Type} [Field K] {a b : ℕ} {f g : MvPowerSeries ι K}
    (hf : LowZero a f) (hg : LowZero b g) : LowZero (a + b) (f * g) := by
  intro m hm
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hdeg : x.1.degree + x.2.degree = m.degree := by rw [← hx', map_add (f := _)]
  by_cases h : x.1.degree < a
  · rw [hf _ h, zero_mul]
  · rw [hg _ (by omega), mul_zero]

private theorem lowZero_one {ι K : Type} [Field K] : LowZero 0 (1 : MvPowerSeries ι K) :=
  fun _ hm => absurd hm (Nat.not_lt_zero _)

private theorem lowZero_pow {ι K : Type} [Field K] {f : MvPowerSeries ι K}
    (hf : LowZero 1 f) (e : ℕ) : LowZero e (f ^ e) := by
  induction e with
  | zero => simpa using lowZero_one
  | succ e ih => rw [pow_succ]; exact lowZero_mul ih hf

private theorem lowZero_prod {ι K : Type} [Field K] (a : ι → MvPowerSeries ι K)
    (ha : ∀ i, LowZero 1 (a i)) (k : ι →₀ ℕ) (s : Finset ι) :
    LowZero (∑ i ∈ s, k i) (∏ i ∈ s, a i ^ k i) := by
  induction s using Finset.induction_on with
  | empty => simpa using lowZero_one
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact lowZero_mul (lowZero_pow (ha i) _) ih

private theorem coeff_subst_low {ι K : Type} [Field K] (a : ι → MvPowerSeries ι K)
    (hs : MvPowerSeries.HasSubst a) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (W : MvPowerSeries ι K) (d : ℕ) (hW : ∀ k : ι →₀ ℕ, k.degree ≤ d → MvPowerSeries.coeff k W = 0)
    (m : ι →₀ ℕ) (hm : m.degree ≤ d) : MvPowerSeries.coeff m (MvPowerSeries.subst a W) = 0 := by
  have ha1 : ∀ i, LowZero 1 (a i) := by
    intro i n hn
    have hn0 : n = 0 := by
      have : n.degree = 0 := by omega
      exact (Finsupp.degree_eq_zero_iff n).mp this
    rw [hn0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ha i]
  rw [MvPowerSeries.coeff_subst hs]
  refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
  by_cases hk : k.degree ≤ d
  · rw [hW k hk, zero_smul]
  · have h := lowZero_prod a ha1 k k.support m (by
      have : k.degree = ∑ i ∈ k.support, k i := rfl
      omega)
    have e : (k.prod fun s e => a s ^ e) = ∏ i ∈ k.support, a i ^ k i := rfl
    rw [e, h, smul_zero]

theorem low_coeff_of_param (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (K1 : Type) [Field K1]
    [Algebra (K0 p) K1] (Un : (ι →₀ ℕ) → MvPowerSeries ι (K0 p))
    (hUn : ∀ n, inParam p (Un n) = MvPowerSeries.monomial n 1 ∧
      (∀ m : ι →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m (Un n) = 0))
    (U : MvPowerSeries ι K1) (d : ℕ) (S : Finset (ι →₀ ℕ))
    (hS : ∀ n : ι →₀ ℕ, n.degree ≤ d → n ∈ S) (m : ι →₀ ℕ) (hm : m.degree ≤ d) :
    MvPowerSeries.coeff m U = ∑ n ∈ S, MvPowerSeries.coeff n (inParamK p K1 U) *
      algebraMap (K0 p) K1 (MvPowerSeries.coeff m (Un n)) := by
  have hs := Pf.en_Ec_hs p K1 (ι := ι)
  set c : (ι →₀ ℕ) → K1 := fun n => MvPowerSeries.coeff n (inParamK p K1 U) with hc

  have hmon : ∀ n, MvPowerSeries.subst (Pf.en_Ec p K1) (MvPowerSeries.monomial n (1 : K1)) =
      MvPowerSeries.map (algebraMap (K0 p) K1) (Un n) := by
    intro n
    have h1 : inParamK p K1 (MvPowerSeries.map (algebraMap (K0 p) K1) (Un n)) =
        MvPowerSeries.monomial n (1 : K1) := by
      have h2 := Pf.th_inParamK_map p (K0 p) K1 (Un n)
      rw [h2, ← Pf.th_inParam_eq, (hUn n).1]
      ext k
      rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_monomial, MvPowerSeries.coeff_monomial]
      split_ifs <;> simp
    rw [← h1, Pf.en_Ec_inParamK]
  set W : MvPowerSeries ι K1 := inParamK p K1 U - ∑ n ∈ S, c n • MvPowerSeries.monomial n (1 : K1) with hWdef
  have hWlow : ∀ k : ι →₀ ℕ, k.degree ≤ d → MvPowerSeries.coeff k W = 0 := by
    intro k hk
    have hkS := hS k hk
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hWdef, map_sub, map_sum]
    simp only [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq S k]
    simp [hkS, hc]
  have hV : MvPowerSeries.subst (Pf.en_Ec p K1) W =
      U - ∑ n ∈ S, c n • MvPowerSeries.map (algebraMap (K0 p) K1) (Un n) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← MvPowerSeries.coe_substAlgHom hs, hWdef, map_sub, map_sum, MvPowerSeries.coe_substAlgHom hs,
      Pf.en_Ec_inParamK]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← MvPowerSeries.coe_substAlgHom hs, map_smul, MvPowerSeries.coe_substAlgHom hs, hmon n]
  have h0 := coeff_subst_low (Pf.en_Ec p K1) hs (Pf.en_Ec_zero p K1) W d hWlow m hm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hV, map_sub, map_sum, sub_eq_zero] at h0
  rw [h0]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map, hc, smul_eq_mul]

end GlobalTheory.TwU
end

