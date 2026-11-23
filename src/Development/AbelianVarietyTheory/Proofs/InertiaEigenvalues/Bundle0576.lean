module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandard
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogTeichmullerPowSemistablePeriods
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LogFlat

theorem rootT_cocycle_of_pow_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (g : GQ l) (y ϖ x : Per.Fl l) (n : ℕ) (a b : ℤ_[l]),
    y ^ n = ϖ * x → ϖ.untilt ≠ 0 →
    (∀ m, rootT (Per.σF g y) m = rootT C.ε m ^ (PadicInt.toZModPow m a).val * rootT y m) →
    (∀ m, rootT (Per.σF g ϖ) m = rootT C.ε m ^ (PadicInt.toZModPow m b).val * rootT ϖ m) →
    ∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m ((n : ℤ_[l]) * a - b)).val * rootT x m := by
  intro l _ C g y ϖ x n a b hyx hϖ ha hb m
  have hmul : ∀ u v : Per.Fl l, rootT (u * v) m = rootT u m * rootT v m := by
    intro u v; simp only [rootT, iterate_map_mul, map_mul]
  have hpow : ∀ u : Per.Fl l, rootT (u ^ n) m = rootT u m ^ n := by
    intro u; simp only [rootT, iterate_map_pow, map_pow]
  have hζ : rootT C.ε m ^ (l ^ m) = 1 := by
    rw [rootT_pow_eq_untilt]; exact (core_isEps l C).1
  have hϖm : rootT ϖ m ≠ 0 := by
    intro h0; apply hϖ; rw [← rootT_pow_eq_untilt, h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
  have hζ0 : ∀ k : ℕ, rootT C.ε m ^ k ≠ 0 := by
    intro k h0
    have : rootT C.ε m = 0 := pow_eq_zero_iff'.mp h0 |>.1
    rw [this, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hζ
    exact zero_ne_one hζ
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set A := (PadicInt.toZModPow m a).val
  set B := (PadicInt.toZModPow m b).val
  set Cc := (PadicInt.toZModPow m ((n : ℤ_[l]) * a - b)).val
  have hexp : rootT C.ε m ^ (n * A) = rootT C.ε m ^ (B + Cc) := by
    rw [pow_eq_pow_mod (n * A) hζ, pow_eq_pow_mod (B + Cc) hζ]
    congr 1
    rw [← ZMod.natCast_eq_natCast_iff']
    simp only [A, B, Cc, Nat.cast_mul, Nat.cast_add, ZMod.natCast_val, ZMod.cast_id', id, map_sub, map_mul,
      map_natCast]
    ring
  have h1 : rootT ((Per.σF g y) ^ n) m = rootT (Per.σF g ϖ * Per.σF g x) m := by
    rw [← map_pow, ← map_mul, hyx]
  rw [hpow, hmul, ha, hb, mul_pow, ← pow_mul, ← hpow y, hyx, hmul, mul_comm A n, hexp] at h1
  have h2 : rootT C.ε m ^ B * (rootT ϖ m * rootT ((Per.σF g) x) m) =
      rootT C.ε m ^ B * (rootT ϖ m * (rootT C.ε m ^ Cc * rootT x m)) := by
    rw [pow_add] at h1; linear_combination -h1
  have h3 := mul_left_cancel₀ (hζ0 B) h2
  exact mul_left_cancel₀ hϖm h3

theorem rootT_σF_tilt_l : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (C : Core l), C.ζ = P.ζQ → ∀ ϖ : Per.Fl l,
    (∀ m : ℕ, (rootT ϖ m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (lRoot l m)) → ∀ (g : GQ l) (m : ℕ),
    rootT (Per.σF g ϖ) m = rootT C.ε m ^ (PadicInt.toZModPow m (kummer P g)).val * rootT ϖ m := by
  intro l _ P C hζ ϖ hr g m
  have hit : ∀ k : ℕ, ((frobeniusEquiv (Per.Fl l) l).symm)^[k] (Per.σF g ϖ) =
      Per.σF g (((frobeniusEquiv (Per.Fl l) l).symm)^[k] ϖ) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, RingHom.map_frobeniusEquiv_symm]
  have hsig : rootT (Per.σF g ϖ) m = Per.σO g (rootT ϖ m) := by
    rw [rootT, hit, GlobalTheory.RingBasics.untilt_σF]; rfl
  rw [hsig]
  apply Subtype.ext
  have h1 : ((Per.σO g (rootT ϖ m) : Per.OC l) : ℂ_[l]) = Per.σC g (rootT ϖ m : ℂ_[l]) :=
    GlobalTheory.RingIface.sigO_coe l g _
  have h2 : Per.σC g (algebraMap (Om l) ℂ_[l] (lRoot l m)) = algebraMap (Om l) ℂ_[l] (g (lRoot l m)) :=
    GlobalTheory.RingBasics.σC_coe g _
  push_cast
  rw [h1, hr, h2, isKummer_kummer P g m, map_mul, map_pow, C.ε_root, hζ]

theorem exists_log_flat_pow_Bst : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (_ : True), ∃ (b : P.R.B) (c : ↥(GK K) → ℤ_[l]), ((∀ g : ↥(GK K), actSt P (g : GQ l) (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C ((c g : ℚ_[l]) • P.tB)) ∧ phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b)) ∧ (∀ g, bk.FixFlat g → c g = 0) ∧ ∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m := by
  intro l _ K bk P AI T C hF _
  obtain ⟨ϖ, hr⟩ := GlobalTheory.Pst.NoLog.exists_tilt (lRoot l) (lRoot_succ l) l (lRoot_zero l)
  have hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l) := Subtype.ext (by
    have := hr 0
    rw [lRoot_zero, map_natCast] at this
    exact this.trans (SubringClass.coe_natCast _ _).symm)
  obtain ⟨x, hxu, hx⟩ := GlobalTheory.T.tilt_uniformizer_pow_eq_mul_unit l K bk ϖ hϖ
  obtain ⟨cπ, hcπ, hfix⟩ := GlobalTheory.T.exists_kummer_cocycle_tilt_uniformizer l K bk C
  obtain ⟨bx, hφ, hgal⟩ := GlobalTheory.T.exists_teichmuller_log_unit_bcris l C x hxu
  have hϖ0 : ϖ.untilt ≠ 0 := by
    rw [hϖ]; exact_mod_cast (Fact.out : l.Prime).ne_zero
  refine ⟨T.eB.symm bx, fun g => (bk.Ep.natDegree : ℤ_[l]) * cπ g, ⟨fun g => ?_, ?_⟩,
    fun g hg => by simp [hfix g hg], GlobalTheory.T.exists_truncLog_gal_mod_filP l K bk C cπ hcπ⟩
  · have hx' := rootT_cocycle_of_pow_eq_mul l C (g : GQ l) bk.flat ϖ x bk.Ep.natDegree (cπ g) (kummer P g) hx hϖ0 (hcπ g)
      (rootT_σF_tilt_l l P C hF.ζ ϖ hr g)
    have h1 := hgal (g : GQ l) _ hx'
    have h2 : P.actQ (g : GQ l) (T.eB.symm bx) = T.eB.symm bx +
        (((bk.Ep.natDegree : ℤ_[l]) * cπ g - kummer P g : ℤ_[l]) : ℚ_[l]) • P.tB := by
      apply T.eB.injective
      rw [T.actB, RingEquiv.apply_symm_apply, h1, map_add (f := _), RingEquiv.apply_symm_apply, Algebra.smul_def, map_mul,
        T.zB, hF.t]
    rw [map_add (f := _), actSt_X, actSt_C, h2, Polynomial.C_add]
    have key : ((kummer P (g : GQ l) : ℤ_[l]) : ℚ_[l]) • P.tB +
        (((bk.Ep.natDegree : ℤ_[l]) * cπ g - kummer P g : ℤ_[l]) : ℚ_[l]) • P.tB =
        (((bk.Ep.natDegree : ℤ_[l]) * cπ g : ℤ_[l]) : ℚ_[l]) • P.tB := by
      rw [← add_smul]; congr 1; push_cast; ring
    show _ = _ + Polynomial.C ((((bk.Ep.natDegree : ℤ_[l]) * cπ g : ℤ_[l]) : ℚ_[l]) • P.tB)
    rw [← key, Polynomial.C_add]; ring
  · have h2 : P.φB (T.eB.symm bx) = (l : P.R.B) * T.eB.symm bx := by
      apply T.eB.injective
      rw [T.frob, RingEquiv.apply_symm_apply, hφ, map_mul, map_natCast, RingEquiv.apply_symm_apply]
    rw [map_add (f := _), phiSt_X, phiSt_C, h2, mul_add, Polynomial.C_mul, map_natCast]

end GlobalTheory.LogFlat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNumerator
section
set_option autoImplicit false

namespace GlobalTheory.ScalarUnit

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts
open scoped nonZeroDivisors

section Ideals

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem smul_eq_idlE_mul (J : Ideal (𝓞 E)) (M : Submodule (𝓞 E) E) : J • M = idlE J * M := by
  unfold idlE
  apply le_antisymm
  · refine Submodule.smul_le.mpr fun r hr m hm => ?_
    rw [Algebra.smul_def]
    exact Submodule.mul_mem_mul (Submodule.mem_map_of_mem hr) hm
  · refine Submodule.mul_le.mpr fun x hx m hm => ?_
    obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.mp hx
    rw [Algebra.linearMap_apply, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hr hm

omit [NumberField E] in
theorem idlE_mul (I J : Ideal (𝓞 E)) : idlE (I * J) = idlE I * idlE J := IsLocalization.coeSubmodule_mul E I J

theorem idlE_cancel {G : Ideal (𝓞 E)} (hG : G ≠ ⊥) {X Y : Submodule (𝓞 E) E} (h : idlE G * X = idlE G * Y) :
    X = Y := by
  have hG' : (G : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hG
  have e : idlE G = ((G : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := rfl
  have key : ∀ Z : Submodule (𝓞 E) E,
      (((G : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) *
        (idlE G * Z) = Z := by
    intro Z
    rw [e, ← mul_assoc, ← FractionalIdeal.coe_mul, inv_mul_cancel₀ hG', FractionalIdeal.coe_one, one_mul]
  rw [← key X, h, key Y]

theorem index_coprime {n p : ℕ} (hp : p.Prime) (Λ : GenLat E n) (h : Λ.TrivAt p)
    (h0 : (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ≠ 0) :
    Nat.Coprime (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index p := by
  obtain ⟨k, hk, hk1, -⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Λ.La.toAddSubgroup ⧸ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero h0
  let _ := Fintype.ofFinite (Λ.La.toAddSubgroup ⧸ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup)
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have hdvd' : p ∣ Fintype.card
      (Λ.La.toAddSubgroup ⧸ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup) := by
    rw [← Nat.card_eq_fintype_card]; exact hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hdvd'
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hmem : k • y ∈ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup := by
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]
    have hc : ((k • y : Λ.La.toAddSubgroup) : Fin n → E) = (k : 𝓞 E) • (y : Fin n → E) := by
      rw [Nat.cast_smul_eq_nsmul]
      rfl
    rw [hc]
    have h1 : (k : 𝓞 E) • (y : Fin n → E) ∈ Ideal.span {(k : 𝓞 E)} • Λ.La :=
      Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) y.2
    show (k : 𝓞 E) • (y : Fin n → E) ∈ Λ.La ⊓ stdLat E n
    exact Submodule.mem_inf.mpr ⟨Λ.La.smul_mem _ y.2, hk1 h1⟩
  have hz : k • (QuotientAddGroup.mk y :
      Λ.La.toAddSubgroup ⧸ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup) = 0 := by
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hmem
  have hpk : p ∣ k := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero hz
  exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hk.symm hpk)

theorem val_natCast {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {p a : ℕ}
    (hp : (p : 𝓞 K) ∈ la.asIdeal) (h : Nat.Coprime a p) : la.valuation K (a : K) = 1 := by
  have hnot : (a : 𝓞 K) ∉ la.asIdeal := by
    intro ha
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr h).map (Int.castRingHom (𝓞 K))
    have huv' : u * (a : 𝓞 K) + v * (p : 𝓞 K) = 1 := by simpa using huv
    apply la.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← huv']
    exact la.asIdeal.add_mem (la.asIdeal.mul_mem_left u ha) (la.asIdeal.mul_mem_left v hp)
  rw [← map_natCast (algebraMap (𝓞 K) K) a]
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (v := la) (K := K)).mpr hnot

variable [IsCMField E]

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem map_bar_bar (H : Host E) (J : Ideal (𝓞 E)) :
    (J.map (H.bar : 𝓞 E →+* 𝓞 E)).map (H.bar : 𝓞 E →+* 𝓞 E) = J := by
  rw [Ideal.map_map]
  have hid : (H.bar : 𝓞 E →+* 𝓞 E).comp (H.bar : 𝓞 E →+* 𝓞 E) = RingHom.id _ :=
    RingHom.ext fun a => bar_bar H a
  rw [hid, Ideal.map_id]

theorem conjI_eq (H : Host E) (J : Ideal (𝓞 E)) : GlobalTheory.SW.conjI J = J.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  unfold GlobalTheory.SW.conjI
  rw [Ideal.map]
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, hab⟩
    refine ⟨b, hb, ?_⟩
    apply RingOfIntegers.ext
    exact (H.bar_eq b).trans hab.symm
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, H.bar_eq b⟩

theorem exists_numerator (H : Host E) {n : ℕ} (Λ : GenLat E n) (h : Λ.Unimod) :
    (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ≠ 0 ∧
    ∃ cc : Ideal (𝓞 E), cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧
      Submodule.span (𝓞 E) (detSet Λ.La) * idlE (cc.map (H.bar : 𝓞 E →+* 𝓞 E)) = idlE cc ∧
      (((Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℕ) : 𝓞 E) ∈ cc := by
  obtain ⟨J, hJ0, hJn, hJd, hJc, -⟩ := GlobalTheory.DetIdeal.detIdeal_selfDual E n Λ h
  refine ⟨?_, ?_⟩
  · rw [← hJn]
    exact fun h0 => hJ0 (Ideal.absNorm_eq_zero_iff.mp h0)
  have hrel : idlE J * Submodule.span (𝓞 E) (detSet Λ.La) = idlE (J.map (H.bar : 𝓞 E →+* 𝓞 E)) := by
    rw [← smul_eq_idlE_mul, ← hJd, hJc, conjI_eq H]
    rfl
  obtain ⟨A, hA⟩ : J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E) ∣ J := Ideal.dvd_iff_le.mpr le_sup_left
  have hG0 : J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := fun h0 => hJ0 (eq_bot_iff.mpr (h0 ▸ le_sup_left))
  have hGbar : (J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E)).map (H.bar : 𝓞 E →+* 𝓞 E) =
      J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [Ideal.map_sup, map_bar_bar, sup_comm]
  have hJbar : J.map (H.bar : 𝓞 E →+* 𝓞 E) =
      (J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E)) * A.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    conv_lhs => rw [hA]
    rw [Ideal.map_mul, hGbar]
  have hcop : A ⊔ A.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ := by
    have e : (J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E)) * (A ⊔ A.map (H.bar : 𝓞 E →+* 𝓞 E)) =
        (J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E)) * ⊤ := by
      rw [Ideal.mul_sup, ← hA, ← hJbar, Ideal.mul_top]
    exact mul_left_cancel₀ hG0 e
  have hJA : J ≤ A := by
    rw [hA]
    exact Ideal.mul_le_right
  refine ⟨A.map (H.bar : 𝓞 E →+* 𝓞 E), ?_, ?_, ?_⟩
  · rw [map_bar_bar, sup_comm]
    exact hcop
  · rw [map_bar_bar, mul_comm]
    apply idlE_cancel hG0
    rw [← mul_assoc, ← idlE_mul, ← hA, hrel]
    conv_lhs => rw [hJbar]
    rw [idlE_mul]
  · have hm : (((Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℕ) : 𝓞 E) ∈ J := by
      rw [← hJn]
      exact Ideal.absNorm_mem J
    have h2 := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hm
    rw [map_natCast] at h2
    exact Ideal.map_mono hJA h2

end Ideals

end GlobalTheory.ScalarUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootInRayClassFieldNatModulus
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT

namespace GlobalTheory.RayRootOfUnity

theorem norm_pos_of_pos_real {K : Type} [Field K] [NumberField K] {x : K} (hx : x ≠ 0)
    (h : ∀ τ : K →+* ℝ, 0 < τ x) : 0 < Algebra.norm ℚ x := by
  classical
  let c : (K →ₐ[ℚ] ℂ) → (K →ₐ[ℚ] ℂ) := fun φ =>
    { (starRingEnd ℂ).comp φ.toRingHom with
      commutes' := fun a => by
        change starRingEnd ℂ (φ (algebraMap ℚ K a)) = _
        rw [φ.commutes]; simp }
  have hc : ∀ φ e, c φ e = starRingEnd ℂ (φ e) := fun _ _ => rfl
  have hφ : ∀ φ : K →ₐ[ℚ] ℂ, φ x ≠ 0 := fun φ => (map_ne_zero _).2 hx
  have hn : ∀ φ : K →ₐ[ℚ] ℂ, (‖φ x‖ : ℂ) ≠ 0 := fun φ => by
    exact_mod_cast (norm_ne_zero_iff.2 (hφ φ))
  have h1 : ∏ φ : K →ₐ[ℚ] ℂ, (φ x / (‖φ x‖ : ℂ)) = 1 := by
    refine Finset.prod_involution (fun φ _ => c φ) (fun φ _ => ?_) (fun φ _ hne he => ?_)
      (fun _ _ => Finset.mem_univ _) (fun φ _ => ?_)
    · rw [hc, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have := hn φ
      push_cast
      field_simp
    · apply hne
      have hr : ∀ e, ((φ e).re : ℂ) = φ e := fun e =>
        Complex.conj_eq_iff_re.1 (by rw [← hc, he])
      let τ : K →+* ℝ :=
        { toFun := fun e => (φ e).re, map_one' := by simp, map_zero' := by simp,
          map_add' := by simp, map_mul' := fun a b => by
            apply Complex.ofReal_injective
            rw [Complex.ofReal_mul, hr, hr, hr, map_mul] }
      have hτ : 0 < (φ x).re := h τ
      rw [← hr x, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]
      exact div_self (by exact_mod_cast hτ.ne')
    · ext e; simp [hc]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun φ _ => hn φ),
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ x] at h1
  have h2 : ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ φ : K →ₐ[ℚ] ℂ, ‖φ x‖ := by
    apply Complex.ofReal_injective
    push_cast
    rw [← h1]
    rfl
  have : (0 : ℝ) < ((Algebra.norm ℚ x : ℚ) : ℝ) := by
    rw [h2]; exact Finset.prod_pos fun φ _ => norm_pos_iff.2 (hφ φ)
  exact_mod_cast this

theorem absNorm_modEq_one {K : Type} [Field K] [NumberField K] {𝔮 : Ideal (𝓞 K)} {p : ℕ}
    (hq : 𝔮 ≤ Ideal.span {(p : 𝓞 K)}) {I : Ideal (𝓞 K)} {α β : 𝓞 K} (hαβ : RayPair 𝔮 α β)
    (hI : I * Ideal.span {β} = Ideal.span {α}) : Ideal.absNorm I ≡ 1 [MOD p] := by
  obtain ⟨hα, hβ, _, hcβ, hd, hpos⟩ := hαβ
  have hpos' : 0 < Algebra.norm ℤ α * Algebra.norm ℤ β := by
    have hx : ((α * β : 𝓞 K) : K) ≠ 0 := by simpa using mul_ne_zero hα hβ
    have := norm_pos_of_pos_real hx fun τ => by
      have := hpos τ
      simpa [map_mul] using this
    rw [← Algebra.coe_norm_int, map_mul] at this
    exact_mod_cast this
  have h1 := congrArg Ideal.absNorm hI
  rw [map_mul, Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton] at h1
  have h2 : (Ideal.absNorm I : ℤ) * Algebra.norm ℤ β * Algebra.norm ℤ β = Algebra.norm ℤ α * Algebra.norm ℤ β := by
    have e := congrArg (Nat.cast : ℕ → ℤ) h1
    rw [Nat.cast_mul, Int.natCast_natAbs, Int.natCast_natAbs] at e
    have e2 : (Ideal.absNorm I : ℤ) * |Algebra.norm ℤ β| * |Algebra.norm ℤ β| =
        |Algebra.norm ℤ α| * |Algebra.norm ℤ β| := by rw [e]
    rw [mul_assoc, abs_mul_abs_self, ← abs_mul, abs_of_pos hpos'] at e2
    rw [mul_assoc]; exact e2
  have h3 := GlobalTheory.Mem.RayNorm.norm_cast_eq K p (hq hd)
  obtain ⟨u, hu, v, hv, huv⟩ := Ideal.isCoprime_iff_exists.1 hcβ
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have h4 := GlobalTheory.Mem.RayNorm.norm_cast_eq K p (x := b * β) (y := 1) (by
    have : b * β - 1 = -v := by linear_combination huv
    rw [this]; exact neg_mem (hq hv))
  rw [map_mul, map_one] at h4
  have h5 := congrArg (Int.cast : ℤ → ZMod p) h2
  push_cast at h4 h5
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  linear_combination ((Algebra.norm ℤ b : ℤ) : ZMod p) ^ 2 * h5 +
    ((Algebra.norm ℤ b : ℤ) : ZMod p) ^ 2 * ((Algebra.norm ℤ β : ℤ) : ZMod p) * h3 +
    (((Algebra.norm ℤ b : ℤ) : ZMod p) * ((Algebra.norm ℤ β : ℤ) : ZMod p) + 1) * (1 - (Ideal.absNorm I : ZMod p)) * h4

end GlobalTheory.RayRootOfUnity

namespace GlobalTheory.RayRootOfUnity

theorem exists_isPrimitiveRoot_of_isRay : ∀ {K H : Type} [Field K] [NumberField K] [Field H] [NumberField H]
    [Algebra K H] [IsAbelianGalois K H] {n : ℕ}, n ≠ 0 → GlobalTheory.FieldSize.IsRay H (Ideal.span {(n : 𝓞 K)}) →
    ∃ ζ : H, IsPrimitiveRoot ζ n := by
  intro K H _ _ _ _ _ _ n hn hR
  classical
  have hRF : GlobalTheory.Mem.Fld.IsRayField K H (Ideal.span {(n : 𝓞 K)}) := ⟨inferInstance, hR⟩
  have h𝔮 : Ideal.span {(n : 𝓞 K)} ≠ ⊥ := by simpa using hn
  let ψ : H →+* ℂ := (IsAlgClosed.lift : H →ₐ[ℚ] ℂ).toRingHom
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n hn
  obtain ⟨S, hSa, hS⟩ := GlobalTheory.Mem.BaseField.exists_gens H
  obtain ⟨L, hfd, hgal, hSL, -, -⟩ := GlobalTheory.exists_galois_subfield_conj_stable (insert z S) (by
    intro w hw
    rcases Finset.mem_insert.1 hw with rfl | hw
    exacts [GlobalTheory.Mem.BaseField.isAlgebraic_exp n, hSa w hw])
  have hψL : ∀ x, ψ x ∈ L := hS L (fun w hw => hSL w (Finset.mem_insert_of_mem hw)) ψ
  have hzL : z ∈ L := hSL z (Finset.mem_insert_self _ _)
  have : NumberField L := {}
  letI : Algebra H L := (ψ.codRestrict L hψL).toAlgebra
  letI : Algebra K L := ((ψ.codRestrict L hψL).comp (algebraMap K H)).toAlgebra
  have : IsScalarTower K H L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  obtain ⟨x, hx⟩ := GlobalTheory.Mem.RayZeta.root_mem_rayField K H L _ n hn le_rfl hRF
    (GlobalTheory.RayMaximal.closure_isFrob_eq_top L h𝔮)
    (fun I α β hαβ hI => absNorm_modEq_one le_rfl hαβ hI) ⟨z, hzL⟩
    (Subtype.ext (by simpa using hz.pow_eq_one))
  have e : ψ x = z := congrArg Subtype.val hx
  exact ⟨x, IsPrimitiveRoot.of_map_of_injective (f := ψ) (by rw [e]; exact hz) ψ.injective⟩

end GlobalTheory.RayRootOfUnity
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPeriodMemNonZeroDivisorsDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem per_ne_zero {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) {τ : Ainf l} (h : bk.IsPer τ) : τ ≠ 0 := by
  rintro rfl
  obtain ⟨-, ε, η, hε, hφ⟩ := h
  rw [map_zero] at hφ
  have h1 : WittVector.teichmuller l ε - 1 = 0 := (Units.mul_right_eq_zero η).1 hφ.symm
  have h2 : ε = 1 := by
    have := congrArg (fun w => WittVector.coeff w 0) (sub_eq_zero.1 h1)
    simpa using this
  subst h2
  exact hε.2 (by simp)

theorem iA_per_mem_nonZeroDivisors : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l),
    bk.IsPer τ → bk.iA τ ∈ nonZeroDivisors (bk.DA bk.ρ₀) := by
  intro l _ K bk τ hτ
  obtain ⟨h0, h1, -, -⟩ := _root_.GlobalTheory.BSP.norm_E_le_radius l K bk (Ainf l) bk.ev
  haveI : IsDomain (bk.DA bk.ρ₀) := (discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := _root_.GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [← map_zero bk.iA]
  exact fun h => per_ne_zero bk hτ (hinj h)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingsRegularPhiSurjectiveFil
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.MemLoc

theorem tied_regular_and_onto :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
      (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 →
        (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) ∧
      (∀ u : P.R.B, ∃ x, x - P.φB x = u) ∧
      ∀ (K : FinExt l) (w : P.R.BdR), ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 :=
  GlobalTheory.T.bcris_regular_surjections_of_fontaine_theorem _root_.GlobalTheory.MemLoc.fontaineBcris

end GlobalTheory.MemLoc
end

