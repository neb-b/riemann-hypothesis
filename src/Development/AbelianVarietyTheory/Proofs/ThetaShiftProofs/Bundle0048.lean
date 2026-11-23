module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2FamilyUniformCompare
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsBoundedByPowerOfAtLeastTwoInvD4ep0
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.SplitConst

def PB (X : ℝ) (k : ℕ) (a : ℝ) : Prop := 2 ≤ X ∧ 0 ≤ a ∧ a ≤ X ^ k

variable {X a b : ℝ} {i j : ℕ}

theorem PB.mono (h : PB X i a) (hij : i ≤ j) : PB X j a :=
  ⟨h.1, h.2.1, h.2.2.trans (pow_le_pow_right₀ (by linarith [h.1]) hij)⟩

theorem PB.of_le (h : PB X i a) (hb : 0 ≤ b) (hba : b ≤ a) : PB X i b := ⟨h.1, hb, hba.trans h.2.2⟩

theorem PB.add (h : PB X i a) (h' : PB X j b) : PB X (max i j + 1) (a + b) := by
  have h1 := (h.mono (le_max_left i j)).2.2
  have h2 := (h'.mono (le_max_right i j)).2.2
  have h3 : 0 ≤ X ^ max i j := pow_nonneg (by linarith [h.1]) _
  refine ⟨h.1, add_nonneg h.2.1 h'.2.1, ?_⟩
  rw [pow_succ]
  nlinarith [h.1]

theorem PB.mul (h : PB X i a) (h' : PB X j b) : PB X (i + j) (a * b) := by
  refine ⟨h.1, mul_nonneg h.2.1 h'.2.1, ?_⟩
  rw [pow_add]
  exact mul_le_mul h.2.2 h'.2.2 h'.2.1 (h.2.1.trans h.2.2)

theorem PB.pow (h : PB X i a) (n : ℕ) : PB X (i * n) (a ^ n) := by
  refine ⟨h.1, pow_nonneg h.2.1 _, ?_⟩
  rw [pow_mul]
  exact pow_le_pow_left₀ h.2.1 h.2.2 _

theorem PB.const (hX : 2 ≤ X) (k : ℕ) (ha : 0 ≤ a) (h : a ≤ 2 ^ k) : PB X k a :=
  ⟨hX, ha, h.trans (pow_le_pow_left₀ (by norm_num) hX _)⟩

theorem PB.base (hX : 2 ≤ X) (ha : 0 ≤ a) (h : a ≤ X) : PB X 1 a := ⟨hX, ha, by simpa using h⟩

theorem PB.sqrt (h : PB X i a) : PB X i (Real.sqrt a) := by
  refine ⟨h.1, Real.sqrt_nonneg _, ?_⟩
  have h1 : 1 ≤ X ^ i := one_le_pow₀ (by linarith [h.1])
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith [h.2.2]

theorem PB.log (h : PB X i a) (ha : 1 ≤ a) : PB X i (Real.log a) :=
  h.of_le (Real.log_nonneg ha) (by linarith [Real.log_le_sub_one_of_pos (show 0 < a by linarith)])

theorem PB.log_le {Z : ℝ} (h : PB (Real.exp Z) i a) (ha : 0 < a) : Real.log a ≤ i * Z := by
  have := Real.log_le_log ha h.2.2
  rwa [Real.log_pow, Real.log_exp] at this

theorem rpow_le_self {d s : ℝ} (hd : 1 ≤ d) (hs : 1 ≤ s) : d ^ (1 / s) ≤ d := by
  have := Real.rpow_le_rpow_of_exponent_le hd (show 1 / s ≤ 1 by rw [div_le_one (by linarith)]; exact hs)
  simpa using this

theorem isBoundedByPowerOfAtLeastTwo_inv_d4ep0 {g d f NA NC c w : ℝ} (hX : 2 ≤ X) (hg : 1 ≤ g) (hd : 1 ≤ d) (hf : 1 ≤ f) (hNA : 1 ≤ NA)
    (hNC : 1 ≤ NC) (hc : 0 < c) (hw : 1 ≤ w) (hg' : g ≤ X) (hd' : d ≤ X) (hf' : f ≤ X) (hNA' : NA ≤ X)
    (hNC' : NC ≤ X) (hc' : c ≤ X) (hw' : w ≤ X) : PB X 50 (flowEpsilonBound g d f NA NC c w)⁻¹ := by
  have pg := PB.base hX (by linarith) hg'
  have pd := PB.base hX (by linarith) hd'
  have pf := PB.base hX (by linarith) hf'
  have pNA := PB.base hX (by linarith) hNA'
  have pNC := PB.base hX (by linarith) hNC'
  have pc := PB.base hX hc.le hc'
  have pw := PB.base hX (by linarith) hw'
  have p1 : PB X 0 1 := PB.const hX 0 (by norm_num) (by norm_num)
  have p2 : PB X 1 2 := PB.const hX 1 (by norm_num) (by norm_num)
  have p4 : PB X 2 4 := PB.const hX 2 (by norm_num) (by norm_num)
  have prd : PB X 1 (d ^ (1 / (2 * f))) :=
    pd.of_le (Real.rpow_nonneg (by linarith) _) (rpow_le_self hd (by linarith))
  have pN0 := pg.mul (pd.pow 2)
  have pH := (pNC.pow 2).mul (p2.add (((p4.mul (pf.pow 4)).mul (prd.pow 2)).mul (pNA.pow 2)))
  have pK' := (pN0.mul pH).mul ((p2.mul pc).add p1)
  have pK := p1.add pK'
  have pN2 := p4.mul pf
  have pl := ((p2.mul pK).mul pN2).log (by nlinarith [pK'.2.1])
  have pR := ((pw.add (pN2.mul pl)).add pN2).add p2
  have pD := ((((pN0.pow 2).mul (pNC.pow 2)).mul pc).mul pR).mono (j := 50) (by norm_num)
  unfold flowEpsilonBound
  simp only []
  rcases min_choice (1 : ℝ) _ with h | h <;> rw [h]
  · rw [inv_one]; exact p1.mono (by norm_num)
  · rw [inv_div]
    refine pD.of_le (div_nonneg pD.2.1 (by positivity)) (div_le_self pD.2.1 (one_le_pow₀ hf))

theorem rh_inv {c w : ℝ} (hX : 2 ≤ X) (hc : 0 < c) (hw : 1 ≤ w) (hc' : c ≤ X) (hw' : w ≤ X) :
    PB X 8 (d6rh c w)⁻¹ := by
  have pc := PB.base hX hc.le hc'
  have pw := PB.base hX (by linarith) hw'
  have p12 : PB X 4 12 := PB.const hX 4 (by norm_num) (by norm_num)
  have ppi : PB X 2 Real.pi := PB.const hX 2 Real.pi_pos.le (by linarith [Real.pi_le_four])
  unfold d6rh
  rw [one_div, inv_inv]
  exact ((p12.mul ppi).mul (pc.add pw)).mono (by norm_num)

end GlobalTheory.SplitConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTauCanonicalIffOfIsPullDegTauBimult
section
noncomputable section

namespace GlobalTheory.TauCanPull

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TauTwist GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem cPoint_unit (D : DegPre R) (y : D.X) : cP D (𝟙_ (Over (Sp R))) y = D.c y := by
  rw [cP, toUnit_unit, Category.id_comp]

theorem c_pow_eq_one_iff (D : DegPre R) (n : ℕ) (y : D.X) : D.c y ^ n = 1 ↔ D.c (n • y) = D.c 0 := by
  rw [← cPoint_unit D (n • y), ← cPoint_unit D 0, cPoint_nsmul, cPoint_zero, cPoint_unit]

theorem c_eq_iff (hD : IsPullDeg φ D D') (hφ : Function.Injective φ) (x x' : D'.X) :
    D.c (hD.xe x) = D.c (hD.xe x') ↔ D'.c x = D'.c x' := by
  constructor
  · intro h
    refine Over.OverMorphism.ext ((pull_grp hD).1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [hD.c_pr, hD.c_pr, h]
  · intro h
    haveI : IsDominant (spMap φ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)⟩
    haveI : IsProper D.P.A.hom := D.P.isAb.proper
    exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp R) D.P.A.hom
      ((Over.w _).trans (Over.w _).symm) (spMap φ)
      ((hD.c_pr x).symm.trans ((congrArg (fun q => q.left ≫ _) h).trans (hD.c_pr x'))))

theorem torsion_iff (hD : IsPullDeg φ D D') (hφ : Function.Injective φ) (n : ℕ) :
    (∀ y, D.c y ^ n = 1) ↔ ∀ y, D'.c y ^ n = 1 := by
  rw [hD.xe.surjective.forall]
  refine forall_congr' fun y => ?_
  rw [c_pow_eq_one_iff, c_pow_eq_one_iff, ← c_eq_iff hD hφ, map_nsmul, map_zero]

theorem val_tau_kappa {n : ℕ} (hc : ∀ y, D.c y ^ n = 1) (a b : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J}
    (hJ : Good D.P.L z J) : val (D.tau (n • a) (n • b)) r z J = unitAt r z (kappa hc a b) := by
  have h : LB.Gen.Corr D.P.L _ _ _ _ (D.tau (n • a) (n • b)) (scaleGen (unitOn (kappa hc a b)) (LB.oneGen D.P.L)) :=
    corr_of_val D.P.isLB fun y I hI => (unitAt_kappa hc a b hI).symm.trans
      ((val_scale _ _ _ hI).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans (_root_.mul_one _))).symm
  exact (val_corr hJ h r).trans ((val_scale _ _ _ hJ).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans
    (_root_.mul_one _)))

theorem kappa_pull (hD : IsPullDeg φ D D') (hφ : Function.Injective φ) {n : ℕ} (hc : ∀ y, D.c y ^ n = 1)
    (hc' : ∀ y, D'.c y ^ n = 1) (a b : D'.X) :
    kappa hc' a b = Units.map (fracMap hφ).toMonoidHom (kappa hc (hD.xe a) (hD.xe b)) := by
  let z : (TK R').left := IsLocalRing.closedPoint (FractionRing R')
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB z
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
  have e := tau_val hD _ _ (fracMap_sq hφ) hJ hJ' (n • a) (n • b)
  have a₁ : ∀ w : D'.X, D'.xK (n • w) = (1 : TK R' ⟶ D'.P.A).left := fun w =>
    congrArg (fun q => q.left) (cPoint_nsmul_eq_one hc' (TK R') w)
  rw [map_nsmul, map_nsmul, val_tau_kappa hc _ _ _ hJ, val_tau_kappa hc' _ _ _ hJ', ← nsmul_add, a₁, a₁, a₁,
    inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul] at e
  refine unitAt_injective z (e.symm.trans ?_)
  exact (congrArg (fun q => unitAt q z _) (Category.id_comp (genMap hφ)).symm).trans
    (unitAt_spMap (𝟙 _) (fracMap hφ) z _)

theorem tauCan_iff (hD : IsPullDeg φ D D') (hφ : Function.Injective φ) (n : ℕ) :
    ArcCM.TauCan D n ↔ ArcCM.TauCan D' n := by
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨(torsion_iff hD hφ n).1 hc, fun y y' => ?_⟩
    rw [kappa_pull hD hφ hc, h, map_one]
  · rintro ⟨hc', h⟩
    refine ⟨(torsion_iff hD hφ n).2 hc', fun y y' => ?_⟩
    obtain ⟨y, rfl⟩ := hD.xe.surjective y
    obtain ⟨y', rfl⟩ := hD.xe.surjective y'
    apply Units.map_injective (f := (fracMap hφ).toMonoidHom) (fracMap hφ).injective
    rw [← kappa_pull hD hφ _ hc', h, map_one]

end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem tauCan_iff_of_isPullDeg : Known → ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] (f : R →+* R') (D₀ : Out.DegPre R) (D₁ : Out.DegPre R') (p : Out.IsPullDeg f D₀ D₁) (n : ℕ), Function.Injective f → D₀.TauBimult → D₁.TauBimult → (TauCan D₀ n ↔ TauCan D₁ n) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ p n hf _ _ => tauCan_iff p hf n

end GlobalTheory.TauCanPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SplitBaseChange
section
noncomputable section

namespace GlobalTheory.SplitBC

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

section One

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {n : ℕ}
  {s : ∀ T : Over (Sp R), (T ⟶ D.P.A) → GtPt D T} (hs : IsSplit D n s)
include hs

theorem cv_one (T : Over (Sp R)) (χ : D.X) {y : T.left} {J} (hJ : Good D.P.L y J) : cv (s T 1) χ y J = 1 := by
  have e := ((TorusModel.isAdd_iff _ _ _).1 (hs.2.1 T 1 1)).2 χ y J hJ
  have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
  rw [_root_.mul_one, hs.1, one_pow, C.face₃, _root_.mul_one] at e
  exact (mul_eq_left.1 e.symm)

theorem val_univ {T : Over (Sp R)} (b : T ⟶ D.P.A) (χ : D.X) {Z : Scheme.{0}} (r : Z ⟶ T.left) {z : Z} {J}
    (hJ : Good D.P.L z J) : val ((s T b).s χ) r z J = val ((s D.P.A (𝟙 _)).s χ) (r ≫ b.left) z J := by
  have e := hs.2.2 D.P.A T b (𝟙 _)
  rw [Category.comp_id] at e
  exact (val_corr hJ (e.2 χ) r).trans (val_pull hJ _ _ _)

theorem val_univ_one (T : Over (Sp R)) (χ : D.X) {y : T.left} {J} (hJ : Good D.P.L y J) :
    val ((s D.P.A (𝟙 _)).s χ) (1 : T ⟶ D.P.A).left y J = 1 := by
  have e := val_univ hs (1 : T ⟶ D.P.A) χ (𝟙 _) hJ
  rw [Category.id_comp] at e
  exact e.symm.trans (cv_one hs T χ hJ)

theorem gtTanR_split {v : epsR R ⟶ D.P.A} (hv : IsTangent v) : GtTanR (s (epsR R) v) := by
  let o : Over.mk (𝟙 (Sp R)) ⟶ epsR R := Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id (CommRingCat.of R))))
  have ho : o ≫ v = 1 := Over.OverMorphism.ext (hv.trans (Category.id_comp _).symm)
  have e := hs.2.2 _ _ o v
  rw [ho] at e
  refine ⟨s _ 1, ⟨(hs.1 _ _).trans (one_pow n), fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩, e⟩
  exact (cv_one hs _ χ hJ).trans (val_one _).symm

end One

section Two

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'} {D₀ : DegPre R}
  {D₁ : DegPre R'} (p : IsPullDeg f D₀ D₁) {n : ℕ} {s₀ : ∀ T : Over (Sp R), (T ⟶ D₀.P.A) → GtPt D₀ T}
  {s₁ : ∀ T : Over (Sp R'), (T ⟶ D₁.P.A) → GtPt D₁ T}

theorem univ_corr (hG : GlobalFnsSt) (h₀ : IsSplit D₀ n s₀) (h₁ : IsSplit D₁ n s₁) (χ : D₁.X) :
    (∀ k, DegPre.gtφT D₁ D₁.P.A (s₁ D₁.P.A (𝟙 _)).b χ k ≫ prj p =
      prj p ≫ DegPre.gtφT D₀ D₀.P.A (s₀ D₀.P.A (𝟙 _)).b (p.xe χ) k) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ D₁.P.A.left) (z : Z) J J', Good D₀.P.L z J → Good D₁.P.L z J' →
      val ((s₀ D₀.P.A (𝟙 _)).s (p.xe χ)) (r ≫ prj p) z J =
        (∏ k, ConstFam.wVal p.w z J J' (r ≫ DegPre.gtφT D₁ D₁.P.A (s₁ D₁.P.A (𝟙 _)).b χ k) ^ DegPre.gtε k) *
          val ((s₁ D₁.P.A (𝟙 _)).s χ) r z J' := by
  have gp := pull_grp p
  obtain ⟨g, hg⟩ := ConstPoint.exists_gtPt_through hG gp p.w_gen p.xe.toAddMonoidHom p.c_pr
    (T := D₀.P.A) (T' := D₁.P.A) (prj p) gp.1.w (s₀ D₀.P.A (𝟙 _))
  let ρ : Over.mk (D₁.P.A.hom ≫ spMap f) ⟶ D₀.P.A := Over.homMk (prj p) gp.1.w
  have hρ : pushHom gp D₁.P.A (𝟙 _) = ρ := Over.OverMorphism.ext (Category.id_comp _)
  have r₁ : pushHom gp D₁.P.A g.b = ρ ≫ (s₀ D₀.P.A (𝟙 _)).b := Over.OverMorphism.ext ((hg 0).1 2)
  have hb : g.b = (s₁ D₁.P.A (𝟙 _)).b := ConstGrp.push_injective gp _ (by
    rw [r₁, h₀.1, h₁.1, map_pow, hρ, MonObj.comp_pow, Category.comp_id])
  have he : (1 : 𝟙_ (Over (Sp R')) ⟶ D₁.P.A).left ≫ D₁.P.A.hom = 𝟙 _ := Over.w _
  have key := gen_unique' D₁.P.isLB (u := g.s χ) (u' := (s₁ D₁.P.A (𝟙 _)).s χ) (fun U _ k => by rw [hb]) D₁.P.A.hom _ he
    (hG _ _ D₁.P.isAb).2 (g.isGen χ) ((s₁ D₁.P.A (𝟙 _)).isGen χ) (fun y J' hJ' => by
      obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D₀.P.isLB y
      have v := (hg χ).2 _ (1 : 𝟙_ (Over (Sp R')) ⟶ D₁.P.A).left y J J' hJ hJ'
      have o : (1 : 𝟙_ (Over (Sp R')) ⟶ D₁.P.A).left ≫ prj p =
          (1 : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap f) ⟶ D₀.P.A).left :=
        congrArg (fun q => q.left) (map_one (pushHom gp (𝟙_ (Over (Sp R')))))
      have q := FormalPoint.prod_gtφT (1 : 𝟙_ (Over (Sp R')) ⟶ D₁.P.A) g.b χ (ConstFam.wVal p.w y J J')
      rw [hb, h₁.1, MonObj.comp_pow, Category.comp_id, one_pow, _root_.mul_one, inv_mul_cancel, _root_.one_mul,
        mul_inv_cancel, ← h₁.1, ← hb] at q
      rw [o, q, _root_.one_mul] at v
      exact v.symm.trans ((val_univ_one h₀ (Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap f)) _ hJ).trans
        (val_univ_one h₁ _ χ hJ').symm))
  refine ⟨fun k => hb ▸ (hg χ).1 k, fun Z r z J J' hJ hJ' => ?_⟩
  rw [← key Z r z J' hJ', ← hb]
  exact (hg χ).2 Z r z J J' hJ hJ'

theorem letBC_split (hG : GlobalFnsSt) (h₀ : IsSplit D₀ n s₀) (h₁ : IsSplit D₁ n s₁) {v : epsR R ⟶ D₀.P.A}
    {v₁ : epsR R' ⟶ D₁.P.A} (hv : v₁.left ≫ prj p = spMap (dualMap f) ≫ v.left) :
    LetBC p (s₀ (epsR R) v) (s₁ (epsR R') v₁) := by
  have a₀ : ∀ x k, DegPre.gtφT D₀ _ (s₀ (epsR R) v).b x k = v.left ≫ DegPre.gtφT D₀ _ (s₀ D₀.P.A (𝟙 _)).b x k := by
    intro x k
    have e := (h₀.2.2 _ _ v (𝟙 _)).1
    rw [Category.comp_id] at e
    rw [(TorusCoord.comp_eq_of_left _ (s₀ (epsR R) v).b v.left (𝟙 _) (e.symm.trans (Category.id_comp _).symm)).1 x k,
      Category.id_comp, TorusCoord.gtφT_eq]
  have a₁ : ∀ x k, DegPre.gtφT D₁ _ (s₁ (epsR R') v₁).b x k = v₁.left ≫ DegPre.gtφT D₁ _ (s₁ D₁.P.A (𝟙 _)).b x k := by
    intro x k
    have e := (h₁.2.2 _ _ v₁ (𝟙 _)).1
    rw [Category.comp_id] at e
    rw [(TorusCoord.comp_eq_of_left _ (s₁ (epsR R') v₁).b v₁.left (𝟙 _) (e.symm.trans (Category.id_comp _).symm)).1 x k,
      Category.id_comp, TorusCoord.gtφT_eq]
  have hψ : ∀ χ k, DegPre.gtφT D₁ _ (s₁ (epsR R') v₁).b χ k ≫ prj p =
      spMap (dualMap f) ≫ DegPre.gtφT D₀ _ (s₀ (epsR R) v).b (p.xe χ) k := fun χ k => by
    rw [a₀, a₁, Category.assoc, (univ_corr p hG h₀ h₁ χ).1, ← Category.assoc, hv, Category.assoc]
  refine (ArcQBC.letBC_iff p _ _).2 ⟨hψ 0 2, fun χ => ⟨hψ χ, ArcQBC.pmaps_of_val p.w_gen D₀.P.isLB D₁.P.isLB (hψ χ)
    ((s₁ _ v₁).isGen χ) ((s₀ _ v).isGen _) fun y J J' hJ hJ' => ?_⟩⟩
  have e := (univ_corr p hG h₀ h₁ χ).2 _ v₁.left y J J' hJ hJ'
  rw [hv] at e
  refine (val_univ h₀ v _ _ hJ).trans ?_
  rw [val_univ h₁ v₁ χ _ hJ']
  simp only [Category.id_comp, a₁]
  exact e

end Two

theorem split_baseChange : Known → ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] (f : R →+* R') (D₀ : Out.DegPre R) (D₁ : Out.DegPre R') (p : Out.IsPullDeg f D₀ D₁) (n : ℕ) (s₀ : ∀ T : Over (Sp R), (T ⟶ D₀.P.A) → Out.GtPt D₀ T) (s₁ : ∀ T : Over (Sp R'), (T ⟶ D₁.P.A) → Out.GtPt D₁ T), Function.Injective f → IsSplit D₀ n s₀ → IsSplit D₁ n s₁ → ∀ (v : epsR R ⟶ D₀.P.A) (v₁ : epsR R' ⟶ D₁.P.A), v₁.left ≫ prj p = spMap (dualMap f) ≫ v.left → (IsTangent v → GtTanR (s₀ (epsR R) v)) ∧ LetBC p (s₀ (epsR R) v) (s₁ (epsR R') v₁) :=
  fun hK _ _ _ _ _ _ _ _ _ _ _ p _ _ _ _ h₀ h₁ _ _ hv =>
    ⟨fun ht => gtTanR_split h₀ ht, letBC_split p hK.laws.globalFns h₀ h₁ hv⟩

end GlobalTheory.SplitBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaNormLieNormUniqueAtEmbedding
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArchNormUnique

open MeasureTheory GlobalTheory.ArchMetricCompare GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms

theorem mean_eq {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {Fd : Set (Fin g → ℂ)} (hF : IsAddFundamentalDomain Λ Fd volume) {f : (Fin g → ℂ) → ℝ}
    (hf : ∀ a ∈ Λ, ∀ x, f (x + a) = f x) :
    (∫ z in Fd, f z) / (volume Fd).toReal = latticeMean Λ f := by
  rw [latticeMean_eq Λ volume hF hf, ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF, smul_eq_mul,
    div_eq_inv_mul]
  rfl

theorem archimedean_l2_norm_unique (hU : ThetaUnifAV) {K : Type} [Field K] {P : Out.PolAV (Sp K)} {σ : K →+* ℂ}
    {rig : LB.Gen (P.L.pull (eSec P.A))} {s : P.L.Sec} {v v' : ℝ} (h : IsL2SquareIntegralProblem P rig σ s v)
    (h' : IsL2SquareIntegralProblem P rig σ s v') : v = v' := by
  obtain ⟨-, A, _, φ, u, Hm, χ, θ, Fd, hp, hu, o, hθ, hF, -, -, -, rfl⟩ := h
  obtain ⟨-, A', _, φ', u', Hm', χ', θ', Fd', hp', hu', o', hθ', hF', -, -, -, rfl⟩ := h'
  obtain ⟨e, he, heψ⟩ := grpPullback_iso hp hp'
  obtain ⟨-, -, -, -, t1, t2, -⟩ := AHWeil.tangent_and_weil_of_isAH hU (pullPol P hp') P.g u' Hm' χ' hu'
  obtain ⟨F, hFe, hFΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom A A' (pullPol P hp).isAb (pullPol P hp').isAb
    _ _ P.g P.g u u' t1 t2 e.hom he
  have hL := pull_isLB P.isLB φ
  have hL' := pull_isLB P.isLB φ'
  obtain ⟨t, ht⟩ : LBIso ((P.L.pull φ').pull e.hom.left) (P.L.pull φ) := by
    have h0 : LBIso (P.L.pull φ') (P.L.pull φ') := ⟨idIso _, idIso_isGen hL'⟩
    have h1 := (PolFibre.lbIso_pull_comp h0 e.hom.left).symm
    rwa [heψ] at h1
  have hHH : ∀ z w, hermForm Hm' (F z) (F w) = hermForm Hm z w := fun z w => by
    simpa using hermForm_pull_eq_of_lbIso_pow A A' _ _ hL hL' _ _ u u' Hm χ Hm' χ' hu hu' e.hom F hFe 1 1
      ⟨LB.linCombIso t _ _, DVR.linCombIso_isGen t ht _ _⟩ z w
  have hinj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun z hz => by
    by_contra hne
    have h1 := hu.2.1 z hne
    have h2 := hHH z z
    rw [hz] at h2
    change 0 < (hermForm Hm z z).re at h1
    rw [← h2] at h1
    simp [hermForm] at h1
  let T := LinearEquiv.ofInjectiveEndo F hinj
  have hT : ∀ z, T z = F z := fun _ => rfl
  have hx : ∀ z, (u'.ex (F z)).left ≫ φ' = (u.ex z).left ≫ φ := fun z => by
    rw [hFe, Over.comp_left, Category.assoc, heψ]
  have hΛ : ∀ z, F z ∈ u'.Λ ↔ z ∈ u.Λ := fun z => ⟨fun hz => by
    rw [← u'.ker, hFe, ← (u'.ker 0).2 u'.Λ.zero_mem, ← map_zero F, hFe, cancel_mono] at hz
    rw [← u.ker, hz, u.ker]
    exact u.Λ.zero_mem, hFΛ z⟩
  let U : P.L.ι → (Fin P.g → ℂ) → Prop := fun j z => ⊤ ≤ (u.ex z).left ⁻¹ᵁ (P.L.pull φ).U fun _ => j
  have U' : ∀ j z, U j z → ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ (P.L.pull φ').U fun _ => j := fun j z hz =>
    (le_pull_iff _ _ _ _).2 ((hx z).symm ▸ (le_pull_iff _ _ _ _).1 hz)
  have Uc : ∀ z, ∃ j, U j z := fun z => by
    obtain ⟨j, hj⟩ := exists_chart_at hL (u.ex z).left
    exact ⟨j PUnit.unit, hj⟩
  let Pm : u.Λ →+ (Fin P.g → ℂ) := u.Λ.subtype.toAddMonoidHom
  have hr : Set.range Pm = u.Λ := Subtype.range_coe
  have hr' : Pm.range = u.Λ.toAddSubgroup := SetLike.coe_injective hr
  have hfr : ∀ j z, U j z → u'.fr (fun _ => j) (F z) = u.fr (fun _ => j) z :=
    GeneratorNorm.frames_eq Pm (by rw [hr']; exact u.discrete) (by rw [hr]; exact u.full) U (fun j => (u.hol _ 0).1) Uc
      (fun j z a hz => by
        have := ex_add_period u z a
        simp only [U] at hz ⊢
        exact this ▸ hz)
      (fun j j' z => valAt' ((u.ex z).left ≫ φ) (P.L.U j ⊓ P.L.U j') (P.L.g j j').val)
      (fun j => u.fr fun _ => j) (fun j z => u'.fr (fun _ => j) (F z))
      (fun a z => Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re))
      (fun j => u.fr_hol _)
      (fun j => (u'.fr_hol _).comp (LinearMap.toContinuousLinearMap F).differentiable.differentiableOn (U' j))
      (fun j z => u.fr_ne _ z)
      (fun j j' z h1 h2 => by
        have h3 := (top_le_preimage_inf _ _ _).2 ⟨h1, h2⟩
        rw [u.fr_compat _ _ z h3, val_pull_g _ _ _ _ _ h3])
      (fun j j' z h1 h2 => by
        have h3 := (top_le_preimage_inf _ _ _).2 ⟨U' j z h1, U' j' z h2⟩
        show u'.fr _ (F z) = _ * u'.fr _ (F z)
        rw [u'.fr_compat _ _ _ h3, val_pull_g _ _ _ _ _ h3, hx])
      (fun j hj => by
        have h0 : ⊤ ≤ (P.L.pull (eSec P.A)).U fun _ => j := by
          have h1 := (le_pull_iff _ _ _ _).1 hj
          rw [TangentOrigin.ex_zero_left] at h1
          refine (le_spMap_iff σ _).1 ((le_pull_iff _ _ _ _).2 ?_)
          exact PolBaseChange.eSec_comm hp ▸ h1
        show u'.fr _ (F 0) = _
        rw [map_zero, o' j h0, o j h0])
      (fun a j z hz => by
        show ‖u.fr _ z‖ = _ * ‖u.fr _ (z + a)‖
        rw [hu.2.2.2 a _ z hz, norm_mul, norm_mul, hu.2.2.1, _root_.one_mul]
        exact congrArg (· * _) (GeneratorNorm.norm_factor Hm z a))
      (fun a j z hz => by
        show ‖u'.fr _ (F z)‖ = _ * ‖u'.fr _ (F (z + a))‖
        rw [hu'.2.2.2 ⟨F a, hFΛ a a.2⟩ _ _ (U' j z hz), norm_mul, norm_mul, hu'.2.2.1, _root_.one_mul, map_add (f := _),
          ← hHH, ← hHH]
        exact congrArg (· * _) (GeneratorNorm.norm_factor Hm' (F z) (F a)))
  have hθθ : ∀ z, θ' (F z) = θ z := fun z => by
    obtain ⟨j, hj⟩ := Uc z
    have h1 := hθ' j (F z) ((le_pull_iff _ _ _ _).1 (U' j z hj))
    rw [hx, hθ j z ((le_pull_iff _ _ _ _).1 hj), hfr j z hj] at h1
    exact (mul_right_cancel₀ (u.fr_ne _ z hj) h1).symm
  have hff : ∀ z, ‖θ' (F z)‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm' (F z)) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z) := fun z => by
    rw [hθθ, show hermSq Hm' (F z) = hermSq Hm z from congrArg Complex.re (hHH z z)]
  have hper : ∀ a ∈ u.Λ, ∀ z, ‖θ (z + a)‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm (z + a)) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm z) := fun a ha z => by
    obtain ⟨th, hth⟩ := sec_pull_down ((isGen_iff _).1 (idIso_isGen hL)) P.isLB hL s
    have hth := KeyPow.appLE_eq_of_stalk _ s th (hth _ (𝟙 _))
    refine weight_periodic hL hu (s := th) (fun j z hz => ?_) ⟨a, ha⟩ z
    have e := val_via _ s th hth (u.ex z).left (j PUnit.unit) j ((top_le_preimage_inf _ _ _).2 ⟨hz, hz⟩)
    refine Eq.trans ?_ (hθ (j PUnit.unit) z ((le_pull_iff _ _ _ _).1 hz))
    rw [e]
    exact ((congrArg (· * _) (val_g_self hL _ j hz)).trans (_root_.one_mul _)).symm
  have hper' : ∀ a ∈ u'.Λ, ∀ z, ‖θ' (z + a)‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm' (z + a)) =
      ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * hermSq Hm' z) := fun a ha z => by
    obtain ⟨a, rfl⟩ := T.surjective a
    obtain ⟨z, rfl⟩ := T.surjective z
    rw [← map_add (f := _), hT, hT, hff, hff, hper a ((hΛ a).1 ha)]
  haveI := u.discrete
  haveI := u'.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  haveI : IsZLattice ℝ u'.Λ := ⟨u'.full⟩
  rw [mean_eq u.Λ hF hper, mean_eq u'.Λ hF' hper',
    ← latticeMean_comp_equiv u.Λ u'.Λ (T.restrictScalars ℝ).toContinuousLinearEquiv hΛ hper']
  exact congrArg _ (funext fun z => (hff z).symm)

theorem norms_unique : Known → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (σ : K →+* ℂ) (v v' : ℝ), (∀ (rig : LB.Gen (P.L.pull (eSec P.A))) (th : P.L.Sec), rig.IsGen → Arch.IsThNormAt P rig th σ v → Arch.IsThNormAt P rig th σ v' → v = v') ∧ ∀ η' : epsR K ⟶ P.A, IsTangent η' → Arch.IsLieNormAt P η' σ v → Arch.IsLieNormAt P η' σ v' → v = v' := by
  intro hK K _ P σ v v'
  refine ⟨fun rig th _ h h' => archimedean_l2_norm_unique hK.theta ((isL2Sq_iff_isThNormAt P rig σ th v).2 h)
    ((isL2Sq_iff_isThNormAt P rig σ th v').2 h'), ?_⟩
  rintro t ht ⟨Q, φ, w, x, hp, hw, hx, u, Hm, χ, z, hu, hz, rfl⟩ ⟨Q', φ', w', x', hp', hw', hx', u', Hm', χ', z', hu', hz', rfl⟩
  have e := CM.LieMetric.hermForm_eq hK.theta (P := P) (s := σ) ⟨g_eq hp, hp, LBIso.symm ⟨w, hw⟩⟩
    ⟨g_eq hp', hp', LBIso.symm ⟨w', hw'⟩⟩ hu hu' (I := PUnit) (v := fun _ => t) (fun _ => ht)
    (w := fun _ => x) (w' := fun _ => x') (W := fun _ => z) (W' := fun _ => z') (fun _ => ⟨hx, hz⟩) (fun _ => ⟨hx', hz'⟩)
    PUnit.unit PUnit.unit
  exact congrArg (fun c : ℂ => Real.log (Real.pi * c.re) / 2) e

end GlobalTheory.ArchNormUnique
end

