module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0493
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulMemLatticeOfAcrisBound
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.Count

section Coord

variable {l : ℕ} [hl : Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

def cfO {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) : O ⊗[ℤ_[l]] R →ₗ[ℤ_[l]] R :=
  (TensorProduct.lid ℤ_[l] R).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id

theorem cfO_tmul {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) (o : O) (r : R) :
    cfO f (o ⊗ₜ[ℤ_[l]] r) = f o • r := by
  simp [cfO]

theorem cfO_mul {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) (β : R)
    (y : O ⊗[ℤ_[l]] R) : cfO f (((1 : O) ⊗ₜ[ℤ_[l]] β) * y) = β * cfO f y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [mul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
  | tmul o r => rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, cfO_tmul, cfO_tmul, mul_smul_comm]

theorem cfO_map {R R' : Type} [CommRing R] [Algebra ℤ_[l] R] [CommRing R'] [Algebra ℤ_[l] R']
    (f : O →ₗ[ℤ_[l]] ℤ_[l]) (φ : R →ₐ[ℤ_[l]] R') (y : O ⊗[ℤ_[l]] R) :
    cfO f (Algebra.TensorProduct.map (AlgHom.id O O) φ y) = φ (cfO f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul o r => rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, cfO_tmul, cfO_tmul, map_smul]

theorem cfO_natCast_smul {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) (m : ℕ)
    (y : O ⊗[ℤ_[l]] R) : cfO f ((m : O) • y) = (m : R) * cfO f y := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]

theorem cfO_smul_one {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) (o : O) :
    cfO f (o • (1 : O ⊗[ℤ_[l]] R)) = algebraMap ℤ_[l] R (f o) := by
  rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one, cfO_tmul,
    Algebra.smul_def, mul_one]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [Algebra O LL] [TopologicalSpace LL]

def cfT {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) (g : ↥T.L.T →ₗ[O] O) :
    TW R T →ₗ[O] R :=
  (TensorProduct.rid O R).toLinearMap ∘ₗ TensorProduct.map LinearMap.id g

theorem cfT_tmul {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) (g : ↥T.L.T →ₗ[O] O)
    (s : R) (t : ↥T.L.T) : cfT T g (s ⊗ₜ[O] t) = g t • s := by
  simp [cfT]

theorem cfT_incl {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (T : LocLat G Qp LL O) (g : ↥T.L.T →ₗ[O] O) (φ : R →ₐ[O] R') (z : TW R T) :
    cfT T g (TWincl φ T z) = φ (cfT T g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul s t => rw [TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      cfT_tmul, cfT_tmul, map_smul]

theorem cfT_smul {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) (g : ↥T.L.T →ₗ[O] O)
    (r : R) (z : TW R T) : cfT T g (r • z) = r * cfT T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
  | tmul s t => rw [TensorProduct.smul_tmul', cfT_tmul, cfT_tmul, smul_eq_mul, mul_smul_comm]

end Coord

end GlobalTheory.BKGal.Count

namespace GlobalTheory.BKGal.Count

variable {l : ℕ} [hl : Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
  [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K]

theorem smul_cancel (T : LocLat (Gl l) ℚ_[l] K O) (c : ℕ) {u v : TW (OB l O) T}
    (h : ((l : O) ^ c) • u = ((l : O) ^ c) • v) : u = v := by
  have e : ∀ w : TW (OB l O) T, ((l : O) ^ c) • w = ((l : OB l O) ^ c) • w := by
    intro w
    rw [← algebraMap_smul (OB l O) ((l : O) ^ c) w, map_pow, map_natCast]
  rw [e, e] at h
  exact (isUnit_l_OB.pow c).smul_left_cancel.1 h

theorem toB_algebraMap (q : ℤ_[l]) :
    acrisToBcris l (ainfToAcris l (algebraMap ℤ_[l] (Ainf l) q)) = algebraMap ℤ_[l] (Per.Bcris l) q := by
  rw [AlgHom.commutes, AlgHom.commutes]

theorem le_of_bound {n c v j : ℕ} (hj : 2 * j < l - 1) (h : (l - 1) * n ≤ (l - 1) * (c + v) + 2 * j) :
    n ≤ c + v := by
  have h1 : (l - 1) * n < (l - 1) * (c + v + 1) := by
    rw [mul_add, mul_one]; omega
  exact Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_left h1)

end GlobalTheory.BKGal.Count

namespace GlobalTheory.BKGal.Count

theorem count : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O), l ≠ 2 → ∀ ε : OCb l, IsEps ε → ∀ (j n c : ℕ),
    2 * j < l - 1 → ∀ (u : TW (OB l O) T) (x : ↥T.L.T) (w : TW (OCr l O) T),
    (l : O) ^ n • u = (1 : OB l O) ⊗ₜ[O] x →
    toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ j) • ((l : O) ^ c • u) = TWincl (toOB l O) T w →
    ∃ x' : ↥T.L.T, (l : O) ^ c • u = (1 : OB l O) ⊗ₜ[O] x' := by
  intro l _ O K _ _ _ _ _ _ _ _ _ T hl2 ε hε j n c hj u x w h1 h2
  let bO := Module.Free.chooseBasis ℤ_[l] O
  let bT := latBasis T
  have hr0 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε) = (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (muOf ε)) := by
    simp only [toB, toOB, toOCr, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have hr : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ j) =
      (1 : O) ⊗ₜ[ℤ_[l]] (acrisToBcris l (ainfToAcris l (muOf ε)) ^ j) := by
    rw [map_pow, hr0, Algebra.TensorProduct.tmul_pow, one_pow]
  have hlO : ∀ m : ℕ, (l : O) ^ m = ((l ^ m : ℕ) : O) := fun m => by push_cast; rfl
  have key : ∀ k i, (l : ℤ_[l]) ^ (n - c) ∣ bO.coord k (bT.coord i x) := by
    intro k i
    by_cases ha : bO.coord k (bT.coord i x) = 0
    · rw [ha]; exact dvd_zero _
    have e1 := congrArg (fun z => cfO (bO.coord k) (cfT T (bT.coord i) z)) h1
    have e2 := congrArg (fun z => cfO (bO.coord k) (cfT T (bT.coord i) z)) h2
    rw [hlO, map_smul, cfO_natCast_smul, cfT_tmul, cfO_smul_one] at e1
    rw [hr, cfT_smul, cfO_mul, hlO, map_smul, cfO_natCast_smul, cfT_incl, toOB, cfO_map] at e2
    set U := cfO (bO.coord k) (cfT T (bT.coord i) u)
    set a := bO.coord k (bT.coord i x)
    set W' := cfO (bO.coord k) (cfT T (bT.coord i) w)
    have e3 : acrisToBcris l ((l : Per.Acris l) ^ n * W') = acrisToBcris l
        (ainfToAcris l (muOf ε ^ j * algebraMap ℤ_[l] (Ainf l) ((l : ℤ_[l]) ^ c * a))) := by
      rw [map_mul, map_mul, ← e2, map_pow, map_natCast, map_mul, toB_algebraMap, map_mul, ← e1]
      push_cast
      simp only [map_pow]
      ring
    have e4 := GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l e3
    have hne : (l : ℤ_[l]) ^ c * a ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)) ha
    have hb := GlobalTheory.T.valuation_bound_of_primePow_dvd_mu_pow_acris l hl2 ε hε j n ((l : ℤ_[l]) ^ c * a) hne ⟨W', e4.symm⟩
    rw [PadicInt.valuation_p_pow_mul c a ha] at hb
    have hv : n - c ≤ a.valuation := by have := le_of_bound hj hb; omega
    exact Ideal.mem_span_singleton.1 ((PadicInt.mem_span_pow_iff_le_valuation a ha (n - c)).2 hv)
  choose q hq using key
  let x' : ↥T.L.T := bT.equivFun.symm fun i => bO.equivFun.symm fun k => q k i
  have hx' : (l : O) ^ (n - c) • x' = x := by
    apply bT.equivFun.injective
    funext i
    rw [map_smul, Pi.smul_apply, LinearEquiv.apply_symm_apply, smul_eq_mul]
    apply bO.equivFun.injective
    funext k
    rw [show (l : O) ^ (n - c) = algebraMap ℤ_[l] O ((l : ℤ_[l]) ^ (n - c)) by rw [map_pow, map_natCast],
      ← Algebra.smul_def, map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul,
      Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, ← hq k i]
    rfl
  refine ⟨(l : O) ^ (c + (n - c) - n) • x', smul_cancel T (n - c) ?_⟩
  have e5 : (l : O) ^ (n - c) • ((l : O) ^ c • u) = (l : O) ^ (c + (n - c) - n) • ((l : O) ^ n • u) := by
    rw [smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2
    omega
  rw [e5, h1, ← hx', TensorProduct.tmul_smul, TensorProduct.tmul_smul, smul_smul,
    smul_smul, mul_comm]

end GlobalTheory.BKGal.Count
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiUnitOnRescaleUniformizerOfQVal
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

noncomputable section

namespace GlobalTheory.TauTwist

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out

theorem psiUnitOn_rescale_of_qVal : ∀ (T : Formalism.L2.Pj.CDVR) (D : DegPre T.V) (ϖ : T.V), Irreducible ϖ → ∀ (y : D.X) (n : ℤ), QVal D ϖ y n → ∀ q : D.X → (FractionRing T.V)ˣ, (q y : FractionRing T.V) = algebraMap T.V (FractionRing T.V) ϖ ^ (-n) → PsiUnitOn (GlobalTheory.TauTwist.rescale D q) y Set.univ := by
  intro T D ϖ hϖ y n hQ q hq j V hV hU hc h
  obtain ⟨e, -, c, ⟨u, hu⟩, hC⟩ := genHasVal_units _ _ _ _ _ _ hQ
  obtain ⟨C, hCv, hCt⟩ := hC j
  have hW : V ≤ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c y).left) j :=
    fun x hx => Set.mem_iInter.2 fun k => by cases k; exact hc hx
  have hπ : algebraMap T.V (FractionRing T.V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).mpr hϖ.ne_zero
  have hqc : (q y : FractionRing T.V) * c = algebraMap T.V (FractionRing T.V) (u : T.V) := by
    rw [hq, hu, ← _root_.mul_assoc, ← zpow_add₀ hπ, neg_add_cancel, zpow_zero, _root_.one_mul]
  have hconst : (res (X := Spec (CommRingCat.of (FractionRing T.V)))
      (le_top : LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c y)) j ≤ ⊤) (unitOn (q y))).val * C.val =
      (res (X := Spec (CommRingCat.of (FractionRing T.V))) le_top
        (unitOn (Units.map (algebraMap T.V (FractionRing T.V)).toMonoidHom u))).val := by
    rw [hCv]
    show ((Spec (CommRingCat.of (FractionRing T.V))).presheaf.map (homOfLE le_top).op).hom _ *
      ((Spec (CommRingCat.of (FractionRing T.V))).presheaf.map (homOfLE le_top).op).hom _ =
      ((Spec (CommRingCat.of (FractionRing T.V))).presheaf.map (homOfLE le_top).op).hom _
    rw [← map_mul]
    congr 1
    simp only [scal, unitOn, Units.coe_map, MonoidHom.coe_coe, Scheme.Hom.id_appTop]
    change (Scheme.ΓSpecIso (CommRingCat.of (FractionRing T.V))).inv.hom (q y : FractionRing T.V) *
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing T.V))).inv.hom c =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing T.V))).inv.hom (algebraMap T.V (FractionRing T.V) (u : T.V))
    rw [← map_mul, hqc]
  refine ⟨(res (le_top : V ≤ ⊤) (unitOn u)).val * (res hW (e.s j)).val, (Units.isUnit _).mul (Units.isUnit _), ?_⟩
  have hval : (((rescale D q).psi y).s j).val = (res (X := Spec (CommRingCat.of (FractionRing T.V)))
      (le_top : LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c y)) j ≤ ⊤)
        (unitOn (Units.map (algebraMap T.V (FractionRing T.V)).toMonoidHom u))).val *
      (res (wchart_le_preimage D.P.L (jK T.V) (fun _ => (D.c y).left) (fun _ => ptK (D.c y))
        (fun _ => QForm.ptK_eq D y) j) (pullU (jK T.V) _ (e.s j))).val := by
    show (HMul.hMul (α := (Γ(Spec (CommRingCat.of (FractionRing T.V)), LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c y)) j))ˣ)
      (β := (Γ(Spec (CommRingCat.of (FractionRing T.V)), LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c y)) j))ˣ)
      (res le_top (unitOn (q y))) ((D.psi y).s j)).val = _
    rw [hCt, ← _root_.mul_assoc, Units.val_mul, Units.val_mul, hconst]
  rw [hval]
  apply fn_ext
  intro x hx
  refine (gs_pull (𝟙 _) (jK T.V) x V hx _).trans (Eq.trans ?_ (gs_res (𝟙 _) x h hx _).symm)
  rw [gs_mul (𝟙 _ ≫ jK T.V) x V hx]
  refine Eq.trans (congrArg₂ (· * ·) ?_ ?_) (gs_mul (𝟙 _) x _ (h hx) _ _).symm
  · refine (gs_res _ x le_top hx _).trans (Eq.trans ?_ (gs_res _ x le_top (h hx) _).symm)
    exact (unitAt_val (𝟙 _ ≫ jK T.V) x u).symm.trans ((congrArg Units.val
      (unitAt_spMap (𝟙 _) (algebraMap T.V (FractionRing T.V)) x u)).trans (unitAt_val _ x _))
  · refine (gs_res _ x hW hx _).trans (Eq.trans ?_ (gs_res _ x _ (h hx) _).symm)
    exact (gs_pull (𝟙 _) (jK T.V) x _ (hW hx) _).symm

end GlobalTheory.TauTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QValPullbackMulRamificationCompleteDvr
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)
open ReciprocityTheory.ChartRestriction.G.DVR (HasVal GenHasVal wchart_le_preimage)

noncomputable section

namespace GlobalTheory.QValPull

theorem chart_eq_of_val {V : Type} [CommRing V] [IsDomain V] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {φ : PUnit → (Spec (CommRingCat.of V) ⟶ X)} {φ' : PUnit → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    (hφ : ∀ k, φ' k = jK V ≫ φ k) {ε : PUnit → ℤ} {t : LB.Gen (LB.LinComb L φ' ε)}
    {e : LB.Gen (LB.LinComb L φ ε)} {c : FractionRing V}
    (h : ∀ (z : Spec (CommRingCat.of (FractionRing V))) (J : (Spec (CommRingCat.of (FractionRing V)) ⟶ X) → L.ι),
      Good L z J → (val t (𝟙 _) z J).val =
        gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) * (val e (𝟙 _ ≫ jK V) z J).val)
    (j : PUnit → L.ι) :
    (t.s j).val = resTop _ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) *
      (res (wchart_le_preimage L (jK V) φ φ' hφ j) (pullU (jK V) _ (e.s j))).val := by
  apply fn_ext
  intro x hx
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL x φ' j (fun a b _ => by cases a; cases b; rfl)
    (fun k => LB.wchart_le L φ' j k hx)
  have h1 : ∀ k, J (𝟙 _ ≫ φ' k) = j k := fun k => by rw [Category.id_comp]; exact hJj k
  have h2 : ∀ k, J ((𝟙 _ ≫ jK V) ≫ φ k) = j k := fun k => by rw [Category.id_comp, ← hφ]; exact hJj k
  have eL : gs (𝟙 _) x _ (t.s j).val = (val t (𝟙 _) x J).val :=
    (gs_unit _ x _ hx _).trans (congrArg Units.val (val_of t (𝟙 _) x J j h1).symm)
  rw [eL, h x J hJ]
  refine Eq.trans ?_ (gs_mul _ x _ hx _ _).symm
  congr 1
  · exact (gs_res _ x _ hx _).symm
  · have hx' : x ∈ LB.wchart L φ' j := hx
    have hxe : x ∈ jK V ⁻¹ᵁ LB.wchart L φ j := wchart_le_preimage L (jK V) φ φ' hφ j hx'
    unfold res pullU
    simp only [Units.coe_map, MonoidHom.coe_coe]
    refine Eq.symm ((gs_res _ x _ hx _).trans ((gs_pull (𝟙 _) (jK V) x _ hxe _).trans
      ((gs_unit (𝟙 _ ≫ jK V) x _ hxe _).trans ?_)))
    exact congrArg Units.val (val_of e _ x J j h2).symm

theorem hasVal_fracMap {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] {g : V →+* V'}
    (hg : Function.Injective g) {ϖ : V} {ϖ' : V'} {e : ℕ} (ha : Associated (g ϖ) (ϖ' ^ e))
    {c : FractionRing V} {n : ℤ} (hc : HasVal ϖ c n) : HasVal ϖ' (ArcPull.fracMap hg c) (e * n) := by
  obtain ⟨u, rfl⟩ := hc
  obtain ⟨v, hv⟩ := ha
  refine ⟨v⁻¹ ^ n * Units.map (g : V →* V') u, ?_⟩
  have hϖ : g ϖ = ϖ' ^ e * ((v⁻¹ : V'ˣ) : V') := by
    rw [← hv, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
  have key : ∀ (w : V'ˣ) (m : ℤ), algebraMap V' (FractionRing V') ((w ^ m : V'ˣ) : V') =
      algebraMap V' (FractionRing V') (w : V') ^ m := by
    intro w m
    have h1 := Units.coe_map (algebraMap V' (FractionRing V') : V' →* FractionRing V') (w ^ m)
    rw [map_zpow, Units.val_zpow_eq_zpow_val, Units.coe_map] at h1
    simpa only [MonoidHom.coe_coe] using h1.symm
  rw [map_mul, map_zpow₀, ArcPull.fracMap_algebraMap, ArcPull.fracMap_algebraMap, hϖ, Units.val_mul, map_mul,
    map_mul, map_pow, key, mul_zpow, ← zpow_natCast, ← zpow_mul]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  ring

theorem gs_scal_spMap {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (z : Spec (CommRingCat.of K')) (c : K) :
    gs (spMap f) z ⊤ (scal (𝟙 (Spec (CommRingCat.of K))) c) =
      gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of K'))) (f c)) := by
  unfold gs scal spMap
  simp only [TopologicalSpace.Opens.mem_top, ↓reduceDIte]
  have hn := congrArg (fun φ => CommRingCat.Hom.hom φ c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  rw [hn]
  rfl

theorem qVal_pull {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    {g : V →+* V'} {D : DegPre V} {D' : DegPre V'} (hD : IsPullDeg g D D') {ϖ : V} {ϖ' : V'} {e : ℕ}
    (hg : Function.Injective g) (ha : Associated (g ϖ) (ϖ' ^ e)) (y : D'.X) (n : ℤ) (h : QVal D ϖ (hD.xe y) n) :
    QVal D' ϖ' y (e * n) := by
  obtain ⟨e0, he0, c0, hc0, hch⟩ := h
  obtain ⟨e', he', hdown⟩ := ArcPull.exists_down_om hD.w_gen D.P.isLB D'.P.isLB (spMap g)
    (fun _ : PUnit => hD.c_pr y) e0 he0
  refine ⟨e', he', ArcPull.fracMap hg c0, hasVal_fracMap hg ha hc0, ?_⟩
  refine chart_eq_of_val D'.P.isLB (fun _ => DVR.QForm.ptK_eq D' y) ?_
  intro z J' hJ'
  obtain ⟨J, hJ, -⟩ := exists_good D.P.L D.P.isLB z (fun k : Empty => k.elim) (fun k : Empty => k.elim)
    (fun a => a.elim) (fun k => k.elim)
  have hv := DVR.SectionScalarValuation.val_genHasVal (hφ := fun _ => DVR.QForm.ptK_eq D (hD.xe y)) hch (ArcPull.genMap hg) z hJ
  have hp := ArcPull.psi_val hD (ArcPull.genMap hg) (𝟙 (Spec (CommRingCat.of (FractionRing V')))) (ArcPull.fracMap_sq hg) hJ hJ' y
  have hd := hdown _ (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') z J J' hJ hJ'
  have hr : ArcPull.genMap hg ≫ jK V = (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') ≫ spMap g := by
    rw [← ArcPull.fracMap_sq hg, Category.assoc]
    rfl
  have hxk : (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ D'.xK y) = (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') ≫ (D'.c y).left := by
    rw [Category.assoc]
    exact congrArg _ (DVR.QForm.ptK_eq D' y)
  rw [hp, hr, hd] at hv
  simp only [Fintype.prod_unique, zpow_neg, zpow_one] at hv
  rw [← hxk, show ArcPull.genMap hg = spMap (ArcPull.fracMap hg) from rfl, gs_scal_spMap] at hv
  generalize ArcPull.om hD.w z J J' (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ D'.xK y) = o at hv
  generalize val (D'.psi y) (𝟙 (Spec (CommRingCat.of (FractionRing V')))) z J' = A at hv ⊢
  generalize val e' (𝟙 (Spec (CommRingCat.of (FractionRing V'))) ≫ jK V') z J' = E at hv ⊢
  generalize gs (𝟙 (Spec (CommRingCat.of (FractionRing V')))) z ⊤ (scal (𝟙 _) (ArcPull.fracMap hg c0)) = G at hv ⊢
  rw [Units.val_mul, Units.val_mul] at hv
  linear_combination o.val * hv + (G * E.val - A.val) * Units.mul_inv o

theorem main : ∀ (T T' : Formalism.L2.Pj.CDVR) (g : T.V →+* T'.V) (D : DegPre T.V) (D' : DegPre T'.V) (hD : IsPullDeg g D D')
    (ϖ : T.V) (ϖ' : T'.V) (e : ℕ), Function.Injective g → Irreducible ϖ → Irreducible ϖ' →
    Associated (g ϖ) (ϖ' ^ e) → ∀ (y : D'.X) (n : ℤ), QVal D ϖ (hD.xe y) n → QVal D' ϖ' y (e * n) := by
  intro T T' g D D' hD ϖ ϖ' e hg _ _ ha y n h
  exact qVal_pull hD hg ha y n h

end GlobalTheory.QValPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumPowGrowth
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_pow_growth :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B C : Subgroup (L ≃ₐ[K] L)), A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → (∀ σ ∈ A, σ ^ p ∈ C → σ ∈ B) → min (2 * jumpSum (wild K L) A B) (jumpSum (wild K L) A B + E) ≤ jumpSum (wild K L) A C := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E A B C hA hE hC hB
  obtain ⟨j, hj, hr, -, hG⟩ := _root_.GlobalTheory.PMon.Ram.baseChange_fixedField K L A
  have hmem : ∀ σ, j σ ∈ A := fun σ => hr.le ⟨σ, rfl⟩
  have hw : wild ↥(IntermediateField.fixedField A) L = fun t => (wild K L t).comap j := by
    funext t
    exact hG _
  have h0 : lowerRamificationGroup ↥(IntermediateField.fixedField A) L 0 = ⊤ := by
    rw [hG, eq_top_iff]
    intro σ _
    exact hA (hmem σ)
  have key := _root_.GlobalTheory.PMon.Ram.min_jumpSum_le_of_pow_mem_of_inertia_eq_top ↥(IntermediateField.fixedField A) L p E (B.comap j) (C.comap j) h0 hE
    (fun σ τ => by
      have := hC _ (hmem σ) _ (hmem τ)
      simpa [Subgroup.mem_comap, map_mul, map_inv] using this)
    (fun σ h => by
      have h' : j σ ^ p ∈ C := by simpa [Subgroup.mem_comap, map_pow] using h
      exact hB _ (hmem σ) h')
  rw [hw, jumpSum_comap_injective _ _ j _ B hj, jumpSum_comap_injective _ _ j _ C hj, hr] at key
  exact key

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualRepSpansMatrixAlgebraOfGoodPoint
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem GlobalTheory.Pass.residualRep_spans_matrixAlgebra_of_goodPoint : ∀ D : D7, ResidualIrreducibleRankR D → ResidualAbsIrreducible (D := D) := by
  intro D hN9
  have hr2 : 2 ≤ D.R.r := by
    unfold Ranks.r; have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  refine ⟨hr2, ?_⟩
  intro i hi rb hrb
  have hirr := (hN9 i hi rb hrb).1
  have habs := GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (D.naut.kFbar i) (by omega) rb
    fun W hW => hirr W fun g _ x hx => hW g x hx
  exact GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub rb habs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanMulMem
section
namespace GlobalTheory.SpanMulInertiaEigenvalues

open NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem span_mul_mem {a b : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E}
    (ha : a ∈ Formalism.L2.SG.LocVol.OEv v) (hb : b ∈ Formalism.L2.SG.LocVol.OEv v) :
    a * b ∈ Formalism.L2.SG.LocVol.OEv v := by
  unfold Formalism.L2.SG.LocVol.OEv at *
  rw [SetLike.mem_coe] at *
  set S := (fun x : 𝓞 E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (x : E)) '' Set.univ
    with hS
  have hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    refine ⟨x * y, Set.mem_univ _, ?_⟩
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR _ (algebraMap (𝓞 E) E (x * y)) = _
    rw [map_mul, map_mul]
  have key : ∀ x ∈ S, ∀ y ∈ Submodule.span (v.adicCompletionIntegers F) S,
      x * y ∈ Submodule.span (v.adicCompletionIntegers F) S := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (hSmul x hx y hy)
    | zero => simp
    | add y z _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  induction ha using Submodule.span_induction with
  | mem x hx => exact key x hx b hb
  | zero => simp
  | add x z _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : Algebra F E] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {a b : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E}, a ∈ Formalism.L2.SG.LocVol.OEv v → b ∈ Formalism.L2.SG.LocVol.OEv v → a * b ∈ Formalism.L2.SG.LocVol.OEv v :=
  fun v _ _ ha hb => span_mul_mem v ha hb

end GlobalTheory.SpanMulInertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittPowerSeriesMemDividedPowerSeriesGeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ x : (Wq l a)⟦X⟧, inclS t K x ∈ SdSet t K e := by
  first | exact @GlobalTheory.CrysPrism.inclS_mem_SdSet | exact GlobalTheory.CrysPrism.inclS_mem_SdSet | (intros; apply GlobalTheory.CrysPrism.inclS_mem_SdSet <;> assumption)
end

