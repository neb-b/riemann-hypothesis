module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparison
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0508
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0509
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0467
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0510

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisComparisonKisinLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CrisCmpExist

variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G]
  {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}

theorem twincl_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul b x => simp [TWincl, TensorProduct.smul_tmul']

theorem twincl_injective {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (hf : Function.Injective f) : Function.Injective (TWincl f T) := by
  haveI : Module.Free O ↥T.L.T := T.L.free
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T) f.toLinearMap hf

theorem inclL_smul' (r : OA l O) (d : ι → OA l O) : inclL t ϖ P (r • d) = inclO l O r • inclL t ϖ P d := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  exact congrArg _ (funext fun i => map_mul _ _ _)

variable {I : Ident t ϖ P T} {m n : OA l O}

def dFun (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (x : ↥T.L.T) : ι → OA l O :=
  (LinearMap.mem_range.1 (hn x)).choose

theorem dFun_spec (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (x : ↥T.L.T) :
    inclL t ϖ P (dFun hn x) = inclO l O n • I.ofT x :=
  (LinearMap.mem_range.1 (hn x)).choose_spec

def dMap (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) : ↥T.L.T →ₗ[O] (ι → OA l O) where
  toFun := dFun hn
  map_add' x y := inclL_injective t ϖ P (by
    rw [map_add (f := _), dFun_spec, dFun_spec, dFun_spec, map_add (f := _), smul_add])
  map_smul' r x := inclL_injective t ϖ P (by
    rw [LinearMap.map_smul, dFun_spec, dFun_spec, LinearMap.map_smul, RingHom.id_apply, smul_comm])

theorem dMap_spec (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (x : ↥T.L.T) :
    inclL t ϖ P (dMap hn x) = inclO l O n • I.ofT x :=
  dFun_spec hn x

def gA (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) : TW (OA l O) T →ₗ[OA l O] (ι → OA l O) :=
  LinearMap.liftBaseChange (OA l O) (dMap hn)

theorem inclL_gA (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (z : TW (OA l O) T) :
    inclL t ϖ P (gA hn z) = inclO l O n • I.j.symm (TWincl (inclO l O) T z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul b x =>
    rw [gA, LinearMap.liftBaseChange_tmul, inclL_smul', dMap_spec]
    have : TWincl (inclO l O) T (b ⊗ₜ[O] x) = inclO l O b • ((1 : OW l O) ⊗ₜ[O] x) := by
      simp [TWincl, smul_tmul']
    rw [this, LinearEquiv.map_smul, smul_comm]
    rfl

def zz (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z) (i : ι) :
    TW (OA l O) T :=
  (hm _ ⟨Pi.single i 1, rfl⟩).choose

theorem zz_spec (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z)
    (i : ι) : I.j (inclO l O m • inclL t ϖ P (Pi.single i 1)) = TWincl (inclO l O) T (zz hm i) :=
  (hm _ ⟨Pi.single i 1, rfl⟩).choose_spec

def crisComparisonLToBcrisTensorMap (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z) :
    (ι → OB l O) →ₗ[OB l O] TW (OB l O) T :=
  (Pi.basisFun (OB l O) ι).constr (OB l O) fun i => TWincl (toB l O) T (zz hm i)

def crisComparisonBcrisTensorToLMap (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) : TW (OB l O) T →ₗ[OB l O] (ι → OB l O) :=
  LinearMap.liftBaseChange (OB l O) (((toB l O).toLinearMap.compLeft ι) ∘ₗ dMap hn)

theorem kisin_jB_toB (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z)
    (c : ι → OA l O) (z : TW (OA l O) T)
    (hz : I.j (inclO l O m • inclL t ϖ P c) = TWincl (inclO l O) T z) :
    crisComparisonLToBcrisTensorMap hm (fun i => toB l O (c i)) = TWincl (toB l O) T z := by
  have hz' : z = ∑ i, c i • zz hm i := by
    apply twincl_injective (T := T) (inclO l O) inclO_injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hz, map_sum]
    have hc : inclL t ϖ P c = ∑ i, inclO l O (c i) • inclL t ϖ P (Pi.single i 1) := by
      conv_lhs => rw [pi_eq_sum_univ' c]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => inclL_smul' _ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [twincl_smul, ← zz_spec hm i, smul_comm, LinearEquiv.map_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hz', map_sum, crisComparisonLToBcrisTensorMap, Module.Basis.constr_apply_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [twincl_smul, Pi.basisFun_equivFun]
  rfl

theorem kisin_kB_tensor_incl (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (z : TW (OA l O) T) :
    crisComparisonBcrisTensorToLMap hn (TWincl (toB l O) T z) = fun i => toB l O (gA hn z i) := by
  induction z using TensorProduct.induction_on with
  | zero => funext i; simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]; funext i; simp
  | tmul b x =>
    have : TWincl (toB l O) T (b ⊗ₜ[O] x) = toB l O b ⊗ₜ[O] x := by simp [TWincl]
    rw [this, crisComparisonBcrisTensorToLMap, gA, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul]
    funext i
    simp

theorem kisin_kB_comp_jB (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z)
    (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (v : ι → OB l O) :
    crisComparisonBcrisTensorToLMap hn (crisComparisonLToBcrisTensorMap hm v) = (toB l O m * toB l O n) • v := by
  have h : (crisComparisonBcrisTensorToLMap hn).comp (crisComparisonLToBcrisTensorMap hm) = (toB l O m * toB l O n) • LinearMap.id := by
    refine (Pi.basisFun (OB l O) ι).ext fun i => ?_
    rw [LinearMap.comp_apply, crisComparisonLToBcrisTensorMap, Module.Basis.constr_basis, kisin_kB_tensor_incl, LinearMap.smul_apply, LinearMap.id_apply]
    have hg : gA hn (zz hm i) = (m * n) • Pi.single i 1 := by
      apply inclL_injective t ϖ P
      rw [inclL_gA, ← zz_spec hm i, LinearEquiv.symm_apply_apply, inclL_smul', map_mul, mul_smul, smul_comm]
    rw [hg, Pi.basisFun_apply]
    funext j
    by_cases hij : j = i
    · subst hij; simp
    · simp [Pi.single_apply, hij]
  exact LinearMap.congr_fun h v

theorem kisin_jB_comp_kB (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z)
    (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (w : TW (OB l O) T) :
    crisComparisonLToBcrisTensorMap hm (crisComparisonBcrisTensorToLMap hn w) = (toB l O m * toB l O n) • w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | tmul b x =>
    have h1 : b ⊗ₜ[O] x = b • ((1 : OB l O) ⊗ₜ[O] x) := by rw [smul_tmul', smul_eq_mul, mul_one]
    rw [h1, LinearMap.map_smul, LinearMap.map_smul, smul_comm]
    congr 1
    rw [crisComparisonBcrisTensorToLMap, LinearMap.liftBaseChange_tmul, one_smul]
    change crisComparisonLToBcrisTensorMap hm (fun i => toB l O (dMap hn x i)) = _
    rw [kisin_jB_toB hm (dMap hn x) ((m * n) ⊗ₜ[O] x)]
    · simp [TWincl, smul_tmul']
    · rw [dMap_spec, smul_smul, ← map_mul, LinearEquiv.map_smul, Ident.j_ofT]
      simp [TWincl, smul_tmul']

theorem exists_of (hm : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O m • v) = TWincl (inclO l O) T z)
    (hn : ∀ x, inclO l O n • I.ofT x ∈ LA t ϖ P) (hu : IsUnit (toB l O m)) (hv : IsUnit (toB l O n)) :
    ∃ jB, IsCrisCmp I jB := by
  obtain ⟨u, hu'⟩ := hu
  obtain ⟨v, hv'⟩ := hv
  let F : (ι → OB l O) →ₗ[OB l O] TW (OB l O) T := ((u⁻¹ : (OB l O)ˣ) : OB l O) • crisComparisonLToBcrisTensorMap hm
  let Gm : TW (OB l O) T →ₗ[OB l O] (ι → OB l O) := ((v⁻¹ : (OB l O)ˣ) : OB l O) • crisComparisonBcrisTensorToLMap hn
  have key : ((u⁻¹ : (OB l O)ˣ) : OB l O) * (((v⁻¹ : (OB l O)ˣ) : OB l O) * (toB l O m * toB l O n)) = 1 := by
    rw [← hu', ← hv']
    calc _ = (((u⁻¹ : (OB l O)ˣ) : OB l O) * u) * (((v⁻¹ : (OB l O)ˣ) : OB l O) * v) := by ring
      _ = 1 := by rw [Units.inv_mul, Units.inv_mul, mul_one]
  have key2 : ((v⁻¹ : (OB l O)ˣ) : OB l O) * (((u⁻¹ : (OB l O)ˣ) : OB l O) * (toB l O m * toB l O n)) = 1 := by
    rw [← key]; ring
  refine ⟨LinearEquiv.ofLinear F Gm ?_ ?_, ?_⟩
  · refine LinearMap.ext fun w => ?_
    simp only [F, Gm, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.map_smul, kisin_jB_comp_kB, smul_smul,
      LinearMap.id_apply]
    rw [key, one_smul]
  · refine LinearMap.ext fun w => ?_
    simp only [F, Gm, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.map_smul, kisin_kB_comp_jB, smul_smul,
      LinearMap.id_apply]
    rw [key2, one_smul]
  · intro c z hz
    rw [LinearEquiv.ofLinear_apply]
    have hz2 : I.j (inclO l O m • inclL t ϖ P c) = TWincl (inclO l O) T (m • z) := by
      rw [LinearEquiv.map_smul, hz, twincl_smul]
    simp only [F, LinearMap.smul_apply]
    rw [kisin_jB_toB hm c _ hz2, twincl_smul, smul_smul, ← hu', Units.inv_mul, one_smul]

end GlobalTheory.BKGal.CrisCmpExist

theorem GlobalTheory.BKGal.exists_isCrisCmp : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T), ∃ jB, IsCrisCmp I jB := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  obtain ⟨ε, hε⟩ := (_root_.GlobalTheory.MuOfEps.main l).1
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨-, -, -, hunit, -, -, -⟩ := (_root_.GlobalTheory.MuOfEps.main l).2 ε δ hε hδ
  obtain ⟨-, -, h3, h4⟩ := _root_.GlobalTheory.BKExp.exponents l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ
  have hU : ∀ k : ℕ, IsUnit (toB l O (1 ⊗ₜ (muOf ε ^ k))) := fun k => by
    have : toB l O (1 ⊗ₜ (muOf ε ^ k)) = (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
        (acrisToBcris l (ainfToAcris l (muOf ε))) ^ k := by
      rw [← map_pow, ← map_pow, ← map_pow]
      rfl
    rw [this]
    exact (hunit.map _).pow k
  exact GlobalTheory.BKGal.CrisCmpExist.exists_of h4 h3 (hU α) (hU β)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinHomOfUniformizerFrameStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisinHom_of_uniformizerFrame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K)) (d v : C.A), IsFrame bk C d v → C.D.δ v = 0 → ∃ g : Hom bk.prism C, BK.hf g X = v := by
  first | exact @GlobalTheory.BSP.exists_hom_of_frame | exact GlobalTheory.BSP.exists_hom_of_frame | (intros; apply GlobalTheory.BSP.exists_hom_of_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinLiftCompatibleBdRPrismsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisin_lift_compatible_bdR_prisms : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (n : ℕ) (x : ↥(OL K)), ∃ (k : ℕ) (s : bk.S), aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * C.o ((x : ↥K.1) : Om l) ∈ Per.FilP l n ∧ (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, BK.hf f bk.E ^ n ∣ (l : B.A) ^ k * (BK.hf f s - BK.hf g s)) := by
  first | exact @GlobalTheory.BSP.RingHomLiftCongruence.exists_lift | exact GlobalTheory.BSP.RingHomLiftCongruence.exists_lift | (intros; apply GlobalTheory.BSP.RingHomLiftCongruence.exists_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspidalListHarishChandraPairingNeZero
section
noncomputable section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.SuppCusp

section general
variable {G : Type} [Group G] [Fintype G]

theorem ip_add_left (u v w : G → ℂ) : ip (fun x => u x + v x) w = ip u w + ip v w := by
  unfold ip; rw [← mul_add, ← Finset.sum_add_distrib]; congr 1
  apply Finset.sum_congr rfl; intro x _; ring

theorem ip_add_right (u v w : G → ℂ) : ip u (v + w) = ip u v + ip u w := by
  unfold ip; rw [← mul_add, ← Finset.sum_add_distrib]; congr 1
  apply Finset.sum_congr rfl; intro x _; simp only [Pi.add_apply]; ring

theorem irr_char {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h; exact ⟨V, hV⟩

theorem char_class {χ : G → ℂ} (h : IsChar χ) : IsClass χ := (_root_.GlobalTheory.charDec G χ).2.2.1 h

theorem ip_irr_char_nat {α A : G → ℂ} (hα : IsIrr α) (hA : IsChar A) : ∃ c : ℕ, ip α A = c := by
  obtain ⟨L, hL, rfl⟩ := (_root_.GlobalTheory.charDec G A).1 hA
  clear hA
  induction L with
  | nil => exact ⟨0, by simp [ip]⟩
  | cons ρ L ih =>
    obtain ⟨c, hc⟩ := ih (fun r hr => hL r (List.mem_cons_of_mem _ hr))
    have h1 := (_root_.GlobalTheory.GLq.ZOrth.zorth G α ρ hα (hL ρ (by simp))).2.2
    refine ⟨(if α = ρ then 1 else 0) + c, ?_⟩
    rw [List.sum_cons, ip_add_right, hc, h1]; split_ifs <;> simp

end general

section prod
variable {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]

theorem ip_prod_single (α A : G → ℂ) (β B : H → ℂ) :
    ip (fun p : G × H => α p.1 * β p.2) (fun p => A p.1 * B p.2) = ip α A * ip β B := by
  unfold ip
  rw [Fintype.card_prod, Fintype.sum_prod_type]
  simp only [Prod.fst_inv, Prod.snd_inv]
  have e : ∀ x y, α x * β y * (A x⁻¹ * B y⁻¹) = (α x * A x⁻¹) * (β y * B y⁻¹) := by intros; ring
  simp only [e]
  rw [show ((Fintype.card G : ℂ))⁻¹ * (∑ x, α x * A x⁻¹) * (((Fintype.card H : ℂ))⁻¹ * ∑ y, β y * B y⁻¹) =
    ((Fintype.card G : ℂ))⁻¹ * ((Fintype.card H : ℂ))⁻¹ * ((∑ x, α x * A x⁻¹) * ∑ y, β y * B y⁻¹) by ring,
    Finset.sum_mul_sum, Nat.cast_mul, mul_inv]

theorem ip_prod_list (R : List ((G → ℂ) × (H → ℂ))) (A : G → ℂ) (B : H → ℂ) :
    ip (fun p : G × H => (R.map fun k => k.1 p.1 * k.2 p.2).sum) (fun p => A p.1 * B p.2) =
      (R.map fun k => ip k.1 A * ip k.2 B).sum := by
  induction R with
  | nil => simp [ip]
  | cons k R ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ip_add_left (fun p : G × H => k.1 p.1 * k.2 p.2), ih, ip_prod_single]

theorem sum_nat_ne_zero (R : List ((G → ℂ) × (H → ℂ))) (A : G → ℂ) (B : H → ℂ)
    (hR : ∀ k ∈ R, IsIrr k.1 ∧ IsIrr k.2) (hA : IsChar A) (hB : IsChar B) :
    ∃ N : ℕ, (R.map fun k => ip k.1 A * ip k.2 B).sum = N ∧
      ((∃ k ∈ R, ip k.1 A ≠ 0 ∧ ip k.2 B ≠ 0) → N ≠ 0) := by
  induction R with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons k R ih =>
    obtain ⟨N, hN, hN0⟩ := ih (fun r hr => hR r (List.mem_cons_of_mem _ hr))
    obtain ⟨c, hc⟩ := ip_irr_char_nat (hR k (by simp)).1 hA
    obtain ⟨d, hd⟩ := ip_irr_char_nat (hR k (by simp)).2 hB
    refine ⟨c * d + N, by simp [List.sum_cons, hN, hc, hd], ?_⟩
    rintro ⟨k', hk', h1, h2⟩
    rcases List.mem_cons.1 hk' with rfl | hk'
    · rw [hc] at h1; rw [hd] at h2
      have hc0 : c ≠ 0 := by rintro rfl; simp at h1
      have hd0 : d ≠ 0 := by rintro rfl; simp at h2
      have := Nat.mul_ne_zero hc0 hd0; omega
    · have := hN0 ⟨k', hk', h1, h2⟩; omega

end prod

section lists
variable {g : ℕ} [Fact g.Prime]

theorem degL_append (L₁ L₂ : List (Pc g)) : degL (L₁ ++ L₂) = degL L₁ + degL L₂ := by
  simp [degL, List.map_append, List.sum_append]

theorem class_hcL (L : List (Pc g)) (hL : ∀ p ∈ L, IsChar p.2) : IsClass (hcL L (degL L)) :=
  char_class (_root_.GlobalTheory.gl_list_product_perm_char g L L (degL L) rfl hL).1

theorem char_hcL (L : List (Pc g)) (hL : ∀ p ∈ L, IsChar p.2) : IsChar (hcL L (degL L)) :=
  (_root_.GlobalTheory.gl_list_product_perm_char g L L (degL L) rfl hL).1

theorem hcL_append (L₁ L₂ : List (Pc g)) (h : ∀ p ∈ L₁ ++ L₂, IsChar p.2) (n : ℕ)
    (hn : n = degL L₁ + degL L₂) :
    hcL (L₁ ++ L₂) n = hc (degL L₁) (degL L₂) (hcL L₁ (degL L₁)) (hcL L₂ (degL L₂)) n := by
  induction L₁ generalizing n with
  | nil =>
    have h2 : ∀ p ∈ L₂, IsChar p.2 := fun p hp => h p (by simpa using hp)
    change n = 0 + degL L₂ at hn
    rw [Nat.zero_add] at hn; subst hn
    exact ((_root_.GlobalTheory.GLq.HcRing.main g (degL L₂) 0 0 (degL L₂) (hcL L₂ (degL L₂)) (fun _ => 1) (fun _ => 1)
      (class_hcL L₂ h2) (fun _ _ => rfl) (fun _ _ => rfl)).2.2.1).symm
  | cons p L₁ ih =>
    have hp : IsChar p.2 := h p (by simp)
    have h1 : ∀ q ∈ L₁, IsChar q.2 := fun q hq => h q (by simp [hq])
    have h2 : ∀ q ∈ L₂, IsChar q.2 := fun q hq => h q (by simp [hq])
    have h12 : ∀ q ∈ L₁ ++ L₂, IsChar q.2 := fun q hq => h q (by simp at hq ⊢; tauto)
    have e1 := degL_append L₁ L₂
    have e2 : degL (p :: L₁) = p.1 + degL L₁ := by simp [degL]
    rw [List.cons_append, hcL_cons, hcL_cons, ih h12 (degL (L₁ ++ L₂)) e1, e1, e2]
    exact ((_root_.GlobalTheory.GLq.HcRing.main g p.1 (degL L₁) (degL L₂) n p.2 (hcL L₁ (degL L₁)) (hcL L₂ (degL L₂))
      (char_class hp) (class_hcL L₁ h1) (class_hcL L₂ h2)).1 (by omega)).symm

end lists

theorem exists_cusp_list (g : ℕ) [Fact g.Prime] (n : ℕ) (χ : Gn g n → ℂ) (hχ : IsIrr χ) :
    ∃ L : List (Pc g), (∀ p ∈ L, IsCusp p.2) ∧ degL L = n ∧ ip χ (hcL L n) ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hcls : IsClass χ := char_class (irr_char hχ)
  have hself : ip χ χ = 1 := by simpa using (_root_.GlobalTheory.GLq.ZOrth.zorth _ χ χ hχ hχ).2.2
  by_cases hn : n = 0
  · subst hn
    have hsub : ∀ x : Gn g 0, x = 1 := fun x => Units.ext (Matrix.ext fun i _ => i.elim0)
    have hu : (Finset.univ : Finset (Gn g 0)) = {1} := by ext x; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]; exact hsub x
    have hcard : Fintype.card (Gn g 0) = 1 := by rw [← Finset.card_univ, hu]; simp
    have hc1 : ∀ f : Gn g 0 → ℂ, ip χ f = χ 1 * f 1 := by
      intro f; unfold ip; rw [hcard, hu]; simp
    refine ⟨[], by simp, rfl, ?_⟩
    rw [hcL_nil, hc1]; rw [hc1] at hself
    simp only [mul_one]; intro h0; rw [h0] at hself; simp at hself
  · by_cases hcu : IsCusp χ
    · refine ⟨[⟨n, χ⟩], by simpa using hcu, by simp [degL], ?_⟩
      have e : hcL [(⟨n, χ⟩ : Pc g)] n = χ := by
        rw [hcL_cons]
        exact (_root_.GlobalTheory.GLq.HcRing.main g n 0 0 n χ (fun _ => 1) (fun _ => 1) hcls (fun _ _ => rfl)
          (fun _ _ => rfl)).2.2.2
      rw [e, hself]; exact one_ne_zero
    · have hne : ∃ a, 0 < a ∧ a < n ∧ res a (n - a) χ 1 1 ≠ 0 := by
        by_contra hc; push_neg at hc
        exact hcu ⟨Nat.pos_of_ne_zero hn, hχ, fun a h1 h2 => hc a h1 h2⟩
      obtain ⟨a, ha0, han, hres⟩ := hne
      generalize hb : n - a = b at hres
      have hnab : n = a + b := by omega
      obtain ⟨R, hR, hRes⟩ := (_root_.GlobalTheory.GLq.HCChar.hc_isChar_and_res_decomp g a b n hnab).2 χ (irr_char hχ)
      obtain ⟨k, hk⟩ : ∃ k, k ∈ R := by
        rcases R with _ | ⟨k, R⟩
        · exact absurd (by simpa using hRes 1 1) hres
        · exact ⟨k, by simp⟩
      obtain ⟨L₁, hL₁c, hL₁d, hL₁⟩ := ih a han k.1 (hR k hk).1
      obtain ⟨L₂, hL₂c, hL₂d, hL₂⟩ := ih b (by omega) k.2 (hR k hk).2
      have hch : ∀ p ∈ L₁ ++ L₂, IsChar p.2 := by
        intro p hp
        rcases List.mem_append.1 hp with h | h
        exacts [irr_char (hL₁c p h).2.1, irr_char (hL₂c p h).2.1]
      refine ⟨L₁ ++ L₂, fun p hp => ?_, ?_, ?_⟩
      · rcases List.mem_append.1 hp with h | h
        exacts [hL₁c p h, hL₂c p h]
      · rw [degL_append]; omega
      · subst hL₁d; subst hL₂d
        have hc1 : IsChar (hcL L₁ (degL L₁)) := char_hcL L₁ fun p hp => hch p (by simp [hp])
        have hc2 : IsChar (hcL L₂ (degL L₂)) := char_hcL L₂ fun p hp => hch p (by simp [hp])
        rw [hcL_append L₁ L₂ hch n hnab]
        have e : ip χ (hc (degL L₁) (degL L₂) (hcL L₁ (degL L₁)) (hcL L₂ (degL L₂)) n) =
            ip (fun p : Gn g (degL L₁) × Gn g (degL L₂) => (R.map fun k => k.1 p.1 * k.2 p.2).sum)
              (fun p => hcL L₁ (degL L₁) p.1 * hcL L₂ (degL L₂) p.2) := by
          rw [← funext fun p : Gn g (degL L₁) × Gn g (degL L₂) => hRes p.1 p.2]
          exact _root_.GlobalTheory.GLq.FrobRecHC.hcT_adjoint g _ _ n hnab χ (fun x y => hcL L₁ (degL L₁) x * hcL L₂ (degL L₂) y) hcls
        rw [e, ip_prod_list]
        obtain ⟨N, hN, hN0⟩ := sum_nat_ne_zero R _ _ hR hc1 hc2
        rw [hN]; exact_mod_cast hN0 ⟨k, hk, hL₁, hL₂⟩

end GlobalTheory.GLq.SuppCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHwFonCmpTies
section
namespace GlobalTheory.HWL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem exists_hw_fon_cmp_ties : GlobalTheory.Published.BhattScholzeCrystallineLattices →
    ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)),
      (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) →
      ∃ (H : HWOf L) (F : FonOf L A H), Nonempty (CmpOf L A H F) ∧ Nonempty (Formalism.MainNotions.LocalSituation.Ties L A H F) := by
  intro hBS L A hT
  obtain ⟨H, F, hC⟩ := _root_.GlobalTheory.HWL.exists_hwOf_fonOf_cmpOf L A hT (fun l _ => _root_.GlobalTheory.WachLattice.main hBS l (L l) (A l) (hT l))
  exact ⟨H, F, hC, ⟨⟨fun l _ => Classical.choice (_root_.GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l (L l) (A l) (hT l))⟩⟩⟩

end GlobalTheory.HWL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectivePushoutOfPrismCover
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.BSP.cover_po_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B C : Obj l ↥(OL K)) (h : Hom B C), Cover h → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q),
    ∃ (Q' : Obj l ↥(OL K)) (h' : Hom Q Q') (a' : Hom C Q'), a'.comp h = h'.comp a ∧ Function.Injective h'.f := by
  intro l _ K bk d S B C h hc Q a
  obtain ⟨Q', a', h', hpo⟩ := hc.stable.po Q a
  have hc' : Cover h' := (_root_.GlobalTheory.BSP.stable_cover_of_isPO l _ B C Q Q' h a a' h' hpo).2 hc
  exact ⟨Q', h', a', hpo.comm, (_root_.GlobalTheory.BSP.cover_injective_and_descent l _ Q Q' h' hc').1⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKernelVectorMemOEOfFrobeniusStableStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kernel_vector_mem_OE_of_frobenius_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y A : Matrix (Fin d) (Fin d) (Cb l)), A.det ≠ 0 → (∀ i j, A i j ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l))) → Y.map (frobenius (Cb l) l) = Y * A → (∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (Cb l), IsUnit R ∧ R * Y.map (autCb l (galTilt l (g : GQ l))) = Y) → Y.det = 0 → ∃ v : Fin d → Cb l, v ≠ 0 ∧ (∀ i, v i ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l))) ∧ Y.mulVec v = 0 := by
  first | exact @GlobalTheory.BSP.exists_ker_vector_mem_OE | exact GlobalTheory.BSP.exists_ker_vector_mem_OE | (intros; apply GlobalTheory.BSP.exists_ker_vector_mem_OE <;> assumption)
end

