module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinInfGaloisActsThroughDescentDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0204
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0554
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusPotentialCocycleClass
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalPot

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G]

theorem inclL_smul (P : PhiMod O K l e a ι) (r : OA l O) (d : ι → OA l O) :
    inclL t ϖ P (r • d) = inclO l O r • inclL t ϖ P d := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  exact congrArg _ (funext fun i => map_mul _ _ _)

theorem isCrisVal_add {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} {w w' : ι → OW l O} {b b' : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) (h' : IsCrisVal t ϖ P jB w' b') :
    IsCrisVal t ϖ P jB (w + w') (b + b') := by
  obtain ⟨m, c, hm, h1, h2⟩ := h
  obtain ⟨m', c', hm', h1', h2'⟩ := h'
  refine ⟨m * m', m' • c + m • c', by rw [map_mul]; exact hm.mul hm', ?_, ?_⟩
  · rw [map_add (f := _), inclL_smul, inclL_smul, ← h1, ← h1', map_mul, smul_add, mul_smul, mul_smul,
      smul_comm (inclO l O m) (inclO l O m') w]
  · have e1 : (fun i => toB l O ((m' • c + m • c') i)) =
        toB l O m' • (fun i => toB l O (c i)) + toB l O m • (fun i => toB l O (c' i)) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul]
    rw [e1, map_add (f := _), map_smul, map_smul, ← h2, ← h2', map_mul, smul_add, mul_smul, mul_smul,
      smul_comm (toB l O m) (toB l O m') b]

theorem isCrisVal_zero {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} : IsCrisVal t ϖ P jB 0 0 :=
  ⟨1, 0, by rw [map_one]; exact isUnit_one, by rw [smul_zero, map_zero], by
    rw [smul_zero]
    have e0 : (fun i => toB l O ((0 : ι → OA l O) i)) = 0 := funext fun i => map_zero (toB l O)
    rw [e0, map_zero]⟩

theorem isCrisVal_nsmul {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} {w : ι → OW l O} {b : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) (n : ℕ) : IsCrisVal t ϖ P jB (n • w) (n • b) := by
  induction n with
  | zero => rw [zero_smul, zero_smul]; exact isCrisVal_zero
  | succ n ih => rw [succ_nsmul, succ_nsmul]; exact isCrisVal_add ih h

variable [TameDescentExponentData K l e a] {s : G →* GQ l} {η H : ℕ} {D : BKDat O K l e a ι η H} {T : LocLat G ℚ_[l] K O}

theorem isPotential_add (R : GalDat t ϖ s D T) {y y' : Vec K a ι} {b b' : TW (OB l O) T}
    (h : R.IsPotential y b) (h' : R.IsPotential y' b') : R.IsPotential (y + y') (b + b') := by
  obtain ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨hy', m₀', σ', b₀', h1', h2', h3', h4', h5'⟩ := h'
  refine ⟨add_mem hy hy', m₀ + m₀', σ + σ', b₀ + b₀', ?_, add_mem h2 h2', ?_, ?_, ?_⟩
  · change _ = toW t ϖ D.toPhiMod (⟨y, hy⟩ + ⟨y', hy'⟩)
    rw [map_add (f := _), map_add (f := _), ← h1, ← h1']
    abel
  · rw [Submodule.coe_add, map_add (f := _), map_add (f := _), h3, h3']
  · rw [map_add (f := _)]
    exact isCrisVal_add h4 h4'
  · rw [h5, h5', map_add (f := _), map_add (f := _)]
    abel

theorem isPotential_nsmul (R : GalDat t ϖ s D T) {y : Vec K a ι} {b : TW (OB l O) T}
    (h : R.IsPotential y b) (n : ℕ) : R.IsPotential (n • y) (n • b) := by
  obtain ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, h5⟩ := h
  refine ⟨(ME D.toPhiMod).nsmul_mem hy n, n • m₀, n • σ, n • b₀, ?_, D.desc.inv.nsmul_mem h2 n, ?_, ?_, ?_⟩
  · change _ = toW t ϖ D.toPhiMod (n • ⟨y, hy⟩)
    rw [map_nsmul, map_nsmul, ← h1, smul_sub]
  · show D.conn (n • σ.1) = _
    rw [map_nsmul, map_nsmul, h3]
  · rw [map_nsmul]
    exact isCrisVal_nsmul h4 n
  · rw [h5, map_nsmul, map_nsmul, nsmul_sub]

theorem isCobOf_pow {b : TW (OB l O) T} {c : G → T.V} (h : IsCobOf s T b c) (k : ℕ) :
    IsCobOf s T ((l ^ k : ℕ) • b) ((l : K) ^ k • c) := by
  intro g n x hx
  have h1 := h g (n + k) x (by rw [hx, Pi.smul_apply, smul_smul, pow_add])
  rw [h1, map_nsmul, ← nsmul_sub, ← Nat.cast_smul_eq_nsmul O, smul_smul, Nat.cast_pow, pow_add]

theorem exists_isEps : ∃ ε : OCb l, IsEps ε := by
  obtain ⟨ε, h1, h2⟩ := GlobalTheory.MemLoc.Model.exists_isEps l
  exact ⟨ε, h1, (frobeniusEquiv (Per.Fl l) l).symm ε, frobeniusEquiv_symm_pow_p _ _ _, h2⟩

theorem isUnit_toB_muOf {ε : OCb l} (hε : IsEps ε) (n : ℕ) :
    IsUnit (toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n))) := by
  obtain ⟨δ, hδ, -⟩ := hε.2
  have hu : IsUnit (acrisToBcris l (ainfToAcris l (muOf ε))) :=
    ((_root_.GlobalTheory.MuOfEps.main l).2 ε δ hε hδ).2.2.2.1
  have e1 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n)) =
      (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
        (acrisToBcris l (ainfToAcris l (muOf ε)) ^ n) := by
    simp only [toB, toOB, toOCr, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.includeRight_apply, map_pow, Algebra.TensorProduct.tmul_pow, one_pow]
  rw [e1]
  exact (hu.pow n).map _

theorem actB_mul (s : G →* GQ l) (T : LocLat G ℚ_[l] K O) (g g' : G) (z : TW (OB l O) T) :
    actB s T (g * g') z = actB s T g (actB s T g' z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul w x =>
    have hw : galOB O (s (g * g')) w = galOB O (s g) (galOB O (s g') w) := by
      rw [map_mul]
      induction w using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add u v hu hv => simp only [map_add (f := _), hu, hv]
      | tmul o c =>
        simp only [galOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        exact congrArg (fun z : Per.Bcris l => o ⊗ₜ[ℤ_[l]] z) ((GlobalTheory.MemLoc.ActLaws.act_laws l).1 _ _ c)
    have hx : T.actT (g * g') x = T.actT g (T.actT g' x) :=
      Subtype.ext (LinearMap.congr_fun (map_mul T.ρ g g') (x : T.V))
    simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, hw, hx]

theorem sub_mem_B1T {s : G →* GQ l} {T : LocLat G ℚ_[l] K O} {b b' ξ : TW (OB l O) T} {c c' : G → T.V}
    (x : ↥T.L.T) (hb : IsCobOf s T b c) (hb' : IsCobOf s T b' c') (hξ : ∀ g, actB s T g ξ = ξ)
    (h : b - b' = ξ - (1 : OB l O) ⊗ₜ[O] x) : c - c' ∈ latticeCoboundaries T.L := by
  refine ⟨-(x : T.V), neg_mem x.2, funext fun g => ?_⟩
  obtain ⟨n₁, hn₁⟩ := _root_.GlobalTheory.LatPow.pow_smul_mem l O K G T (c g)
  obtain ⟨n₂, hn₂⟩ := _root_.GlobalTheory.LatPow.pow_smul_mem l O K G T (c' g)
  obtain ⟨x₁, hx₁⟩ := hn₁ (max n₁ n₂) (le_max_left _ _)
  obtain ⟨x₂, hx₂⟩ := hn₂ (max n₁ n₂) (le_max_right _ _)
  have e1 := hb g _ x₁ hx₁
  have e2 := hb' g _ x₂ hx₂
  have hact : actB s T g ((1 : OB l O) ⊗ₜ[O] x) = (1 : OB l O) ⊗ₜ[O] (T.actT g x) := by
    rw [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]
  have hbb : b = b' + (ξ - (1 : OB l O) ⊗ₜ[O] x) := by rw [← h]; abel
  have e3 : (1 : OB l O) ⊗ₜ[O] (x₁ - x₂) =
      (1 : OB l O) ⊗ₜ[O] (((l : O) ^ max n₁ n₂) • (x - T.actT g x)) := by
    rw [TensorProduct.tmul_sub, e1, e2, ← smul_sub, TensorProduct.tmul_smul, TensorProduct.tmul_sub, ← hact,
      hbb, map_add, map_sub, hξ]
    congr 1
    abel
  have e4 := congrArg (fun z : ↥T.L.T => (z : T.V)) (_root_.GlobalTheory.TensorOneInj.tensor_one_injective l O K G T e3)
  simp only [Submodule.coe_sub, Submodule.coe_smul] at e4
  have eO : ∀ v : T.V, ((l : O) ^ max n₁ n₂) • v = (l : K) ^ max n₁ n₂ • v := fun v => by
    rw [← algebraMap_smul K ((l : O) ^ max n₁ n₂) v, map_pow, map_natCast]
  rw [hx₁, hx₂, ← smul_sub, eO] at e4
  have hl0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hl.out.ne_zero)
  have e5 := (smul_right_inj (pow_ne_zero (max n₁ n₂) hl0)).1 e4
  simp only [LinearMap.restrictScalars_apply, Pi.sub_apply]
  rw [e5]
  change T.ρ g (-(x : T.V)) - (-(x : T.V)) = (x : T.V) - T.ρ g (x : T.V)
  rw [map_neg]
  abel

section Ql

variable [TameDescentExponentData K l e a] {η H : ℕ} {D : BKDat O K l e a ι η H} {T : LocLat (Gl l) ℚ_[l] K O}

theorem exists_isCrisVal (R : GalDat t ϖ (sQ l) D T) {y : Vec K a ι} (hyY : y ∈ D.Y) (hy : y ∈ ME D.toPhiMod)
    (m₀ : ι → OW l O) (h : phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩) :
    ∃ b₀, IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) b₀ := by
  obtain ⟨ε, hε⟩ := exists_isEps (l := l)
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨c, hc⟩ := (_root_.GlobalTheory.BKGal.LiftStep.mu_pow_smul_mem l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ ⟨y, hy⟩
    hyY.1 m₀ h).2
  obtain ⟨u, hu⟩ := isUnit_toB_muOf (O := O) hε (H + η)
  refine ⟨(↑u⁻¹ : OB l O) • R.jB (fun i => toB l O (c i)), (1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ (H + η)), c,
    ⟨u, hu⟩, hc.symm, ?_⟩
  rw [← hu, smul_smul, Units.mul_inv, one_smul]

theorem fix_of_horiz (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (hinv : σ.1 ∈ D.desc.inv)
    (hc : D.conn σ.1 = 0) (g : Gl l) :
    actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) = R.jB (toBcris t ϖ D.toPhiMod σ) := by
  obtain ⟨h, k, rfl, hh, γ, hk⟩ := _root_.GlobalTheory.TameCoverGen.main l a e O K t ϖ g
  have hx := _root_.GlobalTheory.horiz_eq_xi_red O K l e a ι D.toPhiMod σ.1 hc
  have hm : D.xi (red σ.1) ∈ D.MMl := by rw [← hx]; exact σ.2
  have hσ : (⟨D.xi (red σ.1), hm⟩ : D.MMl) = σ := Subtype.ext hx.symm
  have h2 := R.horiz h hh (red σ.1) hm
  rw [hσ] at h2
  have h3 := _root_.GlobalTheory.TameAct.main l a e O K t ϖ ι D.toPhiMod T R.I R.jB D.desc R.cmp R.desc k γ hk σ σ (hinv γ).symm
  rw [actB_mul, h3, h2]

end Ql

theorem potential_class : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), (∀ y ∈ D.Y, ∃ b, R.IsPotential y b) ∧ (∀ y c c', R.ClassOf y c → R.ClassOf y c' → c - c' ∈ latticeCoboundaries T.L) ∧ (∀ y c (k : ℕ), R.ClassOf y c → R.ClassOf ((l : K) ^ k • y) ((l : K) ^ k • c)) ∧ ∀ y c, ∀ m ∈ D.Minv, R.ClassOf y c → R.ClassOf (y + (D.phi m - m)) c := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (K := K) (l := l) (e := e) (a := a)
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hyY
    have hy : y ∈ ME D.toPhiMod := BKDat.mem_invE_of_mem_Y hyY
    obtain ⟨m₀, hm₀⟩ := R.I.exists_phiW_sub (toW t ϖ D.toPhiMod ⟨y, hy⟩)
    have hYl : y ∈ D.Yl := D.desc.mem_Yl_iff.2 ⟨0, by rw [pow_zero, one_smul]; exact hyY⟩
    obtain ⟨⟨σ, hσ, hinv, hconn, -⟩, -⟩ := _root_.GlobalTheory.BK.BKDat.Mon_mem_range_Lc O K l e a ι η H D y hYl
    obtain ⟨b₀, hb₀⟩ := exists_isCrisVal R hyY hy m₀ hm₀
    exact ⟨_, hy, m₀, ⟨σ, hσ⟩, b₀, hm₀, hinv, hconn, hb₀, rfl⟩
  · rintro y c c' ⟨b, ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, h5⟩, hc⟩ ⟨b', ⟨hy', m₀', σ', b₀', h1', h2', h3', h4', h5'⟩, hc'⟩
    have hT : m₀ - m₀' ∈ Treal t ϖ D.toPhiMod := by
      rw [mem_Treal, map_sub]
      exact sub_eq_sub_iff_sub_eq_sub.1 (h1.trans h1'.symm)
    obtain ⟨x, hx⟩ : m₀ - m₀' ∈ LinearMap.range R.I.ofT := by rw [R.I.range_ofT]; exact hT
    have hphi : phiW t ϖ D.toPhiMod m₀' + R.I.ofT x = phiW t ϖ D.toPhiMod m₀ := by
      rw [hx, ← mem_Treal.1 hT, map_sub]
      abel
    have hof := ((_root_.GlobalTheory.CrisComparison.main l a e O K t ϖ ι D.toPhiMod T R.I).2 R.jB R.cmp).2.2.2.1 x
    have hsum := isCrisVal_add h4' hof
    rw [hphi] at hsum
    have hb₀ : b₀ = b₀' + (1 : OB l O) ⊗ₜ[O] x := UnitModel.isCrisVal_unique t ϖ h4 hsum
    refine sub_mem_B1T x hc hc' (fix_of_horiz R (σ - σ') (sub_mem h2 h2') ?_) ?_
    · show D.conn (σ.1 - σ'.1) = 0
      rw [map_sub, h3, h3', sub_self]
    · rw [h5, h5', hb₀, map_sub, map_sub]
      abel
  · rintro y c k ⟨b, hb, hc⟩
    refine ⟨(l ^ k : ℕ) • b, ?_, isCobOf_pow hc k⟩
    have := isPotential_nsmul R hb (l ^ k)
    rwa [← Nat.cast_smul_eq_nsmul K, Nat.cast_pow] at this
  · rintro y c m hm ⟨b, hb, hc⟩
    exact ⟨b + 0, isPotential_add R hb (UnitModel.isPotential_phi_sub t ϖ R hm), by rwa [add_zero]⟩

end GlobalTheory.GalPot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisDescentDatumAndStable
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.GalDescent

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G] [TameDescentExponentData K l e a]
  {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}

def colMat (w : ι → Vec K a ι) : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => Matrix.of fun i j => w j τ i


omit [NeZero e] in
theorem matAct_eq_sum (γ : TameGal K l e a) (w : ι → Vec K a ι) (v : Vec K a ι) :
    Descent.matAct γ (colMat w) v = ∑ j, ringAct γ (fun σ => v σ j) • w j := by
  ext τ i : 2
  simp only [Descent.matAct_apply, colMat, Finset.sum_apply, Pi.smul_apply', ringAct_apply, Matrix.mulVec,
    dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem bas_mem_ME (j : ι) : (bas j : Vec K a ι) ∈ ME P := mem_ME_of_mem_M (P.bas_mem_M j)

theorem matAct_mem_ME (γ : TameGal K l e a) (w : ι → ME P) (v : ME P) :
    Descent.matAct γ (colMat fun j => (w j).1) v.1 ∈ ME P := by
  rw [matAct_eq_sum]
  exact Submodule.sum_mem _ fun j _ => P.smul_tot_mem_Mext
    (fun τ => (rot_A.invE).ringAct_mem γ (fun σ => mem_tot.1 v.2 σ j) τ) (w j).2

theorem covers_inv {h : GQ l} {γ : TameGal K l e a} (hc : Covers K t ϖ h γ) : Covers K t ϖ h⁻¹ γ⁻¹ := by
  intro f f' hf
  have h1 : galOA O h (ϖ.iTot t K f') = ϖ.iTot t K f := hc f' f fun τ => by
    rw [show (fun σ => ((f' σ : A O K) : K⟦X⟧)) = ringAct γ⁻¹ (fun σ => (f σ : K⟦X⟧)) from funext hf,
      ← AlgHom.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgHom.one_apply]
  apply inclO_injective
  rw [← h1, ← galOW_inclO, ← galOW_inclO, ← galOW_mul, inv_mul_cancel, galOW_one]

theorem toW_sum_smul (c : ι → ZMod a → invE l e (A O K)) (w : ι → ME P)
    (hv : (∑ j, (fun τ => (c j τ : K⟦X⟧)) • (w j).1) ∈ ME P) :
    toW t ϖ P ⟨_, hv⟩ = ∑ j, ϖ.iW t K (c j) • toW t ϖ P (w j) := by
  have : (⟨_, hv⟩ : ME P) = ∑ j, (⟨(fun τ => (c j τ : K⟦X⟧)) • (w j).1,
      P.smul_tot_mem_Mext (fun τ => (c j τ).2) (w j).2⟩ : ME P) := Subtype.ext (by
    rw [Submodule.coe_sum])
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, map_sum]
  exact Finset.sum_congr rfl fun j _ => toW_smul t ϖ P (c j) (w j) _ fun τ => rfl

theorem act_toW_sum (I : Ident t ϖ P T) {s : GQ l} {g : G} {γ : TameGal K l e a} (hc : Covers K t ϖ s γ)
    (w : ι → ME P) (hw : ∀ j, I.act s g (toW t ϖ P ⟨bas j, bas_mem_ME j⟩) = toW t ϖ P (w j)) (v : ME P)
    (hv : Descent.matAct γ (colMat fun j => (w j).1) v.1 ∈ ME P) :
    I.act s g (toW t ϖ P v) = toW t ϖ P ⟨_, hv⟩ := by
  obtain ⟨v, hvm⟩ := v
  let f : ι → ZMod a → invE l e (A O K) := fun j τ => ⟨v τ j, mem_tot.1 hvm τ j⟩
  let f' : ι → ZMod a → invE l e (A O K) := fun j τ =>
    ⟨ringAct γ (fun σ => v σ j) τ, (rot_A.invE).ringAct_mem γ (fun σ => mem_tot.1 hvm σ j) τ⟩
  have e1 : (∑ j, (fun τ => (f j τ : K⟦X⟧)) • ((⟨bas j, bas_mem_ME j⟩ : ME P) : Vec K a ι)) ∈ ME P := by
    rw [← eq_sum_bas v]; exact hvm
  have e2 : (∑ j, (fun τ => (f' j τ : K⟦X⟧)) • (w j).1) ∈ ME P := by
    rw [← matAct_eq_sum]; exact hv
  have hv1 : toW t ϖ P ⟨v, hvm⟩ = toW t ϖ P ⟨_, e1⟩ := congrArg _ (Subtype.ext (eq_sum_bas v))
  have hv2 : toW t ϖ P ⟨_, hv⟩ = toW t ϖ P ⟨_, e2⟩ := congrArg _ (Subtype.ext (matAct_eq_sum γ _ v))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hv1, hv2, toW_sum_smul, toW_sum_smul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Ident.act_smul, hw, UnitModel.galOW_iW_of_covers t ϖ hc (f j) (f' j) fun τ => rfl]

theorem act_eq_of_covers (I : Ident t ϖ P T) (s : G →* GQ l)
    (hmul : ∀ k k' γ γ', Covers K t ϖ k γ → Covers K t ϖ k' γ' → Covers K t ϖ (k * k') (γ * γ'))
    (hone : ∀ k, Covers K t ϖ k 1 → k ∈ ϖ.GfieldInf a)
    (H1 : ∀ g : G, s g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (s g) g (toW t ϖ P v) = toW t ϖ P v)
    {g g' : G} {γ : TameGal K l e a} (hc : Covers K t ϖ (s g) γ) (hc' : Covers K t ϖ (s g') γ) (v : ME P) :
    I.act (s g) g (toW t ϖ P v) = I.act (s g') g' (toW t ϖ P v) := by
  have h1 : s (g'⁻¹ * g) ∈ ϖ.GfieldInf a := hone _ (by
    rw [map_mul, map_inv, ← inv_mul_cancel γ]
    exact hmul _ _ _ _ (covers_inv hc') hc)
  have h2 : g = g' * (g'⁻¹ * g) := (mul_inv_cancel_left g' g).symm
  rw [h2, map_mul, Ident.act_mul, H1 _ h1]

theorem exists_desc (I : Ident t ϖ P T) (s : G →* GQ l)
    (hex : ∀ γ : TameGal K l e a, ∃ g : G, Covers K t ϖ (s g) γ)
    (hmul : ∀ k k' γ γ', Covers K t ϖ k γ → Covers K t ϖ k' γ' → Covers K t ϖ (k * k') (γ * γ'))
    (hone : ∀ k, Covers K t ϖ k 1 → k ∈ ϖ.GfieldInf a)
    (H1 : ∀ g : G, s g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (s g) g (toW t ϖ P v) = toW t ϖ P v)
    (H2 : ∀ (g : G) (γ : TameGal K l e a), Covers K t ϖ (s g) γ → ∀ v : ME P, v.1 ∈ P.M →
      ∃ v' : ME P, v'.1 ∈ P.M ∧ I.act (s g) g (toW t ϖ P v) = toW t ϖ P v') :
    ∃ Δ : Descent P, IsGalDesc s I Δ := by
  choose gOf hgOf using hex
  choose w hwM hw using fun γ j => H2 (gOf γ) γ (hgOf γ) ⟨bas j, bas_mem_ME j⟩ (P.bas_mem_M j)
  have hact : ∀ γ (v : ME P), I.act (s (gOf γ)) (gOf γ) (toW t ϖ P v) =
      toW t ϖ P ⟨_, matAct_mem_ME γ (w γ) v⟩ :=
    fun γ v => act_toW_sum I (hgOf γ) (w γ) (hw γ) v _
  have hone' : ∀ j, (w 1 j).1 = bas j := fun j => congrArg Subtype.val (toW_injective t ϖ P
    ((hw 1 j).symm.trans (H1 _ (hone _ (hgOf 1)) _)))
  have hmul' : ∀ γ δ j, (w (γ * δ) j).1 = Descent.matAct γ (colMat fun k => (w γ k).1) (w δ j).1 :=
    fun γ δ j => congrArg Subtype.val (toW_injective t ϖ P (show toW t ϖ P (w (γ * δ) j) =
        toW t ϖ P ⟨_, matAct_mem_ME γ (w γ) (w δ j)⟩ by
      have hc : Covers K t ϖ (s (gOf γ * gOf δ)) (γ * δ) := by
        rw [map_mul]; exact hmul _ _ _ _ (hgOf γ) (hgOf δ)
      rw [← hw, act_eq_of_covers I s hmul hone H1 (hgOf (γ * δ)) hc, map_mul, Ident.act_mul, hw, hact]))
  have hcomm : ∀ γ j, Descent.matAct γ (colMat fun k => (w γ k).1) (P.phi (bas j)) = P.phi (w γ j).1 :=
    fun γ j => by
      have e1 := hact γ ⟨P.phi (bas j), mem_ME_of_mem_L (P.phi_mem_L (P.bas_mem_M j))⟩
      rw [toW_phi t ϖ P (P.bas_mem_M j), Ident.act_phiW] at e1
      have e2 := toW_phi t ϖ P (hwM γ j)
      have e3 : I.act (s (gOf γ)) (gOf γ) (toW t ϖ P ⟨bas j, mem_ME_of_mem_M (P.bas_mem_M j)⟩) =
          toW t ϖ P ⟨(w γ j).1, mem_ME_of_mem_M (hwM γ j)⟩ := hw γ j
      rw [e3, ← e2] at e1
      exact congrArg Subtype.val (toW_injective t ϖ P e1).symm
  refine ⟨Descent.ofMatrix P (fun γ => colMat fun j => (w γ j).1) (fun γ τ i j => mem_tot.1 (hwM γ j) τ i)
    (fun τ => ?_) (fun γ δ τ => ?_) (fun γ τ => ?_), fun g γ hc v v' hv' => ?_⟩
  · ext i j
    simp only [colMat, Matrix.of_apply, hone', bas, Pi.single_apply, Matrix.one_apply]
  · ext i j
    simp only [colMat, Matrix.of_apply, hmul', Descent.matAct_apply, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Matrix.map_apply]
  · refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun (hcomm γ j) τ) i
    simp only [Descent.matAct_apply, PhiMod.phi_bas, Matrix.col_apply] at this
    simp only [PhiMod.phi_apply, Matrix.mulVec, dotProduct, frobV_apply] at this
    simpa only [colMat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply] using this
  · rw [act_eq_of_covers I s hmul hone H1 hc (hgOf γ) v, hact]
    exact congrArg _ (Subtype.ext hv'.symm)

theorem stable_of_desc (I : Ident t ϖ P T) (s : G →* GQ l) {Δ : Descent P} (hΔ : IsGalDesc s I Δ) {g : G}
    {γ : TameGal K l e a} (hc : Covers K t ϖ (s g) γ) : ∀ v ∈ LA t ϖ P, I.act (s g) g v ∈ LA t ϖ P := by
  have key : ∀ (r : OA l O) (d : ι → OA l O), inclL t ϖ P (r • d) = inclO l O r • inclL t ϖ P d := fun r d => by
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    exact congrArg _ (funext fun i => map_mul _ _ _)
  have hcol : ∀ j, inclL t ϖ P (Pi.single j 1) =
      toW t ϖ P ⟨P.phi (bas j), mem_ME_of_mem_L (P.phi_mem_L (P.bas_mem_M j))⟩ := fun j => by
    rw [toW_of_mx t ϖ P _ (Pi.single j 1) fun τ => ?_, inclL_apply]
    · congr 1
      ext1 j'
      by_cases h : j' = j
      · subst h; simp
      · simp [h]
    · show P.phi (bas j) τ = _
      rw [PhiMod.phi_bas]
      ext1 i
      simp only [Matrix.mulVec, dotProduct, Matrix.col_apply]
      rw [Finset.sum_eq_single j (fun x _ hx => by simp [Pi.single_apply, hx]) (by simp)]
      simp
  rintro _ ⟨c, rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pi_eq_sum_univ' c, map_sum, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [key, Ident.act_smul, galOW_inclO, hcol, hΔ g γ hc _ ⟨Δ.act γ (P.phi (bas j)),
    mem_ME_of_mem_L (Δ.act_mem_ext γ le_rfl rot_A (P.phi_mem_L (P.bas_mem_M j)))⟩ rfl]
  obtain ⟨c', hc'⟩ := toW_mem_LA t ϖ P (Δ.act_mem_ext γ le_rfl rot_A (P.phi_mem_L (P.bas_mem_M j)))
  rw [← hc', ← key]
  exact ⟨_, rfl⟩

theorem stable_of_factor (I : Ident t ϖ P T) (s : G →* GQ l) {Δ : Descent P} (hΔ : IsGalDesc s I Δ)
    {g g₁ g₂ : G} (hg : g = g₁ * g₂) {γ : TameGal K l e a} (hc : Covers K t ϖ (s g₂) γ)
    (h₁ : ∀ v ∈ LA t ϖ P, I.act (s g₁) g₁ v ∈ LA t ϖ P) : ∀ v ∈ LA t ϖ P, I.act (s g) g v ∈ LA t ϖ P := by
  subst hg
  intro v hv
  rw [map_mul, Ident.act_mul]
  exact h₁ _ (stable_of_desc I s hΔ hc v hv)

end GlobalTheory.BKGal.GalDescent

theorem gal_res_eq {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {ϖ : PiSys l e} {LL : FinExt l} [HasUnr a LL]
    [TameDescentExponentData ↥LL.1 l e a] {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod ↥(OL LL) ↥LL.1 l e a ι}
    {T : QLat LL} (I : Ident (thetaW a LL) ϖ P T) (x : ↥(GK (ϖ.field a))) (v : ι → OW l ↥(OL LL)) :
    Ident.gal (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) x v =
      I.act (sQ l (inclG (ϖ.field a) x)) (inclG (ϖ.field a) x) v := rfl

theorem coe_inclG {l : ℕ} [Fact l.Prime] (F : FinExt l) (x : ↥(GK F)) : sQ l (inclG F x) = x := rfl

theorem act_mem_LA_of_stable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {ϖ : PiSys l e} {LL : FinExt l}
    [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : PhiMod ↥(OL LL) ↥LL.1 l e a ι} {T : QLat LL} (I : Ident (thetaW a LL) ϖ P T)
    (hst : Ident.Stable (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)))
    (x : ↥(GK (ϖ.field a))) : ∀ v ∈ LA (thetaW a LL) ϖ P,
      I.act (sQ l (inclG (ϖ.field a) x)) (inclG (ϖ.field a) x) v ∈ LA (thetaW a LL) ϖ P := fun v hv => by
  have h := (hst x).1 v hv
  rwa [gal_res_eq] at h


open GlobalTheory.BKGal.GalDescent in
theorem GlobalTheory.BKGal.GalDescent.exists_galDesc_and_stable : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), (∀ g : Gl l, sQ l g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v) → (∀ (g : Gl l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ → ∀ v : ME P, v.1 ∈ P.M → ∃ v' : ME P, v'.1 ∈ P.M ∧ I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v') → (∃ Δ : Descent P, IsGalDesc (sQ l) I Δ) ∧ (Ident.Stable (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ g : Gl l, ∀ v ∈ LA (thetaW a LL) ϖ P, I.act (sQ l g) g v ∈ LA (thetaW a LL) ϖ P) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I H1 H2
  obtain ⟨c1, c2, c3, -, c5, c6, -⟩ := _root_.GlobalTheory.TameCover.main l a e ϖ LL
  have hmem : ∀ k : GQ l, k ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := fun k => by
    change k ∈ (⊥ : IntermediateField ℚ_[l] (Om l)).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    trivial
  have hex : ∀ γ : TameGal ↥LL.1 l e a, ∃ g : Gl l, Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ := fun γ => by
    obtain ⟨k, -, hk⟩ := c3 γ
    exact ⟨⟨k, hmem k⟩, hk⟩
  obtain ⟨Δ, hΔ⟩ := exists_desc I (sQ l) hex c5 (fun k hk => (c6 k).1 hk) H1 H2
  refine ⟨⟨Δ, hΔ⟩, fun hst g => ?_⟩
  choose hOf hhOf kOf hkOf hgOf using c1
  choose γOf hγOf using c2
  have e1 : g = inclG (ϖ.field a) ⟨hOf g, hhOf g⟩ * ⟨kOf g, hmem _⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact (hgOf g).trans (congrArg (· * kOf g) (coe_inclG (ϖ.field a) ⟨hOf g, hhOf g⟩).symm)
  exact stable_of_factor I (sQ l) hΔ e1 (hγOf _ (hkOf g)) (act_mem_LA_of_stable I hst _)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1ReductionIndexBoundDualStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H1_reduction_index_bound_of_tateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ Nat.card (QuotientCohomology LA _ hI) ∧ Nat.card (QuotientCohomology LA _ hI) ≤ C * Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) := by
  first | exact @GlobalTheory.BoundedIndex.h1_reduction_index_bounded | exact GlobalTheory.BoundedIndex.h1_reduction_index_bounded | (intros; apply GlobalTheory.BoundedIndex.h1_reduction_index_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOfCrystallineBreuilKisinFrameStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrys_of_crystallineBreuilKisinFrame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (F : Frame bk N d fun g => (ρ g).val), F.IsCr → IsCrys (P.PD K) (qRep ρ) := by
  first | (exact @GlobalTheory.CrTop.crys_of_frame) | (exact GlobalTheory.CrTop.crys_of_frame) | (intros; apply GlobalTheory.CrTop.crys_of_frame  <;> assumption)
end

