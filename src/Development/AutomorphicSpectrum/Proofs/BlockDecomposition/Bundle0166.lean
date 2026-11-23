module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0160
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltAdicComplete
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0163
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0157
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0161
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0165

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompatibleRootsLiftToTilt
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

section Adic

variable {R : Type*} [CommRing R]

theorem smodEq_span_pow_iff (π x y : R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {π} ^ n • (⊤ : Submodule R R))] ↔ π ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem eq_zero_of_forall_pow_dvd {π x : R} (h : IsHausdorff (Ideal.span {π}) R)
    (hx : ∀ n : ℕ, π ^ n ∣ x) : x = 0 :=
  h.haus x fun n => (smodEq_span_pow_iff π x 0 n).2 (by simpa using hx n)

theorem exists_limit_of_pow_dvd {π : R} (h : IsPrecomplete (Ideal.span {π}) R) (f : ℕ → R)
    (hf : ∀ n : ℕ, π ^ n ∣ f (n + 1) - f n) : ∃ L, ∀ n : ℕ, π ^ n ∣ f n - L :=
  _root_.UpperTheory.Reformulated.B.Yra6.main h f hf

theorem pow_pow_of_compatible {M : Type*} [Monoid M] {l : ℕ} {v : ℕ → M}
    (hv : ∀ i, v (i + 1) ^ l = v i) (i j : ℕ) : v (i + j) ^ l ^ j = v i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', pow_mul, ← add_assoc, hv, ih]

end Adic

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem sub_pow_pow (x y : A.A) (j : ℕ) : (x - y) ^ l ^ j = x ^ l ^ j - y ^ l ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, ih, pow_mul, pow_mul]
    exact map_sub A.frob _ _

theorem exists_limit_pow (b : ℕ → A.A) (hb : ∀ j, A.pi ∣ b (j + 1) ^ l - b j) (i : ℕ) :
    ∃ L, ∀ n : ℕ, A.pi ^ n ∣ b (i + n) ^ l ^ n - L := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  refine exists_limit_of_pow_dvd (π := A.pi) A.compl.toIsPrecomplete
    (fun n => b (i + n) ^ l ^ n) fun n => ?_
  have e : b (i + (n + 1)) ^ l ^ (n + 1) - b (i + n) ^ l ^ n
      = (b (i + n + 1) ^ l - b (i + n)) ^ l ^ n := by
    rw [sub_pow_pow, ← pow_mul, ← pow_succ', add_assoc]
  change A.pi ^ n ∣ b (i + (n + 1)) ^ l ^ (n + 1) - b (i + n) ^ l ^ n
  rw [e]
  exact (pow_dvd_pow _ (Nat.lt_pow_self hl).le).trans (pow_dvd_pow_of_dvd (hb _) _)

theorem exists_compatible_roots_of_sharp : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (u : ℕ → A.U),
    (∀ i, u (i + 1) ^ l = u i) →
    ∃ a : ℕ → A.A, (∀ i, a (i + 1) ^ l = a i) ∧ ∀ i, A.sharp (a i) = u i := by
  intro l _ A u hu
  obtain ⟨hsurj, hker⟩ := sharp_map_surjective_ker A
  choose b hb using fun j => hsurj (Ideal.Quotient.mk _ (u j))
  have hbd : ∀ j, A.pi ∣ b (j + 1) ^ l - b j := fun j => by
    rw [← Ideal.mem_span_singleton]
    rw [← hker, RingHom.mem_ker, map_sub, map_pow, hb, hb, ← map_pow, hu, sub_self]
  choose a ha using exists_limit_pow A b hbd
  have hA : IsHausdorff (Ideal.span {A.pi}) A.A := A.compl.toIsHausdorff
  have hroot : ∀ i, a (i + 1) ^ l = a i := fun i => by
    refine sub_eq_zero.1 (eq_zero_of_forall_pow_dvd hA fun n => ?_)
    have h1 : A.pi ^ n ∣ b (i + 1 + n) ^ l ^ (n + 1) - a (i + 1) ^ l := by
      rw [pow_succ, pow_mul]
      exact (ha (i + 1) n).trans (sub_dvd_pow_sub_pow _ _ l)
    have h2 : A.pi ^ n ∣ b (i + 1 + n) ^ l ^ (n + 1) - a i := by
      have := ha i (n + 1)
      rw [show i + (n + 1) = i + 1 + n by ring] at this
      exact (pow_dvd_pow _ (Nat.le_succ n)).trans this
    have := dvd_sub h2 h1
    simpa using this
  have hmod : ∀ i, A.pi ∣ a i - b i := fun i => by
    have h1 := ha i 1
    rw [pow_one, pow_one] at h1
    have := dvd_sub (hbd i) h1
    simpa using this
  have hl1 : ∀ i, (l : A.U) ∣ A.sharp (a i) - u i := fun i => by
    have h0 : A.aToU1 (a i) = A.aToU1 (b i) := by
      rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hker, Ideal.mem_span_singleton]
      exact hmod i
    rw [hb, sharpMap_eq] at h0
    have := Ideal.Quotient.eq.1 h0
    rwa [pow_one, Ideal.mem_span_singleton] at this
  refine ⟨a, hroot, fun i => sub_eq_zero.1 ?_⟩
  refine eq_zero_of_forall_pow_dvd (π := (l : A.U)) (_root_.GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U A).toIsHausdorff fun n => ?_
  have h1 := dvd_sub_pow_of_dvd_sub (hl1 (i + n)) n
  rw [← map_pow, pow_pow_of_compatible hroot, pow_pow_of_compatible hu] at h1
  exact (pow_dvd_pow _ (Nat.le_succ n)).trans h1

end GlobalTheory.CompanionTheory.Untilt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexHessianLogDehomogeniseStatement
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_hessian_log_dehomogenise : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U : Set (V d)) (b : α → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (b j) U) → (∀ z ∈ U, b j₀ z ≠ 0) → ∀ z ∈ U, cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z = cHess d (fun v => ((Real.log (1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2) : ℝ) : ℂ)) z := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.HessFrame.cHess_log_sum_normSq_eq | exact GlobalTheory.CompanionTheory.FSCrofton.HessFrame.cHess_log_sum_normSq_eq | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.HessFrame.cHess_log_sum_normSq_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexHessianLogFubiniStudy
section
noncomputable section

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton Filter Topology
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

variable {n : ℕ}

theorem hessLog_chain {k : ℝ → ℝ} {v : V n → ℝ} {x : V n} (hv : ContDiffAt ℝ 2 v x)
    (hk : ContDiffAt ℝ 2 k (v x)) (j c : Fin n) :
    wd n j (wdb n c (fun y => ((k (v y) : ℝ) : ℂ))) x =
      ((deriv (deriv k) (v x) : ℝ) : ℂ) * wd n j (fun y => ((v y : ℝ) : ℂ)) x *
          conj (wd n c (fun y => ((v y : ℝ) : ℂ)) x) +
        ((deriv k (v x) : ℝ) : ℂ) * wd n j (wdb n c (fun y => ((v y : ℝ) : ℂ))) x := by
  have hv1 : DifferentiableAt ℝ v x := hv.differentiableAt (by simp)
  have hk1 : DifferentiableAt ℝ (deriv k) (v x) := differentiableAt_deriv_of_contDiffAt hk
  have hv' : ContDiffAt ℝ 2 (fun y => ((v y : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hv
  have hvd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ v y := eventually_differentiableAt_of_contDiffAt hv
  have hkd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ k (v y) :=
    hv1.continuousAt.tendsto.eventually (eventually_differentiableAt_of_contDiffAt hk)
  have hE : wdb n c (fun y => ((k (v y) : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun y => ((deriv k (v y) : ℝ) : ℂ) * wdb n c (fun y => ((v y : ℝ) : ℂ)) y := by
    filter_upwards [hvd, hkd] with y hy1 hy2
    exact wdb_ofReal_comp hy2 hy1
  have hD1 : DifferentiableAt ℝ (fun y => ((deriv k (v y) : ℝ) : ℂ)) x :=
    differentiableAt_ofReal (hk1.comp x hv1)
  rw [wd_congr hE,
    wd_mul (f := fun y => ((deriv k (v y) : ℝ) : ℂ)) (g := wdb n c (fun y => ((v y : ℝ) : ℂ)))
      hD1 (differentiableAt_wdb hv'),
    wd_ofReal_comp hk1 hv1, wdb_ofReal hv1]

theorem hessLog_normSq {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) (j c : Fin n) :
    wd n j (wdb n c (fun y => ((Complex.normSq (g y) : ℝ) : ℂ))) x =
      wd n j g x * conj (wd n c g x) := by
  have hgd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y :=
    (hg.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by simp)
  have hgx : DifferentiableAt ℂ g x := hg.differentiableAt (by simp)
  have hf : (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) := by
    funext y; rw [Complex.mul_conj]
  have h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x := hg.fderiv_right (by norm_num)
  have hh : DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n c)) x :=
    (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
  have hE : wdb n c (fun y => g y * conj (g y)) =ᶠ[𝓝 x]
      fun y => g y * conj (fderiv ℂ g y (bas n c)) := by
    filter_upwards [hgd] with y hy
    rw [wdb_mul (hy.restrictScalars ℝ) (differentiableAt_conj (hy.restrictScalars ℝ)),
      wdb_of_differentiableAt hy, wdb_conj (hy.restrictScalars ℝ), wd_of_differentiableAt hy]
    ring
  rw [hf, wd_congr hE, wd_mul (f := g) (g := fun y => conj (fderiv ℂ g y (bas n c)))
    (hgx.restrictScalars ℝ) (differentiableAt_conj (hh.restrictScalars ℝ)),
    wd_conj (hh.restrictScalars ℝ), wdb_of_differentiableAt hh]
  simp [wd_of_differentiableAt hgx]

theorem cHess_log_one_add_sum : ∀ (d : ℕ) (β : Type) [Fintype β] (U : Set (V d)) (f : β → V d → ℂ),
    IsOpen U → (∀ j, DifferentiableOn ℂ (f j) U) → ∀ z ∈ U,
    cHess d (fun v => ((Real.log (1 + ∑ j, ‖f j v‖ ^ 2) : ℝ) : ℂ)) z =
      fsLevi (fun j => f j z) (Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1)) := by
  intro d β _ U f hU hf z hz
  have hC : ∀ j, ContDiffAt ℂ 2 (f j) z := fun j =>
    ((contDiffOn_of_differentiableOn d (f j) U hU (hf j)).contDiffAt (hU.mem_nhds hz)).of_le
      ENat.LEInfty.out
  have hu : ∀ j, ContDiffAt ℝ 2 (fun y => Complex.normSq (f j y)) z := fun j =>
    H.contDiffAt_normSq_comp (hC j)
  have hu' : ∀ j, ContDiffAt ℝ 2 (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) z := fun j =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (hu j)
  have hnorm : ∀ v, (1 + ∑ j, ‖f j v‖ ^ 2 : ℝ) = 1 + ∑ j, Complex.normSq (f j v) := fun v => by
    simp only [Complex.normSq_eq_norm_sq]
  set S : V d → ℝ := fun y => 1 + ∑ j, Complex.normSq (f j y) with hSdef
  have hSpos : 0 < S z :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)
  have hS : ContDiffAt ℝ 2 S z := contDiffAt_const.add (ContDiffAt.sum fun j _ => hu j)
  have hlog : ContDiffAt ℝ 2 Real.log (S z) := Real.contDiffAt_log.2 hSpos.ne'
  have hSc : (fun y => ((S y : ℝ) : ℂ)) =
      fun y => 1 + ∑ j, ((Complex.normSq (f j y) : ℝ) : ℂ) := by
    funext y; simp [hSdef]
  have hTd : ∀ {y}, (∀ j, DifferentiableAt ℝ (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) y) →
      DifferentiableAt ℝ (fun y => ∑ j, ((Complex.normSq (f j y) : ℝ) : ℂ)) y := fun h =>
    DifferentiableAt.fun_sum fun j _ => h j
  have hwd : ∀ a, wd d a (fun y => ((S y : ℝ) : ℂ)) z =
      ∑ j, wd d a (f j) z * conj (f j z) := fun a => by
    have h1 : ∀ j, DifferentiableAt ℝ (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) z := fun j =>
      (hu' j).differentiableAt (by simp)
    rw [hSc, wd_add (differentiableAt_const _) (hTd h1), wd_sum Finset.univ fun j _ => h1 j]
    simp only [fun j => H.wd_normSq_comp (j := a) (hC j)]
    simp [wd]
  have hhess : ∀ a c, wd d a (wdb d c (fun y => ((S y : ℝ) : ℂ))) z =
      ∑ j, wd d a (f j) z * conj (wd d c (f j) z) := fun a c => by
    have hev : wdb d c (fun y => ((S y : ℝ) : ℂ)) =ᶠ[𝓝 z]
        fun y => ∑ j, wdb d c (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) y := by
      have : ∀ᶠ y in 𝓝 z, ∀ j,
          DifferentiableAt ℝ (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) y := by
        rw [Filter.eventually_all]
        exact fun j => eventually_differentiableAt_of_contDiffAt (hu' j)
      filter_upwards [this] with y hy
      rw [hSc, wdb_add (differentiableAt_const _) (hTd hy), wdb_sum Finset.univ fun j _ => hy j]
      simp [wdb]
    rw [wd_congr hev, wd_sum Finset.univ fun j _ => differentiableAt_wdb (hu' j)]
    exact Finset.sum_congr rfl fun j _ => hessLog_normSq (hC j) a c
  have hd1 : deriv Real.log (S z) = (S z)⁻¹ := by rw [Real.deriv_log']
  have hd2 : deriv (deriv Real.log) (S z) = -((S z) ^ 2)⁻¹ := by
    rw [Real.deriv_log']; exact deriv_inv
  have hS0 : ((S z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hSpos.ne'
  ext a c
  have hfun : (fun v => ((Real.log (1 + ∑ j, ‖f j v‖ ^ 2) : ℝ) : ℂ)) =
      fun v => ((Real.log (S v) : ℝ) : ℂ) := by
    funext v; rw [hnorm]
  have hF : ∀ (j : β) (a : Fin d), fderiv ℂ (f j) z (EuclideanSpace.single a 1) = wd d a (f j) z :=
    fun j a => (wd_of_differentiableAt ((hC j).differentiableAt (by simp))).symm
  have hval : ((1 + ∑ j, ‖f j z‖ ^ 2 : ℝ) : ℂ) = ((S z : ℝ) : ℂ) := by rw [hnorm]
  simp only [cHess, fsLevi, Matrix.of_apply, hF, hfun, hval]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hessLog_chain hS hlog a c, hd1, hd2, hwd a, hwd c, hhess a c, map_sum]
  have hconj : ∑ j, conj (wd d c (f j) z * conj (f j z)) = ∑ j, f j z * conj (wd d c (f j) z) :=
    Finset.sum_congr rfl fun j _ => by rw [map_mul, Complex.conj_conj, mul_comm]
  rw [hconj]
  push_cast
  field_simp
  ring

end GlobalTheory.CompanionTheory.FSCrofton
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverIntersectionGradedIso
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob

namespace GlobalTheory.CompanionTheory.CapKC

variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem inU_capO {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {ι : Type} (U : ι → X.Opens) {n : ℕ}
    (i : Fin n → ι) (T : Thick (nlFun γ p X q κ)) : InU (capO U i) T ↔ ∀ a, InU (U (i a)) T := by
  constructor
  · intro h a x hx
    exact capO_le U i a (h hx)
  · intro h x hx
    let W : X.Opens := ⟨⋂ a, (U (i a) : Set X), isOpen_iInter_of_finite fun a => (U (i a)).isOpen⟩
    have hW : W ≤ capO U i := le_iInf fun a y hy => Set.mem_iInter.1 hy a
    exact hW (Set.mem_iInter.2 fun a => h a hx)

variable (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι)

def toCap : (KS q (a + 1) {capO U.U i}).FullSubcategory ⥤ (capT (Vk q U a) i).FullSubcategory :=
  (capT (Vk q U a) i).lift ((KC q U a).lift (KS q (a + 1) {capO U.U i}).ι fun T =>
      ⟨T.property.1, U.U (i 0), ⟨i 0, rfl⟩, by
        obtain ⟨_, V, rfl, hV⟩ := T.property
        exact (inU_capO U.U i T.obj).1 hV 0⟩) fun T k => by
    obtain ⟨_, V, rfl, hV⟩ := T.property
    exact (inU_capO U.U i T.obj).1 hV k

def ofCap : (capT (Vk q U a) i).FullSubcategory ⥤ (KS q (a + 1) {capO U.U i}).FullSubcategory :=
  (KS q (a + 1) {capO U.U i}).lift ((capT (Vk q U a) i).ι ⋙ (KC q U a).ι) fun T =>
    ⟨T.obj.property.1, capO U.U i, rfl, (inU_capO U.U i T.obj.obj).2 T.property⟩

def capAdj : toCap q U a n i ⊣ ofCap q U a n i := Adjunction.mkOfHomEquiv
  { homEquiv := fun A B =>
      { toFun := fun g => ObjectProperty.homMk g.hom.hom
        invFun := fun g => ObjectProperty.homMk (ObjectProperty.homMk g.hom)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    homEquiv_naturality_left_symm := fun _ _ => rfl
    homEquiv_naturality_right := fun _ _ => rfl }

theorem cap_kc : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a n : ℕ)
    (i : Fin (n + 1) → U.ι) (r : ℕ), Nonempty (HU (Fk q U a) (capT (Vk q U a) i) r ≃+ HQ (KS q (a + 1) {capO U.U i}) (a : ℤ) ((a : ℤ) + 1) r) := by
  intro K _ X q U a n i r
  have hb := CrystallineSemistableComparison.P.adj ((capT (Vk q U a) i).ι ⋙ Fk q U a) (toCap q U a n i) (ofCap q U a n i) (capAdj q U a n i) r
  exact ⟨(LinearEquiv.ofBijective _ hb).toAddEquiv⟩

end GlobalTheory.CompanionTheory.CapKC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationSaturated
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

theorem Fil0_succ_le {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) : A.Fil0 (r + 1) ≤ A.Fil0 r :=
  Ideal.span_mono fun _ ⟨k, hk, e⟩ => ⟨k, by omega, e⟩

theorem crystalline_filtration_l_saturated : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) (z : A.Acr0),
    (l : A.Acr0) * z ∈ A.Fil0 r → z ∈ A.Fil0 r := by
  intro l _ A r
  induction r with
  | zero =>
    intro z _
    rw [(_root_.GlobalTheory.CompanionTheory.FilMul.main A).1]
    exact Submodule.mem_top
  | succ r ih =>
    intro z hz
    have hzr : z ∈ A.Fil0 r := ih z (Fil0_succ_le A r hz)
    obtain ⟨h1, h2, -⟩ := _root_.GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces A r
    obtain ⟨w, hw⟩ := h1 z hzr
    have hlw : algebraMap A.W A.Acr0 ((l : A.W) * w) * A.dxi0 r ∈ A.Fil0 (r + 1) := by
      have e : algebraMap A.W A.Acr0 ((l : A.W) * w) * A.dxi0 r =
          (l : A.Acr0) * z - (l : A.Acr0) * (z - algebraMap A.W A.Acr0 w * A.dxi0 r) := by
        rw [map_mul, map_natCast]; ring
      rw [e]
      exact sub_mem hz (Ideal.mul_mem_left _ _ hw)
    have hmem : (l : A.W) * w ∈ Ideal.span {A.xi} := (h2 _).1 hlw
    have hth : (l : A.U) * A.th w = 0 := by
      rw [← map_natCast A.th, ← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hmem
    have hth0 : A.th w = 0 :=
      (mem_nonZeroDivisors_iff_left.1 (_root_.GlobalTheory.CompanionTheory.UntiltRegular.untilt_regular A).1) _ hth
    have hwx : w ∈ Ideal.span {A.xi} := Ideal.Quotient.eq_zero_iff_mem.1 hth0
    have := add_mem hw ((h2 w).2 hwx)
    simpa using this

end GlobalTheory.CompanionTheory.PerfFil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaNat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

section Pts

variable {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D)

def Gp : Pt E' ⥤ Pt E where
  obj X := ⟨m.G.obj X.T, e ≫ m.G.map X.s⟩
  map {X Y} f := m.G.map (show X.T ⟶ Y.T from f)
  map_id X := m.G.map_id X.T
  map_comp {X Y Z} f g := m.G.map_comp (show X.T ⟶ Y.T from f) (show Y.T ⟶ Z.T from g)

def mPt (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') :
    CH.Mor (Pt.U E ⋙ sq a b) (Pt.U E' ⋙ sq a' b') σ where
  G := Gp m E E' e
  τ X := (m.sqC c ha hb).τ X.T
  nat {X Y} φ x := (m.sqC c ha hb).nat (show X.T ⟶ Y.T from φ) x

end Pts

section Cuts

variable {d : ℕ} (E : Frame Φ (d + 1)) (E' : Frame Φ' (d + 1)) (e : E.D ⟶ m.G.obj E'.D)
  (he : m.Fr E E' e) (hρ : ∀ T, Function.Injective (m.ρ T))

include he hρ in
theorem cut_mem {X Y : Cut E'} (φ : X ⟶ Y) :
    E.τ 0 ((e ≫ m.G.map X.s) ≫ m.G.map φ.1) (e ≫ m.G.map Y.s) = 0 := by
  apply hρ Y.T
  have h := he 0 (X.s ≫ φ.1) Y.s
  rw [map_zero, Category.assoc, ← m.G.map_comp, h]
  exact φ.2

def G1 : Cut E' ⥤ Cut E where
  obj X := ⟨m.G.obj X.T, e ≫ m.G.map X.s⟩
  map {X Y} φ := ⟨m.G.map φ.1, cut_mem m E E' e he hρ φ⟩
  map_id X := Cut.hom_ext (m.G.map_id X.T)
  map_comp {X Y Z} f g := Cut.hom_ext (m.G.map_comp f.1 g.1)

def m1 : SMor (Cut.Φ1 E) (Cut.Φ1 E') σ where
  G := G1 m E E' e he hρ
  ρ T := m.ρ T.T
  comm T r := m.comm T.T r
  nat {T T'} φ x := m.nat φ.1 x
  mem T x hx := m.mem T.T hx
  dp T k x hx := m.dp T.T k hx

def e1 : (Cut.E1 E).D ⟶ (G1 m E E' e he hρ).obj (Cut.E1 E').D :=
  ⟨e, by
    change E.τ 0 (𝟙 E.D ≫ e) (e ≫ m.G.map (𝟙 E'.D)) = 0
    rw [Category.id_comp, m.G.map_id, Category.comp_id]
    exact E.τ_self 0 e⟩

theorem fr1 : (m1 m E E' e he hρ).Fr (Cut.E1 E) (Cut.E1 E') (e1 m E E' e he hρ) :=
  fun i {T} s s' => he i.succ s.1 s'.1

variable (Q : Poly Φ) (Q' : Poly Φ')

def etaC (X : Pt E') : (Cut.P0 Q).obj ((Gp m E E' e).obj X) ⟶ (G1 m E E' e he hρ).obj ((Cut.P0 Q').obj X) :=
  Cut.adjInv Q _ _ (m.G.map (Q'.j X.T))

theorem j_eta (X : Pt E') : Q.j (m.G.obj X.T) ≫ (etaC m E E' e he hρ Q Q' X).1 = m.G.map (Q'.j X.T) :=
  Cut.adjInv_j Q ((Gp m E E' e).obj X) ((G1 m E E' e he hρ).obj ((Cut.P0 Q').obj X)) (m.G.map (Q'.j X.T))

theorem rho_eta (X : Pt E') :
    m.ρ (Q'.P X.T) ((Φ.A.map (etaC m E E' e he hρ Q Q' X).1).hom (Q.X (m.G.obj X.T))) = Q'.X X.T := by
  have h1 : (Φ.A.map (etaC m E E' e he hρ Q Q' X).1).hom (Q.X (m.G.obj X.T)) =
      E.τ 0 ((e ≫ m.G.map X.s) ≫ m.G.map (Q'.j X.T)) (e ≫ m.G.map (Cut.sec Q' X)) :=
    Q.lift_X (m.G.map (Q'.j X.T)) _ (E.mem 0 _ _)
  rw [h1, Category.assoc, ← m.G.map_comp, he 0 (X.s ≫ Q'.j X.T) (Cut.sec Q' X), Cut.sec_spec, if_pos rfl]

theorem eta_nat {X Y : Pt E'} (φ : X.T ⟶ Y.T) :
    Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ) ≫ (etaC m E E' e he hρ Q Q' Y).1 =
      (etaC m E E' e he hρ Q Q' X).1 ≫ m.G.map (Cut.Pmap (X := X) (Y := Y) Q' φ) := by
  have e1 : Q.j (m.G.obj X.T) ≫ Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ) =
      m.G.map φ ≫ Q.j (m.G.obj Y.T) := Cut.Pmap_j (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ)
  have e2 : Q'.j X.T ≫ Cut.Pmap (X := X) (Y := Y) Q' φ = φ ≫ Q'.j Y.T := Cut.Pmap_j (X := X) (Y := Y) Q' φ
  have e3 : Q.j (m.G.obj X.T) ≫ Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ) ≫
      (etaC m E E' e he hρ Q Q' Y).1 = Q.j (m.G.obj X.T) ≫ (etaC m E E' e he hρ Q Q' X).1 ≫
        m.G.map (Cut.Pmap (X := X) (Y := Y) Q' φ) := by
    rw [← Category.assoc, e1, Category.assoc, j_eta, ← Category.assoc (Q.j _), j_eta, ← m.G.map_comp, ← m.G.map_comp, e2]
  have e4 := Cut.truncation_hom_ext Q (X := (Gp m E E' e).obj X) (Y := (G1 m E E' e he hρ).obj ((Cut.P0 Q').obj Y))
    (ψ := (Cut.P0 Q).map (show (Gp m E E' e).obj X ⟶ (Gp m E E' e).obj Y from m.G.map φ) ≫ etaC m E E' e he hρ Q Q' Y)
    (ψ' := etaC m E E' e he hρ Q Q' X ≫ (G1 m E E' e he hρ).map ((Cut.P0 Q').map (show X ⟶ Y from φ))) e3
  exact congrArg Subtype.val e4

def eta : Gp m E E' e ⋙ Cut.P0 Q ⟶ Cut.P0 Q' ⋙ G1 m E E' e he hρ where
  app X := etaC m E E' e he hρ Q Q' X
  naturality {X Y} φ := Cut.hom_ext (eta_nat m E E' e he hρ Q Q' (X := X) (Y := Y) φ)

def mP (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') :
    CH.Mor (Cut.P0 Q ⋙ Cut.U E ⋙ sq a b) (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq a' b') σ where
  G := Gp m E E' e
  τ X := ((m.sqC c ha hb).τ (Q'.P X.T)).comp ((sq a b).map (etaC m E E' e he hρ Q Q' X).1).hom
  nat {X Y} φ x := by
    have key : ∀ (φ : X.T ⟶ Y.T) (x : sqM a b (Q.P (m.G.obj X.T))),
        (m.sqC c ha hb).τ (Q'.P Y.T) (((sq a b).map (etaC m E E' e he hρ Q Q' Y).1).hom
          (((sq a b).map (Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ))).hom x)) =
        ((sq a' b').map (Cut.Pmap (X := X) (Y := Y) Q' φ)).hom
          ((m.sqC c ha hb).τ (Q'.P X.T) (((sq a b).map (etaC m E E' e he hρ Q Q' X).1).hom x)) := by
      intro φ x
      rw [← (m.sqC c ha hb).nat]
      congr 1
      have h := eta_nat m E E' e he hρ Q Q' (X := X) (Y := Y) φ
      have h2 := congrArg (fun t => ((sq a b).map t).hom x) h
      simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
      exact h2
    exact key φ x

end Cuts

end GlobalTheory.CompanionTheory.LocBC
end
end

