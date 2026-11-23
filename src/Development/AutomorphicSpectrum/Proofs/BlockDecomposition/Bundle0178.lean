module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0164
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0174
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0158
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0172
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0175
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0177

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisLevelOneFacts
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg TensorProduct

namespace GlobalTheory.CompanionTheory.ACrisMod

variable {l : ℕ} [Fact l.Prime]


variable (l) in
abbrev Qt : Type := Ob l ⧸ Ideal.span {pFlat l ^ l}


variable (l) in
abbrev Nm : Type := ℕ →₀ Qt l

@[reducible] def modAcr (A : PAlg l) : Module (Ob l) (A.Acr 1) := Module.compHom _ (A.aTo1.comp A.s)

attribute [local instance] modAcr

theorem smul_acr (A : PAlg l) (c : Ob l) (y : A.Acr 1) : c • y = A.aTo1 (A.s c) * y := rfl

def mulDxi (A : PAlg l) (k : ℕ) : A.A →ₗ[Ob l] A.Acr 1 where
  toFun a := A.aTo1 a * A.dxi 1 (l * k)
  map_add' x y := by rw [map_add (f := _), add_mul]
  map_smul' c a := by
    rw [Algebra.smul_def, map_mul, RingHom.id_apply, smul_acr, mul_assoc]; rfl

theorem mulDxi_apply (A : PAlg l) (k : ℕ) (a : A.A) : mulDxi A k a = A.aTo1 a * A.dxi 1 (l * k) := rfl

theorem pow_smul_mulDxi (A : PAlg l) (k : ℕ) : pFlat l ^ l • mulDxi A k = 0 := by
  ext a
  have h := (_root_.GlobalTheory.CompanionTheory.PerfFil.Expand.main A).2.2.2 (l * k)
  rw [LinearMap.smul_apply, smul_acr, mulDxi_apply, LinearMap.zero_apply, map_pow, mul_left_comm]
  have e : A.aTo1 (A.s (pFlat l) ^ l) * A.dxi 1 (l * k) = 0 := h
  rw [e, mul_zero]

def tk (A : PAlg l) (k : ℕ) : Qt l →ₗ[Ob l] (A.A →ₗ[Ob l] A.Acr 1) :=
  (Ideal.span {pFlat l ^ l}).liftQ (LinearMap.toSpanSingleton (Ob l) _ (mulDxi A k)) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, mul_smul, pow_smul_mulDxi, smul_zero])

def tauL (A : PAlg l) : Nm l ⊗[Ob l] A.A →ₗ[Ob l] A.Acr 1 :=
  TensorProduct.lift (Finsupp.lsum ℕ (tk A))

theorem tauL_one (A : PAlg l) (k : ℕ) (a : A.A) :
    tauL A (Finsupp.single k 1 ⊗ₜ a) = A.aTo1 a * A.dxi 1 (l * k) := by
  have : (1 : Qt l) = Submodule.Quotient.mk (1 : Ob l) := rfl
  rw [tauL, TensorProduct.lift.tmul, Finsupp.lsum_single, this, tk, Submodule.liftQ_apply,
    LinearMap.toSpanSingleton_apply, one_smul, mulDxi_apply]

theorem smul_one_Qt (r : Ob l) : r • (1 : Qt l) = Submodule.Quotient.mk r := by
  change r • (Submodule.Quotient.mk (1 : Ob l) : Qt l) = _
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]

theorem pow_smul_Qt (q : Qt l) : pFlat l ^ l • q = 0 := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def gen (A : PAlg l) (c : ℕ →₀ A.A) : Nm l ⊗[Ob l] A.A := c.sum fun k a => Finsupp.single k 1 ⊗ₜ a

theorem gen_zero (A : PAlg l) : gen A 0 = 0 := Finsupp.sum_zero_index

theorem gen_add (A : PAlg l) (c d : ℕ →₀ A.A) : gen A (c + d) = gen A c + gen A d :=
  Finsupp.sum_add_index' (fun _ => TensorProduct.tmul_zero _ _) (fun _ _ _ => TensorProduct.tmul_add _ _ _)

theorem gen_single (A : PAlg l) (k : ℕ) (a : A.A) : gen A (Finsupp.single k a) = Finsupp.single k 1 ⊗ₜ a :=
  Finsupp.sum_single_index (TensorProduct.tmul_zero _ _)

theorem tauL_gen (A : PAlg l) (c : ℕ →₀ A.A) : tauL A (gen A c) = A.expand c := by
  rw [gen, map_finsuppSum, expand]
  exact Finsupp.sum_congr fun k _ => tauL_one A k (c k)

theorem exists_gen (A : PAlg l) (x : Nm l ⊗[Ob l] A.A) : ∃ c, gen A c = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, gen_zero A⟩
  | add x y hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    exact ⟨c + d, gen_add A c d⟩
  | tmul n a =>
    induction n using Finsupp.induction_linear with
    | zero => exact ⟨0, by rw [gen_zero, TensorProduct.zero_tmul]⟩
    | add f g hf hg =>
      obtain ⟨c, hc⟩ := hf
      obtain ⟨d, hd⟩ := hg
      exact ⟨c + d, by rw [gen_add, hc, hd, TensorProduct.add_tmul]⟩
    | single k q =>
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine ⟨Finsupp.single k (r • a), ?_⟩
      rw [gen_single, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Finsupp.smul_single]
      congr 2
      exact smul_one_Qt r

theorem gen_eq_zero (A : PAlg l) (c : ℕ →₀ A.A) (h : ∀ k, c k ∈ Ideal.span {A.pi ^ l}) : gen A c = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (h k)
  have e : c k = pFlat l ^ l • b := by
    rw [Algebra.smul_def, ← hb, mul_comm]
    congr 1
    exact (map_pow A.s _ _).symm
  have z : pFlat l ^ l • (Finsupp.single k 1 : Nm l) = 0 := by
    rw [Finsupp.smul_single, pow_smul_Qt, Finsupp.single_zero]
  change Finsupp.single k 1 ⊗ₜ[Ob l] (c k) = 0
  rw [e, ← TensorProduct.smul_tmul, z, TensorProduct.zero_tmul]

theorem tauL_bijective (A : PAlg l) : Function.Bijective (tauL A) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨c, rfl⟩ := exists_gen A x
    rw [tauL_gen] at hx
    exact gen_eq_zero A c ((_root_.GlobalTheory.CompanionTheory.ExpandKer.expand_eq_zero_iff A c).1 hx)
  · obtain ⟨c, rfl⟩ := (_root_.GlobalTheory.CompanionTheory.PerfFil.Expand.main A).1 y
    exact ⟨gen A c, tauL_gen A c⟩

def tau (A : PAlg l) : Nm l ⊗[Ob l] A.A ≃+ A.Acr 1 :=
  { Equiv.ofBijective (tauL A) (tauL_bijective A) with map_add' := map_add (tauL A) }

theorem tau_apply (A : PAlg l) (x : Nm l ⊗[Ob l] A.A) : tau A x = tauL A x := rfl

theorem map_gen {A B : PAlg l} (f : A ⟶ B) (c : ℕ →₀ A.A) :
    ((D.toPf l ⋙ D.tensF l (Ob l) (Nm l)).map f).hom (gen A c) =
      gen B (c.mapRange (Hom.f f) (map_zero _)) := by
  rw [gen, map_finsuppSum, gen, Finsupp.sum_mapRange_index (fun _ => TensorProduct.tmul_zero _ _)]
  rfl

theorem pow_smul_Nm (x : Nm l) : pFlat l ^ l • x = 0 :=
  Finsupp.ext fun k => (Finsupp.smul_apply _ _ _).trans (pow_smul_Qt (x k))

theorem algebraMap_eq (A : PAlg l) (a : Ainf l) (y : A.Acr 1) :
    algebraMap (Ainf l) (A.Acr 1) a * y = a.coeff 0 • y := by
  rw [(_root_.GlobalTheory.CompanionTheory.PAlgNat.expand_nat A A (𝟙 A)).2.2.2.2.2 a]
  rfl

theorem tau_smul (A : PAlg l) (a : Ainf l) (x : Nm l ⊗[Ob l] A.A) :
    tau A (a.coeff 0 • x) = algebraMap (Ainf l) (A.Acr 1) a * tau A x :=
  ((tauL A).map_smul (a.coeff 0) x).trans (algebraMap_eq A a (tauL A x)).symm

theorem tau_map (A B : PAlg l) (f : A ⟶ B) (x : Nm l ⊗[Ob l] A.A) :
    tau B (((D.toPf l ⋙ D.tensF l (Ob l) (Nm l)).map f).hom x) = mapAcr f 1 (tau A x) := by
  obtain ⟨c, rfl⟩ := exists_gen A x
  rw [tau_apply, tau_apply, map_gen, tauL_gen, tauL_gen]
  exact ((_root_.GlobalTheory.CompanionTheory.PAlgNat.expand_nat A B f).2.1 c).symm

theorem acr1 (l : ℕ) [Fact l.Prime] : CrystallineSemistableComparison.D.RAcr1 l :=
  ⟨Nm l, inferInstance, inferInstance, l, tau, pow_smul_Nm, tau_smul, tau_map⟩

end GlobalTheory.CompanionTheory.ACrisMod
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariance
section
open MeasureTheory Filter Topology
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisAvg

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem pointwise_bound {K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {φ : K → ℂ} {M : ℝ}
    (hM1 : 1 ≤ M) (hM : ∀ κ, ‖ρ κ‖ ≤ M) (hc : ∀ p ∈ P, ‖c p‖ = 1) (hL : Law K P c φ)
    (hN : Near K P {v | ‖ρ v - 1‖ ≤ 1 / (4 * M)} φ) {w : W} (hw : w ∈ secSp K P c ρ) (κ : K) :
    ‖φ κ • ρ κ w - ((‖φ κ‖ : ℝ) : ℂ) • w‖ ≤ ‖φ κ‖ * ‖w‖ / 2 := by
  by_cases h0 : φ κ = 0
  · simp [h0]
  obtain ⟨r, v, hr, hv, rfl, hn⟩ := hN κ h0
  have hM0 : 0 < M := by linarith
  have hcr : ‖c r‖ = 1 := hc _ hr
  have hφ : φ (r * v) = c r * φ v := hL r v hr
  have hnorm : ‖φ (r * v)‖ = ‖φ v‖ := by rw [hφ, norm_mul, hcr, one_mul]
  have hwr : c r • ρ r w = w := hw r hr
  obtain ⟨u, hu⟩ : ∃ u, u = ρ v w - w := ⟨_, rfl⟩
  have hub : ‖u‖ ≤ ‖w‖ / (4 * M) := by
    have h1 : u = (ρ v - 1) w := by simp [hu]
    have hv' : ‖ρ v - 1‖ ≤ 1 / (4 * M) := hv
    rw [h1]
    calc ‖(ρ v - 1) w‖ ≤ ‖ρ v - 1‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 / (4 * M) * ‖w‖ := by gcongr
      _ = ‖w‖ / (4 * M) := by ring
  have hrb : ‖c r • ρ r u‖ ≤ ‖w‖ / 4 := by
    rw [norm_smul, hcr, one_mul]
    calc ‖ρ r u‖ ≤ ‖ρ r‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * (‖w‖ / (4 * M)) := by
          gcongr
          exact hM r
      _ = ‖w‖ / 4 := by field_simp
  have hexp : φ (r * v) • ρ (r * v) w - ((‖φ (r * v)‖ : ℝ) : ℂ) • w =
      (φ v - ((‖φ v‖ : ℝ) : ℂ)) • w + φ v • (c r • ρ r u) := by
    have h2 : ρ v w = w + u := by simp [hu]
    have h3 : ρ (r * v) w = ρ r w + ρ r u := by
      rw [map_mul, ContinuousLinearMap.mul_apply, h2, map_add (f := _)]
    rw [hnorm, hφ, h3, smul_add, mul_comm, mul_smul, hwr, sub_smul, mul_smul]
    abel
  rw [hexp, hnorm]
  calc ‖(φ v - ((‖φ v‖ : ℝ) : ℂ)) • w + φ v • (c r • ρ r u)‖
      ≤ ‖φ v - ((‖φ v‖ : ℝ) : ℂ)‖ * ‖w‖ + ‖φ v‖ * ‖c r • ρ r u‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
    _ ≤ ‖φ v‖ / 4 * ‖w‖ + ‖φ v‖ * (‖w‖ / 4) := by gcongr
    _ = ‖φ v‖ * ‖w‖ / 2 := by ring

theorem avg_sub_bound [FiniteDimensional ℂ W] {K : Subgroup G} [MeasurableSpace K] [BorelSpace K]
    [CompactSpace K] (μ : Measure K) [IsProbabilityMeasure μ] {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ)
    {φ : K → ℂ} (hφ : Continuous φ) (w : W)
    (h : ∀ κ, ‖φ κ • ρ κ w - ((‖φ κ‖ : ℝ) : ℂ) • w‖ ≤ ‖φ κ‖ * ‖w‖ / 2) :
    ‖avg μ ρ φ w - ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w‖ ≤ (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2 := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hint : Integrable (fun κ => φ κ • ρ κ) μ :=
    (hφ.smul hρ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun κ => ‖φ κ‖) μ :=
    hφ.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint3 : Integrable (fun κ => φ κ • ρ κ w) μ := by
    have := hint.apply_continuousLinearMap w
    exact this
  have hint4 : Integrable (fun κ => ((‖φ κ‖ : ℝ) : ℂ) • w) μ :=
    (hint2.ofReal (𝕜 := ℂ)).smul_const w
  have e1 : avg μ ρ φ w = ∫ κ, φ κ • ρ κ w ∂μ := ContinuousLinearMap.integral_apply hint w
  have e2 : ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w = ∫ κ, ((‖φ κ‖ : ℝ) : ℂ) • w ∂μ := by
    rw [integral_smul_const, integral_complex_ofReal]
  rw [e1, e2, ← integral_sub hint3 hint4]
  have e3 : (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2 = ∫ κ, ‖φ κ‖ * ‖w‖ / 2 ∂μ := by
    rw [integral_div, integral_mul_const]
  rw [e3]
  exact norm_integral_le_of_norm_le ((hint2.mul_const _).div_const _) (Eventually.of_forall h)

theorem mass_pos {K : Subgroup G} [MeasurableSpace K] [BorelSpace K] [CompactSpace K]
    [IsTopologicalGroup K] (μ : Measure K) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    {φ : K → ℂ} (hφ : Continuous φ) (h1 : φ 1 = 1) : 0 < ∫ κ, ‖φ κ‖ ∂μ := by
  refine hφ.norm.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun _ => norm_nonneg _) (x := 1) ?_
  simp [h1]

end Abstract

theorem avgInv_of_avgMem : AvgMem → AvgInv := by
  intro hA G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hH hP Γ P c hPar
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI := hH
  haveI := hP
  obtain ⟨M, hM1, hM⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ κ, ‖ρ κ‖ ≤ M := by
    obtain ⟨C, hC⟩ := (isCompact_range hρ).isBounded.exists_norm_le
    exact ⟨max 1 C, le_max_left _ _, fun κ => (hC _ ⟨κ, rfl⟩).trans (le_max_right _ _)⟩
  have hM0 : 0 < M := by linarith
  refine ⟨{v | ‖ρ v - 1‖ ≤ 1 / (4 * M)}, ?_, ?_⟩
  · have ht : Tendsto (fun v => ρ v - 1) (𝓝 (1 : K)) (𝓝 0) := by
      have h5 := hρ.tendsto (1 : K)
      rw [map_one] at h5
      simpa using h5.sub_const 1
    have h4 : (0 : ℝ) < 1 / (4 * M) := by positivity
    filter_upwards [ht (Metric.closedBall_mem_nhds 0 h4)] with v hv
    simpa using hv
  · intro φ hφ h1 hL hN
    have hI : 0 < ∫ κ, ‖φ κ‖ ∂μ := mass_pos μ hφ h1
    have hb : ∀ w ∈ secSp K P c ρ,
        ‖avg μ ρ φ w - ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w‖ ≤ (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2 := fun w hw =>
      avg_sub_bound μ hρ hφ w (pointwise_bound hM1 hM hPar.ch.norm hL hN hw)
    have hmem : ∀ w : W, avg μ ρ φ w ∈ secSp K P c ρ := fun w =>
      hA G W K ρ hK hρ μ hH hP Γ P c hPar φ hφ hL w
    let T : secSp K P c ρ →ₗ[ℂ] secSp K P c ρ :=
      ((avg μ ρ φ : W →L[ℂ] W) : W →ₗ[ℂ] W).restrict fun w _ => hmem w
    have hinj : Function.Injective T := by
      refine (injective_iff_map_eq_zero T).mpr fun w hw => ?_
      have h0 : avg μ ρ φ (w : W) = 0 := congrArg Subtype.val hw
      have h6 := hb w w.2
      rw [h0, zero_sub, norm_neg, norm_smul, Complex.norm_real, Real.norm_of_nonneg hI.le] at h6
      have h7 : ‖(w : W)‖ = 0 := by
        have h8 : 0 ≤ ‖(w : W)‖ := norm_nonneg _
        nlinarith
      exact Subtype.ext (norm_eq_zero.mp h7)
    let e := LinearEquiv.ofInjectiveEndo T hinj
    refine ⟨LinearMap.toContinuousLinearMap ((secSp K P c ρ).subtype ∘ₗ e.symm.toLinearMap), fun w => ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply w)

end GlobalTheory.CompanionTheory.RgEisAvg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageMembership
section
open MeasureTheory PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.EisMirGen

theorem avgMem : AvgMem := by
  unfold AvgMem ForRep
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hHaar _ _Γ P c _ φ hφ hLaw w
  haveI := hHaar
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  change ∀ r : K, (r : G) ∈ P → c r • ρ r (avg μ ρ φ w) = avg μ ρ φ w
  intro r hr
  have hcont : Continuous fun κ : K => φ κ • ρ κ := hφ.smul hρ
  have hint : Integrable (fun κ : K => φ κ • ρ κ) μ :=
    hcont.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  have key : avg μ ρ φ = c r • (ρ r).comp (avg μ ρ φ) := by
    show ∫ κ, φ κ • ρ κ ∂μ = c r • (ρ r).comp (∫ κ, φ κ • ρ κ ∂μ)
    calc ∫ κ, φ κ • ρ κ ∂μ = ∫ κ, φ (r * κ) • ρ (r * κ) ∂μ :=
          (integral_mul_left_eq_self (fun κ => φ κ • ρ κ) r).symm
      _ = ∫ κ, c r • (ContinuousLinearMap.compL ℂ W W W (ρ r)) (φ κ • ρ κ) ∂μ := by
          congr 1
          funext κ
          rw [hLaw r κ hr, map_mul]
          ext x
          simp [mul_smul]
      _ = c r • ∫ κ, (ContinuousLinearMap.compL ℂ W W W (ρ r)) (φ κ • ρ κ) ∂μ := integral_smul _ _
      _ = c r • (ρ r).comp (∫ κ, φ κ • ρ κ ∂μ) := by
          rw [(ContinuousLinearMap.compL ℂ W W W (ρ r)).integral_comp_comm hint]
          rfl
  have hw := congrArg (fun T : W →L[ℂ] W => T w) key
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply] at hw
  exact hw.symm

end GlobalTheory.CompanionTheory.EisMirGen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechConnectingPullNatural
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

noncomputable section

namespace GlobalTheory.CompanionTheory.CechOne

theorem hPull_zero {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}
    (φ : G ⟶ (push f).obj G') (s : G.obj.obj (op ⊤)) :
    hPull f φ 0 ((Sheaf.H.equiv₀ G isTerminalTop).symm s) =
      (Sheaf.H.equiv₀ G' isTerminalTop).symm
        (G'.obj.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op (φ.hom.app (op ⊤) s)) := by
  have hx : (Sheaf.H.equiv₀ G isTerminalTop).symm s =
      GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop ((GlobalTheory.SheafLES.equivZero.{0} G ⊤).symm s) := by
    rw [AddEquiv.symm_apply_eq]
    refine Eq.symm ((GlobalTheory.SiteCoh.equiv₀_terminalEquiv G isTerminalTop _).trans ?_)
    exact (GlobalTheory.SheafLES.equivZero.{0} G ⊤).apply_symm_apply s
  rw [hx, AddEquiv.eq_symm_apply]
  have h1 : hPull f φ 0 (GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop ((GlobalTheory.SheafLES.equivZero.{0} G ⊤).symm s)) =
      GlobalTheory.SiteCoh.terminalEquiv G' 0 isTerminalTop
        (pull.{0, 0} f φ 0 (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤)
          ((GlobalTheory.SheafLES.equivZero.{0} G ⊤).symm s)) := by
    simp only [hPull, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
  rw [h1]
  refine (GlobalTheory.SiteCoh.equiv₀_terminalEquiv G' isTerminalTop _).trans ?_
  refine (SheafPull.equivZero_pull f φ (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤) _).trans ?_
  rw [AddEquiv.apply_symm_apply]

theorem pullCoch_globalCocycle {X Y : TopCat.{0}} (f : X ⟶ Y) {P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (φ : P ⟶ (Opens.map f).op ⋙ Q)
    {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (s : P.obj (op ⊤)) :
    pullCoch f φ V U τ hτ 0 (globalCocycle P V s).1 =
      (globalCocycle Q U (Q.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op
        (φ.app (op ⊤) s))).1 := by
  funext t
  change res Q (inter_le_map f V U τ hτ t) (φ.app (op (inter V (τ ∘ t))) (res P _ s)) =
    res Q _ (Q.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op (φ.app (op ⊤) s))
  rw [app_res_map, res_res]
  change _ = res Q _ (res Q _ (φ.app (op ⊤) s))
  rw [res_res]

theorem cechHOneEquiv_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤)
    (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)} (hS : S.ShortExact) [Injective S.X₂]
    (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : GroundTheory.Arith.SchemeCoh.CechAcyclic S.X₂.obj V) (hS' : S'.ShortExact) [Injective S'.X₂]
    (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : GroundTheory.Arith.SchemeCoh.CechAcyclic S'.X₂.obj U) (α : S ⟶ S'.map (push f))
    (x : GroundTheory.Arith.SchemeCoh.cechH S.X₁.obj V 1) :
    (cechHOneEquiv U hU hS' hC' hI' : GroundTheory.Arith.SchemeCoh.cechH S'.X₁.obj U 1 ≃+ Sheaf.H.{0} S'.X₁ 1) (cechPullH f α.τ₁.hom V U τ hτ 1 x) =
      hPull f α.τ₁ 1 ((cechHOneEquiv V hV hS hC hI : GroundTheory.Arith.SchemeCoh.cechH S.X₁.obj V 1 ≃+ Sheaf.H.{0} S.X₁ 1) x) := by
  obtain ⟨s, hs⟩ := cechOneProj_surjective V hV hC hI x
  rw [← hs]
  have h₁₂ : ∀ W y, α.τ₂.hom.app W (S.f.hom.app W y) = S'.f.hom.app _ (α.τ₁.hom.app W y) := fun W y =>
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun g => g.hom) α.comm₁₂.symm) W) y
  have h₂₃ : ∀ W y, α.τ₃.hom.app W (S.g.hom.app W y) = S'.g.hom.app _ (α.τ₂.hom.app W y) := fun W y =>
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun g => g.hom) α.comm₂₃.symm) W) y
  have hmap : cechPullH f α.τ₁.hom V U τ hτ 1 (cechOneProj V hC s) =
      cechOneProj U hC' (S'.X₃.obj.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op
        (α.τ₃.hom.app (op ⊤) s)) := by
    change cechPullH f α.τ₁.hom V U τ hτ (0 + 1) (hC.delta 0 (globalCocycle S.X₃.obj V s)) =
      hC'.delta 0 (globalCocycle S'.X₃.obj U _)
    refine (GlobalTheory.T.cech_short_exact_pull_compat f V U τ hτ hC hC' α.τ₁.hom α.τ₂.hom α.τ₃.hom h₁₂ h₂₃ 0 _).trans ?_
    exact congrArg (hC'.delta 0) (Subtype.ext (pullCoch_globalCocycle f α.τ₃.hom V U τ hτ s))
  rw [hmap, cechHOneEquiv_cechOneProj, cechHOneEquiv_cechOneProj]
  change H.δ hS' 0 1 rfl ((Sheaf.H.equiv₀ S'.X₃ isTerminalTop).symm _) =
    hPull f α.τ₁ 1 (H.δ hS 0 1 rfl ((Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm s))
  rw [GlobalTheory.T.sheaf_pull_connecting_compat f hS hS' α 0 _]
  exact congrArg (H.δ hS' 0 1 rfl) (hPull_zero f α.τ₃ s).symm

end GlobalTheory.CompanionTheory.CechOne
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechSheafCohomologyPullCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechStep

theorem cechHEquivStep_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) [Injective S.X₂] (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : GroundTheory.Arith.SchemeCoh.CechAcyclic S.X₂.obj V)
    (hS' : S'.ShortExact) [Injective S'.X₂] (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : GroundTheory.Arith.SchemeCoh.CechAcyclic S'.X₂.obj U)
    (α : S ⟶ S'.map (push f)) (m : ℕ) (e : GroundTheory.Arith.SchemeCoh.cechH S.X₃.obj V (m + 1) ≃+ Sheaf.H.{0} S.X₃ (m + 1))
    (e' : GroundTheory.Arith.SchemeCoh.cechH S'.X₃.obj U (m + 1) ≃+ Sheaf.H.{0} S'.X₃ (m + 1))
    (he : ∀ y, e' (cechPullH f α.τ₃.hom V U τ hτ (m + 1) y) = hPull f α.τ₃ (m + 1) (e y))
    (x : GroundTheory.Arith.SchemeCoh.cechH S.X₁.obj V (m + 2)) :
    cechHEquivStep U hS' hC' hI' m e' (cechPullH f α.τ₁.hom V U τ hτ (m + 2) x) =
      hPull f α.τ₁ (m + 2) (cechHEquivStep V hS hC hI m e x) := by
  have h₁₂ : ∀ W z, α.τ₂.hom.app W (S.f.hom.app W z) =
      S'.f.hom.app ((Opens.map f).op.obj W) (α.τ₁.hom.app W z) := fun W z => by
    have h := congrArg (fun k => k.hom.app W) α.comm₁₂
    exact (ConcreteCategory.congr_hom h z).symm
  have h₂₃ : ∀ W z, α.τ₃.hom.app W (S.g.hom.app W z) =
      S'.g.hom.app ((Opens.map f).op.obj W) (α.τ₂.hom.app W z) := fun W z => by
    have h := congrArg (fun k => k.hom.app W) α.comm₂₃
    exact (ConcreteCategory.congr_hom h z).symm
  obtain ⟨y, rfl⟩ := (hC.deltaEquiv hI m).surjective x
  have hδ : (hC'.deltaEquiv hI' m).symm (cechPullH f α.τ₁.hom V U τ hτ (m + 2) (hC.deltaEquiv hI m y)) =
      cechPullH f α.τ₃.hom V U τ hτ (m + 1) y := by
    rw [AddEquiv.symm_apply_eq]
    obtain ⟨σ, hσ, rfl⟩ := GroundTheory.Arith.SchemeCoh.exists_cls y
    exact (GlobalTheory.T.cech_short_exact_pull_compat f V U τ hτ hC hC' α.τ₁.hom α.τ₂.hom α.τ₃.hom h₁₂ h₂₃ (m + 1)
      ⟨σ, (GroundTheory.Arith.SchemeCoh.mem_cocycles σ).2 hσ⟩).trans rfl
  simp only [cechHEquivStep, AddEquiv.trans_apply, AddEquiv.symm_apply_apply, hδ, he]
  exact (GlobalTheory.T.sheaf_pull_connecting_compat f hS hS' α (m + 1) (e y)).symm

end GlobalTheory.CompanionTheory.CechStep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsThetaKernelEqFiltrationOne
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfectAlg

theorem exists_theta_mod {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    ∃ θ : A.Acr n →+* A.Un n, (∀ x : A.W, θ (A.toAcr n x) = Ideal.Quotient.mk _ (A.th x)) ∧
      RingHom.ker θ = A.Fil n 1 := by
  obtain ⟨hsurj, hker, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Untilt.uToQ_main A n
  refine ⟨((Ideal.quotEquivOfEq hker).toRingHom.comp
      (RingHom.quotientKerEquivOfSurjective hsurj).symm.toRingHom).comp
      (Ideal.Quotient.mk (A.Fil n 1)), fun x => ?_, ?_⟩
  · have h1 : A.uToQ n (A.th x) = Ideal.Quotient.mk (A.Fil n 1) (A.toAcr n x) := by rfl
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← h1, ← RingHom.quotientKerEquivOfSurjective_apply_mk hsurj, RingEquiv.symm_apply_apply,
      Ideal.quotEquivOfEq_mk]
  · ext y
    simp only [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [map_eq_zero_iff _ (RingEquiv.injective _), map_eq_zero_iff _ (RingEquiv.injective _),
      Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.CompanionTheory.PerfectAlg
end

