module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0361
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0365
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0351
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0366

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupport
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.TwAvgInd

open GlobalTheory.CompanionTheory.TwistedAverage

theorem exists_finite_average {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    {L : Subgroup G} (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L))
    (x : V) :
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → L) (c : ℂ),
      x - c • ∑ i, twOrbit ρ L θ x (r i) ∈ twKer ρ L θ ∧
      ∀ l : L, ρ (l : G) (c • ∑ i, twOrbit ρ L θ x (r i)) =
        (θ l : ℂ) • (c • ∑ i, twOrbit ρ L θ x (r i)) := by
  classical
  haveI := finiteIndex_stabKer hρ hL θ hθ x
  haveI : Finite (L ⧸ stabKer ρ L θ x) := Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (L ⧸ stabKer ρ L θ x)
  have hn : ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hF : ∀ a b : L, (QuotientGroup.mk a : L ⧸ stabKer ρ L θ x) = QuotientGroup.mk b →
      twOrbit ρ L θ x a = twOrbit ρ L θ x b := by
    intro a b h
    have hm : a⁻¹ * b ∈ stabKer ρ L θ x := QuotientGroup.eq.1 h
    have := twOrbit_mul_right ρ L θ x a _ hm
    rw [mul_inv_cancel_left] at this
    exact this.symm
  refine ⟨L ⧸ stabKer ρ L θ x, inferInstance, Quotient.out,
    ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ)⁻¹, ?_, ?_⟩
  · have e : x - ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ)⁻¹ •
          ∑ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (Quotient.out q) =
        ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ)⁻¹ •
          ∑ q : L ⧸ stabKer ρ L θ x, (x - twOrbit ρ L θ x (Quotient.out q)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_)
    have e2 : x - twOrbit ρ L θ x (Quotient.out q) =
        (-(((θ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)) •
          (ρ ((Quotient.out q : L) : G) x - (θ (Quotient.out q) : ℂ) • x) := by
      rw [twOrbit, smul_sub, smul_smul, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        neg_smul, neg_smul, one_smul]
      abel
    rw [e2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, rfl⟩)
  · intro l
    have h1 : ∀ t : L, ρ (l : G) (twOrbit ρ L θ x t) = (θ l : ℂ) • twOrbit ρ L θ x (l * t) := by
      intro t
      have h0 : θ l * (θ (l * t))⁻¹ = (θ t)⁻¹ := by
        rw [map_mul, mul_inv, mul_inv_cancel_left]
      simp only [twOrbit, map_smul, smul_smul]
      rw [← Units.val_mul, h0, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    have h2 : ∑ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (l * Quotient.out q) =
        ∑ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (Quotient.out q) := by
      let e : Equiv.Perm (L ⧸ stabKer ρ L θ x) := MulAction.toPerm l
      have h3 : ∀ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (l * Quotient.out q) =
          twOrbit ρ L θ x (Quotient.out (e q)) := by
        intro q
        refine hF _ _ ?_
        rw [QuotientGroup.out_eq']
        conv_rhs => rw [← QuotientGroup.out_eq' q]
        rfl
      rw [Finset.sum_congr rfl fun q _ => h3 q]
      exact Equiv.sum_comp e (fun q => twOrbit ρ L θ x (Quotient.out q))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, Finset.sum_congr rfl fun q _ => h1 _, ← Finset.smul_sum, h2,
      smul_comm]

def evalAt {G W : Type} [AddCommGroup W] [Module ℂ W] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G) (τ : Representation ℂ P W)
    (g : G) : smoothPart (ind P τ) →ₗ[ℂ] W :=
  (LinearMap.proj g) ∘ₗ (indSpace P τ).subtype ∘ₗ (smoothPart (ind P τ)).subtype

theorem exists_twisted_average_smInd {G : Type} {W : Type} [AddCommGroup W] [Module ℂ W] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G) (τ : Representation ℂ P W)
    (L : Subgroup G) (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L))
    (f : smoothPart (ind P τ)) :
    ∃ f' : smoothPart (ind P τ), f - f' ∈ twKer (smInd P τ) L θ ∧
      (∀ g, f'.1.1 g ≠ 0 → ∃ l ∈ L, f.1.1 (g * l) ≠ 0) ∧
      ∀ (l : L) (g : G), f'.1.1 (g * l) = (θ l : ℂ) • f'.1.1 g := by
  obtain ⟨ι, _, r, c, h1, h2⟩ :=
    exists_finite_average (smInd P τ) (GlobalTheory.CompanionTheory.BZFun.isSmooth_smInd P τ) hL θ hθ f
  refine ⟨_, h1, ?_, ?_⟩
  · intro g hg
    by_contra hcon
    push_neg at hcon
    apply hg
    have hz : ∀ i, evalAt P τ g (twOrbit (smInd P τ) L θ f (r i)) = 0 := by
      intro i
      have : evalAt P τ g (smInd P τ ((r i : L) : G) f) = 0 := hcon _ (r i).2
      simp only [twOrbit, map_smul, this, smul_zero]
    have : evalAt P τ g (c • ∑ i, twOrbit (smInd P τ) L θ f (r i)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, map_sum, Finset.sum_eq_zero fun i _ => hz i, smul_zero]
    exact this
  · intro l g
    have h3 := congrArg (evalAt P τ g) (h2 l)
    rw [map_smul] at h3
    exact h3

end GlobalTheory.CompanionTheory.TwAvgInd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableT2LocalField
section
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.GLMeasure

open ValuativeRel

theorem secondCountable_t2_local_field (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k ∧ T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  exact ⟨secondCountable_of_proper, inferInstance⟩

theorem secondCountable_GL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) : SecondCountableTopology (GL (Fin n) k) := by
  obtain ⟨_, _⟩ := secondCountable_t2_local_field k
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → k))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) k)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) k)).secondCountableTopology

end GlobalTheory.CompanionTheory.GLMeasure
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Sl2SquareKillsVector
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount

theorem sl2_square_kills : ∀ {n : ℕ} {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (E : Fin n → Fin n → Module.End ℂ Z), Formalism.REAL.GlRel E →
    (∀ x y (f g : Z), ⟪E x y f, g⟫_ℂ = ⟪f, E y x g⟫_ℂ) → ∀ {i j : Fin n}, i ≠ j → ∀ {a : Z}, a ≠ 0 →
    ∀ {p r : ℝ}, E i i a = (p : ℂ) • a → E j j a = (r : ℂ) • a → (∃ m : ℤ, p - r = m) → -1 ≤ p - r →
    (E i j a = 0 ∨ E j i a = 0) → ((E i j) ^ 2) a = 0 := by
  intro n Z _ _ E hG hA i j hij a ha p r hp hr hm hd hor
  have hji : j ≠ i := hij.symm
  have c1 : ∀ v, E i j (E j i v) - E j i (E i j v) = E i i v - E j j v := by
    intro v
    have h := LinearMap.congr_fun (hG i j j i) v
    simpa [Module.End.mul_apply] using h
  have c2 : ∀ v, E i i (E i j v) - E i j (E i i v) = E i j v := by
    intro v
    have h := LinearMap.congr_fun (hG i i i j) v
    simpa [Module.End.mul_apply, hji] using h
  have c3 : ∀ v, E j j (E i j v) - E i j (E j j v) = - E i j v := by
    intro v
    have h := LinearMap.congr_fun (hG j j i j) v
    simpa [Module.End.mul_apply, hji] using h
  have hsq : ((E i j) ^ 2) a = E i j (E i j a) := by
    simp [pow_two, Module.End.mul_apply]
  rw [hsq]
  rcases hor with h | h
  · simp [h]
  have hYX : E j i (E i j a) = ((r : ℂ) - p) • a := by
    have h1 := c1 a
    rw [h, map_zero, hp, hr, zero_sub] at h1
    rw [sub_smul, ← neg_sub ((p : ℂ) • a), ← h1, neg_neg]
  have hn : ‖E i j a‖ ^ 2 = (r - p) * ‖a‖ ^ 2 := by
    have h1 : ⟪E i j a, E i j a⟫_ℂ = ((r : ℂ) - p) * ⟪a, a⟫_ℂ := by
      rw [hA, hYX, inner_smul_right]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
    have h2 : (((‖E i j a‖ ^ 2 : ℝ)) : ℂ) = (((r - p) * ‖a‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      simpa using h1
    exact_mod_cast h2
  have hapos : 0 < ‖a‖ ^ 2 := by positivity
  have hle : 0 ≤ r - p := by
    by_contra hc
    have : (r - p) * ‖a‖ ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.mp hc) hapos
    nlinarith [sq_nonneg ‖E i j a‖]
  obtain ⟨m, hm⟩ := hm
  have hm1 : (-1 : ℤ) ≤ m := by
    have : ((-1 : ℤ) : ℝ) ≤ (m : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hm2 : m ≤ 0 := by
    have : (m : ℝ) ≤ ((0 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hcases : m = 0 ∨ m = -1 := by omega
  rcases hcases with h0 | h0
  · have hpr : r - p = 0 := by rw [h0] at hm; push_cast at hm; linarith
    rw [hpr, zero_mul] at hn
    have h3 : E i j a = 0 := by
      have : ‖E i j a‖ = 0 := by simpa using hn
      exact norm_eq_zero.mp this
    simp [h3]
  · have hpr : r - p = 1 := by rw [h0] at hm; push_cast at hm; linarith
    have hprC : (r : ℂ) - p = 1 := by exact_mod_cast hpr
    have hYX' : E j i (E i j a) = a := by rw [hYX, hprC, one_smul]
    have e1 : E i i (E i j a) = ((p : ℂ) + 1) • E i j a := by
      have h1 := c2 a
      rw [hp, map_smul] at h1
      rw [add_smul, one_smul, add_comm]
      exact sub_eq_iff_eq_add.mp h1
    have e2 : E j j (E i j a) = ((r : ℂ) - 1) • E i j a := by
      have h1 := c3 a
      rw [hr, map_smul] at h1
      rw [sub_smul, one_smul, sub_eq_add_neg, ← h1]
      abel
    have hY2 : E j i (E i j (E i j a)) = 0 := by
      have h1 := c1 (E i j a)
      rw [hYX', e1, e2] at h1
      have h2 : E j i (E i j (E i j a)) =
          (1 - (((p : ℂ) + 1) - ((r : ℂ) - 1))) • E i j a := by
        rw [sub_smul, sub_smul, one_smul, ← h1]
        abel
      have h3 : (1 - (((p : ℂ) + 1) - ((r : ℂ) - 1))) = 0 := by
        linear_combination hprC
      rw [h2, h3, zero_smul]
    have h4 : ⟪E i j (E i j a), E i j (E i j a)⟫_ℂ = 0 := by
      rw [hA, hY2, inner_zero_right]
    exact inner_self_eq_zero.mp h4

end GlobalTheory.CompanionTheory.RealCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothingFundamentalDomainBound
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc

theorem lintegral_sq_le {Y : Type*} [MeasurableSpace Y] (P : Measure Y) [IsProbabilityMeasure P]
    (g : Y → ℝ≥0∞) (hg : AEMeasurable g P) : (∫⁻ y, g y ∂P) ^ 2 ≤ ∫⁻ y, g y ^ 2 ∂P := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hg
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
  have h2 := pow_le_pow_left' h 2
  have h3 : ((∫⁻ y, g y ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))) ^ 2 = ∫⁻ y, g y ^ (2 : ℝ) ∂P := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [h3] at h2
  simpa [ENNReal.rpow_ofNat] using h2

theorem enorm_sub_sm_sq_le (E : Type) [Field E] [NumberField E] (N : ℕ)
    [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)]
    (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (β : archGroup E N → ℝ) (hk : Ker ν β)
    (f : AdelicGLn.AdelicGL E N → ℂ) (hf : Continuous f) (x : AdelicGLn.AdelicGL E N) :
    ‖f x - sm ν β f x‖ₑ ^ 2 ≤ ∫⁻ y, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2
      ∂(ν.withDensity fun y => ENNReal.ofReal (β y)) := by
  have hwm : Measurable fun y => ENNReal.ofReal (β y) := hk.cont.measurable.ennreal_ofReal
  have : IsProbabilityMeasure (ν.withDensity fun y => ENNReal.ofReal (β y)) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hk.cont.integrable_of_hasCompactSupport hk.cpt)
        (Eventually.of_forall hk.nonneg), hk.mass, ENNReal.ofReal_one]
  have hc1 : Continuous fun y => f (x * infEmb E N y) :=
    hf.comp (continuous_const.mul continuous_infEmb)
  have hi1 : Integrable (fun y => (β y : ℂ) * f (x * infEmb E N y)) ν :=
    ((Complex.continuous_ofReal.comp hk.cont).mul hc1).integrable_of_hasCompactSupport
      (hk.cpt.comp_left Complex.ofReal_zero |>.mul_right)
  have hi2 : Integrable (fun y => (β y : ℂ) * f x) ν :=
    ((Complex.continuous_ofReal.comp hk.cont).mul continuous_const).integrable_of_hasCompactSupport
      (hk.cpt.comp_left Complex.ofReal_zero |>.mul_right)
  have hmass : ∫ y, (β y : ℂ) * f x ∂ν = f x := by
    rw [integral_mul_const, integral_complex_ofReal, hk.mass]
    simp
  have heq : f x - sm ν β f x = ∫ y, (β y : ℂ) * (f x - f (x * infEmb E N y)) ∂ν := by
    simp only [mul_sub]
    rw [integral_sub hi2 hi1, hmass]
    rfl
  have hgm : Measurable fun y => ‖f (x * infEmb E N y) - f x‖ₑ :=
    (continuous_enorm.comp (hc1.sub continuous_const)).measurable
  have hle : ‖f x - sm ν β f x‖ₑ ≤ ∫⁻ y, ‖f (x * infEmb E N y) - f x‖ₑ
      ∂(ν.withDensity fun y => ENNReal.ofReal (β y)) := by
    rw [heq, lintegral_withDensity_eq_lintegral_mul ν hwm hgm]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    have hb : ‖(β y : ℂ)‖ₑ = ENNReal.ofReal (β y) := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hk.nonneg y)]
    rw [enorm_mul, hb, enorm_sub_rev]
    rfl
  exact (pow_le_pow_left' hle 2).trans (lintegral_sq_le _ _ hgm.aemeasurable)

end GlobalTheory.CompanionTheory.Conc

theorem GlobalTheory.CompanionTheory.Conc.smNear : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)] (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (F : Set (GA E N)) (β : archGroup E N → ℝ) (c : ℝ≥0∞), IsFundamentalDomain (latticeGL E N) F μ → Ker ν β →
  ∀ f : GA E N → ℂ, Continuous f → (∀ y ∈ tsupport β, ∫⁻ x in F, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2 ∂μ ≤ c) →
  ∫⁻ x in F, ‖f x - sm ν β f x‖ₑ ^ 2 ∂μ ≤ c := by
  intro E _ _ _ N _ _ μ _ _ _ ν _ F β c _ hk f hf hc
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  have : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → Ad E))
  have : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : LocallyCompactSpace (GA E N) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → Ad E))
  have : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (GA E N) := Units.isEmbedding_embedProduct.secondCountableTopology
  have : SigmaCompactSpace (GA E N) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SFinite μ := inferInstance
  have hwm : Measurable fun y => ENNReal.ofReal (β y) := hk.cont.measurable.ennreal_ofReal
  set P : Measure (archGroup E N) := ν.withDensity fun y => ENNReal.ofReal (β y) with hP
  have : IsProbabilityMeasure P := by
    refine ⟨?_⟩
    rw [hP, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hk.cont.integrable_of_hasCompactSupport hk.cpt)
        (Eventually.of_forall hk.nonneg), hk.mass, ENNReal.ofReal_one]
  have hG : Continuous fun p : GA E N × archGroup E N => ‖f (p.1 * infEmb E N p.2) - f p.1‖ₑ ^ 2 :=
    (ENNReal.continuous_pow 2).comp (continuous_enorm.comp
      ((hf.comp (continuous_fst.mul (continuous_infEmb.comp continuous_snd))).sub
        (hf.comp continuous_fst)))
  have hae : ∀ᵐ y ∂P, y ∈ tsupport β := by
    rw [hP, ae_withDensity_iff hwm]
    refine Eventually.of_forall fun y hy => subset_tsupport _ ?_
    intro h0
    exact hy (by rw [h0, ENNReal.ofReal_zero])
  calc ∫⁻ x in F, ‖f x - sm ν β f x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in F, ∫⁻ y, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2 ∂P ∂μ :=
        lintegral_mono fun x => enorm_sub_sm_sq_le E N ν β hk f hf x
    _ = ∫⁻ y, ∫⁻ x in F, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2 ∂μ ∂P :=
        lintegral_lintegral_swap hG.measurable.aemeasurable
    _ ≤ ∫⁻ _, c ∂P := lintegral_mono_ae (hae.mono fun y hy => hc y hy)
    _ = c := by simp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothingLipschitzBound
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc

open scoped Pointwise

theorem sm_lip_of_sq_zero : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ), Ker ν β → ∀ R : ℝ, ∃ (Q₀ : Set (AdelicGLn.AdelicGL K n)) (C : ℝ), IsCompact Q₀ ∧ 0 ≤ C ∧
  ∀ (f : AdelicGLn.AdelicGL K n → ℂ), Continuous f → ∀ g (Y : ArchMatrix K n) (M : ℝ), Y * Y = 0 → ‖Y‖ ≤ R → (∀ q ∈ Q₀, ‖f (g * q)‖ ≤ M) →
    ‖sm ν β f (g * CuspidalSpectrum.archExp Y) - sm ν β f g‖ ≤ C * ‖Y‖ * M := by
  intro K _ _ n _ _ ν _ β hβ R
  obtain ⟨L, hL0, hL⟩ := hβ.lip
  set e : ArchMatrix K n → archGroup K n :=
    fun Y => (isExpLieAlgebra K n).expG ⟨Y, Submodule.mem_top⟩ with he
  have hec : Continuous e :=
    (isExpLieAlgebra K n).continuous_expG.comp (continuous_id.subtype_mk _)
  have hT₀ : IsCompact (tsupport β) := hβ.cpt
  haveI : ProperSpace (ArchMatrix K n) := FiniteDimensional.proper ℝ _
  have hB : IsCompact (e '' Metric.closedBall 0 R) := (isCompact_closedBall 0 R).image hec
  set T : Set (archGroup K n) := tsupport β ∪ (e '' Metric.closedBall 0 R) * tsupport β with hTdef
  have hT : IsCompact T := hT₀.union (hB.mul hT₀)
  obtain ⟨S, hS0, hS⟩ := (hT.image continuous_mat).isBounded.exists_pos_norm_le
  have hne : (tsupport β).Nonempty := by
    rcases Set.eq_empty_or_nonempty (tsupport β) with h0 | h0
    · exfalso
      have hz : ∀ y, β y = 0 := fun y => image_eq_zero_of_notMem_tsupport (by simp [h0])
      have := hβ.mass
      simp [hz] at this
    · exact h0
  refine ⟨infEmb K n '' T, L * S * ν.real T, hT.image continuous_infEmb, by positivity, ?_⟩
  intro f hf g Y M hYY hYR hM
  obtain ⟨t₀, ht₀⟩ := hne
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ ⟨t₀, Or.inl ht₀, rfl⟩)
  set h : archGroup K n → ℂ := fun y => f (g * infEmb K n y) with hh
  have hhc : Continuous h := hf.comp (continuous_const.mul continuous_infEmb)

  have hexp : mat (e Y) = 1 + Y :=
    (CuspidalSpectrum.coe_expG_top Y).trans (CuspidalSpectrum.exp_eq_one_add_of_mul_self_eq_zero hYY)
  have hmul : ∀ a b : archGroup K n, mat (a * b) = mat a * mat b := fun _ _ => rfl
  have hinv : mat (e Y)⁻¹ = 1 - Y := by
    have h1 : mat (e Y) * (1 - Y) = 1 := by
      have : (1 + Y) * (1 - Y) = 1 - Y * Y := by noncomm_ring
      rw [hexp, this, hYY, sub_zero]
    have h2 : mat (e Y)⁻¹ * mat (e Y) = 1 := by
      rw [← hmul, inv_mul_cancel]; rfl
    calc mat (e Y)⁻¹ = mat (e Y)⁻¹ * (mat (e Y) * (1 - Y)) := by rw [h1, mul_one]
      _ = 1 - Y := by rw [← mul_assoc, h2, one_mul]

  have hz2 : ∀ u, u ∉ T → β u = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport fun hc => hu (Or.inl hc)
  have hz1 : ∀ u, u ∉ T → β ((e Y)⁻¹ * u) = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport fun hc => hu (Or.inr
      ⟨e Y, ⟨Y, by simpa using hYR, rfl⟩, _, hc, by simp⟩)
  set F₁ : archGroup K n → ℂ := fun u => (β ((e Y)⁻¹ * u) : ℂ) * h u with hF₁
  set F₂ : archGroup K n → ℂ := fun u => (β u : ℂ) * h u with hF₂
  have hF₁c : Continuous F₁ :=
    (Complex.continuous_ofReal.comp (hβ.cont.comp (continuous_const.mul continuous_id))).mul hhc
  have hF₂c : Continuous F₂ := (Complex.continuous_ofReal.comp hβ.cont).mul hhc
  have hF₁z : ∀ u, u ∉ T → F₁ u = 0 := fun u hu => by simp [hF₁, hz1 u hu]
  have hF₂z : ∀ u, u ∉ T → F₂ u = 0 := fun u hu => by simp [hF₂, hz2 u hu]
  have hF₁i : Integrable F₁ ν :=
    hF₁c.integrable_of_hasCompactSupport (HasCompactSupport.intro hT hF₁z)
  have hF₂i : Integrable F₂ ν :=
    hF₂c.integrable_of_hasCompactSupport (HasCompactSupport.intro hT hF₂z)
  have hsm1 : sm ν β f (g * CuspidalSpectrum.archExp Y) = ∫ u, F₁ u ∂ν := by
    rw [← integral_mul_left_eq_self (μ := ν) F₁ (e Y)]
    unfold sm
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hF₁, hh, inv_mul_cancel_left, map_mul]
    rw [CuspidalSpectrum.archExp, mul_assoc]
  have hsm2 : sm ν β f g = ∫ u, F₂ u ∂ν := rfl
  rw [hsm1, hsm2, ← integral_sub hF₁i hF₂i,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := T)
      (fun u hu => by rw [hF₁z u hu, hF₂z u hu, sub_zero])]
  have hpt : ∀ u ∈ T, ‖F₁ u - F₂ u‖ ≤ L * S * ‖Y‖ * M := by
    intro u hu
    have hd : F₁ u - F₂ u = ((β ((e Y)⁻¹ * u) - β u : ℝ) : ℂ) * h u := by
      simp only [hF₁, hF₂]; push_cast; ring
    have hm : mat ((e Y)⁻¹ * u) - mat u = -(Y * mat u) := by
      rw [hmul, hinv]; noncomm_ring
    have h1 : |β ((e Y)⁻¹ * u) - β u| ≤ L * (‖Y‖ * S) := by
      refine (hL _ _).trans (mul_le_mul_of_nonneg_left ?_ hL0)
      rw [hm, norm_neg]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hS _ ⟨u, hu, rfl⟩) (norm_nonneg _))
    have h2 : ‖h u‖ ≤ M := hM _ ⟨u, hu, rfl⟩
    rw [hd, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |β ((e Y)⁻¹ * u) - β u| * ‖h u‖ ≤ (L * (‖Y‖ * S)) * M :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = L * S * ‖Y‖ * M := by ring
  have := norm_setIntegral_le_of_norm_le_const (μ := ν) (s := T) hT.measure_lt_top hpt
  refine this.trans (le_of_eq ?_)
  ring

end GlobalTheory.CompanionTheory.Conc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedInvariantSmallBoxesStatement
section
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_invariant_small_boxes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (χ : Multiplicative (Fin n → k) →* ℂˣ) (v : V), v ∈ twKer ρ ⊤ (χ.comp (⊤ : Subgroup (Multiplicative (Fin n → k))).subtype) → ∃ j : ℤ, ∀ j' ≤ j, v ∈ twKer ρ (box k n j') (χ.comp (box k n j').subtype) := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_mem_twKer_box | exact GlobalTheory.CompanionTheory.MirFourier.exists_mem_twKer_box | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_mem_twKer_box <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformTwistedInvarianceOnBallStatement
section
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_twisted_invariance_on_ball : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (v : V) (M : ℤ), (∀ a : Fin n → k, ∃ j : ℤ, ∀ j' ≤ j, v ∈ twKer ρ (box k n j') (chiOn k ψ a (box k n j'))) → ∃ J : ℤ, ∀ J' ≤ J, ∀ a : Fin n → k, (∀ i, a i ∈ valBall k M) → v ∈ twKer ρ (box k n J') (chiOn k ψ a (box k n J')) := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_box_forall_chi | exact GlobalTheory.CompanionTheory.MirFourier.exists_box_forall_chi | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_box_forall_chi <;> assumption)
end

