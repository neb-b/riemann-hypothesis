module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalIntegersTensorCoordsPrimeToDiscriminant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FixedUnitNorm.Coords

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem isIntegral_of_trace_norm (w : E) (t n : 𝓞 F) (ht : w + σ w = algebraMap F E t)
    (hn : w * σ w = algebraMap F E n) : IsIntegral ℤ w := by
  have hE : IsIntegral (𝓞 E) w := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (algebraMap (𝓞 F) (𝓞 E) t) * Polynomial.X +
      Polynomial.C (algebraMap (𝓞 F) (𝓞 E) n), by monicity!, ?_⟩
    have h1 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t) = algebraMap F E t := rfl
    have h2 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) n) = algebraMap F E n := rfl
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, h1, h2, ← ht, ← hn]
    ring
  exact isIntegral_trans (R := ℤ) w hE

theorem exists_coords (h : IsCMExt F E σ) (w : E) (t n : 𝓞 F) (ht : w + σ w = algebraMap F E t)
    (hn : w * σ w = algebraMap F E n) (x : 𝓞 E) :
    ∃ a b : 𝓞 F, (x : E) * algebraMap F E ((t ^ 2 - 4 * n : 𝓞 F) : F) =
      algebraMap F E a + algebraMap F E b * w := by
  have hσ := GlobalTheory.SelfDualLatticeCompare.conj_conj h
  let W : 𝓞 E := ⟨w, isIntegral_of_trace_norm w t n ht hn⟩
  let s : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)
  have hs : ∀ y : 𝓞 E, ((s y : 𝓞 E) : E) = σ y := fun _ => rfl
  have hW : ((W : 𝓞 E) : E) = w := rfl
  obtain ⟨a, ha⟩ := GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h
    ((s x * W - x * s W) * (W - s W)) (by
      change σ ((σ (x : E) * w - (x : E) * σ w) * (w - σ w)) = (σ (x : E) * w - (x : E) * σ w) * (w - σ w)
      simp only [map_mul, map_sub, hσ]
      ring)
  obtain ⟨b, hb⟩ := GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h
    ((x - s x) * (W - s W)) (by
      change σ (((x : E) - σ x) * (w - σ w)) = ((x : E) - σ x) * (w - σ w)
      simp only [map_mul, map_sub, hσ]
      ring)
  have ha' : algebraMap F E a = (σ x * w - x * σ w) * (w - σ w) := by
    exact congrArg (algebraMap (𝓞 E) E) ha
  have hb' : algebraMap F E b = (x - σ x) * (w - σ w) := by
    exact congrArg (algebraMap (𝓞 E) E) hb
  refine ⟨a, b, ?_⟩
  have hd : algebraMap F E ((t ^ 2 - 4 * n : 𝓞 F) : F) = (algebraMap F E t) ^ 2 - 4 * algebraMap F E n := by
    push_cast
    simp [map_sub, map_pow, map_mul, map_ofNat]
  rw [hd, ha', hb', ← ht, ← hn]
  ring

theorem tmul_move {K : Type} [Field K] [Algebra F K] (m : K) (r : F) (e : E) :
    (algebraMap F K r * m) ⊗ₜ[F] e = m ⊗ₜ[F] (algebraMap F E r * e) := by
  rw [← Algebra.smul_def, ← Algebra.smul_def, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]

theorem coords_add {K : Type} [Field K] [Algebra F K] (a b a' b' : K) (w : E) :
    (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] w) + (a' ⊗ₜ[F] (1 : E) + b' ⊗ₜ[F] w) = (a + a') ⊗ₜ[F] (1 : E) + (b + b') ⊗ₜ[F] w := by
  rw [TensorProduct.add_tmul, TensorProduct.add_tmul, add_add_add_comm]

theorem coords_neg {K : Type} [Field K] [Algebra F K] (a b : K) (w : E) :
    -(a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] w) = (-a) ⊗ₜ[F] (1 : E) + (-b) ⊗ₜ[F] w := by
  rw [TensorProduct.neg_tmul, TensorProduct.neg_tmul, neg_add]

end Field

end GlobalTheory.FixedUnitNorm.Coords

namespace GlobalTheory.FixedUnitNorm.Coords


set_option maxHeartbeats 1000000 in
theorem mem_intV_coords : ∀ (D : D7) (v : Pl D) (w : D.host.E) (t n : 𝓞 D.host.F),
    w + D.sp.cm.sig w = algebraMap D.host.F D.host.E t → w * D.sp.cm.sig w = algebraMap D.host.F D.host.E n →
    t ^ 2 - 4 * n ∉ v.asIdeal → ∀ z ∈ intV D v, ∃ a ∈ v.adicCompletionIntegers D.host.F,
      ∃ b ∈ v.adicCompletionIntegers D.host.F, z = a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w := by
  intro D v w t n ht hn hv z hz
  have hcm := GlobalTheory.AdelicU.isCMExt_host D
  have hcoe : ∀ r : 𝓞 D.host.F, ((algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) r :
      v.adicCompletionIntegers D.host.F) : Fv D.host.F v) = algebraMap D.host.F (Fv D.host.F v) (r : D.host.F) :=
    fun r => rfl
  have hmem : ∀ r : 𝓞 D.host.F, algebraMap D.host.F (Fv D.host.F v) (r : D.host.F) ∈
      v.adicCompletionIntegers D.host.F := fun r => hcoe r ▸ (algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) r).2
  obtain ⟨u, hu⟩ := ((GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (t ^ 2 - 4 * n)).2 hv).exists_left_inv
  set U : Fv D.host.F v := ((u : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) with hU
  have hu' : U * algebraMap D.host.F (Fv D.host.F v) ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) = 1 := by
    have := congrArg (fun y : v.adicCompletionIntegers D.host.F => (y : Fv D.host.F v)) hu
    rw [MulMemClass.coe_mul, hcoe, OneMemClass.coe_one] at this
    exact this
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, x, rfl⟩ := hy
    obtain ⟨a, b, hab⟩ := exists_coords hcm w t n ht hn x
    refine ⟨c * U * algebraMap D.host.F (Fv D.host.F v) (a : D.host.F), mul_mem (mul_mem hc u.2) (hmem a),
      c * U * algebraMap D.host.F (Fv D.host.F v) (b : D.host.F), mul_mem (mul_mem hc u.2) (hmem b), ?_⟩
    have hc' : c = algebraMap D.host.F (Fv D.host.F v) ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) * (c * U) := by
      rw [mul_comm, mul_assoc, hu', mul_one]
    calc c ⊗ₜ[D.host.F] (x : D.host.E)
        = (algebraMap D.host.F (Fv D.host.F v) ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) * (c * U)) ⊗ₜ[D.host.F]
            (x : D.host.E) := by rw [← hc']
      _ = (c * U) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) * x) :=
          tmul_move _ _ _
      _ = (c * U) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (a : D.host.F) * 1 +
            algebraMap D.host.F D.host.E (b : D.host.F) * w) := by rw [mul_comm (algebraMap D.host.F D.host.E _) (x : D.host.E), hab, mul_one]
      _ = (algebraMap D.host.F (Fv D.host.F v) (a : D.host.F) * (c * U)) ⊗ₜ[D.host.F] (1 : D.host.E) +
            (algebraMap D.host.F (Fv D.host.F v) (b : D.host.F) * (c * U)) ⊗ₜ[D.host.F] w := by
          rw [TensorProduct.tmul_add, tmul_move, tmul_move]
      _ = _ := by rw [mul_comm (algebraMap D.host.F (Fv D.host.F v) (a : D.host.F)),
            mul_comm (algebraMap D.host.F (Fv D.host.F v) (b : D.host.F))]
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add y y' _ _ h h' =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    obtain ⟨a', ha', b', hb', rfl⟩ := h'
    refine ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', ?_⟩
    exact coords_add a b a' b' w
  | neg y _ h =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    refine ⟨-a, neg_mem ha, -b, neg_mem hb, ?_⟩
    exact coords_neg a b w

end GlobalTheory.FixedUnitNorm.Coords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanValueIneqRightTranslateRealPointNearOne
section
noncomputable section

namespace GlobalTheory.CuspGeo.MeanValue

section Abstract

open GlobalTheory.SmoothForms

variable {L G ι : Type} [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] [Fintype ι]

theorem norm_sub_le (e : L → G) (he0 : e 0 = 1) (he : ∀ (Z : L) (s t : ℝ), e ((s + t) • Z) = e (s • Z) * e (t • Z))
    (b : Module.Basis ι ℝ L) {φ : G → ℂ} (hφ : Sm e φ) (g : G) (Z : L) (a : ℝ) (ha : ∀ i, |b.repr Z i| ≤ a) (c : ι → ℝ)
    (hc : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Der e (b i) φ (g * e (t • Z))‖ ≤ c i) :
    ‖φ (g * e Z) - φ g‖ ≤ a * ∑ i, c i := by
  have hc0 : ∀ i, 0 ≤ c i := fun i => (norm_nonneg _).trans (hc i 0 ⟨le_refl 0, zero_le_one⟩)

  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (g * e (s • Z)))
      (fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) ((t - t) • Z) Z) t := by
    intro t
    have hF : Differentiable ℝ (fun X : L => φ (g * e (t • Z) * e X)) :=
      (hφ (g * e (t • Z))).differentiable (by simp)
    have h1 : HasDerivAt (fun s : ℝ => (s - t) • Z) ((1 : ℝ) • Z) t :=
      ((hasDerivAt_id' t).sub_const t).smul_const Z
    rw [one_smul] at h1
    have h2 := (hF ((t - t) • Z)).hasFDerivAt.comp_hasDerivAt t h1
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show φ (g * e (s • Z)) = φ (g * e (t • Z) * e ((s - t) • Z))
    rw [mul_assoc, ← he, show t + (s - t) = s by ring]

  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) 0 Z‖ ≤ a * ∑ i, c i := by
    intro t ht
    set F' := fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) 0 with hF'
    have hZ : F' Z = ∑ i, b.repr Z i • F' (b i) := by
      have : F' Z = F' (∑ i, b.repr Z i • b i) := by rw [b.sum_repr]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, map_sum]
      simp only [map_smul]
    rw [hZ, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    have hi : ‖F' (b i)‖ ≤ c i := by
      have := hc i t ht
      rwa [DerLinear.der_eq_fderiv hφ] at this
    exact mul_le_mul (ha i) hi (norm_nonneg _) ((abs_nonneg _).trans (ha i))
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => φ (g * e (s • Z))) (fun t _ => (hderiv t).hasDerivWithinAt)
    (fun t ht => by
      rw [sub_self, zero_smul]
      exact key t (Set.Ico_subset_Icc_self ht))
  simpa [he0] using hmv

theorem exists_coord_bound (b : Module.Basis ι ℝ L) : ∃ K : ℝ, 0 ≤ K ∧ ∀ Z i, |b.repr Z i| ≤ K * ‖Z‖ := by
  have : FiniteDimensional ℝ L := Module.Finite.of_basis b
  let f : ι → L →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  refine ⟨∑ i, ‖f i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun Z i => ?_⟩
  have h1 : |b.repr Z i| = ‖f i Z‖ := by
    simp [f, Real.norm_eq_abs]
  rw [h1]
  exact ((f i).le_opNorm Z).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => norm_nonneg (f j)) (Finset.mem_univ i)) (norm_nonneg Z))

end Abstract

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem expInf_zero (R : RealPoints θ V) : expInf θ V 0 = 1 := by
  have hE := isExpFam_expInf R
  refine R.2.2.1 _ (hE (0 : LieN V)).1 _ (GinfC V).one_mem fun τ => ?_
  rw [(hE (0 : LieN V)).2 τ, R.2.2.2.2.1 1 (GfC V).one_mem τ]
  show NormedSpace.exp (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) = 1
  exact NormedSpace.exp_zero

theorem expInf_add (R : RealPoints θ V) (Z : LieN V) (s t : ℝ) :
    expInf θ V ((s + t) • Z) = expInf θ V (s • Z) * expInf θ V (t • Z) := by
  have hE := isExpFam_expInf R
  refine R.2.2.1 _ (hE ((s + t) • Z)).1 _ (mul_mem (hE (s • Z)).1 (hE (t • Z)).1) fun τ => ?_
  rw [R.2.2.2.1, (hE ((s + t) • Z)).2 τ, (hE (s • Z)).2 τ, (hE (t • Z)).2 τ]
  show NormedSpace.exp ((s + t) • (Z τ).1) = NormedSpace.exp (s • (Z τ).1) * NormedSpace.exp (t • (Z τ).1)
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl (Z τ).1).smul_right t).smul_left s)

theorem continuous_expInf (hθ : IsInfFam θ) (R : RealPoints θ V) : Continuous (expInf θ V) := by
  have H := isLieData R
  have h1 : Continuous fun X : LieN V => NormedSpace.exp (jInf V X) :=
    (DerLinear.contDiff_exp H).continuous
  exact (GlobalTheory.Mem.DerClosed.continuousOn_secInf hθ V).comp_continuous h1 fun X => DerLinear.exp_unitary H X


open Classical in
theorem exists_basis (V : HSp D) : ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ (LieN V)) (p : ι → D.what₂.Tau)
    (X : ∀ i, LieAt V (p i)), ∀ i, b i = atPlace V (p i) (X i) := by
  refine ⟨Σ τ, Fin (Module.finrank ℝ (lieU (gramAt D V τ)).toSubmodule), inferInstance,
    Pi.basis fun τ => Module.finBasis ℝ (lieU (gramAt D V τ)).toSubmodule, fun i => i.1,
    fun i => ⟨(Module.finBasis ℝ (lieU (gramAt D V i.1)).toSubmodule i.2).1,
      (Module.finBasis ℝ (lieU (gramAt D V i.1)).toSubmodule i.2).2⟩, fun i => ?_⟩
  exact (Pi.basis_apply _ i).trans rfl

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem norm_lieN_le (Z : LieN V) {r : ℝ} (hr : 0 ≤ r) (h : ∀ τ i j, ‖(Z τ).1 i j‖ ≤ r) : ‖Z‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg hr).2 fun τ => ?_
  rw [Submodule.coe_norm]
  exact (Matrix.norm_le_iff hr).2 (h τ)

end

theorem exists_log (hθ : IsInfFam θ) (R : RealPoints θ V) : ∃ δ₁ C : ℝ, 0 < δ₁ ∧ 0 ≤ C ∧
    ∀ (u : GA D V) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseR θ V u δ → ∃ Z : LieN V, expInf θ V Z = u ∧ ‖Z‖ ≤ C * δ := by
  have hG : ∀ τ, IsUnit (gramAt D V τ).det := fun τ => (R.1 τ).2
  choose δτ Cτ hδτ hτ using fun τ => GlobalTheory.T.exists_log_near_one_unitaryGroup_of_form_linear_bound V.rank (gramAt D V τ) (hG τ)
  obtain ⟨δ₁, hδ₁, hle⟩ : ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ τ, δ₁ ≤ δτ τ := by
    rcases isEmpty_or_nonempty D.what₂.Tau with h | h
    · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
    · obtain ⟨τ₀, hτ₀⟩ := Finite.exists_min δτ
      exact ⟨δτ τ₀, hδτ τ₀, hτ₀⟩
  have hC : ∀ τ, Cτ τ ≤ ∑ τ', |Cτ τ'| := fun τ =>
    (le_abs_self _).trans (Finset.single_le_sum (fun τ' _ => abs_nonneg (Cτ τ')) (Finset.mem_univ τ))
  refine ⟨δ₁, ∑ τ, |Cτ τ|, hδ₁, Finset.sum_nonneg fun τ _ => abs_nonneg _, fun u δ hδ hδle hu => ?_⟩

  have hX : ∀ τ, ∃ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 ∧
      NormedSpace.exp X = infMat D.sp.cm.sig V.gram (θ τ) u ∧ ∀ i j, ‖X i j‖ ≤ Cτ τ * δ := fun τ =>
    hτ τ _ δ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V u τ) (hδle.trans (hle τ)) (hu.2 τ)
  choose X hXl hXe hXn using hX
  let Z : LieN V := fun τ => ⟨X τ, (mem_lieAt_iff τ (X τ)).1 (hXl τ)⟩
  refine ⟨Z, ?_, ?_⟩
  · have hE := isExpFam_expInf R
    refine R.2.2.1 _ (hE Z).1 _ hu.1 fun τ => ?_
    rw [(hE Z).2 τ]
    exact hXe τ
  · refine norm_lieN_le Z (mul_nonneg (Finset.sum_nonneg fun τ _ => abs_nonneg _) hδ) fun τ i j => ?_
    exact (hXn τ i j).trans (mul_le_mul_of_nonneg_right (hC τ) hδ)

theorem mean_value : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ V : HSp D, ∃ (B : Finset (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (Ω : Set (GA D V)) (C δ₁ : ℝ), (∀ p ∈ B, p.2 ∈ lieAt V p.1) ∧ IsCompact Ω ∧ 0 < δ₁ ∧ 0 ≤ C ∧ ∀ ψ : GA D V → ℂ, SmoothW θ V ψ → ∀ (g u : GA D V) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseR θ V u δ → ∀ c : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → ℝ, (∀ p ∈ B, ∀ w ∈ Ω, ‖Rder θ V p.1 p.2 ψ (g * w)‖ ≤ c p) → ‖ψ (g * u) - ψ g‖ ≤ C * δ * ∑ p ∈ B, c p := by
  intro D θ hθ V
  classical
  have R : RealPoints θ V := (RealPts.realPoints D).2 θ hθ V
  obtain ⟨ι, hι, b, p, X, hb⟩ := exists_basis V
  obtain ⟨K, hK, hKb⟩ := exists_coord_bound b
  obtain ⟨δ₁, C₀, hδ₁, hC₀, hlog⟩ := exists_log hθ R
  have : FiniteDimensional ℝ (LieN V) := Module.Finite.of_basis b
  set B := Finset.univ.image fun i => (p i, (X i).1) with hB
  have hmemB : ∀ i, (p i, (X i).1) ∈ B := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have h0 : expInf θ V 0 ∈ expInf θ V '' Metric.closedBall 0 (C₀ * δ₁) :=
    ⟨0, Metric.mem_closedBall_self (mul_nonneg hC₀ hδ₁.le), rfl⟩
  refine ⟨B, expInf θ V '' Metric.closedBall 0 (C₀ * δ₁), K * C₀ * Fintype.card ι, δ₁, ?_, ?_, hδ₁,
    mul_nonneg (mul_nonneg hK hC₀) (Nat.cast_nonneg _), ?_⟩
  · intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq
    exact (mem_lieAt_iff _ _).2 (X i).2
  · exact (isCompact_closedBall 0 _).image (continuous_expInf hθ R)
  · intro ψ hψ g u δ hδ hδle hu c hc
    obtain ⟨Z, rfl, hZ⟩ := hlog u δ hδ hδle hu
    have hsm : Sm (expInf θ V) ψ := (isSmoothInf_iff ψ).1 ((smooth_iff R ψ).1 hψ)
    have hcn : ∀ q ∈ B, 0 ≤ c q := fun q hq => (norm_nonneg _).trans (hc q hq _ h0)
    have ha : ∀ i, |b.repr Z i| ≤ K * (C₀ * δ) := fun i =>
      (hKb Z i).trans (mul_le_mul_of_nonneg_left hZ hK)
    have hder : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖Der (expInf θ V) (b i) ψ (g * expInf θ V (t • Z))‖ ≤ c (p i, (X i).1) := by
      intro i t ht
      rw [hb i, ← lieDer_eq, ← Rder_eq R]
      refine hc _ (hmemB i) _ ⟨t • Z, ?_, rfl⟩
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖Z‖ ≤ 1 * (C₀ * δ) := mul_le_mul ht.2 hZ (norm_nonneg _) zero_le_one
        _ ≤ C₀ * δ₁ := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hδle hC₀
    have key := norm_sub_le (expInf θ V) (expInf_zero R) (expInf_add R) b hsm g Z (K * (C₀ * δ)) ha
      (fun i => c (p i, (X i).1)) hder
    have hsum : ∑ i, c (p i, (X i).1) ≤ Fintype.card ι * ∑ q ∈ B, c q := by
      calc ∑ i, c (p i, (X i).1) ≤ ∑ _i : ι, ∑ q ∈ B, c q :=
            Finset.sum_le_sum fun i _ => Finset.single_le_sum hcn (hmemB i)
        _ = Fintype.card ι * ∑ q ∈ B, c q := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc ‖ψ (g * expInf θ V Z) - ψ g‖ ≤ K * (C₀ * δ) * ∑ i, c (p i, (X i).1) := key
      _ ≤ K * (C₀ * δ) * (Fintype.card ι * ∑ q ∈ B, c q) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hK (mul_nonneg hC₀ hδ))
      _ = K * C₀ * Fintype.card ι * δ * ∑ q ∈ B, c q := by ring

end GlobalTheory.CuspGeo.MeanValue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuasiMeasurePreservingSkewHermitianCongruenceUni
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.SkewConjQmp

theorem skewConj_matMul {D : D7} {ρ : ℕ} (a b : Mx D ρ ρ) (c : skewA D ρ) :
    skewConj (a ⬝ b) c = skewConj a (skewConj b c) := by
  apply Subtype.ext
  simp only [skewConj, adj_mul, Matrix.mul_assoc]

theorem skewConj_matOne {D : D7} {ρ : ℕ} (c : skewA D ρ) : skewConj (1 : Mx D ρ ρ) c = c := by
  apply Subtype.ext
  simp only [skewConj, adj_one, Matrix.one_mul, Matrix.mul_one]

theorem skewConj_addArg {D : D7} {ρ : ℕ} (a : Mx D ρ ρ) (c d : skewA D ρ) :
    skewConj a (c + d) = skewConj a c + skewConj a d := by
  apply Subtype.ext
  simp only [skewConj, AddSubgroup.coe_add, Matrix.mul_add, Matrix.add_mul]

theorem continuous_skewConj_arg {D : D7} {ρ : ℕ} (a : Mx D ρ ρ) : Continuous (skewConj a : skewA D ρ → skewA D ρ) := by
  have h1 : Continuous fun c : skewA D ρ => (a ⬝ c.1 : Mx D ρ ρ) := continuous_const.matrix_mul continuous_subtype_val
  have h2 : Continuous fun c : skewA D ρ => (a ⬝ c.1 ⬝ adj a : Mx D ρ ρ) := h1.matrix_mul continuous_const
  exact Continuous.subtype_mk h2 _

noncomputable def skewConjEquiv {D : D7} {ρ : ℕ} (g : GL (Fin ρ) (AE D)) : skewA D ρ ≃+ skewA D ρ where
  toFun := skewConj g.val
  invFun := skewConj (g⁻¹).val
  left_inv c := by
    rw [← skewConj_matMul]
    have : (g⁻¹).val ⬝ g.val = 1 := Units.inv_mul g
    rw [this, skewConj_matOne]
  right_inv c := by
    rw [← skewConj_matMul]
    have : g.val ⬝ (g⁻¹).val = 1 := Units.mul_inv g
    rw [this, skewConj_matOne]
  map_add' := skewConj_addArg _


set_option synthInstance.maxHeartbeats 200000 in
theorem quasiMeasurePreserving_skewConj : ∀ (D : D7) (ρ : ℕ) (lC : Measure (skewA D ρ)), lC.IsAddHaarMeasure →
    ∀ u : UX D ρ, Measure.QuasiMeasurePreserving (skewConj u.1.1) lC lC := by
  intro D ρ lC hC u
  obtain ⟨a1, a2, a3, a4, -⟩ := lattice_Mx D ρ ρ
  have : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  have hcl : IsClosed (skewA D ρ : Set (Mx D ρ ρ)) := isClosed_eq continuous_adj continuous_neg
  have : LocallyCompactSpace (skewA D ρ) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : IsTopologicalAddGroup (skewA D ρ) := inferInstance
  have : SecondCountableTopology (skewA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  have hc := continuous_skewConj_arg (u.1.1 : Mx D ρ ρ)
  have hH : (lC.map (skewConj u.1.1)).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map lC (skewConjEquiv u.1) hc
      (continuous_skewConj_arg (u.1⁻¹).val)
  refine ⟨hc.measurable.aemeasurable, ?_⟩
  exact Measure.absolutelyContinuous_isAddHaarMeasure _ _

end GlobalTheory.Unf.SkewConjQmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RapidDecRTrans
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.RTransDecay

theorem rapidDec_rTrans : ∀ (D : D7) (V : HSp D) (G : GA D V → ℂ), RapidDec V G → (∀ h, RapidDec V (rTrans h G)) ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ g h, ‖G (g * h)‖ * quotHeight V g ^ N ≤ C * height V h ^ N := by
  intro D V G hG
  refine ⟨fun h => hG.mul_right h, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hG.decay N
  refine ⟨C, fun g h => ?_⟩
  have h1 : GlobalTheory.Grow.quotHeight V g ≤ GlobalTheory.Grow.quotHeight V (g * h) * GlobalTheory.Grow.height V h := by
    simpa using GlobalTheory.Grow.quotHeight_mul_le V (g * h) h⁻¹
  calc ‖G (g * h)‖ * GlobalTheory.Grow.quotHeight V g ^ N
        ≤ ‖G (g * h)‖ * (GlobalTheory.Grow.quotHeight V (g * h) * GlobalTheory.Grow.height V h) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (GlobalTheory.Grow.quotHeight_pos V g).le h1 N) (norm_nonneg _)
    _ = ‖G (g * h)‖ * GlobalTheory.Grow.quotHeight V (g * h) ^ N * GlobalTheory.Grow.height V h ^ N := by ring
    _ ≤ C * GlobalTheory.Grow.height V h ^ N := mul_le_mul_of_nonneg_right (hC _) (pow_pos (GlobalTheory.Grow.height_pos V h) N).le

end GlobalTheory.RTransDecay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalUnitarySubgroupCountableDiscreteFundDoma
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.RationalSubgroupFund

theorem countable_discrete_exists_fundamentalDomain : ∀ (D : D7) (W : HSp D) (Γ : Subgroup (GA D W)), Γ ≤ GQ W → Countable Γ ∧ DiscreteTopology Γ ∧ ∀ μ : Measure (GA D W), μ.IsHaarMeasure → ∃ 𝓑 : Set (GA D W), IsFundamentalDomain Γ 𝓑 μ := by
  intro D W Γ hΓ
  obtain ⟨_, h2, _, h4, h5, h6, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  haveI := h2; haveI := h4; haveI := h5; haveI := h6
  haveI hdisc : DiscreteTopology Γ :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : Γ => (⟨(x : GA D W), hΓ x.2⟩ : GQ W))
      (continuous_subtype_val.subtype_mk _)
      (fun x y hxy => Subtype.ext (by simpa using congrArg Subtype.val hxy))
  obtain ⟨hc, 𝓓, h𝓓m, h𝓓⟩ := GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain Γ
  haveI := hc
  refine ⟨hc, hdisc, fun μ _ => ⟨𝓓, ?_⟩⟩
  exact IsFundamentalDomain.mk' h𝓓m.nullMeasurableSet (fun g => h𝓓 g)

end GlobalTheory.RationalSubgroupFund
end

