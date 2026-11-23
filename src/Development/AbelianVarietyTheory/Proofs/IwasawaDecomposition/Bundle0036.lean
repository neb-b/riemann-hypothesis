module

public import Mathlib
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatCongruenceLeOpenSubgroupGL
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory

theorem valued_absNorm_lt_one_adicCompletion (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) < 1 := by
  have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v
    ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2 (Ideal.absNorm_mem _)
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  convert h using 2
  have : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) : F) := by simp
  rw [this]
  rfl

theorem exists_nat_congruence_le_open_subgroup_GL :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (K : Subgroup (GL (Fin n) (v.adicCompletion F))), IsOpen (K : Set (GL (Fin n) (v.adicCompletion F))) →
    ∃ M : ℕ, 0 < M ∧ ∀ g : GL (Fin n) (v.adicCompletion F),
      (∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤
        Valued.v ((M : v.adicCompletion F))) →
      (∀ i j, Valued.v (((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j -
        (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ Valued.v ((M : v.adicCompletion F))) → g ∈ K := by
  intro F _ _ v n K hK
  by_contra hcon
  push Not at hcon
  set q : ℕ := Ideal.absNorm v.asIdeal with hq
  have hq0 : 0 < q := lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)
  choose g hg1 hg2 hg3 using fun k : ℕ => hcon (q ^ k) (pow_pos hq0 k)
  have hlt : ‖(q : v.adicCompletion F)‖ < 1 :=
    Valued.toNormedField.norm_lt_one_iff.2 (valued_absNorm_lt_one_adicCompletion F v)
  have hpow : Filter.Tendsto (fun k : ℕ => ‖((q ^ k : ℕ) : v.adicCompletion F)‖)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt
  have key : ∀ A : ℕ → Matrix (Fin n) (Fin n) (v.adicCompletion F),
      (∀ k i j, Valued.v (A k i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤
        Valued.v ((q ^ k : ℕ) : v.adicCompletion F)) →
      Filter.Tendsto A Filter.atTop (nhds 1) := by
    intro A hA
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun k => Valued.toNormedField.norm_le_iff.2 (hA k i j)) hpow
  have hlim : Filter.Tendsto g Filter.atTop (nhds 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine Filter.Tendsto.prodMk_nhds (key _ hg1) ?_
    exact (MulOpposite.continuous_op.tendsto _).comp (key _ hg2)
  obtain ⟨k, hk⟩ := (hlim.eventually (hK.mem_nhds K.one_mem)).exists
  exact hg3 k hk

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealAdd
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct

namespace GlobalTheory.SplitComp

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

theorem exists_imag : ∃ θ : L, θ ≠ 0 ∧ IsCMField.complexConj L θ = -θ := by
  have h := IsCMField.complexConj_ne_one L
  obtain ⟨x, hx⟩ : ∃ x : L, IsCMField.complexConj L x ≠ x := by
    by_contra hc
    push Not at hc
    exact h (AlgEquiv.ext hc)
  refine ⟨x - IsCMField.complexConj L x, sub_ne_zero.mpr hx.symm, ?_⟩
  rw [map_sub, IsCMField.complexConj_apply_apply]; ring

theorem exists_real_add (θ : L) (h0 : θ ≠ 0) (hθ : IsCMField.complexConj L θ = -θ) (x : L) :
    ∃ a b : maximalRealSubfield L, x = a • (1 : L) + b • θ := by
  have h2 : IsCMField.complexConj L (2 : L) = 2 := map_ofNat _ 2
  have ha : (x + IsCMField.complexConj L x) / 2 ∈ maximalRealSubfield L := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add (f := _), IsCMField.complexConj_apply_apply, h2]
    ring
  have hb : (x - IsCMField.complexConj L x) / (2 * θ) ∈ maximalRealSubfield L := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul,
      IsCMField.complexConj_apply_apply, h2, hθ]
    field_simp
    ring
  refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩
  change x = (x + IsCMField.complexConj L x) / 2 * 1 + (x - IsCMField.complexConj L x) / (2 * θ) * θ
  field_simp
  ring

theorem exists_tmul_add (θ : L) (h0 : θ ≠ 0) (hθ : IsCMField.complexConj L θ = -θ) (z : AL L) :
    ∃ a b : AFplus L, z = (1 : L) ⊗ₜ[maximalRealSubfield L] a + θ ⊗ₜ[maximalRealSubfield L] b := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul x c =>
    obtain ⟨a, b, rfl⟩ := exists_real_add L θ h0 hθ x
    exact ⟨a • c, b • c, by rw [add_tmul, smul_tmul, smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [tmul_add, tmul_add]; abel⟩

theorem compAt_eq_zero : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (z : AL L),
    s.proj z = 0 → s.proj (conjAL L z) = 0 → compAt L s.v z = 0 := by
  intro L _ _ _ s z h1 h2
  obtain ⟨θ, h0, hθ⟩ := exists_imag L
  obtain ⟨a, b, rfl⟩ := exists_tmul_add L θ h0 hθ z
  have e1 : evalAt L s.v a + s.i θ * evalAt L s.v b = 0 := by
    simpa [SplitPlace.proj] using h1
  have e2 : evalAt L s.v a - s.i θ * evalAt L s.v b = 0 := by
    simpa [SplitPlace.proj, conjAL, hθ, neg_tmul, sub_eq_add_neg] using h2
  have hi : s.i θ ≠ 0 := (map_ne_zero s.i).mpr h0
  have : CharZero (s.v.adicCompletion (maximalRealSubfield L)) :=
    algebraRat.charZero _
  have ha : evalAt L s.v a = 0 := by linear_combination (e1 + e2) / 2
  have hb : evalAt L s.v b = 0 := by
    rw [ha, zero_add] at e1
    exact (mul_eq_zero.mp e1).resolve_left hi
  simp [compAt, ha, hb]

end GlobalTheory.SplitComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FderivCompress
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift.VacBd

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
  {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}

theorem orbit_lip (h : IsHeis om ρ) {f : B} (hf : Sm ρ f) : ∃ C : ℝ, ∀ z, ‖ρ z f - f‖ ≤ C * ‖z‖ := by
  have hd := (ContDiff.differentiable hf (by simp) 0).hasFDerivAt.isBigO_sub
  obtain ⟨C, hC0, hC⟩ := hd.exists_pos
  obtain ⟨δ, hδ, hC⟩ := Metric.eventually_nhds_iff.1 hC.bound
  refine ⟨C + 2 * ‖f‖ / δ, fun z => ?_⟩
  have h0 : 0 ≤ 2 * ‖f‖ / δ * ‖z‖ := by positivity
  have h1 : 0 ≤ C * ‖z‖ := by positivity
  rw [add_mul]
  by_cases hz : ‖z‖ < δ
  · have := hC (y := z) (by simpa using hz)
    simp only [h.1, sub_zero] at this
    linarith
  · have h2 : ‖ρ z f - f‖ ≤ 2 * ‖f‖ := by
      have := norm_sub_le (ρ z f) f
      rw [h.2.2.1] at this
      linarith
    have h3 : 2 * ‖f‖ ≤ 2 * ‖f‖ / δ * ‖z‖ := by
      calc 2 * ‖f‖ = 2 * ‖f‖ / δ * δ := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (not_lt.1 hz) (by positivity)
    linarith

theorem dH_bound [CompleteSpace B] (h : IsHeis om ρ) (T : B →L[ℂ] B) (hT : ∀ x, Sm ρ (T x)) :
    ∃ C : ℝ, ∀ z x, ‖dH ρ z (T x)‖ ≤ C * ‖z‖ * ‖x‖ := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun z : V => ((‖z‖ : ℂ)⁻¹) • ((ρ z).comp T - T)) (fun x => by
    obtain ⟨C, hC⟩ := orbit_lip h (hT x)
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z = 0
    · simp [hz]
    · have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        norm_smul, norm_inv, Complex.norm_real, norm_norm]
      rw [inv_mul_le_iff₀ hz', mul_comm]
      exact (hC z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hz'.le))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C, fun z x => ?_⟩
  have h1 : ‖fderiv ℝ (fun u => ρ u (T x)) 0‖ ≤ C * ‖x‖ := by
    refine (ContDiff.differentiable (hT x) (by simp) 0).hasFDerivAt.le_of_lip' (by positivity)
      (Filter.Eventually.of_forall fun w => ?_)
    by_cases hz : w = 0
    · simp [hz]
    · have hz' : 0 < ‖w‖ := norm_pos_iff.2 hz
      have := ContinuousLinearMap.le_of_opNorm_le _ (hC w) x
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        norm_smul, norm_inv, Complex.norm_real, norm_norm] at this
      rw [inv_mul_le_iff₀ hz', mul_comm] at this
      simpa only [h.1, sub_zero] using this
  have := ContinuousLinearMap.le_of_opNorm_le _ h1 z
  unfold dH
  linarith [mul_right_comm C ‖x‖ ‖z‖]

end General

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B}

set_option linter.unusedSectionVars false

theorem heis_dH (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (v w : V) :
    ρ w (dH ρ v f) = (π * I * (omJ J w v : ℂ)) • ρ w f + fderiv ℝ (fun u => ρ u f) w v := by
  have h1 := ((ρ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v hf)
  have h2 : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
  have h3 : HasDerivAt (fun t : ℝ => ρ (w + t • v) f) (fderiv ℝ (fun u => ρ u f) w v) 0 :=
    (ContDiff.differentiable hf (by simp) w).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h2 (by simp)
  have h4 : HasDerivAt (fun t : ℝ => cexp ((π * I * (omJ J w v : ℂ)) * (t : ℂ))) (π * I * (omJ J w v : ℂ)) 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul (π * I * (omJ J w v : ℂ))).cexp
  have h5 := h4.smul h3
  have e : ((ρ w).restrictScalars ℝ) ∘ (fun t : ℝ => ρ (t • v) f) =
      (fun t : ℝ => cexp ((π * I * (omJ J w v : ℂ)) * (t : ℂ))) • fun t : ℝ => ρ (w + t • v) f := by
    funext t
    simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars', h.2.1, Pi.smul_apply', omJ, map_smul,
      real_inner_smul_right]
    congr 2
    push_cast
    ring
  rw [e] at h1
  have := h1.unique h5
  simpa [add_comm] using this

theorem contDiff_omJ (v : V) : ContDiff ℝ ∞ fun w : V => (π * I * (omJ J w v : ℂ)) := by
  unfold omJ
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const))

theorem sm_dH (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (v : V) : Sm ρ (dH ρ v f) := by
  unfold Sm
  simp only [heis_dH h hf]
  exact ((contDiff_omJ v).smul hf).add
    ((ContDiff.fderiv_right (m := ∞) hf (by simp)).clm_apply contDiff_const)

theorem fderiv_compress (P : B →L[ℂ] B) {g y : B} (hg : Sm ρ g) {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (e : ∀ w, P (ρ w g) = φ w • y) (w v : V) : P (fderiv ℝ (fun u => ρ u g) w v) = fderiv ℝ φ w v • y := by
  have h1 := (P.restrictScalars ℝ).hasFDerivAt.comp w (ContDiff.differentiable hg (by simp) w).hasFDerivAt
  have h2 := (hφ.differentiable (by simp) w).hasFDerivAt.smul_const y
  have e' : (P.restrictScalars ℝ) ∘ (fun u => ρ u g) = fun u => φ u • y := funext e
  rw [e'] at h1
  simpa using DFunLike.congr_fun (h1.unique h2) v

theorem vacuum_bound : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, (∃ C : ℝ, ∀ z x, ‖dH ρ z (proj h x)‖ ≤ C * ‖z‖ * ‖x‖) ∧ (∀ u v, ∃ C : ℝ, ∀ x, ‖dH ρ u (dH ρ v (proj h x))‖ ≤ C * ‖x‖) ∧ ∀ u v, ∃ lam : ℂ, ∀ x, proj h (dH ρ u (dH ρ v (proj h x))) = lam • proj h x := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h
  have hs : ∀ x, Sm ρ (proj h x) := fun x => (Osc.good_proj hJ h x).sm hJ
  obtain ⟨C, hC⟩ := dH_bound h (proj h) hs
  refine ⟨⟨C, hC⟩, fun u v => ?_, fun u v => ?_⟩
  · let T : B →L[ℂ] B := LinearMap.mkContinuous
      { toFun := fun x => dH ρ v (proj h x)
        map_add' := fun x y => by rw [map_add (f := _), dH_add v (hs x) (hs y)]
        map_smul' := fun a x => by rw [map_smul, dH_smul v a (hs x), RingHom.id_apply] } (C * ‖v‖) (hC v)
    obtain ⟨D, hD⟩ := dH_bound h T fun x => sm_dH h (hs x) v
    exact ⟨D * ‖u‖, hD u⟩
  · have hg : ContDiff ℝ ∞ (gau : V → ℂ) := contDiff_gau
    have hφ : ContDiff ℝ ∞ fun w : V => (π * I * (omJ J w v : ℂ)) * gau w + fderiv ℝ gau w v :=
      ((contDiff_omJ v).mul hg).add ((ContDiff.fderiv_right (m := ∞) hg (by simp)).clm_apply contDiff_const)
    refine ⟨_, fun x => fderiv_compress (proj h) (sm_dH h (hs x) v) hφ (fun w => ?_) 0 u⟩
    rw [heis_dH h (hs x), map_add (f := _), map_smul, proj_heis_proj hJ h,
      fderiv_compress (proj h) (hs x) hg (fun w => proj_heis_proj hJ h w x), add_smul, mul_smul _ (gau w)]

end GlobalTheory.Mem.Lift.VacBd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FderivEqQuadComm
section
noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift

theorem IsQuadOf.apply_vec {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] {om : V → V → ℝ} {X : V → V} {κ : Type} [Fintype κ] {c : κ → ℂ} {p q : κ → V}
    (h : IsQuadOf om X c p q) (L : V →ₗ[ℝ] B) (v : V) :
    (2 * π * I : ℂ) • ∑ i, c i • ((om (q i) v : ℂ) • L (p i) + (om (p i) v : ℂ) • L (q i)) = L (X v) := by
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)]
  intro φ
  have := h ((φ.restrictScalars ℝ).toLinearMap ∘ₗ L) v
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum, ← mul_add] using this

theorem fderiv_eq_quad_comm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ (X : V → V) (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → V), IsQuadOf (fun x y => om x y) X c p q → ∀ f, Sm ρ f → ∀ w, fderiv ℝ (fun u => ρ u f) w (X w) = quad ρ c p q (ρ w f) - ρ w (quad ρ c p q f) := by
  intro V _ _ B _ _ om ρ h0 hH X κ _ c p q hQ f hf w
  have C := GlobalTheory.Mem.Lift.DCalc.dH_calculus V B om ρ h0 hH
  obtain ⟨h1, h2, h3, h4, -⟩ := C f hf
  have skew : om w (X w) = - om (X w) w := by
    have := h0 (w + X w)
    simp only [map_add (f := _), _root_.add_apply, h0] at this
    linarith
  have key : ∀ u v, dH ρ u (dH ρ v (ρ w f)) = ρ w (dH ρ u (dH ρ v f))
      + (2 * π * I : ℂ) • ρ w ((om v w : ℂ) • dH ρ u f + (om u w : ℂ) • dH ρ v f)
      + ((2 * π * I : ℂ) * ((2 * π * I : ℂ) * ((om v w : ℂ) * (om u w : ℂ)))) • ρ w f := by
    intro u v
    obtain ⟨-, g2, -, g4, -⟩ := C _ (h1 v)
    have hs : Sm ρ ((2 * π * I * (om v w : ℂ)) • ρ w f) := (smS ρ).smul_mem _ (h2 w)
    rw [h4 v w, dH_add u (g2 w) hs, dH_smul u _ (h2 w), g4 u w, h4 u w]
    simp only [map_add (f := _), map_smul]
    module
  have e1 := hQ.apply_vec (fderiv ℝ (fun u => ρ u f) 0).toLinearMap w
  have e1' : (2 * π * I : ℂ) • ∑ i, c i • ((om (q i) w : ℂ) • dH ρ (p i) f + (om (p i) w : ℂ) • dH ρ (q i) f)
      = dH ρ (X w) f := e1
  have e2 := hQ (Complex.ofRealCLM.toLinearMap ∘ₗ (om.flip w).toLinearMap) w
  have e2' : 2 * π * I * ∑ i, c i * ((om (q i) w : ℂ) * (om (p i) w : ℂ) + (om (p i) w : ℂ) * (om (q i) w : ℂ))
      = (om (X w) w : ℂ) := e2
  have e3 : ∑ i, c i * ((2 * π * I : ℂ) * ((2 * π * I : ℂ) * ((om (q i) w : ℂ) * (om (p i) w : ℂ))))
      = π * I * (om (X w) w : ℂ) := by
    rw [← e2', Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e4 : ∑ i, c i • (2 * π * I : ℂ) • ρ w ((om (q i) w : ℂ) • dH ρ (p i) f + (om (p i) w : ℂ) • dH ρ (q i) f)
      = ρ w (dH ρ (X w) f) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e1', map_smul, map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_comm]
  have e5 : quad ρ c p q (ρ w f) = ρ w (quad ρ c p q f) + ρ w (dH ρ (X w) f)
      + (π * I * (om (X w) w : ℂ)) • ρ w f := by
    rw [← e3, ← e4, Finset.sum_smul]
    unfold quad
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key, smul_add, smul_add, map_smul, smul_smul (c i) _ (ρ w f)]
  rw [h3, e5, skew]
  push_cast
  module

end GlobalTheory.Mem.Lift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorOfMemIsotypicComponent
section
open Formalism.L2 Formalism.AUTREP ReciprocityTheory.Aut NumberField

namespace GlobalTheory.IsoFix

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem fixed_transport {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (GAf L n → W)} (K : Set (GAf L n))
    (hS : NG.IsSubrep ρ S) (hiso : NG.IsoRep S S') {x : GAf L n → W} (hx : x ∈ S') (hx0 : x ≠ 0)
    (hfix : ∀ κ ∈ K, NG.rt L n κ x = x) :
    ∃ f' ∈ S, f' ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ f' = f' := by
  obtain ⟨T, hT⟩ := hiso
  have hTf0 : T (T.symm ⟨x, hx⟩) = ⟨x, hx⟩ := T.apply_symm_apply _
  refine ⟨(T.symm ⟨x, hx⟩ : S), (T.symm ⟨x, hx⟩).2, ?_, ?_⟩
  · intro h
    have h1 : T.symm ⟨x, hx⟩ = 0 := Subtype.ext h
    have h2 : (⟨x, hx⟩ : S') = 0 := by rw [← hTf0, h1, map_zero]
    exact hx0 (congrArg Subtype.val h2)
  · intro κ hκ
    have hmem : NG.rt L n κ ((T.symm ⟨x, hx⟩ : S) : GAf L n → W) ∈ S := hS.stable κ _ (T.symm ⟨x, hx⟩).2
    have key := hT κ (T.symm ⟨x, hx⟩) ⟨_, hmem⟩ rfl
    rw [hTf0] at key
    have h3 : T ⟨_, hmem⟩ = T (T.symm ⟨x, hx⟩) := by
      apply Subtype.ext
      rw [key, hTf0]
      exact hfix κ hκ
    exact congrArg Subtype.val (T.injective h3)

theorem iSup_finset_stable (s : Finset (Submodule ℂ (GAf L n → W)))
    (hs : ∀ i ∈ s, ∀ h, ∀ f ∈ i, NG.rt L n h f ∈ i) (h : GAf L n) :
    ∀ f ∈ (⨆ i ∈ s, i), NG.rt L n h f ∈ (⨆ i ∈ s, i) := by
  have hle : (⨆ i ∈ s, i) ≤ (⨆ i ∈ s, i).comap (NG.rt L n h) := by
    refine iSup₂_le fun i hi => ?_
    intro f hf
    exact (le_iSup₂ (f := fun i (_ : i ∈ s) => i) i hi) (hs i hi h f hf)
  exact fun f hf => hle hf

theorem fixed_of_mem_finset_sum (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W))
    (K : Set (GAf L n)) (hS : NG.IsIrrRep ρ S) (s : Finset (Submodule ℂ (GAf L n → W))) :
    (↑s ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ s, i), f ≠ 0 →
      (∀ κ ∈ K, NG.rt L n κ f = f) → ∃ f' ∈ S, f' ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ f' = f' := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ f hf hf0 _
    simp at hf
    exact absurd hf hf0
  | insert a s ha ih =>
    intro hsub f hf hf0 hfix
    have haF : NG.IsIrrRep ρ a ∧ NG.IsoRep S a := hsub (Finset.mem_insert_self a s)
    have hsF : (↑s : Set _) ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ s, i), NG.rt L n h g ∈ (⨆ i ∈ s, i) :=
      iSup_finset_stable s (fun i hi => (hsF hi).1.1.stable)
    have hsubrep : NG.IsSubrep ρ (a ⊓ ⨆ i ∈ s, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ K, NG.rt L n κ y = y := by
        intro κ hκ
        have e := hfix κ hκ
        rw [map_add (f := _)] at e
        have hd : NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ s, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      by_cases hy0 : y = 0
      · subst hy0
        simp only [zero_add] at hf0 hfix
        exact ih hsF z hz hf0 hfix
      · exact fixed_transport K hS.1 haF.2 hy hy0 hyfix
    · have hle : a ≤ ⨆ i ∈ s, i := inf_eq_left.1 htop
      exact ih hsF f ((sup_le hle le_rfl) hf) hf0 hfix

theorem fixed_of_isoTyp : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (K : Set (GAf L n)),
    NG.IsIrrRep ρ S → ∀ f ∈ NG.isoTyp ρ S, f ≠ 0 → (∀ κ ∈ K, NG.rt L n κ f = f) →
      ∃ f' ∈ S, f' ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ f' = f' := by
  intro L _ _ _ n W _ _ ρ S K hS f hf hf0 hfix
  obtain ⟨s, hs, hfs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  exact fixed_of_mem_finset_sum ρ S K hS s hs f hfs hf0 hfix

end GlobalTheory.IsoFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlRelOfCanonicalCommutationRelations
section
open Matrix GlobalTheory.Mem.Lift

namespace GlobalTheory.Mem.Lift

theorem IsCCR.comm_monomial {A : Type} [Ring A] {κ : Type} [DecidableEq κ] {x d : κ → A} (h : IsCCR x d)
    (k l k' l' : κ) : x k * d l * (x k' * d l') - x k' * d l' * (x k * d l) =
      (if k' = l then x k * d l' else 0) - (if k = l' then x k' * d l else 0) := by
  obtain ⟨hx, hd, hc⟩ := h
  have e1 : x k * d l * (x k' * d l') = x k * (d l * x k' - x k' * d l) * d l' + x k * x k' * (d l * d l') := by
    noncomm_ring
  have e2 : x k' * d l' * (x k * d l) = x k' * (d l' * x k - x k * d l') * d l + x k' * x k * (d l' * d l) := by
    noncomm_ring
  rw [e1, e2, hc, hc, hx k' k, hd l' l]
  split_ifs <;> simp

theorem glRel_of_isCCR (A : Type) [Ring A] (n m : ℕ) (x d : Fin n × Fin m → A) (h : IsCCR x d) :
    Formalism.REAL.GlRel (fun i j : Fin n => ∑ a, x (i, a) * d (j, a)) ∧
      Formalism.REAL.GlRel (fun a b : Fin m => -∑ i, x (i, b) * d (i, a)) := by
  refine ⟨fun i j k l => ?_, fun a b c e => ?_⟩
  · beta_reduce
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (f := fun s t => x (k, s) * d (l, s) * (x (i, t) * d (j, t))),
      ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, h.comm_monomial, Finset.sum_sub_distrib, Prod.mk.injEq]
    congr 1
    · by_cases hjk : j = k
      · simp [hjk]
      · simp [hjk, Ne.symm hjk]
    · by_cases hli : l = i
      · simp [hli]
      · simp [hli, Ne.symm hli]
  · beta_reduce
    rw [neg_mul_neg, neg_mul_neg, Finset.sum_mul_sum, Finset.sum_mul_sum,
      Finset.sum_comm (f := fun s t => x (s, e) * d (s, c) * (x (t, b) * d (t, a))), ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, h.comm_monomial, Finset.sum_sub_distrib, Prod.mk.injEq]
    by_cases hbc : b = c <;> by_cases hea : e = a <;> simp [hbc, hea, sub_eq_neg_add, add_comm]

end GlobalTheory.Mem.Lift
end

