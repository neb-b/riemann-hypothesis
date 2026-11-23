module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.NormChar
public import Development.AutomorphicArithmetic.WhittakerHecke.CentralCharGaloisInvariantOfConjInv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0657
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
public import GroundTheory.AutomorphicForms.CompactFormulaCountable
public import Mathlib.NumberTheory.LSeries.Positivity

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.CenExOf
section
open UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.cenEx_of :
    CenEx := by
  intro E _ _ _ hE P hP
  obtain ⟨ω, hω⟩ := GlobalTheory.CuspRep.Central.exists_hasCentChar (GlobalTheory.CuspRep.CG.mk P)
  obtain ⟨χ, hχ⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.A.normChar_of_inv hE ω (UpperTheory.centralChar_galois_invariant_of_conjInv E P ω hω hP)
  refine ⟨χ, fun f hf z g => ?_⟩
  have h1 := (GlobalTheory.CuspRep.CuspSub.hasCentral_iff (π := P) (ω := ω)).2 hω z f hf
  have h2 := congrFun (congrArg Subtype.val h1) g
  rw [GlobalTheory.CuspRep.scalar_comm, ← hχ z]
  exact h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ExistsNat
section
open NumberField IsDedekindDomain
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open UpperTheory.ConvolutionTheory.RankTwoDescent
open HeckeValGen GlobalTheory.HeckeSplit

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.ChExPf

private theorem nat_le_one (v : H.P ℚ) (c : ℕ) : Valued.v (c : H.Kv v) ≤ 1 := by
  induction c with
  | zero => simp
  | succ c ih =>
    push_cast
    exact Valuation.map_add_le _ ih (by simp)

private theorem dvd_le (v : H.P ℚ) {a b : ℕ} (h : a ∣ b) : Valued.v (b : H.Kv v) ≤ Valued.v (a : H.Kv v) := by
  obtain ⟨c, rfl⟩ := h
  push_cast
  rw [map_mul]
  exact mul_le_of_le_one_right' (nat_le_one v c)

private theorem exists_nat {K : Type} [Field K] [NumberField K] (v : H.P K) (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ Valued.v (m : H.Kv v) ≤ WithZero.exp (-(n : ℤ)) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  refine ⟨Ideal.absNorm v.asIdeal ^ n, pow_pos (Nat.pos_of_ne_zero h0) n, ?_⟩
  have hm : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ n ∈ v.asIdeal ^ n :=
    Ideal.pow_mem_pow (Ideal.absNorm_mem _) n
  have h1 := (v.intValuation_le_pow_iff_mem _ n).2 hm
  have h3 : Valued.v ((algebraMap (𝓞 K) K (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ n) : K) : v.adicCompletion K) ≤
      WithZero.exp (-(n : ℤ)) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
    exact h1
  have h2 : ((Ideal.absNorm v.asIdeal ^ n : ℕ) : H.Kv v) =
      ((algebraMap (𝓞 K) K (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ n) : K) : v.adicCompletion K) := by
    change _ = algebraMap K (v.adicCompletion K) _
    simp
  rw [h2]
  exact h3

end UpperTheory.ConvolutionTheory.RankTwoDescent.ChExPf

open UpperTheory.ConvolutionTheory.RankTwoDescent.ChExPf in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.chEx_of :
    ChEx := by
  intro χ
  classical
  set S := (GlobalTheory.HCharRam.ram_finite ℚ χ).toFinset with hSdef
  choose n hn using fun v => GlobalTheory.HeckeSplit.exists_level χ.1 χ.2.1 v
  choose M hM0 hM using fun v : H.P ℚ => exists_nat v (n v)
  refine ⟨∏ v ∈ S, M v, Finset.prod_pos fun v _ => hM0 v, fun N hN t ht hD => ?_⟩
  have key := GlobalTheory.HeckeSplit.char_eq_prod_local χ.1 χ.2.1 t S (fun v hv => by
    have hu : χ.UnrAt v := by
      by_contra hc
      exact hv ((Set.Finite.mem_toFinset _).2 hc)
    exact hu _ (ht.2 v))
  have hinf : infPart ℚ t = 1 := Units.ext ht.1
  rw [key, hinf, map_one, map_one, one_mul]
  refine Finset.prod_eq_one fun v hv => hn v _ ?_
  have h1 : Valued.v (H.cp v ((t : A ℚ) - 1)) ≤ Valued.v (N : H.Kv v) := (hD v)
  rw [map_sub, map_one] at h1
  exact h1.trans ((dvd_le v ((Finset.dvd_prod_of_mem M hv).trans hN)).trans (hM v))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ExtOf
section
open UpperTheory.ConvolutionTheory.RankTwoDescent
open Filter Topology

private theorem glue_aux (A : ℂ → ℂ)
    (h : ∀ s₀ : ℂ, ∃ (r : ℝ) (H m : ℂ → ℂ), r < s₀.re ∧
      DifferentiableOn ℂ H {s | r < s.re} ∧ DifferentiableOn ℂ m {s | r < s.re} ∧ m s₀ ≠ 0 ∧
      ∀ s : ℂ, 4 < s.re → H s = A s * m s) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ s : ℂ, 4 < s.re → F s = A s := by
  choose r H m hr hH hm hne hA using h
  have hopen : ∀ ρ : ℝ, IsOpen {z : ℂ | ρ < z.re} := fun ρ =>
    isOpen_lt continuous_const Complex.continuous_re
  have key : ∀ a b s : ℂ, r a < s.re → r b < s.re → H a s * m b s = H b s * m a s := by
    intro a b s ha hb
    have hUc : IsPreconnected {z : ℂ | max (r a) (r b) < z.re} :=
      (convex_halfSpace_re_gt (max (r a) (r b))).isPreconnected
    have hsa : {z : ℂ | max (r a) (r b) < z.re} ⊆ {z | r a < z.re} :=
      fun z hz => show r a < z.re from lt_of_le_of_lt (le_max_left _ _) hz
    have hsb : {z : ℂ | max (r a) (r b) < z.re} ⊆ {z | r b < z.re} :=
      fun z hz => show r b < z.re from lt_of_le_of_lt (le_max_right _ _) hz
    have d1 : DifferentiableOn ℂ (fun z => H a z * m b z) {z : ℂ | max (r a) (r b) < z.re} :=
      ((hH a).mono hsa).mul ((hm b).mono hsb)
    have d2 : DifferentiableOn ℂ (fun z => H b z * m a z) {z : ℂ | max (r a) (r b) < z.re} :=
      ((hH b).mono hsb).mul ((hm a).mono hsa)
    have hz₀ : ((max (max (r a) (r b)) 4 + 1 : ℝ) : ℂ) ∈ {z : ℂ | max (r a) (r b) < z.re} := by
      show max (r a) (r b) < (((max (max (r a) (r b)) 4 + 1 : ℝ) : ℂ)).re
      rw [Complex.ofReal_re]
      linarith [le_max_left (max (r a) (r b)) 4]
    have h4 : ((max (max (r a) (r b)) 4 + 1 : ℝ) : ℂ) ∈ {z : ℂ | (4 : ℝ) < z.re} := by
      show (4 : ℝ) < (((max (max (r a) (r b)) 4 + 1 : ℝ) : ℂ)).re
      rw [Complex.ofReal_re]
      linarith [le_max_right (max (r a) (r b)) 4]
    have hev : (fun z => H a z * m b z) =ᶠ[𝓝 ((max (max (r a) (r b)) 4 + 1 : ℝ) : ℂ)]
        fun z => H b z * m a z := by
      filter_upwards [(hopen 4).mem_nhds h4] with z hz
      rw [hA a z hz, hA b z hz]
      ring
    exact (d1.analyticOnNhd (hopen _)).eqOn_of_preconnected_of_eventuallyEq
      (d2.analyticOnNhd (hopen _)) hUc hz₀ hev (show max (r a) (r b) < s.re from max_lt ha hb)
  refine ⟨fun s => H s s / m s s, ?_, ?_⟩
  · intro s₀
    have hU : {z : ℂ | r s₀ < z.re} ∈ 𝓝 s₀ := (hopen _).mem_nhds (hr s₀)
    have hdH : DifferentiableAt ℂ (H s₀) s₀ := (hH s₀).differentiableAt hU
    have hdm : DifferentiableAt ℂ (m s₀) s₀ := (hm s₀).differentiableAt hU
    have hne' : ∀ᶠ z in 𝓝 s₀, m s₀ z ≠ 0 := hdm.continuousAt.eventually_ne (hne s₀)
    have heq : (fun s => H s s / m s s) =ᶠ[𝓝 s₀] fun z => H s₀ z / m s₀ z := by
      filter_upwards [hU, hne'] with z hz hz'
      rw [div_eq_div_iff (hne z) hz']
      exact (key s₀ z z hz (hr z)).symm
    exact heq.differentiableAt_iff.mpr (hdH.div hdm (hne s₀))
  · intro s hs
    show H s s / m s s = A s
    rw [hA s s hs, mul_div_assoc, div_self (hne s), mul_one]

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.ext_of :
    TrAdm → PerTr → Ent → Unf → PhiMem → Fac → ShiftM → Hol → NonZ → Ext := by
  intro hTr hPer hEnt hUnf hPhi hFac hSh hHol hNZ
  intro E _ _ _ D P ω χ hC hU hχ M U hNo L N φ hCh hG hW a ha hsum
  have hA := hTr E D P ω χ hC hU hχ
  have hPz := hPer E D P ω χ hC hU hχ hA M U hNo
  obtain ⟨c₁, hc₁, hZ⟩ := hUnf E D P ω χ hC hU hχ M U
  obtain ⟨c₂, hc₂, hF⟩ := hFac E D P ω χ hC hU hχ M L N hCh
  have hN := hG.pos
  have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine glue_aux (LSeries a) ?_
  intro s₀
  obtain ⟨k, hk⟩ := exists_nat_gt (1 - s₀.re)
  have hk' : 1 - (k : ℝ) < s₀.re := by linarith
  obtain ⟨φ', e, p, hG', hp, hne⟩ := hNZ E D P ω χ hC hU hχ hA L N φ hG hW k s₀ hk'
  obtain ⟨n, f, q, hfq, hsumM⟩ := hSh E D P ω χ hC hU hχ L N k φ' e p hG' hp
  have hAf : ∀ i, admitted D ω (f i) := fun i => hA _ (hfq i).1.mem
  have hdZ : Differentiable ℂ fun s => ∑ i, Zs M U χ (f i) (PhiN N (q i)) s :=
    Differentiable.fun_sum fun i _ =>
      hEnt E D P ω χ hC hU hχ M U (f i) (hAf i) (hPz _ (hfq i).1.mem) _ (hPhi N (q i) hN)
  have hdP : Differentiable ℂ fun s : ℂ => (Real.pi : ℂ) ^ (s + ((e + k : ℕ) : ℂ)) :=
    (differentiable_id.add_const _).const_cpow (Or.inl hπ0)
  have hdG : Differentiable ℂ fun s : ℂ => (Complex.Gamma (s + ((e + k : ℕ) : ℂ)))⁻¹ :=
    Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _)
  have hdH : Differentiable ℂ fun s : ℂ => (c₁ * c₂)⁻¹ *
      ((Real.pi : ℂ) ^ (s + ((e + k : ℕ) : ℂ)) * ((Complex.Gamma (s + ((e + k : ℕ) : ℂ)))⁻¹)) *
        ∑ i, Zs M U χ (f i) (PhiN N (q i)) s :=
    ((differentiable_const _).mul (hdP.mul hdG)).mul hdZ
  refine ⟨1 - k, _, Mk D χ k φ' p, hk', hdH.differentiableOn,
    hHol E D P ω χ hC hU hχ k φ' p (hA _ hG'.mem), hne, ?_⟩
  intro s hs
  have h1 : ∀ i, Zs M U χ (f i) (PhiN N (q i)) s =
      c₁ * (c₂ * ((Real.pi : ℂ) ^ (-(s + ((e + k : ℕ) : ℂ))) * Complex.Gamma (s + ((e + k : ℕ) : ℂ))) *
        LSeries a s * Mk D χ 0 (f i) (q i) s) := fun i => by
    rw [hZ (f i) (hAf i) _ (hPhi N (q i) hN) s hs,
      hF (f i) (hAf i) (hfq i).1 a ha (e + k) (q i) (hfq i).2 s hs (hsum s hs)]
  have hsM := hsumM s hs
  simp only [h1]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← hsM]
  have hre : 0 < (s + ((e + k : ℕ) : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ ((e + k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hΓ := Complex.Gamma_ne_zero_of_re_pos hre
  have hXY : (Real.pi : ℂ) ^ (s + ((e + k : ℕ) : ℂ)) * (Real.pi : ℂ) ^ (-(s + ((e + k : ℕ) : ℂ))) = 1 := by
    rw [← Complex.cpow_add _ _ hπ0, add_neg_cancel, Complex.cpow_zero]
  have hc : c₁ * c₂ ≠ 0 := mul_ne_zero hc₁ hc₂
  generalize (Real.pi : ℂ) ^ (s + ((e + k : ℕ) : ℂ)) = X at hXY ⊢
  generalize (Real.pi : ℂ) ^ (-(s + ((e + k : ℕ) : ℂ))) = Y at hXY ⊢
  generalize Complex.Gamma (s + ((e + k : ℕ) : ℂ)) = G at hΓ ⊢
  calc (c₁ * c₂)⁻¹ * (X * G⁻¹) * (c₁ * (c₂ * (Y * G) * LSeries a s * Mk D χ k φ' p s))
      = (X * Y) * ((c₁ * c₂)⁻¹ * (c₁ * c₂)) * (G⁻¹ * G) * (LSeries a s * Mk D χ k φ' p s) := by
        ring
    _ = LSeries a s * Mk D χ k φ' p s := by
        rw [hXY, inv_mul_cancel₀ hc, inv_mul_cancel₀ hΓ]
        ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.InnerInt
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

variable {E : Type} [Field E] [NumberField E]

private theorem cont_em : Continuous (em E) := by
  have hM : Continuous ((AdeleBaseChange.adeleMap ℚ E).mapMatrix.toMonoidHom :
      Matrix (Fin 2) (Fin 2) (A ℚ) → Matrix (Fin 2) (Fin 2) (A E)) :=
    continuous_id.matrix_map AdeleBaseChange.continuous_adeleMap
  exact Continuous.units_map _ hM

private theorem sc_idele : SecondCountableTopology (IdeleGroup ℚ) := by
  haveI : SecondCountableTopology (A ℚ) := GroundTheory.Automorphic.secondCountableTopology_adeleRing ℚ
  haveI : SecondCountableTopology (A ℚ)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem cont_in {φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous φ) (t : (A ℚ)ˣ) :
    Continuous fun g : G1 ℚ => φ (em E (gl g * dM t)) :=
  hc.comp (cont_em.comp (Matrix.SpecialLinearGroup.continuous_toGL.mul continuous_const))

private theorem inner_int (M : Meas ℚ) {φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous φ) {B : ℝ}
    (hB : ∀ g, ‖φ g‖ ≤ B) (t : (A ℚ)ˣ) :
    IntegrableOn (fun g : G1 ℚ => φ (em E (gl g * dM t))) M.D M.μ := by
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  exact Integrable.of_bound (cont_in hc t).aestronglyMeasurable B (ae_of_all _ fun g => hB _)

private theorem outer_int (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1)
    {φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous φ) {B : ℝ} (hB : ∀ g, ‖φ g‖ ≤ B) :
    Integrable (fun t => ((χ.1 t : ℂˣ) : ℂ) * ∫ g in M.D, φ (em E (gl g * dM t)) ∂M.μ) U.υ := by
  haveI := U.prob
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  haveI := sc_idele
  have hF : Continuous fun t : IdeleGroup ℚ => ∫ g in M.D, φ (em E (gl g * dM t)) ∂M.μ := by
    refine continuous_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
    · exact fun t => (cont_in hc t).aestronglyMeasurable
    · exact fun t => ae_of_all _ fun g => hB _
    · exact ae_of_all _ fun g =>
        hc.comp (cont_em.comp (continuous_const.mul UpperTheory.ConvolutionTheory.R2.continuous_dM))
  have hχc : Continuous fun t : IdeleGroup ℚ => ((χ.1 t : ℂˣ) : ℂ) :=
    Units.continuous_val.comp χ.2.1
  refine Integrable.of_bound (hχc.mul hF).aestronglyMeasurable (B * (M.μ.restrict M.D).real Set.univ)
    (ae_of_all _ fun t => ?_)
  rw [norm_mul, hχ, one_mul]
  exact norm_integral_le_of_norm_le_const (ae_of_all _ fun g => hB _)

private theorem per_add (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1)
    {φ₁ φ₂ : GL (Fin 2) (A E) → ℂ} (h₁ : Continuous φ₁) (h₂ : Continuous φ₂) {B₁ B₂ : ℝ}
    (b₁ : ∀ g, ‖φ₁ g‖ ≤ B₁) (b₂ : ∀ g, ‖φ₂ g‖ ≤ B₂) :
    Per M U χ (φ₁ + φ₂) = Per M U χ φ₁ + Per M U χ φ₂ := by
  unfold Per
  rw [← integral_add (outer_int M U χ hχ h₁ b₁) (outer_int M U χ hχ h₂ b₂)]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [Pi.add_apply]
  rw [integral_add (inner_int M h₁ b₁ t) (inner_int M h₂ b₂ t), mul_add]

private theorem per_smul (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (c : ℂ) (φ : GL (Fin 2) (A E) → ℂ) :
    Per M U χ (c • φ) = c * Per M U χ φ := by
  unfold Per
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul]
  ring

private theorem per_zero (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) :
    Per M U χ (0 : GL (Fin 2) (A E) → ℂ) = 0 := by
  simp [Per]

end UpperTheory.ConvolutionTheory.RankTwoDescent

open UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.perTr_of :
    PerTr := by
  intro E _ _ _ D P ω χ _ hω hχω hAdm M U hNo φ hφ
  have hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
    intro a
    have h := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) (hχω a)
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, hω a, mul_one,
      Units.val_one, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, h, rfl⟩ := hx
    exact hNo f hf h
  | zero => exact per_zero M U χ
  | add x y hx hy ihx ihy =>
    obtain ⟨B₁, b₁⟩ := (hAdm x hx).bdd
    obtain ⟨B₂, b₂⟩ := (hAdm y hy).bdd
    rw [per_add M U χ hχ (hAdm x hx).cont (hAdm y hy).cont b₁ b₂, ihx, ihy, add_zero]
  | smul c x hx ih =>
    rw [per_smul, ih, mul_zero]

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.Landau
section
open UpperTheory.ConvolutionTheory.RankTwoDescent

open scoped ComplexOrder

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.landau_of :
    Landau := by
  intro b hb0 hb1 hbs hent
  obtain ⟨F, hF, hFb⟩ := hent
  by_contra hinf
  have hinf' : ({n | 1 ≤ b n} \ {0, 1} : Set ℕ).Infinite :=
    Set.Infinite.diff hinf (Set.toFinite _)
  obtain ⟨m, hm⟩ := exists_nat_gt (F 0).re
  obtain ⟨S, hSsub, hScard⟩ := hinf'.exists_subset_card_eq m
  have hS0 : ∀ n ∈ S, n ≠ 0 := fun n hn h => (hSsub hn).2 (by simp [h])
  have hS1 : 1 ∉ S := fun hn => (hSsub hn).2 (by simp)
  have hS2 : ∀ n ∈ S, 1 ≤ b n := fun n hn => (hSsub hn).1
  let a : ℕ → ℂ := fun n => if n ∈ S then 0 else b n
  let G : ℂ → ℂ := fun s => F s - ∑ n ∈ S, b n / (n : ℂ) ^ s
  have hG : Differentiable ℂ G := by
    refine hF.sub (Differentiable.fun_sum fun n hn => ?_)
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hS0 n hn)
    exact (differentiable_const _).div (differentiable_id.const_cpow (Or.inl hn0))
      fun s => by simp [Complex.cpow_eq_zero_iff, hn0]
  have hsum : ∀ s : ℂ, 4 < s.re →
      HasSum (LSeries.term a s) (LSeries b s - ∑ n ∈ S, b n / (n : ℂ) ^ s) := by
    intro s hs
    have h1 : HasSum (LSeries.term b s) (LSeries b s) := (hbs s hs).LSeriesHasSum
    have h2 : HasSum (fun n => if n ∈ S then LSeries.term b s n else 0)
        (∑ n ∈ S, b n / (n : ℂ) ^ s) := by
      have h3 : HasSum (fun n => if n ∈ S then LSeries.term b s n else 0)
          (∑ n ∈ S, if n ∈ S then LSeries.term b s n else 0) :=
        hasSum_sum_of_ne_finset_zero (fun n hn => by simp [hn])
      have h5 : (∑ n ∈ S, if n ∈ S then LSeries.term b s n else 0) =
          ∑ n ∈ S, b n / (n : ℂ) ^ s :=
        Finset.sum_congr rfl fun n hn => by
          simp [hn, LSeries.term_of_ne_zero (hS0 n hn)]
      rwa [h5] at h3
    have h6 : LSeries.term a s =
        fun n => LSeries.term b s n - if n ∈ S then LSeries.term b s n else 0 := by
      funext n
      by_cases hn : n ∈ S
      · simp [a, hn, LSeries.term_def]
      · simp [a, hn, LSeries.term_def]
    rw [h6]
    exact h1.sub h2
  have ha0 : 0 ≤ a := by
    intro n
    by_cases hn : n ∈ S
    · simp [a, hn]
    · simpa [a, hn] using hb0 n
  have ha1 : 0 < a 1 := by
    simp [a, hS1, hb1]
  have habs : LSeries.abscissaOfAbsConv a ≤ (4 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      (hsum y (by simpa using hy)).summable
  have hEq : {s : ℂ | (4 : ℝ) < s.re}.EqOn G (LSeries a) := by
    intro s hs
    have hs' : (4 : ℝ) < s.re := hs
    have h4 : (4 : ℝ) < s.re := hs'
    have : LSeries a s = LSeries b s - ∑ n ∈ S, b n / (n : ℂ) ^ s :=
      LSeriesHasSum.LSeries_eq (hsum s h4)
    simp only [G, hFb s h4]
    exact this.symm
  have hpos := LSeries.positive_of_differentiable_of_eqOn ha0 ha1 hG habs hEq 0
  have hG0 : G ((0 : ℝ) : ℂ) = F 0 - ∑ n ∈ S, b n := by
    simp [G]
  rw [hG0] at hpos
  have hre : (∑ n ∈ S, b n).re < (F 0).re := by
    have := (Complex.lt_def.mp hpos).1
    simpa using this
  have hcard : (m : ℝ) ≤ (∑ n ∈ S, b n).re := by
    rw [Complex.re_sum, ← hScard]
    have : ∀ n ∈ S, (1 : ℝ) ≤ (b n).re := fun n hn => by
      simpa using (Complex.le_def.mp (hS2 n hn)).1
    simpa using Finset.card_nsmul_le_sum S _ 1 this
  linarith
end

