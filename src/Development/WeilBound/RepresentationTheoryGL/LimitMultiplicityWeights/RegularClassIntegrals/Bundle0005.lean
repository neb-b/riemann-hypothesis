module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0621
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DDerMemc
section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open scoped ContDiff ComplexConjugate Topology

noncomputable section

namespace MainStatements.WeightKernel.Dec.DDerMemc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem exp_entry (Z : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • Z)) i j := by
  open scoped Matrix.Norms.Operator in
  have h1 : ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • Z) : Matrix (Fin n) (Fin n) ℂ) := by
    have : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
      contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
    exact this.comp (contDiff_id.smul contDiff_const)
  open scoped Matrix.Norms.Operator in
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).contDiff.comp h1

theorem lineSm (h : IsCMExt F E σ) {b : ℝ → GAd σ J} (hb : IsRealLine σ J b) :
    ContDiff ℝ ∞ fun t => infCoord σ J (projInf σ J (b t)) := by
  classical
  obtain ⟨w, τ, Z, -, hZ⟩ := hb
  choose y hy hyZ using hZ
  refine contDiff_pi.2 fun u => contDiff_pi.2 fun τ' => contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have e0 : ∀ t, infCoord σ J (projInf σ J (b t)) u τ' i j = archMat σ J τ' (projArch σ J u (embArch σ J w (y t))) i j :=
    fun t => by rw [← hy t, ← projInfArch_projInf]; rfl
  simp only [e0]
  by_cases hu : u = w
  · subst hu
    simp only [projArch_embArch_self]
    have e1 : ∀ t, infEmb τ ((matHom _ σ J (y t)).1 i j) = (NormedSpace.exp (t • Z)) i j := fun t => by
      rw [← hyZ t]; rfl
    rcases infEmb_eq_or_conj h τ τ' with e | e
    · have : ∀ t, archMat σ J τ' (y t) i j = (NormedSpace.exp (t • Z)) i j := fun t => by
        rw [← e1 t, ← e]; rfl
      simp only [this]; exact exp_entry Z i j
    · have : ∀ t, archMat σ J τ' (y t) i j = conj ((NormedSpace.exp (t • Z)) i j) := fun t => by
        rw [← e1 t]
        change infEmb τ' _ = _
        rw [e]; rfl
      simp only [this]; exact Complex.conjCLE.contDiff.comp (exp_entry Z i j)
  · simp only [projArch_embArch_ne σ J hu]
    exact contDiff_const

theorem main (h : IsCMExt F E σ) {b : ℝ → GAd σ J} (hb : IsRealLine σ J b) {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J) :
    (∀ g, DifferentiableAt ℝ (fun t => f (g * b t)) 0) ∧ lineDer b f ∈ CcAd σ J := by
  have hβ := lineSm h hb
  have hfin : ∀ t, projFin σ J (b t) = 1 := fun t =>
    mem_infPts.1 (GlobalTheory.RealLineInf.realLine_mem_infPts F E σ n J b hb t)
  have hbc : Continuous b := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J b hb
  have hb0 : b 0 = 1 := GlobalTheory.UAut.ConstAut.realLine_zero h hb
  obtain ⟨-, ⟨m, hm, em⟩, -⟩ := isGroupCoord_infCoord σ J
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ⟨hac, Φ, hΦ, ea⟩, c, hc, rfl⟩ := hf
    set G := fun p : _ × ℝ => Φ (m (p.1, infCoord σ J (projInf σ J (b p.2)))) with hG
    have hGs : ContDiff ℝ ∞ G := hΦ.comp (hm.comp (contDiff_fst.prodMk (hβ.comp contDiff_snd)))
    have hd : ∀ x, HasDerivAt (fun t : ℝ => G (x, t)) (fderiv ℝ G (x, 0) (0, 1)) 0 := fun x =>
      ((hGs.differentiable (by simp)) (x, (0 : ℝ))).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ)))
    have ea' : ∀ (g : GInf σ J) t, a (g * projInf σ J (b t)) = G (infCoord σ J g, t) := fun g t => by
      rw [ea, em]
    have e1 : ∀ g, (fun t => infFin σ J a c (g * b t)) =
        fun t => G (infCoord σ J (projInf σ J g), t) * c (projFin σ J g) := fun g => funext fun t => by
      simp only [infFin, map_mul, hfin, mul_one, ea']
    refine ⟨fun g => by rw [e1]; exact ((hd _).mul_const _).differentiableAt, ?_⟩
    have e2 : lineDer b (infFin σ J a c) =
        infFin σ J (fun g => fderiv ℝ G (infCoord σ J g, 0) (0, 1)) c := funext fun g => by
      rw [lineDer, e1, ((hd _).mul_const _).deriv]; rfl
    rw [e2]
    refine infFin_mem_ccAd ⟨HasCompactSupport.intro hac.isCompact fun g hg => ?_,
      fun x => fderiv ℝ G (x, 0) (0, 1), ?_, fun _ => rfl⟩ hc
    · rw [← (hd _).deriv]
      have hc1 : Continuous fun t => g * projInf σ J (b t) :=
        continuous_const.mul ((continuous_projInf σ J).comp hbc)
      have : ∀ᶠ t in 𝓝 (0 : ℝ), g * projInf σ J (b t) ∈ (tsupport a)ᶜ :=
        hc1.continuousAt.eventually_mem ((isClosed_tsupport a).isOpen_compl.mem_nhds (by simpa [hb0] using hg))
      have e3 : (fun t : ℝ => G (infCoord σ J g, t)) =ᶠ[𝓝 0] fun _ => 0 :=
        this.mono fun t ht => (ea' g t).symm.trans (image_eq_zero_of_notMem_tsupport ht)
      rw [e3.deriv_eq, deriv_const]
    · exact ((hGs.fderiv_right (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const
  | zero => exact ⟨fun g => differentiableAt_const _, by
      have : lineDer b (0 : GAd σ J → ℂ) = 0 := funext fun g => by simp [lineDer]
      rw [this]; exact zero_mem _⟩
  | add f f' _ _ h1 h2 =>
    refine ⟨fun g => (h1.1 g).add (h2.1 g), ?_⟩
    have : lineDer b (f + f') = lineDer b f + lineDer b f' := funext fun g => deriv_add (h1.1 g) (h2.1 g)
    rw [this]; exact add_mem h1.2 h2.2
  | smul a f _ h1 =>
    refine ⟨fun g => (h1.1 g).const_smul a, ?_⟩
    have : lineDer b (a • f) = a • lineDer b f := funext fun g => deriv_const_smul a (h1.1 g)
    rw [this]; exact Submodule.smul_mem _ a h1.2

end MainStatements.WeightKernel.Dec.DDerMemc

theorem MainStatements.WeightKernel.Dec.derMem : MainStatements.WeightKernel.Dec.DerMem :=
  fun _ _ _ _ _ _ _ _ h _ _ _ _ hf _ hb => (MainStatements.WeightKernel.Dec.DDerMemc.main h hb hf).2
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.DSmOfb
section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem smOf : SmOf := by
  intro F E _ _ _ _ _ σ h n J _ f hf k γ hγ g
  exact (GlobalTheory.Orb.isSmoothRealFam_prod (fun i =>
    (GlobalTheory.ThK.CuspTransfer.Smooth.line_fam h (hγ i)).1.comp (contDiff_apply ℝ (fun _ => ℝ) i))).contDiff hf g

end MainStatements.WeightKernel.Dec

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.NsumLevel
section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open PositivityTheory.ThKR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DCore

theorem nsum_level {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (Γ : Subgroup (GAd σ J)) (f : GAd σ J → ℂ)
    (z h κ : GAd σ J) (hκ : ∀ g, f (g * κ) = f g) : nsum Γ f z (h * κ) = nsum Γ f z h := by
  unfold nsum
  exact tsum_congr fun ν => by rw [← mul_assoc, hκ]

theorem nsum_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (Γ : Subgroup (GAd σ J)) (f : GAd σ J → ℂ)
    (z h γ : GAd σ J) (hγ : γ ∈ Γ) : nsum Γ f z (γ * h) = nsum Γ f z h := by
  unfold nsum
  have := (Equiv.mulRight (⟨γ, hγ⟩ : Γ)).tsum_eq (fun ν : Γ => f (z * ν * h))
  simpa [mul_assoc] using this

end MainStatements.WeightKernel.Dec.DCore

namespace MainStatements.WeightKernel.Dec
open MainStatements.WeightKernel.Dec.DCore

theorem core : DerMem → DerVan → Level → SumSm → Variation → NearCusp → Base → Core := by
  intro hDM hDV hL hSS hV hNC hBase D V r X Y hW c hc s
  have hcm := isCMExt_host D
  have hJV := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm).2 V
  have hiso : GlobalTheory.UAut.IsIsoCols D.sp.cm.sig V.gram (pre X s) :=
    GlobalTheory.UAut.isIsoCols_of_isWittFrame hW (sigma_sigma hcm) hJV s.2
  have hcl : IsClosed (unipRad D.sp.cm.sig V.gram (pre X s) : Set (GAd D.sp.cm.sig V.gram)) :=
    GlobalTheory.UAut.unipFlag_const (σ := D.sp.cm.sig) (J := V.gram) (pre X s) 0 ▸
      GlobalTheory.UAut.isClosed_unipFlag hJV (sigma_sigma hcm) hiso _
  obtain ⟨A, hA⟩ := hBase D V r X Y hW c hc
  refine ⟨A, fun m => ?_⟩
  induction m with
  | zero =>
    intro f hf _ C W hC hWc
    obtain ⟨B, hB⟩ := hA (NF D.sp.cm.sig V.gram (pre X s)) inf_le_left f (continuous_of_mem_ccAd hf).1 (continuous_of_mem_ccAd hf).2 C W hC hWc
    exact ⟨B, fun t ht a ha x hx y hy => by simpa using hB t ht a ha x hx y hy⟩
  | succ m ih =>
    intro f hf hvan C W hC hWc
    obtain ⟨q, b, Ω₀, Cv, δ₁, hb, hΩ₀, hδ₁, hCv, hmv⟩ := _root_.GlobalTheory.CompanionTheory.RapidDecay.Mean.mean_value _ _ D.sp.cm.sig hcm _ V.gram hJV
    have hW' : IsCompact ((fun x : GAd D.sp.cm.sig V.gram × GAd D.sp.cm.sig V.gram => x.1 * x.2) '' (W ×ˢ Ω₀)) :=
      (hWc.prod hΩ₀).image (by fun_prop)
    choose B hB using fun i => ih (lineDer (b i) f) (hDM _ _ _ hcm _ _ hJV f hf (b i) (hb i))
      (hDV _ _ _ hcm _ _ hJV _ hcl f hf (b i) (hb i) hvan) C _ hC hW'
    obtain ⟨B₀, hB₀⟩ := ih f hf hvan C W hC hWc
    obtain ⟨U, hUo, hU⟩ := hL _ _ _ hcm _ _ hJV f hf
    obtain ⟨M, hM0, hM⟩ := hNC _ _ _ hcm _ _ hJV r X Y hW W c U hWc hc hUo s
    have hR1 : 1 ≤ max 1 (M / δ₁) := le_max_left _ _
    have hSum : 0 ≤ ∑ i, |B i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨max 1 (M / δ₁) * |B₀| + Cv * M * ∑ i, |B i|, fun t ht a ha x hx y hy => ?_⟩
    have hρ : 0 < ratio t s := ratio_pos ht s
    have hT : 0 ≤ (∏ i, max (t i) 1) ^ A :=
      pow_nonneg (Finset.prod_nonneg fun i _ => le_trans zero_le_one (le_max_right _ _)) _
    have hρm : 0 < (ratio t s)⁻¹ ^ m := pow_pos (inv_pos.2 hρ) m
    have hρm1 : 0 < (ratio t s)⁻¹ ^ (m + 1) := pow_pos (inv_pos.2 hρ) _
    have key : (ratio t s)⁻¹ ^ m = ratio t s * (ratio t s)⁻¹ ^ (m + 1) := by
      rw [pow_succ]; field_simp
    have hB0a : 0 ≤ |B₀| := abs_nonneg _
    have hX : 0 ≤ Cv * M * (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by
      have := mul_nonneg (mul_nonneg hCv hM0) hSum
      positivity
    by_cases hcase : ratio t s ≤ max 1 (M / δ₁)
    · have h1 := hB₀ t ht a ha x hx y hy
      have h2 : B₀ * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m ≤
          |B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hT) hρm.le
      have h3 : ratio t s * (|B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1)) ≤
          max 1 (M / δ₁) * (|B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1)) :=
        mul_le_mul_of_nonneg_right hcase (by positivity)
      have h4 : |B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m =
          ratio t s * (|B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1)) := by
        rw [key]; ring
      have h5 : (max 1 (M / δ₁) * |B₀| + Cv * M * ∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) =
          max 1 (M / δ₁) * (|B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1)) +
          Cv * M * (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by ring
      rw [h5]
      linarith
    · push Not at hcase
      have hδ : M / ratio t s ≤ δ₁ := by
        rw [div_le_iff₀ hρ]
        have h1 : M / δ₁ ≤ max 1 (M / δ₁) := le_max_right _ _
        rw [div_le_iff₀ hδ₁] at h1
        nlinarith
      have hsm := hSS _ _ _ hcm _ _ hJV (NF D.sp.cm.sig V.gram (pre X s)) inf_le_left f hf (x * a⁻¹)
      have hcc : ∀ i, ∀ x' ∈ Ω₀, ‖lineDer (b i) (nsum (NF D.sp.cm.sig V.gram (pre X s)) f (x * a⁻¹)) ((a * y) * x')‖ ≤
          |B i| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m := fun i x' hx' => by
        rw [hsm.2 (b i) (hb i), mul_assoc]
        exact (hB i t ht a ha x hx (y * x') ⟨(y, x'), ⟨hy, hx'⟩, rfl⟩).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hT) hρm.le)
      have hvar := hV _ _ _ hcm _ _ hJV _ (pre X s) hiso f (continuous_of_mem_ccAd hf).1 (continuous_of_mem_ccAd hf).2
        hvan (x * a⁻¹) (a * y) (Cv * (M / ratio t s) * ∑ i, |B i| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m)
        (fun m' hm' => by
          obtain ⟨γ, hγ, u, κ, hu, hκU, hκf, e'⟩ := hM t ht a ha y hy m' hm'
          rw [e', nsum_level _ _ _ _ _ (hU κ hκU hκf), mul_assoc γ, nsum_left _ _ _ _ _ hγ]
          exact hmv _ hsm.1 (a * y) u _ (div_nonneg hM0 hρ.le) hδ hu _ hcc)
      have hsum : ∑ i, |B i| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m =
          (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m := by
        rw [Finset.sum_mul, Finset.sum_mul]
      have h6 : Cv * (M / ratio t s) * ∑ i, |B i| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m =
          Cv * M * (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by
        rw [hsum, pow_succ, div_eq_mul_inv]; ring
      have h7 : 0 ≤ max 1 (M / δ₁) * |B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by positivity
      rw [h6] at hvar
      have h5 : (max 1 (M / δ₁) * |B₀| + Cv * M * ∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) =
          max 1 (M / δ₁) * |B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) +
          Cv * M * (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by ring
      rw [h5]
      linarith

end MainStatements.WeightKernel.Dec
end
end

