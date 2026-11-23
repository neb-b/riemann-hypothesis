module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsContRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0042
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermPairingVanishesOfOrthogonal
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
open scoped NumberField.AdeleRing

private theorem nn_zero {K : Type} [Field K] [NumberField K] : (nn (K := K) 0) = 1 := unipOne_zero 2

private theorem lv_left {K : Type} [Field K] [NumberField K] {F : G1 K (2 + 2) → ℂ}
    (hP : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.PFun F) (m₂ : G1 K 2) (s : ℝ)
    (γ : G1 K 2) (hγ : γ ∈ Gam K 2) (m : G1 K 2) (g : G1 K (2 + 2)) :
    F (lv m₂ (γ * m) s * g) = F (lv m₂ m s * g) := by
  have hmem : lv 1 γ 0 ∈ PK K := (pkLaws.2.1 _).2 ⟨0, 1, ⟨γ, hγ⟩, by
    have h0 : unipOne (K := K) (n := 2 + 2) 2
        ((0 : unipLattice K (2 + 2) 2) : UPos (2 + 2) 2 → 𝔸[K]) = 1 := nn_zero
    rw [h0, one_mul]
    rfl⟩
  have e : lv m₂ (γ * m) s = lv 1 γ 0 * lv m₂ m s := by
    rw [blkLaws.2.1, one_mul, zero_add]
  rw [e, mul_assoc, hP.rat _ hmem]

private theorem rep_ae {K : Type} [Field K] [NumberField K] {μ : Measure (G1 K 2)} [μ.IsHaarMeasure] {v : L2 μ}
    {φ : G1 K 2 → ℂ} (hc : Continuous φ) (hi : ∀ γ ∈ Gam K 2, ∀ y, φ (γ * y) = φ y) (hr : Reps μ v φ) :
    (v : RightCosetSpace (Gam K 2) → ℂ) =ᵐ[quotientMeasure (Gam K 2) μ] fun y => φ (Quotient.out y) := by
  set_option synthInstance.maxHeartbeats 200000 in
    let q : RightCosetSpace (Gam K 2) → ℂ := Quotient.lift φ (fun a b hab => by
      obtain ⟨γ, rfl⟩ := hab
      exact hi γ γ.2 b)
    have hq : Continuous q := (isOpenQuotientMap_mk (Gam K 2)).isQuotientMap.continuous_iff.2 hc
    have hm : ∀ᵐ x ∂(Measure.map (mk (Gam K 2)) (μ.restrict (fundamentalDomain (Gam K 2)))),
        (v : RightCosetSpace (Gam K 2) → ℂ) x = q x := by
      refine (ae_map_iff (measurable_mk (Gam K 2)).aemeasurable
        (measurableSet_eq_fun (Lp.stronglyMeasurable v).measurable hq.measurable)).2 ?_
      exact ae_restrict_of_ae (hr.mono fun y hy => by simpa [q, RightCosetSpace.mk] using hy)
    have hm' : (v : RightCosetSpace (Gam K 2) → ℂ) =ᵐ[quotientMeasure (Gam K 2) μ] q := by
      rwa [map_restrict_eq_quotientMeasure μ (isFundamentalDomain_fundamentalDomain (Gam K 2) μ)] at hm
    refine hm'.trans (Eventually.of_forall fun y => ?_)
    change q y = φ (Quotient.out y)
    conv_lhs => rw [← Quotient.out_eq y]
    rfl

private theorem long_swap {K : Type} [Field K] [NumberField K] (F : G1 K (2 + 2) → ℂ) (m m₂ : G1 K 2) (s : ℝ)
    (k : G1 K (2 + 2)) (hF : Continuous F) :
    (∫ X, F (w0 K * nn X * (lv m m₂ s * k)) ∂unipMeasure K (2 + 2) 2) =
      (Real.exp (4 * s) : ℝ) • ∫ X, F (lv m₂ m (-s) * (w0 K * nn X * k)) ∂unipMeasure K (2 + 2) 2 := by
  obtain ⟨e, he, hm⟩ := adMeas m m₂ s
  have h1 : ∀ X, F (w0 K * nn X * (lv m m₂ s * k)) = F (lv m₂ m (-s) * (w0 K * nn (e X) * k)) := fun X => by
    congr 1
    calc w0 K * nn X * (lv m m₂ s * k) = w0 K * (nn X * lv m m₂ s) * k := by simp only [mul_assoc]
      _ = w0 K * (lv m m₂ s * nn (e X)) * k := by rw [he]
      _ = (w0 K * lv m m₂ s) * nn (e X) * k := by simp only [mul_assoc]
      _ = lv m₂ m (-s) * w0 K * nn (e X) * k := by rw [blkLaws.2.2.2.2.2.2.2.2.2.1]
      _ = _ := by simp only [mul_assoc]
  simp_rw [h1]
  have hme : MeasurableEmbedding (e : (UPos (2 + 2) 2 → _) → _) := e.toHomeomorph.measurableEmbedding
  rw [← hme.integral_map (g := fun X => F (lv m₂ m (-s) * (w0 K * nn X * k))), hm, integral_smul_measure,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

private theorem long_cont {K : Type} [Field K] [NumberField K] {F : G1 K (2 + 2) → ℂ} (hF : Continuous F) (m₂ : G1 K 2) (s : ℝ)
    (k : G1 K (2 + 2)) :
    Continuous fun p : G1 K 2 × (UPos (2 + 2) 2 → 𝔸[K]) => F (lv m₂ p.1 (-s) * (w0 K * nn p.2 * k)) := by
  have hl : Continuous fun p : G1 K 2 × G1 K 2 × ℝ => lv p.1 p.2.1 p.2.2 := by
    obtain ⟨-, -, -, h, -⟩ := blkLaws (K := K)
    exact h
  have h0 : Continuous fun p : G1 K 2 × (UPos (2 + 2) 2 → 𝔸[K]) => ((m₂, p.1, -s) : G1 K 2 × G1 K 2 × ℝ) :=
    continuous_const.prodMk (continuous_fst.prodMk continuous_const)
  have h1 : Continuous fun p : G1 K 2 × (UPos (2 + 2) 2 → 𝔸[K]) => lv m₂ p.1 (-s) := by
    have h := Continuous.comp hl h0
    simpa only [Function.comp_def] using h
  have h2 : Continuous fun p : G1 K 2 × (UPos (2 + 2) 2 → 𝔸[K]) => nn p.2 :=
    (continuous_unipOne (K := K) (n := 2 + 2) 2).comp continuous_snd
  exact hF.comp (h1.mul ((continuous_const.mul h2).mul continuous_const))

private theorem swap_zero {Y X : Type} [MeasurableSpace Y] [MeasurableSpace X] (Q : Measure Y) (ν : Measure X)
    [IsFiniteMeasure Q] [IsFiniteMeasure ν] (f : Y → X → ℂ) (hI : Integrable (Function.uncurry f) (Q.prod ν))
    (hZ : ∀ x, ∫ y, f y x ∂Q = 0) : ∫ y, ∫ x, f y x ∂ν ∂Q = 0 := by
  rw [integral_integral_swap hI]
  simp only [hZ, integral_zero]

theorem UpperTheory.constantTerm_pairing_vanishes_of_orthogonal :
    ∀ {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ ρ : Submodule ℂ (L2 μ₂)) (F : G1 K (2 + 2) → ℂ) (h : G1 K 2 → ℂ),
          UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.PFun F → InBand F → Slices τ₁ τ₂ F → τ₂ ⟂ ρ → Continuous h → (∀ γ ∈ Gam K 2, ∀ m, h (γ * m) = h m) → (∃ v ∈ ρ, Reps μ₂ v h) →
          ∀ (m₂ : G1 K 2) (s : ℝ), ∀ k ∈ KG K (2 + 2),
            Integrable (fun y : RightCosetSpace (Gam K 2) => (∫ X, F (w0 K * nn X * (lv (Quotient.out y) m₂ s * k)) ∂unipMeasure K (2 + 2) 2) * starRingEnd ℂ (h (Quotient.out y))) (quotientMeasure (Gam K 2) μ₂) ∧
            ∫ y : RightCosetSpace (Gam K 2), (∫ X, F (w0 K * nn X * (lv (Quotient.out y) m₂ s * k)) ∂unipMeasure K (2 + 2) 2) * starRingEnd ℂ (h (Quotient.out y)) ∂quotientMeasure (Gam K 2) μ₂ = 0 := by
  set_option synthInstance.maxHeartbeats 200000 in
   intro K _ _ μ₂ _ τ₁ τ₂ ρ F h hP hB hS hort hc hi hv m₂ s k hk
   obtain ⟨v, hvρ, hvr⟩ := hv
   have hQf := isFiniteMeasure_quotientMeasure (K := K) (n := 2) μ₂
   obtain ⟨R, hR⟩ := hB
   obtain ⟨B, hBd⟩ := hP.bdd
   obtain ⟨C, hCc, hC⟩ := (longCell (K := K)).2 (R - s)
   haveI : IsFiniteMeasure ((unipMeasure K (2 + 2) 2).restrict C) := ⟨by simpa using hCc.measure_lt_top⟩
   let Φ : G1 K 2 → (UPos (2 + 2) 2 → 𝔸[K]) → ℂ := fun m X => F (lv m₂ m (-s) * (w0 K * nn X * k))
   let P : RightCosetSpace (Gam K 2) → (UPos (2 + 2) 2 → 𝔸[K]) → ℂ := fun y X => Φ (Quotient.out y) X
   let H : RightCosetSpace (Gam K 2) → ℂ := fun y => h (Quotient.out y)
   have hΦi : ∀ X, ∀ γ ∈ Gam K 2, ∀ m, Φ (γ * m) X = Φ m X := fun X γ hγ m => lv_left hP m₂ (-s) γ hγ m _
   have hΦc : Continuous (Function.uncurry Φ) := long_cont hP.cont m₂ s k
   have hPc : Continuous (Function.uncurry P) := by
     have hq := (isOpenQuotientMap_mk (Gam K 2)).prodMap (IsOpenQuotientMap.id (X := UPos (2 + 2) 2 → 𝔸[K]))
     rw [hq.isQuotientMap.continuous_iff]
     refine hΦc.congr fun p => ?_
     change Φ p.1 p.2 = Φ (Quotient.out (mk (Gam K 2) p.1)) p.2
     have he : mk (Gam K 2) (Quotient.out (mk (Gam K 2) p.1)) = mk (Gam K 2) p.1 := Quotient.out_eq _
     obtain ⟨γ, hγ⟩ := Quotient.exact he
     rw [← hγ]
     exact (hΦi p.2 γ γ.2 p.1).symm
   have hPb : ∀ y X, ‖P y X‖ ≤ B := fun y X => hBd _
   have hsupp : ∀ m X, X ∉ C → Φ m X = 0 := fun m X hX => by
     by_contra hne
     have h1 := hR _ hne
     have h2 := (hpSpec (K := K)).1 0 m₂ m (-s) (w0 K * nn X * k)
     rw [nn_zero, one_mul] at h2
     rw [h2, abs_le] at h1
     exact hX (hC X k hk (by linarith [h1.1]))
   have hHr := rep_ae hc hi hvr
   have hHm : MemLp H 2 (quotientMeasure (Gam K 2) μ₂) := (Lp.memLp v).ae_eq hHr
   have hHi : Integrable H (quotientMeasure (Gam K 2) μ₂) := hHm.integrable one_le_two
   have hHs : AEStronglyMeasurable H (quotientMeasure (Gam K 2) μ₂) := hHi.1
   have hI : Integrable (Function.uncurry fun y X => P y X * starRingEnd ℂ (H y))
       ((quotientMeasure (Gam K 2) μ₂).prod ((unipMeasure K (2 + 2) 2).restrict C)) := by
     have hm : AEStronglyMeasurable (fun p : RightCosetSpace (Gam K 2) × (UPos (2 + 2) 2 → 𝔸[K]) => starRingEnd ℂ (H p.1))
         ((quotientMeasure (Gam K 2) μ₂).prod ((unipMeasure K (2 + 2) 2).restrict C)) :=
       (continuous_star.comp_aestronglyMeasurable hHs).comp_fst
     refine Integrable.mono' (hHi.norm.mul_prod (integrable_const B))
       (hPc.aestronglyMeasurable.mul hm) (Eventually.of_forall fun p => ?_)
     show ‖P p.1 p.2 * starRingEnd ℂ (H p.1)‖ ≤ ‖H p.1‖ * B
     rw [norm_mul, RCLike.norm_conj, mul_comm]
     exact mul_le_mul_of_nonneg_left (hPb _ _) (norm_nonneg _)
   have hT : ∀ y : RightCosetSpace (Gam K 2),
       (∫ X, F (w0 K * nn X * (lv (Quotient.out y) m₂ s * k)) ∂unipMeasure K (2 + 2) 2) * starRingEnd ℂ (h (Quotient.out y)) =
         (Real.exp (4 * s) : ℝ) • ∫ X in C, P y X * starRingEnd ℂ (H y) ∂unipMeasure K (2 + 2) 2 := fun y => by
     rw [long_swap F _ m₂ s k hP.cont, smul_mul_assoc, integral_mul_const]
     congr 2
     exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun X hX => hsupp _ X hX).symm
   have hZ : ∀ X, ∫ y, P y X * starRingEnd ℂ (H y) ∂quotientMeasure (Gam K 2) μ₂ = 0 := fun X => by
     obtain ⟨u, huτ, hur⟩ := (hS (lv 1 1 (-s) * (w0 K * nn X * k))).2 m₂
     have hur' : Reps μ₂ u (fun m => Φ m X) := by
       have e : (fun m => F (lv m₂ m 0 * (lv 1 1 (-s) * (w0 K * nn X * k)))) = fun m => Φ m X := by
         funext m
         show _ = F (lv m₂ m (-s) * (w0 K * nn X * k))
         rw [← mul_assoc, blkLaws.2.1, mul_one, mul_one, zero_add]
       rwa [e] at hur
     have h1 : (u : RightCosetSpace (Gam K 2) → ℂ) =ᵐ[quotientMeasure (Gam K 2) μ₂] fun y => P y X :=
       rep_ae (hΦc.comp (continuous_id.prodMk continuous_const)) (hΦi X) hur'
     have h3 : inner ℂ v u = 0 := inner_eq_zero_symm.1 (Submodule.isOrtho_iff_inner_eq.1 hort u huτ v hvρ)
     rw [L2.inner_def] at h3
     rw [← h3]
     refine integral_congr_ae ?_
     filter_upwards [h1, hHr] with y a b
     rw [a, b, RCLike.inner_apply]
   have hI2 : Integrable (fun y => ∫ X in C, P y X * starRingEnd ℂ (H y) ∂unipMeasure K (2 + 2) 2)
       (quotientMeasure (Gam K 2) μ₂) := hI.integral_prod_left
   refine ⟨?_, ?_⟩
   · simp_rw [hT]
     exact hI2.smul (Real.exp (4 * s))
   · simp_rw [hT]
     rw [integral_smul, @swap_zero _ _ _ _ _ _ hQf _ _ hI hZ, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicWeilCharProperties
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Wd

private theorem cw_cyc {l : ℕ} [Fact l.Prime] (L : FinExt l) (n : ℤ) :
    Continuous fun g : GQ l => (((cycL L g ^ n : (↥L.1)ˣ) : ↥L.1) : Om l) := by
  have h0 := UpperTheory.V.Loc.cycFacts l l
  have h1 : Continuous fun g : GQ l => (((cycL L g : (↥L.1)ˣ) : ↥L.1) : Om l) := by
    have : (fun g : GQ l => (((cycL L g : (↥L.1)ˣ) : ↥L.1) : Om l)) =
        fun g => algebraMap ℚ_[l] (Om l) (((Loc.cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
      funext g
      rw [← h0.2.2 g]
      rfl
    rw [this]
    have h2 : Continuous fun z : ℤ_[l] => (z : ℚ_[l]) := continuous_subtype_val
    exact (continuous_algebraMap ℚ_[l] (Om l)).comp (h2.comp (Units.continuous_val.comp h0.1))
  have : (fun g : GQ l => (((cycL L g ^ n : (↥L.1)ˣ) : ↥L.1) : Om l)) =
      fun g => (((cycL L g : (↥L.1)ˣ) : ↥L.1) : Om l) ^ n := by
    funext g
    rw [Units.val_zpow_eq_zpow_val]
    exact map_zpow₀ L.1.val _ _
  rw [this]
  exact h1.zpow₀ n fun g => Or.inl ((map_ne_zero L.1.val).2 (Units.ne_zero (cycL L g)))

private theorem cw_lc {l : ℕ} [Fact l.Prime] (K K' : FinExt l) {C : Type} [Group C] (χ : ↥(GK K) →* C)
    (hχ : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → χ g = 1) : IsLocallyConstant χ := by
  have := K'.2
  have ho : IsOpen ((GK K' : Subgroup (GQ l)) : Set (GQ l)) := IntermediateField.fixingSubgroup_isOpen K'.1
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨{y | ((x⁻¹ * y : ↥(GK K)) : GQ l) ∈ GK K'}, ?_, ?_, fun y hy => ?_⟩
  · exact ho.preimage (continuous_subtype_val.comp (continuous_const.mul continuous_id))
  · simp
  · have := hχ _ hy
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm

private theorem cw_eta {l : ℕ} [Fact l.Prime] (K K' L : FinExt l) (κ χ : ↥(GK K) →* (↥L.1)ˣ) (m : ℤ)
    (hκc : Continuous (fun g => ((κ g : ↥L.1) : Om l)))
    (hK' : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → χ g = 1) :
    ∃ η : ↥(GK K) →* (↥L.1)ˣ, (∀ g, κ g = cycL L (g : GQ l) ^ m * χ g * η g) ∧
      Continuous (fun g => ((η g : ↥L.1) : Om l)) := by
  let ε : ↥(GK K) →* (↥L.1)ˣ := (cycL L).comp (GK K).subtype
  refine ⟨κ * ε ^ (-m) * χ⁻¹, fun g => ?_, ?_⟩
  · change κ g = _ * (κ g * cycL L (g : GQ l) ^ (-m) * (χ g)⁻¹)
    rw [zpow_neg]
    generalize cycL L (g : GQ l) ^ m = a
    rw [mul_mul_mul_comm, mul_inv_cancel, mul_one, mul_comm (κ g), mul_inv_cancel_left]
  · have h3 : Continuous fun g => ((((χ g)⁻¹ : (↥L.1)ˣ) : ↥L.1) : Om l) :=
      ((cw_lc K K' χ hK').comp fun u => (((u⁻¹ : (↥L.1)ˣ) : ↥L.1) : Om l)).continuous
    exact (hκc.mul ((cw_cyc L (-m)).comp continuous_subtype_val)).mul h3

private theorem cw_line {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw)
    (L : FinExt l) (V : Type) [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) (h1 : finrank ↥L.1 V = 1) (hV : IsPst P ρ)
    (u : V ⊗[ℚ_[l]] Bst P) (hmem : u ∈ Dpst P ρ) (hu0 : u ≠ 0) (e : ↥L.1) (he0 : e ≠ 0)
    (hu : e • (phiV P ↥L.1 V ^ resDeg l w) u = u) (σ : ↥(Weil h)) (s : ↥L.1)
    (hs : stRep P ρ (weilToGK Bw h σ) u = s • u) (y : WDSpace P ι ρ) :
    haveI := hV.finite; wdRho P ι Bw h hj ρ σ y = ι ((e⁻¹ ^ (-deg σ) * s : ↥L.1) : Om l) • y := by
  refine UpperTheory.weil_deligne_rank_one_line F Ω l P ι w A h O Bw hj L V ρ h1 hV ⟨u, hmem⟩ (fun h0 => hu0 (congrArg Subtype.val h0)) e⁻¹
    (inv_ne_zero he0) (Subtype.ext ?_) σ s (Subtype.ext hs) y
  have h1 : ((phiD P ρ ^ resDeg l w) ⟨u, hmem⟩).1 = (phiV P ↥L.1 V ^ resDeg l w) u := by
    rw [phiD, Module.End.pow_restrict]
    rfl
  rw [h1]
  change (phiV P ↥L.1 V ^ resDeg l w) u = e⁻¹ • u
  exact (eq_inv_smul_iff₀ he0).2 hu

private theorem cw_calc {k : Type} [Field k] (a κ c χ η : kˣ) (l : k) (m d : ℤ) (f : ℕ) (h1 : κ = c ^ m * χ * η)
    (h2 : η = a ^ d) :
    ((a : k) * l ^ (m * (f : ℕ)))⁻¹ ^ (-d) * (χ : k) = (l ^ f) ^ (m * d) * ((κ * c ^ (-m) : kˣ) : k) := by
  have h3 : κ * c ^ (-m) = a ^ d * χ := by
    rw [h1, h2, zpow_neg, mul_comm, mul_assoc (c ^ m), inv_mul_cancel_left, mul_comm]
  rw [h3, inv_zpow', neg_neg, mul_zpow, ← zpow_natCast, ← zpow_mul, ← zpow_mul, Units.val_mul,
    Units.val_zpow_eq_zpow_val, show m * (f : ℕ) * d = (f : ℕ) * (m * d) by ring]
  ring

private theorem cw_fin {l : ℕ} [Fact l.Prime] (ι : Om l ≃+* ℂ) (L : FinExt l) (f : ℕ) (n : ℤ) (x : ↥L.1) :
    ι (((((l : ↥L.1) ^ f) ^ n * x : ↥L.1)) : Om l) = ((l ^ f : ℕ) : ℂ) ^ n * ι (x : Om l) := by
  have h1 : L.1.val (((l : ↥L.1) ^ f) ^ n * x) = ((l : Om l) ^ f) ^ n * L.1.val x := by
    rw [map_mul, map_zpow₀, map_pow, map_natCast]
  refine (congrArg ι h1).trans ?_
  rw [map_mul, map_zpow₀, map_pow, map_natCast, Nat.cast_pow]
  rfl

private theorem cw_unr {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : Induces Bw) {C : Type} [Group C] (η : ↥(GK Bw.Kw) →* C)
    (hηI : ∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ Loc.Iq l → η g = 1) (σ : ↥(Weil h)) :
    η (weilToGK Bw h σ) = η (weilToGK Bw h (frob h)) ^ deg σ := by
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  have hτI : (weilToGK Bw h (ineIncl h τ) : GQ l) ∈ Loc.Iq l := by
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
    have := weilToGK_frobUr hj (ineIncl h τ) (a := 0) (b := 0) (actsAs_zero_iff.mpr τ.2) ⟨x, hx⟩
    simpa using this
  conv_lhs => rw [hτ]
  rw [map_mul, map_mul, hηI _ hτI, mul_one, map_zpow, map_zpow]

theorem UpperTheory.cyclotomicWeilChar_properties :
    UpperTheory.V.Af.Wd.CharWD := by
  intro F Ω _ _ _ _ _ l _ ι w A h O _ _ _ Bw hj L κ χ m hκc hχ hI hκ σ y
  obtain ⟨K', hK'⟩ := hχ
  obtain ⟨η, hκη, hηc⟩ := cw_eta Bw.Kw K' L κ χ m hκc hK'
  have hηI : ∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ Loc.Iq l → η g = 1 := fun g hg =>
    mul_left_cancel ((hκη g).symm.trans ((hI g hg).trans (mul_one _).symm))
  obtain ⟨u, hu0, hu1, hu2⟩ := UpperTheory.weilDeligne_character_twist_period l Bw.Kw L κ χ η m hκη hηc hηI
  have hF := (UpperTheory.crystalline_period_ring_properties F Ω l w A h O Bw hj).1
  have hmem : u ∈ Dpst (Loc.PP l) (Loc.chRep κ) :=
    (mem_Dpst _ _).2 ⟨K', fun g hg => by rw [hu1, hK' g hg, Units.val_one, one_smul]⟩
  have hl : (l : ↥L.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have he0 : (η (weilToGK Bw h (frob h)) : ↥L.1) * (l : ↥L.1) ^ (m * (resDeg l w : ℕ)) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (zpow_ne_zero _ hl)
  have key := cw_line (Loc.PP l) ι h Bw hj L ↥L.1 (Loc.chRep κ) (Module.finrank_self _) hκ u hmem hu0 _ he0
    (hu2 _ _ hF) σ _ (hu1 _) y
  have h3 := cw_calc _ _ _ _ _ (l : ↥L.1) m (deg σ) (resDeg l w) (hκη (weilToGK Bw h σ)) (cw_unr h Bw hj η hηI σ)
  have h4 := (congrArg (fun x : ↥L.1 => ι (x : Om l)) h3).trans (cw_fin ι L _ _ _)
  rw [← normV_eq_pow (hj.mem_placesOver h)] at h4
  exact key.trans (congrArg (fun z : ℂ => z • y) h4)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiltrationInverseFrobeniusMatrix
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

private theorem slopeHi_spec {L : Type} [Field L] {d : ℕ} (G : Matrix (Fin d) (Fin d) L) (hG : IsUnit G.det) {a : L}
    (ha : a ∈ spectrum L G) : a ≠ 0 ∧ a⁻¹ ∈ spectrum L (G⁻¹).transpose := by
  rw [spectrum.mem_iff] at ha
  have h0 : a ≠ 0 := by
    rintro rfl
    apply ha
    rw [map_zero, zero_sub]
    exact ((Matrix.isUnit_iff_isUnit_det _).2 hG).neg
  refine ⟨h0, spectrum.mem_iff.2 fun hu => ha ?_⟩
  have e : (algebraMap L (Matrix (Fin d) (Fin d) L) a⁻¹ - (G⁻¹).transpose).transpose * ((-a) • G) =
      algebraMap L (Matrix (Fin d) (Fin d) L) a - G := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.sub_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.nonsing_inv_mul _ hG, smul_sub, smul_smul, neg_mul,
      mul_inv_cancel₀ h0, neg_smul, neg_smul, one_smul]
    abel
  rw [← e]
  refine ((Matrix.isUnit_transpose _).2 hu).mul ?_
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
  exact ((IsUnit.mk0 _ (neg_ne_zero.2 h0)).pow _).mul hG

private theorem slopeHi_inv {R S : Type} [Field R] [CommRing S] [Nontrivial S] (j : R →+* S) (ψ : S →+* S)
    {d : ℕ} (M M' : Matrix (Fin d) (Fin d) S) (F : Matrix (Fin d) (Fin d) R) (hMM : M * M' = 1)
    (h : M.map ψ = M * F.map j) :
    IsUnit F.det ∧ M'.transpose.map ψ = M'.transpose * (F⁻¹).transpose.map j := by
  have hMM' : M' * M = 1 := mul_eq_one_comm.1 hMM
  have e1 : M'.map ψ * M.map ψ = 1 := by
    rw [← Matrix.map_mul, hMM', Matrix.map_one _ (map_zero _) (map_one _)]
  have hF : IsUnit F.det := by
    refine IsUnit.mk0 _ fun h0 => ?_
    have := congrArg Matrix.det e1
    have h1 : (F.map j).det = 0 := by
      have h2 := RingHom.map_det j F
      rw [h0, map_zero] at h2
      exact h2.symm
    rw [h, Matrix.det_mul, Matrix.det_mul, h1, mul_zero, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨hF, ?_⟩
  rw [Matrix.transpose_map, Matrix.transpose_map, ← Matrix.transpose_mul]
  congr 1
  have e2 : F.map j * (F⁻¹).map j = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hF, Matrix.map_one _ (map_zero _) (map_one _)]
  calc M'.map ψ = M'.map ψ * (M * (F.map j * (F⁻¹).map j) * M') := by
        rw [e2, Matrix.mul_one, hMM, Matrix.mul_one]
    _ = _ := by
        rw [← Matrix.mul_assoc M, ← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul]

theorem UpperTheory.filtration_inverse_frobenius_matrix :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), 0 < f → (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ {d : ℕ} (M M' : Matrix (Fin d) (Fin d) (Bcr l)) (A F : Matrix (Fin d) (Fin d) ↥(K0 K)), M * M' = 1 → IsUnit A.det → M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l)) → M.map (((PP l).φB)^[f]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ b : ℤ, (∀ i j, (PP l).ιB (M' i j) ∈ ((PP l).PD (botExt l)).Fil (-b)) → ∀ β ∈ spectrum (Om l) (F.map (algebraMap ↥(K0 K) (Om l))), ‖((l : Om l) ^ f) ^ b * β⁻¹‖ ≤ 1 := by
  intro l _ K f hf hσ d M M' A F hMM _ hA hF b hb β hβ
  haveI : Nontrivial (Bcr l) := ⟨⟨1, 0, fun h => ((PP l).PD K).not_mem_filtration_two (by
    rw [← mul_one ((PP l).PD K).t, h, mul_zero, map_zero]; exact Submodule.zero_mem _)⟩⟩
  have hc : ((PP l).φB)^[f] = ⇑((PP l).φB ^ f) := (AlgHom.coe_pow _ _).symm
  obtain ⟨hA1, hA2⟩ := slopeHi_inv (algebraMap ↥(K0 K) (Bcr l)) ((PP l).φB : Bcr l →+* Bcr l) M M' A hMM hA
  obtain ⟨hF1, hF2⟩ := slopeHi_inv (algebraMap ↥(K0 K) (Bcr l)) (((PP l).φB ^ f : Bcr l →ₐ[ℚ_[l]] Bcr l) : Bcr l →+* Bcr l)
    M M' F hMM (by rw [hc] at hF; exact hF)
  have hu : IsUnit (F.map (algebraMap ↥(K0 K) (Om l))).det := by
    have := hF1.map (algebraMap ↥(K0 K) (Om l))
    rw [RingHom.map_det] at this
    exact this
  obtain ⟨-, ha'⟩ := slopeHi_spec _ hu hβ
  have e : (F.map (algebraMap ↥(K0 K) (Om l)))⁻¹ = (F⁻¹).map (algebraMap ↥(K0 K) (Om l)) := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hF1, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [e, ← Matrix.transpose_map] at ha'
  have h := UpperTheory.filtration_entries_of_frobenius_matrix K f hf hσ M'.transpose M.transpose (A⁻¹).transpose (F⁻¹).transpose
    (by rw [← Matrix.transpose_mul, hMM, Matrix.transpose_one])
    (by rw [Matrix.det_transpose]; exact Matrix.isUnit_nonsing_inv_det _ hA1)
    hA2 (by rw [hc]; exact hF2) (-b) (fun i j => hb j i) β⁻¹ ha'
  rwa [neg_neg] at h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalSpanAdjoinOrbitOfCommuting
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_span_adjoin_orbit_of_commuting :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (x : M) (s : Set (Module.End ℂ M)), s.Finite → (∀ a ∈ s, ∀ b ∈ s, a * b = b * a) → (∀ T ∈ s, AlgMod (Submodule.span ℂ {x}) ⊥ T) → FiniteDimensional ℂ (Submodule.span ℂ ((fun T : Module.End ℂ M => T x) '' (Algebra.adjoin ℂ s : Set (Module.End ℂ M)))) := by
  intro M _ _ x s hs hc h
  refine UpperTheory.finiteDimensional_span_adjoin_apply_of_commuting_algebraic M s x hc (FiniteDimensional.span_of_finite ℂ hs) fun a ha => ?_
  obtain ⟨p, hp, hx⟩ := h a ha
  exact ⟨p, hp.ne_zero, (Submodule.mem_bot ℂ).1 (hx x (Submodule.mem_span_singleton_self x))⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepresentationModelOverFiniteExtension
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Wd

private theorem exists_lift {Γ k K : Type} [Group Γ] [Field k] [Field K] [Algebra k K] (L : IntermediateField k K)
    (ψ : Γ →* Kˣ) (hψ : ∀ g, (ψ g : K) ∈ L) : ∃ ψL : Γ →* (↥L)ˣ, ∀ g, ((ψL g : ↥L) : K) = ψ g :=
  ⟨MonoidHom.toHomUnits (((Units.coeHom K).comp ψ).codRestrict L hψ), fun _ => rfl⟩

private theorem toMatrix_repE {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) {m : ℕ} (L : FinExt l) (r : ↥Gw →* GL (Fin m) ↥L.1) (g : ↥(GK Bw.Kw)) :
    LinearMap.toMatrix (Pi.basisFun ↥L.1 (Fin m)) (Pi.basisFun ↥L.1 (Fin m)) (Bw.repE L r g) =
      (r (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L.1) := by
  have e : Bw.repE L r g = Matrix.toLin' (r (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L.1) :=
    LinearMap.ext fun _ => rfl
  rw [e, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem UpperTheory.galois_representation_model_over_finite_extension :
    UpperTheory.V.Af.Wd.Model := by
  intro F Ω _ _ _ _ _ l _ ι n r w A h O _ _ _ Bw hj κ χ hχ hfl hr
  obtain ⟨p, hp⟩ := hfl
  let r' : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l) :=
    (MulAut.conj p).toMonoidHom.comp (r.comp (Dec (F := F) A).subtype)
  have hr' : ∀ s, r' s = p * r s * p⁻¹ := fun _ => rfl
  have hc := GlobalTheory.T.fontaineParameter_invariant_under_conjugation F Ω l ι n (Loc.PP l) (Loc.AIP l) (Loc.tiedP l) w A h O Bw hj
    (r.comp (Dec (F := F) A).subtype) r' p hr' hr
  obtain ⟨hpst, hwd⟩ := hc
  have hm := wdAt_of_isPstAt ι Bw h hj hpst
  obtain ⟨L₁, r₁, hm₁, hp₁, e₁⟩ := hm
  have hL : ∃ L : FinExt l, L₁.1 ≤ L.1 ∧ ∀ i s, (χ i s : Om l) ∈ L.1 := by
    have hfin : (⋃ i, Units.val '' Set.range (χ i)).Finite := Set.finite_iUnion fun i => (hχ i).image _
    haveI : Finite ↥(⋃ i, Units.val '' Set.range (χ i)) := hfin
    refine ⟨supExt L₁ ⟨IntermediateField.adjoin ℚ_[l] (⋃ i, Units.val '' Set.range (χ i)),
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩,
      le_sup_left, fun i s => ?_⟩
    exact (le_sup_right : IntermediateField.adjoin ℚ_[l] (⋃ i, Units.val '' Set.range (χ i)) ≤ _)
      (IntermediateField.subset_adjoin _ _ (Set.mem_iUnion.2 ⟨i, _, ⟨s, rfl⟩, rfl⟩))
  obtain ⟨L, h₁, hχL⟩ := hL
  have hm₂ := hm₁.enlarge h₁
  have hp₂ := _root_.GlobalTheory.PstExt.isPst_enlarge (Loc.PP l) Bw h₁ r₁ hp₁
  have e₂ := GlobalTheory.T.potSemistableParameter_coefficientField_enlarge (Loc.PP l) ι Bw h hj h₁ r₁ hp₁
  generalize mapRep (IntermediateField.inclusion h₁).toRingHom r₁ = r₂ at hm₂ hp₂ e₂
  have er : ∀ s i j, (p * r (s : ↥(Dec (F := F) A)) * p⁻¹ : GL (Fin n) (Qbar l)) i j =
      (((r₂ s : Matrix (Fin n) (Fin n) ↥L.1) i j : ↥L.1) : Om l) :=
    fun s i j => by rw [← hr', ← hm₂.2]; rfl
  have hκL : ∀ i s, (κ i s : Om l) ∈ L.1 := fun i s => by
    rw [← (hp s).2 i, er]; exact SetLike.coe_mem _
  choose κL hκ using fun i => exists_lift L.1 ((κ i).comp Bw.e.symm.toMonoidHom) fun g => hκL i _
  choose χL hχ' using fun i => exists_lift L.1
    (((χ i).comp (Dec (F := F) A).subtype).comp Bw.e.symm.toMonoidHom) fun g => hχL i _
  refine ⟨L, Bw.repE L r₂, κL, χL, hp₂, hwd.symm.trans (e₁.trans e₂.symm),
    ⟨Pi.basisFun _ _, fun g => ⟨fun i j hij => ?_, fun i => ?_⟩⟩, fun i s => ?_, fun i s => ?_⟩
  · rw [toMatrix_repE]
    exact Subtype.ext ((er _ i j).symm.trans ((hp _).1 i j hij))
  · rw [toMatrix_repE]
    exact Subtype.ext (((er _ i i).symm.trans ((hp _).2 i)).trans (hκ i g).symm)
  · rw [hκ]
    exact congrArg (fun t => (κ i t : Qbar l)) (Bw.e.symm_apply_apply s)
  · rw [hχ']
    exact congrArg (fun t : ↥(Dec (F := F) A) => (χ i t : Qbar l)) (Bw.e.symm_apply_apply s)
end

