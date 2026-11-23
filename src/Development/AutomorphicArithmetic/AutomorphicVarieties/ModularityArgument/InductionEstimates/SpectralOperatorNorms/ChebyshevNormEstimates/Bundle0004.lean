module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.BloIn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PseudoEisensteinSectionPfunInBandSlicesReps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0046
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle0001
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsContRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistUnitary

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.CompLine
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem lev_eq {R : Type} [CommRing R] (r s : ℕ) (x : GL (Fin r) R) (y : GL (Fin s) R) :
    GlobalTheory.CompanionTheory.CTFin.lev R r s (x, y) = blk x y := by
  have hs : GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) = finSumFinEquiv := by
    ext (x | x) <;> simp
  refine Units.ext ?_
  rw [GlobalTheory.CompanionTheory.CTFin.lev, GlobalTheory.SmGL.val_emb₂, hs]
  rfl

private theorem blk_nil {R : Type} [CommRing R] (x : GL (Fin 2) R) (y : GL (Fin 0) R) : blk x y = x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (Matrix.fromBlocks x.val 0 0 y.val) (finSumFinEquiv.symm (Fin.castAdd 0 i)) (finSumFinEquiv.symm (Fin.castAdd 0 j)) = _
  rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
  rfl

private theorem ct_nil {K : Type} [Field K] [NumberField K] (ψ : AdelicGLn.AdelicGL K (2 + 0) → ℂ) (g : AdelicGLn.AdelicGL K (2 + 0)) :
    constantTerm 2 ψ g = ψ g := by
  haveI : IsEmpty (UPos (2 + 0) 2) := ⟨fun p => by have := p.2.2; have := p.1.2.isLt; omega⟩
  have h1 : unipFundamentalDomain K (2 + 0) 2 = Set.univ := Set.eq_univ_of_forall fun X p => isEmptyElim p
  have h2 : ∀ X : UPos (2 + 0) 2 → AdeleRing (𝓞 K) K, unipGL X = 1 := fun X => by
    rw [Subsingleton.elim X 0, unipGL_zero]
  rw [constantTerm, h1, Measure.restrict_univ, unipMeasure, Measure.pi_of_empty]
  simp only [h2, one_mul]
  simp

private theorem zt_add (K : Type) [Field K] [NumberField K] (n : ℕ) (a b : ℝ) : BW.zt K n (a + b) = BW.zt K n a * BW.zt K n b := by
  rw [BW.zt, BW.zt, BW.zt, ← map_mul]
  congr 1
  exact Subtype.ext (Real.exp_add a b)

private theorem blk_zt (K : Type) [Field K] [NumberField K] (a : ℝ) : blk (BW.zt K 2 a) (BW.zt K 2 a) = BW.zt K (2 + 2) (2 * a) := by
  have h : rpowHom (((2 : ℕ) * Module.finrank ℚ K : ℝ))⁻¹ ⟨Real.exp a, Real.exp_pos a⟩ =
      rpowHom (((2 + 2 : ℕ) * Module.finrank ℚ K : ℝ))⁻¹ ⟨Real.exp (2 * a), Real.exp_pos _⟩ := by
    refine Subtype.ext ?_
    change Real.exp a ^ _ = Real.exp (2 * a) ^ _
    rw [← Real.exp_mul, ← Real.exp_mul]
    congr 1
    push_cast
    rw [mul_inv, mul_inv]
    ring
  refine Units.ext ?_
  simp only [BW.zt, centralSection, MonoidHom.comp_apply, h, scalarUnits_apply, coe_diagUnits, blk]
  rw [Matrix.fromBlocks_diagonal, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  congr 1
  funext i
  induction i using Fin.addCases <;> simp

private theorem pt_eq {K : Type} [Field K] [NumberField K] (y₁ y₂ : G1 K 2) (a b : ℝ) :
    blk (BW.zt K 2 a * (y₁ : AdelicGLn.AdelicGL K 2)) (BW.zt K 2 b * (y₂ : AdelicGLn.AdelicGL K 2)) =
      BW.zt K (2 + 2) (a + b) * (lv y₁ y₂ ((a - b) / 2) : G1 K (2 + 2)) := by
  have e : ∀ (t : ℝ) (y : AdelicGLn.AdelicGL K 2), y * UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.zt K t = BW.zt K 2 t * y := fun t y =>
    (centralSection_mul_comm _ y).symm
  rw [blkLaws.1, e, e, show a + b = 2 * ((a + b) / 2) by ring, ← blk_zt, blkLaws.2.2.2.2.2.1, ← mul_assoc, ← mul_assoc,
    ← zt_add, ← zt_add]
  congr 3 <;> ring

private theorem int_pair {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {S : Set (Pl E)} (b : BW.Blo S 2)
    {τ : Submodule ℂ (L2 (BW.mu1 E 2))} {m B} (hb : BloIn b τ m B) {v : L2 (BW.mu1 E 2)} {φ : G1 E 2 → ℂ} (hc : Continuous φ)
    (hr : Reps (BW.mu1 E 2) v φ) :
    Integrable (fun x : RightCosetSpace (Gam E 2) => φ (Quotient.out x) *
      starRingEnd ℂ (b.f.1 ((Quotient.out x : G1 E 2) : GlobalTheory.CuspRep.GA E 2))) (quotientMeasure (Gam E 2) (BW.mu1 E 2)) := by
  have key : ∀ {w : L2 (BW.mu1 E 2)} {ψ : G1 E 2 → ℂ}, Continuous ψ → Reps (BW.mu1 E 2) w ψ →
      MemLp (fun x : RightCosetSpace (Gam E 2) => ψ (Quotient.out x)) 2 (quotientMeasure (Gam E 2) (BW.mu1 E 2)) := by
    intro w ψ hc hr
    have hinv : ∀ γ ∈ Gam E 2, ∀ y, ψ (γ * y) = ψ y := fun γ hγ => by
      have h1 : (fun y => ψ (γ * y)) =ᵐ[BW.mu1 E 2] ψ := by
        filter_upwards [hr, (measurePreserving_mul_left (BW.mu1 E 2) γ).quasiMeasurePreserving.ae hr] with y a b
        rw [← a, ← b, mk_mul_of_mem hγ]
      exact congrFun (((hc.comp (continuous_const_mul γ)).ae_eq_iff_eq _ hc).1 h1)
    let q : RightCosetSpace (Gam E 2) → ℂ := Quotient.lift ψ (fun a b hab => by
      obtain ⟨γ, rfl⟩ := hab
      exact hinv γ γ.2 b)
    have hq : Continuous q := (isOpenQuotientMap_mk (Gam E 2)).isQuotientMap.continuous_iff.2 hc
    set_option synthInstance.maxHeartbeats 200000 in
    have he : (w : RightCosetSpace (Gam E 2) → ℂ) =ᵐ[quotientMeasure (Gam E 2) (BW.mu1 E 2)] q := by
      have hm : ∀ᵐ x ∂(Measure.map (mk (Gam E 2)) ((BW.mu1 E 2).restrict (fundamentalDomain (Gam E 2)))), w x = q x := by
        refine (ae_map_iff (measurable_mk (Gam E 2)).aemeasurable
          (measurableSet_eq_fun (Lp.stronglyMeasurable w).measurable hq.measurable)).2 ?_
        exact ae_restrict_of_ae hr
      rwa [map_restrict_eq_quotientMeasure (BW.mu1 E 2) (isFundamentalDomain_fundamentalDomain (Gam E 2) (BW.mu1 E 2))] at hm
    apply (Lp.memLp w).ae_eq (he.trans ?_)
    exact Eventually.of_forall fun x => by
      change q x = ψ (Quotient.out x)
      conv_lhs => rw [← Quotient.out_eq x]
      rfl
  obtain ⟨w, -, hw⟩ := hb.mem
  have hf : Continuous b.f.1 := ((BW.umgOps E 2).2 b.f (BW.cuspUmg E 2 b.f b.cusp).1).1
  exact (key hc hr).integrable_mul (key (hf.comp continuous_subtype_val) hw).star

private theorem zt_zero (K : Type) [Field K] [NumberField K] : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.zt K 0 = 1 := by
  have : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext Real.exp_zero
  rw [UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.zt, this, map_one]

private theorem ell_swap {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {S : Set (Pl E)} (b b' : BW.Blo S 2)
    {τ τ' ρ ρ' : Submodule ℂ (L2 (BW.mu1 E 2))} {m B m' B'} (hb : BloIn b τ m B) (hb' : BloIn b' τ' m' B')
    {f : G1 E (2 + 2) → ℂ} (hf : IsSec ρ ρ' f) (k : G1 E (2 + 2)) :
    (∀ m₂ : G1 E 2, Integrable (fun m₁ : RightCosetSpace (Gam E 2) => f (lv (Quotient.out m₁) m₂ 0 * k) *
      starRingEnd ℂ (b.f.1 ((Quotient.out m₁ : G1 E 2) : GlobalTheory.CuspRep.GA E 2))) (quotientMeasure (Gam E 2) (BW.mu1 E 2))) ∧
    ell b b' k f = ∫ m₂, (∫ m₁, f (lv (Quotient.out m₁) (Quotient.out m₂) 0 * k) *
      starRingEnd ℂ (b.f.1 ((Quotient.out m₁ : G1 E 2) : GlobalTheory.CuspRep.GA E 2)) ∂quotientMeasure (Gam E 2) (BW.mu1 E 2)) *
      starRingEnd ℂ (b'.f.1 ((Quotient.out m₂ : G1 E 2) : GlobalTheory.CuspRep.GA E 2)) ∂quotientMeasure (Gam E 2) (BW.mu1 E 2) := by
  haveI hfin : IsFiniteMeasure (quotientMeasure (Gam E 2) (BW.mu1 E 2)) := isFiniteMeasure_quotientMeasure (K := E) (n := 2) (BW.mu1 E 2)
  haveI hsf : SFinite (quotientMeasure (Gam E 2) (BW.mu1 E 2)) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfin)
  obtain ⟨d, φ, ψ, hφ, hψ, h⟩ := hf.levi k
  have e : ∀ m₁ m₂ : G1 E 2, f (lv m₁ m₂ 0 * k) = ∑ i, φ i m₁ * ψ i m₂ := fun m₁ m₂ =>
    h m₁ m₂ _ (by rw [Subgroup.coe_mul, blkLaws.1, neg_zero, zt_zero, mul_one, mul_one])
  have i₁ := fun i => int_pair b hb (hφ i).1 (hφ i).2.choose_spec.2
  have i₂ := fun i => int_pair b' hb' (hψ i).1 (hψ i).2.choose_spec.2
  refine ⟨fun m₂ => ?_, ?_⟩
  · simp only [e, Finset.sum_mul]
    refine integrable_finsetSum _ fun i _ => ?_
    simpa only [mul_right_comm] using (i₁ i).mul_const (ψ i m₂)
  · simp only [← integral_mul_const]
    refine integral_integral_swap ?_
    simp only [Function.uncurry_def, e, Finset.sum_mul]
    refine integrable_finsetSum _ fun i _ => ((i₁ i).mul_prod (i₂ i)).congr (Eventually.of_forall fun p => ?_)
    ring

private theorem rep_eq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} {μ : Measure (normOneGL (K := E) (n := n))}
    [μ.IsHaarMeasure] {v : L2 μ} {φ : GlobalTheory.CuspRep.Sm E n} (h : BW.Rep μ v φ) {Φ : G1 E n → ℂ} (hc : Continuous Φ)
    (hr : Reps μ v Φ) (g : G1 E n) : φ.1 (g : GlobalTheory.CuspRep.GA E n) = Φ g := by
  have h1 : Continuous fun g : G1 E n => φ.1 (g : GlobalTheory.CuspRep.GA E n) := ((BW.umgOps E n).2 φ h.umg).1.comp continuous_subtype_val
  refine congrFun ((h1.ae_eq_iff_eq μ hc).1 ?_) g
  filter_upwards [hr, MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam E n) μ) h.ae] with y a b
  rw [← a, b]
  obtain ⟨⟨γ, δ, hδ⟩, hγ⟩ := mk_eq_mk_iff.1 (Quotient.out_eq (mk (Gam E n) y))
  rw [← hγ]
  change _ = φ.1 ((γ : GlobalTheory.CuspRep.GA E n) * y)
  exact (hδ ▸ h.umg.left δ y).symm

set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.compLine :
    ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {μ : Measure (normOneGL (K := E) (n := (2 + 2)))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : _root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam 𝔢) (b b' : BW.Blo 𝔢.S 2), BloIn b 𝔵.τ₂ 𝔵.m₂ 𝔵.B₂ → BloIn b' 𝔵.τ₁ 𝔵.m₁ 𝔵.B₁ →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ k ∈ KG E (2 + 2), ∀ (u : ℝ → Eu 𝔵.d') (U : L (Eu 𝔵.d')) (φ : GlobalTheory.CuspRep.Sm E (2 + 2)), Continuous u → HasCompactSupport u →
        (∀ᵐ x : ℝ, U x = u x) → BW.Rep μ (𝔵.A'.J U) φ → ∀ t : Fin (dat2 b b').len → ℝ,
          (dat2 b b').comp (GlobalTheory.CuspRep.rt E (2 + 2) ((k : G1 E (2 + 2)) : GlobalTheory.CuspRep.GA E (2 + 2)) φ).1 t =
            c * Complex.exp ((t (0 : Fin 2) - t (1 : Fin 2) : ℝ) : ℂ) * ell b b' k (𝔵.A'.sec (u ((t (0 : Fin 2) - t (1 : Fin 2)) / 2))) := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 b b' hb hb'
  haveI : CompactSpace (KG E (2 + 2)) := isCompact_iff_compactSpace.1 (blkLaws.2.2.2.2.2.2.2.2.2.2.2 _).1
  have hv : 0 < volN E := (unf μ (BW.mu1 E 2) (Measure.haar : Measure (KG E (2 + 2)))).2
  refine ⟨volN E, by exact_mod_cast hv.ne', fun k hk u U φ hu hu' hU hφ t => ?_⟩
  obtain ⟨F, hF⟩ : ∃ F : G1 E (2 + 2) → ℂ, ∀ g, F g = Complex.exp (2 * (HH g : ℂ)) * 𝔵.A'.sec (u (HH g)) g := ⟨_, fun _ => rfl⟩
  obtain ⟨hP, hB, hS, hR⟩ := UpperTheory.pseudoEisenstein_section_pfun_inBand_slices_reps μ _ _ _ _ 𝔵.A' 𝔵.pair.irr₂ 𝔵.pair.irr₁ u F hu hu' hF
  have hth := rep_eq hφ (thBasic μ F hP.cont hP.rat hB).2.1 (hR U hU)
  obtain ⟨a, ha⟩ : ∃ a, a = t (0 : Fin 2) := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a, a = t (1 : Fin 2) := ⟨_, rfl⟩
  obtain ⟨hsec, hfix⟩ := (𝔵.A'.onto _).1 ⟨u ((a - a') / 2), rfl⟩
  have hray := (secFun _ _ _ _ 𝔵.pair.irr₂ 𝔵.pair.irr₁ _ hsec hfix).ray
  have hFk : ∀ y₁ y₂, F (lv y₁ y₂ ((a - a') / 2) * k) =
      Complex.exp ((a - a' : ℝ) : ℂ) * 𝔵.A'.sec (u ((a - a') / 2)) (lv y₁ y₂ 0 * k) := fun y₁ y₂ => by
    have h1 := hpSpec.1 0 y₁ y₂ ((a - a') / 2) k
    rw [nn, unipOne_zero, one_mul, (hpSpec.2.1 k hk).1, add_zero] at h1
    rw [hF, h1, ← hray ((a - a') / 2) (lv y₁ y₂ 0 * k), ← mul_assoc, blkLaws.2.1, one_mul, one_mul, add_zero]
    congr 2
    push_cast
    ring
  have hct : ∀ y₁ y₂ : G1 E 2, constantTerm 2 (GlobalTheory.CuspRep.rt E (2 + 2) ((k : G1 E (2 + 2)) : GlobalTheory.CuspRep.GA E (2 + 2)) φ).1
      (blk (BW.zt E 2 a * (y₁ : AdelicGLn.AdelicGL E 2)) (BW.zt E 2 a' * (y₂ : AdelicGLn.AdelicGL E 2))) =
      volN E * Complex.exp ((a - a' : ℝ) : ℂ) * 𝔵.A'.sec (u ((a - a') / 2)) (lv y₁ y₂ 0 * k) +
        ∫ X, F (w0 E * nn X * (lv y₁ y₂ ((a - a') / 2) * k)) ∂unipMeasure E (2 + 2) 2 := fun y₁ y₂ => by
    rw [mul_assoc, ← hFk, ← (thCt F hP hB _).2.2.2, constantTerm, pt_eq]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    have hz : ∀ g : AdelicGLn.AdelicGL E (2 + 2), g * BW.zt E (2 + 2) (a + a') = BW.zt E (2 + 2) (a + a') * g := fun g =>
      (centralSection_mul_comm _ g).symm
    change φ.1 (_ * (k : GlobalTheory.CuspRep.GA E (2 + 2))) = th F (unipOne (K := E) (n := 2 + 2) 2 X * (lv y₁ y₂ ((a - a') / 2) * k))
    rw [← hth, ← hφ.cen (a + a') ((unipOne (K := E) (n := 2 + 2) 2 X * (lv y₁ y₂ ((a - a') / 2) * k) : G1 E (2 + 2)) : GlobalTheory.CuspRep.GA E (2 + 2))]
    congr 1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_unipOne, ← mul_assoc (unipGL X), hz, mul_assoc, mul_assoc]
  have hbU := (BW.cuspUmg E 2 b.f b.cusp).1
  have hbc : Continuous fun g : G1 E 2 => b.f.1 (g : GlobalTheory.CuspRep.GA E 2) := ((BW.umgOps E 2).2 b.f hbU).1.comp continuous_subtype_val
  have hbi : ∀ γ ∈ Gam E 2, ∀ m : G1 E 2, b.f.1 ((γ * m : G1 E 2) : GlobalTheory.CuspRep.GA E 2) = b.f.1 (m : GlobalTheory.CuspRep.GA E 2) := by
    rintro γ ⟨δ, hδ⟩ m
    have h1 := hbU.left δ (m : GlobalTheory.CuspRep.GA E 2)
    rw [hδ] at h1
    exact h1
  obtain ⟨hI, hE⟩ := ell_swap b b' hb hb' hsec k
  rw [← ha, ← ha', hE, ← integral_const_mul]
  change BW.slice (r := 2) (s := 0) b'.f.1 (t (1 : Fin 2)) (BW.slice (r := 2) (s := 2 + 0) b.f.1 (t (0 : Fin 2)) _) 1 = _
  rw [← ha, ← ha', BW.slice]
  refine integral_congr_ae (Eventually.of_forall fun y₂ => ?_)
  obtain ⟨hL, hL0⟩ := UpperTheory.constantTerm_pairing_vanishes_of_orthogonal (BW.mu1 E 2) _ _ 𝔵.τ₂ F _ hP hB hS 𝔵.pair.orth hbc hbi hb.mem (Quotient.out y₂) ((a - a') / 2) k hk
  simp only
  rw [ct_nil, lev_eq, blk_nil, ← mul_assoc, BW.slice]
  congr 1
  rw [← integral_const_mul, ← add_zero (∫ _, _ * (_ * _) ∂_), ← hL0, ← integral_add ((hI _).const_mul _) hL]
  refine integral_congr_ae (Eventually.of_forall fun y₁ => ?_)
  simp only
  rw [lev_eq]
  erw [hct]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.TwistP
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
open scoped InnerProductSpace

section Abstract

variable {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

private theorem comm_of_ker (U : H ≃ₗᵢ[ℂ] H) (Q : H →L[ℂ] H) (hs : IsSelfAdjoint Q) (hi : Q ∘L Q = Q)
    (hk : ∀ h, Q (U h) = 0 ↔ Q h = 0) (h : H) : U (Q h) = Q (U h) := by
  have hQ : ∀ x, Q (Q x) = Q x := fun x => by
    have := congrArg (fun A : H →L[ℂ] H => A x) hi
    simpa using this
  have hsym : ∀ x y, ⟪Q x, y⟫_ℂ = ⟪x, Q y⟫_ℂ := fun x y => hs.isSymmetric x y
  have h1 : Q (U (h - Q h)) = 0 := (hk _).2 (by rw [map_sub, hQ, sub_self])
  rw [map_sub, map_sub, sub_eq_zero] at h1
  rw [h1]
  set w := U (Q h) - Q (U (Q h)) with hw
  have hw0 : Q w = 0 := by rw [hw, map_sub, hQ, sub_self]
  have hw1 : Q (U.symm w) = 0 := (hk _).1 (by simpa using hw0)
  have h2 : ⟪w, U (Q h)⟫_ℂ = 0 := by
    have := U.inner_map_map (U.symm w) (Q h)
    rw [U.apply_symm_apply] at this
    rw [this, ← hsym, hw1, inner_zero_left]
  have h3 : ⟪w, w⟫_ℂ = 0 := by
    conv_lhs => rw [hw, inner_sub_right, ← hw]
    rw [h2, ← hsym, hw0, inner_zero_left, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h3)

private theorem lift_ex (s : V ≃ₗᵢ[ℂ] W) (u : L V) : ∃ v : L W, ∀ᵐ x : ℝ, v x = s (u x) :=
  ⟨(s.toContinuousLinearEquiv : V →L[ℂ] W).compLp u, (s.toContinuousLinearEquiv : V →L[ℂ] W).coeFn_compLp u⟩

private theorem lift_ex' (s : V ≃ₗᵢ[ℂ] W) (v : L W) : ∃ u : L V, ∀ᵐ x : ℝ, v x = s (u x) := by
  obtain ⟨u, hu⟩ := lift_ex s.symm v
  exact ⟨u, hu.mono fun x hx => by rw [hx, s.apply_symm_apply]⟩

private theorem abs_main (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (U : H ≃ₗᵢ[ℂ] H) (s : V ≃ₗᵢ[ℂ] W) (t : W ≃ₗᵢ[ℂ] V)
    (hs : ∀ (u : L V) (v : L W), (∀ᵐ x : ℝ, v x = s (u x)) → U (J u) = J' v)
    (ht : ∀ (v : L W) (u : L V), (∀ᵐ x : ℝ, u x = t (v x)) → U (J' v) = J u) :
    (∀ P : H →L[ℂ] H, IsOrthogonalProjectionTwoLines J J' P → ∀ h, U (P h) = P (U h)) ∧
    ∀ (T : ℝ) (Λ : H →L[ℂ] H), (IsSelfAdjoint Λ ∧ Λ ∘L Λ = Λ ∧ ∀ h : H, Λ h = 0 ↔
      ∃ (u : L V) (v : L W), (∀ᵐ x : ℝ, x ≤ T → u x = 0) ∧ (∀ᵐ x : ℝ, x ≤ T → v x = 0) ∧ h = J u + J' v) →
      ∀ h, U (Λ h) = Λ (U h) := by
  refine ⟨fun P ⟨h1, h2, h3⟩ => comm_of_ker U P h1 h2 fun h => ?_,
    fun T Λ ⟨h1, h2, h3⟩ => comm_of_ker U Λ h1 h2 fun h => ?_⟩
  · rw [h3, h3]
    constructor
    · rintro ⟨a, b⟩
      refine ⟨fun u => ?_, fun v => ?_⟩
      · obtain ⟨v, hv⟩ := lift_ex s u
        rw [← U.inner_map_map, hs u v hv, b]
      · obtain ⟨u, hu⟩ := lift_ex t v
        rw [← U.inner_map_map, ht v u hu, a]
    · rintro ⟨a, b⟩
      refine ⟨fun u => ?_, fun v => ?_⟩
      · obtain ⟨v, hv⟩ := lift_ex' t u
        rw [← ht v u hv, U.inner_map_map, b]
      · obtain ⟨u, hu⟩ := lift_ex' s v
        rw [← hs u v hu, U.inner_map_map, a]
  · rw [h3, h3]
    constructor
    · rintro ⟨u, v, hu, hv, e⟩
      obtain ⟨v', hv'⟩ := lift_ex' t u
      obtain ⟨u', hu'⟩ := lift_ex' s v
      refine ⟨u', v', ?_, ?_, ?_⟩
      · filter_upwards [hv, hu'] with x a b hx
        exact s.injective (by rw [← b, a hx, map_zero])
      · filter_upwards [hu, hv'] with x a b hx
        exact t.injective (by rw [← b, a hx, map_zero])
      · apply U.injective
        rw [e, map_add (f := _), hs u' v hu', ht v' u hv', add_comm]
    · rintro ⟨u, v, hu, hv, e⟩
      obtain ⟨v', hv'⟩ := lift_ex s u
      obtain ⟨u', hu'⟩ := lift_ex t v
      refine ⟨u', v', ?_, ?_, ?_⟩
      · filter_upwards [hv, hu'] with x a b hx
        rw [b, a hx, map_zero]
      · filter_upwards [hu, hv'] with x a b hx
        rw [b, a hx, map_zero]
      · rw [e, map_add (f := _), hs u v' hv', ht v u' hu', add_comm]

end Abstract

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.twistP :
    ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
      {μ : Measure (normOneGL (K := E) (n := (2 + 2)))} [μ.IsHaarMeasure] {θ : Twist μ}
      {𝔢 : Side θ 2} (𝔵 : _root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam 𝔢),
      θ.U ∘L 𝔵.P = 𝔵.P ∘L θ.U ∧
      ∀ (T : ℝ) (Λ : L2 μ →L[ℂ] L2 μ), IsTrunc 𝔵.A.J 𝔵.A'.J T Λ → θ.U ∘L Λ = Λ ∘L θ.U := by
  intro E _ _ _ μ _ θ 𝔢 𝔵
  obtain ⟨U, hU, -, -⟩ := UpperTheory.ConvolutionTheory.C.twistUnitary E (2 + 2) μ θ
  have hU' : ∀ h, θ.U h = U h := fun h => by rw [← hU]; rfl
  obtain ⟨t, -, ht⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.convU E μ (BW.mu1 E 2) 𝔵.τ₂ 𝔵.τ₁ ⟨𝔵.pair.irr₂, 𝔵.pair.irr₁, 𝔵.pair.orth.symm⟩
    𝔵.D 𝔵.d' 𝔵.d 𝔵.A' 𝔵.A 𝔵.σ θ 𝔵.θ₂ 𝔵.gal 𝔵.gal₂ 𝔵.stable 𝔵.swap₂ 𝔵.swap₁
  obtain ⟨a, b⟩ := abs_main 𝔵.A.J 𝔵.A'.J U 𝔵.s t (fun u v h => by rw [← hU']; exact 𝔵.s_op u v h)
    (fun v u h => by rw [← hU']; exact ht v u h)
  refine ⟨ContinuousLinearMap.ext fun h => ?_, fun T Λ hΛ => ContinuousLinearMap.ext fun h => ?_⟩
  · simp only [ContinuousLinearMap.comp_apply, hU']
    exact a _ 𝔵.isP h
  · simp only [ContinuousLinearMap.comp_apply, hU']
    exact b T Λ hΛ h
end

