module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0365
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConjugationDifferences.ExpDivExpEq
public import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothModelRestrictionBijective

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetIteratedPhiEquiv
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZMir

theorem iterPhi_twJacquet_equiv (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (τ : MRep k (n + j)) :
    Nonempty (TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1 ≃ₗ[ℂ]
      TwJacquet τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n)) := by
  induction j with
  | zero =>
    exact ⟨Submodule.quotEquivOfEq _ _ (_root_.GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM k ψ n τ.V τ.ρ)⟩
  | succ j ih =>
    obtain ⟨e₁⟩ := ih (MRep.phiM k ψ τ)
    obtain ⟨e₂⟩ := _root_.GlobalTheory.CompanionTheory.BZMirStep.phiMinus_twJacquet_equiv k ψ (n + j) n (Nat.le_add_right n j) τ.V τ.ρ
    exact ⟨e₁.trans e₂⟩

end GlobalTheory.CompanionTheory.BZMir
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelConjugation
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirabolic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem twKer_le_comap_levi (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k n) V) (a : Fin n → k) (m : GL (Fin n) k) :
    twKer τ (MirUin k n) (thetaA k ψ (vecMul a (m : Matrix (Fin n) (Fin n) k))) ≤
      (twKer τ (MirUin k n) (thetaA k ψ a)).comap (τ (levi k n m)) := by
  unfold GlobalTheory.PRep.twKer
  rw [Submodule.span_le]
  intro x hx
  have key : ∀ (u : GlobalTheory.BZMir.MirUin k n) (w : V),
      τ (GlobalTheory.BZMir.levi k n m) (τ u w) =
        τ (GlobalTheory.BZMir.levi k n m * u * (GlobalTheory.BZMir.levi k n m)⁻¹) (τ (GlobalTheory.BZMir.levi k n m) w) := by
    intro u w
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  first
    | (obtain ⟨u, w, rfl⟩ := hx
       obtain ⟨hm, hc⟩ := GlobalTheory.CompanionTheory.BZMirabolic.thetaConj k ψ n a m u
       simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, Units.smul_def, map_smul]
       rw [key, hc]
       exact Submodule.subset_span ⟨⟨_, hm⟩, _, rfl⟩)
    | (obtain ⟨⟨u, w⟩, rfl⟩ := hx
       obtain ⟨hm, hc⟩ := GlobalTheory.CompanionTheory.BZMirabolic.thetaConj k ψ n a m u
       simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, Units.smul_def, map_smul]
       rw [key, hc]
       exact Submodule.subset_span ⟨(⟨_, hm⟩, _), rfl⟩)

theorem twKerConj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : TwKerConj k := by
  unfold GlobalTheory.BZMir.Fun.TwKerConj
  intro ψ n V _ _ τ a m v
  constructor
  · intro hv
    exact GlobalTheory.CompanionTheory.BZMirabolic.twKer_le_comap_levi ψ τ a m hv
  · intro hv
    have ha : vecMul (vecMul a (m : Matrix (Fin n) (Fin n) k))
        ((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = a := by
      rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
    rw [← ha] at hv
    have h := GlobalTheory.CompanionTheory.BZMirabolic.twKer_le_comap_levi ψ τ _ m⁻¹ hv
    rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel,
      map_one, map_one, Module.End.one_apply] at h
    exact h

end GlobalTheory.CompanionTheory.BZMirabolic

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundOfArchimedeanLipschitz
section
noncomputable section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open scoped NumberField.AdeleRing Pointwise
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
  GroundTheory.Automorphic.CuspidalSpectrum

namespace GlobalTheory.CompanionTheory.Conc


open PositivityTheory.Rg.Rs.diffstep in
theorem diffStepU (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type)
    (f₀ f₁ : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (r : ℕ) (hr : 0 < r) (hrn : r < n) (hN : UFam f₁)
    (hlip' : ∀ R : ℝ, ∃ (Q₀ : Set (AdelicGLn.AdelicGL K n)) (C : ℝ), IsCompact Q₀ ∧ 0 ≤ C ∧
      ∀ i g (Y : ArchMatrix K n) (M : ℝ), Y * Y = 0 → ‖Y‖ ≤ R →
        (∀ q ∈ Q₀, ‖f₀ i (g * q)‖ ≤ M) → ‖f₁ i (g * CuspidalSpectrum.archExp Y) - f₁ i g‖ ≤ C * ‖Y‖ * M)
    (hB : UBnd f₀ m) :
    UBnd (fun i g => f₁ i g - An.ctn r (f₁ i) g) (Function.update m r (m r - 1)) := by
  intro ω hω hωB t₀ Q hQ
  obtain ⟨U, hU, hlev⟩ := hN.level
  obtain ⟨M, hM, hMc⟩ := exists_natCast_conj_mem U hU hω hQ r
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_conjArch_le hω hωB hQ (Real.exp_pos (-t₀)) hr hrn
    (isCompact_scaledInfSet (K := K) M)
  obtain ⟨Q₀, C₂, hQ₀, hC₂, hlip⟩ := hlip' (C₁ * Real.exp t₀)
  obtain ⟨C₃, hC₃⟩ := hB ω hω hωB t₀ (Q * Q₀) (hQ.mul hQ₀)
  set C₃' := max C₃ 0 with hC₃'
  have hC₃'0 : 0 ≤ C₃' := le_max_right _ _
  refine ⟨C₂ * C₁ * C₃', ?_⟩
  intro i b hb x hx q hq
  set g := b * An.tor K x * q with hg
  set S := ∑ i ∈ Finset.range n, m i * An.sr x i with hS
  have hsieg := siegel_of_sr hx
  have hpt : ∀ X ∈ scaledUnipFD K n r M, ‖f₁ i g - f₁ i (unipGL X * g)‖ ≤
      C₂ * (C₁ * Real.exp (-An.sr x r)) * (C₃' * Real.exp S) := by
    intro X hX
    set Y := conjArch K n g (truncInf X) with hY
    have hYn : ‖Y‖ ≤ C₁ * Real.exp (-An.sr x r) := by
      have h := hC₁ b hb (fun i => Real.exp (x i)) (fun i => Real.exp_pos _) hsieg q hq (truncInf X)
        (fun p => rfl) (fun p => infinite_mem_scaledInfSet hM hX p)
      rw [exp_div_exp_eq hr hrn x] at h
      exact h
    have hYR : ‖Y‖ ≤ C₁ * Real.exp t₀ :=
      hYn.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [hx r])) hC₁0)
    obtain ⟨u, hu⟩ := hMc b hb (fun i => Real.exp (x i)) (fun i => Real.exp_pos _) q hq (truncFin X)
      (fun p => rfl) (fun p => exists_finite_eq_natCast_mul hM hX p)
    have hu' : g⁻¹ * unipGL (truncFin X) * g =
        finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) := hu
    have hdecomp : unipGL X * g = g * archExp Y * (g⁻¹ * unipGL (truncFin X) * g) := by
      rw [hY, ← conj_unipGL_eq_archExp g (truncInf X) (fun p => rfl)]
      conv_lhs => rw [← truncInf_add_truncFin X, unipGL_add]
      group
    have heq : f₁ i (unipGL X * g) = f₁ i (g * archExp Y) := by rw [hdecomp, hu', hlev]
    have hMg : ∀ q' ∈ Q₀, ‖f₀ i (g * q')‖ ≤ C₃' * Real.exp S := by
      intro q' hq'
      have h := hC₃ i b hb x hx (q * q') (Set.mul_mem_mul hq hq')
      rw [show g * q' = b * An.tor K x * (q * q') by rw [hg, mul_assoc]]
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have hl := hlip i g Y (C₃' * Real.exp S) (conjArch_mul_conjArch _ _ _) hYR hMg
    rw [norm_sub_rev, heq]
    calc _ ≤ C₂ * ‖Y‖ * (C₃' * Real.exp S) := hl
      _ ≤ _ := by gcongr
  have hD := isAddFundamentalDomain_scaledUnipFD (K := K) (n := n) (r := r) hM
  have hD1 := unipMeasure_scaledUnipFD (K := K) (n := n) (r := r) hM
  obtain ⟨Cc, hCc, hDC⟩ := exists_isCompact_superset_scaledUnipFD (K := K) (n := n) r hM
  have hint : IntegrableOn (fun X => f₁ i (unipGL X * g)) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    (((hN.cont i).comp (continuous_unipGL.mul continuous_const)).continuousOn.integrableOn_compact
      hCc).mono_set hDC
  have hfin : unipMeasure K n r (scaledUnipFD K n r M) < ⊤ := by
    rw [hD1]
    exact ENNReal.one_lt_top
  have hct : An.ctn r (f₁ i) g = ∫ X in scaledUnipFD K n r M, f₁ i (unipGL X * g) ∂unipMeasure K n r := by
    rw [An.ctn, measureReal_def, unipMeasure_unipFundamentalDomain, ENNReal.toReal_one,
      Complex.ofReal_one, inv_one, one_mul]
    exact constantTerm_eq_setIntegral (hN.left i) hD g
  have hdiff : f₁ i g - An.ctn r (f₁ i) g =
      ∫ X in scaledUnipFD K n r M, (f₁ i g - f₁ i (unipGL X * g)) ∂unipMeasure K n r := by
    have hconst : IntegrableOn (fun _ => f₁ i g) (scaledUnipFD K n r M) (unipMeasure K n r) :=
      integrableOn_const hfin.ne enorm_ne_top
    rw [hct, integral_sub hconst hint, setIntegral_const, measureReal_def, hD1,
      ENNReal.toReal_one, one_smul]
  change ‖f₁ i g - An.ctn r (f₁ i) g‖ ≤ _
  rw [hdiff]
  refine (norm_setIntegral_le_of_norm_le_const hfin hpt).trans (le_of_eq ?_)
  rw [measureReal_def, hD1, ENNReal.toReal_one, mul_one, sum_update_sub hrn, ← hS, sub_eq_add_neg,
    Real.exp_add]
  ring

end GlobalTheory.CompanionTheory.Conc

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundSmoothing
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

open scoped Pointwise

namespace GlobalTheory.CompanionTheory.Conc

theorem norm_integral_ker_le {K : Type} [Field K] [NumberField K] {n : ℕ}
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] {β : archGroup K n → ℝ} (hk : Ker ν β)
    (g : archGroup K n → ℂ) {M : ℝ} (hg : ∀ y ∈ tsupport β, ‖g y‖ ≤ M) :
    ‖∫ y, (β y : ℂ) * g y ∂ν‖ ≤ M := by
  have hint : Integrable (fun y => β y * M) ν :=
    (hk.cont.integrable_of_hasCompactSupport hk.cpt).mul_const M
  have hpt : ∀ y, ‖(β y : ℂ) * g y‖ ≤ β y * M := by
    intro y
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hk.nonneg y)]
    by_cases hy : y ∈ tsupport β
    · exact mul_le_mul_of_nonneg_left (hg y hy) (hk.nonneg y)
    · rw [image_eq_zero_of_notMem_tsupport hy]
      simp
  have h := norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
  rwa [integral_mul_const, hk.mass, one_mul] at h

theorem uBnd_sm (K : Type) [Field K] [NumberField K] (n : ℕ)
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (ι : Type)
    (f : ι → AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (hk : Ker ν β) (_hf : ∀ i, Continuous (f i))
    (hb : UBnd f m) : UBnd (fun i => sm ν β (f i)) m := by
  intro ω hω hsub t₀ Q hQ
  have hQ' : IsCompact (Q * infEmb K n '' tsupport β) :=
    hQ.mul (hk.cpt.isCompact.image continuous_infEmb)
  obtain ⟨C, hC⟩ := hb ω hω hsub t₀ _ hQ'
  refine ⟨max C 0, fun i b hbω x hx q hq => ?_⟩
  refine norm_integral_ker_le ν hk _ ?_
  intro y hy
  rw [mul_assoc (b * _) q]
  refine (hC i b hbω x hx _ (Set.mul_mem_mul hq (Set.mem_image_of_mem _ hy))).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

end GlobalTheory.CompanionTheory.Conc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformFamilySmoothing
section
noncomputable section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc

theorem continuous_sm_uFam {K : Type} [Field K] [NumberField K] {n : ℕ}
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] {β : archGroup K n → ℝ} (hβ : Ker ν β) {f : AdelicGLn.AdelicGL K n → ℂ}
    (hf : Continuous f) : Continuous (sm ν β f) := by
  have hF : Continuous (Function.uncurry fun (x : AdelicGLn.AdelicGL K n) (y : archGroup K n) =>
      (β y : ℂ) * f (x * infEmb K n y)) := by
    refine (Complex.continuous_ofReal.comp (hβ.cont.comp continuous_snd)).mul (hf.comp ?_)
    exact continuous_fst.mul (continuous_infEmb.comp continuous_snd)
  set_option synthInstance.maxHeartbeats 1000000 in
  have h := continuous_parametric_integral_of_continuous (μ := ν) hF hβ.cpt.isCompact
  refine h.congr fun x => ?_
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
  have : β y = 0 := image_eq_zero_of_notMem_tsupport hy
  simp [this]

theorem uFam_sm : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ)
    (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ), Ker ν β → UFam f → UFam (fun i => sm ν β (f i)) := by
  intro K _ _ n _ _ ν _ β ι f hβ hf
  refine ⟨fun i => continuous_sm_uFam ν hβ (hf.cont i), fun i γ x => ?_, ?_⟩
  · simp only [sm, mul_assoc]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [hf.left i γ (x * infEmb K n y)]
  · obtain ⟨U, hU, hlev⟩ := hf.level
    refine ⟨U, hU, fun i g u => ?_⟩
    simp only [sm]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [mul_assoc g, ← infEmb_mul_finEmb_comm, ← mul_assoc, hlev i (g * infEmb K n y) u]

end GlobalTheory.CompanionTheory.Conc

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEuclideanModel
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

noncomputable section

namespace GlobalTheory.CompanionTheory.RealCount

variable {n : ℕ}

def dualCoord (E : KMod n) :
    (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) where
  toFun ξ := WithLp.toLp 2 fun i => ξ (stdOrthonormalBasis ℂ E.V i)
  map_add' x y := by
    ext i
    simp
  map_smul' c x := by
    ext i
    simp
  invFun v := ∑ i, v i • innerSL ℂ (stdOrthonormalBasis ℂ E.V i)
  left_inv ξ := by
    ext x
    have hx := (stdOrthonormalBasis ℂ E.V).sum_repr' x
    conv_rhs => rw [← hx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, mul_comm]
  right_inv v := by
    ext j
    have ho := (stdOrthonormalBasis ℂ E.V).orthonormal
    simp [orthonormal_iff_ite.mp ho]

theorem norm_dualCoord (E : KMod n) (ξ : E.V →L[ℂ] ℂ) : ‖dualCoord E ξ‖ = ‖ξ‖ := by
  set r := (InnerProductSpace.toDual ℂ E.V).symm ξ with hr
  have h1 : ‖r‖ = ‖ξ‖ := (InnerProductSpace.toDual ℂ E.V).symm.norm_map ξ
  have h2 : ‖(stdOrthonormalBasis ℂ E.V).repr r‖ = ‖r‖ :=
    (stdOrthonormalBasis ℂ E.V).repr.norm_map r
  rw [← h1, ← h2, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h3 : (dualCoord E ξ) i = ξ (stdOrthonormalBasis ℂ E.V i) := rfl
  rw [h3, OrthonormalBasis.repr_apply_apply, ← InnerProductSpace.toDual_symm_apply (𝕜 := ℂ), ← hr,
    norm_inner_symm]

def dualAct (E : KMod n) : (E.V →L[ℂ] E.V) →ₗ[ℂ]
    (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ]
      EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) where
  toFun T := LinearMap.toContinuousLinearMap
    ((dualCoord E).toLinearMap ∘ₗ
      (((ContinuousLinearMap.compL ℂ E.V E.V ℂ).flip T : (E.V →L[ℂ] ℂ) →L[ℂ] (E.V →L[ℂ] ℂ)) :
        (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) ∘ₗ (dualCoord E).symm.toLinearMap)
  map_add' S T := by
    ext v : 1
    simp
  map_smul' c T := by
    ext v : 1
    simp

theorem dualAct_apply (E : KMod n) (T : E.V →L[ℂ] E.V) (v) :
    dualAct E T v = dualCoord E ((dualCoord E).symm v ∘L T) := by
  simp [dualAct]

theorem continuous_unitary_inv :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => k⁻¹ := by
  refine Continuous.subtype_mk (p := (· ∈ Matrix.unitaryGroup (Fin n) ℂ)) ?_ _
  simpa using (continuous_subtype_val.star :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => star k.1)

theorem dualRep_exists {n : ℕ} (E : KMod n) :
    ∃ (e : (E.V →L[ℂ] ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)))
      (ρ' : Matrix.unitaryGroup (Fin n) ℂ →*
        (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ]
          EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)))),
      Continuous ρ' ∧ (∀ k v, ‖ρ' k v‖ = ‖v‖) ∧ ∀ k ξ, e (ξ ∘L E.ρ k⁻¹) = ρ' k (e ξ) := by
  have hact : ∀ k ξ, dualAct E (E.ρ k⁻¹) (dualCoord E ξ) = dualCoord E (ξ ∘L E.ρ k⁻¹) := by
    intro k ξ
    rw [dualAct_apply, LinearEquiv.symm_apply_apply]
  let ρ' : Matrix.unitaryGroup (Fin n) ℂ →*
      (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ]
        EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) :=
    { toFun := fun k => dualAct E (E.ρ k⁻¹)
      map_one' := by
        ext1 v
        rw [dualAct_apply, inv_one, map_one]
        change dualCoord E ((dualCoord E).symm v ∘L ContinuousLinearMap.id ℂ E.V) = v
        rw [ContinuousLinearMap.comp_id, LinearEquiv.apply_symm_apply]
      map_mul' := by
        intro k l
        ext1 v
        obtain ⟨ξ, rfl⟩ := (dualCoord E).surjective v
        rw [ContinuousLinearMap.mul_apply, hact l, hact k, hact (k * l), _root_.mul_inv_rev, map_mul]
        rfl }
  refine ⟨dualCoord E, ρ', ?_, ?_, fun k ξ => (hact k ξ).symm⟩
  · have h1 : Continuous (dualAct E) := LinearMap.continuous_of_finiteDimensional _
    exact h1.comp (E.cont.comp continuous_unitary_inv)
  · intro k v
    obtain ⟨ξ, rfl⟩ := (dualCoord E).surjective v
    have hle : ∀ (l : Matrix.unitaryGroup (Fin n) ℂ) (η : E.V →L[ℂ] ℂ), ‖η ∘L E.ρ l‖ ≤ ‖η‖ := by
      intro l η
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
      simpa [E.iso] using η.le_opNorm (E.ρ l x)
    have hback : (ξ ∘L E.ρ k⁻¹) ∘L E.ρ k = ξ := by
      ext x
      have : E.ρ k⁻¹ (E.ρ k x) = x := by
        have h := congrArg (fun T : E.V →L[ℂ] E.V => T x) (E.ρ.map_mul k⁻¹ k)
        simpa using h.symm
      simp [this]
    have h2 : ‖ξ ∘L E.ρ k⁻¹‖ = ‖ξ‖ := by
      refine le_antisymm (hle _ _) ?_
      calc ‖ξ‖ = ‖(ξ ∘L E.ρ k⁻¹) ∘L E.ρ k‖ := by rw [hback]
        _ ≤ _ := hle _ _
    change ‖dualAct E (E.ρ k⁻¹) (dualCoord E ξ)‖ = _
    rw [hact, norm_dualCoord, norm_dualCoord, h2]

end GlobalTheory.CompanionTheory.RealCount
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittSiteRestrictBijective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution

noncomputable section

namespace GlobalTheory.CompanionTheory.FlatZar

section Main
variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}

def resG (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ)
    (P Q : ObjectProperty (Thick (Wc.L l (B.schFn q) ρ m))) (h : Q ≤ P) :
    CH.Mor (P.ι ⋙ Wc.OM l (B.schFn q) ρ m) (Q.ι ⋙ Wc.OM l (B.schFn q) ρ m) (RingHom.id (WittVector l k)) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

set_option maxHeartbeats 1600000 in
theorem resG_bij (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens) (hU : sSup 𝒱 = ⊤)
    (P : ObjectProperty (Thick (Wc.L l (B.schFn q) ρ m))) (hP : P = stF q ρ m {⊤}) (h : stF q ρ m 𝒱 ≤ P) (j : ℕ) :
    Function.Bijective ((resG q ρ m P (stF q ρ m 𝒱) h).pull j) := by
  subst hP
  have z := (zar (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT
    (Or.inr ⟨(Fact.out : l.Prime).ne_zero, Or.inr rfl⟩) 𝒱 {⊤} h
    (fun W _ => by rw [hU]; exact le_top) j).2.2
  have c1 := GlobalTheory.CompanionTheory.FlatRes.scM_bij q ρ m (stF q ρ m {⊤}) j
  have c2 := GlobalTheory.CompanionTheory.FlatRes.scM_bij q ρ m (stF q ρ m 𝒱) j
  refine (Function.Bijective.of_comp_iff' c2 _).1 ?_
  have e : ⇑((GlobalTheory.CompanionTheory.FlatRes.scM q ρ m (stF q ρ m 𝒱)).pull j) ∘ ⇑((resG q ρ m _ (stF q ρ m 𝒱) h).pull j) =
      ⇑((incl h).o.pull j) ∘ ⇑((GlobalTheory.CompanionTheory.FlatRes.scM q ρ m (stF q ρ m {⊤})).pull j) := by
    funext x
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
  rw [e]
  exact z.comp c1

theorem resV_bij : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (m : ℕ) (𝒱 : Set X.Opens), sSup 𝒱 = ⊤ → ∀ j, Function.Bijective ((resV q ρ m 𝒱).pull j) := by
  intro l _ k _ _ _ O _ X q ρ m 𝒱 hU j
  exact resG_bij q ρ m 𝒱 hU (fl l (B.schFn q) ρ m)
    (GlobalTheory.CompanionTheory.FlatRes.st_top_eq (γ := Wc.pd l k m) (p := l) (q := q) (κ := (Wc.res l k m).comp ρ) FlatT).symm
    (fun _ h => h.1) j

end Main

end GlobalTheory.CompanionTheory.FlatZar

end
end

