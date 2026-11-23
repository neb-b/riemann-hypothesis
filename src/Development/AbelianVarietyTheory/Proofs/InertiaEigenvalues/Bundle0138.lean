module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0121
public import GroundTheory.LocalFields.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0110

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearDescentPartialFourierEqFourierDescent
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc.Swap

theorem norm_eq_of_sub_lt {K : Type} [NormedField K] [IsUltrametricDist K] {x y : K}
    (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  have h1 : ‖x‖ ≤ max ‖x - y‖ ‖y‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (x - y) y
  have h2 : ‖y‖ ≤ max ‖y - x‖ ‖x‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (y - x) x
  rw [norm_sub_rev] at h2
  apply le_antisymm
  · exact h1.trans (max_le h.le le_rfl)
  · rcases le_max_iff.mp h2 with h3 | h3
    · exact absurd h3 (not_le.mpr h)
    · exact h3

theorem eta_eventually {F : Type} [NormedField F] [IsUltrametricDist F] {x : F} (hx : x ≠ 0) :
    ∀ᶠ y in 𝓝 x, eta x = eta y := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  filter_upwards [Metric.ball_mem_nhds x hpos] with y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have := norm_eq_of_sub_lt hy
  unfold eta
  rw [this]

theorem continuous_eta_det {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] (r : ℕ) :
    Continuous (fun g : GL (Fin r) F => eta ((g : Matrix (Fin r) (Fin r) F).det)) := by
  rw [continuous_iff_continuousAt]
  intro g
  have hd : ((g : Matrix (Fin r) (Fin r) F).det) ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  have hc : Continuous (fun g : GL (Fin r) F => (g : Matrix (Fin r) (Fin r) F).det) :=
    Units.continuous_val.matrix_det
  exact ContinuousAt.comp (f := fun g : GL (Fin r) F => (g : Matrix (Fin r) (Fin r) F).det)
    (continuousAt_const.congr (eta_eventually hd)) hc.continuousAt

theorem continuous_psi {F : Type} [NormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    Continuous ψ := by
  rw [continuous_iff_continuousAt]
  intro x
  refine ContinuousAt.congr (f := fun _ => ψ x) continuousAt_const ?_
  filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have : y = x + (y - x) := by ring
  rw [this, AddChar.map_add_eq_mul, hψ.1 _ hy.le, mul_one]

theorem continuous_act {F : Type} [NontriviallyNormedField F] (r : ℕ) :
    Continuous (fun z : GL (Fin r) F × Gl r F => act z.1 z.2) := by
  unfold act
  have h1 : Continuous (fun z : GL (Fin r) F × Gl r F => ((z.1 : Matrix (Fin r) (Fin r) F))) :=
    Units.continuous_val.comp continuous_fst
  have h2 : Continuous (fun z : GL (Fin r) F × Gl r F =>
      (((z.1⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))) :=
    Units.continuous_coe_inv.comp continuous_fst
  exact ((h1.matrix_mul continuous_snd.fst).matrix_mul h2).prodMk
    ((h1.matrix_mulVec continuous_snd.snd.fst).prodMk
      ((continuous_snd.snd.snd.fst.matrix_vecMul h2).prodMk continuous_snd.snd.snd.snd))

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] (A : Et F E)

theorem K_inst {r : ℕ} {τ : A.K} {p : Fin r → F} (hG : A.IsGen τ p) [SecondCountableTopology F] :
    T2Space A.K ∧ SecondCountableTopology A.K := by
  have hc : Continuous (bas A hG).equivFun :=
    IsModuleTopology.continuous_of_linearMap (bas A hG).equivFun.toLinearMap
  have hc' : Continuous (bas A hG).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (bas A hG).equivFun.symm.toLinearMap
  let e : A.K ≃ₜ (Fin r → F) :=
    { toEquiv := (bas A hG).equivFun.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  exact ⟨e.isEmbedding.t2Space, e.isEmbedding.secondCountableTopology⟩

theorem continuous_pt {r : ℕ} {τ : A.K} {p : Fin r → F} (hG : A.IsGen τ p) (lam : F) :
    Continuous (fun q : A.K × A.K => pt A hG lam q.1 q.2) := by
  unfold pt
  have he : Continuous (bas A hG).equivFun :=
    IsModuleTopology.continuous_of_linearMap (bas A hG).equivFun.toLinearMap
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.prodMk ((he.comp continuous_fst).prodMk
    ((continuous_pi fun i => htr.comp (continuous_const.mul continuous_snd)).prodMk continuous_const))

end GlobalTheory.JR.LinDesc.Swap

namespace GlobalTheory.JR.LinDesc.Swap

theorem swap_triple {X Y : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [T2Space Y] [SecondCountableTopology Y]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (ν : Measure Y) [IsFiniteMeasureOnCompacts ν]
    [SigmaFinite ν] (k : X → Y → Y → ℂ) (hk : Continuous (fun z : (Y × Y) × X => k z.2 z.1.1 z.1.2))
    (S : Set X) (B C : Set Y) (hS : IsCompact S) (hB : IsCompact B) (hC : IsCompact C)
    (hsupp : ∀ g b c, k g b c ≠ 0 → g ∈ S ∧ b ∈ B ∧ c ∈ C) :
    ∫ g, ∫ b, ∫ c, k g b c ∂ν ∂ν ∂μ = ∫ b, ∫ c, ∫ g, k g b c ∂μ ∂ν ∂ν := by
  haveI : IsFiniteMeasure (μ.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hS.measure_lt_top⟩
  set Φ : (Y × Y) × X → ℂ := fun z => k z.2 z.1.1 z.1.2 with hΦdef
  have hΦc : HasCompactSupport Φ := by
    refine HasCompactSupport.intro ((hB.prod hC).prod hS) fun z hz => ?_
    by_contra h
    obtain ⟨h1, h2, h3⟩ := hsupp _ _ _ h
    exact hz ⟨⟨h2, h3⟩, h1⟩
  have hΦ : Integrable Φ ((ν.prod ν).prod (μ.restrict S)) := hk.integrable_of_hasCompactSupport hΦc
  have hL : ∫ g, ∫ b, ∫ c, k g b c ∂ν ∂ν ∂μ = ∫ g in S, ∫ b, ∫ c, k g b c ∂ν ∂ν ∂μ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
    have : ∀ b c, k g b c = 0 := fun b c => by
      by_contra h; exact hg (hsupp _ _ _ h).1
    simp [this]
  have hR : ∀ b c, ∫ g, k g b c ∂μ = ∫ g in S, k g b c ∂μ := fun b c => by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
    by_contra h; exact hg (hsupp _ _ _ h).1
  simp_rw [hR]
  rw [hL]
  calc ∫ g in S, ∫ b, ∫ c, k g b c ∂ν ∂ν ∂μ
      = ∫ g, ∫ q, Φ (q, g) ∂(ν.prod ν) ∂(μ.restrict S) := by
        refine integral_congr_ae ?_
        filter_upwards [hΦ.prod_left_ae] with g hg
        exact (integral_prod (fun q => Φ (q, g)) hg).symm
    _ = ∫ q, ∫ g, Φ (q, g) ∂(μ.restrict S) ∂(ν.prod ν) :=
        (integral_integral_swap (f := fun q g => Φ (q, g)) hΦ).symm
    _ = ∫ b, ∫ c, ∫ g in S, k g b c ∂μ ∂ν ∂ν := integral_prod _ hΦ.integral_prod_left

end GlobalTheory.JR.LinDesc.Swap

namespace GlobalTheory.JR.LinDesc.Swap

theorem desc_fourG_eq_fourK_desc : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ μK : Measure A.K, SelfDual μK (A.kerK ψ) → ∀ (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → (∀ (g : GL (Fin r) F) (b c : A.K), fourG M ψ f' (act g (LinDesc.pt A hG lam b c)) = A.fourK μK ψ (fun x => f' (act g (LinDesc.pt A hG lam x.1 x.2))) (b, c)) → ∀ x : A.K × A.K, LinDesc.desc A M hG lam α (fourG M ψ f') x = A.fourK μK ψ (LinDesc.desc A M hG lam α f') x := by
  intro F E _ _ _ _ _ A r τ p hG lam M ψ hψ μK hμK α f' hf' hα hαc hyp x
  letI := M.mG
  haveI := M.bG
  haveI := M.haarG
  haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)
  haveI : IsUltrametricDist F := Unram.ultraF (F := F) (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨hT2, hSC⟩ := K_inst A hG
  haveI := hT2
  haveI := hSC
  haveI := hμK.1
  set k : GL (Fin r) F → A.K → A.K → ℂ := fun g b' c' =>
    f' (act g (pt A hG lam b' c')) * A.psiK ψ (x.1 * c' + b' * x.2) *
      (eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ)) with hk
  have hL : desc A M hG lam α (fourG M ψ f') x = ∫ g, ∫ b', ∫ c', k g b' c' ∂μK ∂μK ∂M.μG := by
    unfold desc
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only
    rw [hyp g x.1 x.2]
    unfold Et.fourK
    rw [mul_assoc, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun b' => ?_)
    simp only
    rw [← integral_mul_const]
  have hR : A.fourK μK ψ (desc A M hG lam α f') x = ∫ b', ∫ c', ∫ g, k g b' c' ∂M.μG ∂μK ∂μK := by
    unfold Et.fourK desc
    refine integral_congr_ae (Eventually.of_forall fun b' => ?_)
    refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
    simp only
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [hk]; ring
  rw [hL, hR]
  have hbij := (GlobalTheory.JR.EtInv.invK_regular_iff_isUnit F E A r τ p lam hG).1
  let ρl : A.K →ₗ[F] (Fin r → F) :=
    LinearMap.pi fun i : Fin r => (Algebra.trace F A.K).comp (LinearMap.mulLeft F (τ ^ (i : ℕ)))
  let ρe : A.K ≃ₗ[F] (Fin r → F) := LinearEquiv.ofBijective ρl (by exact hbij)
  have hρs : Continuous ρe.symm := IsModuleTopology.continuous_of_linearMap ρe.symm.toLinearMap
  have hes : Continuous (bas A hG).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (bas A hG).equivFun.symm.toLinearMap
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hST : IsCompact (tsupport α ×ˢ tsupport f') := hαc.prod hf'.2
  refine swap_triple M.μG μK k ?_ (tsupport α)
    ((bas A hG).equivFun.symm '' ((fun z : GL (Fin r) F × Gl r F =>
      ((z.1⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) *ᵥ z.2.2.1) '' (tsupport α ×ˢ tsupport f')))
    (ρe.symm '' ((fun z : GL (Fin r) F × Gl r F =>
      z.2.2.2.1 ᵥ* (z.1 : Matrix (Fin r) (Fin r) F)) '' (tsupport α ×ˢ tsupport f')))
    hαc ?_ ?_ ?_
  · have h1 : Continuous (fun z : (A.K × A.K) × GL (Fin r) F => f' (act z.2 (pt A hG lam z.1.1 z.1.2))) :=
      hf'.1.continuous.comp ((continuous_act r).comp
        (continuous_snd.prodMk ((continuous_pt A hG lam).comp continuous_fst)))
    have h2 : Continuous (fun z : (A.K × A.K) × GL (Fin r) F => A.psiK ψ (x.1 * z.1.2 + z.1.1 * x.2)) :=
      (continuous_psi ψ hψ).comp (htr.comp
        ((continuous_const.mul continuous_fst.snd).add (continuous_fst.fst.mul continuous_const)))
    have h3 : Continuous (fun z : (A.K × A.K) × GL (Fin r) F => eta ((z.2 : Matrix (Fin r) (Fin r) F).det)) :=
      (continuous_eta_det r).comp continuous_snd
    have h4 : Continuous (fun z : (A.K × A.K) × GL (Fin r) F => ((α z.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hα.continuous.comp continuous_snd)
    exact (h1.mul h2).mul (h3.mul h4)
  · exact (hST.image ((Units.continuous_coe_inv.comp continuous_fst).matrix_mulVec
      continuous_snd.snd.fst)).image hes
  · exact (hST.image (continuous_snd.snd.snd.fst.matrix_vecMul
      (Units.continuous_val.comp continuous_fst))).image hρs
  · intro g b c hne
    have hf0 : f' (act g (pt A hG lam b c)) ≠ 0 := fun h => hne (by simp only [hk, h, zero_mul])
    have hα0 : α g ≠ 0 := fun h => hne (by simp only [hk, h, Complex.ofReal_zero, mul_zero])
    have hgS : g ∈ tsupport α := subset_tsupport _ hα0
    have hYT : act g (pt A hG lam b c) ∈ tsupport f' := subset_tsupport _ hf0
    have hinv : ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * (g : Matrix (Fin r) (Fin r) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine ⟨hgS, ⟨_, ⟨(g, _), ⟨hgS, hYT⟩, rfl⟩, ?_⟩, ⟨_, ⟨(g, _), ⟨hgS, hYT⟩, rfl⟩, ?_⟩⟩
    · simp only [act, pt, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, LinearEquiv.symm_apply_apply]
    · have hρc : ρe c = fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c) := rfl
      simp only [act, pt, Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
      rw [← hρc, LinearEquiv.symm_apply_apply]

end GlobalTheory.JR.LinDesc.Swap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NegOneMemNormOfValuationEq
section
open ValuativeRel

namespace GlobalTheory


open GroundTheory.LocalField in
theorem neg_one_mem_norm_of_valuation_eq : ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E], (∀ y : E, ∃ x : F, y ≤ᵥ algebraMap F E x ∧ algebraMap F E x ≤ᵥ y) → ∃ z : E, Algebra.norm F z = -1 := by
  intro F E _ _ _ _ _ _ _ _ _ _ _ hval
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  obtain ⟨x, h1, h2⟩ := hval (ϖ : E)
  have hv : valuation E (ϖ : E) = valuation E (algebraMap F E x) :=
    le_antisymm ((Valuation.Compatible.vle_iff_le _ _).1 h1) ((Valuation.Compatible.vle_iff_le _ _).1 h2)
  have hord : ord (ϖ : E) = ord (algebraMap F E x) := by
    simp only [ord]
    rw [(normalizedValuation_eq_iff (K := E)).2 hv]
  rw [ord_uniformizer hϖ, ord_algebraMap] at hord
  have he : ramificationIndex F E = 1 := by
    have hd : ((ramificationIndex F E : ℕ) : ℤ) ∣ 1 := ⟨ord x, hord⟩
    exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hd
  haveI : IsUnramified F E := (isUnramified_iff F E).2 he
  obtain ⟨w, hw⟩ := normIntegerUnits_surjective (K := F) (L := E) (-1)
  refine ⟨((w : 𝒪[E]) : E), ?_⟩
  have := congrArg (fun u : 𝒪[F]ˣ => ((u : 𝒪[F]) : F)) hw
  simp only [coe_normIntegerUnits_eq] at this
  rw [← coe_norm_integer]
  simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem _root_.GlobalTheory.Cyc.norm_natCast_prime_padicComplex (l : ℕ) [Fact l.Prime] :
    ‖(l : PadicComplex l)‖ = (l : ℝ)⁻¹ := by
  have h1 := PadicComplex.norm_extends l (algebraMap ℚ_[l] (PadicAlgCl l) l)
  rw [PadicAlgCl.norm_extends, Padic.norm_p, map_natCast] at h1
  rw [← h1]
  norm_cast

theorem _root_.GlobalTheory.Cyc.norm_sub_one_le_of_isPrimitiveRoot {K : Type*} [NormedField K]
    [IsUltrametricDist K]
    {n : ℕ} (hn : n ≠ 0) {ζ μ : K} (hζ : IsPrimitiveRoot ζ n) (hμ : μ ^ n = 1) :
    ‖μ - 1‖ ≤ ‖ζ - 1‖ := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨k, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  have hnorm : ‖ζ‖ = 1 := by
    have h := congrArg norm hζ.pow_eq_one
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hn).mp h
  clear hμ
  induction k with
  | zero => simp
  | succ k ih =>
    have : ζ ^ (k + 1) - 1 = ζ ^ k * (ζ - 1) + (ζ ^ k - 1) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
    rw [norm_mul, norm_pow, hnorm, one_pow, one_mul]

theorem _root_.GlobalTheory.Cyc.norm_primitiveRoot_sub_one (l : ℕ) [hl : Fact l.Prime] (j : ℕ)
    (hj : 1 ≤ j) (ζ : PadicComplex l) (hζ : IsPrimitiveRoot ζ (l ^ j)) :
    ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by
  have hpos : 0 < l ^ j := pow_pos hl.out.pos j
  have hall : ∀ μ ∈ primitiveRoots (l ^ j) (PadicComplex l), ‖1 - μ‖ = ‖ζ - 1‖ := by
    intro μ hμ
    rw [mem_primitiveRoots hpos] at hμ
    rw [norm_sub_rev]
    exact le_antisymm
      (_root_.GlobalTheory.Cyc.norm_sub_one_le_of_isPrimitiveRoot hpos.ne' hζ hμ.pow_eq_one)
      (_root_.GlobalTheory.Cyc.norm_sub_one_le_of_isPrimitiveRoot hpos.ne' hμ hζ.pow_eq_one)
  have heval :=
    congrArg (Polynomial.eval 1) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Polynomial.eval_one_cyclotomic_prime_pow, Polynomial.eval_prod] at heval
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heval
  have hprod := congrArg norm heval
  rw [_root_.GlobalTheory.Cyc.norm_natCast_prime_padicComplex, norm_prod, Finset.prod_congr rfl hall, Finset.prod_const,
    hζ.card_primitiveRoots, Nat.totient_prime_pow hl.out (Nat.succ_pos k)] at hprod
  simp only [Nat.succ_sub_one, Nat.add_sub_cancel] at hprod ⊢
  have hN : l ^ k * (l - 1) ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ hl.out.ne_zero) (Nat.sub_ne_zero_of_lt hl.out.one_lt)
  have hcast : ((l ^ k * (l - 1) : ℕ) : ℝ) = (l : ℝ) ^ k * ((l : ℝ) - 1) := by
    push_cast [Nat.cast_sub hl.out.one_le]
    ring
  rw [← Real.pow_rpow_inv_natCast (norm_nonneg (ζ - 1)) hN, ← hprod, hcast,
    Real.inv_rpow (Nat.cast_nonneg l), ← Real.rpow_neg (Nat.cast_nonneg l), neg_div, one_div]

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotIsRootResidueCofactorUnramifiedExt
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr.ResMult

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem not_isRoot_cofactor : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ s : K'.O,
    (∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O, algebraMap K'.O K'.E y =
      f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) + algebraMap K'.O K'.E z) →
    ∀ (p : K.O[X]) (r c : K'.O[X]), p.Monic → r.Monic →
      r.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ r.natDegree →
      p.natDegree = d * r.natDegree →
      p.map (φ.comp (algebraMap K.O K.E)) = (r * c).map (algebraMap K'.O K'.E) →
      ¬ (c.map (IsLocalRing.residue K'.O)).IsRoot (IsLocalRing.residue K'.O s) := by
  intro K K' d φ hU s hgen p r c hp hr hrbar hdeg heq
  classical
  set φO := intMap hU with hφO
  have hspec : (algebraMap K'.O K'.E).comp φO = φ.comp (algebraMap K.O K.E) :=
    RingHom.ext fun a => intMap_spec hU a
  have hmax : ∀ a ∈ IsLocalRing.maximalIdeal K.O, φO a ∈ IsLocalRing.maximalIdeal K'.O := by
    intro a ha
    rw [← map_maximalIdeal hU]
    exact Ideal.mem_map_of_mem _ ha
  haveI : IsLocalHom φO := ⟨fun a ha => by
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal _).1 (hmax a ((IsLocalRing.mem_maximalIdeal _).2 h)) ha⟩
  let k := IsLocalRing.ResidueField K.O
  let k' := IsLocalRing.ResidueField K'.O
  let ψ : k →+* k' := IsLocalRing.ResidueField.map φO
  have hψ : ∀ a : K.O, ψ (IsLocalRing.residue K.O a) = IsLocalRing.residue K'.O (φO a) :=
    fun a => IsLocalRing.ResidueField.map_residue φO a
  letI : Algebra k k' := ψ.toAlgebra
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype k' := Fintype.ofFinite k'
  set Q := Fintype.card k with hQdef
  have hQ : Q = K.q ^ 2 := by rw [hQdef, ← Nat.card_eq_fintype_card]; exact K.card_res
  have hQ' : Fintype.card k' = Q ^ d := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (IsLocalRing.ResidueField K'.O) = _
    rw [K'.card_res, hU.1, hQ, ← pow_mul, ← pow_mul, mul_comm]
  have hQ1 : 1 < Q := Fintype.one_lt_card
  have hd : d ≠ 0 := hU.ne_zero
  set F := FiniteField.frobeniusAlgHom k k' with hF
  have hFpow : ∀ (i : ℕ) (x : k'), (F ^ i) x = x ^ (Q ^ i) := by
    intro i x
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', AlgHom.mul_apply, ih, FiniteField.coe_frobeniusAlgHom]
      show (x ^ Q ^ i) ^ Q = x ^ Q ^ (i + 1)
      rw [← pow_mul, ← pow_succ]

  have hrc : r * c = p.map φO := by
    apply Polynomial.map_injective _ (IsFractionRing.injective K'.O K'.E)
    rw [← heq, Polynomial.map_map, hspec]
  set sb := IsLocalRing.residue K'.O s with hsb
  set P := (r * c).map (IsLocalRing.residue K'.O) with hP
  have hP2 : P = (p.map (IsLocalRing.residue K.O)).map ψ := by
    rw [hP, hrc, Polynomial.map_map, Polynomial.map_map]
    congr 1
  have hPmon : P.Monic := by rw [hP2]; exact (hp.map _).map _
  have hP0 : P ≠ 0 := hPmon.ne_zero
  have hPdeg : P.natDegree = d * r.natDegree := by
    rw [hP2, (hp.map _).natDegree_map, hp.natDegree_map, hdeg]
  have hPmul : P = r.map (IsLocalRing.residue K'.O) * c.map (IsLocalRing.residue K'.O) := by
    rw [hP, Polynomial.map_mul]
  have hmu : rootMultiplicity sb P = r.natDegree + rootMultiplicity sb (c.map (IsLocalRing.residue K'.O)) := by
    rw [hPmul, rootMultiplicity_mul (hPmul ▸ hP0), hrbar, rootMultiplicity_X_sub_C_pow]

  have hconj : ∀ i : ℕ, rootMultiplicity sb P ≤ rootMultiplicity (sb ^ (Q ^ i)) P := by
    intro i
    have h := le_rootMultiplicity_map (f := ((F ^ i : k' →ₐ[k] k') : k' →+* k')) (p := P) ?_ sb
    · have hPFi : P.map ((F ^ i : k' →ₐ[k] k') : k' →+* k') = P := by
        rw [hP2, Polynomial.map_map]
        congr 1
        exact RingHom.ext fun x => (F ^ i).commutes x
      rw [hPFi] at h
      simpa [hFpow] using h
    · rw [hP2, Polynomial.map_map]
      have : ((F ^ i : k' →ₐ[k] k') : k' →+* k').comp ψ = ψ := RingHom.ext fun x => (F ^ i).commutes x
      rw [this, ← hP2]; exact hP0

  have hinj : ∀ i j, i < j → j < d → sb ^ (Q ^ i) ≠ sb ^ (Q ^ j) := by
    intro i j hij hjd h
    obtain ⟨m, rfl⟩ : ∃ m, j = i + m := ⟨j - i, by omega⟩
    have hm : 0 < m := by omega
    have hfix : sb ^ (Q ^ m) = sb := by
      apply RingHom.injective ((F ^ i : k' →ₐ[k] k') : k' →+* k')
      rw [AlgHom.coe_toRingHom, hFpow, hFpow, h, ← pow_mul, pow_add, mul_comm]
    have hall : ∀ y : k', y ^ (Q ^ m) = y := by
      intro y
      obtain ⟨y', rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨f, z, hz, hy⟩ := hgen y'
      have hy' : y' = f.eval₂ φO s + z := by
        apply IsFractionRing.injective K'.O K'.E
        rw [hy, map_add (f := _), Polynomial.hom_eval₂, hspec]
      have hres : IsLocalRing.residue K'.O y' = f.eval₂ (ψ.comp (IsLocalRing.residue K.O)) sb := by
        rw [hy', map_add (f := _), (IsLocalRing.residue_eq_zero_iff z).2 hz, add_zero, Polynomial.hom_eval₂]
        congr 1
      have hev := Polynomial.hom_eval₂ f (ψ.comp (IsLocalRing.residue K.O))
        ((F ^ m : k' →ₐ[k] k') : k' →+* k') sb
      have hc : ((F ^ m : k' →ₐ[k] k') : k' →+* k').comp (ψ.comp (IsLocalRing.residue K.O)) =
          ψ.comp (IsLocalRing.residue K.O) := RingHom.ext fun a => (F ^ m).commutes (IsLocalRing.residue K.O a)
      rw [hc, AlgHom.coe_toRingHom, hFpow m sb, hfix, hFpow] at hev
      rw [hres]; exact hev
    have hQm : 1 < Q ^ m := Nat.one_lt_pow hm.ne' hQ1
    have hcard : Fintype.card k' ≤ Q ^ m := by
      have h1 := card_le_degree_of_subset_roots (p := (X ^ (Q ^ m) - X : k'[X])) (Z := Finset.univ) (by
        intro y _
        rw [mem_roots (Polynomial.X_pow_sub_X_ne_zero (R := k') hQm)]
        simp [IsRoot, hall y])
      rwa [Polynomial.natDegree_X_pow_sub_X (R := k') hQm, Finset.card_univ] at h1
    rw [hQ'] at hcard
    exact absurd hcard (not_le.2 (Nat.pow_lt_pow_right hQ1 (by omega)))

  let t : ℕ → k' := fun i => sb ^ (Q ^ i)
  have htinj : Set.InjOn t (Finset.range d) := by
    intro i hi j hj h
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd h (hinj i j h' (by simpa using hj))
    · exact h'
    · exact absurd h.symm (hinj j i h' (by simpa using hi))
  set S := (Finset.range d).image t with hSdef
  have hS : S.card = d := by rw [Finset.card_image_of_injOn htinj, Finset.card_range]
  have hsum1 : d * rootMultiplicity sb P ≤ ∑ x ∈ S, P.roots.count x := by
    calc d * rootMultiplicity sb P = ∑ _x ∈ S, rootMultiplicity sb P := by
          rw [Finset.sum_const, hS, smul_eq_mul]
      _ ≤ ∑ x ∈ S, P.roots.count x := Finset.sum_le_sum fun x hx => by
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
          rw [count_roots]; exact hconj i
  have hsum2 : ∑ x ∈ S, P.roots.count x ≤ Multiset.card P.roots := by
    calc ∑ x ∈ S, P.roots.count x ≤ ∑ x ∈ S ∪ P.roots.toFinset, P.roots.count x :=
          Finset.sum_le_sum_of_subset Finset.subset_union_left
      _ = ∑ x ∈ P.roots.toFinset, P.roots.count x :=
          (Finset.sum_subset Finset.subset_union_right fun x _ hx =>
            Multiset.count_eq_zero.2 (by simpa using hx)).symm
      _ = Multiset.card P.roots := Multiset.toFinset_sum_count_eq _
  have hle : d * rootMultiplicity sb P ≤ d * r.natDegree :=
    hsum1.trans (hsum2.trans ((card_roots' P).trans hPdeg.le))
  have hle' := Nat.le_of_mul_le_mul_left hle (Nat.pos_of_ne_zero hd)
  have hc0 : c.map (IsLocalRing.residue K'.O) ≠ 0 := right_ne_zero_of_mul (hPmul ▸ hP0)
  intro hroot
  have := (rootMultiplicity_pos hc0).2 hroot
  omega

end GlobalTheory.UnitLemma.Unr.ResMult
end
end

