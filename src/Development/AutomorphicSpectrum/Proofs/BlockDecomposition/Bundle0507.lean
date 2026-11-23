module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExponentialGluing.ExpNegGlueHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2Gluing.IntegralLeToReal
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UnipotentVanishing.InfAtUnipInvEqZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0478

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoExpMulPoly
section
noncomputable section

open NumberField MeasureTheory Filter Topology
open scoped ENNReal
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E.E3

namespace GlobalTheory.CompanionTheory.LocExponent

theorem tendsto_exp_mul_poly (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (M : ℕ) :
    Tendsto (fun t : ℝ => Real.exp (-(2 * ε * t)) * (1 + B * (1 + t)) ^ M) atTop (𝓝 0) := by
  have h := (isLittleO_pow_exp_pos_mul_atTop M (show 0 < 2 * ε by positivity)).tendsto_div_nhds_zero
  have h2 := h.const_mul ((1 + 2 * B) ^ M)
  rw [mul_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with t ht
    have h0 : 0 ≤ 1 + B * (1 + t) := by nlinarith
    positivity
  · filter_upwards [eventually_ge_atTop 1] with t ht
    have h1 : 1 + B * (1 + t) ≤ (1 + 2 * B) * t := by nlinarith
    have h0 : 0 ≤ 1 + B * (1 + t) := by nlinarith
    have hp := pow_le_pow_left₀ h0 h1 M
    rw [Real.exp_neg, mul_comm (Real.exp (2 * ε * t))⁻¹, ← div_eq_mul_inv, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by rwa [mul_pow] at hp) (Real.exp_pos _).le

theorem re_lt_of_dec {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (μ : Measure G) [μ.IsHaarMeasure] (ρ : ℝ) (a : ℝ → G)
    {F : G → ℂ} (hdecF : PositivityTheory.Rg.Rs.JExpNegGlue.Dec μ ρ a F) (hF0 : F ≠ 0) {c : ℂ}
    (hFeq : ∀ (t : ℝ) g, F (a t * g) = Complex.exp (c * t) * F g) : c.re < ρ := by
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, F g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hF0 (funext h)
  obtain ⟨Q, hQc, hQn⟩ := exists_compact_mem_nhds g₀
  have hFc := hdecF.1
  set I := ∫ g in Q, ‖F g‖ ^ 2 ∂μ with hI
  have hIpos : 0 < I := by
    have hint : IntegrableOn (fun g => ‖F g‖ ^ 2) Q μ := (hFc.norm.pow 2).continuousOn.integrableOn_compact hQc
    rw [hI, setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun g => by show (0 : ℝ) ≤ ‖F g‖ ^ 2; positivity) hint]
    have hopen : IsOpen (Function.support (fun g => ‖F g‖ ^ 2) ∩ interior Q) :=
      (hFc.norm.pow 2).isOpen_support.inter isOpen_interior
    have hne : (Function.support (fun g => ‖F g‖ ^ 2) ∩ interior Q).Nonempty :=
      ⟨g₀, by simp [Function.mem_support, hg₀], mem_interior_iff_mem_nhds.2 hQn⟩
    exact lt_of_lt_of_le (hopen.measure_pos μ hne)
      (measure_mono (Set.inter_subset_inter_right _ interior_subset))
  have hval : ∀ t : ℝ, Real.exp (-(2 * ρ * t)) * ∫ g in Q, ‖F (a t * g)‖ ^ 2 ∂μ =
      Real.exp (2 * (c.re - ρ) * t) * I := by
    intro t
    have hre : (c * (t : ℂ)).re = c.re * t := by simp
    have hpt : ∀ g, ‖F (a t * g)‖ ^ 2 = Real.exp (c.re * t) ^ 2 * ‖F g‖ ^ 2 := by
      intro g
      rw [hFeq, norm_mul, Complex.norm_exp, mul_pow, hre]
    simp_rw [hpt]
    rw [integral_const_mul, ← mul_assoc, sq, ← Real.exp_add, ← Real.exp_add]
    congr 2; ring
  have hlim := hdecF.2 Q hQc
  rw [tendsto_congr hval] at hlim
  by_contra hge
  push Not at hge
  have hev : ∀ᶠ t in atTop, I ≤ Real.exp (2 * (c.re - ρ) * t) * I := by
    filter_upwards [eventually_ge_atTop 0] with t ht
    have h1 : 1 ≤ Real.exp (2 * (c.re - ρ) * t) :=
      Real.one_le_exp (by nlinarith [mul_nonneg (sub_nonneg.2 hge) ht])
    nlinarith
  have := ge_of_tendsto hlim hev
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}


omit [IsCMField E] in
theorem mult_of_lat {S : Set (GA E N)} {n : ℕ}
    (h : ∀ x, {γ : An.lat E N | (γ : GA E N) * x ∈ S}.encard ≤ n) : Mult S n := by
  intro x
  have hle : (ratGL E N).range ≤ An.lat E N := le_sup_left
  refine le_trans ?_ (h x)
  have hinj : Set.InjOn (Subgroup.inclusion hle) {γ : (ratGL E N).range | (γ : GA E N) * x ∈ S} :=
    (Subgroup.inclusion_injective hle).injOn
  rw [← hinj.encard_image]
  refine Set.encard_le_encard ?_
  rintro _ ⟨γ, hγ, rfl⟩
  exact hγ

omit [IsCMField E] in
theorem rho_nonneg {r : ℕ} (hrN : r < N) : 0 ≤ An.rho E N r := by
  unfold An.rho
  have : (r : ℝ) ≤ N := by exact_mod_cast hrN.le
  exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 this)) two_pos.le)

theorem integral_ctn_le (hSize : SizeT) {φ : GA E N → ℂ} (hφ : Continuous φ) (hLoc : Loc φ) {r : ℕ}
    (hr : 0 < r) (hrN : r < N) (μ : Measure (GA E N)) [hμ : μ.IsHaarMeasure] {Q : Set (GA E N)} (hQ : IsCompact Q) :
    ∃ (K B : ℝ) (M : ℕ), 0 ≤ K ∧ 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
      ∫ g in Q, ‖An.ctn r φ (An.aR E N r t * g)‖ ^ 2 ∂μ ≤
        K * (Real.exp (2 * An.rho E N r * t) * (1 + B * (1 + t)) ^ M) := by
  obtain ⟨D, hD, hD0⟩ := GroundTheory.Automorphic.AutomorphicForm.exists_isCompact_superset_unipFundamentalDomain
    (K := E) (n := N) (r := r)
  obtain ⟨C₁, hC₁⟩ := l2glue.count_le count_holds hr hrN hD hQ
  obtain ⟨C, M, hCM⟩ := hLoc μ hμ
  obtain ⟨B, hB, hsz⟩ := hSize E N (GroundTheory.Automorphic.AutomorphicForm.unipGL '' D) Q
    (hD.image GroundTheory.Automorphic.AutomorphicForm.continuous_unipGL) hQ
  have hρ : 0 ≤ An.rho E N r := rho_nonneg hrN
  refine ⟨max C 0 * (max C₁ 0 + 1), B, M, by positivity, hB, fun t ht => ?_⟩
  set e := Real.exp (2 * An.rho E N r * t) with he
  set n : ℕ := ⌈C₁ * e⌉₊ with hn
  set R : ℝ := B * (1 + t) with hR
  have hR0 : 0 ≤ R := by positivity
  have hS := l2glue.isCompact_sset r t hD hQ
  have hmult : Mult (l2glue.sset E N r t D Q) n := mult_of_lat (hC₁ t ht)
  have hlog : ∀ g ∈ l2glue.sset E N r t D Q, logSize g ≤ R := by
    rintro _ ⟨⟨X, q⟩, ⟨hX, hq⟩, rfl⟩
    have hx := hsz _ ⟨X, hX, rfl⟩ q hq (fun i : Fin N => if (i : ℕ) < r then t else 0)
    refine hx.trans (mul_le_mul_of_nonneg_left ?_ hB)
    have : ‖fun i : Fin N => if (i : ℕ) < r then t else 0‖ ≤ t := by
      refine (pi_norm_le_iff_of_nonneg ht).2 fun i => ?_
      split_ifs
      · rw [Real.norm_of_nonneg ht]
      · simpa using ht
    linarith
  have h3 := hCM _ hS n R hR0 hmult hlog
  have h2 := l2glue.swap μ φ hφ r t hD hD0 hQ
  have h1 := l2glue.integral_le_toReal (μ.restrict Q) (fun g => An.ctn r φ (An.aR E N r t * g))
  have hP : 0 ≤ (1 + R) ^ M := by positivity
  have he1 : 1 ≤ e := Real.one_le_exp (by positivity)
  have hnle : (n : ℝ) ≤ (max C₁ 0 + 1) * e := by
    have h6 : (n : ℝ) ≤ ⌈max C₁ 0 * e⌉₊ := by
      exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (by linarith))
    have h7 := (Nat.ceil_lt_add_one (show 0 ≤ max C₁ 0 * e by positivity)).le
    nlinarith
  have h4 : ENNReal.ofReal (C * n * (1 + R) ^ M) ≤ ENNReal.ofReal (max C 0 * n * (1 + R) ^ M) := by
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)) hP)
  have h5 : (∫⁻ g in Q, ‖An.ctn r φ (An.aR E N r t * g)‖ₑ ^ 2 ∂μ).toReal ≤ max C 0 * n * (1 + R) ^ M := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h2.trans (h3.trans h4))
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  calc _ ≤ _ := h1
    _ ≤ _ := h5
    _ ≤ max C 0 * ((max C₁ 0 + 1) * e) * (1 + R) ^ M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnle (by positivity)) hP
    _ = _ := by ring

theorem tendsto_ctn (hSize : SizeT) {φ : GA E N → ℂ} (hφ : Continuous φ) (hLoc : Loc φ) {r : ℕ}
    (hr : 0 < r) (hrN : r < N) (μ : Measure (GA E N)) [hμ : μ.IsHaarMeasure] {ε : ℝ} (hε : 0 < ε)
    {Q : Set (GA E N)} (hQ : IsCompact Q) :
    Tendsto (fun t : ℝ => Real.exp (-(2 * (An.rho E N r + ε) * t)) *
      ∫ g in Q, ‖An.ctn r φ (An.aR E N r t * g)‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  obtain ⟨K, B, M, hK, hB, hb⟩ := integral_ctn_le hSize hφ hLoc hr hrN μ hQ
  have hlim := (tendsto_exp_mul_poly B ε hB hε M).const_mul K
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun t => mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => by positivity)) ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  have h := mul_le_mul_of_nonneg_left (hb t ht) (Real.exp_pos (-(2 * (An.rho E N r + ε) * t))).le
  refine h.trans (le_of_eq ?_)
  have hee : Real.exp (-(2 * (An.rho E N r + ε) * t)) * Real.exp (2 * An.rho E N r * t) = Real.exp (-(2 * ε * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← hee]; ring

end GlobalTheory.CompanionTheory.LocExponent

namespace GlobalTheory.CompanionTheory.LocExponent


open PositivityTheory.Rg.Rs.JExpNegGlue in
theorem locNonPosGlue_holds : LocNonPosGlue := by
  intro hSize E _ _ _ N φ hA hLoc r hr0 hrN c hc
  have : LocallyCompactSpace (GA E N) := by
    set_option synthInstance.maxHeartbeats 400000 in
      exact inferInstance
  have : T2Space (GA E N) := by
    set_option synthInstance.maxHeartbeats 400000 in
      exact inferInstance
  obtain ⟨haR, -, -, hct⟩ := dict_holds E N
  have hctn := (hct φ hA r hr0 hrN).2
  obtain ⟨F₀, hF₀, F, hFspan, hF0, hFeq⟩ := hc
  obtain ⟨c₀, -, hF₀eq⟩ := hctn F₀ hF₀
  subst hF₀eq
  have hφc : Continuous φ.1 := GlobalTheory.CompanionTheory.ConstTerm.continuous_of_isOpen_stab φ hA.level
  let μ : Measure (GA E N) := Measure.haar
  have : μ.IsHaarMeasure := inferInstance
  set a : ℝ → GA E N := aT E N r with ha
  have hcomm : ∀ s t, a s * a t = a t * a s := aT_comm E N r
  have hlt : ∀ ε : ℝ, 0 < ε → c.re < An.rho E N r + ε := by
    intro ε hε
    have hdec_ctn : Dec μ (An.rho E N r + ε) a (An.ctn r φ.1) := by
      have hctc : Continuous (An.ctn r φ.1) := by
        have : SecondCountableTopology (GA E N) := by
          set_option synthInstance.maxHeartbeats 400000 in
            exact inferInstance
        have : FirstCountableTopology (GA E N) := by
          set_option synthInstance.maxHeartbeats 400000 in
            exact inferInstance
        obtain ⟨C, hC, hDC⟩ := GroundTheory.Automorphic.AutomorphicForm.exists_isCompact_superset_unipFundamentalDomain (K := E) (n := N) (r := r)
        have : IsFiniteMeasure ((GroundTheory.Automorphic.AutomorphicForm.unipMeasure E N r).restrict (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r)) :=
          isFiniteMeasure_restrict.2 (by rw [GroundTheory.Automorphic.AutomorphicForm.unipMeasure_unipFundamentalDomain]; exact ENNReal.one_ne_top)
        have hf : Continuous (Function.uncurry fun (g : GA E N) (X : GroundTheory.Automorphic.AutomorphicForm.UPos N r → AdeleRing (𝓞 E) E) =>
            φ.1 (GroundTheory.Automorphic.AutomorphicForm.unipGL X * g)) :=
          hφc.comp ((GroundTheory.Automorphic.AutomorphicForm.continuous_unipGL.comp continuous_snd).mul continuous_fst)
        have h := continuous_parametric_integral_of_continuous
          (μ := (GroundTheory.Automorphic.AutomorphicForm.unipMeasure E N r).restrict (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r)) hf hC
        have e : ∀ g : GA E N, GroundTheory.Automorphic.AutomorphicForm.constantTerm r φ.1 g = ∫ X in C, φ.1 (GroundTheory.Automorphic.AutomorphicForm.unipGL X * g)
            ∂((GroundTheory.Automorphic.AutomorphicForm.unipMeasure E N r).restrict (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r)) := by
          intro g
          rw [Measure.restrict_restrict' GroundTheory.Automorphic.AutomorphicForm.measurableSet_unipFundamentalDomain, Set.inter_eq_right.2 hDC]
          rfl
        unfold An.ctn
        exact continuous_const.mul (h.congr fun g => (e g).symm)
      refine ⟨hctc, fun Q hQ => ?_⟩
      have h := tendsto_ctn hSize hφc hLoc hr0 hrN μ hε hQ
      simp only [ha, haR]
      exact h
    have hdecF : Dec μ (An.rho E N r + ε) a F := by
      refine Submodule.span_induction (p := fun H _ => Dec μ (An.rho E N r + ε) a H) ?_ (dec_zero μ _ a)
        (fun x y _ _ hx hy => dec_add μ _ a hx hy) (fun b x _ hx => dec_smul μ _ a b hx) hFspan
      rintro _ ⟨s, rfl⟩
      convert dec_smul μ _ a c₀ (dec_translate μ _ a hcomm s hdec_ctn) using 1
    exact re_lt_of_dec μ _ a hdecF hF0 hFeq
  have hle : c.re ≤ An.rho E N r := le_of_forall_pos_le_add fun ε hε => (hlt ε hε).le
  have hd : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  rw [An.rho] at hle
  unfold pE
  have : c.re / (Module.finrank ℚ E : ℝ) ≤ (r : ℝ) * ((N : ℝ) - r) / 2 := by
    rw [div_le_iff₀ hd]; linarith
  linarith

end GlobalTheory.CompanionTheory.LocExponent

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusSiegelHeightLowerBound
section
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov.FirstLower

section Helpers

open PositivityTheory.ThKEst (rId)
open PositivityTheory.ThKEst.Sieg (rId_add rId_zero' rId_snd)
open GroundTheory.Automorphic.Anisotropic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rIdele [IsTotallyReal F] (c : ℝ) : GroundTheory.Global.IdeleGroup F where
  val := rId F c
  inv := rId F (-c)
  val_inv := by rw [← rId_add, add_neg_cancel, rId_zero']
  inv_val := by rw [← rId_add, neg_add_cancel, rId_zero']

theorem ideleModule_rIdele [IsTotallyReal F] (c : ℝ) :
    (GroundTheory.Global.IdeleGroup.ideleModule F (rIdele c) : ℝ) = Real.exp ((Module.finrank ℚ F : ℝ) * c) := by
  have hm : ∀ w : InfinitePlace F, w.mult = 1 := fun w => by
    rw [InfinitePlace.mult, ite_eq_left (IsTotallyReal.isReal w)]
  have hinf : ∀ w : InfinitePlace F, ‖(rId F c).1 w‖ ^ w.mult = Real.exp c := fun w => by
    rw [hm, pow_one]
    exact norm_evInf_rId w c
  have hfin : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ‖(rId F c).2 v‖ = 1 := fun v => by
    rw [rId_snd]
    exact norm_one
  have e : (GroundTheory.Global.IdeleGroup.ideleModule F (rIdele c) : ℝ) =
      (∏ w : InfinitePlace F, ‖(rId F c).1 w‖ ^ w.mult) *
        ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ‖(rId F c).2 v‖ :=
    GroundTheory.Global.IdeleGroup.ideleModule_eq _
  rw [e, finprod_eq_one_of_forall_eq_one hfin, mul_one, Finset.prod_congr rfl fun w _ => hinf w,
    Finset.prod_const, Finset.card_univ, card_infinitePlace, ← Real.exp_nat_mul]

variable {n r : ℕ}

theorem mulVec_ratV_col {X : Matrix (Fin n) (Fin (r + 1)) E} {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)}
    {B : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)} (hB : B.BlockTriangular id)
    (h : M * adMat F X = adMat F X * B) : M *ᵥ ratV F (Xᵀ 0) = B 0 0 • ratV F (Xᵀ 0) := by
  funext i
  have h1 : (M *ᵥ ratV F (Xᵀ 0)) i = (M * adMat F X) i 0 := rfl
  rw [h1, h, Matrix.mul_apply, Finset.sum_eq_single 0]
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  · intro j _ hj
    rw [hB (show id (0 : Fin (r + 1)) < id j from Fin.pos_of_ne_zero hj), mul_zero]
  · simp

theorem ratV_smul (e : E) (w : Fin n → E) : ratV F (e • w) = inclR (F := F) (AF F) e • ratV F w := by
  funext i
  simp [ratV, map_mul]

theorem resVec_algebraMap_smul [Algebra.IsQuadraticExtension F E] (c : AF F) (ξ : Fin n → AF F ⊗[F] E) :
    resVec (ι := Fin n) (Module.finBasis F E) (AF F) (algebraMap (AF F) (AF F ⊗[F] E) c • ξ) =
      c • resVec (ι := Fin n) (Module.finBasis F E) (AF F) ξ := by
  have e : algebraMap (AF F) (AF F ⊗[F] E) c • ξ = c • ξ := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def]
  rw [e]
  conv_lhs => rw [← ofResVec_resVec (Module.finBasis F E) (AF F) ξ, ← ofResVec_smul, resVec_ofResVec]

variable {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin (r + 1)) E}

theorem IsTorus.inv_eq {a : (Fin (r + 1) → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) (s : Fin (r + 1) → ℝ) :
    (a s)⁻¹ = a (-s) := by
  have h0 : a 0 = 1 := by
    have := ha.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  rw [inv_eq_iff_mul_eq_one, ← ha.add, add_neg_cancel, h0]

theorem torus_inv_mulVec {a : (Fin (r + 1) → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) {p : GAd σ J}
    (hp : p ∈ minPar σ J X) (s : Fin (r + 1) → ℝ) (e : E) :
    (matHom _ σ J (a s)⁻¹).1 *ᵥ ((matHom _ σ J p).1 *ᵥ ratV F (e • Xᵀ 0)) =
      algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s 0)) • ((matHom _ σ J p).1 *ᵥ ratV F (e • Xᵀ 0)) := by
  obtain ⟨B, hB, hpB⟩ := hp
  have h1 := mulVec_ratV_col hB hpB
  have h2 := mulVec_ratV_col (Matrix.blockTriangular_diagonal _) (ha.onX (-s))
  rw [Matrix.diagonal_apply_eq] at h2
  rw [IsTorus.inv_eq ha, ratV_smul, Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_smul, h2]
  funext i
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem col_ne_zero (hW : IsWittFrame σ J X Y) : Xᵀ 0 ≠ 0 := by
  intro h0
  have h1 := congrFun (congrFun hW.xy 0) 0
  have hc : ∀ i, X i 0 = 0 := fun i => congrFun h0 i
  simp [cT, Matrix.mul_apply, hc] at h1

end Helpers


open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic GlobalTheory.CompanionTheory.RedCov.Bridge in
theorem vecMul_trG_torus {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {X Y : Matrix (Fin n) (Fin (r + 1)) E} {a : (Fin (r + 1) → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a)
    {ω : GAd σ J} (hω : ω⁻¹ ∈ minPar σ J X) (s : Fin (r + 1) → ℝ) (e : E) :
    (Reduction.ratVec (cvec F (e • Xᵀ 0)) ᵥ* (trG σ J ω).1) ᵥ* (trG σ J (a s)).1 =
      ((rIdele (-s 0) : GroundTheory.Global.IdeleGroup F) : AF F) •
        (Reduction.ratVec (cvec F (e • Xᵀ 0)) ᵥ* (trG σ J ω).1) := by
  have step : ∀ (g : GAd σ J) (ξ : Fin n → AF F ⊗[F] E),
      resVec (ι := Fin n) (Module.finBasis F E) (AF F) ξ ᵥ* (trG σ J g).1 =
        resVec (ι := Fin n) (Module.finBasis F E) (AF F) ((matHom _ σ J g⁻¹).1 *ᵥ ξ) := fun g ξ => by
    rw [trG, MonoidHom.comp_apply, map_inv]
    exact resVec_vecMul_trHom _ _ _ _
  rw [ratVec_cvec, step, step, torus_inv_mulVec ha hω, resVec_algebraMap_smul]
  rfl


open GroundTheory.Automorphic GlobalTheory.CompanionTheory.RedCov.Bridge in
theorem exp_le_hgt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ a, IsTorus σ J X Y a → ∀ (Ω C : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minPar σ J X → IsCompact C → ∃ P : ℝ, 0 < P ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 → Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0)) ≤ P * hgt σ J (ω * a s * κ) (e • Xᵀ 0) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW a ha Ω C hΩ hΩP hC
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  haveI : IsTotallyReal F := h.1
  have hcont : Continuous fun g : GAd σ J => (trG σ J g)⁻¹ := (continuous_trG σ J).inv
  obtain ⟨P₁, hP₁, hb₁⟩ := Reduction.exists_adelicNorm_vecMul_le_mul (hC.image hcont)
  obtain ⟨P₂, hP₂, hb₂⟩ := Reduction.exists_adelicNorm_vecMul_le_mul (hΩ.image hcont)
  refine ⟨P₁ * P₂, mul_pos hP₁ hP₂, fun ω hω s κ hκ e he => ?_⟩
  have hv : e • Xᵀ 0 ≠ 0 := smul_ne_zero he (col_ne_zero hW)
  have hc0 := cvec_ne_zero (F := F) hv
  set y₀ := Reduction.ratVec (cvec F (e • Xᵀ 0)) with hy₀
  have hf₀ : Reduction.HasFiniteContent y₀ := Reduction.hasFiniteContent_ratVec hc0
  set y₁ := y₀ ᵥ* (trG σ J ω).1 with hy₁
  have hf₁ : Reduction.HasFiniteContent y₁ := hf₀.vecMul (trG σ J ω)
  set u := rIdele (F := F) (-s 0) with hu
  have hkey : y₁ ᵥ* (trG σ J (a s)).1 = (u : AF F) • y₁ :=
    vecMul_trG_torus ha (inv_mem_minPar h hJ hW (hΩP hω)) s e
  have hg : hgt σ J (ω * a s * κ) (e • Xᵀ 0) = Reduction.adelicNorm (((u : AF F) • y₁) ᵥ* (trG σ J κ).1) := by
    rw [hgt_eq, Reduction.height, map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, ← hy₀, ← hy₁, hkey]
  have hf₂ : Reduction.HasFiniteContent (((u : AF F) • y₁) ᵥ* (trG σ J κ).1) := (hf₁.smul u).vecMul (trG σ J κ)
  have hb3 : Reduction.adelicNorm ((u : AF F) • y₁) ≤ P₁ * hgt σ J (ω * a s * κ) (e • Xᵀ 0) := by
    have := hb₁ _ ⟨κ, hκ, rfl⟩ _ hf₂
    rwa [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one, ← hg] at this
  have hb4 : Reduction.adelicNorm y₀ ≤ P₂ * Reduction.adelicNorm y₁ := by
    have := hb₂ _ ⟨ω, hω, rfl⟩ _ hf₁
    rwa [hy₁, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one] at this
  have h1 : 1 ≤ Reduction.adelicNorm y₀ := Reduction.one_le_adelicNorm_ratVec hc0
  have hsm : Reduction.adelicNorm ((u : AF F) • y₁) =
      Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0)) * Reduction.adelicNorm y₁ := by
    rw [Reduction.adelicNorm_smul hf₁ u, hu, ideleModule_rIdele, mul_neg]
  have hexp := Real.exp_pos (- ((Module.finrank ℚ F : ℝ) * s 0))
  calc Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0))
      ≤ Real.exp (- ((Module.finrank ℚ F : ℝ) * s 0)) * (P₂ * Reduction.adelicNorm y₁) :=
        le_mul_of_one_le_right hexp.le (h1.trans hb4)
    _ = P₂ * Reduction.adelicNorm ((u : AF F) • y₁) := by rw [hsm]; ring
    _ ≤ P₂ * (P₁ * hgt σ J (ω * a s * κ) (e • Xᵀ 0)) := mul_le_mul_of_nonneg_left hb3 hP₂.le
    _ = P₁ * P₂ * hgt σ J (ω * a s * κ) (e • Xᵀ 0) := by ring

end GlobalTheory.CompanionTheory.RedCov.FirstLower
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryPointsHeightBoundFinite
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor isTopologicalRing_tensor

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Mahler

open GlobalTheory.CompanionTheory.RedCov.Bridge

def pointsHomeo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    GAd (conj F E).toAlgHom J ≃ₜ unitaryPoints F E J 𝔸[F] where
  toFun g := ⟨matHom _ _ J g, (SetLike.ext_iff.1 (CompanionTheory.SWFin.HR_eq J (AF F)) _).1 g.2⟩
  invFun u := ⟨u.1, (SetLike.ext_iff.1 (CompanionTheory.SWFin.HR_eq J (AF F)) _).2 u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val _

theorem exists_isCompact_of_le_hgt : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsUnit H.det → ∀ (Y : Set (unitaryPoints F E H 𝔸[F])) (ε : ℝ), 0 < ε → (∀ u ∈ Y, ∀ x : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F, x ≠ 0 → ε ≤ Reduction.height (trHom (ι := Fin n) (Module.finBasis F E) 𝔸[F] (u : GL (Fin n) (𝔸[F] ⊗[F] E))) x) → ∃ Ω : Set (unitaryPoints F E H 𝔸[F]), IsCompact Ω ∧ ∀ u ∈ Y, ∃ θ ∈ (unitaryDiagonal F H).range, θ⁻¹ * u ∈ Ω) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ t : ℝ, 0 < t → ∃ C₀ : Set (GAd σ J), IsCompact C₀ ∧ ∀ g : GAd σ J, (∀ v : Fin n → E, v ≠ 0 → t ≤ hgt σ J g v) → ∃ γ ∈ ratPts σ J, γ⁻¹ * g ∈ C₀ := by
  intro hM F E _ _ _ _ _ σ hσ n J hJ t ht
  obtain ⟨hF, hE', h2, hc⟩ := hσ
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((hc τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)
  have hu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  let e := pointsHomeo (F := F) (E := E) J
  obtain ⟨Ω, hΩ, hcov⟩ := hM F E n J hu
    (e '' {g | ∀ v : Fin n → E, v ≠ 0 → t ≤ hgt _ J g v}) t ht (by
      rintro _ ⟨g, hg, rfl⟩ x hx
      obtain ⟨v, rfl⟩ := cvec_surjective (F := F) (E := E) (n := n) x
      have hv : v ≠ 0 := by
        rintro rfl
        apply hx
        funext p
        simp [cvec]
      have := hg v hv
      rw [hgt_eq] at this
      exact this)
  refine ⟨e ⁻¹' Ω, e.isCompact_preimage.2 hΩ, fun g hg => ?_⟩
  obtain ⟨θ, hθ, hθΩ⟩ := hcov (e g) ⟨g, hg, rfl⟩
  rw [← CompanionTheory.SWFin.HFin_eq, Subgroup.mem_subgroupOf] at hθ
  refine ⟨e.symm θ, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 hθ
  · exact hθΩ

end GlobalTheory.CompanionTheory.RedCov.Mahler
end
end

