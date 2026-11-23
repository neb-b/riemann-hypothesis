module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import GroundTheory.AutomorphicForms.ReductionFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0830
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysAtShortRationalVectorsRapidKernelOperator
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.RapidKernelDecay

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem norm_pInf_apply (x : Ad E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _


omit [_root_.NumberField.IsTotallyComplex E] in
theorem height_inv (y : GL (Fin a) (Cinf E)) : height y⁻¹ = height y := by
  unfold height; rw [inv_inv]; ring


omit [_root_.NumberField.IsTotallyComplex E] in
theorem pFin_vecMul (x : Fin a → Ad E) (m : GA E a) :
    (fun i => pFin E ((x ᵥ* m.val) i)) = (fun i => pFin E (x i)) ᵥ* m.val.map (pFin E) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [vecMul, dotProduct, map_sum]

theorem norm_vecMul_infGL_le (y : GL (Fin a) (Cinf E)) (x : Fin a → Ad E) :
    ‖fun i => pInf E ((x ᵥ* (infGL E a y).val) i)‖ ≤ (a * height y) * ‖fun i => pInf E (x i)‖ := by
  have hy : ∀ j i, ‖pInf E ((infGL E a y).val j i)‖ ≤ height y := by
    intro j i
    have e : pInf E ((infGL E a y).val j i) = y.val j i :=
      congrArg (fun u : GL (Fin a) (Cinf E) => u.val j i) (pInf_infGL (E := E) y)
    rw [e]
    have : ‖y.val j i‖ ≤ ‖toL y.val‖ :=
      (norm_le_pi_norm (toL y.val j) i).trans (norm_le_pi_norm (toL y.val) j)
    unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have h1 := one_le_height y
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [vecMul, dotProduct, map_sum, map_mul]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (height y * ‖fun i => pInf E (x i)‖)
    fun j _ => ?_).trans ?_)
  · rw [mul_comm (height y)]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_le_pi_norm (fun i => pInf E (x i)) j) (hy j i)
      (norm_nonneg _) (norm_nonneg _))
  · simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_of_eq (by ring)

theorem ideleModule_det_infGL_le (z : GL (Fin a) (Cinf E)) :
    (ideleModule E (GeneralLinearGroup.det (infGL E a z)) : ℝ) ≤
      ((a.factorial : ℝ) * height z ^ a) ^ (2 * Fintype.card (InfinitePlace E)) := by
  set u := GeneralLinearGroup.det (infGL E a z) with hu
  have hB : 1 ≤ (a.factorial : ℝ) * height z ^ a :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast a.factorial_pos) (one_le_pow₀ (one_le_height z))
  have hinf : pInf E (u : Ad E) = (GeneralLinearGroup.det z : Cinf E) := by
    rw [hu, ← CuspRep.det_map, pInf_infGL]
  have hfin : pFin E (u : Ad E) = 1 := by
    rw [hu, ← CuspRep.det_map, pFin_infGL, map_one, Units.val_one]
  rw [ideleModule_eq]
  have h2 : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖(u : Ad E).2 v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by
      have : (u : Ad E).2 = 1 := hfin
      rw [this]
      exact norm_one
  rw [h2, mul_one, pow_mul, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun w _ => ?_
  have h1 : ‖(u : Ad E).1 w‖ ≤ a.factorial * height z ^ a := by
    rw [← norm_pInf_apply, hinf]
    exact (norm_le_pi_norm _ w).trans (norm_det_le _ (by unfold height; linarith [norm_nonneg (toL (z⁻¹).val)]))
  have hm : w.mult ≤ 2 := by unfold InfinitePlace.mult; split_ifs <;> norm_num
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 _).trans (pow_le_pow_right₀ hB hm)

end GlobalTheory.RapidKernelDecay

namespace GlobalTheory.RapidKernelDecay

theorem decays_integral : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ)
    (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)),
    GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.ShortVecDecay.Decays F →
      GlobalTheory.ShortVecDecay.Decays (fun g : GA E a => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) := by
  intro E _ _ _ a F X _ ν _ k γ hk hF L hL C₀ hC₀ N
  obtain ⟨-, -, hkI⟩ := hk
  obtain ⟨C, hC⟩ := hF L hL C₀ hC₀ N
  obtain ⟨M₁, hM₁, h₁⟩ := GlobalTheory.ShortVecDecay.exists_norm_vecMul_le hC₀
  obtain ⟨M₂, hM₂, h₂⟩ := GlobalTheory.ShortVecDecay.exists_norm_vecMul_le hC₀.inv
  set n := a * Module.finrank ℚ E with hn
  set p := 2 * Fintype.card (InfinitePlace E) with hp
  set K₀ : ℝ := (M₂ * a * M₁) ^ n * (a.factorial : ℝ) ^ p with hK₀
  set m := n + a * p with hm
  set I := ∫ x, ‖k x‖ * height (γ x) ^ (m * N) ∂ν with hI
  refine ⟨I * (|C| * K₀ ^ N), fun g c hc ξ hξ hξL => ?_⟩
  set v : Fin a → Ad E := fun j => algebraMap E (Ad E) (ξ j) with hv
  set Xn := ‖fun i => pInf E ((v ᵥ* g.val) i)‖ with hXn
  set G := (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hG
  have hGpos : 0 < G := (ideleModule E _).2
  have key : ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * c * infGL E a y)‖ ≤ |C| * K₀ ^ N * height y ^ (m * N) * (Xn ^ n / G) ^ N := by
    intro y
    have hy1 := one_le_height y
    set g' := g * c * infGL E a y * c⁻¹ with hg'
    have eg : g * c * infGL E a y = g' * c := (inv_mul_cancel_right _ c).symm
    have hfin : (fun i => pFin E ((v ᵥ* g'.val) i)) = (fun i => pFin E ((v ᵥ* g.val) i)) := by
      rw [pFin_vecMul, pFin_vecMul]
      congr 1
      show (GeneralLinearGroup.map (pFin E) g').val = (GeneralLinearGroup.map (pFin E) g).val
      simp [hg', map_mul, map_inv, pFin_infGL]
    have hinf : ‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ≤ M₂ * a * M₁ * height y * Xn := by
      have e : v ᵥ* g'.val = ((v ᵥ* g.val ᵥ* c.val) ᵥ* (infGL E a y).val) ᵥ* (c⁻¹ : GA E a).val := by
        simp only [hg', Units.val_mul, vecMul_vecMul]
      rw [e]
      calc _ ≤ M₂ * ‖fun i => pInf E (((v ᵥ* g.val ᵥ* c.val) ᵥ* (infGL E a y).val) i)‖ :=
            h₂ c⁻¹ (Set.inv_mem_inv.2 hc) _
        _ ≤ M₂ * ((a * height y) * ‖fun i => pInf E ((v ᵥ* g.val ᵥ* c.val) i)‖) :=
            mul_le_mul_of_nonneg_left (norm_vecMul_infGL_le y _) hM₂.le
        _ ≤ M₂ * ((a * height y) * (M₁ * Xn)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h₁ c hc _) (by positivity)) hM₂.le
        _ = _ := by ring
    set D := (ideleModule E (GeneralLinearGroup.det (infGL E a y)) : ℝ) with hD
    have hDpos : 0 < D := (ideleModule E _).2
    have hdet : (ideleModule E (GeneralLinearGroup.det g') : ℝ) = G * D := by
      have : GeneralLinearGroup.det g' = GeneralLinearGroup.det g * GeneralLinearGroup.det (infGL E a y) := by
        simp only [hg', map_mul, map_inv]
        rw [mul_right_comm (GeneralLinearGroup.det g), mul_inv_cancel_right]
      rw [this, map_mul, Positive.val_mul]
    have hDinv : D⁻¹ ≤ ((a.factorial : ℝ) * height y ^ a) ^ p := by
      have h := ideleModule_det_infGL_le (E := E) y⁻¹
      rw [height_inv] at h
      have hDD : D * (ideleModule E (GeneralLinearGroup.det (infGL E a y⁻¹)) : ℝ) = 1 := by
        rw [hD, ← Positive.val_mul, ← map_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, map_one]
        rfl
      rw [eq_inv_of_mul_eq_one_right hDD] at h
      exact h
    have hq : (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n / (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ≤
        K₀ * height y ^ m * (Xn ^ n / G) := by
      rw [hdet]
      have hXn0 : 0 ≤ Xn := norm_nonneg _
      have hb0 : 0 ≤ M₂ * a * M₁ * height y * Xn := by
        have := hM₁.le; have := hM₂.le; positivity
      have hc0 : 0 ≤ ((a.factorial : ℝ) * height y ^ a) ^ p := by positivity
      calc _ = ‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n * D⁻¹ / G := by ring
        _ ≤ (M₂ * a * M₁ * height y * Xn) ^ n * ((a.factorial : ℝ) * height y ^ a) ^ p / G :=
            div_le_div_of_nonneg_right (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hinf n) hDinv
              (inv_nonneg.2 hDpos.le) (pow_nonneg hb0 _)) hGpos.le
        _ = _ := by rw [hK₀, hm, pow_add, pow_mul]; ring
    have hL' : (fun i => pFin E ((v ᵥ* g'.val) i)) ∈ L := hfin ▸ hξL
    have hF' := hC g' c hc ξ hξ hL'
    rw [eg]
    have hnn : 0 ≤ (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n / (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ^ N :=
      pow_nonneg (div_nonneg (pow_nonneg (norm_nonneg _) _) (ideleModule E _).2.le) _
    calc ‖F (g' * c)‖ ≤ |C| * (‖fun i => pInf E ((v ᵥ* g'.val) i)‖ ^ n /
          (ideleModule E (GeneralLinearGroup.det g') : ℝ)) ^ N :=
          hF'.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hnn)
      _ ≤ |C| * (K₀ * height y ^ m * (Xn ^ n / G)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg (pow_nonneg (norm_nonneg _) _)
            (ideleModule E _).2.le) hq N) (abs_nonneg C)
      _ = _ := by ring
  have hint : Integrable (fun x => ‖k x‖ * height (γ x) ^ (m * N)) ν := hkI (m * N)
  show ‖∫ x, k x * F (g * c * infGL E a (γ x)) ∂ν‖ ≤ I * (|C| * K₀ ^ N) * (Xn ^ n / G) ^ N
  calc ‖∫ x, k x * F (g * c * infGL E a (γ x)) ∂ν‖
      ≤ ∫ x, ‖k x‖ * height (γ x) ^ (m * N) * (|C| * K₀ ^ N * (Xn ^ n / G) ^ N) ∂ν :=
        norm_integral_le_of_norm_le (hint.mul_const _) (.of_forall fun x => by
          rw [norm_mul]
          calc ‖k x‖ * ‖F (g * c * infGL E a (γ x))‖
              ≤ ‖k x‖ * (|C| * K₀ ^ N * height (γ x) ^ (m * N) * (Xn ^ n / G) ^ N) :=
                mul_le_mul_of_nonneg_left (key _) (norm_nonneg _)
            _ = _ := by ring)
    _ = _ := by rw [integral_mul_const, hI]; ring

end GlobalTheory.RapidKernelDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstTwistCharactersEqLadicCharactersAllReadings
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwInputs.isChars_of_sideB : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ChiTOk D cf → GrpSide D → CharSide D cf → ValLL0 D cf → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ i b (ρ : GlobalTheory.Triple.Reading D.ntw i b), GlobalTheory.Triple.IsChars cf art ρ := by
  intro _hCh hGAR D cf Rw low Pq S hL eig θ Bs hT hG _hCS hV _hroots art ha i b ρ
  have hchi := GlobalTheory.TwChiGal.firstTwistCharacter_eq_ladic_heckeCharacter D cf Bs.chiD Bs.chi Bs.eta_eq Bs.ringSpec_normalisedCharacter_eq Bs.del_eq hV art ha i b ρ
  refine ⟨hchi, fun j k hk v => ?_⟩
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hN, u, ϖ, π, hu, hϖ1, hϖ2, hπ, hval, hord⟩ := GlobalTheory.TameGenRep.exists_rep D hG k v
  have hAw : IsPlaceOver (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) := D.nd.plOm.2 _
  have hu0 : (u : D.host.E) ≠ 0 := fun h => hu (by
    rw [show u = 0 from RingOfIntegers.coe_eq_zero_iff.1 h]; exact zero_mem _)
  have hTR : NX.TameRep (D.naut.plGw k v) 1 (D.ntypes.tg k v) u :=
    ⟨_, hAw, D.ntypes.tg_mem k v, ϖ, π, hϖ1, hϖ2, hπ, by simpa using hval⟩
  obtain ⟨c, hc, hcv⟩ := hT k v j u hu0 hTR
  have hxu : IsUnitAt (D.naut.plGw k v) (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) := by
    show Valued.v (((u : D.host.E) : (D.naut.plGw k v).adicCompletion D.host.E)) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hu
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om art ha
    (D.naut.plGw k v) _ hAw ϖ hϖ1 hϖ2 π hπ (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) u hxu
    (by simp [atFin])
  obtain ⟨n, hn⟩ := hchi j
  have hl := GlobalTheory.Triple.Model.notMem_l (X := D.ntw) hk v
  have e1 := hn.loc (Or.inl hl) hσart.symm
  obtain ⟨h1, -, h3, -, h5⟩ := GlobalTheory.GalChar.inertialOrderFifteenChar_auxiliaryPrime_spec (GlobalTheory.Triple.hframe cf) (l := D.ntw.l i)
  have hdel : (cf.delAt (D.ntw.l i)).UnrAt (D.naut.plGw k v) :=
    h5.unr _ (GlobalTheory.GalChar.notMem_of_ne (D.host.g_prime k) h1 (h3 k).symm (D.naut.plGw_over k v))
  rw [GlobalTheory.Triple.blockChar, GlobalTheory.GalChar.block_loc (cf.isEta.unr _) hxu, GlobalTheory.Triple.muBase] at e1
  change _ = ((cf.mu0 j).loc _ _ : ℂ) * ((cf.delAt (D.ntw.l i)).loc _ _ : ℂ) at e1
  simp only [hdel _ hxu, Units.val_one, mul_one] at e1
  have hg2 := (D.host.g_prime k).two_le
  have hgw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hm : ((normV (D.naut.plGw k v) - 1 : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := by
    rw [hN]
    intro h
    apply (D.naut.plGw k v).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := (D.naut.plGw k v).asIdeal.sub_mem hgw h
    rwa [Nat.cast_sub (by omega), Nat.cast_one, sub_sub_cancel] at this
  have hI : ∀ τ ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
      GlobalTheory.GalChar.inQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b) τ ^ (normV (D.naut.plGw k v) - 1) = 1 := by
    intro τ hτ
    rw [hN, GlobalTheory.GalChar.inQ, MonoidHom.comp_apply, ← map_pow, D.ntw.twistCharacterFamily_tame i (j.1 + 1) b k _ hgw hl _ hAw τ hτ, map_one]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by rw [hN]; omega)] at hπ
    apply hϖ2
    have h0 : (ϖ : D.host.E) = 0 := (map_eq_zero_iff _ (algebraMap D.host.E D.nd.Om).injective).1 hπ.symm
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]
    exact zero_mem _
  have hsub : (D.nd.plOm.1 (D.naut.plGw k v)).valuation (σ π / π - D.ntypes.tg k v π / π) < 1 := by
    have e : σ π / π - D.ntypes.tg k v π / π = (σ π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) -
      (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) := by ring
    rw [e]
    exact Valuation.map_sub_lt _ hσval hval
  have e2 := GlobalTheory.TameCharDet.eq_of_tameChar D.host.E D.nd.Om (D.naut.plGw k v) _ hAw _ (D.ntypes.tg_gen k v) _
    (GlobalTheory.GalChar.inQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b)) (hn.cont (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg) _ (by omega) hm hI π _
    hπ0 hπ hord σ hσI hsub
  refine ⟨c, hc, ?_⟩
  rw [GlobalTheory.Triple.Reading.toC_apply, ← GlobalTheory.GalChar.inQ_val, ← e2, GlobalTheory.GalChar.inQ_val, e1]
  exact hcv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicMapExtremalVectorEqPhaseSmulLetters
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section
namespace GlobalTheory.SerIntLetters
open GlobalTheory.AdTh.PhaseMap GlobalTheory.SerLetters


set_option maxHeartbeats 1600000 in
theorem io_eq_phase_smul_harmLetters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 → ∀ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank ≃ FVar D (Wc D i).rank (Vc D i).rank, IsLetters (T.Q.Dw ((i : ℕ) + 1)) lt → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∃ J : VsV D i ℂ →ₗ[ℂ] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) ℂ, (∀ v, J v ∈ HHa (T.Q.Dw ((i : ℕ) + 1)).mult (Vc D i).rank ℂ ComplexEmbedding.conjugate (InPsi T.Q.H) (fun τ j => wtA (κ i) (τ, j))) ∧ (∀ k : Subfield ℂ, (∀ x ∈ T.Q.c.F, x ∈ k) → ∀ v : VsV D i ℂ, (∀ m, AddMonoidAlgebra.coeff (v : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) m ∈ k) → ∀ mo, (J v).coeff mo ∈ k) ∧ ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ v, pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f (R.ioP i (PiTensorProduct.tprod ℂ u) (c0 v)) = ka • stdF R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) f (MvPolynomial.rename lt (J v)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hLaws hL hGrp hFam hMod hThP hTie i hstd u hu c0 hc lt hlt
  obtain ⟨ka, hka, io, hio, hJ⟩ := io_eq_phase_smul_letters D G Pl0 T0 A T R κ v₀ hL hFam hMod hThP hTie i hstd u hu c0 hc
    (⇑lt) (fun ℓ => hlt ℓ)
  let b : Formalism.L2.DIV.VVIdx (lamV D i) → VsV D i ℂ := fun j =>
    GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) (Formalism.L2.DIV.bVV T.Q.c.F (lamV D i) j)
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range b) := fun x _ => by
    obtain ⟨a, rfl⟩ := GlobalTheory.AdTh.CoefExt.exists_coord (inC T.Q.c) (lamV D i) x
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hli : LinearIndependent ℂ b := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank hsp ?_
    rw [Module.finrank_eq_card_basis (Formalism.L2.DIV.bVV ℂ (lamV D i))]
  let e : Formalism.L2.DIV.VVIdx (lamV D i) → MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) ℂ := fun j =>
    MvPolynomial.map (inC T.Q.c) (io (Formalism.L2.DIV.bVV T.Q.c.F (lamV D i) j))
  let J : VsV D i ℂ →ₗ[ℂ] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) ℂ := (Module.Basis.mk hli hsp).constr ℂ e
  have hJv : ∀ a : Formalism.L2.DIV.VVIdx (lamV D i) → ℂ, J (∑ j, a j • b j) = ∑ j, a j • e j := fun a => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, J]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show b j = Module.Basis.mk hli hsp j from (Module.Basis.mk_apply hli hsp j).symm, Module.Basis.constr_basis]
  refine ⟨ka, hka, J, fun v => ?_, fun k hk v hv mo => ?_, fun f hf v => ?_⟩
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdTh.CoefExt.exists_coord (inC T.Q.c) (lamV D i) v
    rw [hJv]
    refine GlobalTheory.PtId.mem_HHa_of_span _ _ _ _ _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    exact GlobalTheory.SerLetters.map_mem_HHa (inC T.Q.c) (GlobalTheory.PtId.mem_HHa_of_span _ _ _ _ _ _ (hio _))
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdTh.CoefExt.exists_coord (inC T.Q.c) (lamV D i) v
    have hF : ∀ x : T.Q.c.F, inC T.Q.c x ∈ k := fun x => hk _ (by rw [show inC T.Q.c x = (x : ℂ) from rfl]; exact x.2)
    let φ : T.Q.c.F →+* k := (inC T.Q.c).codRestrict k hF
    let eK : Formalism.L2.DIV.VVIdx (lamV D i) → Formalism.L2.DIV.Pol k D.what₂.Tau (Vc D i).rank := fun j =>
      MvPolynomial.map φ (Formalism.L2.DIV.bVV T.Q.c.F (lamV D i) j : Formalism.L2.DIV.Pol T.Q.c.F D.what₂.Tau (Vc D i).rank)
    have hmap : ∀ j, MvPolynomial.map k.subtype (eK j) = (b j : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) := fun j => by
      show MvPolynomial.map k.subtype (MvPolynomial.map φ _) = MvPolynomial.map (inC T.Q.c) _
      rw [MvPolynomial.map_map]
      rfl
    have hli' : LinearIndependent ℂ fun j => MvPolynomial.map k.subtype (eK j) := by
      have h2 := hli.map' (Submodule.subtype _) (Submodule.ker_subtype _)
      have e2 : (fun j => MvPolynomial.map k.subtype (eK j)) = (Submodule.subtype _) ∘ b := funext hmap
      rw [e2]
      exact h2
    have hsum : (∑ j, a j • MvPolynomial.map k.subtype (eK j)) =
        ((∑ j, a j • b j : VsV D i ℂ) : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) := by
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, hmap]
    have hcoef : ∀ m, AddMonoidAlgebra.coeff (∑ j, a j • MvPolynomial.map k.subtype (eK j)) m ∈ k.subtype.fieldRange := fun m => by
      rw [hsum]
      exact RingHom.mem_fieldRange.2 ⟨⟨_, hv m⟩, rfl⟩
    have ha : ∀ j, a j ∈ k := fun j => by
      obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.1 (coord_mem_fieldRange k.subtype eK hli' a hcoef j)
      rw [← hy]
      exact y.2
    rw [hJv, MvPolynomial.coeff_sum]
    refine Subfield.sum_mem _ fun j _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    exact Subfield.mul_mem _ (ha j) (by rw [MvPolynomial.coeff_map]; exact hF _)
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdTh.CoefExt.exists_coord (inC T.Q.c) (lamV D i) v
    rw [hJv]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hJ f hf, GlobalTheory.AdTh.PhaseMap.toF_apply, smul_comm]

end GlobalTheory.SerIntLetters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolysReachSmallFieldCoefficientFunctions
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntExpOnto

theorem exists_harm_complex {D : D7} (m n : ℕ) (w : Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m)
    (F : Pol ℂ D.what₂.Tau n) (hF : F ∈ VV ℂ w.lam) :
    ∃ P ∈ harm m w B, harmFn m w B P = coefFn (RingHom.id ℂ) w.lam F := by
  obtain ⟨s, hs⟩ := GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta D m n w B hw hm
  have hs0 : ((s : ℤ) : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
  have key : ∀ u : GLR D n, harmFn m w B (fockGL m w B u (w.delta m)) =
      ((s : ℤ) : ℂ) • Onto.coefLin w.lam (actP w.lam (invTrK (u * B)) (ten fun τ => extremal ℂ n (w.lam τ))) := fun u => by
    funext x
    rw [harmFn_fockGL, hs, Pi.smul_apply, smul_eq_mul]
    congr 1
    change _ = coefFn _ _ _ _
    rw [Onto.coefFn_actP, _root_.mul_inv_rev, mul_assoc]
  have hle : (VV ℂ w.lam).map (Onto.coefLin w.lam) ≤ (harm m w B).map (harmFn m w B) := by
    rw [GlobalTheory.OrbitSpan.VV_eq_span_orbit, harm, Submodule.map_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have h2 := key (invTrK g * B⁻¹)
    rw [inv_mul_cancel_right, Onto.invTrK_invTrK] at h2
    refine (Submodule.smul_mem_iff _ hs0).1 ?_
    beta_reduce
    rw [← h2]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
  exact hle ⟨F, hF, rfl⟩

theorem exists_harm {D : D7} (m n : ℕ) (w : Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m)
    {K : Type} [Field K] [CharZero K] (σ : K →+* ℂ) (F : VV K w.lam) :
    ∃ P ∈ harm m w B, harmFn m w B P = coefFn σ w.lam (F : Pol K D.what₂.Tau n) := by
  obtain ⟨P, hP, e⟩ := exists_harm_complex m n w B hw hm (MvPolynomial.map σ F.1) (GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ _ _ F.2)
  refine ⟨P, hP, e.trans (funext fun x => ?_)⟩
  rw [coefFn, coefFn, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]

theorem onto : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b (F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam), ∃ P ∈ (Y.Z.ρ.B i j b).valSpace, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) := by
  intro _ _ _ D X E Y _ _ i _ j b F
  have hB := Y.Z.good.base i j b
  refine exists_harm _ _ _ _ hB.wt (fun τ => ?_) _ F
  have h1 := hB.sig τ
  have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
  rw [← h1] at h2
  exact h2.le

end GlobalTheory.IntExpOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HoweDualityCompactPairPolynomialFockAllRealPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
namespace GlobalTheory.HoweCompactAlg

theorem mem_of_equivariant : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ (k : K) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r k) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → (∀ g : GlobalTheory.ExportSeries.GLR D n, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ k, r k = g) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ k, U.map (ρ k) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ M : Submodule ℂ (W →ₗ[ℂ] PolF D m n), (∀ ψ ∈ M, ∀ (k : K) (w' : W), ψ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ w')) → (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (Z : Matrix (Fin m) (Fin m) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) Z ∘ₗ ψ ∈ M) → M ≠ ⊥ → ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → φ ∈ M := by
  intro D n m w BS K _ r hU hOnto W _ _ _ ρ hρ M hMeq hMT hM0 φ hφ
  obtain ⟨ψ, hψM, hψ0, hψH⟩ := _root_.GlobalTheory.LowerHarm.lower_to_harmonic D n m w.p W M (fun ψ hψ τ i l _ _ => hMT ψ hψ τ _) hM0
  let S : Submodule ℂ (W →ₗ[ℂ] PolF D m n) :=
    { carrier := {ψ | ψ ∈ M ∧ ∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (ψ w') = 0}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨M.add_mem ha hb, fun w' τ' i l h1 h2 => ?_⟩
        simp [LinearMap.add_apply, map_add (f := _), ha' w' τ' i l h1 h2, hb' w' τ' i l h1 h2]
      zero_mem' := ⟨M.zero_mem, fun w' τ' i l _ _ => by simp⟩
      smul_mem' := by
        rintro c a ⟨ha, ha'⟩
        refine ⟨M.smul_mem c ha, fun w' τ' i l h1 h2 => ?_⟩
        simp [LinearMap.smul_apply, map_smul, ha' w' τ' i l h1 h2] }
  have hS : ∀ φ' : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ' (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ' w')) → (∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (φ' w') = 0) → φ' ∈ S := by
    refine _root_.GlobalTheory.LowestKType.lowestKType_irreducible D n m w BS K r hU hOnto W ρ hρ S (fun ψ' h => hMeq ψ' h.1) (fun ψ' h => h.2) ?_ ?_
    · intro ψ' h τ a b hab
      refine ⟨hMT ψ' h.1 τ _, fun w' => ?_⟩
      exact _root_.GlobalTheory.CompactHarm.fockT_compact_harm D n m w.p (ψ' w') (h.2 w') τ a b hab
    · intro h
      apply hψ0
      have : ψ ∈ S := ⟨hψM, hψH⟩
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
  exact _root_.GlobalTheory.RaiseGen.mem_of_raise D n m w BS K r hU W ρ M (fun φ' h1 h2 => (hS φ' h1 h2).1)
    (fun ψ' h τ i l _ _ => hMT ψ' h τ _) φ hφ

end GlobalTheory.HoweCompactAlg
end

