module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0071

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFHoriz
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace PFHoriz

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}

def genMap (G : GenFibre v P') : MRing ι ⧸ imageZ v P' →+* G.Φ :=
  Ideal.Quotient.lift _ (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom
    (fun a ha => by rw [← G.ker_x] at ha; exact RingHom.mem_ker.mp ha)

theorem genMap_mk (G : GenFibre v P') (f : MRing ι) :
    genMap G (Ideal.Quotient.mk _ f) = aeval G.x f := rfl

theorem genMap_injective (G : GenFibre v P') : Function.Injective (genMap G) := by
  refine (injective_iff_map_eq_zero (genMap G).toAddMonoidHom).2 fun a ha => ?_
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  change genMap G (Ideal.Quotient.mk _ f) = 0 at ha
  rw [genMap_mk] at ha
  rw [Ideal.Quotient.eq_zero_iff_mem, ← G.ker_x]
  exact RingHom.mem_ker.mpr ha

theorem isFractionRing_genMap (G : GenFibre v P') :
    @IsFractionRing (MRing ι ⧸ imageZ v P') _ G.Φ _ (genMap G).toAlgebra := by
  letI := (genMap G).toAlgebra
  haveI : FaithfulSMul (MRing ι ⧸ imageZ v P') G.Φ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (genMap_injective G)
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨f, g, -, rfl⟩ := G.gen z
  exact ⟨Ideal.Quotient.mk _ f, Ideal.Quotient.mk _ g, rfl⟩

def quotIncl (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    MRing ι ⧸ imageZ v P' →+* FractionRing (MRing ι' ⧸ W) :=
  (algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).comp
    (Ideal.quotientMap W (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom hW.symm.le)

theorem quotIncl_injective (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    Function.Injective (quotIncl W hW) :=
  (IsFractionRing.injective (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).comp
    (Ideal.quotientMap_injective' (H := hW.symm.le) hW.le)

def genAlg (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    G.Φ →+* FractionRing (MRing ι' ⧸ W) :=
  letI := (genMap G).toAlgebra
  haveI := isFractionRing_genMap G
  IsFractionRing.lift (quotIncl_injective W hW)

theorem genAlg_alt (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P')
    (p : Σ k, ι k) :
    genAlg G W hW (G.x p) =
      algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W)) (Ideal.Quotient.mk W (X (v p))) := by
  letI := (genMap G).toAlgebra
  haveI := isFractionRing_genMap G
  have hx : G.x p = algebraMap (MRing ι ⧸ imageZ v P') G.Φ (Ideal.Quotient.mk _ (X p)) := by
    show G.x p = genMap G (Ideal.Quotient.mk _ (X p))
    rw [genMap_mk, aeval_X]
  rw [hx]
  exact (IsFractionRing.lift_algebraMap (quotIncl_injective W hW) _).trans (by
    simp [quotIncl, Ideal.quotientMap_mk])

def xW (W : Ideal (MRing ι')) [W.IsPrime] (q : Σ k', ι' k') : FractionRing (MRing ι' ⧸ W) :=
  algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W)) (Ideal.Quotient.mk W (X q))

theorem aeval_xW (W : Ideal (MRing ι')) [W.IsPrime] (f : MRing ι') :
    aeval (R := ℤ) (xW W) f =
      algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W)) (Ideal.Quotient.mk W f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, eq_intCast (algebraMap ℤ (FractionRing (MRing ι' ⧸ W))) a]
    exact (eq_intCast (((algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).comp
      (Ideal.Quotient.mk W)).comp C) a).symm
  | add p q hp hq =>
    change (aeval (R := ℤ) (xW W)).toRingHom (p + q) = _
    change (aeval (R := ℤ) (xW W)).toRingHom p = _ at hp
    change (aeval (R := ℤ) (xW W)).toRingHom q = _ at hq
    rw [(aeval (R := ℤ) (xW W)).map_add, (Ideal.Quotient.mk W).map_add,
      (algebraMap (MRing ι' ⧸ W) (FractionRing (MRing ι' ⧸ W))).map_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, xW]

theorem ker_aeval_xW (W : Ideal (MRing ι')) [W.IsPrime] :
    RingHom.ker (aeval (R := ℤ) (xW W)) = W := by
  ext f
  rw [RingHom.mem_ker, aeval_xW, map_eq_zero_iff _ (IsFractionRing.injective _ _),
    Ideal.Quotient.eq_zero_iff_mem]

def genFibreOf (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime] (hW : imageZ v W = imageZ v P') :
    GenFibre v W where
  Φ := G.Φ
  Φ' := FractionRing (MRing ι' ⧸ W)
  alg := (genAlg G W hW).toAlgebra
  x := G.x
  x' := xW W
  ker_x := by rw [hW]; exact G.ker_x
  gen := G.gen
  genericFibre_ker_target := by
    refine Eq.trans ?_ (ker_aeval_xW W)
    ext f
    simp only [RingHom.mem_ker, aeval_def, algebraMap_int_eq]
    rw [RingHom.ext_int (algebraMap ℤ (FractionRing (MRing ι' ⧸ W))) (Int.castRingHom _)]
  compat p := (genAlg_alt G W hW p).symm

theorem baseSubst_rename (hκv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι) :
    baseSubst κ G (rename v f) = C (aeval G.x f) := by
  have e : (baseSubst κ G).comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom =
      (C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int (((baseSubst κ G).comp
        (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom).comp C)
        (((C : G.Φ →+* MRingOver G.Φ (fibreIdx ι' κ)).comp
          (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom).comp C)) a
    · have h1 : (v p).1 ∈ Set.range κ := ⟨p.1, (hκv.2.2.1 p).symm⟩
      have h2 : v p ∈ Set.range v := ⟨p, rfl⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, aeval_X]
      rw [baseSubst, eval₂Hom_X', dite_eq_left h1, dite_eq_left h2, hκv.2.1 h2.choose_spec]
  exact RingHom.congr_fun e f

theorem exists_clear (hκv : IsBlockMap κ v) (G : GenFibre v P') (g : MRingOver G.Φ (fibreIdx ι' κ)) :
    ∃ (b : MRing ι) (F : MRing ι'), aeval G.x b ≠ 0 ∧ C (aeval G.x b) * g = baseSubst κ G F := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨f, b, hb, rfl⟩ := G.gen a
    refine ⟨b, rename v f, hb, ?_⟩
    rw [baseSubst_rename hκv, ← C_mul, mul_div_cancel₀ _ hb]
  | add p q hp hq =>
    obtain ⟨b₁, F₁, h₁, e₁⟩ := hp
    obtain ⟨b₂, F₂, h₂, e₂⟩ := hq
    refine ⟨b₁ * b₂, rename v b₂ * F₁ + rename v b₁ * F₂, by rw [map_mul]; exact mul_ne_zero h₁ h₂, ?_⟩
    simp only [map_add (f := _), map_mul, baseSubst_rename hκv, ← e₁, ← e₂]
    ring
  | mul_X p n hp =>
    obtain ⟨b, F, h, e⟩ := hp
    refine ⟨b, F * X ⟨n.1.1, n.2⟩, h, ?_⟩
    rw [map_mul, ← e, mul_assoc]
    congr 2
    rw [baseSubst, eval₂Hom_X', dite_eq_right n.1.2]

theorem ker_eq_map {σ τ Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ']
    (β : MvPolynomial τ ℤ →+* MvPolynomial σ Φ) (y : σ → Φ') (φ : MvPolynomial τ ℤ →+* Φ')
    (W : Ideal (MvPolynomial τ ℤ)) (hφ : RingHom.ker φ = W) (hcomp : ∀ F, aeval y (β F) = φ F)
    (hclear : ∀ g, ∃ c : Φ, c ≠ 0 ∧ ∃ F, C c * g = β F) :
    RingHom.ker (aeval y : MvPolynomial σ Φ →ₐ[Φ] Φ') = Ideal.map β W := by
  apply le_antisymm
  · intro g hg
    obtain ⟨c, hc, F, e⟩ := hclear g
    have hF : F ∈ W := by
      rw [← hφ, RingHom.mem_ker, ← hcomp, ← e, map_mul, RingHom.mem_ker.mp hg, mul_zero]
    have hg' : g = C c⁻¹ * β F := by
      rw [← e, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
    rw [hg']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hF)
  · rw [Ideal.map_le_iff_le_comap]
    intro F hF
    rw [Ideal.mem_comap, RingHom.mem_ker, hcomp, ← RingHom.mem_ker, hφ]
    exact hF

variable {W : Ideal (MRing ι')} [W.IsPrime] (hW : imageZ v W = imageZ v P')

theorem aeval_baseSubst (hκv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι') :
    letI := (genAlg G W hW).toAlgebra
    aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => xW W ⟨q.1.1, q.2⟩) (baseSubst κ G f) =
      aeval (R := ℤ) (xW W) f := by
  letI := (genAlg G W hW).toAlgebra
  have e : (aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => xW W ⟨q.1.1, q.2⟩) :
        MRingOver G.Φ (fibreIdx ι' κ) →ₐ[G.Φ] FractionRing (MRing ι' ⧸ W)).toRingHom.comp (baseSubst κ G) =
      (aeval (R := ℤ) (xW W)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun q => ?_)
    · rw [RingHom.comp_apply, baseSubst, eval₂Hom_C,
        eq_intCast (algebraMap ℤ (MRingOver G.Φ (fibreIdx ι' κ))) a, eq_intCast (C : ℤ →+* MRing ι') a,
        map_intCast, map_intCast]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      rw [baseSubst, eval₂Hom_X']
      by_cases h : q.1 ∈ Set.range κ
      · have h' : q ∈ Set.range v := hκv.2.2.2 q h
        rw [dite_eq_left h, dite_eq_left h', aeval_C, RingHom.algebraMap_toAlgebra, genAlg_alt, h'.choose_spec]
        rfl
      · rw [dite_eq_right h, aeval_X]
  exact RingHom.congr_fun e f

theorem fibreIdeal_genFibreOf (hκv : IsBlockMap κ v) (G : GenFibre v P') :
    fibreIdeal κ (genFibreOf G W hW) = fibreOf κ G W := by
  letI := (genAlg G W hW).toAlgebra
  exact ker_eq_map (baseSubst κ G) (fun q : Σ k : FibreBlock κ, ι' k.1 => xW W ⟨q.1.1, q.2⟩)
    (aeval (R := ℤ) (xW W)).toRingHom W (ker_aeval_xW W) (aeval_baseSubst hW hκv G)
    (fun g => let ⟨_, F, hb, e⟩ := exists_clear hκv G g; ⟨_, hb, F, e⟩)

end PFHoriz

theorem PFHoriz.proof : PFHoriz.Statement := by
  intro I r hPF K _ ι _ K' _ ι' _ κ v P' W d G J L L' N hκv hW hWP hP hJ hL hLL hN
  haveI : W.IsPrime := hW.2.1.1
  have h := hPF K ι K' ι' κ v W d (PFHoriz.genFibreOf G W hWP) J L L' N hκv hW (by rw [hWP]; exact hP)
    hJ hL hLL hN
  rw [PFHoriz.fibreIdeal_genFibreOf hWP hκv G, hWP] at h
  exact h

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsRegLimit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsRegLimit.abs_half_log_le {x ε : ℝ} (hx : x ≠ 0) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |Real.log (x ^ 2 + ε) / 2| ≤ |Real.log x| + |Real.log (x ^ 2 + 1) / 2| := by
  have h2 : 0 < x ^ 2 := lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 hx))
  have hlo : Real.log x ≤ Real.log (x ^ 2 + ε) / 2 := by
    have : Real.log x = Real.log (x ^ 2) / 2 := by rw [Real.log_pow]; push_cast; ring
    rw [this]
    exact div_le_div_of_nonneg_right (Real.log_le_log h2 (by linarith)) (by norm_num)
  have hhi : Real.log (x ^ 2 + ε) / 2 ≤ Real.log (x ^ 2 + 1) / 2 :=
    div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith)) (by norm_num)
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log x), abs_nonneg (Real.log (x ^ 2 + 1) / 2)]
  · linarith [le_abs_self (Real.log (x ^ 2 + 1) / 2), abs_nonneg (Real.log x)]

theorem PtsRegLimit.tendsto_half_log {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun ε : ℝ => Real.log (x ^ 2 + ε) / 2) (𝓝[>] 0) (𝓝 (Real.log x)) := by
  have h2 : x ^ 2 + 0 ≠ 0 := by rw [add_zero]; exact pow_ne_zero 2 hx
  have hc : ContinuousAt (fun ε : ℝ => Real.log (x ^ 2 + ε) / 2) 0 :=
    ((continuousAt_const.add continuousAt_id).log h2).div_const 2
  have hv : Real.log (x ^ 2 + 0) / 2 = Real.log x := by
    rw [add_zero, Real.log_pow]; push_cast; ring
  rw [← hv]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

theorem PtsRegLimit.proof (hInt : PtsIntegrableStatement) (hAbs : PtsAbsIntegrable.Statement) :
    PtsRegLimit.Statement := by
  intro K _ ι _ Q e M E t ht hQ hM hE htQ
  classical
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ
  swap
  · simp only [dif_neg hΨ]
    exact tendsto_const_nhds
  simp only [dif_pos hΨ]
  have hgood := hΨ.choose_spec
  generalize hΨ.choose = Ψ at hgood ⊢
  unfold ptsIntegralAt
  obtain ⟨a, haE, hta⟩ := id ht
  have hfin : ∀ y, (ReciprocityTheory.ChartRestriction.G.Geo.fibre Q Ψ y).Finite := fibreFinite K ι Q e Ψ hQ hgood
  have h1 : (1 : MRing ι) ∉ Q := fun h => hQ.2.1.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)
  have hone : ∀ ε, IsSectionOn Q (regLine E t ht ε) 1 := fun ε =>
    ⟨fun _ => 0, fun k => by rw [regLine_a]; simp, fun m hm k => by
      rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
      subst hm
      simp, h1⟩

  have hsdlog : ∀ (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) y w, sheetDensity Q Ψ (pot M) (fun z => Real.log (B.h z)) y w =
      -sheetDensity Q Ψ (pot M) (logNorm B 1) y w := by
    intro B y w
    by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
    · simp only [sheetDensity, dif_pos hγ, logNorm, map_one, norm_one, one_div, Real.log_inv]
      ring
    · simp only [sheetDensity, dif_neg hγ, neg_zero]
  have hFint : ∀ ε, 0 < ε → Integrable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre Q Ψ y,
      sheetDensity Q Ψ (pot M) (fun z => Real.log ((regLine E t ht ε).h z)) y w) := by
    intro ε hε
    refine (hInt K ι Q e Ψ M (regLine E t ht ε) 1 hQ hgood hM (isSmoothHerm_regLine hE hε)
      (hone ε)).neg.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.neg_apply]
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun w _ => (hsdlog _ y w).symm

  have hJ : IsMultiHomogIdeal (Ideal.span {t}) :=
    ⟨{t}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hta⟩, rfl⟩
  have hJP : ¬ Ideal.span {t} ≤ Q := fun h => htQ (h (Ideal.subset_span rfl))
  have hN : ∀ᵐ y, y ∈ {y : Fin e → ℂ | ∃ z ∈ mcPts Q, z ∈ mcPts (Ideal.span {t}) ∧
      Ψ (segre z) = Fin.cons 1 y}ᶜ := compl_mem_ae_iff.mpr (projB_null Ψ hQ hgood hJ hJP)
  have hpt : ∀ y, y ∈ {y : Fin e → ℂ | ∃ z ∈ mcPts Q, z ∈ mcPts (Ideal.span {t}) ∧
      Ψ (segre z) = Fin.cons 1 y}ᶜ → ∀ w (hγ : ∃ γ, IsSheet Q Ψ y w γ), secNorm E t (hγ.choose y) ≠ 0 := by
    intro y hy w hγ h0
    obtain ⟨-, hev⟩ := hγ.choose_spec
    obtain ⟨-, hmem, hproj⟩ := hev.self_of_nhds
    have hev0 : eval (hγ.choose y) (map (Int.castRingHom ℂ) t) = 0 := by
      rcases div_eq_zero_iff.mp h0 with h | h
      · exact norm_eq_zero.mp h
      · exact absurd h (E.pos _ hmem.1).ne'
    refine hy ⟨hγ.choose y, hmem, ⟨hmem.1, fun f hf => ?_⟩, hproj⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [map_mul, map_mul, hev0, mul_zero]
  have hB1 : ∀ z, |Real.log ((regLine E t ht 1).h z)| = |Real.log (secNorm E t z ^ 2 + 1) / 2| := fun z => by
    rw [log_regLine_h]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre Q Ψ y, |sheetDensity Q Ψ (pot M) (logNorm E t) y w| +
      ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre Q Ψ y, |sheetDensity Q Ψ (pot M) (fun z => Real.log ((regLine E t ht 1).h z)) y w|)
    (eventually_mem_nhdsWithin.mono fun ε hε => (hFint ε hε).aestronglyMeasurable) ?_ ?_ ?_
  ·
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    filter_upwards [hN] with y hy
    rw [Real.norm_eq_abs, finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      ← Finset.sum_add_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
    · simp only [sheetDensity, dif_pos hγ, abs_mul, ← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [hB1, log_regLine_h, logNorm_eq_log_secNorm]
      exact PtsRegLimit.abs_half_log_le (hpt y hy w hγ) hε.1 hε.2.le
    · simp only [sheetDensity, dif_neg hγ, abs_zero, add_zero, le_refl]
  ·
    have hts : IsSectionOn Q E t := ⟨a, haE, hta, htQ⟩
    refine (hAbs K ι Q e Ψ M E t hQ hgood hM hE hts).add ((hAbs K ι Q e Ψ M (regLine E t ht 1) 1 hQ hgood hM
      (isSmoothHerm_regLine hE one_pos) (hone 1)).congr (Eventually.of_forall fun y => ?_))
    exact finsum_mem_congr rfl fun w _ => by rw [hsdlog, abs_neg]
  ·
    filter_upwards [hN] with y hy
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    simp only [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    refine tendsto_finsetSum _ fun w _ => ?_
    by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
    · simp only [sheetDensity, dif_pos hγ]
      refine Tendsto.mul_const _ ?_
      simp only [log_regLine_h, logNorm_eq_log_secNorm]
      exact PtsRegLimit.tendsto_half_log (hpt y hy w hγ)
    · simp only [sheetDensity, dif_neg hγ]
      exact tendsto_const_nhds

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PRatioAlgDep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace RatioAlgebraicDependence

variable {K : Type} {ι : K → Type} {d : ℕ}

def homog (c : ∀ k, ι k) (p : Fin d → Σ k, ι k) (f : MvPolynomial (Fin d) ℤ) : MvPolynomial (Σ k, ι k) ℤ :=
  ∑ m ∈ f.support, C (AddMonoidAlgebra.coeff f m) *
    ∏ j, X (p j) ^ m j * X ⟨(p j).1, c (p j).1⟩ ^ (f.totalDegree - m j)

theorem aeval_homog {F : Type} [Field F] [Algebra ℤ F] (c : ∀ k, ι k) (p : Fin d → Σ k, ι k)
    (f : MvPolynomial (Fin d) ℤ) (w : (Σ k, ι k) → F) (hw : ∀ j, w ⟨(p j).1, c (p j).1⟩ ≠ 0) :
    aeval w (homog c p f) = (∏ j, w ⟨(p j).1, c (p j).1⟩) ^ f.totalDegree *
      aeval (fun j ↦ w (p j) / w ⟨(p j).1, c (p j).1⟩) f := by
  classical
  have hsum : aeval (fun j ↦ w (p j) / w ⟨(p j).1, c (p j).1⟩) f =
      ∑ m ∈ f.support, aeval (fun j ↦ w (p j) / w ⟨(p j).1, c (p j).1⟩) (monomial m (AddMonoidAlgebra.coeff f m)) := by
    conv_lhs => rw [f.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, Finset.mul_sum, homog, map_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hle : ∀ j, m j ≤ f.totalDegree := fun j ↦
    (monomial_le_degreeOf j hm).trans (degreeOf_le_totalDegree f j)
  rw [map_mul, aeval_C, map_prod, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
    ← Finset.prod_pow, mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (hle j)
  rw [map_mul, map_pow, map_pow, aeval_X, aeval_X, div_pow, he, Nat.add_sub_cancel_left, pow_add]
  rw [mul_comm (w ⟨(p j).1, c (p j).1⟩ ^ m j), mul_assoc, mul_div_cancel₀ _ (pow_ne_zero _ (hw j)),
    mul_comm]

end RatioAlgebraicDependence


open RatioAlgebraicDependence in
theorem RatioAlgDep.proof : RatioAlgDep.Statement := by
  intro K _ ι _ Q d c p hQ
  classical
  by_cases hX : ∃ k, (X ⟨k, c k⟩ : MRing ι) ∈ Q
  · obtain ⟨k, hk⟩ := hX
    refine ⟨1, one_ne_zero, fun z hz hzc ↦ absurd ?_ (hzc k)⟩
    simpa using hz _ hk
  push Not at hX
  obtain ⟨Ω, _, y, hy, hbir⟩ := HilbertSamuel.BirationalModelExists.proof K ι Q d hQ
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 ↦ hX k (by
    rw [← hy, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul])
  obtain ⟨_, ⟨hprime, -, -⟩, hhor, hdim⟩ := hQ
  have htr := ConeTrdeg.proof K ι Ω y hbir (fun k ↦ ⟨c k, hc k⟩) (hy ▸ hhor)
  rw [hy] at htr
  have := hprime
  have hA := IntDomainDim.proof (MRing ι ⧸ Q) (CoordinateConeArithVar.algebraMap_injective Q hhor)
  rw [hdim, htr, map_add (f := _), map_natCast] at hA
  have hA' : ((d + Fintype.card K : ℕ) : ℕ∞) =
      Cardinal.toENat (Algebra.trdeg ℤ Ω) + Fintype.card K + 1 := by exact_mod_cast hA
  have hlt : Algebra.trdeg ℤ Ω < d := by
    rw [← Cardinal.toENat_lt_natCast]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, Cardinal.toENat (Algebra.trdeg ℤ Ω) = n := by
      refine ENat.ne_top_iff_exists.mp (fun htop ↦ ?_) |>.imp fun _ h ↦ h.symm
      rw [htop] at hA'
      simp at hA'
    rw [hn] at hA' ⊢
    have : d + Fintype.card K = n + Fintype.card K + 1 := by exact_mod_cast hA'
    exact_mod_cast (by omega : n < d)
  have hdep : ¬ AlgebraicIndependent ℤ (fun j : Fin d ↦ y (p j) / y ⟨(p j).1, c (p j).1⟩) :=
    fun hind ↦ by
      have h := hind.cardinalMk_le_trdeg
      rw [Cardinal.mk_fin] at h
      exact absurd hlt (not_lt.2 h)
  rw [algebraicIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨f, hf0, hfne⟩ := hdep

  have hH : homog c p f ∈ Q := by
    rw [← hy, mCoordIdeal, RingHom.mem_ker]
    set L := FractionRing (MvPolynomial K Ω)
    let φ : MvPolynomial K Ω →ₐ[ℤ] L :=
      { algebraMap (MvPolynomial K Ω) L with
        commutes' := fun n ↦ by simp }
    have hφ : Function.Injective φ := fun a b h ↦ IsFractionRing.injective (MvPolynomial K Ω) L h
    have hw : ∀ q : Σ k, ι k, y q ≠ 0 → φ (C (y q) * X q.1) ≠ 0 := fun q hq ↦ by
      rw [Ne, ← map_zero φ, hφ.eq_iff]
      exact mul_ne_zero (by rwa [Ne, C_eq_zero]) (X_ne_zero _)
    have hrat : ∀ j, φ (C (y (p j)) * X (p j).1) / φ (C (y ⟨(p j).1, c (p j).1⟩) * X (p j).1) =
        φ (C (y (p j) / y ⟨(p j).1, c (p j).1⟩)) := fun j ↦ by
      rw [div_eq_iff (hw _ (hc _)), ← map_mul, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ (hc _)]
    refine hφ ?_
    rw [map_zero, mConeMap, comp_aeval_apply, aeval_homog c p f _ (fun j ↦ hw _ (hc _))]
    simp only [hrat]
    let ψ : Ω →ₐ[ℤ] L := φ.comp (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial K Ω))
    have key : (aeval fun j ↦ φ (C (y (p j) / y ⟨(p j).1, c (p j).1⟩))) f =
        ψ (aeval (fun j ↦ y (p j) / y ⟨(p j).1, c (p j).1⟩) f) := by
      rw [comp_aeval_apply]
      rfl
    rw [key, hf0, map_zero, mul_zero]
  refine ⟨f, hfne, fun z hz hzc ↦ ?_⟩
  have h1 := hz _ hH
  rw [eval_map, ← algebraMap_int_eq, ← aeval_def, aeval_homog c p f z (fun j ↦ hzc _)] at h1
  rw [eval_map, ← algebraMap_int_eq, ← aeval_def]
  exact (mul_eq_zero.1 h1).resolve_left
    (pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun j _ ↦ hzc _))

end GroundTheory.Heights₂.Heights.Inter
end
end

