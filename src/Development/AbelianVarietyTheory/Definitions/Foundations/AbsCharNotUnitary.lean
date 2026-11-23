module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsUnitaryOfOrder
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain nonZeroDivisors

namespace GlobalTheory.Mem.Chr.CharModel

section Norm

variable (F : Type) [Field F] [NumberField F]

def infPart : Ideles F →* (InfiniteAdeleRing F)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

def finPart : Ideles F →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

def logInf (a : (InfiniteAdeleRing F)ˣ) : ℝ :=
  ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log ‖(a : InfiniteAdeleRing F) w‖

theorem inf_ne (a : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) : (a : InfiniteAdeleRing F) w ≠ 0 := by
  intro h
  have h1 : (a : InfiniteAdeleRing F) w * ((a⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w = 1 :=
    congrFun a.mul_inv w
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem logInf_mul (a b : (InfiniteAdeleRing F)ˣ) : logInf F (a * b) = logInf F a + logInf F b := by
  unfold logInf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have : ((a * b : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w =
    (a : InfiniteAdeleRing F) w * (b : InfiniteAdeleRing F) w := rfl
  rw [this, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (inf_ne F a w)) (norm_ne_zero_iff.2 (inf_ne F b w)), mul_add]

theorem logInf_one : logInf F 1 = 0 := by
  have := logInf_mul F 1 1
  rw [mul_one] at this
  linarith

theorem continuous_logInf : Continuous (logInf F) := by
  unfold logInf
  refine continuous_finsetSum _ fun w _ => continuous_const.mul ?_
  refine Continuous.log ?_ fun a => norm_ne_zero_iff.2 (inf_ne F a w)
  have h : Continuous fun x : InfiniteAdeleRing F => x w := continuous_apply w
  exact (h.comp Units.continuous_val).norm

def logFin (t : (FiniteAdeleRing (𝓞 F) F)ˣ) : ℝ :=
  Real.log ((FractionalIdeal.absNorm (GlobalTheory.Idele.idealOf t) : ℚ) : ℝ)

theorem logFin_mul (t s : (FiniteAdeleRing (𝓞 F) F)ˣ) : logFin F (t * s) = logFin F t + logFin F s := by
  have h : ∀ t : (FiniteAdeleRing (𝓞 F) F)ˣ, ((FractionalIdeal.absNorm (GlobalTheory.Idele.idealOf t) : ℚ) : ℝ) ≠ 0 :=
    fun t => by simpa [FractionalIdeal.absNorm_eq_zero_iff] using GlobalTheory.Idele.idealOf_ne_zero t
  unfold logFin
  rw [GlobalTheory.Idele.idealOf_mul, map_mul, Rat.cast_mul, Real.log_mul (h t) (h s)]

theorem logFin_one : logFin F 1 = 0 := by
  have := logFin_mul F 1 1
  rw [mul_one] at this
  linarith

theorem logFin_eventually : ∀ᶠ t in nhds (1 : (FiniteAdeleRing (𝓞 F) F)ˣ), logFin F t = 0 := by
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  have h1 : ∀ᶠ t : (FiniteAdeleRing (𝓞 F) F)ˣ in nhds 1,
      ∀ v, (t : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F :=
    (hO.preimage (Units.continuous_val (M := FiniteAdeleRing (𝓞 F) F))).mem_nhds
      (fun v : HeightOneSpectrum (𝓞 F) => one_mem (v.adicCompletionIntegers F))
  have h2 : ∀ᶠ t in nhds (1 : (FiniteAdeleRing (𝓞 F) F)ˣ),
      ∀ v, ((t⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F :=
    (hO.preimage Units.continuous_coe_inv).mem_nhds fun v => one_mem _
  filter_upwards [h1, h2] with t h1 h2
  have : GlobalTheory.Idele.idealOf t = 1 := by
    rw [← GlobalTheory.Idele.smul_one_eq, GlobalTheory.Idele.smul_eq_self_iff t one_ne_zero]
    intro v
    have e := congrArg Valued.v (GlobalTheory.Idele.idele_apply_mul_inv t v)
    rw [map_mul, map_one] at e
    have a1 : Valued.v ((t : FiniteAdeleRing (𝓞 F) F) v) ≤ 1 := h1 v
    have a2 : Valued.v (((t⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) ≤ 1 := h2 v
    refine le_antisymm a1 ?_
    rw [← e]
    exact mul_le_of_le_one_right' a2
  simp [logFin, this]

def logNorm (a : Ideles F) : ℝ := logInf F (infPart F a) - logFin F (finPart F a)

theorem logNorm_mul (a b : Ideles F) : logNorm F (a * b) = logNorm F a + logNorm F b := by
  unfold logNorm
  rw [map_mul, map_mul, logInf_mul, logFin_mul]
  ring

theorem logInf_principal (x : Fˣ) :
    logInf F (infPart F (diagUnits F x)) = Real.log ((|Algebra.norm ℚ (x : F)| : ℚ) : ℝ) := by
  rw [← InfiniteAdeleRing.coe_norm_eq_abs_norm, InfiniteAdeleRing.norm_def, Real.log_prod]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.log_pow]
    rfl
  · intro w _
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (inf_ne F (infPart F (diagUnits F x)) w))

theorem logNorm_principal (x : Fˣ) : logNorm F (diagUnits F x) = 0 := by
  have h1 : finPart F (diagUnits F x) = FiniteAdeleRing.unitEmbedding (𝓞 F) F x := Units.ext rfl
  unfold logNorm logFin
  rw [h1, GlobalTheory.Idele.idealOf_unitEmbedding, FractionalIdeal.absNorm_span_singleton, sub_eq_zero, logInf_principal]

def absHom (s : ℂ) : Ideles F →* ℂˣ :=
  MonoidHom.mk' (fun a => Units.mk0 (Complex.exp (s * logNorm F a)) (Complex.exp_ne_zero _)) fun a b => by
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0]
    rw [logNorm_mul, ← Complex.exp_add]; push_cast; ring_nf

theorem absHom_val (s : ℂ) (a : Ideles F) : ((absHom F s a : ℂˣ) : ℂ) = Complex.exp (s * logNorm F a) := rfl

theorem continuous_logNorm : Continuous (logNorm F) := by
  let f : Ideles F →* Multiplicative ℝ := MonoidHom.mk' (fun a => Multiplicative.ofAdd (logNorm F a))
    fun a b => by rw [logNorm_mul]; rfl
  have c1 : Continuous (infPart F) := Continuous.units_map _ continuous_fst
  have c2 : Continuous (finPart F) := Continuous.units_map _ continuous_snd
  have h : ∀ᶠ a in nhds (1 : Ideles F), logFin F (finPart F a) = 0 := by
    have := c2.continuousAt (x := 1)
    rw [ContinuousAt, map_one] at this
    exact this.eventually (logFin_eventually F)
  have hf : Continuous f := by
    refine continuous_of_continuousAt_one _ ?_
    refine ContinuousAt.congr (f := fun a => Multiplicative.ofAdd (logInf F (infPart F a)))
      (continuous_ofAdd.comp ((continuous_logInf F).comp c1)).continuousAt ?_
    filter_upwards [h] with a ha
    change _ = Multiplicative.ofAdd (logNorm F a)
    rw [logNorm, ha, sub_zero]
  exact continuous_toAdd.comp hf

theorem continuous_absHom (s : ℂ) : Continuous (absHom F s) := by
  have h : ∀ s : ℂ, Continuous fun a : Ideles F => Complex.exp (s * logNorm F a) := fun s =>
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_logNorm F)))
  refine Units.continuous_iff.2 ⟨h s, ?_⟩
  refine (h (-s)).congr fun a => ?_
  rw [Units.val_inv_eq_inv_val, absHom_val, ← Complex.exp_neg, neg_mul]

def absChar (s : ℂ) : HChar F :=
  ⟨absHom F s, continuous_absHom F s, fun k => Units.ext (by rw [absHom_val, logNorm_principal]; simp)⟩

variable {F}

theorem idealOf_local (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) (n : ℤ)
    (hx : Valued.v (x : v.adicCompletion F) = WithZero.exp (-n)) :
    GlobalTheory.Idele.idealOf (finPart F (localIdele F v x)) = (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ n := by
  have hv : (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot
  refine GlobalTheory.Idele.eq_of_count_eq (GlobalTheory.Idele.idealOf_ne_zero _) (zpow_ne_zero _ hv) fun w => ?_
  rw [GlobalTheory.Idele.count_idealOf, GlobalTheory.Idele.ord_vw]
  by_cases h : w = v
  · subst h
    have : ((finPart F (localIdele F w x) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w = x :=
      Model.localIdele_snd_self F w x
    rw [this, hx, FractionalIdeal.count_zpow_self]; simp
  · have : ((finPart F (localIdele F v x) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w = 1 :=
      Model.localIdele_snd_ne F v w h x
    rw [this, FractionalIdeal.count_zpow, FractionalIdeal.count_maximal_coprime F w (Ne.symm h)]; simp

theorem logNorm_local (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) (n : ℤ)
    (hx : Valued.v (x : v.adicCompletion F) = WithZero.exp (-n)) :
    logNorm F (localIdele F v x) = -(n * Real.log (Ideal.absNorm v.asIdeal : ℕ)) := by
  have h1 : infPart F (localIdele F v x) = 1 := Units.ext rfl
  rw [logNorm, h1, logInf_one, logFin, idealOf_local v x n hx, map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
  push_cast
  rw [Real.log_zpow]; ring

theorem infDiag_parts (k : Fˣ) : infPart F (infDiag k) = infPart F (diagUnits F k) ∧ finPart F (infDiag k) = 1 := by
  classical
  constructor
  · apply Units.ext
    funext w
    rw [infDiag, MonoidHom.finsetProd_apply, map_prod, Units.coe_prod]
    have e : (∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) : (InfiniteAdeleRing F)ˣ) :
        InfiniteAdeleRing F)) w = ∏ u : InfinitePlace F, ((infPart F (((infIdele F u).comp (atInf u)) k) :
          (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w := Finset.prod_apply _ _ _
    rw [e, Finset.prod_eq_single w]
    · exact Model.infIdele_fst_self F w _
    · intro u _ hu
      exact Model.infIdele_fst_ne F u w (Ne.symm hu) _
    · simp
  · rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
    exact Finset.prod_eq_one fun u _ => Units.ext rfl

theorem logNorm_infDiag (k : Fˣ) : logNorm F (infDiag k) = ∑ φ : F →+* ℂ, Real.log ‖φ (k : F)‖ := by
  rw [logNorm, (infDiag_parts k).1, (infDiag_parts k).2, logFin_one, sub_zero, logInf_principal,
    ← Real.log_prod (fun φ _ => norm_ne_zero_iff.2 ((map_ne_zero φ).2 k.ne_zero))]
  congr 1
  have h := congrArg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ (k : F))
  simp only [norm_prod] at h
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => ‖φ (k : F)‖)
    (fun σ : F →ₐ[ℚ] ℂ => ‖σ (k : F)‖) (fun _ => rfl)] at h
  rw [← h]
  simp

theorem absChar_isAbsPow (s : ℝ) : (absChar F s).IsAbsPow s := by
  refine ⟨fun v x hx => Units.ext ?_, fun v => ?_, fun k => ?_⟩
  · change Complex.exp (s * logNorm F (localIdele F v x)) = 1
    rw [logNorm_local v x 0 (by simpa [IsUnitAt] using hx)]; simp
  · change Complex.exp (s * logNorm F (localIdele F v (atFin v (unif v)))) = _
    have h0 : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot
    rw [logNorm_local v _ 1 (unif_spec v), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
      ← Complex.natCast_log]
    congr 1; push_cast; ring
  · change Complex.exp (s * logNorm F (infDiag k)) = _
    rw [logNorm_infDiag, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun φ _ => ?_
    have h0 : 0 < ‖φ (k : F)‖ := norm_pos_iff.2 ((map_ne_zero φ).2 k.ne_zero)
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast h0.ne'), ← Complex.ofReal_log h0.le, mul_comm]

theorem absChar_not_unitary : ¬ (absChar F 1).IsUnitary := by
  intro h
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩
  have h1 := h (localIdele F v (atFin v (unif v)))
  change ‖Complex.exp (1 * logNorm F _)‖ = 1 at h1
  rw [logNorm_local v _ 1 (unif_spec v), one_mul, Complex.norm_exp_ofReal, Real.exp_eq_one_iff] at h1
  have h2 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have := Real.log_pos h2
  push_cast at h1 this
  linarith

end Norm

section Product

variable {F : Type} [Field F] [NumberField F]


open Classical in
def cut (a : FiniteAdeleRing (𝓞 F) F) (T : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ T then a v else 1, by
    refine Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun w hw => ?_)
    by_contra h
    apply hw
    have h' : w ∉ T := h
    simp only [h', if_false]
    exact one_mem _⟩

theorem tendsto_cut (a : FiniteAdeleRing (𝓞 F) F) : Filter.Tendsto (cut a) Filter.atTop (nhds a) := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | a v ∈ v.adicCompletionIntegers F}
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal S)
  let f : Finset (HeightOneSpectrum (𝓞 F)) → P := fun T => ⟨fun v => if v ∈ T then a v else 1, by
    rw [Filter.eventually_principal]
    intro w hw
    by_cases h : w ∈ T
    · simp only [h, if_true]; exact hw
    · simp only [h, if_false]; exact one_mem _⟩
  let a' : P := ⟨fun v => a v, by rw [Filter.eventually_principal]; exact fun w hw => hw⟩
  have hf : Filter.Tendsto f Filter.atTop (nhds a') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change a v = if v ∈ T then a v else 1
    rw [if_pos this]
  exact ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf

theorem prod_local (k : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ((infDiag k * ∏ v ∈ T, localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F) =
      (((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F).1, cut ((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F).2 T) := by
  classical
  refine Prod.ext ?_ ?_
  · change ((infPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) = _
    have e : ∏ v ∈ T, infPart F (localIdele F v (atFin v k)) = 1 := Finset.prod_eq_one (fun v _ => Units.ext rfl)
    rw [map_mul, map_prod, (infDiag_parts k).1, e, mul_one]
    rfl
  · change ((finPart F (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k)) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) = _
    rw [map_mul, (infDiag_parts k).2, one_mul]
    induction T using Finset.induction_on with
    | empty => rw [Finset.prod_empty, map_one]; exact Subtype.ext (funext fun v => by simp [cut]; rfl)
    | insert u T hu ih =>
      rw [Finset.prod_insert hu, map_mul, Units.val_mul, ih]
      refine Subtype.ext (funext fun v => ?_)
      change ((localIdele F u (atFin u k) : Ideles F) : AdeleRing (𝓞 F) F).2 v * (if v ∈ T then _ else 1) =
        if v ∈ insert u T then _ else 1
      by_cases h : v = u
      · subst h
        rw [Model.localIdele_snd_self, if_neg hu, if_pos (Finset.mem_insert_self _ _), mul_one]; rfl
      · rw [Model.localIdele_snd_ne F u v h, one_mul]; simp [h]

theorem tendsto_prod_local (k : Fˣ) :
    Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => infDiag k * ∏ v ∈ T, localIdele F v (atFin v k))
      Filter.atTop (nhds (diagUnits F k)) := by
  have h : ∀ k : Fˣ, Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      ((infDiag k * ∏ v ∈ T, localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F))
      Filter.atTop (nhds ((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F)) := fun k => by
    simp only [prod_local]
    exact tendsto_const_nhds.prodMk_nhds (tendsto_cut _)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h k).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h k⁻¹
  simp only [map_inv, Finset.prod_inv_distrib, ← mul_inv] at h2
  exact h2

theorem locK_unr (χ : HChar F) {v : HeightOneSpectrum (𝓞 F)} (h : χ.UnrAt v) (k : Fˣ) :
    χ.locK v k = χ.val v ^ ordF v k := by
  have hu : IsUnitAt v (atFin v (k * (unif v ^ ordF v k)⁻¹)) := by
    have h2 := unif_spec v
    have hk : Valued.v ((atFin v k : (v.adicCompletion F)ˣ) : v.adicCompletion F) = v.valuation F (k : F) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)
    have h0 : v.valuation F (k : F) ≠ 0 := by simp
    unfold IsUnitAt IsUnifAt at *
    rw [map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h2, hk, ← WithZero.exp_zsmul, ordF]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
    rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
  have h3 : χ.locK v (k * (unif v ^ ordF v k)⁻¹) = 1 := h _ hu
  rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
  exact h3

theorem finite_ordF (k : Fˣ) : {v : HeightOneSpectrum (𝓞 F) | ordF v k ≠ 0}.Finite := by
  have h := Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero (FiniteAdeleRing.unitEmbedding (𝓞 F) F k))
  refine h.subset fun v hv h0 => hv ?_
  have hk : Valued.v (((FiniteAdeleRing.unitEmbedding (𝓞 F) F k : (FiniteAdeleRing (𝓞 F) F)ˣ) :
      FiniteAdeleRing (𝓞 F) F) v) = v.valuation F (k : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : F)
  rw [GlobalTheory.Idele.ord_vw, hk] at h0
  exact h0

theorem productRule (χ : HChar F) : χ.ProductRule := by
  classical
  intro S hS k
  have h1 := (χ.2.1.tendsto _).comp (tendsto_prod_local k)
  rw [χ.2.2 k] at h1
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) h1
  filter_upwards [Filter.eventually_ge_atTop (S ∪ (finite_ordF k).toFinset)] with T hT
  have hST : S ⊆ T := Finset.subset_union_left.trans hT
  change _ = χ.1 (infDiag k * ∏ v ∈ T, localIdele F v (atFin v k))
  rw [map_mul, map_prod, mul_assoc, ← Finset.prod_sdiff hST, mul_comm (∏ v ∈ T \ S, _)]
  refine congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) rfl ?_)
  rw [finprod_cond_eq_prod_of_cond_iff (fun v => χ.val v ^ ordF v k) (p := fun v => v ∉ S) (t := T \ S)]
  · exact Finset.prod_congr rfl fun v hv => (locK_unr χ (hS v (Finset.mem_sdiff.1 hv).2) k).symm
  · intro v hv
    rw [Finset.mem_sdiff]
    refine ⟨fun h => ⟨hT (Finset.mem_union_right _ ?_), h⟩, fun h => h.2⟩
    rw [Set.Finite.mem_toFinset]
    intro h0
    exact hv (by rw [h0, zpow_zero])

end Product

section HostData

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

end HostData

end GlobalTheory.Mem.Chr.CharModel
