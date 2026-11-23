module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFactsAlt
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwistSatHolds
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0227

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFacts
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

private theorem symm_eq_mk {E : Type} [Field E] [NumberField E] [IsCMField E]
    (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w)
    (w : InfinitePlace (maximalRealSubfield E)) :
    (IsCMField.equivInfinitePlace E).symm w = InfinitePlace.mk (emb w).1 := by
  rw [Equiv.symm_apply_eq, IsCMField.equivInfinitePlace_apply, InfinitePlace.comap_mk, (emb w).2,
    InfinitePlace.mk_embedding]

private theorem logNorm_diag {E : Type} [Field E] [NumberField E] [IsCMField E] (k : Eˣ) :
    GlobalTheory.Mem.Chr.CharModel.logNorm E (infDiag k) = ∑ v : InfinitePlace E, 2 * Real.log (v (k : E)) := by
  have hp : ∀ v : InfinitePlace E, v (k : E) ≠ 0 := fun v => by simp
  have h := InfinitePlace.prod_eq_abs_norm (k : E)
  change GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.infDiag k) = _
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm, (GlobalTheory.Mem.Chr.CharModel.infDiag_parts k).1,
    (GlobalTheory.Mem.Chr.CharModel.infDiag_parts k).2, GlobalTheory.Mem.Chr.CharModel.logFin_one, sub_zero,
    GlobalTheory.Mem.Chr.CharModel.logInf_principal, ← h, Real.log_prod (fun v _ => pow_ne_zero _ (hp v))]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Real.log_pow, InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v))]
  norm_num

theorem UpperTheory.Gal.TP.Chr.absFacts :
    UpperTheory.Gal.TP.Chr.AbsFacts := by
  intro E _ _ _ emb z
  refine ⟨fun w => ⟨DiscreteGroups.T1.G.absC_unrAt z w, ?_⟩, fun k => ?_⟩
  · simpa [Formalism.UG.qV, Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply,
      Submodule.cardQuot_apply] using DiscreteGroups.T1.G.absC_val z w
  ·
    change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E (infDiag k)) = _
    rw [logNorm_diag, ← (IsCMField.equivInfinitePlace E).symm.sum_comp, Complex.ofReal_sum, Finset.mul_sum,
      Complex.exp_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    have h0 : 0 < ‖(emb w).1 (k : E)‖ := norm_pos_iff.2 ((map_ne_zero _).2 k.ne_zero)
    rw [symm_eq_mk emb w, InfinitePlace.apply, Complex.cpow_def_of_ne_zero (by exact_mod_cast h0.ne'),
      ← Complex.ofReal_log h0.le]
    congr 1
    push_cast
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ChrExPf
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

noncomputable section

namespace UpperTheory.Gal.TP.Chr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private def psi (μ : HChar E) (k : ℕ) (s : ℤ) : HChar E := μ ^ k * Model.absC E ((s : ℂ) / 2)

private theorem hpow_apply (μ : HChar E) (k : ℕ) (x) : (μ ^ k).1 x = μ.1 x ^ k := by
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

private theorem hpow_loc (μ : HChar E) (k : ℕ) (w) (x) : (μ ^ k).loc w x = μ.loc w x ^ k :=
  hpow_apply μ k _

private theorem hpow_inf (μ : HChar E) (k : ℕ) (x) : (μ ^ k).inf x = μ.inf x ^ k :=
  hpow_apply μ k _

private theorem hpow_val (μ : HChar E) (k : ℕ) (w) : (μ ^ k).val w = μ.val w ^ k :=
  hpow_apply μ k _

private theorem lc_pow (χ : Chr (maximalRealSubfield E) E) (k : ℕ) (w : HeightOneSpectrum (𝓞 E)) (x) :
    locChar (χ ^ k) w x = locChar χ w x ^ k := by
  show Circle.toUnits ((χ ^ k) (locIdele _ w x)) = Circle.toUnits (χ (locIdele _ w x)) ^ k
  rw [MonoidHom.pow_apply, map_pow]

private theorem typ_term (z : ℂ) (hz : z ≠ 0) (a b : ℤ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (a - b) * ((‖z‖ : ℝ) : ℂ) ^ (a + b) = z ^ a * (starRingEnd ℂ z) ^ b := by
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  have hc : starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 / z := by
    rw [eq_div_iff hz, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have h2 : (((‖z‖ : ℝ) : ℂ) ^ 2) ^ b = (((‖z‖ : ℝ) : ℂ) ^ b) ^ 2 := by
    rw [← zpow_natCast, ← zpow_natCast, zpow_comm]
  have hA : z ^ a ≠ 0 := zpow_ne_zero _ hz
  have hB : z ^ b ≠ 0 := zpow_ne_zero _ hz
  have hC : ((‖z‖ : ℝ) : ℂ) ^ a ≠ 0 := zpow_ne_zero _ hn
  have hD : ((‖z‖ : ℝ) : ℂ) ^ b ≠ 0 := zpow_ne_zero _ hn
  rw [hc, div_zpow, div_zpow, zpow_sub₀ hz, zpow_sub₀ hn, zpow_add₀ hn, h2]
  field_simp

private theorem inf_psi (hAb : AbsFacts) (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w)
    (μ : HChar E) (m : InfinitePlace (maximalRealSubfield E) → ℤ) (hμ : InfExp emb μ m) (k : ℕ) (s : ℤ) (x : Eˣ) :
    (((psi μ k s).inf x : ℂˣ) : ℂ) = ∏ w, ((emb w).1 (x : E) / ‖(emb w).1 (x : E)‖) ^ ((k : ℤ) * m w) *
      ((‖(emb w).1 (x : E)‖ : ℝ) : ℂ) ^ s := by
  rw [psi, HChar.inf_mul, Units.val_mul, hpow_inf, Units.val_pow_eq_pow_val, hμ x, (hAb E emb _).2 x,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h2 : (2 : ℂ) * ((s : ℂ) / 2) = s := by ring
  rw [h2, Complex.cpow_intCast, mul_comm (k : ℤ), zpow_mul, zpow_natCast]

private theorem exps {k : ℕ} {s m : ℤ} (hev : Even ((k : ℤ) + s)) (hm : Odd m) :
    ∃ a b : ℤ, (s + k * m) / 2 = a ∧ (s - k * m) / 2 = b ∧ a + b = s ∧ a - b = k * m := by
  obtain ⟨r, hr⟩ := hev
  obtain ⟨t, rfl⟩ := hm
  refine ⟨r + k * t, r - k * t - k, ?_, ?_, ?_, ?_⟩
  · rw [show s + k * (2 * t + 1) = 2 * (r + k * t) by linear_combination hr,
      Int.mul_ediv_cancel_left _ two_ne_zero]
  · rw [show s - k * (2 * t + 1) = 2 * (r - k * t - k) by linear_combination hr,
      Int.mul_ediv_cancel_left _ two_ne_zero]
  · linear_combination -hr
  · ring

end UpperTheory.Gal.TP.Chr

theorem UpperTheory.Gal.TP.Chr.chrEx :
    UpperTheory.Gal.TP.Chr.MuEmb → UpperTheory.Gal.TP.Chr.ReadEx → UpperTheory.Gal.TP.Chr.ReadLoc → UpperTheory.Gal.TP.Chr.ReadRes → UpperTheory.Gal.TP.Chr.ReadExp → UpperTheory.Gal.TP.Chr.AbsFacts → UpperTheory.Gal.TP.Chr.TypProd → UpperTheory.Gal.TP.Chr.ExpInj → UpperTheory.Gal.TP.Chr.ChrEx := by
  intro hMu hRE hRL hRR hRX hAb hTP hEI E _ _ _ hun emb w₀ m hm
  have hloc (α β : HChar E) (w : HeightOneSpectrum (𝓞 E)) (x) :
      (α * β).loc w x = α.loc w x * β.loc w x := by
    rfl
  obtain ⟨μ, hμu, hμq, hμi, hμ0⟩ := hMu E hun emb w₀ m hm
  obtain ⟨χ, hr, hH⟩ := hRE E μ hμu
  have hl := hRL E μ χ hr
  have hres := hRR E μ χ hr hμq
  have hexp := hRX E emb μ χ m hr hμi
  have hval : ∀ w, val χ w = μ.val w := fun w => by
    show locChar χ w (atFin w (unif w)) = μ.loc w (atFin w (unif w))
    rw [hl]
  refine ⟨χ, psi μ, fun x hx => ?_, fun k => ⟨⟨hH.1.pow k, fun x => ?_⟩, fun z hz => ?_, fun j hj a => ?_⟩,
    fun k s w => ⟨⟨fun h x hx => ?_, fun h x hx => ?_⟩, ?_⟩, fun k s hev x _ => ?_, fun k k' s s' h => ?_⟩
  · rw [hl]
    exact hμ0 x hx
  · rw [MonoidHom.pow_apply, hH.2 x, one_pow]
  · rw [MonoidHom.pow_apply, Circle.coe_pow, hexp z hz, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    beta_reduce
    rw [mul_comm (k : ℤ), zpow_mul, zpow_natCast]
  · rw [MonoidHom.pow_apply, Circle.coe_pow, hres a]
    split_ifs with h
    · simp
    · rw [pow_one, neg_one_pow_eq_pow_mod_two, ← hj, ← neg_one_pow_eq_pow_mod_two]
  · have h1 : (psi μ k s).loc w x = 1 := h x hx
    rw [psi, hloc, hpow_loc, ((hAb E emb _).1 w).1 x hx, mul_one] at h1
    rw [lc_pow, hl]
    exact h1
  · have h1 : locChar (χ ^ k) w x = 1 := h x hx
    rw [lc_pow, hl] at h1
    rw [psi, hloc, hpow_loc, ((hAb E emb _).1 w).1 x hx, mul_one]
    exact h1
  · rw [psi, HChar.val_mul, Units.val_mul, hpow_val, Units.val_pow_eq_pow_val, ((hAb E emb _).1 w).2, hval, neg_div]
  · rw [hTP E emb _ _ (x : E), inf_psi hAb emb μ m hμi]
    refine Finset.prod_congr rfl fun w _ => ?_
    obtain ⟨a, b, ha, hb, h1, h2⟩ := exps hev (hm w)
    have hz : (emb w).1 (x : E) ≠ 0 := (map_ne_zero (emb w).1).2 x.ne_zero
    beta_reduce
    rw [ha, hb, ← typ_term _ hz a b, h1, h2]
  · have h1 := hEI E emb (fun w => k * m w) (fun w => k' * m w) s s' fun x => by
      rw [← inf_psi hAb emb μ m hμi k s x, ← inf_psi hAb emb μ m hμi k' s' x, h]
    obtain ⟨w⟩ : Nonempty (InfinitePlace (maximalRealSubfield E)) := inferInstance
    have h3 : (k : ℤ) * m w = k' * m w := congrFun h1 w
    have hm0 : m w ≠ 0 := fun h0 => by simpa [h0] using hm w
    exact_mod_cast mul_right_cancel₀ hm0 h3

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ExpInj
section
open NumberField IsDedekindDomain GlobalTheory.AdelicU

namespace UpperTheory.Gal.TP.Chr

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private lemma exists_ext (τ : E →+* ℂ) :
    ∃ e : (InfinitePlace.mk τ).Completion → ℂ, Continuous e ∧ Function.Surjective e ∧
      ∀ x : E, e (algebraMap E _ x) = τ x := by
  have hs := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex
    (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
  have hc : Continuous (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk τ)) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous
  have hv : ∀ x : E, InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk τ)
      (algebraMap E _ x) = (InfinitePlace.mk τ).embedding x := fun x => by
    simpa [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply] using
      InfinitePlace.Completion.extensionEmbedding_coe _ (WithAbs.toAbs _ x)
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · exact ⟨_, hc, hs, fun x => by rw [hv, h]⟩
  · refine ⟨fun z => starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding _ z),
      Complex.continuous_conj.comp hc, fun y => ?_, fun x => ?_⟩
    · obtain ⟨z, hz⟩ := hs (starRingEnd ℂ y)
      exact ⟨z, by simp [hz]⟩
    · simp only [hv, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

private lemma dense_emb (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w) :
    DenseRange (fun (x : E) (w : InfinitePlace (maximalRealSubfield E)) => (emb w).1 x) := by
  classical
  have key : ∀ w, (InfinitePlace.mk (emb w).1).comap (algebraMap (maximalRealSubfield E) E) = w := by
    intro w
    rw [InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]
  have hinj : ∀ w w', InfinitePlace.mk (emb w).1 = InfinitePlace.mk (emb w').1 → w = w' := by
    intro w w' h
    rw [← key w, ← key w', h]
  choose e hc hs he using fun w => exists_ext (emb w).1
  let T : (∀ v : InfinitePlace E, v.Completion) → (∀ _ : InfinitePlace (maximalRealSubfield E), ℂ) :=
    fun f w => e w (f (InfinitePlace.mk (emb w).1))
  have hT : Continuous T := continuous_pi fun w => (hc w).comp (continuous_apply _)
  have hTs : Function.Surjective T := by
    intro y
    choose g hg using fun w => hs w (y w)
    have hcast : ∀ w w' (h : InfinitePlace.mk (emb w').1 = InfinitePlace.mk (emb w).1),
        (h ▸ g w' : (InfinitePlace.mk (emb w).1).Completion) = g w := by
      intro w w' h
      obtain rfl := hinj _ _ h
      rfl
    refine ⟨fun v => if h : ∃ w, InfinitePlace.mk (emb w).1 = v then h.choose_spec ▸ g h.choose else 0, ?_⟩
    funext w
    have hex : ∃ w', InfinitePlace.mk (emb w').1 = InfinitePlace.mk (emb w).1 := ⟨w, rfl⟩
    simp only [T, dif_pos hex]
    rw [hcast w _ hex.choose_spec, hg]
  have hd := hTs.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hT
  convert hd using 1
  funext x w
  exact (he w x).symm

end

theorem expInj : ExpInj := by
  intro E _ _ _ emb m m' s s' h
  classical
  funext w₀
  let F : (InfinitePlace (maximalRealSubfield E) → ℤ) → ℤ →
      (InfinitePlace (maximalRealSubfield E) → ℂ) → ℂ :=
    fun n t y => ∏ w, (y w / ‖y w‖) ^ n w * ((‖y w‖ : ℝ) : ℂ) ^ t
  let U : Set (InfinitePlace (maximalRealSubfield E) → ℂ) := {y | ∀ w, y w ≠ 0}
  have hU : IsOpen U := by
    simp only [U, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (continuous_apply w) continuous_const
  have hcont : ∀ n t, ContinuousOn (F n t) U := by
    intro n t
    refine continuousOn_finsetProd _ fun w _ => ?_
    have h1 : Continuous fun y : InfinitePlace (maximalRealSubfield E) → ℂ => y w := continuous_apply w
    have h2 : Continuous fun y : InfinitePlace (maximalRealSubfield E) → ℂ => ((‖y w‖ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp h1.norm
    have hne : ∀ y ∈ U, ((‖y w‖ : ℝ) : ℂ) ≠ 0 := fun y hy => by
      simpa using hy w
    refine ContinuousOn.mul (ContinuousOn.zpow₀ (h1.continuousOn.div h2.continuousOn hne) _
      fun y hy => Or.inl (div_ne_zero (hy w) (hne y hy))) (ContinuousOn.zpow₀ h2.continuousOn _
      fun y hy => Or.inl (hne y hy))
  have hEq : ∀ y ∈ U, F m s y = F m' s' y := by
    intro y hy
    by_contra hne
    have hop := ((hcont m s).sub (hcont m' s')).isOpen_inter_preimage hU
      (isOpen_compl_singleton (x := (0 : ℂ)))
    obtain ⟨x, hxU, hx⟩ := (dense_emb emb).exists_mem_open hop
      ⟨y, hy, fun h0 => hne (sub_eq_zero.1 h0)⟩
    have hx0 : x ≠ 0 := fun h0 => hxU w₀ (by simp [h0])
    exact hx (sub_eq_zero.2 (h (Units.mk0 x hx0)))
  have hF : ∀ n t (θ : ℝ), F n t (Function.update (1 : InfinitePlace (maximalRealSubfield E) → ℂ) w₀ (Complex.exp (θ * Complex.I))) =
      Complex.exp (θ * Complex.I) ^ n w₀ := by
    intro n t θ
    simp only [F]
    rw [Finset.prod_eq_single w₀]
    · simp [Complex.norm_exp_ofReal_mul_I]
    · intro w _ hw
      simp [Function.update_of_ne hw]
    · simp
  have hUy : ∀ θ : ℝ, Function.update (1 : InfinitePlace (maximalRealSubfield E) → ℂ) w₀ (Complex.exp (θ * Complex.I)) ∈ U := by
    intro θ w
    by_cases hw : w = w₀
    · subst hw; simp [Complex.exp_ne_zero]
    · simp [Function.update_of_ne hw]
  by_contra hne
  have hd0 : ((m w₀ - m' w₀ : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.2 hne
  set θ : ℝ := Real.pi / ((m w₀ - m' w₀ : ℤ) : ℝ) with hθ
  have h1 := hEq _ (hUy θ)
  rw [hF, hF] at h1
  have h2 : Complex.exp (θ * Complex.I) ^ (m w₀ - m' w₀) = 1 := by
    rw [zpow_sub₀ (Complex.exp_ne_zero _), h1, div_self (zpow_ne_zero _ (Complex.exp_ne_zero _))]
  rw [← Complex.exp_int_mul] at h2
  have h3 : ((m w₀ - m' w₀ : ℤ) : ℂ) * (θ * Complex.I) = Real.pi * Complex.I := by
    have : ((m w₀ - m' w₀ : ℤ) : ℂ) * (θ : ℂ) = Real.pi := by
      have : ((m w₀ - m' w₀ : ℤ) : ℝ) * θ = Real.pi := by
        rw [hθ]; field_simp
      exact_mod_cast this
    rw [← mul_assoc, this]
  rw [h3, Complex.exp_pi_mul_I] at h2
  norm_num at h2

end UpperTheory.Gal.TP.Chr
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ReadEx
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

set_option maxHeartbeats 400000 in
theorem UpperTheory.Gal.TP.Chr.readEx :
    UpperTheory.Gal.TP.Chr.ReadEx := by
  intro E _ _ _ μ hU
  let e := GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)
  let f : (AE (↥(maximalRealSubfield E)) E)ˣ →* (AdeleRing (𝓞 E) E)ˣ := Units.map (e : _ →* _)
  refine ⟨{ toFun := fun z => ⟨((μ.1 (f z) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hU (f z))⟩,
            map_one' := ?_, map_mul' := ?_ }, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp
  · intro x y
    apply Subtype.ext
    simp only [map_mul, Units.val_mul]
    rfl
  · intro z
    rfl
  · have hf : Continuous f := by
      show Continuous (Units.map (e : AE (↥(maximalRealSubfield E)) E →* AdeleRing (𝓞 E) E))
      exact Continuous.units_map _ (GlobalTheory.UnitaryHeckeBaseChange.continuous_toAdele _ E)
    have hμc : Continuous (μ.1 : Ideles E → ℂˣ) := μ.2.1
    refine continuous_induced_rng.2 ?_
    exact Units.continuous_val.comp (hμc.comp hf)
  · intro x
    apply Subtype.ext
    show ((μ.1 (f _) : ℂˣ) : ℂ) = 1
    rw [show f _ = diagUnits E x from Units.ext ?_, μ.2.2 x]
    · rfl
    · exact GlobalTheory.UnitaryHeckeBaseChange.toAdele_incA (x : E)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ReadExp
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.TP.Chr

private theorem exists_read {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) :
    ∃ ρ : (InfinitePlace.mk φ).Completion →+* ℂ, Continuous ρ ∧
      ∀ x : E, ρ (algebraMap E (InfinitePlace.mk φ).Completion x) = φ x := by
  have hc := (InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk φ)).continuous
  have he : ∀ x : E, InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ)
      (algebraMap E (InfinitePlace.mk φ).Completion x) = (InfinitePlace.mk φ).embedding x := fun x =>
    by
      rw [InfinitePlace.Completion.algebraMap_apply]
      exact InfinitePlace.Completion.extensionEmbedding_coe (InfinitePlace.mk φ) (WithAbs.toAbs _ x)
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · exact ⟨_, hc, fun x => (he x).trans (by rw [h])⟩
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ)),
      Complex.continuous_conj.comp hc, fun x => ?_⟩
    rw [RingHom.comp_apply, he, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

private theorem inf_formula {E ι : Type} [Field E] [NumberField E] [Fintype ι] (μ : HChar E) (φ : ι → E →+* ℂ)
    (m : ι → ℤ) (ρ : ∀ i, (InfinitePlace.mk (φ i)).Completion →+* ℂ) (hc : ∀ i, Continuous (ρ i))
    (hρ : ∀ i x, ρ i (algebraMap E _ x) = φ i x)
    (h : ∀ k : Eˣ, ((μ.inf k : ℂˣ) : ℂ) = ∏ i, (φ i (k : E) / ‖φ i (k : E)‖) ^ m i)
    (y : (InfiniteAdeleRing E)ˣ) :
    ((μ.1 (GlobalTheory.CompanionTheory.HeckeFin.infIdele E y) : ℂˣ) : ℂ) =
      ∏ i, (ρ i ((y : InfiniteAdeleRing E) (InfinitePlace.mk (φ i))) /
        ‖ρ i ((y : InfiniteAdeleRing E) (InfinitePlace.mk (φ i)))‖) ^ m i := by
  have hne : ∀ (i) (u : (InfiniteAdeleRing E)ˣ), ρ i ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ i))) ≠ 0 := by
    intro i u e
    have h1 : (u : InfiniteAdeleRing E) (InfinitePlace.mk (φ i)) *
        ((u⁻¹ : (InfiniteAdeleRing E)ˣ) : InfiniteAdeleRing E) (InfinitePlace.mk (φ i)) = 1 :=
      congrFun u.mul_inv (InfinitePlace.mk (φ i))
    have h2 := congrArg (ρ i) h1
    rw [map_mul, map_one, e, zero_mul] at h2
    exact zero_ne_one h2
  have hci : ∀ i, Continuous fun u : (InfiniteAdeleRing E)ˣ => ρ i ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ i))) :=
    fun i => (hc i).comp ((continuous_apply _).comp Units.continuous_val)
  have hL : Continuous fun u : (InfiniteAdeleRing E)ˣ => ((μ.1 (GlobalTheory.CompanionTheory.HeckeFin.infIdele E u) : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (μ.2.1.comp (GlobalTheory.CompanionTheory.HeckeFin.continuous_infIdele E))
  have hR : Continuous fun u : (InfiniteAdeleRing E)ˣ => ∏ i, (ρ i ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ i))) /
      ‖ρ i ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ i)))‖) ^ m i := by
    refine continuous_finsetProd _ fun i _ => ?_
    refine Continuous.zpow₀ ((hci i).div (Complex.continuous_ofReal.comp (hci i).norm) fun u => ?_) _ fun u => Or.inl ?_
    · exact Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne i u))
    · exact div_ne_zero (hne i u) (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne i u)))
  refine congrFun ((GlobalTheory.CompanionTheory.HeckeFin.denseRange_units E).equalizer hL hR (funext fun k => ?_)) y
  have e1 : GlobalTheory.CompanionTheory.HeckeFin.infIdele E (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) = infDiag k := by
    classical
    refine Units.ext ?_
    rw [infDiag, MonoidHom.finsetProd_apply, Units.coe_prod]
    let p1 : AdeleRing (𝓞 E) E →+* InfiniteAdeleRing E := RingHom.fst _ _
    let p2 : AdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E := RingHom.snd _ _
    refine Prod.ext ?_ ?_
    · change _ = p1 _
      rw [map_prod]
      change _ = ∏ w : InfinitePlace E, Pi.mulSingle w (algebraMap E w.Completion (k : E))
      exact (Finset.univ_prod_mulSingle _).symm
    · change _ = p2 _
      rw [map_prod]
      exact (Finset.prod_eq_one fun _ _ => rfl).symm
  simp only [Function.comp_apply]
  rw [e1]
  refine (h k).trans (Finset.prod_congr rfl fun i _ => ?_)
  have e2 : ρ i (((Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k : (InfiniteAdeleRing E)ˣ) : InfiniteAdeleRing E)
      (InfinitePlace.mk (φ i))) = φ i (k : E) := hρ i k
  rw [e2]

private theorem piInf_read {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {w : InfinitePlace F} (τ : EmbOver E w) (ρ : (InfinitePlace.mk τ.1).Completion →+* ℂ) (hc : Continuous ρ)
    (hρ : ∀ x, ρ (algebraMap E _ x) = τ.1 x) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piInf τ z = ρ ((GlobalTheory.UnitaryHeckeBaseChange.toAdele F E z).1 (InfinitePlace.mk τ.1)) := by
  have key : (fun b : InfiniteAdeleRing F => InfinitePlace.Completion.extensionEmbedding w (b w)) =
      fun b => ρ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E b (InfinitePlace.mk τ.1)) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
      ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply _))
      (hc.comp ((continuous_apply _).comp (GlobalTheory.UnitaryHeckeBaseChange.continuous_infiniteAdeleMap F E))) (funext fun x => ?_)
    have h1 : InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion x) = w.embedding x :=
      by
        rw [InfinitePlace.Completion.algebraMap_apply]
        exact InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)
    have h2 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E (algebraMap F _ x) (InfinitePlace.mk τ.1) =
        algebraMap E (InfinitePlace.mk τ.1).Completion (algebraMap F E x) :=
      congrFun (congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap F E x)) _
    simp only [Function.comp_apply]
    change InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion x) = ρ _
    rw [h1, h2, hρ]
    exact (RingHom.congr_fun τ.2 x).symm
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    exact (map_zero ρ).symm
  | add x y hx hy =>
    rw [map_add (f := _), hx, hy, map_add (f := _), ← map_add (f := _)]
    rfl
  | tmul a e =>
    rw [GlobalTheory.UnitaryHeckeBaseChange.toAdele_tmul]
    have h3 : InfinitePlace.Completion.extensionEmbedding w (a.1 w) =
        ρ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E a.1 (InfinitePlace.mk τ.1)) := congrFun key a.1
    have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * algebraMap E (AdeleRing (𝓞 E) E) e).1 (InfinitePlace.mk τ.1) =
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E a.1 (InfinitePlace.mk τ.1) *
          algebraMap E (InfinitePlace.mk τ.1).Completion e := rfl
    rw [h4, map_mul, ← h3, hρ]
    rfl

theorem readExp : ReadExp := by
  intro E _ _ _ emb μ χ m hR hI z hz
  have hcm := GlobalTheory.GalOfCusp.isCMExt_real E
  set x : Ideles E := Units.map (GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv hcm).toRingHom.toMonoidHom z with hx
  have hx1 : (x : AdeleRing (𝓞 E) E) = GlobalTheory.UnitaryHeckeBaseChange.toAdele _ E (z : AE (maximalRealSubfield E) E) := rfl
  have hfin : (x : AdeleRing (𝓞 E) E).2 = 1 := by
    let u : AF (maximalRealSubfield E) := (0, 1)
    have h0 : u • ((z : AE (maximalRealSubfield E) E) - 1) = 0 := hz u (map_zero _)
    have h1 := congrArg (GlobalTheory.UnitaryHeckeBaseChange.toAdele (maximalRealSubfield E) E) h0
    rw [Algebra.smul_def, map_mul, GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap, map_sub, map_one, map_zero, ← hx1] at h1
    have h2 := congrArg Prod.snd h1
    have h3 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap (maximalRealSubfield E) E u).2 = 1 := map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap (maximalRealSubfield E) E)
    change (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap (maximalRealSubfield E) E u).2 * ((x : AdeleRing (𝓞 E) E).2 - 1) = 0 at h2
    rw [h3, one_mul] at h2
    exact sub_eq_zero.1 h2
  let y : (InfiniteAdeleRing E)ˣ := Units.map (RingHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)).toMonoidHom x
  have hxy : x = GlobalTheory.CompanionTheory.HeckeFin.infIdele E y := Units.ext (Prod.ext rfl hfin)
  choose ρ hc hρ using fun w => exists_read (emb w).1
  have hf := inf_formula μ (fun w => (emb w).1) m ρ hc hρ hI y
  rw [hR z]
  change ((μ.1 x : ℂˣ) : ℂ) = _
  rw [hxy, hf]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [piInf_read (emb w) (ρ w) (hc w) (hρ w) z]
  rfl

end UpperTheory.Gal.TP.Chr

end
end

