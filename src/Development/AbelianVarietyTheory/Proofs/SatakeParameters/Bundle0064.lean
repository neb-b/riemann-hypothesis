module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharConstOnTranslatesTrivial
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0017
public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharInfTrivialOfTrivAtDegOne
section
noncomputable section
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit NumberField.mixedEmbedding
namespace GlobalTheory.HeckeInfTriv

section Inf
variable (E : Type) [Field E] [NumberField E]

theorem continuous_mixedSymm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace E).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_infIdele : Continuous (infIdele E) :=
  Continuous.units_map _ (continuous_id.prodMk continuous_const)

variable [_root_.NumberField.IsTotallyComplex E]

def cplxUnit : ({w : InfinitePlace E // w.IsComplex} → ℂˣ) →* (mixedSpace E)ˣ where
  toFun z := ⟨((fun _ => 1), fun w => (z w : ℂ)), ((fun _ => 1), fun w => ((z w)⁻¹ : ℂˣ)),
    Prod.ext (funext fun _ => mul_one _) (funext fun w => (z w).mul_inv),
    Prod.ext (funext fun _ => mul_one _) (funext fun w => (z w).inv_mul)⟩
  map_one' := Units.ext (Prod.ext rfl (funext fun _ => rfl))
  map_mul' z z' := Units.ext (Prod.ext (funext fun _ => (mul_one _).symm) (funext fun _ => rfl))

def infUnit : ({w : InfinitePlace E // w.IsComplex} → ℂˣ) →* (InfiniteAdeleRing E)ˣ :=
  (Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm.toRingHom.toMonoidHom).comp (cplxUnit E)

theorem continuous_infUnit : Continuous (infUnit E) := by
  refine (Continuous.units_map ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm.toRingHom.toMonoidHom) (continuous_mixedSymm E)).comp (f := cplxUnit E) ?_
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.prodMk (continuous_pi fun w => Units.continuous_val.comp (continuous_apply w))
  · exact continuous_const.prodMk (continuous_pi fun w => Units.continuous_coe_inv.comp (continuous_apply w))

theorem real_eq (f g : {w : InfinitePlace E // w.IsReal} → ℝ) : f = g :=
  funext fun w => absurd w.2 (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1))

theorem infUnit_emb (k : Eˣ) :
    infUnit E (fun w => Units.map w.1.embedding.toMonoidHom k) = infPart E (diagUnits E k) := by
  apply Units.ext
  change (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm ((fun _ => 1), fun w => w.1.embedding (k : E)) =
    algebraMap E (InfiniteAdeleRing E) (k : E)
  rw [RingEquiv.symm_apply_eq, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  exact Prod.ext (real_eq E _ _) (funext fun w => (mixedEmbedding_apply_isComplex E (k : E) w).symm)

theorem infUnit_surj (u : (InfiniteAdeleRing E)ˣ) : ∃ z, infUnit E z = u := by
  refine ⟨fun w => Units.map (((Pi.evalRingHom _ w).comp (RingHom.snd _ _)).comp
    (InfiniteAdeleRing.ringEquiv_mixedSpace E).toRingHom).toMonoidHom u, ?_⟩
  apply Units.ext
  change (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm ((fun _ => 1),
    fun w => (InfiniteAdeleRing.ringEquiv_mixedSpace E (u : InfiniteAdeleRing E)).2 w) = u
  rw [RingEquiv.symm_apply_eq]
  exact Prod.ext (real_eq E _ _) rfl

end Inf

section Loc
variable {E : Type} [Field E] [NumberField E]

theorem finPart_diag_val (v : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    ((finPart E v (diagUnits E k) : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
      algebraMap E (v.adicCompletion E) (k : E) := rfl

theorem val_coe (v : HeightOneSpectrum (𝓞 E)) (y : 𝓞 E) :
    Valued.v (algebraMap E (v.adicCompletion E) (y : E)) = v.intValuation y :=
  (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (y : E)).trans (v.valuation_of_algebraMap y)

theorem loc_unit (χ : Ideles E →* ℂˣ) (v : HeightOneSpectrum (𝓞 E)) (k : Eˣ) (y : 𝓞 E) (hk : (k : E) = y)
    (hy : y ∉ v.asIdeal) (hu : UnrAt χ v) : χ (localIdele E v (finPart E v (diagUnits E k))) = 1 := by
  apply hu
  rw [finPart_diag_val, hk, val_coe]
  exact v.intValuation_eq_one_iff.2 hy

theorem coe_algebraMap (F : Type) [Field F] [NumberField F] [Algebra F E] (a : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) = algebraMap F E (a : F) := rfl

end Loc

theorem inf_trivial_of_trivAt_degOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ → (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → ∀ x : (InfiniteAdeleRing E)ˣ, χ (infIdele E x) = 1 := by
  intro F E _ _ _ _ _ _ _ _ χ hχ hdeg
  classical
  obtain ⟨hunr, hcond, hfact⟩ := _root_.GlobalTheory.HeckeSplit.continuous_char_factor E χ hχ.1
  obtain ⟨θ, hθF, D, hD0, hDspan⟩ := _root_.GlobalTheory.quadratic_exists_integral_generator_common_denominator F E
  have hθ0 : (θ : E) ≠ 0 := fun h => hθF ⟨0, by rw [h, map_zero]⟩
  have hθ0' : θ ≠ 0 := fun h => hθ0 (by rw [h]; rfl)
  have hD0' : algebraMap (𝓞 F) (𝓞 E) D ≠ 0 := by
    intro h
    apply hD0
    have h1 : algebraMap F E (D : F) = 0 := by rw [← coe_algebraMap, h]; rfl
    exact_mod_cast (map_eq_zero_iff _ (algebraMap F E).injective).1 h1
  set e0 : 𝓞 E := algebraMap (𝓞 F) (𝓞 E) D * θ with he0
  have he0ne : e0 ≠ 0 := mul_ne_zero hD0' hθ0'
  have hfin : Set.Finite ({v | ¬ UnrAt χ v} ∪ {v | ¬ (DegOne F v → TrivAt χ v)} ∪
      {v : HeightOneSpectrum (𝓞 E) | e0 ∈ v.asIdeal}) := by
    refine ((Filter.eventually_cofinite.1 hunr).union (Filter.eventually_cofinite.1 hdeg)).union ?_
    refine (Ideal.finite_factors (I := Ideal.span {e0}) ?_).subset fun v hv => ?_
    · rwa [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    · exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)
  set S := hfin.toFinset with hS
  have hnotS : ∀ v, v ∉ S → UnrAt χ v ∧ (DegOne F v → TrivAt χ v) ∧ e0 ∉ v.asIdeal := by
    intro v hv
    simp only [hS, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
    exact ⟨hv.1.1, hv.1.2, hv.2⟩
  choose n hn using hcond
  have hπ : ∀ v : HeightOneSpectrum (𝓞 E), ∃ π : 𝓞 E, π ∈ v.asIdeal ∧ π ≠ 0 := fun v =>
    Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  choose π hπv hπ0 using hπ
  set P : 𝓞 E := ∏ v ∈ S, π v ^ n v with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hπ0 v)
  set m : Ideal (𝓞 F) := (Ideal.span {θ * P}).comap (algebraMap (𝓞 F) (𝓞 E)) with hm
  have hm0 : m ≠ ⊥ := Ideal.comap_ne_bot_of_integral_mem (mul_ne_zero hθ0' hP0)
    (Ideal.mem_span_singleton_self _) (Algebra.IsIntegral.isIntegral _)
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.residueClass_relativelyDense F m 0 hm0
  set t : Eˣ := Units.mk0 (θ : E) hθ0 with ht
  have hxb : ∀ b : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 E) b + θ : 𝓞 E) : E) ≠ 0 := by
    intro b h
    apply hθF
    refine ⟨-(b : F), ?_⟩
    have h1 : ((algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) + (θ : E) = 0 := by exact_mod_cast h
    rw [coe_algebraMap] at h1
    rw [map_neg]
    linear_combination -h1
  set xb : 𝓞 F → Eˣ := fun b => Units.mk0 _ (hxb b) with hxbdef
  have key : ∀ b ∈ m, χ (infIdele E (infPart E (diagUnits E (xb b)))) =
      χ (infIdele E (infPart E (diagUnits E t))) := by
    intro b hb
    have hloc : ∀ v, χ (localIdele E v (finPart E v (diagUnits E (xb b * t⁻¹)))) = 1 := by
      intro v
      by_cases hvS : v ∈ S
      · apply hn v
        obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hb)
        have h2 : algebraMap (𝓞 F) (𝓞 E) b + θ = (r * P + 1) * θ := by rw [← hr]; ring
        have h3 : ((algebraMap (𝓞 F) (𝓞 E) b + θ : 𝓞 E) : E) = ((r * P : 𝓞 E) : E) * (θ : E) + (θ : E) := by
          rw [h2]; push_cast; ring
        have hq1 : ((xb b * t⁻¹ : Eˣ) : E) - 1 = ((r * P : 𝓞 E) : E) := by
          simp only [hxbdef, ht, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
          rw [h3]
          field_simp
          ring
        rw [finPart_diag_val, ← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, hq1, val_coe,
          v.intValuation_le_pow_iff_mem]
        obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun w => π w ^ n w) hvS
        exact Ideal.mul_mem_left _ _ (by rw [hP, hc]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hπv v) _))
      · obtain ⟨hu, hd, he0v⟩ := hnotS v hvS
        simp only [map_mul, map_inv]
        have htv : χ (localIdele E v (finPart E v (diagUnits E t))) = 1 :=
          loc_unit χ v t θ rfl (fun h => he0v (Ideal.mul_mem_left _ _ h)) hu
        rw [htv, inv_one, mul_one]
        by_cases hmem : algebraMap (𝓞 F) (𝓞 E) b + θ ∈ v.asIdeal
        · haveI := v.isPrime
          haveI := v.isMaximal
          have hdeg1 : DegOne F v := _root_.GlobalTheory.residue_degree_one_of_linear_mem (𝓞 F) (𝓞 E) v.asIdeal θ D b 1
            (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := 𝓞 F) v.asIdeal) hDspan
            (fun h => he0v (Ideal.mul_mem_right _ _ h))
            (by rw [map_one]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h))
            (by rwa [map_one, one_mul])
          exact hd hdeg1 _
        · exact loc_unit χ v (xb b) _ rfl hmem hu
    have hdq := hfact (diagUnits E (xb b * t⁻¹)) S (fun v _ => hloc v)
    rw [hχ.2, Finset.prod_eq_one (fun v _ => hloc v), mul_one] at hdq
    simp only [map_mul, map_inv] at hdq
    exact mul_inv_eq_one.1 hdq.symm

  have hreal : ∀ i : {w : InfinitePlace E // w.IsComplex},
      ComplexEmbedding.IsReal (i.1.embedding.comp (algebraMap F E)) := fun i =>
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
  set τ : {w : InfinitePlace E // w.IsComplex} → (F →+* ℝ) := fun i => (hreal i).embedding with hτ
  have hτapp : ∀ i (a : F), ((τ i a : ℝ) : ℂ) = i.1.embedding (algebraMap F E a) := fun i a =>
    (hreal i).coe_embedding_apply a
  have hτinj : ∀ {j i : {w : InfinitePlace E // w.IsComplex}}, τ j = τ i → j = i := by
    intro j i h
    apply Subtype.ext
    apply GlobalTheory.T.infinitePlace_eq_of_embedding_comp_algebraMap_eq' F E
    ext a
    simp only [RingHom.comp_apply]
    rw [← hτapp, ← hτapp, h]
  set ψ : ({w : InfinitePlace E // w.IsComplex} → ℂˣ) →* ℂˣ := (χ.comp (infIdele E)).comp (infUnit E) with hψ
  have hψc : Continuous ψ := hχ.1.comp ((continuous_infIdele E).comp (continuous_infUnit E))
  set T : Set ({w : InfinitePlace E // w.IsComplex} → ℝ) := {y | ∃ b ∈ m, y = fun i => τ i (b : F)} with hT
  have hψ1 := _root_.GlobalTheory.charConstOnTranslates_trivial {w : InfinitePlace E // w.IsComplex} ψ (fun i => i.1.embedding (θ : E)) T (max C 0)
    (χ (infIdele E (infPart E (diagUnits E t)))) hψc (fun i => GlobalTheory.T.im_embedding_ne_zero_of_not_mem_range_algebraMap F E i.1 θ hθF) ?_ ?_
  · intro x
    obtain ⟨z, rfl⟩ := infUnit_surj E x
    have := DFunLike.congr_fun hψ1 z
    simpa [hψ] using this
  · intro y
    let y' : (F →+* ℝ) → ℝ := fun τ' => if h : ∃ i, τ i = τ' then y h.choose else 0
    obtain ⟨b, hb, hbC⟩ := hC y'
    refine ⟨fun i => τ i (b : F), ⟨b, by simpa using hb, rfl⟩, ?_⟩
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun i => ?_
    have hy' : y' (τ i) = y i := by
      have h : ∃ j, τ j = τ i := ⟨i, rfl⟩
      simp only [y', dif_pos h]
      rw [hτinj h.choose_spec]
    rw [Pi.sub_apply, Real.norm_eq_abs, ← hy']
    exact (hbC (τ i)).trans (le_max_left _ _)
  · rintro _ ⟨b, hb, rfl⟩ z hz
    have hzb : z = fun w => Units.map w.1.embedding.toMonoidHom (xb b) := funext fun i => Units.ext (by
      rw [hz i, Units.coe_map, hτapp]
      simp only [hxbdef, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      rw [← map_add (f := _), ← coe_algebraMap]
      rfl)
    rw [hzb]
    show χ (infIdele E (infUnit E _)) = _
    rw [infUnit_emb]
    exact key b hb

end GlobalTheory.HeckeInfTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharTrivialAtPlaceOfDegOneCofiniteTrivial
section
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

namespace GlobalTheory.HeckeFin

section ValLemmas
variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem val_eq_one_of_sub_one (v : Valuation K Γ) {a : K} {ε : Γ} (hε : ε < 1)
    (ha : v (a - 1) ≤ ε) : v a = 1 := by
  have e : a = 1 + (a - 1) := by ring
  rw [e, Valuation.map_one_add_of_lt v (lt_of_le_of_lt ha hε)]

theorem mul_sub_one_le (v : Valuation K Γ) {a b : K} {ε : Γ} (hε : ε < 1)
    (ha : v (a - 1) ≤ ε) (hb : v (b - 1) ≤ ε) : v (a * b - 1) ≤ ε := by
  have e : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  rw [e]
  refine le_trans (Valuation.map_add v _ _) (max_le ?_ ha)
  rw [map_mul, val_eq_one_of_sub_one v hε ha, one_mul]; exact hb

theorem inv_sub_one_le (v : Valuation K Γ) {a : K} {ε : Γ} (hε : ε < 1)
    (ha : v (a - 1) ≤ ε) : v (a⁻¹ - 1) ≤ ε := by
  have h1 := val_eq_one_of_sub_one v hε ha
  have ha0 : a ≠ 0 := by rintro rfl; simp at h1
  have e : a⁻¹ - 1 = -(a - 1) * a⁻¹ := by field_simp; ring
  rw [e, map_mul, Valuation.map_neg, map_inv₀, h1, inv_one, mul_one]; exact ha

end ValLemmas
end GlobalTheory.HeckeFin

namespace GlobalTheory.HeckeFin

theorem val_coe_sub_one (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (v.adicCompletion E) a - 1) = v.valuation E (a - 1) := by
  rw [← map_one (algebraMap E (v.adicCompletion E)), ← map_sub]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (a - 1)

theorem trivAt_of_degOne_cofinite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ → (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → (∀ x : (InfiniteAdeleRing E)ˣ, χ (infIdele E x) = 1) → ∀ w, TrivAt χ w := by
  intro F E _ _ _ _ _ _ _ _ χ hχ hdeg hinf w x
  classical
  obtain ⟨hunr, hloc, hfac⟩ := _root_.GlobalTheory.HeckeSplit.continuous_char_factor E χ hχ.1
  choose nf hnf using hloc
  have hU := Filter.eventually_cofinite.mp hunr
  have hX := Filter.eventually_cofinite.mp hdeg
  set S : Finset (HeightOneSpectrum (𝓞 E)) := hU.toFinset ∪ hX.toFinset ∪ {w} with hS
  have hSu : ∀ v ∉ S, UnrAt χ v := by
    intro v hv; by_contra h
    exact hv (by simp only [hS, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inl (Or.inl h))
  have hSd : ∀ v ∉ S, DegOne F v → TrivAt χ v := by
    intro v hv; by_contra h
    exact hv (by simp only [hS, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inl (Or.inr h))
  have hwS : w ∈ S := by simp [hS]
  obtain ⟨θ, D, hD0, hθ⟩ := _root_.GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen F E (Algebra.IsQuadraticExtension.finrank_eq_two F E)
  set ι := algebraMap (𝓞 F) (𝓞 E) with hι
  have hιinj : Function.Injective ι := by
    first
    | exact FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)
    | exact NoZeroSMulDivisors.algebraMap_injective (𝓞 F) (𝓞 E)
  set m : Ideal (𝓞 F) := Ideal.span {D} * Ideal.comap ι (∏ Q ∈ S, Q.asIdeal) with hm
  have hm0 : m ≠ ⊥ := by
    have hP : (∏ Q ∈ S, Q.asIdeal) ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
      intro Q _; rw [Ideal.zero_eq_bot]; exact Q.ne_bot
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    have hC : Ideal.comap ι (∏ Q ∈ S, Q.asIdeal) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ha0 ha (Algebra.IsIntegral.isIntegral a)
    have hD : Ideal.span {D} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    rw [hm, ← Ideal.zero_eq_bot]
    exact mul_ne_zero (by rwa [Ideal.zero_eq_bot]) (by rwa [Ideal.zero_eq_bot])
  have hmD : m ≤ Ideal.span {D} := Ideal.mul_le_left
  have hmS : ∀ Q ∈ S, m ≤ Q.asIdeal.comap ι := fun Q hQ =>
    le_trans Ideal.mul_le_right (Ideal.comap_mono (by rw [← Finset.mul_prod_erase S (fun Q => Q.asIdeal) hQ]; exact Ideal.mul_le_left))
  have hfin : {P : HeightOneSpectrum (𝓞 E) | m ≤ P.asIdeal.comap ι}.Finite := by
    have h0 : m.map ι ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective hιinj]; exact hm0
    refine (Ideal.finite_factors h0).subset ?_
    intro P hP
    simp only [Set.mem_setOf_eq] at hP ⊢
    rw [Ideal.dvd_iff_le]; exact Ideal.map_le_iff_le_comap.mpr hP
  set S' := hfin.toFinset with hS'
  have memS' : ∀ P, P ∈ S' ↔ m ≤ P.asIdeal.comap ι := by intro P; simp [hS']
  have hwS' : w ∈ S' := (memS' w).2 (hmS w hwS)
  have hSS' : ∀ v ∉ S', v ∉ S := fun v hv h => hv ((memS' v).2 (hmS v h))
  set n : ℕ := S'.sup nf + 1 with hn
  set ε : WithZero (Multiplicative ℤ) := WithZero.exp (-(n:ℤ)) with hεdef
  have hε : ε < 1 := by rw [hεdef, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hεv : ∀ v ∈ S', ε ≤ WithZero.exp (-(nf v : ℤ)) := by
    intro v hv; rw [hεdef, WithZero.exp_le_exp]; have := Finset.le_sup (f := nf) hv; omega
  obtain ⟨y, hy0, hyw, hyv⟩ := _root_.GlobalTheory.HkFin.exists_weak_approx_unit E S' w x n
  obtain ⟨y1, y2, hy2, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
  have hy2' : y2 ≠ 0 := nonZeroDivisors.ne_zero hy2
  have hy1' : y1 ≠ 0 := by rintro rfl; simp at hy0
  have hDι : ι D ≠ 0 := by
    intro h; apply hD0; apply hιinj; rw [h, map_zero]
  have hc1 : ι D * y1 ≠ 0 := mul_ne_zero hDι hy1'
  have hc2 : ι D * y2 ≠ 0 := mul_ne_zero hDι hy2'
  choose Nf hNf using fun (v : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E) (hc : c ≠ 0) => _root_.GlobalTheory.exists_pow_valuation_div_sub_one_le E v c hc n
  set N : ℕ := S'.sup (fun v => Nf v _ hc1 ⊔ Nf v _ hc2) with hN
  obtain ⟨k1, hk1, hk1P⟩ := _root_.GlobalTheory.exists_shift_mod_pow_degOne F E θ D hθ m hm0 hmD y1 N
  obtain ⟨k2, hk2, hk2P⟩ := _root_.GlobalTheory.exists_shift_mod_pow_degOne F E θ D hθ m hm0 hmD y2 N
  have hmem : ∀ v ∈ S', ∀ (k c : 𝓞 E), k - c ∈ Ideal.map ι (m ^ N) → ∀ M ≤ N, k - c ∈ v.asIdeal ^ M := by
    intro v hv k c h M hM
    have h1 : Ideal.map ι (m ^ N) ≤ v.asIdeal ^ N := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr ((memS' v).1 hv)) N
    exact Ideal.pow_le_pow_right hM (h1 h)
  have hcl1 : ∀ v ∈ S', v.valuation E ((k1 : E) / ((ι D * y1 : 𝓞 E) : E) - 1) ≤ ε := fun v hv =>
    hNf v _ hc1 k1 (hmem v hv _ _ hk1 _ (le_trans le_sup_left (Finset.le_sup (f := fun v => Nf v _ hc1 ⊔ Nf v _ hc2) hv)))
  have hcl2 : ∀ v ∈ S', v.valuation E ((k2 : E) / ((ι D * y2 : 𝓞 E) : E) - 1) ≤ ε := fun v hv =>
    hNf v _ hc2 k2 (hmem v hv _ _ hk2 _ (le_trans le_sup_right (Finset.le_sup (f := fun v => Nf v _ hc1 ⊔ Nf v _ hc2) hv)))
  have hk1' : (k1 : E) ≠ 0 := by
    intro h; have := hcl1 w hwS'; rw [h, zero_div, zero_sub, Valuation.map_neg, map_one] at this
    exact absurd hε (not_lt.mpr this)
  have hk2' : (k2 : E) ≠ 0 := by
    intro h; have := hcl2 w hwS'; rw [h, zero_div, zero_sub, Valuation.map_neg, map_one] at this
    exact absurd hε (not_lt.mpr this)
  have ha : ∀ z : 𝓞 E, algebraMap (𝓞 E) E z = (z : E) := fun z => rfl
  have hDE : ((ι D : 𝓞 E) : E) ≠ 0 := by exact_mod_cast hDι
  have hy1E : (y1 : E) ≠ 0 := by exact_mod_cast hy1'
  have hy2E : (y2 : E) ≠ 0 := by exact_mod_cast hy2'
  set kk : E := (k1 : E) / (k2 : E) with hkk
  have hkk0 : kk ≠ 0 := div_ne_zero hk1' hk2'
  have hkey : kk = ((k1 : E) / ((ι D * y1 : 𝓞 E) : E)) * ((k2 : E) / ((ι D * y2 : 𝓞 E) : E))⁻¹ *
      (algebraMap (𝓞 E) E y1 / algebraMap (𝓞 E) E y2) := by
    rw [ha, ha, hkk]; push_cast; field_simp
  have hv1 : ∀ v ∈ S', v ≠ w → v.valuation E (kk - 1) ≤ ε := by
    intro v hv hvw
    rw [hkey]
    exact GlobalTheory.HeckeFin.mul_sub_one_le _ hε (GlobalTheory.HeckeFin.mul_sub_one_le _ hε (hcl1 v hv)
      (GlobalTheory.HeckeFin.inv_sub_one_le _ hε (hcl2 v hv))) (hyv v hv hvw)
  have hvw : Valued.v (algebraMap E (w.adicCompletion E) kk *
      ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) ≤ ε := by
    have e : algebraMap E (w.adicCompletion E) kk * ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        algebraMap E (w.adicCompletion E) (((k1 : E) / ((ι D * y1 : 𝓞 E) : E)) * ((k2 : E) / ((ι D * y2 : 𝓞 E) : E))⁻¹) *
        (algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E y1 / algebraMap (𝓞 E) E y2) *
          ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E)) := by
      rw [hkey, map_mul, mul_assoc]
    rw [e]
    refine GlobalTheory.HeckeFin.mul_sub_one_le _ hε ?_ hyw
    rw [val_coe_sub_one]
    exact GlobalTheory.HeckeFin.mul_sub_one_le _ hε (hcl1 w hwS') (GlobalTheory.HeckeFin.inv_sub_one_le _ hε (hcl2 w hwS'))
  set kU : Eˣ := Units.mk0 kk hkk0 with hkU
  have hcoe : ∀ v : HeightOneSpectrum (𝓞 E), ((finPart E v (diagUnits E kU) : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
      algebraMap E (v.adicCompletion E) kk := fun v => rfl
  have hout : ∀ v ∉ S', χ (localIdele E v (finPart E v (diagUnits E kU))) = 1 := by
    intro v hv
    have hvS := hSS' v hv
    have hmv : ¬ m ≤ v.asIdeal.comap ι := fun h => hv ((memS' v).2 h)
    by_cases h1 : k1 ∈ v.asIdeal
    · exact hSd v hvS (hk1P v hmv h1) _
    by_cases h2 : k2 ∈ v.asIdeal
    · exact hSd v hvS (hk2P v hmv h2) _
    apply hSu v hvS
    rw [hcoe, show Valued.v (algebraMap E (v.adicCompletion E) kk) = v.valuation E kk from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v kk, hkk, map_div₀]
    have e1 : ∀ k : 𝓞 E, k ∉ v.asIdeal → v.valuation E (k : E) = 1 := by
      intro k hk
      refine le_antisymm (v.valuation_le_one k) ?_
      rw [← not_lt]; intro hlt; exact hk ((v.valuation_lt_one_iff_mem k).mp hlt)
    rw [e1 k1 h1, e1 k2 h2, div_one]
  have hprod := hfac (diagUnits E kU) S' hout
  rw [hχ.2 kU, hinf, one_mul, Finset.prod_eq_single w] at hprod
  · set z : (w.adicCompletion E)ˣ := (finPart E w (diagUnits E kU))⁻¹ * x with hz
    have hzv : χ (localIdele E w z) = 1 := by
      apply hnf w z
      refine le_trans ?_ (hεv w hwS')
      have e : (z : w.adicCompletion E) = (algebraMap E (w.adicCompletion E) kk *
          ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E))⁻¹ := by
        rw [hz, Units.val_mul, Units.val_inv_eq_inv_val, hcoe, Units.val_inv_eq_inv_val, mul_inv, inv_inv]
      rw [e]; exact GlobalTheory.HeckeFin.inv_sub_one_le _ hε hvw
    have hx : x = finPart E w (diagUnits E kU) * z := by rw [hz, mul_inv_cancel_left]
    show χ (localIdele E w x) = 1
    rw [hx, map_mul, map_mul, ← hprod, hzv, one_mul]
  · intro v hv hvw
    apply hnf v
    rw [hcoe]; refine le_trans ?_ (hεv v hv)
    rw [val_coe_sub_one]; exact hv1 v hv hvw
  · intro h; exact absurd hwS' h

end GlobalTheory.HeckeFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankTwoLogbFiveSqLe
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem rank_two_logb_five_sq_le {eps : ℝ} (Fm : FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
      2 * Real.logb 5 ((Fm.L x i).sc.a ^ 2) + 2 ≤ ((Fm.D x i).R.k : ℝ) - 1 := by
  refine ⟨3, fun x hx hx1 i => ?_⟩
  have hK := (Fm.sizes x hx1 i).2.2.1.1
  have hsx := Fm.L_x x i hx1
  have he := (Fm.L x i).sc.eps_pos
  have he' := (Fm.L x i).sc.eps_lt
  have hx3 : (3 : ℝ) ≤ x := hx
  have hx0 : (0 : ℝ) < x := by linarith
  rw [hsx] at hK
  have h4 : x ^ (4 : ℕ) ≤ ((Fm.D x i).R.k : ℝ) := by
    refine le_trans ?_ hK
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    unfold szTh
    push_cast
    linarith
  have hL : (Fm.L x i).sc.L ≤ x := by
    unfold Scale.L
    rw [hsx]
    calc x ^ (Fm.L x i).sc.eps ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = x := Real.rpow_one x
  have hL0 : 0 ≤ (Fm.L x i).sc.L := by
    unfold Scale.L
    rw [hsx]
    positivity
  have hla : Real.log (Fm.L x i).sc.a = Real.log x + (Fm.L x i).sc.L := by
    unfold Scale.a Scale.b
    rw [hsx, Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hlx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h5 : 1 ≤ Real.log 5 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hb : Real.logb 5 ((Fm.L x i).sc.a ^ 2) ≤ 4 * x := by
    rw [Real.logb, Real.log_pow, hla]
    push_cast
    refine (div_le_self (by linarith) h5).trans (by linarith)
  have h27 : 27 ≤ x ^ 3 := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx3 3
  have : 27 * x ≤ x ^ 4 := by
    calc 27 * x ≤ x ^ 3 * x := mul_le_mul_of_nonneg_right h27 hx0.le
      _ = x ^ 4 := by ring
  linarith

end GlobalTheory
end

