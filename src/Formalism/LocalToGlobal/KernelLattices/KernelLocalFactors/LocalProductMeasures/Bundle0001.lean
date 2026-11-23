module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.Bundle0003
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0002
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

@[expose] public section

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.HeckeCharacterCompatibleSystem
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.Host

section Loc

variable {E : Type} [Field E] [NumberField E]

theorem hk_le_exp {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem hk_val_one {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : OneAt P a) : P.valuation E a = 1 := by
  have e : a = 1 + (a - 1) := by ring
  rw [e]
  have h1 : P.valuation E (a - 1) < P.valuation E (1 : E) := by rw [map_one]; exact h
  rw [Valuation.map_add_eq_of_lt_left _ h1, map_one]

theorem hk_valued (P : HeightOneSpectrum (𝓞 E)) (a : Eˣ) :
    Valued.v ((atFin P a : (P.adicCompletion E)ˣ) : P.adicCompletion E) = P.valuation E (a : E) :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (a : E)

theorem hk_valued_sub (P : HeightOneSpectrum (𝓞 E)) (a : Eˣ) :
    Valued.v (((atFin P a : (P.adicCompletion E)ˣ) : P.adicCompletion E) - 1) = P.valuation E ((a : E) - 1) := by
  have e : ((atFin P a : (P.adicCompletion E)ˣ) : P.adicCompletion E) - 1 = (((a : E) - 1 : E) : P.adicCompletion E) := by
    show algebraMap E (P.adicCompletion E) (a : E) - 1 = algebraMap E (P.adicCompletion E) ((a : E) - 1)
    rw [map_sub, map_one]
  rw [e]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P ((a : E) - 1)

theorem hk_tame (χ : HChar E) {P : HeightOneSpectrum (𝓞 E)} (h : χ.TameAt P) (a : Eˣ) (ha : OneAt P (a : E)) : χ.locK P a = 1 := by
  refine h (atFin P a) ?_ ?_
  · show Valued.v _ = 1
    rw [hk_valued, hk_val_one ha]
  · rw [hk_valued_sub]
    exact hk_le_exp ha

theorem hk_unr (χ : HChar E) {P : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt P) (a : Eˣ) (ha : P.valuation E (a : E) = 1) : χ.locK P a = 1 := by
  refine h (atFin P a) ?_
  show Valued.v _ = 1
  rw [hk_valued, ha]

theorem hk_unif (χ : HChar E) {P : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt P) (a : Eˣ) (ha : P.valuation E (a : E) = WithZero.exp (-1 : ℤ)) :
    χ.locK P a = χ.val P := by
  refine χ.val_eq h (atFin P a) ?_
  show Valued.v _ = _
  rw [hk_valued, ha]

theorem hecke_character_local_behaviour : HLoc := fun _ _ _ χ _ =>
  ⟨fun h a ha => hk_tame χ h a ha, fun h a ha => hk_unr χ h a ha, fun h a ha => hk_unif χ h a ha⟩

end Loc

section Sys

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hk_mem_above (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) :
    P ∈ aboveF (L := E) F v ↔ P.asIdeal.under (𝓞 F) = v.asIdeal := by
  unfold aboveF
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · intro h; rw [← h]; rfl
  · intro h; exact HeightOneSpectrum.ext h

theorem hk_lamH (χ : HChar E) (v : HeightOneSpectrum (𝓞 F)) (a : Eˣ) :
    lamH (F := F) χ v a = ∏ P ∈ aboveF (L := E) F v, χ.locK P a := by
  unfold lamH
  rw [MonoidHom.finsetProd_apply]

theorem hecke_character_compatible_system : HSys := by
  intro F E _ _ _ _ _ χ Rm ht hF hu
  refine ⟨?_, ?_, ?_⟩
  · intro v a ha
    rw [hk_lamH]
    exact Finset.prod_eq_one fun P hP => hk_tame χ (ht P) a (ha P ((hk_mem_above v P).1 hP))
  · intro v k
    rw [hk_lamH]
    have h := hF.1 v k
    unfold HChar.resFin at h
    rw [MonoidHom.finsetProd_apply] at h
    exact h
  · intro v hv a ha
    rw [hk_lamH]
    exact Finset.prod_eq_one fun P hP =>
      hk_unr χ (hu v hv P ((hk_mem_above v P).1 hP)) a (ha P ((hk_mem_above v P).1 hP))

theorem hecke_character_evaluation : HEval := by
  intro F E _ _ _ _ _ χ ht v P hP b hb
  rw [hk_lamH]
  refine Finset.prod_eq_single P ?_ ?_
  · intro P' hP' hne
    exact hk_tame χ (ht P') b (hb P' hne ((hk_mem_above v P').1 hP'))
  · intro h
    exact absurd ((hk_mem_above v P).2 hP) h

end Sys

section Prod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hecke_character_product_formula : HProd := by
  classical
  intro F E _ _ _ _ _ χ S hS x
  have hfin : {P : HeightOneSpectrum (𝓞 E) | ¬ P.valuation E (x : E) = 1}.Finite := by
    have h := Filter.eventually_cofinite.1 (valued_comp_eventually E (diagUnits E x))
    simpa only [diag_comp] using h
  set T0 : Finset (HeightOneSpectrum (𝓞 E)) := S ∪ hfin.toFinset with hT0
  have hval : ∀ P, P ∉ T0 → P.valuation E (x : E) = 1 := by
    intro P hP
    by_contra h
    exact hP (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
  have hone : ∀ P, P ∉ T0 → χ.locK P x = 1 := fun P hP =>
    hk_unr χ (hS P fun h => hP (Finset.mem_union_left _ h)) x (hval P hP)
  have hmain : χ.inf x * ∏ P ∈ T0, χ.locK P x = 1 := by
    have h := χ.productRule T0 (fun P hP => hS P fun h => hP (Finset.mem_union_left _ h)) x
    have h2 : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ T0), χ.val v ^ ordF v x) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun P => ?_
      rw [finprod_eq_if]
      split_ifs with hP
      · rfl
      · have h0 : ordF P x = 0 := by
          unfold ordF
          rw [hval P hP, WithZero.log_one, neg_zero]
        rw [h0, zpow_zero]
    rw [h2, mul_one] at h
    exact h
  set T : Finset (HeightOneSpectrum (𝓞 F)) := T0.image (fun P => P.under (𝓞 F)) with hT
  have hsupp : ∀ v, v ∉ T → lamH (F := F) χ v x = 1 := by
    intro v hv
    rw [hk_lamH]
    refine Finset.prod_eq_one fun P hP => hone P fun hPT => hv ?_
    rw [hT, Finset.mem_image]
    exact ⟨P, hPT, HeightOneSpectrum.ext ((hk_mem_above v P).1 hP)⟩
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => lamH (F := F) χ v x) ⊆ ↑T := by
    intro v hv
    by_contra h
    exact hv (hsupp v h)
  refine ⟨T.finite_toSet.subset hsub, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  have e : ∏ v ∈ T, lamH (F := F) χ v x = ∏ P ∈ T0, χ.locK P x := by
    rw [← Finset.prod_fiberwise_of_maps_to (s := T0) (t := T) (g := fun P => P.under (𝓞 F)) (fun P hP => Finset.mem_image_of_mem _ hP)]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hk_lamH]
    symm
    refine Finset.prod_subset ?_ ?_
    · intro P hP
      rw [Finset.mem_filter] at hP
      rw [hk_mem_above, ← hP.2]
      rfl
    · intro P hP hn
      apply hone
      intro hPT
      apply hn
      rw [Finset.mem_filter]
      exact ⟨hPT, HeightOneSpectrum.ext ((hk_mem_above v P).1 hP)⟩
  rw [e]
  exact eq_inv_of_mul_eq_one_right hmain

end Prod

section Inf

theorem hk_sq (w : ℂ) (hw : w ≠ 0) : (w / ((‖w‖ : ℝ) : ℂ)) ^ 2 = w / (starRingEnd ℂ) w := by
  have h1 : ((‖w‖ : ℝ) : ℂ) ^ 2 = w * (starRingEnd ℂ) w := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have hc : (starRingEnd ℂ) w ≠ 0 := (map_ne_zero _).2 hw
  rw [div_pow, h1]
  field_simp

theorem hecke_character_infinity_type : HInf := by
  intro X hX σ₀ χ n e hn hne x
  rw [hn x]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hw : X.embC σ₀ τ (x : X.E) ≠ 0 := (map_ne_zero _).2 x.ne_zero
  rw [hne τ, zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hk_sq _ hw, ← hX.conjE (X.embC σ₀ τ) (x : X.E)]
  congr 1
  rw [map_div₀, map_div₀]
  rfl

end Inf

end Formalism.L2.Ker
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.TwistComponentsCompatibleSystem
section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.UG Formalism.UG.P Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

section XS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem xs_intAt (P : HeightOneSpectrum (𝓞 E)) (a : E) (h : P.valuation E a ≤ 1) :
    ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r := by
  obtain ⟨r₀, s₀, hs₀, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
  have hs0 : s₀ ≠ 0 := nonZeroDivisors.ne_zero hs₀
  have hsE : algebraMap (𝓞 E) E s₀ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hs0
  have hv0 : P.intValuation s₀ ≠ 0 := P.intValuation_ne_zero s₀ hs0
  have hle1 : P.intValuation s₀ ≤ 1 := P.intValuation_le_one s₀
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P.intValuation s₀ = WithZero.exp (-(n : ℤ)) := by
    refine ⟨(-(WithZero.log (P.intValuation s₀))).toNat, ?_⟩
    have hl : WithZero.log (P.intValuation s₀) ≤ 0 := by
      rw [WithZero.log_le_iff_le_exp hv0, WithZero.exp_zero]
      exact hle1
    rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hv0]
  have hsn : s₀ ∈ P.asIdeal ^ n := (P.intValuation_le_pow_iff_mem s₀ n).1 hn.le
  have hsn1 : s₀ ∉ P.asIdeal ^ (n + 1) := fun hm => by
    have h1 := (P.intValuation_le_pow_iff_mem s₀ (n + 1)).2 hm
    rw [hn, WithZero.exp_le_exp] at h1
    push_cast at h1
    omega
  have hrn : r₀ ∈ P.asIdeal ^ n := by
    rw [← intValuation_le_pow_iff_mem, ← hn]
    rw [map_div₀, valuation_of_algebraMap, valuation_of_algebraMap] at h
    exact (div_le_one₀ (zero_lt_iff.2 hv0)).1 h
  obtain ⟨J, hJ⟩ : P.asIdeal ^ n ∣ Ideal.span {s₀} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hsn)
  have hJP : ¬ J ≤ P.asIdeal := fun hle => hsn1 (by
    have h2 : Ideal.span {s₀} ≤ P.asIdeal ^ (n + 1) := by
      rw [hJ, pow_succ]
      exact Ideal.mul_mono_right hle
    exact h2 (Ideal.mem_span_singleton_self _))
  obtain ⟨j, hj, hjP⟩ := SetLike.not_le_iff_exists.1 hJP
  have h3 : r₀ * j ∈ Ideal.span {s₀} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hrn hj
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h3
  refine ⟨t, j, hjP, ?_⟩
  have h4 := congrArg (algebraMap (𝓞 E) E) ht
  rw [map_mul, map_mul] at h4
  rw [mul_div_assoc', div_eq_iff hsE, h4]
  ring

theorem xs_den (v : HeightOneSpectrum (𝓞 F)) (a : E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.under (𝓞 F) = v.asIdeal → P.valuation E a ≤ 1) :
    ∃ (d : 𝓞 F) (r : 𝓞 E), d ∉ v.asIdeal ∧ algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) d) * a = algebraMap (𝓞 E) E r := by
  let I : Ideal (𝓞 E) :=
    { carrier := {t | ∃ r : 𝓞 E, algebraMap (𝓞 E) E t * a = algebraMap (𝓞 E) E r}
      add_mem' := by
        rintro x y ⟨r, hr⟩ ⟨r', hr'⟩
        exact ⟨r + r', by rw [map_add (f := _), add_mul, hr, hr', map_add (f := _)]⟩
      zero_mem' := ⟨0, by rw [map_zero, zero_mul]⟩
      smul_mem' := by
        rintro c x ⟨r, hr⟩
        exact ⟨c * r, by rw [smul_eq_mul, map_mul, mul_assoc, hr, map_mul]⟩ }
  by_contra hcon
  have hle : Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) I ≤ v.asIdeal := by
    intro d hd
    obtain ⟨r, hr⟩ := hd
    by_contra hdv
    exact hcon ⟨d, r, hdv, hr⟩
  have := v.isPrime
  obtain ⟨Q, hQ, hQp, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal I hle
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  obtain ⟨r, s, hs, hrs⟩ := xs_intAt ⟨Q, hQp, hQ0⟩ a (h ⟨Q, hQp, hQ0⟩ hQv)
  exact hs (hQ ⟨r, hrs⟩)

theorem xs_elt (v : HeightOneSpectrum (𝓞 F)) (a : E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.under (𝓞 F) = v.asIdeal → P.valuation E a ≤ 1) :
    ∃ t : RInt F E, (t : AfE F E) = a ⊗ₜ[F] Formalism.L2.G.sgl F v 1 ∧
      ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E a < 1 → t ∈ P.asIdeal.map (toRInt F E) := by
  obtain ⟨d, r, hd, hr⟩ := xs_den v a h
  have hval : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d)) = 1 := by
    rw [AdeleIntA.val_R, intValuation_eq_one_iff_mem_primeCompl]
    exact Ideal.mem_primeCompl_iff.mpr hd
  have ha0 : algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hval
    exact zero_ne_one hval
  have hc : (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d))⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  refine ⟨toRInt F E r * ⟨(1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d))⁻¹, qu_right _ (qu_sgl_int v _ hc)⟩,
    ?_, fun P hP => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)⟩
  · show ((algebraMap (𝓞 E) E r) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) *
      ((1 : E) ⊗ₜ[F] Formalism.L2.G.sgl F v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d))⁻¹) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← hr, qu_tow, ← Algebra.smul_def, TensorProduct.smul_tmul, ← map_smul, Algebra.smul_def,
      mul_inv_cancel₀ ha0]
  · rw [← valuation_lt_one_iff_mem (K := E)]
    show P.valuation E (algebraMap (𝓞 E) E r) < 1
    rw [← hr, map_mul]
    calc P.valuation E (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) d)) * P.valuation E a ≤ 1 * P.valuation E a :=
          mul_le_mul' (P.valuation_le_one _) le_rfl
      _ = P.valuation E a := one_mul _
      _ < 1 := hP

theorem xs_val (v : HeightOneSpectrum (𝓞 F)) (a : Eˣ) :
    ((locId E v a : (AfE F E)ˣ) : AfE F E) = (a : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1) := rfl

theorem xs_supp (v : HeightOneSpectrum (𝓞 F)) (a : Eˣ) : locId E v a ∈ suppAt E v := by
  rw [b_mem_suppAt]
  intro v' hv'
  show (Algebra.TensorProduct.map (AlgHom.id F E) (evalV F v')) ((a : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1)) = 1
  rw [map_add (f := _), Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_sub, Formalism.L2.G.sgl_apply_ne F v 1 hv', TensorProduct.tmul_zero,
    zero_add, sub_zero, map_one (evalV F v')]
  rfl

theorem xs_one_sub (v : HeightOneSpectrum (𝓞 F)) : (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1) ∈ RInt F E :=
  qu_right _ ((intAd F).sub_mem (intAd F).one_mem (qu_sgl_int v 1 (one_mem _)))

theorem xs_intU (v : HeightOneSpectrum (𝓞 F)) (a : Eˣ)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.under (𝓞 F) = v.asIdeal → P.valuation E (a : E) = 1) : locId E v a ∈ intU F E := by
  rw [intU, Submonoid.mem_units_iff]
  constructor
  · obtain ⟨t, ht, _⟩ := xs_elt v (a : E) (fun P hP => (h P hP).le)
    show (a : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1) ∈ RInt F E
    rw [← ht]
    exact add_mem t.2 (xs_one_sub v)
  · obtain ⟨t, ht, _⟩ := xs_elt v ((a⁻¹ : Eˣ) : E) (fun P hP => by rw [Units.val_inv_eq_inv_val, map_inv₀, h P hP, inv_one])
    show ((a⁻¹ : Eˣ) : E) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1) ∈ RInt F E
    rw [← ht]
    exact add_mem t.2 (xs_one_sub v)

theorem xs_unit_of_oneAt {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : OneAt P a) : P.valuation E a = 1 := by
  have h1 := Valuation.map_one_add_of_lt (v := P.valuation E) h
  rwa [add_sub_cancel] at h1

theorem xs_wild (v : HeightOneSpectrum (𝓞 F)) (a : Eˣ)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.under (𝓞 F) = v.asIdeal → OneAt P (a : E)) : locId E v a ∈ wildAt E v := by
  obtain ⟨u, hu⟩ := b_intU _ (xs_intU v a fun P hP => xs_unit_of_oneAt (h P hP))
  rw [← hu]
  apply tpWild_proof' v u (by rw [hu]; exact xs_supp v a)
  intro P
  by_cases hP : P.asIdeal.under (𝓞 F) = v.asIdeal
  · obtain ⟨t, ht, hm⟩ := xs_elt v ((a : E) - 1) (fun P' hP' => (h P' hP').le)
    have e : (u : RInt F E) - 1 = t := Subtype.ext (by
      show ((u : RInt F E) : AfE F E) - 1 = t
      have h1 : ((u : RInt F E) : AfE F E) = ((locId E v a : (AfE F E)ˣ) : AfE F E) := congrArg Units.val hu
      rw [h1, ht, xs_val, TensorProduct.sub_tmul, ← locId_one (E := E) v]
      ring)
    rw [e]
    exact hm P (h P hP)
  · exact tpOff_proof' v P hP u (by rw [hu]; exact xs_supp v a)

theorem xs_idF (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : locId E v (Units.map (algebraMap F E).toMonoidHom k) ∈ (idF F E).range := by
  have h1 : Formalism.L2.G.sgl F v 1 * Formalism.L2.G.sgl F v 1 = Formalism.L2.G.sgl F v 1 := by rw [← Formalism.L2.G.sgl_mul, one_mul]
  have hk : algebraMap F (FiniteAdeleRing (𝓞 F) F) (k : F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((k⁻¹ : Fˣ) : F) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  let y : (FiniteAdeleRing (𝓞 F) F)ˣ :=
    { val := algebraMap F (FiniteAdeleRing (𝓞 F) F) (k : F) * Formalism.L2.G.sgl F v 1 + (1 - Formalism.L2.G.sgl F v 1)
      inv := algebraMap F (FiniteAdeleRing (𝓞 F) F) ((k⁻¹ : Fˣ) : F) * Formalism.L2.G.sgl F v 1 + (1 - Formalism.L2.G.sgl F v 1)
      val_inv := by
        linear_combination (algebraMap F (FiniteAdeleRing (𝓞 F) F) (k : F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((k⁻¹ : Fˣ) : F)
          - algebraMap F (FiniteAdeleRing (𝓞 F) F) (k : F) - algebraMap F (FiniteAdeleRing (𝓞 F) F) ((k⁻¹ : Fˣ) : F) + 1) * h1 + Formalism.L2.G.sgl F v 1 * hk
      inv_val := by
        linear_combination (algebraMap F (FiniteAdeleRing (𝓞 F) F) (k : F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((k⁻¹ : Fˣ) : F)
          - algebraMap F (FiniteAdeleRing (𝓞 F) F) (k : F) - algebraMap F (FiniteAdeleRing (𝓞 F) F) ((k⁻¹ : Fˣ) : F) + 1) * h1 + Formalism.L2.G.sgl F v 1 * hk }
  refine ⟨y, Units.ext ?_⟩
  show (1 : E) ⊗ₜ[F] (algebraMap F (FiniteAdeleRing (𝓞 F) F) (k : F) * Formalism.L2.G.sgl F v 1 + (1 - Formalism.L2.G.sgl F v 1)) =
    (algebraMap F E (k : F)) ⊗ₜ[F] Formalism.L2.G.sgl F v 1 + (1 : E) ⊗ₜ[F] (1 - Formalism.L2.G.sgl F v 1)
  rw [TensorProduct.tmul_add, qu_move]

end XS

theorem twist_components_compatible_system : XiSys := by
  intro F E _ _ _ _ _ L _ S ξ
  refine ⟨fun v a h => ?_, fun v k => ?_, fun v hv a h => ?_⟩
  · exact MonoidHom.mem_ker.1 ((mem_kills.1 ((Subgroup.mem_iInf.1 ξ.2.1.2) v)) (xs_wild v a h))
  · exact MonoidHom.mem_ker.1 ((mem_kills.1 ξ.2.1.1.2) (xs_idF v k))
  · have hle : inertAt E v ≤ (ξ : Chr F E L).ker := by
      by_contra hc
      exact hv hc
    exact MonoidHom.mem_ker.1 (hle ⟨xs_intU v a h, xs_supp v a⟩)

end Formalism.L2.Ker
end
end

