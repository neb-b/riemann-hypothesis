module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
public import GroundTheory.GlobalFields.GlobalReciprocity.General
public import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassFieldLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvOneSubBound

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.NormCnt
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.SmGL GlobalTheory.SplitWeil
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.SemiLocal
open scoped Classical

namespace UpperTheory.V.Z.Gam

private theorem count_one {A : Type} [CommGroup A] (U : Subgroup A) (l : ℕ) (hl : l.Prime) (η θ : A →* ℂˣ)
    (hη : ∀ x, η x ^ l = 1) (hθ : ∀ x ∈ U, η x = 1 → θ x = 1) (u : A) (hu : u ∈ U) (h1 : η u ≠ 1) :
    ((Finset.range l).filter fun j => ∀ x ∈ U, θ x * η x ^ j = 1).card = 1 := by
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have hp : IsPrimitiveRoot (η u) l := by
    rw [← orderOf_eq_prime (hη u) h1]
    exact IsPrimitiveRoot.orderOf _
  have h2 : (θ u)⁻¹ ∈ rootsOfUnity l ℂ := by
    rw [mem_rootsOfUnity, inv_pow, ← map_pow, hθ _ (U.pow_mem hu l) (by rw [map_pow, hη]), inv_one]
  obtain ⟨j, hj, e⟩ := hp.eq_pow_of_mem_rootsOfUnity h2
  rw [Finset.card_eq_one]
  refine ⟨j, Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, fun x hx => ?_⟩, fun i hi => ?_⟩⟩
  · obtain ⟨m, -, hm⟩ := hp.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity l (η x)).2 (hη x))
    have h3 := hθ (x * (u ^ m)⁻¹) (U.mul_mem hx (U.inv_mem (U.pow_mem hu m)))
      (by rw [map_mul, map_inv, map_pow, hm, mul_inv_cancel])
    rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at h3
    rw [h3, ← hm, ← pow_mul, mul_comm m, pow_mul, e, ← mul_pow, mul_inv_cancel, one_pow]
  · obtain ⟨hi, h⟩ := Finset.mem_filter.1 hi
    refine hp.pow_inj (Finset.mem_range.1 hi) hj ?_
    rw [e]
    exact (eq_inv_of_mul_eq_one_right (h u hu))

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {v : HeightOneSpectrum (𝓞 K)}

private theorem fdeg_eq (w : PlacesOver L v) : fdeg w = w.1.asIdeal.inertiaDeg (𝓞 K) := by
  have := w.1.isMaximal
  have := v.isMaximal
  exact Ideal.inertiaDeg'_eq_inertiaDeg _ _

private theorem fdeg_pos (w : PlacesOver L v) : 0 < fdeg w := by
  have := w.1.isPrime
  rw [fdeg_eq]
  exact Ideal.inertiaDeg_pos _ _

private theorem ord_nm (w : PlacesOver L v) (x : (w.1.adicCompletion L)ˣ) :
    ord ((nm w x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = fdeg w * ord (x : w.1.adicCompletion L) := by
  rw [fdeg_eq, ← inertiaDeg_integer v w.1]
  exact ord_norm (x : w.1.adicCompletion L)

private theorem unr_iff (θ : (v.adicCompletion K)ˣ →* ℂˣ) :
    IsUnram θ ↔ ∀ x ∈ unitFiltrationUnits (v.adicCompletion K) 0, θ x = 1 :=
  forall_congr' fun _ => by rw [mem_unitFiltrationUnits_zero_iff]

private theorem unr_nm (w : PlacesOver L v) (θ : (v.adicCompletion K)ˣ →* ℂˣ) :
    IsUnram (θ.comp (nm w)) ↔ ∀ x ∈ unitFiltrationUnits (v.adicCompletion K) 0, x ∈ (nm w).range → θ x = 1 := by
  rw [unr_iff]
  constructor
  · rintro h _ hx ⟨y, rfl⟩
    refine h y ?_
    rw [← ord_eq_zero_iff_mem, ord_nm] at hx
    exact ord_eq_zero_iff_mem.1 ((mul_eq_zero.1 hx).resolve_left (by exact_mod_cast (fdeg_pos w).ne'))
  · intro h y hy
    refine h _ ?_ ⟨y, rfl⟩
    rw [← ord_eq_zero_iff_mem, ord_nm, ord_eq_zero_iff_mem.2 hy, mul_zero]

private theorem sum_ef (v : HeightOneSpectrum (𝓞 K)) :
    ∑ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) * fdeg w = Module.finrank K L := by
  have := v.isMaximal
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 K) K (𝓞 L) L,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 L)]
  exact Fintype.sum_equiv (placesOverEquiv L v) _ _ fun w => by rw [fdeg_eq]; rfl

private theorem gal_e [IsGalois K L] (w w' : PlacesOver L v) :
    w.1.asIdeal.ramificationIdx (𝓞 K) = w'.1.asIdeal.ramificationIdx (𝓞 K) ∧ fdeg w = fdeg w' := by
  have := w.1.isPrime
  have := w'.1.isPrime
  have hw : w.1.asIdeal.LiesOver v.asIdeal := w.2
  have e : w.1.asIdeal.under (𝓞 K) = w'.1.asIdeal.under (𝓞 K) := w.2.over.symm.trans w'.2.over
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) (L ≃ₐ[K] L) _ _ e
  rw [fdeg_eq, fdeg_eq, hσ]
  exact ⟨(Ideal.ramificationIdx_smul _ _ σ).symm, (Ideal.inertiaDeg_smul _ _ σ).symm⟩

private theorem prim (η : HChar K) (w : PlacesOver L v) (hk : (η.loc v).ker = (nm w).range)
    (hu : unitFiltrationUnits (v.adicCompletion K) 0 ≤ (η.loc v).ker) :
    η.UnrAt v ∧ IsPrimitiveRoot (η.val v) (fdeg w) := by
  have h1 : η.UnrAt v := fun x hx => hu (mem_unitFiltrationUnits_zero_iff_valued.2 hx)
  obtain ⟨π, hπ, hπ'⟩ := exists_ord_eq_one_valued v
  obtain ⟨ϖ, hϖ⟩ := exists_ord_eq_one_units (w.1.adicCompletion L)
  refine ⟨h1, ?_⟩
  rw [← η.val_eq h1 π hπ']
  constructor
  · have h2 : π ^ (fdeg w : ℤ) * (nm w ϖ)⁻¹ ∈ (η.loc v).ker := by
      apply hu
      rw [← ord_eq_zero_iff_mem, Units.val_mul, ord_mul (Units.ne_zero _) (Units.ne_zero _), ← map_inv, ord_nm,
        ord_zpow_units hπ, ← zpow_neg_one, ord_zpow_units hϖ]
      ring
    have h3 : nm w ϖ ∈ (η.loc v).ker := hk ▸ ⟨ϖ, rfl⟩
    rw [MonoidHom.mem_ker] at h2 h3
    rwa [map_mul, map_inv, h3, inv_one, mul_one, zpow_natCast, map_pow] at h2
  · intro m hm
    rw [← map_pow, ← MonoidHom.mem_ker, hk] at hm
    obtain ⟨y, hy⟩ := hm
    have h4 := ord_nm w y
    rw [hy, ← zpow_natCast, ord_zpow_units hπ] at h4
    exact Int.natCast_dvd_natCast.1 ⟨_, h4⟩

private theorem exists_eta [IsGalois K L] (hl : (Module.finrank K L).Prime) :
    ∃ η : HChar K, ∀ v : HeightOneSpectrum (𝓞 K), (∀ x, η.loc v x ^ Module.finrank K L = 1) ∧
      ∀ w : PlacesOver L v, (η.loc v).ker = (nm w).range ∧
        (unitFiltrationUnits (v.adicCompletion K) 0 ≤ (nm w).range ↔ w.1.asIdeal.ramificationIdx (𝓞 K) = 1) := by
  haveI : Fact (Module.finrank K L).Prime := ⟨hl⟩
  haveI : NeZero (Module.finrank K L) := ⟨hl.ne_zero⟩
  have hc : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card hc
  haveI : IsMulCommutative (L ≃ₐ[K] L) := inferInstance
  let ι : (L ≃ₐ[K] L) →* ℂˣ := (rootsOfUnity (Module.finrank K L) ℂ).subtype.comp
    (mulEquivOfPrimeCardEq hc (Complex.card_rootsOfUnity _)).toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp (MulEquiv.injective _)
  have hm : ι.comp (ideleSymbol K L) ∈ hcharSub K :=
    ⟨(continuous_of_discreteTopology (f := ι)).comp (continuous_ideleSymbol L),
      fun k => (congrArg ι (ideleSymbol_diagonal (L := L) k)).trans (map_one ι)⟩
  refine ⟨⟨_, hm⟩, fun v => ?_⟩
  have e : HChar.loc (⟨ι.comp (ideleSymbol K L), hm⟩ : HChar K) v = ι.comp (localSymbol L v) :=
    MonoidHom.ext fun x => congrArg ι (ideleSymbol_finiteEmbedding (L := L) v x)
  rw [e]
  refine ⟨fun x => by rw [MonoidHom.comp_apply, ← map_pow, ← hc, pow_card_eq_one', map_one], fun w => ?_⟩
  have hk : (localSymbol L v).ker = (nm w).range := ker_localSymbol L v w
  refine ⟨by rw [MonoidHom.ker_comp_of_injective _ _ hι, hk], ?_⟩
  rw [← hk]
  refine ⟨fun h => ramificationIdx_eq_one_of_units_le_ker_localSymbol v h w.1, fun h x hx => ?_⟩
  refine units_le_ker_localSymbol L v w h ?_
  have h1 := mem_unitFiltrationUnits_zero_iff_valued.1 hx
  have h2 := mem_unitFiltrationUnits_zero_iff_valued.1 (inv_mem hx)
  exact (Submonoid.mem_units_iff _ _).2 ⟨h1.le, h2.le⟩

private theorem loc_pow (η : HChar K) (j : ℕ) (x : (v.adicCompletion K)ˣ) : (η ^ j).loc v x = η.loc v x ^ j := by
  induction j with
  | zero => simp [HChar.loc]
  | succ j ih =>
    simp only [HChar.loc, MonoidHom.comp_apply] at ih ⊢
    rw [pow_succ]
    change (η ^ j).1 (Neutral.B1.localIdele K v x) * η.1 (Neutral.B1.localIdele K v x) = _
    rw [ih, pow_succ]

end UpperTheory.V.Z.Gam

theorem UpperTheory.V.Z.Gam.normCnt :
    UpperTheory.V.Z.Gam.NormCnt := by
  intro K L _ _ _ _ _ _ hl
  obtain ⟨η, hη⟩ := exists_eta (K := K) (L := L) hl
  refine ⟨η, ?_, fun v w => ?_⟩
  · filter_upwards [IdeleNorm.eventually_forall_placesOver K (IdeleNorm.eventually_ramificationIdx_eq_one K L)] with v hv
    have h := fun w : PlacesOver L v =>
      prim η w ((hη v).2 w).1 (by rw [((hη v).2 w).1]; exact ((hη v).2 w).2.2 (hv w))
    obtain ⟨w₀⟩ := nonempty_placesOver L v
    refine ⟨(h w₀).1, fun w => ⟨(h w).2, ?_⟩⟩
    rw [← sum_ef v, Finset.sum_congr rfl fun w' _ => show _ = fdeg w by rw [hv w', one_mul, (gal_e w' w).2]]
    simp
  obtain ⟨hp, hw⟩ := hη v
  refine ⟨MonoidHom.ext fun y => ?_, fun w' θ h => ?_, fun θ hθ => ⟨?_, fun h => ?_, fun h => ?_⟩⟩
  · exact ((hw w).1.ge ⟨y, rfl⟩ :)
  · have h1 := (unr_nm w θ).1 h
    rw [← (hw w).1, (hw w').1] at h1
    exact (unr_nm w' θ).2 h1
  · unfold IsSmoothChar at hθ ⊢
    rw [← MonoidHom.comap_ker]
    exact hθ.preimage (continuous_normUnits (K := v.adicCompletion K) (L := w.1.adicCompletion L))
  · exact (unr_nm w θ).2 fun x hx _ => (unr_iff θ).1 h x hx
  have h1 := (unr_nm w θ).1 h
  have e : ∀ j : ℕ, IsUnram (θ * (η ^ j).loc v) ↔
      ∀ x ∈ unitFiltrationUnits (v.adicCompletion K) 0, θ x * η.loc v x ^ j = 1 := fun j => by
    rw [unr_iff]
    simp only [MonoidHom.mul_apply, loc_pow]
  have hs : w.1.asIdeal.ramificationIdx (𝓞 K) * ∑ w' : PlacesOver L v, fdeg w' = Module.finrank K L := by
    rw [← sum_ef v, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w' _ => by rw [(gal_e w w').1]
  refine (congrArg Finset.card (Finset.filter_congr fun j _ => e j)).trans ?_
  by_cases hr : w.1.asIdeal.ramificationIdx (𝓞 K) = 1
  · rw [hr, one_mul] at hs
    rw [hs, Finset.filter_true_of_mem, Finset.card_range]
    intro j _ x hx
    have h2 := (hw w).2.2 hr hx
    rw [h1 x hx h2, show η.loc v x = 1 from (hw w).1.ge h2, one_pow, one_mul]
  · obtain ⟨u, hu, hu'⟩ := SetLike.not_le_iff_exists.1 (mt (hw w).2.1 hr)
    rw [← (hw w).1] at hu' h1
    rw [← hs] at hl
    have h3 := ((Nat.prime_mul_iff.1 hl).resolve_right fun h => hr h.2).2
    rw [hs] at hl
    rw [h3]
    convert count_one _ _ hl (η.loc v) θ hp h1 u hu hu'
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.RegroupBC
section
noncomputable section

open NumberField IsDedekindDomain Polynomial GlobalTheory.HenQ
open GroundTheory.Global.SemiLocal

namespace UpperTheory.V.Z.Gam

namespace BaseChangeLocalFactorRegrouping

private theorem one_period {f : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ f) (hf : 0 < f) (y : ℂ) :
    ∏ j ∈ Finset.range f, (1 - ζ ^ j * y) = 1 - y ^ f := by
  have h1 := congrArg (Polynomial.eval (1 : ℂ)) (X_pow_sub_C_eq_prod h hf (rfl : y ^ f = y ^ f))
  rw [Polynomial.eval_prod] at h1
  simpa using h1.symm

private theorem periods {f : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ f) (hf : 0 < f) (y : ℂ) (g : ℕ) :
    ∏ j ∈ Finset.range (g * f), (1 - ζ ^ j * y) = (1 - y ^ f) ^ g := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [Nat.succ_mul, Finset.prod_range_add, ih, pow_succ, ← one_period h hf y]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [pow_add, mul_comm g f, pow_mul, h.pow_eq_one, one_pow, one_mul]

private theorem fac_eq {f : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ f) (hf : 0 < f) (g : ℕ) (B : Multiset ℂ) (x : ℂ) :
    ∏ j ∈ Finset.range (g * f), ((B.map (· * ζ ^ j)).map fun b => (1 - b * x)⁻¹).prod =
      (((B.map (· ^ f)).map fun b => (1 - b * x ^ f)⁻¹).prod) ^ g := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons a B ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [Finset.prod_mul_distrib, ih, mul_pow, Finset.prod_inv_distrib, ← mul_pow a x, inv_pow, ← periods h hf]
    congr 2
    refine Finset.prod_congr rfl fun j _ => ?_
    ring

private theorem cast_pow_cpow (N f : ℕ) (z : ℂ) : (((N ^ f : ℕ)) : ℂ) ^ z = (((N : ℕ) : ℂ) ^ z) ^ f := by
  induction f with
  | zero => simp
  | succ f ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem norm_eq {p : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L p) :
    Ideal.absNorm w.1.asIdeal = Ideal.absNorm p.asIdeal ^ fdeg w :=
  Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.1.asIdeal p.asIdeal p.isPrime p.ne_bot

private theorem under_eq {p : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L p) : w.1.under (𝓞 K) = p := by
  ext1
  rw [HeightOneSpectrum.under_asIdeal]
  exact w.2.over.symm

private theorem nonempty_over (p : HeightOneSpectrum (𝓞 K)) : Nonempty (PlacesOver L p) := by
  haveI := p.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) p.asIdeal
  exact ⟨⟨⟨P, hPm.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot P⟩, hP⟩⟩

private theorem core (d : ℕ) (MainNotions : Set (HeightOneSpectrum (𝓞 K))) (SL : Set (HeightOneSpectrum (𝓞 L)))
    (BK : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (BL : HeightOneSpectrum (𝓞 L) → Multiset ℂ)
    (e : HeightOneSpectrum (𝓞 K) → ℂ) (c₀ : ℝ) (r : ℕ) (hd : 0 < d)
    (hS : ∀ w, w ∈ SL ↔ w.under (𝓞 K) ∈ MainNotions)
    (h : ∀ p ∉ MainNotions, Multiset.card (BK p) ≤ r ∧ (∀ b ∈ BK p, ‖b‖ ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ c₀) ∧
      ∀ w : PlacesOver L p, IsPrimitiveRoot (e p) (fdeg w) ∧ Fintype.card (PlacesOver L p) * fdeg w = d ∧
        BL w.1 = (BK p).map (· ^ fdeg w))
    (s : ℂ) (hs : c₀ + 1 < s.re) :
    ∏ j ∈ Finset.range d, eulerL K (fun p => (BK p).map (· * e p ^ j)) MainNotions s = eulerL L BL SL s := by
  have hf : ∀ p ∉ MainNotions, ∀ w : PlacesOver L p, 0 < fdeg w := by
    intro p hp w
    have := ((h p hp).2.2 w).2.1
    rcases Nat.eq_zero_or_pos (fdeg w) with h0 | h0
    · rw [h0] at this; omega
    · exact h0
  have hL := (GlobalTheory.HenQ.Regroup.multipliable_E L SL BL c₀ r (by
    intro w hw
    have hp : w.under (𝓞 K) ∉ MainNotions := (hS w).not.mp hw
    let w' : PlacesOver L (w.under (𝓞 K)) := ⟨w, ⟨rfl⟩⟩
    obtain ⟨h1, h2, h3⟩ := h _ hp
    have hB : BL w = _ := (h3 w').2.2
    have hN : Ideal.absNorm w.asIdeal = _ := norm_eq w'
    refine ⟨by rw [hB, Multiset.card_map]; exact h1, fun b hb => ?_⟩
    rw [hB] at hb
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
    rw [hN, norm_pow, Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (h2 a ha) _) s hs).hasProd
  have hK : ∀ j ∈ Finset.range d, Multipliable (fun p : {p : HeightOneSpectrum (𝓞 K) // p ∉ MainNotions} =>
      (((BK p.1).map (· * e p.1 ^ j)).map fun b => (1 - b * ((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod) := by
    intro j _
    refine GlobalTheory.HenQ.Regroup.multipliable_E K MainNotions (fun p => (BK p).map (· * e p ^ j)) c₀ r ?_ s hs
    intro p hp
    obtain ⟨h1, h2, h3⟩ := h _ hp
    obtain ⟨w⟩ := nonempty_over (L := L) p
    have he : ‖e p‖ = 1 := (h3 w).1.norm'_eq_one (hf p hp w).ne'
    refine ⟨by rw [Multiset.card_map]; exact h1, fun b hb => ?_⟩
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
    rw [norm_mul, norm_pow, he, one_pow, mul_one]
    exact h2 a ha
  let E : (Σ p : {p : HeightOneSpectrum (𝓞 K) // p ∉ MainNotions}, PlacesOver L p.1) ≃
      {w : HeightOneSpectrum (𝓞 L) // w ∉ SL} :=
    { toFun := fun x => ⟨x.2.1, by rw [hS, under_eq x.2]; exact x.1.2⟩
      invFun := fun w => ⟨⟨w.1.under (𝓞 K), (hS w.1).not.mp w.2⟩, ⟨w.1, ⟨rfl⟩⟩⟩
      left_inv := by
        rintro ⟨⟨p, hp⟩, w⟩
        have hw := under_eq w
        obtain ⟨w, hw'⟩ := w
        simp only at hw
        subst hw
        rfl
      right_inv := by intro w; rfl }
  have h2 := (E.hasProd_iff).mpr hL
  unfold eulerL
  rw [← Multipliable.tprod_finsetProd hK]
  refine (h2.sigma ?_).tprod_eq
  rintro ⟨p, hp⟩
  obtain ⟨w₀⟩ := nonempty_over (L := L) p
  obtain ⟨-, -, h3⟩ := h p hp
  have hcard : 0 < Fintype.card (PlacesOver L p) := Fintype.card_pos_iff.mpr ⟨w₀⟩
  have hff : ∀ w : PlacesOver L p, fdeg w = fdeg w₀ := fun w =>
    Nat.eq_of_mul_eq_mul_left hcard ((h3 w).2.1.trans (h3 w₀).2.1.symm)
  convert hasProd_fintype _ using 1
  · dsimp only [E, Equiv.coe_fn_mk, Function.comp_apply]
    rw [← (h3 w₀).2.1, fac_eq (h3 w₀).1 (hf p hp w₀), ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [(h3 w).2.2, norm_eq w, cast_pow_cpow, hff w]

end BaseChangeLocalFactorRegrouping

end UpperTheory.V.Z.Gam

open UpperTheory.V.Z.Gam.BaseChangeLocalFactorRegrouping in
theorem UpperTheory.V.Z.Gam.regroupBC :
    UpperTheory.V.Z.Gam.RegroupBC := by
  intro K L _ _ _ _ _ d MainNotions SL BK BL e c₀ r hd hS h
  refine ⟨c₀ + 1, fun s => ⟨fun hs => core d MainNotions SL BK BL e c₀ r hd.pos hS
    (fun p hp => ⟨(h p hp).1, fun b hb => ((h p hp).2.1 b hb).1, (h p hp).2.2⟩) s hs, fun hs => ?_⟩⟩
  unfold eulerLd
  rw [← core d MainNotions SL (fun p => (BK p).map (·⁻¹)) (fun w => (BL w).map (·⁻¹)) (fun p => (e p)⁻¹) c₀ r hd.pos hS
    ?_ (1 - s) ?_]
  · refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    funext p
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, mul_inv, inv_pow]
  · intro p hp
    obtain ⟨h1, h2, h3⟩ := h p hp
    refine ⟨by rw [Multiset.card_map]; exact h1, fun b hb => ?_, fun w => ⟨(h3 w).1.inv, (h3 w).2.1, ?_⟩⟩
    · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
      exact (h2 a ha).2
    · simp only [(h3 w).2.2, Multiset.map_map]
      refine Multiset.map_congr rfl fun b _ => ?_
      simp only [Function.comp_apply, inv_pow]
  · simp only [Complex.sub_re, Complex.one_re]
    linarith
end
end

