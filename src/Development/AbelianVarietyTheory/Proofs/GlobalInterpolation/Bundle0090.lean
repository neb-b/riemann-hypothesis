module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0083
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValueLatticeAddSubgroupSmulMoveLaws
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSupportedIdele
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation
open TensorProduct Formalism.UG Formalism.UG.P

noncomputable section

namespace GlobalTheory.SuppIdele

section Base

variable {F : Type} [Field F] [NumberField F]

theorem exists_int_mul (a : 𝓞 F) (ha : a ≠ 0) (z : FiniteAdeleRing (𝓞 F) F)
    (hz : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v (z w) ≤ w.intValuation a) :
    ∃ x ∈ intAd F, z = (a : F) • x := by
  have ha' : (a : F) ≠ 0 := by simpa using ha
  refine ⟨(a : F)⁻¹ • z, fun w => ?_, by rw [smul_smul, mul_inv_cancel₀ ha', one_smul]⟩
  rw [afsplit_smul_apply, HeightOneSpectrum.mem_adicCompletionIntegers, Algebra.smul_def, map_mul, map_inv₀, map_inv₀]
  have h1 : Valued.v (algebraMap F (w.adicCompletion F) (a : F)) = w.intValuation a := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (a : F)
  rw [h1, inv_mul_le_iff₀ (zero_lt_iff.2 (w.intValuation_ne_zero a ha)), mul_one]
  exact hz w

theorem val_algebraMap (w : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    Valued.v (algebraMap F (w.adicCompletion F) (a : F)) = w.intValuation a := by
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (a : F)

theorem intVal_eq_one (w : HeightOneSpectrum (𝓞 F)) {a : 𝓞 F} (h : a ∉ w.asIdeal) : w.intValuation a = 1 :=
  le_antisymm (w.intValuation_le_one a) (not_lt.1 fun h' => h ((w.intValuation_lt_one_iff_mem a).1 h'))

theorem exists_notMem {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : ∃ c ∈ w.asIdeal, c ∉ v.asIdeal := by
  by_contra H
  push Not at H
  exact h (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top H))

theorem eps_dvd (v : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F) (hc : c ∉ v.asIdeal) :
    ∃ x ∈ intAd F, afsplitI v 1 = (c : F) • x := by
  refine exists_int_mul c (by rintro rfl; exact hc (zero_mem _)) _ fun w => ?_
  by_cases h : w = v
  · subst h
    rw [afsplitI_self, map_one, intVal_eq_one w hc]
  · rw [afsplitI_ne v w h, map_zero]
    exact zero_le

theorem one_sub_eps (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a ∈ v.asIdeal ^ 2, ∃ r ∈ v.asIdeal ^ 2, ∃ x ∈ intAd F,
      1 - afsplitI v 1 = (a : F) • x + (r : F) • (1 - afsplitI v 1) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (pow_ne_zero 2 v.ne_bot)
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hI⟩ := Ideal.eq_prime_pow_mul_coprime (I := Ideal.span {a}) (by simpa using ha0) v.asIdeal
  have hc : IsCoprime (v.asIdeal ^ 2) Q := (Ideal.isCoprime_iff_sup_eq.2 hQ).pow_left
  obtain ⟨r, hr, q, hq, hrq⟩ := Ideal.isCoprime_iff_exists.1 hc
  obtain ⟨x, hx, hxe⟩ := exists_int_mul a ha0 ((q : F) • (1 - afsplitI v 1)) fun w => by
    rw [afsplit_smul_apply, afsplit_sub_apply, afsplit_one_apply]
    by_cases h : w = v
    · subst h
      rw [afsplitI_self, sub_self, smul_zero, map_zero]
      exact zero_le
    · rw [afsplitI_ne v w h, sub_zero, Algebra.smul_def, mul_one, val_algebraMap]
      obtain ⟨t, ht, htw⟩ := exists_notMem (Ne.symm h)
      have hm := Ideal.mul_mem_mul (Ideal.pow_mem_pow ht
        (Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})))) hq
      rw [← hI, Ideal.mem_span_singleton'] at hm
      obtain ⟨s, hs⟩ := hm
      have := congrArg w.intValuation hs
      rw [map_mul, map_mul, map_pow, intVal_eq_one w htw, one_pow, one_mul] at this
      rw [← this]
      exact mul_le_of_le_one_left' (w.intValuation_le_one s)
  refine ⟨a, ha, r, hr, x, hx, ?_⟩
  rw [← hxe, ← add_smul]
  have : (q : F) + (r : F) = 1 := by
    rw [add_comm]; exact_mod_cast congrArg (fun t : 𝓞 F => (t : F)) hrq
  rw [this, one_smul]

end Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (E) in
def ofInt (x : FiniteAdeleRing (𝓞 F) F) (hx : x ∈ intAd F) : RInt F E :=
  ⟨(1 : E) ⊗ₜ[F] x, Subring.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)⟩

theorem coe_toRInt (b : 𝓞 E) : (toRInt F E b : AfE F E) = (b : E) ⊗ₜ[F] 1 := rfl

theorem tmul_smul_eq (a : 𝓞 F) (x : FiniteAdeleRing (𝓞 F) F) (hx : x ∈ intAd F) :
    (1 : E) ⊗ₜ[F] ((a : F) • x) = ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) a) * ofInt E x hx : RInt F E) : AfE F E) := by
  rw [Subring.coe_mul, coe_toRInt, ofInt, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
  rfl

theorem eps_int (v : HeightOneSpectrum (𝓞 F)) : afsplitI v 1 ∈ intAd F := afsplitI_mem_intAd v 1 (one_mem _)

theorem exists_crt (I Q : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hQ : Q ≠ ⊥) (h : IsCoprime I Q) (b : 𝓞 E) :
    ∃ b' : 𝓞 E, b' ≠ 0 ∧ b' - b ∈ I ∧ b' - 1 ∈ Q := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Ideal.isCoprime_iff_exists.1 h
  have h1 : b * q + p - b ∈ I := by
    have : b * q + p - b = (1 - b) * p := by linear_combination b * hpq
    rw [this]; exact I.mul_mem_left _ hp
  have h2 : b * q + p - 1 ∈ Q := by
    have : b * q + p - 1 = (b - 1) * q := by linear_combination hpq
    rw [this]; exact Q.mul_mem_left _ hq
  by_cases h0 : b * q + p = 0
  · obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (mul_ne_zero hI hQ)
    rw [h0] at h1 h2
    refine ⟨t, ht0, ?_, ?_⟩
    · have h3 : t ∈ I := Ideal.mul_le_inf ht |>.1
      rw [show t - b = t + (0 - b) by ring]
      exact I.add_mem h3 h1
    · have h3 : t ∈ Q := Ideal.mul_le_inf ht |>.2
      rw [show t - 1 = t + (0 - 1) by ring]
      exact Q.add_mem h3 h2
  · exact ⟨_, h0, h1, h2⟩

theorem exists_supported_idele (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (b : 𝓞 E)
    (hPv : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    ∃ (y : (AfE F E)ˣ) (y₀ : RInt F E), (y₀ : AfE F E) = (y : AfE F E) ∧ y ∈ suppAt E v ∧
      y₀ - toRInt F E b ∈ (P.asIdeal ^ 2).map (toRInt F E) ∧
      ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → y₀ - 1 ∈ P'.asIdeal.map (toRInt F E) := by
  haveI := P.isMaximal
  have hv0 : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  obtain ⟨Q, hQ, hI⟩ := Ideal.eq_prime_pow_mul_coprime hv0 P.asIdeal
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    exact hv0 (by rw [hI, Ideal.mul_bot])
  obtain ⟨b', hb0, hb1, hb2⟩ := exists_crt (P.asIdeal ^ 2) Q (pow_ne_zero 2 P.ne_bot) hQ0
    (Ideal.isCoprime_iff_sup_eq.2 hQ).pow_left b
  have hb0' : (b' : E) ≠ 0 := by simpa using hb0
  set e : RInt F E := ofInt E (afsplitI v 1) (eps_int v) with he
  have hee : (e : AfE F E) = afsplitEps E v := rfl
  set ι := inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) with hι
  have hid := afsplit_eps_idem (E := E) v
  have hinv : ι b' * ι (b' : E)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hb0', map_one]
  have hmul : (1 + (ι b' - 1) * afsplitEps E v) * (1 + (ι (b' : E)⁻¹ - 1) * afsplitEps E v) = 1 := by
    linear_combination (ι b' - 1) * (ι (b' : E)⁻¹ - 1) * hid + afsplitEps E v * hinv
  refine ⟨⟨_, _, hmul, by rw [mul_comm, hmul]⟩, 1 + (toRInt F E b' - 1) * e, rfl, ?_, ?_, ?_⟩
  · simp only [Formalism.L2.DIV.suppAt, Subgroup.mem_iInf, MonoidHom.mem_ker]
    intro w hw
    apply Units.ext
    show prV (E := E) w (1 + (ι b' - 1) * afsplitEps E v) = 1
    rw [map_add (f := _), map_mul, afsplit_prV_eps_ne v w hw, mul_zero, add_zero, map_one]
  · obtain ⟨a, ha, r, hr, x, hx, hxe⟩ := one_sub_eps v
    have hle : ∀ c ∈ v.asIdeal ^ 2, toRInt F E (algebraMap (𝓞 F) (𝓞 E) c) ∈ (P.asIdeal ^ 2).map (toRInt F E) := by
      intro c hc
      apply Ideal.mem_map_of_mem
      have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hc
      rw [Ideal.map_pow] at h1
      refine Ideal.pow_right_mono ?_ 2 h1
      rw [← hPv]; exact Ideal.map_comap_le
    have hx' : 1 - afsplitI v 1 ∈ intAd F := sub_mem (one_mem _) (eps_int v)
    have h1 : 1 - e = toRInt F E (algebraMap (𝓞 F) (𝓞 E) a) * ofInt E x hx +
        toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) * ofInt E _ hx' := by
      apply Subtype.ext
      rw [Subring.coe_add, ← tmul_smul_eq, ← tmul_smul_eq, ← TensorProduct.tmul_add, ← hxe, TensorProduct.tmul_sub]
      rfl
    have h2 : 1 - e ∈ (P.asIdeal ^ 2).map (toRInt F E) := by
      rw [h1]
      exact add_mem (Ideal.mul_mem_right _ _ (hle a ha)) (Ideal.mul_mem_right _ _ (hle r hr))
    have h3 : 1 + (toRInt F E b' - 1) * e - toRInt F E b = toRInt F E (b' - b) + (1 - toRInt F E b') * (1 - e) := by
      rw [map_sub]; ring
    rw [h3]
    exact add_mem (Ideal.mem_map_of_mem _ hb1) (Ideal.mul_mem_left _ _ h2)
  · intro P' hP'
    rw [add_sub_cancel_left]
    by_cases hle : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ P'.asIdeal
    · rw [hI] at hle
      have hQP : Q ≤ P'.asIdeal := by
        rcases P'.isPrime.mul_le.1 hle with h | h
        · haveI := P'.isPrime
          exact absurd (HeightOneSpectrum.ext (P.isMaximal.eq_of_le P'.isPrime.ne_top
            (Ideal.IsPrime.le_of_pow_le h))).symm hP'
        · exact h
      have := Ideal.mem_map_of_mem (toRInt F E) (hQP hb2)
      rw [map_sub, map_one] at this
      exact Ideal.mul_mem_right _ _ this
    · have hc : ∃ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) c ∈ P'.asIdeal ∧ c ∉ v.asIdeal := by
        by_contra H
        push Not at H
        haveI := P'.isMaximal
        have hm : (P'.asIdeal.under (𝓞 F)).IsMaximal := inferInstance
        apply hle
        rw [← hm.eq_of_le v.isPrime.ne_top (fun c hc => H c hc)]
        exact Ideal.map_comap_le
      obtain ⟨c, hc1, hc2⟩ := hc
      obtain ⟨x, hx, hxe⟩ := eps_dvd v c hc2
      have h1 : e = toRInt F E (algebraMap (𝓞 F) (𝓞 E) c) * ofInt E x hx := by
        apply Subtype.ext
        rw [← tmul_smul_eq, ← hxe]
        rfl
      rw [h1]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc1))

end GlobalTheory.SuppIdele
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeNodes
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_sizeNodes : SzRow (fun _ _ L => SizeNodes L) := by
  intro eps he0 he1 C _
  obtain ⟨x1, hx1⟩ := _root_.GlobalTheory.EX.rank_basic_bounds eps he0 he1
  refine ⟨0, fun cD hcD => ⟨1300 + cD, fun ch hch => ⟨max x1 200, fun D L hε hx hV => ?_⟩⟩⟩
  simp only [max_le_iff, ge_iff_le] at hx hch
  obtain ⟨hxa, hxb⟩ := hx
  obtain ⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, ht, hN, -, -⟩ := hx1 L.sc D.R hε hxa hV.ranks
  have hxone : 1 ≤ L.sc.x := by linarith
  have hxpos : 0 < L.sc.x := by linarith
  have cast : ∀ a : ℕ, L.sc.x ^ (a : ℝ) = L.sc.x ^ a := fun a => Real.rpow_natCast _ _
  have hf' : (D.R.f : ℝ) ≤ L.sc.x ^ 3 := by rw [← cast]; exact_mod_cast hf
  have hr' : (D.R.r : ℝ) ≤ L.sc.x ^ 5 := by rw [← cast]; exact_mod_cast hr
  have ht' : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by rw [← cast]; exact_mod_cast ht
  have hN' : (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ 402 := by rw [← cast]; exact_mod_cast hN
  have hk' : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := le_trans (by exact_mod_cast hkr) hr'
  have hnf : (D.R.n : ℝ) ≤ D.R.f := by
    have : D.R.n ≤ D.R.f := by unfold Ranks.f; omega
    exact_mod_cast this
  have hm2 := D.R.two_le_m
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hMN : (D.R.r : ℝ) + D.R.m * D.R.t ≤ D.R.N D.R.m := by
    have : D.R.r + D.R.m * D.R.t ≤ D.R.N D.R.m := by
      unfold Ranks.N Ranks.r
      rw [Nat.mul_add, Nat.mul_one]; omega
    exact_mod_cast this
  have hY : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hxone hcD
  have hDel : ((Delv L.sc cD : ℕ) : ℝ) ≤ 2 * L.sc.x ^ cD := by
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)
    unfold Delv; linarith
  have hSc : L.Sc = (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) := by
    rw [L.Sc_eq, hV.Del_eq]; push_cast; ring
  have hS0 : 0 ≤ L.Sc := by rw [hSc]; positivity
  have hS : L.Sc ≤ L.sc.x ^ 6 * L.sc.x ^ cD := by
    rw [hSc]
    calc (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) ≤ L.sc.x ^ 5 * (4 * (2 * L.sc.x ^ cD)) := by gcongr
      _ = L.sc.x ^ 5 * 8 * L.sc.x ^ cD := by ring
      _ ≤ L.sc.x ^ 5 * L.sc.x * L.sc.x ^ cD := by gcongr; linarith
      _ = _ := by ring
  have hh0 : L.sc.x ^ ch ≤ L.etaSz / D.R.m := by
    have e : L.etaSz / D.R.m = (h0v L.sc ch : ℝ) := by
      rw [hV.eta_eq]; field_simp
    have := Nat.le_ceil (L.sc.x ^ ch)
    have h0' : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℕ) := Nat.cast_nonneg _
    rw [e]; unfold h0v; push_cast; linarith
  have hH : L.sc.x ^ 1300 * L.sc.x ^ cD ≤ L.etaSz / D.R.m := by
    refine le_trans ?_ hh0
    rw [← cast, ← Real.rpow_add hxpos]
    exact Real.rpow_le_rpow_of_exponent_le hxone (by exact_mod_cast hch)
  have hth : L.sc.x ^ szTh L ≤ L.sc.x := by
    have : szTh L ≤ 1 := by unfold szTh; rw [hε]; linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hxone this
  obtain ⟨a1, a2, a3, a5, a6, a7, -, a9, -⟩ := nodeGap_poly hxb hY
    (Nat.cast_nonneg D.R.n) (Nat.cast_nonneg D.R.f) hm1 (Nat.cast_nonneg D.R.k) (Nat.cast_nonneg D.R.r)
    (Nat.cast_nonneg D.R.t) (Nat.cast_nonneg (D.R.N D.R.m))
    (by positivity : (0 : ℝ) ≤ (D.R.r : ℝ) + D.R.m * D.R.t) (by linarith : 0 ≤ L.sc.L) hS0
    (hnf.trans hf') hf' hm hk' hr' ht' hN' (hMN.trans hN') hL hS hth hth hH
  refine ⟨?_, a2, a3, a5, a6, a7, a9⟩
  have hb : 0 < L.sc.b := by unfold Scale.b; positivity
  refine le_trans (le_of_eq ?_) a1
  unfold szlStar
  rw [div_div_eq_mul_div]
  field_simp

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExtInOfValIn
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section

namespace GlobalTheory.LvT.UKS

variable {D : D7} {u : D.what₂.Word} {X : Ch D u}

theorem emb_mem_Fi (X : Ch D u) (i : ℕ) (x : Vl X i) : X.fm.emb i x ∈ X.fm.Fi i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (X.fm.emb_basis i).2, ← (X.fm.lat i).b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem inv_natCast_mem (w : D.what₂.places.Pl) (n : ℕ) (hn : ¬ D.what₂.places.resChar w ∣ n) :
    ((n : D.what₂.LL))⁻¹ ∈ Ow D w := by
  set p := D.what₂.places.resChar w with hp
  have hpr : p.Prime := D.what₂.places.resChar_prime w
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hpr).2 hn
  have hint : ∀ z : ℤ, 0 ≤ D.what₂.places.val w (z : D.what₂.LL) := fun z => intCast_mem (Ow D w) z
  have hbez : ((p : ℤ) * Nat.gcdA p n + (n : ℤ) * Nat.gcdB p n) = 1 := by
    have := Nat.gcd_eq_gcd_ab p n
    rw [hcop.gcd_eq_one] at this
    exact_mod_cast this.symm
  have hbez' : (p : D.what₂.LL) * ((Nat.gcdA p n : ℤ) : D.what₂.LL) + (n : D.what₂.LL) * ((Nat.gcdB p n : ℤ) : D.what₂.LL) = 1 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : D.what₂.LL)) hbez
  have hvp : 0 < D.what₂.places.val w (p : D.what₂.LL) := by
    rw [hp, D.what₂.places.val_resChar w]
    have := D.what₂.places.ramIdx_pos w
    exact_mod_cast this
  have hvn : D.what₂.places.val w (n : D.what₂.LL) = 0 := by
    have h0 : 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := by exact_mod_cast hint n
    by_contra hne
    have hpos : 0 < D.what₂.places.val w (n : D.what₂.LL) := lt_of_le_of_ne h0 (Ne.symm hne)
    have h1 : 0 < D.what₂.places.val w ((p : D.what₂.LL) * ((Nat.gcdA p n : ℤ) : D.what₂.LL)) := by
      rw [AddValuation.map_mul]; exact add_pos_of_pos_of_nonneg hvp (hint _)
    have h2 : 0 < D.what₂.places.val w ((n : D.what₂.LL) * ((Nat.gcdB p n : ℤ) : D.what₂.LL)) := by
      rw [AddValuation.map_mul]; exact add_pos_of_pos_of_nonneg hpos (hint _)
    have h3 := (D.what₂.places.val w).map_lt_add h1 h2
    rw [hbez', AddValuation.map_one] at h3
    exact lt_irrefl _ h3
  show 0 ≤ D.what₂.places.val w ((n : D.what₂.LL))⁻¹
  rw [AddValuation.map_inv, hvn]
  simp

section
variable {i : ℕ} {M : PtModel X i} (Co : M.Coord)

def ExtIn (w : D.what₂.places.Pl) (V : Finset X.A.vT) (φ : Fn X i) : Prop :=
  ∃ Φ, M.IsExt φ Φ ∧ ∀ p, Φ p ∈ Co.valB w V p

variable {Co}

theorem extIn_of_valIn (hC : Co.Ok) {w} (hw : OverT X w) {V} {φ : Fn X i} (hφ : φ ∈ X.fm.Fi i)
    (h : M.ValIn (Co.valB w V) φ) : ExtIn Co w V φ := by
  obtain ⟨Φ, hΦ⟩ := (_root_.GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt D u X i M φ).1 hφ
  refine ⟨Φ, hΦ, fun p => ?_⟩
  obtain ⟨c, g, rfl⟩ := M.rep_surj p
  obtain ⟨y, hy, hyc⟩ := h c
  have : Φ (M.rep c) = y := Subtype.ext ((hΦ.1 c).symm.trans hyc)
  rw [hΦ.2, this]
  exact (_root_.GlobalTheory.LvT.ValEq.valB_laws D u X i M Co hC w hw V _).2.2.2 g y hy

theorem ExtIn.mem_Fi {w V} {φ : Fn X i} (h : ExtIn Co w V φ) : φ ∈ X.fm.Fi i := by
  obtain ⟨Φ, hΦ, -⟩ := h
  exact (_root_.GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt D u X i M φ).2 ⟨Φ, hΦ⟩

theorem ExtIn.valIn {w V} {φ : Fn X i} (h : ExtIn Co w V φ) : M.ValIn (Co.valB w V) φ := by
  obtain ⟨Φ, hΦ, h⟩ := h
  exact fun c => ⟨_, h _, hΦ.1 c⟩

theorem isExt_smul {φ : Fn X i} {Φ} (h : M.IsExt φ Φ) (a : ℂ) : M.IsExt (a • φ) (fun p => a • Φ p) := by
  refine ⟨fun c => ?_, fun g p => ?_⟩
  · show a • φ c = _
    rw [h.1 c]; rfl
  · simp only [h.2, map_smul]

theorem pow_smul_mem (hC : Co.Ok) {w} (hw : OverT X w) {V p y} (hy : y ∈ Co.valB w V p) (n : ℕ) :
    ((X.A.T : ℂ) ^ n) • y ∈ Co.valB w V p := by
  have := (_root_.GlobalTheory.LvT.ValEq.valB_laws D u X i M Co hC w hw V p).2.2.1 ((X.A.T : D.what₂.LL) ^ n)
    (pow_mem (natCast_mem _ _) n) y hy
  simpa using this

theorem ExtIn.pow_smul (hC : Co.Ok) {w} (hw : OverT X w) {V} {φ : Fn X i} (h : ExtIn Co w V φ) (n : ℕ) :
    ExtIn Co w V (((X.A.T : ℂ) ^ n) • φ) := by
  obtain ⟨Φ, hΦ, h⟩ := h
  exact ⟨_, isExt_smul hΦ _, fun p => pow_smul_mem hC hw (h p) n⟩

theorem ExtIn.uop (hC : Co.Ok) {w} (hw : OverT X w) (hs : X.fm.seenP w = true) {V v} (hv : v ∈ V)
    {φ : Fn X i} (h : ExtIn Co w V φ) : ExtIn Co w (V.erase v) (Uop X i v φ) := by
  obtain ⟨Φ, hΦ, h⟩ := h
  refine ⟨_, _root_.GlobalTheory.LvT.uop_isExt D u X i M v φ Φ hΦ, fun p => ?_⟩
  have hv' := _root_.GlobalTheory.LvT.ValEq.valB_laws D u X i M Co hC w hw (V.erase v) p
  refine finsum_mem_induction (fun y => y ∈ Co.valB w (V.erase v) p) hv'.1
    (fun y y' hy hy' => hv'.2.1 y hy y' hy') fun p₁ hp₁ => ?_
  rw [← GlobalTheory.LvT.valB_of_inc D u X i M Co w V v p p₁ hs hv hp₁]
  exact h p₁

theorem ExtIn.uops (hC : Co.Ok) {w} (hw : OverT X w) (hs : X.fm.seenP w = true) {V}
    {φ : Fn X i} (h : ExtIn Co w V φ) (l : List X.A.vT) (hl : l.Nodup) (hV : ∀ v ∈ l, v ∈ V) :
    ExtIn Co w (V \ l.toFinset) (l.foldr (fun v g => (Uop X i v).comp g) LinearMap.id φ) := by
  induction l with
  | nil => simpa using h
  | cons v l ih =>
    rw [List.nodup_cons] at hl
    have h1 := ih hl.2 (fun v' hv' => hV v' (List.mem_cons_of_mem _ hv'))
    have h2 := h1.uop hC hw hs (v := v) (by simp [hl.1, hV v List.mem_cons_self])
    have e : (V \ l.toFinset).erase v = V \ (v :: l).toFinset := by
      ext x; simp; tauto
    rw [e] at h2
    exact h2

theorem ExtIn.drop (hC : Co.Ok) {w} (hw : OverT X w) (hs : X.fm.seenP w = true) {V}
    {φ : Fn X i} (h : ExtIn Co w V φ) (A : Finset X.A.vT) (hA : A ⊆ V) :
    ExtIn Co w (V \ A)
      (((X.A.T : ℂ) ^ (∑ v ∈ A, (PtModel.lamT X i (X.fm.tauOf w v)).w ⟨0, D.R.N_pos i⟩)) • φ) := by
  have hT : (X.A.T : ℂ) ≠ 0 := by exact_mod_cast X.A.T_prime.ne_zero
  induction A using Finset.induction_on with
  | empty => simpa using h
  | insert v A hv ih =>
    obtain ⟨Φ, hΦ, h1⟩ := ih ((Finset.subset_insert _ _).trans hA)
    have e : (V \ A).erase v = V \ insert v A := by
      ext x; simp; tauto
    rw [Finset.sum_insert hv, zpow_add₀ hT, mul_smul, ← e]
    exact ⟨_, isExt_smul hΦ _, fun p => _root_.GlobalTheory.LvT.pow_smul_mem_valB_erase D u X i M Co hC w hw hs _ v
      (by simp [hv, hA (Finset.mem_insert_self _ _)]) p _ (h1 p)⟩

end

theorem extIn_K {i : ℕ} {M : PtModel X i} {M' : PtModel X (i + 1)} {Co : M.Coord} {Co' : M'.Coord}
    (hC' : Co'.Ok) (K : KerPt M M') (hK : K.TgtEq) {w} (hw : OverT X w)
    (hst : ∀ c, ¬ X.A.T ∣ Nat.card (X.C.stab i c)) (a : ℂ) {V}
    (ha : ∀ p p', ∀ y ∈ Co.valB w ∅ p, a • K.k p p' y ∈ Co'.valB w V p')
    {φ : Fn X i} (h : ExtIn Co w ∅ φ) : ExtIn Co' w V (a • KT X i φ) := by
  obtain ⟨Φ, hΦ, h⟩ := h
  refine ⟨_, isExt_smul (GlobalTheory.LvT.isExt_KT D u X i M M' K φ Φ hK hΦ) a, fun p' => ?_⟩
  have hv := _root_.GlobalTheory.LvT.ValEq.valB_laws D u X (i + 1) M' Co' hC' w hw V p'
  simp only [Finset.smul_sum]
  refine Finset.sum_induction _ (fun y => y ∈ Co'.valB w V p') (fun y y' hy hy' => hv.2.1 y hy y' hy') hv.1
    fun c _ => ?_
  rw [smul_comm]
  have := hv.2.2.1 _ (inv_natCast_mem w (Nat.card (X.C.stab i c)) (by rw [show _ = _ from hw]; exact hst c)) _
    (ha _ p' _ (h (M.rep c)))
  simpa [ColumnChain.wt] using this

theorem ukSharp (D : D7) (u : D.what₂.Word) (X : Ch D u) (Lv : LevTie X) (Vt : ValTie Lv) (Kt : KerTie Lv)
    (hK : KerLaws Vt Kt) (hst : StabUnit X) (hW : WtBounds X) : UKSharp X := by
  intro w hw i hi x hx
  have hT : (X.A.T : ℂ) ≠ 0 := by exact_mod_cast X.A.T_prime.ne_zero
  have hC := (Vt i hi.le).2
  have hC' := (Vt (i + 1) hi).2
  have h0 : ExtIn (Vt i hi.le).1 w ∅ (X.fm.emb i x) :=
    extIn_of_valIn hC hw (emb_mem_Fi X i x) ((hC.S_on w hw _ (emb_mem_Fi X i x)).1 ⟨x, hx, rfl⟩)
  suffices h : ExtIn (Vt (i + 1) hi).1 w ∅
      (tpow X (if X.fm.seenP w then 2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m else 0) •
        Uprod X (i + 1) w (KT X i (X.fm.emb i x))) from (hC'.S_on w hw _ h.mem_Fi).2 h.valIn
  by_cases hs : X.fm.seenP w = true
  · have h1 := extIn_K hC' (Kt i hi) (hK.tgt i hi) hw (hst i hi.le) _ (hK.intP i hi w hw hs) h0
    have h2 := h1.uops hC' hw hs (VVT X w).toList (Finset.nodup_toList _) (fun v _ => Finset.mem_univ v)
    have h3 := h2.drop hC' hw hs _ (Finset.Subset.refl _)
    rw [Finset.sdiff_self, Finset.toList_toFinset, map_smul, smul_smul, ← zpow_add₀ hT] at h3
    set e : ℤ := ∑ v ∈ Finset.univ \ VVT X w, (PtModel.lamT X (i + 1) (X.fm.tauOf w v)).w ⟨0, D.R.N_pos _⟩ +
      (((D.R.f * D.R.N i : ℕ) : ℤ) + ∑ τ, X.C.sDiv i τ) with he
    have hle : e ≤ ((2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m : ℕ) : ℤ) := by
      have a1 : ∑ v ∈ Finset.univ \ VVT X w, (PtModel.lamT X (i + 1) (X.fm.tauOf w v)).w ⟨0, D.R.N_pos _⟩ ≤
          ∑ τ, (Wt X τ : ℤ) := by
        rw [← Equiv.sum_comp (X.fm.tauOf w)]
        refine le_trans (Finset.sum_le_sum fun v hv => (hW.2 i hi _).2.2.2 ?_)
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Int.natCast_nonneg _)
        simpa [VVT, hs] using hv
      have a2 : ∑ τ, X.C.sDiv i τ ≤ ∑ τ, (Wt X τ : ℤ) := Finset.sum_le_sum fun τ _ => (hW.2 i hi τ).2.1
      have a3 : D.R.f * D.R.N i ≤ D.R.f * D.R.N D.R.m :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _)
      have a3' : ((D.R.f * D.R.N i : ℕ) : ℤ) ≤ ((D.R.f * D.R.N D.R.m : ℕ) : ℤ) := by exact_mod_cast a3
      rw [he, Nat.cast_add, Nat.cast_mul 2, Nat.cast_sum]
      simp only [Nat.cast_ofNat]
      linarith
    obtain ⟨n, hn⟩ := Int.le.dest hle
    have h4 := h3.pow_smul hC' hw n
    rw [smul_smul, ← zpow_natCast, ← zpow_add₀ hT, add_comm (n : ℤ), hn, zpow_natCast] at h4
    rw [if_pos hs]
    exact h4
  · have hs' : X.fm.seenP w = false := by simpa using hs
    have h1 := extIn_K (V := ∅) hC' (Kt i hi) (hK.tgt i hi) hw (hst i hi.le) 1 (fun p p' y hy => by
      obtain ⟨y', hy', e⟩ := hK.bar i hi w hw hs' p p' y hy
      rw [one_smul, e]
      exact pow_smul_mem hC' hw hy' _) h0
    rw [if_neg hs]
    simpa [tpow, Uprod, VVT, hs'] using h1

end GlobalTheory.LvT.UKS
end
end

