module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Formalism.HermitianLattices.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsNormEqFinprod
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.IdealResProd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
variable {p : HeightOneSpectrum (𝓞 F)}

theorem val_le_iff (A : LocAt F E sig p) (x y : F) :
    valuation A.Fp (A.ιF x) ≤ valuation A.Fp (A.ιF y) ↔ p.valuation F x ≤ p.valuation F y := by
  rw [← A.val, (valuation A.Fp).vle_iff_le]

theorem val_unit {K : Type} [Field K] [ValuativeRel K] (u : (𝒪[K])ˣ) :
    valuation K ((u : 𝒪[K]) : K) = 1 :=
  (Valuation.integer.integers (valuation K)).valuation_unit u

theorem val_unif (A : LocAt F E sig p) {ϖ : 𝒪[A.Fp]} (hϖ : Irreducible ϖ) {π : F}
    (hπ : p.valuation F π = WithZero.exp (-1)) :
    valuation A.Fp (A.ιF π) = valuation A.Fp ϖ := by
  haveI := A.lf
  have h0 : (ϖ : A.Fp) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hv0 : valuation A.Fp ϖ ≠ 0 := by simpa using h0
  have hlt : valuation A.Fp ϖ < 1 := by
    refine lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_
    exact ((Valuation.integer.integers (valuation A.Fp)).isUnit_iff_valuation_eq_one).2 h
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ; exact WithZero.exp_ne_zero hπ.symm
  have hπ1 : valuation A.Fp (A.ιF π) < 1 := by
    have : ¬ valuation A.Fp (A.ιF 1) ≤ valuation A.Fp (A.ιF π) := by
      rw [val_le_iff, hπ, map_one, not_le, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    simpa using this
  apply le_antisymm
  · obtain ⟨k, u, hk⟩ := GlobalTheory.UnramVal.exists_eq_zpow_mul_unit hϖ ((map_ne_zero A.ιF).2 hπ0)
    rw [hk, map_mul, val_unit, mul_one, map_zpow₀] at hπ1 ⊢
    have hk1 : 0 < k := (zpow_lt_one_iff_right_of_lt_one₀ (zero_lt_iff.2 hv0) hlt).1 hπ1
    calc _ ≤ valuation A.Fp ϖ ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ (zero_lt_iff.2 hv0) hlt.le hk1
      _ = _ := zpow_one _
  · have hn : {z : A.Fp | valuation A.Fp z = valuation A.Fp ϖ} ∈ nhds (ϖ : A.Fp) := by
      rw [IsValuativeTopology.mem_nhds_iff]
      refine ⟨Units.mk0 _ hv0, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (valuation A.Fp).map_add_eq_of_lt_left hz
    obtain ⟨y, hy⟩ := A.dense.mem_nhds hn
    have hy : valuation A.Fp (A.ιF y) = valuation A.Fp ϖ := hy
    rw [← hy, val_le_iff, hπ]
    have h1 : ¬ p.valuation F 1 ≤ p.valuation F y := by
      rw [← val_le_iff A, hy, map_one, map_one, not_le]; exact hlt
    rw [map_one, not_le] at h1
    by_cases hz : p.valuation F y = 0
    · rw [hz]; exact zero_le
    · rw [← WithZero.exp_log hz] at h1 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      rw [WithZero.exp_le_exp]; omega

theorem mem_pow_iff (A : LocAt F E sig p) {ϖ : 𝒪[A.Fp]} (hϖ : Irreducible ϖ) (x : 𝓞 F) (n : ℕ) :
    x ∈ p.asIdeal ^ n ↔ valuation A.Fp (A.ιF x) ≤ valuation A.Fp ϖ ^ n := by
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer F
  rw [← val_unif A hϖ hπ, ← map_pow, ← map_pow, val_le_iff, map_pow, hπ, ← WithZero.exp_nsmul,
    ← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
  simp

theorem le_pow_iff (I : Ideal (𝓞 F)) (hI : I ≠ 0) (n : ℕ) :
    I ≤ p.asIdeal ^ n ↔ n ≤ (Associates.mk p.asIdeal).count (Associates.mk I).factors := by
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI) p.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

theorem val_lt_one {K : Type} [Field K] [ValuativeRel K] {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    0 < valuation K ϖ ∧ valuation K ϖ < 1 := by
  have h0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨zero_lt_iff.2 (by simpa using h0), lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_⟩
  exact ((Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one).2 h

theorem mem_span_iff (A : LocAt F E sig p) (L : LocE A.Fp A.Ep) {c : A.Fp} (hc : c ≠ 0) (x : A.Fp) :
    algebraMap A.Fp A.Ep x ∈ Submodule.span L.O {algebraMap A.Fp A.Ep c} ↔
      valuation A.Fp x ≤ valuation A.Fp c := by
  have hun : IsUnit (algebraMap A.Fp A.Ep c) := (IsUnit.mk0 _ hc).map _
  have hx : algebraMap A.Fp A.Ep x = algebraMap A.Fp A.Ep (x / c) * algebraMap A.Fp A.Ep c := by
    rw [← map_mul, div_mul_cancel₀ _ hc]
  have h1 : valuation A.Fp x ≤ valuation A.Fp c ↔ x / c ∈ 𝒪[A.Fp] := by
    rw [Valuation.mem_integer_iff, map_div₀, div_le_one₀ (zero_lt_iff.2 (by simpa using hc))]
  rw [h1, ← GlobalTheory.UnramOrder.algebraMap_mem_iff L, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨o, ho⟩
    rw [hx] at ho
    have : (o : A.Ep) = algebraMap A.Fp A.Ep (x / c) := hun.mul_right_cancel ho
    rw [← this]; exact o.2
  · intro h
    exact ⟨⟨_, h⟩, hx.symm⟩

theorem vE_eq_count (A : LocAt F E sig p) (L : LocE A.Fp A.Ep) {ϖ : 𝒪[A.Fp]} (hϖ : Irreducible ϖ)
    (I : Ideal (𝓞 F)) (hI : I ≠ 0) {c : A.Fp} (hc : c ≠ 0)
    (h : Submodule.span L.O ((fun x : 𝓞 F => A.ιE (algebraMap F E x)) '' (I : Set (𝓞 F))) =
      Submodule.span L.O {algebraMap A.Fp A.Ep c}) :
    vE L ϖ (algebraMap A.Fp A.Ep c) =
      ((Associates.mk p.asIdeal).count (Associates.mk I).factors : ℕ) := by
  haveI := A.lf
  obtain ⟨h0, h1⟩ := val_lt_one hϖ
  have hϖ0 : (ϖ : A.Fp) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  obtain ⟨k, u, rfl⟩ := GlobalTheory.UnramVal.exists_eq_zpow_mul_unit hϖ hc
  rw [GlobalTheory.UnramVal.vE_zpow_mul_unit L hϖ]
  have key : ∀ n : ℕ, n ≤ (Associates.mk p.asIdeal).count (Associates.mk I).factors ↔ (n : ℤ) ≤ k := by
    intro n
    rw [← le_pow_iff I hI]
    have e1 : (n : ℤ) ≤ k ↔ Submodule.span L.O {algebraMap A.Fp A.Ep ((ϖ : A.Fp) ^ k * ((u : 𝒪[A.Fp]) : A.Fp))}
        ≤ Submodule.span L.O {algebraMap A.Fp A.Ep ((ϖ : A.Fp) ^ n)} := by
      rw [Submodule.span_singleton_le_iff_mem, mem_span_iff A L (pow_ne_zero n hϖ0), map_mul, val_unit,
        mul_one, map_zpow₀, map_pow, ← zpow_natCast, zpow_le_zpow_iff_right_of_lt_one₀ h0 h1]
    rw [e1, ← h, Submodule.span_le, Set.image_subset_iff]
    refine forall₂_congr fun x _ => ?_
    rw [mem_pow_iff A hϖ, Set.mem_preimage, A.compat, SetLike.mem_coe,
      mem_span_iff A L (pow_ne_zero n hϖ0), map_pow]
  have hk : 0 ≤ k := by simpa using (key 0).1 (Nat.zero_le _)
  lift k to ℕ using hk
  have a := (key k).2 le_rfl
  have b := (key _).1 le_rfl
  omega

theorem absNorm_eq_finprod (I : Ideal (𝓞 F)) (hI : I ≠ 0) :
    ∏ᶠ p : HeightOneSpectrum (𝓞 F), (Ideal.absNorm p.asIdeal : ℝ) ^
      (Associates.mk p.asIdeal).count (Associates.mk I).factors = (Ideal.absNorm I : ℝ) := by
  have := map_finprod ((Nat.castRingHom ℝ).toMonoidHom.comp (Ideal.absNorm (S := 𝓞 F)).toMonoidHom)
    (Ideal.hasFiniteMulSupport hI)
  rw [Ideal.finprod_heightOneSpectrum_factorization hI] at this
  simpa [HeightOneSpectrum.maxPowDividing] using this.symm

theorem discr_and_level : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ ϖ : ∀ p, 𝒪[(A.loc p).Fp], (∀ p, Irreducible (ϖ p)) → (∀ c : ∀ p, ((A.loc p).Fp)ˣ, (∀ p, Submodule.span (A.L p).O ((fun x : 𝓞 F => (A.loc p).ιE (algebraMap F E x)) '' (differentIdeal ℤ (𝓞 F) : Set (𝓞 F))) = Submodule.span (A.L p).O {algebraMap (A.loc p).Fp (A.loc p).Ep (c p)}) → ∏ᶠ p, (resQ (ϖ p) : ℝ) ^ vE (A.L p) (ϖ p) (algebraMap (A.loc p).Fp (A.loc p).Ep (c p)) = |(NumberField.discr F : ℝ)|) ∧ ∀ g : ℕ, g ≠ 0 → (∀ p : HeightOneSpectrum (𝓞 F), (g : 𝓞 F) ∈ p.asIdeal → ∃ u : (𝒪[(A.loc p).Fp])ˣ, (g : (A.loc p).Fp) = ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) * (ϖ p : (A.loc p).Fp)) → ∏ᶠ p : HeightOneSpectrum (𝓞 F), (if (g : 𝓞 F) ∈ p.asIdeal then (resQ (ϖ p) : ℝ) else 1) = (g : ℝ) ^ Module.finrank ℚ F := by
  intro F E _ _ _ _ _ sig A ϖ hϖ
  have hq : ∀ p, resQ (ϖ p) = Ideal.absNorm p.asIdeal := fun p => (GlobalTheory.HL.PlacesInt.integers_local A).2.2.2 p _ (hϖ p)
  refine ⟨fun c hc => ?_, fun g hg hu => ?_⟩
  · have hI : differentIdeal ℤ (𝓞 F) ≠ 0 := by
      intro h
      have := absNorm_differentIdeal F (𝓞 F)
      rw [h, map_zero] at this
      exact discr_ne_zero F (Int.natAbs_eq_zero.1 this.symm)
    have := absNorm_eq_finprod _ hI
    rw [absNorm_differentIdeal F (𝓞 F), Nat.cast_natAbs, Int.cast_abs] at this
    rw [← this]
    refine finprod_congr fun p => ?_
    rw [vE_eq_count (A.loc p) (A.L p) (hϖ p) _ hI (c p).ne_zero (hc p), zpow_natCast, hq]
  · have hg' : (g : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hg
    have hI : Ideal.span {(g : 𝓞 F)} ≠ 0 := by simpa using hg
    have := absNorm_eq_finprod _ hI
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Nat.cast_pow] at this
    rw [← this]
    refine finprod_congr fun p => ?_
    have key := le_pow_iff (p := p) _ hI
    simp only [Ideal.span_singleton_le_iff_mem] at key
    split_ifs with h
    · obtain ⟨u, hu⟩ := hu p h
      obtain ⟨h0, h1⟩ := val_lt_one (hϖ p)
      have a := (key 1).1 (by simpa using h)
      have b : ¬ (g : 𝓞 F) ∈ p.asIdeal ^ 2 := by
        rw [mem_pow_iff (A.loc p) (hϖ p)]
        have e : (A.loc p).ιF ((g : 𝓞 F) : F) = (g : (A.loc p).Fp) := by simp
        rw [e, hu, map_mul, val_unit, one_mul, not_le]
        calc _ < valuation (A.loc p).Fp (ϖ p) ^ 1 := pow_lt_pow_right_of_lt_one₀ h0 h1 (by norm_num)
          _ = _ := pow_one _
      rw [key] at b
      have : (Associates.mk p.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 F)})).factors = 1 := by omega
      rw [this, pow_one, hq]
    · have b : ¬ (g : 𝓞 F) ∈ p.asIdeal ^ 1 := by simpa using h
      rw [key] at b
      have : (Associates.mk p.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 F)})).factors = 0 := by omega
      rw [this, pow_zero]

end GlobalTheory.IdealResProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasicInequality
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.BasicIneq

theorem amp_le_mass {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ)
    (S : Frames L r k) (d : S.Datum) (P : Submodule L.O S.V → Prop) :
    ENNReal.ofReal (‖S.amp d P‖) ≤ S.mass d P := by
  rw [ofReal_norm_eq_enorm]
  unfold Frames.amp Frames.mass
  refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun o => ?_)
  split_ifs with h
  · obtain ⟨p, hp⟩ := h.1
    have h1 : ‖S.om d o.out‖ = 1 := (WitIndep.witness_independence L r k S d _ _ _ hp).2.2.2.2
    have h2 : 0 ≤ S.mu o.out := by
      unfold Frames.mu invVol
      positivity
    rw [← ofReal_norm_eq_enorm, norm_mul, h1, mul_one, Complex.norm_real, Real.norm_of_nonneg h2]
  · simp

theorem basic_inequality : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 1 ≤ k → (∀ d P, ENNReal.ofReal (‖S.amp d P‖) ≤ S.mass d P) ∧ ∀ (P : S.Datum → Submodule L.O S.V → Prop) (B ε : ℝ), 0 ≤ ε → (∀ d, S.mass d (P d) ≤ ENNReal.ofReal (B)) → (∀ d, ENNReal.ofReal (‖S.amp d (P d)‖) ≤ ENNReal.ofReal (ε) * S.mass d (P d)) → S.ampSq P ≤ ENNReal.ofReal (ε ^ 2 * B) * S.sumData fun d => S.mass d (P d) := by
  intro F _ _ _ _ _ E _ _ _ L r k S _
  refine ⟨amp_le_mass L r k S, fun P B ε hε hB hA => ?_⟩
  unfold Frames.ampSq Frames.sumData
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun o => ?_
  rw [mul_left_comm]
  refine mul_le_mul_right ?_ _
  beta_reduce
  rw [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_mul (sq_nonneg ε), ENNReal.ofReal_pow hε]
  calc ENNReal.ofReal ‖S.amp o.out (P o.out)‖ ^ 2
      ≤ (ENNReal.ofReal ε * S.mass o.out (P o.out)) ^ 2 := by
        gcongr
        exact hA _
    _ = ENNReal.ofReal ε ^ 2 * S.mass o.out (P o.out) * S.mass o.out (P o.out) := by ring
    _ ≤ ENNReal.ofReal ε ^ 2 * ENNReal.ofReal B * S.mass o.out (P o.out) := by
        gcongr
        exact hB _

end GlobalTheory.HL.BasicIneq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CloseOnCompletedLatticeOfCloseOnFrames
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LatClose

section
variable {K R : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [CommRing R] [Algebra K R] [TopologicalSpace R]
  (L : LocE K R) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) R)

theorem hf_add_right (x a b : Fin n → R) : hf L Hm x (a + b) = hf L Hm x a + hf L Hm x b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_right (x : Fin n → R) (c : R) (a : Fin n → R) : hf L Hm x (c • a) = L.cj c * hf L Hm x a := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_zero_right (x : Fin n → R) : hf L Hm x 0 = 0 := by simp [hf]
end

theorem form_sub_sum {E : Type} [Field E] {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} [Fintype ι] (x : Fin n → E) (a : ι → E)
    (v : ι → Fin n → E) (s : Fin n → E) :
    ∑ i, ∑ j, (x - ∑ k, a k • v k) i * Hm i j * s j =
      (∑ i, ∑ j, x i * Hm i j * s j) - ∑ k, a k * ∑ i, ∑ j, v k i * Hm i j * s j := by
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  calc _ = ∑ i, ∑ k, ∑ j, a k * v k i * Hm i j * s j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem bc_add (x y : Fin n → E) : A.bc p (x + y) = A.bc p x + A.bc p y := by
  funext i; simp [Places.bc]
theorem bc_smul (c : E) (x : Fin n → E) : A.bc p (c • x) = (A.loc p).ιE c • A.bc p x := by
  funext i; simp [Places.bc]
theorem bc_sum {ι : Type} (s : Finset ι) (x : ι → Fin n → E) :
    A.bc p (∑ i ∈ s, x i) = ∑ i ∈ s, A.bc p (x i) := by
  funext j; simp [Places.bc, Finset.sum_apply]
theorem bc_mem_lat (Λ : Submodule (𝓞 E) (Fin n → E)) {x : Fin n → E} (hx : x ∈ Λ) :
    A.bc p x ∈ A.lat p Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem step (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {n m : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (D : ℤ) (h : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))
    (g : Fin m → Fin n → E) (Mx : Matrix (Fin m) (Fin m) (A.loc p).Ep) (t : (A.loc p).Fp)
    (hg : ∀ j, h (A.bc p (g j)) = ∑ i, Mx i j • A.bc p (g i))
    (hMx : ∀ i j, ∃ o ∈ (A.L p).O, (Mx - 1) i j =
      algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o)
    (hgΛ : ∀ i, (D : 𝓞 E) • g i ∈ Λ) (a : E) (ha : ∃ o : 𝓞 E, (D : E) ^ 2 * a = o) (j : Fin m) :
    ∃ z ∈ A.lat p Λ, (A.loc p).ιE a • (h (A.bc p (g j)) - A.bc p (g j)) =
      algebraMap (A.loc p).Fp (A.loc p).Ep t • z := by
  obtain ⟨oa, hoa⟩ := ha
  choose o ho hoeq using hMx
  have hdiff : h (A.bc p (g j)) - A.bc p (g j) = ∑ i, (Mx - 1) i j • A.bc p (g i) := by
    rw [hg]
    simp [Matrix.sub_apply, Matrix.one_apply, sub_smul, Finset.sum_sub_distrib]
  refine ⟨∑ i, (⟨o i j, ho i j⟩ : (A.L p).O) • A.bc p (oa • ((D : 𝓞 E) • g i)),
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bc_mem_lat A p Λ (Λ.smul_mem _ (hgΛ i))), ?_⟩
  rw [hdiff, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : (oa • ((D : 𝓞 E) • g i) : Fin n → E) = ((D : E) ^ 3 * a) • g i := by
    change (oa : E) • (((D : 𝓞 E) : E) • g i) = _
    have hD : ((D : 𝓞 E) : E) = (D : E) := by simp
    rw [smul_smul, ← hoa, hD]
    congr 1
    ring
  rw [Subring.smul_def, e1, bc_smul, hoeq, smul_smul, smul_smul, smul_smul]
  congr 1
  simp only [map_mul, map_pow, map_intCast]
  ring
end

theorem close_on_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (Λ : G.Lt) (D : ℤ) (p : HeightOneSpectrum (𝓞 F)) (h : (G.S p).GLV) (M M' : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep) (t : (A.loc p).Fp), (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j)) = 1 → (∀ k l, ∃ o : 𝓞 E, (D : E) * (Matrix.of fun k l : Fin (r + 1) ⊕ Fin (r + 1) => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j))⁻¹ k l = o) → (∀ x ∈ Λ, ∀ l, ∃ o : 𝓞 E, (D : E) * ∑ a, ∑ b, x a * G.Hm a b * sig (Sum.elim G.f G.f' l b) = o) → (∀ l, (D : 𝓞 E) • Sum.elim G.f G.f' l ∈ Λ) → h ∈ (G.S p).St → (∀ j, h (A.bc p (G.f j)) = ∑ i, M i j • A.bc p (G.f i)) → (∀ j, h (A.bc p (G.f' j)) = ∑ i, M' i j • A.bc p (G.f' i)) → (∀ i j, ∃ o ∈ (A.L p).O, (M - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o) → (∀ i j, ∃ o ∈ (A.L p).O, (M' - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (t * (D : (A.loc p).Fp) ^ 3) * o) → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, h x - x = algebraMap (A.loc p).Fp (A.loc p).Ep t • y := by
  intro F E _ _ _ _ _ sig A r k G Λ D p h M M' t hΓ hΓD hb hDu hh hM hM' hM1 hM1'
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  have key : ∀ l ∈ Λ, ∃ y ∈ A.lat p Λ,
      h (A.bc p l) - A.bc p l = algebraMap (A.loc p).Fp (A.loc p).Ep t • y := by
    intro l hl
    set Γ : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
      Matrix.of fun k l => ∑ i, ∑ j, Sum.elim G.f G.f' k i * G.Hm i j * sig (Sum.elim G.f G.f' l j)
      with hΓdef
    have hbl : ∀ m, ∃ o : 𝓞 E, (D : E) * ∑ i, ∑ j, l i * G.Hm i j * sig (Sum.elim G.f G.f' m j) = o :=
      hb l hl
    choose ob hob using hbl
    choose og hog using hΓD
    let b : Fin (r + 1) ⊕ Fin (r + 1) → E := fun m => ∑ i, ∑ j, l i * G.Hm i j * sig (Sum.elim G.f G.f' m j)
    let α := Matrix.vecMul b Γ⁻¹
    let w := l - ∑ q, α q • Sum.elim G.f G.f' q
    have hw0 : ∀ m, ∑ i, ∑ j, w i * G.Hm i j * sig (Sum.elim G.f G.f' m j) = 0 := by
      intro m
      rw [form_sub_sum]
      have e : ∑ q, α q * ∑ i, ∑ j, Sum.elim G.f G.f' q i * G.Hm i j * sig (Sum.elim G.f G.f' m j) =
          Matrix.vecMul α Γ m := rfl
      rw [e, Matrix.vecMul_vecMul, hΓ, Matrix.vecMul_one, sub_self]
    have hwloc : ∀ m, hf (A.L p) (G.S p).Hm (A.bc p w) (A.bc p (Sum.elim G.f G.f' m)) = 0 := by
      intro m
      rw [G.Hm_eq p, (RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1, hw0, map_zero]
    have hwW : A.bc p w ∈ (G.S p).W0 := by
      have hME : (G.S p).ME = Submodule.span _ (Set.range (Sum.elim (G.S p).f (G.S p).f')) := by
        rw [Frames.ME, FrameStab.spanTo_top, FrameStab.spanTo_top, Set.Sum.elim_range, Submodule.span_union]
      change ∀ y ∈ (G.S p).ME, hf (A.L p) (G.S p).Hm (A.bc p w) y = 0
      intro y hy
      rw [hME] at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨q, rfl⟩ := hy
        rcases q with a | a
        · have e := G.f_eq p a
          have h0 := hwloc (Sum.inl a)
          simp only [Sum.elim_inl] at h0 ⊢
          rw [← e, hf_smul_right, AlgEquiv.commutes] at h0
          exact ((((G.c p).isUnit.pow _).map (algebraMap _ _)).mul_right_eq_zero).1 h0
        · have e := G.f'_eq p a
          have h0 := hwloc (Sum.inr a)
          simp only [Sum.elim_inr] at h0 ⊢
          rw [← e, hf_smul_right, AlgEquiv.commutes] at h0
          exact ((((G.c p).isUnit.pow _).map (algebraMap _ _)).mul_right_eq_zero).1 h0
      | zero => exact hf_zero_right _ _ _
      | add x y _ _ hx hy => rw [hf_add_right, hx, hy, add_zero]
      | smul c x _ hx => rw [hf_smul_right, hx, mul_zero]
    have hhw : h (A.bc p w) = A.bc p w := (FrameStab.stab_eq (A.L p) r k (G.S p)).1 h hh _ hwW
    have hl' : l = w + ∑ q, α q • Sum.elim G.f G.f' q := by simp only [w, sub_add_cancel]
    have hsplit : h (A.bc p l) - A.bc p l = ∑ q, (A.loc p).ιE (α q) •
        (h (A.bc p (Sum.elim G.f G.f' q)) - A.bc p (Sum.elim G.f G.f' q)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hl', bc_add, bc_sum, map_add (f := _), map_sum, hhw]
      simp only [bc_smul, map_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    have hα : ∀ q, ∃ o : 𝓞 E, (D : E) ^ 2 * α q = o := by
      intro q
      refine ⟨∑ m, ob m * og m q, ?_⟩
      have e : ((∑ m, ob m * og m q : 𝓞 E) : E) = ∑ m, ((ob m : 𝓞 E) : E) * ((og m q : 𝓞 E) : E) := by
        simp
      rw [e]
      simp only [α, Matrix.vecMul, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      linear_combination ((D : E) * Γ⁻¹ m q) * hob m + ((ob m : 𝓞 E) : E) * hog m q
    have hper : ∀ q, ∃ z ∈ A.lat p Λ, (A.loc p).ιE (α q) •
        (h (A.bc p (Sum.elim G.f G.f' q)) - A.bc p (Sum.elim G.f G.f' q)) =
          algebraMap (A.loc p).Fp (A.loc p).Ep t • z := by
      rintro (j | j)
      · exact step A p Λ D h G.f M t hM hM1 (fun i => hDu (Sum.inl i)) (α (Sum.inl j)) (hα _) j
      · exact step A p Λ D h G.f' M' t hM' hM1' (fun i => hDu (Sum.inr i)) (α (Sum.inr j)) (hα _) j
    choose z hz hze using hper
    exact ⟨∑ q, z q, Submodule.sum_mem _ fun q _ => hz q, by
      rw [hsplit, Finset.smul_sum]; exact Finset.sum_congr rfl fun q _ => hze q⟩
  intro x hx
  change x ∈ Submodule.span _ _ at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨l, hl, rfl⟩ := hx; exact key l hl
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb' =>
    obtain ⟨y1, hy1, e1⟩ := ha
    obtain ⟨y2, hy2, e2⟩ := hb'
    exact ⟨y1 + y2, add_mem hy1 hy2, by rw [map_add (f := _), smul_add, ← e1, ← e2]; abel⟩
  | smul c a _ ha =>
    obtain ⟨y, hy, e⟩ := ha
    refine ⟨c • y, Submodule.smul_mem _ c hy, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, map_smul, ← smul_sub, e, smul_comm]

end GlobalTheory.HL.LatClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeLeSumVolumeOfCover
section
open MeasureTheory NumberField Finset

namespace GlobalTheory


open Pointwise in
theorem covolume_le_sum_volume_of_cover (ι : Type) [Fintype ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (κ : Type) (T : Finset κ) (A : κ → Set (ι → ℝ))
    (_hA : ∀ k, MeasurableSet (A k))
    (hcov : ∀ t : ι → ℝ, ∃ k ∈ T, ∃ l ∈ L, t + l ∈ A k) :
    ENNReal.ofReal (ZLattice.covolume L volume) ≤ ∑ k ∈ T, volume (A k) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  have hF := ZLattice.isAddFundamentalDomain b (volume : Measure (ι → ℝ))
  set F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L) with hFdef
  haveI : Countable L := b.repr.toEquiv.countable_iff.2 inferInstance
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume hF]
  refine le_trans ENNReal.ofReal_toReal_le ?_
  refine le_trans ?_ (measure_biUnion_finset_le T A)
  set U := ⋃ k ∈ T, A k with hU
  haveI : MeasurableConstVAdd L (ι → ℝ) :=
    ⟨fun c => by
      change Measurable fun x : ι → ℝ => (c : ι → ℝ) + x
      exact measurable_const_add _⟩
  haveI : VAddInvariantMeasure L (ι → ℝ) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : ι → ℝ) s⟩
  rw [hF.measure_eq_tsum U]
  refine le_trans (measure_mono ?_) (measure_iUnion_le _)
  intro t ht
  obtain ⟨k, hk, l, hl, htl⟩ := hcov t
  refine Set.mem_iUnion.2 ⟨-(⟨l, hl⟩ : L), ?_, ht⟩
  rw [Set.mem_neg_vadd_set_iff]
  have : (⟨l, hl⟩ : L) +ᵥ t = t + l := by
    change l + t = t + l
    exact add_comm _ _
  rw [this]
  exact Set.mem_biUnion hk htl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCharactersAgreeCommonStabiliserStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_characters_agree_commonStabiliser : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.St, S.psi h = S.psi' h := by
  first | exact @GlobalTheory.HL.CharAgree.psi_eq_psi' | exact GlobalTheory.HL.CharAgree.psi_eq_psi' | (intros; apply GlobalTheory.HL.CharAgree.psi_eq_psi' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerDataStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), Function.Injective c.dat ∧ (∀ g ∈ P.UW0, ∀ d d', LocNG.Datum.Moves g d d' ↔ c.grp g • c.dat d = c.dat d') ∧ (∀ d d', LocNG.Datum.Rel d d' ↔ ∃ h ∈ S.H0, h • c.dat d = c.dat d') ∧ (∀ d g, g ∈ LocNG.Datum.Stab d ↔ c.grp g ∈ S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) ∧ ∀ d0 d, LocNG.Datum.wt d0 d = invVol (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d0)) (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) := by
  first | exact @GlobalTheory.HL.CoordDatum.transport | exact GlobalTheory.HL.CoordDatum.transport | (intros; apply GlobalTheory.HL.CoordDatum.transport <;> assumption)
end

