module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitConjSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def OrbitConjSum.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (g : (Coord n → ℂ) → ℝ), BlockNonzero x →
    (∀ (c : ι → ℂ) (z : Coord n → ℂ), (∀ k, c k ≠ 0) →
      z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x) → g (fun p ↦ c p.1 * z p) = g z) →
    (Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) *
        ∑ σ : coordField x →+* ℂ, g (fun p ↦ σ (coordVec x p.1 p.2)) =
      (Module.finrank ℚ (coordField x) : ℝ) *
        ∑ᶠ q : projPts (ι := blockIdx n) (orbitIdeal x),
          g (Quot.out q : Geo.mcPts (ι := blockIdx n) (orbitIdeal x))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PCentredRingNormal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField IsDedekindDomain

namespace CentredRingNormal

variable {L : Type} [Field L] [NumberField L]


omit [NumberField L] in
theorem isIntegral_of_comp {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R L] [Algebra R' L]
    (f : R →+* R') (hf : (algebraMap R' L).comp f = algebraMap R L) {x : L}
    (hx : IsIntegral R x) : IsIntegral R' x := by
  obtain ⟨p, hp, hpx⟩ := hx
  exact ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map, hf]; exact hpx⟩

theorem mem_valuationSubring_iff_place (v : HeightOneSpectrum (𝓞 L)) (x : L) :
    x ∈ (v.valuation L).valuationSubring ↔ FinitePlace.mk v x ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, FinitePlace.mk_apply, FinitePlace.norm_embedding',
    NNReal.coe_le_one,
    ← map_one (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v)),
    (WithZeroMulInt.toNNReal_strictMono
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le]

theorem exists_place_of_valuationSubring (V : ValuationSubring L) (hV : V ≠ ⊤) :
    ∃ w : FinitePlace L, ∀ x : L, x ∈ V ↔ w x ≤ 1 := by
  have hint : ∀ a : 𝓞 L, algebraMap (𝓞 L) L a ∈ V := fun a ↦ by
    have h : IsIntegral V (algebraMap (𝓞 L) L a) :=
      isIntegral_of_comp (Int.castRingHom V) (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe a)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
    rw [← hy]
    exact y.2
  let φ : 𝓞 L →+* V := (algebraMap (𝓞 L) L).codRestrict V hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal V).comap φ
  have hinv : ∀ s : 𝓞 L, s ∉ P → (algebraMap (𝓞 L) L s)⁻¹ ∈ V := fun s hs ↦ by
    have h1 : V.valuation (φ s : L) = 1 := by
      rcases V.valuation_lt_one_or_eq_one (φ s) with h | h
      · exact absurd ((V.valuation_lt_one_iff (φ s)).mpr h) hs
      · exact h
    rw [← V.valuation_le_one_iff, map_inv₀]
    change (V.valuation (φ s : L))⁻¹ ≤ 1
    rw [h1, inv_one]
  have hPne : P ≠ ⊥ := by
    intro hP
    apply hV
    ext x
    simp only [ValuationSubring.mem_top, iff_true]
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
    have hbP : b ∉ P := by
      rw [hP, Ideal.mem_bot]
      exact nonZeroDivisors.ne_zero hb
    rw [div_eq_mul_inv]
    exact mul_mem (hint a) (hinv b hbP)
  let v : HeightOneSpectrum (𝓞 L) := ⟨P, Ideal.comap_isPrime _ _, hPne⟩
  have hle : HeightOneSpectrum.valuationSubringAtPrime L v ≤ V := by
    rintro x ⟨a, s, hs, rfl⟩
    exact mul_mem (hint a) (hinv s hs)
  refine ⟨FinitePlace.mk v, fun x ↦ ?_⟩
  rw [← mem_valuationSubring_iff_place,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring (K := L) v,
    ValuationSubring.eq_of_le_of_ne_top _ hle hV]

theorem absCentredAt_of_le_one (O : Subalgebra ℤ L) [IsFractionRing O L] (m : Ideal O) [m.IsMaximal]
    (w : FinitePlace L)
    (hA : ∀ y ∈ Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors,
      w y ≤ 1)
    (x : L) (hx : 1 < w x) : AbsCentredAt O m fun t ↦ w t := by
  have hO : ∀ u : O, w u ≤ 1 := fun u ↦ hA _ (Subalgebra.algebraMap_mem _ u)
  let q : Ideal O :=
    { carrier := {u | w u < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb ↦ by
        change w ((a : L) + b) < 1
        exact (FinitePlace.add_le w _ _).trans_lt (max_lt ha hb)
      smul_mem' := fun c a ha ↦ by
        change w ((c : L) * a) < 1
        rw [map_mul]
        exact (mul_le_of_le_one_left (apply_nonneg w _) (hO c)).trans_lt ha }
  have hmem : ∀ u : O, u ∈ q ↔ w u < 1 := fun _ ↦ Iff.rfl
  have hq_prime : q.IsPrime := by
    refine ⟨fun h ↦ ?_, fun {a b} hab ↦ ?_⟩
    · have h1 : (1 : O) ∈ q := h ▸ Submodule.mem_top
      rw [hmem] at h1
      simp at h1
    · by_contra hne
      rw [not_or, hmem, hmem, not_lt, not_lt] at hne
      rw [hmem] at hab
      change w ((a : L) * b) < 1 at hab
      rw [map_mul, le_antisymm (hO a) hne.1, le_antisymm (hO b) hne.2, one_mul] at hab
      exact lt_irrefl _ hab
  have hq_ne : q ≠ ⊥ := by
    intro hq
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    have hb1 : w (algebraMap O L b) = 1 := by
      refine le_antisymm (hO b) (not_lt.mp fun h ↦ nonZeroDivisors.ne_zero hb ?_)
      rw [← Ideal.mem_bot, ← hq]
      exact h
    rw [map_div₀, hb1, div_one] at hx
    exact absurd (hO a) (not_le.mpr hx)
  have hq_max : q.IsMaximal := SubringPrimeMaximal.proof L O q hq_prime hq_ne
  have hqm : q ≤ m := fun u hu ↦ by
    by_contra hum
    have hu0 : (u : L) ≠ 0 := fun h ↦ hum (by rw [show u = 0 from Subtype.ext h]; exact m.zero_mem)
    have hinv : w (u : L)⁻¹ ≤ 1 := hA _ ⟨1, u, hum, by rw [map_one, one_mul]; rfl⟩
    have hprod : w (u : L) * w (u : L)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hu0, map_one]
    have hu' : w u < 1 := hu
    nlinarith [apply_nonneg w (u : L), apply_nonneg w (u : L)⁻¹]
  have hqe : q = m := hq_max.eq_of_le (Ideal.IsMaximal.ne_top ‹_›) hqm
  refine ⟨hO, fun u ↦ ?_⟩
  rw [← hqe]
  exact (hmem u).symm

theorem proof : CentredRingNormal.Statement := by
  intro L _ _ O _ _ m _
  set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors with hAdef
  have hcent : ∀ w : FinitePlace L, AbsCentredAt O m (fun t ↦ w t) → ∀ y ∈ A, w y ≤ 1 := by
    rintro w ⟨hO, hm⟩ y ⟨a, s, hs, rfl⟩
    have hs1 : w (algebraMap O L s) = 1 := le_antisymm (hO s) (not_lt.mp fun h ↦ hs ((hm s).mp h))
    rw [map_mul, map_inv₀, hs1, inv_one, mul_one]
    exact hO a
  ext x
  rw [mem_placesRing, Subalgebra.mem_toSubring, mem_integralClosure_iff]
  constructor
  · intro hx
    have hall : x ∈ ⨅ V : {V : ValuationSubring L // (A : Set L) ⊆ V.toSubring}, V.1.toSubring := by
      refine Subring.mem_iInf.mpr fun ⟨V, hAV⟩ ↦ ?_
      by_cases hV : V = ⊤
      · have h : x ∈ V := hV ▸ ValuationSubring.mem_top x
        exact h
      obtain ⟨w, hw⟩ := exists_place_of_valuationSubring V hV
      by_contra hxV
      have hwx : 1 < w x := not_le.mp fun h ↦ hxV ((hw x).mpr h)
      have hc := absCentredAt_of_le_one O m w (fun y hy ↦ (hw y).mp (hAV hy)) x hwx
      exact hxV ((hw x).mpr (hx w hc))
    rw [iInf_valuationSubring_superset, Subalgebra.mem_toSubring, mem_integralClosure_iff] at hall
    refine isIntegral_of_comp ((algebraMap (Subring.closure (A : Set L)) L).codRestrict A fun y ↦ ?_) (RingHom.ext fun _ ↦ rfl) hall
    exact (Subring.closure_le (t := A.toSubring)).mpr (fun z hz ↦ hz) y.2
  · intro hx w hw
    let v := FinitePlace.maximalIdeal w
    have hAV : ∀ y ∈ A, y ∈ (v.valuation L).valuationSubring := fun y hy ↦ by
      rw [mem_valuationSubring_iff_place, FinitePlace.mk_maximalIdeal]
      exact hcent w hw y hy
    have hxV : IsIntegral (v.valuation L).valuationSubring x :=
      isIntegral_of_comp ((algebraMap A L).codRestrict _ fun y ↦ hAV y y.2)
        (RingHom.ext fun _ ↦ rfl) hx
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxV
    have h := (mem_valuationSubring_iff_place v x).mp (hy ▸ y.2)
    rwa [FinitePlace.mk_maximalIdeal] at h

end CentredRingNormal

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalLengthPlaces
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem LocalLengthPlaces.proof (hC : LocalQuotCard.Statement) (hF : CentredPlacesFinite.Statement)
    (hE : LocalQuotCentred.Statement) (hP : PlacesRingQuot.Statement) :
    LocalLengthPlaces.Statement := by
  intro L _ _ O hft hfr m _ f hf
  have hfS : (f : L) ∈ placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t} :=
    fun w hw ↦ hw.1 f
  have hg : (⟨f, hfS⟩ : placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t}) ≠ 0 :=
    fun h ↦ hf (Subtype.ext (by simpa using congrArg Subtype.val h))
  rw [← Real.log_pow, ← Nat.cast_pow, ← hC L O hft hfr m f hf, hE L O hft hfr m f hf ⟨f, hfS⟩ rfl]
  exact hP L _ (hF L O hft hfr m) ⟨f, hfS⟩ hg

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalQuotCard
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField IsLocalRing

theorem LocalQuotCard.proof : LocalQuotCard.Statement := by
  intro L _ _ O hft _ m _ f hf
  have : IsNoetherianRing O := Algebra.FiniteType.isNoetherianRing ℤ O
  have hO : Ring.KrullDimLE 1 O := Ring.KrullDimLE.mk₁' fun q hq0 hq ↦
    SubringPrimeMaximal.proof L O q hq hq0
  let R := Localization.AtPrime m
  have : Ring.KrullDimLE 1 R := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height m R]
    exact Ideal.height_le_ringKrullDim_of_isPrime.trans (Ring.krullDimLE_iff.mp hO)
  have hf' : algebraMap O R f ≠ 0 := by
    intro h
    apply hf
    exact IsLocalization.injective R m.primeCompl_le_nonZeroDivisors (by simpa using h)
  have hspan : Ideal.span {algebraMap O R f} = LinearMap.range (LinearMap.lsmul R R (algebraMap O R f)) := by
    ext z
    simp [Ideal.mem_span_singleton', LinearMap.mem_range, mul_comm]
  have hfin : Module.length R (R ⧸ Ideal.span {algebraMap O R f}) ≠ ⊤ := by
    rw [hspan]
    exact ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top R hf'
  unfold localQuotLength
  rw [Inter.card_eq_card_residueField_pow_length _ hfin]
  congr 1
  exact Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal m R).toEquiv.symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalQuotCentred
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem card_quot_span_eq_relIndex {L : Type*} [CommRing L] (R : Subring L) (x : R) :
    Nat.card (R ⧸ Ideal.span {x}) =
      (R.toAddSubgroup.map (AddMonoidHom.mulLeft (x : L))).relIndex R.toAddSubgroup := by
  have h : (Ideal.span {x}).toAddSubgroup =
      (R.toAddSubgroup.map (AddMonoidHom.mulLeft (x : L))).addSubgroupOf R.toAddSubgroup := by
    ext y
    simp only [Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, by simp [mul_comm]⟩
    · rintro ⟨a, ha, hy⟩
      exact ⟨⟨a, ha⟩, Subtype.ext (by simpa [mul_comm] using hy)⟩
  rw [AddSubgroup.relIndex, ← h]
  rfl

theorem relIndex_mulLeft_eq {L : Type*} [CommRing L] [IsDomain L] (A B : Subring L) (hAB : A ≤ B)
    (hfin : A.toAddSubgroup.relIndex B.toAddSubgroup ≠ 0) (f : L) (hf : f ≠ 0) (hfA : f ∈ A) :
    (A.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex A.toAddSubgroup =
      (B.toAddSubgroup.map (AddMonoidHom.mulLeft f)).relIndex B.toAddSubgroup := by
  have hinj : Function.Injective (AddMonoidHom.mulLeft f) := mul_right_injective₀ hf
  have h1 : A.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ B.toAddSubgroup.map (AddMonoidHom.mulLeft f) :=
    AddSubgroup.map_mono hAB
  have h2 : B.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ B.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact B.mul_mem (hAB hfA) hy
  have h3 : A.toAddSubgroup.map (AddMonoidHom.mulLeft f) ≤ A.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact A.mul_mem hfA hy
  have e1 := AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2
  have e2 := AddSubgroup.relIndex_mul_relIndex _ _ _ h3 (show A.toAddSubgroup ≤ B.toAddSubgroup from hAB)
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hinj, ← e2, mul_comm] at e1
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hfin) e1).symm

theorem LocalQuotCentred.proof (hN : CentredRingNormal.Statement) (hI : LocalNormalIndex.Statement) :
    LocalQuotCentred.Statement := by
  intro L _ _ O hft hfr m _ f hf g hg
  set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors with hAdef
  have hS := hN L O hft m
  have hAI := hI L O hft m
  set P := placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t} with hPdef
  have hAP : A.toSubring ≤ P := by
    rw [hS]
    intro x hx
    exact (isIntegral_algebraMap : IsIntegral A (algebraMap A L ⟨x, hx⟩))
  have hfin : A.toSubring.toAddSubgroup.relIndex P.toAddSubgroup ≠ 0 := by
    rw [hS]
    exact hAI
  let e : Localization.AtPrime m ≃ₐ[O] A := IsLocalization.algEquiv m.primeCompl _ _
  have h1 : Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) f}) =
      Nat.card (A.toSubring ⧸ Ideal.span {(algebraMap O A f : A.toSubring)}) := by
    refine Nat.card_congr (Ideal.quotientEquiv _ _ e.toRingEquiv ?_).toEquiv
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact (e.commutes f).symm
  have hfL : ((algebraMap O A f : A.toSubring) : L) = (f : L) := rfl
  have hf0 : (f : L) ≠ 0 := fun h ↦ hf (Subtype.ext h)
  rw [h1, card_quot_span_eq_relIndex, card_quot_span_eq_relIndex, hfL, hg]
  exact relIndex_mulLeft_eq _ _ hAP hfin _ hf0 (algebraMap O A f).2

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartResidue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

theorem int_isJacobsonRing : IsJacobsonRing ℤ := by
  refine isJacobsonRing_iff_prime_eq.mpr fun P hP ↦ ?_
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun a ha ↦ ?_) Ideal.le_jacobson
    rw [Ideal.mem_jacobson_bot] at ha
    have h1 := Int.isUnit_iff.mp (ha 1)
    have h2 := Int.isUnit_iff.mp (ha (-1))
    rw [Ideal.mem_bot]
    omega
  · have := hP.isMaximal h
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem natCard_eq_pow_length_of_finiteType (F : Type) [Field F] [Algebra.FiniteType ℤ F]
    (q : ℕ) [CharP F q] :
    q.Prime ∧ Nat.card F = q ^ (Module.length ℤ F).toNat := by
  have := int_isJacobsonRing
  have : Module.Finite ℤ F := finite_of_finite_type_of_isJacobsonRing ℤ F
  have hq : q ≠ 0 := by
    rintro rfl
    have : CharZero F := CharP.charP_to_charZero F
    exact Int.not_isField (isField_of_isIntegral_of_isField
      (fun a b h ↦ by simpa using h) (Field.toIsField F))
  have hqp : q.Prime := (CharP.char_is_prime_or_zero F q).resolve_right hq
  have : Fact q.Prime := ⟨hqp⟩
  let : Algebra (ZMod q) F := ZMod.algebra F q
  have : Module.Finite (ZMod q) F := Module.Finite.of_restrictScalars_finite ℤ (ZMod q) F
  have : Finite F := Module.finite_of_finite (ZMod q)
  have : Fintype F := Fintype.ofFinite F
  refine ⟨hqp, ?_⟩
  rw [Module.length_eq_of_surjective (S := ℤ) (R := ZMod q) (M := F) (ZMod.intCast_surjective),
    Module.length_eq_finrank, ENat.toNat_natCast, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod q), ZMod.card]

theorem OrbitChartResidue.proof (hM : OrbitChartMax.Statement) (hQ : OrbitChartQuot.Statement)
    (hD : OrbitChartDehom.Statement) : OrbitChartResidue.Statement := by
  intro ι _ _ _ n A x s hx hs V hV c hc
  have hPV : orbitIdeal x ≤ V := le_sup_left.trans hV.1.1.2
  have hrel : Geo.IsRelevant V := hV.2
  have hxc : ∀ c' : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) → ∀ k, x k (c' k) ≠ 0 := by
    intro c' h k h0
    apply h k
    apply hPV
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [flatCone, h0]
  set i : (k : ι) → Fin (n k + 1) := fun k ↦ (hrel k).choose
  have hi : ∀ k, (X ⟨k, i k⟩ : MvPolynomial (Coord n) ℤ) ∉ V := fun k ↦ (hrel k).choose_spec
  obtain ⟨eQ⟩ := hQ ι n x c (hxc c hc) V hPV
  obtain ⟨hchar, ⟨eD⟩⟩ := hD ι n A x s hx hs V hV i c hi hc
  set J := V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, i k⟩ : MvPolynomial (Coord n) ℤ) - 1)
  let e : (chartRing x c ⧸ chartPoint x c V) ≃+* (MvPolynomial (Coord n) ℤ ⧸ J) := eQ.trans eD.symm
  have := hM ι n A x s hx hs V hV c hc
  have hfield : IsField (MvPolynomial (Coord n) ℤ ⧸ J) :=
    MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance)
      e.symm.toMulEquiv
  have : J.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient J).mpr hfield
  let : Field (MvPolynomial (Coord n) ℤ ⧸ J) := Ideal.Quotient.field J
  have hft : Algebra.FiniteType ℤ (MvPolynomial (Coord n) ℤ ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ J)
      (Ideal.Quotient.mkₐ_surjective ℤ J)
  have : CharP (MvPolynomial (Coord n) ℤ ⧸ J) (Geo.charOf V) := by
    constructor
    intro a
    have hJC : ∀ b : ℤ, ((b : MvPolynomial (Coord n) ℤ ⧸ J) = 0 ↔ b ∈ V.comap (C : ℤ →+* _)) := by
      intro b
      rw [(map_intCast (Ideal.Quotient.mk J) b).symm.trans (congrArg _ (eq_intCast C b).symm),
        Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hchar]
    rw [← Int.cast_natCast, hJC, Submodule.IsPrincipal.mem_iff_generator_dvd, ← Int.natAbs_dvd,
      Int.natCast_dvd_natCast]
    rfl
  obtain ⟨-, hcard⟩ := @natCard_eq_pow_length_of_finiteType (MvPolynomial (Coord n) ℤ ⧸ J) _
    (by convert hft using 1 <;> rfl) (Geo.charOf V) _
  have hgeo : Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 =
      ((Module.length ℤ (MvPolynomial (Coord n) ℤ ⧸ J)).toNat : ℤ) := by
    simp only [Geo.geoNum, dif_pos hrel]
    rfl
  rw [hgeo, Nat.card_congr e.toEquiv, hcard, Nat.cast_pow, Real.log_pow]
  push_cast
  ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

theorem mem_closure_chartRatio (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) (z : ratioField x) :
    z ∈ Subfield.closure (Set.range (chartRatio x c)) := by
  set T := Subfield.closure (Set.range (chartRatio x c))
  let T' : Subfield (AlgebraicClosure ℚ) := T.map (ratioField x).val.toRingHom
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    T'.toIntermediateField fun q ↦ by
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem T' q
  have hE : ratioField x ≤ E := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨⟨k, i, j⟩, rfl⟩
    refine ⟨chartRatio x c ⟨k, i⟩ / chartRatio x c ⟨k, j⟩,
      div_mem (Subfield.subset_closure (Set.mem_range_self _))
        (Subfield.subset_closure (Set.mem_range_self _)), ?_⟩
    simp [chartRatio, div_div_div_cancel_right₀ (hc k)]
  obtain ⟨t, ht, hzt⟩ := hE z.2
  have : t = z := Subtype.ext hzt
  exact this ▸ ht

theorem OrbitChartRing.proof : OrbitChartRing.Statement := by
  intro ι _ _ n x c hc
  refine ⟨(Subalgebra.fg_iff_finiteType _).mp
    ⟨(Set.finite_range (chartRatio x c)).toFinset, by simp [chartRing]⟩, ?_⟩
  refine (isLocalization_iff _ _).mpr ⟨fun y ↦ ?_, fun z ↦ ?_, fun {a b} h ↦ ⟨1, ?_⟩⟩
  · refine isUnit_iff_ne_zero.mpr fun h ↦ nonZeroDivisors.coe_ne_zero y ?_
    exact Subtype.ext h
  · have hsub : Subring.closure (Set.range (chartRatio x c)) ≤ (chartRing x c).toSubring :=
      Subring.closure_le.mpr fun _ hp ↦ Algebra.subset_adjoin hp
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Subfield.mem_closure_iff.mp (mem_closure_chartRatio x c hc z)
    by_cases hb0 : b = 0
    · refine ⟨(0, 1), ?_⟩
      rw [hb0, div_zero] at hab
      simp [← hab]
    · have hb' : (⟨b, hsub hb⟩ : chartRing x c) ≠ 0 := fun h ↦ hb0 (congrArg Subtype.val h)
      refine ⟨(⟨a, hsub ha⟩, ⟨⟨b, hsub hb⟩, mem_nonZeroDivisors_of_ne_zero hb'⟩), ?_⟩
      change z * b = a
      rw [← hab, div_mul_cancel₀ _ hb0]
  · rw [Subtype.val_injective h]

end

end GroundTheory.Heights₂.Heights
end

