module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.DenseSurj

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.MemSpanLIff
section
namespace PI.CompDegEF

open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem mem_span_l_iff {l : ℕ} [hl : Fact l.Prime] (K : FinExt l) (y : ↥(ball K)) :
    y ∈ Ideal.span {((l : ℕ) : ↥(ball K))} ↔
      ‖((y : ↥K.1) : Om l)‖ ≤ ‖((l : ℕ) : Om l)‖ := by
  have hl0' : ((l : ℕ) : Om l) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l))]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hl.out.ne_zero)
  have hl0 : ((l : ℕ) : ↥K.1) ≠ 0 := by
    intro h
    apply hl0'
    have h' : (((l : ℕ) : ↥K.1) : Om l) = 0 := by rw [h]; rfl
    simpa using h'
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, rfl⟩
    have hz : ‖((z : ↥K.1) : Om l)‖ ≤ 1 := z.2
    have hc : (((z * ((l : ℕ) : ↥(ball K)) : ↥(ball K)) : ↥K.1) : Om l) =
        ((z : ↥K.1) : Om l) * ((l : ℕ) : Om l) := by simp
    rw [hc, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hz
  · intro h
    have hmem : ‖(((y : ↥K.1) / ((l : ℕ) : ↥K.1) : ↥K.1) : Om l)‖ ≤ 1 := by
      have hc : (((y : ↥K.1) / ((l : ℕ) : ↥K.1) : ↥K.1) : Om l) =
          ((y : ↥K.1) : Om l) / ((l : ℕ) : Om l) := by simp
      rw [hc, norm_div, div_le_one (norm_pos_iff.mpr hl0')]
      exact h
    refine ⟨⟨(y : ↥K.1) / ((l : ℕ) : ↥K.1), hmem⟩, ?_⟩
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    push_cast
    exact div_mul_cancel₀ _ hl0

theorem locDegOf_of (hB : BallCard) (hD : DenseSurj) (hK : KerProp) (hN : NormCard) :
    LocDegOf := by
  intro l hl E _ _ φ K hφK hdense v hv hφv
  let ψ : 𝓞 E →+* ↥(ball K) :=
    { toFun := fun x => ⟨⟨φ (x : E), hφK _⟩, (hφv x).1⟩
      map_one' := Subtype.ext <| Subtype.ext <| by simp
      map_mul' := fun a b => Subtype.ext <| Subtype.ext <| by simp
      map_zero' := Subtype.ext <| Subtype.ext <| by simp
      map_add' := fun a b => Subtype.ext <| Subtype.ext <| by simp }
  let q := (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : ↥(ball K))})).comp ψ
  have hsurj : Function.Surjective q := by
    intro w
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨x, hx⟩ := hD l E φ K hφK hdense ((y : ↥K.1) : Om l) (y : ↥K.1).2 y.2
    refine ⟨x, ?_⟩
    show Ideal.Quotient.mk _ (ψ x) = Ideal.Quotient.mk _ y
    rw [Ideal.Quotient.eq, mem_span_l_iff]
    have hc : (((ψ x - y : ↥(ball K)) : ↥K.1) : Om l) = φ (x : E) - ((y : ↥K.1) : Om l) := rfl
    rw [hc, norm_sub_rev]
    exact hx
  have hker : RingHom.ker q = v.asIdeal ^ v.asIdeal.ramificationIdx ℤ := by
    ext x
    rw [RingHom.mem_ker]
    show Ideal.Quotient.mk _ (ψ x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (mem_span_l_iff K (ψ x)).trans (hK l E φ v hv hφv x)
  have hcard : Nat.card (𝓞 E ⧸ v.asIdeal ^ v.asIdeal.ramificationIdx ℤ) =
      Nat.card (↥(ball K) ⧸ Ideal.span {((l : ℕ) : ↥(ball K))}) := by
    rw [← hker]
    exact Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv
  rw [hN l E v hv, hB l K] at hcard
  exact (Nat.pow_right_injective hl.out.two_le hcard).symm

end PI.CompDegEF
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.NormLeOneOfInteger
section
namespace PI.CompDegEF

open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem norm_natCast_lt_one (l : ℕ) [hl : Fact l.Prime] : ‖((l : ℕ) : Om l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt)

theorem norm_natCast_pos (l : ℕ) [hl : Fact l.Prime] : 0 < ‖((l : ℕ) : Om l)‖ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_pos.2 (by exact_mod_cast hl.out.pos)

theorem norm_le_one_of_integer {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) (x : 𝓞 E) : ‖φ (x : E)‖ ≤ 1 := by
  have hv := Valuation.integer.integers (Valued.v : Valuation (Om l) NNReal)
  have h1 : IsIntegral ℤ (φ (x : E)) := (RingOfIntegers.isIntegral_coe x).map φ.toIntAlgHom
  have h2 : IsIntegral (Valued.v : Valuation (Om l) NNReal).integer (φ (x : E)) := h1.tower_top
  have h3 := (hv.isIntegral_iff_v_le_one).1 h2
  rw [PadicAlgCl.valuation_def] at h3
  exact_mod_cast h3

def plIdeal {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] (φ : E →+* Om l) :
    Ideal (𝓞 E) where
  carrier := {x | ‖φ (x : E)‖ < 1}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    change ‖φ (algebraMap (𝓞 E) E (a + b))‖ < 1
    change ‖φ (algebraMap (𝓞 E) E a)‖ < 1 at ha
    change ‖φ (algebraMap (𝓞 E) E b)‖ < 1 at hb
    rw [map_add (f := _), map_add (f := _)]
    exact lt_of_le_of_lt (PadicAlgCl.isNonarchimedean l _ _) (max_lt ha hb)
  smul_mem' c {a} ha := by
    change ‖φ (algebraMap (𝓞 E) E (c * a))‖ < 1
    change ‖φ (algebraMap (𝓞 E) E a)‖ < 1 at ha
    rw [map_mul, map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_integer φ c)) ha

theorem mem_plIdeal {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] (φ : E →+* Om l)
    (x : 𝓞 E) : x ∈ plIdeal φ ↔ ‖φ (x : E)‖ < 1 := Iff.rfl

theorem natCast_mem_plIdeal {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) : ((l : ℕ) : 𝓞 E) ∈ plIdeal φ := by
  rw [mem_plIdeal]
  simpa using norm_natCast_lt_one l

theorem plIdeal_isPrime {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) : (plIdeal φ).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro h
    have : (1 : 𝓞 E) ∈ plIdeal φ := h ▸ Submodule.mem_top
    rw [mem_plIdeal] at this
    simp at this
  · intro a b hab
    simp only [mem_plIdeal, RingOfIntegers.coe_eq_algebraMap, map_mul, norm_mul] at hab ⊢
    by_contra! h
    exact (not_le_of_gt hab) (by
      simpa only [one_mul] using mul_le_mul h.1 h.2 zero_le_one (norm_nonneg _))

theorem plIdeal_ne_bot {l : ℕ} [hl : Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (φ : E →+* Om l) : plIdeal φ ≠ ⊥ := by
  intro h
  have h1 := natCast_mem_plIdeal (E := E) φ
  rw [h, Ideal.mem_bot] at h1
  have : ((l : ℕ) : E) = 0 := by exact_mod_cast congrArg (fun y : 𝓞 E => (y : E)) h1
  exact hl.out.ne_zero (by exact_mod_cast this)

def plOf {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] (φ : E →+* Om l) :
    HeightOneSpectrum (𝓞 E) :=
  ⟨plIdeal φ, plIdeal_isPrime φ, plIdeal_ne_bot φ⟩

theorem placeProp : PlaceProp := by
  intro l _ E _ _ φ
  refine ⟨plOf φ, natCast_mem_plIdeal φ, fun x => ⟨norm_le_one_of_integer φ x, Iff.rfl⟩⟩

end PI.CompDegEF
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.SpanLIsMaximal
section
namespace PI.CompDegEF

open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem span_l_isMaximal (l : ℕ) [hl : Fact l.Prime] : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal := by
  refine Ideal.IsPrime.isMaximal ?_ ?_
  · exact (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hl.out)
  · simp [hl.out.ne_zero]

theorem liesOver_of_mem {l : ℕ} [hl : Fact l.Prime] {E : Type} [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E l) :
    v.asIdeal.LiesOver (Ideal.span {((l : ℕ) : ℤ)}) := by
  constructor
  refine (span_l_isMaximal l).eq_of_le ?_ ?_
  · intro h
    rw [Ideal.comap_eq_top_iff] at h
    exact v.isPrime.ne_top h
  · rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change algebraMap ℤ (𝓞 E) ((l : ℕ) : ℤ) ∈ v.asIdeal
    simpa using (show ((l : ℕ) : 𝓞 E) ∈ v.asIdeal from hv)

theorem normCard : NormCard := by
  intro l _ E _ _ v hv
  have := liesOver_of_mem hv
  have hmax := span_l_isMaximal l
  have hvmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have h1 : Nat.card (𝓞 E ⧸ v.asIdeal ^ v.asIdeal.ramificationIdx ℤ) =
      Ideal.absNorm (v.asIdeal ^ v.asIdeal.ramificationIdx ℤ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [h1, map_pow, Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver v.asIdeal
    (Ideal.span {((l : ℕ) : ℤ)}) hmax.isPrime (by simp [(Fact.out : l.Prime).ne_zero]),
    Ideal.absNorm_span_natCast, Module.finrank_self, pow_one,
    Ideal.inertiaDeg'_eq_inertiaDeg, Formalism.MainNotions.N.locDeg, ← pow_mul, mul_comm]

end PI.CompDegEF
end

