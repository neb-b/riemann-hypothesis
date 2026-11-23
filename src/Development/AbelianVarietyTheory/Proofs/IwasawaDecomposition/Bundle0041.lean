module

public import Mathlib
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfSupportedAtSplit
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct

namespace GlobalTheory.SplitLocEq


open NumberField IsDedekindDomain TensorProduct in
theorem _root_.GlobalTheory.SplitLocEq.conj_entry {L : Type} [Field L] [NumberField L] [IsCMField L]
    {n : ℕ} (x : _root_.ReciprocityTheory.Aut.GA L n) (i j : Fin n) :
    _root_.ReciprocityTheory.Aut.conjAL L ((x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) i j) =
      (((x⁻¹ : _root_.ReciprocityTheory.Aut.GA L n).1 : GL (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) j i := by
  have h : (x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) *
      _root_.ReciprocityTheory.Aut.conjT (_root_.ReciprocityTheory.Aut.conjAL L) (x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) = 1 := x.2
  have hinv : _root_.ReciprocityTheory.Aut.conjT (_root_.ReciprocityTheory.Aut.conjAL L) (x.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) =
      (((x⁻¹ : _root_.ReciprocityTheory.Aut.GA L n).1 : GL (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) := by
    have h' := congrArg
      (fun M => (((x.1)⁻¹ : GL (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) * M) h
    simpa [← mul_assoc] using h'
  rw [← hinv]
  rfl

theorem proj_entry {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) (x : GA L n)
    (i j : Fin n) : SplitPlace.proj s ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      ((SplitPlace.loc s n x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j := rfl

open NumberField IsDedekindDomain TensorProduct in
private theorem evalAt_apply' {L : Type} [Field L] [NumberField L] (w)
    (a : _root_.ReciprocityTheory.Aut.AFplus L) : _root_.ReciprocityTheory.Aut.evalAt L w a = a w := rfl

open NumberField IsDedekindDomain TensorProduct in
private theorem eq_zero_of_compAt_eq_zero_of_proj_conj_eq_zero {L : Type} [Field L] [NumberField L] [IsCMField L]
    (s : _root_.ReciprocityTheory.Aut.SplitPlace L) (d : _root_.ReciprocityTheory.Aut.AL L)
    (hw : ∀ w, w ≠ s.v → _root_.ReciprocityTheory.Aut.compAt L w d = 0) (h₁ : SplitPlace.proj s d = 0)
    (h₂ : SplitPlace.proj s (_root_.ReciprocityTheory.Aut.conjAL L d) = 0) : d = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L :=
    Module.finBasisOfFinrankEq _ _ (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
  obtain ⟨a, c, rfl⟩ := _root_.GlobalTheory.tensor_exists_decomp b d
  have hw' : ∀ w, w ≠ s.v → a w = 0 ∧ c w = 0 := fun w hne =>
    _root_.GlobalTheory.tensor_decomp_eq_zero b _ _
      (by simpa [_root_.ReciprocityTheory.Aut.compAt, evalAt_apply'] using hw w hne)
  simp only [map_add (f := _), _root_.ReciprocityTheory.Aut.SplitPlace.proj, _root_.ReciprocityTheory.Aut.conjAL] at h₁ h₂
  simp [evalAt_apply'] at h₁ h₂
  set σ := IsCMField.complexConj L
  have hΔ : s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) ≠ 0 := by
    intro h0
    have h0' : b 0 * σ (b 1) - b 1 * σ (b 0) = 0 :=
      (injective_iff_map_eq_zero s.i.toRingHom).mp (RingHom.injective s.i.toRingHom) _ h0
    have hb1 : b 1 ≠ 0 := b.ne_zero 1
    have hσb1 : σ (b 1) ≠ 0 := by simpa using hb1
    have hfix : σ (b 0 / b 1) = b 0 / b 1 := by
      rw [map_div₀, div_eq_div_iff hσb1 hb1]
      linear_combination -h0'
    obtain ⟨k, hk⟩ : ∃ k : maximalRealSubfield L, (k : L) = b 0 / b 1 :=
      ⟨⟨_, (IsCMField.complexConj_eq_self_iff L _).mp hfix⟩, rfl⟩
    have hsum : ∑ i, (![1, -k] : Fin 2 → maximalRealSubfield L) i • b i = 0 := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
      have hsm : k • b 1 = (k : L) * b 1 := rfl
      rw [hsm, hk, div_mul_cancel₀ _ hb1]
      ring
    have := Fintype.linearIndependent_iff.mp b.linearIndependent _ hsum 0
    simp at this
  have hA : a s.v = 0 := by
    have : s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) * a s.v = 0 := by
      simp only [map_sub, map_mul]
      linear_combination s.i (σ (b 1)) * h₁ - s.i (b 1) * h₂
    exact (mul_eq_zero.mp this).resolve_left hΔ
  have hC : c s.v = 0 := by
    have : s.i (b 0 * σ (b 1) - b 1 * σ (b 0)) * c s.v = 0 := by
      simp only [map_sub, map_mul]
      linear_combination s.i (b 0) * h₂ - s.i (σ (b 0)) * h₁
    exact (mul_eq_zero.mp this).resolve_left hΔ
  have ha : a = 0 := by
    ext w : 1
    by_cases hv : w = s.v
    · subst hv; exact hA
    · exact (hw' w hv).1
  have hc : c = 0 := by
    ext w : 1
    by_cases hv : w = s.v
    · subst hv; exact hC
    · exact (hw' w hv).2
  simp [ha, hc]


open NumberField IsDedekindDomain TensorProduct in
theorem _root_.GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq : ∀ (L : Type) [Field L] [NumberField L]
    [IsCMField L] (n : ℕ) (s : _root_.ReciprocityTheory.Aut.SplitPlace L) (x y : _root_.Formalism.AUTREP.GAf L n),
    _root_.ReciprocityTheory.Aut.TrivOutside (L := L) {s.v} x →
    _root_.ReciprocityTheory.Aut.TrivOutside (L := L) {s.v} y →
      SplitPlace.loc s n x = SplitPlace.loc s n y → x = y := by
  intro L _ _ _ n s x y hx hy hxy
  have triv : ∀ z : _root_.ReciprocityTheory.Aut.GA L n, _root_.ReciprocityTheory.Aut.TrivOutside (L := L) {s.v} z → ∀ w, w ≠ s.v → ∀ i j,
      _root_.ReciprocityTheory.Aut.compAt L w ((z.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) i j) =
        (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro z hz w hw i j
    have := hz w (by simpa using hw)
    exact congrFun (congrFun this i) j
  have trivInv : ∀ z : _root_.ReciprocityTheory.Aut.GA L n, _root_.ReciprocityTheory.Aut.TrivOutside (L := L) {s.v} z → _root_.ReciprocityTheory.Aut.TrivOutside (L := L) {s.v} z⁻¹ := by
    intro z hz w hw
    show ((z⁻¹).1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)).map (_root_.ReciprocityTheory.Aut.compAt L w) = 1
    have hm : (z.1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) *
        ((z⁻¹).1 : Matrix (Fin n) (Fin n) (_root_.ReciprocityTheory.Aut.AL L)) = 1 := by simp
    have h2 := congrArg (Matrix.map · (_root_.ReciprocityTheory.Aut.compAt L w)) hm
    simp only [Matrix.map_mul] at h2
    rw [hz w hw, one_mul] at h2
    rw [h2]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hinv : SplitPlace.loc s n x⁻¹ = SplitPlace.loc s n y⁻¹ := by simp [map_inv, hxy]
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [← sub_eq_zero]
  apply eq_zero_of_compAt_eq_zero_of_proj_conj_eq_zero s
  · intro w hw
    rw [map_sub, triv x hx w hw, triv y hy w hw, sub_self]
  · rw [map_sub, _root_.GlobalTheory.SplitLocEq.proj_entry, _root_.GlobalTheory.SplitLocEq.proj_entry, hxy, sub_self]
  · rw [map_sub, _root_.GlobalTheory.SplitLocEq.conj_entry, _root_.GlobalTheory.SplitLocEq.conj_entry,
      map_sub, _root_.GlobalTheory.SplitLocEq.proj_entry, _root_.GlobalTheory.SplitLocEq.proj_entry, hinv, sub_self]

end GlobalTheory.SplitLocEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApproxFinitePlacesNumberFieldTarget
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

noncomputable section

namespace GlobalTheory.FinPlaceApprox

theorem exists_approx_finite_places (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F) → F) (M : ℕ) :
    ∃ a : F, ∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ)) := by
  classical
  obtain ⟨⟨d, hd⟩, hdS⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F)) (T.image t)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hn : ∀ v ∈ T, ∃ n : 𝓞 F, algebraMap (𝓞 F) F n = algebraMap (𝓞 F) F d * t v := by
    intro v hv
    obtain ⟨n, hn⟩ := hdS (t v) (Finset.mem_image_of_mem t hv)
    exact ⟨n, by rw [hn, Algebra.smul_def]⟩
  choose! n hn using hn
  have h0 : ∀ v : HeightOneSpectrum (𝓞 F), v.intValuation d ≠ 0 := fun v => v.intValuation_ne_zero d hd0
  obtain ⟨x, hx⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun v => v.asIdeal)
    (fun v => M + ((v.intValuation d).log).natAbs) (fun v _ => v.prime)
    (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => n v.1)
  have dE : algebraMap (𝓞 F) F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
  refine ⟨algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F d, fun v hv => ?_⟩
  have hxv : x - n v ∈ v.asIdeal ^ (M + ((v.intValuation d).log).natAbs) := hx v hv
  have key : algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F d - t v =
      algebraMap (𝓞 F) F (x - n v) / algebraMap (𝓞 F) F d := by
    rw [map_sub, hn v hv]; field_simp
  rw [key, map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    div_le_iff₀ (zero_lt_iff.2 (h0 v))]
  refine ((v.intValuation_le_pow_iff_mem _ _).2 hxv).trans ?_
  have hle : (v.intValuation d).log ≤ 0 := by
    have := v.intValuation_le_one d
    rw [← WithZero.exp_log (h0 v), ← WithZero.exp_zero, WithZero.exp_le_exp] at this
    exact this
  conv_rhs => rw [← WithZero.exp_log (h0 v)]
  rw [← WithZero.exp_add, WithZero.exp_le_exp]
  omega

theorem approx_target : ∀ (F : Type) [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F)))
    (t : HeightOneSpectrum (𝓞 F) → F) (M : ℕ),
    ∃ a : F, ∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ)) :=
  fun F _ _ T t M => exists_approx_finite_places F T t M

end GlobalTheory.FinPlaceApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongOfCongOnFixed
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne Pointwise

namespace GlobalTheory.InertiaMovesRoot

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem val_eq_one_of_notMem (h : IsPlaceOver A w) {s : 𝓞 E} (hs : s ∉ w.asIdeal) :
    A.valuation (algebraMap E Ω (s : E)) = 1 :=
  le_antisymm (valuation_le_one_intCl (F := E) A (algebraMap (𝓞 E) _ s))
    (not_lt.mp fun hlt => hs ((h s).mp hlt))

theorem exists_val_eq_zpow (h : IsPlaceOver A w) {ϖ : 𝓞 E} (h1 : ϖ ∈ w.asIdeal)
    (h2 : ϖ ∉ w.asIdeal ^ 2) {a : E} (ha : a ≠ 0) :
    ∃ m : ℤ, A.valuation (algebraMap E Ω a) = A.valuation (algebraMap E Ω (ϖ : E)) ^ m := by
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hϖ0' : (ϖ : E) ≠ 0 := by simpa using hϖ0
  have hv : w.intValuation ϖ = WithZero.exp (-1 : ℤ) := by
    have a1 := (w.intValuation_le_pow_iff_mem ϖ 1).2 (by rw [pow_one]; exact h1)
    have a2 : ¬ _ := fun hh => h2 ((w.intValuation_le_pow_iff_mem ϖ 2).1 hh)
    rw [← WithZero.exp_log (w.intValuation_ne_zero ϖ hϖ0), WithZero.exp_le_exp] at a1 a2
    rw [← WithZero.exp_log (w.intValuation_ne_zero ϖ hϖ0)]
    congr 1
    omega
  have hv' : w.valuation E (ϖ : E) = WithZero.exp (-1 : ℤ) := by
    rw [← hv]; exact w.valuation_of_algebraMap ϖ
  have ha' : w.valuation E a ≠ 0 := by simpa using ha
  set n := WithZero.log (w.valuation E a)
  have hu : w.valuation E (a * (ϖ : E) ^ n) = 1 := by
    rw [map_mul, map_zpow₀, hv', ← WithZero.exp_log ha', ← WithZero.exp_zsmul, ← WithZero.exp_add,
      ← WithZero.exp_zero]
    congr 1
    simp [n]
  obtain ⟨t, d, htd⟩ := w.exists_primeCompl_mul_eq_of_integer _ hu.le
  have hd : w.valuation E (algebraMap (𝓞 E) E d) = 1 := (w.valuation_eq_one_iff_notMem).2 d.2
  have ht : w.valuation E (algebraMap (𝓞 E) E t) = 1 := by rw [← htd, map_mul, hu, hd, one_mul]
  have ht' := val_eq_one_of_notMem h ((w.valuation_eq_one_iff_notMem).1 ht)
  have hd' := val_eq_one_of_notMem h d.2
  have e := congrArg (fun z => A.valuation (algebraMap E Ω z)) htd
  simp only [map_mul, map_zpow₀] at e
  change _ * A.valuation (algebraMap E Ω ((d : 𝓞 E) : E)) = A.valuation (algebraMap E Ω (t : E)) at e
  rw [ht', hd', mul_one] at e
  exact ⟨-n, by rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left e⟩

theorem val_term_le_one {ι : Type*} (s : Finset ι) (f : ι → Ω)
    (hf : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → A.valuation (f i) = A.valuation (f j) → i = j)
    (hs : A.valuation (∑ i ∈ s, f i) ≤ 1) : ∀ i ∈ s, A.valuation (f i) ≤ 1 := by
  classical
  intro i hi
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => A.valuation (f i)) ⟨i, hi⟩
  by_cases h0 : f j = 0
  · refine (hmax i hi).trans ?_
    simp [h0]
  refine (hmax i hi).trans ?_
  rw [← Finset.add_sum_erase s f hj] at hs
  rwa [Valuation.map_add_eq_of_lt_left] at hs
  refine Valuation.map_sum_lt _ (by simpa using h0) fun k hk => ?_
  rw [Finset.mem_erase] at hk
  exact lt_of_le_of_ne (hmax k hk.2) fun he => hk.1 (hf j hj k hk.2 h0 he.symm).symm

theorem cong_on_adjoin (h : IsPlaceOver A w) {l : ℕ} (hl : 2 ≤ l) {ϖ : 𝓞 E} (h1 : ϖ ∈ w.asIdeal)
    (h2 : ϖ ∉ w.asIdeal ^ 2) {x : Ω} (hx : x ^ l = algebraMap E Ω (ϖ : E)) :
    x ∉ (⊥ : IntermediateField E Ω) ∧ ∀ (g : Ω ≃ₐ[E] Ω) (b : Ω),
      b ∈ IntermediateField.adjoin E {x} → A.valuation b ≤ 1 → A.valuation (g b - b) < 1 := by
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hl0 : l ≠ 0 := by omega
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hl0, eq_comm, map_eq_zero] at hx
    exact hϖ0 (by simpa using hx)
  set t := A.valuation x with ht
  have htl : A.valuation (algebraMap E Ω (ϖ : E)) = t ^ l := by rw [← hx, map_pow]
  have ht0 : 0 < t := zero_lt_iff.mpr (by simpa [ht] using hx0)
  have ht1 : t < 1 := by
    have := (h ϖ).mpr h1
    rw [htl] at this
    exact (pow_lt_one_iff hl0).mp this
  have hinj : Function.Injective fun n : ℤ => t ^ n := zpow_right_injective₀ ht0 ht1.ne
  have hval : ∀ (a : E) (i : ℕ), algebraMap E Ω a * x ^ i ≠ 0 →
      ∃ m : ℤ, A.valuation (algebraMap E Ω a * x ^ i) = t ^ ((i : ℤ) + l * m) := by
    intro a i ha
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    obtain ⟨m, hm⟩ := exists_val_eq_zpow h h1 h2 ha0
    refine ⟨m, ?_⟩
    rw [map_mul, hm, htl, map_pow, zpow_add₀ ht0.ne', zpow_mul, zpow_natCast, zpow_natCast, mul_comm]
  have hmod : ∀ (i j : ℕ) (m n : ℤ), i < l → j < l → t ^ ((i : ℤ) + l * m) = t ^ ((j : ℤ) + l * n) →
      i = j := by
    intro i j m n hi hj he
    have := congrArg (· % (l : ℤ)) (hinj he)
    simp only [Int.add_mul_emod_self_left] at this
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at this
    omega
  constructor
  · intro hb
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hb
    obtain ⟨m, hm⟩ := hval a 0 (by simpa [ha] using hx0)
    have := hmod 0 1 m 0 (by omega) (by omega) (by rw [← hm]; simp [ha, ht])
    omega
  intro g b hb hb1
  have halg : IsAlgebraic E x := Algebra.IsAlgebraic.isAlgebraic x
  have hb' : b ∈ Algebra.adjoin E {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]; exact hb
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb'
  obtain ⟨p₀, rfl⟩ := hb'
  have hq : (X ^ l - C (ϖ : E)).Monic := monic_X_pow_sub_C _ hl0
  set p := p₀ %ₘ (X ^ l - C (ϖ : E))
  have hp : aeval x p = aeval x p₀ := aeval_modByMonic_eq_self_of_root (by simp [hx])
  have hdeg : p.natDegree < l := by
    have := natDegree_modByMonic_lt p₀ hq (by
      intro h1
      have := congrArg natDegree h1
      rw [natDegree_X_pow_sub_C _, natDegree_one] at this
      exact hl0 this)
    rwa [natDegree_X_pow_sub_C _] at this
  change A.valuation (aeval x p₀) ≤ 1 at hb1
  change A.valuation (g (aeval x p₀) - aeval x p₀) < 1
  rw [← hp, aeval_eq_sum_range' hdeg] at hb1 ⊢
  simp only [Algebra.smul_def] at hb1 ⊢
  have hle := val_term_le_one _ _ (fun i hi j hj h0 he => by
    obtain ⟨m, hm⟩ := hval _ i h0
    obtain ⟨n, hn⟩ := hval (p.coeff j) j (by
      intro h00
      rw [h00, map_zero] at he
      exact h0 (by simpa using he))
    exact hmod i j m n (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (by rw [← hm, ← hn, he])) hb1
  have hgx : A.valuation (g x) = t := by
    refine (pow_left_injective hl0 : Function.Injective (fun a : A.ValueGroup => a ^ l)) ?_
    show _ ^ l = t ^ l
    rw [← map_pow, ← map_pow, hx, g.commutes, htl]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  have hlt : A.valuation (algebraMap E Ω (p.coeff i) * x ^ i) < 1 := by
    refine lt_of_le_of_ne (hle i hi) fun he => ?_
    obtain ⟨m, hm⟩ := hval (p.coeff i) i (by intro h0; simp [h0] at he)
    have := hmod i 0 m 0 (Finset.mem_range.mp hi) (by omega) (by rw [← hm, he]; simp)
    omega
  refine Valuation.map_sub_lt _ ?_ hlt
  rw [map_mul g, g.commutes, map_pow g, map_mul, map_pow, hgx]
  rwa [map_mul, map_pow] at hlt

theorem mem_Ine_of_cong {σ : Ω ≃ₐ[E] Ω}
    (hσ : ∀ b : IntCl E Ω, σ • b - b ∈ primeBelow (F := E) A) : σ ∈ Ine (F := E) A := by
  have hc : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1 :=
    fun b hb => hσ ⟨b, hb.tower_top⟩
  have hdec : σ • A = A := by
    refine eq_of_valuation_lt_one_iff E fun b hb => ?_
    let b' : IntCl E Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := E) (σ • A) ↔ b' ∈ primeBelow (F := E) A
    rw [primeBelow_smul, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have := hσ (σ⁻¹ • b')
    rw [smul_inv_smul] at this
    exact ⟨fun hh => by simpa using add_mem this hh, fun hh => by simpa using sub_mem hh this⟩
  refine ⟨hdec, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den E A hx
  have hσx : A.valuation (σ x) ≤ 1 := by
    rw [A.valuation_le_one_iff, apply_mem_iff_of_mem_Dec hdec, ← A.valuation_le_one_iff]; exact hx
  have key : s * (σ x - x) = (σ t - t) - (σ s - s) * σ x := by
    rw [← e, map_mul]; ring
  have hv : A.valuation (s * (σ x - x)) < 1 := by
    rw [key]
    refine Valuation.map_sub_lt _ (hc t ht) ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hσx) (hc s hs)
  rwa [map_mul, hs1, one_mul] at hv

theorem exists_cong_of_cong_on_fixed {R S G : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace S] [DiscreteTopology S] [ContinuousSMul G S]
    (H : Subgroup G) [CompactSpace H] [TotallyDisconnectedSpace H] (Q : Ideal S) [Q.IsPrime]
    (g : G) (hg : ∀ b : S, (∀ k ∈ H, k • b = b) → g • b - b ∈ Q) :
    ∃ k ∈ H, ∃ k' ∈ H, ∀ b : S, (k' * g * k) • b - b ∈ Q := by
  let R' := FixedPoints.subalgebra R S H
  have hR' : ∀ b : R', ∀ k ∈ H, k • (b : S) = b := fun b k hk => b.2 ⟨k, hk⟩
  have : SMulCommClass H R' S := ⟨fun k r b => by
    change (k : G) • ((r : S) * b) = (r : S) * (k : G) • b
    rw [smul_mul', hR' r k k.2]⟩
  have : Algebra.IsInvariant R' S H := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  have : (g⁻¹ • Q).IsPrime := Ideal.IsPrime.smul _
  obtain ⟨k, hk⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := R') (G := H)
    Q (g⁻¹ • Q) (by
      ext b
      rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap,
        Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
      have := hg b (hR' b)
      change (b : S) ∈ Q ↔ g • (b : S) ∈ Q
      exact ⟨fun hh => by simpa using add_mem this hh, fun hh => by simpa using sub_mem hh this⟩)
  have hQ : (g * k) • Q = Q := by
    have hk2 : g⁻¹ • Q = (k : G) • Q := hk
    rw [mul_smul, ← hk2, smul_inv_smul]
  let φ : (S ⧸ Q) ≃ₐ[R' ⧸ Q.under R'] (S ⧸ Q) := AlgEquiv.ofRingEquiv
    (f := Ideal.quotientEquiv Q Q (MulSemiringAction.toRingEquiv G S (g * k)) hQ.symm)
    (fun r => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      change Ideal.Quotient.mk Q ((g * k) • (r : S)) = Ideal.Quotient.mk Q (r : S)
      rw [Ideal.Quotient.eq, mul_smul, hR' r k k.2]
      exact hg r (hR' r))
  obtain ⟨⟨k', hk'Q⟩, hk'⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H)
    (Q.under R') Q φ
  refine ⟨k, k.2, k'⁻¹, inv_mem k'.2, fun b => ?_⟩
  have h1 : Ideal.Quotient.mk Q ((k' : G) • b) = Ideal.Quotient.mk Q ((g * k) • b) :=
    DFunLike.congr_fun hk' (Ideal.Quotient.mk Q b)
  rw [eq_comm, Ideal.Quotient.eq] at h1
  have h2 : (k' : G) • Q = Q := hk'Q
  rw [← h2, Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, inv_smul_smul, smul_smul] at h1
  rwa [mul_assoc]

theorem exists_mem_Ine_apply_ne : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (l : ℕ), l.Prime → ∀ (ϖ : 𝓞 E), ϖ ∈ w.asIdeal → ϖ ∉ w.asIdeal ^ 2 → ∀ x : Ω,
    x ^ l = algebraMap E Ω (ϖ : E) → ∃ σ ∈ Ine (F := E) A, σ x ≠ x := by
  intro E Ω _ _ _ _ _ A w h l hl ϖ h1 h2 x hx
  obtain ⟨hx1, hx2⟩ := cong_on_adjoin h hl.two_le h1 h2 hx
  obtain ⟨g, hg⟩ : ∃ g : Ω ≃ₐ[E] Ω, g x ≠ x := by
    by_contra hc
    push Not at hc
    exact hx1 ((InfiniteGalois.mem_bot_iff_fixed x).mpr hc)
  letI : TopologicalSpace (IntCl E Ω) := ⊥
  haveI : DiscreteTopology (IntCl E Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl E Ω
  let H := MulAction.stabilizer (Ω ≃ₐ[E] Ω) x
  have hH : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) :=
    H.isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral (K := E) x)
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  obtain ⟨k, hk, k', hk', hc⟩ := exists_cong_of_cong_on_fixed (R := 𝓞 E) H (primeBelow (F := E) A) g
    (fun b hb => by
      refine hx2 g b ?_ (valuation_le_one_intCl A b)
      rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin E {x}),
        IntermediateField.mem_fixedField_iff]
      intro f hf
      exact congrArg Subtype.val (hb f (hf ⟨x, IntermediateField.mem_adjoin_simple_self E x⟩)))
  refine ⟨k' * g * k, mem_Ine_of_cong hc, fun he => hg ?_⟩
  have e1 : k x = x := hk
  have e2 : k' x = x := hk'
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, e1] at he
  exact k'.injective (he.trans e2.symm)

end GlobalTheory.InertiaMovesRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqPowOfWeilDegreeEqSmooth
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne


open NumberField IsDedekindDomain Polynomial Module in
theorem _root_.GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (_root_.GlobalTheory.WeilDeligne.Weil h) V),
    _root_.GlobalTheory.WeilDeligne.IsSmooth ρ → ∀ σ τ : _root_.GlobalTheory.WeilDeligne.Weil h, _root_.GlobalTheory.WeilDeligne.deg σ = _root_.GlobalTheory.WeilDeligne.deg τ →
      ∃ m : ℕ, 0 < m ∧ ρ σ ^ m = ρ τ ^ m := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ ρ hρ σ τ hdeg
  let x : ℕ → _root_.GlobalTheory.WeilDeligne.Weil h := fun k ↦ (τ ^ k)⁻¹ * σ ^ k
  have hmem : ∀ k, ρ (x k) ∈ Set.range fun ι ↦ ρ (_root_.GlobalTheory.WeilDeligne.ineIncl h ι) := by
    intro k
    have h0 : _root_.GlobalTheory.WeilDeligne.deg (x k) = 0 := by
      simp only [x, _root_.GlobalTheory.WeilDeligne.deg_mul, _root_.GlobalTheory.WeilDeligne.deg_inv, _root_.GlobalTheory.WeilDeligne.deg_pow, hdeg]
      ring
    refine ⟨⟨_, _root_.GlobalTheory.WeilDeligne.deg_eq_zero_iff.mp h0⟩, ?_⟩
    simp only
    congr 1
  obtain ⟨k, l, hkl, hρkl⟩ :=
    Set.Finite.exists_lt_map_eq_of_forall_mem hmem hρ.finite_range
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hkl
  have hx : ρ (x k) = ρ (x (k + m + 1)) := hρkl
  refine ⟨m + 1, Nat.succ_pos m, ?_⟩
  have key : σ ^ (m + 1) = τ ^ (k + m + 1) * x (k + m + 1) * (x k)⁻¹ * (τ ^ k)⁻¹ := by
    simp only [x]
    group
  have key' : τ ^ (m + 1) = τ ^ (k + m + 1) * (τ ^ k)⁻¹ := by
    group
  have hinv : ρ (x k) * ρ (x k)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [← map_pow, ← map_pow, key, key']
  simp only [map_mul]
  rw [← hx, mul_assoc (ρ _) (ρ (x k)), hinv, mul_one]

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusInvMulMemInertiaStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_inv_mul_mem_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ τ τ' : G E Ω, IsFrob (F := E) A (normV v) τ →
    IsFrob (F := E) A (normV v) τ' → τ'⁻¹ * τ ∈ Ine (F := E) A := by
  first | exact @GlobalTheory.frob_inv_mul_mem_inertia | exact GlobalTheory.frob_inv_mul_mem_inertia | (intros; apply GlobalTheory.frob_inv_mul_mem_inertia <;> assumption)
end

