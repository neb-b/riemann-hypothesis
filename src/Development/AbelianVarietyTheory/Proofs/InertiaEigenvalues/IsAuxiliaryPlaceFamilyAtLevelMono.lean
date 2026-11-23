module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelOrderExponentsSmallValuationDetermina
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PropEOfAdmissible

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

section Places

variable {R : Ranks} {H : Host R}

theorem conj_conj (H : Host R) (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  have h1 := H.conjE_apply H.φ₀ (H.conj x)
  have h2 := H.conjE_apply H.φ₀ x
  refine h1.trans ?_
  show starRingEnd ℂ (H.φ₀ (H.conj x)) = _
  rw [h2, Complex.conj_conj]

theorem conj_int (H : Host R) (x : 𝓞 H.E) : ∃ y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) :=
  ⟨⟨H.conj (x : H.E), (x.isIntegral_coe).map (H.conj.toAlgHom.restrictScalars ℤ)⟩, rfl⟩

theorem isConjPl_symm {w w' : PlE H} (h : IsConjPl H w w') : IsConjPl H w' w :=
  fun x y hy => (h y x (by rw [hy, conj_conj])).symm

theorem isConjPl_unique {w w' w'' : PlE H} (h : IsConjPl H w w') (h' : IsConjPl H w w'') : w' = w'' := by
  apply HeightOneSpectrum.ext
  ext y
  obtain ⟨x, hx⟩ := conj_int H y
  have : (y : H.E) = H.conj (x : H.E) := by rw [hx, conj_conj]
  exact (h x y this).symm.trans (h' x y this)

end Places

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem over_of_over {P P' v : PlE D.host} (h : Over P v) (h' : Over P' v) : Over P P' := by
  rcases h with rfl | h <;> rcases h' with rfl | h'
  · exact Or.inl rfl
  · exact Or.inr (isConjPl_symm h')
  · exact Or.inr h
  · exact Or.inl (isConjPl_unique (isConjPl_symm h') (isConjPl_symm h))

theorem exists_isQ {ι : Type} [Fintype ι] (P : ι → PlE D.host) :
    ∃ Q : Finset (PlE D.host), IsQ P Q ∧ Q.card ≤ 2 * Fintype.card ι := by
  classical
  have : ∀ q, ∃ v, ∀ w, IsConjPl D.host (P q) w ↔ (w = v ∧ IsConjPl D.host (P q) v) := by
    intro q
    by_cases h : ∃ v, IsConjPl D.host (P q) v
    · obtain ⟨v, hv⟩ := h
      exact ⟨v, fun w => ⟨fun hw => ⟨isConjPl_unique hw hv, hv⟩, fun hw => hw.1 ▸ hw.2⟩⟩
    · exact ⟨P q, fun w => ⟨fun hw => absurd ⟨w, hw⟩ h, fun hw => hw.1 ▸ hw.2⟩⟩
  choose c hc using this
  refine ⟨Finset.univ.image P ∪ (Finset.univ.filter fun q => IsConjPl D.host (P q) (c q)).image c, fun v => ?_, ?_⟩
  · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, Over]
    constructor
    · rintro (⟨q, rfl⟩ | ⟨q, h, rfl⟩)
      · exact ⟨q, Or.inl rfl⟩
      · exact ⟨q, Or.inr h⟩
    · rintro ⟨q, rfl | h⟩
      · exact Or.inl ⟨q, rfl⟩
      · exact Or.inr ⟨q, ((hc q v).1 h).2, ((hc q v).1 h).1.symm⟩
  · refine (Finset.card_union_le _ _).trans ?_
    have h1 : (Finset.univ.image P).card ≤ Fintype.card ι := Finset.card_image_le
    have h2 : ((Finset.univ.filter fun q => IsConjPl D.host (P q) (c q)).image c).card ≤ Fintype.card ι :=
      Finset.card_image_le.trans (Finset.card_le_univ _)
    omega

theorem conjCl_of_isQ {ι : Type} {P : ι → PlE D.host} {Q : Finset (PlE D.host)} (hQ : IsQ P Q) :
    ConjCl (D := D) Q := by
  intro v hv v' h
  obtain ⟨q, hq⟩ := (hQ v).1 hv
  refine (hQ v').2 ⟨q, ?_⟩
  exact over_of_over hq (Or.inr (isConjPl_symm h))

theorem l_ne_zero_Ok (i : X.Tw) (k : ℕ) : ((X.l i : ℕ) : X.Ok i k) ≠ 0 ∧ ((X.l i : ℕ) : X.O i) ≠ 0 ∧
    ((X.l i : ℕ) : X.O0 i) ≠ 0 := by
  have hl : (X.l i).Prime := (X.lPrime i).out
  haveI : NeZero (X.l i ^ 1) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have h1 : ((X.l i ^ 1 : ℕ) : X.Ok i 1) ≠ 0 := (IsPrimitiveRoot.neZero' (X.zk_prim i 1)).out
  rw [pow_one] at h1
  have h2 : ((X.l i : ℕ) : X.O i) ≠ 0 := fun h => h1 (by
    rw [← map_natCast (algebraMap (X.O i) (X.Ok i 1)), h, map_zero])
  refine ⟨fun h => h2 (X.Ok_inj i k (by rw [map_natCast, h, map_zero])), h2, fun h => h2 (by
    rw [← map_natCast (algebraMap (X.O0 i) (X.O i)), h, map_zero])⟩

theorem isLocalHom_Ok (i : X.Tw) (k : ℕ) : IsLocalHom (algebraMap (X.O i) (X.Ok i k)) := by
  haveI := X.Ok_fin i k
  haveI : FaithfulSMul (X.O i) (X.Ok i k) := (faithfulSMul_iff_algebraMap_injective _ _).2 (X.Ok_inj i k)
  infer_instance

theorem l_not_unit (i : X.Tw) (k : ℕ) : ¬ IsUnit ((X.l i : ℕ) : X.Ok i k) ∧ ¬ IsUnit ((X.l i : ℕ) : X.O i) ∧
    ¬ IsUnit ((X.l i : ℕ) : X.O0 i) := by
  have h2 : ¬ IsUnit ((X.l i : ℕ) : X.O i) := X.O_l i
  haveI := isLocalHom_Ok i k
  refine ⟨fun h => h2 (isUnit_of_map_unit (algebraMap (X.O i) (X.Ok i k)) _ (by rwa [map_natCast])), h2,
    fun h => h2 ?_⟩
  rw [← map_natCast (algebraMap (X.O0 i) (X.O i))]
  exact h.map _

theorem isLocalHom_O (i : X.Tw) : IsLocalHom (algebraMap (X.O0 i) (X.O i)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.O0 i)
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨m, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (l_ne_zero_Ok i 0).2.2 hϖ
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hna
  rw [map_mul, map_pow] at ha
  have h1 := (isUnit_pow_iff hn).1 (isUnit_of_mul_isUnit_right ha)
  apply (l_not_unit i 0).2.1
  rw [← map_natCast (algebraMap (X.O0 i) (X.O i)), hw, map_mul, map_pow]
  exact (w.isUnit.map _).mul (h1.pow _)

section Val

variable {S : Type} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] {l : ℕ}

theorem e_pos (h0 : (l : S) ≠ 0) (h1 : ¬ IsUnit (l : S)) :
    0 < (IsDiscreteValuationRing.addVal S (l : S)).toNat := by
  rw [Nat.pos_iff_ne_zero, Ne, ENat.toNat_eq_zero]
  rintro (h | h)
  · exact h1 (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
  · exact h0 (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)

theorem addVal_l_pow (h0 : (l : S) ≠ 0) (n : ℕ) :
    IsDiscreteValuationRing.addVal S ((l : S) ^ n) = ((n * (IsDiscreteValuationRing.addVal S (l : S)).toNat : ℕ) : ℕ∞) := by
  rw [IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul, Nat.cast_mul,
    ENat.coe_toNat (by simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using h0)]

theorem nval_nonneg (x : S) : 0 ≤ nval S l x := by
  unfold nval
  positivity

theorem valE_eq (h0 : (l : S) ≠ 0) (h1 : ¬ IsUnit (l : S)) {x : S} (hx : x ≠ 0) :
    valE S l x = ENNReal.ofReal (nval S l x) := by
  have he := e_pos h0 h1
  have hT : IsDiscreteValuationRing.addVal S x ≠ ⊤ := by
    simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using hx
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hT
  unfold valE nval
  rw [← hm, ENNReal.ofReal_div_of_pos (by exact_mod_cast he)]
  simp

theorem nval_l_pow (h0 : (l : S) ≠ 0) (h1 : ¬ IsUnit (l : S)) (n : ℕ) : nval S l ((l : S) ^ n) = n := by
  have he := e_pos h0 h1
  unfold nval
  rw [IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul, ENat.toNat_mul, ENat.toNat_coe, Nat.cast_mul,
    mul_div_assoc, div_self (by exact_mod_cast he.ne'), mul_one]

end Val

theorem ordHyp_mono {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {l M R n n' v : ℕ}
    {f : MvPolynomial (Fin R ⊕ Fin R) O} (h : OrdHyp O l M R n v f) (hn : n ≤ n') : OrdHyp O l M R n' v f := by
  obtain ⟨Dd, g, h1, h2, u, m, h3, h4, h5⟩ := h
  exact ⟨Dd, g, h1, h2, u, m, h3, fun i => (h4 i).trans hn, h5⟩

theorem isAuxiliaryPlaceFamilyAtLevel_mono {i : X.Tw} {M : ℕ} {A A' : Finset (PlE D.host)} {ι : Type} {P : ι → PlE D.host} {d}
    (h : SlopeTestRemainingChoices X i M A P d) (hA : A' ⊆ A) : SlopeTestRemainingChoices X i M A' P d :=
  ⟨fun q v hv => let ⟨a, b, c, e, f, g⟩ := h.1 q v hv; ⟨a, b, c, e, fun h => f (hA h), g⟩, h.2⟩

theorem steps_mono {i : X.Tw} {M : ℕ} {H H' : Subgroup (GE N)} {z : GE N} {R : ℕ} {P : Fin R ⊕ Fin R → PlE D.host} {d}
    (h : Steps X i M H z P d) (hH : H ≤ H') : Steps X i M H' z P d :=
  ⟨fun a σ hσ => let ⟨g, hg⟩ := h.1 a σ hσ; ⟨g, hH hg⟩, h.2⟩

def prodChar {ι κ A : Type} [Fintype ι] [CommGroup A] (n : ℕ) [NeZero n] (c : ι → κ) (u : ι → A)
    (hu : ∀ q, u q ^ n = 1) : Multiplicative (κ → ZMod n) →* A where
  toFun x := ∏ q, u q ^ (Multiplicative.toAdd x (c q)).val
  map_one' := by simp
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ (hu q)]

theorem totient_bound {l k e : ℕ} (hl : l.Prime) (he : e < k) :
    1 / (Nat.totient (l ^ (k - e)) : ℝ) = (l : ℝ) ^ e / (Nat.totient (l ^ k) : ℝ) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_lt he
  have : e + a + 1 - e = a + 1 := by omega
  rw [this, Nat.totient_prime_pow_succ hl, Nat.totient_prime_pow_succ hl]
  have h1 : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have h2 : ((l - 1 : ℕ) : ℝ) ≠ 0 := by
    have := hl.two_le
    exact_mod_cast (by omega : l - 1 ≠ 0)
  push_cast
  field_simp
  ring

theorem exists_ine {i : X.Tw} {M : ℕ} (hM : 1 ≤ M) {A0 : Finset (PlE D.host)} {ι : Type} [Fintype ι]
    {P : ι → PlE D.host} {d} (h : SlopeTestRemainingChoices X i M A0 P d) {Γ : Type} [CommGroup Γ] (u : ι → Γ) (ψ : GE N →* Γ)
    (hψ : ∀ g, ψ g = ∏ q, u q ^ (Multiplicative.toAdd (d q g)).val) {q : ι} {v : PlE D.host} (hv : Over (P q) v)
    (A : ValuationSubring N.Om) (hA : IsPlaceOver A v) : ∃ σ ∈ Ine (F := D.host.E) A, ψ σ = u q := by
  have hl : (X.l i).Prime := (X.lPrime i).out
  obtain ⟨σ, hσ, h1⟩ := (h.2.2 q).2.2.2.2 v hv A hA (Multiplicative.ofAdd 1)
  refine ⟨σ, hσ, ?_⟩
  haveI : Fact (1 < X.l i ^ M) := ⟨Nat.one_lt_pow (by omega) hl.one_lt⟩
  rw [hψ, Finset.prod_eq_single q, h1, toAdd_ofAdd, ZMod.val_one, pow_one]
  · intro q' _ hq'
    rw [(h.2.2 q').2.2.2.1 v (fun hv' => hq' (h.2.1 q' q (over_of_over hv' hv))) A hA σ hσ]
    simp
  · simp

theorem tameVal_le {S : Type} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] (l : ℕ) (ψ : GE N →* Sˣ)
    (A : ValuationSubring N.Om) {σ : GE N} (hσ : σ ∈ Ine (F := D.host.E) A) (h : ψ σ ≠ 1) :
    tameVal l ψ A ≤ nval S l ((ψ σ : S) - 1) := by
  refine csInf_le ⟨0, ?_⟩ ⟨σ, hσ, h, rfl⟩
  rintro x ⟨τ, -, -, rfl⟩
  exact nval_nonneg _

theorem exists_factor (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (M : ℕ) {Q : Finset (PlE D.host)}
    (hQ : ∀ v ∈ Q, v ∉ X.S0 i) :
    ∃ f : X.RCG i Q →* Multiplicative (DelQM D.host (X.l i) Q M), f.comp (X.art i Q) = Y.delU i Q M := by
  have hl : (X.l i).Prime := (X.lPrime i).out
  haveI : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ hl.ne_zero⟩
  refine X.art_univ i Q (fun v hv h => hQ v hv (X.twistExcludedPlaces_contains_residueChar i h)) _ (fun x => ⟨M, ?_⟩) _ (Y.delU_open i Q M)
    (Y.delU_anti i Q M) (Y.delU_unr i Q M)
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext v
  rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]

theorem psiAt_prod {Γ A ι : Type} [Group Γ] [CommGroup A] [Fintype ι] (b : Bool) (ψ : Γ →* A) (ζ : A) (a n : ι → ℕ) (g : Γ)
    (h : ψ g = ∏ q, (ζ ^ a q) ^ n q) : psiAt b ψ g = ∏ q, ((if b then ζ else ζ⁻¹) ^ a q) ^ n q := by
  cases b
  · simp [psiAt, h]
  · simp [psiAt, h]

theorem vK_bounds {S : Type} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] {l : ℕ}
    (h0 : (l : S) ≠ 0) (h1 : ¬ IsUnit (l : S)) {a : S} (ha : a ≠ 0) {n : ℕ} {x : FractionRing S}
    (h : algebraMap S (FractionRing S) a = (l : FractionRing S) ^ n * x) :
    x ≠ 0 ∧ vK S l x = nval S l a - n := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact ha (IsFractionRing.injective S (FractionRing S) (by rw [h, map_zero]))
  refine ⟨hx, ?_⟩
  have hmul : ∀ {a b : S}, a ≠ 0 → b ≠ 0 → nval S l (a * b) = nval S l a + nval S l b := by
    intro a b ha hb
    unfold nval
    rw [IsDiscreteValuationRing.addVal_mul,
      ENat.toNat_add (fun h => ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp h))
        (fun h => hb (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)), Nat.cast_add, add_div]
  have hb : (l : S) ^ n ≠ 0 := pow_ne_zero n h0
  have heq : x * algebraMap S (FractionRing S) ((l : S) ^ n) = algebraMap S (FractionRing S) a := by
    rw [h, map_pow, map_natCast, mul_comm]
  unfold vK
  generalize_proofs hE
  have hinj := IsFractionRing.injective S (FractionRing S)
  have key : ∀ q : S × nonZeroDivisors S,
      x * algebraMap S (FractionRing S) q.2 = algebraMap S (FractionRing S) q.1 →
      nval S l q.1 - nval S l q.2 = nval S l a - nval S l ((l : S) ^ n) := by
    intro q hq
    have hq2 : (q.2 : S) ≠ 0 := nonZeroDivisors.ne_zero q.2.2
    have hq1 : q.1 ≠ 0 := by
      intro hzero
      rw [hzero, map_zero] at hq
      exact mul_ne_zero hx ((map_ne_zero_iff _ hinj).mpr hq2) hq
    have hcross : a * q.2 = q.1 * (l : S) ^ n := by
      apply hinj
      rw [map_mul, map_mul, ← heq, ← hq]
      ring
    have hc := congrArg (nval S l) hcross
    rw [hmul ha hq2, hmul hq1 hb] at hc
    linarith
  rw [← nval_l_pow h0 h1 n]
  exact key hE.choose hE.choose_spec

theorem exists_level (i : X.Tw) (R Dd nmax M₀ : ℕ) (I J : Type) [Finite I] [Finite J] (μ : ℕ) (v : J → ℕ)
    (F : ∀ M, M₀ ≤ M → I → MvPolynomial (Fin R ⊕ Fin R) (X.O0 i))
    (f : ∀ M, M₀ ≤ M → J → MvPolynomial (Fin R ⊕ Fin R) (X.O i))
    (hF : ∀ M h x, ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ Dd ∧
      IsDiscreteValuationRing.addVal (X.O0 i) ((F M h x).coeff m) ≤ μ)
    (hf : ∀ M h y, OrdHyp (X.O i) (X.l i) M R nmax (v y) (f M h y)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (M : ℕ) (h : M₀ ≤ M) (k : ℕ) (e : Fin R ⊕ Fin R → ℕ), 1 ≤ k ∧ k ≤ M ∧
      (∀ q, e q < k ∧ (X.l i : ℝ) ^ e q / (Nat.totient (X.l i ^ k) : ℝ) ≤ ε) ∧
      ∀ ζ : (X.Ok i k)ˣ, IsPrimitiveRoot (ζ : X.Ok i k) (X.l i ^ k) →
        (∀ x, MvPolynomial.eval₂ (phiK X i k) (fun q => ((ζ ^ (X.l i ^ e q) : (X.Ok i k)ˣ) : X.Ok i k) - 1) (F M h x) ≠ 0 ∧
          nval (X.Ok i k) (X.l i)
            (MvPolynomial.eval₂ (phiK X i k) (fun q => ((ζ ^ (X.l i ^ e q) : (X.Ok i k)ˣ) : X.Ok i k) - 1) (F M h x)) ≤
            (μ : ℝ) / ((IsDiscreteValuationRing.addVal (X.O0 i) (X.l i : X.O0 i)).toNat : ℝ) + ε) ∧
        ∀ y, MvPolynomial.aeval (fun q => ((ζ ^ (X.l i ^ e q) : (X.Ok i k)ˣ) : X.Ok i k) - 1) (f M h y) ≠ 0 ∧
          nval (X.Ok i k) (X.l i)
            (MvPolynomial.aeval (fun q => ((ζ ^ (X.l i ^ e q) : (X.Ok i k)ˣ) : X.Ok i k) - 1) (f M h y)) ≤
            (v y : ℝ) / ((IsDiscreteValuationRing.addVal (X.O i) (X.l i : X.O i)).toNat : ℝ) + ε := by
  classical
  have hl : (X.l i).Prime := (X.lPrime i).out
  haveI := X.twistBaseCoefficientRing_residueField_finite i
  haveI := isLocalHom_O i
  choose D1 g hDg using hf
  obtain ⟨M, k, e, hM, hk, hkM, he, H⟩ := _root_.GlobalTheory.OrderEval.order_eval (X.O0 i) (X.O i) (X.O_inj i) (X.l i) hl (l_ne_zero_Ok i 0).2.2
    (l_not_unit i 0).2.2 R Dd nmax M₀ I J (fun _ => μ) v (fun M x => if h : M₀ ≤ M then F M h x else 0)
    (fun M x => if h : M₀ ≤ M then f M h x else 0) (fun M x => if h : M₀ ≤ M then D1 M h x else 0)
    (fun M x => if h : M₀ ≤ M then g M h x else 0)
    (fun M h x => by simp only [dif_pos h]; exact hF M h x) (fun M h y => by simp only [dif_pos h]; exact hDg M h y) ε hε
  refine ⟨M, hM, k, e, hk, hkM, he, fun ζ hζ => ?_⟩
  haveI := isLocalHom_Ok i k
  have := H (X.Ok i k) (X.Ok_inj i k) ζ hζ
  simp only [dif_pos hM, MvPolynomial.aeval_def, MvPolynomial.eval₂_map] at this
  simp only [Units.val_pow_eq_pow_val, MvPolynomial.aeval_def]
  exact this

end GlobalTheory.TwistChoice

end
