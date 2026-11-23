module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHomReductionDescendsFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0707

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfMemAdjoinInv
section
open GlobalTheory.LN

namespace GlobalTheory.ValCrit


open Polynomial in
theorem _root_.GlobalTheory.ValCrit.isIntegral_of_mem_adjoin_inv {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (y : K) (hy : y ≠ 0)
    (h : y⁻¹ ∈ Algebra.adjoin R {y}) : IsIntegral R y⁻¹ := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h
  obtain ⟨p, hp⟩ := h
  letI : Invertible y := invertibleOfNonzero hy
  set n := p.natDegree
  have hrefl : (reflect n p).degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_le_natDegree) ?_
    have : (reflect n p).natDegree ≤ n := natDegree_reflect_le.trans (by simp [n])
    exact_mod_cast Nat.lt_succ_of_le this
  refine ⟨X ^ (n + 1) - reflect n p, monic_X_pow_sub hrefl, ?_⟩
  have key := eval₂_reflect_mul_pow (algebraMap R K) y n p le_rfl
  rw [invOf_eq_inv] at key
  have hp' : eval₂ (algebraMap R K) y p = y⁻¹ := hp
  rw [hp'] at key
  have hval : eval₂ (algebraMap R K) y⁻¹ (reflect n p) = y⁻¹ ^ (n + 1) := by
    have hyn : y ^ n ≠ 0 := pow_ne_zero _ hy
    rw [← mul_inv_cancel_right₀ hyn (eval₂ (algebraMap R K) y⁻¹ (reflect n p)), key, pow_succ,
      inv_pow, mul_comm]
  rw [eval₂_sub, eval₂_X_pow, hval, sub_self]

private theorem maximalIdeal_map_sup_span_ne_univ_of_inv_not_mem_adjoin {R K : Type} [CommRing R]
    [IsLocalRing R] [Field K] [Algebra R K] (y : K) (hnot : y⁻¹ ∉ Algebra.adjoin R {y}) :
    (IsLocalRing.maximalIdeal R).map (algebraMap R (Algebra.adjoin R {y})) ⊔
      Ideal.span {(⟨y, Algebra.self_mem_adjoin_singleton R y⟩ : Algebra.adjoin R {y})} ≠ ⊤ := by
  set S := Algebra.adjoin R {y}
  set ys : S := ⟨y, Algebra.self_mem_adjoin_singleton R y⟩
  intro hJ
  set π := Ideal.Quotient.mk (Ideal.span {ys})
  have hsurj : Function.Surjective (π.comp (algebraMap R S)) := by
    intro s
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective s
    have hs2 : (s : K) ∈ (Polynomial.aeval (R := R) y).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact s.2
    obtain ⟨f, hf⟩ := hs2
    have hfs : Polynomial.aeval ys f = s :=
      Subtype.ext (by rw [← hf, Polynomial.aeval_subalgebra_coe]; rfl)
    refine ⟨f.coeff 0, ?_⟩
    rw [← hs, ← hfs, RingHom.comp_apply]
    conv_rhs => rw [← Polynomial.X_mul_divX_add f]
    rw [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_add (f := _), map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ys), zero_mul, zero_add]
  have htop : (IsLocalRing.maximalIdeal R).map (π.comp (algebraMap R S)) = ⊤ := by
    have := congrArg (Ideal.map π) hJ
    rwa [Ideal.map_sup, Ideal.map_map, Ideal.map_quotient_self, sup_bot_eq, Ideal.map_top] at this
  obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1
    (htop ▸ Submodule.mem_top : (1 : S ⧸ Ideal.span {ys}) ∈ _)
  have hmem : ys ∣ algebraMap R S (1 - a) := by
    rw [← Ideal.mem_span_singleton, map_sub, map_one, ← Ideal.Quotient.eq]
    exact ha1.symm
  have hunitA : IsUnit (algebraMap R S (1 - a)) :=
    (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits a
      ((IsLocalRing.mem_maximalIdeal a).1 ha)).map _
  obtain ⟨u, hu⟩ := isUnit_of_dvd_unit hmem hunitA
  apply hnot
  have h1 : ((u⁻¹ : Sˣ) : S) * ys = 1 := by rw [← hu, Units.inv_mul]
  have h2 : (((u⁻¹ : Sˣ) : S) : K) = y⁻¹ := eq_inv_of_mul_eq_one_left (congrArg Subtype.val h1)
  exact h2 ▸ ((u⁻¹ : Sˣ) : S).2

theorem _root_.GlobalTheory.ValCrit.dvd_of_forall_cdvr : ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (p q : R), q ≠ 0 →
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V),
      _root_.GlobalTheory.LN.CDvr V → Function.Injective φ →
      (IsLocalRing.maximalIdeal V).comap φ = IsLocalRing.maximalIdeal R → φ q ∣ φ p) →
    q ∣ p := by
  intro R _ _ _ _ _ _ p q hq H
  by_cases hp : p = 0
  · exact hp ▸ dvd_zero q
  by_contra hdvd
  set K := FractionRing R
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hpK : algebraMap R K p ≠ 0 := (map_ne_zero_iff _ hinjK).2 hp
  have hqK : algebraMap R K q ≠ 0 := (map_ne_zero_iff _ hinjK).2 hq
  set y : K := algebraMap R K q / algebraMap R K p with hy_def
  have hy : y ≠ 0 := div_ne_zero hqK hpK
  set S := Algebra.adjoin R {y}
  have hnot : y⁻¹ ∉ S := by
    intro hmem
    have hint := _root_.GlobalTheory.ValCrit.isIntegral_of_mem_adjoin_inv y hy hmem
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine hdvd ⟨r, hinjK ?_⟩
    rw [map_mul, hr, hy_def, inv_div, mul_comm, div_mul_cancel₀ _ hqK]
  let ys : S := ⟨y, Algebra.self_mem_adjoin_singleton R y⟩
  have hinjS : Function.Injective (algebraMap R S) := by
    intro a b hab
    exact hinjK (congrArg Subtype.val hab)
  haveI : Algebra.FiniteType R S := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton y)
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  haveI : CharZero S := charZero_of_injective_algebraMap hinjS
  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) ⊔ Ideal.span {ys}
  have hJ : J ≠ ⊤ := maximalIdeal_map_sup_span_ne_univ_of_inv_not_mem_adjoin y hnot
  obtain ⟨P, hPmax, hJP⟩ := Ideal.exists_le_maximal J hJ
  have hyP : ys ∈ P := hJP (Ideal.mem_sup_right (Ideal.mem_span_singleton_self ys))
  have hcomapP : P.comap (algebraMap R S) = IsLocalRing.maximalIdeal R := by
    refine ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le ?_ ?_).symm
    · exact (hPmax.isPrime.comap (algebraMap R S)).ne_top
    · exact Ideal.map_le_iff_le_comap.1 (le_trans le_sup_left hJP)
  obtain ⟨V, _, _, _, φ, hV, hφ, hcomap⟩ :=
    _root_.GlobalTheory.PrimeUnif.exists_cdvr S P
  have hψ : Function.Injective (φ.comp (algebraMap R S)) := hφ.comp hinjS
  have hψc : (IsLocalRing.maximalIdeal V).comap (φ.comp (algebraMap R S)) =
      IsLocalRing.maximalIdeal R := by
    rw [← Ideal.comap_comap, hcomap, hcomapP]
  obtain ⟨v, hv⟩ := H V (φ.comp (algebraMap R S)) hV hψ hψc
  have hrel : ys * algebraMap R S p = algebraMap R S q := by
    apply Subtype.ext
    change y * algebraMap R K p = algebraMap R K q
    rw [hy_def, div_mul_cancel₀ _ hpK]
  have hψp : φ (algebraMap R S p) ≠ 0 := by
    intro h0
    exact hp (hψ (by simpa using h0))
  have hone : φ ys * v = 1 := by
    apply mul_left_cancel₀ hψp
    simp only [RingHom.comp_apply] at hv
    rw [← hrel, map_mul] at hv
    calc φ (algebraMap R S p) * (φ ys * v) = φ ys * φ (algebraMap R S p) * v := by ring
      _ = φ (algebraMap R S p) := hv.symm
      _ = φ (algebraMap R S p) * 1 := (mul_one _).symm
  have hunit : IsUnit (φ ys) := isUnit_iff_exists_inv.2 ⟨v, hone⟩
  have hys : ys ∉ P := by
    rw [← hcomap, Ideal.mem_comap]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h hunit
  exact hys hyP

end GlobalTheory.ValCrit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpannedByGLColumnsEqIffGLintCoset
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLatCoset

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

def vec (y : Fin m → w.adicCompletion E) : B.A := ∑ i, e.symm (y i) • b i

def crd (a : B.A) : Fin m → w.adicCompletion E := fun i => e (b.repr a i)

def IntV (y : Fin m → w.adicCompletion E) : Prop := ∀ i, y i ∈ Ov E w

lemma vec_crd (a : B.A) : vec e b (crd e b a) = a := by
  simp [vec, crd, b.sum_repr]

lemma crd_vec (y : Fin m → w.adicCompletion E) : crd e b (vec e b y) = y := by
  funext i; simp only [vec, crd]; rw [Module.Basis.repr_sum_self]; simp

lemma sum_cols (M : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (x : Fin m → w.adicCompletion E) :
    ∑ j, e.symm (x j) • vec e b (fun i => M i j) = vec e b (M *ᵥ x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [vec, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

lemma memOv (x : w.adicCompletion E) : x ∈ Ov E w ↔ Valued.v x ≤ 1 := by
  simp [Ov, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]

lemma intV_mulVec {M : Matrix (Fin m) (Fin m) (w.adicCompletion E)} (hM : ∀ i j, M i j ∈ Ov E w)
    {z : Fin m → w.adicCompletion E} (hz : IntV z) : IntV (M *ᵥ z) := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hM i j) (hz j)

lemma intV_single (j : Fin m) : IntV (w := w) (Pi.single j 1) := by
  intro i
  rcases eq_or_ne i j with rfl | h
  · simp [Subring.one_mem]
  · simp [Pi.single_apply, h, Subring.zero_mem]

lemma gl_vec (h : GL (Fin m) (w.adicCompletion E)) (z : Fin m → w.adicCompletion E) :
    (↑h⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ ((↑h : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

lemma gl_vec' (h : GL (Fin m) (w.adicCompletion E)) (z : Fin m → w.adicCompletion E) :
    (↑h : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ ((↑h⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

lemma preserves_iff (h : GL (Fin m) (w.adicCompletion E)) :
    (∀ z, IntV ((↑h : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ z) ↔ IntV z) ↔ h ∈ GLint (Fin m) (Ov E w) := by
  constructor
  · intro H
    have hh : ∀ i j, (↑h : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j ∈ Ov E w := by
      intro i j
      have := (H (Pi.single j 1)).2 (intV_single j) i
      simpa [Matrix.mulVec_single_one] using this
    have hi : ∀ i j, (↑h⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j ∈ Ov E w := by
      intro i j
      have := (H ((↑h⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ Pi.single j 1)).1 (by rw [gl_vec']; exact intV_single j) i
      simpa [Matrix.mulVec_single_one] using this
    have inj : Function.Injective ((Ov E w).subtype.mapMatrix :
        Matrix (Fin m) (Fin m) (Ov E w) →+* Matrix (Fin m) (Fin m) (w.adicCompletion E)) := by
      intro A A' hAA
      exact Matrix.ext fun i j => Subtype.ext (congrArg (fun M : Matrix (Fin m) (Fin m) (w.adicCompletion E) => M i j) hAA)
    let M1 : Matrix (Fin m) (Fin m) (Ov E w) := Matrix.of fun i j => ⟨_, hh i j⟩
    let M2 : Matrix (Fin m) (Fin m) (Ov E w) := Matrix.of fun i j => ⟨_, hi i j⟩
    have e1 : (Ov E w).subtype.mapMatrix M1 = ↑h := Matrix.ext fun i j => rfl
    have e2 : (Ov E w).subtype.mapMatrix M2 = ↑h⁻¹ := Matrix.ext fun i j => rfl
    let k : GL (Fin m) (Ov E w) :=
      ⟨M1, M2, inj (by rw [map_mul, map_one, e1, e2, ← Units.val_mul, mul_inv_cancel, Units.val_one]),
        inj (by rw [map_mul, map_one, e1, e2, ← Units.val_mul, inv_mul_cancel, Units.val_one])⟩
    exact ⟨k, Units.ext (Matrix.ext fun i j => rfl)⟩
  · rintro ⟨k, rfl⟩ z
    have ent : ∀ (k : GL (Fin m) (Ov E w)) i j,
        ((bc (Ov E w).subtype k : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j ∈ Ov E w :=
      fun k i j => (k.val i j).2
    constructor
    · intro hz
      have := intV_mulVec (ent k⁻¹) hz
      rwa [map_inv, gl_vec] at this
    · exact intV_mulVec (ent k)

lemma mem_lat (hI : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (g : GLw m w) (a : B.A) :
    a ∈ GlobalTheory.TwLat.lat e b g ↔
      IntV ((↑g⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ crd e b a) := by
  constructor
  · intro ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      have : crd e b (∑ i, e.symm ((↑g : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) • b i) =
          (↑g : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ Pi.single j 1 := by
        rw [Matrix.mulVec_single_one]
        exact crd_vec e b _
      rw [this, gl_vec]
      exact intV_single j
    | zero =>
      have : crd e b (0 : B.A) = 0 := by funext i; simp [crd]
      rw [this, Matrix.mulVec_zero]
      intro i; exact Subring.zero_mem _
    | add x y _ _ hx hy =>
      have : crd e b (x + y) = crd e b x + crd e b y := by funext i; simp [crd]
      rw [this, Matrix.mulVec_add]
      intro i; exact Subring.add_mem _ (hx i) (hy i)
    | smul c x _ hx =>
      have hc : e (algebraMap K.O K.E c) ∈ Ov E w := (memOv _).2 ((hI _).1 ⟨c, rfl⟩)
      have : crd e b (c • x) = e (algebraMap K.O K.E c) • crd e b x := by
        funext i; simp only [crd, Pi.smul_apply, smul_eq_mul]; rw [← algebraMap_smul K.E c x, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
      rw [this, Matrix.mulVec_smul]
      intro i; exact Subring.mul_mem _ hc (hx i)
  · intro hx
    set x := (↑g⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ crd e b a with hxdef
    have hr : ∀ j, e.symm (x j) ∈ (algebraMap K.O K.E).range := fun j =>
      (hI _).2 (by rw [RingEquiv.apply_symm_apply]; exact (memOv _).1 (hx j))
    choose c hc using hr
    have hsum : a = ∑ j, c j • vec e b (fun i => (↑g : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) := by
      simp_rw [← algebraMap_smul K.E (c _), hc]
      rw [sum_cols, hxdef, gl_vec', vec_crd]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem lat_coset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) →
    (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) →
    (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ)
    (b : Module.Basis (Fin m) K.E B.A),
    (∀ g g' : GLw m w, GlobalTheory.TwLat.lat e b g = GlobalTheory.TwLat.lat e b g' ↔ g⁻¹ * g' ∈ GlobalTheory.LFun.KGL w (n := m)) ∧
      ∀ g : GLw m w, GlobalTheory.UnitLemma.IsLat K.O K.E (GlobalTheory.TwLat.lat e b g) := by
  intro E _ _ _ _ w _ K e _ hI _ B m b
  refine ⟨fun g g' => ?_, fun g => ?_⟩
  · show _ ↔ g⁻¹ * g' ∈ GLint (Fin m) (Ov E w)
    rw [SetLike.ext_iff, ← preserves_iff]
    simp only [mem_lat e b hI]
    constructor
    · intro H z
      have := H (vec e b ((↑g' : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ z))
      rw [crd_vec, gl_vec] at this
      rwa [Units.val_mul, ← Matrix.mulVec_mulVec]
    · intro H a
      have := H ((↑g'⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ crd e b a)
      rwa [Units.val_mul, ← Matrix.mulVec_mulVec, gl_vec'] at this
  · refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff]
    intro a _
    have hsum : a = ∑ j, e.symm (((↑g⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ crd e b a) j) •
        vec e b (fun i => (↑g : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) := by
      rw [sum_cols, gl_vec', vec_crd]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Submodule.subset_span ⟨j, rfl⟩))

end GlobalTheory.TwLatCoset
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpannedByGLColumnsMulLeftMatrixEqMul
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwLatMul

theorem col_eq {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
    (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ}
    (b : Module.Basis (Fin m) K.E B.A) (a : B.A) (g h : GLw m w)
    (hh : h.val = GlobalTheory.TwLat.mulMat e b a * g.val) (j : Fin m) :
    ∑ i, e.symm (h.val i j) • b i = a * ∑ i, e.symm (g.val i j) • b i := by
  set M := LinearMap.toMatrix b b (LinearMap.mulLeft K.E a) with hM
  have hij : ∀ i, e.symm (h.val i j) = ∑ k, M i k * e.symm (g.val k j) := by
    intro i
    rw [hh]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, GlobalTheory.TwLat.mulMat, map_sum, map_mul, hM]
  have hab : ∀ k, a * b k = ∑ i, M i k • b i := by
    intro k
    simp only [hM, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply]
    exact (b.sum_repr _).symm
  simp_rw [hij, Finset.mul_sum, mul_smul_comm, hab, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp_rw [mul_comm]

theorem lat_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (a : B.A) (g h : GLw m w), h.val = GlobalTheory.TwLat.mulMat e b a * g.val → GlobalTheory.TwLat.lat e b h = GlobalTheory.UnitLemma.mulLat K.O a (GlobalTheory.TwLat.lat e b g) := by
  intro E _ _ _ _ w _ K e _ _ _ B m b a g h hh
  unfold GlobalTheory.TwLat.lat GlobalTheory.UnitLemma.mulLat
  rw [Submodule.map_span, ← Set.range_comp]
  refine congrArg _ (congrArg Set.range (funext fun j => ?_))
  exact col_eq e b a g h hh j

end GlobalTheory.TwLatMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordinateMatrixEquivariant
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace GlobalTheory.WigAlg

theorem mul_embeddingScalar_eq_coord_mul {E : Type} [Field E] (τ : E →+* ℂ) (c : Cinf E) (z : ℂ) :
    c * atEmb τ z = atEmb τ (coord τ c * z) := by
  classical
  unfold coord atEmb
  funext w
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw
    split_ifs <;> simp
  · split_ifs <;> simp [Pi.single_eq_of_ne hw]

end GlobalTheory.WigAlg

namespace GlobalTheory.WigAlg

end GlobalTheory.WigAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomExistsOfNoetherian
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftHom_exists_of_noetherian : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∃ f : A ⟶ B, i ≫ f.left = f₀.left ≫ j := by
  intro P H R _ I h R₀ _ π hπ hker g A₀ _ A _ i hA abA smA g' B₀ _ B _ j hB abB smB f₀ _ hfil
  obtain ⟨S, ι₀, AS₀, _, AS, _, iS, BS₀, _, BS, _, jS, fS₀, φA, φB, ψA, ψB, hfg, hι, _, hAS, hBS, abAS, smAS,
    abBS, smBS, pA, pB, qA, qB, cA, cB, cf⟩ := _root_.GlobalTheory.AbHomDesc.abelian_hom_reduction_descends R I R₀ π hπ hker g A₀ A i hA abA smA g' B₀ B j hB abB smB f₀
  have hS : (I.comap S.subtype) ^ 2 = 0 := by
    rw [Ideal.zero_eq_bot, eq_bot_iff]
    refine (Ideal.le_comap_pow _ 2).trans ?_
    rw [h, Ideal.zero_eq_bot, Ideal.comap_bot_of_injective _ Subtype.val_injective]
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  have hfilS := _root_.GlobalTheory.SqLift.push_mem_liftFil_of_injective P R I h R₀ π hπ hker S S.subtype Subtype.val_injective (I.comap S.subtype) hS
    (S ⧸ I.comap S.subtype) (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.mk_ker) ι₀ hι
    g A₀ A i hA AS₀ AS iS hAS abA smA abAS smAS φA ψA pA qA cA
    g' B₀ B j hB BS₀ BS jS hBS abB smB abBS smBS φB ψB pB qB cB f₀ fS₀ cf hfil
  obtain ⟨fS, ⟨_, efS⟩, -⟩ := (H S (I.comap S.subtype) hS (S ⧸ I.comap S.subtype) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective Ideal.mk_ker).2 g AS₀ AS iS hAS abAS smAS g' BS₀ BS jS hBS abBS smBS fS₀ hfilS
  let fl : A.left ⟶ B.left := pB.1.lift (φA ≫ fS.left) A.hom (by
    rw [Category.assoc, Over.w fS, pA.1.w])
  refine ⟨Over.homMk fl (pB.1.lift_snd _ _ _), ?_⟩
  apply pB.1.hom_ext
  · simp only [Over.homMk_left, Category.assoc, fl, pB.1.lift_fst]
    rw [reassoc_of% cA, efS, ← Category.assoc, ← cf, Category.assoc, cB]
  · simp only [Over.homMk_left, Category.assoc, fl, pB.1.lift_snd]
    rw [hA.1.w, hB.1.w, ← Category.assoc, Over.w f₀]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MuExist

def nsUnits (E : Type) [Field E] [NumberField E] [IsCMField E] : Subgroup (Neutral.B1.Ideles E) :=
  Subgroup.closure {x | ∃ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ), ¬ GlobalTheory.UnitaryBC.IsSplitAt w ∧
    Valued.v (u : w.adicCompletion E) = 1 ∧ x = Neutral.B1.localIdele E w u}

theorem localIdele_mem_nsUnits {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E))
    (u : (w.adicCompletion E)ˣ) (hw : ¬ GlobalTheory.UnitaryBC.IsSplitAt w) (hu : Valued.v (u : w.adicCompletion E) = 1) :
    Neutral.B1.localIdele E w u ∈ nsUnits E :=
  Subgroup.subset_closure ⟨w, u, hw, hu, rfl⟩

end GlobalTheory.MuExist
end
end

