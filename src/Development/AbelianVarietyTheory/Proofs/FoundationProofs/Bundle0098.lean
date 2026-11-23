module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsJointGenEigenspaceIdempotentPoly
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.GenEigIdem

open Polynomial Module

section SlopeTestRemainingChoices

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def stabAlg (Z B : Submodule K V) : Subalgebra K (Module.End K V) where
  carrier := {f | (∀ z ∈ Z, f z ∈ Z) ∧ ∀ z ∈ B, f z ∈ B}
  mul_mem' := fun {f g} hf hg =>
    ⟨fun z hz => hf.1 _ (hg.1 z hz), fun z hz => hf.2 _ (hg.2 z hz)⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun z hz => Z.add_mem (hf.1 z hz) (hg.1 z hz),
     fun z hz => B.add_mem (hf.2 z hz) (hg.2 z hz)⟩
  algebraMap_mem' := fun c =>
    ⟨fun z hz => by simpa [Module.algebraMap_end_apply] using Z.smul_mem c hz,
     fun z hz => by simpa [Module.algebraMap_end_apply] using B.smul_mem c hz⟩

def quotAlgHom (Z B : Submodule K V) :
    stabAlg Z B →ₐ[K] Module.End K (Z ⧸ B.comap Z.subtype) where
  toFun f := (B.comap Z.subtype).mapQ (B.comap Z.subtype)
    ((f : Module.End K V).restrict f.2.1) (fun z hz => f.2.2 _ hz)
  map_one' := by ext z; rfl
  map_mul' f g := by ext z; rfl
  map_zero' := by ext z; rfl
  map_add' f g := by ext z; rfl
  commutes' c := by ext z; rfl

theorem quotAlgHom_mk (Z B : Submodule K V) (f : stabAlg Z B) (z : Z) :
    quotAlgHom Z B f (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨(f : Module.End K V) z, f.2.1 z z.2⟩ := rfl

theorem quotAlgHom_mk_eq_zero (Z B : Submodule K V) (f : stabAlg Z B) (z : Z) :
    quotAlgHom Z B f (Submodule.Quotient.mk z) = 0 ↔ (f : Module.End K V) z ∈ B := by
  rw [quotAlgHom_mk, Submodule.Quotient.mk_eq_zero]; rfl

theorem exists_poly_genEig (M : Type) [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (A : Module.End K M) (c : K) :
    ∃ p : K[X], p.eval c = 1 ∧
      ∀ w, aeval A ((X - C c) ^ finrank K M) (aeval A p w) = 0 := by
  set χ := A.charpoly with hχdef
  have hχ : χ ≠ 0 := (LinearMap.charpoly_monic A).ne_zero
  set a := χ.rootMultiplicity c
  set r := χ /ₘ (X - C c) ^ a
  have hr : r.eval c ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero c hχ
  have hfac : (X - C c) ^ a * r = χ := pow_mul_divByMonic_rootMultiplicity_eq χ c
  have ha : a ≤ finrank K M := by
    have h1 : (X - C c) ^ a ∣ χ := ⟨r, hfac.symm⟩
    have h2 := natDegree_le_of_dvd h1 hχ
    rwa [natDegree_pow, natDegree_X_sub_C, mul_one, hχdef, LinearMap.charpoly_natDegree] at h2
  refine ⟨C (r.eval c)⁻¹ * r, by simp [hr], fun w => ?_⟩
  rw [← Module.End.mul_apply, ← map_mul]
  have : (X - C c) ^ finrank K M * (C (r.eval c)⁻¹ * r) =
      C (r.eval c)⁻¹ * (X - C c) ^ (finrank K M - a) * χ := by
    rw [← hfac]
    conv_lhs => rw [← Nat.sub_add_cancel ha, pow_add]
    ring
  rw [this, map_mul, LinearMap.aeval_self_charpoly, mul_zero, LinearMap.zero_apply]

end SlopeTestRemainingChoices

end GlobalTheory.GenEigIdem

namespace GlobalTheory

open Polynomial Module GlobalTheory.GenEigIdem

theorem exists_genEig_idem_poly : ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] (Z B : Submodule K V) (ι : Type) (S : ι → Prop) (T : ι → Module.End K V) (lam : ι → K), B ≤ Z → FiniteDimensional K Z → (∀ t, S t → ∀ z ∈ Z, T t z ∈ Z) → (∀ t, S t → ∀ z ∈ B, T t z ∈ B) → (∀ t t', S t → S t' → ∀ z ∈ Z, T t (T t' z) - T t' (T t z) ∈ B) → (∀ z ∈ Z, ∀ n : ℕ, (∀ t, S t → ((T t - lam t • 1) ^ n) z ∈ B) → ∀ t, S t → (T t - lam t • 1) z ∈ B) → ∃ P ∈ Algebra.adjoin K (FreeAlgebra.ι K '' {t | S t}), FreeAlgebra.lift K lam P = 1 ∧ ∀ z ∈ Z, ∀ t, S t → (T t - lam t • 1) (FreeAlgebra.lift K T P z) ∈ B := by
  intro K _ V _ _ Z B ι S T lam _hBZ hfd hZ hB hcomm hgen
  let Tg : {t // S t} → stabAlg Z B := fun t => ⟨T t.1, hZ t.1 t.2, hB t.1 t.2⟩
  let φ := quotAlgHom Z B
  let d := finrank K (Z ⧸ B.comap Z.subtype)
  have hex : ∀ t : {t // S t}, ∃ p : K[X], p.eval (lam t.1) = 1 ∧
      ∀ w, aeval (φ (Tg t)) ((X - C (lam t.1)) ^ d) (aeval (φ (Tg t)) p w) = 0 :=
    fun t => exists_poly_genEig _ _ _
  choose p hp1 hp2 using hex
  let N : {t // S t} → Submodule K (Z ⧸ B.comap Z.subtype) := fun t =>
    LinearMap.ker (aeval (φ (Tg t)) ((X - C (lam t.1)) ^ d))
  let Ninf : Finset {t // S t} → Submodule K (Z ⧸ B.comap Z.subtype) := fun F => ⨅ t ∈ F, N t
  obtain ⟨F, -, hF⟩ := (measure fun F : Finset {t // S t} => finrank K (Ninf F)).wf.has_min
    Set.univ ⟨∅, trivial⟩
  classical
  have hFle : ∀ s, Ninf F ≤ N s := by
    intro s
    have hins : Ninf (insert s F) = N s ⊓ Ninf F := Finset.iInf_insert _ _ _
    have hmin : ¬ finrank K (Ninf (insert s F)) < finrank K (Ninf F) := hF (insert s F) trivial
    have heq : Ninf (insert s F) = Ninf F := by
      apply Submodule.eq_of_le_of_finrank_le
      · rw [hins]; exact inf_le_right
      · exact not_lt.mp hmin
    rw [← heq, hins]; exact inf_le_left
  have hinv : ∀ (s t : {t // S t}) (q : K[X]) (w : Z ⧸ B.comap Z.subtype), w ∈ N t →
      aeval (φ (Tg s)) q w ∈ N t := by
    intro s t q w hw
    have hc : Commute (φ (Tg s)) (φ (Tg t)) := by
      refine LinearMap.ext fun w => Submodule.Quotient.induction_on _ w fun z => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, quotAlgHom_mk, quotAlgHom_mk, quotAlgHom_mk,
        quotAlgHom_mk, Submodule.Quotient.eq]
      exact hcomm s.1 t.1 s.2 t.2 z z.2
    have hc2 : Commute (aeval (φ (Tg s)) q) (aeval (φ (Tg t)) ((X - C (lam t.1)) ^ d)) :=
      Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton K _)
        (Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton K _)
          hc.symm).symm
    have hw' := LinearMap.mem_ker.mp hw
    refine LinearMap.mem_ker.mpr ?_
    rw [← Module.End.mul_apply, ← hc2.eq, Module.End.mul_apply, hw', map_zero]
  have hprod : ∀ (l : List {t // S t}) (w : Z ⧸ B.comap Z.subtype) (t : {t // S t}), t ∈ l →
      φ (l.map fun s => aeval (Tg s) (p s)).prod w ∈ N t := by
    intro l
    induction l with
    | nil => intro w t ht; simp at ht
    | cons a l ih =>
      intro w t ht
      rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ← aeval_algHom_apply]
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact LinearMap.mem_ker.mpr (hp2 _ _)
      · exact hinv _ _ _ _ (ih _ _ ht')
  let P : FreeAlgebra K ι := (F.toList.map fun t => aeval (FreeAlgebra.ι K t.1) (p t)).prod
  let Q : stabAlg Z B := (F.toList.map fun t => aeval (Tg t) (p t)).prod
  have hPQ : FreeAlgebra.lift K T P = (Q : Module.End K V) := by
    rw [show (Q : Module.End K V) = (stabAlg Z B).val Q from rfl]
    simp only [P, Q, map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply]
    rw [← aeval_algHom_apply, ← aeval_algHom_apply, FreeAlgebra.lift_ι_apply]
    rfl
  have hPmem : P ∈ Algebra.adjoin K (FreeAlgebra.ι K '' {t | S t}) := by
    refine Subalgebra.list_prod_mem _ fun x hx => ?_
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_image_of_mem (FreeAlgebra.ι K) (show t.1 ∈ {t | S t} from t.2)))
      (aeval_mem_adjoin_singleton K _)
  have hPlam : FreeAlgebra.lift K lam P = 1 := by
    simp only [P, map_list_prod, List.map_map]
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    simp only [Function.comp_apply]
    rw [← aeval_algHom_apply, FreeAlgebra.lift_ι_apply, coe_aeval_eq_eval, hp1]
  refine ⟨P, hPmem, hPlam, fun z hz s hs => ?_⟩
  rw [hPQ]
  have hQz : (Q : Module.End K V) z ∈ Z := Q.2.1 z hz
  refine hgen _ hQz d (fun t ht => ?_) s hs
  let U : stabAlg Z B := (Tg ⟨t, ht⟩ - algebraMap K (stabAlg Z B) (lam t)) ^ d
  have hU : (U : Module.End K V) = (T t - lam t • 1) ^ d := by
    simp [U, Tg, Algebra.algebraMap_eq_smul_one]
  rw [← hU]
  have key : φ U (Submodule.Quotient.mk ⟨(Q : Module.End K V) z, hQz⟩) = 0 := by
    have h1 : φ Q (Submodule.Quotient.mk ⟨z, hz⟩) =
        Submodule.Quotient.mk ⟨(Q : Module.End K V) z, hQz⟩ := quotAlgHom_mk _ _ _ _
    rw [← h1]
    have hφU : φ U = aeval (φ (Tg ⟨t, ht⟩)) ((X - C (lam t)) ^ d) := by
      simp [U]
    rw [hφU]
    refine LinearMap.mem_ker.mp (hFle ⟨t, ht⟩ ?_)
    simp only [Ninf, Submodule.mem_iInf]
    intro s' hs'
    exact hprod _ _ _ (Finset.mem_toList.mpr hs')
  exact (quotAlgHom_mk_eq_zero Z B U _).mp key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroHalfStandardAltFormConstOfExponentOn
section
open Function

namespace GlobalTheory

section General

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem pow_succ_dvd_bilin_of_const_on_cosets (h2 : IsUnit (2 : R)) (r : R)
    (B : LinearMap.BilinForm R M) (hB : ∀ x y, B x y = B y x) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + r • a) (c : R) (hc : ∀ t ∈ T, B t t = c) (i : ℕ)
    (hi : ∀ x y, r ^ i ∣ B x y) (x y : M) : r ^ (i + 1) ∣ B x y := by
  have h1 : ∀ z, r ^ (i + 1) ∣ B z z - c := by
    intro z
    obtain ⟨t, ht, a, rfl⟩ := hT z
    have : B (t + r • a) (t + r • a) - c = (B t a + B a t + r * B a a) * r := by
      simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        ← hc t ht]
      ring
    rw [this, pow_succ]
    exact mul_dvd_mul_right (((hi _ _).add (hi _ _)).add ((hi _ _).mul_left _)) r
  have h0 : r ^ (i + 1) ∣ c := by simpa using h1 0
  have h3 : ∀ z, r ^ (i + 1) ∣ B z z := fun z => by simpa using (h1 z).add h0
  have h4 : 2 * B x y = B (x + y) (x + y) - B x x - B y y := by
    simp only [map_add (f := _), LinearMap.add_apply, hB y x]
    ring
  exact h2.dvd_mul_left.1 (h4 ▸ ((h3 _).sub (h3 _)).sub (h3 _))

theorem bilin_eq_zero_of_const_on_cosets (h2 : IsUnit (2 : R)) {r : R} (hr : IsNilpotent r)
    (B : LinearMap.BilinForm R M) (hB : ∀ x y, B x y = B y x) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + r • a) (c : R) (hc : ∀ t ∈ T, B t t = c) : B = 0 := by
  have h : ∀ (i : ℕ) (x y : M), r ^ i ∣ B x y := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => exact pow_succ_dvd_bilin_of_const_on_cosets h2 r B hB T hT c hc i ih
  obtain ⟨k, hk⟩ := hr
  ext x y
  simpa [hk] using h k x y

theorem end_eq_zero_of_quad_const_on_cosets (h2 : IsUnit (2 : R)) {r : R} (hr : IsNilpotent r)
    (ω : LinearMap.BilinForm R M) (hω : Injective ω) (S : M →ₗ[R] M)
    (hS : ∀ x y, ω (S x) y = ω (S y) x) (u : Rˣ) (q : M → R)
    (hq : ∀ x, 2 * q x = u * ω (S x) x) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + r • a) (c : R) (hc : ∀ t ∈ T, q t = c) : S = 0 := by
  have h : (ω ∘ₗ S : LinearMap.BilinForm R M) = 0 := by
    refine bilin_eq_zero_of_const_on_cosets h2 hr (ω ∘ₗ S) hS T hT (↑u⁻¹ * (2 * c)) fun t ht => ?_
    rw [← hc t ht, hq, Units.inv_mul_cancel_left]
    rfl
  ext x
  exact hω ((LinearMap.congr_fun h x).trans (by simp))

end General

section ZMod

variable {n k : ℕ}

theorem isUnit_two_zmod_pow (hn : Odd n) (k : ℕ) : IsUnit (2 : ZMod (n ^ k)) := by
  have h : Nat.Coprime 2 (n ^ k) := (Nat.coprime_two_left.2 hn).pow_right k
  simpa using (ZMod.isUnit_iff_coprime 2 (n ^ k)).2 h

theorem exists_eq_nsmul_of_nsmul_eq_zero_zmod (hn : n ≠ 0) (hk : 2 ≤ k) (x : ZMod (n ^ k))
    (hx : n • x = 0) : ∃ a, x = n • a := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have h1 : (((n : ℤ) * z : ℤ) : ZMod (n ^ (j + 2))) = 0 := by
    rw [← hx]; simp
  obtain ⟨w, hw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1
  have h2 : z = n * ((n : ℤ) ^ j * w) := by
    apply mul_left_cancel₀ (Int.natCast_ne_zero.2 hn)
    rw [hw]; push_cast; ring
  exact ⟨(((n : ℤ) ^ j * w : ℤ) : ZMod (n ^ (j + 2))), by rw [h2]; simp⟩

end ZMod

section LevelForm

open ReciprocityTheory.ChartRestriction.G.Out

theorem injective_toBilin'_stdSymp {R : Type*} [CommRing R] (g : ℕ) :
    Injective (Matrix.toBilin' (Matrix.of fun i j => ((stdSymp g i j : ℤ) : R))) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  funext i
  have key : ∀ j, ∑ l, x l * ((stdSymp g l j : ℤ) : R) = 0 := fun j => by
    have := LinearMap.congr_fun hx (Pi.single j 1)
    simpa [Matrix.toBilin'_apply, Pi.single_apply] using this
  by_cases hi : (i : ℕ) < g
  · have h := key ⟨i + g, by omega⟩
    rw [Finset.sum_eq_single i] at h
    · simpa [stdSymp, hi] using h
    · intro l _ hl
      have h1 : (l : ℕ) ≠ i := fun h => hl (Fin.ext h)
      have : stdSymp g l ⟨i + g, by omega⟩ = 0 := by
        unfold stdSymp
        rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
      simp [this]
    · simp
  · have hi2 := i.2
    have h := key ⟨i - g, by omega⟩
    rw [Finset.sum_eq_single i] at h
    · have : stdSymp g i ⟨i - g, by omega⟩ = -1 := by
        unfold stdSymp
        rw [if_neg (by simp only; omega), if_pos (by simp only; omega)]
      simpa [this] using h
    · intro l _ hl
      have h1 : (l : ℕ) ≠ i := fun h => hl (Fin.ext h)
      have : stdSymp g l ⟨i - g, by omega⟩ = 0 := by
        unfold stdSymp
        rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
      simp [this]
    · simp

end LevelForm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldExpansionCoeffs
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.NF
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem exp_inj (X : Tower Ω ε) : Function.Injective X.exp :=
  (X.exp : X.K →+* HahnSeries ℚ Ω).injective

theorem gal_alg (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply exp_inj X
  ext r
  rw [X.gal_exp, AlgHom.commutes, AlgHom.commutes, HahnSeries.algebraMap_apply', HahnSeries.algebraMap_apply']
  by_cases h : r = 0 <;> simp [h, HahnSeries.coeff_single]

theorem gal_j (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.gal s X.jK = X.jK := by
  apply exp_inj X
  ext r
  rw [X.gal_exp]
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [hn, map_intCast]

theorem gal_aeval (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (p : Polynomial Ω) (h : ∀ c ∈ p.coeffs, s c = c) :
    X.gal s (Polynomial.aeval X.jK p) = Polynomial.aeval X.jK p := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.aeval_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, map_pow, gal_j, gal_alg]
  by_cases h0 : p.coeff i = 0
  · simp [h0]
  · rw [h _ (Polynomial.coeff_mem_coeffs h0)]

theorem exists_poly (X : Tower Ω ε) (f : X.K) : ∃ (C : Set Ω) (P : Polynomial X.K), C.Finite ∧ P ≠ 0 ∧
    ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ c ∈ C, s c = c) → P.IsRoot (X.gal s f) := by
  obtain ⟨p, hp, hf⟩ := X.alg_j f
  have key : ∀ i : ℕ, ∃ u v : Polynomial Ω, (p.coeff i : X.K) = Polynomial.aeval X.jK u / Polynomial.aeval X.jK v :=
    fun i => (IntermediateField.mem_adjoin_simple_iff Ω _).1 (p.coeff i).2
  choose u v huv using key
  refine ⟨⋃ i ∈ p.support, ((u i).coeffs ∪ (v i).coeffs : Set Ω), p.map (algebraMap _ X.K), ?_, ?_, ?_⟩
  · exact Set.Finite.biUnion (Finset.finite_toSet _) fun i _ => (Finset.finite_toSet _).union (Finset.finite_toSet _)
  · exact Polynomial.map_ne_zero hp
  · intro s hs
    have hP : (p.map (algebraMap _ X.K)).map (X.gal s : X.K →+* X.K) = p.map (algebraMap _ X.K) := by
      ext i
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      by_cases h0 : p.coeff i = 0
      · simp [h0]
      · have hi : i ∈ p.support := Polynomial.mem_support_iff.2 h0
        show X.gal s (p.coeff i : X.K) = (p.coeff i : X.K)
        rw [huv, map_div₀, gal_aeval X s _ fun c hc => hs c (Set.mem_biUnion hi (Or.inl hc)),
          gal_aeval X s _ fun c hc => hs c (Set.mem_biUnion hi (Or.inr hc))]
    have h1 : (p.map (algebraMap _ X.K)).IsRoot f := by
      rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, hf]
    rw [← hP]
    exact Polynomial.IsRoot.map (f := (X.gal s : X.K →+* X.K)) h1

theorem coeff_numberField {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (f : X.K) :
    ∃ F : IntermediateField ℚ Ω, FiniteDimensional ℚ F ∧ ∀ r : ℚ, (X.exp f).coeff r ∈ F := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨C, P, hC, hP, hroot⟩ := exists_poly X f
  haveI := hC.to_subtype
  let F₀ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ C
  haveI : FiniteDimensional ℚ F₀ :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : @IsScalarTower ℚ F₀ Ω Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Normal F₀ Ω := IntermediateField.normal ℚ Ω F₀
  let L : Finset ℚ → IntermediateField F₀ Ω := fun T =>
    IntermediateField.adjoin F₀ ((T.image fun r => (X.exp f).coeff r : Finset Ω) : Set Ω)
  have hfin : ∀ T, FiniteDimensional F₀ (L T) := fun T =>
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hb : ∀ T, Module.finrank F₀ (L T) ≤ P.natDegree := by
    intro T
    haveI := hfin T
    haveI : Algebra.IsSeparable F₀ (L T) := by
      haveI : CharZero F₀ := algebraRat.charZero F₀
      infer_instance
    rw [← AlgHom.card F₀ (L T) Ω]
    let e : (L T →ₐ[F₀] Ω) → (Ω ≃ₐ[ℚ] Ω) := fun σ =>
      (AlgEquiv.ofBijective (σ.liftNormal Ω) (Algebra.IsAlgebraic.algHom_bijective _)).restrictScalars ℚ
    have he : ∀ σ (x : L T), e σ x = σ x := fun σ x => σ.liftNormal_commutes Ω x
    have hm : ∀ σ, X.gal (e σ) f ∈ P.roots.toFinset := by
      intro σ
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
      exact hroot _ fun c hc => (σ.liftNormal Ω).commutes (⟨c, IntermediateField.subset_adjoin ℚ C hc⟩ : F₀)
    calc Fintype.card (L T →ₐ[F₀] Ω) ≤ P.roots.toFinset.card := by
          rw [← Finset.card_univ]
          refine Finset.card_le_card_of_injOn (fun σ => X.gal (e σ) f) (fun σ _ => hm σ) ?_
          intro σ _ τ _ h
          apply IntermediateField.adjoin_algHom_ext
          intro x hx
          rw [← he, ← he]
          obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hx
          show e σ ((X.exp f).coeff r) = e τ ((X.exp f).coeff r)
          rw [← X.gal_exp, ← X.gal_exp]
          exact congrArg (fun g => (X.exp g).coeff r) h
      _ ≤ _ := (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P)
  have hB : BddAbove (Set.range fun T => Module.finrank F₀ (L T)) := ⟨P.natDegree, by rintro _ ⟨T, rfl⟩; exact hb T⟩
  obtain ⟨T, hT⟩ := Nat.sSup_mem (Set.range_nonempty fun T => Module.finrank F₀ (L T)) hB
  haveI := hfin T
  refine ⟨(L T).restrictScalars ℚ, FiniteDimensional.trans ℚ F₀ (L T), fun r => ?_⟩
  haveI := hfin (insert r T)
  have h : L T = L (insert r T) := by
    refine IntermediateField.eq_of_le_of_finrank_le (IntermediateField.adjoin.mono _ _ _ ?_) ?_
    · exact Finset.coe_subset.2 (Finset.image_subset_image (Finset.subset_insert _ _))
    · exact (le_csSup hB ⟨_, rfl⟩).trans hT.ge
  rw [IntermediateField.mem_restrictScalars, h]
  exact IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _)))

end GlobalTheory.KZ.ES.NF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowDivPrimeZpowIntegralClosureUnitStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_div_prime_zpow_integralClosure_unit : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ x : Ω, x ≠ 0 → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ IsInt (p := p) (x ^ b / (p : Ω) ^ a) ∧
    IsInt (p := p) ((p : Ω) ^ a / x ^ b) := by
  intro p _ Ω _ _ hΩ x hx
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
  have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [hmax]
    exact o0_isAdicComplete_span_p p
  have : FaithfulSMul (O0 p) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hΩ.inj
  let _ : Algebra (FractionRing (O0 p)) Ω := FractionRing.liftAlgebra (O0 p) Ω
  have : IsScalarTower (O0 p) (FractionRing (O0 p)) Ω :=
    FractionRing.isScalarTower_liftAlgebra (O0 p) Ω
  have : Algebra.IsAlgebraic (O0 p) Ω := hΩ.alg
  have : Algebra.IsAlgebraic (FractionRing (O0 p)) Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
  have hIntegral := exists_pow_div_zpow_isIntegral (O0 p) (FractionRing (O0 p)) Ω (p : O0 p)
    hirr x hx
  simpa only [IsInt, map_natCast] using hIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSlTwoIntSmulOfFixesJK
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES.JStab

theorem eps_eOm_of_alg {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (x : ℚ) : ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hε : Function.Injective ε := ε.injective
  unfold eOm
  apply Function.invFun_eq
  haveI : NeZero (x.den : Ω) := ⟨by exact_mod_cast x.den_nz⟩
  obtain ⟨ζ, hζ0⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic x.den Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 x.den_pos).ne')
  have hζ : IsPrimitiveRoot ζ x.den := (Polynomial.isRoot_cyclotomic_iff).1 hζ0
  have hζ' : IsPrimitiveRoot (ε ζ) x.den := hζ.map_of_injective hε
  haveI : NeZero x.den := ⟨x.den_nz⟩
  have hpow : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have hx : (x : ℂ) * x.den = x.num := by exact_mod_cast Rat.mul_den_eq_num x
    calc (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = ((x : ℂ) * x.den) * (2 * Real.pi * Complex.I) := by ring
      _ = _ := by rw [hx]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

theorem eOm_ne_zero' {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    eOm ε x ≠ 0 := by
  intro h0
  have := eps_eOm_of_alg ε x
  rw [h0, map_zero] at this
  exact Complex.exp_ne_zero _ this.symm

end GlobalTheory.KZ.ES.JStab
end
end

