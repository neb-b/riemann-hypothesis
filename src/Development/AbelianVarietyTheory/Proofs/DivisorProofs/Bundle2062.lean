module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentsAbelianSchemeConstantDimension
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DimSplit

theorem idem_eq_of {S : Type} [CommRing S] {a b : S} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : ∀ q : PrimeSpectrum S, a ∉ q.asIdeal ↔ b ∉ q.asIdeal) : a = b := by
  have := (PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).injective
    (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (by
      ext q
      show q ∈ PrimeSpectrum.basicOpen a ↔ q ∈ PrimeSpectrum.basicOpen b
      simp only [PrimeSpectrum.mem_basicOpen]
      exact hab q)
  exact congrArg Subtype.val this

theorem exists_idempotents_of_isLocallyConstant {R α : Type} [CommRing R] (d : PrimeSpectrum R → α)
    (hd : IsLocallyConstant d) :
    ∃ (n : ℕ) (e : Fin n → R), CompleteOrthogonalIdempotents e ∧
      ∀ k, ∃ a : α, ∀ p : PrimeSpectrum R, 1 - e k ∈ p.asIdeal → d p = a := by
  classical
  have hfin : (Set.range d).Finite := hd.range_finite
  let s := hfin.toFinset
  let g : Fin s.card → α := fun k => (s.equivFin.symm k).1
  have hg : Function.Injective g := fun i j h => s.equivFin.symm.injective (Subtype.val_injective h)
  let C : Fin s.card → TopologicalSpace.Clopens (PrimeSpectrum R) := fun k =>
    ⟨d ⁻¹' {g k}, hd.isClopen_fiber _⟩
  let e : Fin s.card → R := fun k => ((PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm (C k)).1
  have he : ∀ k, IsIdempotentElem (e k) := fun k =>
    ((PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).symm (C k)).2
  have hmem : ∀ k (p : PrimeSpectrum R), e k ∉ p.asIdeal ↔ d p = g k := by
    intro k p
    have h := PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm (R := R) (C k)
    rw [← PrimeSpectrum.mem_basicOpen]
    show p ∈ PrimeSpectrum.basicOpen (e k) ↔ _
    rw [h]
    rfl
  have horth : OrthogonalIdempotents e := by
    refine ⟨he, fun i j hij => idem_eq_of ((he i).mul (he j)) IsIdempotentElem.zero fun q => ?_⟩
    refine ⟨fun h => ?_, fun h => absurd q.asIdeal.zero_mem h⟩
    have hi : e i ∉ q.asIdeal := fun hi => h (q.asIdeal.mul_mem_right _ hi)
    have hj : e j ∉ q.asIdeal := fun hj => h (q.asIdeal.mul_mem_left _ hj)
    exact absurd (hg (((hmem i q).1 hi).symm.trans ((hmem j q).1 hj))) hij
  refine ⟨s.card, e, ⟨horth, ?_⟩, fun k => ⟨g k, fun p hp => (hmem k p).1 fun hk => ?_⟩⟩
  · refine idem_eq_of horth.isIdempotentElem_sum IsIdempotentElem.one fun q => ?_
    refine ⟨fun _ => q.isPrime.ne_top ∘ (Ideal.eq_top_iff_one _).2, fun _ hsum => ?_⟩
    have hq : d q ∈ s := hfin.mem_toFinset.2 ⟨q, rfl⟩
    let k := s.equivFin ⟨d q, hq⟩
    have hk : g k = d q := by simp [g, k]
    have hrest : ∑ j ∈ Finset.univ.erase k, e j ∈ q.asIdeal := by
      refine Ideal.sum_mem _ fun j hj => ?_
      by_contra hj'
      exact (Finset.ne_of_mem_erase hj) (hg (((hmem j q).1 hj').symm.trans hk.symm))
    have : e k ∈ q.asIdeal := by
      have h2 := q.asIdeal.sub_mem hsum hrest
      rwa [← Finset.add_sum_erase _ _ (Finset.mem_univ k), add_sub_cancel_right] at h2
    exact (hmem k q).2 hk.symm this
  · exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using p.asIdeal.add_mem hp hk))

end GlobalTheory.DimSplit

namespace GlobalTheory.DimSplit

theorem exists_idempotents_smoothOfRelativeDimension : ∀ (R₀ : Type) [CommRing R₀] (A : Over (Sp R₀)) [GrpObj A],
    IsAbelianScheme A → ∃ (n : ℕ) (e : Fin n → R₀), CompleteOrthogonalIdempotents e ∧ ∀ k, ∃ g : ℕ,
      SmoothOfRelativeDimension g (Limits.pullback.snd A.hom (spMap (Ideal.Quotient.mk (Ideal.span {1 - e k})))) := by
  intro R₀ _ A _ hA
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim A.hom
  have loc : ∀ x y, y ∈ W x → n y = n x := fun x y hy => by
    have := hd x
    have := hd y
    have e₁ : SmoothOfRelativeDimension (0 + n y) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W y ⊓ W x ≤ W y), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + n x) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W y ⊓ W x ≤ W x), Category.assoc]; infer_instance
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨y, hW y, hy⟩
  have hc : IsLocallyConstant n :=
    (IsLocallyConstant.iff_exists_open n).2 fun x => ⟨W x, (W x).isOpen, hW x, loc x⟩
  have fib : ∀ x y, A.hom x = A.hom y → n x = n y := fun x y h =>
    hc.apply_eq_of_isPreconnected (A.hom.isConnected_preimage_singleton (A.hom x)).isPreconnected
      rfl h.symm
  have hsurj : Function.Surjective A.hom := (inferInstance : Surjective A.hom).surj
  let d : PrimeSpectrum R₀ → ℕ := fun p => n (Classical.choose (hsurj p))
  have hdn : ∀ x, d (A.hom x) = n x := fun x => fib _ _ (Classical.choose_spec (hsurj (A.hom x)))
  have hdl : IsLocallyConstant d := by
    refine (IsLocallyConstant.iff_isOpen_fiber).2 fun g => ?_
    have hcl : IsClosed (A.hom '' (n ⁻¹' {g})ᶜ) :=
      A.hom.isClosedMap _ (hc.isOpen_fiber g).isClosed_compl
    have heq : (d ⁻¹' {g})ᶜ = A.hom '' (n ⁻¹' {g})ᶜ := by
      ext p
      refine ⟨fun hp => ⟨_, hp, Classical.choose_spec (hsurj p)⟩, ?_⟩
      rintro ⟨x, hx, rfl⟩
      exact fun h => hx (show n x = g from (hdn x).symm.trans h)
    rw [← isClosed_compl_iff, heq]
    exact hcl
  obtain ⟨m, e, he, hk⟩ := exists_idempotents_of_isLocallyConstant d hdl
  refine ⟨m, e, he, fun k => ?_⟩
  obtain ⟨g, hg⟩ := hk k
  refine ⟨g, GlobalTheory.SmoothNearFibre.smoothOfRelativeDimension_pullback_snd A.hom _ g fun z w hzw => ⟨W z, hW z, ?_⟩⟩
  have hn : n z = g := by
    rw [← hdn z, hzw]
    apply hg
    show Ideal.Quotient.mk _ (1 - e k) ∈ w.asIdeal
    have h0 : Ideal.Quotient.mk (Ideal.span {1 - e k}) (1 - e k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _))
    rw [h0]
    exact w.asIdeal.zero_mem
  rw [← hn]
  exact hd z

end GlobalTheory.DimSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelTor

theorem zeta_pow_div_of_dvd {n N : ℕ} (hN : N ≠ 0) (h : n ∣ N) : zeta N ^ (N / n) = zeta n := by
  obtain ⟨c, rfl⟩ := h
  have hn : n ≠ 0 := left_ne_zero_of_mul hN
  have hc : c ≠ 0 := right_ne_zero_of_mul hN
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn), zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem cycAway_le_of_dvd {n N : ℕ} (hN : N ≠ 0) (h : n ∣ N) : cycAway n ≤ cycAway N := by
  refine Subring.closure_le.2 ?_
  rintro x (rfl | rfl)
  · rw [← zeta_pow_div_of_dvd hN h]
    exact pow_mem (zetaAway N).2 _
  · obtain ⟨c, rfl⟩ := h
    have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (right_ne_zero_of_mul hN)
    have e : (n : ℂ)⁻¹ = (c : ℂ) * ((n * c : ℕ) : ℂ)⁻¹ := by
      push_cast
      field_simp
    rw [e]
    exact mul_mem (natCast_mem _ _) (Subring.subset_closure (Or.inr rfl))

theorem zetaAway_pow_self {N : ℕ} (hN : N ≠ 0) : zetaAway N ^ N = 1 :=
  Subtype.ext (Complex.isPrimitiveRoot_exp N hN).pow_eq_one

theorem formallyUnramified_cycAway {N : ℕ} (hN : N ≠ 0) (R : Type) [CommRing R] [Algebra R (cycAway N)] :
    Algebra.FormallyUnramified R (cycAway N) := by
  have hD : ∀ x : cycAway N, KaehlerDifferential.D R (cycAway N) x = 0 := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · have h := congrArg (KaehlerDifferential.D R (cycAway N)) (zetaAway_pow_self hN)
        rw [Derivation.leibniz_pow, Derivation.map_one_eq_zero, ← Nat.cast_smul_eq_nsmul (cycAway N), smul_smul] at h
        have hu : IsUnit ((N : cycAway N) * zetaAway N ^ (N - 1)) :=
          (isUnit_natCast hN).mul ((IsUnit.of_pow_eq_one (zetaAway_pow_self hN) hN).pow _)
        exact hu.smul_eq_zero.1 h
      · let v : cycAway N := ⟨(N : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
        have hv : (N : cycAway N) * v = 1 :=
          Subtype.ext (by simpa [v] using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN : (N : ℂ) ≠ 0))
        have h := congrArg (KaehlerDifferential.D R (cycAway N)) hv
        rw [Derivation.leibniz, Derivation.map_one_eq_zero, Derivation.map_natCast, smul_zero, add_zero] at h
        exact (isUnit_natCast hN).smul_eq_zero.1 h
    | zero => exact map_zero _
    | one => exact Derivation.map_one_eq_zero _
    | add x y hx' hy' hx hy =>
      have := map_add (KaehlerDifferential.D R (cycAway N)) ⟨x, hx'⟩ ⟨y, hy'⟩
      rw [hx, hy, add_zero] at this
      exact this
    | neg x hx' hx =>
      have := map_neg (KaehlerDifferential.D R (cycAway N)) ⟨x, hx'⟩
      rw [hx, neg_zero] at this
      exact this
    | mul x y hx' hy' hx hy =>
      have := (KaehlerDifferential.D R (cycAway N)).leibniz ⟨x, hx'⟩ ⟨y, hy'⟩
      rw [hx, hy, smul_zero, smul_zero, add_zero] at this
      exact this
  refine ⟨subsingleton_of_forall_eq 0 fun ω => ?_⟩
  have hω : ω ∈ Submodule.span (cycAway N) (Set.range (KaehlerDifferential.D R (cycAway N))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine (Submodule.mem_bot (cycAway N)).1 (Submodule.span_le.2 ?_ hω)
  rintro _ ⟨x, rfl⟩
  exact (Submodule.mem_bot (cycAway N)).2 (hD x)

theorem isIntegral_inclusion_cycAway {n N a : ℕ} (hN : N ≠ 0) (h : n ∣ N) (ha : N ∣ n ^ a) :
    (Subring.inclusion (cycAway_le_of_dvd hN h)).IsIntegral := by
  have hn : n ≠ 0 := fun h0 => hN (by simpa [h0] using h)
  rintro ⟨x, hx⟩
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨Polynomial.X ^ N - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hN, by
        simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, map_one, Polynomial.eval₂_one]
        exact sub_eq_zero.2 (zetaAway_pow_self hN)⟩
    · obtain ⟨c, hc⟩ := ha
      let v : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
      have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
      have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
      have hc' : (n : ℂ) ^ a = N * c := by exact_mod_cast hc
      convert RingHom.isIntegralElem_map (Subring.inclusion (cycAway_le_of_dvd hN h)) (x := (c : cycAway n) * v ^ a)
      refine Subtype.ext ?_
      change (N : ℂ)⁻¹ = (c : ℂ) * ((n : ℂ)⁻¹) ^ a
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← _root_.mul_assoc, ← hc', ← mul_pow, mul_inv_cancel₀ hn', one_pow]
  | zero => exact RingHom.isIntegralElem_zero _
  | one => exact RingHom.isIntegralElem_one _
  | add x y _ _ hx hy => exact hx.add _ hy
  | neg x _ hx => exact hx.neg _
  | mul x y _ _ hx hy => exact hx.mul _ hy

theorem exists_inclusion_cycAway : ∀ n N : ℕ, N ≠ 0 → n ∣ N → ∃ j : cycAway n →+* cycAway N, Function.Injective j ∧
    j (zetaAway n) = zetaAway N ^ (N / n) ∧
    ((∃ a, N ∣ n ^ a) → IsFinite (spMap j) ∧ Etale (spMap j) ∧ Surjective (spMap j)) := by
  intro n N hN h
  have hn : n ≠ 0 := fun h0 => hN (by simpa [h0] using h)
  let j := Subring.inclusion (cycAway_le_of_dvd hN h)
  have hj : Function.Injective j := Subring.inclusion_injective _
  refine ⟨j, hj, Subtype.ext (zeta_pow_div_of_dvd hN h).symm, fun ⟨a, ha⟩ => ?_⟩
  have hint : j.IsIntegral := isIntegral_inclusion_cycAway hN h ha
  letI := j.toAlgebra
  have : IsDedekindDomain (cycAway n) := (arBase_cycAway n hn).1
  have : Algebra.IsIntegral (cycAway n) (cycAway N) := ⟨hint⟩
  have := finiteType_cycAway N
  have : Algebra.FiniteType (cycAway n) (cycAway N) := .of_restrictScalars_finiteType ℤ _ _
  have hfin : Module.Finite (cycAway n) (cycAway N) := Algebra.IsIntegral.finite
  have : FaithfulSMul (cycAway n) (cycAway N) := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
  have : Module.Flat (cycAway n) (cycAway N) := inferInstance
  have : Algebra.FinitePresentation (cycAway n) (cycAway N) := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have := formallyUnramified_cycAway hN (cycAway n)
  have het : Algebra.Etale (cycAway n) (cycAway N) := Algebra.Etale.of_formallyUnramified_of_flat
  refine ⟨(IsFinite.SpecMap_iff _).2 hfin, HasRingHomProperty.Spec_iff.2 het, ⟨?_⟩⟩
  exact hint.comap_surjective hj

end GlobalTheory.SiegelTor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndepDenom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.GaussDown

theorem descent {R₁ E : Type} [CommRing R₁] [CommRing E] [IsLocalRing E] (a : R₁ →+* E) (ha : a.Flat)
    (q : Ideal R₁) (hq : ∀ t ∈ q, a t ∈ maximalIdeal E) {m J : ℕ} (p : Fin m → R₁) (g : Fin J → Fin m → R₁)
    (e : Fin J → E) (h : ∀ i, a (p i) = ∑ j, e j * a (g j i)) :
    ∃ s, s ∉ q ∧ ∃ r : Fin J → R₁, ∀ i, s * p i = ∑ j, r j * g j i := by
  classical
  letI : Algebra R₁ E := a.toAlgebra
  haveI : Module.Flat R₁ E := ha
  let A : Matrix (Fin (J + 1)) (Fin m) R₁ := Fin.cons p g
  let xv : Fin (J + 1) → E := Fin.cons 1 (fun j => -e j)
  let f : (Fin m → R₁) →ₗ[R₁] (Fin (J + 1) → R₁) := A.mulVecLin
  let x : (Fin (J + 1) → R₁) →ₗ[R₁] E := Fintype.linearCombination R₁ xv
  have hxf : x ∘ₗ f = 0 := by
    ext k
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, f, x, Matrix.mulVecLin_apply,
      Fintype.linearCombination_apply, Matrix.mulVec, dotProduct]
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [Fin.sum_univ_succ, A, xv, Fin.cons_zero, Fin.cons_succ, smul_eq_mul, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra, map_mul, Pi.single_apply]
    rw [h i, Finset.sum_mul, Finset.sum_mul]
    simp only [_root_.mul_one, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun j _ => by ring
  obtain ⟨k, α, y, hxy, hαf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
  let ev : ∀ {n : ℕ}, Fin n → Fin n → R₁ := fun c j => if c = j then 1 else 0
  have h1 : y (α (ev 0)) = 1 := by
    have := LinearMap.congr_fun hxy (ev 0)
    simp only [LinearMap.comp_apply] at this
    rw [← this]
    simp [x, xv, ev, Fintype.linearCombination_apply, Fin.sum_univ_succ]
  have hy : ∀ c' : Fin k →₀ R₁, y c' = ∑ l ∈ c'.support, a (c' l) * y (Finsupp.single l 1) := by
    intro c'
    conv_lhs => rw [← Finsupp.sum_single c']
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← _root_.mul_one (c' l), ← smul_eq_mul, ← Finsupp.smul_single, map_smul, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra]
    simp only [smul_eq_mul, _root_.mul_one]
  obtain ⟨l, hl⟩ : ∃ l, α (ev 0) l ∉ q := by
    by_contra hall
    push_neg at hall
    have : (1 : E) ∈ maximalIdeal E := by
      rw [← h1, hy]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hq _ (hall l))
    exact (maximalIdeal.isMaximal E).ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine ⟨α (ev 0) l, hl, fun j => -(α (ev j.succ) l), fun i => ?_⟩
  have h2 := congrArg (fun z : Fin k →₀ R₁ => z l) (LinearMap.congr_fun hαf (ev i))
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply] at h2
  rw [LinearMap.pi_apply_eq_sum_univ α] at h2
  simp only [Fin.sum_univ_succ] at h2
  have hA : ∀ c, (A.mulVecLin (ev i)) c = A c i := by
    intro c
    simp [Matrix.mulVec, dotProduct, ev]
  simp only [f, hA, A, Fin.cons_zero, Fin.cons_succ] at h2
  have hs : ∑ j, -(α (ev j.succ) l) * g j i = -∑ j, g j i * α (ev j.succ) l := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul] at h2
  rw [hs]
  simp only [ev] at h2 ⊢
  linear_combination h2

end GlobalTheory.Desc.GaussDown

namespace GlobalTheory.Desc.GaussDown

theorem exists_indep_denom {R₁ F₁ : Type} [CommRing R₁] [IsDomain R₁] [Field F₁] (c₁ : R₁ →+* F₁) {n : ℕ}
    (y : Fin n → F₁) :
    ∃ (m : ℕ) (b : Fin m → F₁) (δ : R₁) (G : Fin n → Fin m → R₁),
      (∀ r : Fin m → R₁, ∑ i, c₁ (r i) * b i = 0 → r = 0) ∧ δ ≠ 0 ∧
        ∀ l, c₁ δ * y l = ∑ i, c₁ (G l i) * b i := by
  classical
  letI : Algebra R₁ F₁ := c₁.toAlgebra
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn R₁ y
  have hex : ∀ l, ∃ a : R₁, a ≠ 0 ∧ a • y l ∈ Submodule.span R₁ (y '' s) := by
    intro l
    by_cases hl : l ∈ s
    · exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span ⟨l, hl, rfl⟩⟩
    · exact hmax l hl
  choose a ha0 ha using hex
  let eqv : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let b : Fin (Fintype.card s) → F₁ := fun i => y (eqv i)
  have hb : LinearIndependent R₁ b := hs.comp eqv eqv.injective
  have hspan : Submodule.span R₁ (y '' s) = Submodule.span R₁ (Set.range b) := by
    congr 1
    ext z
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨eqv.symm ⟨l, hl⟩, by simp [b]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, (eqv i).2, rfl⟩
  have hδ : (∏ l, a l) ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => ha0 l
  have hmem : ∀ l, (∏ l, a l) • y l ∈ Submodule.span R₁ (Set.range b) := by
    intro l
    rw [← hspan, ← Finset.prod_erase_mul _ _ (Finset.mem_univ l), mul_smul]
    exact Submodule.smul_mem _ _ (ha l)
  choose G hG using fun l => (Submodule.mem_span_range_iff_exists_fun R₁).1 (hmem l)
  refine ⟨_, b, ∏ l, a l, G, ?_, hδ, ?_⟩
  · intro r hr
    have := Fintype.linearIndependent_iff.1 hb r
      (by simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hr)
    funext i
    exact this i
  · intro l
    have := hG l
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] at this
    exact this.symm

end GlobalTheory.Desc.GaussDown

namespace GlobalTheory.Desc.GaussDown

theorem gaussAt_descent : ∀ (R₀ R₁ E F F₁ FE : Type) [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁] [CommRing E] [IsDomain E] [IsLocalRing E] [Field F] [Field F₁] [Field FE] (ρ : R₀ →+* R₁) (a : R₁ →+* E) (c₀ : R₀ →+* F) (c₁ : R₁ →+* F₁) (cE : E →+* FE) (θ : F →+* F₁) (θE : F₁ →+* FE) (q : Ideal R₁) [q.IsPrime] (W : Set F) (W₁ : Set F₁) (WE : Set FE), a.Flat → Function.Injective c₁ → (∀ s, s ∉ q → IsUnit (a s)) → (∀ t, t ∈ q → a t ∈ maximalIdeal E) → θ.comp c₀ = c₁.comp ρ → θE.comp c₁ = cE.comp a → LinDisj c₀ c₁ θ → LinDisj c₁ cE θE → θE ⁻¹' WE = W₁ → GaussAt cE (maximalIdeal E) (θE.comp θ) W WE → GaussAt c₁ q θ W W₁ := by
  intro R₀ R₁ E F F₁ FE _ _ _ _ _ _ _ _ _ _ ρ a c₀ c₁ cE θ θE q _ W W₁ WE ha hc₁ hunit hmax _ hE _ hL1 hW hG
  have hcomp : ∀ r, cE (a r) = θE (c₁ r) := fun r => (RingHom.congr_fun hE r).symm
  have ha0 : ∀ d : R₁, d ≠ 0 → a d ≠ 0 := by
    intro d hd h
    apply hd
    apply hc₁
    apply θE.injective
    rw [← hcomp, h, map_zero, map_zero, map_zero]
  intro v ⟨d, hd, hdv⟩
  have hEv : ∃ d' : E, d' ≠ 0 ∧ cE d' * θE v ∈ spanBy cE (Set.range (θE.comp θ)) := by
    obtain ⟨n, r, u, hu, hsum⟩ := hdv
    refine ⟨a d, ha0 d hd, n, fun i => a (r i), fun i => θE (u i), fun i => ?_, ?_⟩
    · obtain ⟨w, hw⟩ := hu i
      exact ⟨w, by rw [RingHom.comp_apply, hw]⟩
    · have := congrArg θE hsum
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, hcomp] using this
  rw [← hW, Set.mem_preimage, hG (θE v) hEv]
  constructor
  · rintro ⟨t, ht, n, e, z, hz, hsum⟩
    choose w hwW hwz using hz
    obtain ⟨m, b, δ, G, hb, hδ, hGb⟩ := exists_indep_denom c₁ (Fin.cons v (fun j => θ (w j)) : Fin (n + 1) → F₁)
    have hv : c₁ δ * v = ∑ i, c₁ (G 0 i) * b i := by simpa using hGb 0
    have hw' : ∀ j, c₁ δ * θ (w j) = ∑ i, c₁ (G j.succ i) * b i := fun j => by simpa using hGb j.succ
    have htu : IsUnit t := by
      by_contra h
      exact ht ((mem_maximalIdeal _).2 h)
    have e1 : ∑ i, cE (a (G 0 i)) * θE (b i) = θE (c₁ δ) * θE v := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_mul, hv, map_sum]
      simp [hcomp]
    have e2 : ∀ j, ∑ i, cE (a (G j.succ i)) * θE (b i) = θE (c₁ δ) * z j := by
      intro j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hwz j, RingHom.comp_apply, ← map_mul, hw' j, map_sum]
      simp [hcomp]
    have hz0 := hL1 m b hb (fun i => t * a (G 0 i) - ∑ j, e j * a (G j.succ i)) (by
      calc ∑ i, cE (t * a (G 0 i) - ∑ j, e j * a (G j.succ i)) * θE (b i)
          = cE t * (∑ i, cE (a (G 0 i)) * θE (b i)) - ∑ j, cE (e j) * (∑ i, cE (a (G j.succ i)) * θE (b i)) := by
            set_option synthInstance.maxHeartbeats 100000 in
              simp only [map_sub, map_mul, map_sum, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
              (f := fun i j => cE (e j) * cE (a (G j.succ i)) * θE (b i))]
            congr 1
            · exact Finset.sum_congr rfl fun i _ => by ring
            · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
        _ = θE (c₁ δ) * (cE t * θE v - ∑ j, cE (e j) * z j) := by
            rw [e1, mul_sub, Finset.mul_sum]
            simp only [e2]
            congr 1
            · ring
            · exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hsum, sub_self, mul_zero])
    have hrel : ∀ i, a (G 0 i) = ∑ j, (↑htu.unit⁻¹ * e j) * a (G j.succ i) := by
      intro i
      have h1 := sub_eq_zero.1 (congrFun hz0 i)
      simp only [_root_.mul_assoc, ← Finset.mul_sum]
      rw [← h1, ← _root_.mul_assoc, IsUnit.val_inv_mul, _root_.one_mul]
    obtain ⟨s, hs, r, hr⟩ := descent a ha q hmax (G 0) (fun j => G j.succ) _ hrel
    refine ⟨s, hs, n, r, fun j => θ (w j), fun j => ⟨w j, hwW j, rfl⟩, ?_⟩
    have hδ' : c₁ δ ≠ 0 := (map_ne_zero_iff _ hc₁).2 hδ
    apply mul_left_cancel₀ hδ'
    calc c₁ δ * (c₁ s * v) = c₁ s * (c₁ δ * v) := by ring
      _ = ∑ i, c₁ (s * G 0 i) * b i := by
          rw [hv, Finset.mul_sum]
          simp only [map_mul, _root_.mul_assoc]
      _ = ∑ i, ∑ j, c₁ (r j) * (c₁ (G j.succ i) * b i) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [hr, map_sum, map_mul, Finset.sum_mul, _root_.mul_assoc]
      _ = ∑ j, c₁ (r j) * (c₁ δ * θ (w j)) := by
          rw [Finset.sum_comm]
          simp only [hw', Finset.mul_sum]
      _ = c₁ δ * ∑ j, c₁ (r j) * θ (w j) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  · rintro ⟨s, hs, n, r, z, hz, hsum⟩
    refine ⟨a s, fun hm => ((mem_maximalIdeal _).1 hm) (hunit s hs), n, fun i => a (r i), fun i => θE (z i),
      fun i => ?_, ?_⟩
    · obtain ⟨w, hw, hwz⟩ := hz i
      exact ⟨w, hw, by rw [RingHom.comp_apply, hwz]⟩
    · have := congrArg θE hsum
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, hcomp] using this

end GlobalTheory.Desc.GaussDown
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedMultiplicationPullbackFunctionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalised_multiplicationPullback_function : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ (m : ℕ) (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ), FnT u 1 th f → ∃ (α : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![(snd (baseOver (Sp ℂ)) x.P.A).left, (snd (baseOver (Sp ℂ)) x.P.A ^ m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (s₁ : LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp ℂ)))), α.IsGen ∧ LB.Gen.Corr x.P.L _ _ _ _ (LB.pullGen x.P.L _ _ α (ptSecT x.P.A 1).left) (rigT x.P.A x.P.L x.rig (baseOver (Sp ℂ)) (((m ^ 2 : ℕ) : ℤ) - 1)) ∧ IsTwistPull x.P.A x.P.L (mulT x.P.A (baseOver (Sp ℂ)) m) (snd (baseOver (Sp ℂ)) x.P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧ FnT u (m ^ 2) s₁ fun z => f ((m : ℂ) • z) := by
  first | exact @GlobalTheory.MBLow.Cl.exists_normalised_mulPull_fnT | exact GlobalTheory.MBLow.Cl.exists_normalised_mulPull_fnT | (intros; apply GlobalTheory.MBLow.Cl.exists_normalised_mulPull_fnT <;> assumption)
end

