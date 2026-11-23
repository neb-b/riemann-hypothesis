module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0035
public import Development.EtaleCohomology.EtaleSheaves.Bundle0040
public import Development.EtaleCohomology.EtaleSheaves.Bundle0036
public import Development.EtaleCohomology.EtaleSheaves.Bundle0041
public import Development.EtaleCohomology.EtaleSheaves.Bundle0039
public import Development.EtaleCohomology.EtaleSheaves.Bundle0015
public import Development.EtaleCohomology.EtaleSheaves.PartDiagCut

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfD
section
namespace LateralTheory.E.E4

open MvPolynomial

noncomputable def killFirst (k : Type) [Field k] (s j : ℕ) :
    MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin s) k :=
  aeval (fun i => if i.val < j then 0 else X i)

lemma killFirst_X (k : Type) [Field k] (s j : ℕ) (i : Fin s) :
    killFirst k s j (X i) = if i.val < j then 0 else X i := by
  simp [killFirst]

lemma X_mem_ker_killFirst (k : Type) [Field k] (s j : ℕ) (i : Fin s) (hi : i.val < j) :
    (X i : MvPolynomial (Fin s) k) ∈ RingHom.ker (killFirst k s j) := by
  rw [RingHom.mem_ker]; erw [killFirst_X]; simp [hi]

lemma X_not_mem_ker_killFirst (k : Type) [Field k] (s j : ℕ) (i : Fin s) (hi : ¬ i.val < j) :
    (X i : MvPolynomial (Fin s) k) ∉ RingHom.ker (killFirst k s j) := by
  rw [RingHom.mem_ker]; erw [killFirst_X]; simp [hi, X_ne_zero]

theorem LeafNoetherDim_of : LeafNoetherDim := by
  intro k B _ _ _ _ _ _ hB s g hg hf
  let : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  have hint : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := ⟨fun x => hf.to_isIntegral x⟩
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin s) k) B) := hg
  by_contra hs
  rcases Nat.lt_or_gt_of_ne hs with h0 | h2
  ·
    obtain rfl : s = 0 := by omega
    apply hB
    rw [← Algebra.IsIntegral.isField_iff_isField hinj]
    exact MulEquiv.isField (Field.toIsField k) (isEmptyAlgEquiv k (Fin 0)).toMulEquiv
  ·
    set A := MvPolynomial (Fin s) k
    let P1 : Ideal A := RingHom.ker (killFirst k s 1)
    let P2 : Ideal A := RingHom.ker (killFirst k s 2)
    have hP1 : P1.IsPrime := RingHom.ker_isPrime _
    have hP2 : P2.IsPrime := RingHom.ker_isPrime _
    let i0 : Fin s := ⟨0, by omega⟩
    let i1 : Fin s := ⟨1, by omega⟩
    have h12 : P1 ≤ P2 := by
      intro p hp
      simp only [P1, P2, RingHom.mem_ker] at hp ⊢
      have : killFirst k s 2 = (killFirst k s 2).comp (killFirst k s 1) := by
        apply MvPolynomial.algHom_ext; intro i
        simp only [AlgHom.comp_apply, killFirst_X]
        by_cases h : i.val < 1
        · simp [h, show i.val < 2 by omega]
        · simp [h, killFirst_X]
      rw [this, AlgHom.comp_apply]; erw [hp]; simp
    have x0P1 : (X i0 : A) ∈ P1 := X_mem_ker_killFirst k s 1 i0 (by simp [i0])
    have x1P2 : (X i1 : A) ∈ P2 := X_mem_ker_killFirst k s 2 i1 (by simp [i1])
    have x1P1 : (X i1 : A) ∉ P1 := X_not_mem_ker_killFirst k s 1 i1 (by simp [i1])
    have : (⊥ : Ideal B).IsPrime := Ideal.isPrime_bot
    have hc0 : Ideal.under A (⊥ : Ideal B) = ⊥ := by
      exact Ideal.comap_bot_of_injective _ hinj
    obtain ⟨Q1, -, hQ1, hcQ1⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime P1 (⊥ : Ideal B) (by rw [hc0]; exact bot_le)
    obtain ⟨Q2, hQ12, hQ2, hcQ2⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime P2 Q1 (by rw [hcQ1]; exact h12)
    have hQ1ne : Q1 ≠ ⊥ := by
      rintro rfl
      rw [hc0] at hcQ1
      apply X_ne_zero (R := k) i0
      have : (X i0 : A) ∈ (⊥ : Ideal A) := hcQ1 ▸ x0P1
      simp at this
    have hQ1max : Q1.IsMaximal := hQ1.isMaximal hQ1ne
    have hne : Q1 ≠ Q2 := by
      rintro rfl
      rw [hcQ1] at hcQ2
      exact x1P1 (hcQ2 ▸ x1P2)
    have := hQ1max.eq_of_le hQ2.ne_top hQ12
    exact hne this

end LateralTheory.E.E4
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfF
section
namespace LateralTheory.E.E4

open Polynomial

theorem mem_bot_of_mem_adjoin_inv {k L : Type} [Field k] [Field L] [Algebra k L] (t : L) (ht : Transcendental k t)
    (c : L) (h1 : c ∈ Algebra.adjoin k {t}) (h2 : c ∈ Algebra.adjoin k {t⁻¹}) : c ∈ (⊥ : Subalgebra k L) := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h1 h2
  obtain ⟨p, rfl⟩ := h1
  obtain ⟨q, hq⟩ := h2
  have ht0 : t ≠ 0 := by
    rintro rfl; exact ht (isAlgebraic_zero)
  set N := q.natDegree
  have key : aeval t (X ^ N * p) = aeval t (reflect N q) := by
    let _ : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht0)
    have h := eval₂_reflect_mul_pow (algebraMap k L) t⁻¹ N q le_rfl
    rw [invOf_eq_inv, inv_inv] at h
    have hq' : aeval t⁻¹ q = aeval t p := hq
    rw [aeval_def, aeval_def] at hq'
    rw [map_mul, map_pow, aeval_X, aeval_def, aeval_def, ← hq', ← h, mul_comm, mul_assoc, ← mul_pow,
      inv_mul_cancel₀ ht0, one_pow, mul_one]
  have hinj : Function.Injective (aeval t : k[X] →ₐ[k] L) := transcendental_iff_injective.mp ht
  have heq := hinj key
  by_cases hp : p = 0
  · simp [hp]
  have hdeg : (X ^ N * p).natDegree = N + p.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hp, natDegree_X_pow]
  have hle : (reflect N q).natDegree ≤ N := natDegree_reflect_le.trans (by simp [N])
  have hp0 : p.natDegree = 0 := by rw [heq] at hdeg; omega
  rw [eq_C_of_natDegree_eq_zero hp0]
  simp

def LeafMinpolyCoeff : Prop := ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (s : L), Transcendental k s →
  ∀ (F : IntermediateField k L), F = IntermediateField.adjoin k {s} → ∀ x : L, IsIntegral (Algebra.adjoin k {s}) x →
  ∀ i : ℕ, ((minpoly F x).coeff i : L) ∈ Algebra.adjoin k {s}

theorem isIntegral_adjoin_of {k L : Type} [Field k] [Field L] [Algebra k L] (s : L) (x : L)
    (hx : IsIntegral (Algebra.adjoin k {s}) x) : IsIntegral (IntermediateField.adjoin k {s}) x := by
  obtain ⟨p, hm, hp⟩ := hx
  let ι : Algebra.adjoin k {s} →+* IntermediateField.adjoin k {s} :=
    Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin k {s}) |>.toRingHom
  refine ⟨p.map ι, hm.map _, ?_⟩
  rw [eval₂_map]
  exact hp

theorem LeafIntBoth_of' (hM : LeafMinpolyCoeff) : ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (t : L),
    Transcendental k t → ∀ x : L,
    IsIntegral (Algebra.adjoin k {t}) x → IsIntegral (Algebra.adjoin k {t⁻¹}) x → IsIntegral k x := by
  intro k L _ _ _ t ht x h1 h2
  have ht' : Transcendental k t⁻¹ := fun h => ht (by simpa using h.inv)
  set F := IntermediateField.adjoin k {t}
  have hEq : F = IntermediateField.adjoin k {t⁻¹} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      simpa using inv_mem (IntermediateField.mem_adjoin_simple_self k t⁻¹)
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self k t)
  have hxF : IsIntegral F x := isIntegral_adjoin_of t x h1
  have hc : ∀ i, ((minpoly F x).coeff i : L) ∈ (⊥ : Subalgebra k L) := fun i =>
    mem_bot_of_mem_adjoin_inv t ht _ (hM k L t ht F rfl x h1 i) (hM k L t⁻¹ ht' F hEq x h2 i)
  have hl : minpoly F x ∈ lifts (algebraMap k F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp (hc n)
    exact ⟨a, Subtype.ext ha⟩
  obtain ⟨P, hP, -, hPm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hxF)
  refine ⟨P, hPm, ?_⟩
  have := minpoly.aeval F x
  rw [← hP, aeval_map_algebraMap] at this
  exact this

theorem LeafIntBoth_of (hM : LeafMinpolyCoeff) : LeafIntBoth := LeafIntBoth_of' hM

theorem LeafOrdAtInfinity_of_cut (hV : LeafOrdInfHom) (hM : LeafMinpolyCoeff) : LeafOrdAtInfinity :=
  LeafOrdAtInfinity_of hV (LeafIntBoth_of hM)

end LateralTheory.E.E4
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocACPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.BuildCut LateralTheory.E.CompCut

namespace LateralTheory.E.LocACPf

variable {W : Type} [CommRing W]

lemma idem_split {e : W} (he : IsIdempotentElem e) : e * (1 - e) = 0 := by
  rw [mul_sub, mul_one, he.eq, sub_self]

lemma map_zero_of_mem (hW : ProdACF W) (p : Ideal W) [p.IsPrime] {a : W} (ha : a ∈ p) :
    algebraMap W (Localization.AtPrime p) a = 0 := by
  obtain ⟨e, u, he, hu, rfl⟩ := hW.2 a
  have heq : e ∈ p := by
    rcases (inferInstance : p.IsPrime).mem_or_mem ha with h | h
    · exact h
    · exact absurd (p.eq_top_of_isUnit_mem h hu) (inferInstance : p.IsPrime).ne_top
  have h1 : (1 - e) ∈ p.primeCompl := by
    intro h
    have : (1 : W) ∈ p := by simpa using p.add_mem heq h
    exact (inferInstance : p.IsPrime).ne_top ((Ideal.eq_top_iff_one _).2 this)
  rw [IsLocalization.map_eq_zero_iff p.primeCompl]
  refine ⟨⟨1 - e, h1⟩, ?_⟩
  show (1 - e) * (e * u) = 0
  rw [← mul_assoc, mul_comm (1 - e), idem_split he, zero_mul]

lemma map_idem_one (hW : ProdACF W) (p : Ideal W) [p.IsPrime] {e : W} (he : IsIdempotentElem e) (hne : e ∉ p) :
    algebraMap W (Localization.AtPrime p) e = 1 := by
  have h1 : (1 - e) ∈ p := by
    rcases (inferInstance : p.IsPrime).mem_or_mem (show e * (1 - e) ∈ p by rw [idem_split he]; exact p.zero_mem) with h | h
    · exact absurd h hne
    · exact h
  have := map_zero_of_mem hW p h1
  rw [map_sub, map_one, sub_eq_zero] at this
  exact this.symm

lemma surj (hW : ProdACF W) (p : Ideal W) [p.IsPrime] :
    Function.Surjective (algebraMap W (Localization.AtPrime p)) := by
  intro x
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
  obtain ⟨e, u, he, hu, hs⟩ := hW.2 (s : W)
  have hne : e ∉ p := fun h => s.2 (hs ▸ p.mul_mem_right u h)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  refine ⟨a * e * v, ?_⟩
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, hs]
  have : a * e * v * (e * u) = a * e * e * (v * u) := by ring
  rw [this, hv, mul_one, mul_assoc, he.eq, map_mul, map_idem_one hW p he hne, mul_one]

theorem LocAC_of : LocAC := by
  intro W _ hW q
  have := q.isPrime
  set p := q.asIdeal
  constructor
  · rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_eq_bot_iff_le_ker]
    intro a ha
    exact map_zero_of_mem hW p ha
  · intro P hP hdeg
    have hl : P ∈ Polynomial.lifts (algebraMap W (Localization.AtPrime p)) := by
      obtain ⟨Q, hQ⟩ := Polynomial.map_surjective _ (surj hW p) P
      exact Polynomial.mem_lifts _ |>.2 ⟨Q, hQ⟩
    obtain ⟨Q, hQ, hdQ, hmQ⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hP
    obtain ⟨r, hr⟩ := hW.1 Q hmQ (hdQ ▸ hdeg)
    refine ⟨algebraMap W _ r, ?_⟩
    rw [← hQ, Polynomial.eval_map, Polynomial.eval₂_at_apply, hr, map_zero]

end LateralTheory.E.LocACPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.NonunitCase
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.AlgGlue₂

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

theorem mS_mul (S : Subalgebra A K) {x b : K} (hx : x ∈ mS S) (hb : b ∈ S) : x * b ∈ mS S := by
  unfold mS at hx ⊢
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha s hs
    rw [smul_mul_assoc]
    exact Submodule.smul_mem_smul ha (S.mul_mem hs hb)
  · intro x y hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy

theorem unit_case (S : Subalgebra A K) {u h e : K} (hu : u ∈ S) (hh : h ∈ S) (huh : u * h = 1)
    (he : e ∈ S) (hue : u - e ∈ mS S) (hee : e * e - e ∈ mS S) : e - 1 ∈ mS S := by
  have key : e - 1 = (e * e - e) * h + (u - e) * ((e - 1) * h) := by
    linear_combination (1 - e) * huh
  rw [key]
  exact Submodule.add_mem _ (mS_mul S hee hh)
    (mS_mul S hue (S.mul_mem (S.sub_mem he (S.one_mem)) hh))

theorem nonunit_case (S : Subalgebra A K) {u h e : K} (hu : u ∈ S) (hh : h ∈ S) (huh : (1 - u) * h = 1)
    (he : e ∈ S) (hue : u - e ∈ mS S) (hee : e * e - e ∈ mS S) : e ∈ mS S := by
  have h1 := unit_case S (u := 1 - u) (e := 1 - e) (S.sub_mem S.one_mem hu) hh huh
    (S.sub_mem S.one_mem he)
    (by
      have : (1 - u) - (1 - e) = (u - e) * (-1) := by ring
      rw [this]; exact mS_mul S hue (S.neg_mem S.one_mem))
    (by
      have : (1 - e) * (1 - e) - (1 - e) = e * e - e := by ring
      rw [this]; exact hee)
  have : e = (1 - e - 1) * (-1) := by ring
  rw [this]; exact mS_mul S h1 (S.neg_mem S.one_mem)

theorem AlgGlue_of (hL : IdemLift) (hF : LateralTheory.E.LZProperCut.LZHensFinite) : AlgGlue := by
  intro A _ _ _ K _ _ B C t hc hint e f hef
  obtain ⟨heB, hfC, hee, hff, hd⟩ := hef
  obtain ⟨g, hgB, hgC, hge, hgf⟩ := hL A K B C t hc e f ⟨heB, hfC, hee, hff, hd⟩
  set R : Subalgebra A K := Algebra.adjoin A {g} with hR
  have hRB : R ≤ B := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hgB)
  have hRC : R ≤ C := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hgC)
  have hgi : IsIntegral A g := hint g hgB hgC
  have : Module.Finite A R := Algebra.finite_adjoin_simple_of_isIntegral hgi
  have : IsDomain R := inferInstance
  have : ConnectedSpace ↑(Spec (CommRingCat.of R)) := by
    change ConnectedSpace (PrimeSpectrum R)
    infer_instance
  have : IsLocalRing R := hF A R this
  have hgR : g ∈ R := Algebra.self_mem_adjoin_singleton A g
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨g, hgR⟩ : R) with hu | hu
  · obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hv' : g * (v : K) = 1 := by
      have := congrArg Subtype.val hv; simpa using this
    right
    exact ⟨unit_case B hgB (hRB v.2) hv' heB hge hee, unit_case C hgC (hRC v.2) hv' hfC hgf hff⟩
  · obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hv' : (1 - g) * (v : K) = 1 := by
      have := congrArg Subtype.val hv; simpa using this
    left
    exact ⟨nonunit_case B hgB (hRB v.2) hv' heB hge hee, nonunit_case C hgC (hRC v.2) hv' hfC hgf hff⟩

end LateralTheory.E.AlgGlue₂
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.NormACPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CompCut

namespace LateralTheory.E.NormACPf

theorem aic_integralClosure (A K : Type) [CommRing A] [CommRing K] [Algebra A K] (hK : AIC K) :
    AIC (integralClosure A K) := by
  intro p hp hd
  obtain ⟨a, ha⟩ := hK (p.map (integralClosure A K).val.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective Subtype.val_injective])
  have hint : IsIntegral (integralClosure A K) a := ⟨p, hp, by
    rw [Polynomial.eval_map] at ha; exact ha⟩
  have haA : a ∈ integralClosure A K := isIntegral_trans (R := A) a hint
  refine ⟨⟨a, haA⟩, Subtype.val_injective ?_⟩
  have h4 : (integralClosure A K).val.toRingHom (Polynomial.eval (⟨a, haA⟩ : integralClosure A K) p) = 0 := by
    rw [← Polynomial.eval₂_at_apply]; rw [Polynomial.eval_map] at ha; exact ha
  simpa using h4

theorem aic_of_subsingleton (R : Type) [CommRing R] [Subsingleton R] : AIC R :=
  fun _ _ _ => ⟨0, Subsingleton.elim _ _⟩

theorem aic_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : AIC R) : AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have h4 : e.symm.toRingHom (Polynomial.eval (e a) p) = 0 := by
    rw [← Polynomial.eval₂_at_apply]; rw [Polynomial.eval_map] at ha; simpa using ha
  simpa using h4

theorem aic_spec_field (K : Type) [Field K] (hA : AIC K) (W : (Spec (CommRingCat.of K)).Opens) :
    AIC Γ(Spec (CommRingCat.of K), W) := by
  by_cases h : (default : Spec (CommRingCat.of K)) ∈ W
  · have : W = ⊤ := by
      ext x; simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      rwa [Subsingleton.elim x default]
    subst this
    exact aic_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm hA
  · have : W = ⊥ := by
      ext x; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      rwa [Subsingleton.elim x default]
    subst this
    exact aic_of_subsingleton _

def Loc : Prop := ∀ (Z : Scheme.{0}), IsIntegral Z → (∀ z : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ z ∈ U ∧ AIC Γ(Z, U)) →
  ∀ U : Z.Opens, IsAffineOpen U → (U : Set Z).Nonempty → AIC Γ(Z, U)

theorem NormAC_of (hL : Loc) : NormAC := by
  intro P _ _ K _ hF hA v
  let := hF.toField
  have hI : IsIntegral v.normalization := inferInstance
  refine ⟨hI, hL _ hI ?_⟩
  intro z
  obtain ⟨V, hV, hz, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp P.isBasis_affineOpens
    (show v.fromNormalization z ∈ (⊤ : P.Opens) from trivial)
  refine ⟨v.fromNormalization ⁻¹ᵁ V, hV.preimage _, hz, ?_⟩
  letI := (v.app V).hom.toAlgebra
  exact aic_of_ringEquiv (v.normalizationObjIso hV).commRingCatIsoToRingEquiv.symm
    (aic_integralClosure _ _ (aic_spec_field K hA _))

end LateralTheory.E.NormACPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PairExtensionOfTensorUniversal
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafPairExtPf2
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafPairExtPf LateralTheory.E.LeafTwPairExistsPf

def pre {R : Type} [CommRing R] {I' I J K : Cx R} (μ : Pair I J K) (f : I' ⟶ I) : Pair I' J K where
  mul U s t w h := (μ.mul U s t w h).comp ((f.f s).hom.app (op U)).hom
  nat g s t w h a b := by
    change Sec.res g (μ.mul _ s t w h (Sec.map (f.f s) a) b) = μ.mul _ s t w h (Sec.map (f.f s) (Sec.res g a)) (Sec.res g b)
    rw [μ.nat, res_map]
  leibniz U s t w h a b := by
    change Sec.map (K.d w (w + 1)) (μ.mul U s t w h (Sec.map (f.f s) a) b) =
      μ.mul U (s + 1) t (w + 1) _ (Sec.map (f.f (s + 1)) (Sec.map (I'.d s (s + 1)) a)) b +
      s.negOnePow • μ.mul U s (t + 1) (w + 1) _ (Sec.map (f.f s) a) (Sec.map (J.d t (t + 1)) b)
    rw [μ.leibniz, map_map, map_map, f.comm]

def LeafTensUP : Prop := ∀ (R : Type) [CommRing R] {I J T K : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ μ : Pair I J K,
  ∃ u : T ⟶ K, ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map (u.f w) (τ.mul U s t w h a b) = μ.mul U s t w h a b

def LeafExtTens : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {S T : Cx (ZMod q)} (σ : Pair (sgl (tw q 0)) (res _ (tw q i)) S)
  (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map ((resAug (tw q 0)).f s) a) b) →
  ∀ u : S ⟶ res _ (tw q i), ∃ g : T ⟶ res _ (tw q i), ι ≫ g = u

theorem LeafExtAlongAug_of (hup : LeafTensUP) (hext : LeafExtTens) : LeafExtAlongAug := by
  intro q _ i lam
  let σ := LateralTheory.E.LeafTwTensExPf.tau (sgl (tw q 0)) (res _ (tw q i))
  let τ := LateralTheory.E.LeafTwTensExPf.tau (res _ (tw q 0)) (res _ (tw q i))
  have hσ : σ.IsTensor := LateralTheory.E.LeafTwTensExPf.tau_isTensor _ _
  have hτ : τ.IsTensor := LateralTheory.E.LeafTwTensExPf.tau_isTensor _ _
  obtain ⟨u, hu⟩ := hup _ σ hσ lam
  obtain ⟨ι, hι⟩ := hup _ σ hσ (pre τ (resAug (tw q 0)))
  obtain ⟨g, hg⟩ := hext q i σ τ hσ hτ ι hι u
  refine ⟨post τ g, fun U t x b => ?_⟩
  have e : Sec.map (ι.f t) (σ.mul U 0 t t (zero_add t) x b) =
      τ.mul U 0 t t (zero_add t) (Sec.map ((resAug (tw q 0)).f 0) x) b := hι U 0 t t (zero_add t) x b
  rw [post_mul, ← e, map_map, ← HomologicalComplex.comp_f, hg, hu]

end LateralTheory.E.LeafPairExtPf2
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PartBPf
section
noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.PartBPf

theorem comp_mem {B : Type} [CommRing B] (I : Ideal B) (P : PartDiagCut.Part (B ⧸ I)) (x : PiLocalization₂ I P)
    (hx : x ∈ I.map (βP I P)) (e : P.1) :
    x e ∈ I.map (algebraMap B (Localization (S I e.1))) := by
  have h1 : (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) x ∈
      (I.map (βP I P)).map (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) :=
    Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_map] at h1
  have h2 : (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e).comp (βP I P) =
      algebraMap B (Localization (S I e.1)) := by
    ext b; rfl
  rw [h2] at h1
  exact h1

theorem comp_unit {B : Type} [CommRing B] (I : Ideal B) (e : B ⧸ I) (y : Localization (S I e))
    (hy : y ∈ I.map (algebraMap B (Localization (S I e)))) : IsUnit (1 + y) := by
  obtain ⟨⟨⟨i, hi⟩, ⟨s, hs⟩⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff (S I e) _).1 hy
  simp only at h
  have hsi : s + i ∈ S I e := by
    obtain ⟨t, ht⟩ := hs
    refine ⟨t, ?_⟩
    have : Ideal.Quotient.mk I i = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hi
    rw [map_add (f := _), this, add_zero]; exact ht
  have hu : IsUnit ((1 + y) * algebraMap B _ s) := by
    rw [add_mul, one_mul, h, ← map_add (f := _)]
    exact IsLocalization.map_units (Localization (S I e)) ⟨s + i, hsi⟩
  exact isUnit_of_mul_isUnit_left hu

theorem PartB_of : LateralTheory.E.PartDiagCut.PartB := by
  intro B _ I P x hx
  rw [Pi.isUnit_iff]
  intro e
  exact comp_unit I e.1 (x e) (comp_mem I P x hx e)

end LateralTheory.E.PartBPf
end
end

