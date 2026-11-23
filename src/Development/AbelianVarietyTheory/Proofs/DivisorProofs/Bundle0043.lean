module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootSubMemOfEvalMem
section
open IsLocalRing Polynomial

namespace GlobalTheory.AbsIntClosedLocal

theorem exists_root_sub_mem_of_eval_mem (T : Type) [CommRing T] [IsLocalRing T] [IsDomain T]
    (hroot : ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) :
    ∀ (n : ℕ) (f : T[X]), f.Monic → f.natDegree = n → ∀ a₀ : T, f.eval a₀ ∈ maximalIdeal T →
      ∃ a : T, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal T := by
  intro n
  induction n with
  | zero =>
    intro f hf hdeg a₀ hmem
    have : f = 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
      have := hf.coeff_natDegree
      rw [hdeg] at this
      rw [this, map_one]
    rw [this, eval_one] at hmem
    exact absurd ((Ideal.eq_top_iff_one _).2 hmem) (maximalIdeal.isMaximal T).ne_top
  | succ n ih =>
    intro f hf hdeg a₀ hmem
    obtain ⟨r, hr⟩ := hroot f hf (by omega)
    have hrr : f.IsRoot r := hr
    have hdiv := (mul_divByMonic_eq_iff_isRoot (p := f) (a := r)).2 hrr
    set g := f /ₘ (X - C r) with hg
    have hgm : g.Monic := (monic_X_sub_C r).of_mul_monic_left (by rw [hdiv]; exact hf)
    have hgdeg : g.natDegree = n := by
      have := natDegree_divByMonic f (monic_X_sub_C r)
      rw [natDegree_X_sub_C] at this
      rw [hg, this, hdeg]; omega
    have hev : f.eval a₀ = (a₀ - r) * g.eval a₀ := by
      conv_lhs => rw [← hdiv]
      simp [eval_mul]
    rw [hev] at hmem
    rcases (maximalIdeal.isMaximal T).isPrime.mem_or_mem hmem with h | h
    · refine ⟨r, hrr, ?_⟩
      have := (maximalIdeal T).neg_mem h
      simpa using this
    · obtain ⟨a, ha, ha'⟩ := ih g hgm hgdeg a₀ h
      refine ⟨a, ?_, ha'⟩
      rw [← hdiv]
      simp [IsRoot, eval_mul, ha.eq_zero]

theorem henselian_isAlgClosed_pow_surj :
    ∀ (T : Type) [CommRing T] [IsLocalRing T], (IsDomain T ∧ ∀ f : Polynomial T, f.Monic →
      0 < f.natDegree → ∃ x : T, f.eval x = 0) →
      HenselianLocalRing T ∧ IsAlgClosed (ResidueField T) ∧
        ∀ (n : ℕ) (u : Tˣ), 0 < n → ∃ v : Tˣ, v ^ n = u := by
  intro T _ _ ⟨hdom, hroot⟩
  refine ⟨⟨fun f hf a₀ h₁ _ => exists_root_sub_mem_of_eval_mem T hroot _ f hf rfl a₀ h₁⟩, ?_, ?_⟩
  · refine IsAlgClosed.of_exists_root _ (fun p hpm hpirr => ?_)
    have hl : p ∈ lifts (residue T) := (mem_lifts p).2 (map_surjective _ residue_surjective p)
    obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hpm
    obtain ⟨x, hx⟩ := hroot q hqm (by rw [hqd]; exact hpirr.natDegree_pos)
    refine ⟨residue T x, ?_⟩
    rw [← hq, eval_map, eval₂_hom, hx, map_zero]
  · intro n u hn
    obtain ⟨x, hx⟩ := hroot (X ^ n - C (u : T)) (monic_X_pow_sub_C _ hn.ne')
      (by rw [natDegree_X_pow_sub_C _]; exact hn)
    have hxn : x ^ n = (u : T) := by
      simp only [eval_sub, eval_pow, eval_X, eval_C] at hx
      exact sub_eq_zero.1 hx
    have hxu : IsUnit x := (isUnit_pow_iff hn.ne').1 (hxn ▸ u.isUnit)
    refine ⟨hxu.unit, Units.ext ?_⟩
    simp [hxn]

end GlobalTheory.AbsIntClosedLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRowPermLeadingMinorsNotMem
section
namespace GlobalTheory

theorem exists_injective_rows_leadingMinors_not_mem (R : Type) [CommRing R] (p : Ideal R) :
    ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) R), T.det ∉ p →
    ∃ f : Fin n → Fin n, Function.Injective f ∧ ∀ (k : ℕ) (hk : k ≤ n),
      (Matrix.of fun a b : Fin k => T (f (Fin.castLE hk a)) (Fin.castLE hk b)).det ∉ p := by
  intro n
  induction n with
  | zero =>
    intro T hT
    refine ⟨id, Function.injective_id, fun k hk => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    have h1 : T.det = 1 := Matrix.det_isEmpty
    rw [Matrix.det_isEmpty]
    rwa [h1] at hT
  | succ n ih =>
    intro T hT
    have hsum := T.det_succ_column (Fin.last n)
    obtain ⟨i, hi⟩ : ∃ i : Fin (n+1), (-1) ^ ((i : ℕ) + (Fin.last n : ℕ)) * T i (Fin.last n) *
        (T.submatrix i.succAbove (Fin.last n).succAbove).det ∉ p := by
      by_contra h
      push_neg at h
      exact hT (hsum ▸ p.sum_mem fun i _ => h i)
    have hM : (T.submatrix i.succAbove Fin.castSucc).det ∉ p := by
      intro hm
      apply hi
      rw [Fin.succAbove_last]
      exact p.mul_mem_left _ hm
    obtain ⟨g, hg, hmin⟩ := ih _ hM
    set f : Fin (n+1) → Fin (n+1) := Fin.lastCases i (fun j => i.succAbove (g j))
    have hf : Function.Injective f := by
      intro a b hab
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => rfl
        | cast b =>
          simp only [f, Fin.lastCases_last, Fin.lastCases_castSucc] at hab
          exact absurd hab.symm (Fin.succAbove_ne i _)
      | cast a =>
        induction b using Fin.lastCases with
        | last =>
          simp only [f, Fin.lastCases_last, Fin.lastCases_castSucc] at hab
          exact absurd hab (Fin.succAbove_ne i _)
        | cast b =>
          simp only [f, Fin.lastCases_castSucc] at hab
          rw [hg (Fin.succAbove_right_injective hab)]
    refine ⟨f, hf, ?_⟩
    intro k hk
    rcases Nat.lt_or_ge k (n+1) with hlt | hge
    · have hk' : k ≤ n := Nat.lt_succ_iff.mp hlt
      have hmat : (Matrix.of fun a b : Fin k => T (f (Fin.castLE hk a)) (Fin.castLE hk b)) =
          Matrix.of fun a b : Fin k => (T.submatrix i.succAbove Fin.castSucc)
            (g (Fin.castLE hk' a)) (Fin.castLE hk' b) := by
        ext a b
        have e1 : (Fin.castLE hk a : Fin (n+1)) = Fin.castSucc (Fin.castLE hk' a) := Fin.ext rfl
        have e2 : (Fin.castLE hk b : Fin (n+1)) = Fin.castSucc (Fin.castLE hk' b) := Fin.ext rfl
        rw [Matrix.of_apply, Matrix.of_apply, e1, e2]
        simp only [f, Fin.lastCases_castSucc, Matrix.submatrix_apply]
      rw [hmat]
      exact hmin k hk'
    · obtain rfl : k = n + 1 := le_antisymm hk hge
      let σ : Equiv.Perm (Fin (n+1)) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
      have hmat : (Matrix.of fun a b : Fin (n+1) => T (f (Fin.castLE hk a)) (Fin.castLE hk b)) =
          T.submatrix σ id := by
        ext a b
        have e1 : Fin.castLE hk a = a := Fin.ext rfl
        have e2 : Fin.castLE hk b = b := Fin.ext rfl
        simp [σ, e1, e2]
      rw [hmat, Matrix.det_permute]
      intro hm
      apply hT
      have hs : T.det = ((Equiv.Perm.sign σ : ℤ) : R) * (((Equiv.Perm.sign σ : ℤ) : R) * T.det) := by
        rw [← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
        simp
      rw [hs]
      exact p.mul_mem_left _ hm

theorem exists_rowPerm_leadingMinors_not_mem : ∀ (R : Type) [CommRing R] (n : ℕ)
    (T : Matrix (Fin n) (Fin n) R) (p : Ideal R), p.IsPrime → T.det ∉ p →
    ∃ w : Equiv.Perm (Fin n), ∀ (k : ℕ) (hk : k ≤ n),
      ((T.submatrix w id).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ∉ p := by
  intro R _ n T p _ hT
  obtain ⟨f, hf, h⟩ := exists_injective_rows_leadingMinors_not_mem R p n T hT
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), fun k hk => h k hk⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfFinite
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.FiniteSectionLift

theorem exists_section_of_finite (R A K : CommRingCat) (φ : R ⟶ K)
    (hinj : Function.Injective φ.hom)
    (hint : ∀ x : K, φ.hom.IsIntegralElem x → ∃ r : R, φ.hom r = x)
    (g : R ⟶ A) (hg : g.hom.Finite) (f : A ⟶ K) (hf : g ≫ f = φ) :
    ∃ s : A ⟶ R, g ≫ s = 𝟙 R ∧ s ≫ φ = f := by
  have hmem : ∀ a, f.hom a ∈ φ.hom.range := by
    intro a
    obtain ⟨q, hq, h0⟩ := hg.to_isIntegral a
    obtain ⟨r, hr⟩ := hint (f.hom a) ⟨q, hq, by
      rw [← hf, CommRingCat.hom_comp, ← Polynomial.hom_eval₂, h0, map_zero]⟩
    exact ⟨r, hr⟩
  let e : R ≃+* φ.hom.range := RingEquiv.ofBijective φ.hom.rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), φ.hom.rangeRestrict_surjective⟩
  let t : A →+* R := e.symm.toRingHom.comp (f.hom.codRestrict φ.hom.range hmem)
  have hkey : ∀ a, φ.hom (t a) = f.hom a := by
    intro a
    have h1 : e (e.symm ⟨f.hom a, hmem a⟩) = ⟨f.hom a, hmem a⟩ := e.apply_symm_apply _
    exact congrArg Subtype.val h1
  refine ⟨CommRingCat.ofHom t, ?_, ?_⟩
  · ext r
    apply hinj
    change φ.hom (t (g.hom r)) = φ.hom r
    rw [hkey, ← hf]
    rfl
  · ext a
    exact hkey a

theorem lift_of_finite : ∀ (R K : CommRingCat) (φ : R ⟶ K),
    Function.Injective (⇑(CommRingCat.Hom.hom φ) : (↑R : Type) → (↑K : Type)) →
    (∀ (x : (↑K : Type)), RingHom.IsIntegralElem (CommRingCat.Hom.hom φ) x →
      ∃ (r : (↑R : Type)), (CommRingCat.Hom.hom φ : (↑R : Type) → (↑K : Type)) r = x) →
    ∀ (Z P : AlgebraicGeometry.Scheme) (p : Z ⟶ P) (ξ₀ : AlgebraicGeometry.Spec R ⟶ P)
      (y : AlgebraicGeometry.Spec K ⟶ Z), AlgebraicGeometry.IsFinite p →
      CategoryTheory.CategoryStruct.comp y p =
        CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map φ) ξ₀ →
      ∃ (ξ : AlgebraicGeometry.Spec R ⟶ Z),
        CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Spec.map φ) ξ = y ∧
        CategoryTheory.CategoryStruct.comp ξ p = ξ₀ := by
  intro R K φ hinj hint Z P p ξ₀ y hp hy
  haveI : IsAffine (pullback p ξ₀) := isAffine_of_isAffineHom (pullback.snd p ξ₀)
  let l : Spec K ⟶ pullback p ξ₀ := pullback.lift y (Spec.map φ) hy
  let g : R ⟶ Γ(pullback p ξ₀, ⊤) :=
    Spec.preimage ((pullback p ξ₀).isoSpec.inv ≫ pullback.snd p ξ₀)
  let f : Γ(pullback p ξ₀, ⊤) ⟶ K := Spec.preimage (l ≫ (pullback p ξ₀).isoSpec.hom)
  have hgS : Spec.map g = (pullback p ξ₀).isoSpec.inv ≫ pullback.snd p ξ₀ := Spec.map_preimage _
  have hfS : Spec.map f = l ≫ (pullback p ξ₀).isoSpec.hom := Spec.map_preimage _
  have hgfin : g.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hgS]
    infer_instance
  have hf : g ≫ f = φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hfS, hgS]
    simp only [l, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_snd _ _ _
  obtain ⟨s, hs1, hs2⟩ := exists_section_of_finite R _ K φ hinj hint g hgfin f hf
  refine ⟨Spec.map s ≫ (pullback p ξ₀).isoSpec.inv ≫ pullback.fst p ξ₀, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, hs2, hfS]
    simp only [l, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc _ (pullback.snd p ξ₀),
      ← hgS, ← Category.assoc, ← Spec.map_comp, hs1, Spec.map_id, Category.id_comp]

end GlobalTheory.FiniteSectionLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearExtensionOfFormWithTransportedRe
section
open Module

namespace GlobalTheory.SemilinearReading

theorem exists_semilinear_extension_rep :
    ∀ {K LL Cs W G : Type} [Field K] [Field LL] [Algebra K LL] [AddCommGroup Cs] [Module K Cs] [AddCommGroup W] [Module ℂ W] [Group G] {n m : ℕ} (σ₀ : K →+* ℂ) (σ : LL →+* ℂ), (∀ a, σ (algebraMap K LL a) = σ₀ a) → ∀ (cu : Cs →ₗ[K] (Fin n → LL)) (b : Fin m → Cs), Submodule.span K (Set.range b) = ⊤ → LinearIndependent LL (fun k => cu (b k)) → Submodule.span LL (Set.range fun k => cu (b k)) = ⊤ → ∀ (R : Cs →ₛₗ[σ₀] W), LinearIndependent ℂ (fun k => R (b k)) → Submodule.span ℂ (Set.range R) = ⊤ → ∀ (ρL : G →* ((Fin n → LL) →ₗ[LL] (Fin n → LL))), ∃ (f : (Fin n → LL) →ₛₗ[σ] W) (ρ : Representation ℂ G W), (∀ F, f (cu F) = R F) ∧ (∀ g w, ρ g (f w) = f (ρL g w)) ∧ (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ := by
  intro K LL Cs W G _ _ _ _ _ _ _ _ n m σ₀ σ hσ cu b hbs hbi hbt R hR hRs ρL
  classical
  let B : Basis (Fin m) LL (Fin n → LL) := Basis.mk hbi hbt.ge
  have hB : ∀ k, B k = cu (b k) := fun k => Basis.mk_apply _ _ _
  let f : (Fin n → LL) →ₛₗ[σ] W :=
    { toFun := fun w => ∑ k, σ (B.repr w k) • R (b k)
      map_add' := by
        intro x y
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp [Finset.smul_sum, mul_smul] }
  have hfB : ∀ k, f (B k) = R (b k) := by
    intro k
    change ∑ j, σ (B.repr (B k) j) • R (b j) = _
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Finsupp.single_apply, hj.symm]
    · simp
  have hcu : ∀ F, f (cu F) = R F := by
    intro F
    have hF : F ∈ Submodule.span K (Set.range b) := by rw [hbs]; trivial
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hF
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smulₛₗ R, ← hB, ← algebraMap_smul LL (a k) (B k), map_smulₛₗ f, hσ, hfB]
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun k => R (b k)) := by
    rw [← hRs, Submodule.span_le]
    rintro _ ⟨F, rfl⟩
    rw [← hcu]
    change ∑ j, σ (B.repr (cu F) j) • R (b j) ∈ _
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let C : Basis (Fin m) ℂ W := Basis.mk hR hsp
  have hC : ∀ k, C k = f (B k) := fun k => by rw [hfB]; exact Basis.mk_apply _ _ _
  let r : G → W →ₗ[ℂ] W := fun g => C.constr ℂ fun k => f (ρL g (B k))
  have hr : ∀ g w, r g (f w) = f (ρL g w) := by
    intro g w
    conv_lhs => rw [← B.sum_repr w]
    conv_rhs => rw [← B.sum_repr w]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ f, map_smul, map_smul, map_smulₛₗ f, ← hC]
    simp [r]
  let ρ : Representation ℂ G W :=
    { toFun := r
      map_one' := C.ext fun k => by rw [hC, hr]; simp
      map_mul' := fun g h => C.ext fun k => by
        rw [hC, Module.End.mul_apply, hr, hr, hr, map_mul]; rfl }
  refine ⟨f, ρ, hcu, hr, ?_, ?_⟩
  · have hmn : m = n := by
      simpa using (Module.finrank_eq_card_basis B).symm
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · refine hsp.trans ?_
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      change R (b k) ∈ _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hfB, ← (Pi.basisFun LL (Fin n)).sum_repr (B k), map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [map_smulₛₗ f, Pi.basisFun_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Module.finrank_eq_card_basis C, hmn]
  · rw [eq_top_iff]
    refine hsp.trans (Submodule.span_mono ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨B k, hfB k⟩

end GlobalTheory.SemilinearReading
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparabilityElementOfTraceNondegenerate
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory.TraceCasimir

variable {A : Type} [Ring A] [Module.Free ℤ A] [Module.Finite ℤ A]

noncomputable def trL : A →ₗ[ℤ] ℤ := LinearMap.trace ℤ A ∘ₗ LinearMap.mul ℤ A

lemma trL_apply (z : A) : trL z = LinearMap.trace ℤ A (LinearMap.mulLeft ℤ z) := rfl

lemma trL_comm (x y : A) : trL (x * y) = trL (y * x) := by
  rw [trL_apply, trL_apply, LinearMap.mulLeft_mul, LinearMap.mulLeft_mul]
  exact LinearMap.trace_mul_comm ℤ _ _

lemma trL_eq_sum {n : ℕ} (b : Module.Basis (Fin n) ℤ A) (z : A) :
    trL z = ∑ k, b.repr (z * b k) k := by
  rw [trL_apply, LinearMap.trace_eq_matrix_trace ℤ b, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply]

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ A)

noncomputable def gram : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun k l => trL (b k * b l)

noncomputable def dualD (l : Fin n) : A := ∑ m, (gram b).adjugate m l • b m

lemma trL_mul_dualD (u : A) (l : Fin n) :
    trL (u * dualD b l) = ∑ m, (gram b).adjugate m l * trL (u * b m) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dualD, Finset.mul_sum, mul_smul_comm, map_sum, map_zsmul, smul_eq_mul]

lemma trL_basis_mul_dualD (k l : Fin n) :
    trL (b k * dualD b l) = if k = l then (gram b).det else 0 := by
  rw [trL_mul_dualD]
  calc ∑ m, (gram b).adjugate m l * trL (b k * b m)
      = ∑ m, gram b k m * (gram b).adjugate m l :=
        Finset.sum_congr rfl fun m _ => mul_comm _ _
    _ = (gram b * (gram b).adjugate) k l := (Matrix.mul_apply).symm
    _ = _ := by rw [Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply]; split_ifs <;> simp

lemma det_mul_repr (u : A) (k : Fin n) :
    (gram b).det * b.repr u k = trL (u * dualD b k) := by
  conv_rhs => rw [← b.sum_repr u]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_zsmul, trL_basis_mul_dualD, smul_eq_mul]
  simp [mul_comm]

lemma det_smul_eq (u : A) : (gram b).det • u = ∑ l, trL (u * dualD b l) • b l := by
  conv_lhs => rw [← b.sum_repr u]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul, det_mul_repr]

section Nondeg

variable (hnd : ∀ x : A, (∀ y : A, LinearMap.trace ℤ A (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0)
include hnd

lemma eq_zero_of_trL_mul_basis (v : A) (hv : ∀ k, trL (v * b k) = 0) : v = 0 := by
  apply hnd v
  intro y
  rw [← trL_apply]
  conv_lhs => rw [← b.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_zsmul, hv, smul_zero,
    Finset.sum_const_zero]

lemma eq_zero_of_trL_basis_mul (v : A) (hv : ∀ k, trL (b k * v) = 0) : v = 0 :=
  eq_zero_of_trL_mul_basis b hnd v fun k => by rw [trL_comm]; exact hv k

lemma det_smul_eq' (u : A) : (gram b).det • u = ∑ l, trL (b l * u) • dualD b l := by
  rw [← sub_eq_zero]
  apply eq_zero_of_trL_basis_mul b hnd
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mul_sub, Finset.mul_sum, mul_smul_comm, map_sub, map_sum, map_zsmul, smul_eq_mul,
    trL_basis_mul_dualD, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

lemma det_ne_zero : (gram b).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  apply hv0
  have hx : ∑ k, v k • b k = 0 := by
    apply eq_zero_of_trL_mul_basis b hnd
    intro l
    have := congrFun hv l
    simp only [Matrix.vecMul, dotProduct, gram, Matrix.of_apply, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_zsmul, smul_eq_mul]
    exact this
  funext k
  exact Fintype.linearIndependent_iff.mp b.linearIndependent v hx k

lemma sum_mul_dualD : ∑ k, b k * dualD b k = ((gram b).det : A) := by
  rw [← sub_eq_zero]
  apply eq_zero_of_trL_mul_basis b hnd
  intro j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [sub_mul, map_sub, Finset.sum_mul, map_sum]
  have h1 : ∀ k, trL (b k * dualD b k * b j) = (gram b).det * b.repr (b j * b k) k := by
    intro k
    rw [trL_comm, ← mul_assoc, ← det_mul_repr]
  rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.mul_sum, ← trL_eq_sum b, ← zsmul_eq_mul,
    map_zsmul, smul_eq_mul, sub_self]

lemma balanced (c : A) :
    ∑ k, (c * b k) ⊗ₜ[ℤ] dualD b k = ∑ k, b k ⊗ₜ[ℤ] (dualD b k * c) := by
  haveI : Module.Free ℤ (A ⊗[ℤ] A) := Module.Free.of_basis (b.tensorProduct b)
  apply smul_right_injective (A ⊗[ℤ] A) (det_ne_zero b hnd)
  dsimp only
  simp only [Finset.smul_sum]
  have hL : ∀ k, (gram b).det • ((c * b k) ⊗ₜ[ℤ] dualD b k) =
      ∑ l, trL (c * b k * dualD b l) • (b l ⊗ₜ[ℤ] dualD b k) := by
    intro k
    rw [TensorProduct.smul_tmul', det_smul_eq, TensorProduct.sum_tmul]
    simp only [TensorProduct.smul_tmul']
  have hR : ∀ k, (gram b).det • (b k ⊗ₜ[ℤ] (dualD b k * c)) =
      ∑ l, trL (b l * (dualD b k * c)) • (b k ⊗ₜ[ℤ] dualD b l) := by
    intro k
    rw [← TensorProduct.tmul_smul, det_smul_eq' b hnd, TensorProduct.tmul_sum]
    simp only [TensorProduct.tmul_smul]
  simp only [hL, hR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  congr 1
  rw [mul_assoc, trL_comm, mul_assoc]

end Nondeg

end GlobalTheory.TraceCasimir


open GlobalTheory.TraceCasimir in
theorem GlobalTheory.exists_separability_element_of_trace_nondegenerate :
    ∀ (A : Type) [Ring A] [Module.Free ℤ A] [Module.Finite ℤ A],
      (∀ x : A, (∀ y : A, LinearMap.trace ℤ A (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0) →
      ∃ (N : ℤ) (k : ℕ) (x y : Fin k → A), N ≠ 0 ∧ ∑ j, x j * y j = (N : A) ∧
        ∀ c : A, ∑ j, (c * x j) ⊗ₜ[ℤ] y j = ∑ j, x j ⊗ₜ[ℤ] (y j * c) := by
  intro A _ _ _ hnd
  let b := Module.finBasis ℤ A
  exact ⟨(gram b).det, _, b, dualD b, det_ne_zero b hnd, sum_mul_dualD b hnd, balanced b hnd⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherMore
section
universe u_1 u_2

namespace GlobalTheory.BandLemmaThird

theorem main : (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop := @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦ ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k)); ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [inst_1 : Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ} {i j : ℕ} {X Y : Matrix ι ι k}, d1 ℓ i X → d1 ℓ j Y → d1 ℓ (i + j) (X * Y)) := by
  intro d1 k _ ι _ _ ℓ i j X Y hX hY r s hrs
  show (X * Y) r s = 0
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases h : ℓ t < ℓ r + i
  · rw [hX r t h, zero_mul]
  · rw [hY t s (by omega), mul_zero]

end GlobalTheory.BandLemmaThird
end

