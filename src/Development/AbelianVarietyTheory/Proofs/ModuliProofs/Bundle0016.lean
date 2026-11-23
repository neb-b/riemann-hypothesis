module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DehomogenisationIsRadicalAndTorsionFree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem eval₂_scale_of_isHomogeneous {o σ S : Type} [CommRing o] [CommRing S] (f : o →+* S)
    (g : σ → S) (u : S) {F : MvPolynomial σ o} {e : ℕ} (hF : F.IsHomogeneous e) :
    MvPolynomial.eval₂ f (fun j => g j * u) F = MvPolynomial.eval₂ f g F * u ^ e := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hF.degree_eq_sum_deg_support hd, ← Finset.prod_pow_eq_pow_sum, _root_.mul_assoc,
    ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun j _ => mul_pow _ _ _

theorem exists_ker_eq_dehomogenisation {o σ : Type} [CommRing o] (I : Ideal (MvPolynomial σ o))
    (i : σ) (hI : ∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) :
    ∃ ψ : MvPolynomial σ o →+*
        Localization.Away (Ideal.Quotient.mk I (MvPolynomial.X i)),
      (∀ c, ψ (MvPolynomial.C c) = algebraMap (MvPolynomial σ o ⧸ I) _
        (Ideal.Quotient.mk I (MvPolynomial.C c))) ∧
      RingHom.ker ψ = I ⊔ Ideal.span {MvPolynomial.X i - 1} := by
  classical
  let x := Ideal.Quotient.mk I (MvPolynomial.X i)
  let L := Localization.Away x
  let g : MvPolynomial σ o →+* L :=
    (algebraMap (MvPolynomial σ o ⧸ I) L).comp (Ideal.Quotient.mk I)
  let u : L := IsLocalization.Away.invSelf x
  let ψ : MvPolynomial σ o →+* L :=
    MvPolynomial.eval₂Hom (g.comp MvPolynomial.C) (fun j => g (MvPolynomial.X j) * u)

  have hg : ∀ F : MvPolynomial σ o,
      MvPolynomial.eval₂ (g.comp MvPolynomial.C) (fun j => g (MvPolynomial.X j)) F = g F := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [MvPolynomial.eval₂_add, hp, hq, map_add (f := _)]
    | mul_X p j hp => rw [MvPolynomial.eval₂_mul, hp, MvPolynomial.eval₂_X, map_mul]
  have hxu : g (MvPolynomial.X i) * u = 1 := IsLocalization.Away.mul_invSelf x
  refine ⟨ψ, fun c => by exact MvPolynomial.eval₂Hom_C _ _ c, le_antisymm ?_ ?_⟩
  ·
    let J := I ⊔ Ideal.span {MvPolynomial.X i - 1}
    let q : MvPolynomial σ o ⧸ I →+* MvPolynomial σ o ⧸ J :=
      Ideal.Quotient.lift I (Ideal.Quotient.mk J)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (le_sup_left (a := I) ha))
    have hq1 : q x = 1 := by
      change Ideal.Quotient.mk J (MvPolynomial.X i) = 1
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      exact le_sup_right (a := I) (Ideal.subset_span (Set.mem_singleton _))
    have hunit : IsUnit (q x) := by rw [hq1]; exact isUnit_one
    let θ : L →+* MvPolynomial σ o ⧸ J := IsLocalization.Away.lift x hunit
    have hθ : ∀ a, θ (algebraMap _ L a) = q a := IsLocalization.Away.lift_eq x hunit
    have hθu : θ u = 1 := by
      have h := congrArg θ hxu
      rw [map_mul, map_one] at h
      have h' : θ (g (MvPolynomial.X i)) = 1 := by
        change θ (algebraMap _ L x) = 1
        rw [hθ, hq1]
      rwa [h', _root_.one_mul] at h
    have hcomp : θ.comp ψ = Ideal.Quotient.mk J := by
      apply MvPolynomial.ringHom_ext
      · intro c
        rw [RingHom.comp_apply]
        change θ (MvPolynomial.eval₂Hom (g.comp MvPolynomial.C)
          (fun j => g (MvPolynomial.X j) * u) (MvPolynomial.C c)) = _
        rw [MvPolynomial.eval₂Hom_C]
        change θ (algebraMap _ L (Ideal.Quotient.mk I (MvPolynomial.C c))) = _
        rw [hθ]
        rfl
      · intro j
        rw [RingHom.comp_apply]
        change θ (MvPolynomial.eval₂Hom (g.comp MvPolynomial.C)
          (fun j => g (MvPolynomial.X j) * u) (MvPolynomial.X j)) = _
        rw [MvPolynomial.eval₂Hom_X', map_mul, hθu, _root_.mul_one]
        change θ (algebraMap _ L (Ideal.Quotient.mk I (MvPolynomial.X j))) = _
        rw [hθ]
        rfl
    intro F hF
    rw [RingHom.mem_ker] at hF
    have h0 : Ideal.Quotient.mk J F = 0 := by
      rw [← hcomp, RingHom.comp_apply, hF, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  · apply sup_le
    ·
      intro F hF
      set_option synthInstance.maxHeartbeats 100000 in
        rw [RingHom.mem_ker, ← MvPolynomial.sum_homogeneousComponent F, map_sum]
      refine Finset.sum_eq_zero fun e _ => ?_
      have h1 := eval₂_scale_of_isHomogeneous (g.comp MvPolynomial.C)
        (fun j => g (MvPolynomial.X j)) u (MvPolynomial.homogeneousComponent_isHomogeneous e F)
      rw [MvPolynomial.coe_eval₂Hom, h1, hg]
      have h2 : Ideal.Quotient.mk I (MvPolynomial.homogeneousComponent e F) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (hI F hF e)
      change algebraMap _ L (Ideal.Quotient.mk I _) * _ = 0
      rw [h2, map_zero, zero_mul]
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub, map_one]
      change MvPolynomial.eval₂Hom (g.comp MvPolynomial.C)
        (fun j => g (MvPolynomial.X j) * u) (MvPolynomial.X i) - 1 = 0
      rw [MvPolynomial.eval₂Hom_X', hxu, sub_self]

theorem dehomogenisation_isRadical_and_torsionFree :
    ∀ (o σ : Type) [CommRing o] (I : Ideal (MvPolynomial σ o)) (i : σ), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → (I.IsRadical → (I ⊔ Ideal.span {MvPolynomial.X i - 1}).IsRadical) ∧ ((∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ I → F ∈ I) → ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ I ⊔ Ideal.span {MvPolynomial.X i - 1} → F ∈ I ⊔ Ideal.span {MvPolynomial.X i - 1}) := by
  intro o σ _ I i hI
  obtain ⟨ψ, hC, hker⟩ := exists_ker_eq_dehomogenisation I i hI
  rw [← hker]
  refine ⟨fun hrad => ?_, fun htf c F hc hF => ?_⟩
  ·
    have : IsReduced (MvPolynomial σ o ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hrad
    rintro F ⟨n, hn⟩
    rw [RingHom.mem_ker] at hn ⊢
    rw [map_pow] at hn
    exact IsReduced.eq_zero _ ⟨n, hn⟩
  ·
    rw [RingHom.mem_ker, map_mul] at hF
    rw [RingHom.mem_ker]
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective
      (S := Localization.Away (Ideal.Quotient.mk I (MvPolynomial.X i)))
      (Submonoid.powers (Ideal.Quotient.mk I (MvPolynomial.X i))) (ψ F)
    simp only at hs
    rw [← hs, hC, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hF
    obtain ⟨⟨_, k, rfl⟩, hm⟩ := hF
    obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hIG : MvPolynomial.C c * (MvPolynomial.X i ^ k * G) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hm]
      simp only [map_mul, map_pow]
      ring
    have hG : MvPolynomial.X i ^ k * G ∈ I := htf c _ hc hIG
    rw [← hs, IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨_, k, rfl⟩, ?_⟩
    change Ideal.Quotient.mk I (MvPolynomial.X i) ^ k * Ideal.Quotient.mk I G = 0
    rw [← map_pow, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hG

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnComplexExtend
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

noncomputable def complexExtend {O M : Type} [CommRing O] [Ring M] [Algebra ℂ M]
    (f : O →+* M) : ℂ ⊗[ℤ] O →ₐ[ℂ] M :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ M) f.toIntAlgHom
    (fun x y => Algebra.commute_algebraMap_left x (f y))

theorem complexExtend_tmul {O M : Type} [CommRing O] [Ring M] [Algebra ℂ M]
    (f : O →+* M) (c : ℂ) (a : O) : complexExtend f (c ⊗ₜ a) = c • f a := by
  rw [Algebra.smul_def]
  exact Algebra.TensorProduct.lift_tmul _ _ _ c a

theorem exists_eigen_element (O : Type) [CommRing O] [Module.Finite ℤ O]
    [IsReduced (ℂ ⊗[ℤ] O)] (τ : O →+* ℂ) :
    ∃ e : ℂ ⊗[ℤ] O, complexExtend τ e = 1 ∧ ∀ a : O, ((1 : ℂ) ⊗ₜ[ℤ] a) * e = τ a • e := by
  haveI : IsArtinianRing (ℂ ⊗[ℤ] O) := IsArtinianRing.of_finite ℂ _
  haveI : IsSemisimpleRing (ℂ ⊗[ℤ] O) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  obtain ⟨f, hf, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent
    (RingHom.ker (complexExtend τ))
  have hf0 : complexExtend τ f = 0 := by
    have : f ∈ RingHom.ker (complexExtend τ) := hI ▸ Ideal.mem_span_singleton_self f
    exact this
  refine ⟨1 - f, by simp [hf0], fun a => ?_⟩
  have hk : ((1 : ℂ) ⊗ₜ[ℤ] a) - algebraMap ℂ (ℂ ⊗[ℤ] O) (τ a) ∈
      RingHom.ker (complexExtend τ) := by
    rw [RingHom.mem_ker, map_sub, complexExtend_tmul, AlgHom.commutes]
    simp
  rw [hI, Ideal.mem_span_singleton'] at hk
  obtain ⟨y, hy⟩ := hk
  rw [Algebra.smul_def, ← sub_eq_zero, ← sub_mul, ← hy, _root_.mul_assoc, mul_sub, _root_.mul_one, hf.eq,
    sub_self, mul_zero]

theorem complexExtend_diagonal {O : Type} [CommRing O] {g : ℕ}
    (f : O →+* Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (O →+* ℂ))
    (hf : ∀ a, f a = Matrix.diagonal (fun i => ty i a)) (x : ℂ ⊗[ℤ] O) :
    complexExtend f x = Matrix.diagonal (fun i => complexExtend (ty i) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    simp only [complexExtend_tmul, hf]
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, Matrix.diagonal_add]

theorem differentiableOn_complexExtend {O : Type} [CommRing O] {g m : ℕ}
    {B : Set (Fin m → ℂ)} (F : (Fin m → ℂ) → (O →+* Matrix (Fin g) (Fin g) ℂ))
    (hF : ∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) (x : ℂ ⊗[ℤ] O) (i j : Fin g) :
    DifferentiableOn ℂ (fun b => complexExtend (F b) x i j) B := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    simp only [complexExtend_tmul, Matrix.smul_apply, smul_eq_mul]
    exact (hF a i j).const_mul c
  | add x y hx hy =>
    simp only [map_add (f := _), Matrix.add_apply]
    exact hx.add hy

theorem holomorphic_diagonalisation :
    ∀ (O : Type) [CommRing O] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (F : (Fin m → ℂ) → (O →+* Matrix (Fin g) (Fin g) ℂ)) (ty : Fin g → (O →+* ℂ)), Module.Finite ℤ O → IsReduced (ℂ ⊗[ℤ] O) → IsOpen B → b₀ ∈ B → (∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) → (∀ a, F b₀ a = Matrix.diagonal (fun i => ty i a)) → ∃ (B' : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h b) ∧ ∀ a, F b a * h b = h b * Matrix.diagonal (fun i => ty i a) := by
  intro O _ g m B b₀ F ty hfin hred hB hb₀ hF hF₀
  choose e he1 he using fun τ => exists_eigen_element O τ
  let h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ :=
    fun b => Matrix.of fun i j => complexExtend (F b) (e (ty j)) i j
  have hd : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B := fun i j =>
    differentiableOn_complexExtend F hF _ i j
  have h0 : h b₀ = 1 := by
    ext i j
    simp only [h, Matrix.of_apply, complexExtend_diagonal _ ty hF₀]
    by_cases hij : i = j
    · subst hij; simp [he1]
    · simp [hij]
  have hc : ContinuousOn h B :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hd i j).continuousOn
  have hdet : ContinuousOn (fun b => (h b).det) B :=
    (Continuous.matrix_det continuous_id).comp_continuousOn hc
  refine ⟨B ∩ (fun b => (h b).det) ⁻¹' {0}ᶜ, h,
    hdet.isOpen_inter_preimage hB isOpen_compl_singleton, ⟨hb₀, by simp [h0]⟩,
    Set.inter_subset_left, h0, fun i j => (hd i j).mono Set.inter_subset_left, ?_⟩
  rintro b ⟨-, hb⟩
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hb), fun a => ?_⟩
  ext i j
  have key := congrArg (fun x => complexExtend (F b) x i j) (he (ty j) a)
  simp only [map_mul, map_smul, complexExtend_tmul, one_smul, Matrix.smul_apply,
    smul_eq_mul] at key
  rw [Matrix.mul_diagonal, mul_comm]
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOfNormResultantEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace ResultantNorm

open Polynomial Filter Topology

theorem exists_prod_aeval {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (a : Multiset Ω)
    (P : K[X]) (hP : P.map (algebraMap K Ω) = (a.map fun x => X - C x).prod) (F : K[X]) :
    ∃ u : K, algebraMap K Ω u = (a.map fun x => aeval x F).prod := by
  have hs : (P.map (algebraMap K Ω)).Splits := by
    rw [hP]; exact Splits.multisetProd (by
      intro f hf; obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 hf; exact Splits.X_sub_C x)
  have hm : (P.map (algebraMap K Ω)).Monic := by
    rw [hP]; exact monic_multisetProd_X_sub_C a
  have hr : (P.map (algebraMap K Ω)).roots = a := by
    rw [hP]; exact roots_multiset_prod_X_sub_C a
  refine ⟨resultant P F (P.map (algebraMap K Ω)).natDegree F.natDegree, ?_⟩
  rw [← resultant_map_map, resultant_eq_prod_eval _ _ _ natDegree_map_le hs, hm.leadingCoeff,
    one_pow, _root_.one_mul, hr]
  congr 1
  refine Multiset.map_congr rfl fun x _ => ?_
  rw [eval_map_algebraMap]

theorem eq_of_countP {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    [DecidableEq Ω] (n : ℕ) : ∀ (a b : Multiset Ω) (P Q : K[X]), a.card = n →
      P.map (algebraMap K Ω) = (a.map fun x => X - C x).prod →
      Q.map (algebraMap K Ω) = (b.map fun x => X - C x).prod →
      (∀ G : K[X], a.countP (fun x => aeval x G = 0) = b.countP (fun x => aeval x G = 0)) →
      P = Q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b P Q hn hP hQ h
  have hinj := map_injective (algebraMap K Ω) (algebraMap K Ω).injective
  by_cases ha : a = 0
  · have h0 := h 0
    subst ha
    simp at h0
    have hb : b = 0 := by
      rw [← Multiset.card_eq_zero]
      simpa using h0.symm
    subst hb
    exact hinj (hP.trans hQ.symm)
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero ha
  have hxi : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  set G := minpoly K x with hG
  have hpos : 0 < b.countP (fun y => aeval y G = 0) := by
    rw [← h G]; exact Multiset.countP_pos.2 ⟨x, hx, minpoly.aeval K x⟩
  obtain ⟨y, hy, hyG⟩ := Multiset.countP_pos.1 hpos
  have hGy : G = minpoly K y :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hxi) hyG (minpoly.monic hxi)
  have hGm : (G.map (algebraMap K Ω)).Monic := (minpoly.monic hxi).map _
  have key : ∀ (c : Multiset Ω) (R : K[X]) (z : Ω), z ∈ c → G = minpoly K z →
      R.map (algebraMap K Ω) = (c.map fun x => X - C x).prod →
      ∃ (c' : Multiset Ω) (R' : K[X]), R = G * R' ∧ c = (G.map (algebraMap K Ω)).roots + c' ∧
        R'.map (algebraMap K Ω) = (c'.map fun x => X - C x).prod := by
    intro c R z hz hGz hR
    have hs : (R.map (algebraMap K Ω)).Splits := by
      rw [hR]; exact Splits.multisetProd (by
        intro f hf; obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 hf; exact Splits.X_sub_C x)
    have hm : (R.map (algebraMap K Ω)).Monic := by
      rw [hR]; exact monic_multisetProd_X_sub_C c
    have hr : (R.map (algebraMap K Ω)).roots = c := by
      rw [hR]; exact roots_multiset_prod_X_sub_C c
    have hz0 : aeval z R = 0 := by
      rw [← hr] at hz
      have := (mem_roots hm.ne_zero).1 hz
      rwa [IsRoot.def, eval_map_algebraMap] at this
    obtain ⟨R', hR'⟩ : G ∣ R := hGz ▸ minpoly.dvd K z hz0
    have hmul : R.map (algebraMap K Ω) = G.map (algebraMap K Ω) * R'.map (algebraMap K Ω) := by
      rw [hR', Polynomial.map_mul]
    refine ⟨(R'.map (algebraMap K Ω)).roots, R', hR', ?_, ?_⟩
    · rw [← hr, ← roots_mul (hmul ▸ hm.ne_zero), ← hmul]
    · exact (hs.of_dvd hm.ne_zero ⟨_, by rw [hmul, mul_comm]⟩).eq_prod_roots_of_monic
        (hGm.of_mul_monic_left (hmul ▸ hm))
  obtain ⟨a', P', hP1, hP2, hP3⟩ := key a P x hx hG hP
  obtain ⟨b', Q', hQ1, hQ2, hQ3⟩ := key b Q y hy hGy hQ
  have hxr : x ∈ (G.map (algebraMap K Ω)).roots := by
    rw [mem_roots hGm.ne_zero, IsRoot.def, eval_map_algebraMap]; exact minpoly.aeval K x
  have hlt : a'.card < n := by
    have := Multiset.card_pos_iff_exists_mem.2 ⟨x, hxr⟩
    rw [← hn, hP2, Multiset.card_add]; omega
  rw [hP1, hQ1, ih _ hlt a' b' P' Q' rfl hP3 hQ3 fun H => ?_]
  have := h H
  rw [hP2, hQ2, Multiset.countP_add, Multiset.countP_add] at this
  omega

section Normed

variable {K Ω : Type} [NontriviallyNormedField K] [NormedField Ω] [NormedAlgebra K Ω]

theorem norm_prod_add [DecidableEq Ω] (a : Multiset Ω) (g : Ω → Ω) (t : K) :
    ‖(a.map fun x => g x + algebraMap K Ω t).prod‖ =
      ‖t‖ ^ a.countP (fun x => g x = 0) *
        ‖((a.filter fun x => ¬ g x = 0).map fun x => g x + algebraMap K Ω t).prod‖ := by
  induction a using Multiset.induction_on with
  | empty => simp
  | cons x a ih =>
    by_cases hx : g x = 0
    · rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih,
        Multiset.countP_cons_of_pos _ (by exact hx), Multiset.filter_cons_of_neg _ (by simpa using hx), hx,
        zero_add, norm_algebraMap']
      ring
    · rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih,
        Multiset.countP_cons_of_neg _ (by exact hx), Multiset.filter_cons_of_pos _ (by exact hx),
        Multiset.map_cons, Multiset.prod_cons, norm_mul]
      ring

theorem countP_le [DecidableEq Ω] (a b : Multiset Ω) (g : Ω → Ω)
    (h : ∀ t : K, ‖(a.map fun x => g x + algebraMap K Ω t).prod‖ =
      ‖(b.map fun x => g x + algebraMap K Ω t).prod‖) :
    b.countP (fun x => g x = 0) ≤ a.countP (fun x => g x = 0) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
  set A : K → ℝ := fun t =>
    ‖((a.filter fun x => ¬ g x = 0).map fun x => g x + algebraMap K Ω t).prod‖ with hA
  set B : K → ℝ := fun t =>
    ‖((b.filter fun x => ¬ g x = 0).map fun x => g x + algebraMap K Ω t).prod‖ with hB
  have hc : ∀ c : Multiset Ω, Continuous fun t : K =>
      ‖(c.map fun x => g x + algebraMap K Ω t).prod‖ := fun c =>
    (continuous_multiset_prod c fun x _ => continuous_const.add (continuous_algebraMap K Ω)).norm
  have hAc : Continuous A := hc _
  have hBc : Continuous fun t : K => ‖t‖ ^ (k + 1) * B t := (continuous_norm.pow _).mul (hc _)
  have heq : Set.EqOn A (fun t : K => ‖t‖ ^ (k + 1) * B t) {0}ᶜ := by
    intro t ht
    have ht0 : ‖t‖ ≠ 0 := norm_ne_zero_iff.2 ht
    have := h t
    rw [norm_prod_add a, norm_prod_add b, hk, add_assoc, pow_add, _root_.mul_assoc] at this
    exact mul_left_cancel₀ (pow_ne_zero _ ht0) this
  have h0 := congrFun (Continuous.ext_on (dense_compl_singleton (0 : K)) hAc hBc heq) 0
  simp only [hA, norm_zero, pow_succ, mul_zero, zero_mul, map_zero, add_zero, norm_eq_zero,
    Multiset.prod_eq_zero_iff, Multiset.mem_map, Multiset.mem_filter] at h0
  obtain ⟨x, ⟨-, hx⟩, hx'⟩ := h0
  exact hx hx'

end Normed

section Padic

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

theorem card_eq (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] Ω] (a b : Multiset Ω)
    (h : ∀ F : ℤ[X], ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖) :
    a.card = b.card := by
  have h1 := h (C (l : ℤ))
  have hl : ‖(l : Ω)‖ = ‖(l : ℚ_[l])‖ := by
    rw [← norm_algebraMap' Ω (l : ℚ_[l]), map_natCast]
  simp only [aeval_C, map_natCast, Multiset.map_const', Multiset.prod_replicate, norm_pow,
    hl] at h1
  refine pow_right_injective₀ ?_ ?_ h1
  · exact norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  · exact Padic.norm_p_lt_one.ne

theorem rat_case (a b : Multiset Ω)
    (h : ∀ F : ℤ[X], ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖)
    (F : ℚ[X]) :
    ‖(a.map fun x => aeval x (F.map (algebraMap ℚ ℚ_[l]))).prod‖ =
      ‖(b.map fun x => aeval x (F.map (algebraMap ℚ ℚ_[l]))).prod‖ := by
  obtain ⟨d, hd, hF⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) F
  set F₀ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) F
  have hd0 : ((d : ℚ_[l])) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hd)
  have hx : ∀ x : Ω, aeval x F₀ =
      algebraMap ℚ_[l] Ω (d : ℚ_[l]) * aeval x (F.map (algebraMap ℚ ℚ_[l])) := by
    intro x
    have h1 : F₀.map (algebraMap ℤ ℚ_[l]) = C (d : ℚ_[l]) * F.map (algebraMap ℚ ℚ_[l]) := by
      have := congrArg (Polynomial.map (algebraMap ℚ ℚ_[l])) hF
      rw [Polynomial.map_map, zsmul_eq_mul, Polynomial.map_mul, Polynomial.map_intCast] at this
      rw [← C_eq_intCast] at this
      rw [← this]
      congr 1
    rw [← aeval_map_algebraMap ℚ_[l], h1, map_mul, aeval_C]
  have h1 := h F₀
  simp only [hx, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, norm_mul,
    norm_pow, norm_algebraMap', card_eq l a b h] at h1
  exact mul_left_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.2 hd0)) h1

theorem padic_case (a b : Multiset Ω)
    (h : ∀ F : ℤ[X], ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖)
    (F : ℚ_[l][X]) :
    ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖ := by
  set n := F.natDegree + 1
  let φ : Multiset Ω → (Fin n → ℚ_[l]) → ℝ := fun c v =>
    ‖(c.map fun x => ∑ i : Fin n, algebraMap ℚ_[l] Ω (v i) * x ^ (i : ℕ)).prod‖
  have hc : ∀ c, Continuous (φ c) := fun c =>
    (continuous_multiset_prod c fun x _ => continuous_finsetSum _ fun i _ =>
      ((continuous_algebraMap ℚ_[l] Ω).comp (continuous_apply i)).mul continuous_const).norm
  have hd : DenseRange (Pi.map (fun (_ : Fin n) => ((↑) : ℚ → ℚ_[l]))) :=
    DenseRange.piMap fun _ => Padic.denseRange_ratCast l
  have heq : φ a = φ b := by
    refine Continuous.ext_on hd (hc a) (hc b) ?_
    rintro _ ⟨v, rfl⟩
    have := rat_case (l := l) a b h (∑ i : Fin n, monomial (i : ℕ) (v i))
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [φ, Polynomial.map_sum, aeval_monomial] using this
  have := congrFun heq fun i => F.coeff i
  have hx : ∀ x : Ω, aeval x F = ∑ i : Fin n, algebraMap ℚ_[l] Ω (F.coeff i) * x ^ (i : ℕ) := by
    intro x
    rw [aeval_eq_sum_range, Finset.sum_range]
    simp only [Algebra.smul_def]
    rfl
  simpa only [hx] using this

end Padic

end ResultantNorm

theorem eq_of_norm_resultant_eq : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ_[l] Ω] [Algebra.IsAlgebraic ℚ_[l] Ω] (a b : Multiset Ω) (P Q : Polynomial ℚ_[l]), P.map (algebraMap ℚ_[l] Ω) = (a.map fun x => Polynomial.X - Polynomial.C x).prod → Q.map (algebraMap ℚ_[l] Ω) = (b.map fun x => Polynomial.X - Polynomial.C x).prod → (∀ (F : Polynomial ℤ) (u v : ℚ_[l]), algebraMap ℚ_[l] Ω u = (a.map fun x => Polynomial.aeval x F).prod → algebraMap ℚ_[l] Ω v = (b.map fun x => Polynomial.aeval x F).prod → ‖u‖ = ‖v‖) → P = Q := by
  intro l _ Ω _ _ _ a b P Q hP hQ h
  classical
  letI : NormedField Ω := spectralNorm.normedField ℚ_[l] Ω
  letI : NormedAlgebra ℚ_[l] Ω := spectralNorm.normedAlgebra ℚ_[l] Ω
  have h1 : ∀ F : Polynomial ℤ, ‖(a.map fun x => Polynomial.aeval x F).prod‖ =
      ‖(b.map fun x => Polynomial.aeval x F).prod‖ := by
    intro F
    obtain ⟨u, hu⟩ := ResultantNorm.exists_prod_aeval a P hP (F.map (algebraMap ℤ ℚ_[l]))
    obtain ⟨v, hv⟩ := ResultantNorm.exists_prod_aeval b Q hQ (F.map (algebraMap ℤ ℚ_[l]))
    simp only [Polynomial.aeval_map_algebraMap] at hu hv
    rw [← hu, ← hv, norm_algebraMap', norm_algebraMap']
    exact h F u v hu hv
  refine ResultantNorm.eq_of_countP _ a b P Q rfl hP hQ fun G => ?_
  have h2 : ∀ t : ℚ_[l],
      ‖(a.map fun x => Polynomial.aeval x G + algebraMap ℚ_[l] Ω t).prod‖ =
      ‖(b.map fun x => Polynomial.aeval x G + algebraMap ℚ_[l] Ω t).prod‖ := by
    intro t
    simpa only [map_add (f := _), Polynomial.aeval_C] using
      ResultantNorm.padic_case (l := l) a b h1 (G + Polynomial.C t)
  exact le_antisymm (ResultantNorm.countP_le b a _ fun t => (h2 t).symm)
    (ResultantNorm.countP_le a b _ h2)

end GlobalTheory
end

