module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgEquivMatrixGlueCrt
section
open scoped TensorProduct
open Function

namespace GlobalTheory

noncomputable def crtAlgEquiv (A : Type) [CommRing A] (ι : Type) [Fintype ι] (I : ι → Ideal A)
    (hI : Pairwise (IsCoprime on I)) (hbot : ⨅ i, I i = ⊥) : A ≃ₐ[A] (Π i, A ⧸ I i) :=
  AlgEquiv.ofRingEquiv (f := (RingEquiv.quotientBot A).symm.trans
    ((Ideal.quotEquivOfEq hbot.symm).trans (Ideal.quotientInfRingEquivPiQuotient I hI)))
    (fun x => by ext i; rfl)

theorem matrix_glue_crt : ∀ (A Λ : Type) [CommRing A] [Ring Λ] [Algebra A Λ] (ι : Type) [Fintype ι] (I : ι → Ideal A), Pairwise (IsCoprime on I) → ⨅ i, I i = ⊥ → ∀ (n : ℕ), (∀ i, Nonempty ((A ⧸ I i) ⊗[A] Λ ≃ₐ[A ⧸ I i] Matrix (Fin n) (Fin n) (A ⧸ I i))) → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  intro A Λ _ _ _ ι _ I hI hbot n he
  classical
  let c := crtAlgEquiv A ι I hI hbot
  let e : ∀ i, (A ⧸ I i) ⊗[A] Λ ≃ₐ[A ⧸ I i] Matrix (Fin n) (Fin n) (A ⧸ I i) := fun i => (he i).some
  exact ⟨(Algebra.TensorProduct.rid A A Λ).symm
    |>.trans (Algebra.TensorProduct.congr AlgEquiv.refl c)
    |>.trans (Algebra.TensorProduct.piRight A A Λ (fun i => A ⧸ I i))
    |>.trans (AlgEquiv.piCongrRight (fun i => (Algebra.TensorProduct.comm A Λ (A ⧸ I i)).trans ((e i).restrictScalars A)))
    |>.trans (Matrix.piAlgEquiv A).symm
    |>.trans (AlgEquiv.mapMatrix c.symm)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapEqMk
section
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KummerAlg

open MvPolynomial

variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {q : ℕ}

def rels (φ : (Π _ : Fin q, L) →ₘₗ[B] B) : Set (MvPolynomial L B) :=
  Set.range (fun p : L × L => X (p.1 + p.2) - X p.1 - X p.2) ∪
  Set.range (fun p : B × L => X (p.1 • p.2) - C p.1 * X p.2) ∪
  Set.range (fun ℓ : Fin q → L => ∏ i, X (ℓ i) - C (φ ℓ))

def ideal (φ : (Π _ : Fin q, L) →ₘₗ[B] B) : Ideal (MvPolynomial L B) :=
  Ideal.span (rels φ)

abbrev Alg (φ : (Π _ : Fin q, L) →ₘₗ[B] B) : Type :=
  MvPolynomial L B ⧸ ideal φ

variable (φ : (Π _ : Fin q, L) →ₘₗ[B] B)

theorem algebraMap_eq_mk (c : B) : algebraMap B (Alg φ) c = Ideal.Quotient.mk _ (C c) := rfl

theorem add_mem (a b : L) : X (a + b) - X a - X b ∈ ideal φ :=
  Ideal.subset_span (Or.inl (Or.inl ⟨(a, b), rfl⟩))

theorem smul_mem (c : B) (a : L) : X (c • a) - C c * X a ∈ ideal φ :=
  Ideal.subset_span (Or.inl (Or.inr ⟨(c, a), rfl⟩))

theorem prod_mem (ℓ : Fin q → L) : ∏ i, X (ℓ i) - C (φ ℓ) ∈ ideal φ :=
  Ideal.subset_span (Or.inr ⟨ℓ, rfl⟩)

def gen : L →ₗ[B] Alg φ where
  toFun ℓ := Ideal.Quotient.mk _ (X ℓ)
  map_add' a b := by
    rw [← sub_eq_zero, sub_add_eq_sub_sub, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact add_mem φ a b
  map_smul' c a := by
    rw [← sub_eq_zero, RingHom.id_apply, Algebra.smul_def, algebraMap_eq_mk,
      ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact smul_mem φ c a

theorem gen_apply (ℓ : L) : gen φ ℓ = Ideal.Quotient.mk _ (X ℓ) := rfl

theorem prod_gen (ℓ : Fin q → L) : ∏ i, gen φ (ℓ i) = algebraMap B (Alg φ) (φ ℓ) := by
  rw [← sub_eq_zero]
  simp only [gen_apply, ← map_prod, algebraMap_eq_mk]
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact prod_mem φ ℓ

def scalePoly (t : B) : MvPolynomial L B →ₐ[B] MvPolynomial L B := aeval fun ℓ => C t * X ℓ

theorem scalePoly_X (t : B) (ℓ : L) : scalePoly t (X ℓ) = C t * X ℓ := by simp [scalePoly]

theorem scalePoly_C (t c : B) : scalePoly (L := L) t (C c) = C c := by
  simp [scalePoly, aeval_C, MvPolynomial.algebraMap_eq]

theorem le_comap_scale (t : B) (ht : t ^ q = 1) : ideal φ ≤ (ideal φ).comap (scalePoly t) := by
  rw [ideal, Ideal.span_le]
  rintro r ((⟨⟨a, b⟩, rfl⟩ | ⟨⟨c, a⟩, rfl⟩) | ⟨ℓ, rfl⟩)
  · change scalePoly t _ ∈ ideal φ
    have : scalePoly t (X (a + b) - X a - X b) = C t * (X (a + b) - X a - X b) := by
      simp only [map_sub, scalePoly_X]; ring
    rw [this]; exact Ideal.mul_mem_left _ _ (add_mem φ a b)
  · change scalePoly t _ ∈ ideal φ
    have : scalePoly t (X (c • a) - C c * X a) = C t * (X (c • a) - C c * X a) := by
      simp only [map_sub, map_mul, scalePoly_X, scalePoly_C]; ring
    rw [this]; exact Ideal.mul_mem_left _ _ (smul_mem φ c a)
  · change scalePoly t _ ∈ ideal φ
    have : scalePoly t (∏ i, X (ℓ i) - C (φ ℓ)) = ∏ i, X (ℓ i) - C (φ ℓ) := by
      simp only [map_sub, map_prod, scalePoly_X, scalePoly_C, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← map_pow, ht, map_one, one_mul]
    rw [this]; exact prod_mem φ ℓ

def scale (t : B) (ht : t ^ q = 1) : Alg φ →ₐ[B] Alg φ :=
  Ideal.quotientMapₐ (ideal φ) (scalePoly t) (le_comap_scale φ t ht)

theorem scale_mk (t : B) (ht : t ^ q = 1) (p : MvPolynomial L B) :
    scale φ t ht (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (scalePoly t p) := rfl

theorem scale_gen (t : B) (ht : t ^ q = 1) (ℓ : L) : scale φ t ht (gen φ ℓ) = t • gen φ ℓ := by
  rw [gen_apply, scale_mk, scalePoly_X, map_mul, Algebra.smul_def, algebraMap_eq_mk]

theorem scale_ext {f g : Alg φ →ₐ[B] Alg φ} (h : ∀ ℓ, f (gen φ ℓ) = g (gen φ ℓ)) : f = g :=
  Ideal.Quotient.algHom_ext B (MvPolynomial.algHom_ext fun ℓ => h ℓ)

theorem scale_comp (s t : B) (hs : s ^ q = 1) (ht : t ^ q = 1) :
    (scale φ s hs).comp (scale φ t ht) = scale φ (s * t) (by rw [mul_pow, hs, ht, one_mul]) :=
  scale_ext φ fun ℓ => by
    rw [AlgHom.comp_apply, scale_gen, map_smul, scale_gen, scale_gen, smul_smul, mul_comm]

theorem scale_eq_id (t : B) (ht : t ^ q = 1) (h1 : t = 1) : scale φ t ht = AlgHom.id B (Alg φ) :=
  scale_ext φ fun ℓ => by rw [scale_gen, h1, one_smul, AlgHom.id_apply]

theorem scale_congr (s t : B) (hs : s ^ q = 1) (ht : t ^ q = 1) (h : s = t) :
    scale φ s hs = scale φ t ht := by subst h; rfl

def tw (ζ : B) (g : ZMod q) : B := ζ ^ g.val

theorem tw_add [NeZero q] {ζ : B} (hζ : ζ ^ q = 1) (g h : ZMod q) :
    tw ζ (g + h) = tw ζ g * tw ζ h := by
  rw [tw, tw, tw, ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (g.val + h.val) q, pow_add, pow_mul, hζ, one_pow, mul_one]

theorem tw_pow {ζ : B} (hζ : ζ ^ q = 1) (g : ZMod q) : tw ζ g ^ q = 1 := by
  rw [tw, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem tw_zero (ζ : B) : tw ζ (0 : ZMod q) = 1 := by simp [tw]

theorem tw_mul_tw_neg [NeZero q] {ζ : B} (hζ : ζ ^ q = 1) (g : ZMod q) :
    tw ζ g * tw ζ (-g) = 1 := by rw [← tw_add hζ, add_neg_cancel, tw_zero]

def act [NeZero q] (ζ : B) (hζ : ζ ^ q = 1) : Multiplicative (ZMod q) →* (Alg φ ≃ₐ[B] Alg φ) where
  toFun g := AlgEquiv.ofAlgHom (scale φ (tw ζ g.toAdd) (tw_pow hζ _))
    (scale φ (tw ζ (-g.toAdd)) (tw_pow hζ _))
    (by rw [scale_comp]; exact scale_eq_id φ _ _ (tw_mul_tw_neg hζ _))
    (by rw [scale_comp]; exact scale_eq_id φ _ _ (by rw [mul_comm]; exact tw_mul_tw_neg hζ _))
  map_one' := AlgEquiv.ext fun x => by
    change scale φ (tw ζ (0 : ZMod q)) (tw_pow hζ 0) x = x
    rw [scale_eq_id φ _ _ (tw_zero ζ)]; rfl
  map_mul' g h := AlgEquiv.ext fun x => by
    change scale φ (tw ζ (g.toAdd + h.toAdd)) (tw_pow hζ _) x =
      scale φ (tw ζ g.toAdd) (tw_pow hζ _) (scale φ (tw ζ h.toAdd) (tw_pow hζ _) x)
    rw [← AlgHom.comp_apply, scale_comp]
    exact DFunLike.congr_fun (scale_congr φ _ _ _ _ (tw_add hζ _ _)) x

theorem act_gen [NeZero q] (ζ : B) (hζ : ζ ^ q = 1) (g : ZMod q) (ℓ : L) :
    act φ ζ hζ (Multiplicative.ofAdd g) (gen φ ℓ) = ζ ^ g.val • gen φ ℓ :=
  scale_gen φ _ (tw_pow hζ _) ℓ

end GlobalTheory.KummerAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapNormMemSpan
section
open Polynomial

namespace GlobalTheory.PicDiv.SquarefreeFibre

theorem algebraMap_norm_mem_span {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (g : S) :
    algebraMap R S (Algebra.norm R g) ∈ Ideal.span {g} := by
  set p := LinearMap.charpoly (Algebra.lmul R S g) with hp
  have h1 : aeval g p = 0 := by
    have h2 := congrArg (fun φ : Module.End R S => φ 1) (LinearMap.aeval_self_charpoly (Algebra.lmul R S g))
    rw [← hp, Polynomial.aeval_algHom_apply (Algebra.lmul R S) g p] at h2
    simpa using h2
  have h3 : algebraMap R S (p.coeff 0) = -(g * aeval g p.divX) := by
    have h4 := X_mul_divX_add p
    rw [← h4] at h1
    simp only [map_add (f := _), map_mul, aeval_X, aeval_C] at h1
    linear_combination h1
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, map_mul, ← hp, h3]
  exact Ideal.mul_mem_left _ _ ((Ideal.span {g}).neg_mem
    (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g)))

theorem main : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A], (∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → algebraMap k[X] A (X - C α) ∉ Q ^ 2) → ∀ (g : A) (s : ℕ), g ≠ 0 → ∃ (q : k[X]) (r : ℕ) (Q : Fin r → Ideal A), q.Monic ∧ q.natDegree = s ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, g ∉ Q i) ∧ Ideal.span {algebraMap k[X] A q} = ∏ i, Q i := by
  intro k A _ _ _ _ _ _ _ _ _ hred g s hg
  classical
  obtain ⟨δ, hδ0, hδ⟩ := hred
  set u := algebraMap k[X] A with hu
  set N := Algebra.norm k[X] g with hNdef
  have hN : N ≠ 0 := Algebra.norm_ne_zero_iff.mpr hg
  have hinj : Function.Injective u := FaithfulSMul.algebraMap_injective k[X] A
  have huC : ∀ c : k, u (C c) = algebraMap k A c := by
    intro c
    rw [IsScalarTower.algebraMap_apply k k[X] A c, Polynomial.algebraMap_eq]

  have hCnot : ∀ (P : Ideal A), P.IsPrime → ∀ c : k, c ≠ 0 → u (C c) ∉ P := by
    intro P hP c hc hmem
    rw [huC] at hmem
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit hc).map (algebraMap k A)))

  have hgnot : ∀ (P : Ideal A), P.IsPrime → ∀ α : k, N.eval α ≠ 0 → u (X - C α) ∈ P → g ∉ P := by
    intro P hP α hα hX hgP
    have hNP : u N ∈ P := (Ideal.span_singleton_le_iff_mem P).mpr hgP (algebraMap_norm_mem_span g)
    have hdec := modByMonic_add_div N (X - C α)
    rw [modByMonic_X_sub_C_eq_C_eval] at hdec
    have h5 : C (N.eval α) = N - (X - C α) * (N /ₘ (X - C α)) := eq_sub_of_add_eq hdec
    have : u (C (N.eval α)) = u N - u (X - C α) * u (N /ₘ (X - C α)) := by
      rw [h5, map_sub, map_mul]
    exact hCnot P hP _ hα (this ▸ P.sub_mem hNP (P.mul_mem_right _ hX))

  have hδN : δ * N ≠ 0 := mul_ne_zero hδ0 hN
  have hfin : {a : k | (δ * N).eval a = 0}.Finite :=
    ((δ * N).roots.toFinset.finite_toSet).subset (fun a ha => by
      simp only [Set.mem_setOf_eq] at ha
      simp [Polynomial.mem_roots hδN, ha])
  have hinf : {a : k | (δ * N).eval a ≠ 0}.Infinite := by
    have := hfin.infinite_compl
    simpa [Set.compl_setOf] using this
  obtain ⟨F, hFS, hFcard⟩ := hinf.exists_subset_card_eq s
  have hF : ∀ a ∈ F, δ.eval a ≠ 0 ∧ N.eval a ≠ 0 := by
    intro a ha
    have := hFS ha
    simp only [Set.mem_setOf_eq, eval_mul] at this
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  set q : k[X] := ∏ a ∈ F, (X - C a) with hq
  have hqm : q.Monic := monic_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hqdeg : q.natDegree = s := by
    rw [hq, natDegree_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)]
    simp [hFcard]

  have hone : ∀ (P : Ideal A), P.IsPrime → u q ∈ P → ∃ a ∈ F, u (X - C a) ∈ P := by
    intro P hP hqP
    rw [hq, map_prod] at hqP
    exact Ideal.IsPrime.prod_mem_iff.mp hqP
  have huniq : ∀ (P : Ideal A), P.IsPrime → ∀ a b : k, u (X - C a) ∈ P → u (X - C b) ∈ P → a = b := by
    intro P hP a b ha hb
    by_contra hab
    have : u (C (b - a)) = u (X - C a) - u (X - C b) := by
      rw [← map_sub]; congr 1; simp [C_sub]
    exact hCnot P hP (b - a) (sub_ne_zero.mpr (Ne.symm hab)) (this ▸ P.sub_mem ha hb)
  have hnotsq : ∀ (P : Ideal A), P.IsMaximal → u q ∉ P ^ 2 := by
    intro P hPm hq2
    have hP : P.IsPrime := hPm.isPrime
    obtain ⟨a, haF, haP⟩ := hone P hP (Ideal.pow_le_self two_ne_zero hq2)
    have hsplit : q = (∏ b ∈ F.erase a, (X - C b)) * (X - C a) := by
      rw [hq, mul_comm, Finset.mul_prod_erase F (fun b => X - C b) haF]
    rw [hsplit, map_mul] at hq2
    rcases Ideal.IsPrime.mul_mem_pow P hq2 with hrest | hX2
    · rw [map_prod] at hrest
      obtain ⟨b, hbF, hbP⟩ := Ideal.IsPrime.prod_mem_iff.mp hrest
      exact (Finset.ne_of_mem_erase hbF) (huniq P hP b a hbP haP)
    · exact hδ a (hF a haF).1 P hPm hX2

  set I : Ideal A := Ideal.span {u q} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact fun h => hqm.ne_zero (hinj (h.trans (map_zero u).symm))
  have hsq : Squarefree I := by
    intro J hJ
    by_contra hJu
    have hJtop : J ≠ ⊤ := fun h => hJu (Ideal.isUnit_iff.mpr h)
    obtain ⟨P, hPm, hJP⟩ := Ideal.exists_le_maximal J hJtop
    have hle : I ≤ P ^ 2 := (Ideal.le_of_dvd hJ).trans (by rw [pow_two]; exact Ideal.mul_mono hJP hJP)
    exact hnotsq P hPm (hle (Ideal.mem_span_singleton_self _))
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  set M := UniqueFactorizationMonoid.normalizedFactors I with hM
  have hmem : ∀ P ∈ M, P.IsMaximal ∧ g ∉ P := by
    intro P hPM
    have hPp : P.IsPrime := Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor P hPM)
    have hPne : P ≠ ⊥ := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hPM
    refine ⟨hPp.isMaximal hPne, ?_⟩
    have hqP : u q ∈ P := Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hPM)
      (Ideal.mem_span_singleton_self _)
    obtain ⟨a, haF, haP⟩ := hone P hPp hqP
    exact hgnot P hPp a (hF a haF).2 haP
  let e := M.toFinset.equivFin
  refine ⟨q, M.toFinset.card, fun i => (e.symm i : Ideal A), hqm, hqdeg, ?_, ?_, ?_, ?_⟩
  · intro i; exact (hmem _ (Multiset.mem_toFinset.mp (e.symm i).2)).1
  · intro i j h; exact e.symm.injective (Subtype.ext h)
  · intro i; exact (hmem _ (Multiset.mem_toFinset.mp (e.symm i).2)).2
  · rw [Fintype.prod_equiv e.symm (fun i => (e.symm i : Ideal A)) (fun x => (x : Ideal A)) (fun _ => rfl),
      Finset.prod_coe_sort M.toFinset (fun x => x), Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      hnodup.dedup, Multiset.map_id', hM, ← hI]
    exact (Ideal.prod_normalizedFactors_eq_self hI0).symm

end GlobalTheory.PicDiv.SquarefreeFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQuotBijective
section
open Polynomial

namespace GlobalTheory
namespace DedekindCodimG

variable {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

end DedekindCodimG
end GlobalTheory

namespace GlobalTheory
namespace DedekindCodimG

variable {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

private theorem isArtinianRing_quotient_of_ne_bot_of_isDedekindDomain (A : Type) [CommRing A] [IsDedekindDomain A]
    (I : Ideal A) (hI : I ≠ ⊥) : IsArtinianRing (A ⧸ I) := by
  have : Ring.KrullDimLE 0 (A ⧸ I) := by
    refine Ring.KrullDimLE.mk₀ fun Q hQ => ?_
    have hle : I ≤ Q.comap (Ideal.Quotient.mk I) := fun a ha => by
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha, Q.zero_mem]
    have hne : Q.comap (Ideal.Quotient.mk I) ≠ ⊥ := fun h => hI (le_bot_iff.mp (h ▸ hle))
    have hmax := (Ideal.IsPrime.comap (Ideal.Quotient.mk I) (hK := hQ)).isMaximal hne
    have := hmax.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using hle)
    rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at this
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

private theorem module_finite_quotient_of_ne_bot_of_isDedekindDomain (k A : Type) [Field k] [CommRing A] [IsDedekindDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (I : Ideal A) (hI : I ≠ ⊥) :
    Module.Finite k (A ⧸ I) := by
  haveI := isArtinianRing_quotient_of_ne_bot_of_isDedekindDomain A I hI
  exact Module.finite_of_isArtinianRing k (A ⧸ I)

private theorem algebraMap_quotient_bijective_of_isMaximal_of_isAlgClosed (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (P : Ideal A) [P.IsMaximal] :
    Function.Bijective (algebraMap k (A ⧸ P)) := by
  letI := Ideal.Quotient.field P
  haveI : Module.Finite k (A ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ P)
  exact ⟨(algebraMap k (A ⧸ P)).injective, IsSepClosed.algebraMap_surjective k (A ⧸ P)⟩

private theorem mul_sup_span_singleton_eq_of_mem_of_not_mem_mul (A : Type) [CommRing A] [IsDedekindDomain A]
    (I P : Ideal A) (hI : I ≠ ⊥) (hP : P.IsMaximal) (hP0 : P ≠ ⊥) {x : A} (hxI : x ∈ I)
    (hxIP : x ∉ I * P) : I * P ⊔ Ideal.span {x} = I := by
  have hle : I * P ⊔ Ideal.span {x} ≤ I :=
    sup_le (Ideal.mul_le_inf.trans inf_le_left) ((Ideal.span_singleton_le_iff_mem I).mpr hxI)
  obtain ⟨M, hM⟩ := Ideal.dvd_iff_le.mpr hle
  have hMP : M ∣ P := by
    have : I * M ∣ I * P := Ideal.dvd_iff_le.mpr (hM ▸ le_sup_left)
    exact (mul_dvd_mul_iff_left hI).mp this
  obtain ⟨N, hN⟩ := hMP
  rcases (Ideal.prime_of_isPrime hP0 hP.isPrime).irreducible.isUnit_or_isUnit hN with hu | hu
  · rw [hM, Ideal.isUnit_iff.mp hu, Ideal.mul_top]
  · rw [Ideal.isUnit_iff.mp hu, Ideal.mul_top] at hN
    subst hN
    refine absurd ?_ hxIP
    rw [← hM]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)

private theorem exists_sub_algebraMap_mem_of_isMaximal_of_isAlgClosed (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (P : Ideal A) [P.IsMaximal] (r : A) :
    ∃ c : k, r - algebraMap k A c ∈ P := by
  obtain ⟨c, hc⟩ := (algebraMap_quotient_bijective_of_isMaximal_of_isAlgClosed k A P).2 (Ideal.Quotient.mk P r)
  refine ⟨c, Ideal.Quotient.eq.mp ?_⟩
  rw [Ideal.Quotient.mk_algebraMap, hc]

private theorem finrank_quotient_mul_maximal_eq_finrank_add_one (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (I P : Ideal A)
    (hI : I ≠ ⊥) (hP : P.IsMaximal) (hP0 : P ≠ ⊥) :
    Module.finrank k (A ⧸ I * P) = Module.finrank k (A ⧸ I) + 1 := by
  haveI := hP
  haveI := module_finite_quotient_of_ne_bot_of_isDedekindDomain k A (I * P) (mul_ne_zero hI hP0)
  haveI := module_finite_quotient_of_ne_bot_of_isDedekindDomain k A I hI
  obtain ⟨x, hxI, hxIP⟩ : ∃ x ∈ I, x ∉ I * P := by
    by_contra! h
    have hIP : I * P = I * ⊤ := by
      rw [Ideal.mul_top]
      exact le_antisymm (Ideal.mul_le_inf.trans inf_le_left) fun y hy => h y hy
    exact hP.ne_top (mul_left_cancel₀ hI hIP)
  let f : (A ⧸ I * P) →ₗ[k] (A ⧸ I) :=
    (Ideal.Quotient.factorₐ k (Ideal.mul_le_inf.trans inf_le_left : I * P ≤ I)).toLinearMap
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hker : LinearMap.ker f = k ∙ Ideal.Quotient.mk (I * P) x := by
    apply le_antisymm
    · intro z hz
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      have haI : a ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hz)
      rw [← mul_sup_span_singleton_eq_of_mem_of_not_mem_mul A I P hI hP hP0 hxI hxIP] at haI
      obtain ⟨b, hb, y, hy, rfl⟩ := Submodule.mem_sup.mp haI
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_of_isMaximal_of_isAlgClosed k A P r
      refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
      rw [← Ideal.Quotient.mkₐ_eq_mk k, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq,
        Algebra.smul_def]
      have h1 : x * (r - algebraMap k A c) ∈ I * P := Ideal.mul_mem_mul hxI hc
      have h2 : algebraMap k A c * x - (b + r * x) = -(b + x * (r - algebraMap k A c)) := by ring
      rw [h2]
      exact (I * P).neg_mem ((I * P).add_mem hb h1)
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hxI
  have hx0 : Ideal.Quotient.mk (I * P) x ≠ 0 := fun h => hxIP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, finrank_span_singleton hx0] at h
  exact h.symm

theorem _root_.GlobalTheory.DedekindCodimG.dedekind_finiteType_codim (k A : Type) [Field k]
    [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    (∀ (I : Ideal A), I ≠ ⊥ → Module.Finite k (A ⧸ I)) ∧
    (∀ (P : Ideal A), P.IsMaximal →
      Module.finrank k (A ⧸ P) = (1 : ℕ) ∧ ∃ (φ : A →ₐ[k] k), ∀ (u : A), u ∈ P ↔ (φ : A → k) u = (0 : k)) ∧
    (∀ (I J : Ideal A), I ≠ ⊥ → J ≠ ⊥ →
      Module.finrank k (A ⧸ I * J) = Module.finrank k (A ⧸ I) + Module.finrank k (A ⧸ J)) ∧
    ∀ (I J : Ideal A), I ≠ ⊥ → I ≤ J → Module.finrank k (A ⧸ I) ≤ Module.finrank k (A ⧸ J) →
      I = J := by
  refine ⟨fun I hI => module_finite_quotient_of_ne_bot_of_isDedekindDomain k A I hI, ?_, ?_, ?_⟩
  · intro P hP
    haveI := hP
    let e : k ≃ₐ[k] A ⧸ P :=
      AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ P)) (algebraMap_quotient_bijective_of_isMaximal_of_isAlgClosed k A P)
    refine ⟨by rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self],
      e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k P), fun u => ?_⟩
    change u ∈ P ↔ e.symm (Ideal.Quotient.mk P u) = 0
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  · intro I J hI hJ
    induction J using UniqueFactorizationMonoid.induction_on_prime generalizing I with
    | h₁ => exact absurd rfl hJ
    | h₂ u hu =>
      rw [Ideal.isUnit_iff.mp hu, Ideal.mul_top]
      haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      rw [Module.finrank_zero_of_subsingleton (M := A ⧸ (⊤ : Ideal A)), add_zero]
    | h₃ a p ha hp ih =>
      have hp0 : p ≠ ⊥ := hp.ne_zero
      have hpmax : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp0
      have ha' : a ≠ ⊥ := ha
      rw [show I * (p * a) = I * a * p by ring, mul_comm p a,
        finrank_quotient_mul_maximal_eq_finrank_add_one k A (I * a) p (mul_ne_zero hI ha') hpmax hp0,
        finrank_quotient_mul_maximal_eq_finrank_add_one k A a p ha' hpmax hp0, ih I hI ha']
      ring
  · intro I J hI hIJ hle
    have hJ : J ≠ ⊥ := fun h => hI (le_bot_iff.mp (h ▸ hIJ))
    haveI := module_finite_quotient_of_ne_bot_of_isDedekindDomain k A I hI
    haveI := module_finite_quotient_of_ne_bot_of_isDedekindDomain k A J hJ
    let f : (A ⧸ I) →ₗ[k] (A ⧸ J) := (Ideal.Quotient.factorₐ k hIJ).toLinearMap
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Ideal.Quotient.mk _ a, rfl⟩
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
    have hker : LinearMap.ker f = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    refine le_antisymm hIJ fun a ha => ?_
    have hmem : Ideal.Quotient.mk I a ∈ LinearMap.ker f :=
      LinearMap.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
    rw [hker, Submodule.mem_bot] at hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmem

end DedekindCodimG
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BandMono
section
universe u_1 u_2

namespace GlobalTheory.BandMonotonicity

theorem band_mono :
    (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop :=
      @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦
        ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k));
    ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ}
      {i j : ℕ} {X : Matrix ι ι k}, d1 ℓ j X → i ≤ j → d1 ℓ i X) := by
  intro d1 k _ ι _ _ ℓ i j X h hij r s hrs
  exact h r s (by omega)

end GlobalTheory.BandMonotonicity
end

