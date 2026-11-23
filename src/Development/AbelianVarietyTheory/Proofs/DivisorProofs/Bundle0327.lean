module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParabolicInductionTrivialPreservesVirtualCharact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyGLHarishChandraRecursio
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct GlobalTheory.ParabVirt
open scoped Classical

noncomputable section
namespace GlobalTheory.ShinPsiRec

variable {F : Type} [Field F]

def low (a n : ℕ) : Submodule F (Fin n → F) where
  carrier := {v | ∀ i : Fin n, a ≤ (i : ℕ) → v i = 0}
  add_mem' := fun {u v} hu hv i hi => by simp [hu i hi, hv i hi]
  zero_mem' := fun i _ => rfl
  smul_mem' := fun c v hv i hi => by simp [hv i hi]

theorem mem_stab_low_iff (a n : ℕ) (x : GL (Fin n) F) : x ∈ stab (low (F := F) a n) ↔ InPar a x := by
  rw [mem_stab]
  constructor
  · intro h i j hj hi
    have hv : (Pi.single j 1 : Fin n → F) ∈ low a n := by
      intro k hk
      have : k ≠ j := by intro e; subst e; omega
      simp [Pi.single_apply, this]
    have := h _ hv i hi
    simpa [Matrix.toLin'_apply, Matrix.mulVec_single_one] using this
  · intro h v hv i hi
    rw [Matrix.toLin'_apply]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : (j : ℕ) < a
    · rw [h i j hj hi, zero_mul]
    · rw [hv j (by omega), mul_zero]

def lowEquiv {a n : ℕ} (ha : a ≤ n) : low (F := F) a n ≃ₗ[F] (Fin a → F) where
  toFun v := fun i => v.1 (Fin.castLE ha i)
  map_add' u v := rfl
  map_smul' c v := rfl
  invFun w := ⟨fun k => if h : (k : ℕ) < a then w ⟨k, h⟩ else 0, fun k hk => dif_neg (by omega)⟩
  left_inv v := by
    ext k
    dsimp only
    split_ifs with h
    · rfl
    · exact (v.2 k (by omega)).symm
  right_inv w := by
    funext i
    simp

theorem resMat_low {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F) (hp : p ∈ stab (low (F := F) a n)) :
    resMat (low a n) (lowEquiv ha) ⟨p, hp⟩ = tl a (p : Matrix (Fin n) (Fin n) F) := by
  ext i j
  have hs : ((lowEquiv (F := F) ha).symm (Pi.single j 1)).1 = Pi.single (Fin.castLE ha j) 1 := by
    funext k
    change (if h : (k : ℕ) < a then (Pi.single j 1 : Fin a → F) ⟨k, h⟩ else 0) = _
    split_ifs with h
    · simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castLE]
    · have : k ≠ Fin.castLE ha j := by
        intro e; rw [e, Fin.val_castLE] at h; exact h j.2
      simp [Pi.single_apply, this]
  simp only [resMat, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.toMatrix'_apply, LinearEquiv.conj_apply_apply]
  change (Matrix.toLin' (p : Matrix (Fin n) (Fin n) F) ((lowEquiv (F := F) ha).symm (Pi.single j 1)).1)
    (Fin.castLE ha i) = _
  rw [hs, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  have hi : (i : ℕ) < n := by omega
  have hj : (j : ℕ) < n := by omega
  simp only [tl, ent, dif_pos (And.intro hi hj), Matrix.transpose_apply]
  rfl

theorem tl_isUnit {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F) (hp : InPar a p) :
    IsUnit (tl a (p : Matrix (Fin n) (Fin n) F)) := by
  have hp' := (mem_stab_low_iff a n p).2 hp
  rw [← resMat_low ha p hp']
  exact IsUnit.map (resMat (low a n) (lowEquiv ha)) (Group.isUnit _)

theorem coe_tlG {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F) (hp : InPar a p) :
    ((tlG a p : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = tl a (p : Matrix (Fin n) (Fin n) F) := by
  unfold tlG toG
  rw [dif_pos (tl_isUnit ha p hp)]
  rfl

theorem psi_restrict_low (S : F[X] → ℂ) {a n : ℕ} (ha : a ≤ n) (p : GL (Fin n) F)
    (hp : p ∈ stab (low (F := F) a n)) :
    psi S (low (F := F) a n) ((Matrix.toLin' (p : Matrix (Fin n) (Fin n) F)).restrict hp) =
      psiG S a (tlG a p) := by
  rw [psiG, coe_tlG ha p ((mem_stab_low_iff a n p).1 hp), ← resMat_low ha p hp]
  simp only [resMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.toLin'_toMatrix']
  rw [psi_conj]

def resPsi (S : F[X] → ℂ) {n : ℕ} (x : GL (Fin n) F) (W : Submodule F (Fin n → F)) : ℂ :=
  if h : x ∈ stab W then psi S W ((Matrix.toLin' (x : Matrix (Fin n) (Fin n) F)).restrict h) else 0

theorem finsum_rank_eq_hc [Finite F] (S : F[X] → ℂ) {a n : ℕ} (ha : a ≤ n) (x : GL (Fin n) F) :
    ∑ᶠ W : {W : Submodule F (Fin n → F) // Module.finrank F W = a}, resPsi S x W.1 =
      hc a (n - a) (psiG S a) (fun _ => 1) n x := by
  classical
  haveI : Finite (Submodule F (Fin n → F)) :=
    Finite.of_injective (fun W : Submodule F (Fin n → F) => (W : Set (Fin n → F))) SetLike.coe_injective
  letI := Fintype.ofFinite (GL (Fin n) F)
  letI := Fintype.ofFinite (Submodule F (Fin n → F))
  set W₀ := low (F := F) a n with hW₀def
  have hW₀ : Module.finrank F W₀ = a := (lowEquiv ha).finrank_eq.trans (Module.finrank_fin_fun F)
  let π : GL (Fin n) F → {W : Submodule F (Fin n → F) // Module.finrank F W = a} := fun t =>
    ⟨W₀.map (lin t).toLinearMap, (LinearEquiv.finrank_map_eq _ _).trans hW₀⟩
  have hs : Function.Surjective π := by
    intro W
    obtain ⟨f⟩ : Nonempty (W₀ ≃ₗ[F] W.1) :=
      FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (hW₀.trans W.2.symm)
    obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
    obtain ⟨t, rfl⟩ := lin_surjective g
    refine ⟨t, Subtype.ext ?_⟩
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v, hv, rfl⟩
      have := (f ⟨v, hv⟩).2
      rw [hg] at this
      exact this
    · exact (π t).2.trans W.2.symm
  have hsum := sum_fibres (stab W₀) π hs
    (fun s t => Subtype.ext_iff.trans (map_eq_map_iff W₀ s t)) (fun W => resPsi S x W.1)
  have hg : ∀ t : GL (Fin n) F, gal (RingHom.id F) n t = t := by
    intro t; ext i j; simp [gal]
  have hterm : ∀ t : GL (Fin n) F, resPsi S x (π t).1 =
      (if InPar a (t⁻¹ * x * gal (RingHom.id F) n t) then
        psiG S a (tlG a (t⁻¹ * x * gal (RingHom.id F) n t)) *
          (fun _ => (1 : ℂ)) (brG a (n - a) (t⁻¹ * x * gal (RingHom.id F) n t)) else 0) := by
    intro t
    rw [hg, mul_one]
    simp only [resPsi, π]
    by_cases h : t⁻¹ * x * t ∈ stab W₀
    · have h' := (conj_mem_stab_iff W₀ x t).1 h
      rw [dif_pos h', if_pos ((mem_stab_low_iff a n _).1 h), ← psi_restrict_low S ha _ h,
        ← psi_conj F S _ _ ((lin t).submoduleMap W₀)]
      congr 1
      refine LinearMap.ext fun v => ?_
      obtain ⟨w, rfl⟩ := ((lin t).submoduleMap W₀).surjective v
      rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
      ext1
      change lin x (lin t w) = lin t (lin (t⁻¹ * x * t) w)
      rw [← lin_mul, ← lin_mul, mul_assoc, mul_inv_cancel_left]
    · rw [dif_neg (fun h' => h ((conj_mem_stab_iff W₀ x t).2 h')),
        if_neg (fun h'' => h ((mem_stab_low_iff a n _).2 h''))]
  have hcard : Nat.card {p : GL (Fin n) F // InPar a p} = Nat.card (stab W₀) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun p => (mem_stab_low_iff a n p).symm)
  have hc0 : (Nat.card (stab W₀) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  simp only [hc, hcTw]
  rw [hcard, ← finsum_congr hterm, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, hsum,
    inv_mul_cancel_left₀ hc0]

end GlobalTheory.ShinPsiRec

namespace GlobalTheory.ShinPsiRec

theorem ne_top_iff_finrank_lt {F : Type} [Field F] {n : ℕ} (W : Submodule F (Fin n → F)) :
    W ≠ ⊤ ↔ Module.finrank F W < n := by
  constructor
  · intro h
    have := Submodule.finrank_lt h
    rwa [Module.finrank_fin_fun] at this
  · intro h htop
    rw [htop, finrank_top, Module.finrank_fin_fun] at h
    exact lt_irrefl _ h

theorem psiG_eq_chG_sub_hc (F : Type) [Field F] [Finite F] (S : F[X] → ℂ) (n : ℕ) (x : GL (Fin n) F) :
    psiG S n x = chG S n x - ∑ a ∈ Finset.range n, hc a (n - a) (psiG S a) (fun _ => 1) n x := by
  classical
  haveI : Finite (Submodule F (Fin n → F)) :=
    Finite.of_injective (fun W : Submodule F (Fin n → F) => (W : Set (Fin n → F))) SetLike.coe_injective
  letI := Fintype.ofFinite (Submodule F (Fin n → F))
  show psi S _ _ = S _ - _
  rw [psi_eq, Matrix.charpoly_toLin']
  congr 1
  rw [Finset.sum_congr rfl fun a ha =>
    (finsum_rank_eq_hc S (le_of_lt (Finset.mem_range.1 ha)) x).symm]
  have step : ∀ a : ℕ, ∑ᶠ W : {W : Submodule F (Fin n → F) // Module.finrank F W = a}, resPsi S x W.1 =
      ∑ W : Submodule F (Fin n → F), if Module.finrank F W = a then resPsi S x W else 0 := by
    intro a
    rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) _).symm
  simp only [step]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq]
  rw [finsum_eq_sum_of_fintype]
  rw [Finset.sum_congr rfl (g := fun W => resPsi S x W.1) fun W _ => by
    unfold resPsi; rw [dif_pos (show x ∈ stab W.1 from W.2.2)]]
  rw [← Finset.sum_subtype (Finset.univ.filter fun W : Submodule F (Fin n → F) => W ≠ ⊤ ∧ ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W)
    (fun W => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (resPsi S x), Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  by_cases hx : ∀ v ∈ W, Matrix.toLin' (x : Matrix (Fin n) (Fin n) F) v ∈ W
  · simp only [Finset.mem_range, ne_top_iff_finrank_lt, and_iff_left hx]
  · have hx' : x ∉ stab W := hx
    simp [resPsi, hx', hx]

end GlobalTheory.ShinPsiRec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.PrimBasic
open Polynomial

def μc (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)

lemma μc_prim (q : ℕ) [NeZero q] : IsPrimitiveRoot (μc q) q :=
  Complex.isPrimitiveRoot_exp q (NeZero.ne q)

lemma aeval_cyc {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    aeval x (cyclotomic n ℤ) = eval x (cyclotomic n R) := by
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]

lemma transfer {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (P : ℤ[X])
    (hP : aeval (μc q) P = 0) : aeval ζ.1 P = 0 := by
  have hμ := μc_prim q
  have h1 : cyclotomic q ℤ = minpoly ℤ (μc q) := cyclotomic_eq_minpoly hμ (NeZero.pos q)
  have hd : cyclotomic q ℤ ∣ P := h1 ▸ minpoly.isIntegrallyClosed_dvd (hμ.isIntegral (NeZero.pos q)) hP
  obtain ⟨Q, rfl⟩ := hd
  rw [map_mul, ζ.2.2, zero_mul]

lemma transfer2 {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (F : (ℤ[X])[X])
    (hF : F.map (aeval (μc q)).toRingHom = 0) : F.map (aeval ζ.1).toRingHom = 0 := by
  ext k
  rw [coeff_map, coeff_zero]
  apply transfer ζ
  have := congrArg (fun G : ℂ[X] => G.coeff k) hF
  simpa [coeff_map] using this

lemma nthRoots_eq (q : ℕ) [NeZero q] :
    nthRootsFinset q (1 : ℂ) = (Finset.range q).image (fun a => μc q ^ a) := by
  have hμ := μc_prim q
  ext z
  rw [mem_nthRootsFinset (NeZero.pos q), Finset.mem_image]
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := hμ.eq_pow_of_pow_eq_one hz
    exact ⟨i, Finset.mem_range.2 hi, rfl⟩
  · rintro ⟨a, -, rfl⟩
    rw [← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]

lemma primRoots_eq (q : ℕ) [NeZero q] :
    primitiveRoots q ℂ = ((Finset.range q).filter (fun a => Nat.Coprime a q)).image (fun a => μc q ^ a) := by
  have hμ := μc_prim q
  ext z
  rw [mem_primitiveRoots (NeZero.pos q), Finset.mem_image]
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := hμ.eq_pow_of_pow_eq_one hz.pow_eq_one
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, (hμ.pow_iff_coprime (NeZero.pos q) i).1 hz⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact hμ.pow_of_coprime a (Finset.mem_filter.1 ha).2

lemma injOn (q : ℕ) [NeZero q] (s : Finset ℕ) (hs : s ⊆ Finset.range q) :
    Set.InjOn (fun a => μc q ^ a) s := by
  intro i hi j hj h
  exact (μc_prim q).pow_inj (Finset.mem_range.1 (hs hi)) (Finset.mem_range.1 (hs hj)) h

lemma C_prod_range (q : ℕ) [NeZero q] :
    ∏ a ∈ Finset.range q, (X - C (μc q ^ a)) = (X ^ q - 1 : ℂ[X]) := by
  rw [X_pow_sub_one_eq_prod (NeZero.pos q) (μc_prim q), nthRoots_eq,
    Finset.prod_image (injOn q _ (subset_refl _))]

lemma C_prod_coprime (q : ℕ) [NeZero q] :
    ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (X - C (μc q ^ a)) = cyclotomic q ℂ := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (μc_prim q), primRoots_eq,
    Finset.prod_image (injOn q _ (Finset.filter_subset _ _))]

lemma C_prod_erase (q : ℕ) [NeZero q] :
    ∏ a ∈ (Finset.range q).erase 0, (X - C (μc q ^ a)) = ∑ i ∈ Finset.range q, (X ^ i : ℂ[X]) := by
  have h0 : 0 ∈ Finset.range q := Finset.mem_range.2 (NeZero.pos q)
  have h := Finset.mul_prod_erase (Finset.range q) (fun a => (X - C (μc q ^ a) : ℂ[X])) h0
  have hne : (X - C (1 : ℂ) : ℂ[X]) ≠ 0 := X_sub_C_ne_zero 1
  apply mul_left_cancel₀ hne
  calc (X - C (1 : ℂ)) * ∏ a ∈ (Finset.range q).erase 0, (X - C (μc q ^ a))
      = ∏ a ∈ Finset.range q, (X - C (μc q ^ a)) := by simpa only [pow_zero] using h
    _ = X ^ q - 1 := C_prod_range q
    _ = (X - C (1 : ℂ)) * ∑ i ∈ Finset.range q, (X ^ i : ℂ[X]) := by
        rw [map_one, mul_comm, geom_sum_mul]

end GlobalTheory.EtC.PrimBasic

namespace GlobalTheory.EtC.PrimBasic
open Polynomial

lemma prim_pow_q {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  have h := transfer ζ (X ^ q - 1) (by simp [(μc_prim q).pow_eq_one])
  simpa [sub_eq_zero] using h

lemma prod_range {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ a ∈ Finset.range q, (X - C (ζ.1 ^ a)) = (X ^ q - 1 : A[X]) := by
  have h := transfer2 ζ (∏ a ∈ Finset.range q, (X - C X ^ a) - (X ^ q - 1 : (ℤ[X])[X])) (by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic]
    simp only [← C_pow]; rw [C_prod_range, sub_self])
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic] at h
  simpa only [← C_pow, sub_eq_zero] using h

lemma prod_coprime {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (X - C (ζ.1 ^ a)) = cyclotomic q A := by
  have h := transfer2 ζ (∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (X - C X ^ a)
      - cyclotomic q (ℤ[X])) (by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic]
    simp only [← C_pow]; rw [C_prod_coprime, sub_self])
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic] at h
  simpa only [← C_pow, sub_eq_zero] using h

lemma prod_erase {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ a ∈ (Finset.range q).erase 0, (1 - ζ.1 ^ a) = (q : A) := by
  have h := transfer2 ζ (∏ a ∈ (Finset.range q).erase 0, (X - C X ^ a) - ∑ i ∈ Finset.range q, (X ^ i : (ℤ[X])[X])) (by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic]
    simp only [← C_pow]; rw [C_prod_erase, sub_self])
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_pow, map_X, map_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X, Polynomial.map_one, map_cyclotomic] at h
  have h2 := congrArg (eval (1 : A)) h
  simp only [eval_sub, eval_prod, eval_finsetSum, eval_X, eval_C, eval_pow, one_pow, eval_zero,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, sub_eq_zero] at h2
  simpa [← C_pow] using h2

end GlobalTheory.EtC.PrimBasic

namespace GlobalTheory.EtC.PrimBasic
open Polynomial

lemma isUnit_one_sub {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (c : ℕ)
    (hc : c % q ≠ 0) : IsUnit (1 - ζ.1 ^ c) := by
  have hmem : c % q ∈ (Finset.range q).erase 0 :=
    Finset.mem_erase.2 ⟨hc, Finset.mem_range.2 (Nat.mod_lt _ (NeZero.pos q))⟩
  have hd : (1 - ζ.1 ^ (c % q)) ∣ (q : A) :=
    (Finset.dvd_prod_of_mem (fun a => 1 - ζ.1 ^ a) hmem).trans (dvd_of_eq (prod_erase ζ))
  rw [pow_eq_pow_mod c (prim_pow_q ζ)]
  exact isUnit_of_dvd_unit hd ζ.2.1

lemma isUnit_val {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : IsUnit ζ.1 := by
  refine isUnit_iff_exists_inv.2 ⟨ζ.1 ^ (q - 1), ?_⟩
  rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos q), prim_pow_q ζ]

lemma isUnit_pow_sub_pow_of_le {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (a b : ℕ)
    (hab : ¬ a ≡ b [MOD q]) (hle : b ≤ a) : IsUnit (ζ.1 ^ a - ζ.1 ^ b) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hd : d % q ≠ 0 := by
    intro h0
    apply hab
    exact (Nat.modEq_iff_dvd' hle).2 (by simpa using Nat.dvd_of_mod_eq_zero h0) |>.symm
  have e : ζ.1 ^ (b + d) - ζ.1 ^ b = -(ζ.1 ^ b * (1 - ζ.1 ^ d)) := by ring
  rw [e]
  exact (((isUnit_val ζ).pow b).mul (isUnit_one_sub ζ d hd)).neg

theorem prim_basic : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], (∀ ζ : Prim q A, ζ.1 ^ q = 1) ∧ (∀ (ζ : Prim q A) (a : ℕ), Nat.Coprime a q → ∃ ξ : Prim q A, ξ.1 = ζ.1 ^ a) ∧ (∀ (ζ : Prim q A) (a b : ℕ), ¬ a ≡ b [MOD q] → IsUnit (ζ.1 ^ a - ζ.1 ^ b)) ∧ (∀ (ζ : Prim q A) (x : A), x ^ q = 1 → ∏ a ∈ Finset.range q, (x - ζ.1 ^ a) = 0) ∧ (∀ (ζ ξ : Prim q A), ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (ξ.1 - ζ.1 ^ a) = 0) ∧ ∀ (r : ℕ), r ∣ q → ∀ ζ : Prim q A, ∃ ξ : Prim r A, ξ.1 = ζ.1 ^ (q / r) := by
  intro q _ A _
  refine ⟨fun ζ => prim_pow_q ζ, ?_, ?_, ?_, ?_, ?_⟩
  · intro ζ a ha
    have h : aeval (ζ.1 ^ a) (cyclotomic q ℤ) = 0 := by
      rw [← aeval_X_pow (R := ℤ), ← aeval_comp]
      apply transfer ζ
      rw [aeval_comp, aeval_X_pow, aeval_cyc]
      exact ((μc_prim q).pow_of_coprime a ha).isRoot_cyclotomic (NeZero.pos q)
    exact ⟨(⟨ζ.1 ^ a, ζ.2.1, h⟩ : {z : A // IsUnit (q : A) ∧ aeval z (cyclotomic q ℤ) = 0}), rfl⟩
  · intro ζ a b hab
    rcases le_total b a with hle | hle
    · exact isUnit_pow_sub_pow_of_le ζ a b hab hle
    · have := isUnit_pow_sub_pow_of_le ζ b a (fun h => hab h.symm) hle
      have e : ζ.1 ^ a - ζ.1 ^ b = -(ζ.1 ^ b - ζ.1 ^ a) := by ring
      rw [e]; exact this.neg
  · intro ζ x hx
    have h := congrArg (eval x) (prod_range ζ)
    simpa [eval_prod, hx] using h
  · intro ζ ξ
    have h := congrArg (eval ξ.1) (prod_coprime ζ)
    rw [← aeval_cyc, ξ.2.2] at h
    simpa [eval_prod] using h
  · intro r hr ζ
    have hq0 : q ≠ 0 := NeZero.ne q
    have hr0 : r ≠ 0 := by rintro rfl; exact hq0 (Nat.eq_zero_of_zero_dvd hr)
    have hk0 : q / r ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hr) (Nat.pos_of_ne_zero hr0)).ne'
    have hunit : IsUnit (r : A) := by
      obtain ⟨k, hk⟩ := hr
      have : IsUnit ((r : A) * k) := by rw [← Nat.cast_mul, ← hk]; exact ζ.2.1
      exact isUnit_of_mul_isUnit_left this
    have h : aeval (ζ.1 ^ (q / r)) (cyclotomic r ℤ) = 0 := by
      rw [← aeval_X_pow (R := ℤ), ← aeval_comp]
      apply transfer ζ
      rw [aeval_comp, aeval_X_pow, aeval_cyc]
      have hp := (μc_prim q).pow_of_dvd hk0 (Nat.div_dvd_of_dvd hr)
      rw [Nat.div_div_self hr hq0] at hp
      exact hp.isRoot_cyclotomic (Nat.pos_of_ne_zero hr0)
    exact ⟨(⟨ζ.1 ^ (q / r), hunit, h⟩ : {z : A // IsUnit (r : A) ∧ aeval z (cyclotomic r ℤ) = 0}), rfl⟩

end GlobalTheory.EtC.PrimBasic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientTransitionSurjectiveSameSubgroup
section
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.QuotTransition

theorem transition_surjective : ∀ (O : Type) [CommRing O] (A₁ : Type) [CommRing A₁] [HopfAlgebra O A₁] [IsCocomm O A₁] [Module.Finite O A₁] [Module.Projective O A₁] (A₂ : Type) [CommRing A₂] [HopfAlgebra O A₂] [IsCocomm O A₂] [Module.Finite O A₂] [Module.Projective O A₂] (B₁ : Type) [CommRing B₁] [HopfAlgebra O B₁] [IsCocomm O B₁] [Module.Finite O B₁] [Module.Projective O B₁] (B₂ : Type) [CommRing B₂] [HopfAlgebra O B₂] [IsCocomm O B₂] [Module.Finite O B₂] [Module.Projective O B₂] (π : A₂ →ₐc[O] A₁) (j₁ : B₁ →ₐc[O] A₁) (j₂ : B₂ →ₐc[O] A₂) (r : B₂ →ₐc[O] B₁) (ρ : A₁ →ₗ[O] B₁), (∀ b, ρ (j₁ b) = b) → (∀ b, j₁ (r b) = π (j₂ b)) → kerIdeal j₁ = Ideal.map (π : A₂ →ₐ[O] A₁) (kerIdeal j₂) → Function.Surjective r := by
  intro O _ A₁ _ _ _ _ _ A₂ _ _ _ _ _ B₁ _ _ _ _ _ B₂ _ _ _ _ _ π j₁ j₂ r ρ hρ hsq hker
  let j₁' : B₁ →ₗ[O] A₁ := (j₁ : B₁ →ₐ[O] A₁).toLinearMap
  let r' : B₂ →ₗ[O] B₁ := (r : B₂ →ₐ[O] B₁).toLinearMap
  have hcomp : j₁' ∘ₗ r' = ((π.comp j₂ : B₂ →ₐc[O] A₁) : B₂ →ₐ[O] A₁).toLinearMap := by
    ext b
    exact hsq b
  have hs : Function.Surjective r' := by
    refine GlobalTheory.surjective_of_fibre_rank O B₂ B₁ r' fun q => ?_
    have hinj : Function.Injective (j₁'.baseChange q.asIdeal.ResidueField) := by
      apply Function.LeftInverse.injective (g := ρ.baseChange q.asIdeal.ResidueField)
      intro x
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have hid : ρ ∘ₗ j₁' = LinearMap.id := LinearMap.ext hρ
      rw [hid, LinearMap.baseChange_id, LinearMap.id_apply]
    have h1 : fibreRank (j₁' ∘ₗ r') q = fibreRank r' q := by
      rw [fibreRank, fibreRank, LinearMap.baseChange_comp, LinearMap.range_comp]
      exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
    have h2 : fibreRank j₁' q = fibreDim B₁ q := LinearMap.finrank_range_of_inj hinj
    have h3 := fibreDim_eq_ker_mul_range (π.comp j₂) q
    have h4 := fibreDim_eq_ker_mul_range j₁ q
    rw [kerIdeal_comp, ← hker, ← hcomp] at h3
    have h5 : fibreDim (A₁ ⧸ kerIdeal j₁) q ≠ 0 := fun h0 =>
      fibreDim_ne_zero (A := A₁) q (by rw [h4, h0, zero_mul])
    have h6 : fibreRank (j₁' ∘ₗ r') q = fibreRank j₁' q :=
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h5) (h3.symm.trans h4)
    have h7 : fibreRank r' q = fibreDim B₁ q := by rw [← h1, h6, h2]
    exact h7
  exact hs

end GlobalTheory.QuotTransition
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceStabilizerTrivial
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem eq_one_of_mem_slice_of_mul_mem_slice (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k) :
    Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1 := by
  rintro ⟨J, hJ, hZ⟩ ⟨J', hJ', hgZ⟩
  have m1 : minor Z J = 1 := by rw [minor, hJ, det_one]
  have m1' : minor (g.val * Z) J' = 1 := by rw [minor, hJ', det_one]
  have e1 : valuation k (g.val.det) * valuation k (minor Z J') = 1 := by
    rw [← map_mul, ← minor_mul, m1', map_one]
  have hg : valuation k (g.val.det) ≤ 1 := by
    have := (hgZ J).1
    rwa [minor_mul, m1, mul_one] at this
  have hZJ' : valuation k (minor Z J') = 1 := by
    refine le_antisymm (hZ J').1 ?_
    calc (1 : ValueGroupWithZero k) = valuation k (g.val.det) * valuation k (minor Z J') := e1.symm
      _ ≤ 1 * valuation k (minor Z J') := mul_le_mul_of_nonneg_right hg zero_le
      _ = valuation k (minor Z J') := one_mul _
  have hg1 : valuation k (g.val.det) = 1 := by rwa [hZJ', mul_one] at e1
  have hJJ : J = J' := by
    rcases lt_trichotomy (idx J') (idx J) with h | h | h
    · exact absurd ((hZ J').2 h) (by rw [hZJ']; exact lt_irrefl _)
    · exact (idx.injective h).symm
    · have := (hgZ J).2 h
      rw [minor_mul, m1, mul_one, hg1] at this
      exact absurd this (lt_irrefl _)
  subst hJJ
  have hsub : (g.val * Z).submatrix id J = g.val * Z.submatrix id J := by
    ext i j; simp [Matrix.mul_apply, submatrix_apply]
  rw [hsub, hJ, Matrix.mul_one] at hJ'
  exact Units.ext hJ'

end GlobalTheory.RankFibreKer
end

