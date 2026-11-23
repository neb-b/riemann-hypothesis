module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingCharacterEqFinrankInte
section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.pair_character_eq_finrank : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W), _root_.GlobalTheory.BI.pair (fun g => algebraMap K L (σ.character g)) (fun g => algebraMap K L (ρ.character g)) = (Module.finrank K (Representation.IntertwiningMap ρ σ) : L) := by
  intro K L _ _ _ _ _ G _ _ V _ _ _ W _ _ _ ρ σ
  classical
  haveI := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have h := congrArg (algebraMap K L)
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ)
  unfold _root_.GlobalTheory.BI.pair
  rw [finsum_eq_sum_of_fintype]
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_mul, map_sum, map_inv₀, map_natCast] using h

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingEqZeroOfDistinctIrredu
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

theorem pair_eq_zero_of_isIrrChar_ne : ∀ (G : Type) [Group G] [Finite G] (a b : G → ℂ),
    IsIrrChar ℂ ℂ a → IsIrrChar ℂ ℂ b → a ≠ b → pair a b = 0 := by
  intro G _ _ a b ha hb hab
  obtain ⟨n, ρ, hρ, ha⟩ := ha
  obtain ⟨m, σ, hσ, hb⟩ := hb
  have := hρ
  have := hσ
  have := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have ha' : a = ρ.character := funext fun g => by simp [ha]
  have hb' : b = σ.character := funext fun g => by simp [hb]
  have hne : ¬ Nonempty (Representation.Equiv σ ρ) := by
    rintro ⟨φ⟩
    exact hab (by rw [ha', hb', Representation.char_iso φ])
  have h := Representation.char_orthonormal ρ σ
  rw [if_neg hne] at h
  unfold pair
  rw [finsum_eq_sum_of_fintype, ha', hb']
  simpa using h
end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClos
section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem pair_self_of_isIrrChar_algClosed (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G]
    (χ : G → L) (h : IsIrrChar L L χ) : pair χ χ = 1 := by
  classical
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : L) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : ρ.IsIrreducible := hρ

  have key := ρ.card_inv_mul_sum_char_mul_char_eq_finrank ρ
  rw [Representation.IsIrreducible.finrank_intertwiningMap_self] at key
  unfold pair
  rw [finsum_eq_sum_of_fintype]
  simp only [hχ, Algebra.algebraMap_self, RingHom.id_apply]
  simpa using key
end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteMonicNatDegree
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

private theorem torus_iff {F : Type} [Field F] [Finite F] (n : ℕ) (α : AlgebraicClosure F) (h0 : α ≠ 0) :
    α ^ (Nat.card F ^ n - 1) = 1 ↔ (minpoly F α).natDegree ∣ n := by
  have hi : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  rw [(minpoly.irreducible hi).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, minpoly.dvd_iff]
  have hq : 0 < Nat.card F ^ n := pow_pos Nat.card_pos _
  simp only [map_sub, map_pow, aeval_X, sub_eq_zero]
  obtain ⟨k, hk⟩ : ∃ k, Nat.card F ^ n = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hq).symm⟩
  rw [hk, Nat.add_sub_cancel, pow_succ]
  constructor
  · intro h; rw [h, one_mul]
  · intro h; exact mul_right_cancel₀ h0 (h.trans (one_mul α).symm)

private theorem finite_monic_natDegree {F : Type} [Field F] [Finite F] (n : ℕ) :
    {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}.Finite := by
  have : Finite (Polynomial.degreeLT F (n + 1)) := Finite.of_equiv _ (degreeLTEquiv F (n + 1)).symm.toEquiv
  have h : (Polynomial.degreeLT F (n + 1) : Set F[X]).Finite := Set.toFinite _
  refine h.subset fun P hP => ?_
  simp only [SetLike.mem_coe, mem_degreeLT]
  exact (degree_le_of_natDegree_le hP.2.1.le).trans_lt (by exact_mod_cast Nat.lt_succ_self n)

private theorem finite_torus {F : Type} [Field F] [Finite F] (n : ℕ) (hn : 0 < n) :
    {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}.Finite := by
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  refine (Polynomial.nthRootsFinset (Nat.card F ^ n - 1) (1 : AlgebraicClosure F)).finite_toSet.subset
    fun α hα => ?_
  exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset (by omega) _).2 hα)

theorem sum_poly_eq_sum_torus : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (n : ℕ), 0 < n → ∀ (c : F[X] → ℂ) (l : ℕ), (∀ P : F[X], P.Monic → P.natDegree = n → (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) → c P = 0) → ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}, c P * star (rootSum θ l P) = ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, ((n / (minpoly F α).natDegree : ℕ) : ℂ) * c (minpoly F α ^ (n / (minpoly F α).natDegree)) * star (θ α ^ l) := by
  intro F _ _ θ n hn c l hc
  classical
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  have hi : ∀ α : AlgebraicClosure F, IsIntegral F α := fun α => Algebra.IsIntegral.isIntegral α
  have hne : ∀ α : AlgebraicClosure F, α ^ (Nat.card F ^ n - 1) = 1 → α ≠ 0 := by
    rintro α h rfl
    rw [zero_pow (by omega)] at h
    exact zero_ne_one h
  rw [finsum_mem_eq_finite_toFinset_sum _ (finite_monic_natDegree n),
    finsum_mem_eq_finite_toFinset_sum _ (finite_torus n hn),
    ← Finset.sum_fiberwise_of_maps_to (s := (finite_torus (F := F) n hn).toFinset) (t := (finite_monic_natDegree (F := F) n).toFinset)
      (g := fun α => minpoly F α ^ (n / (minpoly F α).natDegree))]
  swap
  · intro α hα
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hα ⊢
    have hm := minpoly.monic (hi α)
    refine ⟨hm.pow _, ?_, ?_⟩
    · rw [hm.natDegree_pow, Nat.div_mul_cancel ((torus_iff n α (hne α hα)).1 hα)]
    · rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
      exact pow_ne_zero _ (minpoly.coeff_zero_ne_zero (hi α) (hne α hα))
  refine Finset.sum_congr rfl fun P hP => ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
  obtain ⟨hP, hd, h0⟩ := hP
  by_cases hex : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m
  swap
  · rw [hc P hP hd hex, zero_mul]
    refine (Finset.sum_eq_zero fun α hα => ?_).symm
    rw [(Finset.mem_filter.1 hα).2, hc P hP hd hex, mul_zero, zero_mul]
  obtain ⟨f, m, hf, hirr, hm, rfl⟩ := hex
  rw [hf.natDegree_pow] at hd
  have hdiv : n / f.natDegree = m := by
    rw [← hd, Nat.mul_div_cancel _ hirr.natDegree_pos]
  have hmp : ∀ α : AlgebraicClosure F, aeval α f = 0 → minpoly F α = f := fun α h =>
    (minpoly.eq_of_irreducible_of_monic hirr h hf).symm
  have hfib : Finset.filter (fun α : AlgebraicClosure F => minpoly F α ^ (n / (minpoly F α).natDegree) = f ^ m)
      (finite_torus (F := F) n hn).toFinset = (f.map (algebraMap F (AlgebraicClosure F))).roots.toFinset := by
    ext α
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Multiset.mem_toFinset]
    rw [mem_roots (hf.map _).ne_zero, IsRoot.def, eval_map_algebraMap]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : n / (minpoly F α).natDegree ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd hn ((torus_iff n α (hne α h1)).1 h1)) (minpoly.natDegree_pos (hi α))).ne'
      have h4 := congrArg (aeval α) h2
      rw [map_pow, map_pow, minpoly.aeval, zero_pow h3] at h4
      exact pow_eq_zero_iff hm.ne' |>.1 h4.symm
    · intro h
      have hα : α ≠ 0 := by
        rintro rfl
        apply h0
        rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
        rw [aeval_def, eval₂_at_zero, map_eq_zero] at h
        rw [h, zero_pow hm.ne']
      rw [torus_iff n α hα, hmp α h, hdiv]
      exact ⟨Dvd.intro_left _ hd, rfl⟩
  have hsep : f.Separable := PerfectField.separable_of_irreducible hirr
  have hnd : (f.map (algebraMap F (AlgebraicClosure F))).roots.Nodup := nodup_roots hsep.map
  rw [hfib, rootSum, Polynomial.map_pow, roots_pow, Multiset.map_nsmul, Multiset.sum_nsmul,
    ← Multiset.dedup_eq_self.2 hnd, ← Multiset.toFinset_val, ← Finset.sum_eq_multiset_sum,
    Finset.val_toFinset, Finset.smul_sum, star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Multiset.mem_toFinset, mem_roots (hf.map _).ne_zero, IsRoot.def, eval_map_algebraMap] at hα
  rw [hmp α hα, hdiv, star_nsmul, nsmul_eq_mul]
  ring

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinrankEigenspaceMonomialMatrixLift
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.MonoEigen

def orbProd {K : Type} [CommMonoid K] {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → K)
    (m : ℕ) (j : Fin n) : K :=
  ∏ i ∈ Finset.range m, a ((σ ^ i) j)

def GoodRep {K : Type} [CommMonoid K] {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → K)
    (j : Fin n) : Prop :=
  (∀ m : ℕ, j ≤ (σ ^ m) j) ∧ ∀ m : ℕ, (σ ^ m) j = j → orbProd σ a m j = 1

section
variable {K : Type} [Field K] {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n → K)

lemma orbProd_succ (m : ℕ) (j : Fin n) :
    orbProd σ a (m + 1) j = orbProd σ a m j * a ((σ ^ m) j) := by
  simp [orbProd, Finset.prod_range_succ]

lemma orbProd_add (d m : ℕ) (j : Fin n) :
    orbProd σ a (d + m) j = orbProd σ a d j * orbProd σ a m ((σ ^ d) j) := by
  unfold orbProd
  rw [Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [add_comm, pow_add, Equiv.Perm.mul_apply]

lemma orbProd_eq {j : Fin n} (hj : ∀ m : ℕ, (σ ^ m) j = j → orbProd σ a m j = 1)
    (m m' : ℕ) (h : (σ ^ m) j = (σ ^ m') j) : orbProd σ a m j = orbProd σ a m' j := by
  wlog hle : m ≤ m' generalizing m m'
  · exact (this m' m h.symm (le_of_not_ge hle)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hle
  have hd : (σ ^ d) j = j := by
    rw [add_comm, pow_add, Equiv.Perm.mul_apply] at h
    exact ((σ ^ m).injective h).symm
  rw [orbProd_add, hj d hd, hd, one_mul]

lemma apply_pow {v : Fin n → K} (hv : ∀ j, v (σ j) = a j * v j) (m : ℕ) (j : Fin n) :
    v ((σ ^ m) j) = orbProd σ a m j * v j := by
  induction m with
  | zero => simp [orbProd]
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, hv, ih, orbProd_succ]; ring

lemma exists_back (m : ℕ) (j : Fin n) : ∃ m' : ℕ, (σ ^ m') ((σ ^ m) j) = j := by
  have h : σ.SameCycle ((σ ^ m) j) j := by
    rw [Equiv.Perm.sameCycle_pow_left]
  exact h.exists_nat_pow_eq

lemma exists_rep (i : Fin n) : ∃ j : Fin n, (∀ m : ℕ, j ≤ (σ ^ m) j) ∧ ∃ m : ℕ, (σ ^ m) j = i := by
  classical
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun j => ∃ m : ℕ, (σ ^ m) i = j) id ⟨i, by simpa using ⟨0, by simp⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, id] at hj hmin
  obtain ⟨m, rfl⟩ := hj
  refine ⟨_, fun k => hmin _ ⟨k + m, by rw [pow_add, Equiv.Perm.mul_apply]⟩, exists_back σ m i⟩

lemma exists_vec {s : Fin n} (hs : GoodRep σ a s) :
    ∃ v : Fin n → K, (∀ j, v (σ j) = a j * v j) ∧ v s = 1 ∧
      ∀ t, GoodRep σ a t → t ≠ s → v t = 0 := by
  classical
  let v : Fin n → K := fun i => if h : ∃ m : ℕ, (σ ^ m) s = i then orbProd σ a h.choose s else 0
  have hv : ∀ m : ℕ, v ((σ ^ m) s) = orbProd σ a m s := by
    intro m
    have h : ∃ m' : ℕ, (σ ^ m') s = (σ ^ m) s := ⟨m, rfl⟩
    simp only [v, dif_pos h]
    exact orbProd_eq σ a hs.2 _ _ h.choose_spec
  refine ⟨v, fun j => ?_, by simpa [orbProd] using hv 0, fun t ht hts => ?_⟩
  · by_cases h : ∃ m : ℕ, (σ ^ m) s = j
    · obtain ⟨m, rfl⟩ := h
      rw [← Equiv.Perm.mul_apply, ← pow_succ', hv, hv, orbProd_succ, mul_comm]
    · have h' : ¬ ∃ m : ℕ, (σ ^ m) s = σ j := by
        rintro ⟨m, hm⟩
        obtain ⟨m', hm'⟩ := exists_back σ 1 j
        refine h ⟨m' + m, ?_⟩
        rw [pow_add, Equiv.Perm.mul_apply, hm]
        simpa using hm'
      simp only [v, dif_neg h, dif_neg h', mul_zero]
  · have h' : ¬ ∃ m : ℕ, (σ ^ m) s = t := by
      rintro ⟨m, rfl⟩
      obtain ⟨m', hm'⟩ := exists_back σ m s
      have h1 := ht.1 m'
      rw [hm'] at h1
      exact hts (le_antisymm h1 (hs.1 m))
    simp only [v, dif_neg h']

theorem finrank_eq_card (E : Submodule K (Fin n → K))
    (hE : ∀ v, v ∈ E ↔ ∀ j, v (σ j) = a j * v j) :
    Module.finrank K E = Nat.card {j // GoodRep σ a j} := by
  classical
  let f : E →ₗ[K] ({j // GoodRep σ a j} → K) :=
    (LinearMap.funLeft K K Subtype.val).comp E.subtype
  have hf : ∀ (v : E) s, f v s = v.1 s.1 := fun _ _ => rfl
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v h0
    have hv := (hE _).1 v.2
    ext i
    obtain ⟨j, hj, m, rfl⟩ := exists_rep σ i
    have : v.1 j = 0 := by
      by_cases hg : GoodRep σ a j
      · have := congrFun h0 ⟨j, hg⟩
        simpa [hf] using this
      · have : ¬ ∀ m : ℕ, (σ ^ m) j = j → orbProd σ a m j = 1 := fun h => hg ⟨hj, h⟩
        push_neg at this
        obtain ⟨r, hr, hne⟩ := this
        have h2 := apply_pow σ a hv r j
        rw [hr] at h2
        by_contra h3
        exact hne (mul_right_cancel₀ h3 (by rw [← h2, one_mul]))
    simp [apply_pow σ a hv, this]
  have hsurj : Function.Surjective f := by
    intro w
    choose u hu h1 h0 using fun s : {j // GoodRep σ a j} => exists_vec σ a s.2
    refine ⟨∑ s, w s • ⟨u s, (hE _).2 (hu s)⟩, ?_⟩
    ext t
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply, Finset.sum_eq_single t]
    · simp [hf, h1]
    · intro s _ hst
      simp [hf, h0 s t.1 t.2 (fun h => hst (Subtype.ext h).symm)]
    · simp
  rw [(LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

lemma mem_eigenspace_iff (c : Fin n → K) (μ : K) (hμ : μ ≠ 0) (v : Fin n → K) :
    v ∈ Module.End.eigenspace
      (Matrix.toLin' (Matrix.of fun i j => if i = σ j then c j else 0)) μ ↔
      ∀ j, v (σ j) = (c j * μ⁻¹) * v j := by
  rw [Module.End.mem_eigenspace_iff, funext_iff, ← σ.forall_congr_right]
  refine forall_congr' fun j => ?_
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
    EmbeddingLike.apply_eq_iff_eq, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    field_simp
    linear_combination -h
  · intro h
    rw [h]; field_simp

end

theorem finrank_eigenspace_monomial_lift :
    ∀ (k : Type) [Field k] (θ : k →* ℂ), (∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (c : Fin n → k), (∀ j, c j ≠ 0) → ∀ μ : k, μ ≠ 0 → Module.finrank k (Module.End.eigenspace (Matrix.toLin' (Matrix.of fun i j => if i = σ j then c j else 0)) μ) = Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' (Matrix.of fun i j => if i = σ j then θ (c j) else 0)) (θ μ)) := by
  intro k _ θ hθ n σ c hc μ hμ
  have hmul : θ μ * θ μ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hμ, map_one]
  have hθμ : θ μ ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hinv : (θ μ)⁻¹ = θ μ⁻¹ := inv_eq_of_mul_eq_one_right hmul
  rw [finrank_eq_card σ (fun j => c j * μ⁻¹) _ (mem_eigenspace_iff σ c μ hμ),
    finrank_eq_card σ (fun j => θ (c j) * (θ μ)⁻¹) _
      (mem_eigenspace_iff σ (fun j => θ (c j)) (θ μ) hθμ)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun j => ?_)
  refine and_congr_right fun _ => forall_congr' fun m => imp_congr_right fun _ => ?_
  have h1 : orbProd σ (fun j => θ (c j) * (θ μ)⁻¹) m j
      = θ (orbProd σ (fun j => c j * μ⁻¹) m j) := by
    simp only [orbProd, map_prod, map_mul, hinv]
  have h2 : orbProd σ (fun j => c j * μ⁻¹) m j ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hc _) (inv_ne_zero hμ)
  rw [h1]
  constructor
  · intro h; rw [h, map_one]
  · intro h
    exact hθ _ _ h2 one_ne_zero (by rw [h, map_one])

end GlobalTheory.MonoEigen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumCardCyclicVectorsInvariantSubspaces
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem finsum_card_cyclic_eq (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (g : Module.End F V) :
    ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W},
      (Nat.card {v : W.1 // ∀ U : Submodule F (W.1),
        (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤} : ℂ)
      = (Nat.card F : ℂ) ^ Module.finrank F V := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) :=
    Finite.of_injective (fun W : Submodule F V => (W : Set V)) SetLike.coe_injective
  haveI : Fintype {W : Submodule F V // ∀ x ∈ W, g x ∈ W} := Fintype.ofFinite _
  have key : ∀ (W W' : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}) (v : W.1),
      (∀ U : Submodule F (W.1), (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤) →
      (v : V) ∈ W'.1 → W.1 ≤ W'.1 := by
    intro W W' v hv hv' x hx
    have h := hv (W'.1.comap W.1.subtype) (fun y hy => W'.2 _ hy) hv'
    have : (⟨x, hx⟩ : W.1) ∈ W'.1.comap W.1.subtype := h ▸ Submodule.mem_top
    exact this
  let f : (Σ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, {v : W.1 // ∀ U : Submodule F (W.1),
        (∀ x ∈ U, (g.restrict W.2) x ∈ U) → v ∈ U → U = ⊤}) → V := fun p => (p.2.1 : V)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨W, v, hv⟩ ⟨W', v', hv'⟩ h
      have h' : (v : V) = v' := h
      have hW : W = W' := Subtype.ext (le_antisymm (key W W' v hv (h' ▸ v'.2))
        (key W' W v' hv' (h' ▸ v.2)))
      subst hW
      have : v = v' := Subtype.ext h'
      subst this
      rfl
    · intro v
      let S : Set (Submodule F V) := {U | (∀ x ∈ U, g x ∈ U) ∧ v ∈ U}
      have hinv : ∀ x ∈ sInf S, g x ∈ sInf S := by
        intro x hx
        rw [Submodule.mem_sInf] at hx ⊢
        exact fun p hp => hp.1 x (hx p hp)
      have hv : v ∈ sInf S := by
        rw [Submodule.mem_sInf]
        exact fun p hp => hp.2
      refine ⟨⟨⟨sInf S, hinv⟩, ⟨v, hv⟩, ?_⟩, rfl⟩
      intro U hU hvU
      have hle : sInf S ≤ U.map (sInf S).subtype := by
        refine sInf_le ⟨?_, ⟨_, hvU, rfl⟩⟩
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨_, hU y hy, rfl⟩
      rw [eq_top_iff]
      rintro ⟨x, hx⟩ -
      obtain ⟨y, hy, hyx⟩ := hle hx
      have : y = ⟨x, hx⟩ := Subtype.ext hyx
      exact this ▸ hy
  have hc := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_sigma, Module.natCard_eq_pow_finrank (K := F)] at hc
  rw [finsum_eq_sum_of_fintype]
  exact_mod_cast hc

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IndMulClassFunEqIndMulRestrict
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI

theorem ind_mul_classFun_eq_ind_mul_restrict :
    ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → ℂ) (φ : G → ℂ),
      (∀ g x : G, φ (x⁻¹ * g * x) = φ g) → ind H ψ * φ = ind H (fun h => ψ h * φ h) := by
  intro G _ _ H ψ φ hφ
  funext g
  have key : ∀ x : G, ext0 H (fun h => ψ h * φ h) (x⁻¹ * g * x) = ext0 H ψ (x⁻¹ * g * x) * φ g := by
    intro x
    rw [← hφ g x]
    simp [ext0]
  simp only [Pi.mul_apply, ind]
  simp_rw [key]
  rw [mul_assoc, finsum_mul]

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsAbelianByPrimePowerGroupSubgroup
section
namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.AbByP.subgroup :
    ∀ (G : Type) [Group G] (T : Subgroup G),
      _root_.GlobalTheory.BI.AbByP G → _root_.GlobalTheory.BI.AbByP T := by
  intro G _ T h
  unfold _root_.GlobalTheory.BI.AbByP at h ⊢
  obtain ⟨p, hp, A, hA, hcomm, hpow⟩ := h
  haveI := hA
  refine ⟨p, hp, A.subgroupOf T, Subgroup.normal_subgroupOf, ?_, ?_⟩
  · intro a ha b hb
    exact Subtype.ext (hcomm _ ha _ hb)
  · intro g
    obtain ⟨n, hn⟩ := hpow g
    exact ⟨n, by simpa [Subgroup.mem_subgroupOf] using hn⟩

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.LinearMapShortExactCommuteStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_map_short_exact_commute : ∀ (K : Type) [Field K] (U : Type) [AddCommGroup U] [Module K U] [FiniteDimensional K U] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (i : U →ₗ[K] V) (p : V →ₗ[K] W) (a : U →ₗ[K] U) (b : V →ₗ[K] V) (c : W →ₗ[K] W), Function.Injective i → Function.Surjective p → LinearMap.range i = LinearMap.ker p → b ∘ₗ i = i ∘ₗ a → p ∘ₗ b = c ∘ₗ p → LinearMap.trace K V b = LinearMap.trace K U a + LinearMap.trace K W c := by
  first | exact @GlobalTheory.trace_eq_add_of_shortExact | exact GlobalTheory.trace_eq_add_of_shortExact | (intros; apply GlobalTheory.trace_eq_add_of_shortExact <;> assumption)
end

