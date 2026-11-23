module

public import Development.EtaleCohomology.DivisorCycles.Bundle0001

@[expose] public section

-- bundled from Development.EtaleCohomology.DivisorCycles.TangentDegree
section
open Matrix

namespace LateralTheory.DivDb.TangentDegree
open LateralTheory.DivDb

variable {C : Type} [Field C]

lemma aeval_self_eq_ev {N : ℕ} (x : Mat C N) (f : MP C N) :
    MvPolynomial.aeval (fun p : Fin N × Fin N => x p.1 p.2) f = ev x f := rfl

noncomputable def U {N : ℕ} (Y : Mat C N) : Matrix (Fin N) (Fin N) (PowerSeries C) :=
  fun i j => PowerSeries.mk fun k => ((k.factorial : C)⁻¹ • Y ^ k) i j

noncomputable def Z {N : ℕ} (Y : Mat C N) : Matrix (Fin N) (Fin N) (PowerSeries C) :=
  fun i j => PowerSeries.mk fun k => (((k + 1).factorial : C)⁻¹ • Y ^ (k + 1)) i j

lemma U_eq {N : ℕ} (Y : Mat C N) : U Y = 1 + (PowerSeries.X : PowerSeries C) • Z Y := by
  ext i j k
  rcases k with _ | k
  · simp only [U, Z, PowerSeries.coeff_mk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _),
      PowerSeries.coeff_zero_X_mul, add_zero, Matrix.one_apply, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one]
    split_ifs <;> simp
  · simp only [U, Z, PowerSeries.coeff_mk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _),
      PowerSeries.coeff_succ_X_mul, Matrix.one_apply]
    split_ifs <;> simp

lemma constantCoeff_Z {N : ℕ} (Y : Mat C N) (i j : Fin N) : PowerSeries.constantCoeff (Z Y i j) = Y i j := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [Z, PowerSeries.coeff_mk]

lemma map_aeval_ring {R S σ : Type} [CommRing R] [CommRing S] [Algebra C R] [Algebra C S] (k : R →+* S)
    (hk : k.comp (algebraMap C R) = algebraMap C S) (x : σ → R) (f : MvPolynomial σ C) :
    k (MvPolynomial.aeval x f) = MvPolynomial.aeval (k ∘ x) f := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, hk]

lemma van_of (hD : DegPoly) {N n : ℕ} (S : Submonoid (Mat C N)) (hS : ∀ x ∈ S, Deg n x) :
    ∃ 𝓕 : Set (MP C N), (∀ (F : Type) [Field F] [Algebra C F] (x : Mat F N),
      Deg n x ↔ ∀ f ∈ 𝓕, MvPolynomial.aeval (fun p : Fin N × Fin N => x p.1 p.2) f = 0) ∧
      ∀ f ∈ 𝓕, f ∈ Van (S : Set (Mat C N)) := by
  obtain ⟨𝓕, h𝓕⟩ := hD C N n
  refine ⟨𝓕, h𝓕, fun f hf x hx => ?_⟩
  rw [← aeval_self_eq_ev]
  exact (h𝓕 C x).1 (hS x hx) f hf

lemma tan_deg (hE : ExpVan) (hD : DegPoly) [CharZero C] {N n : ℕ} (S : Submonoid (Mat C N))
    (hS : ∀ x ∈ S, Deg n x) (Y : Mat C N) (hY : Y ∈ Tan (S : Set (Mat C N))) : Deg n Y := by
  obtain ⟨𝓕, h𝓕, hvan⟩ := van_of hD S hS
  let F := FractionRing (PowerSeries C)
  let ι : PowerSeries C →+* F := algebraMap (PowerSeries C) F
  let alg : Algebra C F := (ι.comp (algebraMap C (PowerSeries C))).toAlgebra
  have hιinj : Function.Injective ι := IsFractionRing.injective (PowerSeries C) F
  have hmap : ∀ (M : Matrix (Fin N) (Fin N) (PowerSeries C)) (f : MP C N),
      @MvPolynomial.aeval C F _ _ _ alg (fun p : Fin N × Fin N => (M.map ι) p.1 p.2) f
        = ι (MvPolynomial.aeval (fun p : Fin N × Fin N => M p.1 p.2) f) := by
    intro M f
    rw [map_aeval_ring (S := F) ι rfl]
    rfl
  have hUF : Deg n ((U Y).map ι) := by
    refine (@h𝓕 F _ alg ((U Y).map ι)).2 fun f hf => ?_
    rw [hmap]
    have := hE C N S Y hY f (hvan f hf)
    simp only [U] at this ⊢
    rw [this, map_zero]
  set s : F := ι PowerSeries.X with hsdef
  have hs : s ≠ 0 := (map_ne_zero_iff ι hιinj).2 PowerSeries.X_ne_zero
  have hUZ : (U Y).map ι = 1 + s • (Z Y).map ι := by
    rw [U_eq]; ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
      Matrix.one_apply, hsdef]
    split_ifs <;> simp
  have hZF : Deg n ((Z Y).map ι) := by
    obtain ⟨q, hq0, hqd, hqx⟩ := hUF
    refine ⟨q.comp (Polynomial.C s * Polynomial.X + Polynomial.C 1), ?_, ?_, ?_⟩
    · intro h
      rcases Polynomial.comp_eq_zero_iff.1 h with h | ⟨_, h⟩
      · exact hq0 h
      · have := congrArg Polynomial.natDegree h
        rw [Polynomial.natDegree_linear hs, Polynomial.natDegree_C] at this
        exact one_ne_zero this
    · rw [Polynomial.natDegree_comp, Polynomial.natDegree_linear hs, mul_one]; exact hqd
    · rw [Polynomial.aeval_comp]
      convert hqx using 2
      rw [hUZ]
      simp [Algebra.algebraMap_eq_smul_one, add_comm]
  have hZ0 : ∀ f ∈ 𝓕, MvPolynomial.aeval (fun p : Fin N × Fin N => Z Y p.1 p.2) f = 0 := by
    intro f hf
    have := (@h𝓕 F _ alg ((Z Y).map ι)).1 hZF f hf
    rw [hmap] at this
    exact (map_eq_zero_iff ι hιinj).1 this
  refine (h𝓕 C Y).2 fun f hf => ?_
  have hk : (PowerSeries.constantCoeff (R := C)).comp (algebraMap C (PowerSeries C)) = algebraMap C C := by
    ext c; simp
  have := congrArg PowerSeries.constantCoeff (hZ0 f hf)
  rw [map_aeval_ring _ hk, map_zero] at this
  convert this using 2
  congr 1
  funext p
  simp [constantCoeff_Z]

theorem TanDeg_of (hE : ExpVan) (hD : DegPoly) : TanDeg := by
  intro C _ _ N n S hS
  refine ⟨fun x hx => ?_, fun Y hY => tan_deg hE hD S hS Y hY⟩
  obtain ⟨𝓕, h𝓕, hvan⟩ := van_of hD S hS
  refine (h𝓕 C x).2 fun f hf => ?_
  rw [aeval_self_eq_ev]
  exact hx f (hvan f hf)

end LateralTheory.DivDb.TangentDegree
end

-- bundled from Development.EtaleCohomology.DivisorCycles.TangentIndexDvd
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb
namespace TangentIndexDvd

section
variable {C : Type} [Field C] {N : ℕ}

theorem subset_zcl (S : Set (Mat C N)) : S ⊆ Zcl S := fun _ hx _ hf => hf _ hx

theorem ev_mul (x : Mat C N) (f g : MP C N) : ev x (f * g) = ev x f * ev x g := by
  simp only [ev, map_mul]

theorem ev_prod {ι : Type} (s : Finset ι) (x : Mat C N) (q : ι → MP C N) :
    ev x (∏ c ∈ s, q c) = ∏ c ∈ s, ev x (q c) := by
  simp only [ev, map_prod]

theorem dAt_mul (f g : MP C N) (x Y : Mat C N) :
    dAt (f * g) x Y = ev x f * dAt g x Y + ev x g * dAt f x Y := by
  unfold dAt
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Derivation.leibniz]
  simp only [ev, smul_eq_mul, map_add (f := _), map_mul]
  ring

theorem mem_img {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C) (U : Subgroup Γ) (x : Mat C N) :
    x ∈ img ρ U ↔ ∃ u ∈ U, ((ρ u : GL (Fin N) C) : Mat C N) = x := by
  simp [img, Submonoid.mem_map]

theorem coset_poly {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C) (U : Subgroup Γ) [U.Normal]
    [U.FiniteIndex] (hChain : Chain) (hMul : ZclMul) (f : MP C N)
    (hf : f ∈ Van (img ρ U : Set (Mat C N))) (g : Γ) :
    ∃ q : MP C N, ev 1 q ≠ 0 ∧ ∀ γ : Γ, (γ : Γ ⧸ U) = (g : Γ ⧸ U) →
      ev ((ρ γ : GL (Fin N) C) : Mat C N) (f * q) = 0 := by
  by_cases h : ∃ q : MP C N, ev 1 q ≠ 0 ∧ ∀ γ : Γ, (γ : Γ ⧸ U) = (g : Γ ⧸ U) →
      ev ((ρ γ : GL (Fin N) C) : Mat C N) q = 0
  · obtain ⟨q, hq1, hq⟩ := h
    exact ⟨q, hq1, fun γ hγ => by rw [ev_mul, hq γ hγ, mul_zero]⟩
  have h' : ∀ q : MP C N, (∀ γ : Γ, (γ : Γ ⧸ U) = (g : Γ ⧸ U) →
      ev ((ρ γ : GL (Fin N) C) : Mat C N) q = 0) → ev 1 q = 0 := fun q hq => by
    by_contra hne; exact h ⟨q, hne, hq⟩
  have hinv : ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) ∈ Zcl (img ρ U : Set (Mat C N)) := by
    intro h0 hh0
    obtain ⟨h1, hev, -⟩ := hChain C N N (LinearMap.mulLeft C ((ρ g⁻¹ : GL (Fin N) C) : Mat C N)) h0
    have key := h' h1 (fun γ hγ => by
      rw [hev, LinearMap.mulLeft_apply]
      apply hh0
      rw [SetLike.mem_coe, mem_img]
      refine ⟨g⁻¹ * γ, QuotientGroup.eq.mp hγ.symm, ?_⟩
      rw [map_mul, Units.val_mul])
    rwa [hev, LinearMap.mulLeft_apply, mul_one] at key
  obtain ⟨k, hk, hkU⟩ : ∃ k : ℕ, 0 < k ∧ g ^ k ∈ U := by
    have : Finite (Γ ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
    refine ⟨orderOf (g : Γ ⧸ U), orderOf_pos _, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, pow_orderOf_eq_one]
  have hpow : ∀ m : ℕ, ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) ^ m ∈ Zcl (img ρ U : Set (Mat C N)) := by
    intro m
    induction m with
    | zero => rw [pow_zero]; exact subset_zcl _ (img ρ U).one_mem
    | succ m ih => rw [pow_succ]; exact hMul C N _ _ ih _ hinv
  have hg : ((ρ g : GL (Fin N) C) : Mat C N) ∈ Zcl (img ρ U : Set (Mat C N)) := by
    have e : ((ρ g : GL (Fin N) C) : Mat C N) = ((ρ (g ^ k) : GL (Fin N) C) : Mat C N) *
        ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) ^ (k - 1) := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← map_pow, ← map_mul]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      congr 2
      simp [pow_succ', mul_assoc, inv_pow]
    rw [e]
    exact hMul C N _ _ (subset_zcl _ ((mem_img ρ U _).2 ⟨_, hkU, rfl⟩)) _ (hpow _)
  refine ⟨1, by simp [ev], fun γ hγ => ?_⟩
  rw [mul_one]
  have hγU : g⁻¹ * γ ∈ U := QuotientGroup.eq.mp hγ.symm
  have e : ((ρ γ : GL (Fin N) C) : Mat C N) = ((ρ g : GL (Fin N) C) : Mat C N) *
      ((ρ (g⁻¹ * γ) : GL (Fin N) C) : Mat C N) := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  rw [e]
  exact hMul C N _ _ hg _ (subset_zcl _ ((mem_img ρ U _).2 ⟨_, hγU, rfl⟩)) f hf

end

theorem TanIndex_of (hChain : Chain) (hMul : ZclMul) : TanIndex := by
  classical
  intro Γ C _ _ N ρ U hN hU Y hY
  have : Finite (Γ ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (Γ ⧸ U) := Fintype.ofFinite _
  have hY' : ∀ F ∈ Van (img ρ ⊤ : Set (Mat C N)), dAt F 1 Y = 0 := hY
  show ∀ f ∈ Van (img ρ U : Set (Mat C N)), dAt f 1 Y = 0
  intro f hf
  have hc : ∀ c : Γ ⧸ U, ∃ q : MP C N, ev 1 q ≠ 0 ∧ ∀ γ : Γ, (γ : Γ ⧸ U) = c →
      ev ((ρ γ : GL (Fin N) C) : Mat C N) (f * q) = 0 := by
    intro c
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    exact coset_poly ρ U hChain hMul f hf g
  choose q hq1 hq using hc
  have hF : f * ∏ c, q c ∈ Van (img ρ ⊤ : Set (Mat C N)) := by
    intro x hx
    obtain ⟨γ, -, rfl⟩ := (mem_img ρ ⊤ x).1 hx
    have h0 := hq (γ : Γ ⧸ U) γ rfl
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (γ : Γ ⧸ U)), ← mul_assoc,
      ev_mul, h0, zero_mul]
  have key := hY' _ hF
  rw [dAt_mul] at key
  have hf1 : ev 1 f = 0 := hf 1 (img ρ U).one_mem
  have hG1 : ev 1 (∏ c, q c) ≠ 0 := by
    rw [ev_prod]; exact Finset.prod_ne_zero_iff.2 fun c _ => hq1 c
  rw [hf1, zero_mul, zero_add] at key
  exact (mul_eq_zero.1 key).resolve_left hG1

end TangentIndexDvd
end LateralTheory.DivDb
end

