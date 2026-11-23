module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0015
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PDenseCoset
section
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private def latt {O K ι : Type} [CommRing O] [Field K] (τ : ι → (O →+* K)) (N : O) (k : ℕ) :
    AddSubgroup (ι × Fin k → K) where
  carrier := {x | ∃ β : Fin k → O, x = pt τ (fun s => N * β s)}
  add_mem' := by
    rintro _ _ ⟨β, rfl⟩ ⟨β', rfl⟩
    refine ⟨β + β', ?_⟩
    funext p
    simp [pt, mul_add]
  zero_mem' := by
    refine ⟨0, ?_⟩
    funext p
    simp [pt]
  neg_mem' := by
    rintro _ ⟨β, rfl⟩
    refine ⟨-β, ?_⟩
    funext p
    simp [pt]

theorem denseCoset_of : DenseSub → SpanTop → DenseOff → DenseCoset := by
  intro hS hT hO O K ι _ _ _ _ τ hτ N hN k a Q hQ
  have hspan : Submodule.span K ((latt τ N k : AddSubgroup (ι × Fin k → K)) : Set (ι × Fin k → K)) = ⊤ :=
    hT O K ι τ hτ N hN k
  have hd := hS K (ι × Fin k) (latt τ N k) (pt τ a) hspan
  have hd2 := hO K (ι × Fin k) _ hd Q hQ
  intro P hP
  apply hd2
  rintro x ⟨hx, hxQ⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin k → O, x - pt τ a = pt τ (fun s => N * β s) := hx
  have hxe : x = pt τ (fun s => a s + N * β s) := by
    rw [sub_eq_iff_eq_add.mp hβ]
    funext p
    simp [pt, add_comm]
  refine hP x ⟨fun s => a s + N * β s, fun s => ?_, ?_, hxe⟩
  · simp
  · rw [← hxe]
    exact hxQ

end UpperTheory.Gal.Schur
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PDenseOff
section
open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.denseOff :
    DenseOff := by
  intro K σ _ D hD Q hQ P hP
  have hPQ : P * Q = 0 := by
    apply hD
    intro x hx
    by_cases hq : eval x Q = 0
    · rw [map_mul, hq, mul_zero]
    · rw [map_mul, hP x ⟨hx, hq⟩, zero_mul]
  exact (mul_eq_zero.1 hPQ).resolve_right hQ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PDenseSub
section
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem denseSub : DenseSub := by
  intro K σ _ _ _ L a hL Q hQ
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  have hx : x - a ∈ Submodule.span K (L : Set (σ → K)) := by
    rw [hL]
    exact Submodule.mem_top
  obtain ⟨n, c, v, hcv⟩ := Submodule.mem_span_set'.mp hx
  let p0 : (Fin n → K) → σ → K := fun t j => a j + ∑ i, t i * (v i : σ → K) j
  let F : σ → MvPolynomial (Fin n) K := fun j => C (a j) + ∑ i, X i * C ((v i : σ → K) j)
  have hev : ∀ t, eval t (bind₁ F Q) = eval (p0 t) Q := by
    intro t
    have h1 : aeval t (bind₁ F Q) = eval t (bind₁ F Q) := rfl
    have h2 : aeval (fun j => aeval t (F j)) Q = eval (fun j => aeval t (F j)) Q := rfl
    rw [← h1, aeval_bind₁, h2]
    congr 2
    funext j
    simp [p0, F]
  have hzero : bind₁ F Q = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → K)) ?_ ?_
    · intro _
      exact Set.infinite_range_of_injective Int.cast_injective
    · intro t ht
      rw [hev, map_zero]
      choose m hm using fun i => ht i (Set.mem_univ i)
      apply hQ
      show p0 t - a ∈ L
      have hsum : p0 t - a = ∑ i, m i • (v i : σ → K) := by
        funext j
        simp [p0, ← hm, Finset.sum_apply, zsmul_eq_mul]
      rw [hsum]
      exact sum_mem (fun i _ => zsmul_mem (v i).2 (m i))
  have hxp : p0 c = x := by
    funext j
    have hj := congrFun hcv j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hj
    simp only [p0, hj]
    ring
  rw [← hxp, ← hev, hzero, map_zero]

end UpperTheory.Gal.Schur
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PESpan
section
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem elementary_span_mul (K : Type) [CommRing K] (n k l : ℕ)
    (P Q : MvPolynomial (Fin n) K) (hP : P ∈ eSpan K n k) (hQ : Q ∈ eSpan K n l) :
    P * Q ∈ eSpan K n (k + l) := by
  have hmem : P * Q ∈ eSpan K n k * eSpan K n l := Submodule.mul_mem_mul hP hQ
  have hle : eSpan K n k * eSpan K n l ≤ eSpan K n (k + l) := by
    unfold eSpan
    rw [Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨m, rfl⟩, _, ⟨m', rfl⟩, rfl⟩
    refine ⟨Fin.append m m', ?_⟩
    simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  exact hle hmem

private theorem one_mem_eSpan (K : Type) [CommRing K] (n j : ℕ) :
    (1 : MvPolynomial (Fin n) K) ∈ eSpan K n j := by
  unfold eSpan
  apply Submodule.subset_span
  refine ⟨fun _ => 0, ?_⟩
  simp [esymm_zero]

theorem eSpanMul : ESpanMul := by
  intro K _ n
  refine ⟨fun k l hkl => ?_, fun k l P Q hP hQ => elementary_span_mul K n k l P Q hP hQ⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  intro P hP
  simpa using elementary_span_mul K n k d P 1 hP (one_mem_eSpan K n d)

end UpperTheory.Gal.Schur
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PExpand
section
open Finset MvPolynomial UpperTheory.Gal.Schur

private lemma one_factor {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (n : ℕ) (x : R)
    (g : Fin n → R) :
    detOne x g = ∑ a : Fin (n + 1), x ^ (a : ℕ) * ((-1) ^ (a : ℕ) * aeval g (esymm (Fin n) K a)) := by
  have key : ∀ a : ℕ, x ^ a * ((-1) ^ a * aeval g (esymm (Fin n) K a)) =
      ∑ t ∈ powersetCard a (univ : Finset (Fin n)), ∏ j ∈ t, (-(x * g j)) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [esymm, map_sum, map_prod, aeval_X, mul_sum]
    refine sum_congr rfl fun t ht => ?_
    rw [prod_neg, prod_mul_distrib, prod_const, (mem_powersetCard.1 ht).2]
    ring
  rw [Fin.sum_univ_eq_sum_range (fun a => x ^ a * ((-1) ^ a * aeval g (esymm (Fin n) K a))) (n + 1)]
  simp only [key]
  have hc : n + 1 = #(univ : Finset (Fin n)) + 1 := by simp
  rw [hc, ← sum_powerset, ← prod_one_add]
  unfold detOne
  simp only [sub_eq_add_neg]

theorem UpperTheory.Gal.Schur.expand :
    Expand := by
  intro K R π _ _ _ _ _ n x g
  simp only [one_factor (K := K)]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [prod_mul_distrib]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PExtract
section
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem extract : Extract := by
  classical
  intro K σ A M _ _ _ x hx e he w
  set v : A → M → K := fun a m => ∏ p, x a p ^ e m p with hvdef
  have htop : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
    have hφv : ∀ u : M → K, φ u = ∑ m, u m * φ (Pi.single m 1) := by
      intro u
      rw [LinearMap.pi_apply_eq_sum_univ φ u]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_eq_mul]
      congr 2
      ext s
      simp [Pi.single_apply, eq_comm]
    let E : M → σ →₀ ℕ := fun m => Finsupp.equivFunOnFinite.symm (e m)
    have hE : Function.Injective E := fun a b h => he (by simpa [E] using h)
    let Q : MvPolynomial σ K := ∑ m, monomial (E m) (φ (Pi.single m 1))
    have hQ : Q = 0 := by
      refine hx Q ?_
      rintro _ ⟨a, rfl⟩
      have h1 : φ (v a) = 0 := by
        have h2 := Submodule.mem_map_of_mem (f := φ) (Submodule.subset_span ⟨a, rfl⟩ : v a ∈ Submodule.span K (Set.range v))
        rw [hmap, Submodule.mem_bot] at h2
        exact h2
      rw [hφv] at h1
      rw [← h1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Q, map_sum, eval_monomial]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), mul_comm]
      rfl
    apply hφ
    refine LinearMap.ext fun u => ?_
    rw [hφv, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    have hc := congrArg (AddMonoidAlgebra.coeff · (E m)) hQ
    simp only [Q, coeff_sum, coeff_monomial, AddMonoidAlgebra.coeff_zero, hE.eq_iff] at hc
    simp at hc
    rw [hc, mul_zero]
  have hw : w ∈ Submodule.span K (Set.range v) := by rw [htop]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hw
  refine ⟨c, fun m => ?_⟩
  rw [← hc]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hvdef]

end UpperTheory.Gal.Schur
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PFibre
section
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private lemma prod_scaleOff {R : Type} [CommRing R] {n : ℕ} (y : R) (i : Fin n) (g : Fin n → R) :
    ∏ k, scaleOff y i g k = y ^ (n - 1) * ∏ k, g k := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i), ← Finset.mul_prod_erase univ g (mem_univ i)]
  have h : ∏ k ∈ univ.erase i, scaleOff y i g k = ∏ k ∈ univ.erase i, (y * g k) :=
    Finset.prod_congr rfl (fun k hk => by simp [scaleOff, (mem_erase.1 hk).1])
  rw [h, prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ i), card_univ,
    Fintype.card_fin]
  simp only [scaleOff, if_true]
  ring

theorem fibre_of : SchurY → SchurHomog → SchurDet → Fibre := by
  intro hY hH hD R ι _ _ _ _ n t₀ t₁ h01 ε lam m hm g y hu
  have hconst : ∀ h : Fin n → R, sch (lam t₁) h = (∏ k, h k) ^ m := by
    intro h
    have e := (hD R n h).2 (fun _ => 0) m
    simp only [zero_add, (hD R n h).1, mul_one] at e
    have hl : lam t₁ = fun _ => m := funext hm
    rw [hl, e]
  have h10 : t₁ ≠ t₀ := fun h => h01 h.symm
  have h1mem : t₁ ∈ univ.erase t₀ := mem_erase.mpr ⟨h10, mem_univ _⟩
  have hrest : ∀ i, ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (twist t₀ t₁ ε y i g t) =
      y ^ (∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ k, lam t k) *
        ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (g t) := by
    intro i
    rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    apply prod_congr rfl
    intro t ht
    have ht1 : t ≠ t₁ := (mem_erase.mp ht).1
    have ht0 : t ≠ t₀ := (mem_erase.mp (mem_erase.mp ht).2).1
    simp only [twist, if_neg ht0, if_neg ht1]
    rw [hH R n (lam t) (g t) (y ^ ε t), ← pow_mul]
  have hi : ∀ i, ∏ t, sch (lam t) (twist t₀ t₁ ε y i g t) =
      sch (lam t₀) (scaleAt y i (g t₀)) *
        (y ^ ((n - 1) * m + ∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ k, lam t k) *
          ∏ t ∈ univ.erase t₀, sch (lam t) (g t)) := by
    intro i
    rw [← mul_prod_erase univ _ (mem_univ t₀), ← mul_prod_erase (univ.erase t₀) _ h1mem,
      ← mul_prod_erase (univ.erase t₀) (fun t => sch (lam t) (g t)) h1mem, hrest i]
    simp only [twist, eq_self_iff_true, ↓reduceIte, h10]
    rw [hconst, hconst, prod_scaleOff, mul_pow, ← pow_mul, pow_add]
    ring
  calc ∑ i, (∏ t, sch (lam t) (twist t₀ t₁ ε y i g t)) *
        ∏ k ∈ univ.erase i, (g t₀ k - y * g t₀ i) * Ring.inverse (g t₀ k - g t₀ i)
      = (y ^ ((n - 1) * m + ∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ k, lam t k) *
          ∏ t ∈ univ.erase t₀, sch (lam t) (g t)) *
        ∑ i, sch (lam t₀) (scaleAt y i (g t₀)) *
          ∏ k ∈ univ.erase i, (g t₀ k - y * g t₀ i) * Ring.inverse (g t₀ k - g t₀ i) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        rw [hi i]
        ring
    _ = _ := by
        rw [hY R n (lam t₀) (g t₀) y hu, ← mul_prod_erase univ (fun t => sch (lam t) (g t)) (mem_univ t₀)]
        ring

end UpperTheory.Gal.Schur
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PFibreOff
section
open Finset MvPolynomial UpperTheory.Gal.Schur

private lemma prod_scale_at {R : Type} [CommRing R] {n : ℕ} (y : R) (i : Fin n) (g : Fin n → R) :
    ∏ k, scaleAt y i g k = y * ∏ k, g k := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i), ← Finset.mul_prod_erase univ g (mem_univ i)]
  have h1 : scaleAt y i g i = y * g i := by simp [scaleAt]
  have h2 : ∏ k ∈ univ.erase i, scaleAt y i g k = ∏ k ∈ univ.erase i, g k :=
    Finset.prod_congr rfl (fun k hk => by simp [scaleAt, ne_of_mem_erase hk])
  rw [h1, h2]; ring

theorem UpperTheory.Gal.Schur.fibreOff_of :
    SchurYOff → SchurHomog → SchurDet → FibreOff := by
  intro hY hH hD
  intro R ι _ _ _ _ n t₀ t₁ h ε lam m hm g y hu
  have hsplit : ∀ F : ι → R,
      ∏ t, F t = F t₀ * (F t₁ * ∏ t ∈ (univ.erase t₀).erase t₁, F t) := by
    intro F
    rw [← Finset.mul_prod_erase univ F (mem_univ t₀),
      ← Finset.mul_prod_erase (univ.erase t₀) F (mem_erase.2 ⟨h.symm, mem_univ _⟩)]
  have hlam : lam t₀ = fun i => (fun _ => 0 : Fin n → ℕ) i + m := by
    funext i; simp [hm]
  have hsch0 : ∀ h' : Fin n → R, sch (lam t₀) h' = (∏ k, h' k) ^ m := by
    intro h'
    rw [hlam]
    exact ((hD R n h').2 _ m).trans (by rw [(hD R n h').1, mul_one])
  have hrest : ∀ i, ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (twist t₀ t₁ ε y i g t) =
      y ^ (∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ i, lam t i) *
        ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (g t) := by
    intro i
    have hc : ∀ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (twist t₀ t₁ ε y i g t) =
        y ^ (ε t * ∑ i, lam t i) * sch (lam t) (g t) := by
      intro t ht
      have ht1 : t ≠ t₁ := ne_of_mem_erase ht
      have ht0 : t ≠ t₀ := ne_of_mem_erase (mem_of_mem_erase ht)
      simp only [twist, if_neg ht0, if_neg ht1]
      rw [hH, ← pow_mul]
    rw [Finset.prod_congr rfl hc, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have tw0 : ∀ i, twist t₀ t₁ ε y i g t₀ = scaleAt y i (g t₀) := by
    intro i; simp [twist]
  have tw1 : ∀ i, twist t₀ t₁ ε y i g t₁ = scaleOff y i (g t₁) := by
    intro i; simp [twist, h.symm]
  have hterm : ∀ i : Fin n,
      (∏ t, sch (lam t) (twist t₀ t₁ ε y i g t)) *
          ∏ k ∈ univ.erase i, ((g t₁ i - y * g t₁ k) * Ring.inverse (g t₁ i - g t₁ k)) =
        (y ^ m * (∏ k, g t₀ k) ^ m *
            (y ^ (∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ i, lam t i) *
              ∏ t ∈ (univ.erase t₀).erase t₁, sch (lam t) (g t))) *
          (sch (lam t₁) (scaleOff y i (g t₁)) *
            ∏ k ∈ univ.erase i, ((g t₁ i - y * g t₁ k) * Ring.inverse (g t₁ i - g t₁ k))) := by
    intro i
    rw [hsplit (fun t => sch (lam t) (twist t₀ t₁ ε y i g t)), tw0, tw1, hrest, hsch0,
      prod_scale_at, mul_pow]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum, hY R n (lam t₁) (g t₁) y hu,
    hsplit (fun t => sch (lam t) (g t)), hsch0, pow_add]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PHomog
section
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem aeval_mul_of_isHomogeneous {σ R : Type} [Fintype σ] [CommRing R] [Algebra ℚ R]
    {P : MvPolynomial σ ℚ} {d : ℕ} (hP : P.IsHomogeneous d) (y : R) (g : σ → R) :
    aeval (fun k => y * g k) P = y ^ d * aeval g P :=
  _root_.UpperTheory.Reformulated.B.Qh65.aeval_mul_of_isHomogeneous hP y g

theorem schurHomog : SchurHomog := by
  intro R _ _ n lam g y
  unfold sch
  exact aeval_mul_of_isHomogeneous
    (GroundTheory.Heights₂.Heights.RestTerms.SchSchurHomogeneous.proof (Fin n) n lam) y g

end UpperTheory.Gal.Schur
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PMixDet
section
open Finset MvPolynomial UpperTheory.Gal.Schur

private theorem prod_ite_eq_mul_prod_erase {R : Type} [CommRing R] {n : ℕ} (d d' : Fin n → R) (a : Fin n) :
    ∏ b, (if b = a then d b else d' b) = d a * ∏ b ∈ univ.erase a, d' b := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ a), if_pos rfl]
  congr 1
  refine Finset.prod_congr rfl fun b hb => ?_
  rw [if_neg (Finset.ne_of_mem_erase hb)]

theorem UpperTheory.Gal.Schur.mixDet :
    MixDet := by
  intro R _ n M d d'
  simp only [Matrix.det_apply, Matrix.of_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, Units.smul_def, zsmul_eq_mul]
  have key : ∀ i, (∏ j, if j = i then d (σ j) else d' (σ j)) =
      ∏ b, (if b = σ i then d b else d' b) := by
    intro i
    rw [← Equiv.prod_comp σ (fun b => if b = σ i then d b else d' b)]
    simp only [σ.injective.eq_iff]
  calc _ = (∑ i, ∏ b, (if b = σ i then d b else d' b)) *
        ((Equiv.Perm.sign σ : ℤ) * ∏ x, M (σ x) x) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [key]
        ring
    _ = _ := by
        congr 1
        rw [Equiv.sum_comp σ (fun a => ∏ b, if b = a then d b else d' b)]
        exact Finset.sum_congr rfl fun a _ => prod_ite_eq_mul_prod_erase d d' a
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PPairCount
section
open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.pairCount_of :
    PairSplit → PairCount := by
  intro hP n i
  have hS : ∑ a : Fin n, (n - 1 - (a : ℕ)) = n.choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun a => n - 1 - a), Finset.sum_range_reflect (fun a => a) n,
      Finset.sum_range_id, Nat.choose_two_right]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  have hC : (m + 1).choose 2 = m.choose 2 + m := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  have hi : (i : ℕ) ≤ m := by have := i.isLt; omega
  simp only [Nat.add_sub_cancel] at hS ⊢
  refine ⟨?_, ?_⟩
  · have h1 := Finset.add_sum_erase (univ : Finset (Fin (m + 1))) (fun k => m - (k : ℕ))
      (Finset.mem_univ i)
    omega
  · have h := hP (Multiplicative ℕ) (m + 1) (fun _ _ => Multiplicative.ofAdd 1) i
    apply_fun Multiplicative.toAdd at h
    simp [toAdd_prod] at h
    omega
end

