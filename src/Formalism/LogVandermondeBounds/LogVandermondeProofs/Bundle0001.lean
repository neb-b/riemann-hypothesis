module

public import Formalism.LogVandermondeBounds.Bundle0001

@[expose] public section

-- bundled from Formalism.LogVandermondeBounds.LogVandermondeProofs.BlockDimensionIdentities
section
namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

theorem eulerProductBounds : EulerProductBounds := by
  intro q hq n
  set x := q⁻¹ with hx
  have hx0 : 0 < x := inv_pos.mpr (by linarith)
  have hxq : x * q = 1 := inv_mul_cancel₀ (by linarith)
  have hx3 : x ≤ 1 / 3 := by nlinarith
  have hx1 : x ≤ 1 := by linarith
  have key : ∀ n : ℕ, 1 - 2 * x + x ^ (n + 1) ≤ (1 - x) * ∏ i ∈ range n, (1 - x ^ (i + 1)) := by
    intro n
    induction n with
    | zero => simp; linarith
    | succ n ih =>
      rw [Finset.prod_range_succ, ← mul_assoc]
      set y := x ^ (n + 1) with hy
      have hy0 : 0 ≤ y := pow_nonneg hx0.le _
      have hyx : y ≤ x := pow_le_of_le_one hx0.le hx1 (by omega)
      have hc : 0 ≤ 1 - y := by have : y ≤ 1 := pow_le_one₀ hx0.le hx1; linarith
      have h1 := mul_le_mul_of_nonneg_right ih hc
      have h2 : y * y ≤ y * x := mul_le_mul_of_nonneg_left hyx hy0
      have e : x ^ (n + 1 + 1) = y * x := by rw [hy, pow_succ]
      rw [e]
      nlinarith
  have hfac : ∀ i ∈ range n, 0 ≤ 1 - x ^ (i + 1) ∧ 1 - x ^ (i + 1) ≤ 1 := by
    intro i _
    exact ⟨by have : x ^ (i + 1) ≤ 1 := pow_le_one₀ hx0.le hx1; linarith,
      by have : 0 ≤ x ^ (i + 1) := pow_nonneg hx0.le _; linarith⟩
  refine ⟨?_, Finset.prod_le_one₀ (fun i hi => (hfac i hi).1) (fun i hi => (hfac i hi).2)⟩
  by_contra hlt
  push_neg at hlt
  have h1 : (1 - x) * ∏ i ∈ range n, (1 - x ^ (i + 1)) < (1 - x) * (1 / 2) :=
    mul_lt_mul_of_pos_left hlt (by linarith)
  have := key n
  have := pow_pos hx0 (n + 1)
  linarith

end Formalism.LogVandermondeBounds.StandardLattice
end

-- bundled from Formalism.LogVandermondeBounds.LogVandermondeProofs.MulSingleMulApplySelf
section
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section Core

variable {ι H K : Type} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [DecidableEq H] [Field K]

def eps (a h : H) : K := if h = a then 1 else if h = 1 then -1 else 0

def bas (a : ι → {c : H // c ≠ 1}) (h : ι → H) : K := ∏ w, (eps ((a w : H)) (h w) : K)

omit [Fintype H] in
lemma mulSingle_mul_apply_ne (v w : ι) (c : H) (h : ι → H) (hw : w ≠ v) :
    ((Pi.mulSingle v c : ι → H) * h) w = h w := by
  rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hw, _root_.one_mul]

omit [Fintype H] in
lemma mulSingle_mul_apply_self (v : ι) (c : H) (h : ι → H) :
    ((Pi.mulSingle v c : ι → H) * h) v = c * h v := by
  rw [Pi.mul_apply, Pi.mulSingle_eq_same]

lemma sum_eps (a t : H) (ha : a ≠ 1) : ∑ c : H, (eps a (c * t) : K) = 0 := by
  have key : ∀ h : H, (eps a h : K) = (if h = a then 1 else 0) + (if h = 1 then -1 else 0) := by
    intro h
    unfold eps
    by_cases h1 : h = a
    · subst h1
      simp [ha]
    · simp [h1]
  rw [show (∑ c : H, (eps a (c * t) : K)) = ∑ h : H, (eps a h : K) from
    Equiv.sum_comp (Equiv.mulRight t) (fun h => (eps a h : K))]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma sum_bas (a : ι → {c : H // c ≠ 1}) (v : ι) (h : ι → H) :
    ∑ c : H, (bas a ((Pi.mulSingle v c : ι → H) * h) : K) = 0 := by
  have hfac : ∀ c : H, (bas a ((Pi.mulSingle v c : ι → H) * h) : K)
      = (eps (a v : H) (c * h v) : K) * ∏ w ∈ univ.erase v, (eps (a w : H) (h w) : K) := by
    intro c
    unfold bas
    rw [← Finset.mul_prod_erase univ _ (mem_univ v)]
    simp only [mulSingle_mul_apply_self]
    congr 1
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [mulSingle_mul_apply_ne v w c h (Finset.ne_of_mem_erase hw)]
  simp only [hfac, ← Finset.sum_mul, sum_eps (K := K) (a v : H) (h v) (a v).2, zero_mul]

lemma bas_avoid (a b : ι → {c : H // c ≠ 1}) :
    (bas a (fun w => (b w : H)) : K) = if a = b then 1 else 0 := by
  unfold bas
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    refine Finset.prod_eq_one fun w _ => ?_
    unfold eps
    simp
  · rw [if_neg hab]
    have hw : ∃ w, a w ≠ b w := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hab (funext hcon)
    obtain ⟨w, hw⟩ := hw
    refine Finset.prod_eq_zero (mem_univ w) ?_
    have h1 : (b w : H) ≠ a w := fun h => hw (Subtype.ext h.symm)
    unfold eps
    simp [h1, (b w).2]

lemma inj_core (ψ : (ι → H) → K)
    (hψ : ∀ (v : ι) (h : ι → H), ∑ c : H, ψ ((Pi.mulSingle v c : ι → H) * h) = 0)
    (h0 : ∀ a : ι → {c : H // c ≠ 1}, ψ (fun w => (a w : H)) = 0) :
    ∀ h, ψ h = 0 := by
  classical
  suffices key : ∀ n, ∀ h : ι → H, (univ.filter (fun w => h w = 1)).card = n → ψ h = 0 from
    fun h => key _ h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h hn
    by_cases hall : ∀ w, h w ≠ 1
    · exact h0 (fun w => ⟨h w, hall w⟩)
    · simp only [not_forall, not_not] at hall
      obtain ⟨v, hv⟩ := hall
      have hsum := hψ v h
      rw [Finset.sum_eq_single (1 : H)] at hsum
      · simpa using hsum
      · intro c _ hc
        apply ih _ _ _ rfl
        rw [← hn]
        have hset : univ.filter (fun w => ((Pi.mulSingle v c : ι → H) * h) w = 1)
            = (univ.filter (fun w => h w = 1)).erase v := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
          by_cases hwv : w = v
          · subst hwv
            rw [mulSingle_mul_apply_self, hv, mul_one]
            simp [hc]
          · rw [mulSingle_mul_apply_ne v w c h hwv]
            simp [hwv]
        rw [hset]
        exact Finset.card_erase_lt_of_mem (by simp [hv])
      · intro h1
        exact absurd (Finset.mem_univ _) h1

end Core

section Main

variable {ι H X K : Type} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [DecidableEq H]
  [Fintype X] [MulAction (ι → H) X] [Field K]

def restr (Q : Type) (e : Q × (ι → H) ≃ X) :
    ramSub ι H X K →ₗ[K] (Q × (ι → {c : H // c ≠ 1}) → K) where
  toFun φ p := (φ : X → K) (e (p.1, fun w => (p.2 w : H)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_core (Q : Type) [Fintype Q] (e : Q × (ι → H) ≃ X)
    (he : ∀ (m : ι → H) (ω : Q) (g : ι → H), e (ω, m * g) = m • e (ω, g)) :
    Module.finrank K (ramSub ι H X K) = Fintype.card Q * (Fintype.card H - 1) ^ Fintype.card ι := by
  classical
  have hmem : ∀ φ : ramSub ι H X K, ∀ v x,
      ∑ c : H, (φ : X → K) ((Pi.mulSingle v c : ι → H) • x) = 0 := fun φ => φ.2
  have hinj : Function.Injective (restr (K := K) Q e) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    apply Subtype.ext
    funext x
    obtain ⟨⟨ω, g⟩, rfl⟩ := e.surjective x
    have hz := inj_core (K := K) (fun h => (φ : X → K) (e (ω, h)))
      (fun v h => by simpa only [he] using hmem φ v (e (ω, h)))
      (fun a => congrFun hφ (ω, a)) g
    simpa using hz
  have hsurj : Function.Surjective (restr (K := K) Q e) := by
    intro f
    let φ0 : X → K := fun x =>
      ∑ a : ι → {c : H // c ≠ 1}, f ((e.symm x).1, a) * bas a (e.symm x).2
    have hφ0 : φ0 ∈ ramSub ι H X K := by
      show ∀ (v : ι) (x : X), ∑ c : H, φ0 ((Pi.mulSingle v c : ι → H) • x) = 0
      intro v x
      obtain ⟨⟨ω, g⟩, rfl⟩ := e.surjective x
      have hx : ∀ c : H, e.symm ((Pi.mulSingle v c : ι → H) • e (ω, g))
          = (ω, (Pi.mulSingle v c : ι → H) * g) := by
        intro c
        rw [← he, Equiv.symm_apply_apply]
      simp only [φ0, hx]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [← Finset.mul_sum, sum_bas, mul_zero]
    refine ⟨⟨φ0, hφ0⟩, ?_⟩
    funext p
    obtain ⟨ω, a'⟩ := p
    show φ0 (e (ω, fun w => (a' w : H))) = f (ω, a')
    simp only [φ0, Equiv.symm_apply_apply, bas_avoid]
    simp
  have hc : Fintype.card {c : H // c ≠ 1} = Fintype.card H - 1 := by
    simp [Fintype.card_subtype_compl]
  rw [(LinearEquiv.ofBijective (restr (K := K) Q e) ⟨hinj, hsurj⟩).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fun, hc]

end Main

theorem exists_equiv (ι H X : Type) [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [Fintype X]
    [MulAction (ι → H) X] (hfree : ∀ (g : ι → H) (x : X), g • x = x → g = 1) :
    ∃ (Q : Type) (_ : Fintype Q) (e : Q × (ι → H) ≃ X),
      ∀ (m : ι → H) (ω : Q) (g : ι → H), e (ω, m * g) = m • e (ω, g) := by
  classical
  let Q := MulAction.orbitRel.Quotient (ι → H) X
  letI : Fintype Q := Fintype.ofFinite Q
  let rep : Q → X := fun ω => Quotient.out ω
  have hrep : ∀ ω : Q, Quotient.mk (MulAction.orbitRel (ι → H) X) (rep ω) = ω :=
    fun ω => Quotient.out_eq ω
  let f : Q × (ι → H) → X := fun p => p.2 • rep p.1
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨ω, g⟩ ⟨ω', g'⟩ h
      change g • rep ω = g' • rep ω' at h
      have hω : ω = ω' := by
        rw [← hrep ω, ← hrep ω']
        apply Quotient.sound
        show rep ω ∈ MulAction.orbit (ι → H) (rep ω')
        refine ⟨g⁻¹ * g', ?_⟩
        show (g⁻¹ * g') • rep ω' = rep ω
        rw [mul_smul, ← h, inv_smul_smul]
      subst hω
      have hfix : (g'⁻¹ * g) • rep ω = rep ω := by rw [mul_smul, h, inv_smul_smul]
      have hg := hfree _ _ hfix
      rw [inv_mul_eq_one] at hg
      rw [hg]
    · intro x
      have hx : rep (Quotient.mk (MulAction.orbitRel (ι → H) X) x) ∈ MulAction.orbit (ι → H) x :=
        Quotient.exact (hrep _)
      obtain ⟨g, hg⟩ := hx
      refine ⟨(Quotient.mk (MulAction.orbitRel (ι → H) X) x, g⁻¹), ?_⟩
      show g⁻¹ • rep (Quotient.mk (MulAction.orbitRel (ι → H) X) x) = x
      rw [← hg, inv_smul_smul]
  refine ⟨Q, inferInstance, Equiv.ofBijective f hf, ?_⟩
  intro m ω g
  show (m * g) • rep ω = m • (g • rep ω)
  rw [mul_smul]

theorem finrankFiberSumZero : FinrankFiberSumZero := by
  intro ι H X K _ _ _ _ _ _ _ hfree
  classical
  obtain ⟨Q, _, e, he⟩ := exists_equiv ι H X hfree
  rw [finrank_core (K := K) Q e he, ← Fintype.card_congr e, Fintype.card_prod, Fintype.card_fun]
  ring

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
end

-- bundled from Formalism.LogVandermondeBounds.LogVandermondeProofs.PrimePowerSubgroupTrivial
section
namespace Formalism.LogVandermondeBounds.StandardLattice

open Polynomial

theorem primeOrderFinrank : PrimeOrderFinrank := by
  intro K _ _ n g A hg hA hA1
  haveI := Fact.mk hg
  let f : (Fin n → K) →ₗ[ℚ] (Fin n → K) := (Matrix.toLin' A).restrictScalars ℚ
  have hpow : ∀ v : Fin n → K, (f ^ g) v = v := by
    intro v
    rw [Module.End.pow_apply]
    show (⇑(Matrix.toLin' A))^[g] v = v
    rw [← Module.End.pow_apply, ← Matrix.toLin'_pow, hA, Matrix.toLin'_one, LinearMap.id_apply]
  have hfg : f ^ g = 1 := LinearMap.ext hpow
  have hint : IsIntegral ℚ f := IsIntegral.of_finite ℚ f
  have hm0 : minpoly ℚ f ≠ 0 := minpoly.ne_zero hint
  have hdvd : minpoly ℚ f ∣ Polynomial.cyclotomic g ℚ * (Polynomial.X - 1) := by
    rw [Polynomial.cyclotomic_prime_mul_X_sub_one]
    apply minpoly.dvd
    simp [hfg]
  have hirr := Polynomial.cyclotomic.irreducible_rat hg.pos
  have hdeg : (Polynomial.cyclotomic g ℚ).natDegree = g - 1 := by
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hg]
  have hle : (minpoly ℚ f).natDegree ≤ Module.finrank ℚ K * n := by
    have h1 := Polynomial.natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly f) (LinearMap.charpoly_monic f).ne_zero
    rw [LinearMap.charpoly_natDegree] at h1
    have h2 : Module.finrank ℚ (Fin n → K) = Module.finrank ℚ K * n := by
      rw [Module.finrank_pi_fintype]
      simp [mul_comm]
    omega
  by_cases hc : Polynomial.cyclotomic g ℚ ∣ minpoly ℚ f
  · have := Polynomial.natDegree_le_of_dvd hc hm0
    omega
  · exfalso
    apply hA1
    have hcop : IsCoprime (minpoly ℚ f) (Polynomial.cyclotomic g ℚ) :=
      ((hirr.coprime_iff_not_dvd).2 hc).symm
    have h1 : minpoly ℚ f ∣ Polynomial.X - 1 := by
      first
        | exact hcop.dvd_of_dvd_mul_left hdvd
        | exact hcop.dvd_of_dvd_mul_right hdvd
        | exact hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at hdvd)
        | exact hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at hdvd)
    have h2 : Polynomial.aeval f (Polynomial.X - 1 : Polynomial ℚ) = 0 := by
      obtain ⟨q, hq⟩ := h1
      rw [hq, map_mul, minpoly.aeval, zero_mul]
    have hf1 : f = 1 := by
      simpa [sub_eq_zero] using h2
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_one]
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun hf1 v
    simpa [f] using this

end Formalism.LogVandermondeBounds.StandardLattice
end

