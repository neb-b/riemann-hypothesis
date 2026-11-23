module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0080
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvOfFintype
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.EvRing

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]


variable (p Ω) in
def zpH : ℤ_[p] →+* Ω := (algebraMap (O0 p) Ω).comp ((algebraMap (Lau p) (O0 p)).comp HahnSeries.C)

theorem zp_eq (z : ℤ_[p]) : zp Ω z = zpH (p := p) (Ω := Ω) z := rfl

theorem thL_coeff (a : Lau p) (r : ℤ) : (thL a).coeff r = (r : ℤ_[p]) * a.coeff r := rfl

theorem thL_mul (a b : Lau p) : thL (a * b) = thL a * b + a * thL b := by
  apply HahnSeries.ext
  funext r
  have hs : (thL a).support ⊆ a.support := fun i hi h => hi (by simp [thL_coeff, h])
  have ht : (thL b).support ⊆ b.support := fun i hi h => hi (by simp [thL_coeff, h])
  rw [HahnSeries.coeff_add, HahnSeries.coeff_mul_left' a.isPWO_support hs,
    HahnSeries.coeff_mul_right' b.isPWO_support ht, thL_coeff,
    HahnSeries.coeff_mul (x := a) (y := b), Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  rw [thL_coeff, thL_coeff, ← hij.2.2]
  push_cast
  ring

theorem thL_neg (a : Lau p) : thL (-a) = -thL a := by
  ext r
  simp [thL_coeff]

theorem ev_of_fintype {ι : Type} [Fintype ι] (ψ : O0 p →+* Ω) (c : ℤ → Ω) (x x' : Ω) (e : ι → Ω)
    (a : ι → Lau p) (he : ∀ t, IsInt (p := p) (e t) ∧ IsAlgZp (p := p) (e t))
    (hc : ∀ r, c r = ∑ t, e t * zp Ω ((a t).coeff r))
    (hx : x = ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)))
    (hx' : x' = ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (thL (a t)))) : GlobalTheory.Glue.Ev ψ c x x' := by
  let σ := Fintype.equivFin ι
  refine ⟨Fintype.card ι, e ∘ σ.symm, a ∘ σ.symm, fun t => he _, fun r => ?_, ?_, ?_⟩
  · rw [hc r]; exact (Equiv.sum_comp σ.symm (fun t => e t * zp Ω ((a t).coeff r))).symm
  · rw [hx]; exact (Equiv.sum_comp σ.symm (fun t => e t * ψ (algebraMap (Lau p) (O0 p) (a t)))).symm
  · rw [hx']; exact (Equiv.sum_comp σ.symm (fun t => e t * ψ (algebraMap (Lau p) (O0 p) (thL (a t))))).symm

theorem repr {d : ℕ} (e : Fin d → Ω) (a : Fin d → Lau p) (C : HahnSeries ℤ Ω)
    (h : ∀ r, C.coeff r = ∑ t, e t * zp Ω ((a t).coeff r)) :
    C = ∑ t, HahnSeries.C (e t) * (a t).map (zpH (p := p) (Ω := Ω)).toNonUnitalRingHom := by
  ext r
  rw [h r, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.map_coeff]
  rfl

theorem isAlgZp_mul {x y : Ω} (hx : IsAlgZp (p := p) x) (hy : IsAlgZp (p := p) y) :
    IsAlgZp (p := p) (x * y) := by
  let : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra
  have : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have key : ∀ z : Ω, IsAlgZp (p := p) z ↔ IsAlgebraic ℤ_[p] z := by
    intro z; simp only [IsAlgZp, IsAlgebraic, Polynomial.aeval_map_algebraMap]
  rw [key] at hx hy ⊢
  exact hx.mul hy

theorem isAlgZp_gal (g : Gal p Ω) {x : Ω} (hx : IsAlgZp (p := p) x) : IsAlgZp (p := p) (g x) := by
  obtain ⟨P, hP, h⟩ := hx
  exact ⟨P, hP, by rw [Polynomial.aeval_algHom_apply, h, map_zero]⟩

end GlobalTheory.Glue.EvRing

namespace GlobalTheory.Glue.EvRing


open GlobalTheory.K5.Basic in
theorem ev_ring : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ →
    (∀ (C D : HahnSeries ℤ Ω) (x x' y y' : Ω),
      GlobalTheory.Glue.Ev ψ C.coeff x x' → GlobalTheory.Glue.Ev ψ D.coeff y y' →
      GlobalTheory.Glue.Ev ψ (C * D).coeff (x * y) (x' * y + x * y') ∧
      GlobalTheory.Glue.Ev ψ (C + D).coeff (x + y) (x' + y') ∧
      GlobalTheory.Glue.Ev ψ (C - D).coeff (x - y) (x' - y')) ∧
    (∀ (c : ℤ → Ω) (x x' : Ω), GlobalTheory.Glue.Ev ψ c x x' →
      IsInt (p := p) x ∧ IsInt (p := p) x' ∧ (∃ C : HahnSeries ℤ Ω, C.coeff = c) ∧
      (∃ x'', GlobalTheory.Glue.Ev ψ (fun r => (r : Ω) * c r) x' x'') ∧
      (∀ e : Ω, IsInt (p := p) e → IsAlgZp (p := p) e →
        GlobalTheory.Glue.Ev ψ (fun r => e * c r) (e * x) (e * x')) ∧
      ∀ g : Gal p Ω, g (T.qq n) = T.qq n → GlobalTheory.Glue.Ev ψ (fun r => g (c r)) (g x) (g x')) := by
  intro p hp Ω _ _ _ T n ψ hreb
  refine ⟨?_, ?_⟩
  · rintro C D x x' y y' ⟨d, e, a, he, hc, hx, hx'⟩ ⟨d', f, b, hf, hd, hy, hy'⟩
    refine ⟨?_, ?_, ?_⟩
    · refine ev_of_fintype (ι := Fin d × Fin d') ψ _ _ _ (fun ts => e ts.1 * f ts.2)
        (fun ts => a ts.1 * b ts.2) (fun ts => ⟨IsIntegral.mul (he _).1 (hf _).1, isAlgZp_mul (he _).2 (hf _).2⟩)
        (fun r => ?_) ?_ ?_
      · rw [repr e a C hc, repr f b D hd, Finset.sum_mul_sum, HahnSeries.coeff_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [HahnSeries.coeff_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [show HahnSeries.C (e t) * (a t).map (zpH (p := p) (Ω := Ω)).toNonUnitalRingHom *
            (HahnSeries.C (f s) * (b s).map (zpH (p := p) (Ω := Ω)).toNonUnitalRingHom) =
            HahnSeries.C (e t * f s) * (a t * b s).map (zpH (p := p) (Ω := Ω)).toNonUnitalRingHom by
          rw [HahnSeries.map_mul, map_mul]; ring]
        rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.map_coeff]
        rfl
      · rw [hx, hy, Finset.sum_mul_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
        simp only [map_mul]
        ring
      · rw [hx, hx', hy, hy', Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib,
          Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [thL_mul, map_add (f := _), map_mul]
        ring
    · refine ev_of_fintype (ι := Fin d ⊕ Fin d') ψ _ _ _ (Sum.elim e f) (Sum.elim a b)
        (by rintro (t | t) <;> simp [he, hf]) (fun r => ?_) ?_ ?_
      · simp [Fintype.sum_sum_type, hc, hd]
      · simp [Fintype.sum_sum_type, hx, hy]
      · simp [Fintype.sum_sum_type, hx', hy']
    · refine ev_of_fintype (ι := Fin d ⊕ Fin d') ψ _ _ _ (Sum.elim e f) (Sum.elim a fun s => -b s)
        (by rintro (t | t) <;> simp [he, hf]) (fun r => ?_) ?_ ?_
      · simp [Fintype.sum_sum_type, hc, hd, zp_eq, sub_eq_add_neg]
      · simp [Fintype.sum_sum_type, hx, hy, sub_eq_add_neg]
      · simp [Fintype.sum_sum_type, hx', hy', thL_neg, sub_eq_add_neg]
  · rintro c x x' ⟨d, e, a, he, hc, hx, hx'⟩
    have hpow : T.qq n ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) := by
      clear hreb
      induction n with
      | zero => simp [T.q0]
      | succ n ih => rw [pow_succ', pow_mul, T.qpow, ih]
    have hq : IsIntegral (O0 p) (T.qq n) :=
      IsIntegral.of_pow (pow_pos hp.out.pos n) (hpow ▸ isIntegral_algebraMap)
    have hmem : ∀ y, ψ y ∈ Algebra.adjoin (O0 p) {T.qq n} := fun y => by
      have : ψ y ∈ ψ.range := ⟨y, rfl⟩
      rw [hreb.rng] at this
      exact this
    have hint : ∀ y, IsInt (p := p) (ψ y) := fun y => adjoin_le_integralClosure hq (hmem y)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx]; exact IsIntegral.sum _ fun t _ => IsIntegral.mul (he t).1 (hint _)
    · rw [hx']; exact IsIntegral.sum _ fun t _ => IsIntegral.mul (he t).1 (hint _)
    · refine ⟨∑ t, HahnSeries.C (e t) * (a t).map (zpH (p := p) (Ω := Ω)).toNonUnitalRingHom, funext fun r => ?_⟩
      rw [hc r, HahnSeries.coeff_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.map_coeff]
      rfl
    · refine ⟨_, ev_of_fintype ψ _ x' _ e (fun t => thL (a t)) he (fun r => ?_) hx' rfl⟩
      rw [hc r, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [thL_coeff, zp_eq, zp_eq, map_mul, map_intCast]
      ring
    · intro e0 hi ha
      refine ev_of_fintype ψ _ _ _ (fun t => e0 * e t) a
        (fun t => ⟨IsIntegral.mul hi (he t).1, isAlgZp_mul ha (he t).2⟩) (fun r => ?_) ?_ ?_
      · rw [hc r, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
      · rw [hx, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
      · rw [hx', Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
    · intro g hg
      have hfix : ∀ y, g (ψ y) = ψ y := fun y =>
        (AlgHom.eqOn_adjoin_iff (φ := (g : Ω →ₐ[O0 p] Ω)) (ψ := AlgHom.id (O0 p) Ω) (s := {T.qq n})).2
          (by intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact hg) (hmem y)
      have hint_gal : ∀ t, IsInt (p := p) (g (e t)) := fun t =>
        IsIntegral.map g.toAlgHom (he t).1
      refine ev_of_fintype ψ _ _ _ (fun t => g (e t)) a
        (fun t => ⟨hint_gal t, isAlgZp_gal g (he t).2⟩) (fun r => ?_) ?_ ?_
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [hc r, map_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [map_mul]
          congr 1
          exact g.commutes _
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [hx, map_sum]
          exact Finset.sum_congr rfl fun t _ => by rw [map_mul, hfix]
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [hx', map_sum]
          exact Finset.sum_congr rfl fun t _ => by rw [map_mul, hfix]

end GlobalTheory.Glue.EvRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesAndDerivUniqueOfCoefficients
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.EvUniq

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]


variable (Ω) in
def zpHom : ℤ_[p] →+* Ω :=
  (algebraMap (O0 p) Ω).comp ((algebraMap (Lau p) (O0 p)).comp HahnSeries.C)

theorem zpHom_apply (z : ℤ_[p]) : zpHom (Ω := Ω) z = zp Ω z := by
  simp [zpHom, zp, HahnSeries.C_apply]

theorem zp_neg (z : ℤ_[p]) : zp Ω (-z) = - zp Ω z := by
  rw [← zpHom_apply, map_neg, zpHom_apply]

theorem zpHom_injective (hc : IsClo p Ω) : Function.Injective (zpHom (p := p) (Ω := Ω)) := by
  haveI := Basic.charZero_of_isClo hc
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro m hm
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hm
  have hu : zpHom (Ω := Ω) ((PadicInt.unitCoeff h0 : ℤ_[p])) ≠ 0 :=
    ((Units.isUnit (PadicInt.unitCoeff h0)).map (zpHom (Ω := Ω))).ne_zero
  have hp0 : (p : Ω) ^ m.valuation ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  exact mul_ne_zero hu hp0 hm

theorem exists_coords (hc : IsClo p Ω) {ι : Type} [Fintype ι] (E : ι → Ω) :
    ∃ (κ : Type) (_ : Fintype κ) (f : κ → Ω) (M : ι → κ → ℤ_[p]),
      (∀ k, E k = ∑ i, zp Ω (M k i) * f i) ∧
      ∀ v : ι → ℤ_[p], ∑ k, zp Ω (v k) * E k = 0 → ∀ i, ∑ k, v k * M k i = 0 := by
  letI : Algebra ℤ_[p] Ω := (zpHom (p := p) (Ω := Ω)).toAlgebra
  have hsm : ∀ (m : ℤ_[p]) (x : Ω), m • x = zp Ω m * x := fun m x => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, zpHom_apply]
  haveI : NoZeroSMulDivisors ℤ_[p] Ω := ⟨fun {m x} hmx => by
    rw [hsm] at hmx
    rcases mul_eq_zero.1 hmx with h0 | h0
    · left; exact zpHom_injective hc (by rw [zpHom_apply, h0, map_zero])
    · right; exact h0⟩
  let S : Submodule ℤ_[p] Ω := Submodule.span ℤ_[p] (Set.range E)
  haveI : Module.Finite ℤ_[p] S := Module.Finite.span_of_finite _ (Set.finite_range E)
  haveI : Module.Free ℤ_[p] S := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ_[p] S
  have hE : ∀ k, E k ∈ S := fun k => Submodule.subset_span ⟨k, rfl⟩
  refine ⟨Module.Free.ChooseBasisIndex ℤ_[p] S, inferInstance, fun i => (b i : Ω),
    fun k i => b.repr ⟨E k, hE k⟩ i, ?_, ?_⟩
  · intro k
    have h2 := congrArg Subtype.val (b.sum_repr ⟨E k, hE k⟩)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul, hsm] at h2
    exact h2.symm
  · intro v hv i
    have h0 : (∑ k, v k • (⟨E k, hE k⟩ : S)) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul, hsm, Submodule.coe_zero]
      exact hv
    have := congrArg (fun s => b.repr s i) h0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    exact this

theorem psi_C {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (m : ℤ_[p]) :
    ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C m)) = zp Ω m := by
  rw [h.sub (HahnSeries.C m) (HahnSeries.C m), zp, HahnSeries.C_apply]
  · intro i
    simp only [HahnSeries.C_apply, HahnSeries.coeff_single]
    by_cases hi : i = 0
    · simp [hi]
    · have : (p : ℤ) ^ n * i ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) hi
      simp [hi, this]
  · intro r hr
    have : r ≠ 0 := by rintro rfl; exact hr (dvd_zero _)
    simp [HahnSeries.C_apply, HahnSeries.coeff_single, this]

theorem sum_psi_eq_zero (hc : IsClo p Ω) {T : Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ)
    {ι : Type} [Fintype ι] (E : ι → Ω) (A G : ι → Lau p) (φ : ℤ → ℤ_[p])
    (hA : ∀ r, ∑ k, E k * zp Ω ((A k).coeff r) = 0)
    (hG : ∀ k r, (G k).coeff r = φ r * (A k).coeff r) :
    ∑ k, E k * ψ (algebraMap (Lau p) (O0 p) (G k)) = 0 := by
  obtain ⟨κ, _, f, M, hE, hind⟩ := exists_coords hc E
  have hB : ∀ i, ∑ k, HahnSeries.C (M k i) * G k = 0 := by
    intro i
    apply HahnSeries.ext
    funext r
    rw [HahnSeries.coeff_sum]
    simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, hG,
      HahnSeries.coeff_zero]
    have h1 := hind (fun k => (A k).coeff r) (by rw [← hA r]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _) i
    calc ∑ k, M k i * (φ r * (A k).coeff r) = φ r * ∑ k, (A k).coeff r * M k i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := by rw [h1, mul_zero]
  calc ∑ k, E k * ψ (algebraMap (Lau p) (O0 p) (G k))
      = ∑ i, f i * ψ (algebraMap (Lau p) (O0 p) (∑ k, HahnSeries.C (M k i) * G k)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul, psi_C h, hE, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by simp only [hB, map_zero, mul_zero, Finset.sum_const_zero]

theorem thL_coeff (a : Lau p) (r : ℤ) : (thL a).coeff r = (r : ℤ_[p]) * a.coeff r := rfl

theorem ev_unique : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (c : ℤ → Ω) (x x' y y' : Ω),
    Ev ψ c x x' → Ev ψ c y y' → x = y ∧ x' = y' := by
  intro p _ Ω _ _ hc T n ψ h c x x' y y' hx hy
  obtain ⟨d, e, a, -, hca, rfl, rfl⟩ := hx
  obtain ⟨d', e', a', -, hca', rfl, rfl⟩ := hy
  let E : Fin d ⊕ Fin d' → Ω := Sum.elim e e'
  let A : Fin d ⊕ Fin d' → Lau p := Sum.elim a (fun s => -a' s)
  have hA : ∀ r, ∑ k, E k * zp Ω ((A k).coeff r) = 0 := by
    intro r
    simp only [E, A, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, HahnSeries.coeff_neg, zp_neg,
      mul_neg, Finset.sum_neg_distrib]
    linear_combination hca' r - hca r
  have h1 := sum_psi_eq_zero hc h E A A (fun _ => 1) hA (fun k r => by simp)
  have h2 := sum_psi_eq_zero hc h E A (fun k => thL (A k)) (fun r => (r : ℤ_[p])) hA
    (fun k r => thL_coeff _ _)
  have thL_neg : ∀ b : Lau p, thL (-b) = - thL b := fun b => by
    apply HahnSeries.ext
    funext r
    simp only [thL_coeff, HahnSeries.coeff_neg, mul_neg]
  simp only [E, A, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_neg, mul_neg,
    Finset.sum_neg_distrib, thL_neg] at h1 h2
  exact ⟨sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h1), sub_eq_zero.1 (by simpa [sub_eq_add_neg] using h2)⟩

end GlobalTheory.EvUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommonLevelSpanMultiple
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ


open scoped MatrixGroups TensorProduct in
open Matrix in
theorem _root_.GlobalTheory.KZ.gamma_le_of_dvd {M M' : ℕ} (h : M ∣ M') :
    CongruenceSubgroup.Gamma M' ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have e : ∀ z : ℤ, (z : ZMod M) = ZMod.castHom h (ZMod M) (z : ZMod M') := fun z =>
    (map_intCast _ z).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e, h1, map_one]
  · rw [e, h2, map_zero]
  · rw [e, h3, map_zero]
  · rw [e, h4, map_one]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.lev_mono (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] {M M' : ℕ} (h : M ∣ M') :
    X.Lev l M ≤ X.Lev l M' := by
  apply Submodule.span_mono
  rintro x ⟨f, hf, rfl⟩
  exact ⟨f, fun γ hγ => hf γ (gamma_le_of_dvd h hγ), rfl⟩

theorem Tower.exists_lev (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (y : X.Kl l) :
    ∃ M : ℕ, 0 < M ∧ y ∈ X.Lev l M := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, Submodule.zero_mem _⟩
  | tmul a f =>
    obtain ⟨M, hM, hf⟩ := X.level (Additive.toMul f : X.Kˣ)
    refine ⟨M, hM, ?_⟩
    have hmem : (1 : ℤ_[l]) ⊗ₜ[ℤ] f ∈ X.Lev l M :=
      Submodule.subset_span ⟨Additive.toMul f, fun γ hγ => hf γ hγ, rfl⟩
    have e : a ⊗ₜ[ℤ] f = a • ((1 : ℤ_[l]) ⊗ₜ[ℤ] f) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    exact Submodule.smul_mem _ a hmem
  | add y z hy hz =>
    obtain ⟨M, hM, hy⟩ := hy
    obtain ⟨M', hM', hz⟩ := hz
    refine ⟨M * M', Nat.mul_pos hM hM', Submodule.add_mem _ ?_ ?_⟩
    · exact X.lev_mono l (dvd_mul_right M M') hy
    · exact X.lev_mono l (dvd_mul_left M' M) hz

theorem Tower.exists_lev_family : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (K : ℕ) {ι : Type} [Fintype ι] (y : ι → X.Kl l), 0 < K →
    ∃ M : ℕ, 0 < M ∧ K ∣ M ∧ ∀ i, y i ∈ X.Lev l M := by
  intro Ω _ _ ε X l _ K ι _ y hK
  choose L hL hy using fun i => X.exists_lev l (y i)
  refine ⟨K * ∏ i, L i, Nat.mul_pos hK (Finset.prod_pos fun i _ => hL i), dvd_mul_right _ _, fun i => ?_⟩
  refine X.lev_mono l ?_ (hy i)
  exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem L (Finset.mem_univ i)) K

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfMemVB
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.H3

theorem polySlash_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (p : MvPolynomial (Fin 2) R) : slP m (MvPolynomial.map φ p) = MvPolynomial.map φ (slP m p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, Betti.slP_X, MvPolynomial.smul_eq_C_mul]

theorem map_mem_pot {E : Type} [CommRing E] {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] E] {w : ℕ}
    {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) ℤ_[l]} (hF : F ∈ Pot ℤ_[l] w Γ) :
    (fun z => MvPolynomial.map (algebraMap ℤ_[l] E) (F z)) ∈ Pot E w Γ := by
  obtain ⟨h1, h2⟩ := hF
  refine ⟨fun z => (h1 z).map _, fun γ hγ => ?_⟩
  obtain ⟨p, hp⟩ := h2 γ hγ
  refine ⟨MvPolynomial.map (algebraMap ℤ_[l] E) p, fun z hz => ?_⟩
  rw [← hp z hz, map_sub, polySlash_map]

theorem exists_pot_of_mem_VB : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l w : ℕ)
    [Fact l.Prime] {E : Type} [Field E] [Algebra ℤ_[l] E],
    (∀ b ∈ X.BSet N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), H3.Rel X l b F) →
      ∀ x ∈ X.VB N l w E, ∃ G ∈ Pot E w (Gam N l), (x, G) ∈ H3.abelian₂ X l E := by
  intro Ω _ _ ε X N l w _ E _ _ hB
  let S : Submodule E (E ⊗[ℤ_[l]] X.Fn l) :=
    { carrier := {x | ∃ G ∈ Pot E w (Gam N l), (x, G) ∈ abelian₂ X l E}
      add_mem' := by
        rintro x y ⟨G, hG, hx⟩ ⟨G', hG', hy⟩
        exact ⟨G + G', (Betti.potSub E w (Gam N l)).add_mem hG hG', (abelian₂ X l E).add_mem hx hy⟩
      zero_mem' := ⟨0, (Betti.potSub E w (Gam N l)).zero_mem, (abelian₂ X l E).zero_mem⟩
      smul_mem' := by
        rintro c x ⟨G, hG, hx⟩
        exact ⟨c • G, (Betti.potSub E w (Gam N l)).smul_mem c hG, (abelian₂ X l E).smul_mem c hx⟩ }
  have h1 : ∀ b ∈ X.B N l w, (1 : E) ⊗ₜ[ℤ_[l]] b ∈ S := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨F, hF, hR⟩ := hB b hb
      exact ⟨_, map_mem_pot hF, Submodule.subset_span ⟨b, F, hR, rfl⟩⟩
    | zero => simpa using S.zero_mem
    | add b b' _ _ h h' => simpa [TensorProduct.tmul_add] using S.add_mem h h'
    | smul r b _ h =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul E r]
      exact S.smul_mem _ h
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  show _ ∈ S
  induction y using TensorProduct.induction_on with
  | zero => simpa using S.zero_mem
  | tmul c b =>
    rw [LinearMap.baseChange_tmul, Submodule.subtype_apply]
    have : c ⊗ₜ[ℤ_[l]] (b : X.Fn l) = c • ((1 : E) ⊗ₜ[ℤ_[l]] (b : X.Fn l)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]; exact S.smul_mem c (h1 b b.2)
  | add y y' h h' => rw [map_add (f := _)]; exact S.add_mem h h'

end GlobalTheory.KZ.H3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankEichlerShimuraCocyclesLeGamma1Statement
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_z1_le_of_le_gamma1_of_finiteIndex : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (w : ℕ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → Γ.FiniteIndex → FiniteDimensional ℂ (Z1 Γ w) ∧ 12 * Module.finrank ℂ (Z1 Γ w) ≤ (w + 1) * (12 + Γ.index) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCocycles_le_Gamma1 | exact GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCocycles_le_Gamma1 | (intros; apply GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCocycles_le_Gamma1 <;> assumption)
end

