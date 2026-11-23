module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteInvolutionFixedUnitEqMulConj
section
namespace GlobalTheory

private lemma exists_pos_pow_mul_pow_eq_pow_of_finite {S : Type} [Monoid S] [Finite S] (a : S) :
    ∃ M : ℕ, 0 < M ∧ a ^ M * a ^ M = a ^ M := by
  have key : ∀ i j : ℕ, i < j → a ^ i = a ^ j → ∃ M : ℕ, 0 < M ∧ a ^ M * a ^ M = a ^ M := by
    intro i j hij h
    obtain ⟨p, rfl⟩ : ∃ p, j = i + (p + 1) := ⟨j - i - 1, by omega⟩
    have step : ∀ n, a ^ (i + n + (p + 1)) = a ^ (i + n) := by
      intro n
      rw [show i + n + (p + 1) = n + (i + (p + 1)) by ring, pow_add, ← h, ← pow_add,
        show n + i = i + n by ring]
    have rep : ∀ k n, a ^ (i + n + k * (p + 1)) = a ^ (i + n) := by
      intro k
      induction k with
      | zero => intro n; simp
      | succ k ih =>
        intro n
        rw [show i + n + (k + 1) * (p + 1) = i + (n + k * (p + 1)) + (p + 1) by ring, step,
          ← add_assoc, ih]
    refine ⟨(i + 1) * (p + 1), by positivity, ?_⟩
    rw [← pow_add]
    have hr := rep (i + 1) (i * p + p + 1)
    rwa [show i + (i * p + p + 1) + (i + 1) * (p + 1) = (i + 1) * (p + 1) + (i + 1) * (p + 1) by ring,
      show i + (i * p + p + 1) = (i + 1) * (p + 1) by ring] at hr
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt h
  · exact key j i hlt h.symm

theorem finite_involution_hilbert90 {S : Type} [CommRing S] [Finite S] (c : S →+* S)
    (hc : ∀ x, c (c x) = x) (ω : S) (hω : IsUnit (ω - c ω)) (y : S) (hy : y * c y = 1) :
    ∃ x : S, IsUnit x ∧ x = y * c x := by
  have hyu : IsUnit y := ⟨⟨y, c y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
  obtain ⟨M, hM0, hM⟩ := exists_pos_pow_mul_pow_eq_pow_of_finite ((1 + y) * c (1 + y))
  obtain ⟨e, he⟩ : ∃ e, e = ((1 + y) * c (1 + y)) ^ M := ⟨_, rfl⟩
  rw [← he] at hM
  have hce : c e = e := by
    rw [he, map_pow, map_mul, hc, mul_comm]
  have h1 : y * c (1 + y) = 1 + y := by
    rw [map_add (f := _), map_one]; linear_combination hy
  refine ⟨e * (1 + y) + (1 - e) * (ω + y * c ω), ?_, ?_⟩
  · by_contra hx
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hx)
    have hp := hm.isPrime
    have hnot : y * (ω - c ω) ∉ m := fun h => hm.ne_top (Ideal.eq_top_of_isUnit_mem m h (hyu.mul hω))
    have hid : ω * (1 + y) - (ω + y * c ω) = y * (ω - c ω) := by ring
    have hex : e ∈ m → 1 + y ∈ m := by
      intro h
      rw [he] at h
      rcases hp.mem_or_mem (hp.mem_of_pow_mem M h) with h' | h'
      · exact h'
      · rw [← h1]; exact m.mul_mem_left y h'
    by_cases hem : e ∈ m
    · have hx1 : 1 + y ∈ m := hex hem
      have h2 : (1 - e) * (ω + y * c ω) ∈ m := by
        have hr : (1 - e) * (ω + y * c ω)
            = (e * (1 + y) + (1 - e) * (ω + y * c ω)) - e * (1 + y) := by ring
        rw [hr]; exact m.sub_mem hxm (m.mul_mem_right _ hem)
      have h1e : 1 - e ∉ m := by
        intro h
        apply hm.ne_top
        rw [Ideal.eq_top_iff_one]
        have hs := m.add_mem hem h
        rwa [add_sub_cancel] at hs
      have hxω : ω + y * c ω ∈ m := (hp.mem_or_mem h2).resolve_left h1e
      apply hnot
      rw [← hid]
      exact m.sub_mem (m.mul_mem_left ω hx1) hxω
    · have hee : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hM, sub_self]
      have h1e : 1 - e ∈ m := by
        refine (hp.mem_or_mem ?_).resolve_left hem
        rw [hee]; exact m.zero_mem
      have h2 : e * (1 + y) ∈ m := by
        have hr : e * (1 + y)
            = (e * (1 + y) + (1 - e) * (ω + y * c ω)) - (1 - e) * (ω + y * c ω) := by ring
        rw [hr]; exact m.sub_mem hxm (m.mul_mem_right _ h1e)
      have hx1 : 1 + y ∈ m := (hp.mem_or_mem h2).resolve_left hem
      apply hem
      rw [he]
      exact Ideal.pow_mem_of_mem m (m.mul_mem_right _ hx1) M hM0
  · simp only [map_add (f := _), map_mul, map_sub, map_one, hc, hce]
    linear_combination (-(e + (1 - e) * ω)) * hy

theorem finite_involution_fixed_unit_isNorm :
    ∀ (S : Type) [CommRing S] [Finite S] (c : S →+* S), (∀ x, c (c x) = x) →
      (∃ ω, IsUnit (ω - c ω)) → ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u := by
  intro S _ _ c hc hω u hcu hu
  obtain ⟨ω, hω⟩ := hω
  let cu : Sˣ →* Sˣ := Units.map (c : S →* S)
  have hcuv : ∀ x : Sˣ, ((cu x : Sˣ) : S) = c x := fun x => rfl
  have hcc : ∀ x : Sˣ, cu (cu x) = x := fun x => Units.ext (by rw [hcuv, hcuv, hc])
  let N : Sˣ →* Sˣ := MonoidHom.id Sˣ * cu
  let ψ : Sˣ →* Sˣ := MonoidHom.id Sˣ / cu
  have hN : ∀ x, N x = x * cu x := fun x => rfl
  have hψ : ∀ x, ψ x = x / cu x := fun x => MonoidHom.div_apply _ _ x
  have hker : N.ker ≤ ψ.range := by
    intro y hy
    rw [MonoidHom.mem_ker, hN] at hy
    have hy' : (y : S) * c y = 1 := by
      have := congrArg Units.val hy
      rwa [Units.val_mul, hcuv, Units.val_one] at this
    obtain ⟨x, hxu, hx⟩ := finite_involution_hilbert90 c hc ω hω y hy'
    refine ⟨hxu.unit, ?_⟩
    rw [hψ, div_eq_iff_eq_mul]
    exact Units.ext (by rw [Units.val_mul, hcuv, IsUnit.unit_spec]; exact hx)
  have hrange : N.range ≤ ψ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, hψ, div_eq_one, hN, map_mul, hcc, mul_comm]
  have hcard : Nat.card ψ.ker ≤ Nat.card N.range := by
    have e1 := N.ker.card_mul_index
    have e2 := ψ.ker.card_mul_index
    rw [Subgroup.index_ker] at e1 e2
    have hle : Nat.card N.ker ≤ Nat.card ψ.range := Subgroup.card_le_of_le hker
    have hpos : 0 < Nat.card ψ.range := Nat.card_pos
    have h3 : Nat.card ψ.ker * Nat.card ψ.range ≤ Nat.card N.range * Nat.card ψ.range := by
      rw [e2, ← e1, mul_comm (Nat.card N.range)]
      exact Nat.mul_le_mul_right _ hle
    exact Nat.le_of_mul_le_mul_right h3 hpos
  have heq : N.range = ψ.ker := Subgroup.eq_of_le_of_card_ge hrange hcard
  have hmem : hu.unit ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hψ, div_eq_one]
    exact Units.ext (by rw [hcuv, IsUnit.unit_spec, hcu])
  rw [← heq] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_⟩
  have := congrArg Units.val hx
  rwa [hN, Units.val_mul, hcuv, IsUnit.unit_spec] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FunctionalFixedByIdempotentRepresented
section
namespace GlobalTheory

theorem functional_fixed_by_idempotent_represented
    {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hL : ∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) (_hR : ∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0)
    (P P' : Module.End ℂ V) (_hP : P ∘ₗ P = P) (hfin : FiniteDimensional ℂ (LinearMap.range P))
    (hadj : ∀ φ ψ, B (P φ) ψ = B φ (P' ψ)) (f : V →ₗ[ℂ] ℂ) (hf : f ∘ₗ P = f) :
    ∃ ψ, ∀ φ, B φ ψ = f φ := by
  set U := LinearMap.range P

  let T : V →ₗ[ℂ] Module.Dual ℂ U := (B.domRestrict U).flip
  have hT : ∀ ψ (u : U), T ψ u = B u ψ := fun _ _ => rfl
  have hcoann : (LinearMap.range T).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_dualCoannihilator] at hu
    have : (u : V) = 0 := hL u (fun ψ => by
      have := hu (T ψ) ⟨ψ, rfl⟩
      simpa [hT] using this)
    simpa using Subtype.ext this
  have hsurj : LinearMap.range T = ⊤ := by
    have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range T)
    rw [hcoann] at h
    rw [← h]
    exact Submodule.dualAnnihilator_bot
  have : f.domRestrict U ∈ LinearMap.range T := by rw [hsurj]; trivial
  obtain ⟨ψ, hψ⟩ := this
  refine ⟨P' ψ, fun φ => ?_⟩
  rw [← hadj]
  have h1 : T ψ ⟨P φ, φ, rfl⟩ = f (P φ) := by rw [hψ]; rfl
  rw [hT] at h1
  rw [h1]
  exact congrArg (fun g : V →ₗ[ℂ] ℂ => g φ) hf

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GLInvMulCongrOneModUniformizer
section
open Matrix

namespace GlobalTheory

theorem GL_inv_mul_congr_one : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {N : ℕ} (π : K), π ≠ 0 → Valued.v π < 1 →
  ∀ (a a₁ : GL (Fin N) K), (∀ i j, Valued.v (π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) →
    (∀ i j, Valued.v (π⁻¹ * ((a₁ : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) →
    ∀ i j, Valued.v (π⁻¹ * (((a⁻¹ * a₁ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1 := by
  intro K _ _ N π hπ0 hπ a a₁ ha ha₁
  set v : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v with hv
  let S : Subring K := v.integer
  have hpS : π ∈ S := (Valuation.mem_integer_iff _ _).2 hπ.le
  let p : S := ⟨π, hpS⟩
  let B : Matrix (Fin N) (Fin N) S := fun i j =>
    ⟨π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j, (Valuation.mem_integer_iff _ _).2 (ha i j)⟩
  let B₁ : Matrix (Fin N) (Fin N) S := fun i j =>
    ⟨π⁻¹ * ((a₁ : Matrix (Fin N) (Fin N) K) - 1) i j, (Valuation.mem_integer_iff _ _).2 (ha₁ i j)⟩
  let f : S →+* K := S.subtype
  let A' : Matrix (Fin N) (Fin N) S := 1 + p • B
  have hA : f.mapMatrix A' = (a : Matrix (Fin N) (Fin N) K) := by
    ext i j
    have h1 : (((1 : Matrix (Fin N) (Fin N) S) i j : S) : K) = (1 : Matrix (Fin N) (Fin N) K) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    change ((A' i j : S) : K) = _
    change (((1 + p • B) i j : S) : K) = _
    rw [Matrix.add_apply, Matrix.smul_apply, Subring.coe_add, smul_eq_mul, Subring.coe_mul, h1]
    change _ + π * (π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j) = _
    rw [← mul_assoc, mul_inv_cancel₀ hπ0, one_mul, Matrix.sub_apply]
    ring
  have hB : (a₁ : Matrix (Fin N) (Fin N) K) - a = π • f.mapMatrix (B₁ - B) := by
    ext i j
    rw [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, smul_eq_mul]
    change _ = π * (((B₁ i j - B i j : S)) : K)
    rw [AddSubgroupClass.coe_sub]
    change _ = π * (π⁻¹ * ((a₁ : Matrix (Fin N) (Fin N) K) - 1) i j - π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j)
    rw [← mul_sub, ← mul_assoc, mul_inv_cancel₀ hπ0, one_mul, Matrix.sub_apply, Matrix.sub_apply]
    ring
  let I : Ideal S := Ideal.span {p}
  have hp : Ideal.Quotient.mk I p = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have hdet1 : A'.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det]
    have hm : (Ideal.Quotient.mk I).mapMatrix A' = 1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      simp only [A', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, hp, zero_mul,
        add_zero, Matrix.one_apply]
      split_ifs <;> simp
    rw [hm, det_one, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hdet1
  have hvd : v (f A'.det) = 1 := by
    have hlt : v (f (A'.det - 1)) < 1 := by
      rw [← hc, map_mul, map_mul]
      have hc' : v (f c) ≤ 1 := (Valuation.mem_integer_iff _ _).1 c.2
      calc v (f c) * v (f p) ≤ 1 * v (f p) := mul_le_mul_of_nonneg_right hc' zero_le'
        _ = v π := one_mul _
        _ < 1 := hπ
    have he : f A'.det = 1 + f (A'.det - 1) := by rw [map_sub, map_one]; ring
    rw [he, Valuation.map_add_eq_of_lt_left v (by rwa [v.map_one]), v.map_one]
  have hu : IsUnit A'.det := (Valuation.integer.integers v).isUnit_of_one' hvd
  have hinv : (a : Matrix (Fin N) (Fin N) K) * f.mapMatrix A'⁻¹ = 1 := by
    rw [← hA, ← map_mul, Matrix.mul_nonsing_inv _ hu, map_one]
  have hainv : ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = f.mapMatrix A'⁻¹ := by
    calc ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
        = ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * ((a : Matrix (Fin N) (Fin N) K) * f.mapMatrix A'⁻¹) := by
          rw [hinv, mul_one]
      _ = _ := by rw [← mul_assoc, Units.inv_mul, one_mul]
  have key : ((a⁻¹ * a₁ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) - 1 = π • f.mapMatrix (A'⁻¹ * (B₁ - B)) := by
    calc ((a⁻¹ * a₁ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) - 1
        = ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * a₁ - ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * a := by
          rw [Units.val_mul, Units.inv_mul]
      _ = ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * ((a₁ : Matrix (Fin N) (Fin N) K) - a) := by rw [Matrix.mul_sub]
      _ = ((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * (π • f.mapMatrix (B₁ - B)) := by rw [hB]
      _ = π • (((a⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * f.mapMatrix (B₁ - B)) := by rw [Matrix.mul_smul]
      _ = _ := by rw [map_mul, hainv]
  intro i j
  rw [key, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hπ0, one_mul,
    RingHom.mapMatrix_apply, Matrix.map_apply]
  exact (Valuation.mem_integer_iff _ _).1 ((A'⁻¹ * (B₁ - B)) i j).2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlHomNnrealTrivialOfScalarTrivial
section
namespace GlobalTheory
open Matrix

section HomTriv
variable {k : Type} [Field k] {N : ℕ}

private lemma hom_ne_zero (φ : GL (Fin N) k →* NNReal) (g : GL (Fin N) k) : φ g ≠ 0 := by
  intro h
  have := map_mul φ g g⁻¹
  rw [mul_inv_cancel, map_one, h, zero_mul] at this
  exact one_ne_zero this

private lemma det_diagonal_ne_zero (d : Fin N → k) (hd : ∀ m, d m ≠ 0) :
    (diagonal d).det ≠ 0 := by
  rw [det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun m _ => hd m

private lemma diag_perm (φ : GL (Fin N) k →* NNReal) (σ : Equiv.Perm (Fin N))
    (d : Fin N → k) (hd : ∀ m, d m ≠ 0) :
    φ (nonsingInvUnit (diagonal (d ∘ σ))
        (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero _ fun m => hd (σ m)))) =
      φ (nonsingInvUnit (diagonal d) (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero d hd))) := by
  set G := nonsingInvUnit (diagonal d) (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero d hd))
  have h1 : (σ.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) k) * σ.symm.toPEquiv.toMatrix = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  have h2 : (σ.symm.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) k) * σ.toPEquiv.toMatrix = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  let U : GL (Fin N) k := ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, h1, h2⟩
  have hconj : nonsingInvUnit (diagonal (d ∘ σ))
      (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero _ fun m => hd (σ m))) = U * G * U⁻¹ := by
    apply Units.ext
    show diagonal (d ∘ σ) = σ.toPEquiv.toMatrix * diagonal d * σ.symm.toPEquiv.toMatrix
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix,
      Equiv.symm_symm]
    exact (submatrix_diagonal_equiv d σ).symm
  rw [hconj, map_mul, map_mul, mul_comm (φ U), mul_assoc, ← map_mul, mul_inv_cancel, map_one,
    mul_one]

end HomTriv
end GlobalTheory

namespace GlobalTheory
open Matrix
section HomTriv2
variable {k : Type} [Field k] {N : ℕ}

private lemma diag_conj_transvection (i j : Fin N) (hij : i ≠ j) (y c : k) :
    diagonal (Pi.mulSingle i y) * transvection i j c =
      transvection i j (y * c) * diagonal (Pi.mulSingle i y) := by
  ext a b
  simp only [diagonal_mul, mul_diagonal, transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Pi.mulSingle_apply]
  by_cases ha : a = i <;> by_cases hb : b = j <;> by_cases hab : a = b <;>
    simp_all [eq_comm] <;> ring

private lemma transvection_trivial (φ : GL (Fin N) k →* NNReal) (hx : ∃ x : k, x ≠ 0 ∧ x ≠ 1)
    (i j : Fin N) (hij : i ≠ j) (c : k) (g : GL (Fin N) k)
    (hg : (g : Matrix (Fin N) (Fin N) k) = transvection i j c) : φ g = 1 := by
  obtain ⟨x, hx0, hx1⟩ := hx
  have hdetT : ∀ c : k, (transvection i j c).det ≠ 0 := fun c => by
    rw [det_transvection_of_ne _ _ hij]; exact one_ne_zero
  let T : k → GL (Fin N) k := fun c => nonsingInvUnit _ (isUnit_iff_ne_zero.mpr (hdetT c))
  have hgT : g = T c := Units.ext hg
  have hmulT : ∀ a b, T a * T b = T (a + b) := fun a b =>
    Units.ext (transvection_mul_transvection_same i j hij a b)
  have hscale : ∀ y : k, y ≠ 0 → ∀ c, φ (T (y * c)) = φ (T c) := by
    intro y hy c
    have hd : ∀ m, (Pi.mulSingle i y : Fin N → k) m ≠ 0 := fun m => by
      by_cases hm : m = i
      · rw [hm, Pi.mulSingle_eq_same]; exact hy
      · rw [Pi.mulSingle_eq_of_ne hm]; exact one_ne_zero
    let D : GL (Fin N) k :=
      nonsingInvUnit (diagonal (Pi.mulSingle i y)) (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero _ hd))
    have hc : D * T c = T (y * c) * D := Units.ext (diag_conj_transvection i j hij y c)
    have := congrArg φ hc
    rw [map_mul, map_mul, mul_comm (φ (T (y * c)))] at this
    exact (mul_left_cancel₀ (hom_ne_zero φ D) this).symm
  rw [hgT]
  have key : φ (T c) = φ (T c) * φ (T c) := by
    calc φ (T c) = φ (T (x * c)) := (hscale x hx0 c).symm
      _ = φ (T (c + (x - 1) * c)) := by congr 2; ring
      _ = φ (T c) * φ (T ((x - 1) * c)) := by rw [← hmulT, map_mul]
      _ = φ (T c) * φ (T c) := by rw [hscale (x - 1) (sub_ne_zero.mpr hx1) c]
  have h0 := hom_ne_zero φ (T c)
  exact (mul_right_eq_self₀.mp key.symm).resolve_right h0

end HomTriv2
end GlobalTheory

namespace GlobalTheory
open Matrix
section HomTriv3
variable {k : Type} [Field k] {N : ℕ}

private lemma mulSingle_unit_ne_zero (m : Fin N) (a : kˣ) (t : Fin N) :
    (Pi.mulSingle m (a : k) : Fin N → k) t ≠ 0 := by
  by_cases ht : t = m
  · rw [ht, Pi.mulSingle_eq_same]; exact a.ne_zero
  · rw [Pi.mulSingle_eq_of_ne ht]; exact one_ne_zero

private noncomputable def elemDiag (m : Fin N) (a : kˣ) : GL (Fin N) k :=
  nonsingInvUnit (diagonal (Pi.mulSingle m (a : k)))
    (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero _ (mulSingle_unit_ne_zero m a)))

private lemma elemDiag_coe (m : Fin N) (a : kˣ) :
    (elemDiag m a : Matrix (Fin N) (Fin N) k) = diagonal (Pi.mulSingle m (a : k)) := rfl

private lemma prod_elemDiag (d : Fin N → kˣ) :
    ((((List.finRange N).map fun m => elemDiag m (d m)).prod : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) = diagonal (fun t => (d t : k)) := by
  have h1 : ((((List.finRange N).map fun m => elemDiag m (d m)).prod : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) = ((List.finRange N).map
          ((diagonalRingHom (Fin N) k) ∘ fun m => Pi.mulSingle m (d m : k))).prod := by
    rw [show ((List.finRange N).map
        ((diagonalRingHom (Fin N) k) ∘ fun m => Pi.mulSingle m (d m : k))) =
        (List.finRange N).map ((Units.coeHom (Matrix (Fin N) (Fin N) k)) ∘
          fun m => elemDiag m (d m)) from rfl, List.prod_map_hom]
    rfl
  rw [h1, List.prod_map_hom, ← Fin.prod_univ_def, Finset.univ_prod_mulSingle (fun t => (d t : k))]
  rfl

private lemma elemDiag_swap (φ : GL (Fin N) k →* NNReal) (m m' : Fin N) (a : kˣ) :
    φ (elemDiag m a) = φ (elemDiag m' a) := by
  have hcomp : (Pi.mulSingle m' (a : k) : Fin N → k) ∘ (Equiv.swap m m') =
      Pi.mulSingle m (a : k) := by
    funext t
    simp only [Function.comp_apply, Pi.mulSingle_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have h := diag_perm φ (Equiv.swap m m') _ (mulSingle_unit_ne_zero m' a)
  have he : elemDiag m a = nonsingInvUnit (diagonal ((Pi.mulSingle m' (a : k) : Fin N → k) ∘
      (Equiv.swap m m'))) (isUnit_iff_ne_zero.mpr (det_diagonal_ne_zero _
        fun t => mulSingle_unit_ne_zero m' a ((Equiv.swap m m') t))) :=
    Units.ext (by rw [elemDiag_coe]; exact congrArg diagonal hcomp.symm)
  rw [he, h]
  rfl

private lemma elemDiag_trivial (φ : GL (Fin N) k →* NNReal)
    (hφ : ∀ z : kˣ, φ (Matrix.GeneralLinearGroup.scalar (Fin N) z) = 1) (m : Fin N) (a : kˣ) :
    φ (elemDiag m a) = 1 := by
  have hs : Matrix.GeneralLinearGroup.scalar (Fin N) a =
      ((List.finRange N).map fun t => elemDiag t ((fun _ => a) t)).prod := by
    apply Units.ext
    rw [prod_elemDiag]
    simp [Matrix.GeneralLinearGroup.scalar]
  have h1 := hφ a
  rw [hs, map_list_prod, List.map_map, ← Fin.prod_univ_def] at h1
  simp only [Function.comp_apply] at h1
  rw [Finset.prod_congr rfl (fun t _ => elemDiag_swap φ t m a), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at h1
  have hN : N ≠ 0 := by rintro rfl; exact m.elim0
  exact (pow_eq_one_iff_of_nonneg zero_le hN).mp h1

private lemma diagonal_trivial (φ : GL (Fin N) k →* NNReal)
    (hφ : ∀ z : kˣ, φ (Matrix.GeneralLinearGroup.scalar (Fin N) z) = 1) (D : Fin N → k)
    (hD : ∀ t, D t ≠ 0) (g : GL (Fin N) k) (hg : (g : Matrix (Fin N) (Fin N) k) = diagonal D) :
    φ g = 1 := by
  let d : Fin N → kˣ := fun t => Units.mk0 (D t) (hD t)
  have : g = ((List.finRange N).map fun m => elemDiag m (d m)).prod :=
    Units.ext (by rw [prod_elemDiag, hg]; rfl)
  rw [this, map_list_prod, List.map_map, ← Fin.prod_univ_def]
  exact Finset.prod_eq_one fun m _ => elemDiag_trivial φ hφ m (d m)

theorem gl_hom_nnreal_trivial_of_scalar :
    ∀ (k : Type) [Field k], (∃ x : k, x ≠ 0 ∧ x ≠ 1) → ∀ (N : ℕ) (φ : GL (Fin N) k →* NNReal),
      (∀ z : kˣ, φ (Matrix.GeneralLinearGroup.scalar (Fin N) z) = 1) → ∀ g, φ g = 1 := by
  intro k _ hx N φ hφ g
  have hdet : (g : Matrix (Fin N) (Fin N) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  refine diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ g : GL (Fin N) k, (g : Matrix (Fin N) (Fin N) k) = M → φ g = 1)
    (g : Matrix (Fin N) (Fin N) k) hdet ?_ ?_ ?_ g rfl
  · intro D hD h hh
    rw [det_diagonal] at hD
    exact diagonal_trivial φ hφ D (fun t => (Finset.prod_ne_zero_iff.mp hD) t (Finset.mem_univ t)) h hh
  · intro t h hh
    exact transvection_trivial φ hx t.i t.j t.hij t.c h hh
  · intro A B hA hB hPA hPB h hh
    let uA : GL (Fin N) k := nonsingInvUnit A (isUnit_iff_ne_zero.mpr hA)
    let uB : GL (Fin N) k := nonsingInvUnit B (isUnit_iff_ne_zero.mpr hB)
    have : h = uA * uB := Units.ext hh
    rw [this, map_mul, hPA uA rfl, hPB uB rfl, mul_one]

end HomTriv3
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBis
section
namespace GlobalTheory.PolynomialNormBound

theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {j m : ℕ}, j ≠ (0 : ℕ) → ¬l ^ m ∣ j →
    ∃ (c : ℤ_[l]), (↑j : ℤ_[l]) * c = (↑l : ℤ_[l]) ^ (m - (1 : ℕ)) := by
  intro l inst j m hj hdvd
  have hl : l.Prime := inst.out
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hj l hl.ne_one
  have hvm : v < m := by
    by_contra h
    exact hdvd (Dvd.dvd.mul_right (Nat.pow_dvd_pow l (not_lt.mp h)) u)
  have hunit : IsUnit (u : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl).mpr hu
  obtain ⟨w, hw⟩ := hunit
  refine ⟨(↑w⁻¹ : ℤ_[l]) * (l : ℤ_[l]) ^ (m - 1 - v), ?_⟩
  have hsplit : (l : ℤ_[l]) ^ (m - 1) = (l : ℤ_[l]) ^ v * (l : ℤ_[l]) ^ (m - 1 - v) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit]
  push_cast
  rw [← hw]
  calc (l : ℤ_[l]) ^ v * ↑w * (↑w⁻¹ * (l : ℤ_[l]) ^ (m - 1 - v))
      = (l : ℤ_[l]) ^ v * ((↑w * ↑w⁻¹) * (l : ℤ_[l]) ^ (m - 1 - v)) := by ring
    _ = (l : ℤ_[l]) ^ v * (l : ℤ_[l]) ^ (m - 1 - v) := by rw [Units.mul_inv, one_mul]

end GlobalTheory.PolynomialNormBound
end

