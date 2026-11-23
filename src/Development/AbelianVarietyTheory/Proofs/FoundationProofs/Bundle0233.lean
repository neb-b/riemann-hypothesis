module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.FinWeil

def sgO (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E := MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj

theorem coe_sgO (D : D7) (r : 𝓞 D.host.E) : ((sgO D r : 𝓞 D.host.E) : D.host.E) = D.host.conj (r : D.host.E) := rfl

abbrev XA (D : D7) (N N' : ℕ) : Type := Matrix (Fin N') (Fin N) (AE D)

theorem smul_AE (D : D7) (r : 𝓞 D.host.E) (y : AE D) : r • y = inc D (r : D.host.E) * y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.smul_tmul']
    simp [inc, Formalism.UG.inclE, Algebra.smul_def]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

theorem ihE_mul (D : D7) (cc : Ideal (𝓞 D.host.K)) {s t : AE D} (hs : s ∈ OhE D) (ht : t ∈ IhE D cc) : s * t ∈ IhE D cc := by
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, s', hs', rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, s * s', mul_mem hs hs', by ring⟩
  | zero => simpa using zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

def latA (D : D7) (cc : Ideal (𝓞 D.host.K)) (N N' : ℕ) : Submodule (𝓞 D.host.E) (XA D N N') where
  carrier := {ζ | ∀ i j, ζ i j ∈ IhE D cc}
  add_mem' := fun ha hb i j => add_mem (ha i j) (hb i j)
  zero_mem' := fun _ _ => zero_mem _
  smul_mem' := fun r ζ h i j => by
    rw [Matrix.smul_apply, smul_AE]
    exact ihE_mul D cc ((AdLattice.incl_mem_iff (F := ℚ) _).2 ⟨r, rfl⟩) (h i j)

theorem mem_latA {D : D7} {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} {ζ : XA D N N'} :
    ζ ∈ latA D cc N N' ↔ ∀ i j, ζ i j ∈ IhE D cc := Iff.rfl

def actA (D : D7) (N N' : ℕ) : GA D N × GA D N' →* Module.End (𝓞 D.host.E) (XA D N N') where
  toFun u :=
    { toFun := fun ζ => ((u.2 : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * ζ *
        (((u.1 : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
      map_add' := fun x y => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r x => by
        have h : ∀ {a b : ℕ} (y : Matrix (Fin a) (Fin b) (AE D)), r • y = inc D (r : D.host.E) • y := fun y => by
          ext i j
          rw [Matrix.smul_apply, Matrix.smul_apply, smul_AE, smul_eq_mul]
        rw [RingHom.id_apply, h, h, Matrix.mul_smul, Matrix.smul_mul] }
  map_one' := by
    ext1 ζ
    simp
  map_mul' u v := by
    ext1 ζ
    simp [Matrix.mul_assoc]

theorem actA_apply {D : D7} {N N' : ℕ} (g : GA D N) (g' : GA D N') (ζ : XA D N N') :
    actA D N N' (g, g') ζ = ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * ζ *
      (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := rfl

theorem wd_add {D : D7} {T : Tor D} {N N' : ℕ} (x : VC D N N') (F G : VC D N N' → ℂ) :
    Wd D T x (F + G) = Wd D T x F + Wd D T x G := by
  funext z
  simp only [Wd, U, Pi.add_apply]
  ring

theorem wd_smul {D : D7} {T : Tor D} {N N' : ℕ} (x : VC D N N') (c : ℂ) (F : VC D N N' → ℂ) :
    Wd D T x (c • F) = c • Wd D T x F := by
  funext z
  simp only [Wd, U, Pi.smul_apply, smul_eq_mul]
  ring

def TTs (D : D7) (T : Tor D) (N N' : ℕ) : Submodule ℂ (VC D N N' → ℂ) where
  carrier := TT D T N N'
  add_mem' := by
    rintro F G ⟨hF, m, hm, h⟩ ⟨hG, n, hn, h'⟩
    refine ⟨hF.add hG, m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩
    rw [wd_add]
    congr 1
    · rw [mul_smul]; exact h _ (AddSubgroup.nsmul_mem _ hx n)
    · rw [mul_comm, mul_smul]; exact h' _ (AddSubgroup.nsmul_mem _ hx m)
  zero_mem' := ⟨differentiable_const _, 1, one_pos, fun x _ => by funext z; simp [Wd, U]⟩
  smul_mem' := by
    rintro c F ⟨hF, m, hm, h⟩
    exact ⟨hF.const_smul c, m, hm, fun x hx => by rw [wd_smul, h x hx]⟩

def psi0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : D.host.E) : ℂ :=
  ee (-(‖δ‖ ^ 2 / area (lamOf D cc δ) * (∑ τ, embT D τ a).im))

def IsPsi (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (ψ : AE D → ℂ) : Prop :=
  (∀ x y, ψ (x + y) = ψ x * ψ y) ∧ ψ 0 = 1 ∧ (∀ a, ψ (inc D a) = psi0 D cc δ a) ∧ (∀ y, ψ (y + sgA D y) = 1) ∧
    ∃ m : ℕ, 0 < m ∧ ∀ s ∈ OhE D, ψ ((m : AE D) * s) = 1

def gamA {D : D7} (ψ : AE D → ℂ) {N N' : ℕ} (ζ η : XA D N N') : ℂ := ψ (∑ i, ∑ j, ζ i j * sgA D (η i j))

def IsModel (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (w : 𝓞 D.host.E) (γ : XA D N N' → XA D N N' → ℂ)
    (WA : XA D N N' → TTs D (tor0 D cc δ) N N' →ₗ[ℂ] TTs D (tor0 D cc δ) N N') : Prop :=
  IsHeis (sgO D) w γ WA ∧ SelfDual γ (latA D cc N N') ∧
  (∀ u ζ η, γ (actA D N N' u ζ) (actA D N N' u η) = γ ζ η) ∧
  (∀ (z : Matrix (Fin N') (Fin N) D.host.E) (F : TTs D (tor0 D cc δ) N N'),
    (WA (z.map (inc D)) F : VC D N N' → ℂ) = Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F) ∧
  ∀ ζ F, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ latA D cc N N', WA (ζ + m • a) F = WA ζ F

end GlobalTheory.FinWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdaptedPointChangeOfRationalBasis
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.AdaptedBasis

theorem exists_denominator {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] (κ : ι → K) :
    ∃ R : ℕ, 0 < R ∧ ∃ a : ι → 𝓞 K, ∀ i, (a i : K) = (R : K) * κ i := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image κ)
  have h' : ∀ i, IsIntegral ℤ (((y.natAbs : ℕ) : K) * κ i) := by
    intro i
    have hi := h (κ i) (Finset.mem_image_of_mem κ (Finset.mem_univ i))
    rw [zsmul_eq_mul] at hi
    rcases Int.natAbs_eq y with e | e
    · have : ((y.natAbs : ℕ) : K) = (y : K) := by
        conv_rhs => rw [e]
        simp only [Int.cast_natCast]
      rw [this]; exact hi
    · have : ((y.natAbs : ℕ) : K) = -(y : K) := by
        conv_rhs => rw [e]
        simp only [Int.cast_neg, Int.cast_natCast, neg_neg]
      rw [this, neg_mul]; exact hi.neg
  exact ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i => ⟨_, h' i⟩, fun i => rfl⟩

theorem embV_sum (D : D7) (T : Tor D) (h0 : ∀ τ, T.emb τ 0 = 0)
    (hadd : ∀ τ x y, T.emb τ (x + y) = T.emb τ x + T.emb τ y)
    (hmul : ∀ τ (a : D.host.K) y, T.emb τ ((a : D.host.E) * y) = D.host.φ₀ (a : D.host.E) * T.emb τ y)
    {N N' r : ℕ} (B : Fin r → Matrix (Fin N') (Fin N) D.host.E) (κ : Fin r → D.host.K) :
    embV D T (∑ i, κ i • B i) = ∑ i, D.host.φ₀ (κ i : D.host.E) • embV D T (B i) := by
  funext τ p q
  let f : D.host.E →+ ℂ := ⟨⟨T.emb τ, h0 τ⟩, hadd τ⟩
  have e : (∑ i, κ i • B i) p q = ∑ i, (κ i : D.host.E) * B i p q := by
    rw [Matrix.sum_apply]
    rfl
  have e2 : T.emb τ (∑ i, (κ i : D.host.E) * B i p q) = ∑ i, T.emb τ ((κ i : D.host.E) * B i p q) :=
    map_sum f _ _
  simp only [embV, e, e2, hmul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem liftM_of_mem (M : IntermediateField ℚ ℂ) {x : ℂ} (h : x ∈ M) : liftM M x = ⟨x, h⟩ := dif_pos h

theorem sum_smul_comm {V : Type*} [AddCommGroup V] [Module ℂ V] {r s : ℕ} (c : Fin s → ℂ) (k : Fin s → Fin r → ℂ)
    (v : Fin r → V) : ∑ j, c j • ∑ i, k j i • v i = ∑ i, (∑ j, k j i * c j) • v i := by
  simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem rationalLatticePoint_add {Λ : AddSubgroup ℂ} {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) : InRationalLattice Λ (x + y) := by
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨n, hn, hy⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have : ((m * n : ℕ) : ℂ) * (x + y) = n • ((m : ℂ) * x) + m • ((n : ℂ) * y) := by
    simp only [nsmul_eq_mul]; push_cast; ring
  rw [this]
  exact Λ.add_mem (Λ.nsmul_mem hx n) (Λ.nsmul_mem hy m)

theorem adpB_of_family : ∀ (D : D7), admG1 D → galStar D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ → DataIn D (tor0 D cc δ) M → ∀ (N N' r s : ℕ) (B : Fin r → Matrix (Fin N') (Fin N) D.host.E) (b : Fin s → Matrix (Fin N') (Fin N) D.host.E), OnB D B → ∃ R : ℕ, 0 < R ∧ ∀ (n : ℕ) (c c' : Fin s → ℂ), 0 < n → (∀ j, InRationalLattice (lamOf D cc δ) (c j)) → (∀ j, Adp1 M ρ (lamOf D cc δ) (n * R) (c j) (c' j)) → AdpB D (tor0 D cc δ) M ρ B n (∑ j, c j • embV D (tor0 D cc δ) (b j)) (∑ j, c' j • embV D (torConj D (tor0 D cc δ) M ρ) (b j)) := by
  intro D hG hS cc δ hC M ρ hF hD N N' r s B b hB
  have hspan : ∀ j, ∃ κ : Fin r → D.host.K, ∑ i, κ i • B i = b j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun D.host.K).1 (by rw [hB.2]; trivial)
  choose κ hκ using hspan
  obtain ⟨R, hR, a, ha⟩ := exists_denominator (fun p : Fin s × Fin r => κ p.1 p.2)
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have haφ : ∀ j i, D.host.φ₀ (((a (j, i) : D.host.K) : D.host.E)) = R * D.host.φ₀ (κ j i : D.host.E) := by
    intro j i
    rw [ha]
    push_cast
    rw [map_mul, map_natCast]
  have hΛ := (GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hC).2.2.2.2
  obtain ⟨-, -, -, hadd, hmul, -⟩ := hS cc δ hC M ρ hF hD.2.1 hD.2.2
  have hM : ∀ τ x, embT D τ x ∈ M := hD.1
  have hψ := hG.1
  have e1 : ∀ j, embV D (tor0 D cc δ) (b j) =
      ∑ i, D.host.φ₀ (κ j i : D.host.E) • embV D (tor0 D cc δ) (B i) := by
    intro j
    rw [← hκ j]
    refine embV_sum D _ (fun τ => map_zero (embT D τ)) (fun τ => map_add (embT D τ)) (fun τ k y => ?_) B _
    show embT D τ _ = _ * embT D τ y
    rw [map_mul, hψ]
  have e2 : ∀ j, embV D (torConj D (tor0 D cc δ) M ρ) (b j) =
      ∑ i, D.host.φ₀ (κ j i : D.host.E) • embV D (torConj D (tor0 D cc δ) M ρ) (B i) := by
    intro j
    rw [← hκ j]
    refine embV_sum D _ (fun τ => ?_) (fun τ x y => ?_) (fun τ k y => ?_) B _
    · show ρ (liftM M (embT D τ 0)) = 0
      rw [map_zero, liftM_of_mem M (zero_mem M)]
      exact map_zero ρ
    · show ρ (liftM M (embT D τ (x + y))) = ρ (liftM M (embT D τ x)) + ρ (liftM M (embT D τ y))
      rw [liftM_of_mem M (hM τ _), liftM_of_mem M (hM τ _), liftM_of_mem M (hM τ _), ← map_add ρ]
      congr 1
      exact Subtype.ext (map_add (embT D τ) x y)
    · show ρ (liftM M (embT D τ (_ * y))) = _ * ρ (liftM M (embT D τ y))
      rw [← (hF k).2, cj, liftM_of_mem M (hM τ _), liftM_of_mem M (hM τ _), liftM_of_mem M (hF k).1, ← map_mul ρ]
      congr 1
      apply Subtype.ext
      show embT D τ (_ * y) = D.host.φ₀ _ * embT D τ y
      rw [map_mul, hψ]
  refine ⟨R, hR, fun n c c' hn hc hA => ⟨fun i => ∑ j, D.host.φ₀ (κ j i : D.host.E) * c j,
    fun i => ∑ j, D.host.φ₀ (κ j i : D.host.E) * c' j, fun i => ?_, ?_, ?_, fun i => ?_⟩⟩
  · refine Finset.sum_induction _ (InRationalLattice (lamOf D cc δ)) (fun x y => rationalLatticePoint_add)
      ⟨1, one_pos, by simp⟩ (fun j _ => ?_)
    obtain ⟨m, hm, hj⟩ := hc j
    refine ⟨R * m, Nat.mul_pos hR hm, ?_⟩
    have := hΛ (a (j, i)) _ hj
    rw [haφ] at this
    convert this using 1
    push_cast; ring
  · simp only [e1]; exact sum_smul_comm _ _ _
  · simp only [e2]; exact sum_smul_comm _ _ _
  · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have key : ∀ t : Finset (Fin s), StarPt M ρ (lamOf D cc δ)
        ((∑ j ∈ t, D.host.φ₀ (κ j i : D.host.E) * c j) / n) ((∑ j ∈ t, D.host.φ₀ (κ j i : D.host.E) * c' j) / n) := by
      intro t
      induction t using Finset.induction_on with
      | empty => left; simp
      | insert j t hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, add_div, add_div]
        refine hadd _ _ _ _ ?_ ih
        have := hmul (a (j, i)) _ _ (hA j)
        rw [haφ] at this
        convert this using 1 <;> (push_cast; field_simp)
    exact key Finset.univ

end GlobalTheory.AdaptedBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdaptedTorsionLiftDeeperLevel
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalTheta

theorem adapted_lift_deeper : ∀ (D : D7), galStar D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, FixK D ⊤ σ → ∀ (c c' : ℂ) (n₀ n : ℕ), 0 < n₀ → 0 < n → InRationalLattice (lamOf D cc δ) c → Adp1 ⊤ σ (lamOf D cc δ) n₀ c c' → ∃ ω ∈ lamOf D cc δ, Adp1 ⊤ σ (lamOf D cc δ) (n₀ * n) (c + (n₀ : ℂ) * ω) c' := by
  intro D hS cc δ hC σ hσ c c' n₀ n h₀ hn hc hA
  obtain ⟨-, -, -, h4, h5, h6, h7⟩ := hS cc δ hC ⊤ σ hσ IntermediateField.mem_top IntermediateField.mem_top
  obtain ⟨k, hk, hkc⟩ := hc
  have e₀ : (n₀ : ℂ) ≠ 0 := by exact_mod_cast h₀.ne'
  have e₁ : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold Adp1 at hA ⊢
  have a1 : ((k * n₀ : ℕ) : ℂ) * (c / (n₀ : ℂ)) ∈ lamOf D cc δ := by
    have : ((k * n₀ : ℕ) : ℂ) * (c / (n₀ : ℂ)) = (k : ℂ) * c := by
      push_cast; field_simp
    rw [this]; exact hkc
  have a2 := (h6 _ _ _ hA).1 a1
  have a3 : ((k * n₀ * n : ℕ) : ℂ) * (c' / ((n₀ * n : ℕ) : ℂ)) ∈ lamConj ⊤ σ (lamOf D cc δ) := by
    have : ((k * n₀ * n : ℕ) : ℂ) * (c' / ((n₀ * n : ℕ) : ℂ)) = ((k * n₀ : ℕ) : ℂ) * (c' / (n₀ : ℂ)) := by
      push_cast; field_simp
    rw [this]; exact a2
  obtain ⟨u, -, hu⟩ := h7 (k * n₀ * n) (by positivity)
    (fun _ _ _ => ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩) _ a3
  have b1 := h5 (n : 𝓞 D.host.K) _ _ hu
  have b2 := h5 (-1 : 𝓞 D.host.K) _ _ hA
  have c1 : D.host.φ₀ ((((n : 𝓞 D.host.K) : D.host.K) : D.host.E)) = (n : ℂ) := by simp
  have c2 : D.host.φ₀ ((((-1 : 𝓞 D.host.K) : D.host.K) : D.host.E)) = (-1 : ℂ) := by simp
  rw [c1] at b1
  rw [c2] at b2
  have b3 := h4 _ _ _ _ b1 b2
  have z : (n : ℂ) * (c' / ((n₀ * n : ℕ) : ℂ)) + -1 * (c' / (n₀ : ℂ)) = 0 := by
    push_cast; field_simp; ring
  rw [z] at b3
  have b4 := (h6 1 _ _ b3).2 (by simp)
  rw [Nat.cast_one, one_mul] at b4
  refine ⟨_, b4, ?_⟩
  have : (c + (n₀ : ℂ) * ((n : ℂ) * u + -1 * (c / (n₀ : ℂ)))) / ((n₀ * n : ℕ) : ℂ) = u := by
    push_cast; field_simp; ring
  rw [this]; exact hu

end GlobalTheory.GalTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory NumberField GlobalTheory.Mem.Vol Matrix Topology

namespace GlobalTheory.Mem.Vol.Scale

variable {n P Q : ℕ} {ε : Fin n → Bool}

def Sorts (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) : Prop :=
  (∀ i, ε (e (Sum.inl i)) = true) ∧ ∀ j, ε (e (Sum.inr j)) = false

theorem Sorts.reindex_Jpq {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) :
    Matrix.reindex e e (Formalism.UG.Jpq P Q) = Formalism.REAL.Jm ε := by
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Formalism.REAL.Jm,
    Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq, Formalism.UG.Jpq]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, h.1, h.2]
  split_ifs <;> simp

theorem Sorts.card_true {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) : Nat.card {a // ε a = true} = P := by
  have : Function.Bijective fun i : Fin P => (⟨e (Sum.inl i), h.1 i⟩ : {a // ε a = true}) := by
    refine ⟨fun i j hij => Sum.inl_injective (e.injective (congrArg Subtype.val hij)), ?_⟩
    rintro ⟨a, ha⟩
    obtain ⟨b | b, rfl⟩ := e.surjective a
    · exact ⟨b, rfl⟩
    · rw [h.2] at ha; cases ha
  rw [← Nat.card_eq_of_bijective _ this]; simp

theorem Sorts.add_eq (e : Fin P ⊕ Fin Q ≃ Fin n) : P + Q = n := by
  simpa using Fintype.card_congr e

theorem exists_sorts (ε : Fin n → Bool) : ∃ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n), Sorts ε e := by
  refine ⟨_, _, (Equiv.sumCongr (Fintype.equivFin {a // ε a = true}).symm
    (Fintype.equivFin {a // ¬ ε a = true}).symm).trans (Equiv.sumCompl fun a => ε a = true), fun i => ?_, fun j => ?_⟩
  · exact ((Fintype.equivFin {a // ε a = true}).symm i).2
  · exact Bool.eq_false_iff.2 ((Fintype.equivFin {a // ¬ ε a = true}).symm j).2

def reindexUnits (e : Fin P ⊕ Fin Q ≃ Fin n) :
    GL (Fin P ⊕ Fin Q) ℂ ≃ₜ* (Matrix (Fin n) (Fin n) ℂ)ˣ where
  toMulEquiv := Units.mapEquiv (Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv
  continuous_toFun := Units.continuous_map
    (f := ((Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv.toMonoidHom))
    (continuous_id.matrix_reindex _ _)
  continuous_invFun := Units.continuous_map
    (f := ((Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv.symm.toMonoidHom))
    ((continuous_id.matrix_reindex e.symm e.symm).congr fun _ => rfl)

theorem reindexUnits_val (e : Fin P ⊕ Fin Q ≃ Fin n) (g : GL (Fin P ⊕ Fin Q) ℂ) :
    (reindexUnits e g : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.reindex e e (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := rfl

theorem Sorts.mem_iff {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) (g : GL (Fin P ⊕ Fin Q) ℂ) :
    reindexUnits e g ∈ Formalism.REAL.UJ ε ↔ g ∈ Formalism.UG.Upq P Q := by
  change Formalism.REAL.inUJ ε (reindexUnits e g : Matrix (Fin n) (Fin n) ℂ) ↔
    (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).conjTranspose * Formalism.UG.Jpq P Q *
      (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) = Formalism.UG.Jpq P Q
  rw [Formalism.REAL.inUJ, reindexUnits_val, ← h.reindex_Jpq, Matrix.conjTranspose_reindex]
  rw [← (Matrix.reindex (α := ℂ) e e).injective.eq_iff]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

def Sorts.equiv {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) : UpqT P Q ≃ₜ* Formalism.REAL.UJ ε where
  toFun g := ⟨reindexUnits e (g : Formalism.UG.Upq P Q).1, (h.mem_iff _).2 (g : Formalism.UG.Upq P Q).2⟩
  invFun k := (⟨(reindexUnits e).symm k.1, (h.mem_iff _).1 (by simpa using k.2)⟩ : Formalism.UG.Upq P Q)
  left_inv g := Subtype.ext ((reindexUnits e).symm_apply_apply _)
  right_inv k := Subtype.ext ((reindexUnits e).apply_symm_apply _)
  map_mul' g k := Subtype.ext (map_mul (reindexUnits e) _ _)
  continuous_toFun := ((reindexUnits e).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((reindexUnits e).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem Sorts.umat_equiv {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) (g : UpqT P Q) :
    umat (h.equiv g) = Matrix.reindex e e (UpqT.mat g) := rfl

theorem umat_injective : Function.Injective (umat : Formalism.REAL.UJ ε → _) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem Sorts.set_eq {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) (A : Set (Formalism.REAL.UJ ε)) :
    {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)} = h.equiv ⁻¹' A := by
  ext g
  constructor
  · rintro ⟨a, ha, hg⟩
    rw [← h.umat_equiv] at hg
    rw [Set.mem_preimage, ← umat_injective hg]
    exact ha
  · intro hg
    exact ⟨_, hg, rfl⟩

theorem Sorts.exists_conj {e e' : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) (h' : Sorts ε e') :
    ∃ u : UpqT P Q, ∀ g, h'.equiv g = h.equiv (u * g * u⁻¹) := by
  set σ : Fin P ⊕ Fin Q ≃ Fin P ⊕ Fin Q := e.trans e'.symm with hσ
  have hJ : (Formalism.UG.Jpq P Q).submatrix σ σ = Formalism.UG.Jpq P Q := by
    apply (Matrix.reindex (α := ℂ) e e).injective
    rw [h.reindex_Jpq, ← h'.reindex_Jpq]
    ext i j
    simp [hσ]
  have hmem : (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).submatrix σ id ∈
      Set.range (UpqT.mat (P := P) (Q := Q)) := by
    rw [GlobalTheory.UpqTopology.range_mat]
    change _ = _
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
    conv_lhs => rw [← hJ]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    simp
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u, fun g => ?_⟩
  rw [← h.equiv.symm_apply_eq, eq_mul_inv_iff_mul_eq]
  apply GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective
  have h1 : UpqT.mat (h.equiv.symm (h'.equiv g)) = (UpqT.mat g).submatrix σ σ := by
    apply (Matrix.reindex (α := ℂ) e e).injective
    rw [← h.umat_equiv, h.equiv.apply_symm_apply, h'.umat_equiv]
    ext i j
    simp [hσ]
  change UpqT.mat (h.equiv.symm (h'.equiv g)) * UpqT.mat u = UpqT.mat u * UpqT.mat g
  rw [h1, hu, Matrix.submatrix_mul_equiv, Matrix.mul_one]
  have := Matrix.submatrix_mul_equiv (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (UpqT.mat g) σ
    (Equiv.refl _) id
  simpa using this.symm

theorem Sorts.measurable_equiv {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) : Measurable h.equiv := by
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  exact h.equiv.continuous.measurable

theorem Sorts.map_eq (cd : CDHaar) {P' Q' : ℕ} {e : Fin P ⊕ Fin Q ≃ Fin n} {e' : Fin P' ⊕ Fin Q' ≃ Fin n}
    (h : Sorts ε e) (h' : Sorts ε e') : (cd.cd P' Q').map h'.equiv = (cd.cd P Q).map h.equiv := by
  obtain rfl : P = P' := h.card_true.symm.trans h'.card_true
  obtain rfl : Q = Q' := by
    have h1 := Sorts.add_eq e
    have h2 := Sorts.add_eq e'
    omega
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  haveI := cd.haar P Q
  haveI := GlobalTheory.UpqHaarRight.isMulRightInvariant P Q _ (cd.haar P Q)
  obtain ⟨u, hu⟩ := h.exists_conj h'
  have : (h'.equiv : UpqT P Q → Formalism.REAL.UJ ε) = h.equiv ∘ (fun g => g * u⁻¹) ∘ fun g => u * g := funext hu
  rw [this, ← Measure.map_map h.measurable_equiv ((measurable_mul_const _).comp (measurable_const_mul _)),
    ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self,
    map_mul_right_eq_self]

theorem Sorts.exists_scale (cd : CDHaar) {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) :
    ∃ c : NNReal, 0 < c ∧ (cd.cd P Q).map h.equiv = (c : ENNReal) • Formalism.REAL.muG ε := by
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  haveI := cd.haar P Q
  haveI : ((cd.cd P Q).map h.equiv).IsHaarMeasure := h.equiv.isHaarMeasure_map _
  exact ⟨_, Measure.haarScalarFactor_pos_of_isHaarMeasure _ _,
    Measure.isMulLeftInvariant_eq_smul ((cd.cd P Q).map h.equiv) (Formalism.REAL.muG ε)⟩

theorem exists_cdScaleIs (cd : CDHaar) :
    ∃ sc : ∀ n : ℕ, (Fin n → Bool) → NNReal, (∀ n ε, 0 < sc n ε) ∧ CdScaleIs cd sc := by
  choose P Q e he using fun (n : ℕ) (ε : Fin n → Bool) => exists_sorts ε
  choose sc hpos hsc using fun (n : ℕ) (ε : Fin n → Bool) => (he n ε).exists_scale cd
  refine ⟨sc, hpos, fun n ε P' Q' e' h1 h2 A hA => ?_⟩
  have h' : Sorts ε e' := ⟨h1, h2⟩
  rw [h'.set_eq, ← Measure.map_apply h'.measurable_equiv hA, (he n ε).map_eq cd h', hsc]

theorem cdScaleIs_trueScale : ∀ cd : CDHaar, CdScaleIs cd (trueScale cd) := by
  intro cd
  unfold trueScale
  rw [dite_eq_left (exists_cdScaleIs cd)]
  exact (Classical.choose_spec (exists_cdScaleIs cd)).2

theorem cdScaleIs_unique (cd : CDHaar) {sc sc' : ∀ n : ℕ, (Fin n → Bool) → NNReal}
    (h : CdScaleIs cd sc) (h' : CdScaleIs cd sc') : sc = sc' := by
  funext n ε
  obtain ⟨P, Q, e, he⟩ := exists_sorts ε
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Formalism.REAL.UJ ε)) := inferInstance
  have hm : MeasurableSet (K : Set (Formalism.REAL.UJ ε)) := K.isCompact.measurableSet
  have h0 : Formalism.REAL.muG ε K ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have ht : Formalism.REAL.muG ε K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have := (h n ε P Q e he.1 he.2 K hm).trans (h' n ε P Q e he.1 he.2 K hm).symm
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul] at this
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 ht).1 this)

end GlobalTheory.Mem.Vol.Scale
end
end

