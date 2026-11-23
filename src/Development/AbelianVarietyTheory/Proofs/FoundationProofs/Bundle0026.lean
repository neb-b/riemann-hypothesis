module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqDiscriminantMulOfExpDecayCusps
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory

theorem discriminant_slash_specialLinearGroup (x : SL(2, ℤ)) :
    (ModularForm.discriminant ∣[(12 : ℤ)] x) = ModularForm.discriminant :=
  (isCF_coe_top CuspForm.discriminant).1 x (Subgroup.mem_top x)

theorem exists_eq_discriminant_mul (Γ : Subgroup SL(2, ℤ)) (K : ℤ) (H : ℍ → ℂ) (hH : IsMF Γ K H)
    (hdec : ∀ x : SL(2, ℤ), (H ∣[K] x) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) :
    ∃ G : ℍ → ℂ, IsMF Γ (K - 12) G ∧ H = ModularForm.discriminant * G := by
  have hsl : ∀ x : SL(2, ℤ), (H / ModularForm.discriminant) ∣[K - 12] x =
      (H ∣[K] x) / ModularForm.discriminant := by
    intro x
    have := ModularForm.div_slash_SL2 K 12 x H ModularForm.discriminant
    rw [discriminant_slash_specialLinearGroup] at this
    exact this
  refine ⟨H / ModularForm.discriminant, ⟨fun γ hγ => ?_, ?_, fun x => ?_⟩, ?_⟩
  · rw [hsl, hH.1 γ hγ]
  · exact hH.2.1.div CuspForm.discriminant.holo' ModularForm.discriminant_ne_zero
  · rw [hsl, IsBoundedAtImInfty, BoundedAtFilter]
    exact (Asymptotics.div_isBoundedUnder_of_isBigO ((hdec x).trans ModularForm.exp_isBigO_discriminant)).isBigO_one ℝ
  · ext τ
    simp [mul_div_cancel₀ _ (ModularForm.discriminant_ne_zero τ)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsExtensionOfDense
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem exists_extension_of_dense {X₀ X M : Type} [AddCommGroup X₀] [AddCommGroup X]
    [AddCommGroup M] [Module ℂ M] (ι : X₀ →+ X) (A : AddSubgroup X) (β : X → X → ℂ)
    (W₀ : X₀ → M →ₗ[ℂ] M)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z)
    (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hA : ∀ a ∈ A, ∀ b ∈ A, β a b = 1)
    (hβ : ∀ x, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ A, β x (m • a) = 1 ∧ β (m • a) x = 1)
    (hW : ∀ x y v, W₀ x (W₀ y v) = β (ι x) (ι y) • W₀ (x + y) v)
    (hd : ∀ (x : X) (m : ℕ), 0 < m → ∃ z, ∃ a ∈ A, ι z = x + m • a)
    (hs : ∀ v, ∃ m : ℕ, 0 < m ∧ ∀ z, (∃ a ∈ A, ι z = m • a) → W₀ z v = v) :
    ∃ W : X → M →ₗ[ℂ] M, (∀ z, W (ι z) = W₀ z) ∧
      (∀ x y v, W x (W y v) = β x y • W (x + y) v) ∧
      ∀ x v, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ A, W (x + m • a) v = W x v := by
  choose b hb0 hb using hβ
  have hb' : ∀ x (n : ℕ), b x ∣ n → ∀ a ∈ A, β x (n • a) = 1 ∧ β (n • a) x = 1 := by
    rintro x n ⟨k, rfl⟩ a ha
    rw [mul_smul]
    exact hb x _ (A.nsmul_mem ha k)
  have hex : ∀ (x : X) (v : M), ∃ G : M, ∃ m : ℕ, 0 < m ∧
      ∀ n : ℕ, m ∣ n → ∀ z, ∀ a ∈ A, ι z = x + n • a → W₀ z v = G := by
    intro x v
    obtain ⟨m, hm0, hm⟩ := hs v
    obtain ⟨z₁, a₁, ha₁, hz₁⟩ := hd x (m * b x) (Nat.mul_pos hm0 (hb0 x))
    refine ⟨W₀ z₁ v, m * b x, Nat.mul_pos hm0 (hb0 x), ?_⟩
    rintro n ⟨k, rfl⟩ z a ha hz
    rw [mul_smul] at hz
    have ha' : k • a ∈ A := A.nsmul_mem ha k
    have hsub : a₁ - k • a ∈ A := A.sub_mem ha₁ ha'
    have hιd : ι (z₁ - z) = (m * b x) • (a₁ - k • a) := by
      rw [map_sub, hz₁, hz, smul_sub]; abel
    have h1 : W₀ (z₁ - z) v = v :=
      hm _ ⟨b x • (a₁ - k • a), A.nsmul_mem hsub _, by rw [hιd, mul_smul]⟩
    have h2 := hW z (z₁ - z) v
    rw [h1, hιd, hz, hl, (hb' x _ (Dvd.intro_left m rfl) _ hsub).1,
      hA _ (A.nsmul_mem ha' _) _ (A.nsmul_mem hsub _), add_sub_cancel] at h2
    simpa using h2
  choose val lev hlev0 hlev using hex
  refine ⟨fun x =>
    { toFun := val x
      map_add' := ?_
      map_smul' := ?_ }, ?_, ?_, ?_⟩
  · intro v w
    obtain ⟨z, a, ha, hz⟩ := hd x (lev x v * lev x w * lev x (v + w))
      (Nat.mul_pos (Nat.mul_pos (hlev0 _ _) (hlev0 _ _)) (hlev0 _ _))
    rw [← hlev x v _ ⟨lev x w * lev x (v + w), by ring⟩ z a ha hz,
      ← hlev x w _ ⟨lev x v * lev x (v + w), by ring⟩ z a ha hz,
      ← hlev x (v + w) _ ⟨lev x v * lev x w, by ring⟩ z a ha hz, map_add]
  · intro c v
    obtain ⟨z, a, ha, hz⟩ := hd x (lev x v * lev x (c • v))
      (Nat.mul_pos (hlev0 _ _) (hlev0 _ _))
    rw [← hlev x v _ ⟨lev x (c • v), by ring⟩ z a ha hz,
      ← hlev x (c • v) _ ⟨lev x v, by ring⟩ z a ha hz, map_smul, RingHom.id_apply]
  · intro z
    ext v
    exact (hlev (ι z) v _ dvd_rfl z 0 A.zero_mem (by simp)).symm
  · intro x y v
    change val x (val y v) = β x y • val (x + y) v
    obtain ⟨n, hn0, h1, h2, h3, h4, h5⟩ : ∃ n : ℕ, 0 < n ∧ lev x (val y v) ∣ n ∧ lev y v ∣ n ∧
        lev (x + y) v ∣ n ∧ b x ∣ n ∧ b y ∣ n :=
      ⟨lev x (val y v) * lev y v * lev (x + y) v * b x * b y,
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (hlev0 _ _) (hlev0 _ _)) (hlev0 _ _))
          (hb0 _)) (hb0 _),
        ⟨lev y v * lev (x + y) v * b x * b y, by ring⟩,
        ⟨lev x (val y v) * lev (x + y) v * b x * b y, by ring⟩,
        ⟨lev x (val y v) * lev y v * b x * b y, by ring⟩,
        ⟨lev x (val y v) * lev y v * lev (x + y) v * b y, by ring⟩,
        ⟨lev x (val y v) * lev y v * lev (x + y) v * b x, by ring⟩⟩
    obtain ⟨z, a, ha, hz⟩ := hd x n hn0
    obtain ⟨w, c, hc, hw⟩ := hd y n hn0
    have hzw : ι (z + w) = x + y + n • (a + c) := by
      rw [map_add (f := _), hz, hw, smul_add]; abel
    have hβzw : β (ι z) (ι w) = β x y := by
      rw [hz, hw, hl, hr, hr, (hb' x n h4 c hc).1, (hb' y n h5 a ha).2,
        hA _ (A.nsmul_mem ha n) _ (A.nsmul_mem hc n)]
      ring
    rw [← hlev x (val y v) n h1 z a ha hz, ← hlev (x + y) v n h3 (z + w) _ (A.add_mem ha hc) hzw,
      ← hlev y v n h2 w c hc hw, hW, hβzw]
  · intro x v
    refine ⟨lev x v, hlev0 _ _, fun a ha => ?_⟩
    change val (x + lev x v • a) v = val x v
    obtain ⟨z, c, hc, hz⟩ := hd (x + lev x v • a) (lev x v * lev (x + lev x v • a) v)
      (Nat.mul_pos (hlev0 _ _) (hlev0 _ _))
    rw [← hlev _ v _ (Dvd.intro_left _ rfl) z c hc hz]
    refine hlev x v _ dvd_rfl z (a + lev (x + lev x v • a) v • c)
      (A.add_mem ha (A.nsmul_mem hc _)) ?_
    rw [hz, smul_add, mul_smul, add_assoc]

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePidSubalgebraDivPadicInt
section
namespace GlobalTheory

theorem exists_finite_pid_subalgebra_div_padicInt :
  ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgebraic ℤ_[p] s) →
  ∃ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R ∧ IsPrincipalIdealRing R ∧ ∀ s ∈ S, ∃ a ∈ R, ∃ b ∈ R, s = a / b := by
  intro p _ Ω _ _ hinj S hS
  haveI : FaithfulSMul ℤ_[p] Ω := (faithfulSMul_iff_algebraMap_injective ℤ_[p] Ω).mpr hinj
  letI : Algebra (FractionRing ℤ_[p]) Ω := FractionRing.liftAlgebra ℤ_[p] Ω
  haveI : IsScalarTower ℤ_[p] (FractionRing ℤ_[p]) Ω := FractionRing.isScalarTower_liftAlgebra ℤ_[p] Ω
  set L := IntermediateField.adjoin (FractionRing ℤ_[p]) (S : Set Ω) with hL
  haveI : FiniteDimensional (FractionRing ℤ_[p]) L := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    exact ((hS x hx).extendScalars (IsFractionRing.injective ℤ_[p] (FractionRing ℤ_[p]))).isIntegral
  haveI : Algebra.IsSeparable (FractionRing ℤ_[p]) L := inferInstance
  haveI : IsDedekindDomain (integralClosure ℤ_[p] L) :=
    integralClosure.isDedekindDomain ℤ_[p] (FractionRing ℤ_[p]) L
  haveI : Module.Finite ℤ_[p] (integralClosure ℤ_[p] L) :=
    IsIntegralClosure.finite ℤ_[p] (FractionRing ℤ_[p]) L (integralClosure ℤ_[p] L)
  have hPID : IsPrincipalIdealRing (integralClosure ℤ_[p] L) := by
    apply IsPrincipalIdealRing.of_finite_primes
    haveI := GlobalTheory.finite_maximalSpectrum_of_finite_of_isLocalRing ℤ_[p] (integralClosure ℤ_[p] L)
    apply ((Set.finite_range (fun M : MaximalSpectrum (integralClosure ℤ_[p] L) => M.asIdeal)).insert ⊥).subset
    intro I hI
    by_cases h : I = ⊥
    · exact Or.inl h
    · exact Or.inr ⟨⟨I, (show I.IsPrime from hI).isMaximal h⟩, rfl⟩
  let f : L →ₐ[ℤ_[p]] Ω :=
    { algebraMap L Ω with
      commutes' := fun r => by
        change ((algebraMap ℤ_[p] L r : L) : Ω) = _
        rw [IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p]) L r]
        exact (IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p]) Ω r).symm }
  have hf : Function.Injective f := Subtype.val_injective
  let e := Subalgebra.equivMapOfInjective (integralClosure ℤ_[p] L) f hf
  refine ⟨(integralClosure ℤ_[p] L).map f, Module.Finite.equiv e.toLinearEquiv,
    IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective, ?_⟩
  intro s hs
  obtain ⟨c, hc0, hci⟩ := (hS s hs).exists_integral_multiple
  have hsL : s ∈ L := IntermediateField.subset_adjoin _ _ hs
  refine ⟨c • s, ?_, algebraMap ℤ_[p] Ω c, Subalgebra.algebraMap_mem _ c, ?_⟩
  · rw [Subalgebra.mem_map]
    refine ⟨c • ⟨s, hsL⟩, ?_, rfl⟩
    show IsIntegral ℤ_[p] (c • (⟨s, hsL⟩ : L))
    rw [← isIntegral_algHom_iff f hf]
    exact hci
  · rw [Algebra.smul_def, mul_div_cancel_left₀ _ ((map_ne_zero_iff _ hinj).mpr hc0)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDlog
section
open GlobalTheory.K5 Polynomial

namespace GlobalTheory.K5

def dlogSub (p : ℕ) [Fact p.Prime] (n : ℕ) : Subalgebra (O0 p) (On p n) where
  carrier := {w | KaehlerDifferential.D (O0 p) (On p n) w ∈
    Submodule.span (On p n) ({KaehlerDifferential.D (O0 p) (On p n) (xn p n),
      KaehlerDifferential.D (O0 p) (On p n) (yn p n)} : Set _)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Derivation.leibniz] at *
    exact add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ ha)
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add (f := _)] at *
    exact add_mem ha hb
  algebraMap_mem' := by
    intro r
    simp only [Set.mem_setOf_eq, Derivation.map_algebraMap]
    exact zero_mem _

theorem mem_dlogSub (p : ℕ) [Fact p.Prime] (n : ℕ) (w : On p n) : w ∈ dlogSub p n := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hx : xn p n ∈ dlogSub p n :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hy : yn p n ∈ dlogSub p n :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hC : ∀ a : Polynomial (O0 p), Ideal.Quotient.mk (towerIdeal p n) (C a) ∈ dlogSub p n := by
    intro a
    induction a using Polynomial.induction_on with
    | C r =>
      have : Ideal.Quotient.mk (towerIdeal p n) (C (C r)) = algebraMap (O0 p) (On p n) r := rfl
      rw [this]; exact Subalgebra.algebraMap_mem _ r
    | add a b ha hb => rw [Polynomial.C_add, RingHom.map_add (Ideal.Quotient.mk (towerIdeal p n))]; exact add_mem ha hb
    | monomial k r _ =>
      rw [Polynomial.C_mul, Polynomial.C_pow, map_mul, map_pow]
      refine mul_mem ?_ (pow_mem hx _)
      have : Ideal.Quotient.mk (towerIdeal p n) (C (C r)) = algebraMap (O0 p) (On p n) r := rfl
      rw [this]; exact Subalgebra.algebraMap_mem _ r
  induction f using Polynomial.induction_on with
  | C a => exact hC a
  | add a b ha hb => rw [RingHom.map_add (Ideal.Quotient.mk (towerIdeal p n))]; exact add_mem ha hb
  | monomial k a _ =>
    rw [map_mul, map_pow]
    exact mul_mem (hC a) (pow_mem hy _)

theorem exists_isDlog : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (w : (On p n)ˣ), ∃ α β : On p n, IsDlog p n (w : On p n) α β := by
  intro p _ n w
  have h : KaehlerDifferential.D (O0 p) (On p n) (w : On p n) ∈
      Submodule.span (On p n) ({KaehlerDifferential.D (O0 p) (On p n) (xn p n),
        KaehlerDifferential.D (O0 p) (On p n) (yn p n)} : Set _) := mem_dlogSub p n (w : On p n)
  obtain ⟨P, Q, hPQ⟩ := Submodule.mem_span_pair.mp h
  refine ⟨yn p n * Q * ((w⁻¹ : (On p n)ˣ) : On p n), xn p n * P * ((w⁻¹ : (On p n)ˣ) : On p n), ?_⟩
  unfold IsDlog
  rw [← hPQ, smul_add, smul_smul, smul_smul, add_comm]
  congr 1
  · congr 1
    have := w.mul_inv
    linear_combination (xn p n * yn p n * Q) * (-this)
  · congr 1
    have := w.mul_inv
    linear_combination (xn p n * yn p n * P) * (-this)

end GlobalTheory.K5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOfMemAdjoin
section
noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
open Polynomial

namespace GlobalTheory.K5.Level

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

abbrev Bn (T : Tower p Ω) (n : ℕ) : Subalgebra (O0 p) Ω :=
  Algebra.adjoin (O0 p) {T.ζ n, T.qq n}

theorem bn_le_succ (T : Tower p Ω) (n : ℕ) : Bn T n ≤ Bn T (n + 1) := by
  rw [Algebra.adjoin_le_iff]
  rintro x (rfl | rfl)
  · rw [← T.ζpow n]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) _
  · rw [← T.qpow n]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) _

theorem bn_mono (T : Tower p Ω) : Monotone (Bn T) :=
  monotone_nat_of_le_succ (bn_le_succ T)

theorem bn_le_B (T : Tower p Ω) (n : ℕ) :
    Bn T n ≤ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  apply Algebra.adjoin_mono
  rintro x (rfl | rfl)
  · exact Or.inl ⟨n, rfl⟩
  · exact Or.inr ⟨n, rfl⟩

theorem exists_mem_bn (T : Tower p Ω) {b : Ω}
    (hb : b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq)) : ∃ n, b ∈ Bn T n := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · exact ⟨n, Algebra.subset_adjoin (by simp)⟩
    · exact ⟨n, Algebra.subset_adjoin (by simp)⟩
  | algebraMap r => exact ⟨0, Subalgebra.algebraMap_mem _ r⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨k, hk⟩ := hy
    exact ⟨max m k, Subalgebra.add_mem _ (bn_mono T (le_max_left m k) hm)
      (bn_mono T (le_max_right m k) hk)⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨k, hk⟩ := hy
    exact ⟨max m k, Subalgebra.mul_mem _ (bn_mono T (le_max_left m k) hm)
      (bn_mono T (le_max_right m k) hk)⟩

theorem bn_le_range (T : Tower p Ω) (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (h : IsEmb T n ι) :
    Bn T n ≤ ι.range := by
  rw [Algebra.adjoin_le_iff]
  rintro x (rfl | rfl)
  · exact ⟨xn p n, h.1⟩
  · exact ⟨yn p n, h.2⟩

theorem range_le_bn (T : Tower p Ω) (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (h : IsEmb T n ι)
    (w : On p n) : ι w ∈ Bn T n := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hX : ι (Ideal.Quotient.mk (towerIdeal p n) (C X)) ∈ Bn T n := by
    have : ι (xn p n) = T.ζ n := h.1
    simp only [xn] at this
    rw [this]; exact Algebra.subset_adjoin (by simp)
  have hY : ι (Ideal.Quotient.mk (towerIdeal p n) X) ∈ Bn T n := by
    have : ι (yn p n) = T.qq n := h.2
    simp only [yn] at this
    rw [this]; exact Algebra.subset_adjoin (by simp)
  have hC : ∀ a : Polynomial (O0 p), ι (Ideal.Quotient.mk (towerIdeal p n) (C a)) ∈ Bn T n := by
    intro a
    induction a using Polynomial.induction_on with
    | C c =>
      have : (Ideal.Quotient.mk (towerIdeal p n) (C (C c))) = algebraMap (O0 p) (On p n) c := rfl
      rw [this, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ c
    | add f g hf hg =>
      set_option synthInstance.maxHeartbeats 200000 in
        simpa only [map_add] using Subalgebra.add_mem (Bn T n) hf hg
    | monomial k c _ =>
      simp only [map_mul, map_pow]
      refine Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ hX _)
      have : (Ideal.Quotient.mk (towerIdeal p n) (C (C c))) = algebraMap (O0 p) (On p n) c := rfl
      rw [this, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ c
  induction P using Polynomial.induction_on with
  | C a => exact hC a
  | add f g hf hg =>
    set_option synthInstance.maxHeartbeats 200000 in
      simpa only [map_add] using Subalgebra.add_mem (Bn T n) hf hg
  | monomial k a _ =>
    simp only [map_mul, map_pow]
    exact Subalgebra.mul_mem _ (hC a) (Subalgebra.pow_mem _ hY _)

end GlobalTheory.K5.Level

theorem GlobalTheory.K5.exists_level_of_mem_adjoin :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
      ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq),
        ∃ (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (w : On p n), 1 ≤ n ∧ IsEmb T n ι ∧ ι w = b ∧
          ∀ w' : On p n, ι w' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq) := by
  intro p _ Ω _ _ _ T b hb
  obtain ⟨m, hm⟩ := GlobalTheory.K5.Level.exists_mem_bn T hb
  have hm1 : b ∈ GlobalTheory.K5.Level.Bn T (m + 1) := GlobalTheory.K5.Level.bn_le_succ T m hm
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T (m + 1)
  obtain ⟨w, hw⟩ := GlobalTheory.K5.Level.bn_le_range T (m + 1) ι hι hm1
  exact ⟨m + 1, ι, w, Nat.le_add_left 1 m, hι, hw, fun w' =>
    GlobalTheory.K5.Level.bn_le_B T (m + 1) (GlobalTheory.K5.Level.range_le_bn T (m + 1) ι hι w')⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOneFormOneAddExpDecay
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory

theorem levelOne_form_one_add_expDecay :
    ∀ d : ℤ, 4 ≤ d → Even d → ∃ e : ℍ → ℂ, IsMF ⊤ d e ∧
      (fun τ : ℍ => e τ - 1) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  intro d hd hev
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ d)
  have hk : 3 ≤ k := by omega
  have hk2 : Even k := by simpa [Int.even_coe_nat] using hev
  let f : ModularForm 𝒮ℒ (k : ℤ) := ModularForm.E hk
  refine ⟨f, isMF_coe_top f, ?_⟩
  have h0 : valueAtInfty (f : ℍ → ℂ) = 1 := by
    rw [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)]
    exact EisensteinSeries.E_qExpansion_coeff_zero hk hk2
  have h := exp_decay_sub_atImInfty one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)
  rw [h0] at h
  simpa using h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalFiniteIndexFixing
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_normal_finiteIndex_fixing (L : Type) [Field L] (G : Type) [Group G]
    [MulSemiringAction G L] (S : Finset L) (hS : ∀ s ∈ S, (MulAction.orbit G s).Finite) :
    ∃ U : Subgroup G, U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix L U) ∧
      ∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x := by
  classical
  set T : Set L := ⋃ s ∈ S, MulAction.orbit G s with hT
  have hTfin : T.Finite := Set.Finite.biUnion S.finite_toSet (fun s hs => hS s hs)
  have hTstab : ∀ g : G, ∀ x ∈ T, g • x ∈ T := by
    intro g x hx
    simp only [hT, Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hx⟩ := hx
    exact ⟨s, hs, MulAction.mem_orbit_of_mem_orbit g hx⟩
  set F : Finset L := hTfin.toFinset
  have hF : ∀ x, x ∈ F ↔ x ∈ T := fun x => hTfin.mem_toFinset
  let U : Subgroup G := ⨅ x ∈ F, MulAction.stabilizer G x
  have hU : ∀ g : G, g ∈ U ↔ ∀ x ∈ T, g • x = x := by
    intro g
    simp only [U, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff, hF]
  have hST : ∀ s ∈ S, s ∈ T := by
    intro s hs
    simp only [hT, Set.mem_iUnion]
    exact ⟨s, hs, MulAction.mem_orbit_self s⟩
  have hFix : ∀ x ∈ T, x ∈ Fix L U := by
    intro x hx
    change ∀ m : U, m • x = x
    rintro ⟨g, hg⟩
    exact (hU g).1 hg x hx
  refine ⟨U, ?_, ?_, fun s hs => hFix s (hST s hs), ?_⟩
  · refine ⟨fun n hn g => ?_⟩
    rw [hU] at hn ⊢
    intro x hx
    have := hn (g⁻¹ • x) (hTstab g⁻¹ x hx)
    rw [mul_smul, mul_smul, this, smul_inv_smul]
  · refine Subgroup.finiteIndex_iInf' _ (fun x hx => ?_)
    refine ⟨?_⟩
    rw [MulAction.index_stabilizer]
    have hx' := (hF x).1 hx
    simp only [hT, Set.mem_iUnion] at hx'
    obtain ⟨s, hs, hxs⟩ := hx'
    rw [MulAction.orbit_eq_iff.mpr hxs]
    exact (Set.ncard_pos (hS s hs)).mpr ⟨s, MulAction.mem_orbit_self s⟩ |>.ne'
  · intro h hh
    rw [hU] at hh
    push_neg at hh
    obtain ⟨x, hx, hne⟩ := hh
    exact ⟨x, hFix x hx, hne⟩

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesShiftTwistStatement
section
open Complex Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lSeries_twist_natPow_eq_shift : ∀ (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → LSeries (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) = LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) := by
  first | exact @GlobalTheory.lseries_shift_twist | exact GlobalTheory.lseries_shift_twist | (intros; apply GlobalTheory.lseries_shift_twist <;> assumption)
end

