module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjAlgApply
section
namespace GlobalTheory.ConjugateAlgebraLemmas

open Matrix

def conjAlg {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) K where
  toFun M := ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * (g : Matrix (Fin n) (Fin n) K)
  map_one' := by simp
  map_mul' M N := by
    have h : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (M * N) * (g : Matrix (Fin n) (Fin n) K)
        = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * ((g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * N * (g : Matrix (Fin n) (Fin n) K) := by rw [h, Matrix.mul_one, Matrix.mul_assoc ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M N]
      _ = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * (g : Matrix (Fin n) (Fin n) K) * (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N * (g : Matrix (Fin n) (Fin n) K)) := by simp only [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' M N := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by
    have h : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h]

theorem conjAlg_apply {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) (M : Matrix (Fin n) (Fin n) K) :
    conjAlg g M = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * (g : Matrix (Fin n) (Fin n) K) := rfl

theorem aeval_conj {K : Type} [Field K] {n : ℕ} (γ g : GL (Fin n) K) (Q : Polynomial K) :
    Polynomial.aeval ((↑(g⁻¹ * γ * g) : Matrix (Fin n) (Fin n) K)) Q
      = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q * (g : Matrix (Fin n) (Fin n) K) := by
  have h : ((↑(g⁻¹ * γ * g) : Matrix (Fin n) (Fin n) K)) = conjAlg g (γ : Matrix (Fin n) (Fin n) K) := by
    rw [conjAlg_apply, Units.val_mul, Units.val_mul]
  rw [h, Polynomial.aeval_algHom_apply, conjAlg_apply]

theorem gram_eq {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : (g.map σ)ᵀ * g = 1) (a b : Fin n → K) :
    ∑ k : Fin n, σ ((g *ᵥ a) k) * (g *ᵥ b) k = ∑ k : Fin n, σ (a k) * b k := by
  have h1 : ∀ k, σ ((g *ᵥ a) k) = ((g.map σ) *ᵥ (fun i => σ (a i))) k := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp_rw [h1]
  change (g.map σ *ᵥ fun i => σ (a i)) ⬝ᵥ (g *ᵥ b) = (fun i => σ (a i)) ⬝ᵥ b
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hg, Matrix.vecMul_one]

theorem main : ∀ {K : Type} [inst : Field K] (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K), Matrix.transpose (Matrix.map (↑g : Matrix (Fin n) (Fin n) K) (⇑σ : K → K)) * (↑g : Matrix (Fin n) (Fin n) K) = (1 : Matrix (Fin n) (Fin n) K) → ∀ (Q : Polynomial K) {ι : Type} (u : ι → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = LinearMap.ker ((Matrix.toLin' : Matrix (Fin n) (Fin n) K → (Fin n → K) →ₗ[K] Fin n → K) ((Polynomial.aeval (↑(g⁻¹ * γ * g) : Matrix (Fin n) (Fin n) K) : Polynomial K → Matrix (Fin n) (Fin n) K) Q)) → (LinearIndependent K fun (i : ι) ↦ Matrix.mulVec (↑g : Matrix (Fin n) (Fin n) K) (u i)) ∧ Submodule.span K (Set.range fun (i : ι) ↦ Matrix.mulVec (↑g : Matrix (Fin n) (Fin n) K) (u i)) = LinearMap.ker ((Matrix.toLin' : Matrix (Fin n) (Fin n) K → (Fin n → K) →ₗ[K] Fin n → K) ((Polynomial.aeval (↑γ : Matrix (Fin n) (Fin n) K) : Polynomial K → Matrix (Fin n) (Fin n) K) Q)) ∧ ((Matrix.of : (ι → ι → K) → Matrix ι ι K) fun (i j : ι) ↦ ∑ k : Fin n, (σ : K → K) (Matrix.mulVec (↑g : Matrix (Fin n) (Fin n) K) (u i) k) * Matrix.mulVec (↑g : Matrix (Fin n) (Fin n) K) (u j) k) = (Matrix.of : (ι → ι → K) → Matrix ι ι K) fun (i j : ι) ↦ ∑ k : Fin n, (σ : K → K) (u i k) * u j k := by
  intro K _ σ n γ g hg Q ι u hu hspan
  have hgg : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgg' : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨?_, ?_, ?_⟩
  · have hinj : Function.Injective (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) := by
      intro x y hxy
      have h := congrArg (fun z => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z) hxy
      simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hgg'] using h
    exact hu.map' (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) (LinearMap.ker_eq_bot.mpr hinj)
  · have hmap : Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) =
        (Submodule.span K (Set.range u)).map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmap, hspan, aeval_conj]
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker, Matrix.toLin'_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      calc Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ x)
          = (g : Matrix (Fin n) (Fin n) K) *ᵥ ((((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q * (g : Matrix (Fin n) (Fin n) K)) *ᵥ x) := by
            simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hgg, Matrix.one_mul]
        _ = 0 := by rw [hx, Matrix.mulVec_zero]
    · intro hy
      refine ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y, ?_, ?_⟩
      · calc (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q * (g : Matrix (Fin n) (Fin n) K)) *ᵥ
              (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y)
            = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
              (Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q *ᵥ y) := by
              simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hgg, Matrix.mul_one]
          _ = 0 := by rw [hy, Matrix.mulVec_zero]
      · rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  · ext i j
    simp only [Matrix.of_apply]
    exact gram_eq σ (g : Matrix (Fin n) (Fin n) K) hg (u i) (u j)

end GlobalTheory.ConjugateAlgebraLemmas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjDualPartsKilledOfPerfectPairing
section
namespace GlobalTheory.DualParts

theorem card_le_of_injective_chars (G H : Type) [CommGroup G] [Finite G] (U : Type) [CommRing U]
    [IsDomain U] (f : H → (G →* Uˣ)) (hf : Function.Injective f) :
    Finite H ∧ Nat.card H ≤ Nat.card G := by
  classical
  haveI := Fintype.ofFinite G
  let g : H → (G →* U) := fun h => (Units.coeHom U).comp (f h)
  have hg : Function.Injective g := by
    intro a b hab
    apply hf
    refine MonoidHom.ext fun x => Units.ext ?_
    have := congrArg (fun χ : G →* U => χ x) hab
    simpa [g] using this
  have hli : LinearIndependent U (fun h => (g h : G → U)) :=
    (linearIndependent_monoidHom G U).comp g hg
  haveI : Finite H := hli.finite
  haveI := Fintype.ofFinite H
  refine ⟨inferInstance, ?_⟩
  have := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at this
  simpa [Nat.card_eq_fintype_card] using this

theorem conj_dual_parts : ∀ (O : Type) [CommRing O] (bar : O →+* O) (U : Type) [CommRing U] [IsDomain U] (M M' : Type) [CommGroup M] [CommGroup M'] (α : O → M →* M) (α' : O → M' →* M'), (∀ y, α 1 y = y) → (∀ a b y, α (a * b) y = α a (α b y)) → (∀ a b y, α (a + b) y = α a y * α b y) → (∀ x, α' 1 x = x) → (∀ a b x, α' (a * b) x = α' a (α' b x)) → (∀ a b x, α' (a + b) x = α' a x * α' b x) → (∀ a, bar (bar a) = a) → ∀ (e : M' →* M →* Uˣ) (e' : M →* M' →* Uˣ), Function.Injective e → Function.Injective e' → (∀ a x y, e (α' a x) y = e x (α (bar a) y)) → (∀ a y x, e' (α a y) x = e' y (α' (bar a) x)) → ∀ (u w : Ideal O) (n : ℕ), u ≤ w → u ⊔ u.map bar = ⊤ → (∀ a ∈ (u * u.map bar) ^ n, (∀ y, α a y = 1) ∧ ∀ x, α' a x = 1) → (∀ y, (∃ m : ℕ, ∀ a ∈ u ^ m, α a y = 1) → ∀ a ∈ w, α a y = 1) → Finite {y : M // ∀ a ∈ w, α a y = 1} → (∀ x, (∃ m : ℕ, ∀ a ∈ (u.map bar) ^ m, α' a x = 1) → ∀ a ∈ w.map bar, α' a x = 1) ∧ Nat.card {x : M' // ∀ a ∈ w.map bar, α' a x = 1} = Nat.card {y : M // ∀ a ∈ w, α a y = 1} := by
  intro O _ bar U _ _ M M' _ _ α α' h1 hmul hadd h1' hmul' hadd' hbb e e' he he' hee hee' u w n huw hcop
    hkill hw hfin
  have hsurj : Function.Surjective bar := fun a => ⟨bar a, hbb a⟩
  have hbarbar : (u.map bar).map bar = u := by
    rw [Ideal.map_map]
    have : bar.comp bar = RingHom.id O := RingHom.ext hbb
    rw [this, Ideal.map_id]
  have hsplit : ∀ k : ℕ, ∃ a₀ ∈ u ^ k, ∃ b₀ ∈ (u.map bar) ^ k, a₀ + b₀ = 1 := by
    intro k
    have hc : IsCoprime u (u.map bar) := Ideal.isCoprime_iff_sup_eq.2 hcop
    have hs : u ^ k ⊔ (u.map bar) ^ k = ⊤ := Ideal.isCoprime_iff_sup_eq.1 (hc.pow)
    have h1mem : (1 : O) ∈ u ^ k ⊔ (u.map bar) ^ k := by rw [hs]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1mem
    exact ⟨a, ha, b, hb, hab⟩
  have hbar1 : ∀ k, ∀ a ∈ u ^ k, bar a ∈ (u.map bar) ^ k := by
    intro k a ha
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem bar ha
  have hbar2 : ∀ k, ∀ b ∈ (u.map bar) ^ k, bar b ∈ u ^ k := by
    intro k b hb
    have := Ideal.mem_map_of_mem bar hb
    rwa [Ideal.map_pow, hbarbar] at this
  have hprod : ∀ k, n ≤ k → ∀ a ∈ u ^ k, ∀ b ∈ (u.map bar) ^ k, a * b ∈ (u * u.map bar) ^ n := by
    intro k hk a ha b hb
    have : a * b ∈ (u * u.map bar) ^ k := by rw [mul_pow]; exact Ideal.mul_mem_mul ha hb
    exact Ideal.pow_le_pow_right hk this
  have hpowle : ∀ (I : Ideal O) (k m : ℕ), m ≤ k → I ^ k ≤ I ^ m := fun I k m h =>
    Ideal.pow_le_pow_right h

  have part1 : ∀ x, (∃ m : ℕ, ∀ a ∈ (u.map bar) ^ m, α' a x = 1) → ∀ a ∈ w.map bar, α' a x = 1 := by
    rintro x ⟨m, hm⟩ c hc
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective bar hsurj).1 hc
    apply he
    rw [map_one]
    refine MonoidHom.ext fun y => ?_
    rw [MonoidHom.one_apply, hee, hbb]
    obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := hsplit (m + n)
    have hy : y = α a₀ y * α b₀ y := by rw [← hadd, hab, h1]
    rw [hy, map_mul, map_mul]
    have t1 : e x (α a (α a₀ y)) = 1 := by
      rw [← hmul, ← hbb (a * a₀), ← hee, map_mul bar, hmul',
        hm (bar a₀) (hpowle _ (m + n) m (by omega) (hbar1 _ a₀ ha₀))]
      simp
    have t2 : α a (α b₀ y) = 1 := by
      refine hw (α b₀ y) ⟨m + n, fun c hc => ?_⟩ a ha
      rw [← hmul]; exact (hkill _ (hprod (m + n) (by omega) c hc b₀ hb₀)).1 y
    rw [t1, t2, map_one, one_mul]
  refine ⟨part1, ?_⟩

  obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := hsplit (n + 1)
  let A : Subgroup M :=
    { carrier := {y | ∀ a ∈ w, α a y = 1}
      one_mem' := fun a _ => map_one (α a)
      mul_mem' := fun {y z} hy hz a ha => by
        rw [map_mul, (show ∀ a ∈ w, α a y = 1 from hy) a ha,
          (show ∀ a ∈ w, α a z = 1 from hz) a ha, one_mul]
      inv_mem' := fun {y} hy a ha => by
        rw [map_inv, (show ∀ a ∈ w, α a y = 1 from hy) a ha, inv_one] }
  let B : Subgroup M' :=
    { carrier := {x | ∀ a ∈ w.map bar, α' a x = 1}
      one_mem' := fun a _ => map_one (α' a)
      mul_mem' := fun {y z} hy hz a ha => by
        rw [map_mul, (show ∀ a ∈ w.map bar, α' a y = 1 from hy) a ha,
          (show ∀ a ∈ w.map bar, α' a z = 1 from hz) a ha, one_mul]
      inv_mem' := fun {y} hy a ha => by
        rw [map_inv, (show ∀ a ∈ w.map bar, α' a y = 1 from hy) a ha, inv_one] }
  have hu1 : u ^ (n + 1) ≤ u := Ideal.pow_le_self (by omega)
  have hub1 : (u.map bar) ^ (n + 1) ≤ u.map bar := Ideal.pow_le_self (by omega)

  have F1 : ∀ y, α b₀ y ∈ A := by
    intro y
    refine hw (α b₀ y) ⟨n + 1, fun c hc => ?_⟩
    rw [← hmul]; exact (hkill _ (hprod (n + 1) (by omega) c hc b₀ hb₀)).1 y
  have F2 : ∀ x ∈ B, α' (bar a₀) x = 1 := fun x hx =>
    hx _ (Ideal.map_mono huw (hub1 (hbar1 _ a₀ ha₀)))
  have E1 : ∀ x ∈ B, ∀ y, e x y = e x (α b₀ y) := by
    intro x hx y
    conv_lhs => rw [← h1 y, ← hab, hadd, map_mul]
    rw [← hbb a₀, ← hee, F2 x hx]
    simp
  have F3 : ∀ x, α' a₀ x ∈ B := by
    intro x
    refine part1 (α' a₀ x) ⟨n + 1, fun c hc => ?_⟩
    rw [← hmul', mul_comm]; exact (hkill _ (hprod (n + 1) (by omega) a₀ ha₀ c hc)).2 x
  have F4 : ∀ y ∈ A, α (bar b₀) y = 1 := fun y hy => hy _ (huw (hu1 (hbar2 _ b₀ hb₀)))
  have E2 : ∀ y ∈ A, ∀ x, e' y x = e' y (α' a₀ x) := by
    intro y hy x
    conv_lhs => rw [← h1' x, ← hab, hadd', map_mul]
    rw [← hbb b₀, ← hee', F4 y hy]
    simp
  haveI : Finite A := hfin
  have hAB : Finite B ∧ Nat.card B ≤ Nat.card A := by
    refine card_le_of_injective_chars A B U (fun x => (e x.1).comp A.subtype) ?_
    intro x₁ x₂ h
    apply Subtype.ext
    apply he
    refine MonoidHom.ext fun y => ?_
    rw [E1 x₁.1 x₁.2, E1 x₂.1 x₂.2]
    exact congrArg (fun χ : A →* Uˣ => χ ⟨α b₀ y, F1 y⟩) h
  haveI : Finite B := hAB.1
  have hBA : Finite A ∧ Nat.card A ≤ Nat.card B := by
    refine card_le_of_injective_chars B A U (fun y => (e' y.1).comp B.subtype) ?_
    intro y₁ y₂ h
    apply Subtype.ext
    apply he'
    refine MonoidHom.ext fun x => ?_
    rw [E2 y₁.1 y₁.2, E2 y₂.1 y₂.2]
    exact congrArg (fun χ : B →* Uˣ => χ ⟨α' a₀ x, F3 x⟩) h
  exact le_antisymm hAB.2 hBA.2

end GlobalTheory.DualParts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTransposeMulMulSelfOfUnitaryConj
section
open scoped ComplexOrder
open Matrix

namespace GlobalTheory


open scoped ComplexOrder in
open Matrix in
theorem _root_.GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj :
    ∀ (n d : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ) (Xb Yb : Matrix (Fin n) (Fin d) ℂ) (y₀ : GL (Fin d) ℂ),
    J.conjTranspose = J → P.conjTranspose = P → Xb.conjTranspose * J * Xb = 0 → Yb.conjTranspose * J * Yb = 0 →
    Xb.conjTranspose * J * Yb = 1 →
    P * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) → P * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) →
    ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
      let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
      let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
      G.conjTranspose * P * G = P := by
  intro n d J P X Y y₀ hJ hP hXX hYY hXY hPX hPY k hk m G
  have hki : (k⁻¹).1 = k.1ᴴ := by
    calc (k⁻¹).1 = (k.1ᴴ * k.1) * (k⁻¹).1 := by rw [hk, Matrix.one_mul]
      _ = k.1ᴴ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hm : m.1 = y₀.1 * k.1 * (y₀⁻¹).1 := by simp [m]
  have hmi : (m⁻¹).1 = y₀.1 * k.1ᴴ * (y₀⁻¹).1 := by
    simp only [m, _root_.mul_inv_rev, inv_inv, Units.val_mul, hki, Matrix.mul_assoc]
  have hab : y₀.1ᴴ * (y₀⁻¹).1ᴴ = 1 := by
    rw [← conjTranspose_mul, Units.inv_mul, conjTranspose_one]
  have hAm : m.1ᴴ * ((y₀⁻¹).1ᴴ * (y₀⁻¹).1) * m.1 = (y₀⁻¹).1ᴴ * (y₀⁻¹).1 := by
    rw [hm]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc y₀.1ᴴ, hab, Matrix.one_mul, ← Matrix.mul_assoc (y₀⁻¹).1 y₀.1, Units.inv_mul,
      Matrix.one_mul, ← Matrix.mul_assoc k.1ᴴ k.1, hk, Matrix.one_mul]
  have hBm : (m⁻¹).1 * (y₀.1 * y₀.1ᴴ) * (m⁻¹).1ᴴ = y₀.1 * y₀.1ᴴ := by
    rw [hmi]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (y₀⁻¹).1 y₀.1, Units.inv_mul, Matrix.one_mul, ← Matrix.mul_assoc y₀.1ᴴ, hab,
      Matrix.one_mul, ← Matrix.mul_assoc k.1ᴴ k.1, hk, Matrix.one_mul]
  have hAh : ((y₀⁻¹).1ᴴ * (y₀⁻¹).1)ᴴ = (y₀⁻¹).1ᴴ * (y₀⁻¹).1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have hBh : (y₀.1 * y₀.1ᴴ)ᴴ = y₀.1 * y₀.1ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [G]
  generalize (y₀⁻¹).1ᴴ * (y₀⁻¹).1 = A at hPX hAm hAh
  generalize y₀.1 * y₀.1ᴴ = B at hPY hBm hBh
  generalize m.1 = m₁ at hAm
  generalize (m⁻¹).1 = m₂ at hBm
  have hYX : Yᴴ * J * X = 1 := by
    have h := congrArg conjTranspose hXY
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using h
  have hXP : Xᴴ * P = A * (Yᴴ * J) := by
    have h := congrArg conjTranspose hPX
    simpa [conjTranspose_mul, hJ, hP, hAh, Matrix.mul_assoc] using h
  have hYP : Yᴴ * P = B * (Xᴴ * J) := by
    have h := congrArg conjTranspose hPY
    simpa [conjTranspose_mul, hJ, hP, hBh, Matrix.mul_assoc] using h
  have r1 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Xᴴ * (J * (X * Z)) = 0 := fun Z => by
    simp only [← Matrix.mul_assoc, hXX, Matrix.zero_mul]
  have r2 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Yᴴ * (J * (Y * Z)) = 0 := fun Z => by
    simp only [← Matrix.mul_assoc, hYY, Matrix.zero_mul]
  have r3 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Xᴴ * (J * (Y * Z)) = Z := fun Z => by
    simp only [← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have r4 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), Yᴴ * (J * (X * Z)) = Z := fun Z => by
    simp only [← Matrix.mul_assoc, hYX, Matrix.one_mul]
  have r5 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), P * (X * Z) = J * (Y * (A * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hPX]
  have r6 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), P * (Y * Z) = J * (X * (B * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hPY]
  have r7 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin n) c ℂ), Xᴴ * (P * Z) = A * (Yᴴ * (J * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hXP]
  have r8 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin n) c ℂ), Yᴴ * (P * Z) = B * (Xᴴ * (J * Z)) := fun Z => by
    simp only [← Matrix.mul_assoc, hYP]
  have r9 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), m₁ᴴ * (A * (m₁ * Z)) = A * Z := fun Z => by
    simp only [← Matrix.mul_assoc, hAm]
  have r10 : ∀ {c : Type} [Fintype c] (Z : Matrix (Fin d) c ℂ), m₂ * (B * (m₂ᴴ * Z)) = B * Z := fun Z => by
    simp only [← Matrix.mul_assoc, hBm]
  simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_one,
    conjTranspose_conjTranspose, hJ, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, hXP, hYP,
    Matrix.mul_zero, Matrix.zero_mul, sub_zero, add_zero, zero_add]
  abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffHasse
section
namespace GlobalTheory.PicDiv

variable {R : Type*} [CommRing R]

noncomputable def hasse (l : ℕ) : PowerSeries R →ₗ[R] PowerSeries R where
  toFun φ := PowerSeries.mk fun n => ((n + l).choose l : R) * PowerSeries.coeff (n + l) φ
  map_add' φ ψ := by ext n; simp [mul_add]
  map_smul' c φ := by ext n; simp [mul_left_comm]

theorem coeff_hasse (l n : ℕ) (φ : PowerSeries R) :
    PowerSeries.coeff n (hasse l φ) = ((n + l).choose l : R) * PowerSeries.coeff (n + l) φ := by
  simp [hasse]

theorem constantCoeff_hasse (l : ℕ) (φ : PowerSeries R) :
    PowerSeries.constantCoeff (hasse l φ) = PowerSeries.coeff l φ := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_hasse]; simp

theorem coeff_one_hasse (l : ℕ) (φ : PowerSeries R) :
    PowerSeries.coeff 1 (hasse l φ) = ((l + 1 : ℕ) : R) * PowerSeries.coeff (l + 1) φ := by
  rw [coeff_hasse, add_comm 1 l, Nat.choose_succ_self_right]

theorem hasse_zero (φ : PowerSeries R) : hasse 0 φ = φ := by
  ext n; simp [coeff_hasse]

end GlobalTheory.PicDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffTsumOfLocallySummableBounds
section
open scoped ContDiff

namespace GlobalTheory

theorem contDiff_tsum_of_locally_summable_bounds {k : ℕ} {ι : Type} (f : ι → (Fin k → ℝ) → ℂ)
    (hf : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i))
    (hu : ∀ (n : ℕ) (R : ℝ), ∃ u : ι → ℝ, Summable u ∧
      ∀ i t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (f i) t‖ ≤ u i) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, f i t) := by
  choose u hus hub using hu
  have hinf : ((⊤ : ℕ∞) : WithTop ℕ∞) = ∞ := rfl
  rw [hinf] at hf ⊢
  rw [contDiff_infty]
  intro n
  rw [contDiff_iff_contDiffAt]
  intro t₀
  let ρ : ContDiffBump t₀ := ⟨1/2, 1, by norm_num, by norm_num⟩
  set R : ℝ := ‖t₀‖ + 1 with hR
  let ρc : (Fin k → ℝ) → ℂ := fun t => ((ρ t : ℝ) : ℂ)
  have hρc : ContDiff ℝ ∞ ρc := Complex.ofRealCLM.contDiff.comp ρ.contDiff
  have hρcs : HasCompactSupport ρc := ρ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hB : ∀ j : ℕ, ∃ B, ∀ x, ‖iteratedFDeriv ℝ j ρc x‖ ≤ B := fun j =>
    (hρc.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hρcs.iteratedFDeriv j)
  choose B hB using hB
  have hsupp : ∀ j x, x ∉ Metric.closedBall t₀ 1 → iteratedFDeriv ℝ j ρc x = 0 := by
    intro j x hx
    by_contra h
    have hx1 : x ∈ tsupport ρc := support_iteratedFDeriv_subset j h
    have h2 : tsupport ρc ⊆ tsupport (ρ : (Fin k → ℝ) → ℝ) :=
      tsupport_comp_subset Complex.ofReal_zero _
    rw [ρ.tsupport_eq] at h2
    exact hx (h2 hx1)
  have hunonneg : ∀ m i, 0 ≤ u m R i := fun m i =>
    (norm_nonneg _).trans (hub m R i 0 (by rw [norm_zero, hR]; positivity))
  have hB0 : ∀ j, 0 ≤ B j := fun j => (norm_nonneg _).trans (hB j 0)
  let v : ℕ → ι → ℝ := fun m i =>
    ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * B j * u (m - j) R i
  have hv : ∀ m, Summable (v m) := fun m => by
    apply summable_sum
    intro j _
    exact (hus (m - j) R).mul_left _
  have hbound : ∀ m i x, ‖iteratedFDeriv ℝ m (fun y => ρc y * f i y) x‖ ≤ v m i := by
    intro m i x
    refine (norm_iteratedFDeriv_mul_le hρc (hf i) x (by exact_mod_cast le_top)).trans ?_
    apply Finset.sum_le_sum
    intro j _
    by_cases hx : x ∈ Metric.closedBall t₀ 1
    · have hxR : ‖x‖ ≤ R := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hx
        have := norm_sub_norm_le x t₀
        rw [hR]; linarith
      apply mul_le_mul _ (hub _ _ _ _ hxR) (norm_nonneg _)
        (mul_nonneg (by positivity) (hB0 j))
      exact mul_le_mul_of_nonneg_left (hB j x) (by positivity)
    · rw [hsupp j x hx, norm_zero, mul_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (by positivity) (hB0 j)) (hunonneg _ _)
  have hsm : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, ρc t * f i t) :=
    contDiff_tsum (fun i => (hρc.mul (hf i)).of_le (by exact_mod_cast le_top))
      (fun m _ => hv m) (fun m i x _ => hbound m i x)
  have heq : (fun t => ∑' i, f i t) =ᶠ[nhds t₀] (fun t => ∑' i, ρc t * f i t) := by
    filter_upwards [Metric.closedBall_mem_nhds t₀ (by norm_num : (0:ℝ) < 1/2)] with t ht
    rw [tsum_mul_left]
    have h1 : ρ t = 1 := ρ.one_of_mem_closedBall ht
    simp [ρc, h1]
  exact (hsm.contDiffAt).congr_of_eventuallyEq heq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfForallExistsFix
section
universe u_1 u_2 u_3 u_4

namespace GlobalTheory.ContinuityFromFixedPoints

open Topology

theorem continuous_of_forall_exists_fix {k : Type u_1} {F : Type u_2} {k' : Type u_3}
    {F' : Type u_4} [Field k] [Field F] [Algebra k F] [Field k'] [Field F'] [Algebra k' F']
    [Algebra.IsIntegral k F] (φ : Gal(F/k) →* Gal(F'/k'))
    (h : ∀ y : F', ∃ x : F, ∀ σ : Gal(F/k), σ x = x → φ σ y = y) :
    Continuous φ := by
  classical
  choose x hx using h
  refine continuous_of_continuousAt_one φ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E', hE', hs'⟩ := (krullTopology_mem_nhds_one_iff k' F' s).1 hs
  let b := Module.finBasis k' E'
  let S : Set F := Set.range fun i => x (b i : F')
  have hS : S.Finite := Set.finite_range _
  haveI : Finite S := hS.to_subtype
  have hfin : FiniteDimensional k (IntermediateField.adjoin k S) :=
    IntermediateField.finiteDimensional_adjoin fun z _ => Algebra.IsIntegral.isIntegral z
  rw [Filter.mem_map]
  refine (krullTopology_mem_nhds_one_iff k F _).2 ⟨IntermediateField.adjoin k S, hfin, ?_⟩
  intro σ hσ
  apply hs'
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  have hb : ∀ i, φ σ (b i : F') = b i := fun i =>
    hx _ σ (hσ _ (IntermediateField.subset_adjoin k S ⟨i, rfl⟩))
  intro y hy
  have hlin : ((φ σ).toLinearMap ∘ₗ E'.val.toLinearMap) = E'.val.toLinearMap :=
    b.ext fun i => by simpa using hb i
  simpa using LinearMap.congr_fun hlin ⟨y, hy⟩

end GlobalTheory.ContinuityFromFixedPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicThreeRoots
section
namespace GlobalTheory.CMModel

theorem cubic_three_roots (g h e₁ e₂ e₃ : ℂ) (h₁ : 4 * e₁ ^ 3 - g * e₁ - h = 0)
    (h₂ : 4 * e₂ ^ 3 - g * e₂ - h = 0) (h₃ : 4 * e₃ ^ 3 - g * e₃ - h = 0)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) :
    (∀ x, 4 * x ^ 3 - g * x - h = 4 * (x - e₁) * (x - e₂) * (x - e₃)) ∧
      16 * ((3 * e₁ ^ 2 - g / 4) * (3 * e₂ ^ 2 - g / 4) * (3 * e₃ ^ 2 - g / 4))
        = -(g ^ 3 - 27 * h ^ 2) := by
  have a : g = 4 * (e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2) := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₂)
    linear_combination h₂ - h₁
  have b : g = 4 * (e₁ ^ 2 + e₁ * e₃ + e₃ ^ 2) := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₃)
    linear_combination h₃ - h₁
  have c : e₃ = -e₁ - e₂ := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₂₃)
    linear_combination (b - a) / 4
  have d : h = 4 * e₁ ^ 3 - g * e₁ := by linear_combination -h₁
  subst c
  rw [d, a]
  exact ⟨fun x => by ring, by ring⟩

end GlobalTheory.CMModel
end

