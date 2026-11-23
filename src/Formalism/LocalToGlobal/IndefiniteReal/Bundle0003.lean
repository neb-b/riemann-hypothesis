module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0002
public import Lemmata.RankOneOrbitForms.RankOneForm

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.ExistsStrictHenselianAbsolutelyClosedLocalRing
section
open Module NumberField

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement

namespace NormTraceLemmas

section Lin

variable {K : Type} [Field K] {G : Type} [Group G]
  {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]

theorem exists_strictHenselian_absolutely_closed_local_ring (τ : Representation K G T)
    (hirr : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ε₀ ε : T →ₗ[K] T) (h1 : finrank K (LinearMap.range ε₀) = 1) :
    ∃ (γ δ : Fin (finrank K (LinearMap.range ε)) → G)
      (c : Matrix (Fin (finrank K (LinearMap.range ε))) (Fin (finrank K (LinearMap.range ε))) K),
      c.det ≠ 0 ∧
      (∀ i j, c i j = LinearMap.trace K T (ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j))) ∧
      (∀ i j, ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j) ∘ₗ ε₀ = c i j • ε₀) ∧
      ∑ j, ∑ i, c⁻¹ j i • (ε ∘ₗ τ (γ j) ∘ₗ ε₀ ∘ₗ τ (δ i) ∘ₗ ε) = ε := by
  first | exact Bl.RankOneOrbitForms.goal1 .. | (apply Bl.RankOneOrbitForms.goal1 <;> assumption) | (intros; apply Bl.RankOneOrbitForms.goal1 <;> assumption)

end Lin

section Char

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
  {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]


open Classical in
theorem trace_formula (τ : Representation K G T) (H₀ H : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ)
    (χ : H →* (𝓞 K)ˣ) (a b : G) :
    LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b) =
      ((Nat.card H₀ : K)⁻¹ * (Nat.card H : K)⁻¹) *
        ∑ h₀ : H₀, ∑ h : H, ((((χ₀ h₀⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) *
          (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) * charOf τ ((h₀ : G) * a * h * b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← Module.End.mul_eq_comp, epP, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, map_smul, map_sum, smul_eq_mul, ← map_mul, charOf, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h₀ _ => Finset.sum_congr rfl fun h _ => ?_
  rw [map_mul (algebraMap (𝓞 K) K)]
  ring

theorem norm_chi (H : Subgroup G) [Finite H] (χ : H →* (𝓞 K)ˣ) (h : H) (σ : K →+* ℂ) :
    ‖σ (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K)‖ = 1 := by
  have hu : ((χ h : (𝓞 K)ˣ) : 𝓞 K) ^ Nat.card H = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  have h2 : σ (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) ^ Nat.card H = 1 := by
    have := congrArg (σ.comp (algebraMap (𝓞 K) K)) hu
    rw [map_pow, map_one] at this
    exact this
  exact Complex.norm_eq_one_of_pow_eq_one h2 Nat.card_pos.ne'

variable [NumberField K]

theorem norm_trace_le (hC : CharFacts) (τ : Representation K G T) (H₀ H : Subgroup G)
    (χ₀ : H₀ →* (𝓞 K)ˣ) (χ : H →* (𝓞 K)ˣ) (a b : G) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b))‖ ≤ (finrank K T : ℝ) := by
  classical
  rw [trace_formula, map_mul, norm_mul]
  have hA : ‖σ ((Nat.card H₀ : K)⁻¹ * (Nat.card H : K)⁻¹)‖ =
      (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ := by
    simp [map_mul, map_inv₀, map_natCast, norm_inv]
  rw [hA]
  have hB : ‖σ (∑ h₀ : H₀, ∑ h : H, ((((χ₀ h₀⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) *
          (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) * charOf τ ((h₀ : G) * a * h * b))‖ ≤
      ∑ _h₀ : H₀, ∑ _h : H, (finrank K T : ℝ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine norm_sum_le_of_le _ fun h₀ _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine norm_sum_le_of_le _ fun h _ => ?_
    rw [map_mul, map_mul, norm_mul, norm_mul, norm_chi, norm_chi, one_mul, one_mul]
    exact ((hC K G T τ _).2 σ).2
  have hpos : (0 : ℝ) ≤ (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ := by positivity
  calc (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ * ‖_‖ ≤
        (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ * ∑ _h₀ : H₀, ∑ _h : H, (finrank K T : ℝ) :=
        mul_le_mul_of_nonneg_left hB hpos
    _ = (finrank K T : ℝ) := by
        have h0 : (Nat.card H₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
        have h1 : (Nat.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
        field_simp

theorem integral_mem (hC : CharFacts) (τ : Representation K G T) (H₀ H : Subgroup G)
    (χ₀ : H₀ →* (𝓞 K)ˣ) (χ : H →* (𝓞 K)ˣ) (a b : G) :
    (Fintype.card G : K) ^ 2 * LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b) ∈
      integralClosure ℤ K := by
  classical
  rw [trace_formula]
  have hG0 : (Fintype.card G : K) = (Nat.card H₀ : K) * (H₀.index : K) := by
    rw [← Nat.cast_mul, Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  have hG1 : (Fintype.card G : K) = (Nat.card H : K) * (H.index : K) := by
    rw [← Nat.cast_mul, Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  have hsq : (Fintype.card G : K) ^ 2 =
      ((Nat.card H₀ : K) * (H₀.index : K)) * ((Nat.card H : K) * (H.index : K)) := by
    rw [sq]
    nth_rw 1 [hG0]
    rw [hG1]
  have h0 : (Nat.card H₀ : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h1 : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [hsq, show ∀ x : K, (Nat.card H₀ : K) * (H₀.index : K) * ((Nat.card H : K) * (H.index : K)) *
      ((Nat.card H₀ : K)⁻¹ * (Nat.card H : K)⁻¹ * x) = (H₀.index : K) * (H.index : K) * x from
      fun x => by field_simp]
  refine mul_mem (mul_mem (Subalgebra.natCast_mem _ _) (Subalgebra.natCast_mem _ _))
    (Subalgebra.sum_mem _ fun h₀ _ => Subalgebra.sum_mem _ fun h _ => mul_mem (mul_mem ?_ ?_) ?_)
  · exact RingOfIntegers.isIntegral_coe _
  · exact RingOfIntegers.isIntegral_coe _
  · exact (hC K G T τ _).1

end Char

section Alg

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]


open Classical in
def epA (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) : MonoidAlgebra K G :=
  ((Nat.card H : ℕ) : K)⁻¹ •
    ∑ h : H, MonoidAlgebra.single (h : G) ((((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K))

theorem asAlg_epA (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) {V : Type} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) : ρ.asAlgebraHom (epA H χ) = epP H χ ρ := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [epA, epP, map_smul, map_sum, Representation.asAlgebraHom_single]

def eA {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T) : MonoidAlgebra K G :=
  (charOf τ 1 / (Fintype.card G : K)) • ∑ x : G, MonoidAlgebra.single x (charOf τ x⁻¹)

theorem asAlg_eA {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T)
    {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V) :
    ρ.asAlgebraHom (eA τ) = eS τ ρ := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [eA, eS, map_smul, map_sum, Representation.asAlgebraHom_single]

end Alg

end NormTraceLemmas


open NormTraceLemmas in
theorem core_of (hC : CharFacts) (hK : KeyZero) (hS : Schur) (hP : IdemP) : Core := by
  intro K _ _ G _ _ S T _ _ _ τ H₀ χ₀ H χ hgood hM1 s
  obtain ⟨γ, δ, c, hdet, htr, he1, he2⟩ :=
    exists_strictHenselian_absolutely_closed_local_ring (τ s) (hgood.2.1 s) (epP H₀ χ₀ (τ s)) (epP H χ (τ s)) (hM1 s)
  refine ⟨γ, δ, c, fun i j => ⟨(Fintype.card G : K) ^ 2 * c i j, ?_⟩, hdet, fun i j => rfl, ?_, ?_⟩
  · rw [htr i j]
    exact integral_mem hC (τ s) H₀ H χ₀ χ (δ i) (γ j)
  · intro i j σ
    rw [htr i j]
    exact norm_trace_le hC (τ s) H₀ H χ₀ χ (δ i) (γ j) σ
  · intro V _ _ ρ
    let _ : Module (𝓞 K) V := Module.compHom V (algebraMap (𝓞 K) K)
    have : IsScalarTower (𝓞 K) K V := ⟨fun x y v => by
      change (x • y) • v = (algebraMap (𝓞 K) K x) • (y • v)
      rw [Algebra.smul_def, mul_smul]⟩
    obtain ⟨hPe, hPε⟩ := hP K G V ρ
    obtain ⟨hcg, hcε, -⟩ := hPe (T s) (τ s)
    have ce_g : ∀ g x, eS (τ s) ρ (ρ g x) = ρ g (eS (τ s) ρ x) :=
      fun g x => LinearMap.congr_fun (hcg g) x
    have ce₀ : ∀ x, eS (τ s) ρ (epP H₀ χ₀ ρ x) = epP H₀ χ₀ ρ (eS (τ s) ρ x) :=
      fun x => LinearMap.congr_fun (hcε H₀ χ₀) x
    have ce : ∀ x, eS (τ s) ρ (epP H χ ρ x) = epP H χ ρ (eS (τ s) ρ x) :=
      fun x => LinearMap.congr_fun (hcε H χ) x
    have ii₀ : ∀ x, epP H₀ χ₀ ρ (epP H₀ χ₀ ρ x) = epP H₀ χ₀ ρ x :=
      fun x => LinearMap.congr_fun (hPε H₀ χ₀).1 x
    have ii : ∀ x, epP H χ ρ (epP H χ ρ x) = epP H χ ρ x :=
      fun x => LinearMap.congr_fun (hPε H χ).1 x
    have hee : ∀ x, eS (τ s) ρ (eS (τ s) ρ x) = eS (τ s) ρ x := by
      intro x
      have h0 : (τ s).asAlgebraHom (eA (τ s) - 1) = 0 := by
        rw [map_sub, asAlg_eA, (hS K G S T τ hgood).1 s, map_one, Module.End.one_eq_id, sub_self]
      have := LinearMap.congr_fun (hK K G (T s) (τ s) V ρ _ h0) x
      simp only [LinearMap.comp_apply, map_sub, asAlg_eA, map_one, LinearMap.sub_apply,
        Module.End.one_apply, LinearMap.zero_apply, sub_eq_zero] at this
      exact this
    constructor
    · intro i j a ha
      have ea : eS (τ s) ρ a = a := by
        calc eS (τ s) ρ a = eS (τ s) ρ (epP H₀ χ₀ ρ (eS (τ s) ρ a)) := by rw [ha]
          _ = a := by rw [ce₀, hee, ha]
      have e0a : epP H₀ χ₀ ρ a = a := by
        calc epP H₀ χ₀ ρ a = epP H₀ χ₀ ρ (epP H₀ χ₀ ρ (eS (τ s) ρ a)) := by rw [ha]
          _ = a := by rw [ii₀, ha]
      have hx : (τ s).asAlgebraHom (epA H₀ χ₀ * MonoidAlgebra.of K G (δ i) * epA H χ *
          MonoidAlgebra.of K G (γ j) * epA H₀ χ₀ - c i j • epA H₀ χ₀) = 0 := by
        simp only [map_sub, map_mul, map_smul, asAlg_epA, Representation.asAlgebraHom_of,
          Module.End.mul_eq_comp, LinearMap.comp_assoc]
        rw [he1 i j, sub_self]
      have := LinearMap.congr_fun (hK K G (T s) (τ s) V ρ _ hx) a
      simp only [LinearMap.comp_apply, map_sub, map_mul, map_smul, asAlg_epA,
        Representation.asAlgebraHom_of, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.smul_apply, LinearMap.zero_apply, ce₀, ce_g, ce, ea, e0a, sub_eq_zero] at this
      exact this
    · intro a ha
      have ea : eS (τ s) ρ a = a := by
        calc eS (τ s) ρ a = eS (τ s) ρ (epP H χ ρ (eS (τ s) ρ a)) := by rw [ha]
          _ = a := by rw [ce, hee, ha]
      have Ea : epP H χ ρ a = a := by
        calc epP H χ ρ a = epP H χ ρ (epP H χ ρ (eS (τ s) ρ a)) := by rw [ha]
          _ = a := by rw [ii, ha]
      have hy : (τ s).asAlgebraHom (∑ j, ∑ i, c⁻¹ j i • (epA H χ * MonoidAlgebra.of K G (γ j) *
          epA H₀ χ₀ * MonoidAlgebra.of K G (δ i) * epA H χ) - epA H χ) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sub, map_sum, map_mul, map_smul, asAlg_epA, Representation.asAlgebraHom_of,
          Module.End.mul_eq_comp, LinearMap.comp_assoc]
        rw [he2, sub_self]
      have := LinearMap.congr_fun (hK K G (T s) (τ s) V ρ _ hy) a
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.comp_apply, map_sub, map_sum, map_mul, map_smul, asAlg_epA,
        Representation.asAlgebraHom_of, LinearMap.sub_apply, LinearMap.sum_apply,
        Module.End.mul_apply, LinearMap.smul_apply, LinearMap.zero_apply, ce₀, ce_g, ce, ea, Ea,
        sub_eq_zero] at this
      exact this

end Formalism.IndefR.LatticeTransfer
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.TraceOfDiag
section
open Module NumberField

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement

namespace CharacterLemmas

theorem trace_of_diag {V I : Type*} [AddCommGroup V] [Module ℂ V] [Fintype I] [DecidableEq I]
    (v : Basis I ℂ V) (h : V →ₗ[ℂ] V) (c : I → ℂ) (hv : ∀ i, h (v i) = c i • v i) :
    LinearMap.trace ℂ V h = ∑ i, c i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ v h, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hv i, map_smul, Basis.repr_self]
  simp

theorem eigen_data {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ∃ (I : Type) (_ : Fintype I) (μ : I → ℂ), Fintype.card I = finrank ℂ V ∧
      (∀ i, μ i ^ orderOf g = 1) ∧ LinearMap.trace ℂ V (ρ g) = ∑ i, μ i ∧
      LinearMap.trace ℂ V (ρ g⁻¹) = ∑ i, starRingEnd ℂ (μ i) := by
  classical
  set s : Module.End ℂ V := ρ g with hs
  set n := orderOf g with hn
  have hn0 : 0 < n := orderOf_pos g
  have hsn : s ^ n = 1 := by rw [hs, ← map_pow, hn, pow_orderOf_eq_one, map_one]
  have hsq : Squarefree (Polynomial.X ^ n - 1 : Polynomial ℂ) :=
    (Polynomial.X_pow_sub_one_separable_iff.mpr (by exact_mod_cast hn0.ne')).squarefree
  have hss : s.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq (by simp [hsn])
  let eigenDecomp := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    s.eigenspaces_iSupIndep hss.iSup_eigenspace_eq_top
  let I := (ν : ℂ) × Fin (finrank ℂ (s.eigenspace ν))
  let v : Basis I ℂ V := eigenDecomp.collectedBasis fun μ ↦ finBasis ℂ (s.eigenspace μ)
  have hI : Fintype I := FiniteDimensional.fintypeBasisIndex v
  let μ : I → ℂ := Sigma.fst
  have hsv (i : I) : s (v i) = μ i • v i :=
    Module.End.mem_eigenspace_iff.mp (eigenDecomp.collectedBasis_mem _ i)
  have hpow : ∀ (i : I) (k : ℕ), (s ^ k) (v i) = μ i ^ k • v i := by
    intro i k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, hsv, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hμn : ∀ i, μ i ^ n = 1 := by
    intro i
    have h1 := hpow i n
    rw [hsn, Module.End.one_apply] at h1
    have h2 : (μ i ^ n - 1) • v i = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 (v.ne_zero i)
  have hμ0 : ∀ i, μ i ≠ 0 := by
    intro i h0
    have := hμn i
    rw [h0, zero_pow hn0.ne'] at this
    exact zero_ne_one this
  have hinv : ∀ i, ρ g⁻¹ (v i) = (starRingEnd ℂ) (μ i) • v i := by
    intro i
    have h1 : ρ g⁻¹ (s (v i)) = v i := by
      rw [hs, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hsv, map_smul] at h1
    have h2 : (μ i)⁻¹ = (starRingEnd ℂ) (μ i) :=
      Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one (hμn i) hn0.ne')
    rw [← h2]
    calc ρ g⁻¹ (v i) = (μ i)⁻¹ • (μ i • ρ g⁻¹ (v i)) := by
          rw [smul_smul, inv_mul_cancel₀ (hμ0 i), one_smul]
      _ = (μ i)⁻¹ • v i := by rw [h1]
  exact ⟨I, hI, μ, (finrank_eq_card_basis v).symm, hμn, trace_of_diag v _ μ hsv,
    trace_of_diag v _ _ hinv⟩

theorem char_complex {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    IsIntegral ℤ (LinearMap.trace ℂ V (ρ g)) ∧
      LinearMap.trace ℂ V (ρ g⁻¹) = star (LinearMap.trace ℂ V (ρ g)) ∧
      ‖LinearMap.trace ℂ V (ρ g)‖ ≤ (finrank ℂ V : ℝ) := by
  obtain ⟨I, hI, μ, hcard, hμ, htr, htr'⟩ := eigen_data ρ g
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [htr]
    refine IsIntegral.sum _ fun i _ => ?_
    refine IsIntegral.of_pow (orderOf_pos g) ?_
    rw [hμ i]
    exact isIntegral_one
  · rw [htr', htr, star_sum]
    rfl
  · rw [htr]
    calc ‖∑ i, μ i‖ ≤ ∑ i, ‖μ i‖ := norm_sum_le _ _
      _ = ∑ _i : I, (1 : ℝ) := Finset.sum_congr rfl fun i _ => by
          have h1 : ‖μ i‖ ^ orderOf g = 1 := by rw [← norm_pow, hμ i, norm_one]
          exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h1
      _ = (finrank ℂ V : ℝ) := by simp [hcard]

def repC {K : Type} [Field K] (σ : K →+* ℂ) {G : Type} [Group G] {T : Type} [AddCommGroup T]
    [Module K T] [FiniteDimensional K T] (τ : Representation K G T) :
    Representation ℂ G (Fin (finrank K T) → ℂ) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin (finrank K T)) (Fin (finrank K T)) ℂ ≃ₐ[ℂ] _) :
      Matrix (Fin (finrank K T)) (Fin (finrank K T)) ℂ →* _).comp
    (((σ.mapMatrix : Matrix (Fin (finrank K T)) (Fin (finrank K T)) K →+* _) :
        Matrix (Fin (finrank K T)) (Fin (finrank K T)) K →* _).comp
      (((LinearMap.toMatrixAlgEquiv (Module.finBasis K T)) : (T →ₗ[K] T) →* _).comp τ))

theorem trace_repC {K : Type} [Field K] (σ : K →+* ℂ) {G : Type} [Group G] {T : Type}
    [AddCommGroup T] [Module K T] [FiniteDimensional K T] (τ : Representation K G T) (g : G) :
    LinearMap.trace ℂ _ (repC σ τ g) = σ (charOf τ g) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin (finrank K T))), charOf,
    LinearMap.trace_eq_matrix_trace K (Module.finBasis K T) (τ g)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [repC, LinearMap.toMatrix_eq_toMatrix', Matrix.trace, map_sum, LinearMap.toMatrixAlgEquiv_apply,
    LinearMap.toMatrix_apply]

end CharacterLemmas

open CharacterLemmas

theorem charFacts : CharFacts := by
  intro K _ _ G _ _ T _ _ _ τ g
  have hmain : ∀ σ : K →+* ℂ, IsIntegral ℤ (σ (charOf τ g)) ∧
      σ (charOf τ g⁻¹) = star (σ (charOf τ g)) ∧ ‖σ (charOf τ g)‖ ≤ (finrank K T : ℝ) := by
    intro σ
    obtain ⟨h1, h2, h3⟩ := char_complex (repC σ τ) g
    rw [trace_repC, trace_repC] at h2
    rw [trace_repC] at h1 h3
    refine ⟨h1, h2, ?_⟩
    simpa using h3
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := by
    first
    | exact inferInstance
    | exact ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := K)).toRingHom⟩
  refine ⟨?_, fun σ' => ⟨(hmain σ').2.1, (hmain σ').2.2⟩⟩
  exact (isIntegral_algHom_iff σ.toIntAlgHom σ.injective).1 (hmain σ).1

theorem liftChar : LiftChar := by
  intro K _ _ H _ _ χ
  have hint : ∀ h, IsIntegral ℤ ((χ h : Kˣ) : K) := by
    intro h
    refine IsIntegral.of_pow (orderOf_pos h) ?_
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
    exact isIntegral_one
  let φ : H →* 𝓞 K :=
    { toFun := fun h => ⟨((χ h : Kˣ) : K), hint h⟩
      map_one' := by
        apply RingOfIntegers.ext
        show ((χ 1 : Kˣ) : K) = 1
        rw [map_one, Units.val_one]
      map_mul' := fun a b => by
        apply RingOfIntegers.ext
        show ((χ (a * b) : Kˣ) : K) = ((χ a : Kˣ) : K) * ((χ b : Kˣ) : K)
        rw [map_mul, Units.val_mul] }
  exact ⟨φ.toHomUnits, fun h => rfl⟩

theorem dimSq_of (h : Schur) : DimSq := by
  intro K _ _ G _ _ S T _ _ _ τ hgood s
  obtain ⟨-, -, hsum⟩ := h K G S T τ hgood
  have hs := hsum s
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := by
    first
    | exact inferInstance
    | exact ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := K)).toRingHom⟩
  have hdim : charOf (τ s) 1 = (finrank K (T s) : K) := by
    unfold charOf
    rw [map_one, LinearMap.trace_one]
  have hterm : ∀ x : G, σ (charOf (τ s) x⁻¹ * charOf (τ s) x) =
      ((‖σ (charOf (τ s) x)‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [map_mul, ((charFacts K G (T s) (τ s) x).2 σ).1]
    push_cast
    exact Complex.conj_mul' _
  have e1 := congrArg σ hs
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_natCast] at e1
  simp_rw [hterm] at e1
  have e2 : (∑ x : G, ‖σ (charOf (τ s) x)‖ ^ 2 : ℝ) = (Fintype.card G : ℝ) := by
    exact_mod_cast e1
  have key : ((finrank K (T s) : ℝ)) ^ 2 ≤ (Fintype.card G : ℝ) := by
    rw [← e2]
    have h1 : ‖σ (charOf (τ s) 1)‖ ^ 2 = ((finrank K (T s) : ℝ)) ^ 2 := by
      rw [hdim, map_natCast, Complex.norm_natCast]
    rw [← h1]
    exact Finset.single_le_sum (f := fun x : G => ‖σ (charOf (τ s) x)‖ ^ 2)
      (fun x _ => by positivity) (Finset.mem_univ 1)
  have key' : finrank K (T s) ^ 2 ≤ Fintype.card G := by exact_mod_cast key
  refine ⟨key', fun H χ => le_trans ?_ key'⟩
  exact Nat.pow_le_pow_left (Submodule.finrank_le _) 2

end Formalism.IndefR.LatticeTransfer
end
end

