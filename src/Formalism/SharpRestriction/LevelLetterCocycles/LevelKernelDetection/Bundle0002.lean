module

public import Mathlib
public import Formalism.DistinguishedUnitIdeals.Bundle0001
public import Formalism.WeaklyAdmissibleFiltrations.Statement

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.KerEqOfSpan
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.ExponentWindows

abbrev GrQ {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D] (F : ℤ → Submodule LL D) : Type :=
  ↥(Submodule.pi Set.univ fun k : ℤ => F (-k)) ⧸
    ((Submodule.pi Set.univ fun k : ℤ => F (1 - k)).comap (Submodule.pi Set.univ fun k : ℤ => F (-k)).subtype)

theorem finrank_grQ {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
    (F : ℤ → Submodule LL D) (hF : IsFilt F) :
    FiniteDimensional LL (GrQ F) ∧ Module.finrank LL (GrQ F) = Module.finrank LL D := by
  classical
  obtain ⟨hanti, ⟨lo, hlo⟩, ⟨b, hb⟩⟩ := hF
  set a : ℤ := min lo (b - 1) with ha_def
  have hab : a < b := by omega
  have htop : ∀ i, i ≤ a → F i = ⊤ := fun i hi => top_unique (hlo ▸ hanti (le_trans hi (min_le_left _ _)))
  have hbot : ∀ i, b ≤ i → F i = ⊥ := fun i hi => eq_bot_iff.2 (hb ▸ hanti hi)
  set N : ℕ := (b - a).toNat with hN
  let S : Finset ℤ := (Finset.range N).image fun j : ℕ => 1 - b + j
  have hmemS : ∀ k : ℤ, k ∈ S ↔ 1 - b ≤ k ∧ k ≤ -a := by
    intro k
    simp only [S, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · intro h; exact ⟨(k - (1 - b)).toNat, by omega, by omega⟩
  let P0 := Submodule.pi Set.univ fun k : ℤ => F (-k)
  let P1 := Submodule.pi Set.univ fun k : ℤ => F (1 - k)
  have memP0 : ∀ (x : P0) (k : ℤ), (x : ℤ → D) k ∈ F (-k) :=
    fun x k => (Submodule.mem_pi.1 x.2) k (Set.mem_univ _)
  let Qk : ℤ → Type := fun k => ↥(F (-k)) ⧸ (F (1 - k)).comap (F (-k)).subtype
  let φ : P0 →ₗ[LL] ∀ k : S, Qk k :=
    LinearMap.pi fun k => (Submodule.mkQ _) ∘ₗ
      ((LinearMap.proj (R := LL) (φ := fun _ : ℤ => D) (k : ℤ)) ∘ₗ P0.subtype).codRestrict (F (-(k : ℤ)))
        (fun x => memP0 x (k : ℤ))
  have hφ : ∀ (x : P0) (k : S), φ x k =
      (Submodule.Quotient.mk (⟨(x : ℤ → D) k, memP0 x k⟩ : ↥(F (-(k : ℤ)))) : Qk k) := fun x k => rfl
  have hker : LinearMap.ker φ = P1.comap P0.subtype := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_pi]
    constructor
    · intro hx k _
      show (x : ℤ → D) k ∈ F (1 - k)
      by_cases hk : k ∈ S
      · have := congrFun hx ⟨k, hk⟩
        rw [hφ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at this
        exact this
      · rw [hmemS] at hk
        rcases not_and_or.1 hk with h | h
        · have h0 : (x : ℤ → D) k ∈ F (-k) := memP0 x k
          rw [hbot (-k) (by omega)] at h0
          rw [(Submodule.mem_bot LL).1 h0]
          exact Submodule.zero_mem _
        · rw [htop (1 - k) (by omega)]
          exact Submodule.mem_top
    · intro hx
      funext k
      rw [hφ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact hx (k : ℤ) (Set.mem_univ _)
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : ∀ k : S, ∃ z : ↥(F (-(k : ℤ))), (Submodule.Quotient.mk z : Qk k) = y k :=
      fun k => Submodule.Quotient.mk_surjective _ (y k)
    choose z hz using hy
    refine ⟨⟨fun k => if h : k ∈ S then (z ⟨k, h⟩ : D) else 0, ?_⟩, ?_⟩
    · rw [Submodule.mem_pi]
      intro k _
      by_cases h : k ∈ S
      · simp only [dif_pos h]; exact (z ⟨k, h⟩).2
      · simp only [dif_neg h]; exact Submodule.zero_mem _
    · funext k
      rw [hφ, ← hz k]
      congr 1
      apply Subtype.ext
      simp [k.2]
  let e : GrQ F ≃ₗ[LL] ∀ k : S, Qk k :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hsurj)
  have hFD : FiniteDimensional LL (GrQ F) := LinearEquiv.finiteDimensional e.symm
  refine ⟨hFD, ?_⟩
  have hle : ∀ k : ℤ, F (1 - k) ≤ F (-k) := fun k => hanti (by omega)
  have hQk : ∀ k : ℤ, (Module.finrank LL (Qk k) : ℤ) =
      (Module.finrank LL (F (-k)) : ℤ) - Module.finrank LL (F (1 - k)) := by
    intro k
    have h1 := Submodule.finrank_quotient_add_finrank ((F (1 - k)).comap (F (-k)).subtype)
    have h2 : Module.finrank LL ((F (1 - k)).comap (F (-k)).subtype) = Module.finrank LL (F (1 - k)) :=
      (Submodule.comapSubtypeEquivOfLe (hle k)).finrank_eq
    simp only [Qk]
    omega
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  have hsum : ((∑ k : S, Module.finrank LL (Qk k) : ℕ) : ℤ) = Module.finrank LL D := by
    push_cast
    rw [Finset.sum_coe_sort S (fun k => (Module.finrank LL (Qk k) : ℤ))]
    simp only [S]
    rw [Finset.sum_image (fun i _ j _ h => by exact_mod_cast (add_left_cancel h : ((i : ℤ)) = j))]
    simp only [hQk]
    have hrw : ∀ j : ℕ, ((Module.finrank LL (F (-(1 - b + (j : ℤ)))) : ℤ) -
        Module.finrank LL (F (1 - (1 - b + (j : ℤ))))) =
        (Module.finrank LL (F (b - ((j + 1 : ℕ) : ℤ))) : ℤ) - Module.finrank LL (F (b - ((j : ℕ) : ℤ))) := by
      intro j
      rw [show -(1 - b + (j : ℤ)) = b - ((j + 1 : ℕ) : ℤ) by push_cast; ring,
        show 1 - (1 - b + (j : ℤ)) = b - ((j : ℕ) : ℤ) by ring]
    simp only [hrw]
    rw [Finset.sum_range_sub (fun j : ℕ => (Module.finrank LL (F (b - (j : ℤ))) : ℤ)) N]
    have h1 : b - ((N : ℕ) : ℤ) = a := by omega
    rw [h1, Nat.cast_zero, sub_zero, htop a le_rfl, hbot b le_rfl, finrank_top, finrank_bot]
    rfl
  exact_mod_cast hsum

end Formalism.MainNotions.N.Ln03.K8
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvBasisPhi
section
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem lvBasis_φ_act (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] B) :
    actVB PD ρ g (φVB PD (LL := LL) (V := V) x) = φVB PD (LL := LL) (V := V) (actVB PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [Formalism.WeaklyAdmissibleFiltrations.actVB, Formalism.WeaklyAdmissibleFiltrations.φVB, PD.φ_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem lvBasis_φ_mul (c : K₀) (x : V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (PD.σ c) (φVB PD (LL := LL) (V := V) x) =
      φVB PD (LL := LL) (V := V) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [Formalism.WeaklyAdmissibleFiltrations.mulVB, Formalism.WeaklyAdmissibleFiltrations.φVB, PD.φ_K₀]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem lvBasis_mem_Dcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Formalism.WeaklyAdmissibleFiltrations.Dcris, sub_eq_zero]

theorem lvBasis_mem_DcrisL (ρ : Representation LL G V) (τ₀ : K₀ →ₐ[Qp] LL) (x : V ⊗[Qp] B) :
    x ∈ DcrisL PD ρ τ₀ ↔ x ∈ Dcris PD ρ ∧
      ∀ c, mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x = τ₀ c • x := by
  simp [Formalism.WeaklyAdmissibleFiltrations.DcrisL, sub_eq_zero]

theorem lvBasis_φ_Dcris (ρ : Representation LL G V) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ := by
  rw [lvBasis_mem_Dcris] at hx ⊢
  intro g
  rw [lvBasis_φ_act, hx g]

theorem lvBasis_φ_letter (ρ : Representation LL G V) {τ₀ τ₁ : K₀ →ₐ[Qp] LL}
    (h : τ₁.comp PD.σ = τ₀) {x : V ⊗[Qp] B} (hx : x ∈ DcrisL PD ρ τ₀) :
    φVB PD (LL := LL) (V := V) x ∈ DcrisL PD ρ τ₁ := by
  rw [lvBasis_mem_DcrisL] at hx ⊢
  refine ⟨lvBasis_φ_Dcris PD ρ hx.1, fun c => ?_⟩
  obtain ⟨c', rfl⟩ := PD.σ_bij.2 c
  rw [lvBasis_φ_mul, hx.2 c', map_smul, ← h, AlgHom.comp_apply]

theorem lvBasis_φ_inj : Function.Injective (φVB PD (LL := LL) (V := V)) := by
  have hfun : ⇑(Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := V)) = ⇑(LinearMap.lTensor V PD.φ.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [Formalism.WeaklyAdmissibleFiltrations.φVB]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [hfun]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ PD.φ_inj

theorem lvBasis_φpow_inj (k : ℕ) : Function.Injective ((φVB PD (LL := LL) (V := V)) ^ k) := by
  first
  | (rw [Module.End.coe_pow]; exact (lvBasis_φ_inj PD).iterate k)
  | simpa using (lvBasis_φ_inj PD).iterate k

private theorem eigen_finset_eq_zero_of_injective_embeddings {ι : Type} [DecidableEq ι] (τ : ι → (K₀ →ₐ[Qp] LL))
    (hτ : Function.Injective τ) (s : Finset ι) : ∀ (x : ι → V ⊗[Qp] B),
    (∀ i ∈ s, ∀ c, Formalism.WeaklyAdmissibleFiltrations.mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (x i) = τ i c • x i) →
    ∑ i ∈ s, x i = 0 → ∀ i ∈ s, x i = 0 := by
  induction s using Finset.induction_on with
  | empty => intro x _ _ i hi; simp at hi
  | @insert j s hj ih =>
    intro x hx hs
    rw [Finset.sum_insert hj] at hs
    have h2 : ∑ i ∈ s, x i = -x j := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hs
    have key : ∀ c, ∀ i ∈ s, (τ i c - τ j c) • x i = 0 := by
      intro c
      apply ih (fun i => (τ i c - τ j c) • x i)
      · intro i hi c'
        rw [map_smul, hx i (Finset.mem_insert_of_mem hi) c', smul_comm]
      · have h1 := congrArg (Formalism.WeaklyAdmissibleFiltrations.mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c) hs
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_add (f := _), map_sum, map_zero, hx j (Finset.mem_insert_self j s) c,
          Finset.sum_congr rfl (fun i hi => hx i (Finset.mem_insert_of_mem hi) c)] at h1
        simp_rw [sub_smul]
        rw [Finset.sum_sub_distrib, ← Finset.smul_sum, h2, smul_neg, sub_neg_eq_add, add_comm]
        exact h1
    have hs0 : ∀ i ∈ s, x i = 0 := by
      intro i hi
      have hij : τ i ≠ τ j := fun h => hj (by rw [← hτ h]; exact hi)
      obtain ⟨c, hc⟩ : ∃ c, τ i c ≠ τ j c := by
        by_contra hne
        push_neg at hne
        exact hij (AlgHom.ext hne)
      exact (smul_eq_zero.mp (key c i hi)).resolve_left (sub_ne_zero.mpr hc)
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [Finset.sum_eq_zero hs0, add_zero] at hs
      exact hs
    · exact hs0 i hi

theorem lvBasis_indep {ι : Type} [Fintype ι] (τ : ι → (K₀ →ₐ[Qp] LL)) (hτ : Function.Injective τ)
    (x : ι → V ⊗[Qp] B)
    (hx : ∀ i c, mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (x i) = τ i c • x i)
    (hs : ∑ i, x i = 0) (i : ι) : x i = 0 := by
  classical
  exact eigen_finset_eq_zero_of_injective_embeddings τ hτ Finset.univ x (fun i _ c => hx i c) hs i (Finset.mem_univ i)

end Formalism.MainNotions.N.Ln03.Pf
end
end

