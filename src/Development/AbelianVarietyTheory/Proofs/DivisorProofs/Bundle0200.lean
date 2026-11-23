module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0141
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankJointWeightSpaceEqOfCharpoly
section
open scoped TensorProduct

namespace GlobalTheory.WeightCount

open Module

theorem isNilpotent_perturb_mul {R : Type*} [Ring R] {A B a b : R} (hAB : Commute A B)
    (ha : ∀ z, Commute a z) (hb : ∀ z, Commute b z) (hA : IsNilpotent A) (hB : IsNilpotent B) :
    IsNilpotent ((A + a) * (B + b) - a * b) := by
  have e : (A + a) * (B + b) - a * b = A * (B + b) + a * B := by noncomm_ring
  rw [e]
  have h1 : Commute A (B + b) := hAB.add_right (hb A).symm
  have h3 : Commute (A * (B + b)) B := Commute.mul_left hAB ((Commute.refl B).add_left (hb B))
  have h2 : Commute (A * (B + b)) (a * B) := Commute.mul_right (ha _).symm h3
  exact h2.isNilpotent_add (h1.isNilpotent_mul_right hA) ((ha B).isNilpotent_mul_left hB)

theorem weight_isRingHom {k V C : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [CommRing C] (ρ : C →+* Module.End k V) (ψ : C → k)
    (hψ : (⨅ d, (ρ d).maxGenEigenspace (ψ d)) ≠ ⊥) : ∃ φ : C →+* k, ⇑φ = ψ := by
  classical
  set U := ⨅ d, (ρ d).maxGenEigenspace (ψ d) with hU
  have hc : ∀ x y, Commute (ρ x) (ρ y) := fun x y => by
    show ρ x * ρ y = ρ y * ρ x
    rw [← map_mul, ← map_mul, mul_comm]
  have hmaps : ∀ i j μ, Set.MapsTo (ρ i) ((ρ j).maxGenEigenspace μ) ((ρ j).maxGenEigenspace μ) :=
    fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) μ
  have hUm : ∀ m, Set.MapsTo (ρ m) U U := fun m v hv => by
    simp only [U, SetLike.mem_coe, Submodule.mem_iInf] at hv ⊢
    exact fun i => hmaps m i (ψ i) (hv i)
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hψ
  let R : C → Module.End k U := fun m => (ρ m).restrict (hUm m)
  have hRadd : ∀ x y, R (x + y) = R x + R y := fun x y => by
    ext v
    show ρ (x + y) (v : V) = ρ x (v : V) + ρ y (v : V)
    rw [map_add (f := _)]; rfl
  have hRmul : ∀ x y, R (x * y) = R x * R y := fun x y => by
    ext v
    show ρ (x * y) (v : V) = ρ x (ρ y (v : V))
    rw [map_mul]; rfl
  have hR1 : R 1 = 1 := by ext v; simp [R, LinearMap.restrict_apply]
  have hR0 : R 0 = 0 := by ext v; simp [R, LinearMap.restrict_apply]
  have hRc : ∀ x y, Commute (R x) (R y) := fun x y => by
    show R x * R y = R y * R x
    rw [← hRmul, ← hRmul, mul_comm]
  have hnil : ∀ m, IsNilpotent (R m - algebraMap k _ (ψ m)) := by
    intro m
    have hsub : Set.MapsTo (ρ m - algebraMap k (Module.End k V) (ψ m)) (U : Set V) U := by
      intro v hv
      simp only [SetLike.mem_coe, LinearMap.sub_apply, Module.algebraMap_end_apply] at hv ⊢
      exact U.sub_mem (hUm m hv) (U.smul_mem _ hv)
    have hn : IsNilpotent ((ρ m - algebraMap k _ (ψ m)).restrict hsub) :=
      Module.End.isNilpotent_restrict_of_le (iInf_le _ m)
        (Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (ρ m) (ψ m))
    have e : R m - algebraMap k _ (ψ m) = (ρ m - algebraMap k _ (ψ m)).restrict hsub := by
      ext v
      simp only [R, LinearMap.sub_apply, Module.algebraMap_end_apply, Submodule.coe_sub,
        Submodule.coe_smul]
      rfl
    rw [e]
    exact hn
  have hNc : ∀ x y, Commute (R x - algebraMap k _ (ψ x)) (R y - algebraMap k _ (ψ y)) :=
    fun x y => ((hRc x y).sub_right (Algebra.commute_algebraMap_right _ _)).sub_left
      ((Algebra.commute_algebraMap_left _ _).sub_right (Algebra.commute_algebraMap_left _ _))
  have key : ∀ a : k, IsNilpotent (algebraMap k (Module.End k U) a) → a = 0 := fun a h => by
    rwa [IsNilpotent.map_iff (FaithfulSMul.algebraMap_injective k (Module.End k U)),
      isNilpotent_iff_eq_zero] at h
  refine ⟨{ toFun := ψ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, rfl⟩
  · have h := hnil 1
    rw [hR1, ← map_one (algebraMap k (Module.End k U)), ← map_sub] at h
    exact (sub_eq_zero.1 (key _ h)).symm
  · intro x y
    have h1 := isNilpotent_perturb_mul (hNc x y) (Algebra.commute_algebraMap_left (ψ x))
      (Algebra.commute_algebraMap_left (ψ y)) (hnil x) (hnil y)
    rw [sub_add_cancel, sub_add_cancel, ← hRmul, ← map_mul] at h1
    have h2 := hnil (x * y)
    have h3 := (((Commute.refl (R (x * y))).sub_right (Algebra.commute_algebraMap_right _ _)).sub_left
      ((Algebra.commute_algebraMap_left _ _).sub_right
        (Algebra.commute_algebraMap_left _ _))).isNilpotent_sub h1 h2
    have e : R (x * y) - algebraMap k _ (ψ x * ψ y) - (R (x * y) - algebraMap k _ (ψ (x * y))) =
        algebraMap k (Module.End k U) (ψ (x * y) - ψ x * ψ y) := by
      rw [map_sub]; abel
    rw [e] at h3
    exact sub_eq_zero.1 (key _ h3)
  · have h := hnil 0
    rw [hR0, zero_sub, ← map_neg] at h
    exact neg_eq_zero.1 (key _ h)
  · intro x y
    have h1 := (hNc x y).isNilpotent_add (hnil x) (hnil y)
    have h2 := hnil (x + y)
    have h3 := ((hNc (x + y) x).add_right (hNc (x + y) y)).isNilpotent_sub h2 h1
    have e : R (x + y) - algebraMap k _ (ψ (x + y)) -
        (R x - algebraMap k _ (ψ x) + (R y - algebraMap k _ (ψ y))) =
        algebraMap k (Module.End k U) (ψ x + ψ y - ψ (x + y)) := by
      rw [hRadd, map_sub, map_add (f := _)]; abel
    rw [e] at h3
    exact (sub_eq_zero.1 (key _ h3)).symm

theorem exists_finset_weights {k V C : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [CommRing C] (ρ : C →+* Module.End k V) :
    ∃ S : Finset (C →+* k), ∀ ψ : C → k, (⨅ d, (ρ d).maxGenEigenspace (ψ d)) ≠ ⊥ →
      ∃ φ ∈ S, ⇑φ = ψ := by
  classical
  let U : (C → k) → Submodule k V := fun ψ => ⨅ d, (ρ d).maxGenEigenspace (ψ d)
  have hc : ∀ x y, Commute (ρ x) (ρ y) := fun x y => by
    show ρ x * ρ y = ρ y * ρ x
    rw [← map_mul, ← map_mul, mul_comm]
  have hmaps : ∀ i j μ, Set.MapsTo (ρ i) ((ρ j).maxGenEigenspace μ) ((ρ j).maxGenEigenspace μ) :=
    fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) μ
  have hind : iSupIndep U :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun x => ρ x) hmaps
  have hfin : {ψ | U ψ ≠ ⊥}.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  refine ⟨hfin.toFinset.attach.image (fun ψ => Classical.choose (weight_isRingHom ρ ψ.1
    (by have := ψ.2; rw [Set.Finite.mem_toFinset] at this; exact this))), fun ψ hψ => ?_⟩
  have hmem : ψ ∈ hfin.toFinset := by rw [Set.Finite.mem_toFinset]; exact hψ
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨ψ, hmem⟩), ?_⟩
  exact Classical.choose_spec (weight_isRingHom ρ ψ hψ)

end GlobalTheory.WeightCount

namespace GlobalTheory.WeightCount

open Module

theorem maxGenEigenspace_eq_weight {k V C : Type*} [Field k] [IsAlgClosed k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [CommRing C] (ρ : C →+* Module.End k V) (χ : C → k)
    (c : C) (hc : ∀ ψ : C → k, (⨅ d, (ρ d).maxGenEigenspace (ψ d)) ≠ ⊥ → ψ ≠ χ → ψ c ≠ χ c) :
    (ρ c).maxGenEigenspace (χ c) = ⨅ d, (ρ d).maxGenEigenspace (χ d) := by
  classical
  let U : (C → k) → Submodule k V := fun ψ => ⨅ d, (ρ d).maxGenEigenspace (ψ d)
  have hcomm : ∀ x y, Commute (ρ x) (ρ y) := fun x y => by
    show ρ x * ρ y = ρ y * ρ x
    rw [← map_mul, ← map_mul, mul_comm]
  have hmaps : ∀ i j μ, Set.MapsTo (ρ i) ((ρ j).maxGenEigenspace μ) ((ρ j).maxGenEigenspace μ) :=
    fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) μ
  have htop : ⨆ ψ, U ψ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (fun x => ρ x) hmaps
      (fun i => Module.End.iSup_maxGenEigenspace_eq_top (ρ i))
  set E := (ρ c).maxGenEigenspace (χ c) with hE
  have hXE : U χ ≤ E := iInf_le _ c
  have hY : (⨆ ψ, ⨆ (_ : ψ ≠ χ), U ψ) ≤ ⨆ μ, ⨆ (_ : μ ≠ χ c), (ρ c).maxGenEigenspace μ := by
    refine iSup₂_le fun ψ hψ => ?_
    by_cases h0 : U ψ = ⊥
    · rw [h0]; exact bot_le
    · exact le_iSup₂_of_le (f := fun μ (_ : μ ≠ χ c) => (ρ c).maxGenEigenspace μ) (ψ c)
        (hc ψ h0 hψ) (iInf_le _ c)
  have hdisj : Disjoint E (⨆ μ, ⨆ (_ : μ ≠ χ c), (ρ c).maxGenEigenspace μ) :=
    (Module.End.independent_maxGenEigenspace (ρ c)) (χ c)
  have hsup : U χ ⊔ (⨆ ψ, ⨆ (_ : ψ ≠ χ), U ψ) = ⊤ := by
    rw [← htop]; exact (iSup_split_single U χ).symm
  have hEY : (⨆ ψ, ⨆ (_ : ψ ≠ χ), U ψ) ⊓ E = ⊥ := (hdisj.mono_right hY).symm.eq_bot
  calc E = (U χ ⊔ ⨆ ψ, ⨆ (_ : ψ ≠ χ), U ψ) ⊓ E := by rw [hsup, top_inf_eq]
    _ = U χ ⊔ (⨆ ψ, ⨆ (_ : ψ ≠ χ), U ψ) ⊓ E := sup_inf_assoc_of_le _ hXE
    _ = U χ := by rw [hEY, sup_bot_eq]

theorem charpoly_lmul_includeRight (k C : Type) [Field k] [CommRing C] [Module.Free ℤ C]
    [Module.Finite ℤ C] (c : C) :
    LinearMap.charpoly (Algebra.lmul k (k ⊗[ℤ] C)
      ((Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C) c)) =
      (LinearMap.charpoly (LinearMap.mulLeft ℤ c)).map (Int.castRingHom k) := by
  have e : Algebra.lmul k (k ⊗[ℤ] C) ((Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C) c) =
      (LinearMap.mulLeft ℤ c).baseChange k := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [e, LinearMap.charpoly_baseChange, algebraMap_int_eq]

theorem finrank_weight_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C]
    [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H]
    [FiniteDimensional k H] (σ : C →+* Module.End k H) (r : ℕ),
    (∀ c : C, LinearMap.charpoly (σ c) =
      ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ r).map (Int.castRingHom k)) →
    ∀ χ : C →+* k, Module.finrank k ↥(⨅ c : C, (σ c).maxGenEigenspace (χ c)) =
      r * Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
        (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace
          (χ c)) := by
  intro k _ _ C _ _ _ H _ _ _ σ r hσ χ
  classical
  let σA : C →+* Module.End k (k ⊗[ℤ] C) := (Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
    (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom
  have hA : ∀ c, LinearMap.charpoly (σA c) =
      (LinearMap.charpoly (LinearMap.mulLeft ℤ c)).map (Int.castRingHom k) :=
    fun c => charpoly_lmul_includeRight k C c
  obtain ⟨S1, hS1⟩ := exists_finset_weights σ
  obtain ⟨S2, hS2⟩ := exists_finset_weights σA
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_separating_element_ringHom_moduleFinite_int k C (S1 ∪ S2) χ
  have sepH : ∀ ψ : C → k, (⨅ d, (σ d).maxGenEigenspace (ψ d)) ≠ ⊥ → ψ ≠ ⇑χ → ψ c ≠ χ c := by
    intro ψ h hne
    obtain ⟨φ, hφS, rfl⟩ := hS1 ψ h
    exact hc φ (Finset.mem_union_left _ hφS) (fun e => hne (by rw [e]))
  have sepA : ∀ ψ : C → k, (⨅ d, (σA d).maxGenEigenspace (ψ d)) ≠ ⊥ → ψ ≠ ⇑χ → ψ c ≠ χ c := by
    intro ψ h hne
    obtain ⟨φ, hφS, rfl⟩ := hS2 ψ h
    exact hc φ (Finset.mem_union_right _ hφS) (fun e => hne (by rw [e]))
  show Module.finrank k ↥(⨅ d : C, (σ d).maxGenEigenspace (χ d)) =
    r * Module.finrank k ↥(⨅ d : C, (σA d).maxGenEigenspace (χ d))
  rw [← maxGenEigenspace_eq_weight σ χ c sepH, ← maxGenEigenspace_eq_weight σA χ c sepA,
    LinearMap.finrank_maxGenEigenspace_eq, LinearMap.finrank_maxGenEigenspace_eq, hσ c, hA c,
    Polynomial.map_pow, ← Polynomial.count_roots, ← Polynomial.count_roots, Polynomial.roots_pow,
    Multiset.count_nsmul]

end GlobalTheory.WeightCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMemEq
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.Shin.FreeHc

variable {F : Type} [Field F]

def fixSet {m : ℕ} (f : Fin m → F) : Set (GL (Fin m) F) :=
  {x | ∀ w : Fin m → F, f ⬝ᵥ w = 0 → (x : Matrix (Fin m) (Fin m) F) *ᵥ w = w}

def fixSub {m : ℕ} (f : Fin m → F) : Subgroup (GL (Fin m) F) where
  carrier := fixSet f
  one_mem' := by intro w _; simp
  mul_mem' := by
    intro x y hx hy w hw
    rw [Units.val_mul, ← mulVec_mulVec, hy w hw, hx w hw]
  inv_mem' := by
    intro x hx w hw
    calc ((x⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ w
        = ((x⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ ((x : Matrix (Fin m) (Fin m) F) *ᵥ w) := by rw [hx w hw]
      _ = w := by rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem isChar_conj {G : Type} [Group G] {χ : G → ℂ} (h : IsChar ℂ ℂ χ) (x y : G) :
    χ (y⁻¹ * x * y) = χ x := by
  obtain ⟨n, ρ, hρ⟩ := h
  rw [hρ, hρ]
  congr 1
  simpa using ρ.char_conj x y⁻¹

theorem finsum_mem_eq {α : Type} [Fintype α] (s : Set α) (g : α → ℂ) :
    ∑ᶠ x ∈ s, g x = ∑ x, if x ∈ s then g x else 0 := by
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
  simp [Set.indicator_apply]

def eLast (m : ℕ) (hm : 0 < m) : Fin m → F := Pi.single (⟨m - 1, by omega⟩ : Fin m) 1

theorem vmv_mulVec {m : ℕ} (u v w : Fin m → F) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec, of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem key {m : ℕ} (f w₀ : Fin m → F) (hw : f ⬝ᵥ w₀ = 1) (x : GL (Fin m) F) (hx : x ∈ fixSet f) :
    (x : Matrix (Fin m) (Fin m) F) = 1 + vecMulVec ((x : Matrix (Fin m) (Fin m) F) *ᵥ w₀ - w₀) f := by
  have h : ∀ w, (x : Matrix (Fin m) (Fin m) F) *ᵥ w =
      (1 + vecMulVec ((x : Matrix (Fin m) (Fin m) F) *ᵥ w₀ - w₀) f) *ᵥ w := by
    intro w
    have hw' : f ⬝ᵥ (w - (f ⬝ᵥ w) • w₀) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, hw, smul_eq_mul, mul_one, sub_self]
    have h1 := hx _ hw'
    rw [add_mulVec, one_mulVec, vmv_mulVec, smul_sub]
    have : w = (w - (f ⬝ᵥ w) • w₀) + (f ⬝ᵥ w) • w₀ := by abel
    conv_lhs => rw [this]
    rw [mulVec_add, h1, mulVec_smul]
    abel
  ext i j
  have := congr_fun (h (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

theorem conj_mem {m : ℕ} (f : Fin m → F) (z x : GL (Fin m) F) :
    z⁻¹ * x * z ∈ fixSet (f ᵥ* (z : Matrix (Fin m) (Fin m) F)) ↔ x ∈ fixSet f := by
  have hzz : (z : Matrix (Fin m) (Fin m) F) * ((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hzz' : ((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) * (z : Matrix (Fin m) (Fin m) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  constructor
  · intro h w hw
    have hw' : (f ᵥ* (z : Matrix (Fin m) (Fin m) F)) ⬝ᵥ (((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ w) = 0 := by
      rw [← dotProduct_mulVec, mulVec_mulVec, hzz, one_mulVec, hw]
    have := h _ hw'
    have hzw : (z : Matrix (Fin m) (Fin m) F) *ᵥ (((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ w) = w := by
      rw [mulVec_mulVec, hzz, one_mulVec]
    simp only [Units.val_mul] at this
    rw [← mulVec_mulVec, ← mulVec_mulVec, hzw] at this
    have hzv : ∀ v, (z : Matrix (Fin m) (Fin m) F) *ᵥ (((z⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ v) = v := by
      intro v; rw [mulVec_mulVec, hzz, one_mulVec]
    have := congrArg (fun v => (z : Matrix (Fin m) (Fin m) F) *ᵥ v) this
    simpa only [hzv] using this
  · intro h w hw
    rw [← dotProduct_mulVec] at hw
    simp only [Units.val_mul]
    rw [← mulVec_mulVec, ← mulVec_mulVec, h _ hw, mulVec_mulVec, hzz', one_mulVec]

theorem sum_conj {m : ℕ} [Fintype (GL (Fin m) F)] (f : Fin m → F) (z : GL (Fin m) F) (φ : GL (Fin m) F → ℂ) :
    (∑ x, if x ∈ fixSet f then φ (z⁻¹ * x * z) else 0) =
      ∑ g, if g ∈ fixSet (f ᵥ* (z : Matrix (Fin m) (Fin m) F)) then φ g else 0 := by
  refine Fintype.sum_equiv (MulAut.conj z⁻¹).toEquiv _ _ fun x => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
  rw [conj_mem]

end GlobalTheory.Shin.FreeHc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatModPSquaredTorsion
section
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory

theorem zmod_sq_dvd_of_mul_eq_zero (p : ℕ) [hp : Fact p.Prime] (a : ZMod (p ^ 2))
    (ha : (p : ZMod (p ^ 2)) * a = 0) : ∃ c : ZMod (p ^ 2), a = (p : ZMod (p ^ 2)) * c := by
  have h0 : ((p * a.val : ℕ) : ZMod (p ^ 2)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact ha
  rw [ZMod.natCast_eq_zero_iff] at h0
  obtain ⟨k, hk⟩ := h0
  have h1 : a.val = p * k := by
    apply Nat.eq_of_mul_eq_mul_left hp.out.pos
    rw [hk]; ring
  refine ⟨(k : ZMod (p ^ 2)), ?_⟩
  rw [← ZMod.natCast_zmod_val a, h1, Nat.cast_mul]

theorem flat_zmod_sq_mul_p_eq_zero_iff : ∀ (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (φ : ZMod (p ^ 2) →+* B), φ.Flat → ∀ w : B, (p : B) * w = 0 ↔ ∃ v, w = p * v := by
  intro p hp B _ φ hφ w
  letI : Algebra (ZMod (p ^ 2)) B := φ.toAlgebra
  have hflat : Module.Flat (ZMod (p ^ 2)) B := hφ
  have hsmul : ∀ (r : ZMod (p ^ 2)) (b : B), r • b = φ r * b := fun r b => by
    rw [Algebra.smul_def]; rfl
  have hpB : φ (p : ZMod (p ^ 2)) = (p : B) := map_natCast φ p
  constructor
  · intro hw
    have hsum : ∑ i : Unit, (fun _ => (p : ZMod (p ^ 2))) i • (fun _ => w) i = 0 := by
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [hsmul, hpB, hw]
    have htr := @Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (ZMod (p ^ 2)) B _ _ _ hflat Unit _ _ _ hsum
    obtain ⟨k, a, y, hy, ha⟩ := htr
    have ha' : ∀ j, (p : ZMod (p ^ 2)) * a () j = 0 := fun j => by
      simpa only [Finset.univ_unique, Finset.sum_singleton] using ha j
    choose c hc using fun j => zmod_sq_dvd_of_mul_eq_zero p (a () j) (ha' j)
    refine ⟨∑ j, φ (c j) * y j, ?_⟩
    have hw : w = ∑ j, a () j • y j := hy ()
    rw [hw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsmul, hc j, map_mul, hpB, mul_assoc]
  · rintro ⟨v, rfl⟩
    have h2 : (((p ^ 2 : ℕ) : ZMod (p ^ 2))) = 0 := ZMod.natCast_self _
    have : ((p ^ 2 : ℕ) : B) = 0 := by
      rw [← map_natCast φ, h2, map_zero]
    rw [← mul_assoc, ← Nat.cast_mul, ← pow_two, this, zero_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfEssentiallyEtaleLocalAlgebras
section
open IsLocalRing

namespace GlobalTheory

theorem flat_of_algHom_atPrime (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.Etale R A] [Algebra.Etale R B] (p : Ideal B) [p.IsPrime] (φ : A →ₐ[R] Localization.AtPrime p) :
    φ.toRingHom.Flat := by
  obtain ⟨g, hg, ψ, hψ⟩ := _root_.GlobalTheory.FactorAway.factor_away R A B p φ
  set h := Localization.awayLift (algebraMap B (Localization.AtPrime p)) g
    (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hg⟩ : p.primeCompl)) with hh
  have e : φ.toRingHom = h.comp ψ.toRingHom := by ext a; exact (hψ a).symm
  rw [e]
  refine RingHom.Flat.comp ?_ ?_
  · letI : Algebra A (Localization.Away g) := ψ.toRingHom.toAlgebra
    haveI : IsScalarTower R A (Localization.Away g) :=
      IsScalarTower.of_algebraMap_eq (fun r => (ψ.commutes r).symm)
    haveI : Algebra.Etale A (Localization.Away g) := Algebra.Etale.of_restrictScalars R A _
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · letI : Algebra (Localization.Away g) (Localization.AtPrime p) := h.toAlgebra
    haveI : IsScalarTower B (Localization.Away g) (Localization.AtPrime p) :=
      IsScalarTower.of_algebraMap_eq (fun b => by
        change _ = h _
        simp [hh, Localization.awayLift, IsLocalization.Away.lift])
    have : Module.Flat (Localization.Away g) (Localization.AtPrime p) :=
      (Module.flat_iff_of_isLocalization (Localization.Away g) (Submonoid.powers g)
        (Localization.AtPrime p)).mpr inferInstance
    exact RingHom.flat_algebraMap_iff.mpr this

theorem flat_of_essEtale : ∀ (R L₁ L₂ : Type) [CommRing R] [CommRing L₁] [CommRing L₂] [Algebra R L₁] [Algebra R L₂] [Algebra L₁ L₂] [IsScalarTower R L₁ L₂], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] L₁)) → (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] L₂)) → Module.Flat L₁ L₂ := by
  intro R L₁ L₂ _ _ _ _ _ _ _ ⟨A, _, _, _, q, _, ⟨e₁⟩⟩ ⟨A', _, _, _, q', _, ⟨e₂⟩⟩
  let φ : A →ₐ[R] Localization.AtPrime q' :=
    (e₂.symm.toAlgHom.comp (IsScalarTower.toAlgHom R L₁ L₂)).comp
      (e₁.toAlgHom.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q)))
  have hφ := flat_of_algHom_atPrime R A A' q' φ
  let f : A →+* L₁ := e₁.toRingHom.comp (algebraMap A (Localization.AtPrime q))
  letI : Algebra A L₁ := f.toAlgebra
  letI : Algebra A L₂ := ((algebraMap L₁ L₂).comp f).toAlgebra
  haveI : IsScalarTower A L₁ L₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let e₁' : Localization.AtPrime q ≃ₐ[A] L₁ := { e₁ with commutes' := fun _ => rfl }
  haveI : IsLocalization q.primeCompl L₁ := IsLocalization.isLocalization_of_algEquiv q.primeCompl e₁'
  have hflat : Module.Flat A L₂ := by
    rw [← RingHom.flat_algebraMap_iff]
    have : algebraMap A L₂ = e₂.toRingHom.comp φ.toRingHom := by
      ext a; simp [φ, f, RingHom.algebraMap_toAlgebra]
    rw [this]
    exact RingHom.Flat.comp hφ (RingHom.Flat.of_bijective e₂.bijective)
  exact (Module.flat_iff_of_isLocalization L₁ q.primeCompl L₂).mpr hflat

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierInversionSchwartzBruhat
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem GlobalTheory.tensorSum_bijective_iff (A B R S : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] [CommRing S] (κ : R ⊗[A] B →+* S) {r : ℕ} (v : Fin r → B) :
    Function.Bijective (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) ↔ (Function.Surjective κ ∧ LinearIndependent R (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k)) ∧ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k))) = ⊤) := by
  have hsum : ∀ c : Fin r → R, ∑ k, c k • Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k)
      = Ideal.Quotient.mk (RingHom.ker κ) (∑ k, c k ⊗ₜ[A] v k) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : c k • ((1 : R) ⊗ₜ[A] v k) = c k ⊗ₜ[A] v k := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [← h1]
    exact (map_smul (Ideal.Quotient.mkₐ R (RingHom.ker κ)) (c k) ((1 : R) ⊗ₜ[A] v k)).symm
  have hker : ∀ x y : R ⊗[A] B, Ideal.Quotient.mk (RingHom.ker κ) x = Ideal.Quotient.mk (RingHom.ker κ) y ↔ κ x = κ y := by
    intro x y
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
  have hsub : ∀ c c' : Fin r → R, ∑ k, (c - c') k ⊗ₜ[A] v k = ∑ k, c k ⊗ₜ[A] v k - ∑ k, c' k ⊗ₜ[A] v k := by
    intro c c'
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.sub_apply, TensorProduct.sub_tmul]
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun s => ?_, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hsurj s
      exact ⟨_, hc⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [hsum, show (0 : (R ⊗[A] B) ⧸ RingHom.ker κ) = Ideal.Quotient.mk (RingHom.ker κ) 0 from (map_zero _).symm,
        hker] at hg
      have h0 : (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) g = (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) 0 := by
        simp only [Pi.zero_apply, TensorProduct.zero_tmul, Finset.sum_const_zero, map_zero]
        simpa using hg
      intro i
      rw [hinj h0]
      rfl
    · rw [eq_top_iff]
      intro x _
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨c, hc⟩ := hsurj (κ t)
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, by rw [hsum, hker]; exact hc⟩
  · rintro ⟨hsurj, hli, hspan⟩
    refine ⟨fun c c' h => ?_, fun s => ?_⟩
    · rw [Fintype.linearIndependent_iff] at hli
      have h2 := hli (c - c') (by
        rw [hsum, show (0 : (R ⊗[A] B) ⧸ RingHom.ker κ) = Ideal.Quotient.mk (RingHom.ker κ) 0 from (map_zero _).symm,
          hker, hsub, map_sub, map_zero, sub_eq_zero]
        exact h)
      funext i
      exact sub_eq_zero.mp (h2 i)
    · obtain ⟨t, rfl⟩ := hsurj s
      have hm : Ideal.Quotient.mk (RingHom.ker κ) t ∈ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k))) := by
        rw [hspan]; trivial
      rw [Submodule.mem_span_range_iff_exists_fun] at hm
      obtain ⟨c, hc⟩ := hm
      rw [hsum, hker] at hc
      exact ⟨c, hc⟩
end

