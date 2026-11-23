module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0342
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0338
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0344
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToZModPowKummerEqIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTorsionQuotientConjInvariantDecomposition

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductDualTwistIsTwoCocycleUnramified
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem eps_eq_algebraMap (s : G ℚ Ω) :
    eps l s = algebraMap ℤ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := by
  simp [eps, cycBar]
  rfl

theorem eps_mem (c : Coef l) (s : G ℚ Ω) : eps l s ∈ c.O := by
  rw [eps_eq_algebraMap]; exact c.O.algebraMap_mem _

theorem continuous_eps : Continuous (fun s : G ℚ Ω => eps l s) := by
  have h : Continuous fun s : G ℚ Ω => ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (continuous_cycZ ℚ Ω l)
  have e : ∀ s : G ℚ Ω, eps l s = algebraMap ℚ_[l] (Qbar l) (((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) :=
    fun s => rfl
  simp only [e]
  have hc : Continuous (fun x : ℤ_[l] => (x : ℚ_[l])) := continuous_subtype_val
  exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp (hc.comp h)

theorem eps_eq_one_of_mem_Ine [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω} {v : Pl}
    (hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) (h : IsPlaceOver A v) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) :
    eps l σ = 1 := by
  have e : cycBar ℚ Ω l σ = cyc ℚ Ω l σ := (cyc_eq_map_cycZ ℚ Ω l σ).symm
  simp only [eps, e, cyc_eq_one_of_mem_Ine hl h hσ, Units.val_one]

theorem val_dt (W : R2 Ω l) (s : G ℚ Ω) : ((dt W s : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
  simp [dt, mat]

theorem dt_inv_eq (W : R2 Ω l) (h : dt W ^ 2 = 1) : (dt W)⁻¹ = dt W := by
  rw [pow_two] at h; exact inv_eq_of_mul_eq_one_right h

theorem mat_dual1_eq (W : R2 Ω l) (s : G ℚ Ω) :
    mat (dual1 W) s = (eps l s * (((dt W)⁻¹ s : (Qbar l)ˣ) : Qbar l)) • mat W s := by
  simp [mat, dual1, tw_val, eps]

theorem mat_dual1_eq' (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) :
    mat (dual1 W) s = (eps l s * (mat W s).det) • mat W s := by
  rw [mat_dual1_eq, dt_inv_eq W h, val_dt]

theorem continuous_mat (W : R2 Ω l) (hW : Continuous W) : Continuous fun s => mat W s :=
  Units.continuous_val.comp hW

theorem continuous_mat_dual1 (W : R2 Ω l) (hW : Continuous W) (h : dt W ^ 2 = 1) :
    Continuous fun s => mat (dual1 W) s := by
  simp only [mat_dual1_eq' W h]
  exact (continuous_eps.mul (continuous_mat W hW).matrix_det).smul (continuous_mat W hW)

theorem om_add_left (x x' y : Fin 2 → Qbar l) : om (x + x') y = om x y + om x' y := by
  simp only [om, Pi.add_apply]; ring

theorem om_add_right (x y y' : Fin 2 → Qbar l) : om x (y + y') = om x y + om x y' := by
  simp only [om, Pi.add_apply]; ring

theorem om_mulVec_smul (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (c : Qbar l) (x y : Fin 2 → Qbar l) :
    om (M *ᵥ x) ((c • M) *ᵥ y) = c * M.det * om x y := by
  simp only [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.smul_apply, smul_eq_mul]
  ring

theorem om_pair (W : R2 Ω l) (s : G ℚ Ω) (x y : Fin 2 → Qbar l) :
    om (mat W s *ᵥ x) (mat (dual1 W) s *ᵥ y) = eps l s * om x y := by
  rw [mat_dual1_eq, om_mulVec_smul, mul_assoc (eps l s), ← val_dt, ← Units.val_mul,
    show (dt W)⁻¹ s * dt W s = 1 by simp, Units.val_one, mul_one]

theorem cup_cocycle (W : R2 Ω l) {a b : G ℚ Ω → Fin 2 → Qbar l} (ha : a ∈ Z1 (Loc.colRep W))
    (hb : b ∈ Z1 (Loc.colRep (dual1 W))) (r s t : G ℚ Ω) :
    eps l r * cup W a b s t + cup W a b r (s * t) = cup W a b (r * s) t + cup W a b r s := by
  simp only [cup]
  rw [cocycle_mulVec hb s t, cocycle_mulVec ha r s, mat_mul' (dual1 W) r s, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_add, om_add_right, om_add_left, om_pair]
  ring

theorem cg_refl (n : ℕ) (x : Qbar l) : Cg n x x := by
  simp [Cg]

theorem vanish_NS [IsAlgClosure ℚ Ω] {S : Finset Pl} (hS : ContainsAbove S l) (V : R2 Ω l)
    (hV : Continuous fun s => mat V s) {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep V))
    (hu : Unr V z) (hI : ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ V.ker) :
    ∀ α ∈ NS Ω (S : Set Pl), mat V α = 1 ∧ z α = 0 := by
  have z1 : z 1 = 0 := by
    have := cocycle_mulVec hz 1 1
    rw [mul_one, mat_one', Matrix.one_mulVec] at this
    simpa using this
  let K : Subgroup (G ℚ Ω) :=
    { carrier := {g | mat V g = 1 ∧ z g = 0}
      one_mem' := ⟨mat_one' V, z1⟩
      mul_mem' := by
        rintro g h ⟨h1, h2⟩ ⟨h3, h4⟩
        exact ⟨by rw [mat_mul', h1, h3, mul_one], by rw [cocycle_mulVec hz, h2, h4, Matrix.mulVec_zero, add_zero]⟩
      inv_mem' := by
        rintro g ⟨h1, h2⟩
        have hm : mat V g⁻¹ * mat V g = 1 := by rw [← mat_mul', inv_mul_cancel, mat_one']
        rw [h1, mul_one] at hm
        refine ⟨hm, ?_⟩
        have := cocycle_mulVec hz g⁻¹ g
        rw [inv_mul_cancel, z1, h2, Matrix.mulVec_zero, add_zero] at this
        exact this.symm }
  have hK : K.Normal := ⟨fun g ⟨h1, h2⟩ x => by
    have hm : mat V (x * g * x⁻¹) = 1 := by
      rw [mat_mul', mat_mul', h1, mul_one, ← mat_mul', mul_inv_cancel, mat_one']
    refine ⟨hm, ?_⟩
    rw [cob_conj hz x g 0 (by rw [h2, Matrix.mulVec_zero, sub_zero]), hm, Matrix.one_mulVec, sub_self]⟩
  have hcl : IsClosed (K : Set (G ℚ Ω)) :=
    (isClosed_eq hV continuous_const).inter (isClosed_eq hz.1 continuous_const)
  intro α hα
  have hle : NS Ω (S : Set Pl) ≤ K := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hcl
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, A, hA, hτ⟩ := hτ
    have hv' : v ∉ S := by simpa using hv
    have hτ' : τ ∈ Ine (F := ℚ) A := hτ
    have hm : mat V τ = 1 := by
      have h1 : V τ = 1 := hI v hv' A hA hτ'
      simp [mat, h1]
    refine ⟨hm, ?_⟩
    have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv' (hS v h)
    obtain ⟨B0, hB0, x, hx⟩ := hu v hl
    obtain ⟨x', hx'⟩ := (place_indep l Ω V z hz v B0 A hB0 hA).1 ⟨x, hx⟩
    rw [hx' τ hτ', hm, Matrix.one_mulVec, sub_self]
  exact hle hα

theorem cupProductDualTwist_isTwoCocycle_unramified_alt : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ)
    (S : Finset Pl) (W : R2 Ω l) (a b : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) →
    dt W ^ 2 = 1 → ContainsAbove S l →
    (∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) →
    a ∈ Z1 (Loc.colRep W) → b ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, a s i ∈ c.O) → (∀ s i, b s i ∈ c.O) →
    Unr W a → Unr (dual1 W) b → Coc2 c n S (cup W a b) := by
  intro l _ Ω _ _ _ c n S W a b hW hWi hdt hS hI ha hb hai hbi hua hub
  have hWc := continuous_mat W hW
  have hDc := continuous_mat_dual1 W hW hdt
  have hDI : ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ (dual1 W).ker := by
    intro w hw B hB σ hσ
    have h1 : W σ = 1 := hI w hw B hB hσ
    have hm : mat W σ = 1 := by simp [mat, h1]
    have he : eps l σ = 1 := eps_eq_one_of_mem_Ine (fun h => hw (hS w h)) hB hσ
    show dual1 W σ = 1
    apply Units.ext
    show mat (dual1 W) σ = 1
    rw [mat_dual1_eq' W hdt, hm, he, Matrix.det_one, mul_one, one_smul]
  have vW := vanish_NS hS W hWc ha hua hI
  have vD := vanish_NS hS (dual1 W) hDc hb hub hDI
  have hker : (toGS Ω (S : Set Pl)).ker = NS Ω (S : Set Pl) := QuotientGroup.ker_mk' _
  have hD : ∀ s i j, mat (dual1 W) s i j ∈ c.O := by
    intro s i j
    rw [mat_dual1_eq' W hdt, Matrix.smul_apply, smul_eq_mul, Matrix.det_fin_two]
    exact c.O.mul_mem (c.O.mul_mem (eps_mem c s)
      (c.O.sub_mem (c.O.mul_mem (hWi s 0 0) (hWi s 1 1)) (c.O.mul_mem (hWi s 0 1) (hWi s 1 0)))) (hWi s i j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have ha' : Continuous a := ha.1
    have hb' : Continuous b := hb.1
    have hA : ∀ i, Continuous fun p : G ℚ Ω × G ℚ Ω => a p.1 i :=
      fun i => (continuous_apply i).comp (ha'.comp continuous_fst)
    have hB : ∀ i, Continuous fun p : G ℚ Ω × G ℚ Ω => b p.2 i :=
      fun i => (continuous_apply i).comp (hb'.comp continuous_snd)
    have hM : ∀ i j, Continuous fun p : G ℚ Ω × G ℚ Ω => mat (dual1 W) p.1 i j :=
      fun i j => (continuous_apply j).comp ((continuous_apply i).comp (hDc.comp continuous_fst))
    simp only [cup, om, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact ((hA 0).mul (((hM 1 0).mul (hB 0)).add ((hM 1 1).mul (hB 1)))).sub
      ((hA 1).mul (((hM 0 0).mul (hB 0)).add ((hM 0 1).mul (hB 1))))
  · intro s t
    simp only [cup, om, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.sub_mem
      (c.O.mul_mem (hai s 0) (c.O.add_mem (c.O.mul_mem (hD s 1 0) (hbi t 0)) (c.O.mul_mem (hD s 1 1) (hbi t 1))))
      (c.O.mul_mem (hai s 1) (c.O.add_mem (c.O.mul_mem (hD s 0 0) (hbi t 0)) (c.O.mul_mem (hD s 0 1) (hbi t 1))))
  · intro r s t
    rw [cup_cocycle W ha hb r s t]
    exact cg_refl n _
  · intro s t α hα β hβ
    rw [hker] at hα hβ
    have e : cup W a b (s * α) (t * β) = cup W a b s t := by
      simp only [cup]
      rw [cocycle_mulVec ha s α, (vW α hα).2, Matrix.mulVec_zero, add_zero, cocycle_mulVec hb t β, (vD β hβ).2,
        Matrix.mulVec_zero, add_zero, mat_mul', (vD α hα).1, mul_one]
    rw [e]
    exact cg_refl n _

end GlobalTheory.Ord2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommutatorDetNonzero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem commutator_H0_has_no_eigenvalue_one : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W →
    ∃ φ ∈ ⁅H0g W, H0g W⁆, (mat W φ - 1).det ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.CommutingExistence.main
  | exact _root_.GlobalTheory.CommutingExistence.main
  | (apply _root_.GlobalTheory.CommutingExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommutingExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommutingExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommutingExistence.main ..)

end GlobalTheory.Ord2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFrobeniusPowInvMulMemOpenSubgroupStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_pow_inv_mul_mem_open_subgroup : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (q : Pl) (B : ValuationSubring Ω) (K : Subgroup (G ℚ Ω)), IsPlaceOver B q → Ine (F := ℚ) B ≤ K → IsOpen ((K.subgroupOf (Dec (F := ℚ) B) : Subgroup ↥(Dec (F := ℚ) B)) : Set ↥(Dec (F := ℚ) B)) → ∃ (φ : ↥(Dec (F := ℚ) B)) (m : ℕ), 0 < m ∧ ((φ ^ m : ↥(Dec (F := ℚ) B)) : G ℚ Ω) ∈ K ∧ ∀ N : ℕ, 0 < N → ∃ d : ↥(Dec (F := ℚ) B) →* Multiplicative (ZMod (m * N)), IsOpen (d.ker : Set ↥(Dec (F := ℚ) B)) ∧ ∀ s : ↥(Dec (F := ℚ) B), (((φ ^ (Multiplicative.toAdd (d s)).val)⁻¹ * s : ↥(Dec (F := ℚ) B)) : G ℚ Ω) ∈ K := by
  first | exact @GlobalTheory.Ord2.exists_frob_pow_inv_mul_mem | exact GlobalTheory.Ord2.exists_frob_pow_inv_mul_mem | (intros; apply GlobalTheory.Ord2.exists_frob_pow_inv_mul_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsPlaceOverRat
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory

theorem exists_isPlaceOver_rat :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (q : Pl),
      ∃ B : ValuationSubring Ω, IsPlaceOver B q := by
  intro Ω _ _ _ q
  exact ReciprocityTheory.Gal.exists_isPlaceOver Ω q

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitCharacterOfIntegralCyclotomicProductStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitCharacter_of_integral_cyclotomic_product : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (k k' : G ℚ Ω → Qbar l), ContinuousOn k (Dec (F := ℚ) A) → (∀ s ∈ Dec (F := ℚ) A, k s ∈ c.O ∧ k' s ∈ c.O ∧ k s * k' s = eps l s) → (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, k (s * t) = k s * k t) → ∃ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) ∧ ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = k g := by
  first | exact @GlobalTheory.LocChar.unit_of_integral | exact GlobalTheory.LocChar.unit_of_integral | (intros; apply GlobalTheory.LocChar.unit_of_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisHomZlLipschitzOfKerLeLinearGroup
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem norm_natPrime_pow (l : ℕ) [Fact l.Prime] (m : ℕ) : ‖((l : ℕ) : Qbar l) ^ m‖ = ((l : ℝ)⁻¹) ^ m := by
  rw [norm_pow]
  congr 1
  have : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [this, norm_algebraMap', Padic.norm_p]

theorem hom_lipschitz_of_ker_le : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]), Continuous r → (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → Continuous lam → r.ker ≤ lam.ker → ∃ C : ℝ, ∀ (m : ℕ) (g : Γ), (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖) → ‖(lam g).toAdd‖ ≤ C * ‖((l : ℕ) : Qbar l) ^ m‖ := by
  intro l _ c Γ _ _ _ _ r lam hr hO hlam hker
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.lipschitz_of_contraction_per_level l Γ
    (fun m g => ∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖) lam
    (fun m g h i j => (h i j).trans (by
      rw [norm_natPrime_pow, norm_natPrime_pow, pow_succ]
      have h1 : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
      have h2 : (l : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)
      exact mul_le_of_le_one_right (pow_nonneg h1 _) h2))
    (_root_.GlobalTheory.lam_small_of_deep_congruence l Γ r lam hr hlam hker) (_root_.GlobalTheory.DeepLevel.exists_pow_mul_of_deep_level l c Γ r hO)
  exact ⟨C, fun m g hg => by rw [norm_natPrime_pow]; exact hC m g hg⟩

end GlobalTheory.Ord2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualEqOneOfMemKerUnramifiedQ
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ a ∈ (toGS Ω (S : Set Pl)).ker, dual1 W a = 1 := by
  intro l _ Ω _ _ _ e S A W hW a ha
  set T : Subgroup (G ℚ Ω) := W.ker ⊓ (cycZ ℚ Ω l).ker with hT
  have hTc : IsClosed (T : Set (G ℚ Ω)) := by
    have h1 : IsClosed (W.ker : Set (G ℚ Ω)) := isClosed_singleton.preimage hW.cont
    have h2 : IsClosed ((cycZ ℚ Ω l).ker : Set (G ℚ Ω)) := isClosed_singleton.preimage (continuous_cycZ ℚ Ω l)
    exact h1.inter h2
  have hNS : NS Ω (S : Set Pl) ≤ T := by
    refine Subgroup.topologicalClosure_minimal _ ?_ hTc
    apply Subgroup.normalClosure_le_normal
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, B, hB, hτ⟩ := hτ
    refine ⟨hW.unr v hv B hB hτ, ?_⟩
    have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (hW.above v h)
    exact GlobalTheory.WeilDeligne.cycZ_of_mem_Ine hB hl hτ
  have haT : a ∈ T := hNS ((QuotientGroup.eq_one_iff _).mp ha)
  have hWa : W a = 1 := haT.1
  have hca : cycZ ℚ Ω l a = 1 := haT.2
  have hcb : cycBar ℚ Ω l a = 1 := by simp [cycBar, hca]
  have hdt : dt W a = 1 := by simp [dt, hWa]
  apply Units.ext
  rw [dual1, tw_val]
  simp [hcb, hdt, hWa]

end GlobalTheory.Ord2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualMatrixMemCoefRingOfNorma
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∀ s i j, mat (dual1 W) s i j ∈ c.O := by
  intro l _ Ω _ _ _ e S A W hW c hc s i j

  have hdet : (mat W s).det ∈ c.O := by
    let M : Matrix (Fin 2) (Fin 2) c.O := Matrix.of fun i j => ⟨mat W s i j, hc s i j⟩
    have hM : M.map c.O.val = mat W s := by ext i j; rfl
    have h := RingHom.map_det (SubringClass.subtype c.O) M
    rw [RingHom.mapMatrix_apply] at h
    rw [← hM]
    have e1 : (M.map c.O.val) = M.map (SubringClass.subtype c.O) := rfl
    rw [e1, ← h]
    exact (M.det).2

  have hinv : (((dt W s)⁻¹ : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
    have h2 : dt W s ^ 2 = 1 := by
      have := congrArg (fun f => f s) hW.det2
      simpa using this
    have : (dt W s)⁻¹ = dt W s := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, h2]
    rw [this]; rfl
  have hcyc : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) ∈ c.O := by
    show ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) ∈ c.O
    exact c.O.algebraMap_mem _
  have hval : mat (dual1 W) s i j = ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) * (((dt W s)⁻¹ : (Qbar l)ˣ) : Qbar l) * mat W s i j := by
    simp only [mat, dual1, tw_val, Matrix.smul_apply, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul, MonoidHom.inv_apply]
  rw [hval, hinv]
  exact c.O.mul_mem (c.O.mul_mem hcyc hdet) (hc s i j)

end GlobalTheory.Ord2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualUpperTriangularDecomposi
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_upperTriangular_decompGroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ s ∈ Dec (F := ℚ) A, mat (dual1 W) s 1 0 = 0 := by
  intro l _ Ω _ _ _ e S A W hW s hs
  have h := hW.upper s hs
  simp only [mat, dual1, tw_val, Matrix.smul_apply, smul_eq_mul] at h ⊢
  rw [h, mul_zero]

end GlobalTheory.Ord2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTorsionQuotientConjInvariantDecompositionStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaTorsionQuotient_conj_invariant_decomposition : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl) (B : ValuationSubring Ω) (M : Type) [AddCommGroup M] (u : G ℚ Ω → M), IsPlaceOver B w → l ^ n ∣ normV w - 1 → 1 ≤ n → (∀ x : M, l ^ n • x = 0) → IsLocallyConstant (fun s : Ine (F := ℚ) B => u s) → (∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, u (s * t) = u s + u t) → ∀ g ∈ Dec (F := ℚ) B, ∀ s ∈ Ine (F := ℚ) B, u (g * s * g⁻¹) = u s := by
  first | exact @GlobalTheory.TameConjInv.conj_invariant | exact GlobalTheory.TameConjInv.conj_invariant | (intros; apply GlobalTheory.TameConjInv.conj_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleRestrictionOfIso
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.IrrConj

theorem isIrrSub_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ}
    (H H' : Subgroup Γ) (hH : ∀ s, s ∈ H → s ∈ H')
    (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k) (hg : ∀ s, r' s = g * r s * g⁻¹)
    (hr : IsIrrSub (r.comp H.subtype) ⊤) : IsIrrSub (r'.comp H'.subtype) ⊤ := by
  first
  | exact @_root_.GlobalTheory.ConjugateIrreducibility.target
  | exact _root_.GlobalTheory.ConjugateIrreducibility.target
  | (apply _root_.GlobalTheory.ConjugateIrreducibility.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateIrreducibility.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateIrreducibility.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateIrreducibility.target ..)

theorem dt_eq_of_repIso {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
    (W W' : R2 Ω l) (g : GL (Fin 2) (Qbar l)) (hg : ∀ s, W' s = g * W s * g⁻¹) (s : G ℚ Ω) :
    dt W' s = dt W s := by
  simp only [dt, MonoidHom.comp_apply, hg s, map_mul, map_inv]
  rw [mul_comm (Matrix.GeneralLinearGroup.det g), mul_assoc, mul_inv_cancel, mul_one]

theorem irr_of_repIso : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (W W' : R2 Ω l),
    RepIso W W' → IsIrr (W.comp (H0g W).subtype) → IsIrr (W'.comp (H0g W').subtype) := by
  intro Ω _ _ l _ W W' ⟨g, hg⟩ h
  refine isIrrSub_conj (H0g W) (H0g W') ?_ W W' g hg h
  intro s hs
  simp only [H0g, Subgroup.mem_inf, MonoidHom.mem_ker] at hs ⊢
  exact ⟨hs.1, by rw [dt_eq_of_repIso W W' g hg]; exact hs.2⟩

end GlobalTheory.IrrConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerScalarLayerLinkOfShapiroSpecializationAppr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KZ

theorem spLink_of_spec_approx (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (e : ℕ)
    (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (y : G ℚ Ω → Fin 2 → Qbar l)
    (h : ∀ r, ∀ s ∈ Ine (F := ℚ) A, cycBar ℚ Ω l s = 1 →
      ‖y s 1 - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s 1‖ ≤
        ‖((l : ℕ) : Qbar l) ^ r‖) :
    SpLink A e χ (fun r s x => Y r s x 1) y := by
  intro n
  refine ⟨n, fun r hr s hs hc => ?_⟩
  have h1 := h r s hs hc
  have heq : spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s 1 =
      sp (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Y r s x 1) s := by
    simp only [spec, sp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq] at h1
  unfold Cg
  refine h1.trans ?_
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _) hr

end GlobalTheory.KZ
end

