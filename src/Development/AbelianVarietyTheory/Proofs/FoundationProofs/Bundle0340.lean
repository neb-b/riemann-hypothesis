module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimePowMulDeepCongruenceLevel
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.DeepLevel

variable {l : ℕ} [Fact l.Prime]

theorem norm_natCast_l : ‖((l : ℕ) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  have : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [this, norm_algebraMap', Padic.norm_p]

theorem eO_toNat_pos (c : Coef l) : 1 ≤ (UpperTheory.V.Base.eO l c.O).toNat := by
  obtain ⟨-, -, -, -, -, he0, -, hev, -⟩ := UpperTheory.V.Base.dvrFacts l c.O
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have htop : UpperTheory.V.Base.eO l c.O ≠ ⊤ := by
    rw [hev, Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hl0
  have : (UpperTheory.V.Base.eO l c.O).toNat ≠ 0 := by
    intro h; exact he0 ((ENat.toNat_eq_zero).1 h |>.resolve_right htop)
  omega

theorem norm_le_one (c : Coef l) (y : c.O) : ‖(y : PadicAlgCl l)‖ ≤ 1 := by
  by_cases hy : y = 0
  · simp [hy]
  have h := UpperTheory.V.Base.normO l c.O y hy
  have he := eO_toNat_pos c
  have hl : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
  have hl1 : (l : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)
  have : ‖(y : PadicAlgCl l)‖ ^ (UpperTheory.V.Base.eO l c.O).toNat ≤ 1 := by
    rw [h]; exact pow_le_one₀ hl hl1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 this

end GlobalTheory.DeepLevel

namespace GlobalTheory.DeepLevel

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_iff_dvd (c : Coef l) (x : c.O) (k : ℕ) :
    ‖(x : PadicAlgCl l)‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ k‖ ↔ ((l : ℕ) : c.O) ^ k ∣ x := by
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact dvd_zero _
    obtain ⟨-, -, -, -, -, -, -, hev, -⟩ := UpperTheory.V.Base.dvrFacts l c.O
    have h := UpperTheory.V.Base.normO l c.O x hx0
    have he := eO_toNat_pos c
    set e := (UpperTheory.V.Base.eO l c.O).toNat with he_def
    set v := (IsDiscreteValuationRing.addVal c.O x).toNat with hv_def
    have hq0 : (0 : ℝ) < (l : ℝ)⁻¹ := by
      have := (Fact.out : l.Prime).pos; positivity
    have hq1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
    rw [norm_pow, norm_natCast_l] at hx
    have h2 : ‖(x : PadicAlgCl l)‖ ^ e ≤ ((l : ℝ)⁻¹ ^ k) ^ e := pow_le_pow_left₀ (norm_nonneg _) hx e
    rw [h, ← pow_mul] at h2
    have h3 : k * e ≤ v := (pow_le_pow_iff_right_of_lt_one₀ hq0 hq1).1 h2
    have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
      intro h0
      have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h0]; rfl
      have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
      exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
    have htl : IsDiscreteValuationRing.addVal c.O ((l : ℕ) : c.O) ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hl0
    have htx : IsDiscreteValuationRing.addVal c.O x ≠ ⊤ := by
      rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hx0
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
      ← ENat.coe_toNat htl, ← ENat.coe_toNat htx, ← hev, ← he_def, ← hv_def]
    rw [nsmul_eq_mul]
    exact_mod_cast h3
  · rintro ⟨y, rfl⟩
    have : (((l : ℕ) : c.O) ^ k * y : c.O) = ((l : ℕ) : PadicAlgCl l) ^ k * (y : PadicAlgCl l) := by simp
    rw [this, norm_mul]
    calc _ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ k‖ * 1 := mul_le_mul_of_nonneg_left (norm_le_one c y) (norm_nonneg _)
      _ = _ := mul_one _

end GlobalTheory.DeepLevel

namespace GlobalTheory.DeepLevel

theorem pow_expand {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (t : R) (m : ℕ) (hm : 2 ≤ m) (B : Matrix n n R) (N : ℕ) :
    ∃ C : Matrix n n R, (1 + t ^ m • B) ^ N = 1 + ((N : R) * t ^ m) • B + t ^ (m + 2) • C := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  induction N with
  | zero => exact ⟨0, by simp⟩
  | succ N ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨((N : R) * t ^ k) • (B * B) + C + t ^ (k + 2) • (C * B), ?_⟩
    rw [pow_succ, hC]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_one, one_mul, smul_add]
    push_cast
    module

end GlobalTheory.DeepLevel

namespace GlobalTheory.DeepLevel

variable {l : ℕ} [Fact l.Prime]

def intRep (c : Coef l) {Γ : Type} [Group Γ] (r : Γ →* GL (Fin 2) (PadicAlgCl l))
    (hint : ∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) i j ∈ c.O) :
    Γ →* Matrix (Fin 2) (Fin 2) c.O where
  toFun g := Matrix.of fun i j => ⟨_, hint g i j⟩
  map_one' := by
    ext i j
    simp only [map_one, Units.val_one, Matrix.of_apply]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  map_mul' g h := by
    apply Matrix.map_injective (f := (c.O.val : c.O →+* PadicAlgCl l)) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul]
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, Units.val_mul]
    rfl

theorem intRep_map (c : Coef l) {Γ : Type} [Group Γ] (r : Γ →* GL (Fin 2) (PadicAlgCl l))
    (hint : ∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) i j ∈ c.O) (g : Γ) (i j : Fin 2) :
    ((((r g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) - 1) i j) : PadicAlgCl l) =
      ((((intRep c r hint g) - 1) i j : c.O) : PadicAlgCl l) := by
  simp only [Matrix.sub_apply]
  rw [Subalgebra.coe_sub]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem level_iff (c : Coef l) {Γ : Type} [Group Γ] (r : Γ →* GL (Fin 2) (PadicAlgCl l))
    (hint : ∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) i j ∈ c.O) (g : Γ) (k : ℕ) :
    (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) - 1) i j‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ k‖) ↔
      ∃ B : Matrix (Fin 2) (Fin 2) c.O, intRep c r hint g = 1 + (((l : ℕ) : c.O) ^ k) • B := by
  simp only [intRep_map c r hint, norm_le_iff_dvd]
  constructor
  · intro h
    choose B hB using h
    refine ⟨Matrix.of B, ?_⟩
    ext i j
    have := hB i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← this, Matrix.sub_apply]
    ring_nf
  · rintro ⟨B, hB⟩ i j
    exact ⟨B i j, by rw [hB]; simp⟩

end GlobalTheory.DeepLevel

namespace GlobalTheory.DeepLevel

variable {l : ℕ} [Fact l.Prime]

theorem pow_step (c : Coef l) (A B : Matrix (Fin 2) (Fin 2) c.O) (m : ℕ) (hm : 2 ≤ m)
    (hA : A = 1 + (((l : ℕ) : c.O) ^ m) • B) :
    ∃ B' : Matrix (Fin 2) (Fin 2) c.O, A ^ l = 1 + (((l : ℕ) : c.O) ^ (m + 1)) • B' ∧
      B'.map (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : c.O)})) =
        B.map (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : c.O)})) := by
  obtain ⟨C, hC⟩ := pow_expand ((l : ℕ) : c.O) m hm B l
  refine ⟨B + ((l : ℕ) : c.O) • C, ?_, ?_⟩
  · rw [hA, hC, smul_add, smul_smul, show ((l : ℕ) : c.O) * ((l : ℕ) : c.O) ^ m = ((l : ℕ) : c.O) ^ (m + 1) by ring,
      show ((l : ℕ) : c.O) ^ (m + 2) = ((l : ℕ) : c.O) ^ (m + 1) * ((l : ℕ) : c.O) by ring]
    abel
  · ext i j
    have h0 : Ideal.Quotient.mk (Ideal.span {((l : ℕ) : c.O)}) ((l : ℕ) : c.O) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    simp [Matrix.map_apply, h0]

def img (c : Coef l) {Γ : Type} [Group Γ] (ρ : Γ →* Matrix (Fin 2) (Fin 2) c.O) (m : ℕ) :
    Set (Matrix (Fin 2) (Fin 2) (c.O ⧸ Ideal.span {((l : ℕ) : c.O)})) :=
  {X | ∃ g B, ρ g = 1 + (((l : ℕ) : c.O) ^ m) • B ∧ B.map (Ideal.Quotient.mk _) = X}

theorem img_mono (c : Coef l) {Γ : Type} [Group Γ] (ρ : Γ →* Matrix (Fin 2) (Fin 2) c.O) (m : ℕ) (hm : 2 ≤ m) :
    img c ρ m ⊆ img c ρ (m + 1) := by
  rintro X ⟨g, B, hg, rfl⟩
  obtain ⟨B', h1, h2⟩ := pow_step c (ρ g) B m hm hg
  exact ⟨g ^ l, B', by rw [map_pow, h1], h2⟩

theorem exists_pow_mul_of_deep_level : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] (r : Γ →* GL (Fin 2) (Qbar l)), (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ g : Γ, (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ (m + 1)‖) → ∃ h g' : Γ, (∀ i j, ‖((r h : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖) ∧ (∀ i j, ‖((r g' : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ (m + 2)‖) ∧ g = h ^ l * g' := by
  intro l _ c Γ _ r hint
  set ρ := intRep c r hint with hρ
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h0
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h0]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  haveI : Finite (c.O ⧸ Ideal.span {((l : ℕ) : c.O)}) :=
    (UpperTheory.V.X.So.levFacts l c.O ((l : ℕ) : c.O) hl0 _ ⟨LinearEquiv.refl _ _⟩).1
  haveI : Finite (Matrix (Fin 2) (Fin 2) (c.O ⧸ Ideal.span {((l : ℕ) : c.O)})) :=
    inferInstanceAs (Finite (Fin 2 → Fin 2 → _))
  let F : ℕ →o Set (Matrix (Fin 2) (Fin 2) (c.O ⧸ Ideal.span {((l : ℕ) : c.O)})) :=
    ⟨fun n => img c ρ (n + 2), monotone_nat_of_le_succ fun n => img_mono c ρ (n + 2) (by omega)⟩
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition F
  refine ⟨n + 2, fun m hm g hg => ?_⟩
  have hS : img c ρ (m + 1) ⊆ img c ρ m := by
    have e1 := hn (m - 2) (by omega)
    have e2 := hn (m - 1) (by omega)
    have h1 : F (m - 2) = img c ρ m := by
      show img c ρ (m - 2 + 2) = _; congr 1; omega
    have h2 : F (m - 1) = img c ρ (m + 1) := by
      show img c ρ (m - 1 + 2) = _; congr 1; omega
    rw [← h1, ← h2, ← e1, ← e2]
  obtain ⟨B, hB⟩ := (level_iff c r hint g (m + 1)).1 hg
  obtain ⟨h, B₁, hh, hB₁⟩ := hS ⟨g, B, hB, rfl⟩
  obtain ⟨B₂, hh2, hB₂⟩ := pow_step c (ρ h) B₁ m (by omega) hh
  have hD : ∀ i j, ∃ d : c.O, B i j - B₂ i j = ((l : ℕ) : c.O) * d := by
    intro i j
    have := congrFun (congrFun (hB₁.symm.trans hB₂.symm) i) j
    simp only [Matrix.map_apply] at this
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 this)
    exact ⟨d, by rw [← hd]; ring⟩
  choose D hDD using hD
  refine ⟨h, (h ^ l)⁻¹ * g, (level_iff c r hint h m).2 ⟨B₁, hh⟩, (level_iff c r hint _ (m + 2)).2
    ⟨ρ (h ^ l)⁻¹ * Matrix.of D, ?_⟩, (mul_inv_cancel_left _ _).symm⟩
  have hBB : B = B₂ + ((l : ℕ) : c.O) • Matrix.of D := by
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hDD]
    ring_nf
  have hinv : ρ (h ^ l)⁻¹ * ρ (h ^ l) = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hpow : ρ (h ^ l) = 1 + (((l : ℕ) : c.O) ^ (m + 1)) • B₂ := by rw [map_pow, hh2]
  have hg' : ρ g = ρ (h ^ l) + (((l : ℕ) : c.O) ^ (m + 2)) • Matrix.of D := by
    rw [hB, hpow, hBB, smul_add, smul_smul, ← pow_succ]
    abel
  rw [map_mul, hg', mul_add, hinv, Matrix.mul_smul]

end GlobalTheory.DeepLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUpperTriangularConjIntegralCompact
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.StableLatticeTriangular

theorem exists_conj_of_bounded {F : Type} [NormedField F] [IsUltrametricDist F] {Γ : Type} [Group Γ]
    (E : Subfield F) (hK : IsCompact {x : F | x ∈ E ∧ ‖x‖ ≤ 1})
    (r : Γ →* GL (Fin 2) F) (hE : ∀ g i j, (r g : Matrix (Fin 2) (Fin 2) F) i j ∈ E)
    (c : F) (hcE : c ∈ E) (hc0 : c ≠ 0)
    (hc : ∀ g i j, ‖(r g : Matrix (Fin 2) (Fin 2) F) i j * c‖ ≤ 1) :
    ∃ B : GL (Fin 2) F, (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧ ∀ g i j,
      ((B * r g * B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ E ∧
      ‖((B * r g * B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1 := by
  classical
  set K : Set F := {x : F | x ∈ E ∧ ‖x‖ ≤ 1} with hKdef
  set L : Set (Fin 2 → F) := {x | ∀ i, x i ∈ K} ∩
    {x | ∀ g i, ‖((r g : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i‖ ≤ 1} with hL
  have mkL : ∀ x : Fin 2 → F, (∀ i, x i ∈ E) →
      (∀ g i, ‖((r g : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i‖ ≤ 1) → x ∈ L := by
    intro x h1 h2
    refine ⟨fun i => ⟨h1 i, ?_⟩, h2⟩
    simpa using h2 1 i
  have hLc : IsCompact L := by
    refine (isCompact_pi_infinite (fun _ => hK)).inter_right ?_
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun g => isClosed_iInter fun i => ?_
    refine isClosed_le ?_ continuous_const
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hL0c : IsCompact (L ∩ {x | x 1 = 0}) :=
    hLc.inter_right (isClosed_eq (continuous_apply 1) continuous_const)
  have hs : ∀ j : Fin 2, (Pi.single j c : Fin 2 → F) ∈ L := by
    intro j
    refine mkL _ (fun i => ?_) (fun g i => ?_)
    · rw [Pi.single_apply]; split_ifs
      · exact hcE
      · exact E.zero_mem
    · rw [Matrix.mulVec_single]; simpa using hc g i j
  have hr : ∀ h, ∀ x ∈ L, (r h : Matrix (Fin 2) (Fin 2) F) *ᵥ x ∈ L := by
    intro h x hx
    refine mkL _ (fun i => ?_) (fun g i => ?_)
    · simp only [Matrix.mulVec, dotProduct]
      exact E.sum_mem fun j _ => E.mul_mem (hE h i j) (hx.1 j).1
    · rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
      exact hx.2 _ _
  have hsub : ∀ x ∈ L, ∀ y ∈ L, ∀ t ∈ K, x - t • y ∈ L := by
    intro x hx y hy t ht
    refine mkL _ (fun i => ?_) (fun g i => ?_)
    · exact E.sub_mem (hx.1 i).1 (E.mul_mem ht.1 (hy.1 i).1)
    · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx.2 g i) ?_)
      rw [norm_neg, norm_mul]
      exact mul_le_one₀ ht.2 (norm_nonneg _) (hy.2 g i)
  obtain ⟨f1, hf1, hm1⟩ := hLc.exists_isMaxOn ⟨_, hs 1⟩
    (f := fun x : Fin 2 → F => ‖x 1‖) (by fun_prop)
  obtain ⟨f0, hf0, hm0⟩ := hL0c.exists_isMaxOn ⟨Pi.single 0 c, hs 0, by simp⟩
    (f := fun x : Fin 2 → F => ‖x 0‖) (by fun_prop)
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have h1pos : 0 < ‖f1 1‖ := lt_of_lt_of_le hcpos (by simpa using hm1 (hs 1))
  have h0pos : 0 < ‖f0 0‖ := lt_of_lt_of_le hcpos (by
    simpa using hm0 (a := Pi.single 0 c) ⟨hs 0, by simp⟩)
  have h1ne : f1 1 ≠ 0 := norm_pos_iff.mp h1pos
  have h0ne : f0 0 ≠ 0 := norm_pos_iff.mp h0pos
  have hf01 : f0 1 = 0 := hf0.2
  let Pm : Matrix (Fin 2) (Fin 2) F := !![f0 0, f1 0; 0, f1 1]
  have hdet : Pm.det ≠ 0 := by
    simp [Pm, Matrix.det_fin_two, h0ne, h1ne]
  let P : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero Pm hdet
  have hP : (P : Matrix (Fin 2) (Fin 2) F) = Pm := rfl
  have key : ∀ x ∈ L, ∃ v : Fin 2 → F, (∀ i, v i ∈ K) ∧ x = Pm *ᵥ v := by
    intro x hx
    have ht : x 1 / f1 1 ∈ K := ⟨E.div_mem (hx.1 1).1 (hf1.1 1).1, by
      rw [norm_div, div_le_one h1pos]; exact hm1 hx⟩
    have hy := hsub x hx f1 hf1 _ ht
    have hy1 : (x - (x 1 / f1 1) • f1) 1 = 0 := by
      simp [div_mul_cancel₀ _ h1ne]
    have hs' : (x - (x 1 / f1 1) • f1) 0 / f0 0 ∈ K :=
      ⟨E.div_mem (hy.1 0).1 (hf0.1.1 0).1, by
        rw [norm_div, div_le_one h0pos]; exact hm0 ⟨hy, hy1⟩⟩
    refine ⟨![(x - (x 1 / f1 1) • f1) 0 / f0 0, x 1 / f1 1], ?_, ?_⟩
    · intro i; fin_cases i
      · exact hs'
      · exact ht
    · ext i; fin_cases i
      · simp [Pm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        ring
      · simp [Pm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
  refine ⟨P⁻¹, ?_, fun g i j => ?_⟩
  · have h : (Pm * ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) 1 0 = 0 := by
      rw [← hP, ← Units.val_mul, mul_inv_cancel]; simp
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    have e0 : Pm 1 0 = 0 := rfl
    have e1 : Pm 1 1 = f1 1 := rfl
    rw [e0, e1, zero_mul, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left h1ne
  · have hcol : (fun k => Pm k j) ∈ L := by
      fin_cases j
      · convert hf0.1 using 1
        ext k; fin_cases k
        · rfl
        · exact hf01.symm
      · convert hf1 using 1
        ext k; fin_cases k <;> rfl
    obtain ⟨v, hv, hxv⟩ := key _ (hr g _ hcol)
    have : ((P⁻¹ * r g * P⁻¹⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = v i := by
      have h2 : ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ (Pm *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, ← hP, ← Units.val_mul, inv_mul_cancel]; simp
      rw [← hxv, Matrix.mulVec_mulVec] at h2
      rw [inv_inv, Units.val_mul, Units.val_mul, hP, ← h2]
      rfl
    rw [this]
    exact hv i

theorem exists_upperTriangular_conj_integral :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (E : IntermediateField ℚ_[l] (Qbar l)) (r : Γ →* GL (Fin 2) (Qbar l)), FiniteDimensional ℚ_[l] E → Continuous r → (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ E) → ∃ B : GL (Fin 2) (Qbar l), (B : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0 ∧ ∀ g i j, ((B * r g * B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ E ∧ ‖((B * r g * B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) i j‖ ≤ 1 := by
  intro l _ Γ _ _ _ E r hfin hcont hE
  have hK : IsCompact {x : Qbar l | x ∈ E.toSubfield ∧ ‖x‖ ≤ 1} := by
    let V : Submodule ℚ_[l] (Qbar l) := E.toSubalgebra.toSubmodule
    haveI : FiniteDimensional ℚ_[l] V := hfin
    haveI : ProperSpace V := FiniteDimensional.proper ℚ_[l] V
    have h := (isCompact_closedBall (0 : V) 1).image continuous_subtype_val
    convert h using 1
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h1⟩, by simpa using h2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa using hy⟩
  have hf : Continuous fun g : Γ => fun p : Fin 2 × Fin 2 =>
      (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) p.1 p.2 := by
    refine continuous_pi fun p => ?_
    exact (Units.continuous_val.comp hcont).matrix_elem p.1 p.2
  obtain ⟨C, hC⟩ := (isCompact_range hf).isBounded.exists_pos_norm_le
  obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt ℚ_[l] (inv_pos.mpr hC.1)
  have hn : ‖algebraMap ℚ_[l] (Qbar l) c‖ = ‖c‖ := norm_algebraMap' _ _
  refine exists_conj_of_bounded E.toSubfield hK r hE (algebraMap ℚ_[l] (Qbar l) c)
    (E.algebraMap_mem c) (norm_pos_iff.mp (hn ▸ hc0)) (fun g i j => ?_)
  rw [norm_mul, hn]
  have h1 : ‖(r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j‖ ≤ C :=
    (norm_le_pi_norm (fun p : Fin 2 × Fin 2 =>
      (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) p.1 p.2) (i, j)).trans (hC.2 _ ⟨g, rfl⟩)
  calc _ ≤ C * C⁻¹ := mul_le_mul h1 hc.le (norm_nonneg _) hC.1.le
    _ = 1 := mul_inv_cancel₀ hC.1.ne'

end GlobalTheory.StableLatticeTriangular
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasWeightNegOfCyclotomicPowOnInertia
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory

theorem hasWeight_neg_of_pow_cyc_inertia : ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ),
    Continuous (fun σ => (κ σ : Qbar l)) → ∀ (e m : ℕ), 1 ≤ m →
    (∀ σ ∈ Loc.Iq l, (κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ)) ^ m = 1) →
    Loc.HasWeight (MonoidHom.id (GQ l)) κ (-(e : ℤ)) := by
  intro l _ κ hκ e m hm h
  have hcyc : Continuous (Loc.cyc l l) := cyclotomicCharacter.continuous l ℚ_[l] (Om l)
  have ha : Continuous (algebraMap ℤ_[l] (Qbar l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l)]
    exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
  have hA : Continuous (fun σ => (Loc.cycA l l (Qbar l) σ : Qbar l)) :=
    Units.continuous_val.comp
      ((Continuous.units_map (algebraMap ℤ_[l] (Qbar l) : ℤ_[l] →* Qbar l) ha).comp hcyc)
  set f : GQ l → Qbar l := fun σ => ((κ σ * Loc.cycA l l (Qbar l) σ ^ (e : ℤ) : (Qbar l)ˣ) : Qbar l) with hf_def
  have hf : Continuous f := by
    have : f = fun σ => (κ σ : Qbar l) * (Loc.cycA l l (Qbar l) σ : Qbar l) ^ e := by
      funext σ
      simp only [hf_def, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
    rw [this]
    exact hκ.mul (hA.pow e)
  have hf1 : f 1 = 1 := by simp [hf_def]
  have hm0 : 0 < m := hm
  have hfin : ({z : Qbar l | z ^ m = 1} \ {1}).Finite := by
    refine Set.Finite.subset (Multiset.finite_toSet (Polynomial.nthRoots m (1 : Qbar l))) fun z hz => ?_
    exact (Polynomial.mem_nthRoots hm0).2 hz.1
  have ho : IsOpen (f ⁻¹' ({z : Qbar l | z ^ m = 1} \ {1})ᶜ) :=
    hfin.isClosed.isOpen_compl.preimage hf
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho
    (fun hx => hx.2 hf1)
  refine ⟨U.toOpenSubgroup.toSubgroup, U.toOpenSubgroup.isOpen, fun g hg hgI => ?_⟩
  have hgI' : g ∈ Loc.Iq l := hgI
  have hpow : f g ^ m = 1 := by
    have := congrArg Units.val (h g hgI')
    simpa [hf_def, Units.val_pow_eq_pow_val] using this
  have hone : f g = 1 := by
    by_contra hne
    exact hU hg ⟨hpow, hne⟩
  have hu : κ g * Loc.cycA l l (Qbar l) g ^ (e : ℤ) = 1 := Units.ext hone
  simp only [MonoidHom.id_apply, zpow_neg]
  exact eq_inv_of_mul_eq_one_left hu

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenKerAndIsLocallyConstant
section
namespace GlobalTheory.OpenKernelLocallyConstant

theorem isOpen_ker_and_isLocallyConstant {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (C : Type) [Group C] (N : ℕ) (ψ : Formalism.ConjugateSelfDual.G ℚ Ω →* C) (hN : N ≠ 0)
    (hψ : UpperTheory.V.Af.KillsMu N ψ) :
    IsOpen (↑(MonoidHom.ker ψ) : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) ∧
      IsLocallyConstant (⇑ψ : Formalism.ConjugateSelfDual.G ℚ Ω → C) := by
  classical
  have hopen : IsOpen (↑(MonoidHom.ker ψ) : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) := by
    have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
    let S : Set Ω := {z | z ^ N = 1}
    have hS : S.Finite := by
      refine (Polynomial.nthRoots N (1 : Ω)).toFinset.finite_toSet.subset ?_
      intro z hz
      have hz' : z ^ N = 1 := hz
      simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hN)] using hz'
    have : Finite S := hS.to_subtype
    have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => (halg.isAlgebraic x).isIntegral
    refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ S).fixingSubgroup) ?_
      (IntermediateField.fixingSubgroup_isOpen _)
    intro s hs
    rw [MonoidHom.mem_ker]
    refine hψ s ?_
    intro z hz
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs z
      (IntermediateField.subset_adjoin ℚ S hz)
  refine ⟨hopen, ?_⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (MonoidHom.ker ψ : Set (Formalism.ConjugateSelfDual.G ℚ Ω)),
    hopen.preimage (continuous_const.mul continuous_id), by simp, ?_⟩
  intro y hy
  have h : ψ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  exact h.symm

end GlobalTheory.OpenKernelLocallyConstant
end

