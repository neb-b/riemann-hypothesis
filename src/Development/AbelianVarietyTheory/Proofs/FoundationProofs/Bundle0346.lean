module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsQuotientMapToGSProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0337
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0339
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0338

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CohomologyKernelModPrimePowerKilledByFixedPow
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.Kill

variable {l : ℕ} [Fact l.Prime]

theorem mem_of_memE (c : Coef l) {x : Qbar l} (hE : MemE c x) (hx : ‖x‖ ≤ 1) : x ∈ c.O := by
  obtain ⟨k, hk⟩ := hE
  have hl0 : ((l : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hn : ‖(l : Qbar l) ^ k * x‖ ≤ ‖((l : ℕ) : Qbar l) ^ k‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hx
  obtain ⟨w, hw, e⟩ := Rec.exists_eq_pow_mul_of_norm_le hk hn
  have : x = w := mul_left_cancel₀ (pow_ne_zero k hl0) e
  rw [this]; exact hw

theorem adj_mem (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : ∀ i j, M i j ∈ c.O) (i j : Fin 2) :
    M.adjugate i j ∈ c.O := by
  rw [Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [c.O.neg_mem, hM]

theorem norm_mulVec_le (c : Coef l) {A : Matrix (Fin 2) (Fin 2) (Qbar l)} (hA : ∀ i j, A i j ∈ c.O)
    {v : Fin 2 → Qbar l} (hv : ∀ j, ‖v j‖ ≤ 1) (i : Fin 2) : ‖(A *ᵥ v) i‖ ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;>
  · rw [norm_mul]; exact mul_le_one₀ (Rec.norm_le_one_of_mem (hA _ _)) (norm_nonneg _) (hv _)

end GlobalTheory.Ord2.Kill

namespace GlobalTheory.Ord2


open Kill in
theorem exists_pow_smul_cob1_of_cv_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l),
    (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) → ∃ r : ℕ, ∀ (n : ℕ) (a : G ℚ Ω → Fin 2 → Qbar l)
      (y : Fin 2 → Qbar l), (∀ s i, a s i ∈ c.O) → VecE c y → (∀ s, Cv n (a s) (mat W s *ᵥ y - y)) →
      Cob1 c n W ⊤ (fun s => ((l : ℕ) : Qbar l) ^ r • a s) := by
  intro l _ Ω _ _ W c hW ⟨g, hg⟩
  set M := mat W g - 1 with hMdef
  have hMO : ∀ i j, M i j ∈ c.O := fun i j => by
    simp only [M, Matrix.sub_apply, Matrix.one_apply]
    split_ifs
    · exact c.O.sub_mem (hW g i j) c.O.one_mem
    · simpa using hW g i j
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hlpos : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hd : 0 < ‖M.det‖ := norm_pos_iff.2 hg
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hd hlinv
  refine ⟨r, fun n a y ha hy h => ?_⟩
  have hlr : ‖((l : ℕ) : Qbar l) ^ r‖ = (l : ℝ)⁻¹ ^ r := by rw [norm_pow, Rec.norm_natCast_l]
  have hlr1 : ‖((l : ℕ) : Qbar l) ^ r‖ ≤ 1 := by rw [hlr]; exact pow_le_one₀ hlpos.le hlinv.le
  have hln1 : ‖((l : ℕ) : Qbar l) ^ n‖ ≤ 1 := by
    rw [norm_pow, Rec.norm_natCast_l]; exact pow_le_one₀ hlpos.le hlinv.le

  have hMy : ∀ j, ‖(M *ᵥ y) j‖ ≤ 1 := by
    intro j
    have e : (M *ᵥ y) j = a g j - (a g j - (mat W g *ᵥ y - y) j) := by
      simp [M, Matrix.sub_mulVec]
    rw [e]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (Rec.norm_le_one_of_mem (ha g j)) ?_)
    rw [norm_neg]
    exact (h g j).trans hln1

  have hdy : ∀ i, ‖M.det * y i‖ ≤ 1 := by
    intro i
    have e : M.det * y i = (M.adjugate *ᵥ (M *ᵥ y)) i := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp
    rw [e]
    exact norm_mulVec_le c (adj_mem c hMO) hMy i
  have hx : ∀ i, ((l : ℕ) : Qbar l) ^ r * y i ∈ c.O := by
    intro i
    apply mem_of_memE c
    · obtain ⟨k, hk⟩ := hy
      refine ⟨k, ?_⟩
      have e : (l : Qbar l) ^ k * (((l : ℕ) : Qbar l) ^ r * y i) = ((l : ℕ) : Qbar l) ^ r * ((l : Qbar l) ^ k * y i) := by
        ring
      rw [e]
      exact c.O.mul_mem (natPow_mem c r) (hk i)
    · have h1 := hdy i
      rw [norm_mul] at h1 ⊢
      calc ‖((l : ℕ) : Qbar l) ^ r‖ * ‖y i‖ ≤ ‖M.det‖ * ‖y i‖ := by
            gcongr; rw [hlr]; exact hr.le
        _ ≤ 1 := h1
  refine ⟨fun i => ((l : ℕ) : Qbar l) ^ r * y i, hx, fun s _ i => ?_⟩
  have e : (((l : ℕ) : Qbar l) ^ r • a s) i - (mat W s *ᵥ (fun i => ((l : ℕ) : Qbar l) ^ r * y i) -
      fun i => ((l : ℕ) : Qbar l) ^ r * y i) i = ((l : ℕ) : Qbar l) ^ r * (a s i - (mat W s *ᵥ y - y) i) := by
    have : (fun i => ((l : ℕ) : Qbar l) ^ r * y i) = ((l : ℕ) : Qbar l) ^ r • y := by
      funext i; simp
    rw [this, Matrix.mulVec_smul]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  unfold Cg
  rw [e, norm_mul]
  calc ‖((l : ℕ) : Qbar l) ^ r‖ * ‖a s i - (mat W s *ᵥ y - y) i‖ ≤ 1 * ‖((l : ℕ) : Qbar l) ^ n‖ :=
        mul_le_mul hlr1 (h s i) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end GlobalTheory.Ord2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousGaloisRepRankTwoTateDualOfOrdinaryNorm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.DualCont

theorem cyc_cont' {Ω : Type} [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] : Continuous (cycBar ℚ Ω l) :=
  (Continuous.units_map _ (show Continuous (fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) from
    (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ ℚ Ω l)

theorem units_cont {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

theorem continuous_galoisRepRankTwoTateDual : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → Continuous (dual1 W) := by
  intro l _ Ω _ _ _ e S A W hN
  have hW : Continuous fun s => ((W s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp hN.cont
  have hd : Continuous (dt W) := by
    apply units_cont
    show Continuous fun s => (Matrix.GeneralLinearGroup.det (W s) : Qbar l)
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    exact hW.matrix_det
  have hc := cyc_cont' (Ω := Ω) l
  have hχ : Continuous (cycBar ℚ Ω l * (dt W)⁻¹) := by
    show Continuous fun s => cycBar ℚ Ω l s * ((dt W) s)⁻¹
    exact hc.mul hd.inv
  apply units_cont
  show Continuous fun s => ((tw W (cycBar ℚ Ω l * (dt W)⁻¹) s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))
  simp only [tw_val]
  exact (Units.continuous_val.comp hχ).smul hW

end GlobalTheory.Ord2.DualCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineClassRestrictDecompositionGroupStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineClass_restrict_decompositionGroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (A : ValuationSubring Ω), OverL l A → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → ∃ ι : GQ l →* G ℚ Ω, Continuous ι ∧ (∀ σ, ι σ ∈ Dec (F := ℚ) A) ∧ (∀ s ∈ Dec (F := ℚ) A, ∃ σ, ι σ = s) ∧ (∀ σ ∈ Loc.Iq l, ι σ ∈ Ine (F := ℚ) A) ∧ (∀ σ, cycZ ℚ Ω l (ι σ) = Loc.cyc l l σ) ∧ (fun σ => z (ι σ)) ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp ι) := by
  first | exact @GlobalTheory.Ord2.bk_locEmb | exact GlobalTheory.Ord2.bk_locEmb | (intros; apply GlobalTheory.Ord2.bk_locEmb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryMod
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.CupCob

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_int (x : Qbar l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt
  | exact _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt
  | (apply _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> assumption)
  | (intros; apply _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PadicIntegralNorm.norm_le_one_of_isIntegral_padicInt ..)

theorem nsub_le_max (x y : Qbar l) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]; exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  norm_le_one_of_int x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

theorem eps_mem (c : Coef l) (s : G ℚ Ω) : eps l s ∈ c.O := by
  have : eps l s = algebraMap ℤ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]; rfl
  rw [this]; exact c.O.algebraMap_mem _

theorem eps_cont : Continuous fun s : G ℚ Ω => eps l s :=
  (continuous_algebraMap ℚ_[l] (Qbar l)).comp
    (continuous_subtype_val.comp ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l)))

theorem det_sq (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) : (mat W s).det ^ 2 = 1 := by
  have := congrArg (fun f => ((f s : (Qbar l)ˣ) : Qbar l)) h
  simpa [dt] using this

theorem mat_dual1 (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) :
    mat (dual1 W) s = (eps l s * (mat W s).det) • mat W s := by
  have hinv : (dt W s)⁻¹ = dt W s := by
    have h2 := congrArg (fun f => f s) h
    simp only [pow_two, MonoidHom.mul_apply, MonoidHom.one_apply] at h2
    exact inv_eq_of_mul_eq_one_left h2
  simp only [mat, dual1, tw_val, MonoidHom.mul_apply, MonoidHom.inv_apply, hinv, Units.val_mul]
  simp [dt, eps]

theorem om_smul_right (k : Qbar l) (p q : Fin 2 → Qbar l) : om p (k • q) = k * om p q := by
  simp only [om, Pi.smul_apply, smul_eq_mul]; ring

theorem om_mulVec (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (p q : Fin 2 → Qbar l) :
    om (M *ᵥ p) (M *ᵥ q) = M.det * om p q := by
  simp only [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]; ring

theorem om_key (W : R2 Ω l) (h : dt W ^ 2 = 1) (s : G ℚ Ω) (p q : Fin 2 → Qbar l) :
    om (mat W s *ᵥ p) (mat (dual1 W) s *ᵥ q) = eps l s * om p q := by
  rw [mat_dual1 W h, Matrix.smul_mulVec, om_smul_right, om_mulVec]
  linear_combination (eps l s * om p q) * det_sq W h s

theorem mat_dual1_mul (W : R2 Ω l) (s t : G ℚ Ω) (x : Fin 2 → Qbar l) :
    mat (dual1 W) (s * t) *ᵥ x = mat (dual1 W) s *ᵥ (mat (dual1 W) t *ᵥ x) := by
  simp only [mat, map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem mulVec_mem (c : Coef l) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (x : Fin 2 → Qbar l)
    (hM : ∀ i j, M i j ∈ c.O) (hx : ∀ i, x i ∈ c.O) (i : Fin 2) : (M *ᵥ x) i ∈ c.O := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact add_mem (mul_mem (hM _ _) (hx _)) (mul_mem (hM _ _) (hx _))

theorem om_mem (c : Coef l) (p q : Fin 2 → Qbar l) (hp : ∀ i, p i ∈ c.O) (hq : ∀ i, q i ∈ c.O) : om p q ∈ c.O :=
  sub_mem (mul_mem (hp _) (hq _)) (mul_mem (hp _) (hq _))

theorem dual_representation_integral (c : Coef l) (W : R2 Ω l) (h : dt W ^ 2 = 1) (hint : ∀ s i j, mat W s i j ∈ c.O) (s : G ℚ Ω)
    (i j : Fin 2) : mat (dual1 W) s i j ∈ c.O := by
  rw [mat_dual1 W h, Matrix.smul_apply, smul_eq_mul]
  refine mul_mem (mul_mem (eps_mem c s) ?_) (hint s i j)
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hint _ _ _) (hint _ _ _)) (mul_mem (hint _ _ _) (hint _ _ _))

theorem mulVec_le {L : ℝ} (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (q : Fin 2 → Qbar l)
    (hM : ∀ i j, ‖M i j‖ ≤ 1) (hq : ∀ i, ‖q i‖ ≤ L) (i : Fin 2) : ‖(M *ᵥ q) i‖ ≤ L := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact (mul_le_mul (hM _ _) (hq _) (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul L))

theorem om_le_left {L : ℝ} (p q : Fin 2 → Qbar l) (hp : ∀ i, ‖p i‖ ≤ L) (hq : ∀ i, ‖q i‖ ≤ 1) :
    ‖om p q‖ ≤ L := by
  have hL : 0 ≤ L := (norm_nonneg _).trans (hp 0)
  refine (nsub_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact (mul_le_mul (hp _) (hq _) (norm_nonneg _) hL).trans (le_of_eq (mul_one L))

theorem om_le_right {L : ℝ} (p q : Fin 2 → Qbar l) (hp : ∀ i, ‖p i‖ ≤ 1) (hq : ∀ i, ‖q i‖ ≤ L) :
    ‖om p q‖ ≤ L := by
  refine (nsub_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact (mul_le_mul (hp _) (hq _) (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul L))

theorem ident_a (A v w x B2 B1 B0 : Fin 2 → Qbar l) (e : Qbar l) (key : om w v = e * om x B0) :
    om A v - (e * om x B0 - om x B2 + om x B1) = om (A - (w - x)) v + om x (B2 - (B1 + v)) := by
  simp only [om, Pi.sub_apply, Pi.add_apply] at *
  linear_combination key

theorem ident_b (As At Ast Bt x : Fin 2 → Qbar l) (M P : Matrix (Fin 2) (Fin 2) (Qbar l)) (N : Matrix (Fin 2) (Fin 2) (Qbar l))
    (e : Qbar l) (key : om (P *ᵥ At) (M *ᵥ (N *ᵥ x)) = e * om At (N *ᵥ x)) :
    om As (M *ᵥ Bt) - (e * -om At (N *ᵥ x) - -om Ast (M *ᵥ (N *ᵥ x)) + -om As (M *ᵥ x)) =
      om As (M *ᵥ (Bt - (N *ᵥ x - x))) - om (Ast - (As + P *ᵥ At)) (M *ᵥ (N *ᵥ x)) := by
  simp only [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.sub_apply, Pi.add_apply] at *
  linear_combination -key

end GlobalTheory.Ord2.CupCob

namespace GlobalTheory.Ord2.CupCob

theorem cup_cob : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l)
    (H : Subgroup (G ℚ Ω)) (a b : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 →
    Coc1 c n W H a → Coc1 c n (dual1 W) H b → (Cob1 c n W H a ∨ Cob1 c n (dual1 W) H b) → Cob2 c n H (cup W a b) := by
  intro l _ Ω _ _ _ c n W H a b hW hint hdet ha hb hcob
  have hWn : ∀ s i j, ‖mat W s i j‖ ≤ 1 := fun s i j => norm_le_one_of_mem c (hint s i j)
  have hDm : ∀ s i j, mat (dual1 W) s i j ∈ c.O := dual_representation_integral c W hdet hint
  have hDn : ∀ s i j, ‖mat (dual1 W) s i j‖ ≤ 1 := fun s i j => norm_le_one_of_mem c (hDm s i j)
  have han : ∀ s i, ‖a s i‖ ≤ 1 := fun s i => norm_le_one_of_mem c (ha.2.1 s i)
  have hbn : ∀ s i, ‖b s i‖ ≤ 1 := fun s i => norm_le_one_of_mem c (hb.2.1 s i)
  rcases hcob with ⟨x, hx, hax⟩ | ⟨x, hx, hbx⟩
  · have hxn : ∀ i, ‖x i‖ ≤ 1 := fun i => norm_le_one_of_mem c (hx i)
    refine ⟨fun t => om x (b t), ?_, fun t => om_mem c _ _ hx (hb.2.1 t), ?_⟩
    · show ContinuousOn (fun t => x 0 * b t 1 - x 1 * b t 0) H
      exact (continuousOn_const.mul (continuousOn_pi.1 hb.1 1)).sub (continuousOn_const.mul (continuousOn_pi.1 hb.1 0))
    · intro s hs t ht
      show ‖_ - _‖ ≤ _
      have key := om_key W hdet s x (b t)
      rw [cup, ident_a (a s) (mat (dual1 W) s *ᵥ b t) (mat W s *ᵥ x) x (b (s * t)) (b s) (b t) (eps l s) key]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · exact om_le_left _ _ (fun i => hax s hs i) (mulVec_le _ _ (hDn s) (hbn t))
      · exact om_le_right _ _ hxn (fun i => hb.2.2 s hs t ht i)
  · have hxn : ∀ i, ‖x i‖ ≤ 1 := fun i => norm_le_one_of_mem c (hx i)
    have hM : Continuous fun s => mat W s := Units.continuous_val.comp hW
    have hD : Continuous fun s => mat (dual1 W) s := by
      have : (fun s => mat (dual1 W) s) = fun s => (eps l s * (mat W s).det) • mat W s := funext (mat_dual1 W hdet)
      rw [this]
      exact (eps_cont.mul hM.matrix_det).smul hM
    have hv : Continuous fun s => mat (dual1 W) s *ᵥ x := hD.matrix_mulVec continuous_const
    refine ⟨fun s => -om (a s) (mat (dual1 W) s *ᵥ x), ?_,
      fun s => neg_mem (om_mem c _ _ (ha.2.1 s) (mulVec_mem c _ _ (hDm s) hx)), ?_⟩
    · show ContinuousOn (fun s => -(a s 0 * (mat (dual1 W) s *ᵥ x) 1 - a s 1 * (mat (dual1 W) s *ᵥ x) 0)) H
      exact (((continuousOn_pi.1 ha.1 0).mul ((continuous_apply 1).comp hv).continuousOn).sub
        ((continuousOn_pi.1 ha.1 1).mul ((continuous_apply 0).comp hv).continuousOn)).neg
    · intro s hs t ht
      show ‖_ - _‖ ≤ _
      have key := om_key W hdet s (a t) (mat (dual1 W) t *ᵥ x)
      beta_reduce
      rw [cup, mat_dual1_mul W s t x,
        ident_b (a s) (a t) (a (s * t)) (b t) x (mat (dual1 W) s) (mat W s) (mat (dual1 W) t) (eps l s) key]
      refine (nsub_le_max _ _).trans (max_le ?_ ?_)
      · exact om_le_right _ _ (han s) (mulVec_le _ _ (hDn s) (fun i => hbx t ht i))
      · exact om_le_left _ _ (fun i => ha.2.2 s hs t ht i)
          (mulVec_le _ _ (hDn s) (mulVec_le _ _ (hDn t) hxn))

end GlobalTheory.Ord2.CupCob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicCharCongruentOneOnDecompositionGroup
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.EpsDec

theorem natCast_eq_of_pow_eq {M : Type} [CommMonoid M] {ζ : M} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : N ≠ 0)
    {a b : ℕ} (h : ζ ^ a = ζ ^ b) : (a : ZMod N) = b := by
  rw [ZMod.natCast_eq_natCast_iff' a b N]
  rw [pow_eq_pow_mod a hζ.pow_eq_one, pow_eq_pow_mod b hζ.pow_eq_one] at h
  exact hζ.pow_inj (Nat.mod_lt _ (Nat.pos_of_ne_zero hN)) (Nat.mod_lt _ (Nat.pos_of_ne_zero hN)) h

theorem eps_dec_cong : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl)
    (B : ValuationSubring Ω), IsPlaceOver B w → l ^ n ∣ normV w - 1 → 1 ≤ n →
    ∀ σ ∈ Dec (F := ℚ) B, Cg n (eps l σ) 1 := by
  intro l _ Ω _ _ _ n w B hB hdiv hn σ hσ
  have hl : l.Prime := Fact.out
  have hl2 := hl.two_le
  set p := normV w with hpdef
  have hp : p.Prime := GlobalTheory.Ord2.PrimeChar.normV_prime w
  haveI : Fact p.Prime := ⟨hp⟩
  have hA : B.valuation (p : Ω) < 1 := GlobalTheory.Ord2.PrimeChar.val_normV_lt_one hB
  have hpl : p ≠ l := by
    intro e
    have h1 : l ∣ p - 1 := (dvd_pow_self l (by omega)).trans hdiv
    rw [e] at h1
    have h2 := Nat.le_of_dvd (by omega) h1
    omega
  have hcop : (l ^ n).Coprime p :=
    Nat.Coprime.pow_left n ((Nat.coprime_primes hl hp).2 hpl.symm)
  obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω p B hA (l ^ n) hcop σ hσ
  have hp1 : (p : ZMod (l ^ n)) = 1 := by
    have h1 : 1 ≤ p := hp.one_lt.le
    have : ((p - 1 : ℕ) : ZMod (l ^ n)) = 0 := (CharP.cast_eq_zero_iff (ZMod (l ^ n)) (l ^ n) _).2 hdiv
    rw [Nat.cast_sub h1, Nat.cast_one, sub_eq_zero] at this
    exact this
  have hIAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ hl.ne_zero
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hspec := cyclotomicCharacter.spec (L := Ω) l
    (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) ζ hζ.pow_eq_one
  set c : ℤ_[l] := ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) with hc
  have hσζ : σ ζ = ζ ^ (PadicInt.toZModPow n c).val := hspec
  have hζp : ζ ^ (p ^ k) = ζ ^ 1 := by
    rw [pow_eq_pow_mod (p ^ k) hζ.pow_eq_one, pow_eq_pow_mod 1 hζ.pow_eq_one]
    congr 1
    rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_pow, hp1, one_pow, Nat.cast_one]
  have hm : PadicInt.toZModPow n c = 1 := by
    have h1 : ζ ^ (PadicInt.toZModPow n c).val = ζ ^ 1 := by rw [← hσζ, hk ζ hζ.pow_eq_one, hζp]
    have h2 := natCast_eq_of_pow_eq hζ hN0 h1
    rwa [ZMod.natCast_zmod_val, Nat.cast_one] at h2
  have hker : c - 1 ∈ Ideal.span {((l : ℤ_[l])) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hm, map_one, sub_self]
  have hnorm := (PadicInt.norm_le_pow_iff_mem_span_pow (c - 1) n).2 hker
  have e1 : eps l σ - 1 = algebraMap ℚ_[l] (Qbar l) ((c : ℚ_[l]) - 1) := by
    rw [map_sub, map_one]; rfl
  unfold Cg
  rw [e1, norm_algebraMap', norm_pow]
  have e2 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [e2, norm_algebraMap', Padic.norm_p]
  have e3 : ‖(c : ℚ_[l]) - 1‖ = ‖c - 1‖ := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one]
  rw [e3]
  refine hnorm.trans (le_of_eq ?_)
  rw [zpow_neg, zpow_natCast, inv_pow]

end GlobalTheory.Ord2.EpsDec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfForallNormLe
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_mem_coef (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.Rf3.norm_le_one_of_mem_coef c hx

theorem norm_natCast_l : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
  have : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [this, norm_algebraMap', Padic.norm_p]

theorem norm_natCast_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  rw [norm_natCast_l]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem tendsto_norm_l_pow :
    Filter.Tendsto (fun n : ℕ => ‖((l : ℕ) : Qbar l) ^ n‖) Filter.atTop (nhds 0) := by
  simp only [norm_pow]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) norm_natCast_l_lt_one

theorem eq_zero_of_forall_norm_le (x : Qbar l) (h : ∀ n : ℕ, ‖x‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) : x = 0 := by
  have h0 : ‖x‖ ≤ 0 := ge_of_tendsto' tendsto_norm_l_pow h
  exact norm_le_zero_iff.1 h0

theorem cg_symm {n : ℕ} {a b : Qbar l} (h : Cg n a b) : Cg n b a := by
  unfold Cg at *; rwa [norm_sub_rev]

theorem cg_trans {n : ℕ} {a b d : Qbar l} (h : Cg n a b) (h' : Cg n b d) : Cg n a d := by
  unfold Cg at *
  have e : a - d = (a - b) + (b - d) := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

theorem cv_symm {n : ℕ} {a b : Fin 2 → Qbar l} (h : Cv n a b) : Cv n b a := fun i => cg_symm (h i)

theorem cv_trans {n : ℕ} {a b d : Fin 2 → Qbar l} (h : Cv n a b) (h' : Cv n b d) : Cv n a d :=
  fun i => cg_trans (h i) (h' i)

theorem eq_of_forall_cg {a b : Qbar l} (h : ∀ n, Cg n a b) : a = b :=
  sub_eq_zero.1 (eq_zero_of_forall_norm_le _ h)

end GlobalTheory.Ord2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAuxiliaryPrimeFrobeniusNearCommutatorStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_auxiliary_prime_frobenius_near_commutator : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (S S' : Finset Pl) (U : Subgroup (G ℚ Ω)) (σ : G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → σ ∈ ⁅(cycBar ℚ Ω l).ker, (cycBar ℚ Ω l).ker⁆ → ∃ (w : Pl) (B : ValuationSubring Ω) (τ : G ℚ Ω), w ∉ S ∧ w ∉ S' ∧ IsPlaceOver B w ∧ IsFrob B (normV w) τ ∧ τ ∈ Dec (F := ℚ) B ∧ σ⁻¹ * τ ∈ U ∧ l ^ n ∣ normV w - 1 ∧ ∀ v ∈ S, ∃ x : ZMod (normV w), x ^ (l ^ n) = (normV v : ZMod (normV w)) := by
  first | exact @GlobalTheory.Ord2.AuxiliaryInertOddPrime.exists_odd_prime_gt_two_bounds | exact GlobalTheory.Ord2.AuxiliaryInertOddPrime.exists_odd_prime_gt_two_bounds | (intros; apply GlobalTheory.Ord2.AuxiliaryInertOddPrime.exists_odd_prime_gt_two_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterPrimeConductorDegreePrimePowStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_character_primeConductor_degree_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl), 1 ≤ n → l ^ n ∣ normV w - 1 → ∃ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)), KillsMu (normV w) ψ ∧ Function.Surjective ψ ∧ (∀ B : ValuationSubring Ω, IsPlaceOver B w → ∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) ∧ ∀ v : Pl, v ≠ w → (∃ x : ZMod (normV w), x ^ (l ^ n) = (normV v : ZMod (normV w))) → ∀ B : ValuationSubring Ω, IsPlaceOver B v → Dec (F := ℚ) B ≤ ψ.ker := by
  first | exact @GlobalTheory.Ord2.PrimeChar.exists_prime_char | exact GlobalTheory.Ord2.PrimeChar.exists_prime_char | (intros; apply GlobalTheory.Ord2.PrimeChar.exists_prime_char <;> assumption)
end

