module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import ReciprocityTheory.GaloisValuations.Global
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import ReciprocityTheory.NeutralLocalFields.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0151
public import Formalism.CharacterColumnKernels.StatementRho
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0101
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HilbertClassFieldA
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedGaloisHomsBoundedClassNumberOfArtinRec
section
open Formalism.NG Formalism.RepresentationBoundsCohomology.BR NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.UnramifiedClassBound
open Neutral.HilbertClassField

theorem vhE_of_globalArtinReciprocity (hA : GlobalTheory.Published.GlobalArtinReciprocity) : ReciprocityTheory.ChartRestriction.T2.VhE := by
  intro E Ω _ _ _ _ _ Av hAv l _ O _ _ _ _ _ hl M _ _ hM ρ hρ S hS hU
  obtain ⟨eM⟩ := hM
  obtain ⟨art, hsurj, hker, -⟩ := _root_.GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField hA E Ω

  let ψ : (Additive (ClassGroup (𝓞 E)) →+ M) →ₗ[O] coZ1s ρ :=
    { toFun := fun f => ⟨fun g => f (Additive.ofMul (art g)), fun g h => by
        show f (Additive.ofMul (art (g * h))) = f (Additive.ofMul (art g)) + ρ g (f (Additive.ofMul (art h)))
        rw [hρ, map_mul, ofMul_mul, map_add (f := _)]⟩
      map_add' := fun f f' => rfl
      map_smul' := fun r f => rfl }
  let Φ := (Submodule.mkQ ((coB1 ρ).comap (coZ1s ρ).subtype)) ∘ₗ ψ
  have hle : S ≤ LinearMap.range Φ := by
    intro x hx
    obtain ⟨z, rfl, hlc⟩ := hS x hx
    have hz : ∀ g h : G E Ω, (z : G E Ω → M) (g * h) = (z : G E Ω → M) g + (z : G E Ω → M) h := by
      intro g h
      have := z.2 g h
      rw [hρ] at this
      exact this
    have hI : ∀ v, ∀ σ ∈ Ine (F := E) (Av v), (z : G E Ω → M) σ = 0 := by
      intro v σ hσ
      have h1 := hU v hx
      rw [unrH1, LinearMap.mem_ker, Formalism.NG.resH1, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero] at h1
      obtain ⟨w, hw⟩ := h1
      have := congrFun hw ⟨σ, hσ⟩
      simp only [coD0, resRep, LinearMap.coe_mk, AddHom.coe_mk] at this
      exact (show (z : G E Ω → M) σ = _ from this.symm).trans (by simp [hρ])
    have hkill := GlobalTheory.T.hilbertSubgroup_le_ker_of_kills_inertia E Ω Av hAv M z hz hlc hI (fun c hc => _root_.GlobalTheory.addHom_complexConjugation_eq_zero E Ω l O hl M z hz c hc)
    let zH : G E Ω →* Multiplicative M :=
      { toFun := fun g => Multiplicative.ofAdd ((z : G E Ω → M) g)
        map_one' := by
          have := hz 1 1
          simp only [mul_one] at this
          have h0 : (z : G E Ω → M) 1 = 0 := by
            have := congrArg (fun t => t - (z : G E Ω → M) 1) this
            simpa using this.symm
          simp [h0]
        map_mul' := fun g h => by simp [hz g h] }
    have hk : art.ker ≤ zH.ker := by
      intro σ hσ
      rw [hker] at hσ
      simp [zH, MonoidHom.mem_ker, hkill σ hσ]
    let Lf := (MonoidHom.liftOfSurjective art hsurj) ⟨zH, hk⟩
    let f : Additive (ClassGroup (𝓞 E)) →+ M :=
      { toFun := fun a => Multiplicative.toAdd (Lf (Additive.toMul a))
        map_zero' := by simp
        map_add' := fun a b => by simp }
    refine ⟨f, ?_⟩
    change Submodule.mkQ _ (ψ f) = Submodule.mkQ _ z
    congr 1
    apply Subtype.ext
    funext g
    show Multiplicative.toAdd (Lf (art g)) = (z : G E Ω → M) g
    rw [MonoidHom.liftOfRightInverse_comp_apply]
    rfl
  calc Module.length O S ≤ Module.length O (LinearMap.range Φ) :=
        Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    _ ≤ Module.length O (Additive (ClassGroup (𝓞 E)) →+ M) :=
        Module.length_le_of_surjective Φ.rangeRestrict Φ.surjective_rangeRestrict
    _ ≤ _ := by
        have := _root_.GlobalTheory.HomLen.length_addMonoidHom_le l O M eM (Additive (ClassGroup (𝓞 E)))
        rwa [show Nat.card (Additive (ClassGroup (𝓞 E))) = classNumber E from by
          rw [NumberField.classNumber, ← Nat.card_eq_fintype_card]; rfl] at this
end GlobalTheory.UnramifiedClassBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleConsequencesPoleQuotient
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachModulePoleQuotient

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem wachModule_consequences_poleQuotient : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), gammaSemisimpleQuotientGlobal D HW F := by
  intro D HW F Cm
  unfold gammaSemisimpleQuotientGlobal gammaSemisimpleLocal GammaSemisimpleQuotient
  intro l _ K s LL h T hT y hy
  classical
  have hfr := GlobalTheory.T.wachModule_inverseQuotient_free_finite_crystalline D HW F l K s LL h T hT y
  have hJ := GlobalTheory.T.crystallineLattice_hodgeTateJumps_finite D HW l K s LL h T hT
  let Fs : Finset (↥(OL LL))ˣ := (hJ.toFinset ×ˢ Finset.Icc 1 y).image
    (fun p : ℤ × ℕ => uU ((HW l).W K s LL h) ^ (-(p.1 + (p.2 : ℤ))))
  have hmem : ∀ c, c ∈ Fs ↔ ∃ a ∈ Jumps (PD := (D.loc l).PD K) T, ∃ j : ℕ, 1 ≤ j ∧ j ≤ y ∧
      c = uU ((HW l).W K s LL h) ^ (-(a + j)) := by
    intro c
    simp only [Fs, Finset.mem_image, Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_Icc,
      Prod.exists]
    constructor
    · rintro ⟨a, j, ⟨ha, h1, h2⟩, rfl⟩
      exact ⟨a, ha, j, h1, h2, rfl⟩
    · rintro ⟨a, ha, j, h1, h2, rfl⟩
      exact ⟨a, j, ⟨ha, h1, h2⟩, rfl⟩
  refine ⟨hfr.1, hfr.2, Fs, ?_, ?_, ?_⟩
  · ext c
    exact hmem c
  · intro x hx
    exact GlobalTheory.T.prod_gamma_sub_jump_units_annihilates_quotient D HW F Cm l K s LL h T hT y hy Fs
      (fun a ha j h1 h2 => (hmem _).2 ⟨a, ha, j, h1, h2, rfl⟩) x hx
  · intro c hc
    obtain ⟨a, ha, j, h1, h2, rfl⟩ := (hmem c).1 hc
    obtain ⟨x, hx, hxN, hγ⟩ := GlobalTheory.T.gamma_eigenvalue_on_wachLattice_qPower_quotient D HW F Cm l K s LL h T hT y hy a ha j h1 h2
    exact ⟨x, hx, hxN, hγ⟩

end GlobalTheory.NL.WachModulePoleQuotient
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCoefficientRationalMirabolicMul
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

namespace MirCol

section ColAct

variable {R : Type} [CommRing R] {a k : ℕ}

def colAct (M : Matrix (Fin a) (Fin a) R) (x : UnipotentBlockColumnIndex a k k → R) : UnipotentBlockColumnIndex a k k → R :=
  fun t => ∑ s, M t.1.1 s.1.1 * x s

theorem posM_col_apply (x : UnipotentBlockColumnIndex a k k → R) (t : UnipotentBlockColumnIndex a k k) :
    posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) x t.1.1 t.1.2 = x t := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single t]
  · simp
  · intro s _ hne
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hne (Subtype.ext (Prod.ext h1 h2))
  · simp

theorem posM_col_mul (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ i l : Fin a, k ≤ (i : ℕ) → M i l = (1 : Matrix (Fin a) (Fin a) R) i l) (x : UnipotentBlockColumnIndex a k k → R) :
    posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) x * M = posM Subtype.val x := by
  simp only [posM, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single t.1.2]
  · rw [hM _ _ t.2.2.1]
    simp only [Matrix.single_apply, Matrix.one_apply]
    by_cases h1 : t.1.1 = i <;> by_cases h2 : t.1.2 = j <;> simp [h1, h2]
  · intro l _ hl
    rw [Matrix.single_apply, if_neg (fun h => hl h.2.symm), zero_mul]
  · simp

theorem mul_posM_col (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ i l : Fin a, k ≤ (i : ℕ) → M i l = (1 : Matrix (Fin a) (Fin a) R) i l) (x : UnipotentBlockColumnIndex a k k → R) :
    M * posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) x = posM Subtype.val (colAct M x) := by
  ext i j
  have hL : (M * posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) x) i j =
      ∑ s : UnipotentBlockColumnIndex a k k, if s.1.2 = j then M i s.1.1 * x s else 0 := by
    simp only [Matrix.mul_apply, posM, Matrix.sum_apply, Matrix.single_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single s.1.1]
    · simp
    · intro l _ hl
      rw [if_neg (fun h => hl h.1.symm), mul_zero]
    · simp
  rw [hL]
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  by_cases hi : (i : ℕ) < k
  · by_cases hj : (j : ℕ) = k
    · symm
      rw [Finset.sum_eq_single (⟨(i, j), hi, hj.ge, hj.le⟩ : UnipotentBlockColumnIndex a k k)]
      · rw [if_pos (And.intro rfl rfl)]
        simp only [colAct]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [if_pos]
        have h1 := s.2.2
        exact Fin.ext (by omega)
      · intro t _ hne
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact hne (Subtype.ext (Prod.ext h1 h2))
      · simp
    · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
      · intro t _
        rw [if_neg]
        rintro ⟨_, h2⟩
        have h1 := t.2.2
        rw [← h2] at hj
        omega
      · intro t _
        rw [if_neg]
        intro h2
        have h1 := t.2.2
        rw [← h2] at hj
        omega
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro t _
      rw [if_neg]
      rintro ⟨h1, _⟩
      have h2 := t.2.1
      rw [h1] at h2
      exact hi h2
    · intro s _
      have h2 := s.2.1
      rw [hM i _ (by omega), Matrix.one_apply_ne (fun h => by rw [h] at hi; exact hi h2)]
      simp

theorem colAct_colAct {M N : Matrix (Fin a) (Fin a) R}
    (hM : ∀ i l : Fin a, k ≤ (i : ℕ) → M i l = (1 : Matrix (Fin a) (Fin a) R) i l)
    (hN : ∀ i l : Fin a, k ≤ (i : ℕ) → N i l = (1 : Matrix (Fin a) (Fin a) R) i l)
    (h : M * N = 1) (x : UnipotentBlockColumnIndex a k k → R) : colAct M (colAct N x) = x := by
  funext t
  rw [← posM_col_apply (colAct M (colAct N x)) t, ← mul_posM_col M hM, ← mul_posM_col N hN, ← Matrix.mul_assoc, h,
    Matrix.one_mul, posM_col_apply]

theorem inv_rows (γ : GL (Fin a) R)
    (hγ : ∀ i l : Fin a, k ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) R) i l) :
    ∀ i l : Fin a, k ≤ (i : ℕ) → (γ⁻¹).val i l = (1 : Matrix (Fin a) (Fin a) R) i l := by
  intro i l hi
  have h : γ.val * (γ⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 := congrFun (congrFun h i) l
  rw [Matrix.mul_apply] at h2
  simp only [hγ i _ hi, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
  simpa [Matrix.one_apply] using h2

theorem blkU_mul (γ : GL (Fin a) R)
    (hγ : ∀ i l : Fin a, k ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) R) i l) (x : UnipotentBlockColumnIndex a k k → R) :
    blkU x * γ = γ * blkU (colAct (γ⁻¹).val x) := by
  apply Units.ext
  change (1 + posM Subtype.val x) * γ.val = γ.val * (1 + posM Subtype.val (colAct (γ⁻¹).val x))
  have h : γ.val * (γ⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← mul_posM_col _ (inv_rows γ hγ), add_mul, mul_add, posM_col_mul _ hγ, ← Matrix.mul_assoc, h]
  simp

end ColAct

section Rat

variable {E : Type} [Field E] [NumberField E] {a k : ℕ}

theorem ratGL_val_apply (γ : GL (Fin a) E) (i l : Fin a) :
    (ratGL E a γ).val i l = algebraMap E (Ad E) (γ.val i l) := rfl

theorem ratGL_rows (γ : GL (Fin a) E)
    (hγ : ∀ i l : Fin a, k ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) E) i l) :
    ∀ i l : Fin a, k ≤ (i : ℕ) → (ratGL E a γ).val i l = (1 : Matrix (Fin a) (Fin a) (Ad E)) i l := by
  intro i l hi
  rw [ratGL_val_apply, hγ i l hi, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem colAct_rat (γ : GL (Fin a) E) (c : UnipotentBlockColumnIndex a k k → E) :
    colAct (ratGL E a γ).val (fun t => algebraMap E (Ad E) (c t)) =
      fun t => algebraMap E (Ad E) (colAct γ.val c t) := by
  funext t
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [colAct, ratGL_val_apply, map_sum, map_mul]

theorem continuous_colAct (M : Matrix (Fin a) (Fin a) (Ad E)) :
    Continuous (colAct M : (UnipotentBlockColumnIndex a k k → Ad E) → UnipotentBlockColumnIndex a k k → Ad E) :=
  continuous_pi fun _ => continuous_finsetSum _ fun s _ => continuous_const.mul (continuous_apply s)

def colEquiv (γ : GL (Fin a) E)
    (hγ : ∀ i l : Fin a, k ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) E) i l) :
    (UnipotentBlockColumnIndex a k k → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex a k k → Ad E) where
  toFun := colAct (ratGL E a γ).val
  invFun := colAct (ratGL E a γ⁻¹).val
  left_inv x := colAct_colAct (ratGL_rows _ (inv_rows γ hγ)) (ratGL_rows _ hγ)
    (by rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]) x
  right_inv x := colAct_colAct (ratGL_rows _ hγ) (ratGL_rows _ (inv_rows γ hγ))
    (by rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]) x
  map_add' x y := by
    funext t
    simp only [colAct, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  continuous_toFun := continuous_colAct _
  continuous_invFun := continuous_colAct _

theorem colEquiv_mem (γ : GL (Fin a) E)
    (hγ : ∀ i l : Fin a, k ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) E) i l)
    (x : UnipotentBlockColumnIndex a k k → Ad E) : colAct (ratGL E a γ).val x ∈ ratV E (UnipotentBlockColumnIndex a k k) ↔ x ∈ ratV E (UnipotentBlockColumnIndex a k k) := by
  have key : ∀ (δ : GL (Fin a) E) (y : UnipotentBlockColumnIndex a k k → Ad E), y ∈ ratV E (UnipotentBlockColumnIndex a k k) →
      colAct (ratGL E a δ).val y ∈ ratV E (UnipotentBlockColumnIndex a k k) := by
    rintro δ _ ⟨c, rfl⟩
    exact ⟨colAct δ.val c, (colAct_rat δ c).symm⟩
  refine ⟨fun h => ?_, key γ x⟩
  have h2 := key γ⁻¹ _ h
  rwa [colAct_colAct (ratGL_rows _ (inv_rows γ hγ)) (ratGL_rows _ hγ)
    (by rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])] at h2

theorem dot_colAct (γ : GL (Fin a) E) (ξ : UnipotentBlockColumnIndex a k k → E) (y : UnipotentBlockColumnIndex a k k → Ad E) :
    dot ξ (colAct (ratGL E a γ).val y) = dot (fun t => ∑ s : UnipotentBlockColumnIndex a k k, ξ s * γ.val s.1.1 t.1.1) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dot, colAct, ratGL_val_apply, Finset.mul_sum, map_sum, Finset.sum_mul, map_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

end Rat

end MirCol

open MirCol

theorem coefF_ratGL_mul : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ)
    (f : GA E a → ℂ), Continuous f → (∀ γ : GL (Fin a) E, IsMir (m + 1) γ → ∀ g, f (ratGL E a γ * g) = f g) →
    ∀ γ : GL (Fin a) E, IsMir (m + 1) γ → ∀ (ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) (g : GA E a),
    coefF ψ (m + 1) ξ f (ratGL E a γ * g) =
      coefF ψ (m + 1) (fun t => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), ξ s * γ.val s.1.1 t.1.1) f g := by
  intro E _ _ a ψ hψ m f hf hl γ hγ ξ g
  have hr : ∀ i l : Fin a, m + 1 ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) E) i l :=
    fun i l h => hγ i l (Or.inl h)
  have hri := inv_rows γ hr
  have hper := per_coef hψ (fun t => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), ξ s * γ.val s.1.1 t.1.1) hf
    (fun c g => hl _ (isMir_blkU c) g) g
  have hmem : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E,
      colEquiv γ⁻¹ hri x ∈ ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)) ↔ x ∈ ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)) :=
    fun x => colEquiv_mem γ⁻¹ hri x
  have key := _root_.GlobalTheory.CuspGeneric.avg_equiv _ _ (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)))
    (isCoLat_ratV E _) (isCoLat_ratV E _) (colEquiv γ⁻¹ hri) hmem _ hper
  change avg _ _ = avg _ _
  rw [← key]
  congr 1
  funext x
  have hx : colAct (ratGL E a γ).val (colEquiv γ⁻¹ hri x) = x :=
    colAct_colAct (ratGL_rows _ hr) (ratGL_rows _ hri)
      (by rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]) x
  have hd : dot (fun t => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), ξ s * γ.val s.1.1 t.1.1) (colEquiv γ⁻¹ hri x) = dot ξ x := by
    rw [← dot_colAct, hx]
  have hu : blkU x * (ratGL E a γ * g) = ratGL E a γ * (blkU (colEquiv γ⁻¹ hri x) * g) := by
    rw [← mul_assoc, blkU_mul (ratGL E a γ) (ratGL_rows _ hr), mul_assoc, ← map_inv]
    rfl
  beta_reduce
  rw [hd, hu, hl γ hγ]

end GlobalTheory.CuspGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XNygaardExtComesFromBaseField
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

noncomputable section

namespace GlobalTheory.NL.XNTransfer

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n}

theorem exists_aN_iff (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (a : LetA O n)
    (r : RA) (hr : E.io a = r) (w : TW RW T) :
    (∃ z ∈ aN W T a, E.jD T z = w) ↔ ∃ y ∈ E.jD T '' (W.N T : Set (W.DD T)), w = inclR r • y := by
  have hs : ∀ x : W.DD T, E.jD T (a • x) = inclR r • E.jD T x := fun x => by
    rw [← algebraMap_smul W.EE a x, E.jD_smul, E.ioE_ext, hr]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, hs x⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a • x, ⟨x, hx, rfl⟩, hs x⟩

end Generic

theorem image_map_refl {O R M : Type} [CommRing O] [AddCommGroup R] [Module O R] [AddCommGroup M]
    [Module O M] (S : Set (R ⊗[O] M)) :
    (TensorProduct.map (LinearMap.id : R →ₗ[O] R) (LinearEquiv.refl O M).toLinearMap) '' S = S := by
  have : TensorProduct.map (LinearMap.id : R →ₗ[O] R) (LinearEquiv.refl O M).toLinearMap = LinearMap.id :=
    TensorProduct.map_id
  rw [this]
  exact Set.image_id S


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)), z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X → ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, ((F l).E K s LL h).tie.jD T z = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) z') := by
  intro D HW F l _ K s LL h K' h' hle hK0 T hT z' hz'
  have hN := ((GlobalTheory.NL.BaseField.base_indep D HW F l K s LL h K' h' hle hK0).2.2 T
    (resLt (K := K) (K' := K') (LL := LL) hle T) (LinearEquiv.refl ↥(OL LL) ↥T.L.T) (fun _ _ => rfl)).2 hT
    (restrict_crys D hle T hT)
  have hN2 := (image_map_refl (O := ↥(OL LL)) (R := RW LL) (M := ↥T.L.T) _).symm.trans hN
  have h1 := (exists_aN_iff ((F l).E K' s LL h').tie (resLt (K := K) (K' := K') (LL := LL) hle T) _ _
    (GlobalTheory.NL.IoXQ.main D HW F l K' s LL h').1 _).1 ⟨z', hz', rfl⟩
  refine (exists_aN_iff ((F l).E K s LL h).tie T _ _ (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).1 _).2 ?_
  refine h1.elim fun y hy => ⟨toTW hle T y, ?_, hy.2⟩
  exact hN2.subset hy.1

end GlobalTheory.NL.XNTransfer
end
end

