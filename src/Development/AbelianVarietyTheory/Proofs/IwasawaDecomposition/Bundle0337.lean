module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulNonsingInvCancelRightGram

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryTorusUnipotentCosetTransportIff
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd Formalism.UG.P

namespace GlobalTheory.SatInd

section CosetTransport

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem cosetT_le_of_nonunit {x : K} (h1 : Valued.v x ≤ 1) (h2 : ¬ Valued.v x⁻¹ ≤ 1) (h0 : x ≠ 0) :
    Valued.v x ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have hx0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.1 hx0
  rw [map_inv₀, ← hk] at h2
  rw [← hk] at h1 ⊢
  have h2' : ¬ (k⁻¹ : Multiplicative ℤ) ≤ 1 := by
    intro h; apply h2; rw [← WithZero.coe_inv]; exact_mod_cast h
  rw [WithZero.coe_le_coe]
  have : (k⁻¹ : Multiplicative ℤ) = Multiplicative.ofAdd (- Multiplicative.toAdd k) := rfl
  rw [this, ← ofAdd_zero, Multiplicative.ofAdd_le] at h2'
  rw [← ofAdd_toAdd k, Multiplicative.ofAdd_le]
  omega

theorem cosetT_v_image (g : K ≃+* K) (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {ϖ : K}
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    Valued.v (g ϖ) ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hv; exact absurd hv WithZero.zero_ne_coe
  have hmem : ∀ x : K, x ∈ intL K ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  apply cosetT_le_of_nonunit
  · rw [← hmem, ← hint, hmem, hv]; exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1)
  · rw [← map_inv₀, ← hmem, ← hint, hmem, map_inv₀, hv]
    rw [← WithZero.coe_inv, ← WithZero.coe_one, WithZero.coe_le_coe]
    decide
  · exact (map_ne_zero g).2 hϖ0

theorem cosetT_unit (g : K ≃+* K) (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {ϖ ϖ' : K}
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hv' : Valued.v ϖ' = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    Valued.v (g ϖ * ϖ'⁻¹) = 1 := by
  have hint' : ∀ x, x ∈ intL K ↔ g.symm x ∈ intL K := by
    intro x; rw [hint (g.symm x), RingEquiv.apply_symm_apply]
  have hmem : ∀ x : K, x ∈ intL K ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hv; exact absurd hv WithZero.zero_ne_coe
  have hinv : Valued.v ϖ⁻¹ = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_inv₀, hv, ← WithZero.coe_inv]; rfl
  have hinv' : Valued.v ϖ'⁻¹ = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_inv₀, hv', ← WithZero.coe_inv]; rfl
  have hone : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) *
      ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = 1 := by
    rw [← WithZero.coe_mul, ← ofAdd_add]; rfl
  have h1 : Valued.v (g ϖ * ϖ'⁻¹) ≤ 1 := by
    rw [Valuation.map_mul, hinv', ← hone]
    exact mul_le_mul' (cosetT_v_image g hint hv) le_rfl
  have h2 : Valued.v (g.symm ϖ' * ϖ⁻¹) ≤ 1 := by
    rw [Valuation.map_mul, hinv, ← hone]
    exact mul_le_mul' (cosetT_v_image g.symm hint' hv') le_rfl
  have h3 : Valued.v (g ϖ * ϖ'⁻¹)⁻¹ ≤ 1 := by
    have e : (g ϖ * ϖ'⁻¹)⁻¹ = g (g.symm ϖ' * ϖ⁻¹) := by
      rw [map_mul, RingEquiv.apply_symm_apply, map_inv₀, mul_inv, inv_inv, mul_comm]
    rw [e, ← hmem, ← hint, hmem]; exact h2
  rw [map_inv₀] at h3
  have hϖ'0 : ϖ' ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hv'; exact absurd hv' WithZero.zero_ne_coe
  have hne : Valued.v (g ϖ * ϖ'⁻¹) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (mul_ne_zero ((map_ne_zero g).2 hϖ0) (inv_ne_zero hϖ'0))
  exact le_antisymm h1 (by
    have := mul_le_mul' (le_refl (Valued.v (g ϖ * ϖ'⁻¹))) h3
    rwa [mul_inv_cancel₀ hne, mul_one] at this)

end CosetTransport
end GlobalTheory.SatInd

namespace GlobalTheory.SatInd

section CosetTransport2

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem cosetT_tMat_map (g : K →+* K) (x : K) (n m : ℕ) (a : Fin m → ℤ) :
    (tMat x n m a).map g = tMat (g x) n m a := by
  unfold tMat
  rw [Matrix.diagonal_map (map_zero g)]
  congr 1
  funext i
  split_ifs <;> simp [map_zpow₀]

theorem cosetT_tMat_mul (x y : K) (n m : ℕ) (a : Fin m → ℤ) :
    tMat (x * y) n m a = tMat x n m a * tMat y n m a := by
  unfold tMat
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> first | exact mul_zpow _ _ _ | exact (mul_one 1).symm

theorem cosetT_tMat_unit {σ : K →+* K} {u : K} (hσ : σ u = u) (hv : Valued.v u = 1) {n m : ℕ}
    (hm : 2 * m ≤ n) (a : Fin m → ℤ) :
    ∃ t : GU σ n, (((t : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat u n m a ∧
      t ∈ KU σ n := by
  have h0 : u ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hv; exact zero_ne_one hv
  let f : Fin n → K := fun i : Fin n =>
    if h : i.val < m then u ^ (a ⟨i.val, h⟩)
    else if h' : n - m ≤ i.val ∧ n - 1 - i.val < m then u ^ (-(a ⟨n - 1 - i.val, h'.2⟩)) else 1
  have hf : ∀ i, σ (f i) * f i.rev = 1 := by
    intro i
    simp only [f]
    have hs : ∀ k : ℤ, σ (u ^ k) = u ^ k := fun k => by rw [map_zpow₀, hσ]
    have hi := i.isLt
    have hr : (i.rev : ℕ) = n - 1 - i := by rw [Fin.val_rev]; omega
    by_cases h1 : (i : ℕ) < m
    · have h2 : ¬ (i.rev : ℕ) < m := by omega
      have h3 : n - m ≤ (i.rev : ℕ) ∧ n - 1 - (i.rev : ℕ) < m := by omega
      simp only [dif_pos h1, dif_neg h2, dif_pos h3, hs]
      have : (⟨n - 1 - (i.rev : ℕ), h3.2⟩ : Fin m) = ⟨i, h1⟩ := Fin.ext (by simp only; omega)
      rw [this, ← zpow_add₀ h0, add_neg_cancel, zpow_zero]
    · by_cases h1' : n - m ≤ (i : ℕ) ∧ n - 1 - (i : ℕ) < m
      · have h2 : (i.rev : ℕ) < m := by omega
        simp only [dif_neg h1, dif_pos h1', dif_pos h2, hs]
        have : (⟨(i.rev : ℕ), h2⟩ : Fin m) = ⟨n - 1 - i, h1'.2⟩ := Fin.ext (by simp only; omega)
        rw [this, ← zpow_add₀ h0, neg_add_cancel, zpow_zero]
      · have h2 : ¬ (i.rev : ℕ) < m := by omega
        have h3 : ¬ (n - m ≤ (i.rev : ℕ) ∧ n - 1 - (i.rev : ℕ) < m) := by omega
        simp only [dif_neg h1, dif_neg h1', dif_neg h2, dif_neg h3, map_one, one_mul]
  obtain ⟨t, ht, ht'⟩ := fSatake_diag_exists f hf
  have hfval : ∀ i, Valued.v (f i) = 1 := by
    intro i
    simp only [f]
    split_ifs <;> simp [map_zpow₀, hv]
  exact ⟨t, ht, fSatake_diag_mem_K ht ht' hfval⟩

theorem cosetT_guMap_mem_KU (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {n : ℕ} {k : GU σ n} (hk : k ∈ KU σ n) :
    guMap g hg n k ∈ KU σ' n := by
  have hmem : ∀ M : Matrix (Fin n) (Fin n) K, (∀ i j, M i j ∈ intL K) →
      M ∈ (RingHom.mapMatrix (m := Fin n) (intL K).subtype).range := by
    intro M hM
    exact ⟨Matrix.of fun i j => ⟨M i j, hM i j⟩, by ext i j; rfl⟩
  unfold KU intPts
  rw [Subgroup.mem_subgroupOf]
  refine ⟨(guMap g hg n k).2, glint_mem_range_of_integral (intL K) _ ?_ ?_⟩
  · refine hmem _ (fun i j => ?_)
    rw [guMap_val, Matrix.map_apply]
    exact (hint _).1 (fSatake_K_int hk i j)
  · rw [← Subgroup.coe_inv, ← map_inv]
    refine hmem _ (fun i j => ?_)
    rw [guMap_val, Matrix.map_apply]
    exact (hint _).1 (fSatake_K_int (inv_mem hk) i j)

end CosetTransport2
end GlobalTheory.SatInd

namespace GlobalTheory.SatInd

section CosetTransport3

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem cosetT_fwd (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) (ϖ ϖ' : K) (q q' n m : ℕ)
    (hU : IsUnramInv ϖ σ q) (hU' : IsUnramInv ϖ' σ' q') (hm : 2 * m ≤ n) (a : Fin m → ℤ)
    (y : GU σ n)
    (h : ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n,
      ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨u₁, hu₁, k, hk, hy⟩ := h
  have hϖ'0 : ϖ' ≠ 0 := by
    intro h0; have := hU'.2.2.2.1; rw [h0, Valuation.map_zero] at this
    exact absurd this WithZero.zero_ne_coe
  have hcv : Valued.v (g ϖ * ϖ'⁻¹) = 1 := cosetT_unit g hint hU.2.2.2.1 hU'.2.2.2.1
  have hcσ : σ' (g ϖ * ϖ'⁻¹) = g ϖ * ϖ'⁻¹ := by
    rw [map_mul, map_inv₀, ← hg, hU.2.2.1, hU'.2.2.1]
  obtain ⟨t, ht, htK⟩ := cosetT_tMat_unit hcσ hcv hm a
  have hgϖ : g ϖ = ϖ' * (g ϖ * ϖ'⁻¹) := by field_simp
  have hmap : ∀ M N : Matrix (Fin n) (Fin n) K, (M * N).map g = M.map g * N.map g :=
    fun M N => Matrix.map_mul (f := (g : K →+* K))
  have htm : (tMat ϖ n m a).map g = tMat (g ϖ) n m a := cosetT_tMat_map (g : K →+* K) ϖ n m a
  have hgu : IsBorelU (guMap g hg n u₁) := fun i j hij => by
    rw [guMap_val, Matrix.map_apply, hu₁.1 i j hij, map_zero]
  have htb : IsBorelU t := fSatake_borel_tMat ht
  refine ⟨t * guMap g hg n u₁ * t⁻¹,
    ⟨fSatake_borel_mul (fSatake_borel_mul htb hgu) (fSatake_borel_inv htb), fun i => ?_⟩,
    t * guMap g hg n k, mul_mem htK (cosetT_guMap_mem_KU g hg hint hk), ?_⟩
  · rw [fSatake_borel_diag_mul (fSatake_borel_mul htb hgu) (fSatake_borel_inv htb),
      fSatake_borel_diag_mul htb hgu, guMap_val, Matrix.map_apply, hu₁.2 i, map_one, mul_one,
      mul_comm]
    exact fSatake_borel_diag_inv htb i
  · have e : t * guMap g hg n u₁ * t⁻¹ * (t * guMap g hg n k) =
        t * guMap g hg n u₁ * guMap g hg n k := by group
    rw [Matrix.mul_assoc (tMat ϖ' n m a), ← Units.val_mul, ← Subgroup.coe_mul, e, guMap_val, hy,
      hmap, hmap, htm, hgϖ, cosetT_tMat_mul, ← ht]
    simp only [Subgroup.coe_mul, Units.val_mul, guMap_val, Matrix.mul_assoc]

theorem cosetT_iff : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (ϖ ϖ' : K) (q q' n m : ℕ), IsUnramInv ϖ σ q → IsUnramInv ϖ' σ' q' → 2 * m ≤ n → ∀ (a : Fin m → ℤ) (y : GU σ n), (∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ (∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n, ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  intro K _ _ g σ σ' hg hint ϖ ϖ' q q' n m hU hU' hm a y
  constructor
  · exact cosetT_fwd g hg hint ϖ ϖ' q q' n m hU hU' hm a y
  · intro h
    have hg' : ∀ x, g.symm (σ' x) = σ (g.symm x) := fun x => by
      apply g.injective
      rw [RingEquiv.apply_symm_apply, hg, RingEquiv.apply_symm_apply]
    have hint' : ∀ x, x ∈ intL K ↔ g.symm x ∈ intL K := fun x => by
      rw [hint (g.symm x), RingEquiv.apply_symm_apply]
    have h2 := cosetT_fwd g.symm hg' hint' ϖ' ϖ q' q n m hU' hU hm a (guMap g hg n y) h
    have hyy : guMap g.symm hg' n (guMap g hg n y) = y := by
      apply Subtype.ext
      apply Units.ext
      rw [guMap_val, guMap_val]
      ext i j
      simp
    rwa [hyy] at h2

end CosetTransport3
end GlobalTheory.SatInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAdd
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LieSum

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Mem.LiftGen Filter
open scoped Topology Classical

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem hasDerivAt_apply {u : ℝ → BB ψ S T} {A : BB ψ S T} (hu : HasDerivAt u A 0) {f : ℝ → WO S T → ℂ}
    (e : ∀ t, ((u t).1 : WO S T → ℂ) = f t) (w : WO S T) :
    HasDerivAt (fun t => f t w) ((A.1 : WO S T → ℂ) w) 0 := by
  have h3 := ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
  exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (congrFun (e t) w).symm)

theorem theta_nOp {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (hψ : IsStdChar D ψ (-1)) (X : Matrix (Ix S T) (Ix S T) ℂ) (F : BB ψ S T) (hF : IsThetaFunO ψ S T F.1)
    (l : ℂ) : IsThetaFunO ψ S T (nOp (rhoV hψ σ S T) (HM S T) X F + l • F).1 := by
  let J : thetaSub ψ S T →ₗ[ℂ] BB ψ S T :=
    { toFun := fun f => toB hψ f.1 f.2
      map_add' := fun f g => QB_ext fun x => rfl
      map_smul' := fun a f => QB_ext fun x => rfl }
  have hc : ∀ f, ((J f).1 : WO S T → ℂ) = f.1 := fun f => coe_toB hψ f.1 f.2
  have hJ : Function.Injective J := fun f g e => Subtype.ext (by rw [← hc, ← hc, e])
  have ht : ∀ f, IsThetaFunO ψ S T (J f).1 := fun f => (hc f).symm ▸ f.2
  have hs : ∀ f, Sm (rhoV hψ σ S T) (J f) := fun f => sm_of_theta h hψ _ (ht f)
  have hk : ∀ v f, ∃ g, J g = dH (rhoV hψ σ S T) v (J f) := by
    intro v f
    obtain ⟨F', hF', hd⟩ := exists_deriv h hψ (J f) (ht f) v
    refine ⟨⟨F'.1, hF'⟩, QB_ext fun w => ?_⟩
    rw [hc]
    exact (hd w).unique (((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v (hs f)))
  obtain ⟨x, d, -, hn⟩ := GlobalTheory.Mem.Lift.ThOps.exists_ops (HM S T) HM_herm HM_det (rhoV hψ σ S T) (isHeis_rhoB h hψ) J hJ hs hk
  have hxd : ∀ (X : Matrix (Ix S T) (Ix S T) ℂ) (f : thetaSub ψ S T) (F : BB ψ S T),
      (F.1 : WO S T → ℂ) = f.1 → ((∑ k, ∑ l, X k l • (x k * d l)) f).1 = (nOp (rhoV hψ σ S T) (HM S T) X F).1 := by
    intro X f F hF
    have e : F = J f := QB_ext fun w => by rw [hF, hc]
    rw [e, ← hn, hc]
  have h1 := ((∑ k, ∑ l, X k l • (x k * d l)) ⟨F.1, hF⟩).2
  rw [hxd X ⟨F.1, hF⟩ F rfl] at h1
  exact (thetaSub ψ S T).add_mem h1 ((thetaSub ψ S T).smul_mem l hF)

theorem isLittleO_rem {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (Φ : BB ψ S T →L[ℂ] H)
    {u : ℝ → BB ψ S T} {A : BB ψ S T} (hu : HasDerivAt u A 0) :
    (fun t : ℝ => Φ (u t - u 0 - (t : ℂ) • A)) =o[𝓝 0] fun t => t := by
  have h : HasDerivAt (fun t => Φ (u t)) (Φ A) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
  rw [hasDerivAt_iff_isLittleO] at h
  refine h.congr' (Filter.Eventually.of_forall fun t => ?_) (Filter.Eventually.of_forall fun t => sub_zero t)
  beta_reduce
  rw [sub_zero, map_sub, map_sub, map_smul, Complex.coe_smul]

theorem hasDerivAt_of_rem {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (Φ : BB ψ S T →L[ℂ] H)
    {u : ℝ → BB ψ S T} {A : BB ψ S T} (h : (fun t : ℝ => Φ (u t - u 0 - (t : ℂ) • A)) =o[𝓝 0] fun t => t) :
    HasDerivAt (fun t => Φ (u t)) (Φ A) 0 := by
  rw [hasDerivAt_iff_isLittleO]
  refine h.congr' (Filter.Eventually.of_forall fun t => ?_) (Filter.Eventually.of_forall fun t => (sub_zero t).symm)
  beta_reduce
  rw [sub_zero, map_sub, map_sub, map_smul, Complex.coe_smul]


set_option maxHeartbeats 2000000 in
theorem image_deriv_add {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (Φ : BB ψ S T →L[ℂ] H)
    {u₁ u₂ u₃ v : ℝ → BB ψ S T} {A₁ A₂ A₃ B : BB ψ S T}
    (d₁ : HasDerivAt u₁ A₁ 0) (d₂ : HasDerivAt u₂ A₂ 0) (d₃ : HasDerivAt u₃ A₃ 0) (dv : HasDerivAt v B 0)
    (z₁ : u₃ 0 = u₁ 0) (zv : v 0 = A₂)
    (hnorm : ∀ t : ℝ, ‖Φ (u₃ t - u₁ t - (t : ℂ) • v t)‖ = ‖Φ (u₂ t - u₂ 0 - (t : ℂ) • A₂)‖) :
    Φ A₃ = Φ (A₁ + A₂) := by
  have hid : ∀ t : ℝ, u₃ t - u₃ 0 - (t : ℂ) • (A₁ + A₂) = (u₃ t - u₁ t - (t : ℂ) • v t) +
      (t : ℂ) • (v t - v 0) + (u₁ t - u₁ 0 - (t : ℂ) • A₁) := fun t => by
    rw [z₁, zv]
    simp only [smul_sub, smul_add]
    abel
  have hD : HasDerivAt (fun t => Φ (u₃ t)) (Φ (A₁ + A₂)) 0 := by
    apply hasDerivAt_of_rem
    have o1 := isLittleO_rem Φ d₁
    have o2' := (isLittleO_rem Φ d₂).norm_left
    have o2 : (fun t : ℝ => Φ (u₃ t - u₁ t - (t : ℂ) • v t)) =o[𝓝 0] fun t => t := by
      rw [← Asymptotics.isLittleO_norm_left]
      exact o2'.congr_left fun t => (hnorm t).symm
    have hg : Tendsto (fun t => Φ (v t - v 0)) (𝓝 0) (𝓝 0) := by
      have := ((Φ.continuous.tendsto _).comp dv.continuousAt).sub_const (Φ (v 0))
      rw [sub_self] at this
      refine this.congr fun t => ?_
      simp only [Function.comp, map_sub]
    have o3 : (fun t : ℝ => Φ ((t : ℂ) • (v t - v 0))) =o[𝓝 0] fun t => t := by
      have := (Asymptotics.isBigO_refl (fun t : ℝ => t) (𝓝 0)).smul_isLittleO
        ((Asymptotics.isLittleO_one_iff ℝ).2 hg)
      refine this.congr (fun t => ?_) (fun t => ?_)
      · beta_reduce
        rw [map_smul, Complex.coe_smul]
      · simp
    have hΦ : ∀ t : ℝ, Φ (u₃ t - u₃ 0 - (t : ℂ) • (A₁ + A₂)) = Φ (u₃ t - u₁ t - (t : ℂ) • v t) +
        Φ ((t : ℂ) • (v t - v 0)) + Φ (u₁ t - u₁ 0 - (t : ℂ) • A₁) := fun t => by
      rw [hid t, map_add (f := _), map_add (f := _)]
    exact ((o2.add o3).add o1).congr_left fun t => (hΦ t).symm
  have h3 : HasDerivAt (fun t => Φ (u₃ t)) (Φ A₃) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) d₃
  exact h3.unique hD


set_option maxHeartbeats 2000000 in
theorem sum_of_curves (hψ : IsStdChar D ψ (-1)) {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : GlobalTheory.Ker.IsWeak ψ S T om) (γ₁ γ₂ : ℝ → GA D S × GA D T) (h₁ : γ₁ 0 = 1) (h₂ : γ₂ 0 = 1)
    (F : WO S T → ℂ) (hF : IsThetaFunO ψ S T F) {u₁ u₂ u₃ v : ℝ → BB ψ S T} {A₁ A₂ A₃ B : BB ψ S T}
    (e₁ : ∀ t, ((u₁ t).1 : WO S T → ℂ) = om (γ₁ t) F)
    (e₂ : ∀ t, ((u₂ t).1 : WO S T → ℂ) = om (γ₂ t) F)
    (e₃ : ∀ t, ((u₃ t).1 : WO S T → ℂ) = om (γ₁ t * γ₂ t) F)
    (ev : ∀ t, ((v t).1 : WO S T → ℂ) = om (γ₁ t) A₂.1)
    (d₁ : HasDerivAt u₁ A₁ 0) (d₂ : HasDerivAt u₂ A₂ 0) (d₃ : HasDerivAt u₃ A₃ 0) (dv : HasDerivAt v B 0)
    (hA₂ : IsThetaFunO ψ S T A₂.1) : (A₃.1 : WO S T → ℂ) = A₁.1 + A₂.1 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hk : ∀ (p : GA D S × GA D T) (a b : BB ψ S T), IsThetaFunO ψ S T b.1 → (a.1 : WO S T → ℂ) = om p b.1 →
      ‖toL2 _ _ (μ.restrict 𝓕) a‖ = ‖toL2 _ _ (μ.restrict 𝓕) b‖ := by
    intro p a b hb hab
    rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2, hab]
    exact hW.om_unit μ 𝓕 hμ h𝓕 p _ hb
  have z₁ : u₃ 0 = u₁ 0 := QB_ext fun x => congrFun
    (by rw [e₃, e₁, h₁, h₂, one_mul] : ((u₃ 0).1 : WO S T → ℂ) = (u₁ 0).1) x
  have z₂ : ((u₂ 0).1 : WO S T → ℂ) = F := by rw [e₂, h₂, map_one, Module.End.one_apply]
  have zv : v 0 = A₂ := QB_ext fun x => congrFun
    (by rw [ev, h₁, map_one, Module.End.one_apply] : ((v 0).1 : WO S T → ℂ) = A₂.1) x
  have th₂ : ∀ t, IsThetaFunO ψ S T (u₂ t).1 := fun t => by rw [e₂]; exact hW.om_pres _ _ hF
  have hnorm : ∀ t : ℝ, ‖toL2 _ _ (μ.restrict 𝓕) (u₃ t - u₁ t - (t : ℂ) • v t)‖ =
      ‖toL2 _ _ (μ.restrict 𝓕) (u₂ t - u₂ 0 - (t : ℂ) • A₂)‖ := fun t => by
    have ea : ((u₃ t - u₁ t - (t : ℂ) • v t).1 : WO S T → ℂ) =
        ((u₃ t).1 : WO S T → ℂ) - (u₁ t).1 - (t : ℂ) • ((v t).1 : WO S T → ℂ) := rfl
    have eb : ((u₂ t - u₂ 0 - (t : ℂ) • A₂).1 : WO S T → ℂ) =
        ((u₂ t).1 : WO S T → ℂ) - (u₂ 0).1 - (t : ℂ) • (A₂.1 : WO S T → ℂ) := rfl
    refine hk (γ₁ t) _ _ ?_ ?_
    · rw [eb]
      exact (thetaSub ψ S T).sub_mem ((thetaSub ψ S T).sub_mem (th₂ t) (th₂ 0)) ((thetaSub ψ S T).smul_mem _ hA₂)
    · rw [ea, eb, z₂, e₃, e₁, ev, e₂, map_mul, Module.End.mul_apply, map_sub, map_sub, map_smul]
  have key : toL2 _ _ (μ.restrict 𝓕) A₃ = toL2 _ _ (μ.restrict 𝓕) (A₁ + A₂) :=
    image_deriv_add _ d₁ d₂ d₃ dv z₁ zv hnorm
  have h4 := lintegral_norm_sq_eq_toL2 (μ.restrict 𝓕) (A₃ - (A₁ + A₂))
  rw [map_sub, key, sub_self, enorm_zero, zero_pow two_ne_zero,
    lintegral_eq_zero_iff ((A₃ - (A₁ + A₂)).1.continuous.measurable.enorm.pow_const 2)] at h4
  have h5 := GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 _ (A₃ - (A₁ + A₂)).1.continuous
    (BB_norm_periodic hψ _) (by filter_upwards [h4] with x hx; simpa using hx)
  exact sub_eq_zero.1 h5

end GlobalTheory.Mem.LieSum


set_option maxHeartbeats 2000000 in
open Classical in
theorem GlobalTheory.Mem.LieSum.hasDerivAt_add : ∀ (D : D7) (V W : HSp D) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt W τ, ∀ F F₁ F₂ : WO V W → ℂ, IsThetaFunO ψ V W F → (∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) F z) (F₁ z) 0) → (∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) F z) (F₂ z) 0) → ∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, oneP θ W τ Y t) F z) (F₁ z + F₂ z) 0 := by
  intro D V W θ ψ χS χT ω τ hθ hω X hX Y hY F F₁ F₂ hF h₁ h₂ z
  have hψ := hω.std
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hW := GlobalTheory.Ker.isWeak_of_datum hω
  have hc := hω.om_cont
  let γ₁ : ℝ → GA D V × GA D W := fun t => (oneP θ V τ X t, 1)
  let γ₂ : ℝ → GA D V × GA D W := fun t => (1, oneP θ W τ Y t)
  let γ₃ : ℝ → GA D V × GA D W := fun t => (oneP θ V τ X t, oneP θ W τ Y t)
  have hγ : ∀ t, γ₃ t = γ₁ t * γ₂ t := fun t => by
    simp only [γ₁, γ₂, γ₃, Prod.mk_mul_mk, mul_one, one_mul]
  have m₁ : ∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ V W (γ₁ t) k l)
      (GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ (-X)) k l) 0 := fun k l => by
    simp only [γ₁, GlobalTheory.RealWeil.mM_apply, GlobalTheory.Mem.Lift.WeylAction.oneP_inv hθ hX, GlobalTheory.WeilVacMove.mt_one,
      GlobalTheory.WeilVacMove.compAt_one, GlobalTheory.Mem.Lift.WeylAction.blk_apply]
    split_ifs
    · exact (GlobalTheory.Mem.Lift.WeylAction.hasDerivAt_comp hθ (GlobalTheory.Mem.Lift.WeylAction.neg_mem_lieAt hX) _ _ _).const_mul _
    · exact hasDerivAt_const _ _
  have m₂ : ∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ V W (γ₂ t) k l)
      (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) k l) 0 := fun k l => by
    simp only [γ₂, GlobalTheory.RealWeil.mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one,
      GlobalTheory.Mem.Lift.WeylAction.blk_apply]
    split_ifs
    · exact (GlobalTheory.Mem.Lift.WeylAction.hasDerivAt_comp hθ hY _ _ _).mul_const _
    · exact hasDerivAt_const _ _
  have m₃ : ∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ V W (γ₃ t) k l)
      (∑ j, (GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ (-X)) k j * GlobalTheory.RealWeil.mM θ V W (γ₂ 0) j l +
        GlobalTheory.RealWeil.mM θ V W (γ₁ 0) k j * GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) j l)) 0 :=
    fun k l => by
      simp only [hγ, map_mul, Matrix.mul_apply]
      exact HasDerivAt.fun_sum fun j _ => (m₁ k j).mul (m₂ j l)
  obtain ⟨l₁, g₁⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ h ψ hψ V W ω hW hc γ₁
    ((GlobalTheory.Mem.Lift.continuous_oneP hθ hX).prodMk continuous_const)
    (fun s t => by simp only [γ₁]; rw [GlobalTheory.Mem.Lift.oneP_add hθ hX, Prod.mk_mul_mk, one_mul])
    (fun t => ⟨(GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX t).1, one_mem _⟩) _ m₁
  obtain ⟨l₂, g₂⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ h ψ hψ V W ω hW hc γ₂
    (continuous_const.prodMk (GlobalTheory.Mem.Lift.continuous_oneP hθ hY))
    (fun s t => by simp only [γ₂]; rw [GlobalTheory.Mem.Lift.oneP_add hθ hY, Prod.mk_mul_mk, one_mul])
    (fun t => ⟨one_mem _, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t).1⟩) _ m₂
  obtain ⟨l₃, g₃⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ h ψ hψ V W ω hW hc γ₃
    ((GlobalTheory.Mem.Lift.continuous_oneP hθ hX).prodMk (GlobalTheory.Mem.Lift.continuous_oneP hθ hY))
    (fun s t => by simp only [γ₃]; rw [GlobalTheory.Mem.Lift.oneP_add hθ hX, GlobalTheory.Mem.Lift.oneP_add hθ hY, Prod.mk_mul_mk])
    (fun t => ⟨(GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX t).1, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t).1⟩) _ m₃
  have eF := GlobalTheory.RealWeil.coe_toB hψ F hF
  have hFb : IsThetaFunO ψ V W (GlobalTheory.RealWeil.toB hψ F hF).1 := by rw [eF]; exact hF
  obtain ⟨u₁, e₁, d₁⟩ := g₁ _ hFb
  obtain ⟨u₂, e₂, d₂⟩ := g₂ _ hFb
  obtain ⟨u₃, e₃, d₃⟩ := g₃ _ hFb
  have hA₂ := GlobalTheory.Mem.LieSum.theta_nOp h hψ (GlobalTheory.RealWeil.blk (Pi.single τ Y) fun _ => 1) _ hFb l₂
  obtain ⟨v, ev, dv⟩ := g₁ _ hA₂
  rw [eF] at e₁ e₂ e₃
  have k₁ := GlobalTheory.Mem.LieSum.hasDerivAt_apply d₁ e₁ z
  have k₂ := GlobalTheory.Mem.LieSum.hasDerivAt_apply d₂ e₂ z
  have k₃ := GlobalTheory.Mem.LieSum.hasDerivAt_apply d₃ e₃ z
  have hs := GlobalTheory.Mem.LieSum.sum_of_curves hψ hW γ₁ γ₂
    (by simp only [γ₁]; rw [GlobalTheory.Mem.Lift.oneP_zero hθ]; rfl)
    (by simp only [γ₂]; rw [GlobalTheory.Mem.Lift.oneP_zero hθ]; rfl) F hF e₁ e₂ (fun t => by rw [e₃, hγ]) ev d₁ d₂ d₃ dv hA₂
  rw [hs, Pi.add_apply, k₁.unique (h₁ z), k₂.unique (h₂ z)] at k₃
  exact k₃
end

