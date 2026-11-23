module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0025

@[expose] public section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem lift_riesz (D : Formalism.BasicNotions.D7) (φ : (VS D).V →ₗ[D.host.E] D.host.E) : ∃ μ : (VS D).V, ∀ v, (VS D).hT μ v = φ v := by
  classical
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis (VS D).hT (VS D).nondeg (VS D).frame
  refine ⟨∑ j, star (φ ((VS D).frame j)) • bs j, fun v => ?_⟩
  have key : (VS D).hT (∑ j, star (φ ((VS D).frame j)) • bs j) = φ := by
    apply (VS D).frame.ext
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    have hs : ∀ j, (VS D).hT (star (φ ((VS D).frame j)) • bs j) ((VS D).frame i) =
        φ ((VS D).frame j) * (if i = j then 1 else 0) := by
      intro j
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
      congr 1
      rw [← (VS D).herm.eq ((VS D).frame i) (bs j), hbs]
      split_ifs <;> simp
    simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [key]

private theorem lift_span_eq_top_of_unimodular (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hL : Λ.FG) (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) :
    Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ := by
  by_contra hspan
  obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  obtain ⟨μ, hμ⟩ := lift_riesz D φ
  have hμ₀ : μ ≠ 0 := by
    intro h
    apply hφ₀
    ext y
    simpa [h] using (hμ y).symm
  have hline (a : D.host.E) : a • μ ∈ Λ := by
    rw [← hU]
    change a • μ ∈ Formalism.E.hdual (VS D).hT Λ
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    intro y hy
    have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
    simp [← (VS D).herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
  obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
    (show μ ∉ (⊥ : Submodule D.host.E (VS D).V) by simpa using hμ₀)
  let f := ψ.restrictScalars (𝓞 D.host.E)
  have hmap (x : D.host.E) : x ∈ Λ.map f := by
    refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
    change ψ ((x / ψ μ) • μ) = x
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
  obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
    (S := nonZeroDivisors (𝓞 D.host.E)) (hL.map f)
  have hinj := IsFractionRing.injective (𝓞 D.host.E) D.host.E
  have hne {a : 𝓞 D.host.E} (ha : a ≠ 0) : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 :=
    fun h => ha (hinj (h.trans (map_zero _).symm))
  have hinteger (x : D.host.E) : IsLocalization.IsInteger (𝓞 D.host.E) x := by
    have hx := hd _ (hmap ((algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ * x))
    rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
      one_mul] at hx
  apply RingOfIntegers.not_isField D.host.E
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 D.host.E) D.host.E a)⁻¹)
  refine ⟨b, hinj ?_⟩
  rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]


section Lift

variable {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
variable {sE : WbQ D F0 →ₗ[D.host.E] perpS (VS D) F0.X} {u : (VS D).V →ₗ[D.host.E] WbQ D F0}

theorem Xa_le_X (j : ℕ) : F0.Xa j ≤ F0.X :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem gF_X (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v)
    (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) {x : (VS D).V} (hx : x ∈ F0.X) : gF D F0 sE u σ x = x := by
  rw [gF_apply, u_X hu hx, map_zero, sub_self, map_zero, Submodule.coe_zero, add_zero]

theorem gF_perp_mk (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v)
    (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) (y : perpS (VS D) F0.X) (h : gF D F0 sE u σ y ∈ perpS (VS D) F0.X) :
    (Submodule.Quotient.mk ⟨gF D F0 sE u σ y, h⟩ : WbQ D F0) = σ (Submodule.Quotient.mk y) := by
  have e : (⟨gF D F0 sE u σ y, h⟩ : perpS (VS D) F0.X) =
      y + sE (σ (Submodule.Quotient.mk y) - Submodule.Quotient.mk y) := by
    apply Subtype.ext
    change gF D F0 sE u σ (y : (VS D).V) = _
    rw [gF_apply, u_perp hsE hu y, Submodule.coe_add]
  rw [e, Submodule.Quotient.mk_add, hsE]
  abel

theorem quotient_lift_fixes_anisotropic (hsE : ∀ a, (Submodule.Quotient.mk (sE a) : WbQ D F0) = a)
    (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v)
    (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) (hz : σ (zbar D F0) = zbar D F0) : gF D F0 sE u σ F0.z = F0.z := by
  have e : u F0.z = zbar D F0 := u_perp hsE hu ⟨F0.z, z_mem_perp D F0⟩
  rw [gF_apply, e, hz, sub_self, map_zero, Submodule.coe_zero, add_zero]

theorem gF_lam (hu : ∀ a v, hWb D F0 a (u v) = (VS D).hT (sE a : (VS D).V) v)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    (hsEM : ∀ m ∈ Mof D F0 Λ, ((sE m : perpS (VS D) F0.X) : (VS D).V) ∈ Λ)
    (hMu : Formalism.HermitianLatticesTheory.dual (hWb D F0) (Mof D F0 Λ) = Mof D F0 Λ)
    (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0) (hσM : ∀ m ∈ Mof D F0 Λ, σ m ∈ Mof D F0 Λ)
    {l : (VS D).V} (hl : l ∈ Λ) : gF D F0 sE u σ l ∈ Λ := by
  have hul : u l ∈ Mof D F0 Λ := by
    rw [← hMu, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro m hm
    rw [hu]
    obtain ⟨o, ho⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.int_val (S := VS D) hU (hsEM m hm) hl
    exact Submodule.mem_one.2 ⟨o, ho⟩
  rw [gF_apply]
  exact Submodule.add_mem _ hl (hsEM _ (Submodule.sub_mem _ (hσM _ hul) hul))

theorem lift (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hL : Submodule.IsLattice D.host.E Λ)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0)
    (hσ : σ ∈ stabZ (hWb D F0) (zbar D F0) (Mof D F0 Λ)) :
    (σ : WbQ D F0 → WbQ D F0) ∈ autLz D F0 Λ := by
  obtain ⟨⟨hσi, hσz⟩, hσM⟩ := hσ
  have hfull : Submodule.IsFullLattice D.host.E Λ :=
    { toIsLattice := hL, span_eq_top := lift_span_eq_top_of_unimodular D hL.fg hU }
  obtain ⟨sE, hsE, hsEM⟩ := exists_sE (F0 := F0) Λ hfull
  obtain ⟨u, hu⟩ := exists_u D F0 sE
  have hMu : Formalism.HermitianLatticesTheory.dual (hWb D F0) (Mof D F0 Λ) = Mof D F0 Λ := Mof_unimod D F0 Λ hL hU
  have hσM1 : ∀ m ∈ Mof D F0 Λ, σ m ∈ Mof D F0 Λ := by
    intro m hm
    rw [← hσM]
    exact Submodule.mem_map_of_mem hm
  have hσM2 : ∀ m ∈ Mof D F0 Λ, σ.symm m ∈ Mof D F0 Λ := by
    intro m hm
    rw [← hσM] at hm
    obtain ⟨m', hm', rfl⟩ := hm
    simpa using hm'
  have hisom : ∀ x y, hWb D F0 (σ x) (σ y) = hWb D F0 x y := hσi
  refine ⟨gE hsE hu σ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x y
    exact gF_isom hsE hu σ hisom x y
  · intro j
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      show gF D F0 sE u σ w ∈ F0.Xa j
      rw [gF_X hu σ (Xa_le_X j hw)]
      exact hw
    · intro hv
      refine ⟨v, hv, ?_⟩
      show gF D F0 sE u σ v = v
      exact gF_X hu σ (Xa_le_X j hv)
  · exact quotient_lift_fixes_anisotropic hsE hu σ hσz
  · apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩
      exact gF_lam hu Λ hU hsEM hMu σ hσM1 hl
    · intro l hl
      refine ⟨(gE hsE hu σ).symm l, ?_, ?_⟩
      · rw [gE_symm_apply]
        exact gF_lam hu Λ hU hsEM hMu σ.symm hσM2 hl
      · show gE hsE hu σ ((gE hsE hu σ).symm l) = l
        exact LinearEquiv.apply_symm_apply _ l
  · intro x hx
    exact (gF_perp_mk hsE hu σ x hx).symm

end Lift

section Induced

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem Xa_r : F0.Xa D.R.rS = F0.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext v
  simp

variable {D F0}

theorem stabF_X {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) :
    F0.X.map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
  rw [← Xa_r D F0]
  exact hγ.2.1 _

theorem stabilizer_maps_isotropic {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {x : (VS D).V} (hx : x ∈ F0.X) :
    γ x ∈ F0.X := by
  rw [← stabF_X hγ]
  exact Submodule.mem_map_of_mem hx

theorem stabilizer_symm_maps_isotropic {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {x : (VS D).V} (hx : x ∈ F0.X) :
    γ.symm x ∈ F0.X := by
  rw [← stabF_X hγ] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  simpa using hw

theorem stabilizer_maps_orthogonal {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {y : (VS D).V}
    (hy : y ∈ perpS (VS D) F0.X) : γ y ∈ perpS (VS D) F0.X := by
  intro x hx
  have h := hy (γ.symm x) (stabilizer_symm_maps_isotropic hγ hx)
  rw [← hγ.1 (γ.symm x) y, LinearEquiv.apply_symm_apply] at h
  exact h

theorem stabilizer_symm_maps_orthogonal {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) {y : (VS D).V}
    (hy : y ∈ perpS (VS D) F0.X) : γ.symm y ∈ perpS (VS D) F0.X := by
  intro x hx
  have h := hy (γ x) (stabilizer_maps_isotropic hγ hx)
  rw [← LinearEquiv.apply_symm_apply γ y, hγ.1] at h
  exact h

def indL (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hp : ∀ y ∈ perpS (VS D) F0.X, γ y ∈ perpS (VS D) F0.X)
    (hX : ∀ x ∈ F0.X, γ x ∈ F0.X) : WbQ D F0 →ₗ[D.host.E] WbQ D F0 :=
  Submodule.mapQ _ _ ((γ : (VS D).V →ₗ[D.host.E] (VS D).V).restrict hp) (fun x hx => hX _ hx)

theorem indL_mk (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hp : ∀ y ∈ perpS (VS D) F0.X, γ y ∈ perpS (VS D) F0.X)
    (hX : ∀ x ∈ F0.X, γ x ∈ F0.X) (a : perpS (VS D) F0.X) :
    indL γ hp hX (Submodule.Quotient.mk a) = Submodule.Quotient.mk ⟨γ a, hp a a.2⟩ := rfl

def indE {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0 :=
  LinearEquiv.ofLinear (indL γ (fun y hy => stabilizer_maps_orthogonal hγ hy) (fun x hx => stabilizer_maps_isotropic hγ hx))
    (indL γ.symm (fun y hy => stabilizer_symm_maps_orthogonal hγ hy) (fun x hx => stabilizer_symm_maps_isotropic hγ hx))
    (by
      refine LinearMap.ext fun q => ?_
      induction q using Submodule.Quotient.induction_on with | H a => ?_
      rw [LinearMap.comp_apply, indL_mk, indL_mk, LinearMap.id_apply]
      congr 1
      apply Subtype.ext
      simp)
    (by
      refine LinearMap.ext fun q => ?_
      induction q using Submodule.Quotient.induction_on with | H a => ?_
      rw [LinearMap.comp_apply, indL_mk, indL_mk, LinearMap.id_apply]
      congr 1
      apply Subtype.ext
      simp)

theorem indE_mk {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ stabF D F0) (a : perpS (VS D) F0.X) :
    indE hγ (Submodule.Quotient.mk a) = Submodule.Quotient.mk ⟨γ a, stabilizer_maps_orthogonal hγ a.2⟩ := rfl

theorem autLz_sub (Λ : Submodule (𝓞 D.host.E) (VS D).V) (φ : WbQ D F0 → WbQ D F0) (hφ : φ ∈ autLz D F0 Λ) :
    φ ∈ (fun σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0 => (σ : WbQ D F0 → WbQ D F0)) ''
      stabZ (hWb D F0) (zbar D F0) (Mof D F0 Λ) := by
  obtain ⟨γ, hγ, hγΛ, hφ⟩ := hφ
  refine ⟨indE hγ, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro x y
    induction x using Submodule.Quotient.induction_on with | H a => ?_
    induction y using Submodule.Quotient.induction_on with | H b => ?_
    rw [indE_mk, indE_mk, hWb_mk, hWb_mk]
    exact hγ.1 _ _
  · rw [zbar, indE_mk]
    congr 1
    apply Subtype.ext
    exact hγ.2.2
  · apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩
      obtain ⟨b, hbΛ, rfl⟩ := (mem_Mof D F0 Λ m).1 hm
      show indE hγ (Submodule.Quotient.mk b) ∈ Mof D F0 Λ
      rw [indE_mk, mem_Mof]
      refine ⟨_, ?_, rfl⟩
      rw [← hγΛ]
      exact Submodule.mem_map_of_mem hbΛ
    · intro m hm
      obtain ⟨b, hbΛ, rfl⟩ := (mem_Mof D F0 Λ m).1 hm
      have hb' : γ.symm b ∈ Λ := by
        rw [← hγΛ] at hbΛ
        obtain ⟨l, hl, hlb⟩ := hbΛ
        rw [← hlb]
        simpa using hl
      refine ⟨Submodule.Quotient.mk ⟨γ.symm b, stabilizer_symm_maps_orthogonal hγ b.2⟩, (mem_Mof D F0 Λ _).2 ⟨_, hb', rfl⟩, ?_⟩
      show indE hγ (Submodule.Quotient.mk ⟨γ.symm b, stabilizer_symm_maps_orthogonal hγ b.2⟩) = Submodule.Quotient.mk b
      rw [indE_mk]
      congr 1
      apply Subtype.ext
      simp
  · funext q
    induction q using Submodule.Quotient.induction_on with | H a => ?_
    show indE hγ (Submodule.Quotient.mk a) = φ (Submodule.Quotient.mk a)
    rw [indE_mk, hφ a]

theorem autLz_eq (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hL : Submodule.IsLattice D.host.E Λ)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) :
    autLz D F0 Λ = (fun σ : WbQ D F0 ≃ₗ[D.host.E] WbQ D F0 => (σ : WbQ D F0 → WbQ D F0)) ''
      stabZ (hWb D F0) (zbar D F0) (Mof D F0 Λ) := by
  ext φ
  constructor
  · exact autLz_sub Λ φ
  · rintro ⟨σ, hσ, rfl⟩
    exact lift Λ hL hU σ hσ

end Induced

theorem row_weight_formula : RowWeight := by
  intro D u F0 Λ hrow
  obtain ⟨_, ⟨hL, hU, _, _⟩, _⟩ := hrow
  rw [autLz_eq Λ hL hU]
  exact Nat.card_image_of_injective DFunLike.coe_injective _

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf

theorem PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_weight_formula : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeight :=
  PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowWeightPf.row_weight_formula
