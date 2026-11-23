module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTwistRamifiedCharNeSelf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRestrictionWdCompatible
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section
open IsNilpotent

namespace GlobalTheory.AboveL.ResWD

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}
  {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem exists_tval_resI (h' : IsPlaceOver A v') (hl' : ((l : ℕ) : 𝓞 L) ∉ v'.asIdeal)
    {t : Ine (F := K) A →* Multiplicative ℤ_[l]} {t' : Ine (F := L) A →* Multiplicative ℤ_[l]}
    (ht : IsTameChar t) (ht' : IsTameChar t') :
    ∃ c : Qbar l, c ≠ 0 ∧ ∀ σ, tval t (ResEx.resI (K := K) σ) = c * tval t' σ := by
  obtain ⟨c, hc⟩ := GlobalTheory.TameCharUnique.exists_eq_mul L Ω A v' h' l hl' (t.comp ResEx.resI) t'
    (ht.1.comp ResEx.continuous_resI) ht'.1 ht'.2
  refine ⟨algebraMap ℚ_[l] (Qbar l) (c : ℚ_[l]), ?_, fun σ => ?_⟩
  swap
  · have := hc σ
    simp only [MonoidHom.comp_apply] at this
    simp [tval, this]
  intro h0
  rw [map_eq_zero, PadicInt.coe_eq_zero] at h0
  have hc0 : ∀ σ, (t (ResEx.resI (K := K) σ)).toAdd = 0 := fun σ => by
    have := hc σ
    simpa [h0] using this
  obtain ⟨σ, hσ⟩ := ht.2 (Multiplicative.ofAdd 1)
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  let f : ℕ → (L →ₐ[K] Ω) := fun n => (((σ : G K Ω) ^ n : G K Ω) : Ω →ₐ[K] Ω).comp (IsScalarTower.toAlgHom K L Ω)
  have main : ∀ i j : ℕ, i < j → f i = f j → False := fun i j hij e => by
    set k := j - i with hk
    have hk0 : 0 < k := Nat.sub_pos_of_lt hij
    have hfix : ∀ x : L, ((σ : G K Ω) ^ k).toRingEquiv (algebraMap L Ω x) = algebraMap L Ω x := fun x => by
      have e1 := congrArg (fun g : L →ₐ[K] Ω => g x) e
      simp only [f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', AlgEquiv.coe_algHom] at e1
      have e2 : (σ : G K Ω) ^ j = (σ : G K Ω) ^ i * (σ : G K Ω) ^ k := by
        rw [← pow_add, hk, Nat.add_sub_cancel' hij.le]
      rw [e2, AlgEquiv.mul_apply] at e1
      exact (((σ : G K Ω) ^ i).injective e1).symm
    let σ'' : G L Ω := AlgEquiv.ofRingEquiv (f := ((σ : G K Ω) ^ k).toRingEquiv) hfix
    have hres : AlgEquiv.restrictScalarsHom K σ'' = (σ : G K Ω) ^ k := AlgEquiv.ext fun _ => rfl
    have hmem : σ'' ∈ Ine (F := L) A := by
      show AlgEquiv.restrictScalarsHom K σ'' ∈ Ine (F := K) A
      rw [hres]
      exact pow_mem σ.2 k
    have e3 : ResEx.resI (K := K) ⟨σ'', hmem⟩ = σ ^ k := Subtype.ext (by rw [SubgroupClass.coe_pow, ← hres]; rfl)
    have := hc0 ⟨σ'', hmem⟩
    rw [e3, map_pow, hσ, ← ofAdd_nsmul, toAdd_ofAdd, nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at this
    omega
  obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact main i j hlt e
  · exact main j i hlt e.symm

theorem isMonodromy_res {t : Ine (F := K) A →* Multiplicative ℤ_[l]}
    {t' : Ine (F := L) A →* Multiplicative ℤ_[l]} {r : G K Ω →* GL (Fin a) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {c : Qbar l} (hN : IsMonodromy t r N)
    (hc : ∀ σ, tval t (ResEx.resI (K := K) σ) = c * tval t' σ) :
    IsMonodromy t' (resTo L r) (c • N) := by
  obtain ⟨h1, U, hU, H⟩ := hN
  refine ⟨h1.smul c, U.comap ResEx.resI, hU.preimage ResEx.continuous_resI, fun σ hσ => ?_⟩
  have := H _ hσ
  rw [smul_smul, mul_comm, ← hc]
  exact this

theorem exists_conj (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (hl : ((l : ℕ) : 𝓞 K) ∉ v.asIdeal)
    {t : Ine (F := K) A →* Multiplicative ℤ_[l]}
    {t' : Ine (F := L) A →* Multiplicative ℤ_[l]} {r : G K Ω →* GL (Fin a) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {c : Qbar l} (ht : IsTameChar t) (hN : IsMonodromy t r N)
    (hc : ∀ σ, tval t (ResEx.resI (K := K) σ) = c * tval t' σ) :
    ∃ β : Qbar l, ∀ g : Weil h', exp (β • N) * wdMat t' (deg_frob (h := h')) (resTo L r) (c • N) g =
      wdMat t (deg_frob (h := h)) r N (ResEx.resW h h' g) * exp (β • N) := by
  have hq0 : ((normV v : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV v).ne_bot
  have hf : deg (ResEx.resW h h' (frob h')) ≠ 0 := by
    intro h0
    have h1 : ((frob h' : Weil h') : G L Ω) ∈ Ine (F := L) A :=
      (deg_eq_zero_iff (σ := ResEx.resW h h' (frob h'))).1 h0
    have h2 := (deg_eq_zero_iff (σ := frob h')).2 h1
    rw [deg_frob] at h2
    exact one_ne_zero h2
  have hq1 : 1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Ne, inv_eq_one]
    intro h1
    have h3 : (((normV v : ℕ) : ℚ) ^ deg (ResEx.resW h h' (frob h')) : ℚ) = 1 := by
      rw [← Rat.cast_inj (α := Qbar l)]; push_cast; exact h1
    exact hf ((zpow_eq_one_iff_right₀ (Nat.cast_nonneg _)
      (Nat.cast_ne_one.mpr (one_lt_normV v).ne')).mp h3)
  have key : ∀ m : ℤ,
      tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ m)) *
        (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹) =
      tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h'))) *
        (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h') ^ m))⁻¹) := fun m => by
    have h1 := ht.tval_inePart_mul hl (deg_frob (h := h)) (ResEx.resW h h' (frob h'))
      (ResEx.resW h h' (frob h') ^ m)
    have h2 := ht.tval_inePart_mul hl (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ m)
      (ResEx.resW h h' (frob h'))
    rw [(Commute.self_zpow (ResEx.resW h h' (frob h')) m).eq] at h1
    linear_combination h2 - h1
  refine ⟨tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h'))) /
    (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹), fun g => ?_⟩
  have hg : g = frob h' ^ deg g * ineIncl h' (inePart (deg_frob (h := h')) g) := by
    rw [ineIncl_inePart, mul_inv_cancel_left]
  have hRg : ResEx.resW h h' g =
      ResEx.resW h h' (frob h') ^ deg g * ineIncl h (ResEx.resI (inePart (deg_frob (h := h')) g)) := by
    conv_lhs => rw [hg]
    rw [map_mul, map_zpow, ResEx.resW_ineIncl]
  have hT : tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' g)) =
      tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ deg g)) +
        tval t (ResEx.resI (inePart (deg_frob (h := h')) g)) := by
    rw [hRg, ht.tval_inePart_mul hl, deg_ineIncl, zpow_zero, inv_one, one_mul, inePart_ineIncl]
  have hd : deg (ResEx.resW h h' g) = deg (ResEx.resW h h' (frob h') ^ deg g) := by
    rw [hRg, deg_mul, deg_ineIncl, add_zero]
  have hs := key (deg g)
  have hqd : ((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' g) ≠ 0 := zpow_ne_zero _ hq0
  rw [wdMat, wdMat, hT]
  have e1 : (-tval t' (inePart (deg_frob (h := h')) g)) • (c • N) =
      (-tval t (ResEx.resI (inePart (deg_frob (h := h')) g))) • N := by
    rw [smul_smul, hc]
    congr 1
    ring
  have e2 : ((resTo L r g : Matrix (Fin a) (Fin a) (Qbar l))) = r (ResEx.resW h h' g) := rfl
  rw [e1, e2]
  set β := tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h'))) /
    (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹) with hβ
  have h2 := hN.mul_exp hl ht (ResEx.resW h h' g) ((((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' g))⁻¹ * β)
  rw [mul_inv_cancel_left₀ hqd] at h2
  rw [← mul_assoc, ← h2, mul_assoc, mul_assoc, ← exp_add_smul hN.1, ← exp_add_smul hN.1]
  congr 3
  have hsm : tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ deg g)) =
      β * (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h') ^ deg g))⁻¹) := by
    rw [hβ, div_mul_eq_mul_div, eq_div_iff hq1]
    linear_combination hs
  rw [hd]
  linear_combination hsm

end GlobalTheory.AboveL.ResWD

namespace GlobalTheory.AboveL

theorem wdOf_restricts : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G K Ω →* GL (Fin a) (Qbar l)) (hl : ((l : ℕ) : 𝓞 K) ∉ v.asIdeal) (hl' : ((l : ℕ) : 𝓞 L) ∉ v'.asIdeal), Continuous r → Restricts (wdOf h hl ι r) (wdOf h' hl' ι (resTo L r)) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' l _ ι a r hl hl' hr
  have hr' : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp hr
  have ht := isTameChar_tameL h hl
  have ht' := isTameChar_tameL h' hl'
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hr'
  obtain ⟨c, hc0, hc⟩ := ResWD.exists_tval_resI h' hl' ht ht'
  have hN' := ResWD.isMonodromy_res hN hc
  obtain ⟨β, hβ⟩ := ResWD.exists_conj h h' hl ht hN hc
  obtain ⟨aK, haK⟩ := hN.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  have ex : wdOf h hl ι r = WD.mk aK := IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, N, aK, hN, haK, rfl⟩
  have hb : IsFrobSS (fun g => toEndC ι (wdMat (tameL h hl) (deg_frob (h := h)) r N (ResEx.resW h h' g)))
      (toEndC ι N) (ResEx.resRep h h' aK) := ⟨haK.1, fun g => haK.2 _⟩
  obtain ⟨aL2, haL2⟩ := hN'.exists_isFrobSS hl' ht' (deg_frob (h := h')) ι
  have hcomm : ∀ g, hN'.rep hl' ht' (deg_frob (h := h')) ι g * toEndC ι N =
      ((normV v' : ℕ) : ℂ) ^ deg g • (toEndC ι N * hN'.rep hl' ht' (deg_frob (h := h')) ι g) := fun g => by
    have := hN'.rep_comm hl' ht' (deg_frob (h := h')) ι g
    rw [toEndC_smul, mul_smul_comm, smul_mul_assoc, smul_comm] at this
    exact smul_right_injective _ ((map_ne_zero ι).mpr hc0) this
  obtain ⟨aL1, haL1⟩ := WeilDeligne.exists_isFrobSS (hN'.rep hl' ht' (deg_frob (h := h')) ι) (toEndC ι N)
    (hN'.isSmooth_rep hl' ht' _ ι) (hN.1.map _) hcomm
  obtain ⟨u, hu⟩ := (isUnit_exp (hN.1.smul β)).map (toEndC ι (n := Fin a))
  have i1 : aL1.Iso (ResEx.resRep h h' aK) := haL1.iso hb (LinearMap.GeneralLinearGroup.toLinearEquiv u)
    (fun g w => by
      show ((u : Module.End ℂ (Fin a → ℂ)) * toEndC ι (wdMat (tameL h' hl') (deg_frob (h := h')) (resTo L r) (c • N) g)) w =
        (toEndC ι (wdMat (tameL h hl) (deg_frob (h := h)) r N (ResEx.resW h h' g)) * (u : Module.End ℂ (Fin a → ℂ))) w
      rw [hu, ← map_mul, hβ, map_mul])
    (fun w => by
      show ((u : Module.End ℂ (Fin a → ℂ)) * toEndC ι N) w = (toEndC ι N * (u : Module.End ℂ (Fin a → ℂ))) w
      rw [hu, ← map_mul, exp_smul_mul hN.1, map_mul])
  have i2 : aL1.Iso aL2 := haL1.iso_of_smul ((map_ne_zero ι).mpr hc0) (by
    have := haL2
    rw [toEndC_smul] at this
    exact this)
  have ex' : wdOf h' hl' ι (resTo L r) = WD.mk (ResEx.resRep h h' aK) :=
    (IsWDOf.wdOf_eq hl' ⟨_, ht', _, deg_frob, c • N, aL2, hN', haL2, rfl⟩).trans (WD.sound (i2.symm.trans i1))
  refine ⟨a, aK, ResEx.resRep h h' aK, ex.symm, ex'.symm, rfl, fun σ σ' hs => ?_⟩
  show aK.ρ (ResEx.resW h h' σ') = aK.ρ σ
  congr 1
  exact Subtype.ext (AlgEquiv.ext fun z => (hs z).symm)

end GlobalTheory.AboveL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapNormEqOfMapPowEq
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem eig_pow_of_rep {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v} (x : WD h) (σ : Weil h) (k : ℕ) :
    x.eig (σ ^ k) = (x.eig σ).map (· ^ k) := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  rw [WD.eig_mk, WD.eig_mk, map_pow]
  have h2 := GlobalTheory.CharpolyPow.roots_charpoly_pow ℂ n k
    (LinearMap.toMatrix (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n)) (a.ρ σ))
  rw [LinearMap.toMatrix_pow, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix] at h2
  exact h2

end GlobalTheory.AboveL

namespace GlobalTheory.AboveL

open Pointwise

end GlobalTheory.AboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemWeilGroupAtPlaceOfFixesExtension
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.WeilUp

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω]
  [Algebra K L] [IsScalarTower K L Ω] {A : ValuationSubring Ω}

theorem modEq_of_cong {v' : HeightOneSpectrum (𝓞 L)} (h' : IsPlaceOver A v') {Q a b : ℕ}
    (hc : ∀ ζ : 𝓞 L, A.valuation ((algebraMap L Ω (ζ : L)) ^ (Q ^ b) - (algebraMap L Ω (ζ : L)) ^ (Q ^ a)) < 1) :
    Q ^ a ≡ Q ^ b [MOD normV v' - 1] := by
  haveI := v'.isMaximal
  letI : Field (𝓞 L ⧸ v'.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 L ⧸ v'.asIdeal) := v'.asIdeal.finiteQuotientOfFreeOfNeBot v'.ne_bot
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (𝓞 L ⧸ v'.asIdeal)ˣ)
  have hord : orderOf u = normV v' - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units]; rfl
  rw [← hord, ← pow_eq_pow_iff_modEq]
  obtain ⟨ζ, hζ⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 L ⧸ v'.asIdeal)
  have hmem : ζ ^ (Q ^ b) - ζ ^ (Q ^ a) ∈ v'.asIdeal := by
    rw [← h']
    have e : algebraMap L Ω (((ζ ^ (Q ^ b) - ζ ^ (Q ^ a) : 𝓞 L)) : L) =
        (algebraMap L Ω (ζ : L)) ^ (Q ^ b) - (algebraMap L Ω (ζ : L)) ^ (Q ^ a) := by
      push_cast; simp [map_sub, map_pow]
    rw [e]; exact hc ζ
  have h0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  rw [map_sub, map_pow, map_pow, hζ, sub_eq_zero] at h0
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val]
  exact h0.symm

theorem dvd_of_modEq {q f n : ℕ} (hq : 1 < q) (h : q ^ n ≡ 1 [MOD q ^ f - 1]) : f ∣ n := by
  have h1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
  have hd : q ^ f - 1 ∣ q ^ n - 1 := (Nat.modEq_iff_dvd' h1).mp h.symm
  have hg := Nat.pow_sub_one_gcd_pow_sub_one q f n
  rw [Nat.gcd_eq_left hd] at hg
  have h2 : 1 ≤ q ^ f := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ q ^ (f.gcd n) := Nat.one_le_pow _ _ (by omega)
  have h4 : q ^ f = q ^ (f.gcd n) := by omega
  have h5 := Nat.pow_right_injective (Nat.succ_le_of_lt hq) h4
  rw [h5]; exact Nat.gcd_dvd_right f n

theorem actsAs_of_agree {q f a b : ℕ} {σ : G K Ω} {g : G L Ω} (hg : ∀ z : Ω, σ z = g z)
    (hσ : ActsAs A q σ (f * a) (f * b)) : ActsAs A (q ^ f) g a b := by
  have e : σ = (g.restrictScalars K : G K Ω) := AlgEquiv.ext hg
  subst e
  refine ⟨hσ.1, fun x hx => ?_⟩
  have := hσ.2 x hx
  rw [pow_mul, pow_mul] at this
  exact this

end GlobalTheory.AboveL.WeilUp

namespace GlobalTheory.AboveL


open GlobalTheory.AboveL.WeilUp in
theorem mem_weil_of_fix : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ : Weil h) (g : G L Ω), (∀ z : Ω, (σ : G K Ω) z = g z) → g ∈ Weil h' := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' σ g hg
  obtain ⟨f, hf⟩ := normV_eq_pow v v' (comap_eq_of_placeOver h h')
  have hq : 1 < normV v := one_lt_normV v

  have hcong : ∀ a b : ℕ, ActsAs A (normV v) (σ : G K Ω) a b →
      normV v ^ a ≡ normV v ^ b [MOD normV v ^ f - 1] := by
    intro a b hab
    rw [← hf]
    refine modEq_of_cong h' fun ζ => ?_
    have hfix : (σ : G K Ω) (algebraMap L Ω (ζ : L)) = algebraMap L Ω (ζ : L) := by
      rw [hg]; exact g.commutes _
    have hint : A.valuation (algebraMap L Ω (ζ : L)) ≤ 1 := by
      rw [A.valuation_le_one_iff]
      exact mem_of_isIntegral_int A (ζ.2.algebraMap)
    have := hab.2 _ hint
    rwa [hfix] at this
  set d := deg σ with hd
  rcases le_total 0 d with hd0 | hd0
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hd0
    have hact := actsAs_of_deg (σ := σ) (a := n) (b := 0) (by rw [← hd, hn]; simp)
    have hdiv : f ∣ n := dvd_of_modEq hq (by simpa using hcong _ _ hact)
    obtain ⟨k, rfl⟩ := hdiv
    have hact' := actsAs_of_deg (σ := σ) (a := f * k) (b := f * 0) (by rw [← hd, hn]; simp)
    exact (mem_Weil h').mpr ⟨k, 0, hf ▸ actsAs_of_agree hg hact'⟩
  · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hd0
    have hact := actsAs_of_deg (σ := σ) (a := 0) (b := n) (by rw [← hd, hn]; simp)
    have hdiv : f ∣ n := dvd_of_modEq hq (by simpa using (hcong _ _ hact).symm)
    obtain ⟨k, rfl⟩ := hdiv
    have hact' := actsAs_of_deg (σ := σ) (a := f * 0) (b := f * k) (by rw [← hd, hn]; simp)
    exact (mem_Weil h').mpr ⟨0, k, hf ▸ actsAs_of_agree hg hact'⟩

end GlobalTheory.AboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastEqZeroOfDvdCard
section
namespace GlobalTheory.NormDivisibility

open NumberField IsDedekindDomain

theorem natCast_eq_zero_of_dvd_card {R : Type*} [CommRing R] [IsDomain R] [Finite R] {l : ℕ}
    (hl : l.Prime) (h : l ∣ Nat.card R) : (l : R) = 0 := by
  classical
  have := Fintype.ofFinite R
  let _ : Field R := Fintype.fieldOfDomain R

  obtain ⟨n, hp, hc⟩ := FiniteField.card R (ringChar R)
  rw [Nat.card_eq_fintype_card, hc] at h
  rw [(Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow h)]
  exact ringChar.Nat.cast_ringChar

theorem not_dvd_norm_of_not_mem {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : Nat.Prime l)
    (w : HeightOneSpectrum (RingOfIntegers E))
    (hw : (l : RingOfIntegers E) ∉ w.asIdeal) : ¬ l ∣ Formalism.ConjugateSelfDual.normV w := by
  intro h
  have : Finite (RingOfIntegers E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  unfold Formalism.ConjugateSelfDual.normV at h
  have h0 := natCast_eq_zero_of_dvd_card (R := RingOfIntegers E ⧸ w.asIdeal) hl h
  apply hw
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h0

end GlobalTheory.NormDivisibility
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadLift
section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.Published

namespace GlobalTheory.QuadLiftBridge

theorem quadLift : ArthurClozelStrongTC → JacquetShalikaRigidity → GlobalTheory.GalCut.QuadLift := by
  intro hAC hJS K M _ _ _ _ _ _ _ h2 a ha π ⟨w, hw, B, hB⟩
  haveI : Algebra.IsQuadraticExtension K M := ⟨h2⟩
  haveI : IsGalois K M := inferInstance
  refine hAC K M (h2 ▸ Nat.prime_two) a ha π fun η hη hST => ?_
  have hsm : CG.mk π = (CG.mk π).twist η := by
    refine JacquetShalikaRigidity.strong_multiplicity_one hJS ha _ _ (hST.mono fun v ⟨hu, B', h1, h3⟩ => ⟨B', h1, ?_⟩)
    have := h1.twist hu
    rwa [h3] at this
  exact _root_.GlobalTheory.TwistRamified.twist_ne K a ha (CG.mk π) η _ B hB (_root_.GlobalTheory.QuadNormRam.not_unrAt_of_ramified K M h2 η hη w hw) hsm.symm

end GlobalTheory.QuadLiftBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnderConjugatePlaceEqConjugatePlaceUnder
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.ConjUnder

theorem complexConj_algebraMap {K M : Type} [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M]
    [Algebra K M] (x : K) :
    IsCMField.complexConj M (algebraMap K M x) = algebraMap K M (IsCMField.complexConj K x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K M)) x).symm

theorem cPl_asIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (UpperTheory.V.Af.Bc.cPl w).asIdeal =
      w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E) :=
  (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)

theorem cPl_under : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M]
    [Algebra K M] (w : HeightOneSpectrum (𝓞 M)),
    (UpperTheory.V.Af.Bc.cPl w).under (𝓞 K) = UpperTheory.V.Af.Bc.cPl (w.under (𝓞 K)) := by
  intro K M _ _ _ _ _ _ _ w
  apply HeightOneSpectrum.ext
  rw [cPl_asIdeal]
  change (UpperTheory.V.Af.Bc.cPl w).asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = (w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M))).comap _
  rw [cPl_asIdeal, Ideal.comap_comap, Ideal.comap_comap]
  congr 1
  ext x
  exact complexConj_algebraMap (x : K)

end GlobalTheory.ConjUnder
end
end

