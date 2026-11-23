module

public import Mathlib
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.LocalLevelIsKOneAtT
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianIntegralVectorsPairing
public import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfCharConjEmbeddingNegOfInvariantPairing
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0157
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasSubstCoordZA
section
noncomputable section

namespace GlobalTheory.TwU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits Classical Formalism.L2.KerInert.Loc

theorem resV_subst_two {ι κ σ τ R : Type} [CommRing R] [Finite ι] [Finite σ]
    {f : κ → ι} (hf : Function.Injective f) {g : τ → σ} (hg : Function.Injective g)
    {a : σ → MvPowerSeries ι R} (ha : MvPowerSeries.HasSubst a)
    {a' : τ → MvPowerSeries κ R} (ha' : MvPowerSeries.HasSubst a')
    (h1 : ∀ k, resV f (a (g k)) = a' k) (h0 : ∀ i, (∀ k, g k ≠ i) → resV f (a i) = 0)
    (T : MvPowerSeries σ R) :
    resV f (MvPowerSeries.subst a T) = MvPowerSeries.subst a' (resV g T) := by
  rw [resV_subst hf ha, resV_eq_subst hg T, MvPowerSeries.subst_comp_subst_apply (hasSubst_resFam g) ha']
  congr 1
  funext i
  by_cases h : ∃ k, g k = i
  · obtain ⟨k, rfl⟩ := h
    rw [h1, resFam_apply hg, MvPowerSeries.subst_X ha']
  · push_neg at h
    rw [h0 i h, resFam_off g i h, ← MvPowerSeries.coe_substAlgHom ha', map_zero]

theorem resV_CX {ι κ R : Type} [CommRing R] [Finite ι] {f : κ → ι} (hf : Function.Injective f) (c : R) (k : κ) :
    resV f (MvPowerSeries.C c * MvPowerSeries.X (f k) : MvPowerSeries ι R) = MvPowerSeries.C c * MvPowerSeries.X k := by
  rw [resV_mul hf, resV_X hf]
  congr 1
  ext n
  rw [resV_coeff, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn, if_neg]
    intro h0
    apply hn
    have := congrArg Finsupp.degree h0
    rw [degree_mapDomain] at this
    exact (Finsupp.degree_eq_zero_iff n).1 (by simpa using this)

theorem resV_CX_off {ι κ R : Type} [CommRing R] [Finite ι] {f : κ → ι} (hf : Function.Injective f) (c : R) (i : ι)
    (hi : ∀ k, f k ≠ i) :
    resV f (MvPowerSeries.C c * MvPowerSeries.X i : MvPowerSeries ι R) = 0 := by
  rw [resV_mul hf, resV_X_off hf i hi, mul_zero]

theorem inj_at {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) :
    Function.Injective (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j)) :=
  fun a b h => eq_of_heq (Sigma.mk.inj_iff.1 h).2

theorem inE_inj {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) : Function.Injective (inE X j v) := by
  have hg : Function.Injective (fun e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, e⟩ : X.EA j)) :=
    fun a b h => eq_of_heq (Sigma.mk.inj_iff.1 h).2
  exact hg.sumMap hg

end GlobalTheory.TwU

namespace GlobalTheory.TwU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits Classical Formalism.L2.KerInert.Loc

theorem hasSubst_coordZA {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) :
    MvPowerSeries.HasSubst (X.coordZA (K0 p) j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by
    rintro (⟨w, r, a, b⟩ | ⟨w, r, a, b⟩) <;> simp [Sys.coordZA])

theorem hasSubst_coordZ {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (B : OmBasis p n') :
    MvPowerSeries.HasSubst (coordZ (r0 := r0) (r1 := r1) B (K0 p) 1) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by
    rintro (⟨r, a, b⟩ | ⟨r, a, b⟩) <;> simp [coordZ])

theorem resV_ThZA {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) (T : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)) :
    resV (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j)) (X.ThZA (K0 p) j T) =
      ThZ (X.om v) (K0 p) 1 (resV (inE X j v) T) := by
  have hE := inE_inj X j v
  have hZ := inj_at X j v
  unfold Sys.ThZA ThZ
  refine resV_subst_two hZ hE (hasSubst_coordZA X j) (hasSubst_coordZ _) ?_ ?_ T
  · rintro (⟨r, a, b⟩ | ⟨r, a, b⟩)
    · show resV _ (X.coordZA (K0 p) j (Sum.inl ⟨v, (r, a, b)⟩)) = _
      simp only [Sys.coordZA, coordZ]
      rw [resV_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [one_mul, Algebra.algebraMap_self, RingHom.id_apply]
      exact resV_CX hZ _ (s, a, b)
    · show resV _ (X.coordZA (K0 p) j (Sum.inr ⟨v, (r, a, b)⟩)) = _
      simp only [Sys.coordZA, coordZ]
      rw [resV_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [one_mul, Algebra.algebraMap_self, RingHom.id_apply]
      exact resV_CX hZ _ (s, a, b)
  · rintro (⟨w, r, a, b⟩ | ⟨w, r, a, b⟩) hi
    · have hw : w ≠ v := by
        rintro rfl
        exact hi (Sum.inl (r, a, b)) rfl
      simp only [Sys.coordZA]
      rw [resV_sum]
      refine Finset.sum_eq_zero fun s _ => ?_
      exact resV_CX_off hZ _ _ (fun z h => hw (congrArg Sigma.fst h).symm)
    · have hw : w ≠ v := by
        rintro rfl
        exact hi (Sum.inr (r, a, b)) rfl
      simp only [Sys.coordZA]
      rw [resV_sum]
      refine Finset.sum_eq_zero fun s _ => ?_
      exact resV_CX_off hZ _ _ (fun z h => hw (congrArg Sigma.fst h).symm)

theorem resV_phAt {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl) :
    resV (inE X j v) (phAt X be j v) =
      ∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
        sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) := by
  have hE := inE_inj X j v
  unfold phAt
  rw [resV_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [restrict_formalSum hE be (by simp) (by simp)]
  exact congrArg₂ (sub2 p be) (resV_X hE (Sum.inl e)) (resV_X hE (Sum.inr e))

theorem restr_onePlace : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl)
    (U : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)), MvPowerSeries.constantCoeff be = 0 → IntS p (inParam p U) →
    IntS p (inParam p (resV (inE X j v) U)) ∧
      resV (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j))
        (X.ThZA (K0 p) j (expS p (-phAt X be j v) * U)) = thOne (X.om v) be (resV (inE X j v) U) := by
  intro p _ X be j v U _ hU
  have hE := inE_inj X j v
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hg⟩ := hU
    exact ⟨resV (inE X j v) g, by rw [← resV_inParam hE, hg, resV_map]⟩
  · rw [resV_ThZA, resV_mul hE, resV_expS hE, resV_neg, resV_phAt]
    rfl

end GlobalTheory.TwU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWittUnitaryModUniformizer
section
open Matrix

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem witt_mod_base : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L), (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  intro L _ _ _ ϖ σ q hU hq n' JT hJ hJh ι _ z z' hz hz' hi hi' hgr
  classical
  obtain ⟨g₀, hg₀i, hg₀u, hg₀z⟩ := _root_.GlobalTheory.Hk3.ResWitt.exists_int_unitary_mod_of_gram_mod L ϖ σ q hU hq n' JT hJ hJh ι z z' hz hz' hi hi' hgr
  have hstep := _root_.GlobalTheory.Hk3.UnitaryNewton.newton_step L ϖ σ q hU hq n' JT hJ hJh
  obtain ⟨hσσ, hσv, hσϖ, hϖv, -, -, -⟩ := hU
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hJi : ∀ i j, J i j ∈ intL L := by
    obtain ⟨k0, hk0⟩ := hJ
    intro i j; rw [hJdef, ← hk0]; exact ((k0 : Matrix (Fin n') (Fin n') (intL L)) i j).2

  let P : ℕ → Matrix (Fin n') (Fin n') L → Prop := fun k g =>
    (∀ i j, g i j ∈ intL L) ∧ ∀ i j, DvdPow ϖ (k + 1) ((cT σ g * J * g - J) i j)
  have hex : ∀ (k : ℕ) (g : Matrix (Fin n') (Fin n') L), ∃ g' : Matrix (Fin n') (Fin n') L,
      P k g → P (k + 1) g' ∧ ∀ i j, DvdPow ϖ (k + 1) (g' i j - g i j) := by
    intro k g
    by_cases hP : P k g
    · obtain ⟨g', h1, h2, h3⟩ := hstep k g hP.1 hP.2
      exact ⟨g', fun _ => ⟨⟨h1, h3⟩, h2⟩⟩
    · exact ⟨g, fun h => absurd h hP⟩
  choose F hF using hex
  let f : ℕ → Matrix (Fin n') (Fin n') L := fun k => Nat.rec g₀ (fun k g => F k g) k
  have hf0 : f 0 = g₀ := rfl
  have hfs : ∀ k, f (k + 1) = F k (f k) := fun k => rfl
  have hfP : ∀ k, P k (f k) := by
    intro k
    induction k with
    | zero => exact ⟨hg₀i, hg₀u⟩
    | succ k ih => rw [hfs]; exact (hF k (f k) ih).1
  have hclose : ∀ k i j, DvdPow ϖ (k + 1) (f (k + 1) i j - f k i j) := by
    intro k i j; rw [hfs]; exact (hF k (f k) (hfP k)).2 i j

  have hlim := fun i j => GlobalTheory.T.exists_limit_dvdUniformizerPow_cauchy L ϖ hϖv (fun k => f k i j) (fun k => hclose k i j)
  choose b hb using hlim
  let h : Matrix (Fin n') (Fin n') L := Matrix.of b
  have hhk : ∀ k i j, DvdPow ϖ (k + 1) ((h - f k) i j) := fun k i j => hb i j k
  have hϖi : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖv]; exact WithZero.exp_le_exp.2 (by norm_num : (-1 : ℤ) ≤ 0)
  have hhi : ∀ i j, h i j ∈ intL L := by
    intro i j
    have e : h i j = (h - f 0) i j + f 0 i j := by simp
    rw [e]
    exact add_mem (dvdPow_zero_iff.1 (dvdPow_mono hϖi (Nat.zero_le 1) (hhk 0 i j))) ((hfP 0).1 i j)
  have hunit : cT σ h * J * h = J := by
    ext i j
    have hz0 : (cT σ h * J * h - J) i j = 0 := by
      refine eq_zero_of_forall_dvdPow hϖv fun k => ?_
      have e : cT σ h * J * h - J = (cT σ (h - f k) * J * h + cT σ (f k) * J * (h - f k)) +
          (cT σ (f k) * J * f k - J) := by
        rw [cT_sub]; simp only [sub_mul, mul_sub, Matrix.mul_assoc]; abel
      rw [e, Matrix.add_apply, Matrix.add_apply]
      refine dvdPow_add (dvdPow_add ?_ ?_) ((hfP k).2 i j)
      · exact mc_mul_right (mc_mul_right (mc_cT hσv hσϖ (hhk k)) hJi) hhi i j
      · rw [Matrix.mul_assoc]
        exact mc_mul_left (int_cT hσv (hfP k).1) (mc_mul_left hJi (hhk k)) i j
    rw [Matrix.sub_apply] at hz0
    exact sub_eq_zero.1 hz0

  set Ji : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJidef
  have hJiJ : Ji * J = 1 := by rw [hJidef, hJdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hleft : (Ji * cT σ h * J) * h = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ h), hunit, hJiJ]
  have hright : h * (Ji * cT σ h * J) = 1 := mul_eq_one_comm.1 hleft
  let hG : GL (Fin n') L := ⟨h, Ji * cT σ h * J, hright, hleft⟩
  have hmem : hG ∈ UJ σ J := hunit
  refine ⟨⟨hG, hmem⟩, GlobalTheory.UnitarySwap.mem_GLint_of_unitary hσv hJ hmem hhi, fun i r => ?_⟩
  show DvdPow ϖ 1 ((h *ᵥ z i) r - z' i r)
  have e : (h *ᵥ z i) r - z' i r = ((h - g₀) *ᵥ z i) r + ((g₀ *ᵥ z i) r - z' i r) := by
    simp [Matrix.sub_mulVec]
  rw [e]
  refine dvdPow_add ?_ (hg₀z i r)
  simp only [Matrix.mulVec, dotProduct]
  refine dvdPow_sum _ _ fun s _ => ?_
  rw [mul_comm]
  exact dvdPow_mul_int (hhk 0 r s) (hz i s)

end GlobalTheory.Hk3.IntWittBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InverseSeriesFormalGroupIsoIntegral
section
noncomputable section

namespace GlobalTheory.InverseSeriesIntegral

open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (wToC LTIso)
open Formalism.InvariantFactorPaths.G7 (lgF)
open Formalism.L2.KerInert.BeCob (vLT eLT)
open GlobalTheory.CurveDictionary (cc_lgF' lgF_eq_logF)

theorem exists_witt_series_inverse_formalGroup_iso {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) :
    ∃ w : PowerSeries (Formalism.MainNotions.FormalGroupSystem.WW l), PowerSeries.map (wToC l) w = vLT hLT := by
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set th0 := Formalism.L2.G.Pend.thOf hLT with hth0
  have h00 : PowerSeries.constantCoeff th0 = 0 := Formalism.L2.G.Pend.thOf_zero hLT
  have hu : IsUnit (PowerSeries.coeff 1 th0) := Formalism.L2.G.Pend.thOf_unit hLT
  set i0 := th0.substInvOfIsUnit hu with hi0
  have hi00 : PowerSeries.constantCoeff i0 = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hR : PowerSeries.subst i0 th0 = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_right _ h00 hu
  set thC := PowerSeries.map (wToC l) th0 with hthC
  set iC := PowerSeries.map (wToC l) i0 with hiC
  have hthC0 : PowerSeries.constantCoeff thC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hthC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h00, map_zero]
  have hiC0 : PowerSeries.constantCoeff iC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hiC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hi00, map_zero]
  have hRC : PowerSeries.subst iC thC = PowerSeries.X := by
    have h := congrArg (MvPowerSeries.map (wToC l)) hR
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hi00)] at h
    exact h.trans (MvPowerSeries.map_X _ _)
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hlog : PowerSeries.subst thC (lgF ℂ_[l] l) = PowerSeries.C e * g.l := by
    have h := Formalism.L2.G.Pend.thOf_log hLT
    rw [lgF_eq_logF] at h
    exact h
  have hVT : PowerSeries.subst thC (vLT hLT) = PowerSeries.X := by
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hv0)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0),
      PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0), PowerSeries.subst_C, hlog]
    have e1 : (MvPowerSeries.C e⁻¹ : PowerSeries ℂ_[l]) * (PowerSeries.C e * g.l) = g.l := by
      rw [← mul_assoc]
      show PowerSeries.C e⁻¹ * PowerSeries.C e * g.l = g.l
      rw [← map_mul, inv_mul_cancel₀ hene, map_one, one_mul]
    rw [e1]
    exact Formalism.L2.G.Pend.ex_l g hex hinv
  refine ⟨i0, ?_⟩
  show iC = vLT hLT
  symm
  calc vLT hLT = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[l]) (vLT hLT) := (PowerSeries.X_subst _).symm
    _ = PowerSeries.subst (PowerSeries.subst iC thC) (vLT hLT) := by rw [hRC]
    _ = PowerSeries.subst iC (PowerSeries.subst thC (vLT hLT)) :=
        (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0) _).symm
    _ = PowerSeries.subst iC (PowerSeries.X : PowerSeries ℂ_[l]) := by rw [hVT]
    _ = iC := PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0)

theorem v_integral : ∀ (l : ℕ) [Fact l.Prime] (g : G1 l), g.Ok → ∀ (hLT : LTIso g) (n : ℕ),
    ‖PowerSeries.coeff n (vLT hLT)‖ ≤ 1 := by
  intro l _ g hOk hLT n
  obtain ⟨w, hw⟩ := exists_witt_series_inverse_formalGroup_iso hOk hLT
  rw [← hw, PowerSeries.coeff_map]
  have := Formalism.L2.G.Pend.norm_wToC_pow_mul l 0 (PowerSeries.coeff n w)
  simpa using this

end GlobalTheory.InverseSeriesIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedP
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.RegAlgCharAlg

theorem expo_mul' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ χ' : HChar E) (τ : E →+* ℂ) :
    expo (χ * χ') τ = expo χ τ + expo χ' τ := by
  have h := (CG.hasInfChar_ofChar χ τ).twist χ'
  rw [CG.twist_ofChar, Multiset.map_singleton] at h
  have := h.infChar_eq
  rw [CG.infChar_ofChar] at this
  simpa using this

theorem expo_inv' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E) (τ : E →+* ℂ) :
    expo χ⁻¹ τ = -expo χ τ := by
  have := expo_mul' χ χ⁻¹ τ
  rw [mul_inv_cancel, CG.expo_one] at this
  linear_combination -this

theorem isAlgPos_of_polarizedPair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → PolarizedPair π χ →
      ∃ n : (maximalRealSubfield E →+* ℂ) → ℤ, IsAlgPos χ n := by
  intro E _ _ _ a ha π χ hreg hpol
  refine _root_.GlobalTheory.CMRealAlg.isAlgPos_of_compNorm E χ fun τ => ?_
  have hcomm : ∀ (τ : E →+* ℂ) (u : ℂ) (o : Op E a), Commute (cap (a := a) τ u) (act o) := fun τ u o => by
    cases o with
    | fin k => exact commute_cap_finRep τ u k
    | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
    | lie X => exact commute_cap_lie τ u X
  have hm : ∀ σ, π.HasInfChar σ ((CG.mk π).infChar σ) := fun σ =>
    GlobalTheory.CuspRep.hasInfChar_infChar_of_commute E a hcomm (CG.mk π) σ
  set ψ := GlobalTheory.GalOfCusp.compNorm E χ
  have h1 := (hm τ).twist ψ⁻¹
  have key := _root_.GlobalTheory.CapPair.infChar_conj_of_paired E a (π.twist ψ⁻¹) π hpol.dual τ _ _ h1 (hm (NumberField.ComplexEmbedding.conjugate τ))
  obtain ⟨z, hz⟩ : ∃ z, z ∈ (CG.mk π).infChar τ :=
    Multiset.card_pos_iff_exists_mem.1 (by rw [(hm τ).1]; omega)
  obtain ⟨n, hn⟩ := (hreg τ).2 z hz
  have hz' : -(z + expo ψ⁻¹ τ) ∈ (CG.mk π).infChar (NumberField.ComplexEmbedding.conjugate τ) := by
    rw [key, Multiset.map_map]
    exact Multiset.mem_map.2 ⟨z, hz, rfl⟩
  obtain ⟨n', hn'⟩ := (hreg _).2 _ hz'
  refine ⟨n + n' + ((a : ℤ) - 1), ?_⟩
  rw [expo_inv'] at hn'
  push_cast
  linear_combination hn' + hn

end GlobalTheory.RegAlgCharAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatchedSphericalPairsCommuteCompositeLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.SysE


set_option maxHeartbeats 1000000 in
theorem matched_commute : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ SF, IsSF R SF → ∀ t P, Good R t P → ∀ cX c0, MatchE R t P cX c0 → ∀ hX, IsOpsX R t hX → (∀ h, IsOpsE R h → ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y)) ∧ ∀ c, ∀ w ∈ EEc R SF c, hX P cX (LinearMap.adjoint (R.Th t) w) = evC (Yc D 0) P (fun d => c P (dualLab d)) c0 • LinearMap.adjoint (R.Th t) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS SF hSF t P hg cX c0 hM hX hXo
  have gd := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hg0 : Good R A.μ0 P := (gd.2.1 t P hg).2.2
  have injE : Function.Injective R.HE.e := hC.models.HE.1
  have injX : Function.Injective (R.HX t).e := (hC.models.HX t).1

  have part1 : ∀ h, IsOpsE R h → ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y) := by
    intro h hh y
    apply injE
    exact (hM y (hX P cX y) (hXo P hg cX y)).trans (hh P hg0 c0 (R.Th t y)).symm
  refine ⟨part1, ?_⟩
  intro c w hw
  have h01 := _root_.GlobalTheory.Hk3.OpsRows.exists_opsE R F hC hS SF hSF
  rcases h01 with ⟨h0, h0o, h0n, -, h0e, -⟩
  have hX01 := (GlobalTheory.T.realization_family_normal_operators R F hC.lev hC.fam hC.models).1 t
  rcases hX01 with ⟨hX0, hX0o, hX0n⟩
  have eqX : hX P cX = hX0 P cX := by
    ext x
    apply injX
    exact (hXo P hg cX x).trans (hX0o P hg cX x).symm
  have eX : LinearMap.adjoint (hX0 P cX) = hX0 P (dualC (Finsupp.mapRange star (star_zero ℂ) cX)) := hX0n.2 P hg cX
  have cX' : Commute (hX0 P cX) (hX0 P (dualC (Finsupp.mapRange star (star_zero ℂ) cX))) := hX0n.1 P P hg hg _ _
  have nX0 : Commute (hX0 P cX) (LinearMap.adjoint (hX0 P cX)) :=
    @Eq.subst (Module.End ℂ (R.HX t).H) (fun B => Commute (hX0 P cX) B) _ _ eX.symm cX'
  have nX : Commute (hX P cX) (LinearMap.adjoint (hX P cX)) :=
    @Eq.subst (Module.End ℂ (R.HX t).H) (fun B => Commute B (LinearMap.adjoint B)) _ _ eqX.symm nX0
  have eE : LinearMap.adjoint (h0 P c0) = h0 P (dualC (Finsupp.mapRange star (star_zero ℂ) c0)) := h0n.2 P hg0 c0
  have cE : Commute (h0 P c0) (h0 P (dualC (Finsupp.mapRange star (star_zero ℂ) c0))) := h0n.1 P P hg0 hg0 _ _
  have nE : Commute (h0 P c0) (LinearMap.adjoint (h0 P c0)) :=
    @Eq.subst (Module.End ℂ R.HE.H) (fun B => Commute (h0 P c0) B) _ _ eE.symm cE
  exact _root_.GlobalTheory.HkUp.eigen_up_along_adjoint (R.Th t) (fun _ : Unit => hX P cX) (fun _ : Unit => h0 P c0)
    (fun _ u => part1 h0 h0o u) (fun _ => nX) (fun _ => nE) () _ w (h0e c P hg0 c0 w hw)

end GlobalTheory.Hk3.SysE
end

