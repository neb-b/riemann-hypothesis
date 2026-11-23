module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
public import Formalism.SharpRestriction.LevelLetterCocycles.RingHypothesesOfCrystalline
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0785
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0753
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0626
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjLMemWeil
section
open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.FunExt

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FunExt.ConjLift

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω]

theorem mem_Dec_of_iff {F : Type} [Field F] [NumberField F] [Algebra F Ω] {A : ValuationSubring Ω} {σ : G F Ω}
    (hσ : ∀ x, σ x ∈ A ↔ x ∈ A) : σ ∈ Dec (F := F) A := by
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hσ]
  show (σ * σ⁻¹) x ∈ A ↔ x ∈ A
  rw [mul_inv_cancel]; rfl

variable (s : L ≃ₐ[K] L) (g : G K Ω) (hgs : ∀ x : L, g (algebraMap L Ω x) = algebraMap L Ω (s x))
include hgs


variable {A : ValuationSubring Ω}

omit hgs

end GlobalTheory.FunExt.ConjLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenvalueProductMapsLetterLatticeOfConclusionsA
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

noncomputable section

namespace GlobalTheory.PrimeSequence

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

theorem qp_isUnit (hR9 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.R9 W T) :
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) := by
  obtain ⟨wq, hwq⟩ := hR9.qq
  have h1 : IsUnit (algebraMap (LetA O n) W.EE (W.φA letπ)) := by
    have := W.EE_π.map W.φE
    rw [W.φE_ext] at this
    exact this
  rw [W.φA_π, map_mul] at h1
  have h2 := (IsUnit.mul_iff.1 h1).2
  rw [hwq, map_mul] at h2
  exact (IsUnit.mul_iff.1 h2).2

theorem qp_pow_inj (hR9 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.R9 W T) (k : ℕ) {x : W.DD T}
    (h : Formalism.MainNotions.LiftingTheory.qp W ^ k • x = 0) : x = 0 := by
  have hu := (qp_isUnit W hR9).pow k
  rw [← map_pow] at hu
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ k) x] at h
  exact hu.smul_left_cancel.1 (h.trans (smul_zero _).symm)

theorem dl_of_qp (hR9 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.R9 W T) {i : ZMod n} {y : ℕ} {z : W.DD T}
    (h : Formalism.MainNotions.LiftingTheory.InNΔi W T i (Formalism.MainNotions.LiftingTheory.qp W ^ y • z)) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z ∧ Formalism.MainNotions.LiftingTheory.qp W ^ y • z ∈ W.N T := by
  obtain ⟨hNΔ, hl⟩ := h
  have hN : Formalism.MainNotions.LiftingTheory.qp W ^ y • z ∈ W.N T := hNΔ.1
  have hΔ : ∀ δ ∈ W.DelF, W.γD T δ (Formalism.MainNotions.LiftingTheory.qp W ^ y • z) = Formalism.MainNotions.LiftingTheory.qp W ^ y • z := hNΔ.2
  obtain ⟨m, -, hme⟩ := Submodule.mem_map.1 hl
  refine ⟨⟨?_, fun δ hδ => ?_⟩, hN⟩
  · refine sub_eq_zero.1 (qp_pow_inj W hR9 y ?_)
    rw [smul_sub, smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ y) (letE i : LetA O n) z, ← hme]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, Formalism.MainNotions.WachCoordinates.Br.letE_mul_self, sub_self]
  · refine sub_eq_zero.1 (qp_pow_inj W hR9 y ?_)
    have hq : W.γA δ (Formalism.MainNotions.LiftingTheory.qp W ^ y) = Formalism.MainNotions.LiftingTheory.qp W ^ y :=
      (W.AΔ.pow_mem (Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.qp_mem hR9) y) δ hδ
    have e : Formalism.MainNotions.LiftingTheory.qp W ^ y • W.γD T δ z = W.γD T δ (Formalism.MainNotions.LiftingTheory.qp W ^ y • z) := by
      rw [Formalism.MainNotions.WachCoordinates.Br.γD_smulA, hq]
    rw [smul_sub, e, hΔ δ hδ, sub_self]

end GlobalTheory.PrimeSequence

namespace GlobalTheory.PrimeSequence

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

def pseq (dop : W.DD T →ₗ[O] W.DD T) (cc : ℤ → O) (xs : List ℤ) (z : W.DD T) (k : ℕ) : W.DD T :=
  Polynomial.aeval dop (((xs.take k).map fun x => Polynomial.X - Polynomial.C (cc x)).prod) z

theorem pseq_zero (dop : W.DD T →ₗ[O] W.DD T) (cc : ℤ → O) (xs : List ℤ) (z : W.DD T) :
    pseq W dop cc xs z 0 = z := by
  simp [pseq]

theorem pseq_succ (dop : W.DD T →ₗ[O] W.DD T) (cc : ℤ → O) (xs : List ℤ) (z : W.DD T) (k : ℕ)
    (hk : k < xs.length) :
    pseq W dop cc xs z (k + 1) = dop (pseq W dop cc xs z k) - cc (xs.getD k 0) • pseq W dop cc xs z k := by
  have ht : xs.take (k + 1) = xs.take k ++ [xs.getD k 0] := by
    rw [List.take_succ, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
    rfl
  unfold pseq
  rw [ht, List.map_append, List.prod_append, mul_comm, map_mul, Module.End.mul_apply]
  simp [Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]

theorem pseq_length (dop : W.DD T →ₗ[O] W.DD T) (cc : ℤ → O) (X : Finset ℤ) (z : W.DD T) :
    pseq W dop cc X.toList z X.toList.length =
      Polynomial.aeval dop (∏ x ∈ X, (Polynomial.X - Polynomial.C (cc x))) z := by
  unfold pseq
  rw [List.take_length, Finset.prod_map_toList]

end GlobalTheory.PrimeSequence

namespace GlobalTheory.PrimeSequence

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {T : LocLat G Qp LL O}

theorem eigenvalue_product_maps_letter_lattice_local (l : ℕ) (hpl : PD.p = l)
    (hR9 : Formalism.MainNotions.LiftingTheory.CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.R9 W T)
    (hdss : Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (y' Y : ℕ)
      (cO : ℤ → O), (∀ x : ℤ, ((l : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O)) →
      ∀ xs : List ℤ, (∀ (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i →
        IsJumpV PD T.ρ τ a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) →
      ∀ seq : ℕ → W.DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (seq 0) → Formalism.MainNotions.LiftingTheory.qp W ^ Y • seq 0 ∈ W.N T →
      (∀ k < xs.length, W.π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) =
        W.γD T W.gam (seq k) - seq k) →
      Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (seq xs.length) ∧ Formalism.MainNotions.LiftingTheory.qp W ^ y' • seq xs.length ∈ W.N T) :
    Formalism.MainNotions.N.LetterConditionLocal W := by
  intro hCA T hT i y _ dop hdop cc hcc X hX z hz
  obtain ⟨hDL, hzN⟩ := dl_of_qp W (hR9 hCA T hT) hz
  have hcc' : ∀ x : ℤ, ((l : ℕ) : O) * cc x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) := by
    intro x
    have e := hcc x
    rw [hpl] at e
    linear_combination -e
  have hj : ∀ (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i →
      IsJumpV PD T.ρ τ a → 0 < j → j ≤ y → a + (j : ℤ) ∈ X.toList :=
    fun τ a j ho hja h1 h2 => Finset.mem_toList.2 (hX τ a j ho hja h1 h2)
  have hrec : ∀ k < X.toList.length, W.π₀ • (pseq W dop cc X.toList z (k + 1) +
      cc (X.toList.getD k 0) • pseq W dop cc X.toList z k) =
      W.γD T W.gam (pseq W dop cc X.toList z k) - pseq W dop cc X.toList z k := by
    intro k hk
    rw [pseq_succ W dop cc X.toList z k hk, sub_add_cancel]
    exact hdop _
  have key := hdss hCA T hT i 0 y cc hcc' X.toList hj (pseq W dop cc X.toList z)
    (by rw [pseq_zero]; exact hDL) (by rw [pseq_zero]; exact hzN) hrec
  rw [pseq_length] at key
  obtain ⟨hD, hNl⟩ := key
  rw [pow_zero, one_smul] at hNl
  refine ⟨⟨hNl, hD.2⟩, Submodule.mem_map.2 ⟨_, hNl, ?_⟩⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  exact hD.1

end GlobalTheory.PrimeSequence

namespace GlobalTheory.PrimeSequence

open Formalism.BasicNotions.Loc

theorem eigenvalue_product_maps_letter_lattice_of_conclusions : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → Formalism.MainNotions.N.LetterConditionGlobal D HW F := by
  intro D HW F Cm hN l _ K s LL h hCA
  have hs : s = 1 := by rw [← (HW l).W_s K s LL h]; exact hCA.2.1
  subst hs
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := by
    refine ⟨fun x hx => ?_, by rw [← hpl]; exact hCA.2.2, h⟩
    obtain ⟨w, hw⟩ := hCA.1.2 ⟨x, hx⟩
    have h2 := w.2.2
    have : ((w : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hw
    rw [this] at h2
    exact h2
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL h) := hN.2.2.2.2.2.2.2.2.1 l K 1 LL h
  exact eigenvalue_product_maps_letter_lattice_local _ l hpl (fun hA T hT => Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.ring_hypotheses_of_crystalline _ hA h9 T hT)
    (fun _ => GlobalTheory.T.wachOperatorProduct_shift_mem_lattice D HW F Cm hN l K LL hCAl) hCA

end GlobalTheory.PrimeSequence
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfNotAntitoneInt
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WhitTorus

theorem eq_zero_of_not_antitone_int (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (ψ : AddChar (w.adicCompletion E) ℂ)
    (hψ : ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w)
    (W : GL (Fin n) (w.adicCompletion E) → ℂ)
    (hWN : ∀ u ∈ unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (superDiag u) * W g)
    (hWK : ∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (l : Fin n → ℤ) (hl : ¬ Antitone l)
    (D : GL (Fin n) (w.adicCompletion E))
    (hDv : (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.diagonal fun a => ((ϖ ^ l a : (w.adicCompletion E)ˣ) : w.adicCompletion E)) :
    W D = 0 := by
  obtain ⟨i, j, hij, hlt⟩ : ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ l i < l j := by
    by_contra h
    push_neg at h
    apply hl
    cases n with
    | zero => exact fun a => a.elim0
    | succ m =>
      rw [Fin.antitone_iff_succ_le]
      intro k
      exact h k.castSucc k.succ (by simp)
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hlt' : i < j := Fin.lt_def.2 (by omega)
  have hnot : ((ϖ : w.adicCompletion E))⁻¹ ∉ Ov E w := by
    intro h
    change Valued.v (((ϖ : w.adicCompletion E))⁻¹) ≤ 1 at h
    rw [map_inv₀, hϖ, ← WithZero.coe_inv, ← WithZero.coe_one, WithZero.coe_le_coe] at h
    exact absurd (Multiplicative.ofAdd_le.1 (h.trans_eq (ofAdd_zero).symm)) (by norm_num)
  obtain ⟨y, hy, hψy⟩ : ∃ y ∈ Ov E w, ψ (((ϖ : w.adicCompletion E))⁻¹ * y) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hnot ((hψ _).1 h)
  set x : w.adicCompletion E := ((ϖ : w.adicCompletion E))⁻¹ * y with hx
  have hϖ0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  set m : ℕ := (l j - l i).toNat with hm
  have hlj : l j = l i + (m : ℤ) := by omega
  have hm1 : 1 ≤ m := by omega
  have hdj : ((ϖ ^ l j : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      ((ϖ ^ l i : (w.adicCompletion E)ˣ) : w.adicCompletion E) * (ϖ : w.adicCompletion E) ^ m := by
    rw [hlj, _root_.zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
  set c : w.adicCompletion E := (ϖ : w.adicCompletion E) ^ m * x with hc
  have hcO : c ∈ Ov E w := by
    have hϖO : (ϖ : w.adicCompletion E) ∈ Ov E w := mem_Ov_of_isUnifV hϖ
    have : c = (ϖ : w.adicCompletion E) ^ (m - 1) * y := by
      rw [hc, hx, ← mul_assoc, show m = (m - 1) + 1 by omega, pow_succ, mul_assoc _ (ϖ : w.adicCompletion E),
        mul_inv_cancel₀ hϖ0, mul_one, Nat.add_sub_cancel]
    rw [this]
    exact Subring.mul_mem _ (Subring.pow_mem _ hϖO _) hy
  let T : w.adicCompletion E → GL (Fin n) (w.adicCompletion E) := fun a =>
    ⟨Matrix.transvection i j a, Matrix.transvection i j (-a),
      by rw [Matrix.transvection_mul_transvection_same i j hne, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hne, neg_add_cancel, Matrix.transvection_zero]⟩
  have hT : ∀ a, ((T a : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.transvection i j a := fun a => rfl
  have hentry : ∀ {R : Type} [CommRing R] (a : R) (p q : Fin n), Matrix.transvection i j a p q =
      (if p = q then 1 else 0) + (if i = p ∧ j = q then a else 0) := by
    intro R _ a p q
    simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
  have hu : T x ∈ unipB (w.adicCompletion E) (Fin n) := by
    refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun p q hqp => ?_, fun p => ?_⟩
    · rw [hT, hentry, if_neg (fun h => by rw [h] at hqp; exact lt_irrefl _ hqp), if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hqp hlt'
    · rw [hT, hentry, if_pos rfl, if_neg, add_zero]
      rintro ⟨rfl, h⟩
      exact hne h.symm
  have hsd : superDiag (T x) = x := by
    unfold GlobalTheory.Whittaker.superDiag
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · rw [hT, hentry, if_neg hne, if_pos ⟨rfl, rfl⟩, zero_add]
      · intro b hb hbj
        have hb' := (Finset.mem_filter.1 hb).2
        rw [hT, hentry, if_neg (fun h => by rw [← h] at hb'; omega), if_neg (fun h => hbj h.2.symm), add_zero]
      · intro hj
        exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ j, hij⟩) hj
    · intro a _ hai
      refine Finset.sum_eq_zero fun b hb => ?_
      have hb' := (Finset.mem_filter.1 hb).2
      rw [hT, hentry, if_neg (fun h => by rw [← h] at hb'; omega), if_neg (fun h => hai h.1.symm), add_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hk : T c ∈ KGL w (n := n) := by
    refine ⟨⟨Matrix.transvection i j ⟨c, hcO⟩, Matrix.transvection i j (-⟨c, hcO⟩),
      by rw [Matrix.transvection_mul_transvection_same i j hne, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hne, neg_add_cancel, Matrix.transvection_zero]⟩, ?_⟩
    apply Units.ext
    ext p q
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, hT]
    rw [hentry, hentry]
    split_ifs <;> simp
  have hkey : D * T c = T x * D := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hDv, hT, hT]
    ext p q
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hentry, hentry]
    by_cases hpq : i = p ∧ j = q
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [if_neg hne, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, zero_add, zero_add, hc, hdj]
      ring_nf
    · simp only [if_neg hpq, add_zero]
      split_ifs with h
      · subst h
        simp
      · simp
  have h1 := hWK D (T c) hk
  rw [hkey, hWN (T x) hu D, hsd] at h1
  have h2 : (ψ x - 1) * W D = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hψy)

end GlobalTheory.WhitTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSectionMulAdelicFunctionLevelCover
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.CompRat


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem exists_sec_mul_adelic_fun : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → IsUnf U → FnAlgClosed (Xo := Xo) (c := c) → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∃ f' ∈ sec Xo c a n, (∀ h : GA D V, rdU U f' (dict h).1 (dict h).2 = σ (w h) * rdU U f (dict h).1 (dict h).2) ∧ (∀ la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (U.X k).Ψ r, rdU U f ∈ holSub0 U.X la → rdU U f' ∈ holSub0 U.X la) ∧ ∀ lam : HeightOneSpectrum (𝓞 c.F), (∀ h, lam.valuation c.F (w h) ≤ 1) → (∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f) → ∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f' := by
  intro D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hio hpq hA hσ hW hL hdom hU hF w hfin hQ hK a n f hf
  classical
  obtain ⟨v₀, hv₀⟩ := _root_.GlobalTheory.CompFactor.exists_factor_comp D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hio hpq hA hσ hW hL hdom
    w hfin hQ hK
  have hr1 : 1 ≤ r := hU.1 ▸ hpq
  obtain ⟨χ, hχ, hid, -, -, hrd⟩ := GlobalTheory.T.exists_orthogonal_idempotent_sections_indicating_components D.host.E H Dw l Xo c σ r U hr1 hσ hU hF
  let v : U.Comp → c.F := fun k => if ∃ h : GA D V, (dict h).1 = k then v₀ k else 0
  have hv : ∀ h : GA D V, v (dict h).1 = w h := fun h => by
    simp only [v]
    rw [if_pos ⟨h, rfl⟩, hv₀ h]
  have he : (∑ k, v k • χ k) ∈ sec Xo c 0 0 :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hχ k)
  have hval : ∀ k x, x ∈ (U.X k).dom → rdU U (∑ k, v k • χ k) k x = σ (v k) := by
    intro k x hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single k]
    · rw [LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, (hrd k k x hx).1 rfl, smul_eq_mul, mul_one]
    · intro k' _ hk
      rw [LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, (hrd k' k x hx).2 hk.symm, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hmul : rdU U ((∑ k, v k • χ k) * f) = fun k x => σ (v k) * rdU U f k x := by
    funext k x
    rw [GlobalTheory.rdU_mul_apply D.host.E H Dw l Xo c σ r U]
    by_cases hx : x ∈ (U.X k).dom
    · rw [hval k x hx]
    · rw [rdU_mem_offZero U f k x hx, mul_zero, mul_zero]
  refine ⟨(∑ k, v k • χ k) * f, ?_, fun h => ?_, fun la hla => ?_, fun lam hw hint => ?_⟩
  · have := sec_mul Xo c 0 a 0 n he hf
    simpa only [zero_add] using this
  · rw [hmul, ← hv h]
  · rw [hmul]
    exact (GlobalTheory.CompRat.holSub_compMul D.host.E r U.Comp U.X la (fun k => σ (v k)) (rdU U f)).2 hla
  · have hvi : ∀ k, lam.valuation c.F (v k) ≤ 1 := by
      intro k
      by_cases hk : ∃ h : GA D V, (dict h).1 = k
      · obtain ⟨h, rfl⟩ := hk
        rw [hv h]
        exact hw h
      · simp only [v]
        rw [if_neg hk, map_zero]
        exact zero_le_one
    let ε := (Fintype.equivFin U.Comp).symm
    rw [← ε.sum_comp (fun k => v k • χ k)]
    exact _root_.GlobalTheory.IdemInt.idem_comb_mul_nonneg D.host.E H Dw l Xo c lam _ (fun i => χ (ε i)) (fun i => v (ε i))
      (fun i => ⟨hχ _, hid _⟩) (fun i => hvi _) f hint

end GlobalTheory.CompRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotLeOpenSubgroupStatement
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GlobalTheory.DelGlob
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_places_inertia_not_le_openSubgroup : ∀ (Ω : Type) [Field Ω] (k : Type) [Field k] [NumberField k] [Algebra k Ω] [IsAlgClosure k Ω] (N : Subgroup (G k Ω)), IsOpen (N : Set (G k Ω)) → {w : HeightOneSpectrum (𝓞 k) | ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ¬ Ine (F := k) A ≤ N}.Finite := by
  first | exact @GlobalTheory.DelGlob.finite_not_ine_le_of_isOpen | exact GlobalTheory.DelGlob.finite_not_ine_le_of_isOpen | (intros; apply GlobalTheory.DelGlob.finite_not_ine_le_of_isOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartProjectorSpectralAtEveryLocalisation
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.EtaJoin.SpecAll

theorem specPr_all : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M →
    ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → (∀ i : D.nd.Loc, ClassSum (M.loc i)) →
    (∀ i : D.nd.Loc, ThetaCut D (D.nd.mu i) (D.nd.j i)) → D.nd.EigSpan → Rows.IsotInternal D.what₂ →
    SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → GoodFTAll D → ∀ i, SpecPr D i := by
  intro D M HT HR AV Tn HS CS TC HE II UnitaryCharacterOfReals PZ GF i
  have SU : SplitUnif D := GlobalTheory.SplitConjPlace.splitEx_all D
  have hZ : ZSpec D i :=
    GlobalTheory.EtaJoin.TypeSum.main D M i HT AV SU (_root_.GlobalTheory.TypeOrthClassSum.typeOrth_of_classSum D M AV i (CS i)) (TC i) II PZ
      (_root_.GlobalTheory.ExhaustRows.main D M HT AV Tn HS UnitaryCharacterOfReals GF i)
  have hT : TypeTie D i := _root_.GlobalTheory.EtaJoin.TypeTieProof.typeTie_holds D M i HT HR AV SU (_root_.GlobalTheory.HeckeScalarAll.heckeScalar_all D M HT AV i) HE
  exact GlobalTheory.EtaJoin.SpecProj.specPr_of_zSpec_typeTie D i hZ hT

end GlobalTheory.EtaJoin.SpecAll
end

