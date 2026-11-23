module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0169
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdjointSubstLogarithmsIntoParametersOfLogExponen
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusMapSubstPair
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstSumCMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepFrame
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepTrace
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TransportFirstLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0121
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntUnitaryOfGramClass
section
noncomputable section

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem exists_intUnitary_of_gramClass : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n n' : ℕ)
    (JS : GL (Fin n) L) (JT : GL (Fin n') L), Formalism.UG.IsUnramInv ϖ σ q → Odd q →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x y : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweG.HomA σ JS JT x y → GlobalTheory.Hk3.HoweG.GramEq σ JT x y → GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i j, (y - ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) i j ∈ Formalism.UG.intL L := by
  intro L _ _ _ ϖ σ q n n' JS JT hU hq hJS hJT hS hT x y _hG hA hGr hidx
  classical
  have hvϖ := hU.2.2.2.1
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  have hϖint : ϖ ∈ Formalism.UG.intL L := by
    unfold Formalism.UG.intL
    rw [Valuation.mem_integer_iff, hvϖ]
    exact_mod_cast (show Multiplicative.ofAdd (-1 : ℤ) ≤ 1 by decide)
  have mulVec_int : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) L) (v : Fin b → L), (∀ i j, M i j ∈ Formalism.UG.intL L) →
      (∀ j, v j ∈ Formalism.UG.intL L) → ∀ i, (M *ᵥ v) i ∈ Formalism.UG.intL L := by
    intro a b M v hM hv i
    simp only [Matrix.mulVec, dotProduct]
    exact (Formalism.UG.intL L).sum_mem fun j _ => (Formalism.UG.intL L).mul_mem (hM i j) (hv j)
  obtain ⟨V, hV, a, hxV⟩ := _root_.GlobalTheory.Hk3.IntWitt.exists_glInt_mulVec_mem_iff_forall_dvdPow L ϖ hvϖ n n' x
  obtain ⟨g0, hg0⟩ := hV
  have hVint : ∀ i j, (V : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro i j; rw [← hg0]; exact ((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2
  have hVinv : ∀ i j, ((V⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro i j; rw [← hg0, ← map_inv]
    exact (((g0⁻¹ : GL (Fin n) (Formalism.UG.intL L)) : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2
  set Vm : Matrix (Fin n) (Fin n) L := (V : Matrix (Fin n) (Fin n) L) with hVm
  have hyV : ∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (y *ᵥ (Vm *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j)) := by
    intro c hc
    have hu : ∀ i, (Vm *ᵥ c) i ∈ Formalism.UG.intL L := mulVec_int Vm c hVint hc
    rw [← hxV c hc]
    exact ⟨fun h => _root_.GlobalTheory.Hk3.HoweDuality.ker_le_of_latIdx_eq L ϖ σ q hU n n' x y hA.1 hidx _ hu h, fun h => hA.1 _ hu h⟩
  let ej : Fin n → Fin n → L := fun j => Pi.single j (ϖ ^ a j)
  have hej_int : ∀ j k, ej j k ∈ Formalism.UG.intL L := by
    intro j k
    by_cases h : k = j
    · subst h; simpa [ej] using (Formalism.UG.intL L).pow_mem hϖint (a k)
    · simp [ej, Pi.single_apply, h]
  have hej_dvd : ∀ j k, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a k) (ej j k) := by
    intro j k
    by_cases h : k = j
    · subst h; exact ⟨1, (Formalism.UG.intL L).one_mem, by simp [ej]⟩
    · simpa [ej, Pi.single_apply, h] using GlobalTheory.Hk3.IntWitt.dvdPow_zero ϖ (a k)
  let zx : {j : Fin n // 0 < a j} → Fin n' → L := fun j => x *ᵥ (Vm *ᵥ ej j)
  let zy : {j : Fin n // 0 < a j} → Fin n' → L := fun j => y *ᵥ (Vm *ᵥ ej j)
  have hzx : ∀ j r, zx j r ∈ Formalism.UG.intL L := fun j => (hxV _ (hej_int j)).mpr (hej_dvd j)
  have hzy : ∀ j r, zy j r ∈ Formalism.UG.intL L := fun j => (hyV _ (hej_int j)).mpr (hej_dvd j)
  have hix : GlobalTheory.Hk3.IntWitt.IndepMod ϖ zx := _root_.GlobalTheory.columns_indepMod L ϖ hvϖ n n' x Vm a hxV
  have hiy : GlobalTheory.Hk3.IntWitt.IndepMod ϖ zy := _root_.GlobalTheory.columns_indepMod L ϖ hvϖ n n' y Vm a hyV
  have hgr := _root_.GlobalTheory.Hk3.IntWitt.gram_class_columns L ϖ σ q hU n n' JT x y Vm a hVint hxV hGr
  obtain ⟨h, hh, hcong⟩ := _root_.GlobalTheory.Hk3.IntWittMod.witt_mod_pow L ϖ σ q hU hq n' JT hJT hT {j : Fin n // 0 < a j} (fun j => a j) zx zy
    (fun j => j.2) hzx hzy hix hiy (fun i j => hgr i j)
  refine ⟨h, hh, ?_⟩
  set H : Matrix (Fin n') (Fin n') L := ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hH
  have hHint : ∀ i j, H i j ∈ Formalism.UG.intL L := by
    obtain ⟨h0, hh0⟩ := hh
    intro i j; rw [hH, ← hh0]; exact ((h0 : Matrix (Fin n') (Fin n') (Formalism.UG.intL L)) i j).2
  set M := y - H * x with hM
  have hMv : ∀ w : Fin n → L, M *ᵥ w = y *ᵥ w - H *ᵥ (x *ᵥ w) := by
    intro w; rw [hM, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
  have hcol : ∀ j i, (M *ᵥ (Vm *ᵥ Pi.single j 1)) i ∈ Formalism.UG.intL L := by
    intro j i
    by_cases ha : a j = 0
    · have he : Pi.single j (1 : L) = ej j := by simp [ej, ha]
      rw [he, hMv]
      exact (Formalism.UG.intL L).sub_mem ((hyV _ (hej_int j)).mpr (hej_dvd j) i)
        (mulVec_int H _ hHint ((hxV _ (hej_int j)).mpr (hej_dvd j)) i)
    · have hpos : 0 < a j := Nat.pos_of_ne_zero ha
      obtain ⟨b, hb, hbe⟩ := hcong ⟨j, hpos⟩ i
      have he : ej j = ϖ ^ a j • Pi.single j (1 : L) := by
        funext k; simp [ej, Pi.single_apply]
      have key : ϖ ^ a j * (M *ᵥ (Vm *ᵥ Pi.single j 1)) i = ϖ ^ a j * (-b) := by
        have : (M *ᵥ (Vm *ᵥ ej j)) i = -((H *ᵥ zx ⟨j, hpos⟩) i - zy ⟨j, hpos⟩ i) := by
          rw [hMv]; simp only [zx, zy, Pi.sub_apply]; ring
        rw [he, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at this
        rw [this, hbe]; ring
      have := mul_left_cancel₀ (pow_ne_zero _ hϖ0) key
      rw [this]; exact (Formalism.UG.intL L).neg_mem hb
  intro i r
  have hMe : M = (M * Vm) * ((V⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [Matrix.mul_assoc, hVm, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rw [hMe, Matrix.mul_apply]
  refine (Formalism.UG.intL L).sum_mem fun k _ => (Formalism.UG.intL L).mul_mem ?_ (hVinv k r)
  have hc := hcol k i
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.col_apply] at hc

end GlobalTheory.Hk3.HoweG

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterCoordinatesSeriesOnePlace
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

namespace GlobalTheory.OnePlace

theorem exists_letterCoordinates_series_onePlace : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (n' : ℕ) [NeZero n'], Even n' → ∀ (B : OmBasis p n') (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p)), BeProp p be → ∃ bv : MvPowerSeries (ZMod n') ℂ_[p], product_zeroth_first_parts.B1 p n' bv ∧ product_zeroth_first_parts.B2 p n' bv ∧ product_zeroth_first_parts.B3 p n' bv ∧ product_zeroth_first_parts.B4 p n' bv ∧ ∀ (r0 r1 : ℕ) (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)), IntS p (inParam p U) → ∃ U' : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U'‖ ≤ 1) ∧ MvPowerSeries.subst (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U))) = U' * MvPowerSeries.subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1, MvPowerSeries.subst (fun s : ZMod n' => (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) := by
  intro p _ h5 n' _ hev B be hbe
  obtain ⟨σ, hσ, hσw⟩ := GlobalTheory.TwU.exists_isFrob_wToC p
  have hb0 := GlobalTheory.BeRead.isBe0_map p σ hσ hσw be hbe
  have hb00 : MvPowerSeries.constantCoeff (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) be) = 0 := by
    by_contra h
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h
    exact (hb0.axes 0 h).1 rfl
  have hD := GlobalTheory.TwU.dualOm_wToC p σ hσw n' hev B
  obtain ⟨bv, t, x, ⟨h1, h2, h3, h4⟩, hcc, hsim, ht, hx, htla, hxt⟩ :=
    Unr.exists_coords_and_series h5 hσ hb0 n' hev _ _ hD
  refine ⟨bv, h1, h2, h3, h4, fun r0 r1 U hU => ?_⟩
  obtain ⟨V, hV, hVeq⟩ := GlobalTheory.OrbitPair.expS_neg_sum_bivariate_pair_integral σ _ _ _ bv t x hb00 hcc ht hx htla hxt hsim
  obtain ⟨U2, hU2, hU2eq⟩ := GlobalTheory.OnePlacePairs.pairs_all _ bv x V hb00 hcc (fun r => (hx r).2) hV hVeq r0 r1
  obtain ⟨hξ0, hξint⟩ := GlobalTheory.OnePlace.xiE_integral (r0 := r0) (r1 := r1) x hx
  obtain ⟨hJ0, hJ⟩ := GlobalTheory.OnePlace.Letters.subst_inLetters_jetLogG (p := p) (r0 := r0) (r1 := r1) (thOne B be U)
  refine ⟨U2 * MvPowerSeries.subst (xiE x) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inParam p U)), ?_, ?_⟩
  · intro m
    rw [MvPowerSeries.coeff_mul]
    refine (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun q _ => ?_)
    rw [norm_mul]
    exact mul_le_one₀ (hU2 _) (norm_nonneg _) (hξint _ hU _)
  · rw [hJ, GlobalTheory.OnePlaceRead.read_thOne B be hbe U _ (xiE x) hJ0 hξ0 (GlobalTheory.OnePlace.Ident.coordZ_jetZ σ hσw hev B hD t x ht (fun r => (hx r).2) htla hxt r0 r1), hU2eq]
    ring

end GlobalTheory.OnePlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomRhoK
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

def toKur (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) : MaximalUnramifiedExtension p := if h : x ∈ MaximalUnramifiedExtension p then ⟨x, h⟩ else 0

theorem coe_toKur {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (h : x ∈ MaximalUnramifiedExtension p) : ((toKur p x : MaximalUnramifiedExtension p) : ℂ_[p]) = x := by
  simp [toKur, h]

def rhoK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (z : Bool × HH D) (y : D.host.E) : MaximalUnramifiedExtension p :=
  toKur p (tauEmb D lam (tauPl D z) y)

def gK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' r : ℕ}
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (z : Bool × HH D) (a : Fin N) (b₀ : Fin N') (i : Fin r) : MaximalUnramifiedExtension p :=
  ∑ b₁ : Fin N', ∑ a₁ : Fin N, rhoK D lam z (D.host.conj (b i b₁ a₁)) * rhoK D lam z (P' (tauPl D z) b₁ b₀) *
    ((P (tauPl D z)).map (rhoK D lam z))⁻¹ a a₁

def hK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' r : ℕ}
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (w : Bool × HH D) (a : Fin N) (b₀ : Fin N') (i : Fin r) : MaximalUnramifiedExtension p :=
  ∑ b₁ : Fin N', ∑ a₁ : Fin N, ((P' (tauPl D w)).map (rhoK D lam w))⁻¹ b₀ b₁ * rhoK D lam w (b i b₁ a₁) *
    rhoK D lam w (P (tauPl D w) a₁ a)

def fOf (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (e : (R × Fin (nP D p / 2)) × Fin N × Fin N') (i : Fin r) : MaximalUnramifiedExtension p :=
  ∑ t : ZMod (nP D p), if t.val % 2 = 0 then σ^[t.val] (om e.1.2) * g (OrbitPlaces.orbMap D p e.1.1 t) e.2.1 e.2.2 i else 0

def fOf' (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (e : (R × Fin (nP D p / 2)) × Fin N × Fin N') (i : Fin r) : MaximalUnramifiedExtension p :=
  ∑ t : ZMod (nP D p), if t.val % 2 = 0 then 0 else σ^[t.val] (oms e.1.2) * g (OrbitPlaces.orbMap D p e.1.1 t) e.2.1 e.2.2 i

theorem exists_ringHom_rhoK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (hσ : UnrOK (MaximalUnramifiedExtension p) p σ) (hcl : IsResidueClassZero D p ∨ IsSg D p) (z : Bool × HH D) :
    ∃ ρ : D.host.E →+* MaximalUnramifiedExtension p, ∀ y, rhoK D lam z y = ρ y ∧ ((ρ y : MaximalUnramifiedExtension p) : ℂ_[p]) = tauEmb D lam (tauPl D z) y := by
  have hmem : ∀ y, tauEmb D lam (tauPl D z) y ∈ MaximalUnramifiedExtension p := fun y => by
    obtain ⟨a, ha, -⟩ := exists_kur_frob_tauEmb_posPl D p lam σ hσ hcl z y
    rw [← ha]; exact a.2
  let ρ0 : D.host.E →+* ℂ_[p] := lam.comp (Formalism.L2.KerInert.IntegralOrthonormalChange.embQ D (tauPl D z))
  have h0 : ∀ y, ρ0 y = tauEmb D lam (tauPl D z) y := fun y => by
    simp only [ρ0, RingHom.comp_apply, tauEmb, Formalism.L2.KerInert.IntegralOrthonormalChange.lamC_embT]
  refine ⟨ρ0.codRestrict (MaximalUnramifiedExtension p) (fun y => by rw [h0]; exact hmem y), fun y => ⟨?_, ?_⟩⟩
  · apply Subtype.ext
    rw [rhoK, coe_toKur (hmem y)]
    exact (h0 y).symm
  · exact h0 y

theorem coe_rhoK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (hσ : UnrOK (MaximalUnramifiedExtension p) p σ) (hcl : IsResidueClassZero D p ∨ IsSg D p) (z : Bool × HH D) (y : D.host.E) :
    ((rhoK D lam z y : MaximalUnramifiedExtension p) : ℂ_[p]) = tauEmb D lam (tauPl D z) y := by
  obtain ⟨ρ, hρ⟩ := exists_ringHom_rhoK D lam σ hσ hcl z
  rw [(hρ y).1, (hρ y).2]

theorem sigma_rhoK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (hσ : UnrOK (MaximalUnramifiedExtension p) p σ) (hcl : IsResidueClassZero D p ∨ IsSg D p) (z : Bool × HH D) (y : D.host.E) :
    σ (rhoK D lam z y) = rhoK D lam (posPl D p z 1) (D.host.conj y) := by
  obtain ⟨a, ha, hsa⟩ := exists_kur_frob_tauEmb_posPl D p lam σ hσ hcl z y
  have e1 : rhoK D lam z y = a := Subtype.ext (by rw [coe_rhoK D lam σ hσ hcl, ha])
  apply Subtype.ext
  rw [e1, coe_rhoK D lam σ hσ hcl, hsa]

theorem norm_sigma_eq (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (hσ : UnrOK (MaximalUnramifiedExtension p) p σ) (x : MaximalUnramifiedExtension p) :
    ‖σ x‖ = ‖x‖ :=
  Formalism.L2.Th1.D.sigmaIsom (MaximalUnramifiedExtension p) p σ hσ x

end GlobalTheory.KerStd.HypCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorsRowsLiftsRationalAdjointClosed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InertOkH

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem csum_zero_left {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (g : S.Cl → S.V) : S.csum 0 g = 0 := by
  simp [CSD.csum]

theorem csum_zero_right {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (f : S.Cl → S.V) : S.csum f 0 = 0 := by
  simp [CSD.csum]


set_option maxHeartbeats 4000000 in
theorem inertHeckeOperators_rows_rational_adjointClosed (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : R.WeakCharacterisation F) (hJ : InertJunk A3) (t : T) :
    (A3.rowI t).InertRationalAdjoint := by
  obtain ⟨tie⟩ := hW.inert.hR t
  have hrk : D.sp.X'.rank = A3.A.r + D.R.m * A3.A.t := R.toRealDat.B.rankR
  have hpl := (_root_.GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hW).2.2.1 t
  have key := GlobalTheory.T.inertHeckeOperators_rows_rational_selfAdjoint_labels R.toRealDat F.lv2 hW.base.lev hW.base.fam hW.base.models t (A3.okI t × List ℕ)
    (fun i => R.plI i.1) (fun i => Formalism.IndefR.Links.labIn D.sp.X'.rank i.2) (A3.heckeRI t)
    (fun i => Formalism.L2.Col.InertTypeOk D.sp.X'.rank i.2)
    (fun i hi => ⟨(hpl i.1 i.1.2).1, (hpl i.1 i.1.2).2,
      ((_root_.GlobalTheory.Hk3.labIn_selfDual_iff D.sp.X'.rank (Formalism.IndefR.Links.labIn D.sp.X'.rank i.2)).mpr ⟨i.2, hi.2.2, hi.1, hi.2.1, rfl⟩).2.1⟩) tie
  have hop : ∀ k : A3.okI t × List ℕ, A3.heckeRI t k = 0 ∨
      ∃ s', Formalism.L2.Col.InertTypeOk D.sp.X'.rank s' ∧ A3.heckeRI t k = A3.heckeRI t (k.1, s') := by
    rintro ⟨Q, s⟩
    rcases hJ.R t Q s with h | ⟨s', hs', h⟩
    · exact Or.inl h
    · exact Or.inr ⟨s', hrk ▸ hs', h⟩
  refine ⟨fun k a b => ?_, fun k => ⟨k, fun f g => ?_⟩⟩
  · show LinearMap.toMatrix (A3.A.MtildeCSD t).basis (A3.A.MtildeCSD t).basis (A3.heckeRI t k) a b ∈ cmMax D.what₂.LL
    rcases hop k with h | ⟨s', hs', h⟩
    · rw [h]
      simp only [map_zero]
      exact zero_mem _
    · rw [h]
      exact (key (k.1, s') hs').1 a b
  · rcases hop k with h | ⟨s', hs', h⟩
    · have h0 : (A3.rowI t).opI k = 0 := h
      rw [h0]
      simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero, csum_zero_left, csum_zero_right]
    · have h1 : (A3.rowI t).opI k = A3.heckeRI t (k.1, s') := h
      rw [h1]
      exact (key (k.1, s') hs').2.1 f g


set_option maxHeartbeats 4000000 in
theorem inertHeckeOperators_lifts_rational_adjointClosed (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : R.WeakCharacterisation F) (hJ : InertJunk A3) (j : Fin D.R.m) (t : T) :
    (A3.liftI j t).InertRationalAdjoint := by
  obtain ⟨tie⟩ := hW.inert.hL j t
  have hrk : (Vc D j).rank = A3.A.r + A3.A.t := R.toRealDat.B.rankL j
  have hpl := (_root_.GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hW).2.2.1 t
  have key := _root_.GlobalTheory.InertHeckeLift.inert_lifts R.toRealDat F.lv2 hW.base.lev hW.base.fam hW.base.models j t (A3.okI t × List ℕ)
    (fun i => R.plI i.1) (fun i => Formalism.IndefR.Links.labIn (Vc D j).rank i.2) (A3.heckeLI j t)
    (fun i => Formalism.L2.Col.InertTypeOk (Vc D j).rank i.2)
    (fun i hi => ⟨(hpl i.1 i.1.2).1, (hpl i.1 i.1.2).2,
      ((_root_.GlobalTheory.Hk3.labIn_selfDual_iff (Vc D j).rank (Formalism.IndefR.Links.labIn (Vc D j).rank i.2)).mpr ⟨i.2, hi.2.2, hi.1, hi.2.1, rfl⟩).2.1⟩) tie
  have hop : ∀ k : A3.okI t × List ℕ, A3.heckeLI j t k = 0 ∨
      ∃ s', Formalism.L2.Col.InertTypeOk (Vc D j).rank s' ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, s') := by
    rintro ⟨Q, s⟩
    rcases hJ.L j t Q s with h | ⟨s', hs', h⟩
    · exact Or.inl h
    · exact Or.inr ⟨s', hrk ▸ hs', h⟩
  refine ⟨fun k a b => ?_, fun k => ⟨k, fun f g => ?_⟩⟩
  · show LinearMap.toMatrix (A3.A.MtCSD j t).basis (A3.A.MtCSD j t).basis (A3.heckeLI j t k) a b ∈ cmMax D.what₂.LL
    rcases hop k with h | ⟨s', hs', h⟩
    · rw [h]
      simp only [map_zero]
      exact zero_mem _
    · rw [h]
      exact (key (k.1, s') hs').1 a b
  · rcases hop k with h | ⟨s', hs', h⟩
    · have h0 : (A3.liftI j t).opI k = 0 := h
      rw [h0]
      simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero, csum_zero_left, csum_zero_right]
    · have h1 : (A3.liftI j t).opI k = A3.heckeLI j t (k.1, s') := h
      rw [h1]
      exact (key (k.1, s') hs').2.1 f g

theorem heckeOperators_rows_lifts_rational_adjointClosed : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → InertJunk A3 → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) ∧ (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hW hJ
  have h2 := hecke_operators_rational_adjoint_closed_of_weak_char R F hW
  exact ⟨fun t => ⟨h2.1 t, inertHeckeOperators_rows_rational_adjointClosed R F hW hJ t⟩, fun j t => ⟨h2.2 j t, inertHeckeOperators_lifts_rational_adjointClosed R F hW hJ j t⟩⟩

end GlobalTheory.InertOkH

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtFormOfMemStdAt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory.TopLaw

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_form_of_mem_stdAt (a : E) (η : Sp E n →ₗ[E] E) (h : ∀ i, IntAt P (a * η (Pi.single i 1))) {v : Sp E n}
    (hv : v ∈ stdAt E n P) : IntAt P (a * η v) := by
  rw [GlobalTheory.TopInv.form_apply η v, Finset.mul_sum]
  refine GlobalTheory.TopStep.intAt_sum _ fun j _ => ?_
  rw [mul_left_comm]
  exact (mem_stdAt.1 hv j).mul (h j)

theorem intAt_form_comp_iff (a : E) (κ : GLint E n P) (η : Sp E n →ₗ[E] E) :
    (∀ i, IntAt P (a * (η ∘ₗ κ.1.toLinearMap) (Pi.single i 1))) ↔ ∀ i, IntAt P (a * η (Pi.single i 1)) := by
  refine ⟨fun h i => ?_, fun h i => intAt_form_of_mem_stdAt a η h (glint_mem κ (single_mem_stdAt i))⟩
  have h1 := intAt_form_of_mem_stdAt a _ h (glint_mem κ⁻¹ (single_mem_stdAt i))
  have e : κ.1 ((κ⁻¹).1 (Pi.single i 1)) = Pi.single i 1 := LinearEquiv.apply_symm_apply κ.1 _
  have e' : (η ∘ₗ κ.1.toLinearMap) ((κ⁻¹).1 (Pi.single i 1)) = η (Pi.single i 1) := congrArg η e
  rwa [e'] at h1

end SlopeTestRemainingChoices

theorem psi_add_int {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {c : LocCst X SB} (hc : c.Ok) (P : SB) {k : ℕ}
    (hk : k ≤ c.D P) {x z : X.E} (hx : IntAt P.1 ((qOf P.1 : X.E) ^ k * x)) (hz : IntAt P.1 (z - x)) :
    c.psi P ((epsSg : X.E) * z) = c.psi P ((epsSg : X.E) * x) := by
  have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
  have hq := fun m => intAt_pow (GlobalTheory.TopStep.intAt_nat (P := P.1) (qOf P.1)) m
  have hd := he.mul hz
  have h1 : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * ((epsSg : X.E) * x)) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
    have := (hq d).mul (he.mul hx)
    convert this using 1
    rw [hd, pow_add]
    ring
  have := hc.psi_add P _ _ h1 ((hq _).mul hd)
  rw [hc.psi_int P _ hd, mul_one] at this
  rw [← this]
  congr 1
  ring

theorem ftY_comp_glint : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok → ∀ (P : rowSG Pr sel mu), (P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → ∀ {n : ℕ} (κ : GLint X.E n P.1) (η : Sp X.E n →ₗ[X.E] X.E) (y' y'' : Sp X.E n), (P.1 ∈ Pr.vGs → ∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) → (P.1 ∉ Pr.vGs → ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' i)) → (P.1 ∈ Pr.vGs → κ.1 y'' - y' ∈ stdAt X.E n P.1) → (P.1 ∉ Pr.vGs → ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ.1 y'' - y') ∈ stdAt X.E n P.1) → ftY sel mu cst P (η ∘ₗ κ.1.toLinearMap) y'' = ftY sel mu cst P η y' := by
  intro X Pr sel S mu cst hc P hD n κ η y' y'' hy1 hy2 hk1 hk2
  have hq := qOf_ne_zero (P := P.1)
  unfold ftY
  by_cases hP : P.1 ∈ Pr.vGs
  · rw [if_pos hP, if_pos hP]
    have hi := intAt_form_comp_iff 1 κ η
    simp only [one_mul] at hi
    by_cases h : ∀ i, IntAt P.1 (η (Pi.single i 1))
    · rw [if_pos h, if_pos (hi.2 h)]
      have h' : ∀ i, IntAt P.1 (1 * η (Pi.single i 1)) := fun i => by rw [one_mul]; exact h i
      refine psi_add_int hc P (hc.D_pos P) ?_ ?_
      · have := intAt_form_of_mem_stdAt 1 η h' (v := (qOf P.1 : X.E) • y') (mem_stdAt.2 (hy1 hP))
        rwa [one_mul, map_smul, smul_eq_mul, ← pow_one (qOf P.1 : X.E)] at this
      · have := intAt_form_of_mem_stdAt 1 η h' (hk1 hP)
        rwa [one_mul, map_sub] at this
    · rw [if_neg h, if_neg fun h' => h (hi.1 h')]
  · rw [if_neg hP, if_neg hP]
    have hi := intAt_form_comp_iff ((qOf P.1 : X.E) ^ cst.M) κ η
    by_cases h : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single i 1))
    · rw [if_pos h, if_pos (hi.2 h)]
      refine congrArg _ (psi_add_int hc P (hD hP) ?_ ?_)
      · have := intAt_form_of_mem_stdAt _ η h (v := (qOf P.1 : X.E) ^ cst.M • y') (mem_stdAt.2 (hy2 hP))
        rwa [map_smul, smul_eq_mul, ← mul_assoc, ← pow_add, ← two_mul] at this
      · have := intAt_form_of_mem_stdAt _ η h (hk2 hP)
        rwa [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul, map_sub] at this
    · rw [if_neg h, if_neg fun h' => h (hi.1 h')]

end GlobalTheory.TopLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAwayFromMovedLocalDatumStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralAwayFrom_moved_localDatum : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < D.R.m → ∀ (P : rowSG t.Pr t.sel (t.tup μ)) (hal : AutY t.X D.R i) (h : AutY t.X D.R (i + 1)), (P.1 ∈ t.Pr.vGs → hal ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) i P.1) ∧ h ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) (i + 1) P.1)) → ∀ x, IntOff (t.O u μ).S (t.seam.σ₀ (omPhi t.Ch t.sel (t.tup μ) (t.cst μ) i P hal h x)) := by
  first | exact @GlobalTheory.OmPhiInt.intOff_omPhi | exact GlobalTheory.OmPhiInt.intOff_omPhi | (intros; apply GlobalTheory.OmPhiInt.intOff_omPhi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDataIntegralAwayFromLevelsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_data_integralAwayFrom_levels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ p Yb d x, Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N → IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl2 (R := D.R) (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 p Yb d x)) := by
  first | exact @GlobalTheory.CplTwoInt.xiCpl2_intOff_tied | exact GlobalTheory.CplTwoInt.xiCpl2_intOff_tied | (intros; apply GlobalTheory.CplTwoInt.xiCpl2_intOff_tied <;> assumption)
end

