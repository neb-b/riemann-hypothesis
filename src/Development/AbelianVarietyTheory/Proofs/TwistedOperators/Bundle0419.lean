module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0343
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0415
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialSuperdiagonalOffException
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.UniOff

open GlobalTheory.FinPlLoc (idem idem_mem_idAt idem_mem_intAt idem_mul_self cA_idem mem_idAt_iff ePl ePl_int evalV_ePl)

theorem intAt_neg {D : D7} {v : GlobalTheory.FinPl.Pl D} {z : AE D} (h : z ∈ intAt D (· = v)) : -z ∈ intAt D (· = v) :=
  ⟨neg_mem h.1, by rw [map_neg]; exact neg_mem h.2⟩

theorem intAt_add {D : D7} {v : GlobalTheory.FinPl.Pl D} {z w : AE D} (h : z ∈ intAt D (· = v)) (h' : w ∈ intAt D (· = v)) :
    z + w ∈ intAt D (· = v) :=
  ⟨add_mem h.1 h'.1, by rw [map_add]; exact add_mem h.2 h'.2⟩

theorem idem_incA_mem {D : D7} (v : GlobalTheory.FinPl.Pl D) (o : 𝓞 D.host.E) :
    idem D (· = v) * incA D (o : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨Ideal.mul_mem_right _ _ (idem_mem_idAt _), ?_⟩
  rw [map_mul, GlobalTheory.IdeleAA.finPart_incA]
  unfold idem
  rw [GlobalTheory.FinPlLoc.finPart_pair, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  exact AddSubgroup.subset_closure ⟨ePl D (· = v), ePl_int _, o, rfl⟩

theorem idem_incA {D : D7} (P : GlobalTheory.FinPl.Pl D → Prop) (e : D.host.E) :
    idem D P * incA D e = pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] e := by
  unfold idem
  show (pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem gen_mem {D : D7} (S : HSp D) (𝔞 : Set D.host.E) (L : GlobalTheory.FinPl.Lat S) (v : GlobalTheory.FinPl.Pl D)
    (P : GlobalTheory.FinPl.Pl D → Prop) (hP : ∀ w, ¬ P w → w ≠ v) {a : D.host.E} (ha : a ∈ 𝔞) {x : Fin S.rank → D.host.E}
    (hx : x ∈ L) : (fun m => idem D (· = v) * incA D (a * x m)) ∈ GlobalTheory.FinPl.latMul S 𝔞 L P := by
  apply AddSubgroup.subset_closure
  refine ⟨ePl D (· = v), ePl_int _, fun w hw => by rw [evalV_ePl, if_neg (hP w hw)], a, ha, x, hx, ?_⟩
  funext m
  exact idem_incA _ _

theorem col_mem {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (p : Fin c) {t : D.host.E} (ht : t ∈ 𝔟 p) : (fun m => t * d.a m p) ∈ d.lat Λ 𝔟 := by
  classical
  refine ⟨0, Λ.zero_mem, Pi.single p t, fun q => ?_, ?_⟩
  · by_cases hq : q = p
    · subst hq; simpa using ht
    · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem
  · funext m
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

theorem uni_off : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ G.pl.S0 → ∀ o ∈ intAt D (· = v), psiE W.ψ (o * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) = 1 := by
  intro D _ T L _ _ sc G W _ _ F hF ρ h M hM i j hij v hv o ho
  classical
  have h1 : 1 ≤ 2 * ρ + 2 := by omega
  have h1' : 1 ≤ 2 * ρ + 1 := by omega
  have h2' : 2 * ρ + 1 ≤ D.R.m := by omega
  obtain ⟨hleB, heB, -, -⟩ := hF.hB ρ h

  obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D W.ψ W.ψ_std
  obtain ⟨hA, hψ⟩ := hα v

  have sdV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ fun j hj => by
      obtain ⟨h3, -⟩ := Node.grid.inj hj; omega).sd
  have sdW : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (G.isV (X := .grid (2 * ρ + 1) 0) ⟨h2', Nat.zero_le _⟩ fun j hj => by
      obtain ⟨h3, -⟩ := Node.grid.inj hj; omega).sd
  have hMlat := (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ (isSelfDualC_neg sdV) sdW (fun _ => True) M).1 hM.1

  set aB := (G.colDec (2 * ρ + 2) h1 h).a with haB
  set aJ := (G.colDec (2 * ρ + 1) h1' h2').a with haJ
  set p : Fin (2 * ρ + 2 - 1) := Fin.castLE (by omega) j with hp
  have hq : 2 * ρ - 1 - i.1 < 2 * ρ + 1 - 1 := by omega
  set q : Fin (2 * ρ + 1 - 1) := ⟨2 * ρ - 1 - i.1, hq⟩ with hqdef
  set colB : Fin (G.V (.grid (2 * ρ + 2) 0)).rank → AE D := fun l => incA D (aB l p) with hcolB
  set g : AE D := ∑ k, ∑ l, cA D (incA D (aJ k q)) * incA D ((G.V (.grid (2 * ρ + 1) 0)).gram k l) * (M *ᵥ colB) l
    with hg

  have hcol : ∀ k, (M ⬝ (F.dB ρ h).jX) k j = incA D ((-D.host.xi0) ^ (j.1 + 1)) * (M *ᵥ colB) k := by
    intro k
    simp only [Matrix.mul_apply, GlobalTheory.MixModel.HypDec.jX, heB, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [GlobalTheory.MixModel.rat, Matrix.map_apply, colsOf, hcolB, map_mul, map_pow, hp]
    ring
  have hN : ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j = incA D (-D.host.xi0) * g := by
    have e1 : ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j = ((F.dJ ρ h).pX *ᵥ fun k => (M ⬝ (F.dB ρ h).jX) k j) i := rfl
    have e2 := _root_.GlobalTheory.AscFin.incA_neg_xi0_pow_mul_pX_mulVec_eq_sum (G.colDec (2 * ρ + 1) h1' h2') (F.dJ ρ h) (by omega) (hF.hJ ρ h) i hq
      (fun k => (M ⬝ (F.dB ρ h).jX) k j)
    rw [← e1] at e2
    simp only [hcol] at e2
    have e3 : incA D ((-D.host.xi0) ^ (i.1 + 1)) * (incA D (-D.host.xi0) * g) =
        ∑ k, ∑ l, cA D (incA D (aJ k q)) * incA D ((G.V (.grid (2 * ρ + 1) 0)).gram k l) *
          (incA D ((-D.host.xi0) ^ (j.1 + 1)) * (M *ᵥ colB) l) := by
      rw [hg, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have hp1 : (-D.host.xi0) ^ (j.1 + 1) = (-D.host.xi0) ^ (i.1 + 1) * (-D.host.xi0) := by rw [hij, pow_succ]
      rw [hp1, map_mul]
      ring
    have hunit : incA D (((-D.host.xi0) ^ (i.1 + 1))⁻¹) * incA D ((-D.host.xi0) ^ (i.1 + 1)) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)), map_one]
    calc ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j
        = (incA D (((-D.host.xi0) ^ (i.1 + 1))⁻¹) * incA D ((-D.host.xi0) ^ (i.1 + 1))) *
          ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j := by rw [hunit, one_mul]
      _ = incA D (((-D.host.xi0) ^ (i.1 + 1))⁻¹) * (incA D ((-D.host.xi0) ^ (i.1 + 1)) *
          (incA D (-D.host.xi0) * g)) := by rw [mul_assoc, e2, ← e3]
      _ = incA D (-D.host.xi0) * g := by rw [← mul_assoc, hunit, one_mul]

  set Φ : D.host.E → AE D := fun t => ((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) *
    (idem D (· = v) * incA D t * g) with hΦ
  have hgen : ∀ t ∈ {t : D.host.E | ∃ a ∈ D.host.AA, ∃ c' ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q, ∃ c ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p, t = D.host.conj (a * c') * c}, Φ t ∈ intAt D (· = v) := by
    rintro t ⟨a, ha, c', hc', c, hc, rfl⟩
    have hxB : (fun m => c * aB m p) ∈ G.Λ (.grid (2 * ρ + 2) 0) := by
      have e := G.sp.colLat (2 * ρ + 2) h1 h
      show _ ∈ (vtxOf L G.sp.Vs (2 * ρ + 2) 0).lat
      rw [e]
      exact col_mem (G.colDec (2 * ρ + 2) h1 h) _ _ p hc
    have hxJ : (fun m => c' * aJ m q) ∈ G.Λ (.grid (2 * ρ + 1) 0) := by
      have e := G.sp.colLat (2 * ρ + 1) h1' h2'
      show _ ∈ (vtxOf L G.sp.Vs (2 * ρ + 1) 0).lat
      rw [e]
      exact col_mem (G.colDec (2 * ρ + 1) h1' h2') _ _ q hc'
    set y : Fin (G.V (.grid (2 * ρ + 2) 0)).rank → AE D := fun m => idem D (· = v) * incA D (1 * (c * aB m p)) with hy
    have hyT : y ∈ latV (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) (fun _ => True) :=
      gen_mem _ {1} _ v _ (fun w hw => absurd trivial hw) rfl hxB
    set w : Fin (G.V (.grid (2 * ρ + 1) 0)).rank → AE D := fun m => idem D (· = v) * incA D (a * (c' * aJ m q)) with hw
    have hwv : w ∈ latA (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) :=
      gen_mem _ {a | a ∈ D.host.AA} _ v _ (fun w hw => hw) ha hxJ
    have hMy : M *ᵥ y ∈ latA (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) (fun _ => True) := hMlat.2 y hyT
    have hMy' := _root_.GlobalTheory.FinPlLoc.idem_smul_mem_latMul_at D _ _ _ v _ hMy
    have hyy : idem D (· = v) • (M *ᵥ y) = M *ᵥ y := by
      rw [← Matrix.mulVec_smul]
      congr 1
      funext k
      simp [hy, smul_eq_mul, ← mul_assoc, idem_mul_self]
    rw [hyy] at hMy'
    have z1 := (hA _ _ _).1 hMy'
    have z2 := (hA _ _ _).1 hwv
    have hP := _root_.GlobalTheory.LatPairInt.pairing_mem_at D _ _ sdW v _ _ z1 z2
    have hw' : ∀ k, cA D ((((α⁻¹ : (AE D)ˣ) : AE D) • w) k) = cA D ((α⁻¹ : (AE D)ˣ) : AE D) * idem D (· = v) *
        incA D (D.host.conj (a * c')) * cA D (incA D (aJ k q)) := by
      intro k
      simp only [hw, Pi.smul_apply, smul_eq_mul, map_mul, cA_idem, GlobalTheory.IdeleAA.cA_incA]
      ring
    have hz' : ∀ l, (((α⁻¹ : (AE D)ˣ) : AE D) • (M *ᵥ y)) l = ((α⁻¹ : (AE D)ˣ) : AE D) * (idem D (· = v) * incA D c) *
        (M *ᵥ colB) l := by
      intro l
      rw [Pi.smul_apply, smul_eq_mul]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hy, hcolB]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [one_mul, map_mul]
      ring
    have hI := idem_mul_self (D := D) (· = v)
    convert hP using 1
    simp only [hw', hz', hΦ, hg, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    linear_combination (-(((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) * incA D (D.host.conj a) * incA D (D.host.conj c') *
      incA D c * (cA D (incA D (aJ k q)) * incA D ((G.V (.grid (2 * ρ + 1) 0)).gram k l) * (M *ᵥ colB) l))) * hI
  have hspan : ∀ t ∈ Submodule.span (𝓞 D.host.E) {t : D.host.E | ∃ a ∈ D.host.AA, ∃ c' ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q, ∃ c ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p, t = D.host.conj (a * c') * c}, Φ t ∈ intAt D (· = v) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht => exact hgen t ht
    | zero =>
      have : Φ 0 = 0 := by simp only [hΦ, map_zero, mul_zero, zero_mul]
      rw [this]; exact ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
    | add x y _ _ hx hy =>
      have : Φ (x + y) = Φ x + Φ y := by simp only [hΦ, map_add (f := _)]; ring
      rw [this]; exact intAt_add hx hy
    | smul o x _ hx =>
      have hI := idem_mul_self (D := D) (· = v)
      have : Φ (o • x) = (idem D (· = v) * incA D (o : D.host.E)) * Φ x := by
        rw [Algebra.smul_def]
        simp only [hΦ, map_mul]
        linear_combination (-(((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) *
          incA D (algebraMap (𝓞 D.host.E) D.host.E o) * incA D x * g)) * hI
      rw [this]; exact GlobalTheory.IdeleAA.intAt_mul (idem_incA_mem v o) hx
  obtain ⟨u, hu, hus⟩ := _root_.GlobalTheory.StairUnit.exists_unit_mem_span G ρ p q (by simp [hp, hqdef]; omega) v hv
  have hz : idem D (· = v) * (((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) * g) ∈ intAt D (· = v) := by
    refine _root_.GlobalTheory.UnitAtPl.idem_mul_mem_of_unit D v u hu _ ?_
    have := hspan _ hus
    simp only [hΦ] at this
    convert this using 1; ring

  have hs : idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ (idem_mem_idAt _)
  have key : incA D D.host.xi0⁻¹ * ((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) *
      (idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) ∈ intAt D (· = v) := by
    have hx0 : incA D D.host.xi0⁻¹ * incA D (-D.host.xi0) = -1 := by
      rw [← map_mul, mul_neg, inv_mul_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_neg, map_one]
    rw [hN]
    convert intAt_neg hz using 1
    linear_combination (((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) * idem D (· = v) * g) * hx0
  have hoid : idem D (· = v) * o = o := (mem_idAt_iff _ o).1 ho.1
  have := (hψ _ hs).2 key o ho
  rw [← hoid]
  convert this using 2
  ring

end GlobalTheory.UniOff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumScalarSmulMemCompletedModulus
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.HalfScalarHat

open GlobalTheory.FunObj.HatFrame

theorem smul_map_mem_genGrp {D : D7} {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (𝔪 : Ideal (𝓞 D.host.E)) {g : Matrix (Fin m) (Fin n) D.host.E} (hg : g ∈ M)
    {t : Formalism.L2.Herm.intAf D.host.F D.host.E} (ht : t ∈ Formalism.L2.DIV.idS D.host.F 𝔪) :
    (t : EAf D) • g.map (eToEAf D) ∈ genGrp D.host.F (𝔪 • M) := by
  have hgen : ∀ a ∈ 𝔪, ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) •
      g.map (eToEAf D) ∈ genGrp D.host.F (𝔪 • M) := by
    intro a ha
    refine AddSubgroup.subset_closure ⟨1, one_mem _, a • g, Submodule.smul_mem_smul ha hg, ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, Formalism.L2.DIV.oToS_coe, smul_eq_mul, eToEAf,
      Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]
  have hspan : t ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((Formalism.L2.DIV.oToS D.host.F D.host.E) '' (𝔪 : Set (𝓞 D.host.E))) := ht
  clear ht
  induction hspan using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, ha, rfl⟩ := hu
    exact hgen a ha
  | zero =>
    simp only [ZeroMemClass.coe_zero, zero_smul]
    exact zero_mem _
  | add u v _ _ hu hv =>
    simp only [AddMemClass.coe_add, add_smul]
    exact add_mem hu hv
  | smul r u _ hu =>
    simp only [smul_eq_mul, MulMemClass.coe_mul, mul_smul]
    exact smul_mem_genGrp _ _ r.2 _ hu

theorem tmul_split {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (x : A ⊗[R] B) (b g : A) (α : B) :
    x * ((b * g) ⊗ₜ[R] α) = x * ((b ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] α)) * (g ⊗ₜ[R] (1 : B)) := by
  simp only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem v_triple_le {D : D7} {w : HeightOneSpectrum (𝓞 D.host.E)} {s x y z : EAf D} {c : WithZero (Multiplicative ℤ)} (h : s = x * (y * z))
    (hx : GlobalTheory.StdFrames.cpt (D := D) w x = 1) (hy : Valued.v (GlobalTheory.StdFrames.cpt (D := D) w y) ≤ c)
    (hz : Valued.v (GlobalTheory.StdFrames.cpt (D := D) w z) ≤ 1) : Valued.v (GlobalTheory.StdFrames.cpt (D := D) w s) ≤ c := by
  subst h
  rw [map_mul, hx, one_mul, map_mul, map_mul]
  calc Valued.v (GlobalTheory.StdFrames.cpt (D := D) w y) * Valued.v (GlobalTheory.StdFrames.cpt (D := D) w z) ≤ c * 1 :=
        mul_le_mul' hy hz
    _ = c := mul_one c

theorem scalar_mem_idS {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {s x y z : EAf D}
    (h : s = x * (y * z)) (e1 : ∀ w ∈ G.pl.W0, GlobalTheory.StdFrames.cpt (D := D) w x = 1)
    (e2 : ∀ w ∉ G.pl.W0, GlobalTheory.StdFrames.cpt (D := D) w x = 0)
    (hy : ∀ w ∈ G.pl.W0, Valued.v (GlobalTheory.StdFrames.cpt (D := D) w y) ≤ WithZero.exp (-(cosExp G w : ℤ)))
    (hz : z ∈ GlobalTheory.StdFrames.OA D) :
    ∃ t ∈ Formalism.L2.DIV.idS D.host.F G.modul, t.1 = s := by
  have hz' : ∀ w, Valued.v (GlobalTheory.StdFrames.cpt (D := D) w z) ≤ 1 := fun w =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((GlobalTheory.StdFrames.mem_OA_iff z).1 hz w)
  have hs : s ∈ GlobalTheory.StdFrames.OA D := by
    rw [GlobalTheory.StdFrames.mem_OA_iff]
    intro w
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hw : w ∈ G.pl.W0
    · refine v_triple_le h (e1 w hw) ((hy w hw).trans ?_) (hz' w)
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    · rw [h, map_mul, e2 w hw, zero_mul, map_zero]
      exact zero_le'
  refine ⟨⟨s, hs⟩, ?_, rfl⟩
  rw [GlobalTheory.FunObj.Comparison₂.mem_idS_modul]
  intro w hw
  exact v_triple_le h (e1 w hw) (hy w hw) (hz' w)

theorem toEAf_pair {D : D7} (α : Formalism.L2.Herm.Af D.host.F) (x : D.host.E) :
    toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = x ⊗ₜ[D.host.F] α := rfl

theorem map_toEAf_smul {D : D7} {m n : ℕ} (e : AE D) (X : Mx D m n) :
    (e • X).map (toEAf D) = toEAf D e • X.map (toEAf D) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem infPart_smul {D : D7} {m n : ℕ} {e : AE D} (he : infPart D e = 0) (X : Mx D m n) (i : Fin m) (j : Fin n) :
    infPart D ((e • X) i j) = 0 := by
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, he, zero_mul]

theorem smul_pair {D : D7} {m n : ℕ} (x : EAf D) (α : Formalism.L2.Herm.Af D.host.F) (b : D.host.E)
    (g : Matrix (Fin m) (Fin n) D.host.E) :
    x • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * g i j) : Mx D m n).map (toEAf D) =
      (x * ((b ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) : EAf D) * ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D))) •
        g.map (eToEAf D) := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, toEAf_pair, eToEAf,
    Algebra.TensorProduct.includeLeftRingHom_apply]
  exact tmul_split _ b (g i j) α

end GlobalTheory.HalfScalarHat

open GlobalTheory.FunObj.HatFrame GlobalTheory.HalfScalarHat in
theorem GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)) (e : AE D), IsIdemSum e G.pl.W0 → ∀ α ∈ intAf D.host.F, ∀ b : D.host.E, (∀ w ∈ G.pl.W0, Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ))) → ∀ g ∈ M, e • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * g i j) : Mx D m n) ∈ hatMx (G.modul • M) := by
  intro D T L sc G m n M e he α hα b hb g hg
  obtain ⟨hinf, h1, h0⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_iff]
  refine ⟨fun i j => infPart_smul hinf _ i j, ?_⟩
  rw [map_toEAf_smul, smul_pair]
  have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ GlobalTheory.StdFrames.OA D :=
    Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩)
  obtain ⟨t, ht, hts⟩ := scalar_mem_idS G rfl h1 h0
    (fun w hw => by rw [GlobalTheory.FunObj.Comparison₂.cpt_tmul]; exact hb w hw) hα'
  rw [← hts]
  exact smul_map_mem_genGrp M G.modul hg ht
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAdelicGlueVectorOfSelfDualPrimitiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdelicGlueVector_of_selfDual_primitive : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsFullLattice D.host.E L₀ → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) → IsPrim Y z (glueLat Y X ι z u L₀ x₀) → IsGlueVec X u L₀ (vA X x₀) := by
  intro D u Y X ι z h L₀ x₀ hlat hSD hP
  letI := hlat
  exact GlobalTheory.AdIsom.SelfDualGlue.isGlueVec_of_isSDIn D u Y X ι z h L₀ x₀
    (by first | exact hlat | infer_instance) hSD hP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelLeStabilizerSelfDualLatticeFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.LevelInLatStab

theorem mulVec_mem_of_integral {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (e : A ≃+* B) (S : Subring B)
    (β : GL (Fin n) B) {P : AddSubgroup (Fin n → A)}
    (hP : ∀ z, z ∈ P ↔ ∀ i, ((β⁻¹).val *ᵥ fun i => e (z i)) i ∈ S) (m : Matrix (Fin n) (Fin n) A)
    (T : Matrix (Fin n) (Fin n) S) (hm : m.map e = β.val * T.map S.subtype * (β⁻¹).val) :
    ∀ z ∈ P, m *ᵥ z ∈ P := by
  intro z hz
  rw [hP] at hz ⊢
  intro i
  rw [GlobalTheory.LevelActionPinned.equiv_mulVec, hm, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, ← Matrix.mulVec_mulVec]
  exact Subring.sum_mem (t := Finset.univ) _ fun j _ => mul_mem (T i j).2 (hz j)

theorem lev_le_latLev : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 → Formalism.L2.DIV.lev D.sp.cm V.gram β L ≤ GlobalTheory.Mass.Levels.latLev V := by
  intro D V β Λ L hβ x hx
  have hp := Formalism.L2.DIV.lev_le_parLev hx
  have hUA := Formalism.L2.DIV.parLev_UA hp
  have hSt := Formalism.L2.DIV.parLev_St hp
  have hSD : Formalism.IndefR.Links.IsSDFrame V β Λ 1 := ⟨0, by rwa [pow_zero]⟩
  have hP : ∀ z, z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔
      ∀ i, ((β⁻¹).val *ᵥ fun i => GlobalTheory.LevelActionPinned.sw D (z i)) i ∈ GlobalTheory.LevelActionPinned.SI D := by
    intro z
    rw [← GlobalTheory.StdFrameCong.pj_latHat_eq]
    exact GlobalTheory.LevelActionPinned.mem_latHat_iff hSD z
  obtain ⟨t', ht'⟩ := (Formalism.L2.DIV.St β).inv_mem hSt
  obtain ⟨t, ht⟩ := hSt
  let u : UA D.sp.cm V.gram := ⟨x, hUA⟩
  let g := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).symm u
  have hg : ((GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g : UA D.sp.cm V.gram) : GL (Fin V.rank) (Lev.EAf D)) = x := by
    simp only [g, MulEquiv.apply_symm_apply, u]
  have hmat : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = x.val := by
    have h1 := congrArg Units.val (GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g)
    rw [← hg]
    exact h1.symm
  refine ⟨GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g, ⟨g, ?_, rfl⟩, hg⟩
  refine (GlobalTheory.Mass.Levels.mem_latStab V g).2 fun y => ?_
  constructor
  · intro hy
    exact mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP _ t.val
      (by rw [hmat, ← ht]; rfl) y hy
  · intro hy
    let m' := (x⁻¹).val.map (GlobalTheory.LevelActionPinned.sw D).symm
    have hm' : m'.map (GlobalTheory.LevelActionPinned.sw D) = (x⁻¹).val := by
      ext i j; simp only [m', Matrix.map_apply, RingEquiv.apply_symm_apply]
    have hinv : m' * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1 = 1 := by
      apply Matrix.map_injective (GlobalTheory.LevelActionPinned.sw D).injective
      have e := Matrix.map_mul (f := (GlobalTheory.LevelActionPinned.sw D).toRingHom) (L := m')
        (M := (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1)
      have e1 := Matrix.map_one (GlobalTheory.LevelActionPinned.sw D) (map_zero _) (map_one _) (n := Fin V.rank)
      refine (e.trans ?_).trans e1.symm
      change m'.map (GlobalTheory.LevelActionPinned.sw D) * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram g).1.map (GlobalTheory.LevelActionPinned.sw D) = 1
      rw [hm', hmat, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 := mulVec_mem_of_integral (GlobalTheory.LevelActionPinned.sw D) (GlobalTheory.LevelActionPinned.SI D) β hP m' t'.val
      (by rw [hm', ← ht']; rfl) _ hy
    rwa [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h2

end GlobalTheory.LevelInLatStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearMapChainCompositeUpdateSmulStatement
section
open GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearMapChainComposite_update_smul : ∀ {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ)
    (c : ℂ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) (n : ℕ), j₀ < n →
    chainTo (Function.update k j₀ (c • A)) n = c • chainTo (Function.update k j₀ A) n := by
  first | exact @GlobalTheory.ChainSmul.chainTo_update_smul | exact GlobalTheory.ChainSmul.chainTo_update_smul | (intros; apply GlobalTheory.ChainSmul.chainTo_update_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueCoordinatesInFrameLinearStabiliserStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueCoordinatesInFrame_linear_stabiliser : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), IsFrame β Λ → ∀ PP : Pl E, (∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∀ w ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP (v + w) = redV β PP v + redV β PP w) ∧ (∀ (c : Formalism.L2.Herm.intAf F E), ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP ((c : E ⊗[F] Formalism.L2.Herm.Af F) • v) = resS F PP c • redV β PP v) ∧ (∀ M ∈ St β, ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP ((M : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ v) = ((redFn β PP M : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) *ᵥ redV β PP v) := by
  exact @GlobalTheory.SeeConjGroup.redV_add_smul_stab
end

