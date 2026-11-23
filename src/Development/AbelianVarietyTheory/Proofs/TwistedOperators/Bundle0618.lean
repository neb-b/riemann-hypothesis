module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Formalism.FockGram.SymGramPosSemidef
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LawStep
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0599

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeDepthCompFrameBlockBoundedPeriodic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host
open Matrix

namespace GlobalTheory.DepthBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unit_bound {ι : Type} [Fintype ι] (f : ι → k) :
    ∃ R : kˣ, ∀ i, valuation k (f i) ≤ valuation k (R : k) := by
  classical
  let γ : ValueGroupWithZero k := ∏ i, max 1 (valuation k (f i))
  have h1 : 1 ≤ γ := Finset.one_le_prod' (fun i _ => le_max_left _ _)
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective γ
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact absurd (hx ▸ h1) (not_le.2 zero_lt_one)
  refine ⟨Units.mk0 x hx0, fun i => ?_⟩
  rw [Units.val_mk0, hx]
  exact (le_max_right _ _).trans
    (Finset.single_le_prod' (f := fun j => max 1 (valuation k (f j))) (fun j _ => le_max_left _ _) (Finset.mem_univ i))

theorem frameMatrixSecondColumnBlock_mul_transpose {A A' D : Type} [Fintype A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (σ : A ⊕ A' ≃ D) : Y0 k σ * (Y0 k σ)ᵀ = 1 := by
  ext i j
  rw [frameMatrixSecondColumnBlock_mul_apply]
  by_cases hij : i = j
  · subst hij; simp [Y0]
  · simp [Y0, Matrix.one_apply, hij, Ne.symm hij]

theorem latticeDepth_comp_frameBlock_bounded_periodic : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (σ : A ⊕ A' ≃ D) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → ∀ (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}, HasDepth ϖ e (diagLat c) Ψ → ∀ h : GL D k, ∃ R : kˣ, ∃ N : ℕ, (∀ g : Matrix A' A' k, Ψ (g * (Y0 k σ * h.val)) ≠ 0 → ∀ i j, valuation k (g i j) ≤ valuation k (R : k)) ∧ ∀ g Z : Matrix A' A' k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ N : kˣ) : k)) → Ψ ((g + Z) * (Y0 k σ * h.val)) = Ψ (g * (Y0 k σ * h.val)) := by
  intro k _ _ _ _ A A' D _ _ _ _ _ _ σ ϖ e hϖ c Ψ hΨ h
  set Y : Matrix A' D k := Y0 k σ * h.val with hYdef
  set W : Matrix D A' k := (h⁻¹).val * (Y0 k σ)ᵀ with hWdef
  have hYW : Y * W = 1 := by
    rw [hYdef, hWdef, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, frameMatrixSecondColumnBlock_mul_transpose]
  obtain ⟨R, hR⟩ := exists_unit_bound (fun p : D × A' => (c p.1 : k) * W p.1 p.2)
  obtain ⟨R', hR'⟩ := exists_unit_bound (fun p : A' × D => Y p.1 p.2 / (((ϖ ^ e) * c p.2 : kˣ) : k))
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hR'0 : valuation k (R' : k) ≠ 0 := by simp
  obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt (Units.mk0 (valuation k (R' : k))⁻¹ (inv_ne_zero hR'0))
  have hN' : valuation k (ϖ : k) ^ N * valuation k (R' : k) ≤ 1 := by
    have : valuation k (ϖ : k) ^ N ≤ (valuation k (R' : k))⁻¹ := by simpa using hN.le
    calc valuation k (ϖ : k) ^ N * valuation k (R' : k)
        ≤ (valuation k (R' : k))⁻¹ * valuation k (R' : k) := mul_le_mul' this le_rfl
      _ = 1 := inv_mul_cancel₀ hR'0
  refine ⟨R, N, ?_, ?_⟩
  · intro g hg i j
    have hmem : g * Y ∈ matLat A' (diagLat c) := by
      by_contra hc; exact hg (hΨ.1 _ hc)
    have hg' : g = (g * Y) * W := by rw [Matrix.mul_assoc, hYW, Matrix.mul_one]
    rw [hg', Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    calc valuation k ((g * Y) i l) * valuation k (W l j)
        ≤ valuation k (c l : k) * valuation k (W l j) := mul_le_mul' (mem_diagLat.1 (hmem i) l) le_rfl
      _ = valuation k ((c l : k) * W l j) := (map_mul _ _ _).symm
      _ ≤ valuation k (R : k) := hR (l, j)
  · intro g Z hZ
    rw [Matrix.add_mul]
    refine hΨ.2 _ _ fun i => ?_
    rw [smul_diagLat, mem_diagLat]
    intro m
    show valuation k ((Z * Y) i m) ≤ _
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    have hpos : 0 < valuation k ((((ϖ ^ e) * c m : kˣ)) : k) := zero_lt_iff.2 (by simp)
    have h1 := hR' (l, m)
    simp only at h1
    rw [map_div₀, div_le_iff₀ hpos] at h1
    have hz : valuation k (Z i l) ≤ valuation k (ϖ : k) ^ N := by
      simpa [Units.val_pow_eq_pow_val, map_pow] using hZ i l
    calc valuation k (Z i l) * valuation k (Y l m)
        ≤ valuation k (ϖ : k) ^ N * (valuation k (R' : k) * valuation k ((((ϖ ^ e) * c m : kˣ)) : k)) :=
          mul_le_mul' hz h1
      _ = (valuation k (ϖ : k) ^ N * valuation k (R' : k)) * valuation k ((((ϖ ^ e) * c m : kˣ)) : k) :=
          (mul_assoc _ _ _).symm
      _ ≤ 1 * valuation k ((((ϖ ^ e) * c m : kˣ)) : k) := mul_le_mul' hN' le_rfl
      _ = _ := one_mul _

end GlobalTheory.DepthBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftResMulSub
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.ColSubst

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem liftRes_mul_sub {A C : Type} [Fintype C] {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (T : A → C → Res k e)
    (N : Matrix C C 𝒪[k]) (i : A) (j : C) :
    valuation k ((liftRes (Matrix.of T * N.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e)) :
        A → C → Res k e) - liftRes T * N.map (fun x => (x : k))) i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) := by
  set r : 𝒪[k] := Quotient.out ((Matrix.of T * N.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e))) i j) -
    ∑ l, Quotient.out (T i l) * N l j with hr
  have h1 : ((liftRes (Matrix.of T * N.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e)) :
        A → C → Res k e) - liftRes T * N.map (fun x => (x : k))) i j) = (r : k) := by
    simp [hr, liftRes, Matrix.mul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, ← GlobalTheory.SplitFlip.Model.val_le_iff_mem hϖ, ← Ideal.Quotient.eq_zero_iff_mem, hr, map_sub, map_sum]
  simp [Matrix.mul_apply, Ideal.Quotient.mk_out]

theorem sum_liftRes_mul {A C : Type} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ)
    (N N' : Matrix C C 𝒪[k]) (hN : N * N' = 1) (F : Matrix A C k → ℂ)
    (hF : ∀ T Z : Matrix A C k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) → F (T + Z) = F T) :
    ∑ T : A → C → Res k e, F (liftRes T * N.map (fun x => (x : k))) = ∑ T : A → C → Res k e, F (liftRes T) := by
  classical
  set π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) with hπ
  let φ : (A → C → Res k e) → (A → C → Res k e) := fun T => Matrix.of T * N.map π
  have hinj : Function.Injective φ := by
    intro T T' h
    have h2 := congrArg (fun M : Matrix A C (Res k e) => M * N'.map π) h
    simp only [φ, Matrix.mul_assoc, ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero π) (map_one π),
      Matrix.mul_one] at h2
    exact h2
  have hbij : Function.Bijective φ := Finite.injective_iff_bijective.1 hinj
  rw [← hbij.sum_comp (fun T => F (liftRes T))]
  refine Finset.sum_congr rfl fun T _ => ?_
  symm
  rw [show liftRes (φ T) = liftRes T * N.map (fun x => (x : k)) +
    (liftRes (φ T) - liftRes T * N.map (fun x => (x : k))) by abel]
  exact hF _ _ fun i j => liftRes_mul_sub hϖ e T N i j

end GlobalTheory.ColSubst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFrameLatticeIffIntegralCoords
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
namespace GlobalTheory.SplitVacAlg

variable {D : D7}

def frameLat (V : HSp D) : Submodule (𝓞 D.host.E) V.V := Submodule.span (𝓞 D.host.E) (Set.range V.frame)

theorem frameLat_isLattice (V : HSp D) : Submodule.IsFullLattice D.host.E (frameLat V) := by
  refine Submodule.IsFullLattice.mk
    (toIsLattice := Submodule.IsLattice.of_fg D.host.E (Submodule.fg_span (Set.finite_range _))) ?_
  rw [frameLat, Submodule.span_span_of_tower]
  exact V.frame.span_eq

theorem frameLat_unimod (V : HSp D) (hV : V.gram = 1) : Formalism.HermitianLatticesTheory.IsUnimodular V.hT (frameLat V) := by
  have key := (Formalism.E.hermDual (𝓞 D.host.E) D.host.E V.V (Fin V.rank) V.hT V.frame
    (IsFractionRing.injective (𝓞 D.host.E) D.host.E)
    (fun s => ⟨⟨star (s : D.host.E), s.2.map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩)).2
    (1 : Matrix (Fin V.rank) (Fin V.rank) (𝓞 D.host.E)) (fun i j => by
      have := congrFun (congrFun hV i) j
      simp only [HSpace.gram] at this
      rw [this]
      by_cases h : i = j
      · subst h; simp
      · simp [h]) (by simp)
  exact key.2.2 (by simp)

def stdLatSp (V : HSp D) (hV : V.gram = 1) : HSp D :=
  { V with L0 := frameLat V, standardTuple_isLattice := (frameLat_isLattice V).toIsLattice, baseLattice_isUnimodular := frameLat_unimod V hV }

theorem mem_frameLattice_iff_integral_coords (V : HSp D) (hV : V.gram = 1) (y : Fin V.rank → D.host.E) :
    y ∈ L0c D (stdLatSp V hV) ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = y i := by
  change ∑ i, y i • V.frame i ∈ Submodule.span (𝓞 D.host.E) (Set.range V.frame) ↔ _
  rw [V.frame.mem_span_iff_repr_mem (𝓞 D.host.E), Module.Basis.repr_sum_self]
  rfl

end GlobalTheory.SplitVacAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacePartFixesStandardVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.OffPartVac

theorem unrOff_mu_locPl {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (j : Fin D.R.m) {e : AE D} (he : IsIdemSum e (locPl G t)) : Formalism.IndefR.Fin.UnrOff e (L.mu t ((j : ℕ) + 1)) := by

  have hbase : GlobalTheory.VecInv.UnrOff (e + cA D e) (L.mu0 ((j : ℕ) + 1)) := by
    refine GlobalTheory.ChrOff.unrOff_of_unrAt D _ (L.C.mu0 j) (locPl G t) e (hL.mu0 j) he ?_
    intro Q hQ hQc
    by_cases hg : ∀ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal
    · exact (L.C.isMu0 j).unr Q hg
    · exfalso
      push Not at hg
      obtain ⟨k, hk⟩ := hg
      have hk' := (GlobalTheory.FunObj.Good.natCast_mem_under Q (D.host.g k)).2 hk
      have hS1 : Q.under (𝓞 D.host.F) ∈ S1 D := by
        rw [GlobalTheory.ChiGrid.S1_mem_OmF]
        fin_cases k
        · exact Or.inl hk'
        · exact Or.inr (Or.inl hk')
      have hS0 : Q.under (𝓞 D.host.F) ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inr hS1)
      have hW0 : G.pl.w (Q.under (𝓞 D.host.F)) ∈ G.pl.W0 := by
        classical
        exact Finset.mem_image_of_mem _ hS0
      have hw : G.pl.w (Q.under (𝓞 D.host.F)) ∈ locPl G t := GlobalTheory.FunObj.GivenAdm.mem_locPl.2 (Or.inl hW0)
      rcases GlobalTheory.IdemSupport.eq_or_eq_cP (G.pl.under_w hS0).symm with h | h
      · exact hQ (by rw [h]; exact hw)
      · exact hQc _ hw ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 h)

  have htw : GlobalTheory.VecInv.UnrOff (e + cA D e) (L.xi t) := by
    refine GlobalTheory.ChrOff.unrOff_of_unrAt D _ (L.xiH t) (locPl G t) e (hL.xi t) he ?_
    intro Q hQ hQc
    by_contra hr
    rcases (hL.Q_ram t Q).1 hr with hq | ⟨Q', hQ', hc⟩
    · exact hQ (GlobalTheory.FunObj.GivenAdm.mem_locPl.2 (Or.inr hq))
    · exact hQc Q' (GlobalTheory.FunObj.GivenAdm.mem_locPl.2 (Or.inr hQ')) hc
  intro x h1 h2 h3 h4
  show (L.mu0 ((j : ℕ) + 1) * L.xi t) x = 1
  rw [MonoidHom.mul_apply, hbase x h1 h2 h3 h4, htw x h1 h2 h3 h4, one_mul]

private theorem cut_one_sub_eq_resG_one_sub_of_isIdempotentElem {D : D7} (V : HSp D) {ε : AF D.host.F} (hε : IsIdempotentElem ε) {f : AE D}
    (hf : algebraMap (AF D.host.F) (AE D) ε = f) (g : GA D V) :
    cutPart (1 - f) V g = Formalism.IndefR.Fin.LevelGroupLemmas.resG V (1 - ε) g := by
  have hid : IsIdempotentElem (1 - ε) := hε.one_sub
  have ha : algebraMap (AF D.host.F) (AE D) (1 - ε) = 1 - f := by rw [map_sub, map_one, hf]
  have h1 : (1 - f) * (1 - f) = 1 - f := by rw [← ha, ← map_mul, hid.eq]
  have h2 : cA D (1 - f) = 1 - f := by rw [← ha, GlobalTheory.IdemSupport.cA_algebraMap]
  apply Subtype.ext
  apply Units.ext
  change Formalism.L2.Theta.mt V _ = Formalism.L2.Theta.mt V _
  rw [mt_cutPart h1 h2, Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG' hid, ha]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem cut_conj_unipotent_mem_St_succ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m)
    (k : FinPt G (.top (j + 1))) (hk : finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj) {e : AE D}
    (he : IsIdemSum e (locPl G t)) :
    Lev.finE (G.V (.top (j + 1))) (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1)))
      ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))
      ∈ Formalism.L2.DIV.St ((Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)⁻¹ * S.βp (j + 1)) := by
  have hlev : finG (G.V (.top (j + 1))) k ∈ prodLev (S.βp (j + 1)) (locPl G t) _ _ := hk
  refine GlobalTheory.OffPartLattice.finE_cut_mem_St (G.V (.top (j + 1))) (S.βp (j + 1))
    (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (finG (G.V (.top (j + 1))) k) _ ?_ he ?_
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, finG, MonoidHom.comp_apply, Subgroup.coe_subtype]
  · intro Q hQ
    have h2 := (Subgroup.mem_inf.1 hlev).2
    exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 Q) hQ)


open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove GlobalTheory.OffPartLattice in
theorem offPart_fixes_vac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))), 1) (S.Z.vac (.top t (j + 1))) = S.Z.vac (.top t (j + 1)) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he

  have hv := S.Z.vac_is (.top t (j + 1)) hj
  unfold IsVacO at hv
  obtain ⟨_, hv2⟩ := hv
  obtain ⟨_, hθ, hlat, _, hcov, hnrm⟩ := hv2

  obtain ⟨⟨es, hes, hesum⟩, hc⟩ := id he
  have hε : IsIdempotentElem (Formalism.IndefR.Fin.LevelGroupLemmas.epsP (locPl G t)) :=
    Formalism.IndefR.Fin.LevelGroupLemmas.isIdempotentElem_placeIdempotent hes hesum hc _ subset_rfl
  have halg := Formalism.IndefR.Fin.LevelGroupLemmas.algebraMap_epsP hes hesum
  set ε := Formalism.IndefR.Fin.LevelGroupLemmas.epsP (locPl G t)
  have hid : IsIdempotentElem (1 - ε) := hε.one_sub

  have hle1 : j + 1 ≤ D.R.m := by omega
  have hle2 : j + 1 + 1 ≤ D.R.m := hj
  have hr1 := rank_top G hle1
  have hr2 := rank_top G hle2

  set V := G.V (.top (j + 1))
  set g : GA D V := (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D V)
  have hgf : g ∈ GfC V := ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))).2
  have hcut : cutPart (1 - (e + cA D e)) V g = Formalism.IndefR.Fin.LevelGroupLemmas.resG V (1 - ε) g :=
    cut_one_sub_eq_resG_one_sub_of_isIdempotentElem V hε halg g

  have hnodd : ¬ Odd (G.pS (Pair.top t (j + 1))).rank := by
    rw [Nat.not_odd_iff_even]
    change Even (G.V (.top (j + 1))).rank
    rw [hr1]
    exact rankX_even D _
  have hnodd' : ¬ Odd (G.pT (Pair.top t (j + 1))).rank := by
    rw [Nat.not_odd_iff_even]
    change Even (G.V (.top (j + 1 + 1))).rank
    rw [hr2]
    exact rankX_even D _
  have hmu : Formalism.IndefR.Fin.UnrOff e (L.mu t (j + 1 + 1)) := unrOff_mu_locPl G hL t ⟨j + 1, hj⟩ he
  have hchS : G.chrS (Pair.top t (j + 1)) = L.mu t (j + 1 + 1) := by
    simp only [GridData.chrS, Formalism.IndefR.Lift.attChr, hnodd, if_false]
    rfl
  have hchT : G.chrT (Pair.top t (j + 1)) = L.mu t (j + 1 + 1) := by
    simp only [GridData.chrT, Formalism.IndefR.Lift.attChr, hnodd', if_false]
    rfl

  have hfrS := isFrame_moved (S.N.latS (Pair.top t (j + 1))) (G.Λ (.top (j + 1))) (S.βp (j + 1))
    (Lev.finE V (S.N.u (.top (j + 1))).1) (S.βp_is (j + 1) hle1) (S.N.u_lat (.top (j + 1)) hle1)
  have hfrT := isFrame_moved (S.N.latT (Pair.top t (j + 1))) (G.Λ (.top (j + 1 + 1))) (S.βp (j + 1 + 1))
    (Lev.finE (G.V (.top (j + 1 + 1))) (S.N.u (.top (j + 1 + 1))).1) (S.βp_is (j + 1 + 1) hle2)
    (S.N.u_lat (.top (j + 1 + 1)) hle2)
  have hst := cut_conj_unipotent_mem_St_succ S j hj k hk he

  have hVF := Formalism.IndefR.Fin.LevelGroupLemmas.vacFixOff (Formalism.IndefR.Fin.splitLinF D) (Formalism.IndefR.Fin.placeModelAtF D)
    (Formalism.IndefR.Fin.splitOrInert D)
  have hW := W.om_is (Pair.top t (j + 1)) hle2
  refine hVF W.ψ _ _ _ _ _ hW (GlobalTheory.InertAll.inertAllO D _ _ _ _ _ _ hW) ?_ ?_ _ _
    (GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ hle1))
    (GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ hle2))
    _ _ hfrS hfrT (locPl G t) e he (by rw [hchS]; exact hmu) (by rw [hchT]; exact hmu) _ hθ hlat ?_ _ 1 ?_
    (Subgroup.one_mem _) hst (by rw [map_one]; exact Subgroup.one_mem _) ?_ ?_
  · change (G.V (.top (j + 1))).rank ≠ (G.V (.top (j + 1 + 1))).rank
    rw [hr1, hr2]
    unfold GlobalTheory.ChiGrid.rankX
    rw [add_mul (j + 1) 1, one_mul]
    generalize (j + 1) * (D.R.t + 1) = a
    omega
  · left
    change Even (G.V (.top (j + 1))).rank
    rw [hr1]
    exact rankX_even D _
  · obtain ⟨⟨μ, 𝓕⟩, hμ⟩ := hcov
    exact ⟨μ, 𝓕, hμ, hnrm ⟨μ, 𝓕⟩ hμ⟩
  · change cutPart (1 - (e + cA D e)) V g ∈ GfC V
    rw [hcut]
    exact Formalism.IndefR.Fin.LevelGroupLemmas.resG_mem_GfC V hid hgf
  · intro i j'
    change (e + cA D e) * (Formalism.L2.Theta.mt V (cutPart (1 - (e + cA D e)) V g) - 1) i j' = 0
    rw [hcut, Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG_sub hid, ← mul_assoc, ← halg, ← map_mul, mul_sub, mul_one, hε.eq,
      sub_self, map_zero, zero_mul]
  · intro i j'
    simp [Formalism.L2.Theta.mt]

end GlobalTheory.OffPartVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmFockCompact
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem om_fock_chi {μ0 : T} (hL : L.Is μ0) (W : G.Weil) {U : Set T} (S : GridChoice W U)
    (g : Gc D.what₂.Tau (rowSizes D)) (t : T) (i : Fin D.R.m)
    (d : FinDatum G t (.chi i D.R.m)) (hd : S.Z.HasVec d)
    (Q Q' : PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank)
    (hQ : trRow G i Q' = colFock (rowEntries D sc.cGap) i g (trRow G i Q)) :
    W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (ptGrid W g i) (ptGrid W g (i + 1)))
        (W.fock (.chi i D.R.m) (movedVec t S d) Q) =
      W.fock (.chi i D.R.m) (movedVec t S d) Q' := by
  have hX : DefNode D.R.m (.grid (i : ℕ) D.R.m) := ⟨i.2.le, rfl⟩
  have hY : DefNode D.R.m (.grid ((i : ℕ) + 1) D.R.m) := ⟨i.2, rfl⟩
  have hp : DefPair D.R.m (Pair.chi (i : ℕ) D.R.m : Pair T) := ⟨i.2, rfl⟩
  obtain ⟨hf, hv⟩ := _root_.GlobalTheory.RowReal.movedVec_theta_fockVac W S t (.chi i D.R.m) hp d hd
  have hc := _root_.GlobalTheory.RowReal.om_ptGrid_movedVec hL W S g t i d hd
  let u : UG D.what₂.Tau ((rowSizes D).nC (i : ℕ)) := g.2 ⟨(i : ℕ), Nat.lt_succ_of_lt i.2⟩
  let v : UG D.what₂.Tau ((rowSizes D).nC ((i : ℕ) + 1)) := g.2 ⟨(i : ℕ) + 1, Nat.succ_lt_succ i.2⟩
  have c1 : ∀ τ, compAt W.θ τ (mt (G.V (.grid ((i : ℕ) + 1) D.R.m)) (ptGrid W g ((i : ℕ) + 1))) =
      W.onb (.grid ((i : ℕ) + 1) D.R.m) τ * (v τ).1.submatrix
        (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) *
        (W.onb (.grid ((i : ℕ) + 1) D.R.m) τ)⁻¹ := fun τ => by
    rw [ptGrid_le W g (Nat.succ_lt_succ i.2)]
    exact compAt_kappa_snd g ⟨(i : ℕ) + 1, Nat.succ_lt_succ i.2⟩ (posOnb_of_defNode W μ0 hL hY) τ
  have c1' : ∀ τ, compAt W.θ τ (mt (negSp (G.V (.grid ((i : ℕ) + 1) D.R.m)))
      (negGA (G.V (.grid ((i : ℕ) + 1) D.R.m)) (ptGrid W g ((i : ℕ) + 1)))) =
      W.onb (.grid ((i : ℕ) + 1) D.R.m) τ * (v τ).1.submatrix
        (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) *
        (W.onb (.grid ((i : ℕ) + 1) D.R.m) τ)⁻¹ := fun τ => by
    rw [mt_negGA]; exact c1 τ
  have c2 : ∀ τ, compAt W.θ τ (mt (G.V (.grid (i : ℕ) D.R.m)) (ptGrid W g i)) =
      W.onb (.grid (i : ℕ) D.R.m) τ * (u τ).1.submatrix
        (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)) (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)) *
        (W.onb (.grid (i : ℕ) D.R.m) τ)⁻¹ := fun τ => by
    rw [ptGrid_le W g (Nat.lt_succ_of_lt i.2)]
    exact compAt_kappa_snd g ⟨(i : ℕ), Nat.lt_succ_of_lt i.2⟩ (posOnb_of_defNode W μ0 hL hX) τ
  have key := _root_.GlobalTheory.RowReal.om_fock_compact_all W (.chi i D.R.m) ⟨i.2, le_rfl⟩ (fun _ => 0) (fun _ => (G.V (.grid (i : ℕ) D.R.m)).rank)
    (fun _ => Nat.zero_le _) (fun _ => le_rfl) (fun ρ => (_root_.GlobalTheory.RowReal.defNode_cart_onb_all hL W _ hY ρ).2.2.1) (fun ρ => (_root_.GlobalTheory.RowReal.defNode_cart_onb_all hL W _ hX ρ).1)
    (fun ρ => (_root_.GlobalTheory.RowReal.defNode_cart_onb_all hL W _ hY ρ).2.2.2) (fun ρ => (_root_.GlobalTheory.RowReal.defNode_cart_onb_all hL W _ hX ρ).2.1) _ hf hv
    (fun τ => (v τ).1.submatrix (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)))
    (fun τ => (u τ).1.submatrix (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)) (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)))
    (fun ρ => isKMat_cast _ _ (Or.inr rfl)) (fun ρ => isKMat_cast _ _ (Or.inl rfl))
    (negGA _ (ptGrid W g ((i : ℕ) + 1))) (ptGrid W g i) (GlobalTheory.FockReal.negGA_mem_GinfC _ (ptGrid_mem W g _)) (ptGrid_mem W g _)
    c1' c2 _ hc Q
  have hQ' : Q' = colScal (rowEntries D sc.cGap) i g • fockSubAll (fun _ => 0)
      (fun _ => (G.V (.grid (i : ℕ) D.R.m)).rank)
      (fun τ => (v τ).1.submatrix (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)))
      (fun τ => (u τ).1.submatrix (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)) (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)))
      Q := by
    apply trRow_injective G i
    rw [hQ, map_smul, GlobalTheory.T.fockSubstitution_columnStep_rename_conj G i u v Q]
    rfl
  exact key.trans (by rw [hQ', LinearMap.map_smul])

end GlobalTheory.RowReal
end
end

