module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0571
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section
namespace GlobalTheory.LocVacFix

theorem bad_finite (F : Type) [Field F] [NumberField F] :
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) | differentIdeal ℤ (𝓞 F) ≤ v.asIdeal ∨ (6 : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have hd : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) | v.asIdeal ∣ differentIdeal ℤ (𝓞 F)}.Finite :=
    Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  have h6 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) | v.asIdeal ∣ Ideal.span {(6 : 𝓞 F)}}.Finite := by
    refine Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (show ((6 : ℕ) : 𝓞 F) ≠ 0 from Nat.cast_ne_zero.mpr (by norm_num))
  refine (hd.union h6).subset ?_
  rintro v (hv | hv)
  · exact Or.inl (Ideal.dvd_iff_le.mpr hv)
  · exact Or.inr (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hv))

theorem two_three_of_six {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (h6 : (6 : 𝓞 F) ∉ v.asIdeal) : (2 : 𝓞 F) ∉ v.asIdeal ∧ 3 < Ideal.absNorm v.asIdeal := by
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := by
    intro h
    apply h6
    have e : (6 : 𝓞 F) = 3 * 2 := by norm_num
    rw [e]
    exact v.asIdeal.mul_mem_left 3 h
  refine ⟨h2, ?_⟩
  have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have hz : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have ho : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  by_contra hle
  push_neg at hle
  generalize hN : Ideal.absNorm v.asIdeal = N at hmem hz ho hle
  interval_cases N
  · exact hz rfl
  · exact ho rfl
  · exact h2 (by exact_mod_cast hmem)
  · apply h6
    have e : (6 : 𝓞 F) = 2 * 3 := by norm_num
    rw [e]
    exact v.asIdeal.mul_mem_left 2 (by exact_mod_cast hmem)

theorem vac_fixed_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal → 3 < Ideal.absNorm v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hsp hvT hψ h2 h3 k hk
  obtain ⟨hSB, hne, θ, hθ, heig⟩ := hT.geo.hM.vac v
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW F E σ B a a' G X om om' hT v k hk.1 (G.M.vac v) hSB
  have heig₁ := GlobalTheory.T.weilOperator_latticeStabiliser_right_preserves_vacuumType F E σ B a a' G X om om' hT v k hk θ hθ (G.M.vac v) hSB φ₁ hφ₁ heig hact
  obtain ⟨c, hc⟩ := GlobalTheory.T.heisenbergSelfDualLattice_fixedFunctions_line F E σ B a a' G X om om' hT v hψ
    (GlobalTheory.PsiUnrSelfDual.latAtV_selfDual F E σ B a a' G X om om' hT v hψ) θ hθ (G.M.vac v) hSB hne heig
    φ₁ hφ₁ heig₁
  subst hc
  have hc1 : c = 1 := GlobalTheory.SplitVac.eigen_eq_one F E σ B a a' G X om om' hT v hsp hvT hψ h2 h3 k hk c hact
  rw [hc1, one_smul] at hact
  exact hact

end GlobalTheory.LocVacFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationAAModulusDivConjLeCosetExponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.ShiftVal

open scoped Pointwise

theorem valuation_le_of_mem {K : Type} [Field K] [NumberField K] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {I : FractionalIdeal (𝓞 K)⁰ K} {b : K} (hb : b ∈ I) :
    w.valuation K b ≤ WithZero.exp (-FractionalIdeal.count K w I) := by
  by_cases hb0 : b = 0
  · rw [hb0, map_zero]; exact zero_le'
  have h1 : FractionalIdeal.count K w I ≤ FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ b) :=
    FractionalIdeal.count_mono K w (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hb0)
      ((FractionalIdeal.spanSingleton_le_iff_mem).mpr hb)
  rw [ReciprocityTheory.Neutral.Bridge.HCFR.count_spanSingleton K w hb0] at h1
  have hv : w.valuation K b ≠ 0 := (map_ne_zero _).mpr hb0
  rw [← WithZero.exp_log hv, WithZero.exp_le_exp]
  omega

theorem val_le_cosExp : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts}
    (G : GridData L sc), ∀ w ∈ G.pl.W0, ∀ b ∈ D.host.AA * shiftId G,
      Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ)) := by
  intro D hq T L μ0 hL sc G w hw b hb
  classical
  have hM : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact G.pl.modul_ne_bot sc
  have hMb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    unfold Places.modulBar
    intro h
    apply G.pl.modul_ne_bot sc
    have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
    simpa [smul_smul] using this
  have hwl : w ∈ locPl G μ0 := by unfold locPl; exact Finset.mem_union_left _ hw
  have hc : FractionalIdeal.count D.host.E w (shiftId G) = cosExp G w := by
    show FractionalIdeal.count D.host.E w
      (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) *
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹) = _
    rw [FractionalIdeal.count_mul _ _ hM (inv_ne_zero hMb), FractionalIdeal.count_inv,
      count_modul, count_modulBar G hwl, neg_zero, add_zero]
  rw [Good.valued_alg]
  refine FractionalIdeal.mul_induction_on hb ?_ ?_
  · intro a ha s hs
    rw [map_mul]
    have h1 := GlobalTheory.DepthFix.aa_int hL hq G hw a ha
    rw [Good.valued_alg] at h1
    have h2 := valuation_le_of_mem w hs
    rw [hc] at h2
    calc _ ≤ 1 * WithZero.exp (-(cosExp G w : ℤ)) := mul_le_mul' h1 h2
      _ = _ := one_mul _
  · intro x y hx hy
    exact Valuation.map_add_le _ hx hy

end GlobalTheory.AscFin.ShiftVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompactRealPointFockVectorSubstitution
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowReal

section FockAll

open Classical

variable {D : D7}

def fockSubOn {m n : ℕ} (s : Finset D.what₂.Tau) (pS pT : D.what₂.Tau → ℕ) (κS : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (κT : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) : MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m n) ℂ :=
  MvPolynomial.aeval fun y : FVar D m n =>
    if y.1 ∈ s then
      ∑ i, ∑ j, MvPolynomial.C (if (y.2.1.val < pT y.1 ↔ y.2.2.val < pS y.1) then κT y.1 i y.2.1 * (κS y.1)⁻¹ y.2.2 j
        else (starRingEnd ℂ) (κT y.1 i y.2.1 * (κS y.1)⁻¹ y.2.2 j)) * MvPolynomial.X (y.1, i, j)
    else MvPolynomial.X y

variable {m n : ℕ} (pS pT : D.what₂.Tau → ℕ) (κS : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (κT : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)

theorem fockSubOn_empty (Q : MvPolynomial (FVar D m n) ℂ) : fockSubOn ∅ pS pT κS κT Q = Q := by
  have e : fockSubOn (∅ : Finset D.what₂.Tau) pS pT κS κT = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [fockSubOn, MvPolynomial.aeval_X, Finset.notMem_empty, if_false, AlgHom.id_apply]
  rw [e, AlgHom.id_apply]

theorem fockSubOn_univ : fockSubOn Finset.univ pS pT κS κT = fockSubAll pS pT κS κT := by
  apply MvPolynomial.algHom_ext
  intro y
  simp only [fockSubOn, fockSubAll, MvPolynomial.aeval_X, Finset.mem_univ, if_true]

theorem fockSub_fockSubOn {τ : D.what₂.Tau} {s : Finset D.what₂.Tau} (hτ : τ ∉ s) (Q : MvPolynomial (FVar D m n) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub τ (pS τ) (pT τ) (κS τ) (κT τ) (fockSubOn s pS pT κS κT Q) =
      fockSubOn (insert τ s) pS pT κS κT Q := by
  suffices e : (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub τ (pS τ) (pT τ) (κS τ) (κT τ)).comp (fockSubOn s pS pT κS κT) =
      fockSubOn (insert τ s) pS pT κS κT from DFunLike.congr_fun e Q
  apply MvPolynomial.algHom_ext
  intro y
  rw [AlgHom.comp_apply]
  by_cases hy : y.1 ∈ s
  · have hne : y.1 ≠ τ := fun h => hτ (h ▸ hy)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [fockSubOn, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub, MvPolynomial.aeval_X, Finset.mem_insert, hy, if_true, or_true,
      map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, hne, if_false]
  · by_cases h2 : y.1 = τ
    · obtain ⟨ρ, a, b⟩ := y
      simp only at h2 hy
      subst h2
      simp only [fockSubOn, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub, MvPolynomial.aeval_X, Finset.mem_insert, hy, if_false, true_or,
        if_true]
    · simp only [fockSubOn, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockSub, MvPolynomial.aeval_X, Finset.mem_insert, hy, h2, if_false,
        or_false]

theorem om_pureTensorO_compact_all (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.OmT S T) (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (pS pT : D.what₂.Tau → ℕ) (hpS : ∀ ρ, pS ρ ≤ S.rank) (hpT : ∀ ρ, pT ρ ≤ T.rank)
    (hS : ∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) (hT : ∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ))
    (hBS : ∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) (hBT : ∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ))
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (hvac : ∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f)
    (κS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (κT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hκS : ∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pS ρ) (κS ρ)) (hκT : ∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pT ρ) (κT ρ))
    (x : GA D S) (y : GA D T) (hx : x ∈ GinfC S) (hy : y ∈ GinfC T)
    (hxc : ∀ ρ, compAt θ ρ (mt S x) = BS ρ * κS ρ * (BS ρ)⁻¹)
    (hyc : ∀ ρ, compAt θ ρ (mt T y) = BT ρ * κT ρ * (BT ρ)⁻¹)
    (c : ℂ) (hc : om (x, y) f = c • f) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    om (x, y) (pureTensorO ψ θ S T sS sT BS BT f Q) =
      c • pureTensorO ψ θ S T sS sT BS BT f (fockSubAll pS pT κS κT Q) := by
  have hUS : ∀ ρ, compAt θ ρ (mt S x) ∈ Formalism.QuantumDeterminants.UH (gramAt D S ρ) := fun ρ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S x ρ
  have hUT : ∀ ρ, compAt θ ρ (mt T y) ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := fun ρ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ T y ρ
  have hAS : ∀ τ, IsAtTau θ S τ (BS τ * κS τ * (BS τ)⁻¹) (atTau θ S τ (compAt θ τ (mt S x))) := fun τ => by
    rw [← hxc τ]; exact GlobalTheory.PointAtPlaceHom.atTau_spec hθ S τ (hUS τ)
  have hAT : ∀ τ, IsAtTau θ T τ (BT τ * κT τ * (BT τ)⁻¹) (atTau θ T τ (compAt θ τ (mt T y))) := fun τ => by
    rw [← hyc τ]; exact GlobalTheory.PointAtPlaceHom.atTau_spec hθ T τ (hUT τ)
  have hev : ∀ τ, ∃ e : ℂ, om (atTau θ S τ (compAt θ τ (mt S x)), atTau θ T τ (compAt θ τ (mt T y))) f = e • f :=
    fun τ => by
      obtain ⟨mS, mT, h⟩ := GlobalTheory.VacCharAtPlace.vacuum_char_at_place D ψ θ S T χS χT om hom hθ τ
      exact ⟨_, h sS BS sT BT pS pT hpS hpT hS hT hBS hBT f hf hvac (κS τ) (κT τ) (hκS τ) (hκT τ) _ _ (hAS τ) (hAT τ)⟩
  choose e he using hev
  let MSs : Finset D.what₂.Tau → D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ :=
    fun s ρ => if ρ ∈ s then compAt θ ρ (mt S x) else 1
  let MTs : Finset D.what₂.Tau → D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ :=
    fun s ρ => if ρ ∈ s then compAt θ ρ (mt T y) else 1
  have hUSs : ∀ s ρ, MSs s ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D S ρ) := fun s ρ => by
    by_cases h : ρ ∈ s
    · simp only [MSs, if_pos h]; exact hUS ρ
    · simp only [MSs, if_neg h]; exact GlobalTheory.PointAtPlaceHom.one_mem_UH _
  have hUTs : ∀ s ρ, MTs s ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := fun s ρ => by
    by_cases h : ρ ∈ s
    · simp only [MTs, if_pos h]; exact hUT ρ
    · simp only [MTs, if_neg h]; exact GlobalTheory.PointAtPlaceHom.one_mem_UH _
  have key : ∀ s : Finset D.what₂.Tau, ∀ Q, om (realAll θ S (MSs s), realAll θ T (MTs s)) (pureTensorO ψ θ S T sS sT BS BT f Q) =
      (∏ τ ∈ s, e τ) • pureTensorO ψ θ S T sS sT BS BT f (fockSubOn s pS pT κS κT Q) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro Q
      have h1 : MSs ∅ = 1 := by funext ρ; simp [MSs]
      have h2 : MTs ∅ = 1 := by funext ρ; simp [MTs]
      rw [h1, h2, realAll_one hθ, realAll_one hθ, Prod.mk_one_one, map_one, Module.End.one_apply, Finset.prod_empty,
        one_smul, fockSubOn_empty]
    · intro τ s hτ ih Q
      have eS : realAll θ S (MSs (insert τ s)) = atTau θ S τ (compAt θ τ (mt S x)) * realAll θ S (MSs s) := by
        rw [realAll_eq_atTau_mul hθ (hUSs (insert τ s)) τ]
        congr 2
        · simp [MSs]
        · funext ρ
          by_cases h : ρ = τ
          · subst h; simp [MSs, hτ]
          · simp [MSs, Function.update_of_ne h, h]
      have eT : realAll θ T (MTs (insert τ s)) = atTau θ T τ (compAt θ τ (mt T y)) * realAll θ T (MTs s) := by
        rw [realAll_eq_atTau_mul hθ (hUTs (insert τ s)) τ]
        congr 2
        · simp [MTs]
        · funext ρ
          by_cases h : ρ = τ
          · subst h; simp [MTs, hτ]
          · simp [MTs, Function.update_of_ne h, h]
      rw [eS, eT, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, ih Q, map_smul,
        GlobalTheory.FockCompact.om_pureTensorO_compact D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hpS hpT hS hT hBS hBT f hf τ
          (κS τ) (κT τ) (hκS τ) (hκT τ) _ _ (hAS τ) (hAT τ) (e τ) (he τ),
        smul_smul, fockSub_fockSubOn pS pT κS κT hτ, Finset.prod_insert hτ, mul_comm (e τ)]
  have hxr : realAll θ S (MSs Finset.univ) = x :=
    realAll_eq hθ (hUSs _) ⟨hx, fun ρ => by simp only [MSs, Finset.mem_univ, if_true]; rfl⟩
  have hyr : realAll θ T (MTs Finset.univ) = y :=
    realAll_eq hθ (hUTs _) ⟨hy, fun ρ => by simp only [MTs, Finset.mem_univ, if_true]; rfl⟩
  have hall := key Finset.univ
  rw [hxr, hyr, fockSubOn_univ] at hall
  have hE : om (x, y) f = (∏ τ, e τ) • f := by
    have h1 := hall 1
    rw [map_one (fockSubAll pS pT κS κT)] at h1
    simpa only [GlobalTheory.FiniteFock.pureTensorO_one] using h1
  rw [hall Q]
  by_cases hf0 : f = 0
  · subst hf0
    have z : ∀ P, pureTensorO ψ θ S T sS sT BS BT 0 P = 0 := fun P => by
      have := GlobalTheory.FiniteFock.pureTensorO_smul ψ θ S T sS sT BS BT 0 0 P
      rwa [zero_smul, zero_smul] at this
    simp only [z, smul_zero]
  · have hce : c = ∏ τ, e τ := smul_left_injective ℂ hf0 (hc.symm.trans hE)
    rw [hce]

end FockAll

theorem om_fock_compact_all : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (p : Pair T), p.InRange D.R.m →
    ∀ (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ (G.pS p).rank) → (∀ ρ, pT ρ ≤ (G.pT p).rank) →
    (∀ ρ, IsCartanInv (gramAt D (G.pS p) ρ) (G.cartS W.cart p ρ)) →
    (∀ ρ, IsCartanInv (gramAt D (G.pT p) ρ) (G.onT W.cart p ρ)) →
    (∀ ρ, IsONBasis (gramAt D (G.pS p) ρ) (G.cartS W.cart p ρ) (G.onS W.onb p ρ) (pS ρ)) →
    (∀ ρ, IsONBasis (gramAt D (G.pT p) ρ) (G.onT W.cart p ρ) (G.onT W.onb p ρ) (pT ρ)) →
    ∀ f : WO (G.pS p) (G.pT p) → ℂ, IsThetaFunO W.ψ _ _ f →
    (∀ ρ, IsFockVacAt (heisO W.ψ _ _) W.θ ρ (cplxO (G.cartS W.cart p ρ) (G.onT W.cart p ρ)) f) →
    ∀ (κS : D.what₂.Tau → Matrix (Fin (G.pS p).rank) (Fin (G.pS p).rank) ℂ)
      (κT : D.what₂.Tau → Matrix (Fin (G.pT p).rank) (Fin (G.pT p).rank) ℂ),
    (∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pS ρ) (κS ρ)) → (∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pT ρ) (κT ρ)) →
    ∀ (x : GA D (G.pS p)) (y : GA D (G.pT p)), x ∈ GinfC (G.pS p) → y ∈ GinfC (G.pT p) →
    (∀ ρ, compAt W.θ ρ (mt _ x) = G.onS W.onb p ρ * κS ρ * (G.onS W.onb p ρ)⁻¹) →
    (∀ ρ, compAt W.θ ρ (mt _ y) = G.onT W.onb p ρ * κT ρ * (G.onT W.onb p ρ)⁻¹) →
    ∀ c : ℂ, W.om p (x, y) f = c • f → ∀ Q : PolF D (G.pT p).rank (G.pS p).rank,
    W.om p (x, y) (W.fock p f Q) = c • W.fock p f (GlobalTheory.RowReal.fockSubAll pS pT κS κT Q) := by
  intro D T L sc G W p hp pS pT hpS hpT hS hT hBS hBT f hf hvac κS κT hκS hκT x y hx hy hxc hyc c hc Q
  exact om_pureTensorO_compact_all D W.ψ W.θ (G.pS p) (G.pT p) (G.chrS p) (G.chrT p) (W.om p) (W.om_is p hp) W.θ_is
    (G.cartS W.cart p) (G.onS W.onb p) (G.onT W.cart p) (G.onT W.onb p) pS pT hpS hpT hS hT hBS hBT f hf hvac κS κT hκS hκT
    x y hx hy hxc hyc c hc Q

end GlobalTheory.RowReal
end
end

