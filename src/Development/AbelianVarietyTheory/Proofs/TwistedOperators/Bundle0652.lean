module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0641
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2776
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0602
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeColumnsOffFiniteSet
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0649

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdditiveCharacterSuperdiagTrivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

theorem GlobalTheory.AscFin.psiE_superdiag_S0 : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → ∀ v : GlobalTheory.FinPl.Pl D, v ∈ G.pl.S0 → ∀ o ∈ intAt D (· = v), psiE W.ψ (o * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) = 1 := by
  intro D hQ T L μ0 hL sc G W Mv hM F hF ρ h M hMr i j hij v hv o ho
  have hAA : (D.host.AA : GlobalTheory.SeeSaw.FI D) ≠ 0 := GlobalTheory.HostAAPartition.host_AA_ne_zero D
  have hm : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.AscFin.PrimStd.modulBar_ne_bot G.pl sc)
  have hsh : shiftId G ≠ 0 := mul_ne_zero hm (inv_ne_zero hmB)
  have h1 := _root_.GlobalTheory.AscFin.coef_superdiag D hQ T L μ0 hL sc G W Mv hM F hF ρ h M _ (inv_ne_zero hAA) v
    (_root_.GlobalTheory.AscFin.RowAAUnit.smul_mulVec_mem_latV D hQ T L μ0 hL sc G W Mv hM F hF ρ h M hMr v) i j hij
  have h2 := _root_.GlobalTheory.AscFin.coef_superdiag D hQ T L μ0 hL sc G W Mv hM F hF ρ h M _ (mul_ne_zero (inv_ne_zero hAA) (inv_ne_zero hsh)) v
    (_root_.GlobalTheory.AscFin.shiftRow_smul_mulVec_mem D hQ T L μ0 hL sc G W Mv hM F hF ρ h M hMr v) i j hij
  have e1 : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * G.pl.stAbar sc * (D.host.AA : GlobalTheory.SeeSaw.FI D)⁻¹⁻¹ =
      GlobalTheory.SeeSaw.dI D * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := by
    unfold Places.stAbar GlobalTheory.SeeSaw.dI
    rw [inv_inv]
    ring
  have e2 : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * G.pl.stAbar sc *
      ((D.host.AA : GlobalTheory.SeeSaw.FI D)⁻¹ * (shiftId G)⁻¹)⁻¹ =
      GlobalTheory.SeeSaw.dI D * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := by
    unfold Places.stAbar GlobalTheory.SeeSaw.dI shiftId
    rw [mul_inv, inv_inv, inv_inv]
    field_simp
  rw [e1] at h1
  rw [e2] at h2
  have hx := _root_.GlobalTheory.ModulInter.mem_idV_of_inter G.pl sc v _ _ h1 h2
  have hxA : GlobalTheory.FinPlLoc.idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  have hψ := ((_root_.GlobalTheory.SeeSaw.idV_props D W.ψ W.ψ_std v).2.2.2.2.1 _ hxA).1 hx o ho
  have ho' : GlobalTheory.FinPlLoc.idem D (· = v) * o = o := (GlobalTheory.FinPlLoc.mem_idAt_iff _ o).1 ho.1
  rw [← ho']
  rw [← hψ]
  congr 1
  ring

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFirstStepAdjointLineComponentMemLatO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LineAdjZero

open GlobalTheory.AdjLatO GlobalTheory.LineCompLat

variable {D : D7}

theorem genT_smul_left (T : HSp D) {n : ℕ} (x : AF D.host.F) (c : D.host.E) (t : Fin T.rank → D.host.E)
    (u : Fin n → D.host.E) : genT T x (c • t) u = genT T x t (star c • u) := by
  ext p q
  simp only [genT, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem genT_add_left (T : HSp D) {n : ℕ} (x : AF D.host.F) (t t' : Fin T.rank → D.host.E)
    (u : Fin n → D.host.E) : genT T x (t + t') u = genT T x t u + genT T x t' u := by
  ext p q
  simp only [genT, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib, mul_add,
    TensorProduct.tmul_add]

theorem genT_zero_left (T : HSp D) {n : ℕ} (x : AF D.host.F) (u : Fin n → D.host.E) :
    genT T x 0 u = 0 := by
  ext p q
  simp [genT]

theorem latO_idLat_le (S T : HSp D) (LS : Lat S) (LT : Lat T) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (hI : ∀ σ ∈ I, ∀ τ ∈ I, ∃ c : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E c = star σ * τ) (P : GlobalTheory.FinPl.Pl D → Prop) :
    latO S T (idLat I LS : Set _) (idLat I LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  have hσ : ∀ σ ∈ I, ∀ t ∈ idLat I LT, star σ • t ∈ LT := by
    intro σ hσ t ht
    unfold idLat at ht
    induction ht using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨τ, hτ, y, hy, rfl⟩ := hz
      obtain ⟨c, hc⟩ := hI σ hσ τ hτ
      rw [smul_smul, ← hc, algebraMap_smul]
      exact LT.smul_mem c hy
    | zero => rw [smul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [smul_comm]; exact LT.smul_mem r hy
  have key : ∀ t ∈ idLat I LT, genT S (pairA D.host.F 0 α) s (a • t) ∈ latO S T (LS : Set _) (LT : Set _) P := by
    have hs' : s ∈ Submodule.span (𝓞 D.host.E) {z | ∃ s ∈ I, ∃ y ∈ LS, z = s • y} := hs
    clear hs
    induction hs' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨σ, hσI, y, hy, rfl⟩ := hz
      intro t ht
      rw [genT_smul_left, smul_comm]
      exact genT_mem_of_mem_span T S LT LS P α hα hP y hy _
        (Submodule.subset_span ⟨a, ha, _, hσ σ hσI t ht, rfl⟩)
    | zero => intro t _; rw [genT_zero_left]; exact zero_mem _
    | add y z _ _ hy hz => intro t ht; rw [genT_add_left]; exact add_mem (hy t ht) (hz t ht)
    | smul r y _ hy =>
      intro t ht
      obtain ⟨r', hr'⟩ := GlobalTheory.FinPl.LatMem.star_int r
      have e1 : r • y = (r : D.host.E) • y := (algebraMap_smul D.host.E r y).symm
      have e2 : (r' : D.host.E) • t = r' • t := algebraMap_smul D.host.E r' t
      rw [e1, genT_smul_left, smul_comm, ← hr', e2]
      exact hy _ (Submodule.smul_mem _ r' ht)
  exact key t ht

theorem star_mul_shiftId {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    ∀ σ ∈ shiftId G, ∀ τ ∈ shiftId G, ∃ c : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E c = star σ * τ := by
  intro σ hσ τ hτ
  have h1 : star σ ∈ (shiftId G)⁻¹ := by
    rw [← GlobalTheory.RowBig.conjFI_shiftId, GlobalTheory.SeeSaw.mem_conjFI, ← Formalism.BasicNotions.bridge_star_holds D.R D.host, star_star]
    exact hσ
  have h2 := FractionalIdeal.mul_mem_mul h1 hτ
  rw [inv_mul_cancel₀ (GlobalTheory.RowBig.shiftId_ne_zero G)] at h2
  exact (FractionalIdeal.mem_one_iff _).1 h2

theorem mulVec_idLat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (hM : ∀ x ∈ Λ, M *ᵥ x ∈ Λ')
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ∀ x ∈ idLat I Λ, M *ᵥ x ∈ idLat I Λ' := by
  intro x hx
  unfold idLat at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨τ, hτ, y, hy, rfl⟩ := hz
    rw [Matrix.mulVec_smul]
    exact Submodule.subset_span ⟨τ, hτ, _, hM y hy, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | smul r y _ hy => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ r hy

theorem lineComp_mem_shift : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 ∈ latO (negSp F.Lz) (G.V (.core (2 * ρ + 1))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) : Set _) (idLat (shiftId G) (G.Λ (.core (2 * ρ + 1))) : Set _) fun _ => True := by
  intro D hD T L μ0 hL sc G W Mv hM F hF ρ h u hu
  obtain ⟨hsd0, hloc, hsdM, horth⟩ := (_root_.GlobalTheory.AscFin.GridLat.lattices_grid D hD T L μ0 hL sc G W Mv hM F hF).2.1 ρ h
  have sdV : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    (G.sp.V_is (2 * ρ + 1 + 1) 0 (by omega) h (by omega)).sd
  have sdC : IsSelfDualC (G.V (.core (2 * ρ + 1))) (G.Λ (.core (2 * ρ + 1))) :=
    (G.sp.P_is (2 * ρ + 1) (by omega)).sd
  have sdC' := GlobalTheory.RowBig.isSelfDualC_idLat_shiftId G _ sdC
  have hU1 : (F.dJ ρ h).j0 * u * (F.dB ρ h).p0 ∈ latRow G (2 * ρ + 1) := hu
  have hU : (F.dJ ρ h).j0 * u * (F.dB ρ h).p0 ∈ latO (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 1 + 1) 0) : Set _) (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) fun _ => True :=
    _root_.GlobalTheory.RowBig.latRow_le_latBig D hD T L μ0 hL sc G W Mv hM (2 * ρ + 1) (by omega) (by omega) hU1
  clear hU1 hu
  have hq : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), (F.dJ ρ h).q0 *ᵥ t ∈ G.Λ (.core (2 * ρ + 1)) :=
    GlobalTheory.FinPl.CoreProj.wittCoreProjection_mem_lattice_of_splits (F.dJ ρ h) (GlobalTheory.FinPl.LocGlob.mem_of_mem_latV_all sdC) fun v => (hloc v).2
  have hu' : u = (F.dJ ρ h).p0 * ((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) * (F.dB ρ h).j0 := by
    simp only [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    rw [Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [OrthDec.resS_apply]
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ hsdM sdC' _ _).2 ⟨?_, fun z hz => ?_⟩
  · rw [hu']
    exact mxAt_mul_right (mxAt_mul_right (mxAt_mul_left _ (GlobalTheory.FinPl.LatMem.latO_mxAt hU)) _) _
  have h1 : (F.oB ρ h).jB *ᵥ z ∈ latV (F.V₀ ρ) (lat0 F ρ h) fun _ => True := by
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latV_of_local hsdM.1 hsd0.1 (F.oB ρ h).jB (fun v _ y hy => ?_) hz
    refine ((horth v) _).2 ⟨?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, OrthDec.pA_jB, Matrix.zero_mulVec]; exact zero_mem _
    · rw [Matrix.mulVec_mulVec, OrthDec.pB_jB, Matrix.one_mulVec]; exact hy
  have h2 : (F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z) ∈
      latV (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) fun _ => True :=
    rat_mulVec_latV (F.dB ρ h).i₀ (fun x hx => hx) h1
  have h3 := GlobalTheory.FinPl.LatMem.latO_maps sdV hU h2
  have h4 : (F.dJ ρ h).p0 *ᵥ (((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) *ᵥ ((F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z))) ∈
      latA _ (idLat (shiftId G) (G.Λ (.core (2 * ρ + 1)))) fun _ => True := by
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latA (F.dJ ρ h).p0 (fun y hy => ?_) h3
    exact rat_mulVec_latV (F.dJ ρ h).q0 (mulVec_idLat _ hq _) hy
  have e : (F.dJ ρ h).p0 *ᵥ (((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) *ᵥ ((F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z))) =
      (u * (F.oB ρ h).jB) *ᵥ z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    rw [Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [← e]
  exact h4

theorem adj_lineComp_mem_latO : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2) ∈ latO (G.V (.core (2 * 0 + 1))) (negSp F.Lz) (G.Λ (.core (2 * 0 + 1)) : Set _) (Submodule.span (𝓞 D.host.E) {F.ζ 0} : Set _) fun _ => True := by
  intro D hD T L μ0 hL sc G W Mv hM F hF h u hu
  have hx := lineComp_mem_shift D hD T L μ0 hL sc G W Mv hM F hF 0 h u hu
  exact latO_idLat_le _ _ _ _ (shiftId G) (star_mul_shiftId G) _
    (incA_inv_xi0_smul_starAdj_mem_latO D (negSp F.Lz) (G.V (.core (2 * 0 + 1))) _ _ _ _
      (GlobalTheory.AdjSrcZero.star_smul_mem_span G _) _ hx)

end GlobalTheory.LineAdjZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFlagCharacterPrimitiveRowTestMovedLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowShape

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem colMul_besDecAt (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (hjm : j < D.R.m) (i : Fin σ)
    (t : AE D) : colMul (besDecAt G j σ hj).jX i t = fun k => (incA D (D.host.xi0 ^ (i : ℕ)) * t) *
      incA D ((G.rowDec j hjm).a k (Fin.castLE (by omega) i)) := by
  funext k
  simp only [colMul, HypDec.jX, rat, Matrix.map_apply, besDecAt, diagDec, rowBes, besDec, HermitianOrthogonalExtensionData.iso,
    Matrix.mul_diagonal, Matrix.submatrix_apply, lam, id, map_mul]
  ring

theorem rowId_even {j : ℕ} (hj : ¬ Odd j) (p : Fin (D.R.m - 1 - j)) :
    rowId D j p = stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) p := by
  rw [rowId, tiltSc, if_neg hj, FractionalIdeal.spanSingleton_one, one_mul]

theorem stairId_ne_zero (c : ℕ) (p : Fin c) : stairId D.host.AA D.host.AAbar c p ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (GlobalTheory.CuspCharLattice.host_AA_ne_zero _))
    (inv_ne_zero (pow_ne_zero _ (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D)))

theorem primAt_rowN {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (G : GridData L sc) (j σ : ℕ)
    (hj : j + 2 * σ + 2 = D.R.m) (v : Pl D) : PrimAt ψ (besDecAt G j σ hj) (rowN G j) v := by
  have hjm : j < D.R.m := by omega
  have hodd : ¬ Odd j := by
    obtain ⟨a, ha⟩ := D.R.m_even
    rintro ⟨b, hb⟩
    omega
  obtain ⟨-, f2, f3, -, f5, -, -⟩ := _root_.GlobalTheory.SeeSaw.idV_props D ψ hψ v
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.LocFrame.cmHost_imaginaryGenerator_ne_zero

  set I : Fin σ → FI D := fun i => FractionalIdeal.spanSingleton _ (D.host.xi0 ^ (i : ℕ))⁻¹ *
    stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) (Fin.castLE (by omega) i) with hIdef
  have hI0 : ∀ i, I i ≠ 0 := fun i => mul_ne_zero
    ((FractionalIdeal.spanSingleton_ne_zero_iff).2 (inv_ne_zero (pow_ne_zero _ hξ))) (stairId_ne_zero _ _)
  have sub : ∀ (𝔞 : FI D) a, a ∈ idV 𝔞 v → a ∈ idAt D (· = v) := fun 𝔞 a ha => by
    have := (f3 𝔞 1 one_ne_zero a).1 (by rwa [FractionalIdeal.spanSingleton_one, one_mul])
    exact this.2
  have line : ∀ i (t : AE D), t ∈ idAt D (· = v) →
      (colMul (besDecAt G j σ hj).jX i t ∈ latV _ (rowN G j) (· = v) ↔ t ∈ idV (I i) v) := by
    intro i t ht
    rw [colMul_besDecAt G j σ hj hjm, rowN, dite_eq_left hjm,
      (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff (G.rowDec j hjm) (neg_ne_zero.2 one_ne_zero) _ _ _ v _).1, rowId_even hodd,
      hIdef, f3 _ _ (inv_ne_zero (pow_ne_zero _ hξ)), inv_inv]
    exact ⟨fun h => ⟨h, ht⟩, fun h => h.1⟩
  intro i i' hii s hs
  have key : (∀ a : AE D, colMul (besDecAt G j σ hj).jX i' a ∈ latV _ (rowN G j) (· = v) →
      colMul (besDecAt G j σ hj).jX i (s * a) ∈ latV _ (rowN G j) (· = v)) ↔
      ∀ a ∈ idV (I i') v, s * a ∈ idV (I i) v := by
    constructor
    · intro h a ha
      have haA := sub _ a ha
      exact (line i (s * a) (Ideal.mul_mem_left _ _ haA)).1 (h a ((line i' a haA).2 ha))
    · intro h a hc
      have haA := GlobalTheory.SeeSaw.PrimSplit.idAt_of_colMul _ hc
      exact (line i (s * a) (Ideal.mul_mem_left _ _ haA)).2 (h a ((line i' a haA).1 hc))
  have hratio : I i * (I i')⁻¹ = dI D := by
    have hst := stairId_succ (𝔞 := D.host.AA) (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (Fin.castLE (by omega) i : Fin (D.R.m - 1 - j))
      (Fin.castLE (by omega) i') (by simp only [Fin.val_castLE]; exact hii)
    have e : I i = dI D * I i' := by
      simp only [hIdef, dI, hst, hii]
      have e2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (D.host.xi0 ^ (i : ℕ))⁻¹ =
          FractionalIdeal.spanSingleton _ D.host.xi0 * FractionalIdeal.spanSingleton _ (D.host.xi0 ^ ((i : ℕ) + 1))⁻¹ := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
        congr 1
        rw [pow_succ, mul_inv, mul_comm (D.host.xi0 ^ (i : ℕ))⁻¹, ← mul_assoc, mul_inv_cancel₀ hξ, one_mul]
      rw [e2]
      ring
    rw [e, mul_inv_cancel_right₀ (hI0 i')]
  rw [key, f2 _ _ (hI0 i') (hI0 i) s hs, hratio]
  exact f5 s hs

end GlobalTheory.RowShape

namespace GlobalTheory.RowShape

theorem big_primAt_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v,
    GlobalTheory.FinPl.PrimAt ch.W.ψ (besDecAt ch.G j σ hj) (GlobalTheory.RowShape.rowN ch.G j) v :=
  big_mono (fun ch h j σ hj v => primAt_rowN h ch.G j σ hj v) GlobalTheory.BigTop.Fun.OneSqTie.big_std

end GlobalTheory.RowShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiDepthLatticeSplits
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

theorem pcBF_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h
  refine ⟨fun u hu => ?_⟩
  have e1 := ((F.dB ρ h).coordS (G.V (.grid (2 * ρ + 1) 0))).symm_apply_apply u
  have e2 := ((F.dJ ρ h).coordT (F.V₀ ρ)).symm_apply_apply (u ⬝ (F.dB ρ h).j0)
  obtain ⟨s1, -, s3⟩ := _root_.GlobalTheory.AscFin.srcSplit_pcBF D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  obtain ⟨f4, i4⟩ := _root_.GlobalTheory.AscFin.BesIso.splits_iso D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  have b := _root_.GlobalTheory.AscFin.pcBF_big_core D hq T L μ0 hL sc G W M hM F hF ρ h _ s3
  refine ⟨u ⬝ (F.dB ρ h).jX, s1, u ⬝ (F.dB ρ h).jY, AddSubgroup.subset_closure ⟨f4, i4⟩,
    (F.dJ ρ h).pX ⬝ (u ⬝ (F.dB ρ h).j0), b.1, (F.dJ ρ h).pY ⬝ (u ⬝ (F.dB ρ h).j0), b.2,
    (F.dJ ρ h).p0 ⬝ (u ⬝ (F.dB ρ h).j0), _root_.GlobalTheory.AscFin.latRow_bessel_core_split D hq T L μ0 hL sc G W M hM F hF ρ h _ s3, ?_,
    _root_.GlobalTheory.AscFin.pcBF_xZero_char D hq T L μ0 hL sc G W M hM F hF ρ h u hu, GlobalTheory.T.besselSecondBasePoint_character_trivial_depthLattice D hq T L μ0 hL sc G W M hM F hF ρ h u hu⟩
  have e2' : (F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ (u ⬝ (F.dB ρ h).j0)) + (F.dJ ρ h).incY (F.V₀ ρ) ((F.dJ ρ h).pY ⬝ (u ⬝ (F.dB ρ h).j0)) + (F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 ⬝ (u ⬝ (F.dB ρ h).j0)) = (u ⬝ (F.dB ρ h).j0) := by
    simp only [HypDec.coordT, AddEquiv.coe_mk, Equiv.coe_fn_mk, AddEquiv.symm_mk, Equiv.coe_fn_symm_mk] at e2
    exact (add_right_comm _ _ _).trans e2
  have e1' : (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jX) + (F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY) + (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).j0) = u := by
    simp only [HypDec.coordS, AddEquiv.coe_mk, Equiv.coe_fn_mk, AddEquiv.symm_mk, Equiv.coe_fn_symm_mk] at e1
    exact (add_right_comm _ _ _).trans e1
  rw [e2', e1']

end GlobalTheory.AscFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToJacobiBasePointCarriesRowLatticeLines
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.RowColsBF

open GlobalTheory.RowShape GlobalTheory.RowChain GlobalTheory.StairCols

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem tiltSc_odd {j : ℕ} (hj : Odd j) (p : Fin (D.R.m - 1 - j)) (hp : 2 * p.1 < D.R.m - 1 - j) :
    tiltSc D j p = (D.host.xi0 ^ p.1)⁻¹ := by
  rw [tiltSc, if_pos hj, if_pos hp]

theorem tiltSc_even {j : ℕ} (hj : ¬ Odd j) (p : Fin (D.R.m - 1 - j)) : tiltSc D j p = 1 := by
  rw [tiltSc, if_neg hj]

theorem besCol_eq (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (i : Fin σ) (a : AE D) :
    GlobalTheory.FinPl.colMul (besDecAt G j σ hj).jX i a =
      fun k => (a * incA D (D.host.xi0 ^ i.1)) * incA D ((G.rowDec j (by omega)).a k (Fin.castLE (by omega) i)) := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, HypDec.jX, besDecAt, diagDec, rowBes, besDec, HermitianOrthogonalExtensionData.iso, rat, Matrix.map_apply,
    Matrix.mul_diagonal, Matrix.submatrix_apply, lam, id_eq, map_mul]
  ring

theorem jacCol_eq (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (i : Fin σ) (a : AE D) :
    GlobalTheory.FinPl.colMul (xZero (rowJac G (j + 1) (by omega) σ (by omega))) i a =
      fun k => a * incA D ((G.rowDec (j + 1) (by omega)).a k (Fin.castLE (by omega) i)) := rfl

theorem cols (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (v : GlobalTheory.FinPl.Pl D) :
    GlobalTheory.FinPl.ColsAt (besDecAt G j σ hj) (xZero (rowJac G (j + 1) (by omega) σ (by omega)))
      (rowN G j) (rowN G (j + 1)) v := by
  intro i a ha
  have hjm : j < D.R.m := by omega
  have hjm' : j + 1 < D.R.m := by omega
  obtain ⟨k, hk⟩ := D.R.m_even
  have hev : ¬ Odd j := by
    rw [Nat.not_odd_iff_even]; exact ⟨k - σ - 1, by omega⟩
  have hod : Odd (j + 1) := ⟨k - σ - 1, by omega⟩
  rw [besCol_eq G j σ hj i a, jacCol_eq G j σ hj i a]
  have l1 : rowN G j = (G.rowDec j hjm).lat (G.Λ (.top j)) (rowId D j) := dif_pos hjm
  have l2 : rowN G (j + 1) = (G.rowDec (j + 1) hjm').lat (G.Λ (.top (j + 1))) (rowId D (j + 1)) := dif_pos hjm'
  have hpr : (Fin.castLE (by omega : σ ≤ D.R.m - 1 - j) i).rev ≠ Fin.castLE (by omega) i := fun e => by
    have := congrArg Fin.val e
    simp only [Fin.val_rev, Fin.val_castLE] at this
    omega
  have hqr : (Fin.castLE (by omega : σ ≤ D.R.m - 1 - (j + 1)) i).rev ≠ Fin.castLE (by omega) i := fun e => by
    have := congrArg Fin.val e
    simp only [Fin.val_rev, Fin.val_castLE] at this
    omega
  rw [GlobalTheory.FinPl.latV, l1, col_mem_iff (G.rowDec j hjm) _ hpr _ _ 1 {1}
    (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact FractionalIdeal.one_mem_one _)
    (fun x hx => by
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      exact ⟨1, rfl, o, (one_mul _).symm⟩) v]
  rw [GlobalTheory.FinPl.latA, l2, col_mem_iff (G.rowDec (j + 1) hjm') _ hqr _ _ D.host.AA {a | a ∈ D.host.AA} (fun x hx => hx)
    (fun x hx => ⟨x, hx, 1, by simp⟩) v]
  have e3 : D.host.AA * rowId D (j + 1) (Fin.castLE (by omega) i) =
      FractionalIdeal.spanSingleton _ (D.host.xi0 ^ i.1)⁻¹ * (1 * rowId D j (Fin.castLE (by omega) i)) := by
    rw [rowId, rowId, tiltSc_even hev, tiltSc_odd hod _ (by simp only [Fin.val_castLE]; omega),
      FractionalIdeal.spanSingleton_one, one_mul, one_mul, stairId, stairId]
    simp only [Fin.val_castLE]
    have h1 : D.R.m - 1 - j - i.1 = (D.R.m - 1 - (j + 1) - i.1) + 1 := by omega
    rw [h1, pow_succ]
    ring
  rw [e3, GlobalTheory.StairLine.mem_idV_inv_mul (pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)), mul_comm a]

theorem colsAt_bf : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v,
    GlobalTheory.FinPl.ColsAt (besDecAt ch.G j σ hj) (xZero (rowJac ch.G (j + 1) (by omega) σ (by omega)))
      (GlobalTheory.RowShape.rowN ch.G j) (GlobalTheory.RowShape.rowN ch.G (j + 1)) v :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => fun j σ hj v => cols ch.G j σ hj v⟩⟩

end GlobalTheory.RowColsBF
end
end

