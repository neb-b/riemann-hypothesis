module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0007
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0276

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EigSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EigSpan

theorem eig_span : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → ∀ P, GlobalTheory.Hk3.Good R t P → ∀ (a : List ℤ → ℂ) (w : R.HE.H) (s : Set (List ℤ →₀ ℂ)), (∀ c ∈ s, h P c w = GlobalTheory.Hk3.evC (Yc D 0) P a c • w) → ∀ c ∈ Submodule.span ℂ s, h P c w = GlobalTheory.Hk3.evC (Yc D 0) P a c • w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t h hh P hP a w s hs c hc
  have inj : Function.Injective R.HE.e := hC.models.HE.1
  have hkAdd : ∀ c c' : List ℤ →₀ ℂ, GlobalTheory.Hk3.hk (Yc D 0) P (c + c') = GlobalTheory.Hk3.hk (Yc D 0) P c + GlobalTheory.Hk3.hk (Yc D 0) P c' :=
    fun c c' => by
      unfold GlobalTheory.Hk3.hk
      exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)
  have hkSmul : ∀ (z : ℂ) (c : List ℤ →₀ ℂ), GlobalTheory.Hk3.hk (Yc D 0) P (z • c) = z • GlobalTheory.Hk3.hk (Yc D 0) P c :=
    fun z c => by
      unfold GlobalTheory.Hk3.hk
      rw [Finsupp.sum_smul_index', Finsupp.smul_sum]
      · simp only [smul_eq_mul, mul_smul]
      · intro; exact zero_smul _ _
  have hkZero : GlobalTheory.Hk3.hk (Yc D 0) P 0 = 0 := by
    unfold GlobalTheory.Hk3.hk; exact Finsupp.sum_zero_index
  have evAdd : ∀ c c' : List ℤ →₀ ℂ, GlobalTheory.Hk3.evC (Yc D 0) P a (c + c') = GlobalTheory.Hk3.evC (Yc D 0) P a c + GlobalTheory.Hk3.evC (Yc D 0) P a c' :=
    fun c c' => by
      unfold GlobalTheory.Hk3.evC
      exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by split_ifs <;> ring)
  have evSmul : ∀ (z : ℂ) (c : List ℤ →₀ ℂ), GlobalTheory.Hk3.evC (Yc D 0) P a (z • c) = z * GlobalTheory.Hk3.evC (Yc D 0) P a c :=
    fun z c => by
      unfold GlobalTheory.Hk3.evC
      rw [Finsupp.sum_smul_index', Finsupp.mul_sum]
      · exact Finsupp.sum_congr fun d _ => by split_ifs <;> simp [mul_assoc]
      · intro; simp
  have evZero : GlobalTheory.Hk3.evC (Yc D 0) P a 0 = 0 := by
    unfold GlobalTheory.Hk3.evC; exact Finsupp.sum_zero_index
  have pAdd : ∀ L L' x, postOn (R.MY 0) (L + L') x = postOn (R.MY 0) L x + postOn (R.MY 0) L' x := by
    intro L L' x; ext v; simp [postOn]
  have pSmul : ∀ (z : ℂ) L x, postOn (R.MY 0) (z • L) x = z • postOn (R.MY 0) L x := by
    intro z L x; ext v; simp [postOn]
  have pZero : ∀ x, postOn (R.MY 0) 0 x = 0 := by
    intro x; ext v; simp [postOn]
  have hAdd : ∀ c c', h P (c + c') w = h P c w + h P c' w := fun c c' =>
    inj (by rw [hh P hP, map_add (f := _), hh P hP, hh P hP, hkAdd, pAdd])
  have hSmul : ∀ (z : ℂ) c, h P (z • c) w = z • h P c w := fun z c =>
    inj (by rw [hh P hP, map_smul, hh P hP, hkSmul, pSmul])
  have hZero : h P 0 w = 0 := inj (by rw [hh P hP, hkZero, pZero, map_zero])
  induction hc using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => rw [hZero, evZero, zero_smul]
  | add x y _ _ hx hy => rw [hAdd, hx, hy, evAdd, add_smul]
  | smul z x _ hx => rw [hSmul, hx, evSmul, mul_smul]

end GlobalTheory.EigSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfSplitVec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.SplitLabels

open GlobalTheory.Hk3 GlobalTheory.Hk3.LabDet

theorem evC_single_lab {D : D7} (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (d : List ℤ) (hd : IsLab V P d) :
    evC V P a (Finsupp.single d 1) = a d := by
  unfold evC
  rw [Finsupp.sum_single_index (by simp), if_pos hd, one_mul]

theorem eq_of_split_vec : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → ∀ P, GlobalTheory.Hk3.Good R t P → Formalism.DivisionValues.conjPl P ≠ P → ∀ (c : Pl D.host.E → List ℤ → ℂ) (x w : R.HE.H), x ≠ 0 → (∀ P', GlobalTheory.Hk3.Good R t P' → ∀ cc, h P' cc x = GlobalTheory.Hk3.evC (Yc D 0) P' (fun d => c P' (dualLab d)) cc • x) → (∀ k ≤ (Yc D 0).rank, h P (Finsupp.single (splitLab (Yc D 0).rank k) 1) w = GlobalTheory.Hk3.evC (Yc D 0) P (fun d => c P (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1) • w ∧ h (Formalism.DivisionValues.conjPl P) (Finsupp.single (splitLab (Yc D 0).rank k) 1) w = GlobalTheory.Hk3.evC (Yc D 0) (Formalism.DivisionValues.conjPl P) (fun d => c (Formalism.DivisionValues.conjPl P) (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1) • w) → ∀ d, GlobalTheory.Hk3.IsLab (Yc D 0) P d → h P (Finsupp.single d 1) w = c P (dualLab d) • w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t h hh P hP hcP c x w hx0 hxe hw d hd
  obtain ⟨-, hgood, -, -⟩ := _root_.GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hPA : Good R A.μ0 P := (hgood t P hP).2.2
  have hPc : Good R t (Formalism.DivisionValues.conjPl P) := (hgood t P hP).2.1
  obtain ⟨n, hβ⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have hlev := _root_.GlobalTheory.LevOp.level_operators (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβ P
    (by rw [Nat.cast_pow]; exact fun hm => (hgood _ P hPA).1 (P.isPrime.mem_of_pow_mem n hm))
    (fun PP hPP => hPA PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
  have inj : Function.Injective R.HE.e := hC.models.HE.1
  have hmem : ∀ y, R.HE.e y ∈ Mult R.θ (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) :=
    fun y => goodPart_le _ _ _ _ _ (hC.models.HE.2.1 ▸ LinearMap.mem_range_self _ y)
  have hfix : ∀ y, ∀ k ∈ hyp (Yc D 0) P, rRep (R.MY 0) k (R.HE.e y) = R.HE.e y := fun y k hk =>
    mult_lev _ _ _ _ _ (hmem y) k (hlev.1 k hk).1 (hlev.1 k hk).2
  have hop : ∀ P', Good R t P' → ∀ e y, opOf (rRep (R.MY 0)) P' (Finsupp.single e 1) (R.HE.e y) =
      R.HE.e (h P' (Finsupp.single e 1) y) := by
    intro P' hP' e y
    rw [opOf_single, sum_rRep, hh P' hP', GlobalTheory.Hk3.OpsRows.hk_single]
    rfl
  have hu : R.HE.e x ≠ 0 := fun h0 => hx0 (inj (by rw [h0, map_zero]))
  obtain ⟨a, ha, hae⟩ := GlobalTheory.SplitGen.gen_split (Yc D 0) P hcP (MMap (R.MY 0)) (rRep (R.MY 0)) d
  obtain ⟨l, h1, h2⟩ := adjoin_common _ (R.HE.e x) (R.HE.e w) (by
    rintro y ⟨k, hk, rfl | rfl⟩
    · refine ⟨evC (Yc D 0) P (fun d => c P (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1), ?_, ?_⟩
      · rw [hop P hP, hxe P hP, map_smul]
      · rw [hop P hP, (hw k hk).1, map_smul]
    · have hc := (_root_.GlobalTheory.SphConj.sph_conj (Yc D 0) P).2.2 (Finsupp.single (splitLab (Yc D 0).rank k) 1) _ (rRep (R.MY 0))
      have hdc : dualC (Finsupp.single (splitLab (Yc D 0).rank k) 1) =
          Finsupp.single (dualLab (splitLab (Yc D 0).rank k)) 1 := by
        unfold dualC
        rw [Finsupp.mapDomain_single]
      rw [hdc] at hc
      rw [← hc _ (hfix x), ← hc _ (hfix w)]
      refine ⟨evC (Yc D 0) (Formalism.DivisionValues.conjPl P) (fun d => c (Formalism.DivisionValues.conjPl P) (dualLab d))
        (Finsupp.single (splitLab (Yc D 0).rank k) 1), ?_, ?_⟩
      · rw [hop _ hPc, hxe _ hPc, map_smul]
      · rw [hop _ hPc, (hw k hk).2, map_smul]) a ha
  rw [hae _ (hfix x), hop P hP, hxe P hP, evC_single_lab _ _ _ _ hd, map_smul] at h1
  have hl : l = c P (dualLab d) := (smul_left_injective ℂ hu h1).symm
  rw [hae _ (hfix w), hop P hP, hl, ← map_smul] at h2
  exact inj h2

end GlobalTheory.Hk3.SplitLabels

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyExistsDoubleCosetAntiInvolutionUnitary
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

noncomputable section
namespace GlobalTheory.AntiInvLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eventually_isUnram : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
  have hfin := (Ideal.finite_factors (differentIdeal_ne_bot (A := 𝓞 F) (B := 𝓞 E))).image
    (fun P : HeightOneSpectrum (𝓞 E) => P.under (𝓞 F))
  refine Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq] at hv
  rw [GlobalTheory.LFun.isUnram_iff] at hv
  push_neg at hv
  obtain ⟨P, hP, h1⟩ := hv
  refine ⟨P, ?_, hP⟩
  simp only [Set.mem_setOf_eq]
  by_contra hnd
  haveI := not_dvd_differentIdeal_iff.1 hnd
  exact h1 Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)}

theorem exists_antiInv_split (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : Submodule.IsFullLattice E L)
    (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (hd : IsSelfDualAt σ J L v) :
    ∃ θ : GLoc σ J v → GLoc σ J v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧
      ∀ g, ∃ a ∈ stabLoc σ J L v, ∃ b ∈ stabLoc σ J L v, θ g = a * g * b := by
  obtain ⟨w, -, -, hw, -⟩ := id hv
  have h : w.under (𝓞 F) = v := HeightOneSpectrum.ext hw
  obtain ⟨e, ⟨-, he⟩, -⟩ := GlobalTheory.LFun.SplitChart.exists_isSplitChart hc hJ hL.fg (Submodule.IsFullLattice.span_eq_top (self := hL)) h hv hd
  refine ⟨fun g => e.symm (Formalism.UG.P.heckecomm_tr (e g)), fun x y => ?_, fun x => ?_, fun g => ?_⟩
  · simp only [map_mul, Formalism.UG.P.heckecomm_tr_mul]
  · simp only [MulEquiv.apply_symm_apply, Formalism.UG.P.heckecomm_tr_tr, MulEquiv.symm_apply_apply]
  · obtain ⟨a, b, hab⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.P.cartan_decomposition_holds E w n (e g)
    refine ⟨e.symm a, (he _).2 (by simpa using a.2), e.symm b, (he _).2 (by simpa using b.2), ?_⟩
    show e.symm _ = _
    rw [hab]
    apply e.injective
    simp

theorem exists_antiInv_inert (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : Submodule.IsFullLattice E L)
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (hd : IsSelfDualAt σ J L v) :
    ∃ θ : GLoc σ J v → GLoc σ J v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧
      ∀ g, ∃ a ∈ stabLoc σ J L v, ∃ b ∈ stabLoc σ J L v, θ g = a * g * b := by
  have h : w.under (𝓞 F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨-, ⟨c, hc', -⟩, -, -, hrest⟩ := (GlobalTheory.LFun.exists_isInertChart σ hc v).2 w h hw
  obtain ⟨⟨ϖ, hU⟩, hch⟩ := hrest c hc'
  obtain ⟨e, ⟨-, -, he⟩, -⟩ := hch n J L hJ hL.fg (Submodule.IsFullLattice.span_eq_top (self := hL)) hd
  refine ⟨fun g => g⁻¹, mul_inv_rev, inv_inv, fun g => ?_⟩
  obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := GlobalTheory.LFun.ConjParam.inv_mem hU (e g)
  refine ⟨e.symm k₁, (he _).2 (by simpa using hk₁), e.symm k₂, (he _).2 (by simpa using hk₂), ?_⟩
  apply e.injective
  simp [hk]

theorem eventually_exists_antiInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L → ∀ᶠ v in cofinite, ∃ θ : GLoc σ J v → GLoc σ J v, (∀ x y, θ (x * y) = θ y * θ x) ∧ (∀ x, θ (θ x) = x) ∧ ∀ g, ∃ a ∈ stabLoc σ J L v, ∃ b ∈ stabLoc σ J L v, θ g = a * g * b := by
  intro F E _ _ _ _ _ σ hc n J hJ L hL
  filter_upwards [eventually_isUnram (F := F) (E := E),
    GlobalTheory.AdelicU.SelfDual.eventually_isSelfDualAt (σ := σ) hJ.2 hL] with v hu hd
  rcases (GlobalTheory.LFun.exists_isInertChart σ hc v).1 hu with hs | ⟨w, hw⟩
  · exact exists_antiInv_split hc hJ hL hs hd
  · exact exists_antiInv_inert hc hJ hL hw hd

end GlobalTheory.AntiInvLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchSchwartzDerivativeHeisenbergLine
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped SchwartzMap

noncomputable section

namespace GlobalTheory.HeisDeriv

variable {F : Type} [Field F] [NumberField F]

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_sum {κ : Type} [Fintype κ] (g : κ → AF F) : evI F (∑ i, g i) = ∑ i, evI F (g i) := by
  classical
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, evI_add, ih]

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ _ t :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem mul_realAd_eq_zero {a : AF F} (ha : evI F a = 0) (t : ℝ) : a * realAd F t = 0 := by
  have h1 : a.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp ha
  have h2 : (realAd F t).2 = 0 := rfl
  show ((a.1 * (realAd F t).1, a.2 * (realAd F t).2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, 0)
  rw [h1, h2, zero_mul, mul_zero]

end GlobalTheory.HeisDeriv

namespace GlobalTheory.HeisDeriv

open scoped Classical

variable {F : Type} [Field F] [NumberField F]


variable (F) in
def trForm {κ : Type} [Fintype κ] (y : κ → AF F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).comp
      (∑ i, (LinearMap.mulRight ℝ (evI F (y i))).comp (LinearMap.proj i)))

theorem trForm_apply {κ : Type} [Fintype κ] (y : κ → AF F) (z : κ → mixedEmbedding.mixedSpace F) :
    trForm F y z = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, z i * evI F (y i)) := by
  simp [trForm, LinearMap.sum_apply]


variable (F) in
def mult {κ : Type} [Fintype κ] (y : κ → AF F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ :=
  (-(2 * Real.pi * Complex.I)) • (Complex.ofRealCLM.comp (trForm F y))

theorem mult_apply {κ : Type} [Fintype κ] (y : κ → AF F) (z : κ → mixedEmbedding.mixedSpace F) :
    mult F y z = -(2 * Real.pi * Complex.I) * (trForm F y z : ℂ) := by
  simp [mult]


variable (F) in
def heisD {κ : Type} [Fintype κ] (v : κ → mixedEmbedding.mixedSpace F) (y : κ → AF F) :
    SInf F κ →ₗ[ℂ] SInf F κ :=
  (LineDeriv.lineDerivOpCLM ℂ (SInf F κ) v + SchwartzMap.smulLeftCLM ℂ (⇑(mult F y))).toLinearMap

theorem heisD_apply {κ : Type} [Fintype κ] (v : κ → mixedEmbedding.mixedSpace F) (y : κ → AF F) (f : SInf F κ)
    (z : κ → mixedEmbedding.mixedSpace F) :
    heisD F v y f z = fderiv ℝ f z v + mult F y z * f z := by
  have h : (⇑(mult F y)).HasTemperateGrowth := (mult F y).hasTemperateGrowth
  simp [heisD, h, SchwartzMap.lineDerivOp_apply_eq_fderiv]

end GlobalTheory.HeisDeriv

namespace GlobalTheory.HeisDeriv

open scoped Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

theorem exists_heisLine_deriv {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) f (D f) := by
  set x₁ := (M.co.e u).1 with hx₁
  set y₁ := (M.co.e u).2 with hy₁
  set v : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x₁ i) with hv
  refine ⟨heisD F v y₁, fun f r hr x => ?_⟩
  set z : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x i) with hz
  set P : ℝ := trForm F y₁ z with hP
  set Q : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) with hQ
  have hline : ∀ t : ℝ, M.heisLine ψ u t (tens (evI F) f r) x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * (P + t * Q) : ℝ) : ℂ)) * (f (z + t • v) * r x) := by
    intro t
    have he : M.co.e (realAd F t • u) = realAd F t • M.co.e u := map_smul _ _ _
    simp only [Model.heisLine, Darboux.rho, he, schr, tens, Prod.smul_fst, Prod.smul_snd, ← hx₁, ← hy₁]
    have hAt1 : At (evI F) (realAd F t • x₁) := fun a ha => by
      rw [smul_smul, mul_realAd_eq_zero ha, zero_smul]
    rw [hr.1 x _ hAt1]
    set A : AF F := x ⬝ᵥ (realAd F t • y₁) + ⅟(2 : AF F) * ((realAd F t • x₁) ⬝ᵥ (realAd F t • y₁)) with hAdef
    have hA : A = realAd F t * (x ⬝ᵥ y₁ + realAd F t * (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) := by
      simp only [hAdef, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
    have hAt2 : At (evI F) A := fun a ha => by
      rw [hA, smul_eq_mul, ← mul_assoc, mul_realAd_eq_zero ha, zero_mul]
    have hxy : evI F (x ⬝ᵥ y₁) = ∑ i, z i * evI F (y₁ i) := by
      simp only [dotProduct, evI_sum, evI_mul, hz]
    have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F A) = t * (P + t * Q) := by
      rw [hA, evI_mul, evI_add, evI_mul, evI_realAd, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_add (f := _),
        map_smul, hxy, hP, trForm_apply, hQ, smul_eq_mul, smul_eq_mul]
    have harg : (fun i => evI F ((x + realAd F t • x₁) i)) = z + t • v := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_realAd, hz, hv]
      rw [Algebra.smul_def]
    rw [hψ.2.2 A hAt2, htr, harg]
  have h1 : HasDerivAt (fun t : ℝ => t * (P + t * Q)) P 0 := by
    have := (hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_const (0 : ℝ) P).add ((hasDerivAt_id (0 : ℝ)).mul_const Q))
    exact this.congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have h3 : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h4 : HasDerivAt (fun t : ℝ => f (z + t • v)) (fderiv ℝ f z v) 0 := by
    have := (f.hasFDerivAt (z + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) h3
    simpa [Function.comp_def] using this
  have h5 := h2.mul (h4.mul_const (r x))
  refine (h5.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => hline t)
  simp only [tens, heisD_apply, mult_apply, ← hz, ← hP]
  simp
  ring

end GlobalTheory.HeisDeriv


open GlobalTheory.HeisDeriv in
theorem GlobalTheory.HeisDeriv.exists_actsD_heisLine : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f (D f) :=
  fun M ψ hψ u _ => exists_heisLine_deriv M ψ hψ u
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetSumTranslatesFixedCompactSubgroupStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finsetSum_translates_fixed_compactSubgroup : ∀ {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X) (K : Subgroup G), IsCompact (K : Set G) → ∀ x : X, IsOpen {g | ρ g x = x} → ∃ s : Finset G, (∀ g ∈ s, g ∈ K) ∧ s.Nonempty ∧ ∀ k ∈ K, ρ k (∑ g ∈ s, ρ g x) = ∑ g ∈ s, ρ g x := by
  first | exact @GlobalTheory.exists_finset_sum_translate_fixed | exact GlobalTheory.exists_finset_sum_translate_fixed | (intros; apply GlobalTheory.exists_finset_sum_translate_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalUnitaryGroupIsoConjIsometryStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localUnitaryGroupIso_conj_isometry : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {r r' : ℕ} (J : Matrix (Fin r) (Fin r) E) (J' : Matrix (Fin r') (Fin r') E) (v : HeightOneSpectrum (𝓞 F)) (a : Matrix (Fin r') (Fin r) (Fv F v ⊗[F] E)) (b : Matrix (Fin r) (Fin r') (Fv F v ⊗[F] E)), a * b = 1 → b * a = 1 → Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) a * JR (F := F) (Fv F v) J' * a = JR (F := F) (Fv F v) J → ∃ φ : GLoc σ J v ≃ₜ* GLoc σ J' v, ∀ g, (GlobalTheory.AdelicU.matHom _ σ J' (φ g)).val = a * (GlobalTheory.AdelicU.matHom _ σ J g).val * b := by
  first | exact @GlobalTheory.LocIsoConj.exists_locIso | exact GlobalTheory.LocIsoConj.exists_locIso | (intros; apply GlobalTheory.LocIsoConj.exists_locIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdelicUnitaryPointExtLocalComponentsStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicUnitaryPoint_ext_localComponents : ∀ {D : D7} (V : HSp D) (x y : GfC V), (∀ u : HeightOneSpectrum (𝓞 D.host.F), (Formalism.IndefR.Lev.finE V (x : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u) = (Formalism.IndefR.Lev.finE V (y : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u)) → x = y := by
  first | exact @GlobalTheory.TrFinExt.gfc_ext | exact GlobalTheory.TrFinExt.gfc_ext | (intros; apply GlobalTheory.TrFinExt.gfc_ext <;> assumption)
end

