module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0869
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
public import Formalism.SharpRestriction.Divisibility.WeightFamilies
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0867

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSelfCuspRapidSpanNeTop
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors ComplexConjugate
open GlobalTheory.ThetaPoisson GlobalTheory.RSTheta

namespace GlobalTheory.RSThetaSelf

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem rsPsi_self_eq_norm (ℓ : Fin a) (F : GA E a → ℂ) {Φ : (Fin a → Cinf E) → ℂ}
    (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (g : GA E a)
    (y : Fin a → Ad E) : rsPsi ℓ F F Φ J η g y = ((‖rsPsi ℓ F F Φ J η g y‖ : ℝ) : ℂ) := by
  have key : ∀ z w t : ℂ, 0 ≤ w.re → w.im = 0 → (t = 0 ∨ t = 1) →
      z * conj z * w * t = ((‖z * conj z * w * t‖ : ℝ) : ℂ) := by
    intro z w t h1 h2 ht
    have hw : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h2])
    rcases ht with rfl | rfl
    · simp
    · rw [mul_one, Complex.mul_conj, hw, ← Complex.ofReal_mul, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (Complex.normSq_nonneg z) h1)]
  simp only [rsPsi, thetaFn, rsInf]
  refine key _ _ _ (hΦ _).1 (hΦ _).2 ?_
  by_cases h : (fun i => pFin E (y i)) - η ∈ latt a J <;> simp [h]

theorem lintegral_ne_top : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (π : CuspSub E a) (ω : HChar E),
    ω.IsUnitary → π.HasCentChar ω → ∀ F : GA E a → ℂ, F ∈ GlobalTheory.JSW.mspanR π →
    ∀ (Φ : (Fin a → Cinf E) → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ x : ℝ, 1 < x →
    ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ ≠ ⊤ := by
  intro E _ _ _ a ℓ π ω hω hc F hF Φ hΦ hcs hs hpos J η μ _ 𝓕 h𝓕 x hx
  have hπ : π.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hc⟩
  obtain ⟨φ, rfl, hw⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hπ F hF
  have hcont : Continuous φ.1 := by simpa [GlobalTheory.JSW.word_nil] using (hw []).2.cont
  have hrsm : φ ∈ GlobalTheory.RSThetaLowM.rsm π := hF
  obtain ⟨hsum, hup, -⟩ := GlobalTheory.RSThetaM.theta_integral_upper_mspan E a ℓ π π hπ hπ φ φ (Or.inr hF) (Or.inr hF) Φ
    hΦ.continuous hcs hs J η μ 𝓕 h𝓕
  have hlow := (GlobalTheory.RSThetaLowM.integral_low_eq J η hπ hπ hrsm hrsm hcont hcont ⟨hΦ, hcs, hs⟩ h𝓕 (s := (x : ℂ))
    (by simpa using hx)).1
  have hpt : ∀ g : GA E a, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      ‖rsPsi ℓ φ.1 φ.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) *
        ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) =
      ENNReal.ofReal ((∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
        ‖rsPsi ℓ φ.1 φ.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) *
          (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) := by
    intro g
    rw [ENNReal.ofReal_mul (tsum_nonneg fun _ => norm_nonneg _),
      ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hsum g)]
    simp only [ofReal_norm_eq_enorm]
  have hlow' : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      ‖rsPsi ℓ φ.1 φ.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) *
        (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) (𝓕 ∩ GlobalTheory.RSThetaLow.lowSet E a) μ := by
    refine hlow.norm.congr (.of_forall fun g => ?_)
    have e : ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ.1 φ.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val) =
        (((∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
          ‖rsPsi ℓ φ.1 φ.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ : ℝ)) : ℂ) := by
      rw [Complex.ofReal_tsum]
      exact tsum_congr fun ξ => rsPsi_self_eq_norm ℓ φ.1 hpos J η g _
    simp only
    rw [← GlobalTheory.RSThetaLow.tsum_rsPsi_eq_tsum_ne_zero J η _ _ hs g, norm_mul, e, Complex.norm_real,
      Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _),
      Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule E _).2, Complex.ofReal_re]
  have h1 := (hup x).lintegral_lt_top
  have h2 := hlow'.lintegral_lt_top
  have hsub : 𝓕 ⊆ (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) ∪ (𝓕 ∩ GlobalTheory.RSThetaLow.lowSet E a) := by
    intro g hg
    rcases le_total 1 (ideleModule E (GeneralLinearGroup.det g) : ℝ) with h | h
    · exact Or.inl ⟨hg, h⟩
    · exact Or.inr ⟨hg, h⟩
  rw [lintegral_congr hpt]
  exact ne_of_lt ((lintegral_mono_set hsub).trans_lt ((lintegral_union_le _ _ _).trans_lt (ENNReal.add_lt_top.2 ⟨h1, h2⟩)))

end GlobalTheory.RSThetaSelf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundZeroAtLargePrimesOfCongruenceBound
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
open scoped ENNReal

noncomputable section

namespace GlobalTheory.NLink.RowE

open GlobalTheory.IndefiniteRowSideFullHecke

theorem toReal_enat (a : ℕ∞) : ((a : ℝ≥0∞)).toReal = (a.toNat : ℝ) := by
  induction a using ENat.recTopCoe with
  | top => simp
  | coe n => simp

theorem nlen_toReal (O : Type) [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] :
    (BaseSizes.nlen O l M).toReal = (lenUnit (O := O) l M : ℝ) := by
  unfold BaseSizes.nlen lenUnit
  rw [ENNReal.toReal_div, toReal_enat, toReal_enat]
  push_cast
  rfl

theorem nlen_ne_top {O : Type} [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) (hl : Module.length O (O ⧸ Ideal.span {(l : O)}) ≠ 0) :
    BaseSizes.nlen O l M ≠ ⊤ := by
  unfold BaseSizes.nlen
  exact ENNReal.div_ne_top (by simpa using hM) (by simpa using hl)

theorem param_eq (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) : BaseSizes.param D i ρ = JumpDictionary.PP D i ρ := by
  have hI : Finset.Icc 1 D.R.t = (Finset.range D.R.t).map (addRightEmbedding 1) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, addRightEmbedding_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨c - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      omega
  unfold BaseSizes.param JumpDictionary.PP JumpDictionary.param JumpDictionary.run
  congr 1
  rw [hI, Finset.map_val, Multiset.map_map, Finset.range_val]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, addRightEmbedding_apply]
  push_cast
  rfl

theorem embSide_false (D : D7) (ρ : D.what₂.Tau) : BaseSizes.embSide D ρ false = JumpDictionary.embOver D ρ true := by
  ext x
  simp [BaseSizes.embSide, JumpDictionary.embOver, ComplexEmbedding.conjugate_coe_eq, WeightFamilies.emb_conj]

theorem weightTie_of (D : D7) (h : JumpDictionary.WeightParam D) (i : D.nd.Loc) : BaseSizes.WeightTie D i := by
  refine ⟨true, fun ρ => ⟨-1 / 2, ?_, ?_⟩⟩
  · rw [show BaseSizes.embSide D ρ true = JumpDictionary.embOver D ρ false from rfl, (h i ρ).1, param_eq]
    refine Multiset.map_congr rfl fun p _ => ?_
    push_cast
    ring
  · rw [show BaseSizes.embSide D ρ (!true) = JumpDictionary.embOver D ρ true from embSide_false D ρ, (h i ρ).2, param_eq]
    refine Multiset.map_congr rfl fun p _ => ?_
    push_cast
    ring

theorem isRankRPart_of (D : D7) (i : D.nd.Loc) (r₀ : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))
    (ρ₀ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (h : BlockRepresentationsSemisimple.IsComplement D.nd i r₀ ρ₀) :
    BaseSizes.IsRankRPart D i r₀ ρ₀ := by
  obtain ⟨e, he⟩ := h.rho
  refine ⟨h.cont, e, fun g u => ?_⟩
  have := he g u
  rw [BlockRepresentationsSemisimple.blockRep_apply] at this
  exact this

end GlobalTheory.NLink.RowE

namespace GlobalTheory.NLink.RowE

open GlobalTheory.IndefiniteRowSideFullHecke

theorem main : ∀ (D : D7) (L : SizeData₂ D) (r : FamilyRepresentationConstants.RFam D) (ρ : FamilyRepresentationConstants.RhoFam D) (exc : Finset ℕ), GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at D L → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D → GlobalTheory.PtCore.PtFam D r ρ → KillingConditions.KillAt ρ → TwistedPlaces.ShaFinOdd D → 3 ≤ TwistedPlaces.lStar L → (exc : Set ℕ) = GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc L → StarE L ρ exc := by
  intro D L r ρ exc hCB hW hP hK hS h3 hexc i hTw hl hg hx π hπ
  have hg' := (D.Zgood_tie i π).1 hπ
  have hZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 hg'.1
  have hHG : HG D.nd D.naut i := ⟨π, hg'⟩
  have hk : ∀ k, D.nd.l i ≠ D.host.g k := by
    intro k hk
    apply hg
    rw [hk]
    fin_cases k <;> simp [TwistedPlaces.gset]
  have hExc : D.nd.l i ∉ BaseSizes.Exc L := by
    rw [← hexc]
    exact_mod_cast hx
  have hB := hCB i hl hk hExc (GlobalTheory.NLink.RowE.weightTie_of D hW i) hHG (r i) (hP.good i) π hZ (ρ i π)
    (GlobalTheory.NLink.RowE.isRankRPart_of D i _ _ (hP.compl i π hZ))
  obtain ⟨hK1, hK2⟩ := hK i hTw
  have hram := GlobalTheory.Proof.QuotientLengthInfimum.ramLen_ne D i

  have hsP : BaseSizes.sPi D i π (ρ i π) ≠ ⊤ := GlobalTheory.NLink.RowE.nlen_ne_top _ _ (hK1 π hπ).1.ne hram.1
  have hsR : (BaseSizes.sPi D i π (ρ i π)).toReal = (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) :=
    GlobalTheory.NLink.RowE.nlen_toReal _ _ _

  have hodd : Odd (D.nd.l i) := by
    refine (D.nd.lPrime i).out.odd_of_ne_two fun h2 => ?_
    have h4 : (3 : ℝ) < (D.nd.l i : ℝ) := lt_of_le_of_lt h3 hl
    rw [h2] at h4
    norm_num at h4
  have hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) ≠ ⊤ := by
    intro e he
    rw [Finset.mem_Ioo] at he
    exact @hS (D.nd.l i) (D.nd.lPrime i) e he.1 he.2
  have hshaF : BaseSizes.shaSum D i ≠ ⊤ := by
    unfold BaseSizes.shaSum
    exact ENNReal.sum_ne_top.2 fun e he => by simpa using hsha e he
  have hshaR : (BaseSizes.shaSum D i).toReal = TwistedPlaces.VVr D (D.nd.l i) := by
    unfold BaseSizes.shaSum TwistedPlaces.VVr
    rw [ENNReal.toReal_sum (fun e he => by simpa using hsha e he)]
    rw [show D.what₂.VV (D.nd.l i) = ∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen (D.nd.l i) e from rfl,
      show Finset.Ico 1 D.R.t = Finset.Ioo 0 D.R.t by ext; simp; omega]
    push_cast
    refine Finset.sum_congr rfl fun e he => ?_
    have he' := Finset.mem_Ioo.1 he
    rw [GlobalTheory.NLink.RowE.toReal_enat, D.nd.sha_eq (D.nd.l i) e he'.1 he'.2 _ (ENat.coe_toNat (hsha e he)).symm]
    push_cast
    rfl

  have hvC : BaseSizes.vClass D i ≠ ⊤ := by
    unfold BaseSizes.vClass
    simp
  have hvCR : (BaseSizes.vClass D i).toReal = TwistedPlaces.vhE D (D.nd.l i) := by
    unfold BaseSizes.vClass TwistedPlaces.vhE hE
    simp

  have hzeta : ∀ P ∈ D.nd.Q i, BaseSizes.zetaP D i P - 1 ≠ 0 := by
    intro P hP
    rw [BaseSizes.zetaP_eq D i P hP, sub_ne_zero]
    exact ((GlobalTheory.TameDesign.main D i).2 P (Or.inr hP)).2.2.1 hP
  have hvO : ∀ P ∈ D.nd.Q i, BaseSizes.vO (D.nd.O i) (D.nd.l i) (BaseSizes.zetaP D i P - 1) ≠ ⊤ := by
    intro P hP
    refine GlobalTheory.NLink.RowE.nlen_ne_top _ _ ?_ hram.1
    rw [Module.length_ne_top_iff]
    exact isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero (hzeta P hP))
  have hepsF : BaseSizes.epsQ D i ≠ ⊤ := by
    unfold BaseSizes.epsQ
    exact ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.2 hvO)
  have hepsR : (BaseSizes.epsQ D i).toReal ≤ TwistedPlaces.epsL (D.nd.l i) := by
    refine Eq.trans_le ?_ hK2
    unfold BaseSizes.epsQ
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum hvO]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun P hP => ?_
    unfold BaseSizes.vO
    rw [GlobalTheory.NLink.RowE.nlen_toReal, BaseSizes.zetaP_eq D i P hP]

  have hvcc : (BaseSizes.vCC D i π).toReal = (D.nd.vcc i π : ℝ) := by
    rw [GlobalTheory.Proof.QuotientLengthInfimum.vCC_eq]
    exact GlobalTheory.NLink.RowE.nlen_toReal _ _ _
  have hmono := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hsP, hshaF⟩, hvC⟩, hepsF⟩) hB
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hsP, hshaF⟩, hvC⟩) hepsF,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hsP, hshaF⟩) hvC, ENNReal.toReal_add hsP hshaF,
    hvcc, hsR, hshaR, hvCR] at hmono
  unfold Bd
  linarith

end GlobalTheory.NLink.RowE

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogHostClassNumberLeScalePowFamily
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.ClassNumHost

theorem totCx (D : D7) : IsTotallyComplex D.host.E := by
  first
  | exact inferInstance
  | (haveI : IsCMField D.host.E := D.host.isCMField_hostE; exact inferInstance)

theorem log_hE_le_rd (D : D7) :
    Real.log (Formalism.MainNotions.N.hE D.host : ℝ) ≤ (D.R.f : ℝ) * Real.log D.host.rdE +
      2 * D.R.f * Real.log (1 + D.R.f * Real.log D.host.rdE) := by
  haveI := totCx D
  have hf := Formalism.MainNotions.TwistedPlaces.finrank_E_host D
  have h := GlobalTheory.log_classNumber_le_log_abs_discr_div D.host.E D.R.f hf
  have hd : 0 < |(discr D.host.E : ℝ)| := by
    have := NumberField.discr_ne_zero D.host.E
    positivity
  have hrd : Real.log D.host.rdE = Real.log |(discr D.host.E : ℝ)| / (2 * D.R.f) := by
    unfold Formalism.BasicNotions.Host.rdE
    rw [Real.log_rpow hd, hf]
    push_cast
    ring
  rw [hrd]
  unfold Formalism.MainNotions.N.hE
  exact h

theorem log_hE_le_lin (D : D7) (h1 : 1 ≤ D.host.rdE) :
    Real.log (Formalism.MainNotions.N.hE D.host : ℝ) ≤ (1 + 2 * D.R.f) * ((D.R.f : ℝ) * Real.log D.host.rdE) := by
  have h := log_hE_le_rd D
  have hY : 0 ≤ (D.R.f : ℝ) * Real.log D.host.rdE := mul_nonneg (by positivity) (Real.log_nonneg h1)
  have hl : Real.log (1 + D.R.f * Real.log D.host.rdE) ≤ D.R.f * Real.log D.host.rdE := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + D.R.f * Real.log D.host.rdE by linarith)
    linarith
  have hf0 : (0:ℝ) ≤ 2 * D.R.f := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hl hf0]

end GlobalTheory.ClassNumHost

namespace GlobalTheory.ClassNumHost

theorem log_rd_le (D : D7) (h1 : 1 ≤ D.host.rdE)
    (h2 : D.host.rdE ≤ (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d)) :
    Real.log D.host.rdE ≤ 2 * D.R.n + (Real.log D.host.q + Real.log D.host.d) / 2 := by
  have hn : (0:ℝ) < D.R.n := by
    have : 0 < D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hqd : (0:ℝ) < (D.host.q : ℝ) * D.host.d := by
    rcases (show (0:ℝ) ≤ (D.host.q : ℝ) * D.host.d by positivity).lt_or_eq with h | h
    · exact h
    · rw [← h, Real.sqrt_zero] at h2; linarith
  have hq : (0:ℝ) < D.host.q := by
    rcases (show (0:ℝ) ≤ D.host.q by positivity).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hqd; exact absurd hqd (lt_irrefl 0)
  have hd : (0:ℝ) < D.host.d := by
    rcases (show (0:ℝ) ≤ D.host.d by positivity).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hqd; exact absurd hqd (lt_irrefl 0)
  have hQ : (D.host.QS : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by exact_mod_cast D.host.QS_le
  have h3 : D.host.rdE ≤ (D.R.n : ℝ) ^ 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) :=
    h2.trans (mul_le_mul_of_nonneg_right (by have : (0:ℝ) ≤ D.host.QS := Nat.cast_nonneg _; linarith) (Real.sqrt_nonneg _))
  have hl := Real.log_le_log (by linarith) h3
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_sqrt hqd.le, Real.log_mul hq.ne' hd.ne'] at hl
  push_cast at hl
  have hn' : Real.log (D.R.n : ℝ) ≤ D.R.n := by
    have := Real.log_le_sub_one_of_pos hn; linarith
  linarith

end GlobalTheory.ClassNumHost

namespace GlobalTheory

theorem log_hE_le_pow : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x →
    ∀ i : Fm.Ix x, Real.log (Formalism.MainNotions.N.hE (Fm.D x i).host : ℝ) ≤ C * x ^ C := by
  intro eps Fm
  set A : ℝ := |2 + 8 * eps + eps / 100| + |eps / 5 + eps / 100| + 1 with hA
  have hA1 : 1 ≤ A := by have := abs_nonneg (2 + 8 * eps + eps / 100); have := abs_nonneg (eps / 5 + eps / 100); linarith
  refine ⟨30 + 3 * A, 1, fun x hx1 hx i => ?_⟩
  have hs := Fm.sizes x hx i
  obtain ⟨hN, -, -, -, -, -, hQD, -⟩ := hs
  have hLx := Fm.L_x x i hx
  have hLe := Fm.L_eps x i
  unfold SizeN szTh at hN
  unfold SizeQD szTh at hQD
  rw [hLx, hLe] at hN hQD
  obtain ⟨-, -, hq, -, hd, -, hr1, hr2⟩ := hQD
  set D := Fm.D x i with hD
  have hx0 : (0:ℝ) < x := by linarith
  have mono : ∀ a : ℝ, a ≤ A → x ^ a ≤ x ^ A := fun a ha => Real.rpow_le_rpow_of_exponent_le hx1 ha
  have hP1 : 1 ≤ x ^ A := Real.one_le_rpow hx1 (by linarith)
  set P := x ^ A with hP
  have hn : (D.R.n : ℝ) ≤ P := hN.2.trans (mono _ (by
    have := le_abs_self (2 + 8 * eps + eps / 100); have := abs_nonneg (eps / 5 + eps / 100); linarith))
  have hqP : Real.log D.host.q ≤ P := hq.trans (mono _ (by
    have := le_abs_self (eps / 5 + eps / 100); have := abs_nonneg (2 + 8 * eps + eps / 100); linarith))
  have hdP : Real.log D.host.d ≤ P := hd.trans (mono _ (by
    have := le_abs_self (eps / 5 + eps / 100); have := abs_nonneg (2 + 8 * eps + eps / 100); linarith))
  have hrd := GlobalTheory.ClassNumHost.log_rd_le D hr1 hr2
  have hrdP : Real.log D.host.rdE ≤ 3 * P := by linarith
  have hrd0 : 0 ≤ Real.log D.host.rdE := Real.log_nonneg hr1
  have hf : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hfP : (D.R.f : ℝ) ≤ 2 * P := by rw [hf]; linarith
  have hf0 : (0:ℝ) ≤ D.R.f := by positivity
  have hmain := GlobalTheory.ClassNumHost.log_hE_le_lin D hr1
  have hY : (D.R.f : ℝ) * Real.log D.host.rdE ≤ 6 * P ^ 2 := by
    calc (D.R.f : ℝ) * Real.log D.host.rdE ≤ (2 * P) * (3 * P) :=
          mul_le_mul hfP hrdP hrd0 (by linarith)
      _ = 6 * P ^ 2 := by ring
  have hY0 : 0 ≤ (D.R.f : ℝ) * Real.log D.host.rdE := mul_nonneg hf0 hrd0
  have h1f : 1 + 2 * (D.R.f : ℝ) ≤ 5 * P := by linarith
  have hbound : Real.log (Formalism.MainNotions.N.hE D.host : ℝ) ≤ 30 * P ^ 3 := by
    calc _ ≤ (1 + 2 * D.R.f) * ((D.R.f : ℝ) * Real.log D.host.rdE) := hmain
      _ ≤ (5 * P) * (6 * P ^ 2) := mul_le_mul h1f hY hY0 (by linarith)
      _ = 30 * P ^ 3 := by ring
  have hP3 : P ^ 3 = x ^ (3 * A) := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  have hxC : x ^ (3 * A) ≤ x ^ (30 + 3 * A) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hx3 : 1 ≤ x ^ (3 * A) := Real.one_le_rpow hx1 (by linarith)
  rw [hP3] at hbound
  calc _ ≤ 30 * x ^ (3 * A) := hbound
    _ ≤ (30 + 3 * A) * x ^ (30 + 3 * A) := by nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergKernelZeroCoeffTwoCentralChars
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

open GlobalTheory.ThetaPoisson GlobalTheory.RSTheta GlobalTheory.Petersson GlobalTheory.CuspQuot GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix

noncomputable section

namespace GlobalTheory.RSResidue

theorem rsHat_zero_props_two : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → ∀ (φ φ' : Sm E a), φ.1 ∈ GlobalTheory.Petersson.bddForms E a ω → φ'.1 ∈ GlobalTheory.Petersson.bddForms E a ω' → ∀ (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), GlobalTheory.CuspQuot.IsTest (GlobalTheory.RSTheta.rowSet E ℓ) Φ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E), Continuous (fun g => GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧ (∃ C : ℝ, ∀ g, ‖GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0‖ ≤ C) ∧ (∀ (γ : GL (Fin a) E) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (ratGL E a γ * g) 0 = GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧ ∀ (z : Neutral.B1.Ideles E) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (GeneralLinearGroup.scalar (Fin a) z * g) 0 = ((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 := by
  intro E _ _ _ a ω ω' hω hω' φ φ' h h' ℓ Φ hΦ J η
  obtain ⟨c, hc⟩ := rsHat_zero_eq J η φ φ' hΦ
  have hc' : ∀ g, rsHat ℓ φ.1 φ'.1 Φ J η g 0 = (∫ u, rsInf ℓ φ.1 φ'.1 Φ g u ∂infMeasure E a) * c := hc
  have hj : Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ.1 φ'.1 Φ p.1 p.2 :=
    continuous_rsInf h.1 h'.1 hΦ.1.continuous hΦ.2.2
  have h0 : ∀ g, ∀ u ∉ tsupport Φ, rsInf ℓ φ.1 φ'.1 Φ g u = 0 := fun g u hu => by
    rw [rsInf, image_eq_zero_of_notMem_tsupport hu, mul_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [hc']
    exact (continuous_integral_of_compact (infMeasure E a) hΦ.2.1 hj h0).mul continuous_const
  · obtain ⟨C, hC⟩ := h.2.2.2
    obtain ⟨C', hC'⟩ := h'.2.2.2
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
    have hi : Integrable (fun u => C * C' * ‖Φ u‖) (infMeasure E a) :=
      (integrable_infMeasure hΦ.1.continuous hΦ.2.1).norm.const_mul _
    refine ⟨(∫ u, C * C' * ‖Φ u‖ ∂infMeasure E a) * ‖c‖, fun g => ?_⟩
    rw [hc', norm_mul]
    refine mul_le_mul_of_nonneg_right (norm_integral_le_of_norm_le hi (.of_forall fun u => ?_)) (norm_nonneg _)
    rw [rsInf, norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hC' _) (norm_nonneg _) hC0) (norm_nonneg _)
  · intro γ g
    have e : rsPsi ℓ φ.1 φ'.1 Φ J η (ratGL E a γ * g) = rsPsi ℓ φ.1 φ'.1 Φ J η g := funext fun y =>
      rsPsi_ratGL_mul ℓ h.2.1 h'.2.1 Φ J η γ g y
    simp only [rsHat, e]
  · intro z g
    have e : ∀ u, rsInf ℓ φ.1 φ'.1 Φ (GeneralLinearGroup.scalar (Fin a) z * g) u =
        ((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * rsInf ℓ φ.1 φ'.1 Φ g u := fun u => by
      simp only [rsInf, mul_assoc (GeneralLinearGroup.scalar (Fin a) z) g, h.2.2.1, h'.2.2.1, map_mul]
      ring
    rw [hc', hc', funext e, integral_const_mul]
    ring

end GlobalTheory.RSResidue
end
end

