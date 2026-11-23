module

public import Mathlib
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAMulMemIntAt
public import Formalism.LocalRingCardinality.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryLocalPointLatticeGraphNormIdentity
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0582
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLocalComponentData
section
noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix GlobalTheory.GoodPos

namespace GlobalTheory.LineOffT

theorem exists_place (E : Type) [Field E] [NumberField E] {T : ℕ} (hT : T.Prime) :
    ∃ P : HeightOneSpectrum (𝓞 E), (T : 𝓞 E) ∈ P.asIdeal := by
  have hne : Ideal.span {(T : 𝓞 E)} ≠ ⊤ := fun h => by
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at h1
    rcases (Nat.pow_eq_one.1 h1) with h2 | h2
    · exact hT.one_lt.ne' h2
    · exact (Module.finrank_pos (R := ℤ) (M := 𝓞 E)).ne' h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : (T : 𝓞 E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  exact ⟨⟨M, hM.isPrime, fun h => Nat.cast_ne_zero.2 hT.ne_zero (by rwa [h, Ideal.mem_bot] at hmem)⟩, hmem⟩

variable {D : D7}

theorem isU_nat {x : GlobalTheory.FinPl.Pl D} {N : ℕ} (hN : (N : 𝓞 D.host.F) ∉ x.asIdeal) : IsU x (incA D (N : D.host.E)) := by
  have h0 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 fun h => hN (by rw [h, Nat.cast_zero]; exact zero_mem _)
  refine IsU.of_pres (inU _ h0).mul_inv ?_ ?_
  · refine UnitAt.incA_mul_mem_intAt (N := 1)
      (by rw [Int.cast_one]; exact (Ideal.ne_top_iff_one _).1 x.isPrime.ne_top) ?_
    rw [one_smul]
    exact isIntegral_natCast _
  · refine UnitAt.incA_mul_mem_intAt (c := (N : D.host.E)⁻¹) (N := (N : ℤ)) (by rwa [Int.cast_natCast]) ?_
    rw [zsmul_eq_mul, Int.cast_natCast, mul_inv_cancel₀ h0]
    exact isIntegral_one

theorem isU_xi_of_prime {x : GlobalTheory.FinPl.Pl D} {T : ℕ} (hT : T.Prime) (hv : (T : 𝓞 D.host.F) ∈ x.asIdeal)
    (hd : T ≠ D.host.d) (hc : Nat.Coprime (Ideal.absNorm D.host.ccK) T) : IsU x (xiU D : AE D) := by
  have hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqrtMinusD_sq
  have hint : IsIntegral ℤ D.host.sqrtMinusD := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hsq]
    exact (isIntegral_natCast _).neg
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd0 : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hdp.ne_zero
  have h0 : D.host.sqrtMinusD ≠ 0 := fun e => by
    rw [e] at hsq
    exact hd0 (by simpa using hsq.symm)
  have hc0 : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hdT : Nat.Coprime D.host.d T := (Nat.coprime_primes hdp hT).2 hd.symm
  refine IsU.of_pres (xiU D).mul_inv ?_ ?_
  · refine UnitAt.incA_mul_mem_intAt (c := D.host.xi0) (N := ((Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℤ))
      (by rw [Int.cast_natCast]; exact UnitAt.notMem_of_coprime hv (Nat.Coprime.mul_left hc hdT)) ?_
    convert hint using 1
    rw [zsmul_eq_mul, Int.cast_natCast, Nat.cast_mul, Host.xi0]
    field_simp
    linear_combination -hsq
  · refine UnitAt.incA_mul_mem_intAt (c := D.host.xi0⁻¹) (N := 1)
      (by rw [Int.cast_one]; exact (Ideal.ne_top_iff_one _).1 x.isPrime.ne_top) ?_
    rw [one_smul, Host.xi0, inv_div, div_neg, div_one]
    exact ((isIntegral_natCast _).mul hint).neg

theorem isU_alpha_of_prime {x : GlobalTheory.FinPl.Pl D} {T : ℕ} (hT : T.Prime) (hv : (T : 𝓞 D.host.F) ∈ x.asIdeal) (h2 : T ∉ D.host.small)
    (hq : T ≠ D.host.q) (hd : T ≠ D.host.d) (hc : Nat.Coprime (Ideal.absNorm D.host.ccK) T)
    {L : Formalism.BasicNotions.TH.HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) {α : (AE D)ˣ}
    (hα : ∀ (S : Formalism.BasicNotions.TH.HSp D) (L : GlobalTheory.FinPl.Lat S) y,
      y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x)) : IsU x (α : AE D) := by
  have h := UnitAt.latA_eq_latV (UnitAt.notMem_of_coprime hv (GlobalTheory.TwV.HalfDiffInt.absNorm_coprime D hT h2 hq hd))
    (UnitAt.notMem_of_coprime hv hc) (fun a ha => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem _) ha)
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D)
  obtain ⟨e, he, hg⟩ := line_gen hζ (by
    first
    | exact GlobalTheory.WeilAtPlace.isSelfDualC_frameLat L
    | exact (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat L).1) x
  refine IsU.inv (fun a ha => ?_) α.inv_mul
  have h1 := hα L (GlobalTheory.AdelicU.frameLat L) ((incA D e * a) • ratV ζ)
  have e1 : incA D e⁻¹ * incA D e = 1 := (inU e he).inv_mul
  rw [h, smul_smul, hg _ (Ideal.mul_mem_left _ _ ha), hg _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha)),
    mul_left_comm (incA D e⁻¹) ((α⁻¹ : (AE D)ˣ) : AE D), ← mul_assoc (incA D e⁻¹), e1, one_mul] at h1
  exact h1

end GlobalTheory.LineOffT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightSplitPlaceChartBiInvariantTorusVal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped NNReal
namespace GlobalTheory.ChartHgt


open GlobalTheory.Doubling in
theorem hgtV_mul_stab (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (hΛ : IsSelfDualC V Λ)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    {k k' : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v} (hk : k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v)
    (hk' : k' ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) (g : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV V Λ v (k * g * k') = GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV V Λ v g := by
  haveI : Submodule.IsFullLattice D.host.E Λ := GlobalTheory.ProjXCols.selfDual_isFullLattice V Λ hΛ
  have hI := GlobalTheory.Core.Rk.IwSplit.hasIwasawa_of_algHom (GlobalTheory.AdelicU.isCMExt_host D) (gram_hdbl V) (isHermND_gram V)
    (isHermND_gram (dblSp V)) τ Λ (GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hΛ v)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV
  congr 1
  have e1 : ioH (Fv D.host.F v) D.sp.cm.sig (gram_hdbl V) (k * g * k', 1) =
      (ioDiag (R := Fv D.host.F v) (gram_hdbl V) k : GlobalTheory.AdelicU.GLoc D.sp.cm.sig (dblSp V).gram v) *
        ioH (Fv D.host.F v) D.sp.cm.sig (gram_hdbl V) (g, 1) * ioH (Fv D.host.F v) D.sp.cm.sig (gram_hdbl V) (k', k⁻¹) := by
    rw [coe_ioDiag, ← map_mul, ← map_mul]
    congr 1
    ext <;> simp [mul_assoc]
  rw [e1]
  refine (HasIwasawa.hgtH_right (continuous_absEv v) (isCompact_KFin v) hI _
    ((ioH_mem_KFin (gram_hdbl V)).2 ⟨hk', inv_mem hk⟩)).trans ?_
  refine (HasIwasawa.hgtH_left (continuous_absEv v) (isCompact_KFin v) hI _ _).trans ?_
  rw [aH_ioDiag, abs_detH (absEv_conjUnit _ v) (isHermND_gram V).2, one_mul]


open ValuativeRel in
theorem nnnorm_unif (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : (Fv F v)ˣ)
    (h : letI := GlobalTheory.LocalData.complRel v; valuation (Fv F v) (ϖ : Fv F v) = uniformizer (Fv F v)) :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    ‖(ϖ : Fv F v)‖₊ = ((GlobalTheory.SplitWeil.resCard (Fv F v) : ℕ) : ℝ≥0)⁻¹ := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  rw [GlobalTheory.LFun.SatBoundGL.resCard_completion]
  apply GlobalTheory.norm_uniformiser_eq_inv_absNorm
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))
  have h1 : Valued.v (ϖ : Fv F v) < 1 := by
    rw [← he.lt_one_iff_lt_one, h]; exact uniformizer_lt_one
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1 : ℤ))
  have h2 : Valued.v p ≤ Valued.v (ϖ : Fv F v) := by
    rw [← he.le_iff_le, h, le_uniformizer_iff, he.lt_one_iff_lt_one, hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have h0 : Valued.v (ϖ : Fv F v) ≠ 0 := (map_ne_zero _).2 ϖ.ne_zero
  rw [hp, ← WithZero.exp_log h0, WithZero.exp_le_exp] at h2
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  unfold Formalism.UG.IsUnifV
  rw [← WithZero.exp_log h0]
  have : WithZero.log (Valued.v (ϖ : Fv F v)) = -1 := by omega
  rw [this]; rfl

theorem hgtFin_ioH_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (hQ : Q = GlobalTheory.Doubling.dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F))
    (g : GlobalTheory.AdelicU.GLoc σ J v) :
    GlobalTheory.Doubling.hgtFin σ Q L v (GlobalTheory.Doubling.ioH (Fv F v) σ hQ (g, 1)) =
      GlobalTheory.Doubling.hgtFin σ (GlobalTheory.Doubling.dblGram finSumFinEquiv J) L v (GlobalTheory.Doubling.ioH (Fv F v) σ rfl (g, 1)) := by
  subst hQ; rfl

theorem min_zpow_inv (q : ℝ≥0) (hq : 1 ≤ q) (m : ℤ) : min ((q⁻¹) ^ m) (((q⁻¹) ^ m)⁻¹) = q ^ (-|m|) := by
  rw [_root_.inv_zpow', ← _root_.zpow_neg, neg_neg]
  rcases le_total 0 m with hm | hm
  · rw [abs_of_nonneg hm, min_eq_left (zpow_le_zpow_right₀ hq (by omega))]
  · rw [abs_of_nonpos hm, neg_neg, min_eq_right (zpow_le_zpow_right₀ hq (by omega))]

theorem prod_zpow_eq {ι : Type} (s : Finset ι) (q : ℝ≥0) (hq : q ≠ 0) (f : ι → ℤ) :
    ∏ i ∈ s, q ^ f i = q ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

theorem bridge : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v)
    (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ →
    Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v,
    (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) →
    ∃ (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (β : GL (Fin s.V.rank) (Fv D.host.F v))
      (ε : Fin D.R.r ⊕ Blocks k D.R.t ≃ Fin s.V.rank), GlobalTheory.AdelicU.IsSplitBasis τ s.Λ β ∧
      ∀ y, (GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram s.V) τ β (e y)).1.submatrix ε ε = y.1 := by
  intro D s k v φ ι _ hfr ⟨ε, _, hε⟩ e he
  refine ⟨_, _, ε, GlobalTheory.ChartStab.isSplitBasis_frCo hfr φ, fun y => ?_⟩
  have h2 := (hε y).2
  rw [he y, GlobalTheory.ChartStab.grpCo_emb] at h2
  exact h2

theorem isHgt_chart : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) → ∀ x ϖ, IsLocUnif φ x ϖ → GlobalTheory.ParHecke.IsHgt ϖ fun y => GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e y) := by
  intro D s k v φ ι hΛ hβ hι e he x ϖ hϖ
  obtain ⟨τ, β, ε, hB, hy⟩ := bridge D s k v φ ι hΛ hβ hι e he
  have hΨ : ∀ y, (GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram s.V) τ β (e y)).1 =
      y.1.submatrix ε.symm ε.symm := fun y => by
    rw [← hy y, Matrix.submatrix_submatrix]; simp
  have hmul : ∀ a b, e (a * b) = e a * e b := fun a b =>
    (GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram s.V) τ β).injective
      (Units.ext (by rw [map_mul, Units.val_mul, hΨ, hΨ, hΨ, Units.val_mul, Matrix.submatrix_mul_equiv]))
  have hK := GlobalTheory.ChartStab.chart_stab D s k v φ ι hΛ hβ hι e he
  refine ⟨fun κ hκ g => ⟨?_, ?_⟩, fun e' => ?_⟩
  · have := hgtV_mul_stab D s.V s.Λ hΛ v τ ((hK κ).2 hκ) (one_mem _) (e g)
    rwa [mul_one, ← hmul] at this
  · have := hgtV_mul_stab D s.V s.Λ hΛ v τ (one_mem _) ((hK κ).2 hκ) (e g)
    rwa [one_mul, ← hmul] at this
  · haveI : Submodule.IsFullLattice D.host.E s.Λ := GlobalTheory.ProjXCols.selfDual_isFullLattice s.V s.Λ hΛ
    have hsd := GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hΛ v
    obtain ⟨-, hval, -⟩ := (GlobalTheory.GraphNorm.graphNormFinite D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D)
      s.V.rank s.V.gram (GlobalTheory.Doubling.isHermND_gram s.V) s.Λ v hsd).1 τ β hB
      (e (GlobalTheory.GLDoubling.torusElt (Fv D.host.F v) _ ϖ e'))
    have hd : GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice.IsElemDiv (GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D)
        (GlobalTheory.Doubling.isHermND_gram s.V) τ β (e (GlobalTheory.GLDoubling.torusElt (Fv D.host.F v) _ ϖ e')))
        (fun i => ϖ ^ e' (ε.symm i)) := by
      refine ⟨1, one_mem _, 1, one_mem _, ?_⟩
      rw [hΨ, GlobalTheory.GLDoubling.val_torusElt, Matrix.submatrix_diagonal_equiv]
      simp
    have h1 := hval _ hd
    obtain ⟨-, -, -, -, hv⟩ := hϖ
    have hn := nnnorm_unif _ v ϖ hv
    have hq : 1 ≤ ((GlobalTheory.SplitWeil.resCard (Fv D.host.F v) : ℕ) : ℝ≥0) := by
      rw [GlobalTheory.LFun.SatBoundGL.resCard_completion]
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (fun h0 => v.ne_bot ((Ideal.absNorm_eq_zero_iff).1 h0))
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e (GlobalTheory.GLDoubling.torusElt (Fv D.host.F v) _ ϖ e')) =
        (GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice.graphHgt D.sp.cm.sig s.V.gram s.Λ v (e (GlobalTheory.GLDoubling.torusElt (Fv D.host.F v) _ ϖ e')) : ℝ) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice.graphHgt
      exact congrArg _ (hgtFin_ioH_eq _ _ _ _ _ _ _)
    refine e2.trans ?_
    rw [h1]
    simp only [Units.val_zpow_eq_zpow_val, nnnorm_zpow, hn]
    simp only [min_zpow_inv _ hq]
    rw [prod_zpow_eq _ _ (zero_lt_one.trans_le hq).ne', NNReal.coe_zpow, NNReal.coe_natCast, Finset.sum_neg_distrib]
    congr 2
    exact Equiv.sum_comp ε.symm (fun a => |e' a|)

end GlobalTheory.ChartHgt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalFactorizationOfWeilDualPair
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem unrAt_inv_of_unrAt {D : D7} {χ : (AE D)ˣ →* Circle} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : GlobalTheory.LFun.UnrAt χ w) : GlobalTheory.LFun.UnrAt χ⁻¹ w := by
  intro x hx
  have := h x hx
  simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv] at this ⊢
  rw [this, inv_one]

theorem isHeckeChar_inv_sph {D : D7} {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ := by
  refine ⟨?_, fun x => ?_⟩
  · have : (χ⁻¹ : (AE D)ˣ →* Circle) = fun x => (χ x)⁻¹ := rfl
    rw [this]; exact h.1.inv
  · rw [MonoidHom.inv_apply, h.2 x, inv_one]


set_option maxHeartbeats 1000000 in
theorem sphFactor_of_weilRepresentationUnitaryPair (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) (D : D7) : SphFactor D := by
  intro ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU v hv s
  obtain ⟨omh, homh⟩ := _root_.GlobalTheory.Core.Rk.exists_doubled_weilDatum hW D ψ A B χA χB om hP.weil
  have hTC := _root_.GlobalTheory.DoublingTheta.thetaClause D ψ A B χA χB om omh hP.weil homh
  have hCC := _root_.GlobalTheory.Core.Rk.coefClause_of_thetaClause D ψ A B χA χB om omh hP.weil hTC ν 𝓕 hP.covol
  have hδ := (hTC Φ₁ Φ₂ hΦ₁ hΦ₂).1
  have hco := (hCC Φ₁ Φ₂ hΦ₁ hΦ₂).2
  have hlaw := _root_.GlobalTheory.Core.Rk.SWLaw.swSec_law hW D ψ A B χB omh homh ν 𝓕 hP.covol _ hδ
  have hvac := _root_.GlobalTheory.Core.Rk.IP.VacFix.main D ψ A B χB omh homh LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU v hv
  haveI : Submodule.IsLattice D.host.E LA := hU.sdA.1
  haveI : Submodule.IsFullLattice D.host.E LA := GlobalTheory.ProjXCols.selfDual_isFullLattice A LA hU.sdA
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (KAd D.sp.cm.sig (dblSp A).gram LA a) :=
    _root_.GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D A LA a hU.sdA hP.maj
  haveI := t2Space_adeleRing' (F := D.host.F)
  have hK : IsCompact (KAd D.sp.cm.sig (dblSp A).gram LA a : Set (GA D (dblSp A))) := isCompact_KAd (isCMExt_host D)
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : GA D (dblSp A) → ℂ, Ψ = fun g => swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂) g *
      npow (hgtAd D.sp.cm.sig (dblSp A).gram LA a g) (s - sZero A B) := ⟨_, rfl⟩
  have hw : ∀ g : GA D A, wcoef om ν 𝓕 Φ₁ Φ₂ g * npow (hgtL A LA a g) (s - sZero A B) = Ψ (io A (g, 1)) := by
    intro g
    simp only [hΨdef, wcoef, hgtL, hco g]
  have hΨlaw : ∀ (p : siegelH _ D.sp.cm.sig (dblSp A).gram) (g : GA D (dblSp A)),
      Ψ ((p : GA D (dblSp A)) * g) = (χB⁻¹ (aH _ D.sp.cm.sig (dblSp A).gram p) : Circle) *
        npow (absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) * Ψ g := by
    intro p g
    simp only [hΨdef]
    have hleft : hgtAd D.sp.cm.sig (dblSp A).gram LA a ((p : GA D (dblSp A)) * g) =
        absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p) * hgtAd D.sp.cm.sig (dblSp A).gram LA a g :=
      hI.hgtH_left continuous_absE hK p g
    have hr : npow (absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) =
        npow (absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p)) (sZero A B + (A.rank : ℂ) / 2) *
          npow (absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p)) (s - sZero A B) := by
      rw [← npow_add (hom_pos (absE D.host.F D.host.E) (aH _ D.sp.cm.sig (dblSp A).gram p))]
      congr 1; ring
    rw [hlaw p g, hleft, Doubling.npow_mul, hr]
    ring
  have hΨright : ∀ g, ∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram LA v,
      Ψ (g * emb D.sp.cm.sig (dblSp A).gram v k) = Ψ g := by
    intro g k hk
    simp only [hΨdef]
    have hright : hgtAd D.sp.cm.sig (dblSp A).gram LA a (g * emb D.sp.cm.sig (dblSp A).gram v k) =
        hgtAd D.sp.cm.sig (dblSp A).gram LA a g := hI.hgtH_right continuous_absE hK g (emb_mem_KAd hk)
    rw [hright]
    congr 1
    simp only [swSec]
    rw [show ((g * emb D.sp.cm.sig (dblSp A).gram v k, (1 : GA D B))) =
      (g, 1) * (emb D.sp.cm.sig (dblSp A).gram v k, 1) by simp, map_mul, Module.End.mul_apply, hvac k hk]
  have hunr : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χB⁻¹ w := by
    intro w hw'
    refine unrAt_inv_of_unrAt (hU.unr w ?_)
    intro hmem
    exact hv (by simpa [GlobalTheory.LFun.above, hw'] using hmem)
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.Core.Rk.SphSec.exists_isSphSecAt_unique D A LA hU.sdA χB⁻¹ (isHeckeChar_inv_sph homh.hecT) v hunr s
  have huniq := hφ.2
  refine ⟨φ, hφ.1, fun x hx y => ?_⟩
  have hx' : proj D.sp.cm.sig (dblSp A).gram v (io A (x, 1)) = 1 := by
    rw [io, proj_ioH, hx, map_one, ioH_one]
  have hl : ∀ (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram) (g : Gv (dblSp A) v),
      Ψ (emb D.sp.cm.sig (dblSp A).gram v (p * g) * io A (x, 1)) =
        charAt χB⁻¹ v (aH _ D.sp.cm.sig (dblSp A).gram p) *
          npow (absEv D.host.F D.host.E v (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) *
          Ψ (emb D.sp.cm.sig (dblSp A).gram v g * io A (x, 1)) := by
    intro p g
    rw [map_mul, mul_assoc, ← coe_embP, hΨlaw, aH_embP, absE_ideleAt]
    rfl
  have hr : ∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram LA v, ∀ g : Gv (dblSp A) v,
      Ψ (emb D.sp.cm.sig (dblSp A).gram v (g * k) * io A (x, 1)) =
        Ψ (emb D.sp.cm.sig (dblSp A).gram v g * io A (x, 1)) := by
    intro k hk g
    rw [map_mul, mul_assoc, (commute_emb D.sp.cm.sig (dblSp A).gram k hx').eq, ← mul_assoc, hΨright _ k hk]
  have key := huniq (fun g => Ψ (emb D.sp.cm.sig (dblSp A).gram v g * io A (x, 1))) hl hr (ioAt A v y)
  simp only [map_one, one_mul] at key
  rw [hw, hw, ← key, ioAt, emb_ioH, io, ← map_mul, Prod.mk_mul_mk, map_one, one_mul,
    (commute_emb D.sp.cm.sig A.gram y hx).eq]

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TendstoSetIntegralUnramifiedOutsideOpenSubset
section
noncomputable section

namespace GlobalTheory.Core.Rk.IP

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem measurableSet_openOff {D : D7} (A : HSp D) (L : Lat A) (hL : IsSelfDualC A L) (S : Finset (FinPl D)) :
    MeasurableSet (openOff A L S) := by
  have : BorelSpace (GA D A) := ⟨rfl⟩
  have : Countable (FinPl D) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum D.host.F
  haveI := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  have e : openOff A L S = ⋂ v, ⋂ (_ : v ∉ S),
      (proj D.sp.cm.sig A.gram v) ⁻¹' (stabLoc D.sp.cm.sig A.gram L v : Set _) := by
    ext g; simp [openOff]
  rw [e]
  exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
    ((isOpen_stabLoc D.sp.cm.sig A.gram L v).preimage (continuous_proj D.sp.cm.sig A.gram v)).measurableSet

theorem monotone_openOff {D : D7} (A : HSp D) (L : Lat A) : Monotone (openOff A L) :=
  fun _ _ h _ hg v hv => hg v fun h' => hv (h h')

theorem iUnion_openOff {D : D7} (A : HSp D) (L : Lat A) (hL : IsSelfDualC A L) : ⋃ S, openOff A L S = Set.univ := by
  haveI := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  refine Set.eq_univ_of_forall fun g => ?_
  have h := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc D.sp.cm.sig A.gram L g)
  exact Set.mem_iUnion.2 ⟨h.toFinset, fun v hv => by_contra fun h' => hv (h.mem_toFinset.2 h')⟩

theorem tendsto_setIntegral_openOff : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (m : Measure (GA D A)) (F : GA D A → ℂ), Integrable F m → Filter.Tendsto (fun S : Finset (FinPl D) => ∫ g in openOff A L S, F g ∂m) Filter.atTop (nhds (∫ g, F g ∂m)) := by
  intro D A L hL m F hF
  have : Countable (FinPl D) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum D.host.F
  have h := tendsto_setIntegral_of_monotone (μ := m) (f := F) (measurableSet_openOff A L hL) (monotone_openOff A L)
    hF.integrableOn
  rwa [iUnion_openOff A L hL, Measure.restrict_univ] at h

end GlobalTheory.Core.Rk.IP

end
end

