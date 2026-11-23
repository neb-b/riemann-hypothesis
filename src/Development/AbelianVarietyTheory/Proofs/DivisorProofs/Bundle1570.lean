module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0995
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerChainMatricesWithNormBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0745
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0861
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPoissonSummationAnyHaar
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.PoissonReindex

open GlobalTheory.SWQ

variable {F : Type} [Field F] [NumberField F]

def reidx {κ ι : Type} (e : κ ≃ ι) : (ι → AF F) ≃ₜ+ (κ → AF F) where
  toFun u i := u (e i)
  invFun x j := x (e.symm j)
  left_inv u := by funext j; simp
  right_inv x := by funext i; simp
  map_add' u v := rfl
  continuous_toFun := continuous_pi fun i => continuous_apply _
  continuous_invFun := continuous_pi fun j => continuous_apply _

theorem reidx_apply {κ ι : Type} (e : κ ≃ ι) (u : ι → AF F) (i : κ) : reidx (F := F) e u i = u (e i) := rfl

theorem dot_reidx {κ ι : Type} [Fintype κ] [Fintype ι] (e : κ ≃ ι) (u y : ι → AF F) :
    reidx e u ⬝ᵥ reidx e y = u ⬝ᵥ y := by
  simp only [dotProduct, reidx_apply]
  exact e.sum_comp (fun j => u j * y j)

theorem Bd_half {N : ℕ} (s u : Fin N → AF F) : Bd (AF F) (fun _ : Fin N => (1 / 2 : F)) s u = s ⬝ᵥ u := by
  simp only [Bd, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (2 : F) * (1 / 2) = 1 by norm_num, map_one, one_mul]

theorem mem_schA_reidx {κ ι : Type} [Fintype κ] [Fintype ι] (e : κ ≃ ι) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ schA F κ) : (fun u => Φ (reidx e u)) ∈ schA F ι := by
  have h := GlobalTheory.RestrSchA.mem_schA_comp_extend F e.symm e.symm.injective Φ hΦ
  convert h using 2 with u
  congr 1
  funext i
  rw [reidx_apply]
  conv_rhs => rw [← e.symm_apply_apply i]
  exact (e.symm.injective.extend_apply u 0 (e i)).symm

end GlobalTheory.PoissonReindex


open GlobalTheory.SWQ GlobalTheory.PoissonReindex in
theorem GlobalTheory.PoissonReindex.poisson_any : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure],
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ →
      thetaSum F (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) = c * thetaSum F Φ := by
  intro F _ _ hF ψ hψ κ _ inst hB μ hμ
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hinst : inst = MeasurableSpace.pi := by
    rw [hB.measurable_eq]
    exact (Pi.borelSpace (ι := κ) (X := fun _ => AF F)).measurable_eq.symm
  subst hinst
  set N := Fintype.card κ
  let e : κ ≃ Fin N := Fintype.equivFin κ
  have hC1 := GlobalTheory.StdCharFromIsStd.isCharAF hψ
  obtain ⟨lam, hlam⟩ := GlobalTheory.SWQ.exists_isLam F hF ψ hC1
  obtain ⟨ν, hν⟩ := GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F
  let a : Fin N → F := fun _ => 1 / 2
  have hC : Ctx ψ lam ν a := ⟨hF, hC1, hlam, hν, fun _ => by norm_num [a]⟩
  obtain ⟨hHaar, -⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hν
  haveI := hHaar
  let T : (Fin N → AF F) ≃ₜ+ (κ → AF F) := reidx e
  let Tm : (Fin N → AF F) ≃ᵐ (κ → AF F) := T.toHomeomorph.toMeasurableEquiv
  have hTm : ∀ u, Tm u = T u := fun _ => rfl
  haveI hm : (Measure.map Tm (muV N ν)).IsAddHaarMeasure := T.isAddHaarMeasure_map (muV N ν)
  have hr := Measure.isAddLeftInvariant_eq_smul μ (Measure.map Tm (muV N ν))
  set r := μ.addHaarScalarFactor (Measure.map Tm (muV N ν))
  have hr0 : (r : ℂ) ≠ 0 := by
    intro h
    have h' : r = 0 := by exact_mod_cast h
    rw [h', zero_smul] at hr
    exact (NeZero.ne μ) hr
  refine ⟨(r : ℂ), hr0, fun Φ hΦ hFΦ => ?_⟩
  set G : (κ → AF F) → ℂ := fun y => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ with hG
  set Φ' : (Fin N → AF F) → ℂ := fun u => Φ (T u) with hΦ'
  have key : ∀ y', G (T y') = (r : ℂ) * Fo ψ ν a Φ' y' := by
    intro y'
    simp only [hG]
    rw [hr, integral_smul_nnreal_measure, integral_map_equiv]
    simp only [Fo, hΦ', hTm, a, Bd_half, T, dot_reidx]
    rw [NNReal.smul_def, Complex.real_smul]
  have hΦ's : Φ' ∈ schA F (Fin N) := mem_schA_reidx e hΦ
  have hD : Decay Φ' := GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ' hΦ's
  have hGs : (fun u => G (T u)) ∈ schA F (Fin N) := mem_schA_reidx e hFΦ
  have hFeq : Fo ψ ν a Φ' = (r : ℂ)⁻¹ • fun u => G (T u) := by
    funext u
    simp only [Pi.smul_apply, smul_eq_mul, key u]
    rw [← mul_assoc, inv_mul_cancel₀ hr0, one_mul]
  have hFD : Decay (Fo ψ ν a Φ') := by
    rw [hFeq]
    exact GlobalTheory.SchwartzDecay.decay_smul _ (GlobalTheory.SchwartzDecay.decay_of_mem_schA F N _ hGs)
  have hP := GlobalTheory.SWQ.poisson_summation F N ψ lam ν a hC Φ' hD hFD
  let E2 : (Fin N → F) ≃ (κ → F) :=
    { toFun := fun ξ i => ξ (e i), invFun := fun η j => η (e.symm j),
      left_inv := fun ξ => by funext j; simp, right_inv := fun η => by funext i; simp }
  have hth : ∀ H : (κ → AF F) → ℂ, thetaSum F H = th (fun u => H (T u)) := by
    intro H
    simp only [thetaSum, th]
    exact ((E2.tsum_eq (fun η => H (fun i => algebraMap F (AF F) (η i))))).symm
  rw [hth G, hth Φ]
  simp only [th] at hP ⊢
  simp only [key, tsum_mul_left]
  rw [hP]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.BrPairF

variable {K ι : Type} [Field K] [Fintype ι] {n N : ℕ}

def brPairF (σ : ι → DomWeight n) (hN : N = n + 1) (Λ : ι → DomWeight N) :
    VV K Λ →ₗ[K] (VV K fun τ => (σ τ).dual) →ₗ[K] K :=
  (pairBK σ).compl₁₂ (Formalism.L2.Col.Br.brStd hN Λ σ) (GlobalTheory.FunObj.funEquiv σ).symm.toLinearMap

theorem brPairF_apply (σ : ι → DomWeight n) (hN : N = n + 1) (Λ : ι → DomWeight N) (u : VV K Λ)
    (v : VV K fun τ => (σ τ).dual) :
    brPairF σ hN Λ u v = pairBK σ (Formalism.L2.Col.Br.brStd hN Λ σ u) ((GlobalTheory.FunObj.funEquiv σ).symm v) := rfl

end GlobalTheory.BrPairF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeMulOfUnipotentCoverDiscreteSubgroup
section
open scoped TensorProduct NNReal ENNReal Matrix Pointwise
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem card_le_mul_of_unip_cover : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ Γ Q : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M) (μ : Measure G) (D V W : Set G), SemiLat N M Λ ν π DN DM → Λ ≤ Γ → Λ ≤ Q → IsClosed (Q : Set G) → (∀ q ∈ Q, ∃ u ∈ N, ∃ x ∈ M, q = u * x) → (∀ K : Set G, IsCompact K → (K ∩ Γ).Finite) → μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → IsCompact V → IsCompact W → ∃ B : ℝ, 0 ≤ B ∧ ∀ (a : G) (Y T : Finset G), (∀ x ∈ M, a * x = x * a) → (∀ u, u ∈ N ↔ a⁻¹ * u * a ∈ N) → (∀ y ∈ Y, y ∈ N) → (∀ u ∈ N, ∃ γ ∈ Λ, γ ∈ N ∧ ∃ y ∈ Y, ∃ w ∈ V, γ * u = y * a * w * a⁻¹) → (∀ t ∈ T, t ∈ Γ) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ Λ → t = t') → (∀ t ∈ T, ∃ q ∈ Q, ∃ w ∈ W, t = q * a * w) → (T.card : ℝ) ≤ B * Y.card := by
  intro G _ _ _ _ _ _ _ _ N M Λ Γ Q _ ν π DN DM μ D V W H hΛΓ hΛQ hQ hQd hdisc hμ hD hV hW
  haveI := H.haarN
  obtain ⟨U, hUc, hU1⟩ := exists_compact_mem_nhds (1 : G)
  have hU0 : μ U ≠ 0 := (lt_of_lt_of_le (isOpen_interior.measure_pos μ ⟨1, mem_interior_iff_mem_nhds.2 hU1⟩) (measure_mono interior_subset)).ne'
  have hUt : μ U ≠ ⊤ := hUc.measure_ne_top
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.Packing.packing_count G Γ Λ μ D U hΛΓ hdisc hμ hD hUc
  obtain ⟨B₀, hB₀t, hB₀⟩ := _root_.GlobalTheory.ResLine.modulus_mul_measure_shell_le G N M Λ ν π DN DM H μ D hμ hD (W * U) (hW.mul hUc)
  have hνV : ν {u : N | (u : G) ∈ V} ≠ ⊤ :=
    (H.closedN.isClosedEmbedding_subtypeVal.isCompact_preimage hV).measure_ne_top
  have hDN0 : ν DN ≠ 0 := GlobalTheory.ResLine.Inhab.semiLat_ne_zero H
  have hDNt : ν DN ≠ ⊤ := H.finN
  refine ⟨(ν {u : N | (u : G) ∈ V} * k * B₀ / (ν DN * μ U)).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro a Y T haM haN hY hcov hTΓ hTsep hTQ
  obtain ⟨κ, hκ⟩ := _root_.GlobalTheory.SphEis.lintegral_conj_eq_const_mul G N ν a⁻¹ H.closedN H.haarN (fun u => by rw [inv_inv]; exact haN u)
  let S : Set G := (Q : Set G) * (a • (W * U))
  have hSc : IsClosed S := hQ.mul_right_of_isCompact ((hW.mul hUc).smul a)
  have hSm : MeasurableSet S := hSc.measurableSet
  have hSinv : ∀ γ ∈ Λ, ∀ x ∈ S, γ * x ∈ S := by
    intro γ hγ x hx
    obtain ⟨q, hq, y, hy, rfl⟩ := Set.mem_mul.1 hx
    exact Set.mem_mul.2 ⟨γ * q, Q.mul_mem (hΛQ hγ) hq, y, hy, mul_assoc _ _ _⟩
  have hTS : ∀ t ∈ T, ∀ u ∈ U, t * u ∈ S := by
    intro t ht u hu
    obtain ⟨q, hq, w, hw, rfl⟩ := hTQ t ht
    have hm : a • (w * u) ∈ a • (W * U) := Set.smul_mem_smul_set (Set.mul_mem_mul hw hu)
    refine Set.mem_mul.2 ⟨q, hq, a • (w * u), hm, ?_⟩
    simp only [smul_eq_mul, mul_assoc]
  have hpack := hk T S hTΓ hTsep hSm hSinv hTS
  have hshell : κ * μ (S ∩ D) ≤ B₀ := by
    refine hB₀ a⁻¹ κ (fun m hm => (show Commute a m from haM m hm).inv_left) hκ S hSm fun x hx => ?_
    obtain ⟨q, hq, y, hy, rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨c, hc, rfl⟩ := Set.mem_smul_set.1 hy
    obtain ⟨u, hu, m, hm, rfl⟩ := hQd q hq
    refine ⟨a⁻¹ * u * a, (haN u).1 hu, m, hm, c, hc, ?_⟩
    have e : m * a = a * m := (haM m hm).symm
    simp only [smul_eq_mul, mul_assoc]
    rw [← mul_assoc m a c, e, mul_assoc a m c]
  have hcover := _root_.GlobalTheory.SphEis.measure_fund_le_card_mul_of_cover G N Λ ν DN a⁻¹ κ V Y H.haarN H.domN hV hκ hY fun u hu => by
    obtain ⟨γ, hγ, hγN, y, hy, w, hw, e⟩ := hcov u hu
    exact ⟨γ, hγ, hγN, y, hy, w, hw, by rw [inv_inv]; exact e⟩
  have key : ν DN * (T.card * μ U) ≤ Y.card * (ν {u : N | (u : G) ∈ V} * k * B₀) := calc
    ν DN * (T.card * μ U) ≤ (Y.card * (κ * ν {u : N | (u : G) ∈ V})) * (T.card * μ U) := by gcongr
    _ = Y.card * ν {u : N | (u : G) ∈ V} * (κ * (T.card * μ U)) := by ring
    _ ≤ Y.card * ν {u : N | (u : G) ∈ V} * (κ * (k * μ (S ∩ D))) := by gcongr
    _ = Y.card * ν {u : N | (u : G) ∈ V} * k * (κ * μ (S ∩ D)) := by ring
    _ ≤ Y.card * ν {u : N | (u : G) ∈ V} * k * B₀ := by gcongr
    _ = Y.card * (ν {u : N | (u : G) ∈ V} * k * B₀) := by ring
  have hc0 : ν DN * μ U ≠ 0 := mul_ne_zero hDN0 hU0
  have hct : ν DN * μ U ≠ ⊤ := ENNReal.mul_ne_top hDNt hUt
  have hX : ν {u : N | (u : G) ∈ V} * k * B₀ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hνV (ENNReal.natCast_ne_top k)) hB₀t
  have h1 : (T.card : ℝ≥0∞) ≤ Y.card * (ν {u : N | (u : G) ∈ V} * k * B₀ / (ν DN * μ U)) := by
    rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)]
    calc (T.card : ℝ≥0∞) * (ν DN * μ U) = ν DN * (T.card * μ U) := by ring
      _ ≤ _ := key
  have hfin : ν {u : N | (u : G) ∈ V} * k * B₀ / (ν DN * μ U) ≠ ⊤ := (ENNReal.div_lt_top hX hc0).ne
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hfin) h1
  rw [mul_comm]
  simpa [ENNReal.toReal_mul] using h2

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardPrincipalCongruenceTransversalLeAbsNormPow
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

theorem GlobalTheory.card_congRep_le : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (a : ℕ) (R : Finset (GA D a)), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → R.card ≤ Ideal.absNorm 𝔪 ^ (a ^ 2) := by
  intro D 𝔪 h𝔪 a R hR huniq
  classical
  obtain ⟨hne, hle⟩ := GlobalTheory.congLev_relIndex_le D 𝔪 h𝔪 a
  let Q := intG D a ⧸ (congLev D 𝔪 a).subgroupOf (intG D a)
  haveI : Finite Q := Nat.finite_of_card_ne_zero hne
  let f : R → Q := fun r => QuotientGroup.mk (⟨(r : GA D a), hR r r.2⟩ : intG D a)
  have hf : Function.Injective f := by
    rintro ⟨r, hr⟩ ⟨r', hr'⟩ h
    have h1 := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : r⁻¹ * r' ∈ congLev D 𝔪 a := h1
    have h3 := ((mem_congLev_iff D 𝔪 a _).1 h2).2
    have h4 : CongOne D 𝔪 (r'⁻¹ * r') := by
      rw [inv_mul_cancel]; exact congOne_one 𝔪 a
    obtain ⟨s, -, hs⟩ := huniq r' (hR r' hr')
    have e1 := hs r ⟨hr, h3⟩
    have e2 := hs r' ⟨hr', h4⟩
    exact Subtype.ext (e1.trans e2.symm)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hc
  calc R.card ≤ Nat.card Q := hc
    _ = (congLev D 𝔪 a).relIndex (intG D a) := rfl
    _ ≤ _ := hle

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartFrSgnFalseRigFr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.StageDict

open GlobalTheory.ChainFr Matrix

variable {D : D7}

theorem jm_eq_diag {k p : ℕ} {ε : Fin k → ℝ} (h : ∀ a : Fin k, (ε a = 1 ∧ a.val < p) ∨ (ε a = -1 ∧ p ≤ a.val)) :
    Formalism.REAL.Jm (fun a : Fin k => decide (a.val < p)) = Matrix.diagonal (fun a => (ε a : ℂ)) := by
  unfold Formalism.REAL.Jm
  congr 1
  funext a
  rcases h a with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · have : ¬ a.val < p := by omega
    simp [h1, this]

theorem isUnit_of_isONBasis {k p : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G s B p) : IsUnit B := by
  obtain ⟨ε, hε, h1, -⟩ := h
  have hd : IsUnit (Matrix.diagonal fun a => (ε a : ℂ)).det := by
    rw [Matrix.det_diagonal]
    refine IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
    rcases hε a with ⟨e, -⟩ | ⟨e, -⟩ <;> simp [e]
  rw [← h1, Matrix.det_mul, Matrix.det_mul] at hd
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_mul_isUnit_right hd

def sigIdx {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) : ℕ := Classical.choose (h.2.2 τ).2

theorem sigIdx_spec {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) :
    IsONBasis (gramAt D V τ) (r.s τ) (r.B τ) (sigIdx r h τ) := Classical.choose_spec (h.2.2 τ).2

def rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) : Fr V where
  ε τ a := decide (a.val < sigIdx r h τ)
  fr τ := (r.B τ)⁻¹
  fr_unit τ := by
    have hu := isUnit_of_isONBasis (sigIdx_spec r h τ)
    exact (Matrix.isUnit_nonsing_inv_iff).2 hu
  fr_gram τ := by
    have hu := isUnit_of_isONBasis (sigIdx_spec r h τ)
    obtain ⟨ε, hε, h1, -⟩ := sigIdx_spec r h τ
    rw [jm_eq_diag hε, ← h1, Matrix.conjTranspose_nonsing_inv]
    have hu' : IsUnit (r.B τ)ᴴ.det := by
      rw [Matrix.det_conjTranspose]; exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).star
    have hu0 : IsUnit (r.B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 hu
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu0, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hu', Matrix.one_mul]

theorem onb_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) : (rigFr r h).onb τ = r.B τ := by
  have hu0 : IsUnit (r.B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_isONBasis (sigIdx_spec r h τ))
  simp only [Fr.onb, rigFr]
  exact Matrix.nonsing_inv_nonsing_inv _ hu0

theorem cart_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) : (rigFr r h).cart τ = r.s τ := by
  have hu0 : IsUnit (r.B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_isONBasis (sigIdx_spec r h τ))
  obtain ⟨ε, hε, -, h2⟩ := sigIdx_spec r h τ
  simp only [Fr.cart, rigFr]
  rw [Matrix.nonsing_inv_nonsing_inv _ hu0, jm_eq_diag hε, ← h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu0, Matrix.mul_one]

theorem cart_frSgn_true_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) :
    (GlobalTheory.SquareComm.frSgn true (rigFr r h)).cart τ = -r.s τ := by
  rw [← cart_rigFr r h τ]
  simp only [Fr.cart, GlobalTheory.SquareComm.frSgn]
  have e' : Formalism.REAL.Jm (fun a => xor true ((rigFr r h).ε τ a)) = -Formalism.REAL.Jm ((rigFr r h).ε τ) := by
    ext a b
    by_cases hab : a = b
    · subst hab; cases h' : (rigFr r h).ε τ a <;> simp [Formalism.REAL.Jm, h']
    · simp [Formalism.REAL.Jm, hab]
  rw [e', Matrix.mul_neg, Matrix.neg_mul]

theorem cart_frSgn_false_rigFr {V : HSp D} (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V) (h : r.Is) (τ : D.what₂.Tau) :
    (GlobalTheory.SquareComm.frSgn false (rigFr r h)).cart τ = r.s τ := by
  rw [← cart_rigFr r h τ]
  simp [Fr.cart, GlobalTheory.SquareComm.frSgn]

theorem stage_sizes (i j : Fin D.R.m) {p q a a' : ℕ} (hp : p ≤ pp D j) (hq : q ≤ qq D j)
    (ha : a + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p) (ha' : a' + 2 * qq D j = rankV D i j + 2 * q) :
    Even (a + a') ∧ a' + 2 * (2 * (p + q) + 1) < a ∧ 2 * (p + q) + 1 < a' ∧
      a + a' ≤ rankV D (i + 1) (j + 1) + rankV D i j := by
  obtain ⟨u, hu⟩ := D.R.t_odd
  obtain ⟨v, hv⟩ := D.R.m_even
  obtain ⟨w, hw⟩ := D.R.k_even
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have r1 : rankV D i j = D.R.r + j.1 * D.R.t + i.1 * sLen D := rfl
  have r3 : D.R.r = D.R.k + D.R.m - 1 := rfl
  have r4 : sLen D = D.R.r + 6 := rfl
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.three_m_lt_t
  have h3 := D.R.two_le_m
  have hj := j.2
  simp only [pp, qq] at hp hq ha ha'
  refine ⟨Nat.even_iff.2 (by omega), by omega, by omega, by omega⟩

end GlobalTheory.StageDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColonOneSpanImageEqMapStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colon_one_span_image_eq_map_colon : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K), (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
    ∀ (A : Submodule (𝓞 E) E), A.FG → (1 : E) ∈ A →
    (1 : Submodule (𝓞 K) K).colon (Submodule.span (𝓞 K) (τE '' A) : Set K) =
      ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ := by
  first | exact @GlobalTheory.colon_one_span_image_eq_map | exact GlobalTheory.colon_one_span_image_eq_map | (intros; apply GlobalTheory.colon_one_span_image_eq_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColonPowMulCancelFgFractionalStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colon_pow_mul_cancel_fg_fractional : ∀ {K : Type} [Field K] [NumberField K] (𝔟 : Submodule (𝓞 K) K), 𝔟.FG → 𝔟 ≠ ⊥ →
    ∀ (p : ℕ) (A N : Submodule (𝓞 K) K),
    (𝔟 ^ p * N).colon ((𝔟 ^ p * A : Submodule (𝓞 K) K) : Set K) = N.colon (A : Set K) := by
  first | exact @GlobalTheory.ColonPowCancel.colon_pow_mul_cancel | exact GlobalTheory.ColonPowCancel.colon_pow_mul_cancel | (intros; apply GlobalTheory.ColonPowCancel.colon_pow_mul_cancel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnsMemberRowsOfLogLevelLe
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRowsTopS

theorem rowsBody_colFace : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (N : NumDatum) (X : Fields) [_root_.NumberField.IsTotallyComplex X.K] (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (hX : X.Ok) (Bs : DefBase X.K) (Df : DefSide Bs) (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs N.R.r → X.K)) (mu : Bs.Tup → Tup X.F X.E X.K Sg) (cst : ∀ t, LocCst X (rowSG Pr sel (mu t))) (I : ∀ t, ChIdx X Pr N.R (QE sel (mu t : Chr X.F X.E X.K))) (hL : ∀ t, (I t).Ok Ch sel (mu t) (cst t) G (N.R.m - 2)) (hP : ∀ t, (mtildeGSD W Ch sel (mu t) (rPsymF Ch)).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (I t).β (N.R.m - 2 + 1)) (hY : ∀ t x, YbHyp (R := N.R) sel (mu t) (cst t) (I t) (wd x) (N.R.m - 2) (b t x)) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (hK : ∀ t x, KerEquivC W Ch sel (mu t) (cst t) (I t) (ambOf s B χ cD) (wd x) (N.R.m - 2) (b t x) (hY t x) (rPsymF Ch)) (hF : ∀ t x j, (chF W sel (mu t) (I t) (wd x) j).Ok) (hE : ∀ x, (evGSD W Ch sel (mu Bs.μ0) (rPsymF Ch) (wd x)).Ok) (ev : ∀ t, (Fin (Df.nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg (rPsymF Ch)) (pl : RPl N.R ≃ X.Tau) (x : Mem) (δ : Code N) (eJ : Bs.J ≃ Fin N.R.m) (R : RecNums Bs.J (RPl N.R)), HostTie N s Pr → WeightTie N W pl (wd x) δ → CharTie N s W Ch G sel → AnalyticTie D dl χ cD → mu Bs.μ0 = 1 → (cst Bs.μ0).sharp = true → FieldOfDefinition W sel (mu Bs.μ0) (cst Bs.μ0) (wd x) (ambOf s B χ cD) → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Real.log (Pr.T (wd x) : ℝ) ≤ CT * N.R.m * N.sc.L → Reads N eJ δ (Pr.T (wd x)) R → C0 ≤ R.Ch → (∀ v : InfinitePlace X.K, ((Df.HV Bs.μ0).map v.embedding).PosDef) → (∀ X0, IsFrames Df X0 → ∀ v F, ((mtildeGSD W Ch sel (mu Bs.μ0) (rPsymF Ch)).ipAt (hP Bs.μ0) v ((ev Bs.μ0 F).1).1 ((ev Bs.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody (colFace hX Df Xg mu cst I hL hP Mem wd b hY (kerRec mu cst I wd b hY (ambOf s B χ cD) hK) hF ev) x (memQ (A := kerRec mu cst I wd b hY (ambOf s B χ cD) hK) (hF := hF) hE (x := x)) (colsIn W Ch hX sel (mu Bs.μ0) (cst Bs.μ0) (I Bs.μ0) (hL Bs.μ0) (wd x)) R ∧ ∀ v, IsUnit ((MramH W Ch hX (wd x)).X v).det := by
  intro CY CT hCT
  obtain ⟨C, hC, hker⟩ := GlobalTheory.T.kernelHalf_chainNumbers_any_levelPrime CY
  refine ⟨max (2 * (16 + CT)) (max (6 * C + 1 + 2 * C * C) (4 * C * (CT + C))), ?_⟩
  intro D N X _ s Pr W Ch G sel Sg hX Bs Df Xg mu cst I hL hP Mem wd b hY dl B χ cD hK hF hE ev pl x δ eJ R
    hHost hWt hChar hAn hmu hsharp hFD hS hR hlogT hRd hC0 hpos hev
  have hPr : Pr.Ok := hHost.2.2.2.2.2.2.2.2.2.1
  have hT : 1 ≤ Pr.T (wd x) := (hPr.T_prime _).one_le
  have hk := hker D N X s Pr W Ch G sel Sg (mu Bs.μ0) (cst Bs.μ0) (I Bs.μ0) dl B χ cD pl (wd x) δ (b Bs.μ0 x) (hY Bs.μ0 x)
    (hK Bs.μ0 x) (hF Bs.μ0 x) (hE x) Bs.J eJ R hHost hWt hChar hAn hmu hsharp (hL Bs.μ0) hFD hS hR hRd
  have hl := _root_.GlobalTheory.ColRows.LastSideProof.lastSide_of_logT_le CY CT N X Pr W pl (wd x) δ Bs.J eJ R hWt hS hR hlogT hT hRd
  obtain ⟨hn, hA, hsz⟩ := GlobalTheory.ColRows.exists_htNums_of_kerSide_lastSide Bs.J (RPl N.R) (InfinitePlace X.K) R C CT _ _ hC hCT
    ((le_max_left _ _).trans hC0) (((le_max_left _ _).trans (le_max_right _ _)).trans hC0)
    (((le_max_right _ _).trans (le_max_right _ _)).trans hC0) hk hl
  obtain ⟨X0, hX0⟩ := GlobalTheory.ColRows.exists_isFrames X.K Bs Df hpos
  obtain ⟨hdet, hiso⟩ := GlobalTheory.ColFirstIso.colsIn_isometry X hX Pr N.R W Ch sel Sg (mu Bs.μ0) (cst Bs.μ0) (I Bs.μ0) G _ (hL Bs.μ0)
    (wd x) (hF Bs.μ0 x 0) hmu
  have hint : ∀ τ, Br.Interlace (N_m_succ N.R) (W.lamTrue (wd x) N.R.m τ) (W.sgTrue τ) :=
    fun τ => GlobalTheory.BranchMembers.interlace W hWt.1 (wd x) τ
  have hsh : ∀ τ, Br.SameShift (W.lamTrue (wd x) N.R.m τ) (W.sgTrue τ) :=
    fun τ => GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.members_sameShift W hWt.1 (wd x) τ
  have hdat := GlobalTheory.ColRows.evGSD_datFramed X hX Pr N.R W Ch sel Sg (mu Bs.μ0) (rPsymF Ch) (wd x) (hE x)
  refine ⟨_root_.GlobalTheory.DefRowsChain.rowsBody_of_framed X.K Bs Df (colFace hX Df Xg mu cst I hL hP Mem wd b hY (kerRec mu cst I wd b hY (ambOf s B χ cD) hK) hF ev) x
    (memQ (A := kerRec mu cst I wd b hY (ambOf s B χ cD) hK) (hF := hF) hE (x := x)) _
    (colPerL (hP Bs.μ0) Xg (wd x) (ev Bs.μ0)) (RPl N.R) R hn (fun l => (eJ l).1) X0 hdet hiso
    (fun i => GlobalTheory.FamilyFrames.famFramed_chF X hX Pr N.R W Ch sel Sg (mu Bs.μ0) (I Bs.μ0) (wd x) i (hF Bs.μ0 x i)) hdat
    (fun φ F => colPer_eq hX (hP Bs.μ0) Xg _ (hF Bs.μ0 x) (hE x) (hL Bs.μ0) (ev Bs.μ0) φ F) hX0 hsz ?_, hdet⟩
  intro v ψ F
  have hb := GlobalTheory.ColRowsTop.period_le GlobalTheory.BranchNorm.lastMapNorm hX hPr W Ch sel (mu Bs.μ0) hmu (rPsymF Ch) (wd x) hint hsh
    (hP Bs.μ0) (hE x) v ψ.1 (ev Bs.μ0 F).1.1
  rw [hA]
  exact hb.trans (mul_le_mul_of_nonneg_left (hev X0 hX0 v F)
    (mul_nonneg (Real.exp_pos _).le (GlobalTheory.ColRowsTop.ipAt_nonneg_of_datFramed hdat v ψ)))

end GlobalTheory.ColRowsTopS
end

