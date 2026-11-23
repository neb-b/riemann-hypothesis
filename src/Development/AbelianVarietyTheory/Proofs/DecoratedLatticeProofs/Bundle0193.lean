module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SummableOfCount
section
noncomputable section

open scoped NNReal TensorProduct
open NumberField Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Eis.Conv GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GodementSectionReduction


open GlobalTheory.SummCount in
theorem summable_of_count (ι : Type) (n N : ℕ) (b C t : ℝ) (k : ι → Fin n → ℕ)
    (h : ι → ℝ) (hb : 1 < b) (ht : (N : ℝ) < t)
    (hh : ∀ q, 0 ≤ h q ∧ h q ≤ C * ∏ i, (b ^ k q i)⁻¹)
    (hT : ∀ (m : Fin n → ℕ) (T : Finset ι), (∀ q ∈ T, k q = m) →
      (T.card : ℝ) ≤ C * ∏ i, b ^ (N * m i)) :
    Summable fun q => h q ^ t := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg N) ht.le
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨q0⟩⟩
  · exact .of_finite
  have hP : ∀ m : Fin n → ℕ, 0 < ∏ i, (b ^ m i)⁻¹ := fun m => by positivity
  have hC : 0 ≤ C := (mul_nonneg_iff_of_pos_right (hP (k q0))).1 ((hh q0).1.trans (hh q0).2)
  set r := b ^ ((N : ℝ) - t) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hb0.le _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  set g : (Fin n → ℕ) → ℝ := fun m => C * C ^ t * ∏ i, r ^ m i with hg_def
  have hg0 : ∀ m, 0 ≤ g m := fun m => by
    simp only [hg_def]; positivity
  have hg : Summable g :=
    (summable_prod_fin_tuple (summable_geometric_of_lt_one hr0 hr1) (fun _ => pow_nonneg hr0 _)
      n).mul_left _
  have key : ∀ q, h q ^ t ≤ C ^ t * ∏ i, ((b ^ k q i)⁻¹) ^ t := fun q => by
    rw [Real.finsetProd_rpow _ _ (fun i _ => by positivity), ← Real.mul_rpow hC (hP _).le]
    exact Real.rpow_le_rpow (hh q).1 (hh q).2 ht0
  refine summable_of_sum_le (c := ∑' m, g m) (fun q => Real.rpow_nonneg (hh q).1 _) fun T => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (g := k) (t := T.image k)
    (fun q hq => Finset.mem_image_of_mem k hq)]
  refine le_trans (Finset.sum_le_sum fun m _ => ?_) (hg.sum_le_tsum _ (fun m _ => hg0 m))
  calc ∑ q ∈ T with k q = m, h q ^ t
      ≤ ∑ q ∈ T with k q = m, C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t :=
        Finset.sum_le_sum fun q hq => by
          have := key q
          rwa [(Finset.mem_filter.1 hq).2] at this
    _ = ((T.filter (k · = m)).card : ℝ) * (C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C * ∏ i, b ^ (N * m i)) * (C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t) :=
        mul_le_mul_of_nonneg_right (hT m _ fun q hq => (Finset.mem_filter.1 hq).2)
          (mul_nonneg (Real.rpow_nonneg hC _)
            (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by positivity) _))
    _ = g m := by
        simp only [hg_def, hr, ← pow_mul_inv_rpow_eq hb0 N, Finset.prod_mul_distrib]
        ring


open GlobalTheory.Eis.Conv.CovSkew in
theorem cover_adele (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) : ∃ (Ω : Set (AF F ⊗[F] E)) (C : ℝ), IsCompact Ω ∧ ∀ m : ℕ, ∃ Y : Finset (AF F ⊗[F] E),
      (Y.card : ℝ) ≤ C * ((4 : ℝ) ^ Fintype.card (InfinitePlace F)) ^ m ∧ ∀ z : AF F ⊗[F] E, ∃ x : E, ∃ y ∈ Y, ∃ ω ∈ Ω,
        z = inclR (F := F) (AF F) x + y + (halfE F E).1 ^ m * ω := by
  classical
  haveI := hσ.1
  obtain ⟨Ω₀, C₀, hΩ₀, hcov⟩ := _root_.GlobalTheory.Eis.ConvCover.exists_cover F
  obtain ⟨δ, -, hsp⟩ := exists_delta F E σ hσ
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := isTopologicalRing_tens
  have hcont : Continuous fun p : AF F × AF F => psi (F := F) δ p.1 p.2 := by
    unfold psi
    fun_prop
  refine ⟨_, C₀ ^ 2, (hΩ₀.prod hΩ₀).image hcont, fun m => ?_⟩
  obtain ⟨Y, hY, hYc⟩ := hcov m
  refine ⟨(Y ×ˢ Y).image fun y => psi δ y.1 y.2, ?_, fun z => ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Finset.card_product, Nat.cast_mul]
    refine (mul_self_le_mul_self (Nat.cast_nonneg _) hY).trans (le_of_eq ?_)
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, mul_pow]
    ring
  · obtain ⟨u, v, rfl⟩ := exists_coords δ hsp z
    set c : AF F := algebraMap F (AF F) 2⁻¹ with hc
    have h2 : 2 * c = 1 := by
      rw [hc, ← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
    obtain ⟨x, y, hy, ω, hω, e⟩ := hYc (c * (u + v))
    obtain ⟨x', y', hy', ω', hω', e'⟩ := hYc (c * (v - u))
    refine ⟨(x - x') • (1 : E) + (x + x') • δ, _, Finset.mem_image.mpr ⟨(y, y'), Finset.mem_product.2 ⟨hy, hy'⟩, rfl⟩,
      _, ⟨(ω, ω'), ⟨hω, hω'⟩, rfl⟩, ?_⟩
    have : (halfE F E).1 = algebraMap (AF F) (AF F ⊗[F] E) (halfInf F).1 := rfl
    rw [this, ← map_pow, ← psi_split, ← e, ← e', psi_eq]
    congr 2
    · linear_combination (-u) * h2
    · linear_combination (-v) * h2

variable {D : D7} {T T₀ : HSp D} {r : ℕ}

end GlobalTheory.GodementSectionReduction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOExtXExtY
section
namespace I195MixedCoordinates_0e01515b61ee225766e35969

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_0e01515b61ee225766e35969

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HalfNonvan

open GlobalTheory.HalfAverage

variable {D : D7}

theorem symplO_extX_extY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x a : Mx D T.rank ρ) :
    symplO S T (d.extX T x) (d.extY T a) = halfSympl T a x := by
  have h := d.hO_ext T x 0 0 a 0 0
  simp only [map_zero, add_zero, zero_add] at h
  have h0 : hO S₀ T (0 : WO S₀ T) 0 = 0 := by simp [hO]
  have hp : pairS T (0 : Mx D T.rank ρ) 0 = 0 := by simp [pairS, adj]
  rw [h0, hp, add_zero, add_zero] at h
  unfold symplO halfSympl
  rw [h]
  congr 2
  simp only [pairS, halfPair, Matrix.trace, Matrix.diag, Matrix.mul_apply, adj, gA, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, mul_assoc, rat]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_comm

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem exists_mixS_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ T : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)}
    (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {f₀ : WO S₀ T → ℂ} (hf₀ : IsThetaFunO ψ S₀ T f₀) :
    ∃ f, IsThetaFunO ψ S T f ∧ (_root_.I195MixedCoordinates_0e01515b61ee225766e35969.source d) T ψ μ 𝓕 f 0 = f₀ := by
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · obtain ⟨-, hb, hth, -⟩ := GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D ψ S S₀ T d hψ
    have hc : (fun w => (f₀ ∘ (Equiv.ofBijective _ hb).symm) (d.ext0 T w)) = f₀ := by
      funext w
      exact congrArg f₀ ((Equiv.ofBijective _ hb).symm_apply_apply w)
    refine ⟨f₀ ∘ (Equiv.ofBijective _ hb).symm, (hth _).1 (by rw [hc]; exact hf₀), ?_⟩
    change I195MixedCoordinates_7149a82cc25e6f9e668c8c61.source d T ψ μ 𝓕 _ 0 = f₀
    rw [(GlobalTheory.Unf.mixRankZero D ψ).1 S S₀ T d μ 𝓕 hμ, hc]
  · obtain ⟨h1, h2, -, -, -, h6, -⟩ := GlobalTheory.Bridge.heis_bridge D ψ S S₀ T ρ d
    obtain ⟨f, hf, hff⟩ := GlobalTheory.TowerSurj.res_surjective D S S₀ T ρ d.e d.i₀ (h1 hρ) ψ hψ μ 𝓕 (h2 ▸ hμ) f₀ hf₀
    refine ⟨f, hf, ?_⟩
    change I195MixedCoordinates_16b53debd46a2c18720dfcab.source d T ψ μ 𝓕 f 0 = f₀
    rw [h6, map_zero, heisO_zero', hff]


set_option maxHeartbeats 1000000 in
theorem avg_mixS_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, (∃ f, IsThetaFunO ψ S₀ T f ∧ ℓ₀ f ≠ 0) → ∀ H : AddSubgroup (Mx D T.rank ρ), (∀ x, x ∈ H ↔ ∀ i j, cA D e * x i j = x i j) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsAddHaarMeasure], ∃ f, IsThetaFunO ψ S T f ∧ ∫ x : H, ℓ₀ ((_root_.I195MixedCoordinates_0e01515b61ee225766e35969.source d) T ψ μ 𝓕 f x.1) ∂ν ≠ 0 := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ ⟨f₀, hf₀, hℓ⟩ H hH mH bH ν hν
  obtain rfl : H = halfMx (cA D e) T.rank ρ := AddSubgroup.ext fun x => hH x
  obtain ⟨f, hf, hmix⟩ := exists_mixS_zero hψ d hμ hf₀
  by_contra hall
  push_neg at hall
  obtain ⟨-, hY, -⟩ := GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S S₀ T ρ d ⟨μ, 𝓕, hμ⟩ f hf
  obtain ⟨⟨U, hU, hUinv⟩, K, hK, hKs⟩ := GlobalTheory.MixHalf.mixS_half D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he f hf
  obtain ⟨L, hL, hLU, hsep⟩ := GlobalTheory.HalfSeparate.exists_open_separated D ψ hψ T ρ e he
    (U.comap (halfMx (cA D e) T.rank ρ).subtype) (hU.preimage continuous_subtype_val)
  have hφ := @GlobalTheory.fourier_uniqueness_of_openSubgroup (halfMx (cA D e) T.rank ρ) (halfMx e T.rank ρ) _ _ _ mH bH ν hν _
    (fun a t => ψ (halfSympl T (a : Mx D T.rank ρ) (t : Mx D T.rank ρ)))
    (fun a s t => by simp only [AddSubgroup.coe_add, halfSympl_add_right, AddChar.map_add_eq_mul])
    (fun a => by simp only [ZeroMemClass.coe_zero, halfSympl_zero_right, AddChar.map_zero_eq_one])
    (fun t => by simp only [ZeroMemClass.coe_zero, halfSympl_zero_left, AddChar.map_zero_eq_one])
    (fun a b t => by simp only [AddSubgroup.coe_add, halfSympl_add_left, AddChar.map_add_eq_mul])
    L hL hsep (fun t => ℓ₀ ((_root_.I195MixedCoordinates_0e01515b61ee225766e35969.source d) T ψ μ 𝓕 f t.1))
    (Subtype.val ⁻¹' K) ((isClosed_halfMx _ _ _).isClosedEmbedding_subtypeVal.isCompact_preimage hK)
    (fun t ht => by
      have : (_root_.I195MixedCoordinates_0e01515b61ee225766e35969.source d) T ψ μ 𝓕 f t.1 = 0 := by
        by_contra h
        exact ht (hKs t.1 t.2 h)
      simp only [this, map_zero])
    (fun t l hl => by
      simp only [AddSubgroup.coe_add]
      change ℓ₀ (I195MixedCoordinates_41a545e47d405c9816345b57.source d T ψ μ 𝓕 f (t.1 + l.1)) =
        ℓ₀ (I195MixedCoordinates_41a545e47d405c9816345b57.source d T ψ μ 𝓕 f t.1)
      rw [hUinv l.1 (hLU hl) l.2])
    (fun a _ => by
      rw [← hall _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf (d.extY T a.1))]
      refine congrArg (fun g => @integral _ ℂ _ _ mH ν g) (funext fun t => ?_)
      have := hY t.1 a.1
      simp only at this
      change ψ (halfSympl T a.1 t.1) * ℓ₀ (I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d T ψ μ 𝓕 f t.1) =
        ℓ₀ (I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d T ψ μ 𝓕 (heisO ψ S T (d.extY T a.1) f) t.1)
      rw [this, map_smul, smul_eq_mul, symplO_extX_extY])
  apply hℓ
  have := congrFun hφ 0
  simpa [hmix] using this

end GlobalTheory.HalfNonvan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplecticFormInertSupportedPointsAntidiagonal
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameSympl

open Formalism.UG (cT cT_mul cT_one antiJ)
open GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : IsInertAt D.host.F D.host.E v w} {h : w.under (𝓞 D.host.F) = v}

def evW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) : AE D →+* w.adicCompletion D.host.E :=
  (GlobalTheory.LFun.InertChart.complEquiv hw h).toRingHom.comp (compFin D.host.F D.host.E v)

theorem secW_apply (z : w.adicCompletion D.host.E) :
    secW hw h z = GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z) := rfl

theorem secW_mul_right (z : w.adicCompletion D.host.E) (A : AE D) :
    secW hw h z * A = secW hw h (z * evW hw h A) := by
  rw [secW_apply, secW_apply, GlobalTheory.EmbChart.tensAt_mul_right]
  congr 1
  rw [map_mul (GlobalTheory.LFun.InertChart.complEquiv hw h).symm]
  show _ = _ * (GlobalTheory.LFun.InertChart.complEquiv hw h).symm ((GlobalTheory.LFun.InertChart.complEquiv hw h) _)
  rw [RingEquiv.symm_apply_apply]

theorem evW_secW (z : w.adicCompletion D.host.E) : evW hw h (secW hw h z) = z := by
  show GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v (GlobalTheory.EmbChart.tensAt D.host.E v
    ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z))) = z
  rw [GlobalTheory.EmbChart.compFin_tensAt, RingEquiv.apply_symm_apply]

theorem evW_incA (a : D.host.E) : evW hw h (incA D a) = algebraMap D.host.E _ a := by
  show GlobalTheory.LFun.toCompl h (compFin D.host.F D.host.E v ((1 : AF D.host.F) ⊗ₜ[D.host.F] a)) = _
  show GlobalTheory.LFun.toCompl h ((evFin D.host.F v 1) ⊗ₜ[D.host.F] a) = _
  rw [map_one, GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]

theorem incA_mul_secW (a : D.host.E) (z : w.adicCompletion D.host.E) :
    incA D a * secW hw h z = secW hw h (algebraMap D.host.E _ a * z) := by
  rw [mul_comm, secW_mul_right, evW_incA, mul_comm]

theorem cA_secW {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E} (hc : GlobalTheory.LFun.IsConjAt D.sp.cm.sig h c)
    (z : w.adicCompletion D.host.E) : cA D (secW hw h z) = secW hw h (c z) := by
  rw [secW_apply, secW_apply]
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig (GlobalTheory.EmbChart.tensAt D.host.E v _) = GlobalTheory.EmbChart.tensAt D.host.E v _
  rw [GlobalTheory.EmbChart.sigR_tensAt]
  congr 1
  apply (GlobalTheory.LFun.InertChart.complEquiv hw h).injective
  rw [RingEquiv.apply_symm_apply]
  have := hc ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z)
  exact this.symm.trans (congrArg c ((GlobalTheory.LFun.InertChart.complEquiv hw h).apply_symm_apply z))

theorem hO_map_secW {S T : HSp D} {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E}
    (hc : GlobalTheory.LFun.IsConjAt D.sp.cm.sig h c) (M N : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    hO S T (M.map (secW hw h)) (N.map (secW hw h)) = secW hw h (Matrix.trace
      ((S.gram⁻¹.map (algebraMap D.host.E (w.adicCompletion D.host.E)) : Matrix (Fin S.rank) (Fin S.rank) _) *
      cT c N * (T.gram.map (algebraMap D.host.E (w.adicCompletion D.host.E)) : Matrix (Fin T.rank) (Fin T.rank) _) * M)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hO, Matrix.map_apply, cA_secW hc, incA_mul_secW, secW_mul_right, evW_incA, evW_secW, ← map_sum]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Matrix.map_apply, cT, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm) ?_
  rw [Finset.sum_comm]

variable {L : Type} [Field L]

theorem cT_smul' (c : L →+* L) {m n : ℕ} (k : L) (A : Matrix (Fin m) (Fin n) L) : cT c (k • A) = c k • cT c A := by
  ext i j
  simp [cT, Matrix.smul_apply]

theorem inv_eq_of_frame (c : L →+* L) {n : ℕ} {G G' : Matrix (Fin n) (Fin n) L} (hG : G' * G = 1) (a : GL (Fin n) L)
    (ha : cT c a.1 * G * a.1 = antiJ L n) : G' = a.1 * antiJ L n * cT c a.1 := by
  have h1 : G * a.1 = cT c (a⁻¹).1 * antiJ L n := by
    rw [← ha, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, Units.mul_inv, cT_one, Matrix.one_mul]
  have h2 : G * (a.1 * antiJ L n * cT c a.1) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc (cT c (a⁻¹).1),
      Formalism.UG.P.fIwasawa_antiJ_mul_antiJ, Matrix.mul_one, ← cT_mul, Units.mul_inv, cT_one]
  rw [← Matrix.mul_one G', ← h2, ← Matrix.mul_assoc, hG, Matrix.one_mul]

theorem trace_frame (c : L →+* L) {n n' : ℕ} (k : L) (aS : GL (Fin n) L) (aT : GL (Fin n') L)
    (GT J' : Matrix (Fin n') (Fin n') L) (J : Matrix (Fin n) (Fin n) L) (hT : cT c aT.1 * GT * aT.1 = J')
    (x y : Matrix (Fin n') (Fin n) L) :
    Matrix.trace (aS.1 * J * cT c aS.1 * cT c (k • (aT.1 * y * (aS⁻¹).1)) * GT * (k • (aT.1 * x * (aS⁻¹).1))) =
      k * c k * Matrix.trace (J * cT c y * J' * x) := by
  rw [cT_smul', cT_mul, cT_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cT c aS.1) (cT c (aS⁻¹).1), ← cT_mul, Units.inv_mul, cT_one, Matrix.one_mul,
    ← Matrix.mul_assoc GT aT.1, ← Matrix.mul_assoc (cT c aT.1) (GT * aT.1), ← Matrix.mul_assoc (cT c aT.1) GT, hT, Matrix.trace_mul_comm aS.1]
  simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  ring

theorem hO_uPt {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : IsInertAt D.host.F D.host.E v w} {h : w.under (𝓞 D.host.F) = v} {S T : HSp D}
    {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E} (k : w.adicCompletion D.host.E)
    {aS : GL (Fin S.rank) (w.adicCompletion D.host.E)} {aT : GL (Fin T.rank) (w.adicCompletion D.host.E)}
    (hc : GlobalTheory.LFun.IsConjAt D.sp.cm.sig h c)
    (hS : cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = antiJ _ S.rank)
    (hT : cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = antiJ _ T.rank)
    (x y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    hO S T (uPt hw h k aS aT x) (uPt hw h k aS aT y) =
      secW hw h (k * c k * Matrix.trace (antiJ (w.adicCompletion D.host.E) S.rank * cT c y * antiJ (w.adicCompletion D.host.E) T.rank * x)) := by
  have hG : (S.gram⁻¹.map (algebraMap D.host.E (w.adicCompletion D.host.E)) : Matrix (Fin S.rank) (Fin S.rank) _) *
      S.gram.map (algebraMap D.host.E (w.adicCompletion D.host.E)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S),
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [uPt, uPt, hO_map_secW hc, inv_eq_of_frame c hG aS hS, trace_frame c k aS aT _ _ _ hT]

theorem symplOH_uPt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), IsConjAt D.sp.cm.sig h c → Formalism.UG.cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = Formalism.UG.antiJ _ S.rank → Formalism.UG.cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = Formalism.UG.antiJ _ T.rank → ∀ x y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), ψ (symplOH S T (uPt hw h k aS aT x) (uPt hw h k aS aT y)) = thW ψ hw h (k * c k) (2⁻¹ * GlobalTheory.Hk3.locH c 1 (GlobalTheory.SphTheta.antiG _ S.rank) (GlobalTheory.SphTheta.antiG _ T.rank) x y) := by
  intro D ψ v w hw h S T c k aS aT hc hS hT x y
  have h2 : (2 : w.adicCompletion D.host.E) ≠ 0 := by
    have : CharZero (w.adicCompletion D.host.E) := algebraRat.charZero _
    exact two_ne_zero
  have hx : (2⁻¹ : w.adicCompletion D.host.E) • x + (2⁻¹ : w.adicCompletion D.host.E) • x = x := by
    rw [← add_smul, ← two_mul, mul_inv_cancel₀ h2, one_smul]
  have hl : GlobalTheory.Hk3.locH c 1 (GlobalTheory.SphTheta.antiG _ S.rank) (GlobalTheory.SphTheta.antiG _ T.rank) x y =
      Matrix.trace (antiJ (w.adicCompletion D.host.E) S.rank * cT c y * antiJ (w.adicCompletion D.host.E) T.rank * x) := by
    rw [GlobalTheory.Hk3.locH, one_mul]
    rfl
  conv_lhs => rw [← hx, uPt_add, GlobalTheory.SplitScalar.symplOH_add_left, GlobalTheory.SplitScalar.symplOH_add_self]
  rw [thW_apply, symplO, hO_uPt k hc hS hT, hl, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_assoc]

end GlobalTheory.InertFrameSympl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TameLiftResidueCharacterIsTameNotUnramified
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.TameLiftChar

open ValuativeRel

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem val_le_iff (x y : Fv D.host.F v) :
    valuation (Fv D.host.F v) x ≤ valuation (Fv D.host.F v) y ↔ Valued.v x ≤ Valued.v y := by
  haveI : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [← Valuation.Compatible.vle_iff_le (v := valuation (Fv D.host.F v)),
    Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))))]

theorem val_lt_one_iff (x : Fv D.host.F v) :
    valuation (Fv D.host.F v) x < 1 ↔ Valued.v x < 1 := by
  have h := val_le_iff (D := D) (v := v) 1 x
  rw [map_one, map_one] at h
  rw [← not_le, ← not_le, h]

theorem val_eq_one_iff (x : Fv D.host.F v) :
    valuation (Fv D.host.F v) x = 1 ↔ Valued.v x = 1 := by
  have h1 := val_le_iff (D := D) (v := v) 1 x
  have h2 := val_le_iff (D := D) (v := v) x 1
  rw [map_one, map_one] at h1 h2
  rw [le_antisymm_iff, le_antisymm_iff, h1, h2]

theorem rdQ_one (φ : SplitProj D v) : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (1 : D.host.E) = 1 := by
  show φ (1 ⊗ₜ 1) = 1
  rw [← Algebra.TensorProduct.one_def, map_one]

def rdQHom (φ : SplitProj D v) : D.host.E →+* Fv D.host.F v :=
  φ.toRingHom.comp (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] _).toRingHom

theorem rdQHom_apply (φ : SplitProj D v) (x : D.host.E) : rdQHom φ x = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ x := rfl

theorem val_rdQ_le_one (φ : SplitProj D v) (x : 𝓞 D.host.E) : Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E)) ≤ 1 := by
  let w : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ)) := Valued.v
  have hx : IsIntegral ℤ (x : D.host.E) := x.2
  obtain ⟨p, hm, hp⟩ := hx
  have hO : IsIntegral w.integer (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E)) := by
    refine ⟨p.map (Int.castRingHom w.integer), hm.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← rdQHom_apply]
    have : (algebraMap w.integer (Fv D.host.F v)).comp (Int.castRingHom _) =
        (rdQHom φ).comp (algebraMap ℤ D.host.E) := RingHom.ext_int _ _
    rw [this, ← Polynomial.hom_eval₂, hp, map_zero]
  exact (Valuation.integer.integers w).mem_of_integral hO

end GlobalTheory.TameLiftChar

open GlobalTheory.TameLiftChar in
theorem GlobalTheory.tameLift_isTame_not_isUnram : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E) (ξ : (kP PP)ˣ →* ℂˣ), IsProjAt φ PP → ξ ≠ 1 → ∀ ξl : (Fv D.host.F v)ˣ →* ℂˣ, LiftsChar φ PP ξl ξ → GlobalTheory.SplitWeil.IsTame ξl ∧ ¬ GlobalTheory.SplitWeil.IsUnram ξl := by
  intro D v φ PP ξ hP hξ ξl hl
  refine ⟨?_, ?_⟩
  · intro x hx
    have hr : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (x : Fv D.host.F v) ((1 : (kP PP)ˣ) : kP PP) := by
      refine ⟨1, by simp, ?_⟩
      simpa [rdQ_one] using (val_lt_one_iff _).1 hx
    rw [hl x 1 hr, map_one]
  · intro hun
    obtain ⟨k, hk⟩ : ∃ k, ξ k ≠ 1 := by
      by_contra h; push_neg at h; exact hξ (MonoidHom.ext h)
    obtain ⟨x0, hx0⟩ := Ideal.Quotient.mk_surjective (k : kP PP)
    have hnot : x0 ∉ PP.asIdeal := by
      intro hm
      have : ((k : kP PP)) = 0 := by rw [← hx0]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
      exact k.ne_zero this
    have hle := val_rdQ_le_one φ x0
    have hge : ¬ Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E)) < 1 := fun h => hnot ((hP x0).2 h)
    have h1 : Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E)) = 1 := le_antisymm hle (not_lt.1 hge)
    have hne : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h1; exact zero_ne_one h1
    let u : (Fv D.host.F v)ˣ := Units.mk0 _ hne
    have hr : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (u : Fv D.host.F v) (k : kP PP) := ⟨x0, hx0, by simp [u]⟩
    exact hk ((hl u k hr).symm.trans (hun u ((val_eq_one_iff _).2 h1)))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistParahoricChainLastStepsAgreeColumnsStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistParahoricChain_lastSteps_agree_columns : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → LastAgree Ch sel mu cst σ₀ P ι s W ν L := by
  first | exact @GlobalTheory.TwLast.lastAgree | exact GlobalTheory.TwLast.lastAgree | (intros; apply GlobalTheory.TwLast.lastAgree <;> assumption)
end

