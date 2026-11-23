module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0231
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.THProvA

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralThetaLiftTermSumNeTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal

noncomputable section

namespace GlobalTheory.ThetaLiftBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_rat_height_le {D : D7} (W : HSp D) (h : GA D W) :
    ∃ γ ∈ GQ W, GlobalTheory.Grow.height W (γ * h) ≤ 2 * GlobalTheory.Grow.quotHeight W h := by
  have hq := GlobalTheory.Grow.one_le_quotHeight W h
  by_contra hne
  push_neg at hne
  have : 2 * GlobalTheory.Grow.quotHeight W h ≤ GlobalTheory.Grow.quotHeight W h :=
    (GlobalTheory.Grow.le_quotHeight_iff W).2 fun γ hγ => (hne γ hγ).le
  linarith

theorem bound_pow (c a b M q : ℝ) (A : ℕ) (ha : 1 ≤ a) (haM : a ≤ M) (hb : 1 ≤ b) (hbq : b ≤ 2 * q) :
    c * (a * b) ^ A ≤ max c 0 * (M * (2 * q)) ^ A := by
  have hX : a * b ≤ M * (2 * q) := mul_le_mul haM hbq (by linarith) (by linarith)
  have hXp : (a * b) ^ A ≤ (M * (2 * q)) ^ A := pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) hX A
  exact (mul_le_mul_of_nonneg_right (le_max_left c 0) (pow_nonneg (mul_nonneg (by linarith) (by linarith)) A)).trans
    (mul_le_mul_of_nonneg_left hXp (le_max_right c 0))

theorem bound_mul (c M q f C' : ℝ) (A : ℕ) (hM : 0 ≤ M) (hq : 0 ≤ q) (hf : 0 ≤ f) (hF : f * q ^ A ≤ C') :
    max c 0 * (M * (2 * q)) ^ A * f ≤ max c 0 * (2 * M) ^ A * max C' 0 := by
  have e : max c 0 * (M * (2 * q)) ^ A * f = max c 0 * (2 * M) ^ A * (f * q ^ A) := by
    rw [mul_pow, mul_pow, mul_pow]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (hF.trans (le_max_left _ _))
    (mul_nonneg (le_max_right c 0) (pow_nonneg (by linarith) A))

theorem lintegral_ne_top : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → ∀ F : GA D W → ℂ, GlobalTheory.Grow.RapidDec W F → ∀ (Sg : GA D V × GA D W → ℝ≥0∞), (∀ n ∈ NI V C, n ∈ GQ V → ∀ a b, Sg (n * a, b) = Sg (a, b)) → (∀ γ ∈ GQ W, ∀ a b, Sg (a, γ * b) = Sg (a, b)) → ∀ (A : ℕ) (c : ℝ), (∀ a b, Sg (a, b) ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V a * GlobalTheory.Grow.height W b) ^ A)) → ∀ g : GA D V, ∫⁻ n in 𝓝, ∫⁻ h in 𝓕, Sg ((n : GA D V) * g, h) * ‖F h‖ₑ ∂ν ∂κ ≠ ⊤ := by
  intro D V W r C hC κ 𝓝 hκ h𝓝 ν 𝓕 hν h𝓕 F hF Sg h1 h2 A c hc g
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V r C ⟨hC.2.1, hC.2.2⟩).2
  obtain ⟨M, hM⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V
    (hK.image (f := fun k : NI V C => (k : GA D V) * g) (by fun_prop))
  obtain ⟨C', hC'⟩ := hF.2.2 A
  have hbound : ∀ n : NI V C, ∀ h, Sg ((n : GA D V) * g, h) * ‖F h‖ₑ ≤
      ENNReal.ofReal (max c 0 * (2 * M) ^ A * max C' 0) := by
    intro n h
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
    obtain ⟨γ', hγ', hh⟩ := exists_rat_height_le W h
    have e1 : Sg (((γ * k : NI V C) : GA D V) * g, h) = Sg ((k : GA D V) * g, γ' * h) := by
      rw [Subgroup.coe_mul, mul_assoc, h1 _ γ.2 (Subgroup.mem_subgroupOf.1 hγ), h2 _ hγ']
    rw [e1]
    have hkM : GlobalTheory.Grow.height V ((k : GA D V) * g) ≤ M := hM _ ⟨k, hk, rfl⟩
    have hV1 := GlobalTheory.Grow.one_le_height V ((k : GA D V) * g)
    have hW1 := GlobalTheory.Grow.one_le_height W (γ' * h)
    have hq1 := GlobalTheory.Grow.one_le_quotHeight W h
    have hc1 := bound_pow c _ _ M (GlobalTheory.Grow.quotHeight W h) A hV1 hkM hW1 hh
    have hb := bound_mul c M (GlobalTheory.Grow.quotHeight W h) ‖F h‖ C' A (by linarith) (by linarith) (norm_nonneg _) (hC' h)
    calc Sg ((k : GA D V) * g, γ' * h) * ‖F h‖ₑ
        ≤ ENNReal.ofReal (max c 0 * (M * (2 * GlobalTheory.Grow.quotHeight W h)) ^ A) * ENNReal.ofReal ‖F h‖ := by
          rw [ofReal_norm_eq_enorm]
          exact mul_le_mul' ((hc _ _).trans (ENNReal.ofReal_le_ofReal hc1)) le_rfl
      _ = ENNReal.ofReal (max c 0 * (M * (2 * GlobalTheory.Grow.quotHeight W h)) ^ A * ‖F h‖) :=
          (ENNReal.ofReal_mul (mul_nonneg (le_max_right c 0)
            (pow_nonneg (mul_nonneg (by linarith) (by linarith)) A))).symm
      _ ≤ ENNReal.ofReal (max c 0 * (2 * M) ^ A * max C' 0) := ENNReal.ofReal_le_ofReal hb
  have hν𝓕 := (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W ν 𝓕 hν h𝓕).ne
  have hκ𝓝 := GlobalTheory.TowerCT.vol D V r C hC κ 𝓝 hκ h𝓝
  refine ne_top_of_le_ne_top ?_ (lintegral_mono fun n => lintegral_mono fun h => hbound n h)
  rw [setLIntegral_const, setLIntegral_const]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hν𝓕) hκ𝓝

end GlobalTheory.ThetaLiftBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKerOfCoverKer
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.Chain.RealIt.LocalFromCover

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.KerTransfer

theorem locKer_of_coverKer (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ → R₁.U.H)
    (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s)
    (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)) (hm' : (m' : ℚ) = 2 * aS)
    (h₁ : Matches R₁ M τ (barMat e) m U) (h₂ : Matches R₂ M' τ (plainMat e') m' U')
    (hκ : IsPolyIso (M.ε τ) (M'.ε τ) e e' κ) (ha : IsKAct M' τ a') (hC : CoverKer p q R₂.HK) :
    LocKer M M' τ aS aT a' := by
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  have hmem : ∀ v, U'.symm (R₂.ι v) ∈ kFin M' τ := fun v =>
    (h₂.kfin _).2 ⟨v, (U'.apply_symm_apply _).symm⟩
  let j : R₂.HK.V →ₛₗ[starRingEnd ℂ] kFin M' τ :=
    { toFun := fun v => ⟨U'.symm (R₂.ι v), hmem v⟩
      map_add' := fun v w => Subtype.ext (by simp)
      map_smul' := fun c v => Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ]) }
  have hj : ∀ v, U' (j v : M'.H τ) = R₂.ι v := fun v => U'.apply_symm_apply _
  have hsurj : Function.Surjective j := fun y => by
    obtain ⟨v, hv⟩ := (h₂.kfin y).1 y.2
    exact ⟨v, Subtype.ext (U'.injective (by rw [hj, hv]))⟩
  have key : ∀ (Z : Type) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
      (B : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z), IsLocPair M M' τ aS aT a' B →
      ∃ B' : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] Z, IsCoverPair R₂.HK B' ∧
        ∀ P v, B' (κ P) v = B P (j v) := by
    intro Z _ _ B hB
    let B' : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] Z :=
      { toFun := fun P => (B (κ.symm P)).comp j
        map_add' := fun P Q => by ext v; simp
        map_smul' := fun c P => by ext v; simp }
    have hB' : ∀ P v, B' (κ P) v = B P (j v) := fun P v => by simp [B']
    refine ⟨B', ⟨fun X hX P P' y y' => ?_, fun Y hY P y => ?_⟩, hB'⟩
    · obtain ⟨P, rfl⟩ := κ.surjective P
      obtain ⟨P', rfl⟩ := κ.surjective P'
      have hX' : toFrame M τ (barMat e X) ∈ lieAt V τ := h₁.lie ▸ ⟨X, hX, rfl⟩
      have h3 : (barMat e X).map (starRingEnd ℂ) = Matrix.reindex e e X := by ext a b; simp [barMat]
      have h4 : (barMat e X).trace = -X.trace := by
        rw [barMat, trace_reindex', ← trace_conj hX]
        simp [Matrix.trace]
      have h := hB.skew _ hX' P P' (j y) (j y')
      simp only [sOp, fr_toFrame, trace_toFrame, h3, h4, LinearMap.add_apply, LinearMap.smul_apply,
        Module.End.one_apply, map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, map_neg, map_mul, map_ratCast, trace_conj hX] at h
      rw [← hκ.1, ← hκ.1, hB', hB', hB', hB']
      linear_combination h
    · obtain ⟨P, rfl⟩ := κ.surjective P
      have hY' : toFrame M' τ (plainMat e' Y) ∈ lieAt W τ := h₂.lie ▸ ⟨Y, hY, rfl⟩
      have h4 : (plainMat e' Y).trace = Y.trace := trace_reindex' e' Y
      have h5 : a' (toFrame M' τ (plainMat e' Y)) (j y) = j (R₂.HK.act Y y) - ((aS : ℂ) * Y.trace) • j y := by
        have h6 : a' (toFrame M' τ (plainMat e' Y)) (j y) =
            j (R₂.HK.act Y y + ((m' : ℂ) / 2 * Y.trace) • y) := by
          refine Subtype.ext (U'.injective ?_)
          rw [hj, ← h₂.der Y hY y _ (hj y), dRep, (ha.der _ hY' (j y)).deriv]
        rw [h6, map_add (f := _), LinearMap.map_smulₛₗ, map_mul, map_div₀, map_intCast, map_ofNat, trace_conj hY, hmC',
          sub_eq_add_neg, ← neg_smul]
        congr 2
        ring
      have h := hB.inv _ hY' P (j y)
      rw [h5, tOp, fr_toFrame, trace_toFrame, h4] at h
      rw [← hκ.2, hB', hB', ← h]
      simp [plainMat]
  intro Z₁ Z₂ _ _ _ _ B₁ B₂ hB₁ hB₂ hne n a b hs
  obtain ⟨C₁, hC₁, e₁⟩ := key Z₁ B₁ hB₁
  obtain ⟨C₂, hC₂, e₂⟩ := key Z₂ B₂ hB₂
  choose g hg using hsurj
  have hne' : C₁ ≠ 0 := fun h0 => hne (LinearMap.ext fun P => LinearMap.ext fun y => by
    rw [← hg y, ← e₁, h0]; rfl)
  have h := hC Z₁ Z₂ C₁ C₂ hC₁ hC₂ hne' n (fun i => κ (a i)) (fun i => g (b i)) (by simpa [e₁, hg] using hs)
  simpa [e₂, hg] using h

end GlobalTheory.Chain.IoLift.KerTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorFinitePlaceHeisenbergSumBaseVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensorFin

theorem isLocOp_of_mem_span {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hψ : IsStdChar D ψ (-1)) (hμ : IsCovolOne (ratL T S) μ 𝓕) {f₀ : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀) (p : Place D)
    {x : WO S T → ℂ} (hx : x ∈ Submodule.span ℂ (Set.range fun w : WO S T => heisO ψ S T (wAt p w) f₀)) :
    IsThetaFunO ψ S T x ∧ IsLocOp ψ S T μ 𝓕 f₀ p x := by
  have hh := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have ip := _root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    exact ⟨hh _ _ h₀, fun φ => φ w, fun _ _ => rfl, fun f hf => ⟨_, hh (wAt p w) f hf, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  | zero =>
    have hz : ∀ g, ipO μ 𝓕 (0 : WO S T → ℂ) g = 0 := fun g => by simp [ipO]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, fun _ => 0, fun _ _ => by simp,
      fun f _ => ⟨0, GlobalTheory.WeilVacMove.isTheta_zero, fun g _ => hz g⟩, fun g _ => hz g⟩
  | add y z _ _ hy hz =>
    obtain ⟨ty, L, L1, L2, L3⟩ := hy
    obtain ⟨tz, M, M1, M2, M3⟩ := hz
    refine ⟨GlobalTheory.WeilVacMove.isTheta_add ty tz, fun φ => L φ + M φ, fun c φ => ?_, fun f hf => ?_, fun g hg => ?_⟩
    · simp only [L1, M1, mul_add]
    · obtain ⟨a, ta, ha⟩ := L2 f hf
      obtain ⟨b, tb, hb⟩ := M2 f hf
      refine ⟨a + b, GlobalTheory.WeilVacMove.isTheta_add ta tb, fun g hg => ?_⟩
      rw [((ip a g ta hg).2.2.2.1 b tb).1, ha g hg, hb g hg]
    · rw [((ip y g ty hg).2.2.2.1 z tz).1, L3 g hg, M3 g hg]
  | smul c y _ hy =>
    obtain ⟨ty, L, L1, L2, L3⟩ := hy
    refine ⟨GlobalTheory.WeilVacMove.isTheta_smul c ty, fun φ => c * L φ, fun d φ => ?_, fun f hf => ?_, fun g hg => ?_⟩
    · simp only [L1]
      ring
    · obtain ⟨a, ta, ha⟩ := L2 f hf
      refine ⟨c • a, GlobalTheory.WeilVacMove.isTheta_smul c ta, fun g hg => ?_⟩
      rw [((ip a g ta hg).2.2.1 c).1, ha g hg]
    · rw [((ip y g ty hg).2.2.1 c).1, L3 g hg]

theorem isLocOp_of_isLocal_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (x : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → IsLocOp ψ S T μ 𝓕 f₀ (.inl v) x :=
  fun D ψ θ S T sS sT ΛS ΛT f₀ _ _ hb hμ v x hx =>
    (isLocOp_of_mem_span (base_std hb) hμ (base_theta hb) (.inl v)
      (GlobalTheory.T.localFactor_mem_span_localHeisenbergTranslates D ψ θ S T sS sT ΛS ΛT f₀ hb v x hx)).2

end GlobalTheory.PlaceTensorFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFock
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace ENNReal NNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift GlobalTheory.Size GlobalTheory.Grow GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift

namespace GlobalTheory.PairLift.LowAllPf

variable {D : D7}

section Kernel

variable {V W : HSp D} (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (g : GA D V) (h : GA D W)

theorem kernel_zero : thetaKO ω g h 0 = 0 := by simp [thetaKO]

theorem kernel_add (f f' : WO V W → ℂ) : thetaKO ω g h (f + f') = thetaKO ω g h f + thetaKO ω g h f' := by
  simp [thetaKO, map_add (f := _)]

theorem kernel_sub (f f' : WO V W → ℂ) : thetaKO ω g h (f - f') = thetaKO ω g h f - thetaKO ω g h f' := by
  simp [thetaKO, map_sub]

theorem kernel_smul (c : ℂ) (f : WO V W → ℂ) : thetaKO ω g h (c • f) = c * thetaKO ω g h f := by
  simp [thetaKO, map_smul]

end Kernel

theorem multT_apply_smooth_cusp {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S)
    (J : Set (GA D W)) (χ : GA D W → ℂ) (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) :
    IsAutFunSm θ W (F v) ∧ IsCuspFun W (F v) := by
  obtain ⟨T, hT, rfl⟩ := hF
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D θ W S M J χ T).1 hT
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    simp only [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul c (hT'.aut w), GlobalTheory.MultMem.isCuspFun_smul c (hT'.cusp w)⟩
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hx.1 hy.1,
      GlobalTheory.MultMem.isCuspFun_add hx.1.toIsAutFun hy.1.toIsAutFun hx.2 hy.2⟩

theorem liftInt_span_zero {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {Φ : GA D W → ℂ}
    (hI : ∀ f, IsThetaFunO ψ V W f → ∀ x, IntegrableOn (fun h => thetaKO ω x h f * Φ h) 𝓕 ν)
    {s : Set (WO V W → ℂ)} (hs : ∀ g ∈ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0) :
    ∀ g ∈ Submodule.span ℂ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg => exact hs g hg
  | zero =>
    refine ⟨GlobalTheory.OrientedHeis.theta_zero, funext fun x => ?_⟩
    simp [Lift.liftInt, kernel_zero]
  | add a b _ _ ha hb =>
    refine ⟨GlobalTheory.OrientedHeis.theta_add ha.1 hb.1, funext fun x => ?_⟩
    have e : Lift.liftInt ν 𝓕 (thetaKO ω) (a + b) Φ x =
        Lift.liftInt ν 𝓕 (thetaKO ω) a Φ x + Lift.liftInt ν 𝓕 (thetaKO ω) b Φ x := by
      simp only [Lift.liftInt, kernel_add, add_mul]
      exact integral_add (hI a ha.1 x) (hI b hb.1 x)
    simp [e, congrFun ha.2 x, congrFun hb.2 x]
  | smul c a _ ha =>
    refine ⟨GlobalTheory.OrientedHeis.theta_smul c ha.1, funext fun x => ?_⟩
    have e : Lift.liftInt ν 𝓕 (thetaKO ω) (c • a) Φ x = c * Lift.liftInt ν 𝓕 (thetaKO ω) a Φ x := by
      simp only [Lift.liftInt, kernel_smul, mul_assoc]
      exact integral_const_mul c _
    simp [e, congrFun ha.2 x]

theorem eq_zero_of_le_mul_all {a K : ℝ≥0∞} (hK : K ≠ ∞) (h : ∀ δ : ℝ≥0∞, 0 < δ → a ≤ K * δ) : a = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
  rw [zero_add]
  rcases eq_or_ne K 0 with hK0 | hK0
  · have h1 := h 1 one_pos
    rw [hK0, zero_mul] at h1
    exact h1.trans zero_le
  · refine (h (ε / K) (ENNReal.div_pos (ENNReal.coe_ne_zero.2 hε.ne') hK)).trans (le_of_eq ?_)
    exact ENNReal.mul_div_cancel hK0 hK

theorem liftInt_zero_of_approx {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    {cls : (GA D W → ℂ) → Prop} (hL : LiftLaws θ ψ ω ν 𝓕 cls) {Φ : GA D W → ℂ} (hΦ : cls Φ)
    {μ : Measure (WO V W)} {𝓓 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure)
    (h𝓓 : IsAddFundamentalDomain (ratL W V) 𝓓 μ) {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    {f : WO V W → ℂ} (hf : f ∈ thetaLevel ψ V W U)
    (happ : ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g ∈ thetaLevel ψ V W U,
      Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 ∧ sobO ψ θ μ 𝓓 d (f - g) < δ) :
    Lift.liftInt ν 𝓕 (thetaKO ω) f Φ = 0 := by
  obtain ⟨A, hA⟩ := hL.bound
  obtain ⟨d, hd⟩ := hA 0
  obtain ⟨C, hC⟩ := hd μ 𝓓 hμ h𝓓 U hU
  have hKt : (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top (hL.decay_ne_top Φ hΦ A)
  funext x
  have hI : ∀ f', IsThetaFunO ψ V W f' → IntegrableOn (fun h => thetaKO ω x h f' * Φ h) 𝓕 ν := fun f' hf' => by
    simpa only [rTr, mul_one] using hL.integ f' Φ hf' hΦ x 1
  have key : ∀ δ : ℝ≥0∞, 0 < δ → ENNReal.ofReal (‖Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x‖ / height V x ^ A) ≤
      (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ * δ := by
    intro δ hδ
    obtain ⟨g, hgU, hg0, hlt⟩ := happ d δ hδ
    have hfg : f - g ∈ thetaLevel ψ V W U := sub_mem hf hgU
    have e : Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x = Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x := by
      have e' : Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x =
          Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x - Lift.liftInt ν 𝓕 (thetaKO ω) g Φ x := by
        simp only [Lift.liftInt, kernel_sub, sub_mul]
        exact integral_sub (hI f hf.1) (hI g hgU.1)
      rw [e', congrFun hg0 x, Pi.zero_apply, sub_zero]
    have h2 : ENNReal.ofReal (‖Lift.liftInt ν 𝓕 (thetaKO ω) (f - g) Φ x‖ / height V x ^ A) ≤
        growthSob θ V 0 A (lift ω ν 𝓕 (f - g) Φ) := by
      simp only [growthSob, wordSum_zero, growthSize]
      exact le_iSup (fun y => ENNReal.ofReal (‖lift ω ν 𝓕 (f - g) Φ y‖ / height V y ^ A)) x
    rw [e]
    calc _ ≤ _ := h2
      _ ≤ C * sobO ψ θ μ 𝓓 d (f - g) * decayInt ν 𝓕 A Φ := hC (f - g) hfg Φ hΦ
      _ = (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ * sobO ψ θ μ 𝓓 d (f - g) := by ring
      _ ≤ (C : ℝ≥0∞) * decayInt ν 𝓕 A Φ * δ := by gcongr
  have h0 := eq_zero_of_le_mul_all hKt key
  rw [ENNReal.ofReal_eq_zero] at h0
  have hpos : 0 < height V x ^ A := pow_pos (height_pos V x) A
  have h3 : ‖Lift.liftInt ν 𝓕 (thetaKO ω) f Φ x‖ ≤ 0 := by
    simpa using (div_le_iff₀ hpos).1 h0
  exact norm_le_zero_iff.1 h3

end GlobalTheory.PairLift.LowAllPf

namespace GlobalTheory.PairLift

theorem lowAll_of_lowFock : ∀ (D : D7) (X : ProvA), Inputs D X → LowFock D X → LowAll D X := by
  intro D X hIn hLF S S' aS aT hR i V' W M' θ ψ hθ hi hs ω' hω ν 𝓕 hν h𝓕 F hF v f' hf
  obtain ⟨χS, χT, hW, -⟩ := id hω
  have hL := hIn.laws V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hFv := LowAllPf.multT_apply_smooth_cusp θ M' ∅ 1 F hF v
  obtain ⟨A⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').1
  obtain ⟨μ, 𝓓, hμ⟩ := GlobalTheory.Size.exists_isCovolOne V' W
  obtain ⟨U, hU, hfU, happ⟩ := hIn.dense V' W A (Fr.ofModel M') θ ψ hW.std hθ μ 𝓓 hμ f' hf
  have hI : ∀ f, IsThetaFunO ψ V' W f → ∀ x, IntegrableOn (fun h => thetaKO ω' x h f * F v h) 𝓕 ν :=
    fun f hf x => by simpa only [rTr, mul_one] using hL.integ f (F v) hf hFv x 1
  have hspan := LowAllPf.liftInt_span_zero hI
    (s := {g | ∃ f₀ P, IsVacF ψ θ A (Fr.ofModel M') f₀ ∧ f₀ ∈ thetaLevel ψ V' W U ∧
      g = ptF ψ θ A (Fr.ofModel M') f₀ P})
    (by
      rintro _ ⟨f₀, P, hv, -, rfl⟩
      exact ⟨GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW.std hθ _ _ _ _ hv.1 P,
        hLF S S' aS aT hR i V' W M' θ ψ hθ hi hs ω' hω ν 𝓕 hν h𝓕 F hF v A f₀ hv P⟩)
  refine LowAllPf.liftInt_zero_of_approx hL hFv hμ.1 hμ.2.1 hU hfU fun d δ hδ => ?_
  obtain ⟨g, hg, hgU, hlt⟩ := happ d δ hδ
  exact ⟨g, hgU, (hspan g hg).2, hlt⟩

end GlobalTheory.PairLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoeffIsotropicTranslatesEqFourierCoeffs
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCoefUnfold

theorem pcoef : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ κ : ℝ, (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ (y : Mx D W.rank r) (a : Matrix (Fin W.rank) (Fin r) D.host.E), (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) = ∫ t in 𝓨, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * (κ • (∫ y' in 𝓨, ∫ x in 𝓕', (heisO ψ V W (isoPart V W C y) F) (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ)) ∂μ := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ μV 𝓕V hμV h𝓕V μ' 𝓕' hμ' h𝓕' κ hκ F G hF hG y a
  have hth := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W
  have horth := GlobalTheory.TwistFormsOrth.orthogonal D V V' W r C B hs C' h1 h2 h3
  have hPt : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C y) F) := hth.1 _ F hF
  have hγrat : isoPart V W C (a.map (incA D)) ∈ ratL W V := by
    rw [← GlobalTheory.TwistEquiRat.ratW_eq_isoPart]; exact ⟨_, rfl⟩
  have hfirst : heisO ψ V W (isoPart V W C (y + a.map (incA D))) F =
      heisO ψ V W (isoPart V W C (a.map (incA D))) (heisO ψ V W (isoPart V W C y) F) := by
    rw [hth.2.1, GlobalTheory.TwistEquiRat.symplOH_isoPart V W C hs.frame, AddChar.map_zero_eq_one, one_smul,
      GlobalTheory.TwistEquiRat.isoPart_add, add_comm]
  have hpt : ∀ w, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) =
      ψ (symplO V W w (isoPart V W C (a.map (incA D)))) * (heisO ψ V W (isoPart V W C y) F w * star (G w)) := by
    intro w
    rw [hfirst, GlobalTheory.ThetaSchur.heisO_rat hPt hγrat]
    ring
  have hsym : ∀ t y' x, symplO V W (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)
      (isoPart V W C (a.map (incA D))) = symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))) := by
    intro t y' x
    rw [GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left, horth.1 y' _,
      GlobalTheory.PlaceModel.symplO_skew V W (isoPart V W C (a.map (incA D))) (midPart V V' W B x), horth.2.1 _ x]
    simp
  have hHt : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C (y + a.map (incA D))) F) := hth.1 _ F hF
  have hHc : Continuous fun w => heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) :=
    hHt.cont.mul hG.cont.star
  have hHb : ∃ b : ℝ, ∀ w, ‖heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w)‖ ≤ b := by
    obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
    obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn hHc.continuousOn
    refine ⟨b, fun w => ?_⟩
    obtain ⟨g, hg, h⟩ := hKc w
    rw [← GlobalTheory.ThetaSchur.prod_periodic hψ hHt hG hg w]
    exact hb _ h
  have key := hκ _ hHc hHb (fun g hg w => GlobalTheory.ThetaSchur.prod_periodic hψ hHt hG hg w)
  rw [key]
  simp_rw [hpt, hsym, integral_const_mul]
  rw [← integral_smul]
  congr 1
  funext t
  rw [mul_smul_comm]

end GlobalTheory.TwistCoefUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceDeterminantPowerMulNeZeroExp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

theorem detPow_mul_ne_zero_exp : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (m : D.what₂.Tau → ℤ), (∀ a b, detPow θ V m (a * b) = detPow θ V m a * detPow θ V m b) ∧ (∀ a, detPow θ V m a ≠ 0) ∧ (∀ Y : GlobalTheory.SmoothForms.LieN V, detPow θ V m (GlobalTheory.SmoothForms.expInf θ V Y) = cexp (GlobalTheory.AdSpan.ConjHol.trLin V m Y)) := by
  intro D θ hθ V m
  have R : GlobalTheory.SmoothForms.RealPoints θ V := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hd : ∀ a, detPow θ V m a = ∏ ρ, (infMat D.sp.cm.sig V.gram (θ ρ) a).det ^ (m ρ) := fun a => rfl
  refine ⟨fun a b => ?_, fun a => ?_, fun Y => ?_⟩
  · rw [hd, hd, hd, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [R.2.2.2.1, det_mul, mul_zpow]
  · rw [hd]
    refine Finset.prod_ne_zero_iff.2 fun ρ _ => zpow_ne_zero _ fun h0 => ?_
    have h : (infMat D.sp.cm.sig V.gram (θ ρ) a)ᴴ * gramAt D V ρ * infMat D.sp.cm.sig V.gram (θ ρ) a = gramAt D V ρ :=
      GlobalTheory.RealLift.archM_mem hθ V a ρ
    have h2 := congrArg det h
    rw [det_mul, h0, mul_zero] at h2
    exact (R.1 ρ).2.ne_zero h2.symm
  · rw [hd]
    change _ = cexp (∑ ρ, (m ρ : ℂ) * trace (Y ρ).1)
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [(GlobalTheory.SmoothForms.isExpFam_expInf R Y).2 ρ, Formalism.MainNotions.DIV.Inh.det_exp, Complex.exp_int_mul]

end GlobalTheory.AdSpan.ConjHol
end
end

