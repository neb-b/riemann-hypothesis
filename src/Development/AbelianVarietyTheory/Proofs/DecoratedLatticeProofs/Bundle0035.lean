module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainSupportOneOfPattern
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMulOfSupport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AtMostOneHolds
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem atMostOne_holds : AtMostOne := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _
  have hpat : S.Pattern t := _root_.GlobalTheory.SymChain.pattern_iter k s κ S t
  have hclass : S.OneClass t ν := GlobalTheory.T.symmetricChain_oneLatticeClass k ν hν s κ S t
  have hsupp : S.SupportOne t := _root_.GlobalTheory.SymSupport.supportOne_of_pattern k s κ S t hpat
  exact ⟨_root_.GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne k ν hν s κ S t hclass hsupp, GlobalTheory.T.symmetricChain_projected_level_of_pattern k s κ S t hpat, _root_.GlobalTheory.SymChain.oneCoupling k s κ S t hpat⟩

end GlobalTheory.SymChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiTargetBilinearFormIntegral
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open Filter Topology

noncomputable section
namespace GlobalTheory.PosOne.FJTarget
open GlobalTheory.RootEx.Unfolding (omR omR_val omR_mul omR_smooth orbit_locallyConstant opL)

theorem exists_isQuotInt_tInt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c p : ℕ} (hp : 1 ≤ p) (hpc : p ≤ c) {ψ : AddChar k Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ))
    (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure]
    {A : Type} [AddCommGroup A] [Module ℂ A] {σ : Representation ℂ (GL (n ⊕ Fin c) k) A} (hσ : IsSmoothRep σ)
    {B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hB : BilPos ψ μ p σ B) (F : A)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    ∃ z, IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) z := by
  have hE := (opE_SB_and_linear k n n' c p ψ hψ ν).1
  let E : GL (n ⊕ Fin c) k → SB (Matrix n n' k) := fun h =>
    ⟨opE ψ ν p (om μ 1 h Φ.1), hE _ (om_mem_SB μ 1 h Φ.2)⟩
  have hfE : ∀ h, tInt ψ ν μ p σ B F Φ.1 h = B (E h) (σ h F) := fun h => by
    unfold tInt
    rw [show opE ψ ν p (om μ 1 h Φ.1) = ((E h : SB (Matrix n n' k)) : Matrix n n' k → ℂ) from rfl,
      GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe]
  have hmul : ∀ (g h : GL (n ⊕ Fin c) k) (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ),
      om μ 1 (g * h) Ψ = om μ 1 g (om μ 1 h Ψ) := fun g h Ψ => by
    rw [← om_mul, one_mul]
  refine (GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp hpc ν μX μG _).2 ?_ ?_ ?_
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro h
    have hU : IsOpen ({u : GL (n ⊕ Fin c) k | om μ 1 u Φ.1 = Φ.1} ∩ {u | σ u F = F}) :=
      ((isOpen_stabilizer_om hμ Φ.2).preimage (Continuous.prodMk_right 1)).inter (hσ F)
    have ht : Filter.Tendsto (fun y : GL (n ⊕ Fin c) k => h⁻¹ * y) (𝓝 h) (𝓝 1) := by
      simpa using (continuous_const_mul h⁻¹).tendsto h
    filter_upwards [ht.eventually (hU.mem_nhds ⟨om_one μ _, by simp⟩)] with y hy
    obtain ⟨u, rfl⟩ : ∃ u, y = h * u := ⟨h⁻¹ * y, by simp⟩
    rw [inv_mul_cancel_left] at hy
    have h1 : om μ 1 u Φ.1 = Φ.1 := hy.1
    have h2 : σ u F = F := hy.2
    unfold tInt
    rw [hmul, h1, map_mul, Module.End.mul_apply, h2]
  · obtain ⟨Λ, hΛ, hΛ'⟩ := GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup k _ _ Φ.1 Φ.2
    obtain ⟨Ω, hΩ, H⟩ := opE_support_compact_mod_R k n n' c p hp hpc ψ hψ hψ1 ν (tsupport Φ.1)
      Φ.2.2 Λ hΛ
    refine ⟨Ω, hΩ, fun h hh => ?_⟩
    have hne : E h ≠ 0 := fun h0 => hh (by rw [hfE, h0]; simp)
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, opE ψ ν p (om μ 1 h Φ.1) x₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (Subtype.ext (funext hc))
    exact H μ Φ.1 (subset_tsupport _) hΛ' (fun _ => 1) (IsLocallyConstant.const 1) h x₀
      (by simpa using hx₀)
  · intro x u hu h
    set a : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) with ha
    let Ψ : SB (Matrix n n' k) := ⟨om μ 1 x (E h).1, om_mem_SB μ 1 x (E h).2⟩
    have h1 : E (embX c x * u * h) = (a * (ψ (-simpleSum u) : ℂ)) • Ψ := by
      apply Subtype.ext
      show opE ψ ν p (om μ 1 (embX c x * u * h) Φ.1) =
        (a * (ψ (-simpleSum u) : ℂ)) • om μ 1 x (opE ψ ν p (om μ 1 h Φ.1))
      rw [mul_assoc, hmul, (opE_om_embX k n n' c p hp hpc ψ ν μ _).1, hmul,
        opE_om_target_unipotent k n n' c p hp hpc ψ ν μ _ u hu]
      funext y
      simp only [om, Pi.smul_apply, smul_eq_mul, ha]
      ring
    have h3 : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]; simp
    have h4 : a * a =
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) := by
      rw [ha, ← Complex.ofReal_mul, ← Real.rpow_add (nabs_pos _ _)]
      congr 2
      ring
    have h5 := hB.1 (E h) u hu (σ h F)
    have h6 := hB.2 x (E h) Ψ (σ u (σ h F)) rfl
    rw [hfE, hfE, h1, map_smul, LinearMap.smul_apply, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply, h6, h5, ← h4, ← ha, smul_eq_mul]
    linear_combination (a * a * B (E h) (σ h F)) * h3

theorem target_bilinear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : c = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (fj : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : Represents ψ ν ρ σ fj B) (_ : BilPos ψ μ (ρ + 1) σ B) (F : A) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (z : ℂ), IsQuotInt ν μX μG (ρ + 1) (tInt ψ ν μ (ρ + 1) σ B F Φ.1) z ↔ FJInt ψ ν μX μG μ ρ (fun h Ψ Φ₀ => fj Ψ (σ h F) Φ₀) Φ.1 z := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ρ h1 hc ψ hψ hψ1 ν hν μ hμ μX _ μG _ A _ _ σ hσ fj B hb hp F Φ z
  have h2 : ρ < c := by omega
  have := hν.1
  have := secondCountable k
  have := t2Space k
  have e : ∀ h β, app B (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F)) =
      tInt ψ ν μ (ρ + 1) σ B F Φ.1 (colE c (ρ + 1) β * h) := by
    intro h β
    have := om_mul μ 1 1 (colE c (ρ + 1) β) h Φ.1
    rw [one_mul] at this
    unfold tInt
    rw [this, map_mul]
    rfl
  obtain ⟨z₀, hz₀⟩ := exists_isQuotInt_tInt (p := ρ + 1) (by omega) (by omega) hψ hψ1 ν μ hμ μX μG hσ hp F Φ
  have W := _root_.GlobalTheory.QuotIntFJ.weil_formula_FJ k n c ρ h1 h2 ν μX μG (tInt ψ ν μ (ρ + 1) σ B F Φ.1)
  have val : ∀ h w, HasTensorVal (fun Ψ Φ₀ => fj Ψ (σ h F) Φ₀) (fl ψ ν μ ρ (om μ 1 h Φ.1)) w ↔
      w = ∫ β : n → k, app B (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
        ∂(Measure.pi fun _ => ν) := by
    intro h
    have v1 : ∀ w, HasTensorVal (fun Ψ Φ₀ => fj Ψ (σ h F) Φ₀) (fl ψ ν μ ρ (om μ 1 h Φ.1)) w →
        w = ∫ β : n → k, app B (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
          ∂(Measure.pi fun _ => ν) := by
      rintro w ⟨m, Ψ, Φ₀, hd, rfl⟩
      simp only [(hb.2 _ _ _).2]
      rw [← MeasureTheory.integral_finsetSum _ fun i _ => (hb.2 _ _ _).1]
      congr 1; funext β
      have : (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) = (∑ i, (Φ₀ i).1 β • Ψ i : SB (Matrix n n' k)).1 := by
        funext x₀
        simp [hd, mul_comm]
      rw [this, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe]
      simp
    let T : (n → k) → SB (Matrix n n' k) := fun β =>
      opL hψ ν (ρ + 1) (omR μ (1, colE c (ρ + 1) β) (omR μ (1, h) Φ))
    have hT : IsLocallyConstant T :=
      ((orbit_locallyConstant (omR_smooth hμ) (omR μ (1, h) Φ)).comp_continuous
        (continuous_const.prodMk ExchangeSupport.continuous_colE)).comp fun Ψ => opL hψ ν (ρ + 1) Ψ
    obtain ⟨K, hK, HK⟩ := ColumnSupport.opE_colE_eq_zero k n n' c ρ h2 ψ ν μ _ (omR μ (1, h) Φ).2
    obtain ⟨m, Ψ, Φ₀, hd⟩ := GlobalTheory.T.exists_sum_smul_of_locallyConstant_compactSupport (n → k) _ T hT K hK fun β hβ => Subtype.ext (by
      have := HK β hβ fun _ => 1
      simp only [one_mul] at this
      exact this)
    have v2 : HasTensorVal (fun Ψ Φ₀ => fj Ψ (σ h F) Φ₀) (fl ψ ν μ ρ (om μ 1 h Φ.1)) _ :=
      ⟨m, Ψ, Φ₀, fun x y => by
        have := congrArg (fun t : SB (Matrix n n' k) => t.1 x) (hd y)
        refine Eq.trans this ?_
        simp [mul_comm], rfl⟩
    exact fun w => ⟨v1 w, fun hw => by rw [hw, ← v1 _ v2]; exact v2⟩
  have i1 : IsQuotInt ν μX μG (ρ + 1) (tInt ψ ν μ (ρ + 1) σ B F Φ.1) z ↔
        IsQuotIntFJ ν μX μG ρ (fun h => ∫ β : n → k,
          app B (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
            ∂(Measure.pi fun _ => ν)) z := by
    simp only [e]
    exact ⟨fun hz => (W z hz).2, fun hz => _root_.GlobalTheory.QuotIntFJ.quotIntFJ_unique k n c ρ h1 h2 ν μX μG _ _ _ (W z₀ hz₀).2 hz ▸ hz₀⟩
  refine i1.trans ⟨fun hz => ⟨_, fun h => (val h _).2 rfl, hz⟩, ?_⟩
  rintro ⟨f, hf, hz⟩
  rwa [show f = _ from funext fun h => (val h _).1 (hf h)] at hz

end GlobalTheory.PosOne.FJTarget
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeSeriesCellHasSumStatement
section
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_series_cell_has_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (e : Fin n → ℤ), ∀ g ∈ cell k (Fin n) ϖ e, ∀ X : ℂ, (∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * X ^ 2‖ < 1) → HasSum (fun h : {h : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧ (∀ i j, (h.out⁻¹ * g : GL (Fin n) k).1 i j ∈ 𝒪[k])} => X ^ ((-ord k (Matrix.GeneralLinearGroup.det h.1.out)).toNat + (ord k (Matrix.GeneralLinearGroup.det (h.1.out⁻¹ * g))).toNat)) (X ^ (∑ i, |e i|).toNat * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)⁻¹) := by
  first | exact @GlobalTheory.LatticePair.hasSum_pair | exact GlobalTheory.LatticePair.hasSum_pair | (intros; apply GlobalTheory.LatticePair.hasSum_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelReductionExtendEvaluatedIntegrated
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.FlatFactor.KerRedStep

theorem mul_sum_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (S : Finset (m × m')), (∀ e ∈ S, ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → ∀ (b : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (∑ e ∈ S, b e * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β S hS b
  have hlc := GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψ hψc
  induction S using Finset.induction_on with
  | empty =>
    intro Θ Θ' h
    congr 1
    exact Subtype.ext (funext fun t => by simp [h])
  | insert j S hj ih =>
    intro Θ Θ' h
    have hc : Continuous fun t : Matrix m m' k => ∑ e ∈ S, b e * (t e.1 e.2 - β e.1 e.2) :=
      continuous_finsetSum _ fun e _ => continuous_const.mul
        ((continuous_id.matrix_elem _ _).sub continuous_const)
    let Θm : SB (Matrix m m' k) := ⟨fun t => (ψ (∑ e ∈ S, b e * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t,
      (hlc.comp_continuous hc).mul Θ.2.1, Θ.2.2.mul_left⟩
    have h1 : l Θ' = l Θm := hS j (Finset.mem_insert_self j S) (b j) Θm Θ' fun t => by
      rw [h t, Finset.sum_insert hj, AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]
    rw [h1]
    exact ih (fun e he => hS e (Finset.mem_insert_of_mem he)) Θ Θm fun t => rfl

theorem trans_sum_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (S : Finset (m × m')), (∀ e ∈ S, ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) → ∀ (a : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + ∑ e ∈ S, Matrix.single e.1 e.2 (a e))) → l Θ' = l Θ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β S hS a
  induction S using Finset.induction_on with
  | empty =>
    intro Θ Θ' h
    congr 1
    exact Subtype.ext (funext fun t => by simp [h])
  | insert j S hj ih =>
    intro Θ Θ' h
    let c : Matrix m m' k := ∑ e ∈ S, Matrix.single e.1 e.2 (a e)
    let Θm : SB (Matrix m m' k) := ⟨fun t => Θ.1 (t + c),
      Θ.2.1.comp_continuous (continuous_id.add continuous_const),
      Θ.2.2.comp_homeomorph (Homeomorph.addRight c)⟩
    have h1 : l Θ' = l Θm := hS j (Finset.mem_insert_self j S) (a j) Θm Θ' fun t => by
      rw [h t, Finset.sum_insert hj, ← add_assoc]
    rw [h1]
    exact ih (fun e he => hS e (Finset.mem_insert_of_mem he)) Θ Θm fun t => rfl

theorem kerRed_extend : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it ev' it' : Finset (m × m')), ev ⊆ ev' → it ⊆ it' → Disjoint ev' it' → GlobalTheory.FlatFactor.KerRed ν ev it β l → (∀ e ∈ ev', e ∉ ev → ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → (∀ e ∈ it', e ∉ it → ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) → GlobalTheory.FlatFactor.KerRed ν ev' it' β l := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β ev it ev' it' hev hit hd hK hmul htr
  have hd0 : Disjoint ev it := Finset.disjoint_of_subset_left hev (Finset.disjoint_of_subset_right hit hd)
  have L1 : (∀ e ∈ ev, ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) := by
    intro e he b Θ Θ' h
    have he' : e ∉ it := Finset.disjoint_left.mp hd0 he
    have h0 : l (Θ' - Θ) = 0 := hK _ fun t => by
      unfold GlobalTheory.FlatFactor.red
      have hz : ∀ a, (Θ' - Θ).1 (GlobalTheory.FlatFactor.fill ev it β t a) = 0 := by
        intro a
        have hf : GlobalTheory.FlatFactor.fill ev it β t a e.1 e.2 = β e.1 e.2 := by
          simp [GlobalTheory.FlatFactor.fill, he, he']
        simp [h, hf]
      simp [hz]
    rwa [map_sub, sub_eq_zero] at h0
  have hM : (∀ e ∈ ev', ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) := by
    intro e he
    by_cases h : e ∈ ev
    · exact L1 e h
    · exact hmul e he h
  have hT : (∀ e ∈ it', ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) := by
    intro e he
    by_cases h : e ∈ it
    · exact _root_.GlobalTheory.FlatFactor.kerRed_translate_invariant k ψ ν hψc hψ1 hν m m' M l β ev it hd0 hK e h
    · exact htr e he h
  exact _root_.GlobalTheory.FlatFactor.KerEngine.kerRed_of_laws k ψ ν hψc hψ1 hν m m' M l β ev' it' hd
    (mul_sum_law k ψ ν hψc hψ1 hν m m' M l β ev' hM) (trans_sum_law k ψ ν hψc hψ1 hν m m' M l β it' hT)

end GlobalTheory.FlatFactor.KerRedStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneDblIffSum
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

namespace GlobalTheory.PosOne

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma isHaarMeasure_framePositiveSum_rescale (ν : Measure k)
    [ν.IsAddHaarMeasure] (b : GL (n ⊕ Fin c) k) (m : Measure (GL n k)) [m.IsHaarMeasure] :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b m).IsHaarMeasure := by
  have hpos := ENNReal.toReal_pos_iff.mp (_root_.GlobalTheory.StepData.volN_stabLat ν b)
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale
  exact Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr hpos.2.ne)
    (ENNReal.inv_ne_top.mpr hpos.1.ne')

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma posOne_toOne_zero (ν : Measure k)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (P : ℕ) :
    _root_.GlobalTheory.PosOne.toOne ν σ P (fun _ => 0) = fun _ => 0 := by
  have hdown : ∀ p, _root_.GlobalTheory.RootEx.exDown ν p σ (fun _ => (0 : ℂ)) = fun _ => 0 := by
    intro p
    funext v
    simp [_root_.GlobalTheory.RootEx.exDown]
  have key : ∀ m : ℕ, _root_.GlobalTheory.PosOne.toOne ν σ (m + 1) (fun _ => 0) = fun _ => 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [show m + 1 + 1 = m + 2 from rfl, _root_.GlobalTheory.PosOne.toOne_succ, hdown, ih]
  cases P with
  | zero => rfl
  | succ m => exact key m

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma fourierJacobiAverage_app_toOne_comm {X : Type} [TopologicalSpace X]
    (ν : Measure k) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (P : ℕ)
    (B B₁ : _root_.GlobalTheory.SplitWeil.SB X →ₗ[ℂ] A →ₗ[ℂ] ℂ)
    (hB : ∀ Ψ v, B₁ Ψ v = _root_.GlobalTheory.PosOne.toOne ν σ P (B Ψ) v) (x : X → ℂ) (v : A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B₁ x v =
      _root_.GlobalTheory.PosOne.toOne ν σ P (fun w => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B x w) v := by
  by_cases hx : x ∈ _root_.GlobalTheory.SplitWeil.SB X
  · simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app, dif_pos hx]
    exact hB _ _
  · simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app, dif_neg hx, LinearMap.zero_apply]
    rw [posOne_toOne_zero]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma fourierJacobiAverage_app_of_mem_SB {X V : Type} [TopologicalSpace X]
    [AddCommGroup V] [Module ℂ V] (B : _root_.GlobalTheory.SplitWeil.SB X →ₗ[ℂ] V) {x : X → ℂ}
    (hx : x ∈ _root_.GlobalTheory.SplitWeil.SB X) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B x = B ⟨x, hx⟩ := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app, dif_pos hx]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma fourierJacobiAverage_app_of_not_mem_SB {X V : Type} [TopologicalSpace X]
    [AddCommGroup V] [Module ℂ V] (B : _root_.GlobalTheory.SplitWeil.SB X →ₗ[ℂ] V) {x : X → ℂ}
    (hx : x ∉ _root_.GlobalTheory.SplitWeil.SB X) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B x = 0 := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app, dif_neg hx]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma fourierJacobiAverage_app_zero_map {X V : Type} [TopologicalSpace X]
    [AddCommGroup V] [Module ℂ V] (x : X → ℂ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (0 : _root_.GlobalTheory.SplitWeil.SB X →ₗ[ℂ] V) x = 0 := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app
  split_ifs <;> rfl


open MeasureTheory ValuativeRel Matrix in
theorem _root_.GlobalTheory.PosOne.oneDbl_iff_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ) (_ : c + 1 = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) (ν : Measure k) (_ : _root_.GlobalTheory.SplitWeil.IsUnitVol ν) (μ₁ μ₂ : kˣ →* ℂˣ) (_ : IsOpen (μ₁.ker : Set kˣ)) (_ : IsOpen (μ₂.ker : Set kˣ)) (m₁ : Measure (GL n₁ k)) [m₁.IsHaarMeasure] (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) [G₁.IsHaarMeasure] (m₂ : Measure (GL n₂ k)) [m₂.IsHaarMeasure] (G₂ : Measure (GL (n₂ ⊕ Fin c) k)) [G₂.IsHaarMeasure] (L₁ : _root_.GlobalTheory.StepData.Level (GL (n₁ ⊕ Fin (c + 1)) k)) (L₂ : _root_.GlobalTheory.StepData.Level (GL (n₂ ⊕ Fin c) k)) (_ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO L₁.J) (_ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO L₂.J) (_ : G₁ L₁.J = 1) (_ : G₂ L₂.J = 1) (b₁ : GL (n₁ ⊕ Fin (c + 1)) k) (b₂ : GL (n₂ ⊕ Fin c) k) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A) (_ : _root_.GlobalTheory.SplitWeil.IsSmoothRep σ) (T : _root_.GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k) →ₗ[ℂ] _root_.GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : _root_.GlobalTheory.PosOne.TriPos ψ μ₁ μ₂ ρ σ T) (F : A) (_ : ∀ j : L₂.J, σ (j : GL (n₂ ⊕ Fin c) k) F = (L₂.lam j : ℂ) • F) (Φ₁ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (Φ₂ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) (_ : ∀ j : L₁.J, _root_.GlobalTheory.SplitWeil.om μ₁ 1 (j : GL (n₁ ⊕ Fin (c + 1)) k) Φ₁.1 = (((L₁.lam j)⁻¹ : ℂˣ) : ℂ) • Φ₁.1) (_ : _root_.GlobalTheory.StepData.HasTypes μ₂ L₁ L₂ Φ₂.1) (α : GL (n₀ ⊕ Fin (c + 1 + 1)) k) (T₁ : Finset (GL (n₁ ⊕ Fin (c + 1)) k)) (T₂ : Finset (GL (n₂ ⊕ Fin c) k)) (_ : _root_.GlobalTheory.PosOne.Covers 1 L₁.J T₁ fun h => _root_.GlobalTheory.StepData.flat ψ ν μ₁ Φ₁.1 α h) (_ : ∀ γ ∈ T₁, _root_.GlobalTheory.PosOne.Covers 1 L₂.J T₂ fun h => _root_.GlobalTheory.StepData.flat ψ ν μ₂ Φ₂.1 γ h) (z : ℂ), _root_.GlobalTheory.PosOne.OneDbl ψ ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₁ m₁) G₁ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂) G₂ μ₁ μ₂ ρ σ T F (_root_.GlobalTheory.SplitWeil.om μ₁ α 1 Φ₁.1) Φ₂.1 z ↔ z = ∑ γ ∈ T₁, ∑ β ∈ T₂, (((m₁ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₁.J γ))).toReal⁻¹ * (m₂ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) * _root_.GlobalTheory.PosOne.toOne ν σ ρ (fun v => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app T (_root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ)) (_root_.GlobalTheory.StepData.xi ψ ν μ₂ Φ₂.1 L₂.J b₂ γ β) v) (σ β F) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hcond ν hν μ₁ μ₂ hμ₁ hμ₂ m₁ _ G₁ _ m₂ _ G₂ _
    L₁ L₂ hL₁ hL₂ hG₁ hG₂ b₁ b₂ A _ _ σ hσ T hT F hF Φ₁ Φ₂ hΦ₁ hΦ₂ α T₁ T₂ hT₁ hT₂ z
  haveI : ν.IsAddHaarMeasure := hν.1
  have hψ1 : ψ ≠ 1 := hcond.ne_one
  have hsd : _root_.GlobalTheory.SplitWeil.IsSelfDual ψ ν :=
    _root_.GlobalTheory.SplitWeil.isSelfDual_of_isUnitVol ν hcond hν
  have hρ1 : 1 ≤ ρ := by omega
  have hρc : ρ ≤ c := by omega
  haveI : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₁ m₁).IsHaarMeasure :=
    isHaarMeasure_framePositiveSum_rescale ν b₁ m₁
  haveI : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂).IsHaarMeasure :=
    isHaarMeasure_framePositiveSum_rescale ν b₂ m₂
  obtain ⟨ρ₁, hρ₁⟩ := (_root_.GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n₁ ⊕ Fin (c + 1)) (n₂ ⊕ Fin c) μ₂ hμ₂).1
  have hρ₁s := (_root_.GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n₁ ⊕ Fin (c + 1)) (n₂ ⊕ Fin c) μ₂ hμ₂).2 ρ₁ hρ₁
  obtain ⟨b, hb, -, hbone⟩ := _root_.GlobalTheory.PosOne.MidVertex.exists_bilPos_mid k n₀ n₁ n₂ c ρ hcρ ψ hψ hψ1 ν hsd
    μ₁ μ₂ hμ₁ hμ₂ m₁ G₁ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂) G₂ A σ hσ T hT F ρ₁ hρ₁
  obtain ⟨B', hB'eq, hB'⟩ := (_root_.GlobalTheory.PosOne.toOne_isPosOne k n₁ n₀ (c + 1) ρ hρ1 (by omega)
    ψ hψ hψ1 ν _ ρ₁ hρ₁s).2 μ₁ hμ₁ b hb
  have hin : ∀ Ψ, ∃ B₁ : _root_.GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ,
      (∀ Ψ' v, B₁ Ψ' v = _root_.GlobalTheory.PosOne.toOne ν σ ρ (T Ψ Ψ') v) ∧
        _root_.GlobalTheory.PosOne.BilPos ψ μ₂ 1 σ B₁ := fun Ψ =>
    (_root_.GlobalTheory.PosOne.toOne_isPosOne k n₂ n₁ c ρ hρ1 hρc ψ hψ hψ1 ν A σ hσ).2 μ₂ hμ₂ (T Ψ)
      (hT.1 Ψ)
  choose B₁ hB₁eq hB₁ using hin
  have uniq₁ := fun f => (_root_.GlobalTheory.QuotInt.quotInt_unique_exists k n₁ (c + 1) 1 le_rfl
    (by omega) ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₁ m₁) G₁ f).1
  have uniq₂ := fun f => (_root_.GlobalTheory.QuotInt.quotInt_unique_exists k n₂ c 1 le_rfl
    (by omega) ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂) G₂ f).1
  have hinteg : ∀ Ψ Φb, _root_.GlobalTheory.PosOne.tIntOne ψ ν μ₂ ρ σ (T Ψ) F Φb =
      _root_.GlobalTheory.PosOne.tInt ψ ν μ₂ 1 σ (B₁ Ψ) F Φb := by
    intro Ψ Φb
    funext h
    simp only [_root_.GlobalTheory.PosOne.tIntOne, _root_.GlobalTheory.PosOne.tInt]
    exact (fourierJacobiAverage_app_toOne_comm ν σ ρ (T Ψ) (B₁ Ψ) (hB₁eq Ψ) _ _).symm
  have hinner : ∀ h Ψ, _root_.GlobalTheory.RootEx.IsQuotInt ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂)
      G₂ 1 (_root_.GlobalTheory.PosOne.tInt ψ ν μ₂ 1 σ (B₁ Ψ) F (_root_.GlobalTheory.SplitWeil.om μ₂ h 1 Φ₂.1))
      (B' Ψ (ρ₁ h Φ₂)) := by
    intro h Ψ
    have := hbone Ψ (ρ₁ h Φ₂)
    rwa [hρ₁ h Φ₂, ← hB'eq Ψ, hinteg Ψ] at this
  have hF' : ∀ j : L₁.J, ρ₁ (j : GL (n₁ ⊕ Fin (c + 1)) k) Φ₂ = (L₁.lam j : ℂ) • Φ₂ := by
    intro j
    apply Subtype.ext
    rw [hρ₁, Submodule.coe_smul]
    exact hΦ₂.1 j
  have houter := _root_.GlobalTheory.PosOneCell.quotInt_posOne k n₁ n₀ (c + 1) (by omega) ψ hψ hcond ν hν
    μ₁ hμ₁ m₁ G₁ L₁ hL₁ hG₁ b₁ _ ρ₁ hρ₁s B' hB' Φ₂ hF' Φ₁ hΦ₁ α T₁ hT₁
  have hinner_sum : ∀ γ ∈ T₁, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B' (_root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ) (ρ₁ γ Φ₂) = ∑ β ∈ T₂, (((m₂ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) * _root_.GlobalTheory.PosOne.toOne ν σ ρ (fun v => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app T (_root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ)) (_root_.GlobalTheory.StepData.xi ψ ν μ₂ Φ₂.1 L₂.J b₂ γ β) v) (σ β F) := by
    intro γ hγ
    by_cases hx : _root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ ∈ _root_.GlobalTheory.SplitWeil.SB _
    · rw [fourierJacobiAverage_app_of_mem_SB B' hx, fourierJacobiAverage_app_of_mem_SB T hx]
      have hi := _root_.GlobalTheory.PosOneCell.quotInt_posOne k n₂ n₁ c (by omega) ψ hψ hcond ν hν
        μ₂ hμ₂ m₂ G₂ L₂ hL₂ hG₂ b₂ A σ hσ (B₁ ⟨_, hx⟩) (hB₁ _) F hF Φ₂ hΦ₂.2 γ T₂ (hT₂ γ hγ)
      rw [uniq₂ _ _ _ (hinner γ ⟨_, hx⟩) hi]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [fourierJacobiAverage_app_toOne_comm ν σ ρ (T ⟨_, hx⟩) (B₁ ⟨_, hx⟩) (hB₁eq _)]
    · simp only [fourierJacobiAverage_app_of_not_mem_SB B' hx,
        fourierJacobiAverage_app_of_not_mem_SB T hx, fourierJacobiAverage_app_zero_map,
        LinearMap.zero_apply, posOne_toOne_zero, mul_zero,
        Finset.sum_const_zero]
  have hsum : ∀ S, _root_.GlobalTheory.RootEx.IsQuotInt ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₁ m₁) G₁ 1
      (_root_.GlobalTheory.PosOne.tInt ψ ν μ₁ 1 ρ₁ B' Φ₂ (_root_.GlobalTheory.SplitWeil.om μ₁ α 1 Φ₁.1)) S →
      S = ∑ γ ∈ T₁, ∑ β ∈ T₂, (((m₁ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₁.J γ))).toReal⁻¹ * (m₂ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) * _root_.GlobalTheory.PosOne.toOne ν σ ρ (fun v => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app T (_root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ)) (_root_.GlobalTheory.StepData.xi ψ ν μ₂ Φ₂.1 L₂.J b₂ γ β) v) (σ β F) := by
    intro S hS
    rw [uniq₁ _ _ _ hS houter]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [hinner_sum γ hγ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    push_cast
    ring
  have hf : ∀ w : GL (n₁ ⊕ Fin (c + 1)) k → _root_.GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k) →ₗ[ℂ] ℂ,
      (∀ h Ψ, w h Ψ = B' Ψ (ρ₁ h Φ₂)) →
      (fun h => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (w h) (_root_.GlobalTheory.RootEx.opE ψ ν 1
        (_root_.GlobalTheory.SplitWeil.om μ₁ 1 h (_root_.GlobalTheory.SplitWeil.om μ₁ α 1 Φ₁.1)))) =
      _root_.GlobalTheory.PosOne.tInt ψ ν μ₁ 1 ρ₁ B' Φ₂ (_root_.GlobalTheory.SplitWeil.om μ₁ α 1 Φ₁.1) := by
    intro w hw
    funext h
    simp only [_root_.GlobalTheory.PosOne.tInt, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app]
    split_ifs
    · exact hw _ _
    · rfl
  unfold _root_.GlobalTheory.PosOne.OneDbl
  constructor
  · rintro ⟨w, hw, hz⟩
    have hwv : ∀ h Ψ, w h Ψ = B' Ψ (ρ₁ h Φ₂) := by
      intro h Ψ
      have hwh := hw h Ψ
      rw [hinteg] at hwh
      exact uniq₂ _ _ _ hwh (hinner h Ψ)
    rw [hf w hwv] at hz
    exact hsum z hz
  · intro hz
    refine ⟨fun h => B'.flip (ρ₁ h Φ₂), fun h Ψ => ?_, ?_⟩
    · rw [hinteg]
      exact hinner h Ψ
    · rw [hf _ (fun h Ψ => rfl), hz, ← hsum _ houter]
      exact houter

end GlobalTheory.PosOne
end

