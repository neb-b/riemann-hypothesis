module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0614
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumFinitePairVacuumAlgebraicCombination
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingJointDataTwistRatioAtDetRoots
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConTwist

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem commGroup_mul_eq_mul_mul_div {C : Type} [CommGroup C] (a b b' : C) : a * b' = a * b * (b' * b⁻¹) := by
  rw [mul_assoc, mul_comm b' b⁻¹, mul_inv_cancel_left]

theorem commGroup_mul_mul_eq_mul_mul_div {C : Type} [CommGroup C] (a b b' e : C) : a * b' * e = a * b * e * (b' * b⁻¹) := by
  rw [commGroup_mul_eq_mul_mul_div a b b', mul_right_comm]

theorem chrS_mu (t t' : T) (i j : ℕ) :
    G.chrS (.mu t' i j) = G.chrS (.mu t i j) * (L.xi t' * (L.xi t)⁻¹) := by
  simp only [GridData.chrS, GridData.chr, LevCh.mu, Lift.tup, Lift.attChr]
  split_ifs
  · exact commGroup_mul_mul_eq_mul_mul_div _ _ _ _
  · exact commGroup_mul_eq_mul_mul_div _ _ _

theorem chrT_mu (t t' : T) (i j : ℕ) :
    G.chrT (.mu t' i j) = G.chrT (.mu t i j) * (L.xi t' * (L.xi t)⁻¹) := by
  simp only [GridData.chrT, GridData.chr, LevCh.mu, Lift.tup, Lift.attChr]
  split_ifs
  · exact commGroup_mul_mul_eq_mul_mul_div _ _ _ _
  · exact commGroup_mul_eq_mul_mul_div _ _ _

end GlobalTheory.ConTwist

namespace GlobalTheory.ConTwist

open GlobalTheory.RowChain GlobalTheory.Unf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem isDetRoot_one {V V' : HSp D} {y : (AE D)ˣ} (hy : IsDetRoot V 1 y) : IsDetRoot V' 1 y := by
  simp only [IsDetRoot, map_one, Units.val_one, Matrix.det_one, one_mul] at hy ⊢
  exact hy

theorem contr_smul_right {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (c : ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) :
    contr l S vL f₁ (c • f₂) = c • contr l S vL f₁ f₂ := by
  funext u v
  simp only [contr, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem contr_smul_left {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (c : ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) :
    contr l S vL (c • f₁) f₂ = c • contr l S vL f₁ f₂ := by
  funext u v
  simp only [contr, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem lastBi_smul {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (c : ℂ) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) :
    GlobalTheory.FinPl.lastBi o o'' τ (c • Ξ) Φ₂ = c • GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ := by
  funext u v
  simp only [GlobalTheory.FinPl.lastBi, OrthDec.boxT, Pi.smul_apply, smul_eq_mul]
  ring

theorem om_mu_twist (W : G.Weil) (t t' : T) (k : ℕ) (hk : k + 1 ≤ D.R.m) {a : GA D (G.V (.grid D.R.m k))}
    {b : GA D (G.V (.grid D.R.m (k + 1)))} {y y' : (AE D)ˣ} (hy : IsDetRoot _ a y) (hy' : IsDetRoot _ b y')
    {f : WO (G.V (.grid D.R.m k)) (G.V (.grid D.R.m (k + 1))) → ℂ} (hf : IsThetaFunO W.ψ _ _ f) :
    W.om (.mu t' D.R.m k) (a, b) f =
      ((((L.xi t' * (L.xi t)⁻¹) y)⁻¹ * (L.xi t' * (L.xi t)⁻¹) y' : Circle) : ℂ) • W.om (.mu t D.R.m k) (a, b) f := by
  have h0 := W.om_is (.mu t D.R.m k) ⟨le_rfl, hk⟩
  have h1 := W.om_is (.mu t' D.R.m k) ⟨le_rfl, hk⟩
  rw [chrS_mu t t', chrT_mu t t'] at h1
  exact GlobalTheory.TupRoot.twist_eq h0 h1 hy hy' hf

theorem fock_theta (W : G.Weil) (ρ : RealMatch W) (t : T) (P : PolDown G) (k : ℕ) (hk : k < D.R.m) :
    IsThetaFunO W.ψ (G.V (.grid D.R.m k)) (G.V (.grid D.R.m (k + 1)))
      (fockD W t (fun j => ρ.vT D.R.m j) P ⟨k, hk⟩) :=
  GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ (ρ.vT_is t D.R.m k le_rfl hk).2.theta _

end GlobalTheory.ConTwist

namespace GlobalTheory.ConTwist

open GlobalTheory.RowChain GlobalTheory.Unf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem contr_flat_twist {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)}
    {B' : BesLev D σ} (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ)
    (vL : VolM D B'.L.rank J.W₀.rank) (X : WO B.V J.W → ℂ) (Y : WO J.W B'.V → ℂ) (c₁ c₂ : ℂ) :
    contr l J.W₀ vL (flatBF s₁ (c₁ • X)) (flatFB s₂ (c₂ • Y)) =
      (c₁ * c₂) • contr l J.W₀ vL (flatBF s₁ X) (flatFB s₂ Y) := by
  rw [GlobalTheory.HandHom.flatBF_smul, GlobalTheory.HandHom.flatFB_smul, contr_smul_left, contr_smul_right, smul_smul, mul_comm]

theorem lastDat_twist (W : G.Weil) {t t' : T} {M M' : Vol G} (hM : M.Is t) (hM' : M'.Is t') (j : ℕ)
    (hj : j + 2 * 0 + 2 = D.R.m) (vN : VolN (besDecAt G j 0 hj)) (g : GA D (G.V (.grid D.R.m j)))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) (c : ℂ)
    (he : W.om (.mu t' D.R.m j) (g, 1) Φ₁ = c • W.om (.mu t D.R.m j) (g, 1) Φ₁) :
    lastDat W hM' j hj vN g Φ₁ Φ₂ = c • lastDat W hM j hj vN g Φ₁ Φ₂ := by
  have k1 := congrArg (flatBF (lastAt G W t' hM' j hj vN).s) he
  have k2 := GlobalTheory.HandHom.flatBF_smul (lastAt G W t' hM' j hj vN).s c (W.om (.mu t D.R.m j) (g, 1) Φ₁)
  have k := k1.trans k2
  unfold lastDat
  erw [k]
  erw [lastBi_smul]
  rfl

theorem conAt_twist (W : G.Weil) (ρ : RealMatch W) (t t' : T) (M M' : Vol G) (hM : M.Is t) (hM' : M'.Is t')
    (P : PolDown G) (h : Pts G) (x : ℕ → (AE D)ˣ) (hx : ∀ k, IsDetRoot _ (h k) (x k)) (hm : h D.R.m = 1) (j : ℕ)
    (hjm : j < D.R.m) :
    conAt W hM' (fockD W t' (fun j => ρ.vT D.R.m j) P) h j =
      ((((L.xi t' * (L.xi t)⁻¹) (x j))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 2)) : Circle) : ℂ) •
        conAt W hM (fockD W t (fun j => ρ.vT D.R.m j) P) h j := by
  by_cases h0 : j + 2 * 0 + 2 = D.R.m
  · simp only [conAt, h0, ↓reduceDIte]
    have hr : IsDetRoot (G.V (.grid D.R.m (j + 1))) 1 (x D.R.m) := isDetRoot_one (hm ▸ hx D.R.m)
    exact lastDat_twist W hM hM' j h0 _ _ _ _ _
      (om_mu_twist W t t' j (by omega) (hx j) hr (fock_theta W ρ t' P j (by omega)))
  by_cases h1 : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m
  · simp only [conAt, h0, h1, ↓reduceDIte]
    have e1 := om_mu_twist W t t' j (by omega) (hx j) (hx (j + 1)) (fock_theta W ρ t' P j (by omega))
    have e2 : W.om (.mu t' D.R.m (j + 1)) (h (j + 1), h (j + 1 + 1)) (fockD W t' (fun j => ρ.vT D.R.m j) P ⟨j + 1, by omega⟩) =
        ((((L.xi t' * (L.xi t)⁻¹) (x (j + 1)))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 2)) : Circle) : ℂ) •
          W.om (.mu t D.R.m (j + 1)) (h (j + 1), h (j + 1 + 1)) (fockD W t' (fun j => ρ.vT D.R.m j) P ⟨j + 1, by omega⟩) :=
      om_mu_twist W t t' (j + 1) (by omega) (hx (j + 1)) (hx (j + 2)) (fock_theta W ρ t' P (j + 1) (by omega))
    erw [e1, e2]
    refine (contr_flat_twist (J := jacAt G hM' (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega)) _ _ _ _ _ _ _ _).trans ?_
    rw [← Circle.coe_mul]
    have hc : ((L.xi t' * (L.xi t)⁻¹) (x j))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 1)) *
        (((L.xi t' * (L.xi t)⁻¹) (x (j + 1)))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 2))) =
        ((L.xi t' * (L.xi t)⁻¹) (x j))⁻¹ * (L.xi t' * (L.xi t)⁻¹) (x (j + 2)) := by
      group
    rw [hc]
    rfl
  · simp only [conAt, h0, h1, ↓reduceDIte, smul_zero]

end GlobalTheory.ConTwist

namespace GlobalTheory.ConTwist

theorem conAt_twist_big : Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t t' : T) (M M' : Vol ch.G) (hM : M.Is t) (hM' : M'.Is t') (P : PolDown ch.G) (h : Pts ch.G) (x : ℕ → (AE D)ˣ), (∀ k, IsDetRoot _ (h k) (x k)) → h D.R.m = 1 → ∀ j, Even j → j < D.R.m → conAt ch.W hM' (fockD ch.W t' (fun j => ch.rm.vT D.R.m j) P) h j = ((((R.toLevCh.xi t' * (R.toLevCh.xi t)⁻¹) (x j))⁻¹ * (R.toLevCh.xi t' * (R.toLevCh.xi t)⁻¹) (x (j + 2)) : Circle) : ℂ) • conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) h j := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ t t' M M' hM hM' P h x hx hm j _ hjm
  exact conAt_twist ch.W ch.rm t t' M M' hM hM' P h x hx hm j hjm

end GlobalTheory.ConTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentPeriodValueLipschitzRealOneParameter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepPer.LipValue

theorem lip_value : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S') (M : DSModel V S) (p : Pack M₀ M) (Q : ℝ), p.Is θ d Q → ∀ (J : Set (GA D Y)) (χ : GA D Y → ℂ), ∀ t ∈ MultT θ M₀ J χ, ∀ b : ℝ, (∀ x, ‖t (PiTensorProduct.tprod ℂ p.w) x‖ ≤ b) → Lip θ p.A (t (PiTensorProduct.tprod ℂ p.w)) (Real.exp Q * b) := by
  intro hCusp D θ hθ Y V d S S' M₀ M p Q hp J χ t ht b hb
  obtain ⟨hLC, hSC, hT2, hB, hTG, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D Y
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB; haveI := hTG
  haveI : LocallyCompactSpace (GinfC Y) := (GlobalTheory.AdelicSplit.isClosed_GinfC' Y).locallyCompactSpace
  obtain ⟨c, hc⟩ := hp.2 (Measure.haar : Measure (GinfC Y)) inferInstance
  set m : Measure (GinfC Y) := Measure.haar with hm
  set φ : GA D Y → ℂ := t (PiTensorProduct.tprod ℂ p.w) with hφ
  set α : GinfC Y → ℂ := fun h => coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (h : GA D Y)) with hα
  have hαi : Integrable α m := by simpa only [one_mul] using (hc.far 1).1
  have hrep := _root_.GlobalTheory.ValAct.integral_mul_multT_eq hCusp D θ hθ Y S' M₀ J χ t ht p.w m inferInstance α c hαi hc.act

  have hT := (mem_multT θ M₀ J χ t).1 ht
  have hcont : Continuous φ := by
    have key : ∀ T ∈ Mult θ M₀ J χ, Continuous (T p.w) := by
      intro T hT'
      induction hT' using Submodule.span_induction with
      | mem T h => exact (h.aut p.w).cont
      | zero => exact continuous_const
      | add T T' _ _ h h' => exact h.add h'
      | smul a T _ h => exact h.const_smul a
    have := key _ hT
    simpa [PiTensorProduct.lift_symm] using this
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 1)
  intro x τ X hX s
  let k : GinfC Y := ⟨oneP θ Y τ X s, GlobalTheory.PointAtPlaceHom.atTau_mem Y τ _⟩
  have hkinv : ((k⁻¹ : GinfC Y) : GA D Y) = oneP θ Y τ X (-s) := by
    show (oneP θ Y τ X s)⁻¹ = _
    exact inv_eq_of_mul_eq_one_right (by
      rw [← GlobalTheory.Mem.Lift.oneP_add hθ hX, add_neg_cancel, GlobalTheory.Mem.Lift.oneP_zero hθ])
  have hmeas : ∀ y : GA D Y, AEStronglyMeasurable (fun h : GinfC Y => φ (y * h)) m := fun y =>
    (hcont.comp (continuous_const.mul continuous_subtype_val)).aestronglyMeasurable
  have hbd : ∀ y : GA D Y, ∀ᵐ (h : GinfC Y) ∂m, ‖φ (y * h)‖ ≤ b := fun y => Filter.Eventually.of_forall fun h => hb _
  have hαk : Integrable (fun h => α (k⁻¹ * h)) m := hαi.comp_mul_left k⁻¹
  have hI1 : Integrable (fun h => α (k⁻¹ * h) * φ (x * h)) m := hαk.mul_bdd (hmeas x) (hbd x)
  have hI0 : Integrable (fun h => α h * φ (x * h)) m := hαi.mul_bdd (hmeas x) (hbd x)
  have h1 : c * φ (x * k) = ∫ h, α (k⁻¹ * h) * φ (x * h) ∂m := by
    rw [← hrep (x * k)]
    have := integral_mul_left_eq_self (μ := m) (fun h => α (k⁻¹ * h) * φ (x * h)) k
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    show α h * φ (x * ↑k * ↑h) = α (k⁻¹ * (k * h)) * φ (x * ↑(k * h))
    rw [inv_mul_cancel_left, Subgroup.coe_mul, mul_assoc]
  have hdiff : c * (φ (x * k) - φ x) = ∫ h, (α (k⁻¹ * h) - α h) * φ (x * h) ∂m := by
    rw [mul_sub, h1, ← hrep x, ← integral_sub hI1 hI0]
    congr 1
    funext h
    ring
  have hlip := hc.lip τ X hX (-s)
  have hlip' : ∫ h, ‖α (k⁻¹ * h) - α h‖ ∂m ≤ Real.exp Q * ‖c‖ * |s| * hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹) := by
    have e : (fun h : GinfC Y => ‖α (k⁻¹ * h) - α h‖) = fun h : GinfC Y =>
        ‖coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d (oneP θ Y τ X (-s) * h)) - coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d h)‖ := by
      funext h
      simp only [hα, Subgroup.coe_mul, hkinv]
    rw [e]
    simpa only [abs_neg] using hlip
  have hint : Integrable (fun h => ‖α (k⁻¹ * h) - α h‖) m := (hαk.sub hαi).norm
  have hnorm : ‖c‖ * ‖φ (x * k) - φ x‖ ≤ (∫ h, ‖α (k⁻¹ * h) - α h‖ ∂m) * b := by
    rw [← norm_mul, hdiff, ← integral_mul_const]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun h => norm_nonneg _) (hint.mul_const b) (Filter.Eventually.of_forall fun h => ?_))
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc.ne
  have hH : 0 ≤ hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹) := Real.sqrt_nonneg _
  have key : ‖c‖ * ‖φ (x * k) - φ x‖ ≤ ‖c‖ * (Real.exp Q * b * |s| * hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹)) := by
    refine hnorm.trans ?_
    calc (∫ h, ‖α (k⁻¹ * h) - α h‖ ∂m) * b
        ≤ (Real.exp Q * ‖c‖ * |s| * hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹)) * b := mul_le_mul_of_nonneg_right hlip' hb0
      _ = ‖c‖ * (Real.exp Q * b * |s| * hsn (p.A.fr τ * X * (p.A.fr τ)⁻¹)) := by ring
  exact le_of_mul_le_mul_left key hc0

end GlobalTheory.SepPer.LipValue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionMovesStandardVacuumTopNodeEqCharSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.TopLevelInv


open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove in
theorem vac_high_law (hA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))), 1) (S.Z.vac (.top t (j + 1))) = S.Z.vac (.top t (j + 1))) (hC1 : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) = 1) (hC2 : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    ((L.mu t (j + 1 + 1) (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ)) : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) Tm →
      W.om (.top t (j + 1)) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        (∏ w : locPl G t, ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)))⁻¹ : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he Tm hTm
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hee : e * e = e := ho.idem
  have hce : e * cA D e = 0 := he.2
  have hf := idem_conj_sum hee hce
  have hW := W.om_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)
  have hvac := S.Z.vac_is (.top t (j + 1)) (show j + 1 + 1 ≤ D.R.m by omega)
  have hS := GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on (.top (j + 1)) (show j + 1 ≤ D.R.m by omega))
  have hT := GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on (.top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega))
  set g : GA D (G.V (.top (j + 1))) := ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) with hgdef
  have key := GlobalTheory.SplitLinear.splitLinearModel D W.ψ _ _ _ _ _ hW _ _ hS hT (locPl G t) e he _ hvac.2.theta hvac.2.lat 1
    one_ne_zero Tm hTm (cutPart (e + cA D e) _ g) 1 (suppAt_cutPart hee hce _ g) (GlobalTheory.SplitLinear.suppAt_one e _) _ _
    (GlobalTheory.VecInv.isDetAt_detAt e hee _ _) (GlobalTheory.VecInv.isDetAt_detAt e hee _ _) _ (GlobalTheory.isSBHalf_halfInd e _)
  have hvacTm : Tm (halfInd e (stdLatO S (.top t (j + 1)))) = S.Z.vac (.top t (j + 1)) := by
    have := hTm.vac
    rwa [one_smul] at this
  have hr1 : Even (G.V (.top (j + 1 + 1))).rank := by
    rw [GlobalTheory.FunObj.rank_top G (j := j + 1 + 1) (by omega)]; exact GlobalTheory.FunObj.rankX_even D (j + 1 + 1)
  have hr0 : Even (G.V (.top (j + 1))).rank := by
    rw [GlobalTheory.FunObj.rank_top G (j := j + 1) (by omega)]; exact GlobalTheory.FunObj.rankX_even D (j + 1)
  have hTc : G.chrT (.top t (j + 1)) = L.mu t (j + 1 + 1) := by
    simp only [GridData.chrT, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pT, Nat.not_odd_iff_even.2 hr1, if_false]
  have hc : ((splitFacO (G.chrS (.top t (j + 1) : Pair T)) (G.chrT (.top t (j + 1) : Pair T))
      (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g))
      (GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1) : ℂ) *
    (GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T))
      (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g))
      (GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1) : ℂ)) =
      ∏ w : locPl G t, ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)))⁻¹ : ℂˣ) : ℂ) := by
    have h1 : GlobalTheory.VecInv.detAt e hee (G.pT (.top t (j + 1) : Pair T)) 1 = 1 := map_one _
    have h2 := hC1 S hL ht j hj k hk e he
    have h3 := hC2 S hL ht j hj k hk e he
    rw [h1, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac, h2, hTc]
    simp only [splitFacO, map_one, mul_one, Real.one_rpow, Complex.ofReal_one, Circle.coe_inv]
    have h4 : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D 1 = 1 := by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
    simp only [h4, Real.one_rpow, mul_one, Complex.ofReal_one]
    have h5 : ((L.mu t (j + 1 + 1) (GlobalTheory.VecInv.detAt e hee (G.pS (.top t (j + 1) : Pair T)) (cutPart (e + cA D e) _ g)) : Circle) : ℂ) =
        ∏ w : locPl G t, (((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ) := h3
    rw [h5, ← Finset.prod_inv_distrib]
    simp only [Units.val_inv_eq_inv_val]
  calc W.om (.top t (j + 1)) (g, 1) (S.Z.vac (.top t (j + 1)))
      = W.om (.top t (j + 1)) (cutPart (e + cA D e) _ g, 1)
          (W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) _ g, 1) (S.Z.vac (.top t (j + 1)))) := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, ← cutPart_mul hf]
    _ = W.om (.top t (j + 1)) (cutPart (e + cA D e) _ g, 1) (S.Z.vac (.top t (j + 1))) := by
        rw [hA S hL ht j hj k hk e he]
    _ = _ := by
        rw [← hvacTm]
        erw [key]
        rw [← hc]
        conv_rhs => rw [← map_smul]
        congr 1
        funext x
        rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.SplitLinear.subst_eq, halfInd_cutPart hee hce]
        rfl

theorem vac_move_high_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t (j + 1))) 1 (S.Z.vac (.top t (j + 1))) Tm →
      W.om (.top t (j + 1)) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))), 1) (S.Z.vac (.top t (j + 1))) =
        (∏ w : locPl G t, ((((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)))⁻¹ : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t (j + 1))) (actO _ _ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ x) :=
  vac_high_law (by intros; apply _root_.GlobalTheory.OffPartVac.offPart_fixes_vac <;> assumption) (by intros; apply _root_.GlobalTheory.DetIdeleUnit.absFin_detAt_conj_eq_one <;> assumption)
    (by intros; apply _root_.GlobalTheory.TopLevelInv.mu_detAt_eq_prod_loc <;> assumption)

end GlobalTheory.TopLevelInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumFinitePairVacuumAlgebraicCombinationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_finite_pair_vacuum_algebraic_combination : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → IsWeilDatumO ψ S T χS χT om →
    ∀ x ∈ GfC S, ∀ h ∈ GfC T, ∃ (κ : ℂ) (F : WO S T → ℂ), GlobalTheory.MovedAlg.IsAlgComb ψ S T v F ∧ om (x, h) v = κ • F := by
  first | exact @GlobalTheory.FinWeilAlg.om_vac_algComb | exact GlobalTheory.FinWeilAlg.om_vac_algComb | (intros; apply GlobalTheory.FinWeilAlg.om_vac_algComb <;> assumption)
end

