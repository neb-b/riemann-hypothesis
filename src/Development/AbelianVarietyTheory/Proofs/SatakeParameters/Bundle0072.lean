module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalRingCardinality.DataKerI
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0217
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.LocalRingCardinality.Lemmas

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyAt0PolDEquivariant
section
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.BasicNotions NumberField GlobalTheory.ThStr GlobalTheory.ThBe0 Classical

namespace GlobalTheory.ClassSumEquiv

open MvPolynomial

theorem polD_subst (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (FrV D N) ℂ)
    (y' γ' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (γ : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ τ, (γ' τ).det ≠ 0) :
    aeval (fun l : Idx D N N' => ∑ k, C ((γ' l.1)⁻¹ k l.2.1) * (X (l.1, k, l.2.2) : MvPolynomial (Idx D N N') ℂ))
      (aeval (fun l : Idx D N N' => ∑ k, C (γ l.1 l.2.2 k) * (X (l.1, l.2.1, k) : MvPolynomial (Idx D N N') ℂ))
        (polD D s Q (fun τ => γ' τ * y' τ))) =
      polD D s (aeval (fun k : FrV D N => ∑ a : Fin N, C (γ k.1 k.2.1 a) *
        (X (k.1, a, k.2.2) : MvPolynomial (FrV D N) ℂ)) Q) y' := by
  unfold polD
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun ⟨τ, a, k⟩ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  split_ifs with hk
  · have e : y' τ b' ⟨k, hk⟩ = ∑ b, (γ' τ)⁻¹ b' b * (γ' τ * y' τ) b ⟨k, hk⟩ := by
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul_cancel_left _ _ (h τ).isUnit]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul]
    ring
  · simp

theorem applyAt0_polD_equivariant : ∀ (D : D7) (N N' : ℕ) (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (FrV D N) ℂ) (y' γ' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (γ : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) (G : VC D N N' → ℂ), (∀ τ, (γ' τ).det ≠ 0) → Differentiable ℂ G → applyAt0 D (polD D s Q (fun τ => γ' τ * y' τ)) (fun z => G (fun τ => ((γ' τ)⁻¹ * Matrix.of (z τ) * γ τ : Matrix (Fin N') (Fin N) ℂ))) = applyAt0 D (polD D s (MvPolynomial.aeval (fun k : FrV D N => ∑ a : Fin N, MvPolynomial.C (γ k.1 k.2.1 a) * (MvPolynomial.X (k.1, a, k.2.2) : MvPolynomial (FrV D N) ℂ)) Q) y') G := by
  intro D N N' s Q y' γ' γ G h hG
  have hd : Differentiable ℂ (fun z => G (GlobalTheory.NormSum.Minor.mulL (fun τ => (γ' τ)⁻¹) z)) :=
    hG.comp (LinearMap.toContinuousLinearMap (GlobalTheory.NormSum.Minor.mulL (a := N) (fun τ => (γ' τ)⁻¹))).differentiable
  have h1 := GlobalTheory.NormSum.Minor.applyAt0_comp hd (GlobalTheory.NormSum.Minor.mulR γ) (fun l k => γ l.1 l.2.2 k)
    (fun l k => (l.1, l.2.1, k)) (GlobalTheory.NormSum.Minor.mulR_coordV γ) (polD D s Q (fun τ => γ' τ * y' τ))
  rw [GlobalTheory.NormSum.Minor.applyAt0_comp hG (GlobalTheory.NormSum.Minor.mulL (fun τ => (γ' τ)⁻¹))
    (fun l k => (γ' l.1)⁻¹ k l.2.1) (fun l k => (l.1, k, l.2.2)) (GlobalTheory.NormSum.Minor.mulL_coordV _),
    polD_subst D N N' s Q y' γ' γ h] at h1
  rw [← h1]
  simp only [Matrix.mul_assoc]
  rfl

end GlobalTheory.ClassSumEquiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BrEquivAll
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.BranchFormula

open Formalism.L2.Col.Br

theorem brEquiv_all : ∀ (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n), Br.BrEquiv K hN lam sg := by
  intro K _ _ ι _ N n hN lam sg hS g g' h G
  have hB : ∀ τ, IsBlock hN (g' τ : Matrix (Fin N) (Fin N) K) (g τ : Matrix (Fin n) (Fin n) K) 1 := h
  apply Subtype.ext
  have hd : detTwK lam g' = detTwK sg g := by
    rw [detTwK, detTwK]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [detPow, detPow, hS τ, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, (hB τ).det, mul_one]
  simp only [brStd, brStdP, LinearMap.comp_apply, Submodule.subtype_apply, rhoK_coe, LinearMap.smul_apply, actP, trAct,
    AlgHom.toLinearMap_apply, map_smul, Submodule.coe_smul]
  rw [coefLast_blockAct K ι hN _ _ _ (fun _ => 1) fun τ => (hB τ).transpose, map_smul, Submodule.coe_smul, projVV_blockAct]
  simp only [smul_smul, one_pow, Finset.prod_const_one, mul_one]
  rw [hd]
  congr 1
  ring

end GlobalTheory.BranchFormula
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresDoubleCosetAdjointCommute
section
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory

theorem classPres_dcOp_adjoint_commute : ∀ {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : ClassPres ι S σ ρ J χ) (L : Subgroup G) (x : G) (A A' B : Finset G) (T T' U : Module.End K S.Forms), (∀ γ u u', inner ℂ (ρ γ u) (ρ γ u') = inner ℂ u u') → (∀ k, ‖(χ k : ℂ)‖ = 1) → (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l) → (∀ k : J, (k : G) ∈ L → χ k = 1) → (∀ a ∈ A, a ∈ L) → (∀ a ∈ A', a ∈ L) → IsDC J x A → IsDC J x⁻¹ A' → (∀ f : S.Forms, P.ext ((T f : S.Forms) : S.Cl → S.V) = dcOp A (P.ext (f : S.Cl → S.V))) → (∀ f : S.Forms, P.ext ((T' f : S.Forms) : S.Cl → S.V) = dcOp A' (P.ext (f : S.Cl → S.V))) → (∀ f : S.Forms, P.ext ((U f : S.Forms) : S.Cl → S.V) = dcOp B (P.ext (f : S.Cl → S.V))) → (∀ f g : S.Forms, S.csum ((T f : S.Forms) : S.Cl → S.V) (g : S.Cl → S.V) = S.csum (f : S.Cl → S.V) ((T' g : S.Forms) : S.Cl → S.V)) ∧ ((∀ F ∈ AdForms ι ρ J χ, dcOp A (dcOp B F) = dcOp B (dcOp A F)) → Commute T U) := by
  intro G Γ W K _ _ _ _ _ _ _ ι S σ ρ J χ P L x A A' B T T' U hρ hχ hJ hχL hA hA' hx hx' hT hT' hU
  obtain ⟨hmem, hiso, -, -, hinj⟩ := classPres_basic ι S σ ρ J χ P
  refine ⟨fun f g => ?_, fun hc => ?_⟩
  · apply σ.injective
    rw [← hiso, ← hiso, hT, hT']
    exact _root_.GlobalTheory.adInner_dcOp_adjoint ι ρ J L χ P.y x A A' hρ hχ P.reps
      (fun c => Finite.of_equiv _ (P.stabI c).toEquiv) hJ hχL hA hA' hx hx' _ (hmem f) _ (hmem g)
  · refine LinearMap.ext fun f => hinj ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, P.extL_apply, P.extL_apply, hT, hU, hU, hT]
    exact hc _ (hmem f)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientFieldEnlargementLocChiCyclotomic
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem enl_locChi_epsU : ∀ {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw), (∀ z : ℚ_[D.nd.l i], C.inc (algebraMap _ _ z) = algebraMap _ _ z) → ∀ s, C.inc ((Br.locChi D.nbr i w hw (epsU D.nd i) s : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) = ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 s : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
  intro D i w hw C hC s
  rw [GlobalTheory.CycBridge.locChi_epsU D i w hw s]
  exact hC _

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompactSpaceMaximalCompactUnitaryInfinite
section
open GlobalTheory.CuspRep

namespace GlobalTheory.KinfCompactness

theorem norm_entry_le_one {E : Type} [Field E] {a : ℕ} {M : Matrix (Fin a) (Fin a) (Cinf E)}
    (hM : star M * M = 1) (i j : Fin a) (w : NumberField.InfinitePlace E) : ‖M i j w‖ ≤ 1 := by
  have h := congrFun (congrFun (congrFun hM j) j) w
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Finset.sum_apply, Pi.mul_apply,
    Pi.star_apply, Pi.one_apply, Complex.star_def, Complex.conj_mul'] at h
  have h2 : ∑ x, ‖M x j w‖ ^ 2 = 1 := by exact_mod_cast h
  have h3 : ‖M i j w‖ ^ 2 ≤ 1 :=
    h2 ▸ Finset.single_le_sum (f := fun x => ‖M x j w‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  nlinarith [norm_nonneg (M i j w)]

theorem isClosed_unitaryGroup (E : Type) [Field E] (a : ℕ) :
    IsClosed (Matrix.unitaryGroup (Fin a) (Cinf E) : Set (Matrix (Fin a) (Fin a) (Cinf E))) := by
  have e : (Matrix.unitaryGroup (Fin a) (Cinf E) : Set (Matrix (Fin a) (Fin a) (Cinf E))) =
      {M | star M * M = 1} := by
    ext M; exact Matrix.mem_unitaryGroup_iff'
  rw [e]
  exact isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const

theorem compactSpace_Kinf (E : Type) [Field E] (a : ℕ) : CompactSpace (Kinf E a) := by
  let B : Set (Matrix (Fin a) (Fin a) (Cinf E)) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) 1
  have hB : IsCompact B :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hsub : (Matrix.unitaryGroup (Fin a) (Cinf E) : Set (Matrix (Fin a) (Fin a) (Cinf E))) ⊆ B := by
    intro M hM i _ j _ w _
    simpa [Metric.mem_closedBall, dist_zero_right] using
      norm_entry_le_one (Matrix.mem_unitaryGroup_iff'.1 hM) i j w
  exact isCompact_iff_compactSpace.1 (hB.of_isClosed_subset (isClosed_unitaryGroup E a) hsub)

end GlobalTheory.KinfCompactness
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffJetLSubR
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.KFormCore

section Generic

variable {K : Type} [Field K] {σ σ' δ δ' : Type}

def jetL (J : (δ →₀ ℕ) → K) : MvPolynomial (σ ⊕ δ) K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials (σ ⊕ δ) K).constr K fun m =>
    monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (J (m.comapDomain Sum.inr Sum.inr_injective.injOn))

theorem jetL_monomial (J : (δ →₀ ℕ) → K) (m : σ ⊕ δ →₀ ℕ) (c : K) :
    jetL J (monomial m c) = monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
      (c * J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have h1 : (monomial m c : MvPolynomial (σ ⊕ δ) K) = c • basisMonomials (σ ⊕ δ) K m := by
    simp [smul_monomial]
  rw [h1, map_smul, jetL, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

end Generic

section Main

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem applyAt0_eq (l : ℕ) [Fact l.Prime] (a b : ℕ) (Th : MvPowerSeries (ι × Fin a × Fin b) ℂ_[l])
    (Q : MvPolynomial (KM.XZ ι a b) ℤ) :
    KM.applyAt0 a b l Th Q = jetL (fun m => (m.prod fun _ k => (k.factorial : ℂ_[l])) * MvPowerSeries.coeff m Th)
      (MvPolynomial.map (Int.castRingHom ℂ_[l]) Q) := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [Q.as_sum, map_sum, map_sum]
  unfold KM.applyAt0
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_monomial, jetL_monomial, mul_assoc]
  rfl

end Main

end GlobalTheory.KFormCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndSpannedOfIsIrrSubOfIsAlgClosed
section
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem endSpanned_of_isIrrSub_of_isAlgClosed :
    ∀ {Γ E : Type} [Group Γ] [Field E] [IsAlgClosed E] {a : ℕ} (σ : Γ →* GL (Fin a) E)
      (U : Submodule E (Fin a → E)), IsIrrSub σ U → EndSpanned σ U := by
  intro Γ E _ _ _ a σ U h
  classical
  have hinv : ∀ g, ∀ v ∈ U, (Matrix.toLin' ((σ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)) v ∈ U :=
    fun g v hv => by rw [Matrix.toLin'_apply]; exact h.2.1 g v hv
  let r : Representation E Γ U :=
    { toFun := fun g => (Matrix.toLin' ((σ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)).restrict (hinv g)
      map_one' := by
        ext v i
        simp [LinearMap.restrict_apply]
      map_mul' := fun g g' => by
        ext v i
        simp [LinearMap.restrict_apply, Matrix.mulVec_mulVec] }
  have hr : ∀ g (v : U), ((r g v : U) : Fin a → E) = ((σ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).mulVec v :=
    fun g v => by simp [r, LinearMap.restrict_apply]
  have hirr : r.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation r) := by
      refine ⟨⊥, ⊤, fun hbt => h.1 ?_⟩
      have h2 := congrArg Subrepresentation.toSubmodule hbt
      change (⊥ : Submodule E U) = ⊤ at h2
      rw [eq_bot_iff]
      intro v hv
      have : (⟨v, hv⟩ : U) ∈ (⊥ : Submodule E U) := by rw [h2]; trivial
      rw [Submodule.mem_bot] at this
      simpa using congrArg Subtype.val this
    refine ⟨fun W => ?_⟩
    have hle : W.toSubmodule.map U.subtype ≤ U := by
      rintro _ ⟨v, _, rfl⟩; exact v.2
    have hinvW : IsInv σ (W.toSubmodule.map U.subtype) := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨r g v, W.apply_mem_toSubmodule g hv, ?_⟩
      simp [hr]
    rcases h.2.2 _ hle hinvW with h1 | h1
    · left
      refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv => ?_)
      have : (v : Fin a → E) ∈ W.toSubmodule.map U.subtype := ⟨v, hv, rfl⟩
      rw [h1, Submodule.mem_bot] at this
      show v ∈ (⊥ : Submodule E U)
      rw [Submodule.mem_bot]; exact Subtype.ext this
    · right
      refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun v _ => ?_)
      have : (v : Fin a → E) ∈ W.toSubmodule.map U.subtype := by rw [h1]; exact v.2
      obtain ⟨w, hw, hwv⟩ := this
      rwa [show w = v from Subtype.ext hwv] at hw
  have hs := GlobalTheory.BurnsideField.span_range_eq_top_of_isAlgClosed r hirr
  intro φ
  have hφ : φ ∈ Submodule.span E (Set.range r) := by rw [hs]; trivial
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact ⟨_, Submodule.subset_span ⟨g, rfl⟩, fun w => (hr g w).symm⟩
  | zero => exact ⟨0, Submodule.zero_mem _, fun w => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX, hXw⟩ := hx
    obtain ⟨Y, hY, hYw⟩ := hy
    exact ⟨X + Y, Submodule.add_mem _ hX hY, fun w => by rw [Matrix.add_mulVec, hXw, hYw]; simp⟩
  | smul c x _ hx =>
    obtain ⟨X, hX, hXw⟩ := hx
    exact ⟨c • X, Submodule.smul_mem _ c hX, fun w => by rw [Matrix.smul_mulVec, hXw]; simp⟩

end GlobalTheory.SplitField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalTranslationCompCommutingOperator
section
open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.LocFactor

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem glAf_ext {x y : GL (Fin a) (Af E)}
    (h : ∀ v : HeightOneSpectrum (𝓞 E), GeneralLinearGroup.map (pLoc E v) x = GeneralLinearGroup.map (pLoc E v) y) :
    x = y := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun v => ?_)
  have := congrArg (fun m : GL (Fin a) (v.adicCompletion E) => (m.val : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) (h v)
  exact this

theorem locGL_comm_away (w : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E))
    (h : GL (Fin a) (w.adicCompletion E)) :
    locGL E a w h * ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) =
      ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) * locGL E a w h := by
  refine glAf_ext fun v => ?_
  simp only [map_mul, map_inv]
  by_cases hv : v = w
  · subst hv
    rw [pLoc_locGL, pLoc_locGL, inv_mul_cancel, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hv, pLoc_locGL_of_ne hv, inv_one, one_mul, one_mul, mul_one]

theorem op_eq_locRep_comp (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (o : Op E a) :
    ∃ (g : GL (Fin a) (w.adicCompletion E)) (T : Module.End ℂ π.V),
      (∀ h, T ∘ₗ π.locRep w h = π.locRep w h ∘ₗ T) ∧ π.op o = π.locRep w g ∘ₗ T := by
  cases o with
  | fin k =>
    set kw := GeneralLinearGroup.map (pLoc E w) k
    set k' := (locGL E a w kw)⁻¹ * k
    refine ⟨kw, π.op (.fin k'), fun h => ?_, ?_⟩
    · refine LinearMap.ext fun φ => Subtype.ext ?_
      change rt E a (finGL E a k') (rt E a (finGL E a (locGL E a w h)) φ.1) =
        rt E a (finGL E a (locGL E a w h)) (rt E a (finGL E a k') φ.1)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
        locGL_comm_away]
    · refine LinearMap.ext fun φ => Subtype.ext ?_
      change rt E a (finGL E a k) φ.1 = rt E a (finGL E a (locGL E a w kw)) (rt E a (finGL E a k') φ.1)
      rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel_left]
  | cpt k =>
    refine ⟨1, π.op (.cpt k), fun h => ?_, ?_⟩
    · refine LinearMap.ext fun φ => Subtype.ext ?_
      change rt E a (infGL E a (Unitary.toUnits k)) (rt E a (finGL E a (locGL E a w h)) φ.1) =
        rt E a (finGL E a (locGL E a w h)) (rt E a (infGL E a (Unitary.toUnits k)) φ.1)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, infGL_comm]
    · rw [map_one]; rfl
  | lie X =>
    refine ⟨1, π.op (.lie X), fun h => ?_, ?_⟩
    · refine LinearMap.ext fun φ => Subtype.ext ?_
      change lie E a X (rt E a (finGL E a (locGL E a w h)) φ.1) =
        rt E a (finGL E a (locGL E a w h)) (lie E a X φ.1)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, lie_rt_fin]
    · rw [map_one]; rfl

theorem exists_locRep_comp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (o : GlobalTheory.CuspRep.Op E a), ∃ (g : GL (Fin a) (w.adicCompletion E))
    (T : Module.End ℂ π.V), (∀ h, T ∘ₗ π.locRep w h = π.locRep w h ∘ₗ T) ∧ π.op o = π.locRep w g ∘ₗ T :=
  fun _ _ _ _ _ π w o => op_eq_locRep_comp π w o

end GlobalTheory.LocFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeSplitOneOfCharTied
section
namespace GlobalTheory.RowClose

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain


open Polynomial NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.RowClose.heckeSplitOne_of_charTied : ∀ (D : _root_.Formalism.BasicNotions.D7) (C : _root_.Formalism.L2.Host.CharFrame D)
    (nch : _root_.Formalism.BasicNotions.NChoice D) (Tp : _root_.Formalism.L2.Host.TupTied D C nch), _root_.Formalism.L2.Host.NCharTied D C nch Tp →
    _root_.GlobalTheory.RowCopy.HeckeSplitOne D := by
  intro D C nch Tp T
  have h := _root_.GlobalTheory.HeckeSplitRow.heckeSplitOne_of_tie D.nd D.naut
    (_root_.GlobalTheory.HeckeSplitRow.heckeCharTie_of_tied T)
  unfold _root_.GlobalTheory.ThetaExh.HeckeSplitOne at h
  exact h

end GlobalTheory.RowClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeValuationBound
section
noncomputable section

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

namespace GlobalTheory.Proof.LatticeValuationBound

section Chain

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}

theorem exists_chain (M : MemberForms LL embLL Pl Tau hc C A P) {p : ℕ} {G : GAtP p} {Fl : Fills G} {Lv : Levels Fl}
    (Ch : Chain Lv) (σ : LL →+* G.Kf) (cmp : ∀ j, (M.lat j).V →ₛₗ[σ] Lv.Fm j)
    (hK : ∀ j, j < R.m → ∀ (x : (M.lat j).V) (y : (M.lat (j + 1)).V),
      M.emb (j + 1) y = C.K j (M.emb j x) → cmp (j + 1) y = Ch.Kz j (cmp j x))
    (hrat : ∀ j, j < R.m → M.KRat j) (x : (M.lat 0).V) (j : ℕ) (hj : j ≤ R.m) :
    ∃ y : (M.lat j).V, M.emb j y = Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap j (M.emb 0 x) ∧ cmp j y = Ch.chainK j (cmp 0 x) := by
  induction j with
  | zero => exact ⟨x, rfl, rfl⟩
  | succ j ih =>
    obtain ⟨y, hy, hy'⟩ := ih (by omega)
    obtain ⟨z, hz⟩ := hrat j (by omega) y
    refine ⟨z, ?_, ?_⟩
    · rw [hz, hy]; rfl
    · rw [hK j (by omega) y z hz, hy']; rfl

end Chain

variable {D : D7}

theorem col_heq {R : Ranks} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C C' : ColumnChain R Tau hc}
    (h : C = C') {φ : C.cls 0 → C.Y 0 → ℂ} {φ' : C'.cls 0 → C'.Y 0 → ℂ} (hφ : HEq φ φ') :
    HEq (C.col φ) (C'.col φ') := by
  subst h
  rw [eq_of_heq hφ]

theorem VGe_symm {w : D.what₂.places.Pl} (A B : HLat D.what₂.LL) (e : A.V ≃ₗ[D.what₂.LL] B.V)
    (he : ∀ x, x ∈ A.L ↔ e x ∈ B.L) {y : B.V} {s : ℝ} (h : VGe D w B.L y s) : VGe D w A.L (e.symm y) s := by
  obtain ⟨a, z, hz, rfl, ha⟩ := h
  refine ⟨a, e.symm z, ?_, map_smul _ _ _, ha⟩
  obtain ⟨t, ht, hz⟩ := (D.mem_locW_iff w _ _).1 hz
  refine (D.mem_locW_iff w _ _).2 ⟨t, ht, (he _).2 ?_⟩
  rw [← algebraMap_smul D.what₂.LL t, map_smul, LinearEquiv.apply_symm_apply, algebraMap_smul]
  exact hz

end GlobalTheory.Proof.LatticeValuationBound

end
end

