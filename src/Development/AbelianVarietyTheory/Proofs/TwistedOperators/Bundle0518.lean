module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0856
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelIsometryHalfLatticeVolumeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0341
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOPerm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowKer

variable {D : D7}

theorem unitMap_perm {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ) (σ : Equiv.Perm (Fin n))
    (σ' : Equiv.Perm (Fin m)) (i : Fin m) (j : Fin n) :
    unitMap (B.submatrix id σ) (B'.submatrix id σ') i j = unitMap B B' (σ' i) (σ j) := by
  unfold unitMap
  have h : (B.submatrix id σ)⁻¹ = B⁻¹.submatrix σ id := by
    simpa using Matrix.inv_submatrix_equiv B (Equiv.refl _) σ
  rw [h]
  ext a b
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]

theorem pureTensorO_perm {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (σS : D.what₂.Tau → Equiv.Perm (Fin S.rank)) (σT : D.what₂.Tau → Equiv.Perm (Fin T.rank))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (Q : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT (fun τ => (BS τ).submatrix id (σS τ)) (fun τ => (BT τ).submatrix id (σT τ)) f
        (MvPolynomial.rename (fun k : FVar D T.rank S.rank => (k.1, (σT k.1).symm k.2.1, (σS k.1).symm k.2.2)) Q) =
      pureTensorO ψ θ S T sS sT BS BT f Q := by
  unfold pureTensorO
  refine GlobalTheory.ArchRec.LieAtPlace.pure_rename (fun v Q => ?_) (fun v Q => ?_) _ (fun k => ?_) Q
  · refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  · refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  · obtain ⟨τ, i, j⟩ := k
    simp only [aPlusAll, unitMap_perm, Equiv.apply_symm_apply]

open GlobalTheory.GridJoin

theorem heq_ker {V1 V0 U1 U0 : HSp D} (h1 : SameSp V1 U1) (h0 : SameSp V0 U0) (ω : GlobalTheory.Grid.WRep U1 U0)
    (om : GA D (negSp V1) × GA D V0 →* Module.End ℂ (WO (negSp V1) V0 → ℂ)) (hom : HEq (ω.toSgn true) om)
    (F : WO U1 U0 → ℂ) (F' : WO (negSp V1) V0 → ℂ) (hF : HEq F F') :
    HEq (fun (h : GA D U1) (g : GA D U0) => thetaKO ω h g F)
      (fun (h : GA D V1) (g : GA D V0) => thetaKO om (negGA V1 h) g F') := by
  obtain ⟨L, a, b, rfl⟩ := h1
  obtain ⟨L', a', b', rfl⟩ := h0
  cases hom
  cases hF
  rfl

theorem heq_fock {V1 V0 U1 U0 : HSp D} (h1 : SameSp V1 U1) (h0 : SameSp V0 U0) {ψ ψ' : AddChar (AF D.host.F) ℂ}
    {θ θ' : InfFam D} (eψ : ψ' = ψ) (eθ : θ' = θ) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {s1 b1 : D.what₂.Tau → Matrix (Fin V1.rank) (Fin V1.rank) ℂ} {s0 b0 : D.what₂.Tau → Matrix (Fin V0.rank) (Fin V0.rank) ℂ}
    {t1 c1 : D.what₂.Tau → Matrix (Fin U1.rank) (Fin U1.rank) ℂ} {t0 c0 : D.what₂.Tau → Matrix (Fin U0.rank) (Fin U0.rank) ℂ}
    (ht1 : HEq t1 s1) (ht0 : HEq t0 s0) (σ1 : D.what₂.Tau → Equiv.Perm (Fin V1.rank)) (σ0 : D.what₂.Tau → Equiv.Perm (Fin V0.rank))
    (hc1 : HEq c1 fun τ => (b1 τ).submatrix id (σ1 τ)) (hc0 : HEq c0 fun τ => (b0 τ).submatrix id (σ0 τ))
    (hs1 : ∀ τ, IsCartanInv (gramAt D V1 τ) (s1 τ)) (hs0 : ∀ τ, IsCartanInv (gramAt D V0 τ) (s0 τ))
    {f : WO U1 U0 → ℂ} {f' : WO (negSp V1) V0 → ℂ} (hf : HEq f f') (hth : IsThetaFunO ψ (GlobalTheory.Grid.sgn true U1) U0 f)
    (q : PolF D V0.rank V1.rank) : ∃ p : PolF D U0.rank U1.rank,
      HEq (pureTensorO ψ θ (GlobalTheory.Grid.sgn true U1) U0 (fun τ => GlobalTheory.Grid.sgnM true (t1 τ)) t0 c1 c0 f p)
        (pureTensorO ψ' θ' (negSp V1) V0 (fun τ => -s1 τ) s0 b1 b0 f' q) := by
  obtain ⟨L, a, b, rfl⟩ := h1
  obtain ⟨L', a', b', rfl⟩ := h0
  subst eψ eθ
  cases ht1; cases ht0; cases hc1; cases hc0; cases hf
  have hth' : IsThetaFunO _ (negSp V1) V0 _ := ⟨hth.1, hth.2, hth.3, hth.4⟩
  exact ⟨_, heq_of_eq (pureTensorO_perm (S := negSp V1) (T := V0) hψ hθ (fun τ => isCartanInv_neg (hs1 τ)) hs0 b1 b0 σ1 σ0
    hth' q)⟩

end GlobalTheory.RowKer

namespace GlobalTheory.RowKer

open GlobalTheory.GridJoin

theorem kernel_row : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R),
    IsSelfDualC (Yc D 0) (R.ΛY 0) → ch.W.Over R → ∀ (G : GlobalTheory.Grid.GridPre R), G.Is → GlobalTheory.GridJoin.Match G ch.W →
    ∀ (ρ : ch.G.RealVec) (Φ : ch.G.Datum) (i : Fin D.R.m), ∃ f,
      GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V ((i : ℕ) + 1) 0) (G.V i 0) f ∧ ∃ p,
        HEq (fun h g => thetaKO (G.X i 0).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.V ((i : ℕ) + 1) 0) (G.V i 0) f p))
          (fun h g => ch.W.kerA (.right (i : ℕ) 0) (ch.W.datum ρ Φ i) g h) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hY hO G hG hM ρ Φ i
  obtain ⟨hsp, harr⟩ := hM
  have hi : (i : ℕ) < D.R.m := i.2
  obtain ⟨c, hc⟩ := (harr.cos i hi).2 (Φ i)
  have sd : ∀ k, k ≤ D.R.m → IsSelfDualC (G.V k 0).V (G.V k 0).Λ := by
    rintro (_ | k) hk
    · exact hY
    · exact GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ 1 (hG.spaces.vert k 0 hk (Nat.zero_le _)).frame
  have hfin : GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V ((i : ℕ) + 1) 0) (G.V i 0) (G.vC i c) :=
    GlobalTheory.T.isFiniteDatum_of_homLatticeCoset_selfDual c (hG.arrows.X i 0 hi (Nat.zero_le _)).vac (sd _ hi) (sd _ hi.le) hG.chars.places.idem
      (G.toPlaceDat.ideal_ne_bot _) (hG.data i hi c)
  refine ⟨G.vC i c, hfin, ?_⟩
  have n1 := hsp.vert ((i : ℕ) + 1) 0 hi (Nat.zero_le _)
  have n0 := hsp.vert i 0 hi.le (Nat.zero_le _)
  obtain ⟨σ1, hσ1⟩ := n1.onb (by simp)
  obtain ⟨σ0, hσ0⟩ := n0.onb (by simp)
  obtain ⟨p, hp⟩ := heq_fock n1.sp n0.sp hO.ψ hO.θ (hO.ψ ▸ ch.W.ψ_std) (hO.θ ▸ ch.W.θ_is) n1.cart n0.cart σ1 σ0 hσ1 hσ0
    (fun τ => ch.W.cart_is _ (by simp only [GlobalTheory.ChiGrid.Node.InRange]; omega) τ)
    (fun τ => ch.W.cart_is _ (by simp only [GlobalTheory.ChiGrid.Node.InRange]; omega) τ) hc hfin.1 (ρ i)
  exact ⟨p, heq_ker n1.sp n0.sp (G.X i 0).ω (ch.W.om (.chi i 0)) (harr.omX i 0 hi (Nat.zero_le _)) _ _ hp⟩

end GlobalTheory.RowKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelCoordinatesBijOnAndWeilLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitCoordModel

variable {D : D7}

theorem exists_haar (v : FinPl D) : ∃ ν : Measure (Fv D.host.F v), ν.IsAddHaarMeasure := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  exact ⟨MeasureTheory.Measure.addHaar, inferInstance⟩

theorem pull_sub {S T : HSp D} {v : FinPl D} {m n : ℕ} (a : AE D)
    (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)) (Φ₁ Φ₂ : Matrix (Fin m) (Fin n) (Fv D.host.F v) → ℂ) :
    pull a κ (Φ₁ - Φ₂) = pull a κ Φ₁ - pull a κ Φ₂ := by
  funext t
  simp only [pull, Pi.sub_apply]
  split_ifs <;> simp

theorem ipO_smul_smul {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (c : ℂ) (f : Mx D m n → ℂ) :
    ipO μ 𝓕 (c • f) (c • f) = (c * (starRingEnd ℂ) c) * ipO μ 𝓕 f f := by
  unfold ipO
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext w
  ring

theorem bijOn_and_om_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (e a : AE D), IsSplitIdem D e → e + cA D e = idem D (.inl v) → (a = e ∨ a = cA D e) → ∀ (m n : ℕ) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsCoord a (latO S T ΛS ΛT fun _ => True) κ → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → Set.BijOn (fun Φ => Tm (pull a κ Φ)) (GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v))) {f | IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) f} ∧ ∀ g h, SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∀ (γ : GL (Fin n) (Fv D.host.F v)) (δ : GL (Fin m) (Fv D.host.F v)), (∀ t, κ (actO S T g⁻¹ h⁻¹ t) = (δ⁻¹).val * κ t * γ.val) → ∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), om (g, h) (Tm (pull a κ Φ)) = ((splitFacO χS χT x y : Circle) : ℂ) • Tm (pull a κ (linOm v γ δ Φ)) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hC v e a he hev ha m n κ hκ Tm hTm

  obtain ⟨haS, haI⟩ : IsSplitIdem D a ∧ a + cA D a = idem D (.inl v) := by
    rcases ha with rfl | rfl
    · exact ⟨he, hev⟩
    · obtain ⟨h1, h2, w, ε, hε, h3⟩ := he
      refine ⟨⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm]; exact h2, w, ε, hε, by rw [cA_cA, add_comm]; exact h3⟩, ?_⟩
      rw [cA_cA, add_comm]; exact hev
  obtain ⟨-, hloc, hsurj⟩ : _ ∧ _ ∧ _ := by
    have := _root_.GlobalTheory.PlaceModelOnto.placeModel_onto_local D ψ θ S T sS sT ΛS ΛT f₀ hB v a haS haI
    exact ⟨this.1, this.2 Tm hTm⟩
  have hP := GlobalTheory.HalfCoordSB.isSBHalf_iff_pull D S T v m n a _ κ hκ
  obtain ⟨ν, hν⟩ := exists_haar (D := D) v
  obtain ⟨hv0, hvT, hIso⟩ := _root_.GlobalTheory.PlaceIsometry.placeModel_isometry D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC v a haS m n κ hκ Tm hTm ν hν
  have hvol : ((GlobalTheory.SplitWeil.volM ν (Fin m) (Fin n)
      (κ '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf a t})).toReal : ℂ) ≠ 0 := by
    exact_mod_cast ENNReal.toReal_ne_zero.mpr ⟨hv0, hvT⟩
  have hU := GlobalTheory.LinUnit.linOm_unitary D v m n
  have hdef : ∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)),
      GlobalTheory.SplitWeil.ip ν Φ Φ = 0 → Φ = 0 := fun Φ hΦ => ((hU 1 1).2 Φ hΦ).2 ν hν |>.2
  refine ⟨⟨fun Φ hΦ => hloc _ (hP.1 Φ hΦ), ?_, ?_⟩, ?_⟩
  · intro Φ₁ h₁ Φ₂ h₂ heq
    have hd : Φ₁ - Φ₂ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)) :=
      Submodule.sub_mem _ h₁ h₂
    have h0 : Tm (pull a κ (Φ₁ - Φ₂)) = 0 := by
      rw [pull_sub, map_sub, sub_eq_zero]; exact heq
    have hi := hIso _ hd _ hd
    rw [h0] at hi
    refine sub_eq_zero.mp (hdef _ hd ?_)
    rw [← hi]; simp [ipO]
  · intro x hx
    obtain ⟨Ψ, hΨ, rfl⟩ := hsurj x hx
    obtain ⟨Φ, hΦ, rfl⟩ := hP.2 Ψ hΨ
    exact ⟨Φ, hΦ, rfl⟩
  · intro g h hg hh x y hx hy γ δ hκa Φ hΦ
    obtain ⟨r, hr, hom⟩ := GlobalTheory.PlaceTensor.om_placeModel_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ hW hB v e a he hev
      ha Tm hTm g h hg hh x y hx hy
    obtain ⟨r', hr', hlin⟩ := (hU γ δ).1
    have hr'0 : (r' : ℂ) ≠ 0 := by exact_mod_cast hr'.ne'

    have hsub : (fun t => pull a κ Φ (actO S T g⁻¹ h⁻¹ t)) = ((r' : ℂ)⁻¹) • pull a κ (linOm v γ δ Φ) := by
      funext t
      simp only [pull, Pi.smul_apply, smul_eq_mul, hlin]
      by_cases ht : IsHalf a t
      · rw [if_pos (GlobalTheory.SplitHecke.isHalf_actO g⁻¹ h⁻¹ ht), if_pos ht, hκa]
        field_simp
      · have ht' : ¬ IsHalf a (actO S T g⁻¹ h⁻¹ t) := by
          intro h'
          apply ht
          have h2 := GlobalTheory.SplitHecke.isHalf_actO g h h'
          have h3 := GlobalTheory.SplitHecke.actO_inv_actO g⁻¹ h⁻¹ t
          rw [inv_inv, inv_inv] at h3
          rwa [h3] at h2
        rw [if_neg ht', if_neg ht, mul_zero]
    have hmain : om (g, h) (Tm (pull a κ Φ)) =
        (((r : ℂ) * (r' : ℂ)⁻¹) * ((splitFacO χS χT x y : Circle) : ℂ)) • Tm (pull a κ (linOm v γ δ Φ)) := by
      rw [hom _ (hP.1 Φ hΦ), hsub, map_smul, smul_smul]
      congr 1; ring
    by_cases hΦ0 : GlobalTheory.SplitWeil.ip ν Φ Φ = 0
    ·
      have hz := hdef Φ hΦ hΦ0
      subst hz
      have hG0 : pull a κ (linOm v γ δ 0) = 0 := by
        funext t; simp [pull, hlin]
      rw [hmain, hG0]; simp
    ·
      have hF : IsThetaFunO ψ S T (Tm (pull a κ Φ)) := (hloc _ (hP.1 Φ hΦ)).1
      have h1 : ipO μ 𝓕 (om (g, h) (Tm (pull a κ Φ))) (om (g, h) (Tm (pull a κ Φ))) =
          ipO μ 𝓕 (Tm (pull a κ Φ)) (Tm (pull a κ Φ)) := by
        unfold ipO
        exact GlobalTheory.WeilInner.om_inner D ψ S T χS χT om hW μ 𝓕 hC (g, h) _ _ hF hF
      rw [hmain, ipO_smul_smul] at h1
      have hΦL := ((hU γ δ).2 Φ hΦ).1
      have hunit := (((hU γ δ).2 Φ hΦ).2 ν hν).1
      have e1 := hIso Φ hΦ Φ hΦ
      have e2 := hIso _ hΦL _ hΦL
      rw [hunit] at e2
      have hGF := mul_left_cancel₀ hvol (e2.trans e1.symm)
      have hI : ipO μ 𝓕 (Tm (pull a κ Φ)) (Tm (pull a κ Φ)) ≠ 0 := by
        intro h0; apply hΦ0; rw [← e1, h0, mul_zero]
      rw [hGF] at h1
      have hc := mul_right_cancel₀ hI (h1.trans (one_mul _).symm)
      have hχ : ((splitFacO χS χT x y : Circle) : ℂ) * (starRingEnd ℂ) ((splitFacO χS χT x y : Circle) : ℂ) = 1 := by
        rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
      rw [map_mul, map_mul, map_inv₀, Complex.conj_ofReal, Complex.conj_ofReal] at hc
      have hsq : ((r : ℂ) * (r' : ℂ)⁻¹) ^ 2 = 1 := by
        linear_combination hc - ((r : ℂ) * (r' : ℂ)⁻¹) ^ 2 * hχ
      have hsqR : (r * r'⁻¹) ^ 2 = (1 : ℝ) := by exact_mod_cast hsq
      have hq : r * r'⁻¹ = 1 := (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).mp hsqR
      have hqC : (r : ℂ) * (r' : ℂ)⁻¹ = 1 := by exact_mod_cast hq
      rw [hmain, hqC, one_mul]

end GlobalTheory.SplitCoordModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaFactor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly.PureImage

theorem det_ne_of_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  subst hn
  intro h0
  have h1 : Aᵀ * M * A.map star = (A.submatrix finSumFinEquiv id)ᵀ * M.submatrix finSumFinEquiv finSumFinEquiv *
      (A.map star).submatrix finSumFinEquiv id := by
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have h2 := congrArg Matrix.det hA
  rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, h0, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at h2
  simp only [mul_zero, zero_mul, Matrix.det_one, one_mul, mul_one] at h2
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h2.symm

theorem det_ne_of_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  refine det_ne_of_sig h ?_
  have : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, this, h0, map_zero, mul_zero]

theorem exists_factor_inj {U V P : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup P]
    [Module ℂ P] (T : U →ₗ[ℂ] V) (S : Submodule ℂ U) (hT : ∀ x ∈ S, T x = 0 → x = 0) (p : U →ₗ[ℂ] P) :
    ∃ q : V →ₗ[ℂ] P, ∀ x ∈ S, q (T x) = p x := by
  obtain ⟨r, hr⟩ := (T.comp S.subtype).exists_leftInverse_of_injective (by
    rw [LinearMap.ker_eq_bot']
    exact fun x hx => Subtype.ext (hT x.1 x.2 hx))
  refine ⟨p.comp (S.subtype.comp r), fun x hx => ?_⟩
  have := LinearMap.congr_fun hr ⟨x, hx⟩
  change r (T x) = ⟨x, hx⟩ at this
  simp [this]

end GlobalTheory.TripleAssembly.PureImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeChangeOfLatticeLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct nonZeroDivisors ComplexConjugate

namespace GlobalTheory.ReLatPf

variable {D : D7}

theorem theta_relat (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (r : ReLat A) (r' : ReLat B) (f : WO A B → ℂ) :
    IsThetaFunO ψ r.sp r'.sp f ↔ IsThetaFunO ψ A B f := ⟨fun h => ⟨h.1,h.2,h.3,h.4⟩, fun h => ⟨h.1,h.2,h.3,h.4⟩⟩

theorem aut_relat (V : HSp D) (r : ReLat V) (θ : InfFam D) (φ : GA D V → ℂ) : IsAutFunSm θ r.sp φ ↔ IsAutFunSm θ V φ :=
  ⟨fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩,
   fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩⟩

theorem reLatLaw_holds : ∀ D : D7, ReLatLaw D := by
  intro D
  refine ⟨fun V Λ h => ⟨⟨_, GlobalTheory.Core.Rk.DownCompare.latIn_lat h, GlobalTheory.Core.Rk.DownCompare.latIn_unimod h⟩,
      GlobalTheory.Core.Rk.DownCompare.frameLat_reset V Λ h V.sig⟩,
    fun V r θ S M J => ⟨?_, rfl, rfl, rfl, fun _ => Iff.rfl⟩, fun ψ A B r r' => ⟨theta_relat ψ A B r r', fun χS χT ω => ?_⟩⟩
  · have e : (Mult θ (r.mod M) J 1 : Submodule ℂ (MMap M)) = Mult θ M J 1 := by
      unfold Mult
      congr 1
      ext T
      exact ⟨fun h => ⟨fun v => (aut_relat V r θ _).1 (h.1 v), h.2, h.3, h.4, h.5⟩,
        fun h => ⟨fun v => (aut_relat V r θ _).2 (h.1 v), h.2, h.3, h.4, h.5⟩⟩
    exact congrArg (Submodule.map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] _).toLinearMap) e
  · have t := theta_relat ψ A B r r'
    exact ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, fun p f hf => (t _).1 (h.6 p f ((t _).2 hf)),
        fun g k w f hf => h.7 g k w f ((t _).2 hf), fun γ a γ' b f hf => h.8 γ a γ' b f ((t _).2 hf),
        fun f hf => h.9 f ((t _).2 hf), fun μ X a b p f hf => h.10 μ X a b p f ((t _).2 hf),
        fun e he g k a b x y c d => (h.11 e he g k a b x y c d).imp fun _ hr => ⟨hr.1, fun l hl f hf =>
          hr.2 l (fun u hu f hf => hl u hu f ((t _).1 hf)) f ((t _).2 hf)⟩⟩,
      fun h => ⟨h.1, h.2, h.3, h.4, h.5, fun p f hf => (t _).2 (h.6 p f ((t _).1 hf)),
        fun g k w f hf => h.7 g k w f ((t _).1 hf), fun γ a γ' b f hf => h.8 γ a γ' b f ((t _).1 hf),
        fun f hf => h.9 f ((t _).1 hf), fun μ X a b p f hf => h.10 μ X a b p f ((t _).1 hf),
        fun e he g k a b x y c d => (h.11 e he g k a b x y c d).imp fun _ hr => ⟨hr.1, fun l hl f hf =>
          hr.2 l (fun u hu f hf => hl u hu f ((t _).2 hf)) f ((t _).1 hf)⟩⟩⟩

end GlobalTheory.ReLatPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVecCongr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ChainCol

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


open Classical in
def extDat {m n : ℕ} (e e' : AE D) (Λ : AddSubgroup (Mx D m n)) (φ : Mx D m n → ℂ) : Mx D m n → ℂ :=
  fun x => if IsHalf e x ∧ x.map ((e - e') * ·) ∈ Λ then φ (x.map (e' * ·)) else 0


open Classical in
def stepDat (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (LS : LevDat D.host.E ℂ S.rank) (χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (e : AE D) :
    WO S T → ℂ :=
  fun x => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then
      omegaG LS χj (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q LS.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x))
    else 0

theorem r_le_colY {T : Type} (L : LevCh D T) (j : ℕ) : D.R.r ≤ (columnBlock L j).sp.rank := by
  rcases j with _ | j
  · exact r_le_Y 0
  · by_cases h : j + 1 < D.R.m
    · rw [colY_lt L h]; exact r_le_Y _
    · rw [show columnBlock L (j + 1) = ⟨D.sp.X', L.ΛX⟩ from if_neg h]; exact r_le_X

def colDat {T : Type} (L : LevCh D T) (t : T) (j : ℕ) : LevDat D.host.E ℂ (columnBlock L j).sp.rank :=
  Formalism.IndefR.Lev.datY _ D.R.r D.R.t j (r_le_colY L j) L.Pg (L.Q t) (LevelP.triv L.Pg D.R.r ℂ) L.chi (L.xiR t) Formalism.IndefR.Lev.Frm.B

theorem lsp_heq {X : LSp D} {S : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (h : X = ⟨S, Λ⟩) :
    X.sp = S ∧ HEq X.lat Λ := by
  subst h; exact ⟨rfl, HEq.rfl⟩

theorem datY_heq {n n' : ℕ} (h : n = n') (r t j : ℕ) (hr : r ≤ n) (hr' : r ≤ n') (Pg Q : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (fr : Formalism.IndefR.Lev.Frm) :
    HEq (Formalism.IndefR.Lev.datY n r t j hr Pg Q P χ ξ fr) (Formalism.IndefR.Lev.datY n' r t j hr' Pg Q P χ ξ fr) := by
  subst h; rfl

theorem stepVec_congr {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S S' T T' : HSp D} (hS : S = S') (hT : T = T')
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {sS' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ} {sT' : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)} {ΛT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}
    {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)} {βS' : GL (Fin S'.rank) (EAf D)} {βT' : GL (Fin T'.rank) (EAf D)}
    {LS : LevDat D.host.E ℂ S.rank} {LS' : LevDat D.host.E ℂ S'.rank} {χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {Q : Finset (Pl D.host.E)} {f₀ f : WO S T → ℂ} {f₀' f' : WO S' T' → ℂ}
    (h1 : HEq sS sS') (h2 : HEq sT sT') (h3 : HEq ΛS ΛS') (h4 : HEq ΛT ΛT') (h5 : HEq βS βS') (h6 : HEq βT βT')
    (h7 : HEq LS LS') (h8 : HEq f₀ f₀') (h9 : HEq f f')
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f) :
    IsStepVecOf ψ θ S' T' sS' sT' ΛS' ΛT' βS' βT' LS' χj Q ξ f₀' f' := by
  subst hS hT
  cases h1; cases h2; cases h3; cases h4; cases h5; cases h6; cases h7; cases h8; cases h9
  exact h

end GlobalTheory.ChainCol
end
end

