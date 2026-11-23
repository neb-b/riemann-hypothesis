module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1676
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1722
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1731
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1737
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfCosetIndicatorModIdealIsSchwartzBruhatHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

namespace GlobalTheory.BotSmallDict

set_option synthInstance.maxHeartbeats 400000


set_option maxHeartbeats 1000000 in
theorem cosetFn_isSBHalf : ∀ {D : D7} (S T : HSp D) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    Submodule.IsFullLattice D.host.E LS → Submodule.IsFullLattice D.host.E LT → ∀ (a : Formalism.L2.Theta.AE D), infPart D a = 0 →
    ∀ (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ x : WO S T, IsHalf a x →
      IsSBHalf a (latO S T LS LT fun _ => True) (cosetFn a I x) := by
  intro D S T LS LT hS hT a hinf I hI x _
  obtain ⟨k₁, hk₁, h₁⟩ := GlobalTheory.PlaceVec.exists_nsmul_latO_int (S := S) (T := T) hS.fg hT.fg
  obtain ⟨k₄, hk₄, h₄⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO hS hT (S := S) (T := T)
  obtain ⟨d, hd, hx⟩ := GlobalTheory.PlaceVec.exists_common_nsmul (Formalism.L2.Herm.intAf D.host.F D.host.E).toAddSubgroup
    (fun p : Fin T.rank × Fin S.rank => toEAf D (x p.1 p.2)) fun p => GlobalTheory.PlaceVec.exists_nsmul_mem_int _
  obtain ⟨n₀, hn₀, hnI⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I :=
    ⟨_, Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), Ideal.absNorm_mem I⟩
  have hsupp : ∀ t, cosetFn a I x t ≠ 0 →
      IsHalf a t ∧ ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (t i j - x i j)) := fun t ht => by
    unfold cosetFn at ht
    by_contra h
    exact ht (if_neg h)
  refine ⟨fun t ht => (hsupp t ht).1, n₀ * k₁ * (k₄ * d), by positivity, fun u hu hh t => ?_, fun t ht => ?_⟩
  ·
    have hw : ∀ i j, ((k₄ * d) • (k₁ • u.map (toEAf D))) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      fun i j => nsmul_mem (h₁ u hu i j) _
    have hsh : ∀ i j, toEAf D ((t + (n₀ * k₁ * (k₄ * d)) • u : WO S T) i j - x i j) =
        toEAf D (t i j - x i j) + (n₀ : EAf D) * ((k₄ * d) • (k₁ • u.map (toEAf D))) i j := fun i j => by
      rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, RingHom.map_sub,
        RingHom.map_sub, RingHom.map_add, map_nsmul, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    have hH : IsHalf a (t + (n₀ * k₁ * (k₄ * d)) • u) ↔ IsHalf a t := by
      rw [GlobalTheory.PlaceModel.isHalf_iff S T, GlobalTheory.PlaceModel.isHalf_iff S T]
      exact AddSubgroup.add_mem_cancel_right _ (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hh) _)
    have hC : (∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D ((t + (n₀ * k₁ * (k₄ * d)) • u : WO S T) i j - x i j))) ↔
        ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (t i j - x i j)) :=
      ⟨fun H i j => StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.inId_shift hnI (neg_mem (hw i j))
          (by rw [hsh, mul_neg, add_neg_cancel_right]) (H i j),
        fun H i j => StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.inId_shift hnI (hw i j) (hsh i j) (H i j)⟩
    unfold cosetFn
    by_cases hc : IsHalf a t ∧ ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (t i j - x i j))
    · rw [if_pos hc, if_pos ⟨hH.2 hc.1, hC.2 hc.2⟩]
    · rw [if_neg hc, if_neg fun h' => hc ⟨hH.1 h'.1, hC.1 h'.2⟩]
  ·
    obtain ⟨hth, htc⟩ := hsupp t ht
    have hint : IsIntM ((d • t).map (toEAf D)) := fun i j => by
      have e : ((d • t).map (toEAf D)) i j = d • toEAf D (t i j - x i j) + d • toEAf D (x i j) := by
        rw [GlobalTheory.PlaceVec.map_toEAf_nsmul, Matrix.smul_apply, Matrix.map_apply, ← smul_add, RingHom.map_sub, sub_add_cancel]
      rw [e]
      exact add_mem (nsmul_mem (htc i j).1 d) (show d • toEAf D (x i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E from hx (i, j))
    have hinf' : (d • t).map (infPart D) = 0 :=
      GlobalTheory.PlaceVec.half_infPart hinf (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hth) d)
    have h := nsmul_mem (h₄ (d • t) hinf' hint) (n₀ * k₁)
    rw [smul_smul, smul_smul] at h
    rwa [← mul_assoc (n₀ * k₁)]

end GlobalTheory.BotSmallDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeisenbergTranslateFockBox
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RouteBoxDeriv

theorem sum_two {α : Type} (a b : α) (F : α → ℂ) :
    ((Finsupp.single a (1 : ℂ) + Finsupp.single b 1).sum fun P' c => c * F P') = F a + F b := by
  rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _), Finsupp.sum_single_index (zero_mul _),
    Finsupp.sum_single_index (zero_mul _), one_mul, one_mul]


set_option maxHeartbeats 1000000 in
theorem hasDerivAt_box : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ n Φ τ τ', HasFlip B t ρ i j n Φ τ τ' →
    ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → ∀ P : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j), ∃ b : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) →₀ ℂ,
    ∀ d ∈ (τ : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)).support, ∀ v, HasDerivAt (fun s : ℝ =>
      W.ψ (⅟(2 : AF D.host.F) * ((Γ.M.co.e v).1 ⬝ᵥ (Γ.M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)).2 -
        (Γ.M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)).1 ⬝ᵥ (Γ.M.co.e v).2)) *
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) (v + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u))
      (b.sum fun P' c => c * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P') v) 0 := by
  intro D T L sc G μ₀ hL W B ρ t i j M e Bs Γ X om om' h _hT n Φ τ τ' hF u hu P
  classical
  obtain ⟨A, hA⟩ := GlobalTheory.SquareDict.exists_isGridFr W (X := .grid (↑i + 1) (↑j + 1)) ⟨i.2, j.2⟩
  obtain ⟨AV, hV⟩ := GlobalTheory.SquareDict.exists_isGridFr W (X := .grid ↑i (↑j + 1)) ⟨i.2.le, j.2⟩
  obtain ⟨AV₁, hV₁⟩ := GlobalTheory.SquareDict.exists_isGridFr W (X := .grid (↑i + 1) ↑j) ⟨i.2, j.2.le⟩
  have cA : (GlobalTheory.SquareComm.frSgn true A).cart = fun σ => -W.cart (.grid (↑i + 1) (↑j + 1)) σ := funext fun σ =>
    (GlobalTheory.PairLift.cart_frSgn true A σ).trans (congrArg Neg.neg (hA σ).2)
  have cA' : A.cart = W.cart _ := funext fun σ => (hA σ).2
  have cV : AV.cart = W.cart _ := funext fun σ => (hV σ).2
  have cV₁ : AV₁.cart = W.cart _ := funext fun σ => (hV₁ σ).2
  have oA : A.onb = W.onb _ := funext fun σ => (hA σ).1
  have oV : AV.onb = W.onb _ := funext fun σ => (hV σ).1
  have oV₁ : AV₁.onb = W.onb _ := funext fun σ => (hV₁ σ).1
  have e₁ : ∀ f Q, W.fock (.chi i (j + 1)) f Q = GlobalTheory.ChainFr.ptF W.ψ W.θ (GlobalTheory.SquareComm.frSgn true A) AV f Q := by
    intro f Q
    unfold GlobalTheory.ChainFr.ptF
    rw [cA, cV, oV, show (GlobalTheory.SquareComm.frSgn true A).onb = W.onb _ from oA]
    rfl
  have e₂ : ∀ f Q, W.fock (.mu t (i + 1) j) f Q = GlobalTheory.ChainFr.ptF W.ψ W.θ AV₁ A f Q := by
    intro f Q
    unfold GlobalTheory.ChainFr.ptF
    rw [cA', cV₁, oA, oV₁]
    rfl
  obtain ⟨ee, he, -, φ₁, φ₂, hφ, -⟩ := hF
  have v₁ := (ρ.vX_is i (j + 1) i.2 j.2).2
  have v₂ := (ρ.vT_is t (i + 1) j i.2 j.2).2
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have w₁ : ∀ d ∈ (τ : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)).support,
      GlobalTheory.ChainFr.IsVacF W.ψ W.θ (GlobalTheory.SquareComm.frSgn true A) AV d.1.2 := fun d hd => by
    have t₁ := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is (hφ d hd).1.2 v₁.2
    exact ⟨t₁, fun σ => by
      rw [cA, cV]
      exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is ho.infPart_eq ho.conj.infPart_eq (hφ d hd).1.2
        v₁.theta t₁ (v₁.fock σ)⟩
  have w₂ : ∀ d ∈ (τ : TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)).support, GlobalTheory.ChainFr.IsVacF W.ψ W.θ AV₁ A d.2 :=
    fun d hd => by
    have t₂ := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is (hφ d hd).2.2 v₂.2
    exact ⟨t₂, fun σ => by
      rw [cA', cV₁]
      exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is ho.infPart_eq ho.conj.infPart_eq (hφ d hd).2.2
        v₂.theta t₂ (v₂.fock σ)⟩

  have heis0 : ∀ {S' T' : HSp D} (F : WO S' T' → ℂ) (x : WO S' T'), heisO W.ψ S' T' 0 F x = F x := by
    intro S' T' F x
    have h0 : symplOH S' T' x 0 = 0 := by
      have := GlobalTheory.OrientedHeis.symplOH_add_right (S := S') (T := T') x 0 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    simp only [heisO, h0, AddChar.map_zero_eq_one, one_mul, add_zero]
  have line : ∀ {V' W' : HSp D} (A' : GlobalTheory.ChainFr.Fr V') (B' : GlobalTheory.ChainFr.Fr W') (w : WO V' W'),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) w →
      ∃ Δ : PolF D W'.rank V'.rank →ₗ[ℂ] PolF D W'.rank V'.rank, ∀ f, GlobalTheory.ChainFr.IsVacF W.ψ W.θ A' B' f →
        ∀ (Q : PolF D W'.rank V'.rank) (x : WO V' W'),
          HasDerivAt (fun s : ℝ => heisO W.ψ V' W' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • w) (GlobalTheory.ChainFr.ptF W.ψ W.θ A' B' f Q) x)
            (GlobalTheory.ChainFr.ptF W.ψ W.θ A' B' f (Δ Q) x) 0 := by
    intro V' W' A' B' w hw
    choose Δ hΔ using fun σ => _root_.GlobalTheory.FockDerUnif.dRho_ptF_uniform A' B' W.ψ_std W.θ_is σ (compAt W.θ σ w)
    refine ⟨∑ σ, Δ σ, fun f hf Q x => ?_⟩
    have hth : IsThetaFunO W.ψ V' W' (GlobalTheory.ChainFr.ptF W.ψ W.θ A' B' f Q) :=
      GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO W.ψ V' W') (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
        (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta W.ψ_std W.θ_is _ _ _ h) hf.1 Q
    have hd := GlobalTheory.ArchLineSum.hasDerivAt_realAd_smul D W.ψ W.θ W.ψ_std W.θ_is V' W' _ hth w hw x
    convert hd using 1
    have e : GlobalTheory.ChainFr.ptF W.ψ W.θ A' B' f ((∑ σ, Δ σ) Q) = ∑ σ, GlobalTheory.ChainFr.ptF W.ψ W.θ A' B' f (Δ σ Q) := by
      unfold GlobalTheory.ChainFr.ptF
      set_option synthInstance.maxHeartbeats 100000 in
        rw [LinearMap.sum_apply, map_sum]
    rw [e, Finset.sum_apply]
    exact Finset.sum_congr rfl fun σ _ => by rw [hΔ σ f hf Q]

  have sx₁ : ∀ (a : AF D.host.F) (y : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)),
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e (a • y))ᵀ =
        a • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e y)ᵀ := by
    intro a y
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV
    have h1 : ((a • y).submatrix id fun k => e (Sum.inl k)) = a • (y.submatrix id fun k => e (Sum.inl k)) :=
      Matrix.ext fun _ _ => rfl
    simp only [h1, Matrix.transpose_smul, Matrix.smul_mul]
  have sx₂ : ∀ (a : AF D.host.F) (y : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)),
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e (a • y) = a • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e y := by
    intro a y
    have hc : ∀ x : AE D, Formalism.L2.Theta.cA D (a • x) = a • Formalism.L2.Theta.cA D x := fun x =>
      map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) a x
    ext p q
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG, Matrix.neg_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.map_apply, Matrix.submatrix_apply, hc, smul_mul_assoc, Finset.smul_sum, smul_neg]
  have hu₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e u)ᵀ) := fun a ha => by
    rw [← sx₁, hu a ha]
    simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV]
  have hu₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e u) := fun a ha => by
    rw [← sx₂, hu a ha]
    simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG]
  obtain ⟨Δ₁, hΔ₁⟩ := line (GlobalTheory.SquareComm.frSgn true A) AV _ hu₁
  obtain ⟨Δ₂, hΔ₂⟩ := line AV₁ A _ hu₂
  refine ⟨Finsupp.single ((((), Δ₁ P.1.2), P.2) : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)) 1 +
    Finsupp.single ((((), P.1.2), Δ₂ P.2) : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)) 1, fun d hd v => ?_⟩
  have hbox : ∀ (Q : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j)) y,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d Q) y =
        GlobalTheory.ChainFr.ptF W.ψ W.θ (GlobalTheory.SquareComm.frSgn true A) AV d.1.2 Q.1.2
                     (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e y)ᵀ) *
          GlobalTheory.ChainFr.ptF W.ψ W.θ AV₁ A d.2 Q.2 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e y) := by
    intro Q y
    rw [← e₁, ← e₂]
    rfl
  have hr0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 0 = 0 := GlobalTheory.ThetaLineDeriv.realAd_zero
  simp only [hbox]
  simp only [_root_.GlobalTheory.BoxPhase.phase_box_heis e Γ h.JW h.JWW W.ψ, sx₁, sx₂]
  have hm := (hΔ₁ d.1.2 (w₁ d hd) P.1.2 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e v)ᵀ)).mul
    (hΔ₂ d.2 (w₂ d hd) P.2 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e v))
  refine hm.congr_deriv (Eq.trans ?_ (sum_two _ _ _).symm)
  rw [hr0, zero_smul, zero_smul, heis0, heis0]

end GlobalTheory.RouteBoxDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterFiniteIdeleValueEq
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.FinIdlRead

open GlobalTheory.Mem.Col2.SplitChar

theorem toFinE_eq_adEquiv (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) : GlobalTheory.BotFormula.toFinE D y = adEquiv D y := by
  let f : Formalism.MainNotions.StandardLatticesGL3.AE D →+* Formalism.MainNotions.StandardLatticesGL3.AE D := (adEquiv D).symm.toRingHom.comp (GlobalTheory.BotFormula.toFinE D).toRingHom
  have hf : ∀ z, adEquiv D (f z) = GlobalTheory.BotFormula.toFinE D z := fun z => (adEquiv D).apply_symm_apply _
  have hι : ∀ (x : D.host.E) (a : FiniteAdeleRing (𝓞 ℚ) ℚ), (GlobalTheory.BotFormula.toFinE D).toRingHom (x ⊗ₜ[ℚ] a) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E a := GlobalTheory.BotClassDict.toFinE_tmul
  have hinc : ∀ a : D.host.E, f (inc D a) = inc D a := fun a => by
    apply (adEquiv D).injective
    rw [hf, adEquiv_inc]
    have h1 : GlobalTheory.BotFormula.toFinE D (inc D a) = algebraMap D.host.E _ a * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E 1 :=
      GlobalTheory.BotClassDict.toFinE_tmul a 1
    rw [h1, map_one, mul_one]
  have hint : ∀ r ∈ OhE D, f r ∈ OhE D := fun r hr => by
    rw [mem_OhE_iff, hf]
    exact GlobalTheory.AdeleBaseChange.map_mem_int (F := ℚ) (E := D.host.E) hι hr
  have h0 : f y - y = 0 := by
    refine GlobalTheory.AdeleBaseChange.eq_zero_of_divisible (F := ℚ) (E := D.host.E) (f y - y) fun N hN => ?_
    obtain ⟨a, r, hr, e⟩ := exists_approx y hN
    refine ⟨f r - r, sub_mem (hint r hr) hr, ?_⟩
    rw [nsmul_eq_mul]
    change f y - y = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * (f r - r)
    rw [e, map_add (f := _), map_mul, map_natCast, hinc]
    ring
  rw [← hf, sub_eq_zero.1 h0]

theorem finAdEquiv_one_tmul (D : D7) (x : D.host.E) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := by
  show GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]

theorem mem_intAE_iff_finAdEquiv (D : D7) (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y P) ≤ 1 := by
  let c := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv
  let ι : Formalism.L2.DIV.AfE D.host.F D.host.E →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp c.symm.toRingHom
  have hι : ∀ x a, ι (x ⊗ₜ[D.host.F] a) = algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E a :=
    fun x a => (GlobalTheory.LFun.toFinAd_tmul a x).trans (mul_comm _ _)
  have e : ι (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y := by
    change GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (c.symm (c y)) = _
    rw [c.symm_apply_apply]
  rw [GlobalTheory.HostAdeleIso.mem_intAE_iff_comm]
  constructor
  · intro hy
    have := GlobalTheory.AdeleBaseChange.map_mem_int hι hy
    rw [e] at this
    exact this
  · intro hy
    refine GlobalTheory.AdeleBaseChange.mem_int_of_map hι ?_
    rw [e]
    exact hy

theorem chr_finIdl : ∀ {D : D7} (ν : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq ν χ → ∀ x y, IsFinIdl x y →
    ((ν x : Circle) : ℂ) = ((χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) : ℂˣ) : ℂ) := by
  intro D ν χ h x y hxy
  obtain ⟨Φ, -, hΦ', h1, h2, h3⟩ := GlobalTheory.DetRootRead.exists_adele_equiv_fin D (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E)
    (finAdEquiv_one_tmul D) (mem_intAE_iff_finAdEquiv D)
  rw [GlobalTheory.DetRootRead.read_of_equiv D ν χ h Φ hΦ' h1 h2 x]
  obtain ⟨s, hs, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have split : ∀ z w : AE D, infPart D z = infPart D w → finPart D z = finPart D w → z = w := fun z w hi hf =>
    s.injective (Prod.ext ((hs z).1.trans (hi.trans (hs w).1.symm)) ((hs z).2.trans (hf.trans (hs w).2.symm)))
  have hfst : (Φ (x : AE D)).1 = 1 := by
    let w : AE D := Φ.symm (1, (Φ (x : AE D)).2)
    have hw : Φ w = (1, (Φ (x : AE D)).2) := Φ.apply_symm_apply _
    have hwi : infPart D w = 1 := (h3 w).1 (by rw [hw])
    have hwf : finPart D w = finPart D (x : AE D) := by
      apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
      rw [← (h3 w).2, ← (h3 (x : AE D)).2, hw]
    have : w = (x : AE D) := split _ _ (hwi.trans hxy.1.symm) hwf
    rw [← this, hw]
  have he : Units.map Φ.toRingHom.toMonoidHom x = GlobalTheory.Mem.Col2.SplitChar.finIdl D y := by
    refine Units.ext (Prod.ext ?_ ?_)
    · exact hfst
    · change (Φ (x : AE D)).2 = adEquiv D (y : Formalism.MainNotions.StandardLatticesGL3.AE D)
      rw [(h3 _).2, hxy.2, toFinE_eq_adEquiv]
  rw [he]

end GlobalTheory.FinIdlRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweSplittingActsFockActionPlusTraceMultiples
section
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem lieScalarD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ)
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    ∃ c, ActsByD τ C om Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om hCM hψ hFr hΦ hom
  obtain ⟨ω₀, c₀, hH, hc, hact⟩ := GlobalTheory.T.exists_genuineSplitting_adelicSchwartz_placeSignature F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ν, hν, hmul, hνc, hν0⟩ := GlobalTheory.T.archimedean_splittings_differ_by_character F E σ α β κ ψ JA JB d om ω₀ hψ hom hH hc
  obtain ⟨k, hk⟩ := GlobalTheory.T.deriv_continuous_character_real_unitary_one_parameter F E σ β R S τ JB b C hCM hFr.2.2 ν hmul hνc hν0
  refine ⟨fun w => c₀ w + k w, ?_⟩
  intro γ hγ Y hY T g hg l hl
  have hH1 : ∀ t : ℝ, At (evI F) (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - 1) := fun t => hγ.2 _
  have hpm : ∀ f : SInf F κ, pureA F f g ∈ schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have e1 : (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) =
      fun t => ν (γ (Multiplicative.ofAdd t)) * l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g)) := by
    funext t; rw [hν _ (hH1 t) _ (hpm _), map_smul, smul_eq_mul]
  show HasDerivAt (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) _ 0
  rw [e1]
  have h3 := (hk γ hγ Y hY).mul (hact γ hγ Y hY T g hg l hl)
  have hγ0 : γ (Multiplicative.ofAdd (0 : ℝ)) = 1 := by rw [ofAdd_zero, map_one]
  have h1m : At (evI F) (((1 : UG (cA σ) JB).1 : Matrix β β (AE F E)) - 1) := fun u _ => by simp
  have hν1 : ν 1 = 1 := by
    have := hmul 1 1 h1m h1m
    rw [mul_one] at this
    exact (mul_eq_left₀ (hν0 1 h1m)).mp this.symm
  beta_reduce at h3
  set_option backward.isDefEq.respectTransparency false in
    rw [hγ0, hν1, map_one, Module.End.one_apply, one_mul] at h3
  refine h3.congr_deriv ?_
  have e2 : sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) +
        (((fun w => c₀ w + k w) w) * (Y w).trace) • (1 : Module.End ℂ _)) =
      sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) +
        (∑ w, k w * (Y w).trace) • (1 : Module.End ℂ (TensD F P Q R S)) := by
    simp only [add_mul, add_smul, ← add_assoc]
    exact GlobalTheory.LieScal.sumPl_add_smul
      (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) _
  rw [e2, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add (f := _), map_smul]
  have key : ∀ (z : ℂ) (f f' : SInf F κ), pureA F ⇑(f' + z • f) g = z • pureA F ⇑f g + pureA F ⇑f' g := by
    intro z f f'; funext x; simp [pureA]; ring
  rw [key, map_add (f := _), map_smul, smul_eq_mul]

end GlobalTheory.HoweD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeVacuumFixedAndUniqueStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_latticeVacuum_fixed_and_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (Y : Type) [AddCommGroup Y] (Xm : Y →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (P : Y → Prop),
      (∀ u, P u → Xm u ∈ latAtV G.V G.W v) → (∀ z ∈ latAtV G.V G.W v, ∃ u, P u ∧ Xm u = z) →
      ∀ ρ : Y → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)),
      (∀ x (φ : SB (Fin a × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M.co.rho B.ψ (Xm x))
        (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) ((ρ x φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      (∀ s : SB (Fin a × Fin (a + a') → Fv F v), (s : (Fin a × Fin (a + a') → Fv F v) → ℂ) = G.M.vac v → ∀ u, P u → ρ u s = s) ∧
      ∀ s : SB (Fin a × Fin (a + a') → Fv F v), (∀ u, P u → ρ u s = s) →
        ∃ c : ℂ, (s : (Fin a × Fin (a + a') → Fv F v) → ℂ) = c • G.M.vac v := by
  first | exact @GlobalTheory.InertLatVac.vac_fixed_and_unique | exact GlobalTheory.InertLatVac.vac_fixed_and_unique | (intros; apply GlobalTheory.InertLatVac.vac_fixed_and_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewiseStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    (∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T Φ ∈ GlobalTheory.WeilM.schA F κ) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ) →
    (∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      T (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : κ → AF F, (∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → Φ (y + z) = 0) → T Φ y = 0 := by
  first | exact @GlobalTheory.FibreLocality.eq_zero_of_vanish_fibre | exact GlobalTheory.FibreLocality.eq_zero_of_vanish_fibre | (intros; apply GlobalTheory.FibreLocality.eq_zero_of_vanish_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockDenseArchimedeanSchwartzStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialFock_dense_archimedeanSchwartz : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → Dense (M.Pol B.ψ B.emb : Set (SInf F (Fin n × Fin d))) := by
  first | exact @GlobalTheory.PolDense.pol_dense | exact GlobalTheory.PolDense.pol_dense | (intros; apply GlobalTheory.PolDense.pol_dense <;> assumption)
end

