module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0270
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceIntegratedOpMulEqZeroOfIsotypic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOperatorSplitOneRealPlace
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasselmanWallachMultMapEquivariantSobolevContinuStatement
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casselmanWallach_multMap_equivariant_sobolevContinuous : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (ι : E →ₗ[ℂ] (GA D V → ℂ)) (N : ℕ) (π : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → (E →L[ℂ] E)), (∀ d x, p d x = (GlobalTheory.Size.growthSob θ V d N (ι x)).toReal) → (∀ x d, GlobalTheory.Size.growthSob θ V d N (ι x) ≠ ⊤) → (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ x, ι (π τ g x) = rTr V ((GlobalTheory.ChainFr.Fr.ofModel M).elt θ τ g) (ι x)) → ∀ T : MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) E, (∀ τ, ∀ g ∈ Formalism.MainNotions.S.UJset (M.ε τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.σ τ g (v τ) → T (Function.update v τ w) = π τ g (T v)) → (∀ τ (i : ℕ) (v : M.Vec), ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) ∧ ∀ w : M.sm τ, p i (T (Function.update v τ w)) ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → ι (T (Function.update v τ w)) = rTr V (atTau θ V τ g) (ι (T v))) ∧ ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = ι (T (Function.update v τ w)) x := by
  intro D θ V S M E _ _ _ _ _ _ p ι N π hp hfin hπ T hTe hTc
  refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have hg' : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) :=
      GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) hg
    rw [hTe τ _ hg' v w hw, hπ τ _ hg']
    have he : (GlobalTheory.ChainFr.Fr.ofModel M).elt θ τ (M.fr τ * g * (M.fr τ)⁻¹) = atTau θ V τ g := by
      show atTau θ V τ ((M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ) = atTau θ V τ g
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
    rw [he]
  · let f : M.sm τ →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (ι.comp (T.toLinearMap v τ))
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend f
    have hℓw : ∀ w : M.sm τ, ℓ w = ι (T (Function.update v τ w)) x := fun w => by
      have := LinearMap.congr_fun hℓ w
      simpa [f, MultilinearMap.toLinearMap_apply] using this
    refine ⟨ℓ, ?_, hℓw⟩
    obtain ⟨L, C, hL, hC⟩ := hTc τ 0 v
    refine ⟨L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ), GlobalTheory.Grow.height V x ^ N * C, ?_, fun w hw => ?_⟩
    · intro l hl X hX
      obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
      obtain ⟨X₀, hX₀, rfl⟩ := List.mem_map.1 hX
      exact GlobalTheory.GKExtFields.conj_mem_lieAt M τ (hL l₀ hl₀ X₀ hX₀)
    · have hmem : w ∈ M.sm τ := Submodule.subset_span hw
      have hw' : ℓ w = ι (T (Function.update v τ ⟨w, hmem⟩)) x := hℓw ⟨w, hmem⟩
      rw [hw']
      set y := T (Function.update v τ ⟨w, hmem⟩)
      have hpos : 0 < GlobalTheory.Grow.height V x ^ N := pow_pos (GlobalTheory.Grow.height_pos V x) N
      have hsz : p 0 y = (GlobalTheory.Size.growthSize V N (ι y)).toReal := by
        rw [hp]; simp [GlobalTheory.Size.growthSob]
      have hne : GlobalTheory.Size.growthSize V N (ι y) ≠ ⊤ := by
        have := hfin y 0; simpa [GlobalTheory.Size.growthSob] using this
      have hb : ‖ι y x‖ ≤ GlobalTheory.Grow.height V x ^ N * p 0 y := by
        have h1 : ENNReal.ofReal (‖ι y x‖ / GlobalTheory.Grow.height V x ^ N) ≤ GlobalTheory.Size.growthSize V N (ι y) :=
          le_iSup (fun g => ENNReal.ofReal (‖ι y g‖ / GlobalTheory.Grow.height V g ^ N)) x
        rw [ENNReal.ofReal_le_iff_le_toReal hne, div_le_iff₀ hpos, ← hsz] at h1
        linarith
      have hs : ((L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ)).map
          fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum = GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L (⟨w, hmem⟩ : M.sm τ) := by
        unfold GlobalTheory.SmoothGlob.sobNorm
        rw [List.map_map]
        congr 1
        refine List.map_congr_left fun l _ => ?_
        simp only [Function.comp_apply, GlobalTheory.GKExtFields.foldr_dRep_conj]
      rw [hs, mul_assoc]
      exact hb.trans (mul_le_mul_of_nonneg_left (hC ⟨w, hmem⟩) hpos.le)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerRegularLeviCommutativeNoncompact
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

namespace GlobalTheory.LeviCent

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (extSub act)
open Matrix
open scoped TensorProduct

theorem nontrivial_AF (F : Type) [Field F] [NumberField F] : Nontrivial (AF F) := ⟨⟨0, 1, fun e => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact zero_ne_one ((map_zero (evInf F w)).symm.trans ((congrArg (evInf F w) e).trans (map_one _)))⟩⟩

theorem exists_aeval_of_mem_cent {D : D7} {V : HSp D} {γ : GF V} (hγ : IsRegSS γ.1.1) {g : GA D V}
    (hg : g ∈ cent (rat V γ)) :
    ∃ p : (AF D.host.F ⊗[D.host.F] D.host.E)[X],
      (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram g).1 = aeval (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (rat V γ)).1 p := by
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field γ.1.1 hγ
  refine GlobalTheory.Orb.exists_aeval_of_cyclic (v := inclR (AF D.host.F) ∘ v) ?_ ?_
  · change IsUnit (GlobalTheory.ClassParam.krylov (γ.1.1.map (inclR (AF D.host.F))) _).det
    rw [← GlobalTheory.ClassParam.krylov_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 hv).map _
  · have := congrArg (fun x => (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram x).1) (mem_cent.1 hg)
    simp only [map_mul, Units.val_mul] at this
    exact this

theorem mem_parab_of_mem_cent {D : D7} {V : HSp D} {γ : GF V} (hγ : IsRegSS γ.1.1) {g : GA D V}
    (hg : g ∈ cent (rat V γ)) (W : Submodule D.host.E V.V)
    (h : rat V γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) W) :
    g ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) W := by
  set S := extSub (F := D.host.F) V (AF D.host.F) W
  have hs : ∀ y, y ∈ S ↔ act D.sp.cm V (rat V γ) y ∈ S := h
  set M := (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (rat V γ)).1
  have hM : ∀ y ∈ S, M *ᵥ y ∈ S := fun y hy => (hs y).1 hy
  have hp : ∀ p : (AF D.host.F ⊗[D.host.F] D.host.E)[X], ∀ y ∈ S, aeval M p *ᵥ y ∈ S := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
      intro y hy
      rw [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
      exact Submodule.smul_mem _ a hy
    | add p q hp hq =>
      intro y hy
      rw [map_add (f := _), Matrix.add_mulVec]
      exact add_mem (hp y hy) (hq y hy)
    | monomial n a ih =>
      intro y hy
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X, ← Matrix.mulVec_mulVec]
      exact ih _ (hM y hy)
  have key : ∀ g ∈ cent (rat V γ), ∀ y ∈ S, act D.sp.cm V g y ∈ S := by
    intro g hg y hy
    obtain ⟨p, e⟩ := exists_aeval_of_mem_cent hγ hg
    change (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram g).1 *ᵥ y ∈ S
    rw [e]
    exact hp p y hy
  exact fun y => ⟨key g hg y, fun hy => by
    have := key g⁻¹ (inv_mem hg) _ hy
    rwa [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_inv] at this⟩

theorem exists_ne_zero_mem_sub {D : D7} {V : HSp D} (Φ : WittFrame V) {u : SV (wittIndex V)} (hu : u ≠ 0) :
    ∃ x ∈ Φ.sub u, x ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (funext h)
  have h1 := Φ.ef i i
  rw [if_pos rfl] at h1
  rcases h : u i with _ | _ | _
  · exact absurd h hi
  · refine ⟨Φ.f i, Submodule.subset_span (Or.inr ⟨i, h, rfl⟩), fun e => ?_⟩
    rw [e] at h1; simp [HSpace.hD] at h1
  · refine ⟨Φ.e i, Submodule.subset_span (Or.inl ⟨i, h, rfl⟩), fun e => ?_⟩
    rw [e] at h1; simp [HSpace.hD] at h1

theorem cent_levi (D : D7) (V : HSp D) (Φ : WittFrame V) (P : Finset (SV (wittIndex V))) (hP : IsPar P) (γ : GF V)
    (hγ : IsRegSS γ.1.1) (hl : rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) P) :
    IsMulCommutative (cent (rat V γ)) ∧ cent (rat V γ) ≤ Φ.levi D.sp.cm (AF D.host.F) P ∧
      (P ≠ ∅ → ∀ w, ¬ IsCompact (cent (projArch D.sp.cm.sig V.gram w (rat V γ)) : Set (GArch D.sp.cm.sig V.gram w))) := by
  have hl' : ∀ u ∈ P, rat V γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub u) ∧
      rat V γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (-u)) := fun u hu =>
    Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hl u) hu)
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun g hg => ?_, fun hne w hK => ?_⟩
  · obtain ⟨p, hp⟩ := exists_aeval_of_mem_cent hγ a.2
    obtain ⟨q, hq⟩ := exists_aeval_of_mem_cent hγ b.2
    apply GlobalTheory.AdelicU.matHom_injective (AF D.host.F) D.sp.cm.sig V.gram
    apply Units.ext
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul, hp, hq]
    rw [← map_mul, ← map_mul, mul_comm]
  · refine Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact mem_parab_of_mem_cent hγ hg _ (hl' u hu).1
    · exact mem_parab_of_mem_cent hγ hg _ (hl' u hu).2
  · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have hu0 : u ≠ 0 := fun e => hP.1 (e ▸ hu)
    have := nontrivial_AF D.host.F
    have hi : rat V γ⁻¹ ∈ Φ.levi D.sp.cm (AF D.host.F) P := by rw [map_inv]; exact inv_mem hl
    have hi' := Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hi u) hu)
    have h1 := (GlobalTheory.Cusp.diagH_mem_parab (AF D.host.F)).1 (hl' u hu).1
    have h2 := (GlobalTheory.Cusp.diagH_mem_parab (AF D.host.F)).1 (hl' u hu).2
    have h3 := (GlobalTheory.Cusp.diagH_mem_parab (AF D.host.F)).1 hi'.1
    have h4 := (GlobalTheory.Cusp.diagH_mem_parab (AF D.host.F)).1 hi'.2
    obtain ⟨g, g1, g2, g3⟩ := _root_.GlobalTheory.TrScale.exists_scale D V Φ u
    have hc : Commute g γ := _root_.GlobalTheory.Cusp.WeightCommute.commute_of_weights D V Φ u γ g 2 h1 h2 h3 h4 g1 g2 g3
    obtain ⟨x, hxu, hx0⟩ := exists_ne_zero_mem_sub Φ hu0
    obtain ⟨n, hn⟩ := _root_.GlobalTheory.Twist.exists_pow_projArch_not_mem_of_eigen_two D V g x hx0 (g1 x hxu) w _ hK
    exact hn (mem_cent.2 (((hc.pow_left n).map (rat V)).map (projArch D.sp.cm.sig V.gram w)).eq)

end GlobalTheory.LeviCent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassSumInnerEqSumVectorThetaLifts
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftGram

theorem inner_eq_sum_upLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ z₁ z₂ : H.H,
    (∀ h w, inner ℂ (c.ext (H.e z₁) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) (U₁ fun ρ => v ρ) h) →
    (∀ h w, inner ℂ (c.ext (H.e z₂) h) w = GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) (U₂ fun ρ => v ρ) h) →
    ∀ {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℂ c.W),
      inner ℂ z₁ z₂ = ∑ k, GlobalTheory.AdelicScalar.l2 (R.νV i A.μ0) (R.fdV i A.μ0) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ)) (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₂ fun ρ => v ρ)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hirr hS hI hFo hZ hδ i σ s m μ' η' ω B f₀ f c io H hd hν hy hH v hv U₁ hU₁ U₂ hU₂
    z₁ z₂ h₁ h₂ ι _ b
  have hc : c.Is := hd.2.2.2.2.2.2.2.2.2.1
  refine (GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)).elim fun μ h0 => h0.elim fun 𝓧 hμ => ?_
  have h5 := (hd.1.models.νW i).1.2.2 R.θ hd.1.models.inf
  refine h5.1.elim fun Fr hFr => (h5.2 Fr hFr).1.elim fun mR hmR => ?_
  have hint : ∀ k, IntegrableOn (fun h =>
      GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ) h *
      starRingEnd ℂ (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k)))
        (U₂ fun ρ => v ρ) h)) (R.fdV i A.μ0) (R.νV i A.μ0) := fun k =>
    (hI i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io hd _ _ hν μ 𝓧 hμ Fr hFr mR hmR U₁ hU₁ U₂ hU₂ v v
      (io (PiTensorProduct.tprod ℂ v) (b k)) (io (PiTensorProduct.tprod ℂ v) (b k))).2.1
  have hx := fun z => (SetLike.ext_iff.mp hH.2.1 _).mp (LinearMap.mem_range_self H.e z)
  have e1 := GlobalTheory.AdelicScalar.integral_eq_classSum (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m) hν hy
    (fun h => inner ℂ (c.ext (H.e z₁) h) (c.ext (H.e z₂) h)) fun γ hγ k hk x =>
      (congrArg₂ (inner ℂ) (GlobalTheory.AdelicScalar.ext_law c _ _ (hx z₁) hγ k hk x) (GlobalTheory.AdelicScalar.ext_law c _ _ (hx z₂) hγ k hk x)).trans
        (GlobalTheory.AdelicScalar.inner_law c.ρ hc.2.1 (GlobalTheory.AdelicScalar.norm_levChi _ _ k) _ _ _)
  simp only [GlobalTheory.AdelicScalar.ext_finLift c hc] at e1
  rw [hH.2.2 z₁ z₂]
  unfold Bridge.adInner
  rw [← e1]
  have e2 : ∀ h, inner ℂ (c.ext (H.e z₁) h) (c.ext (H.e z₂) h) = ∑ k,
      GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k))) (U₁ fun ρ => v ρ) h *
      starRingEnd ℂ (GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) (b k)))
        (U₂ fun ρ => v ρ) h) := fun h =>
    (b.sum_inner_mul_inner _ _).symm.trans (Finset.sum_congr rfl fun k _ => congrArg₂ (· * ·) (h₁ h (b k))
      ((inner_conj_symm _ _).symm.trans (congrArg (starRingEnd ℂ) (h₂ h (b k)))))
  refine (congrArg (fun F => ∫ h in R.fdV i A.μ0, F h ∂(R.νV i A.μ0)) (funext e2)).trans ?_
  exact integral_finsetSum _ fun k _ => hint k

end GlobalTheory.LiftGram

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspTraceClassOfFactorisation
section
namespace GlobalTheory.Published

theorem cuspTraceClass_of_factorisation : DixmierMalliavinFactorisation → CuspTraceClass :=
  fun h => cuspTraceClass_of_decay _root_.GlobalTheory.CuspGeo.cuspDecayBound h

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesSpectralSide
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace GlobalTheory

theorem isIsotypic_of_uEquiv_left {G X Y K : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {δ : G →* (X →L[ℂ] X)} {δ' : G →* (Y →L[ℂ] Y)} {ρ : G →* (K →L[ℂ] K)}
    (e : ∃ A : X ≃ₗᵢ[ℂ] Y, ∀ g x, A (δ g x) = δ' g (A x)) (h : IsIsotypic δ ρ) : IsIsotypic δ' ρ := by
  obtain ⟨A, hA⟩ := e
  refine eq_top_iff.2 (h.ge.trans (isoPart_le (Submodule.isClosed_topologicalClosure _) fun T hT x => ?_))
  have hs : ∀ g y, A.symm (δ' g y) = δ g (A.symm y) := fun g y => by
    apply A.injective
    rw [hA g, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  have hx : T x = (T ∘L (A.symm : Y →L[ℂ] X)) (A x) := by simp
  rw [hx]
  refine apply_mem_isoPart (mem_homIn_top.2 fun g y => ?_) _
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [hs]
  exact (mem_homIn_top.1 hT) g _

theorem hasDSComp_of_trace_ne_zero : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → HasDSComp M π := by
  intro hDS hFl hHC hPC D V lam S M T U μa μf μ _ _ fa ff hTD H _ _ _ π hπ c hc hc0 τ
  obtain ⟨δ, hδ⟩ := hFl.exists_hasCompPl (isCMExt_host D) (isHermND_gram (V := V)) hπ (.inl (placeOf D τ))
  have hδ' : IsIsotypic (G := GArch D.sp.cm.sig V.gram (placeOf D τ)) δ.π
      (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) := hδ
  obtain ⟨c', hc', himp⟩ := _root_.GlobalTheory.ArchTrace.trace_pseudoCoeff_arch hDS hHC hPC D V lam S M T U μa μf μ fa ff hTD τ δ.H δ.π δ.isIrr
  by_cases hc'0 : c' = 0
  · exfalso
    have hRP : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ := hTD.2.2.2.2.1
    have hmem : ∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w := hTD.2.2.2.2.2.1.mem
    have hfin : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hTD.2.2.2.2.2.2.isFinFamily
    obtain ⟨Q, hQ, hrep⟩ := _root_.GlobalTheory.TrSplit.repOp_tensor_split D V μa μf μ hRP fa ff hmem hfin H π hπ.unitary (placeOf D τ)
    haveI : (μa (placeOf D τ)).IsHaarMeasure := hRP.1 _
    have hint : Integrable (fa (placeOf D τ)) (μa (placeOf D τ)) :=
      (continuous_of_mem_ccSmooth (continuous_archCoord _ _ _) (hmem _)).integrable_of_hasCompactSupport (hmem _).1
    have hπw : IsUnitaryRep (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) :=
      isUnitaryRep_comp hπ.unitary (continuous_embArch _ _ _)
    have htc : IsTraceClass (repOp (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) (μa (placeOf D τ)) (fa (placeOf D τ)) * Q) := hrep ▸ hc.1
    let δw : GArch D.sp.cm.sig V.gram (placeOf D τ) →* (δ.H →L[ℂ] δ.H) := δ.π
    have hδirr : IsIrrUnitary δw := δ.isIrr
    have hδw : IsIsotypic δw (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) := hδ'
    have hc'w : HasTrace (repOp δw (μa (placeOf D τ)) (fa (placeOf D τ))) 0 := hc'0 ▸ hc'
    have h0 := _root_.GlobalTheory.trace_repOp_mul_eq_zero_of_isIsotypic (GArch D.sp.cm.sig V.gram (placeOf D τ)) _ _ hint δ.H H δw _ hδirr hπw hδw Q hQ hc'w htc
    exact hc0 (hc.2.symm.trans (hrep ▸ h0))
  · show IsIsotypic (dsRep M τ) (π.comp (embW V (placeOf D τ)))
    exact isIsotypic_of_uEquiv_left (G := GArch D.sp.cm.sig V.gram (placeOf D τ)) (himp hc'0) hδ'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory

open Polynomial

theorem dixmier_aeval_injective {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (hT : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V))) (p : ℂ[X]) (hp : p ≠ 0) :
    Function.Injective (aeval T p) := by
  have hs := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) IsAlgClosed.card_roots_eq_natDegree
  have hlin : ∀ a : ℂ, aeval T (X - C a) = T - a • 1 := by
    intro a; simp [Algebra.algebraMap_eq_smul_one]
  have key : ∀ m : Multiset ℂ, Function.Injective (aeval T (m.map fun a => X - C a).prod) := by
    intro m
    induction m using Multiset.induction_on with
    | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero, map_one, Module.End.one_eq_id, LinearMap.id_coe]
      exact Function.injective_id
    | cons a m ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
      refine Function.Injective.comp ?_ ih
      rw [hlin]; exact hT a
  rw [← hs, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
  refine Function.Injective.comp ?_ (key _)
  rw [aeval_C, Algebra.algebraMap_eq_smul_one]
  intro x y hxy
  simp only [LinearMap.smul_apply, Module.End.one_apply] at hxy
  exact smul_right_injective V (leadingCoeff_ne_zero.mpr hp) hxy

theorem dixmier_commutant_scalar (ι V : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V)
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hirr : ∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤)
    (T : Module.End ℂ V) (hT : ∀ i, T * ρ i = ρ i * T) : ∃ c : ℂ, T = c • 1 := by
  by_contra hne
  push_neg at hne
  have hcomm : ∀ c : ℂ, ∀ i, (T - c • 1) * ρ i = ρ i * (T - c • 1) := by
    intro c i; rw [sub_mul, mul_sub, hT i, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hinj : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.ker_eq_bot]
    rcases hirr (LinearMap.ker (T - c • 1)) (fun i x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [← Module.End.mul_apply, hcomm c i, Module.End.mul_apply, hx, map_zero]) with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp (LinearMap.ker_eq_top.mp h)) (hne c)
  obtain ⟨v₀, hv₀⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h; push_neg at h
    exact hne 0 (LinearMap.ext fun v => (h _).trans (h _).symm)
  have hsurj : ∀ c : ℂ, Function.Surjective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.range_eq_top]
    rcases hirr (LinearMap.range (T - c • 1)) (fun i x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨ρ i y, by rw [← Module.End.mul_apply, hcomm c i, Module.End.mul_apply]⟩) with h | h
    · exfalso
      have h1 : (T - c • 1) v₀ ∈ LinearMap.range (T - c • 1) := LinearMap.mem_range_self _ _
      rw [h, Submodule.mem_bot] at h1
      exact hv₀ (hinj c (by rw [h1, map_zero]))
    · exact h
  let S : ℂ → V ≃ₗ[ℂ] V := fun c => LinearEquiv.ofBijective (T - c • 1) ⟨hinj c, hsurj c⟩
  let w : ℂ → V := fun c => (S c).symm v₀
  have hw : ∀ c, (T - c • (1 : Module.End ℂ V)) (w c) = v₀ := fun c => (S c).apply_symm_apply v₀
  have hlin : ∀ a : ℂ, aeval T (X - C a) = T - a • 1 := by
    intro a; simp [Algebra.algebraMap_eq_smul_one]
  have hli : LinearIndependent ℂ w := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    let q : ℂ → ℂ[X] := fun c => ∏ d ∈ s.erase c, (X - C d)
    have hq : ∀ c ∈ s, aeval T (∏ d ∈ s, (X - C d)) (w c) = aeval T (q c) v₀ := by
      intro c hc
      rw [← Finset.mul_prod_erase s _ hc, mul_comm, map_mul, Module.End.mul_apply, hlin, hw]
    have h0 : aeval T (∑ c ∈ s, g c • q c) v₀ = 0 := by
      have h2 := congrArg (aeval T (∏ d ∈ s, (X - C d))) hsum
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_zero, map_sum] at h2
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply, ← h2]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [LinearMap.map_smul, hq c hc, map_smul, LinearMap.smul_apply]
    have hp0 : ∑ c ∈ s, g c • q c = 0 := by
      by_contra hp
      exact hv₀ (dixmier_aeval_injective T hinj _ hp (by rw [h0, map_zero]))
    have h3 := congrArg (Polynomial.eval i) hp0
    rw [eval_finsetSum, Finset.sum_eq_single i] at h3
    · simp only [eval_smul, q, eval_prod, eval_sub, eval_X, eval_C, smul_eq_mul, eval_zero] at h3
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h
        obtain ⟨d, hd, hd0⟩ := h
        exact (Finset.ne_of_mem_erase hd) (sub_eq_zero.mp hd0).symm
    · intro c hc hci
      simp only [eval_smul, q, eval_prod, eval_sub, eval_X, eval_C, smul_eq_mul]
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hci, hi⟩) (sub_self i), mul_zero]
    · intro h; exact absurd hi h
  have h4 := hli.cardinal_le_rank
  rw [Cardinal.mk_complex] at h4
  exact absurd (h4.trans hrank) (not_le.mpr Cardinal.aleph0_lt_continuum)

end GlobalTheory
end

