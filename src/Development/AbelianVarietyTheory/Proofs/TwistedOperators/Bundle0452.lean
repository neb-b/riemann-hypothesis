module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultTEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0437
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizer
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0449
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicTypeFiniteDimStable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.FiniteGKSum

open GlobalTheory.SeriesToClosure Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open Matrix Filter
open scoped InnerProductSpace Topology

section Sums

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin V.rank → Bool)
  (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ)

def gkSums : Submodule ℂ (GA D V → ℂ) where
  carrier := {ψ | ∃ (m : ℕ) (T : Fin m → (kFin ε σ →ₗ[ℂ] (GA D V → ℂ))) (p : Fin m → kFin ε σ),
    (∀ j, IsGKMap θ V τ ε σ P (T j)) ∧ ψ = ∑ j, T j (p j)}
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, T, p, hT, rfl⟩ ⟨m', T', p', hT', rfl⟩
    refine ⟨m + m', Fin.append T T', Fin.append p p', fun j => ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa using hT j
      · simpa using hT' j
    · simp [Fin.sum_univ_add]
  smul_mem' := by
    rintro c _ ⟨m, T, p, hT, rfl⟩
    exact ⟨m, T, fun j => c • p j, hT, by simp [Finset.smul_sum]⟩

end Sums

section Closure

variable {D : D7} {V : HSp D}

theorem mem_of_approx {E : Submodule ℂ (GA D V → ℂ)} [FiniteDimensional ℂ E] {φ : GA D V → ℂ}
    (h : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ ψ ∈ E, ∀ x ∈ C, ‖φ x - ψ x‖ < δ) : φ ∈ E := by
  have hE : IsClosed (E : Set (GA D V → ℂ)) := Submodule.closed_of_finiteDimensional E
  have key : ∀ p : Finset (GA D V) × ℕ, ∃ ψ ∈ E, ∀ x ∈ p.1, ‖φ x - ψ x‖ < 1 / ((p.2 : ℝ) + 1) :=
    fun p => h _ p.1.finite_toSet.isCompact _ (by positivity)
  choose u hu hu' using key
  refine hE.mem_of_tendsto (f := u) (b := (atTop : Filter (Finset (GA D V) × ℕ))) ?_
    (Filter.Eventually.of_forall hu)
  refine tendsto_pi_nhds.2 fun x => Metric.tendsto_atTop.2 fun δ hδ => ?_
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨({x}, N), fun p hp => ?_⟩
  have h1 : x ∈ p.1 := hp.1 (Finset.mem_singleton_self x)
  have h2 : (N : ℝ) ≤ p.2 := by exact_mod_cast hp.2
  rw [dist_comm, dist_eq_norm]
  calc ‖φ x - u p x‖ < 1 / ((p.2 : ℝ) + 1) := hu' p x h1
    _ ≤ 1 / ((N : ℝ) + 1) := by gcongr
    _ < δ := hN

end Closure

section Avg

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {τ : D.what₂.Tau}
  {ε : Fin V.rank → Bool} {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem avg_mem (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {W : Submodule ℂ (GA D V → ℂ)} [FiniteDimensional ℂ W]
    (hW : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), P * g * P⁻¹ ∈ Formalism.REAL.Kset ε →
      ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W)
    {φ : GA D V → ℂ} (hφc : Continuous φ) (hφ : φ ∈ W) {e : KG ε → ℂ} (he : KFinFun ε e) :
    avg θ V τ ε P e φ ∈ W := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hk : Continuous fun k : KG ε => atTau θ V τ (P⁻¹ * toMK k * P) :=
    (continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
      fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have cc : ∀ g : Matrix (Fin V.rank) (Fin V.rank) ℂ, P * (P⁻¹ * g * P) * P⁻¹ = g := fun g => by
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  have hmem : ∀ k : KG ε, rTr V (atTau θ V τ (P⁻¹ * toMK k * P)) φ ∈ W := fun k =>
    hW _ (conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))) (by rw [cc]; exact toMK_mem_K k) φ hφ
  let f : KG ε → W := fun k => ⟨_, hmem k⟩
  have hf : Continuous f := (continuous_pi fun x => hφc.comp (continuous_const.mul hk)).subtype_mk _
  let b := Module.finBasis ℂ W
  have hc : ∀ i, Continuous fun k => b.coord i (f k) := fun i =>
    (LinearMap.continuous_of_finiteDimensional (b.coord i)).comp hf
  have he' : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  have hint : ∀ i, Integrable (fun k => e k * b.coord i (f k)) (muK ε) := fun i =>
    integrableOn_univ.mp ((he'.mul (hc i)).continuousOn.integrableOn_compact isCompact_univ)
  have hrep : ∀ k, (f k : GA D V → ℂ) = ∑ i, b.coord i (f k) • (b i : GA D V → ℂ) := fun k => by
    nth_rw 1 [← b.sum_repr (f k)]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rfl
  have key : avg θ V τ ε P e φ = ∑ i, (∫ k, e k * b.coord i (f k) ∂(muK ε)) • (b i : GA D V → ℂ) := by
    funext x
    have hx : ∀ k, φ (x * atTau θ V τ (P⁻¹ * toMK k * P)) = ∑ i, b.coord i (f k) * (b i : GA D V → ℂ) x :=
      fun k => by
        have := congrFun (hrep k) x
        simpa [f, rTr, Finset.sum_apply] using this
    simp only [avg, hx, Finset.mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finsetSum _ fun i _ => ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_mul_const]
      congr 1
      funext k
      ring
    · simpa [mul_assoc] using (hint i).mul_const ((b i : GA D V → ℂ) x)
  rw [key]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2

end Avg

end GlobalTheory.FiniteGKSum

namespace GlobalTheory.FiniteGKSum

end GlobalTheory.FiniteGKSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsAreGridArrows
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Grid

variable {D : D7}

section Transfer

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem actO_eq_of_real {g : GA D S} {h : GA D T} (hg : g ∈ GinfC S) (hh : h ∈ GinfC T) {x : WO S T}
    (hx : x.map (infPart D) = 0) : actO S T g h x = x := by
  have e1 : (Formalism.L2.Theta.mt S g⁻¹).map (finPart D) = 1 := congrArg Units.val (show finHom S g⁻¹ = 1 from inv_mem hg)
  have e2 : (Formalism.L2.Theta.mt T h).map (finPart D) = 1 := congrArg Units.val (show finHom T h = 1 from hh)
  have e3 : (actO S T g h x).map (infPart D) = x.map (infPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hx, Matrix.mul_zero, Matrix.zero_mul]
  have e4 : (actO S T g h x).map (finPart D) = x.map (finPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, e1, e2, Matrix.mul_one, Matrix.one_mul]
  exact Matrix.ext fun i j => GlobalTheory.SplitScalar.adele_ext (congrFun (congrFun e3 i) j) (congrFun (congrFun e4 i) j)

theorem isItW_of_mem_span {χS χT : (AE D)ˣ →* Circle} {ω : WRep S T} (hω : IsWeilDatumO ψ S T χS χT ω) (hθ : IsInfFam θ)
    {P P' : D.what₂.Tau → SPar} {M : DSModel S P} {M' : DSModel T P'}
    {sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {f₀ f : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀)
    (hf : f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀))
    {It : PolF D T.rank S.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M} (h : IsItW θ M M' ω (pureTensorO ψ θ S T sS sT BS BT f) It) :
    IsItW θ M M' ω (pureTensorO ψ θ S T sS sT BS BT f₀) It := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
  let L : Module.End ℂ (WO S T → ℂ) := ∑ a ∈ c.support, c a • GlobalTheory.SplitScalar.heisL ψ S T a.1
  have hL : ∀ F, L F = ∑ a ∈ c.support, c a • heisO ψ S T a.1 F := fun F => by
    simp only [L, LinearMap.sum_apply, LinearMap.smul_apply, GlobalTheory.SplitScalar.heisL_apply]
  have hd : ∀ τ z F, IsThetaFunO ψ S T F → L (dRho (heisO ψ S T) θ τ z F) = dRho (heisO ψ S T) θ τ z (L F) :=
    fun τ z F hF => by
      rw [hL, hL, GlobalTheory.FockTranslate.dRho_sum hω.std.1.1 hθ hF τ z c.support (fun a => a.1) c fun a _ => a.2]
  have hpt : ∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f₀ Q) ∧
      L (pureTensorO ψ θ S T sS sT BS BT f₀ Q) = pureTensorO ψ θ S T sS sT BS BT (L f₀) Q := fun Q => by
    refine GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
      (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) _ _ L (fun k F hF => ?_) f₀ h₀ Q
    obtain ⟨τ, i, j⟩ := k
    refine ⟨GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_sub (GlobalTheory.OrientedHeis.theta_dRho hθ hω.std τ _ hF)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hω.std τ _ hF))), ?_⟩
    simp only [aPlusAll, aPlus, crea]
    rw [map_smul, map_sub, map_smul, hd _ _ _ hF, hd _ _ _ hF]
  have hom : ∀ g ∈ GinfC S, ∀ k ∈ GinfC T, ∀ Q, ω (g, k) (pureTensorO ψ θ S T sS sT BS BT (L f₀) Q) =
      L (ω (g, k) (pureTensorO ψ θ S T sS sT BS BT f₀ Q)) := fun g hg k hk Q => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← (hpt Q).2, hL, hL, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hω.om_heis _ _ _ _ (hpt Q).1, actO_eq_of_real hg hk a.2]
  have hder : ∀ (F : ℝ → WO S T → ℂ) (F' : WO S T → ℂ), (∀ z, HasDerivAt (fun t => F t z) (F' z) 0) →
      ∀ z, HasDerivAt (fun t => L (F t) z) (L F' z) 0 := fun F F' hF z => by
    simp only [hL, Finset.sum_apply, Pi.smul_apply, heisO, smul_eq_mul]
    exact HasDerivAt.fun_sum fun a _ => ((hF _).const_mul _).const_mul _
  have e : (c.sum fun i a => a • heisO ψ S T i.1 f₀) = L f₀ := (hL f₀).symm
  rw [e] at h
  refine ⟨h.ne, h.bdd, fun τ g hg φ φ' H => h.eqK τ g hg φ φ' ?_, fun τ X hX φ φ' H => h.eqg τ X hX φ φ' fun z => ?_,
    fun τ g hg φ φ' v v' H => h.invK τ g hg φ φ' v v' ?_, fun τ X hX φ φ' v v' H => h.invg τ X hX φ φ' v v' fun z => ?_⟩
  · rw [hom _ (GlobalTheory.FinTranslate.atTau_mem θ S τ g) _ (one_mem _), ← H, (hpt φ').2]
  · simp only [fun t => hom _ (GlobalTheory.FinTranslate.oneP_mem θ S τ X t) _ (one_mem _) φ, ← (hpt φ').2]
    exact hder _ _ H z
  · rw [hom _ (one_mem _) _ (GlobalTheory.FinTranslate.atTau_mem θ T τ g), ← H, (hpt φ').2]
  · simp only [fun t => hom _ (one_mem _) _ (GlobalTheory.FinTranslate.oneP_mem θ T τ X t) φ, ← (hpt φ').2]
    exact hder _ _ H z

theorem stepVec_mem_span
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Datum.EAf D)} {βT : GL (Fin T.rank) (Datum.EAf D)} {L : LevDat D.host.E ℂ S.rank}
    {χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {Q : Finset (Pl D.host.E)}
    {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT)
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT L χ Q ξ f₀ f) :
    f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀) := by
  classical
  obtain ⟨hv, e, he', ⟨Tm, hTm⟩, hall⟩ := h
  obtain ⟨P, he, hP⟩ : ∃ P, IsIdemSum e P ∧ ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ Q :=
    ⟨_, he', fun PP => Finset.mem_union⟩
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ dS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ dT) βS βT
  have hSB := GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
      (GlobalTheory.PlaceDatum.exists_den_frMapO dS.1.fg dT.1.fg βS βT)
      ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ P
      (fun y => omegaG L χ y * omegaQ Q L.r ξ 1 y) fun y y' h => by
        rw [GlobalTheory.PlaceDatum.omegaG_congr _ _ y y' fun PP hPP => h PP ((hP PP).2 (Or.inl hPP)),
          GlobalTheory.PlaceDatum.omegaQ_congr _ _ _ 1 y y' fun PP hPP => h PP ((hP PP).2 (Or.inr hPP))]
  rw [hall Tm hTm]
  exact (GlobalTheory.Chain.StepVac.placeModel_span_ne hv.1 dS dT (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 hinf hTm hSB).1

theorem finVec_of_mem_span
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)} {f₀ f : WO S T → ℂ}
    (hv : IsVacO ψ θ S T sS sT ΛS ΛT f₀)
    (hf : f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀)) :
    IsThetaFunO ψ S T f ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
  exact ⟨GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hv.1.1 f₀ hv.2.theta _ c.support (fun a => a.1) c fun a _ => a.2,
    fun τ => GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hv.1.1 hv.2.inf f₀ hv.2.theta τ _ (hv.2.fock τ) _ c.support
      (fun a => a.1) c fun a _ => a.2⟩

end Transfer

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem chrStep_eq_muAt (R : RealDat D A Ks) (t : T) (j : ℕ) : Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1) =
    (GridPre.muAt R t (j + 1) (rkV D 0 j), GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) := by
  have hr : Odd D.R.r := by
    have h1 := D.R.k_even; have h2 := D.R.m_even; have h3 := D.R.two_le_m
    unfold Ranks.r; grind
  rw [Lift.chrStep_eq_att _ _ hr D.R.t_odd (Nat.le_add_left 1 j)]
  simp [rkV]

end GlobalTheory.Grid

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColMapVUpdateLast
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastColumnMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem fockComp_mul_right (B : VertexFrames G) (t : T) (j : ℕ) (hj : (Pair.top t j : Pair T).InRange D.R.m)
    {f : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ} (hf : IsThetaFunO W.ψ _ _ f)
    (a : FinPt G (.top j)) (b h : FinPt G (.top (j + 1))) :
    fockComp W B (.top t j) f a (b * h) = fockComp W B (.top t j) (W.om (.top t j) (G.toPair (.top t j) 1 h.1) f) a b := by
  unfold fockComp
  congr 1
  funext k
  unfold jetTab kerFin GridData.Weil.ker thetaKO
  have e1 : G.toPair (.top t j) (a : GA D (G.V (Pair.top t j : Pair T).small)) ((b * h : FinPt G (.top (j + 1))) : GA D _) =
      G.toPair (.top t j) a b * G.toPair (.top t j) 1 h.1 := by
    simp [GridData.toPair, Prod.ext_iff]
  have e2 : G.toPair (.top t j) 1 h.1 = ((1 : GA D _), h.1) := rfl
  rw [e1, map_mul, Module.End.mul_apply, e2]
  unfold fockIn
  rw [GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om _) (W.om_is _ hj) W.θ W.θ_is 1 (one_mem _) h.1 h.2 _ _ _ _ f _ hf]

theorem update_top_eq {a b : ℕ} (h : a = b) (x : ∀ j, FinPt G (.top j)) (v : FinPt G (.top a)) :
    Function.update x a v b = h ▸ v := by
  subst h; simp

theorem cast_mul_top {a b : ℕ} (h : a = b) (x : ∀ j, FinPt G (.top j)) (p : FinPt G (.top a)) :
    (h ▸ (x a * p) : FinPt G (.top b)) = x b * (h ▸ p : FinPt G (.top b)) := by
  subst h; rfl

theorem cast_conj_top {a b : ℕ} (h : a = b) (u : ∀ X : Node, FinPt G X) (p : FinPt G (.top a)) :
    (h ▸ ((u (.top a))⁻¹ * p * u (.top a)) : FinPt G (.top b)) = (u (.top b))⁻¹ * (h ▸ p : FinPt G (.top b)) * u (.top b) := by
  subst h; rfl

end GlobalTheory.LastColumnMove

namespace GlobalTheory.LastColumnMove

theorem colMapV_update_last : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (fs : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ) (x : ∀ j, FinPt G (.top j)) (g : FinPt G (.top D.R.m)),
    IsThetaFunO W.ψ (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))) (fs (lastIx D)) →
    colMapV S fs (Function.update x D.R.m (x D.R.m * g)) = colMapV S (Function.update fs (lastIx D) (colShift S t g (fs (lastIx D)))) x := by
  intro D T L sc G W U S t fs x g hf
  unfold colMapV
  refine congrArg (fun k => LinearMap.comp (chainTo (V := fun j => VV ℂ (wt G (.top j))) k D.R.m) _) ?_
  funext j
  by_cases hjm : j < D.R.m
  · rw [dite_eq_left hjm, dite_eq_left hjm]
    by_cases hj1 : j + 1 < D.R.m
    · have h1 : j ≠ D.R.m := by omega
      have h2 : j + 1 ≠ D.R.m := by omega
      have h3 : (⟨j, hjm⟩ : Fin D.R.m) ≠ lastIx D := by
        intro h; have := congrArg Fin.val h; simp [lastIx] at this; omega
      rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
    · obtain rfl : j = (lastIx D : ℕ) := by simp [lastIx]; omega
      have h1 : ((lastIx D : ℕ)) ≠ D.R.m := by have := lastIx_succ D; omega
      rw [Function.update_of_ne h1, update_top_eq (lastIx_succ D), cast_mul_top (lastIx_succ D)]
      have e : ∀ a p v : FinPt G (.top ((lastIx D : ℕ) + 1)), a * p * v = a * v * (v⁻¹ * p * v) := by
        intro a p v; group
      rw [e, ← cast_conj_top (lastIx_succ D) S.N.u]
      have hf' : IsThetaFunO W.ψ _ _ (fs ⟨(lastIx D : ℕ), hjm⟩) := hf
      rw [fockComp_mul_right _ t _ (inRange_top t (lastIx D)) hf',
        show Function.update fs (lastIx D) (colShift S t g (fs (lastIx D))) ⟨(lastIx D : ℕ), hjm⟩ =
          colShift S t g (fs (lastIx D)) from Function.update_self _ _ _]
      rfl
  · rw [dite_eq_right hjm, dite_eq_right hjm]

end GlobalTheory.LastColumnMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceLevelOfEmbeddingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_level_of_embedding : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (h : GA D A), Lev.finE B (stabilizerEmbedding d h) ∈ congLev D.sp.cm B.gram (d.lat Λ 𝔟) 𝔪 → Lev.finE A h ∈ congLev D.sp.cm A.gram Λ 𝔪 := by
  first | exact @GlobalTheory.LevRestrict.finE_mem_congLev | exact GlobalTheory.LevRestrict.finE_mem_congLev | (intros; apply GlobalTheory.LevRestrict.finE_mem_congLev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruencePreimageVolumeFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitaryEmbeddingVolume

open Topology

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}


set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem isClosedEmbedding_unitaryEmbedding (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) : IsClosedEmbedding (stabilizerEmbedding d) := by
  haveI : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  set P' := (frameMat B A d.ι).map (incA D)
  set Q' := (GlobalTheory.UnitaryEmbeddingProperties.qM d).map (incA D)
  have hv : Continuous fun g : GA D B => mt B g := Units.continuous_val.comp continuous_subtype_val
  have hvi : Continuous fun g : GA D B => mt B g⁻¹ := Units.continuous_coe_inv.comp continuous_subtype_val
  let Φ : GA D B → Matrix (Fin A.rank) (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E) ×
      (Matrix (Fin A.rank) (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E))ᵐᵒᵖ :=
    fun g => (Q' * mt B g * P', MulOpposite.op (Q' * mt B g⁻¹ * P'))
  have hΦ : Continuous Φ :=
    ((continuous_const.matrix_mul hv).matrix_mul continuous_const).prodMk
      (MulOpposite.continuous_op.comp ((continuous_const.matrix_mul hvi).matrix_mul continuous_const))
  let φ : GA D A →* GA D B := MonoidHom.mk' (stabilizerEmbedding d) (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d)
  have hcomp : Φ ∘ stabilizerEmbedding d = (Units.embedProduct _) ∘ (fun h : GA D A => matHom A h) := by
    funext h
    have e : stabilizerEmbedding d h⁻¹ = (stabilizerEmbedding d h)⁻¹ := map_inv φ h
    simp only [Function.comp_apply, Φ, Units.embedProduct_apply]
    refine Prod.ext ?_ ?_
    · exact (GlobalTheory.UnitaryEmbeddingGroup.matA_eq d h).symm
    · show MulOpposite.op (Q' * mt B (stabilizerEmbedding d h)⁻¹ * P') = _
      rw [← e]
      exact congrArg MulOpposite.op (GlobalTheory.UnitaryEmbeddingGroup.matA_eq d h⁻¹).symm
  have hind : IsInducing (stabilizerEmbedding d) := by
    refine IsInducing.of_comp (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding d) hΦ ?_
    rw [hcomp]
    exact Units.isEmbedding_embedProduct.isInducing.comp (IsInducing.subtypeVal (t := ((HR (AF D.host.F) D.sp.cm.sig A.gram : Subgroup _) : Set (GL (Fin A.rank) (AF D.host.F ⊗[D.host.F] D.host.E)))))
  have hrange : Set.range (stabilizerEmbedding d) = {g : GA D B | mt B g * d.a.map (incA D) = d.a.map (incA D)} := by
    ext g
    constructor
    · rintro ⟨h, rfl⟩
      exact GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_fixes_vectors d h
    · intro hg
      exact GlobalTheory.UnitaryEmbeddingGroup.mem_range_of_fix d hε g hg
  have hcl : IsClosed (Set.range (stabilizerEmbedding d)) := by
    rw [hrange]
    haveI : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
    exact isClosed_eq (hv.matrix_mul continuous_const) continuous_const
  exact ⟨⟨hind, GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_injective d⟩, hcl⟩

end GlobalTheory.UnitaryEmbeddingVolume

namespace GlobalTheory.UnitaryEmbeddingVolume

open Topology

theorem vol_pos_lt_top : ∀ (D : D7) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)),
    IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ μ : Measure (GfC Y), μ.IsHaarMeasure →
      MeasurableSet {b : GfC Y | Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪} ∧
      0 < μ {b : GfC Y | Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪} ∧
      μ {b : GfC Y | Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪} < ⊤ := by
  intro D Y V d Λ 𝔪 hΛ h𝔪 μ hμ
  obtain ⟨hU, hK⟩ := congLev_open_compact V (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V Λ hΛ) h𝔪
  set S := {b : GfC Y | Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪}
  have hc : Continuous fun b : GfC Y => stabilizerEmbedding d (b : GA D Y) :=
    (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding d).comp continuous_subtype_val
  have hS : S = (fun b : GfC Y => stabilizerEmbedding d (b : GA D Y)) ⁻¹'
      (((congLev D.sp.cm V.gram Λ 𝔪).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := rfl
  have hopen : IsOpen S := by
    rw [hS]; exact hU.preimage hc
  have h1 : (1 : GfC Y) ∈ S := by
    show Lev.finE V (stabilizerEmbedding d ((1 : GfC Y) : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪
    rw [OneMemClass.coe_one, show stabilizerEmbedding d (1 : GA D Y) = 1 from
      map_one (MonoidHom.mk' (stabilizerEmbedding d) (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d)), map_one]
    exact (congLev D.sp.cm V.gram Λ 𝔪).one_mem
  have hce : IsClosedEmbedding fun b : GfC Y => stabilizerEmbedding d (b : GA D Y) :=
    (isClosedEmbedding_unitaryEmbedding d one_ne_zero).comp (GlobalTheory.Ker.CongTop.isClosed_GfC Y).isClosedEmbedding_subtypeVal
  have hsub : S ⊆ (fun b : GfC Y => stabilizerEmbedding d (b : GA D Y)) ⁻¹'
      ((Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪) : Subgroup (GA D V)) : Set (GA D V)) := by
    intro b hb
    refine ⟨?_, hb⟩
    show stabilizerEmbedding d (b : GA D Y) ∈ GfC V
    rw [GlobalTheory.UnitaryEmbeddingGroup.mem_GfC_iff, ← GlobalTheory.UnitaryEmbeddingGroup.map_eq_one_iff d, ← GlobalTheory.UnitaryEmbeddingGroup.mem_GfC_iff]
    exact b.2
  refine ⟨hopen.measurableSet, hopen.measure_pos μ ⟨1, h1⟩, ?_⟩
  exact (measure_mono hsub).trans_lt (hce.isCompact_preimage hK).measure_lt_top

end GlobalTheory.UnitaryEmbeddingVolume
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeIntegralUnitsEqResidueCharProductStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameHecke_integralUnits_eq_residueCharProduct : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (e : AE D) (P : Finset (Pl D.host.E)) (cR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), ChrEq c χ → (∀ PP, χ.TameAt PP) → IsIdemSum e P → (∀ PP, PP ∉ P → (¬ ∃ PP' ∈ P, Lev.IsConjPl PP' PP) → χ.UnrAt PP) → (∀ PP ∈ P, IsRes χ PP (cR PP)) → TameOn c e P cR := by
  first | exact @GlobalTheory.TameProd.tameOn_of_tame | exact GlobalTheory.TameProd.tameOn_of_tame | (intros; apply GlobalTheory.TameProd.tameOn_of_tame <;> assumption)
end

