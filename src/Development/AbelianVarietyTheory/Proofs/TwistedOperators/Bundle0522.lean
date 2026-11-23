module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslatesSpanDenseThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelIsometryHalfLatticeVolumeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0448
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsInnerEqFockInnerProductMulNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOperatorActsByNoncompactQuadraticOps
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteThetaLiftLocalVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0481
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeRowMulVecMemModulusScaledCompletion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.DepthRowLem

variable {D : D7}

theorem pairA_mul (α β : Af D.host.F) : pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) :=
  Prod.ext (mul_zero _) rfl

theorem intAf_mul {α β : Af D.host.F} (hα : α ∈ intAf D.host.F) (hβ : β ∈ intAf D.host.F) : α * β ∈ intAf D.host.F :=
  fun v => by rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem mulVec_mem_smul {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) {x : Matrix (Fin m) (Fin n) D.host.E}
    (hx : x ∈ 𝔪 • homLat Λ Λ') {y : Fin n → D.host.E} (hy : y ∈ Λ) : x *ᵥ y ∈ 𝔪 • Λ' := by
  refine Submodule.smul_induction_on hx (fun a ha h hh => ?_) (fun x x' hx hx' => ?_)
  · rw [smul_mulVec]; exact Submodule.smul_mem_smul ha (hh y hy)
  · rw [add_mulVec]; exact add_mem hx hx'


open GlobalTheory.FinPl in
theorem tmul_mem_latMul {T : HSp D} {Λ' : Lat T} (𝔪 : Ideal (𝓞 D.host.E)) {P : Pl D → Prop} {γ : Af D.host.F}
    (hγ : γ ∈ intAf D.host.F) (hγP : ∀ v, ¬ P v → evalV D.host.F v γ = 0) {w : Fin T.rank → D.host.E} (hw : w ∈ 𝔪 • Λ') :
    (fun r => pairA D.host.F 0 γ ⊗ₜ[D.host.F] w r) ∈
      latMul T {a | a ∈ ((𝔪 : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)} Λ' P := by
  refine Submodule.smul_induction_on hw (fun m hm l hl => ?_) (fun w w' hw hw' => ?_)
  · refine AddSubgroup.subset_closure ⟨γ, hγ, hγP, algebraMap (𝓞 D.host.E) D.host.E m,
      (FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).2 ⟨m, hm, rfl⟩, l, hl, ?_⟩
    funext r
    simp only [Pi.smul_apply, Algebra.smul_def]
  · have : (fun r => pairA D.host.F 0 γ ⊗ₜ[D.host.F] (w + w') r) =
        (fun r => pairA D.host.F 0 γ ⊗ₜ[D.host.F] w r) + (fun r => pairA D.host.F 0 γ ⊗ₜ[D.host.F] w' r) := by
      funext r; simp only [Pi.add_apply, TensorProduct.tmul_add]
    rw [this]; exact add_mem hw hw'


open GlobalTheory.FinPl in
theorem mulVec_mem_latMul {S T : HSp D} {Λ : Lat S} {Λ' : Lat T} (𝔪 : Ideal (𝓞 D.host.E)) {P : Pl D → Prop}
    {Z : Mx D T.rank S.rank} (hZ : Z ∈ hatMx (𝔪 • homLat Λ Λ')) {y : Fin S.rank → AE D} (hy : y ∈ latV S Λ P) :
    Z *ᵥ y ∈ latMul T {a | a ∈ ((𝔪 : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)} Λ' P := by
  change y ∈ AddSubgroup.closure _ at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβ, hβP, a, ha, y₀, hy₀, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at ha
    subst ha
    change Z ∈ AddSubgroup.closure _ at hZ
    induction hZ using AddSubgroup.closure_induction with
    | mem Z hZ =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hZ
      have e : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] x i j) *ᵥ
          (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * y₀ i)) =
          fun r => pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] (x *ᵥ y₀) r := by
        funext r
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, pairA_mul, one_mul,
          ← TensorProduct.tmul_sum]
      rw [e]
      refine tmul_mem_latMul 𝔪 (intAf_mul hα hβ) (fun v hv => ?_) (mulVec_mem_smul 𝔪 hx hy₀)
      rw [map_mul, hβP v hv, mul_zero]
    | zero => rw [zero_mulVec]; exact zero_mem _
    | add Z Z' _ _ h h' => rw [add_mulVec]; exact add_mem h h'
    | neg Z _ h => rw [neg_mulVec]; exact neg_mem h
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [mulVec_add]; exact add_mem h h'
  | neg y _ h => rw [mulVec_neg]; exact neg_mem h

end GlobalTheory.DepthRowLem

theorem GlobalTheory.DepthRowLem.latRow_mulVec : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ Y ∈ latRow G i, ∀ (v : GlobalTheory.FinPl.Pl D) (y : Fin (G.V (.grid (i + 1) 0)).rank → AE D), y ∈ latV _ (G.Λ (.grid (i + 1) 0)) (· = v) → (e • Y) *ᵥ y ∈ GlobalTheory.FinPl.latMul _ {a | a ∈ ((G.modul : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)} (G.Λ (.grid i 0)) (· = v) := by
  intro D _ T L μ0 _ sc G W M _ i _ e he Y hY v y hy
  exact GlobalTheory.DepthRowLem.mulVec_mem_latMul _ (hY.2 e he) hy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivEqZeroOfEven
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting
open scoped TensorProduct ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

theorem unitary (D : D7) : Unitary D := by
  intro ψ S T χS χT om hW
  have hstd := hW.std
  obtain ⟨μ₀, 𝓕₀, h₀⟩ := GlobalTheory.ThetaAllChar.covolOneExists (D := D) S T
  refine ⟨⟨(μ₀, 𝓕₀), h₀⟩, fun q hq f₁ f₂ hf₁ hf₂ => ?_⟩
  have L := _root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T q.1 q.2 hstd hq f₁ f₂ hf₁ hf₂
  refine ⟨fun c => GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul c hf₁) hf₂, L.1, L.2.2.2.2.2.1,
    L.2.2.2.2.2.2.2, fun w => ⟨?_, (L.2.2.2.2.2.2.1 w).1⟩, fun p => ⟨hW.om_pres p f₁ hf₁, ?_⟩,
    _root_.GlobalTheory.WeilNormCont.continuous_meanSquareNorm_weilRep_sub D ψ S T χS χT om q.1 q.2 hW hq f₁ f₂ hf₁ hf₂⟩
  · exact (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd S T).1 w f₁ hf₁
  · exact GlobalTheory.WeilInner.om_inner D ψ S T χS χT om hW q.1 q.2 hq p f₁ f₂ hf₁ hf₂

theorem restrictedTensor (D : D7) : RestrictedTensor D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ
  have hstd := base_std hB
  have hinf := base_inf hB
  refine ⟨fun p f hf => ⟨((_root_.GlobalTheory.PlaceStable.heis_stable D ψ θ S T sS sT ΛS ΛT hstd hinf f hf.1).2 p hf).1,
      _root_.GlobalTheory.LocalFactorUnitary.isLocal_om_gAt D ψ θ S T χS χT om sS sT ΛS ΛT hW hinf p f hf⟩,
    fun x hx => _root_.GlobalTheory.PureTensorExists.existsUnique_isPure D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x hx, fun f hf ε hε => ?_,
    fun x f hx => ⟨fun w => GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hx w,
      fun g h => _root_.GlobalTheory.PlaceTensor.PureOm.isPure_om D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ x f hx g h⟩⟩
  obtain ⟨f', hf', hlt⟩ := _root_.GlobalTheory.HeisDense.span_translates_dense D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ f hf ε hε
  refine ⟨f', Submodule.span_mono ?_ hf', hlt⟩
  rintro _ ⟨w, rfl⟩
  exact ⟨_, GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ (fun _ => f₀) f₀
    (_root_.GlobalTheory.LocalPure.isPure_base_and_local D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ).1 w⟩

theorem coeffProduct (D : D7) : CoeffProduct D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ x₁ f₁ x₂ f₂ h₁ h₂ g h
  exact _root_.GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ _ x₂ _ f₂
    (_root_.GlobalTheory.PlaceTensor.PureOm.isPure_om D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ x₁ f₁ h₁ g h) h₂

theorem cA_cA {D : D7} {e : AE D} {p : Place D} (h : e + cA D e = idem D p) : cA D (cA D e) = e := by
  have hp : cA D (idem D p) = idem D p := (_root_.GlobalTheory.PlaceTensor.idem_spec D).2.2.1 p
  have h2 : cA D e + cA D (cA D e) = cA D e + e := by
    rw [← map_add (f := _), h, hp, ← h, add_comm]
  exact add_left_cancel h2

theorem isSplitIdem_cA {D : D7} {e : AE D} {p : Place D} (he : IsSplitIdem D e) (h : e + cA D e = idem D p) :
    IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hv, hε⟩ := he
  have hcc := cA_cA h
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hv, ?_⟩
  · rw [hcc, mul_comm, h2]
  · rw [hcc, add_comm, hε]

theorem splitModel (D : D7) : SplitModel D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v φ e he BS BT
  have hC := _root_.GlobalTheory.PlaceCoord.isCoord_mapCo D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he BS BT
  refine ⟨(_root_.GlobalTheory.PlaceModelOnto.placeModel_onto_local D ψ θ S T sS sT ΛS ΛT f₀ hB v e he.1 he.2.1).1, fun Tm hTm => ?_⟩
  have M := _root_.GlobalTheory.SplitCoordModel.bijOn_and_om_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v e e he.1 he.2.1 (Or.inl rfl)
    T.rank S.rank (mapCo φ S T BS BT) hC.1 Tm hTm
  rw [onHalf_eq_pull]
  exact ⟨M.1, fun ν hν => _root_.GlobalTheory.PlaceIsometry.placeModel_isometry D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ v e he.1 T.rank S.rank
    (mapCo φ S T BS BT) hC.1 Tm hTm ν hν, fun g h hg hh x y hx hy Φ hΦ =>
    M.2 g h hg hh x y hx hy (grpCo φ S BS g) (grpCo φ T BT h) (fun t => hC.2 g h t) Φ hΦ⟩

theorem splitModelAdj (D : D7) : SplitModelAdj D := by
  intro ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v φ e he BS BT
  have hC := _root_.GlobalTheory.PlaceTensor.adjCo_isCoord D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he BS BT
  have hs : IsSplitIdem D (cA D e) := isSplitIdem_cA he.1 he.2.1
  have hsum : cA D e + cA D (cA D e) = idem D (.inl v) := by
    rw [cA_cA he.2.1, add_comm]
    exact he.2.1
  refine ⟨(_root_.GlobalTheory.PlaceModelOnto.placeModel_onto_local D ψ θ S T sS sT ΛS ΛT f₀ hB v (cA D e) hs hsum).1, fun Tm hTm => ?_⟩
  have M := _root_.GlobalTheory.SplitCoordModel.bijOn_and_om_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ v e (cA D e) he.1 he.2.1 (Or.inr rfl)
    S.rank T.rank (adjCo φ S T BS BT) hC.1 Tm hTm
  rw [onHalfAdj_eq_pull]
  exact ⟨M.1, fun ν hν => _root_.GlobalTheory.PlaceIsometry.placeModel_isometry D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ v (cA D e) hs S.rank T.rank
    (adjCo φ S T BS BT) hC.1 Tm hTm ν hν, fun g h hg hh x y hx hy Φ hΦ =>
    M.2 g h hg hh x y hx hy (grpCo φ T BT h) (grpCo φ S BS g) (fun t => hC.2 g h t) Φ hΦ⟩

theorem deriv_eq_zero_of_even {c : ℝ → ℂ} {a : ℂ} (h : HasDerivAt c a 0) (he : ∀ t, c (-t) = c t) : a = 0 := by
  have hn : HasDerivAt (fun t : ℝ => -t) (-1) 0 := (hasDerivAt_id' (0 : ℝ)).neg
  have h0 : HasDerivAt c a (-(0 : ℝ)) := by rwa [neg_zero]
  have h1 := h0.scomp (0 : ℝ) hn
  have h2 : (c ∘ fun t : ℝ => -t) = c := funext fun t => he t
  rw [h2] at h1
  have h3 := h.unique h1
  rw [neg_one_smul] at h3
  linear_combination h3 / 2

private theorem exists_conj_mul_eq_mul {ι : Type*} {n : ℕ} (C C' : ι → Matrix (Fin n) (Fin n) ℂ) (h : ∀ i, C i * C' i = 1)
    (s B : ι → Matrix (Fin n) (Fin n) ℂ) :
    ∃ s' B' : ι → Matrix (Fin n) (Fin n) ℂ, (∀ i, s' i * C i = C i * s i) ∧ ∀ i, B' i = C i * B i := by
  refine ⟨fun i => C i * s i * C' i, fun i => C i * B i, fun i => ?_, fun i => rfl⟩
  have h' : C' i * C i = 1 := mul_eq_one_comm.mp (h i)
  simp only [Matrix.mul_assoc, h', Matrix.mul_one]

theorem fockModel (D : D7) : FockModel D := by
  intro ψ θ S T χS χT om hW hθ τ
  obtain ⟨mS, mT, hm⟩ := _root_.GlobalTheory.VacCharAtPlace.vacuum_char_at_place D ψ θ S T χS χT om hW hθ τ
  refine ⟨mS, mT, ?_⟩
  intro sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT f hf hvac P
  have hstd := hW.std
  have hPT : ∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q) := by
    intro Q
    obtain ⟨sS', BS', hS', hBS'⟩ := exists_conj_mul_eq_mul _ _
      (fun ρ => GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) ρ (1 : GA D S)) sS BS
    obtain ⟨sT', BT', hT', hBT'⟩ := exists_conj_mul_eq_mul _ _
      (fun ρ => GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) ρ (1 : GA D T)) sT BT
    exact (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS' BS BS' sT sT' BT BT' 1 1
      hS' hT' hBS' hBT' f hf Q).1
  obtain ⟨μ₀, 𝓕₀, h₀⟩ := GlobalTheory.ThetaAllChar.covolOneExists (D := D) S T
  refine ⟨hPT P, fun μ 𝓕 hμ Q => _root_.GlobalTheory.FockIsometry.ipO_pureTensorO D ψ θ S T hstd hθ sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT
      f hf hvac μ 𝓕 hμ P Q,
    fun κS κT hκS hκT g h hg hh => _root_.GlobalTheory.FockCompact.om_pureTensorO_compact D ψ θ S T χS χT om hW hθ sS BS sT BT pS pT hpS hpT hsS hsT
      hBS hBT f hf τ κS κT hκS hκT g h hg hh _
      (hm sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT f hf hvac κS κT hκS hκT g h hg hh) P,
    fun YS YT hYS hYT w => ?_⟩
  have hL := _root_.GlobalTheory.VacuumEven.coeff_even D ψ θ S T χS χT om hW hθ sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT τ YS YT hYS hYT
  obtain ⟨Gn, hGn⟩ := _root_.GlobalTheory.PlaceTensor.GenPair.exists_generator D ψ θ S T χS χT om hW hθ τ _ hL.1 _ hL.2.1

  have key := _root_.GlobalTheory.FockLieQuad.acts_by_fockP D ψ θ S T hstd hθ sS BS sT BT pS pT hpS hpT hsS hsT hBS hBT τ YS YT hYS hYT μ₀ 𝓕₀ h₀ Gn
    (fun f' hf' => ⟨(hGn f' hf').1, (hGn f' hf').2.1, (hGn f' hf').2.2.1⟩) f hf hvac
    (fun g hg hgv => deriv_eq_zero_of_even ((hGn f hf).2.2.2.2 μ₀ 𝓕₀ h₀ g hg)
      (fun t => hL.2.2 f g hf hvac hg hgv μ₀ 𝓕₀ h₀ t)) P
  rw [← key]
  exact (hGn _ (hPT P)).2.2.2.1 w

theorem placeModels : ∀ D : D7, PlaceModels D := fun D =>
  ⟨unitary D, restrictedTensor D, coeffProduct D, splitModel D, splitModelAdj D, _root_.GlobalTheory.SplitLatticeHalves.splitLattice D, _root_.GlobalTheory.PlaceTensor.inertVacuumFixed D,
    _root_.GlobalTheory.PlaceTensor.splitVacuumFixed D, fockModel D, _root_.GlobalTheory.FockPureTensor.fockPure D, _root_.GlobalTheory.AdjVecLocal.thetaVecLocal D, GlobalTheory.T.thetaChainStepVector_localPureTensor D⟩

end GlobalTheory.PlaceTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleMixedModelClassStableFlatVacua
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFinStab

variable {D : D7}

theorem symplO_eq_two (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add (f := _)]
  norm_num

theorem heisO_comm_of (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {a b : WO S T} (g : WO S T → ℂ)
    (h : ψ (symplOH S T a b + symplOH S T a b) = 1) :
    heisO ψ S T a (heisO ψ S T b g) = heisO ψ S T b (heisO ψ S T a g) := by
  rw [GlobalTheory.FinTranslate.heisO_heisO, GlobalTheory.FinTranslate.heisO_heisO, GlobalTheory.FinTranslate.symplOH_skew S T a b, add_comm b a]
  congr 1
  calc ψ (symplOH S T a b) = ψ ((symplOH S T a b + symplOH S T a b) + -symplOH S T a b) := by congr 1; ring
    _ = ψ (-symplOH S T a b) := by rw [AddChar.map_add_eq_mul, h, one_mul]

theorem heisO_smul'' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (c : ℂ) (g : WO S T → ℂ) :
    heisO ψ S T w (c • g) = c • heisO ψ S T w g := by
  funext z
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem fin_of_mxAt {m n : ℕ} {a : Mx D m n} (h : MxAt (fun _ => True) a) : a.map (infPart D) = 0 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  exact RingHom.mem_ker.1 (Ideal.mem_inf.1 (h i j)).1

theorem fin_mul_left {k m n : ℕ} (M : Mx D k m) {u : Mx D m n} (hu : u.map (infPart D) = 0) :
    (M * u).map (infPart D) = 0 := by
  rw [Matrix.map_mul, hu, Matrix.mul_zero]

theorem fin_mul_right {k m n : ℕ} {u : Mx D k m} (hu : u.map (infPart D) = 0) (M : Mx D m n) :
    (u * M).map (infPart D) = 0 := by
  rw [Matrix.map_mul, hu, Matrix.zero_mul]

theorem isHalf_mul_left {e : AE D} {k m n : ℕ} (M : Mx D k m) {u : Mx D m n} (hu : IsHalf e u) : IsHalf e (M * u) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, hu l j]

theorem isHalf_mul_right {e : AE D} {k m n : ℕ} {u : Mx D k m} (hu : IsHalf e u) (M : Mx D m n) : IsHalf e (u * M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, hu i l]

end GlobalTheory.AscFinStab

namespace GlobalTheory.AscFinStab

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ}

def Comm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : WO S T) : Prop :=
  ∀ g : WO S T → ℂ, heisO ψ S T a (heisO ψ S T b g) = heisO ψ S T b (heisO ψ S T a g)

theorem mem_cls_of_comm (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ)
    (y : Mx D V₀.rank σ) {Φ : WO V W → ℂ} (hΦ : Φ ∈ cls dV dW p x y ψ) (c : WO V W)
    (hθ : IsThetaFunO ψ V W (heisO ψ V W c Φ))
    (h₁ : ∀ a ∈ p.A₁, Comm ψ V W (dV.extX W a) c) (h₂ : ∀ a ∈ p.A₂, Comm ψ V W (dV.extY W a) c)
    (h₃ : ∀ ξ ∈ p.B₁, Comm ψ V W (dV.ext0 W (dW.incX V₀ ξ)) c)
    (h₄ : ∀ η ∈ p.B₂, Comm ψ V W (dV.ext0 W (dW.incY V₀ η)) c)
    (h₅ : ∀ u ∈ p.Γ₀, Comm ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u)) c)
    (h₆ : ∀ e, IsSplitIdem D e → ∀ u ∈ p.Γ₀, IsHalf e (dV.ext0 W (dW.inc0 V₀ u)) → Comm ψ V W (dV.ext0 W (dW.inc0 V₀ u)) c) :
    heisO ψ V W c Φ ∈ cls dV dW p x y ψ := by
  simp only [cls, Set.mem_ofPred_eq] at hΦ ⊢
  obtain ⟨_, hA₁, hA₂, hB₁, hB₂, hL⟩ := hΦ
  refine ⟨hθ, fun a ha => ?_, fun a ha => ?_, fun ξ hξ => ?_, fun η hη => ?_, ?_⟩
  · rw [h₁ a ha, hA₁ a ha]
  · rw [h₂ a ha, hA₂ a ha, heisO_smul'']
  · rw [h₃ ξ hξ, hB₁ ξ hξ, heisO_smul'']
  · rw [h₄ η hη, hB₂ η hη]
  · unfold IsLatVac
    refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
    · obtain ⟨u₀, hu₀, rfl⟩ := AddSubgroup.mem_map.1 hu
      have e1 : heisO ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u₀)) Φ = Φ := hL.1 (dV.ext0 W (dW.inc0 V₀ u₀)) hu
      show heisO ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u₀)) (heisO ψ V W c Φ) = heisO ψ V W c Φ
      rw [h₅ u₀ hu₀, e1]
    · obtain ⟨u₀, hu₀, rfl⟩ := AddSubgroup.mem_map.1 hu
      have e1 : heisO ψ V W (dV.ext0 W (dW.inc0 V₀ u₀)) Φ = Φ := hL.2 e he (dV.ext0 W (dW.inc0 V₀ u₀)) hu hh
      show heisO ψ V W (dV.ext0 W (dW.inc0 V₀ u₀)) (heisO ψ V W c Φ) = heisO ψ V W c Φ
      rw [h₆ e he u₀ hu₀ hh, e1]

end GlobalTheory.AscFinStab

namespace GlobalTheory.AscFinStab

theorem cls_stable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∀ Φ ∈ cls dV dW p (rat x₀) y ψ, (∀ w : WO V W, w.map (finPart D) = 0 → heisO ψ V W w Φ ∈ cls dV dW p (rat x₀) y ψ) ∧ (∀ w ∈ Ann ψ V₀ W₀ p.Γ₀, heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Φ ∈ cls dV dW p (rat x₀) y ψ) ∧ VacG ψ V₀ W₀ p.Γ₀ (flatS dV dW s (rat x₀) y Φ) := by
  intro D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hlin p hp Φ hΦ
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  have hΦ' := hΦ
  simp only [cls, Set.mem_ofPred_eq] at hΦ'
  obtain ⟨hθ, -, -, -, -, hL⟩ := hΦ'
  have hJ : ∀ a b : WO V₀ W₀,
      symplOH V W (dV.ext0 W (dW.inc0 V₀ a)) (dV.ext0 W (dW.inc0 V₀ b)) = symplOH V₀ W₀ a b := by
    intro a b
    rw [dV.wittDecomp_sympl_extAnisotropic_extAnisotropic W, dW.wittDecomp_sympl_inclAnisotropic_inclAnisotropic V₀]
  have hfin0 : ∀ u ∈ p.Γ₀, (dV.ext0 W (dW.inc0 V₀ u)).map (infPart D) = 0 := fun u hu =>
    fin_mul_right (fin_mul_left _ (fin_of_mxAt (hp.fin₀ u hu))) _
  have comm0 : ∀ {a b : WO V W}, symplOH V W a b = 0 → Comm ψ V W a b := fun h g =>
    heisO_comm_of ψ g (by rw [h, add_zero, AddChar.map_zero_eq_one])
  refine ⟨fun w hw => ?_, fun w hw => ?_, ?_⟩
  · have cr : ∀ {a : WO V W}, a.map (infPart D) = 0 → Comm ψ V W a w := fun ha =>
      comm0 (GlobalTheory.FinTranslate.symplOH_fin_real ha hw)
    exact mem_cls_of_comm dV dW p _ y hΦ w (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hθ w)
      (fun a ha => cr (fin_mul_right (fin_of_mxAt (hp.a₁.fin a ha)) _))
      (fun a ha => cr (fin_mul_right (fin_of_mxAt (hp.a₂.fin a ha)) _))
      (fun ξ hξ => cr (fin_mul_right (fin_mul_left _ (fin_of_mxAt (hp.b₁.fin ξ hξ))) _))
      (fun η hη => cr (fin_mul_right (fin_mul_left _ (fin_of_mxAt (hp.b₂.fin η hη))) _))
      (fun u hu => cr (by
        rw [← map_nsmul (dV.ext0 W), ← map_nsmul (dW.inc0 V₀)]
        exact hfin0 _ (nsmul_mem hu 2)))
      (fun e _ u hu _ => cr (hfin0 u hu))
  · obtain ⟨hw1, hw2⟩ := hw
    have hc : ∀ u : WO V₀ W₀, ψ (symplO V₀ W₀ w u) = 1 →
        Comm ψ V W (dV.ext0 W (dW.inc0 V₀ u)) (dV.ext0 W (dW.inc0 V₀ w)) := by
      intro u hu g
      refine heisO_comm_of ψ g ?_
      rw [hJ, GlobalTheory.FinTranslate.symplOH_skew V₀ W₀ w u, ← neg_add, AddChar.map_neg_eq_inv, ← symplO_eq_two, hu, inv_one]
    exact mem_cls_of_comm dV dW p _ y hΦ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hθ _)
      (fun a _ => comm0 (dV.wittDecomp_sympl_extIsotropic_extAnisotropic W a _))
      (fun a _ => comm0 (dV.wittDecomp_sympl_extDual_extAnisotropic W a _))
      (fun ξ _ => comm0 (by rw [dV.wittDecomp_sympl_extAnisotropic_extAnisotropic W, dW.wittDecomp_sympl_inclIsotropic_inclAnisotropic V₀]))
      (fun η _ => comm0 (by rw [dV.wittDecomp_sympl_extAnisotropic_extAnisotropic W, dW.wittDecomp_sympl_inclDual_inclAnisotropic V₀]))
      (fun u hu => by
        rw [← map_nsmul (dV.ext0 W), ← map_nsmul (dW.inc0 V₀)]
        exact hc _ (hw1 u hu))
      (fun e he u hu hh => hc u (hw2 e he u hu (by
        have h' := isHalf_mul_right (isHalf_mul_left dW.p0 hh) dV.j0
        have eq : dW.p0 * (dV.ext0 W (dW.inc0 V₀ u)) * dV.j0 = u := by
          rw [dV.matrixExtendByZero_apply, dW.wittDecomp_inclAnisotropicHom_apply]
          simp only [← Matrix.mul_assoc, dW.p0_j0, Matrix.one_mul]
          rw [Matrix.mul_assoc, dV.p0_j0, Matrix.mul_one]
        rwa [eq] at h')))
  · have hfl := GlobalTheory.FlatHeis.flatAt_heisO D ψ hstd V V₀ W W₀ ρ σ dV dW s.vS s.vT s.vU (rat x₀) y Φ hθ
    unfold VacG IsLatVac
    refine ⟨(GlobalTheory.Unf.Flat.flatLaw D ψ hstd V V₀ W W₀ ρ σ dV dW s.vS s.vT s.vU x₀ hlin y Φ hθ).2,
      fun u hu => ?_, fun e he u hu hh => ?_⟩
    · have e1 : heisO ψ V W (2 • dV.ext0 W (dW.inc0 V₀ u)) Φ = Φ :=
        hL.1 _ (AddSubgroup.mem_map_of_mem _ hu)
      show heisO ψ V₀ W₀ (2 • u) (flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ) =
        flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ
      rw [← hfl.2.1, map_nsmul (dW.inc0 V₀), map_nsmul (dV.ext0 W), e1]
    · have e1 : heisO ψ V W (dV.ext0 W (dW.inc0 V₀ u)) Φ = Φ :=
        hL.2 e he _ (AddSubgroup.mem_map_of_mem _ hu) (isHalf_mul_right (isHalf_mul_left _ hh) _)
      show heisO ψ V₀ W₀ u (flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ) =
        flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν (rat x₀) y Φ
      rw [← hfl.2.1, e1]

end GlobalTheory.AscFinStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledFirstFactorMemDoubledLatticeStabilizerStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledFirstFactor_mem_doubledLatticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)),
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, GlobalTheory.InertDbl.inlD σ W k ∈ GlobalTheory.InertDbl.KAtD σ W v := by
  first | exact @GlobalTheory.InertDbl.inlD_mem_KAtD | exact GlobalTheory.InertDbl.inlD_mem_KAtD | (intros; apply GlobalTheory.InertDbl.inlD_mem_KAtD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledStabilizerGeneratedDiagAntidiagSplitPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledStabilizer_generated_diag_antidiag_splitPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    (2 : 𝓞 F) ∉ v.asIdeal → 3 < Ideal.absNorm v.asIdeal → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.W),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PAnti σ G.W → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, g ∈ H := by
  first | exact @GlobalTheory.DblVac.gen_diag_anti_split | exact GlobalTheory.DblVac.gen_diag_anti_split | (intros; apply GlobalTheory.DblVac.gen_diag_anti_split <;> assumption)
end

