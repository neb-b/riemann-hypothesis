module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiesOnRamOfInvariant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0279
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInnerProductSmoothVectorsTensor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThreeOrbitsGluedCoreAtPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)

namespace GlobalTheory.FinPl

theorem sec_mul_sec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {D : D7}
    (p : SplitPt D k) (a : AE D) (u : k) : p.sec (p.pr a * u) = a * p.sec u := by
  have h1 : p.sec (p.pr a * u) = p.sec (p.pr (a * p.sec u)) := by rw [map_mul p.pr, p.pr_sec]
  have h2 : p.e * p.sec u = p.sec u := by rw [← p.sec_pr, p.pr_sec]
  rw [h1, p.sec_pr, mul_left_comm, h2]

theorem mulVec_sec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {D : D7}
    (p : SplitPt D k) {r : ℕ} (m : Matrix (Fin r) (Fin r) (AE D)) (u : Fin r → k) :
    m *ᵥ (fun i => p.sec (u i)) = fun i => p.sec ((m.map p.pr *ᵥ u) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, map_sum, Matrix.map_apply, sec_mul_sec]

theorem single_mem_gluedS {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [DecidableEq n] (q : Unif k) (P : Pair k n) :
    (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∈ gluedS q 1 P.ker P.vec := by
  refine GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨q.1, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
  · have h0 : (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∘ Sum.inl = 0 := by
      funext j
      simp
    rw [h0, zero_sub]
    exact neg_mem (Pair.smul_mem_ker q.mem_max P.hasVal_vec.mem)
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [Pi.single_eq_same, Unif.inv, inv_mul_cancel₀ q.ne_zero]

theorem zero_col_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n), GluedCore B L₀ q β β₀ P → ∀ γ : GA D B.V₀, (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) → mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) → mt B.V₀ γ⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k)) i)) ∈ latV B.V₀ L₀ (· = p.v) := by
  intro D k _ _ _ _ p n _ _ q σ B L₀ β β₀ P hg γ hpres
  have he : p.sec 1 = p.e := by rw [← map_one p.pr, p.sec_pr, mul_one]
  have hvec : p.sec 1 • ratV (vecB B.o B.ζ) =
      fun i => p.sec ((β₀.b *ᵥ (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k)) i) := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, he, mulVec_single_one, hg.sum]
    simp [p.sec_pr]
  have hmem : p.sec 1 • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) := by
    rw [hg.unit.2, hvec, ← hg.lat]
    exact single_mem_gluedS q P
  have := hpres _ hmem
  rwa [hg.unit.2, hvec] at this

theorem orbitGlued (D : D7) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ)
      (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n) (β₀ : Frame p B.V₀ (n ⊕ Fin 1))
      (P : Pair k n), IsSelfDualC B.V₀ L₀ → GluedCore B L₀ q β β₀ P →
      ∀ γ ∈ grpAt B.V₀ (· = p.v),
        (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) →
          mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) →
        (∃ a ∈ grpAt B.A (· = p.v), ∃ κ, InK B.V₀ L₀ (· = p.v) κ ∧ γ = B.o.emb (a, 1) * κ) ∨
        ∃ (Λ : Submodule 𝒪[k] (n → k)) (_ : Λ.IsFullLattice k),
          β₀.IsLatMoved γ L₀ (lastKer Λ) ∨ β₀.IsLatMoved γ L₀ (lastPair q Λ).lat := by
  intro k _ _ _ _ p n _ _ q σ B L₀ β β₀ P hsd hg γ hγ hpres
  obtain ⟨hF1, -, -, hF4, -⟩ := _root_.GlobalTheory.FrameAt.frame_facts D k p B.V₀ (n ⊕ Fin 1) β₀
  obtain ⟨h, rfl⟩ := (hF1 γ).1 hγ
  have key : ∀ x, mt B.V₀ (β₀.gl h)⁻¹ *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV B.V₀ L₀ (· = p.v) ↔
      x ∈ h • gluedS q 1 P.ker P.vec := by
    intro x
    rw [← map_inv, mulVec_sec, β₀.gl_mat, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, β₀.b'b,
      Matrix.mul_one, ← mulVec_mulVec, ← hg.lat, GlobalTheory.LatPair.mem_smul_iff]
    rfl
  have hz := (key _).1 (zero_col_mem D k p n q σ B L₀ β β₀ P hg _ hpres)
  have hint : ∀ x ∈ h • gluedS q 1 P.ker P.vec, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k] :=
    fun x hx => _root_.GlobalTheory.FinPl.glued_last_integral D k p n q σ B L₀ β β₀ P hsd hg _ hγ hpres x ((key x).2 hx)
  rcases _root_.GlobalTheory.GluedOrbit.smul_gluedS_cases k n q P h hz hint with ⟨Λ, hΛ, hM | hM⟩ | ⟨g, hM⟩
  · exact Or.inr ⟨Λ, hΛ, Or.inl fun x => by rw [← hM]; exact (key x).symm⟩
  · exact Or.inr ⟨Λ, hΛ, Or.inr fun x => by rw [← hM]; exact (key x).symm⟩
  · obtain ⟨hA1, -⟩ := _root_.GlobalTheory.FrameAt.frame_facts D k p B.A n β
    obtain ⟨Λ₀, -, hΛ₀, hK⟩ := hF4 L₀ hsd
    have hΛG : Λ₀ = gluedS q 1 P.ker P.vec := Submodule.ext fun x => (hΛ₀ x).trans (hg.lat x).symm
    refine Or.inl ⟨β.gl g, (hA1 _).2 ⟨g, rfl⟩, β₀.gl ((embX 1 g)⁻¹ * h), ?_, ?_⟩
    · rw [hK, hΛG, mul_smul, hM, inv_smul_smul]
    · rw [_root_.GlobalTheory.FinPl.emb_gl_sumFrame D k p n σ B β β₀ hg.sum g, ← map_mul, mul_inv_cancel_left]

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitVectorRowsConjugate
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

noncomputable section

namespace GlobalTheory.MiTop.LineV

open GlobalTheory.PiTensorInner

theorem tprod_eq_smul_of_prod_inner {ι : Type} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (a b : ∀ i, E i) (l : ℂ)
    (h : ∀ x : ∀ i, E i, ∏ i, ⟪a i, x i⟫_ℂ = l * ∏ i, ⟪b i, x i⟫_ℂ) :
    PiTensorProduct.tprod ℂ a = (starRingEnd ℂ l) • PiTensorProduct.tprod ℂ b := by
  set w := PiTensorProduct.tprod ℂ a - (starRingEnd ℂ l) • PiTensorProduct.tprod ℂ b with hw
  have hy : ∀ y, ipT y w = 0 := by
    intro y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [hw, map_smul, LinearMap.smul_apply, map_sub, map_smulₛₗ, ipT_tprod, ipT_tprod, h x]
      simp
    | add x y hx hy => rw [map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
  by_contra hne
  have := ipT_pos w (sub_ne_zero.2 hne)
  rw [hy w] at this
  simp at this

end GlobalTheory.MiTop.LineV

namespace GlobalTheory.MiTop.LineV

theorem eq_of_evS_ae {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {θ : InfFam D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {M : DSModel (D.sp.Y 0) S} {J : Set (GA D (D.sp.Y 0))}
    {χ : GA D (D.sp.Y 0) → ℂ} (t : GA D (D.sp.Y 0)) {T T' : SmT M →ₗ[ℂ] (GA D (D.sp.Y 0) → ℂ)}
    (hT : T ∈ MultT θ M J χ) (hT' : T' ∈ MultT θ M J χ) (a b : M.Vec)
    (he : evS X h t (T (PiTensorProduct.tprod ℂ a)) =ᵐ[muX X] evS X h t (T' (PiTensorProduct.tprod ℂ b))) :
    T (PiTensorProduct.tprod ℂ a) = T' (PiTensorProduct.tprod ℂ b) := by
  have hU := (GlobalTheory.MultMem.mem_mult_iff D θ _ _ M J χ _).1 ((mem_multT θ M J χ T).1 hT)
  have hU' := (GlobalTheory.MultMem.mem_mult_iff D θ _ _ M J χ _).1 ((mem_multT θ M J χ T').1 hT')
  have hva : (PiTensorProduct.lift.symm T : MMap M) a = T (PiTensorProduct.tprod ℂ a) := by
    simp [PiTensorProduct.lift_symm]
  have hvb : (PiTensorProduct.lift.symm T' : MMap M) b = T' (PiTensorProduct.tprod ℂ b) := by
    simp [PiTensorProduct.lift_symm]
  have hc := (hU.aut a).cont
  have hl := (hU.aut a).left
  have hc' := (hU'.aut b).cont
  have hl' := (hU'.aut b).left
  rw [← hva, ← hvb] at he ⊢
  generalize (PiTensorProduct.lift.symm T : MMap M) a = f at hc hl he ⊢
  generalize (PiTensorProduct.lift.symm T' : MMap M) b = f' at hc' hl' he ⊢
  let ι : GA D (D.sp.Y 0) ≃ₜ* X.B.I.GA := iotaX X h
  have hQ : ∀ γ ∈ X.B.I.GFset, ι.symm γ ∈ GQ (D.sp.Y 0) := by
    intro γ hγ
    refine (Formalism.IndefR.RationalEmbedding.iota_rat D (ι.symm γ)).2 ?_
    show Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact GlobalTheory.TranslatedEvalInj.castGA_symm_mem _ γ hγ
  let φ : X.B.I.GA → ℂ := fun x => f (ι.symm x * t) - f' (ι.symm x * t)
  have hφc : Continuous φ := by
    have hm : Continuous fun x : X.B.I.GA => ι.symm x * t := ι.symm.continuous.mul continuous_const
    exact (hc.comp hm).sub (hc'.comp hm)
  have hφi : ∀ γ ∈ X.B.I.GFset, ∀ y, φ (γ * y) = φ y := by
    intro γ hγ y
    simp only [φ, map_mul, mul_assoc]
    rw [hl _ (hQ γ hγ), hl' _ (hQ γ hγ)]
  have hae : φ =ᵐ[(X.B.I.muA X.B.μf).restrict X.B.fund] 0 := by
    have he' : evS X h t f =ᵐ[muX X] evS X h t f' := he
    filter_upwards [he'] with x hx
    simp only [φ, Pi.zero_apply, sub_eq_zero]
    exact hx
  have hz := GlobalTheory.TranslatedEvalInj.eq_zero_of_ae_fund X.B.I X.B.μf X.B.fund_spec hφc hφi hae
  funext g
  have e := hz (ι (g * t⁻¹))
  simp only [φ, ContinuousMulEquiv.symm_apply_apply, inv_mul_cancel_right, sub_eq_zero] at e
  exact e

end GlobalTheory.MiTop.LineV

namespace GlobalTheory.MiTop.LineV

theorem line_of_eq {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {θ : InfFam D} {M : DSModel V S}
    {J : Set (GA D V)} {χ : GA D V → ℂ} (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ)
    {T T' : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hT : T ∈ MultT θ M J χ) (hT' : T' ∈ MultT θ M J χ) (v₀ v : M.Vec)
    (h1 : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) (hT0 : T ≠ 0)
    (he : T (PiTensorProduct.tprod ℂ v₀) = T' (PiTensorProduct.tprod ℂ v)) :
    ∃ l : ℂ, l ≠ 0 ∧ PiTensorProduct.tprod ℂ v₀ = l • PiTensorProduct.tprod ℂ v := by
  obtain ⟨ν, 𝓖, hν, h𝓖⟩ := GlobalTheory.RawLift.exists_haar_fundDomain V
  have hUm := (mem_multT θ M J χ T).1 hT
  have hUm' := (mem_multT θ M J χ T').1 hT'
  have hU := (GlobalTheory.MultMem.mem_mult_iff D θ _ _ M J χ _).1 hUm
  set U : MMap M := PiTensorProduct.lift.symm T with hUd
  set U' : MMap M := PiTensorProduct.lift.symm T' with hUd'
  have hval : ∀ x, U x = T (PiTensorProduct.tprod ℂ x) := fun x => by simp [U, PiTensorProduct.lift_symm]
  have hval' : ∀ x, U' x = T' (PiTensorProduct.tprod ℂ x) := fun x => by simp [U', PiTensorProduct.lift_symm]
  have hUv : U v₀ = U' v := by rw [hval, hval', he]
  have hne : ∀ τ, (v₀ τ : M.H τ) ≠ 0 := fun τ hz => by
    have h1τ := h1 τ
    rw [hz, norm_zero] at h1τ
    exact zero_ne_one h1τ
  have hU0 : U v₀ ≠ 0 := by
    intro hz
    apply hT0
    have h0 : U = 0 := GlobalTheory.TranslatedEvalInj.eq_zero_of_value hU v₀ hne hz
    have : T = PiTensorProduct.lift U := (PiTensorProduct.lift.apply_symm_apply T).symm
    rw [this, h0, map_zero]
  obtain ⟨c1, hc1⟩ := GlobalTheory.MultFinite.schurMult hP ν 𝓖 hθ hν h𝓖 U hUm U hUm
  obtain ⟨c2, hc2⟩ := GlobalTheory.MultFinite.schurMult hP ν 𝓖 hθ hν h𝓖 U' hUm' U hUm
  have hpos := GlobalTheory.SchurConst.re_pos_of_isMultIP M ν 𝓖 hν h𝓖 U hc1 v₀ (hU.aut v₀).cont (hU.aut v₀).left hU0
  have hc10 : c1 ≠ 0 := fun hz => by simp [hz] at hpos
  have key : ∀ x : M.Vec, ∏ τ, ⟪v₀ τ, x τ⟫_ℂ = (c2 / c1) * ∏ τ, ⟪v τ, x τ⟫_ℂ := by
    intro x
    have e1 := (hc1 v₀ x).2
    have e2 := (hc2 v x).2
    rw [hUv, e2] at e1
    have e3 : ∏ τ, ⟪v₀ τ, x τ⟫_ℂ = ∏ τ, ⟪(v₀ τ : M.H τ), (x τ : M.H τ)⟫_ℂ := rfl
    have e4 : ∏ τ, ⟪v τ, x τ⟫_ℂ = ∏ τ, ⟪(v τ : M.H τ), (x τ : M.H τ)⟫_ℂ := rfl
    rw [e3, e4, div_mul_eq_mul_div, eq_div_iff hc10, mul_comm, e1]
  have hl := tprod_eq_smul_of_prod_inner v₀ v _ key
  refine ⟨_, ?_, hl⟩
  intro hz
  rw [hz, zero_smul] at hl
  have hp := GlobalTheory.PiTensorInner.ipT_tprod v₀ v₀
  simp only [hl, map_zero] at hp
  have : ∏ τ, ⟪v₀ τ, v₀ τ⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    show ((‖(v₀ τ : M.H τ)‖ : ℂ)) ^ 2 = 1
    rw [h1]; simp
  rw [this] at hp
  exact zero_ne_one hp

end GlobalTheory.MiTop.LineV

namespace GlobalTheory.MiTop

end GlobalTheory.MiTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.RdVal
variable {D : D7}

theorem toEAf_sig (a : AE D) :
    toEAf D (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig a) =
      Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [toEAf, finPart, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR, sigD]
  | add a b ha hb =>
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, RingHom.map_add (f := _), RingHom.map_add (f := _)]

theorem toEAf_incl (e : D.host.E) :
    toEAf D (incA D e) = Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) e := by
  simp [toEAf, finPart, incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Formalism.UG.inclE]

theorem isUnit_det_mt (V : HSp D) (g : GA D V) : IsUnit (mt V g).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (matHom V g))

theorem mt_unitary (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (mt V g) * V.gram.map (incA D) * mt V g =
      V.gram.map (incA D) := by
  exact (show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig V.gram from g).2

theorem finM_mem (V : HSp D) {n : ℕ} (hn : V.rank = n) (J : Matrix (Fin n) (Fin n) D.host.E)
    (hJ : J = V.gram.reindex (finCongr hn) (finCongr hn)) (g : GA D V) :
    ∃ x : UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F), x.1.1 = finM V hn g := by
  have hdet : IsUnit (finM V hn g).det := by
    simp only [finM, Matrix.det_reindex_self]
    have hm := RingHom.map_det (toEAf D) (mt V g)
    rw [RingHom.mapMatrix_apply] at hm
    rw [← hm]
    exact (isUnit_det_mt V g).map _
  refine ⟨⟨((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit, ?_⟩, rfl⟩
  show Formalism.UG.cT _ (finM V hn g) * J.map _ * finM V hn g = J.map _
  have key : Formalism.UG.cT (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (finM V hn g) =
      ((Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (mt V g)).map (toEAf D)).reindex
        (finCongr hn) (finCongr hn) := by
    ext i j; simp [finM, Formalism.UG.cT, Matrix.reindex_apply, toEAf_sig]
  have hJ' : J.map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =
      ((V.gram.map (incA D)).map (toEAf D)).reindex (finCongr hn) (finCongr hn) := by
    subst hJ; ext i j; simp [Matrix.reindex_apply, toEAf_incl]
  rw [key, hJ', finM]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, ← Matrix.map_mul, mt_unitary]

theorem infM_unit (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (τ : D.what₂.Tau) :
    IsUnit (infM θ V hn g τ).det := by
  simp only [infM, Matrix.det_reindex_self]
  have hm := RingHom.map_det ((θ τ).comp (infPart D)) (mt V g)
  rw [RingHom.mapMatrix_apply] at hm
  have e : compAt θ τ (mt V g) = (mt V g).map ((θ τ).comp (infPart D)) := rfl
  rw [e, ← hm]
  exact (isUnit_det_mt V g).map _

theorem atInf_mul_inv {n : ℕ} (γ : GL (Fin n) D.host.E) (τ : D.what₂.Tau) :
    atInf (embT D) (γ : Matrix (Fin n) (Fin n) D.host.E) τ * atInf (embT D) ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ = 1 := by
  simp only [atInf, ← Matrix.map_mul, Units.mul_inv]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end GlobalTheory.AdForm.RdVal


open GlobalTheory.AdForm.RdVal in
theorem GlobalTheory.AdForm.rdS_val : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (hn : V.rank = n) (J : Matrix (Fin n) (Fin n) D.host.E), J = V.gram.reindex (finCongr hn) (finCongr hn) → ∀ (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (cl : Type) (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)) → ∀ Ψ ∈ AdFun S (embT D), ∀ (y : Frames (gramC J (embT D))) (g : GA D V), (∃ x : UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F), x.1.1 = finM V hn g) ∧ (∀ τ, IsUnit (infM θ V hn g τ).det) ∧ ∀ (x : UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (y' : Frames (gramC J (embT D))), x.1.1 = finM V hn g → IsTr (infM θ V hn g) y y' → rdS θ V hn S yc (fun c => Ψ (yc c)) y g = Ψ x y' := by
  intro D θ _ V n hn J hJ T f bad S cl yc hbij Ψ hΨ y g
  refine ⟨finM_mem V hn J hJ g, fun τ => infM_unit θ V hn g τ, ?_⟩
  intro x y' hx hy
  obtain ⟨c, hc⟩ := hbij.2 (Quotient.mk'' x : Cls S)
  have hex : ∃ p, IsDec S yc (finM V hn g) p := by
    obtain ⟨h, hh, k, hk, hxe⟩ := (@DoubleCoset.eq _ _ _ _ _ _).mp hc
    obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hh)
    refine ⟨(c, γ, ⟨k.1, Subgroup.mem_subgroupOf.mp hk⟩), hγ, ?_⟩
    dsimp only
    rw [hγe, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← hxe, hx]
  have hp := hex.choose_spec
  have hfr : ∀ τ, IsUnit (atInf (embT D) ((hex.choose.2.1)⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ * y.1 τ).det := by
    intro τ
    rw [Matrix.det_mul, Matrix.det_mul]
    exact ((Matrix.isUnit_det_of_left_inverse (atInf_mul_inv hex.choose.2.1 τ)).mul (infM_unit θ V hn g τ)).mul (y.2 τ)
  unfold rdS
  rw [dite_eq_left hex, atFr, dite_eq_left hfr]
  have law := hΨ hex.choose.2.1 hp.1 (yc hex.choose.1) x hex.choose.2.2 (Units.ext (hx.trans hp.2)) y' ⟨_, hfr⟩ (by
    intro τ
    show y'.1 τ = _
    rw [hy τ]
    simp only [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul])
  exact law.symm
end

