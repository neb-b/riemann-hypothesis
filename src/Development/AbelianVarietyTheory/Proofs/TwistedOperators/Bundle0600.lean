module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardArrowLeftInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.DownKer

theorem kerA_down_left_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : ℕ),
    i ≤ D.R.m → j < D.R.m → ∀ Ψ : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ,
    IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) Ψ → ∀ h : GA D (G.V (.grid i j)),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g, W.kerA (.down t i j) Ψ (γ * g) h = W.kerA (.down t i j) Ψ g h := by
  intro D T L sc G W t i j hi hj Ψ hΨ h γ hγ g
  have hR : (Pair.mu t i j : Pair T).InRange D.R.m := ⟨hi, hj⟩
  have hw := W.om_is (.mu t i j) hR
  show (W.om (.mu t i j)) (h, γ * g) Ψ 0 = (W.om (.mu t i j)) (h, g) Ψ 0
  have e : ((h, γ * g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (1, γ) * (h, g) := by
    simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hw.om_aut 1 (one_mem _) γ hγ _ (hw.om_pres _ _ hΨ)

end GlobalTheory.DownKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardTestGridEqSenderGrid
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipDown

theorem kernel_down : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
    {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (t : T) (i j : ℕ), i ≤ D.R.m → j < D.R.m →
    ∀ (eA : GA D (G.V i (j + 1)).V = GA D (G'.V (.grid i (j + 1)))) (eB : GA D (G.V i j).V = GA D (G'.V (.grid i j)))
    (Ψ : WO (G'.pS (.mu t i j)) (G'.pT (.mu t i j)) → ℂ), IsThetaFunO W.ψ (G'.pS (.mu t i j)) (G'.pT (.mu t i j)) Ψ →
    ∃ Φ : WO (G.V i j).V (G.V i (j + 1)).V → ℂ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ ∧
      ∀ h g, thetaKO (G.th t i j).ω h g Φ = W.kerA (.down t i j) Ψ (cast eA g) (cast eB h) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W hW G hG hM t i j hi hj eA eB Ψ hΨ
  obtain ⟨L1, a1, b1, e1⟩ := (hM.1.vert i j hi (by omega)).sp
  obtain ⟨L2, a2, b2, e2⟩ := (hM.1.vert i (j + 1) hi (by omega)).sp
  have hω := hM.2.omT t i j hi hj
  revert eA eB hω
  generalize (G.th t i j).ω = ω
  revert ω
  generalize (G.V i j).V = S at e1 ⊢
  generalize (G.V i (j + 1)).V = U at e2 ⊢
  subst e1 e2
  intro ω eA eB hω
  have hω' : ω = W.om (.mu t i j) := eq_of_heq hω
  subst hω'
  refine ⟨Ψ, ?_, fun h g => rfl⟩
  rw [← hW.ψ]
  exact ⟨hΨ.1, hΨ.2, hΨ.3, hΨ.4⟩

end GlobalTheory.FlipDown
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftVerticalCuspidalSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColFockRed

open GlobalTheory.Grid

theorem isContAut_cusp {D : D7} {θ : InfFam D} {N : Node D} (F : N.Cusp θ) (x : SmT N.M) :
    GlobalTheory.Unf.IsContAut N.V (F.1 x) := by
  have sm : ∀ {f : GA D N.V → ℂ}, GlobalTheory.Unf.IsContAut N.V f → ∀ c : ℂ, GlobalTheory.Unf.IsContAut N.V (c • f) := fun hf c =>
    ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩
  have ad : ∀ {f g : GA D N.V → ℂ}, GlobalTheory.Unf.IsContAut N.V f → GlobalTheory.Unf.IsContAut N.V g → GlobalTheory.Unf.IsContAut N.V (f + g) :=
    fun hf hg => ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩
  obtain ⟨G, hG⟩ := F
  show GlobalTheory.Unf.IsContAut N.V (G x)
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact sm ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact ad hx hy
  | zero => rw [map_zero, LinearMap.zero_apply]; exact ⟨fun _ _ _ => rfl, continuous_const⟩
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact ad (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact sm (h x) c

theorem xp_is {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GlobalTheory.Grid.GridPre R}
    (hG : G.Is) (k : ℕ) (hk : k ≤ D.R.m) : ∃ ν P, (G.Xp k).Is ν 0 P := by
  cases k with
  | zero =>
    have h := hG.spaces.P D.R.m le_rfl
    rw [show (D.R.m - D.R.m + 1) / 2 = 0 by omega] at h
    exact ⟨_, _, h⟩
  | succ k => exact ⟨_, _, hG.spaces.X k hk⟩

theorem measDat_haar_fd {D : D7} {N : Node D} {m : N.MeasDat} {df : Prop} {K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))}
    (h : m.Is df K) : m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
  by_cases hd : df
  · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
  · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩

theorem measX_haar_fd {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {G : GridPre R}
    (hG : G.Is) (j : ℕ) (hj : j ≤ D.R.m) :
    (G.measX j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.Xp j).V) (G.measX j).fd (G.measX j).ν := by
  cases j with
  | zero => exact measDat_haar_fd (hG.meas.P D.R.m le_rfl)
  | succ j => exact measDat_haar_fd (hG.meas.X j hj)

end GlobalTheory.ColFockRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalAtRealPlaceCommuteInfTrivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FibreAtTau

theorem comm_and_inf_trivial : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau), (∀ p ∈ GlobalTheory.FibreAtTau.atP θ V C τ, ∀ q ∈ GlobalTheory.FibreAtTau.offP θ V C τ, p * q = q * p) ∧ ∀ h, h ∈ GlobalTheory.FibreAtTau.atP θ V C τ → h ∈ GlobalTheory.FibreAtTau.offP θ V C τ → h = 1 := by
  intro D θ hθ V r C τ
  have hc : ∀ (ρ : D.what₂.Tau) (x : GA D V), cmp θ ρ x = GlobalTheory.RowReal.infMatHom V (θ ρ) x := fun _ _ => rfl
  have one_spec : GlobalTheory.RowReal.IsRealAll θ V 1 (1 : GA D V) :=
    ⟨one_mem _, fun _ => GlobalTheory.PointAtPlaceHom.infMat_one V _⟩
  refine ⟨fun p hp q hq => ?_, fun h hp hq => ?_⟩
  · rw [mem_atP] at hp
    rw [mem_offP] at hq
    obtain ⟨hpf, hpc⟩ := hp
    have hpf' : finHom V (p : GA D V) = 1 := hpf
    set c : GA D V := (p : GA D V) * q * (p : GA D V)⁻¹ * (q : GA D V)⁻¹ with hcdef
    have hcR : GlobalTheory.RowReal.IsRealAll θ V 1 c := by
      refine ⟨?_, fun ρ => ?_⟩
      · show finHom V c = 1
        simp only [hcdef, map_mul, map_inv, hpf', one_mul, inv_one, mul_one, mul_inv_cancel]
      · show GlobalTheory.RowReal.infMatHom V (θ ρ) c = 1
        by_cases hρ : ρ = τ
        · have hinv : ∀ x : GA D V, GlobalTheory.RowReal.infMatHom V (θ ρ) x * GlobalTheory.RowReal.infMatHom V (θ ρ) x⁻¹ = 1 :=
            fun x => by rw [← map_mul, mul_inv_cancel, map_one]
          have hinv1 : ∀ x : GA D V, GlobalTheory.RowReal.infMatHom V (θ ρ) x = 1 → GlobalTheory.RowReal.infMatHom V (θ ρ) x⁻¹ = 1 :=
            fun x hx => by have := hinv x; rwa [hx, Matrix.one_mul] at this
          subst hρ
          have hq' : GlobalTheory.RowReal.infMatHom V (θ ρ) (q : GA D V) = 1 := by rw [← hc]; exact hq
          rw [hcdef, map_mul, map_mul, map_mul, hq', hinv1 _ hq', Matrix.mul_one, Matrix.mul_one, hinv]
        · have hinv : ∀ x : GA D V, GlobalTheory.RowReal.infMatHom V (θ ρ) x * GlobalTheory.RowReal.infMatHom V (θ ρ) x⁻¹ = 1 :=
            fun x => by rw [← map_mul, mul_inv_cancel, map_one]
          have hinv1 : ∀ x : GA D V, GlobalTheory.RowReal.infMatHom V (θ ρ) x = 1 → GlobalTheory.RowReal.infMatHom V (θ ρ) x⁻¹ = 1 :=
            fun x hx => by have := hinv x; rwa [hx, Matrix.one_mul] at this
          have hp' : GlobalTheory.RowReal.infMatHom V (θ ρ) (p : GA D V) = 1 := by rw [← hc]; exact hpc ρ hρ
          rw [hcdef, map_mul, map_mul, map_mul, hp', hinv1 _ hp', Matrix.one_mul, Matrix.mul_one, hinv]
    have e : c = 1 := hcR.unique hθ one_spec
    apply Subtype.ext
    have e2 : (p : GA D V) * q * (p : GA D V)⁻¹ * (q : GA D V)⁻¹ = 1 := e
    have e3 : (p : GA D V) * q = (q : GA D V) * p := by
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at e2
      exact e2
    simpa using e3
  · rw [mem_atP] at hp
    rw [mem_offP] at hq
    apply Subtype.ext
    have hR : GlobalTheory.RowReal.IsRealAll θ V 1 (h : GA D V) := by
      refine ⟨hp.1, fun ρ => ?_⟩
      by_cases hρ : ρ = τ
      · subst hρ; exact hq
      · exact hp.2 ρ hρ
    exact hR.unique hθ one_spec

end GlobalTheory.FibreAtTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalEqAtRealPlaceMulTrivialAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FibreAtTau

variable {D : D7}

def atPHom {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) : GA D V →* GA D V where
  toFun x := atTau θ V τ (cmp θ τ x)
  map_one' := by
    show atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) 1) = 1
    rw [GlobalTheory.PointAtPlaceHom.infMat_one]
    exact GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ
  map_mul' x y := by
    show atTau θ V τ (infMat D.sp.cm.sig V.gram (θ τ) (x * y)) = _
    rw [GlobalTheory.PointAtPlaceHom.infMat_mul]
    exact GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ)
      (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V y τ)

theorem atPHom_spec {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) (x : GA D V) :
    IsAtTau θ V τ (cmp θ τ x) (atPHom hθ V τ x) :=
  GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ)


open Classical in
theorem matHom_atPHom {θ : InfFam D} (hθ : IsInfFam θ) {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (hσ : GlobalTheory.FockCompare.Chart θ σ) (V : HSp D) (τ : D.what₂.Tau) (x : GA D V) (i j : Fin V.rank) :
    ((matHom V (atPHom hθ V τ x)).1 - 1) i j = σ (Pi.single τ 1) * ((matHom V x).1 - 1) i j := by
  have hs := atPHom_spec hθ V τ x
  have inf1 : ∀ (y : GA D V) (ρ : D.what₂.Tau),
      θ ρ (infPart D (((matHom V y).1 - 1) i j)) = infMat D.sp.cm.sig V.gram (θ ρ) y i j - (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j := by
    intro y ρ
    have e1 : θ ρ (infPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j := congrFun (congrFun (GlobalTheory.PointAtPlaceHom.infMat_one V (θ ρ)) i) j
    rw [Matrix.sub_apply, RingHom.map_sub, RingHom.map_sub, e1]
    rfl
  rw [← sub_eq_zero]
  refine hσ.ext _ ?_ fun ρ => ?_
  · have a2 : (finHom V (atPHom hθ V τ x)).1 = (finHom V 1).1 := by rw [map_one]; exact congrArg Units.val hs.1
    have e : finPart D ((matHom V (atPHom hθ V τ x)).1 i j) = finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) :=
      congrFun (congrFun a2 i) j
    rw [Matrix.sub_apply, RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, e, hσ.fin, zero_mul, sub_self, sub_zero]
  · let π : AE D →+* ℂ := (θ ρ).comp (infPart D)
    have hπ : ∀ z, θ ρ (infPart D z) = π z := fun _ => rfl
    have hc : π (σ (Pi.single τ 1)) = (Pi.single τ 1 : D.what₂.Tau → ℂ) ρ := hσ.comp (Pi.single τ 1) ρ
    have i1 : ∀ y : GA D V, π (((matHom V y).1 - 1) i j) =
        infMat D.sp.cm.sig V.gram (θ ρ) y i j - (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j := fun y => inf1 y ρ
    rw [hπ, RingHom.map_sub π, RingHom.map_mul π, i1, i1, hc]
    by_cases c : ρ = τ
    · subst c
      rw [hs.2.1, Pi.single_eq_same, one_mul, sub_self]
    · rw [hs.2.2 ρ c, Pi.single_eq_of_ne c, zero_mul, sub_self, sub_zero]

theorem mul_eq_zero_of_entry {n k : ℕ} {A : Type} [CommRing A] {m m' : Matrix (Fin n) (Fin n) A} {e : A}
    (he : ∀ i j, m' i j = e * m i j) {N : Matrix (Fin n) (Fin k) A} (h : m * N = 0) : m' * N = 0 := by
  ext i l
  have := congrFun (congrFun h i) l
  simp only [Matrix.mul_apply, Matrix.zero_apply] at this ⊢
  simp only [he, mul_assoc, ← Finset.mul_sum, this, mul_zero]

theorem entry_mul_eq_zero {n k : ℕ} {A : Type} [CommRing A] {m m' : Matrix (Fin n) (Fin n) A} {e : A}
    (he : ∀ i j, m' i j = e * m i j) {N : Matrix (Fin k) (Fin n) A} (h : N * m = 0) : N * m' = 0 := by
  ext i l
  have := congrFun (congrFun h i) l
  simp only [Matrix.mul_apply, Matrix.zero_apply] at this ⊢
  simp only [he, mul_left_comm _ e, ← Finset.mul_sum, this, mul_zero]

theorem mulVec_of_entry {n k : ℕ} {A : Type} [CommRing A] {m m' : Matrix (Fin n) (Fin n) A} {e : A}
    (he : ∀ i j, m' i j = e * m i j) {N : Matrix (Fin n) (Fin k) A} {y : Fin n → A} {a : Fin k → A}
    (h : m *ᵥ y = N *ᵥ a) : m' *ᵥ y = N *ᵥ fun l => e * a l := by
  funext i
  have := congrFun h i
  simp only [Matrix.mulVec, dotProduct] at this ⊢
  simp only [he, mul_assoc, mul_left_comm _ e, ← Finset.mul_sum, this]

theorem atPHom_mem_NI {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (τ : D.what₂.Tau) {h : GA D V} (hh : h ∈ NI V C) : atPHom hθ V τ h ∈ NI V C := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have key : NI V C ≤ (NI V C).comap (atPHom hθ V τ) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    obtain ⟨h1, h2, h3⟩ := hx
    have hm := matHom_atPHom hθ hσ V τ x
    refine Subgroup.subset_closure ⟨mul_eq_zero_of_entry hm h1, entry_mul_eq_zero hm h2, fun y hy => ?_⟩
    obtain ⟨a, ha⟩ := h3 y hy
    exact ⟨_, mulVec_of_entry hm ha⟩
  exact key hh

theorem decomp : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∀ (τ : D.what₂.Tau) (h : NI V C), ∃ p ∈ GlobalTheory.FibreAtTau.atP θ V C τ, ∃ q ∈ GlobalTheory.FibreAtTau.offP θ V C τ, h = p * q := by
  intro D θ hθ V r C _ τ h
  have hs := atPHom_spec hθ V τ (h : GA D V)
  let p : NI V C := ⟨atPHom hθ V τ h, atPHom_mem_NI hθ V C τ h.2⟩
  refine ⟨p, mem_atP.2 ⟨hs.1, hs.2.2⟩, p⁻¹ * h, mem_offP.2 ?_, (mul_inv_cancel_left p h).symm⟩
  show infMat D.sp.cm.sig V.gram (θ τ) ((atPHom hθ V τ h)⁻¹ * h) = 1
  have e : infMat D.sp.cm.sig V.gram (θ τ) (atPHom hθ V τ h) = infMat D.sp.cm.sig V.gram (θ τ) h := hs.2.1
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, ← e, ← GlobalTheory.PointAtPlaceHom.infMat_mul, inv_mul_cancel,
    GlobalTheory.PointAtPlaceHom.infMat_one]

end GlobalTheory.FibreAtTau

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryInBasisIntegralAtConjugatePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjPlaceUnitary

open GlobalTheory.AdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents (cjA inc)

variable {D : D7}

theorem entries_of_mem_GLint {L : Type} [Field L] {n : ℕ} (O : Subring L) {g : GL (Fin n) L}
    (hg : g ∈ Formalism.UG.GLint (Fin n) O) (i j : Fin n) : g.1 i j ∈ O ∧ (g⁻¹).1 i j ∈ O := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨(h.1 i j).2, by rw [← map_inv]; exact ((h⁻¹).1 i j).2⟩

theorem frame_change {n : ℕ} {β β' : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : IsFrame β Λ) (h' : IsFrame β' Λ) (i j : Fin n) : (β⁻¹ * β').1 i j ∈ OA D := by
  have h1 : β'.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := (h' _).2 fun k => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have h2 := (h _).1 h1 i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h2
  exact h2

theorem dual_frame {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsFrame β Λ) (hd : Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ) :
    ∃ β' : GL (Fin V.rank) (Lev.EAf D), Formalism.UG.cT (cjA D) β.val * V.gram.map (inc D) * β'.val = 1 ∧
      (∀ i j, (β⁻¹ * β').1 i j ∈ OA D) ∧ (∀ i j, (β'⁻¹ * β).1 i j ∈ OA D) := by
  have hL := GlobalTheory.DiagLiftFix.isLattice_of_isFrame hβ
  have hsd : IsSelfDualC V Λ := ⟨hL, fun y => by
    have key := GlobalTheory.SDFrameLattice.mem_dualL_iff V Λ y
    rw [hd] at key
    exact key⟩
  obtain ⟨β', h1, -⟩ := exists_dual_frame V β
  have h' : IsFrame β' Λ := by
    intro y
    rw [← hd, ← mem_hat, mem_hat_dualL_iff (selfDual_isFullLattice hsd)]
    rw [← dual_frame_gen (OA D) (cjA D) (fun _ => cjA_mem) h1]
    refine forall_congr' fun x => ?_
    rw [mem_hat, hβ, ← cjA_mem_iff, cjA_hA, hA_eq]
  exact ⟨β', h1, frame_change hβ h', frame_change h' hβ⟩

end GlobalTheory.ConjPlaceUnitary

namespace GlobalTheory.ConjPlaceUnitary

open GlobalTheory.AdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents (cjA inc)

theorem conj_formula_gen {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ}
    (J B Bi B' B'i Z Zi : Matrix (Fin n) (Fin n) A) (hB : B * Bi = 1) (hB' : B' * B'i = 1) (hZ : Z * Zi = 1)
    (h1 : Formalism.UG.cT σ B * J * B' = 1) (hz : Formalism.UG.cT σ Z * J * Z = J) :
    Bi * Z * B = Bi * B' * Formalism.UG.cT σ (Bi * Zi * B) * (B'i * B) := by
  have hcBi : Formalism.UG.cT σ Bi * Formalism.UG.cT σ B = 1 := by
    rw [← GlobalTheory.StdFrames.cT_mul', hB, GlobalTheory.StdFrames.cT_one']
  have hzi : Formalism.UG.cT σ Zi * Formalism.UG.cT σ Z = 1 := by
    rw [← GlobalTheory.StdFrames.cT_mul', hZ, GlobalTheory.StdFrames.cT_one']
  have hM : Formalism.UG.cT σ B * J = B'i := by
    calc Formalism.UG.cT σ B * J = Formalism.UG.cT σ B * J * (B' * B'i) := by rw [hB', Matrix.mul_one]
      _ = B'i := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h1' : B' * (Formalism.UG.cT σ B * J) = 1 := by rw [hM, hB']
  have hz' : Formalism.UG.cT σ Zi * (Formalism.UG.cT σ Z * J * Z) = J * Z := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hzi, Matrix.one_mul]
  rw [GlobalTheory.StdFrames.cT_mul', GlobalTheory.StdFrames.cT_mul', ← hM]
  calc Bi * Z * B = Bi * (B' * (Formalism.UG.cT σ B * J)) * Z * B := by rw [h1', Matrix.mul_one]
    _ = Bi * B' * Formalism.UG.cT σ B * (Formalism.UG.cT σ Zi * (Formalism.UG.cT σ Z * J * Z)) * B := by
        rw [hz']
        simp only [Matrix.mul_assoc]
    _ = Bi * B' * Formalism.UG.cT σ B * (Formalism.UG.cT σ Zi * (Formalism.UG.cT σ Bi * Formalism.UG.cT σ B) * J) * B := by
        rw [hz, hcBi, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

variable {D : D7}

theorem conj_formula {n : ℕ} (J : Matrix (Fin n) (Fin n) (Lev.EAf D)) (β β' z : GL (Fin n) (Lev.EAf D))
    (h1 : Formalism.UG.cT (cjA D) β.val * J * β'.val = 1) (hz : Formalism.UG.cT (cjA D) z.val * J * z.val = J) :
    (β⁻¹ * z * β).val = (β⁻¹ * β').val * Formalism.UG.cT (cjA D) (β⁻¹ * z⁻¹ * β).val * (β'⁻¹ * β).val := by
  simp only [Units.val_mul]
  exact conj_formula_gen (cjA D) J β.val (β⁻¹).val β'.val (β'⁻¹).val z.val (z⁻¹).val
    (Units.mul_inv β) (Units.mul_inv β') (Units.mul_inv z) h1 hz

end GlobalTheory.ConjPlaceUnitary

namespace GlobalTheory.ConjPlaceUnitary

open GlobalTheory.AdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents (cjA inc)

variable {D : D7}

theorem cpt_conj_mem {n : ℕ} (w : Pl D.host.E) (P C M : Matrix (Fin n) (Fin n) (Lev.EAf D))
    (hP : ∀ i j, P i j ∈ OA D) (hM : ∀ i j, M i j ∈ OA D)
    (hC : ∀ i j, cpt w (C i j) ∈ w.adicCompletionIntegers D.host.E) (i j : Fin n) :
    cpt (Formalism.DivisionValues.conjPl w) ((P * Formalism.UG.cT (cjA D) C * M) i j) ∈
      (Formalism.DivisionValues.conjPl w).adicCompletionIntegers D.host.E := by
  rw [GlobalTheory.FunObj.conjPl_eq_cP]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul]
  refine sum_mem fun l _ => mul_mem (sum_mem fun k _ => mul_mem ?_ ?_) ?_
  · exact (mem_OA_iff _).1 (hP i k) _
  · exact ConjugatePlaceIntegrality.GlobalTheory.CompanionTheory.ConjPlaceInt.cpt_sg_mem_integers w (C l k) (hC l k)
  · exact (mem_OA_iff _).1 (hM l j) _

end GlobalTheory.ConjPlaceUnitary

namespace GlobalTheory.ConjPlaceUnitary

open GlobalTheory.AdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents (cjA inc)

theorem inBasis_conjPl_mem_KO : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsFrame β Λ → Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ → ∀ x ∈ UA D.sp.cm V.gram, ∀ w : Pl D.host.E, inBasis rfl β w x ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin V.rank) → inBasis rfl β (Formalism.DivisionValues.conjPl w) x ∈ GlobalTheory.SplitWeil.KO (Kw (Formalism.DivisionValues.conjPl w)) (Fin V.rank) := by
  intro D V β Λ hβ hd x hx w hw
  obtain ⟨β', h1, hP, hM⟩ := dual_frame hβ hd
  have hu : ∀ z ∈ UA D.sp.cm V.gram, Formalism.UG.cT (cjA D) z.val * V.gram.map (inc D) * z.val = V.gram.map (inc D) :=
    fun z hz => hz
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion] at hw ⊢
  have hC : ∀ a b, cpt w ((β⁻¹ * x * β).val a b) ∈ w.adicCompletionIntegers D.host.E := fun a b =>
    (entries_of_mem_GLint _ hw a b).1
  have hC' : ∀ a b, cpt w ((β⁻¹ * x⁻¹ * β).val a b) ∈ w.adicCompletionIntegers D.host.E := fun a b => by
    have := (entries_of_mem_GLint _ hw a b).2
    rw [← map_inv] at this
    exact this
  refine GlobalTheory.FunObj.mem_GLint_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [GlobalTheory.FunObj.inBasis_apply, conj_formula _ β β' x h1 (hu x hx)]
    exact cpt_conj_mem w _ _ _ hP hM hC' _ _
  · rw [← map_inv, GlobalTheory.FunObj.inBasis_apply]
    have e := conj_formula _ β β' x⁻¹ h1 (hu _ (inv_mem hx))
    rw [inv_inv] at e
    rw [e]
    exact cpt_conj_mem w _ _ _ hP hM hC _ _

end GlobalTheory.ConjPlaceUnitary
end
end

