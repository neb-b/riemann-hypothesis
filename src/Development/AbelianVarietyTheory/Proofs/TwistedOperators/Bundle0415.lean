module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReadOffFormsAutomorphicInverseMultiplier
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupCongruentOfTwoLatticeMoves
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405
public import Formalism.LocalToGlobal.Divisibility.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0216

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearMapChainCompositeUpdateSmul
section
open GlobalTheory.FunObj

namespace GlobalTheory.ChainSmul

theorem chainTo_update_of_le {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (B : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    ∀ n, n ≤ j₀ → chainTo (Function.update k j₀ B) n = chainTo k n
  | 0, _ => rfl
  | n + 1, h => by
    have hne : n ≠ j₀ := by omega
    show Function.update k j₀ B n ∘ₗ chainTo (Function.update k j₀ B) n = k n ∘ₗ chainTo k n
    rw [Function.update_of_ne hne, chainTo_update_of_le k j₀ B n (by omega)]

theorem chainTo_update_smul {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    (k : ∀ j, V j →ₗ[ℂ] V (j + 1)) (j₀ : ℕ) (c : ℂ) (A : V j₀ →ₗ[ℂ] V (j₀ + 1)) :
    ∀ n, j₀ < n → chainTo (Function.update k j₀ (c • A)) n = c • chainTo (Function.update k j₀ A) n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    show Function.update k j₀ (c • A) n ∘ₗ chainTo (Function.update k j₀ (c • A)) n =
      c • (Function.update k j₀ A n ∘ₗ chainTo (Function.update k j₀ A) n)
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · have hne : n ≠ j₀ := by omega
      rw [Function.update_of_ne hne, Function.update_of_ne hne, chainTo_update_smul k j₀ c A n h',
        LinearMap.comp_smul]
    · rw [Function.update_self, Function.update_self, chainTo_update_of_le k j₀ _ j₀ le_rfl,
        chainTo_update_of_le k j₀ _ j₀ le_rfl, LinearMap.smul_comp]

end GlobalTheory.ChainSmul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSpanAddSmulLatticeOfFrameCoeffsZmod
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

namespace GlobalTheory

open Formalism.L2.SG.Pf.BunEx.Unip Formalism.L2.SG.Pf.unitaryCongruence in
theorem mo_of_coef_mod : ∀ (I : AutInst) (g : ℕ) {r k : ℕ} (e0 f0 : Fin r → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (ew : I.E ⊗[I.F] Af I.F), Formalism.L2.SG.Pf.BunEx.Unip.FH I g e0 f0 z0 bw bwd ew → ∀ v ∈ I.Lf, ∀ (Se : Set (Fin r)) (Sb : Set (Fin k)), (∀ a, a ∉ Se → ZMod' I g (hA I (f0 a) v)) → (∀ a, ZMod' I g (hA I (e0 a) v)) → ZMod' I g (hA I z0 v) → (∀ i, i ∉ Sb → ZMod' I g (hA I (bwd i) v)) → (∀ i, ZMod' I g (hA I (bw i) v)) → v ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo I g (e0 '' Se ∪ bw '' Sb) := by
  intro I g r k e0 f0 z0 bw bwd ew h v hv Se Sb hf he hz hbd hb
  have hm := h.mem
  refine mem_Mo_of (exp h v hv) ?_
  classical
  unfold Rc
  refine add_mem (add_mem (sub_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · refine Submodule.sum_mem _ fun a _ => ?_
    by_cases ha : a ∈ Se
    · exact span_Mo (smul_span I (Formalism.L2.SG.Pf.unitaryCongruence.hA_int I (hm.1 a).2 hv) (Or.inl ⟨a, ha, rfl⟩))
    · exact mL_Mo I (Zv I g (hf a ha) (hm.1 a).1)
  · exact mL_Mo I (sumZ I g _ _ _ (fun a _ => he a) (fun a _ => (hm.1 a).2))
  · exact mL_Mo I (Zv I g hz hm.2.1)
  · refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ Sb
    · exact span_Mo (smul_span I (Formalism.L2.SG.Pf.unitaryCongruence.hA_int I (hm.2.2 i).2 hv) (Or.inr ⟨i, hi, rfl⟩))
    · exact mL_Mo I (Zv I g (hbd i hi) (hm.2.2 i).1)
  · exact mL_Mo I (sumZ I g _ _ _ (fun i _ => hb i) (fun i _ => (hm.2.2 i).2))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSpanThetaSeriesOfBoundedHolomorphic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → 4 * (Module.finrank ℚ D.host.E * T.rank) + 4 ≤ S.rank → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → HolUpTo C B (ThFr.wtOf C.X C.hr c c' S.rank) z φ → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → φ ∈ Submodule.span ℂ (thetaSet C om B (C.uVec Lv hn f') c c') := by
  intro D S T C om hW hsz Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hhol hγ hk hbdd
  obtain ⟨v₀, μ, hv, hμ⟩ := GlobalTheory.SW.exists_vacua_and_multipliers D.host.E T.rank C.X C.g C.bas C.idx S.rank
    C.sympl C.even Lv
  obtain ⟨ep, cf, hep⟩ := _root_.GlobalTheory.Ker.LevelMove.om_Th_phi D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB
  have hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ := by rw [GlobalTheory.Ker.Red.fmt_one]; exact GlobalTheory.Ker.Red.isMov_one _
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [GlobalTheory.Ker.Red.fmtC_one]; exact GlobalTheory.Ker.Red.isMov_one _
  obtain ⟨hV, hL⟩ := _root_.GlobalTheory.Ker.MovLev.mov_mem_lattices D S T C
  have hΛl : C.X.Λ ∈ Lv.lats := (hL Lv 1 _ C.X.Λ_fg hm1).2.1 (GlobalTheory.Ker.Red.trivAt_one _ _)
  obtain ⟨t, ht0, hft⟩ := (_root_.GlobalTheory.Ker.LevVec.uVec_eq D S T C Lv hn M hw hM hM𝔪 B hB).1 f' hbase (v₀ C.X.Λ) (hv _ hΛl)
  have hu : C.uVec Lv hn f' = t • C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank)) := by
    rw [hft]; exact ((_root_.GlobalTheory.Ker.LevVec.uVec_eq D S T C Lv hn M hw hM hM𝔪 B hB).2 v₀ hv).2 t
  have hex : ∀ L : Lt D.host.E T.rank, ∃ g : GA D T, L ∈ Lv.lats →
      g ∈ GfC T ∧ TrivAt T (C.under Lv) g ∧ IsMov (fmt T g) C.X.Λ L := by
    intro L
    by_cases hL' : L ∈ Lv.lats
    · obtain ⟨g, hg, h1, h2⟩ := GlobalTheory.Ker.OntoLat.exists_trivAt_mov D S T C Lv L hL'
      exact ⟨g, fun _ => ⟨hg, h1, h2⟩⟩
    · exact ⟨1, fun h => absurd h hL'⟩
  choose gL hgL using hex
  choose Qf hQd hQb hQv using fun L => hhol (gL L)
  have hne : ∀ L ∈ Lv.lats, ep 1 * cf (gL L) ≠ 0 := by
    intro L hL'
    obtain ⟨g1, g2, -⟩ := hep 1 _ (gL L) L (one_mem _) (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1
      (hgL L hL').1 (hgL L hL').2.1 hL'.1.1 (hgL L hL').2.2
    refine mul_ne_zero ?_ ?_ <;> intro h0
    · rw [h0, norm_zero] at g1; exact zero_ne_one g1
    · rw [h0, norm_zero] at g2; exact zero_ne_one g2
  let F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ := fun L x => Qf L x / (ep 1 * cf (gL L))
  have hFhol : ∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom := fun L _ => by
    show DifferentiableOn ℂ (fun x => Qf L x / (ep 1 * cf (gL L))) C.X.dom
    simpa only [div_eq_mul_inv] using (hQd L).mul_const (ep 1 * cf (gL L))⁻¹
  have hFbor : ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank,
      F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x := by
    intro L _ x hx b hb
    show Qf L (rmul x b) / _ = _ * (Qf L x / _)
    rw [hQb L x hx b hb, mul_div_assoc]
  have hFv : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T,
      φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B)) := by
    intro L hL' a ha
    show _ = _ * (Qf L _ / _)
    rw [hQv L a ha, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (hne L hL')]
  have hForm : IsForm C.X Lv.grp Lv.lats μ (wtOf C.X C.hr c c' S.rank) F :=
    ⟨hFhol, hFbor, _root_.GlobalTheory.Ker.AutRead.read_off_automorphic D S T C om hW Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hγ hk v₀ μ hv hμ ep cf hep
      gL hgL F hFhol hFbor hFv,
     _root_.GlobalTheory.AdSpan.BddForms.pnorm_le_of_bdd D S T C om hW Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hγ hk v₀ μ hv hμ ep cf hep
      gL hgL F hFhol hFbor hFv hbdd⟩
  obtain ⟨m, Λs, P, a, hΛP, hsp⟩ := GlobalTheory.SW.level_theta_span D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx
    S.rank C.sympl C.even hsz Lv hn M hM hM𝔪 v₀ hv μ hμ c c' F hForm
  choose hs hsf hst hsm using fun i => _root_.GlobalTheory.KerOntoStd.exists_trivAt_isMov D S T C M hM (Λs i) (hΛP i).1
  have hbij := (_root_.GlobalTheory.Ker.fvec_Th_zero D S T C).1
  let Qs : Fin m → MvPolynomial (FVar D T.rank S.rank) ℂ := fun i => Function.surjInv hbij.2 (P i)
  have hQs : ∀ i, C.toH (Qs i) = P i := fun i => Function.surjInv_eq hbij.2 (P i)
  have hepn : ∀ i, ep (hs i) ≠ 0 := by
    intro i h0
    obtain ⟨g1, -⟩ := hep (hs i) (Λs i) 1 C.X.Λ (hsf i) (hst i) (hΛP i).1.1 (hsm i) (one_mem _)
      (GlobalTheory.Ker.Red.trivAt_one _ _) C.X.Λ_fg hm1
    rw [h0, norm_zero] at g1; exact zero_ne_one g1
  let Θ : Fin m → GA D T → ℂ := fun i g => om (hs i, g) (C.fvec B (C.uVec Lv hn f') (Qs i)) 0
  let ψ : GA D T → ℂ := ∑ i, (a i * ep 1 / (t * ep (hs i))) • Θ i
  have hψ : ∀ g, ψ g = ∑ i, (a i * ep 1 / (t * ep (hs i))) * Θ i g := by
    intro g; simp only [ψ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hψmem : ψ ∈ Submodule.span ℂ (thetaSet C om B (C.uVec Lv hn f') c c') :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨hs i, Qs i, by rw [hQs i]; exact (hΛP i).2, rfl⟩)
  suffices hφψ : φ = ψ by rw [hφψ]; exact hψmem
  set u0 := C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank)) with hu0
  have hJ := (_root_.GlobalTheory.Ker.onBasis_frame_period D S T C).2
  have hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M :=
    hV M 1 _ hM (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1
  have hth0 : C.IsTh u0 := (_root_.GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ (hJ B hB).2.1 _
    (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv
      C.X.Λ hΛl _ hstd).1).1.1
  have hΘ : ∀ i g, Θ i g = t * om (hs i, g) (C.fvec B u0 (Qs i)) 0 := by
    intro i g
    show om (hs i, g) (C.fvec B (C.uVec Lv hn f') (Qs i)) 0 = _
    rw [hu, (_root_.GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C B hB (fun _ => 1) u0 hth0 (Qs i)).2.2.2.2.1 t, map_smul, Pi.smul_apply,
      smul_eq_mul]
  have hk0 : ∀ k, C.LevK Lv k 1 → om (1, k) u0 = u0 := by
    intro k hk'
    have e := (hk k 1 hk').1
    rw [hu, map_smul] at e
    exact smul_right_injective _ ht0 e
  have hinv := fun i => _root_.GlobalTheory.Ker.ThInv.fvec_val_inv D S T C om hW Lv (hs i) B hB u0 hth0 (Qs i)
  have hψγ : ∀ γ ∈ GQ T, ∀ g, ψ (γ * g) = ψ g := by
    intro γ hγ' g
    rw [hψ, hψ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΘ, hΘ, (hinv i).1 γ hγ' g]
  have hψk : ∀ k, C.LevK Lv k 1 → ∀ g, ψ (g * k) = ψ g := by
    intro k hk' g
    rw [hψ, hψ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΘ, hΘ, (hinv i).2 hk0 k hk' g]
  have hag : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = ψ (gL L * a) := by
    intro L hL' a ha
    have hx : C.xB (C.mvB a B) ∈ C.X.dom := (hJ _ ((hJ B hB).2.2.2.2.2 a).1).2.1
    have hev : ∀ i, Θ i (gL L * a) = t * ep (hs i) * cf (gL L) * z a *
        thP C.X C.hr C.bas C.idx (Lv.phi C.bas hn v₀ L (Λs i)) (P i) (C.xB (C.mvB a B)) := by
      intro i
      show om _ (C.fvec B (C.uVec Lv hn f') _) 0 = _
      rw [hu, _root_.GlobalTheory.AdSpan.EvalAt.theta_eval D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB ep cf hep z hz t (hs i) (Λs i) (hsf i) (hst i)
        (hΛP i).1.1 (hsm i) (gL L) L (hgL L hL').1 (hgL L hL').2.1 hL'.1.1 (hgL L hL').2.2 a ha (Qs i), hQs i]
    rw [hFv L hL' a ha, hψ, hsp L hL' _ hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hev i]
    have h1 := hepn i
    field_simp
  exact _root_.GlobalTheory.Ker.ExtInv.eq_of_invariant D S T C Lv M hM hM𝔪 gL hgL φ ψ hγ hψγ (fun k hk' => (hk k 1 hk').2) hψk hag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveLatticeGluedFromIntersectionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_lattice_glued_from_intersection : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ L, IsSDIn Y (flatSp Y X ι z) L → IsPrim Y z L → Submodule.IsFullLattice D.host.E (capX Y X ι L) ∧ ∃ x₀ : X.V, L = glueLat Y X ι z u (capX Y X ι L) x₀ := by
  intro D u Y X ι z hl L hL hp
  obtain ⟨hlat, hglue⟩ := GlobalTheory.AdIsom.Unglue.isLattice_capX_and_exists_glue D u Y X ι z hl L hL hp
  refine ⟨{ toIsLattice := by first | exact hlat | exact hlat.toIsLattice, span_eq_top := ?_ }, hglue⟩
  apply Submodule.eq_top_iff'.2
  intro y
  let x := (Formalism.L2.Herm.crd X).symm y
  have hx : ι x ∈ Submodule.span D.host.E (L : Set Y.V) := by
    rw [hL.2.1]
    exact Submodule.mem_sup_left (LinearMap.mem_range_self ι x)
  obtain ⟨c, hc, hcx⟩ := GlobalTheory.AdIsom.Unglue.exists_smul_mem L hx
  have hcy : c • y ∈ capX Y X ι L := by
    change c • y ∈ Formalism.L2.Herm.crdLat X (L.comap (ι.restrictScalars (𝓞 D.host.E)))
    refine ⟨c • x, ?_, ?_⟩
    · change ι (c • x) ∈ L
      simpa using hcx
    · simp [x]
  have hcy' : c • y ∈ Submodule.span D.host.E (capX Y X ι L : Set (Fin X.rank → D.host.E)) :=
    Submodule.subset_span hcy
  rw [← algebraMap_smul D.host.E c] at hcy'
  have h := (Submodule.span D.host.E (capX Y X ι L : Set (Fin X.rank → D.host.E))).smul_mem
    (c : D.host.E)⁻¹ hcy'
  simpa only [smul_smul, inv_mul_cancel₀ (RingOfIntegers.coe_ne_zero_iff.2 hc), one_smul] using h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceHermitianDualBasisStabilise
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjChar

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf

theorem cpt_cP_eq_zero_of_orth {D : D7} {PP : Pl D.host.E} {e : EAf D} (ho : e * GlobalTheory.StdFrames.sg D e = 0)
    (h1 : GlobalTheory.StdFrames.cpt PP e = 1) : GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP PP) e = 0 := by
  have h2 := GlobalTheory.StdFrames.cpt_sg_eq_zero (Q := GlobalTheory.IdemSupport.cP PP) (z := 1 - e)
    (by rw [GlobalTheory.StdFrames.cP_cP, RingHom.map_sub, h1, RingHom.map_one, sub_self])
  rw [RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one, sub_eq_zero] at h2
  have h3 := congrArg (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP PP)) ho
  rwa [RingHom.map_mul, ← h2, mul_one, RingHom.map_zero] at h3

theorem resT_eq_zero_of_fixed {D : D7} {Q : Pl D.host.E} {e x : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (he : GlobalTheory.StdFrames.cpt Q e = 0) (hf : x = e * x) : resT Q x = 0 := by
  unfold resT
  rw [dite_eq_left hx]
  refine (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt Q ⟨x, hx⟩).2 ?_
  have h0 : GlobalTheory.StdFrames.cpt Q x = 0 := by rw [hf, RingHom.map_mul, he, zero_mul]
  show Valued.v (GlobalTheory.StdFrames.cpt Q x) < 1
  rw [h0, Valuation.map_zero]
  exact zero_lt_one

theorem resT_cP_hT_bwd_eq_zero : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ PP : Pl D.host.E, GlobalTheory.SeeConjChar.sideAt X h PP = true → ∀ M ∈ St β, ∀ i j : Fin D.R.k, GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j))) = 0 := by
  intro D X h β hF PP hs M hM i j
  have hb := X.vectorsInLattice.2.2
  have ho := X.ew_orth
  have hw := X.bwd_w i
  have h1 : GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 := by
    unfold sideAt at hs
    simpa only [decide_eq_true_eq] using hs
  have hfix : ∀ v, hA X.B.I (X.bwd i) v = X.ew * hA X.B.I (X.bwd i) v := fun v => by
    conv_lhs => rw [hw, unitaryCongruence.hA_smul_left, unitaryCongruence.sigA_sigA]
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h hb ho hfix
  subst h
  have hv := (hb j).1
  rw [GlobalTheory.SeeMatchOnto.Lf_eq] at hv
  have hv2 := (GlobalTheory.SeeMatchOnto.mem_hatL_iff_of_St hF hM _).1 hv
  have hv3 := (GlobalTheory.SeeMatchOnto.Lf_eq (D := D)).ge hv2
  have hint := unitaryCongruence.hA_int _ (hb i).2 hv3
  exact ⟨hint, resT_eq_zero_of_fixed hint (cpt_cP_eq_zero_of_orth ho h1) (hfix _)⟩

end GlobalTheory.SeeConjChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueCoordinatesInFrameLinearStabiliser
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

noncomputable section
namespace GlobalTheory.SeeConjGroup

section RedLemmas
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem redV_eq_of_int (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (h : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec v i ∈
      Formalism.L2.Herm.intAf F E) (i : Fin n) :
    redV β PP v i = resS F PP ⟨_, h i⟩ := by
  unfold redV
  rw [dite_eq_left (h i)]

end RedLemmas

theorem redV_add_smul_stab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), IsFrame β Λ → ∀ PP : Pl E, (∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∀ w ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP (v + w) = redV β PP v + redV β PP w) ∧ (∀ (c : Formalism.L2.Herm.intAf F E), ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP ((c : E ⊗[F] Formalism.L2.Herm.Af F) • v) = resS F PP c • redV β PP v) ∧ (∀ M ∈ St β, ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP ((M : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ v) = ((redFn β PP M : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) *ᵥ redV β PP v) := by
  intro F E _ _ _ _ _ n β Λ hF PP
  have hint : ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∀ i,
      ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec v i ∈
        Formalism.L2.Herm.intAf F E := fun v hv => (hF v).1 hv
  refine ⟨?_, ?_, ?_⟩
  · intro v hv w hw
    have hs : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec (v + w) i ∈
        Formalism.L2.Herm.intAf F E := by
      intro i
      rw [Matrix.mulVec_add]
      exact Subring.add_mem _ (hint v hv i) (hint w hw i)
    funext i
    rw [Pi.add_apply, redV_eq_of_int β PP _ hs, redV_eq_of_int β PP _ (hint v hv), redV_eq_of_int β PP _ (hint w hw),
      ← map_add]
    congr 1
    apply Subtype.ext
    simp [Matrix.mulVec_add]
  · intro c v hv
    have hs : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec
        ((c : E ⊗[F] Formalism.L2.Herm.Af F) • v) i ∈ Formalism.L2.Herm.intAf F E := by
      intro i
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      exact Subring.mul_mem _ c.2 (hint v hv i)
    funext i
    rw [Pi.smul_apply, smul_eq_mul, redV_eq_of_int β PP _ hs, redV_eq_of_int β PP _ (hint v hv), ← map_mul]
    congr 1
    apply Subtype.ext
    simp [Matrix.mulVec_smul]
  · rintro M ⟨y, rfl⟩ v hv
    set X : Fin n → Formalism.L2.Herm.intAf F E := fun j => ⟨_, hint v hv j⟩ with hX
    have hM : ((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * ((intGL F E n y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
          ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      simp [frGL, MulAut.conj_apply]
    have hkey : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec
        (((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ v) i =
        ((((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) *ᵥ X) i : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) := by
      intro i
      rw [hM, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul, ← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec, dotProduct, hX]
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rfl
    have hs : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec
        (((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ v) i ∈
          Formalism.L2.Herm.intAf F E := fun i => by rw [hkey i]; exact Subtype.property _
    funext i
    rw [redV_eq_of_int β PP _ hs, redFn_frGL]
    have e1 : (⟨_, hs i⟩ : Formalism.L2.Herm.intAf F E) = ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) *ᵥ X) i :=
      Subtype.ext (hkey i)
    rw [e1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [redV_eq_of_int β PP _ (hint v hv) j]
    rfl

end GlobalTheory.SeeConjGroup
end
end

