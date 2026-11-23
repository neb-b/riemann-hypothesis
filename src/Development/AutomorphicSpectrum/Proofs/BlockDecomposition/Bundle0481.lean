module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0334
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0380
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0333
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
public import Development.AutomorphicSpectrum.Proofs.JetProofs.ScalarOnComplement
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionOpenCellModuloWhittaker
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Rodier.Bad

section Gen

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
  {P : Subgroup G} {τ : Representation ℂ P W}

theorem isClopen_supp (f : smoothPart (ind P τ)) : IsClopen {g | f.1.1 g ≠ 0} := by
  have ho : IsOpen {g : G | ind P τ g f.1 = f.1} := f.2
  have hlc : IsLocallyConstant f.1.1 := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x =>
      ⟨(fun y => x⁻¹ * y) ⁻¹' {g | ind P τ g f.1 = f.1}, ho.preimage (by fun_prop), ?_, ?_⟩
    · show ind P τ (x⁻¹ * x) f.1 = f.1
      simp
    · intro y hy
      have h : f.1.1 (x * (x⁻¹ * y)) = f.1.1 x := congrFun (congrArg Subtype.val hy) x
      rwa [mul_inv_cancel_left] at h
  exact (hlc.isClopen_fiber 0).compl

theorem ne_zero_left (f : smoothPart (ind P τ)) (p : P) (g : G) (hg : f.1.1 g ≠ 0) : f.1.1 (p * g) ≠ 0 := by
  intro h
  have h1 : τ p (f.1.1 g) = 0 := (f.1.2 p g).symm.trans h
  apply hg
  have h2 := congrArg (τ p⁻¹) h1
  rw [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2
  exact h2

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cell_mul {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N} {w : Equiv.Perm (Fin N)} {g n : GL (Fin N) k}
    (hg : g ∈ cell k d hd w) (hn : n ∈ unipB k (Fin N)) : g * n ∈ cell k d hd w := by
  obtain ⟨p, hp, m, hm, rfl⟩ := hg
  exact ⟨p, hp, m * n, mul_mem hm hn, by simp only [mul_assoc]⟩

theorem kill_cell (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {h N : ℕ} (d : Fin h → ℕ)
    (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (f : IndSp (stdBlocks d hd) ρ)
    (w : Equiv.Perm (Fin N)) (hbad : cell k d hd w ≠ cell k d hd (wOpen d hd))
    (hcl : IsClosed ({g | f.1.1 g ≠ 0} ∩ cell k d hd w)) :
    ∃ f' : IndSp (stdBlocks d hd) ρ,
      f - f' ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) ∧
      (∀ g, f'.1.1 g ≠ 0 → ∃ n ∈ unipB k (Fin N), f.1.1 (g * n) ≠ 0) ∧
      ∀ g ∈ cell k d hd w, f'.1.1 g = 0 := by
  classical
  obtain ⟨L, hLm, hLc, hLU, hLex⟩ := GlobalTheory.CompanionTheory.UnipExhaust.exists_monotone_compact_exhaustion k N (unipB k (Fin N)) le_rfl
    GlobalTheory.LocLanglands.InvInt.isClosed_unipB
  have hcellL : cell k d hd w =
      {g | ∃ p ∈ parab k (stdBlocks d hd), ∃ j, ∃ n ∈ L j, g = p * pm k w * n} := by
    ext g
    constructor
    · rintro ⟨p, hp, n, hn, rfl⟩
      obtain ⟨j, hj⟩ := hLex n hn
      exact ⟨p, hp, j, n, hj, rfl⟩
    · rintro ⟨p, hp, j, n, hn, rfl⟩
      exact ⟨p, hp, n, hLU j hn, rfl⟩
  obtain ⟨i, j, hij, hb⟩ := (exists_adjacent_blk_lt_or_cell_eq_open k h N d hd w).resolve_right hbad
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hψ1 (by ext x; simp [hc x])
  obtain ⟨u, hu, hwu, hrad⟩ := GlobalTheory.CompanionTheory.Rodier.RootElt.exists_root_conj_mem_unipRad k ψ h N d hd w i j hij hb t
  have : T2Space (GL (Fin N) k) := by
    obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
    infer_instance
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.CompanionTheory.BaireCoset.baire_double_coset (parab k (stdBlocks d hd))
    (by
      obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
      have heq : (parab k (stdBlocks d hd) : Set (GL (Fin N) k)) =
          ⋂ i, ⋂ j, ⋂ _ : blk (stdBlocks d hd) j < blk (stdBlocks d hd) i,
            {g : GL (Fin N) k | g.val i j = 0} := by
        ext g
        simp only [SetLike.mem_coe, mem_parab, Set.mem_iInter, Set.mem_setOf_eq]
      rw [heq]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const)
    (GlobalTheory.SplitWeil.KO k (Fin N) : Set (GL (Fin N) k)) GlobalTheory.SplitFlip.isCompact_KO
    (fun g => by
      obtain ⟨p, c, hc, e⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul (stdBlocks d hd) g
      exact ⟨p, p.2, c, hc, e⟩)
    L hLm hLc (pm k w) {g | f.1.1 g ≠ 0} (isClopen_supp f).isOpen
    (fun p hp g hg => ne_zero_left f ⟨p, hp⟩ g hg) (by rw [← hcellL]; exact hcl)
  obtain ⟨j₁, hj₁⟩ := hLex u hu
  have hJ0 : L j₀ ≤ L (max j₀ j₁) := hLm (le_max_left _ _)
  have hJ1 : L j₁ ≤ L (max j₀ j₁) := hLm (le_max_right _ _)
  generalize max j₀ j₁ = J at hJ0 hJ1
  let θ : L J →* ℂˣ := (whitChar ψ N).comp (Subgroup.inclusion (hLU J))
  have hθ : IsOpen (θ.ker : Set (L J)) :=
    (GlobalTheory.Whittaker.isSmoothChar_whitChar hψ).preimage
      (Continuous.subtype_mk continuous_subtype_val _ : Continuous (Subgroup.inclusion (hLU J)))
  obtain ⟨f', h1, h2, h3⟩ := GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd (parab k (stdBlocks d hd)) _ (L J) (hLc J) θ hθ f
  have hu' : u ∈ L J := hJ1 hj₁
  have hfw : f'.1.1 (pm k w) = 0 := by
    have e1 := h3 ⟨u, hu'⟩ (pm k w)
    have hθu : θ ⟨u, hu'⟩ = Circle.toUnits (ψ t) := hwu
    have hq : leviProj k (stdBlocks d hd) ⟨_, unipRad_le_parab k _ hrad⟩ = 1 :=
      (coe_mem_unipRad k (⟨_, unipRad_le_parab k _ hrad⟩ : parab k (stdBlocks d hd))).1 hrad
    have e2 := parInd_law (stdBlocks d hd) ρ f' ⟨_, unipRad_le_parab k _ hrad⟩ (pm k w)
    rw [hq] at e2
    simp only [map_one, Units.val_one, one_smul, Module.End.one_apply, inv_mul_cancel_right] at e2
    rw [e2] at e1
    rw [hθu] at e1
    have hne : ((Circle.toUnits (ψ t) : ℂˣ) : ℂ) ≠ 1 := fun e => ht (Circle.ext (by simpa using e))
    have h0 : (((Circle.toUnits (ψ t) : ℂˣ) : ℂ) - 1) • f'.1.1 (pm k w) = 0 := by
      rw [sub_smul, one_smul, ← e1, sub_self]
    exact (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)
  refine ⟨f', ?_, ?_, ?_⟩
  · refine (Submodule.span_mono ?_) h1
    rintro _ ⟨n, v, rfl⟩
    exact ⟨⟨n.1, hLU J n.2⟩, v, rfl⟩
  · intro g hg
    obtain ⟨l, hl, hne⟩ := h2 g hg
    exact ⟨l, hLU J hl, hne⟩
  · intro g hg
    by_contra hne
    obtain ⟨l, hl, hfl⟩ := h2 g hne
    have hgl := cell_mul hg (hLU J hl)
    obtain ⟨p, hp, n, hn, e⟩ := hj₀ (g * l) hfl (by rw [hcellL] at hgl; exact hgl)
    have hl2 : n * l⁻¹ ∈ L J := mul_mem (hJ0 hn) (inv_mem hl)
    have hg' : g = (⟨p, hp⟩ : parab k (stdBlocks d hd)) * (pm k w * (n * l⁻¹)) := by
      show g = p * (pm k w * (n * l⁻¹))
      rw [← mul_assoc, ← mul_assoc, ← e]
      group
    apply hne
    have e3 := h3 ⟨_, hl2⟩ (pm k w)
    rw [hfw, smul_zero] at e3
    rw [hg', f'.1.2 ⟨p, hp⟩, e3, map_zero]

end GlobalTheory.CompanionTheory.Rodier.Bad

namespace GlobalTheory.CompanionTheory.Rodier


open Bad in
theorem exists_open_congr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (f : IndSp (stdBlocks d hd) ρ),
    ∃ f₀ ∈ openFns d hd ρ, f - f₀ ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) := by
  intro k _ _ _ _ ψ hψ hψ1 h N d hd W _ _ ρ f
  classical
  obtain ⟨hcov, ht, hconst, hclos, hmax⟩ := GlobalTheory.CompanionTheory.Rodier.CellOrder.cells_main k h N d hd
  let bad : IndSp (stdBlocks d hd) ρ → Finset (Equiv.Perm (Fin N)) := fun f =>
    Finset.univ.filter fun w => cell k d hd w ≠ cell k d hd (wOpen d hd) ∧ ∃ g ∈ cell k d hd w, f.1.1 g ≠ 0
  have mem_bad : ∀ f w, w ∈ bad f ↔
      cell k d hd w ≠ cell k d hd (wOpen d hd) ∧ ∃ g ∈ cell k d hd w, f.1.1 g ≠ 0 := fun f w => by
    simp [bad]
  suffices H : ∀ n, ∀ f, (bad f).card = n → ∃ f₀ ∈ openFns d hd ρ,
      f - f₀ ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) from H _ f rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hn
  rcases (bad f).eq_empty_or_nonempty with hE | hne
  · refine ⟨f, ?_, by simp⟩
    intro g hg
    obtain ⟨w, hw⟩ := hcov g
    by_contra hno
    have hb : w ∈ bad f := (mem_bad f w).2 ⟨fun e => hno (e ▸ hw), g, hw, hg⟩
    simp [hE] at hb
  · obtain ⟨w, hw, hmin⟩ := Finset.exists_min_image (bad f) (fun w => ht (pm k w)) hne
    obtain ⟨hbad, hmet⟩ := (mem_bad f w).1 hw
    have hcl : IsClosed ({g | f.1.1 g ≠ 0} ∩ cell k d hd w) := by
      refine isClosed_of_closure_subset fun x hx => ?_
      have hxS : x ∈ {g | f.1.1 g ≠ 0} :=
        (isClopen_supp f).isClosed.closure_subset_iff.2 Set.inter_subset_left hx
      refine ⟨hxS, ?_⟩
      rcases hclos w (closure_mono Set.inter_subset_right hx) with hC | hlt
      · exact hC
      · exfalso
        have hlt' : ht x < ht (pm k w) := hlt
        obtain ⟨w', hw'⟩ := hcov x
        by_cases ho : cell k d hd w' = cell k d hd (wOpen d hd)
        · have h1 : ht x = ht (pm k (wOpen d hd)) := by
            rw [hconst w' x hw']
            refine (hconst w' _ ?_).symm
            rw [ho]
            exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
          have := hmax w hbad
          omega
        · have h1 := hmin w' ((mem_bad f w').2 ⟨ho, x, hw', hxS⟩)
          have h2 := hconst w' x hw'
          omega
    obtain ⟨f', h1, h2, h3⟩ := kill_cell ψ hψ hψ1 d hd ρ f w hbad hcl
    have hsub : bad f' ⊂ bad f := by
      refine (Finset.ssubset_iff_of_subset fun w' hw' => ?_).2 ⟨w, hw, fun hw' => ?_⟩
      · obtain ⟨hb, g, hg, hfg⟩ := (mem_bad f' w').1 hw'
        obtain ⟨n, hn, hfn⟩ := h2 g hfg
        exact (mem_bad f w').2 ⟨hb, g * n, cell_mul hg hn, hfn⟩
      · obtain ⟨_, g, hg, hfg⟩ := (mem_bad f' w).1 hw'
        exact hfg (h3 g hg)
    have hlt : (bad f').card < n := hn ▸ Finset.card_lt_card hsub
    obtain ⟨f₀, hf₀, h4⟩ := ih _ hlt f' rfl
    refine ⟨f₀, hf₀, ?_⟩
    have := add_mem h1 h4
    simpa using this

end GlobalTheory.CompanionTheory.Rodier

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableDescendOfCover
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

namespace GlobalTheory.CompanionTheory.AutCover

open scoped Pointwise

theorem integrable_descend_of_cover : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (S : Set (GA D V)),
    MeasurableSet S → (∀ g, ∃ γ ∈ GQ V, ∃ s ∈ S, g = γ * s) → ∀ φ : GA D V → ℂ, GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ →
      Measurable φ → IntegrableOn φ S μ → Integrable (descend (GQ V) φ) (autMeasure V μ) := by
  intro D V μ _ S hS hcov φ hinv hφ hint
  have hmeas : AEStronglyMeasurable (descend (GQ V) φ) (autMeasure V μ) :=
    (GlobalTheory.AutomorphicL2Unitary.aestronglyMeasurable_quotMeasure_iff_lift).2 (by
      rw [hinv.lift_descend]
      exact hφ.aestronglyMeasurable)
  refine ⟨hmeas, ?_⟩
  have hfin : ∫⁻ g in S, ‖φ g‖ₑ ∂μ < ⊤ := hint.2
  have hmf : AEMeasurable (S.indicator fun g => ‖φ g‖ₑ) μ := (hφ.enorm.indicator hS).aemeasurable
  have key := GlobalTheory.AutomorphicL2Unitary.lintegral_eq_lintegral_tsum (Γ := GQ V) (μ := μ) hmf
  rw [lintegral_indicator hS] at key
  show ∫⁻ q, ‖descend (GQ V) φ q‖ₑ ∂(autMeasure V μ) < ⊤
  refine lt_of_le_of_lt ?_ hfin
  rw [key]
  apply lintegral_mono
  intro q
  obtain ⟨γ, hγ, s, hs, hq⟩ := hcov q.out
  have e : (((⟨γ, hγ⟩ : GQ V)⁻¹ : GQ V) : GA D V) * q.out = s := by
    show γ⁻¹ * q.out = s
    rw [hq, inv_mul_cancel_left]
  have hmem : (((⟨γ, hγ⟩ : GQ V)⁻¹ : GQ V) : GA D V) * q.out ∈ S := by
    rw [e]
    exact hs
  have h1 : S.indicator (fun g => ‖φ g‖ₑ) ((((⟨γ, hγ⟩ : GQ V)⁻¹ : GQ V) : GA D V) * q.out) = ‖φ q.out‖ₑ := by
    rw [Set.indicator_of_mem hmem, hinv _ (((⟨γ, hγ⟩ : GQ V)⁻¹ : GQ V)).2]
  show ‖φ q.out‖ₑ ≤ _
  rw [← h1]
  exact ENNReal.le_tsum (f := fun γ : GQ V => S.indicator (fun g => ‖φ g‖ₑ) ((γ : GA D V) * q.out)) _

end GlobalTheory.CompanionTheory.AutCover
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIsoFrameFirstCols
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.CompanionTheory.RegInt

variable {D : D7} {V : HSp D} {r : ℕ}

def firstCols (X : Matrix (Fin V.rank) (Fin r) D.host.E) (j : Fin r) :
    Matrix (Fin V.rank) (Fin (j.val + 1)) D.host.E := X.submatrix id (Fin.castLE j.2)

def root (t : Fin r → ℝ) (j : Fin r) : ℝ := if h : j.val + 1 < r then t j / t ⟨j.val + 1, h⟩ else t j

theorem isIsoFrame_firstCols {X Y : Matrix (Fin V.rank) (Fin r) D.host.E}
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r) : IsIsoFrame V (firstCols X j) := by
  refine ⟨Nat.succ_pos _, ?_, ?_⟩
  · have h1 : LinearIndependent D.host.E (fun i : Fin r => fun a : Fin V.rank => X a i) := by
      refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
      have h3 : ∀ a, ∑ l, g l * X a l = 0 := fun a => by
        have := congrFun hg a
        simpa [Finset.sum_apply, mul_comm] using this
      have h4 : (fun l => (D.sp.cm.sig : D.host.E →+* D.host.E) (g l)) ᵥ*
          Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X = 0 := by
        funext a
        have := congrArg (D.sp.cm.sig : D.host.E →+* D.host.E) (h3 a)
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul, map_zero] at this
        simpa [Matrix.vecMul, dotProduct, Formalism.UG.cT] using this
      have h5 := congrArg (fun v => v ᵥ* (V.gram * Y)) h4
      simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul, ← Matrix.mul_assoc, hW.xy, Matrix.vecMul_one] at h5
      have h6 := congrFun h5 i
      simpa using h6
    have h2 : (firstCols X j).transpose = (fun i : Fin r => fun a : Fin V.rank => X a i) ∘ Fin.castLE j.2 := by
      funext i a; rfl
    change LinearIndependent D.host.E (firstCols X j).transpose
    rw [h2]
    exact h1.comp _ (Fin.castLE_injective _)
  · have h := hW.xx
    refine Matrix.ext fun a b => ?_
    have := congrFun (congrFun h (Fin.castLE j.2 a)) (Fin.castLE j.2 b)
    simpa [Matrix.mul_apply, Formalism.UG.cT, firstCols] using this

end GlobalTheory.CompanionTheory.RegInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicHyperbolicComplement
section
open Matrix

namespace GlobalTheory.CompanionTheory.Dblock.CompFrame

theorem exists_comp_frame : ∀ {n D : ℕ} (ε : Fin n → Bool) (C : Matrix (Fin n) (Fin D) ℂ),
    Cᴴ * C = 1 → Cᴴ * Formalism.REAL.Jm ε * C = 0 →
    ∃ (m : ℕ) (R : Matrix (Fin n) (Fin m) ℂ) (ε' : Fin m → Bool),
      Rᴴ * R = 1 ∧ Formalism.REAL.Jm ε * R = R * Formalism.REAL.Jm ε' ∧ Cᴴ * R = 0 ∧
      C * Cᴴ + Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε + R * Rᴴ = 1 := by
  intro n D ε C h1 h2
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := GlobalTheory.CompanionTheory.HCSide.CentreNone.Jm_herm ε
  generalize hJ : Formalism.REAL.Jm ε = J at *
  have hAA : C * Cᴴ * (C * Cᴴ) = C * Cᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Cᴴ, h1, Matrix.one_mul]
  have hAB : C * Cᴴ * (J * C * Cᴴ * J) = 0 := by
    have e : C * Cᴴ * (J * C * Cᴴ * J) = C * (Cᴴ * J * C) * Cᴴ * J := by
      simp only [Matrix.mul_assoc]
    rw [e, h2]; simp
  have hBA : J * C * Cᴴ * J * (C * Cᴴ) = 0 := by
    have e : J * C * Cᴴ * J * (C * Cᴴ) = J * C * (Cᴴ * J * C) * Cᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, h2]; simp
  have hBB : J * C * Cᴴ * J * (J * C * Cᴴ * J) = J * C * Cᴴ * J := by
    have e : J * C * Cᴴ * J * (J * C * Cᴴ * J) = J * C * (Cᴴ * (J * J) * C) * Cᴴ * J := by
      simp only [Matrix.mul_assoc]
    rw [e, hJJ, Matrix.mul_one, h1, Matrix.mul_one]
  have hPh : (1 - C * Cᴴ - J * C * Cᴴ * J)ᴴ = 1 - C * Cᴴ - J * C * Cᴴ * J := by
    simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose, hJh,
      Matrix.mul_assoc]
  have hPP : (1 - C * Cᴴ - J * C * Cᴴ * J) * (1 - C * Cᴴ - J * C * Cᴴ * J) =
      1 - C * Cᴴ - J * C * Cᴴ * J := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hAA, hAB, hBA, hBB]
    abel
  have hPJ : J * (1 - C * Cᴴ - J * C * Cᴴ * J) = (1 - C * Cᴴ - J * C * Cᴴ * J) * J := by
    have e1 : J * (J * C * Cᴴ * J) = C * Cᴴ * J := by
      simp only [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
    have e2 : J * C * Cᴴ * J * J = J * (C * Cᴴ) := by
      rw [Matrix.mul_assoc _ J J, hJJ, Matrix.mul_one, Matrix.mul_assoc]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, e1, e2]
    abel
  subst hJ
  obtain ⟨m, ε', R, r1, r2, r3⟩ := GlobalTheory.CompanionTheory.HCSide.CentreNone.exists_frame_J hPh hPP hPJ
  refine ⟨m, R, ε', r1, r3, ?_, ?_⟩
  · have hCP : Cᴴ * (1 - C * Cᴴ - Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε) = 0 := by
      have e : Cᴴ * (Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε) =
          (Cᴴ * Formalism.REAL.Jm ε * C) * Cᴴ * Formalism.REAL.Jm ε := by
        simp only [Matrix.mul_assoc]
      rw [Matrix.mul_sub, Matrix.mul_sub, e, h2, ← Matrix.mul_assoc, h1]
      simp
    have e : R = (1 - C * Cᴴ - Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε) * R := by
      rw [← r2, Matrix.mul_assoc, r1, Matrix.mul_one]
    rw [e, ← Matrix.mul_assoc, hCP, Matrix.zero_mul]
  · rw [r2]; abel

end GlobalTheory.CompanionTheory.Dblock.CompFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointL2
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.LieSkew

theorem continuous_infGL_map (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E) :=
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  refine Continuous.units_map _ ?_
  exact continuous_const.add (continuous_id.matrix_map hs)

theorem inner_R_R {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (g : G) (F F' : L2 Γ μ) :
    inner ℂ (R Γ μ g F) (R Γ μ g F') = inner ℂ F F' :=
  (LinearIsometry.mk (R Γ μ g).toLinearMap (norm_R g)).inner_map_map F F'

theorem lie_skew : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : GlobalTheory.CuspRep.Lie E a) (φ ψ : Sm E a) (hφ : MemL2Quotient (latticeGL E a) μ φ.1) (hψ : MemL2Quotient (latticeGL E a) μ ψ.1) (hXφ : MemL2Quotient (latticeGL E a) μ (lie E a X φ).1) (hXψ : MemL2Quotient (latticeGL E a) μ (lie E a X ψ).1), Continuous φ.1 → Continuous ψ.1 → Continuous (lie E a X φ).1 → Continuous (lie E a X ψ).1 → inner ℂ hXφ.toL2 hψ.toL2 = - inner ℂ hφ.toL2 hXψ.toL2 := by
  intro E _ _ _ a μ _ _ X φ ψ hφ hψ hXφ hXψ cφ cψ cXφ cXψ
  obtain ⟨c, hc, h0, hadd, hd, -⟩ := _root_.GlobalTheory.CompanionTheory.LieCurve.exists_curve E a X
  have hγ : Continuous fun t => infGL E a (c t) := (continuous_infGL_map E a).comp hc
  have hγ0 : infGL E a (c 0) = 1 := by rw [h0, map_one]
  have hγa : ∀ s t, infGL E a (c (s + t)) = infGL E a (c s) * infGL E a (c t) := fun s t => by
    rw [hadd, map_mul]
  have d1 := _root_.GlobalTheory.CompanionTheory.TransDeriv.hasDerivAt_R (GA E a) (latticeGL E a) μ φ.1 (lie E a X φ).1 hφ hXφ
    (fun t => infGL E a (c t)) cφ cXφ hγ hγ0 hγa (fun g => hasDerivAt_curve φ g c X h0 hd) 0
  have d2 := _root_.GlobalTheory.CompanionTheory.TransDeriv.hasDerivAt_R (GA E a) (latticeGL E a) μ ψ.1 (lie E a X ψ).1 hψ hXψ
    (fun t => infGL E a (c t)) cψ cXψ hγ hγ0 hγa (fun g => hasDerivAt_curve ψ g c X h0 hd) 0
  have d3 := d1.inner ℂ d2
  have hconst : (fun t : ℝ => inner ℂ (R (latticeGL E a) μ (infGL E a (c t)) hφ.toL2)
      (R (latticeGL E a) μ (infGL E a (c t)) hψ.toL2)) = fun _ => inner ℂ hφ.toL2 hψ.toL2 :=
    funext fun t => inner_R_R _ μ _ _ _
  rw [hconst] at d3
  have h := d3.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [hγ0, map_one, ContinuousLinearMap.one_apply] at h
  exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans h)

end GlobalTheory.CompanionTheory.LieSkew
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormFinitePlaceBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_norm_finite_place_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Type) [Fintype J] (v : Pl (F := F)) (u : J → E) (δ : (Fv F v ⊗[F] E)ˣ) (z : J → Fv F v ⊗[F] E) (c : ℝ≥0),
    (∀ f, z f = ((1 : Fv F v) ⊗ₜ[F] u f) * δ.1) → (∀ f, absFin F v (z f) ≤ c) →
    GlobalTheory.Doubling.absEv F E v δ * locFin σ v u ≤ c ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.absEv_mul_locFin_le | exact GlobalTheory.CompanionTheory.GodementH.absEv_mul_locFin_le | (intros; apply GlobalTheory.CompanionTheory.GodementH.absEv_mul_locFin_le <;> assumption)
end

