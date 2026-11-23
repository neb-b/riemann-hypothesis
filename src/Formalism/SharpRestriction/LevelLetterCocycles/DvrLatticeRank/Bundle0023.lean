module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0022
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0019
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0020
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0017
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0022
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalFiltrationHolds

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePf
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}
    (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))

theorem framepf_back (hT : IsCrys PD T.ρ) (Eπ : LetA O n) (h' M : ℕ)
    (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hEΔ : Eπ ∈ W.AΔ) (u : LetA O n) (huΔ : u ∈ W.AΔ)
    (hφ : W.φA π' ^ M = π' ^ M * Eπ ^ (4 * h') * u) :
    FramepfBack Bs π' c hπ0 hΔπ hR2 γ0 hu Eπ h' M := by
  intro H H' K₁ K₂ lam h₁ h₂
  obtain ⟨βφ, hβφ⟩ := framepf_phiBasis Bs hT
  let eb : Module.Basis (Fin Bs.r) O (LcQ W T π' c) :=
    Module.Basis.ofEquivFun (framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu)
  have heb : ∀ j, eb j = framepf_ebar Bs π' c hπ0 hΔπ hR2 γ0 hu j := fun j => by
    simp only [eb, Module.Basis.coe_ofEquivFun, framepf_ebar]
  have hΨ : ∀ (e : W.EE) j, framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H (e ⊗ₜ eb j) =
      e • ∑ m, W.φA (framepf_ι π' (c - 1) (H m j)) • W.φD T (Bs.b m) := fun e j => by
    rw [heb, framepf_Ψα_tmul, framepf_hh_ebar, framepf_φD_vec]
  have hΦ : ∀ a : Fin Bs.r → LetA O n,
      framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ H' (∑ k, a k • W.φD T (Bs.b k)) =
        ∑ j, algebraMap (LetA O n) W.EE (∑ k, a k * W.φA (framepf_ι π' (c - 1) (H' j k))) ⊗ₜ eb j :=
    fun a => by simp only [heb]; exact framepf_Ψβ_sum Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ H' a
  have hS : ∀ (Km : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) m k,
      u * W.φA (framepf_ι π' (c - 1) (Km m k)) ∈ W.AΔ := fun Km m k =>
    W.AΔ.mul_mem huΔ (framepf_φA_ι_mem π' c hπ0 hΔπ γ0 _)
  refine ⟨framepf_Ψβ Bs π' c hπ0 hΔπ hR2 γ0 hu βφ H',
    framepf_Ψβ_Lam Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ Eπ hEΔ h' hT H',
    framepf_Ψβ_J Bs π' c hπ0 hΔπ hR2 γ0 hu βφ hβφ Eπ h' M hT H',
    framepf_βα_core Bs π' Eπ h' M c huE eb (fun j k => W.φA (framepf_ι π' (c - 1) (H' j k)))
      (fun j k => W.φA (framepf_ι π' (c - 1) (H j k))) _ (hS K₁) lam (fun j k => ?_) _ _ hΨ hΦ,
    framepf_αβ_core Bs hT π' Eπ h' M c huE hEΔ eb (fun j k => W.φA (framepf_ι π' (c - 1) (H' j k)))
      (fun j k => W.φA (framepf_ι π' (c - 1) (H j k))) _ (hS K₂) lam (fun j k => ?_) _ _ hΨ hΦ⟩
  · rw [framepf_φA_ι_matmul Bs π' c hπ0, h₁, framepf_φA_ι_entry Bs π' c hπ0, hφ, mul_assoc _ u]
  · rw [framepf_φA_ι_matmul Bs π' c hπ0, h₂, framepf_φA_ι_entry Bs π' c hπ0, hφ, mul_assoc _ u]

end Local


set_option maxHeartbeats 1000000 in
theorem frame_pf : FrameStep := by
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hR h' hh' c
  exact framepf_rec D HW F Cm hA.1 l hl K LL hG π' E hR h' hh' c
    fun T hT Bs hπ0 hΔπ hR2 γ0 hu huE hEΔ u huΔ hφ =>
      framepf_back Bs π' c hπ0 hΔπ hR2 γ0 hu hT _ h' _ huE hEΔ u huΔ hφ

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfI
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLI

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem expS_neg (ζ : LL) {m : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T) {i : ℤ} (hi : i < 0) :
    expS W T c ζ a y i = 0 := by
  simp [expS, serC, if_neg (show ¬ (0 ≤ i) by omega)]

theorem ind_fil (τ : K →ₐ[Qp] LL) (U : PowerSeries LL) (hU : PowerSeries.constantCoeff U ≠ 0)
    {g : ℤ → T.V ⊗[Qp] BdR} {m₀ : ℤ} (hg : MLG.Bdd g m₀)
    (hH : ∀ j, serMul U g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j)) :
    ∀ j, g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
  have key : ∀ N : ℕ, ∀ j, j < m₀ + N → g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
    intro N
    induction N with
    | zero => intro j hj; rw [hg j (by omega)]; exact Submodule.zero_mem _
    | succ N ih =>
      intro j hj
      by_cases hjN : j < m₀ + N
      · exact ih j hjN
      · have hj' : j = m₀ + N := by push_cast at hj; omega
        have hs := hH j
        rw [MLG.serMul_eq_sum U hg j ((j - m₀).toNat + 1) le_rfl, Finset.sum_range_succ'] at hs
        have hrest : ∑ k ∈ Finset.range (j - m₀).toNat, PowerSeries.coeff (k + 1) U • g (j - ((k + 1 : ℕ) : ℤ)) ∈
            Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
          refine Submodule.sum_mem _ (fun k hk => Submodule.smul_mem _ _ ?_)
          rw [Finset.mem_range] at hk
          exact u3upPf_FilC_anti (PD := PD) T τ (by push_cast; omega) (ih _ (by push_cast; omega))
        have h0 := Submodule.sub_mem _ hs hrest
        rw [add_sub_cancel_left, PowerSeries.coeff_zero_eq_constantCoeff_apply, Nat.cast_zero, sub_zero] at h0
        exact (Submodule.smul_mem_iff _ hU).1 h0
  intro j
  exact key ((j - m₀).toNat + 1) j (by omega)

end Generic

end Formalism.MainNotions.N.Ln34.MLI

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalLiftFiltration
section
noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules PowerSeries

theorem universal_lift_filtration (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) (hdR : DdRFull D) (hDi : DiRank D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ)
    (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
    (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)) (hbrep : ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k))
    (S η m : ℕ) (upτ : Bool) (bτ : ℕ)
    (hj : JumpsInV ((D.loc l).PD K) T.ρ τ (deep upτ bτ S ∪ Set.Icc (-(η : ℤ)) η)) (hηb : η < bτ)
    (hm : ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV ((D.loc l).PD K) T.ρ τ a ≤ m) :
    (upτ = true →
      (∀ i : ℤ, i < -((bτ : ℤ) + S) → ∀ d : Fin r → ↥LL.1,
        Phi ((HW l).W K 1 LL hG) T c ζ rep d ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-i) → d = 0) ∧
      r ≤ finrank ↥LL.1 ((Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ bτ).comap (Phi ((HW l).W K 1 LL hG) T c ζ rep)) + m) ∧
    (upτ = false →
      finrank ↥LL.1 ((Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-(bτ : ℤ) + 1)).comap
        (Phi ((HW l).W K 1 LL hG) T c ζ rep)) ≤ m ∧
      ∀ d : Fin r → ↥LL.1,
        Phi ((HW l).W K 1 LL hG) T c ζ rep d ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-((bτ : ℤ) + S))) := by
  exact UniversalFiltration.universal_filtration_holds D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T hT c τ ζ hpt r bL rep hrep hbrep
    S η m upτ bτ hj hηb hm

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end

