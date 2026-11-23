module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0328
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiFactorsLocalFlat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFreeEntryTranslationLawsBesselToJaco
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFlatMapLocalUnipotentTranslationLaw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeisenbergCombinationSplitPlaceDatum
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocComb

variable {D : D7}

theorem comb_add (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (c + c') f = comb ψ S T c f + comb ψ S T c' f :=
  Finsupp.sum_add_index' (h := fun u (a : ℂ) => a • heisO ψ S T u f) (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

theorem comb_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (a • c) f = a • comb ψ S T c f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, GlobalTheory.HeisComb.comb_eq_sum,
    Finsupp.sum_smul_index' (h := fun u (a : ℂ) => a • heisO ψ S T u f) fun _ => zero_smul _ _, Finsupp.smul_sum]
  simp only [smul_eq_mul, mul_smul]

theorem comb_single (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (y : WO S T) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single y 1) f = heisO ψ S T y f := by
  rw [GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum_single_index (h := fun u (a : ℂ) => a • heisO ψ S T u f) (zero_smul _ _),
    one_smul]

theorem heis_comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {e : AE D} {y : WO S T} (hy : IsHalf e y) {c : WO S T →₀ ℂ}
    (hc : ∀ w ∈ c.support, IsHalf e w) :
    ∃ c' : WO S T →₀ ℂ, (∀ w ∈ c'.support, IsHalf e w) ∧ ∀ f, comb ψ S T c' f = heisO ψ S T y (comb ψ S T c f) := by
  obtain ⟨c', h1, h2⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 (Finsupp.single y 1) c
  refine ⟨c', fun w hw => ?_, fun f => by rw [h2, comb_single]⟩
  obtain ⟨x, hx, z, hz, rfl⟩ := h1 w hw
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx), add_comm]
  exact (Witness.half_add hy).2 (hc z hz)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']


omit [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] in
theorem trans_mem_SB {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (x : Matrix Y Y' k) :
    (fun t => Φ (t + x)) ∈ SB (Matrix Y Y' k) :=
  ⟨hΦ.1.comp_continuous (continuous_add_const x), hΦ.2.comp_homeomorph (Homeomorph.addRight x)⟩


omit [DecidableEq Y] [DecidableEq Y'] in
theorem modul_mem_SB {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {Φ : Matrix Y Y' k → ℂ}
    (hΦ : Φ ∈ SB (Matrix Y Y' k)) (b : Matrix Y Y' k) : (fun t => Inhab.pairing ψ t b * Φ t) ∈ SB (Matrix Y Y' k) := by
  have hψ : IsLocallyConstant ψ := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    filter_upwards [((isOpen_cball d).preimage (continuous_sub_right x)).mem_nhds
      (show x - x ∈ cball d by simp [cball])] with z hz
    rw [← add_sub_cancel x z, AddChar.map_add_eq_mul, (hd d).2 le_rfl _ hz, mul_one]
  have h2 : IsLocallyConstant fun t : Matrix Y Y' k => Inhab.pairing ψ t b :=
    (hψ.comp_continuous (f := fun t : Matrix Y Y' k => ∑ r, ∑ q, b r q * t r q) (by fun_prop)).comp fun z : Circle => (z : ℂ)
  exact ⟨h2.mul hΦ.1, hΦ.2.mul_left⟩

theorem exists_comb : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ Φ₀ Φ : SB (Matrix Y Y' k), Φ₀ ≠ 0 → ∃ c : WO S T →₀ ℂ, (∀ w ∈ c.support, IsHalf (p.e + cA D p.e) w) ∧ ∀ Tm, p.IsModel ψ FS FT Tm → Tm Φ = comb ψ S T c (Tm Φ₀) := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ Φ₀ Φ hΦ₀
  classical
  obtain ⟨⟨ψk, hψk⟩, hcn, -, -, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨hcont, hne⟩ := hcn ψk hψk
  obtain ⟨d, hd⟩ := exists_hasConductor_of_continuous ψk hcont hne
  obtain ⟨hup, -, -, hsymk, hsurj⟩ := GlobalTheory.LocSympl.halves_at_split D k p Y Y' S T FS FT ψ ψk hψk
  obtain ⟨-, hec, -⟩ := p.split
  have hce : cA D p.e * p.e = 0 := by rw [mul_comm, hec]
  have half1 : ∀ u : WO S T, IsHalf p.e u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hce, zero_mul, add_zero, hu i j]
  have half2 : ∀ u : WO S T, IsHalf (cA D p.e) u → IsHalf (p.e + cA D p.e) u := fun u hu i j => by
    rw [add_mul, hu i j, ← hu i j, ← mul_assoc, hec, zero_mul, zero_add, hu i j]
  let M : Submodule ℂ (SB (Matrix Y Y' k)) :=
    { carrier := {Ψ | ∃ c : WO S T →₀ ℂ, (∀ w ∈ c.support, IsHalf (p.e + cA D p.e) w) ∧
        ∀ Tm, p.IsModel ψ FS FT Tm → Tm Ψ = comb ψ S T c (Tm Φ₀)}
      zero_mem' := ⟨0, by simp, fun Tm _ => by simp [comb]⟩
      add_mem' := by
        rintro a b ⟨c, h1, h2⟩ ⟨c', h1', h2'⟩
        refine ⟨c + c', fun w hw => ?_, fun Tm h => by rw [map_add (f := _), comb_add, h2 Tm h, h2' Tm h]⟩
        exact (Finset.mem_union.1 (Finsupp.support_add hw)).elim (h1 w) (h1' w)
      smul_mem' := by
        rintro a b ⟨c, h1, h2⟩
        exact ⟨a • c, fun w hw => h1 w (Finsupp.support_smul hw), fun Tm h => by rw [map_smul, comb_smul, h2 Tm h]⟩ }
  have key : SB (Matrix Y Y' k) ≤ M.map (SB (Matrix Y Y' k)).subtype := by
    refine Inhab.sb_le hd ?_ ?_ Φ₀.2 (fun h => hΦ₀ (Subtype.ext h)) ⟨Φ₀, ⟨Finsupp.single 0 1, fun w hw => ?_, fun Tm _ => ?_⟩, rfl⟩
    · rintro x _ ⟨Ψ, ⟨c, h1, h2⟩, rfl⟩
      obtain ⟨c', h3, h4⟩ := heis_comb ψ S T (half1 _ (hup x).1) h1
      exact ⟨⟨_, trans_mem_SB Ψ.2 x⟩, ⟨c', h3, fun Tm h => by rw [h4, ← h2 Tm h]; exact h.trans x Ψ _ fun _ => rfl⟩, rfl⟩
    · rintro b _ ⟨Ψ, ⟨c, h1, h2⟩, rfl⟩
      obtain ⟨y, hy, hyb⟩ := hsurj b
      obtain ⟨c', h3, h4⟩ := heis_comb ψ S T (half2 _ hy) h1
      refine ⟨⟨_, modul_mem_SB hd Ψ.2 b⟩, ⟨c', h3, fun Tm h => ?_⟩, rfl⟩
      rw [h4, ← h2 Tm h]
      refine h.modul y hy Ψ _ fun t => ?_
      rw [hsymk t y hy, hyb t]
      rfl
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hw)]
      exact fun i j => mul_zero _
    · rw [comb_single]
      funext w
      show _ = ψ (symplOH S T w 0) * Tm Φ₀ (w + 0)
      rw [symplOH, GlobalTheory.PlaceModel.symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]
  obtain ⟨Ψ, hΨ, e⟩ := key Φ.2
  rw [← show Ψ = Φ from Subtype.ext e]
  exact hΨ

end GlobalTheory.LocComb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMovedNotProportional
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.SeeSaw

namespace GlobalTheory.PlaceCompare.Spherical

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n'' n' n : Type} [Fintype n''] [DecidableEq n''] [Fintype n'] [DecidableEq n'] [Fintype n] [DecidableEq n]

end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum IsDedekindDomain NumberField
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_unram_char (D : D7) (n : ℕ) :
    ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ n ∧ UnramEverywhere D χ := by
  obtain ⟨η, h1, h2, h3, -⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  refine ⟨η ^ n, ⟨?_, fun x => ?_⟩, ⟨h3.1, fun e he a => ?_⟩, fun x a b c => ?_⟩
  · have : ((η ^ n : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ n := by
      funext x; simp
    rw [this]
    exact h1.1.pow n
  · rw [MonoidHom.pow_apply, h1.2 x, one_pow]
  · rw [MonoidHom.pow_apply, h3.2 e he a, pow_one]
  · rw [MonoidHom.pow_apply, h2 x a b c, one_pow]

end Global

end GlobalTheory.PlaceCompare.Spherical

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardCartanInvolutionCommuteCompact
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.KComm

variable {D : D7}

theorem comm_of_unitary_isom {m : ℕ} {u J : Matrix (Fin m) (Fin m) ℂ} (hu : uᴴ * u = 1) (hJ : uᴴ * J * u = J) :
    u * J = J * u := by
  have hu' : u * uᴴ = 1 := mul_eq_one_comm.1 hu
  calc u * J = u * (uᴴ * J * u) := by rw [hJ]
    _ = (u * uᴴ) * J * u := by simp only [Matrix.mul_assoc]
    _ = J * u := by rw [hu', Matrix.one_mul]

theorem compAt_K_comm (θ : InfFam D) (hθ : IsInfFam θ) (n : ℕ) (k : G D n) (hk : k ∈ K D n) (τ : D.what₂.Tau) :
    compAt θ τ (mat k) * blk4 0 1 (-1) 0 = blk4 0 1 (-1) 0 * compAt θ τ (mat k) := by
  have e1 : compAt θ τ (mat k) = Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (Jst D n) (θ τ) k := rfl
  have e2 : θ τ = AdelicU.infProj (embOverOf D τ) := AdelicU.eq_infProj hθ (embOverOf D τ) rfl
  have hk' : k ∈ AdelicU.levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1 := hk
  have hw := (AdelicU.mem_levelAll.1 hk').2 (placeOf D τ)
  have hunit := (GlobalTheory.Doubling.mem_stabArch_iff_unitary (isCMExt_host D) (embOverOf D τ) (Jst D n) 1 k).1 hw
  rw [inv_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_one _ (map_zero _) (map_one _)] at hunit
  simp only [Matrix.one_mul, Matrix.mul_one] at hunit
  rw [← e2, ← e1] at hunit
  have hiso := (AdelicU.archEquiv (Jst D n) (isCMExt_host D) (embOverOf D τ)
    (AdelicU.projArch D.sp.cm.sig (Jst D n) (placeOf D τ) k)).2
  have hiso' : (compAt θ τ (mat k))ᴴ * (Jst D n).map (embOverOf D τ).1 * compAt θ τ (mat k) =
      (Jst D n).map (embOverOf D τ).1 := by
    rw [e1, e2, AdelicU.infMat_infProj (Jst D n) (isCMExt_host D)]
    exact hiso
  rw [Jst, GlobalTheory.CartanPt.blkJ_map] at hiso'
  exact comm_of_unitary_isom hunit hiso'

end GlobalTheory.StdUnn.KComm

namespace GlobalTheory.StdUnn.KComm

theorem exists_stdInv_comm_K : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ θ : InfFam D, IsInfFam θ → ∃ s' : RealMat (dblSp A), IsStdInv A μ s' ∧ ∀ k : GA D (dblSp A), κ k ∈ K D A.rank → ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * s' τ = s' τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) := by
  intro D A μ hμ κ hκ θ hθ
  obtain ⟨k₀, -, hk₀⟩ := GlobalTheory.CartanPt.exists_mem_K_compAt_eq_stdInv D θ hθ A.rank μ hμ
  have hch : ∀ g τ, (Tm A μ).map (tauE D τ) * compAt θ τ (mat (κ g)) =
      compAt θ τ (Formalism.L2.Theta.mt (dblSp A) g) * (Tm A μ).map (tauE D τ) := by
    intro g τ
    have h2 := congrArg (compAt θ τ) (hκ g)
    have hr : compAt θ τ (rat (Tm A μ)) = (Tm A μ).map (tauE D τ) := GlobalTheory.AdForm.RatMove.compAt_rat hθ τ _
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.AdForm.RatMove.compAt_mul, hr] at h2
    exact h2
  refine ⟨fun τ => compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k₀)), fun τ => ?_, fun k hk τ => ?_⟩
  · have h := hch (κ.symm k₀) τ
    rw [κ.apply_symm_apply, hk₀] at h
    exact h.symm
  · dsimp only
    set T := (Tm A μ).map (tauE D τ) with hTdef
    have hT : IsUnit T.det := by
      have h := (GlobalTheory.StdUnn.Tm_gram_inv D A μ hμ).2.1.map (tauE D τ)
      rwa [RingHom.map_det] at h
    set X := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)
    set S := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k₀))
    set U := compAt θ τ (mat (κ k))
    have hX : T * U = X * T := hch k τ
    have hS : T * stdInv A.rank μ τ = S * T := by
      have h := hch (κ.symm k₀) τ
      rw [κ.apply_symm_apply, hk₀] at h
      exact h
    have hU : U * stdInv A.rank μ τ = stdInv A.rank μ τ * U := by
      rw [stdInv, Matrix.mul_smul, Matrix.smul_mul, compAt_K_comm θ hθ A.rank (κ k) hk τ]
    have key : X * S * T = S * X * T := by
      calc X * S * T = X * (T * stdInv A.rank μ τ) := by rw [hS, Matrix.mul_assoc]
        _ = T * U * stdInv A.rank μ τ := by rw [hX, Matrix.mul_assoc]
        _ = T * stdInv A.rank μ τ * U := by rw [Matrix.mul_assoc, hU, Matrix.mul_assoc]
        _ = S * X * T := by rw [hS, Matrix.mul_assoc, hX, Matrix.mul_assoc]
    have h2 := congrArg (· * T⁻¹) key
    simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT, Matrix.mul_one] using h2

end GlobalTheory.StdUnn.KComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryScalarBlendSelfAdjointIdempotent
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitTorus

theorem hform_mulVec_two {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M M' : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M' *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M') x y := by
  have e : ∀ (N : Matrix n n A) (u v : n → A), Formalism.UG.hform σ N u v = (σ ∘ u) ⬝ᵥ (N *ᵥ v) := by
    intro N u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (M *ᵥ x) = M.map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ M x i
  rw [e, e, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]

theorem hform_single {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (N : Matrix n n A) (i j : n) :
    Formalism.UG.hform σ N (Pi.single i 1) (Pi.single j 1) = N i j := by
  simp [Formalism.UG.hform, Pi.single_apply]

theorem matrix_eq_of_hform {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (N N' : Matrix n n A) (h : ∀ x y, Formalism.UG.hform σ N x y = Formalism.UG.hform σ N' x y) : N = N' := by
  ext i j
  rw [← hform_single σ N i j, ← hform_single σ N' i j, h]

theorem unit_of_proj {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J P : Matrix n n A) (c : A) (hPP : P * P = P) (hSA : Formalism.UG.cT σ P * J = J * P) (hc : c * σ c = 1) :
    (c • 1 + (1 - c) • P) * (σ c • 1 + (1 - σ c) • P) = 1 ∧
    (σ c • 1 + (1 - σ c) • P) * (c • 1 + (1 - c) • P) = 1 ∧
    Formalism.UG.cT σ (c • 1 + (1 - c) • P) * J * (c • 1 + (1 - c) • P) = J := by
  have hcT : Formalism.UG.cT σ (c • (1 : Matrix n n A) + (1 - c) • P) = σ c • 1 + (1 - σ c) • Formalism.UG.cT σ P := by
    ext i j
    by_cases h : j = i
    · subst h; simp [Formalism.UG.cT]
    · simp [Formalism.UG.cT, Matrix.one_apply, h, Ne.symm h]
  refine ⟨?_, ?_, ?_⟩
  · simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hPP, smul_smul]
    calc _ = (c * σ c) • (1 : Matrix n n A) + (1 - c * σ c) • P := by module
      _ = 1 := by rw [hc, sub_self, zero_smul, add_zero, one_smul]
  · simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hPP, smul_smul]
    calc _ = (c * σ c) • (1 : Matrix n n A) + (1 - c * σ c) • P := by module
      _ = 1 := by rw [hc, sub_self, zero_smul, add_zero, one_smul]
  · rw [hcT]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hSA,
      Matrix.mul_assoc, hPP, smul_smul]
    calc _ = (c * σ c) • J + (1 - c * σ c) • (J * P) := by module
      _ = J := by rw [hc, sub_self, zero_smul, add_zero, one_smul]

end GlobalTheory.UnitTorus

open GlobalTheory.UnitTorus in
theorem GlobalTheory.unitTorus_unit : ∀ (I : AutInst) (P : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (c : I.E ⊗[I.F] Af I.F), (∀ y, P *ᵥ (P *ᵥ y) = P *ᵥ y) → (∀ x y, hA I (P *ᵥ x) y = hA I x (P *ᵥ y)) → c * sigA I c = 1 → ∃ h : I.Gf, I.fmat h = c • 1 + (1 - c) • P ∧ I.fmat h⁻¹ = sigA I c • 1 + (1 - sigA I c) • P := by
  intro I P c hP hSA hc
  have hPP : P * P = P := by
    ext i j
    have := congrFun (hP (Pi.single j 1)) i
    rw [Matrix.mulVec_mulVec] at this
    simpa using this
  have hSA' : Formalism.UG.cT (sigA I) P * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) =
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * P := by
    have := matrix_eq_of_hform (sigA I) (Formalism.UG.cT (sigA I) P * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * 1)
      (Formalism.UG.cT (sigA I) 1 * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * P) (fun x y => by
        rw [← hform_mulVec_two, ← hform_mulVec_two, one_mulVec, one_mulVec]
        exact hSA x y)
    simpa [Formalism.UG.cT_one] using this
  obtain ⟨h1, h2, h3⟩ := unit_of_proj (sigA I) _ P c hPP hSA' hc
  exact ⟨⟨⟨_, _, h1, h2⟩, h3⟩, rfl, rfl⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModel
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatBFLoc

theorem flatBF_of_laws : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → FlatBF D := by
  intro D hFL hFLs hOm k _ _ _ _ _ _ p ν hν ψ ψk hψk ρ B J st s hs n n' _ _ _ _ c FA F₀ FV G₀ FW hco hbe hja Tm hTm
  obtain ⟨hcont, hne⟩ := (_root_.GlobalTheory.LocChar.weil_char_split D k p ψ st.weil.std).2.1 ψk hψk
  have hc : c = 2 * ρ := by have := hbe.1; omega
  let L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ) :=
    { toFun := fun Φ => flatBF st (Tm Φ)
      map_add' := fun Φ Φ' => by
        simp only [map_add (f := _)]
        exact (_root_.GlobalTheory.FlatLin.flatBF_linear D hFL ψ ρ B J st (Tm Φ) (Tm Φ') 1 (hTm.theta Φ) (hTm.theta Φ')).1
      map_smul' := fun a Φ => by
        simp only [map_smul, RingHom.id_apply]
        exact (_root_.GlobalTheory.FlatLin.flatBF_linear D hFL ψ ρ B J st (Tm Φ) (Tm Φ) a (hTm.theta Φ) (hTm.theta Φ)).2 }
  obtain ⟨L₀, hL₀⟩ := _root_.GlobalTheory.FlatFactor.flCol_factor k ψk ν hcont hne hν n n' c ρ (WO B.V₀ J.W₀ → ℂ) L hc
    (_root_.GlobalTheory.FlatColLaw.law_dual_col D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
    (_root_.GlobalTheory.FlatRow.flatBF_mul_row D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
    (_root_.GlobalTheory.FlatTransLaw.flatBF_trans D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
    (_root_.GlobalTheory.FlatUnip.flatBF_unip D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
  have hL : ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ := hL₀
  refine ⟨L₀, ⟨?_, ?_, ?_⟩, hL⟩
  · exact _root_.GlobalTheory.LocModTheta.flat_model_theta D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm L₀ hL
  · exact _root_.GlobalTheory.FlatTrans.factor_trans D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm L₀ hL
  · exact _root_.GlobalTheory.FlatBFLoc.ModelModul.model_modul D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm L₀ hL

end GlobalTheory.FlatBFLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierInversionInverseRowTransformNegOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KappaModel

theorem finv_hat_neg_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψk : AddChar k Circle) (ν : Measure k), Continuous ψk → ψk ≠ 1 → ν.IsAddHaarMeasure → ∃ C : ℂ, ∀ c : Matrix n Unit k → ℂ, c ∈ SB (Matrix n Unit k) → ∀ Φ : Matrix Unit n k → ℂ, (∀ η, Φ η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c (Matrix.of fun r _ => y r)) (η ())) → GlobalTheory.KappaModel.finv ψk ν C Φ = c := by
  intro k _ _ _ _ _ _ n _ _ ψk ν hψ hne hν
  have := secondCountable k
  have := t2Space k
  let ψ' : AddChar k Circle :=
    { toFun := fun u => ψk (-u)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by intro a b; rw [neg_add, AddChar.map_add_eq_mul] }
  have hψ'app : ∀ u, ψ' u = ψk (-u) := fun _ => rfl
  have hψ' : Continuous ψ' := hψ.comp continuous_neg
  have hne' : ψ' ≠ 1 := by
    intro h
    apply hne
    refine DFunLike.ext _ _ fun u => ?_
    have := congrArg (fun χ : AddChar k Circle => χ (-u)) h
    simpa [hψ'app] using this
  obtain ⟨C', hC'pos, hC'⟩ :=
    GlobalTheory.LocFlat.PartialFourier.partial_fourier_inversion k ψ' ν hψ' hne' hν n
  refine ⟨((C' : ℂ))⁻¹, fun c hc Φ hΦ => ?_⟩
  funext x
  let e : (n → k) ≃ₜ Matrix n Unit k :=
    { toFun := fun y => Matrix.of fun r _ => y r
      invFun := fun M r => M r ()
      left_inv := fun _ => rfl
      right_inv := fun M => by ext i j; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  set g : (n → k) → ℂ := fun y => c (Matrix.of fun r _ => y r) with hgdef
  have hg : g ∈ SB (n → k) := ⟨hc.1.comp_continuous e.continuous, hc.2.comp_homeomorph e⟩
  letI : IsEmpty Empty := ⟨fun x => nomatch x⟩
  letI : Unique (Empty → k) := ⟨⟨fun x => nomatch x⟩, fun f => funext fun x => nomatch x⟩
  let p : (n → k) × (Empty → k) ≃ₜ (n → k) := Homeomorph.prodUnique (n → k) (Empty → k)
  set f : (n → k) × (Empty → k) → ℂ := fun q => g q.1 with hfdef
  have hf : f ∈ SB ((n → k) × (Empty → k)) := ⟨hg.1.comp_continuous continuous_fst, hg.2.comp_homeomorph p⟩
  set a : n → k := fun r => x r () with hadef
  obtain ⟨-, hinv⟩ := hC' Empty a f hf
  set μJ : Measure (Empty → k) := Measure.pi fun _ => ν with hμJ
  letI : SFinite μJ := by
    rw [hμJ, Measure.pi_of_empty (x := fun e => e.elim)]
    infer_instance
  have hJ : μJ.real Set.univ = 1 := by
    rw [hμJ, Measure.pi_of_empty (x := (fun e => e.elim))]
    simp
  have h1 : ∀ l : n → k, ∫ q : (n → k) × (Empty → k), f q * (ψ' (l ⬝ᵥ q.1) : ℂ) ∂((Measure.pi fun _ => ν).prod μJ) =
      ∫ y : n → k, g y * (ψk (-1 * (l ⬝ᵥ y)) : ℂ) ∂(Measure.pi fun _ => ν) := by
    intro l
    rw [hfdef]
    simp only [hψ'app, neg_one_mul]
    rw [integral_fun_fst (f := fun y : n → k => g y * (ψk (-(l ⬝ᵥ y)) : ℂ)), hJ, one_smul]
  have h2 : ∫ y : Empty → k, f (a, y) ∂μJ = g a := by
    rw [hfdef]
    simp only
    rw [integral_const, hJ, one_smul]
  simp only [h1, h2] at hinv
  simp only [hψ'app, neg_neg] at hinv
  have h3 : g a = c x := by
    rw [hgdef]; congr 1
  have hC0 : (C' : ℂ) ≠ 0 := by exact_mod_cast hC'pos.ne'
  simp only [finv, hΦ]
  rw [← h3, show ∫ η : n → k, GlobalTheory.StepData.hat ψk ν (-1) g ((Matrix.of fun _ r => η r : Matrix Unit n k) ()) * (ψk (η ⬝ᵥ fun r => x r ()) : ℂ) ∂(Measure.pi fun _ => ν) = ∫ l : n → k, (ψk (l ⬝ᵥ a) : ℂ) * ∫ y : n → k, g y * (ψk (-1 * (l ⬝ᵥ y)) : ℂ) ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν) from by
    congr 1; funext η; rw [mul_comm]; rfl]
  rw [hinv]
  field_simp

end GlobalTheory.KappaModel
end
end

