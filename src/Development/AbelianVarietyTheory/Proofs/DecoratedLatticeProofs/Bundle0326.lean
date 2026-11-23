module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceAlongLineDatumOverVacuumSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastSrcSlice

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem col_mem_SB {n n' : Type} {Ψ : Matrix n n' k → ℂ} {a : (n → k) → ℂ}
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) (hΨ : Ψ ≠ 0) : a ∈ SB (n → k) := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, Ψ x₀ ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hΨ (funext h0)
  have hg := Comm.comp_mem_SB h
    (p := fun y : n → k => Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y i) j)
    (s := fun x : Matrix n (n' ⊕ Fin 1) k => fun i => x i (Sum.inr 0)) ?_ (by fun_prop) (fun y => rfl)
  · have e : a = (Ψ x₀)⁻¹ • fun y : n → k =>
        tensCol Ψ a (Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y i) j) := by
      funext y
      show a y = (Ψ x₀)⁻¹ * (Ψ x₀ * a y)
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ hg
  · refine continuous_matrix fun i j => ?_
    rcases j with j | j
    · exact continuous_const
    · exact (continuous_apply i)

theorem sb_of_sbHalf (p : SplitPt D k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S T : HSp D} (α : Frame p S n') (β : Frame p T n) {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) {Φ : WO S T → ℂ} (hΦ : IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) Φ) :
    (fun x => Φ (HalfInd.wr α β x)) ∈ SB (Matrix n n' k) := by
  classical
  haveI := Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  have : CharZero k := charZero_of_injective_ringHom (f := p.pr.comp (incA D)) (RingHom.injective _)
  obtain ⟨-, k0, hk0, hinv, hsup⟩ := hΦ
  obtain ⟨hUc, hUo⟩ := HalfInd.compact_open α β hS hT
  set U := {x : Matrix n n' k | HalfInd.wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧
    IsHalf p.e (HalfInd.wr α β x)} with hU
  have hc : ((k0 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
  have hwr : ∀ z : Matrix n n' k, HalfInd.wr α β (((k0 : ℕ) : k) • z) = k0 • HalfInd.wr α β z := by
    intro z
    rw [Nat.cast_smul_eq_nsmul, map_nsmul]
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · refine ⟨{x' | ((k0 : ℕ) : k)⁻¹ • (x' - x) ∈ U}, hUo.preimage (by fun_prop), ?_, fun x' hx' => ?_⟩
    · show ((k0 : ℕ) : k)⁻¹ • (x - x) ∈ U
      rw [sub_self, smul_zero]
      refine ⟨?_, HalfInd.isHalf_wr α β 0⟩
      rw [map_zero]; exact zero_mem _
    · set z := ((k0 : ℕ) : k)⁻¹ • (x' - x) with hz
      have hx'z : x' = x + ((k0 : ℕ) : k) • z := by
        rw [hz, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]
      show Φ (HalfInd.wr α β x') = Φ (HalfInd.wr α β x)
      rw [hx'z, map_add (f := _), hwr]
      exact hinv _ hx'.1 hx'.2 _
  · refine HasCompactSupport.intro (hUc.image (f := fun z => ((k0 : ℕ) : k)⁻¹ • z) (by fun_prop)) fun x hx => ?_
    by_contra h
    have h1 := hsup _ h
    have h2 : ((k0 : ℕ) : k) • x ∈ U := by
      refine ⟨?_, HalfInd.isHalf_wr α β _⟩
      rw [hwr]; exact h1
    exact hx ⟨_, h2, by beta_reduce; rw [smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

theorem extFun_wr (p : SplitPt D k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {S T : HSp D} (α : Frame p S n') (β : Frame p T n) {Φ : WO S T → ℂ} (hΦ : ∀ t, Φ t ≠ 0 → IsHalf p.e t) :
    extFun α β (fun x => Φ (HalfInd.wr α β x)) = Φ := by
  classical
  funext t
  unfold extFun
  by_cases ht : IsHalf p.e t
  · rw [if_pos ht]
    beta_reduce
    rw [HalfInd.wr_rd α β ht]
  · rw [if_neg ht]
    by_contra h
    exact ht (hΦ t (Ne.symm h))

end GlobalTheory.LastSrcSlice

namespace GlobalTheory.LastSrcSlice

theorem main : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), a ≠ 0 → ∀ (LA : Lat A) (LS : Lat S), IsSelfDualC A LA → IsSelfDualC S LS → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ a) Ξ → ∀ y : WO L S, ∃ g, Over ψ α β LA LS g Ψ (fun u => Ξ ((o.resS S).symm (u, y))) := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ _ V₀ A L S o ζ _ α α₀ β hsum Ψ a ha LA LS hLA hLS L₁ L₂ f₁ Ξ hΞ y
  obtain ⟨hL₁, hL₂, hf₁, hSB, ⟨T, hT⟩, hall⟩ := hΞ
  have hΞT : Ξ = T (extFun α₀ β (tensCol Ψ a)) := hall T hT
  by_cases hΨ0 : Ψ = 0
  ·
    subst hΨ0
    have hext : extFun α₀ β (tensCol (0 : Matrix n n' k → ℂ) a) = 0 := by
      classical
      funext t
      simp [extFun, tensCol]
    have hslice : (fun u => Ξ ((o.resS S).symm (u, y))) = 0 := by
      rw [hΞT, hext, map_zero]; rfl
    have hheis0 : ∀ (w : WO A S), heisO ψ A S w (0 : WO A S → ℂ) = 0 := by
      intro w; funext x; simp [heisO]
    refine ⟨0, hLA, hLS, ⟨?_, ?_⟩, Submodule.zero_mem _, ⟨0, ?_⟩, fun T' hT' => ?_⟩
    · exact { quasi := fun γ w => by simp
              level := ⟨⊤, isOpen_univ, fun u _ _ => hheis0 u⟩
              cont := continuous_const
              smooth := fun _ _ _ _ _ => by simpa using contDiff_const }
    · exact ⟨fun u _ => hheis0 _, fun _ _ u _ _ => hheis0 u⟩
    · exact ⟨fun Φ _ x _ => by simp [hheis0], fun Φ _ y' _ => by simp [hheis0], by simp⟩
    · rw [hslice]
      have : extFun α β (0 : Matrix n n' k → ℂ) = 0 := by
        classical
        funext t; simp [extFun]
      beta_reduce
      rw [this, map_zero]
  · have haSB : a ∈ SB (n → k) := col_mem_SB hSB hΨ0
    have hΨSB : Ψ ∈ SB (Matrix n n' k) := TensSB.of_tensCol_mem hSB ha
    set r := o.resS S with hr
    set a' := ExtZero.colFun β ζ a with ha'
    set ΛA := latO A S (LA : Set (Fin A.rank → D.host.E)) (LS : Set (Fin S.rank → D.host.E)) (· = p.v) with hΛA
    set Λ₁ := latO V₀ S (L₁ : Set (Fin V₀.rank → D.host.E)) (L₂ : Set (Fin S.rank → D.host.E)) (· = p.v) with hΛ₁
    set T₁ := ExtZero.restrModel r a' T y with hT₁
    set g := T₁ (halfInd p.e ΛA) with hg
    have hbox : ∀ Φ : WO A S → ℂ, (fun t => Φ (r t).1 * a' (r t).2) = o.boxS S Φ a' := fun Φ => rfl

    have hsb : ∀ Φ, IsSBHalf p.e ΛA Φ → IsSBHalf p.e Λ₁ (fun t => Φ (r t).1 * a' (r t).2) := by
      intro Φ hΦ
      have h1 := sb_of_sbHalf p α β hLA hLS hΦ
      have h2 := extFun_wr p α β (Φ := Φ) hΦ.1
      rw [hbox, ← h2, ← _root_.GlobalTheory.FinPl.ExtZero.extFun_tensCol_sum D k p n n' V₀ A L S o ζ α α₀ β hsum]
      exact OverProof.isSBHalf_extFun D k p _ _ V₀ S α₀ β L₁ L₂ hL₁ hL₂ _ (Comm.tensCol_mem h1 haSB)

    have hmodel : IsPlaceModel ψ (symplO A S) (heisO ψ A S) p.e ΛA 1 g T₁ := by
      refine ⟨?_, ?_, ?_⟩
      · intro Φ hΦ x hx
        funext w
        rw [ExtZero.restrModel_apply]
        have hfun : (fun t => (fun t => Φ (t + x)) (r t).1 * a' (r t).2) =
            fun t => (fun t => Φ (r t).1 * a' (r t).2) (t + r.symm (x, 0)) := by
          funext t
          simp only [map_add (f := _), AddEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, add_zero]
        rw [hfun, hT.trans _ (hsb Φ hΦ) _ (ExtZero.half_resS_symm o hx), hr, ExtZero.heisO_resS_symm]
        rfl
      · intro Φ hΦ y' hy'
        funext w
        rw [ExtZero.restrModel_apply]
        have hfun : (fun t => (fun t => ψ (symplO A S t y') * Φ t) (r t).1 * a' (r t).2) =
            fun t => ψ (symplO V₀ S t (r.symm (y', 0))) * (fun t => Φ (r t).1 * a' (r t).2) t := by
          funext t
          rw [hr, ExtZero.symplO_resS_symm, mul_assoc]
        rw [hfun, hT.modul _ (hsb Φ hΦ) _ (ExtZero.half_resS_symm o hy'), hr, ExtZero.heisO_resS_symm]
        rfl
      · rw [one_smul]

    have hlat : IsLatVac (heisO ψ A S) ΛA g :=
      Rebase.latVac_image D k p ψ hψ A S LA LA LS LS hLA hLS hLA hLS g T₁ hmodel

    have htheta : IsThetaFunO ψ A S g := by
      obtain ⟨ΨA, hΨA, hΨAe⟩ := HalfInd.exists_SB_extFun_eq_halfInd D k p A S n n' α β LA LS hLA hLS
      have hover := (_root_.GlobalTheory.FinPl.overBasic D k p n (n' ⊕ Fin 1) ψ hψ V₀ S α₀ β L₁ L₂ hL₁ hL₂ f₁ hf₁).1
      obtain ⟨F, hF, -⟩ := hover _ (Comm.tensCol_mem hΨA haSB)
      have hFth := ((_root_.GlobalTheory.FinPl.overBasic D k p n (n' ⊕ Fin 1) ψ hψ V₀ S α₀ β L₁ L₂ hL₁ hL₂ f₁ hf₁).2.1 _ _ hF).1
      have hFT : F = T (extFun α₀ β (tensCol ΨA a)) := hF.2.2.2.2.2 T hT
      rw [_root_.GlobalTheory.FinPl.ExtZero.extFun_tensCol_sum D k p n n' V₀ A L S o ζ α α₀ β hsum, hΨAe] at hFT
      have := GlobalTheory.BoxSlice.isThetaFunO_slice_left o hFth y
      rw [hFT] at this
      exact this
    have hvac : Vac ψ A S LA LS (· = p.v) g := ⟨htheta, hlat⟩

    have hslice : (fun u => Ξ ((o.resS S).symm (u, y))) = T₁ (extFun α β Ψ) := by
      funext u
      rw [ExtZero.restrModel_apply, hΞT, _root_.GlobalTheory.FinPl.ExtZero.extFun_tensCol_sum D k p n n' V₀ A L S o ζ α α₀ β hsum]
      rfl
    refine ⟨g, ?_⟩
    obtain ⟨f, hf, -⟩ := (_root_.GlobalTheory.FinPl.overBasic D k p n n' ψ hψ A S α β LA LS hLA hLS g hvac).1 Ψ hΨSB
    have hfT₁ : f = T₁ (extFun α β Ψ) := hf.2.2.2.2.2 T₁ hmodel
    rw [hslice, ← hfT₁]
    exact hf

end GlobalTheory.LastSrcSlice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocMod.LinSpace

variable {D : D7}

theorem heisO_add' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g := by
  funext w; simp [heisO, mul_add]

theorem heisO_smul' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
  funext w; simp [heisO]; ring

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) :
    heisO ψ S T u 0 = 0 := by
  funext w; simp [heisO]

theorem isThetaFunO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T 0 := {
  quasi := by intro γ w; simp
  level := ⟨⊤, isOpen_univ, fun u _ _ => heisO_zero' ψ S T u⟩
  cont := continuous_const
  smooth := by intro k L _ _ w; exact contDiff_const }

theorem isThetaFunO_add {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (f + g) := {
  quasi := by intro γ w; simp [hf.quasi, hg.quasi, mul_add]
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨V, hV, hVg⟩ := hg.level
    refine ⟨U ⊓ V, ?_, ?_⟩
    · rw [AddSubgroup.coe_inf]; exact hU.inter hV
    · intro u hu h0
      rw [heisO_add', hUf u hu.1 h0, hVg u hu.2 h0]
  cont := hf.cont.add hg.cont
  smooth := by
    intro k L hL hL' w
    exact (hf.smooth k L hL hL' w).add (hg.smooth k L hL hL' w) }

theorem isThetaFunO_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (c : ℂ)
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := {
  quasi := by intro γ w; simp [hf.quasi]; ring
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisO_smul', hUf u hu h0]⟩
  cont := continuous_const.mul hf.cont
  smooth := by
    intro k L hL hL' w
    exact contDiff_const.mul (hf.smooth k L hL hL' w) }

end GlobalTheory.LocMod.LinSpace


open GlobalTheory.LocMod.LinSpace in
theorem GlobalTheory.LocMod.Place.isModel_linear : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), p.IsModel ψ FS FT 0 ∧ ∀ T₁ T₂, p.IsModel ψ FS FT T₁ → p.IsModel ψ FS FT T₂ → p.IsModel ψ FS FT (T₁ + T₂) ∧ ∀ c : ℂ, p.IsModel ψ FS FT (c • T₁) := by
  intro D k _ _ _ _ p ψ Y Y' _ _ _ _ S T FS FT
  refine ⟨⟨fun Φ => isThetaFunO_zero ψ S T, ?_, ?_⟩, ?_⟩
  · intro x Φ Φ' _; simp [heisO_zero']
  · intro y _ Φ Φ' _; simp [heisO_zero']
  · intro T₁ T₂ h₁ h₂
    refine ⟨⟨fun Φ => isThetaFunO_add (h₁.theta Φ) (h₂.theta Φ), ?_, ?_⟩, fun c => ⟨fun Φ => isThetaFunO_smul c (h₁.theta Φ), ?_, ?_⟩⟩
    · intro x Φ Φ' h
      simp only [LinearMap.add_apply]
      rw [h₁.trans x Φ Φ' h, h₂.trans x Φ Φ' h, heisO_add']
    · intro y hy Φ Φ' h
      simp only [LinearMap.add_apply]
      rw [h₁.modul y hy Φ Φ' h, h₂.modul y hy Φ Φ' h, heisO_add']
    · intro x Φ Φ' h
      simp only [LinearMap.smul_apply]
      rw [h₁.trans x Φ Φ' h, heisO_smul']
    · intro y hy Φ Φ' h
      simp only [LinearMap.smul_apply]
      rw [h₁.modul y hy Φ Φ' h, heisO_smul']
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHeisenbergActionLineModulationTranslat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Generic

variable {p : SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n'] {α : Frame p S n'} {β : Frame p T n} {LS : Lat S} {LT : Lat T} {f₀ f : WO S T → ℂ}
  {Ψ Ψ' : Matrix n n' k → ℂ}

theorem over_trans (h : Over ψ α β LS LT f₀ Ψ f) {x : WO S T} (hx : IsHalf p.e x) (hΨ' : Ψ' ∈ SB (Matrix n n' k))
    (he : ∀ t, IsHalf p.e t → Ψ' (rd α β t) = Ψ (rd α β (t + x))) : Over ψ α β LS LT f₀ Ψ' (heisO ψ S T x f) := by
  obtain ⟨hS, hT, hV, hΨ, hex, hall⟩ := h
  have hsb := GlobalTheory.FinPl.OverProof.isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ
  have hfun : extFun α β Ψ' = fun t => extFun α β Ψ (t + x) := by
    funext t
    have hc : IsHalf p.e (t + x) ↔ IsHalf p.e t := forall_congr' fun i => forall_congr' fun j => by
      rw [Matrix.add_apply, mul_add, hx i j, add_left_inj]
    unfold extFun
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht, if_pos (hc.2 ht), he t ht]
    · rw [if_neg ht, if_neg (fun h' => ht (hc.1 h'))]
  refine ⟨hS, hT, hV, hΨ', hex, fun Tm hTm => ?_⟩
  show heisO ψ S T x f = Tm (extFun α β Ψ')
  rw [hall Tm hTm, hfun, hTm.trans _ hsb x hx]

theorem over_modul (h : Over ψ α β LS LT f₀ Ψ f) {y : WO S T} (hy : IsHalf (cA D p.e) y)
    (hΨ' : Ψ' ∈ SB (Matrix n n' k))
    (he : ∀ t, IsHalf p.e t → Ψ' (rd α β t) = ψ (symplO S T t y) * Ψ (rd α β t)) :
    Over ψ α β LS LT f₀ Ψ' (heisO ψ S T y f) := by
  obtain ⟨hS, hT, hV, hΨ, hex, hall⟩ := h
  have hsb := GlobalTheory.FinPl.OverProof.isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ
  have hfun : extFun α β Ψ' = fun t => ψ (symplO S T t y) * extFun α β Ψ t := by
    funext t
    unfold extFun
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht, if_pos ht, he t ht]
    · rw [if_neg ht, if_neg ht, mul_zero]
  refine ⟨hS, hT, hV, hΨ', hex, fun Tm hTm => ?_⟩
  show heisO ψ S T y f = Tm (extFun α β Ψ')
  rw [hall Tm hTm, hfun, hTm.modul _ hsb y hy]

end Generic

section SBLemmas

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem tensCol_mul_mem {Ψ : Matrix n n' k → ℂ} {a g : (n → k) → ℂ} (hg : IsLocallyConstant g)
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) :
    tensCol Ψ (fun y => g y * a y) ∈ SB (Matrix n (n' ⊕ Fin 1) k) := by
  have e : tensCol Ψ (fun y => g y * a y) =
      (fun x : Matrix n (n' ⊕ Fin 1) k => g fun i => x i (Sum.inr 0)) * tensCol Ψ a := by
    funext x; simp only [tensCol, Pi.mul_apply]; ring
  rw [e]
  exact ⟨(hg.comp_continuous (by fun_prop)).mul h.1, h.2.mul_left⟩

theorem tensRow_mul_mem {Ψ : Matrix n' n k → ℂ} {b g : (n → k) → ℂ} (hg : IsLocallyConstant g)
    (h : tensRow Ψ b ∈ SB (Matrix (n' ⊕ Fin 1) n k)) :
    tensRow Ψ (fun y => g y * b y) ∈ SB (Matrix (n' ⊕ Fin 1) n k) := by
  have e : tensRow Ψ (fun y => g y * b y) =
      (fun x : Matrix (n' ⊕ Fin 1) n k => g (x (Sum.inr 0))) * tensRow Ψ b := by
    funext x; simp only [tensRow, Pi.mul_apply]; ring
  rw [e]
  exact ⟨(hg.comp_continuous (by fun_prop)).mul h.1, h.2.mul_left⟩

theorem tensCol_sub_mem {Ψ : Matrix n n' k → ℂ} {a : (n → k) → ℂ} (t : n → k)
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) :
    tensCol Ψ (fun y => a (y - t)) ∈ SB (Matrix n (n' ⊕ Fin 1) k) := by
  let M : Matrix n (n' ⊕ Fin 1) k := Matrix.of fun i j => Sum.elim (fun _ => 0) (fun _ => t i) j
  have e : tensCol Ψ (fun y => a (y - t)) = tensCol Ψ a ∘ Homeomorph.subRight M := by
    funext x
    simp only [tensCol, Function.comp_apply, Homeomorph.subRight_apply]
    congr 2
    all_goals first | (ext i j; simp [M]) | (funext i; simp [M])
  rw [e]
  exact ⟨h.1.comp_continuous (Homeomorph.subRight M).continuous, h.2.comp_homeomorph _⟩

theorem tensRow_sub_mem {Ψ : Matrix n' n k → ℂ} {b : (n → k) → ℂ} (t : n → k)
    (h : tensRow Ψ b ∈ SB (Matrix (n' ⊕ Fin 1) n k)) :
    tensRow Ψ (fun y => b (y - t)) ∈ SB (Matrix (n' ⊕ Fin 1) n k) := by
  let M : Matrix (n' ⊕ Fin 1) n k := Matrix.of fun i j => Sum.elim (fun _ => 0) (fun _ => t j) i
  have e : tensRow Ψ (fun y => b (y - t)) = tensRow Ψ b ∘ Homeomorph.subRight M := by
    funext x
    simp only [tensRow, Function.comp_apply, Homeomorph.subRight_apply]
    congr 2
    all_goals first | (ext i j; simp [M]) | (funext i; simp [M])
  rw [e]
  exact ⟨h.1.comp_continuous (Homeomorph.subRight M).continuous, h.2.comp_homeomorph _⟩

end SBLemmas

end GlobalTheory.FinPl.LineAct

end

noncomputable section
namespace GlobalTheory.FinPl.LineAct

theorem line_act : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ →
    ∃ ε : k, (ε = 1 ∨ ε = -1) ∧ ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (σ : ℕ) (B : BesLev D (σ + 1)) (B' : BesLev D σ) (W₀ : HSp D) (l : Link B B'.L B'.ζ) (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n) (γ : Frame p B'.A n'') (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ → IsStdChar D ψ (-1) → ∀ t : n → k,
      (∃ w₀ : WO W₀ B'.L,
        (∀ (L₁ : Lat B.V₀) (L₂ : Lat W₀) (f₁ : WO B.V₀ W₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (Ξ : WO B.V₀ W₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ fun y => (χ (ε * (t ⬝ᵥ y)) : ℂ) * a y) (heisO ψ B.V₀ W₀ ((B.o.resS W₀).symm (0, l.κ W₀ w₀)) Ξ)) ∧
        (∀ (L₂' : Lat W₀) (L₃ : Lat B'.V₀) (f₂ : WO W₀ B'.V₀ → ℂ) (Ψ₂ : Matrix n'' n k → ℂ) (b : (n → k) → ℂ) (Ξ : WO W₀ B'.V₀ → ℂ),
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ fun η => b (η - t)) (heisO ψ W₀ B'.V₀ ((B'.o.resT W₀).symm (0, -w₀)) Ξ))) ∧
      (∃ w₀ : WO W₀ B'.L,
        (∀ (L₁ : Lat B.V₀) (L₂ : Lat W₀) (f₁ : WO B.V₀ W₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (Ξ : WO B.V₀ W₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ fun y => a (y - t)) (heisO ψ B.V₀ W₀ ((B.o.resS W₀).symm (0, l.κ W₀ w₀)) Ξ)) ∧
        (∀ (L₂' : Lat W₀) (L₃ : Lat B'.V₀) (f₂ : WO W₀ B'.V₀ → ℂ) (Ψ₂ : Matrix n'' n k → ℂ) (b : (n → k) → ℂ) (Ξ : WO W₀ B'.V₀ → ℂ),
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ fun η => (χ (ε * (η ⬝ᵥ t)) : ℂ) * b η) (heisO ψ W₀ B'.V₀ ((B'.o.resT W₀).symm (0, -w₀)) Ξ))) := by
  intro D k _ _ _ _ p ψ χ hχ
  refine ⟨-1, Or.inr rfl, ?_⟩
  intro n n' n'' _ _ _ _ _ _ σ B B' W₀ l α α₀ β γ γ₀ hα hγ hstd t
  have hχc := (_root_.GlobalTheory.FinPl.SplitChar.cont_ne_one D k p ψ χ hχ hstd).1
  have hχl := GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar χ hχc
  have hlc : IsLocallyConstant fun y : n → k => (χ (-1 * (t ⬝ᵥ y)) : ℂ) :=
    hχl.comp_continuous (continuous_const.mul (continuous_const.dotProduct continuous_id))
  have hlc' : IsLocallyConstant fun η : n → k => (χ (-1 * (η ⬝ᵥ t)) : ℂ) :=
    hχl.comp_continuous (continuous_const.mul (continuous_id.dotProduct continuous_const))
  constructor
  · obtain ⟨h1h, h1m⟩ := _root_.GlobalTheory.KappaRowChar.kappa_wRow_char D k p ψ χ hχ n n' (σ + 1) B B'.L W₀ B'.ζ l α α₀ β hα t
    obtain ⟨h1ah, h1ar⟩ := _root_.GlobalTheory.FinPl.LineAct.neg_wRow_half_rd D k p n n'' B'.V₀ B'.A B'.L W₀ B'.o B'.ζ β γ γ₀ hγ t
    refine ⟨wRow p B'.ζ β t, fun L₁ L₂ f₁ Ψ₁ a Ξ h => ?_, fun L₂' L₃ f₂ Ψ₂ b Ξ h => ?_⟩
    · refine over_modul h h1h (tensCol_mul_mem hlc h.2.2.2.1) fun x hx => ?_
      rw [h1m x hx]
      simp only [tensCol, neg_one_mul]
      ring
    · refine over_trans h h1ah (tensRow_sub_mem t h.2.2.2.1) fun x hx => ?_
      simp only [tensRow, GlobalTheory.FinPl.OverProof.rd_add]
      congr 1
      · congr 1; ext i j; simp [Matrix.add_apply, h1ar]
      · congr 1; funext j; simp [Matrix.add_apply, h1ar, sub_eq_add_neg]
  · obtain ⟨h2h, h2r⟩ := _root_.GlobalTheory.FinPl.LineAct.kappa_wCol_translate D k p n n' (σ + 1) B B'.L W₀ B'.ζ l B'.line α α₀ β hα t
    obtain ⟨h2bh, h2bm⟩ := GlobalTheory.T.conjugateHalfPoint_neg_multiplies_by_character D k p ψ χ hχ n n'' B'.V₀ B'.A B'.L W₀ B'.o B'.ζ B'.line β γ γ₀ hγ t
    refine ⟨wCol p B'.ζ β t, fun L₁ L₂ f₁ Ψ₁ a Ξ h => ?_, fun L₂' L₃ f₂ Ψ₂ b Ξ h => ?_⟩
    · refine over_trans h h2h (tensCol_sub_mem t h.2.2.2.1) fun x hx => ?_
      simp only [tensCol, GlobalTheory.FinPl.OverProof.rd_add]
      congr 1
      · congr 1; ext i j; simp [Matrix.add_apply, h2r]
      · congr 1; funext i; simp [Matrix.add_apply, h2r, sub_eq_add_neg]
    · refine over_modul h h2bh (tensRow_mul_mem hlc' h.2.2.2.1) fun x hx => ?_
      rw [h2bm x hx]
      simp only [tensRow, neg_one_mul]
      ring
end GlobalTheory.FinPl.LineAct
end
end

