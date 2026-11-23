module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomFramesChangeStageZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardThetaPairSecondIsSchwartzBruhatConjHalf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardThetaPairFirstFrameChangeUnitTranslate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardThetaPairSecondFrameChangeUnitTranslate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPointCountOneClassCommensurable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0999
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2815
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleRootOfUnityTwist
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.BottomFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BottomRebase

theorem isFrame_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {Λ : Submodule (𝓞 E) (Fin n → E)} (h : ∀ y, y ∈ Λ ↔ ∀ i, ∃ b : 𝓞 E, (b : E) = y i) :
    Formalism.L2.DIV.IsFrame (1 : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) Λ := by
  have e : Λ = Formalism.UG.stdLat (n := Fin n) (A := E) (𝓞 E) := by
    ext y
    rw [h, Formalism.UG.stdLat, Submodule.mem_pi]
    exact ⟨fun H i _ => H i, fun H i => H i trivial⟩
  exact e ▸ Formalism.L2.DIV.frame_standard F E n


set_option maxHeartbeats 4000000 in
theorem frame_change {D : D7} {T : Type} {A A' WW : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E))
    (Y : Tri T A A' WW) (hI : Y.Is ψ θ α β νH S) (b : GL (Fin WW.rank) (EAf D)) (fW : Formalism.L2.DIV.IsFrame b Y.rW.Λ) :
    ∃ (Z : Tri T A A' WW) (v : T → ℂ), Z.Is ψ θ α β νH S ∧ Z.rA = Y.rA ∧ Z.rA' = Y.rA' ∧ Z.rW = ⟨Y.rW.Λ, b, Y.rW.s, Y.rW.B⟩ ∧
      (∀ t, ∃ n : ℕ, 0 < n ∧ v t ^ n = 1) ∧ ∀ c : T → ℂ, Y.IsConst ψ θ c → Z.IsConst ψ θ (fun t => v t * c t) := by
  classical
  have fA := hI.rigA.2.1
  have fA' := hI.rigA'.2.1
  have hee : ∀ t, Y.e t * Y.e t = Y.e t := fun t => GlobalTheory.PlaceDatum.idemSum_mul_self (hI.idem t)
  choose k hk1 hk2 hk3 hk4 using fun t =>
    GlobalTheory.T.exists_unitaryStabilizer_transition_selfDualFrames (Y.e t) (S t) (hI.idem t) WW Y.rW.Λ hI.rigW.1 Y.rW.β b hI.rigW.2.1 fW
  choose x1 hx1 hx1' using fun t => GlobalTheory.T.standardThetaPair_first_frameChange_unitTranslate (α t / β t) (Y.e t) (S t) (hI.idem t) (Y.ideal S t) A WW
    Y.rA.Λ Y.rA.β Y.rA.β hI.rigA.2.1 fA Y.rW.β b (k t) (hk1 t) (hk3 t)
  choose x2 hx2 hx2' using fun t => GlobalTheory.T.standardThetaPair_second_frameChange_unitTranslate (α t / β t) (Y.e t) (S t) (hI.idem t) (Y.ideal S t) A.rank
    A' WW Y.rA'.Λ Y.rA'.β Y.rA'.β hI.rigA'.2.1 fA' Y.rW.β b (k t) (hk1 t) (hk3 t)
  set y : T → (AE D)ˣ := fun t => GlobalTheory.VecInv.detAt (Y.e t) (hee t) WW (k t) with hy
  have hy1 : ∀ t, IsDetAt (Y.e t) WW (k t) (y t) := fun t => GlobalTheory.VecInv.isDetAt_detAt _ _ _ _
  set c1 : T → ℂ := fun t => (((α t / β t) (x1 t) : Circle) : ℂ) * (((β t (y t) : Circle) : ℂ))⁻¹ with hc1
  set c2 : T → ℂ := fun t => (((α t / β t) (x2 t) : Circle) : ℂ) * (((α t (y t) : Circle) : ℂ))⁻¹ with hc2

  have hψ : IsStdChar D ψ (-1) := hI.isVac.1
  have hSdA := selfDual_neg hI.rigA.1
  have hinf : ∀ t, infPart D (Y.e t) = 0 := fun t => GlobalTheory.PlaceDatum.infPart_idemSum (hI.idem t)
  have hinf' : ∀ t, infPart D (cA D (Y.e t)) = 0 := fun t => GlobalTheory.PlaceDatum.infPart_cA (hinf t)
  have hee' : ∀ t, cA D (Y.e t) * cA D (Y.e t) = cA D (Y.e t) := fun t => by rw [← RingHom.map_mul, hee t]
  have hSB : ∀ t, IsSBHalf (Y.e t) (latO (GlobalTheory.Grid.neg A) WW (Y.rA.Λ : Set (Fin A.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (Y.e t) (Y.ideal S t) A WW Y.rA.β Y.rW.β) := fun t => by
    obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := GlobalTheory.Grid.neg A)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hSdA)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (hI.rigW.1)) Y.rA.β Y.rW.β
    exact StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.stdFst_isSB (hI.weil' t).hecT.1 (hI.idem t) (GlobalTheory.ConstRatio.ideal_ne_bot Y S t)
      A WW Y.rA.β Y.rW.β _ (GlobalTheory.PlaceDatum.exists_den_frMapO (S := GlobalTheory.Grid.neg A) hSdA.1.fg hI.rigW.1.1.fg Y.rA.β Y.rW.β)
      ⟨K, hK, fun t' ht => hC t' (GlobalTheory.PlaceDatum.infPart_of_half (hinf t) ht)⟩
  have hSB' : ∀ t, IsSBHalf (cA D (Y.e t)) (latO A' WW (Y.rA'.Λ : Set (Fin A'.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW Y.rA'.β Y.rW.β) := fun t =>
    GlobalTheory.T.standardThetaPair_second_isSchwartzBruhat_conjHalf _ (hI.weil' t).hecT.1 (Y.e t) (S t) (hI.idem t) _ (GlobalTheory.ConstRatio.ideal_ne_bot Y S t) A.rank A' WW
      Y.rA'.Λ Y.rW.Λ hI.rigA'.1 hI.rigW.1 Y.rA'.β Y.rW.β
  have thY : ∀ t, IsThetaFunO ψ (GlobalTheory.Grid.neg A) WW (Y.f t) := fun t => by
    obtain ⟨Tm, hTm⟩ := (hI.fst t).1
    rw [(hI.fst t).2 Tm hTm]
    exact GlobalTheory.SchrTheta.isTheta_placeModel D ψ hψ (GlobalTheory.Grid.neg A) WW Y.rA.Λ Y.rW.Λ hSdA hI.rigW.1 (Y.e t) (hee t) (hinf t)
      Y.vac hI.isVac.2.theta Tm hTm _ (hSB t)
  have thY' : ∀ t, IsThetaFunO ψ A' WW (Y.f' t) := fun t => by
    obtain ⟨Tm, hTm⟩ := (hI.snd t).1
    rw [(hI.snd t).2 Tm hTm]
    exact GlobalTheory.SchrTheta.isTheta_placeModel D ψ hψ A' WW Y.rA'.Λ Y.rW.Λ hI.rigA'.1 hI.rigW.1 (cA D (Y.e t)) (hee' t) (hinf' t)
      Y.vac' hI.isVac'.2.theta Tm hTm _ (hSB' t)
  let Z : Tri T A A' WW :=
    ⟨⟨Y.rA.Λ, Y.rA.β, Y.rA.s, Y.rA.B⟩, ⟨Y.rA'.Λ, Y.rA'.β, Y.rA'.s, Y.rA'.B⟩, ⟨Y.rW.Λ, b, Y.rW.s, Y.rW.B⟩, Y.ω, Y.ω',
      Y.vac, Y.vac', Y.e, Y.c, fun t => c1 t • (Y.ω t).toSgn true (1, k t) (Y.f t), fun t => c2 t • Y.ω' t (1, k t) (Y.f' t),
      Y.m, Y.fd, Y.m', Y.fd'⟩
  have hZI : Z.Is ψ θ α β νH S := by
    refine ⟨hI.rank, ⟨hI.rigA.1, fA, hI.rigA.2.2⟩, ⟨hI.rigA'.1, fA', hI.rigA'.2.2⟩, ⟨hI.rigW.1, fW, hI.rigW.2.2⟩, hI.weil,
      hI.weil', hI.isVac, hI.isVac', hI.idem, hI.expo, fun t => ?_, fun t => ?_, hI.meas, hI.meas'⟩
    · refine ⟨(hI.fst t).1, fun Tm hTm => ?_⟩
      have hY := (hI.fst t).2 Tm hTm
      have hLaw := ((GlobalTheory.WeilSplit.weilSplitFormula D ψ θ (GlobalTheory.Grid.neg A) WW (β t) (β t / α t) ((Y.ω t).toSgn true)
        (hI.weil t) (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.Λ Y.rW.Λ hSdA hI.rigW.1 Y.vac hI.isVac (Y.e t)
        (Or.inr ⟨_, hI.idem t⟩)).1 Tm hTm) 1 (k t) (suppAt_one' _ _) (hk1 t) (stabLat_one' _ _) (hk2 t) 1 (y t)
        (isDetAt_one' _ _) (hy1 t) _ (hSB t)
      have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (Y.e t) (Y.ideal S t) A WW Y.rA.β b =
          (((α t / β t) (x1 t) : Circle) : ℂ) • fun s => GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (Y.e t) (Y.ideal S t) A WW
            Y.rA.β Y.rW.β (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt (GlobalTheory.Grid.neg A) WW 1 (k t) s) := funext fun s => hx1' t s
      show c1 t • (Y.ω t).toSgn true (1, k t) (Y.f t) = Tm (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (Y.e t) (Y.ideal S t) A WW Y.rA.β b)
      rw [hY, hLaw, e1, map_smul, smul_smul]
      congr 1
      rw [hc1, map_one, Circle.coe_one, inv_one, one_mul, mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _), mul_one]
    · refine ⟨(hI.snd t).1, fun Tm hTm => ?_⟩
      have hY := (hI.snd t).2 Tm hTm
      have hLaw := ((GlobalTheory.WeilSplit.weilSplitFormula D ψ θ A' WW (α t) (α t / β t) (Y.ω' t)
        (hI.weil' t) Y.rA'.s Y.rW.s Y.rA'.Λ Y.rW.Λ hI.rigA'.1 hI.rigW.1 Y.vac' hI.isVac' (Y.e t)
        (Or.inr ⟨_, hI.idem t⟩)).2 Tm hTm) 1 (k t) (suppAt_one' _ _) (hk1 t) (stabLat_one' _ _) (hk2 t) 1 (y t)
        (isDetAt_one' _ _) (hy1 t) _ (hSB' t)
      have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW Y.rA'.β b =
          (((α t / β t) (x2 t) : Circle) : ℂ) • fun s => GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW
            Y.rA'.β Y.rW.β (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt A' WW 1 (k t) s) := funext fun s => hx2' t s
      show c2 t • Y.ω' t (1, k t) (Y.f' t) = Tm (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW Y.rA'.β b)
      rw [hY, hLaw, e1, map_smul, smul_smul]
      congr 1
      rw [hc2, map_one, Circle.coe_one, inv_one, one_mul, mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _), mul_one]

  have tsg : ∀ t (h' : GA D WW), (Y.ω t).toSgn true (1, h') = Y.ω t (1, h') := fun t h' => by
    show Y.ω t ((GlobalTheory.Grid.ofSgn true A) 1, h') = _
    rw [map_one]
  have kerZ : ∀ t P h' g, Z.ker ψ θ t P h' g = c1 t * Y.ker ψ θ t P (h' * k t) g := by
    intro t P h' g
    have hop := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ (GlobalTheory.Grid.neg A) WW _ _ ((Y.ω t).toSgn true) (hI.weil t) hθ
      (fun τ => -Y.rA.s τ) (fun τ => -Y.rA.s τ) Y.rA.B Y.rA.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B 1 (k t)
      (fun τ => by rw [GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [compAt_supp θ (hinf t) (hk1 t), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.one_mul])
      (fun τ => by rw [compAt_supp θ (hinf t) (hk1 t), Matrix.one_mul]) (Y.f t) (thY t) P).2
    have hm : ∀ F, Y.ω t (g, h') (Y.ω t (1, k t) F) = Y.ω t (g, h' * k t) F := fun F => by
      have e := (Y.ω t).map_mul (g, h') (1, k t)
      rw [Prod.mk_mul_mk, mul_one] at e
      rw [e]; rfl
    have e1 : pureTensorO ψ θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B
        (c1 t • (Y.ω t).toSgn true (1, k t) (Y.f t)) P = c1 t • (Y.ω t) (1, k t)
        (pureTensorO ψ θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P) := by
      rw [GlobalTheory.SeeSaw.Resc.pureTensorO_smul, LinearMap.smul_apply, ← tsg, hop]
    calc Z.ker ψ θ t P h' g = (Y.ω t (g, h') (c1 t • Y.ω t (1, k t)
          (pureTensorO ψ θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P))) 0 := by
          rw [← e1]; rfl
      _ = c1 t * (Y.ω t (g, h') (Y.ω t (1, k t)
          (pureTensorO ψ θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P))) 0 := by
          rw [LinearMap.map_smul]; rfl
      _ = c1 t * Y.ker ψ θ t P (h' * k t) g :=
          congrArg (c1 t * ·) (congrFun (hm (pureTensorO ψ θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P)) 0)
  have kerZ' : ∀ t P h' g, Z.ker' ψ θ t P h' g = c2 t * Y.ker' ψ θ t P (h' * k t) g := by
    intro t P h' g
    have hw' : IsWeilDatumO ψ A' WW (α t) (α t / β t) (Y.ω' t) := hI.weil' t
    have hop := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ A' WW (α t) (α t / β t) (Y.ω' t) hw' hθ
      Y.rA'.s Y.rA'.s Y.rA'.B Y.rA'.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B 1 (k t)
      (fun τ => by rw [GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [compAt_supp θ (hinf t) (hk1 t), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.one_mul])
      (fun τ => by rw [compAt_supp θ (hinf t) (hk1 t), Matrix.one_mul]) (Y.f' t) (thY' t) P).2
    have hm : ∀ F, Y.ω' t (g, h') (Y.ω' t (1, k t) F) = Y.ω' t (g, h' * k t) F := fun F => by
      have e : Y.ω' t ((g, h') * (1, k t)) = Y.ω' t (g, h') * Y.ω' t (1, k t) := map_mul _ _ _
      rw [Prod.mk_mul_mk, mul_one] at e
      rw [e]; rfl
    have e1 : pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B
        (c2 t • Y.ω' t (1, k t) (Y.f' t)) P = c2 t • (Y.ω' t) (1, k t)
        (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P) := by
      rw [GlobalTheory.SeeSaw.Resc.pureTensorO_smul, LinearMap.smul_apply, hop]
    calc Z.ker' ψ θ t P h' g = (Y.ω' t (g, h') (c2 t • Y.ω' t (1, k t)
          (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P))) 0 := by
          rw [← e1]; rfl
      _ = c2 t * (Y.ω' t (g, h') (Y.ω' t (1, k t)
          (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P))) 0 := by
          rw [LinearMap.map_smul]; rfl
      _ = c2 t * Y.ker' ψ θ t P (h' * k t) g :=
          congrArg (c2 t * ·) (congrFun (hm (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P)) 0)
  have IZ : ∀ t P h', Z.I ψ θ t P h' = c1 t * Y.I ψ θ t P (h' * k t) := fun t P h' => by
    show ∫ g in Y.fd, Z.ker ψ θ t P h' g ∂Y.m = _
    simp only [kerZ]
    exact MeasureTheory.integral_const_mul _ _
  have IZ' : ∀ t P h', Z.I' ψ θ t P h' = c2 t * Y.I' ψ θ t P (h' * k t) := fun t P h' => by
    show ∫ g in Y.fd', Z.ker' ψ θ t P h' g ∂Y.m' = _
    simp only [kerZ']
    exact MeasureTheory.integral_const_mul _ _
  have c1ne : ∀ t, c1 t ≠ 0 := fun t => mul_ne_zero (Circle.coe_ne_zero _) (inv_ne_zero (Circle.coe_ne_zero _))
  have c2ne : ∀ t, c2 t ≠ 0 := fun t => mul_ne_zero (Circle.coe_ne_zero _) (inv_ne_zero (Circle.coe_ne_zero _))

  refine ⟨Z, fun t => c1 t / c2 t, hZI, rfl, rfl, rfl, fun t => ?_, fun c hc => ?_⟩
  · obtain ⟨-, -, -, m, hm, H⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D (α t / β t) (hI.weil' t).hecT.1
    have H' : ∀ x, Formalism.L2.Pj.FinUnit x → (((α t / β t) x : Circle) : ℂ) ^ m = 1 := fun x hx => by
      rw [← Circle.coe_pow, H x hx, Circle.coe_one]
    refine ⟨m, hm, ?_⟩
    have e : c1 t / c2 t = (((α t / β t) (x1 t) : Circle) : ℂ) * (((α t / β t) (y t) : Circle) : ℂ) /
        (((α t / β t) (x2 t) : Circle) : ℂ) := by
      rw [MonoidHom.div_apply (α t) (β t) (y t), Circle.coe_div]
      exact (ratio_alg (Circle.coe_ne_zero _) (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)).symm
    show (c1 t / c2 t) ^ m = 1
    rw [e, div_pow, mul_pow, H' _ (hx1 t), H' _ (hx2 t), H' _ (hk4 t _ (hy1 t))]
    simp
  · obtain ⟨⟨t0, ht0⟩, P, P', H⟩ := hc
    refine ⟨⟨t0, mul_ne_zero (div_ne_zero (c1ne t0) (c2ne t0)) ht0⟩, P, P', fun t => ⟨fun h' => ⟨?_, ?_⟩, ?_, fun h' => ?_⟩⟩
    · have e : Z.ker ψ θ t P h' = fun g => c1 t * Y.ker ψ θ t P (h' * k t) g := funext (kerZ t P h')
      rw [e]
      exact ((H t).1 (h' * k t)).1.const_mul _
    · have e : Z.ker' ψ θ t P' h' = fun g => c2 t * Y.ker' ψ θ t P' (h' * k t) g := funext (kerZ' t P' h')
      rw [e]
      exact ((H t).1 (h' * k t)).2.const_mul _
    · obtain ⟨h0, hh0⟩ := (H t).2.1
      refine ⟨h0 * (k t)⁻¹, ?_⟩
      rw [IZ', inv_mul_cancel_right]
      exact mul_ne_zero (c2ne t) hh0
    · show Z.I ψ θ t P h' = c1 t / c2 t * c t * Z.I' ψ θ t P' h'
      rw [IZ, IZ', (H t).2.2]
      exact const_alg (c2ne t)

end GlobalTheory.BottomRebase

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalModificationKsIsoStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_modification_ks_iso : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g ∈ vanBd TF.X Z s, H0.restr le_top g = m) ↔ ∃ g : H0 (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str (tens (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z b).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).canChart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB hs).mul ω₀.ω ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).pullOff m) := by
  first | exact @GlobalTheory.LogCanonicalReflexive.logCanon_refl | exact GlobalTheory.LogCanonicalReflexive.logCanon_refl | (intros; apply GlobalTheory.LogCanonicalReflexive.logCanon_refl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentSumEqZeroOfOrbitalIntegralEqZero
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DefVanish

section Generic

variable {Γ H : Type} [Group Γ] [Group H]

theorem finite_coset_preimage (ι : Γ →* H) (hι : Function.Injective ι) (K : Subgroup H) (x : H) (c : H ⧸ K)
    (hstab : Finite (GlobalTheory.LKLoc.locPart ι.range K x)) :
    {w : Γ | (QuotientGroup.mk (x⁻¹ * ι w * x) : H ⧸ K) = c}.Finite := by
  by_cases hne : ∃ w₀ : Γ, (QuotientGroup.mk (x⁻¹ * ι w₀ * x) : H ⧸ K) = c
  · obtain ⟨w₀, hw₀⟩ := hne
    have hfin : ((GlobalTheory.LKLoc.locPart ι.range K x : Subgroup H) : Set H).Finite := Set.toFinite _
    have hpre : (ι ⁻¹' (GlobalTheory.LKLoc.locPart ι.range K x : Set H)).Finite := hfin.preimage hι.injOn
    refine (hpre.image (fun u => w₀ * u)).subset ?_
    intro w hw
    refine ⟨w₀⁻¹ * w, ?_, by simp⟩
    have h1 : (QuotientGroup.mk (x⁻¹ * ι w * x) : H ⧸ K) = QuotientGroup.mk (x⁻¹ * ι w₀ * x) := by
      rw [hw, hw₀]
    rw [QuotientGroup.eq] at h1
    simp only [Set.mem_preimage, SetLike.mem_coe, GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, MonoidHom.mem_range]
    refine ⟨⟨w₀⁻¹ * w, rfl⟩, ?_⟩
    rw [GlobalTheory.LKCountPoint.mem_map_conj]
    have e : x⁻¹ * ι (w₀⁻¹ * w) * x = (x⁻¹ * ι w₀ * x)⁻¹ * (x⁻¹ * ι w * x) := by
      simp only [map_mul, map_inv]; group
    rw [e]
    have h2 := K.inv_mem h1
    rwa [_root_.mul_inv_rev, inv_inv] at h2
  · push_neg at hne
    have : {w : Γ | (QuotientGroup.mk (x⁻¹ * ι w * x) : H ⧸ K) = c} = ∅ := by
      ext w; simp [hne w]
    rw [this]; exact Set.finite_empty

theorem finite_supp_cent (ι : Γ →* H) (hι : Function.Injective ι) (K : Subgroup H) (F₀ : H → ℂ) (y : Γ)
    (hbi : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, F₀ (k * g * k') = F₀ g)
    (hcls : Finite (DoubleCoset.Quotient (ι.range : Set H) (K : Set H)))
    (hstab : ∀ x, Finite (GlobalTheory.LKLoc.locPart ι.range K x))
    (hsupp : (Function.support (fun c : H ⧸ K => F₀ c.out)).Finite) :
    {q : DoubleCoset.Quotient (((Subgroup.centralizer {y}).map ι : Subgroup H) : Set H) (K : Set H) |
      F₀ ((Quotient.out q)⁻¹ * ι y * Quotient.out q) ≠ 0}.Finite := by
  set D := DoubleCoset.Quotient (ι.range : Set H) (K : Set H)

  set W : Set Γ := ⋃ d : D, ⋃ c ∈ Function.support (fun c : H ⧸ K => F₀ c.out),
    {w : Γ | (QuotientGroup.mk ((Quotient.out d)⁻¹ * ι w * Quotient.out d) : H ⧸ K) = c}
  have hW : W.Finite :=
    Set.finite_iUnion fun d => hsupp.biUnion fun c _ => finite_coset_preimage ι hι K _ c (hstab _)
  let cj : Γ → Γ := fun w => if h : ∃ γ : Γ, γ⁻¹ * y * γ = w then h.choose else 1
  let g : Γ × D → DoubleCoset.Quotient (((Subgroup.centralizer {y}).map ι : Subgroup H) : Set H) (K : Set H) :=
    fun wd => DoubleCoset.mk _ K (ι (cj wd.1) * Quotient.out wd.2)
  refine ((hW.prod (Set.finite_univ (α := D))).image g).subset ?_
  intro q hq
  simp only [Set.mem_setOf_eq] at hq
  set x := Quotient.out q
  obtain ⟨h, hh, k, hk, hd⟩ := DoubleCoset.mk_out_eq_mul ι.range K x
  obtain ⟨γ₀, rfl⟩ := hh
  set d : D := DoubleCoset.mk ι.range K x

  have hx : x = ι γ₀⁻¹ * Quotient.out d * k⁻¹ := by
    rw [hd, map_inv]; group
  set w := γ₀ * y * γ₀⁻¹
  have hconj : x⁻¹ * ι y * x = k * ((Quotient.out d)⁻¹ * ι w * Quotient.out d) * k⁻¹ := by
    rw [hx]; simp only [w, map_mul, map_inv]; group
  have hF : F₀ ((Quotient.out d)⁻¹ * ι w * Quotient.out d) ≠ 0 := by
    rw [hconj, hbi k hk _ (K.inv_mem hk)] at hq; exact hq
  have hwW : w ∈ W := by
    simp only [W, Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨d, QuotientGroup.mk ((Quotient.out d)⁻¹ * ι w * Quotient.out d), ?_, rfl⟩
    simp only [Function.mem_support]
    obtain ⟨k', hk'⟩ := QuotientGroup.mk_out_eq_mul K ((Quotient.out d)⁻¹ * ι w * Quotient.out d)
    rw [hk']
    have := hbi 1 K.one_mem k' k'.2 ((Quotient.out d)⁻¹ * ι w * Quotient.out d)
    rw [one_mul] at this
    rw [this]; exact hF
  refine ⟨(w, d), ⟨hwW, Set.mem_univ _⟩, ?_⟩
  have hex : ∃ γ : Γ, γ⁻¹ * y * γ = w := ⟨γ₀⁻¹, by simp [w]⟩
  have hcj : cj w = hex.choose := dif_pos hex
  have hcs := hex.choose_spec
  set γw := hex.choose

  have hz : γ₀⁻¹ * γw⁻¹ ∈ Subgroup.centralizer {y} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : y * γw = γw * w := by rw [← hcs]; group
    have e2 : w = γ₀ * y * γ₀⁻¹ := rfl
    calc γ₀⁻¹ * γw⁻¹ * y = γ₀⁻¹ * (γw⁻¹ * (y * γw)) * γw⁻¹ := by group
      _ = γ₀⁻¹ * w * γw⁻¹ := by rw [e]; group
      _ = y * (γ₀⁻¹ * γw⁻¹) := by rw [e2]; group
  show DoubleCoset.mk _ K (ι (cj w) * Quotient.out d) = q
  rw [← DoubleCoset.out_eq' q]
  rw [DoubleCoset.eq]
  refine ⟨ι (γ₀⁻¹ * γw⁻¹), ⟨_, hz, rfl⟩, k⁻¹, K.inv_mem hk, ?_⟩
  show x = _
  rw [hx, hcj]; simp only [map_mul, map_inv]; group

end Generic

end GlobalTheory.DefVanish

namespace GlobalTheory.DefVanish

variable {p : ℕ} [Fact p.Prime]

theorem toAfF_injective (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) : Function.Injective (GlobalTheory.LKCx.toAfF G β x t hx) := by
  haveI := GlobalTheory.LKMid.finiteAdeleRingAway_nontrivial p
  intro a b h
  have h0 := congrArg Subtype.val h
  have h1 := congrArg Prod.fst h0
  have h2 := congrArg Prod.snd h0
  simp only [GlobalTheory.LKCx.toAfF, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply,
    Prod.map_fst, Prod.map_snd, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj,
    mul_right_inj] at h1 h2
  have e1 : (a : G.Cˣ × ℚˣ).1 = (b : G.Cˣ × ℚˣ).1 := by
    apply Units.ext
    have := congrArg Units.val h1
    simp only [Units.coe_map, MonoidHom.coe_coe] at this
    exact Algebra.TensorProduct.includeRight_injective (algebraMap ℚ (AfP p)).injective this
  have e2 : (a : G.Cˣ × ℚˣ).2 = (b : G.Cˣ × ℚˣ).2 := by
    apply Units.ext
    have := congrArg Units.val h2
    simp only [Units.coe_map, MonoidHom.coe_coe] at this
    exact (algebraMap ℚ (AfP p)).injective this
  exact Subtype.ext (Prod.ext e1 e2)

theorem emb_injective (G : HTGroup p) (B : GlobalTheory.LKDef.DForm G) : Function.Injective B.emb := fun a b h =>
  toAfF_injective G B.β _ _ _ (congrArg Prod.fst h)

end GlobalTheory.DefVanish

open scoped Pointwise

namespace GlobalTheory.DefVanish
theorem conjAct_smul_eq_map' {H : Type} [Group H] (g : H) (S : Subgroup H) :
    (ConjAct.toConjAct g • S) = S.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  rfl
end GlobalTheory.DefVanish


open GlobalTheory.DefVanish in
theorem GlobalTheory.LKDef.DForm.centSum_eq_zero_of_orbK : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
    ∀ (B : GlobalTheory.LKDef.DForm G) (y : GlobalTheory.LKCx.grp G B.β),
      orbK (MonoidHom.id _) (L.K.toSubgroup.prod K') (B.emb y) (fun h => f h.1 * f' h.2) = 0 →
      centSum (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec)
        (GlobalTheory.LKCx.toP1 G B.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' y = 0 := by
  intro p _ G ha L f hf hfb K' f' hf' hf'b B y horb
  have hι : Function.Injective B.emb := emb_injective G B
  have hemb : (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec).prod
      (GlobalTheory.LKCx.toP1 G B.β) = B.emb := rfl
  set K : Subgroup (G.GAf × Gr G 1) := L.K.toSubgroup.prod K' with hKdef
  set F₀ : G.GAf × Gr G 1 → ℂ := fun h => f h.1 * f' h.2 with hF₀
  set Γ' : Subgroup (G.GAf × Gr G 1) := (Subgroup.centralizer {y}).map B.emb with hΓ'
  set T : Subgroup (G.GAf × Gr G 1) := GlobalTheory.BCT.twCent (MonoidHom.id _) (B.emb y) with hT
  have hK'c : ∀ g : Gr G 1, (K'.map (MulAut.conj g).toMonoidHom).Commensurable K' := by
    intro g
    have h1 : (K'.map (MulAut.conj g).toMonoidHom).Commensurable
        ((KHT p G.m G.n 1 G.Fw).map (MulAut.conj g).toMonoidHom) := by
      rw [← conjAct_smul_eq_map', ← conjAct_smul_eq_map']
      exact hf'.1.smul (ConjAct.toConjAct g)
    exact (h1.trans ((GlobalTheory.T.unitarySimilitudeIntegralSubgroup_commensurated_frobenius p G 1 one_pos).1 g)).trans hf'.1.symm
  have hK : ∀ x : G.GAf × Gr G 1, (K.map (MulAut.conj x).toMonoidHom).Commensurable K :=
    GlobalTheory.LKCountComm.commensurable_prod _ _ (GlobalTheory.T.compactOpenLevel_conj_commensurable p G L) hK'c
  have hbi : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, F₀ (k * g * k') = F₀ g := by
    intro k hk k' hk' g
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.1 hk
    obtain ⟨hk1', hk2'⟩ := Subgroup.mem_prod.1 hk'
    simp only [hF₀, Prod.fst_mul, Prod.snd_mul]
    rw [hfb _ hk1 _ hk1', hf'b _ hk2 _ hk2']
  have hrange : Γ' ≤ B.emb.range := by
    rintro _ ⟨c, -, rfl⟩; exact ⟨c, rfl⟩
  have hΓT : Γ' ≤ T := by
    rintro _ ⟨c, hc, rfl⟩
    show B.emb c * B.emb y = B.emb y * (MonoidHom.id _) (B.emb c)
    rw [MonoidHom.id_apply, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hc]
  have hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F₀ ((t * x * k)⁻¹ * B.emb y * (t * x * k)) = F₀ (x⁻¹ * B.emb y * x) := by
    intro t ht x k hk
    have ht' : t * B.emb y = B.emb y * t := ht
    have e : (t * x * k)⁻¹ * B.emb y * (t * x * k) = k⁻¹ * (x⁻¹ * B.emb y * x) * k := by
      have e0 : t⁻¹ * B.emb y * t = B.emb y := by rw [mul_assoc, ← ht', inv_mul_cancel_left]
      calc (t * x * k)⁻¹ * B.emb y * (t * x * k) = k⁻¹ * (x⁻¹ * (t⁻¹ * B.emb y * t) * x) * k := by group
        _ = _ := by rw [e0]
    rw [e, hbi _ (K.inv_mem hk) _ hk]
  have hstab := GlobalTheory.T.definiteForm_stabilizer_finite_away_from_p p G ha L K' hf'.1 B
  have hfin : ∀ x : G.GAf × Gr G 1, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup (G.GAf × Gr G 1)) : Set (G.GAf × Gr G 1)).Finite := by
    intro x
    haveI := hstab x
    exact (Set.toFinite ((GlobalTheory.LKLoc.locPart B.emb.range K x : Subgroup (G.GAf × Gr G 1)) : Set (G.GAf × Gr G 1))).subset
      (SetLike.coe_subset_coe.2 (inf_le_inf_right _ hrange))
  have hsupp := finite_supp_cent B.emb hι K F₀ y hbi (GlobalTheory.T.finite_doubleCoset_definiteHermitianForm_level p G ha L K' hf'.1 B) hstab
    (_root_.GlobalTheory.testProd_support_finite p G L f hf hfb K' f' hf' hf'b)
  have hcore := (GlobalTheory.LKCountComm.core_count_of_commensurable Γ' T K (fun x => F₀ (x⁻¹ * B.emb y * x)) hΓT hK
    hF hfin hsupp).1
  have horb' : (∑ᶠ q : DoubleCoset.Quotient (T : Set (G.GAf × Gr G 1)) (K : Set (G.GAf × Gr G 1)),
      ((vol (T ⊓ K) (T ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℚ) : ℂ)⁻¹ *
        F₀ ((Quotient.out q)⁻¹ * B.emb y * Quotient.out q)) = 0 := horb
  rw [horb', mul_zero] at hcore
  have hcard : ∀ x : G.GAf × Gr G 1, Nat.card (GlobalTheory.LKCount.stab (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose
      B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec) (GlobalTheory.LKCx.toP1 G B.β) L.K.toSubgroup K' x ⊓
      Subgroup.centralizer {y} : Subgroup (GlobalTheory.LKCx.grp G B.β)) =
      Nat.card (Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup (G.GAf × Gr G 1)) := by
    intro x
    rw [GlobalTheory.LKCountPoint.stab_eq]
    change Nat.card (((K.map (MulAut.conj x).toMonoidHom).comap B.emb ⊓ Subgroup.centralizer {y} :
      Subgroup (GlobalTheory.LKCx.grp G B.β))) = _
    have heq : ((K.map (MulAut.conj x).toMonoidHom).comap B.emb ⊓ Subgroup.centralizer {y}).map B.emb =
        Γ' ⊓ K.map (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.map_inf_eq _ _ _ hι, Subgroup.map_comap_eq, inf_comm B.emb.range, inf_assoc,
        inf_eq_right.2 hrange, inf_comm]
    rw [← heq]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ hι).toEquiv
  rw [← hcore]
  unfold centSum
  refine finsum_congr fun q => ?_
  rw [hcard]
  congr 1
  · simp only [term, hF₀, hemb, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, mul_one, MonoidHom.id_apply]
    rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneHodgeFiltrationPerfectFieldStatement
section
open GlobalTheory GlobalTheory.PDivGroup

theorem GlobalTheory.T.dieudonne_hodgeFiltration_perfectField :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
      (∀ x : G.RigExt, (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega) ∧
      (∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n) ∧
      (∀ m, G.rigToLie (GlobalTheory.Dieu.p_eq_zero p k) (T.red G m) = 0 ↔ ∃ n, m = T.V G n) ∧
      Function.Injective G.rigOfOmega :=
  @GlobalTheory.Dieu.Theory.hodge_filtration
end

