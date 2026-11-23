module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0406
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0421
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0428
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCoinvariantLeviAction
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Coinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cls {i : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (x : τ.V) : (phiN ψ τ).V :=
  (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ x

theorem phiN_cls {i : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (a : Mir k i) (x : τ.V) :
    (phiN ψ τ).ρ a (cls ψ τ x) = ((dpowM i (-1 / 2) a : ℂˣ) : ℂ) • cls ψ τ (τ.ρ (sEmb k i a) x) :=
  twist_apply _ _ _ _

theorem dpowM_half (i : ℕ) (a : Mir k i) :
    ((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpowM i (-1 / 2) a : ℂˣ) : ℂ) = 1 := by
  have h : dpow (k := k) (i + 1) (1 / 2 + -1 / 2) = dpow (i + 1) (1 / 2) * dpow (i + 1) (-1 / 2) :=
    GlobalTheory.CompanionTheory.LeibPhi.dpow_add k (i + 1) _ _
  have h0 : dpow (k := k) (i + 1) (1 / 2 + -1 / 2) = 1 := by
    rw [show ((1 / 2 + -1 / 2 : ℝ)) = 0 by norm_num]
    ext g
    simp [dpow, detChar, absPow]
  have h1 := congrArg (fun f => ((f (a : GL (Fin (i + 1)) k) : ℂˣ) : ℂ)) (h.symm.trans h0)
  simpa [dpowM] using h1

theorem dpow_step (i t : ℕ) (w : GL (Fin (t + 1)) k) :
    ((dpow (t + 1) (-((i + 1 + 1 : ℕ) : ℝ) / 2) w : ℂˣ) : ℂ) =
      ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ) * ((dpow (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) w : ℂˣ) : ℂ) := by
  have e : (-((i + 1 + 1 : ℕ) : ℝ) / 2) = -1 / 2 + (-((i + 1 : ℕ) : ℝ) / 2) := by
    push_cast; ring
  rw [e, GlobalTheory.CompanionTheory.LeibPhi.dpow_add]
  simp

theorem smul_tmul_scal {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (p : X) (q : Y)
    (c d e f f' g : ℂ) (h : c * d = e * (f * f' * g)) :
    (c • p) ⊗ₜ[ℂ] (d • q) = e • ((f • f' • p) ⊗ₜ[ℂ] (g • q)) := by
  rw [smul_smul f f' p]
  generalize f * f' = f at h
  rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul',
    smul_smul, smul_smul, smul_smul, mul_comm d c, h, mul_comm f g, mul_assoc]

theorem intertwine (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (a : Mir k i) (w : GL (Fin (t + 1)) k) (v : τ.V ⊗[ℂ] σ.V) :
  qO τ σ ψ (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a, w) v) =
    (((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ)) •
      extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ (a, w) (qO τ σ ψ v) := by
  let L : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (phiN ψ τ).V ⊗[ℂ] σ.V := (qO τ σ ψ) ∘ₗ
    (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a, w))
  let R : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (phiN ψ τ).V ⊗[ℂ] σ.V :=
    (((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ)) •
      ((extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ (a, w)) ∘ₗ (qO τ σ ψ))
  have hLR : L = R := by
    refine TensorProduct.ext' fun x y => ?_
    have hl : (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a) x =
        ((dpowM i (((t + 1 : ℕ) : ℝ) / 2) a : ℂˣ) : ℂ) • τ.ρ (sEmb k i a) x :=
      (twist_apply _ _ _ _).trans (by
        rw [show sEmb k i a = (levi k (i + 1)).comp (Mir k i).subtype a from rfl, GlobalTheory.CompanionTheory.LeibPhiTw.dpowM_levi]
        rfl)
    have hr : ∀ s : ℝ, (σ.tw s).ρ w y = ((dpow (t + 1) s w : ℂˣ) : ℂ) • σ.ρ w y := fun s => twist_apply _ _ _ _
    have hm : (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ a (cls ψ τ x) =
        ((dpowM i (((t + 1 : ℕ) : ℝ) / 2) a : ℂˣ) : ℂ) • (phiN ψ τ).ρ a (cls ψ τ x) := twist_apply _ _ _ _
    have hc : ∀ (c : ℂ) (z : τ.V), cls ψ τ (c • z) = c • cls ψ τ z := fun c z => map_smul _ c z
    have eL : L (x ⊗ₜ[ℂ] y) = cls ψ τ ((mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a) x) ⊗ₜ[ℂ]
        (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ w y := rfl
    have eR : R (x ⊗ₜ[ℂ] y) = (((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ)) •
        ((mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ a (cls ψ τ x) ⊗ₜ[ℂ] (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ w y) := rfl
    rw [eL, eR, hl, hm, phiN_cls, hr, hr, hc, dpow_step]
    have hh := dpowM_half i a
    refine smul_tmul_scal (X := (phiN ψ τ).V) (Y := σ.V) _ _ _ _ _ _ _ _ ?_
    linear_combination (-(((dpowM i (((t + 1 : ℕ) : ℝ) / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ) * ((dpow (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) w : ℂˣ) : ℂ))) * hh
  exact LinearMap.congr_fun hLR v

end GlobalTheory.CompanionTheory.BZPhiPG.Coinv

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedInvariantPairingCharacter
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.Descend

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_uM (ψ : AddChar k Circle) (n : ℕ) (u : MirUin k (n + 1)) :
    ∃ y : Fin (n + 1) → k, (u : Mir k (n + 1)) = uM (n + 1) y ∧
      ((mirChar k ψ n u : ℂˣ) : ℂ) = ((ψ (y (Fin.last n)) : Circle) : ℂ) := by
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp u.2)
  refine ⟨Multiplicative.toAdd w, Subtype.ext hw.symm, ?_⟩
  rw [GlobalTheory.BZMir.mirChar_eq k ψ n u w hw.symm, Circle.toUnits_apply, Units.val_mk0]

theorem left_kill (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (f : V →ₗ[ℂ] ℂ)
    (h : ∀ (y : Fin (n + 1) → k) v, f (T (uM (n + 1) y) v) = ((ψ (y (Fin.last n)) : Circle) : ℂ) * f v) :
    twKer T (MirUin k (n + 1)) (mirChar k ψ n) ≤ LinearMap.ker f := by
  rw [GlobalTheory.PRep.twKer, Submodule.span_le]
  rintro w ⟨u, v, rfl⟩
  obtain ⟨y, hu, hχ⟩ := GlobalTheory.CompanionTheory.MirPair.Descend.exists_uM ψ n u
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, hu, h, hχ, sub_self]

theorem phiMinus_mk (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (p : Mir k n) (v : V) :
    phiMinus k ψ T p (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) := rfl

theorem descend : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B₀ : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), (∀ (y : Fin (n + 1) → k) v v', B₀ (T (uM (n + 1) y) v) v' = ((ψ (y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (y : Fin (n + 1) → k) v v', B₀ v (T' (uM (n + 1) y) v') = ((ψ (-y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (p : Mir k n) v v', B₀ (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B₀ v v') → (∀ v, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ v', B₀ v v' ≠ 0) → ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ] TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ, (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧ (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  intro k _ _ _ _ ψ n s V V' _ _ _ _ T T' B₀ hT hT' hL hnd
  have hleft : ∀ v' : V', GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) ≤ LinearMap.ker (B₀.flip v') := fun v' =>
    GlobalTheory.CompanionTheory.MirPair.Descend.left_kill ψ T (B₀.flip v') fun y v => by
      rw [LinearMap.flip_apply, LinearMap.flip_apply]
      exact hT y v v'
  have hright : ∀ v : V, GlobalTheory.PRep.twKer T' (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) ≤ LinearMap.ker (B₀ v) := fun v =>
    GlobalTheory.CompanionTheory.MirPair.Descend.left_kill ψ⁻¹ T' (B₀ v) fun y v' => by
      rw [AddChar.inv_apply]
      exact hT' y v v'
  have h₁ : GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) ≤ LinearMap.ker B₀ := by
    intro v hv
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun v' => ?_
    have h := LinearMap.mem_ker.mp (hleft v' hv)
    rw [LinearMap.flip_apply] at h
    rw [h, LinearMap.zero_apply]
  let B₁ : GlobalTheory.PRep.TwJacquet T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) →ₗ[ℂ] V' →ₗ[ℂ] ℂ :=
    Submodule.liftQ _ B₀ h₁
  have h₂ : GlobalTheory.PRep.twKer T' (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) ≤ LinearMap.ker B₁.flip := by
    intro v' hv'
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact LinearMap.mem_ker.mp (hright v hv')
  let B' : GlobalTheory.PRep.TwJacquet T (GlobalTheory.BZMir.MirUin k (n + 1))
      (GlobalTheory.BZMir.mirChar k ψ n) →ₗ[ℂ] GlobalTheory.PRep.TwJacquet T'
      (GlobalTheory.BZMir.MirUin k (n + 1)) (GlobalTheory.BZMir.mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ :=
    (Submodule.liftQ _ B₁.flip h₂).flip
  have hB' : ∀ (v : V) (v' : V'), B' (Submodule.Quotient.mk v) (Submodule.Quotient.mk v') = B₀ v v' :=
    fun _ _ => rfl
  refine ⟨B', ?_, ?_⟩
  · intro p w w'
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨v', rfl⟩ := Submodule.Quotient.mk_surjective _ w'
    rw [GlobalTheory.CompanionTheory.MirPair.Descend.phiMinus_mk, GlobalTheory.CompanionTheory.MirPair.Descend.phiMinus_mk, hB', hB', hL]
  · intro w hw
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hv : v ∉ GlobalTheory.PRep.twKer T (GlobalTheory.BZMir.MirUin k (n + 1))
        (GlobalTheory.BZMir.mirChar k ψ n) := fun h =>
      hw ((Submodule.Quotient.mk_eq_zero _).mpr h)
    obtain ⟨v', hv'⟩ := hnd v hv
    exact ⟨Submodule.Quotient.mk v', by rw [hB']; exact hv'⟩

end GlobalTheory.CompanionTheory.MirPair.Descend

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UMLeviMulUMLevi
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

open ValuativeRel Topology GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

variable {k : Type} [Field k]

theorem uM_levi_mul_uM_levi (n : ℕ) (y y' : Fin n → k) (b b' : GL (Fin n) k) :
    uM k n y * levi k n b * (uM k n y' * levi k n b') =
      uM k n (y + (b : Matrix (Fin n) (Fin n) k).mulVec y') * levi k n (b * b') := by
  rw [mul_assoc, ← mul_assoc (GlobalTheory.BZMir.levi k n b), GlobalTheory.CompanionTheory.BZPsiPG.levi_mul_uM,
    GlobalTheory.CompanionTheory.BZPsiPG.uM_add, map_mul]
  simp only [mul_assoc]

theorem mirProj_levi_eq (n : ℕ) (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_levi n g

theorem mirProj_uM (n : ℕ) (y : Fin n → k) : mirabolicProjection k n (uM k n y) = 1 :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_uv n y

theorem uM_injective (n : ℕ) : Function.Injective (uM k n) := by
  intro y y' h
  funext a
  have entry : ∀ z : Fin n → k, ((GlobalTheory.CompanionTheory.BZPsiPG.uM k n z : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.last n) = z a := by
    intro z
    change (1 + GlobalTheory.BZMir.colMat k n z) (Fin.castSucc a) (Fin.last n) = z a
    simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]
  rw [← entry y, ← entry y', h]

theorem uM_levi_inj (n : ℕ) {y y' : Fin n → k} {g g' : GL (Fin n) k}
    (h : uM k n y * levi k n g = uM k n y' * levi k n g') : y = y' ∧ g = g' := by
  have hg : g = g' := by
    have hp := congrArg (GlobalTheory.BZMir.mirabolicProjection k n) h
    simpa only [map_mul, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mirProj_levi_eq, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mirProj_uM, one_mul] using hp
  subst hg
  exact ⟨GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.uM_injective n (mul_right_cancel h), rfl⟩

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def latt (n : ℕ) (c : kˣ) : AddSubgroup (Fin n → k) where
  carrier := {y | ∀ j, y j ∈ cball c}
  add_mem' ha hb j := add_mem_cball (ha j) (hb j)
  zero_mem' j := by simp [cball]
  neg_mem' ha j := neg_mem_cball (ha j)

theorem mem_latt {n : ℕ} {c : kˣ} {y : Fin n → k} : y ∈ latt n c ↔ ∀ j, y j ∈ cball c :=
  Iff.rfl

theorem latt_eq_pi (n : ℕ) (c : kˣ) : (latt n c : Set (Fin n → k)) = Set.univ.pi fun _ => cball c := by
  ext y
  simp only [SetLike.mem_coe, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_latt, Set.mem_univ_pi]

theorem isOpen_latt (n : ℕ) (c : kˣ) : IsOpen (latt n c : Set (Fin n → k)) := by
  rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ => GlobalTheory.SplitWeil.isOpen_cball c

theorem isCompact_latt (n : ℕ) (c : kˣ) : IsCompact (latt n c : Set (Fin n → k)) := by
  rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt_eq_pi]
  exact isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball c

theorem isClosed_latt (n : ℕ) (c : kˣ) : IsClosed (latt n c : Set (Fin n → k)) :=
  AddSubgroup.isClosed_of_isOpen _ (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_latt n c)

theorem exists_latt_subset {n : ℕ} {U : Set (Fin n → k)} (hU : U ∈ 𝓝 (0 : Fin n → k)) :
    ∃ c : kˣ, (latt n c : Set (Fin n → k)) ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  have hmem : (⋂ j, t j) ∈ 𝓝 (0 : k) := Filter.iInter_mem.2 fun j => by simpa using ht j
  obtain ⟨c, hc⟩ := GlobalTheory.SplitWeil.exists_cball_subset hmem
  refine ⟨c, fun y hy => hsub (Set.mem_pi.2 fun j _ => ?_)⟩
  exact Set.mem_iInter.1 (hc (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_latt.1 hy j)) j

theorem mulVec_mem_latt {n : ℕ} {c : kˣ} {κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) {y : Fin n → k}
    (hy : y ∈ latt n c) : (κ : Matrix (Fin n) (Fin n) k).mulVec y ∈ latt n c := by
  rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_latt] at hy ⊢
  have hint := ((GlobalTheory.SplitFlip.mem_KO_iff κ).1 hκ).1
  intro j
  change valuation k ((κ : Matrix (Fin n) (Fin n) k).mulVec y j) ≤ valuation k (c : k)
  simp only [Matrix.mulVec, dotProduct]
  apply Valuation.map_sum_le
  intro i _
  rw [map_mul]
  calc valuation k ((κ : Matrix (Fin n) (Fin n) k) j i) * valuation k (y i)
      ≤ 1 * valuation k (c : k) :=
        mul_le_mul' ((Valuation.mem_integer_iff _ _).1 (hint j i)) (hy i)
    _ = valuation k (c : k) := one_mul _

def Bgrp (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ KO k (Fin n)) : Subgroup (Mir k n) where
  carrier := {p | ∃ y ∈ latt n c, ∃ b ∈ K₁, p = uM k n y * levi k n b}
  mul_mem' := by
    rintro _ _ ⟨y, hy, b, hb, rfl⟩ ⟨y', hy', b', hb', rfl⟩
    exact ⟨_, add_mem hy (mulVec_mem_latt (h hb) hy'), _, mul_mem hb hb', uM_levi_mul_uM_levi n y y' b b'⟩
  one_mem' := ⟨0, zero_mem _, 1, one_mem _, by rw [uM_zero, map_one, one_mul]⟩
  inv_mem' := by
    rintro _ ⟨y, hy, b, hb, rfl⟩
    refine ⟨_, mulVec_mem_latt (h (inv_mem hb)) (neg_mem hy), b⁻¹, inv_mem hb, ?_⟩
    rw [_root_.mul_inv_rev, ← map_inv, GlobalTheory.CompanionTheory.BZPsiPG.Cont.uM_inv, levi_mul_uM]

theorem mem_Bgrp {n : ℕ} {c : kˣ} {K₁ : Subgroup (GL (Fin n) k)} {h : K₁ ≤ KO k (Fin n)} {p : Mir k n} :
    p ∈ Bgrp n c K₁ h ↔ ∃ y ∈ latt n c, ∃ b ∈ K₁, p = uM k n y * levi k n b :=
  Iff.rfl

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentBallMemCongruence
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem colMat_mem_ball {s : kˣ} {n : ℕ} {v : Fin n → k} (hv : ∀ a, v a ∈ GlobalTheory.SplitWeil.cball s)
    (a b : Fin (n + 1)) : colMat k n v a b ∈ GlobalTheory.SplitWeil.cball s := by
  have h0 : (0 : k) ∈ GlobalTheory.SplitWeil.cball s := by simp [GlobalTheory.SplitWeil.cball]
  by_cases hb : b = Fin.last n
  · subst hb
    induction a using Fin.lastCases with
    | last => simpa [GlobalTheory.BZMir.colMat] using h0
    | cast a => simpa [GlobalTheory.BZMir.colMat] using hv a
  · simpa [GlobalTheory.BZMir.colMat, hb] using h0

theorem unip_mem_congGL {s : kˣ} (hs : ValuativeRel.valuation k (s : k) ≤ 1) {n : ℕ} {v : Fin n → k}
    (hv : ∀ a, v a ∈ GlobalTheory.SplitWeil.cball s) :
    unip k n (Multiplicative.ofAdd v) ∈ congGL k s hs (n + 1) := by
  have h1 : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s (1 + GlobalTheory.BZMir.colMat k n v) := by
    intro a b
    rw [Matrix.add_apply, add_sub_cancel_left]
    exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.colMat_mem_ball hv a b
  have h2 : GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s (1 - GlobalTheory.BZMir.colMat k n v) := by
    intro a b
    rw [Matrix.sub_apply, sub_sub_cancel_left]
    exact GlobalTheory.SplitWeil.neg_mem_cball (GlobalTheory.CompanionTheory.BZPhiPG.Onto.colMat_mem_ball hv a b)
  exact And.intro h1 h2

theorem colMat_mul_apply {n : ℕ} (v : Fin n → k) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (a : Fin n)
    (c : Fin (n + 1)) : (colMat k n v * A) (Fin.castSucc a) c = v a * A (Fin.last n) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
  · simp [GlobalTheory.BZMir.colMat]
  · intro j _ hj
    simp [GlobalTheory.BZMir.colMat, hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ball_of_unip_eq_mul {s : kˣ} (hs : ValuativeRel.valuation k (s : k) ≤ 1) {n : ℕ} {v : Fin n → k}
    {h κ : GL (Fin (n + 1)) k} (heq : unip k n (Multiplicative.ofAdd v) = h * κ)
    (hκ : κ ∈ congGL k s hs (n + 1)) (a : Fin n)
    (h0 : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.last n) = 0)
    (h1 : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1) :
    v a ∈ GlobalTheory.SplitWeil.cball s := by
  have hinv : κ⁻¹ = (GlobalTheory.BZMir.unip k n (Multiplicative.ofAdd v))⁻¹ * h := by
    rw [heq, _root_.mul_inv_rev, inv_mul_cancel_right]
  have hmat : ((κ⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      (1 - GlobalTheory.BZMir.colMat k n v) * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    rw [hinv, Units.val_mul]
    rfl
  have hc := (show _ ∧ GlobalTheory.CompanionTheory.BZPhiPG.Onto.NearOne s ((κ⁻¹ : GL (Fin (n + 1)) k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) k) from hκ).2 (Fin.castSucc a) (Fin.last n)
  rw [hmat, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, GlobalTheory.CompanionTheory.BZPhiPG.Onto.colMat_mul_apply, h0, h1,
    Matrix.one_apply_ne (Fin.castSucc_ne_last a)] at hc
  simp only [zero_sub, mul_one, sub_zero] at hc
  have hneg := GlobalTheory.SplitWeil.neg_mem_cball hc
  rwa [neg_neg] at hneg

theorem Mir_last_last {n : ℕ} (g : Mir k n) :
    ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  have hrow := (GlobalTheory.BZMir.mem_Mir_iff k (g : GL (Fin (n + 1)) k)).1 g.2
  have hentry := congrFun hrow (Fin.last n)
  simpa [GlobalTheory.BZMir.eLast] using hentry

theorem ePG_true_natAdd (i t : ℕ) (j : Fin (t + 1)) :
    ePG (i + 1) (t + 1) ⟨true, j⟩ = Fin.castSucc (Fin.natAdd (i + 1) j) := by
  first
    | rfl
    | exact Fin.ext rfl
    | (ext; simp [GlobalTheory.BZMir.Leib.ePG])

theorem HPG_entry_zero {i t : ℕ} (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1)) (j : Fin (t + 1)) :
    ((h : GL (Fin ((i + 1) + (t + 1) + 1)) k) : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k)
      (Fin.castSucc (Fin.natAdd (i + 1) j)) (Fin.last ((i + 1) + (t + 1))) = 0 := by
  have hh' : (h : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈
      GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG (i + 1) (t + 1)) := hh
  have hz := GlobalTheory.SmGL.mem_parab_iff.1 hh' true false j (Fin.last (i + 1)) (by decide)
  rwa [GlobalTheory.CompanionTheory.BZPhiPG.Onto.ePG_true_natAdd, GlobalTheory.BZMir.Leib.ePG_false_last] at hz

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

theorem GlobalTheory.CompanionTheory.BZPhiPG.Onto.dEmb_mem_congM_and_ball : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (d : Fin (t + 1) → k),
  ((∀ j, d j ∈ GlobalTheory.SplitWeil.cball s) → dEmb k i t d ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t + 1)) ∧
  ∀ (h : Mir k ((i + 1) + t + 1)), h ∈ HPG k (i + 1) (t + 1) → ∀ κ ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs ((i + 1) + t + 1),
    dEmb k i t d = h * κ → ∀ j, d j ∈ GlobalTheory.SplitWeil.cball s := by
  intro k _ _ _ _ i t s hs d
  refine ⟨fun hd => ?_, fun h hh κ hκ he j => ?_⟩
  · have hv : ∀ a, Fin.append (0 : Fin (i + 1) → k) d a ∈ GlobalTheory.SplitWeil.cball s := by
      intro a
      refine Fin.addCases (fun a => ?_) (fun b => ?_) a
      · rw [Fin.append_left]
        simp [GlobalTheory.SplitWeil.cball]
      · rw [Fin.append_right]
        exact hd b
    first
      | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.unip_mem_congGL hs hv
      | exact Subgroup.mem_comap.2 (GlobalTheory.CompanionTheory.BZPhiPG.Onto.unip_mem_congGL hs hv)
  · have he' : GlobalTheory.BZMir.unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append (0 : Fin (i + 1) → k) d)) =
        (h : GL (Fin ((i + 1) + (t + 1) + 1)) k) * (κ : GL (Fin ((i + 1) + (t + 1) + 1)) k) :=
      congrArg Subtype.val he
    have hmem := GlobalTheory.CompanionTheory.BZPhiPG.Onto.ball_of_unip_eq_mul hs he' hκ (Fin.natAdd (i + 1) j)
      (GlobalTheory.CompanionTheory.BZPhiPG.Onto.HPG_entry_zero h hh j)
      (GlobalTheory.CompanionTheory.BZPhiPG.Onto.Mir_last_last h)
    rwa [Fin.append_right] at hmem

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryBorelSplitting
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BorelSplit

theorem borelSplitU : PositivityTheory.SphericalProduct.BorelSplitU := by
  intro L _ _ σ n _ b hb
  have hbT : ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id :=
    (Formalism.UG.P.spherical_upper_iff _).1 hb
  let qb : GlobalTheory.LGrp.blockQ L (id : Fin n → Fin n) := ⟨(b : GL (Fin n) L), hbT⟩
  have htG : GlobalTheory.LGrp.blockProj id qb ∈ GU σ n :=
    GlobalTheory.LGrp.blockProj_mem_GU σ (GlobalTheory.LGrp.selfDualBlocks_id n) qb b.2
  let t : GU σ n := ⟨GlobalTheory.LGrp.blockProj id qb, htG⟩
  have hdiag : ∀ i, ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
    intro i
    show (GlobalTheory.LGrp.blockProj id qb).val i i = _
    rw [GlobalTheory.LGrp.blockProj_val]
    simp [GlobalTheory.LGrp.blockPart, qb]
  have hoff : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
    intro i j hij
    show (GlobalTheory.LGrp.blockProj id qb).val i j = _
    rw [GlobalTheory.LGrp.blockProj_val]
    simp [GlobalTheory.LGrp.blockPart, hij]
  have htT : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id :=
    fun i j h => hoff i j (ne_of_gt h)
  have htiT := Formalism.UG.P.spherical_upper_inv _ htT
  refine ⟨t, t⁻¹ * b, hoff, ⟨?_, ?_⟩, by group⟩
  · refine (Formalism.UG.P.spherical_upper_iff _).2 ?_
    show ((((t : GL (Fin n) L))⁻¹ * (b : GL (Fin n) L) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id
    exact Formalism.UG.P.spherical_upper_mul _ _ htiT hbT
  · intro i
    show ((((t : GL (Fin n) L))⁻¹ * (b : GL (Fin n) L) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1
    have h1 : ((((t : GL (Fin n) L))⁻¹ * (t : GL (Fin n) L) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
      rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [Units.val_mul, Formalism.UG.P.spherical_diag_mul _ _ htiT hbT, ← hdiag]
    rwa [Units.val_mul, Formalism.UG.P.spherical_diag_mul _ _ htiT htT] at h1

end GlobalTheory.CompanionTheory.BorelSplit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittFrameRankLeWittIndexStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_frame_rank_le_witt_index : ∀ (D : D7) (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  first | exact @GlobalTheory.CompanionTheory.WittFrame.length_le_wittIdx | exact GlobalTheory.CompanionTheory.WittFrame.length_le_wittIdx | (intros; apply GlobalTheory.CompanionTheory.WittFrame.length_le_wittIdx <;> assumption)
end

