module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelDoubleStepOfFlatColumnFlatRow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotIntPosOne
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents app_coe)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale volR)

noncomputable section
namespace GlobalTheory.PosOneCell

section Lemmas
variable {X : Type} [TopologicalSpace X] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem app_smul (l : SB X →ₗ[ℂ] V) (z : ℂ) (f : X → ℂ) : app l (z • f) = z • app l f := by
  by_cases hz : z = 0
  · subst hz
    have : app l (0 : X → ℂ) = 0 := by
      rw [show (0 : X → ℂ) = ((0 : SB X) : X → ℂ) from rfl, app_coe, map_zero]
    rw [zero_smul, zero_smul, this]
  · by_cases hf : f ∈ SB X
    · have hzf : z • f ∈ SB X := (SB X).smul_mem z hf
      simp only [app, hf, hzf, dif_pos]
      rw [← map_smul]
      rfl
    · have hzf : z • f ∉ SB X := fun h => hf (((SB X).smul_mem_iff hz).1 h)
      simp [app, hf, hzf]

theorem app_zero (l : SB X →ₗ[ℂ] V) : app l (0 : X → ℂ) = 0 := by
  rw [show (0 : X → ℂ) = ((0 : SB X) : X → ℂ) from rfl, app_coe, map_zero]

end Lemmas

theorem quotInt_posOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (_ : 1 ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : HasConductor ψ 1) (ν : Measure k) (_ : IsUnitVol ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (m : Measure (GL n k)) [m.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (L : Level (GL (n ⊕ Fin c) k)) (_ : IsCO L.J) (_ : μG L.J = 1) (b : GL (n ⊕ Fin c) k) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ 1 σ B) (F : A) (_ : ∀ j : L.J, σ (j : GL (n ⊕ Fin c) k) F = (L.lam j : ℂ) • F) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (_ : ∀ j : L.J, om μ 1 (j : GL (n ⊕ Fin c) k) Φ.1 = (((L.lam j)⁻¹ : ℂˣ) : ℂ) • Φ.1) (h' : GL (n' ⊕ Fin (c + 1)) k) (T : Finset (GL (n ⊕ Fin c) k)) (_ : Covers 1 L.J T fun h => flat ψ ν μ Φ.1 h' h), IsQuotInt ν (rescale ν b m) μG 1 (tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1)) (∑ h ∈ T, (((m (prX (Cgrp L.J h))).toReal⁻¹ : ℝ) : ℂ) * app B (xi ψ ν μ Φ.1 L.J b h' h) (σ h F)) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c hc ψ hψ hψc ν hν μ hμ m _ μG _ L hJ hJ1 b A _ _ σ hσ B hB F hF Φ hΦ h' T hT
  haveI : ν.IsAddHaarMeasure := hν.1
  have hr := volN_stabLat (n := n) (c := c) ν b
  haveI : (rescale ν b m).IsHaarMeasure := by
    unfold rescale
    exact Measure.IsHaarMeasure.smul m (ENNReal.inv_ne_zero.2 (ENNReal.toReal_pos_iff.1 hr).2.ne)
      (ENNReal.inv_ne_top.2 (ENNReal.toReal_pos_iff.1 hr).1.ne')
  have hflat : ∀ h, tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) h = app B (flat ψ ν μ Φ.1 h' h) (σ h F) := by
    intro h
    simp only [tInt, flat]
    rw [← om_mul]
    simp
  have hSB : ∀ h, flat ψ ν μ Φ.1 h' h ∈ SB (Matrix n n' k) := fun h =>
    (GlobalTheory.RootEx.opE_SB_and_linear k n n' c 1 ψ hψ ν).1 _ (om_mem_SB μ h' h Φ.2)
  have hinv : ∀ h, ∀ j ∈ L.J, tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) (h * j) = tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) h := by
    intro h j hj
    have hΦj : om μ 1 j Φ.1 = (((L.lam ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) • Φ.1 := hΦ ⟨j, hj⟩
    have hFj : σ j F = (L.lam ⟨j, hj⟩ : ℂ) • F := hF ⟨j, hj⟩
    have e : flat ψ ν μ Φ.1 h' (h * j) = (((L.lam ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) • flat ψ ν μ Φ.1 h' h := by
      unfold flat
      rw [show om μ h' (h * j) Φ.1 = om μ h' h (om μ 1 j Φ.1) by rw [← om_mul]; simp, hΦj,
        GlobalTheory.UnfoldedEntries.om_smul, GlobalTheory.UnfoldedEntries.opE_smul]
    rw [hflat, hflat, e, PosOneCell.app_smul, map_mul, Module.End.mul_apply, hFj, map_smul, map_smul,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mul]
  have hmod : ∀ (x : GL n k), ∀ u ∈ N k n c 1, ∀ h, tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) (embX c x * u * h) =
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * ((1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) h := by
    intro x u hu h
    have e : flat ψ ν μ Φ.1 h' (embX c x * u * h) =
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) •
          om μ 1 x ((ψ (-simpleSum u) : ℂ) • flat ψ ν μ Φ.1 h' h) := by
      unfold flat
      rw [show om μ h' (embX c x * u * h) Φ.1 = om μ 1 (embX c x) (om μ 1 u (om μ h' h Φ.1)) by
          rw [← om_mul, ← om_mul]; simp,
        (GlobalTheory.RootEx.opE_om_embX k n n' c 1 le_rfl hc ψ ν μ _).1,
        GlobalTheory.RootEx.opE_om_target_unipotent k n n' c 1 le_rfl hc ψ ν μ _ u hu]
    let Ψ : SB (Matrix n n' k) := ⟨flat ψ ν μ Φ.1 h' h, hSB h⟩
    let Ψ₁ : SB (Matrix n n' k) := ⟨om μ 1 x (flat ψ ν μ Φ.1 h' h), om_mem_SB μ 1 x (hSB h)⟩
    have a0 : app B (flat ψ ν μ Φ.1 h' h) = B Ψ := app_coe B Ψ
    have a1 : app B (om μ 1 x (flat ψ ν μ Φ.1 h' h)) = B Ψ₁ := app_coe B Ψ₁
    rw [hflat, hflat, e, GlobalTheory.UnfoldedEntries.om_smul, smul_smul, PosOneCell.app_smul, map_mul, map_mul,
      Module.End.mul_apply, Module.End.mul_apply, a0, a1, LinearMap.smul_apply, hB.2 x Ψ Ψ₁ _ rfl,
      hB.1 Ψ u hu, smul_eq_mul]
    have key : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
    have hp := GlobalTheory.RootEx.OpELevi.nabs_pos (Matrix.GeneralLinearGroup.det x)
    have rp : ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) =
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * ((1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add hp]
      congr 2
      ring
    linear_combination (B Ψ (σ h F)) * (((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ)) * key
      + (B Ψ (σ h F)) * rp
  have hcov : Covers 1 L.J T (tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1)) := by
    refine ⟨hT.1, fun h hh => hT.2 h ?_⟩
    intro h0
    apply hh
    simp only at h0
    rw [hflat, h0, PosOneCell.app_zero, LinearMap.zero_apply]
  obtain ⟨-, hiff⟩ := _root_.GlobalTheory.CellQuotInt.isQuotInt_cells k n c 1 le_rfl hc ν (rescale ν b m) μG L.J hJ _ hinv hmod T hcov
  refine (hiff _).2 (Finset.sum_congr rfl fun h _ => ?_)
  obtain ⟨-, -, -, -, hm⟩ := GlobalTheory.UnfoldedEntries.cosetMeasure (ν := ν) n c hc L.J hJ h
  obtain ⟨-, -, -, hresc, -⟩ := hm m inferInstance
  have hvc : volCell ν (rescale ν b m) 1 L.J h = volR ν (rescale ν b m) (Cgrp L.J h) := by
    unfold volCell volR
    refine lintegral_congr fun g => ?_
    congr 1
    ext u
    simp only [Set.mem_setOf_eq, mem_Cgrp]
    refine ⟨fun H => ⟨?_, H⟩, fun H => H.2⟩
    exact (R k n c 1).mul_mem (Subgroup.mem_sup_left (MonoidHom.mem_range.2 ⟨g, rfl⟩)) (Subgroup.mem_sup_right u.2)
  have hxi : xi ψ ν μ Φ.1 L.J b h' h = (((volNat ν b (Cgrp L.J h))⁻¹ : ℝ) : ℂ) • flat ψ ν μ Φ.1 h' h := rfl
  rw [hxi, PosOneCell.app_smul, LinearMap.smul_apply, smul_eq_mul, hflat, hvc, hresc b, hJ1, ENNReal.toReal_one]
  push_cast
  ring

end GlobalTheory.PosOneCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMulAddCharLinearForm
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.PartRed

theorem sb_mul_addChar_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (R Q : Type) [Fintype R] [Fintype Q] (f : Matrix R Q k →ₗ[k] k) (z : k) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → (fun x => (ψ (f x + z) : ℂ) * Φ x) ∈ SB (Matrix R Q k) := by
  intro k _ _ _ _ ψ hψ R Q _ _ f z Φ hΦ
  classical
  obtain ⟨h1, h2⟩ := hΦ
  have hexp : ∀ x : Matrix R Q k, f x = ∑ i, ∑ j, x i j * f (Matrix.single i j 1) := by
    intro x
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← LinearMap.map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hf : Continuous f := by
    have : (f : Matrix R Q k → k) = fun x => ∑ i, ∑ j, x i j * f (Matrix.single i j 1) := funext hexp
    rw [this]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (continuous_id.matrix_elem i j).mul continuous_const
  refine ⟨?_, ?_⟩
  · exact ((OpenKernel.isLocallyConstant_coe_addChar ψ hψ).comp_continuous
      (hf.add continuous_const)).mul h1
  · exact h2.mul_left

end GlobalTheory.PartRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymCollapseOfAllPositions
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.LocFlat

theorem symCollapse_of_allPositions : AllPositions → GlobalTheory.LocFlat.SymCollapse := by
  intro hA k _ _ _ _ _ _ ν hν s κ S t _ _
  obtain ⟨hO, hE⟩ := hA k ν hν s κ S t
  have hP : S.Pattern t := GlobalTheory.SymChain.pattern_iter k s κ S t
  have hC := _root_.GlobalTheory.LocFlat.pureCol_of_pattern k ν hν s κ S t hP hE
  have hR := _root_.GlobalTheory.LocFlat.pureRow_of_exchange k ν hν s κ S t hP hE
  exact ⟨_root_.GlobalTheory.LocFlat.suppCol_of_oneIndexAt k ν hν s κ S t hO, hC, hR, _root_.GlobalTheory.LocFlat.doubleStep_of_pureCol_pureRow k ν hν s κ S t hP hO hC hR⟩

end GlobalTheory.LocFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainClassAtEveryPosition
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem classAt_all : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.ClassAt t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ j c H p hp1 hpc h hE
  haveI := hν.1
  obtain ⟨D, hDdef⟩ : ∃ D : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k,
      D = embA (XIx (Fin κ) t (j + 1)) (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)) := ⟨_, rfl⟩
  obtain ⟨D', hD'def⟩ : ∃ D' : GL (XIx (Fin κ) t j ⊕ Fin (c + 1)) k,
      D' = embA (XIx (Fin κ) t j) (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1)) := ⟨_, rfl⟩
  have hD : (S.T t).bas (j + 1) c (by omega) = D := by rw [hDdef]; rfl
  have hlt : valuation k (S.ϖ : k) < 1 := (S.unif (S.ϖ : k)).2 le_rfl
  let lv' : XIx (Fin κ) t (j + 1) ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))
  have hlv : ∀ r s, lev p s < lev p r → lv' s < lv' r := by
    rintro (r | r) (s | s) h0 <;> simp only [lev, lv', Sum.elim_inl, Sum.elim_inr] at h0 ⊢ <;> omega
  obtain ⟨b, hb, w, hw, hbw⟩ := iwasawa_blockTriangular k _ lv' (h * D)
  have hb' : b.val.BlockTriangular (lev p) := fun r s hrs => hb (hlv r s hrs)
  obtain ⟨u, hu, m, hm1, hm2, hum⟩ := BlockLevi.exists_unip_mul_levi k _ c p b hb'
  have hh : h = u * (m * w * D⁻¹) := by
    have : h = h * D * D⁻¹ := by group
    rw [this, hbw, hum]; group
  obtain ⟨v, hv⟩ : ∃ v, v = m * w * D⁻¹ := ⟨_, rfl⟩
  rw [← hv] at hh
  have key : om (S.μ (j + 1)) 1 (u * v) ((S.T t).Phi j c H) =
      om (S.μ (j + 1)) 1 u (om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H)) := by
    simpa using Model.om_mul (S.μ (j + 1)) 1 1 u v ((S.T t).Phi j c H)
  have hE' : opE S.ψ ν p (om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H)) ≠ 0 := by
    intro h0; apply hE
    rw [hh, key, opE_om_target_unipotent k _ _ c p hp1 hpc S.ψ ν (S.μ (j + 1)) _ u hu, h0, smul_zero]
  have eg : D⁻¹ * v⁻¹ = w⁻¹ * m⁻¹ := by rw [hv]; group
  have ev : ∀ x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k,
      (D⁻¹).val * ((v⁻¹).val * x) * D'.val = (w⁻¹).val * ((m⁻¹).val * x * D'.val) := by
    intro x
    rw [← Matrix.mul_assoc (D⁻¹).val, ← Units.val_mul, eg, Units.val_mul]; simp only [Matrix.mul_assoc]
  have hinst := GlobalTheory.T.symmetricLevelChain_phi_support_periodic k s κ S t j c H
  rw [← hDdef, ← hD'def] at hinst
  have hsup : ∀ x, om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H) x ≠ 0 → IntM ((m⁻¹).val * x * D'.val) := by
    intro x hx
    have hΦ : (S.T t).Phi j c H ((v⁻¹).val * x) ≠ 0 := by
      have := right_ne_zero_of_mul hx
      simpa using this
    have h1 := (hinst ((v⁻¹).val * x) 0).1 hΦ
    rw [ev] at h1
    have e2 : (m⁻¹).val * x * D'.val = w.val * ((w⁻¹).val * ((m⁻¹).val * x * D'.val)) := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [e2]; exact (intM_of_mem_KO hw).mul h1
  have hper : ∀ x z, MaxM ((m⁻¹).val * z * D'.val) →
      om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H) (x + z) = om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H) x := by
    intro x z hz
    have h1 : MaxM ((D⁻¹).val * ((v⁻¹).val * z) * D'.val) := by
      rw [ev]; exact (mem_KO.1 hw).2.mul_maxM hz
    simp only [om, Units.val_one, Matrix.mul_one, Matrix.mul_add]
    rw [(hinst ((v⁻¹).val * x) ((v⁻¹).val * z)).2 h1]
  have sm1 : m.val.BlockTriangular lv' := by
    intro r s hrs
    by_cases e : lev p r = lev p s
    · rw [hm2 r s e]; exact hb hrs
    · exact hm1 r s e
  have sm2 : m.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) := by
    intro r s hrs
    exact hm1 r s (Nat.ne_of_lt (OrderDual.toDual_lt_toDual.mp hrs))
  have si1 : (m⁻¹).val.BlockTriangular lv' := BlockLevi.blockTriangular_inv lv' m sm1
  have si2 : (m⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) := by
    letI : Invertible m.val := m.invertible
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular sm2
  have sm1' : (m⁻¹⁻¹).val.BlockTriangular lv' := by rw [inv_inv]; exact sm1
  have sm2' : (m⁻¹⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) := by rw [inv_inv]; exact sm2
  rw [hD'def] at hsup hper
  obtain ⟨E1, E2⟩ := _root_.GlobalTheory.PosEntries.entries k S.ψ ν S.cond S.ϖ hlt _ _ c p hp1 hpc m⁻¹ si1 si2 sm1' sm2' _ hsup hper hE'
  obtain ⟨γ, hK⟩ := _root_.GlobalTheory.PClassAlg.blockDiag_mem_KO k S.ϖ _ c p hp1 hpc m⁻¹ si1 si2 sm1' sm2' E1 E2
  rw [← hDdef] at hK
  refine ⟨u * embX c γ, mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨γ, rfl⟩),
    (u * embX c γ)⁻¹ * h, ?_, by group⟩
  rw [hD, mem_stabLat]
  have : D⁻¹ * ((u * embX c γ)⁻¹ * h) * D = (m⁻¹ * embX c γ * D)⁻¹ * w := by
    rw [hh, hv]; group
  rw [this]
  exact mul_mem (inv_mem hK) hw

end GlobalTheory.SymChain
end

