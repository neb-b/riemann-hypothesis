module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0642
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicAverageEqCoeffSinglePlaceElement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.MirAvg

theorem bc_ringEquiv_eq_one_iff {r : ℕ} {K K' : Type} [CommRing K] [CommRing K'] (e : K ≃+* K') (h : GL (Fin r) K) :
    Formalism.UG.bc (e : K →+* K') h = 1 ↔ h = 1 := by
  refine ⟨fun H => ?_, fun H => by rw [H, map_one]⟩
  ext i j
  have := congrArg (fun u : GL (Fin r) K' => (u : Matrix (Fin r) (Fin r) K') i j) H
  apply e.injective
  have h1 : ((Formalism.UG.bc (e : K →+* K') h : GL (Fin r) K') : Matrix (Fin r) (Fin r) K') i j
      = e ((h : Matrix (Fin r) (Fin r) K) i j) := rfl
  simp only [h1] at this
  rw [this]
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem bc_ringEquiv_mulVec {r : ℕ} {K K' : Type} [CommRing K] [CommRing K'] (e : K ≃+* K') (h : GL (Fin r) K)
    (x : Fin r → K) :
    ((Formalism.UG.bc (e : K →+* K') h : GL (Fin r) K') : Matrix (Fin r) (Fin r) K').mulVec (fun j => e (x j)) =
      fun j => e ((h : Matrix (Fin r) (Fin r) K).mulVec x j) := by
  funext j
  have h1 : ∀ i j, ((Formalism.UG.bc (e : K →+* K') h : GL (Fin r) K') : Matrix (Fin r) (Fin r) K') i j
      = e ((h : Matrix (Fin r) (Fin r) K) i j) := fun _ _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, h1, map_sum, map_mul]

theorem det_bc_ringEquiv {r : ℕ} {K K' : Type} [CommRing K] [CommRing K'] (e : K ≃+* K') (h : GL (Fin r) K) :
    Matrix.GeneralLinearGroup.det (Formalism.UG.bc (e : K →+* K') h) =
      Units.map (e : K →* K') (Matrix.GeneralLinearGroup.det h) := by
  ext
  exact ((e : K →+* K').map_det (h : Matrix (Fin r) (Fin r) K)).symm

theorem mirSet_iff_bc {g : ℕ} [Fact g.Prime] {r : ℕ} {K' : Type} [CommRing K'] (e : ZMod g ≃+* K')
    (h : GL (Fin r) (ZMod g)) (a : Fin r → K') (b : Bool) :
    (if b then ∀ x, ∃ c : K', ((Formalism.UG.bc (e : ZMod g →+* K') h : GL (Fin r) K') :
        Matrix (Fin r) (Fin r) K').mulVec x - x = c • a
      else ∀ x, a ⬝ᵥ x = 0 → ((Formalism.UG.bc (e : ZMod g →+* K') h : GL (Fin r) K') :
        Matrix (Fin r) (Fin r) K').mulVec x = x) ↔ mirSet (fun j => e.symm (a j)) b h := by
  have hs : Function.Surjective (fun (x : Fin r → ZMod g) j => e (x j)) :=
    fun x => ⟨fun j => e.symm (x j), by funext j; simp⟩
  cases b with
  | true =>
    simp only [mirSet, if_true]
    rw [hs.forall]
    refine forall_congr' fun x => ?_
    rw [bc_ringEquiv_mulVec, e.surjective.exists]
    refine exists_congr fun c => ?_
    simp only [funext_iff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine forall_congr' fun j => ?_
    rw [← e.injective.eq_iff (a := _ - _), map_sub, map_mul, e.apply_symm_apply]
  | false =>
    simp only [mirSet, Bool.false_eq_true, if_false]
    rw [hs.forall]
    refine forall_congr' fun x => ?_
    rw [bc_ringEquiv_mulVec]
    refine imp_congr ?_ ?_
    · rw [← e.injective.eq_iff (b := 0), map_zero]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, map_sum, map_mul, e.apply_symm_apply]
    · simp only [funext_iff, e.injective.eq_iff]

theorem mirC_eq_coeff_mirEl : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eR : G ≃* G0g D.nd)
    (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) →
    ∀ (i : Fin D.R.m) (kv0 : Σ k : Fin 2, D.nd.PlG k) (a : Fin D.R.r → kP (plg kv0).1) (b : Bool) (ε : ℤ) (y : G),
    haveI : Fact (D.host.g kv0.1).Prime := ⟨D.host.g_prime kv0.1⟩
    GlobalTheory.DownLift.mirC R i (plg kv0) a b ε y = (open Classical in if ∀ kv, kv ≠ kv0 → eR y kv = 1 then
      (GlobalTheory.MirAvg.mirEl ((zpowGroupHom ε).comp ((R.chi ((i : ℕ) + 1) (plg kv0).1).comp
        (Units.map (iso kv0 : ZMod (D.host.g kv0.1) →* kP (plg kv0).1))))
        (fun j => (iso kv0).symm (a j)) b).coeff (eR y kv0) else 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R eR plg iso hrec i kv0 a b ε y
  haveI : Fact (D.host.g kv0.1).Prime := ⟨D.host.g_prime kv0.1⟩
  have h1 : (∀ PP', PP' ≠ plg kv0 → R.eG y PP' = 1) ↔ ∀ kv, kv ≠ kv0 → eR y kv = 1 := by
    rw [plg.surjective.forall]
    refine forall_congr' fun kv => imp_congr plg.injective.ne_iff ?_
    rw [hrec]
    exact bc_ringEquiv_eq_one_iff _ _
  have h2 := mirSet_iff_bc (iso kv0) (eR y kv0) a b
  have h3 := det_bc_ringEquiv (iso kv0) (eR y kv0)
  rw [← hrec] at h2 h3
  rw [mirEl_coeff]
  unfold GlobalTheory.DownLift.mirC
  by_cases hA : ∀ kv, kv ≠ kv0 → eR y kv = 1
  · rw [if_pos hA]
    by_cases hB : mirSet (fun j => (iso kv0).symm (a j)) b (eR y kv0)
    · rw [if_pos hB, if_pos ⟨h1.2 hA, h2.2 hB⟩, h3]
      rfl
    · rw [if_neg hB, if_neg fun H => hB (h2.1 H.2)]
  · rw [if_neg hA, if_neg fun H => hA (h1.1 H.1)]

end GlobalTheory.MirAvg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OmRatInvApply
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift.Move

variable {D : D7}

theorem heisO_eval_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  have h : symplOH S T 0 w = 0 := by
    simp [symplOH, symplO, hO]
  simp [heisO, h]

theorem mt_one_eq (S : HSp D) : mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem mt_mul_eq (S : HSp D) (g h : GA D S) : mt S (g * h) = mt S g * mt S h := by simp [Formalism.L2.Theta.mt]

theorem actO_one_left (V W : HSp D) (γ : GA D W) (w : WO V W) :
    actO V W 1 γ w = HMul.hMul (mt W γ) (w : Matrix (Fin W.rank) (Fin V.rank) (AE D)) := by
  unfold actO
  rw [inv_one, mt_one_eq, Matrix.mul_one]

theorem om_rat_actO {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (H : IsWeilDatumO ψ V W χV χW om) {γ : GA D W}
    (hγ : γ ∈ GQ W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (w : WO V W) :
    om (1, γ) f (actO V W 1 γ w) = f w := by
  have h1 := H.om_heis 1 γ w f hf
  have h2 := H.om_aut 1 (one_mem _) γ hγ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all H.std hf w)
  rw [← heisO_eval_zero ψ V W (actO V W 1 γ w) (om (1, γ) f), ← h1, h2, heisO_eval_zero]

theorem om_rat_inv_apply {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (H : IsWeilDatumO ψ V W χV χW om) {γ : GA D W}
    (hγ : γ ∈ GQ W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (w : WO V W) :
    om (1, γ⁻¹) f w = f (actO V W 1 γ w) := by
  have h := om_rat_actO H (inv_mem hγ) hf (actO V W 1 γ w)
  have e : actO V W 1 γ⁻¹ (actO V W 1 γ w) = w := by
    rw [actO_one_left, actO_one_left, ← Matrix.mul_assoc, ← mt_mul_eq, inv_mul_cancel, mt_one_eq, Matrix.one_mul]
  rwa [e] at h

theorem ratMul_eq_actO {V W : HSp D} {γ : GA D W} {c : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hc : mt W γ = c.map (incA D)) (u : WO V W) : ratMul c u = actO V W 1 γ u := by
  rw [actO_one_left, hc]
  rfl

theorem termMove : ∀ D : D7, TermMove D := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr h f₁ f₂ h₁ h₂
  refine ⟨fun Y C hC => lagTerm_frame_indep D ψ V W μ 𝓕 h.covol h.weil.std f₁ f₂ h₁ h₂ Y C (fr Y) hC (h.frame Y),
    fun γ hγ c hc => ⟨fun C => ?_, ?_⟩⟩
  · unfold lagTerm
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [← ratMul_ratMul, ratMul_eq_actO hc, om_rat_actO h.weil hγ h₁]
  · unfold lagTerm thetaIP
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [ratMul_one, om_rat_inv_apply h.weil hγ h₂, ratMul_eq_actO hc, mul_comm]

end GlobalTheory.RawLift.Move
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicModulusSqrtCharRefinedBlocksInStages
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages

namespace GlobalTheory.JacStages

theorem toLex_sigma_lt_iff_same {s : ℕ} {t : Fin s → ℕ} (a : Fin s) (b b' : Fin (t a)) :
    toLex (⟨a, b⟩ : Σ a, Fin (t a)) < toLex ⟨a, b'⟩ ↔ b < b' := by
  show Sigma.Lex (· < ·) (fun _ => (· < ·)) (⟨a, b⟩ : Σ a, Fin (t a)) ⟨a, b'⟩ ↔ _
  rw [Sigma.lex_iff]
  simp

theorem toLex_sigma_lt_iff_ne {s : ℕ} {t : Fin s → ℕ} (a a' : Fin s) (b : Fin (t a)) (b' : Fin (t a'))
    (h : a ≠ a') : toLex (⟨a, b⟩ : Σ a, Fin (t a)) < toLex ⟨a', b'⟩ ↔ a < a' := by
  show Sigma.Lex (· < ·) (fun _ => (· < ·)) (⟨a, b⟩ : Σ a, Fin (t a)) ⟨a', b'⟩ ↔ _
  rw [Sigma.lex_iff]
  simp [h]

theorem sum_toLex_gt {s : ℕ} {t : Fin s → ℕ} (f : (Σ a, Fin (t a)) → ℤ) (a : Fin s) (b : Fin (t a)) :
    ∑ q, (if toLex (⟨a, b⟩ : Σ a, Fin (t a)) < toLex q then f q else 0) =
      (∑ a' with a < a', ∑ b', f ⟨a', b'⟩) + ∑ b' with b < b', f ⟨a, b'⟩ := by
  rw [Fintype.sum_sigma, Fintype.sum_eq_add_sum_compl a, add_comm]
  congr 1
  · rw [Finset.sum_filter, Fintype.sum_eq_add_sum_compl a, if_neg (lt_irrefl a), zero_add]
    refine Finset.sum_congr rfl fun a' ha' => ?_
    have hne : a ≠ a' := fun h => by simp [h] at ha'
    by_cases hlt : a < a'
    · rw [if_pos hlt]
      exact Finset.sum_congr rfl fun b' _ => by rw [if_pos ((toLex_sigma_lt_iff_ne a a' b b' hne).2 hlt)]
    · rw [if_neg hlt]
      exact Finset.sum_eq_zero fun b' _ => by rw [if_neg (mt (toLex_sigma_lt_iff_ne a a' b b' hne).1 hlt)]
  · rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun b' _ => by simp only [toLex_sigma_lt_iff_same]

theorem sum_toLex_lt {s : ℕ} {t : Fin s → ℕ} (f : (Σ a, Fin (t a)) → ℤ) (a : Fin s) (b : Fin (t a)) :
    ∑ q, (if toLex q < toLex (⟨a, b⟩ : Σ a, Fin (t a)) then f q else 0) =
      (∑ a' with a' < a, ∑ b', f ⟨a', b'⟩) + ∑ b' with b' < b, f ⟨a, b'⟩ := by
  rw [Fintype.sum_sigma, Fintype.sum_eq_add_sum_compl a, add_comm]
  congr 1
  · rw [Finset.sum_filter, Fintype.sum_eq_add_sum_compl a, if_neg (lt_irrefl a), zero_add]
    refine Finset.sum_congr rfl fun a' ha' => ?_
    have hne : a' ≠ a := fun h => by simp [h] at ha'
    by_cases hlt : a' < a
    · rw [if_pos hlt]
      exact Finset.sum_congr rfl fun b' _ => by rw [if_pos ((toLex_sigma_lt_iff_ne a' a b' b hne).2 hlt)]
    · rw [if_neg hlt]
      exact Finset.sum_eq_zero fun b' _ => by rw [if_neg (mt (toLex_sigma_lt_iff_ne a' a b' b hne).1 hlt)]
  · rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun b' _ => by simp only [toLex_sigma_lt_iff_same]

end GlobalTheory.JacStages

namespace GlobalTheory.JacStages

theorem modExp_flat {s : ℕ} (d t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (c : Fin (∑ a, t a)) :
    modExp (fun c : Fin (∑ a, t a) => Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) c =
      modExp (fun a => Fin (d a)) (finSigmaFinEquiv.symm c).1 +
        modExp (fun b => Fin (d' (finSigmaFinEquiv.symm c).1 b)) (finSigmaFinEquiv.symm c).2 := by
  have hiff : ∀ x y : Fin (∑ a, t a),
      toLex (finSigmaFinEquiv.symm x : Σ a, Fin (t a)) < toLex (finSigmaFinEquiv.symm y) ↔ x < y :=
    fun x y => (finSigmaFinEquiv_symm_strictMono_lex s t).lt_iff_lt
  have hd : ∀ a, ∑ b, (d' a b : ℤ) = d a := fun a => by
    have := Fintype.card_congr (e' a)
    simp only [Fintype.card_sigma, Fintype.card_fin] at this
    exact_mod_cast this
  set F : (Σ a, Fin (t a)) → ℤ := fun q => (d' q.1 q.2 : ℤ) with hF
  have hgt : ∑ c' with c < c', (Fintype.card (Fin (d' (finSigmaFinEquiv.symm c').1 (finSigmaFinEquiv.symm c').2)) : ℤ) =
      ∑ q, if toLex (finSigmaFinEquiv.symm c) < toLex q then F q else 0 := by
    rw [Finset.sum_filter]
    exact Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun c' => by simp only [hiff, hF, Fintype.card_fin]
  have hlt : ∑ c' with c' < c, (Fintype.card (Fin (d' (finSigmaFinEquiv.symm c').1 (finSigmaFinEquiv.symm c').2)) : ℤ) =
      ∑ q, if toLex q < toLex (finSigmaFinEquiv.symm c) then F q else 0 := by
    rw [Finset.sum_filter]
    exact Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun c' => by simp only [hiff, hF, Fintype.card_fin]
  unfold modExp
  rw [hgt, hlt]
  generalize finSigmaFinEquiv.symm c = p
  obtain ⟨a, b⟩ := p
  rw [sum_toLex_gt, sum_toLex_lt]
  simp only [hF, Fintype.card_fin, hd]
  ring

end GlobalTheory.JacStages

namespace GlobalTheory.JacStages

theorem deltaHalf_flatHom (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (g : ∀ a b, GL (Fin (d' a b)) k) :
    deltaHalf k (fun c : Fin (∑ a, t a) => Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2))
        (flatHom (fun a b => GL (Fin (d' a b)) k) g) =
      deltaHalf k (fun a => Fin (d a)) (relEmbD k e' g) * relDeltaHalfD k (fun a b => Fin (d' a b)) g := by
  rw [deltaHalf_apply, deltaHalf_apply, relDeltaHalfD_apply]
  simp only [relEmbD_apply, det_leviEmb, map_prod, deltaHalf_apply, ← Finset.prod_mul_distrib,
    ← MonoidHom.mul_apply, ← absPow_add]
  rw [← Fintype.prod_sigma (fun p : Σ a, Fin (t a) => absPow k ((modExp (fun a => Fin (d a)) p.1 : ℂ) / 2 +
      (modExp (fun b => Fin (d' p.1 b)) p.2 : ℂ) / 2) (Matrix.GeneralLinearGroup.det (g p.1 p.2))),
    ← Equiv.prod_comp finSigmaFinEquiv.symm]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [flatHom_apply, modExp_flat d t d' e' c]
  congr 2
  push_cast
  ring

end GlobalTheory.JacStages
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatSpanOfLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RatSpanProof

theorem ratSpan_of_laws : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → RatSpan R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t
  exact GlobalTheory.HeckeClassSums.span_jV hL.models.HV hL.models.jV i t

end GlobalTheory.RatSpanProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalUnitaryLagrangianActionEqOfMemFrameUnipo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RallisCuspStab

open GlobalTheory.MixModel GlobalTheory.RallisCusp

variable {D : D7}

theorem inv_fix {n s : ℕ} (A B : Matrix (Fin n) (Fin n) (AE D)) (M : Matrix (Fin n) (Fin s) (AE D))
    (hBA : B * A = 1) (h : A ⬝ M = M) : B ⬝ M = M := by
  calc B ⬝ M = B ⬝ (A ⬝ M) := by rw [h]
    _ = M := by rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]

theorem inv_sub_one {n : ℕ} (A B : Matrix (Fin n) (Fin n) (AE D)) (hBA : B * A = 1) : B - 1 = -(B * (A - 1)) := by
  rw [Matrix.mul_sub, hBA, Matrix.mul_one, neg_sub]


set_option maxHeartbeats 1000000 in
theorem ni_prop (W : HSp D) {s : ℕ} (I : Matrix (Fin W.rank) (Fin s) D.host.E) (g : GA D W) (hg : g ∈ NI W I) :
    Formalism.L2.Theta.mt W g ⬝ I.map (incA D) = I.map (incA D) ∧
    ∀ x : Fin W.rank → D.host.E, (Iᴴ * W.gram) *ᵥ x = 0 →
      ∃ a : Fin s → AE D, (Formalism.L2.Theta.mt W g - 1) *ᵥ (fun i => incA D (x i)) = I.map (incA D) *ᵥ a := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    refine ⟨?_, fun x hx => hg.2.2 x hx⟩
    have h1 : (Formalism.L2.Theta.mt W g - 1) ⬝ I.map (incA D) = 0 := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    exact h1
  | one =>
    refine ⟨by rw [GlobalTheory.MixModel.mt_one, Matrix.one_mul], fun x _ => ⟨0, ?_⟩⟩
    rw [GlobalTheory.MixModel.mt_one, sub_self, Matrix.zero_mulVec, Matrix.mulVec_zero]
  | mul x y _ _ hx hy =>
    refine ⟨by rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, hy.1, hx.1], fun v hv => ?_⟩
    obtain ⟨a, ha⟩ := hx.2 v hv
    obtain ⟨b, hb⟩ := hy.2 v hv
    refine ⟨b + a, ?_⟩
    have e : Formalism.L2.Theta.mt W (x * y) - 1 =
        Formalism.L2.Theta.mt W x * (Formalism.L2.Theta.mt W y - 1) + (Formalism.L2.Theta.mt W x - 1) := by
      rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_sub, Matrix.mul_one, sub_add_sub_cancel]
    rw [e, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hb, ha, Matrix.mulVec_mulVec, hx.1, Matrix.mulVec_add]
  | inv x _ hx =>
    obtain ⟨hx1, hx2⟩ := hx
    have hinv := inv_fix _ _ _ (GlobalTheory.MixModel.mt_inv_mul W x) hx1
    refine ⟨hinv, fun v hv => ?_⟩
    obtain ⟨a, ha⟩ := hx2 v hv
    refine ⟨-a, ?_⟩
    rw [inv_sub_one _ _ (GlobalTheory.MixModel.mt_inv_mul W x), Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, hinv, Matrix.mulVec_neg]

theorem exists_leftInv {m s : ℕ} (I : Matrix (Fin m) (Fin s) D.host.E) (hI : LinearIndependent D.host.E I.transpose) :
    ∃ L : Matrix (Fin s) (Fin m) D.host.E, L * I = 1 := by
  have hB : Function.Injective I.mulVec := by
    rw [Matrix.mulVec_injective_iff]
    exact hI
  have hker : LinearMap.ker (Matrix.toLin' I) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y h
    exact hB (by simpa [Matrix.toLin'_apply] using h)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' I) hker
  exact ⟨LinearMap.toMatrix' g, by
    rw [← LinearMap.toMatrix'_toLin' I, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]⟩

theorem descend {m s : ℕ} (I : Matrix (Fin m) (Fin s) D.host.E) (hI : LinearIndependent D.host.E I.transpose)
    (v : Fin m → D.host.E) (a : Fin s → AE D) (h : (fun i => incA D (v i)) = I.map (incA D) *ᵥ a) :
    ∃ b : Fin s → D.host.E, v = I *ᵥ b := by
  obtain ⟨L, hL⟩ := exists_leftInv I hI
  refine ⟨L *ᵥ v, ?_⟩
  have ha : a = fun j => incA D ((L *ᵥ v) j) := by
    have h1 : L.map (incA D) *ᵥ (fun i => incA D (v i)) = a := by
      rw [h, Matrix.mulVec_mulVec, ← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    rw [← h1]
    funext j
    exact (RingHom.map_mulVec (incA D) L v j).symm
  funext i
  apply incA_injective
  have := congrFun h i
  rw [this, ha]
  exact (RingHom.map_mulVec (incA D) I (L *ᵥ v) i).symm

theorem fst_perp (W : HSp D) (Y : Lag W) {s : ℕ} (I : Matrix (Fin W.rank) (Fin s) D.host.E)
    (hY : Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _))
    (y : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) (hy : y ∈ Y.1) : (Iᴴ * W.gram) *ᵥ y.1 = 0 := by
  funext a
  have hcol : ((I.transpose a, 0) : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) ∈ Y.1 := by
    have h : I.transpose a ∈ Y.1.comap (LinearMap.inl D.host.E _ _) := hY ▸ Submodule.subset_span ⟨a, rfl⟩
    exact h
  have hiso := Y.2.2 _ hcol y hy
  simp only [star_zero, zero_dotProduct] at hiso
  rw [← Matrix.mulVec_mulVec]
  show _ = (0 : D.host.E)
  rw [← hiso]
  rfl

theorem lagAct_eq_of_mem_NI : ∀ (D : D7) (W : HSp D) (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E),
    IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) →
    ∀ n : GQ W, (n : GA D W) ∈ NI W I → GlobalTheory.RallisCusp.lagAct W n Y = Y := by
  intro D W Y s I hI hY n hn
  have hn' : ((n⁻¹ : GQ W) : GA D W) ∈ NI W I := by
    rw [InvMemClass.coe_inv]
    exact inv_mem hn
  obtain ⟨-, hP⟩ := ni_prop W I _ hn'
  have hc : Formalism.L2.Theta.mt W ((n⁻¹ : GQ W) : GA D W) - 1 = (gqMat W n⁻¹ - 1).map (incA D) := by
    rw [← rat_gqMat, ← rat_one, ← rat_sub]
    rfl
  have hle : Y.1 ≤ (lagAct W n Y).1 := by
    intro y hy
    rw [mem_lagAct]
    obtain ⟨a, ha⟩ := hP y.1 (fst_perp W Y I hY y hy)
    obtain ⟨b, hb⟩ := descend I hI.2.1 ((gqMat W n⁻¹ - 1) *ᵥ y.1) a (by
      rw [← ha, hc]
      funext i
      exact RingHom.map_mulVec (incA D) _ _ i)
    have hIb : ((I *ᵥ b, 0) : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) ∈ Y.1 := by
      have h : I *ᵥ b ∈ Submodule.span D.host.E (Set.range I.col) := by
        rw [← Matrix.range_mulVecLin]
        exact ⟨b, rfl⟩
      have h' : I *ᵥ b ∈ Y.1.comap (LinearMap.inl D.host.E _ _) := by
        rw [← hY]
        exact h
      exact h'
    have e : ((gqMat W n⁻¹ *ᵥ y.1, y.2) : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)) =
        y + (I *ᵥ b, 0) := by
      rw [← hb, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact Prod.ext (by simp) (by simp)
    rw [e]
    exact Y.1.add_mem hy hIb
  exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (by rw [Y.2.1, (lagAct W n Y).2.1])).symm

end GlobalTheory.RallisCuspStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLeStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y := by
  first | exact @GlobalTheory.LocGL.UnitaryOrder.add_one_le_of_precedes | exact GlobalTheory.LocGL.UnitaryOrder.add_one_le_of_precedes | (intros; apply GlobalTheory.LocGL.UnitaryOrder.add_one_le_of_precedes <;> assumption)
end

