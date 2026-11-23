module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsKilledHeisenbergAverageIsotropic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentMulNatPowOfMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductDatumThetaHasShapeAdjointPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DownLift.ProdShape

variable {D : D7}

theorem isSBHalf_sub_smul {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {f g : Mx D m n → ℂ}
    (hf : IsSBHalf e Λ f) (hg : IsSBHalf e Λ g) (c : ℂ) : IsSBHalf e Λ (f - c • g) := by
  obtain ⟨f1, k, hk, f2, f3⟩ := hf
  obtain ⟨g1, l, hl, g2, g3⟩ := hg
  have hne : ∀ t, (f - c • g) t ≠ 0 → f t ≠ 0 ∨ g t ≠ 0 := fun t ht => by
    by_contra h
    push_neg at h
    exact ht (by rw [Pi.sub_apply, Pi.smul_apply, h.1, h.2, smul_zero, sub_zero])
  have hh : ∀ (j : ℕ) (u : Mx D m n), IsHalf e u → IsHalf e (j • u) := fun j u hu => by
    rw [GlobalTheory.SplitScalar.isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  refine ⟨fun t ht => (hne t ht).elim (f1 t) (g1 t), k * l, mul_pos hk hl, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · have e1 : f (t + (k * l) • u) = f t := by
      rw [mul_smul]; exact f2 _ (nsmul_mem hu l) (hh l u hu') t
    have e2 : g (t + (k * l) • u) = g t := by
      rw [mul_comm, mul_smul]; exact g2 _ (nsmul_mem hu k) (hh k u hu') t
    rw [Pi.sub_apply, Pi.smul_apply, Pi.sub_apply, Pi.smul_apply, e1, e2]
  · rcases hne t ht with h | h
    · rw [mul_comm, mul_smul]; exact nsmul_mem (f3 t h) l
    · rw [mul_smul]; exact nsmul_mem (g3 t h) k

theorem isHalf_add_iff {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (t : Mx D m n) :
    IsHalf e (t + x) ↔ IsHalf e t := by
  rw [GlobalTheory.SplitScalar.isHalf_iff] at hx
  rw [GlobalTheory.SplitScalar.isHalf_iff, GlobalTheory.SplitScalar.isHalf_iff, smul_add, hx, add_left_inj]

theorem isSBHalf_transl {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {f : Mx D m n → ℂ}
    (hf : IsSBHalf e Λ f) {x : Mx D m n} (hx : IsHalf e x) (hx' : ∃ l : ℕ, 0 < l ∧ l • x ∈ Λ) :
    IsSBHalf e Λ fun t => f (t + x) := by
  obtain ⟨f1, k, hk, f2, f3⟩ := hf
  obtain ⟨l, hl, hlx⟩ := hx'
  have hh : ∀ (j : ℕ) (u : Mx D m n), IsHalf e u → IsHalf e (j • u) := fun j u hu => by
    rw [GlobalTheory.SplitScalar.isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  refine ⟨fun t ht => (isHalf_add_iff hx t).1 (f1 _ ht), k * l, mul_pos hk hl, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · beta_reduce
    rw [add_right_comm, mul_smul]
    exact f2 _ (nsmul_mem hu l) (hh l u hu') _
  · have h1 : (k * l) • (t + x) ∈ Λ := by rw [mul_comm, mul_smul]; exact nsmul_mem (f3 _ ht) l
    have h2 : (k * l) • x ∈ Λ := by rw [mul_smul]; exact nsmul_mem hlx k
    have := sub_mem h1 h2
    rwa [smul_add, add_sub_cancel_right] at this

theorem frMapAdj_conj_smul (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D))
    (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (e : AE D) (x : WO S T) :
    frMapAdj S T βS βT (cA D e • x) = toEAf D e • frMapAdj S T βS βT x := by
  have h : (((cA D e • x).map (toEAf D)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      toEAf D e • ((x.map (toEAf D)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ := Matrix.ext fun i j => by
    change GlobalTheory.AdelicLatMove.cF D (toEAf D (cA D e * x j i)) = toEAf D e * GlobalTheory.AdelicLatMove.cF D (toEAf D (x j i))
    rw [RingHom.map_mul, RingHom.map_mul, GlobalTheory.AdelicLatMove.toEAf_cA, GlobalTheory.PlaceVec.cF_cF_toEAf]
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.frMapAdj_eq, h, Matrix.mul_smul, Matrix.smul_mul]

section Red

variable {a b : ℕ} {p : Formalism.IndefR.Datum.EAf D} {M N : Matrix (Fin a) (Fin b) (Formalism.IndefR.Datum.EAf D)}

theorem isIntM_add_iff (hp : p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hM : p • M = 0) (hN : p • N = N) :
    IsIntM (M + N) ↔ IsIntM M ∧ IsIntM N := by
  refine ⟨fun h => ?_, fun h i j => add_mem (h.1 i j) (h.2 i j)⟩
  have h1 : p • (M + N) = N := by rw [smul_add, hM, hN, zero_add]
  have h2 : IsIntM N := fun i j => by
    rw [← h1]
    exact mul_mem hp (h i j)
  exact ⟨fun i j => (add_mem_cancel_right (h2 i j)).1 (h i j), h2⟩

theorem redM_add (PP : Pl D.host.E) (hM : IsIntM M) (hN : IsIntM N) : redM PP (M + N) = redM PP M + redM PP N := by
  funext i j
  have h2 : (M + N) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := add_mem (hM i j) (hN i j)
  rw [Matrix.add_apply]
  unfold redM
  rw [dite_eq_left h2, dite_eq_left (hM i j), dite_eq_left (hN i j), ← RingHom.map_add (f := _)]
  rfl

theorem redM_smul (PP : Pl D.host.E) (hp : p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hM : IsIntM M) :
    redM PP (p • M) = resS D.host.F PP ⟨p, hp⟩ • redM PP M := by
  funext i j
  have h2 : (p • M) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := mul_mem hp (hM i j)
  rw [Matrix.smul_apply, smul_eq_mul]
  unfold redM
  rw [dite_eq_left h2, dite_eq_left (hM i j), ← RingHom.map_mul]
  rfl

theorem redM_add_of_one (PP : Pl D.host.E) (hp : p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h1 : resS D.host.F PP ⟨p, hp⟩ = 1) (hM : p • M = 0) (hN : p • N = N) (iM : IsIntM M) (iN : IsIntM N) :
    redM PP (M + N) = redM PP N := by
  have h := redM_smul PP hp ((isIntM_add_iff hp hM hN).2 ⟨iM, iN⟩)
  rw [h1, one_smul, smul_add, hM, hN, zero_add] at h
  exact h.symm

theorem redM_add_of_zero (PP : Pl D.host.E) (hp : p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h0 : resS D.host.F PP ⟨p, hp⟩ = 0) (hN : p • N = N) (iM : IsIntM M) (iN : IsIntM N) :
    redM PP (M + N) = redM PP M := by
  have h := redM_smul PP hp iN
  rw [h0, zero_smul, hN] at h
  rw [redM_add PP iM iN, h, add_zero]

end Red

theorem hasShape_adjDat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (P : Finset (Pl D.host.E)) (e e₀ : AE D) (PP : Pl D.host.E), IsIdemSum e P → PP ∈ P → Formalism.L2.NTheta.IsIdemAt e₀ PP → ∀ ω₁ ω₂ : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)) → ℂ, (∀ y y', y PP = y' PP → ω₁ y = ω₁ y') → (∀ y y', (∀ PP' ∈ P, PP' ≠ PP → y PP' = y' PP') → ω₂ y = ω₂ y') → ∀ f₀ f : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latH S T ΛS ΛT) 1 f₀ (adjDat S T βS βT e fun y => ω₁ y * ω₂ y) f → HasShape ψ S T (cA D e₀) (adjDat S T βS βT e₀ ω₁) f := by
  intro D ψ S T hψ ΛS ΛT hS hT βS βT P e e₀ PP he hPP he₀ ω₁ ω₂ h₁ h₂ f₀ f hf₀ hf ℓ hℓ
  classical
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
  have hfT : f = Tm (adjDat S T βS βT e fun y => ω₁ y * ω₂ y) := hall Tm hTm
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hee : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hec : cA D e * cA D (cA D e) = 0 := by rw [← RingHom.map_mul, he.2, RingHom.map_zero]
  have hee₀ : cA D e * cA D e₀ = cA D e₀ := by rw [← RingHom.map_mul, GlobalTheory.DiagLiftFix.idemSum_mul he hPP he₀]
  have hSB : ∀ ω : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)) → ℂ,
      (∀ y y', (∀ PP ∈ P, y PP = y' PP) → ω y = ω y') →
      IsSBHalf (cA D e) (latH S T ΛS ΛT) (adjDat S T βS βT e ω) := fun ω hω =>
    GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice S ΛS hS)
      (GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hT) hinf (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)
      (GlobalTheory.PlaceVec.frMapAdj_up S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_down S T βS βT) P ω hω
  have s12 := hSB (fun y => ω₁ y * ω₂ y) fun y y' h => by
    rw [h₁ y y' (h PP hPP), h₂ y y' fun Q hQ _ => h Q hQ]
  have s2 := hSB ω₂ fun y y' h => h₂ y y' fun Q hQ _ => h Q hQ
  refine ⟨ℓ (Tm (adjDat S T βS βT e ω₂)), fun x hx => ?_⟩
  have hxs : cA D e₀ • x = x := (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx
  have hx' : IsHalf (cA D e) x := by
    rw [GlobalTheory.SplitScalar.isHalf_iff, ← hxs, smul_smul, hee₀]
  have st := isSBHalf_transl s12 hx' (GlobalTheory.PlaceVec.exists_nsmul_mem_latO
    (GlobalTheory.PlaceVec.selfDual_isFullLattice S ΛS hS) (GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hT) x
    (GlobalTheory.PlaceVec.half_infPart hinf ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hx')))
  obtain ⟨hp, hp1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e₀ PP he₀
  have hN : toEAf D e₀ • frMapAdj S T βS βT x = frMapAdj S T βS βT x := by
    rw [← frMapAdj_conj_smul, hxs]
  have key := _root_.GlobalTheory.DownLift.SplitCoef.form_placeModel_eq_zero_of_vanish D ψ S T hψ ΛS ΛT hS hT (cA D e₀) (cA D e) (GlobalTheory.SplitScalar.isSplitIdem_conj he₀.1)
    hee hec hinf hee₀ f₀ Tm hf₀ hTm ℓ hℓ _ (isSBHalf_sub_smul st s2 (adjDat S T βS βT e₀ ω₁ x)) fun t ht => by
      have hz : frMapAdj S T βS βT 0 = 0 :=
        (AddMonoidHom.mk' (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)).map_zero
      have hM : toEAf D e₀ • frMapAdj S T βS βT t = 0 := by
        rw [← frMapAdj_conj_smul, ht, hz]
      have hI := isIntM_add_iff hp hM hN
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_zero]
      unfold adjDat
      rw [GlobalTheory.PlaceVec.frMapAdj_add]
      by_cases c1 : IsIntM (frMapAdj S T βS βT x)
      · by_cases c2 : IsHalf (cA D e) t ∧ IsIntM (frMapAdj S T βS βT t)
        · rw [if_pos ⟨(isHalf_add_iff hx' t).2 c2.1, hI.2 ⟨c2.2, c1⟩⟩, if_pos ⟨hx, c1⟩, if_pos c2]
          beta_reduce
          rw [h₁ _ (fun Q => redM Q (frMapAdj S T βS βT x)) (redM_add_of_one PP hp hp1 hM hN c2.2 c1),
            h₂ _ (fun Q => redM Q (frMapAdj S T βS βT t)) fun Q _ hQ =>
              redM_add_of_zero Q hp (GlobalTheory.TameProd.resS_idem_eq_zero he₀ hQ.symm hp) hN c2.2 c1]
        · rw [if_neg c2, if_neg fun h => c2 ⟨(isHalf_add_iff hx' t).1 h.1, (hI.1 h.2).1⟩, mul_zero]
      · rw [if_neg fun h => c1 (hI.1 h.2).2, if_neg fun h => c1 h.2, zero_mul]
  rw [map_sub, map_smul, hTm.trans _ s12 x hx', ← hfT, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at key
  rw [key, mul_comm]

end GlobalTheory.DownLift.ProdShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceChartFiniteAdeleTensorLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChartLevels

theorem linIndep_rows_iff_map {k₁ k₂ : Type} [Field k₁] [Field k₂] (ι : k₁ →+* k₂) {m n : ℕ}
    (y : Matrix (Fin m) (Fin n) k₁) :
    LinearIndependent k₁ y.row ↔ LinearIndependent k₂ (y.map ι).row := by
  have key : ∀ {k : Type} [Field k] (y : Matrix (Fin m) (Fin n) k),
      LinearIndependent k y.row ↔ ∀ c : Fin m → k, c ᵥ* y = 0 → c = 0 := by
    intro k _ y
    rw [Fintype.linearIndependent_iff]
    have h : ∀ c : Fin m → k, ∑ i, c i • y.row i = c ᵥ* y := fun c => by
      ext j
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    simp only [h]
    exact ⟨fun H c hc => funext (H c hc), fun H c hc i => congrFun (H c hc) i⟩
  have inv : ∀ {k : Type} [Field k] (y : Matrix (Fin m) (Fin n) k),
      LinearIndependent k y.row → ∃ B : Matrix (Fin n) (Fin m) k, y * B = 1 := by
    intro k _ y hy
    rw [key] at hy
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.vecMulLinear y)
      (LinearMap.ker_eq_bot.2 fun a b hab => sub_eq_zero.1 (hy _ (by
        rw [Matrix.sub_vecMul]
        exact sub_eq_zero.2 hab)))
    refine ⟨(LinearMap.toMatrix' g)ᵀ, ?_⟩
    have hc : ∀ c : Fin m → k, c ᵥ* (y * (LinearMap.toMatrix' g)ᵀ) = c := fun c => by
      rw [← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
      exact congrArg (fun f => f c) hg
    refine Matrix.ext fun i j => ?_
    have := congrFun (hc (Pi.single i 1)) j
    rw [Matrix.single_one_vecMul] at this
    rw [Matrix.row_apply] at this
    rw [this, Matrix.one_apply, Pi.single_apply]
    simp only [eq_comm]
  constructor
  · intro hy
    obtain ⟨B, hB⟩ := inv y hy
    rw [key]
    intro c hc
    have : c ᵥ* ((y.map ι) * B.map ι) = c := by
      rw [← Matrix.map_mul, hB, Matrix.map_one _ ι.map_zero ι.map_one, Matrix.vecMul_one]
    rw [← Matrix.vecMul_vecMul, hc, Matrix.zero_vecMul] at this
    exact this.symm
  · intro hy
    rw [key] at hy ⊢
    intro c hc
    have h1 := hy (ι ∘ c) (funext fun j => by
      rw [← RingHom.map_vecMul, hc]
      simp)
    funext i
    exact ι.injective ((congrFun h1 i).trans ι.map_zero.symm)

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem residue_eq_zero_iff (x : GlobalTheory.SplitHecke.Ov D v) :
    IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v) x = 0 ↔ Valued.v (x : Fv D.host.F v) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hx : Valued.v (x : Fv D.host.F v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2
  constructor
  · intro hnu
    refine lt_of_le_of_ne hx fun h1 => hnu ?_
    have h0 : (x : Fv D.host.F v) ≠ 0 := fun h => by
      rw [h, map_zero] at h1
      exact zero_ne_one h1
    have hmem : (x : Fv D.host.F v)⁻¹ ∈ v.adicCompletionIntegers D.host.F :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, h1, inv_one])
    refine IsUnit.of_mul_eq_one (a := x) ⟨_, hmem⟩ (Subtype.ext ?_)
    show (x : Fv D.host.F v) * (x : Fv D.host.F v)⁻¹ = 1
    exact mul_inv_cancel₀ h0
  · intro hlt hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h2 := congrArg (fun t : GlobalTheory.SplitHecke.Ov D v => Valued.v (t : Fv D.host.F v)) hw
    have hw1 : Valued.v (w : Fv D.host.F v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 w.2
    simp only [MulMemClass.coe_mul, map_mul, OneMemClass.coe_one, map_one] at h2
    have : Valued.v (x : Fv D.host.F v) * Valued.v (w : Fv D.host.F v) < 1 :=
      (mul_le_of_le_one_right' hw1).trans_lt hlt
    rw [h2] at this
    exact lt_irrefl _ this

theorem resS_surjective (PP : Pl D.host.E) : Function.Surjective (resS D.host.F PP) := by
  rw [resS, RingHom.coe_comp]
  exact (RingEquiv.surjective _).comp Ideal.Quotient.mk_surjective

end GlobalTheory.ChartLevels

namespace GlobalTheory.ChartLevels

theorem prim_map_eq {k₁ k₂ : Type} [Field k₁] [Field k₂] (ι : k₁ →+* k₂) {m n : ℕ}
    (y : Matrix (Fin m) (Fin n) k₁) : prim (y.map ι) = prim y := by
  unfold prim
  by_cases h : LinearIndependent k₁ y.row
  · rw [if_pos h, if_pos ((linIndep_rows_iff_map ι y).1 h)]
  · rw [if_neg h, if_neg (mt (linIndep_rows_iff_map ι y).2 h)]

theorem gl_map_inv_val {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (β : GL (Fin n) R) :
    ((Matrix.GeneralLinearGroup.map f β)⁻¹).1 = (β⁻¹).1.map f := by
  rw [← map_inv]
  rfl

end GlobalTheory.ChartLevels

namespace GlobalTheory.ChartLevels

theorem frame_of_baseFrame {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (φ : Datum.EAf D →+* Fv D.host.F v) (hφ : ∀ a, φ (toEAf D a) = π a)
    (hint : ∀ N : Datum.EAf D, toEAf D e * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) (φ N))
    (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hβ : Lev.IsBaseFrame V β Λ 1) : GlobalTheory.SplitHecke.Frame V e π (Matrix.GeneralLinearGroup.map φ β) := by
  intro y
  have hL := (GlobalTheory.FinAdIdent.lamHat_good hβ (f := 1) ⟨mul_one 1, 1, by simp⟩).2
  have hL' : ∀ x, x ∈ Formalism.L2.NTheta.LamHat V ↔ (fun a => Lev.swapAE D (x a)) ∈ Formalism.L2.Herm.hatL Λ :=
    fun x => by simpa only [one_smul, one_mul] using hL x
  refine (hL' _).trans ((hβ.1 _).trans (forall_congr' fun i => ?_))
  have e2 : (fun a => Lev.swapAE D (finPart D (e * y a))) = toEAf D e • (fun a => toEAf D (y a)) := by
    funext a
    rw [Pi.smul_apply, smul_eq_mul, ← RingHom.map_mul]
    rfl
  have e4 : (φ ∘ fun a => toEAf D (y a)) = fun k => π (y k) := funext fun k => hφ (y k)
  rw [e2, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hint, RingHom.map_mulVec, e4, gl_map_inv_val]

end GlobalTheory.ChartLevels

namespace GlobalTheory.ChartLevels

theorem chart_levels : ∀ (D : D7) (e : AE D) (P : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsIdemAt e P → GlobalTheory.SplitHecke.Chart e v π → ∃ φ : Datum.EAf D →+* Fv D.host.F v, (∀ a, φ (toEAf D a) = π a) ∧ (∀ N : Datum.EAf D, toEAf D e * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) (φ N)) ∧ (∀ (m n : ℕ) (N : Matrix (Fin m) (Fin n) (Datum.EAf D)), IsIntM N → ∀ z : Matrix (Fin m) (Fin n) (GlobalTheory.SplitHecke.Ov D v), z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) = N.map φ → prim (redM P N) = prim (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)))) ∧ ∀ (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Lev.IsBaseFrame V β Λ 1 → GlobalTheory.SplitHecke.Frame V e π (Matrix.GeneralLinearGroup.map φ β) := by
  intro D e P v π he hπ
  obtain ⟨φ, hφ, hres⟩ := GlobalTheory.ThetaSupport.exists_chart_levels he hπ
  obtain ⟨hi, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e P he
  have hπe : π e = 1 := hπ.map_e he.1.1
  have hint : ∀ N : Datum.EAf D, toEAf D e * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) (φ N) := by
    intro N
    obtain ⟨a, rfl⟩ := GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) N
    rw [hφ, ← (hπ.2.2.2 a), ← RingHom.map_mul]
    exact ⟨GlobalTheory.PlaceDatum.finPart_mem_of_toEAf, GlobalTheory.IdemRes.toEAf_mem_of_finPart⟩
  refine ⟨φ, hφ, hint, ?_, ?_⟩
  · have hR : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, φ s ∈ v.adicCompletionIntegers D.host.F := fun s =>
      GlobalTheory.SplitHecke.isInt_Ov.1 ((hint s).1 (mul_mem hi s.2))
    let φR : Formalism.L2.Herm.intAf D.host.F D.host.E →+* GlobalTheory.SplitHecke.Ov D v :=
      (φ.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).codRestrict (v.adicCompletionIntegers D.host.F) hR
    let ρ : Formalism.L2.Herm.intAf D.host.F D.host.E →+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) :=
      (IsLocalRing.residue _).comp φR
    have hker : RingHom.ker (resS D.host.F P) ≤ RingHom.ker ρ := by
      intro s hs
      rw [RingHom.mem_ker] at hs ⊢
      exact (residue_eq_zero_iff (φR s)).2 (hres s hs)
    let ι : kP P →+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v) :=
      (resS D.host.F P).liftOfRightInverse _ (Function.rightInverse_surjInv (resS_surjective P)) ⟨ρ, hker⟩
    have hι : ∀ s, ι (resS D.host.F P s) = ρ s := fun s =>
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ s
    intro m n N hN z hz
    have e1 : z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) = (redM P N).map ι := by
      ext i j
      have hzij : z i j = φR ⟨N i j, hN i j⟩ := Subtype.ext (congrFun (congrFun hz i) j)
      simp only [Matrix.map_apply, redM, dif_pos (hN i j), hι, hzij]
      rfl
    rw [e1]
    exact (prim_map_eq ι _).symm
  · exact frame_of_baseFrame φ hφ hint

end GlobalTheory.ChartLevels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaCoefficientIsSchwartzBruhatUniformSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.DownLift.SplitCoef

variable {D : D7}

theorem symplO_nsmul_left_eq (S T : HSp D) (k : ℕ) (l x : WO S T) :
    symplO S T (k • l) x = symplO S T l (k • x) := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, GlobalTheory.PlaceModel.symplO_zero_left, GlobalTheory.PlaceModel.symplO_zero_right]
  | succ n ih => rw [succ_nsmul, succ_nsmul, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right, ih]

theorem coef_isSBHalf_uniform : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∃ k : ℕ, 0 < k ∧ (∀ u ∈ latH S T ΛS ΛT, IsHalf a u ∨ IsHalf (cA D a) u → heisO ψ S T (k • u) f = f) ∧ ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) ≠ 0 → k • x ∈ latH S T ΛS ΛT) ∧ (∀ ℓ, InvForm ψ S T a ℓ → IsSBHalf a (latH S T ΛS ΛT) (coef ψ S T a ℓ f)) ∧ ∃ X : Finset (WO S T), (∀ x ∈ X, IsHalf a x) ∧ ∀ x, IsHalf a x → (∀ ℓ, InvForm ψ S T a ℓ → ℓ (heisO ψ S T x f) = 0) ∨ ∃ x₁ ∈ X, heisO ψ S T x f = heisO ψ S T x₁ f := by
  intro D ψ S T hψ ΛS ΛT hS hT a ha f hf
  classical
  have ha' := GlobalTheory.SplitScalar.isSplitIdem_conj ha
  have hd := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  have hstc : ∀ u ∈ latH S T ΛS ΛT, cA D a • u ∈ latH S T ΛS ΛT := fun u hu =>
    GlobalTheory.SplitScalar.idem_smul_mem ha'.1 u hu
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨k, hk, hkU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).1 U hU
  have hinv : ∀ u ∈ latH S T ΛS ΛT, heisO ψ S T (k • u) f = f := fun u hu =>
    hUf _ (hkU u hu) (GlobalTheory.SplitScalar.latO_fin ((latH S T ΛS ΛT).nsmul_mem hu k))
  have hsupp : ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) ≠ 0 → k • x ∈ latH S T ΛS ΛT := by
    intro ℓ hℓ x hx hne
    by_contra hn
    obtain ⟨l, hl, hlh, hlne⟩ := GlobalTheory.SplitScalar.exists_dual_half ha hd hstc
      (GlobalTheory.SplitScalar.isHalf_nsmul hx k) hn
    have h1 := hℓ (k • l) (GlobalTheory.SplitScalar.isHalf_nsmul hlh k) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf x)
    rw [GlobalTheory.SplitScalar.heisO_comm, hinv l hl, map_smul, smul_eq_mul, symplO_nsmul_left_eq] at h1
    apply hlne
    have h2 : (ψ (symplO S T l (k • x)) - 1) * ℓ (heisO ψ S T x f) = 0 := by
      rw [sub_mul, h1, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hne)
  have hcoef : ∀ ℓ, InvForm ψ S T a ℓ → IsSBHalf a (latH S T ΛS ΛT) (coef ψ S T a ℓ f) := by
    intro ℓ hℓ
    refine ⟨fun t ht => ?_, k, hk, fun u hu huh t => ?_, fun t ht => ?_⟩
    · by_contra hn
      exact ht (by simp only [coef, if_neg hn])
    · by_cases htt : IsHalf a t
      · have h2 : IsHalf a (t + k • u) := GlobalTheory.SplitScalar.isHalf_add htt (GlobalTheory.SplitScalar.isHalf_nsmul huh k)
        simp only [coef, if_pos htt, if_pos h2]
        rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T
          (GlobalTheory.SplitScalar.half_orth ha htt (GlobalTheory.SplitScalar.isHalf_nsmul huh k)), hinv u hu]
      · have h2 : ¬ IsHalf a (t + k • u) := fun h => htt (by
          have := GlobalTheory.SplitScalar.isHalf_sub h (GlobalTheory.SplitScalar.isHalf_nsmul huh k)
          rwa [add_sub_cancel_right] at this)
        simp only [coef, if_neg htt, if_neg h2]
    · have htt : IsHalf a t := by
        by_contra hn
        exact ht (by simp only [coef, if_neg hn])
      refine hsupp ℓ hℓ t htt ?_
      simpa only [coef, if_pos htt] using ht
  obtain ⟨R, hR, hRm⟩ := GlobalTheory.DiagLiftFix.half_finite_mod (S := S) (T := T) hS.1.fg hT.1.fg ha.1 (k * k)
    (Nat.mul_pos hk hk)
  have tf : Function.Injective fun t : WO S T => k • t := fun x y hxy => by
    rw [← GlobalTheory.PlaceModel.inv_smul_nsmul S T hk x, ← GlobalTheory.PlaceModel.inv_smul_nsmul S T hk y]
    exact congrArg _ hxy
  have hP : ((fun t : WO S T => k • t) ⁻¹' R).Finite := hR.preimage tf.injOn
  refine ⟨⟨k, hk, fun u hu _ => hinv u hu, hsupp⟩, hcoef, hP.toFinset.filter (fun x => IsHalf a x),
    fun x hx => (Finset.mem_filter.1 hx).2, fun x hx => ?_⟩
  by_cases hkx : k • x ∈ latH S T ΛS ΛT
  · right
    obtain ⟨r, hr, u, hu, e⟩ := hRm (k • x)
      ⟨hkx, (GlobalTheory.PlaceModel.isHalf_iff S T).1 (GlobalTheory.SplitScalar.isHalf_nsmul hx k)⟩
    have huh : IsHalf a u := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu.2
    have hxu : IsHalf a (x - k • u) := GlobalTheory.SplitScalar.isHalf_sub hx (GlobalTheory.SplitScalar.isHalf_nsmul huh k)
    refine ⟨x - k • u, Finset.mem_filter.2 ⟨hP.mem_toFinset.2 ?_, hxu⟩, ?_⟩
    · show k • (x - k • u) ∈ R
      rwa [smul_sub, e, smul_smul, add_sub_cancel_right]
    · conv_lhs => rw [show x = (x - k • u) + k • u by abel]
      rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T
        (GlobalTheory.SplitScalar.half_orth ha hxu (GlobalTheory.SplitScalar.isHalf_nsmul huh k)), hinv u hu.1]
  · left
    intro ℓ hℓ
    by_contra hne
    exact hkx (hsupp ℓ hℓ x hx hne)

end GlobalTheory.DownLift.SplitCoef

end
end

