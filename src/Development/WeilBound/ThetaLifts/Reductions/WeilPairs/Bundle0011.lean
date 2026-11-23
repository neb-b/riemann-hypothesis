module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0003
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEtaC
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0010
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0004
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0005
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilRepresentationHeisenberg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationOfLatticeVacua

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutEta
section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

theorem eta_prod (hB : B.IsGood σ) {η : (AEF F E)ˣ →* Circle} (h1 : IsHeckeCharF η) (h2 : ResEtaF η 1)
    (h3 : HasExp B.emb η (fun _ => 1)) (h4 : UnramInert σ η) (hlam : GoodNorm (sgOF σ) lam)
    (hsq : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQF σ q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) :
    ∃ ε, IsHalfF σ ε ∧ ∀ (x : E) (k : ℕ), x ≠ 0 → (k : ℚ) = |Algebra.norm ℚ x| → ∀ y : (AEF F E)ˣ,
      (y : AEF F E) = (ε + cAF σ ε) * incAF F E x + (1 - (ε + cAF σ ε)) →
        ∃ r : ℝ, 0 < r ∧ (η y : ℂ) * lam k * ∏ v, tauB B v x = r :=
  AutEtaA.exists_half_character_eta_product hB h1 h2 h3 h4 hlam hsq

end PositivityTheory.ThKW

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutReal
section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

theorem exists_inf (C : Ctx σ B JS JT ξ₀ θ ι) : ∃ oi, IsInfWeilF σ JS JT ξ₀ B.ψ oi ∧
    ∀ s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ, s * s = 1 → ((HMF JS JT ξ₀ (tauB B)) * s).PosDef → ∀ p,
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsVacF σ JS JT ξ₀ B.ψ ι s f →
        oi p f = GlobalTheory.RealWeil.dP s (mMF σ JS JT θ p) • f :=
  exists_inf_A C

theorem integral_gaussV {κ : Type} [Fintype κ] [DecidableEq κ] {H s g g' : Matrix κ κ ℂ} (hH : Hᴴ = H) (hs : s * s = 1)
    (hQ : (H * s).PosDef) (hg : gᴴ * H * g = H) (hc : s * g = g * s) (hi : g * g' = 1) (hd : (g - 1).det ≠ 0) :
    Integrable (gaussV H s g) volume ∧ GlobalTheory.RealWeil.dP s g' ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧
      (∫ v, gaussV H s g v) * (g - 1).det = r * (-s).det * (g.det * GlobalTheory.RealWeil.dP s g') :=
  integral_gaussV_B hH hs hQ hg hc hi hd

theorem det_mMF (C : Ctx σ B JS JT ξ₀ θ ι) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    (mMF σ JS JT θ (g⁻¹, h⁻¹)).det = ∏ v, tauB B v (b ⊗ₖ aᵀ).det ∧
      (mMF σ JS JT θ (g⁻¹, h⁻¹) - 1).det = ∏ v, tauB B v (b ⊗ₖ aᵀ - 1).det :=
  det_mMF_B C ha hb

end PositivityTheory.ThKW

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRep
section
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {ψ : AddChar (AF F) ℂ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)}

namespace LatC

theorem symplOHF_two (x y : WOF F E nS nT) : symplOHF σ JS JT ξ₀ x (2 • y) = symplOF σ JS JT ξ₀ x y := by
  rw [two_nsmul, GlobalTheory.HeisLineF.symplOHF_add_right, symplOHF_add_self]

theorem phase_two (hA : SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ)) (w : 𝓞 E) {u : XFF F E nS nT}
    (hu : u ∈ latF F E nS nT Λ) : phaseF σ JS JT ξ₀ ψ w (2 • u) = 1 := by
  have h : ψ (symplOF σ JS JT ξ₀ (intAF F w • ((2 • u : XFF F E nS nT) : WOF F E nS nT)) u) = 1 :=
    (hA _).1 ((latF F E nS nT Λ).smul_mem w (nsmul_mem hu 2)) u hu
  have h2 := AddChar.map_add_eq_mul ψ (-symplOF σ JS JT ξ₀ (intAF F w • ((2 • u : XFF F E nS nT) : WOF F E nS nT)) u)
    (symplOF σ JS JT ξ₀ (intAF F w • ((2 • u : XFF F E nS nT) : WOF F E nS nT)) u)
  rw [neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one] at h2
  rw [phaseF, h2, ← symplOHF_two]
  rfl

theorem smooth_theta (hg : GoodLat Λ) {hc : HeisClosedF σ JS JT ξ₀ ψ} {w : 𝓞 E}
    (H : IsHeis (sgOF σ) w (gamFF σ JS JT ξ₀ ψ) (opFF hc w)) (hA : SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ))
    (f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) :
    ∃ B : Submodule (𝓞 E) (XFF F E nS nT), idx (latF F E nS nT Λ) B ≠ 0 ∧
      ∀ a ∈ latF F E nS nT Λ, (∀ t ∈ B, gamFF σ JS JT ξ₀ ψ a t = 1) → opFF hc w a f = f := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  obtain ⟨U, hU, hf⟩ := IsThetaFunOF.level f.2
  obtain ⟨N, hN, hNU⟩ := lat_lev hg U hU
  have hN2 : 0 < 2 * N := by omega
  have hdiv : ∀ x : XFF F E nS nT, (2 * N) • (incAF F E ((2 * N : ℕ) : E)⁻¹ • x) = x := nsmul_inv_smul hN2
  refine ⟨(latF F E nS nT Λ).comap ((2 * N) • LinearMap.id), idx_ne_zero hg _
    (DistribSMul.toAddMonoidHom _ (incAF F E ((2 * N : ℕ) : E)⁻¹)) (continuous_const_smul (incAF F E ((2 * N : ℕ) : E)⁻¹))
    (fun l hl => fin_smul _ (lat_fin hl)) (fun b hb => ⟨(2 * N) • (b : WOF F E nS nT), hb, ?_⟩), fun a _ ha => ?_⟩
  · show incAF F E ((2 * N : ℕ) : E)⁻¹ • ((2 * N) • (b : WOF F E nS nT)) = b
    rw [smul_comm, nsmul_inv_smul hN2]
  obtain ⟨a', rfl⟩ : ∃ a', a = (2 * N) • a' := ⟨_, (hdiv a).symm⟩
  have ha' : a' ∈ latF F E nS nT Λ := (hA a').2 fun t ht => by
    rw [← hdiv t, H.nsmul_right, ← H.nsmul_left]
    refine ha _ ?_
    show (2 * N) • (incAF F E ((2 * N : ℕ) : E)⁻¹ • t) ∈ latF F E nS nT Λ
    rw [hdiv]
    exact ht
  apply Subtype.ext
  rw [coe_opFF, hf _ (by rw [XFF.coe_nsmul, mul_comm, mul_smul]; exact hNU _ (nsmul_mem ha' 2)) (XFF.fin _),
    mul_smul, phase_two hA w (nsmul_mem ha' N), one_smul]

end LatC

theorem latRep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E), GoodLat Λ → RatSD σ JS JT ξ₀ Λ →
      ∀ hc : HeisClosedF σ JS JT ξ₀ B.ψ, ∃ (w : 𝓞 E) (lam : ℕ →* ℂ)
        (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ Λ hg hsd hc
  have hσ := LatA.sig_sig hB
  obtain ⟨w, hw⟩ := exists_integral_trace_one σ B hB
  obtain ⟨lam, hlam, hsq⟩ := exists_good_norm_character σ B hB
  have H := isHeis_opFF hσ hS hT hξ hc hw
  have hA := LatC.lat_sd hσ hB.std hg hsd
  have hspan := _root_.GlobalTheory.FinWeil.span_translates_vacua H _ hA (LatC.smooth_theta hg H hA)
  have hidx : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0 := fun p => by
    refine LatC.idx_ne_zero hg _ (AddMonoidHom.mk' (actOF σ JS JT p.1 p.2) (actOF_add _ _))
      (LatC.continuous_act_right p.1 p.2) (fun l hl => actOF_mem_finSubF _ _ (lat_fin hl)) ?_
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  obtain ⟨Om, h1, h2⟩ := _root_.GlobalTheory.FinWeil.exists_weil_rep_of_vacua H lam hlam _ hA hspan (rhoFF σ JS JT) (LatA.gamFF_rhoFF hS) hidx
  refine ⟨w, lam, Om, hw, hA, hspan, hidx, h1, fun p => (h2 p).1, fun p => (h2 p).2, hlam, hsq, fun x => ?_,
    LatC.near hg, LatC.near' hg, lattice_stable_under_idempotents σ B hB Λ, lattice_index_prime_to_inert σ B hB JS JT Λ hidx⟩
  obtain ⟨M, hM, hx⟩ := lat_den hg (x : WOF F E nS nT) x.fin
  refine ⟨2 * M, by omega, fun l hl => ?_⟩
  have h3 : gamFF σ JS JT ξ₀ B.ψ x (M • l) = 1 := by
    rw [H.nsmul_right, ← H.nsmul_left]
    exact H.iso hA hx hl
  rw [mul_smul, LatC.symplOHF_two]
  exact h3

end PositivityTheory.ThKW

end
end

