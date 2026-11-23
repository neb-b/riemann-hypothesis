module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThCLeftStab
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CocRZeroLeft
section
open NumberField IsDedekindDomain Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.SemiTwist

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}
  (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ)

def cocR (x y : Formalism.L2.Col.HomE E a b) : ℝ :=
  (Real.sqrt d * (HV (ι := ι) sc (embH emb δ x) (embH emb δ y)).re +
    Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2

theorem cocR_add_left (x y z : Formalism.L2.Col.HomE E a b) :
    cocR emb δ d sc (x + y) z = cocR (ι := ι) emb δ d sc x z + cocR emb δ d sc y z := by
  simp only [cocR, Formalism.L2.Th1.H.altE, map_add (f := _), LinearMap.add_apply, Complex.add_re, Complex.add_im]; ring

theorem cocR_zero_left (z : Formalism.L2.Col.HomE E a b) : cocR (ι := ι) emb δ d sc 0 z = 0 := by
  simp [cocR, Formalism.L2.Th1.H.altE]

theorem hv_embH_smul (hconj : ∀ τ x, emb τ (star x) = starRingEnd ℂ (emb τ x)) (r : E) (x y : Formalism.L2.Col.HomE E a b) :
    HV (ι := ι) sc (embH emb δ (r • x)) (embH emb δ y) = HV sc (embH emb δ x) (embH emb δ (star r • y)) := by
  simp only [HV, LinearMap.mk₂'ₛₗ_apply, embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, map_mul, hconj, Complex.conj_conj]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem cocR_smul (hconj : ∀ τ x, emb τ (star x) = starRingEnd ℂ (emb τ x)) (r : E) (x y : Formalism.L2.Col.HomE E a b) :
    cocR (ι := ι) emb δ d sc (r • x) y = cocR emb δ d sc x (star r • y) := by
  simp only [cocR, Formalism.L2.Th1.H.altE, hv_embH_smul emb δ sc hconj]

theorem semiChar_twO : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → 0 < c → (∀ Q, e (Formalism.L2.Col.conjPrime₂ Q) = -e Q) → (∀ Q, e Q = 1 ∨ e Q = 0 ∨ e Q = -1) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ (twist₂ M c e)) (alV d sc) := by
  intro E _ _ _ ι _ _ a b emb δ d sc M c e _ hconj hc he _ _ hM
  have hH : Formalism.L2.Th1.H.IsHerm (HV (ι := ι) (a := a) (b := b) sc) := fun x y => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Formalism.L2.Ker.HV, map_sum, mul_comm]
  have h0 : ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, cocR emb δ d sc x y = n := fun x hx y hy =>
    (GlobalTheory.KerLaw.semi_iff hH (Real.sqrt d) _).1 hM (embH emb δ x) ⟨x, hx, rfl⟩ (embH emb δ y) ⟨y, hy, rfl⟩
  refine (GlobalTheory.KerLaw.semi_iff hH (Real.sqrt d) _).2 ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  change ∃ n : ℤ, cocR emb δ d sc x y = n
  let I : Ideal (𝓞 E) :=
    { carrier := {r | ∀ s : 𝓞 E, ∃ n : ℤ, cocR emb δ d sc ((s * r) • x) y = n}
      zero_mem' := fun s => ⟨0, by simp [cocR_zero_left]⟩
      add_mem' := fun {r r'} hr hr' s => by
        obtain ⟨n, hn⟩ := hr s
        obtain ⟨m, hm⟩ := hr' s
        exact ⟨n + m, by rw [mul_add, add_smul, cocR_add_left, hn, hm, Int.cast_add]⟩
      smul_mem' := fun t r hr s => by
        rw [smul_eq_mul, ← mul_assoc]
        exact hr _ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 E) :=
      ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
    obtain ⟨u, hu, hx⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 ((GlobalTheory.KerLaw.mem_tw _ _ _ _).1 hx Q)
    obtain ⟨v, hv, hy⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 ((GlobalTheory.KerLaw.mem_tw _ _ _ _).1 hy (Formalism.L2.Col.conjPrime₂ Q))
    rw [he, zpow_neg, inv_inv] at hy
    have hmem : u * Formalism.L2.Col.cO E v ∈ I := by
      intro s
      obtain ⟨n, hn⟩ := h0 _ (Submodule.smul_mem _ s hx) _ hy
      refine ⟨n, ?_⟩
      rw [← hn]
      have e1 : (s * (u * Formalism.L2.Col.cO E v)) • x =
          (star (algebraMap (𝓞 E) E v) * (c : E) ^ e Q) • (s • u • ((c : E) ^ e Q)⁻¹ • x) := by
        rw [← algebraMap_smul E s, ← algebraMap_smul E u, ← algebraMap_smul E (s * _), smul_smul, smul_smul, smul_smul,
          map_mul, map_mul, Formalism.L2.Col.algebraMap_cO]
        congr 1
        have hk : (c : E) ^ e Q ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 hc.ne')
        field_simp
      rw [e1, cocR_smul emb δ d sc hconj, star_mul', star_star, star_zpow₀, star_natCast, mul_smul, algebraMap_smul]
    rcases hm.isPrime.mem_or_mem (hle hmem) with h' | h'
    · exact hu h'
    · exact hv h'
  have : (1 : 𝓞 E) ∈ I := hI ▸ Submodule.mem_top
  simpa using this 1

end GlobalTheory.SemiTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColMatchAll
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.Core.Ht2

theorem colMatchAll : ColMatchAll := by
  intro B X I h hX l Z hJ u a
  have KO := GlobalTheory.Mem.Col2.KerRat.kernelsOver_of_family I l Z h hJ (GlobalTheory.Core.Ht2.family_laws I h hX l Z) u a
  refine ⟨?_, fun c x φ F z hx hF => ?_⟩
  · obtain ⟨⟨b⟩, hb⟩ := KO.period
    obtain ⟨hY, hK, hF, -, -⟩ := hb b
    exact ⟨⟨b, hY, hK, hF⟩⟩
  · obtain ⟨hY, hK, hF', hM, heq⟩ := KO.period.2 c.b
    have ex : x = GlobalTheory.Mem.Col2.KerRat.colForm I l h u a φ := Subtype.ext (funext hx)
    have eF : F = GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a z := by
      apply Subtype.ext; funext t p; exact hF p
    subst ex; subst eF
    rw [heq φ z]
    rfl

end GlobalTheory.Core.Ht2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeightDoublingEmbeddingLePowMulHeights
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Cont.HeightIo

theorem height_io_le_mul {D : D7} (V : HSp D) (g₁ g₂ : GA D V) :
    GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂ := by
  have h := GlobalTheory.BlockHeight.heightGL_blk_le D.host.F finSumFinEquiv
    (Formalism.L2.Theta.matHom (dblSp V) (io V (g₁, g₂))) (Formalism.L2.Theta.matHom V g₁) (Formalism.L2.Theta.matHom V g₂) rfl rfl
  show ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ) ≤
    ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ) * ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

theorem height_io_bound : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (c : ℕ), ∀ g₁ g₂ : GA D V,
    GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c := by
  intro D V
  refine ⟨1, 1, fun g₁ g₂ => ?_⟩
  rw [one_mul, pow_one]
  exact height_io_le_mul V g₁ g₂

end GlobalTheory.Cont.HeightIo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatSchwartzTargetUnipotentConjBesselCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB.UnipAct

variable {D : D7}

theorem levi_mem_flag {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    d.levi u ∈ flagN d :=
  d.levi_mem_NFlag hu

theorem psiUni_mul_of_mem (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    {u v : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) (hv : v ∈ UX D ρ) : psiUni ψ (u * v) = psiUni ψ u * psiUni ψ v := by
  have h : ∀ a, psiFlag ψ d (d.levi a) = psiUni ψ a := fun a => by
    have := psiFlag_levi_mul ψ d a (one_mem (stabX d))
    rwa [mul_one] at this
  rw [← h, ← h, ← h, map_mul, psiFlag_mul d ψ (levi_mem_flag d hu) (levi_mem_flag d hv)]

theorem flatFB_flagN : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (Ψ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Ψ → ∀ n ∈ flagN B.d, flatFB s (s.om (1, n) Ψ) = star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • flatFB s Ψ := by
  intro D hD ψ σ J B s Ψ hΨ n hn
  obtain ⟨γ, hγ, hnγ⟩ := ((_root_.GlobalTheory.Unf.FB.besselGroup_action_fourierBesselBasePoint D σ B).1 n).1 (Subgroup.mem_sup_left hn)
  have hψ : psiBes ψ B.d 1 (vecB B.o B.ζ) n = psiUni ψ γ :=
    (GlobalTheory.T.flagUnipotentRadical_surjects_unitriangular_characters_agree D σ B).2 ψ n hn 1 ⟨γ, hγ⟩ (by rw [map_one, mul_one]; exact hnγ)
  have h1 : mt B.V n⁻¹ ⬝ (x0 B ⬝ γ.1) = x0 B := by
    rw [← hnγ, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  have hev : ∀ M : Mx D B.V.rank (σ + 1), evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n) Ψ) M 0 =
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (mt B.V n⁻¹ ⬝ M) 0 := by
    intro M
    have := _root_.GlobalTheory.Unf.FB.evalAt_zero_equivariant D hD ψ σ J B s Ψ hΨ 1 n hn 1 M
    simp only [map_one, mul_one] at this
    rw [this, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one, Module.End.one_apply]
  have : BorelSpace (UX D (σ + 1)) := ⟨rfl⟩
  have := s.vU.unit.1
  funext w
  simp only [flatFB, flatLast, flatAt, flatFun, Pi.smul_apply, smul_eq_mul, hev]
  rw [← integral_const_mul, ← integral_mul_left_eq_self _ (⟨γ, hγ⟩ : UX D (σ + 1))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hm : mt B.V n⁻¹ ⬝ (x0 B ⬝ ((⟨γ, hγ⟩ * u : UX D (σ + 1)) : GL (Fin (σ + 1)) (AE D)).1) = x0 B ⬝ u.1.1 := by
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (x0 B), h1]
  change star (psiUni ψ ((⟨γ, hγ⟩ * u : UX D (σ + 1)) : GL (Fin (σ + 1)) (AE D))) *
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (mt B.V n⁻¹ ⬝ (x0 B ⬝ ((⟨γ, hγ⟩ * u : UX D (σ + 1)) : GL (Fin (σ + 1)) (AE D)).1)) 0 w = _
  rw [hm, Subgroup.coe_mul, psiUni_mul_of_mem ψ J.d hγ u.2, star_mul', hψ, mul_assoc]
  rfl

end GlobalTheory.Unf.FB.UnipAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlobalDoublingZetaFormSelfDualLatticeTransfer
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.GlobMove

variable {D : D7}

theorem rmul_one' {V : HSp D} (q : AutomorphicL2Unitary.Quot (GQ V)) : AutomorphicL2Unitary.rmul (GQ V) 1 q = q := by
  induction q using Quotient.inductionOn' with
  | h x => exact congrArg _ (mul_one x)

def rmulEquiv {V : HSp D} (y : GA D V) : AutomorphicL2Unitary.Quot (GQ V) ≃ᵐ AutomorphicL2Unitary.Quot (GQ V) where
  toFun := AutomorphicL2Unitary.rmul (GQ V) y
  invFun := AutomorphicL2Unitary.rmul (GQ V) y⁻¹
  left_inv q := by rw [← AutomorphicL2Unitary.rmul_mul, mul_inv_cancel, rmul_one']
  right_inv q := by rw [← AutomorphicL2Unitary.rmul_mul, inv_mul_cancel, rmul_one']
  measurable_toFun := AutomorphicL2Unitary.measurable_rmul y
  measurable_invFun := AutomorphicL2Unitary.measurable_rmul y⁻¹

theorem descend_mul_right {V : HSp D} {φ : GA D V → ℂ} (hφ : AutomorphicL2Unitary.LeftInv (GQ V) φ) (y : GA D V) :
    AutomorphicL2Unitary.descend (GQ V) (fun x => φ (x * y)) = AutomorphicL2Unitary.descend (GQ V) φ ∘ AutomorphicL2Unitary.rmul (GQ V) y := by
  funext q
  have e : AutomorphicL2Unitary.rmul (GQ V) y q = AutomorphicL2Unitary.mk (GQ V) (q.out * y) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  simp only [Function.comp, e, hφ.descend_mk]
  rfl

section Quot

variable {V : HSp D} (m : Measure (GA D V)) [m.IsHaarMeasure] [m.IsMulRightInvariant]

theorem integral_descend_mul_right {φ : GA D V → ℂ} (hφ : AutomorphicL2Unitary.LeftInv (GQ V) φ) (y : GA D V) :
    ∫ q, AutomorphicL2Unitary.descend (GQ V) (fun x => φ (x * y)) q ∂autMeasure V m =
      ∫ q, AutomorphicL2Unitary.descend (GQ V) φ q ∂autMeasure V m := by
  rw [descend_mul_right hφ y]
  exact (AutomorphicL2Unitary.measurePreserving_rmul (Γ := GQ V) (μ := m) y).integral_comp (rmulEquiv y).measurableEmbedding _

theorem integrable_descend_mul_right_iff {φ : GA D V → ℂ} (hφ : AutomorphicL2Unitary.LeftInv (GQ V) φ) (y : GA D V) :
    Integrable (AutomorphicL2Unitary.descend (GQ V) (fun x => φ (x * y))) (autMeasure V m) ↔
      Integrable (AutomorphicL2Unitary.descend (GQ V) φ) (autMeasure V m) := by
  rw [descend_mul_right hφ y]
  exact (AutomorphicL2Unitary.measurePreserving_rmul (Γ := GQ V) (μ := m) y).integrable_comp_emb (rmulEquiv y).measurableEmbedding

theorem petersson_rTr {φ ψ : GA D V → ℂ} (hφ : AutomorphicL2Unitary.LeftInv (GQ V) φ) (hψ : AutomorphicL2Unitary.LeftInv (GQ V) ψ) (y : GA D V) :
    petersson V m (rTr V y φ) (rTr V y ψ) = petersson V m φ ψ := by
  show ∫ q, AutomorphicL2Unitary.descend (GQ V) (fun x => φ (x * y)) q * conj (AutomorphicL2Unitary.descend (GQ V) (fun x => ψ (x * y)) q)
      ∂autMeasure V m = ∫ q, AutomorphicL2Unitary.descend (GQ V) φ q * conj (AutomorphicL2Unitary.descend (GQ V) ψ q) ∂autMeasure V m
  rw [descend_mul_right hφ y, descend_mul_right hψ y]
  exact (AutomorphicL2Unitary.measurePreserving_rmul (Γ := GQ V) (μ := m) y).integral_comp (rmulEquiv y).measurableEmbedding
    (fun q => AutomorphicL2Unitary.descend (GQ V) φ q * conj (AutomorphicL2Unitary.descend (GQ V) ψ q))

end Quot

section Conj

variable {V : HSp D} (m : Measure (GA D V)) [m.IsHaarMeasure] [m.IsMulRightInvariant]

theorem integral_conj (F : GA D V → ℂ) (k : GA D V) : ∫ y, F (k * y * k⁻¹) ∂m = ∫ y, F y ∂m := by
  rw [integral_mul_left_eq_self (fun z => F (z * k⁻¹)) k, integral_mul_right_eq_self F k⁻¹]

theorem integrable_of_conj {F : GA D V → ℂ} (k : GA D V) (h : Integrable (fun y => F (k * y * k⁻¹)) m) :
    Integrable F m := by
  have h2 := (h.comp_mul_left k⁻¹).comp_mul_right k
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

end Conj

end GlobalTheory.Core.Rk.GlobMove

namespace GlobalTheory.Core.Rk.GlobMove

variable {D : D7}

section Weil

variable {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χA χB : (AE D)ˣ →* Circle} {om : WRep A B}

theorem om_mul_one (g g' : GA D A) (f : WO A B → ℂ) : om (g, 1) (om (g', 1) f) = om (g * g', 1) f := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem thetaKO_om (g k : GA D A) (h : GA D B) (Φ : WO A B → ℂ) :
    thetaKO om g h (om (k, 1) Φ) = thetaKO om (g * k) h Φ := by
  unfold thetaKO
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem leftInv_thetaKO (hW : IsWeilDatumO ψ A B χA χB om) {Φ : WO A B → ℂ} (hΦ : IsThetaFunO ψ A B Φ) (h : GA D B) :
    AutomorphicL2Unitary.LeftInv (GQ A) fun g => thetaKO om g h Φ := by
  intro γ hγ g
  show om (γ * g, h) Φ 0 = om (g, h) Φ 0
  have e : ((γ * g, h) : GA D A × GA D B) = (γ, 1) * (g, h) := by rw [Prod.mk_mul_mk, one_mul]
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut γ hγ 1 (GQ B).one_mem _ (hW.om_pres _ _ hΦ)

theorem wcoef_om (hW : IsWeilDatumO ψ A B χA χB om) {ν : Measure (WO A B)} {𝓕 : Set (WO A B)}
    (hν : IsCovolOne (ratL B A) ν 𝓕) {Φ₁ Φ₂ : WO A B → ℂ} (h₁ : IsThetaFunO ψ A B Φ₁) (h₂ : IsThetaFunO ψ A B Φ₂)
    (k y : GA D A) :
    wcoef om ν 𝓕 (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) y = wcoef om ν 𝓕 Φ₁ Φ₂ (k * y * k⁻¹) := by
  have e : om (y, 1) (om (k⁻¹, 1) Φ₁) = om (k⁻¹, 1) (om (k * y * k⁻¹, 1) Φ₁) := by
    rw [om_mul_one, om_mul_one]; congr 2; group
  have key := GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hW.std A B ν 𝓕 hν.1 hν.2.1 (om (k⁻¹, 1))
    (fun f hf => hW.om_pres (k⁻¹, 1) f hf) (fun f hf => hW.om_unit ν 𝓕 hν.1 hν.2.1 (k⁻¹, 1) f hf)
    (om (k * y * k⁻¹, 1) Φ₁) Φ₂ (hW.om_pres _ _ h₁) h₂
  simp only [wcoef, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, e]
  exact key

end Weil

section Cusp

variable {V : HSp D} (m : Measure (GA D V)) [m.IsHaarMeasure] [m.IsMulRightInvariant]

theorem rcoef_rTr {u₁ u₂ : GA D V → ℂ} (h₁ : AutomorphicL2Unitary.LeftInv (GQ V) u₁) (h₂ : AutomorphicL2Unitary.LeftInv (GQ V) u₂) (k y : GA D V) :
    rcoef m (rTr V k⁻¹ u₁) (rTr V k⁻¹ u₂) y = rcoef m u₁ u₂ (k * y * k⁻¹) := by
  unfold rcoef
  have h₃ : AutomorphicL2Unitary.LeftInv (GQ V) (rTr V (k * y * k⁻¹) u₁) := h₁.mul_right _
  rw [← petersson_rTr m h₃ h₂ k⁻¹]
  congr 1
  funext x
  change u₁ ((x * y) * k⁻¹) = u₁ ((x * k⁻¹) * (k * y * k⁻¹))
  congr 1
  group

end Cusp

end GlobalTheory.Core.Rk.GlobMove

namespace GlobalTheory.Core.Rk.GlobMove

variable {D : D7}

theorem cuspFormsArchimedeanKFinite_left_invariant {θ : InfFam D} {A : HSp D} {cA : CptF A} {u : GA D A → ℂ} (hu : u ∈ A0 θ A cA) :
    AutomorphicL2Unitary.LeftInv (GQ A) u :=
  AutomorphicL2Unitary.leftInv_of_isAutFun (Submodule.mem_inf.1 hu).1.1.toIsAutFun

theorem globalFormAt_move : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' →
    GlobalFormAt A L → GlobalFormAt A L' := by
  intro D A L L' hL hL' hG
  obtain ⟨k, hk, hh⟩ := _root_.GlobalTheory.Core.Rk.IP.hgtL_eq_conj_of_selfDual D A L L' hL hL'
  intro ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hw m mH hm hmH Φ₁ Φ₂ hΦ₁ hΦ₂ u₁ hu₁ u₂ hu₂
  haveI := hm
  haveI := hmH
  haveI : m.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds A m hm
  have hW := hP.weil
  have hθ : IsInfFam θ := hP.setting.2.2.2.1
  have hki : k⁻¹ ∈ GfC A := inv_mem hk
  have fock : ∀ Φ, IsFockVec ψ θ A B sA sB Φ → IsFockVec ψ θ A B sA sB (om (k⁻¹, 1) Φ) := by
    rintro Φ ⟨hΦ, N, hN⟩
    refine ⟨hW.om_pres _ _ hΦ, N, fun l hl => ?_⟩
    refine _root_.GlobalTheory.CartanFockDeg.om_keeps_fockDeg D ψ θ A B χA χB om sA sB hW hθ k⁻¹ (fun τ => ?_) N Φ hΦ hN l hl
    rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ A hki τ, Matrix.one_mul, Matrix.mul_one]
  have lu₁ := cuspFormsArchimedeanKFinite_left_invariant hu₁
  have lu₂ := cuspFormsArchimedeanKFinite_left_invariant hu₂

  have upEq : ∀ Φ, IsThetaFunO ψ A B Φ → ∀ u : GA D A → ℂ, AutomorphicL2Unitary.LeftInv (GQ A) u →
      (∀ h, AutomorphicL2Unitary.descend (GQ A) (fun g => thetaKO om g h (om (k⁻¹, 1) Φ) * rTr A k⁻¹ u g) =
        AutomorphicL2Unitary.descend (GQ A) (fun g => (fun x => thetaKO om x h Φ * u x) (g * k⁻¹))) ∧
      ∀ h, AutomorphicL2Unitary.LeftInv (GQ A) (fun x => thetaKO om x h Φ * u x) := by
    intro Φ hΦ u hu
    refine ⟨fun h => ?_, fun h γ hγ g => ?_⟩
    · congr 1
      funext g
      rw [thetaKO_om]
      rfl
    · simp only [leftInv_thetaKO hW hΦ h γ hγ g, hu γ hγ g]
  have upConvIff : ∀ Φ, IsThetaFunO ψ A B Φ → ∀ u : GA D A → ℂ, AutomorphicL2Unitary.LeftInv (GQ A) u →
      up om m (om (k⁻¹, 1) Φ) (rTr A k⁻¹ u) = up om m Φ u ∧
      (UpConv om m mH (om (k⁻¹, 1) Φ) (rTr A k⁻¹ u) → UpConv om m mH Φ u) := by
    intro Φ hΦ u hu
    obtain ⟨e1, e2⟩ := upEq Φ hΦ u hu
    have hup : up om m (om (k⁻¹, 1) Φ) (rTr A k⁻¹ u) = up om m Φ u := by
      funext h
      simp only [up]
      rw [e1 h, integral_descend_mul_right m (e2 h) k⁻¹]
    refine ⟨hup, fun ⟨c1, c2⟩ => ⟨fun h => ?_, hup ▸ c2⟩⟩
    have := c1 h
    rw [e1 h, integrable_descend_mul_right_iff m (e2 h) k⁻¹] at this
    exact this

  have hint : ∀ s y, integrand om m ν 𝓕 L a (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (rTr A k⁻¹ u₁) (rTr A k⁻¹ u₂) s y =
      integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s (k * y * k⁻¹) := by
    intro s y
    simp only [integrand]
    rw [wcoef_om hW hP.covol hΦ₁.1 hΦ₂.1, rcoef_rTr m lu₁ lu₂, hh a hP.maj]
    congr 3
    group
  obtain ⟨c1, c2, c3, z, hz, hpet⟩ := hG ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hw m mH hm hmH
    (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (fock Φ₁ hΦ₁) (fock Φ₂ hΦ₂)
    (rTr A k⁻¹ u₁) (_root_.GlobalTheory.Core.Rk.RTr.cuspFormsArchimedeanKFinite_rightTranslate_finite D θ A cA hθ k⁻¹ hki u₁ hu₁)
    (rTr A k⁻¹ u₂) (_root_.GlobalTheory.Core.Rk.RTr.cuspFormsArchimedeanKFinite_rightTranslate_finite D θ A cA hθ k⁻¹ hki u₂ hu₂)
  obtain ⟨up₁, cv₁⟩ := upConvIff Φ₁ hΦ₁.1 u₁ lu₁
  obtain ⟨up₂, cv₂⟩ := upConvIff Φ₂ hΦ₂.1 u₂ lu₂
  refine ⟨cv₁ c1, cv₂ c2, fun s hs => integrable_of_conj m k ?_, z, ?_, ?_⟩
  · have := c3 s hs
    rwa [show integrand om m ν 𝓕 L a (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (rTr A k⁻¹ u₁) (rTr A k⁻¹ u₂) s =
      fun y => integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s (k * y * k⁻¹) from funext (hint s)] at this
  · have e : (fun s => ∫ g, integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s g ∂m) =
        fun s => ∫ g, integrand om m ν 𝓕 L a (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (rTr A k⁻¹ u₁) (rTr A k⁻¹ u₂) s g ∂m := by
      funext s
      simp only [hint]
      rw [integral_conj m (integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s) k]
    rw [e]
    exact hz
  · rw [← up₁, ← up₂]
    exact hpet

end GlobalTheory.Core.Rk.GlobMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightIoLe
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section
namespace GlobalTheory.Grow.IoHeight

theorem height_io_le (D : D7) (A : HSp D) (g₁ g₂ : GA D A) :
    GlobalTheory.Grow.height (dblSp A) (io A (g₁, g₂)) ≤ GlobalTheory.Grow.height A g₁ * GlobalTheory.Grow.height A g₂ := by
  have h := GlobalTheory.BlockHeight.heightGL_blk_le D.host.F (finSumFinEquiv (m := A.rank) (n := A.rank))
    (Formalism.L2.Theta.matHom (dblSp A) (io A (g₁, g₂))) (Formalism.L2.Theta.matHom A g₁) (Formalism.L2.Theta.matHom A g₂) rfl rfl
  show ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ) ≤ ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ) * ((GlobalTheory.AdelicU.heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

theorem main : ∀ (D : D7) (A : HSp D), ∃ (C : ℝ) (c : ℕ), ∀ g₁ g₂ : GA D A, GlobalTheory.Grow.height (dblSp A) (io A (g₁, g₂)) ≤ C * (GlobalTheory.Grow.height A g₁ * GlobalTheory.Grow.height A g₂) ^ c :=
  fun D A => ⟨1, 1, fun g₁ g₂ => by simpa using height_io_le D A g₁ g₂⟩

end GlobalTheory.Grow.IoHeight
end
end

