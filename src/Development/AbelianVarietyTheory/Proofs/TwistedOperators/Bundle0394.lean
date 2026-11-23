module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorMixedLaplacianKilledLoweringKilled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0856
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0380
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.HeckeKerZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumMatrixCoefficientEven
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumEven

theorem cartan_laws {k p : ℕ} {G s B Y : Matrix (Fin k) (Fin k) ℂ} (hB : IsONBasis G s B p) (hY : IsPMat p Y) :
    (∃ κ, IsKMat p κ ∧ B * κ * B⁻¹ = s) ∧ (B * Y * B⁻¹)ᴴ * G + G * (B * Y * B⁻¹) = 0 ∧
      s * (B * Y * B⁻¹) = -(B * Y * B⁻¹ * s) := by
  obtain ⟨ε, hε, hBG, hsB⟩ := hB
  obtain ⟨hYh, hY0⟩ := hY

  have hEE : (diagonal fun a => (ε a : ℂ)) * (diagonal fun a => (ε a : ℂ)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hEh : (diagonal fun a => (ε a : ℂ))ᴴ = diagonal fun a => (ε a : ℂ) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    rcases hε a with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]

  have hEY : (diagonal fun a => (ε a : ℂ)) * Y = -(Y * diagonal fun a => (ε a : ℂ)) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal]
    by_cases hij : (i.val < p ↔ j.val < p)
    · rw [hY0 i j hij]
      simp
    · rcases hε i with ⟨hi, hip⟩ | ⟨hi, hip⟩ <;> rcases hε j with ⟨hj, hjp⟩ | ⟨hj, hjp⟩
      · exact absurd (iff_of_true hip hjp) hij
      · rw [hi, hj]
        push_cast
        ring
      · rw [hi, hj]
        push_cast
        ring
      · exact absurd (iff_of_false (not_lt.2 hip) (not_lt.2 hjp)) hij
  have hoff : ∀ i j, ¬ (i.val < p ↔ j.val < p) → (diagonal fun a => (ε a : ℂ)) i j = 0 := by
    intro i j hij
    apply Matrix.diagonal_apply_ne
    intro h
    subst h
    exact hij Iff.rfl
  generalize (diagonal fun a => (ε a : ℂ)) = E at hEE hEh hEY hoff hBG hsB

  have hdet : IsUnit B.det := by
    have h1 : (Bᴴ * G * B * E).det = 1 := by rw [hBG, hEE, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul] at h1
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0] at h1
    simp at h1
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
  have hBi' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hdet
  have hc3 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hBi', Matrix.conjTranspose_one]
  have hc4 : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hBi, Matrix.conjTranspose_one]
  have hc1 : ∀ Z : Matrix (Fin k) (Fin k) ℂ, B⁻¹ * (B * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hBi, Matrix.one_mul]
  have hc2 : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Bᴴ * ((B⁻¹)ᴴ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hc4, Matrix.one_mul]
  have hs : s = B * E * B⁻¹ := by
    calc s = s * B * B⁻¹ := by rw [Matrix.mul_assoc, hBi', Matrix.mul_one]
      _ = B * E * B⁻¹ := by rw [hsB]
  have hG : G = (B⁻¹)ᴴ * E * B⁻¹ := by
    rw [← hBG]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (B⁻¹)ᴴ, hc3, Matrix.one_mul, hBi', Matrix.mul_one]
  subst hs hG
  refine ⟨⟨E, ⟨?_, hoff⟩, rfl⟩, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hEh, hEE]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hYh]
    simp only [Matrix.mul_assoc, hc1, hc2]
    rw [← Matrix.mul_assoc E Y, hEY]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel]
  · simp only [Matrix.mul_assoc, hc1]
    rw [← Matrix.mul_assoc E Y, hEY]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

theorem atTau_oneP {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    {s X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hs : IsCartanInv (gramAt D V τ) s) (hX : X ∈ lieAt V τ)
    (ha : s * X = -(X * s)) (t : ℝ) : atTau θ V τ s * oneP θ V τ X t = oneP θ V τ X (-t) * atTau θ V τ s := by
  obtain ⟨hss, hsU, -⟩ := hs
  unfold oneP
  rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ hsU (GlobalTheory.Mem.Lift.exp_mem hX t),
    ← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (GlobalTheory.Mem.Lift.exp_mem hX (-t)) hsU, GlobalTheory.FockKill.conj_exp hss ha t]

theorem ipO_smul_smul {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (c : ℂ) (f g : Mx D m n → ℂ) :
    ipO μ 𝓕 (c • f) (c • g) = (Complex.normSq c : ℂ) * ipO μ 𝓕 f g := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  rw [← Complex.mul_conj]
  funext a
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem coeff_even : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ (τ : D.what₂.Tau) YS YT, IsPMat (pS τ) YS → IsPMat (pT τ) YT → BS τ * YS * (BS τ)⁻¹ ∈ lieAt S τ ∧ BT τ * YT * (BT τ)⁻¹ ∈ lieAt T τ ∧ ∀ f g, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → IsThetaFunO ψ S T g → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) g) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ t : ℝ, ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) f) g = ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) f) g := by
  intro D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hpS hpT hcS hcT hbS hbT τ YS YT hYS hYT
  obtain ⟨⟨κS, hκS, hsS⟩, hlS, haS⟩ := cartan_laws (hbS τ) hYS
  obtain ⟨⟨κT, hκT, hsT⟩, hlT, haT⟩ := cartan_laws (hbT τ) hYT
  refine ⟨hlS, hlT, ?_⟩
  intro f g hf hvf hg hvg μ 𝓕 hμ t
  obtain ⟨mS, mT, hchar⟩ := GlobalTheory.VacCharAtPlace.vacuum_char_at_place D ψ θ S T χS χT om hom hθ τ
  have hUS : sS τ ∈ Formalism.QuantumDeterminants.UH (gramAt D S τ) := by
    obtain ⟨-, h, -⟩ := hcS τ
    exact h
  have hUT : sT τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
    obtain ⟨-, h, -⟩ := hcT τ
    exact h
  have hssS : sS τ * sS τ = 1 := by
    obtain ⟨h, -, -⟩ := hcS τ
    exact h
  have hssT : sT τ * sT τ = 1 := by
    obtain ⟨h, -, -⟩ := hcT τ
    exact h

  have hmul : ∀ a b φ, om a (om b φ) = om (a * b) φ := fun a b φ => by
    rw [map_mul, Module.End.mul_apply]

  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ φ, IsThetaFunO ψ S T φ →
      (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) φ) →
      om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) φ = c • φ :=
    ⟨_, fun φ hφ hvφ => hchar sS BS sT BT pS pT hpS hpT hcS hcT hbS hbT φ hφ hvφ κS κT hκS hκT _ _
      (by rw [hsS]; exact GlobalTheory.PointAtPlaceHom.atTau_spec hθ S τ hUS)
      (by rw [hsT]; exact GlobalTheory.PointAtPlaceHom.atTau_spec hθ T τ hUT)⟩
  by_cases hf0 : f = 0
  · subst hf0
    simp [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO]

  have hkk : om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) f) = f := by
    have h1 : ((1 : GA D S), (1 : GA D T)) = (1 : GA D S × GA D T) := rfl
    rw [hmul, Prod.mk_mul_mk, ← GlobalTheory.PointAtPlaceHom.atTau_mul hθ S τ hUS hUS,
      ← GlobalTheory.PointAtPlaceHom.atTau_mul hθ T τ hUT hUT, hssS, hssT, GlobalTheory.PointAtPlaceHom.atTau_one hθ S τ,
      GlobalTheory.PointAtPlaceHom.atTau_one hθ T τ, h1, map_one, Module.End.one_apply]
  rw [hc f hf hvf, map_smul, hc f hf hvf, smul_smul] at hkk
  have hcc : c * c = 1 := by
    by_contra hne
    apply hf0
    have h0 : (c * c - 1) • f = 0 := by rw [sub_smul, hkk, one_smul, sub_self]
    exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)
  have hn : (Complex.normSq c : ℂ) = 1 := by
    have h2 : Complex.normSq c * Complex.normSq c = 1 := by
      rw [← Complex.normSq_mul, hcc, Complex.normSq_one]
    have h3 : Complex.normSq c = 1 := by nlinarith [Complex.normSq_nonneg c]
    rw [h3, Complex.ofReal_one]

  have hconj : (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) *
      (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) =
      (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) *
      (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) := by
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, atTau_oneP hθ S τ (hcS τ) hlS haS (-t),
      atTau_oneP hθ T τ (hcT τ) hlT haT (-t), neg_neg]

  have hU : ∀ p φ φ', IsThetaFunO ψ S T φ → IsThetaFunO ψ S T φ' →
      ipO μ 𝓕 (om p φ) (om p φ') = ipO μ 𝓕 φ φ' := fun p φ φ' hφ hφ' =>
    GlobalTheory.WeilInner.om_inner D ψ S T χS χT om hom μ 𝓕 hμ p φ φ' hφ hφ'
  calc ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) f) g
      = ipO μ 𝓕 (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ))
          (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) f))
          (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) g) := (hU _ _ g (hom.om_pres _ f hf) hg).symm
    _ = ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t)
          (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) f))
          (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) g) := by
      congr 1
      rw [hmul, hmul, hconj]
    _ = ipO μ 𝓕 (c • om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) f) (c • g) := by
      rw [hc f hf hvf, hc g hg hvg, map_smul]
    _ = ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) f) g := by
      rw [ipO_smul_smul, hn, one_mul]

end GlobalTheory.VacuumEven
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyAppellHumbertFramePullEqTransitionMu
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

noncomputable section

namespace GlobalTheory.HeckeEx

theorem frame_pull_eq_transition_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (yx zx : Sp ℂ ⟶ Xo.X) (p : ℕ)
  (ψp : (Over.mk yx ⟶ Xo.univ.t.G) →* (Over.mk zx ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk yx ⟶ Xo.univ.t.G) → ℂ)
  (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk yx ⟶ Xo.univ.t.G)) (e' : (Fin g → ℂ) → (Over.mk zx ⟶ Xo.univ.t.G))
  (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
  Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
  IsHolTo Set.univ (fun w => (e w).left) → IsHolTo Set.univ (fun w => (e' w).left) →
  (∀ w w', e (w + w') = e w * e w') → (∀ a ∈ Λ, e a = 1) → (∀ w, e' (h w) = ψp (e w)) →
  (∀ a ∈ Λ, h a ∈ Λ') →
  (∀ i j (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) →
  (∀ i j i' j' (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
    ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
    b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
      valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) →
  (∀ i j, ⊤ ≤ (1 : Over.mk zx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
    ⊤ ≤ (1 : Over.mk yx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
      b i j 1 * valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
  (∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
    {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    Hm.IsHermitian →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (e z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (e z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (e 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ, ∀ j z, ‖χl a‖ = 1 ∧ (⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl a * Complex.exp (Real.pi * hermForm Hm z a + Real.pi / 2 * hermForm Hm a a) * fr j (z + a))) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j j' z, ⊤ ≤ (e' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (e' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (e' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ', ∀ j z, ‖χl' a‖ = 1 ∧ (⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' a * Complex.exp (Real.pi * hermForm Hm' z a + Real.pi / 2 * hermForm Hm' a a) * fr' j (z + a))) →
  ∀ w i j, ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    fr' i (h w) = b i j (e w) * fr j ((p : ℂ) • w) := by
  intro E _ _ _ H Dw l Xo yx zx p ψp b g Λ Λ' e e' h hΛ hhe hhe' hadd hker hψ hΛΛ' hbn hbc hb0 hbd
    Hm χl fr hH hd hn hc h0 ha Hm' χl' fr' hHH hd' hc' h0' ha' w i j hi hj
  have e0 : e 0 = 1 := hker 0 (zero_mem Λ)
  have hpow : ∀ (n : ℕ) z, e ((n : ℂ) • z) = e z ^ n := by
    intro n z
    induction n with
    | zero => rw [Nat.cast_zero, zero_smul, e0, pow_zero]
    | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  have e'0 : e' 0 = 1 := by rw [← map_zero h, hψ, e0, map_one]
  have hpa : ∀ a ∈ Λ, (p : ℂ) • a ∈ Λ := fun a haa => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem haa p
  have per : ∀ a ∈ Λ, ∀ z, e (z + a) = e z := fun a haa z => by rw [hadd, hker a haa]; exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hsm : ∀ z a, hermForm Hm ((p : ℂ) • z) ((p : ℂ) • a) = (p : ℂ) ^ 2 * hermForm Hm z a := fun z a => by
    rw [GlobalTheory.UnitFrameGen.hermForm_smul_left, GlobalTheory.UnitFrameGen.hermForm_smul_right, star_natCast]; ring
  have ho1 : ∀ V, IsOpen {z | ⊤ ≤ (e z).left ⁻¹ᵁ V} := fun V => by simpa using (hhe V 0).1
  have ho1' : ∀ V, IsOpen {z | ⊤ ≤ (e' z).left ⁻¹ᵁ V} := fun V => by simpa using (hhe' V 0).1
  have hch : Continuous h := h.toLinearMap.continuous_of_finiteDimensional
  have dh : Differentiable ℂ (fun z => h z) := (LinearMap.toContinuousLinearMap h.toLinearMap).differentiable
  have dsm : Differentiable ℂ (fun z : Fin g → ℂ => (p : ℂ) • z) := differentiable_id.const_smul (p : ℂ)
  have key := GlobalTheory.UnitFrameGen.frames_eq Λ hΛ
    (fun q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι =>
      {w | ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U q.1 ∧ ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U q.2})
    (fun q => ((ho1' _).preimage hch).inter ((ho1 _).preimage (continuous_const_smul (p : ℂ))))
    (fun z => by
      obtain ⟨i', hi'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (e' (h z)).left
      obtain ⟨j', hj'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (e ((p : ℂ) • z)).left
      exact ⟨(i', j'), hi', hj'⟩)
    (fun q a haa z hz => by
      refine ⟨?_, ?_⟩
      · rw [hψ, per a haa, ← hψ]; exact hz.1
      · rw [smul_add, per _ (hpa a haa)]; exact hz.2)
    (fun q z => b q.1 q.2 (e z) * fr q.2 ((p : ℂ) • z)) (fun q z => fr' q.1 (h z))
    (fun q q' z => valAt' (e' (h z)).left (Xo.univ.t.PP.L.U q.1 ⊓ Xo.univ.t.PP.L.U q'.1)
      (Xo.univ.t.PP.L.g q.1 q'.1).val)
    (fun a z => Real.exp (Real.pi * (hermForm Hm ((p : ℂ) • z) ((p : ℂ) • a)).re +
      Real.pi / 2 * (hermForm Hm ((p : ℂ) • a) ((p : ℂ) • a)).re))
    (fun q => ((hbd q.1 q.2).mono fun z hz => ⟨by rw [← hψ]; exact hz.1, by rw [← hpow]; exact hz.2⟩).mul
      ((hd q.2).comp dsm.differentiableOn fun z hz => hz.2))
    (fun q => (hd' q.1).comp dh.differentiableOn fun z hz => hz.1)
    (fun q z hz => mul_ne_zero (hbn q.1 q.2 (e z) (by rw [← hψ]; exact hz.1) (by rw [← hpow]; exact hz.2))
      (hn q.2 _ hz.2))
    (fun q q' z h1 h2 => by
      have e1 := hc q.2 q'.2 ((p : ℂ) • z) ((top_le_preimage_inf _ _ _).2 ⟨h1.2, h2.2⟩)
      have e2 := hbc q.1 q.2 q'.1 q'.2 (e z)
        (by rw [← hψ]; exact (top_le_preimage_inf _ _ _).2 ⟨h1.1, h2.1⟩)
        (by rw [← hpow]; exact (top_le_preimage_inf _ _ _).2 ⟨h1.2, h2.2⟩)
      rw [hpow] at e1
      rw [hψ, e1]
      linear_combination e2 * fr q'.2 ((p : ℂ) • z))
    (fun q q' z h1 h2 => hc' q.1 q'.1 (h z) ((top_le_preimage_inf _ _ _).2 ⟨h1.1, h2.1⟩))
    (fun q hz => by
      have z1 := hz.1
      have z2 := hz.2
      rw [map_zero] at z1
      rw [smul_zero] at z2
      rw [map_zero, smul_zero, h0' _ z1, h0 _ z2, e0]
      rw [e'0] at z1
      rw [e0] at z2
      exact hb0 q.1 q.2 z1 z2)
    (fun q a haa z hz => by
      have := GlobalTheory.UnitFrameGen.norm_factor Hm _ _ _ _ _ (ha _ (hpa a haa) q.2 ((p : ℂ) • z)).1
        ((ha _ (hpa a haa) q.2 _).2 hz.2)
      rw [per a haa, smul_add, norm_mul, norm_mul, this]; ring)
    (fun q a haa z hz => by
      have := GlobalTheory.UnitFrameGen.norm_factor Hm' _ _ _ _ _ (ha' _ (hΛΛ' a haa) q.1 (h z)).1
        ((ha' _ (hΛΛ' a haa) q.1 (h z)).2 hz.1)
      rw [hHH, hHH] at this
      rw [map_add (f := _), this, hsm, hsm])
  exact key (i, j) w ⟨hi, hj⟩

end GlobalTheory.HeckeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKerLatticeBounds
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section

set_option autoImplicit false

namespace GlobalTheory.HeckeKerIdx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem ex_smul_act (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (c : ℂ) (r : 𝓞 E) (v : (F.Di i).La) :
    F.ex i P (c • P (r • v)) = F.ex i P (c • P v) ≫ Xo.univ.t.act.act r := by
  rw [← F.ex_lin i P hP]
  congr 1
  ext k
  rw [Pi.smul_apply, hP.1, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]

theorem inv_smul_natCast {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (P : La →+ (Fin g → ℂ)) {n : ℕ}
    (hn : n ≠ 0) (w : La) : ((n : ℂ))⁻¹ • P ((n : 𝓞 E) • w) = P w := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_smul]

theorem sq_inv_smul_natCast {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (P : La →+ (Fin g → ℂ)) {n : ℕ}
    (hn : n ≠ 0) (w : La) : ((n : ℂ) ^ 2)⁻¹ • P ((n : 𝓞 E) • w) = (n : ℂ)⁻¹ • P w := by
  rw [pow_two, mul_inv, mul_smul, inv_smul_natCast P hn]

theorem mem_span_smul_top {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (n : ℕ) (x : La) :
    x ∈ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) La) ↔ ∃ b, (n : 𝓞 E) • b = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

end GlobalTheory.HeckeKerIdx


open GlobalTheory.HeckeKerIdx in
theorem GlobalTheory.heckeKer_lattice_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (𝔓 : Ideal (𝓞 E)) (p k : ℕ) (C : Subgroup (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (M : Submodule (𝓞 E) (F.Di i).La), IsPeriod (F.Di i) ty P → GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l 𝔓 p → Xo.univ.t.HeckeKer (Over.mk (F.u i P)) Dw 𝔓 p k C → (∀ a, F.ex i P (((p : ℂ) ^ 2)⁻¹ • P a) ∈ C ↔ a ∈ M) → (Ideal.span {(p : 𝓞 E)} * 𝔓) • (⊤ : Submodule (𝓞 E) (F.Di i).La) ≤ M ∧ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) • M ≤ Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La) ∧ Nat.card (↥(Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La)) ⧸ M.comap (Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La)).subtype) = Ideal.absNorm 𝔓 ^ k := by
  intro E _ _ _ H Dw l Xo σ g ty F i P 𝔓 p k C M hP hH hK hM
  obtain ⟨-, -, -, hp, hp𝔓⟩ := hH
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0
  refine ⟨?_, ?_, ?_⟩
  · rw [Submodule.smul_le]
    intro x hx a _
    obtain ⟨π, hπ, rfl⟩ := Ideal.mem_span_singleton_mul.1 hx
    obtain ⟨J, hJ⟩ : 𝔓 ∣ Ideal.span {(p : 𝓞 E)} :=
      Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hp𝔓)
    rw [← hM, mul_smul, sq_inv_smul_natCast P hp0]
    refine hK.2.1 J (by rw [hJ, mul_comm]) fun j hj => ?_
    rw [← ex_smul_act F i P hP, smul_smul]
    have hjπ : j * π ∈ Ideal.span {(p : 𝓞 E)} := by
      rw [hJ, mul_comm j]
      exact Ideal.mul_mem_mul hπ hj
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hjπ
    rw [hc, mul_smul, inv_smul_natCast P hp0]
    exact (F.ex_ker i P hP _).2 ⟨_, rfl⟩
  · rw [Submodule.smul_le]
    intro r hr a ha
    have h1 := hK.2.2.1 ((hM a).2 ha) ((p : 𝓞 E) * r)
      (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hr)
    rw [← ex_smul_act F i P hP, mul_smul, sq_inv_smul_natCast P hp0, F.ex_ker i P hP] at h1
    obtain ⟨b, hb⟩ := h1
    rw [mem_span_smul_top]
    refine ⟨b, hP.2.1 ?_⟩
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hpC, one_smul]
  · set N : Submodule (𝓞 E) (F.Di i).La := Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La) with hN
    set Tp := GlobalTheory.HeckeKerModel.torsSub Xo.univ.t (Over.mk (F.u i P)) p with hTp
    have hmemTp : ∀ y, y ∈ Tp ↔ y ^ p = 1 := fun y => GlobalTheory.HeckeKerModel.mem_tors_span Xo.univ.t y p
    have hpow : ∀ w, F.ex i P w ^ p = F.ex i P (p • w) := fun w => (GlobalTheory.HeckeKerLat.ex_nsmul F i P hP p w).symm
    have hinvmem : ∀ b, F.ex i P ((p : ℂ)⁻¹ • P b) ∈ Tp := fun b => by
      rw [hmemTp, hpow, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hpC, one_smul]
      exact (F.ex_ker i P hP _).2 ⟨b, rfl⟩
    have hmemN : ∀ x ∈ N, F.ex i P (((p : ℂ) ^ 2)⁻¹ • P x) ∈ Tp := fun x hx => by
      obtain ⟨b, rfl⟩ := (mem_span_smul_top p x).1 hx
      rw [sq_inv_smul_natCast P hp0]
      exact hinvmem b
    let fA : ↥N →+ Additive ↥Tp :=
      { toFun := fun x => Additive.ofMul ⟨F.ex i P (((p : ℂ) ^ 2)⁻¹ • P x), hmemN x.1 x.2⟩
        map_zero' := by
          apply Additive.toMul.injective
          apply Subtype.ext
          show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P 0) = 1
          rw [map_zero, smul_zero]
          exact (F.ex_ker i P hP 0).2 (zero_mem _)
        map_add' := fun x y => by
          apply Additive.toMul.injective
          apply Subtype.ext
          show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P (x.1 + y.1)) = F.ex i P (((p : ℂ) ^ 2)⁻¹ • P x.1) * F.ex i P (((p : ℂ) ^ 2)⁻¹ • P y.1)
          rw [map_add (f := _), smul_add, F.ex_add i P hP] }
    let h0 : (F.Di i).La →+ ↥N :=
      { toFun := fun a => ⟨(p : 𝓞 E) • a, (mem_span_smul_top p _).2 ⟨a, rfl⟩⟩
        map_zero' := by ext; simp
        map_add' := fun a b => by ext; simp [smul_add] }
    have hgsurj : Function.Surjective (fA.comp h0) := by
      intro y
      obtain ⟨w, hw⟩ := F.ex_onto i P hP (Additive.toMul y).1
      have h1 : F.ex i P (p • w) = 1 := by rw [← hpow, hw]; exact (hmemTp _).1 (Additive.toMul y).2
      obtain ⟨a, ha⟩ := (F.ex_ker i P hP _).1 h1
      refine ⟨a, ?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P ((p : 𝓞 E) • a)) = (Additive.toMul y).1
      rw [sq_inv_smul_natCast P hp0, ha, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hpC, one_smul, hw]
    have hsurj : Function.Surjective fA := fun y => by
      obtain ⟨a, ha⟩ := hgsurj y
      exact ⟨h0 a, ha⟩
    set H' : AddSubgroup (Additive ↥Tp) := Subgroup.toAddSubgroup (C.subgroupOf Tp) with hH'
    have hker : (M.comap N.subtype).toAddSubgroup = H'.comap fA := by
      ext x
      rw [AddSubgroup.mem_comap]
      show x.1 ∈ M ↔ _
      rw [← hM]
      rfl
    have hidx : Nat.card (↥N ⧸ M.comap N.subtype) = H'.index := by
      rw [← AddSubgroup.index_comap_of_surjective H' hsurj, ← hker]
      rfl
    have hcardTp : Nat.card (Additive ↥Tp) = Nat.card (Xo.univ.t.tors (Over.mk (F.u i P)) (Ideal.span {(p : 𝓞 E)})) := rfl
    have hcardH : Nat.card H' = Nat.card ((C : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) ∩ Xo.univ.t.tors (Over.mk (F.u i P)) (Ideal.span {(p : 𝓞 E)}) : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) :=
      Nat.card_congr
        { toFun := fun z => ⟨(Additive.toMul z.1).1, z.2, (Additive.toMul z.1).2⟩
          invFun := fun z => ⟨Additive.ofMul ⟨z.1, z.2.2⟩, z.2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hfin : Nat.card (Additive ↥Tp) ≠ 0 := by
      have := (F.Di i).fin
      have := GlobalTheory.datum_free_int (F.Di i)
      have : Module.Finite ℤ (F.Di i).La := Module.Finite.trans (𝓞 E) (F.Di i).La
      have hle : (nsmulAddMonoidHom (α := (F.Di i).La) p).range ≤ (fA.comp h0).ker := by
        rintro _ ⟨b, rfl⟩
        rw [AddMonoidHom.mem_ker]
        apply Additive.toMul.injective
        apply Subtype.ext
        show F.ex i P (((p : ℂ) ^ 2)⁻¹ • P ((p : 𝓞 E) • (p • b))) = 1
        rw [sq_inv_smul_natCast P hp0, ← Nat.cast_smul_eq_nsmul (𝓞 E), inv_smul_natCast P hp0]
        exact (F.ex_ker i P hP _).2 ⟨b, rfl⟩
      have hd := AddSubgroup.index_dvd_of_le hle
      rw [AddSubgroup.index_range_nsmul, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hgsurj,
        AddSubgroup.card_top] at hd
      intro h0'
      rw [h0', zero_dvd_iff] at hd
      exact pow_ne_zero _ hp0 hd
    have key := H'.index_mul_card
    rw [hcardTp, hK.2.2.2.2.2, hcardH] at key
    rw [hidx]
    have hc : Nat.card ((C : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) ∩ Xo.univ.t.tors (Over.mk (F.u i P)) (Ideal.span {(p : 𝓞 E)}) : Set (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) ≠ 0 := by
      intro hc0
      apply hfin
      rw [hcardTp, hK.2.2.2.2.2, hc0, zero_mul]
    rw [mul_comm (Nat.card _) (Ideal.absNorm 𝔓 ^ k)] at key
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hc) key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersAtRealPlaces
section
open Formalism.BasicNotions

namespace GlobalTheory

theorem vacChar_of_record : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D :=
  _root_.GlobalTheory.VacuumCharacter.vacChar

end GlobalTheory
end

