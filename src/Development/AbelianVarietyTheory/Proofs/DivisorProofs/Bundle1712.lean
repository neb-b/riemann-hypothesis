module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0924
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceSchwartzBruhatVacuumConditionEqSmul
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.VacUniqInert

theorem eq_smul_of_eigen {K κ : Type} [Field K] [Fintype κ] [Invertible (2 : K)] (ψ₀ : AddChar K ℂ) {ι : Type}
    (L : ι → (κ → K) × (κ → K)) (c : ι → ℂ)
    (hD : ∀ u : κ → K, (∀ i, (L i).1 = 0 → ψ₀ (u ⬝ᵥ (L i).2) = 1) → ∃ i, (L i).1 = u)
    (f η : (κ → K) → ℂ) (hf : ∀ i, schr ψ₀ (L i) f = c i • f) (hη : ∀ i, schr ψ₀ (L i) η = c i • η)
    (hη0 : η ≠ 0) : ∃ c' : ℂ, f = c' • η := by
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, η X₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hη0 (funext h)
  have hne : ∀ t, ψ₀ t ≠ 0 := fun t h => by
    have e := AddChar.map_add_eq_mul ψ₀ t (-t)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at e
    exact one_ne_zero e
  refine ⟨f X₀ / η X₀, funext fun X => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hu : ∀ i, (L i).1 = 0 → ψ₀ ((X - X₀) ⬝ᵥ (L i).2) = 1
  · obtain ⟨i, hi⟩ := hD _ hu
    have hX : X₀ + (L i).1 = X := by rw [hi]; abel
    have e1 := congrFun (hf i) X₀
    have e2 := congrFun (hη i) X₀
    simp only [schr, Pi.smul_apply, smul_eq_mul, hX] at e1 e2
    have hA := hne (X₀ ⬝ᵥ (L i).2 + ⅟(2 : K) * ((L i).1 ⬝ᵥ (L i).2))
    field_simp
    refine mul_left_cancel₀ hA ?_
    linear_combination η X₀ * e1 - f X₀ * e2
  · push_neg at hu
    obtain ⟨i, hi0, hne1⟩ := hu
    have key : ∀ g : (κ → K) → ℂ, schr ψ₀ (L i) g = c i • g → ∀ Y, ψ₀ (Y ⬝ᵥ (L i).2) * g Y = c i * g Y := by
      intro g hg Y
      have e := congrFun hg Y
      simpa [schr, hi0] using e
    have hc : ψ₀ (X₀ ⬝ᵥ (L i).2) = c i := mul_right_cancel₀ hX₀ (key η (hη i) X₀)
    have hz : ∀ g : (κ → K) → ℂ, schr ψ₀ (L i) g = c i • g → g X = 0 := by
      intro g hg
      by_contra hgX
      have h1 : ψ₀ (X ⬝ᵥ (L i).2) = ψ₀ (X₀ ⬝ᵥ (L i).2) := by
        rw [hc]; exact mul_right_cancel₀ hgX (key g hg X)
      apply hne1
      have e : X ⬝ᵥ (L i).2 = (X - X₀) ⬝ᵥ (L i).2 + X₀ ⬝ᵥ (L i).2 := by rw [sub_dotProduct]; ring
      rw [e, AddChar.map_add_eq_mul] at h1
      exact mul_right_cancel₀ (hne _) (h1.trans (one_mul _).symm)
    rw [hz f (hf i), hz η (hη i), mul_zero]

theorem vac_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 →
      (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • (G.M'.vac v))) →
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • φ)) → ∃ c : ℂ, φ = c • G.M'.vac v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin θ _ hvac φ hφ hfix
  classical
  have hat : ∀ γ ∈ latAtV G.V' G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  let cf : latAtV G.V' G.W v → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ)
  have hloc : ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v), (∀ γ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (G.M'.co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • f)) →
      ∀ γ : latAtV G.V' G.W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) f = cf γ • f := by
    intro f hf h γ
    exact GlobalTheory.TensUniq.eq_of_tens_eq v f _ _ hf fun r hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v γ (hat γ γ.2) f r hr).symm.trans (h γ γ.2 r hr)
  have hsd : ∀ z, z ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v) ↔
      ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v), GlobalTheory.LatVac.psiAt B.ψ v (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1 :=
    GlobalTheory.LatVac.DualLoc.map_selfDual v G.M'.co B.ψ (latAtV G.V' G.W v) hat
      (fun z hz => GlobalTheory.T.inertPlace_tensorLattice_selfDual_symplectic F E σ B hTr.base G.V' G.W _ _ _ _ hTr.geo.hV' hTr.geo.hW v w hin z hz)
  have hst : ∀ t ∈ v.adicCompletionIntegers F, ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v),
      t • l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v) := by
    rintro t ht _ ⟨γ, hγ, rfl⟩
    refine ⟨GlobalTheory.LatVac.liftV v t • γ, (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).2 t ht γ hγ, ?_⟩
    rw [GlobalTheory.LatOpenCpt.locCo_smul, GlobalTheory.LatVac.evFin_liftV]
  have hbd : ∃ c : Fv F v, c ≠ 0 ∧ ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v), ∀ i,
      c * l.1 i ∈ v.adicCompletionIntegers F := by
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V' G.W v G.M'.co hTr.geo.hV'.lat.toIsLattice hTr.geo.hW.lat.toIsLattice
    exact ⟨c, hc0, by rintro _ ⟨γ, hγ, rfl⟩ i; exact (hc γ hγ i).1⟩
  have hD := _root_.GlobalTheory.selfDual_exists_snd_of_orth v (GlobalTheory.LatVac.psiAt B.ψ v) _ hsd hst hbd
  refine eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v) (fun γ : latAtV G.V' G.W v => GlobalTheory.LatVac.locCo G.M'.co v γ) cf
    (fun u hu => ?_) φ (G.M'.vac v) (hloc φ hφ hfix) (hloc _ (hTr.geo.hM'.vac v).1 hvac) (hTr.geo.hM'.vac v).2.1
  obtain ⟨y', γ, hγ, he⟩ := hD u (by
    rintro y ⟨γ, hγ, he⟩
    have h1 := hu ⟨γ, hγ⟩ (congrArg Prod.fst he)
    have h2 : (GlobalTheory.LatVac.locCo G.M'.co v γ).2 = y := congrArg Prod.snd he
    simp only at h1
    rw [h2] at h1
    exact h1)
  exact ⟨⟨γ, hγ⟩, congrArg Prod.fst he⟩

end GlobalTheory.VacUniqInert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceWeilNormalisesHeisenberg
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBridge

theorem weil_normalises_heis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∀ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) →
    ∀ g h x, ω (g, h) * ρ x =
      ρ (((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
        (((g : GL (Fin a') L)⁻¹ : GL (Fin a') L) : Matrix (Fin a') (Fin a') L)) * ω (g, h) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w _ _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ ω hω g h x
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hEq, _, _, _, _⟩ := hC
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a' × Fin (a + a')) v
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  have hωA : ∀ (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (om' (ιS g, ιT h))
      (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    fun m => (hω g h m _ (ω (g, h) m).2).2 rfl
  refine LinearMap.ext fun m => ?_
  apply Subtype.ext
  set y := ((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
        (((g : GL (Fin a') L)⁻¹ : GL (Fin a') L) : Matrix (Fin a') (Fin a') L) with hy
  have e1 : om' (ιS g, ιT h) (G.M'.co.rho B.ψ (κ x) (tens (evFin F v) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R)) =
      tens (evFin F v) (((ω (g, h) (ρ x m)) : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R := by
    rw [hρ x m R (hR _ m.2), hωA (ρ x m) R (hR _ (ρ x m).2)]
  have e2 : om' (ιS g, ιT h) (G.M'.co.rho B.ψ (κ x) (tens (evFin F v) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R)) =
      tens (evFin F v) (((ρ y (ω (g, h) m)) : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R := by
    have he : actAB (cA σ) (ιS g, ιT h) (κ x) = κ y := by
      unfold cA
      exact (hEq g h x).trans (congrArg κ hy.symm)
    rw [hS.impl (ιS g, ιT h) (κ x) _ (hR _ m.2).2]
    rw [he, hωA m R (hR _ m.2),
      hρ y (ω (g, h) m) R (hR _ (ω (g, h) m).2)]
  have e := e1.symm.trans e2
  show (((ω (g, h) (ρ x m)) : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) =
    (((ρ y (ω (g, h) m)) : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)
  funext yv
  set z : (Fin a' × Fin (a + a')) → AF F := fun i => GlobalTheory.LatVac.liftV v (yv i) with hz
  have hza : At (evFin F v) z := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have hrx : R (0 + z) = R 0 := (hR _ m.2).1 0 z hza
  have hyv : (fun i => evFin F v (((0 : (Fin a' × Fin (a + a')) → AF F) + z) i)) = yv := by
    funext i
    simp only [hz, Pi.add_apply, Pi.zero_apply, zero_add, GlobalTheory.LatVac.evFin_liftV]
  have e' := congrFun e (0 + z)
  simp only [tens] at e'
  rw [hrx, hyv] at e'
  exact mul_right_cancel₀ hR0 e'

end GlobalTheory.InertBridge

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrablePowerNormCompact
section
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal ENNReal

noncomputable section
namespace GlobalTheory.LocTateInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)

theorem finite_FE : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E

attribute [local instance] finite_FE

def basisEv : Module.Basis (Fin (Module.finrank F E)) (Fv F v) (Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)

theorem isModuleTopology_Ev : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩

def coordEv : (Fv F v ⊗[F] E) ≃ₜ+ (Fin (Module.finrank F E) → Fv F v) :=
  haveI := isModuleTopology_Ev (E := E) v
  { (basisEv v).equivFun.toAddEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (basisEv (E := E) v).equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap (basisEv (E := E) v).equivFun.symm.toLinearMap }

theorem isTopologicalRing_Ev : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens

theorem t2Space_Fv_tensor : T2Space (Fv F v ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension

theorem locallyCompactSpace_Ev : LocallyCompactSpace (Fv F v ⊗[F] E) :=
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  (coordEv (E := E) v).toHomeomorph.isClosedEmbedding.locallyCompactSpace

theorem secondCountable_Ev : SecondCountableTopology (Fv F v ⊗[F] E) :=
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  (coordEv (E := E) v).toHomeomorph.isEmbedding.secondCountableTopology

theorem isOpenUnits_Ev : IsOpenUnits (Fv F v ⊗[F] E) :=
  haveI := isModuleTopology_Ev (E := E) v
  haveI := isTopologicalRing_Ev (E := E) v
  GlobalTheory.GaugeEx.isOpenUnits_of_basis (basisEv v)

attribute [local instance] isTopologicalRing_Ev t2Space_Fv_tensor locallyCompactSpace_Ev secondCountable_Ev isOpenUnits_Ev

theorem distribHaarChar_Ev (u : (Fv F v ⊗[F] E)ˣ) :
    distribHaarChar (Fv F v ⊗[F] E) u = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ := by
  borelize (Fv F v ⊗[F] E)
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  set b := basisEv (E := E) v
  set M := Algebra.leftMulMatrix b (u : Fv F v ⊗[F] E) with hMdef
  have hdet : M.det = Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) := (Algebra.norm_eq_matrix_det b _).symm
  have hM : IsUnit M.det := hdet ▸ u.isUnit.map (Algebra.norm (Fv F v))
  have hN0 : Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) ≠ 0 := (hdet ▸ hM).ne_zero
  rw [GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar]
  have ht := GlobalTheory.ModuLR.addEquivAddHaarChar_transport (coordEv (E := E) v).symm (GlobalTheory.ModuLR.mulVecCE M hM)
  have hext : (((coordEv (E := E) v).symm.symm.trans (GlobalTheory.ModuLR.mulVecCE M hM)).trans (coordEv (E := E) v).symm) =
      GlobalTheory.ModuNorm.mulUnitCE u := by
    ext x
    show b.equivFun.symm (Matrix.mulVec M (b.equivFun x)) = (u : Fv F v ⊗[F] E) * x
    rw [show Matrix.mulVec M (b.equivFun x) = b.equivFun ((u : Fv F v ⊗[F] E) * x) from Algebra.leftMulMatrix_mulVec_repr b _ x,
      LinearEquiv.symm_apply_apply]
  rw [hext] at ht
  rw [ht, GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE _ inferInstance inferInstance, hdet, GlobalTheory.GaugeEx.modu,
    dite_eq_left (hdet ▸ hM)]
  convert GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v _ hN0 using 2
  exact Units.ext rfl

end GlobalTheory.LocTateInt

namespace GlobalTheory.LocTateInt

open scoped Pointwise

attribute [local instance] finite_FE isTopologicalRing_Ev t2Space_Fv_tensor locallyCompactSpace_Ev secondCountable_Ev isOpenUnits_Ev

end GlobalTheory.LocTateInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCuspFormsFullLattice
section
noncomputable section

namespace GlobalTheory.GoodLat.Obj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Arith Formalism.IndefR.FWT

theorem nV_pos (D : D7) : 0 < D.R.nV := by
  have := D.R.three_m_lt_t
  rw [Ranks.nV]
  omega

theorem fullLat {D : D7} (T : Core D) (hT : LawsM T) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) (hn : 0 < w.n) :
    FullLat (T.cuspA j (wtA w) w.n) (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)) fun la => isVal_valSet la :=
  (GlobalTheory.IndefiniteRowSideFullHecke.SupremumLattice.supIn_full_iff _ _ _).1
    (GlobalTheory.SupFull.fullAt_of_pins D T hT.pins j hj (hT.unf j hj _ T.good_σ₀) w hn)

section Real

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem latFull (T : CoreJ D) (hT : LawsJ T) {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} (hκ : KapIs κ) :
    LatFull T κ := fun i =>
  fullLat T.toCore hT.toLawsM (inR i) (κ i) (by rw [(hκ i (D.eTau.symm 1)).2.2]; exact nV_pos D)

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem mkFull_of_tie (t : FWTie T R κ v₀) (i : Fin D.R.m) : (R.FW i).MKFull :=
  GlobalTheory.GoodLat.mkFull_of_tie t (latFull T t.laws t.kap) i

theorem mLat_of_tie (t : FWTie T R κ v₀) (F : Face D A) (b : Bool) : (R.toCx F).MLat b :=
  GlobalTheory.GoodLat.mLat_of_tie t (latFull T t.laws t.kap) F b

end Real

end GlobalTheory.GoodLat.Obj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.StdPairCone

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def blk₁ {m a a' : ℕ} (X : Matrix (Fin m) (Fin (a + a')) k) : Matrix (Fin m) (Fin a) k :=
  Matrix.of fun i j => X i (Fin.castAdd a' j)

def blk₂ {m a a' : ℕ} (X : Matrix (Fin m) (Fin (a + a')) k) : Matrix (Fin m) (Fin a') k :=
  Matrix.of fun i j => X i (Fin.natAdd a j)

def IsGLO {n : ℕ} (g : Matrix (Fin n) (Fin n) k) : Prop := (∀ i j, g i j ∈ 𝒪[k]) ∧ valuation k g.det = 1


open Classical in
def stdA (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (X : Matrix (Fin a) (Fin (a + a')) k) : ℂ :=
  if h : (blk₁ X).det ≠ 0 ∧ IsGLO (blk₁ X) ∧ ∀ i j, blk₂ X i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
    (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ) else 0


open Classical in
def stdB (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (Y : Matrix (Fin a') (Fin (a + a')) k) : ℂ :=
  if h : (blk₂ Y).det ≠ 0 ∧ IsGLO (blk₂ Y) ∧ ∀ i j, blk₁ Y i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
    (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ) else 0


open Classical in
def unitInd (ν : kˣ →* ℂˣ) (y : k) : ℂ :=
  if h : y ≠ 0 ∧ valuation k y = 1 then (((ν (Units.mk0 y h.1))⁻¹ : ℂˣ) : ℂ) else 0

def sgn (s : ℤˣ) : kˣ := Units.map (Int.castRingHom k).toMonoidHom s

end Local

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end Glob

end GlobalTheory.StdPairCone
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNatDatumSquareFlip
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.FunObj.LocTensor

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem condLE_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) {e e' : ℕ} (he : e ≤ e') {χ : kˣ →* ℂˣ} (h : CondLE ϖ e χ) : CondLE ϖ e' χ :=
  fun x hx => h x ⟨hx.1, hx.2.trans (by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow]
    exact pow_le_pow_right_of_le_one' hϖ.mem he)⟩

theorem isNatDatum_squareFlip [MeasurableSpace k] [BorelSpace k] {A A' C : Type} [Fintype A] [DecidableEq A] [Fintype A']
    [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [hμ : μ.IsHaarMeasure] (σ : A ⊕ A' ≃ C)
    {ψ : AddChar k Circle} {α β : kˣ →* ℂˣ} {ϖ : kˣ} {e e' : ℕ} (h : IsRightTranslationIsometric ϖ ψ α β e) (he : e ≤ e') (P : Finset C)
    {Φ : Matrix A' C k → ℂ} (hΦ : IsNatDatum ϖ e' Φ) : IsNatDatum ϖ e' (squareFlip μ σ ψ (α / β) ϖ e' P Φ) := by
  refine (GlobalTheory.SplitFlip.FourierDepth.fourier_exchange k A C ψ⁻¹ ϖ e' Pᶜ h.unif h.inv.cond).2 _ ?_
  rw [← latA_blockLat]
  exact GlobalTheory.FrameDepth.hasDepth_phiA k A A' C μ (hμ := hμ) σ _ ϖ e' _ _ h.unif (h.one_le.trans he) (condLE_mono h.unif he h.condν)
    ((GlobalTheory.SplitFlip.FourierDepth.fourier_exchange k A' C ψ ϖ e' P h.unif h.cond).1 _ hΦ)

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}

theorem isNatDatum_flipAt (hL : L.Is μ₀) (W : G.Weil) {t : T} (i j : Fin D.R.m) {w : Pl D.host.E} (hw : w ∈ locPl G t)
    (hb : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) {n : ℕ} (hn : depthAt G w ≤ n)
    {Φ : Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ} (hΦ : IsNatDatum (unifAt w) n Φ) :
    IsNatDatum (unifAt w) n (flipAt W t i j w n Φ) := by
  have h1 := GivenAdm.givenLevel_open hL hw ((i : ℕ), (j : ℕ))
  have h2 := isOpen_map_invT h1.1 h1.2
  have := isHaarMeasure_haarVol h2.1 h2.2
  rw [flipAt, ← Grid.alpha_div_beta]
  exact isNatDatum_squareFlip _ _ ((Good.isGood_of_notMem hL W hw hb).square i i.2 j j.2) hn _ hΦ

theorem local_tensors (hL : L.Is μ₀) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) :
    (∃ e, IsIdemSum e (locPl G t)) ∧
    (∀ e, IsIdemSum e (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Φ, (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Φ w)) →
      ∃ τ : TotT G (routeSmall t i j),
        HasLocal B t e (X := (i, j + 1)) (M := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩
          (IsLocVec W (.mu t i j) e (ρ.vT i j)) (IsLocVec W (.chi i j) e (ρ.vX i j)) τ Φ) ∧
    (∀ e, IsIdemSum e (locPl G t) → ∀ (n : Pl D.host.E → ℕ) Φ, (∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (Φ w)) →
      ∃ τ : TotT G (routeBig t i j),
        HasLocal B t e (X := (i, j + 1)) (M := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩
          (IsLocVec W (.chi i (j + 1)) e (ρ.vX i (j + 1))) (IsLocVec W (.mu t (i + 1) j) e (ρ.vT (i + 1) j)) τ Φ) ∧
    ((∀ w ∈ locPl G t, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) →
      ∀ n Φ, (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) →
        ∃ τ τ', HasFlip B t ρ i j n Φ τ τ' ∧ ∀ b, ∃ a, ρ.Matched a b ∧ IsMatched B t ρ i j (tensT W a τ) (tensT W b τ')) := by
  refine ⟨exists_idemSum_locPl hL G t, fun e he n Φ h => exists_hasLocal_small B ρ t i j hL he h,
    fun e he n Φ h => exists_hasLocal_big B ρ t i j hL he h, fun hb n Φ h => ?_⟩
  obtain ⟨τ, τ', H⟩ := exists_hasFlip_of_nat B ρ t i j hL (fun w hw => (h w hw).2)
    fun w hw => isNatDatum_flipAt hL W i j hw (hb w hw) (h w hw).1 (h w hw).2
  refine ⟨τ, τ', H, fun b => ?_⟩
  obtain ⟨a, ha⟩ := ρ.exists_matched i j b
  exact ⟨a, ha t, a, b, τ, τ', n, Φ, ha t, h, H, rfl, rfl⟩

end GlobalTheory.FunObj.LocTensor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JUnifAndLUnifOfTieIn
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem jUnif_and_lUnif_of_tieIn : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → JUnif T R κ v₀ ∧ (GeoAct T R κ v₀ → (topR T R κ v₀).LUnif) := by
  intro h1 h2 D G _ _ Pl0 T0 A T _ R κ v₀ hL hM hT hpb hnV
  have hlp := GlobalTheory.HolDict.lastPos_of_kapIs D κ hT.kap
  exact ⟨_root_.GlobalTheory.UnifAll.unif_all h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hpb hlp hnV,
    _root_.GlobalTheory.HolDict.lUnif_topR_of_geoAct h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hpb hlp hnV⟩

end GlobalTheory.HolDict
end

