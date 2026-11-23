module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealDirectionThetaNonzero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.RealDirectionThetaNonzero

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def l2Sq {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f : WO S T → ℂ) : ℝ≥0∞ :=
  ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ

def l2InnerPairing {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f f' : WO S T → ℂ) : ℂ :=
  ∫ w in 𝓕, f w * starRingEnd ℂ (f' w) ∂μ

def IsRealDir {S T : HSp D} (L : ℝ →+ WO S T) : Prop :=
  Continuous L ∧ ∀ t, (L t).map (finPart D) = 0

def dHeis (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (L : ℝ →+ WO S T) (f : WO S T → ℂ) : WO S T → ℂ :=
  fun x => deriv (fun t : ℝ => heisO ψ S T (L t) f x) 0

def dHeisWord (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Ls : List (ℝ →+ WO S T)) (f : WO S T → ℂ) :
    WO S T → ℂ :=
  Ls.foldr (dHeis ψ S T) f

def HasLevel (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (U : AddSubgroup (WO S T)) (f : WO S T → ℂ) : Prop :=
  ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f

def IsThetaCont (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) →
    ∃ (words : List (List (ℝ →+ WO S T))) (C : ℝ), (∀ Ls ∈ words, ∀ L ∈ Ls, IsRealDir L) ∧
      ∀ f, IsThetaFunO ψ S T f → HasLevel ψ S T U f →
        ∀ B : ℝ, 0 ≤ B → (∀ Ls ∈ words, ∀ w, ‖dHeisWord ψ S T Ls f w‖ ≤ B) → ‖ℓ f‖ ≤ C * B

def Schur (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop :=
  ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
    ∀ A : Module.End ℂ (WO S T → ℂ),
      (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (A f)) →
      (∀ w f, IsThetaFunO ψ S T f → A (heisO ψ S T w f) = heisO ψ S T w (A f)) →
      (∃ C : ℝ≥0, ∀ f, IsThetaFunO ψ S T f → l2Sq μ 𝓕 (A f) ≤ (C : ℝ≥0∞) * l2Sq μ 𝓕 f) →
      ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T f → A f = c • f

def ThetaUnique (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop :=
  ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
    (∀ γ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (ratW T S γ) f) = ℓ f) →
    IsThetaCont ψ S T ℓ →
    ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T f → ℓ f = c * f 0

def CovolOneExists (S T : HSp D) : Prop :=
  ∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕

def HeisenbergLemma (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop :=
  ∀ (μ μ' : Measure (WO S T)) (𝓕 𝓕' : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → IsCovolOne (ratL T S) μ' 𝓕' →
    ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' →
      IntegrableOn (fun ξ => heisO ψ S T ξ f 0 * starRingEnd ℂ (heisO ψ S T ξ f' 0)) 𝓕 μ ∧
      IntegrableOn (fun w => f w * starRingEnd ℂ (f' w)) 𝓕' μ' ∧
      ∫ ξ in 𝓕, heisO ψ S T ξ f 0 * starRingEnd ℂ (heisO ψ S T ξ f' 0) ∂μ = l2InnerPairing μ' 𝓕' f f'

def ThetaNonzero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop :=
  ∃ f, IsThetaFunO ψ S T f ∧ f ≠ 0

def ThetaFactsAt (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop :=
  Schur ψ S T ∧ ThetaUnique ψ S T ∧ (CovolOneExists S T ∧ HeisenbergLemma ψ S T) ∧ ThetaNonzero ψ S T

def ThetaFacts (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → ∀ S T : HSp D, ThetaFactsAt ψ S T

theorem ThetaFacts.std (h : ThetaFacts D) {ψ : AddChar (AF D.host.F) ℂ} {s : ℤ} (hψ : IsStdChar D ψ s) (S T : HSp D) :
    ThetaFactsAt ψ S T := h ψ hψ.1 S T

theorem symplOH_zero_left (S T : HSp D) (y : WO S T) : symplOH S T 0 y = 0 := by
  simp [symplOH, symplO, hO]

theorem heisO_apply_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ξ : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T ξ f 0 = f ξ := by
  simp [heisO, symplOH_zero_left]

end GlobalTheory.IndefiniteRowSideFullHecke.RealDirectionThetaNonzero

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def compFin (D : D7) (w : HeightOneSpectrum (𝓞 D.host.F)) :
    Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F w ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)).toRingHom

def ExtUnramAt (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime], P.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 D.host.F) P

def CharUnramAt (D : D7) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → (∀ w, w ≠ v → compFin D w (finPart D (x : AE D)) = 1) →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def InStabAt (V : HSp D) (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (k : GA D V) : Prop :=
  (Formalism.L2.Theta.mt V k).map (infPart D) = 1 ∧
    (∀ w, w ≠ v → ((Formalism.L2.Theta.mt V k).map (finPart D)).map (compFin D w) = 1) ∧
    ∀ y, y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt V k).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E))

def VacFixedAt (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    CharUnramAt D χS v → CharUnramAt D χT v →
    ∀ (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
      IsSelfDualC S LS → IsSelfDualC T LT →
      ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
        IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) fun w => w = v) f →
        ∀ (k : GA D S) (k' : GA D T), InStabAt S LS v k → InStabAt T LT v k' → om (k, k') f = f

def VacFixed (D : D7) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.F), ExtUnramAt D v → VacFixedAt D v

theorem inStabAt_one (V : HSp D) (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (v : HeightOneSpectrum (𝓞 D.host.F)) : InStabAt V L v 1 := by
  have h : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
  refine ⟨?_, fun w _ => ?_, fun y => ?_⟩
  · rw [h]; exact Matrix.map_one _ (map_zero _) (map_one _)
  · rw [h, Matrix.map_one _ (map_zero _) (map_one _)]; exact Matrix.map_one _ (map_zero _) (map_one _)
  · rw [h, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

theorem isLatVac_at_of_all {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (hf : IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) f) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    IsLatVac (heisO ψ S T) (latO S T LS LT fun w => w = v) f := by
  have hle : (latO S T LS LT fun w => w = v) ≤ latO S T LS LT fun _ => True := by
    apply AddSubgroup.closure_mono
    rintro x ⟨α, hα, -, h⟩
    exact ⟨α, hα, fun w hw => absurd trivial hw, h⟩
  exact ⟨fun u hu => hf.1 u (hle hu), fun e he u hu => hf.2 e he u (hle hu)⟩

end GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def WeilDatumExists (D : D7) : Prop :=
  ∀ (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle),
    IsStdChar D ψ (-1) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank →
      ∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om

theorem weilDatumExists_iff (D : D7) :
    WeilDatumExists D ↔ ∀ (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle),
      ((∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om) ↔
        IsStdChar D ψ (-1) ∧ IsHeckeChar D χS ∧ IsHeckeChar D χT ∧ ResEta D χS S.rank ∧ ResEta D χT T.rank) := by
  constructor
  · intro h S T ψ χS χT
    constructor
    · rintro ⟨om, H⟩
      exact ⟨H.std, H.hecS, H.hecT, H.resS, H.resT⟩
    · rintro ⟨hψ, h1, h2, h3, h4⟩
      exact h S T ψ χS χT hψ h1 h2 h3 h4
  · intro h S T ψ χS χT hψ h1 h2 h3 h4
    exact (h S T ψ χS χT).2 ⟨hψ, h1, h2, h3, h4⟩

end GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumUniqueness
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion

variable {D : D7}

def TrivOnF (D : D7) (ξ : (AE D)ˣ →* Circle) : Prop := ∀ a : (AF D.host.F)ˣ, ξ (idF D a) = 1

def IsTildeDet (V : HSp D) (ξ : (AE D)ˣ →* Circle) (g : GA D V) (c : Circle) : Prop :=
  (∃ x, IsDetRoot V g x) ∧ ∀ x, IsDetRoot V g x → ξ x = c

def WeilDatumUnique (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS χT om' →
      ∀ (g : GA D S) (h : GA D T) (f : WO S T → ℂ), IsThetaFunO ψ S T f → om' (g, h) f = om (g, h) f

def WeilDatumTwist (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT ξ ξ' : (AE D)ˣ →* Circle)
    (om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    TrivOnF D ξ → TrivOnF D ξ' →
    IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T (χS * ξ) (χT * ξ') om' →
      ∀ (g : GA D S) (h : GA D T), ∃ a b : Circle, IsTildeDet S ξ' g a ∧ IsTildeDet T ξ h b ∧
        ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
          om' (g, h) f = ((a⁻¹ * b : Circle) : ℂ) • om (g, h) f

def WeilDatumDetermined (D : D7) : Prop := WeilDatumUnique D ∧ WeilDatumTwist D

theorem IsTildeDet.at_one {V : HSp D} {ξ : (AE D)ˣ →* Circle} {c : Circle} (h : IsTildeDet V ξ 1 c) : c = 1 := by
  have h1 : IsDetRoot V 1 1 := by simp [IsDetRoot]
  rw [← h.2 1 h1, map_one]

theorem WeilDatumTwist.unique (H : WeilDatumTwist D) : WeilDatumUnique D := by
  intro ψ S T χS χT om om' h h' g k f hf
  obtain ⟨a, b, ha, hb, e⟩ := H ψ S T χS χT 1 1 om om' (fun _ => rfl) (fun _ => rfl) h
    (by simpa using h') g k
  obtain ⟨x, hx⟩ := ha.1
  obtain ⟨y, hy⟩ := hb.1
  have ha1 : a = 1 := (ha.2 x hx).symm
  have hb1 : b = 1 := (hb.2 y hy).symm
  simpa [ha1, hb1] using e f hf

end GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion

end
end

