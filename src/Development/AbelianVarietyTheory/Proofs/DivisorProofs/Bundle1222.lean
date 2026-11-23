module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0157
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFormAniso
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

namespace GlobalTheory.BottomRallis

variable {D : D7}

def SiegelWeilFockAniso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → A.rank < B.rank → wittIndex B = 0 →
  ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a →
  ∀ (θ : InfFam D) (sS : RealMat (dblSp A)) (sB : RealMat B), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) →
    (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
      sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) →
  ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 →
  ∀ mH : Measure (GA D B), mH.IsHaarMeasure →
  ∀ φ : WO (dblSp A) B → ℂ, IsFockVec ψ θ (dblSp A) B sS sB φ →
    (∀ g, Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧
    Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 φ) (sZero A B)) (sZero A B) (ThetaMean.thetaMean omh mH φ)

def GlobalFormAnisoAt (A : HSp D) (L : Lat A) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → wittIndex B = 0 →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA,
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    (∀ s : ℂ, (A.rank : ℝ) / 2 < s.re → Integrable (integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ s) m) ∧
    ∃ z, HolValueAt (fun s => ∫ g, integrand om m ν 𝓕 L a Φ₁ Φ₂ u₁ u₂ s g ∂m) (sZero A B) z ∧
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) = volQ B mH * z

def GlobalFormAniso (D : D7) : Prop := ∀ (A : HSp D) (L : Lat A), IsSelfDualC A L → GlobalFormAnisoAt A L

def HeckeFormAniso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → wittIndex B = 0 →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ),
    IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : LFun.Fam D.host.E,
    LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ →
    (∃ s₁ : ℝ, s₁ < (t : ℝ) / 2 ∧ IntegrableOn (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s₁) (openOff A LA Sf) m) →
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m ∧
    ∀ l, HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) ((t : ℂ) / 2) l →
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) =
        volQ B mH * (l / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank ((t : ℂ) / 2)) *
          ∫ g in openOff A LA Sf, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m

def trivPar (a : ℕ) : LFun.Fam D.host.E := LFun.segFam (fun _ => 1) a

end GlobalTheory.BottomRallis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAniso
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RallisBottom

open GlobalTheory.Core.Rk.IP

variable {D : D7}

def HeckeFormAniso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A)
    (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B))
    (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → wittIndex B = 0 →
  ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ),
    IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ →
  ∀ (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure →
  ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : LFun.Fam D.host.E,
    LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ →
    (∃ s₁ : ℝ, s₁ < (t : ℝ) / 2 ∧ IntegrableOn (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s₁) (openOff A LA Sf) m) →
    UpConv om m mH Φ₁ u₁ ∧ UpConv om m mH Φ₂ u₂ ∧
    IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m ∧
    ∀ l, HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) ((t : ℂ) / 2) l →
      petersson B mH (up om m Φ₁ u₁) (up om m Φ₂ u₂) =
        volQ B mH * (l / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank ((t : ℂ) / 2)) *
          ∫ g in openOff A LA Sf, wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g ∂m

end GlobalTheory.RallisBottom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoArchimedeanAdelicPureTensor
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.ArchHeisPure

open scoped Classical Matrix

theorem exists_phase_translate {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (a : V)
    (f : SchwartzMap V ℂ) : ∃ g : SchwartzMap V ℂ, ∀ x,
      g x = Complex.exp (-(2 * Real.pi * Complex.I) * ((L x + c : ℝ) : ℂ)) * f (x + a) := by
  refine ⟨SchwartzMap.smulLeftCLM ℂ (GlobalTheory.LinPhaseSeminorm.phaseLine c 1 ∘ ⇑L) (SchwartzMap.compSubConstCLM ℂ (-a) f),
    fun x => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.LinPhaseSeminorm.hasTemperateGrowth_phase L c 1),
    ← GlobalTheory.LinPhaseSeminorm.phase_eq]
  simp

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]


variable (F) in
def evHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

def trForm (c : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c)
      map_add' := fun y y' => by rw [add_dotProduct, map_add (f := _)]
      map_smul' := fun r y => by rw [smul_dotProduct, map_smul]; rfl }

theorem evHom_apply (a : AF F) : evHom F a = evI F a := rfl

theorem trForm_apply (c y : κ → mixedEmbedding.mixedSpace F) :
    trForm c y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c) := rfl

theorem schr_pureA [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {w : (κ → AF F) × (κ → AF F)}
    (hw : At (evI F) w) (f : SInf F κ) :
    ∃ f₁ : SInf F κ, ∀ h : (κ → Af F) → ℂ, schr ψ w (pureA F f h) = pureA F f₁ h := by
  obtain ⟨p, q⟩ := w
  obtain ⟨g, hg⟩ := exists_phase_translate (trForm fun i => evI F (q i))
    (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (p ⬝ᵥ q)))) (fun i => evI F (p i)) f
  refine ⟨g, fun h => funext fun x => ?_⟩
  have hfin : (fun i => ((x + p) i).2) = fun i => (x i).2 := by
    funext i
    have h0 : evI F ((0, 1) : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    have h1 : (1 : Af F) * (p i).2 = 0 := congrArg (fun z : (κ → AF F) × (κ → AF F) => (z.1 i).2) (hw _ h0)
    change (x i).2 + (p i).2 = _
    rw [one_mul] at h1
    rw [h1, add_zero]
  have harch : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + p) i).1) =
      (fun i => evI F (x i)) + fun i => evI F (p i) := by
    funext i
    exact map_add (evHom F) (x i) (p i)
  have hAt : At (evI F) (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q)) := by
    intro v hv
    have hq : v • q = 0 := congrArg Prod.snd (hw v hv)
    rw [smul_add, ← dotProduct_smul, smul_eq_mul, mul_left_comm, ← smul_eq_mul v, ← dotProduct_smul, hq]
    simp
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q))) =
      trForm (fun i => evI F (q i)) (fun i => evI F (x i)) +
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (p ⬝ᵥ q))) := by
    rw [← evHom_apply, map_add (f := _), map_add (f := _), RingHom.map_dotProduct, trForm_apply]
    rfl
  simp only [schr, pureA]
  rw [hψ.2.2 _ hAt, htr, hfin, harch, ← mul_assoc, ← hg]
  rfl

theorem rho_pureA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    IsStd ψ → ∀ u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → ∀ f : SInf F κ,
      ∃ f₁ : SInf F κ, ∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d hψ u hu f
  refine schr_pureA hψ (fun r hr => ?_) f
  rw [← map_smul, hu r hr, map_zero]

end GlobalTheory.ArchHeisPure

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoSplitArchimedeanFinite
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.HeisSplit

theorem schr_add_of_orth {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a b : (κ → R) × (κ → R)) (h1 : a.1 ⬝ᵥ b.2 = 0) (h2 : b.1 ⬝ᵥ a.2 = 0) (φ : (κ → R) → ℂ) :
    schr ψ (a + b) φ = schr ψ a (schr ψ b φ) := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add, h1, h2]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  ring

theorem dot_eq_zero {R : Type} [CommRing R] {κ : Type} [Fintype κ] (e : R) (a c : κ → R) (h : e • a = 0) :
    a ⬝ᵥ (e • c) = 0 := by
  rw [dotProduct_smul, ← smul_dotProduct, h, zero_dotProduct]

section

variable (F : Type) [Field F] [NumberField F]

noncomputable def finAd (z : Af F) : AF F := ((0 : InfiniteAdeleRing F), z)

theorem finAd_mul (x : AF F) : finAd F x.2 * finAd F 1 = x * finAd F 1 := by
  refine Prod.ext ?_ ?_
  · show (0 : InfiniteAdeleRing F) * 0 = x.1 * 0
    simp
  · rfl

theorem finAd_idem : finAd F 1 * finAd F 1 = finAd F 1 := by
  refine Prod.ext ?_ ?_
  · show (0 : InfiniteAdeleRing F) * 0 = 0
    simp
  · show (1 : Af F) * 1 = 1
    simp

theorem evI_finAd : evI F (finAd F 1) = 0 := by
  exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem mul_finAd_of (t : AF F) (ht : evI F t = 0) : t * finAd F 1 = t := by
  have h : t.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 ht
  refine Prod.ext ?_ ?_
  · show t.1 * 0 = t.1
    simp [h]
  · show t.2 * 1 = t.2
    simp

theorem schr_pureA [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (c : (κ → AF F) × (κ → AF F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (h : (κ → Af F) → ℂ) :
    schr ψ (finAd F 1 • c) (pureA F f h) =
      pureA F f (fun z => schr ψ (finAd F 1 • c) (fun x => h fun i => (x i).2) fun i => finAd F (z i)) := by
  funext x
  have e1 : (fun i => finAd F (x i).2) ⬝ᵥ (finAd F 1 • c).2 = x ⬝ᵥ (finAd F 1 • c).2 := by
    simp only [dotProduct, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, ← mul_assoc, finAd_mul]
  have e2 : ∀ i, ((x + (finAd F 1 • c).1) i).1 = (x i).1 := by
    intro i
    show (x i).1 + 0 * (c.1 i).1 = (x i).1
    simp
  have e3 : ∀ i, (((fun i => finAd F (x i).2) + (finAd F 1 • c).1) i).2 = ((x + (finAd F 1 • c).1) i).2 := fun i => rfl
  simp only [schr, pureA, e1, e2, e3]
  ring

end

theorem rho_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    ∀ w : Matrix α β (AE F E),
    ∃ (u : Matrix α β (AE F E)) (H : ((κ → Af F) → ℂ) → (κ → Af F) → ℂ), At (evI F) u ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        ∀ (f f₁ : SInf F κ) (h : (κ → Af F) → ℂ),
          (∀ h' : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F f h') = pureA F f₁ h') →
            d.rho ψ (actB (cA σ) g w) (pureA F f h) = pureA F f₁ (H h) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d w
  have hu : finAd F 1 • (w - finAd F 1 • w) = 0 := by
    rw [smul_sub, smul_smul, finAd_idem, sub_self]
  refine ⟨w - finAd F 1 • w,
    fun h z => schr ψ (finAd F 1 • d.e w) (fun x => h fun i => (x i).2) fun i => finAd F (z i), ?_, ?_⟩
  · intro t ht
    rw [smul_sub, smul_smul, mul_finAd_of F t ht, sub_self]
  · intro g hg f f₁ h hyp
    have hg' := hg _ (evI_finAd F)
    rw [smul_sub, sub_eq_zero] at hg'
    have hv : actB (cA σ) g (finAd F 1 • w) = finAd F 1 • w := by
      unfold actB
      rw [Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.transpose_smul, hg', Matrix.transpose_smul, Matrix.transpose_one,
        Matrix.mul_smul, Matrix.mul_one]
    have hw : actB (cA σ) g w = actB (cA σ) g (w - finAd F 1 • w) + finAd F 1 • w := by
      have : actB (cA σ) g (w - finAd F 1 • w) = actB (cA σ) g w - actB (cA σ) g (finAd F 1 • w) := by
        unfold actB
        rw [Matrix.sub_mul]
      rw [this, hv, sub_add_cancel]
    have ha : finAd F 1 • d.e (actB (cA σ) g (w - finAd F 1 • w)) = 0 := by
      rw [← map_smul]
      unfold actB
      rw [← Matrix.smul_mul, hu, Matrix.zero_mul, map_zero]
    rw [← hyp, hw]
    unfold Darboux.rho
    rw [map_add (f := _), map_smul, schr_add_of_orth, schr_pureA]
    · exact dot_eq_zero _ _ _ (congrArg Prod.fst ha)
    · rw [dotProduct_comm]
      exact dot_eq_zero _ _ _ (congrArg Prod.snd ha)

end GlobalTheory.HeisSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyTwistBoundOfRegularSectionStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.higherCohomology_twist_bound_of_regular_section : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X) (hL : L.IsLB), (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ p : ℕ, 1 ≤ p → ∀ s : (lbPow L p).Sec, Mono (cutHom F (isLB_lbPow hL p) s) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @GlobalTheory.hdim_twist_pow_le_of_regular_section | exact GlobalTheory.hdim_twist_pow_le_of_regular_section | (intros; apply GlobalTheory.hdim_twist_pow_le_of_regular_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyTwistBoundOfTwoCutsStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.higherCohomology_twist_bound_of_two_cuts : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @GlobalTheory.hdim_twist_lbPow_le_of_two_le | exact GlobalTheory.hdim_twist_lbPow_le_of_two_le | (intros; apply GlobalTheory.hdim_twist_lbPow_le_of_two_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertModelConjugationAntilinearBijection
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjHilb

theorem nonempty_antilinear {H H' Y : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H']
    (ev : H → Y → ℂ) (ev' : H' → Y → ℂ)
    (ha : ∀ a b g, ev (a + b) g = ev a g + ev b g) (hs : ∀ (z : ℂ) a g, ev (z • a) g = z * ev a g)
    (ha' : ∀ a b g, ev' (a + b) g = ev' a g + ev' b g) (hs' : ∀ (z : ℂ) a g, ev' (z • a) g = z * ev' a g)
    (hinj : Function.Injective ev) (hinj' : Function.Injective ev')
    (hx : ∀ y, ∃ x, ∀ g, ev' x g = starRingEnd ℂ (ev y g)) (hy : ∀ x, ∃ y, ∀ g, ev y g = starRingEnd ℂ (ev' x g)) :
    Nonempty (H' ≃ₗ⋆[ℂ] H) := by
  choose x hx using hx
  choose y hy using hy
  exact ⟨{ toFun := y
           invFun := x
           map_add' := fun a b => hinj (funext fun g => by rw [ha, hy, hy, hy, ha', map_add (f := _)])
           map_smul' := fun z a => hinj (funext fun g => by rw [hs, hy, hy, hs', map_mul])
           left_inv := fun a => hinj' (funext fun g => by rw [hx, hy, Complex.conj_conj])
           right_inv := fun a => hinj (funext fun g => by rw [hy, hx, Complex.conj_conj]) }⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_conj_value (R : RealDat D A Ks) (hm : R.models_HW) (i : Fin D.R.m) (σ σ' : D.what₂.LL →+* ℂ)
    (c : ∀ τ, (R.MW i σ).H τ ≃ₗᵢ⋆[ℂ] (R.MW i σ').H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) τ), ∀ w, c τ ((R.MW i σ).rep τ g w) = (R.MW i σ').rep τ g (c τ w))
    (v : (R.MW i σ).Vec) (v' : (R.MW i σ').Vec) (hv : ∀ τ, (v' τ : (R.MW i σ').H τ) = c τ (v τ)) (y : (R.HW i σ').H) :
    ∃ x : (R.HW i σ).H, ∀ g, evAt R i σ v x g = starRingEnd ℂ (evAt R i σ' v' y g) := by
  obtain ⟨-, hmul⟩ := GlobalTheory.ConjMult.conj_mult R.θ (R.MW i σ') (R.MW i σ) c hc
  have hχ : (fun k => star (levChi _ (R.βW i) (R.datWp i R.triv) k)) = levChi _ (R.βW i) (R.datWp i R.triv) := by
    funext k
    rw [GlobalTheory.ConjEval.levChi_principal, star_one]
  have h1 : (R.HW i σ').e y ∈ R.Wall i σ' := (hm i _).2.1 ▸ LinearMap.mem_range_self _ y
  obtain ⟨T', hT', h2⟩ := hmul _ _ _ h1
  rw [hχ] at hT'
  obtain ⟨x, rfl⟩ : T' ∈ LinearMap.range (R.HW i σ).e := (hm i σ).2.1.symm ▸ hT'
  exact ⟨x, h2 v _ hv⟩

theorem evAt_inj (R : RealDat D A Ks) (hm : R.models_HW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec)
    (hv : IsUnitV v) : Function.Injective (evAt R i σ v) :=
  GlobalTheory.EvalInj.evAt_injective_of_ne R hm i σ v fun τ h => by
    have := hv τ
    rw [h, norm_zero] at this
    exact zero_ne_one this

theorem conj_hilbert : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → (∀ i σ, ¬ GoodEmb T.Q.c (res T σ) → Nonempty ((R.HW i σ).H ≃ₗ⋆[ℂ] (R.HW i ((starRingEnd ℂ).comp σ)).H)) ∧ (JEvExists T R κ v₀ → JEvBar T R κ) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hM ht
  have hm := hM.HW
  have hadd : ∀ i (σ' : D.what₂.LL →+* ℂ) (u : (R.MW i σ').Vec) a b g,
      evAt R i σ' u (a + b) g = evAt R i σ' u a g + evAt R i σ' u b g := fun i σ' u a b g => by
    simp [evAt]
  have hsmul : ∀ i (σ' : D.what₂.LL →+* ℂ) (u : (R.MW i σ').Vec) (z : ℂ) a g,
      evAt R i σ' u (z • a) g = z * evAt R i σ' u a g := fun i σ' u z a g => by
    simp [evAt]
  have key : ∀ i σ, ¬ GoodEmb T.Q.c (res T σ) → ∃ v : (R.MW i σ).Vec, IsUnitV v ∧
      (∀ y, ∃ x, ∀ g, evAt R i σ v x g = starRingEnd ℂ (evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) y g)) ∧
      ∀ x, ∃ y, ∀ g, evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) y g = starRingEnd ℂ (evAt R i σ v x g) := by
    intro i σ hσ
    obtain ⟨c, hc⟩ := _root_.GlobalTheory.ConjEq.exists_conj_equiv D G Pl0 T0 A T R κ v₀ hM ht i σ hσ
    obtain ⟨hsm, -⟩ := GlobalTheory.ConjMult.conj_mult R.θ (R.MW i ((starRingEnd ℂ).comp σ)) (R.MW i σ) c hc
    let v : (R.MW i σ).Vec := fun τ => ⟨(c τ).symm (v₀ i ((starRingEnd ℂ).comp σ) τ), (hsm τ _).2 (by
      rw [LinearIsometryEquiv.apply_symm_apply]; exact (v₀ i ((starRingEnd ℂ).comp σ) τ).2)⟩
    refine ⟨v, fun τ => ((c τ).symm.norm_map _).trans ((ht.hv₀ i _).norm R τ),
      exists_conj_value R hm i σ _ c hc v _ fun τ => ((c τ).apply_symm_apply _).symm,
      exists_conj_value R hm i _ σ (fun τ => (c τ).symm) (fun τ g hg w => (c τ).injective ?_) _ v fun τ => rfl⟩
    rw [hc τ g hg, (c τ).apply_symm_apply, (c τ).apply_symm_apply]
  refine ⟨fun i σ hσ => ?_, fun hJ i σ hσ hV => ?_⟩
  · obtain ⟨v, hv, hx, hy⟩ := key i σ hσ
    exact nonempty_antilinear _ _ (hadd _ _ _) (hsmul _ _ _) (hadd _ _ _) (hsmul _ _ _)
      (evAt_inj R hm i _ _ fun τ => (ht.hv₀ i _).norm R τ) (evAt_inj R hm i σ v hv) hx hy
  · obtain ⟨v, hv, hx, -⟩ := key i σ hσ
    exact ⟨v, hv, GlobalTheory.ConjEval.evEx_conj (res T σ) _ _ (hadd _ _ _) (hsmul _ _ _) (hadd _ _ _) (hsmul _ _ _)
      (evAt_inj R hm i σ v hv) hx _ (hJ i ((starRingEnd ℂ).comp σ) (good_resC T hσ) hV)⟩

end GlobalTheory.ConjHilb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnOffCoordinateHyperplanesOfPoincareBo
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integrableOn_offHyp_of_norm_le_poin {n : ℕ} (S : Finset (Fin n)) (U K : Set (V n)) (g : V n → ℂ) (C : ℝ)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hs : ∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2)
    (hg : ContinuousOn g (offHyp S U)) (h0 : ∀ v ∈ offHyp S U, v ∉ K → g v = 0)
    (hb : ∀ v ∈ offHyp S U, v ∈ K → ‖g v‖ ≤ C * ∏ a, (poinWt S v a)⁻¹ ^ 2) :
    IntegrableOn g (offHyp S U) := by
  have hO : MeasurableSet (offHyp S U) := (isOpen_offHyp_of_isOpen S U hU).measurableSet
  have hv : IntegrableOn (fun v => C * ∏ a, (poinWt S v a)⁻¹ ^ 2) K :=
    (GlobalTheory.T.poincare_volume_integrableOn_compact_punctured_polydisc S K hK fun v hv => hs v (hKU hv)).const_mul C
  have hi : Integrable (K.indicator fun v => C * ∏ a, (poinWt S v a)⁻¹ ^ 2) :=
    (integrable_indicator_iff hK.measurableSet).2 hv
  refine Integrable.mono' hi.integrableOn (hg.aestronglyMeasurable hO) ?_
  refine (ae_restrict_iff' hO).2 (Eventually.of_forall fun v hvO => ?_)
  by_cases hvK : v ∈ K
  · rw [Set.indicator_of_mem hvK]
    exact hb v hvO hvK
  · rw [Set.indicator_of_notMem hvK, h0 v hvO hvK, norm_zero]

end GlobalTheory.GoodTop
end

