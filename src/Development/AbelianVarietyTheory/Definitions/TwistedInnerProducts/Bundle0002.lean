module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsStdIsVacVec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField

namespace GlobalTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exp_of_even {k : Fin D.R.m} (hk : Even (k : ℕ)) (τ : D.what₂.Tau) :
    expS D k τ = -(D.hc τ).e k - 1 / 2 ∧ expT D k τ = -(D.hc τ).e k := by
  simp [expS, expT, hk]

theorem exp_of_odd {k : Fin D.R.m} (hk : ¬ Even (k : ℕ)) (τ : D.what₂.Tau) :
    expS D k τ = -(D.hc τ).e k ∧ expT D k τ = -(D.hc τ).e k - 1 / 2 := by
  simp [expS, expT, hk]

theorem hasInfExp_div {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a b : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ b) : HasInfExp D (χ * η⁻¹) τ (a - b) := by
  obtain ⟨n, hn, h1, h2⟩ := hχ
  obtain ⟨m, hm, -, h3⟩ := hη
  refine ⟨n - m, by push_cast; rw [hn, hm]; ring, h1, fun θ hθ x hx hτ => ?_⟩
  have e1 := h2 θ hθ x hx hτ
  have e2 := h3 θ hθ x hx hτ
  set z : ℂ := θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ) with hz
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv, e1, e2]
  by_cases h0 : z = 0
  · have a1 : n = 0 := by
      by_contra h; exact (χ x).coe_ne_zero (by rw [e1, h0, zero_zpow _ h])
    have a2 : m = 0 := by
      by_contra h; exact (η x).coe_ne_zero (by rw [e2, h0, zero_zpow _ h])
    simp [a1, a2]
  · rw [zpow_sub₀ h0, div_eq_mul_inv]

theorem isHeckeChar_div {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) :
    IsHeckeChar D (χ * η⁻¹) :=
  ⟨hχ.1.mul hη.1.inv, fun x => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχ.2, hη.2]; simp⟩

end GlobalTheory.Chain

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.Size GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open scoped ENNReal

namespace GlobalTheory.ChainFr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure Fr (V : HSp D) where

  ε : D.what₂.Tau → Fin V.rank → Bool

  fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ
  fr_unit : ∀ τ, IsUnit (fr τ)
  fr_gram : ∀ τ, (fr τ)ᴴ * Formalism.REAL.Jm (ε τ) * fr τ = gramAt D V τ

namespace Fr

variable {V : HSp D}

def ofModel {S : D.what₂.Tau → SPar} (M : DSModel V S) : Fr V := ⟨M.ε, M.fr, M.fr_unit, M.fr_gram⟩

def cart (A : Fr V) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * A.fr τ

def onb (A : Fr V) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ := (A.fr τ)⁻¹

def elt (θ : InfFam D) (A : Fr V) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  atTau θ V τ ((A.fr τ)⁻¹ * g * A.fr τ)

end Fr

section Clauses

variable {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)

def ptF (f : WO V W → ℂ) : PolF D W.rank V.rank → (WO V W → ℂ) :=
  pureTensorO ψ θ V W A.cart B.cart A.onb B.onb f

def IsVacF (f : WO V W → ℂ) : Prop :=
  IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) f

variable (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau)

def LieFockWith (κS : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ) (κT : Matrix (Fin W.rank) (Fin W.rank) ℂ → ℂ) : Prop :=
  (∀ X ∈ lieAt V τ, ∀ (P : PolF D W.rank V.rank) (z : WO V W),
    HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (ptF ψ θ A B f P) z)
      (ptF ψ θ A B f (fockS τ (A.ε τ) (B.ε τ) ((A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P + κS X • P) z) 0) ∧
  ∀ Y ∈ lieAt W τ, ∀ (P : PolF D W.rank V.rank) (z : WO V W),
    HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (ptF ψ θ A B f P) z)
      (ptF ψ θ A B f (fockT τ (A.ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) P + κT Y • P) z) 0

def CompactFockF (aS aT : ℚ) : Prop :=
  ∃ x y : Bool → ℤ, (∀ j, (x (A.ε τ j) : ℚ) = wtS (B.ε τ) aT (A.ε τ j)) ∧
    (∀ i, (y (B.ε τ i) : ℚ) = wtT (A.ε τ) aS (B.ε τ i)) ∧
    ∀ h ∈ Formalism.REAL.Kset (A.ε τ), ∀ k ∈ Formalism.REAL.Kset (B.ε τ), ∀ P : PolF D W.rank V.rank,
      ω (A.elt θ τ h, B.elt θ τ k) (ptF ψ θ A B f P) =
        (signBlockDeterminant (A.ε τ) true h ^ x true * signBlockDeterminant (A.ε τ) false h ^ x false *
          (signBlockDeterminant (B.ε τ) true k ^ y true * signBlockDeterminant (B.ε τ) false k ^ y false)) •
          ptF ψ θ A B f (subst τ (A.ε τ) (B.ε τ) (h.map (starRingEnd ℂ)) k P)

end Clauses

def LieFockUpTo (D : D7) : Prop :=
  ∀ (V W : HSp D) (A : Fr V) (B : Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω →
    ∃ κS κT, ∀ f, IsVacF ψ θ A B f → LieFockWith ψ θ A B ω f τ κS κT

def LieFockAll (D : D7) : Prop :=
  ∀ (V W : HSp D) (A : Fr V) (B : Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ),
    IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → HasInfExp D χS τ aS → HasInfExp D χT τ aT → IsVacF ψ θ A B f →
      LieFockWith ψ θ A B ω f τ (fun X => -((aT : ℂ) * X.trace)) fun Y => (aS : ℂ) * Y.trace

def CompactFockAll (D : D7) : Prop :=
  ∀ (V W : HSp D) (A : Fr V) (B : Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ),
    IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → HasInfExp D χS τ aS → HasInfExp D χT τ aT → IsVacF ψ θ A B f → f ≠ 0 →
      CompactFockF ψ θ A B ω f τ aS aT

def fockSpan {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)
    (U : AddSubgroup (WO V W)) : Submodule ℂ (WO V W → ℂ) :=
  Submodule.span ℂ {g | ∃ f₀ P, IsVacF ψ θ A B f₀ ∧ f₀ ∈ thetaLevel ψ V W U ∧ g = ptF ψ θ A B f₀ P}

def FockDense (D : D7) : Prop :=
  ∀ (V W : HSp D) (A : Fr V) (B : Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ f, IsThetaFunO ψ V W f →
      ∃ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) ∧ f ∈ thetaLevel ψ V W U ∧
        ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g ∈ fockSpan ψ θ A B U, g ∈ thetaLevel ψ V W U ∧ sobO ψ θ μ 𝓕 d (f - g) < δ

def LowVanishFock (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (i : ℕ) (V' W : HSp D) (M' : DSModel W (parB (Ptw D) (k + 1)))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    1 ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered (parB (Ptw D) k) i V' →
    ∀ ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ), IsStepWeil k ψ V' W ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ (J : Set (GA D W)) (χ : GA D W → ℂ), ∀ F ∈ MultT θ M' J χ, ∀ (v : SmT M') (A : Fr V') (f₀ : WO V' W → ℂ),
      IsVacF ψ θ A (Fr.ofModel M') f₀ → ∀ P,
        Lift.liftInt ν 𝓕 (thetaKO ω') (ptF ψ θ A (Fr.ofModel M') f₀ P) (F v) = 0

theorem ptF_ofModel {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ) :
    ptF ψ θ (Fr.ofModel M) (Fr.ofModel M') f = ptOf ψ θ M M' f := rfl

theorem isVacF_of_isVacVec {V W : HSp D} {S S' : D.what₂.Tau → SPar} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {M : DSModel V S} {M' : DSModel W S'} {f : WO V W → ℂ} (h : IsVacVec ψ θ M M' f) :
    IsVacF ψ θ (Fr.ofModel M) (Fr.ofModel M') f := ⟨h.theta, h.vac⟩

end GlobalTheory.ChainFr

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MixedModelTargetHeisenbergAnisotropicPart
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixModel.Check

open GlobalTheory.OrientedHeis HypDec

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem symplOH_add_self (S T : HSp D) (x y : WO S T) : symplOH S T x y + symplOH S T x y = symplO S T x y := by
  rw [symplOH, ← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

section Source

variable {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ))

theorem mixS_eq (f : WO S T → ℂ) (x : Mx D T.rank ρ) (w₀ : WO S₀ T) : d.mixS T ψ μ 𝓕 f x w₀ =
    ∫ a in 𝓕, ψ (symplOH S T (d.extY T a) (d.extX T x)) * f (d.extY T a + d.extX T x + d.ext0 T w₀) ∂μ := by
  simp only [mixS, integrandS_eq]

theorem mixS_heis_extX (f : WO S T → ℂ) (u x : Mx D T.rank ρ) :
    d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T u) f) x = d.mixS T ψ μ 𝓕 f (x + u) := by
  funext w₀
  have h : symplOH S T (d.ext0 T w₀) (d.extX T u) = 0 := by rw [symplOH_skew, wittDecomp_sympl_extIsotropic_extAnisotropic, neg_zero]
  simp only [mixS_eq, heisO, map_add (d.extX T), symplOH_add_left, symplOH_add_right, symplOH_extX_extX, h, add_zero,
    AddChar.map_add_eq_mul, mul_assoc]
  congr 1; funext a; congr 3; abel

theorem mixedModelSource_heisenberg_anisotropic_part (f : WO S T → ℂ) (u : WO S₀ T) (x : Mx D T.rank ρ) :
    d.mixS T ψ μ 𝓕 (heisO ψ S T (d.ext0 T u) f) x = heisO ψ S₀ T u (d.mixS T ψ μ 𝓕 f x) := by
  funext w₀
  simp only [mixS_eq, heisO, map_add (d.ext0 T), symplOH_add_left, wittDecomp_sympl_extIsotropic_extAnisotropic, wittDecomp_sympl_extDual_extAnisotropic,
    wittDecomp_sympl_extAnisotropic_extAnisotropic, zero_add, ← integral_const_mul, add_assoc]
  congr 1; funext a; ring

variable {μ 𝓕}

theorem mixS_heis_extY (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (y x : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extY T y) f) x w₀ =
      ψ (symplO S T (d.extX T x) (d.extY T y)) * d.mixS T ψ μ 𝓕 f x w₀ := by
  have h : symplOH S T (d.ext0 T w₀) (d.extY T y) = 0 := by rw [symplOH_skew, wittDecomp_sympl_extDual_extAnisotropic, neg_zero]
  have h2 := covolOne_integral_add hμ
    (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) f)) 0)
    (d.integrandS_periodic hf x w₀) y
  rw [mixS, mixS, ← h2, ← integral_const_mul]
  congr 1; funext a
  simp only [integrandS_eq]
  simp only [heisO, map_add (d.extY T), symplOH_add_left, symplOH_extY_extY, h, add_zero, zero_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, ← symplOH_add_self, symplOH_skew S T (d.extX T x) (d.extY T y)]
  congr 2
  · abel
  · abel

theorem mixS_quasi (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (x : Mx D T.rank ρ) (γ : Matrix (Fin T.rank) (Fin S₀.rank) D.host.E) (w₀ : WO S₀ T) :
    d.mixS T ψ μ 𝓕 f x (ratW T S₀ γ + w₀) = ψ (-(symplOH S₀ T (ratW T S₀ γ) w₀)) * d.mixS T ψ μ 𝓕 f x w₀ := by
  obtain ⟨δ, hδ⟩ : d.ext0 T (ratW T S₀ γ) ∈ ratMx D _ _ := ratMx_mul (rat_mem γ) (rat_mem _)
  simp only [mixS_eq, ← integral_const_mul]
  congr 1; funext a
  have h := hf.quasi δ (d.extY T a + d.extX T x + d.ext0 T w₀)
  rw [show ratW T S δ = d.ext0 T (ratW T S₀ γ) from hδ] at h
  have h1 : symplOH S T (d.ext0 T (ratW T S₀ γ)) (d.extY T a) = 0 := by rw [symplOH_skew, wittDecomp_sympl_extDual_extAnisotropic, neg_zero]
  have h2 : symplOH S T (d.ext0 T (ratW T S₀ γ)) (d.extX T x) = 0 := by rw [symplOH_skew, wittDecomp_sympl_extIsotropic_extAnisotropic, neg_zero]
  rw [symplOH_add_right, symplOH_add_right, h1, h2, wittDecomp_sympl_extAnisotropic_extAnisotropic, zero_add, zero_add] at h
  rw [map_add (d.ext0 T), show d.extY T a + d.extX T x + (d.ext0 T (ratW T S₀ γ) + d.ext0 T w₀) =
    d.ext0 T (ratW T S₀ γ) + (d.extY T a + d.extX T x + d.ext0 T w₀) by abel, h]
  ring

end Source

section Target

variable {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank))

theorem mixT_eq (f : WO S T → ℂ) (y : Mx D S.rank ρ) (w₀ : WO S T₀) : d.mixT S ψ μ 𝓕 f y w₀ =
    ∫ a in 𝓕, ψ (symplOH S T (d.incX S a) (d.incAdj S y)) * f (d.incX S a + d.incAdj S y + d.inc0 S w₀) ∂μ := by
  simp only [mixT, integrandT_eq]

theorem mixT_heis_incAdj (f : WO S T → ℂ) (u y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (heisO ψ S T (d.incAdj S u) f) y = d.mixT S ψ μ 𝓕 f (y + u) := by
  funext w₀
  have h : symplOH S T (d.inc0 S w₀) (d.incAdj S u) = 0 := by
    rw [symplOH_skew, incAdj_apply, wittDecomp_sympl_inclDual_inclAnisotropic, neg_zero]
  have h' : symplOH S T (d.incAdj S y) (d.incAdj S u) = 0 := d.symplOH_incY_incY S _ _
  simp only [mixT_eq, heisO, map_add (d.incAdj S), symplOH_add_left, symplOH_add_right, h, h', add_zero,
    AddChar.map_add_eq_mul, mul_assoc]
  congr 1; funext a; congr 3; abel

theorem mixedModelTarget_heisenberg_anisotropic_part (f : WO S T → ℂ) (u : WO S T₀) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (heisO ψ S T (d.inc0 S u) f) y = heisO ψ S T₀ u (d.mixT S ψ μ 𝓕 f y) := by
  funext w₀
  have h' : symplOH S T (d.incAdj S y) (d.inc0 S u) = 0 := d.wittDecomp_sympl_inclDual_inclAnisotropic S _ _
  simp only [mixT_eq, heisO, map_add (d.inc0 S), symplOH_add_left, wittDecomp_sympl_inclIsotropic_inclAnisotropic, h',
    wittDecomp_sympl_inclAnisotropic_inclAnisotropic, zero_add, ← integral_const_mul, add_assoc]
  congr 1; funext a; ring

variable {μ 𝓕}

end Target

end GlobalTheory.MixModel.Check

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar

namespace GlobalTheory.LiftRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Eig (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

structure Given (F : Face D A) : Prop where
  core : GlobalTheory.Hk3.Core R F
  params : ∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)
  irr : ∀ χ ∈ A.X, IsAbsIrrChar χ
  types : GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R
  guard : FWT.QGuard R
  gapR : ∀ (τ : D.what₂.Tau) (n : ℕ), n + 1 < D.R.r →
    100 * (D.R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) n - Formalism.L2.NTheta.lamAt (D.hc τ) (n + 1)

def IsLval (i : Fin D.R.m) (t : T) (c : Eig D) (z : ℝ) : Prop :=
  ∃ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B ∧ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsLValue R t B ((i : ℕ) + 1) z

variable (SF : Finset (HeightOneSpectrum (𝓞 D.host.F)))

def AForm : Prop :=
  ∃ a : Fin D.R.m → ℝ, (∀ i, 0 < a i) ∧ ∀ i t c, GlobalTheory.Hk3.Wcc R SF i c ≠ ⊥ → ∃ z : ℝ, IsLval R i t c z ∧
    ∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, R.thG i t (LinearMap.adjoint (R.thG i t) x) = ((a i * z : ℝ) : ℂ) • x

def BForm : Prop :=
  ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ t c (z : Fin D.R.m → ℝ), (∀ i, IsLval R i t c (z i)) →
    ∀ x ∈ GlobalTheory.Hk3.EEc R SF c, R.Th t (LinearMap.adjoint (R.Th t) x) = ((κ₀ * ∏ i, z i : ℝ) : ℂ) • x

def Scal : Prop :=
  ∃ (lam : Fin D.R.m → T → Eig D → ℝ) (κ : ℝ), 0 < κ ∧ (∀ i t c, 0 < lam i t c) ∧
    (∀ i t c, ∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, R.thG i t (LinearMap.adjoint (R.thG i t) x) = ((lam i t c : ℝ) : ℂ) • x) ∧
    ∀ t c, ∀ x ∈ GlobalTheory.Hk3.EEc R SF c, R.Th t (LinearMap.adjoint (R.Th t) x) = ((κ * ∏ i, lam i t c : ℝ) : ℂ) • x

def Kept : Prop :=
  ∀ t c, ∀ x ∈ GlobalTheory.Hk3.EEc R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c,
    R.Th t (LinearMap.adjoint (R.Th t) x) ∈ GlobalTheory.Hk3.EEc R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c

def MatchUp : Prop := ∀ c, GlobalTheory.Hk3.EEc R SF c ≠ ⊥ → ∀ i, GlobalTheory.Hk3.Wcc R SF i c ≠ ⊥

def RowsNe (F : Face D A) : Prop := ∀ b, R.EEat (R.levR F b) ≠ ⊥

def UpInj : Prop := ∀ t, Function.Injective (LinearMap.adjoint (R.Th t))

def UpInjW : Prop :=
  ∀ i t x, GlobalTheory.Hk3.eH R i x = x → LinearMap.adjoint (R.thG i t) x = 0 → x = 0

def GoodV (i : Fin D.R.m) (y : (R.HV i A.μ0).H) : Prop :=
  ∀ ℓ : (R.cV i).W →ₗ[ℂ] ℂ,
    gaL (Vc D i) (R.βV i) (R.datVt i A.μ0) R.eG (RealDat.eC (A := A) (sg0 D A)) (fun h => ℓ (R.extV i A.μ0 y h)) =
      fun h => ℓ (R.extV i A.μ0 y h)

def LiftInj : Prop :=
  ∀ i h, GlobalTheory.Hk3.IsOpsV R i A.μ0 h → ∀ s : Eig D, ∀ x y : (R.HV i A.μ0).H,
    (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.IsLab (Vc D i) P d → h P (Finsupp.single d 1) x = s P d • x) →
    (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.IsLab (Vc D i) P d → h P (Finsupp.single d 1) y = s P d • y) →
    R.thG i A.μ0 x ≠ 0 → GoodV R i y → R.thG i A.μ0 y = 0 → y = 0

def IsLiftDataC (F : Face D A) (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (P : LevelP R.Pg D.R.r ℂ)
    (cμ cη : (AE D)ˣ →* Circle) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ)
    (c : CoefA (Vc D i)) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) : Prop :=
  GlobalTheory.Hk3.Core R F ∧ PrimeToHost R t ∧ IsEmbOverK D σ s ∧ IsLocalLevel P ∧ IsConjChars R i t s cμ cη m ∧
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω ∧
    (∀ ρ, Datum.IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (BW ρ) (pW D i ρ)) ∧
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i P) (R.Q t) m f₀ f ∧
    Lift.PtTheta R.ψ (Vc D i) (Wc D i) (ptAt R i σ BW f) ∧ c.Is ∧
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ BW f) (deltaAtEmb D i σ) io

def ForLiftDataC (F : Face D A)
    (Φ : ∀ (i : Fin D.R.m) (_t : T) (σ : D.what₂.LL →+* ℂ) (_P : LevelP R.Pg D.R.r ℂ) (_m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
      (_ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
      (_BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (_f : Datum.WO (Vc D i) (Wc D i) → ℂ)
      (c : CoefA (Vc D i)) (_io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), Prop) : Prop :=
  ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → Φ i t σ P m ω BW f c io

def SourceLevelLawC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t σ P m ω BW f _ _ =>
    ∀ κ ∈ Lev.levA (Vc D i) (levV R i t P m), ∀ Q : PolF D (Wc D i).rank (Vc D i).rank,
      ω (κ, 1) (ptAt R i σ BW f Q) = (Lev.levChi (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m) κ)⁻¹ • ptAt R i σ BW f Q


open Datum in
def InnerProductFormulaC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t σ P m ω BW f _ _ =>
    ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))), IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕 →
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    ∀ Fr : Frames (Wc D i), IsFrames (Wc D i) Fr → ∀ mR : ∀ ρ, Measure (Upq (Wc D i) ρ), (∀ ρ, Lev.IsMinf (mR ρ)) →
    ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ (v₁ v₂ : ∀ ρ, lowT (R.MW i σ) ρ) (Q₁ Q₂ : PolF D (Wc D i).rank (Vc D i).rank),
      let φ₁ := ptAt R i σ BW f Q₁
      let φ₂ := ptAt R i σ BW f Q₂
      let F₁ := U₁ fun ρ => v₁ ρ
      let F₂ := U₂ fun ρ => v₂ ρ
      let Z : GA D (Wc D i) → ℂ := fun g => l2 μ 𝓧 (ω (1, g) φ₁) φ₂ * starRingEnd ℂ (petW R i (rTr (Wc D i) g F₁) F₂)
      let pt : FinCos (Wc D i) (levW R i) → (∀ ρ, Upq (Wc D i) ρ) → GA D (Wc D i) := fun x b =>
        x.rep * realElt R.θ (Wc D i) fun ρ => realMat (Wc D i) Fr ρ (b ρ)
      (∀ h, IntegrableOn (fun g => thetaKO ω h g φ₁ * starRingEnd ℂ (F₁ g)) (R.fdW i) (R.νW i)) ∧
      IntegrableOn (fun h => upLift R i ω φ₁ F₁ h * starRingEnd ℂ (upLift R i ω φ₂ F₂ h)) 𝓕 ν ∧
      ∫⁻ b, ∑' x, ‖Z (pt x b)‖ₑ ∂(Measure.pi mR) < ⊤ ∧
      l2 ν 𝓕 (upLift R i ω φ₁ F₁) (upLift R i ω φ₂ F₂) = ((ν 𝓕).toReal : ℂ) * ∫ b, ∑' x, Z (pt x b) ∂(Measure.pi mR)


open Datum in
def FockCoefficientC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i _ σ _ _ ω BW f c io =>
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    ∀ x ∈ GfC (Wc D i), ∀ g : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ,
      (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) ρ)) → ∀ (e e' : ∀ ρ, lowT (R.MW i σ) ρ) (w w' : c.W),
      l2 μ 𝓧 (ω (1, x * realElt R.θ (Wc D i) g) (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e) w)))
          (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e') w')) =
        Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) *
          (∏ ρ, ⟪((e' ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ), (R.MW i σ).rep ρ (g ρ) ((e ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ) *
          ⟪w', w⟫_ℂ * l2 μ 𝓧 (ω (1, x) f) f


open Datum in
def FiniteZetaL (F : Face D A) : Prop :=
  ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io →
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    ∀ ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, typePart R i σ t P ev ≠ ⊥ →
      ∃ B : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsSysParamD D (finS R t) D.R.r ev B ∧
        (∀ w, OffS D (finS R t) w → ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)) ∧
        GlobalTheory.LFun.Converges (GlobalTheory.LFun.above D.host.E (finS R t : Set (HeightOneSpectrum (𝓞 D.host.F))))
          (GlobalTheory.LFun.twist B (GlobalTheory.LFun.val cμ)⁻¹) ((1 + (D.R.t : ℂ)) / 2) ∧
        ∀ U₁ ∈ partFull R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (Lev.levChi _ (R.βW i) (R.datWp i P)) (finS R t) ev,
        ∀ U₂ ∈ R.Wall i σ, ∀ v₁ v₂ : (R.MW i σ).Vec,
          HasSum (fun y : FinCos (Wc D i) (levW R i) =>
              l2 μ 𝓧 (ω (1, y.rep) f) f * starRingEnd ℂ (petW R i (rTr (Wc D i) y.rep (U₁ v₁)) (U₂ v₂)))
            ((Nat.card P.H : ℂ) * (nrm2 μ 𝓧 f : ℂ) * (GlobalTheory.LFun.LSD D (finS R t) B cμ ((1 + (D.R.t : ℂ)) / 2) / (dOff D (finS R t) : ℂ)) *
              starRingEnd ℂ (petW R i (U₁ v₁) (U₂ v₂)))


open Datum in
def LevelIndexNormC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t _ P m _ _ f _ _ =>
    levV R i t P m ≤ GlobalTheory.Mass.Levels.latLev (Vc D i) ∧
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
      (((levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) : ℕ) : ℝ) * nrm2 μ 𝓧 f = ∏ v ∈ finS R t, (dLoc D v)⁻¹

def RealLowestKTypeCoeffSquareIntegrable : Prop :=
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), ∃ δ : ℝ, 0 < δ ∧
    ∀ Fr : Frames (Wc D i), IsFrames (Wc D i) Fr → ∀ mR : Measure (Upq (Wc D i) ρ), Lev.IsMinf mR →
    ∀ e : lowT (R.MW i σ) ρ, ‖((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1 →
      let k : Upq (Wc D i) ρ → ℝ := fun b => ‖⟪((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
        (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2
      Integrable k mR ∧ ∫ b, k b ∂mR = δ

end GlobalTheory.LiftRows

end
end

