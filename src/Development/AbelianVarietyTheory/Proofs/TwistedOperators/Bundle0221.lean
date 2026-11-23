module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1070
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobolevCauchyTendstoSmoothLimit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyMulTorProd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

variable {D : D7} {S T : HSp D}

def torProd (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (s : D.what₂.Tau → Fin V.rank → ℝ) : GA D V :=
  (Finset.univ.toList.map fun ρ => torAt θ V B ρ (s ρ)).prod

def conjL {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} : Frame Ψ r →ₗ[ℝ] Frame Ψ r where
  toFun Z := fun τ a b => conj (Z τ a b)
  map_add' Z Z' := funext fun τ => funext fun a => funext fun b => map_add (starRingEnd ℂ) _ _
  map_smul' c Z := funext fun τ => funext fun a => funext fun b => by
    change conj ((c : ℂ) * Z τ a b) = (c : ℂ) * conj (Z τ a b)
    rw [map_mul, Complex.conj_ofReal]

theorem mat_conjL {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (Z : Frame Ψ r) (τ : Ψ) :
    mat (conjL Z) τ = (mat Z τ).map (starRingEnd ℂ) := rfl

def toLieC (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas) :
    Frame C.X.Ψ T.rank →ₗ[ℝ] GlobalTheory.SmoothForms.LieN T :=
  (GlobalTheory.HolRead.AdExt.toLie R B (fun ρ => C.m.e ρ)).comp conjL

theorem isUnit_det_B (C : Ctx S T) {B : C.Bas} (hB : C.IsB B) (ρ : D.what₂.Tau) : IsUnit (B ρ).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have := congrArg det (hB ρ)
  rw [det_mul, det_mul, h0, mul_zero, sgnM, det_diagonal] at this
  refine Finset.prod_ne_zero_iff.2 (fun c _ => ?_) this.symm
  unfold sgn
  split_ifs <;> norm_num

theorem exp_map_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (NormedSpace.exp A).map (starRingEnd ℂ) = NormedSpace.exp (A.map (starRingEnd ℂ)) := by
  have h : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map (starRingEnd ℂ) = Mᴴᵀ := fun M => by
    ext i j
    simp [conjTranspose_apply]
  rw [h, h, Matrix.exp_transpose, Matrix.exp_conjTranspose]

def trLin (V : HSp D) (m : D.what₂.Tau → ℤ) : GlobalTheory.SmoothForms.LieN V →ₗ[ℝ] ℂ where
  toFun Y := ∑ ρ, (m ρ : ℂ) * trace (Y ρ).1
  map_add' Y Y' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    change (m ρ : ℂ) * trace ((Y ρ).1 + (Y' ρ).1) = _
    rw [trace_add, mul_add]
  map_smul' c Y := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    change (m ρ : ℂ) * trace (c • (Y ρ).1) = c • ((m ρ : ℂ) * trace (Y ρ).1)
    rw [trace_smul, mul_smul_comm]

def trCL (V : HSp D) (m : D.what₂.Tau → ℤ) : GlobalTheory.SmoothForms.LieN V →L[ℝ] ℂ where
  toLinearMap := trLin V m
  cont := continuous_finsetSum _ fun ρ _ =>
    continuous_const.mul ((continuous_subtype_val.comp (continuous_apply ρ)).matrix_trace)

theorem trCL_apply (V : HSp D) (m : D.what₂.Tau → ℤ) (Y : GlobalTheory.SmoothForms.LieN V) : trCL V m Y = trLin V m Y := rfl

end GlobalTheory.AdSpan.ConjHol

namespace GlobalTheory.AdSpan.ConjHol

variable {D : D7} {S T : HSp D}

theorem apply_mul_torProd (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (w : D.what₂.Tau → Fin V.rank → ℤ) (ψ : GA D V → ℂ)
    (h : ∀ (ρ : D.what₂.Tau) (t : Fin V.rank → ℝ) (g : GA D V),
      ψ (g * torAt θ V B ρ t) = cexp (((∑ a, (w ρ a : ℝ) * t a : ℝ) : ℂ) * I) * ψ g)
    (s : D.what₂.Tau → Fin V.rank → ℝ) (g : GA D V) :
    ψ (g * torProd θ V B s) = cexp (((∑ ρ, ∑ a, (w ρ a : ℝ) * s ρ a : ℝ) : ℂ) * I) * ψ g := by
  unfold torProd
  suffices H : ∀ l : List D.what₂.Tau, l.Nodup → ∀ g, ψ (g * (l.map fun ρ => torAt θ V B ρ (s ρ)).prod) =
      cexp (((∑ ρ ∈ l.toFinset, ∑ a, (w ρ a : ℝ) * s ρ a : ℝ) : ℂ) * I) * ψ g by
    have := H (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _) g
    rwa [Finset.toList_toFinset] at this
  intro l hl
  induction l with
  | nil => intro g; simp
  | cons ρ l ih =>
    intro g
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, ← mul_assoc, ih hl.2, h, List.toFinset_cons,
      Finset.sum_insert (by simpa using hl.1), ← mul_assoc, ← Complex.exp_add, ← add_mul]
    congr 3
    push_cast
    ring

theorem xB_mvB_mul (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (a k : GA D T) (b : Frame C.X.Ψ T.rank)
    (hk : ∀ ρ, compAt C.θ ρ (Formalism.L2.Theta.mt T k) = B ρ * (mat b (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹) :
    C.xB (C.mvB (a * k) B) = rmul (C.xB (C.mvB a B)) b := by
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  funext σ i j
  obtain ⟨ρ, rfl⟩ := C.m.e.surjective σ
  have e1 : C.mvB (a * k) B ρ = C.mvB a B ρ * (mat b (C.m.e ρ)).map (starRingEnd ℂ) := by
    have hm : compAt C.θ ρ (Formalism.L2.Theta.mt T (a * k)) =
        compAt C.θ ρ (Formalism.L2.Theta.mt T a) * compAt C.θ ρ (Formalism.L2.Theta.mt T k) := R.2.2.2.1 a k ρ
    simp only [Ctx.mvB]
    rw [hm, hk]
    simp only [Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_B C hB ρ), Matrix.mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Ctx.xB, rmul, mat, Equiv.symm_apply_apply, e1, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply,
    map_sum, map_mul, Complex.conj_conj]

end GlobalTheory.AdSpan.ConjHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairLift

def NoLow (X : ProvA) (p q : ℕ) {r s : ℕ} (lam' : Ix r s → ℚ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ p → i ≤ q → ∀ (MM : GKMod (p - i) (q - i))
    (f : Pol (p - i) (q - i) r s →ₗ[ℂ] TensorProduct ℂ MM.V (X.ds r s lam').HK.V),
    Formalism.BasicNotions.TH.IsIntw (X.fock (p - i) (q - i) r s) MM (X.ds r s lam').HK f → f = 0

structure Rule (X : ProvA) {p q r s : ℕ} (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ) : Prop where
  pos : 1 ≤ p + q
  pos' : 1 ≤ r + s
  par : IsParam lam
  par' : IsParam lam'
  down : Formalism.MainNotions.SchurIrreducible.ARiiiDown X lam lam'
  line : Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam lam'
  low : NoLow X p q lam'

def RulePar (X : ProvA) (S S' : SPar) (aS aT : ℚ) : Prop :=
  ∃ (p q r s : ℕ) (l₁ l₂ l₁' l₂' : List ℚ), l₁.length = p ∧ l₂.length = q ∧ l₁'.length = r ∧ l₂'.length = s ∧
    Rule X (ofBlocks l₁ l₂ : Ix p q → ℚ) (ofBlocks l₁' l₂' : Ix r s → ℚ) ∧
    S = dualPar (signed l₁ l₂ aT) ∧ S' = dualPar (signed l₁' l₂' aS)

def ThetaPar (t : ℕ) (P P' : SPar) (c c' : ℚ) : Prop :=
  ∃ al be ga de : List ℚ, P = signed (al ++ be) (ga ++ de) c ∧
    ((Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧ P' = signed (al ++ block t ++ de) (ga ++ be) c') ∨
      (Formalism.MainNotions.SchurIrreducible.DataARm t al be ga de ∧ P' = signed (al ++ de) (ga ++ block t ++ be) c'))

def PairPar (S S' : SPar) (aS aT : ℚ) : Prop :=
  ∃ (t : ℕ) (P P' : SPar), S = dualPar P ∧ S' = dualPar P' ∧
    ((ThetaPar t P P' aT aS ∧ GlobalTheory.SignedHC.FarFrom aT (((t : ℚ) + 3) / 2) P) ∨ ThetaPar t P' P aS aT)

def partner (t : ℕ) (b : Bool) (c c' : ℚ) (P : SPar) : SPar :=
  (P.image fun x => (x.1 - c + c', if x.1 < c then !x.2 else x.2)) ∪ (TPar.block c' t).image fun x => (x, b)

def GapOver (P : SPar) (h : ℚ) : Prop := ∀ x ∈ P, ∀ y ∈ P, x.2 ≠ y.2 → h < |x.1 - y.1|

def att (c : ℚ) (n : ℕ) : ℚ := if Odd n then c - 1 / 2 else c

variable {D : D7}

structure Inputs (D : D7) (X : ProvA) : Prop where
  chosen : GlobalTheory.Chain.RealIt.ChosenSeries X
  hc : GlobalTheory.Published.HarishChandraModules
  decay : GlobalTheory.Published.CuspRapidDecay
  bridge : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D
  vacChar : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D
  lie : LieFockAll D
  cpt : CompactFockAll D
  dense : FockDense D
  laws : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.LiftProps D
  const : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTerm D
  ext : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.GKExtension D

def IsWeilExp (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (aS aT : D.what₂.Tau → ℚ) (ω : WRep V W) : Prop :=
  ∃ χS χT : (AE D)ˣ →* Circle, IsWeilDatumO ψ V W χS χT ω ∧ ∀ τ, HasInfExp D χS τ (aS τ) ∧ HasInfExp D χT τ (aT τ)

def LowFock (D : D7) (X : ProvA) : Prop :=
  ∀ (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ), (∀ τ, RulePar X (S τ) (S' τ) (aS τ) (aT τ)) →
    ∀ (i : ℕ) (V' W : HSp D) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ →
    1 ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered S i V' → ∀ ω' : WRep V' W, IsWeilExp ψ V' W aS aT ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ F ∈ MultT θ M' ∅ 1, ∀ (v : SmT M') (A : Fr V') (f₀ : WO V' W → ℂ), IsVacF ψ θ A (Fr.ofModel M') f₀ → ∀ P,
      Lift.liftInt ν 𝓕 (thetaKO ω') (ptF ψ θ A (Fr.ofModel M') f₀ P) (F v) = 0

def LowAll (D : D7) (X : ProvA) : Prop :=
  ∀ (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ), (∀ τ, RulePar X (S τ) (S' τ) (aS τ) (aT τ)) →
    ∀ (i : ℕ) (V' W : HSp D) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ →
    1 ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered S i V' → ∀ ω' : WRep V' W, IsWeilExp ψ V' W aS aT ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ F ∈ MultT θ M' ∅ 1, ∀ (v : SmT M') (f' : WO V' W → ℂ), IsThetaFunO ψ V' W f' →
      Lift.liftInt ν 𝓕 (thetaKO ω') f' (F v) = 0

def CuspAll (D : D7) (X : ProvA) : Prop :=
  ∀ (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ), (∀ τ, RulePar X (S τ) (S' τ) (aS τ) (aT τ)) →
    ∀ (V W : HSp D) (_M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ →
    ∀ ω : WRep V W, IsWeilExp ψ V W aS aT ω →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ F ∈ MultT θ M' ∅ 1, ∀ (v : SmT M') (f : WO V W → ℂ), IsThetaFunO ψ V W f →
      IsCuspFun V (Lift.liftInt ν 𝓕 (thetaKO ω) f (F v))

def LiftsM (θ : InfFam D) {A B : HSp D} {SA SB : D.what₂.Tau → SPar} (MA : DSModel A SA) (MB : DSModel B SB) {P : Type}
    (ν : Measure (GA D A)) (𝓕 : Set (GA D A)) (K : P → GA D B → GA D A → ℂ) (It : P → SmT MA → SmT MB) : Prop :=
  ∀ F ∈ MultT θ MA ∅ 1, ∃ F' ∈ MultT θ MB ∅ 1, ∀ (p : P) (v : SmT MA) (h : GA D B),
    IntegrableOn (fun g => K p h g * F v g) 𝓕 ν ∧ ∫ g in 𝓕, K p h g * F v g ∂ν = F' (It p v) h

def PairLifts (D : D7) (X : ProvA) : Prop :=
  ∀ (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ), (∀ τ, RulePar X (S τ) (S' τ) (aS τ) (aT τ)) →
    ∀ (V W : HSp D) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ →
    ∀ ω : WRep V W, IsWeilExp ψ V W aS aT ω →
    ∀ (f₀ : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsVacVec ψ θ M M' f₀ →
      IsItW θ M M' ω (ptOf ψ θ M M' f₀) It →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ f, IsVacF ψ θ (Fr.ofModel M) (Fr.ofModel M') f →
      LiftsM θ M' M ν 𝓕 (fun P g h => thetaKO ω g h (ptOf ψ θ M M' f P)) fun P v => It P v

structure IsIntwF {V W : HSp D} {S S' : D.what₂.Tau → SPar} {Z P : Type} (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (ω : GA D V × GA D W →* Module.End ℂ (Z → ℂ)) (pt : P → (Z → ℂ))
    (It : P → SmT M' →ₗ[ℂ] SmT M) : Prop where
  ne : ∃ φ, It φ ≠ 0
  bdd : ∀ φ w, ∃ c : ℝ, ∀ v : M'.Vec,
    ‖ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v)))‖ ≤ c * ∏ τ, ‖(v τ : M'.H τ)‖
  eqK : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ φ', pt φ' = ω (atTau θ V τ g, 1) (pt φ) →
    ∀ v, inclT M (It φ' v) = actT M τ g (inclT M (It φ v))
  eqg : ∀ τ, ∀ Y ∈ lieAt V τ, ∀ φ φ', (∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ Y t, 1) (pt φ) z) (pt φ' z) 0) →
    ∀ v, DerT M τ Y (It φ v) (It φ' v)
  invK : ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ φ' v v', pt φ' = ω (1, atTau θ W τ h) (pt φ) →
    inclT M' v' = actT M' τ h (inclT M' v) → It φ' v' = It φ v
  invg : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ φ' v v', (∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (pt φ) z) (pt φ' z) 0) →
    DerT M' τ Y v v' → It φ' v + It φ v' = 0

structure ModelTr (σ : ℂ →+* ℂ) (ε : Bool) (θ : InfFam D) {V : HSp D} {S S₁ : D.what₂.Tau → SPar}
    (M₁ : DSModel (sgn ε V) S₁) (M : DSModel V S) (κ : SmT M₁ ≃+ SmT M) : Prop where
  smul : ∀ (c : ℂ) x, κ (c • x) = σ c • κ x
  cart : ∀ τ, cart M₁ τ = sgnM ε (cart M τ)
  act : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ x y,
    inclT M₁ y = actT M₁ τ g (inclT M₁ x) ↔ inclT M (κ y) = actT M τ g (inclT M (κ x))
  der : ∀ τ, ∀ Y ∈ lieAt V τ, ∀ x y, DerT M₁ τ Y x y ↔ DerT M τ Y (κ x) (κ y)
  ell : ∀ w₁, ∃ w, ∀ x, ellT M₁ w₁ (inclT M₁ x) = σ (ellT M w (inclT M (κ x)))
  vec : ∀ v₁ : M₁.Vec, ∃ v : M.Vec, κ (PiTensorProduct.tprod ℂ v₁) = PiTensorProduct.tprod ℂ v ∧
    ∀ τ, ‖(v τ : M.H τ)‖ = ‖(v₁ τ : M₁.H τ)‖
  mult : ∀ F ∈ MultT θ M ∅ 1, ∃ F₁ ∈ MultT θ M₁ ∅ 1, ∀ x g, F₁ x g = σ (F (κ x) (ofSgn ε V g))
  mult' : ∀ F₁ ∈ MultT θ M₁ ∅ 1, ∃ F ∈ MultT θ M ∅ 1, ∀ x g, F₁ x g = σ (F (κ x) (ofSgn ε V g))

structure SgnLaw (θ : InfFam D) (ε : Bool) (V : HSp D) : Prop where
  rat : ∀ g, g ∈ GQ (sgn ε V) ↔ ofSgn ε V g ∈ GQ V
  fin : ∀ g, g ∈ GfC (sgn ε V) ↔ ofSgn ε V g ∈ GfC V
  inf : ∀ g, g ∈ GinfC (sgn ε V) ↔ ofSgn ε V g ∈ GinfC V
  grp : ∀ τ, Formalism.QuantumDeterminants.UH (gramAt D (sgn ε V) τ) = Formalism.QuantumDeterminants.UH (gramAt D V τ)
  lie : ∀ τ, lieAt (sgn ε V) τ = lieAt V τ
  atTau : ∀ τ g, ofSgn ε V (atTau θ (sgn ε V) τ g) = atTau θ V τ g
  meas : ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν →
    ∃ ν₁ : Measure (GA D (sgn ε V)), ν₁.IsHaarMeasure ∧ IsFundamentalDomain (GQ (sgn ε V)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ∧
      ∀ φ : GA D V → ℂ, (IntegrableOn (fun g => φ (ofSgn ε V g)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ↔ IntegrableOn φ 𝓕 ν) ∧
        ∫ g in ofSgn ε V ⁻¹' 𝓕, φ (ofSgn ε V g) ∂ν₁ = ∫ g in 𝓕, φ g ∂ν

def adjO (S T : HSp D) (y : WO T S) : WO S T :=
  HMul.hMul (HMul.hMul (T.gram⁻¹.map (incA D)) ((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D)).transpose)
    (S.gram.map (incA D))

def dag (S T : HSp D) (f : WO S T → ℂ) : WO T S → ℂ := fun y => starRingEnd ℂ (f (adjO S T y))

structure AdjLaw (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop where
  invol : ∀ x : WO S T, adjO S T (adjO T S x) = x
  add : ∀ y y' : WO T S, adjO S T (y + y') = adjO S T y + adjO S T y'
  cont : Continuous (adjO S T)
  sympl : ∀ y y' : WO T S, symplO S T (adjO S T y) (adjO S T y') = -symplO T S y y'
  act : ∀ (g : GA D S) (h : GA D T) (y : WO T S), adjO S T (actO T S h g y) = actO S T g h (adjO S T y)
  rat : ∀ y : WO T S, adjO S T y ∈ ratL T S ↔ y ∈ ratL S T
  half : ∀ (e : AE D) (y : WO T S), IsHalf e y → IsHalf (cA D e) (adjO S T y)
  Heisenberg₂ : ∀ (y : WO T S) (f : WO S T → ℂ), heisO ψ T S y (dag S T f) = dag S T (heisO ψ S T (adjO S T y) f)
  theta : ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ T S (dag S T f)

def frSgn (ε : Bool) {V : HSp D} (A : Fr V) : Fr (sgn ε V) where
  ε τ a := xor ε (A.ε τ a)
  fr := A.fr
  fr_unit := A.fr_unit
  fr_gram τ := by
    cases ε
    · simp only [Bool.false_xor]
      exact A.fr_gram τ
    · have e : gramAt D (neg V) τ = -gramAt D V τ := by ext i j; simp [gramAt, neg_gram]
      have h : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ) := by
        ext a b
        by_cases hab : a = b
        · subst hab; cases h : A.ε τ a <;> simp [Formalism.REAL.Jm, h]
        · simp [Formalism.REAL.Jm, hab]
      show _ = gramAt D (neg V) τ
      rw [e, h, ← A.fr_gram τ, Matrix.mul_neg, Matrix.neg_mul]

theorem cart_frSgn (ε : Bool) {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : (frSgn ε A).cart τ = sgnM ε (A.cart τ) := by

  have hJ : Formalism.REAL.Jm (fun a => xor ε (A.ε τ a)) = sgnM ε (Formalism.REAL.Jm (A.ε τ)) := by
    cases ε
    · simp [sgnM]
    · simp only [sgnM, cond_true, Formalism.REAL.Jm, Bool.true_xor]
      rw [Matrix.diagonal_neg]
      congr 1
      funext a
      cases A.ε τ a <;> simp
  show (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor ε (A.ε τ a)) * A.fr τ = sgnM ε ((A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * A.fr τ)
  rw [hJ]
  cases ε
  · rfl
  · simp only [sgnM, cond_true, Matrix.mul_neg, Matrix.neg_mul]

end GlobalTheory.PairLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryTorusRealPlaceTensorEqComplexPow
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RealTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r) {w : InfinitePlace F} (τ : EmbOver E w)

theorem trace_eq_sum (y : Fld P) : τ.1 (Algebra.trace E (Fld P) y) = ∑ i, psiL P τ i y := by
  letI : Algebra E ℂ := τ.1.toAlgebra
  haveI : Algebra.IsSeparable E (Fld P) := Algebra.IsAlgebraic.isSeparable_of_perfectField

  let emb : Fin r → (Fld P →ₐ[E] ℂ) := fun i =>
    { psiL P τ i with commutes' := fun e => psiL_algebraMap P τ i e }
  have hinj : Function.Injective emb := by
    intro i j h
    apply cxRoots_injective P τ
    have h' := congrArg (fun f : Fld P →ₐ[E] ℂ => f (alpha P)) h
    simpa [emb] using h'
  have hcard : Fintype.card (Fin r) = Fintype.card (Fld P →ₐ[E] ℂ) := by
    rw [Fintype.card_fin, AlgHom.card, finrank_Fld]
  have hbij : Function.Bijective emb :=
    (Fintype.bijective_iff_injective_and_card emb).2 ⟨hinj, hcard⟩
  have htr := trace_eq_sum_embeddings (K := E) (L := Fld P) (E := ℂ) (x := y)
  rw [show τ.1 (Algebra.trace E (Fld P) y) = algebraMap E ℂ (Algebra.trace E (Fld P) y) from rfl, htr]
  exact (Fintype.sum_bijective emb hbij (fun i => psiL P τ i y) (fun g => g y) (fun i => rfl)).symm

theorem psiL_star (hCM : IsCMExt F E σ) (i : Fin r) (hi : ‖cxRoots τ.1 P i‖ = 1) (y : Fld P) :
    psiL P τ i (star' P y) = conj (psiL P τ i y) := by
  have key : ((psiL P τ i).comp (star' P : Fld P →+* Fld P) : AdjoinRoot P.1 →+* ℂ) =
      ((starRingEnd ℂ).comp (psiL P τ i) : AdjoinRoot P.1 →+* ℂ) := by
    apply AdjoinRoot.ringHom_ext
    · ext e
      show psiL P τ i (star' P (algebraMap E (Fld P) e)) = conj (psiL P τ i (algebraMap E (Fld P) e))
      rw [star'_algebraMap, psiL_algebraMap, psiL_algebraMap]
      exact hCM.2.2.2 τ.1 e
    · show psiL P τ i (star' P (alpha P)) = conj (psiL P τ i (alpha P))
      rw [star'_alpha, map_inv₀, psiL_alpha]

      have h1 : cxRoots τ.1 P i * conj (cxRoots τ.1 P i) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hi]
        norm_num
      exact (eq_inv_of_mul_eq_one_right h1).symm
  exact RingHom.congr_fun key y

theorem ext_real (a : w.Completion) (hw : w.IsReal) :
    conj (InfinitePlace.Completion.extensionEmbedding w a) = InfinitePlace.Completion.extensionEmbedding w a := by

  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw a, Complex.conj_ofReal]

end GlobalTheory.TrEll.RealTorus


open GlobalTheory.TrEll.RealTorus in
theorem GlobalTheory.TrEll.realTorus_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), CompactSpace (Tor P w.Completion) → ∃ Ψ : w.Completion ⊗[F] Fld P ≃+* (Fin r → ℂ), (∀ y i, Ψ (sigR w.Completion (star' P) y) i = conj (Ψ y i)) ∧ (∀ e i, Ψ (algebraMap (w.Completion ⊗[F] E) _ e) i = infEmb τ e) ∧ Ψ (1 ⊗ₜ[F] alpha P) = cxRoots τ.1 P ∧ (∀ y, infEmb τ (trBase P w.Completion y) = ∑ i, Ψ y i) ∧ Function.Injective (cxRoots τ.1 P) ∧ ∀ i, ‖cxRoots τ.1 P i‖ = 1 := by
  intro F E _ _ _ _ _ σ hCM r P w τ hc
  have hbij := _root_.GlobalTheory.TrEll.RealTorus.PsiAll_bijective F E σ hCM r P w τ
  have hnorm := _root_.GlobalTheory.TrEll.realTorus_norm_cxRoots F E σ hCM r P w τ hbij hc
  have hw : w.IsReal := hCM.1.isReal w
  refine ⟨RingEquiv.ofBijective (PsiAll P τ) hbij, ?_, ?_, ?_, ?_, cxRoots_injective P τ, hnorm⟩
  · intro y i
    simp only [RingEquiv.ofBijective_apply, PsiAll_apply]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      rw [show sigR w.Completion (star' P) (a ⊗ₜ[F] y) = a ⊗ₜ[F] star' P y from rfl]
      rw [Psi_tmul, Psi_tmul, psiL_star P τ hCM i (hnorm i), map_mul, ext_real a hw]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · intro e i
    simp only [RingEquiv.ofBijective_apply, PsiAll_apply]
    induction e using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [show algebraMap (w.Completion ⊗[F] E) (w.Completion ⊗[F] Fld P) (a ⊗ₜ[F] e) =
        a ⊗ₜ[F] algebraMap E (Fld P) e from rfl]
      rw [Psi_tmul, infEmb_tmul, psiL_algebraMap]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · funext i
    simp only [RingEquiv.ofBijective_apply, PsiAll_apply, Psi_tmul, map_one, psiL_alpha, one_mul]
  · intro y
    simp only [RingEquiv.ofBijective_apply, PsiAll_apply]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      rw [show trBase P w.Completion (a ⊗ₜ[F] y) = a ⊗ₜ[F] Algebra.trace E (Fld P) y from rfl]
      rw [infEmb_tmul, trace_eq_sum P τ y, Finset.mul_sum]
      simp only [Psi_tmul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, Finset.sum_add_distrib]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRestrictedWeilFirstFactorApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ResFirstCont

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

theorem continuous_res_left : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ x, Continuous fun m : GA D V => GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, 1) f) x := by
  intro D V V' W r C B ψ χS χT ω hω μ 𝓨 h𝓨 f hf x
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, h𝓨.2.2]; exact ENNReal.one_lt_top⟩
  have hy : Continuous fun y : Mx D W.rank r => isoPart V W C y + midPart V V' W B x := by
    unfold isoPart
    exact (continuous_id.matrix_mul continuous_const).add continuous_const
  refine continuous_iff_continuousAt.2 fun m₀ => ?_
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds m₀
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ V W χS χT ω hω f hf (K ×ˢ {1})
    (hK.prod isCompact_singleton)
  unfold res
  refine continuousAt_of_dominated (bound := fun _ => c) ?_ ?_ (integrable_const c) ?_
  · exact Filter.Eventually.of_forall fun m =>
      ((hω.om_pres (m, 1) f hf).cont.comp hy).aestronglyMeasurable
  · filter_upwards [hKn] with m hm
    exact Filter.Eventually.of_forall fun y => hc (m, 1) ⟨hm, rfl⟩ _
  · refine Filter.Eventually.of_forall fun y => ?_
    exact ((hω.om_cont f hf _).comp (Continuous.prodMk_left 1)).continuousAt

end GlobalTheory.ResFirstCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobolevCauchyTendstoSmoothLimitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.growthSobolev_cauchy_tendsto_smooth_limit : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (N : ℕ) (ψ : ℕ → GA D V → ℂ), (∀ n, Continuous (ψ n) ∧ ψ n ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (ψ n) ≠ ⊤) → (∀ d, Filter.Tendsto (fun p : ℕ × ℕ => GlobalTheory.Size.growthSob θ V d N (ψ p.1 - ψ p.2)) Filter.atTop (nhds 0)) → ∃ f : GA D V → ℂ, Continuous f ∧ f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, Filter.Tendsto (fun n => GlobalTheory.Size.growthSob θ V d N (ψ n - f)) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.GrowthComplete.complete | exact GlobalTheory.GrowthComplete.complete | (intros; apply GlobalTheory.GrowthComplete.complete <;> assumption)
end

