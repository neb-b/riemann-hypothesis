module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3126
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0095
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0107
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0053
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0091
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0092
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareConstantProportionalRegular
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0018
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralKernelLieAlgebraStable
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquareIdentityOfMatching
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomTripleIntegralFactorizationOfReal
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.BotFac
open GlobalTheory.SquareComm in
theorem bottom_triple_integral_factorization_real : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ W : G.Weil, IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∃ (Pi : ModuleCat.{0} ℂ) (p : PolF D WW.rank A.rank →ₗ[ℂ] Pi)
      (p' : PolF D WW.rank A'.rank →ₗ[ℂ] Pi) (J : T → (Pi →ₗ[ℂ] (GA D WW → ℂ))), Function.Surjective p ∧
      (∀ t, J t = 0 ∨ Function.Injective (J t)) ∧ (∀ t, ∃ lam : ℂ, ∀ P, X.I W.ψ W.θ t P = lam • J t (p P)) ∧
      ∀ t P', X.I' W.ψ W.θ t P' = J t (p' P') := by
  intro hP hK hM
  have hH := hP.howeDualityReal
  have hLM := _root_.GlobalTheory.T.twisted_local_factors_match hH hP hK hM
  have hTA := _root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hK hM
  obtain ⟨CF1, H1⟩ := _root_.GlobalTheory.BotDict.bottom_dictionary
  obtain ⟨CF2, H2⟩ := _root_.GlobalTheory.T.theta_bottom_finite_place_matching hH hP hK hM
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, G1⟩ := H1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, G2⟩ := H2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hμ G W _ i j A A' WW X hX => ?_⟩
  obtain ⟨FA, FA', FW, a, b, hdA, hdef, hdW, hD⟩ :=
    G1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX
  have hF := G2 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX
  obtain ⟨Pr, q, q', hq, hq', hLMt⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW a b
  have eI : ∀ t P, thetaInt (X.ω t) X.m X.fd (fockF W.ψ W.θ true FA FW (X.f t) P) = X.I W.ψ W.θ t P := fun t P => by
    funext h; simp only [thetaInt, Tri.I, (hD t).2.2.2.2.1]
  have eI' : ∀ t P, thetaInt (X.ω' t) X.m' X.fd' (fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.I' W.ψ W.θ t P := fun t P => by
    funext h; simp only [thetaInt, Tri.I', (hD t).2.2.2.2.2]
  have iI' : ∀ t P h, IntegrableOn (fun g => thetaKO (X.ω' t) g h (fockF W.ψ W.θ false FA' FW (X.f' t) P)) X.fd' X.m' :=
    fun t P h => by simp only [(hD t).2.2.2.2.2]; exact (hX.integrable t).2 P h
  have key : ∀ t, (∀ P', q' P' = 0 → X.I' W.ψ W.θ t P' = 0) ∧
      ((∀ P', X.I' W.ψ W.θ t P' = 0) ∨ ∀ P', X.I' W.ψ W.θ t P' = 0 → q' P' = 0) ∧
      (∃ lam : ℂ, ∀ P P', q P = q' P' → X.I W.ψ W.θ t P = lam • X.I' W.ψ W.θ t P') := by
    intro t
    obtain ⟨hTr, hInf, hf, hf', -, -⟩ := hD t
    obtain ⟨hex, hfac⟩ := hLMt _ _ hTr hInf
    obtain ⟨Pm, rf, rl, p, p', hm⟩ := _root_.GlobalTheory.T.triple_weil_transfer_matching hH hP hK hM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex (X.ω t) (X.ω' t)
      (hX.is.weil t) (hX.is.weil' t)
    obtain ⟨Pf, r, r', e, -, -, hr, hr'⟩ := hfac _ _ _ _ _ _ _ hm
    obtain ⟨c, hc0, hc⟩ := hTA D W.ψ W.θ W.θ_is A A' WW FA FA' FW _ _ hTr X.m X.fd X.m' X.fd' hX.is.meas hX.is.meas'
      (X.ω t) (X.ω' t) Pm rf rl p p' hm
    have hrel := _root_.GlobalTheory.T.theta_integral_vanishes_on_finite_relations hP D W.ψ W.θ W.ψ_std W.θ_is A' WW FA' FW _ _ (X.ω' t) (hX.is.weil' t) hdef X.m' X.fd' hX.is.meas'
    have kerp' := finRel_le_ker p' hm.mapB.invf
    have memF : ∀ P', fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ algF W.ψ W.θ false FA' FW :=
      fun P' => Submodule.subset_span ⟨_, P', hf', rfl⟩
    have same : ∀ Ψ ∈ algF W.ψ W.θ false FA' FW, (∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m') →
        ∀ Φ₀, Ψ - Φ₀ ∈ finRel (X.ω' t) (algF W.ψ W.θ false FA' FW) → ModInt W.θ (X.ω' t) X.m' X.fd' Φ₀ →
        thetaInt (X.ω' t) X.m' X.fd' Ψ = thetaInt (X.ω' t) X.m' X.fd' Φ₀ := by
      intro Ψ _ hΨ Φ₀ hd hmod
      obtain ⟨N, K, hmod⟩ := hmod
      funext h
      have h0 := congrFun (hrel _ hd) h
      simp only [thetaInt, thetaKO_sub] at h0 ⊢
      rw [integral_sub (hΨ h) (hmod h).1] at h0
      exact sub_eq_zero.1 h0
    have kill : ∀ Ψ ∈ algF W.ψ W.θ false FA' FW, (∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m') →
        p' Ψ = 0 → thetaInt (X.ω' t) X.m' X.fd' Ψ = 0 := by
      intro Ψ hΨ hi hp
      obtain ⟨Φ₀, hΦ₀, hd, hmod, hI⟩ := hc Ψ hΨ
      have hp0 : p' Φ₀ = 0 := by
        have := kerp' hd
        rw [LinearMap.mem_ker, map_sub, hp, zero_sub, neg_eq_zero] at this
        exact this
      have h1 := hI 0 (zero_mem _) (by rw [map_zero, hp0])
      have h2 : thetaInt (X.ω t) X.m X.fd 0 = 0 := by funext h; simp [thetaInt, thetaKO_zero]
      rw [h2] at h1
      rw [same Ψ hΨ hi Φ₀ hd hmod]
      exact ((smul_eq_zero.1 h1.symm).resolve_left hc0)
    have hp'F : ∀ P', p' (fockF W.ψ W.θ false FA' FW (X.f' t) P') = e (q' P' ⊗ₜ r' (X.f' t)) := hr' _ hf'
    refine ⟨fun P' h0 => ?_, ?_, ?_⟩
    · rw [← eI']
      exact kill _ (memF P') (iI' t P') (by rw [hp'F, h0, TensorProduct.zero_tmul, map_zero])
    · by_cases hall : ∀ P', X.I' W.ψ W.θ t P' = 0
      · exact Or.inl hall
      refine Or.inr fun P' h0 => ?_
      by_contra hq0
      refine hall fun P'' => ?_
      rw [← eI']
      by_cases hy : r' (X.f' t) = 0
      · exact kill _ (memF P'') (iI' t P'') (by rw [hp'F, hy, TensorProduct.tmul_zero, map_zero])
      · have hne : p' (fockF W.ψ W.θ false FA' FW (X.f' t) P') ≠ 0 := by
          rw [hp'F]; exact e.map_ne_zero_iff.2 (tmul_ne_zero' hq0 hy)
        exact _root_.GlobalTheory.T.theta_lift_vanishes_of_irreducible_defect hH hP hK hM hTA D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hdA hdef hdW X.m X.fd X.m' X.fd' hX.is.meas hX.is.meas'
          (X.ω t) (X.ω' t) Pm rf rl p p' hm _ (memF P') hne (by rw [eI']; exact h0) _ (memF P'')
    · obtain ⟨κ, hκ⟩ := hF FA FA' FW t hf hf' Pm rf rl p p' hm Pr Pf q q' r r' e hq hq' hr hr'
      refine ⟨c * κ, fun P P' hPP => ?_⟩
      set Ψ := κ • fockF W.ψ W.θ false FA' FW (X.f' t) P' with hΨdef
      have hΨ : Ψ ∈ algF W.ψ W.θ false FA' FW := Submodule.smul_mem _ _ (memF P')
      have hΨi : ∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m' := fun h => by
        simp only [hΨdef, thetaKO_smul]; exact (iI' t P' h).const_mul κ
      obtain ⟨Φ₀, -, hd, hmod, hI⟩ := hc Ψ hΨ
      have hpp : p (fockF W.ψ W.θ true FA FW (X.f t) P) = p' Φ₀ := by
        have h1 : p' Φ₀ = p' Ψ := by
          have := kerp' hd
          rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
          exact this.symm
        rw [h1, hΨdef, map_smul, hp'F, hr _ hf, hκ, hPP, TensorProduct.tmul_smul, map_smul]
      have h2 := hI _ (Submodule.subset_span ⟨_, P, hf, rfl⟩) hpp
      rw [eI, ← same Ψ hΨ hΨi Φ₀ hd hmod] at h2
      rw [h2, ← eI', mul_smul]
      congr 1
      funext h
      simp [hΨdef, thetaInt, thetaKO_smul, integral_const_mul]
  choose hker hirr hlam using key
  let Il : T → PolF D WW.rank A'.rank →ₗ[ℂ] (GA D WW → ℂ) := fun t =>
    { toFun := fun P' => X.I' W.ψ W.θ t P'
      map_add' := fun P Q => by
        show X.I' W.ψ W.θ t (P + Q) = X.I' W.ψ W.θ t P + X.I' W.ψ W.θ t Q
        rw [← eI', ← eI', ← eI', map_add (f := _)]; funext h
        simp only [thetaInt, thetaKO_add, Pi.add_apply]
        exact integral_add (iI' t P h) (iI' t Q h)
      map_smul' := fun c P => by
        show X.I' W.ψ W.θ t (c • P) = c • X.I' W.ψ W.θ t P
        rw [← eI', ← eI', map_smul]; funext h
        simp [thetaInt, thetaKO_smul, integral_const_mul] }
  have hK : ∀ t, LinearMap.ker q' ≤ LinearMap.ker (Il t) := fun t P' h0 => hker t P' h0
  let J : T → (Pr →ₗ[ℂ] (GA D WW → ℂ)) := fun t =>
    ((LinearMap.ker q').liftQ (Il t) (hK t)) ∘ₗ (q'.quotKerEquivOfSurjective hq').symm.toLinearMap
  have hJ : ∀ t P', J t (q' P') = X.I' W.ψ W.θ t P' := fun t P' => by
    have : (q'.quotKerEquivOfSurjective hq').symm (q' P') = Submodule.Quotient.mk P' := by
      rw [LinearEquiv.symm_apply_eq]; exact (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _).symm
    simp only [J, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]; rfl
  refine ⟨Pr, q, q', J, hq, fun t => ?_, fun t => ?_, fun t P' => (hJ t P').symm⟩
  · rcases hirr t with h | h
    · left; refine LinearMap.ext fun x => ?_; obtain ⟨P', rfl⟩ := hq' x; rw [hJ, h P']; rfl
    · right; rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']; intro x hx0; obtain ⟨P', rfl⟩ := hq' x
      rw [hJ] at hx0; exact h P' hx0
  · obtain ⟨lam, hl⟩ := hlam t
    refine ⟨lam, fun P => ?_⟩
    obtain ⟨P', hP'⟩ := hq' (q P)
    rw [← hP', hJ]; exact hl P P' hP'.symm
end GlobalTheory.BotFac
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_triple_integral_factorization_of_real : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ W : G.Weil, IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∃ (Pi : ModuleCat.{0} ℂ) (p : PolF D WW.rank A.rank →ₗ[ℂ] Pi)
      (p' : PolF D WW.rank A'.rank →ₗ[ℂ] Pi) (J : T → (Pi →ₗ[ℂ] (GA D WW → ℂ))), Function.Surjective p ∧
      (∀ t, J t = 0 ∨ Function.Injective (J t)) ∧ (∀ t, ∃ lam : ℂ, ∀ P, X.I W.ψ W.θ t P = lam • J t (p P)) ∧
      ∀ t P', X.I' W.ψ W.θ t P' = J t (p' P') := by
  first | exact @_root_.GlobalTheory.BotFac.bottom_triple_integral_factorization_real | exact _root_.GlobalTheory.BotFac.bottom_triple_integral_factorization_real | (intros; apply _root_.GlobalTheory.BotFac.bottom_triple_integral_factorization_real <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsScalarOfRealStandingData
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.RealSep
section Generic
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.BigNZ
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
end Generic
section Nonzero
open GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ blkU conjU UB)
end Nonzero
section Read
open GlobalTheory.SquareComm GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.TripleRead GlobalTheory.SquareIdent
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (incM conjU)
variable {D : D7}
end Read
section Grid
open GlobalTheory.SquareComm GlobalTheory.SquareAgree GlobalTheory.TripleRead GlobalTheory.SquareIdent GlobalTheory.SquareDict GlobalTheory.BigNZ
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta blkU spV spW spW₁ spV₁ xiV xiV₁)
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
end Grid
section Null
open GlobalTheory.SquareComm GlobalTheory.SquareIdent GlobalTheory.SquareDict
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta spV spW spW₁ spV₁)
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
set_option maxHeartbeats 1000000 in
theorem exists_nullSpace_realPlace (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hLM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (hst : ∀ t, SquareStanding G t)
    (i j : Fin D.R.m) {A : Fr (spW G i j)} {AV : Fr (spV G i j)} {AV₁ : Fr (spV₁ G i j)} (hA : IsGridFr W _ A)
    (hV : IsGridFr W _ AV) (hV₁ : IsGridFr W _ AV₁)
    (ι : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) →ₗ[ℂ]
      PolF D (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank (spW G i j).rank)
    (hι : ∀ (t : T) (B : Frames G) (ρ : RealMatch W) n Φ (τ : TotT G (routeBig t i j)) τ', HasFlip B t ρ i j n Φ τ τ' →
      ∀ a : PolT G (routeBig t i j) →₀ ℂ,
        datumA W (tensT W a τ) = fockF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ) (ι (toTens a))) :
    ∃ K : Submodule ℂ (PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j)),
      (∀ B ρ t x, IsNull W B ρ t i j x ↔ x ∈ K) ∧
      (∀ x ∈ K, ∀ t ν 𝓕, IsHaarFD (spW G i j) ν 𝓕 → ∀ ωA : GlobalTheory.Grid.WRep (spW G i j) (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)),
        GlobalTheory.Grid.IsWeil W.ψ true _ _ (beta G i j) (beta G i j / alpha G t i j) ωA →
        ∀ f, IsFinF W.ψ W.θ true A (frSum AV AV₁) f → thetaInt ωA ν 𝓕 (fockF W.ψ W.θ true A (frSum AV AV₁) f (ι x)) = 0) ∧
      ∀ B (ρ : RealMatch W) t (M : Vol G), M.Is t → ∀ n Φ τ τ', (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) →
        HasFlip B t ρ i j n Φ τ τ' → ∀ g g₁, ∃ l : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) →ₗ[ℂ] ℂ,
          ∀ a, ∫ u in M.fd _, kerBig W (tensT W a τ) g g₁ u ∂M.ν _ = l (toTens a) := by
  obtain ⟨A₁, hA₁⟩ := exists_isGridFr W (X := .grid i j) ⟨i.2.le, j.2.le⟩
  have hD := fun t => dict hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁
  have hT := fun t => (hD t).1 (hst t) _ (exists_vol G hL t).choose_spec
  choose a b ha hb _ using (hT μ₀).gap
  obtain ⟨Pr, q, H⟩ := _root_.GlobalTheory.T.thetaIntegral_factors_through_kType hP hK hLM D W.ψ W.θ W.ψ_std W.θ_is _ _ _ A A₁ (frSum AV AV₁) a b
  replace H := fun t => H _ _ (hT t) fun τ => ⟨GlobalTheory.SquareRel.hasInfExp_alpha G i j hL μ₀ t τ (ha τ), hb τ⟩
  choose ωA ωB hωA hωB using fun t => _root_.GlobalTheory.T.weilRepresentation_square_comm hP D W.ψ W.ψ_std _ _ _ _ _ (hT t)
  have hbig : Node.InRange D.R.m (.grid (i + 1) (j + 1)) := ⟨i.2, j.2⟩
  have form : ∀ B (ρ : RealMatch W) t (M : Vol G), M.Is t → ∀ n Φ τ τ',
      (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) → HasFlip B t ρ i j n Φ τ τ' →
      ∃ (Pf : ModuleCat.{0} ℂ) (y : Pf) (J : Pr ⊗[ℂ] Pf →ₗ[ℂ] (GA D (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) → ℂ))
        (κ : _ → ℂ), (J = 0 ∨ Function.Injective J) ∧
        (∀ P, thetaInt (ωA t) (M.ν _) (M.fd _) (fockF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ) P) = J (q P ⊗ₜ y)) ∧
        ∀ g g₁ a, ∫ u in M.fd _, kerBig W (tensT W a τ) g g₁ u ∂M.ν _ = κ (g, g₁) * J (q (ι (toTens a)) ⊗ₜ y) (blk _ _ (g, g₁)) := by
    intro B ρ t M hM n Φ τ τ' hn hF
    obtain ⟨_, _, _, _, _, -, hc⟩ := _root_.GlobalTheory.SquareIdent.square_identity_reduction hP.howeDualityReal hP hLM hL W i j A A₁ AV AV₁ hA hA₁ hV hV₁ t B ρ M (hst t) hM (hT t)
      _ _ (hωA t) (hωB t)
    obtain ⟨_, hc⟩ := hc 0
    obtain ⟨Pf, y, J, h1, h2⟩ := H t _ _ (hM.vtx _ hbig).haar_fund _ (hωA t) _ (hc n Φ τ τ' hn hF).1
    obtain ⟨κ, hκ⟩ := (hD t).2 _ _ (hωA t) (hωB t)
    refine ⟨Pf, y, J, κ, h1, h2, fun g g₁ a => ?_⟩
    obtain ⟨b', hb'⟩ := ρ.onto_big i j (toTens a)
    obtain ⟨b, rfl⟩ := toTens_surjective b'
    rw [(hκ B ρ _ _ ⟨a, b, τ, τ', n, Φ, hb', hn, hF, rfl, rfl⟩).2.2.2.2.1 M g g₁, hι t B ρ n Φ τ τ' hF, h2]
  refine ⟨LinearMap.ker (q ∘ₗ ι), fun B ρ t x => ⟨fun h0 => ?_, fun hx M hM a ha n Φ τ τ' hn hF g g₁ => ?_⟩,
    fun x hx t ν 𝓕 hν ω hω f hf => ?_, fun B ρ t M hM n Φ τ τ' hn hF g g₁ => ?_⟩
  · obtain ⟨a, rfl⟩ := toTens_surjective x
    obtain ⟨M, hM, a₀, τ, τ', n, Φ, hn, hF, g, g₁, hne⟩ :=
      exists_integral_ne_zero hP.strongApproxSU hK hLM hL W B ρ t i j (hst t)
    obtain ⟨Pf, y, J, κ, h1, h2, h3⟩ := form B ρ t M hM n Φ τ τ' hn hF
    rw [h3] at hne
    have hy : y ≠ 0 := by rintro rfl; simp at hne
    have hJ : Function.Injective J := h1.resolve_left (by rintro rfl; simp at hne)
    have h4 := thetaInt_eq_zero hP.strongApproxSU hK hLM hL W B ρ t i j (hst t) hA hA₁ hV hV₁ (hωA t)
      (fun n Φ τ τ' hF => hι t B ρ n Φ τ τ' hF a) h0 hM hn hF
    rw [h2, ← map_zero J] at h4
    obtain ⟨c, hc⟩ := exists_scalar (Q := Pr) hy 0
    have h5 := congrArg (TensorProduct.comm ℂ Pr Pf) (hJ h4)
    rw [TensorProduct.comm_tmul, map_zero] at h5
    exact (hc _ 0 (h5.trans (TensorProduct.zero_tmul _ _).symm)).trans (smul_zero c)
  · obtain ⟨Pf, y, J, κ, -, -, h3⟩ := form B ρ t M hM n Φ τ τ' hn hF
    rw [h3, ha, show q (ι x) = 0 from hx, TensorProduct.zero_tmul, map_zero, Pi.zero_apply, mul_zero]
  · obtain ⟨Pf, y, J, -, h2⟩ := H t ν 𝓕 hν ω hω f hf
    rw [h2, show q (ι x) = 0 from hx, TensorProduct.zero_tmul, map_zero]
  · obtain ⟨Pf, y, J, κ, -, -, h3⟩ := form B ρ t M hM n Φ τ τ' hn hF
    exact ⟨κ (g, g₁) • (LinearMap.proj (blk _ _ (g, g₁)) ∘ₗ J ∘ₗ (TensorProduct.mk ℂ Pr Pf).flip y ∘ₗ q ∘ₗ ι), fun a => h3 g g₁ a⟩
theorem exists_scalar_of_realStandingData (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hLM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (hst : ∀ t, SquareStanding G t)
    (B : Frames G) (ρ ρ₀ : RealMatch W) (h1 : ρ₀.vX = ρ.vX) (h2 : ρ₀.vT = ρ.vT) (i j : Fin D.R.m) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ t c' c₀, IsSquareConst W B ρ t i j c' → GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀ → c₀ ≠ 0 ∧ c' = lam * c₀ ∧
      ∀ a a₀ b, (a, b) ∈ ρ.rel i j → (a₀, b) ∈ ρ₀.rel i j → ∀ t', IsNull W B ρ t' i j (a - lam • a₀) := by
  obtain ⟨A, hA⟩ := exists_isGridFr W (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩
  obtain ⟨AV, hV⟩ := exists_isGridFr W (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩
  obtain ⟨AV₁, hV₁⟩ := exists_isGridFr W (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩
  obtain ⟨ι, -, hι⟩ := realA hL W i j A AV AV₁ hA hV hV₁
  obtain ⟨K, hN, -, hl⟩ := _root_.GlobalTheory.RealSep.exists_nullSpace_realPlace hP hK hLM hL W hst i j hA hV hV₁ ι hι
  obtain ⟨x, hx⟩ := exists_not_isNull hP.strongApproxSU hK hLM hL W B ρ μ₀ i j (hst μ₀)
  rw [hN] at hx
  have key : ∀ t c' c₀, IsSquareConst W B ρ t i j c' → GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀ →
      ∀ a a₀ b, (a, b) ∈ ρ.rel i j → (a₀, b) ∈ ρ₀.rel i j → (c₀ • a - c' • a₀ ∈ K) ∧ (c' = 0 → a ∈ K) ∧ (c₀ = 0 → a₀ ∈ K) := by
    intro t c' c₀ hc hc₀ a a₀ b hab hab₀
    obtain ⟨a, rfl⟩ := toTens_surjective a
    obtain ⟨a₀, rfl⟩ := toTens_surjective a₀
    obtain ⟨b, rfl⟩ := toTens_surjective b
    have H : ∀ M : Vol G, M.Is t → ∀ n Φ τ τ', (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) →
        HasFlip B t ρ i j n Φ τ τ' → ∀ g g₁,
        ∃ (l : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) →ₗ[ℂ] ℂ) (r : ℂ),
          (∀ a, ∫ u in M.fd _, kerBig W (tensT W a τ) g g₁ u ∂M.ν _ = l (toTens a)) ∧ l (toTens a) = c' * r ∧
            l (toTens a₀) = c₀ * r := by
      intro M hM n Φ τ τ' hn hF g g₁
      obtain ⟨l, e⟩ := hl B ρ t M hM n Φ τ τ' hn hF g g₁
      have hΘ : IsMatched B t ρ i j (tensT W a τ) (tensT W b τ') := ⟨a, b, τ, τ', n, Φ, hab, hn, hF, rfl, rfl⟩
      obtain ⟨z, z0, z1, z2⟩ := hc₀ M hM _ _ ⟨a₀, b, τ, τ', n, Φ, hab₀, hn, hasFlip_congr h1 h2 hF, rfl, rfl⟩ g g₁
      have z3 := hc M hM _ _ hΘ z g g₁ ⟨_root_.GlobalTheory.FunObj.routeBig_kerBig_integrableOn (_root_.GlobalTheory.T.twisted_theta_integral_converges hP.siegelSetUnitary hP) hL W B ρ t i j
        (GlobalTheory.T.squareThetaTripleHypotheses_of_standing hL W t i j (hst t)) M hM _ _ hΘ g₁ g, z1.2⟩
      replace z2 := (congrArg (zdeg z * ·) (e a₀)).symm.trans z2
      replace z3 := (congrArg (zdeg z * ·) (e a)).symm.trans z3
      exact ⟨l, _ / zdeg z, e, by rw [← mul_div_assoc, ← z3, mul_div_cancel_left₀ _ z0],
        by rw [← mul_div_assoc, ← z2, mul_div_cancel_left₀ _ z0]⟩
    refine ⟨(hN B ρ t _).1 ?_, fun h => (hN B ρ t _).1 ?_, fun h => (hN B ρ t _).1 ?_⟩ <;>
    · intro M hM a' ha' n Φ τ τ' hn hF g g₁
      obtain ⟨l, r, e1, e2, e3⟩ := H M hM n Φ τ τ' hn hF g g₁
      rw [e1, ha']
      first
        | rw [map_sub, map_smul, map_smul, e2, e3, smul_eq_mul, smul_eq_mul]; ring
        | rw [e2, h, zero_mul]
        | rw [e3, h, zero_mul]
  obtain ⟨b, hb⟩ := ρ.onto_big i j x
  obtain ⟨x₀, hx₀⟩ := ρ₀.onto_small i j b
  obtain ⟨b₁, hb₁⟩ := ρ₀.onto_big i j x
  obtain ⟨x₁, hx₁⟩ := ρ.onto_small i j b₁
  by_cases hex : ∃ t c' c₀, IsSquareConst W B ρ t i j c' ∧ GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀
  swap
  · exact ⟨1, one_ne_zero, fun t c' c₀ h h₀ => absurd ⟨t, c', c₀, h, h₀⟩ hex⟩
  obtain ⟨s, d', d₀, hd, hd₀⟩ := hex
  have n₀ : ∀ t c' c₀, IsSquareConst W B ρ t i j c' → GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀ → c₀ ≠ 0 := fun t c' c₀ h h₀ e =>
    hx ((key t c' c₀ h h₀ _ _ _ hx₁ hb₁).2.2 e)
  have k : ∀ a a₀ b, (a, b) ∈ ρ.rel i j → (a₀, b) ∈ ρ₀.rel i j → a - (d' / d₀) • a₀ ∈ K := fun a a₀ b h h₀ => by
    have := K.smul_mem d₀⁻¹ (key s d' d₀ hd hd₀ a a₀ b h h₀).1
    rwa [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ (n₀ _ _ _ hd hd₀), one_smul, ← div_eq_inv_mul] at this
  refine ⟨d' / d₀, div_ne_zero (fun e => hx ((key s d' d₀ hd hd₀ _ _ _ hb hx₀).2.1 e)) (n₀ _ _ _ hd hd₀),
    fun t c' c₀ h h₀ => ⟨n₀ t c' c₀ h h₀, ?_, fun a a₀ b h h₀ t' => (hN B ρ t' _).2 (k a a₀ b h h₀)⟩⟩
  by_contra hne
  have e := K.sub_mem (key t c' c₀ h h₀ _ _ _ hx₁ hb₁).1 (K.smul_mem c₀ (k _ _ _ hx₁ hb₁))
  rw [smul_sub, sub_sub_sub_cancel_left, smul_smul, ← sub_smul] at e
  exact hx ((K.smul_mem_iff (sub_ne_zero.2 fun e => hne (by rw [← e, mul_comm]))).1 e)
end Null
section Main
open GlobalTheory.SquareComm GlobalTheory.SquareIdent GlobalTheory.SquareDict GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (alpha beta spV spW spW₁ spV₁)
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
theorem realPlace_theta_matching : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (B : Frames G) (ρ ρ₀ : RealMatch W), ρ₀.vX = ρ.vX → ρ₀.vT = ρ.vT →
      ∀ i j : Fin D.R.m, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (t : T) (c' c₀ : ℂ), IsSquareConst W B ρ t i j c' →
        GlobalTheory.SqTower.RegConst W B ρ₀ t i j c₀ → c₀ ≠ 0 ∧ c' = lam * c₀ := by
  intro hP hK hLM
  refine ⟨0, fun ε CF _ => ⟨0, (12 : ℝ) ^ (5 / ε), fun C _ D large₂ he hx hR T Lc μ₀ hL G W B ρ ρ₀ h1 h2 i j => ?_⟩⟩
  have hst := standing hR.size hL hR.size.2.1.eleven_le G
  obtain ⟨lam, h0, H⟩ := _root_.GlobalTheory.RealSep.exists_scalar_of_realStandingData hP hK hLM hL W hst B ρ ρ₀ h1 h2 i j
  exact ⟨lam, h0, fun t c' c₀ hc hc₀ => ⟨(H t c' c₀ hc hc₀).1, (H t c' c₀ hc hc₀).2.1⟩⟩
end Main
end GlobalTheory.RealSep
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_real_places_separation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (B : Frames G) (ρ ρ₀ : RealMatch W), ρ₀.vX = ρ.vX → ρ₀.vT = ρ.vT →
    ∀ i j : Fin D.R.m, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (t : T) (c' c₀ : ℂ), IsSquareConst W B ρ t i j c' → RegConst W B ρ₀ t i j c₀ → c₀ ≠ 0 ∧ c' = lam * c₀ := by
  first | exact @_root_.GlobalTheory.RealSep.realPlace_theta_matching | exact _root_.GlobalTheory.RealSep.realPlace_theta_matching | (intros; apply _root_.GlobalTheory.RealSep.realPlace_theta_matching <;> assumption)
end
end

