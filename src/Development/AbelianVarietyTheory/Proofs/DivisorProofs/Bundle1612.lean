module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzThetaPolynomialGrowth
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.FinDenom

theorem finDiv_finPart_mul' {F : Type} [Field F] [NumberField F] {N m : ℕ} {T : AF F} (hT : GlobalTheory.FinSupp.FinDiv F N ((m : AF F) * T))
    (a : 𝓞 F) : GlobalTheory.FinSupp.FinDiv F N (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F))) * T) := by
  intro v
  obtain ⟨b, hb, e⟩ := hT v
  have ha : algebraMap F (Fv F v) (a : F) ∈ v.adicCompletionIntegers F := HeightOneSpectrum.coe_mem_adicCompletionIntegers v a
  refine ⟨algebraMap F (Fv F v) (a : F) * b, mul_mem ha hb, ?_⟩
  have e1 : evFin F v (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F)))) =
      evFin F v (algebraMap F (AF F) ((m : F) * (a : F))) := rfl
  rw [map_mul, e1, AlgHom.commutes, map_mul, map_natCast]
  simp only [map_mul, map_natCast] at e
  rw [mul_comm ((m : Fv F v)) _, mul_assoc, e]
  ring

theorem finPart_mul_congr {F : Type} [Field F] [NumberField F] (x : AF F) {y z : AF F} (h : y.2 = z.2) :
    GlobalTheory.FinSupp.finPart F x * y = GlobalTheory.FinSupp.finPart F (x * z) :=
  Prod.ext (zero_mul _) (by show x.2 * y.2 = x.2 * z.2; rw [h])

theorem exists_denominator_of_finite_component : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
      ∀ (x : Fin n × Fin d → AF F) (ξ : Fin n × Fin d → F), (∀ i, (x i).2 = (algebraMap F (AF F) (ξ i)).2) →
        om (g, h) Φ x ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  have S := hP.weil.isUSplitting
  have hstd : IsStd B.ψ := hP.base.std
  obtain ⟨N, hN1, hinv⟩ := _root_.GlobalTheory.FinSuppHeis.heis_fix_finDiv F (Fin n × Fin d) B.ψ hstd.1 Φ hΦ
  obtain ⟨C, k, hC⟩ := _root_.GlobalTheory.MovedLat.exists_scale F E n d (Fin n × Fin d) M.co.e N hN1
  obtain ⟨D, hD1, hD⟩ := _root_.GlobalTheory.FinSupp.DenStd.exists_den F
  refine ⟨D * C, k, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hmT⟩ := hC g.1 h.1
  refine ⟨D * m, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, ?_⟩
  · push_cast
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmC (by positivity)
  · intro x ξ hxξ hξ i
    have key : ∀ a : 𝓞 F, B.ψ (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((a : F) * ((m : F) * ξ i)))) = 1 := by
      intro a
      set c : AF F := GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F))) with hc
      set y : Fin n × Fin d → AF F := c • Pi.single i 1 with hy
      set w' := M.co.e.symm (0, y) with hw'
      set p : UA σ X.J × UA σ W.J := (g, h) with hp
      set w := actAB (cA σ) p⁻¹ w' with hw
      have hwe : M.co.e w = c • M.co.e ((((g.1)⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) *
          M.co.e.symm (0, Pi.single i 1) * (((h.1⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ) := by
        rw [hw, hw', hy, hp]
        rw [show ((0 : Fin n × Fin d → AF F), c • Pi.single i (1 : AF F)) = c • ((0 : Fin n × Fin d → AF F), Pi.single i (1 : AF F)) by simp]
        rw [LinearEquiv.map_smul, ← LinearEquiv.map_smul M.co.e]
        congr 1
        simp only [actAB, Prod.inv_mk, Subgroup.coe_inv]
        rw [Matrix.mul_smul, Matrix.smul_mul]
      have hrho : M.co.rho B.ψ w Φ = Φ := by
        unfold Darboux.rho
        apply hinv
        intro l
        rw [hwe]
        obtain ⟨h1, h2⟩ := hmT i l
        refine ⟨?_, ?_, ?_, ?_⟩
        · show (c * _).1 = 0
          exact zero_mul _
        · rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
          exact finDiv_finPart_mul' h1 a
        · show (c * _).1 = 0
          exact zero_mul _
        · rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
          exact finDiv_finPart_mul' h2 a
      have himpl := S.impl p w Φ hΦ
      rw [hrho] at himpl
      have hact : actAB (cA σ) p w = w' := by
        rw [hw]
        simp only [actAB, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv, hp]
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
          Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
          Matrix.mul_one]
      rw [hact] at himpl
      have hx := congrFun himpl x
      simp only [Darboux.rho, hw', LinearEquiv.apply_symm_apply, schr, zero_dotProduct, mul_zero, add_zero] at hx
      have h1 : B.ψ (x ⬝ᵥ y) = 1 := by
        have hne : om p Φ x ≠ 0 := hξ
        exact (mul_eq_right₀ hne).1 hx.symm
      rw [hy, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one, hc, finPart_mul_congr _ (hxξ i), ← map_mul] at h1
      convert h1 using 3
      ring_nf
    have := hD B.ψ hstd _ key
    convert this using 1
    push_cast
    ring

end GlobalTheory.FinDenom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeInvariantVector
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section
namespace GlobalTheory.SelfDualFirstProjAny

theorem exists_valuation_eq (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    ∃ a : v.adicCompletion F, Valued.v a = WithZero.exp n := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨(π : v.adicCompletion F) ^ (-n), ?_⟩
  rw [map_zpow₀, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  simp [← WithZero.exp_zsmul]

theorem exists_pair_of_annihilator_any : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
    ∀ (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v), c ≠ 0 →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψ (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ η : κ → Fv F v, (∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψ (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ := by
  intro F _ _ v κ _ ψ hcont hnorm hne Λ c hc hself hbd η hη
  classical
  have hne' : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (by ext t; simpa using h t)
  obtain ⟨n, hn⟩ := GlobalTheory.CharConductor.exists_conductor_exponent F v ψ hcont hnorm hne'
  obtain ⟨a, ha⟩ := exists_valuation_eq F v n
  have ha0 : a ≠ 0 := by
    intro h; rw [h, map_zero] at ha; exact WithZero.zero_ne_coe ha
  let O := v.adicCompletionIntegers F
  let ψ₀ : AddChar (Fv F v) ℂ := ψ.mulShift a
  have hψ₀ : ∀ x, ψ₀ x = ψ (a * x) := fun x => rfl

  have hcond : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) ↔
      x ∈ v.adicCompletionIntegers F := by
    intro x
    have := hn (a * x)
    simp only [hψ₀, mul_assoc] at this ⊢
    rw [this, map_mul, ha, HeightOneSpectrum.mem_adicCompletionIntegers]
    have e : Valued.v x = WithZero.exp (-n) * (WithZero.exp n * Valued.v x) := by
      rw [← mul_assoc, ← WithZero.exp_add]; simp
    constructor
    · intro h
      rw [e]
      calc WithZero.exp (-n) * (WithZero.exp n * Valued.v x) ≤ WithZero.exp (-n) * WithZero.exp n := by gcongr
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · intro h
      calc WithZero.exp n * Valued.v x ≤ WithZero.exp n * 1 := by gcongr
        _ = WithZero.exp n := mul_one _

  let f : ((κ → Fv F v) × (κ → Fv F v)) →+ ((κ → Fv F v) × (κ → Fv F v)) :=
    { toFun := fun w => (w.1, a • w.2)
      map_zero' := by simp
      map_add' := by intro x y; simp [smul_add] }
  let Λ₀ := Λ.comap f
  have hmem : ∀ w, w ∈ Λ₀ ↔ (w.1, a • w.2) ∈ Λ := fun w => Iff.rfl
  have hback : ∀ l : (κ → Fv F v) × (κ → Fv F v), (l.1, a • (a⁻¹ • l.2)) = l := by
    intro l; rw [smul_smul, mul_inv_cancel₀ ha0, one_smul]
  have hself₀ : ∀ w, w ∈ Λ₀ ↔ ∀ l ∈ Λ₀, ψ₀ (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1 := by
    intro w
    rw [hmem, hself]
    constructor
    · intro h l hl
      have := h (l.1, a • l.2) hl
      rw [hψ₀]
      convert this using 2
      simp only [mul_sub, dotProduct_smul, smul_eq_mul]
    · intro h l hl
      have hl' : (l.1, a⁻¹ • l.2) ∈ Λ₀ := by rw [hmem]; simpa [hback l] using hl
      have := h _ hl'
      rw [hψ₀] at this
      convert this using 2
      simp only [mul_sub, dotProduct_smul, smul_eq_mul, smul_dotProduct]
      rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]

  obtain ⟨c', hc', hbd₀⟩ : ∃ c' : Fv F v, c' ≠ 0 ∧ ∀ l ∈ Λ₀, ∀ i,
      c' * l.1 i ∈ v.adicCompletionIntegers F ∧ c' * l.2 i ∈ v.adicCompletionIntegers F := by
    rcases O.mem_or_inv_mem a with haO | haO
    · refine ⟨c * a, mul_ne_zero hc ha0, fun l hl i => ?_⟩
      have h := hbd _ ((hmem l).1 hl) i
      simp only [Pi.smul_apply, smul_eq_mul] at h
      refine ⟨?_, ?_⟩
      · have e : c * a * l.1 i = a * (c * l.1 i) := by ring
        rw [e]; exact O.toSubring.mul_mem haO h.1
      · have e : c * a * l.2 i = c * (a * l.2 i) := by ring
        rw [e]; exact h.2
    · refine ⟨c, hc, fun l hl i => ?_⟩
      have h := hbd _ ((hmem l).1 hl) i
      simp only [Pi.smul_apply, smul_eq_mul] at h
      refine ⟨h.1, ?_⟩
      have e : c * l.2 i = a⁻¹ * (c * (a * l.2 i)) := by
        rw [mul_left_comm, ← mul_assoc a⁻¹ a, inv_mul_cancel₀ ha0, one_mul]
      rw [e]; exact O.toSubring.mul_mem haO h.2
  have hη₀ : ∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ₀ → ψ₀ (η ⬝ᵥ b) = 1 := by
    intro b hb
    rw [hmem] at hb
    rw [hψ₀, ← smul_eq_mul, ← dotProduct_smul]
    exact hη _ hb
  obtain ⟨y, hy⟩ := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v ψ₀ Λ₀ c' hc' hcond hself₀ hbd₀ η hη₀
  exact ⟨a • y, (hmem _).1 hy⟩

end GlobalTheory.SelfDualFirstProjAny
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralConjugateScaledUnitaryGroupEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjUIntegral

theorem setIntegral_conjU_eq : ∀ {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E), c ≠ 0 →
    ∀ (h : J = c • V.gram) (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) fd ν →
    ∀ dom : Set (UB J), IsFundamentalDomain (ratU D.sp.cm.sig J) dom (ν.map (conjU V c h)) →
    ∀ f : UB J → ℂ, (∀ γ ∈ ratU D.sp.cm.sig J, ∀ x, f (γ * x) = f x) →
      ∫ u in fd, f (conjU V c h u) ∂ν = ∫ x in dom, f x ∂(ν.map (conjU V c h)) := by
  intro D V J c hc h ν fd hν hfd dom hdom f hf
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  have : BorelSpace (UB J) := ⟨rfl⟩
  let φ := GlobalTheory.ConjUTransport.conjEquiv V c hc h
  have c1 : Continuous φ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU V c h
  have c2 : Continuous φ.symm := GlobalTheory.ConjUTransport.continuous_conjUInv V c hc h
  let H : GA D V ≃ₜ UB J := ⟨φ.toEquiv, c1, c2⟩
  have hme : MeasurableEmbedding (conjU V c h) := H.measurableEmbedding
  obtain ⟨hH, hfd'⟩ := GlobalTheory.ConjUTransport.map_isHaar_isFundamentalDomain V c hc h ν fd hν hfd
  have e1 : ∫ x in conjU V c h '' fd, f x ∂(ν.map (conjU V c h)) = ∫ u in fd, f (conjU V c h u) ∂ν := by
    rw [hme.setIntegral_map, Set.preimage_image_eq _ hme.injective]
  rw [← e1]
  haveI := GlobalTheory.UnitaryVol.countable_ratU D.sp.cm.sig J
  haveI := hH
  haveI : SMulInvariantMeasure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (UB J) (ν.map (conjU V c h)) :=
    ⟨fun γ A _ => measure_preimage_mul (ν.map (conjU V c h)) γ.1 A⟩
  exact hfd'.setIntegral_eq hdom fun γ x => hf γ.1 γ.2 x

end GlobalTheory.ConjUIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewSelfDualLatticeLocalisedAtPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

namespace GlobalTheory.SkewLocDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_smul_left (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (c : E) (x y : Fin d → E) :
    form σ J (c • x) y = c * form σ J x y := by
  simp [form, smul_dotProduct]

theorem form_add_right (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (x y z : Fin d → E) :
    form σ J x (y + z) = form σ J x y + form σ J x z := by
  have h : (fun i => σ ((y + z) i)) = (fun i => σ (y i)) + fun i => σ (z i) := funext fun i => by simp
  simp only [form, h, Matrix.mulVec_add, dotProduct_add]

theorem form_zero_right (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (x : Fin d → E) :
    form σ J x 0 = 0 := by
  have h : (fun i => σ ((0 : Fin d → E) i)) = 0 := funext fun i => by simp
  simp only [form, h, Matrix.mulVec_zero, dotProduct_zero]

theorem form_smul_right (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (o : 𝓞 E) (x y : Fin d → E) :
    form σ J x (o • y) = σ (o : E) * form σ J x y := by
  have h : (fun i => σ ((o • y) i)) = σ (o : E) • fun i => σ (y i) := funext fun i => by
    simp [Algebra.smul_def]
  simp only [form, h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem isIntegral_algebraMap_int (a : 𝓞 F) : IsIntegral ℤ (algebraMap F E (a : F)) :=
  (NumberField.RingOfIntegers.isIntegral_coe a).map (algebraMap F E).toIntAlgHom

theorem isIntegral_conj (σ : E →ₐ[F] E) (o : 𝓞 E) : IsIntegral ℤ (σ (o : E)) :=
  (NumberField.RingOfIntegers.isIntegral_coe o).map (σ : E →+* E).toIntAlgHom

end GlobalTheory.SkewLocDual

open GlobalTheory.SkewLocDual in
theorem GlobalTheory.SkewLocDual.exists_smul_mem_of_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {d r s : ℕ} (Y : Spc F E d), Y.IsSkew σ B r s → ∀ (v : Pl (F := F)) (u : Fin d → E),
    (∀ y ∈ Y.L, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap F E (t : F) * form σ Y.J u y)) →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • u ∈ Y.L := by
  intro F E _ _ _ _ _ σ B d r s Y hY v u hu
  classical
  haveI := v.isPrime
  obtain ⟨S, hS⟩ := hY.lat.fg
  have hgen : ∀ y ∈ S, y ∈ Y.L := fun y hy => hS ▸ Submodule.subset_span hy
  choose! T hT using fun y (hy : y ∈ S) => hu y (hgen y hy)
  have ht : (∏ y ∈ S, T y) ∉ v.asIdeal := by
    rw [Ideal.IsPrime.prod_mem_iff]
    push_neg
    exact fun y hy => (hT y hy).1
  have key : ∀ y ∈ Y.L,
      IsIntegral ℤ (algebraMap F E ((∏ y ∈ S, T y : 𝓞 F) : F) * form σ Y.J u y) := by
    rw [← hS]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      have hsplit : algebraMap F E ((∏ y ∈ S, T y : 𝓞 F) : F) =
          algebraMap F E ((∏ y ∈ S.erase x, T y : 𝓞 F) : F) * algebraMap F E (T x : F) := by
        rw [← map_mul, ← Finset.prod_erase_mul S T hx]; rfl
      rw [hsplit, mul_assoc]
      exact (isIntegral_algebraMap_int _).mul (hT x hx).2
    | zero => simpa [form_zero_right] using (isIntegral_zero : IsIntegral ℤ (0 : E))
    | add x y _ _ hx hy => rw [form_add_right, mul_add]; exact hx.add hy
    | smul o x _ hx => rw [form_smul_right, mul_left_comm]; exact (isIntegral_conj σ o).mul hx
  refine ⟨∏ y ∈ S, T y, ht, (hY.dual _).2 fun x hx o => ?_⟩
  rw [form_smul_left]
  exact Algebra.isIntegral_trace ((NumberField.RingOfIntegers.isIntegral_coe o).mul (key x hx))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberHalfIsometryMoved
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriMove.StdFstMove

variable {D : D7}

private theorem rdi_mul_rdx {K : Type} [CommRing K] {m n m' n' : ℕ} (h : m = n) (h' : m' = n') (M : Matrix (Fin m) (Fin m') K) :
    HMul.hMul (HMul.hMul (rdi (K := K) h) M) (rdx (K := K) h') = M.submatrix (finCongr h).symm (finCongr h').symm := by
  subst h; subst h'
  ext i j
  simp [rdi, rdx, Matrix.mul_apply, Matrix.one_apply]

private theorem isIntM_re {a a' b b' : ℕ} (ha : a = a') (hb : b = b') (M : Matrix (Fin b) (Fin a) (Formalism.IndefR.Datum.EAf D)) :
    Formalism.IndefR.Datum.IsIntM (D := D) (M.submatrix (finCongr hb).symm (finCongr ha).symm) ↔ Formalism.IndefR.Datum.IsIntM (D := D) M := by
  subst ha; subst hb; simp

private theorem inId_re (I : Ideal (𝓞 D.host.E)) {a a' b b' : ℕ} (ha : a = a') (hb : b = b') (M : Matrix (Fin b) (Fin a) (Formalism.IndefR.Datum.EAf D)) :
    (∀ i j, a' ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (M.submatrix (finCongr hb).symm (finCongr ha).symm i j)) ↔
      ∀ i j, a ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (M i j) := by
  subst ha; subst hb; simp

private theorem unitChar_re (ν : (AE D)ˣ →* Circle) (e : AE D) {a a' b b' : ℕ} (ha : a = a') (hb : b = b')
    (M : Matrix (Fin b) (Fin a) (Formalism.IndefR.Datum.EAf D)) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e (Formalism.IndefR.Datum.topL a' (M.submatrix (finCongr hb).symm (finCongr ha).symm)) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e (Formalism.IndefR.Datum.topL a M) := by
  subst ha; subst hb; simp

private theorem fixed_two {R : Type} [CommRing R] {p q r s : ℕ} (e : R) (M : Matrix (Fin p) (Fin q) R) (N : Matrix (Fin r) (Fin s) R)
    (x : Matrix (Fin q) (Fin r) R) (H : ∀ i j, e * x i j = x i j) (i : Fin p) (j : Fin s) :
    e * (M * x * N) i j = (M * x * N) i j := by
  have hx : e • x = x := by ext i j; exact H i j
  have : e • (M * x * N) = M * x * N := by rw [← Matrix.smul_mul, ← Matrix.mul_smul, hx]
  exact congrFun (congrFun this i) j

variable {S S' T T' : HSp D}

private theorem isHalf_homMap (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (e : AE D) (x : WO S T) :
    Formalism.IndefR.Datum.IsHalf e (homMap IS IT x) ↔ Formalism.IndefR.Datum.IsHalf e x := by
  constructor
  · intro h
    have hx : x = HMul.hMul (HMul.hMul IT.aQ (homMap IS IT x)) IS.aP := ((homMap IS IT).symm_apply_apply x).symm
    intro i j
    rw [hx]
    exact fixed_two e _ _ _ h i j
  · intro h i j
    exact fixed_two e _ _ _ h i j

private theorem map_aP (I : GlobalTheory.Mem.Isom.IsoMat S S') : I.aP.map (Formalism.IndefR.Datum.toEAf D) = fP I := by
  ext i j; rfl

private theorem map_aQ (I : GlobalTheory.Mem.Isom.IsoMat S S') : I.aQ.map (Formalism.IndefR.Datum.toEAf D) = fQ I := by
  ext i j; rfl

private theorem frMapO_homMap (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T')
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (x : WO S T) :
    frMapO S' T' (betaMove IS βS) (betaMove IT βT) (homMap IS IT x) =
      HMul.hMul (HMul.hMul (rdi (K := Lev.EAf D) IT.rank_eq) (frMapO S T βS βT x)) (rdx (K := Lev.EAf D) IS.rank_eq) := by
  unfold frMapO
  rw [homMap_apply]
  show HMul.hMul (HMul.hMul (HMul.hMul (HMul.hMul (rdi (K := Lev.EAf D) IT.rank_eq) (βT⁻¹).val) (fQ IT))
      ((HMul.hMul (HMul.hMul IT.aP x) IS.aQ).map (Formalism.IndefR.Datum.toEAf D)))
      (HMul.hMul (HMul.hMul (fP IS) βS.val) (rdx (K := Lev.EAf D) IS.rank_eq)) = _
  rw [Matrix.map_mul, Matrix.map_mul, map_aP, map_aQ]
  calc _ = HMul.hMul (HMul.hMul (HMul.hMul (HMul.hMul (HMul.hMul (HMul.hMul (rdi (K := Lev.EAf D) IT.rank_eq) (βT⁻¹).val) (HMul.hMul (fQ IT) (fP IT)))
            (x.map (Formalism.IndefR.Datum.toEAf D))) (HMul.hMul (fQ IS) (fP IS))) βS.val) (rdx (K := Lev.EAf D) IS.rank_eq) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by rw [fQ_fP, fQ_fP, Matrix.mul_one, Matrix.mul_one, ← Matrix.mul_assoc (rdi _), ← Matrix.mul_assoc (rdi _)]

private theorem stdFst_move : ∀ {D : D7} {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)),
  GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S' T' (GlobalTheory.TriMove.betaMove IS βS) (GlobalTheory.TriMove.betaMove IT βT) = GlobalTheory.TriMove.trH IS IT (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT) := by
  intro D S S' T T' IS IT ν e I βS βT
  classical
  funext w
  obtain ⟨x, rfl⟩ := (homMap IS IT).surjective w
  unfold trH
  rw [AddEquiv.symm_apply_apply]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  rw [frMapO_homMap, rdi_mul_rdx]
  exact if_congr (and_congr (isHalf_homMap IS IT e x) (and_congr (isIntM_re _ _ _) (inId_re I _ _ _))) (unitChar_re ν e _ _ _) rfl

end GlobalTheory.TriMove.StdFstMove

end

theorem _root_.GlobalTheory.T.standardPairFirstMemberHalf_isometry_moved : ∀ {D : D7} {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)),
  GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S' T' (GlobalTheory.TriMove.betaMove IS βS) (GlobalTheory.TriMove.betaMove IT βT) = GlobalTheory.TriMove.trH IS IT (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT) := @GlobalTheory.TriMove.StdFstMove.stdFst_move
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedByElementaryStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_group_generated_by_elementary : ∀ (K : Type) [Field K] [CharZero K] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix (κ ⊕ κ) (κ ⊕ κ) K),
    GlobalTheory.SympChange.IsSymp G → G ∈ Submonoid.closure (GlobalTheory.SympChange.gens (F := K) (κ := κ)) := by
  first | exact @GlobalTheory.SympChangeGen.mem_closure_gens | exact GlobalTheory.SympChangeGen.mem_closure_gens | (intros; apply GlobalTheory.SympChangeGen.mem_closure_gens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForLeviMatrixStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_for_levi_matrix : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F), IsUnit A.det →
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.leviM A) := by
  first | exact @GlobalTheory.LeviOp.hasOp_levi | exact GlobalTheory.LeviOp.hasOp_levi | (intros; apply GlobalTheory.LeviOp.hasOp_levi <;> assumption)
end

