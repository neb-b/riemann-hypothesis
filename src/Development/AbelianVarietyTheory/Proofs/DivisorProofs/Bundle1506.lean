module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TestFnConstTermVanishX
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0360
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Formalism.LocalToGlobal.GlobalTheory.GL3.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1485
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonFieldTypeVanishingX
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Proof.parabolic_and_constant_term
section Star
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}
end Star

theorem testFnConstTermVanishX : TestFnConstTermVanishX := by
  intro D V hodd S M T hH U μa _ μf _ f hf 𝔉 hP
  obtain ⟨a, ha0, ha2, hpar⟩ := parabolicAtSplitPlaces D V hodd T 𝔉 hP
  obtain ⟨v, hv⟩ := hH a ha0 (by omega)
  obtain ⟨fa, ff, hfa, hff, rfl⟩ := hf
  obtain ⟨h, hh, e⟩ := hff.2.1 v
  have hA : ∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w := hfa.mem
  have hF := hff.isFinFamily
  have he := (T.frame v).idem_mem (μf v.1) (T.τ v)
  constructor
  · refine _root_.GlobalTheory.TestConstTerm.unipIntegralsVanish_tensor D V 𝔉 fa ff hA hF v.1 fun ν _ x y => ?_
    exact (_root_.GlobalTheory.LocConst.unip_integral_vanish D V T v a ha0 (by omega) hv 𝔉 (hpar v).1 (μf v.1) _ (conv_mem_SB he hh) (ff v.1) (Or.inr e)
      ν x y).2
  · rw [starFn_tensor]
    refine _root_.GlobalTheory.TestConstTerm.unipIntegralsVanish_tensor D V 𝔉 _ _ (fun w => starFn_mem_ccArch (hA w)) (isFinFamily_starFn hF) v.1 fun ν _ x y => ?_
    have e' : starFn (ff v.1) = GlobalTheory.AutomorphicL2Unitary.conv (μf v.1) ((T.frame v).idem (μf v.1) (T.τ v))
        (GlobalTheory.AutomorphicL2Unitary.conv (μf v.1) (starFn h) ((T.frame v).idem (μf v.1) (T.τ v))) := by
      rw [e, starFn_conv, starFn_conv]
      simp only [TypeData.idem, SplitAt.starFn_idem]
    exact (_root_.GlobalTheory.LocConst.unip_integral_vanish D V T v a ha0 (by omega) hv 𝔉 (hpar v).1 (μf v.1) _ (conv_mem_SB (starFn_mem_SB hh) he) _
      (Or.inl e') ν x y).2

theorem parabolicAndConstTermX : ParabolicAndConstTermX := ⟨parabolicAtSplitPlaces, testFnConstTermVanishX⟩
end GlobalTheory.Proof.parabolic_and_constant_term
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.PsCo.Plug.parabolicT : GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTermX := by
  first | exact @GlobalTheory.Proof.parabolic_and_constant_term.parabolicAndConstTermX | exact GlobalTheory.Proof.parabolic_and_constant_term.parabolicAndConstTermX | (intros; apply GlobalTheory.Proof.parabolic_and_constant_term.parabolicAndConstTermX <;> assumption)
end

section
open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms (plusAlg genAlg)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH NoFixed radical)
open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt
open scoped TensorProduct ENNReal
noncomputable section
namespace GlobalTheory.NonFieldType
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {V : HSp D}
set_option maxHeartbeats 4000000 in
theorem productClauseX {S : D.what₂.Tau → SPar} {M : DSModel V S} {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V}
    {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {μ : Measure (GA D V)} (hμ : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ)
    {fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (ha : IsTestArchGX M μa fa) (hf : IsTestFin T U μf ff)
    {γ : GRat D.sp.cm.sig V.gram} (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1) :
    ProductClause μa μf μ fa ff (ratEmb D.sp.cm.sig V.gram γ) := by
  intro dta dtf dt hdt 𝓣 h𝓣
  have hreg := hγ.1
  have hcm := isCMExt_host D
  have hJ := isHermND_gram V
  obtain ⟨hta, htf, htt, -⟩ := id hdt
  have i1 : ∀ w, (dta w).IsMulRightInvariant := fun w =>
    haveI := hta w; isMulRightInvariant_cent (isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hreg w)) _
  have i2 : ∀ v, (dtf v).IsMulRightInvariant := fun v =>
    haveI := htf v; isMulRightInvariant_cent (isMulCommutative_cent_HA (isRegSS_proj_ratEmb hreg v)) _
  have hvol : dt 𝓣 < ⊤ := @covol_lt_top D V γ hγ dt htt 𝓣 h𝓣
  have hfa : ∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w) := fun w =>
    ⟨continuous_of_mem_ccSmooth (continuous_archCoord _ _ w) (ha.mem w), (ha.mem w).1⟩
  have hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hf.isFinFamily
  have hKv := (regular_semisimple_adelic hcm hJ (frameLat V) γ hreg).1
  have hpa : ∀ w, IsProperOrbit (cent (projArch D.sp.cm.sig V.gram w (ratEmb D.sp.cm.sig V.gram γ)))
      (projArch D.sp.cm.sig V.gram w (ratEmb D.sp.cm.sig V.gram γ)) := fun w =>
    isProperOrbit_GArch hcm hJ (isRegSS_projArch_ratEmb hreg w)
  have hpf : ∀ v, IsProperOrbit (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ)))
      (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ)) := fun v =>
    isProperOrbit_GLoc hcm hJ (isRegSS_proj_ratEmb hreg v)
  obtain ⟨-, hoa, hob, h1, hO⟩ := @hasOrbInt_tensor _ _ _ _ _ _ _ _ _ _ (frameLat V) _ μa μf μ _ dta dtf dt fa ff
    hμ hdt i1 i2 hfa hff hKv (fun w => Or.inl (hpa w)) (fun v => Or.inl (hpf v))
  refine ⟨hvol, _, _, hoa, hob, h1, hO, fun 𝓕 h𝓕 => ?_⟩
  have hc := continuous_of_mem_ccAd (tensor_mem_ccAd ha.mem hf.isFinFamily)
  exact @_root_.GlobalTheory.ClassUnfold.hasClassInt_of_hasOrbInt (GA D V) _ _ _ _ _ _ _ _ (GQ V) _ (ratEmb D.sp.cm.sig V.gram γ) (ratEmb_mem_GQ γ)
    (isMulCommutative_cent_ratEmb hreg) μ hμ.2.2.1 dt htt 𝓣 h𝓣 hvol _ _ hc.1 hc.2 hO 𝓕 h𝓕

set_option maxHeartbeats 4000000 in
theorem nonFieldTypeVanishingX : NonFieldTypeVanishingX := by
  intro D V _ S M T U hH μa μf μ hμ fa ff ha hf γ hγ
  have hL := localClause (fun v => hμ.2.1 v) hf hγ
  have hP := productClauseX hμ ha hf hγ
  exact ⟨hL, hP, zeroClause hH hγ hL hP⟩
end GlobalTheory.NonFieldType
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.PsCo.Plug.nonFieldT : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.NonFieldTypeVanishingX := by
  first | exact @GlobalTheory.NonFieldType.nonFieldTypeVanishingX | exact GlobalTheory.NonFieldType.nonFieldTypeVanishingX | (intros; apply GlobalTheory.NonFieldType.nonFieldTypeVanishingX <;> assumption)
end

section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
noncomputable section
namespace GlobalTheory.TrEllSum

theorem ellipticPartX : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.EllipticPartX := by
  intro D V lam S M T U μa μf μ fa ff h dta dtf dt ht
  obtain ⟨-, -, -, -, hμ, ha, hf⟩ := h
  exact elliptic_expansion (isCMExt_host D) (GlobalTheory.InertOfConj.unram D) (isHermND_gram V) (frameLat V) hμ ha.mem hf.isFinFamily
    dta dtf dt ht _ rfl _ rfl
end GlobalTheory.TrEllSum
end
end

section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.PsCo.Plug.ellipticT : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.EllipticPartX := by
  first | exact @GlobalTheory.TrEllSum.ellipticPartX | exact GlobalTheory.TrEllSum.ellipticPartX | (intros; apply GlobalTheory.TrEllSum.ellipticPartX <;> assumption)
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNonzeroThetaVectorsNumberField
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem GlobalTheory.ColNorms.familyVectors : GlobalTheory.ColNorms.FamilyVectors := by
  intro D cc δ B χ _ _ hc hδ hχ _ N N' L L' hA
  obtain ⟨h1, h2⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.vector_bound_link D cc hc δ hδ B χ hχ N N' L L' hA
  refine ⟨h1, h2, ?_⟩
  obtain ⟨χ', e, -, hv, -⟩ := GlobalTheory.TrueTheta.exists_family_of_curve D cc δ ⟨hc, hδ⟩
  obtain ⟨e1, e2, M, hM, hC⟩ := hv N N' L L' hA
  obtain ⟨c, hcE⟩ := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ ⟨hc, hδ⟩ N N' _
    (Or.inr ⟨_, _, hA.2.2.1, hA.2.2.2, rfl⟩)).1 _ h1 _ e1 e2
  have hE : B.eNat χ N N' L L' = fun z => c * e N N' L L' z := hcE
  have hQ : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α ∈ Qbar := by
    intro α
    have := GlobalTheory.ThLoc.algTAll D cc δ B χ hc hδ hχ N N' L L' hA 0 ⟨1, one_pos, by simpa using zero_mem _⟩ α
    have hU : U D B.tor 0 (B.eNat χ N N' L L') = B.eNat χ N N' L L' := by
      funext z; simp [U, Hf]
    rwa [hU] at this
  have ht : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α = c * Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α := fun α => by
    rw [hE, GlobalTheory.ProdThetaConj.taylor_const_mul e1.1]
  obtain ⟨α, hα⟩ : ∃ α, Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α ≠ 0 := by
    by_contra h
    push_neg at h
    apply e2
    funext z
    rw [← GlobalTheory.ProdThetaConj.tsum_taylor_mono D e1.1 z]
    simp [h]
  have hMQ : ∀ x ∈ M, x ∈ Qbar := fun x hx => mem_algebraicClosure_iff.2
    (IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (⟨x, hx⟩ : M)))
  have hcQ : c ∈ Qbar := by
    have : c = Formalism.MainNotions.TaylorLogMetric.taylor D (B.eNat χ N N' L L') α / Formalism.MainNotions.TaylorLogMetric.taylor D (e N N' L L') α := by rw [ht, mul_div_cancel_right₀ _ hα]
    rw [this]
    exact div_mem (hQ α) (hMQ _ (hC α))
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {c}) :=
    IntermediateField.adjoin.finiteDimensional (mem_algebraicClosure_iff.1 hcQ).isIntegral
  refine ⟨M ⊔ IntermediateField.adjoin ℚ {c}, IntermediateField.finiteDimensional_sup _ _, fun β => ?_⟩
  rw [ht]
  exact mul_mem ((le_sup_right : IntermediateField.adjoin ℚ {c} ≤ _) (IntermediateField.subset_adjoin ℚ {c} (Set.mem_singleton _)))
    ((le_sup_left : M ≤ _) (hC β))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseNeZero
section
noncomputable section

open Formalism.BasicNotions IsDedekindDomain NumberField Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.HeckeUOps

variable {D : D7}

theorem phase_ne_zero (τ : D.what₂.Tau) (a : D.host.Eˣ) :
    embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ) ≠ 0 := by
  have h : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
  exact div_ne_zero h (by exact_mod_cast (norm_ne_zero_iff.2 h))

def mul {N₁ N₂ : ℕ} (N : ℕ) (χ₁ : HeckeU D N₁) (χ₂ : HeckeU D N₂) (h : Even ((N₁ : ℤ) + N₂ - N)) : HeckeU D N where
  f := χ₁.f * χ₂.f
  n := χ₁.n + χ₂.n
  unitary x := by
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, χ₁.unitary, χ₂.unitary, one_mul]
  cont := by
    obtain ⟨m₁, hm₁, h₁⟩ := χ₁.cont
    obtain ⟨m₂, hm₂, h₂⟩ := χ₂.cont
    refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, fun u hu ⟨s, hs, e⟩ => ?_⟩
    rw [MonoidHom.mul_apply, h₁ u hu ⟨m₂ * s, mul_mem (natCast_mem _ _) hs, by rw [e]; push_cast; ring⟩,
      h₂ u hu ⟨m₁ * s, mul_mem (natCast_mem _ _) hs, by rw [e]; push_cast; ring⟩, one_mul]
  aut a := by
    have h1 := χ₁.aut a
    have h2 := χ₂.aut a
    have e : ∀ τ ∈ Finset.univ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ ((χ₁.n + χ₂.n) τ) =
        (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ₁.n τ) *
          (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ₂.n τ) := fun τ _ => by
      rw [Pi.add_apply, zpow_add₀ (phase_ne_zero τ a)]
    rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, MonoidHom.mul_apply, Units.val_mul]
    calc _ = (((χ₁.f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) *
          ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ₁.n τ)) *
        (((χ₂.f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) *
          ∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ₂.n τ)) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  norm x := by rw [MonoidHom.mul_apply, χ₁.norm, χ₂.norm, one_mul]
  par τ := by
    have := (χ₁.par τ).add ((χ₂.par τ).add h)
    have e : (χ₁.n + χ₂.n) τ - (N : ℤ) = χ₁.n τ - N₁ + (χ₂.n τ - N₂ + (N₁ + N₂ - N)) := by
      simp only [Pi.add_apply]; ring
    rw [e]; exact this
  unr u hu hz := by rw [MonoidHom.mul_apply, χ₁.unr u hu hz, χ₂.unr u hu hz, one_mul]

def inv {N : ℕ} (N' : ℕ) (χ : HeckeU D N) (h : Even ((N : ℤ) - N')) : HeckeU D N' where
  f := χ.f⁻¹
  n := -χ.n
  unitary x := by rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, χ.unitary, inv_one]
  cont := by
    obtain ⟨m, hm, h₁⟩ := χ.cont
    exact ⟨m, hm, fun u hu hs => by rw [MonoidHom.inv_apply, h₁ u hu hs, inv_one]⟩
  aut a := by
    have h1 := χ.aut a
    have e : ∀ τ ∈ Finset.univ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ ((-χ.n) τ) =
        ((embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ.n τ))⁻¹ := fun τ _ => by
      rw [Pi.neg_apply, zpow_neg]
    rw [Finset.prod_congr rfl e, Finset.prod_inv_distrib, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, ← mul_inv, h1,
      inv_one]
  norm x := by rw [MonoidHom.inv_apply, χ.norm, inv_one]
  par τ := by
    have := ((χ.par τ).neg.sub h).sub (even_two_mul (N' : ℤ))
    have e : (-χ.n) τ - (N' : ℤ) = -(χ.n τ - N) - (N - N') - 2 * N' := by
      simp only [Pi.neg_apply]; ring
    rw [e]; exact this
  unr u hu hz := by rw [MonoidHom.inv_apply, χ.unr u hu hz, inv_one]

def ofChar (N : ℕ) (χ : HChar D.host.E) (n : D.what₂.Tau → ℤ) (hu : χ.IsUnitary) (hi : χ.HasInf (embT D) n)
    (hc : ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) → χ.1 (finIdl D u) = 1)
    (hn : ∀ x, χ.1 (finIdl D (x * sgU D x)) = 1) (hp : ∀ τ, Even (n τ - (N : ℤ)))
    (hr : ∀ u, IntU D u → (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((u : AE D) - 1)) → χ.1 (finIdl D u) = 1) :
    HeckeU D N where
  f := χ.1.comp (finIdl D)
  n := n
  unitary _ := hu _
  cont := hc
  aut a := by
    have h1 := χ.2.2 a
    rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← GlobalTheory.Mem.Col2.SplitChar.finIdl_incU, mul_comm] at h1
    have h3 := congrArg (Units.val : ℂˣ → ℂ) h1
    rw [Units.val_mul, Units.val_one] at h3
    rw [← h3]
    exact congrArg _ (hi a).symm
  norm := hn
  par := hp
  unr := hr

@[simp] theorem mul_f {N₁ N₂ N : ℕ} (χ₁ : HeckeU D N₁) (χ₂ : HeckeU D N₂) (h) (x) :
    (mul N χ₁ χ₂ h).f x = χ₁.f x * χ₂.f x := rfl

@[simp] theorem inv_f {N N' : ℕ} (χ : HeckeU D N) (h) (x) : (inv N' χ h).f x = (χ.f x)⁻¹ := rfl

end GlobalTheory.HeckeUOps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyMapOfSum
section
open Matrix GlobalTheory.LeviHC
open Formalism.REAL (GlRel qdet)

noncomputable section

namespace GlobalTheory.LeviHC.MidThree

open GlobalTheory.LeviHC.MidBlock (stab mem_stab glComm comm_qdet)
open Polynomial

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem polyMap_of_sum {ι : Type} (s : Finset ι) (f : ι → ℂ[X]) (a : ι → A) (d : ℕ) (k₀ : ι) (hk₀ : k₀ ∈ s)
    (hm : (f k₀).Monic) (hd : (f k₀).natDegree = d) (hlt : ∀ k ∈ s, k ≠ k₀ → (f k).natDegree < d) :
    ∃ b : ℕ → A, b d = a k₀ ∧ ∀ u, ∑ k ∈ s, (f k).eval u • a k = ∑ i ∈ Finset.range (d + 1), u ^ i • b i := by
  refine ⟨fun i => ∑ k ∈ s, (f k).coeff i • a k, ?_, fun u => ?_⟩
  · show ∑ k ∈ s, (f k).coeff d • a k = a k₀
    rw [Finset.sum_eq_single_of_mem k₀ hk₀ fun k hk hne => by
      rw [coeff_eq_zero_of_natDegree_lt (hlt k hk hne), zero_smul]]
    rw [← hd, hm.coeff_natDegree, one_smul]
  · simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : (f k).natDegree < d + 1 := by
      by_cases h : k = k₀
      · rw [h, hd]; omega
      · have := hlt k hk h; omega
    rw [eval_eq_sum_range' hk', Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]

theorem monic_shift {p : ℂ → A} (t : ℂ)
    (hp : ∃ (d : ℕ) (a : ℕ → A), a d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) :
    ∃ (d : ℕ) (a : ℕ → A), a d = 1 ∧ ∀ u, p (u - t) = ∑ i ∈ Finset.range (d + 1), u ^ i • a i := by
  obtain ⟨d, a, ha, hp⟩ := hp
  have hdeg : ∀ i, ((X - C t) ^ i).natDegree = i := fun i => by
    rw [(monic_X_sub_C t).natDegree_pow, natDegree_X_sub_C, mul_one]
  obtain ⟨b, hb, e⟩ := polyMap_of_sum (Finset.range (d + 1)) (fun i => (X - C t) ^ i) a d d
    (Finset.self_mem_range_succ d) ((monic_X_sub_C t).pow d) (hdeg d) fun k hk hne => by
      rw [hdeg]; have := Finset.mem_range.1 hk; omega
  refine ⟨d, b, hb.trans ha, fun u => ?_⟩
  rw [hp, ← e]
  simp

end Alg

end GlobalTheory.LeviHC.MidThree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimRows3OfParts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory

theorem primRows3_of_parts : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → R.PPos → R.PrincipalLevelBijective F → R.PThmB → R.toRealDat.LUnif → (R.toCx3 F).MLat false → R.PThmA → (R.toCx3 F).GalD F.cr false → PrimRows3 R F := by
  intro hCusp hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLift hOk hC hEx hInert hGS hCD hME hR hL hHk hGU hGE hRT hLT hLTB hOnto hPos hPP hH2 hB hU hM hA hGal
  have hPP' : 0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0 := ⟨hPP.1, fun i t p => hPP.2 i t p _⟩
  exact
    { heckeR := hR
      heckeL := hL
      hecke := hHk
      gUnit := hGU
      gEquiv := hGE
      block := _root_.GlobalTheory.Hk3.inBlock_of_cuspRapidDecay hCusp R F hLift hOk hC hEx hGE
      rowTest := hRT
      liftTest := hLT
      liftTestB := hLTB
      liftOnto := hOnto
      pos := hPos
      posScal := hPP
      levE := _root_.GlobalTheory.LevelRowsPrincipal.pLevE_of hCusp hHowe R F hLift hOk hC hEx hInert hGE hPos hPP' hB hRT
      h2P := hH2
      thmB := hB
      sumE := _root_.GlobalTheory.RowsSum3.partsE hCusp hHowe R F hLift hOk hC hEx hInert hR hGE hPos hPP' hB
      unif := hU
      mLat := hM
      levW := _root_.GlobalTheory.LevW.levW_of_parts hCusp hHowe R F hLift hOk hC hEx hInert hGS hCD hME hGE hPos hPP' hA hLT hU
      thmA := hA
      sumW := _root_.GlobalTheory.SumW.partsW_base hCusp hHowe R F hLift hOk hC hEx hInert hGS hCD hME hR hGE hPos hPP' hB hU
      scalConj := hGal
      dimParts := _root_.GlobalTheory.DimPartsFull.dimParts hCusp R F hOk hC hEx hGS hCD hME hU }

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetLIntegralTsumUnfoldOfCosetRepresentatives
section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal Pointwise

namespace GlobalTheory.ResLine

theorem setLIntegral_tsum_unfold (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) (Γ Λ : Subgroup G) [Countable Γ] (T : Set Γ) (𝓕 D : Set G)
    (hμ : μ.IsHaarMeasure) (hle : Λ ≤ Γ)
    (hT : ∀ γ : Γ, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : Γ) : G) ∈ Λ)
    (hF : IsFundamentalDomain Γ 𝓕 μ) (hD : IsFundamentalDomain Λ D μ)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ γ ∈ Λ, ∀ g, f (γ * g) = f g) :
    ∫⁻ g in 𝓕, ∑' t : T, f (t.1.1 * g) ∂μ = ∫⁻ g in D, f g ∂μ := by
  haveI : Countable Λ := (Subgroup.inclusion_injective hle).countable
  let e0 : T × Λ → Γ := fun p => Subgroup.inclusion hle p.2 * p.1.1
  have hbij : Function.Bijective e0 := by
    constructor
    · rintro ⟨⟨t, ht⟩, l⟩ ⟨⟨s, hs⟩, m⟩ h
      simp only [e0] at h
      have hts : t = s := by
        refine (hT (Subgroup.inclusion hle l * t)).unique ⟨ht, ?_⟩ ⟨hs, ?_⟩
        · simp
        · rw [h]; simp
      subst hts
      have := Subgroup.inclusion_injective hle (mul_right_cancel h)
      subst this
      rfl
    · intro γ
      obtain ⟨t, ⟨ht, hm⟩, -⟩ := hT γ
      refine ⟨(⟨t, ht⟩, ⟨_, hm⟩), ?_⟩
      apply Subtype.ext
      simp [e0]
  have h1 : ∀ t : T, ∫⁻ g in 𝓕, f (t.1.1 * g) ∂μ
      = ∑' l : Λ, ∫⁻ g in D ∩ (e0 (t, l)) • 𝓕, f g ∂μ := by
    intro t
    have h2 : ∫⁻ g in 𝓕, f (t.1.1 * g) ∂μ = ∫⁻ g in t.1 • 𝓕, f g ∂μ :=
      (measurePreserving_smul t.1 μ).setLIntegral_comp_emb (measurableEmbedding_const_smul t.1) f 𝓕
    rw [h2, hD.setLIntegral_eq_tsum' f]
    refine tsum_congr fun l => ?_
    have h3 : l • t.1 • 𝓕 = (e0 (t, l)) • 𝓕 := by
      simp only [e0, mul_smul]
      rfl
    rw [h3, Set.inter_comm]
    refine lintegral_congr fun x => ?_
    exact hinv _ (l⁻¹).2 x
  rw [lintegral_tsum (f := fun (t : T) g => f (t.1.1 * g)) (fun t : T => (hf.comp (measurable_const_mul t.1.1)).aemeasurable),
    hF.setLIntegral_eq_tsum f D, ← (Equiv.ofBijective e0 hbij).tsum_eq, ENNReal.tsum_prod']
  exact tsum_congr h1

end GlobalTheory.ResLine
end

