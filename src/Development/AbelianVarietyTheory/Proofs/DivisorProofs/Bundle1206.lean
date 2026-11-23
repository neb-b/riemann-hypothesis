module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRegularConjugateLocalScalarNorm
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxRegLoc

theorem local_class_scalar_norm_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β →
    ∀ y₀ : grp G β, (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    ∃ S : Finset ℕ, ∀ (y : grp G β) (g : G.GAf), f (g⁻¹ * toAfF G β x t hx y * g) ≠ 0 →
    ∀ c : G.Cˣ, (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) ∧
      inC G ℚ_[ℓ] (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (β : G.C) *
        (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G L f hf β x t hx hβ y₀ hsep hdeg
  have hcomm : ∀ a b : G.C, Commute a (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) →
      Commute b (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) → Commute a b :=
    fun a b ha hb => GlobalTheory.LKCx.ClsReg.commute_of_commute_of_separable G _ hsep hdeg a b ha hb
  obtain ⟨Ω, hΩc, hΩ⟩ := GlobalTheory.T.exists_compact_support_twistedHeckeTestFunction p G L f hf
  have hev := eventually_compL_mem_intPts p G Ω hΩc
  have hlat := GlobalTheory.T.eventually_kottwitz_lattice_separable_minpoly p G (y₀ : G.Cˣ × ℚˣ).1 hsep hdeg
  have hnorm := GlobalTheory.T.eventually_tauFixed_unit_centralizer_is_norm p G β hβ (y₀ : G.Cˣ × ℚˣ).1 _ y₀.2.1 hsep hdeg
  have hstab := GlobalTheory.FinClsLoc.intC_stab p G β
  obtain ⟨S, hS⟩ := GlobalTheory.FinClsLoc.exists_finset_forall_prime_awayP_padic p _ (hev.and (hlat.and (hnorm.and hstab)))
  refine ⟨S, fun y g hfy c hc ℓ _ hℓ => ?_⟩
  obtain ⟨w, ⟨hev', hlat', hnorm', hmul, hstar, hβi, hβi'⟩, ⟨e⟩⟩ := hS ℓ hℓ
  apply GlobalTheory.T.localTwistedNormConclusion_transfer_ringEquiv p G (w.1.adicCompletion ℚ) ℚ_[ℓ] e
  have hint := hev' _ (hΩ _ hfy)
  obtain ⟨k, lam, hk1, hk2, hk3⟩ := GlobalTheory.T.exists_local_conj_trivialization_at_place_awayP p G β x t hx y g c (y₀ : G.Cˣ × ℚˣ).1 hc w
  obtain ⟨z, m, hz, hm, hm', hkzm⟩ := hlat' k (by rw [hk1]; exact hint.1) (by rw [hk2]; exact hint.2.1)
  have hap := GlobalTheory.grp_conj_unit_props p G β hβ y y₀ c hc (GlobalTheory.grp_factor_eq_of_conj p G β y y₀ c hc)
  have hinv := starT_invol G (w.1.adicCompletion ℚ)
  have hbb : inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) * inC G (w.1.adicCompletion ℚ) (β : G.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hβ' : (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (β : G.C))).unop = inC G (w.1.adicCompletion ℚ) (β : G.C) := by
    show (starT G.star (w.1.adicCompletion ℚ) ((1 : w.1.adicCompletion ℚ) ⊗ₜ (β : G.C))).unop = (1 : w.1.adicCompletion ℚ) ⊗ₜ (β : G.C)
    rw [starT_tmul]
    exact congrArg (TensorProduct.tmul ℚ (1 : w.1.adicCompletion ℚ)) hβ
  have hY' : inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * inC G (w.1.adicCompletion ℚ) (β : G.C) *
      (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))).unop =
      algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (algebraMap ℚ (w.1.adicCompletion ℚ) ((y₀ : G.Cˣ × ℚˣ).2 : ℚ)) * inC G (w.1.adicCompletion ℚ) (β : G.C) := by
    have h := congrArg (inC G (w.1.adicCompletion ℚ)) y₀.2.1
    rw [map_mul, map_mul, map_mul] at h
    have e1 : inC G (w.1.adicCompletion ℚ) (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) =
        (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))).unop :=
      (starT_tmul G.star (w.1.adicCompletion ℚ) 1 _).symm
    have e2 : inC G (w.1.adicCompletion ℚ) (algebraMap ℚ G.C ((y₀ : G.Cˣ × ℚˣ).2 : ℚ)) =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (algebraMap ℚ (w.1.adicCompletion ℚ) ((y₀ : G.Cˣ × ℚˣ).2 : ℚ)) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] w.1.adicCompletion ℚ ⊗[ℚ] G.C).commutes _
    rw [e1, e2] at h
    exact h
  have hN : ∀ m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = m * (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) →
      Commute (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) →
      inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) = m' →
      ∃ v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) ∧
        (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = v * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
    intro m' hm'v hcm hτ
    have hss : (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = 1 := by
      rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
    have h1 : (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop *
        ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) = 1 := by
      rw [hm'v]
      calc _ = (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * ((starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop *
            (inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) * inC G (w.1.adicCompletion ℚ) (β : G.C)) *
            (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop) * ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) := by
            simp only [mul_assoc]
        _ = 1 := by rw [hbb, mul_one, hss, mul_one, Units.mul_inv]
    have hinv' := Units.inv_eq_of_mul_eq_one_right h1
    refine hnorm' m' hcm ?_ ?_ hτ
    · rw [hm'v]; exact hmul _ _ (hmul _ _ hm (hstar _ hm)) hβi'
    · rw [hinv']; exact hmul _ _ (hmul _ _ hβi (hstar _ hm')) hm'
  have halg := GlobalTheory.twisted_norm_local_step (starT G.star (w.1.adicCompletion ℚ)) hinv
    (Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom β)
    (Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom (y₀ : G.Cˣ × ℚˣ).1) k z m
    (inC G (w.1.adicCompletion ℚ) (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)))
    lam (Units.map (algebraMap ℚ (w.1.adicCompletion ℚ)).toMonoidHom (y₀ : G.Cˣ × ℚˣ).2) hβ' hY'
    (hap.2.1.map (inC G (w.1.adicCompletion ℚ))) hk3 hkzm hz hN
  obtain ⟨z', hz', hz'eq⟩ := halg
  exact ⟨lam, z', hz', hz'eq⟩

end GlobalTheory.CxRegLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharCMEtaLocalEqNegOnePowValInert
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MuInert

theorem valuation_eq_uniformizer {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    {x : w.adicCompletion E} (hx : Valued.v x = WithZero.exp (-1 : ℤ)) :
    ValuativeRel.valuation (w.adicCompletion E) x = ValuativeRel.uniformizer (w.adicCompletion E) := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E)) Valued.v
  apply le_antisymm
  · rw [ValuativeRel.le_uniformizer_iff, he.lt_one_iff_lt_one, hx, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  · obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer (w.adicCompletion E))
    rw [← hy]
    have h1 : Valued.v y < 1 := by
      rw [← he.lt_one_iff_lt_one, hy]; exact ValuativeRel.uniformizer_lt_one
    rw [he.le_iff_le, hx]
    by_cases hy0 : Valued.v y = 0
    · rw [hy0]; exact zero_le'
    · rw [← WithZero.exp_log hy0] at h1 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      rw [WithZero.exp_le_exp]; omega

theorem valued_eq_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    {x : w.adicCompletion E} (hx : ValuativeRel.valuation (w.adicCompletion E) x = 1) : Valued.v x = 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E)) Valued.v).eq_one_iff_eq_one.1 hx

end GlobalTheory.MuInert

namespace GlobalTheory.MuInert

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteCompletionMap ideleMap)

theorem loc_eq_unrChar_neg_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ μ : HChar E,
    (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) →
    (∀ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ), ¬ IsSplitAt w → Valued.v (u : w.adicCompletion E) = 1 →
      μ.1 (Neutral.B1.localIdele E w u) = 1) →
    ∀ w : Pl E, ¬ IsSplitAt w → μ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (-1) := by
  intro E _ _ _ hU μ hres hunit w hw
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hns : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E))) := by
    intro hs
    obtain ⟨a, b, hab, ha, hb⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    apply hw
    rcases eq_or_ne a w with rfl | haw
    · exact ⟨b, hab.symm, hb⟩
    · exact ⟨a, haw, ha⟩
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 (maximalRealSubfield E))) := by
    refine GlobalTheory.LFun.isUnram_iff.2 fun u hu => ?_
    obtain rfl := GlobalTheory.LFun.eq_of_not_isSplit hns hu rfl
    haveI := u.isPrime
    exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.1 (hU u)
  have he : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := GlobalTheory.LFun.isUnram_iff.1 hun w rfl
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.exists_isUniformiser (w.under (𝓞 (maximalRealSubfield E)))
  set ϖE : (w.adicCompletion E)ˣ := Units.map (finiteCompletionMap (maximalRealSubfield E) E w).toMonoidHom ϖ with hϖE
  have hvE : Valued.v (ϖE : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (finiteCompletionMap (maximalRealSubfield E) E w ϖ) = _
    rw [← GlobalTheory.CharTransport.locMap_eq, ← GlobalTheory.LFun.complMap_rfl, GlobalTheory.LFun.valued_complMap rfl ϖ.ne_zero, he, pow_one]
    exact hϖ
  have hid : ideleMap (maximalRealSubfield E) E (Neutral.B1.localIdele _ (w.under (𝓞 (maximalRealSubfield E))) ϖ) =
      Neutral.B1.localIdele E w ϖE := by
    refine Units.ext (Prod.ext ?_ (FiniteAdeleRing.ext _ fun u => ?_))
    · exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap (maximalRealSubfield E) E)
    · rw [GlobalTheory.ArtinTransfer.ideleMap_apply]
      by_cases hu : u = w
      · subst hu
        rw [GlobalTheory.ArtinTransfer.loc_same, GlobalTheory.ArtinTransfer.loc_same]
        rfl
      · have hu' : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) :=
          fun e => hu (GlobalTheory.LFun.eq_of_not_isSplit hns e rfl)
        rw [GlobalTheory.ArtinTransfer.loc_ne hu', GlobalTheory.ArtinTransfer.loc_ne hu, map_one]
  have hq : (GlobalTheory.GalOfCusp.quadChar E).1 (Neutral.B1.localIdele _ (w.under (𝓞 (maximalRealSubfield E))) ϖ) = -1 := by
    change Units.map _ (GlobalTheory.IdeleNormChar.normSign E (Neutral.B1.localIdele _ _ ϖ)) = -1
    rw [GlobalTheory.LFun.normSign_localIdele]
    have hne := fun h => GlobalTheory.LFun.not_mem_normGroup_of_inert h2 hns hun hϖ (GlobalTheory.QuadSymbol.eta_eq_one_iff.1 h)
    rcases Int.units_eq_one_or (GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E _ ϖ) with h | h
    · exact absurd h hne
    · rw [h]; ext; simp
  have hval : μ.loc w ϖE = -1 := by
    change μ.1 (Neutral.B1.localIdele E w ϖE) = -1
    rw [← hid, hres, hq]
  have hunr : GlobalTheory.SplitWeil.IsUnram (μ.loc w) := fun x hx => hunit w x hw (valued_eq_one w hx)
  rw [GlobalTheory.SmGL.eq_unrChar hunr (valuation_eq_uniformizer w hvE), hval]

end GlobalTheory.MuInert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterPrescribedCentre
section
open NumberField

namespace GlobalTheory.SplitCentreChar

theorem exists_hChar_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (d : ℕ), 0 < d →
    ∀ s : ℂ, ∃ χ : Formalism.L2.Host.HChar E, ∀ t : ℝ,
      ((GlobalTheory.CuspRep.chiDet d χ (GlobalTheory.UnitaryBC.splitCentre E d t) : ℂˣ) : ℂ) = Complex.exp (-(t * s)) := by
  intro E _ _ _ d hd s
  obtain ⟨χ, hχ⟩ := GlobalTheory.CuspQuot.exists_chiDet_splitCentre (E := E) hd (-s)
  exact ⟨χ, fun t => by rw [hχ t]; congr 1; ring⟩

end GlobalTheory.SplitCentreChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatVacSign

variable {D : D7} {S T : HSp D}

theorem cA_incA' (w : D.host.E) : cA D (incA D w) = incA D (star w) := rfl

theorem hO_smul_smul (c c' : AE D) (x y : WO S T) :
    hO S T (c • x) (c' • y) = c * cA D c' * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

theorem symplO_smul_smul (w w' : D.host.E) (x y : WO S T) :
    symplO S T (incA D w • x) (incA D w' • y) =
      Algebra.trace (AF D.host.F) (AE D) (incA D (D.host.xi0 * (w * star w')) * hO S T x y) := by
  rw [symplO, hO_smul_smul, cA_incA', map_mul (incA D), map_mul (incA D)]
  congr 1
  ring

theorem symplOH_smul_norm {w : D.host.E} {n : ℤ} (hw : w * star w = 2 * n) (x y : WO S T) :
    symplOH S T (incA D w • x) (incA D w • y) = (n : AF D.host.F) * symplO S T x y := by
  have e : incA D (D.host.xi0 * (w * star w)) * hO S T x y =
      ((2 * n : ℤ) : AE D) * (incA D D.host.xi0 * hO S T x y) := by
    rw [hw]
    simp only [map_mul, map_intCast, map_ofNat]
    push_cast
    ring
  rw [symplOH, symplO_smul_smul, e, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, ← symplO]
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  push_cast
  linear_combination ((n : AF D.host.F) * symplO S T x y) * h2

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem char_symplOH_smul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) {w : D.host.E} {n : ℤ} (hw : w * star w = 2 * n) {x y : WO S T}
    (hx : x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (hy : y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    ψ (symplOH S T (incA D w • x) (incA D w • y)) = 1 := by
  rw [symplOH_smul_norm hw, ← zsmul_eq_mul, AddChar.map_zsmul_eq_zpow,
    GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hx hy, _root_.one_zpow]

theorem incA_smul_finTens {m k : ℕ} (w : D.host.E) (α : Af D.host.F) (M : Matrix (Fin m) (Fin k) D.host.E) :
    incA D w • GlobalTheory.LatVac.finTens α M = GlobalTheory.LatVac.finTens α (w • M) := by
  ext i j
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] w : AE D) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] M i j) =
    pairA D.host.F 0 α ⊗ₜ[D.host.F] (w * M i j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem smul_mem_latO' {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} (w : 𝓞 D.host.E)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    incA D (w : D.host.E) • u ∈ latO S T LS LT fun _ => True := by
  refine GlobalTheory.LatVac.latO_induction (p := fun u => incA D (w : D.host.E) • u ∈ latO S T LS LT fun _ => True)
    ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    rw [incA_smul_finTens]
    exact GlobalTheory.LatVac.finTens_mem_latO hα (GlobalTheory.LatVac.smul_mem_latRat w hM)
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

def fixGroup (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (c : AE D)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplOH S T (c • x) (c • y)) = 1) : AddSubgroup (WO S T) where
  carrier := {u | u ∈ Λ ∧ ∀ f, IsLatVac (heisO ψ S T) Λ f → heisO ψ S T (c • u) f = f}
  zero_mem' := ⟨zero_mem _, fun f _ => by rw [smul_zero, GlobalTheory.LatVac.heisO_zero]⟩
  add_mem' := by
    rintro a b ⟨ha, fa⟩ ⟨hb, fb⟩
    refine ⟨add_mem ha hb, fun f hf => ?_⟩
    have h1 := GlobalTheory.LatVac.heisO_heisO ψ (c • a) (c • b) f
    rw [fb f hf, fa f hf, hΛ a ha b hb, one_smul, ← smul_add] at h1
    exact h1.symm
  neg_mem' := by
    rintro a ⟨ha, fa⟩
    refine ⟨neg_mem ha, fun f hf => ?_⟩
    have h1 := GlobalTheory.LatVac.heisO_heisO ψ (c • -a) (c • a) f
    rw [fa f hf, hΛ (-a) (neg_mem ha) a ha, one_smul, ← smul_add, neg_add_cancel,
      smul_zero, GlobalTheory.LatVac.heisO_zero] at h1
    exact h1

theorem mem_fixGroup {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {c : AE D}
    {hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplOH S T (c • x) (c • y)) = 1} {u : WO S T} :
    u ∈ fixGroup ψ Λ c hΛ ↔ u ∈ Λ ∧ ∀ f, IsLatVac (heisO ψ S T) Λ f → heisO ψ S T (c • u) f = f := Iff.rfl

theorem heisO_smul_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) (w : 𝓞 D.host.E) {n : ℤ} (hw : (w : D.host.E) * star (w : D.host.E) = 2 * n)
    {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (f : WO S T → ℂ)
    (hf : IsLatVac (heisO ψ S T)
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f) :
    heisO ψ S T (incA D (w : D.host.E) • u) f = f := by
  have hΛ : ∀ x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∀ y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ψ (symplOH S T (incA D (w : D.host.E) • x) (incA D (w : D.host.E) • y)) = 1 :=
    fun x hx y hy => char_symplOH_smul hψ hS hT hw hx hy
  have h2 : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      2 • u ∈ fixGroup ψ _ _ hΛ := by
    intro u hu
    refine mem_fixGroup.2 ⟨nsmul_mem hu 2, fun f hf => ?_⟩
    have e : incA D (w : D.host.E) • (2 • u) = 2 • (incA D (w : D.host.E) • u) := by
      rw [two_nsmul, two_nsmul, smul_add]
    rw [e]
    exact hf.1 _ (smul_mem_latO' w hu)
  have hh : ∀ e, IsSplitIdem D e →
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf e u → u ∈ fixGroup ψ _ _ hΛ := by
    intro e he u hu hh
    refine mem_fixGroup.2 ⟨hu, fun f hf => hf.2 e he _ (smul_mem_latO' w hu) fun i j => ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hh i j]
  exact (mem_fixGroup.1 (GlobalTheory.LatVac.le_of_two_of_half _ h2 hh hu)).2 f hf

theorem hRat_smul_smul (a b : D.host.E) (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T (a • M) (b • N) = a * star b * GlobalTheory.LatVac.hRat S T M N := by
  simp only [GlobalTheory.LatVac.hRat, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul, star_mul']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

theorem finRat_eq (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.VacUnique.finRat S T M = GlobalTheory.LatVac.finTens 1 M := by
  ext i j; rfl

theorem algebraMap_mul_pair (c : D.host.F) (β : Af D.host.F) :
    algebraMap D.host.F (AF D.host.F) c * pairA D.host.F 0 β =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) c * β) :=
  Prod.ext (mul_zero _) rfl

end GlobalTheory.LatVacSign


open GlobalTheory.LatVacSign in
theorem GlobalTheory.LatVacSign.heisO_finRat_sign : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → ∀ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T (-v) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃ k : ℤ, (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T v v) ∧ heisO ψ S T (GlobalTheory.VacUnique.finRat S T (-v)) f = ((-1 : ℂ) ^ k) • f := by
  intro D ψ S T ΛS ΛT hψ hS hT f hf v hv
  have hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have hst : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    have := D.host.isCMField_hostE
    have h2 : D.host.φ₀ (star D.host.sqrtMinusD) = starRingEnd ℂ (D.host.φ₀ D.host.sqrtMinusD) :=
      NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ D.host.sqrtMinusD
    rw [h2, map_neg, h1]
    simp
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (D.host.d : ℤ) + 1 = 8 * n :=
    ⟨((D.host.d : ℤ) + 1) / 8, by have := D.host.hyp.2.2.2.1; omega⟩
  have hnE : (D.host.d : D.host.E) = 8 * n - 1 := by
    have := congrArg (Int.cast (R := D.host.E)) hn
    push_cast at this
    linear_combination this
  set w₀ : D.host.E := (1 + D.host.sqrtMinusD) / 2 with hw₀
  have hstw : star w₀ = 1 - w₀ := by
    rw [hw₀, star_div₀, star_add, star_one, hst, star_ofNat]
    ring
  have hnorm : w₀ * (1 - w₀) = 2 * n := by
    rw [hw₀]
    linear_combination (-1 / 4 : D.host.E) * hsq + (1 / 4 : D.host.E) * hnE
  have hint : IsIntegral ℤ w₀ := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (2 * n), by monicity!, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, eq_intCast]
    push_cast
    linear_combination (-1 : D.host.E) * hnorm
  let W : 𝓞 D.host.E := ⟨w₀, hint⟩
  let W' : 𝓞 D.host.E := 1 - W
  have hW : (W : D.host.E) = w₀ := rfl
  have hW' : (W' : D.host.E) = 1 - w₀ := by
    change algebraMap (𝓞 D.host.E) D.host.E (1 - W) = 1 - w₀
    rw [map_sub, map_one]
    rfl
  have nW : (W : D.host.E) * star (W : D.host.E) = 2 * n := by rw [hW, hstw, hnorm]
  have nW' : (W' : D.host.E) * star (W' : D.host.E) = 2 * n := by
    rw [hW', star_sub, star_one, hstw, sub_sub_cancel, mul_comm, hnorm]
  set u := GlobalTheory.VacUnique.finRat S T (-v) with hu_def
  have h1 := heisO_smul_fix hψ hS hT W nW hv f hf
  have h2 := heisO_smul_fix hψ hS hT W' nW' hv f hf
  have hsum : incA D (W : D.host.E) • u + incA D (W' : D.host.E) • u = u := by
    rw [← add_smul, ← map_add (f := _), hW, hW', add_sub_cancel, map_one, one_smul]
  have key := GlobalTheory.LatVac.heisO_heisO ψ (incA D (W : D.host.E) • u) (incA D (W' : D.host.E) • u) f
  rw [h2, h1, hsum] at key

  set z : D.host.E := D.host.xi0 * w₀ ^ 2 * GlobalTheory.LatVac.hRat S T v v with hz
  have hpair : symplO S T (incA D (W : D.host.E) • u) (incA D (W' : D.host.E) • u) =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (Algebra.trace D.host.F D.host.E z)) := by
    rw [hu_def, finRat_eq, incA_smul_finTens, incA_smul_finTens, GlobalTheory.LatVac.symplO_finTens, one_mul, one_mul]
    congr 3
    rw [hz, ← neg_one_smul D.host.E v, smul_smul, smul_smul, hRat_smul_smul, hW, hW', star_mul', star_sub,
      star_one, hstw, star_neg, star_one]
    ring
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Algebra.trace ℚ D.host.E z = k := by
    have := GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT (smul_mem_latO' W hv) (smul_mem_latO' W' hv)
    rw [hpair] at this
    exact (GlobalTheory.LatVac.char_rat hψ z).1 this
  have hsign : ψ (symplOH S T (incA D (W : D.host.E) • u) (incA D (W' : D.host.E) • u)) = (-1 : ℂ) ^ k := by
    rw [symplOH, hpair, algebraMap_mul_pair, ← map_mul, _root_.GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ]
    have e : Algebra.trace ℚ D.host.F (1 / 2 * Algebra.trace D.host.F D.host.E z) = (1 / 2 : ℚ) * k := by
      have h12 : (1 / 2 : D.host.F) = algebraMap ℚ D.host.F (1 / 2) := by simp
      rw [h12, ← Algebra.smul_def, map_smul, Algebra.trace_trace, hk, smul_eq_mul]
    rw [e, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  rw [hsign] at key
  refine ⟨k, hk.symm, ?_⟩
  have hsq1 : ((-1 : ℂ) ^ k) * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_zpow]; norm_num
  calc heisO ψ S T u f = (((-1 : ℂ) ^ k) * (-1 : ℂ) ^ k) • heisO ψ S T u f := by rw [hsq1, one_smul]
    _ = (-1 : ℂ) ^ k • f := by rw [mul_smul, ← key]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSupportHermitianDecompositionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_support_hermitian_decomposition : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (S : Finset ℕ), (∀ q ∈ S, q.Prime) →
    ∀ x : GA D V, x ∈ GfC V →
    ∃ (γ : GL (Fin V.rank) D.host.E) (h k : GA D V),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram ∧ h ∈ GfC V ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V h ∧ ∀ w ∈ P, Off S w) ∧
      k ∈ GfC V ∧ (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) ∧
      (Formalism.IndefR.Lev.finE V x).1 = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 * (Formalism.IndefR.Lev.finE V k).1 := by
  first | exact @GlobalTheory.FunObj.StdReps.exists_rep_std | exact GlobalTheory.FunObj.StdReps.exists_rep_std | (intros; apply GlobalTheory.FunObj.StdReps.exists_rep_std <;> assumption)
end

