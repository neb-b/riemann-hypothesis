module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMatrixOfOrthonormalLocalBasisAllPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0173
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0174
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.B0StandardSeriesAdmissible
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem nP_eq_one_of_hP_eq_zero (D : D7) (p : ℕ) (hC : IsResidueClassZero D p) (h0 : hP D p = 0) : nP D p = 1 := by
  have hS : ¬ IsSg D p := by
    intro hs
    unfold IsResidueClassZero at hC
    unfold IsSg at hs
    rw [hC] at hs
    exact absurd hs (by decide)
  unfold nP
  rw [if_neg hS, h0, addOrderOf_zero]

theorem thetaExpansionRealPlaces_stdSer_of_adm : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → 5 ≤ p → IsResidueClassZero D p → hP D p = 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → OrbitPlaces.ThetaExpansionRealPlaces D p (stdSer D lam (fun _ => 1) P P' G) := by
  intro D cc δ B χ p _ lam hHost h5 hC hP0 N N' L L' P P' hAdm hS hS' G hG
  obtain ⟨c, g2, g3, s2, ε, σ, F, hc, hcd, hfam⟩ := hHost
  obtain ⟨r, b, hLB, hON, hInt⟩ := hfam N N' L L' hAdm
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := _root_.GlobalTheory.KerStd.unitary_of_orthonormal D p lam σ hcd.2.2.2.2.2.1 h5 hC hP0 N N' L L' P P' hAdm hS hS' r b hLB hON
  have hU := _root_.GlobalTheory.KerStd.HostLog.subst_unitary p g2 g3 s2 ε σ F hcd (Fin r) (OrbitPlaces.Pl D × Fin N × Fin N') γ hγ1 (by convert hγ2) _ (hInt G hG)
  rw [← hγ3 c G] at hU
  exact _root_.GlobalTheory.KerStd.expShape_of_integralClass D p g2 g3 s2 ε σ F hcd (nP_eq_one_of_hP_eq_zero D p hC hP0) N N' c _ hc hU

end GlobalTheory.KerStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicCharacterUnitary
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

namespace GlobalTheory.LadicInf

theorem exists_place (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (τ : E →+* Qbar l) :
    ∃ (u : HeightOneSpectrum (𝓞 E)) (j : u.adicCompletion E →+* Qbar l),
      ((l : ℕ) : 𝓞 E) ∈ u.asIdeal ∧ Continuous j ∧ j.comp (algebraMap E (u.adicCompletion E)) = τ := by
  obtain ⟨u, hu⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l τ
  obtain ⟨j, hj, hjE⟩ := GlobalTheory.exists_continuous_extension_adicCompletion E l τ u hu
  refine ⟨u, j, ?_, hj, hjE⟩
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
  have h1 : ‖τ ((((l : ℕ) : 𝓞 E)) : E)‖ < 1 := by
    have : τ ((((l : ℕ) : 𝓞 E)) : E) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this]
    have := PadicAlgCl.norm_extends (p := l) (l : ℚ_[l])
    rw [this]
    first | exact Padic.norm_p_lt_one | exact padicNormE.norm_p_lt_one
  have := (hu (((l : ℕ) : 𝓞 E) : E)).2 h1
  simpa using this

end GlobalTheory.LadicInf

namespace GlobalTheory.LadicInf

end GlobalTheory.LadicInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicFormWeightLevelSmoothAtPlace
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.Cong

theorem exists_continuous_inv_cLoc {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (w₀ : HeightOneSpectrum (𝓞 E)) :
    ∃ ι : GL (Fin n) (w₀.adicCompletion E) → GA E n, Continuous ι ∧ ι 1 = 1 ∧
      ∀ x : UA E n, x ∈ locU n w₀ → ι (cLoc w₀ x) = x.1 := by
  by_cases hsp : IsSplitAt w₀
  · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w₀ hsp
    refine ⟨fun h => ((e.symm h : locU n w₀) : UA E n).1,
      continuous_subtype_val.comp (continuous_subtype_val.comp e.symm.continuous), by simp, fun x hx => ?_⟩
    have h1 : e.symm (cLoc w₀ x) = ⟨x, hx⟩ := by
      rw [← he ⟨x, hx⟩]
      exact e.symm_apply_apply _
    simp only [h1]
  · have hc0 : GlobalTheory.CuspRep.conjSrc (IsCMField.complexConj E).toRingEquiv w₀ = w₀ := by
      by_contra hne
      exact hsp ⟨_, hne, GlobalTheory.DefU.LocRet.under_conjSrc w₀⟩
    have hw : GlobalTheory.Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv w₀ w₀ := by
      have h := GlobalTheory.SplitPts.conjPl_self_conjSrc (E := E) w₀
      change GlobalTheory.Mem.Chr.ConjPl _ w₀ (GlobalTheory.CuspRep.conjSrc (IsCMField.complexConj E).toRingEquiv w₀) at h
      rwa [hc0] at h
    refine ⟨fun h => finGL E n (locGL E n w₀ h),
      GlobalTheory.DefU.Inert.continuous_finGL.comp (GlobalTheory.CuspRep.CuspSub.continuous_locGL w₀), by simp,
      fun x hx => GlobalTheory.DefU.Inert.finGL_cLoc hw ⟨x, hx⟩⟩

theorem exists_algForm_ofType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : (E →+* ℂ) → DomWeight n) (K : Subgroup (UA E n)) (U : Submodule ℂ (UA E n → ℂ)), K ≤ finU (E := E) (n := n) → OfType lam K U → ∀ w₀ : HeightOneSpectrum (𝓞 E), ∃ (W : Wt E n) (f : algForms W), (∀ τ, W.at τ = lam τ) ∧ f ≠ 0 ∧ (∀ v, f.1 v ∈ U) ∧ (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) ∧ ∃ N ∈ nhds (1 : GL (Fin n) (w₀.adicCompletion E)), ∀ x ∈ locU n w₀, cLoc w₀ x ∈ N → ∀ v g, f.1 v (g * x) = f.1 v g := by
  intro E _ _ _ n lam K U hK hU w₀
  classical
  let π : AutSub E n := ⟨U, hU.aut⟩
  set W := (AU.mk π).wt with hWdef
  have hWat : ∀ τ, W.at τ = lam τ := fun τ => by
    have h1 : (AU.mk π).HasWt τ (lam τ) := (AU.hasWt_mk π τ (lam τ)).2 (hU.wt τ)
    exact hasWeightAt_unique π τ ((AU.hasWt_mk π τ _).1 h1.wt) (hU.wt τ)
  let M := π.finPart W
  have hM0 : M ≠ ⊥ := AutSub.finPart_wt_ne_bot E n π
  have hV : π.V = Pairs.img (Pairs.jOf W M) := Pairs.V_eq_img π (Pairs.finPart_stable π W) hM0 le_rfl
  obtain ⟨φ, hφU, hφ0, hφK⟩ := hU.fix
  haveI : Nontrivial W.Sp := (Pairs.nontrivial_of_ne_bot hM0).1
  let b := Module.finBasis ℂ W.Sp
  obtain ⟨c, hc⟩ : φ ∈ LinearMap.range (Pairs.total b (Pairs.jOf W M)) := by
    rw [Pairs.range_total, ← hV]
    exact hφU
  let Fx : Submodule ℂ (UA E n → ℂ) :=
    { carrier := {ψ | ∀ k ∈ K, RU E n k ψ = ψ}
      add_mem' := fun {x y} hx hy k hk => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_add (f := _), hx k hk, hy k hk]
      zero_mem' := fun k _ => map_zero _
      smul_mem' := fun r ψ h k hk => by
        simp only [Set.mem_setOf_eq] at h ⊢
        rw [map_smul, h k hk] }
  have hFx : ∀ x : infU E n, ∀ u ∈ Fx, RU E n x.1 u ∈ Fx := fun x u hu k hk => by
    change RU E n k (RU E n x.1 u) = RU E n x.1 u
    rw [RU_RU, fin_mul_inf (hK hk) x.2, ← RU_RU, hu k hk]
  have hcF : ∀ a v, Pairs.jOf W M (c a) v ∈ Fx := Pairs.coeff_mem (Pairs.span_rep W) (R := fun x => RU E n x.1)
    (Pairs.jOf_rep W M) hFx b (by rw [hc]; exact hφK)
  obtain ⟨a, ha⟩ : ∃ a, c a ≠ 0 := by
    by_contra h
    push_neg at h
    apply hφ0
    rw [← hc, Pairs.total_apply]
    simp [h]
  have hS : IsOpen {k : finU (E := E) (n := n) | algRep W k (c a).1 = (c a).1} := isSmooth_algRep W (c a).1
  obtain ⟨ι, hι, hι1, hιx⟩ := exists_continuous_inv_cLoc n w₀
  have hS1 : {k : finU (E := E) (n := n) | algRep W k (c a).1 = (c a).1} ∈ nhds (1 : finU (E := E) (n := n)) :=
    hS.mem_nhds (by
      show algRep W 1 (c a).1 = (c a).1
      rw [map_one]
      rfl)
  rw [nhds_subtype, Filter.mem_comap] at hS1
  obtain ⟨T1, hT1, hT1S⟩ := hS1
  rw [nhds_subtype, Filter.mem_comap] at hT1
  obtain ⟨T, hT, hTT1⟩ := hT1
  refine ⟨W, (c a).1, hWat, fun h => ha (Subtype.ext h), fun v => AutSub.mem_finPart.1 (c a).2 v,
    fun k hk v g => congrFun (hcF a v k hk) g, ι ⁻¹' T, hι.continuousAt.preimage_mem_nhds (by rw [hι1]; exact hT),
    fun x hx hxN v g => ?_⟩
  have hxfin : x ∈ finU (E := E) (n := n) := (Subgroup.mem_inf.1 hx).1
  have h2 : x.1 ∈ T := hιx x hx ▸ hxN
  have hk : (⟨x, hxfin⟩ : finU (E := E) (n := n)) ∈ {k : finU (E := E) (n := n) | algRep W k (c a).1 = (c a).1} := hT1S (hTT1 h2)
  exact congrFun (LinearMap.congr_fun (congrArg Subtype.val hk) v) g

end GlobalTheory.Cong

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicModularFormMulArchInvariant
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
open GlobalTheory.DefU

namespace GlobalTheory.AlgMul

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem RU_mul (x : UA E n) (a b : UA E n → ℂ) : RU E n x (a * b) = RU E n x a * RU E n x b := rfl

theorem isOpen_fix_of {ψ : UA E n → ℂ} (U : Set (finU (E := E) (n := n))) (hU : IsOpen U) (h1 : (1 : finU (E := E) (n := n)) ∈ U)
    (hs : ∀ k ∈ U, RU E n k ψ = ψ) : IsOpen {k : finU (E := E) (n := n) | RU E n k ψ = ψ} := by
  let St : Subgroup (finU (E := E) (n := n)) :=
    { carrier := {k | RU E n k ψ = ψ}
      mul_mem' := fun {a b} ha hb => by
        change RU E n ((a : UA E n) * b) ψ = ψ
        rw [← RU_RU]
        change RU E n a (RU E n b ψ) = ψ
        rw [hb]; exact ha
      one_mem' := by
        change RU E n ((1 : finU (E := E) (n := n)) : UA E n) ψ = ψ
        simp
      inv_mem' := fun {a} ha => by
        change RU E n ((a : UA E n)⁻¹) ψ = ψ
        conv_lhs => rw [← (show RU E n (a : UA E n) ψ = ψ from ha)]
        rw [RU_RU, inv_mul_cancel, map_one, Module.End.one_apply] }
  have : (St : Set (finU (E := E) (n := n))) ∈ nhds (1 : finU (E := E) (n := n)) :=
    Filter.mem_of_superset (hU.mem_nhds h1) hs
  exact Subgroup.isOpen_of_mem_nhds St this

theorem isAutFormU_mul {e φ : UA E n → ℂ} (he : IsAutFormU e) (hinv : ∀ g, ∀ x ∈ infU E n, e (g * x) = e g)
    (hφ : IsAutFormU φ) : IsAutFormU (e * φ) := by
  refine ⟨he.cont.mul hφ.cont, fun γ hγ g => ?_, ?_, ?_⟩
  · simp only [Pi.mul_apply, he.left γ hγ g, hφ.left γ hγ g]
  · refine isOpen_fix_of _ (he.level.inter hφ.level) ⟨by simp, by simp⟩ ?_
    rintro k ⟨hk1, hk2⟩
    rw [RU_mul, show RU E n k e = e from hk1, show RU E n k φ = φ from hk2]
  · have := hφ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)).map (LinearMap.mulLeft ℂ e))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨RU E n k φ, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
    show e * RU E n k φ = RU E n k (e * φ)
    rw [RU_mul]
    congr 1
    funext g
    exact (hinv g k k.2).symm

end GlobalTheory.AlgMul

theorem GlobalTheory.AlgMul.exists_mul_algForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (f : algForms W) (e : UA E n → ℂ), IsAutFormU e → (∀ g, ∀ x ∈ infU E n, e (g * x) = e g) → ∃ f' : algForms W, ∀ v g, f'.1 v g = e g * f.1 v g := by
  intro E _ _ _ n W f e he hinv
  have hmem : (LinearMap.mulLeft ℂ e).comp f.1 ∈ algForms W := by
    refine ⟨fun v => GlobalTheory.AlgMul.isAutFormU_mul he hinv (f.2.1 v), fun x v => ?_⟩
    change e * f.1 (W.rep x v) = RU E n x (e * f.1 v)
    rw [f.2.2 x v, GlobalTheory.AlgMul.RU_mul]
    congr 1
    funext g
    exact (hinv g x x.2).symm
  exact ⟨⟨_, hmem⟩, fun v g => rfl⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsConjugateModelExtremalDualParameter
section
noncomputable section

namespace GlobalTheory.Hk3.HoweG

theorem gramClass_orbit_mod_lower : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, s ≠ 0 → GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ v ∈ Submodule.span ℂ (Set.range fun g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s),
      ∃ u ∈ Submodule.span ℂ {v : M | ∃ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweDuality.latIdx y < GlobalTheory.Hk3.HoweDuality.latIdx x ∧ v = ρ y s},
        v - u ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} ∧ v - u ≠ 0 := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hs hvac hspan x hx
  classical
  obtain ⟨C, c, hxC, hC, hpw, hsum⟩ := _root_.GlobalTheory.Hk3.HoweG.gramClass_sum_mem_span_selfDual_vac L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac x hx
  have hψ0 : ∀ e : L, ψ e ≠ 0 := fun e h => by
    have h2 : ψ e * ψ (-e) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [h, zero_mul] at h2; exact zero_ne_one h2
  have hint_mul : ∀ (u : Matrix (Fin n') (Fin n) L) (k : GL (Fin n) L), (∀ i j, u i j ∈ Formalism.UG.intL L) →
      k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ∀ i j, (u * (k : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L := by
    intro u k hu hk i j
    obtain ⟨k0, rfl⟩ := hk
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hu i l) ((k0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) l j).2

  have hvacSS : Submodule.span ℂ {w : M | ∃ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
        ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w} ≤
      Submodule.span ℂ (Set.range fun g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s) := by
    rw [Submodule.span_le]
    rintro w ⟨a, ha, hw⟩
    obtain ⟨g, k, hk, hak⟩ := _root_.GlobalTheory.Hk3.HoweG.selfDual_eq_unitary_mul_int L ϖ σ q n JS hP.unr hP.odd hP.intS hP.hermS a ha
    have hw' : GlobalTheory.Hk3.LocVac ρ (ω (g⁻¹, 1) w) := by
      intro u hu
      have h1 := hP.norm g⁻¹ 1 (u * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
      have h2 : ρ (u * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w := by
        have := hw (u * (k : Matrix (Fin n) (Fin n) L)) (hint_mul u k hu hk)
        rw [hak] at this
        simpa [Matrix.mul_assoc, mul_inv_rev] using this
      have h3 := congrArg (fun F : Module.End ℂ M => F w) h1
      simp only [Module.End.mul_apply, h2] at h3
      have e : (((1 : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L)) : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *
          (u * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
          ((((g⁻¹ : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L)) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = u := by
        rw [Subgroup.coe_inv, inv_inv, OneMemClass.coe_one, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, Matrix.mul_one]
      rw [e] at h3
      exact h3.symm
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 (_root_.GlobalTheory.Hk3.locVac_mem_span_vac L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac hspan _ hw')
    have hww : w = t • ω (g, 1) s := by
      have e1 : ω (g, 1) (ω (g⁻¹, 1) w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one, Prod.mk_one_one, map_one,
          Module.End.one_apply]
      rw [← e1, ← ht, map_smul]
    rw [SetLike.mem_coe, hww]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  refine ⟨∑ y ∈ C, c y • ρ y s, hvacSS hsum,
    ∑ y ∈ C.filter (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y ≠ GlobalTheory.Hk3.HoweDuality.latIdx x), c y • ρ y s, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun y hy => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, ?_, rfl⟩)
    obtain ⟨hyC, hne⟩ := Finset.mem_filter.1 hy
    exact lt_of_le_of_ne (_root_.GlobalTheory.Hk3.HoweDuality.latIdx_le_of_ker L ϖ σ q n' n x y hP.unr (hC y hyC).2.1.1) hne
  have hsplit : ∑ y ∈ C, c y • ρ y s - ∑ y ∈ C.filter (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y ≠ GlobalTheory.Hk3.HoweDuality.latIdx x), c y • ρ y s =
      ∑ y ∈ C.filter (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x), c y • ρ y s := by
    rw [← Finset.sum_filter_add_sum_filter_not C (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x)]
    exact add_sub_cancel_right _ _
  rw [hsplit]

  have hshift : ∀ y y' : Matrix (Fin n') (Fin n) L, (∀ i j, (y - y') i j ∈ Formalism.UG.intL L) → ∃ ζ : ℂ, ζ ≠ 0 ∧ ρ y' s = ζ • ρ y s := by
    intro y y' hl
    refine ⟨ψ ((GlobalTheory.Hk3.locH σ δ JS JT y' (y - y') + σ (GlobalTheory.Hk3.locH σ δ JS JT y' (y - y'))) / 2), hψ0 _, ?_⟩
    have h1 := congrArg (fun F : Module.End ℂ M => F s) (hP.rho_mul y' (y - y'))
    simp only [Module.End.mul_apply, hvac _ hl, LinearMap.smul_apply, add_sub_cancel] at h1
    exact h1
  refine ⟨Submodule.sum_mem _ fun y hy => ?_, ?_⟩
  · obtain ⟨hyC, heq⟩ := Finset.mem_filter.1 hy
    obtain ⟨h, hh, hyl⟩ := _root_.GlobalTheory.Hk3.HoweG.exists_intUnitary_of_gramClass L ϖ σ q n n' JS JT hP.unr hP.odd hP.intS hP.intT hP.hermS hP.hermT x y hx (hC y hyC).2.1 (hC y hyC).2.2 heq
    obtain ⟨ζ, hζ, hζe⟩ := hshift y (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) hyl
    have : ρ y s = ζ⁻¹ • ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s := by
      rw [hζe, smul_smul, inv_mul_cancel₀ hζ, one_smul]
    rw [this, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, hh, rfl⟩)
  ·
    have hI := GlobalTheory.Hk3.locVac_span_classes_indep L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac
    set P := C.filter (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x) with hPdef
    have hxP : x ∈ P := Finset.mem_filter.2 ⟨hxC, rfl⟩
    set F := fun cl : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n =>
      Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
        (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n) = cl ∧ w = ρ x s} with hF
    have hmem : ∀ y : Matrix (Fin n') (Fin n) L, ∀ t : ℂ, t • ρ y s ∈ F (QuotientAddGroup.mk y) :=
      fun y t => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl, rfl⟩)
    have hrest : ∑ y ∈ P.erase x, c y • ρ y s ∈ ⨆ (j) (_ : j ≠ (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n)), F j := by
      refine Submodule.sum_mem _ fun y hy => ?_
      have hyx : y ≠ x := Finset.ne_of_mem_erase hy
      have hyC : y ∈ C := (Finset.mem_filter.1 (Finset.mem_of_mem_erase hy)).1
      have hne : (QuotientAddGroup.mk y : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n) ≠ QuotientAddGroup.mk x := by
        intro he
        apply hpw y hyC x hxC hyx
        have := (QuotientAddGroup.eq).1 he.symm
        have h2 : y - x = -x + y := by abel
        rw [h2]; exact this
      exact (le_iSup₂_of_le (QuotientAddGroup.mk y) hne le_rfl : F (QuotientAddGroup.mk y) ≤ _) (hmem y (c y))
    intro h0
    rw [← Finset.add_sum_erase P _ hxP] at h0
    have hxx : c x • ρ x s = 0 := by
      have hd := (hI (QuotientAddGroup.mk x))
      rw [Submodule.disjoint_def] at hd
      apply hd _ (hmem x (c x))
      have : c x • ρ x s = -(∑ y ∈ P.erase x, c y • ρ y s) := eq_neg_of_add_eq_zero_left h0
      rw [this]; exact neg_mem hrest
    have hcx := (hC x hxC).1
    rw [smul_eq_zero] at hxx
    rcases hxx with h | h
    · exact hcx h
    · apply hs
      have h1 := congrArg (fun F : Module.End ℂ M => F s) (hP.rho_mul (-x) x)
      simp only [Module.End.mul_apply, h, map_zero, neg_add_cancel, hP.rho_zero, LinearMap.smul_apply, Module.End.one_apply] at h1
      exact (smul_eq_zero.1 h1.symm).resolve_left (hψ0 _)

end GlobalTheory.Hk3.HoweG

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterCoordinatesSeriesOnePlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_letterCoordinates_series_onePlace_alt : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (n' : ℕ) [NeZero n'], Even n' → ∀ (B : OmBasis p n') (be : MvPowerSeries (Fin 2) (FormalGroupSystem.K0 p)), BeProp p be → ∃ bv : MvPowerSeries (ZMod n') ℂ_[p], product_zeroth_first_parts.B1 p n' bv ∧ product_zeroth_first_parts.B2 p n' bv ∧ product_zeroth_first_parts.B3 p n' bv ∧ product_zeroth_first_parts.B4 p n' bv ∧ ∀ (r0 r1 : ℕ) (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p)), IntS p (inParam p U) → ∃ U' : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p], (∀ m, ‖MvPowerSeries.coeff m U'‖ ≤ 1) ∧ MvPowerSeries.subst (fun v : ZMod n' × Fin r0 × Fin r1 => MvPowerSeries.C (1 : ℂ_[p]) * jetLogG p n' v) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U))) = U' * MvPowerSeries.subst (jetLogG p n' (β := Fin r0 × Fin r1)) (product_zeroth_first_parts.expS ℂ_[p] ((-1 : ℂ_[p]) • ∑ a : Fin r0, ∑ b : Fin r1, MvPowerSeries.subst (fun s : ZMod n' => (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) bv)) := by
  first | exact @GlobalTheory.OnePlace.exists_letterCoordinates_series_onePlace | exact GlobalTheory.OnePlace.exists_letterCoordinates_series_onePlace | (intros; apply GlobalTheory.OnePlace.exists_letterCoordinates_series_onePlace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
namespace GlobalTheory.Cong.LevelExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_locU_iff {w : HeightOneSpectrum (𝓞 E)} (x : UA E n) :
    x ∈ locU n w ↔ x ∈ finU (E := E) (n := n) ∧ ∀ u, Apart u w → cLoc u x = 1 := by
  unfold locU Apart
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]

theorem cLoc_conj_eq_one {w : HeightOneSpectrum (𝓞 E)} (x : UA E n) (h1 : cLoc w x = 1) :
    cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x = 1 := by
  have hw1 : ∀ v, v = w → cLoc v x = 1 := by
    rintro v rfl
    exact h1
  have hce := GlobalTheory.SplitPts.comp_eq x (conjSrc (GlobalTheory.SplitPts.conjE E) w)
  rw [hw1 _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w), Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.transpose_one, Matrix.one_mul] at hce
  exact Units.ext hce

theorem one_of_cLoc {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (x : UA E n) (h1 : cLoc w x = 1) :
    ∀ u, ¬ Apart u w → cLoc u x = 1 := by
  intro u hu
  have hu' : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := by
    by_contra h
    exact hu h
  rcases (GlobalTheory.SplitPts.over_split hw).2.2 u hu' with rfl | rfl
  · exact h1
  · exact cLoc_conj_eq_one x h1

end GlobalTheory.Cong.LevelExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelFunctionsCommonLinearOperatorOffSplitPrimeStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelFunctions_common_linearOperator_off_splitPrime : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.LatAll → B.VecP χ → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ T : (TaylorLogMetric.VC D a b → ℂ) →ₗ[ℂ] (TaylorLogMetric.VC D a b → ℂ), ∀ i, kerTh B χ SS cl (N i) (N' i) Ξ = T (B.eNat χ a b (N i) (N' i)) := by
  first | exact @GlobalTheory.KerCommon.kerTh_common_op | exact GlobalTheory.KerCommon.kerTh_common_op | (intros; apply GlobalTheory.KerCommon.kerTh_common_op <;> assumption)
end

