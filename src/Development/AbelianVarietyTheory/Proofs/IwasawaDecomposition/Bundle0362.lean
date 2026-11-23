module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightActionMatrixCoeffPolynomialInEntries
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NablaSqEndomorphismEqSumGLOperators
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZariskiDenseRationalPointsDefiniteUnitaryCharZer
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PderivComm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperUnipotentGenericCharacterMemIntegralField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3

theorem addChar_pow_natCard_eq_one {A L : Type} [AddGroup A] [CommMonoid L] (ψ : AddChar A L) (c : A) :
    ψ c ^ Nat.card A = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]

theorem mem_Ks_of_pow_g (B : Base) (k : Fin 2) {x : B.LL} (hx : x ^ B.host.g k = 1) : x ∈ B.Ks := by
  have hp := B.host.g_prime k
  obtain ⟨z, hzK, hz⟩ := B.roots_Ks (B.host.g k * (B.host.g k - 1)) (by fin_cases k <;> simp)
  have hne : B.host.g k * (B.host.g k - 1) ≠ 0 := mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim : IsPrimitiveRoot z (B.host.g k * (B.host.g k - 1)) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := B.embLL) ?_ B.embLL.injective
    rw [hz]
    exact_mod_cast Complex.isPrimitiveRoot_exp _ hne
  have : NeZero (B.host.g k * (B.host.g k - 1)) := ⟨hne⟩
  obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one (ξ := x) (by rw [pow_mul, hx, one_pow])
  rw [← hj]
  exact pow_mem hzK j

theorem chr0_mem_Ks : ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px) (p : lev0 I),
    ((chr0 I p : B.LLˣ) : B.LL) ∈ B.Ks := by
  classical
  intro B px I p
  have hPr := (GlobalTheory.Mem.Col2.base_fields_primes_ok B px).2.1
  unfold chr0 P0 LevelP.ofLocal
  letI : IsOneApply (lev0 I →* B.LLˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply (lev0 I →* B.LLˣ) := ⟨fun _ _ _ => rfl⟩
  erw [prod_apply, Units.coe_prod]
  refine B.Ks.prod_mem fun PP _ => ?_
  have hk : ∃ k, PP.1 ∈ (B.primes px).vG k := by
    have h : PP.1 ∈ (B.primes px).vG 0 ∪ (B.primes px).vG 1 := by
      have h0 := PP.2
      unfold Formalism.L2.Col.Primes.vGs at h0
      convert h0
    rcases Finset.mem_union.1 h with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨k, hw⟩ := hk
  refine mem_Ks_of_pow_g B k ?_
  have hc : Nat.card (kP PP.1) = B.host.g k := by
    have h := hPr.vG_norm k PP.1 hw
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
    exact h
  rw [← hc]
  exact addChar_pow_natCard_eq_one _ _

end GlobalTheory.Mem.R3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesEqMassesOfUnfold
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.VolMass

theorem volumes_eq_masses_of_unfold :
    (∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) → ∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D :=
  fun hU D hV =>
    have hT : StandardLattice.VolTie D := Formalism.L2.Theta.VolTieG.volTie hV
    StandardLattice.volume_eq_mass_of_definite D (StandardLattice.volumeMass_of_unfolding D (hU D hT))
      (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.mass_volume_identity_of_class_decomp D hT (GlobalTheory.genusMassStd_all D)
        (GlobalTheory.DefiniteDecompObj.doubleCosets_mass D))

end GlobalTheory.Mem.VolMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorRepOfEmbeddingsIsIrreducible
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem GlobalTheory.AlgWtF.tenRepF_isIrreducible : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → (GlobalTheory.AlgWtF.tenRepF emb lam).IsIrreducible := by
  intro L _ _ _ n ι _ K _ _ emb lam hCM
  have hstab : ∀ W : Submodule K (Formalism.L2.DIV.VV K lam),
      (∀ γ : GQ L n, ∀ w ∈ W, GlobalTheory.AlgWtF.tenRepF emb lam γ w ∈ W) →
      ∀ g : ι → GL (Fin n) K, ∀ w ∈ W, Formalism.L2.DIV.rhoK lam g w ∈ W := by
    intro W hW g w hw
    have hrat : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → ∀ w ∈ W,
        Formalism.L2.DIV.rhoK lam (GlobalTheory.AlgWtF.embGLF emb γ₀) w ∈ W := by
      intro γ₀ hγ₀ w hw
      obtain ⟨γ, rfl⟩ := GlobalTheory.T.unitaryRationalPointMatrixHom_surjective_onto L n γ₀ hγ₀
      exact hW γ w hw
    by_contra hnot
    have hx : ((Formalism.L2.DIV.rhoK lam g w : Formalism.L2.DIV.VV K lam) : Formalism.L2.DIV.Pol K ι n) ∉
        W.map (Formalism.L2.DIV.VV K lam).subtype := by
      rintro ⟨y, hy, hyx⟩
      exact hnot (by rw [show Formalism.L2.DIV.rhoK lam g w = y from Subtype.ext hyx.symm]; exact hy)
    obtain ⟨ψ, hψx, hψW⟩ := Submodule.exists_le_ker_of_notMem hx
    obtain ⟨P, hP⟩ := _root_.GlobalTheory.ActPolyCoeff.polyAction_coeff_poly K ι n lam (w : Formalism.L2.DIV.Pol K ι n) ψ
    let f : (ι ⊕ ι) × Fin n × Fin n → (L →+* K) × Fin n × Fin n :=
      fun v => (Sum.elim emb (fun τ => (emb τ).comp (IsCMField.complexConj L : L →+* L)) v.1, v.2)
    have hzero := _root_.GlobalTheory.UnitaryDense.unitary_points_dense L n K (MvPolynomial.rename f P) ?_
    · obtain ⟨B, hBc, hBe⟩ := _root_.GlobalTheory.cmType_family_extend L n ι K emb hCM g
      have h0 := hzero B hBc
      rw [MvPolynomial.eval_rename] at h0
      apply hψx
      have h1 : ((Formalism.L2.DIV.rhoK lam g w : Formalism.L2.DIV.VV K lam) : Formalism.L2.DIV.Pol K ι n) =
          Formalism.L2.DIV.actP lam g w := rfl
      rw [h1, hP g, ← h0]
      refine congrArg (fun y => MvPolynomial.eval y P) ?_
      funext v
      rcases v with ⟨τ | τ, a, b⟩
      · simp [f, hBe]
      · simp only [f, Function.comp_apply, Sum.elim_inr]
        rw [hBc (emb τ), hBe τ]
        rfl
    · intro γ₀ hγ₀
      rw [MvPolynomial.eval_rename]
      have h2 := hrat γ₀ hγ₀ w hw
      have h3 : ψ (Formalism.L2.DIV.actP lam (GlobalTheory.AlgWtF.embGLF emb γ₀) w) = 0 :=
        hψW ⟨_, h2, rfl⟩
      rw [hP] at h3
      rw [← h3]
      refine congrArg (fun y => MvPolynomial.eval y P) ?_
      funext v
      rcases v with ⟨τ | τ, a, b⟩
      · simp [f, GlobalTheory.AlgWtF.embGLF]
      · have hinv : (((γ₀⁻¹ : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) =
            ReciprocityTheory.Aut.conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L) :=
          Units.inv_eq_of_mul_eq_one_right hγ₀
        simp only [f, Function.comp_apply, Sum.elim_inr, GlobalTheory.AlgWtF.embGLF, MonoidHom.pi_apply, ← map_inv,
          Matrix.GeneralLinearGroup.map_apply, hinv, ReciprocityTheory.Aut.conjT, Matrix.transpose_apply, Matrix.map_apply,
          RingHom.comp_apply]
  have hsimple : ∀ W : Submodule K (Formalism.L2.DIV.VV K lam),
      (∀ g : ι → GL (Fin n) K, ∀ w ∈ W, Formalism.L2.DIV.rhoK lam g w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    _root_.GlobalTheory.TensorIrr.eq_bot_or_eq_top K ι n lam (fun τ => _root_.GlobalTheory.NablaDensity.endo_eq_sum_sqAct K n (lam τ) (_root_.GlobalTheory.AlcZero.nablaSq_simple_charZero K n (lam τ)))
  haveI hnt : Nontrivial (Formalism.L2.DIV.VV K lam) := _root_.GlobalTheory.CoeffSpace.nontrivial_VV K ι n lam
  haveI : Nontrivial (Subrepresentation (GlobalTheory.AlgWtF.tenRepF emb lam)) := by
    refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
    have h' := congrArg Subrepresentation.toSubmodule h
    obtain ⟨x, hx⟩ := exists_ne (0 : Formalism.L2.DIV.VV K lam)
    have hxt : x ∈ (⊤ : Subrepresentation (GlobalTheory.AlgWtF.tenRepF emb lam)).toSubmodule := trivial
    rw [← h'] at hxt
    exact hx hxt
  refine { eq_bot_or_eq_top := fun W => ?_ }
  rcases hsimple W.toSubmodule (hstab W.toSubmodule (fun γ w hw => W.apply_mem_toSubmodule γ hw)) with h | h
  · left; exact Subrepresentation.ext h
  · right; exact Subrepresentation.ext h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealDerivativeFockVectorsAll
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilReal

open GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.WeilReal.QuadAlg Formalism.IndefR.Fock.Sk

def frOf {D : D7} (V : HSp D) (s B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (p : D.what₂.Tau → ℕ)
    (h : ∀ τ, IsONBasis (gramAt D V τ) (s τ) (B τ) (p τ)) : Fr V where
  ε τ := sgB (p τ)
  fr τ := (B τ)⁻¹
  fr_unit τ := (isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det _ (onb_facts (h τ)).1)
  fr_gram τ := by
    obtain ⟨u, g, -⟩ := onb_facts (h τ)
    rw [← g]
    have h1 : ((B τ)⁻¹)ᴴ * (B τ)ᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ u, conjTranspose_one]
    calc _ = (((B τ)⁻¹)ᴴ * (B τ)ᴴ) * gramAt D V τ * (B τ * (B τ)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, mul_nonsing_inv _ u, Matrix.one_mul, Matrix.mul_one]

variable {D : D7} {V : HSp D} {s B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {p : D.what₂.Tau → ℕ}

theorem frOf_onb (h : ∀ τ, IsONBasis (gramAt D V τ) (s τ) (B τ) (p τ)) : (frOf V s B p h).onb = B := by
  funext τ
  exact nonsing_inv_nonsing_inv _ (onb_facts (h τ)).1

theorem frOf_cart (h : ∀ τ, IsONBasis (gramAt D V τ) (s τ) (B τ) (p τ)) : (frOf V s B p h).cart = s := by
  funext τ
  obtain ⟨u, -, c⟩ := onb_facts (h τ)
  change ((B τ)⁻¹)⁻¹ * Formalism.REAL.Jm (sgB (p τ)) * (B τ)⁻¹ = s τ
  rw [nonsing_inv_nonsing_inv _ u, ← c, mul_nonsing_inv_cancel_right _ _ u]

theorem pure_zero {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i, A i 0 = 0) (P : MvPolynomial ι ℂ) :
    pureTensorL A (0 : X → ℂ) P = 0 := by
  have h : ∀ l : List ι, l.foldr (fun i g => A i g) (0 : X → ℂ) = 0 := fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.foldr_cons, ih, hA]
  have hz : pureTensorL A (0 : X → ℂ) = 0 := (MvPolynomial.basisMonomials ι ℂ).ext fun k => by
    simp only [pureTensorL, Module.Basis.constr_basis, LinearMap.zero_apply]
    exact h _
  rw [hz, LinearMap.zero_apply]

end GlobalTheory.WeilReal

namespace GlobalTheory.WeilReal

open GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.WeilReal.QuadAlg Formalism.IndefR.Fock.Sk

theorem comb {R : Type} [AddCommGroup R] [Module ℂ R] (a b q P : R) (h c d : ℂ) (hq : a + b = q + h • P) :
    q + (h + c - d) • P = (a + (-d) • P) + (b + c • P) := by
  have e : q = a + b - h • P := eq_sub_of_add_eq hq.symm
  rw [e]
  module

theorem realAllO : ∀ D : D7, Formalism.IndefR.WeilFull.RealAllO D := by
  intro D ψ S T χS χT om hd _ θ sS sT BS BT pS pT hp τ αS αT hαS hαT XS XT hXS hXT f hf hv P x
  obtain ⟨A, hA⟩ : ∃ A : Fr S, A = frOf S sS BS pS hp.onbS := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fr T, B = frOf T sT BT pT hp.onbT := ⟨_, rfl⟩
  have cA : A.cart = sS := hA ▸ frOf_cart hp.onbS
  have cB : B.cart = sT := hB ▸ frOf_cart hp.onbT
  have oA : A.onb = BS := hA ▸ frOf_onb hp.onbS
  have oB : B.onb = BT := hB ▸ frOf_onb hp.onbT
  have eA : A.ε τ = sgB (pS τ) := by rw [hA]; rfl
  have eB : B.ε τ = sgB (pT τ) := by rw [hB]; rfl
  have rA : A.fr τ = (BS τ)⁻¹ := by rw [hA]; rfl
  have rB : B.fr τ = (BT τ)⁻¹ := by rw [hB]; rfl
  have pt : pureTensorO ψ θ S T sS sT BS BT f = ptF ψ θ A B f := by
    rw [ptF, cA, cB, oA, oB]
  rw [pt]
  have lin : ∀ (g : WO S T → ℂ) (Q Q' : MvPolynomial (FVar D T.rank S.rank) ℂ),
      ptF ψ θ A B g (Q + Q') = ptF ψ θ A B g Q + ptF ψ θ A B g Q' := fun g Q Q' =>
    map_add (pureTensorO ψ θ S T A.cart B.cart A.onb B.onb g) Q Q'
  have lsm : ∀ (g : WO S T → ℂ) (c : ℂ) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ),
      ptF ψ θ A B g (c • Q) = c • ptF ψ θ A B g Q := fun g c Q =>
    map_smul (pureTensorO ψ θ S T A.cart B.cart A.onb B.onb g) c Q
  by_cases f0 : f = 0
  · subst f0
    have z0 : ∀ Q, ptF ψ θ A B 0 Q = 0 := fun Q => by
      refine pure_zero _ (fun k => ?_) Q
      funext y
      simp [aPlusAll, aPlus, crea, Datum.dRho, heisO]
    simp only [z0, map_zero]
    exact hasDerivAt_const _ _
  obtain ⟨f₀, hv0, hne⟩ := _root_.GlobalTheory.Mem.VacReal.exists_isVacF_ne_zero D S T A B θ ψ hp.std hp.inf f hf f0
  obtain ⟨κS, κT, hκ⟩ := GlobalTheory.T.realLieAlgebra_acts_by_fockOperators_upToScalars D S T A B θ ψ χS χT om τ hp.inf hd
  have k0 := hκ f₀ hv0.1 (hv0.2 τ)
  have all := _root_.GlobalTheory.LieScalar.lieFockAll D S T A B θ ψ χS χT om f₀ τ αS αT hp.inf hd hαS hαT hv0
  obtain ⟨z, hz⟩ := Function.ne_iff.1 hne
  have hz' : f₀ z ≠ 0 := hz
  have one : ∀ c : ℂ, ptF ψ θ A B f₀ (c • (1 : MvPolynomial _ ℂ)) z = c * f₀ z := fun c => by
    rw [lsm]
    have e1 : ptF ψ θ A B f₀ 1 = f₀ := GlobalTheory.FockIndep.pure_one f₀
    rw [e1]
    rfl
  have eS : κS XS = -((αT : ℂ) * XS.trace) := by
    have e := (k0.1 XS hXS 1 z).unique (all.1 XS hXS 1 z)
    rw [lin, lin, Pi.add_apply, Pi.add_apply, add_right_inj, one, one] at e
    exact mul_right_cancel₀ hz' e
  have eT : κT XT = (αS : ℂ) * XT.trace := by
    have e := (k0.2 XT hXT 1 z).unique (all.2 XT hXT 1 z)
    rw [lin, lin, Pi.add_apply, Pi.add_apply, add_right_inj, one, one] at e
    exact mul_right_cancel₀ hz' e
  have kf := hκ f hf (by rw [cA, cB]; exact hv)
  have ht : IsThetaFunO ψ S T (ptF ψ θ A B f P) :=
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hp.std hp.inf _ _ _ _ hf P
  have sm := _root_.GlobalTheory.Mem.LieSum.hasDerivAt_add D S T θ ψ χS χT om τ hp.inf hd XS hXS XT hXT _ _ _ ht (kf.1 XS hXS P) (kf.2 XT hXT P) x
  have uS := (onb_facts (hp.onbS τ)).1
  have uT := (onb_facts (hp.onbT τ)).1
  have frA : (A.fr τ * XS * (A.fr τ)⁻¹) = (BS τ)⁻¹ * XS * BS τ := by
    rw [rA, nonsing_inv_nonsing_inv _ uS]
  have frB : (B.fr τ * XT * (B.fr τ)⁻¹) = (BT τ)⁻¹ * XT * BT τ := by
    rw [rB, nonsing_inv_nonsing_inv _ uT]
  have q := fock_eq_quad τ (pS τ) (pT τ) (hp.onbS τ) (hp.onbT τ) hXS hXT P
  have e : ptF ψ θ A B f (quadOp τ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) P +
      (halfTrJ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) + (αS : ℂ) * XT.trace - (αT : ℂ) * XS.trace) • P) x =
      ptF ψ θ A B f (fockS τ (A.ε τ) (B.ε τ) ((A.fr τ * XS * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P + κS XS • P) x +
      ptF ψ θ A B f (fockT τ (A.ε τ) (B.ε τ) (B.fr τ * XT * (B.fr τ)⁻¹) P + κT XT • P) x := by
    rw [← Pi.add_apply (ptF ψ θ A B f _), ← lin, frA, frB, eS, eT, eA, eB, comb _ _ _ _ _ _ _ q]
  rw [e]
  exact sm

end GlobalTheory.WeilReal

end
end

