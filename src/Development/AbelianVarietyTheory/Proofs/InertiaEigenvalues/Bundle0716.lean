module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOMulSource
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParametersUnramifiedUnitary
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertHeckeEigen

open Formalism.UG GlobalTheory.PRep

section Abstract

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def quotMap (p : G →* H) (K : Subgroup H) : G ⧸ K.comap p → H ⧸ K :=
  Quotient.map' p fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [← map_inv, ← map_mul]
    exact hab

theorem quotMap_mk (p : G →* H) (K : Subgroup H) (a : G) :
    quotMap p K (a : G ⧸ K.comap p) = (p a : H ⧸ K) := rfl

theorem quotMap_bijective (p : G →* H) (hp : Function.Surjective p) (K : Subgroup H) :
    Function.Bijective (quotMap p K) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [quotMap_mk, quotMap_mk, QuotientGroup.eq] at hxy
    rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]
    exact hxy
  · intro d
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective d
    obtain ⟨a, rfl⟩ := hp y
    exact ⟨a, rfl⟩

theorem heckeVec_comp_surj (p : G →* H) (hp : Function.Surjective p) {K : Subgroup H} {h : H → ℂ}
    (hh : IsBiInv K h) (ρ : Representation ℂ H V) {v : V} (hv : v ∈ fixed ρ K) :
    GlobalTheory.LFun.heckeVec (ρ.comp p) (K.comap p) (fun x => h (p x)) v = GlobalTheory.LFun.heckeVec ρ K h v := by
  let e := Equiv.ofBijective _ (quotMap_bijective p hp K)
  rw [GlobalTheory.LFun.heckeVec_eq_of_section hh hv (fun d => p (e.symm d).out) fun d => ?_]
  · rw [← finsum_comp_equiv e (f := fun d => h (p (e.symm d).out) • ρ (p (e.symm d).out) v)]
    simp only [Equiv.symm_apply_apply]
    rfl
  · rw [← quotMap_mk, QuotientGroup.out_eq']
    exact e.apply_symm_apply d

theorem finite_support_comp (p : G →* H) (hp : Function.Surjective p) {K : Subgroup H} {h : H → ℂ}
    (hh : IsBiInv K h) (hf : {d : H ⧸ K | h d.out ≠ 0}.Finite) :
    {c : G ⧸ K.comap p | h (p c.out) ≠ 0}.Finite := by
  refine (hf.preimage (quotMap_bijective p hp K).1.injOn).subset fun c hc => ?_
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hc ⊢
  have hk : (quotMap p K c).out⁻¹ * p c.out ∈ K := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← quotMap_mk, QuotientGroup.out_eq']
  have e1 := hh 1 ⟨_, hk⟩ (quotMap p K c).out
  simp only [OneMemClass.coe_one, one_mul, mul_inv_cancel_left] at e1
  rwa [e1] at hc

theorem heckeVec_eq_sum (ρ : Representation ℂ G V) (K : Subgroup G) (h : G → ℂ) (S : Finset (G ⧸ K))
    (hS : ∀ c : G ⧸ K, h c.out ≠ 0 → c ∈ S) (x : V) :
    GlobalTheory.LFun.heckeVec ρ K h x = ∑ c ∈ S, h c.out • ρ c.out x := by
  refine finsum_eq_sum_of_support_subset _ fun c hc => hS c fun h0 => hc ?_
  simp [h0]

theorem mem_of_mem_iSup {ι : Type} (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (hσ : σ.IsIrreducible)
    (f : ι → W →ₗ[ℂ] V) (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Set G) (Z : Submodule ℂ V)
    (hZ : ∀ i v, (∀ k ∈ K, σ k v = v) → f i v ∈ Z) (hZK : ∀ z ∈ Z, ∀ k ∈ K, ρ k z = z) (φ : V)
    (hK : ∀ k ∈ K, ρ k φ = φ) (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) : φ ∈ Z := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7; revert G V W h_3 h_4 h_5 h_6 h_7 ι ρ σ hσ f hf K Z hZ hZK φ hK hφ; exact @_root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range)
  | exact @_root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range
  | exact _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range
  | (apply _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvariantSupremum.fixed_mem_of_mem_iSup_range ..)

end Abstract

end GlobalTheory.InertHeckeEigen


open GlobalTheory.InertHeckeEigen Formalism.UG GlobalTheory.PRep GlobalTheory.DefU in
theorem GlobalTheory.InertHeckeEigen.heckeVec_eq_satU_of_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (w : HeightOneSpectrum (𝓞 L)) (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), Formalism.UG.IsUnramInv ϖ s q → ∀ p : locU n w →* Formalism.UG.GU s n, Function.Surjective p → ∀ σ : SmIrr (Formalism.UG.GU s n), IsCompAlong U (locU n w) p σ.ρ → ∀ α0 : Fin (n / 2) → ℂˣ, GlobalTheory.LFun.HasSatU ϖ q σ.ρ α0 → ∀ φ ∈ U, (∀ x : locU n w, p x ∈ Formalism.UG.KU s n → RU L n x.val φ = φ) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU s n), GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU s n).comap p) (fun x => h (p x)) φ = Formalism.UG.SatU ϖ q h (fun i => (α0 i : ℂ)) • φ := by
  intro L _ _ _ n U hU w s ϖ q hq p hp σ hcomp α0 hsat φ hφ hfix h hh
  have hfin : {c : locU n w ⧸ (KU s n).comap p | h (p c.out) ≠ 0}.Finite :=
    finite_support_comp p hp hh.1 (Formalism.UG.P.finite_support_cosets (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hq n) hh.2)
  have hS : ∀ c : locU n w ⧸ (KU s n).comap p, (fun x => h (p x)) c.out ≠ 0 → c ∈ hfin.toFinset :=
    fun c hc => hfin.mem_toFinset.2 hc
  let T : (UA L n → ℂ) →ₗ[ℂ] (UA L n → ℂ) :=
    ∑ c ∈ hfin.toFinset, h (p c.out) • (RU L n) (c.out : UA L n)
  have hT : ∀ x, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((KU s n).comap p) (fun x => h (p x)) x
      = T x := fun x => by
    rw [heckeVec_eq_sum _ _ _ _ hS x]
    simp [T, LinearMap.sum_apply]
  let lam := SatU ϖ q h (fun i => (α0 i : ℂ))
  let Z : Submodule ℂ (UA L n → ℂ) :=
    fixed ((RU L n).comp (locU n w).subtype) ((KU s n).comap p) ⊓ LinearMap.ker (T - lam • LinearMap.id)
  have hZ' : ∀ x, x ∈ Z ↔ (∀ k ∈ (KU s n).comap p, RU L n (k : UA L n) x = x) ∧ T x = lam • x := fun x => by
    simp only [Z, Submodule.mem_inf, GlobalTheory.LGrp.mem_fixed, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl

  let π : AutSub L n := ⟨U, hU⟩
  obtain ⟨hσirr, f, hf0, hfm, hf⟩ := hcomp
  have hirr : Representation.IsIrreducible (σ.ρ.comp p) := by
    obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
    obtain ⟨x, rfl⟩ := hp g
    exact hY x v hv
  let F : Representation.IntertwiningMap (σ.ρ.comp p) (π.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints L n w
  have htop := (_root_.GlobalTheory.CuspRep.CompUniq.isotypic (UA L n) (locU n w) π.V σ.V σ.V π.rep (locU n w).subtype (σ.ρ.comp p) (σ.ρ.comp p)
    π.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  let fi : Representation.IntertwiningMap (σ.ρ.comp p) (π.rep.comp (locU n w).subtype) → σ.V →ₗ[ℂ] (UA L n → ℂ) :=
    fun i => U.subtype ∘ₗ i.toLinearMap
  have hfi : ∀ i g u, fi i ((σ.ρ.comp p) g u) = (RU L n).comp (locU n w).subtype g (fi i u) := fun i g u =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining (σ.ρ.comp p) (π.rep.comp (locU n w).subtype) i g u)
  have hmem : φ ∈ ⨆ i, LinearMap.range (fi i) := by
    have : φ ∈ (⨆ i : Representation.IntertwiningMap (σ.ρ.comp p) (π.rep.comp (locU n w).subtype),
        LinearMap.range i.toLinearMap).map U.subtype := by
      rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
    simp only [fi, LinearMap.range_comp]
    rwa [Submodule.map_iSup] at this

  have hZ : ∀ i v, (∀ k ∈ ((KU s n).comap p : Set (locU n w)), (σ.ρ.comp p) k v = v) → fi i v ∈ Z := by
    intro i v hv
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]; exact Z.zero_mem
    have hvK : v ∈ fixed σ.ρ (KU s n) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
      obtain ⟨x, rfl⟩ := hp k
      exact hv x hk
    refine (hZ' _).2 ⟨fun k hk => (hfi i k v).symm.trans (congrArg (fi i) (hv k hk)), ?_⟩
    have e2 := heckeVec_comp_surj p hp hh.1 σ.ρ hvK
    rw [heckeVec_eq_sum _ _ _ _ hS] at e2
    rw [((hsat.2 v hvK hv0).2.2 h hh)] at e2
    rw [← hT (fi i v), heckeVec_eq_sum _ _ _ _ hS]
    calc _ = fi i (∑ c ∈ hfin.toFinset, h (p c.out) • (σ.ρ.comp p) c.out v) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [map_smul, hfi]
      _ = lam • fi i v := by rw [e2, map_smul]
  have hZK : ∀ z ∈ Z, ∀ k ∈ ((KU s n).comap p : Set (locU n w)), (RU L n).comp (locU n w).subtype k z = z :=
    fun z hz k hk => ((hZ' z).1 hz).1 k hk
  have hφZ := mem_of_mem_iSup ((RU L n).comp (locU n w).subtype) (σ.ρ.comp p) hirr fi hfi _ Z hZ hZK φ
    (fun k hk => hfix k hk) hmem
  rw [hT]
  exact ((hZ' φ).1 hφZ).2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilDoublingProductRationalTranslateEqFram
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLagTerms
variable {D : D7}

theorem cA_incA_loc (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

theorem adjO_mul_rat (V W : HSp D) (y : Mx D V.rank W.rank) (M : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    GlobalTheory.PairLift.adjO V W (HMul.hMul (y : Matrix (Fin V.rank) (Fin W.rank) (AE D)) (M.map (incA D))) =
      ratMul (hAdj W M) (GlobalTheory.PairLift.adjO V W y) := by
  have e : ((M.map (incA D)).map (cA D))ᵀ = ((M.map star)ᵀ).map (incA D) := by
    ext i j; simp [cA_incA_loc]
  rw [GlobalTheory.AdjLawPf.adjO_eq, GlobalTheory.AdjLawPf.adjO_eq, GlobalTheory.AdjLawPf.conjT_mul, e]
  unfold ratMul hAdj
  rw [Matrix.map_mul, Matrix.map_mul]
  have g1 : (HSpace.gram W).map (incA D) * (HSpace.gram W)⁻¹.map (incA D) = 1 :=
    mul_eq_one_comm.1 (GlobalTheory.AdjLawPf.inv_mul_gram W)
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((HSpace.gram W).map (incA D)), g1, Matrix.one_mul]

theorem act_lagr (V W : HSp D) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E)
    (hg : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D)) (y : Mx D V.rank W.rank) :
    actO (GlobalTheory.Doubling.dblSp W) V γ⁻¹ 1 (GlobalTheory.SiegelFormula.lagr W V y) =
      HMul.hMul (GlobalTheory.SiegelFormula.lagr W V y : Matrix (Fin V.rank) (Fin (W.rank + W.rank)) (AE D)) (g₀.map (incA D)) := by
  unfold actO
  rw [inv_inv, hg, GlobalTheory.AdjLawPf.mt_one, Matrix.one_mul]

theorem resL_lagr (V W : HSp D) (y : Mx D V.rank W.rank)
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL W V (HMul.hMul (GlobalTheory.SiegelFormula.lagr W V y : Matrix (Fin V.rank) (Fin (W.rank + W.rank)) (AE D)) (g₀.map (incA D))) =
      HMul.hMul (y : Matrix (Fin V.rank) (Fin W.rank) (AE D)) (((blk W g₀).toBlocks₁₁ - (blk W g₀).toBlocks₂₁).map (incA D)) := by
  ext i j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [GlobalTheory.SiegelFormula.lagr, Matrix.of_apply, GlobalTheory.Doubling.pairVec_inl, GlobalTheory.Doubling.pairVec_inr, blk,
    Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Matrix.submatrix_apply, Matrix.sub_apply, map_sub, mul_sub,
    Finset.sum_sub_distrib, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  abel

theorem resR_lagr (V W : HSp D) (y : Mx D V.rank W.rank)
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    -GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR W V (HMul.hMul (GlobalTheory.SiegelFormula.lagr W V y : Matrix (Fin V.rank) (Fin (W.rank + W.rank)) (AE D)) (g₀.map (incA D))) =
      HMul.hMul (y : Matrix (Fin V.rank) (Fin W.rank) (AE D)) (((blk W g₀).toBlocks₂₂ - (blk W g₀).toBlocks₁₂).map (incA D)) := by
  ext i j
  simp only [Matrix.neg_apply, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [GlobalTheory.SiegelFormula.lagr, Matrix.of_apply, GlobalTheory.Doubling.pairVec_inl, GlobalTheory.Doubling.pairVec_inr, blk,
    Matrix.toBlocks₂₂, Matrix.toBlocks₁₂, Matrix.submatrix_apply, Matrix.sub_apply, map_sub, mul_sub,
    Finset.sum_sub_distrib, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  abel

theorem dbl_actO_lagr : ∀ (D : D7) (V W : HSp D) (f₁ f₂ : WO V W → ℂ) (γ : GA D (GlobalTheory.Doubling.dblSp W))
    (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E),
    Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) → ∀ (y : Mx D V.rank W.rank),
    GlobalTheory.SWPairProof.dbl V W f₁ f₂ (actO (GlobalTheory.Doubling.dblSp W) V γ⁻¹ 1 (GlobalTheory.SiegelFormula.lagr W V y)) =
      f₁ (ratMul (frameOf W g₀).1 (GlobalTheory.PairLift.adjO V W y)) * star (f₂ (ratMul (frameOf W g₀).2 (GlobalTheory.PairLift.adjO V W y))) := by
  intro D V W f₁ f₂ γ g₀ hg y
  rw [act_lagr V W γ g₀ hg y, GlobalTheory.SWPairProof.dbl_apply, resL_lagr, resR_lagr, adjO_mul_rat, adjO_mul_rat,
    frameOf_fst, frameOf_snd, starRingEnd_apply, mul_comm]

end GlobalTheory.SWLagTerms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.Published GlobalTheory.LFun

namespace GlobalTheory.SpehPair

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N a d : ℕ}

theorem isUnitary_of_isNormalised {π : CuspSub E a} (h : IsNormalised π) : π.IsUnitary := by
  obtain ⟨ω, hω⟩ := Central.exists_hasCentral E a π
  have hs : ∀ (b : ℕ) (t : ℝ), splitCentre E b t =
      Matrix.GeneralLinearGroup.scalar (Fin b) (infId E (expU fun _ => (t : ℂ))) := fun b t =>
    (cornerGL_scalar (sInf E) _)
  have h1 : ∀ t : ℝ, ((ω.1 (infId E (expU fun _ => (t : ℂ))) : ℂˣ) : ℂ) = 1 := fun t => by
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
    obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h0 (Subtype.ext (funext hc))
    have h2 := hω.apply hφ (infId E (expU fun _ => (t : ℂ))) g
    rw [← hs, h φ hφ] at h2
    exact mul_right_cancel₀ hg (h2.symm.trans (one_mul _).symm)
  have h3 : ((CuspSub.triv E (le_refl 1)).twist ω).HasCentral ω :=
    CuspSub.hasCentral_iff.2 (CG.hasCentChar_ofChar ω)
  have h4 : IsNormalised ((CuspSub.triv E (le_refl 1)).twist ω) := fun φ hφ t g => by
    rw [hs, h3.apply hφ, h1, one_mul]
  exact hω.isUnitary_iff.2 (h3.isUnitary_iff.1 (Model.isUnitary_of_isNormalised h4))

theorem eventually_spherical {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ σ, IsLocCompGL V w σ →
      GlobalTheory.LGrp.IsSpherical σ.ρ (KGL w (n := N)) := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  filter_upwards [LocSph.eventually_mem ((hV.aut φ hφ).level.mem_nhds (by simp))] with w hw σ hσ
  obtain ⟨f, hf0, hfV, hf⟩ := hσ
  let F : σ.V →ₗ[ℂ] V := f.codRestrict V hfV
  have hF : ∀ g v, F (σ.ρ g v) = DiscLocEx.locRepD hV.stable w g (F v) := fun g v => Subtype.ext (hf g v)
  have hF0 : F ≠ 0 := fun e => hf0 (LinearMap.ext fun v => congrArg Subtype.val (LinearMap.congr_fun e v))
  have hi : LinearMap.ker F = ⊥ := ((isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hF, hv, map_zero]) |>.resolve_right fun e => hF0 (LinearMap.ker_eq_top.1 e)
  have hfix : (⟨φ, hφ⟩ : V) ∈ GlobalTheory.PRep.fixed (DiscLocEx.locRepD hV.stable w) (KGL w (n := N)) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (by
      obtain ⟨g, rfl⟩ := hk
      exact hw g)
  have h1 : LinearMap.range F ⊓ GlobalTheory.PRep.fixed (DiscLocEx.locRepD hV.stable w) (KGL w (n := N)) ≠ ⊥ := fun e =>
    hF0 (LinearMap.range_eq_bot.1 (DiscLocEx.eq_bot_of_fixedD hV w GlobalTheory.SatInd.isCompact_KGL
      (fun e => h0 (congrArg Subtype.val e)) hfix _ (by rintro g _ ⟨v, rfl⟩; exact ⟨_, hF g v⟩) e))
  obtain ⟨_, ⟨⟨v, rfl⟩, hv⟩, hv0⟩ := (Submodule.ne_bot_iff _).1 h1
  exact (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => LinearMap.ker_eq_bot.1 hi (by
    rw [hF, GlobalTheory.LGrp.mem_fixed.1 hv k hk]), fun e => hv0 (by rw [e, map_zero])⟩

theorem exists_sat_twist (hd : 1 ≤ d) {π : CuspSub E a} {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} {σ' : SmIrr (GL (Fin N) (w.adicCompletion E))}
    (hσ : π.IsLocComp w σ) (h : GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ)
    {T : Multiset ℂˣ} (hT : HasSatGL w σ'.ρ T) (ν : ℝ → HChar E) (hν : ∀ s, (ν s).IsAbsPow s) :
    ∃ B : Fin d → Multiset ℂˣ, (∀ i, ((CG.mk π).twist (ν (-spehExp d i))).HasSat w (B i)) ∧ ∑ i, B i = T := by
  obtain ⟨S, hS, e⟩ := GlobalTheory.SatInd.exists_sat_of_isSpeh hd σ.smooth σ.irred h hT
  refine ⟨_, fun i => GlobalTheory.SphGal.hasSatGL_twist E a π _ w S ((hν _).1 w)
    (GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ hS), ?_⟩
  refine Multiset.map_injective Units.val_injective (Eq.trans ?_ e)
  refine (map_sum (Multiset.mapAddMonoidHom _) _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [Multiset.coe_mapAddMonoidHom, Multiset.map_map]
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [Function.comp_apply, Units.val_mul, (hν _).2.1 w, spehExp]
  congr 2
  push_cast
  ring

end GlobalTheory.SpehPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumHeisOPureTensorO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.FiniteHeisComb

variable {D : D7}

theorem heisO_aPlus (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {u : WO S T}
    (hu : u.map (infPart D) = 0) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    heisO ψ S T u (aPlus (heisO ψ S T) θ τ J z g) = aPlus (heisO ψ S T) θ τ J z (heisO ψ S T u g) := by
  simp only [aPlus, crea]
  change GlobalTheory.Hk3.FiniteHeis.heisLin ψ S T u _ = _
  rw [map_smul, map_sub, map_smul]
  show _ • (heisO ψ S T u (Formalism.IndefR.Datum.dRho _ _ _ _ _) - _ • heisO ψ S T u (Formalism.IndefR.Datum.dRho _ _ _ _ _)) = _
  rw [GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hu, GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hu]

theorem aPlus_sum {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {S T : HSp D} (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (c : WO S T → ℂ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    (s : Finset (WO S T)) :
    IsThetaFunO ψ S T (∑ u ∈ s, c u • heisO ψ S T u g) ∧
      aPlus (heisO ψ S T) θ τ J z (∑ u ∈ s, c u • heisO ψ S T u g) =
        ∑ u ∈ s, c u • aPlus (heisO ψ S T) θ τ J z (heisO ψ S T u g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using (GlobalTheory.OrientedHeis.theta_zero : IsThetaFunO ψ S T 0), ?_⟩
    have e := GlobalTheory.AdTh.SourceBasis.aPlus_smul hψ hθ τ J z 0 (GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := S) (T := T))
    simpa using e
  | insert a s ha ih =>
    have ht : IsThetaFunO ψ S T (c a • heisO ψ S T a g) :=
      GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hg a)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨GlobalTheory.OrientedHeis.theta_add ht ih.1, ?_⟩
    rw [GlobalTheory.AdTh.SourceBasis.aPlus_add hψ hθ τ J z ht ih.1, ih.2,
      GlobalTheory.AdTh.SourceBasis.aPlus_smul hψ hθ τ J z _ (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hg a)]

theorem sum_heisO_pureTensorO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (c : WO S T →₀ ℂ), (∀ u ∈ c.support, u.map (infPart D) = 0) → ∀ x : WO S T → ℂ, IsThetaFunO ψ S T x → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, (c.sum fun u z => z • heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT x P)) = pureTensorO ψ θ S T sS sT BS BT (c.sum fun u z => z • heisO ψ S T u x) P := by
  intro D ψ θ S T hψ hθ sS BS sT BT c hc x hx P
  let Φ : Module.End ℂ (WO S T → ℂ) := c.sum fun u z => z • GlobalTheory.Hk3.FiniteHeis.heisLin ψ S T u
  have hΦ : ∀ g, Φ g = c.sum fun u z => z • heisO ψ S T u g := by
    intro g
    simp only [Φ, Finsupp.sum]
    rw [LinearMap.sum_apply]
    rfl
  have h := (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ ha hb => GlobalTheory.OrientedHeis.theta_add ha hb) (fun a _ h => GlobalTheory.OrientedHeis.theta_smul a h)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) Φ
    (fun k g hg => ⟨?_, ?_⟩) x hx P).2
  · rw [hΦ, hΦ] at h
    exact h
  · exact GlobalTheory.AdTh.SourceBasis.aPlus_th hψ hθ _ _ _ hg
  · obtain ⟨τ, i, j⟩ := k
    simp only [aPlusAll]
    rw [hΦ, hΦ, Finsupp.sum, Finsupp.sum, (aPlus_sum hψ hθ τ _ _ c hg c.support).2]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [heisO_aPlus ψ hθ (hc u hu)]

end GlobalTheory.FiniteHeisComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdeleIdentificationNonemptyPresenta
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open Matrix
open scoped TensorProduct

namespace GlobalTheory.FinIsoProof

open GlobalTheory.DefU.ClassFin GlobalTheory.AdeleBaseChange

theorem nonempty_finIso (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : Nonempty (FinIso L n) := by
  obtain ⟨ι, hι⟩ := exists_toAd (maximalRealSubfield L) L
  let κ : AL L ≃+* FiniteAdeleRing (𝓞 L) L := RingEquiv.ofBijective ι ⟨map_injective hι, map_surjective hι⟩
  have hκ : ∀ x a, κ (x ⊗ₜ a) = algebraMap L _ x * adMap (maximalRealSubfield L) L a := hι
  have hc : ∀ y, κ (conjAL L y) = conjFin (cc L) (κ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul x a =>
      change κ ((IsCMField.complexConj L x) ⊗ₜ a) = _
      rw [hκ, hκ, map_mul, conjFin_adMap (cc L) (fun k => IsCMField.complexConj_apply_eq_self L k), conjFin_algebraMap]
      rfl
  have hc' : ∀ y, κ.symm (conjFin (cc L) y) = conjAL L (κ.symm y) := fun y => by
    rw [RingEquiv.symm_apply_eq, hc, RingEquiv.apply_symm_apply]
  let p : GAf L n →* GL (Fin n) (FiniteAdeleRing (𝓞 L) L) :=
    (GeneralLinearGroup.map κ.toRingHom).comp (ReciprocityTheory.Aut.GA L n).subtype
  have hp : ∀ x, Formalism.UG.cT (conjFin (cc L)) (p x).val * (p x).val = 1 := fun x =>
    unitary_map κ.toRingHom (conjAL L) (conjFin (cc L)) hc x.1.val (mul_eq_one_comm.mp x.2)
  let j : GAf L n →* UA L n := ((finGL L n).comp p).codRestrict (UA L n) fun x => finGL_mem_UA _ (hp x)
  refine ⟨⟨κ, map_tmul_one hι, ?_, j, fun x => MonoidHom.mem_ker.2 (pInf_finGL (p x)), ?_, ?_⟩⟩
  · intro w v h
    have hv : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext h
    subst hv
    refine ⟨locMap _ w, GlobalTheory.LFun.InertChart.continuous_complMap (rfl : w.under (𝓞 (maximalRealSubfield L)) = _), fun a => ?_⟩
    rw [hκ, map_one, one_mul]
    rfl
  · intro x w s t
    have h1 : (finGL L n (p x)).val.map (pFin L) = (p x).val := congrArg Units.val (pFin_finGL (p x))
    exact congrArg (pLoc L w) (congrFun₂ h1 s t)
  · intro y hy
    let z := GeneralLinearGroup.map (pFin L) y.1
    have hz : Formalism.UG.cT (conjFin (cc L)) z.val * z.val = 1 := cT_pFin y
    have hm : GeneralLinearGroup.map κ.symm.toRingHom z ∈ ReciprocityTheory.Aut.GA L n :=
      mul_eq_one_comm.mp (unitary_map κ.symm.toRingHom _ _ hc' z.val hz)
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    have e : p ⟨_, hm⟩ = z := Units.ext (Matrix.ext fun i k => κ.apply_symm_apply _)
    change finGL L n (p ⟨_, hm⟩) = _
    rw [e]
    exact finGL_pFin ⟨y, hy⟩

theorem finIso_nonempty : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), Nonempty (FinIso L n) :=
  fun L _ _ _ n => nonempty_finIso L n

end GlobalTheory.FinIsoProof
end
end

