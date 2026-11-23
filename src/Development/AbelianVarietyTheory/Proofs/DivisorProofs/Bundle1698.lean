module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0475
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeIntegratedOperatorRangesPolynomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1675
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0487
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubOrthProjPerpMem
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open scoped Matrix TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassSumIdentity

theorem sub_orthProj_perp_mem {K : Type} [Field K] [NumberField K] [StarRing K] {v0 : InfinitePlace K} (h0 : IsConjAt v0) {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} (hH : (H.map v0.embedding).PosDef) (N : Submodule K (Fin n → K)) (x : Fin n → K) :
    x - orthProj H (perpOf H N) x ∈ N := by
  have hd : ∀ Z : Submodule K (Fin n → K), Hᴴ = H ∧ IsUnit ((subE Z)ᴴ * H * subE Z).det := fun Z =>
    have k := orthogonal_projection_exists K v0 h0 _ _ H hH (subE Z) (subspace_image_spec K n Z).1
    ⟨k.1, k.2.2.1⟩
  have h1 : ∀ u y : Fin n → K, hform H u y = star u ⬝ᵥ H.mulVec y := fun u y => by
    simp [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, starRingEnd_apply, mul_assoc,
      mul_comm, mul_left_comm]
  have hs : ∀ u y : Fin n → K, hform H u y = 0 → hform H y u = 0 := fun u y e => by
    rw [h1] at e ⊢
    have := congrArg star e
    rwa [star_zero, ← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, (hd N).1, ← Matrix.dotProduct_mulVec] at this
  set y := x - orthProj H (perpOf H N) x
  have hy : y ∈ perpOf H (perpOf H N) := sub_orthProj_mem_perpOf H _ (hd _).2 x
  have hq : orthProj H N y ∈ N := orthProj_mem H N y
  have hw : y - orthProj H N y ∈ perpOf H N := sub_orthProj_mem_perpOf H _ (hd _).2 y
  have hw' : y - orthProj H N y ∈ perpOf H (perpOf H N) :=
    Submodule.sub_mem _ hy fun z hz => hs _ _ (hz _ hq)
  obtain ⟨a, ha⟩ := (subspace_image_spec K n (perpOf H N)).2.ge hw
  have h2 : ((subE (perpOf H N))ᴴ * H * subE (perpOf H N)).mulVec a = 0 := by
    funext i
    have := hw' _ ((subspace_image_spec K n (perpOf H N)).2.le ⟨Pi.single i 1, rfl⟩)
    rw [← ha, h1, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    simpa [← Pi.single_star] using this
  have h3 : a = 0 := by
    rw [← Matrix.one_mulVec a, ← Matrix.nonsing_inv_mul _ (hd (perpOf H N)).2, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]
  rw [h3, map_zero] at ha
  exact sub_eq_zero.1 ha.symm ▸ hq

theorem lvlE_lvlOp {K : Type} [Field K] [NumberField K] [StarRing K] {v0 : InfinitePlace K} (h0 : IsConjAt v0) (S : CSD K)
    (hH : (S.H.map v0.embedding).PosDef) {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms) (hr : S.ActGood r)
    (U : Subgroup G) (ψ : U →* Kˣ) (a : MonoidAlgebra K G) (ha : ∀ b, b * a = a * b) (x : Fin (S.lvlDim r U ψ) → K) :
    S.basis.equivFun.symm ((S.lvlE r U ψ).mulVec ((S.lvlOp r U ψ a).mulVec x)) =
      ∑ g, a.coeff g • r g (S.basis.equivFun.symm ((S.lvlE r U ψ).mulVec x)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mulVec_mulVec, (level_operator_spec K v0 h0 S hH G r hr U ψ a (ha _).symm).1, ← Matrix.mulVec_mulVec, CSD.gaMat,
    Matrix.sum_mulVec, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Matrix.smul_mulVec, map_smul]
  exact congrArg _ (Subtype.ext (action_matrix_spec K S G r g _))

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


open GlobalTheory.TraceIncl in
theorem classSum_eOp {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T0}
    {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ} (h : HidaSetting R i t) {θ} (hθ : OnTies.IsClassSum R i t U ψ ph θ)
    (c : G → D.what₂.LL) {x y : Fin (OnTies.srcDim A i t U ψ) → D.what₂.LL}
    (e : srcForm A i t U ψ y = ∑ g, c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x)) : θ y = (R.FW i).eOp c (θ x) := by
  rcases subsingleton_or_nontrivial (Fin (R.nW i) → D.what₂.LL) with hs | hs
  · exact Subsingleton.elim _ _
  refine h.eq_of_adForm fun v => ?_
  have e0 : adForm R i ((R.FW i).eOp c (θ x)) = ∑ g, adForm R i ((c g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (R.FW i).ρ g (θ x)) := by
    unfold adForm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Arith.FormsL.eOp_apply, map_sum, map_sum]
  have e4 : ∀ g, adForm R i ((c g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (R.FW i).ρ g (θ x)) (fun ρ => v ρ) =
      ph • (clSum (presV R i t) (kern R i t) (c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x))) v := fun g => by
    have e1 : adForm R i ((R.FW i).ρ g (θ x)) (fun ρ => v ρ) = sg0 D A ((R.FW i).chi g : D.what₂.LLˣ) •
        Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (adForm R i (θ x) fun ρ => v ρ) :=
      DFunLike.congr_fun ((h.unif i _).2.2 g (θ x)) _
    have e2 : clSum (presV R i t) (kern R i t) (A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v =
        Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)
          (clSum (presV R i t) (kern R i t) (srcForm A i t U ψ x) v) :=
      congrFun (h.clSum_equiv g (srcForm A i t U ψ x)) v
    have e3 : sg0 D A ((R.FW i).chi g : D.what₂.LLˣ) = D.what₂.embLL ((R.FW i).chi g : D.what₂.LLˣ) :=
      congrArg (fun s : D.what₂.LL →+* ℂ => s _) (sign_at_base_place_eq_embedding R)
    have e5 : clSum (presV R i t) (kern R i t) (c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v =
        D.what₂.embLL (c g) • clSum (presV R i t) (kern R i t) (A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v :=
      congrFun (LinearMap.map_smulₛₗ _ _ _) v
    have e6 : D.what₂.embLL (c g * (((R.FW i).chi g)⁻¹ : D.what₂.LLˣ)) * D.what₂.embLL ((R.FW i).chi g : D.what₂.LLˣ) =
        D.what₂.embLL (c g) := by rw [← map_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [e5, e2, adForm_smul, MultilinearMap.smul_apply, e1, e3, h.adForm_theta hθ, smul_smul, e6, LinearMap.map_smul, smul_comm]
  have e7 : clSum (presV R i t) (kern R i t) (srcForm A i t U ψ y) v =
      ∑ g, clSum (presV R i t) (kern R i t) (c g • A.leftGroupActionLift i t g (srcForm A i t U ψ x)) v :=
    (congrArg (fun f => clSum (presV R i t) (kern R i t) f v) e).trans
      ((congrFun (map_sum (clSum (presV R i t) (kern R i t)) _ _) v).trans (Finset.sum_apply _ _ _))
  refine (h.adForm_theta hθ y v).trans (((congrArg (fun F => ph • F) e7).trans Finset.smul_sum).trans (Eq.symm ?_))
  exact (DFunLike.congr_fun e0 _).trans ((MultilinearMap.sum_apply _ _ _).trans (Finset.sum_congr rfl fun g _ => e4 g))

section Comparison₂

attribute [local instance 2000] Submodule.module

variable {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (OnTies.srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}

theorem identity_of_tie (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y)
    (hS : GlobalTheory.TraceIncl.HidaSetting R ι (R.mu v)) {s : ℕ} (hOk : A.fam.Ok s) (hr : ClassSumRational R ι (R.mu v) U ψ ph) :
    O.θ' v i ∘ₗ O.eX v i = O.e i ∘ₗ O.θ' v i ∧
      ∀ x ∈ LinearMap.range (O.eX v i), x - O.pr v i x ∈ LinearMap.ker (O.θ' v i) := by
  have hθy : ∀ x, (toForms h fw ι z ∘ₗ O.θ' v i ∘ₗ y.symm.toLinearMap) (y x) = toForms h fw ι z (O.θ' v i x) := fun x =>
    congrArg (fun a => toForms h fw ι z (O.θ' v i a)) (y.symm_apply_apply x)
  refine ⟨LinearMap.ext fun x => (toForms_bijective h fw ι z).1 ?_, fun x _ => ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, t.e_eOp, ← hθy, ← hθy]
    refine classSum_eOp hS (t.θ'_eq hr) _ ?_
    refine (congrArg (srcForm A ι (R.mu v) U ψ) (LinearMap.congr_fun t.eX_eq x)).trans ?_
    exact lvlE_lvlOp hOk.conj (A.MtCSD ι (R.mu v)) ((hOk.lifts ι (R.mu v)).hpos _) (A.leftGroupActionLift ι (R.mu v)) hS.act U ψ _
      (idempotent_central _ _ A.X hOk.irr).2 (y x)
  · have hpos : (((A.MtCSD ι (R.mu v)).lvlH (A.leftGroupActionLift ι (R.mu v)) U ψ).map A.v0.embedding).PosDef :=
      BlockDat.lf_lvlH_pos (B := A.fam.L ι (R.mu v)) (ℓ := ⟨A.X, U, ψ⟩) ⟨hOk.conj, hOk.irr, hOk.lifts ι (R.mu v)⟩ A.v0
    obtain ⟨a, ha, e⟩ := sub_orthProj_perp_mem hOk.conj hpos ((LinearMap.ker (O.θ' v i)).map y.toLinearMap) (y x)
    have e' : y a = y (x - O.pr v i x) :=
      e.trans ((congrArg (fun b => y x - b) (LinearMap.congr_fun t.pr_eq x).symm).trans (y.map_sub _ _).symm)
    exact y.injective e' ▸ ha

end Comparison₂


attribute [local instance] GlobalTheory.BigOn.runAlg' in
theorem leafIdentity_of_isRec : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ s : ℕ, A.fam.Ok s → R.Char F → R.LUnif → TwistedRational R F (fun _ => 1) → LeafIdentity O := by
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hO s hOk hC hU hrat
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hO.tied
  have key : ∀ v j, ClassSumRational R j (R.mu v) F.P0 F.ψ0⁻¹ 1 →
      O.θ' v j ∘ₗ O.eX v j = O.e j ∘ₗ O.θ' v j ∧
        ∀ x ∈ LinearMap.range (O.eX v j), x - O.pr v j x ∈ LinearMap.ker (O.θ' v j) := fun v j hr =>
    identity_of_tie (T := (r.used v).full) (inst := inst) (R := R) (ht v j).1
      ⟨hC.lev, hC.grp.red_L, hC.fam.tie, hC.models, hC.thP, hU, ⟨_, (fw.hv₀ j _).1⟩, (hOk.lifts _ _).act,
        _root_.GlobalTheory.VecInv.omega_lifts_vP R hC.lev hC.models.inf hC.thP.ωP hC.thP.vP j (R.mu v)⟩ hOk hr
  exact fun w hw => ⟨fun j => key w j (hrat w hw j), fun j => key _ j (by rw [hC.tup.mu_conj w]; exact hrat w hw j)⟩

end GlobalTheory.ClassSumIdentity
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumInnerIntegralEq
section
noncomputable section

open MeasureTheory GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.Pc3

theorem sum_inner_integral_eq {X U ι : Type} [MeasurableSpace X] [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [CompleteSpace U] [Fintype ι] (ν : Measure X) (f : X → ℂ) (ρ : X → U →L[ℂ] U) (e : ι → U) (T : U →L[ℂ] U)
    (h : ∀ v, Integrable (fun x => f x • ρ x v) ν ∧ T v = ∫ x, f x • ρ x v ∂ν) :
    ∑ j, ⟪e j, T (e j)⟫_ℂ = ∫ x, f x * ∑ j, ⟪e j, ρ x (e j)⟫_ℂ ∂ν := by
  have h1 : ∀ j, ⟪e j, T (e j)⟫_ℂ = ∫ x, ⟪e j, f x • ρ x (e j)⟫_ℂ ∂ν := fun j => by
    rw [(h (e j)).2, integral_inner (h (e j)).1]
  simp only [h1]
  rw [← integral_finsetSum _ fun j _ => (h (e j)).1.const_inner (e j)]
  simp only [inner_smul_right, Finset.mul_sum]

theorem stTr_of_range_steps (hF : UFin) (hS : RangeShape) (hK : RangeK) (hT : TraceSum) : StTr := by
  intro n ε μ _ U _ _ _ π hπ hirr d
  obtain ⟨L, hL, hmem, -⟩ := hF n ε U π hπ hirr d
  refine ⟨fun g => ∑ j, ⟪(stdOrthonormalBasis ℂ L j : U), π g (stdOrthonormalBasis ℂ L j : U)⟫_ℂ, ?_, ?_, ?_⟩
  · exact continuous_finsetSum _ fun j _ => continuous_const.inner (hπ.continuous_apply _)
  · intro φ hφ
    obtain ⟨hop, hr⟩ := hS n ε μ U π hπ d φ hφ
    have := hT U L _ fun u => hmem _ (hr u).1
    rwa [sum_inner_integral_eq μ (fun g => φ (toM g)) (fun g => π g) _ _ hop] at this
  · intro P hP
    obtain ⟨B, hB, hr⟩ := hK n ε U π hπ P
    refine ⟨B, fun v => (hB v).2, ?_⟩
    have := hT U L B fun u => hmem _ fun l => by
      obtain ⟨Q, hQ, hQ'⟩ := hr u l
      exact ⟨Q, hQ.trans hP, hQ'⟩
    rwa [sum_inner_integral_eq (muK ε) (fun k : KG ε => ev (toMK k) P) (fun k : KG ε => π k) _ _ hB] at this

theorem stTr : StTr := stTr_of_range_steps _root_.GlobalTheory.PsCo.Pc3.uFin _root_.GlobalTheory.PsCo.Pc3.rangeShape rangeK GlobalTheory.OpTrace.hasTrace_sum_inner_of_range_le

end GlobalTheory.PsCo.Pc3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeightRpowParabolicCosets
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem summable_height_rpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), Submodule.IsFullLattice E L → (∀ g : GAd σ J, ∃ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 ∧ ∃ k ∈ levelAll σ J L a, g = p * k) → ∀ h : GAd σ J → ℝ≥0, (∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det β)) → ∀ (g : GAd σ J) (t : ℝ), (n : ℝ) - j < t → Summable fun q : GlobalTheory.Eis.Cosets (parFlag σ J C (fun _ => 0)) (ratPts σ J) => (h ((q.out : ratPts σ J) * g) : ℝ) ^ t := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF L a hL hI h hh g t ht
  let _ : Submodule.IsFullLattice E L := hL
  obtain ⟨lv, hlv⟩ := _root_.GlobalTheory.SphEis.exists_isLv F E σ n J j m C D Z J₀ hF
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := GlobalTheory.Doubling.isCompact_levelAll hF.cm J L a
  choose p β hp k hk e using fun q : GlobalTheory.Eis.Cosets (parFlag σ J C (fun _ => 0)) (ratPts σ J) =>
    hI ((q.out : ratPts σ J) * g)
  have h1 := _root_.GlobalTheory.SphEis.Summ.summable_absDet F E σ n J j m C D Z J₀ hF lv hlv _
    (fun q : GlobalTheory.Eis.Cosets (parFlag σ J C (fun _ => 0)) (ratPts σ J) => (q.out : ratPts σ J)) p
    (fun q => k q * g⁻¹) β _ (hK.image (continuous_mul_const g⁻¹)) (fun q => q.out.2)
    (fun q => (eq_mul_inv_of_mul_eq (e q)).trans (mul_assoc _ _ _)) (fun q => ⟨k q, hk q, rfl⟩) hp
    (fun q q' hq => ?_) t (by
      have h2 : (m : ℝ) + 2 * j = n := by exact_mod_cast hF.dim
      push_cast
      linarith)
  · refine h1.congr fun q => ?_
    rw [e, hh _ _ (hp q) _ (hk q)]
  · rw [← q.out_eq, ← q'.out_eq]
    exact GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨q'.out * q.out⁻¹, Subgroup.mem_subgroupOf.2 hq⟩, inv_mul_cancel_right _ _⟩

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharacterQuotientNotUnramifiedOverBaseP
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ThetaGridRamifiedOverBasePlace

theorem thetaGridCharacterQuotient_not_unramified_over_basePlace : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = G.pl.v0 →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  intro D T L sc G μ₀ hL t i j w hv
  rw [show alpha G t i j / beta G i j = G.nu t i (j + 1) from mul_div_mul_right_eq_div _ _ _,
    GlobalTheory.LFun.unrAt_iff_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL) w]
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have hchi : ¬ (G.ch.chiH (D.R.m - i)).UnrAt w := (G.ch.lev0 _ hm.1 hm.2 _ hv).2
  have hmu : (L.C.mu0 j).UnrAt w := (L.C.isMu0 j).unr _ fun k hk => G.ch.basePlace_not_mem_chiGridBadPlaces (by
    have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
      rw [map_natCast]; exact hk
    rw [hv] at h
    refine (S1_mem_OmF D).2 ?_
    fin_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have hxi : (L.xiH t).UnrAt w := by
    by_contra hc
    rcases (hL.Q_ram t _).1 hc with h | ⟨PP', h, hc'⟩
    · exact G.pl.levelPlace_ne_basePlace t _ h hv
    · exact G.pl.levelPlace_ne_basePlace t PP' h ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc').trans hv)
  intro hn
  apply hchi
  have e : G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH t / SqNum.nuH G t i j := by
    rw [SqNum.nuH, div_div_cancel]
  rw [e, div_eq_mul_inv]
  exact (hmu.mul hxi).mul hn.inv

end GlobalTheory.ThetaGridRamifiedOverBasePlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIoExtensionOfWeakCharacterisationFrames
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IoExtStd

theorem thetaIoExtension_of_weakCharacterisation_frames : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ i, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧ (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)) → IoExt R.toRealDat := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hC hE hF
  have hB := GlobalTheory.OneMapBridge.heckeChoiceClauses_of_weakCharacterisation_at_face D G Pl0 I0 T0 A3 Ks R F hC hE
  have hcore := hB.1
  have hsh := GlobalTheory.DefLift.holShape_fixed D G Pl0 T0 A3.A Ks R.toRealDat hcore.models.order
  exact GlobalTheory.AdTh.IoExtCore.ioExt_core D G Pl0 T0 A3.A Ks R.toRealDat F.lv2 hcore
    (fun i => GlobalTheory.StdFrame.vStd_of_orthonormal_span D i (hF i))
    (fun i => ⟨GlobalTheory.LowSmooth.lowSm_MW D G Pl0 T0 A3.A Ks R.toRealDat i _,
      GlobalTheory.HolLowOnce.extLine_of_holShape D _ _ _ (hsh i).1⟩)

end GlobalTheory.IoExtStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEqClassSumThetaKernelsLowestKType
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftUnfoldCore


set_option maxHeartbeats 1000000 in
theorem thF_eq_classSum_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (K' : Type) [Field K'] (σ' : K' →+* ℂ) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)) (bad : ℕ) (J' : Subgroup (Bridge.Gf (Vc D i))) (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K'), VStd D i → RepsR R i t h bad J' Lh gam vol → ∀ (y : (R.HV i t).H) (x : Cl → VsV D i K'), Place R i t h c0' y x → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)), R.thF i t y (fun ρ => u ρ) g = ∑ k, σ' (vol * ((gam k : K'))⁻¹) * thetaKO (R.ωP i t) (h k) g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) (c0' (x k)))) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i t K' _ σ' c0' Cl _ h bad J' Lh gam vol hV hrep y x hpl u g
  refine (hR.thP.thF i t).elim fun thP hPF => ?_
  have hle := hrep.2.2.1
  have hN := hrep.2.2.2.1
  have hvol := hrep.2.2.2.2.1
  have hy := hrep.2.2.2.2.2.1
  have hk := hrep.2.2.2.2.2.2
  have hx : (R.HV i t).e y ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hR.models.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hfin : ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ levJ R i t, ∀ P, R.ωP i t (k, 1) (R.ptP i t P) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.ptP i t P := fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hR.models.inf
      (hR.thP.ωP i t) _ _ _ _ _ (hR.thP.pt_theta i t) k hk 1 (one_mem _) _
      (GlobalTheory.AdTh.LevelLawCore.omega_level_vP_core D G Pl0 T0 A Ks R F hR i t k hV hk hk')
  have key := GlobalTheory.LiftUnfold.integral_theta (hR.thP.ωP i t) (D.sp.V_sig _) (hR.models.vpos i) (R.cV i) (hR.models.cV i) (R.βV i)
    (R.datVt i t) (fun _ => Iff.rfl) hx
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u)) (fun w => hR.thP.pt_theta i t _)
    (fun a ha w => (hR.thP.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hR.models.νV i t) J' Cl h hle hN hy (fun k => (hk k).1.1) g
  have h1 := congrFun (hPF.2 y u) g
  have h2 := hPF.1.eq ((R.extV i t).rangeRestrict y) (PiTensorProduct.tprod ℂ u) g
  refine h1.trans (h2.trans (Eq.trans ?_ (key.trans (Finset.sum_congr rfl fun k _ => ?_))))
  · rfl
  have h3 : σ' (vol * ((gam k : K'))⁻¹) = ((J'.relIndex (levJ R i t) : ℕ) : ℂ)⁻¹ *
      ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) J' (fin (Vc D i) (h k))) : ℕ) : ℂ)⁻¹ := by
    rw [map_mul σ', hvol, map_inv₀ σ', map_inv₀ σ', map_natCast σ', map_natCast σ', (hk k).2.2]
  rw [h3, ← hpl k]
  rfl

end GlobalTheory.LiftUnfoldCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLevelLiftsLowestKType
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaShift

open GlobalTheory.ThetaProjEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem smul_apply_of_eq {H W : Type} [AddCommGroup W] [Module ℂ W] (c : ℂ) (hc : c ≠ 0) (f : H → W) (h : H) (w : W)
    (hw : f h = c⁻¹ • w) : (c • f) h = w := by
  rw [Pi.smul_apply, hw, smul_inv_smul₀ hc]

theorem pt_shift (R : RealDat D A Ks) (hM : R.IsModels) (hP : R.IsThP) (i : Fin D.R.m) (t : T0)
    (κ : GA D (Vc D i)) (κ' : GA D (Wc D i)) (hκ : κ ∈ GfC (Vc D i)) (hκ' : κ' ∈ GfC (Wc D i)) (a : ℂ)
    (hv : R.ωP i t (κ, κ') (R.vP i t) = a • R.vP i t) :
    ∀ P, R.ωP i t (κ, κ') (R.ptP i t P) = a • R.ptP i t P :=
  GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hM.inf (hP.ωP i t) _ _ _ _ _
    (hP.pt_theta i t) κ hκ κ' hκ' a hv

theorem thF_shift_of_eigen (R : RealDat D A Ks) (hM : R.IsModels) (hP : R.IsThP) (i : Fin D.R.m) (t : T0)
    (g0 : G0 R.Pg D.R.r)
    (κ : GA D (Vc D i)) (κ' : GA D (Wc D i)) (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ)
    (y y' : (R.HV i t).H) (c : ℂ) (hc0 : c ≠ 0)
    (hpt : ∀ P, R.ωP i t (κ, κ') (R.ptP i t P) = c⁻¹ • R.ptP i t P)
    (hy : ∀ h, (c • R.extV i t y') h = R.extV i t y (h * κ))
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : GA D (Wc D i)) :
    R.thF i t y' (fun ρ => v ρ) x = R.thF i t y (fun ρ => v ρ) (x * κ') := by
  refine (hP.thF i t).elim fun thP hPF => ?_
  have hker := fun P => GlobalTheory.thetaKO_rat_left_and_eigen_right R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) (hP.ωP i t)
    (R.ptP i t P) (hP.pt_theta i t P)
  have hm := thetaLift_shift hPF.1 (GQ (Vc D i)) κ κ' c hc0
    (integral_shift (Vc D i) (R.βV i) (R.datVt i t) g0 κ hκ (R.νV i t) (hM.νV i t).1.1 (R.fdV i t)
      (hM.νV i t).2)
    (fun P γ hγ g h => by
      have := (hker P).1 γ hγ 1 (GQ (Wc D i)).one_mem h g
      rwa [one_mul] at this)
    (fun P g h => (hker P).2 κ κ' c⁻¹ (hpt P) h g)
    ((R.extV i t).rangeRestrict y) ((R.extV i t).rangeRestrict y')
    (extV_left R hM.HV i t y)
    hy
    (PiTensorProduct.tprod ℂ v) x
  exact (congrFun (hPF.2 y' v) x).trans (hm.trans (congrFun (hPF.2 y v) (x * κ')).symm)

theorem thF_shift_of_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ y y' : (R.HV i t).H, (∀ h, R.extV i t y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : GA D (Wc D i)), R.thF i t y' (fun ρ => v ρ) x = R.thF i t y (fun ρ => v ρ) (x * κ') := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hlev hM hP i t g0 κ κ' hκ hκ' y y' hy v x
  have hc0 := levChi_ne_zero (V := Vc D i) (β := R.βV i) (flagL (R.datVt i t)) κ
  exact thF_shift_of_eigen R hM hP i t g0 κ κ' hκ y y' (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ) hc0
    (pt_shift R hM hP i t κ κ' hκ.1 hκ'.1 _ (_root_.GlobalTheory.VecInv.omega_lifts_vP R hlev hM.inf hP.ωP hP.vP i t g0 κ κ' hκ hκ'))
    (fun h => smul_apply_of_eq _ hc0 _ h _ (hy h)) v x

end GlobalTheory.ThetaShift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFiniteStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_factorizable_restriction_finite : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl (F := F))) (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w, w ∉ S → φ w = G.M'.vac w) →
    ∀ (m : ℕ) (f' : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ' : Fin m → ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ i w, φ' i w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ i w, w ∉ S → φ' i w = G.M'.vac w) →
    (∀ u : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ t : AF F, evI F t = 0 → (∀ w ∈ S, evFin F w t = 0) → t • u = 0) →
      ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → AF F) (borel _),
        @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        (@MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x =>
            (∑ i, pure (f' i) (φ' i)) x * starRingEnd ℂ (G.M'.co.rho B.ψ u (∑ i, pure (f' i) (φ' i)) x)) =
          @MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x => pure f φ x * starRingEnd ℂ (G.M'.co.rho B.ψ u (pure f φ) x)) →
    ∃ c : ℂ, ∑ i, pure (f' i) (φ' i) = c • pure f φ := by
  first | exact @GlobalTheory.SplitSvN.scalar_of_coeff | exact GlobalTheory.SplitSvN.scalar_of_coeff | (intros; apply GlobalTheory.SplitSvN.scalar_of_coeff <;> assumption)
end

