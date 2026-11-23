module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0983
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianActionColumnBase
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocFrame
open GlobalTheory.EmbChart (idem)
open GlobalTheory.StepData (LatFrame)
open GlobalTheory.RootEx (colE rowE)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (schT schM)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SrcHalfOne
open GlobalTheory.EmbChart (tensAt atPlace)
open GlobalTheory.AdelicU (splitProj compFin isCMExt_host)
variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem cA_cA' (z : AE D) : cA D (cA D z) = z := Formalism.L2.Theta.cA_cA z
theorem cA_alg (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
  rw [map_one]; rfl

theorem compFin_cA (z : AE D) : compFin D.host.F D.host.E v (cA D z) = sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

variable (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem piW_cA_idem : piW τ (cA D (idem τ)) = 0 :=
  ((chart_piW τ).2.1 _).2 (GlobalTheory.EmbChart.isSplitIdem_idem τ).2.1

theorem piW_idem : piW τ (idem τ) = 1 := by
  change splitProj τ (compFin _ _ v (idem τ)) = 1
  rw [GlobalTheory.EmbChart.compFin_idem, GlobalTheory.AdelicU.splitProj_splitIdem]

theorem piW_alg (a : Fv D.host.F v) : piW τ (algebraMap (AF D.host.F) (AE D) (atPlace v a)) = a := by
  rw [(chart_piW τ).2.2.1]
  exact GlobalTheory.AdelicU.evalV_singleFin_self v a

theorem piW_cA (z : AE D) : piW τ (cA D z) = splitProj (τ.comp D.sp.cm.sig) (compFin D.host.F D.host.E v z) := by
  change splitProj τ (compFin _ _ v (cA D z)) = _
  rw [compFin_cA, GlobalTheory.AdelicU.splitProj_comp]

def plcC (y : Fv D.host.F v) : AE D := cA D (idem τ) * algebraMap (AF D.host.F) (AE D) (atPlace v y)

theorem piW_plcC (y) : piW τ (plcC τ y) = 0 := by rw [plcC, map_mul, piW_cA_idem, zero_mul]
theorem piW_cA_plcC (y) : piW τ (cA D (plcC τ y)) = y := by
  rw [plcC, map_mul, cA_cA', cA_alg, map_mul, piW_idem, piW_alg, one_mul]

theorem idem_mul_self : idem τ * idem τ = idem τ := (GlobalTheory.EmbChart.isSplitIdem_idem τ).1

section Frame

variable (V : HSp D) {ι : Type} [Fintype ι] [DecidableEq ι] (β : LatFrame (Fv D.host.F v) ι (Fin V.rank))

end Frame

section FJ

variable {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ (σ + 1)) {n : Type} [Fintype n] [DecidableEq n]
  {γ : LatFrame (Fv D.host.F v) n (Fin V₀.rank)} {β : LatFrame (Fv D.host.F v) (n ⊕ Fin (2 * (σ + 1))) (Fin V.rank)}
  {t : ℕ → Fv D.host.F v}

variable {τ}

open GlobalTheory.RootEx (colE rowE)

variable (hβ : IsScaled V V₀ τ d.i₀ (fourierJacobiVectors d) γ β t)
include hβ

end FJ

section Jac

variable {V V₀ L : HSp D} {σ : ℕ} (d : HypDec V V₀ (σ + 1)) (ζ : Fin L.rank → D.host.E)

end Jac
end GlobalTheory.SrcHalfOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqZeroOfMemRangeAdjoint
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar

theorem ker_le_span_of_rel {K X Y H W : Type} [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y]
    [Module K Y] [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (j : X →ₛₗ[σ] H)
    (jW : Y →ₛₗ[σ] W) (T : H →ₗ[ℂ] W) (Rel : X → Y → Prop) (hex : ∀ x, ∃ y, Rel x y)
    (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (hind : ∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k))
    (hT : ∀ x y, Rel x y → jW y = T (j x)) :
    LinearMap.ker T ≤ Submodule.span ℂ (j '' {u | Rel u 0}) := by
  have hinj : Function.Injective jW := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    by_contra h0
    exact (hind 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hx
  choose f hf using hex
  have e : ∀ x, jW (f x) = T (j x) := fun x => hT x _ (hf x)
  let θ : X →ₗ[K] Y :=
    { toFun := f
      map_add' := fun x y => hinj (by rw [map_add (f := _), e, e, e, map_add (f := _), map_add (f := _)])
      map_smul' := fun a x => hinj (by rw [RingHom.id_apply, map_smulₛₗ, e, e, map_smulₛₗ, map_smul]) }
  refine (GlobalTheory.ker_le_span_image_ker_of_semilinear K X Y H W σ θ j jW T hsp hind fun x => (e x).symm).trans
    (Submodule.span_mono (Set.image_mono fun u hu => ?_))
  have h0 : f u = 0 := hu
  exact h0 ▸ hf u

theorem mem_orthogonal_of_le_span {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {N : Submodule ℂ H} {s : Set H}
    (h : N ≤ Submodule.span ℂ s) {v : H} (hv : ∀ u ∈ s, ⟪v, u⟫_ℂ = 0) : v ∈ Nᗮ := by
  refine Submodule.orthogonal_le h ((Submodule.mem_orthogonal' _ _).2 fun u hu => ?_)
  induction hu using Submodule.span_induction with
  | mem u hu => exact hv u hu
  | zero => exact inner_zero_right _
  | add u u' _ _ h h' => rw [inner_add_right, h, h', add_zero]
  | smul a u _ h => rw [inner_smul_right, h, mul_zero]

theorem toF_mem {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z y ∈ Z := by
  obtain ⟨f, hf, e⟩ : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := (subspace_image_spec _ _ _).2.le ⟨y, rfl⟩
  have : B.toF ℓ Z y = f := (congrArg B.S.basis.equivFun.symm e.symm).trans (B.S.basis.equivFun.symm_apply_apply f)
  exact this ▸ hf

theorem inner_eq_zero_of_mem_range_adjoint {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (T : H →ₗ[ℂ] W) {a b : H}
    (ha : a ∈ LinearMap.range (LinearMap.adjoint T)) (hb : T b = 0) : ⟪a, b⟫_ℂ = 0 := by
  obtain ⟨w, rfl⟩ := ha
  rw [LinearMap.adjoint_inner_left, hb, inner_zero_right]

theorem mem_orthogonal_of_rel {K X Y H W : Type} [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y]
    [Module K Y] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ)
    (j : X →ₛₗ[σ] H) (jW : Y →ₛₗ[σ] W) (th : H →ₗ[ℂ] W) (U : W ≃ₗᵢ[ℂ] W) (κ : ℂ) (g : W →ₗ[ℂ] W) (Rel : X → Y → Prop)
    (hex : ∀ x, ∃! y, Rel x y) (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (hind : ∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k))
    (hT : ∀ x y, Rel x y → U (jW y) = κ • g (th (j x))) {v : H} (hv : ∀ u, Rel u 0 → ⟪v, j u⟫_ℂ = 0) :
    v ∈ (LinearMap.ker th)ᗮ := by
  have hk := ker_le_span_of_rel σ j jW ((U.symm.toLinearEquiv.toLinearMap ∘ₗ (κ • g)) ∘ₗ th) Rel (fun x => (hex x).exists) hsp
    hind (fun x y h => U.toLinearEquiv.eq_symm_apply.2 (hT x y h))
  refine mem_orthogonal_of_le_span ((LinearMap.ker_le_ker_comp _ _).trans hk) ?_
  rintro _ ⟨u, hu, rfl⟩
  exact hv u hu

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem csum_eq_zero_of_adjoint (h1 : R.models_HV) (h2 : R.models_jV) (i : Fin D.R.m) (t : T0) {f g : A.fam.amb.FL i t}
    (hf : R.jV i t f ∈ LinearMap.range (LinearMap.adjoint (R.thG i t))) (hg : R.thG i t (R.jV i t g) = 0) :
    (A.fam.L i t).S.csum f.1 g.1 = 0 := by
  have h3 : inner ℂ (R.jV i t f) (R.jV i t g) = D.what₂.embLL ((A.fam.L i t).S.csum f.1 g.1) := by
    refine ((h1 i t).2.2 (R.jV i t f) (R.jV i t g)).trans ?_
    refine (congrArg₂ (Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y)
      (h2 i t f) (h2 i t g)).trans ?_
    exact GlobalTheory.PresBasic.isom (R.B.L i t).pres f g
  exact (map_eq_zero _).1 (h3.symm.trans (inner_eq_zero_of_mem_range_adjoint _ hf hg))

end


set_option maxHeartbeats 1600000 in
theorem conjForms_mem_orthogonal_ker : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → R.LUnif → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), ∀ ph : ℂ, ph ≠ 0 → (∀ x, ∃! y, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph x y) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.ConjAt R i σ ph (c0L i) → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th → ∀ (ℓ : Lvl D.what₂.LL G) (Z : Submodule D.what₂.LL (A.fam.L i A.μ0).S.Forms), Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A.fam.L i A.μ0).HZ ℓ Z) ((A.fam.L i A.μ0).XQ ℓ Z) → (∀ a k, (A.fam.L i A.μ0).fE ℓ Z a k ∈ Formalism.DivisionValues.cmMax D.what₂.LL) → (∀ z ∈ Z, R.jV i A.μ0 z ∈ LinearMap.range (LinearMap.adjoint (R.thG i A.μ0))) → ∀ x, j ((A.fam.L i A.μ0).toF ℓ Z x) ∈ (LinearMap.ker th)ᗮ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hM hU gramR c0R c0L hT i σ c c₁ H j μ' η' th ph hph hex hC hD ℓ Z hH hE hZ x
  obtain ⟨-, -, u, U, z, ζ, -, -, -, hall⟩ := hC
  obtain ⟨-, κ, -, hκ⟩ := hall μ' η' c c₁ H j th hD
  have hsp := GlobalTheory.ConjSpan.span_conjForms R hM.jV gramR c0R c0L hT i σ c c₁ H j hD.2.2.1
  have : FiniteDimensional D.what₂.LL (A.fam.amb.FL i A.μ0) := Module.Finite.of_basis (A.fam.L i A.μ0).S.basis
  refine mem_orthogonal_of_rel σ j ((R.FW i).j σ) th U κ (R.gW i σ z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R i ph) hex hsp (hU i σ).1
    hκ fun v hv => ?_
  have h0 : R.thG i A.μ0 (R.jV i A.μ0 v) = 0 :=
    (smul_eq_zero.1 ((map_zero _).symm.trans hv).symm).resolve_left hph
  refine (GlobalTheory.LiftLower.inner_conjForms_eq_csumAt R hM.jV gramR c0R c0L hT i σ c c₁ H j hD.2.2.1 _ v).trans ?_
  exact (GlobalTheory.Proof.ConjugateTransposeMajorant.majAt_eq_csumAt (A.fam.L i A.μ0) ℓ Z hH hE).2 v
    (fun y => csum_eq_zero_of_adjoint hM.HV hM.jV i A.μ0 (hZ _ (toF_mem _ ℓ Z y)) h0) σ x

end GlobalTheory.ConjScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacuumAtReframeFunctionOnHoms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec.FockVac

variable {D : D7}

theorem continuous_reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : Continuous (reW S T b) := by
  unfold reW
  exact Continuous.matrix_mul continuous_id continuous_const

theorem compAt_frPinv {θ : InfFam D} (hθ : IsInfFam θ) (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (τ : D.what₂.Tau) : compAt θ τ ((frPinv S b).map (incA D)) = (frPinv S b).map (tauE D τ) := by
  unfold compAt
  rw [Matrix.map_map]
  congr 1
  funext e
  exact GlobalTheory.FockCompare.comp_incA hθ τ e

theorem lineAt_reW {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    reW S T b (lineAt θ τ z t) = lineAt θ τ (z * (frPinv S b).map (tauE D τ)) t := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  let R : WO (reS S b) T →+ WO S T := AddMonoidHom.mk' (reW S T b) (fun x y => Matrix.add_mul x y _)
  let L : ℝ →+ WO S T := R.comp (lineAt θ τ z)
  have hL' : IsLineAt θ τ (z * (frPinv S b).map (tauE D τ)) L := by
    refine ⟨(continuous_reW S T b).comp hL.1, fun t => ?_, fun t τ' => ?_⟩
    · show (reW S T b (lineAt θ τ z t)).map (finPart D) = 0
      unfold reW
      rw [Matrix.map_mul, hL.2.1, Matrix.zero_mul]
    · show compAt θ τ' (reW S T b (lineAt θ τ z t)) = _
      unfold reW
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2, compAt_frPinv hθ]
      split_ifs with h
      · subst h
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _) hL']
  rfl

theorem lineAt_reW' {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin (reS S b).rank) ℂ) (t : ℝ) :
    reW S T b (lineAt θ τ z t) =
      lineAt θ τ (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) ℂ) z ((frPinv S b).map (tauE D τ))) t :=
  lineAt_reW hθ S T b τ z t

theorem dRho_reF (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D)
    (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (hs : ∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y))
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin (reS S b).rank) ℂ) (f : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ (reS S b) T) θ τ z (reF S T b f) =
      reF S T b (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ
        (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) ℂ) z ((frPinv S b).map (tauE D τ))) f) := by
  funext x
  rw [reF_apply]
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [← lineAt_reW' hθ]
  have hadd (u v : WO (reS S b) T) : reW S T b (u + v) = reW S T b u + reW S T b v :=
    Matrix.add_mul _ _ _
  simp only [heisO, reF_apply, symplOH, hs, hadd]

theorem isFockVacAt_reF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (b : Module.Basis (Fin S.rank) D.host.E S.V), IsInfFam θ →
    (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) →
    ∀ (τ : D.what₂.Tau) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ),
      IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 sT) f → IsFockVacAt (heisO ψ (reS S b) T) θ τ (cplxO 1 sT) (reF S T b f) := by
  intro D ψ θ S T b hθ hs τ sT f hf z
  let P' : Matrix (Fin S.rank) (Fin S.rank) ℂ := (frPinv S b).map (tauE D τ)
  let z' : Matrix (Fin T.rank) (Fin S.rank) ℂ := z
  have hJ : HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) ℂ) (cplxO 1 sT z) P' = cplxO 1 sT (z' * P') := by
    show Complex.I • (sT * z' * 1) * P' = Complex.I • (sT * (z' * P') * 1)
    rw [Matrix.mul_one, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc]
  funext x
  have h0 : Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z' * P') f (reW S T b x) +
      Complex.I • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO 1 sT (z' * P')) f (reW S T b x) = 0 :=
    congrFun (hf (z' * P')) (reW S T b x)
  rw [← hJ] at h0
  have e1 := congrFun (dRho_reF ψ hθ S T b hs τ z f) x
  have e2 := congrFun (dRho_reF ψ hθ S T b hs τ (cplxO 1 sT z) f) x
  refine (congrArg₂ (fun a c : ℂ => a + Complex.I • c) e1 e2).trans ?_
  exact h0

end GlobalTheory.AdSpan.ReVec.FockVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFrameFrameChangeInverseGLMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem hatL_mulVec_mem (M : Matrix (Fin n) (Fin n) E) (Λ Λ' : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ y ∈ Λ, M *ᵥ y ∈ Λ') (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hx : x ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    M.map (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] Formalism.L2.Herm.Af F) *ᵥ x ∈
      Formalism.L2.Herm.hatL (F := F) Λ' := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at *
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨M *ᵥ z, h z hz, ?_⟩
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, Formalism.UG.inclE, map_sum]
  | zero => simp
  | add y z _ _ hy hz =>
    rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [Subring.smul_def, Matrix.mulVec_smul]
    exact Submodule.smul_mem _ c hy

end General

theorem sum_smul_frame_frP {D : D7} (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (y : Fin S.rank → D.host.E) :
    ∑ i, y i • b i = ∑ j, (frP S b *ᵥ y) j • S.frame j := by
  simp only [frP, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [← S.frame.sum_repr (b i), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, mul_comm]

theorem mem_stdL_iff {D : D7} (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (hO : StdFrame.OrthFrame (reS S b)) (y : Fin S.rank → D.host.E) :
    y ∈ stdL D.host.E S.rank ↔ ∑ i, y i • b i ∈ S.L0 := by
  have hpi : (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) =
      stdL D.host.E S.rank := by
    apply le_antisymm
    · intro x hx
      rw [← Finset.univ_sum_single x]
      refine Submodule.sum_mem _ fun a _ => ?_
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hx a trivial)
      have : (Pi.single a (x a) : Fin S.rank → D.host.E) = c • (Pi.single a 1 : Fin S.rank → D.host.E) := by
        rw [← Pi.single_smul, ← hc, Algebra.smul_def, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩ j -
      by_cases h : j = a
      · subst h
        exact Submodule.mem_one.2 ⟨1, by simp⟩
      · simp [h]
  rw [← hpi, Submodule.mem_pi]
  exact (⟨fun k a => k a trivial, fun k a _ => k a⟩ : _ ↔ _).trans (hO.mem_iff (V := reS S b) y).symm

theorem isFrame_frPinvGL_mul : ∀ (D : D7) (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (βS : GL (Fin S.rank) (Lev.EAf D)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)), StdFrame.OrthFrame (reS S b) → (ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame (frPinvGL S b * βS) (stdL D.host.E (reS S b).rank) := by
  intro D S b βS ΛS hO hΛ hfr
  change Formalism.L2.DIV.IsFrame _ (stdL D.host.E S.rank)
  have hA : ∀ y ∈ stdL D.host.E S.rank, frP S b *ᵥ y ∈ ΛS := by
    intro y hy
    have h1 : frP S b *ᵥ y ∈ (ΛS : Set (Fin S.rank → D.host.E)) := by
      rw [hΛ]
      show ∑ j, (frP S b *ᵥ y) j • S.frame j ∈ S.L0
      rw [← sum_smul_frame_frP]
      exact (mem_stdL_iff S b hO y).1 hy
    exact h1
  have hB : ∀ y ∈ ΛS, frPinv S b *ᵥ y ∈ stdL D.host.E S.rank := by
    intro y hy
    rw [mem_stdL_iff S b hO, sum_smul_frame_frP, Matrix.mulVec_mulVec, frameMatrix_mul_frameMatrixInv, Matrix.one_mulVec]
    have h1 : y ∈ (ΛS : Set (Fin S.rank → D.host.E)) := hy
    rw [hΛ] at h1
    exact h1
  unfold Formalism.L2.DIV.IsFrame at hfr ⊢
  intro x
  have hinv : ((frPinvGL S b * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val *ᵥ x =
      (βS⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val *ᵥ ((frP S b).map (eToEAf D) *ᵥ x) := by
    rw [_root_.mul_inv_rev, Units.val_mul, frPinvGL_inv_val, Matrix.mulVec_mulVec]
  rw [hinv, ← hfr]
  constructor
  · intro hx
    exact hatL_mulVec_mem (frP S b) _ ΛS hA x hx
  · intro hx
    have h2 := hatL_mulVec_mem (F := D.host.F) (frPinv S b) ΛS _ hB _ hx
    have h3 : (frPinv S b).map (eToEAf D) *ᵥ ((frP S b).map (eToEAf D) *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, frPinv_mul_frP, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec]
    exact h3 ▸ h2

end GlobalTheory.AdSpan.ReVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalHeckeCharDetDoubleCosetSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localHeckeChar_det_doubleCoset_splitPlace : ∀ (D : D7) (T : HSp D) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), UnrAt χ w → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := T.rank), ∀ k₂ ∈ KGL w (n := T.rank), ((locChar χ w (Matrix.GeneralLinearGroup.det (locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂)))) : ℂˣ) : ℂ) = ((val χ w : ℂˣ) : ℂ) ^ (∑ i, d i) := by
  first | exact @GlobalTheory.DetVal.locChar_det_doubleCoset | exact GlobalTheory.DetVal.locChar_det_doubleCoset | (intros; apply GlobalTheory.DetVal.locChar_det_doubleCoset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosedSubgroupOfLocalStabilizerPairsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closedSubgroup_of_localStabilizerPairs : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (H : Subgroup (GA D S × GA D T)), IsClosed (H : Set (GA D S × GA D T)) → (∀ v ε, IsPlaceIdem D v ε → ∀ g h, Stab S βS g → Stab T βT h → SuppPl ε S g → SuppPl ε T h → (g, h) ∈ H) → ∀ g h, Stab S βS g → Stab T βT h → (g, h) ∈ H := by
  first | exact @GlobalTheory.StabDense.mem_of_local | exact GlobalTheory.StabDense.mem_of_local | (intros; apply GlobalTheory.StabDense.mem_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzGaussianFormReNegStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_form_re_neg_of_ne_zero : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (M : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (g : SchwartzMap V ℂ), g ≠ 0 →
    (∀ x, g x = g 0 * Complex.exp (M x x)) → ∀ v, v ≠ 0 → (M v v).re < 0 := by
  first | exact @GlobalTheory.schwartz_gaussian_form_re_neg | exact GlobalTheory.schwartz_gaussian_form_re_neg | (intros; apply GlobalTheory.schwartz_gaussian_form_re_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSubgroupConjugacyClassEqTsumWeightedStatement
section
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_subgroupConjugacyClass_eq_tsum_weighted : ∀ (H : Type) [Group H] (Γ : Subgroup H) (γ : H), γ ∈ Γ → ∀ (α : H → ℝ≥0∞), (∀ y, ∑' h : Γ.subgroupOf (cent γ), α (((h : cent γ) : H) * y) = 1) → ∀ (G : H → ℝ≥0∞) (x : H), ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) = ∑' g : Γ, α ((g : H) * x) * G (((g : H) * x)⁻¹ * γ * ((g : H) * x)) := by
  first | exact @GlobalTheory.Twist.ClassSumReindex.tsum_ratClass_eq_tsum_weighted | exact GlobalTheory.Twist.ClassSumReindex.tsum_ratClass_eq_tsum_weighted | (intros; apply GlobalTheory.Twist.ClassSumReindex.tsum_ratClass_eq_tsum_weighted <;> assumption)
end

