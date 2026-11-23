module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelFunctionFieldCompatibility
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ModelFn

open SmallSec

theorem ratVal_eq {Z : Scheme.{0}} [IsIntegral Z] {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ}
    (y : CxPts q σ) (f : Z.functionField) : ratVal f y = valAt y.1 f := by
  by_cases hf : RegAt (under y) f
  · exact ratVal_eq_valAt y hf
  · rw [ratVal, valAt, dite_eq_right hf, dite_eq_right hf]

theorem valAt_comp {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X) [IsPreimmersion j]
    (hη : j (genericPoint Y) ⤳ genericPoint X) {K : Type} [Field K] (y : Sp K ⟶ Y) (f : X.functionField) :
    valAt (y ≫ j) f = valAt y (fnMap j hη f) := by
  by_cases hf : RegAt (j (below y)) f
  · exact (valAt_fnMap j hη y hf).symm
  · have h₁ : ¬ RegAt (below (y ≫ j)) f := hf
    rw [valAt, valAt, dite_eq_right h₁, dite_eq_right (mt (regAt_fnMap_iff j hη).1 hf)]

end GlobalTheory.TrueGeo.ModelFn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V leviV)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.ChartGlue
open scoped ContDiff

namespace GlobalTheory.TrueGeo.OfLattice

section Rect

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {B : LB X} {α β : Type} [Fintype α] [Fintype β]

def combWeight (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) : Weight p σ B :=
  Weight.fs hB _ (fun _ => Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (secVal_mem _)) h

theorem combWeight_φ (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) (i : B.ι) (y : CxPts p σ) :
    (combWeight hB s A h).φ i y = Real.log (∑ a, ‖∑ j, A j a * valR y.1 (B.U i) ((s j).f i)‖ ^ 2) := by
  simp only [combWeight, Weight.fs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem isCInf_combWeight (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) : (combWeight hB s A h).IsCInf := fun i y hy => by
  have hs : ContDiff ℝ ∞ fun v : α → ℂ => ∑ a, ‖∑ j, A j a * v j‖ ^ 2 :=
    ContDiff.sum fun a _ => (ContDiff.sum fun j _ =>
      contDiff_const.mul (contDiff_apply ℝ (fun _ => ℂ) j)).norm_sq ℂ
  refine ⟨B.U i, α, inferInstance, fun j => (s j).f i,
    fun v => Real.log (∑ a, ‖∑ j, A j a * v j‖ ^ 2), {v | ∑ a, ‖∑ j, A j a * v j‖ ^ 2 ≠ 0}, hy,
    isOpen_ne_fun hs.continuous continuous_const, ?_, hs.contDiffOn.log fun _ h => h,
    .of_forall fun z => combWeight_φ hB s A h i z⟩
  have := (h.sum_pos hy).ne'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this

theorem semiPosReg_combWeight (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) (D : ℕ) :
    (combWeight hB s A h).SemiPosReg D := fun i c y hy ξ => by
  let G (a : β) (v : V D) : ℂ := ∑ j, A j a * ev p σ _ ((s j).f i) (c.e.symm v)
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hG (a) : ContDiffAt ℂ 2 (G a) (c.e y) := ContDiffAt.sum fun j _ => contDiffAt_const.mul
    (((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho (c.holo _ ((s j).f i))).contDiffAt
      (ho.mem_nhds (mem_over c.e hy.1 hy.2))).of_le (by norm_cast))
  have e (v : V D) : ∑ a, Complex.normSq (G ((Fintype.equivFin β).symm a) v) = ∑ a, ‖G a v‖ ^ 2 :=
    (Equiv.sum_comp (Fintype.equivFin β).symm fun a => Complex.normSq (G a v)).trans
      (Finset.sum_congr rfl fun a _ => Complex.normSq_eq_norm_sq _)
  have h0 := h.sum_pos hy.2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
  have := ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg
    (u := fun a v => Complex.normSq (G ((Fintype.equivFin β).symm a) v))
    (fun a => ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp (hG _))
    (fun a => ReciprocityTheory.L2DbarEstimates.logPshAt_normSq (hG _))
    (by rw [e]; simp only [G, c.e.left_inv hy.1]; exact h0) ξ
  simp only [e] at this
  simp only [combWeight_φ]
  exact this

variable [DecidableEq β]

theorem isConj_combWeight (hB : B.IsLB) (s : α → B.Sec) {σ σ' : k →+* ℂ} {A A' : Matrix α β ℂ}
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j))
    (h' : Weight.NoCommonZero fun a => ∑ j, A' j a • secVal p σ' (s j)) {U : Matrix β β ℂ}
    (hU : U ∈ Matrix.unitaryGroup β ℂ) (e : A' = A.map (starRingEnd ℂ) * U) :
    (combWeight hB s A h).IsConj (combWeight hB s A' h') := fun i y y' hy' hy => by
  rw [combWeight_φ, combWeight_φ]
  congr 1
  have hv (j : α) : valR y'.1 (B.U i) ((s j).f i) = starRingEnd ℂ (valR y.1 (B.U i) ((s j).f i)) :=
    CxPts.ev_conj hy' hy _
  have := sum_normSq_vecMul_unitary hU fun a =>
    starRingEnd ℂ (∑ j, A j a * valR y.1 (B.U i) ((s j).f i))
  simp only [RCLike.norm_conj] at this
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) this
  congr 2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, hv, Matrix.mul_apply, Matrix.map_apply, Matrix.vecMul, dotProduct, map_sum, map_mul,
    Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

def combHerm (hB : B.IsLB) (s : α → B.Sec) (A : (k →+* ℂ) → Matrix α β ℂ)
    (h : ∀ σ, Weight.NoCommonZero fun a => ∑ j, A σ j a • secVal p σ (s j))
    (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup β ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U) :
    HermLB p where
  B := B
  isLB := hB
  φ σ := combWeight hB s (A σ) (h σ)
  cInf σ := isCInf_combWeight hB s _ _
  conj σ σ' i y y' e hy := by
    obtain rfl := eq_conj_of_conj e
    obtain ⟨U, hU, e'⟩ := hc σ
    exact isConj_combWeight hB s (h σ) (h _) hU e' i y y' e hy

end Rect

theorem nefFib_of_isGenerated {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (L : HermLB p) (hL : IsGenerated L.B) : ArInt.NefFib L := by
  intro Z i _ _ κ _ _ _ hd
  have := hX.finite
  have : IsProper p := CommonModel.isProper_of_isProjOver hX.isProjOver
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hX.isProjOver
  have hA := hH.pull_of_isClosedImmersion i
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have h := (isNef_iff_isClosedImmersion.1 ((hL.pull i).isNef (k := κ) hA)).2 Z (𝟙 Z) inferInstance inferInstance hd
    (by rw [Category.id_comp]; infer_instance)
  rw [interNumOn_id] at h
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

variable {F : Type} [Field F] [NumberField F]

section Values

variable {K : Type} [Field K] {Y : Var F} (y : Sp K ⟶ Y.X) {τ : F →+* K}




end Values

theorem injective_emb (σ : 𝓞 F →+* ℂ) : Function.Injective σ :=
  (RingHom.injective_iff_ker_eq_bot σ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (by
    rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _))

def extEmb (σ : 𝓞 F →+* ℂ) : F →+* ℂ := IsFractionRing.lift (injective_emb σ)

theorem extEmb_comp (σ : 𝓞 F →+* ℂ) : (extEmb σ).comp (algebraMap (𝓞 F) F) = σ :=
  RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := F) (injective_emb σ) a

theorem extEmb_eq {σ : 𝓞 F →+* ℂ} {τ : F →+* ℂ} (h : τ.comp (algebraMap (𝓞 F) F) = σ) : extEmb σ = τ :=
  IsFractionRing.ringHom_ext (A := 𝓞 F) fun a => RingHom.congr_fun ((extEmb_comp σ).trans h.symm) a

variable [StarRing F]




end GlobalTheory.TrueGeo.OfLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ArInt

theorem cls_eq_zero_of_chart_eq_top {Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) (i₀ : L.ι)
    (h : L.U i₀ = ⊤) : cls L hL = 0 := by
  have le : ∀ j, L.U j ≤ L.U j ⊓ L.U i₀ := fun j => le_inf le_rfl (h ▸ le_top)
  have hm : ∀ y : Z, y ∈ L.U i₀ := fun y => h ▸ Opens.mem_top y
  have H : ∃ t : LB.Gen L, t.IsGen :=
    ⟨⟨fun j => res (le j) (L.g j i₀)⟩, fun i j => unit_ext fun y hy => by
      rw [map_mul, gm_res (𝟙 Z) y _ hy, gm_res (𝟙 Z) y _ hy.1, gm_res (𝟙 Z) y _ hy, gm_res (𝟙 Z) y _ hy.2]
      exact (gm_cocycle hL (𝟙 Z) y hy.1 hy.2 (hm y)).symm⟩
  exact (cls_eq_iff hL (LB.isLB_triv Z)).2 (LBIso.symm ((iso_triv_iff L).2 H))

theorem topSelf_pull_eq_zero_of_const {X Z : Scheme.{0}} (κ : Type) [Field κ] [Algebra κ Γ(Z, ⊤)]
    {M : LB X} (hM : M.IsLB) (g : Z ⟶ X) (x : X) (hg : ∀ z, g z = x) :
    topSelfIntersection κ (M.pull g) 1 = 0 := by
  obtain ⟨i, hi⟩ := exists_chart hM x
  have h := cls_eq_zero_of_chart_eq_top (pull_isLB hM g) (fun _ => i)
    (top_le_iff.1 fun z _ => mem_pull.2 ((hg z).symm ▸ hi))
  exact interNum_eq_zero_of_cls_eq_zero κ _ (fun _ => pull_isLB hM g) 0 h

theorem isProper_strHom (κ : Type) [Field κ] {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)] (t : Z ⟶ Sp ℤ)
    [IsProper t] : IsProper (strHom κ (X := Z)) := by
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = t := specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  exact IsProper.of_comp _ (spMap (Int.castRingHom κ))

theorem appTop_injective_of_denseRange {Z W : Scheme.{0}} [IsReduced Z] (φ : W ⟶ Z)
    (h : DenseRange φ) : Function.Injective φ.appTop.hom := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  by_contra hne0
  have hne : Z.basicOpen a ≠ ⊥ := fun h0 => hne0 ((basicOpen_eq_bot_iff a).1 h0)
  obtain ⟨w, hw⟩ := h.exists_mem_open (Z.basicOpen a).isOpen
    (Set.nonempty_iff_ne_empty.2 fun e => hne (Opens.ext e))
  have e : φ ⁻¹ᵁ Z.basicOpen a = W.basicOpen (φ.appTop.hom a) := Scheme.preimage_basicOpen_top φ a
  have hw' : w ∈ W.basicOpen (φ.appTop.hom a) := e ▸ hw
  rw [ha, Scheme.basicOpen_zero] at hw'
  exact hw'

section

attribute [local instance low] specializationOrder

theorem one_le_dim {S : Type} [TopologicalSpace S] [QuasiSober S] [T0Space S] {a b : S} (h : a ⤳ b)
    (hne : a ≠ b) : 1 ≤ topologicalKrullDim S := by
  rw [PosBaseChange.dim_eq_krullDim]
  exact Order.one_le_krullDim_iff.2 ⟨b, a, lt_of_le_of_ne h hne.symm⟩

end

section Curve

variable {X W : Scheme.{0}} [IsIntegral W] (ℓ : ℕ) [Fact ℓ.Prime] [Algebra (ZMod ℓ) Γ(W, ⊤)]

theorem topSelf_pull_nonneg (t : X ⟶ Sp ℤ) [IsProper t] (hd : topologicalKrullDim W = 1)
    {M : LB X} (hM : M.IsLB) (g : W ⟶ X) [IsProper (g ≫ t)]
    (H : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      [Algebra (ZMod ℓ) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod ℓ) (M.pull i) 1) :
    0 ≤ topSelfIntersection (ZMod ℓ) (M.pull g) 1 := by
  have : IsProper g := .of_comp g t
  have hW : IsProper (strHom (ZMod ℓ) (X := W)) := isProper_strHom (ZMod ℓ) (g ≫ t)
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (strHom (ZMod ℓ) W)
  have := isNoetherian_of_locallyOfFiniteType_field (strHom (ZMod ℓ) W)
  by_cases hc : ∀ w, g w = g (genericPoint W)
  · exact (topSelf_pull_eq_zero_of_const (ZMod ℓ) hM g _ hc).ge
  push_neg at hc
  obtain ⟨x₀, hx₀⟩ := hc
  let φ : W ⟶ g.image := g.toImage
  have e : φ ≫ g.imageι = g := g.toImage_imageι
  have : IsProper (φ ≫ g.imageι) := by rw [e]; infer_instance
  have : IsProper φ := .of_comp φ g.imageι
  have hne : φ x₀ ≠ φ (genericPoint W) := fun h => hx₀ (by
    rw [← e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h])
  have : LocallyQuasiFinite φ := ProperCurve.locallyQuasiFinite_of_ne hd φ hne
  have : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  have hdense : DenseRange φ := g.toImage.denseRange
  have hsurj : Function.Surjective φ := by
    rw [← Set.range_eq_univ, ← φ.isClosedMap.isClosed_range.closure_eq]
    exact hdense.closure_range
  have hgen : φ (genericPoint W) = genericPoint g.image := by
    have h₁ := (genericPoint_spec W).image φ.continuous
    rw [Set.image_univ, hdense.closure_range] at h₁
    exact h₁.eq (genericPoint_spec _)
  have hdZ : topologicalKrullDim g.image = 1 := by
    exact le_antisymm ((PosBaseChange.dim_le_of_isClosedMap φ.isClosedMap hsurj).trans hd.le)
      (one_le_dim (genericPoint_specializes (φ x₀)) fun h => hne (h.symm.trans hgen.symm))
  have hinj := appTop_injective_of_denseRange φ hdense
  have : CharP Γ(W, ⊤) ℓ := charP_of_injective_algebraMap (algebraMap (ZMod ℓ) Γ(W, ⊤)).injective ℓ
  have : CharP Γ(g.image, ⊤) ℓ := φ.appTop.hom.charP hinj ℓ
  letI : Algebra (ZMod ℓ) Γ(g.image, ⊤) := ZMod.algebra _ ℓ
  have hf (r : ZMod ℓ) : φ.appTop (algebraMap (ZMod ℓ) Γ(g.image, ⊤) r) = algebraMap (ZMod ℓ) Γ(W, ⊤) r :=
    RingHom.congr_fun (RingHom.ext_zmod (φ.appTop.hom.comp (algebraMap (ZMod ℓ) Γ(g.image, ⊤)))
      (algebraMap (ZMod ℓ) Γ(W, ⊤))) r
  have : IsProper (g.imageι ≫ t) := inferInstance
  have hZ : IsProper (strHom (ZMod ℓ) (X := g.image)) := isProper_strHom (ZMod ℓ) (g.imageι ≫ t)
  have hproj : IsProjOver (strHom (ZMod ℓ) (X := g.image)) := ProperCurve.isProjOver_of_isProper _ hdZ
  have hN := pull_isLB hM g.imageι
  have h₁ := GlobalTheory.ProjFin.interNumOn_eq_residueDegree_mul (ZMod ℓ) g.image W φ hproj hdZ hgen (M.pull g.imageι) hN
  have h₂ := interNumOn_eq_interNum_pull (k := ZMod ℓ) (L := ![M.pull g.imageι]) hf
    (fun i => by fin_cases i; exact hN)
  have h₃ : topSelfIntersection (ZMod ℓ) (M.pull g) 1 =
      interNum (ZMod ℓ) (structureModule W) fun i => (![M.pull g.imageι] i).pull φ := by
    refine interNum_congr_cls _ _ (fun _ => pull_isLB hM g) (fun i => by fin_cases i; exact pull_isLB hN φ) fun i => ?_
    fin_cases i
    refine (cls_pull hM g _).trans ?_
    refine Eq.trans ?_ (cls_pull hN φ _).symm
    exact (congrArg (fun f => pull f (cls M hM)) e.symm).trans (pull_comp φ g.imageι _)
  have h₄ : interNum (ZMod ℓ) (structureModule g.image) ![M.pull g.imageι] =
      topSelfIntersection (ZMod ℓ) (M.pull g.imageι) 1 := by
    refine congrArg _ (funext fun j => ?_)
    fin_cases j
    rfl
  rw [h₃, ← h₂, h₁, h₄]
  exact mul_nonneg (Int.natCast_nonneg _) (H _ g.imageι hdZ)

end Curve

theorem nefFib_pull : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k)
    (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p),
    ArInt.NefFib L → ArInt.NefFib (L.pull π hπ) := by
  intro k _ _ X Y p q hp hq π hπ L hL
  refine nefFib_of_primeField k Y q _ fun W i _ _ ℓ _ _ hd => ?_
  obtain ⟨N, j, _, hj⟩ := hp
  obtain ⟨N', j', _, hj'⟩ := hq
  have := isProper_str k N
  have := isProper_str k N'
  have : IsProper p := hj ▸ inferInstance
  have : IsProper q := hj' ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have hp' : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := .of_comp π p
  have hg : IsProper ((i ≫ π) ≫ p ≫ spMap (Int.castRingHom k)) := inferInstance
  have h := topSelf_pull_nonneg ℓ (p ≫ spMap (Int.castRingHom k)) hd L.isLB (i ≫ π)
    fun Z i' _ _ _ hd' => hL Z i' (ZMod ℓ) hd'
  have e : cls ((L.pull π hπ).B.pull i) (pull_isLB (L.pull π hπ).isLB i) =
      cls (L.B.pull (i ≫ π)) (pull_isLB L.isLB _) := by
    refine (cls_pull (L.pull π hπ).isLB i _).trans ?_
    refine Eq.trans ?_ (cls_pull L.isLB (i ≫ π) _).symm
    exact (pull_comp i π (cls L.B L.isLB)).symm
  rwa [topSelf_congr (ZMod ℓ) (pull_isLB (L.pull π hπ).isLB i) (pull_isLB L.isLB _)
    ((cls_eq_iff _ _).1 e)]

end GlobalTheory.ArInt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormGaloisEquivariance
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem laws_cast {D : D7} {T : CoreJ D} (L : LawsJ T) {j : ℕ} (hj : InR D j) {σ : T.Q.c.F →+* ℂ}
    (hσ : GoodEmb T.Q.c σ) {W : HSp D} (hV : T.V j σ = W) (hr : W.rank = D.R.r) :
    (∀ k, ModelW W hr ((T.U j σ).X k)) ∧
    (∀ h, (castDict hV (T.dict j σ) h).2 ∈ ((T.U j σ).X (castDict hV (T.dict j σ) h).1).dom) ∧
    (∀ h, IsUnitFr ((T.U j σ).X (castDict hV (T.dict j σ) h).1) (castDict hV (T.dict j σ) h).2) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ))
      (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif (T.Q.Xo j) (σ.comp (IntermediateField.inclusion T.Q.c.le).toRingHom)
        (fun i => relab T.Q.c σ (e i).1))
      (ik : (T.U j σ).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ)
      (th : ∀ k, ((T.U j σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧
        DictLat (T.U j σ) W hr (castDict hV (T.dict j σ))
          (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) e F ik φ th (T.x₀ j σ) := by
  subst hV
  obtain ⟨_, hm⟩ := L.modelW j hj σ hσ
  obtain ⟨_, _, -, hd⟩ := L.dictU j hj σ hσ
  obtain ⟨_, g, e, F, ik, φ, th, -, -, h1, h2⟩ := L.adPin j hj σ hσ
  exact ⟨hm, hd.2.2.2.1, (L.muUnit j hj σ hσ).2.2.2, g, e, F, ik, φ, th, h1, h2⟩

theorem exists_type_equiv {D : D7} (Q : Par D) (hp : Q.PinHost) (Ψ : Finset (D.host.E →+* ℂ))
    (hΨ : ∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ τ (Q.H.rt : D.host.E) = Q.H.rt0) :
    ∃ eT : D.what₂.Tau ≃ Ψ, ∀ ρ, (eT ρ).1 = tauE D ρ := by
  refine ⟨Equiv.ofBijective (fun ρ => ⟨tauE D ρ, (hΨ _).2 (hp.2.2.2 ρ)⟩) ⟨fun a b h => ?_, fun τ => ?_⟩, fun _ => rfl⟩
  · exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 (congrArg Subtype.val h)))
  · obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi Q hp τ.1 ((hΨ _).1 τ.2)
    exact ⟨t, Subtype.ext ht.symm⟩

end GlobalTheory.OneMapRef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts

namespace GlobalTheory.ProjModel

theorem isArithVar_pspace (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (hd : ringKrullDim k = 1) (N : ℕ) : IsArithVar (PSpace.str k N) N := by
  have := isIntegral_of_isDomain k N
  have : IsNoetherianRing k := IsNoetherianRing.of_finite ℤ k
  have : Smooth (PSpace.str k N) := SmoothOfRelativeDimension.smooth N _
  have hc : ∀ i, topologicalKrullDim (chart k N i : Set (PSpace k N)) = (N + 1 : ℕ) := fun i => by
    rw [topologicalKrullDim_eq_of_isEmbedding (chartι k N i).isOpenEmbedding.isEmbedding
      (congrArg SetLike.coe (opensRange_chartι k N i))]
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
      (R := MvPolynomial {j // j ≠ i} k)).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, hd]
    simp [add_comm]
  refine ⟨inferInstance, inferInstance, ‹_›, ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩, ?_,
    le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_)
      ((hc 0).ge.trans (topologicalKrullDim_subspace_le _ _))⟩
  · have h := (ArithBase.isArithVar_id hd).flat
    rw [Category.id_comp] at h
    infer_instance
  · obtain ⟨i, hi⟩ := exists_mem_chart k N x
    exact ⟨_, (chart k N i).isOpen, hi, (hc i).le⟩

theorem nefFib_of_isAmpleLB {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsProper p]
    (L : HermLB p) (hL : IsAmpleLB L.B) : ArInt.NefFib L := by
  intro Z i _ _ κ _ _ _ hd
  have hA := hL.pull_of_isClosedImmersion i
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have h := (isNef_iff_isClosedImmersion.1 (hA.isNef (k := κ))).2 Z (𝟙 Z) inferInstance inferInstance hd
    (by rw [Category.id_comp]; infer_instance)
  rw [interNumOn_id] at h
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

variable (F : Type) [Field F] [NumberField F] (n : ℕ)

end GlobalTheory.ProjModel
end
end

