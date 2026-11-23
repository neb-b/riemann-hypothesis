module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0757
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPointLengthFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoheightEqOneOfDimClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2135
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0756
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0546
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecializesIffPointIdealLe

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermStar
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical Kronecker
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtAdj

section Generic

variable {H : Type} [Group H]

theorem rStab_conj (u : H → ℂ) : rStab (fun x => starRingEnd ℂ (u x)) = rStab u := by
  ext k
  constructor
  · intro hk x
    exact (starRingEnd ℂ).injective (hk x)
  · intro hk x
    show starRingEnd ℂ (u (x * k)) = starRingEnd ℂ (u x)
    rw [hk x]

theorem finsum_conj {α : Type} (g : α → ℂ) : ∑ᶠ q, starRingEnd ℂ (g q) = starRingEnd ℂ (∑ᶠ q, g q) :=
  (AddMonoidHom.map_finsum_of_injective (starRingEnd ℂ).toAddMonoidHom (starRingEnd ℂ).injective g).symm

theorem hint_conj (K : Subgroup H) (u : H → ℂ) :
    hint K (fun x => starRingEnd ℂ (u x)) = starRingEnd ℂ (hint K u) := by
  unfold hint
  rw [rStab_conj, map_mul, map_inv₀, map_natCast, finsum_conj]

theorem avg_conj (u : H → ℂ) : avg (fun x => starRingEnd ℂ (u x)) = starRingEnd ℂ (avg u) := by
  unfold avg
  rw [rStab_conj, map_mul, map_inv₀, map_natCast, finsum_conj]

end Generic

theorem det_lr {k : Type} [Field k] {a b : ℕ} (A : Matrix (Fin a) (Fin a) k) (B : Matrix (Fin b) (Fin b) k)
    (L : Matrix (Fin a) (Fin b) k →ₗ[k] Matrix (Fin a) (Fin b) k) (hL : ∀ X, L X = A * X * B) :
    LinearMap.det L = A.det ^ b * B.det ^ a := by
  let e : Matrix (Fin a) (Fin b) k ≃ₗ[k] (Fin a × Fin b → k) := (LinearEquiv.curry k k (Fin a) (Fin b)).symm
  have h : (e.toLinearMap ∘ₗ L ∘ₗ e.symm.toLinearMap) = Matrix.toLin' (A ⊗ₖ Bᵀ) := by
    apply LinearMap.ext
    intro v
    funext ⟨i, j⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hL, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
    show (A * (Matrix.of fun l c => v (l, c)) * B) i j = _
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [← LinearMap.det_conj L e, h, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose,
    Fintype.card_fin, Fintype.card_fin]

variable {E : Type} [Field E] [NumberField E]

theorem absHalf_one (w : Pl E) : absHalf w (1 : w.adicCompletion E) = 1 := by
  have h := GlobalTheory.LeviDesc.absHalf_mul E w 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  have h0 := GlobalTheory.LeviDesc.absHalf_ne_zero' w (1 : w.adicCompletion E)
  exact (mul_right_cancel₀ h0 (by rw [one_mul]; exact h)).symm

theorem absHalf_inv_mul (w : Pl E) {x : w.adicCompletion E} (hx : x ≠ 0) :
    absHalf w x⁻¹ * absHalf w x = 1 := by
  rw [← GlobalTheory.LeviDesc.absHalf_mul E w _ _ (inv_ne_zero hx) hx, inv_mul_cancel₀ hx, absHalf_one]

theorem conj_absHalf (w : Pl E) (x : w.adicCompletion E) : starRingEnd ℂ (absHalf w x) = absHalf w x := by
  unfold absHalf
  exact Complex.conj_ofReal _

variable [IsCMField E]

def negL {a b : ℕ} {w : Pl E} (m : GLw a w × GLw b w) :
    Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E) where
  toFun X := -(m.1.val * X * (m.2⁻¹).val)
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul, neg_add]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem det_inv_val {k : ℕ} {w : Pl E} (g : GLw k w) : (g⁻¹).val.det = (g.val.det)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]

theorem det_ne_zero {k : ℕ} {w : Pl E} (g : GLw k w) : g.val.det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero

theorem v_det_negL {a b : ℕ} {w : Pl E} (m : GLw a w × GLw b w) :
    Valued.v (LinearMap.det (negL m)) = Valued.v (m.1.val.det ^ b / m.2.val.det ^ a) := by
  have h : LinearMap.det (negL m) = (-m.1.val).det ^ b * (m.2⁻¹).val.det ^ a :=
    det_lr _ _ _ fun X => by simp [negL, Matrix.neg_mul]
  rw [h, det_inv_val, Matrix.det_neg, Fintype.card_fin, div_eq_mul_inv, map_mul, map_mul, map_pow, map_mul, map_pow,
    map_pow, map_pow, map_inv₀, map_inv₀, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, inv_pow]

theorem det_negL_ne_zero {a b : ℕ} {w : Pl E} (m : GLw a w × GLw b w) : LinearMap.det (negL m) ≠ 0 := by
  intro h0
  have h := v_det_negL m
  rw [h0, map_zero] at h
  exact div_ne_zero (pow_ne_zero _ (det_ne_zero m.1)) (pow_ne_zero _ (det_ne_zero m.2))
    ((Valuation.zero_iff _).1 h.symm)

theorem ct_adj {n a b : ℕ} (h : a + b = n) (w : Pl E) (F : GLw n w → ℂ)
    (hF : ∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' F) (m : GLw a w × GLw b w) :
    ct h w (fun y => starRingEnd ℂ (F y⁻¹)) m = starRingEnd ℂ (ct h w F m⁻¹) := by
  obtain ⟨hU, hcs⟩ := GlobalTheory.T.conjAverage_unipotent_locallyConstant_compactSupport E n a b h w F hF m⁻¹
  have hJ := _root_.GlobalTheory.LeviDesc.hint_comp_linear E w a b (negL m)
    (fun X => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ X)) (det_negL_ne_zero m) hU hcs
  have hpt : ∀ X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)),
      avg (fun k : GlobalTheory.LFun.KGL w (n := n) => starRingEnd ℂ (F ((((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k))⁻¹))) =
      starRingEnd ℂ (GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ (negL m (Multiplicative.toAdd X)))) := by
    intro X
    unfold GlobalTheory.LeviDesc.cavg
    rw [← avg_conj]
    congr 1
    funext k
    have e : ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)⁻¹ =
        (k : GLw n w)⁻¹ * blk h w m⁻¹ (negL m (Multiplicative.toAdd X)) * k := by
      have e2 : blk h w m⁻¹ (negL m (Multiplicative.toAdd X)) = (blk h w m (Multiplicative.toAdd X))⁻¹ :=
        (CtLevel.blk_inv h w m _).symm
      rw [e2]
      group
    rw [e]
  have hD0 : m.1.val.det ^ b / m.2.val.det ^ a ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (det_ne_zero m.1)) (pow_ne_zero _ (det_ne_zero m.2))
  have hinv : (m⁻¹).1.val.det ^ b / (m⁻¹).2.val.det ^ a = (m.1.val.det ^ b / m.2.val.det ^ a)⁻¹ := by
    rw [Prod.fst_inv, Prod.snd_inv, det_inv_val, det_inv_val, inv_pow, inv_pow, inv_div, div_eq_mul_inv, inv_inv, mul_comm,
      div_eq_mul_inv]
  have hc : absHalf w (LinearMap.det (negL m)) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) :=
    GlobalTheory.BCT.AbsHalfInv.absHalf_congr (v_det_negL m)
  have h1 : hint (intMat a b w) (fun X => avg fun k : GlobalTheory.LFun.KGL w (n := n) =>
        starRingEnd ℂ (F (((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)⁻¹))) =
      starRingEnd ℂ (hint (intMat a b w) fun X =>
        GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ (negL m (Multiplicative.toAdd X)))) := by
    rw [← hint_conj]
    congr 1
    funext X
    exact hpt X
  have hJ' : (hint (intMat a b w) fun X =>
      GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ (negL m (Multiplicative.toAdd X)))) =
      (absHalf w (LinearMap.det (negL m)) ^ 2)⁻¹ * hint (intMat a b w) (fun X =>
        GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ (Multiplicative.toAdd X))) := hJ
  show absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * hint (intMat a b w) (fun X => avg fun k : GlobalTheory.LFun.KGL w (n := n) =>
        starRingEnd ℂ (F (((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)⁻¹))) =
      starRingEnd ℂ (absHalf w ((m⁻¹).1.val.det ^ b / (m⁻¹).2.val.det ^ a) * hint (intMat a b w) (fun X =>
        GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) F (blk h w m⁻¹ (Multiplicative.toAdd X))))
  rw [h1, hJ', hc, hinv, map_mul, map_mul, map_inv₀, map_pow, conj_absHalf, conj_absHalf]
  have hA := GlobalTheory.LeviDesc.absHalf_ne_zero' w (m.1.val.det ^ b / m.2.val.det ^ a)
  rw [eq_inv_of_mul_eq_one_left (absHalf_inv_mul w hD0)]
  field_simp

theorem mu_conj {K : Type} [Group K] (μ : K →* ℂˣ) (hμ : ∀ u, ‖((μ u : ℂˣ) : ℂ)‖ = 1) (x : K) :
    ((μ x⁻¹ : ℂˣ) : ℂ) = starRingEnd ℂ ((μ x : ℂˣ) : ℂ) := by
  rw [map_inv, Units.val_inv_eq_inv_val]
  exact Complex.inv_eq_conj (hμ x)

theorem ctStar : PositivityTheory.Rg.BcB.F.MLM.CtStar := by
  intro E _ _ _ n a ha w hw μ hμ f hf
  have hU : UL n w = ⊤ := if_pos hw
  funext m
  have hH := GlobalTheory.CompanionTheory.CtMulSplit.isHk_of_isHecke hU hf
  have hF : ∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' (fun y => f (toSub (UL n w) y)) :=
    ⟨GlobalTheory.LFun.KGL w (n := n), (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, hH.2.2.1, fun k hk x =>
      ⟨by simpa using hH.2.2.2 k hk 1 (Subgroup.one_mem _) x, by simpa using hH.2.2.2 1 (Subgroup.one_mem _) k hk x⟩⟩
  have hstar : (fun y => PositivityTheory.Rg.BcB.F.Eig.lstar f (toSub (UL n w) y)) =
      fun y => starRingEnd ℂ (f (toSub (UL n w) y⁻¹)) := by
    funext y
    show starRingEnd ℂ (f (toSub (UL n w) y)⁻¹) = _
    have e : (toSub (UL n w) y)⁻¹ = toSub (UL n w) y⁻¹ :=
      Subtype.ext (by rw [Subgroup.coe_inv, GlobalTheory.CompanionTheory.CtMulSplit.val_toSub hU, GlobalTheory.CompanionTheory.CtMulSplit.val_toSub hU])
    rw [e]
  show ((μ _ : ℂˣ) : ℂ) * ct _ w (fun y => PositivityTheory.Rg.BcB.F.Eig.lstar f (toSub (UL n w) y)) m =
    starRingEnd ℂ (((μ _ : ℂˣ) : ℂ) * ct _ w (fun y => f (toSub (UL n w) y)) m⁻¹)
  rw [hstar, ct_adj _ w (fun y => f (toSub (UL n w) y)) hF m, map_mul (starRingEnd ℂ)]
  congr 1
  rw [← mu_conj μ hμ]
  congr 2
  have hs : (((-1 : (w.adicCompletion E)ˣ) ^ (a * (n - a)))⁻¹) = (-1) ^ (a * (n - a)) := by
    rw [← inv_pow]
    simp
  simp only [Prod.fst_inv, Prod.snd_inv, map_inv, inv_pow, mul_inv, inv_inv, hs]

end GlobalTheory.CompanionTheory.CtAdj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerCharacteristicDimensionZero
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MixZ.VertBase

theorem isField_of_subsingleton_primeSpectrum {R : Type} [CommRing R] [IsDomain R]
    (h : Subsingleton (PrimeSpectrum R)) : IsField R := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal R
  have hP : (⟨M, hM.isPrime⟩ : PrimeSpectrum R) = ⟨⊥, Ideal.isPrime_bot⟩ := Subsingleton.elim _ _
  have hMb : M = ⊥ := congrArg PrimeSpectrum.asIdeal hP
  exact Ring.isField_iff_maximal_bot.mpr (hMb ▸ hM)

variable (Z : Scheme.{0}) [IsIntegral Z]

theorem eq_genericPoint (hd : topologicalKrullDim Z = (0 : ℕ)) (x : Z) : x = genericPoint Z := by
  have hle : Order.krullDim (IrreducibleCloseds Z) ≤ 0 := by
    have h0 := hd
    simp only [topologicalKrullDim] at h0
    rw [h0]
    simp
  have hmax := Order.krullDim_nonpos_iff_forall_isMax.mp hle
  let C : IrreducibleCloseds Z := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let U : IrreducibleCloseds Z := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
  have h1 : C ≤ U := fun _ _ => Set.mem_univ _
  have h2 : U ≤ C := hmax C h1
  have hg : genericPoint Z ∈ closure ({x} : Set Z) := h2 (Set.mem_univ _)
  have hs1 : x ⤳ genericPoint Z := specializes_iff_mem_closure.mpr hg
  have hs2 : genericPoint Z ⤳ x := (genericPoint_spec Z).specializes (Set.mem_univ x)
  exact (hs1.antisymm hs2).eq

theorem isAffineOpen_top (hd : topologicalKrullDim Z = (0 : ℕ)) : IsAffineOpen (⊤ : Z.Opens) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint Z ∈ (⊤ : Z.Opens) from Set.mem_univ _)
  have hUt : U = ⊤ := eq_top_iff.mpr fun y _ => by rw [eq_genericPoint Z hd y]; exact hxU
  exact hUt ▸ hU

theorem isField_top (hd : topologicalKrullDim Z = (0 : ℕ)) : IsField Γ(Z, ⊤) := by
  have hA := isAffineOpen_top Z hd
  have hsub : Subsingleton (PrimeSpectrum Γ(Z, ⊤)) := by
    constructor
    intro p q
    exact hA.fromSpec.isOpenEmbedding.injective
      ((eq_genericPoint Z hd _).trans (eq_genericPoint Z hd _).symm)
  exact isField_of_subsingleton_primeSpectrum hsub

theorem bijective_top (hd : topologicalKrullDim Z = (0 : ℕ)) :
    Function.Bijective ((IsLocalRing.residue (Z.presheaf.stalk (genericPoint Z))).comp
      (algebraMap Γ(Z, ⊤) Z.functionField)) := by
  have hF := isField_top Z hd
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel h
    have h1 := congrArg ((IsLocalRing.residue (Z.presheaf.stalk (genericPoint Z))).comp
      (algebraMap Γ(Z, ⊤) Z.functionField)) hb
    rw [map_mul, ha, zero_mul, map_one] at h1
    exact zero_ne_one h1
  · intro y
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨U, hm, s, hs⟩ := Z.presheaf.exists_germ_eq t
    have hU : U = ⊤ := eq_top_iff.mpr fun x _ => by rw [eq_genericPoint Z hd x]; exact hm
    subst hU
    exact ⟨s, by rw [RingHom.comp_apply, ← hs]; rfl⟩

theorem chi_eq_geoNum : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ MP ℤ m n)
    [IsClosedImmersion f] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) Γ(Z, ⊤)],
    topologicalKrullDim Z = (0 : ℕ) → ∀ a : Fin 0 → Fin (m + 1) → ℤ,
      chi (ZMod p) (structureModule Z) = geoNum 0 (ptIdeal (f (genericPoint Z))) a := by
  intro m n Z _ f _ p _ _ hd a
  have hp : p.Prime := Fact.out
  have hA := isAffineOpen_top Z hd
  haveI : IsAffine (⊤ : Z.Opens) := hA
  haveI : IsAffine Z := by
    first
      | exact IsAffine.of_isIso Z.topIso.inv
      | exact isAffine_of_isIso Z.topIso.inv
      | exact AlgebraicGeometry.isAffineOpen_top_iff.mp hA
      | exact (AlgebraicGeometry.isAffineOpen_top_iff Z).mp hA
      | exact IsAffine.of_isIso (Scheme.topIso Z).inv
      | exact hA.isAffine_of_top
  rw [GlobalTheory.chi_structureModule_of_isAffine Z (ZMod p)]
  have hb := bijective_top Z hd
  have hRes : CharP (Z.residueField (genericPoint Z)) p :=
    (RingHom.charP_iff_charP (((IsLocalRing.residue (Z.presheaf.stalk (genericPoint Z))).comp
      (algebraMap Γ(Z, ⊤) Z.functionField)).comp (algebraMap (ZMod p) Γ(Z, ⊤))) p).mp inferInstance
  haveI hΩ : CharP ((MP ℤ m n).residueField (f (genericPoint Z))) p :=
    (RingHom.charP_iff_charP (f.residueFieldMap (genericPoint Z)).hom p).mpr hRes
  have hcomap : (ptIdeal (f (genericPoint Z))).comap (C : ℤ →+* MRing (Bk n)) =
      Ideal.span {(p : ℤ)} := by
    ext z
    rw [Ideal.mem_comap, Ideal.mem_span_singleton,
      ← CharP.intCast_eq_zero_iff ((MP ℤ m n).residueField (f (genericPoint Z))) p]
    simp only [ptIdeal, ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal, RingHom.mem_ker, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_apply, MvPolynomial.C_eq_zero, eq_intCast]
    rw [map_intCast, ← map_intCast (MvPolynomial.C : (MP ℤ m n).residueField (f (genericPoint Z)) →+*
      MvPolynomial (Fin (m + 1)) ((MP ℤ m n).residueField (f (genericPoint Z)))), MvPolynomial.C_eq_zero]
  have hchar : charOf (ptIdeal (f (genericPoint Z))) = p := by
    have key : ∀ I : Ideal ℤ, I = Ideal.span {(p : ℤ)} →
        (Submodule.IsPrincipal.generator I).natAbs = p := by
      rintro I rfl
      have hg := Submodule.IsPrincipal.span_singleton_generator (Ideal.span {(p : ℤ)})
      have hass : Associated (Submodule.IsPrincipal.generator (Ideal.span {(p : ℤ)})) (p : ℤ) :=
        Ideal.span_singleton_eq_span_singleton.mp hg
      rw [Int.natAbs_eq_iff_associated.mpr hass]
      simp
    exact key _ hcomap
  have hcl : topologicalKrullDim (closure ({genericPoint Z} : Set Z)) = (0 : ℕ) :=
    (dim_closure_generic Z).trans hd
  have hL := _root_.GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen m n Z f (genericPoint Z) hcl a
  rw [hchar] at hL
  have hcard : Nat.card (Z.residueField (genericPoint Z)) = Nat.card Γ(Z, ⊤) :=
    (Nat.card_eq_of_bijective _ hb).symm
  rw [hcard] at hL
  have hlogp : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  by_cases hfin : Module.Finite (ZMod p) Γ(Z, ⊤)
  · rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, Nat.cast_pow, Real.log_pow] at hL
    have hg : (geoNum 0 (ptIdeal (f (genericPoint Z))) a : ℝ) =
        (Module.finrank (ZMod p) Γ(Z, ⊤) : ℝ) := mul_right_cancel₀ hlogp hL
    exact_mod_cast hg.symm
  · rw [Module.finrank_of_not_finite hfin]
    haveI : Infinite Γ(Z, ⊤) := by
      by_contra hinf
      rw [not_infinite_iff_finite] at hinf
      exact hfin Module.Finite.of_finite
    rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero, Real.log_zero] at hL
    have hg : (geoNum 0 (ptIdeal (f (genericPoint Z))) a : ℝ) = 0 := by
      rcases mul_eq_zero.mp hL with h | h
      · exact h
      · exact absurd h hlogp
    exact_mod_cast hg.symm

end GlobalTheory.CompanionTheory.MixZ.VertBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericPointNonvanishingCoordinateSection
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MixZ.VertGen

private theorem pullForm_X_eq_pullRatio {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace ℤ N) (W : Y.Opens)
    (i : Fin (N + 1)) (hi : W ≤ (Opens.map φ.base).obj (GlobalTheory.ProjSpace.chart ℤ N i)) (l : Fin (N + 1))
    (h : (MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℤ).IsHomogeneous 1) :
    GlobalTheory.ProjBlowup.pullForm φ W i hi 1 (MvPolynomial.X l) h = GlobalTheory.ProjSpace.pullRatio φ W i hi l := by
  unfold GlobalTheory.ProjBlowup.pullForm GlobalTheory.ProjSpace.pullRatio GlobalTheory.ProjSpace.formOn GlobalTheory.ProjSpace.ratio
    GlobalTheory.ProjSpace.ratioOn
  congr 1
  congr 1
  exact pow_one _

theorem genericPoint_mem_nonzeroLocus : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] (k : Fin (m + 1)) (l : Bk n k), (X ⟨k, l⟩ : Pol n) ∉ ptIdeal (f (genericPoint Z)) → genericPoint Z ∈ Out.nonzeroLocus (pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l)) := by
  intro m n Z _ f _ k l hX
  have hxj := GlobalTheory.CompanionTheory.MPDict.mem_ptChart (f (genericPoint Z)) k
  have hne : GlobalTheory.CompanionTheory.MPDict.ptCoord (f (genericPoint Z)) ⟨k, l⟩ ≠ 0 := by
    intro h0
    apply hX
    show (MvPolynomial.X ⟨k, l⟩ : Pol n) ∈
      RingHom.ker (ReciprocityTheory.ChartRestriction.G.Geo.mConeMap (GlobalTheory.CompanionTheory.MPDict.ptCoord (f (genericPoint Z))))
    rw [RingHom.mem_ker]
    simp [ReciprocityTheory.ChartRestriction.G.Geo.mConeMap, h0]
  let j : (pullO (f ≫ prB n k) 1).ι := (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k : Fin (n k + 1))
  have hξ : genericPoint Z ∈ (pullO (f ≫ prB n k) 1).U j := hxj
  apply GlobalTheory.basicOpen_le_nonzeroLocus _ j
  refine (Scheme.evaluation_ne_zero_iff_mem_basicOpen Z (genericPoint Z) hξ _).mp ?_
  dsimp only [GlobalTheory.ProjBlowup.pullFormSec]
  have hle : (pullO (f ≫ prB n k) 1).U j ≤
      (Opens.map (f ≫ prB n k).base).obj (GlobalTheory.ProjSpace.chart ℤ (n k) (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k)) :=
    le_rfl
  have e := pullForm_X_eq_pullRatio (f ≫ prB n k) ((pullO (f ≫ prB n k) 1).U j)
    (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k) hle l (isHomogeneous_X ℤ l)
  have key := GlobalTheory.CompanionTheory.MPDict.FnDeg.eval_pullRatio_comp f (prB n k) (genericPoint Z)
    (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k) hxj l
  have h2 : (CommRingCat.Hom.hom (Scheme.Hom.residueFieldMap f (genericPoint Z)))
      (GlobalTheory.CompanionTheory.MPDict.ptCoord (f (genericPoint Z)) ⟨k, l⟩) ≠ 0 := (map_ne_zero _).mpr hne
  convert h2 using 1
  refine Eq.trans ?_ key.symm
  exact congrArg (ConcreteCategory.hom (Z.evaluation _ (genericPoint Z) hξ)) e

end GlobalTheory.CompanionTheory.MixZ.VertGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.O1ClassPullbackNaturality
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MixZ

def chartPullPullO {R : Type} [CommRing R] {N : ℕ} {S T : Scheme.{0}} (r : T ⟶ S) (φ : S ⟶ PSpace R N) :
    ChartPull (pullO (r ≫ φ) 1) (pullO φ 1) r where
  idx i := i
  le _ _ h := h
  g y i j hi hj := by
    have hle : (pullO (r ≫ φ) 1).U i ⊓ (pullO (r ≫ φ) 1).U j ≤
        r ⁻¹ᵁ ((pullO φ 1).U i ⊓ (pullO φ 1).U j) := fun _ h => h
    have hm : r y ∈ (pullO φ 1).U i ⊓ (pullO φ 1).U j := ⟨hi, hj⟩
    have ev : (((pullO φ 1).g i j : Γ(S, (pullO φ 1).U i ⊓ (pullO φ 1).U j)ˣ) :
        Γ(S, (pullO φ 1).U i ⊓ (pullO φ 1).U j)) = pullRatio φ _ i inf_le_left j :=
      (Units.val_pow_eq_pow_val _ _).trans (pow_one _)
    have ev' : (((pullO (r ≫ φ) 1).g i j : Γ(T, (pullO (r ≫ φ) 1).U i ⊓ (pullO (r ≫ φ) 1).U j)ˣ) :
        Γ(T, (pullO (r ≫ φ) 1).U i ⊓ (pullO (r ≫ φ) 1).U j)) = pullRatio (r ≫ φ) _ i inf_le_left j :=
      (Units.val_pow_eq_pow_val _ _).trans (pow_one _)
    have e : (pullO (r ≫ φ) 1).g i j = res hle (pullU r _ ((pullO φ 1).g i j)) := by
      apply Units.ext
      refine ev'.trans (Eq.trans ?_ (congrArg (r.appLE _ _ hle).hom ev).symm)
      exact (appLE_pullRatio (hi := inf_le_left) r hle).symm
    rw [e, gm_res (𝟙 T) y hle ⟨hi, hj⟩, gm_pull (𝟙 T) r y _ hm, Category.id_comp]

theorem cls_pullO_comp {R : Type} [CommRing R] {N : ℕ} {S T : Scheme.{0}} (r : T ⟶ S) (φ : S ⟶ PSpace R N) :
    cls (pullO (r ≫ φ) 1) (isLB_pullO _ 1) = CechPic.pull r (cls (pullO φ 1) (isLB_pullO _ 1)) := by
  rw [← cls_pull (isLB_pullO φ 1) r (pull_isLB (isLB_pullO φ 1) r)]
  exact (cls_eq_iff _ _).2 (LBIso.chartPull (chartPullPullO r φ)
    (chartPullPull (pullO φ 1) r) (PolBaseChange.lbIso_refl (isLB_pullO φ 1)))

end GlobalTheory.CompanionTheory.MixZ
end
end

