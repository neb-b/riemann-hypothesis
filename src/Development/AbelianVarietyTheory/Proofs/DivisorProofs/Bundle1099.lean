module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTopologicalKrullDimDiffOpenLt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.Div

theorem exists_finite_topologicalKrullDim_diff_lt :
    ∀ (T : Type) [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T] [T0Space T] (Z : Set T),
      IsClosed Z → ∃ S : Set T, S.Finite ∧ ∀ U : Set T, IsOpen U → S ⊆ U → ∀ d : ℕ,
        (topologicalKrullDim Z < (d + 1 : ℕ) → topologicalKrullDim (Z \ U : Set T) < (d : ℕ)) := by
  intro T _ _ _ _ Z _
  have hfin : (irreducibleComponents Z).Finite := NoetherianSpace.finite_irreducibleComponents
  have hne : ∀ K : irreducibleComponents Z, ∃ x : Z, x ∈ (K : Set Z) := fun K => K.2.1.nonempty
  choose p hp using hne
  haveI : Finite (irreducibleComponents Z) := hfin.to_subtype
  refine ⟨Set.range (fun K => (p K : T)), Set.finite_range _, fun U _ hSU d hd => ?_⟩
  have hsub : (Z \ U : Set T) ⊆ Z := Set.diff_subset
  have hi : IsInducing (Set.inclusion hsub) := (IsEmbedding.inclusion hsub).isInducing
  have hcl : IsClosed {x : Z | (x : T) ∉ U} :=
    (IsOpen.preimage continuous_subtype_val ‹IsOpen U›).isClosed_compl
  refine Order.krullDim_lt_coe_iff.2 fun s => ?_
  have hm := IrreducibleCloseds.map_strictMono_of_isInducing hi
  let s' := s.map _ hm
  obtain ⟨K, hK, hsK⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (s'.last : Set Z) s'.last.isIrreducible
  let K' : IrreducibleCloseds Z := ⟨K, hK.1, isClosed_of_mem_irreducibleComponents K hK⟩
  have hlast : (s'.last : Set Z) ⊆ {x : Z | (x : T) ∉ U} := by
    have : s'.last = IrreducibleCloseds.map _ hi.continuous s.last := by
      simp [s']
    rw [this]
    refine closure_minimal ?_ hcl
    rintro _ ⟨y, -, rfl⟩
    exact y.2.2
  have hlt : s'.last < K' := by
    refine lt_of_le_of_ne hsK fun h => ?_
    have h1 : p ⟨K, hK⟩ ∈ (s'.last : Set Z) := by
      rw [h]; exact hp ⟨K, hK⟩
    exact hlast h1 (hSU ⟨⟨K, hK⟩, rfl⟩)
  have h2 := Order.krullDim_lt_coe_iff.1 hd (s'.snoc K' hlt)
  simp [s'] at h2
  exact h2

end GlobalTheory.Div
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapDoubleSpaceGenericPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPush

theorem exists_functionField_map_of_genericPoint :
    ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K)
      (ζ : Sp K ⟶ W.Z), ζ (IsLocalRing.closedPoint K) = genericPoint W.Z → ζ ≫ W.p₁ = spMap ψ₁ ≫ (ratOf Y).pt →
        ζ ≫ W.p₂ = spMap ψ₂ ≫ (ratOf Y).pt → ∃ j : W.Z.functionField →+* K, j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  intro F _ Y W K _ ψ₁ ψ₂ ζ h h₁ h₂
  have hs : ζ (IsLocalRing.closedPoint K) ⤳ genericPoint W.Z := h ▸ specializes_rfl
  let j : W.Z.functionField →+* K :=
    (W.Z.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (R := .of K) ζ).hom
  have e : spMap j ≫ W.Z.fromSpecStalk (genericPoint W.Z) = ζ := by
    change Spec.map (CommRingCat.ofHom j) ≫ W.Z.fromSpecStalk (genericPoint W.Z) = ζ
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact spMap_stalkClosedPointTo ζ
  have key : ∀ (p : W.Z ⟶ Y.X) [IsDominant p] (ψ : Y.Fn →+* K), ζ ≫ p = spMap ψ ≫ (ratOf Y).pt →
      j.comp (functionFieldMap p) = ψ := by
    intro p _ ψ hp
    have e2 : spMap (j.comp (functionFieldMap p)) ≫ Y.X.fromSpecStalk (genericPoint Y.X) =
        spMap ψ ≫ Y.X.fromSpecStalk (genericPoint Y.X) := by
      change Spec.map (CommRingCat.ofHom (j.comp (functionFieldMap p))) ≫ genericFieldPoint Y.X = _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, specMap_functionFieldMap,
        ← Category.assoc]
      change (spMap j ≫ W.Z.fromSpecStalk (genericPoint W.Z)) ≫ p = _
      rw [e, hp]
      rfl
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp e2))
  exact ⟨j, key W.p₁ ψ₁ h₁, key W.p₂ ψ₂ h₂⟩

end GlobalTheory.FlagPush
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLLatticeSpannedByGLColumnsEqFullLattice
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

theorem exists_lat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A)
    (L : Submodule K.O B.A), GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ q : GLw a w, GlobalTheory.TwLat.lat e b q = L := by
  intro E _ _ _ w K e a B b L hL
  obtain ⟨hfg, hspan⟩ := hL
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors K.O B.A := ⟨fun {r x} h => by
    rw [← algebraMap_smul K.E r x] at h
    rcases smul_eq_zero.mp h with h | h
    · left; exact (IsFractionRing.injective K.O K.E) (by simpa using h)
    · right; exact h⟩
  haveI : Module.Free K.O L := Module.free_of_finite_type_torsion_free'
  let y := Module.Free.chooseBasis K.O L
  let v : Module.Free.ChooseBasisIndex K.O L → B.A := fun i => (y i : B.A)
  have hli : LinearIndependent K.O v := y.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliE : LinearIndependent K.E v := (LinearIndependent.iff_fractionRing K.O K.E).mp hli
  have hLv : Submodule.span K.O (Set.range v) = L := by
    have : Set.range v = L.subtype '' Set.range y := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, y.span_eq, Submodule.map_subtype_top]
  have hspE : Submodule.span K.E (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower K.O K.E, hLv]; exact hspan
  let c := Module.Basis.mk hliE hspE.ge
  let c' := c.reindex (c.indexEquiv b)
  let U : (Matrix (Fin a) (Fin a) K.E)ˣ :=
    ⟨b.toMatrix c', c'.toMatrix b, b.toMatrix_mul_toMatrix_flip c', c'.toMatrix_mul_toMatrix_flip b⟩
  refine ⟨Units.map (e.toRingHom.mapMatrix : Matrix (Fin a) (Fin a) K.E →+* _).toMonoidHom U, ?_⟩
  rw [latOf_eq, ← hLv]
  have hcol : ∀ j, (ofCrd e b fun i =>
      (Units.map (e.toRingHom.mapMatrix : Matrix (Fin a) (Fin a) K.E →+* _).toMonoidHom U).val i j) = c' j := by
    intro j
    rw [← ofCrd_crd e b (c' j)]
    congr 1
  simp only [hcol]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨(c.indexEquiv b).symm j, ?_⟩
    simp [c', c, v]
  · rintro ⟨i, rfl⟩
    refine ⟨c.indexEquiv b i, ?_⟩
    simp [c', c, v]

end GlobalTheory.TwOrbLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingSecsOfClsEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.CechPic

theorem exists_generating_secs_of_cls_eq : ∀ (X : Scheme.{0}) (L A : LB X) (hL : L.IsLB) (hA : A.IsLB), cls L hL = cls A hA → ∀ (ι : Type) (u : ι → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∃ v : ι → A.Sec, ⨆ i, nonzeroLocus (v i) = ⊤ := by
  intro X L A hL hA h ι u hu
  have hiso : LBIso A L := (cls_eq_iff hA hL).1 h.symm
  choose v hv using fun i => GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso hA hL hiso (u i)
  refine ⟨v, ?_⟩
  simp only [hv]
  exact hu

end GlobalTheory.CechPic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalIffEtaProd
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.QuadRecip

open GlobalTheory.QuadSymbol

theorem exists_global_iff_etaProd (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (x : FinFam K) (y : InfFam K)
    (hx : AlmostNorm K L x) :
    (∃ t : Kˣ, (∀ v, x v / finDiag K t v ∈ normGroup K L (v.adicCompletion K)) ∧
        ∀ w, y w / infDiag K t w ∈ normGroup K L w.Completion) ↔
      etaProd K L x y = 1 :=
  (exactSequence K L).2.2.1 x y hx

theorem ringEquivReal_infDiag {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}
    (hw : w.IsReal) (t : Kˣ) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infDiag K t w : (w.Completion)ˣ) : w.Completion) =
      InfinitePlace.embedding_of_isReal hw (t : K) :=
  by
    simp [infDiag, QuadSymbol.toUnits, InfinitePlace.Completion.algebraMap_apply]

theorem mem_normGroup_of_pos {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] {w : InfinitePlace K} (hw : w.IsReal) (z : (w.Completion)ˣ)
    (hz : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (z : w.Completion)) :
    z ∈ normGroup K L w.Completion := by
  obtain ⟨δ, b, -, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  rw [mem_normGroup_iff_form b h0 h1]
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  refine ⟨e.symm (Real.sqrt (e z)), 0, e.injective ?_⟩
  simp [Real.sq_sqrt hz.le]

theorem mem_normGroup_iff_pos {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hL : IsTotallyComplex L)
    {w : InfinitePlace K} (hw : w.IsReal) (z : (w.Completion)ˣ) :
    z ∈ normGroup K L w.Completion ↔
      0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (z : w.Completion) := by
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  refine ⟨fun hz => ?_, mem_normGroup_of_pos hw z⟩
  have hne : e (z : w.Completion) ≠ 0 := (map_ne_zero e).2 z.ne_zero
  refine lt_of_le_of_ne (not_lt.1 fun hlt => ?_) hne.symm
  have hm : (-z) ∈ normGroup K L w.Completion :=
    mem_normGroup_of_pos hw (-z) (by rw [Units.val_neg, map_neg]; exact neg_pos.2 hlt)
  have h1 : (-1 : (w.Completion)ˣ) = z * (-z)⁻¹ := by rw [inv_neg, mul_neg, mul_inv_cancel]
  exact SignCount.neg_one_not_mem_normGroup hL hw (h1 ▸ mul_mem hz (inv_mem hm))

end GlobalTheory.QuadRecip

namespace GlobalTheory.QuadRecip

open GlobalTheory.QuadSymbol


open Classical in
theorem prod_sign_eq {K : Type} [Field K] [NumberField K] (S : Finset {w : InfinitePlace K // w.IsReal})
    (f : InfinitePlace K → ℤˣ)
    (hf : ∀ w, f w = if (∃ hw : w.IsReal, (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ S) then -1 else 1) :
    ∏ w, f w = (-1) ^ S.card := by
  classical
  simp_rw [hf]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  congr 1
  have : (Finset.univ.filter fun w : InfinitePlace K =>
      ∃ hw : w.IsReal, (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ S) =
      S.map (Function.Embedding.subtype _) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨hw, h⟩
      exact ⟨_, h, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, hu⟩
  rw [this, Finset.card_map]


open Classical in
theorem exists_signs_iff_even (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hL : IsTotallyComplex L)
    (S : Finset {w : InfinitePlace K // w.IsReal}) :
    (∃ h : Kˣ, (∀ w : {w : InfinitePlace K // w.IsReal},
        (w ∈ S → InfinitePlace.embedding_of_isReal w.2 (h : K) < 0) ∧
        (w ∉ S → 0 < InfinitePlace.embedding_of_isReal w.2 (h : K))) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), finDiag K h v ∈ normGroup K L (v.adicCompletion K)) ↔
      Even S.card := by
  classical
  obtain ⟨δ, b, -, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hneg1 : ((-1 : ℤˣ) ≠ 1) := by decide
  constructor
  · rintro ⟨h, hsgn, hfin⟩
    have hpf := (productFormula K L h).2
    unfold etaProd at hpf
    have hf1 : ∀ v : HeightOneSpectrum (𝓞 K), eta K L (v.adicCompletion K) (finDiag K h v) = 1 :=
      fun v => eta_eq_one_iff.2 (hfin v)
    simp only [hf1, finprod_one, one_mul] at hpf
    rw [prod_sign_eq S _ (fun w => ?_)] at hpf
    · exact (neg_one_pow_eq_one_iff_even hneg1).1 hpf
    · by_cases hw : w.IsReal
      · have key := mem_normGroup_iff_pos hL hw (infDiag K h w)
        rw [ringEquivReal_infDiag hw h] at key
        by_cases hS : (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ S
        · rw [if_pos ⟨hw, hS⟩, eta_eq_neg_one_iff, key]
          exact not_lt.2 ((hsgn ⟨w, hw⟩).1 hS).le
        · rw [if_neg (by rintro ⟨hw', h'⟩; exact hS h'), eta_eq_one_iff, key]
          exact (hsgn ⟨w, hw⟩).2 hS
      · rw [if_neg (by rintro ⟨hw', _⟩; exact hw hw'), eta_eq_one_iff]
        exact Converse.mem_normGroup_of_isComplex b h0 h1 (InfinitePlace.not_isReal_iff_isComplex.1 hw) _
  · intro hS
    let P : InfinitePlace K → Prop := fun w =>
      ∃ hw : w.IsReal, (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ S
    let y : InfFam K := fun w => if P w then -1 else 1
    have hy : ∀ w, eta K L w.Completion (y w) = if P w then -1 else 1 := by
      intro w
      by_cases hP : P w
      · simp only [y, if_pos hP]
        exact eta_eq_neg_one_iff.2 (SignCount.neg_one_not_mem_normGroup hL hP.1)
      · simp only [y, if_neg hP]
        exact eta_eq_one_iff.2 (one_mem _)
    have hx : AlmostNorm K L (1 : FinFam K) := by
      refine Set.Finite.subset Set.finite_empty fun v hv => hv ?_
      exact one_mem _
    have hprod : etaProd K L 1 y = 1 := by
      unfold etaProd
      have hf1 : ∀ v : HeightOneSpectrum (𝓞 K),
          eta K L (v.adicCompletion K) ((1 : FinFam K) v) = 1 := fun v => eta_eq_one_iff.2 (one_mem _)
      simp only [hf1, finprod_one, one_mul]
      rw [prod_sign_eq S _ hy]
      exact hS.neg_one_pow
    obtain ⟨t, htf, hti⟩ := (exists_global_iff_etaProd K L 1 y hx).2 hprod
    refine ⟨t, fun w => ?_, fun v => ?_⟩
    · have key := (mem_normGroup_iff_pos hL w.2 _).1 (hti w.1)
      rw [Units.val_div_eq_div_val, map_div₀, ringEquivReal_infDiag w.2 t] at key
      have hP : P w.1 ↔ w ∈ S := ⟨by rintro ⟨_, h⟩; exact h, fun h => ⟨w.2, h⟩⟩
      constructor
      · intro hw
        have hyw : y w.1 = -1 := if_pos (hP.2 hw)
        rw [hyw, Units.val_neg, Units.val_one, map_neg, map_one] at key
        have := (div_pos_iff.1 key)
        rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
        · linarith
        · exact h2
      · intro hw
        have hyw : y w.1 = 1 := if_neg (fun h => hw (hP.1 h))
        rw [hyw, Units.val_one, map_one] at key
        exact (one_div_pos).1 key
    · have := htf v
      rw [Pi.one_apply, one_div, inv_mem_iff] at this
      exact this

theorem exists_signs_of_even (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hK : IsTotallyReal K) (hL : IsTotallyComplex L)
    (S : Finset (InfinitePlace K)) (hS : Even S.card) :
    ∃ h : Kˣ, (∀ w (hw : w ∈ S), InfinitePlace.embedding_of_isReal (hK.isReal w) (h : K) < 0) ∧
      (∀ w (hw : w ∉ S), 0 < InfinitePlace.embedding_of_isReal (hK.isReal w) (h : K)) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), finDiag K h v ∈ normGroup K L (v.adicCompletion K) := by
  classical
  let S' : Finset {w : InfinitePlace K // w.IsReal} := S.subtype _
  have hc : S'.card = S.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem fun w _ => hK.isReal w
  obtain ⟨h, hsgn, hfin⟩ := (exists_signs_iff_even K L hL S').2 (hc ▸ hS)
  refine ⟨h, fun w hw => (hsgn ⟨w, hK.isReal w⟩).1 ?_, fun w hw => (hsgn ⟨w, hK.isReal w⟩).2 ?_, hfin⟩
  · simpa [S'] using hw
  · simpa [S'] using hw

end GlobalTheory.QuadRecip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntersectionFormPicardDoubleSpace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_interForm_dbl : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∃ T : MultilinearMap (RingHom.id ℤ) (fun _ : Fin (Y.dim + 1) => Pic W.Z) ℤ, (∀ (σ : Equiv.Perm (Fin (Y.dim + 1))) (y : Fin (Y.dim + 1) → Pic W.Z), T (y ∘ σ) = T y) ∧ ∀ y : Fin (Y.dim + 1) → CartierDiv W.Z, T (fun i => toPic (y i)) = W.num y := by
  intro F _ Y W hW
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hv : DiffVanish (Y.dim + 1 + 1) (chiPic F (structureModule W.Z)) :=
    diffVanish_chiPic_of_isProjOver (algebraΓOfHom_algebraMap (W.p₁ ≫ Y.str)) (structureModule W.Z) W.proj
      (by rw [GlobalTheory.QCoh.suppDim_structureModule]; exact hW)
  refine ⟨hv.form, fun σ y => hv.form_comp_perm y σ, fun y => ?_⟩
  rw [hv.form_apply _ 0]
  show _ = interNum F (structureModule W.Z) fun i => toLB (y i)
  rw [interNum_eq_multiDiff F _ fun i => isLB_toLB (y i)]
  rfl

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuativeCriterionVarieties
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPush

theorem exists_lift_of_var : ∀ (F : Type) [Field F] (X Y : Var F) (f : Y.X ⟶ X.X), f ≫ X.str = Y.str → ∀ (K : Type) [Field K] (V : ValuationSubring K) (v₁ : Sp V ⟶ Y.X) (q₂ : Sp K ⟶ Y.X), q₂ ≫ f = spMap (algebraMap V K) ≫ v₁ ≫ f → ∃ v₂ : Sp V ⟶ Y.X, spMap (algebraMap V K) ≫ v₂ = q₂ ∧ v₂ ≫ f = v₁ ≫ f := by
  intro F _ X Y f hs K _ V v₁ q₂ hq
  haveI : IsProper (f ≫ X.str) := hs ▸ inferInstance
  haveI : UniversallyClosed f := UniversallyClosed.of_comp_of_isSeparated f X.str
  have hE : ValuativeCriterion.Existence f :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) f).1
  obtain ⟨⟨l⟩⟩ := hE { R := V, K := K, i₁ := q₂, i₂ := v₁ ≫ f, commSq := ⟨hq⟩ }
  exact ⟨l.l, l.fac_left, l.fac_right⟩

end GlobalTheory.FlagPush
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareMatrixImageSubmoduleContainsUniformiStatement
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_matrix_image_submodule_contains_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O) (N : Submodule O (Fin n → O)), ϖ ≠ 0 → (∀ y : Fin n → O, (fun a => ϖ * y a) ∈ N) → ∃ A : Matrix (Fin n) (Fin n) O, (∀ x, x ∈ N ↔ ∃ u, A *ᵥ u = x) ∧ A.det ≠ 0 := by
  first | exact @GlobalTheory.exists_square_matrix_of_submodule_between | exact GlobalTheory.exists_square_matrix_of_submodule_between | (intros; apply GlobalTheory.exists_square_matrix_of_submodule_between <;> assumption)
end

