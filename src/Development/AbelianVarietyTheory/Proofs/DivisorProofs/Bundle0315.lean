module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import GroundTheory.FunctionField.PlaceSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0286
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafHomEquivNaturalSections
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FreeHom

variable {R : Type} [CommRing R]

theorem val_eq {P : PSh} {G : Shv R} (s : (free R).obj P ⟶ G) (U : Scheme.{0}) (x : P.obj (op U)) :
    val s U x = ((toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom).app (op U)).hom
      (ModuleCat.freeMk (ULift.up x)) := rfl

theorem freePresheaf_map_freeMk (P : PSh) {U V : Scheme.{0}ᵒᵖ} (g : U ⟶ V) (x : P.obj U) :
    (((freeP R).obj P).map g).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (P.map g x)) := by
  change ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map (P.map g))).hom (ModuleCat.freeMk (ULift.up x)) = _
  exact ModuleCat.free_map_apply _ _

theorem freePresheaf_map_app_freeMk {P P' : PSh} (f : P' ⟶ P) (U : Scheme.{0}ᵒᵖ) (x : P'.obj U) :
    (((freeP R).map f).app U).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (f.app U x)) := by
  change ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map (f.app U))).hom (ModuleCat.freeMk (ULift.up x)) = _
  exact ModuleCat.free_map_apply _ _

theorem ext {P : PSh} {G : Shv R} (s s' : (free R).obj P ⟶ G) (h : ∀ U x, val s U x = val s' U x) : s = s' := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ G.property
  apply NatTrans.ext
  funext U
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  have hx := h U.unop x
  rw [val_eq, val_eq] at hx
  exact hx

def descP (P : PSh) (G : Shv R) (φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x)) :
    (freeP R).obj P ⟶ G.obj where
  app U := ModuleCat.freeDesc (TypeCat.ofHom fun x => φ U.unop x.down)
  naturality U V g := by
    apply ModuleCat.free_hom_ext
    rintro ⟨x⟩
    change (ModuleCat.freeDesc _).hom ((((freeP R).obj P).map g).hom (ModuleCat.freeMk (ULift.up x))) =
      (G.obj.map g).hom ((ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up x)))
    rw [freePresheaf_map_freeMk]
    erw [ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact hφ V.unop U.unop g.unop x

def desc (P : PSh) (G : Shv R) (φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x)) :
    (free R).obj P ⟶ G :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).symm (descP P G φ hφ)

theorem val_desc (P : PSh) (G : Shv R) (φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x))
    (U : Scheme.{0}) (x : P.obj (op U)) : val (desc P G φ hφ) U x = φ U x := by
  rw [val_eq]
  have key : toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ (desc P G φ hφ).hom = descP P G φ hφ := by
    have hs := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).apply_symm_apply
      (descP P G φ hφ)
    rw [Adjunction.homEquiv_unit] at hs
    exact hs
  rw [key]
  change (ModuleCat.freeDesc _).hom (ModuleCat.freeMk (ULift.up x)) = _
  erw [ModuleCat.freeDesc_apply]
  rfl

private theorem val_nat_lemma {P : PSh} {F : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (η : (freeP R).obj P ⟶ F)
    {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (P.map g.op x))) =
      (F.map g.op).hom ((η.app (op U)).hom (ModuleCat.freeMk (ULift.up x))) :=
  calc (η.app (op V)).hom (ModuleCat.freeMk (ULift.up (P.map g.op x)))
      = (η.app (op V)).hom ((((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x))) :=
        congrArg (η.app (op V)).hom (freePresheaf_map_freeMk P g.op x).symm
    _ = _ := congrArg (fun k => k.hom (ModuleCat.freeMk (ULift.up x))) (η.naturality g.op)

theorem val_nat {P : PSh} {G : Shv R} (s : (free R).obj P ⟶ G) (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)) :
    val s V (P.map g.op x) = Sec.res g (val s U x) := by
  rw [val_eq, val_eq]
  exact val_nat_lemma _ g x

theorem val_free_map {P P' : PSh} (f : P' ⟶ P) {G : Shv R} (s : (free R).obj P ⟶ G) (U : Scheme.{0}) (x : P'.obj (op U)) :
    val ((free R).map f ≫ s) U x = val s U (f.app (op U) x) := by
  rw [val_eq, val_eq]
  have hn : toSheafify Scheme.etaleTopology ((freeP R).obj P') ≫ ((free R).map f ≫ s).hom
      = (freeP R).map f ≫ toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ s.hom :=
    (toSheafify_naturality_assoc Scheme.etaleTopology ((freeP R).map f) s.hom).symm
  rw [hn]
  change ((toSheafify _ _ ≫ s.hom).app (op U)).hom ((((freeP R).map f).app (op U)).hom (ModuleCat.freeMk (ULift.up x))) = _
  rw [freePresheaf_map_app_freeMk]

theorem val_comp {P : PSh} {G G' : Shv R} (s : (free R).obj P ⟶ G) (ψ : G ⟶ G') (U : Scheme.{0}) (x : P.obj (op U)) :
    val (s ≫ ψ) U x = Sec.map ψ (val s U x) := rfl

theorem val_add {P : PSh} {G : Shv R} (s s' : (free R).obj P ⟶ G) (U : Scheme.{0}) (x : P.obj (op U)) :
    val (s + s') U x = val s U x + val s' U x := rfl

def valHom (P : PSh) (G : Shv R) (U : Scheme.{0}) (x : P.obj (op U)) : ((free R).obj P ⟶ G) →+ Sec G U :=
  AddMonoidHom.mk' (fun s => val s U x) (fun s s' => val_add s s' U x)

theorem val_zsmul {P : PSh} {G : Shv R} (s : (free R).obj P ⟶ G) (m : ℤ) (U : Scheme.{0}) (x : P.obj (op U)) :
    val (m • s) U x = m • val s U x := by
  exact map_zsmul (valHom P G U x) m s

theorem main : ∀ (R : Type) [CommRing R] (P : PSh) (G : Shv R), (∀ s s' : (free R).obj P ⟶ G, (∀ U x, val s U x = val s' U x) → s = s') ∧ (∀ φ : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), φ V (P.map g.op x) = Sec.res g (φ U x)) → ∃ s : (free R).obj P ⟶ G, ∀ U x, val s U x = φ U x) ∧ (∀ (s : (free R).obj P ⟶ G) (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), val s V (P.map g.op x) = Sec.res g (val s U x)) ∧ (∀ (P' : PSh) (f : P' ⟶ P) (s : (free R).obj P ⟶ G) U x, val ((free R).map f ≫ s) U x = val s U (f.app (op U) x)) ∧ (∀ (G' : Shv R) (ψ : G ⟶ G') (s : (free R).obj P ⟶ G) U x, val (s ≫ ψ) U x = Sec.map ψ (val s U x)) ∧ ∀ (s s' : (free R).obj P ⟶ G) (m : ℤ) U x, val (s + s') U x = val s U x + val s' U x ∧ val (m • s) U x = m • val s U x := by
  intro R _ P G
  exact ⟨fun s s' h => ext s s' h, fun φ hφ => ⟨desc P G φ hφ, val_desc P G φ hφ⟩,
    fun s V U g x => val_nat s V U g x, fun P' f s U x => val_free_map f s U x,
    fun G' ψ s U x => val_comp s ψ U x, fun s s' m U x => ⟨val_add s s' U x, val_zsmul s m U x⟩⟩

end GlobalTheory.EtC.FreeHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankIffNonzeroMinor
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem rank_eq_iff_exists_minor_ne_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) :
    Y.rank = a ↔ ∃ J, minor Y J ≠ 0 := by
  constructor
  · intro hr
    obtain ⟨κ, f, hinj, hspan, hli⟩ := exists_linearIndependent' k Y.col
    haveI : Finite κ := Finite.of_injective f hinj
    haveI : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = a := by
      rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_cols, hr]
    let e : κ ≃ Fin a := Fintype.equivFinOfCardEq hcard
    let J : Fin a ↪ Fin d := ⟨f ∘ e.symm, hinj.comp e.symm.injective⟩
    refine ⟨J, ?_⟩
    have hc : (Y.submatrix id J).col = (Y.col ∘ f) ∘ e.symm := by
      funext j i; rfl
    have hli' : LinearIndependent k (Y.submatrix id J).col := by
      rw [hc]; exact hli.comp e.symm e.symm.injective
    have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hli'
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  · rintro ⟨J, hJ⟩
    have hu : IsUnit (Y.submatrix id J) := (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hJ)
    have hli' := Matrix.linearIndependent_rows_iff_isUnit.mpr hu
    have hr : (Y.submatrix id J).row = (LinearMap.funLeft k k J) ∘ Y.row := by
      funext i j; rfl
    rw [hr] at hli'
    have hli := LinearIndependent.of_comp _ hli'
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hli, Fintype.card_fin]

end GlobalTheory.RankFibreKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldOneVariableTranscendentalFiniteAndE
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

open IntermediateField

theorem finiteDimensional_adjoin_of_trdeg_le_one {k F : Type} [Field k] [Field F] [Algebra k F]
    [Algebra.EssFiniteType k F] (htr : Algebra.trdeg k F ≤ 1) (x : F) (hx : Transcendental k x) :
    FiniteDimensional k⟮x⟯ F := by
  have hind : AlgebraicIndependent k (fun _ : Unit => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have hb : IsTranscendenceBasis k (fun _ : Unit => x) :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
  have halg : Algebra.IsAlgebraic k⟮x⟯ F := by
    have := hb.isAlgebraic_field
    rwa [Set.range_const] at this
  have : Algebra.EssFiniteType k⟮x⟯ F := Algebra.EssFiniteType.of_comp k k⟮x⟯ F
  obtain ⟨S, hS⟩ := IntermediateField.fg_top_iff.mpr this
  have hfin : FiniteDimensional k⟮x⟯ (adjoin k⟮x⟯ (S : Set F)) :=
    IntermediateField.finiteDimensional_adjoin fun y _ => (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  rw [hS] at hfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := k⟮x⟯) (E := F)).toLinearEquiv

theorem essFiniteType_trdeg_of_isFF {k F : Type} [Field k] [Field F] [Algebra k F] (h : IsFF k F) :
    Algebra.EssFiniteType k F ∧ Algebra.trdeg k F ≤ 1 := by
  obtain ⟨t, ht, hfin⟩ := h
  have h1 : Algebra.EssFiniteType k k⟮t⟯ :=
    IntermediateField.essFiniteType_iff.mpr ⟨{t}, by simp⟩
  refine ⟨Algebra.EssFiniteType.comp k k⟮t⟯ F, ?_⟩
  open IntermediateField.algebraAdjoinAdjoin in
  have : Algebra.IsAlgebraic (Algebra.adjoin k {t}) F := Algebra.IsAlgebraic.trans _ k⟮t⟯ _
  have hind : AlgebraicIndependent k (fun _ : Unit => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  have hb : IsTranscendenceBasis k (fun _ : Unit => t) :=
    hind.isTranscendenceBasis_iff_isAlgebraic.mpr (by rwa [Set.range_const])
  rw [← hb.cardinalMk_eq_trdeg]
  simp

theorem isFF_main : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], IsFF k F →
    (∀ x : F, Transcendental k x → FiniteDimensional k⟮x⟯ F) ∧
    ∀ (E : Type) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k E := by
  intro k F _ _ _ h
  obtain ⟨hfg, htr⟩ := essFiniteType_trdeg_of_isFF h
  refine ⟨fun x hx => finiteDimensional_adjoin_of_trdeg_le_one htr x hx, ?_⟩
  intro E _ _ _ _ _
  have hfgE : Algebra.EssFiniteType k E := Algebra.EssFiniteType.comp k F E
  have h0 : Algebra.trdeg F E = 0 := trdeg_eq_zero_iff.mpr inferInstance
  have htrE : Algebra.trdeg k E ≤ 1 := by
    rw [← trdeg_add_eq k F, h0, add_zero]; exact htr
  obtain ⟨t, ht, _⟩ := h
  have ht' : Transcendental k (algebraMap F E t) :=
    (transcendental_algebraMap_iff (algebraMap F E).injective).mpr ht
  exact ⟨algebraMap F E t, ht', finiteDimensional_adjoin_of_trdeg_le_one htrE _ ht'⟩

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculus
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

namespace GlobalTheory.Nef.OrdCalc

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem vne (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x ≠ 0 := (map_ne_zero v.1).2 hx

theorem ord_mul (v : Place k F) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    ord v (x * y) = ord v x + ord v y := by
  unfold ord
  rw [map_mul, WithZero.log_mul (vne v hx) (vne v hy)]; ring

theorem ord_zpow (v : Place k F) (x : F) (m : ℤ) : ord v (x ^ m) = m * ord v x := by
  unfold ord
  rw [map_zpow₀, WithZero.log_zpow]; simp [smul_eq_mul]

theorem le_one_iff (v : Place k F) (x : F) (hx : x ≠ 0) : v.1 x ≤ 1 ↔ 0 ≤ ord v x := by
  unfold ord
  rw [← WithZero.log_le_log (vne v hx) one_ne_zero, WithZero.log_one, neg_nonneg]

theorem le_iff (v : Place k F) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x := by
  unfold ord
  rw [← WithZero.log_le_log (vne v hx) (vne v hy), neg_le_neg_iff]

theorem eq_one_iff (v : Place k F) (x : F) (hx : x ≠ 0) : v.1 x = 1 ↔ ord v x = 0 := by
  have h1 := WithZero.log_le_log (vne v hx) (one_ne_zero (α := WithZero (Multiplicative ℤ)))
  have h2 := WithZero.log_le_log (one_ne_zero (α := WithZero (Multiplicative ℤ))) (vne v hx)
  rw [WithZero.log_one] at h1 h2
  unfold ord
  constructor
  · intro h; rw [h, WithZero.log_one]; simp
  · intro h
    exact le_antisymm (h1.1 (by omega)) (h2.1 (by omega))

theorem exists_unif (v : Place k F) : ∃ π : F, π ≠ 0 ∧ ord v π = 1 := by
  obtain ⟨π, hπ⟩ := v.2.1 (WithZero.exp (-1 : ℤ))
  refine ⟨π, ?_, ?_⟩
  · rintro rfl; rw [map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
  · unfold ord; rw [hπ, WithZero.log_exp]; simp

theorem nrm_max (v : Place k F) (n : ℕ) (x : Fin n → F) (hx : x ≠ 0) :
    ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i) := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hx
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨i0, Finset.mem_univ _⟩ (fun i => v.1 (x i))
  have hle : ∀ j, v.1 (x j) ≤ v.1 (x i) := fun j => by
    rw [← hi]; exact Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ j)
  refine ⟨i, ?_, hi, ?_, hle⟩
  · intro h0
    have := hle i0
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi0 this
  · unfold ordVec ord nrm; rw [hi]

theorem nrm_smul (v : Place k F) (n : ℕ) (x : Fin n → F) (c : F) :
    nrm v (c • x) = v.1 c * nrm v x := by
  unfold nrm
  apply le_antisymm
  · apply Finset.sup_le; intro i _
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_mul' le_rfl (Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ i))
  · rcases isEmpty_or_nonempty (Fin n) with h | h
    · simp [Finset.univ_eq_empty]
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i => v.1 (x i))
      rw [hi]
      calc v.1 c * v.1 (x i) = v.1 ((c • x) i) := by simp
      _ ≤ _ := Finset.le_sup (f := fun i => v.1 ((c • x) i)) (Finset.mem_univ i)

theorem nrm_mulVec_le (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) : nrm v (u.mulVec x) ≤ nrm v x := by
  unfold nrm
  apply Finset.sup_le; intro i _
  simp only [Matrix.mulVec, dotProduct]
  apply Valuation.map_sum_le
  intro j _
  rw [map_mul]
  calc v.1 (u i j) * v.1 (x j) ≤ 1 * Finset.univ.sup (fun i => v.1 (x i)) :=
        mul_le_mul' (hu i j) (Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ j))
  _ = _ := one_mul _

theorem mul_int (v : Place k F) (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) (hu' : ∀ i j, v.1 (u' i j) ≤ 1) : ∀ i j, v.1 ((u * u') i j) ≤ 1 := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Valuation.map_sum_le
  intro l _
  rw [map_mul]
  calc v.1 (u i l) * v.1 (u' l j) ≤ 1 * 1 := mul_le_mul' (hu i l) (hu' l j)
  _ = 1 := one_mul _

theorem det_adj_int (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) : v.1 u.det ≤ 1 ∧ ∀ i j, v.1 (u.adjugate i j) ≤ 1 := by
  let M : Matrix (Fin n) (Fin n) v.O := fun i j => ⟨u i j, (Valuation.mem_valuationSubring_iff _ _).2 (hu i j)⟩
  have hM : M.map v.O.subtype = u := by ext i j; rfl
  constructor
  · have e : u.det = ((M.det : v.O) : F) := by
      rw [← hM]; exact (RingHom.map_det v.O.subtype M).symm
    rw [e]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (M.det).2
  · intro i j
    have e : u.adjugate i j = ((M.adjugate i j : v.O) : F) := by
      rw [← hM]
      have := congrFun (congrFun (RingHom.map_adjugate v.O.subtype M) i) j
      exact this.symm
    rw [e]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (M.adjugate i j).2

theorem unimod_mul_inv (v : Place k F) (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F)
    (hu : Unimod v u) (hu' : Unimod v u') : Unimod v (u * u') ∧ Unimod v u⁻¹ := by
  refine ⟨⟨mul_int v n u u' hu.1 hu'.1, by rw [Matrix.det_mul, map_mul, hu.2, hu'.2, one_mul]⟩, ?_⟩
  have hd : u.det ≠ 0 := fun h => by have := hu.2; rw [h, map_zero] at this; exact zero_ne_one this
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hu.2, inv_one, one_mul]
    exact (det_adj_int v n u hu.1).2 i j
  · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, hu.2, inv_one]

theorem nrm_unimod (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : Unimod v u) : nrm v (u.mulVec x) = nrm v x := by
  have hd : IsUnit u.det := isUnit_iff_ne_zero.2 (fun h => by
    have := hu.2; rw [h, map_zero] at this; exact zero_ne_one this)
  apply le_antisymm (nrm_mulVec_le v n u x hu.1)
  have h := nrm_mulVec_le v n u⁻¹ (u.mulVec x) (unimod_mul_inv v n u u hu hu).2.1
  rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul u hd, Matrix.one_mulVec] at h

end GlobalTheory.Nef.OrdCalc

open GlobalTheory.Nef.OrdCalc in
theorem GlobalTheory.Nef.ord_calculus : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], ∀ v : Place k F, (∀ x y : F, x ≠ 0 → y ≠ 0 → ord v (x * y) = ord v x + ord v y) ∧ (∀ x : F, x ≠ 0 → ∀ m : ℤ, ord v (x ^ m) = m * ord v x) ∧ (∀ x : F, x ≠ 0 → (v.1 x ≤ 1 ↔ 0 ≤ ord v x)) ∧ (∀ x : F, x ≠ 0 → (v.1 x = 1 ↔ ord v x = 0)) ∧ (∀ x y : F, x ≠ 0 → y ≠ 0 → (v.1 x ≤ v.1 y ↔ ord v y ≤ ord v x)) ∧ (∃ π : F, π ≠ 0 ∧ ord v π = 1) ∧ (∀ (n : ℕ) (x : Fin n → F), x ≠ 0 → ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i)) ∧ (∀ (n : ℕ) (x : Fin n → F) (c : F), nrm v (c • x) = v.1 c * nrm v x) ∧ (∀ (n : ℕ) (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F), Unimod v u → nrm v (u.mulVec x) = nrm v x) ∧ (∀ (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F), Unimod v u → Unimod v u' → Unimod v (u * u') ∧ Unimod v u⁻¹) := by
  intro k F _ _ _ v
  exact ⟨fun x y hx hy => ord_mul v x y hx hy, fun x _ m => ord_zpow v x m,
    fun x hx => le_one_iff v x hx, fun x hx => eq_one_iff v x hx, fun x y hx hy => le_iff v x y hx hy,
    exists_unif v, fun n x hx => nrm_max v n x hx, fun n x c => nrm_smul v n x c,
    fun n u x hu => nrm_unimod v n u x hu, fun n u u' hu hu' => unimod_mul_inv v n u u' hu hu'⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceSumOrderEqFinrank
section
set_option autoImplicit false

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef.FundId

variable {k F : Type} [Field k] [Field F] [Algebra k F]

noncomputable def toRing (v : Place k F) : GroundTheory.FunctionField.Place k F where
  ring := v.1.valuationSubring
  ne_top := by
    intro h
    obtain ⟨x, hx⟩ := v.2.1 (WithZero.exp 1)
    have hm : x ∈ v.1.valuationSubring := h ▸ ValuationSubring.mem_top _
    rw [Valuation.mem_valuationSubring_iff, hx, ← WithZero.exp_zero, WithZero.exp_le_exp] at hm
    omega
  algebraMap_mem c := by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · exact (v.2.2 c hc).le

theorem valuation_toRing [GroundTheory.FunctionField.IsFunctionField k F] (v : Place k F) :
    (toRing v).valuation = v.1 := by
  refine GroundTheory.FunctionField.valuation_eq_of_isEquiv ?_ (toRing v).valuation_surjective v.2.1
  refine Valuation.isEquiv_iff_val_le_one.2 fun {x} => ?_
  rw [GroundTheory.FunctionField.Place.valuation_le_one_iff]
  rfl

theorem ord_toRing [GroundTheory.FunctionField.IsFunctionField k F] (v : Place k F) (x : F) :
    (toRing v).ord x = ord v x := by
  unfold ord
  rw [← valuation_toRing]
  rfl

theorem toRing_injective [GroundTheory.FunctionField.IsFunctionField k F] :
    Function.Injective (toRing : Place k F → _) := fun v w h =>
  Subtype.ext (by rw [← valuation_toRing, ← valuation_toRing, h])

theorem toRing_surjective [GroundTheory.FunctionField.IsFunctionField k F] :
    Function.Surjective (toRing : Place k F → _) := by
  intro w
  refine ⟨⟨w.valuation, w.valuation_surjective, fun c hc => ?_⟩, ?_⟩
  · exact w.valuation_algebraMap' hc
  · ext x
    exact w.valuation_le_one_iff x

theorem deg_eq_one [IsAlgClosed k] [GroundTheory.FunctionField.IsFunctionField k F]
    (w : GroundTheory.FunctionField.Place k F) : w.deg = 1 := by
  have h : Function.Bijective (algebraMap k w.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have e : k ≃ₗ[k] w.ResidueField :=
    LinearEquiv.ofBijective (Algebra.linearMap k w.ResidueField) h
  have := e.finrank_eq
  rw [Module.finrank_self] at this
  exact this.symm

theorem sum_ord_eq_finrank : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ (v : Place k F) (π : F), π ≠ 0 → ord v π = 1 → {p | ρ p = v}.Finite ∧ ∑ᶠ p ∈ {p | ρ p = v}, ord p (algebraMap F E π) = Module.finrank F E := by
  intro k F E _ _ _ _ _ _ _ _ _ _ hF ρ hρ v π _ hπ
  classical
  haveI : GroundTheory.FunctionField.IsFunctionField k F := ⟨hF⟩
  haveI : GroundTheory.FunctionField.IsFunctionField k E :=
    GroundTheory.FunctionField.IsFunctionField.of_finiteDimensional (k := k) (K := F)
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  have key : ∀ p : Place k E, ρ p = v ↔ (toRing p).LiesOver (toRing v) := by
    intro p
    have h1 : (toRing p).LiesOver (toRing (ρ p)) := by
      ext x
      exact hρ p x
    constructor
    · rintro rfl; exact h1
    · intro h
      exact toRing_injective (GroundTheory.FunctionField.Place.ext (h1.symm.trans h))
  have hfin := (toRing v).finite_liesOver (K' := E)
  have hfin' : {p | ρ p = v}.Finite := by
    refine (hfin.preimage toRing_injective.injOn).subset fun p hp => (key p).1 hp
  refine ⟨hfin', ?_⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin', ← (toRing v).sum_ramificationIdx_mul_inertiaDeg (K' := E),
    Nat.cast_sum]
  refine Finset.sum_bij (fun p _ => toRing p) ?_ ?_ ?_ ?_
  · intro p hp
    simpa [key] using hp
  · intro p _ q _ h
    exact toRing_injective h
  · intro w hw
    obtain ⟨p, rfl⟩ := toRing_surjective w
    exact ⟨p, by simpa [key] using hw, rfl⟩
  · intro p hp
    have h : (toRing p).LiesOver (toRing v) := by simpa [key] using hp
    rw [← ord_toRing, h.ord_algebraMap, ord_toRing, hπ, GroundTheory.FunctionField.Place.inertiaDeg,
      deg_eq_one, deg_eq_one]
    simp

end GlobalTheory.Nef.FundId
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralCompAddEquivRescaleStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale : ∀ (X Y : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (μ : Measure X) (μ' : Measure Y) (T : X ≃ₜ+ Y) (r : NNReal) (f : Y → ℂ) (γ : ℂ), μ.map T = r • μ' → HasGauss μ' f γ → HasGauss μ (fun x => f (T x)) ((r : ℝ) * γ) := by
  first | exact @GlobalTheory.KSp.hasGauss_comp_equiv | exact GlobalTheory.KSp.hasGauss_comp_equiv | (intros; apply GlobalTheory.KSp.hasGauss_comp_equiv <;> assumption)
end

