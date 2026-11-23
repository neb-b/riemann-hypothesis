module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodConstantEqOfCardCmType
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet

namespace GlobalTheory.LatAlgebraic

theorem natAbs_discr_of_finrank_one (F : Type) [Field F] [NumberField F] (h : Module.finrank ℚ F = 1) :
    (discr F).natAbs = 1 := by
  have hb : (⊥ : Subalgebra ℚ F) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  let e : ℚ ≃ₐ[ℚ] F := (Algebra.botEquiv ℚ F).symm.trans ((Subalgebra.equivOfEq _ _ hb).trans Subalgebra.topEquiv)
  rw [← NumberField.discr_eq_discr_of_algEquiv (f := e), NumberField.discr_rat]
  rfl

theorem two_le_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] (h : UnramFin E) :
    2 ≤ Module.finrank ℚ (maximalRealSubfield E) := by
  by_contra hlt
  have h1 : Module.finrank ℚ (maximalRealSubfield E) = 1 := by
    have := Module.finrank_pos (R := ℚ) (M := maximalRealSubfield E)
    omega
  have hE := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (maximalRealSubfield E)
    (𝓞 (maximalRealSubfield E)) E (𝓞 E)
  have hU : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := h
  rw [hU, Ideal.absNorm_top, one_mul, natAbs_discr_of_finrank_one _ h1, one_pow] at hE
  have h2 : Module.finrank ℚ E = 2 := by
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E),
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, h1]
  have h3 := NumberField.abs_discr_gt_two (K := E) (by omega)
  have h4 : |(discr E : ℤ)| = 1 := by rw [Int.abs_eq_natAbs, hE]; rfl
  omega

theorem card_eq_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    {φ : I → E →+* ℂ} (h : IsCMType φ) : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E) := by
  have hreal : ∀ i j, φ i ≠ ComplexEmbedding.conjugate (φ j) := by
    intro i j hij
    obtain ⟨k, -, hk⟩ := h (φ i)
    have e : i = j := (hk i (Or.inl rfl)).trans (hk j (Or.inr hij)).symm
    subst e
    have hr : ComplexEmbedding.IsReal (φ i) := ComplexEmbedding.isReal_iff.mpr hij.symm
    exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex (InfinitePlace.mk (φ i)))
      (InfinitePlace.isReal_mk_iff.mpr hr)
  have hbij : Function.Bijective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))) := by
    refine ⟨?_, ?_⟩
    · rintro (i | i) (j | j) hij
      · simp only [Sum.elim_inl] at hij
        obtain ⟨k, -, hk⟩ := h (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl hij)]
      · exact absurd hij (hreal i j)
      · exact absurd hij.symm (hreal j i)
      · simp only [Sum.elim_inr] at hij
        have hij' : φ i = φ j := by
          simpa using congrArg ComplexEmbedding.conjugate hij
        obtain ⟨k, -, hk⟩ := h (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl hij')]
    · intro σ
      obtain ⟨k, hk, -⟩ := h σ
      rcases hk with hk | hk
      · exact ⟨Sum.inl k, hk.symm⟩
      · exact ⟨Sum.inr k, hk.symm⟩
  have h1 := Fintype.card_of_bijective hbij
  rw [Fintype.card_sum, NumberField.Embeddings.card E ℂ] at h1
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E),
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  omega

theorem gamma_nat_add (k n : ℕ) (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + n) = ((k - 1).factorial : ℝ) * ∏ j ∈ Finset.range n, ((k : ℝ) + j) := by
  induction n with
  | zero =>
    have : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hk]; ring
    simp only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    rw [this, Real.Gamma_nat_eq_factorial]
  | succ n ih =>
    have hpos : (k : ℝ) + n ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hpos, ih]
    ring

theorem exists_list_count {I : Type} [Fintype I] [DecidableEq I] (κ : I → ℕ) :
    ∃ u : List I, ∀ i, u.count i = κ i := by
  refine ⟨(∑ i, Multiset.replicate (κ i) i).toList, fun i => ?_⟩
  rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum', Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Multiset.count_replicate]
    simp [hj]
  · simp

theorem cmPeriodConstant_eq_of_card_cmType {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
    (hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)) (d s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) :
    C0 E d (2 * s) κ = GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) *
      (∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) * (2 * Real.pi / Real.sqrt d) ^ (∑ i, κ i) := by
  have hk : 1 ≤ 2 * s := by omega
  rw [cmValueConst_eq, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt, Finset.prod_congr rfl (fun i _ => gamma_nat_add (2 * s) (κ i) hk),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
  ring

theorem risingFactor_eq {I : Type} [Fintype I] (k : ℕ) (κ : I → ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor k κ =
      (-1) ^ (∑ i, κ i) * (((∏ i, ∏ j ∈ Finset.range (κ i), ((k : ℝ) + j)) : ℝ) : ℂ) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  rfl

end GlobalTheory.LatAlgebraic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCohomologousOfDeRhamSurjective
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt.Lift

variable {R : Type} [CommRing R] {X : Over (Sp R)}

def trivEquiv (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) : T.B ≃+* T.B₀ :=
  RingEquiv.ofBijective T.π ⟨(injective_iff_map_eq_zero T.π).2 fun b hb ↦ by
      have h := (T.ker b).1 hb
      rw [hT] at h
      exact Ideal.mem_bot.1 h, T.surj⟩

theorem trivEquiv_symm_π (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) (b : T.B) :
    (trivEquiv T hT).symm (T.π b) = b :=
  (trivEquiv T hT).symm_apply_apply b

def trivPt (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) : Pt X T.B :=
  Over.homMk (U := SpAlg R T.B) (spMap ((trivEquiv T hT).symm.toRingHom) ≫ T.x) (by
    have h : T.x ≫ X.hom = spMap (T.π.comp (algebraMap R T.B)) :=
      ((Category.comp_id _).symm.trans (Category.assoc _ _ _)).trans T.w
    change (spMap _ ≫ T.x) ≫ X.hom = spMap (algebraMap R T.B)
    rw [Category.assoc, h, ← Cris.spMap_comp]
    congr 1
    ext r
    exact trivEquiv_symm_π T hT _)

theorem spOver_trivPt {T T' : Thick (dp0 R) (X.hom ≫ 𝟙 _)} (hT : T.J = ⊥) (hT' : T'.J = ⊥) (φ : T ⟶ T') :
    spOver φ.φ ≫ trivPt T hT = trivPt T' hT' := by
  apply Over.OverMorphism.ext
  change spMap (φ.φ : T.B →+* T'.B) ≫ spMap ((trivEquiv T hT).symm.toRingHom) ≫ T.x =
    spMap ((trivEquiv T' hT').symm.toRingHom) ≫ T'.x
  rw [← φ.pt, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
  congr 2
  ext b
  obtain ⟨b, rfl⟩ := T.surj b
  change φ.φ ((trivEquiv T hT).symm (T.π b)) = (trivEquiv T' hT').symm (φ.φ₀ (T.π b))
  rw [φ.comm, trivEquiv_symm_π, trivEquiv_symm_π]

theorem trivPt_trivAt {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) : trivPt (trivAt x) rfl = x := by
  apply Over.OverMorphism.ext
  change spMap ((trivEquiv (trivAt x) rfl).symm.toRingHom) ≫ x.left = x.left
  have : (trivEquiv (trivAt x) rfl).symm.toRingHom = RingHom.id D :=
    RingHom.ext fun b ↦ trivEquiv_symm_π (trivAt x) rfl b
  rw [this, Cris.spMap_id, Category.id_comp]

def trivCoc (u : Fn1 X) (hu : IsCoc (whole X) u) :
    Z1 ((IsTriv (X.hom ≫ 𝟙 _)).ι ⋙ O (dp0 R) (X.hom ≫ 𝟙 _)) :=
  ⟨fun T T' φ ↦ u T.obj.B T'.obj.B φ.hom.φ (trivPt T.obj T.property), fun T T' T'' φ ψ ↦ by
    change u _ _ (ψ.hom.φ.comp φ.hom.φ) _ = ψ.hom.φ (u _ _ φ.hom.φ _) + u _ _ ψ.hom.φ _
    rw [hu _ _ _ φ.hom.φ ψ.hom.φ _ (sm_whole _), spOver_trivPt T.property T'.property φ.hom]⟩

end GlobalTheory.PtExt.Lift


open GlobalTheory.PtExt.Lift in
theorem GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective : ∀ (R : Type) [CommRing R] (X : Over (Sp R)),
    Function.Surjective (toH1O (X.hom ≫ 𝟙 _)) → ∀ u : Fn1 X, IsCoc (whole X) u →
      ∃ f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)), Cohom (whole X) u (fv f) := by
  intro R _ X hs u hu
  obtain ⟨c, hc⟩ := hs (H1.mk _ (trivCoc u hu))
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  have hc' : H1.mk _ ((CoefMap.restrict (O (dp0 R) (X.hom ≫ 𝟙 _)) (IsTriv (X.hom ≫ 𝟙 _)).ι).pullbackOneCocycle f) =
      H1.mk _ (trivCoc u hu) := hc
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 hc'
  refine ⟨f, fun D _ _ x ↦ -g ⟨trivAt x, rfl⟩, ?_⟩
  intro D _ _ D' _ _ φ x _
  let T : (IsTriv (X.hom ≫ 𝟙 _)).FullSubcategory := ⟨trivAt x, rfl⟩
  let T' : (IsTriv (X.hom ≫ 𝟙 _)).FullSubcategory := ⟨trivAt (spOver φ ≫ x), rfl⟩
  let a : T ⟶ T' := ObjectProperty.homMk (trivMap φ x)
  let b : D := g T
  let b' : D' := g T'
  have h := congrFun (congrFun (congrFun hg T) T') a
  change b' - φ b = ev f (trivMap φ x) - u D D' φ (trivPt (trivAt x) rfl) at h
  rw [trivPt_trivAt] at h
  change u D D' φ x + -ev f (trivMap φ x) = -b' - φ (-b)
  rw [map_neg]
  linear_combination h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAndMultiplicityPullbackIsIsoOpen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy.MultIso

theorem ord_ringEquiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (a : A) :
    Ring.ord B (e a) = Ring.ord A a := by
  have : RingHomSurjective (e : A →+* B) := ⟨e.surjective⟩
  have hIJ : Ideal.span {e a} = (Ideal.span {a}).map (e : A →+* B) := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  let q := Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {e a}) e hIJ
  let f : (A ⧸ Ideal.span {a}) →ₛₗ[(e : A →+* B)] (B ⧸ Ideal.span {e a}) :=
    { toFun := q
      map_add' := q.map_add
      map_smul' := fun r x => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        show q (Ideal.Quotient.mk _ (r * y)) = Ideal.Quotient.mk _ (e r) * q (Ideal.Quotient.mk _ y)
        rw [Ideal.quotientEquiv_mk, Ideal.quotientEquiv_mk, map_mul, map_mul] }
  rw [Ring.ord, Ring.ord, Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f q.bijective)]

theorem ordFrac_ringEquiv {A B K L : Type} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Ring.KrullDimLE 1 A] [Ring.KrullDimLE 1 B]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    (e : A ≃+* B) (φ : K →+* L) (h : ∀ a, φ (algebraMap A K a) = algebraMap B L (e a)) (f : K) :
    Ring.ordFrac B (φ f) = Ring.ordFrac A f := by
  have key : ∀ a : A, Ring.ordFrac B (algebraMap B L (e a)) = Ring.ordFrac A (algebraMap A K a) := by
    intro a
    by_cases ha : a = 0
    · subst ha; simp
    have hea : e a ≠ 0 := by simpa using ha
    rw [Ring.ordFrac_eq_ord (R := B) (K := L), Ring.ordFrac_eq_ord (R := A) (K := K)]
    simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      mem_nonZeroDivisors_iff_ne_zero, ne_eq, ha, hea, not_false_eq_true, if_true,
      ord_ringEquiv]
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) f
  dsimp only at hxy
  subst hxy
  have hspec := IsLocalization.mk'_spec K x y
  have h1 : Ring.ordFrac A (IsLocalization.mk' K x y) * Ring.ordFrac A (algebraMap A K y) =
      Ring.ordFrac A (algebraMap A K x) := by rw [← map_mul, hspec]
  have h2 : Ring.ordFrac B (φ (IsLocalization.mk' K x y)) * Ring.ordFrac B (algebraMap B L (e y)) =
      Ring.ordFrac B (algebraMap B L (e x)) := by rw [← map_mul, ← h, ← map_mul, hspec, h]
  rw [key, key] at h2
  have hy : algebraMap A K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2
  have hc : Ring.ordFrac A (algebraMap A K y) ≠ 0 := (map_ne_zero _).mpr hy
  exact mul_right_cancel₀ hc (h2.trans h1.symm)

private theorem isIso_stalkMap_restrict_of_isIso {X Y : Scheme.{0}} (s : Y ⟶ X) (U : X.Opens)
    [IsIso (s ∣_ U)] (x : s ⁻¹ᵁ U) : IsIso ((s ∣_ U).stalkMap x) := by
  have h : IsOpenImmersion (s ∣_ U) := inferInstance
  exact LocallyRingedSpace.IsOpenImmersion.stalk_iso (H := h) (s ∣_ U).toLRSHom x

theorem isIso_stalkMap_of_isIso_restrict {X Y : Scheme.{0}} (s : Y ⟶ X) (U : X.Opens)
    [IsIso (s ∣_ U)] (w : Y) (hw : s w ∈ U) : IsIso (s.stalkMap w) := by
  have hw' : w ∈ s ⁻¹ᵁ U := hw
  have e := morphismRestrictStalkMap s U ⟨w, hw'⟩
  have hi : IsIso ((s ∣_ U).stalkMap ⟨w, hw'⟩) := isIso_stalkMap_restrict_of_isIso s U _
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).mp hi

theorem coheight_eq_of_isIso_stalkMap {X Y : Scheme.{0}} (s : Y ⟶ X) (w : Y)
    [IsIso (s.stalkMap w)] : Order.coheight w = Order.coheight (s w) := by
  apply WithBot.coe_injective
  rw [← ringKrullDim_stalk_eq_coheight, ← ringKrullDim_stalk_eq_coheight]
  exact (ringKrullDim_eq_of_ringEquiv (asIso (s.stalkMap w)).commRingCatIsoToRingEquiv).symm

theorem ord_functionFieldMap_of_isIso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X)
    [IsDominant s] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (w : Y)
    [IsIso (s.stalkMap w)] (f : X.functionField) :
    Scheme.ord (functionFieldMap s f) w = Scheme.ord f (s w) := by
  have hco := coheight_eq_of_isIso_stalkMap s w
  by_cases hc : Order.coheight (s w) = 1
  · have hw : Order.coheight w = 1 := hco.trans hc
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hw, Scheme.ord_eq_ordHom_of_coheight_eq_one hc]
    have : Ring.KrullDimLE 1 (X.presheaf.stalk (s w)) := krullDimLE_of_coheight_le hc.le
    have : Ring.KrullDimLE 1 (Y.presheaf.stalk w) := krullDimLE_of_coheight_le hw.le
    congr 2
    exact ordFrac_ringEquiv (asIso (s.stalkMap w)).commRingCatIsoToRingEquiv (functionFieldMap s)
      (fun a => functionFieldMap_algebraMap s w a) f
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hc,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hc (hco ▸ h))]

theorem coheight_eq_and_mult_pullCart : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (U : X.Opens), IsIso (s ∣_ U) → ∀ w : Y, s w ∈ U → Order.coheight w = Order.coheight (s w) ∧ ∀ D : CartierDiv X, (pullCart s D).mult w = D.mult (s w) := by
  intro X Y _ _ s _ _ _ U hU w hw
  haveI := hU
  haveI := isIso_stalkMap_of_isIso_restrict s U w hw
  refine ⟨coheight_eq_of_isIso_stalkMap s w, fun D => ?_⟩
  obtain ⟨g, hg⟩ := D.exists_isEqn (s w)
  rw [(isEqn_pullCart s hg).mult_eq, hg.mult_eq]
  exact ord_functionFieldMap_of_isIso s w (g : X.functionField)

end GlobalTheory.Discrepancy.MultIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqOfIsUnitFinrank
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep


open Module in
theorem comap_map_eq_of_isUnit_finrank : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [CommRing V'] [IsDomain V'] [Algebra V V'] [Module.Finite V V'], Function.Injective (algebraMap V V') → IsUnit ((Module.finrank V V' : ℕ) : V) → ∀ I : Ideal V, (I.map (algebraMap V V')).comap (algebraMap V V') = I := by
  intro V V' _ _ _ _ _ _ _ hinj hunit I
  refine le_antisymm ?_ Ideal.le_comap_map
  let K := FractionRing V
  let L := FractionRing V'
  have hinjL : Function.Injective (algebraMap V L) := by
    rw [IsScalarTower.algebraMap_eq V V' L]
    exact (IsFractionRing.injective V' L).comp hinj
  haveI : FaithfulSMul V L := (faithfulSMul_iff_algebraMap_injective V L).mpr hinjL
  letI : Algebra K L := FractionRing.liftAlgebra V L
  haveI : IsScalarTower V K L := FractionRing.isScalarTower_liftAlgebra V L
  have hrank : finrank K L = finrank V V' := IsFractionRing.finrank_eq V K V' L
  have hn0 : finrank K L ≠ 0 := by
    intro h
    rw [← hrank, h, Nat.cast_zero] at hunit
    exact not_isUnit_zero hunit
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hn0)
  haveI : Module.Free K L := Module.Free.of_divisionRing K L
  haveI : Algebra.IsIntegral V V' := Algebra.IsIntegral.of_finite V V'

  have htrV : ∀ z : V', ∃ t : V, algebraMap V K t = Algebra.trace K L (algebraMap V' L z) := by
    intro z
    have hz : IsIntegral V (algebraMap V' L z) :=
      (Algebra.IsIntegral.isIntegral (R := V) z).map (IsScalarTower.toAlgHom V V' L)
    exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace hz)
  have hmul : ∀ (i : V) (w : L), Algebra.trace K L (algebraMap V L i * w) =
      algebraMap V K i * Algebra.trace K L w := by
    intro i w
    rw [IsScalarTower.algebraMap_apply V K L, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have key : ∀ y ∈ I.map (algebraMap V V'), ∀ z : V', ∃ c ∈ I,
      algebraMap V K c = Algebra.trace K L (algebraMap V' L (z * y)) := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, hi, rfl⟩ z
      obtain ⟨t, ht⟩ := htrV z
      refine ⟨i * t, I.mul_mem_right t hi, ?_⟩
      rw [map_mul, ht, mul_comm z, map_mul, ← IsScalarTower.algebraMap_apply V V' L, hmul]
    · intro z
      exact ⟨0, I.zero_mem, by simp⟩
    · intro x y _ _ hx hy z
      obtain ⟨c, hc, hcx⟩ := hx z
      obtain ⟨d, hd, hdy⟩ := hy z
      exact ⟨c + d, I.add_mem hc hd, by rw [map_add (f := _), hcx, hdy, mul_add, map_add (f := _), map_add (f := _)]⟩
    · intro w x _ hx z
      obtain ⟨c, hc, hcx⟩ := hx (z * w)
      exact ⟨c, hc, by rw [hcx, smul_eq_mul, _root_.mul_assoc]⟩
  intro a ha
  obtain ⟨c, hc, hca⟩ := key _ ha 1
  rw [_root_.one_mul, ← IsScalarTower.algebraMap_apply V V' L, IsScalarTower.algebraMap_apply V K L,
    Algebra.trace_algebraMap, hrank, nsmul_eq_mul, ← map_natCast (algebraMap V K), ← map_mul] at hca
  have hc' : c = (finrank V V' : V) * a := IsFractionRing.injective V K hca
  obtain ⟨u, hu⟩ := hunit
  have : a = ↑u⁻¹ * c := by rw [hc', ← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  rw [this]
  exact I.mul_mem_left _ hc

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConductorSquareFlatBaseChangeSchemesStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductorSquare_flat_baseChange_schemes : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (X X' Z : Scheme.{0}) (u : X ⟶ Sp R) (p : X' ⟶ X) (u' : X' ⟶ Sp R') (i : Z ⟶ X) (v : Z ⟶ Sp (R ⧸ c)), Flat u → IsPullback p u' u (spMap (algebraMap R R')) → IsPullback i v u (spMap (Ideal.Quotient.mk c)) → GlobalTheory.Pinch.Cond p i := by
  first | exact @GlobalTheory.Pinch.FlatSq.cond_of_flat | exact GlobalTheory.Pinch.FlatSq.cond_of_flat | (intros; apply GlobalTheory.Pinch.FlatSq.cond_of_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceSubgroupIndicatorWeightStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroup_indicator_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n a b k : ℕ), a + b = n → 1 ≤ k → Match n a b w 1 ((({γ : UL n w | γ.1 ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}} : Set (UL n w))).indicator 1) (fun y : GLw a w × GLw b w => ((-((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (k * a * b))⁻¹ * (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) := by
  first | exact @GlobalTheory.CongMatch.match_principal_congruence_inert | exact GlobalTheory.CongMatch.match_principal_congruence_inert | (intros; apply GlobalTheory.CongMatch.match_principal_congruence_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountingVolumeLeSelfIntersectionNefHermitianBund
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory

open Filter Topology

theorem countVol_le_selfInter : ∀ (k : Type) [CommRing k] (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp k) (D d a : ℕ) (L : GlobalTheory.HermLB p) (A : ℝ) (m : ℕ → ℕ∞), GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.IsArithVar p D → L.IsNef D → L.IsSelfInter A → 0 < d → 0 < a → (∀ i : ℕ, 1 ≤ i → m (a * i) ≤ (L.pow (a * i)).smallSec.encard) → countVol D d a m ≤ ENNReal.ofReal (A / ((d : ℝ) * ((D : ℝ) + 1))) := by
  intro k _ X _ p D d a L A m hAHS hX hL hA hd ha hm
  have hmul : Tendsto (fun j : ℕ => a * j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j ha) tendsto_id
  have h1 := ((hAHS.tendsto_of_triv hX hL hA).comp hmul).div_const ((d : ℝ) * ((D : ℝ) + 1))
  have h2 := ENNReal.tendsto_ofReal h1
  refine (limsup_le_limsup ?_).trans_eq h2.limsup_eq
  filter_upwards [hmul.eventually (hAHS.of_triv hX hL hA).1, eventually_ge_atTop 1] with j hfin hj
  have hx : 0 ≤ Real.log (((L.pow (a * j)).smallSec.ncard : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hN : (0 : ℝ) < ((a * j : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.mul_pos ha hj)
  have hd' : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.2 hd
  have hlog : logCard (m (a * j)) ≤ ENNReal.ofReal (Real.log (((L.pow (a * j)).smallSec.ncard : ℕ) : ℝ)) := by
    rw [← logCard_coe, hfin.cast_ncard_eq]
    exact EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 (hm j hj)))
  have hden : (d : ℝ≥0∞) * ((a * j : ℕ) : ℝ≥0∞) ^ (D + 1) =
      ENNReal.ofReal ((d : ℝ) * ((a * j : ℕ) : ℝ) ^ (D + 1)) := by
    rw [ENNReal.ofReal_mul hd'.le, ENNReal.ofReal_pow hN.le, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  calc _ ≤ (D.factorial : ℝ≥0∞) * ENNReal.ofReal (Real.log (((L.pow (a * j)).smallSec.ncard : ℕ) : ℝ)) /
        ((d : ℝ≥0∞) * ((a * j : ℕ) : ℝ≥0∞) ^ (D + 1)) := by gcongr
    _ = _ := by
      rw [hden, ← ENNReal.ofReal_natCast (D.factorial), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_div_of_pos (by positivity)]
      simp only [Function.comp]
      congr 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp

end GlobalTheory
end

