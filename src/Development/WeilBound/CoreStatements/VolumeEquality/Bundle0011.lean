module

public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0049
public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0008

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushJoin
section
noncomputable section

namespace SheetDecomposition

open scoped TensorProduct

namespace Join

theorem tower {P Ω : Type} [Field P] [Field Ω] (φ : P →+* Ω) (K₀ : Subfield P) :
    Module.finrank (K₀.map φ) Ω = Module.finrank K₀ P * Module.finrank φ.fieldRange Ω := by
  letI : Algebra P Ω := φ.toAlgebra
  letI : Algebra K₀ Ω := (φ.comp K₀.subtype).toAlgebra
  haveI : IsScalarTower K₀ P Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : Module.finrank P Ω = Module.finrank φ.fieldRange Ω :=
    Algebra.finrank_eq_of_equiv_equiv φ.rangeRestrictFieldEquiv (RingEquiv.refl Ω) (RingHom.ext fun _ => rfl)
  have h2 : Module.finrank K₀ Ω = Module.finrank (K₀.map φ) Ω :=
    Algebra.finrank_eq_of_equiv_equiv (K₀.toSubring.equivMapOfInjective φ φ.injective) (RingEquiv.refl Ω)
      (RingHom.ext fun _ => rfl)
  rw [← h1, ← h2, Module.finrank_mul_finrank]

theorem finrank_congr {Ω : Type} [Field Ω] {A B : Subfield Ω} (h : A = B) : Module.finrank A Ω = Module.finrank B Ω := by
  subst h; rfl

theorem map_adjoin {F P Ω : Type} [Field F] [Field P] [Field Ω] [Algebra F P] [Algebra F Ω] (φ : P →+* Ω)
    (hφ : φ.comp (algebraMap F P) = algebraMap F Ω) {I : Type} (w : I → P) :
    (IntermediateField.adjoin F (Set.range w)).toSubfield.map φ =
      (IntermediateField.adjoin F (Set.range fun q => φ (w q))).toSubfield := by
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield, RingHom.map_field_closure, Set.image_union,
    ← Set.range_comp, ← Set.range_comp, ← hφ]
  rfl

theorem core (F A B : Type) [Field F] [Field A] [Field B] [Algebra F A] [Algebra F B] {I : Type} (w : I → B) (d₂ e : ℕ)
    (hw : AlgebraicIndependent F w) (hd : 0 < d₂) (hB : Module.finrank (IntermediateField.adjoin F (Set.range w)) B = d₂)
    (he : 0 < e) (hA : Module.finrank F A = e) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra A Ω) (i : B →+* Ω) (d n : ℕ),
      i.comp (algebraMap F B) = (algebraMap A Ω).comp (algebraMap F A) ∧ AlgebraicIndependent A (fun q => i (w q)) ∧ 0 < d ∧
      Module.finrank (IntermediateField.adjoin A (Set.range fun q => i (w q))) Ω = d ∧
      Module.finrank i.fieldRange Ω = n ∧ 0 < n ∧ n * d₂ = d * e := by
  haveI : FiniteDimensional F A := Module.finite_of_finrank_pos (hA ▸ he)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (B ⊗[F] A)
  letI : Field ((B ⊗[F] A) ⧸ m) := Ideal.Quotient.field m
  let j : A →ₐ[F] ((B ⊗[F] A) ⧸ m) := (Ideal.Quotient.mkₐ F m).comp Algebra.TensorProduct.includeRight
  letI : Algebra A ((B ⊗[F] A) ⧸ m) := j.toRingHom.toAlgebra
  haveI : IsScalarTower F A ((B ⊗[F] A) ⧸ m) := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Module.Finite B ((B ⊗[F] A) ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ B m).toLinearMap (Ideal.Quotient.mkₐ_surjective B m)
  let Ω := ((B ⊗[F] A) ⧸ m)
  let i : B →+* Ω := algebraMap B Ω
  have hi : i.comp (algebraMap F B) = algebraMap F Ω := (IsScalarTower.algebraMap_eq F B Ω).symm
  have hx0 : AlgebraicIndependent F (fun q => i (w q)) :=
    hw.map' (f := IsScalarTower.toAlgHom F B Ω) (algebraMap B Ω).injective
  have hx : AlgebraicIndependent A (fun q => i (w q)) := hx0.extendScalars A
  have hn : 0 < Module.finrank i.fieldRange Ω := by
    rw [← Algebra.finrank_eq_of_equiv_equiv i.rangeRestrictFieldEquiv (RingEquiv.refl Ω) (RingHom.ext fun _ => rfl)]
    exact Module.finrank_pos
  have t1 := tower i (IntermediateField.adjoin F (Set.range w)).toSubfield
  rw [finrank_congr (map_adjoin i hi w)] at t1
  let P := FractionRing (MvPolynomial I A)
  let φ : P →+* Ω := (IntermediateField.adjoin A (Set.range fun q => i (w q))).val.toRingHom.comp hx.aevalEquivField.toRingEquiv.toRingHom
  letI : Algebra F P := ((algebraMap A P).comp (algebraMap F A)).toAlgebra
  have hφA : ∀ a, φ (algebraMap A P a) = algebraMap A Ω a := fun a => congrArg Subtype.val (hx.aevalEquivField.commutes a)
  have hφ : φ.comp (algebraMap F P) = algebraMap F Ω := RingHom.ext fun a =>
    (hφA _).trans (IsScalarTower.algebraMap_apply F A Ω a).symm
  have hX : (fun q => φ (algebraMap (MvPolynomial I A) P (MvPolynomial.X q))) = fun q => i (w q) := funext fun q =>
    (hx.aevalEquivField_algebraMap_apply_coe _).trans (MvPolynomial.aeval_X _ q)
  have hr : φ.fieldRange = (IntermediateField.adjoin A (Set.range fun q => i (w q))).toSubfield := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (hx.aevalEquivField y).2
    · intro hz
      exact ⟨hx.aevalEquivField.symm ⟨z, hz⟩, congrArg Subtype.val (hx.aevalEquivField.apply_symm_apply ⟨z, hz⟩)⟩
  have t2 := tower φ (IntermediateField.adjoin F (Set.range fun q => algebraMap (MvPolynomial I A) P (MvPolynomial.X q))).toSubfield
  rw [finrank_congr (map_adjoin φ hφ _), hX, finrank_congr hr] at t2
  have t3 := GlobalTheory.CompanionTheory.FieldDeg.finrank_fraction_over_adjoin_X_eq F A I rfl
  have key : d₂ * Module.finrank i.fieldRange Ω =
      e * Module.finrank (IntermediateField.adjoin A (Set.range fun q => i (w q))) Ω := by
    rw [← hB, ← hA, ← t3]
    exact t1.symm.trans t2
  refine ⟨Ω, inferInstance, inferInstance, i, _, _, hi.trans (IsScalarTower.algebraMap_eq F A Ω), hx, ?_, rfl, rfl, hn, ?_⟩
  · refine Nat.pos_of_ne_zero fun h => ?_
    rw [h, mul_zero] at key
    exact (Nat.mul_pos hd hn).ne' key
  · rw [mul_comm, key, mul_comm]

theorem adjoin_entries (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {S : Type} {r : S → ℕ}
    (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1) (h0 : ∀ s l m, l < m → u s l m = 0) :
    IntermediateField.adjoin k (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin k
        (Set.range fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ ?_)
  · rintro _ ⟨⟨s, l, m⟩, rfl⟩
    show u s l m ∈ _
    rcases lt_trichotomy l m with h | rfl | h
    · rw [h0 s l m h]; exact zero_mem _
    · rw [h1]; exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, ⟨(l, m), h⟩⟩, rfl⟩
  · rintro _ ⟨⟨s, lm, h⟩, rfl⟩
    exact ⟨⟨s, lm⟩, rfl⟩

end Join

theorem fieldJoin : FieldJoin := by
  intro Ω₀ Ω₁ Ω₂ _ _ _ _ _ S _ r u d₂ e ⟨h1, h0, hi, hd, hf⟩ he hA
  rw [Join.adjoin_entries Ω₀ u h1 h0] at hf
  obtain ⟨Ω, _, _, i, d, n, a1, a2, a3, a4, a5, a6, a7⟩ := Join.core Ω₀ Ω₁ Ω₂ _ d₂ e hi hd hf he hA
  have g1 : ∀ s m, (u s).map i m m = 1 := fun s m => by simp [h1]
  have g0 : ∀ s l m, l < m → (u s).map i l m = 0 := fun s l m h => by simp [h0 s l m h]
  refine ⟨Ω, inferInstance, inferInstance, i, d, n, a1, ⟨g1, g0, a2, a3, ?_⟩, a5, a6, a7⟩
  rw [Join.adjoin_entries Ω₁ (fun s => (u s).map i) g1 g0]
  exact a4

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushMap
section
noncomputable section

namespace SheetDecomposition

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal pointConeMap intNum)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)]

theorem pointIdeal_rat {Ω : Type} [Field Ω] [inst : Algebra ℚ Ω] (y : (Σ b, ι b) → Ω) :
    pointIdeal ℚ y = (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) := by
  have hcomp : ∀ F : MRing ι, pointConeMap ℚ y (MvPolynomial.map (Int.castRingHom ℚ) F) = mConeMap y F := by
    intro F
    simp only [pointConeMap, mConeMap, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
    exact RingHom.ext_int _ _
  have key : ∀ G : MvPolynomial (Σ b, ι b) ℚ, ∃ n : ℕ, 0 < n ∧ ∃ F : MRing ι,
      MvPolynomial.map (Int.castRingHom ℚ) F = (n : MvPolynomial (Σ b, ι b) ℚ) * G := by
    intro G
    induction G using MvPolynomial.induction_on with
    | C a =>
      refine ⟨a.den, a.pos, C a.num, ?_⟩
      rw [map_C, ← map_natCast (C : ℚ →+* MvPolynomial (Σ b, ι b) ℚ), ← C_mul, Rat.den_mul_eq_num]
      rfl
    | add p q hp hq =>
      obtain ⟨n, hn, F, hF⟩ := hp
      obtain ⟨n', hn', F', hF'⟩ := hq
      refine ⟨n * n', Nat.mul_pos hn hn', C (n' : ℤ) * F + C (n : ℤ) * F', ?_⟩
      rw [map_add (f := _), map_mul, map_mul, hF, hF', map_C, map_C]
      simp only [eq_intCast, Int.cast_natCast, map_natCast, Nat.cast_mul]
      ring
    | mul_X p j hp =>
      obtain ⟨n, hn, F, hF⟩ := hp
      exact ⟨n, hn, F * X j, by rw [map_mul, map_X, hF, mul_assoc]⟩
  apply le_antisymm
  · intro G hG
    obtain ⟨n, hn, F, hF⟩ := key G
    have hG0 : pointConeMap ℚ y G = 0 := hG
    have hFker : F ∈ mCoordIdeal y := by
      show mConeMap y F = 0
      rw [← hcomp, hF, map_mul, hG0, mul_zero]
    have hGeq : G = C ((n : ℚ)⁻¹) * MvPolynomial.map (Int.castRingHom ℚ) F := by
      rw [hF, ← mul_assoc, ← map_natCast (C : ℚ →+* MvPolynomial (Σ b, ι b) ℚ), ← C_mul,
        inv_mul_cancel₀ (by exact_mod_cast hn.ne'), C_1, one_mul]
    rw [hGeq]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hFker)
  · rw [Ideal.map_le_iff_le_comap]
    intro F hF
    show pointConeMap ℚ y (MvPolynomial.map (Int.castRingHom ℚ) F) = 0
    rw [hcomp]
    exact hF

omit [Fintype K] [∀ b, Fintype (ι b)] in
theorem pointIdeal_map {R Ω₂ Ω : Type} [CommRing R] [Field Ω₂] [Field Ω] [Algebra R Ω₂] [Algebra R Ω] (i : Ω₂ →ₐ[R] Ω)
    (y : (Σ b, ι b) → Ω₂) : pointIdeal R (fun x => i (y x)) = pointIdeal R y := by
  have h : (MvPolynomial.mapAlgHom i).comp (pointConeMap R y) = pointConeMap R (fun x => i (y x)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap]
  ext F
  change pointConeMap R (fun x => i (y x)) F = 0 ↔ pointConeMap R y F = 0
  rw [← h, AlgHom.comp_apply]
  constructor
  · intro h0
    apply MvPolynomial.map_injective (i : Ω₂ →+* Ω) i.toRingHom.injective
    rw [map_zero]
    exact h0
  · intro h0
    rw [h0, map_zero]

theorem ne_of_arith {Ω : Type} [Field Ω] {y : (Σ b, ι b) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) (b : K) :
    ∃ j, y ⟨b, j⟩ ≠ 0 := by
  obtain ⟨j, hj⟩ := h.2.1.2.2 b
  refine ⟨j, fun h0 => hj ?_⟩
  show mConeMap y (X ⟨b, j⟩) = 0
  simp [mConeMap, h0]

theorem range_le_fnField {Ω₂ Ω : Type} [Field Ω₂] [Field Ω] (i : Ω₂ →+* Ω) {y : (Σ b, ι b) → Ω₂} (hb : Birational y)
    (hy : ∀ b, ∃ j, y ⟨b, j⟩ ≠ 0) (k : Type) [Field k] [Algebra k Ω] :
    i.fieldRange ≤ (fnField k fun x => i (y x)).toSubfield := by
  choose c hc using hy
  have htop := BirationalRatioClosure.full K ι Ω₂ y c hb hc
  rintro _ ⟨s, rfl⟩
  have hs : s ∈ Subfield.closure (GroundTheory.Heights₂.Heights.coneRatios y c) := htop ▸ Subfield.mem_top s
  have hle : Subfield.closure (GroundTheory.Heights₂.Heights.coneRatios y c) ≤
      (fnField k fun x => i (y x)).toSubfield.comap i := by
    rw [Subfield.closure_le]
    rintro _ ⟨p, rfl⟩
    show i (y p / y ⟨p.1, c p.1⟩) ∈ (fnField k fun x => i (y x)).toSubfield
    rw [map_div₀]
    exact IntermediateField.subset_adjoin k _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  exact hle hs

private theorem finiteDimensional_of_subfield_le {Ω : Type} [Field Ω] (S T : Subfield Ω) (h : S ≤ T) [FiniteDimensional S Ω] :
    FiniteDimensional T Ω := by
  letI : Algebra S T := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower S T Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  exact Module.Finite.of_restrictScalars_finite S T Ω

private theorem trdeg_eq_of_finrank_fieldRange_pos {Ω₂ Ω : Type} [Field Ω₂] [Field Ω] [Algebra ℚ Ω₂] [Algebra ℚ Ω] (i : Ω₂ →+* Ω)
    (d : ℕ) (hZ : Algebra.trdeg ℤ Ω₂ = d) (hfin : 0 < Module.finrank i.fieldRange Ω) :
    Algebra.trdeg ℚ Ω = d := by
  have hQ : Algebra.trdeg ℚ Ω₂ = d := by
    haveI := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have h := _root_.trdeg_add_eq ℤ ℚ (A := Ω₂)
    rw [_root_.trdeg_eq_zero, zero_add, hZ] at h
    exact h
  letI : Algebra Ω₂ Ω := i.toAlgebra
  haveI : IsScalarTower ℚ Ω₂ Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : Algebra Ω₂ i.fieldRange := i.rangeRestrictField.toAlgebra
  haveI : IsScalarTower Ω₂ i.fieldRange Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : Module.Finite i.fieldRange Ω := Module.finite_of_finrank_pos hfin
  haveI : Module.Finite Ω₂ i.fieldRange := by
    refine Module.Finite.of_surjective (Algebra.linearMap Ω₂ i.fieldRange) ?_
    rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := RingHom.mem_fieldRange.1 hz
    exact ⟨x, Subtype.ext rfl⟩
  haveI : Module.Finite Ω₂ Ω := Module.Finite.trans i.fieldRange Ω
  have h := _root_.trdeg_add_eq ℚ Ω₂ (A := Ω)
  rw [_root_.trdeg_eq_zero (R := Ω₂) (A := Ω), add_zero, hQ] at h
  exact h.symm

theorem numMap : NumMap := by
  intro Ω₂ _ _ Ω _ _ i K _ ι _ y d hb har hfin
  have hy : ∀ b, ∃ j, y ⟨b, j⟩ ≠ 0 := ne_of_arith har
  have hiy : ∀ b, ∃ j, i (y ⟨b, j⟩) ≠ 0 := fun b => by
    obtain ⟨j, hj⟩ := hy b
    exact ⟨j, (map_ne_zero i).2 hj⟩
  haveI : FiniteDimensional i.fieldRange Ω := Module.finite_of_finrank_pos hfin
  have hFD : ∀ (k : Type) [Field k] [Algebra k Ω], FiniteDimensional (fnField k fun x => i (y x)) Ω := by
    intro k _ _
    haveI := finiteDimensional_of_subfield_le i.fieldRange _ (range_le_fnField i hb hy k)
    exact this
  have heq : (fnField ℚ fun x => i (y x)).toSubfield = i.fieldRange := by
    refine le_antisymm ?_ (range_le_fnField i hb hy ℚ)
    rw [fnField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨q, rfl⟩ | ⟨p, p', _, rfl⟩)
    · exact RingHom.mem_fieldRange.2 ⟨algebraMap ℚ Ω₂ q, by simp⟩
    · exact RingHom.mem_fieldRange.2 ⟨y p / y p', by rw [map_div₀]⟩
  have hrank : Module.finrank (fnField ℚ fun x => i (y x)) Ω = Module.finrank i.fieldRange Ω := by
    rw [show Module.finrank (fnField ℚ fun x => i (y x)) Ω =
      Module.finrank (fnField ℚ fun x => i (y x)).toSubfield Ω from rfl, heq]
  have hpi : pointIdeal ℚ (fun x => i (y x)) = pointIdeal ℚ y := pointIdeal_map i.toRatAlgHom y
  refine ⟨⟨hiy, hFD ℚ, trdeg_eq_of_finrank_fieldRange_pos i d (FnFieldTrdeg.full K ι Ω₂ y d hb har) hfin⟩, hFD, fun a => ?_, fun a => ?_⟩
  · simp only [num, inum]
    rw [hrank, hpi]
  · simp only [inum, GroundTheory.Heights₂.Heights.HilbertSamuel.genDeg]
    rw [pointIdeal_rat]

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.DegPushMuLinkA
section
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

section Lin

variable {Ω₃ : Type} [Field Ω₃] (O : ValuationSubring Ω₃) {r : ℕ}

theorem mu_det_le (T T' : Matrix (Fin r) (Fin r) Ω₃)
    (h : ∀ k, (fun m => T m k) ∈ Submodule.span O (Set.range fun k m => T' m k)) :
    O.valuation T.det ≤ O.valuation T'.det := by
  choose N hN using fun k => (Submodule.mem_span_range_iff_exists_fun O).1 (h k)
  have e : T = T' * (Matrix.of fun a b => N b a).map O.subtype := by
    ext m k
    have := congrFun (hN k) m
    simp only [Finset.sum_apply, Pi.smul_apply] at this
    rw [← this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have e2 : ((Matrix.of fun a b => N b a).map O.subtype).det = ((Matrix.of fun a b => N b a).det : O) :=
    (RingHom.map_det O.subtype _).symm
  rw [e, Matrix.det_mul, map_mul, e2]
  exact mul_le_of_le_one_right' (O.valuation_le_one _)

theorem mu_det_eq (T T' : Matrix (Fin r) (Fin r) Ω₃)
    (h : Submodule.span O (Set.range fun k m => T m k) = Submodule.span O (Set.range fun k m => T' m k)) :
    O.valuation T.det = O.valuation T'.det :=
  le_antisymm (mu_det_le O T T' fun k => h ▸ Submodule.subset_span ⟨k, rfl⟩)
    (mu_det_le O T' T fun k => h ▸ Submodule.subset_span ⟨k, rfl⟩)

theorem mu_coord {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] (R : Subring Ω) (i : Ω →+* Ω₃) (hi : ∀ a ∈ R, i a ∈ O)
    (c : Fin r → V) (hc : LinearIndependent Ω c) (Z : Set V) (Λ : Submodule O (Fin r → Ω₃))
    (hZ : ∀ w ∈ Z, ∃ x : Fin r → Ω, w = ∑ m, x m • c m ∧ (fun m => i (x m)) ∈ Λ) (x : Fin r → Ω)
    (hx : ∑ m, x m • c m ∈ Submodule.span R Z) : (fun m => i (x m)) ∈ Λ := by
  have key : ∀ w ∈ Submodule.span R Z, ∃ x : Fin r → Ω, w = ∑ m, x m • c m ∧ (fun m => i (x m)) ∈ Λ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact hZ w hw
    | zero => exact ⟨0, by simp, by simp only [Pi.zero_apply, map_zero]; exact Λ.zero_mem⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, rfl, hx⟩ := ha
      obtain ⟨y, rfl, hy⟩ := hb
      refine ⟨x + y, by simp [add_smul, Finset.sum_add_distrib], ?_⟩
      convert Λ.add_mem hx hy using 1
      ext m; simp
    | smul a w _ hw =>
      obtain ⟨x, rfl, hx⟩ := hw
      refine ⟨fun m => (a : Ω) * x m, ?_, ?_⟩
      · rw [Subring.smul_def]
        simp [Finset.smul_sum, mul_smul]
      · convert Λ.smul_mem ⟨i a, hi a a.2⟩ hx using 1
        ext m
        show i (a * x m) = i a * i (x m)
        exact map_mul _ _ _
  obtain ⟨x', e, hx'⟩ := key _ hx
  have : x = x' := funext (Fintype.linearIndependent_iffₛ.1 hc x x' e)
  exact this ▸ hx'

theorem mu_alg {G : Type} [CommGroupWithZero G] {m₁ m₂ e₁ e₂ t₁ t₂ r₁ r₂ : G} (h₁ : m₁ * e₁ * t₁ = 1) (h₂ : m₂ * e₂ * t₂ = 1)
    (h : r₁ * t₁ = r₂ * t₂) (hr : r₁ ≠ 0) : m₂ = e₁ * r₂ / (r₁ * e₂) * m₁ := by
  have he : e₂ ≠ 0 := by rintro rfl; simp at h₂
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hr he)]
  calc m₂ * (r₁ * e₂) = m₂ * (r₁ * e₂) * (m₁ * e₁ * t₁) := by rw [h₁, mul_one]
    _ = m₂ * e₂ * (r₁ * t₁) * (m₁ * e₁) := by ac_rfl
    _ = m₂ * e₂ * t₂ * (e₁ * r₂ * m₁) := by rw [h]; ac_rfl
    _ = _ := by rw [h₂, one_mul]

end Lin

section Lats

variable {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] {ξ : Sp Ω ⟶ X} {q : Cpt ξ}

theorem mu_gen_ratio {Λ : Lat ξ Ω} {t t' : Ω} (h : Λ.IsGenAt q t) (h' : Λ.IsGenAt q t') : t' / t ∈ regAt ξ q := by
  have : t' ∈ Submodule.span (regAt ξ q) {t} := h.2 ▸ h'.2 ▸ Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
  have e : (a : Ω) * t = t' := ha
  rw [← e, mul_div_cancel_right₀ _ h.1]
  exact a.2

theorem mu_gen_val {O : ValuationSubring Ω₃} {i : Ω →+* Ω₃} (hD : Dom O i ξ q) {Λ : Lat ξ Ω} {t t' : Ω} (h : Λ.IsGenAt q t)
    (h' : Λ.IsGenAt q t') : O.valuation (i t) = O.valuation (i t') := by
  have k : ∀ {t t' : Ω}, Λ.IsGenAt q t → Λ.IsGenAt q t' → O.valuation (i t') ≤ O.valuation (i t) := fun {t t'} h h' => by
    have h1 := (O.valuation_le_one_iff _).2 (hD.1 _ (mu_gen_ratio h h'))
    have e : t' = t * (t' / t) := (mul_div_cancel₀ _ h.1).symm
    rw [e, map_mul, map_mul]
    exact mul_le_of_le_one_right' h1
  exact le_antisymm (k h' h) (k h h')

theorem mu_tens_gen {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} (a : I → ℤ) {t : I → Ω} (h : ∀ j, (Λ j).IsGenAt q (t j)) :
    (Lat.tens Λ a).IsGenAt q (∏ j, t j ^ a j) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ (h j).1, le_antisymm (Submodule.span_le.2 ?_)
    (Submodule.span_le.2 ?_)⟩
  · rintro _ ⟨s, hs, rfl⟩
    have hm : ∏ j, (s j / t j) ^ a j ∈ regAt ξ q := prod_mem fun j _ => by
      obtain ⟨n, e | e⟩ := (a j).eq_nat_or_neg
      · rw [e, zpow_natCast]; exact pow_mem (mu_gen_ratio (h j) (hs j)) _
      · rw [e, zpow_neg, zpow_natCast, ← inv_pow, inv_div]; exact pow_mem (mu_gen_ratio (hs j) (h j)) _
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hm⟩, ?_⟩
    show (∏ j, (s j / t j) ^ a j) * ∏ j, t j ^ a j = _
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [← mul_zpow, div_mul_cancel₀ _ (h j).1]
  · rintro _ rfl
    exact Submodule.subset_span ⟨t, h, rfl⟩

theorem mu_tens_ex {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} {a : I → ℤ} {w : Ω} (h : (Lat.tens Λ a).IsGenAt q w) :
    ∃ t : I → Ω, ∀ j, (Λ j).IsGenAt q (t j) := by
  by_contra hn
  have e : (Lat.tens Λ a) q = ⊥ := by
    refine le_bot_iff.1 (Submodule.span_le.2 ?_)
    rintro _ ⟨s, hs, rfl⟩
    exact absurd ⟨s, hs⟩ hn
  have : w ∈ (Lat.tens Λ a) q := h.2 ▸ Submodule.mem_span_singleton_self _
  rw [e] at this
  exact h.1 this

theorem mu_deg_gen {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {Λ : Lat ξ Ω} {a : K → ℤ} {e : Ω}
    (h : Λ.IsDegOn Set.univ y a e) {ch : ∀ k, J k} (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ch q) :
    Λ.IsGenAt q ((∏ k, y ⟨k, ch k⟩ ^ a k) * e) :=
  ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ _))) h.1,
    h.2 q trivial ch hc⟩

theorem mu_char0 [Algebra ℚ Ω₃] {O : ValuationSubring Ω₃} {i : Ω →+* Ω₃} (hD : Dom O i ξ q)
    (hO : ∀ x : ℚ, algebraMap ℚ Ω₃ x ∈ O) (p : ℕ) (hp : p.Prime) : ¬ InFibre ξ p q := by
  have : CharZero Ω₃ := algebraRat.charZero Ω₃
  have h0 : (p : Ω) ≠ 0 := fun h => by
    have := congrArg i h
    rw [map_natCast, map_zero] at this
    exact hp.ne_zero (Nat.cast_eq_zero.1 this)
  refine not_not.2 ⟨h0, natCast_mem _ _, hD.2 _ (natCast_mem _ _) h0 ?_⟩
  simpa using hO (p : ℚ)⁻¹

theorem mu_side {V : Type} [AddCommGroup V] [Module Ω V] (L : Lat ξ V) {r r' : ℕ} (hr : r = r') (W : Submodule Ω V)
    (hL : L.IsVB r W) (c : Fin r → V) (hc : LinearIndependent Ω c) (hW : Submodule.span Ω (Set.range c) = W)
    (s : Fin r' → V) (hs : LinearIndependent Ω s) (hsW : ∀ k, s k ∈ W) :
    ∃ ρ : Ω, ρ ≠ 0 ∧ ∀ (q : Cpt ξ) (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃) (Ω₀ : Type) (ψ : Ω₀ → Ω) (B : Set (Fin r → Ω₀)),
      Dom O i ξ q → L q = Submodule.span (regAt ξ q) {w | ∃ a ∈ B, w = ∑ m, ψ (a m) • c m} →
      ∃ (t : Ω) (T : Matrix (Fin r) (Fin r) Ω₃), (detLat L s).IsGenAt q t ∧ T.det = i (ρ * t) ∧
        Submodule.span O (Set.range fun k m => T m k) = Submodule.span O {x | ∃ a ∈ B, x = fun m => i (ψ (a m))} := by
  subst hr
  subst hW
  choose P hP using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hsW k)
  have hPi : LinearIndependent Ω P := by
    refine LinearIndependent.of_comp (Fintype.linearCombination Ω c) ?_
    convert hs using 1
    funext k
    simpa [Fintype.linearCombination_apply] using hP k
  set Pm : Matrix (Fin r) (Fin r) Ω := (Matrix.of P).transpose with hPm
  have hd : Pm.det ≠ 0 := by
    rw [hPm, Matrix.det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hPi)).ne_zero
  refine ⟨Pm.det, hd, fun q O i Ω₀ ψ B hD hq => ?_⟩
  obtain ⟨U, hU, b, hb, hf⟩ := hL q trivial
  have hf := hf q trivial hU
  choose T₀ hT using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1
    (show b k ∈ Submodule.span Ω (Set.range c) from hb ▸ Submodule.subset_span ⟨k, rfl⟩)
  set Tm : Matrix (Fin r) (Fin r) Ω := (Matrix.of T₀).transpose with hTm
  have hPT : Pm * (Pm⁻¹ * Tm) = Tm := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hd), Matrix.one_mul]
  have hbs : ∀ k, b k = ∑ k', (Pm⁻¹ * Tm) k' k • s k' := fun k => by
    rw [← hT k]
    simp only [← hP, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have := congrFun (congrFun hPT m) k
    rw [Matrix.mul_apply] at this
    rw [show T₀ k m = Tm m k from rfl, ← this]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  refine ⟨(Pm⁻¹ * Tm).det, Tm.map i, _root_.LevelTowerAlt.determinant_lattice_generator X Ω ξ V L r s b _ q hs hf hbs, ?_, le_antisymm (Submodule.span_le.2 ?_)
    (Submodule.span_le.2 ?_)⟩
  · rw [← Matrix.det_mul, hPT]
    exact (RingHom.map_det i _).symm
  · rintro _ ⟨k, rfl⟩
    refine mu_coord O (regAt ξ q) i hD.1 c hc {w | ∃ a ∈ B, w = ∑ m, ψ (a m) • c m} _ ?_ (T₀ k) ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨_, rfl, Submodule.subset_span ⟨a, ha, rfl⟩⟩
    · rw [← hq, hT k, hf.2]
      exact Submodule.subset_span ⟨k, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine mu_coord O (regAt ξ q) i hD.1 c hc (Set.range b) _ ?_ (fun m => ψ (a m)) ?_
    · rintro _ ⟨k, rfl⟩
      exact ⟨T₀ k, (hT k).symm, Submodule.subset_span ⟨k, rfl⟩⟩
    · rw [← hf.2, hq]
      exact Submodule.subset_span ⟨a, ha, rfl⟩

end Lats

end SheetDecomposition
end
end

