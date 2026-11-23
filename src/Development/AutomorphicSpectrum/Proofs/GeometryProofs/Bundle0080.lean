module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.WeilBound.CoreStatements.AmpleLineBundles.ExistsPointsBoundedLineHeights
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0020
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundedHeightPointsDense
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Dense0

theorem dense_bounded_lines : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ), IsArithVar P d → ∀ (J : Type) [Fintype J] (A : J → HermLine ι), (∀ j, IsSmoothHerm (A j)) → ∃ C : ℝ, ∀ f : MRing ι, (∃ a, IsMultiHomog f a) → f ∉ P → ∃ (L : Type) (_ : Field L) (_ : NumberField L), ∃ w ∈ ptsOver L P, aeval w f ≠ 0 ∧ ∀ j, |lineHt (A j) L w| ≤ C :=
  @CoverDenseAlt.exists_points_bounded_line_heights

end GlobalTheory.CompanionTheory.Ar.Dense0
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharpolySplitsOfEmbeddings
section
open Polynomial NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ

theorem map_charpoly_lmul_eq_prod_embeddings (E : Type) [Field E] [NumberField E]
    (Ω : Type) [Field Ω] [Fintype (E →+* Ω)]
    (hc : Nat.card (E →+* Ω) = Module.finrank ℚ E) (a : 𝓞 E) :
    (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom Ω) =
      ∏ s : E →+* Ω, (X - C (s (a : E))) := by
  classical
  let e := NumberField.RingOfIntegers.basis E
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →+* Ω) := by
    rw [← Module.finrank_eq_card_basis e, NumberField.RingOfIntegers.rank, ← hc,
      Nat.card_eq_fintype_card]
  let eqv := Fintype.equivOfCardEq hcard
  let P : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E →ₐ[ℤ] Ω :=
    fun j => ((eqv j).comp (algebraMap (𝓞 E) E)).toIntAlgHom
  have hP : Function.Injective P := by
    intro i j hij
    apply eqv.injective
    apply IsFractionRing.injective_comp_algebraMap (A := 𝓞 E) (K := E) (L := Ω)
    show (eqv i).comp (algebraMap (𝓞 E) E) = (eqv j).comp (algebraMap (𝓞 E) E)
    ext x
    exact DFunLike.congr_fun hij x
  have h := GlobalTheory.map_charpoly_leftMulMatrix_eq_prod_algHom e hP a
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, algebraMap_int_eq] at h
  refine h.trans ?_
  exact Fintype.prod_equiv eqv _ _ fun j => rfl

theorem charpoly_lmul_splits_of_conjugates (E : Type) [Field E] [NumberField E]
    (Ω : Type) [Field Ω] [CharZero Ω] (O : Type) [CommRing O] [Algebra O Ω]
    (K : Type) [Field K] (g : O →+* K) (hinj : Function.Injective (algebraMap O Ω))
    (hc : Nat.card (E →+* Ω) = Module.finrank ℚ E)
    (hO : ∀ (s' : E →+* Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Ω).range) (a : 𝓞 E) :
    ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits := by
  classical
  haveI : Finite (E →+* Ω) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Module.finrank_pos.ne')
  letI : Fintype (E →+* Ω) := Fintype.ofFinite _
  have hO' : ∀ (s' : E →+* Ω) (a : 𝓞 E), ∃ y, algebraMap O Ω y = s' (a : E) :=
    fun s' a => RingHom.mem_range.mp (hO s' a)
  choose o ho using hO'
  have hΩ := GlobalTheory.CompanionTheory.Ar.Flat.DegZ.map_charpoly_lmul_eq_prod_embeddings E Ω hc a
  have hO2 : (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom O) =
      ∏ s : E →+* Ω, (X - C (o s a)) := by
    apply Polynomial.map_injective (algebraMap O Ω) hinj
    rw [Polynomial.map_map,
      RingHom.ext_int ((algebraMap O Ω).comp (Int.castRingHom O)) (Int.castRingHom Ω), hΩ,
      Polynomial.map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, ho]
  have hK : (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K) =
      ∏ s : E →+* Ω, (X - C (g (o s a))) := by
    rw [RingHom.ext_int (Int.castRingHom K) (g.comp (Int.castRingHom O)), ← Polynomial.map_map, hO2,
      Polynomial.map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [hK]
  exact Polynomial.Splits.prod fun s _ => Polynomial.Splits.X_sub_C _

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmConjugationCompatComplexConj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem conjugate_coe_eq_bar (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (τ : E →+* ℂ) (a : 𝓞 E) :
    ComplexEmbedding.conjugate τ (a : E) = τ (H.bar a : 𝓞 E) ∧ H.bar (H.bar a) = a := by
  constructor
  · rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  · apply RingOfIntegers.ext
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpEmbeddingFactorsThroughComplex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem exists_emb_through_coeff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : Nat.Primes)
    (κ : c.F →+* ℂ_[p]) (s : E →+* ℂ_[p]), ∃ τ : E →+* ℂ, s = κ.comp (inE c τ) := by
  intro E _ _ _ H l c p κ s
  haveI : CharZero ℂ_[p] := charZero_of_injective_ringHom κ.injective
  have hinj : Function.Injective (fun τ : E →+* ℂ => κ.comp (inE c τ)) := by
    intro τ τ' h
    ext a
    have h1 : κ (inE c τ a) = κ (inE c τ' a) := RingHom.congr_fun h a
    have h2 := κ.injective h1
    exact congrArg (fun x : c.F => (x : ℂ)) h2
  have hle : Nat.card (E →+* ℂ_[p]) ≤ Nat.card (E →+* ℂ) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, NumberField.Embeddings.card E ℂ,
      NumberField.Embeddings.card E ℂ_[p]]
  haveI : Finite (E →+* ℂ_[p]) := inferInstance
  obtain ⟨τ, hτ⟩ := (hinj.bijective_of_nat_card_le hle).2 s
  exact ⟨τ, hτ.symm⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpIntegersValuationRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem norm_prime_padicComplex (p : Nat.Primes) : ‖((p : ℕ) : ℂ_[p])‖ = ((p : ℕ) : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]

theorem ocp_integers : ∀ p : Nat.Primes, (NormedField.valuation (K := ℂ_[p])).Integers (OCp p) ∧
    (∃ x : ℂ_[p], 0 < NormedField.valuation (K := ℂ_[p]) x ∧ NormedField.valuation (K := ℂ_[p]) x < 1) ∧
    ∀ x : ℂ_[p], x ∈ (algebraMap (OCp p) ℂ_[p]).range ↔ ‖x‖ ≤ 1 := by
  intro p
  have hI : (NormedField.valuation (K := ℂ_[p])).Integers (GlobalTheory.CompanionTheory.Ar.Flat.CPoint.OCp p) :=
    Valuation.valuationSubring.integers _
  refine ⟨hI, ⟨((p : ℕ) : ℂ_[p]), ?_, ?_⟩, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_zero,
      GlobalTheory.CompanionTheory.Ar.Flat.CPoint.norm_prime_padicComplex]
    exact inv_pos.2 (by exact_mod_cast p.2.pos)
  · rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one,
      GlobalTheory.CompanionTheory.Ar.Flat.CPoint.norm_prime_padicComplex]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)
  · obtain ⟨y, rfl⟩ := RingHom.mem_range.1 hx
    have h := hI.map_le_one y
    rwa [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one] at h
  · refine RingHom.mem_range.2 (hI.exists_of_le_one ?_)
    rwa [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspDataOfFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

section Ip

variable (R : RiemLat E g Λ)

theorem ip_add_right (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' := by
  simp [RiemLat.ip, add_dotProduct]

theorem ip_smul_right (c : ℂ) (x y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y := by
  simp [RiemLat.ip, smul_dotProduct]

theorem ip_conj (x y : Fin g → ℂ) : starRingEnd ℂ (R.ip x y) = R.ip y x := by
  show star (y ⬝ᵥ R.Hm *ᵥ star x) = x ⬝ᵥ R.Hm *ᵥ star y
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

def ipL (x : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun := R.ip x
  map_add' := ip_add_right R x
  map_smul' c y := ip_smul_right R c x y

theorem ip_add_left (x x' y : Fin g → ℂ) : R.ip (x + x') y = R.ip x y + R.ip x' y := by
  rw [← ip_conj R y, ip_add_right, map_add (f := _), ip_conj, ip_conj]

theorem ip_smul_left (c : ℂ) (x y : Fin g → ℂ) : R.ip (c • x) y = starRingEnd ℂ c * R.ip x y := by
  rw [← ip_conj R y, ip_smul_right, map_mul, ip_conj]

end Ip

section Eig

variable (R : RiemLat E g Λ)

theorem ip_sum_right {A : Type} (t : Finset A) (f : A → Fin g → ℂ) (x : Fin g → ℂ) :
    R.ip x (∑ i ∈ t, f i) = ∑ i ∈ t, R.ip x (f i) := map_sum (ipL R x) f t

theorem ip_sum_left {A : Type} (t : Finset A) (f : A → Fin g → ℂ) (y : Fin g → ℂ) :
    R.ip (∑ i ∈ t, f i) y = ∑ i ∈ t, R.ip (f i) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← ip_conj R y, ip_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => ip_conj R y (f i)


omit [IsCMField E] in
theorem comp_ne {s s' : E →+* ℂ} (h : s ≠ s') :
    s.comp (algebraMap (𝓞 E) E) ≠ s'.comp (algebraMap (𝓞 E) E) :=
  fun e => h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e)


omit [IsCMField E] in
theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def extEmb (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (emb_injective s)

omit [IsCMField E] in
theorem extEmb_apply (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : extEmb s (algebraMap (𝓞 E) E a) = s a :=
  IsFractionRing.lift_algebraMap (emb_injective s) a

omit [IsCMField E] in
theorem extEmb_comp (s : 𝓞 E →+* ℂ) : (extEmb s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext (extEmb_apply s)


end Eig

section Family

variable {K : Type} {J : K → Type} {Ψ : Type}



variable {T : Set ((Σ k, J k) → ℂ)} {R : ((Σ k, J k) → ℂ) → RiemLat E g Λ} {w : (Σ k, J k) → ℂ}

end Family

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.Lin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointComponentEigenReduction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.PointVal

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def baseFn {O : Type} [CommRing O] (s : X ⟶ Sp O) (o : O) : Γ(X, ⊤) :=
  s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)


set_option backward.isDefEq.respectTransparency false in
theorem baseFn_value {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] (s : X ⟶ Sp O) (f : Sp R ⟶ X)
    (φ : O →+* R) (hf : f ≫ s = spMap φ) (o : O) :
    (Scheme.stalkClosedPointTo f).hom (X.presheaf.germ ⊤ (centre f) trivial (baseFn s o)) = φ o := by
  have e : X.presheaf.germ ⊤ (f (IsLocalRing.closedPoint R)) trivial ≫ Scheme.stalkClosedPointTo f =
      f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    set_option backward.isDefEq.respectTransparency.types false in
      rw [Scheme.germ_stalkClosedPointTo]
      simp [Iso.trans_hom, Scheme.Hom.appTop]
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ s.appTop ≫ f.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom = CommRingCat.ofHom φ := by
    rw [← Category.assoc s.appTop, ← Scheme.Hom.comp_appTop, hf, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
  rw [← e] at e2
  exact congrArg (fun q => q.hom o) e2


set_option backward.isDefEq.respectTransparency false in
theorem genMap_germ (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (g : Γ(X, ⊤)) :
    genMap ξ p (X.presheaf.germ ⊤ p.1 trivial g) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ ⊤ (genPt ξ) trivial g) := by
  have e := TopCat.Presheaf.germ_stalkSpecializes X.presheaf (U := ⊤) (x := genPt ξ) (y := p.1) trivial p.2
  have e2 := congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom g) e
  exact e2


set_option backward.isDefEq.respectTransparency false in
theorem genMap_specializes (ξ : Sp Ω ⟶ X) (p q : Cpt ξ) (h : p.1 ⤳ q.1) (s : X.presheaf.stalk q.1) :
    genMap ξ p ((X.presheaf.stalkSpecializes h).hom s) = genMap ξ q s := by
  have e := TopCat.Presheaf.stalkSpecializes_comp X.presheaf p.2 h
  have e2 := congrArg (fun r => (r ≫ Scheme.stalkClosedPointTo ξ).hom s) e
  exact e2

theorem exists_inv {A L₁ L₂ : Type} [CommRing A] [Field L₁] [Field L₂] (f₁ : A →+* L₁) (f₂ : A →+* L₂)
    (hl : ∀ b, IsUnit (f₂ b) → IsUnit b) (g : A) (a₁ : L₁) (a₂ : L₂) (ha : a₂ ≠ 0)
    (h₁ : f₁ g = a₁⁻¹) (h₂ : f₂ g = a₂⁻¹) : ∃ u, f₁ u = a₁ ∧ f₂ u = a₂ := by
  obtain ⟨g, rfl⟩ := hl g (by rw [h₂]; exact (inv_ne_zero ha).isUnit)
  refine ⟨(g⁻¹ : Aˣ), ?_, ?_⟩
  · have := map_units_inv f₁.toMonoidHom g
    refine this.trans ?_
    show (f₁ g)⁻¹ = _
    rw [h₁, inv_inv]
  · have := map_units_inv f₂.toMonoidHom g
    refine this.trans ?_
    show (f₂ g)⁻¹ = _
    rw [h₂, inv_inv]

def valMap (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (hi : Function.Injective (genMap ξ p)) {R : Type} [CommRing R]
    (ev : X.presheaf.stalk p.1 →+* R) : regAt ξ p →+* R :=
  ev.comp (RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun _ _ h => hi (congrArg Subtype.val h), (genMap ξ p).rangeRestrict_surjective⟩).symm.toRingHom

theorem valMap_genMap (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (hi : Function.Injective (genMap ξ p)) {R : Type} [CommRing R]
    (ev : X.presheaf.stalk p.1 →+* R) (s : X.presheaf.stalk p.1) (h : genMap ξ p s ∈ regAt ξ p) :
    valMap ξ p hi ev ⟨genMap ξ p s, h⟩ = ev s := by
  have : (RingEquiv.ofBijective (genMap ξ p).rangeRestrict
      ⟨fun _ _ h => hi (congrArg Subtype.val h), (genMap ξ p).rangeRestrict_surjective⟩).symm
      ⟨genMap ξ p s, h⟩ = s := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  show ev _ = ev s
  exact congrArg ev this

variable {O F V K : Type} [CommRing O] [Field F] [CommRing V] [IsLocalRing V] [Field K] [Algebra V K]

theorem exists_germ (ξ : Sp Ω ⟶ X) (s : X ⟶ Sp O) (inc : F →+* Ω) (β : O →+* F) (βK : F →+* K) (y : Sp K ⟶ X)
    (hξ : ξ ≫ s = spMap (inc.comp β)) (hy : y ≫ s = spMap (βK.comp β)) (h₁ : genPt ξ ⤳ centre y) (x : F)
    (hx : x ∈ β.range ∨ x⁻¹ ∈ β.range) :
    ∃ u : X.presheaf.stalk (centre y), genMap ξ ⟨_, h₁⟩ u = inc x ∧ (Scheme.stalkClosedPointTo y).hom u = βK x := by
  have key : ∀ o : O, genMap ξ ⟨_, h₁⟩ (X.presheaf.germ ⊤ (centre y) trivial (baseFn s o)) = inc (β o) ∧
      (Scheme.stalkClosedPointTo y).hom (X.presheaf.germ ⊤ (centre y) trivial (baseFn s o)) = βK (β o) := by
    intro o
    refine ⟨?_, baseFn_value s y (βK.comp β) hy o⟩
    exact (genMap_germ ξ ⟨_, h₁⟩ (baseFn s o)).trans (baseFn_value s ξ (inc.comp β) hξ o)
  by_cases h0 : x = 0
  · subst h0
    exact ⟨0, (map_zero _).trans (map_zero inc).symm,
      (map_zero (Scheme.stalkClosedPointTo y).hom).trans (map_zero βK).symm⟩
  rcases hx with ⟨o, rfl⟩ | ⟨o, ho⟩
  · exact ⟨_, key o⟩
  obtain ⟨k1, k2⟩ := key o
  rw [ho] at k1 k2
  exact exists_inv (genMap ξ ⟨_, h₁⟩) (Scheme.stalkClosedPointTo y).hom
    (fun b hb => (Scheme.isLocalHom_stalkClosedPointTo' y).map_nonunit b hb) _ (inc x) (βK x) ((map_ne_zero βK).2 h0)
    (k1.trans (map_inv₀ inc x)) (k2.trans (map_inv₀ βK x))

theorem val_abs (ξ : Sp Ω ⟶ X) (hg : IsCptGen ξ) (s : X ⟶ Sp O) (inc : F →+* Ω) (β : O →+* F) (βK : F →+* K)
    (y : Sp K ⟶ X) (z : Sp V ⟶ X) (hξ : ξ ≫ s = spMap (inc.comp β)) (hy : y ≫ s = spMap (βK.comp β))
    (hz : spMap (algebraMap V K) ≫ z = y) (h₁ : genPt ξ ⤳ centre y)
    (hF : ∀ x : F, x ∈ β.range ∨ x⁻¹ ∈ β.range) :
    ∃ (h₂ : genPt ξ ⤳ centre z) (ψ : regAt ξ ⟨_, h₁⟩ →+* K),
      centre y ⤳ centre z ∧ regAt ξ ⟨_, h₂⟩ ≤ regAt ξ ⟨_, h₁⟩ ∧
      (∀ a : regAt ξ ⟨_, h₁⟩, ValAt ξ y (a : Ω) (ψ a)) ∧
      (∀ (a : Ω) (r : K), ValAt ξ y a r → ∃ h, ψ ⟨a, h⟩ = r) ∧
      (∀ (a : Ω) (h : a ∈ regAt ξ ⟨_, h₁⟩), a ∈ regAt ξ ⟨_, h₂⟩ → ψ ⟨a, h⟩ ∈ (algebraMap V K).range) ∧
      ∀ x : F, ∃ h : inc x ∈ regAt ξ ⟨_, h₁⟩, ψ ⟨_, h⟩ = βK x := by
  have hsp : centre y ⤳ centre z := by
    subst hz
    exact (IsLocalRing.specializes_closedPoint _).map z.continuous
  have h₂ : genPt ξ ⤳ centre z := h₁.trans hsp
  let ψ : regAt ξ ⟨_, h₁⟩ →+* K := valMap ξ ⟨_, h₁⟩ (hg.inj _) (Scheme.stalkClosedPointTo y).hom
  have c3 : ∀ a : regAt ξ ⟨_, h₁⟩, ValAt ξ y (a : Ω) (ψ a) := by
    rintro ⟨_, s', rfl⟩
    exact ⟨h₁, s', rfl, (valMap_genMap ξ ⟨_, h₁⟩ (hg.inj _) _ s' _).symm⟩
  have c4 : ∀ (a : Ω) (r : K), ValAt ξ y a r → ∃ h, ψ ⟨a, h⟩ = r := by
    rintro a r ⟨h, s', rfl, rfl⟩
    exact ⟨⟨s', rfl⟩, valMap_genMap ξ ⟨_, h₁⟩ (hg.inj _) _ s' _⟩
  refine ⟨h₂, ψ, hsp, ?_, c3, c4, ?_, ?_⟩
  · rintro _ ⟨s', rfl⟩
    refine ⟨(X.presheaf.stalkSpecializes hsp).hom s', ?_⟩
    exact genMap_specializes ξ ⟨_, h₁⟩ ⟨_, h₂⟩ hsp s'
  · rintro a h ⟨s', rfl⟩
    have v : ValAt ξ z (genMap ξ ⟨_, h₂⟩ s') ((Scheme.stalkClosedPointTo z).hom s') := ⟨h₂, s', rfl, rfl⟩
    have v' := _root_.GlobalTheory.CompanionTheory.Ar.ChangeRing.valAt_change X Ω ξ V K (algebraMap V K) z _ _ v (by rw [hz]; exact h₁)
    rw [hz] at v'
    obtain ⟨h', e⟩ := c4 _ _ v'
    exact ⟨_, e.symm⟩
  · intro x
    obtain ⟨u, e1, e2⟩ := exists_germ ξ s inc β βK y hξ hy h₁ x (hF x)
    obtain ⟨h, e⟩ := c4 _ _ (⟨h₁, u, e1, e2⟩ : ValAt ξ y (inc x) (βK x))
    exact ⟨h, e⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.PointVal

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem point_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (j : K →+* ℂ_[p]) (βK : c.F →+* K) (y : Sp K ⟶ Xo.XF c) (z : Sp V ⟶ Y.X),
    Function.Injective β → (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) →
    j.comp βK = κ → y ≫ pullback.snd _ _ = spMap βK → Set.range y ⊆ U → spMap (algebraMap V K) ≫ z = y ≫ Y.j →
    ∃ (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (h₂ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre z)
      (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K),
      centre (y ≫ Y.j) ⤳ centre z ∧ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ ≤ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ ∧
      (∀ a : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (a : Z.Ω) (ψ a)) ∧
      (∀ (a : Z.Ω) (r : K), ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) a r → ∃ h, ψ ⟨a, h⟩ = r) ∧
      (∀ (a : Z.Ω) (h : a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩), a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ →
        ψ ⟨a, h⟩ ∈ (algebraMap V K).range) ∧
      ∀ x : c.F, ∃ h : Z.inc x ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ψ ⟨_, h⟩ = βK x := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z p κ V K _ _ _ _ _ _ j βK y z hβ hκ hj hjk hy hU hz
  have hsj : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have hξ : (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp β) := by
    rw [Category.assoc, hsj, ← Category.assoc, Z.over_inc, ← Spec.map_comp]
    rfl
  have hy' : (y ≫ Y.j) ≫ Y.s = spMap (βK.comp β) := by
    rw [Category.assoc, hsj, ← Category.assoc, hy, ← Spec.map_comp]
    rfl
  have h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) :=
    ((Z.closure _).1 (hU ⟨IsLocalRing.closedPoint K, rfl⟩)).map Y.j.continuous
  have hF : ∀ x : c.F, x ∈ β.range ∨ x⁻¹ ∈ β.range := by
    intro x
    by_cases h : ‖κ x‖ ≤ 1
    · exact Or.inl ((hκ x).1 h)
    · refine Or.inr ((hκ _).1 ?_)
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ (not_le.1 h).le
  obtain ⟨h₂, ψ, r⟩ := PointVal.val_abs (Z.ξ₀ ≫ Y.j) Z.gen Y.s Z.inc β βK (y ≫ Y.j) z hξ hy' hz h₁ hF
  exact ⟨h₁, h₂, ψ, r⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

