module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnipotentLatticeMembership
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypesIdempotentCoefficients
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1074
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnitsOfIsCompactClosureZpowersMul
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwLat

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

noncomputable def mulMatHom : B.A →+* Matrix (Fin m) (Fin m) (w.adicCompletion E) :=
  (e : K.E →+* w.adicCompletion E).mapMatrix.comp
    ((LinearMap.toMatrixAlgEquiv b).toRingHom.comp (Algebra.lmul K.E B.A).toRingHom)

theorem mulMatHom_apply (a : B.A) : mulMatHom e b a = mulMat e b a := by
  rw [mulMat_eq_map]
  simp only [mulMatHom, RingHom.comp_apply]
  congr 1

theorem mulMatHom_algebraMap (x : K.E) :
    mulMatHom e b (algebraMap K.E B.A x) = algebraMap (w.adicCompletion E) _ (e x) := by
  simp only [mulMatHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgEquiv.coe_toRingEquiv,
    RingEquiv.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  rw [Matrix.algebraMap_eq_diagonal, Matrix.algebraMap_eq_diagonal]
  simp [Pi.algebraMap_def]

theorem mulMatHom_injective : Function.Injective (mulMatHom e b) := by
  intro a a' h
  rw [mulMatHom_apply, mulMatHom_apply] at h
  exact mulMat_injective e b h

theorem isIntegral_of_isIntegral_mulMat
    (hint : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (a : B.A)
    (h : IsIntegral (w.adicCompletionIntegers E) (mulMat e b a)) : IsIntegral K.O a := by
  obtain ⟨p, hpm, hp⟩ := h
  set Q : (w.adicCompletion E)[X] := p.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) with hQdef
  have hQ : aeval (mulMat e b a) Q = 0 := by
    rw [hQdef, aeval_map_algebraMap]; exact hp
  set Q' : K.E[X] := Q.map e.symm.toRingHom with hQ'def
  have hQQ : Q'.map (e : K.E →+* w.adicCompletion E) = Q := by
    rw [hQ'def, Polynomial.map_map]
    convert Polynomial.map_id
    ext x; simp
  have hu : aeval a Q' = 0 := by
    apply mulMatHom_injective e b
    rw [map_zero, aeval_def, Polynomial.hom_eval₂]
    have hc : (mulMatHom e b).comp (algebraMap K.E B.A) =
        (algebraMap (w.adicCompletion E) (Matrix (Fin m) (Fin m) (w.adicCompletion E))).comp
          (e : K.E →+* w.adicCompletion E) := by
      ext x; simp [mulMatHom_algebraMap]
    rw [hc, ← Polynomial.eval₂_map, hQQ, mulMatHom_apply, ← aeval_def]
    exact hQ
  have hlift : Q' ∈ Polynomial.lifts (algebraMap K.O K.E) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [hQ'def, Polynomial.coeff_map, hQdef, Polynomial.coeff_map]
    have hv : Valued.v (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) (p.coeff i)) ≤ 1 :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (p.coeff i).2
    have := (hint (e.symm (algebraMap _ _ (p.coeff i)))).2 (by simpa using hv)
    simpa using this
  obtain ⟨P, hPm, -, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift (by rw [hQ'def]; exact (hpm.map _).map _)
  refine ⟨P, hPmon, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K.E, hPm]
  exact hu

theorem mem_intUnits_of_isCompact_closure_zpowers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (a : B.Aˣ), IsCompact (closure (Subgroup.zpowers (GlobalTheory.TwLat.mulU e b a) : Set (GLw m w))) → a ∈ GlobalTheory.UnitLemma.intUnits K.O B.A := by
  intro E _ _ _ _ w _ K e _ hint _ B m b a hc
  have h1 : IsIntegral (w.adicCompletionIntegers E) (mulMat e b (a : B.A)) := by
    rw [← mulU_val]
    exact GlobalTheory.isIntegral_of_isCompact_closure_zpowers E w m _ hc
  have hc' : IsCompact (closure (Subgroup.zpowers (mulU e b a⁻¹) : Set (GLw m w))) := by
    rw [map_inv, Subgroup.zpowers_inv]; exact hc
  have h2 : IsIntegral (w.adicCompletionIntegers E) (mulMat e b ((a⁻¹ : B.Aˣ) : B.A)) := by
    rw [← mulU_val]
    exact GlobalTheory.isIntegral_of_isCompact_closure_zpowers E w m _ hc'
  exact ⟨isIntegral_of_isIntegral_mulMat e b hint _ h1, isIntegral_of_isIntegral_mulMat e b hint _ h2⟩

end GlobalTheory.TwLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlmostLowerTriangularOfShearParabolic
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem shear_apply_of_ne {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {K : Type} [CommRing K] (t : K)
    {σ : ι} (h : σ ≠ τ) : shear τ a b t σ = 1 := by
  ext i k
  simp only [shear, Matrix.add_apply, Matrix.of_apply]
  rw [if_neg, add_zero]
  rintro ⟨h1, -⟩
  exact h (congrArg Sigma.fst h1)

theorem shear_self_mul_apply {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {K : Type} [CommRing K] (t : K)
    (A : Matrix (Fin (m τ)) (Fin (m τ)) K) (i c : Fin (m τ)) :
    (shear τ a b t τ * A) i c = A i c + if i = a then t * A b c else 0 := by
  have e : ∀ k, shear τ a b t τ i k = (1 : Matrix (Fin (m τ)) (Fin (m τ)) K) i k + if i = a ∧ k = b then t else 0 := by
    intro k
    simp only [shear, Matrix.add_apply, Matrix.of_apply]
    congr 1
    by_cases h1 : i = a <;> by_cases h2 : k = b <;> simp [h1, h2]
  rw [Matrix.mul_apply]
  simp only [e, add_mul, Finset.sum_add_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases h1 : i = a <;> simp [h1]

theorem almostLow_of_shear : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 →
    ∀ (L K : Type) [Field L] [Field K] (j : L →+* K) (t : K), t ≠ 0 → ∀ C : Mat m L,
      Par m ⊤ (shear τ a b t * C.map j) → AlmostLow τ a b C := by
  intro ι m τ a b hab L K _ _ j t ht C hP
  have hmap : ∀ σ i c, (C.map j) σ i c = j (C σ i c) := fun _ _ _ => rfl
  have hL : ∀ σ, shear τ a b t σ * (C.map j) σ = (shear τ a b t * C.map j) σ := fun _ => rfl
  have hz : ∀ σ (i c : Fin (m σ)), i < c → (shear τ a b t σ * (C.map j) σ) i c = 0 := fun σ i c h => by
    rw [hL]; exact (hP σ).2.2.2 i c i.isLt h
  have hd : ∀ σ, (shear τ a b t σ * (C.map j) σ).det ≠ 0 := fun σ => by rw [hL]; exact (hP σ).2.1
  have hdiag : ∀ σ (i : Fin (m σ)), (shear τ a b t σ * (C.map j) σ) i i ≠ 0 := fun σ i => by
    have hbt : (shear τ a b t σ * (C.map j) σ).BlockTriangular OrderDual.toDual := fun p q hpq =>
      hz σ p q (OrderDual.toDual_lt_toDual.1 hpq)
    have := hd σ
    rw [Matrix.det_of_lowerTriangular _ hbt] at this
    exact Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ _)
  have hab' : a < b := by rw [Fin.lt_def]; omega
  have hba : b ≠ a := ne_of_gt hab'
  refine ⟨fun σ hσ => hd σ ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Mat.det_map, hσ, map_zero, mul_zero]
  · intro h0
    have h1 := hz τ a b hab'
    have h2 := hdiag τ b
    rw [shear_self_mul_apply] at h1 h2
    rw [if_pos rfl, hmap, h0, map_zero, zero_add] at h1
    rw [if_neg hba, add_zero] at h2
    exact h2 ((mul_eq_zero.1 h1).resolve_left ht)
  · intro σ i c hic hn
    refine (map_eq_zero j).1 ?_
    rw [← hmap]
    by_cases hσ : σ = τ
    · subst hσ
      have hn' : ¬ (i = a ∧ c = b) := fun h => hn ⟨by rw [h.1], by rw [h.2]⟩
      have h1 := hz σ i c hic
      rw [shear_self_mul_apply] at h1
      by_cases hi : i = a
      · subst hi
        have hcb : c ≠ b := fun h => hn' ⟨rfl, h⟩
        have hbc : b < c := by
          rw [Fin.lt_def] at hic ⊢
          have : (c : ℕ) ≠ b := fun h => hcb (Fin.ext h)
          omega
        have h2 := hz σ b c hbc
        rw [shear_self_mul_apply, if_neg hba, add_zero] at h2
        rw [if_pos rfl, h2, mul_zero, add_zero] at h1
        exact h1
      · rw [if_neg hi, add_zero] at h1
        exact h1
    · have h1 := hz σ i c hic
      rw [shear_apply_of_ne τ a b t hσ, one_mul] at h1
      exact h1

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
section
noncomputable section

namespace GlobalTheory.GoodLatCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Arith Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLatticeMembership

section Clause

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G']


end Clause

section Forms

variable {D : D7} (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j)
variable {LL : Type} [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
  [Module (𝓞 T.Q.c.F) WL] [IsScalarTower (𝓞 T.Q.c.F) T.Q.c.F WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G : Type} [Group G]

end Forms

section Local

variable {κ κ' : Type} [CommRing κ] [CommRing κ'] {r : ℕ}

end Local

structure PlaceIso (D : D7) (Pg : Finset (Pl D.host.E)) where
  pl : TypePl D ≃ ↥Pg
  iso : ∀ v : TypePl D, ZMod (D.host.g v.1) ≃+* kP (pl v).1

namespace PlaceIso

variable {D : D7} {Pg : Finset (Pl D.host.E)} (P : PlaceIso D Pg) {LL : Type} [Field LL]

end PlaceIso

section Places

open scoped Pointwise

variable {D : D7}

variable {T : Core D} (hb : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (T.pb k).asIdeal)
include hb

end Places


open GlobalTheory.MemN.TypesInhab in
theorem goodSeriesIdempotent_central_idempotent (D : D7) :
    D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) ∧ D.ntypes.e0 * D.ntypes.e0 = D.ntypes.e0 := by
  classical
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  obtain ⟨hc, hm⟩ := good_sum (I := TypePl D) (P := fun v => Fin D.R.r → ZMod (D.host.g v.1))
    (fun v p => D.ntypes.eSer v.1 (Formalism.CyclotomicNorms.monicOf p))
    (fun a => D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))) D.ntypes.e0 (fun g => rfl)
    (fun _ _ => D.ntypes.eSer_idem _ _) (fun _ _ => D.ntypes.eSer_central _ _)
    (fun _ p q hpq => D.ntypes.eSer_orth _ _ _ fun h => hpq (funext fun i => by
      rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt p i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]))
  refine ⟨hc, ?_⟩
  have h : D.ntypes.e0 = ∑ a : ∀ v : TypePl D, Fin D.R.r → ZMod (D.host.g v.1),
      if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ten (fun v => D.ntypes.eSer v.1 (Formalism.CyclotomicNorms.monicOf (a v))) else 0 := by
    ext g
    rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    refine (finsum_eq_sum_of_fintype _).trans (Finset.sum_congr rfl fun a _ => ?_)
    split_ifs <;> rfl
  conv_lhs => rhs; rw [h]
  rw [Finset.mul_sum]
  conv_rhs => rw [h]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · rw [hm, if_pos ha]
  · rw [mul_zero]

theorem isCentralIdempotent_of_goodSeriesIdempotent {D : D7} {LL : Type} [Field LL] (σ₀ : LL →+* ℂ) {eC : G0g D.nd → LL}
    (h : ∀ g, σ₀ (eC g) = D.ntypes.e0.coeff g) : IsCentralIdem eC := by
  obtain ⟨hc, hi⟩ := goodSeriesIdempotent_central_idempotent D
  refine ⟨fun g x => σ₀.injective ?_, fun g => σ₀.injective ?_⟩
  · have := congrArg (fun z => z.coeff (x * g))
      (Subalgebra.mem_center_iff.1 hc (MonoidAlgebra.single x (1 : ℂ)))
    simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply, inv_mul_cancel_left, one_mul, mul_one] at this
    rw [h, h, this]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, h, ← hi, GlobalTheory.MemN.TypesInhab.coeff_mul_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [map_mul, h, h]

section Sides

variable {D : D7} (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j)
  (LL : Type) [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]

end Sides

end GlobalTheory.GoodLatCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersMulIntegralUnit
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.IntCpt

open IsDedekindDomain.HeightOneSpectrum

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

theorem entries_le_one (hint : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1)
    (g : GLw m w) (x : B.A) (hx : ∀ y ∈ GlobalTheory.TwLat.lat e b g, x * y ∈ GlobalTheory.TwLat.lat e b g) (i j : Fin m) :
    Valued.v (((g⁻¹).val * GlobalTheory.TwLat.mulMat e b x * g.val) i j) ≤ 1 := by
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin m) (Fin m) (w.adicCompletion E),
      Y = (g⁻¹).val * GlobalTheory.TwLat.mulMat e b x * g.val := ⟨_, rfl⟩
  rw [← hY]
  have hgY : g.val * Y = GlobalTheory.TwLat.mulMat e b x * g.val := by
    rw [hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hgcol : ∀ j, x * Lv.col e b g.val j = ∑ l, e.symm (Y l j) • Lv.col e b g.val l := by
    intro j
    rw [Lv.mul_col, ← hgY]
    apply b.repr.injective
    ext i
    rw [Lv.repr_sum_smul_col, Lv.repr_col]
    simp only [RingEquiv.apply_symm_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have hmem : x * Lv.col e b g.val j ∈ GlobalTheory.TwLat.lat e b g := hx _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun K.O).mp hmem
  have ho' : ∑ l, algebraMap K.O K.E (o l) • Lv.col e b g.val l = ∑ l, e.symm (Y l j) • Lv.col e b g.val l := by
    rw [← hgcol j, ← ho]
    exact Finset.sum_congr rfl fun l _ => algebraMap_smul K.E (o l) _
  have := congrFun (Lv.sum_smul_col_inj e b g _ _ ho') i
  have hi := (hint (algebraMap K.O K.E (o i))).mp ⟨o i, rfl⟩
  rw [this, RingEquiv.apply_symm_apply] at hi
  exact hi

theorem isCompact_intGL :
    IsCompact {h : GLw m w | (∀ i j, Valued.v (h.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((h⁻¹).val i j) ≤ 1} := by
  have hO : IsCompact ((w.adicCompletionIntegers E).toSubring : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers E w)
  have := GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint (n := Fin m) _ hO
  rw [GlobalTheory.LFun.IntPtsUnitary.coe_GLint] at this
  convert this using 1
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, ValuationSubring.mem_toSubring, mem_adicCompletionIntegers]

def unitsIn (R : Subalgebra K.O B.A) : Subgroup B.Aˣ where
  carrier := {u | (u : B.A) ∈ R ∧ ((u⁻¹ : B.Aˣ) : B.A) ∈ R}
  one_mem' := by simp [R.one_mem]
  mul_mem' := by
    intro u v hu hv
    refine ⟨by simpa using R.mul_mem hu.1 hv.1, ?_⟩
    rw [_root_.mul_inv_rev, Units.val_mul]
    exact R.mul_mem hv.2 hu.2
  inv_mem' := by
    intro u hu
    exact ⟨hu.2, by simpa using hu.1⟩

end GlobalTheory.TwLat.IntCpt

namespace GlobalTheory.TwLat

open IsDedekindDomain.HeightOneSpectrum

theorem isCompact_closure_zpowers_mulU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (a : B.Aˣ), a ∈ GlobalTheory.UnitLemma.intUnits K.O B.A → IsCompact (closure (Subgroup.zpowers (GlobalTheory.TwLat.mulU e b a) : Set (GLw m w))) := by
  intro E _ _ _ hU w hw K e hc hint hval B m b a ha
  let R : Subalgebra K.O B.A := Algebra.adjoin K.O {(a : B.A), ((a⁻¹ : B.Aˣ) : B.A)}
  haveI : Module.Finite K.O R := by
    apply Algebra.finite_adjoin_of_finite_of_isIntegral (Set.toFinite _)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha.1
    · exact ha.2
  let L : Submodule K.O B.A := (Submodule.span R (Set.range b)).restrictScalars K.O
  have hLfg : L.FG := Submodule.FG.restrictScalars (Submodule.fg_span (Set.finite_range b))
  have hbL : ∀ i, b i ∈ L := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hLsp : Submodule.span K.E (L : Set B.A) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (hbL i)
  have hLst : ∀ x ∈ R, ∀ y ∈ L, x * y ∈ L := by
    intro x hx y hy
    exact (Submodule.span R (Set.range b)).smul_mem (⟨x, hx⟩ : R) hy
  obtain ⟨g, hg⟩ := GlobalTheory.TwLat.exists_GLw_lat_eq E hU w hw K e hc hint hval B m b L ⟨hLfg, hLsp⟩
  have haH : a ∈ IntCpt.unitsIn R :=
    ⟨Algebra.subset_adjoin (Set.mem_insert _ _), Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)⟩
  let S : Set (GLw m w) := {h | (∀ i j, Valued.v (h.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((h⁻¹).val i j) ≤ 1}
  have hC : IsCompact ((fun h => g * h * g⁻¹) '' S) :=
    (IntCpt.isCompact_intGL (w := w) (m := m)).image (by fun_prop)
  have hsub : (Subgroup.zpowers (mulU e b a) : Set (GLw m w)) ⊆ (fun h => g * h * g⁻¹) '' S := by
    rintro _ ⟨k, rfl⟩
    have hu : a ^ k ∈ IntCpt.unitsIn R := zpow_mem haH k
    refine ⟨g⁻¹ * mulU e b (a ^ k) * g, ⟨?_, ?_⟩, ?_⟩
    · intro i j
      have := IntCpt.entries_le_one e b hint g _ (hg ▸ hLst _ hu.1) i j
      rw [Units.val_mul, Units.val_mul, mulU_val]
      exact this
    · intro i j
      have := IntCpt.entries_le_one e b hint g _ (hg ▸ hLst _ hu.2) i j
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← map_inv (mulU e b), ← mul_assoc, Units.val_mul,
        Units.val_mul, mulU_val]
      exact this
    · show g * (g⁻¹ * mulU e b (a ^ k) * g) * g⁻¹ = mulU e b a ^ k
      rw [map_zpow]
      group
  exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)

end GlobalTheory.TwLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOffCoordinateHyperplanes
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop


open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
theorem _root_.GlobalTheory.GoodTop.isOpen_offHyp_of_isOpen {n : ℕ} (S : Finset (Fin n)) (U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (hU : IsOpen U) :
    IsOpen (_root_.GlobalTheory.GoodTop.offHyp S U) := by
  unfold _root_.GlobalTheory.GoodTop.offHyp
  have hset : {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v ∈ U ∧ ∀ a ∈ S, v.ofLp a ≠ 0} =
      U ∩ ⋂ a ∈ S, {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v.ofLp a ≠ 0} := by
    ext v
    simp
  rw [hset]
  refine hU.inter (isOpen_biInter_finset fun a _ => isOpen_ne_fun ?_ continuous_const)
  unfold _root_.ReciprocityTheory.L2DbarEstimates.V
  fun_prop

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberEqGenericRankMulStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIntersectionNumber_eq_genericRank_mul : ∀ (κ : Type) [Field κ] (Z : Scheme.{0}) [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ (X := Z)) → ∀ (ι : Type) [Fintype ι], topologicalKrullDim Z ≤ (Fintype.card ι : ℕ) → ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G] (P : ι → LB Z), (∀ i, (P i).IsLB) → interNum κ G P = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) P := by
  first | exact @GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver | exact GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver | (intros; apply GlobalTheory.VB.interNum_eq_genRank_mul_of_isProjOver <;> assumption)
end

