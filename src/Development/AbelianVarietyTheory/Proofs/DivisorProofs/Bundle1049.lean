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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValResultantCharpolyShiftedUnitAdjoinRoot
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.UnitLemma.ShiftRes

def shiftPoly {F : Type} [Field F] (t s : F) (p : F[X]) : F[X] :=
  C (t ^ p.natDegree)⁻¹ * p.comp (C t * X + C s)

theorem natDegree_lin {F : Type} [Field F] (t s : F) (ht : t ≠ 0) : (C t * X + C s).natDegree = 1 := by
  rw [natDegree_add_C, natDegree_C_mul_X t ht]

theorem natDegree_shiftPoly {F : Type} [Field F] (t s : F) (ht : t ≠ 0) (p : F[X]) :
    (shiftPoly t s p).natDegree = p.natDegree := by
  unfold shiftPoly
  rw [natDegree_C_mul (inv_ne_zero (pow_ne_zero _ ht)), natDegree_comp, natDegree_lin t s ht, mul_one]

theorem monic_shiftPoly {F : Type} [Field F] (t s : F) (ht : t ≠ 0) (p : F[X]) (hp : p.Monic) :
    (shiftPoly t s p).Monic := by
  unfold shiftPoly Monic
  rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp (by rw [natDegree_lin t s ht]; exact one_ne_zero),
    hp.leadingCoeff, one_mul]
  have : (C t * X + C s).leadingCoeff = t := by
    rw [leadingCoeff, natDegree_lin t s ht]; simp
  rw [this, inv_mul_cancel₀ (pow_ne_zero _ ht)]

theorem map_shiftPoly {F L : Type} [Field F] [Field L] (φ : F →+* L) (t s : F) (p : F[X]) :
    (shiftPoly t s p).map φ = shiftPoly (φ t) (φ s) (p.map φ) := by
  unfold shiftPoly
  rw [Polynomial.map_mul, map_C, Polynomial.map_comp, natDegree_map]
  simp

theorem shiftPoly_mul {F : Type} [Field F] (t s : F) (p q : F[X]) (hp : p.Monic) (hq : q.Monic) :
    shiftPoly t s (p * q) = shiftPoly t s p * shiftPoly t s q := by
  unfold shiftPoly
  rw [hp.natDegree_mul hq, mul_comp, pow_add, mul_inv, C_mul]
  ring

theorem shiftPoly_eq_prod {L : Type} [Field L] [IsAlgClosed L] (t s : L) (ht : t ≠ 0) (p : L[X]) (hp : p.Monic) :
    shiftPoly t s p = ((p.roots.map fun α => (α - s) / t).map fun a => X - C a).prod := by
  have hsp := IsAlgClosed.splits p
  have hcard : Multiset.card p.roots = p.natDegree := hsp.natDegree_eq_card_roots.symm
  unfold shiftPoly
  conv_lhs => arg 2; rw [hsp.eq_prod_roots_of_monic hp]
  rw [multiset_prod_comp, Multiset.map_map, Multiset.map_map]
  have key : ∀ α : L, (X - C α).comp (C t * X + C s) = C t * (X - C ((α - s) / t)) := by
    intro α
    rw [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, mul_div_cancel₀ _ ht, C_sub]
    ring
  simp only [Function.comp_def, key]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard, ← C_pow, ← mul_assoc, ← C_mul,
    inv_mul_cancel₀ (pow_ne_zero _ ht), C_1, one_mul]

theorem resultant_shiftPoly_alg {L : Type} [Field L] [IsAlgClosed L] (t s : L) (ht : t ≠ 0) (p q : L[X])
    (hp : p.Monic) (hq : q.Monic) :
    resultant (shiftPoly t s p) (shiftPoly t s q) = (t ^ (p.natDegree * q.natDegree))⁻¹ * resultant p q := by
  have hcp : Multiset.card p.roots = p.natDegree := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hcq : Multiset.card q.roots = q.natDegree := (IsAlgClosed.splits q).natDegree_eq_card_roots.symm
  rw [resultant_eq_prod_roots_sub _ _ (monic_shiftPoly t s ht p hp) (monic_shiftPoly t s ht q hq)
    (IsAlgClosed.splits _) (IsAlgClosed.splits _), resultant_eq_prod_roots_sub p q hp hq (IsAlgClosed.splits p)
    (IsAlgClosed.splits q), shiftPoly_eq_prod t s ht p hp, shiftPoly_eq_prod t s ht q hq,
    roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C, Multiset.prod_map_product_eq_prod_prod,
    Multiset.prod_map_product_eq_prod_prod]
  simp only [Multiset.map_map, Function.comp_def]
  have key : ∀ α β : L, (α - s) / t - (β - s) / t = t⁻¹ * (α - β) := by
    intro α β; field_simp; ring
  simp only [key]
  simp only [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcq]
  rw [hcp, ← pow_mul, inv_pow, mul_comm q.natDegree p.natDegree]

theorem resultant_shiftPoly {F : Type} [Field F] (t s : F) (ht : t ≠ 0) (p q : F[X]) (hp : p.Monic) (hq : q.Monic) :
    resultant (shiftPoly t s p) (shiftPoly t s q) = (t ^ (p.natDegree * q.natDegree))⁻¹ * resultant p q := by
  let φ := algebraMap F (AlgebraicClosure F)
  apply φ.injective
  have e1 : φ (resultant (shiftPoly t s p) (shiftPoly t s q)) =
      resultant ((shiftPoly t s p).map φ) ((shiftPoly t s q).map φ) := by
    rw [resultant_map_map, natDegree_map, natDegree_map]
  have e2 : φ (resultant p q) = resultant (p.map φ) (q.map φ) := by
    rw [resultant_map_map, natDegree_map, natDegree_map]
  rw [e1, map_mul, e2, map_shiftPoly, map_shiftPoly,
    resultant_shiftPoly_alg _ _ ((_root_.map_ne_zero φ).2 ht) _ _ (hp.map φ) (hq.map φ), natDegree_map, natDegree_map,
    map_inv₀, map_pow]

theorem separable_shiftPoly {F : Type} [Field F] (t s : F) (ht : t ≠ 0) (p : F[X]) (hp : p.Separable) :
    (shiftPoly t s p).Separable := by
  have h1 := IsCoprime.map hp (Polynomial.compRingHom (C t * X + C s))
  rw [Polynomial.coe_compRingHom_apply, Polynomial.coe_compRingHom_apply] at h1
  have h2 : IsCoprime (p.comp (C t * X + C s)) (C t) :=
    ⟨0, C t⁻¹, by rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ ht, C_1]⟩
  have h3 : derivative (p.comp (C t * X + C s)) = (derivative p).comp (C t * X + C s) * C t := by
    rw [derivative_comp, derivative_add, derivative_C_mul_X, derivative_C, add_zero, mul_comm]
  have hc : (p.comp (C t * X + C s)).Separable := by
    show IsCoprime _ _
    rw [h3]
    exact h1.mul_right h2
  unfold shiftPoly
  have hu : IsUnit (C (t ^ p.natDegree)⁻¹ : F[X]) := isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero (pow_ne_zero _ ht)))
  show IsCoprime _ _
  rw [derivative_mul, derivative_C, zero_mul, zero_add]
  exact (isCoprime_mul_unit_left hu _ _).2 hc

theorem charpoly_eq_of_adjoin {F A : Type} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A] (x : A)
    (hx : Algebra.adjoin F ({x} : Set A) = ⊤) (p : F[X]) (hp : p.Monic) (hpx : aeval x p = 0)
    (hd : p.natDegree = Module.finrank F A) : (LinearMap.mulLeft F x).charpoly = p := by
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hmon := minpoly.monic hint
  have hCH : aeval x (LinearMap.mulLeft F x).charpoly = 0 := by
    have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft F x)
    have h2 := Polynomial.aeval_algHom_apply (Algebra.lmul F A) x (LinearMap.mulLeft F x).charpoly
    have h3 : (Algebra.lmul F A) (aeval x (LinearMap.mulLeft F x).charpoly) = 0 := by rw [← h2]; exact h
    simpa using congrArg (fun f => f 1) h3
  have hcd : (LinearMap.mulLeft F x).charpoly.natDegree = Module.finrank F A := LinearMap.charpoly_natDegree _
  have hle : Module.finrank F A ≤ (minpoly F x).natDegree := by
    let pb := AdjoinRoot.powerBasis' hmon
    haveI : Module.Finite F (AdjoinRoot (minpoly F x)) := pb.finite
    let f := AdjoinRoot.liftAlgHom (minpoly F x) (Algebra.ofId F A) x
      (by rw [← minpoly.aeval F x, aeval_def]; rfl)
    have hs : Function.Surjective f := by
      intro y
      have hy : y ∈ Algebra.adjoin F ({x} : Set A) := hx ▸ Algebra.mem_top
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
      obtain ⟨r, rfl⟩ := hy
      exact ⟨AdjoinRoot.mk _ r, by rw [AdjoinRoot.liftAlgHom_mk]; rfl⟩
    have h1 := LinearMap.finrank_range_le f.toLinearMap
    rw [LinearMap.range_eq_top.2 hs, finrank_top, pb.finrank, AdjoinRoot.powerBasis'_dim] at h1
    exact h1
  have h1 : p = minpoly F x :=
    eq_of_monic_of_dvd_of_natDegree_le hmon hp (minpoly.dvd F x hpx) (by omega)
  have h2 : (LinearMap.mulLeft F x).charpoly = minpoly F x :=
    eq_of_monic_of_dvd_of_natDegree_le hmon (LinearMap.charpoly_monic _) (minpoly.dvd F x hCH) (by omega)
  rw [h2, h1]

theorem val_inv_pow_mul {K : UQ} {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ) :
    val K.O ((x ^ n)⁻¹ * y) = val K.O y - n * val K.O x := by
  unfold val
  have h1 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E ((x ^ n)⁻¹) ≠ 0 := by simp [hx]
  have h2 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E y ≠ 0 := by simp [hy]
  rw [map_mul, WithZero.log_mul h1 h2, map_inv₀, map_pow, WithZero.log_inv, WithZero.log_pow, nsmul_eq_mul]
  ring

theorem val_resultant_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (k : ℕ) (t : K.O), t ≠ 0 → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (a b : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → Algebra.adjoin K.E {(1 + algebraMap K.O B₁.A t * B₁.g)} = ⊤ → aeval (1 + algebraMap K.O B₁.A t * B₁.g) (Q₁.map e.symm.toRingHom) = 0 → Module.finrank K.E B₁.A = Q₁.natDegree → Algebra.adjoin K.E {(1 + algebraMap K.O B₂.A t * B₂.g)} = ⊤ → aeval (1 + algebraMap K.O B₂.A t * B₂.g) (Q₂.map e.symm.toRingHom) = 0 → Module.finrank K.E B₂.A = Q₂.natDegree → (B₁.P * B₂.P).Separable ∧ GlobalTheory.UnitLemma.val K.O (resultant B₁.P B₂.P) = ordL (resultant Q₁ Q₂) - ((k * a * b : ℕ) : ℤ) := by
  intro E _ _ _ w K e hval k t ht hk a b Q₁ Q₂ B₁ B₂ hm₁ hm₂ ha hb hsep hadj₁ hQ₁ hf₁ hadj₂ hQ₂ hf₂
  set t' : K.E := algebraMap K.O K.E t with ht'def
  have ht' : t' ≠ 0 := by
    rw [ht'def]; exact (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ht
  have hP : ∀ (B : InvAlg K) (Q : (w.adicCompletion E)[X]), Q.Monic →
      Algebra.adjoin K.E {(1 + algebraMap K.O B.A t * B.g)} = ⊤ →
      aeval (1 + algebraMap K.O B.A t * B.g) (Q.map e.symm.toRingHom) = 0 →
      Module.finrank K.E B.A = Q.natDegree → B.P = shiftPoly t' 1 (Q.map e.symm.toRingHom) := by
    intro B Q hQm hadj hQ hfin
    have hd : (Q.map e.symm.toRingHom).natDegree = Q.natDegree := natDegree_map _
    have hu : aeval B.g (C t' * X + C 1) = 1 + algebraMap K.O B.A t * B.g := by
      rw [map_add (f := _), map_mul, aeval_C, aeval_X, aeval_C, map_one, ht'def, ← IsScalarTower.algebraMap_apply]
      ring
    unfold InvAlg.P
    apply charpoly_eq_of_adjoin
    · rw [eq_top_iff, ← hadj]
      apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff, ← hu]
      exact aeval_mem_adjoin_singleton _ _
    · exact monic_shiftPoly t' 1 ht' _ (hQm.map _)
    · unfold shiftPoly
      rw [map_mul, aeval_C, aeval_comp, hu, hQ, mul_zero]
    · rw [natDegree_shiftPoly t' 1 ht', hd, hfin]
  have e₁ := hP B₁ Q₁ hm₁ hadj₁ hQ₁ hf₁
  have e₂ := hP B₂ Q₂ hm₂ hadj₂ hQ₂ hf₂
  have hm₁' : (Q₁.map e.symm.toRingHom).Monic := hm₁.map _
  have hm₂' : (Q₂.map e.symm.toRingHom).Monic := hm₂.map _
  refine ⟨?_, ?_⟩
  · rw [e₁, e₂, ← shiftPoly_mul t' 1 _ _ hm₁' hm₂', ← Polynomial.map_mul]
    exact separable_shiftPoly t' 1 ht' _ hsep.map
  · rw [e₁, e₂, resultant_shiftPoly t' 1 ht' _ _ hm₁' hm₂']
    have hR : resultant (Q₁.map e.symm.toRingHom) (Q₂.map e.symm.toRingHom) = e.symm (resultant Q₁ Q₂) := by
      rw [resultant_map_map, natDegree_map, natDegree_map]; rfl
    have hR0 : resultant Q₁ Q₂ ≠ 0 := resultant_ne_zero _ _ hsep.isCoprime
    rw [hR, natDegree_map, natDegree_map, val_inv_pow_mul ht' ((_root_.map_ne_zero _).2 hR0), hval, RingEquiv.apply_symm_apply, hk, ha, hb]
    push_cast; ring

end GlobalTheory.UnitLemma.ShiftRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfEqSumHeis
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DatumFourierOnCmp

open GlobalTheory.DatumFourier


set_option maxHeartbeats 1600000 in
theorem vecOf_eq_sum_heis : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (χ : (AE D)ˣ →* Circle) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (Ω : GlobalTheory.OnCmp.DatFn D i) (ω : GlobalTheory.OnTies.WeilRep D i) (φv : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.OnCmp.IsWeilTw R i χ ω → Formalism.IndefR.Lev.IsTwistPlaces D.host.g Q → GlobalTheory.OnCmp.ReadsOnly (R.Pg ∪ Q) Ω → GlobalTheory.OnCmp.VecOf R i Q Ω φv → ∀ (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), GlobalTheory.OnCmp.PhiOf R i Q Ω ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (R.Pg ∪ Q) → φv = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (Matrix.of fun a b => e * incA D (((δ : ℤ) : D.host.E) * ι (cSep l₂ • levRep (q b)) a / (l₂.M : D.host.E))) (R.vacP i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hI
  obtain ⟨ε, hε⟩ := hI
  refine ⟨ε, fun χ Q Ω ω φv _ _ hRO hVec l φ hφ hP e he => ?_⟩
  obtain ⟨hvac, e₁, he₁, hθ⟩ := hVec
  obtain ⟨e₂, he₂, hφ⟩ := hφ
  obtain rfl := idemSum_unique (Vc D i) he₁ he
  obtain rfl := idemSum_unique (Vc D i) he₂ he
  have hβV := hR.lev.βV i
  have hβW := hR.lev.βW i
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβV
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβW
  have hstd : R.ΛV i = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβV, ← GlobalTheory.SplitReps.hLat_one, hV.2]
  have hlat := mem_latRat_iff hV.1 hstd hβW
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hM' : (l.M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hsurj : ∀ M ∈ GlobalTheory.LatVac.latRat (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)), ∃ x : Fin (Vc D i).rank → Dw.La, M = Matrix.of fun a b => ι (x b) a := by
    intro M hM
    choose x hx using fun b => hι.2.ge ((hlat M).1 hM b)
    exact ⟨x, Matrix.ext fun a b => (congrFun (hx b) a).symm⟩
  have hint : ∀ u ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True),
      IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u)) := fun u hu =>
    int_of_mem_latO (fun M hM => by
      obtain ⟨x, rfl⟩ := hsurj M hM
      exact (hφ x).1) hu
  have : Finite (LevQ Dw l) := GlobalTheory.LevelPairing.finite_LevQ
  have := Fintype.ofFinite (Fin (Vc D i).rank → LevQ Dw l)
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  simp only [smul_smul]
  refine thetaAt_eq_sum _ _ hθ (fun q a b => ?_) fun w => ?_
  · rw [GlobalTheory.LatVac.cA_cA, Matrix.of_apply, ← mul_assoc, GlobalTheory.PlaceVec.idemSum_mul_self he]
  by_cases hw : w ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True) ∧ IsHalf (cA D e) w
  swap
  · rw [halfInd, if_neg hw, zero_mul, if_neg]
    rintro ⟨h1, h2⟩
    have hN : ∀ PP ∈ R.Pg ∪ Q, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP h =>
      (hP PP (Finset.mem_union.1 hPP)).2 (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
    exact hw ⟨mem_latO_of_int hS hT hβV.choose_spec.1 hβW.choose_spec.1 he (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) hN h1 h2, h1⟩
  have hw' : cA D e • w = w := Matrix.ext hw.2
  obtain ⟨M, hM0, u, hu, hwM⟩ := approx_mod (Nat.pos_of_ne_zero hM) hw.1
  obtain ⟨x, rfl⟩ := hsurj M hM0
  have hfr : frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w =
      uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b)) +
        l.M • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u) := by
    rw [← hw', hwM, smul_add, GlobalTheory.PlaceVec.frMapAdj_add, frMapAdj_half, smul_comm]
    congr 1
    · exact one_smul _ _
    · exact (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add _ _ (R.βV i) (R.βW i))).map_nsmul _ _
  have hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) =
      redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b))) := fun PP hPP => by
    rw [hfr]
    have : Ideal.span {(l.M : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact GlobalTheory.PlaceVec.redM_add_nsmul PP ((hP PP hPP).1 (this (Ideal.subset_span rfl))) (hφ x).1 (hint u hu)
  rw [halfInd, if_pos hw, one_mul, if_pos ⟨hw.2, hw' ▸ hint w hw.1⟩,
    hRO _ (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b))))
      (fun PP h => hred PP (Finset.mem_union.1 h)), ← (hφ x).2, ← inversion l φ x]
  refine Finset.sum_congr rfl fun q _ => congrArg _ ?_
  have hY : (Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) =
      Matrix.of fun a b => (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) * ι (cSep l • levRep (q b)) a :=
    Matrix.ext fun a b => by simp only [Matrix.of_apply]; ring
  refine Eq.trans ?_ (char_eq (Y := Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E))
    hvac.1 hS hT (GlobalTheory.PlaceVec.idemSum_infPart he) hw.2 hu hwM ((hlat _).2 fun b => ?_)).symm
  · rw [hY, hRat_std hV.1 _ _ _ (by rw [star_div₀, star_intCast, star_natCast]), ← Complex.exp_int_mul]
    congr 1
    have h1 : ∀ c : ℚ, ∀ z : D.host.E, Algebra.trace ℚ D.host.E (D.host.xi0 * ((c : D.host.E) * z)) =
        c * Algebra.trace ℚ D.host.E (D.host.xi0 * z) := fun c z => by
      rw [mul_left_comm, ← Rat.smul_def, map_smul, smul_eq_mul]
    have h2 : ∀ y z, Dw.EF y z = -Dw.EF z y := fun y z => (LinearMap.IsAlt.neg Dw.alt z y).symm
    have h3 : ((pairL (l := l) x (fun b => levRep (q b)) : ℤ) : ℚ) = -(((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 *
        ∑ b, (Wc D i).hT ((Wc D i).frame.equivFun.symm (ι (cSep l • levRep (q b)))) ((Wc D i).frame.equivFun.symm (ι (x b))))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [pairL, Int.cast_sum, Finset.mul_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by rw [h2, Int.cast_neg, hε]
    have h4 := congrArg (fun z : ℚ => (z : ℂ)) h3
    rw [show (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) = ((((ε : ℤ) : ℚ) / (l.M : ℚ) : ℚ) : D.host.E) by push_cast; rfl, h1]
    push_cast at h4 ⊢
    rw [h4]
    ring
  · have h1 := hι.2.le (LinearMap.mem_range_self ι ((ε : ℤ) • cSep l • levRep (q b)))
    convert h1 using 1
    funext a
    rw [map_zsmul, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, mul_div_cancel₀ _ hM', Pi.smul_apply, zsmul_eq_mul]

end GlobalTheory.DatumFourierOnCmp

end
end

