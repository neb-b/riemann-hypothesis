module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolySubComm
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0927
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0204
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalFrameReadingEqConjugateDatumTheta
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixAdjoinTensorUnramifiedToMatrixInjectiveStatement
section
open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixAdjoinTensorUnramifiedToMatrix_injective : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ) (γ : Matrix (Fin n) (Fin n) K), 0 < r → Function.Injective (GlobalTheory.PolyTensor.phi p K n γ r) := by
  first | (exact @GlobalTheory.PolyTensor.phi_injective) | (exact GlobalTheory.PolyTensor.phi_injective) | (intros; apply GlobalTheory.PolyTensor.phi_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGroupOfCongruent
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrincCore


set_option maxHeartbeats 1000000 in
theorem mem_group_of_congruent : ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k (γ : GL (Fin D.R.r) D.host.E), ReciprocityTheory.ChartRestriction.G.FD.IsUStab ((T.U j σ).X k).Gm ((T.U j σ).X k).Λ γ → (∀ v ∈ ((T.U j σ).X k).Λ, ∃ u ∈ ((T.U j σ).X k).Λ, Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) v = v + T.Q.l.M • u) → γ ∈ ((T.U j σ).X k).Γ := by
  intro D T h j hj σ hσ k γ hγ hc0
  have hc : ∀ x ∈ ((T.U j σ).X k).Λ, ∃ y ∈ ((T.U j σ).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (T.Q.l.M : D.host.E) • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := hc0 x hx
    exact ⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
  obtain ⟨hgood, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hr : 0 < D.R.r := (hnum j hj).2.1
  have hM : 3 ≤ T.Q.l.M := le_trans (hgood 2 Nat.prime_two) (Nat.div_le_self _ _)
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (h.unf j hj σ hσ) hA hr k γ hγ hc
  obtain ⟨th, hrk, hth, hD⟩ := h.dictU j hj σ hσ
  have hK := h.levelK j hj σ hσ
  rw [← h.pins.2.1.1] at hK
  have h1 := root_eq_one (T.V j σ) hrk hr (T.U j σ).X (T.dict j σ) (T.mu j σ) (T.Kf j σ) th hth hD
    (h.muUnit j hj σ hσ) _ hM hK k γ γ' hγ' hc u n hn hu he
  rw [h1, one_smul] at he
  exact Units.ext he ▸ hγ'

end GlobalTheory.PrincCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubringOfPthPowerTwistedMonomialMem
section
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem LogDR.round_coeff_mem : ∀ (K : Type) [Field K] (p : ℕ) (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (I J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ) (g : K), 0 < p → AlgChart A x → (∀ j, r j < p) → g ^ p * ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) / ∏ j ∈ I \ J, (x j : K) ∈ A → g * t / ∏ j ∈ I \ J, (x j : K) ∈ A := by
  intro K _ p A n x I J t r g hp hA hr h
  have hP0 : (∏ j ∈ I \ J, (x j : K)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (x j).ne_zero)
  have hQ0 : (∏ j ∈ J, (x j : K)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (x j).ne_zero)
  have hcast : ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) = (t : K) ^ p * ∏ j ∈ J, (x j : K) ^ (r j) := by
    push_cast; rfl
  rw [hcast] at h
  have hpow : ∀ j ∈ J, (x j : K) ^ p = (x j : K) ^ (r j) * (x j : K) * (x j : K) ^ (p - 1 - r j) := by
    intro j _
    rw [← pow_succ, ← pow_add]
    congr 1
    have := hr j
    omega
  have hprod : (∏ j ∈ J, (x j : K)) ^ p = (∏ j ∈ J, (x j : K) ^ (r j)) * (∏ j ∈ J, (x j : K)) *
      ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hpow
  have hS : ∏ j ∈ J ∪ I \ J, (x j : K) = (∏ j ∈ J, (x j : K)) * ∏ j ∈ I \ J, (x j : K) :=
    Finset.prod_union Finset.disjoint_sdiff
  have hB : ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) ∈ A :=
    Subring.prod_mem _ (fun j _ => Subring.pow_mem _ (hA.mem j) _)
  have key : (g * t * ∏ j ∈ J, (x j : K)) ^ p / ∏ j ∈ J ∪ I \ J, (x j : K) =
      (g ^ p * ((t : K) ^ p * ∏ j ∈ J, (x j : K) ^ (r j)) / ∏ j ∈ I \ J, (x j : K)) *
        ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) := by
    rw [hS, mul_pow, mul_pow, hprod]
    field_simp
  have h2 := hA.root (J ∪ I \ J) _ p hp (key ▸ A.mul_mem h hB)
  have e : (g * t * ∏ j ∈ J, (x j : K)) / ∏ j ∈ J ∪ I \ J, (x j : K) = g * t / ∏ j ∈ I \ J, (x j : K) := by
    rw [hS]
    field_simp
  rwa [e] at h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolySeparableOfNoSqZeroPolynomialImageStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minpoly_separable_of_no_sq_zero_polynomial_image : ∀ (F C : Type) [Field F] [Ring C] [IsSimpleRing C] [Algebra F C] [FiniteDimensional F C] (n : ℕ) (σ : F →+* ℂ) (ψ : C →+* Matrix (Fin n) (Fin n) ℂ), 0 < n → (∀ x : F, ψ (algebraMap F C x) = Matrix.scalar (Fin n) (σ x)) → ∀ c : C, (∀ P : Polynomial ℂ, Polynomial.aeval (ψ c) P * Polynomial.aeval (ψ c) P = 0 → Polynomial.aeval (ψ c) P = 0) → (minpoly F c).Separable := by
  first | (exact @GlobalTheory.LKCx.minpoly_separable_of_sq_zero_free) | (exact GlobalTheory.LKCx.minpoly_separable_of_sq_zero_free) | (intros; apply GlobalTheory.LKCx.minpoly_separable_of_sq_zero_free  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCellFiniteUnionLocalDoubleCosetsStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_cell_finite_union_local_double_cosets : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (N : ℕ) (z : Fin N → ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, IsCompact (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ IsOpen (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) ∧ (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ i j : Fin N, (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z j w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → i = j) ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), (p ∈ GlobalTheory.JSW.MirPatch.cell K q ↔ ∃ i : Fin N, ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) := by
  first | (exact @GlobalTheory.JSW.MirPatch.cell_decomp) | (exact GlobalTheory.JSW.MirPatch.cell_decomp) | (intros; apply GlobalTheory.JSW.MirPatch.cell_decomp  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MkEqIffRelAndOutRel
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem GlobalTheory.LKMid.Pair.mk_eq_iff_rel_and_out_rel :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G),
      (Quot.mk Pair.Rel P = Quot.mk Pair.Rel Q ↔ P.Rel Q) ∧
        (Quot.out (Quot.mk Pair.Rel P : Cls G)).Rel P := by
  intro p _ G P Q
  have e : Equivalence (Pair.Rel (G := G)) := GlobalTheory.T.kottwitzPairScalarIsomorphic_equivalence p G
  have key : ∀ A B : Pair G, (Quot.mk Pair.Rel A = Quot.mk Pair.Rel B ↔ A.Rel B) := by
    intro A B
    rw [Quot.eq, e.eqvGen_iff]
  refine ⟨key P Q, ?_⟩
  exact (key _ _).1 (Quot.out_eq _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemLatGHat
section
set_option autoImplicit false

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelUnique

theorem mem_map_prod {O S : Type} [CommRing O] [IsDedekindDomain O] [CommRing S] (f : O →+* S)
    (T : Finset (HeightOneSpectrum O)) {s : S} (h : ∀ P ∈ T, s ∈ P.asIdeal.map f) :
    s ∈ (∏ P ∈ T, P.asIdeal).map f := by
  have e : (∏ P ∈ T, P.asIdeal).map f = ∏ P ∈ T, P.asIdeal.map f := map_prod (Ideal.mapHom f) _ _
  rw [e, Ideal.prod_eq_iInf_of_pairwise_isCoprime (J := fun P : HeightOneSpectrum O => P.asIdeal.map f) fun P _ Q _ hne =>
    (HeightOneSpectrum.isCoprime_of_ne P Q hne).map (Ideal.mapHom f)]
  exact Ideal.mem_iInf.2 fun P => Ideal.mem_iInf.2 fun hP => h P hP

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem sub_mem_idS {P : Pl E} {s t : Formalism.L2.Herm.intAf F E} (h : resS F P s = resS F P t) : s - t ∈ idS F P.asIdeal :=
  Ideal.Quotient.eq.1 ((RingEquiv.ofBijective (cmpS F P.asIdeal) (cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm.injective h)

theorem exists_matrix (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)}) {y y' : GL (Fin n) (Formalism.L2.Herm.intAf F E)}
    (h : ∀ P ∈ T, Formalism.UG.bc (resS F P) y = Formalism.UG.bc (resS F P) y') {b : 𝓞 E} (hb : b ∈ J) :
    ∃ s : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E), oToS F E b • (y.1 - y'.1) = M • s := by
  have key : ∀ i j, ∃ c, oToS F E b * (y.1 i j - y'.1 i j) = M • c := by
    intro i j
    have h1 : y.1 i j - y'.1 i j ∈ (∏ P ∈ T, P.asIdeal).map (oToS F E) :=
      mem_map_prod _ T fun P hP => sub_mem_idS (congrArg (fun g : GL (Fin n) (kP P) => g.1 i j) (h P hP))
    have h2 := Ideal.mul_mem_mul h1 (Ideal.mem_map_of_mem (oToS F E) hb)
    rw [← Ideal.map_mul, hJ, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton'] at h2
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, by rw [mul_comm, ← hc, nsmul_eq_mul, mul_comm]⟩
  choose c hc using key
  exact ⟨Matrix.of c, Matrix.ext fun i j => hc i j⟩

end Res

theorem conj_mulVec_mem {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) (s : Matrix (Fin n) (Fin n) S)
    (z : Fin n → R) (hz : ∀ j, ((β⁻¹).1 *ᵥ z) j ∈ S) (i : Fin n) :
    ((β⁻¹).1 *ᵥ ((β.1 * s.map S.subtype * (β⁻¹).1) *ᵥ z)) i ∈ S := by
  rw [Matrix.mulVec_mulVec, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, ← Matrix.mulVec_mulVec]
  generalize (β⁻¹).1 *ᵥ z = w at hz
  exact Subring.sum_mem S (t := Finset.univ) (f := fun j => (s i j : R) * w j) fun j _ => mul_mem (s i j).2 (hz j)

theorem conj_smul_sub {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) {y y' : GL (Fin n) S}
    {s : Matrix (Fin n) (Fin n) S} {b : S} {M : ℕ} (h : b • (y.1 - y'.1) = M • s) :
    (b : R) • ((β * Formalism.UG.bc S.subtype y * β⁻¹).1 - (β * Formalism.UG.bc S.subtype y' * β⁻¹).1) =
      M • (β.1 * s.map S.subtype * (β⁻¹).1) := by
  have e : (b : R) • ((Formalism.UG.bc S.subtype y).1 - (Formalism.UG.bc S.subtype y').1) = M • s.map S.subtype := by
    ext i j
    have := congrArg (fun m : Matrix (Fin n) (Fin n) S => S.subtype (m i j)) h
    simp only [Matrix.smul_apply, map_nsmul, smul_eq_mul, map_mul, Matrix.sub_apply, map_sub] at this
    exact this
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, ← sub_mul, ← mul_sub, ← smul_mul_assoc, ← mul_smul_comm, e,
    mul_smul_comm, smul_mul_assoc]

theorem exists_matrix_hat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ)
    (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ} (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)})
    {x x' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hx : x ∈ St β) (hx' : x' ∈ St β)
    (h : ∀ P ∈ T, redFn β P x = redFn β P x') {b : 𝓞 E} (hb : b ∈ J)
    {K K' : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hK : ∀ i j, x.1 i j = Algebra.TensorProduct.comm F _ E (K i j))
    (hK' : ∀ i j, x'.1 i j = Algebra.TensorProduct.comm F _ E (K' i j)) :
    ∃ N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E),
      (∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), N *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) ∧
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) • (K - K') = M • N := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hx'
  simp only [redFn_frGL] at h
  obtain ⟨s, hs⟩ := exists_matrix T hJ h hb
  have e := conj_smul_sub _ β hs
  have hN := fun z hz => (hfr _).2 (conj_mulVec_mem _ β s z ((hfr z).1 hz))
  generalize β.1 * s.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 = N at e hN
  refine ⟨N.map (Algebra.TensorProduct.comm F _ E).symm, fun z hz => ?_, Matrix.ext fun i j => ?_⟩
  · have h4 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ (hN _ (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz))
    convert h4 using 1
    ext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  · apply (Algebra.TensorProduct.comm F _ E).injective
    rw [Matrix.smul_apply, Matrix.smul_apply, map_nsmul, Matrix.map_apply, AlgEquiv.apply_symm_apply, smul_eq_mul, map_mul,
      Matrix.sub_apply, map_sub, ← hK, ← hK']
    exact congrFun (congrFun e i) j

variable {D : D7}

theorem mulVec_mem_latGHat {V : HSp D} (N : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))
    (h : ∀ z ∈ latHat V, N *ᵥ z ∈ latHat V) : ∀ z ∈ latGHat V 1, N *ᵥ z ∈ latGHat V 1 := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, _, ⟨z, hz, rfl⟩, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a, ha, _, ⟨_, h z hz, rfl⟩, ?_⟩
    rw [GlobalTheory.Member.LatMove.fin_one, GlobalTheory.Member.LatMove.fin_one]
    exact Matrix.mulVec_smul N ((1 : Af D.host.F) ⊗ₜ[D.host.F] a) z
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem exists_cong {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (T : Finset (Pl D.host.E)) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 D.host.E)}) {k k' : GA D V}
    (hk : Lev.finE V k ∈ St β) (hk' : Lev.finE V k' ∈ St β)
    (h : ∀ P ∈ T, redFn β P (Lev.finE V k) = redFn β P (Lev.finE V k')) {b : 𝓞 D.host.E} (hb : b ∈ J) :
    ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • ((finHom V k).1 *ᵥ z - (finHom V k').1 *ᵥ z) = M • w := by
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨N, hN, e⟩ := exists_matrix_hat hfr T hJ hk hk' h hb (K := (finHom V k).1) (K' := (finHom V k').1)
    (fun _ _ => rfl) (fun _ _ => rfl)
  rw [← hl] at hN
  intro z hz
  refine ⟨_, mulVec_mem_latGHat _ hN z hz, ?_⟩
  rw [← Matrix.sub_mulVec, ← Matrix.smul_mulVec, e, Matrix.smul_mulVec]

theorem redFn_eq_of_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (hr : V.rank = L.r)
    {g : G0 L.Pg L.r} {k k' : GA D V} (hk : Lev.IsLevelLift V β L g k) (hk' : Lev.IsLevelLift V β L g k') :
    ∀ P ∈ L.Pg, redFn β P (Lev.finE V k) = redFn β P (Lev.finE V k') := by
  intro P hP
  have e : upperLeftBlock L.hr (redFn β P (Lev.finE V k)) = upperLeftBlock L.hr (redFn β P (Lev.finE V k')) :=
    congrFun (hk.2.2.trans hk'.2.2.symm) ⟨P, hP⟩
  have e' := congrArg Units.val e
  rw [upper_block_val_submatrix _ (blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP)),
    upper_block_val_submatrix _ (blockTri_blkOf_le _ _ (parLev_g hk'.2.1 hP))] at e'
  exact Units.ext (Matrix.ext fun i j => congrFun (congrFun e' (Fin.cast hr i)) (Fin.cast hr j))

theorem sub_eq_nsmul {R : Type} [CommRing R] {n : ℕ} {K K' : Matrix (Fin n) (Fin n) R} {t : R} {x x' z w₁ w₂ w₃ : Fin n → R}
    {M : ℕ} (e₁ : x - K *ᵥ (t • z) = M • w₁) (e₂ : x' - K' *ᵥ (t • z) = M • w₂) (e₃ : t • (K *ᵥ z - K' *ᵥ z) = M • w₃) :
    x - x' = M • (w₁ - w₂ + w₃) := by
  rw [smul_add, smul_sub M, ← e₁, ← e₂, ← e₃, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_sub]
  abel

theorem sub_mem_of_approx {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {I J : Ideal (𝓞 D.host.E)} {M : ℕ} (hM : 0 < M)
    (hI : (M : 𝓞 D.host.E) ∈ I) (hIJ : I ⊔ J = ⊤)
    {K K' : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)}
    (h : ∀ b ∈ J, ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((b : 𝓞 D.host.E) : D.host.E)) • (K *ᵥ z - K' *ᵥ z) = M • w)
    {f f' : La →ₗ[𝓞 D.host.E] La}
    (hf : ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (f a)) - K *ᵥ finVec V (ι a) = M • w)
    (hf' : ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (f' a)) - K' *ᵥ finVec V (ι a) = M • w) (a : La) :
    f a - f' a ∈ I • (⊤ : Submodule (𝓞 D.host.E) La) := by
  have hm : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  have h5 := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1
  obtain ⟨u, hu, b, hb, hub⟩ := Submodule.mem_sup.1 (hIJ ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ I ⊔ J)
  rw [← one_smul (𝓞 D.host.E) (f a - f' a), ← hub, add_smul]
  refine add_mem (Submodule.smul_mem_smul hu Submodule.mem_top) ?_
  obtain ⟨w₁, hw₁, e₁⟩ := hf (b • a) (Submodule.smul_mem_smul hb Submodule.mem_top)
  obtain ⟨w₂, hw₂, e₂⟩ := hf' (b • a) (Submodule.smul_mem_smul hb Submodule.mem_top)
  obtain ⟨w₃, hw₃, e₃⟩ := h b hb _ ((GlobalTheory.Member.LatMove.mem_lat_iff V 1 _).1 (hm a))
  have e₀ : finVec V (ι (b • a)) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • finVec V (ι a) := by
    rw [map_smul]; exact GlobalTheory.AdLat.Tower.fv_smul b (ι a)
  have e₄ : finVec V (ι (b • (f a - f' a))) = finVec V (ι (f (b • a))) - finVec V (ι (f' (b • a))) := by
    rw [smul_sub, ← map_smul f, ← map_smul f', map_sub]; exact GlobalTheory.AdLat.Tower.fv_sub _ _
  have e₅ : finVec V (ι (b • (f a - f' a))) = M • (w₁ - w₂ + w₃) := by
    rw [e₀] at e₁ e₂
    exact e₄.trans (sub_eq_nsmul e₁ e₂ e₃)
  obtain ⟨⟨v, hv⟩, ev⟩ := GlobalTheory.AdLat.Tower.exists_div (F := D.host.F) (M := latG V 1)
    (fun v => h5 ▸ (GlobalTheory.Member.LatMove.mem_lat_iff V 1 v).symm) hM ⟨_, hm (b • (f a - f' a))⟩
    (h5 ▸ add_mem (sub_mem hw₁ hw₂) hw₃) e₅
  obtain ⟨c, rfl⟩ : v ∈ LinearMap.range ι := hι.2 ▸ hv
  have e₆ : b • (f a - f' a) = (M : 𝓞 D.host.E) • c := by
    apply hι.1
    rw [Nat.cast_smul_eq_nsmul, map_nsmul]
    exact congrArg Subtype.val ev
  rw [e₆]
  exact Submodule.smul_mem_smul hI Submodule.mem_top

theorem levUnique (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (hL : R.toLevCh.Is A.μ0) (hT : LawsJ T)
    (hM : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal) (i : Fin D.R.m) : GlobalTheory.OneMapAllCompare.LevUnique T R i := by
  intro lev lev' h h' g a
  obtain ⟨k, hk, hf⟩ := h g
  obtain ⟨k', hk', hf'⟩ := h' g
  have hp : T.Q.l.Mb * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)} := T.Q.l.prod
  have hp' : (∏ PP ∈ R.Pg, PP.asIdeal) * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)} := by rw [← hM]; exact hp
  have hI : ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ T.Q.l.Mb :=
    (hp.ge.trans (Ideal.mul_le_inf.trans inf_le_left)) (Ideal.mem_span_singleton_self _)
  have hc : T.Q.l.Mb ⊔ Mfr T.Q.l = ⊤ := T.Q.l.coprime
  have hr := redFn_eq_of_lift (L := R.datWp i R.triv) (rank_Wc i) hk hk'
  have hcong := fun b hb => exists_cong (b := b) (hL.βW i) R.Pg hp' (parLev_St hk.2.1) (parLev_St hk'.2.1) hr hb
  exact sub_mem_of_approx (GlobalTheory.LevelAction.latEmb_iotaW T hT i) (lt_of_lt_of_le (by norm_num) T.Q.l.three_le) hI hc hcong hf hf' a

end GlobalTheory.LevelUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFiniteTypeIndexOfRowsPos
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.Div

theorem nonempty_ix_of_pos : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m s : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m) (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub A3.fam3.amb3), A3.fam3.Ok3 s → Zs.InBlock → (A3.side3 P ψ Zs).Pos → Nonempty A3.fam3.base3.Ix := by
  intro K _ _ _ G _ _ Pl0 I0 Ty T m s A3 P ψ Zs hOk hin hpos
  by_contra hne
  have hfalse : ∀ x, ¬ A3.fam3.IsType3 (A3.fam3.RI A3.fam3.F.μ0) id x := by
    rintro x ⟨p, hp, -⟩
    exact hne ⟨⟨p, hp⟩⟩
  have hsame := A3.fam3.sameTypes_base3 hOk P ψ hin
  have hbot : Formalism.L2.Col.eigSum (A3.fam3.RI A3.fam3.F.μ0).opAll
      (A3.fam3.IsType3 (A3.fam3.RI A3.fam3.F.μ0) id) = ⊥ := by
    unfold Formalism.L2.Col.eigSum
    simp [hfalse]
  rw [hbot, BlockDat.good_part_coordinates_bot, le_bot_iff] at hsame
  unfold FamIn3.side3 DefFam3.side3 DefSide.Pos at hpos
  simp only [BlockDat.dZ, subDim] at hpos
  rw [hsame] at hpos
  simp at hpos

end GlobalTheory.Div
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddSmulMemUnitary
section
open Matrix

namespace GlobalTheory.UnitaryPerturbation

theorem one_add_smul_mem_unitary {n : ℕ} {Hm : GlobalTheory.HolDict.Mt n} (hH : Matrix.IsHermitian Hm) (v : Fin n → ℂ) (z : ℂ)
    (hz : star z + z + star z * z * star v ⬝ᵥ Matrix.mulVec Hm v = (0 : ℂ)) :
    (1 : Matrix (Fin n) (Fin n) ℂ) + z • (Matrix.vecMulVec v (star v) * Hm) ∈ Formalism.QuantumDeterminants.UH Hm := by
  show (1 + z • (Matrix.vecMulVec v (star v) * Hm))ᴴ * Hm * (1 + z • (Matrix.vecMulVec v (star v) * Hm)) = Hm
  have hHc : Hmᴴ = Hm := hH
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin n) (Fin n) ℂ, M = Matrix.vecMulVec v (star v) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = star v ⬝ᵥ Matrix.mulVec Hm v := ⟨_, rfl⟩
  rw [← hcdef] at hz
  have hMc : Mᴴ = M := by rw [hMdef, Matrix.conjTranspose_vecMulVec, star_star]
  have hMHM : M * Hm * M = c • M := by
    ext i j
    simp only [hMdef, hcdef, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
      dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have key : Hm * (M * (Hm * (M * Hm))) = c • (Hm * (M * Hm)) := by
    have h1 : M * (Hm * (M * Hm)) = c • (M * Hm) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMHM, Matrix.smul_mul]
    rw [h1, Matrix.mul_smul]
  rw [← hMdef, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, hMc, hHc]
  have expand : (1 + star z • (Hm * M)) * Hm * (1 + z • (M * Hm)) =
      Hm + (star z + z + star z * z * c) • (Hm * (M * Hm)) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc]
    rw [key]
    module
  rw [expand, hz, zero_smul, add_zero]

end GlobalTheory.UnitaryPerturbation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderLatticeBasisIntegrality
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.order_lattice_basis_integrality : ∀ {A B : Type} [Ring A] [CommRing B] (j : B →+* A) (Λ : Set A) (R : Set B) (r : ℕ) (e : Fin r → A),
    (0 : A) ∈ Λ → (1 : A) ∈ Λ → (∀ x ∈ Λ, ∀ y ∈ Λ, x + y ∈ Λ) → (∀ x ∈ Λ, -x ∈ Λ) →
    (∀ x ∈ Λ, ∀ y ∈ Λ, x * y ∈ Λ) →
    (0 : B) ∈ R → (1 : B) ∈ R → (∀ x ∈ R, ∀ y ∈ R, x + y ∈ R) → (∀ x ∈ R, -x ∈ R) →
    (∀ x ∈ R, ∀ y ∈ R, x * y ∈ R) →
    (∀ a : A, ∃! β : Fin r → B, a = ∑ i, j (β i) * e i) →
    (∀ β : Fin r → B, (∑ i, j (β i) * e i ∈ Λ) ↔ ∀ i, β i ∈ R) →
    (∀ i i' : Fin r, ∃ (N : ℕ) (ρ : Fin N → B) (μ : Fin N → A), (∀ k, ρ k ∈ R) ∧ (∀ k, μ k ∈ Λ) ∧
      ∀ β : Fin r → B, ∑ k, j (ρ k) * (∑ i'', j (β i'') * e i'') * μ k = j (β i') * e i) →
    (∀ a : A, ∃ D : ℤ, D ≠ 0 ∧ (D : A) * a ∈ Λ) →
    (∀ I : Set B, (0 : B) ∈ I → (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ ∈ R, ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x ∈ R, (D : B) * x ∈ I) ∧ ∀ x ∈ I, (D : B) * x ∈ R) →
      ∃ m : Bˣ, ∀ x, x ∈ I ↔ ∃ ρ ∈ R, x = ↑m * ρ) →
    ∀ X : Aˣ, (∀ ρ ∈ R, (X : A) * j ρ * ↑X⁻¹ ∈ Λ) → ∃ m : Bˣ, (X : A) * j ↑m ∈ Λ ∧ j ↑m⁻¹ * ↑X⁻¹ ∈ Λ := by
  first | (exact @GlobalTheory.AbsLattice.exists_unit_of_conj_stable) | (exact GlobalTheory.AbsLattice.exists_unit_of_conj_stable) | (intros; apply GlobalTheory.AbsLattice.exists_unit_of_conj_stable  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalFrameReadingEqConjugateDatumThetaStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (g : ℕ) (X : Data D.host.E W.rank) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin W.rank) (hstd : IsStdChar D ψ (-1)) (hinf : IsInfFam θ) (he : Even V.rank), V.gram = 1 → IsMod W rfl X → IsSympl X bas → ∃ (X' : Data D.host.E W.rank) (m : GlobalTheory.Ker.Match V W X') (hq' : X'.p0 + X.p0 = W.rank) (hq : X.p0 + X'.p0 = W.rank) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g ≃ X'.Ψ × Fin W.rank) (hs : IsSympl X' bas'), X'.Λ = X.Λ ∧ (∀ a, (bas' a : Fin W.rank → D.host.E) = bas a) ∧ (∀ u v, EF X' u v = EF X u v) ∧ (∀ (y : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (φ : TF V.rank g), heisG X' bas' y φ = heisG X bas y φ) ∧ (∀ j (a : Fin W.rank) (k : Fin X'.p0 ⊕ Fin X.p0), (idx j).2 = rowIdx hq k → ((idx' j).2 : ℕ) = Sum.elim (fun i : Fin X'.p0 => (i : ℕ)) (fun i : Fin X.p0 => X'.p0 + (i : ℕ)) k) ∧ (∀ j, (idx' j).1.1 = ComplexEmbedding.conjugate (idx j).1.1) ∧ ∀ x : Frame X.Ψ W.rank, IsONFr X x → (∃ B, IsBasOf W rfl X hq x B) ∧ ∀ B, IsBasOf W rfl X hq x B → let C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hstd, θ, hinf, X', m, g, X.p0, hq', bas', idx', hs, he⟩; C.IsB B ∧ IsInvOf W rfl X x (C.sB B) ∧ (∀ s, IsInvOf W rfl X x s → s = C.sB B) ∧ (∀ w, C.zOf (C.xB B) w = zOf θ V W rfl X idx x w) ∧ (∀ v, pv X' idx' (C.xB B) v = pv X idx x v) ∧ (∀ z z', hx X' bas' idx' (C.xB B) z z' = hx X bas idx x z z') ∧ (∀ φ : TF V.rank g, thA X' bas' idx' φ (C.xB B) = thA X bas idx φ x) ∧ (∀ u : GA D W, IsONFr X (frMove θ W rfl X u x) ∧ IsBasOf W rfl X hq (frMove θ W rfl X u x) (C.mvB u B)) ∧ ∀ (f : WO V W → ℂ) (φ : TF V.rank g), GlobalTheory.SW.IsSB φ → ((IsThetaFunO ψ V W f ∧ Reads θ V W rfl X bas idx f φ x) ↔ f = C.Th (C.xB B) φ) := by
  first | exact @GlobalTheory.AdTh.reads_iff_eq_th | exact GlobalTheory.AdTh.reads_iff_eq_th | (intros; apply GlobalTheory.AdTh.reads_iff_eq_th <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPrimeDegreeOneStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_prime_degree_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (W : HeightOneSpectrum (𝓞 E)), SplitsFully E (W.under (𝓞 F)) → ∃ p : ℕ, p.Prime ∧ Ideal.absNorm W.asIdeal = p ∧ (p : 𝓞 E) ∉ W.asIdeal ^ 2 := by
  first | exact @GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully | exact GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully | (intros; apply GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully <;> assumption)
end

