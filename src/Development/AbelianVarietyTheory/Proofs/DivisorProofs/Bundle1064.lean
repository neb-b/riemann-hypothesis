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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0558
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFormOfUnitaryGeneratorInvariantForm
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.BetaEx

variable {K : GlobalTheory.UnitLemma.UQ} {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ}

def sv (G : Matrix (Fin m) (Fin m) K.E) (x y : Fin m → K.E) : K.E :=
  x ⬝ᵥ (G *ᵥ fun j => K.c (y j))

def sf (b : Module.Basis (Fin m) K.E B.A) (G : Matrix (Fin m) (Fin m) K.E) (a z : B.A) : K.E :=
  sv G (b.repr a) (b.repr z)

variable (b : Module.Basis (Fin m) K.E B.A) (G : Matrix (Fin m) (Fin m) K.E)

theorem sf_add_left (a a' z : B.A) : sf b G (a + a') z = sf b G a z + sf b G a' z := by
  simp [sf, sv, map_add (f := _), add_dotProduct]

theorem sf_smul_left (l : K.E) (a z : B.A) : sf b G (l • a) z = l * sf b G a z := by
  simp [sf, sv, map_smul, smul_dotProduct]

theorem sf_add_right (a z z' : B.A) : sf b G a (z + z') = sf b G a z + sf b G a z' := by
  have : (fun j => K.c ((b.repr (z + z')) j)) = (fun j => K.c (b.repr z j)) + fun j => K.c (b.repr z' j) := by
    ext j; simp
  simp only [sf, sv, this, mulVec_add, dotProduct_add]

theorem sf_smul_right (l : K.E) (a z : B.A) : sf b G a (l • z) = K.c l * sf b G a z := by
  have : (fun j => K.c ((b.repr (l • z)) j)) = K.c l • fun j => K.c (b.repr z j) := by
    ext j; simp
  simp only [sf, sv, this, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem sf_basis (i j : Fin m) : sf b G (b i) (b j) = G i j := by
  simp [sf, sv, dotProduct, mulVec, Finsupp.single_apply, Pi.single_apply]

end GlobalTheory.TwLat.BetaEx

namespace GlobalTheory.TwLat.BetaEx

variable {K : GlobalTheory.UnitLemma.UQ} {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ}
variable (b : Module.Basis (Fin m) K.E B.A) (G : Matrix (Fin m) (Fin m) K.E)

theorem sv_inv (N : Matrix (Fin m) (Fin m) K.E) (hN : Nᵀ * G * N.map K.c = G) (x y : Fin m → K.E) :
    sv G (N *ᵥ x) (N *ᵥ y) = sv G x y := by
  have hc : (fun j => K.c ((N *ᵥ y) j)) = N.map K.c *ᵥ fun j => K.c (y j) := by
    ext j; exact RingHom.map_mulVec (K.c : K.E →+* K.E) N y j
  unfold sv
  rw [hc, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hN]

theorem sf_mul_u (u : B.A) (hN : (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u))ᵀ * G *
    (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)).map K.c = G) (a z : B.A) :
    sf b G (u * a) (u * z) = sf b G a z := by
  unfold sf
  have h1 := LinearMap.toMatrix_mulVec_repr b b (LinearMap.mulLeft K.E u) a
  have h2 := LinearMap.toMatrix_mulVec_repr b b (LinearMap.mulLeft K.E u) z
  simp only [LinearMap.mulLeft_apply] at h1 h2
  rw [← h1, ← h2, sv_inv G _ hN]

theorem sf_adj (u : B.A) (hu : Algebra.adjoin K.E {u} = ⊤) (hu1 : u * B.σ u = 1)
    (hN : (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u))ᵀ * G *
    (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)).map K.c = G) (x a z : B.A) :
    sf b G (x * a) z = sf b G a (B.σ x * z) := by
  have hx : x ∈ Algebra.adjoin K.E {u} := hu ▸ Algebra.mem_top
  revert a z
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx; subst hx
    intro a z
    conv_lhs => rw [show z = x * (B.σ x * z) by rw [← mul_assoc, hu1, one_mul]]
    exact sf_mul_u b G x hN a _
  | algebraMap l =>
    intro a z
    rw [← Algebra.smul_def, sf_smul_left, B.σ_alg, ← Algebra.smul_def, sf_smul_right, K.c_c]
  | add x y _ _ hx hy =>
    intro a z
    rw [add_mul, sf_add_left, hx, hy, map_add (f := _), add_mul, sf_add_right]
  | mul x y _ _ hx hy =>
    intro a z
    rw [mul_comm x y, mul_assoc, hy, hx, map_mul]; congr 1; ring

end GlobalTheory.TwLat.BetaEx

namespace GlobalTheory.TwLat.BetaEx

theorem exists_beta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (u : B.A), Algebra.adjoin K.E {u} = ⊤ → u * B.σ u = 1 → (Algebra.traceForm K.E B.A).Nondegenerate → ∀ G : Matrix (Fin m) (Fin m) (w.adicCompletion E), (GlobalTheory.TwLat.mulMat e b u)ᵀ * G * (cj w).mapMatrix (GlobalTheory.TwLat.mulMat e b u) = G → ∃ β : B.A, GlobalTheory.TwLat.gram e b β = G := by
  intro E _ _ _ w K e he B m b u hu hu1 hnd G hG
  set N := LinearMap.toMatrix b b (LinearMap.mulLeft K.E u) with hNdef
  set G' : Matrix (Fin m) (Fin m) K.E := G.map e.symm with hG'
  have hGG : G = G'.map e := by ext i j; simp [hG']
  have hN : Nᵀ * G' * N.map K.c = G' := by
    have h2 : ((Nᵀ * G' * N.map K.c).map e) = G'.map e := by
      rw [← hGG]
      conv_rhs => rw [← hG]
      rw [hGG]
      have : (Nᵀ * G' * N.map K.c).map e = ((e : K.E →+* w.adicCompletion E).mapMatrix) (Nᵀ * G' * N.map K.c) := rfl
      rw [this, map_mul, map_mul]
      congr 1
      ext i j
      simp [GlobalTheory.TwLat.mulMat, hNdef, RingHom.mapMatrix_apply, he]
    exact Matrix.map_injective e.injective h2
  let ℓ : Module.Dual K.E B.A :=
    { toFun := fun a => sf b G' a 1
      map_add' := fun a a' => sf_add_left b G' a a' 1
      map_smul' := fun l a => sf_smul_left b G' l a 1 }
  refine ⟨(LinearMap.BilinForm.toDual _ hnd).symm ℓ, ?_⟩
  refine Matrix.ext fun i j => ?_
  set β := (LinearMap.BilinForm.toDual _ hnd).symm ℓ
  have hβ : ∀ a, Algebra.trace K.E B.A (β * a) = ℓ a := by
    intro a
    rw [← Algebra.traceForm_apply, ← LinearMap.BilinForm.toDual_def hnd, LinearEquiv.apply_symm_apply]
  simp only [GlobalTheory.TwLat.gram, Matrix.of_apply, GlobalTheory.UnitLemma.InvAlg.herm]
  rw [mul_assoc, hβ]
  show e (sf b G' (b i * B.σ (b j)) 1) = G i j
  rw [mul_comm, sf_adj b G' u hu hu1 hN, B.σ_σ, mul_one, sf_basis, hG']
  simp

end GlobalTheory.TwLat.BetaEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitRootCyclotomicExpExpansions
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachExp

theorem exists_locExp_expAt : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), l ≠ 2 → (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) → ∃ (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : ↥(OL LL)) (jj : ℕ → PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1), (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ maximalIdeal ↥(OL LL) ∧ ∀ b ∈ Finset.Ioo 0 l, IsLocExp l ↥(OL LL) ↥LL.1 (OL LL).val.toRingHom (ζ ^ b - 1) (u : ℤ_[l]) (jj b) ∧ IsExpAt (OL LL).val.toRingHom (ζ ^ b) (jj b) := by
  intro l _ LL _ hex
  obtain ⟨ζL, hζL⟩ := hex
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hfin := LL.2
  have hint : IsIntegral ℤ_[l] ζL := IsIntegral.of_pow hl (by rw [hζL.pow_eq_one]; exact isIntegral_one)
  let ζ : ↥(OL LL) := ⟨ζL, hint⟩
  have hζ : IsPrimitiveRoot ζ l :=
    IsPrimitiveRoot.of_map_of_injective (f := (OL LL).val) hζL Subtype.val_injective

  have hu : IsUnit (1 + (l : ℤ_[l]) * 1) := by
    have h := IsLocalRing.isUnit_or_isUnit_one_sub_self (-(l : ℤ_[l]))
    rcases h with h | h
    · exact absurd ((IsUnit.neg_iff _).1 h) PadicInt.prime_p.not_isUnit
    · simpa [sub_eq_add_neg] using h
  let u : ℤ_[l]ˣ := hu.unit
  have hu1 : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * 1 := hu.unit_spec

  have hmax : ζ - 1 ∈ maximalIdeal ↥(OL LL) := by
    refine (GlobalTheory.DiscEval.mem_maximalIdeal_iff_norm (p := l) LL.1 _).2 ?_
    refine lt_of_eq_of_lt (b := ‖((((ζL - 1 : ↥LL.1)) : PadicAlgCl l) : ℂ_[l])‖) rfl ?_
    rw [PadicComplex.norm_extends]
    exact norm_root_sub_one_lt LL hζL.pow_eq_one
  have hpow : ∀ b : ℕ, (ζL ^ b) ^ l = 1 := fun b => by
    rw [← pow_mul, mul_comm, pow_mul, hζL.pow_eq_one, one_pow]
  choose ev hC hev using fun b : ℕ => exists_ev LL (ζL ^ b) (hpow b)
  refine ⟨u, 1, ζ, ev, hu1, isUnit_one, hζ, hmax, fun b _ => ⟨⟨fun a => hC b a, ?_, fun f => ?_⟩, ⟨fun a => hC b a, hev b⟩⟩⟩
  · obtain ⟨g, hg⟩ : X ∣ exp ↥LL.1 - 1 := X_dvd_iff.2 (by simp)
    have hg0 : constantCoeff g = 1 := by
      have h := congrArg (coeff 1) hg
      rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply] at h
      rw [← h]; simp [coeff_exp]
    have hzb : ζL ^ b ≠ 0 := pow_ne_zero _ (hζL.ne_zero (by omega))
    have hunit : IsUnit (C (ζL ^ b) * g) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]; simp [hg0, hzb]
    have hcalc : ev b (X - C (ζ ^ b - 1)) = X * (C (ζL ^ b) * g) := by
      rw [map_sub, hev, hC]
      have hco : ((ζ ^ b - 1 : ↥(OL LL)) : ↥LL.1) = ζL ^ b - 1 := rfl
      rw [hco, map_sub (C : ↥LL.1 →+* _), map_one]
      linear_combination (C (ζL ^ b)) * hg
    rw [hcalc]
    exact associated_mul_unit_left X _ hunit
  · set r : ↥LL.1 := algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l]) with hr_def
    have hact : Formalism.CohomologicalDescent.HeightDescentMinors.act l ↥(OL LL) (u : ℤ_[l]) f = GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) f := by
      simp only [Formalism.CohomologicalDescent.HeightDescentMinors.act, Formalism.CohomologicalDescent.HeightDescentMinors.br, GlobalTheory.Fon.gam]
      exact (congrFun (coe_substAlgHom _) f).symm
    have hxz := ringHom_gam_X (O := ↥(OL LL)) (L := ↥LL.1) (ev b) (hC b) (ζL ^ b) (hev b) (hpow b)
      (u : ℤ_[l]) ⟨1, by rw [hu1]; ring⟩
    have huniq := ev_unique LL (C (ζL ^ b) * rescale r (exp ↥LL.1) - 1)
      (by rw [constantCoeff_exp_sub]; exact norm_root_sub_one_lt LL (hpow b))
      ((ev b).comp (GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) : PowerSeries ↥(OL LL) →+* PowerSeries ↥(OL LL)))
      ((rescale r).comp (ev b))
      (fun a => by
        change ev b (GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) (C a)) = _
        rw [GlobalTheory.Fon.gam_C, hC])
      (fun a => by
        change rescale r (ev b (C a)) = _
        rw [hC, rescale_C'])
      hxz
      (by
        change rescale r (ev b X) = _
        rw [hev, map_sub, map_mul, map_one, rescale_C'])
    rw [hact]
    exact RingHom.congr_fun huniq f

end GlobalTheory.WachExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryOfFrameNormConj
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing
open scoped ComplexConjugate

namespace GlobalTheory

section Points

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {B : LB Y}

theorem CxPts.mem_ptsIn_conj {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    {U : Y.Opens} (hy : y ∈ ptsIn p σ U) : y' ∈ ptsIn p σ' U := by
  change ⊤ ≤ y'.1 ⁻¹ᵁ U
  rw [h]
  exact fun x _ => hy (Set.mem_univ _)

end Points

theorem mem_unitaryGroup_of_norm_mulVec {α : Type*} [Fintype α] [DecidableEq α] {V : Matrix α α ℂ}
    (h : ∀ w : α → ℂ, √(∑ i, ‖V.mulVec w i‖ ^ 2) = √(∑ i, ‖w i‖ ^ 2)) : V ∈ Matrix.unitaryGroup α ℂ := by
  have key := (LinearMap.norm_map_iff_inner_map_map (Matrix.toEuclideanLin V)).1 fun x => by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    exact h x.ofLp
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have := key (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  simpa [PiLp.inner_apply, Matrix.mul_apply, Matrix.one_apply, mul_comm, Pi.single_apply, eq_comm] using this

theorem exists_unitary_of_frameNorm_conj {N : ℕ} {M M' : Matrix (Fin N) (Fin N) ℂ} (hM : M.det ≠ 0)
    (hM' : M'.det ≠ 0) (h : ∀ x : Fin N → ℂ, frameNorm M' (fun j => conj (x j)) = frameNorm M x) :
    ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, M' = M.map (starRingEnd ℂ) * U := by
  have hV : M'⁻¹ * M.map (starRingEnd ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    mem_unitaryGroup_of_norm_mulVec fun w => by
      have := h (M.mulVec fun j => conj (w j))
      have e : (fun j => conj (M.mulVec (fun j => conj (w j)) j)) = (M.map (starRingEnd ℂ)).mulVec w :=
        funext fun j => by simp [Matrix.mulVec, dotProduct]
      rw [e, frameNorm, frameNorm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul M hM.isUnit, Matrix.one_mulVec] at this
      simpa only [RCLike.norm_conj] using this
  refine ⟨_, Unitary.star_mem hV, ?_⟩
  have e : M.map (starRingEnd ℂ) = M' * (M'⁻¹ * M.map (starRingEnd ℂ)) := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv M' hM'.isUnit, Matrix.one_mul]
  generalize M'⁻¹ * M.map (starRingEnd ℂ) = V at e hV
  rw [e, Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff.1 hV, Matrix.mul_one]

variable {F : Type} [Field F] [NumberField F]

theorem Adelic.HermSys.isConj_weight (T : Adelic.HermSys F) (hb : T.BasePointFree) (hh : T.Hermitian)
    (hc : T.ConjInvariant) (σ : F →+* ℂ) :
    (T.weight hb hh σ).IsConj (T.weight hb hh (ComplexEmbedding.conjugate σ)) := by
  obtain ⟨U, hU, e⟩ := exists_unitary_of_frameNorm_conj (hh σ) (hh (ComplexEmbedding.conjugate σ)) (hc σ)
  exact Weight.isConj_fsBasis_of_unitary _ _ _ _ _ hU e

namespace HilbertSamuel.Geo

variable (G : Geo F)

theorem isConj_φ₂ (σ : F →+* ℂ) : (G.φ₂ σ).IsConj (G.φ₂ (ComplexEmbedding.conjugate σ)) :=
  G.second.isConj_weight _ _ G.conj₂ σ

variable {G}

end HilbertSamuel.Geo

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationSplitUnitarySchwartzBruh
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.Exist

theorem exists_isKW : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψn hψ1 χ hχ hη _ _ μ _
  obtain ⟨hFD, -, -, -, -, -, -, hM⟩ := _root_.GlobalTheory.quadExt_topology F E c δ hE
  haveI := hFD
  obtain ⟨hMT, hGood⟩ := hM α ν
  haveI := hMT
  haveI := hGood.grp
  obtain ⟨β, hβ, hβs, hβn, -, -⟩ := _root_.GlobalTheory.KSp.pr_alg F E c δ hE α ν Q hQ
  have hpair : IsPair (fun x y : Matrix α ν E => ψ (pr c Q x y)) := by
    have h := _root_.GlobalTheory.KSp.isPair_addChar_form F (Matrix α ν E) ψ hψ hψn hψ1 β hβs hβn
    simpa only [hβ] using h
  have hfm : ∀ φ ∈ SB (Matrix α ν E), fou c ψ Q μ φ ∈ SB (Matrix α ν E) := fun φ hφ =>
    _root_.GlobalTheory.KSp.FourMem.four_mem_SB (Matrix α ν E) hGood μ _ hpair φ hφ
  have hpm := GlobalTheory.T.siegelParabolic_preserves_schwartzBruhat F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη
  obtain ⟨hp1, hpmul⟩ := GlobalTheory.T.parFun_sieg_mul' F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη
  obtain ⟨κ, hκ, hrel⟩ := GlobalTheory.T.exists_weilRepresentation_bigCell_relation_fourier F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη μ
  obtain ⟨C, hC, hff⟩ := GlobalTheory.T.bicharacterFourierTransform_twice_eq_pos_smul_reflect (Matrix α ν E) hGood μ _ hpair

  let parL : sieg c ν → Module.End ℂ (SB (Matrix α ν E)) := fun p =>
    { toFun := fun φ => ⟨parFun c ψ χ Q (mat c p) φ, hpm p p.2 φ φ.2⟩
      map_add' := fun φ φ' => Subtype.ext (funext fun x => by
        simp only [parFun, Submodule.coe_add, Pi.add_apply]; ring)
      map_smul' := fun z φ => Subtype.ext (funext fun x => by
        simp only [parFun, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring) }
  let ρ₀ : sieg c ν →* Module.End ℂ (SB (Matrix α ν E)) :=
    { toFun := parL
      map_one' := LinearMap.ext fun φ => Subtype.ext (hp1 φ)
      map_mul' := fun p q => LinearMap.ext fun φ => Subtype.ext (hpmul p p.2 q q.2 φ) }

  have hint : ∀ φ : Matrix α ν E → ℂ, φ ∈ SB (Matrix α ν E) → ∀ x,
      Integrable (fun y => ψ (pr c Q x y) * φ y) μ := by
    intro φ hφ x
    have hlc : IsLocallyConstant (fun y => ψ (pr c Q x y) * φ y) :=
      (hpair.lc.comp_continuous (continuous_const.prodMk continuous_id)).mul hφ.1
    exact hlc.continuous.integrable_of_hasCompactSupport hφ.2.mul_left
  have fou_smul : ∀ (k : ℂ) (f : Matrix α ν E → ℂ) x, fou c ψ Q μ (k • f) x = k * fou c ψ Q μ f x := by
    intro k f x
    simp only [fou, four, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1; funext y; ring
  let Fo : Module.End ℂ (SB (Matrix α ν E)) :=
    { toFun := fun φ => ⟨fou c ψ Q μ φ, hfm φ φ.2⟩
      map_add' := fun φ φ' => Subtype.ext (funext fun x => by
        simp only [fou, four, Submodule.coe_add, Pi.add_apply, mul_add]
        exact integral_add (hint _ φ.2 x) (hint _ φ'.2 x))
      map_smul' := fun z φ => Subtype.ext (funext fun x => by
        simp only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        exact fou_smul z _ x) }
  have hne : (κ ^ 2 * (C : ℂ)) ≠ 0 := mul_ne_zero (pow_ne_zero _ hκ) (by exact_mod_cast hC.ne')
  have key : ∀ φ : SB (Matrix α ν E),
      (((κ • Fo) ((κ • Fo) φ) : SB (Matrix α ν E)) : Matrix α ν E → ℂ) = fun x => (κ ^ 2 * (C : ℂ)) * (φ : Matrix α ν E → ℂ) (-x) := by
    intro φ
    funext x
    show κ * fou c ψ Q μ (κ • fou c ψ Q μ φ) x = _
    rw [fou_smul]
    have h := hff φ φ.2 x
    change fou c ψ Q μ (fou c ψ Q μ φ) x = _ at h
    rw [h]
    ring
  have hW : IsUnit (κ • Fo) := by
    rw [Module.End.isUnit_iff]
    constructor
    · intro a b hab
      have h2 := congrArg (fun φ => (((κ • Fo) φ : SB (Matrix α ν E)) : Matrix α ν E → ℂ)) hab
      simp only [key] at h2
      apply Subtype.ext
      funext x
      have h3 := congrFun h2 (-x)
      simp only [neg_neg] at h3
      exact mul_left_cancel₀ hne h3
    · intro φ
      have hr : (fun x => (φ : Matrix α ν E → ℂ) (-x)) ∈ SB (Matrix α ν E) :=
        ⟨φ.2.1.comp_continuous continuous_neg, φ.2.2.comp_homeomorph (Homeomorph.neg _)⟩
      refine ⟨(κ ^ 2 * (C : ℂ))⁻¹ • (κ • Fo) ⟨_, hr⟩, Subtype.ext (funext fun x => ?_)⟩
      rw [map_smul, Submodule.coe_smul, Pi.smul_apply, key]
      simp only [neg_neg, smul_eq_mul]
      exact inv_mul_cancel_left₀ hne _
  obtain ⟨Φ, hΦp, hΦw⟩ := _root_.GlobalTheory.bigCell_hom (UG c (stdJ ν E)) (Module.End ℂ (SB (Matrix α ν E)))ˣ (sieg c ν)
    (weyl c ν) ρ₀.toHomUnits hW.unit
    (by
      intro p q hpq
      apply Units.ext
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      funext x
      have h := GlobalTheory.T.fourier_intertwines_siegelLeviOperator F E c δ hE α ν Q hQ ψ hψ hψn hψ1 χ hχ hη μ p p.2 q q.2 hpq φ
      show κ * fou c ψ Q μ (parFun c ψ χ Q (mat c p) φ) x =
        parFun c ψ χ Q (mat c q) (κ • fou c ψ Q μ φ) x
      rw [h]
      simp only [parFun, Pi.smul_apply, smul_eq_mul]
      ring)
    (by
      rintro p ⟨p₁, p₂, h⟩
      obtain ⟨q₁, hq₁, q₂, hq₂, he, hop⟩ := hrel p p.2 ⟨p₁, p₁.2, p₂, p₂.2, h⟩
      refine ⟨⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩, he, ?_⟩
      apply Units.ext
      apply LinearMap.ext
      intro φ
      apply Subtype.ext
      exact hop φ φ.2)
    (by
      intro s
      obtain ⟨u, hu⟩ := _root_.GlobalTheory.KSp.exists_translate_inCell F E c δ hE ν s
      refine ⟨u, fun g hg => ?_⟩
      obtain ⟨p, hp, q, hq, h⟩ := hu g hg
      exact ⟨⟨p, hp⟩, ⟨q, hq⟩, h⟩)
  refine ⟨κ, (Units.coeHom _).comp Φ, ⟨fun p hp φ => ?_, fun φ => ?_⟩⟩
  · have h := hΦp ⟨p, hp⟩
    change ((Φ ((⟨p, hp⟩ : sieg c ν) : UG c (stdJ ν E)) : Module.End ℂ (SB (Matrix α ν E))) φ :
      Matrix α ν E → ℂ) = _
    rw [h]
    rfl
  · change ((Φ (weyl c ν) : Module.End ℂ (SB (Matrix α ν E))) φ : Matrix α ν E → ℂ) = _
    rw [hΦw, IsUnit.unit_spec]
    rfl

end GlobalTheory.KSp.Exist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitEqNormAlmostAllPlacesStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_unit_eq_norm_almost_all_places : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) → (∃ x, c x ≠ x) →
    ∀ (κ : Type) (bL : Module.Basis κ ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ e : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
        Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑e = ↑e → IsIntB v bL ↑e →
        IsIntB v bL ↑e⁻¹ → ∃ y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
          (e : v.adicCompletion ℚ ⊗[ℚ] L) = ↑y * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑y := by
  first | (exact @GlobalTheory.LocNorm.unit_fixed_is_norm) | (exact GlobalTheory.LocNorm.unit_fixed_is_norm) | (intros; apply GlobalTheory.LocNorm.unit_fixed_is_norm  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealIntegralLattice
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractional_ideal_integral_lattice : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ I : Set (v.adicCompletion ℚ ⊗[ℚ] L), 0 ∈ I →
      (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ, IsIntB v ℓ ρ → ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x, IsIntB v ℓ x → (D : v.adicCompletion ℚ ⊗[ℚ] L) * x ∈ I) ∧
        ∀ x ∈ I, IsIntB v ℓ ((D : v.adicCompletion ℚ ⊗[ℚ] L) * x)) →
      ∃ m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, ∀ x, x ∈ I ↔ ∃ ρ, IsIntB v ℓ ρ ∧ x = ↑m * ρ := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_lattice_principal_eventually) | (exact GlobalTheory.AdicSpan.isIntB_lattice_principal_eventually) | (intros; apply GlobalTheory.AdicSpan.isIntB_lattice_principal_eventually  <;> assumption)
end

