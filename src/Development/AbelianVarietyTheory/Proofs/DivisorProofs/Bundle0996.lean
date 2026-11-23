module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialNonneg

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFinrankLineBundleSectionsFiniteEtale
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin
open H0

theorem eq_zero_of_forall_algHom_eq_zero {E A : Type} (Ω : Type) [Field E] [CommRing A]
    [Algebra E A] [Algebra.Etale E A] [Field Ω] [IsAlgClosed Ω] [Algebra E Ω] {a : A}
    (h : ∀ φ : A →ₐ[E] Ω, φ a = 0) : a = 0 := by
  have := Algebra.FormallyUnramified.finite_of_free E A
  have : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field E A
  have : IsArtinianRing A := .of_finite E A
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun J hJ => ?_)
  have hm : J.IsMaximal := IsArtinianRing.isMaximal_of_isPrime J
  let := Ideal.Quotient.field J
  let ψ : (A ⧸ J) →ₐ[E] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have := h (ψ.comp (Ideal.Quotient.mkₐ E J))
  rw [AlgHom.comp_apply, map_eq_zero_iff ψ ψ.toRingHom.injective] at this
  exact Ideal.Quotient.eq_zero_iff_mem.1 this

section Points

variable {k R : Type} [CommRing k] [CommRing R] {S : Scheme.{0}}

theorem evalPt_algX (q : S ⟶ Sp k) (x : Sp R ⟶ S) (U : S.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (c : k) :
    evalPt x U h (algX q U c) =
      evalPt (x ≫ q) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) :=
  congrArg (fun g => (g ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
    (Scheme.Hom.appLE_comp_appLE x q ⊤ U ⊤ le_top h)

theorem evalPt_algX_of_eq (q : S ⟶ Sp k) (x : Sp R ⟶ S) {φ : k →+* R} (hx : x ≫ q = spMap φ)
    (U : S.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (c : k) : evalPt x U h (algX q U c) = φ c := by
  rw [evalPt_algX, hx, evalPt_spMap]

theorem H0.val_smul {q : S ⟶ Sp k} {N : LB S} {O : S.Opens} (x : Sp R ⟶ S) {φ : k →+* R}
    (hx : x ≫ q = spMap φ) (i : N.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ N.U i) (c : k)
    (f : H0 q N O) : val x i hO hi (c • f) = φ c * val x i hO hi f := by
  rw [base_smul, val_fun_smul, evalPt_algX_of_eq q x hx]


variable (R) in
abbrev PtsOver [Algebra k R] (q : S ⟶ Sp k) : Type :=
  {x : Sp R ⟶ S // x ≫ q = spMap (algebraMap k R)}

def ptsOverEquiv [Algebra k R] [IsAffine S] (q : S ⟶ Sp k) :
    letI := (algX q ⊤).toAlgebra
    PtsOver R q ≃ (Γ(S, ⊤) →ₐ[k] R) :=
  letI := (algX q ⊤).toAlgebra
  Equiv.ofBijective
    (fun x => ⟨evalPt x.1 ⊤ le_top, fun c => evalPt_algX_of_eq q x.1 x.2 ⊤ le_top c⟩)
    ⟨fun x y e => Subtype.ext (ext_evalPt (isAffineOpen_top S) le_top le_top
      (congrArg AlgHom.toRingHom e)), fun ψ => by
      obtain ⟨x, h, e⟩ := exists_evalPt_eq (isAffineOpen_top S) ψ.toRingHom
      refine ⟨⟨x, eq_spMap_of_evalPt _ _ fun c => ?_⟩, AlgHom.ext fun a => DFunLike.congr_fun e a⟩
      rw [← evalPt_algX q x ⊤ h, e]
      exact ψ.commutes c⟩

end Points

section FiniteEtale

variable {E : Type} [Field E] {S : Scheme.{0}} (q : S ⟶ Sp E)

theorem etale_algX [IsAffine S] [Etale q] : (algX q ⊤).Etale :=
  RingHom.Etale.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of E)).symm.commRingCatIsoToRingEquiv
    (HasRingHomProperty.appLE @Etale q ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨⊤, isAffineOpen_top _⟩ le_top)

variable {N : LB S}

theorem exists_generator [IsFinite q] [Etale q] (hN : N.IsLB) : ∃ e : H0 q N ⊤,
    (Function.Bijective fun a : Γ(S, ⊤) => a • e) ∧ ∀ i, IsUnit (e.loc i) := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  have := Algebra.FormallyUnramified.finite_of_free E Γ(S, ⊤)
  have : IsArtinianRing Γ(S, ⊤) := .of_finite E _
  obtain ⟨t, ht⟩ := exists_isGen_of_subsingleton_pic_top hN
  refine ⟨H0.ofSec q ⊤ (DVR.genSec t ht), ?_, fun i => (Units.isUnit (t.s i)).map (resG S inf_le_right)⟩
  have := isQuasicoherent_toMod hN
  exact (isFrame_iff_bijective (isAffineOpen_top S) _).1 (isFrame_genSec hN ht ⊤)

variable (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra E Ω] [IsFinite q] [Etale q]


omit [IsAlgClosed Ω] in
theorem finite_ptsOver : Finite (PtsOver Ω q) := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  have := Algebra.FormallyUnramified.finite_of_free E Γ(S, ⊤)
  exact Finite.of_equiv _ (ptsOverEquiv q).symm

theorem finite_finrank_lineBundleSections_finiteEtale (hN : N.IsLB) :
    Module.Finite E (H0 q N ⊤) ∧ Module.finrank E (H0 q N ⊤) = Nat.card (PtsOver Ω q) := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  have := Algebra.FormallyUnramified.finite_of_free E Γ(S, ⊤)
  obtain ⟨e, he, -⟩ := exists_generator q hN
  let ψ : Γ(S, ⊤) →ₗ[E] H0 q N ⊤ :=
    { toFun a := a • e
      map_add' a b := add_smul a b e
      map_smul' c a := mul_smul (algX q ⊤ c) a e }
  let φ := LinearEquiv.ofBijective ψ he
  exact ⟨.equiv φ, by
    rw [← φ.finrank_eq, Nat.card_congr (ptsOverEquiv q), natCard_algHom_eq_finrank_of_etale]⟩

variable {q Ω}

theorem H0.eq_zero_of_forall_val_eq_zero (hN : N.IsLB) (i : PtsOver Ω q → N.ι)
    (hi : ∀ x : PtsOver Ω q, ⊤ ≤ x.1 ⁻¹ᵁ N.U (i x)) {g : H0 q N ⊤}
    (h : ∀ x : PtsOver Ω q, val x.1 (i x) le_top (hi x) g = 0) : g = 0 := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  obtain ⟨e, he, hu⟩ := exists_generator q hN
  obtain ⟨a, rfl⟩ := he.2 g
  have : a = 0 := eq_zero_of_forall_algHom_eq_zero (E := E) Ω fun ψ => by
    obtain ⟨x, rfl⟩ := (ptsOverEquiv q).surjective ψ
    have := (val_fun_smul x.1 (i x) le_top (hi x) a e).symm.trans (h x)
    exact (((hu (i x)).map (evalPt x.1 _ _)).mul_left_eq_zero).1 this
  simp only [this, zero_smul]

end FiniteEtale

section Subscheme

variable {E : Type} [Field E] {Y : Scheme.{0}} {p : Y ⟶ Sp E} {I : Y.IdealSheafData} {B : LB Y}

theorem exists_chart_of_field {F : Type} [Field F] (hB : B.IsLB) (x : Sp F ⟶ Y) :
    ∃ i, ⊤ ≤ x ⁻¹ᵁ B.U i := by
  obtain ⟨i, hi⟩ := exists_chart hB (x (default : PrimeSpectrum F))
  exact ⟨i, fun z _ => (Subsingleton.elim (α := PrimeSpectrum F) default z) ▸ hi⟩

theorem valOn_smul {k R : Type} [CommRing k] [CommRing R] {p : Y ⟶ Sp k}
    (x : Sp R ⟶ I.subscheme) {φ : k →+* R} (hx : x ≫ I.subschemeι ≫ p = spMap φ) (i : B.ι)
    (hi : ⊤ ≤ (x ≫ I.subschemeι) ⁻¹ᵁ B.U i) (c : k) (g : sectionsOnClosedSubscheme p B I) :
    valOn x i hi (c • g) = φ c * valOn x i hi g :=
  H0.val_smul x hx _ _ _ c g

variable [IsFinite (I.subschemeι ≫ p)] [Etale (I.subschemeι ≫ p)] (hB : B.IsLB)
  (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra E Ω]

include hB

theorem finite_H0On : Module.Finite E (sectionsOnClosedSubscheme p B I) :=
  (finite_finrank_lineBundleSections_finiteEtale _ (AlgebraicClosure E) (LB.isLB_pull hB _)).1

theorem finrank_H0On :
    Module.finrank E (sectionsOnClosedSubscheme p B I) = Nat.card (PtsOver Ω (I.subschemeι ≫ p)) :=
  (finite_finrank_lineBundleSections_finiteEtale _ Ω (LB.isLB_pull hB _)).2


variable {Ω} in
theorem eq_zero_of_forall_valOn_eq_zero (i : PtsOver Ω (I.subschemeι ≫ p) → B.ι)
    (hi : ∀ x : PtsOver Ω (I.subschemeι ≫ p), ⊤ ≤ (x.1 ≫ I.subschemeι) ⁻¹ᵁ B.U (i x))
    {g : sectionsOnClosedSubscheme p B I} (h : ∀ x : PtsOver Ω (I.subschemeι ≫ p), valOn x.1 (i x) (hi x) g = 0) : g = 0 :=
  H0.eq_zero_of_forall_val_eq_zero (LB.isLB_pull hB _) (fun x _ => i x) _ h

end Subscheme

end GlobalTheory.Vanishing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePolynomialsBoundedDenom
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Northcott

theorem isIntegral_eig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsIntegral ℤ M) {w : ℂ}
    {x : Fin n → ℂ} (hx : x ≠ 0) (hMx : M *ᵥ x = w • x) : IsIntegral ℤ w := by
  obtain ⟨q, hq, hqM⟩ := hM
  refine ⟨q, hq, ?_⟩
  have hv : Module.End.HasEigenvector (Matrix.toLin' M) w x :=
    ⟨Module.End.mem_eigenspace_iff.2 (by simpa [Matrix.toLin'_apply] using hMx), hx⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q.map (algebraMap ℤ ℂ)) hv
  have h2 : Polynomial.aeval (Matrix.toLin' M) (q.map (algebraMap ℤ ℂ)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    have e := Polynomial.aeval_algHom_apply
      ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] _).toAlgHom.restrictScalars ℤ) M q
    have e2 : Polynomial.aeval M q = 0 := hqM
    rw [e2, map_zero] at e
    exact e
  rw [h2, LinearMap.zero_apply] at h1
  have h3 := (smul_eq_zero.1 h1.symm).resolve_right hx
  rwa [Polynomial.eval_map] at h3

theorem norm_le_of_isIntegral_inv (w : ℂ) (c : ℚ) (N : ℕ) (hN : 0 < N) (hw : ‖w‖ ^ 2 = (c : ℝ))
    (hc : (c : ℝ) ≠ 0) (hI : IsIntegral ℤ ((N : ℂ) * w⁻¹)) : ‖w‖ ≤ N := by
  have hcpos : (0 : ℝ) < c := lt_of_le_of_ne (hw ▸ sq_nonneg _) (Ne.symm hc)
  have hconj : IsIntegral ℤ (starRingEnd ℂ ((N : ℂ) * w⁻¹)) := hI.map (starRingEnd ℂ).toIntAlgHom
  have hprod := hI.mul hconj
  have e : (N : ℂ) * w⁻¹ * starRingEnd ℂ ((N : ℂ) * w⁻¹) = (((N : ℚ) ^ 2 / c : ℚ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, norm_inv, mul_pow, inv_pow, hw,
      Complex.norm_natCast]
    push_cast
    ring
  rw [e] at hprod
  have hq : IsIntegral ℤ ((N : ℚ) ^ 2 / c) := by
    refine (isIntegral_algHom_iff ((algebraMap ℚ ℂ).toIntAlgHom) (algebraMap ℚ ℂ).injective
      (x := (N : ℚ) ^ 2 / c)).1 ?_
    simpa using hprod
  obtain ⟨k, hk⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hq
  have hcq : (0 : ℚ) < c := by exact_mod_cast hcpos
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hpos : (0 : ℚ) < (N : ℚ) ^ 2 / c := by positivity
  have hk1 : (1 : ℚ) ≤ (N : ℚ) ^ 2 / c := by
    rw [← hk] at hpos ⊢
    rw [algebraMap_int_eq, eq_intCast] at hpos ⊢
    have : (0 : ℤ) < k := by exact_mod_cast hpos
    have : (1 : ℤ) ≤ k := this
    exact_mod_cast this
  have hcN : (c : ℚ) ≤ (N : ℚ) ^ 2 := by rwa [le_div_iff₀ hcq, one_mul] at hk1
  have hcN' : (c : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hcN
  rw [← hw] at hcN'
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Nat.cast_nonneg _) two_ne_zero).1 hcN'

end GlobalTheory.LKMid.Northcott
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatZeroFromResolutionAndGaga
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.DFormPos

theorem sim_pos : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (B : GlobalTheory.LKDef.DForm G) (y : G.Cˣ) (s : ℚ),
    (y : G.C) * B.β * sh G y = algebraMap ℚ G.C s * B.β → 0 < s := by
  intro p _ G B y s hsim0
  obtain ⟨v⟩ : Nonempty (InfinitePlace G.F) := inferInstance
  set h := G.gram v
  set A := G.psi v (y : G.C)
  set Ai := G.psi v ((y⁻¹ : G.Cˣ) : G.C)
  set Pb := G.psi v (B.β : G.C)
  set Bm := G.psi v ((B.β⁻¹ : G.Cˣ) : G.C)
  set c : ℂ := ((s : ℚ) : ℂ)
  have hsim := congrArg (G.psi v) hsim0
  have hc : G.psi v (algebraMap ℚ G.C s) = c • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
    rw [IsScalarTower.algebraMap_apply ℚ G.F G.C, G.psi_F]
    ext i j; simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply, c]
  rw [map_mul, map_mul, map_mul, hc] at hsim
  change A * Pb * G.psi v (G.star (y : G.C)).unop = _ at hsim
  rw [G.psi_star, Matrix.smul_mul, Matrix.one_mul] at hsim
  have hBβ : Bm * Pb = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hβB : Pb * Bm = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hAiA : Ai * A = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hdet : IsUnit h.det := isUnit_iff_ne_zero.2 (G.gram_det v)
  have hhi : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h hdet
  have e1 : Aᴴ * h = c • (h * Bm * Ai * Pb) := by
    have := congrArg (fun M => h * Bm * Ai * M) hsim
    calc Aᴴ * h = h * Bm * Ai * (A * Pb * (h⁻¹ * Aᴴ * h)) := by
          simp only [← Matrix.mul_assoc]
          rw [Matrix.mul_assoc (h * Bm) Ai A, hAiA, Matrix.mul_one, Matrix.mul_assoc h Bm Pb, hBβ, Matrix.mul_one, hhi,
            Matrix.one_mul]
      _ = _ := by rw [this, Matrix.mul_smul]
  have key : Aᴴ * (h * Bm) * A = c • (h * Bm) := by
    rw [← Matrix.mul_assoc, e1, Matrix.smul_mul, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pb Bm A, hβB, Matrix.one_mul, hAiA, Matrix.mul_one]
  obtain ⟨x, hx⟩ : ∃ x : Fin G.n → ℂ, x ≠ 0 := ⟨Pi.single ⟨0, G.n_pos⟩ 1, by simp⟩
  have hAx : A *ᵥ x ≠ 0 := fun h0 => hx (by
    have := congrArg (Ai *ᵥ ·) h0
    simpa [Matrix.mulVec_mulVec, hAiA] using this)
  have e2 : star (A *ᵥ x) ⬝ᵥ ((h * Bm) *ᵥ (A *ᵥ x)) = c * (star x ⬝ᵥ ((h * Bm) *ᵥ x)) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc] at key ⊢
    rw [key, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hcr : c = ((s : ℝ) : ℂ) := by simp [c]
  have h1 := B.posR v x hx
  have h2 := B.posR v _ hAx
  change (_ → 0 < (star x ⬝ᵥ ((h * Bm) *ᵥ x)).re) ∧ (_ → (star x ⬝ᵥ ((h * Bm) *ᵥ x)).re < 0) at h1
  change (_ → 0 < (star (A *ᵥ x) ⬝ᵥ ((h * Bm) *ᵥ (A *ᵥ x))).re) ∧
    (_ → (star (A *ᵥ x) ⬝ᵥ ((h * Bm) *ᵥ (A *ᵥ x))).re < 0) at h2
  rw [e2, hcr, Complex.re_ofReal_mul] at h2
  have hs : (0 : ℝ) < s := by
    by_cases hv : sigPosH (G.gram_herm v) = 1
    · have a1 := h1.1 hv
      have a2 := h2.1 hv
      by_contra hn
      push_neg at hn
      nlinarith
    · have a1 := h1.2 hv
      have a2 := h2.2 hv
      by_contra hn
      push_neg at hn
      nlinarith
  exact_mod_cast hs

end GlobalTheory.LKDef.DFormPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlowInvSplit
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem flowInv_herm {n : ℕ} {Hm x₀ : Mt n} {q : ℕ} (h : OrthFr Hm q x₀) : Hmᴴ = Hm := by
  obtain ⟨-, hD⟩ := h
  have hdet : x₀.det ≠ 0 := by
    intro h0
    have hd := congrArg Matrix.det hD
    rw [det_mul, det_mul, h0, mul_zero, det_diagonal] at hd
    refine (Finset.prod_ne_zero_iff.mpr fun a _ => ?_) hd.symm
    unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> norm_num
  have hu : IsUnit x₀ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have huH : IsUnit x₀ᴴ := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ?_)
    rw [det_conjTranspose]
    exact (star_ne_zero).mpr hdet
  have hself : (x₀ᴴ * Hm * x₀)ᴴ = x₀ᴴ * Hm * x₀ := by
    rw [hD, diagonal_conjTranspose]
    congr 1
    funext a
    simp [Complex.conj_ofReal]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc] at hself
  exact huH.mul_right_injective (hu.mul_left_injective hself)

theorem flowInv_sq {n : ℕ} {Hm : Mt n} {e : Fin n → ℂ} (he : star e ⬝ᵥ Hm.mulVec e = 0) :
    vecMulVec e (star e ᵥ* Hm) * vecMulVec e (star e ᵥ* Hm) = 0 := by
  rw [vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, he, zero_smul]
  ext i j
  simp [vecMulVec_apply]

theorem flowInv_adj {n : ℕ} {Hm : Mt n} (hH : Hmᴴ = Hm) (e : Fin n → ℂ) :
    (vecMulVec e (star e ᵥ* Hm))ᴴ * Hm = Hm * vecMulVec e (star e ᵥ* Hm) := by
  rw [conjTranspose_vecMulVec, star_vecMul, star_star, hH, vecMulVec_mul, mul_vecMulVec]

private theorem one_sub_sub_smul_vecMulVec_eq_mul_of_isotropic {n : ℕ} {Hm : Mt n} {e : Fin n → ℂ} (he : star e ⬝ᵥ Hm.mulVec e = 0)
    (a b : ℂ) : (1 - (b - a) • vecMulVec e (star e ᵥ* Hm) : Mt n) =
      (1 + a • vecMulVec e (star e ᵥ* Hm)) * (1 - b • vecMulVec e (star e ᵥ* Hm)) := by
  have hS := flowInv_sq he
  rw [add_mul, one_mul, mul_sub, mul_one, smul_mul_assoc, mul_smul_comm, hS, smul_zero, smul_zero, sub_zero,
    sub_smul]
  abel

theorem flowInv_mem {n : ℕ} {Hm : Mt n} (hH : Hmᴴ = Hm) {e : Fin n → ℂ} (he : star e ⬝ᵥ Hm.mulVec e = 0)
    (s : ℝ) : (1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm) : Mt n) ∈ Formalism.QuantumDeterminants.UH Hm := by
  show (1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm))ᴴ * Hm *
    (1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm)) = Hm
  have hc : star ((s : ℂ) * Complex.I) = -((s : ℂ) * Complex.I) := by
    simp [Complex.conj_ofReal]
  have h1 : (1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm))ᴴ * Hm =
      Hm * (1 + (-((s : ℂ) * Complex.I)) • vecMulVec e (star e ᵥ* Hm)) := by
    rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, add_mul, one_mul, smul_mul_assoc,
      flowInv_adj hH e, hc, mul_add, mul_one, mul_smul_comm]
  have h2 := one_sub_sub_smul_vecMulVec_eq_mul_of_isotropic he (-((s : ℂ) * Complex.I)) (-((s : ℂ) * Complex.I))
  have h3 : (1 - (-((s : ℂ) * Complex.I)) • vecMulVec e (star e ᵥ* Hm) : Mt n) =
      1 + ((s : ℂ) * Complex.I) • vecMulVec e (star e ᵥ* Hm) := by
    rw [neg_smul, sub_neg_eq_add]
  rw [sub_self, zero_smul, sub_zero, h3] at h2
  rw [h1, Matrix.mul_assoc, ← h2, mul_one]

private theorem mul_mem_uh {n : ℕ} {Hm g₁ g₂ : Mt n} (h₁ : g₁ ∈ Formalism.QuantumDeterminants.UH Hm) (h₂ : g₂ ∈ Formalism.QuantumDeterminants.UH Hm) :
    g₁ * g₂ ∈ Formalism.QuantumDeterminants.UH Hm := by
  change g₁ᴴ * Hm * g₁ = Hm at h₁
  change g₂ᴴ * Hm * g₂ = Hm at h₂
  show (g₁ * g₂)ᴴ * Hm * (g₁ * g₂) = Hm
  rw [conjTranspose_mul]
  calc g₂ᴴ * g₁ᴴ * Hm * (g₁ * g₂) = g₂ᴴ * (g₁ᴴ * Hm * g₁) * g₂ := by simp only [Matrix.mul_assoc]
    _ = Hm := by rw [h₁, h₂]

theorem flowInv : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ (P : (ι → Fin n → Fin n → ℂ) → ℂ) (e : ι → Fin n → ℂ), (∀ τ, star (e τ) ⬝ᵥ (Hm τ).mulVec (e τ) = 0) → HolSec Hm q w P → (∀ m : ι → Mt n, (∀ τ, InZe (Hm τ) (e τ) (m τ)) → ∀ u ∈ UG Hm, P (fun τ => (m τ * u τ * x₀ τ : Mt n)) = P (fun τ => (u τ * x₀ τ : Mt n))) → ∀ u ∈ UG Hm, ∀ t : ℝ, 0 ≤ t → P (fun τ => ((1 - (t : ℂ) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ : Mt n)) = P (fun τ => (u τ * x₀ τ : Mt n)) := by
  intro n ι _ _ Hm q x₀ w hO P e he hP hInv u hu t ht
  have hH : ∀ τ, (Hm τ)ᴴ = Hm τ := fun τ => flowInv_herm (hO τ)
  have hu' : ∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (Hm τ) := hu
  obtain ⟨hOpen, -, hStab, hBase⟩ := frDoms_open_preconnected_stable n ι Hm q x₀ hO
  let X : ℂ → (ι → Fin n → Fin n → ℂ) := fun z τ =>
    ((1 - z • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ : Mt n)
  have hXaff : X = fun z τ i j => (u τ * x₀ τ) i j - z * (vecMulVec (e τ) (star (e τ) ᵥ* Hm τ) * u τ * x₀ τ) i j := by
    funext z τ i j
    simp only [X, sub_mul, one_mul, smul_mul_assoc, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have hXd : Differentiable ℂ X := by
    rw [hXaff]
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
    exact (differentiable_const _).sub (differentiable_id.mul (differentiable_const _))
  have hHU : {z : ℂ | 0 ≤ z.re} ⊆ X ⁻¹' frDoms Hm q := by
    intro z hz
    have hGS := fun τ => FlowGS.flowGS n (Hm τ) (q τ) (x₀ τ) (hO τ) (w τ) (e τ) (he τ) (u τ) (hu' τ)
    choose C A hCA using hGS
    choose u' hu' b hbf using fun τ => hCA τ z.re hz
    have hmem := hStab (fun τ => (1 + (((-z.im : ℝ) : ℂ) * Complex.I) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u' τ)
      (show ∀ τ, _ ∈ Formalism.QuantumDeterminants.UH (Hm τ) from fun τ => mul_mem_uh (flowInv_mem (hH τ) (he τ) (-z.im)) (hu' τ)) b (fun τ => (hbf τ).1)
      (fun τ => (x₀ τ : Mt n)) hBase
    suffices hXz : X z = fun τ => ((1 + (((-z.im : ℝ) : ℂ) * Complex.I) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u' τ * x₀ τ * b τ : Mt n) by
      show X z ∈ frDoms Hm q
      rw [hXz]
      exact hmem
    funext τ
    have hfac := (hbf τ).2.1
    have hsplit := one_sub_sub_smul_vecMulVec_eq_mul_of_isotropic (he τ) (((-z.im : ℝ) : ℂ) * Complex.I) (z.re : ℂ)
    have hz' : (z.re : ℂ) - ((-z.im : ℝ) : ℂ) * Complex.I = z := by
      apply Complex.ext <;> simp
    rw [hz'] at hsplit
    show (1 - z • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ = _
    simp only [Matrix.mul_assoc] at hfac ⊢
    rw [hsplit, Matrix.mul_assoc, hfac]
  let f : ℂ → ℂ := fun z => P (X z)
  have hfU : DifferentiableOn ℂ f (X ⁻¹' frDoms Hm q) :=
    hP.1.comp hXd.differentiableOn fun z hz => hz
  have hUo : IsOpen (X ⁻¹' frDoms Hm q) := hOpen.preimage hXd.continuous
  have h0 : (0 : ℂ) ∈ {z : ℂ | 0 ≤ z.re} := by simp
  have hVo := hUo.connectedComponentIn (x := (0 : ℂ))
  have hHV := (convex_halfSpace_re_ge (0 : ℝ)).isPreconnected.subset_connectedComponentIn h0 hHU
  have hfV : AnalyticOnNhd ℂ f (connectedComponentIn (X ⁻¹' frDoms Hm q) 0) :=
    (hfU.mono (connectedComponentIn_subset _ _)).analyticOnNhd hVo
  have eX0 : X 0 = fun τ => (u τ * x₀ τ : Mt n) := by
    funext τ
    show (1 - (0 : ℂ) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ = u τ * x₀ τ
    rw [zero_smul, sub_zero, one_mul]
  have hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, f z = (fun _ => f 0) z := by
    have hT : Filter.Tendsto (fun s : ℝ => (s : ℂ) * Complex.I) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have hc : Continuous (fun s : ℝ => (s : ℂ) * Complex.I) := by fun_prop
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hs) Complex.I_ne_zero
    apply hT.frequently
    refine Filter.Eventually.frequently (Filter.Eventually.of_forall fun s => ?_)
    have h1 := hInv (fun τ => 1 + (((-s : ℝ) : ℂ) * Complex.I) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ))
      (fun τ => by unfold InZe; exact ⟨-s, rfl⟩) u hu
    have eX : X ((s : ℂ) * Complex.I) =
        fun τ => ((1 + (((-s : ℝ) : ℂ) * Complex.I) • vecMulVec (e τ) (star (e τ) ᵥ* Hm τ)) * u τ * x₀ τ : Mt n) := by
      funext τ
      simp only [X]
      congr 2
      push_cast
      simp only [neg_mul, neg_smul, sub_eq_add_neg]
    show P (X ((s : ℂ) * Complex.I)) = P (X 0)
    rw [eX, eX0]
    exact h1
  have hEq := hfV.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
    isPreconnected_connectedComponentIn (mem_connectedComponentIn (hHU h0)) hfreq
  have ht' : (t : ℂ) ∈ {z : ℂ | 0 ≤ z.re} := by simpa using ht
  have key : f t = f 0 := hEq (hHV ht')
  show f t = _
  rw [key]
  show P (X 0) = _
  rw [eX0]

end GlobalTheory.HolDict
end

