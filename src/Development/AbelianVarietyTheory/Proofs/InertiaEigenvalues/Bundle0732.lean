module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0336
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0688
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0661
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeTransformInvariantUnderFieldAutomorphism
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.SatInvAuto

open Formalism.UG GlobalTheory.SatInd

section Local

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

def diagExp (n m : ℕ) (a : Fin m → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < m then a ⟨i.val, h⟩
  else if h' : n - m ≤ i.val ∧ n - 1 - i.val < m then -(a ⟨n - 1 - i.val, h'.2⟩) else 0

theorem tMat_eq_diag (x : K) (n m : ℕ) (a : Fin m → ℤ) :
    tMat x n m a = Matrix.diagonal fun i => x ^ diagExp n m a i := by
  unfold tMat diagExp
  congr 1
  funext i
  split_ifs <;> simp

theorem diagExp_rev {n m : ℕ} (hm : 2 * m ≤ n) (a : Fin m → ℤ) (i : Fin n) :
    diagExp n m a i.rev = -diagExp n m a i := by
  have hi := i.isLt
  have hr : (i.rev : ℕ) = n - 1 - i := by rw [Fin.val_rev]; omega
  unfold diagExp
  by_cases h1 : (i : ℕ) < m
  · have h2 : ¬ (i.rev : ℕ) < m := by omega
    have h3 : n - m ≤ (i.rev : ℕ) ∧ n - 1 - (i.rev : ℕ) < m := by omega
    rw [dite_eq_right h2, dite_eq_left h3, dite_eq_left h1]
    rw [show (⟨n - 1 - (i.rev : ℕ), h3.2⟩ : Fin m) = ⟨i, h1⟩ from
      Fin.ext (show n - 1 - (i.rev : ℕ) = (i : ℕ) by omega)]
  · by_cases h4 : n - m ≤ (i : ℕ) ∧ n - 1 - (i : ℕ) < m
    · have h2 : (i.rev : ℕ) < m := by omega
      rw [dite_eq_left h2, dite_eq_right h1, dite_eq_left h4, neg_neg]
      rw [show (⟨(i.rev : ℕ), h2⟩ : Fin m) = ⟨n - 1 - i, h4.2⟩ from Fin.ext hr]
    · have h2 : ¬ (i.rev : ℕ) < m := by omega
      have h3 : ¬ (n - m ≤ (i.rev : ℕ) ∧ n - 1 - (i.rev : ℕ) < m) := by omega
      rw [dite_eq_right h2, dite_eq_right h3, dite_eq_right h1, dite_eq_right h4, neg_zero]

theorem div_mem_intL {ϖ x : K} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (hx : x ∈ intL K) (hx' : x⁻¹ ∉ intL K) : x / ϖ ∈ intL K := by
  unfold intL at *
  rw [Valuation.mem_integer_iff] at *
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hx'
    simp
  have hlt : Valued.v x < 1 := lt_of_le_of_ne hx (fun h => hx' (by rw [map_inv₀, h, inv_one]))
  have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [map_div₀, hϖ, ← WithZero.exp_log hv0, ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem map_mul_mat (g : K ≃+* K) {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) :
    (A * B).map g = A.map g * B.map g := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mul_apply, map_sum]

end Local

section Cell

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem cell_guMap (g : K ≃+* K) {σ : K →+* K} (hg : ∀ x, g (σ x) = σ (g x))
    (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {ϖ : K} {q n m : ℕ} (hU : IsUnramInv ϖ σ q)
    (hm : 2 * m ≤ n) (a : Fin m → ℤ) (y : GU σ n)
    (hy : ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
      ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨u, hu, k, hk, hyuk⟩ := hy
  obtain ⟨-, hσv, hσϖ, hϖ, -, -, -⟩ := hU
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
  have hϖint : ϖ ∈ intL K := by
    unfold intL
    rw [Valuation.mem_integer_iff, hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  have hϖinv : ϖ⁻¹ ∉ intL K := by
    unfold intL
    rw [Valuation.mem_integer_iff, map_inv₀, hϖ', ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp]; norm_num
  set c : K := g ϖ / ϖ with hc
  have hgϖ : g ϖ = ϖ * c := by rw [hc]; field_simp
  have hc0 : c ≠ 0 := div_ne_zero ((map_ne_zero g).2 h0) h0
  have hcint : c ∈ intL K := div_mem_intL hϖ' ((hint ϖ).1 hϖint)
    (by rw [← map_inv₀]; exact fun h => hϖinv ((hint _).2 h))
  have hcinv : c⁻¹ ∈ intL K := by
    have h1 : g.symm ϖ / ϖ ∈ intL K := div_mem_intL hϖ' (by rw [hint]; simpa using hϖint)
      (by rw [← map_inv₀, hint]; simpa using hϖinv)
    have h2 := (hint _).1 h1
    rw [map_div₀, RingEquiv.apply_symm_apply] at h2
    rw [hc, inv_div]; exact h2
  have hcv : Valued.v c = 1 := by
    unfold intL at hcint hcinv
    rw [Valuation.mem_integer_iff] at hcint hcinv
    refine le_antisymm hcint ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (c * c⁻¹) := by rw [mul_inv_cancel₀ hc0, map_one]
      _ = Valued.v c * Valued.v c⁻¹ := map_mul _ _ _
      _ ≤ Valued.v c * 1 := mul_le_mul' le_rfl hcinv
      _ = Valued.v c := mul_one _
  have hσc : σ c = c := by rw [hc, map_div₀, hσϖ, ← hg, hσϖ]
  set e : Fin n → K := fun i => c ^ diagExp n m a i with he
  have he0 : ∀ i, e i ≠ 0 := fun i => zpow_ne_zero _ hc0
  obtain ⟨d, hd, hd'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ) e (fun i => by
    simp only [he]; rw [map_zpow₀, hσc, diagExp_rev hm, ← zpow_add₀ hc0, add_neg_cancel, zpow_zero])
  have hdK : d ∈ KU σ n := by
    have hI : Formalism.UG.P.fIwasawaInt (((d : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      intro i j
      rw [hd]
      by_cases hij : i = j
      · subst hij; rw [Matrix.diagonal_apply_eq, he]; simp only; rw [map_zpow₀, hcv, one_zpow]
      · rw [Matrix.diagonal_apply_ne _ hij, map_zero]; exact zero_le'
    have := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ d) hI
    have e' : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ d) = d := Subtype.ext (Units.ext rfl)
    rwa [e'] at this
  have hk1 : guMap g hg n k ∈ KU σ n := (mem_KU_iff_guMap g hg hint k).1 hk
  refine ⟨d * guMap g hg n u * d⁻¹, ?_, d * guMap g hg n k, (KU σ n).mul_mem hdK hk1, ?_⟩
  · refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · simp only [Subgroup.coe_mul, Units.val_mul, hd, hd', guMap_val, Matrix.mul_diagonal,
        Matrix.diagonal_mul, Matrix.map_apply]
      rw [hu.1 i j hij, map_zero, mul_zero, zero_mul]
    · simp only [Subgroup.coe_mul, Units.val_mul, hd, hd', guMap_val, Matrix.mul_diagonal,
        Matrix.diagonal_mul, Matrix.map_apply]
      rw [hu.2 i, map_one, mul_one, mul_inv_cancel₀ (he0 i)]
  · rw [guMap_val, hyuk, map_mul_mat, map_mul_mat]
    simp only [Subgroup.coe_mul, Units.val_mul, hd, hd', guMap_val]
    rw [tMat_eq_diag, Matrix.diagonal_map (map_zero _)]
    have hD : (Matrix.diagonal fun i => g (ϖ ^ diagExp n m a i)) =
        Matrix.diagonal (fun i => ϖ ^ diagExp n m a i) * Matrix.diagonal e := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rw [map_zpow₀, hgϖ, mul_zpow]
    have hinv : Matrix.diagonal (fun i => (e i)⁻¹) * Matrix.diagonal e = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact inv_mul_cancel₀ (he0 i)
    rw [hD]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal fun i => (e i)⁻¹) (Matrix.diagonal e), hinv, Matrix.one_mul]

end Cell


open Classical in
theorem satU_guMap_self : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ : K →+* K} (hg : ∀ x, g (σ x) = σ (g x)), (∀ x, x ∈ Formalism.UG.intL K ↔ g x ∈ Formalism.UG.intL K) → ∀ (ϖ : K) (q n m : ℕ), Formalism.UG.IsUnramInv ϖ σ q → 2 * m ≤ n → n ≤ 2 * m + 1 → ∀ h : Formalism.UG.GU σ n → ℂ, Formalism.UG.IsBiInv (Formalism.UG.KU σ n) h → ∀ α : Fin m → ℂ, Formalism.UG.SatU ϖ q (fun y => h (GlobalTheory.SatInd.guMap g hg n y)) α = Formalism.UG.SatU ϖ q h α := by
  intro K _ _ g σ hg hint ϖ q n m hU hm1 _ h hbi α
  have hg' : ∀ x, g.symm (σ x) = σ (g.symm x) := by
    intro x; apply g.injective; rw [hg]; simp
  have hint' : ∀ x, x ∈ intL K ↔ g.symm x ∈ intL K := by
    intro x; rw [hint (g.symm x)]; simp
  refine satU_guMap g hg hint ϖ ϖ q n m h hbi
    (fun a y => ⟨cell_guMap g hg hint hU hm1 a y, fun hy => ?_⟩) α
  have := cell_guMap g.symm hg' hint' hU hm1 a (guMap g hg n y) hy
  rwa [guMap_symm_comp g hg hg' y] at this

end GlobalTheory.SatInvAuto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSegmentRepLengthOneUnramified
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SphSeg

theorem isSubquotient_prodIrr_prinSeries {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = h)
    (μ : Fin h → kˣ →* ℂˣ) (hμ : ∀ a, IsSmoothChar (μ a)) (hx : ∀ a, x a = IrrGL.ofChar (μ a) (hμ a)) :
    IsSubquotient (prodIrr x hd) (prinSeries μ) := by
  obtain rfl : x = fun a => IrrGL.ofChar (μ a) (hμ a) := funext hx
  let φ := multiProdEquiv (stdBlocks (fun a => (IrrGL.ofChar (μ a) (hμ a)).1) hd) fun a =>
    (LocGL.equivRep (IrrRep.det (Fin 1) (μ a) (hμ a))).symm
  exact (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective).trans
    (PermPrin.isSubquotient_multiProd_prinSeries _ μ)

end GlobalTheory.SphSeg

namespace GlobalTheory.SphSeg

theorem len_eq_one_and_isUnramChar : LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing →
    GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (Δ : Segment k) (y : IrrGL (k := k)), IsLSeg Δ y.rep → IsSpherical y.rep →
    Δ.len = 1 ∧ Δ.first.IsUnramChar := by
  intro hLM hSC hZP hGL hBZ k _ _ _ _ _ Δ y hL hS
  obtain ⟨N, c⟩ := y
  obtain ⟨hd, hc⟩ := id hL
  have hsub : IsSubquotient c.rep.ρ (prodIrr Δ.term hd) := hc.isSubquotient
  have hsph := GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k Δ.len N Δ.term hd _ c.rep.ρ hsub hS
  have h0 : Δ.term ⟨0, Δ.len_pos⟩ = Δ.first := by simp [Segment.term]
  have key : ∀ x z : IrrGL (k := k), x = z → IsSpherical x.rep → IsSpherical z.rep := by
    rintro _ _ rfl h; exact h
  have hU : Δ.first.IsUnramChar :=
    GlobalTheory.T.isUnramifiedChar_of_cuspidal_spherical hGL hBZ hZP k Δ.first Δ.isCusp_first (key _ _ h0 (hsph _))
  refine ⟨?_, hU⟩
  obtain ⟨μ, hμ, hfirst⟩ := hU
  have hμs := isSmoothChar_of_isUnram hμ
  have hterm : ∀ a, Δ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _)) :=
    fun a => by simp only [Segment.term, IrrGL.nu, hfirst, IrrGL.tw_ofChar]
  have hd1 : Δ.d = 1 := congrArg Sigma.fst hfirst
  have hN : N = Δ.len := by
    have h2 : ∑ a, (Δ.term a).1 = N := hd
    rw [Segment.sum_term_fst, Segment.deg, hd1, mul_one] at h2
    exact h2.symm
  subst hN

  let Γ := Segment.ofChar μ hμs Δ.len Δ.len_pos
  have hterm' : ∀ a, Γ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _)) :=
    fun a => by
      show (IrrGL.ofChar μ hμs).nu _ = _
      simp only [IrrGL.nu, IrrGL.tw_ofChar]
  have hd' : ∑ a, (Γ.term a).1 = Δ.len := (Segment.sum_term_fst _).trans (mul_one _)
  have hP := isSubquotient_prodIrr_prinSeries Δ.term hd _ _ hterm
  have hP' := isSubquotient_prodIrr_prinSeries Γ.term hd' _ _ hterm'
  let χ' := μ * absPow k (((Δ.len : ℂ) - 1) / 2)
  have hu' : IsUnram χ' := fun x hx => by
    rw [MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]
  have hχs : IsSmoothChar χ' := isSmoothChar_of_isUnram hu'
  obtain ⟨f, hf⟩ := embeds_detRep_segment hμs Δ.len_pos hd'

  obtain ⟨ϖ, hϖ⟩ := LocGL.exists_uniformizer k
  have hu : ∀ i : Fin Δ.len, IsUnram (μ * absPow k ((i : ℕ) : ℂ)) := fun i x hx => by
    rw [MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]
  let α : Fin Δ.len → ℂˣ := fun i => (μ * absPow k ((i : ℕ) : ℂ)) ϖ
  have heq : (fun i => unrChar k (α i)) = fun i : Fin Δ.len => μ * absPow k ((i : ℕ) : ℂ) :=
    funext fun i => (eq_unrChar (hu i) hϖ).symm
  have hA : HasSatake c.rep.ρ α := ⟨c.rep.irr, hS, by rw [heq]; exact hsub.trans hP⟩
  have hB : HasSatake (IrrRep.det (Fin Δ.len) χ' hχs).ρ α :=
    ⟨(IrrRep.det (Fin Δ.len) χ' hχs).irr, isSpherical_detRep hu',
      by rw [heq]; exact (IsSubquotient.of_injective f hf).trans hP'⟩
  obtain ⟨E⟩ := _root_.GlobalTheory.SmGL.SphUniq.equiv_of_hasSatake hBZ k Δ.len α c.rep (IrrRep.det (Fin Δ.len) χ' hχs) hA hB
  have hL2 := (_root_.GlobalTheory.LocGL.isL_det hSC k Δ.len χ' hχs).of_equiv E.symm
  have hL1 := hL.isL
  have hm := (hLM k).1 _ _ ⟨Δ.len, c⟩ hL1 hL2
  have := congrArg Multiset.card hm
  simpa using this.symm

end GlobalTheory.SphSeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlacesInjective
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceInjectivity

theorem eq_or_conj_of_comap_eq {L : Type} [Field L] [NumberField L] [IsCMField L]
    (P P' : HeightOneSpectrum (𝓞 L))
    (h : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) =
      P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L))) :
    P' = P ∨ ∀ x : 𝓞 L, x ∈ P'.asIdeal ↔ IsCMField.ringOfIntegersComplexConj L x ∈ P.asIdeal := by
  set σ : 𝓞 L →+* 𝓞 L := (IsCMField.ringOfIntegersComplexConj L : 𝓞 L →+* 𝓞 L) with hσ
  have key : ∀ x ∈ P'.asIdeal, x ∈ P.asIdeal ∨ x ∈ P.asIdeal.comap σ := by
    intro x hx
    have hfix : IsCMField.complexConj L ((x * σ x : 𝓞 L) : L) = ((x * σ x : 𝓞 L) : L) := by
      simp [hσ, IsCMField.coe_ringOfIntegersComplexConj, mul_comm]
    obtain ⟨y, hy⟩ := (IsCMField.RingOfIntegers.complexConj_eq_self_iff (K := L) (x * σ x)).1 hfix
    have hy' : algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) y = x * σ x := RingOfIntegers.ext hy
    have h1 : y ∈ P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) := by
      rw [Ideal.mem_comap, hy']; exact P'.asIdeal.mul_mem_right _ hx
    rw [← h, Ideal.mem_comap, hy'] at h1
    rcases P.isPrime.mem_or_mem h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (by rw [Ideal.mem_comap]; exact h2)
  have hsub : (P'.asIdeal : Set (𝓞 L)) ⊆ (P.asIdeal : Set (𝓞 L)) ∪ (P.asIdeal.comap σ : Set (𝓞 L)) :=
    fun x hx => key x hx
  have hmax : P'.asIdeal.IsMaximal := P'.isMaximal
  rcases Ideal.subset_union.1 hsub with h3 | h3
  · left
    exact HeightOneSpectrum.ext (hmax.eq_of_le P.isPrime.ne_top h3)
  · right
    have hpr : (P.asIdeal.comap σ).IsPrime := Ideal.comap_isPrime σ P.asIdeal
    have he := hmax.eq_of_le hpr.ne_top h3
    intro x
    rw [he, Ideal.mem_comap]
    rfl

end GlobalTheory.PlaceInjectivity

namespace GlobalTheory.PlaceInjectivity

theorem not_mem_of_coprime {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (w : HeightOneSpectrum (𝓞 E)) (h1 : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) :
    ((q : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  have hco : IsCoprime ((p : ℤ)) ((q : ℤ)) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd_natCast_natCast] using (Nat.coprime_primes hp hq).mpr hpq)
  have hco' : IsCoprime ((p : ℕ) : 𝓞 E) ((q : ℕ) : 𝓞 E) := by
    simpa using hco.map (Int.castRingHom (𝓞 E))
  exact Ideal.IsPrime.notMem_of_isCoprime_of_mem hco' h1

end GlobalTheory.PlaceInjectivity

namespace GlobalTheory.PlaceInj

theorem splitPlace_v_injective : ∀ (D : D7) (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E), (∀ k v, (s k v).w = D.naut.plGw k v) → Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v) := by
  intro D s hs ⟨k, v⟩ ⟨k', v'⟩ heq
  simp only at heq
  have hc : (D.naut.plGw k v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      (D.naut.plGw k' v').asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
    rw [← hs, ← hs, (s k v).w_under, (s k' v').w_under, heq]
  by_cases hk : k = k'
  · subst hk
    rcases GlobalTheory.PlaceInjectivity.eq_or_conj_of_comap_eq _ _ hc with h | h
    · have := D.naut.plGw_inj k h.symm
      subst this
      rfl
    · exfalso
      apply D.naut.plGw_nconj k v v'
      intro x y hxy
      have hconj : (IsCMField.ringOfIntegersComplexConj D.host.E y : D.host.E) = (x : D.host.E) := by
        rw [IsCMField.coe_ringOfIntegersComplexConj, hxy]
        apply D.host.φ₀.injective
        rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
        simp
      rw [h y, RingOfIntegers.ext hconj]
  · exfalso
    have hg : D.host.g k ≠ D.host.g k' := by
      fin_cases k <;> fin_cases k' <;> simp_all [D.host.g_ne, D.host.g_ne.symm]
    have h1 : ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈
        (D.naut.plGw k v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
      rw [Ideal.mem_comap, map_natCast]; exact D.naut.plGw_over k v
    rw [hc, Ideal.mem_comap, map_natCast] at h1
    exact GlobalTheory.PlaceInjectivity.not_mem_of_coprime (D.host.g_prime k') (D.host.g_prime k) hg.symm _
      (D.naut.plGw_over k' v') h1

end GlobalTheory.PlaceInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivOutsidePlaceMemDefiniteUnitaryLocalPoints
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.LocMemTransfer

theorem mem_locU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ y : GAf L n, TrivOutside {v} y → F.j y ∈ locU n w := by
  intro L _ _ _ n F v w hw y hy
  obtain rfl : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hw
  refine Subgroup.mem_inf.2 ⟨F.fin y, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩
  ext s t
  rw [F.loc y u s t]
  have h := hy (u.under (𝓞 (maximalRealSubfield L))) (by simpa using hu)
  have h0 : compAt L (u.under (𝓞 (maximalRealSubfield L)))
      ((y.1 : Matrix (Fin n) (Fin n) (AL L)) s t - (1 : Matrix (Fin n) (Fin n) (AL L)) s t) = 0 := by
    have hst := congrFun (congrFun h s) t
    rw [Matrix.map_apply] at hst
    rw [map_sub, hst]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have h1 := (GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (ι := F.κ.toRingHom) (GlobalTheory.UnramDict.kappa_tmul F)
    (u.under (𝓞 (maximalRealSubfield L))) _).1 h0 u rfl
  rw [map_sub] at h1
  change F.κ _ u - F.κ _ u = 0 at h1
  rw [sub_eq_zero] at h1
  rw [h1]
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp
  rfl

end GlobalTheory.LocMemTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffTendsto
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.TypeRec.TwistInert

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

section Val

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem valuation_lt_one_iff_tendsto (x : K) :
    valuation K x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  refine ⟨GlobalTheory.LocalTraceSum.tendsto_pow, fun h => ?_⟩
  have hO := GlobalTheory.LocalTraceSum.isOpen_lt (K := K) 1
  obtain ⟨n, hn⟩ := (h.eventually (hO.mem_nhds (by simp))).exists
  by_contra hx
  have h1 : 1 ≤ valuation K x := not_lt.1 hx
  have h2 : 1 ≤ valuation K (x ^ n) := by rw [map_pow]; exact one_le_pow₀ h1
  exact absurd hn (not_lt.2 h2)

theorem valuation_lt_one_map (f : K →+* L) (hf : Continuous f) {x : K} (hx : valuation K x < 1) :
    valuation L (f x) < 1 := by
  rw [valuation_lt_one_iff_tendsto] at hx ⊢
  simpa [Function.comp_def, map_pow] using (hf.tendsto 0).comp hx

end Val

def twistEquiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) (χ : G →* ℂˣ) :
    (twist π χ).Equiv (twist σ χ) :=
  Representation.Equiv.mk φ.toLinearEquiv fun g => LinearMap.ext fun x => by
    have e := LinearMap.congr_fun (φ.isIntertwining' g) x
    simp only [LinearMap.comp_apply] at e
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, twist_apply, map_smul]
    congr 1

end GlobalTheory.TypeRec.TwistInert
end
end

