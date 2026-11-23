module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZMatEInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LinearIndependentSingleAdd
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open scoped Matrix ComplexConjugate

namespace GlobalTheory.CuspExist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_congr_diagonal (H : GlobalTheory.Published.Landherr) (X : Data E r) (k : Fin r) :
    ∃ (d : E) (P : Matrix (Fin r) (Fin r) E), P.det ≠ 0 ∧
      Matrix.diagonal (fun a : Fin r => (if (a : ℕ) < X.p0 then (1 : E) else -1) *
        (if a = k then d else 1)) = Pᵀ * X.Gm * P.map cc := by
  classical
  set s : Fin r → E := fun a => if (a : ℕ) < X.p0 then (1 : E) else -1 with hs
  have hs0 : ∀ a, s a ≠ 0 := fun a => by
    simp only [hs]; split_ifs <;> simp
  have hscc : ∀ a, cc (s a) = s a := fun a => by
    simp only [hs]; split_ifs <;> simp [cc]
  have hsτ : ∀ (τ : E →+* ℂ) a, τ (s a) = ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := fun τ a => by
    simp only [hs, sgn]; split_ifs <;> simp
  have hS0 : (Matrix.diagonal s).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hs0 a
  have hSh : ∀ a b, cc (Matrix.diagonal s a b) = Matrix.diagonal s b a := by
    intro a b
    by_cases h : a = b
    · subst h; simpa using hscc a
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]; simp [cc]
  set d : E := X.Gm.det / (Matrix.diagonal s).det with hd
  have hd0 : d ≠ 0 := div_ne_zero X.Gm_det hS0
  have hdcc : cc d = d := by
    have h1 := GlobalTheory.Published.cc_det_of_herm X.Gm_herm
    have h2 := GlobalTheory.Published.cc_det_of_herm hSh
    unfold cc at h1 h2 ⊢
    rw [hd, map_div₀, h1, h2]
  have hdet : (Matrix.diagonal fun a : Fin r => s a * (if a = k then d else 1)).det = X.Gm.det := by
    rw [Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ _),
      ← Matrix.det_diagonal, hd]
    field_simp
  refine ⟨d, GlobalTheory.Published.Landherr.of_signature H X.Gm_herm ?_ X.Gm_det (hdet ▸ X.Gm_det)
    (X.Ψ : Set (E →+* ℂ)) (fun τ => ?_) (fun τ hτ => ⟨X.p0, X.signature ⟨τ, hτ⟩, ?_⟩) ⟨1, ?_⟩⟩
  · intro a b
    by_cases h : a = b
    · subst h
      have h1 := hscc a
      unfold cc at h1 hdcc ⊢
      rw [Matrix.diagonal_apply_eq, map_mul, h1]
      congr 1
      split_ifs
      · exact hdcc
      · exact map_one _
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]; simp [cc]
  · by_cases h : ComplexEmbedding.conjugate τ ∈ X.Ψ
    · exact Or.inr h
    · exact Or.inl ((X.cmType τ).mpr h)
  · obtain ⟨Q, hQ, hg⟩ := X.signature ⟨τ, hτ⟩
    have hpos : 0 < (τ d).re := by
      refine GlobalTheory.Published.Landherr.re_det_div_pos X.Gm_det τ ⟨Q, hQ, ?_⟩
      rw [← GlobalTheory.Published.gram_eq, hg, Matrix.diagonal_map (map_zero τ)]
      simp only [hsτ]
    have hre : ((τ d).re : ℂ) = τ d := by
      rw [← Complex.conj_eq_iff_re, ← GlobalTheory.Published.embedding_cc, hdcc]
    set t : ℝ := (Real.sqrt (τ d).re)⁻¹ with ht
    have ht0 : t ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hpos).ne'
    have htt : (t : ℂ) * τ d * t = 1 := by
      rw [← hre, mul_right_comm, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ht, ← mul_inv,
        Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]
    refine ⟨Matrix.diagonal fun a => if a = k then (t : ℂ) else 1, ?_, ?_⟩
    · rw [Matrix.det_diagonal, Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]
      exact_mod_cast ht0
    · rw [GlobalTheory.Published.gram_eq, Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero τ),
        Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      rw [map_mul, hsτ]
      split_ifs
      · rw [Complex.conj_ofReal]
        linear_combination ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * htt
      · simp
  · rw [hdet, div_self X.Gm_det]; simp [cc]


omit [NumberField E] [IsCMField E] in
theorem linearIndependent_single_add {ρ : ℕ} {i j : Fin ρ → Fin r} (hi : Function.Injective i)
    (hij : ∀ a b, i a ≠ j b) :
    LinearIndependent E fun a => (Pi.single (i a) 1 + Pi.single (j a) 1 : Fin r → E) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have := congrFun hg (i a)
  simpa [Finset.sum_apply, Pi.single_apply, hij, hi.eq_iff] using this

theorem herm_diagonal_single_add {ρ : ℕ} {i j : Fin ρ → Fin r} (hi : Function.Injective i)
    (hj : Function.Injective j) (hij : ∀ a b, i a ≠ j b) (g : Fin r → E)
    (hg : ∀ a, g (i a) + g (j a) = 0) (a b : Fin ρ) :
    herm (Matrix.diagonal g) (Pi.single (i a) 1 + Pi.single (j a) 1)
      (Pi.single (i b) 1 + Pi.single (j b) 1) = 0 := by
  classical
  have hji : ∀ a b, j a ≠ i b := fun a b => (hij b a).symm
  rw [GlobalTheory.Published.LandherrSt.herm_eq, add_dotProduct, single_dotProduct, single_dotProduct,
    Matrix.mulVec_diagonal, Matrix.mulVec_diagonal]
  by_cases h : a = b
  · subst h
    simpa [cc, Pi.single_apply, hij, hji] using hg a
  · simp [cc, hij, hji, hi.eq_iff, hj.eq_iff, h]

theorem nonempty_cuspFD : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r), ρ ≤ X.p0 → ρ + X.p0 ≤ r → 2 * ρ < r → Nonempty (FJ.CuspFD X ρ) := by
  intro HN E _ _ _ r ρ X h1 h2 h3
  classical
  have H := GlobalTheory.Published.landherr_of_landherrSt (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt HN)
  obtain ⟨k, hk⟩ : ∃ k : Fin r, (k : ℕ) + ρ < X.p0 ∨ X.p0 + ρ ≤ k := by
    by_cases h : ρ < X.p0
    · exact ⟨⟨0, by omega⟩, Or.inl (by simpa using h)⟩
    · exact ⟨⟨r - 1, by omega⟩, Or.inr (by simp only; omega)⟩
  obtain ⟨d, P, hP, hG⟩ := exists_congr_diagonal H X k
  let i : Fin ρ → Fin r := fun a => ⟨X.p0 - 1 - a, by have := a.2; omega⟩
  let j : Fin ρ → Fin r := fun a => ⟨X.p0 + a, by have := a.2; omega⟩
  have hi : Function.Injective i := fun a b h => by
    have := a.2; have := b.2
    simp only [i, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  have hj : Function.Injective j := fun a b h => by
    simp only [j, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  have hij : ∀ a b, i a ≠ j b := fun a b h => by
    have := a.2
    simp only [i, j, Fin.mk.injEq] at h
    omega
  refine ⟨⟨fun a => P *ᵥ (Pi.single (i a) 1 + Pi.single (j a) 1), ?_, fun a b => ?_⟩⟩
  · refine (linearIndependent_single_add (E := E) hi hij).map' (Matrix.toLin' P) ?_
    rw [LinearMap.ker_eq_bot]
    exact Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr hP))
  · rw [GlobalTheory.Published.LandherrSt.herm_mulVec, ← hG]
    refine herm_diagonal_single_add hi hj hij _ (fun c => ?_) a b
    have := c.2
    have e1 : i c ≠ k := fun h => by
      have := congrArg Fin.val h
      simp only [i] at this
      omega
    have e2 : j c ≠ k := fun h => by
      have := congrArg Fin.val h
      simp only [j] at this
      omega
    have e3 : (i c : ℕ) < X.p0 := by simp only [i]; omega
    have e4 : ¬ (j c : ℕ) < X.p0 := by simp only [j]; omega
    simp only [if_pos e3, if_neg e4, if_neg e1, if_neg e2]
    ring

end GlobalTheory.CuspExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SkewMatrixMultipleInLattice
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem exists_pos_nsmul_mem (X : Data E r) (v : Fin r → E) : ∃ n : ℕ, 0 < n ∧ n • v ∈ X.Λ := by
  have hv : v ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by rw [X.Λ_span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨n, hn, hy⟩ := hy
    refine ⟨m * n, mul_pos hm hn, ?_⟩
    have : (m * n) • (x + y) = n • m • x + m • n • y := by
      rw [smul_add, smul_smul, smul_smul, mul_comm n m]
    rw [this]
    exact X.Λ.add_mem (nsmul_mem hx _) (nsmul_mem hy _)
  | smul c x _ hx =>
    obtain ⟨m, hm, hx⟩ := hx
    have halg : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
    have hki' : IsIntegral ℤ ((k * k) • c) := by
      rw [mul_smul]; exact hki.smul k
    refine ⟨(k.natAbs * k.natAbs) * m, mul_pos (mul_pos (Int.natAbs_pos.2 hk) (Int.natAbs_pos.2 hk)) hm, ?_⟩
    have h1 := X.Λ.smul_mem (⟨(k * k) • c, hki'⟩ : 𝓞 E) hx
    have h2 : ((k.natAbs * k.natAbs : ℕ) : E) = ((k * k : ℤ) : E) := by
      rw [← Int.natAbs_mul_self, Int.cast_natCast]
    convert h1 using 1
    funext i
    show ((k.natAbs * k.natAbs) * m) • (c * x i) = ((k * k) • c) * (m • x i)
    rw [nsmul_eq_mul, nsmul_eq_mul, zsmul_eq_mul, Nat.cast_mul, h2]
    ring

theorem exists_pos_nsmul_mulVec_mem (X : Data E r) (N : Matrix (Fin r) (Fin r) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ x ∈ X.Λ, d • (N *ᵥ x) ∈ X.Λ := by
  classical
  obtain ⟨s, hs⟩ := X.Λ_fg
  choose n hn0 hn using fun v => exists_pos_nsmul_mem X (N *ᵥ v)
  refine ⟨∏ v ∈ s, n v, Finset.prod_pos fun v _ => hn0 v, fun x hx => ?_⟩
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul s n hx, mul_smul]
    exact nsmul_mem (hn x) _
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, smul_add]; exact X.Λ.add_mem hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul, smul_comm]; exact X.Λ.smul_mem c hx

theorem zMatE_nsmul_mulVec (X : Data E r) (e : Fin ρ → Fin r → E) (β : Matrix (Fin ρ) (Fin ρ) E)
    (n : ℕ) (v : Fin r → E) :
    FJ.zMatE X e (n • β) *ᵥ v = v + n • ((FJ.zMatE X e β - 1) *ᵥ v) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, zMatE_mulVec, zMatE_mulVec, add_sub_cancel_left,
    Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← smul_assoc, Finset.smul_sum]
  simp only [Matrix.smul_apply, smul_mul_assoc]

theorem isSkew_nsmul {β : Matrix (Fin ρ) (Fin ρ) E} (hβ : FJ.IsSkew β) (n : ℕ) :
    FJ.IsSkew (n • β) := by
  intro a b
  have h : cc ((n : E)) = n := by simp [cc]
  rw [Matrix.smul_apply, Matrix.smul_apply, nsmul_eq_mul, nsmul_eq_mul, cc_mul', h, hβ, mul_neg]

noncomputable def zUnit (X : Data E r) (cu : FJ.CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E) : GL (Fin r) E :=
  ⟨FJ.zMatE X cu.e β, FJ.zMatE X cu.e (-β), by rw [← zMatE_add, add_neg_cancel, zMatE_zero],
    by rw [← zMatE_add, neg_add_cancel, zMatE_zero]⟩

theorem zUnit_add (X : Data E r) (cu : FJ.CuspFD X ρ) (β β' : Matrix (Fin ρ) (Fin ρ) E) :
    zUnit X cu (β + β') = zUnit X cu β * zUnit X cu β' :=
  Units.ext (zMatE_add X cu β β')

theorem exists_isUStab_zUnit (X : Data E r) (cu : FJ.CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E)
    (hβ : FJ.IsSkew β) : ∃ d : ℕ, 0 < d ∧ ∀ j : ℕ, IsUStab X.Gm X.Λ (zUnit X cu ((j * d) • β)) := by
  obtain ⟨d, hd, h⟩ := exists_pos_nsmul_mulVec_mem X (FJ.zMatE X cu.e β - 1)
  obtain ⟨d', hd', h'⟩ := exists_pos_nsmul_mulVec_mem X (FJ.zMatE X cu.e (-β) - 1)
  refine ⟨d * d', mul_pos hd hd', fun j => ⟨zMatE_unitary X cu _ (isSkew_nsmul hβ _), fun x => ?_⟩⟩
  show x ∈ X.Λ ↔ FJ.zMatE X cu.e ((j * (d * d')) • β) *ᵥ x ∈ X.Λ
  constructor
  · intro hx
    rw [zMatE_nsmul_mulVec, mul_comm d, ← mul_assoc, mul_smul]
    exact X.Λ.add_mem hx (nsmul_mem (h x hx) _)
  · intro hx
    have h1 : FJ.zMatE X cu.e ((j * (d * d')) • -β) *ᵥ (FJ.zMatE X cu.e ((j * (d * d')) • β) *ᵥ x)
        ∈ X.Λ := by
      rw [zMatE_nsmul_mulVec X cu.e (-β), ← mul_assoc, mul_smul (j * d) d' (_ *ᵥ _)]
      rw [← mul_assoc] at hx
      exact X.Λ.add_mem hx (nsmul_mem (h' _ hx) _)
    rwa [Matrix.mulVec_mulVec, ← zMatE_add, smul_neg, neg_add_cancel, zMatE_zero,
      Matrix.one_mulVec] at h1

theorem exists_nsmul_mem_zGam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), FJ.IsSkew β → ∃ n : ℕ, 0 < n ∧ n • β ∈ FJ.zGam X cu := by
  intro E _ _ _ r ρ X cu β hβ
  obtain ⟨d, hd, h⟩ := exists_isUStab_zUnit X cu β hβ
  obtain ⟨S, hS⟩ := X.Γ_index
  choose s hsS hs using fun j => hS _ (h j)
  have key : ∀ i j, i < j → s i = s j → ∃ n : ℕ, 0 < n ∧ n • β ∈ FJ.zGam X cu := by
    intro i j hij e
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
    refine ⟨(k + 1) * d, mul_pos k.succ_pos hd, isSkew_nsmul hβ _,
      zUnit X cu (((k + 1) * d) • β), ?_, rfl⟩
    have h1 := X.Γ.mul_mem (X.Γ.inv_mem (hs i)) (hs (i + k + 1))
    rw [← e, add_assoc, add_mul, add_smul, zUnit_add, ← mul_assoc (s i)⁻¹, inv_mul_cancel_left] at h1
    exact h1
  obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite (fun j => (⟨s j, hsS j⟩ : S))
  have e' : s i = s j := congrArg Subtype.val e
  rcases lt_or_gt_of_ne hij with h1 | h1
  · exact key i j h1 e'
  · exact key j i h1 e'.symm

end GlobalTheory.CuspCentre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SpanCuspCentreArithmeticGroupFg
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

noncomputable def displ (X : Data E r) (cu : FJ.CuspFD X ρ) (s : Finset (Fin r → E)) :
    Matrix (Fin ρ) (Fin ρ) E →+ (s → Fin r → E) where
  toFun β := fun v => FJ.zMatE X cu.e β *ᵥ v.1 - v.1
  map_zero' := by
    funext v
    simp [zMatE_zero]
  map_add' β β' := by
    funext v
    simp only [zMatE_mulVec, Pi.add_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib,
      add_smul]
    abel

theorem displ_injective (X : Data E r) (cu : FJ.CuspFD X ρ) (s : Finset (Fin r → E))
    (hs : Submodule.span E (s : Set (Fin r → E)) = ⊤) : Function.Injective (displ X cu s) := by
  intro β β' h
  apply zMatE_injective X cu
  apply Matrix.toLin'.injective
  refine LinearMap.ext_on hs fun v hv => ?_
  have h1 : FJ.zMatE X cu.e β *ᵥ v - v = FJ.zMatE X cu.e β' *ᵥ v - v := congrFun h ⟨v, hv⟩
  simpa [Matrix.toLin'_apply] using h1

theorem span_zGam_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ), (Submodule.span ℤ (FJ.zGam X cu)).FG := by
  intro E _ _ _ r ρ X cu
  obtain ⟨s, hs⟩ := X.Λ_fg
  have hsE : Submodule.span E (s : Set (Fin r → E)) = ⊤ := by
    rw [← X.Λ_span, ← hs, Submodule.span_span_of_tower]
  have hΛ : (X.Λ.restrictScalars ℤ).FG := by
    have : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.2 X.Λ_fg
    have h2 : Module.Finite ℤ X.Λ := Module.Finite.trans (𝓞 E) X.Λ
    exact Module.Finite.iff_fg.1 h2
  have hN : (Submodule.pi Set.univ fun _ : s => X.Λ.restrictScalars ℤ).FG :=
    Submodule.fg_pi fun _ => hΛ
  refine Submodule.fg_of_fg_map_injective (displ X cu s).toIntLinearMap
    (displ_injective X cu s hsE) (hN.of_le ?_)
  rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
  rintro β ⟨-, γ, hγ, e⟩ v -
  have hv : v.1 ∈ X.Λ := hs ▸ Submodule.subset_span v.2
  change FJ.zMatE X cu.e β *ᵥ v.1 - v.1 ∈ X.Λ
  rw [← e]
  exact X.Λ.sub_mem (((X.Γ_stab γ hγ).2 _).1 hv) hv

end GlobalTheory.CuspCentre
end

