module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBigCellCoordinateJacobianVerticalChangesEqOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.LogPole.VertDet

theorem det_eq_one_of_key {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] (A : Matrix ι ι R) (k : ι → ℕ)
    (h : ∀ a b, a ≠ b → k a ≤ k b → A a b = 0) (hd : ∀ a, A a a = 1) : A.det = 1 := by
  rw [Matrix.det_apply, Finset.sum_eq_single 1]
  · simp [hd]
  · intro s _ hs
    obtain ⟨i, hi, hk⟩ : ∃ i, s i ≠ i ∧ k (s i) ≤ k i := by
      by_contra hc
      push_neg at hc
      obtain ⟨i₀, hi₀⟩ : ∃ i, s i ≠ i := by
        by_contra h0
        push_neg at h0
        exact hs (Equiv.ext h0)
      have hlt : ∑ i, k i < ∑ i, k (s i) := by
        refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, Finset.mem_univ _, hc i₀ hi₀⟩
        by_cases e : s i = i
        · rw [e]
        · exact (hc i e).le
      rw [Equiv.sum_comp s k] at hlt
      exact lt_irrefl _ hlt
    rw [Finset.prod_eq_zero (f := fun j => A (s j) j) (Finset.mem_univ i) (h _ _ hi hk), smul_zero]
  · intro h1
    exact absurd (Finset.mem_univ _) h1

theorem snd_unip_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {K : Type} [Field K] (N : GlobalTheory.FlagTan.FIx Dw → K) (σ : E →+* ℂ)
    (M : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K) (p q : Fin (Dw.mult σ)) :
    ((GlobalTheory.FlagTan.unip K N σ * M.map (fun r => (TrivSqZeroExt.inl r : DualNumber K))) p q).snd
      = ∑ r, N (some ⟨σ, p, r⟩) * M r q := by
  rw [Matrix.mul_apply, TrivSqZeroExt.snd_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [GlobalTheory.FlagTan.unip, TrivSqZeroExt.snd_mul, mul_comm]

theorem det_vert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K : Type) [Field K] (M : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K), (∀ σ i j, j < i → M σ i j = 0) → (∀ σ i, M σ i i = 1) → (Matrix.of fun a b : VIx Dw => ((GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) a.1 * (M a.1).map (fun r => (TrivSqZeroExt.inl r : DualNumber K))) a.2.1.1 a.2.1.2).snd).det = 1 := by
  intro E _ _ _ H Dw K _ M hM hM1
  refine det_eq_one_of_key _ (fun a => (a.2.1.2 : ℕ)) ?_ ?_
  · rintro ⟨σ, ⟨p, q⟩, hpq⟩ ⟨τ, ⟨i, j⟩, hij⟩ hne hk
    rw [Matrix.of_apply, snd_unip_mul]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases e : (some ⟨σ, p, r⟩ : GlobalTheory.FlagTan.FIx Dw) = GlobalTheory.FlagTan.VIx.toF ⟨τ, ⟨(i, j), hij⟩⟩
    · obtain ⟨rfl, e'⟩ := Sigma.mk.inj_iff.1 (Option.some.inj e)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq e')
      have hlt : q < r := lt_of_le_of_ne hk (by rintro rfl; exact hne rfl)
      rw [hM _ _ _ hlt, mul_zero]
    · rw [Pi.single_eq_of_ne e, zero_mul]
  · rintro ⟨σ, ⟨p, q⟩, hpq⟩
    rw [Matrix.of_apply, snd_unip_mul, Finset.sum_eq_single q]
    · rw [hM1, mul_one]
      exact Pi.single_eq_same _ _
    · intro r _ hr
      rw [Pi.single_eq_of_ne, zero_mul]
      intro e
      obtain ⟨-, e'⟩ := Sigma.mk.inj_iff.1 (Option.some.inj e)
      exact hr (Prod.mk.inj (eq_of_heq e')).2
    · intro h1
      exact absurd (Finset.mem_univ _) h1

end GlobalTheory.LogPole.VertDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFlagTangentConjugateMatrixChangeEqOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.KSChgDet

theorem ksChg_single_eq_blockDiagonal' {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (K : Type) [Field K] (Φ : Finset (E →+* ℂ))
    (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K) (k l : HIx Dw Φ) :
    FlagTan.ksChg Φ g ((Pi.single l 1 : HIx Dw Φ → K)) k =
      Matrix.blockDiagonal' (fun τ : Φ => Matrix.kroneckerMap (· * ·)
        (g (conjEmb τ.1)).transpose (g τ.1).transpose) k l := by
  obtain ⟨τ, a, b⟩ := k
  obtain ⟨τ', a', b'⟩ := l
  rw [FlagTan.ksChg_apply]
  by_cases h : τ = τ'
  · subst h
    rw [Matrix.blockDiagonal'_apply_eq]
    simp [Matrix.kroneckerMap_apply, Pi.single_apply, Sigma.mk.inj_iff, ite_and]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    simp [Pi.single_apply, Sigma.mk.inj_iff, h]

theorem det_ksChg_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (K : Type) [Field K] (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K),
    (∀ σ, (g σ).det = 1) → ∀ (o : Fin Dw.dim ≃ HIx Dw (psiSet H)),
    (Matrix.of fun i j => FlagTan.ksChg (psiSet H) g ((Pi.single (o j) 1 : HIx Dw (psiSet H) → K)) (o i)).det = 1 := by
  intro E _ _ _ H Dw K _ g hg o
  have hM : (Matrix.of fun i j => FlagTan.ksChg (psiSet H) g ((Pi.single (o j) 1 : HIx Dw (psiSet H) → K)) (o i)) =
      (Matrix.blockDiagonal' (fun τ : psiSet H => Matrix.kroneckerMap (· * ·)
        (g (conjEmb τ.1)).transpose (g τ.1).transpose)).submatrix o o := by
    ext i j
    exact ksChg_single_eq_blockDiagonal' K (psiSet H) g (o i) (o j)
  rw [hM, Matrix.det_submatrix_equiv_self, GlobalTheory.Div.BlockChangeDet.det_blockDiagonal'_eq_prod]
  simp [Matrix.det_kronecker, Matrix.det_transpose, hg]

end GlobalTheory.KSChgDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFrameChangeBalancedTensorsCmType
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogKSDiv.DetChange

open GlobalTheory.LogKSDiv
open Classical

theorem sandwich {ι κ K : Type} [Fintype ι] [DecidableEq ι] [CommRing K] (B : Matrix ι κ K) (a b : ι) (x y : κ) :
    (Matrix.transpose B * Matrix.of (fun u v => (if u = a ∧ v = b then (1 : K) else 0) + (if u = b ∧ v = a then 1 else 0)) * B) x y =
      B a x * B b y + B b x * B a y := by
  simp [Matrix.mul_apply, add_mul, mul_add, Finset.sum_add_distrib, ite_and, Finset.sum_mul, Finset.mul_sum]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hostRoot_conj_eq_neg_and_ne_zero (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : starRingEnd ℂ H.rt0 = -H.rt0 ∧ H.rt0 ≠ 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h := H.sqrt_neg_disc_sq
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have hre0 : H.rt0.re = 0 := by
    by_contra hne
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  refine ⟨Complex.ext (by simp [hre0]) (by simp), ?_⟩
  intro h0
  rw [h0] at hre
  simp at hre
  exact H.d_prime.ne_zero hre

theorem emb_rt_cases (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [H.sqrt_neg_disc_sq, ← map_pow]
  have : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  rw [this]; simp

theorem conj_off (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) :
    ((starRingEnd ℂ).comp τ) (H.rt : E) ≠ H.rt0 := by
  obtain ⟨h1, h2⟩ := hostRoot_conj_eq_neg_and_ne_zero H
  rw [RingHom.comp_apply, h, h1]
  intro h3
  exact h2 (by linear_combination (-1/2 : ℂ) * h3)

theorem conj_on (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) (h : τ (H.rt : E) ≠ H.rt0) :
    ((starRingEnd ℂ).comp τ) (H.rt : E) = H.rt0 := by
  rcases emb_rt_cases H τ with h' | h'
  · exact absurd h' h
  · rw [RingHom.comp_apply, h', map_neg, (hostRoot_conj_eq_neg_and_ne_zero H).1, neg_neg]

theorem conj_conj_emb (τ : E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp τ) = τ := by
  ext x; simp

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {K : Type} [Field K]

theorem flatFrame_eq (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (a b : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    flatFrame A e e' (e a) (e' b) = Matrix.blockDiagonal' A a b := by
  simp [flatFrame]

def kronBlocks (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) :
    Matrix (PairIx H Dw) (PairIx H Dw) K :=
  Matrix.blockDiagonal' fun τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} =>
    Matrix.kroneckerMap (· * ·) (A τ.1).transpose (A ((starRingEnd ℂ).comp τ.1)).transpose

theorem lhs_entry (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (P Q : PairIx H Dw) :
    (Matrix.transpose (flatFrame A e e') * symPair (R := K) e P * flatFrame A e e')
      (e' ⟨Q.1.1, Q.2.1⟩) (e' ⟨(starRingEnd ℂ).comp Q.1.1, Q.2.2⟩) = kronBlocks A Q P := by
  unfold symPair
  rw [sandwich, flatFrame_eq, flatFrame_eq, flatFrame_eq, flatFrame_eq]
  obtain ⟨⟨τ, hτ⟩, i, k⟩ := P
  obtain ⟨⟨σ, hσ⟩, i', k'⟩ := Q
  have hne : (starRingEnd ℂ).comp τ ≠ σ := fun h => conj_off H τ hτ (h ▸ hσ)
  dsimp only
  rw [Matrix.blockDiagonal'_apply_ne A _ _ hne, zero_mul, add_zero]
  by_cases h : τ = σ
  · subst h
    simp [kronBlocks, Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply]
  · have h' : (⟨σ, hσ⟩ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}) ≠ ⟨τ, hτ⟩ := fun h2 => h (congrArg Subtype.val h2).symm
    simp [kronBlocks, Matrix.blockDiagonal'_apply_ne _ _ _ h', Matrix.blockDiagonal'_apply_ne A _ _ h]

theorem sym_entry {n' : ℕ} (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (P Q : PairIx H Dw) :
    symPair (R := K) e' P (e' ⟨Q.1.1, Q.2.1⟩) (e' ⟨(starRingEnd ℂ).comp Q.1.1, Q.2.2⟩) = if P = Q then 1 else 0 := by
  obtain ⟨⟨τ, hτ⟩, i, k⟩ := P
  obtain ⟨⟨σ, hσ⟩, i', k'⟩ := Q
  have h2 : ¬ (e' ⟨σ, i'⟩ = e' ⟨(starRingEnd ℂ).comp τ, k⟩ ∧
      e' ⟨(starRingEnd ℂ).comp σ, k'⟩ = e' ⟨τ, i⟩) := by
    rintro ⟨h, -⟩
    have h5 : σ = (starRingEnd ℂ).comp τ := congrArg Sigma.fst (e'.injective h)
    exact conj_off H τ hτ (h5 ▸ hσ)
  simp only [symPair, Matrix.of_apply, if_neg h2, add_zero, e'.apply_eq_iff_eq]
  by_cases h : τ = σ
  · subst h
    simp [Sigma.mk.inj_iff, eq_comm]
    intro h5
    exact (conj_off H τ hτ (by rw [← h5]; exact hτ)).elim
  · have h3 : ¬ (σ = τ) := Ne.symm h
    simp [h, h3]
    intro h5
    exact (conj_off H τ hτ (by rw [← h5]; exact hσ)).elim

theorem L_eq_submatrix (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (ε ε' : Fin Dw.dim ≃ PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) K)
    (hL : ∀ j, Matrix.transpose (flatFrame A e e') * symPair (R := K) e (ε j) * flatFrame A e e' =
      ∑ k, L k j • symPair (R := K) e' (ε' k)) :
    L = (kronBlocks A).submatrix ε' ε := by
  ext a j
  have h := congrFun (congrFun (hL j) (e' ⟨(ε' a).1.1, (ε' a).2.1⟩)) (e' ⟨(starRingEnd ℂ).comp (ε' a).1.1, (ε' a).2.2⟩)
  rw [lhs_entry, Matrix.sum_apply] at h
  simp only [Matrix.smul_apply, sym_entry, smul_eq_mul, mul_ite, mul_one, mul_zero, ε'.apply_eq_iff_eq] at h
  rw [Finset.sum_ite_eq' Finset.univ a] at h
  simpa using h.symm

theorem det_kronBlocks (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) :
    (kronBlocks A).det = ∏ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
      ((A τ.1).det ^ Dw.mult ((starRingEnd ℂ).comp τ.1) * (A ((starRingEnd ℂ).comp τ.1)).det ^ Dw.mult τ.1) := by
  rw [kronBlocks, GlobalTheory.Div.BlockChangeDet.det_blockDiagonal'_eq_prod]
  simp [Matrix.det_kronecker, Matrix.det_transpose]

theorem prod_pairs (f : (E →+* ℂ) → K) :
    ∏ τ : E →+* ℂ, f τ ^ (if τ (H.rt : E) = H.rt0 then Dw.q else Dw.p) =
      ∏ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
        (f τ.1 ^ Dw.mult ((starRingEnd ℂ).comp τ.1) * f ((starRingEnd ℂ).comp τ.1) ^ Dw.mult τ.1) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0), Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr (by convert rfl) fun τ _ => ?_
    rw [if_pos τ.2, Datum.mult, if_neg (conj_off H τ.1 τ.2)]
  · symm
    refine Fintype.prod_equiv
      { toFun := fun τ => ⟨(starRingEnd ℂ).comp τ.1, conj_off H τ.1 τ.2⟩
        invFun := fun σ => ⟨(starRingEnd ℂ).comp σ.1, conj_on H σ.1 σ.2⟩
        left_inv := fun τ => Subtype.ext (conj_conj_emb τ.1)
        right_inv := fun σ => Subtype.ext (conj_conj_emb σ.1) } _ _ (fun τ => ?_)
    simp only [Equiv.coe_fn_mk]
    rw [if_neg (conj_off H τ.1 τ.2), Datum.mult, if_pos τ.2]

end GlobalTheory.LogKSDiv.DetChange

theorem GlobalTheory.LogKSDiv.det_frameChange_balanced :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (K : Type) [Field K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) (n n' : ℕ)
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (ε ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) K),
    (∀ j, _root_.Matrix.transpose (GlobalTheory.LogKSDiv.flatFrame A e e') * GlobalTheory.LogKSDiv.symPair (R := K) e (ε j) * GlobalTheory.LogKSDiv.flatFrame A e e' =
      ∑ k, L k j • GlobalTheory.LogKSDiv.symPair (R := K) e' (ε' k)) →
    ∃ u : K, (u = 1 ∨ u = -1) ∧
      L.det = u * ∏ τ : E →+* ℂ, (A τ).det ^ (if τ (H.rt : E) = H.rt0 then Dw.q else Dw.p) := by
  intro E _ _ _ H Dw K _ A n n' e e' ε ε' L hL
  classical
  rw [GlobalTheory.LogKSDiv.DetChange.L_eq_submatrix A e e' ε ε' L hL]
  have hs : (GlobalTheory.LogKSDiv.DetChange.kronBlocks A).submatrix ε' ε =
      ((GlobalTheory.LogKSDiv.DetChange.kronBlocks A).submatrix ε ε).submatrix (ε'.trans ε.symm) id := by
    ext a b; simp
  refine ⟨((Equiv.Perm.sign (ε'.trans ε.symm) : ℤ) : K), ?_, ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign (ε'.trans ε.symm)) with h | h <;> simp [h]
  · rw [hs, Matrix.det_permute, Matrix.det_submatrix_equiv_self, GlobalTheory.LogKSDiv.DetChange.det_kronBlocks,
      GlobalTheory.LogKSDiv.DetChange.prod_pairs]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfIsIdent
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.FrameBox

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def sgnR {κ : Type} {p q : κ → ℕ} {Ψ : Finset (E →+* ℂ)} (σ : κ ≃ Ψ)
    (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (τ : Ψ) (a : Fin r) : ℝ :=
  if ((e (σ.symm τ)).symm a).isLeft then 1 else -1

def SkewCond {Ψ : Finset (E →+* ℂ)} (d : Ψ → Fin r → ℝ) (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) : Prop :=
  ∀ τ : Ψ, (∑ a, Y (τ, a, a) = 0) ∧
    ∀ a b, Y (τ, b, a) * (d τ b : ℂ) + (d τ a : ℂ) * (starRingEnd ℂ) (Y (τ, a, b)) = 0

def boxEnt (d : Fin r → ℝ) (z a b a' b' : Fin r) : ℂ :=
  if a < b then (if a' = a ∧ b' = b then 1 else if a' = b ∧ b' = a then -((d a * d b : ℝ) : ℂ) else 0)
  else if b < a then
    (if a' = b ∧ b' = a then Complex.I else if a' = a ∧ b' = b then Complex.I * ((d a * d b : ℝ) : ℂ) else 0)
  else (if a' = a ∧ b' = a then Complex.I else if a' = z ∧ b' = z then -Complex.I else 0)


open Classical in
def boxVec {Ψ : Finset (E →+* ℂ)} (d : Ψ → Fin r → ℝ) (z : Fin r) (k : Ψ × {ab : Fin r × Fin r // ab ≠ (z, z)}) :
    EuclideanSpace ℂ (Ψ × Fin r × Fin r) :=
  WithLp.toLp 2 fun m => if m.1 = k.1 then boxEnt (d k.1) z k.2.1.1 k.2.1.2 m.2.1 m.2.2 else 0

def entryL {Ψ : Finset (E →+* ℂ)} (m : Ψ × Fin r × Fin r) : EuclideanSpace ℂ (Ψ × Fin r × Fin r) →ₗ[ℝ] ℂ :=
  ((EuclideanSpace.proj m : EuclideanSpace ℂ (Ψ × Fin r × Fin r) →L[ℂ] ℂ) : _ →ₗ[ℂ] ℂ).restrictScalars ℝ

def boxCoord {Ψ : Finset (E →+* ℂ)} (z : Fin r) (k : Ψ × {ab : Fin r × Fin r // ab ≠ (z, z)}) :
    EuclideanSpace ℂ (Ψ × Fin r × Fin r) →ₗ[ℝ] ℝ :=
  if k.2.1.1 < k.2.1.2 then Complex.reLm ∘ₗ entryL (k.1, k.2.1.1, k.2.1.2)
  else if k.2.1.2 < k.2.1.1 then Complex.imLm ∘ₗ entryL (k.1, k.2.1.2, k.2.1.1)
  else Complex.imLm ∘ₗ entryL (k.1, k.2.1.1, k.2.1.1)

end GlobalTheory.CovTop.VolUp.FrameBox

namespace GlobalTheory.CovTop.VolUp.FrameBox
open Matrix

theorem det_ne_zero_of_isIdent {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (hI : IsIdent p q Ψ G x σ A e) (τ : Ψ) : (mat x τ).det ≠ 0 ∧ (G.map τ.1).det ≠ 0 := by
  obtain ⟨h1, h2⟩ := hI (σ.symm τ)
  rw [Equiv.apply_symm_apply] at h1 h2
  set P := permM (e (σ.symm τ)) with hP
  set J := Formalism.UG.Jpq (p (σ.symm τ)) (q (σ.symm τ)) with hJdef
  set M := mat x τ with hMdef
  set B := A (σ.symm τ) with hBdef
  have hPA : (Pᵀ * B) * M = 1 := by rw [Matrix.mul_assoc, h2, transpose_mul_permM]
  have hdetM : M.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hPA
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  refine ⟨hdetM, fun h => ?_⟩
  have hJ : J * J = 1 := by simp [hJdef, Formalism.UG.Jpq, fromBlocks_multiply]
  have hPc : Pᴴ = Pᵀ := by
    ext i j; simp only [hP, permM, conjTranspose_apply, transpose_apply, of_apply]; split_ifs <;> simp
  have hX : Mᴴ * (Bᴴ * J * B) * M = Pᵀ * J * P := by
    rw [← hPc, ← h2, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have hsq : (Pᵀ * J * P) * (Pᵀ * J * P) = 1 := by
    have e1 : (Pᵀ * J * P) * (Pᵀ * J * P) = Pᵀ * J * (P * Pᵀ) * J * P := by simp only [Matrix.mul_assoc]
    rw [e1, permM_mul_transpose, Matrix.mul_one, Matrix.mul_assoc Pᵀ J J, hJ, Matrix.mul_one, transpose_mul_permM]
  have hd0 : (Bᴴ * J * B).det = 0 := by
    rw [h1, det_neg, det_transpose, h, mul_zero]
  have := congrArg Matrix.det hsq
  rw [← hX, det_mul, det_mul, det_mul, hd0] at this
  simp at this

end GlobalTheory.CovTop.VolUp.FrameBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSchroedingerModelSiegelRule
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DblSchr

theorem doubledModel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
                       ∃ (dd : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA)
                           (GlobalTheory.WeilM.dbl (incM D.host.F JB))) (κ ⊕ κ))
                         (omd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)) →*
                           Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ)),
                         GlobalTheory.WeilM.IsDblCoord (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) co dd ∧
                         GlobalTheory.WeilM.IsUWeilSplit (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ
                           (incM D.host.F JA) (GlobalTheory.WeilM.dbl (incM D.host.F JB)) dd χT (GlobalTheory.WeilM.diagCols (Fin S.rank)) omd ∧
                         ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))
                           (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB))),
                           gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                           ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                             omd gd (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (1, g) φ₁) φ₂ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ _ co hco ω hω om hom
  obtain ⟨ωd, hωd, omd₀, homd⟩ := _root_.GlobalTheory.DblSchr.exists_dbl_weilDatum_transport D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco
  refine ⟨dblD _ co, omdOf omd₀, isDblCoord_dblD _ co,
    ⟨GlobalTheory.WeilM.isLagr_diagCols _ _, _root_.GlobalTheory.DblSchr.isUSplitting_omdOf D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ωd hωd omd₀ homd,
      _root_.GlobalTheory.DiagSiegel.siegelRule_ddr D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ωd hωd omd₀ homd⟩,
    _root_.GlobalTheory.DblRestr.restr_boxFun D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om hom ωd hωd omd₀ homd⟩

end GlobalTheory.DblSchr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrEqLocalizationIntegralClosureComapStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_eq_localization_integralClosure_comap : ∀ (K L : Type) [Field K] [Field L] [CharZero K] (φ : K →+* L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V], IsDiscreteValuationRing (V.comap φ) → ∀ s ∈ V, ∃ b d : L, (b ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ b = 0) ∧ (d ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ d = 0) ∧ d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  first | exact @GlobalTheory.dvr_eq_localization_integralClosure | exact GlobalTheory.dvr_eq_localization_integralClosure | (intros; apply GlobalTheory.dvr_eq_localization_integralClosure <;> assumption)
end

