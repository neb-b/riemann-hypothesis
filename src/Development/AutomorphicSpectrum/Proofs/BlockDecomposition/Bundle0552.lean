module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFacts
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.UnitaryWitt

section Generic

variable {L : Type} [Field L] {n : ℕ}

theorem conj_mem_UJ_one_iff (σ : L →+* L) {J : Matrix (Fin n) (Fin n) L} (b g : GL (Fin n) L)
    (hb : cT σ b.val * b.val = J) : b * g * b⁻¹ ∈ UJ σ 1 ↔ g ∈ UJ σ J := by
  have hbi : b.val * (b⁻¹ : GL (Fin n) L).val = 1 := by rw [← Units.val_mul]; simp
  have hib : (b⁻¹ : GL (Fin n) L).val * b.val = 1 := by rw [← Units.val_mul]; simp
  change cT σ (b * g * b⁻¹).val * 1 * (b * g * b⁻¹).val = 1 ↔ cT σ g.val * J * g.val = J
  simp only [Units.val_mul, Matrix.mul_one]
  have hc : cT σ (b⁻¹ : GL (Fin n) L).val * cT σ b.val = 1 := by
    rw [← cT_mul, hbi, cT_one]
  have key : cT σ (b.val * g.val * (b⁻¹ : GL (Fin n) L).val) * (b.val * g.val * (b⁻¹ : GL (Fin n) L).val)
      = cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ g.val * J * g.val) * (b⁻¹ : GL (Fin n) L).val := by
    rw [← hb]
    simp only [cT_mul, Matrix.mul_assoc]
  rw [key]
  constructor
  · intro h
    have h2 : cT σ b.val * (cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ g.val * J * g.val) * (b⁻¹ : GL (Fin n) L).val) * b.val
        = cT σ b.val * 1 * b.val := by rw [h]
    have hc' : cT σ b.val * cT σ (b⁻¹ : GL (Fin n) L).val = 1 := by
      rw [← cT_mul, hib, cT_one]
    calc cT σ g.val * J * g.val
        = (cT σ b.val * cT σ (b⁻¹ : GL (Fin n) L).val) * (cT σ g.val * J * g.val) * ((b⁻¹ : GL (Fin n) L).val * b.val) := by
          rw [hc', hib, Matrix.one_mul, Matrix.mul_one]
      _ = cT σ b.val * (cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ g.val * J * g.val) * (b⁻¹ : GL (Fin n) L).val) * b.val := by
          simp only [Matrix.mul_assoc]
      _ = J := by rw [h2, Matrix.mul_one, hb]
  · intro h
    rw [h, ← hb]
    calc cT σ (b⁻¹ : GL (Fin n) L).val * (cT σ b.val * b.val) * (b⁻¹ : GL (Fin n) L).val
        = (cT σ (b⁻¹ : GL (Fin n) L).val * cT σ b.val) * (b.val * (b⁻¹ : GL (Fin n) L).val) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hc, hbi, Matrix.one_mul]

theorem diagT_mem_UJ_antiJ_iff (σ : L →+* L) (u : Fin n → Lˣ) :
    GlobalTheory.SmGL.diagT L (Fin n) u ∈ UJ σ (antiJ L n) ↔ ∀ i, σ (u i) * u (Fin.rev i) = 1 := by
  have hent : ∀ i j, (cT σ (GlobalTheory.SmGL.diagT L (Fin n) u).val * antiJ L n * (GlobalTheory.SmGL.diagT L (Fin n) u).val) i j
      = σ (u i) * antiJ L n i j * u j := by
    intro i j
    have hd : cT σ (GlobalTheory.SmGL.diagT L (Fin n) u).val = Matrix.diagonal fun i => σ (u i) := by
      rw [GlobalTheory.SmGL.val_diagT]
      ext a c
      by_cases h : a = c
      · subst h; simp [cT]
      · simp [cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
    rw [hd, GlobalTheory.SmGL.val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hrev : ∀ i : Fin n, antiJ L n i (Fin.rev i) = 1 := by
    intro i
    have : i.val + (Fin.rev i).val + 1 = n := by
      rw [Fin.val_rev]; omega
    exact if_pos this
  change cT σ (GlobalTheory.SmGL.diagT L (Fin n) u).val * antiJ L n * (GlobalTheory.SmGL.diagT L (Fin n) u).val = antiJ L n ↔ _
  constructor
  · intro h i
    have := congrFun (congrFun h i) (Fin.rev i)
    rw [hent, hrev, mul_one] at this
    exact this
  · intro h
    ext i j
    rw [hent]
    by_cases hij : i.val + j.val + 1 = n
    · have hj : j = Fin.rev i := by
        apply Fin.ext; rw [Fin.val_rev]; omega
      subst hj
      rw [hrev, mul_one, h i]
    · have : antiJ L n i j = 0 := by simp [antiJ, hij]
      rw [this]; simp

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem UL_eq_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) : UL n w = UJ (cj w) 1 := if_neg hw

theorem mem_iwU_iff (n : ℕ) (w : Pl E) (b : GLw n w) (γ : UL n w) :
    γ ∈ iwU n w b ↔ b⁻¹ * γ.1 * b ∈ iwGL n w := by
  rw [iwU, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, e⟩
    have e' : b * x * b⁻¹ = γ.1 := e
    rw [← e']
    simpa [mul_assoc] using hx
  · intro h
    refine ⟨_, h, ?_⟩
    change b * (b⁻¹ * γ.1 * b) * b⁻¹ = γ.1
    group

theorem isClosed_UJ_one {w : Pl E} (n : ℕ) (hc : Continuous (cj w)) :
    IsClosed (UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) : Set (GLw n w)) := by
  have hv : Continuous fun g : GLw n w => (g.val : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
    Units.continuous_val
  have hm : Continuous fun g : GLw n w => cT (cj w) g.val * 1 * g.val := by
    refine Continuous.matrix_mul (Continuous.matrix_mul ?_ continuous_const) hv
    exact (hv.matrix_map hc).matrix_transpose
  exact isClosed_eq hm continuous_const

theorem isCompact_iwU {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w) (hc : Continuous (cj w)) :
    IsCompact (iwU n w b : Set (UL n w)) := by
  have hcl : IsClosed (UL n w : Set (GLw n w)) := by
    rw [UL_eq_of_not_split hw]; exact isClosed_UJ_one n hc
  have hK : IsCompact ((fun g : GLw n w => b * g * b⁻¹) '' (iwGL n w : Set (GLw n w))) :=
    (GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori (w.adicCompletion E) (Fin n)).image (by fun_prop)
  have hP := hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have e : (iwU n w b : Set (UL n w)) = Subtype.val ⁻¹'
      ((fun g : GLw n w => b * g * b⁻¹) '' (iwGL n w : Set (GLw n w))) := by
    ext γ
    simp only [SetLike.mem_coe, mem_iwU_iff, Set.mem_preimage, Set.mem_image]
    constructor
    · intro h
      exact ⟨_, h, by group⟩
    · rintro ⟨x, hx, e⟩
      rw [← e]
      simpa [mul_assoc] using hx
  rw [e]
  exact hP

theorem unitary_hyperbolic_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → (∀ g : GLw n w, b * g * b⁻¹ ∈ UL n w ↔ g ∈ UJ (cj w) (antiJ (w.adicCompletion E) n)) ∧ (∀ γ : UL n w, γ ∈ iwU n w b ↔ b⁻¹ * γ.1 * b ∈ iwGL n w) ∧ IsCompact (iwU n w b : Set (UL n w)) ∧ ∀ u : Fin n → (w.adicCompletion E)ˣ, GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u ∈ UJ (cj w) (antiJ (w.adicCompletion E) n) ↔ ∀ i, cj w (u i) * u (Fin.rev i) = 1 := by
  intro E _ _ _ hU w hw n b hb
  refine ⟨fun g => ?_, mem_iwU_iff n w b, isCompact_iwU hw n b (_root_.GlobalTheory.ConjAtPlace.main E hU w).1,
    diagT_mem_UJ_antiJ_iff (cj w)⟩
  rw [UL_eq_of_not_split hw]
  exact conj_mem_UJ_one_iff (cj w) b g hb.2

end GlobalTheory.CompanionTheory.UnitaryWitt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightExponentStrictlyAntitone
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.Wexp

theorem cone_strictAnti {m : ℕ} {l : Fin m → ℤ} (hl : Cone l) : StrictAnti l := by
  have key : ∀ (d : ℕ) (i j : Fin m), (j : ℕ) = i + d + 1 → l j < l i := by
    intro d
    induction d with
    | zero =>
      intro i j hij
      have := hl.1 i j (by omega)
      omega
    | succ d ih =>
      intro i j hij
      have hk : (i : ℕ) + d + 1 < m := by have := j.isLt; omega
      have h1 := ih i ⟨(i : ℕ) + d + 1, hk⟩ rfl
      have h2 := hl.1 ⟨(i : ℕ) + d + 1, hk⟩ j (by simp only; omega)
      omega
  intro i j hij
  have hij' : (i : ℕ) < j := hij
  exact key ((j : ℕ) - i - 1) i j (by omega)

theorem wexp_of_lt {n : ℕ} (l : Fin (n / 2) → ℤ) (i : Fin n) (h : (i : ℕ) < n / 2) :
    wexp n l i = l ⟨i, h⟩ := by
  simp only [wexp, dif_pos h]

theorem wexp_of_rev_lt {n : ℕ} (l : Fin (n / 2) → ℤ) (i : Fin n) (h' : n - 1 - (i : ℕ) < n / 2) :
    wexp n l i = -l ⟨n - 1 - i, h'⟩ := by
  have h : ¬ (i : ℕ) < n / 2 := by have := i.isLt; omega
  simp only [wexp, dif_neg h, dif_pos h']

theorem wexp_of_middle {n : ℕ} (l : Fin (n / 2) → ℤ) (i : Fin n) (h : ¬ (i : ℕ) < n / 2)
    (h' : ¬ n - 1 - (i : ℕ) < n / 2) : wexp n l i = 0 := by
  simp only [wexp, dif_neg h, dif_neg h']

theorem wexp_strictAnti_rev : ∀ (n : ℕ) (l : Fin (n / 2) → ℤ), Cone l →
    StrictAnti (wexp n l) ∧ ∀ i, wexp n l (Fin.rev i) = -wexp n l i := by
  intro n l hl
  have hs := cone_strictAnti hl
  have hp := hl.2
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    have hj := j.isLt
    by_cases h1 : (i : ℕ) < n / 2
    · rw [wexp_of_lt l i h1]
      have a := hp ⟨i, h1⟩
      by_cases h2 : (j : ℕ) < n / 2
      · rw [wexp_of_lt l j h2]
        exact hs (Fin.mk_lt_mk.mpr hij')
      · by_cases h3 : n - 1 - (j : ℕ) < n / 2
        · rw [wexp_of_rev_lt l j h3]
          have b := hp ⟨_, h3⟩
          omega
        · rw [wexp_of_middle l j h2 h3]
          omega
    · have h3 : n - 1 - (j : ℕ) < n / 2 := by omega
      rw [wexp_of_rev_lt l j h3]
      have b := hp ⟨_, h3⟩
      by_cases h2 : n - 1 - (i : ℕ) < n / 2
      · rw [wexp_of_rev_lt l i h2]
        have : l ⟨n - 1 - i, h2⟩ < l ⟨n - 1 - j, h3⟩ := hs (Fin.mk_lt_mk.mpr (by omega))
        omega
      · rw [wexp_of_middle l i h1 h2]
        omega
  · intro i
    have hi := i.isLt
    have hr : ((Fin.rev i : Fin n) : ℕ) = n - 1 - i := by
      rw [Fin.val_rev]; omega
    by_cases h1 : (i : ℕ) < n / 2
    · have h' : n - 1 - ((Fin.rev i : Fin n) : ℕ) < n / 2 := by omega
      rw [wexp_of_rev_lt l _ h', wexp_of_lt l i h1]
      congr 2
      apply Fin.ext
      simp only
      omega
    · by_cases h2 : n - 1 - (i : ℕ) < n / 2
      · have h' : ((Fin.rev i : Fin n) : ℕ) < n / 2 := by omega
        rw [wexp_of_lt l _ h', wexp_of_rev_lt l i h2, neg_neg]
        congr 1
        exact Fin.ext hr
      · rw [wexp_of_middle l i h1 h2, wexp_of_middle l _ (by omega) (by omega), neg_zero]

end GlobalTheory.CompanionTheory.Wexp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationFourierCoefficient
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellVal

section Blocks

variable {R : Type} [CommRing R] {n r t : ℕ} (hn : r + t = n)

theorem block_mul₂ (a a' : Matrix (Fin r) (Fin r) R) (b b' : Matrix (Fin r) (Fin t) R)
    (c c' : Matrix (Fin t) (Fin r) R) (d d' : Matrix (Fin t) (Fin t) R) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one : bl hn (1 : Matrix (Fin r) (Fin r) R) 0 0 1 = 1 := by
  simp only [bl]
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrix_zero : bl hn (0 : Matrix (Fin r) (Fin r) R) 0 0 0 = 0 := by
  simp only [bl, Matrix.fromBlocks_zero]
  rfl

theorem det_bl_unip (y : Matrix (Fin r) (Fin t) R) : (bl hn 1 y 0 1).det = 1 := by
  simp only [bl]
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem trace_bl_last (b : Matrix (Fin t) (Fin t) R) (Z : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (bl hn 0 0 0 b * Z) =
      Matrix.trace (b * Z.submatrix (finSumFinEquiv.trans (finCongr hn) ∘ Sum.inr)
        (finSumFinEquiv.trans (finCongr hn) ∘ Sum.inr)) := by
  set e := finSumFinEquiv.trans (finCongr hn) with he
  have h1 : Z = (Matrix.fromBlocks (Z.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)) (Z.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr))
      (Z.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl)) (Z.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr))).submatrix e.symm e.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;> simp
  conv_lhs => rw [h1]
  simp only [bl, ← he]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  rw [Equiv.sum_comp e.symm (fun s => Matrix.fromBlocks _ _ _ _ s s), Fintype.sum_sum_type]
  simp

end Blocks

section Frames

variable {D : D7} {a n r t : ℕ} (hn : r + t = n)

theorem jn_mul_unip (x : Mx D a r) (y : Mx D r t) :
    (HMul.hMul (jn hn x 0) (bl hn 1 y 0 1) : Mx D a n) = jn hn x (mm x y) := by
  simp only [jn, bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp [mm]

theorem trace_inner_jn (V : HSp D) (b : Mx D t t) (x : Mx D V.rank r) (v : Mx D V.rank t) :
    Matrix.trace (HMul.hMul (bl hn 0 0 0 b) (GlobalTheory.StdUnn.inner V (jn hn x v) (jn hn x v)) : Mx D n n) =
      Matrix.trace (mm b (ip V v v)) := by
  rw [trace_bl_last]
  congr 1
  have h : (GlobalTheory.StdUnn.inner V (jn hn x v) (jn hn x v)).submatrix (finSumFinEquiv.trans (finCongr hn) ∘ Sum.inr)
      (finSumFinEquiv.trans (finCongr hn) ∘ Sum.inr) = ip V v v := by
    ext i j
    simp [GlobalTheory.StdUnn.inner, ip, mm, jn, adj, Matrix.mul_apply]
  rw [h]

def unipGL (y : Mx D r t) : GL (Fin n) (AE D) where
  val := bl hn 1 y 0 1
  inv := bl hn 1 (-y) 0 1
  val_inv := by rw [block_mul₂]; simpa using blockRowSubstitution_one hn
  inv_val := by rw [block_mul₂]; simpa using blockRowSubstitution_one hn

theorem det_unipGL (y : Mx D r t) :
    Matrix.GeneralLinearGroup.det (unipGL hn y : GL (Fin n) (AE D)) = (1 : (AE D)ˣ) :=
  Units.ext (det_bl_unip hn y)

theorem adj_bl_unip_neg (y : Mx D r t) :
    adj (bl hn (1 : Mx D r r) (-y) 0 (1 : Mx D t t)) = bl hn (1 : Mx D r r) 0 (-adj y) (1 : Mx D t t) := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [adj, bl, Matrix.one_apply, apply_ite (cA D)]
  all_goals by_cases h : i = j <;> simp [h, eq_comm]

end Frames

theorem weil_translate_frame {D : D7} {n r t : ℕ} (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (V : HSp D)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ)
    (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)}
    (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕)
    {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕) (Φ : schwartzA θ V.rank n)
    {nb : hermA D t → G D t} (hnb : IsNMap nb) {w : G D t} (hw : IsW w) (b : hermA D t) (y : Mx D r t)
    (x : Mx D V.rank r) :
    (ω (M.sh y * M.emb (w * nb b) * 1) Φ).1 (jn hn x 0) =
      ∫ v, pch ψ b.1 (ip V v v) * Φ.1 (jn hn x v) * ψ (trA (Matrix.trace (ip V (mm x y) v))) ∂μt := by
  have e1 : ω (M.sh y * M.emb (w * nb b) * 1) Φ = ω (M.sh y) (ω (M.emb w) (ω (M.emb (nb b)) Φ)) := by
    simp only [mul_one, map_mul, Module.End.mul_apply]
  have hdet := det_unipGL hn y
  have hsh : mat (M.sh y) = blk4 (unipGL hn y).1 0 0 (adj ((unipGL hn y)⁻¹).1) := by
    rw [M.sh_mat]
    have : ((unipGL hn y)⁻¹).1 = bl hn 1 (-y) 0 1 := rfl
    rw [this, adj_bl_unip_neg]
    rfl
  have hemb : mat (M.emb (nb b)) = blk4 1 (bl hn 0 0 0 b.1) 0 1 := by
    rw [M.emb_mat (nb b) 1 b.1 0 1 (hnb b), blockRowSubstitution_one, blockMatrix_zero]
  rw [e1, hω.levi (M.sh y) (unipGL hn y) hsh, hdet]
  have hpow : npow (absA D 1) ((V.rank : ℂ) / 2) = 1 := by simp [npow]
  rw [map_one, hpow]
  simp only [Circle.coe_one, one_mul]
  have hj : (HMul.hMul (jn hn x 0) (unipGL hn y).1 : Mx D V.rank n) = jn hn x (mm x y) := jn_mul_unip hn x y
  rw [hj, (hP D n r t hn M V ψ hψ χ hχ hη θ hθ μ hμ ω hω μr μt hμr hμt (ω (M.emb (nb b)) Φ)).2.2 w hw x (mm x y)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  rw [hω.unip (M.emb (nb b)) _ hemb, trace_inner_jn]
  rfl

end GlobalTheory.CompanionTheory.CellVal

end
end

