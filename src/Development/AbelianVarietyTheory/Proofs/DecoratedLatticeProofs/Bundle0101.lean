module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Formalism.FormalDegreeBessel.StatementIO
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

namespace GlobalTheory.Unf

theorem contAut_rapidDec_bounded_integrable : ∀ (D : D7) (V : HSp D), CoCpt V → ∀ φ : GA D V → ℂ, IsContAut V φ → RapidDec V φ ∧ (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) ∧ ∀ v : Vol V, IntegrableOn φ v.𝓕 v.μ := by
  intro D V hV φ hφ
  obtain ⟨K, hK, hS⟩ := hV
  have hr : RapidDec V φ := RapidDec.of_isCompact hφ.1 hφ.2 hK hS
  exact ⟨hr, hr.bounded, fun v => hr.integrableOn_fundamentalDomain v.haar v.fund⟩

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoverFactoringRepresentationUnitaryGroupDictiona
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
open scoped InnerProductSpace
open GlobalTheory.CoverModel GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

noncomputable section

namespace GlobalTheory.RealPar.CoverFactor

theorem signCompat_of_blockOrd {p q n : ℕ} {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) :
    SignCompat ε e := by
  rintro (a | a)
  · simpa using h.1 a
  · simpa using h.2.1 a

theorem dictionary : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (U : URep T) (σ : Matrix (Fin n) (Fin n) ℂ → (U.H →L[ℂ] U.H)), BlockOrd e ε → Factors U e σ → IsURepOn (UJset ε) σ ∧ (IrrU U → IsIrredOn (UJset ε) σ) ∧ (∀ x, KFin T U.π x ↔ IsKFin ε σ x) ∧ (∀ Y, Y ∈ upq p q ↔ Formalism.REAL.inG ε (Matrix.reindex e e Y)) ∧ (∀ Y ∈ upq p q, ∀ t : ℝ, U.π (T.expt (t • Y)) = σ (NormedSpace.exp (t • Matrix.reindex e e Y))) ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∃ x ∈ T.Kset, U.π x = σ k := by
  intro p q n e ε T U σ h hF
  have hφ : IsFormIso ε (plainMat e) := isFormIso_plainMat (signCompat_of_blockOrd h)
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have := hF 1
    rw [map_one, map_one] at this
    rw [this]
    simp
  · intro a ha b hb
    obtain ⟨x, rfl⟩ := h.cov_surj T ha
    obtain ⟨y, rfl⟩ := h.cov_surj T hb
    have := hF (x * y)
    rw [map_mul, map_mul, hF x, hF y] at this
    rw [← ContinuousLinearMap.mul_def, this]
    simp [Matrix.submatrix_mul_equiv]
  · intro g hg v
    obtain ⟨x, rfl⟩ := h.cov_surj T hg
    rw [← hF x]
    exact U.isom x v
  · intro v
    refine CoverURep.continuousOn_of_cover h T _ ?_
    simpa only [← hF _] using U.cont v
  · intro hI S hS hst
    refine hI.2 S hS fun x v hv => ?_
    rw [hF x]
    exact hst _ (h.cov_mem T x) v hv
  · intro x
    have := kFin_iff (s := RingHom.id ℂ) hφ (T := T) (π := U.π) (σ := σ) (LinearIsometryEquiv.refl ℂ U.H)
      (c := fun _ => 1) (fun _ => one_ne_zero) (fun g y => by rw [one_smul, hF g]; rfl) x
    exact this.symm
  · intro Y
    exact (hφ.mem_lie Y).symm
  · intro Y hY t
    rw [hF, T.expt_cov _ (KStabLie.smul_mem_upq hY t)]
    exact congrArg σ (hφ.exp Y t).symm
  · intro k hk
    obtain ⟨x, hx⟩ := hφ.surj T (mem_K_iff.1 hk).1
    refine ⟨x, (hφ.mem_K T x).1 (hx ▸ hk), ?_⟩
    rw [hF x]
    exact congrArg σ hx

end GlobalTheory.RealPar.CoverFactor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DependentFrameFirstColumnRelation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.DepFrame

variable {E : Type} [Field E] {n ρ : ℕ}

def FirstRel (x : Matrix (Fin n) (Fin ρ) E) (j : Fin ρ) : Prop :=
  (∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧
    ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0

theorem mulVec_apply_eq_zero_of_upper {u : Matrix (Fin ρ) (Fin ρ) E}
    (hu : ∀ i k, k < i → u i k = 0) {a : Fin ρ → E} {i : Fin ρ}
    (ha : ∀ k, i ≤ k → a k = 0) : (u *ᵥ a) i = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k i with h | h
  · simp [hu i k h]
  · simp [ha k h]

theorem mulVec_apply_eq_of_upper {u : Matrix (Fin ρ) (Fin ρ) E}
    (hu : ∀ i k, k < i → u i k = 0) (hd : ∀ i, u i i = 1) {a : Fin ρ → E} {j : Fin ρ}
    (ha : ∀ i, j < i → a i = 0) : (u *ᵥ a) j = a j := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j]
  · simp [hd]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · simp [hu j k h]
    · simp [ha k h]
  · simp

theorem sum_smul_transpose (x : Matrix (Fin n) (Fin ρ) E) (a : Fin ρ → E) :
    ∑ i, a i • x.transpose i = x *ᵥ a := by
  ext r
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem not_linearIndependent_iff_exists (x : Matrix (Fin n) (Fin ρ) E) :
    ¬ LinearIndependent E x.transpose ↔ ∃ j, FirstRel x j := by
  classical
  have key : LinearIndependent E xᵀ ↔ ∀ g : Fin ρ → E, x *ᵥ g = 0 → ∀ i, g i = 0 := by
    refine (Fintype.linearIndependent_iff (R := E)
      (v := (fun i => xᵀ i : Fin ρ → Fin n → E))).trans ?_
    simp only [sum_smul_transpose]
  rw [key]
  constructor
  · intro h
    push_neg at h
    obtain ⟨g, hg, i₀, hi₀⟩ := h
    let S : Finset (Fin ρ) := Finset.univ.filter fun j =>
      ∃ a : Fin ρ → E, a j ≠ 0 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0
    have hlast : ∀ b : Fin ρ → E, x *ᵥ b = 0 → ∀ i, b i ≠ 0 → ∃ k ∈ S, b k ≠ 0 := by
      intro b hb i hi
      let T : Finset (Fin ρ) := Finset.univ.filter fun k => b k ≠ 0
      have hT : T.Nonempty := ⟨i, by simp [T, hi]⟩
      have hk : T.max' hT ∈ T := Finset.max'_mem T hT
      have hbk : b (T.max' hT) ≠ 0 := by simpa [T] using hk
      refine ⟨T.max' hT, ?_, hbk⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨b, hbk, fun l hl => ?_, hb⟩
      by_contra hne
      have : l ≤ T.max' hT := T.le_max' l (by simp [T, hne])
      exact absurd hl (not_lt.mpr this)
    obtain ⟨k, hkS, -⟩ := hlast g hg i₀ hi₀
    have hS : S.Nonempty := ⟨k, hkS⟩
    have hjS : S.min' hS ∈ S := Finset.min'_mem S hS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
    obtain ⟨a, haj, hagt, hax⟩ := hjS
    refine ⟨S.min' hS, ?_, ?_⟩
    · intro b hb hbx
      by_contra hne
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      obtain ⟨k, hkS, hbk⟩ := hlast b hbx i hi
      have hkj : k < S.min' hS := by
        by_contra h
        exact hbk (hb k (not_lt.mp h))
      exact absurd (S.min'_le k hkS) (not_le.mpr hkj)
    · refine ⟨(a (S.min' hS))⁻¹ • a, by simp only [Pi.smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ haj, fun i hi => by simp [hagt i hi], ?_⟩
      rw [Matrix.mulVec_smul, hax, smul_zero]
  · rintro ⟨j, -, a, haj, -, hax⟩ h
    have := h a hax j
    rw [haj] at this
    exact one_ne_zero this

theorem firstRel_unique (x : Matrix (Fin n) (Fin ρ) E) {j j' : Fin ρ}
    (h : FirstRel x j) (h' : FirstRel x j') : j = j' := by
  have key : ∀ {j j' : Fin ρ}, FirstRel x j → FirstRel x j' → ¬ j < j' := by
    rintro j j' ⟨-, a, haj, hagt, hax⟩ ⟨h1, -⟩ hlt
    have h0 := h1 a (fun i hi => hagt i (lt_of_lt_of_le hlt hi)) hax
    simp [h0] at haj
  rcases lt_trichotomy j j' with hl | he | hg
  · exact absurd hl (key h h')
  · exact he
  · exact absurd hg (key h' h)

theorem firstRel_mul (x : Matrix (Fin n) (Fin ρ) E) (j : Fin ρ) {u v : Matrix (Fin ρ) (Fin ρ) E}
    (hu : ∀ i k, k < i → u i k = 0) (hv : ∀ i k, k < i → v i k = 0) (hvd : ∀ i, v i i = 1)
    (huv : u * v = 1) (hvu : v * u = 1) (h : FirstRel x j) : FirstRel (x * u) j := by
  obtain ⟨h1, a, haj, hagt, hax⟩ := h
  have hmv : ∀ b, (x * u) *ᵥ b = x *ᵥ (u *ᵥ b) := fun b => (Matrix.mulVec_mulVec b x u).symm
  refine ⟨fun b hb hbx => ?_, v *ᵥ a, ?_, fun i hi => ?_, ?_⟩
  · have hub : u *ᵥ b = 0 :=
      h1 _ (fun i hi => mulVec_apply_eq_zero_of_upper hu (fun k hk => hb k (le_trans hi hk)))
        (by rw [← hmv]; exact hbx)
    calc b = (v * u) *ᵥ b := by rw [hvu, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hub, Matrix.mulVec_zero]
  · rw [mulVec_apply_eq_of_upper hv hvd hagt, haj]
  · exact mulVec_apply_eq_zero_of_upper hv (fun k hk => hagt k (lt_of_lt_of_le hi hk))
  · rw [hmv, Matrix.mulVec_mulVec a u v, huv, Matrix.one_mulVec, hax]

theorem firstRel_mul_iff (x : Matrix (Fin n) (Fin ρ) E) (j : Fin ρ) (u : Matrix (Fin ρ) (Fin ρ) E)
    (hd : ∀ i, u i i = 1) (hu : ∀ i k, k < i → u i k = 0) :
    FirstRel x j ↔ FirstRel (x * u) j := by
  have hdet : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i k h => hu i k h)]
    simp [hd]
  have hunit : IsUnit u.det := by rw [hdet]; exact isUnit_one
  letI : Invertible u := Matrix.invertibleOfIsUnitDet u hunit
  have huv : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u hunit
  have hvu : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul u hunit
  have hv : ∀ i k, k < i → u⁻¹ i k = 0 := fun i k h =>
    Matrix.blockTriangular_inv_of_blockTriangular (b := id) (fun i k h => hu i k h) h
  have hvd : ∀ i, u⁻¹ i i = 1 := by
    intro i
    have e := congrFun (congrFun hvu i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at e
    · simpa [hd] using e
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · simp [hv i k h]
      · simp [hu k i h]
    · simp
  constructor
  · exact firstRel_mul x j hu hv hvd huv hvu
  · intro h
    have := firstRel_mul (x * u) j hv hu hd hvu huv h
    rwa [Matrix.mul_assoc, huv, Matrix.mul_one] at this

theorem dependent_frame_first_relation : ∀ (E : Type) [Field E] (n ρ : ℕ) (x : Matrix (Fin n) (Fin ρ) E), (¬ LinearIndependent E x.transpose ↔ ∃ j : Fin ρ, (∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) ∧ (∀ j j' : Fin ρ, ((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) → ((∀ a : Fin ρ → E, (∀ i, j' ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j' = 1 ∧ (∀ i, j' < i → a i = 0) ∧ x *ᵥ a = 0) → j = j') ∧ ∀ (j : Fin ρ) (u : Matrix (Fin ρ) (Fin ρ) E), (∀ i, u i i = 1) → (∀ i k, k < i → u i k = 0) → (((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → x *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ x *ᵥ a = 0) ↔ ((∀ a : Fin ρ → E, (∀ i, j ≤ i → a i = 0) → (x * u) *ᵥ a = 0 → a = 0) ∧ ∃ a : Fin ρ → E, a j = 1 ∧ (∀ i, j < i → a i = 0) ∧ (x * u) *ᵥ a = 0)) := by
  intro E _ n ρ x
  exact ⟨not_linearIndependent_iff_exists x, fun j j' h h' => firstRel_unique x h h',
    fun j u hd hu => firstRel_mul_iff x j u hd hu⟩

end GlobalTheory.DepFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalAdelicEntriesCongrOneOfRatiosAtPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.DiagInt

theorem finMul {D : D7} {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, w, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w' => ?_, u * w, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w') (hb w')
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem intAt_add {D : D7} {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a + b ∈ intAt D (· = v) :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (f := _)]; exact add_mem ha.2 hb.2⟩

theorem intAt_mul {D : D7} {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [RingHom.map_mul]; exact finMul ha.2 hb.2⟩

theorem mul_sub_one {D : D7} {v : Pl D} {a b : AE D} (ha : a - 1 ∈ intAt D (· = v)) (hb : b - 1 ∈ intAt D (· = v)) :
    a * b - 1 ∈ intAt D (· = v) := by
  have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by ring
  rw [e]
  exact intAt_add (intAt_add (intAt_mul ha hb) ha) hb

theorem inv_diag_mul {R : Type*} [CommRing R] {ρ : ℕ} (t : GL (Fin ρ) R) (ht : ∀ i j, i ≠ j → t.1 i j = 0)
    (j : Fin ρ) : (t⁻¹).1 j j * t.1 j j = 1 := by
  have h0 : (t⁻¹).1 * t.1 = 1 := t.inv_mul
  have h := congrFun (congrFun h0 j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [← h, Finset.sum_eq_single j]
  · intro k _ hk; rw [ht k j hk, mul_zero]
  · intro h'; exact absurd (Finset.mem_univ j) h'

theorem diag_int : ∀ (D : D7) (ρ : ℕ) (v : Pl D) (t : GL (Fin ρ) (AE D)), (∀ i j, i ≠ j → t.1 i j = 0) → (∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v)) → (∀ i j : Fin ρ, j.1 = i.1 + 1 → t.1 i i * (t⁻¹).1 j j - 1 ∈ intAt D (· = v)) → (∀ i : Fin ρ, i.1 + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v)) → ∀ i, t.1 i i - 1 ∈ intAt D (· = v) := by
  intro D ρ v t ht _ hr hl
  have key : ∀ k : ℕ, ∀ i : Fin ρ, i.1 + k + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v) := by
    intro k
    induction k with
    | zero => intro i hi; exact hl i (by omega)
    | succ k ih =>
      intro i hi
      have hj : i.1 + 1 < ρ := by omega
      let j : Fin ρ := ⟨i.1 + 1, hj⟩
      have h1 := hr i j rfl
      have h2 := ih j (by simp [j]; omega)
      have e : t.1 i i = t.1 i i * (t⁻¹).1 j j * t.1 j j := by
        rw [mul_assoc, inv_diag_mul t ht j, mul_one]
      rw [e]
      exact mul_sub_one h1 h2
  intro i
  exact key (ρ - 1 - i.1) i (by omega)

end GlobalTheory.FinPl.DiagInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualPickDot
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def iota (p : SplitPt D k) : D.host.E →+* k := p.pr.comp (incA D)

def dualPick {m : Type} [DecidableEq m] (g : m → k) : m → k := by
  classical
  exact if h : ∃ i, g i ≠ 0 then Pi.single h.choose (g h.choose)⁻¹ else 0

theorem dualPick_dot {m : Type} [Fintype m] [DecidableEq m] (g : m → k) (hg : g ≠ 0) : dualPick g ⬝ᵥ g = 1 := by
  classical
  have h : ∃ i, g i ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hg (funext h')
  unfold dualPick
  rw [dite_eq_left h]
  simp only [single_dotProduct]
  exact inv_mul_cancel₀ h.choose_spec

variable {n : Type} [Fintype n] [DecidableEq n]

def wRow (p : SplitPt D k) {W₀ L' : HSp D} (ζ' : Fin L'.rank → D.host.E) (β : Frame p W₀ n) (t : n → k) : WO W₀ L' :=
  Matrix.of fun i j => p.sec (iota p (ζ' i) * (t ᵥ* β.b') j)

def wCol (p : SplitPt D k) {W₀ L' : HSp D} (ζ' : Fin L'.rank → D.host.E) (β : Frame p W₀ n) (t : n → k) : WO W₀ L' :=
  Matrix.of fun i j => cA D (p.sec (dualPick ((L'.gram.map (iota p)) *ᵥ fun i => iota p (ζ' i)) i *
    ((iota p D.host.xi0)⁻¹ * ((W₀.gram.map (iota p)) *ᵥ (β.b *ᵥ t)) j)))

end GlobalTheory.FinPl.LineAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdeleSupportedAtPlaceNotIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.FinPl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FinPl.NotIntAt

variable {D : D7}

def trAt (D : D7) (v : Pl D) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] Fv D.host.F v :=
  (evalV D.host.F v).toLinearMap ∘ₗ (TensorProduct.rid D.host.F (Af D.host.F)).toLinearMap ∘ₗ
    LinearMap.lTensor (Af D.host.F) (Algebra.trace D.host.F D.host.E)

theorem trAt_tmul (v : Pl D) (a : Af D.host.F) (x : D.host.E) :
    trAt D v (a ⊗ₜ[D.host.F] x) =
      algebraMap D.host.F (Fv D.host.F v) (Algebra.trace D.host.F D.host.E x) * evalV D.host.F v a := by
  simp [trAt, Algebra.smul_def]

theorem algebraMap_int_mem (v : Pl D) (r : 𝓞 D.host.F) :
    algebraMap D.host.F (Fv D.host.F v) (r : D.host.F) ∈ v.adicCompletionIntegers D.host.F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (r : D.host.F)
  erw [this]
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact v.intValuation_le_one r

theorem trAt_int (v : Pl D) {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    trAt D v y ∈ v.adicCompletionIntegers D.host.F := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have hle : intAE D ≤ (v.adicCompletionIntegers D.host.F).toSubring.toAddSubgroup.comap
      (trAt D v).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, rfl⟩
    change trAt D v (a ⊗ₜ[D.host.F] (x : D.host.E)) ∈ v.adicCompletionIntegers D.host.F
    rw [trAt_tmul]
    have hint : IsIntegral ℤ (Algebra.trace D.host.F D.host.E (x : D.host.E)) :=
      Algebra.isIntegral_trace x.isIntegral_coe
    exact mul_mem (algebraMap_int_mem v ⟨_, hint⟩) (ha v)
  exact hle hy

theorem evalV_single_same (v : Pl D) (y : Fv D.host.F v) : evalV D.host.F v (singleV D.host.F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : Pl D => w.adicCompletionIntegers D.host.F) v y

theorem evalV_single_ne (v : Pl D) (y : Fv D.host.F v) {w : Pl D} (hw : w ≠ v) :
    evalV D.host.F w (singleV D.host.F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : Pl D => w.adicCompletionIntegers D.host.F) y hw

theorem inv_not_mem (v : Pl D) {π : 𝓞 D.host.F} (hπ : π ∈ v.asIdeal) (hπ0 : π ≠ 0) :
    (algebraMap D.host.F (Fv D.host.F v) (π : D.host.F))⁻¹ ∉ v.adicCompletionIntegers D.host.F := by
  intro h
  have hv : Valued.v (algebraMap D.host.F (Fv D.host.F v) (π : D.host.F)) < 1 := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (π : D.host.F)
    erw [this]
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_lt_one_iff_mem π).2 hπ
  have hne : algebraMap D.host.F (Fv D.host.F v) (π : D.host.F) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hπ0
  have h1 : Valued.v ((algebraMap D.host.F (Fv D.host.F v) (π : D.host.F)) *
      (algebraMap D.host.F (Fv D.host.F v) (π : D.host.F))⁻¹) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h)) hv
  rw [mul_inv_cancel₀ hne, map_one] at h1
  exact lt_irrefl _ h1

theorem exists_not_intAt : ∀ (D : D7) (v : Pl D), ∃ u ∈ idAt D (· = v), u ∉ intAt D (· = v) := by
  intro D v
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  set n : ℕ := Module.finrank D.host.F D.host.E
  have hn : (n : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  set c : Fv D.host.F v := (algebraMap D.host.F (Fv D.host.F v) ((n : D.host.F) * (π : D.host.F)))⁻¹
  refine ⟨pairA D.host.F 0 (singleV D.host.F v c) ⊗ₜ[D.host.F] (1 : D.host.E),
    GlobalTheory.FinPl.LatMem.tmul_mem_idAt (P := (· = v))
      (fun w hw => evalV_single_ne v c hw) 1, fun h => ?_⟩
  have h2 := trAt_int v h.2
  change trAt D v (singleV D.host.F v c ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ _ at h2
  have htr : Algebra.trace D.host.F D.host.E 1 = (n : D.host.F) := by
    simpa using Algebra.trace_algebraMap (R := D.host.F) (S := D.host.E) 1
  rw [trAt_tmul, evalV_single_same, htr] at h2
  have e : algebraMap D.host.F (Fv D.host.F v) (n : D.host.F) * c =
      (algebraMap D.host.F (Fv D.host.F v) (π : D.host.F))⁻¹ := by
    simp only [c, map_mul, map_natCast, mul_inv, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  rw [e] at h2
  exact inv_not_mem v hπ hπ0 h2

end GlobalTheory.FinPl.NotIntAt
end
end

