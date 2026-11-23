module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def DegEq.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s →
    ∀ (pp : Ideal (Kleiman.Poly k N)) (W : Ideal (NumbersDVR.MRing (graphIdx N m) k)),
      Kleiman.IsSubvar x pp 1 → NumbersDVR.IsMultiProjPrime W → mIdealOver k (graphVec x s) ≤ W →
      W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b)) = pp →
      NumbersDVR.intNum k W ![graphDeg n] = Kleiman.interNum pp ![Q.toSubSystem]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerRest
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def CurveComap.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s →
    ∀ W : Ideal (NumbersDVR.MRing (graphIdx N m) k), NumbersDVR.IsMultiProjPrime W →
      mIdealOver k (graphVec x s) ≤ W → ∀ e : ℕ,
        (relDim W = ((e : ℕ) : WithBot (WithTop ℤ)) ↔
          Kleiman.IsSubvar x (W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b))) e)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

def CurveLift.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s →
    ∀ (pp : Ideal (Kleiman.Poly k N)) (e : ℕ), Kleiman.IsSubvar x pp e →
      ∃ W : Ideal (NumbersDVR.MRing (graphIdx N m) k), NumbersDVR.IsMultiProjPrime W ∧
        mIdealOver k (graphVec x s) ≤ W ∧ W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b)) = pp

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeBaseComap
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

theorem isMultiProjPrime_baseComap (F : Type) [Field F] {K : Type} [DecidableEq K] {ι : K → Type} (k₀ : K)
    {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {W : Ideal (NumbersDVR.MRing ι F)} (hW : NumbersDVR.IsMultiProjPrime W) :
    NumbersDVR.IsMultiProjPrime (baseComap F k₀ e W) := by
  refine FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (j := fun _ : Unit => k₀)
    (g := fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) (fun _ => rfl)
    (fun _ _ _ => Subsingleton.elim _ _) ?_ ?_ hW
  · rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and, EmbeddingLike.apply_eq_iff_eq] at h
    rw [h]
  · rintro ⟨k, i⟩ ⟨⟨⟩, hk⟩
    obtain rfl : k₀ = k := hk
    exact ⟨⟨(), e i⟩, by simp⟩

theorem mIdealOver_le_baseComap (F : Type) [Field F] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]
    [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {x : Fin (N + 1) → Ω}
    (hx : x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) {W : Ideal (NumbersDVR.MRing ι F)}
    (hW : mIdealOver F y ≤ W) : mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) ≤ baseComap F k₀ e W := by
  subst hx
  intro f hf
  rw [baseComap, Ideal.mem_comap]
  apply hW
  have hcomp : (mConeMapOver F y).comp
      (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) =
      ((rename (R := Ω) fun _ : Unit => k₀).restrictScalars F).comp
        (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  have hf' : mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) f = 0 := hf
  have h1 := AlgHom.congr_fun hcomp f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hf', map_zero] at h1
  exact h1

theorem ModelCurves.proof (hdim : ModelCurvesDim.Statement) (hlift : ModelCurvesLift.Statement) :
    ModelCurves.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy d
  refine ⟨fun W hW hyW hd => ⟨isMultiProjPrime_baseComap F k₀ e hW,
    mIdealOver_le_baseComap F y k₀ e hx hyW, ?_⟩, fun P hP hxP hd => ?_⟩
  · rw [hdim F K ι Ω y k₀ N e hy W hW hyW, hd]
  · obtain ⟨W, hW, hyW, rfl⟩ := hlift F K ι Ω y k₀ N e x hx hy P hP hxP
    exact ⟨W, hW, hyW, by rw [← hdim F K ι Ω y k₀ N e hy W hW hyW, hd], rfl⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MConeMapOverBaseRename
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

universe u w

section Scale

variable {k : Type u} [Field k] {K' : Type w} [Field K'] [Algebra k K'] {N : ℕ} {y : Fin (N + 1) → K'}

def scaleBundle (P : Kleiman.LineBundle k y) (μ : K') (hμ : μ ≠ 0) : Kleiman.LineBundle k y where
  sub I := Submodule.span (Kleiman.chartRing k y I) {μ} * P.sub I
  mono I J h z hz := by
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_span_singleton_mul.mp hz
    exact Submodule.mem_span_singleton_mul.mpr ⟨w, P.mono I J h w hw, rfl⟩
  mem_iff I J h z := by
    simp only [Submodule.mem_span_singleton_mul]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨a, ha, haw⟩ := (P.mem_iff I J h w).mp hw
      refine ⟨a, ha, (a : K') • w, haw, ?_⟩
      simp only [smul_eq_mul]; ring
    · rintro ⟨a, ha, w, hw, hwz⟩
      refine ⟨μ⁻¹ * z, (P.mem_iff I J h _).mpr ⟨a, ha, ?_⟩, by field_simp⟩
      rw [smul_eq_mul] at hwz ⊢
      rw [show (a : K') * (μ⁻¹ * z) = w by
        rw [mul_left_comm, ← hwz, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul]]
      exact hw
  fg I := (Submodule.fg_span_singleton μ).mul (P.fg I)
  invertible I := by
    obtain ⟨M, hM⟩ := P.invertible I
    refine ⟨Submodule.span (Kleiman.chartRing k y I) {μ⁻¹} * M, ?_⟩
    rw [mul_mul_mul_comm, hM, Submodule.span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ hμ,
      mul_one, ← Submodule.one_eq_span]

theorem restrictData_scale {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}
    {Q : Kleiman.SubSystem k x Ω} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0} {P : Kleiman.LineBundle k y} {r : Ω → K'}
    (hr : Kleiman.RestrictData Q hxy P.toSubSystem r) (μ : K') (hμ : μ ≠ 0) :
    Kleiman.RestrictData Q hxy (scaleBundle P μ hμ).toSubSystem (fun q => μ * r q) := by
  constructor
  · intro I q hq
    exact Submodule.mem_span_singleton_mul.mpr ⟨r q, hr.mem I q hq, rfl⟩
  · intro I q hq q' hq'
    simp only [hr.add I q hq q' hq', mul_add]
  · intro I q hq f s e hs hf hse
    simp only [hr.smul I q hq f s e hs hf hse]
    ring
  · intro I
    change _ = Submodule.span _ {μ} * P.sub I
    rw [← hr.span I, Submodule.span_mul_span, Set.singleton_mul, Set.image_image]

end Scale

section GraphEq

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {N m : ℕ}

abbrev baseRename : Kleiman.Poly k N →ₐ[k] MvPolynomial (Σ c, graphIdx N m c) k :=
  rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)

theorem mConeMapOver_baseRename (x : Fin (N + 1) → Ω) (s : Fin m → Ω) {g : Kleiman.Poly k N} {e : ℕ}
    (hg : g.IsHomogeneous e) :
    mConeMapOver k (graphVec x s) (baseRename g) = C (aeval x g) * X baseBlock ^ e := by
  have h1 := DFunLike.congr_fun (mConeMapOver_graph_comp_base (S := k) x s) g
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at h1
  rw [h1, Kleiman.cone_of_isHomogeneous x hg, AlgHom.restrictScalars_apply, map_mul, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X, MvPolynomial.algebraMap_eq]

theorem mConeMapOver_graphEq (x : Fin (N + 1) → Ω) (s : Fin m → Ω) {f h : Kleiman.Poly k N} {e : ℕ}
    (hf : f.IsHomogeneous e) (hh : h.IsHomogeneous e) (b l : Fin m) :
    mConeMapOver k (graphVec x s) (X ⟨Sum.inr (), b⟩ * baseRename h - X ⟨Sum.inr (), l⟩ * baseRename f) =
      C (s b * aeval x h - s l * aeval x f) * (X (Sum.inr ()) * X baseBlock ^ e) := by
  rw [map_sub, map_mul, map_mul, mConeMapOver_baseRename x s hh, mConeMapOver_baseRename x s hf]
  simp only [mConeMapOver, aeval_X, graphVec_inr, map_sub, map_mul]
  ring

theorem graphEq_of_le {K' : Type} [Field K'] [Algebra k K'] {x : Fin (N + 1) → Ω} {s : Fin m → Ω}
    {x' : Fin (N + 1) → K'} {s' : Fin m → K'}
    (hle : mIdealOver k (graphVec x s) ≤ mIdealOver k (graphVec x' s')) {f h : Kleiman.Poly k N} {e : ℕ}
    (hf : f.IsHomogeneous e) (hh : h.IsHomogeneous e) (b l : Fin m)
    (hx : s b * aeval x h = s l * aeval x f) : s' b * aeval x' h = s' l * aeval x' f := by
  have hmem : X ⟨Sum.inr (), b⟩ * baseRename h - X ⟨Sum.inr (), l⟩ * baseRename f ∈
      mIdealOver k (graphVec x s) := by
    change _ ∈ RingHom.ker _
    rw [RingHom.mem_ker]
    rw [mConeMapOver_graphEq x s hf hh, hx, sub_self, map_zero, zero_mul]
  have h0 := hle hmem
  change _ ∈ RingHom.ker _ at h0
  rw [RingHom.mem_ker] at h0
  change mConeMapOver k (graphVec x' s') _ = 0 at h0
  rw [mConeMapOver_graphEq x' s' hf hh, mul_eq_zero, C_eq_zero, sub_eq_zero] at h0
  exact h0.resolve_right (mul_ne_zero (X_ne_zero _) (pow_ne_zero _ (X_ne_zero _)))

end GraphEq

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemClosureOfMemChartRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section Points

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ}

theorem chartRingOver_oneBlock (x : Fin (N + 1) → Ω) (c : Unit → Fin (N + 1)) (hi : x (c ()) ≠ 0) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c =
      Kleiman.chartRing (S := S) (x := x) (Kleiman.singleChart hi) := by
  have hChart : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x (c ()) =
      Kleiman.chartRing (S := S) (x := x) (Kleiman.singleChart hi) := by
    apply le_antisymm
    · rw [ReciprocityTheory.ChartRestriction.G.Geo.chartRing, Algebra.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      exact ⟨X j, X (c ()), 1, Kleiman.X_mem_monos (Finset.mem_singleton_self _),
        isHomogeneous_X S j, isHomogeneous_X S (c ()), by simp⟩
    · rintro _ ⟨f, s, e, hs, hf, hse, rfl⟩
      have hs₀ := Kleiman.eval_ne_zero_of_mem_monos (Kleiman.singleChart hi) hs
      have hsne : s ≠ 0 := fun he => hs₀ (by rw [he, map_zero])
      obtain ⟨e', hse', hden⟩ := TranslateEq.pow_div_mem_chartRingI S x
        (Kleiman.singleChart hi) (c ()) hs
      have he : e = e' := hse.inj_right hse' hsne
      subst e'
      change x (c ()) ^ e / aeval x s ∈
        IndefiniteRowSideFullHecke.Kleiman.chartRingI S x {c ()} at hden
      rw [IndefiniteRowSideFullHecke.Kleiman.chartRingI_singleton] at hden
      have hnum : aeval x f / x (c ()) ^ e ∈
          ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x (c ()) := by
        rw [← Kleiman.aeval_div_of_isHomogeneous hf, ReciprocityTheory.ChartRestriction.G.Geo.chartRing,
          ← MvPolynomial.aeval_range]
        exact ⟨f, rfl⟩
      have hquot : aeval x f / aeval x s =
          (aeval x f / x (c ()) ^ e) * (x (c ()) ^ e / aeval x s) := by
        field_simp
      rw [hquot]
      exact mul_mem hnum hden
  rw [← hChart]
  unfold chartRingOver ReciprocityTheory.ChartRestriction.G.Geo.chartRing
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(), a⟩, rfl⟩

end Points

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PModelGenericPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

namespace ModelGenericPoint

variable {O : Type} [CommRing O] {K : Type} {ι : K → Type} (P : Ideal (NumbersDVR.MRing ι O))

def genPt : (Σ k, ι k) → FractionRing (NumbersDVR.MRing ι O ⧸ P) :=
  fun p => algebraMap (NumbersDVR.MRing ι O ⧸ P) _ (Ideal.Quotient.mk P (X p))

theorem aeval_genPt (g : NumbersDVR.MRing ι O) :
    aeval (genPt P) g = algebraMap (NumbersDVR.MRing ι O ⧸ P)
      (FractionRing (NumbersDVR.MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) := by
  have h : (aeval (genPt P) : NumbersDVR.MRing ι O →ₐ[O] FractionRing (NumbersDVR.MRing ι O ⧸ P)) =
      (IsScalarTower.toAlgHom O (NumbersDVR.MRing ι O ⧸ P)
        (FractionRing (NumbersDVR.MRing ι O ⧸ P))).comp (Ideal.Quotient.mkₐ O P) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [genPt]
  rw [h]
  rfl

theorem aeval_genPt_eq_zero (g : NumbersDVR.MRing ι O) : aeval (genPt P) g = 0 ↔ g ∈ P := by
  rw [aeval_genPt, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

theorem genPt_ne_zero (p : Σ k, ι k) : genPt P p ≠ 0 ↔ (X p : NumbersDVR.MRing ι O) ∉ P := by
  rw [Ne, ← aeval_genPt_eq_zero, aeval_X]

theorem mIdealOver_genPt [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] [P.IsPrime]
    (hP : NumbersDVR.IsMultiHomogIdeal P) : mIdealOver O (genPt P) = P := by
  ext f
  constructor
  · intro hf
    have hc : ∀ b : K → ℕ, weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f ∈ P := by
      intro b
      rw [← aeval_genPt_eq_zero, ← coeff_mConeMapOver, RingHom.mem_ker.mp hf, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight ι) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    exact Ideal.sum_mem _ fun b _ => hc b
  · intro hf
    refine RingHom.mem_ker.mpr ?_
    ext m
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    have h := coeff_mConeMapOver (S := O) (genPt P) (⇑m) f
    rw [Finsupp.equivFunOnFinite_symm_coe] at h
    rw [h, aeval_genPt_eq_zero]
    exact hP f hf _

end ModelGenericPoint


end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XNotMemMIdealOver
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

def SectionRatio.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    (∃ i, x i ≠ 0) → IsGraphGen Q n s →
    ∀ W : Ideal (NumbersDVR.MRing (graphIdx N m) k), NumbersDVR.IsMultiProjPrime W →
      mIdealOver k (graphVec x s) ≤ W → ∀ j b : Fin m,
        (X ⟨Sum.inr (), j⟩ : NumbersDVR.MRing (graphIdx N m) k) ∉ W →
        ∃ (d : ℕ) (f g : Kleiman.Poly k N), f.IsHomogeneous d ∧ g.IsHomogeneous d ∧
          rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) g ∉ W ∧
          rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) g * X ⟨Sum.inr (), b⟩ -
            rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) f * X ⟨Sum.inr (), j⟩ ∈ W

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

