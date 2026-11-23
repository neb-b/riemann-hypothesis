module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0062
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0052
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OfPowRealises
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

theorem ModelMulSecs.of_powRealises (h : PowRealises.Statement) : ModelMulSecs.Statement :=
  fun F _ K _ _ ι _ Ω _ _ y k₀ N e hmod β Q hQ p j => h F K ι Ω y k₀ N e _ rfl hmod Q β hQ p j

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OneMemSecOverZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver GeneratesOver)

def ModelChangeGen.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
    IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
    ∀ (β : K → ℤ) (β' : K' → ℤ),
      (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
          secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
      ∀ (n : ℕ) (h : Fin n → Ω), (∀ j, h j ∈ secOver F y β) →
        (GeneratesOver F y β h ↔ GeneratesOver F y' β' h)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqSegreRealise
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

theorem SegreRealise.proof (hB : SegreBase.Statement) (hT : SegreTwist.Statement) (hD : SegreDim.Statement)
    (hNf : SegreNef.Statement) (hNm : SegreNum.Statement) (hBd : BundleOfDeg.Statement)
    (hMD : ModelDimEq.Statement) (hMN : ModelNefEq.Statement) (hMNum : ModelNumEq.Statement) :
    SegreRealise.Statement := by
  classical
  intro F _ K _ _ ι _ Ω _ _ y d μs hy hd
  have : ∀ a, Nonempty (ι a) := fun a => ⟨(hy a).choose⟩
  have hcard : 0 < Fintype.card (∀ a, ι a) := Fintype.card_pos
  let N := Fintype.card (∀ a, ι a) - 1
  let eqv : (∀ a, ι a) ≃ Fin (N + 1) := Fintype.equivFinOfCardEq (by omega)
  have hbase : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F (segreJoin y) (Sum.inl ()) := (hB F K ι Ω y hy).1
  choose Ms hMs using fun j =>
    hBd F (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ()) N eqv hbase (IndefiniteRowSideFullHecke.Kleiman2.pullDeg (μs j))
  have hsub : Kleiman.IsSubvar (IndefiniteRowSideFullHecke.Kleiman2.blockVec (segreJoin y) (Sum.inl ()) ∘ eqv.symm)
      (Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (segreJoin y) (Sum.inl ()) ∘ eqv.symm)) d :=
    (hMD F _ _ Ω (segreJoin y) (Sum.inl ()) N eqv hbase d).2 (by rw [hD F K ι Ω y hy]; exact hd)
  refine ⟨N, eqv, IndefiniteRowSideFullHecke.Kleiman2.blockVec (segreJoin y) (Sum.inl ()) ∘ eqv.symm, Ms, fun i => ?_, hsub,
    fun j c => ?_, fun j => ?_, ?_⟩
  · show ∏ a, y ⟨a, eqv.symm (eqv i) a⟩ = ∏ a, y ⟨a, i a⟩
    rw [Equiv.symm_apply_apply]
  · exact (hMs j c).trans (hT F K ι Ω y hy (μs j) c)
  · exact (hMN F _ _ Ω (segreJoin y) (Sum.inl ()) N eqv hbase _ (Ms j) (hMs j)).trans (hNf F K ι Ω y hy (μs j))
  · exact (hMNum F _ _ Ω (segreJoin y) (Sum.inl ()) N eqv hbase d (fun j => IndefiniteRowSideFullHecke.Kleiman2.pullDeg (μs j)) Ms
      hMs hsub).trans (hNm F K ι Ω y hy d μs)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ProdExp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

section Model

variable {Ω : Type} [Field Ω] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem TensorRealises.prod_exp (y : (Σ k, ι k) → Ω) (k₀ : K) (β β' : K → ℤ) (c d : ℤ)
    (cc : ∀ k, ι k) (hc : ∀ k, y ⟨k, cc k⟩ ≠ 0) :
    y ⟨k₀, cc k₀⟩ ^ (-d) * ((∏ k, y ⟨k, cc k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) *
        ∏ k, y ⟨k, cc k⟩ ^ (-(β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) =
      ∏ k, y ⟨k, cc k⟩ ^ (-(β + β' + (2 * c + d) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) := by
  have h0 : y ⟨k₀, cc k₀⟩ ^ (-d) = ∏ k, y ⟨k, cc k⟩ ^ (-(d • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) := by
    rw [Finset.prod_eq_single k₀]
    · simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
    · intro k _ hk
      simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg, hk]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h0, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_add₀ (hc k), ← zpow_add₀ (hc k)]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Model

theorem TensorRealises.proof (hG : ModelGenerated.Statement) (hS : SpanSecs.Statement) :
    TensorRealises.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod L L' β β' hL hL' ct
  obtain ⟨a₀, ha₀⟩ := Kleiman.Generated.full F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) L
  obtain ⟨a₁, ha₁⟩ := Kleiman.Generated.full F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) L'
  obtain ⟨b₀, hb₀⟩ := hG F K ι Ω y k₀ hmod β
  obtain ⟨b₁, hb₁⟩ := hG F K ι Ω y k₀ hmod β'
  obtain ⟨c, h0, h1, h2, h3⟩ : ∃ c, a₀ ≤ c ∧ a₁ ≤ c ∧ b₀ ≤ c ∧ b₁ ≤ c :=
    ⟨max (max a₀ a₁) (max b₀ b₁), by omega, by omega, by omega, by omega⟩
  have hgL := ha₀ c h0
  have hgL' := ha₁ c h1
  have hgY := hb₀ c h2
  have hgY' := hb₁ c h3
  obtain ⟨d, rfl⟩ : ∃ d, ct = 2 * c + d := ⟨ct - 2 * c, by ring⟩
  have hchart : ∀ I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm),
      ((L.tensor L').toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (2 * c + d))).sub I =
        Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I)
            ((secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) *
              (secOver F y (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) * Kleiman.twistMod F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) d I := by
    intro I
    have e1 : (L.toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).sub I =
        Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) := by
      rw [← hgL I, hL c]
    have e2 : (L'.toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).sub I =
        Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I) (secOver F y (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) := by
      rw [← hgL' I, hL' c]
    rw [PowRealises.twist_sub, PowRealises.twistSys_sub] at e1 e2
    show ((L.toSubSystem.twist L'.toSubSystem).twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (2 * c + d))).sub I = _
    rw [PowRealises.twist_sub, PowRealises.twistSys_sub, PowRealises.twist_sub, ← Submodule.span_mul_span, ← e1,
      ← e2, two_mul, ← PowRealises.twistMod_mul, ← PowRealises.twistMod_mul]
    ring
  have hsecs : ((L.tensor L').toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (2 * c + d))).secs =
      ⨅ I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm), (Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I)
          ((secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) *
            (secOver F y (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) *
          Kleiman.twistMod F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) d I).restrictScalars F := by
    simp only [Kleiman.SubSystem.secs, hchart]
  ext s
  rw [hsecs, hS F K ι Ω y k₀ N e _ rfl hmod _ d s, PowRealises.mem_secOver]
  refine forall_congr' fun cc => forall_congr' fun hc => ?_
  have hu : (∏ k, y ⟨k, cc k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  have hu' : (∏ k, y ⟨k, cc k⟩ ^ (-(β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  rw [← Submodule.span_mul_span, PowRealises.span_secOver_eq y _ hgY cc hc,
    PowRealises.span_secOver_eq y _ hgY' cc hc, Submodule.span_mul_span, Set.singleton_mul_singleton, ← mul_inv,
    PowRealises.mem_span_inv_iff _ (mul_ne_zero hu hu'), mul_assoc, TensorRealises.prod_exp y k₀ β β' c d cc hc]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperComponentMulX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart CechC)

noncomputable section

section Lemmas

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

attribute [local instance] MvPolynomial.weightedGradedAlgebra


omit [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] in
theorem snapper_component_mul_X [DecidableEq K] (f : MvPolynomial (Σ k, ι k) F) (b : K → ℕ) (v : Σ k, ι k) :
    weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (b + NumbersDVR.blockWeight ι v) (f * X v) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f * X v := by
  have h := DirectSum.coe_decompose_mul_add_of_right_mem
    (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι)) (a := f) (i := b)
    (isWeightedHomogeneous_X F (NumbersDVR.blockWeight ι) v)
  have key : ∀ (φ : MvPolynomial (Σ k, ι k) F) (c : K → ℕ),
      (DirectSum.decompose (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι)) φ c :
        MvPolynomial (Σ k, ι k) F) = weightedHomogeneousComponent (NumbersDVR.blockWeight ι) c φ :=
    fun φ c => weightedDecomposition.decompose'_apply F (NumbersDVR.blockWeight ι) φ c
  rw [key, key] at h
  exact h


omit [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] in
theorem snapper_colon_X [DecidableEq K] {J : Ideal (MvPolynomial (Σ k, ι k) F)} (hJ : NumbersDVR.IsMultiHomogIdeal J)
    (v : Σ k, ι k) : NumbersDVR.IsMultiHomogIdeal (J.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)})) := by
  intro f hf b
  rw [Submodule.mem_colon_span_singleton, smul_eq_mul] at hf ⊢
  rw [← snapper_component_mul_X]
  exact hJ _ hf _


omit [Fintype K] [LinearOrder K] in
theorem snapper_eval_shift (p : MvPolynomial K ℚ) (e m : K → ℤ) :
    eval (fun k => ((m - e) k : ℚ)) p =
      eval (fun k => (m k : ℚ)) (bind₁ (fun j => X j - C ((e j : ℤ) : ℚ)) p) := by
  have hb : ∀ (x : K → ℚ) (g : K → MvPolynomial K ℚ), eval x (bind₁ g p) = eval (fun j => eval x (g j)) p :=
    fun x g => eval₂Hom_bind₁ _ _ _ _
  rw [hb]
  refine congrArg (fun x => eval x p) (funext fun j => ?_)
  simp

theorem snapper_top (V : Ideal (MvPolynomial (Σ k, ι k) F)) (m : K → ℤ) (n : ℕ)
    (hn : ∑ k, (Fintype.card (ι k) - 1) < n) : Subsingleton (cechHc ι (quotPart F V) m n) := by
  have hI : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n, False := fun I => by
    have h1 : ∑ k, ((I.1 k).card - 1) ≤ ∑ k, (Fintype.card (ι k) - 1) :=
      Finset.sum_le_sum fun k _ => Nat.sub_le_sub_right (Finset.card_le_univ _) 1
    have := I.2.2
    omega
  have : Subsingleton (CechC F ι (MvPolynomial (Σ k, ι k) F ⧸ V) n) :=
    ⟨fun f g => funext fun I => (hI I).elim⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subsingleton.elim x y]

theorem snapper_finite (hS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement) (V : Ideal (MvPolynomial (Σ k, ι k) F))
    (hV : NumbersDVR.IsMultiHomogIdeal V) (m : K → ℤ) (i : ℕ) :
    FiniteDimensional F (cechHc ι (quotPart F V) m i) :=
  (hS F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance
    (HilbertSamuel.QuotPartGraded.proof F K ι V ((NumbersDVR.Objects.isMultiHomogIdeal_iff V).1 hV))).1 m i

end Lemmas

theorem EulerPoly.proof (hS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement) (hE : EulerVar.Statement)
    (hD : PolyOfDiffsExact.Statement) : EulerPoly.Statement := by
  intro F _ K _ _ ι _ _ V hV
  have hfin : ∀ J : Ideal (MvPolynomial (Σ k, ι k) F), NumbersDVR.IsMultiHomogIdeal J →
      ∀ (m : K → ℤ) (i : ℕ), FiniteDimensional F (cechHc ι (quotPart F J) m i) :=
    fun J hJ => snapper_finite hS J hJ
  have key : ∀ J : Ideal (MvPolynomial (Σ k, ι k) F), NumbersDVR.IsMultiHomogIdeal J →
      ∃ p : MvPolynomial K ℚ, ∀ m, eulerChar F ι J m = eval (fun k => (m k : ℚ)) p := by
    intro J hJ
    refine IsNoetherian.induction (P := fun J : Ideal (MvPolynomial (Σ k, ι k) F) =>
      NumbersDVR.IsMultiHomogIdeal J → ∃ p : MvPolynomial K ℚ, ∀ m, eulerChar F ι J m = eval (fun k => (m k : ℚ)) p)
      (fun J ih hJ => ?_) J hJ
    have hlt2 : ∀ v : Σ k, ι k, (X v : MvPolynomial (Σ k, ι k) F) ∉ J →
        J < J ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)} := fun v hvJ =>
      lt_of_le_of_ne le_sup_left fun h => hvJ (h ▸ Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hSup : ∀ v : Σ k, ι k, NumbersDVR.IsMultiHomogIdeal (J ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) :=
      fun v => FieldNumbers.isMultiHomogIdeal_sup_span hJ (isWeightedHomogeneous_X F (NumbersDVR.blockWeight ι) v)
    by_cases hA : ∃ v : Σ k, ι k, (X v : MvPolynomial (Σ k, ι k) F) ∉ J ∧
        J.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) ≠ J
    · obtain ⟨v, hvJ, hne⟩ := hA
      have hle : J ≤ J.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) := fun f hf => by
        rw [Submodule.mem_colon_span_singleton, smul_eq_mul]
        exact Ideal.mul_mem_right _ J hf
      obtain ⟨p1, hp1⟩ := ih _ (lt_of_le_of_ne hle (Ne.symm hne)) (snapper_colon_X hJ v)
      obtain ⟨p2, hp2⟩ := ih _ (hlt2 v hvJ) (hSup v)
      refine ⟨bind₁ (fun j => X j - C (((Pi.single v.1 1 : K → ℤ) j : ℤ) : ℚ)) p1 + p2, fun m => ?_⟩
      rw [hE F K ι J v hJ (hfin J hJ) (hfin _ (snapper_colon_X hJ v)) (hfin _ (hSup v)) m, hp1, hp2, map_add (f := _),
        ← snapper_eval_shift]
    · push Not at hA
      by_cases hB : ∃ k, ∀ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ J
      · obtain ⟨k, hk⟩ := hB
        refine ⟨0, fun m => ?_⟩
        rw [map_zero, eulerChar]
        refine Finset.sum_eq_zero fun i _ => ?_
        have := cechHc_subsingleton_of_block hk m i
        rw [Module.finrank_zero_of_subsingleton]
        simp
      · push Not at hB
        refine hD K (eulerChar F ι J) fun k => ?_
        obtain ⟨i, hi⟩ := hB k
        obtain ⟨q, hq⟩ := ih _ (hlt2 ⟨k, i⟩ hi) (hSup ⟨k, i⟩)
        refine ⟨q, fun m => ?_⟩
        have h := hE F K ι J ⟨k, i⟩ hJ (hfin J hJ) (hfin _ (snapper_colon_X hJ _)) (hfin _ (hSup _)) m
        rw [hA _ hi] at h
        rw [← hq m]
        linarith
  obtain ⟨p, hp⟩ := key V hV
  exact ⟨∑ k, (Fintype.card (ι k) - 1), p, hfin V hV, fun m i hi => snapper_top V m i hi, hp⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

