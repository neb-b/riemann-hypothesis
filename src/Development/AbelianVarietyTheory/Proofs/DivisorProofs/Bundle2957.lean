module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2504
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedQuasiLogBasisPDivGroupLieDual
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogBasis

section Gen

variable {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}
  (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)

theorem up_const (h : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) :
    constantCoeff (up E μ i) = 0 := by
  simp only [up, constantCoeff_map, h, map_zero]

def cobL (h : ∀ i, constantCoeff (μ i) = 0) :
    MvPowerSeries (Fin d) E →ₗ[E] MvPowerSeries (Fin d ⊕ Fin d) E where
  toFun := cob1 (up E μ)
  map_add' := formalCoboundary_add (up_const μ h)
  map_smul' := formalCoboundary_smul (up_const μ h)

theorem cobL_apply (h : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) E) :
    cobL μ h f = cob1 (up E μ) f := rfl

variable {μ}

theorem in_top_add {σ : Type} {f g : MvPowerSeries σ E} (hf : In (⊤ : Ideal O) f)
    (hg : In (⊤ : Ideal O) g) : In (⊤ : Ideal O) (f + g) := fun α => by
  obtain ⟨a, -, ha⟩ := hf α
  obtain ⟨b, -, hb⟩ := hg α
  exact ⟨a + b, trivial, by rw [map_add (f := _), ha, hb, map_add (f := _)]⟩

theorem in_top_sub {σ : Type} {f g : MvPowerSeries σ E} (hf : In (⊤ : Ideal O) f)
    (hg : In (⊤ : Ideal O) g) : In (⊤ : Ideal O) (f - g) := fun α => by
  obtain ⟨a, -, ha⟩ := hf α
  obtain ⟨b, -, hb⟩ := hg α
  exact ⟨a - b, trivial, by rw [map_sub, ha, hb, map_sub]⟩

theorem in_top_smul {σ : Type} {f : MvPowerSeries σ E} (a : O) (hf : In (⊤ : Ideal O) f) :
    In (⊤ : Ideal O) (algebraMap O E a • f) := fun α => by
  obtain ⟨b, -, hb⟩ := hf α
  exact ⟨a * b, trivial, by rw [map_smul, hb, smul_eq_mul, map_mul]⟩

theorem in_top_map {σ : Type} {f : MvPowerSeries σ E} (hf : In (⊤ : Ideal O) f) :
    ∃ s : MvPowerSeries σ O, f = map (algebraMap O E) s := by
  have hf' : ∀ α, ∃ b : O, coeff α f = algebraMap O E b := fun α => by
    obtain ⟨b, -, hb⟩ := hf α
    exact ⟨b, hb⟩
  choose s hs using hf'
  refine ⟨s, ?_⟩
  ext α
  exact (hs α).trans (coeff_map (algebraMap O E) α s).symm

theorem ql_zero (h : ∀ i, constantCoeff (μ i) = 0) : QL μ (⊤ : Ideal O) (0 : MvPowerSeries (Fin d) E) := by
  refine ⟨map_zero _, fun i => ⟨0, trivial, by simp [lin]⟩, fun α => ⟨0, trivial, ?_⟩⟩
  rw [← cobL_apply μ h, map_zero, map_zero, map_zero]

theorem ql_add_smul (h : ∀ i, constantCoeff (μ i) = 0) {f g : MvPowerSeries (Fin d) E}
    (hf : QL μ ⊤ f) (hg : QL μ ⊤ g) (a : O) : QL μ ⊤ (f + algebraMap O E a • g) := by
  refine ⟨?_, fun i => ?_, ?_⟩
  · have h1 := hf.1
    have h2 := hg.1
    rw [← coeff_zero_eq_constantCoeff_apply] at h1 h2 ⊢
    rw [map_add (f := _), map_smul, h1, h2, smul_zero, add_zero]
  · obtain ⟨a1, -, h1⟩ := hf.2.1 i
    obtain ⟨a2, -, h2⟩ := hg.2.1 i
    refine ⟨a1 + a * a2, trivial, ?_⟩
    simp only [lin] at h1 h2 ⊢
    rw [map_add (f := _), map_smul, h1, h2, smul_eq_mul, map_add (f := _), map_mul]
  · rw [← cobL_apply μ h, map_add (f := _), map_smul, cobL_apply, cobL_apply]
    exact in_top_add hf.2.2 (in_top_smul a hg.2.2)

theorem comb_sub {ι : Type} [Fintype ι] (e : ι → MvPowerSeries (Fin d) E) (b b' : ι → O) :
    comb (b - b') e = comb b e - comb b' e := by
  simp only [comb, Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib]

end Gen

section Chart

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (hv : v.Integers O)
  {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d) {E : Type} [CommRing E] [Algebra O E]
  (hE : IsFrame p E (RingHom.id O))
include hv hE

theorem isLie_add {f g : MvPowerSeries (Fin d) E} {l l' : G.dual.Lie} (hf : QL c.μ ⊤ f)
    (hg : QL c.μ ⊤ g) (hl : c.IsLie f l) (hl' : c.IsLie g l') (a : O) :
    c.IsLie (f + algebraMap O E a • g) (l + a • l') :=
  (_root_.GlobalTheory.LieLin.main p C v O hv G d c E hE f g l l' a hl hl').1 hf hg

theorem isLie_int {f : MvPowerSeries (Fin d) E} {l : G.dual.Lie} (hl : c.IsLie f l)
    (hs : ∃ s : MvPowerSeries (Fin d) O, f = map (algebraMap O E) s) : l = 0 :=
  (_root_.GlobalTheory.LieLin.main p C v O hv G d c E hE f f l l 0 hl hl).2.1 hs

theorem isLie_log {f : MvPowerSeries (Fin d) E} {l : G.dual.Lie} (hl : c.IsLie f l)
    (h : cob1 (up E c.μ) f = 0) : l = 0 :=
  (_root_.GlobalTheory.LieLin.main p C v O hv G d c E hE f f l l 0 hl hl).2.2 h

theorem isLie_zero : c.IsLie (0 : MvPowerSeries (Fin d) E) 0 := by
  obtain ⟨l, hl, -⟩ := _root_.GlobalTheory.QLogTangent.main p C v O hv G d c E hE 0 (ql_zero c.isLaw.const)
  rwa [isLie_int hv c hE hl ⟨0, (map_zero _).symm⟩] at hl

theorem isLie_comb {ι : Type} [Fintype ι] {e : ι → MvPowerSeries (Fin d) E} {L : ι → G.dual.Lie}
    (he : ∀ i, QL c.μ ⊤ (e i)) (hL : ∀ i, c.IsLie (e i) (L i)) (b : ι → O) :
    c.IsLie (comb b e) (∑ i, b i • L i) := by
  classical
  have h0 := c.isLaw.const
  suffices ∀ s : Finset ι, QL c.μ ⊤ (∑ i ∈ s, algebraMap O E (b i) • e i) ∧
      c.IsLie (∑ i ∈ s, algebraMap O E (b i) • e i) (∑ i ∈ s, b i • L i) from
    (this Finset.univ).2
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using ⟨ql_zero (E := E) h0, isLie_zero hv c hE⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_comm, add_comm (b a • L a)]
    exact ⟨ql_add_smul h0 ih.1 (he a) (b a), isLie_add hv c hE ih.1 (he a) ih.2 (hL a) (b a)⟩

theorem exists_isLie (l : G.dual.Lie) : ∃ f : MvPowerSeries (Fin d) E, QL c.μ ⊤ f ∧ c.IsLie f l := by
  have h0 := c.isLaw.const
  let M : Submodule O G.dual.Lie :=
    { carrier := {l | ∃ f : MvPowerSeries (Fin d) E, QL c.μ ⊤ f ∧ c.IsLie f l}
      add_mem' := by
        rintro l1 l2 ⟨f1, hf1, hl1⟩ ⟨f2, hf2, hl2⟩
        refine ⟨f1 + algebraMap O E 1 • f2, ql_add_smul h0 hf1 hf2 1, ?_⟩
        have := isLie_add hv c hE hf1 hf2 hl1 hl2 1
        rwa [one_smul] at this
      zero_mem' := ⟨0, ql_zero (E := E) h0, isLie_zero hv c hE⟩
      smul_mem' := by
        rintro a l ⟨f, hf, hl⟩
        refine ⟨0 + algebraMap O E a • f, ql_add_smul h0 (ql_zero (E := E) h0) hf a, ?_⟩
        have := isLie_add hv c hE (ql_zero (E := E) h0) hf (isLie_zero hv c hE) hl a
        simpa only [zero_add] using this }
  have hom := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  haveI := hom.1
  haveI := hom.2
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hp : Ideal.span {(p : O)} ≤ (⊥ : Ideal O).jacobson :=
    ((Ideal.span_singleton_le_iff_mem _).2 ((IsLocalRing.mem_maximalIdeal _).2
      (Fact.out : ¬IsUnit (p : O)))).trans (IsLocalRing.maximalIdeal_le_jacobson _)
  have htop : (⊤ : Submodule O G.dual.Lie) ≤ M := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hp fun x _ => ?_
    obtain ⟨f, l', l'', hf, hl', rfl⟩ := _root_.GlobalTheory.QLog.exists_isLie_add_smul p C v O hv G d c E hE x
    exact Submodule.add_mem_sup ⟨f, hf, hl'⟩
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top)
  exact htop Submodule.mem_top

end Chart

theorem adapted_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∃ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), IsBasis c.μ e ∧ IsAdapted (RingHom.id O) c.μ e ∧ (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) ∧ ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hE
  have h0 := c.isLaw.const
  have hom := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  haveI := hom.1
  haveI := hom.2
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : Module.Free O G.dual.omega := Module.free_of_flat_of_isLocalRing
  let lb := Module.finBasis O G.dual.Lie
  choose F hF using fun j => exists_isLie hv c hE (lb j)
  choose large₂ hLg using fun i : Fin d => _root_.GlobalTheory.QLog.exists_log_of_lin p O E hE d c.μ c.isLaw (Pi.single i 1)
  have hlin : ∀ i, lin (large₂ i) = Pi.single i 1 := fun i => funext fun i' => by
    rw [(hLg i).2.1 i', Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  let e : Fin d ⊕ Fin (Module.finrank O G.dual.Lie) → MvPowerSeries (Fin d) E := Sum.elim large₂ F
  have hQ : ∀ i, QL c.μ ⊤ (e i) := by
    rintro (i | j)
    · refine ⟨(hLg i).1, fun i' => ⟨_, trivial, (hLg i).2.1 i'⟩, fun α => ⟨0, trivial, ?_⟩⟩
      show coeff α (cob1 (up E c.μ) (large₂ i)) = _
      rw [(hLg i).2.2, map_zero, map_zero]
    · exact (hF j).1
  have hcob : ∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0 := fun i => (hLg i).2.2
  have hlin' : ∀ i, lin (e (Sum.inl i)) = Pi.single i 1 := hlin
  have hlie : ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := fun j => (hF j).2
  let L : Fin d ⊕ Fin (Module.finrank O G.dual.Lie) → G.dual.Lie := Sum.elim 0 lb
  have hL : ∀ i, c.IsLie (e i) (L i) := by
    rintro (i | j)
    · obtain ⟨l, hl, -⟩ := _root_.GlobalTheory.QLogTangent.main p C v O hv G d c E hE _ (hQ (Sum.inl i))
      rw [isLie_log hv c hE hl (hcob i)] at hl
      exact hl
    · exact hlie j
  have huniq : ∀ b : Fin d ⊕ Fin (Module.finrank O G.dual.Lie) → O, In (⊤ : Ideal O) (comb b e) → b = 0 := by
    intro b hb
    obtain ⟨s, hs⟩ := in_top_map hb
    have hl0 : ∑ i, b i • L i = 0 := isLie_int hv c hE (isLie_comb hv c hE hQ hL b) ⟨s, hs⟩
    have hr : ∀ j, b (Sum.inr j) = 0 := by
      have : ∑ j, b (Sum.inr j) • lb j = 0 := by simpa [Fintype.sum_sum_type, L] using hl0
      exact Fintype.linearIndependent_iff.1 lb.linearIndependent _ this
    have hc : cob1 (up E c.μ) (map (algebraMap O E) s) = 0 := by
      rw [← hs, ← cobL_apply c.μ h0]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [comb, map_sum, map_smul, Fintype.sum_sum_type, cobL_apply, hcob, hr]
    have hs0 := _root_.GlobalTheory.QLog.IntAdd.eq_zero_of_cob1_eq_zero p C v O hv G d c E hE s hc
    have hc0 : comb b e = 0 := by rw [hs, hs0, map_zero]
    have hl : ∀ i, b (Sum.inl i) = 0 := fun i => by
      have h1 := congrArg (coeff (Finsupp.single i 1)) hc0
      have hco : ∀ i', coeff (Finsupp.single i 1) (e (Sum.inl i')) = (Pi.single i' (1 : E) : Fin d → E) i :=
        fun i' => congrFun (hlin' i') i
      set_option synthInstance.maxHeartbeats 100000 in
        simp [comb, map_sum, Fintype.sum_sum_type, hr, hco, Pi.single_apply] at h1
      exact hE.inj (by rw [map_zero]; simpa [Algebra.smul_def] using h1)
    funext x
    cases x with
    | inl i => exact hl i
    | inr j => exact hr j
  refine ⟨Module.finrank O G.dual.Lie, e, lb, ⟨hQ, fun f hf => ?_⟩,
    fun i => ⟨fun α => ⟨0, (RingHom.mem_ker).2 (map_zero _), by rw [hcob i, map_zero, map_zero]⟩,
      hlin' i⟩, hcob, hlie⟩
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.QLog.Conv.generate_of_step p O E hE d c.μ c.isLaw _ e hQ
    (_root_.GlobalTheory.QLogStep.main p C v O hv G d c E hE _ e lb hQ hcob hlin' hlie) f hf
  refine ⟨b, hb, fun b' hb' => ?_⟩
  have h1 : In (⊤ : Ideal O) (comb (b' - b) e) := by
    rw [comb_sub]
    have := in_top_sub hb hb'
    rwa [sub_sub_sub_cancel_left] at this
  exact sub_eq_zero.1 (huniq _ h1)

end GlobalTheory.QLogBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedHeatConnectionOnAbelianFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn
open GlobalTheory.KS.GlueDer (rsT_eq res_app pre_mono)
open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_sub)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

theorem exists_descData : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) (ν : R), (∀ a, IsField ⊤ (dd a)) → (∀ a V r, dd a V (constFn Y.H.hom V r) = 0) → (∀ a α V f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∃ (V : h.J → Q.P.A.left.Opens) (E : h.J → Fld Q.P.A.left) (P : ∀ i, Γ(Q.P.A.left, V i)), (∀ i, h.W i = Y.q.left ⁻¹ᵁ V i) ∧ (∀ i, IsLift Q.P.A D (V i) (E i)) ∧ (∀ i V', V' ≤ V i → ∀ f, (Y.q.left.app V').hom (E i V' f) = GlobalTheory.HeatConn.dE h ν i _ ((Y.q.left.app V').hom f)) ∧ ∀ i, (Y.q.left.app (V i)).hom (P i) = rsT (GlobalTheory.HeatConn.pE h ν i) (Y.q.left ⁻¹ᵁ V i) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h ν hfield hconst hwt hB
  choose V hV using fun i => (hB i).1
  have hlift : ∀ i, IsLift Y.H D (Y.q.left ⁻¹ᵁ V i) (dE h ν i) := fun i => by
    rw [← hV i]
    refine ⟨isField_dE h ν hfield i, fun O hO r => ?_⟩
    show h.d i O _ + constFn Y.H.hom O ν * ∑ a, constFn Y.H.hom O (h.u a) * dd a O (constFn Y.H.hom O r) = _
    simp only [hconst, mul_zero, Finset.sum_const_zero, add_zero]
    exact (h.lift i).2 O hO r
  have hwt0 : ∀ i (V' : Q.P.A.left.Opens), V' ≤ V i → ∀ f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V') f →
      IsWt Y 0 (Y.q.left ⁻¹ᵁ V') (dE h ν i _ f) := by
    intro i V' hV' f hf
    exact WtAlg.isWt_add ((hB i).2.2.2 0 V' ((GlobalTheory.KS.GlueDer.pre_mono _ hV').trans (hV i).ge) f hf)
      (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ ν)
        (WtAlg.isWt_sum _ _ fun a _ => WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ _) (hwt a 0 _ f hf)))
  choose E hE hq using fun i => AbConst.exists_desc Y (V i) (dE h ν i) D (hlift i) (hwt0 i)
  have hP : ∀ i, ∃ a, (Y.q.left.app (V i)).hom a = rsT (pE h ν i) (Y.q.left ⁻¹ᵁ V i) := fun i => by
    refine AbConst.exists_app_eq Y ?_
    have hw : IsWt Y 0 (h.W i) (pE h ν i) :=
      WtAlg.isWt_add (hB i).2.1 (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ ν) (hB i).2.2.1)
    have tr : ∀ (W : Y.H.left.Opens) (s : Γ(Y.H.left, W)), W = Y.q.left ⁻¹ᵁ V i → IsWt Y 0 W s →
        IsWt Y 0 _ (rsT s (Y.q.left ⁻¹ᵁ V i)) := by
      rintro W s rfl hs
      rwa [WtAlg.rsT_self]
    exact tr _ _ (hV i) hw
  choose P hP using hP
  exact ⟨V, E, P, hV, hE, hq, hP⟩

theorem exists_glue_desc : ∀ {R K : Type} [CommRing R] [Field K] (G : Over (Sp R)) (A₀ : Over (Sp K)) (m₀ : A₀.left ⟶ G.left) (φ : R →+* K), m₀ ≫ G.hom = A₀.hom ≫ spMap φ → ∀ (D : R → R) {I : Type} (V : I → G.left.Opens), ⨆ i, V i = ⊤ → ∀ (E : I → Fld G.left), (∀ i, IsLift G D (V i) (E i)) → (∀ i i' O, O ≤ V i ⊓ V i' → ∀ f, (m₀.app O).hom (E i O f) = (m₀.app O).hom (E i' O f)) → ∃ ed : ∀ W : G.left.Opens, Γ(G.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom G.hom m₀ (fun r => φ (D r)) ⊤ ed ∧ ∀ i U, U ≤ V i → ∀ f, ed U f = (m₀.app U).hom (E i U f) := by
  intro R K _ _ G A₀ m₀ φ hm D I V hV E hE hc
  have hW : ∀ y, ∃ i, m₀ y ∈ V i := fun y => by
    have hy : m₀ y ∈ ⨆ i, V i := by rw [hV]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hy
  have he : ∀ i, GlobalTheory.KS.LocDerK A₀.hom G.hom m₀ (fun r => φ (D r)) (V i) (fun W f => (m₀.app W).hom (E i W f)) := by
    intro i
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h' hW f => ?_, fun W hW r => ?_⟩
    · rw [(hE i).1.1 W hW, map_add (f := _)]
    · rw [(hE i).1.2.1 W hW, map_add (f := _), map_mul, map_mul]
    · rw [(hE i).1.2.2 W W' h' hW, GlobalTheory.KS.GlueDer.rsT_eq (GlobalTheory.KS.GlueDer.pre_mono m₀ h'), GlobalTheory.KS.GlueDer.res_app m₀ h']
    · rw [(hE i).2 W hW, GlobalTheory.KS.GlueDer.app_const φ _ _ m₀ hm]
  obtain ⟨ed, hed, hchar⟩ := GlobalTheory.InteriorKS.glue_along A₀.hom G.hom m₀ (fun r => φ (D r)) V hW
    (fun i W f => (m₀.app W).hom (E i W f)) he fun i i' O hO f => hc i i' O hO f
  refine ⟨ed, hed, fun i U hU f => hchar U f _ fun i' => ?_⟩
  have h1 := (he i).res U (U ⊓ V i') inf_le_left hU f
  rw [GlobalTheory.KS.GlueDer.rsT_eq (GlobalTheory.KS.GlueDer.pre_mono m₀ inf_le_left)] at h1
  rw [← h1]
  exact hc i i' _ (le_inf (inf_le_left.trans hU) inf_le_right) _

theorem connK_transition : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] {φ : R →+* K} {e : ℕ} {ν : R} {A₀ : Over (Sp K)} [GrpObj A₀] {m₀ : A₀.left ⟶ Q.P.A.left}, GlobalTheory.HeatConn.IsFibre Y h φ e ν A₀ m₀ → ∀ {V : h.J → Q.P.A.left.Opens} {ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)} {pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)}, GlobalTheory.HeatConn.IsDesc Y h ν m₀ V ed pb → (∀ i, V i ≤ Q.P.L.U (h.j i)) → ∀ (i i' : h.J), ed (V i ⊓ V i') (rsT (Q.P.L.g (h.j i) (h.j i')).val (V i ⊓ V i')) = pbT m₀ (Q.P.L.g (h.j i) (h.j i')).val (m₀ ⁻¹ᵁ (V i ⊓ V i')) * (rsT (pb i') (m₀ ⁻¹ᵁ (V i ⊓ V i')) - rsT (pb i) (m₀ ⁻¹ᵁ (V i ⊓ V i'))) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hD hV i i'
  have he0 : e ≠ 0 := by
    rintro rfl
    have := hF.inv
    rw [Nat.cast_zero, mul_zero] at this
    exact zero_ne_one this
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he0
  have hUL : V i ⊓ V i' ≤ Q.P.L.U (h.j i) ⊓ Q.P.L.U (h.j i') := inf_le_inf (hV i) (hV i')
  refine ext_lift Y m₀ fun Z a b w z hz => ?_
  have hz' : (a ≫ Y.q.left) z ∈ V i ⊓ V i' := by rw [w]; exact hz
  have haΩ : a z ∈ Y.q.left ⁻¹ᵁ (V i ⊓ V i') := hz'
  have hΩW : Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ h.W i ⊓ h.W i' := by
    rw [hD.1 i, hD.1 i']; exact le_inf (pre_mono _ inf_le_left) (pre_mono _ inf_le_right)
  have hΩL : Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ Y.q.left ⁻¹ᵁ (Q.P.L.U (h.j i) ⊓ Q.P.L.U (h.j i')) := pre_mono _ hUL
  have hG : (Y.q.left.app (V i ⊓ V i')).hom (rsT (Q.P.L.g (h.j i) (h.j i')).val (V i ⊓ V i')) =
      pbT Y.q.left (Q.P.L.g (h.j i) (h.j i')).val (Y.q.left ⁻¹ᵁ (V i ⊓ V i')) := by
    rw [rsT_eq hUL, ← res_app Y.q.left hUL (pre_mono _ hUL), pbT, dif_pos hΩL]; rfl
  have hz1 : (b ≫ m₀) z ∈ V i := hz.1
  have hz2 : (b ≫ m₀) z ∈ V i' := hz.2
  rw [hD.2.1 Z a b w z i _ inf_le_left hz, hG, gs_mul b z _ hz, gs_sub b z _ hz, gs_pbT b m₀ z (pre_mono _ hUL) hz,
    gs_rsT b z (pre_mono m₀ inf_le_right) hz, gs_rsT b z (pre_mono m₀ inf_le_left) hz, hD.2.2 Z a b w z i' hz2,
    hD.2.2 Z a b w z i hz1, ← w, ← gs_pbT a Y.q.left z hΩL haΩ, ← gs_rsT a z (hΩW.trans inf_le_right) haΩ,
    ← gs_rsT a z (hΩW.trans inf_le_left) haΩ]
  simp only [gs_eq_gsH a z _ haΩ]
  set π := gsH a z _ haΩ
  set G := pbT Y.q.left (Q.P.L.g (h.j i) (h.j i')).val (Y.q.left ⁻¹ᵁ (V i ⊓ V i'))
  have hΘ : ∀ a' b', π (constFn Y.H.hom _ (h.Θ a' b')) = 0 := fun a' b' => by
    rw [← gs_eq_gsH, hF.gs_const w z _ haΩ, hF.symb, cst_eq_cstH, map_zero]
  have hpow : ∀ (m : ℕ) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ (V i ⊓ V i'))),
      dE h ν i _ (f ^ (m + 1)) = ((m + 1 : ℕ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ (V i ⊓ V i'))) * f ^ m * dE h ν i _ f := by
    intro m f
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, (isField_dE h ν hF.field i).2.1 _ (hΩW.trans inf_le_left), ih]
      push_cast; ring
  have e1 := congrArg π (h.glue (k + 1) i i' _ hΩW 1)
  rw [_root_.mul_one, map_op h ν (k + 1) hF.inv i _ (hΩW.trans inf_le_left) π hΘ, map_mul,
    map_op h ν (k + 1) hF.inv i' _ (hΩW.trans inf_le_right) π hΘ, hpow,
    AbConst.isField_one (isField_dE h ν hF.field i') (hΩW.trans inf_le_right)] at e1
  simp only [map_mul, map_pow, map_natCast, map_one, map_zero, zero_add, _root_.mul_one] at e1
  have h2 : IsUnit (2 : Z.presheaf.stalk z) := by
    simpa only [map_ofNat] using (two_ne_zero (α := K)).isUnit.map (cstH (b ≫ A₀.hom) z)
  have hk : IsUnit (((k + 1 : ℕ)) : Z.presheaf.stalk z) := by
    simpa only [map_natCast] using
      (Nat.cast_ne_zero.2 (Nat.succ_ne_zero k) : ((k + 1 : ℕ) : K) ≠ 0).isUnit.map (cstH (b ≫ A₀.hom) z)
  have hGu : IsUnit G := by
    simp only [G, pbT, dif_pos hΩL]; exact (Units.isUnit _).map _
  have hc : IsUnit (2 * ((k + 1 : ℕ) : Z.presheaf.stalk z) ^ 2 * π G ^ k) := (h2.mul (hk.pow 2)).mul ((hGu.map π).pow k)
  refine hc.mul_left_cancel ?_
  push_cast at e1 ⊢
  linear_combination e1

theorem exists_connK_desc : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∃ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb ∧ IsDesc Y h ν m₀ V ed pb := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF
  have := (AbConst.surjective_q Y).1
  obtain ⟨V, E, P, hW, hE, hq, hP⟩ := exists_descData Y h ν hF.field hF.const hF.wt hF.basic
  have hm : m₀ ≫ Q.P.A.hom = A₀.hom ≫ spMap φ := hF.pull.1.w
  have hcov : ⨆ i, V i = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, rfl⟩ := Y.q.left.surjective x
    have hy : y ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    rw [hW] at hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  have hVL : ∀ i, V i ≤ Q.P.L.U (h.j i) := fun i x hx => by
    obtain ⟨y, rfl⟩ := Y.q.left.surjective x
    have hy : y ∈ h.W i := by rw [hW]; exact hx
    exact h.le i hy
  have hc : ∀ i i' O, O ≤ V i ⊓ V i' → ∀ f, (m₀.app O).hom (E i O f) = (m₀.app O).hom (E i' O f) := by
    intro i i' O hO f
    refine ext_lift Y m₀ fun Z a b w z hz => ?_
    have hz' : (a ≫ Y.q.left) z ∈ O := by rw [w]; exact hz
    rw [gs_pull b m₀ z O hz, gs_pull b m₀ z O hz, ← w, ← gs_pull a Y.q.left z O hz', ← gs_pull a Y.q.left z O hz',
      hq i O (hO.trans inf_le_left), hq i' O (hO.trans inf_le_right)]
    refine hF.dE_agree w z i i' _ ?_ hz' _
    rw [hW i, hW i']
    exact le_inf (GlobalTheory.KS.GlueDer.pre_mono _ (hO.trans inf_le_left)) (GlobalTheory.KS.GlueDer.pre_mono _ (hO.trans inf_le_right))
  obtain ⟨ed, hed, hedE⟩ := exists_glue_desc Q.P.A A₀ m₀ φ hm D V hcov E hE hc
  let pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i) := fun i => (m₀.app (V i)).hom (P i)
  have hD : IsDesc Y h ν m₀ V ed pb := by
    refine ⟨hW, fun Z a b w z i U hU hz f => ?_, fun Z a b w z i hz => ?_⟩
    · have hz' : (a ≫ Y.q.left) z ∈ U := by rw [w]; exact hz
      rw [hedE i U hU f, gs_pull b m₀ z U hz, ← w, ← gs_pull a Y.q.left z U hz', hq i U hU f]
    · have hz' : (a ≫ Y.q.left) z ∈ V i := by rw [w]; exact hz
      show gs b z _ ((m₀.app (V i)).hom (P i)) = _
      rw [gs_pull b m₀ z (V i) hz, ← w, ← gs_pull a Y.q.left z (V i) hz', hP i]
      exact GlobalTheory.KS.DlogPol.gs_rsT a z (hW i).ge hz' _
  exact ⟨V, ed, pb, ⟨hed, hcov, hVL, fun i i' => connK_transition Y h hF hD hVL i i'⟩, hD⟩

end GlobalTheory.HeatConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericEndomorphismMumfordRingAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.GenericEnd.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), ∃ f : A.A ⟶ A.A, IsMonHom f ∧ ∀ g : G ⟶ G, IsMonHom g → (Over.pullback (jK R)).map g ≫ U.gen.hom = U.gen.hom ≫ f → ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g := by
  intro R _ _ _ hB D A G _ _ hG U O _ _ _ o a
  have hE := (GlobalTheory.Mum.endData_symm_and_ofOAct R D.toPre).2 O o a
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.Mum.EndThick.formalEnd_exists R hB.1 D A G hG U _ _ _ _ hE
  obtain ⟨g, hg, hgb⟩ := _root_.GlobalTheory.Mum.formalEnd_algebraic R hB D A G hG U _ _ _ _ hE b hb
  obtain ⟨f, hf, hact⟩ := GlobalTheory.Mum.GenericEnd.exists_generic_of_formal U.toUnifPre (o.onB.act a)
    (DistribSMul.toAddMonoidHom D.toPre.X (star a)) b hb g hg hgb
  have hfun : (⇑(DistribSMul.toAddMonoidHom D.toPre.X (star a)) : D.toPre.X → D.toPre.X) = fun χ => star a • χ :=
    funext fun χ => DistribSMul.toAddMonoidHom_apply _ _ χ
  rw [hfun] at hact
  exact ⟨f, hf, hact⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGridDatumPureTensorVacuaAEStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gridDatum_pureTensor_vacuaAE : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB ∧
      ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F v) → ℂ)
        (φ₀ : (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ),
        ΦB = ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ k, ∀ᶠ v in Filter.cofinite, φ k v = Γ.M'.vac v) ∧
        (∀ k, φ k Bs.v₁ = φ₀) ∧ φ₀ ∈ GlobalTheory.WeilM.SB _ ∧ φ₀ ≠ 0 ∧
        ∃ (L₁ : Submodule (𝓞 D.host.E) (Fin (G.V (.grid i j)).rank → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → D.host.E))
          (θ : 𝓞 D.host.E), (θ : D.host.E) + D.sp.cm.sig θ = 1 ∧ (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)) ∧
          ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀ := by
  first | exact @GlobalTheory.SmallDatumVac.exists_datum_pure_vac | exact GlobalTheory.SmallDatumVac.exists_datum_pure_vac | (intros; apply GlobalTheory.SmallDatumVac.exists_datum_pure_vac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelAdjointActionPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principal_siegel_adjoint_action_pullback : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (bar : O → O) (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B) (f : S' ⟶ S) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A)), f ≫ s = s' → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → ∃ (w : SiegPre h M ζ s') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act f := by
  first | (exact @GlobalTheory.UPel.HT.siegPre_actPB_pullback) | (exact GlobalTheory.UPel.HT.siegPre_actPB_pullback) | (intros; apply GlobalTheory.UPel.HT.siegPre_actPB_pullback  <;> assumption)
end

