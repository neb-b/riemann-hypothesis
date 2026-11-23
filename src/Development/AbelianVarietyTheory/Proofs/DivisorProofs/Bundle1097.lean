module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1087
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0953
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0952
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0985
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import GroundTheory.AutomorphicForms.Iwasawa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvConjTMul
section
noncomputable section

open MeasureTheory MvPolynomial
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1
open scoped InnerProductSpace

namespace GlobalTheory.PsCo.Pc3.RK

def linT (n : ℕ) : (Fin n × Fin n) ⊕ (Fin n × Fin n) → MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) (Poly n)
  | Sum.inl x => ∑ l, X (Sum.inr (l, x.1)) * C (X (Sum.inl (l, x.2)))
  | Sum.inr x => ∑ l, X (Sum.inl (l, x.1)) * C (X (Sum.inr (l, x.2)))

def TT (n : ℕ) : Poly n →ₐ[ℂ] MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) (Poly n) := aeval (linT n)

theorem TT_deg {n : ℕ} (P : Poly n) : (TT n P).totalDegree ≤ P.totalDegree := by
  first
  | exact @_root_.GlobalTheory.TotalDegreeBounds.main
  | exact _root_.GlobalTheory.TotalDegreeBounds.main
  | (apply _root_.GlobalTheory.TotalDegreeBounds.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.TotalDegreeBounds.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TotalDegreeBounds.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TotalDegreeBounds.main ..)

theorem ev_conjT_mul {n : ℕ} (A M : Mat n) (P : Poly n) :
    ev (A.conjTranspose * M) P =
      eval (Sum.elim (fun x => A x.1 x.2) (fun x => star (A x.1 x.2))) (map (ev M) (TT n P)) := by
  have h : (ev (A.conjTranspose * M) : Poly n →+* ℂ) =
      (eval (Sum.elim (fun x => A x.1 x.2) (fun x => star (A x.1 x.2)))).comp
        ((map (ev M)).comp (TT n).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
    · simp [ev, TT, MvPolynomial.algebraMap_eq]
    · rcases v with x | x
      · simp [ev, TT, linT, Matrix.mul_apply]
      · simp [ev, TT, linT, Matrix.mul_apply]
  exact congrArg (fun f : Poly n →+* ℂ => f P) h

theorem eval_map_eq {n : ℕ} (x : (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ) (f : Poly n →+* ℂ)
    (p : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) (Poly n)) :
    eval x (map f p) = ∑ s ∈ p.support, f (AddMonoidAlgebra.coeff p s) * eval x (monomial s 1) := by
  conv_lhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_monomial, eval_monomial, one_mul]

end GlobalTheory.PsCo.Pc3.RK

namespace GlobalTheory.PsCo.Pc3

open RK

theorem rangeK : RangeK := by
  classical
  intro n ε U _ _ _ π hπ P
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hφc : Continuous fun k : KG ε => toMK k := hemb.continuous
  have hevc : ∀ Q : Poly n, Continuous fun k : KG ε => ev (toMK k) Q := by
    intro Q
    have hent : Continuous fun k : KG ε =>
        (Sum.elim (fun x => toMK k x.1 x.2) (fun x => star (toMK k x.1 x.2)) :
          (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ) := by
      refine continuous_pi fun i => ?_
      rcases i with x | x
      · exact (continuous_apply x.2).comp ((continuous_apply x.1).comp hφc)
      · exact continuous_star.comp ((continuous_apply x.2).comp ((continuous_apply x.1).comp hφc))
    exact (MvPolynomial.continuous_eval Q).comp hent
  have horb : ∀ v : U, Continuous fun k : KG ε => π k v :=
    fun v => (hπ.continuous_apply v).comp continuous_subtype_val
  have hint : ∀ (Q : Poly n) (v : U), Integrable (fun k : KG ε => ev (toMK k) Q • π k v) (muK ε) :=
    fun Q v => ((hevc Q).smul (horb v)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hintC : ∀ g : KG ε → ℂ, Continuous g → Integrable g (muK ε) :=
    fun g hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨M, hM⟩ := (isCompact_univ.image (hevc P)).isBounded.exists_norm_le
  have hMb : ∀ k : KG ε, ‖ev (toMK k) P‖ ≤ M := fun k => hM _ ⟨k, Set.mem_univ _, rfl⟩
  let Bl : U →ₗ[ℂ] U :=
    { toFun := fun v => ∫ k, ev (toMK k) P • π k v ∂(muK ε)
      map_add' := fun v w => by
        simp only [map_add (f := _), smul_add]
        exact integral_add (hint P v) (hint P w)
      map_smul' := fun c v => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun k => smul_comm _ _ _) }
  let B : U →L[ℂ] U := Bl.mkContinuous (M * ((muK ε) Set.univ).toReal) fun v => by
    change ‖∫ k, ev (toMK k) P • π k v ∂(muK ε)‖ ≤ _
    have := norm_integral_le_of_norm_le_const (μ := muK ε) (C := M * ‖v‖)
      (f := fun k : KG ε => ev (toMK k) P • π k v) (Filter.Eventually.of_forall fun k => by
        rw [norm_smul, hπ.norm_apply]
        exact mul_le_mul_of_nonneg_right (hMb k) (norm_nonneg v))
    calc _ ≤ M * ‖v‖ * ((muK ε) Set.univ).toReal := this
      _ = M * ((muK ε) Set.univ).toReal * ‖v‖ := by ring
  refine ⟨B, fun v => ⟨hint P v, rfl⟩, fun u l => ?_⟩
  set p := TT n P with hp
  let f : KG ε → ℂ := fun k => ⟪l, π k u⟫_ℂ
  have hfc : Continuous f := continuous_const.inner (horb u)
  let c : _ → ℂ := fun s => ∫ k, ev (toMK k) (AddMonoidAlgebra.coeff p s) * f k ∂(muK ε)
  refine ⟨∑ s ∈ p.support, C (c s) * monomial s 1, ?_, fun k₀ => ?_⟩
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
    rw [C_mul_monomial, mul_one]
    exact (totalDegree_monomial_le _ _).trans ((le_totalDegree hs).trans (TT_deg P))
  · have hginv : toMK k₀⁻¹ = star (toMK k₀) := by
      have h1 : toMK k₀ * star (toMK k₀) = 1 := Unitary.mul_star_self_of_mem k₀.2.1
      calc toMK k₀⁻¹ = toMK k₀⁻¹ * (toMK k₀ * star (toMK k₀)) := by rw [h1, Matrix.mul_one]
        _ = star (toMK k₀) := by
          rw [← Matrix.mul_assoc]
          change toMK (k₀⁻¹ * k₀) * _ = _
          rw [inv_mul_cancel]
          exact Matrix.one_mul _
    have e1 : π k₀ (B u) = ∫ k, ev (toMK (k₀⁻¹ * k)) P • π k u ∂(muK ε) := by
      change π k₀ (∫ k, ev (toMK k) P • π k u ∂(muK ε)) = _
      rw [← (π k₀).integral_comp_comm (hint P u)]
      have e2 : ∫ k, π k₀ (ev (toMK k) P • π k u) ∂(muK ε) =
          ∫ k, (fun k' : KG ε => ev (toMK (k₀⁻¹ * k')) P • π (k' : UJ ε) u) (k₀ * k) ∂(muK ε) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [map_smul, inv_mul_cancel_left, Subgroup.coe_mul, map_mul, ContinuousLinearMap.mul_apply]
      rw [e2, integral_mul_left_eq_self (fun k' : KG ε => ev (toMK (k₀⁻¹ * k')) P • π (k' : UJ ε) u) k₀]
    have hexp : ∀ k : KG ε, ev (toMK (k₀⁻¹ * k)) P =
        ∑ s ∈ p.support, ev (toMK k) (AddMonoidAlgebra.coeff p s) * ev (toMK k₀) (monomial s 1) := by
      intro k
      change ev (toMK k₀⁻¹ * toMK k) P = _
      rw [hginv, show star (toMK k₀) = (toMK k₀).conjTranspose from rfl, ev_conjT_mul, eval_map_eq]
      rfl
    have hint2 : ∀ s, Integrable (fun k : KG ε => ev (toMK k) (AddMonoidAlgebra.coeff p s) * f k) (muK ε) :=
      fun s => hintC _ ((hevc _).mul hfc)
    have hint3 : Integrable (fun k : KG ε => ev (toMK (k₀⁻¹ * k)) P • π k u) (muK ε) :=
      (((hevc P).comp (continuous_const.mul continuous_id)).smul (horb u)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    calc ⟪l, π k₀ (B u)⟫_ℂ = ∫ k, ⟪l, ev (toMK (k₀⁻¹ * k)) P • π k u⟫_ℂ ∂(muK ε) := by
          rw [e1, integral_inner hint3]
      _ = ∫ k, ∑ s ∈ p.support, ev (toMK k₀) (monomial s 1) * (ev (toMK k) (AddMonoidAlgebra.coeff p s) * f k) ∂(muK ε) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only [inner_smul_right, hexp k, Finset.sum_mul]
          refine Finset.sum_congr rfl fun s _ => ?_
          ring
      _ = ∑ s ∈ p.support, ev (toMK k₀) (monomial s 1) * c s := by
          rw [integral_finsetSum _ fun s _ => (hint2 s).const_mul _]
          exact Finset.sum_congr rfl fun s _ => integral_const_mul _ _
      _ = ev (toMK k₀) (∑ s ∈ p.support, C (c s) * monomial s 1) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_mul, ev, eval_C]
          exact Finset.sum_congr rfl fun s _ => mul_comm _ _

end GlobalTheory.PsCo.Pc3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjugateMemCentralizerMulInte
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GoodConj

theorem eventually_mem_integers {E : Type} [Field E] [NumberField E] (a : E) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite,
      algebraMap E (w.adicCompletion E) a ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) a).2

theorem mem_KGL_of_entries {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E) (g : GLw n w)
    (h1 : ∀ a b, g.val a b ∈ w.adicCompletionIntegers E)
    (h2 : ∀ a b, (g⁻¹).val a b ∈ w.adicCompletionIntegers E) : g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  let O : Subring (w.adicCompletion E) := Ov E w
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => funext fun i => funext fun j => Subtype.ext (congrFun (congrFun h i) j)
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ γ : UE E n,
    γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, ∀ g : UL n w, g⁻¹ * locPt w γ * g ∈ KL n w →
      ∃ t ∈ twCent (MonoidHom.id (UL n w)) (locPt w γ), t⁻¹ * g ∈ KL n w := by
  intro E _ _ _ _ n _ γ hsep
  have hint : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) ((γ.1 : GL (Fin n) E).val i j) ∈ w.adicCompletionIntegers E ∧
      algebraMap E (w.adicCompletion E) (((γ.1 : GL (Fin n) E)⁻¹).val i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j =>
      (eventually_mem_integers _).and (eventually_mem_integers _)
  filter_upwards [hint, _root_.GlobalTheory.IntCop.eventually_integral_coprime E _ hsep] with w hw hP
  obtain ⟨P₀, hP₀, hcop⟩ := hP
  intro g hg
  set y : GLw n w := Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ.1 : GL (Fin n) E) with hy
  by_cases hmem : y ∈ UL n w
  · have hloc : ((locPt w γ : UL n w) : GLw n w) = y := by
      simp only [locPt, toSub]
      rw [dite_eq_left hmem]
    have hyK : y ∈ GlobalTheory.LFun.KGL w (n := n) := by
      apply mem_KGL_of_entries
      · intro a b; exact (hw a b).1
      · intro a b
        rw [hy, ← map_inv]
        exact (hw a b).2
    have hK : locPt w γ ∈ KL n w := by
      rw [KL, Subgroup.mem_subgroupOf, hloc]; exact hyK
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.BCT.cj_involutive_valuation E w
    have hcp : (locPt w γ).1.val.charpoly =
        P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
      rw [hloc, hP₀, hy]
      exact Matrix.charpoly_map _ _
    obtain ⟨t, ht, k, hk, he⟩ := _root_.GlobalTheory.BCT.OrbitT.orbit_main E n w h1 h2 P₀ hcop (locPt w γ) hcp 1 g
      (by simpa using hK) hg
    refine ⟨t, ht, ?_⟩
    rw [he, mul_one, inv_mul_cancel_left]
    exact hk
  · have hloc : locPt w γ = 1 := by
      simp only [locPt, toSub]
      rw [dite_eq_right hmem]
    refine ⟨g, ?_, by rw [inv_mul_cancel]; exact one_mem _⟩
    rw [hloc]
    show g * 1 = 1 * (MonoidHom.id _) g
    simp

end GlobalTheory.BCT.GoodConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjugatorsDifferByCentralizer
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LatStep

theorem isIntB_add' (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) {x y : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) (hy : IsIntB v b y) :
    IsIntB v b (x + y) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hx i) (hy i)

theorem isIntB_neg' (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) {x : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) :
    IsIntB v b (-x) := fun i => by
  rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hx i)

theorem lattice_step : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    (minpoly G.F (γ : G.C)).Separable → ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C),
    Function.Injective ι → (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (κ : Type) (b : Module.Basis κ ℚ G.C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ X X' : (v.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X⁻¹) →
      IsIntB v b (↑X' * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X'⁻¹) →
      ∃ m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ↑m * ↑X'⁻¹) ∧
        IsIntB v b (↑X' * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ↑m⁻¹ * ↑X⁻¹) := by
  intro p _ G γ hdeg _hsep L _ _ ι hι hcent κ b
  let ℓ := Module.finBasis ℚ L
  obtain ⟨r, e, he⟩ := GlobalTheory.T.exists_basis_over_subfield_embedding L G.C ι
  have hE := fun i i' => GlobalTheory.T.exists_sum_two_sided_mul_eq_matrixUnit_unitaryDatum p G γ hdeg L ι hι hcent r e he i i'
  choose N l c hlc using hE
  have hl := fun (i i' : Fin r) (k : Fin (N i i')) => GlobalTheory.T.eventually_one_tmul_adic_integral_coords L _ ℓ (l i i' k)
  have hc := fun (i i' : Fin r) (k : Fin (N i i')) => GlobalTheory.T.eventually_one_tmul_adic_integral_coords G.C κ b (c i i' k)
  choose Sl hSl using hl
  choose Sc hSc using hc
  obtain ⟨S1, hS1⟩ := GlobalTheory.T.adicIntegralTensorBasis_ring_eventually G.C κ b
  obtain ⟨S2, hS2⟩ := GlobalTheory.T.adicIntegralTensorBasis_ring_eventually L _ ℓ
  obtain ⟨S3, hS3⟩ := GlobalTheory.T.almost_all_places_basis_integral L G.C ι r e he _ ℓ κ b
  obtain ⟨S4, hS4⟩ := GlobalTheory.T.eventually_integral_conj_of_integral_conj_generator p G γ hdeg L ι hι hcent κ b _ ℓ
  obtain ⟨S5, hS5⟩ := GlobalTheory.T.fractional_ideal_integral_lattice L _ ℓ
  let SE : Finset (HeightOneSpectrum ℤ) := Finset.univ.biUnion (fun ii : Fin r × Fin r =>
    Finset.univ.biUnion (fun k : Fin (N ii.1 ii.2) => Sl ii.1 ii.2 k ∪ Sc ii.1 ii.2 k))
  refine ⟨S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ SE, ?_⟩
  intro v hv X X' hX hX'
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨⟨⟨⟨hv1, hv2⟩, hv3⟩, hv4⟩, hv5⟩, hvE⟩ := hv
  have hvE' : ∀ i i' k, v ∉ Sl i i' k ∧ v ∉ Sc i i' k := fun i i' k => by
    have : v ∉ Sl i i' k ∪ Sc i i' k := fun h => hvE (Finset.mem_biUnion.2
      ⟨(i, i'), Finset.mem_univ _, Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, h⟩⟩)
    simpa [Finset.mem_union, not_or] using this
  let jv := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι
  have key := GlobalTheory.T.order_lattice_basis_integrality (jv : v.adicCompletion ℚ ⊗[ℚ] L →+* v.adicCompletion ℚ ⊗[ℚ] G.C)
    {y | IsIntB v b y} {x | IsIntB v ℓ x} r (fun i => (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)
    (isIntB_zero v b) (hS1 v hv1).1 (fun x hx y hy => isIntB_add' v b hx hy) (fun x hx => isIntB_neg' v b hx)
    (fun x hx y hy => (hS1 v hv1).2 x y hx hy)
    (isIntB_zero v ℓ) (hS2 v hv2).1 (fun x hx y hy => isIntB_add' v ℓ hx hy) (fun x hx => isIntB_neg' v ℓ hx)
    (fun x hx y hy => (hS2 v hv2).2 x y hx hy)
    (fun a => GlobalTheory.T.existsUnique_left_basis_coords_adicCompletion L G.C ι r e he v a) (hS3 v hv3)
    (fun i i' => ⟨N i i', fun k => (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] l i i' k,
      fun k => (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c i i' k, fun k => hSl i i' k v (hvE' i i' k).1,
      fun k => hSc i i' k v (hvE' i i' k).2,
      fun β => GlobalTheory.T.basis_change_adic_tensor_identity L G.C ι r e (N i i') (l i i') (c i i') i i' (hlc i i') v β⟩)
    (fun a => by
      obtain ⟨D, hD, h⟩ := GlobalTheory.T.exists_int_smul_isAdicIntegralInTensorBasis G.C κ b v a
      exact ⟨D, hD, by simpa [zsmul_eq_mul] using h⟩)
    (fun I h0 hadd hmul hD => hS5 v hv5 I h0 hadd hmul hD)
  obtain ⟨m, hm1, hm2⟩ := key X (fun ρ hρ => hS4 v hv4 X hX ρ hρ)
  obtain ⟨m', hm1', hm2'⟩ := key X' (fun ρ hρ => hS4 v hv4 X' hX' ρ hρ)
  refine ⟨m * m'⁻¹, ?_, ?_⟩
  · have := (hS1 v hv1).2 _ _ hm1 hm2'
    convert this using 1
    simp only [RingHom.coe_coe, Units.val_mul, map_mul, mul_assoc, jv]
  · have := (hS1 v hv1).2 _ _ hm1' hm2
    convert this using 1
    simp only [RingHom.coe_coe, _root_.mul_inv_rev, inv_inv, Units.val_mul, map_mul, mul_assoc, jv]

end GlobalTheory.LatStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyMemKGL
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.Fact

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_KGL_of {w : Pl E} (g : GL (Fin n) (w.adicCompletion E))
    (h1 : ∀ i j, g.1 i j ∈ w.adicCompletionIntegers E) (h2 : ∀ i j, g⁻¹.1 i j ∈ w.adicCompletionIntegers E) :
    g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_mem_KGL (x : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    ∀ᶠ w : Pl E in cofinite, GeneralLinearGroup.map (pLoc E w) x ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have h : ∀ g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E), ∀ᶠ w : Pl E in cofinite,
      ∀ i j, pLoc E w (g.val i j) ∈ w.adicCompletionIntegers E := fun g => by
    simp only [Filter.eventually_all]
    exact fun i j => (g.val i j).2
  filter_upwards [h x, h x⁻¹] with w a b
  exact mem_KGL_of _ a (by rw [← map_inv]; exact b)

end GlobalTheory.EulerTw.Fact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicMulIntegralGL
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

open ValuativeRel

theorem mem_integer_iff_mem_Ov {E : Type} [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) :
    x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Ov E w := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _)
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

theorem integralGL_le_KGL {E : Type} [Field E] [NumberField E] (w : Pl E) (n : ℕ) :
    GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) n ≤ GlobalTheory.LFun.KGL w (n := n) := by
  intro g hg
  obtain ⟨h1, h2⟩ := (GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff _ n).1 hg
  let A : Matrix (Fin n) (Fin n) (Ov E w) :=
    Matrix.of fun i j => ⟨g i j, (mem_integer_iff_mem_Ov w _).1 (h1 i j)⟩
  let B : Matrix (Fin n) (Fin n) (Ov E w) :=
    Matrix.of fun i j => ⟨(g⁻¹ : GL (Fin n) (w.adicCompletion E)) i j, (mem_integer_iff_mem_Ov w _).1 (h2 i j)⟩
  have hinj : Function.Injective (RingHom.mapMatrix (m := Fin n) (Ov E w).subtype) :=
    fun M N h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
  have hA : RingHom.mapMatrix (Ov E w).subtype A = (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := rfl
  have hB : RingHom.mapMatrix (Ov E w).subtype B =
      ((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := rfl
  have hAB : A * B = 1 := hinj (by rw [map_mul, map_one, hA, hB, Units.mul_inv])
  have hBA : B * A = 1 := hinj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

theorem exists_parabolic_mul_maximalCompact : ∀ (E : Type) [Field E] [NumberField E] (a n : ℕ) (w : Pl E) (g : GLw n w),
    ∃ p ∈ GlobalTheory.LeviDesc.parP a n w, ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = p * k := by
  intro E _ _ a n w g
  have hβ : Monotone fun i : Fin n => decide (a ≤ (i : ℕ)) := by
    intro i j hij
    by_cases h : a ≤ (i : ℕ)
    · have : a ≤ (j : ℕ) := h.trans (Fin.le_iff_val_le_val.1 hij)
      simp [h, this]
    · simp [h]
  obtain ⟨p, hp, k, hk, rfl⟩ :=
    GroundTheory.Automorphic.Iwasawa.exists_blockUpper_mul_integralGL (w.adicCompletion E) n hβ g
  exact ⟨p, hp, k, integralGL_le_KGL w n hk, rfl⟩

end GlobalTheory.LeviDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactInvertibleKrylovMatrices
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.Krylov

theorem exists_isCompact_krylov_units : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) (Ω : Set (GLw r w)), IsCompact Ω → (∀ y ∈ Ω, ∃ e, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y.val e).det) → ∃ C : Set (GLw r w), IsCompact C ∧ ∀ y ∈ Ω, ∃ e, ∃ c ∈ C, c.val = GlobalTheory.LeviDesc.Krylov.krylov y.val e := by
  intro E _ _ w r Ω hΩ hcov
  classical
  let kr : (Fin r → w.adicCompletion E) → GLw r w → Matrix (Fin r) (Fin r) (w.adicCompletion E) :=
    fun e y => GlobalTheory.LeviDesc.Krylov.krylov y.val e
  have hkc : ∀ e, Continuous (kr e) := by
    intro e
    have hv : Continuous fun y : GLw r w => (y.val : Matrix (Fin r) (Fin r) (w.adicCompletion E)) :=
      Units.continuous_val
    refine continuous_matrix fun i j => ?_
    simp only [kr, GlobalTheory.LeviDesc.Krylov.krylov_apply]
    exact (continuous_apply i).comp ((hv.pow (j : ℕ)).matrix_mulVec continuous_const)
  let U : (Fin r → w.adicCompletion E) → Set (GLw r w) := fun e => {y | (kr e y).det ≠ 0}
  have hU : ∀ e, IsOpen (U e) := fun e => isOpen_ne_fun ((hkc e).matrix_det) continuous_const
  have hsub : Ω ⊆ ⋃ e, U e := by
    intro y hy
    obtain ⟨e, he⟩ := hcov y hy
    exact Set.mem_iUnion.2 ⟨e, he.ne_zero⟩
  obtain ⟨t, ht⟩ := hΩ.elim_finite_subcover U hU hsub
  obtain ⟨K, hKc, hKU, hΩK⟩ := hΩ.finite_compact_cover t U (fun e _ => hU e) ht
  have hunit : ∀ e, ∀ y : K e, IsUnit (kr e y.1) := fun e y =>
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hKU e y.2))
  let f : ∀ e, K e → GLw r w := fun e y => (hunit e y).unit
  have hf : ∀ e, Continuous (f e) := by
    intro e
    rw [Units.continuous_iff]
    constructor
    · exact (hkc e).comp continuous_subtype_val
    · have : (fun y : K e => ((f e y)⁻¹ : GLw r w).val) = fun y => (kr e y.1)⁻¹ := by
        funext y
        rw [Matrix.coe_units_inv]
        rfl
      rw [this]
      simp only [Matrix.inv_def, Ring.inverse_eq_inv']
      exact (((hkc e).comp continuous_subtype_val).matrix_det.inv₀ fun y => hKU e y.2).smul
        ((hkc e).comp continuous_subtype_val).matrix_adjugate
  refine ⟨⋃ e ∈ t, Set.range (f e), t.isCompact_biUnion fun e _ => ?_, ?_⟩
  · haveI := isCompact_iff_compactSpace.1 (hKc e)
    exact isCompact_range (hf e)
  · intro y hy
    rw [hΩK] at hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨e, he, hyK⟩ := hy
    exact ⟨e, f e ⟨y, hyK⟩, Set.mem_biUnion he ⟨⟨y, hyK⟩, rfl⟩, rfl⟩

end GlobalTheory.LeviDesc.Krylov
end
end

