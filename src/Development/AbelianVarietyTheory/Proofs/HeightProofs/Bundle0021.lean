module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare.RealAction

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {A B : Type} [CommRing A] [CommRing B] {m n : Type} [Fintype m] [Fintype n]

theorem map_triple (φ : A →+* B) (g : Matrix m m A) (x : Matrix m n A) (h : Matrix n n A) :
    (g * x * hᵀ).map φ = g.map φ * x.map φ * (h.map φ)ᵀ := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

theorem map_triple_zero (φ : A →+* B) (g : Matrix m m A) (x : Matrix m n A) (h : Matrix n n A)
    (hx : x.map φ = 0) : (g * x * hᵀ).map φ = 0 := by
  rw [map_triple, hx, Matrix.mul_zero, Matrix.zero_mul]

omit [Fintype m] in
theorem map_conj (s : A →+* A) (φ : A →+* ℂ) (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (g : Matrix m m A) :
    (g.map s).map φ = (g.map φ).map (starRingEnd ℂ) := by
  ext a b
  exact h _

theorem unitary_map (s : A →+* A) (φ : A →+* ℂ) (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (g J : Matrix m m A)
    (hg : (g.map s)ᵀ * J * g = J) : (g.map φ)ᴴ * J.map φ * g.map φ = J.map φ := by
  have e : (g.map φ)ᴴ = ((g.map s)ᵀ).map φ := by
    ext a b
    exact (h _).symm
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hg]

end Generic

variable {D : D7}

theorem infMat_eq (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (k : GA D V) :
    infMat D.sp.cm.sig V.gram θ k = (mt V k).map (θ.comp (infPart D)) := rfl

theorem wAt_eq (θ : InfFam D) (V W : HSp D) (τ : D.what₂.Tau) (x : WA V W) :
    wAt θ V W τ x = x.map ((θ τ).comp (infPart D)) := rfl

theorem gramAt_eq {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    gramAt D V τ = (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) := by
  ext a b
  exact (comp_incA hθ τ _).symm

theorem infMat_mem_UH {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (k : GA D V) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (θ τ) k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  rw [infMat_eq, gramAt_eq hθ]
  exact unitary_map (cA D) ((θ τ).comp (infPart D)) (comp_cA hθ τ) _ _ (mt_rel V k)

theorem wAt_actHom {θ : InfFam D} (hθ : IsInfFam θ) (V W : HSp D) (k : GA D V) (k' : GA D W) (x : WA V W)
    (τ : D.what₂.Tau) : wAt θ V W τ (actHom V W k k' x) =
      actC V W (infMat D.sp.cm.sig V.gram (θ τ) k) (infMat D.sp.cm.sig W.gram (θ τ) k') (wAt θ V W τ x) := by
  rw [infMat_eq, infMat_eq, wAt_eq, wAt_eq]
  unfold actHom actC cM
  split_ifs
  · rw [← map_conj (cA D) ((θ τ).comp (infPart D)) (comp_cA hθ τ)]
    exact map_triple _ _ _ _
  · rw [← map_conj (cA D) ((θ τ).comp (infPart D)) (comp_cA hθ τ)]
    exact map_triple _ _ _ _

theorem isRealW_actHom (V W : HSp D) (k : GA D V) (k' : GA D W) (x : WA V W) (hx : IsRealW V W x) :
    IsRealW V W (actHom V W k k' x) := by
  unfold IsRealW actHom
  split_ifs
  · exact map_triple_zero (finPart D) _ _ _ hx
  · exact map_triple_zero (finPart D) _ _ _ hx

theorem real_action : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ (V : HSp D) (k : GA D V) (τ : D.what₂.Tau), infMat D.sp.cm.sig V.gram (θ τ) k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) ∧ ∀ (V W : HSp D) (k : GA D V) (k' : GA D W) (x : WA V W), (∀ τ, wAt θ V W τ (actHom V W k k' x) = actC V W (infMat D.sp.cm.sig V.gram (θ τ) k) (infMat D.sp.cm.sig W.gram (θ τ) k') (wAt θ V W τ x)) ∧ (IsRealW V W x → IsRealW V W (actHom V W k k' x)) :=
  fun _ _ hθ => ⟨fun V k τ => infMat_mem_UH hθ V k τ, fun V W k k' x =>
    ⟨fun τ => wAt_actHom hθ V W k k' x τ, isRealW_actHom V W k k' x⟩⟩

end GlobalTheory.FockCompare.RealAction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.BddAboveOfSpanningPeriodsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_le_of_continuous_of_spanning_periods : ∀ (R : Type) [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (g : R → ℝ), Continuous g → ∀ S : Set R, Submodule.span ℝ S = ⊤ → (∀ s ∈ S, ∃ N : ℕ, 0 < N ∧ ∀ x, g (x + (N : ℝ) • s) = g x) → ∃ C : ℝ, ∀ x, g x ≤ C := by
  first | exact @GlobalTheory.bddAbove_of_spanning_periods | exact GlobalTheory.bddAbove_of_spanning_periods | (intros; apply GlobalTheory.bddAbove_of_spanning_periods <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CanonicalCommutationRelationsWeylNumber
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeylNumber

theorem exists_parseval_family {R : Type} [AddCommGroup R] [Module ℝ R] [FiniteDimensional ℝ R]
    (g : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (hs : ∀ u v, g u v = g v u) (hp : ∀ u, u ≠ 0 → 0 < g u u) :
    ∃ (n : ℕ) (e : Fin n → R), ∀ x, ∑ k, g x (e k) • e k = x := by
  first
  | exact @_root_.GlobalTheory.PolynomialCoeffEq.main
  | exact _root_.GlobalTheory.PolynomialCoeffEq.main
  | (apply _root_.GlobalTheory.PolynomialCoeffEq.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialCoeffEq.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialCoeffEq.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialCoeffEq.main ..)

theorem weyl_number : ∀ (M R : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℝ R] [FiniteDimensional ℝ R] (Dop : R → Module.End ℂ M) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (κ : ℂ) (j : R →ₗ[ℝ] R), (∀ u v, Dop (u + v) = Dop u + Dop v) → (∀ (c : ℝ) u, Dop (c • u) = (c : ℂ) • Dop u) → κ ≠ 0 → (∀ u v, Dop u * Dop v - Dop v * Dop u = (κ * (om u v : ℝ)) • (1 : Module.End ℂ M)) → (∀ u v, om v u = -om u v) → (∀ u, j (j u) = -u) → (∀ u v, om (j u) (j v) = om u v) → (∀ u, u ≠ 0 → 0 < om u (j u)) → (∀ u v, ∃ β : ℂ, (Dop u + Complex.I • Dop (j u)) * (Dop v - Complex.I • Dop (j v)) - (Dop v - Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) = β • (1 : Module.End ℂ M)) ∧ ∃ (n : ℕ) (e : Fin n → R) (lam : ℂ), lam ≠ 0 ∧ ∀ u, (Dop u + Complex.I • Dop (j u)) * (∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) = ((∑ k, (Dop (e k) - Complex.I • Dop (j (e k))) * (Dop (e k) + Complex.I • Dop (j (e k)))) + lam • (1 : Module.End ℂ M)) * (Dop u + Complex.I • Dop (j u)) := by
  intro M R _ _ _ _ _ Dop om κ j hadd hsmul hκ hcomm hanti hjj hom hpos
  have h1 : ∀ u v, om (j u) v = -om u (j v) := fun u v => by
    rw [← hom (j u) v, hjj]; simp
  have hc : ∀ u v, Dop u * Dop v = Dop v * Dop u + (κ * (om u v : ℝ)) • (1 : Module.End ℂ M) :=
    fun u v => by rw [← hcomm]; abel
  have hneg : ∀ u, Dop (-u) = -Dop u := fun u => by
    have := hsmul (-1) u
    simpa using this
  have hac : ∀ u v, (Dop u + Complex.I • Dop (j u)) * (Dop v - Complex.I • Dop (j v)) =
      (Dop v - Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) +
        (2 * κ * ((om u v : ℝ) - Complex.I * (om u (j v) : ℝ))) • (1 : Module.End ℂ M) := by
    intro u v
    simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
      Complex.I_mul_I]
    rw [hc u v, hc u (j v), hc (j u) v, hc (j u) (j v), hom, h1]
    push_cast
    match_scalars <;> (try ring_nf) <;> (try simp) <;> (try ring)
  have haa : ∀ u v, (Dop u + Complex.I • Dop (j u)) * (Dop v + Complex.I • Dop (j v)) =
      (Dop v + Complex.I • Dop (j v)) * (Dop u + Complex.I • Dop (j u)) := by
    intro u v
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      Complex.I_mul_I]
    rw [hc u v, hc u (j v), hc (j u) v, hc (j u) (j v), hom, h1]
    push_cast
    match_scalars <;> (try ring_nf) <;> (try simp) <;> (try ring)
  refine ⟨fun u v => ⟨_, by rw [hac u v, add_sub_cancel_left]⟩, ?_⟩
  obtain ⟨n, e, he⟩ := exists_parseval_family (om.compl₂ j)
    (fun u v => by
      simp only [LinearMap.compl₂_apply]
      rw [hanti (j u) v, h1, neg_neg])
    (fun u hu => by simpa using hpos u hu)
  simp only [LinearMap.compl₂_apply] at he
  let A : R →+ Module.End ℂ M := AddMonoidHom.mk' (fun u => Dop u + Complex.I • Dop (j u))
    (fun u v => by simp only [map_add (f := _), hadd, smul_add]; abel)
  have hA : ∀ u, A u = Dop u + Complex.I • Dop (j u) := fun _ => rfl
  have hAs : ∀ (c : ℝ) u, A (c • u) = (c : ℂ) • A u := fun c u => by
    simp only [hA, map_smul, hsmul]; module
  have hAj : ∀ u, A (j u) = (-Complex.I) • A u := fun u => by
    simp only [hA, hjj, hneg, smul_add, smul_smul, neg_mul, Complex.I_mul_I]
    module
  have hsum : ∀ x, ∑ k, ((om x (j (e k)) : ℝ) : ℂ) • A (e k) = A x := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← he x, map_sum]
    simp only [hAs]
  refine ⟨n, e, -4 * Complex.I * κ, by simp [hκ], fun u => ?_⟩
  have key : ∀ k, A u * ((Dop (e k) - Complex.I • Dop (j (e k))) * A (e k)) =
      ((Dop (e k) - Complex.I • Dop (j (e k))) * A (e k)) * A u +
        ((2 * κ) • (((om (j u) (j (e k)) : ℝ) : ℂ) • A (e k))
          - (2 * κ * Complex.I) • (((om u (j (e k)) : ℝ) : ℂ) • A (e k))) := fun k => by
    rw [← mul_assoc, hA u, hac, add_mul, mul_assoc, mul_assoc, hA (e k), haa u, hom,
      smul_mul_assoc, one_mul]
    module
  simp only [← hA]
  rw [Finset.mul_sum, add_mul, Finset.sum_mul, Finset.sum_congr rfl fun k _ => key k,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
    hsum, hsum, hAj, smul_mul_assoc, one_mul]
  module

end GlobalTheory.WeylNumber
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CMTypePlaces

open NumberField

theorem mk_tauE_bijective (D : D7) :
    Function.Bijective fun τ : D.what₂.Tau => InfinitePlace.mk (tauE D τ) := by
  obtain ⟨hb, hm⟩ := Formalism.BasicNotions.factEmb D.R D.host
  have hsq := D.host.sqd_sq
  have hd0 : (0 : ℝ) ≤ D.host.d := Nat.cast_nonneg _
  have hmem : ∀ τ : D.what₂.Tau, tauE D τ (D.host.sqd) =
      Complex.I * (Real.sqrt D.host.d : ℂ) := fun τ => (hm _).2 (D.eTau τ).2
  have hdpos : 0 < D.host.d := lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.2
  have hs : (Real.sqrt D.host.d : ℂ) ≠ 0 := by
    have : Real.sqrt D.host.d ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hdpos)).ne'
    exact_mod_cast this
  have hconj : (starRingEnd ℂ) (Complex.I * (Real.sqrt D.host.d : ℂ)) =
      -(Complex.I * (Real.sqrt D.host.d : ℂ)) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  have hsurj : ∀ φ : D.host.E →+* ℂ, φ (D.host.sqd) =
      Complex.I * (Real.sqrt D.host.d : ℂ) → ∃ τ, tauE D τ = φ := by
    intro φ hφ
    obtain ⟨g, rfl⟩ := hb.2 φ
    refine ⟨D.eTau.symm ⟨g, (hm g).1 hφ⟩, ?_⟩
    simp only [tauE, Equiv.apply_symm_apply]
  constructor
  · intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact D.eTau.injective (Subtype.ext (hb.1 h))
    · exfalso
      have h1 := congrArg (fun φ : D.host.E →+* ℂ => φ (D.host.sqd)) h
      simp only [ComplexEmbedding.conjugate_coe_eq] at h1
      rw [hmem, hmem, hconj] at h1
      have h2 : Complex.I * (Real.sqrt D.host.d : ℂ) = 0 := by linear_combination (-1 / 2 : ℂ) * h1
      exact mul_ne_zero Complex.I_ne_zero hs h2
  · intro w
    have h1 : (w.embedding (D.host.sqd)) ^ 2 =
        (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
      rw [← map_pow, hsq, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
        Real.sq_sqrt hd0]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · obtain ⟨τ, hτ⟩ := hsurj _ h
      exact ⟨τ, by simp only [hτ, InfinitePlace.mk_embedding]⟩
    · obtain ⟨τ, hτ⟩ := hsurj (ComplexEmbedding.conjugate w.embedding) (by
        rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, hconj, neg_neg])
      exact ⟨τ, by simp only [hτ, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]⟩

theorem places_bijective : ∀ D : D7, Function.Bijective fun τ : D.what₂.Tau => NumberField.InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)) := by
  intro D
  haveI := D.host.isCMField_hostE
  exact (IsCMField.equivInfinitePlace D.host.E).bijective.comp (mk_tauE_bijective D)

end GlobalTheory.CMTypePlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ComplexStructureOfInvolutionsProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCxAlg

variable {D : D7}

theorem actC_actC (V W : HSp D) (g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h h' : Matrix (Fin W.rank) (Fin W.rank) ℂ) (x : WC V W) :
    actC V W g h (actC V W g' h' x) = actC V W (g * g') (h * h') x := by
  unfold actC
  split_ifs <;> simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem actC_smul (V W : HSp D) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h : Matrix (Fin W.rank) (Fin W.rank) ℂ) (c : ℂ) (x : WC V W) :
    actC V W g h (c • x) = c • actC V W g h x := by
  unfold actC
  split_ifs <;> simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem actC_one (V W : HSp D) (x : WC V W) : actC V W 1 1 x = x := by
  unfold actC
  split_ifs <;> simp

theorem hC_actC (V W : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (h : Matrix (Fin W.rank) (Fin W.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ)
    (hh : hᴴ * gramAt D W τ * h = gramAt D W τ) (x y : WC V W) :
    hC V W τ (actC V W g h x) (actC V W g h y) = hC V W τ x y := by
  unfold hC actC
  split_ifs with hr
  · rw [GlobalTheory.DualPairCheck.sum_small, GlobalTheory.DualPairCheck.sum_small]
    exact GlobalTheory.DualPairCheck.inv_small (starRingEnd ℂ) Complex.conj_conj _ _ _ _ hg hh x y
  · rw [GlobalTheory.DualPairCheck.sum_large, GlobalTheory.DualPairCheck.sum_large]
    exact GlobalTheory.DualPairCheck.inv_large (starRingEnd ℂ) Complex.conj_conj _ _ _ _ hg hh x y

theorem I_smul_unitary {n : ℕ} {G t : Matrix (Fin n) (Fin n) ℂ} (h : tᴴ * G * t = G) :
    (Complex.I • t)ᴴ * G * (Complex.I • t) = G := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h]
  simp

theorem cx_alg : ∀ (D : D7) (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) (s' : Module.End D.host.E W.V), IsCart (gramAt D V τ) (thAt V τ s) → IsCart (gramAt D W τ) (thAt W τ s') → (∀ x, jAt V W τ s s' (jAt V W τ s s' x) = -x) ∧ (∀ x y, symplC V W τ (jAt V W τ s s' x) (jAt V W τ s s' y) = symplC V W τ x y) ∧ (∀ g h, Commute g (thAt V τ s) → Commute h (thAt W τ s') → ∀ x, jAt V W τ s s' (actC V W g h x) = actC V W g h (jAt V W τ s s' x)) ∧ ∃ g ∈ KAt V τ s, ∃ h ∈ KAt W τ s', ∀ x, jAt V W τ s s' x = actC V W g h x := by
  intro D V W τ s s' hV hW
  refine ⟨fun x => ?_, fun x y => ?_, fun g h hg hh x => ?_, ?_⟩
  · unfold jAt
    rw [actC_smul, actC_actC, hV.1, hW.1, actC_one, smul_smul, Complex.I_mul_I, neg_one_smul]
  · unfold symplC jAt
    rw [hC_smul_left, hC_smul_right, hC_actC V W τ _ _ hV.2.1 hW.2.1, ← mul_assoc (starRingEnd ℂ Complex.I),
      Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  · unfold jAt
    rw [actC_smul, actC_actC, actC_actC, hg.eq, hh.eq]
  · by_cases hr : V.rank ≤ W.rank
    · refine ⟨thAt V τ s, ⟨hV.2.1, rfl⟩, Complex.I • thAt W τ s',
        ⟨I_smul_unitary hW.2.1, by rw [Matrix.smul_mul, Matrix.mul_smul]⟩, fun x => ?_⟩
      unfold jAt actC
      rw [if_pos hr, if_pos hr, Matrix.transpose_smul, Matrix.mul_smul]
    · refine ⟨Complex.I • thAt V τ s,
        ⟨I_smul_unitary hV.2.1, by rw [Matrix.smul_mul, Matrix.mul_smul]⟩, thAt W τ s', ⟨hW.2.1, rfl⟩, fun x => ?_⟩
      unfold jAt actC
      rw [if_neg hr, if_neg hr, Matrix.smul_mul, Matrix.smul_mul]

end GlobalTheory.FockCxAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmooth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder Topology

namespace GlobalTheory.FockCompare.ThetaCont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}

theorem infPart_eq_zero (h : Chart θ σ) (a : AE D) (ha : ∀ τ, θ τ (infPart D a) = 0) : infPart D a = 0 := by
  let e : AF D.host.F := ((1 : Ainf D.host.F), (0 : Af D.host.F))
  let E : AE D := e ⊗ₜ[D.host.F] (1 : D.host.E)
  have h1 : infPart D E = 1 := rfl
  have h2 : finPart D E = 0 := by
    show (0 : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  have h3 : infPart D (E * a) = infPart D a := by rw [RingHom.map_mul, h1, one_mul]
  have h4 : E * a = 0 := h.ext _ (by rw [RingHom.map_mul, h2, zero_mul]) fun τ => by rw [h3]; exact ha τ
  rw [← h3, h4, RingHom.map_zero]

theorem continuous_conj : Continuous (cA D) := by
  let f : AE D →ₐ[AF D.host.F] AE D :=
    Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig
  exact IsModuleTopology.continuous_of_linearMap f.toLinearMap

theorem continuous_hHom (V W : HSp D) {X : Type} [TopologicalSpace X] {x y : X → WA V W} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => hHom V W (x t) (y t) := by
  have hx' : ∀ i j, Continuous fun t => cA D (x t i j) := fun i j =>
    continuous_conj.comp ((continuous_apply j).comp ((continuous_apply i).comp hx))
  have hy' : ∀ i j, Continuous fun t => y t i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hy)
  unfold hHom
  split_ifs <;>
    exact continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
      continuous_finsetSum _ fun _ _ => (((hx' _ _).mul continuous_const).mul continuous_const).mul (hy' _ _)

theorem continuous_symplH (V W : HSp D) {X : Type} [TopologicalSpace X] {x y : X → WA V W} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => symplH V W (x t) (y t) := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.mul (ht.comp (continuous_const.mul (continuous_hHom V W hy hx)))

theorem continuous_of_level_of_smooth (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ)
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) (V W : HSp D) (f : WA V W → ℂ)
    (hU : ∃ U : AddSubgroup (WA V W), IsOpen (U : Set (WA V W)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → Heisenberg₂ ψ V W u f = f)
    (hs : Sm (iotaW σ V W) f) : Continuous f := by
  obtain ⟨U, hUo, hU⟩ := hU
  have : IsTopologicalAddGroup (AE D) := IsTopologicalRing.isTopologicalAddGroup
  haveI : IsTopologicalAddGroup (WA V W) := Pi.topologicalAddGroup
  haveI : ContinuousSub (WA V W) := IsTopologicalAddGroup.to_continuousSub
  refine continuous_iff_continuousAt.2 fun w => ?_
  let x : WA V W → RW V W := fun w' => piW θ V W (w' - w)
  let a : WA V W → WA V W := fun w' => w + iotaW σ V W (x w')
  let u : WA V W → WA V W := fun w' => w' - a w'
  have hx : Continuous x := (continuous_pi' h.inf V W).comp (continuous_id.sub continuous_const)
  have ha : Continuous a := continuous_const.add ((h.continuous_iota V W).comp hx)
  have hu : Continuous u := continuous_id.sub ha
  have huw : u w = 0 := by
    show w - (w + iotaW σ V W (piW θ V W (w - w))) = 0
    rw [sub_self, AddMonoidHom.map_zero, AddMonoidHom.map_zero, add_zero, sub_self]
  have hinf : ∀ w', (u w').map (infPart D) = 0 := by
    intro w'
    have hp : piW θ V W (u w') = 0 := by
      show piW θ V W (w' - (w + iotaW σ V W (piW θ V W (w' - w)))) = 0
      rw [← sub_sub, AddMonoidHom.map_sub, h.pi_iota, sub_self]
    ext i j
    exact infPart_eq_zero h _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
  have hg : Continuous fun w' => ψ (-symplH V W (a w') (u w')) * f (a w') :=
    (hψ.comp (continuous_symplH V W ha hu).neg).mul ((hs w).continuous.comp hx)
  have hev : ∀ᶠ w' in 𝓝 w, u w' ∈ U :=
    hu.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [huw]; exact U.zero_mem))
  refine hg.continuousAt.congr (hev.mono fun w' hw' => ?_)
  have e := congrFun (hU _ hw' (hinf w')) (a w')
  have e2 : a w' + u w' = w' := add_sub_cancel _ _
  show ψ (-symplH V W (a w') (u w')) * f (a w') = f w'
  rw [← e]
  show _ * (ψ (symplH V W (a w') (u w')) * f (a w' + u w')) = _
  rw [e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.FockCompare.ThetaCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsHeisenbergDerivativeLinearOperators
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare


open Matrix in
open scoped TensorProduct ContDiff ComplexOrder in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
theorem _root_.GlobalTheory.FockCompare.exists_heisenberg_operators : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) → (∀ (f : G → ℂ), _root_.GlobalTheory.FockCompare.Sm ι f → ∀ (u : R) (w : G), _root_.GlobalTheory.FockCompare.hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) → ∀ (M : Submodule ℂ (G → ℂ)), (∀ f ∈ M, _root_.GlobalTheory.FockCompare.Sm ι f) → (∀ u, ∀ f ∈ M, _root_.GlobalTheory.FockCompare.hD ι π om u f ∈ M) → ∃ Dop : R → Module.End ℂ M, (∀ u (f : M), ((Dop u f : M) : G → ℂ) = _root_.GlobalTheory.FockCompare.hD ι π om u f) ∧ (∀ u v, Dop (u + v) = Dop u + Dop v) ∧ ∀ (c : ℝ) u, Dop (c • u) = (c : ℂ) • Dop u := by
  intro G R _ _ _ _ ι π om _ hform M hSm hM
  have hdiff : ∀ f ∈ M, ∀ w : G, DifferentiableAt ℝ (fun x : R => f (w + ι x)) 0 :=
    fun f hf w => ((hSm f hf w).differentiable (by simp)).differentiableAt
  refine ⟨fun u =>
    { toFun := fun f => ⟨_root_.GlobalTheory.FockCompare.hD ι π om u f, hM u f f.2⟩
      map_add' := ?_
      map_smul' := ?_ }, fun u f => rfl, ?_, ?_⟩
  · intro f g
    ext w
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [hform _ (hSm _ (M.add_mem f.2 g.2)), hform _ (hSm _ f.2), hform _ (hSm _ g.2)]
    have hfun : (fun x : R => ((f : G → ℂ) + g) (w + ι x)) =
        (fun x : R => (f : G → ℂ) (w + ι x)) + fun x : R => (g : G → ℂ) (w + ι x) := rfl
    rw [hfun, fderiv_add (hdiff _ f.2 w) (hdiff _ g.2 w)]
    simp only [Pi.add_apply, ContinuousLinearMap.add_apply]
    ring
  · intro a f
    ext w
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [hform _ (hSm _ (M.smul_mem a f.2)), hform _ (hSm _ f.2)]
    have hfun : (fun x : R => (a • (f : G → ℂ)) (w + ι x)) =
        a • fun x : R => (f : G → ℂ) (w + ι x) := rfl
    rw [hfun, fderiv_const_smul (hdiff _ f.2 w)]
    simp only [Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.smul_apply]
    ring
  · intro u v
    ext f w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Submodule.coe_add,
      Pi.add_apply]
    rw [hform _ (hSm _ f.2), hform _ (hSm _ f.2), hform _ (hSm _ f.2)]
    simp only [map_add (f := _)]
    push_cast
    ring
  · intro c u
    ext f w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, SetLike.val_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [hform _ (hSm _ f.2), hform _ (hSm _ f.2)]
    simp only [map_smul, smul_eq_mul, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.FockCompare
end

