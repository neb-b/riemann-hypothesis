module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.EnvelopingMapSurjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.EnvWords

theorem mem_span_words (L : Type) [LieRing L] [LieAlgebra ℝ L] (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) :
    u ∈ Submodule.span ℂ (Set.range fun l : List L =>
      (l.map fun X => UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)).prod) := by
  have hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (ℂ ⊗[ℝ] L)) :=
    fun u => Quotient.exists_rep u
  obtain ⟨t, rfl⟩ := hs u
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[], rfl⟩)
  | ι x =>
    change UniversalEnvelopingAlgebra.ι ℂ x ∈ _
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul z X =>
      have h : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[X], by simp⟩)
    | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | mul a b ha hb =>
    rw [map_mul]
    have h := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨_, ⟨l, rfl⟩, _, ⟨m, rfl⟩, rfl⟩
    exact ⟨l ++ m, by simp only [List.map_append, List.prod_append]⟩
  | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb

theorem envOf_surjective : ∀ (D : D7) (V : HSp D) (τ : D.what₂.Tau),
    Function.Surjective (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.envOf V τ) := by
  intro D V τ u
  exact (Finsupp.mem_span_range_iff_exists_finsupp).1 (mem_span_words (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ) u)

end GlobalTheory.EnvWords
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEnvelopingAlgHomUnitaryLieAlgebra
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

namespace GlobalTheory.EnvelopingExtension

theorem exists_algHom_of_real (L : Type) [LieRing L] [LieAlgebra ℝ L] (A : Type) [Ring A] [Algebra ℂ A] (ρ : L → A)
    (hadd : ∀ X Y, ρ (X + Y) = ρ X + ρ Y) (hsmul : ∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X)
    (hbr : ∀ X Y, ρ ⁅X, Y⁆ = ρ X * ρ Y - ρ Y * ρ X) :
    ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) →ₐ[ℂ] A,
      ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  let f : L →ₗ[ℝ] A :=
    { toFun := ρ
      map_add' := hadd
      map_smul' := fun c X => by
        rw [hsmul]
        exact Complex.coe_smul c (ρ X) }
  let F : ℂ ⊗[ℝ] L →ₗ[ℂ] A := f.liftBaseChange ℂ
  have hF : ∀ (a : ℂ) (x : L), F (a ⊗ₜ x) = a • ρ x := fun a x => by
    simp [F, f, LinearMap.liftBaseChange_tmul]
  have hlie : ∀ u v : ℂ ⊗[ℝ] L, F ⁅u, v⁆ = ⁅F u, F v⁆ := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u₁ u₂ h₁ h₂ => rw [add_lie, map_add (f := _), h₁, h₂, map_add (f := _), add_lie]
    | tmul a x =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v₁ v₂ h₁ h₂ => rw [lie_add, map_add (f := _), h₁, h₂, map_add (f := _), lie_add]
      | tmul b y =>
        rw [LieAlgebra.ExtendScalars.bracket_tmul, hF, hF, hF, hbr, Ring.lie_def,
          smul_mul_smul_comm, smul_mul_smul_comm, mul_comm b a, smul_sub]
  let G : ℂ ⊗[ℝ] L →ₗ⁅ℂ⁆ A := { F with map_lie' := fun {u v} => hlie u v }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ G, fun X => ?_⟩
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  change F ((1 : ℂ) ⊗ₜ X) = ρ X
  rw [hF, one_smul]

theorem exists_algHom_unitary : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → ∃ π : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J) →ₐ[ℂ] A, ∀ X, π (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  intro n J A _ _ ρ hadd hsmul hbr
  exact exists_algHom_of_real _ A ρ hadd hsmul fun X Y => hbr X Y ⁅X, Y⁆ (by
    rw [LieSubalgebra.coe_bracket, Ring.lie_def])

end GlobalTheory.EnvelopingExtension

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFiniteCosetsAdelicUnitaryBoundedDenominato
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.SmoothForms.Cover

open NumberField IsDedekindDomain Topology

theorem exists_finset_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) (U : Subgroup H) (hU : IsOpen (U : Set H)) (K : Set G) (hK : IsCompact K)
    (Ω : Set H) (hΩ : ∀ k ∈ Ω, (k : G) ∈ K) :
    ∃ S : Finset H, (∀ x ∈ S, x ∈ Ω) ∧ ∀ k ∈ Ω, ∃ x ∈ S, x⁻¹ * k ∈ U := by
  classical
  obtain ⟨W, hW, hWU⟩ := isOpen_induced_iff.1 hU
  have h1 : (1 : G) ∈ W := by
    have : (1 : H) ∈ (U : Set H) := U.one_mem
    rw [← hWU] at this
    exact this
  have hc : Continuous fun p : G × G => p.1⁻¹ * p.2 := by fun_prop
  have h2 : (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' W ∈ 𝓝 ((1, 1) : G × G) :=
    (hW.preimage hc).mem_nhds (by simpa using h1)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 h2
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => (fun y => x⁻¹ * y) ⁻¹' (A ∩ B)) (fun x _ => by
    have : Continuous fun y : G => x⁻¹ * y := by fun_prop
    exact this.continuousAt.preimage_mem_nhds (by simpa using ⟨hA, hB⟩))
  have hch : ∀ x : G, (∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B) → ∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B := fun _ h => h
  choose f hf hf' using hch
  refine ⟨(t.filter fun x => ∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B).attach.image
    fun x => f x.1 (by have h := x.2; rw [Finset.mem_filter] at h; exact h.2), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hf _ _
  · intro k hk
    obtain ⟨x, hx, hxk⟩ := Set.mem_iUnion₂.1 (ht (hΩ k hk))
    have hex : ∃ s ∈ Ω, x⁻¹ * (s : G) ∈ A ∩ B := ⟨k, hk, hxk⟩
    refine ⟨f x hex, Finset.mem_image.2 ⟨⟨x, Finset.mem_filter.2 ⟨hx, hex⟩⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    have h3 := hAB (Set.mk_mem_prod (hf' x hex).1 hxk.2)
    have h4 : (x⁻¹ * (f x hex : G))⁻¹ * (x⁻¹ * (k : G)) = (((f x hex)⁻¹ * k : H) : G) := by
      push_cast; group
    change _ ∈ (U : Set H)
    rw [← hWU]
    change _ ∈ W
    rw [← h4]
    exact h3

theorem isCompact_GL {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] {n : ℕ}
    (C : Fin n → Fin n → Set A) (hC : ∀ i j, IsCompact (C i j)) :
    IsCompact {g : GL (Fin n) A | ∀ i j, g.1 i j ∈ C i j ∧ (g⁻¹).1 i j ∈ C i j} := by
  have h1 : IsCompact {m : Matrix (Fin n) (Fin n) A | ∀ i j, m i j ∈ C i j} :=
    isCompact_pi_infinite fun i => isCompact_pi_infinite (hC i)
  have h2 := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) A)).isCompact_preimage
    (h1.prod (h1.image MulOpposite.continuous_op))
  convert h2 using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image,
    MulOpposite.op_inj, exists_eq_right, forall_and]

theorem exists_compact_denom (D : D7) (d : ℕ) (hd : 0 < d) :
    ∃ C : Set (Af D.host.F ⊗[D.host.F] D.host.E), IsCompact C ∧ ∀ y, d • y ∈ intAE D → y ∈ C := by
  classical
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  let b := RingOfIntegers.basis D.host.E
  let O : AddSubgroup (Af D.host.F) :=
    { carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers D.host.F}
      zero_mem' := fun v => zero_mem _
      add_mem' := fun ha hb v => add_mem (ha v) (hb v)
      neg_mem' := fun ha v => neg_mem (ha v) }
  let φ : (Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) → Af D.host.F) →+
      Af D.host.F ⊗[D.host.F] D.host.E :=
    { toFun := fun a => ∑ i, a i • ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b i : D.host.E))
      map_zero' := by simp
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib] }
  have hφ : Continuous φ :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).fun_smul continuous_const
  have hle : intAE D ≤ (AddSubgroup.pi Set.univ fun _ => O).map φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro y ⟨a, ha, x, rfl⟩
    refine ⟨fun i => b.repr x i • a, fun i _ => zsmul_mem (show a ∈ O from ha) _, ?_⟩
    change ∑ i, (b.repr x i • a) • ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b i : D.host.E)) = _
    conv_rhs => rw [← b.sum_repr x]
    change _ = a ⊗ₜ[D.host.F] (algebraMap (𝓞 D.host.E) D.host.E _)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, smul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact (map_zsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E a) _ _).symm
  have hO : IsCompact (Set.pi Set.univ fun _ : Module.Free.ChooseBasisIndex ℤ (𝓞 D.host.E) =>
      (O : Set (Af D.host.F))) :=
    isCompact_univ_pi fun _ => GlobalTheory.AdeleCocompact.isCompact_integral D.host.F
  let c : Af D.host.F := algebraMap D.host.F (Af D.host.F) (d : D.host.F)⁻¹
  have hcs : Continuous fun y : Af D.host.F ⊗[D.host.F] D.host.E => c • y :=
    (continuous_const (y := c)).fun_smul continuous_id
  refine ⟨(fun y => c • y) '' (φ '' _), (hO.image hφ).image hcs, fun y hy => ?_⟩
  refine ⟨d • y, hle hy, ?_⟩
  have : (d : D.host.F) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  change c • d • y = y
  rw [← Nat.cast_smul_eq_nsmul (Af D.host.F), smul_smul,
    ← map_natCast (algebraMap D.host.F (Af D.host.F)) d, ← map_mul, inv_mul_cancel₀ this, map_one, one_smul]

theorem exists_finset_cover : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ d : ℕ, 0 < d → ∃ S : Finset (GA D V), ∀ k ∈ GfC V, BddDen V d k → ∃ x ∈ S, x⁻¹ * k ∈ U ∧ x⁻¹ * k ∈ GfC V := by
  intro D V U hU d hd
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (AF D.host.F)
  haveI : T2Space (AE D) := e0.isEmbedding.t2Space
  obtain ⟨C, hC, hCd⟩ := exists_compact_denom D d hd
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  let C' : Fin V.rank → Fin V.rank → Set (AE D) := fun i j =>
    e.symm '' ({(1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j} ×ˢ C)
  have hC' : ∀ i j, IsCompact (C' i j) := fun i j => (isCompact_singleton.prod hC).image hc
  have key : ∀ k ∈ GfC V, (∀ i j, d • finMat D.sp.cm.sig V.gram k i j ∈ intAE D) →
      ∀ i j, (matHom V k).1 i j ∈ C' i j := by
    intro k hk h i j
    refine ⟨e ((matHom V k).1 i j), ⟨?_, ?_⟩, e.symm_apply_apply _⟩
    · rw [(he _).1]
      have h1 : (infHom V k).1 i j = _ := congrArg (fun g => g.1 i j) (MonoidHom.mem_ker.1 hk)
      exact h1
    · rw [(he _).2]
      exact hCd _ (h i j)
  obtain ⟨S, hS, hS'⟩ := exists_finset_of_compact (HR (AF D.host.F) D.sp.cm.sig V.gram) U hU _
    (isCompact_GL C' hC') {k : GA D V | k ∈ GfC V ∧ BddDen V d k} (fun k hk i j =>
      ⟨key k hk.1 (fun i j => (hk.2 i j).1) i j, key k⁻¹ (inv_mem hk.1) (fun i j => (hk.2 i j).2) i j⟩)
  refine ⟨S, fun k hk hb => ?_⟩
  obtain ⟨x, hx, hxk⟩ := hS' k ⟨hk, hb⟩
  exact ⟨x, hx, hxk, mul_mem (inv_mem (hS x hx).1) hk⟩

end GlobalTheory.SmoothForms.Cover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NormInfSubmultiplicativeLeAdelicHeight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.SmoothForms.NormInf

theorem entrySum_mul_le {n : Type} [Fintype n] (A B : Matrix n n ℂ) :
    ∑ i, ∑ j, ‖(A * B) i j‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ∑ i, ∑ j, ‖B i j‖ := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j, ‖(A * B) i j‖ ≤ ∑ j, ∑ k, ‖A i k‖ * ‖B k j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    _ = ∑ k, ‖A i k‖ * ∑ j, ‖B k j‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun k => ∑ j, ‖B k j‖)
          (fun k _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ k)

theorem norm_entry_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (i j : n) :
    ‖A i j‖ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ := by
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j (1 : ℂ))
  have h1 : ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ n)‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  refine le_trans (le_of_eq ?_) (PiLp.norm_apply_le _ i)
  congr 1
  change _ = (A *ᵥ Pi.single j 1) i
  simp

theorem sum_mul_add_le {ι : Type} [Fintype ι] (a b c d : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i) :
    ∑ i, (a i * c i + d i * b i) ≤ (∑ i, (a i + b i)) * ∑ i, (c i + d i) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : c i + d i ≤ ∑ i, (c i + d i) :=
    Finset.single_le_sum (f := fun i => c i + d i) (fun i _ => add_nonneg (hc i) (hd i)) (Finset.mem_univ i)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left h (add_nonneg (ha i) (hb i)))
  nlinarith [mul_nonneg (ha i) (hd i), mul_nonneg (hb i) (hc i)]

theorem infMat_mul' {D : D7} (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram θ (g * h) = infMat D.sp.cm.sig V.gram θ g * infMat D.sp.cm.sig V.gram θ h := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (g * h) =
    HA.mat (AF D.host.F) D.sp.cm.sig V.gram g * HA.mat (AF D.host.F) D.sp.cm.sig V.gram h := rfl
  simp only [infMat, this, Units.val_mul]
  rw [Matrix.map_mul, Matrix.map_mul]

theorem infHt_le_height {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau) (g : GA D V) : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ V τ g ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height
  refine le_trans ?_ (le_mul_of_one_le_right' (one_le_finprod' fun _ => le_max_left _ _))
  exact Finset.single_le_prod' (f := fun τ => GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ V τ g)
    (fun _ _ => le_max_left _ _) (Finset.mem_univ τ)

end GlobalTheory.SmoothForms.NormInf

namespace GlobalTheory.SmoothForms


open NormInf in
theorem normInf_mul_le_and_le_height :
    ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
      (∀ g h : GA D V, normInf θ V (g * h) ≤ normInf θ V g * normInf θ V h) ∧
        ∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) := by
  intro D θ V
  refine ⟨fun g h => ?_, ⟨∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (2 : ℝ), fun g => ?_⟩⟩
  · unfold normInf
    simp only [Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin V.rank)))]
    have hn : ∀ (x : GA D V) τ, 0 ≤ ∑ i, ∑ j, ‖infMat D.sp.cm.sig V.gram (θ τ) x i j‖ := fun x τ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    refine le_trans ?_ (sum_mul_add_le _ _ _ _ (hn g) (hn g⁻¹) (hn h) (hn h⁻¹))
    refine Finset.sum_le_sum fun τ _ => ?_
    rw [_root_.mul_inv_rev, infMat_mul', infMat_mul']
    exact add_le_add (entrySum_mul_le _ _) (entrySum_mul_le _ _)
  · unfold normInf
    simp only [Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h0 := infHt_le_height θ V τ g
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ V τ g ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans h0
    have h2 : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ V τ g⁻¹ ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans h0
    have h3 := (norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g) i j).trans (NNReal.coe_le_coe.2 h1)
    have h4 := (norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g⁻¹) i j).trans (NNReal.coe_le_coe.2 h2)
    linarith

end GlobalTheory.SmoothForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NormNatCastAdicCompletionLeOne
section
namespace GlobalTheory.AdicNatCastNorm

theorem norm_natCast_adicCompletion_le_one {F : Type} [inst : Field F] [inst_1 : NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (n : ℕ) :
    ‖(↑n : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)‖ ≤ (1 : ℝ) :=
  IsUltrametricDist.norm_natCast_le_one _ n

end GlobalTheory.AdicNatCastNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NormNatCastLe
section
namespace GlobalTheory.AdicNormZpowEstimates

open IsDedekindDomain NumberField

variable {F : Type} [Field F] [NumberField F]

theorem norm_eq_zpow (v : HeightOneSpectrum (RingOfIntegers F)) (y : v.adicCompletion F)
    (hy : y ≠ 0) : ∃ k : ℤ, ‖y‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ k := by
  have h0 : Valued.v y ≠ 0 := by simpa using hy
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
  exact ⟨_, by push_cast; rfl⟩

theorem one_lt_norm (v : HeightOneSpectrum (RingOfIntegers F)) :
    (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem norm_le_of_lt (v : HeightOneSpectrum (RingOfIntegers F)) (y : v.adicCompletion F) (m : ℤ)
    (h : ‖y‖ < (Ideal.absNorm v.asIdeal : ℝ) ^ (m + 1)) :
    ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  have h1 := one_lt_norm v
  by_cases hy : y = 0
  · rw [hy, norm_zero]
    positivity
  · obtain ⟨k, hk⟩ := norm_eq_zpow v y hy
    rw [hk] at h ⊢
    rw [zpow_lt_zpow_iff_right₀ h1] at h
    exact zpow_le_zpow_right₀ h1.le (by omega)

theorem natCast_eq (v : HeightOneSpectrum (RingOfIntegers F)) (n : ℕ) :
    (n : v.adicCompletion F)
      = FinitePlace.embedding v (algebraMap (RingOfIntegers F) F (n : RingOfIntegers F)) := by
  rw [map_natCast, map_natCast]

theorem norm_natCast_le (v : HeightOneSpectrum (RingOfIntegers F)) (n : ℕ) :
    ‖(n : v.adicCompletion F)‖ ≤ 1 := by
  rw [natCast_eq]
  exact FinitePlace.norm_le_one F v _

theorem norm_absNorm_le (v : HeightOneSpectrum (RingOfIntegers F)) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖
      ≤ (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  have := norm_le_of_lt v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) (-1) (by
    rw [natCast_eq, neg_add_cancel, zpow_zero, FinitePlace.norm_lt_one_iff_mem]
    exact Ideal.absNorm_mem _)
  simpa using this

theorem exists_denominator {F : Type} [Field F] [NumberField F]
    (H : HeightOneSpectrum (RingOfIntegers F) → NNReal) (h1 : ∀ v, (1 : NNReal) ≤ H v)
    (hfin : Set.Finite (Function.mulSupport H)) :
    ∃ d : ℕ, 0 < d ∧ (d : NNReal) ≤ ∏ᶠ v, H v ∧
      ∀ (v : HeightOneSpectrum (RingOfIntegers F)) (y : v.adicCompletion F),
        ‖y‖₊ ≤ H v → ‖(d : v.adicCompletion F) * y‖ ≤ (1 : ℝ) := by
  classical
  have hn : ∀ v : HeightOneSpectrum (RingOfIntegers F), ∃ n : ℕ,
      (Ideal.absNorm v.asIdeal : ℝ) ^ n ≤ H v ∧ (H v : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (n + 1) :=
    fun v => exists_nat_pow_near (by exact_mod_cast h1 v) (one_lt_norm v)
  choose n hle hlt using hn
  refine ⟨∏ v ∈ hfin.toFinset, Ideal.absNorm v.asIdeal ^ n v, ?_, ?_, ?_⟩
  · refine Finset.prod_pos fun v _ => pow_pos ?_ _
    exact lt_trans Nat.one_pos (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  · rw [finprod_eq_prod_of_mulSupport_subset H (s := hfin.toFinset) (by simp), Nat.cast_prod]
    refine Finset.prod_le_prod' fun v _ => ?_
    have := hle v
    exact_mod_cast this
  · intro v y hy
    have hy' : ‖y‖ ≤ (H v : ℝ) := by exact_mod_cast hy
    rw [norm_mul]
    by_cases hv : v ∈ hfin.toFinset
    · have hq := one_lt_norm v
      have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := lt_trans one_pos hq
      have h2 : ‖y‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n v := by
        have := norm_le_of_lt v y (n v) (by
          have := lt_of_le_of_lt hy' (hlt v)
          exact_mod_cast this)
        simpa using this
      rw [← Finset.mul_prod_erase _ _ hv, Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow]
      have h3 : ‖((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)‖ ^ n v
          ≤ ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n v :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_absNorm_le v) _
      calc _ ≤ (((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ n v * 1) * (Ideal.absNorm v.asIdeal : ℝ) ^ n v :=
            mul_le_mul (mul_le_mul h3 (norm_natCast_le v _) (norm_nonneg _) (by positivity)) h2
              (norm_nonneg _) (by positivity)
        _ = 1 := by
            rw [mul_one, ← mul_pow, inv_mul_cancel₀ hq0.ne', one_pow]
    · have h2 : H v = 1 := by simpa using hv
      rw [h2] at hy'
      exact mul_le_one₀ (norm_natCast_le v _) (norm_nonneg _) (by simpa using hy')

end GlobalTheory.AdicNormZpowEstimates
end

