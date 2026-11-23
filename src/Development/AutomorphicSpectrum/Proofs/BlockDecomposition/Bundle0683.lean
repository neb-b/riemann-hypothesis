module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0680
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0150
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0679
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0681

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralOfCharacterTrivialOnLattice
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.DualInt

private theorem trace_single_one_mul {n : ℕ} {R : Type} [CommRing R] (i j : Fin n) (c : R)
    (T : Matrix (Fin n) (Fin n) R) : (Matrix.single j i c * T).trace = c * T i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

theorem mem_of_dual_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D), GoodPsi D ψ v → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) (Fv D.host.F v)), (∀ X : Matrix (Fin n) (Fin n) (Fv D.host.F v), (∀ i j, X i j ∈ v.adicCompletionIntegers D.host.F) → psiV D.host.F ψ v (Matrix.trace (X * T)) = 1) → ∀ i j, T i j ∈ v.adicCompletionIntegers D.host.F := by
  intro D ψ v hψ n T hT i j
  by_contra hx
  set O := v.adicCompletionIntegers D.host.F with hO
  have hx0 : T i j ≠ 0 := by
    intro h
    exact hx (h ▸ O.zero_mem)
  have hy : (T i j)⁻¹ ∈ O := (O.mem_or_inv_mem (T i j)).resolve_left hx
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : (ϖ : v.adicCompletion D.host.F) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hw : (T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F) ∈ O := by
    rcases O.mem_or_inv_mem ((T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F)) with h | h
    · exact h
    · have h' : (ϖ : v.adicCompletion D.host.F) / (T i j)⁻¹ ∈ O := by
        simpa [inv_div] using h
      have hfac : ϖ = (⟨(T i j)⁻¹, hy⟩ : O) * ⟨_, h'⟩ := by
        apply Subtype.ext
        simp only [MulMemClass.coe_mul]
        field_simp
      rcases hϖ.isUnit_or_isUnit hfac with hu | hu
      · exfalso
        apply hx
        obtain ⟨u, hu⟩ := hu
        have hmem : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) ∈ O := Subtype.property _
        have heq : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) = T i j := by
          have h1 : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) * (((u : Oˣ) : O) : v.adicCompletion D.host.F) = 1 := by
            rw [← MulMemClass.coe_mul, Units.inv_mul]
            rfl
          rw [hu] at h1
          field_simp at h1
          simpa using h1
        exact heq ▸ hmem
      · obtain ⟨u, hu⟩ := hu
        have hmem : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) ∈ O := Subtype.property _
        have heq : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) = (T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F) := by
          have h1 : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) * (((u : Oˣ) : O) : v.adicCompletion D.host.F) = 1 := by
            rw [← MulMemClass.coe_mul, Units.inv_mul]
            rfl
          rw [hu] at h1
          simp only at h1
          rw [eq_div_iff hϖ0]
          rw [div_inv_eq_mul, ← mul_assoc] at h1
          exact eq_inv_of_mul_eq_one_left h1
        exact heq ▸ hmem
  obtain ⟨b, hb⟩ := hψ.2 ϖ hϖ
  have hb2 : (b : v.adicCompletion D.host.F) ∈ O := b.2
  apply hb
  have hX := hT (Matrix.single j i ((b : v.adicCompletion D.host.F) * ((T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F)))) (by
    intro k l
    rw [Matrix.single_apply]
    split_ifs
    · exact mul_mem hb2 hw
    · exact O.zero_mem)
  rw [trace_single_one_mul] at hX
  convert hX using 2
  field_simp

end GlobalTheory.CompanionTheory.Jp.DualInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeStabilizerCompact
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.CompanionTheory.KFin.CompactStab

section Abstract

variable {R : Type} [CommRing R] {O : Subring R} {n : ℕ}

theorem exists_common_denom (hden : ∀ a : R, ∃ s ∈ O, IsUnit s ∧ s * a ∈ O) {ι : Type} (T : Finset ι) (f : ι → R) :
    ∃ w ∈ O, IsUnit w ∧ ∀ i ∈ T, w * f i ∈ O := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, O.one_mem, isUnit_one, by simp⟩
  | insert a T _ ih =>
    obtain ⟨w, hw, hwu, h⟩ := ih
    obtain ⟨s, hs, hsu, h'⟩ := hden (f a)
    refine ⟨w * s, O.mul_mem hw hs, hwu.mul hsu, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · rw [mul_assoc]; exact O.mul_mem hw h'
    · rw [mul_right_comm]; exact O.mul_mem (h i hi) hs

theorem smul_mem_of_mem {Λ : Submodule O (Fin n → R)} {a : R} {z : Fin n → R} (ha : a ∈ O) (hz : z ∈ Λ) :
    a • z ∈ Λ :=
  Λ.smul_of_tower_mem (⟨a, ha⟩ : O) hz

theorem exists_smul_mem (hden : ∀ a : R, ∃ s ∈ O, IsUnit s ∧ s * a ∈ O) {Λ : Submodule O (Fin n → R)}
    (hs : Submodule.span R (Λ : Set (Fin n → R)) = ⊤) (x : Fin n → R) : ∃ s ∈ O, IsUnit s ∧ s • x ∈ Λ := by
  have hx : x ∈ Submodule.span R (Λ : Set (Fin n → R)) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, O.one_mem, isUnit_one, by simpa using hx⟩
  | zero => exact ⟨1, O.one_mem, isUnit_one, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs₁, hs₂, hs₃⟩ := hx
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := hy
    refine ⟨s * t, O.mul_mem hs₁ ht₁, hs₂.mul ht₂, ?_⟩
    have : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm t s]
    rw [this]
    exact Λ.add_mem (smul_mem_of_mem ht₁ hs₃) (smul_mem_of_mem hs₁ ht₃)
  | smul a x _ hx =>
    obtain ⟨s, hs₁, hs₂, hs₃⟩ := hx
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := hden a
    refine ⟨t * s, O.mul_mem ht₁ hs₁, ht₂.mul hs₂, ?_⟩
    have : (t * s) • a • x = (t * a) • (s • x) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]
    exact smul_mem_of_mem ht₃ hs₃

theorem exists_unit_inner (hden : ∀ a : R, ∃ s ∈ O, IsUnit s ∧ s * a ∈ O) {Λ : Submodule O (Fin n → R)}
    (hs : Submodule.span R (Λ : Set (Fin n → R)) = ⊤) :
    ∃ u ∈ O, IsUnit u ∧ ∀ x : Fin n → R, (∀ i, x i ∈ O) → u • x ∈ Λ := by
  classical
  have h1 : ∀ T : Finset (Fin n), ∃ u ∈ O, IsUnit u ∧ ∀ j ∈ T, u • (Pi.single j 1 : Fin n → R) ∈ Λ := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨1, O.one_mem, isUnit_one, by simp⟩
    | insert a T _ ih =>
      obtain ⟨w, hw, hwu, h⟩ := ih
      obtain ⟨s, hs₁, hsu, h'⟩ := exists_smul_mem hden hs (Pi.single a 1 : Fin n → R)
      refine ⟨w * s, O.mul_mem hw hs₁, hwu.mul hsu, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [mul_smul]; exact smul_mem_of_mem hw h'
      · rw [mul_comm, mul_smul]; exact smul_mem_of_mem hs₁ (h i hi)
  obtain ⟨u, hu, huu, h⟩ := h1 Finset.univ
  refine ⟨u, hu, huu, fun x hx => ?_⟩
  have e : u • x = ∑ j, x j • (u • (Pi.single j 1 : Fin n → R)) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  rw [e]
  exact sum_mem fun j _ => smul_mem_of_mem (hx j) (h j (Finset.mem_univ _))

theorem exists_unit_outer (hden : ∀ a : R, ∃ s ∈ O, IsUnit s ∧ s * a ∈ O) {Λ : Submodule O (Fin n → R)}
    (hfg : Λ.FG) : ∃ w ∈ O, IsUnit w ∧ ∀ y ∈ Λ, ∀ i, w * y i ∈ O := by
  classical
  obtain ⟨T, rfl⟩ := hfg
  obtain ⟨w, hw, hwu, h⟩ := exists_common_denom hden (T ×ˢ (Finset.univ : Finset (Fin n))) (fun p => p.1 p.2)
  refine ⟨w, hw, hwu, fun y hy i => ?_⟩
  induction hy using Submodule.span_induction with
  | mem y hy => exact h (y, i) (Finset.mem_product.2 ⟨hy, Finset.mem_univ _⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [Pi.add_apply, mul_add]; exact O.add_mem hy hz
  | smul c y _ hy =>
    have : w * (c • y) i = c * (w * y i) := by
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]; ring
    rw [this]
    exact O.mul_mem c.2 hy

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem isOpen_lattice (ho : IsOpen (O : Set R)) (hden : ∀ a : R, ∃ s ∈ O, IsUnit s ∧ s * a ∈ O)
    {Λ : Submodule O (Fin n → R)} (hs : Submodule.span R (Λ : Set (Fin n → R)) = ⊤) :
    IsOpen (Λ : Set (Fin n → R)) := by
  obtain ⟨u, -, huu, h⟩ := exists_unit_inner hden hs
  obtain ⟨c, rfl⟩ := huu
  have hU : IsOpen {x : Fin n → R | ∀ i, ((c⁻¹ : Rˣ) : R) * x i ∈ O} := by
    have : {x : Fin n → R | ∀ i, ((c⁻¹ : Rˣ) : R) * x i ∈ O} =
        ⋂ i, (fun x : Fin n → R => ((c⁻¹ : Rˣ) : R) * x i) ⁻¹' (O : Set R) := by
      ext x; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => ho.preimage (continuous_const.mul (continuous_apply i))
  have hsub : {x : Fin n → R | ∀ i, ((c⁻¹ : Rˣ) : R) * x i ∈ O} ⊆ (Λ : Set (Fin n → R)) := fun x hx => by
    have := h (fun i => ((c⁻¹ : Rˣ) : R) * x i) hx
    have e : (c : R) • (fun i => ((c⁻¹ : Rˣ) : R) * x i) = x := by
      funext i
      simp
    rwa [e] at this
  have h0 : (Λ : Set (Fin n → R)) ∈ nhds (0 : Fin n → R) :=
    Filter.mem_of_superset (hU.mem_nhds fun i => by simp [O.zero_mem]) hsub
  exact AddSubgroup.isOpen_of_mem_nhds Λ.toAddSubgroup h0

variable [T2Space R]

theorem isCompact_stabGL (hc : IsCompact (O : Set R)) (ho : IsOpen (O : Set R))
    (hden : ∀ a : R, ∃ s ∈ O, IsUnit s ∧ s * a ∈ O) {Λ : Submodule O (Fin n → R)} (hfg : Λ.FG)
    (hs : Submodule.span R (Λ : Set (Fin n → R)) = ⊤) :
    IsCompact {M : GL (Fin n) R | ∀ y, y ∈ Λ ↔ M.1 *ᵥ y ∈ Λ} := by
  classical
  obtain ⟨u, -, huu, hu⟩ := exists_unit_inner hden hs
  obtain ⟨w, -, hwu, hw⟩ := exists_unit_outer hden hfg
  obtain ⟨c, hcdef⟩ := hwu.mul huu
  have hb : ∀ M : GL (Fin n) R, (∀ y, y ∈ Λ → M.1 *ᵥ y ∈ Λ) → ∀ i j, (c : R) * M.1 i j ∈ O := by
    intro M hM i j
    have h1 := hu (Pi.single j 1) (fun i => by
      by_cases e : i = j
      · subst e; simp [O.one_mem]
      · simp [e, O.zero_mem])
    have h2 := hw _ (hM _ h1) i
    have e : w * (M.1 *ᵥ (u • (Pi.single j 1 : Fin n → R))) i = (c : R) * M.1 i j := by
      rw [hcdef, Matrix.mulVec_smul, Pi.smul_apply, Matrix.mulVec_single_one, smul_eq_mul, mul_assoc]
      rfl
    rwa [e] at h2
  let C : Set R := (fun z => ((c⁻¹ : Rˣ) : R) * z) '' (O : Set R)
  have hC : IsCompact C := hc.image (continuous_const.mul continuous_id)
  have hmem : ∀ a : R, (c : R) * a ∈ O → a ∈ C := fun a ha => ⟨_, ha, by simp⟩
  let S : Set (Matrix (Fin n) (Fin n) R) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  have hK := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)).isCompact_preimage
    (hS.prod (hS.image MulOpposite.continuous_op))
  have hop := isOpen_lattice ho hden hs
  have hcl : IsClosed (Λ : Set (Fin n → R)) := AddSubgroup.isClosed_of_isOpen Λ.toAddSubgroup hop
  refine hK.of_isClosed_subset ?_ fun M hM => ?_
  · have e : {M : GL (Fin n) R | ∀ y, y ∈ Λ ↔ M.1 *ᵥ y ∈ Λ} =
        ⋂ y, {M : GL (Fin n) R | y ∈ Λ ↔ M.1 *ᵥ y ∈ Λ} := by
      ext M; simp
    rw [e]
    refine isClosed_iInter fun y => ?_
    have hcont : Continuous fun M : GL (Fin n) R => M.1 *ᵥ y :=
      Continuous.matrix_mulVec Units.continuous_val continuous_const
    by_cases hy : y ∈ Λ
    · have : {M : GL (Fin n) R | y ∈ Λ ↔ M.1 *ᵥ y ∈ Λ} = (fun M : GL (Fin n) R => M.1 *ᵥ y) ⁻¹' (Λ : Set _) := by
        ext M; simp [hy]
      rw [this]
      exact hcl.preimage hcont
    · have : {M : GL (Fin n) R | y ∈ Λ ↔ M.1 *ᵥ y ∈ Λ} = (fun M : GL (Fin n) R => M.1 *ᵥ y) ⁻¹' (Λ : Set _)ᶜ := by
        ext M; simp [hy]
      rw [this]
      exact hop.isClosed_compl.preimage hcont
  · have hM' : ∀ y, y ∈ Λ → M.1 *ᵥ y ∈ Λ := fun y hy => (hM y).1 hy
    have hMi : ∀ y, y ∈ Λ → (M⁻¹).1 *ᵥ y ∈ Λ := fun y hy => by
      refine (hM _).2 ?_
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
      simpa using hy
    exact ⟨fun i _ j _ => hmem _ (hb M hM' i j), (M⁻¹).1, fun i _ j _ => hmem _ (hb M⁻¹ hMi i j), rfl⟩

end Abstract

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_denom_intLoc (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E) :
    ∃ s ∈ intLoc F E v, IsUnit s ∧ s * z ∈ intLoc F E v := by
  have key : ∃ d : (𝓞 E)⁰, ((1 : Fv F v) ⊗ₜ[F] ((d : 𝓞 E) : E)) * z ∈ intLoc F E v := by
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨1, by rw [mul_zero]; exact zero_mem _⟩
    | tmul a x =>
      obtain ⟨c, hc, hca⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v a
      obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
      have hm0 : algebraMap (𝓞 E) E m ≠ 0 := by simpa using nonZeroDivisors.ne_zero hm
      have hc' : algebraMap (𝓞 F) (𝓞 E) c ∈ (𝓞 E)⁰ := mem_nonZeroDivisors_of_ne_zero (by
        simpa using nonZeroDivisors.ne_zero hc)
      refine ⟨⟨_, mul_mem hc' hm⟩, ?_⟩
      convert tmul_mem_intLoc (E := E) hca n using 1
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have e : (((algebraMap (𝓞 F) (𝓞 E) c * m : 𝓞 E)) : E) * (algebraMap (𝓞 E) E n / algebraMap (𝓞 E) E m) =
          (c : F) • (n : E) := by
        rw [Algebra.smul_def]
        change algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) c * m) * _ = algebraMap F E (algebraMap (𝓞 F) F c) * algebraMap (𝓞 E) E n
        rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        field_simp
      rw [e, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
      rfl
    | add y z hy hz =>
      obtain ⟨c, hc⟩ := hy
      obtain ⟨d, hd⟩ := hz
      refine ⟨c * d, ?_⟩
      have e : ((1 : Fv F v) ⊗ₜ[F] (((c * d : (𝓞 E)⁰) : 𝓞 E) : E)) * (y + z) =
          ((1 : Fv F v) ⊗ₜ[F] ((d : 𝓞 E) : E)) * (((1 : Fv F v) ⊗ₜ[F] ((c : 𝓞 E) : E)) * y) +
          ((1 : Fv F v) ⊗ₜ[F] ((c : 𝓞 E) : E)) * (((1 : Fv F v) ⊗ₜ[F] ((d : 𝓞 E) : E)) * z) := by
        rw [← mul_assoc, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_add]
        simp [mul_comm]
      rw [e]
      exact add_mem (mul_mem (tmul_mem_intLoc (one_mem _) _) hc) (mul_mem (tmul_mem_intLoc (one_mem _) _) hd)
  obtain ⟨d, hd⟩ := key
  have hd0 : ((d : 𝓞 E) : E) ≠ 0 := by simpa using nonZeroDivisors.ne_zero d.2
  refine ⟨_, tmul_mem_intLoc (one_mem _) (d : 𝓞 E), IsUnit.of_mul_eq_one ((1 : Fv F v) ⊗ₜ[F] ((d : 𝓞 E) : E)⁻¹) ?_, hd⟩
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hd0, ← Algebra.TensorProduct.one_def]

end Place

theorem isCompact_stabLat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, IsCMExt F E σ → IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)), IsLat (intLoc F E v) Λ → IsCompact (stabLat σ J Λ : Set (GLoc σ J v)) := by
  intro F E _ _ _ _ _ σ n J _ _ v Λ hΛ
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
  haveI : T2Space (Fv F v ⊗[F] E) := e.isEmbedding.t2Space
  have hcl : IsClosed (HR (Fv F v) σ J : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
    have hv : Continuous fun g : GL (Fin n) (Fv F v ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR (Fv F v) σ)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hv) continuous_const
  have hemb : Topology.IsClosedEmbedding (matHom (Fv F v) σ J) := hcl.isClosedEmbedding_subtypeVal
  exact hemb.isCompact_preimage (isCompact_stabGL (GlobalTheory.ThK.isCompact_isOpen_intLoc v).1 (GlobalTheory.ThK.isCompact_isOpen_intLoc v).2
    (exists_denom_intLoc v) hΛ.1 hΛ.2)

end GlobalTheory.CompanionTheory.KFin.CompactStab
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTranslationPreservedStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_translation_preserved : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (γ : G D p), γ ∈ GF D p → ∃ T : (Mx D ρ p × Mx D ρ p) ≃ₜ+ (Mx D ρ p × Mx D ρ p), (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) ∧ (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E, T.symm (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) ∧ ∀ y x : Mx D ρ p, ∃ z' : hermA D ρ, M.emb γ * (M.nzx 0 x * M.sh y) = M.nzx z' (T (y, x)).2 * M.sh (T (y, x)).1 * M.emb γ := by
  first | exact @GlobalTheory.CompanionTheory.FJE.Transport.transport | exact GlobalTheory.CompanionTheory.FJE.Transport.transport | (intros; apply GlobalTheory.CompanionTheory.FJE.Transport.transport <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalImageOfUnipotentElement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem block_unipotent_map {A B : Type} {m : ℕ} [Zero A] [One A] [Zero B] [One B] [DecidableEq (Fin m)] (f : A → B) (f0 : f 0 = 0)
    (f1 : f 1 = 1) (x : Matrix (Fin m) (Fin m) A) :
    (blk4 (1 : Matrix (Fin m) (Fin m) A) x 0 1).map f = blk4 1 (x.map f) 0 1 := by
  refine Matrix.ext fun i j => ?_
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply, apply_ite f, f0, f1]

theorem splitHom_proj_nMap (D : D7) (n : ℕ) (nb : hermA D n → G D n) (h : IsNMap nb) (v : Pl D)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : hermA D n) :
    (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1 =
      blk4 1 (tauC τ x.1) 0 1 := by
  have e1 := GlobalTheory.LocIntw.matR_mapH (evFin D.host.F v) (nb x)
  rw [GlobalTheory.LocIntw.matR_adele, h x] at e1
  have e2 : (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1 =
      (GlobalTheory.LocIntw.matR (Fv D.host.F v) D.sp.cm.sig
        (proj D.sp.cm.sig (Jst D n) v (nb x))).map (splitProj τ) := rfl
  have e3 : (GlobalTheory.LocIntw.matR (Fv D.host.F v) D.sp.cm.sig
      (proj D.sp.cm.sig (Jst D n) v (nb x))) = (blk4 1 x.1 0 1).map (cv D v) := e1
  rw [e2, e3, block_unipotent_map _ (map_zero _) (map_one _), block_unipotent_map _ (map_zero _) (map_one _)]
  rfl

theorem thU_proj_nMap (D : D7) (n : ℕ) (nb : hermA D n → G D n) (h : IsNMap nb) (v : Pl D)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : hermA D n) :
    thU D n v τ (proj D.sp.cm.sig (Jst D n) v (nb x)) = nU (tauC τ x.1) := by
  have e := splitHom_proj_nMap D n nb h v τ x
  refine Units.ext (Matrix.ext fun i j => ?_)
  have e' : (thU D n v τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1 i j =
      (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v (nb x))).1
        (finSumFinEquiv i) (finSumFinEquiv j) := rfl
  rw [e', e]
  change (Matrix.fromBlocks 1 (tauC τ x.1) 0 1 : Matrix _ _ _)
    (finSumFinEquiv.symm (finSumFinEquiv i)) (finSumFinEquiv.symm (finSumFinEquiv j)) =
      (Matrix.fromBlocks 1 (tauC τ x.1) 0 1 : Matrix _ _ _) i j
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.Jp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalizedValuationUniformizer
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem nvOK_nvL : ∀ (D : D7) (v : Pl D) (ϖ : Ov D v), Irreducible ϖ → ∀ w : (Lv D v)ˣ,
    (w : Lv D v) = algebraMap (Ov D v) (Lv D v) ϖ → NvOK (O := Ov D v) (nvL D v) w := by
  intro D v ϖ hϖ w hw
  have hu1 : Formalism.UG.IsUnifV D.host.F v (algebraMap (Ov D v) (Lv D v) ϖ) := by
    unfold Formalism.UG.IsUnifV
    rw [GlobalTheory.SplitDetValue.valued_irreducible v hϖ] <;> rfl
  have hn : ‖algebraMap (Ov D v) (Lv D v) ϖ‖₊ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ :=
    GlobalTheory.norm_uniformiser_eq_inv_absNorm D.host.F v _ hu1
  have hc : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ ≠ 0 := by
    rw [Ne, inv_eq_zero, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  unfold NvOK
  refine ⟨fun u => ?_, ?_⟩
  · show ‖algebraMap (Ov D v) (Lv D v) (u : Ov D v)‖₊ = 1
    have hu2 : Formalism.UG.IsUnifV D.host.F v (algebraMap (Ov D v) (Lv D v) ((u : Ov D v) * ϖ)) := by
      unfold Formalism.UG.IsUnifV
      rw [map_mul, map_mul, GlobalTheory.SplitDetValue.valued_unit v u, GlobalTheory.SplitDetValue.valued_irreducible v hϖ,
        one_mul] <;> rfl
    have h2 := GlobalTheory.norm_uniformiser_eq_inv_absNorm D.host.F v _ hu2
    rw [map_mul, nnnorm_mul, hn] at h2
    exact (mul_eq_right₀ hc).mp h2
  · show ‖(w : Lv D v)‖₊ = _
    rw [hw, hn, Fintype.card_eq_nat_card, GlobalTheory.SplitDetValue.card_residue_eq]

end GlobalTheory.CompanionTheory.Jp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodicPartialFourierMeanStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_partial_fourier_mean : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ : hermA D n → ℂ), IsPer Φ → IsPer (pm hn m ψ b₀ Φ) := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.isPer_pm | exact GlobalTheory.CompanionTheory.PcFc.isPer_pm | (intros; apply GlobalTheory.CompanionTheory.PcFc.isPer_pm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftCommutesLeviEmbeddingStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shift_commutes_levi_embedding : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₀ : G D p) (a : GL (Fin p) (AE D)),
  mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1) → ∀ y : Mx D ρ p, M.sh y * M.emb g₀ = M.emb g₀ * M.sh (HMul.hMul y a.1 : Mx D ρ p) := by
  first | exact @GlobalTheory.CompanionTheory.PcB.sh_emb_levi | exact GlobalTheory.CompanionTheory.PcB.sh_emb_levi | (intros; apply GlobalTheory.CompanionTheory.PcB.sh_emb_levi <;> assumption)
end

