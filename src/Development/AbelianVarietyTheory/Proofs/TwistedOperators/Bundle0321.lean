module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetIntegralAdeleMulVecMemLatticeClosure
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
namespace GlobalTheory.AdelicLatticeIntegral

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nsmul_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E)
    (x : Fin n → E) : ∃ D : ℕ, D ≠ 0 ∧ D • x ∈ L := by
  exact _root_.GlobalTheory.NatMultipleInLattice.exists_nsmul_mem_lattice L hL x

theorem exists_nsmul_map_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E)
    (N : (Fin n → E) →ₗ[E] (Fin n → E)) : ∃ D : ℕ, D ≠ 0 ∧ ∀ y ∈ L, D • N y ∈ L := by
  obtain ⟨s, hs⟩ := hL.fg
  choose! D hD hDm using fun g => exists_nsmul_mem L hL (N g)
  refine ⟨∏ g ∈ s, D g, Finset.prod_ne_zero_iff.mpr fun g _ => hD g, ?_⟩
  intro y hy
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem D hg
      rw [hk, mul_comm, mul_smul]; exact nsmul_mem (hDm g) k
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact L.add_mem hx hy
  | smul r x _ hx =>
      have : N (r • x) = r • N x := N.map_smul_of_tower r x
      rw [this, smul_comm]; exact L.smul_mem r hx

end GlobalTheory.AdelicLatticeIntegral

namespace GlobalTheory.AdelicLatticeIntegral

theorem exists_finset_smul_mulVec_mem_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (L : Submodule (𝓞 E) (Fin n → E)), L.IsFullLattice E →
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ w ∉ S₁, ∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a →
      GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F → ∀ y ∈ L,
      a • (M *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)} := by
  intro F E _ _ _ _ _ n M L hL
  classical
  let bF := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) bF
  let c : Fin n × Fin n × Fin (Module.finrank F E) → AF F := fun j => B.repr (M j.1 j.2.1) j.2.2
  let Nm : Fin n × Fin n × Fin (Module.finrank F E) → (Fin n → E) →ₗ[E] (Fin n → E) := fun j =>
    (LinearMap.single E (fun _ : Fin n => E) j.1) ∘ₗ (bF j.2.2 • LinearMap.proj j.2.1)
  let incV : (Fin n → E) → (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := fun y i =>
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)
  have key : ∀ y, (M *ᵥ incV y) = ∑ j, c j • incV (Nm j y) := by
    intro y
    funext r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply]
    rw [Fintype.sum_prod_type]
    symm
    rw [Finset.sum_eq_single r]
    · rw [Fintype.sum_prod_type]
      symm
      refine Finset.sum_congr rfl fun q _ => ?_
      conv_lhs => rw [← B.sum_repr (M r q)]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Nm, incV, B, c, Algebra.TensorProduct.basis_apply, smul_mul_assoc, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
    · intro p _ hp
      simp [Nm, incV, Pi.single_apply, Ne.symm hp]
    · simp
  choose D hD0 hDL using fun j => exists_nsmul_map_mem L hL (Nm j)
  let c' : Fin n × Fin n × Fin (Module.finrank F E) → AF F :=
    fun j => c j * algebraMap F (AF F) ((D j : F)⁻¹)
  have hfin : ∀ j, {w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) |
      ¬ GlobalTheory.AdelicU.evFin F w (c' j) ∈ w.adicCompletionIntegers F}.Finite :=
    fun j => Filter.eventually_cofinite.mp (GlobalTheory.AlgCountDim.eventually_evFin_integral (c' j))
  refine ⟨(Set.finite_iUnion hfin).toFinset, ?_⟩
  intro w hw a ha hai y hy
  have hc' : ∀ j, GlobalTheory.AdelicU.evFin F w (c' j) ∈ w.adicCompletionIntegers F := by
    intro j
    by_contra h
    exact hw ((Set.Finite.mem_toFinset _).mpr (Set.mem_iUnion.mpr ⟨j, h⟩))
  have hterm : ∀ j, a • (c j • incV (Nm j y)) = (a * c' j) • incV (D j • Nm j y) := by
    intro j
    have h1 : incV (D j • Nm j y) = D j • incV (Nm j y) := by
      funext i; simp [incV]
    rw [h1, ← Nat.cast_smul_eq_nsmul (AF F), smul_smul, smul_smul]
    congr 1
    have h2 : (D j : F) ≠ 0 := Nat.cast_ne_zero.mpr (hD0 j)
    simp only [c', mul_assoc]
    rw [← map_natCast (algebraMap F (AF F)), ← map_mul, inv_mul_cancel₀ h2, map_one, mul_one]
  change a • (M *ᵥ incV y) ∈ _
  rw [key, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  rw [hterm j]
  refine AddSubgroup.subset_closure ⟨a * c' j, ?_, ?_, D j • Nm j y, hDL j y hy, rfl⟩
  · intro u hu
    rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u a, ha u hu, zero_mul]
  · rw [map_mul]; exact mul_mem hai (hc' j)

end GlobalTheory.AdelicLatticeIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFunctionalPure
section
noncomputable section

open NumberField IsDedekindDomain Filter

namespace GlobalTheory.FiniteAdelicPoints

theorem exists_functional {ι V : Type} [AddCommGroup V] [Module ℂ V] (p : ι → V) (a : ι → ℂ)
    (h : ∀ (s : Finset ι) (c : ι → ℂ), ∑ i ∈ s, c i • p i = 0 → ∑ i ∈ s, c i * a i = 0) :
    ∃ Λ : V →ₗ[ℂ] ℂ, ∀ i, Λ (p i) = a i := by
  classical

  let P : (ι →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ p
  let A : (ι →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ a

  have hk : LinearMap.ker P ≤ LinearMap.ker A := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have h0 : ∑ i ∈ c.support, c i • p i = 0 := by
      simpa [P, Finsupp.linearCombination_apply, Finsupp.sum] using hc
    simpa [A, Finsupp.linearCombination_apply, Finsupp.sum] using h c.support c h0

  let B : LinearMap.range P →ₗ[ℂ] ℂ :=
    ((LinearMap.ker P).liftQ A hk).comp (P.quotKerEquivRange.symm : LinearMap.range P →ₗ[ℂ] _)
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend B
  refine ⟨Λ, fun i => ?_⟩
  have hp : P (Finsupp.single i 1) = p i := by simp [P]
  have hA : A (Finsupp.single i 1) = a i := by simp [A]
  calc Λ (p i) = Λ (P (Finsupp.single i 1)) := by rw [hp]
    _ = B ⟨P (Finsupp.single i 1), LinearMap.mem_range_self P _⟩ := by rw [← hΛ]; rfl
    _ = A (Finsupp.single i 1) := by
      simp only [B, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
    _ = a i := hA

theorem sum_prod_apply {ι P : Type} {X : P → Type} [∀ v, Nonempty (X v)] (s : Finset ι) (φ : ι → ∀ v, X v → ℂ)
    (l : ∀ v, (X v → ℂ) →ₗ[ℂ] ℂ) (T : Finset P) :
    ∀ c : ι → ℂ, (∀ y : ∀ v, X v, ∑ i ∈ s, c i * ∏ v ∈ T, φ i v (y v) = 0) →
      ∑ i ∈ s, c i * ∏ v ∈ T, l v (φ i v) = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro c hc
    simpa using hc (fun v => Classical.arbitrary (X v))
  | insert w T hw ih =>
    intro c hc

    have key : ∀ y : ∀ v, X v, ∑ i ∈ s, (c i * l w (φ i w)) * ∏ v ∈ T, φ i v (y v) = 0 := by
      intro y
      have hfun : (∑ i ∈ s, (c i * ∏ v ∈ T, φ i v (y v)) • φ i w) = 0 := by
        funext t
        have hupd : ∀ i, ∏ v ∈ T, φ i v (Function.update y w t v) = ∏ v ∈ T, φ i v (y v) := fun i =>
          Finset.prod_congr rfl fun v hv => by
            rw [Function.update_of_ne (fun h => hw (by rw [← h]; exact hv))]
        have h1 := hc (Function.update y w t)
        simp only [Finset.prod_insert hw, Function.update_self, hupd] at h1
        rw [Finset.sum_apply, Pi.zero_apply, ← h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring

      have h2 := congrArg (l w) hfun
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at h2
      simp only [map_smul, smul_eq_mul] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have h3 := ih (fun i => c i * l w (φ i w)) key
    rw [← h3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.prod_insert hw]
    ring

variable {F : Type} [Field F] [NumberField F]


open Classical in
def finAd (T : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) :
    FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ T then y v else 0, by
    filter_upwards [T.eventually_cofinite_notMem] with v hv
    simp only [hv, if_false]
    exact zero_mem _⟩

def adPt {κ : Type} (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (x : κ → mixedEmbedding.mixedSpace F)
    (y : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F :=
  fun k => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x k), finAd T fun v => y v k)


open Classical in
theorem pure_apply {κ : Type} [Fintype κ] (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)))
    (hφ : ∀ v ∉ T, φ v 0 = 1) (x : κ → mixedEmbedding.mixedSpace F)
    (y : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ (adPt T x y) = f x * ∏ v ∈ T, φ v (y v) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure

  have h1 : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (adPt T x y i)) = x := by
    funext i
    change (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i)) = x i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x i)

  have h2 : ∀ v, (fun i => GlobalTheory.AdelicU.evFin F v (adPt T x y i)) =
      fun i => if v ∈ T then y v i else (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) := fun v => by
    funext i
    rfl
  rw [h1]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T)]
  · refine Finset.prod_congr rfl fun v hv => ?_
    rw [h2 v]
    simp only [if_pos hv]
  · intro v hv
    by_contra hvT
    have hvT' : v ∉ T := by simpa using hvT
    have h0 : (fun i => if v ∈ T then y v i else (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) = 0 := by
      funext i
      simp [hvT']
    rw [Function.mem_mulSupport, h2 v, h0] at hv
    exact hv (hφ v hvT')

theorem exists_functional_pure {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (vac : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)
    (hvac : ∀ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) in Filter.cofinite, vac v =
      Set.indicator {x : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v | ∀ (i : κ), x i ∈ HeightOneSpectrum.adicCompletionIntegers F v}
        (1 : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ))
    (lam : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ℂ)
    (l : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (hl : Set.Finite {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) | l v (vac v) ≠ 1}) :
    ∃ (Λ : ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) →ₗ[ℂ] ℂ),
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) in Filter.cofinite, φ v = vac v) →
        Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = lam f * ∏ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), l v (φ v) := by
  classical

  obtain ⟨Λ, hΛ⟩ := exists_functional
    (ι := {q : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ × ((v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) //
      ∀ᶠ v in Filter.cofinite, q.2 v = vac v})
    (fun q => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure q.1.1 q.1.2) (fun q => lam q.1.1 * ∏ᶠ v, l v (q.1.2 v)) (by
    intro s c hc

    have f1 := Filter.eventually_cofinite.1 hvac
    have f2 := s.finite_toSet.biUnion fun q _ => Filter.eventually_cofinite.1 q.2
    let T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) := ((hl.union f1).union f2).toFinset
    have hout : ∀ v ∉ T, l v (vac v) = 1 ∧ (∀ q ∈ s, q.1.2 v = vac v) ∧ vac v 0 = 1 := by
      intro v hv
      simp only [T, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe,
        not_or, not_exists, not_not, ne_eq] at hv
      obtain ⟨⟨hv0, hv1⟩, hv2⟩ := hv
      refine ⟨hv0, fun q hq => hv2 q hq, ?_⟩
      rw [hv1]
      have hz : (0 : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∈
          {x : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v | ∀ i, x i ∈ HeightOneSpectrum.adicCompletionIntegers F v} :=
        fun i => zero_mem _
      rw [Set.indicator_of_mem hz, Pi.one_apply]

    have hrel : ∀ (x : κ → mixedEmbedding.mixedSpace F) (y : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v),
        ∑ q ∈ s, c q * (q.1.1 x * ∏ v ∈ T, q.1.2 v (y v)) = 0 := by
      intro x y
      have h0 := congrFun hc (adPt T x y)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [pure_apply q.1.1 q.1.2 T (fun v hv => by rw [(hout v hv).2.1 q hq, (hout v hv).2.2]) x y]

    have hrel2 : ∀ y : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v,
        ∑ q ∈ s, (c q * lam q.1.1) * ∏ v ∈ T, q.1.2 v (y v) = 0 := by
      intro y
      have hz : ∑ q ∈ s, (c q * ∏ v ∈ T, q.1.2 v (y v)) • q.1.1 = 0 := by
        ext x
        simp only [sum_apply, smul_apply, smul_eq_mul, zero_apply]
        rw [← hrel x y]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
      have h0 := congrArg lam hz
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at h0
      simp only [map_smul, smul_eq_mul] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring

    have h3 := sum_prod_apply s (fun q v => q.1.2 v) l T (fun q => c q * lam q.1.1) hrel2
    rw [← h3]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := T)]
    · ring
    · intro v hv
      by_contra hvT
      rw [Function.mem_mulSupport, (hout v (by simpa using hvT)).2.1 q hq] at hv
      exact hv (hout v (by simpa using hvT)).1)
  exact ⟨Λ, fun f φ hφ => hΛ ⟨(f, φ), hφ⟩⟩

end GlobalTheory.FiniteAdelicPoints

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInstanceFramesOfDiagonalFrameSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem frames_of_diagonalising_frame : ∀ (D : D7) (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∃ fr : Formalism.IndefR.Eqv.UI.Frames D V, fr.Λ = Λ ∧ ∀ τ, fr.ε (Formalism.L2.Host.tauPl D τ) = A.ε τ ∧ fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹ := by
  intro D V A Λ h
  obtain ⟨hlat, hdual⟩ := h
  have hspan : Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) = ⊤ := by
    obtain ⟨s, hs⟩ := hlat.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hdual _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  have hf : ∀ v, IsUnit (A.fr ((Formalism.L2.Host.tauPl D).symm v)) := fun v => A.fr_unit _
  refine ⟨{ ε := fun v => A.ε ((Formalism.L2.Host.tauPl D).symm v)
            P := fun v => (A.fr ((Formalism.L2.Host.tauPl D).symm v))⁻¹
            unit := fun v => (Matrix.isUnit_nonsing_inv_iff).2 (hf v)
            spec := ?_
            Λ := Λ
            Λ_fg := hlat.fg
            Λ_span := hspan
            Λ_dual := ?_ }, rfl, fun τ => ?_⟩
  · intro v
    set τ := (Formalism.L2.Host.tauPl D).symm v
    have hg : V.gram.map (Formalism.IndefR.Eqv.UI.phiV D v) = (A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ := by
      rw [A.fr_gram τ]; rfl
    have hd : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hf v)
    have hdH : IsUnit ((A.fr τ)ᴴ).det := by
      rw [Matrix.det_conjTranspose]; exact hd.star
    rw [hg, Matrix.conjTranspose_nonsing_inv]
    calc ((A.fr τ)ᴴ)⁻¹ * ((A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ) * (A.fr τ)⁻¹
        = (((A.fr τ)ᴴ)⁻¹ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (A.ε τ) := by
          rw [Matrix.nonsing_inv_mul _ hdH, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]
  · intro x
    rw [hdual x]
    refine forall₂_congr fun y _ => ?_
    unfold Formalism.UG.hform
    simp only [RingHom.mem_range, starRingEnd_apply]
  · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowTowerMultiplicitySpacesOfArrow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepRows

theorem rowTower_of_step : RowModels → RowStep → RowTower := by
  intro hmod hstep D q hs T L μ0 hL sc hc G W M hM M₀ h₀ n
  induction n with
  | zero =>
    intro h
    refine ⟨parB (Ptw D) 0, M₀, (parRow_zero D sc.cGap).symm, h₀, fun _ w => w, fun t ht Φ => ⟨t, ht, fun ρ w => ⟨trivial, rfl⟩⟩⟩
  | succ n ih =>
    intro h
    obtain ⟨S, MA, hS, hA, vec, hvec⟩ := ih (Nat.le_of_succ_le h)
    obtain ⟨MB, hB⟩ := hmod D q hs T L μ0 hL sc hc G W M hM (n + 1) h
    obtain ⟨It, hIt⟩ := hstep D q hs T L μ0 hL sc hc G W M hM n h S _ MA MB hS rfl hA hB
    refine ⟨_, MB, rfl, hB, fun ρ w => It (ρ ⟨n, h⟩) (vec ρ w), fun t ht Φ => ?_⟩
    obtain ⟨F, hF, hF'⟩ := hvec t ht Φ
    obtain ⟨F', hF1, hF2⟩ := hIt F hF (Φ ⟨n, h⟩)
    refine ⟨F', hF1, fun ρ w => ?_⟩
    obtain ⟨h1, h2⟩ := hF' ρ w
    obtain ⟨h3, h4⟩ := hF2 (ρ ⟨n, h⟩) (vec ρ w)
    rw [← h2] at h3 h4
    exact ⟨⟨h1, h3⟩, h4⟩

end GlobalTheory.SepRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkMapCuspFormsExtendsToSmoothVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
  MeasureTheory NumberField Matrix

namespace GlobalTheory.GKExtensionToSmoothVectors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gkExtension :
    GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.GKExtension D :=
  fun h₁ h₂ D => ⟨_root_.GlobalTheory.GKExt.extExists h₁ h₂ D, GlobalTheory.KFiniteDetermined.restrInj D⟩

end GlobalTheory.GKExtensionToSmoothVectors
end

