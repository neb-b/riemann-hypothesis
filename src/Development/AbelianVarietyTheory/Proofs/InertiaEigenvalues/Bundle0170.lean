module

public import Mathlib
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0164
public import Formalism.CharacterColumnKernels.StatementRho
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0169
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
section
noncomputable section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC

namespace GlobalTheory.FunctorialityH2

section Functor

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
variable {M'' : Type*} [AddCommGroup M''] [Module R M''] [TopologicalSpace M'']
  [IsTopologicalAddGroup M''] [ContinuousConstSMul R M'']
variable (rho : Representation R G M) (rho' : Representation R G M')
  (rho'' : Representation R G M'')

theorem map_H2_congr {u v : M →ₗ[R] M'} (huv : u = v) (hu : Continuous u)
    (hue : ∀ g m, u (rho g m) = rho' g (u m)) (hv : Continuous v)
    (hve : ∀ g m, v (rho g m) = rho' g (v m)) :
    mapH2 rho rho' u hu hue = mapH2 rho rho' v hv hve := by
  subst huv; rfl

theorem map_H2_id :
    mapH2 rho rho LinearMap.id continuous_id (fun _ _ => rfl) = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
  rfl

theorem map_H2_comp (u : M →ₗ[R] M') (hu : Continuous u)
    (hue : ∀ g m, u (rho g m) = rho' g (u m)) (v : M' →ₗ[R] M'') (hv : Continuous v)
    (hve : ∀ g m, v (rho' g m) = rho'' g (v m)) (hvu : Continuous (v ∘ₗ u))
    (hvue : ∀ g m, (v ∘ₗ u) (rho g m) = rho'' g ((v ∘ₗ u) m)) :
    mapH2 rho rho'' (v ∘ₗ u) hvu hvue =
      mapH2 rho' rho'' v hv hve ∘ₗ mapH2 rho rho' u hu hue := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
  rfl

theorem map_H2_zero (h0 : Continuous (0 : M →ₗ[R] M'))
    (h0e : ∀ g m, (0 : M →ₗ[R] M') (rho g m) = rho' g ((0 : M →ₗ[R] M') m)) :
    mapH2 rho rho' 0 h0 h0e = 0 := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
  rfl

theorem map_H2_add (u v : M →ₗ[R] M') (hu : Continuous u)
    (hue : ∀ g m, u (rho g m) = rho' g (u m)) (hv : Continuous v)
    (hve : ∀ g m, v (rho g m) = rho' g (v m)) (huv : Continuous (u + v))
    (huve : ∀ g m, (u + v) (rho g m) = rho' g ((u + v) m)) :
    mapH2 rho rho' (u + v) huv huve = mapH2 rho rho' u hu hue + mapH2 rho rho' v hv hve := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
  rfl

theorem map_H2_smul (c : R) (u : M →ₗ[R] M') (hu : Continuous u)
    (hue : ∀ g m, u (rho g m) = rho' g (u m)) (hcu : Continuous (c • u))
    (hcue : ∀ g m, (c • u) (rho g m) = rho' g ((c • u) m)) :
    mapH2 rho rho' (c • u) hcu hcue = c • mapH2 rho rho' u hu hue := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun f => ?_)
  rfl

theorem map_H2_sum {ι : Type*} (s : Finset ι) (u : ι → M →ₗ[R] M') (hu : ∀ j, Continuous (u j))
    (hue : ∀ j g m, u j (rho g m) = rho' g (u j m))
    (hs : Continuous ((∑ j ∈ s, u j : M →ₗ[R] M') : M → M'))
    (hse : ∀ g m, (∑ j ∈ s, u j) (rho g m) = rho' g ((∑ j ∈ s, u j) m)) :
    mapH2 rho rho' (∑ j ∈ s, u j) hs hse = ∑ j ∈ s, mapH2 rho rho' (u j) (hu j) (hue j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact map_H2_zero rho rho' _ _
  | insert a s ha ih =>
    have hc : Continuous ((∑ j ∈ s, u j : M →ₗ[R] M') : M → M') := by
      have := continuous_finsetSum s (fun j _ => hu j)
      convert this using 1; ext x; simp
    have he : ∀ g m, (∑ j ∈ s, u j) (rho g m) = rho' g ((∑ j ∈ s, u j) m) := by
      intro g m; simp only [LinearMap.sum_apply, map_sum, hue]
    rw [map_H2_congr rho rho' (Finset.sum_insert ha) hs hse
        ((hu a).add hc) (fun g m => by simp only [LinearMap.add_apply, hue, he, map_add (f := _)]),
      map_H2_add rho rho' _ _ (hu a) (hue a) hc he, ih hc he, Finset.sum_insert ha]

end Functor

section Phi

variable {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ)

theorem cont_span (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [ContinuousSMul O M] (m : M) : Continuous (LinearMap.toSpanSingleton O M m) :=
  continuous_id.smul continuous_const

theorem span_twist (M : Type) [AddCommGroup M] [Module O M] (m : M) (g : G) (a : O) :
    LinearMap.toSpanSingleton O M m (twist ε O g a) =
      twist ε M g (LinearMap.toSpanSingleton O M m a) := by
  show ((ε g : O) • a) • m = (ε g : O) • (a • m)
  rw [smul_assoc]

variable (z : H2 (twist ε O))

def phi (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul O M] [ContinuousSMul O M] : M →ₗ[O] H2 (twist ε M) where
  toFun m := mapH2 (twist ε O) (twist ε M) (LinearMap.toSpanSingleton O M m) (cont_span M m)
    (span_twist ε M m) z
  map_add' m m' := by
    rw [map_H2_congr (twist ε O) (twist ε M) (LinearMap.ext fun a => by simp [smul_add] :
        LinearMap.toSpanSingleton O M (m + m') =
          LinearMap.toSpanSingleton O M m + LinearMap.toSpanSingleton O M m')
      (cont_span M _) (span_twist ε M _) ((cont_span M m).add (cont_span M m'))
      (fun g a => by simp only [LinearMap.add_apply, span_twist, map_add (f := _)]),
      map_H2_add _ _ _ _ (cont_span M m) (span_twist ε M m) (cont_span M m') (span_twist ε M m')]
    rfl
  map_smul' c m := by
    rw [map_H2_congr (twist ε O) (twist ε M) (LinearMap.ext fun a => by simp [smul_comm a c m] :
        LinearMap.toSpanSingleton O M (c • m) = c • LinearMap.toSpanSingleton O M m)
      (cont_span M _) (span_twist ε M _) ((cont_span M m).const_smul c)
      (fun g a => by simp only [LinearMap.smul_apply, span_twist, map_smul]),
      map_H2_smul _ _ c _ (cont_span M m) (span_twist ε M m)]
    rfl

theorem phi_apply (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [ContinuousSMul O M] (m : M) :
    phi ε z M m = mapH2 (twist ε O) (twist ε M) (LinearMap.toSpanSingleton O M m)
      (cont_span M m) (span_twist ε M m) z := rfl

theorem phi_natural (M M' : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [ContinuousSMul O M]
    [AddCommGroup M'] [Module O M'] [TopologicalSpace M']
    [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [ContinuousSMul O M']
    (f : M →ₗ[O] M') (hf : Continuous f) (hfe : ∀ g m, f (twist ε M g m) = twist ε M' g (f m))
    (m : M) : mapH2 (twist ε M) (twist ε M') f hf hfe (phi ε z M m) = phi ε z M' (f m) := by
  rw [phi_apply, phi_apply, ← LinearMap.comp_apply,
    ← map_H2_comp (twist ε O) (twist ε M) (twist ε M') _ (cont_span M m) (span_twist ε M m) f hf hfe
      (hf.comp (cont_span M m)) (fun g a => by simp only [LinearMap.comp_apply, span_twist, hfe])]
  exact congrArg (fun L : H2 (twist ε O) →ₗ[O] H2 (twist ε M') => L z)
    (map_H2_congr _ _ (LinearMap.ext fun a => by simp) _ _ _ _)

theorem phi_self (a : O) : phi ε z O a = a • z := by
  rw [phi_apply, map_H2_congr (twist ε O) (twist ε O)
    (show LinearMap.toSpanSingleton O O a = a • LinearMap.id from
      LinearMap.ext fun b => by simp [mul_comm])
    _ _ (continuous_id.const_smul a) (fun g b => by
      show a * ((ε g : O) * b) = (ε g : O) * (a * b); ring),
    map_H2_smul _ _ a _ continuous_id (fun _ _ => rfl), map_H2_id]
  rfl

end Phi

section Retract

variable {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ) (z : H2 (twist ε O))

theorem twist_equiv {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (f : M →ₗ[O] M') (g : G) (m : M) : f (twist ε M g m) = twist ε M' g (f m) := by
  show f ((ε g : O) • m) = (ε g : O) • f m
  exact map_smul f _ m

theorem cont_sum {ι M M' : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [AddCommGroup M'] [Module O M'] [TopologicalSpace M'] [IsTopologicalAddGroup M']
    (s : Finset ι) (u : ι → M →ₗ[O] M') (hu : ∀ j, Continuous (u j)) :
    Continuous ((∑ j ∈ s, u j : M →ₗ[O] M') : M → M') := by
  have h := continuous_finsetSum s (fun j _ => hu j)
  convert h using 1 <;> ext x <;> simp only [LinearMap.sum_apply, Finset.sum_apply]

theorem bijective_of_retract (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [ContinuousSMul O M]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (N : ι → Type) [∀ j, AddCommGroup (N j)] [∀ j, Module O (N j)] [∀ j, TopologicalSpace (N j)]
    [∀ j, IsTopologicalAddGroup (N j)] [∀ j, ContinuousConstSMul O (N j)]
    [∀ j, ContinuousSMul O (N j)]
    (N' : κ → Type) [∀ i, AddCommGroup (N' i)] [∀ i, Module O (N' i)] [∀ i, TopologicalSpace (N' i)]
    [∀ i, IsTopologicalAddGroup (N' i)] [∀ i, ContinuousConstSMul O (N' i)]
    [∀ i, ContinuousSMul O (N' i)]
    (p : ∀ j, M →ₗ[O] N j) (s : ∀ j, N j →ₗ[O] M) (p' : ∀ i, M →ₗ[O] N' i)
    (s' : ∀ i, N' i →ₗ[O] M) (hp : ∀ j, Continuous (p j)) (hs : ∀ j, Continuous (s j))
    (hp' : ∀ i, Continuous (p' i)) (hs' : ∀ i, Continuous (s' i))
    (hid : ∀ m, ∑ j, s j (p j m) + ∑ i, s' i (p' i m) = m)
    (hN : ∀ j, Function.Bijective (phi ε z (N j)))
    (hN' : ∀ i, Function.Bijective (phi ε z (N' i))) :
    Function.Bijective (phi ε z M) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro m hm
    have h1 : ∀ j, p j m = 0 := fun j => (injective_iff_map_eq_zero _).1 (hN j).1 _ (by
      rw [← phi_natural ε z M (N j) (p j) (hp j) (twist_equiv ε (p j)), hm, map_zero])
    have h2 : ∀ i, p' i m = 0 := fun i => (injective_iff_map_eq_zero _).1 (hN' i).1 _ (by
      rw [← phi_natural ε z M (N' i) (p' i) (hp' i) (twist_equiv ε (p' i)), hm, map_zero])
    rw [← hid m]
    simp [h1, h2]
  · intro w
    choose n hn using fun j =>
      (hN j).2 (mapH2 (twist ε M) (twist ε (N j)) (p j) (hp j) (twist_equiv ε (p j)) w)
    choose n' hn' using fun i =>
      (hN' i).2 (mapH2 (twist ε M) (twist ε (N' i)) (p' i) (hp' i) (twist_equiv ε (p' i)) w)
    refine ⟨∑ j, s j (n j) + ∑ i, s' i (n' i), ?_⟩
    have k1 : ∀ j, phi ε z M (s j (n j)) = mapH2 (twist ε M) (twist ε M) (s j ∘ₗ p j)
        ((hs j).comp (hp j)) (twist_equiv ε _) w := by
      intro j
      rw [← phi_natural ε z (N j) M (s j) (hs j) (twist_equiv ε (s j)), hn j,
        map_H2_comp (twist ε M) (twist ε (N j)) (twist ε M) (p j) (hp j) (twist_equiv ε _) (s j)
          (hs j) (twist_equiv ε _)]
      rfl
    have k2 : ∀ i, phi ε z M (s' i (n' i)) = mapH2 (twist ε M) (twist ε M) (s' i ∘ₗ p' i)
        ((hs' i).comp (hp' i)) (twist_equiv ε _) w := by
      intro i
      rw [← phi_natural ε z (N' i) M (s' i) (hs' i) (twist_equiv ε (s' i)), hn' i,
        map_H2_comp (twist ε M) (twist ε (N' i)) (twist ε M) (p' i) (hp' i) (twist_equiv ε _) (s' i)
          (hs' i) (twist_equiv ε _)]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, map_sum, Finset.sum_congr rfl (fun j _ => k1 j),
      Finset.sum_congr rfl (fun i _ => k2 i), ← LinearMap.sum_apply, ← LinearMap.sum_apply,
      ← map_H2_sum (twist ε M) (twist ε M) _ _ _ _ (cont_sum _ _ fun j => (hs j).comp (hp j))
        (twist_equiv ε _),
      ← map_H2_sum (twist ε M) (twist ε M) _ _ _ _ (cont_sum _ _ fun i => (hs' i).comp (hp' i))
        (twist_equiv ε _),
      ← LinearMap.add_apply,
      ← map_H2_add (twist ε M) (twist ε M) _ _ _ _ _ _
        ((cont_sum _ _ fun j => (hs j).comp (hp j)).add
          (cont_sum _ _ fun i => (hs' i).comp (hp' i))) (twist_equiv ε _),
      map_H2_congr (twist ε M) (twist ε M)
        (LinearMap.ext fun m => by simpa using hid m : (∑ j, s j ∘ₗ p j) + ∑ i, s' i ∘ₗ p' i =
          LinearMap.id) _ _ continuous_id (fun _ _ => rfl), map_H2_id]
    rfl

end Retract

end GlobalTheory.FunctorialityH2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2LevelRepOneLeStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_H2_level_rep_one_le : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → ∀ {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M)
    (h : ((p : O) ^ 1) ∈ Ideal.span {ϖ ^ 1}),
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p 1 h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p 1 h ρ) →
    Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p 1 h ρ)) ≤ Nat.card (IsLocalRing.ResidueField O) := by
  first | exact @GlobalTheory.ShapeNeg.card_H2_level_rep_le | exact GlobalTheory.ShapeNeg.card_H2_level_rep_le | (intros; apply GlobalTheory.ShapeNeg.card_H2_level_rep_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple
section
noncomputable section

namespace GlobalTheory.TraceConj

variable {Γ k : Type} [Group Γ] [Field k] {a : ℕ}

def colRep (ρ : Γ →* GL (Fin a) k) : Representation k Γ (Fin a → k) where
  toFun g := Matrix.toLin' ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)
  map_one' := by
    rw [map_one, Units.val_one, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl

theorem colRep_apply (ρ : Γ →* GL (Fin a) k) (g : Γ) :
    colRep ρ g = Matrix.toLin' ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) := rfl

theorem colRep_semisimple (ρ : Γ →* GL (Fin a) k) (h : Formalism.MainNotions.N.IsSSRep ρ) :
    (colRep ρ).IsSemisimpleRepresentation := by
  refine ⟨fun P => ?_⟩
  obtain ⟨W', h1, h2⟩ := h P.toSubmodule fun g v hv => P.apply_mem_toSubmodule g hv
  refine ⟨⟨W', fun g v hv => h1 g v hv⟩, ?_⟩
  rw [isCompl_iff, disjoint_iff, codisjoint_iff,
    ← Subrepresentation.toSubmodule_injective.eq_iff, ← Subrepresentation.toSubmodule_injective.eq_iff]
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at h2
  exact h2

theorem conj_of_trace_eq : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (a : ℕ)
    (ρ ρ' : Γ →* GL (Fin a) k), Formalism.MainNotions.N.IsSSRep ρ → Formalism.MainNotions.N.IsSSRep ρ' →
    (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).trace =
      ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).trace) →
    ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹ := by
  intro Γ k _ _ _ a ρ ρ' hρ hρ' ht
  obtain ⟨e, he⟩ := GlobalTheory.TraceIso.exists_equiv_of_trace_eq (colRep ρ) (colRep ρ')
    (colRep_semisimple ρ hρ) (colRep_semisimple ρ' hρ') fun g => by
      rw [colRep_apply, colRep_apply, Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, ht]
  let h : GL (Fin a) k :=
    ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp,
      by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨h, fun g => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  have hh : Matrix.toLin' (h : Matrix (Fin a) (Fin a) k) = e.toLinearMap :=
    Matrix.toLin'_toMatrix' _
  rw [hh]
  exact LinearMap.ext fun v => (he g v).symm

end GlobalTheory.TraceConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompleteSpaceOfFinitePadicIntUnitBall
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CoeffComplete

open Filter Topology

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]

theorem norm_natCast_prime_eq : ‖(l : K)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] K) l, norm_algebraMap']
  exact Padic.norm_p

theorem natCast_smul_pow_eq (k : ℕ) (z : O) : ((l : ℤ_[l]) ^ k) • z = (l : O) ^ k * z := by
  rw [Algebra.smul_def, map_pow, map_natCast]

theorem norm_intCoord_le_one {ι : Type} [Fintype ι] (v : ι → ℤ_[l]) : ‖v‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => PadicInt.norm_le_one _

variable {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ_[l] O)

theorem coord_small_of_small (y : O) (k : ℕ) (h : ‖algebraMap O K y‖ ≤ ‖(l : K)‖ ^ k) :
    ‖b.equivFun y‖ ≤ ‖(l : ℤ_[l])‖ ^ k := by
  have hl : (l : K) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_natCast_prime_eq (l := l)]
    exact inv_ne_zero (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hw : ‖algebraMap O K y / (l : K) ^ k‖ ≤ 1 := by
    rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ h (by positivity)
  obtain ⟨z, hz⟩ := (IsUnitBall.mem_range_iff (O := O) _).2 hw
  have hy : y = (l : O) ^ k * z := by
    apply IsUnitBall.inj (K := K)
    rw [map_mul, hz, map_pow, map_natCast, mul_div_cancel₀ _ (pow_ne_zero _ hl)]
  rw [hy, ← natCast_smul_pow_eq, map_smul]
  calc ‖((l : ℤ_[l]) ^ k) • b.equivFun z‖ ≤ ‖(l : ℤ_[l]) ^ k‖ * ‖b.equivFun z‖ := norm_smul_le _ _
    _ ≤ ‖(l : ℤ_[l]) ^ k‖ * 1 := by gcongr; exact norm_intCoord_le_one _
    _ = ‖(l : ℤ_[l])‖ ^ k := by rw [mul_one, norm_pow]

theorem small_of_coord_small (y : O) (k : ℕ) (h : ‖b.equivFun y‖ ≤ ‖(l : ℤ_[l])‖ ^ k) :
    ‖algebraMap O K y‖ ≤ ‖(l : K)‖ ^ k := by
  have hd : ∀ i, ((l : ℤ_[l]) ^ k) ∣ b.equivFun y i := by
    intro i
    rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow]
    have := (pi_norm_le_iff_of_nonneg (by positivity)).1 h i
    rw [PadicInt.norm_p, inv_pow, ← zpow_natCast, ← zpow_neg] at this
    exact this
  choose e he using hd
  have hy : y = (l : O) ^ k * b.equivFun.symm e := by
    rw [← natCast_smul_pow_eq, ← map_smul, ← b.equivFun.symm_apply_apply y]
    congr 1
    funext i
    simp [he i]
  rw [hy, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (norm_algebraMap_le _)

theorem completeSpace_of_finite_unitBall : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K], CompleteSpace K := by
  intro l _ O K _ _ _ _ _ _ _ _ _
  let b := Module.Free.chooseBasis ℤ_[l] O
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hϖ0 : 0 < ‖(l : K)‖ := by rw [norm_natCast_prime_eq (l := l)]; positivity
  have hϖ1 : ‖(l : K)‖ < 1 := by
    rw [norm_natCast_prime_eq (l := l)]; exact inv_lt_one_of_one_lt₀ hl1
  have hπ0 : 0 < ‖(l : ℤ_[l])‖ := by rw [PadicInt.norm_p]; positivity
  have hπ1 : ‖(l : ℤ_[l])‖ < 1 := by rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ hl1
  refine Metric.complete_of_convergent_controlled_sequences (fun N => ‖(l : K)‖ ^ N)
    (fun n => pow_pos hϖ0 n) ?_
  intro u hu
  have h0 : ∀ n, ‖u n - u 0‖ ≤ 1 := fun n => by
    have := hu 0 n 0 (Nat.zero_le _) le_rfl
    rw [dist_eq_norm, pow_zero] at this
    exact this.le
  choose y hy using fun n => (IsUnitBall.mem_range_iff (O := O) _).2 (h0 n)
  have hc : CauchySeq (fun n => b.equivFun (y n)) := by
    refine cauchySeq_of_le_tendsto_0 (fun N => ‖(l : ℤ_[l])‖ ^ N) (fun n m N hn hm => ?_) ?_
    · rw [dist_eq_norm, ← map_sub]
      apply coord_small_of_small (K := K) b
      rw [map_sub, hy, hy, show u n - u 0 - (u m - u 0) = u n - u m by abel]
      have := hu N n m hn hm
      rw [dist_eq_norm] at this
      exact this.le
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one hπ0.le hπ1
  obtain ⟨γ, hγ⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨u 0 + algebraMap O K (b.equivFun.symm γ), ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hϖ1
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hγ _ (pow_pos hπ0 k)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have e : u n - (u 0 + algebraMap O K (b.equivFun.symm γ)) =
      algebraMap O K (y n - b.equivFun.symm γ) := by
    rw [map_sub, hy]; abel
  rw [e]
  refine lt_of_le_of_lt (small_of_coord_small b _ k ?_) hk
  rw [map_sub, LinearEquiv.apply_symm_apply]
  have := hN n hn
  rw [dist_eq_norm] at this
  exact this.le

end GlobalTheory.CoeffComplete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulIntegral
section
namespace GlobalTheory.IntegralPowerMultiple

theorem exists_pow_mul_integral {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) (c : FractionRing O) :
    ∃ (n : ℕ) (a : O), algebraMap O (FractionRing O) (ϖ ^ n) * c = algebraMap O (FractionRing O) a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb

  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨n, ((u⁻¹ : Oˣ) : O) * a, ?_⟩
  have hbK : algebraMap O (FractionRing O) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hu' : algebraMap O (FractionRing O) (u : O) * algebraMap O (FractionRing O) ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [hu, map_mul] at hbK
  rw [hu, map_mul, map_mul]
  rw [mul_div_assoc', div_eq_iff hbK]
  linear_combination (-(algebraMap O (FractionRing O) a * algebraMap O (FractionRing O) (ϖ ^ n))) * hu'

theorem exists_pow_smul_mem : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsDomain O] [IsDiscreteValuationRing O] {V : Type} [inst_3 : AddCommGroup V] [inst_4 : Module O V] [inst_5 : Module (FractionRing O) V] [inst_6 : IsScalarTower O (FractionRing O) V] (T : Submodule O V), Formalism.RepresentationBoundsCohomology.LOC.IsLatticeIn T → ∀ (ϖ : O), Irreducible ϖ → ∀ (v : V), ∃ (m : ℕ), ϖ ^ m • v ∈ T := by
  intro O _ _ _ V _ _ _ _ T hT ϖ hϖ v
  have hv : v ∈ Submodule.span (FractionRing O) (T : Set V) := by rw [hT.2]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m₁, h₁⟩ := hx
    obtain ⟨m₂, h₂⟩ := hy
    refine ⟨m₁ + m₂, ?_⟩
    rw [smul_add, pow_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact T.smul_mem _ h₁
    · rw [mul_smul]
      exact T.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨m, hm⟩ := hx

    obtain ⟨n, a, ha⟩ := exists_pow_mul_integral hϖ c
    refine ⟨n + m, ?_⟩
    have key : ϖ ^ (n + m) • (c • x) = a • (ϖ ^ m • x) := by
      rw [← algebraMap_smul (FractionRing O) (ϖ ^ (n + m)) (c • x), smul_smul,
        ← algebraMap_smul (FractionRing O) a, ← algebraMap_smul (FractionRing O) (ϖ ^ m) x, smul_smul,
        ← ha, pow_add, map_mul]
      congr 1
      ring
    rw [key]
    exact T.smul_mem a hm

end GlobalTheory.IntegralPowerMultiple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneOfFiniteImageStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_of_finite_image : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (G : Type) [Group G] [Finite G] (π : Weil h →* G), IsOpen {σ : Ine (F := E) A | π (ineIncl h σ) = 1} → ∀ (n : ℕ) (R : Representation ℂ G (Fin n → ℂ)) (μ : Weil h →* ℂˣ), IsSmooth μ → ∃ b : WDRep h (Fin n → ℂ), ∀ σ, b.ρ σ = (μ σ : ℂ) • R (π σ) := by
  first | exact @GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist | exact GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist | (intros; apply GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist <;> assumption)
end

