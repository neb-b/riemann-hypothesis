module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0002
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffEqZeroOfSumTraceProjectionsInequivalentIrre
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.TraceSep

theorem exists_smul_eq_ite {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, IsSimpleModule R (M i)]
    (h : ∀ i j, i ≠ j → ∀ f : M i →ₗ[R] M j, f = 0) (i₀ : ι) (s : ∀ i, Finset (M i)) :
    ∃ r : R, ∀ i, ∀ m ∈ s i, r • m = if i = i₀ then m else 0 := by
  first
  | exact @_root_.GlobalTheory.OrthogonalProjectionOnto.main
  | exact _root_.GlobalTheory.OrthogonalProjectionOnto.main
  | (apply _root_.GlobalTheory.OrthogonalProjectionOnto.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthogonalProjectionOnto.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthogonalProjectionOnto.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthogonalProjectionOnto.main ..)

end GlobalTheory.TraceSep

namespace GlobalTheory.TraceSep

theorem hasFinTrace_compress {V : Type} [AddCommGroup V] [Module ℂ V] (P : V →ₗ[ℂ] V) (hP : P ∘ₗ P = P)
    [FiniteDimensional ℂ (LinearMap.range P)] (A : V →ₗ[ℂ] V) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (P ∘ₗ A ∘ₗ P)
      (LinearMap.trace ℂ (LinearMap.range P) (P.rangeRestrict ∘ₗ A ∘ₗ (LinearMap.range P).subtype)) := by
  have hfix : ∀ u ∈ LinearMap.range P, P u = u := by
    rintro u ⟨w, rfl⟩; exact LinearMap.congr_fun hP w
  have hBU : LinearMap.range (P ∘ₗ A ∘ₗ P) ≤ LinearMap.range P := LinearMap.range_comp_le_range _ _
  haveI : FiniteDimensional ℂ (LinearMap.range (P ∘ₗ A ∘ₗ P)) := Submodule.finiteDimensional_of_le hBU
  refine ⟨inferInstance, ?_⟩
  have hQ : ∀ u, (P.rangeRestrict ∘ₗ A ∘ₗ (LinearMap.range P).subtype) u ∈
      (LinearMap.range (P ∘ₗ A ∘ₗ P)).comap (LinearMap.range P).subtype := by
    intro u
    refine ⟨u, ?_⟩
    simp [hfix u u.2]
  rw [← LinearMap.trace_restrict_eq_of_forall_mem _ _ hQ,
    ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hBU)]
  congr 1
  ext ⟨x, hx⟩
  simp [LinearEquiv.conj_apply, Submodule.comapSubtypeEquivOfLe, hfix x (hBU hx)]

theorem coeff_eq_zero_of_sum_trace_eq_zero : ∀ (G : Type) [Group G] (n : ℕ) (W : Fin n → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (σ : ∀ i, Representation ℂ G (W i)), (∀ i, (σ i).IsIrreducible) → (∀ i j, i ≠ j → IsEmpty ((σ i).Equiv (σ j))) → ∀ (P : ∀ i, W i →ₗ[ℂ] W i), (∀ i, P i ∘ₗ P i = P i) → (∀ i, FiniteDimensional ℂ (LinearMap.range (P i))) → ∀ a : Fin n → ℂ, (∀ (g : G) (c : Fin n → ℂ), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (P i ∘ₗ σ i g ∘ₗ P i) (c i)) → ∑ i, a i * c i = 0) → ∀ i, P i ≠ 0 → a i = 0 := by
  intro G _ n W _ _ σ hirr hne P hP hfin a hsum i₀ hi₀
  let Q : ∀ i, MonoidAlgebra ℂ G → Module.End ℂ (LinearMap.range (P i)) := fun i y =>
    (P i).rangeRestrict ∘ₗ (σ i).asAlgebraHom y ∘ₗ (LinearMap.range (P i)).subtype
  have hlin : ∀ y, ∑ i, a i * LinearMap.trace ℂ _ (Q i y) = 0 := by
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of g =>
      refine hsum g _ fun i => ?_
      have := hasFinTrace_compress (P i) (hP i) (σ i g)
      simpa [Q, Representation.asAlgebraHom_of] using this
    | add x y hx hy =>
      simp only [Q, map_add (f := _), LinearMap.add_comp, LinearMap.comp_add, mul_add,
        Finset.sum_add_distrib] at hx hy ⊢
      rw [hx, hy, add_zero]
    | smul c x hx =>
      simp only [Q, map_smul, LinearMap.smul_comp, LinearMap.comp_smul, smul_eq_mul] at hx ⊢
      rw [Finset.sum_congr rfl fun i _ => mul_left_comm (a i) c _, ← Finset.mul_sum, hx, mul_zero]
  haveI : ∀ i, IsSimpleModule (MonoidAlgebra ℂ G) (σ i).asModule := fun i =>
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp (hirr i)
  have hzero : ∀ i j, i ≠ j → ∀ f : (σ i).asModule →ₗ[MonoidAlgebra ℂ G] (σ j).asModule, f = 0 := by
    intro i j hij f
    haveI := hirr i
    haveI := hirr j
    haveI := hne i j hij
    haveI := (Representation.IntertwiningMap.equivLinearMapAsModule (σ i) (σ j)).toEquiv.symm.subsingleton
    exact Subsingleton.elim _ _
  let b : ∀ i, Module.Basis (Fin (Module.finrank ℂ (LinearMap.range (P i)))) ℂ (LinearMap.range (P i)) :=
    fun i => Module.finBasis ℂ _
  obtain ⟨x, hx⟩ := exists_smul_eq_ite (R := MonoidAlgebra ℂ G) (fun i => (σ i).asModule) hzero i₀
    (fun i => Finset.univ.image fun k => (((b i k : LinearMap.range (P i)) : W i) : (σ i).asModule))
  have hQx : ∀ i, Q i x = if i = i₀ then LinearMap.id else 0 := by
    intro i
    refine (b i).ext fun k => ?_
    have h1 := hx i _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    change (σ i).asAlgebraHom x (b i k : W i) = _ at h1
    have hfix : P i (b i k : W i) = b i k := by
      obtain ⟨w, hw⟩ := (b i k).2
      rw [← hw]; exact LinearMap.congr_fun (hP i) w
    apply Subtype.ext
    by_cases hi : i = i₀
    · subst hi
      have h1' : (σ i).asAlgebraHom x (b i k : W i) = b i k := by simpa using h1
      simp [Q, h1', hfix]
    · have h1' : (σ i).asAlgebraHom x (b i k : W i) = 0 :=
        h1.trans (if_neg hi)
      simp [Q, h1', hi]
  have h := hlin x
  rw [Finset.sum_eq_single i₀ (fun i _ hi => by rw [hQx i, if_neg hi, map_zero, mul_zero])
    (by simp)] at h
  rw [hQx i₀, if_pos rfl, LinearMap.trace_id] at h
  have hpos : 0 < Module.finrank ℂ (LinearMap.range (P i₀)) := by
    rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot, Ne, LinearMap.range_eq_bot]
    exact hi₀
  have hne0 : (Module.finrank ℂ (LinearMap.range (P i₀)) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  exact (mul_eq_zero.1 h).resolve_right hne0

end GlobalTheory.TraceSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommuteOfWittFrameWeights
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Polynomial

namespace GlobalTheory.Cusp.WeightCommute

open Matrix

variable {D : D7} {V : HSp D}

theorem ratAct_mul' (a b : GF V) (v : V.V) :
    GlobalTheory.Cusp.ratAct D.sp.cm V (a * b) v = GlobalTheory.Cusp.ratAct D.sp.cm V a (GlobalTheory.Cusp.ratAct D.sp.cm V b v) := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (a * b).1.1 = a.1.1 * b.1.1 from rfl, Matrix.toLin_mul V.frame V.frame V.frame]
  rfl

theorem ratAct_one' (v : V.V) : GlobalTheory.Cusp.ratAct D.sp.cm V 1 v = v := by
  simp only [GlobalTheory.Cusp.ratAct]
  rw [show (1 : GF V).1.1 = 1 from rfl, Matrix.toLin_one]
  rfl

theorem hT_ratAct (γ : GF V) (a b : V.V) :
    V.hT (GlobalTheory.Cusp.ratAct D.sp.cm V γ a) (GlobalTheory.Cusp.ratAct D.sp.cm V γ b) = V.hT a b := by
  have hγ : Formalism.UG.cT (↑D.sp.cm.sig) γ.1.1 * V.gram * γ.1.1 = V.gram := γ.2
  have hc : Formalism.UG.cT (↑D.sp.cm.sig) γ.1.1 = Matrix.conjTranspose γ.1.1 := by
    ext i j; rfl
  rw [hc] at hγ
  have hr : ∀ w, V.frame.repr (GlobalTheory.Cusp.ratAct D.sp.cm V γ w) = γ.1.1 *ᵥ V.frame.repr w := fun w => by
    rw [← LinearMap.toMatrix_mulVec_repr V.frame V.frame, GlobalTheory.Cusp.ratAct, LinearMap.toMatrix_toLin]
  have hform : ∀ x y : Fin V.rank → D.host.E,
      ∑ i, ∑ j, star (x i) * V.gram i j * y j = star x ⬝ᵥ (V.gram *ᵥ y) := by
    intro x y
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord, hr, hr, hform, hform, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hγ]

theorem hT_frame (Φ : WittFrame V) (i j : Fin (wittIndex V)) :
    V.hT (Φ.f j) (Φ.e i) = (if i = j then 1 else 0) ∧ V.hT (Φ.e j) (Φ.f i) = (if i = j then 1 else 0) ∧
    V.hT (Φ.e j) (Φ.e i) = 0 ∧ V.hT (Φ.f j) (Φ.f i) = 0 := by
  refine ⟨Φ.ef i j, ?_, Φ.ee i j, Φ.ff i j⟩
  rw [← V.herm.eq (Φ.f i) (Φ.e j)]
  have h : V.hT (Φ.f i) (Φ.e j) = if j = i then 1 else 0 := Φ.ef j i
  rw [h]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]

end GlobalTheory.Cusp.WeightCommute


open GlobalTheory.Cusp.WeightCommute in
theorem GlobalTheory.Cusp.WeightCommute.commute_of_weights : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (u : SV (wittIndex V)) (γ g : GF V) (t : D.host.E), (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ Φ.sub u) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ Φ.sub (-u)) → (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x ∈ Φ.sub u) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ x ∈ Φ.sub (-u)) → (∀ x ∈ Φ.sub u, GlobalTheory.Cusp.ratAct D.sp.cm V g x = t • x) → (∀ x ∈ Φ.sub (-u), GlobalTheory.Cusp.ratAct D.sp.cm V g x = t⁻¹ • x) → (∀ z, (∀ x ∈ Φ.sub u, V.hT x z = 0) → (∀ x ∈ Φ.sub (-u), V.hT x z = 0) → GlobalTheory.Cusp.ratAct D.sp.cm V g z = z) → g * γ = γ * g := by
  intro D V Φ u γ g t h1 h2 h3 h4 h5 h6 h7
  classical
  obtain ⟨xv, hxv⟩ : ∃ xv : Fin (wittIndex V) → V.V, ∀ i, xv i = if u i = 1 then Φ.e i else Φ.f i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨yv, hyv⟩ : ∃ yv : Fin (wittIndex V) → V.V, ∀ i, yv i = if u i = 1 then Φ.f i else Φ.e i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (wittIndex V)), ∀ i, i ∈ S ↔ u i ≠ 0 :=
    ⟨Finset.univ.filter (fun i => u i ≠ 0), fun i => by simp⟩
  have hsgn : ∀ s : SignType, s ≠ 0 → s = 1 ∨ s = -1 := by decide
  have hne : (-1 : SignType) ≠ 1 := by decide
  have hs : ∀ i ∈ S, u i = 1 ∨ u i = -1 := fun i hi => hsgn _ ((hS i).1 hi)
  have key := hT_frame Φ
  have neq : ∀ i j, u i = 1 → u j = -1 → i ≠ j := by
    rintro i j a b rfl; rw [a] at b; exact hne b.symm

  have mx : ∀ i ∈ S, xv i ∈ Φ.sub u := by
    intro i hi
    rw [WittFrame.sub]
    rcases hs i hi with a | a
    · rw [hxv, if_pos a]; exact Submodule.subset_span (Or.inl ⟨i, a, rfl⟩)
    · rw [hxv, if_neg (by rw [a]; exact hne)]; exact Submodule.subset_span (Or.inr ⟨i, a, rfl⟩)
  have my : ∀ i ∈ S, yv i ∈ Φ.sub (-u) := by
    intro i hi
    rw [WittFrame.sub]
    rcases hs i hi with a | a
    · rw [hyv, if_pos a]
      exact Submodule.subset_span (Or.inr ⟨i, show -(u i) = -1 by rw [a], rfl⟩)
    · rw [hyv, if_neg (by rw [a]; exact hne)]
      exact Submodule.subset_span (Or.inl ⟨i, show -(u i) = 1 by rw [a]; rfl, rfl⟩)

  have genX : ∀ z, (∀ i ∈ S, V.hT (xv i) z = 0) → ∀ w ∈ Φ.sub u, V.hT w z = 0 := by
    intro z hz w hw
    have hle : Φ.sub u ≤ LinearMap.ker (V.hT.flip z) := by
      rw [WittFrame.sub, Submodule.span_le]
      rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · have hiS : i ∈ S := (hS i).2 (by rw [show u i = 1 from hi]; decide)
        have := hz i hiS
        rw [hxv, if_pos (show u i = 1 from hi)] at this
        exact this
      · have hiS : i ∈ S := (hS i).2 (by rw [show u i = -1 from hi]; decide)
        have := hz i hiS
        rw [hxv, if_neg (by rw [show u i = -1 from hi]; exact hne)] at this
        exact this
    exact hle hw
  have genY : ∀ z, (∀ i ∈ S, V.hT (yv i) z = 0) → ∀ w ∈ Φ.sub (-u), V.hT w z = 0 := by
    intro z hz w hw
    have hle : Φ.sub (-u) ≤ LinearMap.ker (V.hT.flip z) := by
      rw [WittFrame.sub, Submodule.span_le]
      rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · have a : u i = -1 := neg_eq_iff_eq_neg.1 (show -(u i) = 1 from hi)
        have hiS : i ∈ S := (hS i).2 (by rw [a]; decide)
        have := hz i hiS
        rw [hyv, if_neg (by rw [a]; exact hne)] at this
        exact this
      · have a : u i = 1 := by
          have h' : -(u i) = -1 := hi
          simpa using h'
        have hiS : i ∈ S := (hS i).2 (by rw [a]; decide)
        have := hz i hiS
        rw [hyv, if_pos a] at this
        exact this
    exact hle hw

  have pxx : ∀ i ∈ S, ∀ j ∈ S, V.hT (xv j) (xv i) = 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hxv, a, b, if_true, if_neg hne]
    · exact (key i j).2.2.1
    · rw [(key i j).1, if_neg (neq i j a b)]
    · rw [(key i j).2.1, if_neg (neq j i b a).symm]
    · exact (key i j).2.2.2
  have pyy : ∀ i ∈ S, ∀ j ∈ S, V.hT (yv j) (yv i) = 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hyv, a, b, if_true, if_neg hne]
    · exact (key i j).2.2.2
    · rw [(key i j).2.1, if_neg (neq i j a b)]
    · rw [(key i j).1, if_neg (neq j i b a).symm]
    · exact (key i j).2.2.1
  have pyx : ∀ i ∈ S, ∀ j ∈ S, V.hT (yv j) (xv i) = if i = j then 1 else 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hxv, hyv, a, b, if_true, if_neg hne]
    · exact (key i j).1
    · rw [(key i j).2.2.1, if_neg (neq i j a b)]
    · rw [(key i j).2.2.2, if_neg (neq j i b a).symm]
    · exact (key i j).2.1
  have pxy : ∀ i ∈ S, ∀ j ∈ S, V.hT (xv j) (yv i) = if i = j then 1 else 0 := by
    intro i hi j hj
    rcases hs i hi with a | a <;> rcases hs j hj with b | b <;> simp only [hxv, hyv, a, b, if_true, if_neg hne]
    · exact (key i j).2.1
    · rw [(key i j).2.2.2, if_neg (neq i j a b)]
    · rw [(key i j).2.2.1, if_neg (neq j i b a).symm]
    · exact (key i j).1

  have decomp : ∀ v : V.V, ∃ x ∈ Φ.sub u, ∃ y ∈ Φ.sub (-u), ∃ z, (∀ w ∈ Φ.sub u, V.hT w z = 0) ∧
      (∀ w ∈ Φ.sub (-u), V.hT w z = 0) ∧ v = x + y + z := by
    intro v
    refine ⟨∑ i ∈ S, V.hT (yv i) v • xv i, Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (mx i hi)),
      ∑ i ∈ S, V.hT (xv i) v • yv i, Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (my i hi)),
      v - (∑ i ∈ S, V.hT (yv i) v • xv i) - ∑ i ∈ S, V.hT (xv i) v • yv i, genX _ ?_, genY _ ?_, by abel⟩
    · intro j hj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sub, map_sum, map_sum,
        Finset.sum_eq_zero (fun i hi => by rw [map_smul, pxx i hi j hj, smul_zero]),
        Finset.sum_eq_single j (fun i hi hij => by rw [map_smul, pxy i hi j hj, if_neg hij, smul_zero])
          (fun h => absurd hj h),
        map_smul, pxy j hj j hj, if_pos rfl, smul_eq_mul, mul_one]
      simp
    · intro j hj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sub, map_sum, map_sum,
        Finset.sum_eq_single j (fun i hi hij => by rw [map_smul, pyx i hi j hj, if_neg hij, smul_zero])
          (fun h => absurd hj h),
        Finset.sum_eq_zero (fun i hi => by rw [map_smul, pyy i hi j hj, smul_zero]),
        map_smul, pyx j hj j hj, if_pos rfl, smul_eq_mul, mul_one]
      simp

  have inv_app : ∀ w, GlobalTheory.Cusp.ratAct D.sp.cm V γ (GlobalTheory.Cusp.ratAct D.sp.cm V γ⁻¹ w) = w := by
    intro w; rw [← ratAct_mul', mul_inv_cancel, ratAct_one']
  have zX : ∀ z, (∀ w ∈ Φ.sub u, V.hT w z = 0) →
      ∀ w ∈ Φ.sub u, V.hT w (GlobalTheory.Cusp.ratAct D.sp.cm V γ z) = 0 := by
    intro z hz w hw
    rw [← inv_app w, hT_ratAct]; exact hz _ (h3 w hw)
  have zY : ∀ z, (∀ w ∈ Φ.sub (-u), V.hT w z = 0) →
      ∀ w ∈ Φ.sub (-u), V.hT w (GlobalTheory.Cusp.ratAct D.sp.cm V γ z) = 0 := by
    intro z hz w hw
    rw [← inv_app w, hT_ratAct]; exact hz _ (h4 w hw)
  have hmat : (g * γ).1.1 = (γ * g).1.1 := by
    apply (Matrix.toLin V.frame V.frame).injective
    apply LinearMap.ext
    intro v
    show GlobalTheory.Cusp.ratAct D.sp.cm V (g * γ) v = GlobalTheory.Cusp.ratAct D.sp.cm V (γ * g) v
    rw [ratAct_mul', ratAct_mul']
    obtain ⟨x, hx, y, hy, z, hzX, hzY, rfl⟩ := decomp v
    simp only [map_add (f := _)]
    rw [h5 _ (h1 x hx), h6 _ (h2 y hy), h7 _ (zX z hzX) (zY z hzY), h5 x hx, h6 y hy, h7 z hzX hzY,
      map_smul, map_smul]
  exact Subtype.ext (Units.ext hmat)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionFiniteAdelicPureTensorEqLocalConvolut
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
noncomputable section

namespace GlobalTheory.TrConv

variable {D : D7}

theorem finFn_eq_tensorFin (V : HSp D) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) (y : GfC V) :
    finFn V ff y = tensorFin D.sp.cm.sig V.gram ff ((finPtsEquiv D.sp.cm.sig V.gram).symm y) := by
  unfold finFn tensorFin
  refine finprod_congr fun v => congrArg (ff v) ?_
  have := proj_ofFin D.sp.cm.sig V.gram v ((finPtsEquiv D.sp.cm.sig V.gram).symm y)
  rw [← this]
  congr 1
  exact (congrArg Subtype.val ((finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply y)).symm

theorem conv_finFn : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ a b, IsFinFamily D.sp.cm.sig V.gram (frameLat V) a → IsFinFamily D.sp.cm.sig V.gram (frameLat V) b → IsFinFamily D.sp.cm.sig V.gram (frameLat V) (fun v => conv (μf v) (a v) (b v)) ∧ finFn V (fun v => conv (μf v) (a v) (b v)) = conv ν (finFn V a) (finFn V b) ∧ finFn V a ∈ GlobalTheory.SplitWeil.SB (GfC V) := by
  intro D V μf _ h1 ν hν a b ha hb
  refine ⟨GlobalTheory.Orb.IsFinFamily.conv ha hb h1, funext fun y => ?_, ?_⟩
  · have hfam := GlobalTheory.Orb.IsFinFamily.mul_translate ha hb (y : GA D V)
    have hint : (fun x : GfC V => finFn V a x * finFn V b (x⁻¹ * y)) =
        finFn V (fun v x => a v x * b v (x⁻¹ * proj D.sp.cm.sig V.gram v (y : GA D V))) := by
      funext x
      have e1 := ha.finite_mulSupport ((finPtsEquiv D.sp.cm.sig V.gram).symm x)
      have e2 := hb.finite_mulSupport ((finPtsEquiv D.sp.cm.sig V.gram).symm (x⁻¹ * y))
      rw [finFn_eq_tensorFin, finFn_eq_tensorFin]
      unfold finFn
      unfold tensorFin
      rw [← finprod_mul_distrib e1 e2]
      refine finprod_congr fun v => ?_
      have p1 := proj_ofFin D.sp.cm.sig V.gram v ((finPtsEquiv D.sp.cm.sig V.gram).symm x)
      have p2 := proj_ofFin D.sp.cm.sig V.gram v ((finPtsEquiv D.sp.cm.sig V.gram).symm (x⁻¹ * y))
      have q1 : ofFin D.sp.cm.sig V.gram ((finPtsEquiv D.sp.cm.sig V.gram).symm x) = (x : GA D V) :=
        congrArg Subtype.val ((finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply x)
      have q2 : ofFin D.sp.cm.sig V.gram ((finPtsEquiv D.sp.cm.sig V.gram).symm (x⁻¹ * y)) = ((x⁻¹ * y : GfC V) : GA D V) :=
        congrArg Subtype.val ((finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply _)
      rw [q1] at p1
      rw [q2] at p2
      rw [← p1, ← p2]
      simp [map_mul, map_inv]
    symm
    show ∫ x, finFn V a x * finFn V b (x⁻¹ * y) ∂ν = _
    rw [hint, hν.2 _ hfam]
    rfl
  · have hm := ha.tensorFin_mem
    rw [show finFn V a = tensorFin D.sp.cm.sig V.gram a ∘ (finPtsEquiv D.sp.cm.sig V.gram).symm from
      funext fun y => finFn_eq_tensorFin V a y]
    exact ⟨hm.1.comp_continuous (finPtsEquiv D.sp.cm.sig V.gram).symm.continuous,
      hm.2.comp_homeomorph (finPtsEquiv D.sp.cm.sig V.gram).symm.toHomeomorph⟩

end GlobalTheory.TrConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspDiscreteDecompositionOfDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CuspHS

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.Orb

variable {D : D7} {V : HSp D} {μ : Measure (GA D V)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem norm_convR_le (hP : GlobalTheory.Published.CuspDecayBound) {f : GA D V → ℂ} (hf : f ∈ CcGA V) :
    ∃ K : ℝ, ∀ F : DividedPowerChartLift V μ, F ∈ L2cusp V μ → ∀ g, ‖convR μ f (lift (GQ V) F) g‖ ≤ K * ‖F‖ := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hfc := continuous_of_mem_ccAd hf
  have hder : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∃ f' ∈ CcGA V, tsupport f' ⊆ tsupport f ∧ ∀ F : DividedPowerChartLift V μ,
        l.foldr (fun p φ => Rder θ V p.1 p.2 φ) (convR μ f (lift (GQ V) F)) = convR μ f' (lift (GQ V) F) := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨f, hf, subset_rfl, fun F => rfl⟩
    | cons p l ih =>
      intro hl
      obtain ⟨f₁, h₁, s₁, e₁⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
      obtain ⟨f₂, h₂, s₂, e₂⟩ := _root_.GlobalTheory.ConvRDeriv.Rder_convR μ θ hθ h₁ (hl p List.mem_cons_self)
      exact ⟨f₂, h₂, s₂.trans s₁, fun F => by simp only [List.foldr_cons, e₁ F, e₂ F]⟩
  choose! fl hfl hsl hel using hder
  have hM : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∃ M : ℝ, ∀ y, ‖fl l y‖ ≤ M := fun l hl =>
    have c := continuous_of_mem_ccAd (hfl l hl)
    c.1.bounded_above_of_compact_support c.2
  choose! M hM using hM
  obtain ⟨A, Cg, hg⟩ := _root_.GlobalTheory.ConvGrowth.norm_convR_le_height μ hfc.2.isCompact (_root_.GlobalTheory.RatCount.ncard_rat_mem_translate_le hfc.2.isCompact)
  obtain ⟨U, hU, hlev⟩ := _root_.GlobalTheory.ConvLevel.convR_level μ hf
  obtain ⟨L, C, hL, hB⟩ := hP D θ hθ V U hU A 0
  refine ⟨C * ∑ l ∈ L, Cg * M l, fun F hF g => ?_⟩
  have hgr : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → ∀ x,
      ‖(l.foldr (fun p φ => Rder θ V p.1 p.2 φ) (convR μ f (lift (GQ V) F))) x‖ ≤
        Cg * M l * ‖F‖ * GlobalTheory.Grow.height V x ^ A := fun l hl x => by
    rw [hel l hl F]
    exact hg _ (continuous_of_mem_ccAd (hfl l hl)).1 (hsl l hl) _ (hM l hl) F x
  have hcont := (GlobalTheory.AutomorphicL2Local.continuous_convR_lift _ (GQ V) μ f hfc.1 hfc.2 F).2
  have key := hB (convR μ f (lift (GQ V) F))
    ⟨fun γ hγ x => ((leftInv_lift (Γ := GQ V) F).convR (μ := μ) f) γ hγ x, ⟨U, hU, hlev F⟩, hcont⟩
    (hlev F) (_root_.GlobalTheory.ConvSmooth.contDiff_convR_lift_oneP μ θ hθ hf F) (fun l hl => ⟨_, hgr l hl⟩) (_root_.GlobalTheory.CuspConv.isCuspFun_convR_lift μ hf F hF)
    (fun l => Cg * M l * ‖F‖) (fun l hl x => hgr l (hL l hl) x) g
  rw [pow_zero, mul_one, ← Finset.sum_mul, ← mul_assoc] at key
  exact key

theorem isHilbertSchmidt_RcuspOp (hP : GlobalTheory.Published.CuspDecayBound) {f : GA D V → ℂ} (hf : f ∈ CcGA V) :
    IsHilbertSchmidt (RcuspOp V μ f) := by
  obtain ⟨K, hK⟩ := norm_convR_le (μ := μ) hP hf
  have hfc := continuous_of_mem_ccAd hf
  have hi : Integrable f μ := hfc.1.integrable_of_hasCompactSupport hfc.2
  have h1 : IsHilbertSchmidt ((L2cusp V μ).subtypeL ∘L RcuspOp V μ f) := by
    refine _root_.GlobalTheory.isHilbertSchmidt_of_ae_bounded _ K fun v => ?_
    have e : ((L2cusp V μ).subtypeL ∘L RcuspOp V μ f) v = RopG V μ f v := coe_RcuspOp V μ hi v
    rw [e]
    refine ae_quotMeasure_iff.2 ?_
    filter_upwards [(GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR _ (GQ V) μ f hi v).2] with x hx
    have hx' : (RopG V μ f v) (mk (GQ V) x) = convR μ f (lift (GQ V) (v : DividedPowerChartLift V μ)) x := hx
    rw [hx']
    simpa using hK v v.2 x
  exact h1.of_norm_le 1 fun x => by simp

end GlobalTheory.CuspHS

namespace GlobalTheory.Published

theorem cuspTraceClass_of_decay (hP : CuspDecayBound) (hDM : DixmierMalliavinFactorisation) : CuspTraceClass :=
  fun _ _ _ _ _ _ hf => CuspSpectrum.isTraceClass_of_isHilbertSchmidt hDM
    (fun _ hg => CuspHS.isHilbertSchmidt_RcuspOp hP hg) hf

end GlobalTheory.Published

end
end

