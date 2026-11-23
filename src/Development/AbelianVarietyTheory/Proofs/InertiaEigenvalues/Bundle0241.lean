module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0028
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanDOfFixed
section
noncomputable section

namespace GlobalTheory.DRFil

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)
    {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

private theorem mulR_mulR (a b : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    mulR ℚ_[l] P.R.BdR LL V a (mulR ℚ_[l] P.R.BdR LL V b x) = mulR ℚ_[l] P.R.BdR LL V (a * b) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v c => simp [mul_assoc]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

private theorem mulR_neg (a : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    mulR ℚ_[l] P.R.BdR LL V (-a) x = -mulR ℚ_[l] P.R.BdR LL V a x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, neg_zero]
  | tmul v c => simp [tmul_neg]
  | add y z hy hz => simp only [map_add (f := _), hy, hz, neg_add]

private theorem mulR_one (x : V ⊗[ℚ_[l]] P.R.BdR) :
    mulR ℚ_[l] P.R.BdR LL V 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v c => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

private theorem act_mulR (K : FinExt l) (ρ : Representation LL ↥(GK K) V) (g : ↥(GK K))
    (a : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    actVdR (P.PD K) ρ g (mulR ℚ_[l] P.R.BdR LL V a x) =
      mulR ℚ_[l] P.R.BdR LL V ((P.PD K).actdR g a) (actVdR (P.PD K) ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v c => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

private def spanD (K : FinExt l) (ρ : Representation LL ↥(GK K) V) :
    AddSubgroup (V ⊗[ℚ_[l]] P.R.BdR) where
  carrier := {y | ∃ (m : ℕ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR),
    (∀ i, d i ∈ DdR (P.PD K) ρ) ∧ y = ∑ i, mulR ℚ_[l] P.R.BdR LL V (b i) (d i)}
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, b, d, hd, rfl⟩ ⟨n, b', d', hd', rfl⟩
    refine ⟨m + n, Fin.append b b', Fin.append d d', fun i => ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hd j
      · rw [Fin.append_right]; exact hd' j
    · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  neg_mem' := by
    rintro _ ⟨m, b, d, hd, rfl⟩
    refine ⟨m, fun i => -b i, d, hd, ?_⟩
    simp only [mulR_neg, Finset.sum_neg_distrib]

private theorem mulR_mem_spanD (K : FinExt l) (ρ : Representation LL ↥(GK K) V) (a : P.R.BdR)
    (x : V ⊗[ℚ_[l]] P.R.BdR) (hx : x ∈ spanD P K ρ) :
    mulR ℚ_[l] P.R.BdR LL V a x ∈ spanD P K ρ := by
  obtain ⟨m, b, d, hd, rfl⟩ := hx
  refine ⟨m, fun i => a * b i, d, hd, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, mulR_mulR]

private theorem act_mem_spanD (K : FinExt l) (ρ : Representation LL ↥(GK K) V) (g : ↥(GK K))
    (x : V ⊗[ℚ_[l]] P.R.BdR) (hx : x ∈ spanD P K ρ) :
    actVdR (P.PD K) ρ g x ∈ spanD P K ρ := by
  obtain ⟨m, b, d, hd, rfl⟩ := hx
  refine ⟨m, fun i => (P.PD K).actdR g (b i), d, hd, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [act_mulR, (mem_DdR (P.PD K) ρ _).1 (hd i)]

private theorem mem_spanD_of_fixed {K K' : FinExt l} (h : K.1 ≤ K'.1)
    (ρ : Representation LL ↥(GK K) V) (x : V ⊗[ℚ_[l]] P.R.BdR)
    (hxH : x ∈ DdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) :
    x ∈ spanD P K ρ := by
  haveI : FiniteDimensional ℚ_[l] ↥K'.1 := K'.2
  haveI : Finite (GQ l ⧸ GK K') :=
    Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen K'.1)
  haveI : (GK K').FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine JumpDescent.descent (Ω := Om l) ((GK K').subgroupOf (GK K))
    (fun g => (actVdR (P.PD K) ρ g).toAddMonoidHom) ?_ ?_
    (fun c => (mulR ℚ_[l] P.R.BdR LL V (algebraMap (Om l) P.R.BdR c)).toAddMonoidHom) ?_ ?_ ?_
    (fun g => ((g : GQ l) : Om l →* Om l)) (fun _ _ _ => rfl) (fun _ => rfl) ?_
    K'.1.toSubalgebra.toSubsemiring.toSubmonoid ?_
    ⊤ (spanD P K ρ) (fun _ _ _ => trivial) (fun _ _ _ => trivial) (act_mem_spanD P K ρ)
    (fun c => mulR_mem_spanD P K ρ _)
    (fun y _ hy' => ⟨1, fun _ => 1, fun _ => y, fun _ => (mem_DdR (P.PD K) ρ y).2 hy', by
      simp only [mulR_one, Fin.sum_univ_one]⟩) x trivial ?_
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  · intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  · intro x
    simp only [map_one, LinearMap.toAddMonoidHom_coe, mulR_one]
  · intro g g' x
    simp only [map_mul, LinearMap.toAddMonoidHom_coe, mulR_mulR]
  · intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, add_zero]
    | tmul v b => simp [add_mul, tmul_add]
    | add y z hy hz => simp only [map_add (f := _)] at hy hz ⊢; rw [hy, hz]; abel
  · intro g c x
    simp only [LinearMap.toAddMonoidHom_coe]
    rw [act_mulR, P.PD_actdR, P.actQdR_Om]
    rfl
  · intro g
    rw [Subgroup.mem_subgroupOf]
    exact ⟨fun hg a ha => hg ⟨a, ha⟩, fun hg a => hg a.1 a.2⟩
  · intro g hg
    have := (mem_DdR (P.PD K') _ x).1 hxH ⟨g.1, hg⟩
    rw [JumpDescent.actVdR_comp P h] at this
    exact this

end

theorem spans_descent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1)
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V),
    Spans (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) → Spans (P.PD K) ρ := by
  intro l _ P K K' LL h V _ _ _ _ ρ hs y
  obtain ⟨m, b, d, hd, rfl⟩ := hs y
  exact (spanD P K ρ).sum_mem fun i _ =>
    mulR_mem_spanD P K ρ _ _ (mem_spanD_of_fixed P h ρ _ (hd i))

end GlobalTheory.DRFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyClosureHomTiltField
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem exists_pow_eq_one_of_algClosure_zmod (l : ℕ) [hl : Fact l.Prime] (a : AlgebraicClosure (ZMod l))
    (ha : a ≠ 0) : ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ a ^ m = 1 := by
  first
  | exact @_root_.GlobalTheory.ProofStatement.main
  | exact _root_.GlobalTheory.ProofStatement.main
  | (apply _root_.GlobalTheory.ProofStatement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProofStatement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProofStatement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProofStatement.main ..)

theorem exists_isPrimitiveRoot_tilt (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (hm : 0 < m) (hlm : ¬ l ∣ m) :
    ∃ e : Per.Fl l, IsPrimitiveRoot e m := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨x, hx⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  obtain ⟨e, he, hex⟩ := exists_tilt_root_of_unity l x m hm hlm hx.pow_eq_one
  refine ⟨e, he, fun d hd => hx.dvd_of_pow_eq_one d ?_⟩
  have h1 : e.untilt ^ d = 1 := by rw [← map_pow, hd, map_one]
  have h2 : (x : ℂ_[l]) ^ d = 1 := by
    rw [← hex]
    exact_mod_cast congrArg Subtype.val h1
  apply (algebraMap (Om l) ℂ_[l]).injective
  rw [map_pow, map_one]
  exact h2

theorem nonempty_algClosure_zmod_to_tilt :
    ∀ (l : ℕ) [Fact l.Prime], Nonempty (AlgebraicClosure (ZMod l) →+* Per.Fl l) := by
  intro l hl
  haveI : IsDomain (Per.Fl l) := inferInstance
  haveI : CharP (Per.Fl l) l := inferInstance
  let Ω := AlgebraicClosure (FractionRing (Per.Fl l))
  let j : Per.Fl l →+* Ω :=
    (algebraMap (FractionRing (Per.Fl l)) Ω).comp (algebraMap (Per.Fl l) (FractionRing (Per.Fl l)))
  have hj : Function.Injective j :=
    (algebraMap (FractionRing (Per.Fl l)) Ω).injective.comp (IsFractionRing.injective _ _)
  haveI : CharP Ω l := charP_of_injective_ringHom hj l
  letI : Algebra (ZMod l) Ω := ZMod.algebra Ω l
  let f₀ : AlgebraicClosure (ZMod l) →ₐ[ZMod l] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hr : ∀ a, (f₀ : AlgebraicClosure (ZMod l) →+* Ω) a ∈ j.range := by
    intro a
    by_cases ha : a = 0
    · rw [ha, map_zero]; exact zero_mem _
    obtain ⟨m, hm, hlm, ham⟩ := exists_pow_eq_one_of_algClosure_zmod l a ha
    obtain ⟨e, he⟩ := exists_isPrimitiveRoot_tilt l m hm hlm
    haveI : NeZero m := ⟨hm.ne'⟩
    obtain ⟨i, -, hi⟩ := (he.map_of_injective hj).eq_pow_of_pow_eq_one
      (ξ := (f₀ : AlgebraicClosure (ZMod l) →+* Ω) a) (by rw [← map_pow, ham, map_one])
    exact ⟨e ^ i, by rw [map_pow, hi]⟩
  let E : Per.Fl l ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun x y h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  exact ⟨E.symm.toRingHom.comp ((f₀ : AlgebraicClosure (ZMod l) →+* Ω).codRestrict j.range hr)⟩

end GlobalTheory.Per
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCoeAutLeOneIff
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

namespace GlobalTheory.EigenCoord

theorem exists_basis_mem_iff {O L V : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L]
    [IsFractionRing O L] [AddCommGroup V] [Module L V] [Module O V] [IsScalarTower O L V]
    (T : Submodule O V) (hfg : T.FG) (hfree : Module.Free O T)
    (hspan : Submodule.span L (T : Set V) = ⊤) :
    ∃ (ρ : ℕ) (t : Module.Basis (Fin ρ) L V),
      ∀ v, v ∈ T ↔ ∀ i, ∃ o : O, algebraMap O L o = t.repr v i := by
  haveI : Module.Finite O T := Module.Finite.iff_fg.mpr hfg
  let c := Module.finBasis O T
  have hli : LinearIndependent O (fun i => (c i : V)) :=
    c.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hli' : LinearIndependent L (fun i => (c i : V)) :=
    (LinearIndependent.iff_fractionRing O L).mp hli
  have hsum : ∀ x : T, (x : V) = ∑ i, algebraMap O L (c.repr x i) • (c i : V) := by
    intro x
    have h := congrArg T.subtype (c.sum_repr x)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simp only [map_smul, Submodule.subtype_apply] at h
    simp only [algebraMap_smul]
    exact h.symm
  have hsp : ⊤ ≤ Submodule.span L (Set.range fun i => (c i : V)) := by
    rw [← hspan, Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, show x = ((⟨x, hx⟩ : T) : V) from rfl, hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let t := Module.Basis.mk hli' hsp
  have ht : ∀ i, t i = (c i : V) := fun i => Module.Basis.mk_apply hli' hsp i
  refine ⟨_, t, fun v => ⟨fun hv i => ⟨c.repr ⟨v, hv⟩ i, ?_⟩, fun h => ?_⟩⟩
  · have h1 : v = ∑ j, algebraMap O L (c.repr ⟨v, hv⟩ j) • t j := by
      simp only [ht]
      exact hsum ⟨v, hv⟩
    have h2 := congrFun (t.repr_sum_self (fun j => algebraMap O L (c.repr ⟨v, hv⟩ j))) i
    rw [← h1] at h2
    exact h2.symm
  · choose o ho using h
    rw [← t.sum_repr v]
    refine T.sum_mem fun i _ => ?_
    rw [← ho, algebraMap_smul, ht]
    exact T.smul_mem _ (c i).2

theorem norm_coe_aut_le_one_iff {l : ℕ} [Fact l.Prime] (ι : GQ l) (x : Om l) :
    ‖((ι x : Om l) : PadicComplex l)‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_extends, ← isIntegral_padicInt_iff_norm_le_one,
    ← isIntegral_padicInt_iff_norm_le_one]
  exact isIntegral_algHom_iff (ι.toAlgHom.restrictScalars ℤ_[l]) ι.injective

theorem exists_matrix_of_basis {F L C V : Type} [NormedField F] [Field L] [NormedField C]
    [Algebra F L] [Algebra F C] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    (S : Set V) {d ρ : ℕ} (b : Module.Basis (Fin d) F V) (t : Module.Basis (Fin ρ) L V)
    (φ : L →ₐ[F] C) (hb : ∀ v, v ∈ S ↔ ∀ i, ‖b.repr v i‖ ≤ 1)
    (hmem : ∀ v, v ∈ S ↔ ∀ i, ‖φ (t.repr v i)‖ ≤ 1) :
    ∃ Pr : Matrix (Fin ρ) (Fin d) C, (∀ i j, ‖Pr i j‖ ≤ 1) ∧
      (∀ a : L, Pr * Matrix.of (fun i k : Fin d => algebraMap F C (b.repr (a • b k) i)) =
        φ a • Pr) ∧
      ∀ y : Fin d → F, (∀ i, ‖Pr.mulVec (fun a => algebraMap F C (y a)) i‖ ≤ 1) →
        ∀ a, ‖y a‖ ≤ 1 := by
  have key : ∀ (y : Fin d → F) (i : Fin ρ),
      ∑ j, φ (t.repr (b j) i) * algebraMap F C (y j) = φ (t.repr (∑ j, y j • b j) i) := by
    intro y i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul L (y j), map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
      AlgHom.commutes, mul_comm]
  refine ⟨Matrix.of fun i j => φ (t.repr (b j) i), fun i j => ?_, fun a => ?_, fun y hy a => ?_⟩
  · refine (hmem _).mp ((hb _).mpr fun k => ?_) i
    rw [b.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  · ext i k
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Matrix.smul_apply]
    rw [key, b.sum_repr, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, smul_eq_mul]
  · have hv : (∑ j, y j • b j) ∈ S := by
      refine (hmem _).mpr fun i => ?_
      rw [← key]
      exact hy i
    have := (hb _).mp hv a
    rwa [congrFun (b.repr_sum_self y) a] at this

theorem exists_matrix : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (b : Module.Basis (Fin d) ℚ_[l] T.V), (∀ v : T.V, v ∈ T.L.T ↔ ∀ i, ‖b.repr v i‖ ≤ 1) → ∀ ι : GQ l, ∃ (ρ : ℕ) (Pr : Matrix (Fin ρ) (Fin d) (PadicComplex l)), (∀ i j, ‖Pr i j‖ ≤ 1) ∧ (∀ a : ↥LL.1, Pr * Matrix.of (fun i k : Fin d => algebraMap ℚ_[l] (PadicComplex l) (b.repr (a • b k) i)) = ((ι (a : Om l) : Om l) : PadicComplex l) • Pr) ∧ ∀ y : Fin d → ℚ_[l], (∀ i, ‖Pr.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) i‖ ≤ 1) → ∀ a, ‖y a‖ ≤ 1 := by
  intro l _ K LL T d b hb ι
  haveI := LL.2
  haveI : IsFractionRing (OL LL) LL.1 := isFractionRing_integralClosure_padicInt l LL.1
  obtain ⟨ρ, t, ht⟩ := exists_basis_mem_iff (L := LL.1) T.L.T T.L.fg T.L.free T.L.span
  let φ : LL.1 →ₐ[ℚ_[l]] PadicComplex l :=
    (IsScalarTower.toAlgHom ℚ_[l] (Om l) (PadicComplex l)).comp (ι.toAlgHom.comp LL.1.val)
  have hφ : ∀ x : LL.1, φ x = ((ι (x : Om l) : Om l) : PadicComplex l) := fun _ => rfl
  have hmem : ∀ v, v ∈ T.L.T ↔ ∀ i, ‖φ (t.repr v i)‖ ≤ 1 := by
    intro v
    rw [ht]
    refine forall_congr' fun i => ?_
    rw [hφ, norm_coe_aut_le_one_iff, ← mem_integralClosure_padicInt_iff]
    exact ⟨fun ⟨o, ho⟩ => ho ▸ o.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  exact ⟨ρ, exists_matrix_of_basis (T.L.T : Set T.V) b t φ hb hmem⟩

end GlobalTheory.EigenCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGeomSumGaloisLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem geom_sum_add_one_eq_sum_choose {R : Type*} [Ring R] (D : R) (n : ℕ) :
    ∑ i ∈ Finset.range n, (D + 1) ^ i = ∑ j ∈ Finset.range n, n.choose (j + 1) • D ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h := (Commute.one_right D).add_pow n
    simp only [one_pow, mul_one] at h
    rw [h]
    simp_rw [Nat.choose_succ_succ', add_smul]
    rw [Finset.sum_add_distrib, Finset.sum_range_succ (fun j => n.choose (j + 1) • D ^ j) n,
      Nat.choose_succ_self, zero_smul, add_zero, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [nsmul_eq_mul, Nat.cast_comm]

theorem norm_geom_sum_galois_le (l : ℕ) [Fact l.Prime] (σ : GQ l) (S : AddSubgroup (Om l)) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hS : ∀ x ∈ S, σ x ∈ S) (hσ : ∀ x ∈ S, ‖σ x - x‖ ≤ s * ‖x‖) :
    ∀ x ∈ S, ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * ‖x‖ ∧
      ‖(σ ^ l) x - x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * s * ‖x‖ := by
  intro x hx
  set M := max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ with hM

  have hpowS : ∀ (i : ℕ), ∀ y ∈ S, (σ ^ i) y ∈ S := by
    intro i
    induction i with
    | zero => intro y hy; simpa using hy
    | succ i ih => intro y hy; rw [pow_succ', AlgEquiv.mul_apply]; exact hS _ (ih y hy)

  let T : AddMonoid.End (Om l) := AddMonoidHom.mk' (fun y => σ y) (fun a b => map_add σ a b)
  have hT : ∀ (i : ℕ) (y : Om l), (T ^ i) y = (σ ^ i) y := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih => intro y; rw [pow_succ', pow_succ', AlgEquiv.mul_apply, ← ih]; rfl
  have hD : ∀ (j : ℕ), ∀ y ∈ S, ((T - 1) ^ j) y ∈ S ∧ ‖((T - 1) ^ j) y‖ ≤ s ^ j * ‖y‖ := by
    intro j
    induction j with
    | zero => intro y hy; rw [pow_zero]; exact ⟨hy, by rw [pow_zero, one_mul]; exact le_rfl⟩
    | succ j ih =>
      intro y hy
      obtain ⟨h1, h2⟩ := ih y hy
      rw [pow_succ']
      change σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y ∈ S ∧
        ‖σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y‖ ≤ s ^ (j + 1) * ‖y‖
      refine ⟨S.sub_mem (hS _ h1) h1, ?_⟩
      calc ‖σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y‖ ≤ s * ‖((T - 1) ^ j) y‖ := hσ _ h1
        _ ≤ s * (s ^ j * ‖y‖) := mul_le_mul_of_nonneg_left h2 hs0
        _ = s ^ (j + 1) * ‖y‖ := by ring

  have hnat : ∀ n : ℕ, ‖((n : ℕ) : Om l)‖ ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih norm_one.le)

  have key := geom_sum_add_one_eq_sum_choose (T - 1) l
  rw [sub_add_cancel] at key
  have hsum : ∑ i ∈ Finset.range l, (σ ^ i) x =
      ∑ j ∈ Finset.range l, l.choose (j + 1) • ((T - 1) ^ j) x := by
    let ev : AddMonoid.End (Om l) →+ Om l :=
      { toFun := fun f => f x, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have h := congrArg ev key
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_nsmul] at h
    calc ∑ i ∈ Finset.range l, (σ ^ i) x = ∑ i ∈ Finset.range l, (T ^ i) x :=
          Finset.sum_congr rfl fun i _ => (hT i x).symm
      _ = _ := h
  have hbound : ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ M * ‖x‖ := by
    rw [hsum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (mul_nonneg (le_max_of_le_right (norm_nonneg _)) (norm_nonneg _)) fun j hj => ?_
    obtain ⟨-, hle⟩ := hD j x hx
    have hsj : s ^ j ≤ 1 := pow_le_one₀ hs0 hs1
    rw [nsmul_eq_mul, norm_mul]
    rcases Nat.lt_or_ge (j + 1) l with hlt | hge
    ·
      obtain ⟨m, hm⟩ := (Fact.out : l.Prime).dvd_choose_self (Nat.succ_ne_zero j) hlt
      rw [hm, Nat.cast_mul, norm_mul]
      have h3 : ‖((T - 1) ^ j) x‖ ≤ 1 * ‖x‖ :=
        hle.trans (mul_le_mul_of_nonneg_right hsj (norm_nonneg _))
      calc _ ≤ ‖((l : ℕ) : Om l)‖ * 1 * (1 * ‖x‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hnat m) (norm_nonneg _)) h3 (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) zero_le_one)
        _ ≤ M * ‖x‖ := by
            rw [mul_one, one_mul]
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    ·
      have hjl : j = l - 1 := by have := Finset.mem_range.mp hj; omega
      have hc : l.choose (j + 1) = 1 := by
        rw [show j + 1 = l by have := Finset.mem_range.mp hj; omega, Nat.choose_self]
      rw [hc, Nat.cast_one, norm_one, one_mul]
      calc _ ≤ s ^ j * ‖x‖ := hle
        _ ≤ M * ‖x‖ := by
            rw [hjl]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

  set y := ∑ i ∈ Finset.range l, (σ ^ i) x with hy
  have hyS : y ∈ S := S.sum_mem fun i _ => hpowS i x hx
  have htel : (σ ^ l) x - x = σ y - y := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, map_sum, ← Finset.sum_sub_distrib]
    have h := Finset.sum_range_sub (fun i => (σ ^ i) x) l
    simp only [pow_zero, AlgEquiv.one_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ', AlgEquiv.mul_apply]
  refine ⟨hbound, ?_⟩
  rw [htel]
  calc ‖σ y - y‖ ≤ s * ‖y‖ := hσ y hyS
    _ ≤ s * (M * ‖x‖) := mul_le_mul_of_nonneg_left hbound hs0
    _ = M * s * ‖x‖ := by ring

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestric
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.PcRes

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (pc P h hN hF hS).Dpcris ρ = Dcris (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) ∧ ((pc P h hN hF hS).IsPotCrys ρ ↔ IsCrys (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) := by
  intro l _ P K K' LL h hN hF hS V _ _ _ _ ρ
  have key : (pc P h hN hF hS).Dpcris ρ =
      Dcris (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) := by
    unfold PotCrysData.Dpcris Dcris
    exact (GKinEquiv h).surjective.iInf_congr (GKinEquiv h) (fun x => rfl)
  refine ⟨key, ?_⟩
  unfold PotCrysData.IsPotCrys IsCrys
  have key' : Dcris (pc P h hN hF hS).PD' ((pc P h hN hF hS).resH ρ) =
      Dcris (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) := key
  rw [key']

end GlobalTheory.PcRes
end

