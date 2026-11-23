module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0027
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0028
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderFundamentalLengthsStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_fundamental_lengths : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∃ d : Fin n → Fin f → R, (∀ (i : Fin n) (s : Fin f), idealD p AA.carrier (flagSub b i) (b i) (σ ^ p ^ (s : ℕ)) = Ideal.span {d i s}) ∧ HasLen v R (AFQuot p AA.carrier) (∏ i, ∏ s, v (algebraMap R C (d i s))) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_lengths | exact GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_lengths | (intros; apply GlobalTheory.CompanionTheory.Relay.stable_hopf_order_fundamental_lengths <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubDegreeBotAndMaxExists
section
noncomputable section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubdegMax

variable {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]

def latOf (i : C.I) {n : ℕ} (b : Module.Basis (Fin n) K V) : AddSubgroup V where
  carrier := {x | ∀ q, C.v i (b.repr x q) ≤ 1}
  zero_mem' := fun q => by simp
  add_mem' := fun {x y} hx hy q => by
    rw [map_add (f := _), Finsupp.add_apply]; exact (C.v i).map_add_le (hx q) (hy q)
  neg_mem' := fun {x} hx q => by
    rw [map_neg, Finsupp.neg_apply, Valuation.map_neg]; exact hx q

theorem isLatOf_latOf (i : C.I) {n : ℕ} (b : Module.Basis (Fin n) K V) :
    IsLatOf C i b (latOf C i b) := fun _ => Iff.rfl

def scale (L : C.I → AddSubgroup V) (c : C.I → Kˣ) : C.I → AddSubgroup V :=
  fun i => (L i).comap (DistribSMul.toAddMonoidHom V (((c i)⁻¹ : Kˣ) : K))

theorem mem_scale (L : C.I → AddSubgroup V) (c : C.I → Kˣ) (i : C.I) (x : V) :
    x ∈ scale C L c i ↔ (((c i)⁻¹ : Kˣ) : K) • x ∈ L i := Iff.rfl

theorem isLatOf_scale {L : C.I → AddSubgroup V} (c : C.I → Kˣ) {i : C.I} {n : ℕ}
    {b : Module.Basis (Fin n) K V} (h : IsLatOf C i b (L i)) :
    IsLatOf C i (b.unitsSMul fun _ => c i) (scale C L c i) := by
  intro x
  rw [mem_scale, h]
  refine forall_congr' fun q => ?_
  rw [Module.Basis.repr_unitsSMul, map_smul, Finsupp.smul_apply]
  rfl

theorem isBun_scale {L : C.I → AddSubgroup V} (c : C.I → Kˣ) (hc : {i | c i ≠ 1}.Finite)
    (h : IsBun C L) : IsBun C (scale C L c) := by
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := h.1 i
    exact ⟨_, isLatOf_scale C c hb⟩
  · obtain ⟨b, hb⟩ := h.2
    refine ⟨b, (hb.union hc).subset fun i hi => ?_⟩
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn hi
    apply hi
    intro x
    rw [mem_scale, hn.2, inv_one, Units.val_one, one_smul]
    exact hn.1 x

theorem deg_scale [FiniteDimensional K V] {L : C.I → AddSubgroup V} (c : C.I → Kˣ)
    (hc : {i | c i ≠ 1}.Finite) (h : IsBun C L) :
    deg C (scale C L c) = deg C L +
      (Module.finrank K V : ℤ) * ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (c i)) := by
  choose b hb using h.1
  obtain ⟨hf, e⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula K C V L _ (Module.finBasis K V) b h hb
  obtain ⟨-, e'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula K C V (scale C L c) _ (Module.finBasis K V)
    (fun i => (b i).unitsSMul fun _ => c i) (isBun_scale C c hc h)
    (fun i => isLatOf_scale C c (hb i))
  have hs1 : (Function.support fun i =>
      (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i)))).Finite := by
    refine hf.subset fun i hi => ?_
    intro h1
    exact hi (by simp [h1])
  have hs3 : (Function.support fun i => (Module.finrank K V : ℤ) *
      ((C.w i : ℤ) * WithZero.log (C.v i (c i)))).Finite := by
    refine hc.subset fun i hi => ?_
    intro h1
    exact hi (by simp [h1])
  rw [e, e', mul_finsum, ← finsum_add_distrib hs1 hs3]
  refine finsum_congr fun i => ?_
  have hd : (Module.finBasis K V).det ((b i).unitsSMul fun _ => c i) =
      (c i : K) ^ Module.finrank K V * (Module.finBasis K V).det (b i) := by
    have : ⇑((b i).unitsSMul fun _ => c i) = fun j => (c i : K) • b i j := by
      funext j; rw [Module.Basis.unitsSMul_apply]; rfl
    rw [this]
    have := (Module.finBasis K V).det.toMultilinearMap.map_smul_univ (fun _ => (c i : K)) (b i)
    simpa using this
  have h0 : C.v i ((Module.finBasis K V).det (b i)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact ((Module.finBasis K V).isUnit_det (b i)).ne_zero
  have h1 : C.v i (c i) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact (c i).ne_zero
  rw [hd, map_mul, map_pow, WithZero.log_mul (pow_ne_zero _ h1) h0, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

theorem exists_scale (i : C.I) {n m : ℕ} (b : Module.Basis (Fin n) K V)
    {b' : Module.Basis (Fin m) K V} {L : AddSubgroup V} (h : IsLatOf C i b' L) :
    ∃ c : Kˣ, 1 ≤ C.v i c ∧ ∀ x ∈ L, ((c⁻¹ : Kˣ) : K) • x ∈ latOf C i b := by
  classical
  obtain ⟨c, -, hc⟩ := Finset.exists_max_image
    (insert (1 : K) (Finset.univ.image fun p : Fin m × Fin n => b.repr (b' p.1) p.2))
    (C.v i) (Finset.insert_nonempty _ _)
  have h1 : 1 ≤ C.v i c := by simpa using hc 1 (Finset.mem_insert_self _ _)
  have hpos : 0 < C.v i c := lt_of_lt_of_le zero_lt_one h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hpos
  refine ⟨Units.mk0 c hc0, h1, fun x hx q => ?_⟩
  have hle : C.v i (b.repr x q) ≤ C.v i c := by
    have hx' : b.repr x q = ∑ j, b'.repr x j * b.repr (b' j) q := by
      conv_lhs => rw [← b'.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [hx']
    refine (C.v i).map_sum_le fun j _ => ?_
    rw [map_mul]
    calc _ ≤ 1 * C.v i c := mul_le_mul' ((h x).1 hx j)
          (hc _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(j, q), Finset.mem_univ _, rfl⟩)))
      _ = _ := one_mul _
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, Units.val_mk0,
    map_inv₀, inv_mul_le_iff₀ hpos, mul_one]
  exact hle

theorem subDeg_bot [FiniteDimensional K V] (L : C.I → AddSubgroup V) : subDeg C L ⊥ = 0 := by
  unfold subDeg deg
  have : IsEmpty (Fin (Module.finrank K (⊥ : Submodule K V))) := by
    rw [finrank_bot]; infer_instance
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  simp [Module.Basis.det_apply]

theorem subDeg_bdd [FiniteDimensional K V] (L : C.I → AddSubgroup V) (h : IsBun C L) :
    ∃ B : ℤ, ∀ W : Submodule K V, subDeg C L W ≤ B := by
  classical
  obtain ⟨b, hb⟩ := h.2
  have key : ∀ i, ∃ c : Kˣ, (IsLatOf C i b (L i) → c = 1) ∧ 1 ≤ C.v i c ∧
      ∀ x ∈ L i, ((c⁻¹ : Kˣ) : K) • x ∈ latOf C i b := by
    intro i
    by_cases hi : IsLatOf C i b (L i)
    · refine ⟨1, fun _ => rfl, by simp, fun x hx => ?_⟩
      rw [inv_one, Units.val_one, one_smul]
      exact (hi x).1 hx
    · obtain ⟨b', hb'⟩ := h.1 i
      obtain ⟨c, h1, h2⟩ := exists_scale C i b hb'
      exact ⟨c, fun h' => absurd h' hi, h1, h2⟩
  choose c hc1 hc2 hc3 using key
  have hc : {i | c i ≠ 1}.Finite := hb.subset fun i hi h' => hi (hc1 i h')
  have h0 : IsBun C (fun i => latOf C i b) :=
    ⟨fun i => ⟨b, isLatOf_latOf C i b⟩, b, by simp [isLatOf_latOf]⟩
  set S : ℤ := ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (c i)) with hS
  have hS0 : 0 ≤ S := by
    refine finsum_nonneg fun i => mul_nonneg (Int.natCast_nonneg _) ?_
    have h1 : C.v i (c i) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact (c i).ne_zero
    have := (WithZero.log_le_log one_ne_zero h1).2 (hc2 i)
    simpa using this
  refine ⟨(Module.finrank K V : ℤ) * S, fun W => ?_⟩
  have hW := (_root_.GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C V _ W h0).1
  have e1 := _root_.GlobalTheory.CompanionTheory.Ar.Crv.deg_le_deg_of_le K C W (sub C L W) (scale C (sub C (fun i => latOf C i b) W) c)
    (_root_.GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C V _ W h).1 (isBun_scale C c hc hW) (fun i x hx => hc3 i x hx)
  have e2 := deg_scale C c hc hW
  have e3 := _root_.GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_zero_of_trivial K C V _ b (fun i => latOf C i b) W (fun i => isLatOf_latOf C i b)
  have e4 : (Module.finrank K W : ℤ) * S ≤ (Module.finrank K V : ℤ) * S :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast W.finrank_le) hS0
  unfold subDeg at e3 ⊢
  rw [← hS] at e2
  linarith

theorem subDeg_max : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (L : C.I → AddSubgroup V), IsBun C L →
    subDeg C L ⊥ = 0 ∧ ∃ W₀ : Submodule K V, ∀ W : Submodule K V, subDeg C L W ≤ subDeg C L W₀ := by
  intro K _ C V _ _ _ L h
  refine ⟨subDeg_bot C L, ?_⟩
  obtain ⟨B, hB⟩ := subDeg_bdd C L h
  obtain ⟨z, ⟨W₀, rfl⟩, hz⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ W : Submodule K V, subDeg C L W = z)
    ⟨B, by rintro _ ⟨W, rfl⟩; exact hB W⟩ ⟨_, ⊥, rfl⟩
  exact ⟨W₀, fun W => hz _ ⟨W, rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.Crv.SubdegMax
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsFiniteFlatSubgroup
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.torsion_points_finite_flat_subgroup : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ K : AddSubgroup N, IsFinFlatSub G (T.A ⧸ vanIdeal T pt K) (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) := by
  classical
  intro p _ C _ _ _ v R _ _ hv hp G _ _ T N _ _ _ pt hpt K
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI : ValuationRing R := ValuationRing.iff_dvd_total.mpr ⟨fun a b => by
    rcases le_total (v (algebraMap R C a)) (v (algebraMap R C b)) with h | h
    · exact Or.inr (hv.dvd_of_le h)
    · exact Or.inl (hv.dvd_of_le h)⟩
  haveI : IsLocalRing R := ValuationRing.isLocalRing R
  haveI : IsBezout R := ValuationRing.instIsBezout
  haveI : Module.Finite R T.A := T.fin
  set I : Ideal T.A := vanIdeal T pt (K : Set N) with hI
  have hpts : ∀ x : N, pt x ^ p = 1 := fun x => (hpt.range (pt x)).mpr ⟨x, rfl⟩
  choose ev hev using fun x : N => (T.univ R (pt x) (hpts x)).exists
  have huniq : ∀ (x : N) (φ : T.A →ₐ[R] R), spMap φ ≫ T.y = pt x → φ = ev x :=
    fun x φ h => (T.univ R (pt x) (hpts x)).unique h (hev x)
  have memI : ∀ a : T.A, a ∈ I ↔ ∀ k ∈ K, ev k a = 0 := by
    intro a
    constructor
    · intro ha k hk
      have ha' : ∀ k ∈ (K : Set N), ∀ φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt k → φ a = 0 := ha
      exact ha' k hk (ev k) (hev k)
    · intro ha
      show ∀ k ∈ (K : Set N), ∀ φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt k → φ a = 0
      intro k hk φ hφ
      rw [huniq k φ hφ]
      exact ha k hk
  obtain ⟨evbar, hevbar⟩ : ∃ e : K → ((T.A ⧸ I) →ₐ[R] R),
      ∀ k, (e k).comp (Ideal.Quotient.mkₐ R I) = ev k :=
    ⟨fun k => Ideal.Quotient.liftₐ I (ev k) (fun a ha => (memI a).mp ha k k.2),
      fun k => Ideal.Quotient.liftₐ_comp _ _ _⟩
  have hsep1 : ∀ b : T.A ⧸ I, (∀ k : K, evbar k b = 0) → b = 0 := by
    intro b hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I b
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, memI]
    intro k hk
    have h1 := hb ⟨k, hk⟩
    rw [← AlgHom.comp_apply, hevbar] at h1
    exact h1
  have htors : Submodule.torsion R (T.A ⧸ I) = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff b).mp hb
    rw [Submodule.mem_bot]
    refine hsep1 b fun k => ?_
    have h1 := congrArg (evbar k) hr
    rw [map_zero, Submonoid.smul_def, map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (nonZeroDivisors.coe_ne_zero r)
  haveI : Module.Flat R (T.A ⧸ I) := (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).mpr htors
  haveI : Module.Finite R (T.A ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ_surjective R I)
  haveI : Module.Free R (T.A ⧸ I) := Module.free_of_flat_of_isLocalRing
  have h0 : pt 0 = 1 := mul_left_cancel (a := pt 0) (by rw [_root_.mul_one, ← hpt.add, add_zero])
  have hneg : ∀ x, pt (-x) = (pt x)⁻¹ := fun x =>
    eq_inv_of_mul_eq_one_left (by rw [← hpt.add, neg_add_cancel, h0])
  have hE : ∀ k : K, spMap (evbar k) ≫ spMap (Ideal.Quotient.mkₐ R I) ≫ T.y = pt k := by
    intro k
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hevbar, hev]
  have hpowA : ∀ {X : Over (Spec (CommRingCat.of R))} (f : X ⟶ sp (R₀ := R) T.A), (f ≫ T.y) ^ p = 1 :=
    fun f => by rw [← CategoryTheory.MonObj.comp_pow, T.y_p, CategoryTheory.MonObj.comp_one]
  have hu : (spMap (Ideal.Quotient.mkₐ R I) ≫ T.y) ^ p = 1 := hpowA _
  have hpowc : ∀ {X : Over (Spec (CommRingCat.of R))} (f : X ⟶ sp (R₀ := R) (T.A ⧸ I)),
      (f ≫ spMap (Ideal.Quotient.mkₐ R I) ≫ T.y) ^ p = 1 :=
    fun f => by rw [← CategoryTheory.MonObj.comp_pow, hu, CategoryTheory.MonObj.comp_one]
  obtain ⟨Λ, hΛt⟩ : ∃ L : K → K → (TensorProduct R (T.A ⧸ I) (T.A ⧸ I) →ₐ[R] R),
      ∀ k1 k2 x y, L k1 k2 (TensorProduct.tmul R x y) = evbar k1 x * evbar k2 y :=
    ⟨fun k1 k2 => Algebra.TensorProduct.lift (evbar k1) (evbar k2) (fun _ _ => Commute.all _ _),
      fun _ _ _ _ => Algebra.TensorProduct.lift_tmul _ _ _ _ _⟩
  have hΛL : ∀ k1 k2, (Λ k1 k2).comp Algebra.TensorProduct.includeLeft = evbar k1 := fun k1 k2 =>
    AlgHom.ext fun b => by simp [hΛt]
  have hΛR : ∀ k1 k2, (Λ k1 k2).comp Algebra.TensorProduct.includeRight = evbar k2 := fun k1 k2 =>
    AlgHom.ext fun b => by simp [hΛt]
  have hι : Function.Injective (Pi.algHom R (fun _ : K => R) evbar).toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    exact hsep1 b fun k => by simpa using congrFun hb k
  have key : ∀ (w : TensorProduct R (T.A ⧸ I) (T.A ⧸ I)) (k1 k2 : K),
      (Pi.algHom R (fun _ : K => R) evbar).toLinearMap
        (TensorProduct.piScalarRight R R (T.A ⧸ I) K
          (((Pi.algHom R (fun _ : K => R) evbar).toLinearMap.lTensor (T.A ⧸ I)) w) k2) k1 =
        Λ k1 k2 w := by
    intro w k1 k2
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hΛt, TensorProduct.piScalarRight_apply, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]
  have hsep2 : ∀ w : TensorProduct R (T.A ⧸ I) (T.A ⧸ I), (∀ k1 k2 : K, Λ k1 k2 w = 0) → w = 0 := by
    intro w hw
    have h1 : TensorProduct.piScalarRight R R (T.A ⧸ I) K
        (((Pi.algHom R (fun _ : K => R) evbar).toLinearMap.lTensor (T.A ⧸ I)) w) = 0 := by
      funext k2
      apply hι
      funext k1
      rw [key, hw]
      simp
    rw [LinearEquiv.map_eq_zero_iff] at h1
    exact (injective_iff_map_eq_zero _).mp
      (Module.Flat.lTensor_preserves_injective_linearMap _ hι) w h1
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro S _ _ φ φ' hφ
    have e1 : spMap (φ.comp (Ideal.Quotient.mkₐ R I)) ≫ T.y =
        spMap (φ'.comp (Ideal.Quotient.mkₐ R I)) ≫ T.y := by
      rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, ← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc,
        Category.assoc, hφ]
    have e2 := (T.univ S _ (hpowA (spMap (φ.comp (Ideal.Quotient.mkₐ R I))))).unique rfl e1.symm
    refine AlgHom.ext fun b => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I b
    exact DFunLike.congr_fun e2 a
  · intro S _ _
    refine ⟨(Algebra.ofId R S).comp (evbar 0), ?_⟩
    rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, hE]
    show spMap (Algebra.ofId R S) ≫ pt 0 = 1
    rw [h0, CategoryTheory.MonObj.comp_one]
  · have hm : ((spMap (Algebra.TensorProduct.includeLeft : (T.A ⧸ I) →ₐ[R] TensorProduct R (T.A ⧸ I) (T.A ⧸ I)) ≫
          spMap (Ideal.Quotient.mkₐ R I) ≫ T.y) *
        (spMap (Algebra.TensorProduct.includeRight : (T.A ⧸ I) →ₐ[R] TensorProduct R (T.A ⧸ I) (T.A ⧸ I)) ≫
          spMap (Ideal.Quotient.mkₐ R I) ≫ T.y)) ^ p = 1 := by
      rw [mul_pow, hpowc, hpowc, _root_.one_mul]
    obtain ⟨ψ0, hψ0⟩ := (T.univ _ _ hm).exists
    have hψI : ∀ a ∈ I, ψ0 a = 0 := by
      intro a ha
      refine hsep2 _ fun k1 k2 => ?_
      have e : spMap ((Λ k1 k2).comp ψ0) ≫ T.y = pt ((k1 : N) + k2) := by
        rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, hψ0, CategoryTheory.MonObj.comp_mul,
          ← Category.assoc (spMap (Λ k1 k2)) (spMap Algebra.TensorProduct.includeLeft),
          ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hΛL, hE,
          ← Category.assoc (spMap (Λ k1 k2)) (spMap Algebra.TensorProduct.includeRight),
          ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hΛR, hE, hpt.add]
      rw [← AlgHom.comp_apply, huniq _ _ e]
      exact (memI a).mp ha _ (K.add_mem k1.2 k2.2)
    intro S _ _ φ φ'
    have hLR : (Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)).comp
        Algebra.TensorProduct.includeRight = φ' := AlgHom.ext fun b => by simp
    refine ⟨(Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)).comp
      (Ideal.Quotient.liftₐ I ψ0 hψI), ?_⟩
    rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc,
      ← Category.assoc (spMap (Ideal.Quotient.liftₐ I ψ0 hψI)), ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp,
      Ideal.Quotient.liftₐ_comp, hψ0, CategoryTheory.MonObj.comp_mul]
    rw [← Category.assoc (spMap (Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)))
        (spMap Algebra.TensorProduct.includeLeft),
      ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Algebra.TensorProduct.lift_comp_includeLeft,
      ← Category.assoc (spMap (Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)))
        (spMap Algebra.TensorProduct.includeRight),
      ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hLR]
  · have hinv : ((spMap (Ideal.Quotient.mkₐ R I) ≫ T.y)⁻¹) ^ p = 1 := by rw [inv_pow, hu, inv_one]
    obtain ⟨ψ0, hψ0⟩ := (T.univ (T.A ⧸ I) _ hinv).exists
    have hψI : ∀ a ∈ I, ψ0 a = 0 := by
      intro a ha
      refine hsep1 _ fun k => ?_
      have e : spMap ((evbar k).comp ψ0) ≫ T.y = pt (-(k : N)) := by
        rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, hψ0, CategoryTheory.GrpObj.comp_inv,
          hE, hneg]
      rw [← AlgHom.comp_apply, huniq _ _ e]
      exact (memI a).mp ha _ (K.neg_mem k.2)
    intro S _ _ φ
    refine ⟨φ.comp (Ideal.Quotient.liftₐ I ψ0 hψI), ?_⟩
    rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc,
      ← Category.assoc (spMap (Ideal.Quotient.liftₐ I ψ0 hψI)), ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp,
      Ideal.Quotient.liftₐ_comp, hψ0, CategoryTheory.GrpObj.comp_inv, inv_mul_cancel]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsHopfOrder
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.torsion_points_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → (∃ AA : HopfOrder (C := C) R N, AA.carrier = torsFun C T pt) ∧ (∀ a : T.A, (∀ φ : T.A →ₐ[R] R, φ a = 0) → a = 0) ∧ (∀ x, ∃! φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt x) ∧ (∀ φ : T.A →ₐ[R] R, ∃ x, spMap φ ≫ T.y = pt x) ∧ ∀ x : N, p • x = 0 := by
  first | exact @PositivityTheory.HtPt.Rf.tors_hopf | exact PositivityTheory.HtPt.Rf.tors_hopf
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsIsogenyHopfOrderStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_isogeny_hopf_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ (T' : TorsRep G' p) (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'] (pt' : N' → (sp (R₀ := R) R ⟶ G')), IsTorsPts G' p pt' → ∀ j : G ⟶ G', IsMonHom j → ∃ (jN : N →+ N') (ψ : T'.A →ₐ[R] T.A), (∀ x, pt' (jN x) = pt x ≫ j) ∧ spMap ψ ≫ T'.y = T.y ≫ j ∧ ∀ g ∈ torsFun C T' pt', (fun x => g (jN x)) ∈ torsFun C T pt := by
  first | exact @GlobalTheory.CompanionTheory.Relay.torsion_points_isogeny_hopf_order | exact GlobalTheory.CompanionTheory.Relay.torsion_points_isogeny_hopf_order | (intros; apply GlobalTheory.CompanionTheory.Relay.torsion_points_isogeny_hopf_order <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnitRatioSameDivisorMultiplicities
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem unitRatio_divisor_cycle_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι), UnitRatio P f g → divSupp P f = divSupp P g ∧ ∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W :=
  @PositivityTheory.UnitarySelfGeneration.i_cycle

end GlobalTheory.CompanionTheory.Ar.Cmp
end

