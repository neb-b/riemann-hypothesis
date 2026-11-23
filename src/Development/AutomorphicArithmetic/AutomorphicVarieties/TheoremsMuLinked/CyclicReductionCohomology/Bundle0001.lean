module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0030
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0001
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DOSmall
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem dO_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.S6.norm_le_one_of_isIntegral l x hx

private theorem dO_small {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (y : A →+* PadicAlgCl l) (hle : ∀ x, ‖y x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ z ∈ maximalIdeal A ^ n, ‖y z‖ < ε := by
  have hl0 : ((l : ℕ) : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl : (l : A) ≠ 0 := fun h => hl0 (by simpa using congrArg y h)
  have hl1 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hl1
  refine ⟨e * n, fun z hz => ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hz
  have hd : (l : A) ^ n ∣ z := by
    refine Dvd.dvd.trans ?_ hz
    rw [pow_mul, hu]
    exact pow_dvd_pow_of_dvd (Units.mul_left_dvd.2 dvd_rfl) n
  obtain ⟨w, rfl⟩ := hd
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (hle w)) hn

private theorem dO_desc {O Q : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field Q] [Algebra O Q]
    (hinj : Function.Injective (algebraMap O Q)) {n : ℕ} (Y : Matrix (Fin n) (Fin n) Q) :
    ∃ (a : O) (Y0 : Matrix (Fin n) (Fin n) O), a ≠ 0 ∧ ∀ (e : O) (A B Z : Matrix (Fin n) (Fin n) O),
      Z.map (algebraMap O Q) = algebraMap O Q e • (A.map (algebraMap O Q) * Y * B.map (algebraMap O Q)) - Y →
      a • Z = e • (A * Y0 * B) - Y0 := by
  haveI : FaithfulSMul O Q := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  let N : Submodule O Q := Submodule.span O (insert 1 (Set.range fun p : Fin n × Fin n => Y p.1 p.2))
  haveI : Module.Finite O N := Module.Finite.span_of_finite O ((Set.finite_range _).insert _)
  let one : N := ⟨1, Submodule.subset_span (Set.mem_insert _ _)⟩
  let Yn : Fin n → Fin n → N := fun i j => ⟨Y i j, Submodule.subset_span (Set.mem_insert_of_mem _ ⟨(i, j), rfl⟩)⟩
  have h1 : one ≠ 0 := fun h => one_ne_zero (congrArg Subtype.val h)
  obtain ⟨π, hπ⟩ := Module.Projective.exists_dual_ne_zero O h1
  refine ⟨π one, Matrix.of fun i j => π (Yn i j), hπ, fun e A B Z h => ?_⟩
  ext i j
  have h2 : Z i j • one = e • (∑ k, ∑ m, (A i m * B k j) • Yn m k) - Yn i j := by
    apply Subtype.ext
    have := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul] at this
    simp only [one, Yn, Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_sum, Algebra.smul_def, mul_one, this, map_mul,
      Finset.sum_mul]
    congr 2
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
  have h3 := congrArg π h2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sub, map_sum, smul_eq_mul] at h3
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Matrix.of_apply, Finset.sum_mul]
  rw [mul_comm, h3]
  congr 2
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring

private theorem dO_pol {O : Type} [CommRing O] {n : ℕ} (P P' A A' B B' Y Z W : Matrix (Fin n) (Fin n) O) (s s' e a : O)
    (hP : P * P' = 1) (hP' : P' * P = 1) (hA : A * A' = 1) (hA' : A' * A = 1) (hs : s * s' = 1)
    (h1 : Aᵀ * P * B = s • P) (h2 : A'ᵀ * P * B' = s' • P) (hz : P * W = Zᵀ * P)
    (hc : a • Z = e • (A * Y * A') - Y) :
    a • W = e • (B * (P' * Yᵀ * P) * B') - P' * Yᵀ * P := by
  have e1 : P * B = s • (A'ᵀ * P) := by
    rw [← Matrix.mul_smul, ← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hA]; simp
  have e2 : P * B' = s' • (Aᵀ * P) := by
    rw [← Matrix.mul_smul, ← h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hA']; simp
  have e3 : P * (a • W) = P * (e • (B * (P' * Yᵀ * P) * B') - P' * Yᵀ * P) := by
    have f1 : P * (B * (P' * Yᵀ * P) * B') = (P * B) * P' * Yᵀ * (P * B') := by simp only [Matrix.mul_assoc]
    have f2 : P * (P' * Yᵀ * P) = Yᵀ * P := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP, Matrix.one_mul]
    have f3 : A'ᵀ * P * P' = A'ᵀ := by rw [Matrix.mul_assoc, hP, Matrix.mul_one]
    rw [Matrix.mul_smul, hz, ← Matrix.smul_mul, ← Matrix.transpose_smul, hc, Matrix.mul_sub, Matrix.mul_smul, f1, f2, e1, e2,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul s, hs, one_smul, f3]
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.mul_assoc]
  have := congrArg (P' * ·) e3
  simpa only [← Matrix.mul_assoc, hP', Matrix.one_mul] using this

private theorem dO_sym {O : Type} [CommRing O] {n : ℕ} (P P' Y : Matrix (Fin n) (Fin n) O)
    (hP : P * P' = 1) (hP' : P' * P = 1) (hs : Pᵀ = P ∨ Pᵀ = -P) :
    P * (Y + P' * Yᵀ * P) = (Y + P' * Yᵀ * P)ᵀ * P := by
  have f2 : P * (P' * Yᵀ * P) = Yᵀ * P := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP, Matrix.one_mul]
  have f0 : P'ᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hP, Matrix.transpose_one]
  have f3 : (P' * Yᵀ * P)ᵀ * P = P * Y := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rcases hs with h | h
    · rw [h] at f0
      rw [f0, h, Matrix.mul_one]
    · rw [h, Matrix.mul_neg, neg_eq_iff_eq_neg] at f0
      rw [f0, h]; simp
  rw [Matrix.mul_add, Matrix.transpose_add, Matrix.add_mul, f2, f3, add_comm]

theorem UpperTheory.V.Th.detO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (c : Coef l) (n : ℕ) (y : Pt G0.frame c.O n) (S : Set G0.G₀), l ≠ 2 → DetQ G0.frame c.O (pushRep (algebraMap c.O (Qbar l)) y.ρ) (GeneralLinearGroup.map (algebraMap c.O (Qbar l)) y.P) S → DetO y S := by
  intro l _ L G0 c n y S _ hQ z hcont hcoc hpol htr
  set f := algebraMap c.O (Qbar l) with hf
  have hinj : Function.Injective f := Subtype.val_injective
  have hle : ∀ x : c.O, ‖f x‖ ≤ 1 := fun x =>
    dO_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val)
  have hm : ∀ g, mat (pushRep f y.ρ) g = (mat y.ρ g).map f := fun g => rfl
  have hP : ((GeneralLinearGroup.map f y.P : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
    (y.P : Matrix (Fin n) (Fin n) c.O).map f := rfl
  have he : ∀ g : G0.G₀, ((G0.frame.eps c.O (Qbar l) g : (Qbar l)ˣ) : Qbar l) =
    f (algebraMap ℤ_[l] c.O (G0.ε g : ℤ_[l])) := fun g => rfl
  obtain ⟨Y, hY⟩ := hQ (fun g => (z g).map f) (by
      refine continuous_matrix fun a b => continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
      obtain ⟨k, hk⟩ := dO_small f hle hε
      filter_upwards [(hcont a b k).eventually_eq g] with g' hg'
      rw [dist_eq_norm, Matrix.map_apply, Matrix.map_apply, ← map_sub]
      exact hk _ (Ideal.Quotient.eq.1 hg'))
    (fun g g' => by
      rw [hcoc, hm, hm, he, Matrix.map_add _ (map_add f), ← Matrix.map_mul, ← Matrix.map_mul]
      congr 1
      all_goals (ext i j; simp))
    (fun g => by rw [hP, ← Matrix.map_mul, hpol, Matrix.map_mul, Matrix.transpose_map])
    (fun σ hσ k => by
      rw [← map_pow, hm, ← Matrix.map_mul, ← AddMonoidHom.map_trace, map_pow, htr σ hσ k, map_zero])
  obtain ⟨a, Y0, ha, hY0⟩ := dO_desc hinj Y
  have hc : ∀ g : G0.G₀, a • z g = algebraMap ℤ_[l] c.O (G0.ε g : ℤ_[l]) • (mat y.ρ g * Y0 * mat y.ρ g⁻¹) - Y0 :=
    fun g => hY0 _ _ _ _ (hY g)
  have hP1 : (y.P : Matrix (Fin n) (Fin n) c.O) * (y.P⁻¹ : GL (Fin n) c.O) = 1 := Units.mul_inv _
  have hP2 : ((y.P⁻¹ : GL (Fin n) c.O) : Matrix (Fin n) (Fin n) c.O) * y.P = 1 := Units.inv_mul _
  refine ⟨a + a, Y0 + (y.P⁻¹ : GL (Fin n) c.O) * Y0ᵀ * y.P, ?_, dO_sym _ _ _ hP1 hP2 y.sgn, fun g => ?_⟩
  · rw [← two_mul]
    exact mul_ne_zero two_ne_zero ha
  have hcc : G0.frame.conj (G0.frame.conj g) = g := by
    apply Subtype.ext
    have h2 : G0.c⁻¹ = G0.c := inv_eq_of_mul_eq_one_right G0.c_sq
    show G0.c * (G0.c * g * G0.c⁻¹) * G0.c⁻¹ = g
    rw [h2, ← mul_assoc, ← mul_assoc, G0.c_sq, one_mul, mul_assoc, G0.c_sq, mul_one]
  have hε : G0.ε (G0.frame.conj g : G0.G₀) = G0.ε g := by
    show G0.ε (G0.c * g * G0.c⁻¹) = _
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have h5 := dO_pol _ _ _ _ _ _ Y0 _ _ _ _ _ a hP1 hP2 (by rw [← map_mul, mul_inv_cancel, map_one])
    (by rw [← map_mul, inv_mul_cancel, map_one])
    (by rw [← Units.val_mul, ← mul_zpow, ← map_mul, mul_inv_cancel, map_one, _root_.one_zpow, Units.val_one])
    (y.form (G0.frame.conj g)) (y.form (G0.frame.conj g)⁻¹) (hpol (G0.frame.conj g)) (hc (G0.frame.conj g))
  rw [map_inv, hcc, hε] at h5
  rw [add_smul, Matrix.mul_add, Matrix.add_mul, smul_add]
  conv_lhs => rw [hc g]; arg 2; rw [← hc g, h5]
  abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualZ
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.dualZ :
    ∀ (N : ℕ) [NeZero N] (V : Type) [AddCommGroup V] [Module (ZMod N) V] [Finite V], Nat.card (Module.Dual (ZMod N) V) = Nat.card V ∧ (∀ v : V, (∀ f : Module.Dual (ZMod N) V, f v = 0) → v = 0) ∧ ∀ (V' : Type) [AddCommGroup V'] [Module (ZMod N) V'] [Finite V'] (b : V →+ V' →+ ZMod N), (∀ x, (∀ y, b x y = 0) → x = 0) → (∀ y, (∀ x, b x y = 0) → y = 0) → Function.Bijective fun y : V' => ((b.flip y).toZModLinearMap N : Module.Dual (ZMod N) V) := by
  intro N _ V _ _ _
  have sep : ∀ {W : Type} [AddCommGroup W] [Module (ZMod N) W] (w : W),
      (∀ f : Module.Dual (ZMod N) W, f w = 0) → w = 0 := by
    intro W _ _ w hw
    by_contra hne
    obtain ⟨f, -, hf⟩ := KStar.Selmer.exists_form_ne_zero (⊥ : Submodule (ZMod N) W)
      (z := w) (by simpa using hne)
    exact hf (hw f)
  have fin : ∀ {W : Type} [AddCommGroup W] [Module (ZMod N) W] [Finite W],
      Finite (Module.Dual (ZMod N) W) := by
    intro W _ _ _
    apply Nat.finite_of_card_ne_zero
    rw [KStar.Selmer.card_dual]
    exact Nat.card_pos.ne'
  refine ⟨KStar.Selmer.card_dual, fun v hv => sep v hv, ?_⟩
  intro V' _ _ _ b hl hr
  haveI := fin (W := V)
  haveI := fin (W := V')
  have inj : Function.Injective fun y : V' =>
      ((b.flip y).toZModLinearMap N : Module.Dual (ZMod N) V) := by
    intro y y' h
    have h' : ∀ x, b x (y - y') = 0 := by
      intro x
      have := LinearMap.congr_fun h x
      simp only [AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.flip_apply] at this
      rw [map_sub, this, sub_self]
    exact sub_eq_zero.mp (hr _ h')
  have inj' : Function.Injective fun x : V =>
      ((b x).toZModLinearMap N : Module.Dual (ZMod N) V') := by
    intro x x' h
    have h' : ∀ y, b (x - x') y = 0 := by
      intro y
      have := LinearMap.congr_fun h y
      simp only [AddMonoidHom.coe_toZModLinearMap] at this
      rw [map_sub, AddMonoidHom.sub_apply, this, sub_self]
    exact sub_eq_zero.mp (hl _ h')
  have c2 := Nat.card_le_card_of_injective _ inj'
  rw [KStar.Selmer.card_dual] at c2
  refine inj.bijective_of_nat_card_le ?_
  rw [KStar.Selmer.card_dual]
  exact c2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.FinZK
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem fin_step {A : Type} [AddCommGroup A] (l : ℕ) (h1 : {a : A | l • a = 0}.Finite) (j : ℕ) :
    {a : A | l ^ j • a = 0}.Finite := by
  induction j with
  | zero =>
    apply Set.Finite.subset (Set.finite_singleton 0)
    intro a ha
    simp only [Set.mem_setOf_eq, pow_zero, one_smul] at ha
    simp [ha]
  | succ j ih =>
    have hsub : {a : A | l ^ (j + 1) • a = 0} ⊆ (fun a => l • a) ⁻¹' {a : A | l ^ j • a = 0} := by
      intro a ha
      simp only [Set.mem_setOf_eq, Set.mem_preimage] at ha ⊢
      rw [smul_smul, ← pow_succ]; exact ha
    refine Set.Finite.subset (Set.Finite.preimage' ih ?_) hsub
    intro b _
    by_cases hne : ((fun a : A => l • a) ⁻¹' {b}).Nonempty
    · obtain ⟨a0, ha0⟩ := hne
      refine Set.Finite.subset (h1.image (fun x => x + a0)) ?_
      intro a ha
      refine ⟨a - a0, ?_, by simp⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha ha0
      simp only [Set.mem_setOf_eq, smul_sub, ha, ha0, sub_self]
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]; exact Set.finite_empty

theorem UpperTheory.V.Th.finZK :
    ∀ (l : ℕ) [Fact l.Prime] (k : ℕ) (R Γ M : Type) [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M), PhiCond Γ l → LC ρ → (∀ m : M, l ^ k • m = 0) → Finite (Zl ρ) := by
  intro l _ k R Γ M _ _ _ _ _ _ _ _ ρ hphi hlc htors
  classical
  let M1 : Submodule R M :=
    { carrier := {m | l • m = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun r {m} hm => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_comm, hm, smul_zero] }
  have hst : ∀ g, ∀ m ∈ M1, ρ g m ∈ M1 := by
    intro g m hm
    show l • ρ g m = 0
    rw [← map_nsmul, show l • m = 0 from hm, map_zero]
  let ρ1 : Representation R Γ M1 :=
    { toFun := fun g => (ρ g).restrict (hst g)
      map_one' := by
        refine LinearMap.ext fun m => Subtype.ext ?_
        simp
      map_mul' := fun g h => by
        refine LinearMap.ext fun m => Subtype.ext ?_
        simp }
  have hlc1 : LC ρ1 := fun m => IsLocallyConstant.desc _ Subtype.val (hlc m.1) Subtype.val_injective
  have htors1 : ∀ m : M1, l • m = 0 := by
    intro m
    have h : l • (m : M) = 0 := m.2
    apply Subtype.ext
    simpa using h
  have hfin1 : Finite (Zl ρ1) := (finZ l R Γ M1 ρ1 hphi hlc1 htors1).1
  have hl : {a : Zl ρ | l • a = 0}.Finite := by
    have hval : ∀ a : {a : Zl ρ // l • a = 0}, ∀ g, (a.1 : Γ → M) g ∈ M1 := by
      intro a g
      have h := congrArg (fun x : Zl ρ => (x : Γ → M) g) a.2
      show l • (a.1 : Γ → M) g = 0
      simpa using h
    have hmemF : ∀ a : {a : Zl ρ // l • a = 0},
        (fun g => (⟨(a.1 : Γ → M) g, hval a g⟩ : M1)) ∈ Zl ρ1 := by
      intro a
      obtain ⟨hlc', hcoc⟩ := (mem_Zl ρ).mp a.1.2
      exact (mem_Zl ρ1).mpr ⟨IsLocallyConstant.desc _ Subtype.val hlc' Subtype.val_injective,
        fun g h => Subtype.ext (hcoc g h)⟩
    let F : {a : Zl ρ // l • a = 0} → Zl ρ1 := fun a => ⟨_, hmemF a⟩
    have hF : Function.Injective F := by
      intro a b hab
      apply Subtype.ext; apply Subtype.ext; funext g
      have := congrFun (congrArg Subtype.val hab) g
      exact congrArg Subtype.val this
    haveI : Finite ↥{a : Zl ρ | l • a = 0} := Finite.of_injective F hF
    exact Set.toFinite _
  have hk := fin_step l hl k
  have huniv : {a : Zl ρ | l ^ k • a = 0} = Set.univ := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    apply Subtype.ext
    funext g
    simp [htors]
  rw [huniv] at hk
  exact Set.finite_univ_iff.mp hk
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.FixCnt
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem fixBd_abs {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Finite (IsLocalRing.ResidueField A)] {E S : Type} [AddCommGroup E] [Module A E] [Module.Finite A E]
    (f : S → E →ₗ[A] E) : ∃ C : ℕ, ∀ (m : ℕ) (E' : Type) [AddCommGroup E'] [Module A E'] (r : E →ₗ[A] E')
      (T : Set E'), LinearMap.ker r = IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E) →
      (∀ Y ∈ T, ∃ Z, r Z = Y ∧ ∀ s, r (f s Z) = 0) →
      T.ncard ≤ Nat.card (IsLocalRing.ResidueField A) ^
        (m * Module.finrank A (⨅ s, LinearMap.ker (f s) : Submodule A E) + C) := by
  obtain ⟨e, he⟩ := UpperTheory.V.AlgebraTools.lemma_B f
  refine ⟨e, fun m E' _ _ r T hk hT => ?_⟩
  have h := he m
  set N := (⨅ s, (IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E)).comap (f s)).map
    (IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E)).mkQ with hN
  have hne : Module.length A N ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) h
  have hfin : Finite N := (UpperTheory.V.AlgebraTools.card_eq_pow_length (A := A) (X := N)).1.2 hne
  have hc := (UpperTheory.V.AlgebraTools.card_eq_pow_length (A := A) (X := N)).2 hfin
  have hsub : T ⊆ ((IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E)).liftQ r hk.ge) '' (SetLike.coe N) := by
    intro Y hY
    obtain ⟨Z, rfl, hZ⟩ := hT Y hY
    refine ⟨_, Submodule.mem_map_of_mem (r := Z) ?_, rfl⟩
    rw [Submodule.mem_iInf]
    intro s
    rw [Submodule.mem_comap, ← hk]
    exact hZ s
  have hf : (SetLike.coe N).Finite := Set.toFinite _
  refine (Set.ncard_le_ncard hsub (hf.image _)).trans ((Set.ncard_image_le hf).trans ?_)
  have : (SetLike.coe N).ncard = Nat.card N := rfl
  rw [this, hc]
  refine Nat.pow_le_pow_right Nat.card_pos ?_
  rw [mul_comm]
  exact ENat.toNat_le_of_le_coe h

theorem UpperTheory.V.Th.fixCnt :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (S : Type) (Φ : S → Matrix (Fin n) (Fin n) O →ₗ[O] Matrix (Fin n) (Fin n) O), ∃ C : ℕ, ∀ m, {Y : Mm O n m | ∃ Y', red m Y' = Y ∧ ∀ s, red m (Φ s Y') = 0}.ncard ≤ Nat.card (ResidueField O) ^ (m * Module.finrank O (⨅ s, LinearMap.ker (Φ s) : Submodule O (Matrix (Fin n) (Fin n) O)) + C) := by
  intro l _ O _ _ _ hO _ n S Φ
  obtain ⟨-, hfin, -⟩ := hO
  obtain ⟨C, hC⟩ := fixBd_abs Φ
  refine ⟨C, fun m => hC m (Mm O n m) (Ideal.Quotient.mkₐ O (maximalIdeal O ^ m)).toLinearMap.mapMatrix _ ?_ fun Y hY => hY⟩
  ext Z
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    rw [Matrix.matrix_eq_sum_single Z]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have h1 : Z i j ∈ maximalIdeal O ^ m := Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun h i) j)
    have e : Matrix.single i j (Z i j) = Z i j • Matrix.single i j (1 : O) := by simp
    rw [e]
    exact Submodule.smul_mem_smul h1 Submodule.mem_top
  · intro h
    refine Submodule.smul_induction_on h (fun a ha Y _ => ?_) fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero]
    ext i j
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ ha)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.LocCntCongr
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.locCntCongr :
    ∀ (l : ℕ) [Fact l.Prime] (D D' : Type) [Group D] [TopologicalSpace D] [Group D'] [TopologicalSpace D'] (α : D ≃ₜ* D') (ε : D →* ℤ_[l]ˣ) (ε' : D' →* ℤ_[l]ˣ) (d : ℕ), (∀ g, ε g = ε' (α g)) → LocCnt D' ε' d → LocCnt D ε d := by
  intro l _ D D' _ _ _ _ α ε ε' d hε H k hk R M M' _ _ _ _ _ _ _ ρ ρ' b hLC hb
  let β : D' →* D := α.symm.toMulEquiv.toMonoidHom
  let σ : Representation R D' M := ρ.comp β
  let σ' : Representation R D' M' := ρ'.comp β
  have hσ : ∀ g, σ g = ρ (α.symm g) := fun _ => rfl
  have hσ' : ∀ g, σ' g = ρ' (α.symm g) := fun _ => rfl
  have h1 : LC σ := fun m => (hLC m).comp_continuous α.symm.continuous
  have h2 : DualPair k ε' σ σ' b := by
    refine ⟨hb.left, hb.right, fun g x y => ?_⟩
    rw [hσ, hσ', hb.equiv]
    simp only [hε, ContinuousMulEquiv.apply_symm_apply]
  obtain ⟨hf, hc⟩ := H k hk R M M' σ σ' b h1 h2
  let e : Zl ρ ≃ Zl σ :=
    { toFun := fun z => ⟨fun g => z.1 (α.symm g), z.2.1.comp_continuous α.symm.continuous, fun g h => by
        beta_reduce
        rw [map_mul, z.2.2, hσ]⟩
      invFun := fun z => ⟨fun g => z.1 (α g), z.2.1.comp_continuous α.continuous, fun g h => by
        beta_reduce
        rw [map_mul, z.2.2, hσ, ContinuousMulEquiv.symm_apply_apply]⟩
      left_inv := fun z => Subtype.ext (funext fun g => by simp)
      right_inv := fun z => Subtype.ext (funext fun g => by simp) }
  have hi : ρ'.invariants = σ'.invariants := by
    ext m
    simp only [Representation.mem_invariants, hσ']
    exact ⟨fun h g => h _, fun h g => by simpa using h (α g)⟩
  exact ⟨Finite.of_equiv _ e.symm, by rw [Nat.card_congr e, hc, hi]⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts
section
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.omFacts :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O], (l ≠ 2 → IsUnit (2 : O)) ∧ ∀ m : ℕ, Finite (Om O m) ∧ Nat.card (Om O m) = Nat.card (ResidueField O) ^ m ∧ (∀ x : Om O m, l ^ m • x = 0) ∧ (∀ a : ℤ_[l], PadicInt.toZModPow m a = 1 → algebraMap O (Om O m) (algebraMap ℤ_[l] O a) = 1) ∧ ∀ (Γ : Type) [TopologicalSpace Γ] (f : Γ → O), AdicCont (maximalIdeal O) f → IsLocallyConstant fun g => algebraMap O (Om O m) (f g) := by
  intro l hl O _ _ _ hO _
  obtain ⟨-, hf, hc⟩ := hO
  have hlm : (l : O) ∈ maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  have hpow : ∀ m : ℕ, ((l : Om O m)) ^ m = 0 := fun m => by
    rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal O ^ m)), ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hlm m)
  refine ⟨fun h2 => ?_, fun m => ⟨?_, ?_, fun x => ?_, fun a ha => ?_, fun Γ _ f hf => hf m⟩⟩
  · by_contra hu
    have h : (2 : O) ∈ maximalIdeal O := hu
    rw [← IsLocalRing.residue_eq_zero_iff, map_ofNat] at h
    have h' : ((2 : ℕ) : ResidueField O) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ResidueField O) l] at h'
    exact h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 h')
  · haveI : Finite (O ⧸ maximalIdeal O) := hf
    exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) m
  · have := cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field O) (i := m)
    rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at this
    exact this
  · rw [nsmul_eq_mul, Nat.cast_pow, hpow, zero_mul]
  · have h : a - 1 ∈ RingHom.ker (PadicInt.toZModPow (p := l) m) := by
      rw [RingHom.mem_ker, RingHom.map_sub, ha, map_one, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at h
    obtain ⟨b, hb⟩ := h
    have e : a = 1 + b * (l : ℤ_[l]) ^ m := by rw [hb]; ring
    rw [e]
    simp only [map_add (f := _), map_one, map_mul, map_pow, map_natCast, hpow, mul_zero, add_zero]
end

