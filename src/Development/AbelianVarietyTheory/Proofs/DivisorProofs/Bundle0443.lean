module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0392
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimQuotientMinimalPrimeOverL
section
namespace GlobalTheory

universe u

theorem trdeg_quotient_eq_of_mem_minimalPrimes_span (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (k : Type u) [Field k] [Algebra R k]
    (hk : Function.Surjective (algebraMap R k)) {ϖ : R} (hϖ0 : ϖ ≠ 0)
    (hker : RingHom.ker (algebraMap R k) = Ideal.span {ϖ})
    {A : Type u} [CommRing A] [IsDomain A] [Algebra R A] [Algebra.FiniteType R A]
    [FaithfulSMul R A] {q : Ideal A}
    (hq : q ∈ (Ideal.span {algebraMap R A ϖ}).minimalPrimes)
    [Algebra k (A ⧸ q)] [IsScalarTower R k (A ⧸ q)] :
    Algebra.trdeg k (A ⧸ q) = Algebra.trdeg R A := by
  have hqp := hq.1.1
  have : Algebra.FiniteType k (A ⧸ q) := .of_restrictScalars_finiteType R k _
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k (A ⧸ q)
  choose x hx using fun i : Fin s ↦ Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let φ : (MvPolynomial (Fin s) R) →ₐ[R] A := MvPolynomial.aeval x
  have hφ (r : (MvPolynomial (Fin s) R)) :
      Ideal.Quotient.mk q (φ r) = g (MvPolynomial.map (algebraMap R k) r) := by
    have : (Ideal.Quotient.mk q).comp φ.toRingHom =
        g.toRingHom.comp (MvPolynomial.map (algebraMap R k)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [φ, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
          Function.comp_apply, MvPolynomial.algHom_C, MvPolynomial.map_C]
        rw [← IsScalarTower.algebraMap_apply]
        rfl
      · intro i
        simp [φ, hx]
    exact congr($this r)
  have hmem (r : (MvPolynomial (Fin s) R)) : φ r ∈ q ↔ MvPolynomial.C ϖ ∣ r := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, map_eq_zero_iff g hg, ← RingHom.mem_ker,
      MvPolynomial.ker_map, hker, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  have hϖA : algebraMap R A ϖ ≠ 0 := by
    intro h
    exact hϖ0 ((FaithfulSMul.algebraMap_injective R A) (h.trans (map_zero _).symm))
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hnu : ¬ IsUnit (MvPolynomial.C ϖ : (MvPolynomial (Fin s) R)) := fun h ↦ hqp.ne_top <|
      Ideal.eq_top_of_isUnit_mem _ ((hmem _).mpr dvd_rfl) (h.map φ)
    obtain ⟨n, a, ha, rfl⟩ := WfDvdMonoid.max_power_factor' hr0 hnu
    rw [map_mul, map_pow, MvPolynomial.algHom_C, mul_eq_zero] at hr
    rcases hr with hr | hr
    · exact hϖA (pow_eq_zero_iff'.mp hr).1
    · exact ha ((hmem a).mp (hr ▸ q.zero_mem))
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin s) R) A :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) R) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Algebra.FiniteType (MvPolynomial (Fin s) R) A :=
    .of_restrictScalars_finiteType R (MvPolynomial (Fin s) R) A
  let := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) (A ⧸ q) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) k) (A ⧸ q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) (A ⧸ q) := ⟨hint⟩
  have : Algebra.QuasiFiniteAt (MvPolynomial (Fin s) R) q := by
    refine quasiFiniteAt_of_isolated (MvPolynomial (Fin s) R) A q
      (fun q' hq' h hle ↦ ?_) (fun q' hq' h hle ↦ ?_)
    · refine hle.antisymm (hq.2 ⟨hq', ?_⟩ hle)
      rw [Ideal.span_singleton_le_iff_mem]
      have : (MvPolynomial.C ϖ : (MvPolynomial (Fin s) R)) ∈ q'.under (MvPolynomial (Fin s) R) :=
        h.ge ((hmem _).mpr dvd_rfl)
      have : φ (MvPolynomial.C ϖ) ∈ q' := this
      simpa using this
    · have : q'.map (Ideal.Quotient.mk q) = ⊥ := by
        refine Ideal.eq_bot_of_comap_eq_bot (R := MvPolynomial (Fin s) k) (eq_bot_iff.mpr ?_)
        intro y hy
        obtain ⟨r, rfl⟩ := MvPolynomial.map_surjective _ hk y
        have hy : g (MvPolynomial.map (algebraMap R k) r) ∈ q'.map (Ideal.Quotient.mk q) := hy
        rw [← hφ, Ideal.mem_quotient_iff_mem hle] at hy
        have : φ r ∈ q := h.le (show r ∈ q'.under (MvPolynomial (Fin s) R) from hy)
        rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, map_eq_zero_iff g hg] at this
        exact this
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at this
      exact this.antisymm hle
  have := isAlgebraic_of_quasiFiniteAt (MvPolynomial (Fin s) R) A q
  rw [trdeg_eq_of_isAlgebraic_top k (MvPolynomial (Fin s) k),
    trdeg_eq_of_isAlgebraic_top R (MvPolynomial (Fin s) R) A,
    MvPolynomial.trdeg_of_isDomain, MvPolynomial.trdeg_of_isDomain]

theorem ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime (A : Type) [CommRing A]
    [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] (l : ℕ) [Fact l.Prime] (q : Ideal A)
    [q.IsPrime] (hq : q ∈ (Ideal.span {(l : A)}).minimalPrimes) (d : ℕ)
    (hd : Algebra.trdeg ℤ A = d) : ringKrullDim (A ⧸ q) = d := by
  have hk : Function.Surjective (algebraMap ℤ (ZMod l)) := ZMod.intCast_surjective
  have hker : RingHom.ker (algebraMap ℤ (ZMod l)) = Ideal.span {(l : ℤ)} := by
    rw [algebraMap_int_eq]; exact ZMod.ker_intCastRingHom l
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (by rw [algebraMap_int_eq]; exact Int.cast_injective)
  have hq' : q ∈ (Ideal.span {algebraMap ℤ A (l : ℤ)}).minimalPrimes := by simpa using hq
  have hlq : (l : A) ∈ q := hq.1.2 (Ideal.mem_span_singleton_self _)
  have hle : RingHom.ker (algebraMap ℤ (ZMod l)) ≤ RingHom.ker (algebraMap ℤ (A ⧸ q)) := by
    rw [hker, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker,
      IsScalarTower.algebraMap_apply ℤ A (A ⧸ q), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    simpa using hlq
  let := ((algebraMap ℤ (ZMod l)).liftOfSurjective hk ⟨_, hle⟩).toAlgebra
  have : IsScalarTower ℤ (ZMod l) (A ⧸ q) := IsScalarTower.of_algebraMap_eq fun x ↦
    (RingHom.liftOfSurjective_comp_apply _ hk ⟨_, hle⟩ x).symm
  have : Algebra.FiniteType (ZMod l) (A ⧸ q) := .of_restrictScalars_finiteType ℤ _ _
  refine ringKrullDim_eq_of_trdeg_eq (ZMod l) _ ?_
  rw [trdeg_quotient_eq_of_mem_minimalPrimes_span ℤ (ZMod l) hk hl0 hker hq', hd]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerRelationBoundaryKernelGeneratorSumZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit

namespace GlobalTheory.EtC.KummerSplit


set_option maxHeartbeats 1000000 in
theorem res_resGen_of_pow (q : ℕ) [NeZero q] {W V : Scheme.{0}} (k : W ⟶ V) (ζ ξ : Prim q Γ(V, ⊤)) (a : (ZMod q)ˣ)
    (h : k.appTop.hom ξ.1 = k.appTop.hom ζ.1 ^ (a : ZMod q).val) :
    Sec.res k (resGen 1 ξ) = (a : ZMod q).val • resGen 1 (ζ.map k.appTop.hom) := by
  have e1 : Sec.res k (resGen 1 ξ) = resGen 1 (ξ.map k.appTop.hom) := by
    unfold resGen
    rw [sec_res_map, (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.1]
  rw [e1]
  have e2 := (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.2.1 W (ζ.map k.appTop.hom) (ξ.map k.appTop.hom) a h
  simp only [zpow_one] at e2
  unfold resGen
  rw [e2]
  exact map_nsmul ((resι (ZMod q) (tw q 1)).hom.app (op W)).hom _ _

end GlobalTheory.EtC.KummerSplit

namespace GlobalTheory.EtC.KummerSplit


set_option maxHeartbeats 1000000 in
theorem relation_kernel (q : ℕ) [NeZero q] (V : Scheme.{0}) (c : (tripP q).obj (op V) →₀ ULift.{1} (ZMod q))
    (hc : (c.sum fun x r => r • (freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).tgt) -
      freeGen (ZMod q) unitsP V (unitsP.mk (tripP.get x).src))) = 0) :
    (c.sum fun x r => r • resGen 1 (tripP.get x).root) = 0 := by
  classical
  set d : unitsP.obj (op V) →₀ ULift.{1} (ZMod q) :=
    c.sum fun x r => Finsupp.single (unitsP.mk (tripP.get x).tgt) r - Finsupp.single (unitsP.mk (tripP.get x).src) r
    with hd_def
  have hd : (d.sum fun u r => r • freeGen (ZMod q) unitsP V u) = 0 := by
    rw [← Finsupp.linearCombination_apply, hd_def, map_finsuppSum, ← hc]
    refine Finsupp.sum_congr fun x _ => ?_
    rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, smul_sub]
  have hloc := (GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination (ZMod q) unitsP V).2 d hd
  by_cases hc0 : c = 0
  · simp [hc0]
  obtain ⟨x₀, -⟩ := Finsupp.support_nonempty_iff.2 hc0
  have hroots : ∀ x : ↥c.support, Loc V fun _ g => ∃ a : (ZMod q)ˣ,
      g.appTop.hom (tripP.get x.1).root.1 = g.appTop.hom (tripP.get x₀).root.1 ^ (a : ZMod q).val :=
    fun x => (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.1 (tripP.get x₀).root (tripP.get x.1).root
  have hall := loc_calculus.2.2.2.2.2.1 V (↥c.support) (fun x _ g => ∃ a : (ZMod q)ˣ,
      g.appTop.hom (tripP.get x.1).root.1 = g.appTop.hom (tripP.get x₀).root.1 ^ (a : ZMod q).val) hroots
  have hboth := loc_calculus.2.2.1 V _ _ hloc hall
  apply sec_eq_zero_of_loc
  refine loc_calculus.2.1 V _ _ hboth ?_
  rintro W k ⟨hkd, hka⟩
  rw [res_sum]
  by_cases hW : IsEmpty W
  · exact sec_eq_zero_of_loc _ _ (loc_calculus.2.2.2.2.2.2 W _)
  rw [not_isEmpty_iff] at hW
  haveI : Nontrivial Γ(W, ⊤) := @Scheme.component_nontrivial W ⊤ ⟨⟨hW.some, trivial⟩⟩
  choose a ha using hka
  let a' : (tripP q).obj (op V) → ℕ := fun x =>
    if h : x ∈ c.support then ((a ⟨x, h⟩ : (ZMod q)ˣ) : ZMod q).val else 0
  have hax : ∀ x (hx : x ∈ c.support), a' x = ((a ⟨x, hx⟩ : (ZMod q)ˣ) : ZMod q).val := fun x hx => dif_pos hx
  have hsum : (c.sum fun x r => r • Sec.res k (resGen 1 (tripP.get x).root)) =
      (c.sum fun x r => r * ((a' x : ℕ) : ULift.{1} (ZMod q))) •
        resGen 1 ((tripP.get x₀).root.map k.appTop.hom) := by
    rw [Finsupp.sum, Finsupp.sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [res_resGen_of_pow q k (tripP.get x₀).root _ (a ⟨x, hx⟩) (ha ⟨x, hx⟩), ← hax x hx, mul_smul,
      Nat.cast_smul_eq_nsmul]
  have halg := GlobalTheory.T.primitiveRoot_free_action_finsupp_sum q Γ(W, ⊤) ((tripP.get x₀).root.map k.appTop.hom) ((tripP q).obj (op V)) c.support
    (fun x => c x) a'
    (fun x => Units.map k.appTop.hom.toMonoidHom (tripP.get x).src)
    (fun x => Units.map k.appTop.hom.toMonoidHom (tripP.get x).tgt) ?_ ?_
  · rw [hsum]
    suffices h0 : (c.sum fun x r => r * ((a' x : ℕ) : ULift.{1} (ZMod q))) = 0 by rw [h0, zero_smul]
    apply ULift.ext
    rw [Finsupp.sum]
    refine Eq.trans ?_ halg
    induction c.support using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ULift.add_down, ih]; simp
  · intro x hx
    rw [hax x hx]
    change k.appTop.hom ((tripP.get x).tgt : Γ(V, ⊤)) =
      k.appTop.hom (tripP.get x₀).root.1 ^ _ * k.appTop.hom ((tripP.get x).src : Γ(V, ⊤))
    rw [(tripP.get x).tgt_eq, map_mul, ha ⟨x, hx⟩]
  · rw [hd_def, Finsupp.sum, Finsupp.mapDomain_finsetSum] at hkd
    simp only [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, unitsP.map_mk] at hkd
    exact hkd

end GlobalTheory.EtC.KummerSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDegreeEqSumOfScalarSplit
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

namespace GlobalTheory.Nef

theorem degLine_eq_sum_of_split : ∀ (k E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field E] [Algebra k E], IsFF k E → ∀ (m n : ℕ) (G : Place k E → Matrix (Fin 2) (Fin 2) E), admitted G → ∀ (S : Place k E → Matrix (Fin n) (Fin n) E) (q : Fin n → E) (c : E) (w : Fin m → Fin 2 → E), c ≠ 0 → (∀ j, w j ≠ 0) → (∀ P, ordVec P ((S P).mulVec q) = ord P c + ∑ j, ordVec P ((G P).mulVec (w j))) → degLine S q = ∑ j, degLine G (w j) := by
  intro k E _ _ _ _ _ hE m n G hG S q c w hc hw hpt
  obtain ⟨hcfin, hcsum⟩ := _root_.GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero k E hE c hc
  have hcs : (Function.support fun P : Place k E => ord P c).Finite :=
    hcfin.subset fun P hP => by
      intro h1
      apply hP
      simp [ord, h1]
  have hjs : ∀ j, (Function.support fun P : Place k E => ordVec P ((G P).mulVec (w j))).Finite := fun j =>
    ((_root_.GlobalTheory.Nef.lineFin k E hE 2 G hG).2 (w j) (hw j)).1.subset fun P hP => by
      intro h1
      apply hP
      show ordVec P ((G P).mulVec (w j)) = 0
      rw [ordVec, h1]
      simp
  have hss : (Function.support fun P : Place k E => ∑ j, ordVec P ((G P).mulVec (w j))).Finite :=
    (Set.finite_iUnion fun j => hjs j).subset fun P hP => by
      obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
      exact Set.mem_iUnion.2 ⟨j, hj⟩
  unfold degLine
  rw [finsum_congr hpt, finsum_add_distrib hcs hss, hcsum, zero_add]
  exact finsum_sum_comm _ _ fun j _ => hjs j

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDegreeGeOfTwistedSection
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

set_option autoImplicit false

namespace GlobalTheory.Nef.LineBound

theorem le_ordVec {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v : Place k F) (x : Fin n → F)
    (hx : x ≠ 0) (m : ℤ) (h : ∀ i, v.1 (x i) ≤ WithZero.exp (-m)) : m ≤ ordVec v x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  have h0 : v.1 (x i) ≠ 0 := (Valuation.ne_zero_iff _).2 hi
  have h1 : v.1 (x i) ≤ nrm v x := Finset.le_sup (f := fun j => v.1 (x j)) (Finset.mem_univ i)
  have h2 : nrm v x ≠ 0 := fun h' => h0 (le_antisymm (h' ▸ h1) zero_le)
  have h3 : nrm v x ≤ WithZero.exp (-m) := Finset.sup_le fun j _ => h j
  have h4 := (WithZero.log_le_log h2 WithZero.exp_ne_zero).2 h3
  rw [WithZero.log_exp] at h4
  unfold ordVec
  omega

end GlobalTheory.Nef.LineBound

theorem GlobalTheory.Nef.degLine_ge_of_twist : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F → ∀ (n : ℕ) (h : Place k F → Matrix (Fin n) (Fin n) F), admitted h → ∀ (v₀ : Place k F) (π : F), π ≠ 0 → ord v₀ π = 1 → ∀ (e : ℤ) (p : Fin n → F), p ≠ 0 → (∀ (v : Place k F) (i : Fin n), v.1 ((twistAt v₀ (π ^ (-e)) h v).mulVec p i) ≤ 1) → e ≤ degLine h p := by
  intro k F _ _ _ _ _ hF n h hA v₀ π hπ hord e p hp hle
  classical
  obtain ⟨-, hw⟩ := _root_.GlobalTheory.Nef.lineFin k F hF n h hA
  obtain ⟨hfin, hne⟩ := hw p hp
  set d : Place k F → ℤ := fun v => ordVec v ((h v).mulVec p) with hd
  have hsupp : Function.support d ⊆ {v : Place k F | nrm v ((h v).mulVec p) ≠ 1} := fun v hv => by
    intro h1
    apply hv
    simp only [hd, ordVec, h1, WithZero.log_one, neg_zero]
  have hnn : ∀ v, v ≠ v₀ → 0 ≤ d v := fun v hv => by
    refine GlobalTheory.Nef.LineBound.le_ordVec v _ (hne v) 0 fun i => ?_
    have := hle v i
    rw [twistAt_of_ne _ _ _ _ hv] at this
    simpa using this
  have hv₀ : e ≤ d v₀ := by
    refine GlobalTheory.Nef.LineBound.le_ordVec v₀ _ (hne v₀) e fun i => ?_
    have h1 := hle v₀ i
    rw [twistAt_self, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_zpow₀] at h1
    have hπ0 : v₀.1 π ≠ 0 := (Valuation.ne_zero_iff _).2 hπ
    have hπv : v₀.1 π = WithZero.exp (-1) := by
      rw [← WithZero.exp_log hπ0]
      congr 1
      unfold ord at hord
      omega
    rw [hπv, ← WithZero.exp_zsmul, smul_eq_mul] at h1
    set y := v₀.1 ((h v₀).mulVec p i)
    have : y = WithZero.exp (-e) * (WithZero.exp (-e * -1) * y) := by
      rw [← mul_assoc, ← WithZero.exp_add]
      ring_nf
      simp
    rw [this]
    calc WithZero.exp (-e) * (WithZero.exp (-e * -1) * y) ≤ WithZero.exp (-e) * 1 := by gcongr
      _ = WithZero.exp (-e) := mul_one _
  have hs : Function.support d ⊆ ↑(hfin.toFinset ∪ {v₀}) := fun v hv => by
    simp only [Finset.coe_union, Set.Finite.coe_toFinset, Finset.coe_singleton]
    exact Or.inl (hsupp hv)
  show e ≤ ∑ᶠ v, d v
  rw [finsum_eq_sum_of_support_subset _ hs, ← Finset.add_sum_erase _ _ (show v₀ ∈ hfin.toFinset ∪ {v₀} by simp)]
  have : 0 ≤ ∑ x ∈ (hfin.toFinset ∪ {v₀}).erase v₀, d x :=
    Finset.sum_nonneg fun v hv => hnn v (Finset.ne_of_mem_erase hv)
  omega
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulEigenPartProjectionMatrixEqScalar
section
open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

open scoped Pointwise

theorem prod_mul_eq_zero_of_mem_span {S X ι : Type} [CommRing S] [Fintype ι] (N : ι → X → S) (W : S)
    (h : ∀ c : ι → X, (∏ j, N j (c j)) * W = 0) (f : ι → S)
    (hf : ∀ j, f j ∈ Ideal.span (Set.range (N j))) : (∏ j, f j) * W = 0 := by
  classical
  have hmem : (∏ j, f j) ∈ Ideal.span (∏ j, Set.range (N j)) := by
    rw [← Ideal.prod_span]
    exact Ideal.prod_mem_prod fun j _ => hf j
  refine Submodule.span_induction (p := fun x _ => x * W = 0) ?_ ?_ ?_ ?_ hmem
  · intro x hx
    obtain ⟨e, he, rfl⟩ := (Set.mem_fintype_prod (fun j => Set.range (N j)) x).1 hx
    choose c hc using he
    simpa [hc] using h c
  · simp
  · intro x y _ _ hx hy; rw [add_mul, hx, hy, add_zero]
  · intro a x _ hx; rw [smul_eq_mul, mul_assoc, hx, mul_zero]

end GlobalTheory.UPel.HT.LieLin.RankIdeal

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

theorem mapMatrix_algebraMap_fin {B K : Type} [CommRing B] [CommRing K] (g : B →+* K) {n : ℕ} (x : B) :
    g.mapMatrix (algebraMap B (Matrix (Fin n) (Fin n) B) x) = algebraMap K (Matrix (Fin n) (Fin n) K) (g x) := by
  ext k l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
  split_ifs <;> simp

theorem map_mul_projMat_eq_smul (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (B : Type) [CommRing B] (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K]
    (g : B →+* K) :
    lieIdeal b βB M ≤ RingHom.ker g → ∀ (i : Fin D.a) (c : 𝓞 D.F),
      (M c).map g * (projMat b βB M i).map g = g (βB (b.t i c)) • (projMat b βB M i).map g := by
  intro hI i c
  classical
  set M' : 𝓞 D.F →+* Matrix (Fin n) (Fin n) K := g.mapMatrix.comp M with hM'
  have hcomm : ∀ a ∈ Set.range M', ∀ a' ∈ Set.range M', a * a' = a' * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; rw [← map_mul, ← map_mul, mul_comm]
  let S := Algebra.adjoin K (Set.range M')
  let : IsMulCommutative S := Algebra.isMulCommutative_adjoin K fun a ha a' ha' _ =>
    hcomm a ha a' ha'
  let : CommRing S := open scoped IsMulCommutative in inferInstance
  let m : 𝓞 D.F → S := fun x => ⟨M' x, Algebra.subset_adjoin ⟨x, rfl⟩⟩
  let sc : R → S := fun r => algebraMap K S (g (βB r))
  let N : Fin D.a → 𝓞 D.F → S := fun j x => m x - sc (b.t j x)
  let WS : S := m D.ω - sc ((D.tr : R) - b.ρ)
  let α : Fin D.a → S := fun j => (comaxC b i j).sum fun x r => sc r * N j x
  let PS : S := (List.ofFn fun j => if j = i then 1 else α j).prod * (sc (uInv b) * WS)
  have hsc : ∀ r, S.val (sc r) = g.mapMatrix (algebraMap B (Matrix (Fin n) (Fin n) B) (βB r)) := by
    intro r; rw [AlgHom.commutes, mapMatrix_algebraMap_fin]
  have hm : ∀ x, S.val (m x) = g.mapMatrix (M x) := fun _ => rfl
  have hN : ∀ j x, S.val (N j x) =
      g.mapMatrix (M x - algebraMap B (Matrix (Fin n) (Fin n) B) (βB (b.t j x))) := by
    intro j x; simp only [N, map_sub, hm, hsc]
  have hW : S.val WS = g.mapMatrix (M D.ω - algebraMap B (Matrix (Fin n) (Fin n) B) (βB ((D.tr : R) - b.ρ))) := by
    simp only [WS, map_sub, hm, hsc]
  have hα : ∀ j, S.val (α j) = g.mapMatrix (alphaMat b βB M i j) := by
    intro j; simp only [α, alphaMat, Finsupp.sum, map_sum, map_mul, hsc, hN]
  have hP : S.val PS = g.mapMatrix (projMat b βB M i) := by
    have hfactor (j : Fin D.a) : S.val (if j = i then 1 else α j) =
        g.mapMatrix (if j = i then 1 else alphaMat b βB M i j) := by
      by_cases hj : j = i <;> simp [hj, hα]
    simp only [PS, projMat, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, hsc, hW,
      hfactor]
  have hlie : ∀ c' : Fin D.a → 𝓞 D.F, (∏ j, N j (c' j)) * WS = 0 := by
    intro c'
    have h0 : g.mapMatrix (lieMat b βB M c') = 0 := by
      ext k l
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]
      exact hI (Ideal.subset_span ⟨c', k, l, rfl⟩)
    rw [← List.prod_ofFn]
    refine (map_eq_zero_iff S.val Subtype.val_injective).1 ?_
    rw [← h0]
    simp only [lieMat, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, hN, hW]
  have hkey : N i c * PS = 0 := by
    have hf : ∀ j, (if j = i then N i c else α j) ∈ Ideal.span (Set.range (N j)) := by
      intro j; split_ifs with hj
      · subst hj; exact Ideal.subset_span ⟨c, rfl⟩
      · exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨x, rfl⟩)
    have h1 := prod_mul_eq_zero_of_mem_span N WS hlie _ hf
    have h2 : N i c * (∏ j, if j = i then (1 : S) else α j) = ∏ j, if j = i then N i c else α j := by
      rw [show (∏ j, if j = i then N i c else α j) =
          ∏ j, ((if j = i then N i c else 1) * if j = i then 1 else α j) from
          Finset.prod_congr rfl fun j _ => by split_ifs <;> simp, Finset.prod_mul_distrib, Finset.prod_ite_eq']
      simp
    simp only [PS, List.prod_ofFn]
    rw [← mul_assoc, h2, mul_left_comm, h1, mul_zero]
  have h3 := congrArg S.val hkey
  rw [map_mul, map_zero, hN, hP, map_sub, mapMatrix_algebraMap_fin, sub_mul] at h3
  change g.mapMatrix (M c) * g.mapMatrix (projMat b βB M i) = _
  rw [Algebra.smul_def, ← sub_eq_zero]
  exact h3

end GlobalTheory.UPel.HT.LieLin.RankIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFMulPosPrincipal
section
open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.IdeleModule
variable {E : Type} [Field E] [NumberField E]

theorem coord_ne (y : (Af E)ˣ) (v : HeightOneSpectrum (𝓞 E)) : Valued.v ((y : Af E) v) ≠ 0 := by
  have := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).1 v
  simpa using this

theorem modF_finite (y : (Af E)ˣ) : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) =>
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (WithZero.log (Valued.v ((y : Af E) v)))).Finite := by
  have := (FiniteAdeleRing.isUnit_iff.1 y.isUnit).2
  rw [Filter.eventually_cofinite] at this
  refine this.subset fun v hv h1 => hv ?_
  simp [h1]

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 E)) : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  positivity

theorem modF_mul (y y' : (Af E)ˣ) : modF (y * y') = modF y * modF y' := by
  unfold modF
  rw [← finprod_mul_distrib (modF_finite y) (modF_finite y')]
  refine finprod_congr fun v => ?_
  have : ((y * y' : (Af E)ˣ) : Af E) v = (y : Af E) v * (y' : Af E) v := rfl
  rw [this, map_mul, WithZero.log_mul (coord_ne y v) (coord_ne y' v), zpow_add₀ (absNorm_pos v).ne']

theorem modF_pos (y : (Af E)ˣ) : 0 < modF y :=
  finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => zpow_pos (absNorm_pos v) _

theorem modF_princ (k : Eˣ) :
    modF (Units.map (algebraMap E (Af E)).toMonoidHom k) = (|((Algebra.norm ℚ (k : E) : ℚ) : ℝ)|)⁻¹ := by
  have h := FinitePlace.prod_eq_inv_abs_norm (K := E) k.ne_zero
  push_cast at h
  rw [← h, ← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := E)).symm]
  unfold modF
  refine finprod_congr fun v => ?_
  rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding']
  have h0 : v.valuation E (k : E) ≠ 0 := by simp
  have h1 : Valued.v (((Units.map (algebraMap E (Af E)).toMonoidHom k : (Af E)ˣ) : Af E) v) = v.valuation E (k : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : E)
  rw [h1, WithZeroMulInt.toNNReal_neg_apply _ h0]
  push_cast
  congr 1

end GlobalTheory.CMVal.IdeleModule

theorem GlobalTheory.CMVal.modF_mul_pos_principal : ∀ (E : Type) [Field E] [NumberField E], (∀ y y' : (Af E)ˣ, modF (y * y') = modF y * modF y') ∧ (∀ y : (Af E)ˣ, 0 < modF y) ∧ ∀ k : Eˣ, modF (Units.map (algebraMap E (Af E)).toMonoidHom k) = (|(Algebra.norm ℚ (k : E) : ℝ)|)⁻¹ :=
  fun _ _ _ => ⟨IdeleModule.modF_mul, IdeleModule.modF_pos, IdeleModule.modF_princ⟩
end

