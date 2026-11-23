module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarEtaleIntegralClosureRootUniformizerStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abhyankar_etale_integralClosure_root_uniformizer : ∀ (S S₁ K K₁ L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁] [Field L] [Algebra K L] [Algebra S L]
    [IsScalarTower S K L] [FiniteDimensional K L] [Algebra.IsSeparable K L],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ q) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] L)) := by
  first | (exact @GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer) | (exact GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer) | (intros; apply GlobalTheory.AbhyankarBC.etale_integralClosure_of_root_uniformizer  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicExtendScalarsZmodOfFlatBoundedBelow
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.FlatExtAcyc

variable {R : Type} [CommRing R]

lemma sres_comp {F : Shv R} {U V W : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) (s : Sec F U) :
    Sec.res k (Sec.res g s) = Sec.res (k ≫ g) s := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

lemma sres_map {F G : Shv R} (a : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map a x) = Sec.map a (Sec.res g x) := by
  have := a.hom.naturality g.op
  exact congrArg (fun t => t.hom x) this.symm

lemma sres_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 :=
  (F.obj.map g.op).hom.map_zero

lemma nsmul_self_eq_zero (q : ℕ) {F : Shv (ZMod q)} {U : Scheme.{0}} (z : Sec F U) : q • z = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by ext; simp
  rw [this, zero_smul]

end GlobalTheory.EtC.FlatExtAcyc


open GlobalTheory.EtC.FlatExtAcyc in
theorem GlobalTheory.EtC.flatExtAcyc.main : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (K : Cx (ZMod Q)) (a : ℤ) [K.IsStrictlyGE a], (∀ n, FlatS (K.X n)) → K.Acyclic → (extCx (ZMod.castHom hq (ZMod q)) K).Acyclic := by
  intro Q q _ hq K a _ hflat hK
  have hqe : q * (Q / q) = Q := Nat.mul_div_cancel' hq
  have hKloc : ∀ (n : ℤ) (U : Scheme.{0}) (b : Sec (K.X n) U), Sec.map (K.d n (n + 1)) b = 0 → Loc U fun V g => ∃ c : Sec (K.X (n - 1)) V, Sec.map (K.d (n - 1) n) c = Sec.res g b := by
    intro n U b hb
    have hex : (K.sc' (n - 1) n (n + 1)).Exact := (K.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).1 (hK n)
    exact ((GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally _ _).1 hex) U b hb
  have hz : ∀ n, n < a → ∀ (U : Scheme.{0}) (x : Sec (K.X n) U), x = 0 := by
    intro n hn U x
    have hZ : IsZero (K.X n) := K.isZero_of_isStrictlyGE a n hn
    have e1 : 𝟙 (K.X n) = 0 := hZ.eq_of_src _ _
    have h1 : Sec.map (𝟙 (K.X n)) x = x := rfl
    rw [← h1, e1]; rfl
  have hQ : ∀ (n : ℤ) (U : Scheme.{0}) (y : Sec (K.X n) U), (q * (Q / q)) • y = 0 := by
    intro n U y
    rw [hqe, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod Q))]
    have : ((Q : ℕ) : ULift.{1} (ZMod Q)) = 0 := by ext; simp
    rw [this, zero_smul]
  have hst := GlobalTheory.T.etaleComplex_staircase_locally_exact (ZMod Q) q (Q / q) K a hz hQ
    (fun n U x hx => GlobalTheory.T.locallyFlatEtaleSheaf_locally_divisible Q q (Q / q) hqe (K.X n) (hflat n) U x hx)
    (fun n U x hx => GlobalTheory.T.locallyFlatEtaleSheaf_locally_divisible Q (Q / q) q (by rw [mul_comm]; exact hqe) (K.X n) (hflat n) U x hx) hKloc
  intro n
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp), GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]

  suffices H : ∀ (U : Scheme.{0}) (z : Sec ((extSh (ZMod.castHom hq (ZMod q))).obj (K.X n)) U),
      Sec.map ((extSh (ZMod.castHom hq (ZMod q))).map (K.d n (n + 1))) z = 0 →
      Loc U fun V g => ∃ b : Sec ((extSh (ZMod.castHom hq (ZMod q))).obj (K.X (n - 1))) V,
        Sec.map ((extSh (ZMod.castHom hq (ZMod q))).map (K.d (n - 1) n)) b = Sec.res g z from H
  intro U z hzz
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.1 U _ ?_
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ (GlobalTheory.T.etaleSheafExtendScalars_zmod_section_locally_tmul Q q hq (K.X n) U z) ?_
  rintro V g ⟨x, hx⟩
  have hdx : extSh.sec (ZMod.castHom hq (ZMod q)) (K.X (n + 1)) V (Sec.map (K.d n (n + 1)) x) = 0 := by
    rw [← extSh.sec_map, hx, ← sres_map, hzz, sres_zero]
  have hloc := GlobalTheory.T.etaleSheafExtendScalars_zmod_kernel_locally_multiple Q q hq (K.X (n + 1)) V _ hdx
  have hloc' : Loc V fun W k => ∃ y : Sec (K.X (n + 1)) W, Sec.map (K.d n (n + 1)) (Sec.res k x) = q • y := by
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 V _ _ hloc ?_
    rintro W k ⟨y, hy⟩
    exact ⟨y, by rw [← sres_map, hy]⟩
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 V _ _ (hst n V x hloc') ?_
  rintro W k ⟨u, y, hy⟩
  refine ⟨extSh.sec (ZMod.castHom hq (ZMod q)) (K.X (n - 1)) W u, ?_⟩
  rw [extSh.sec_map, ← sres_comp, ← hx, extSh.sec_res, hy, map_add (f := _), map_nsmul, nsmul_self_eq_zero, add_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleAdelicMatrixFamilyOrdersFinite
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem lineFin : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → {v : Place k F | ord v (g v).det ≠ 0}.Finite ∧ ∀ w : Fin n → F, w ≠ 0 → {v : Place k F | nrm v ((g v).mulVec w) ≠ 1}.Finite ∧ ∀ v, (g v).mulVec w ≠ 0 := by
  intro k F _ _ _ _ _ hFF n g hg
  obtain ⟨hdet, hfin⟩ := hg
  refine ⟨hfin.subset ?_, fun w hw => ⟨?_, fun v h => hw (Matrix.eq_zero_of_mulVec_eq_zero (hdet v) h)⟩⟩
  · intro v hv hu
    apply hv
    simp [ord, hu.2]
  · let S : Set (Place k F) := {v | ¬ Unimod v (g v)} ∪
      ⋃ i ∈ {i : Fin n | w i ≠ 0}, {v : Place k F | v.1 (w i) ≠ 1}
    have hS : S.Finite := hfin.union (Set.Finite.biUnion (Set.toFinite _)
      fun i hi => ((_root_.GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero k F hFF (w i) hi).1))
    refine hS.subset fun v hv => ?_
    by_contra hvS
    simp only [S, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_not, not_exists] at hvS
    obtain ⟨hu, hw1⟩ := hvS
    apply hv
    rw [(((_root_.GlobalTheory.Nef.ord_calculus k F v).2.2.2.2.2.2.2.2.1) n (g v) w hu)]
    obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
      by_contra h; push_neg at h; exact hw (funext h)
    have h1 : ∀ i, v.1 (w i) ≤ 1 := by
      intro i
      by_cases hi : w i = 0
      · simp [hi]
      · exact le_of_eq (hw1 i hi)
    apply le_antisymm
    · exact Finset.sup_le fun i _ => h1 i
    · have := Finset.le_sup (f := fun i => v.1 (w i)) (Finset.mem_univ i0)
      have e : v.1 (w i0) = 1 := hw1 i0 hi0
      rw [e] at this; exact this

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSchemeRepresentingQcQsFiniteTypeStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertScheme_representing_qc_qs_finiteType : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), QuasiCompact (R.homEquiv (𝟙 H)).1 ∧ QuasiSeparated (R.homEquiv (𝟙 H)).1 ∧ LocallyOfFiniteType (R.homEquiv (𝟙 H)).1 := by
  first | (exact @GlobalTheory.HilbAff.representing_qc_qs_loft) | (exact GlobalTheory.HilbAff.representing_qc_qs_loft) | (intros; apply GlobalTheory.HilbAff.representing_qc_qs_loft <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyCupDegreeZeroSupportCochainStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alexanderWhitney_cup_degree_zero_support_cochain : ∀ {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {S : Spc} {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj S) I n) (β : Cochain ((chains R).obj S) J m) (γ : Cochain ((chains R).obj S) K k), μ.IsAW hk α β γ → (∀ (s : ℕ) (t : ℤ) (h : -(s : ℤ) + n = t) (U : Scheme.{0}) (x : Sx S s U), 0 < s → ev α s t h U x = 0) → ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx S N U), ev γ N w h U x = μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) := by
  first | (exact @GlobalTheory.AWFront.ev_of_front) | (exact GlobalTheory.AWFront.ev_of_front) | (intros; apply GlobalTheory.AWFront.ev_of_front  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyHomotopyFormula
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alexander_whitney_homotopy_formula : ∀ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) → (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) → ∃ K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b', ∀ a b a' b' : ℕ, a' + b' = a + b → G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' + ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b' := by
  first | (exact @GlobalTheory.EZ.HTot.htot) | (exact GlobalTheory.EZ.HTot.htot) | (intros; apply GlobalTheory.EZ.HTot.htot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraCoefficientsRestrictionBijective
section
open CategoryTheory GlobalTheory.CxCoh GlobalTheory.CatCoh

set_option autoImplicit false

namespace GlobalTheory.CxCoh.AlgDict

universe u

variable {R : Type} [CommRing R] {C : Type u} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem singleComplex_mem_cocyclesOne_iff_algebraFunctor (c : (Cx.single (Coef.ofAlg F)).T1) :
    c ∈ (Cx.single (Coef.ofAlg F)).Z1 ↔ c.1 ∈ Z1 F := by
  change (Cx.single (Coef.ofAlg F)).D1 c = 0 ↔ _
  constructor
  · intro h T T' T'' φ ψ
    have := congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst h) T) T') T'') φ) ψ
    change mp F ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ = 0 at this
    linear_combination -this
  · intro h
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext T T' T'' φ ψ
    change mp F ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ = 0
    rw [h φ ψ]; ring

theorem singleComplex_mem_cocyclesTwo_iff_algebraFunctor (c : (Cx.single (Coef.ofAlg F)).T2) :
    c ∈ (Cx.single (Coef.ofAlg F)).Z2 ↔ c.1 ∈ Z2 F :=
  ⟨fun h _ _ _ _ φ ψ χ ↦ h.1 _ _ _ _ φ ψ χ,
    fun h ↦ ⟨fun _ _ _ _ φ ψ χ ↦ h φ ψ χ, fun _ _ _ _ _ ↦ Subsingleton.elim _ _,
      fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ Subsingleton.elim _ _⟩⟩

variable {C' : Type u} [Category.{0} C'] (G : C' ⥤ C)

theorem h1_injective (hi : Function.Injective (CoefMap.restrict F G).pull1) :
    Function.Injective ((Cx.single (Coef.ofAlg F)).resMap G).h1 := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hz : z.1.1 ∈ Z1 F := (singleComplex_mem_cocyclesOne_iff_algebraFunctor F z.1).1 z.2
  change (QuotientAddGroup.mk (((Cx.single (Coef.ofAlg F)).resMap G).z1 z) :
    ((Cx.single (Coef.ofAlg F)).res G).H1) = 0 at hc
  rw [QuotientAddGroup.eq_zero_iff] at hc
  obtain ⟨g, hg⟩ := hc
  have h0 : (CoefMap.restrict F G).pull1 (H1.mk F ⟨z.1.1, hz⟩) = (CoefMap.restrict F G).pull1 0 := by
    rw [map_zero, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
    exact ⟨g, congrArg Prod.fst hg⟩
  obtain ⟨g', hg'⟩ := H1.mk_eq_zero.1 (hi h0)
  rw [QuotientAddGroup.eq_zero_iff]
  exact ⟨g', Prod.ext hg' (Subsingleton.elim _ _)⟩

theorem h1_surjective (hs : Function.Surjective (CoefMap.restrict F G).pull1) :
    Function.Surjective ((Cx.single (Coef.ofAlg F)).resMap G).h1 := by
  intro c'
  obtain ⟨z', rfl⟩ := QuotientAddGroup.mk_surjective c'
  have hz' : z'.1.1 ∈ Z1 (G ⋙ F) := (singleComplex_mem_cocyclesOne_iff_algebraFunctor (G ⋙ F) z'.1).1 z'.2
  obtain ⟨c, hc⟩ := hs (H1.mk _ ⟨z'.1.1, hz'⟩)
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hc
  obtain ⟨g, hg⟩ := hc
  refine ⟨QuotientAddGroup.mk ⟨(f.1, fun _ ↦ 0), (singleComplex_mem_cocyclesOne_iff_algebraFunctor F _).2 f.2⟩, ?_⟩
  change (QuotientAddGroup.mk (((Cx.single (Coef.ofAlg F)).resMap G).z1 _) :
    ((Cx.single (Coef.ofAlg F)).res G).H1) = QuotientAddGroup.mk z'
  rw [QuotientAddGroup.eq]
  refine ⟨-g, Prod.ext ?_ (Subsingleton.elim _ _)⟩
  rw [map_neg]
  funext T T' φ
  have := congrFun (congrFun (congrFun hg T) T') φ
  change -(d0 (G ⋙ F) g T T' φ) = -(f.1 _ _ (G.map φ)) + z'.1.1 T T' φ
  rw [this]
  change -((f.1 _ _ (G.map φ)) - z'.1.1 T T' φ) = _
  abel

theorem h2_injective (hi : Function.Injective (CoefMap.restrict F G).pull2) :
    Function.Injective ((Cx.single (Coef.ofAlg F)).resMap G).h2 := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hz : z.1.1 ∈ Z2 F := (singleComplex_mem_cocyclesTwo_iff_algebraFunctor F z.1).1 z.2
  change (QuotientAddGroup.mk (((Cx.single (Coef.ofAlg F)).resMap G).z2 z) :
    ((Cx.single (Coef.ofAlg F)).res G).H2) = 0 at hc
  rw [QuotientAddGroup.eq_zero_iff] at hc
  obtain ⟨g, hg⟩ := hc
  have h0 : (CoefMap.restrict F G).pull2 (H2.mk F ⟨z.1.1, hz⟩) = (CoefMap.restrict F G).pull2 0 := by
    rw [map_zero, CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]
    exact ⟨g.1, congrArg Prod.fst hg⟩
  obtain ⟨g', hg'⟩ := H2.mk_eq_zero.1 (hi h0)
  rw [QuotientAddGroup.eq_zero_iff]
  exact ⟨(g', fun _ ↦ 0), Prod.ext hg' (Subsingleton.elim _ _)⟩

theorem h2_surjective (hs : Function.Surjective (CoefMap.restrict F G).pull2) :
    Function.Surjective ((Cx.single (Coef.ofAlg F)).resMap G).h2 := by
  intro c'
  obtain ⟨z', rfl⟩ := QuotientAddGroup.mk_surjective c'
  have hz' : z'.1.1 ∈ Z2 (G ⋙ F) := (singleComplex_mem_cocyclesTwo_iff_algebraFunctor (G ⋙ F) z'.1).1 z'.2
  obtain ⟨c, hc⟩ := hs (H2.mk _ ⟨z'.1.1, hz'⟩)
  obtain ⟨f, rfl⟩ := H2.mk_surjective F c
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hc
  obtain ⟨g, hg⟩ := hc
  refine ⟨QuotientAddGroup.mk ⟨(f.1, fun _ _ _ ↦ 0, fun _ ↦ 0), (singleComplex_mem_cocyclesTwo_iff_algebraFunctor F _).2 f.2⟩, ?_⟩
  change (QuotientAddGroup.mk (((Cx.single (Coef.ofAlg F)).resMap G).z2 _) :
    ((Cx.single (Coef.ofAlg F)).res G).H2) = QuotientAddGroup.mk z'
  rw [QuotientAddGroup.eq]
  refine ⟨(-g, fun _ ↦ 0), Prod.ext ?_ (Subsingleton.elim _ _)⟩
  funext T T' T'' φ ψ
  have := congrFun (congrFun (congrFun (congrFun (congrFun hg T) T') T'') φ) ψ
  change d1 (G ⋙ F) (-g) T T' T'' φ ψ = -(f.1 _ _ _ (G.map φ) (G.map ψ)) + z'.1.1 T T' T'' φ ψ
  rw [map_neg, Pi.neg_apply, Pi.neg_apply, Pi.neg_apply, Pi.neg_apply, Pi.neg_apply, this]
  change -((f.1 _ _ _ (G.map φ) (G.map ψ)) - z'.1.1 T T' T'' φ ψ) = _
  abel

end GlobalTheory.CxCoh.AlgDict

theorem GlobalTheory.CxCoh.single_algebra_restriction_bijective : ∀ (R : Type) [CommRing R] (C C' : Type 1) [Category.{0} C]
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C),
    Function.Bijective (CoefMap.restrict F G).pull1 → Function.Bijective (CoefMap.restrict F G).pull2 →
    ((Cx.single (Coef.ofAlg F)).resMap G).PullbackBijectiveDegreesOneTwo :=
  fun _ _ _ _ _ _ F G h1 h2 ↦
    ⟨⟨AlgDict.h1_injective F G h1.1, AlgDict.h1_surjective F G h1.2⟩,
      AlgDict.h2_injective F G h2.1, AlgDict.h2_surjective F G h2.2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproximationQuotientsAgree
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approximation_quotients_agree : ∀ (q : ℕ) (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂] (f : B) (I J : Ideal B) (n i : ℤ) (y : Ht q (sp B) n i), IsCoprime I J → (∀ a : A₁, ∃ b : B, a - algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f}) → (∀ b : B, algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f} ↔ b ∈ I) → (∀ a : A₂, ∃ b : B, a - algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f}) → (∀ b : B, algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f} ↔ b ∈ J) → pull _ (spMap (algebraMap B A₁)) _ _ y = 0 → pull _ (spMap (algebraMap B A₂)) _ _ y = 0 → (∀ a : A₁ × A₂, ∃ b : B, a - algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f}) ∧ (∀ b : B, algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f} ↔ b ∈ I ⊓ J) ∧ pull _ (spMap (algebraMap B (A₁ × A₂))) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.ProdStep.prodStep) | (exact GlobalTheory.EtC.ProdStep.prodStep) | (intros; apply GlobalTheory.EtC.ProdStep.prodStep  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

abbrev secEvalFun (R : Type) [CommRing R] (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙ (evaluation _ _).obj (op U)

theorem injectiveResolution_sections_degree_zero_kernel (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) :
    (∀ w : Sec ((injectiveResolution F).cocomplex.X 0) U,
      Sec.map ((injectiveResolution F).cocomplex.d 0 1) w = 0 →
        ∃ a : Sec F U, Sec.map ((injectiveResolution F).ι.f 0) a = w) ∧
    Function.Injective (Sec.map ((injectiveResolution F).ι.f 0) (U := U)) := by
  set I := injectiveResolution F
  have hlim := KernelFork.mapIsLimit _ I.isLimitKernelFork (secEvalFun R U)
  let S : ShortComplex (ModuleCat.{1} (ULift.{1} R)) :=
    ShortComplex.mk ((secEvalFun R U).map (I.ι.f 0)) ((secEvalFun R U).map (I.cocomplex.d 0 1))
      (by rw [← Functor.map_comp, I.ι_f_zero_comp_complex_d, Functor.map_zero])
  have hS : S.Exact := S.exact_of_f_is_kernel hlim
  refine ⟨fun w hw => (ShortComplex.moduleCat_exact_iff S).1 hS w hw, ?_⟩
  have : Mono ((secEvalFun R U).map (I.ι.f 0)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

theorem chosenInjectiveResolutionAugmentation_eq_iota_comp (R : Type) [CommRing R] (F : Shv R) :
    resι R F = (injectiveResolution F).ι.f 0 ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).inv := by
  simp [resι, InjectiveResolution.ι'_f_zero]
  rfl

theorem chosenInjectiveResolutionEtaleSheaf_d_zero_one_eq (R : Type) [CommRing R] (F : Shv R) :
    (res R F).d 0 1 = ((injectiveResolution F).cochainComplexXIso 0 0 rfl).hom ≫
      (injectiveResolution F).cocomplex.d 0 1 ≫ ((injectiveResolution F).cochainComplexXIso 1 1 rfl).inv :=
  InjectiveResolution.cochainComplex_d _ 0 1 0 1 rfl rfl

theorem chosenInjectiveResolutionEtaleSheaf_exactAt_ne_zero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n ≠ 0) : (res R F).ExactAt n := by
  have h : ((CochainComplex.singleFunctor (Shv R) 0).obj F).ExactAt n :=
    HomologicalComplex.exactAt_single_obj (ComplexShape.up ℤ) 0 F n hn
  exact (quasiIsoAt_iff_exactAt (injectiveResolution F).ι' n h).1 inferInstance

theorem resSec (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) :
    (∀ z : Sec ((res R F).X 0) U, Sec.map ((res R F).d 0 1) z = 0 ↔ ∃ a : Sec F U, Sec.map (resι R F) a = z) ∧
    Function.Injective (Sec.map (resι R F) (U := U)) ∧
    (∀ (m n k : ℤ), 0 < n → m + 1 = n → ∀ z : Sec ((res R F).X n) U, n + 1 = k →
      Sec.map ((res R F).d n k) z = 0 →
        Loc U fun V g => ∃ y : Sec ((res R F).X m) V, Sec.map ((res R F).d m n) y = Sec.res g z) ∧
    ∀ n : ℤ, n < 0 → Subsingleton (Sec ((res R F).X n) U) := by
  obtain ⟨hker, hinj⟩ := injectiveResolution_sections_degree_zero_kernel R F U
  set I := injectiveResolution F
  set e0 := I.cochainComplexXIso 0 0 rfl
  set e1 := I.cochainComplexXIso 1 1 rfl
  have hι : ∀ a : Sec F U, Sec.map (resι R F) a = Sec.map e0.inv (Sec.map (I.ι.f 0) a) := by
    intro a; rw [chosenInjectiveResolutionAugmentation_eq_iota_comp]; rfl
  have hd : ∀ z : Sec ((res R F).X 0) U,
      Sec.map ((res R F).d 0 1) z = Sec.map e1.inv (Sec.map (I.cocomplex.d 0 1) (Sec.map e0.hom z)) := by
    intro z; rw [chosenInjectiveResolutionEtaleSheaf_d_zero_one_eq]; rfl
  have he0 : ∀ z : Sec ((res R F).X 0) U, Sec.map e0.inv (Sec.map e0.hom z) = z := by
    intro z; change Sec.map (e0.hom ≫ e0.inv) z = z; rw [e0.hom_inv_id]; rfl
  have he0' : ∀ w : Sec (I.cocomplex.X 0) U, Sec.map e0.hom (Sec.map e0.inv w) = w := by
    intro w; change Sec.map (e0.inv ≫ e0.hom) w = w; rw [e0.inv_hom_id]; rfl
  have he1 : ∀ w : Sec (I.cocomplex.X 1) U, Sec.map e1.hom (Sec.map e1.inv w) = w := by
    intro w; change Sec.map (e1.inv ≫ e1.hom) w = w; rw [e1.inv_hom_id]; rfl
  refine ⟨fun z => ⟨fun hz => ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hd] at hz
    have hz' : Sec.map (I.cocomplex.d 0 1) (Sec.map e0.hom z) = 0 := by
      have := congrArg (Sec.map e1.hom) hz
      rw [he1] at this
      exact this.trans (map_zero (e1.hom.hom.app (op U)).hom)
    obtain ⟨a, ha⟩ := hker _ hz'
    exact ⟨a, by rw [hι, ha, he0]⟩
  · rintro ⟨a, rfl⟩
    rw [hd, hι, he0']
    change Sec.map e1.inv (Sec.map (I.ι.f 0 ≫ I.cocomplex.d 0 1) a) = 0
    rw [I.ι_f_zero_comp_complex_d]
    exact map_zero _
  · intro a b hab
    rw [hι, hι] at hab
    have := congrArg (Sec.map e0.hom) hab
    rw [he0', he0'] at this
    exact hinj this
  · intro m n k hn hmn z hnk hz
    have hex : ((res R F).sc' m n k).Exact :=
      (HomologicalComplex.exactAt_iff' _ m n k (by simp; omega) (by simp; omega)).1
        (chosenInjectiveResolutionEtaleSheaf_exactAt_ne_zero R F n (by omega))
    exact (GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally R ((res R F).sc' m n k)).1 hex U z hz
  · intro n hn
    haveI : (res R F).IsStrictlyGE 0 := (inferInstance : I.cochainComplex.IsStrictlyGE 0)
    have h0 : IsZero ((res R F).X n) := CochainComplex.isZero_of_isStrictlyGE _ 0 n hn
    exact ModuleCat.isZero_iff_subsingleton.1 ((secEvalFun R U).map_isZero h0)

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleLocalSectionsRestrictCompatibly
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh
  GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

namespace GlobalTheory.CechDR.AffLoc

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem resThk_pt (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) :
    spMap ((RingHom.id (Sec (algStr R T.obj.B) p.1.1.1)).comp
      (Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) : Sec (algStr R T.obj.B) q.1.1.1 →+* Sec (algStr R T.obj.B) p.1.1.1)) ≫
      (affPt (algStr R T.obj.B) q.1.1 ≫ pt T) = affPt (algStr R T.obj.B) p.1.1 ≫ pt T := by
  rw [RingHom.id_comp, ← Category.assoc, affPt_res]

def resThk (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) : thk T q ⟶ thk T p :=
  ⟨Thick.trivHom (T := (thk T p).obj) (Sec.res (algStr R T.obj.B) (Pair.le_fst hpq)) (resThk_pt T hpq)⟩

theorem bM_resThk (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) :
    bM T q ≫ resThk T hpq = bM T p :=
  ObjectProperty.hom_ext _ (Thick.Hom.ext' (AlgHom.ext fun b ↦
    res_toSec R T.obj.B (homOfLE (Pair.le_fst hpq)).op b))

theorem aM_resThk (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) :
    aM T q ≫ resThk T hpq = (affF s).map (homOfLE (Pair.le_snd hpq)).op ≫ aM T p :=
  ObjectProperty.hom_ext _ (Thick.Hom.ext' (AlgHom.ext fun u ↦
    (congrArg (fun t ↦ t.hom u) ((pt T).appLE_map q.2 (homOfLE (Pair.le_fst hpq)).op)).trans
      (congrArg (fun t ↦ t.hom u) ((pt T).map_appLE p.2 (homOfLE (Pair.le_snd hpq)).op)).symm))

theorem hSec_res (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s))
    (hg : ∀ ⦃U V : AffOp X⦄ (a : U ⟶ V), g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a))
    (T : TT s) (p q : Pair (pt T)) (hpq : p ≤ q) :
    Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) (hSec f g T q) = hSec f g T p := by
  set ρ := Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) with hρ
  let d : op q.1.2 ⟶ op p.1.2 := (homOfLE (Pair.le_snd hpq)).op
  have e1 : fv f (bM T p) = ρ (fv f (bM T q)) + fv f (resThk T hpq) := by
    rw [← bM_resThk T hpq]; exact f.2 _ _
  have e2 : ρ (fv f (aM T q)) + fv f (resThk T hpq) =
      secPullA T p (fv f ((affF s).map d)) + fv f (aM T p) := by
    have k := f.2 (aM T q) (resThk T hpq)
    rw [aM_resThk] at k
    exact k.symm.trans (f.2 ((affF s).map d) (aM T p))
  have e3 : g (op p.1.2) = Sec.res s (Pair.le_snd hpq) (g (op q.1.2)) +
      (show Sec s p.1.2.1 from fv f ((affF s).map d)) :=
    sub_eq_iff_eq_add'.1 (hg d)
  have e4 : ∀ u, secPullA T p (Sec.res s (Pair.le_snd hpq) u) = ρ (secPullA T q u) := fun u ↦
    (congrArg (fun m ↦ m.hom.φ u) (aM_resThk T hpq)).symm
  change ρ (secPullA T q (g (op q.1.2)) + fv f (aM T q) - fv f (bM T q)) =
    secPullA T p (g (op p.1.2)) + fv f (aM T p) - fv f (bM T p)
  rw [map_sub, map_add (f := _), e1, e3, map_add (f := _), e4]
  linear_combination e2

end GlobalTheory.CechDR.AffLoc
end
end

