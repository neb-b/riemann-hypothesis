module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.ChartPointCongruence.EqOfMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfLargeAdelicDegree
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem val_le_exp_of_ord (v : Place k F) (x : F) (d : ℤ) (hd : 0 ≤ d) (h : -d ≤ ord v x) :
    v.1 x ≤ WithZero.exp d := by
  by_cases hx : v.1 x = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
    unfold ord at h; omega

theorem val_algebraMap_le_one (v : Place k F) (c : k) : v.1 (algebraMap k F c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (v.2.2 c hc).le

theorem val_comb_le (v : Place k F) {m : ℕ} (f : Fin m → F) (c : Fin m → k)
    (B : WithZero (Multiplicative ℤ)) (h : ∀ j, v.1 (f j) ≤ B) : v.1 (∑ j, c j • f j) ≤ B := by
  apply v.1.map_sum_le
  intro j _
  rw [Algebra.smul_def, map_mul]
  calc v.1 (algebraMap k F (c j)) * v.1 (f j) ≤ 1 * B := mul_le_mul' (val_algebraMap_le_one v _) (h j)
    _ = B := one_mul B

theorem val_mulVec_le_one (v : Place k F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (hM : ∀ i j, v.1 (M i j) ≤ 1) (p : Fin n → F) (hp : ∀ i, v.1 (p i) ≤ 1) (i : Fin n) :
    v.1 (M.mulVec p i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  apply v.1.map_sum_le
  intro j _
  rw [map_mul]
  calc v.1 (M i j) * v.1 (p j) ≤ 1 * 1 := mul_le_mul' (hM i j) (hp j)
    _ = 1 := one_mul 1

theorem exists_exp_bound (v : Place k F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    ∃ d : ℕ, ∀ i j, v.1 (M i j) ≤ WithZero.exp (d : ℤ) := by
  refine ⟨Finset.univ.sup fun ij : Fin n × Fin n => (WithZero.log (v.1 (M ij.1 ij.2))).toNat,
    fun i j => ?_⟩
  by_cases hx : v.1 (M i j) = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
    have := Finset.le_sup (f := fun ij : Fin n × Fin n => (WithZero.log (v.1 (M ij.1 ij.2))).toNat)
      (Finset.mem_univ (i, j))
    simp only at this
    omega

theorem exists_section_of_large_deg : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∃ γ : ℕ, ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → (n : ℤ) * γ < deg g → ∃ p : Fin n → F, p ≠ 0 ∧ ∀ (v : Place k F) (i : Fin n), v.1 ((g v).mulVec p i) ≤ 1 := by
  intro k F _ _ _ _ _ hFF
  obtain ⟨γ, hγ⟩ := _root_.GlobalTheory.Nef.riemann_cofinal k F hFF
  refine ⟨γ, fun n g hg hdeg => ?_⟩
  classical
  set B := hg.2.toFinset with hBdef
  choose d0 hd0 using fun v => exists_exp_bound v (g v)⁻¹
  let D : Place k F →₀ ℤ := Finsupp.onFinset B (fun v => if v ∈ B then (d0 v : ℤ) else 0)
    (by intro v hv; by_contra h; exact hv (if_neg h))
  obtain ⟨D', hDD', m, f, hf, hm, hford⟩ := hγ D
  have hD0 : ∀ v, 0 ≤ D' v := fun v => le_trans
    (by simp only [D, Finsupp.onFinset_apply]; split_ifs <;> omega) (hDD' v)
  have hloc : ∀ v, ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)),
      (N : ℤ) = n * ((D' v).toNat : ℕ) - ord v (g v).det ∧
      ∀ p : Fin n → F, (∀ i, v.1 (p i) ≤ WithZero.exp (((D' v).toNat : ℕ) : ℤ)) → φ p = 0 →
        ∀ i, v.1 ((g v).mulVec p i) ≤ 1 := by
    intro v
    refine _root_.GlobalTheory.Nef.local_index_scaled k F hFF v n (g v) _ (hg.1 v) ?_
    intro i j
    by_cases hv : v ∈ B
    · have hDv : D v = d0 v := by simp [D, Finsupp.onFinset_apply, hv]
      calc v.1 ((g v)⁻¹ i j) ≤ WithZero.exp (d0 v : ℤ) := hd0 v i j
        _ ≤ _ := by
          rw [WithZero.exp_le_exp]; have := hDD' v; rw [hDv] at this; omega
    · have hU : Unimod v (g v) := by simpa [B] using hv
      have hU' := ((_root_.GlobalTheory.Nef.ord_calculus k F v).2.2.2.2.2.2.2.2.2 n (g v) (g v) hU hU).2
      calc v.1 ((g v)⁻¹ i j) ≤ 1 := hU'.1 i j
        _ = WithZero.exp 0 := rfl
        _ ≤ _ := by rw [WithZero.exp_le_exp]; omega
  choose N φ hN hφ using hloc
  set S := B ∪ D'.support with hS
  have hsumD : D'.sum (fun _ m => m) = ∑ v ∈ S, D' v := by
    unfold Finsupp.sum
    apply Finset.sum_subset Finset.subset_union_right
    intro v _ hv; simpa using hv
  have hdegS : deg g = ∑ v ∈ S, ord v (g v).det := by
    unfold deg
    apply finsum_eq_sum_of_support_subset
    intro v hv
    rw [Finset.coe_union]; left
    simp only [B, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro hU; apply hv
    simp [ord, hU.2]
  have hNsum : ((∑ v ∈ S, N v : ℕ) : ℤ) < n * m := by
    push_cast
    rw [Finset.sum_congr rfl (fun v _ => hN v), Finset.sum_sub_distrib, ← Finset.mul_sum]
    have : ∀ v, (((D' v).toNat : ℕ) : ℤ) = D' v := fun v => Int.toNat_of_nonneg (hD0 v)
    simp_rw [this]
    rw [← hsumD, ← hdegS]
    have := mul_le_mul_of_nonneg_left hm (Int.natCast_nonneg n)
    nlinarith
  obtain ⟨c, hp0, hpψ⟩ := _root_.GlobalTheory.exists_ne_zero_comb_mem_ker k F (Place k F) n m f hf S N φ (by exact_mod_cast hNsum)
  refine ⟨_, hp0, fun v i => ?_⟩
  have hpb : ∀ i, v.1 (∑ j, c i j • f j) ≤ WithZero.exp (((D' v).toNat : ℕ) : ℤ) := fun i =>
    val_comb_le v f (c i) _ (fun j => val_le_exp_of_ord v _ _ (by omega)
      (by rw [Int.toNat_of_nonneg (hD0 v)]; exact hford j v))
  by_cases hv : v ∈ S
  · exact hφ v _ hpb (hpψ v hv) i
  · have hvB : v ∉ B := fun h => hv (Finset.mem_union_left _ h)
    have hD'v : D' v = 0 := by
      by_contra h; exact hv (Finset.mem_union_right _ (Finsupp.mem_support_iff.2 h))
    have hU : Unimod v (g v) := by simpa [B] using hvB
    apply val_mulVec_le_one v _ hU.1
    intro i; have := hpb i; rw [hD'v] at this; simpa using this

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateTwistMulDegreeZeroHom
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem Sec.res_map_of_sheaf_morphism {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) := by
  have h := congrArg (fun h => h.hom x) (f.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

theorem Sec.map_nsmul_of_sheaf_morphism {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (x : Sec F U) :
    Sec.map f (n • x) = n • Sec.map f x := map_nsmul (f.hom.app (op U)).hom n x

theorem nsmul_eq_of_natCast_eq_zmod_ulift_module {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] {m n : ℕ}
    (h : (m : ZMod q) = (n : ZMod q)) (x : M) : m • x = n • x := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) m x, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) n x]
  congr 1
  apply ULift.ext
  simpa using h

theorem twist_mul_map : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {K : Cx (ZMod q)}
    (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), ∃ φ : tw q k ⟶ K.X 0, ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) := by
  intro q _ i j k hk K τ
  obtain ⟨-, -, -, h4i, h5i, -⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q i
  obtain ⟨-, -, -, h4j, h5j, -⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q j
  obtain ⟨-, -, -, -, -, h6⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q k
  let e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (K.X 0) U := fun U ζ =>
    τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))
  have hnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom) := by
    intro V U g ζ
    simp only [e]
    rw [τ.nat, Sec.res_map_of_sheaf_morphism, Sec.res_map_of_sheaf_morphism, h4i, h4j]
  have hrel : ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
      e U ξ = ((a ^ k : (ZMod q)ˣ) : ZMod q).val • e U ζ := by
    intro U ζ ξ a h
    simp only [e]
    rw [h5i U ζ ξ a h, h5j U ζ ξ a h, Sec.map_nsmul_of_sheaf_morphism, Sec.map_nsmul_of_sheaf_morphism, map_nsmul, map_nsmul, LinearMap.smul_apply, smul_smul]
    apply nsmul_eq_of_natCast_eq_zmod_ulift_module (q := q)
    rw [Nat.cast_mul, ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id, ZMod.natCast_val, ZMod.cast_id,
      ← hk, zpow_add, Units.val_mul, mul_comm]
  obtain ⟨φ, hφ, -⟩ := h6 (K.X 0) e hnat hrel
  exact ⟨φ, hφ⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceOfFiniteEtaleDegree
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.TrDeg

open GlobalTheory.EtC.Tr

variable (R : Type) [CommRing R]

theorem chainMap_comp {X Y Z : Scheme.{0}} (t : freeSch R X ⟶ freeSch R Y) (t' : freeSch R Y ⟶ freeSch R Z) :
    chainMap R (t ≫ t') = chainMap R t ≫ chainMap R t' := by
  have : simpMap R (t ≫ t') = simpMap R t ≫ simpMap R t' := by ext; rfl
  rw [chainMap, this, Functor.map_comp]
  exact CategoryTheory.Functor.map_comp _ _ _

theorem chainMap_add {X Y : Scheme.{0}} (t t' : freeSch R X ⟶ freeSch R Y) :
    chainMap R (t + t') = chainMap R t + chainMap R t' := by
  have : simpMap R (t + t') = simpMap R t + simpMap R t' := by ext; rfl
  rw [chainMap, this, (AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map_add]
  exact (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map_add

theorem along_comp {X Y Z : Scheme.{0}} (F : Shv R) (n : ℤ) (t : freeSch R X ⟶ freeSch R Y) (t' : freeSch R Y ⟶ freeSch R Z)
    (x : H R (sch.obj Z) F n) : along R F n (t ≫ t') x = along R F n t (along R F n t' x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, chainMap_comp, Cochain.ofHom_comp]

theorem along_add {X Y : Scheme.{0}} (F : Shv R) (n : ℤ) (t t' : freeSch R X ⟶ freeSch R Y)
    (x : H R (sch.obj Y) F n) : along R F n (t + t') x = along R F n t x + along R F n t' x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine (congrArg CohomologyClass.mk (Cocycle.ext ?_)).trans (CohomologyClass.mk_add _ _)
  simp [zcomp, chainMap_add, Cochain.ofHom_add, Cochain.add_comp]

theorem along_nsmul_id (X : Scheme.{0}) (F : Shv R) (n : ℤ) (d : ℕ) (x : H R (sch.obj X) F n) :
    along R F n (d • 𝟙 (freeSch R X)) x = d • x := by
  induction d with
  | zero =>
    have h := along_add R F n (0 : freeSch R X ⟶ freeSch R X) 0 x
    rw [add_zero] at h
    rw [zero_smul, zero_smul]
    exact left_eq_add.1 h
  | succ d ih => rw [succ_nsmul, succ_nsmul, along_add, ih, along_id]

theorem generate_singleton_mem {U X : Scheme.{0}} (u : U ⟶ X) [Etale u] [Surjective u] :
    Sieve.generate (Presieve.singleton u) ∈ Scheme.etaleTopology X :=
  Precoverage.generate_mem_toGrothendieck
    ((Scheme.singleton_mem_precoverage_iff (P := @Etale) u).2 ⟨(inferInstance : Surjective u).surj, inferInstance⟩)

theorem transfer_comp {Y X U : Scheme.{0}} {f : Y ⟶ X} {u : U ⟶ X} [Etale u] [Surjective u] {d : ℕ}
    {s : Fin d → (U ⟶ Y)} (hs : SplitBy f u s) {t : freeSch R X ⟶ freeSch R Y} (ht : IsTransfer R f t) :
    t ≫ (free R).map (yoneda.map f) = d • 𝟙 _ := by
  refine free_hom_ext_of_covering R _ _ _ _ (generate_singleton_mem u) ?_
  rintro V v ⟨_, g, _, ⟨⟩, rfl⟩
  have hg := splitBy_baseChange hs g
  rw [← Category.assoc, ht.apply_of_splitBy R hg, Preadditive.sum_comp]
  have h1 : ∀ j, (free R).map (yoneda.map (g ≫ s j)) ≫ (free R).map (yoneda.map f) =
      (free R).map (yoneda.map (g ≫ u)) := fun j => by
    rw [← Functor.map_comp, ← Functor.map_comp, hg.1 j]
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Preadditive.comp_nsmul, Category.comp_id]

theorem trH_pull {Y X U : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] {u : U ⟶ X} [Etale u] [Surjective u] {d : ℕ}
    {s : Fin d → (U ⟶ Y)} (hs : SplitBy f u s) (F : Shv R) (n : ℤ) (x : H R (sch.obj X) F n) :
    trH R f F n (pull R (sch.map f) F n x) = d • x := by
  rw [trH, ← along_free, ← along_comp,
    transfer_comp R hs (transfer_spec R (existsUnique_isTransfer R f).exists), along_nsmul_id]

end GlobalTheory.EtC.TrDeg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CechDR

open CatCoh

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem pairRes_bijective (φ : X' ⟶ X) (s' : X' ⟶ Sp R') :
    Function.Bijective (pairRes φ s').pull1 ∧ Function.Bijective (pullGlob1 (pairRes φ s')) ∧
      Function.Bijective (pullHyp1 (pairRes φ s')) := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hcov := _root_.GlobalTheory.CechDR.pair_cover_affine φ s'
  have hdir := _root_.GlobalTheory.CechDR.exists_pair_below_two φ s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') (pairFst φ) H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hs1 := _root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' (pairFst φ) hcov
  have hg1 := _root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' (pairFst φ) hcov hdir
  have hs2 := _root_.GlobalTheory.CechDR.twoForm_sep_of_basis s' (pairFst φ) hcov
  have b1 : Function.Bijective (pairRes φ s').pull1 :=
    ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg, _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩
  have bg := _root_.GlobalTheory.restrict_glob1_bijective _ _ hs1 hg1
  exact ⟨b1, bg, _root_.GlobalTheory.CechDR.pullHyp1_restrict_injective _ _ b1.1 (_root_.GlobalTheory.compat_family_extend _ _ hs hg) bg.1,
    _root_.GlobalTheory.CechDR.pullHyp1_restrict_surjective _ _ b1.2 (_root_.GlobalTheory.cocycle_one_forms_coboundary_of_restrict _ _ hs1 hg1) bg.2 hs2⟩

variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ)

theorem existsUnique_isPull1 (c : HH1 s) : ∃! c', IsPull1 h c c' := by
  obtain ⟨c', hc, hu⟩ := (pairRes_bijective φ s').2.2.existsUnique (pullHyp1 (pairPull h) c)
  exact ⟨c', hc.symm, fun y hy ↦ hu y hy.symm⟩

theorem existsUnique_isPullO (c : HO1 s) : ∃! c', IsPullO h c c' := by
  obtain ⟨c', hc, hu⟩ := (pairRes_bijective φ s').1.existsUnique ((pairPull h).pull1 c)
  exact ⟨c', hc.symm, fun y hy ↦ hu y hy.symm⟩

theorem existsUnique_isPullForm (ω : GlobForm s) : ∃! ω', IsPullForm h ω ω' := by
  obtain ⟨ω', hω, hu⟩ := (pairRes_bijective φ s').2.1.existsUnique (pullGlob1 (pairPull h) ω)
  exact ⟨ω', hω.symm, fun y hy ↦ hu y hy.symm⟩

def pairResEquiv1 (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : HH1 s' ≃ₗ[R'] Hyp1 (OPair φ s') :=
  LinearEquiv.ofBijective (pullHyp1 (pairRes φ s')) (pairRes_bijective φ s').2.2

def pairResEquivO (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : HO1 s' ≃ₗ[R'] CatCoh.H1 (OPair φ s') :=
  LinearEquiv.ofBijective (pairRes φ s').pull1 (pairRes_bijective φ s').1

def pairResEquivForm (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : GlobForm s' ≃ₗ[R'] Glob1 (OPair φ s') :=
  LinearEquiv.ofBijective (pullGlob1 (pairRes φ s')) (pairRes_bijective φ s').2.1

def pullHH1 : HH1 s →ₛₗ[σ] HH1 s' :=
  (pairResEquiv1 φ s').symm.toLinearMap.comp (pullHyp1 (pairPull h))

def pullHO1 : HO1 s →ₛₗ[σ] HO1 s' :=
  (pairResEquivO φ s').symm.toLinearMap.comp (pairPull h).pull1

def pullForm : GlobForm s →ₛₗ[σ] GlobForm s' :=
  (pairResEquivForm φ s').symm.toLinearMap.comp (pullGlob1 (pairPull h))

theorem isPull1_pullHH1 (c : HH1 s) : IsPull1 h c (pullHH1 h c) :=
  ((pairResEquiv1 φ s').apply_symm_apply _).symm

theorem isPullO_pullHO1 (c : HO1 s) : IsPullO h c (pullHO1 h c) :=
  ((pairResEquivO φ s').apply_symm_apply _).symm

theorem isPullForm_pullForm (ω : GlobForm s) : IsPullForm h ω (pullForm h ω) :=
  ((pairResEquivForm φ s').apply_symm_apply _).symm

theorem IsPull1.eq_pullHH1 {c : HH1 s} {c' : HH1 s'} (e : IsPull1 h c c') : c' = pullHH1 h c :=
  (existsUnique_isPull1 h c).unique e (isPull1_pullHH1 h c)

theorem IsPullO.eq_pullHO1 {c : HO1 s} {c' : HO1 s'} (e : IsPullO h c c') : c' = pullHO1 h c :=
  (existsUnique_isPullO h c).unique e (isPullO_pullHO1 h c)

theorem IsPullForm.eq_pullForm {ω : GlobForm s} {ω' : GlobForm s'} (e : IsPullForm h ω ω') :
    ω' = pullForm h ω :=
  (existsUnique_isPullForm h ω).unique e (isPullForm_pullForm h ω)

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLim
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdicPt

open IsLocalRing

private theorem factor_range {S : Type} [CommRing S] {Y : Scheme.{0}} {A : CommRingCat.{0}} (j : Spec A ⟶ Y)
    [IsOpenImmersion j] (f : Spec (CommRingCat.of S) ⟶ Y) (h : Set.range f ⊆ Set.range j) :
    ∃ φ : A ⟶ CommRingCat.of S, Spec.map φ ≫ j = f :=
  ⟨Spec.preimage (IsOpenImmersion.lift j f h), by rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩

private theorem range_subset {S : Type} [CommRing S] [IsLocalRing S] {Y : Scheme.{0}} {A : CommRingCat.{0}}
    (j : Spec A ⟶ Y) [IsOpenImmersion j] (f : Spec (CommRingCat.of S) ⟶ Y)
    (h : f (closedPoint S) ∈ Set.range j) : Set.range f ⊆ Set.range j := by
  rintro _ ⟨y, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint y).map f.continuous).mem_open j.isOpenEmbedding.isOpen_range h

variable {R : Type} [CommRing R] [IsLocalRing R] {a : R}

private theorem quot_local (ha : ¬ IsUnit a) (m : ℕ) : IsLocalRing (R ⧸ Ideal.span {a ^ (m + 1)}) := by
  haveI : Nontrivial (R ⧸ Ideal.span {a ^ (m + 1)}) := by
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun h => ha (isUnit_of_dvd_unit (dvd_pow_self a (Nat.succ_ne_zero m)) h)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

private theorem spec_closed {S S' : Type} [CommRing S] [CommRing S'] [IsLocalRing S] [IsLocalRing S']
    (f : S →+* S') (hf : Function.Surjective f) {Y : Scheme.{0}} (g : Spec (CommRingCat.of S) ⟶ Y) :
    (Spec.map (CommRingCat.ofHom f) ≫ g) (closedPoint S') = g (closedPoint S) := by
  haveI : IsLocalHom f := IsLocalHom.of_surjective f hf
  haveI : IsLocalHom (CommRingCat.ofHom f).hom := this
  exact congrArg g (Spec_closedPoint (f := CommRingCat.ofHom f))

theorem scheme_ext (ha : ¬ IsUnit a) (hc : IsAdicComplete (Ideal.span {a}) R) {Y : Scheme.{0}}
    (f g : Spec (CommRingCat.of R) ⟶ Y)
    (h : ∀ m : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a ^ m}))) ≫ f =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a ^ m}))) ≫ g) : f = g := by
  haveI := quot_local ha 0
  have hcl : f (closedPoint R) = g (closedPoint R) := by
    rw [← spec_closed (Ideal.Quotient.mk (Ideal.span {a ^ (0 + 1)})) Ideal.Quotient.mk_surjective f,
      ← spec_closed (Ideal.Quotient.mk (Ideal.span {a ^ (0 + 1)})) Ideal.Quotient.mk_surjective g, h]
  obtain ⟨A, j, _, hx, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := f (closedPoint R)) (U := ⊤) trivial
  obtain ⟨φ, rfl⟩ := factor_range j f (range_subset j f hx)
  obtain ⟨ψ, rfl⟩ := factor_range j g (range_subset j g (hcl ▸ hx))
  congr 2
  ext z
  refine ChPt.eq_of_mod a hc.toIsHausdorff _ _ fun m => ?_
  have e := h m
  rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at e
  exact congrArg (fun k => k.hom z) (Spec.map_injective e)

theorem scheme_lim (ha : ¬ IsUnit a) (hc : IsAdicComplete (Ideal.span {a}) R) {Y : Scheme.{0}}
    (y : ∀ m : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {a ^ m})) ⟶ Y)
    (hy : ∀ m : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (Nat.le_succ m))))) ≫ y (m + 1) = y m) :
    ∃ Q : Spec (CommRingCat.of R) ⟶ Y, ∀ m : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a ^ m}))) ≫ Q = y m := by
  haveI := quot_local ha
  obtain ⟨A, j, _, hx, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := y (0 + 1) (closedPoint _)) (U := ⊤) trivial
  have hcl : ∀ m : ℕ, y (m + 1) (closedPoint _) ∈ Set.range j := by
    intro m
    induction m with
    | zero => exact hx
    | succ m ih =>
      have e := spec_closed _ (Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.mpr
        (pow_dvd_pow a (Nat.le_succ (m + 1))))) (y (m + 1 + 1))
      rw [hy (m + 1)] at e
      obtain ⟨u, hu⟩ := ih
      exact ⟨u, hu.trans e⟩
  have hr : ∀ m : ℕ, Set.range (y m) ⊆ Set.range j := by
    intro m
    rw [← hy m]
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact range_subset j _ (hcl m) ⟨_, rfl⟩
  choose φ hφ using fun m => factor_range j (y m) (hr m)
  obtain ⟨L, hL⟩ := ChPt.algLimSt ℤ A R a hc (fun m => (φ m).hom.toIntAlgHom) (by
    intro m z w hw
    have e := hy m
    rw [← hφ, ← hφ, ← Category.assoc, cancel_mono, ← Spec.map_comp] at e
    have e' := congrArg (fun k => k.hom z) (Spec.map_injective e)
    exact (congrArg (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (Nat.le_succ m)))) hw).trans e')
  refine ⟨Spec.map (CommRingCat.ofHom L.toRingHom) ≫ j, fun m => ?_⟩
  rw [← hφ m, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext z
  exact congrArg (fun k => k z) (hL m)

theorem existsUnique_lim : ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] (a : R), ¬ IsUnit a → IsAdicComplete (Ideal.span {a}) R → ∀ (X : Over (Spec (CommRingCat.of O))) (x : ∀ m : ℕ, specO O (R ⧸ Ideal.span {a ^ m}) ⟶ X), (∀ m : ℕ, ptMap (Ideal.Quotient.factorₐ O (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (Nat.le_succ m)))) ≫ x (m + 1) = x m) → ∃! Q : specO O R ⟶ X, ∀ m : ℕ, ptMap (Ideal.Quotient.mkₐ O (Ideal.span {a ^ m})) ≫ Q = x m := by
  intro O R _ _ _ _ a ha hc X x hx
  obtain ⟨Q, hQ⟩ := scheme_lim ha hc (Y := X.left) (fun m => (x m).left)
    (fun m => congrArg CommaMorphism.left (hx m))
  have hw : Q ≫ X.hom = (specO O R).hom := by
    refine scheme_ext ha hc _ _ fun m => ?_
    rw [← Category.assoc, hQ]
    exact (Over.w (x m)).trans (Over.w (ptMap (Ideal.Quotient.mkₐ O (Ideal.span {a ^ m})))).symm
  refine ⟨Over.homMk Q hw, fun m => Over.OverMorphism.ext (hQ m), fun Q' hQ' => Over.OverMorphism.ext ?_⟩
  refine scheme_ext ha hc _ _ fun m => ?_
  exact (congrArg CommaMorphism.left (hQ' m)).trans (hQ m).symm

end GlobalTheory.AdicPt
end
end

