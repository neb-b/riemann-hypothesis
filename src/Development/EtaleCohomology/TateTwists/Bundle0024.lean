module

public import Development.EtaleCohomology.TateTwists.Bundle0014
public import Development.EtaleCohomology.TateTwists.Bundle0011
public import Development.EtaleCohomology.TateTwists.Bundle0009
public import Development.EtaleCohomology.TateTwists.Bundle0012

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.TwTorsPfR
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TwTorsPf

section Field
variable {q : ℕ} [NeZero q] {k : Type} [Field k]

theorem prim_isPrim (ζ : Prim q k) : IsPrimitiveRoot ζ.1 q := by
  haveI : NeZero (q : k) := ⟨ζ.2.1.ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := ζ.2.2
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic] using h

theorem pow_eq_pow_cast {ζ : k} (h : IsPrimitiveRoot ζ q) {m n : ℕ} (e : ζ ^ m = ζ ^ n) :
    (m : ZMod q) = (n : ZMod q) := by
  have h0 : ζ ≠ 0 := h.ne_zero (NeZero.ne q)
  have e' : ζ ^ ((m : ℤ) - n) = 1 := by
    rw [zpow_sub₀ h0, zpow_natCast, zpow_natCast, e, div_self (pow_ne_zero _ h0)]
  have hd := (h.zpow_eq_one_iff_dvd _).1 e'
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub (n : ℤ) (m : ℤ) q).2 hd
  exact_mod_cast this.symm
end Field

section Field2
variable {q : ℕ} [NeZero q] {k : Type} [Field k]

def ex (ζ0 ξ : Prim q k) : ℕ :=
  ((prim_isPrim ζ0).eq_pow_of_pow_eq_one (prim_isPrim ξ).pow_eq_one).choose

theorem ex_spec (ζ0 ξ : Prim q k) : ζ0.1 ^ ex ζ0 ξ = ξ.1 :=
  ((prim_isPrim ζ0).eq_pow_of_pow_eq_one (prim_isPrim ξ).pow_eq_one).choose_spec.2

theorem ex_cop (ζ0 ξ : Prim q k) : (ex ζ0 ξ).Coprime q := by
  have h := prim_isPrim ξ
  rw [← ex_spec ζ0 ξ] at h
  exact ((prim_isPrim ζ0).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) _).1 h

theorem ex_eq (ζ0 ξ : Prim q k) {m : ℕ} (h : ζ0.1 ^ m = ξ.1) : (ex ζ0 ξ : ZMod q) = m :=
  pow_eq_pow_cast (prim_isPrim ζ0) ((ex_spec ζ0 ξ).trans h.symm)

def exU (ζ0 ξ : Prim q k) : (ZMod q)ˣ := ZMod.unitOfCoprime _ (ex_cop ζ0 ξ)

theorem exU_rel (ζ0 η ξ : Prim q k) (a : (ZMod q)ˣ) (h : ξ.1 = η.1 ^ (a : ZMod q).val) :
    exU ζ0 ξ = exU ζ0 η * a := by
  ext
  simp only [exU, ZMod.coe_unitOfCoprime, Units.val_mul]
  rw [ex_eq ζ0 ξ (m := ex ζ0 η * (a : ZMod q).val)]
  · push_cast
    rw [ZMod.natCast_zmod_val]
  · rw [pow_mul, ex_spec, h]

theorem exU_self (ζ0 : Prim q k) : exU ζ0 ζ0 = 1 := by
  ext
  simp only [exU, ZMod.coe_unitOfCoprime, Units.val_one]
  rw [ex_eq ζ0 ζ0 (m := 1) (pow_one _)]
  simp

def val (i : ℤ) (ζ0 ξ : Prim q k) : ULift.{1} (ZMod q) := ULift.up (((exU ζ0 ξ) ^ i : (ZMod q)ˣ) : ZMod q)

def fn (i : ℤ) (ζ0 : Prim q k) : (Prim q k →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination _ (val i ζ0)

theorem rel_le (i : ℤ) (ζ0 : Prim q k) : twRel q i k ≤ LinearMap.ker (fn i ζ0) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨η, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, fn, Finsupp.linearCombination_single]
  rw [sub_eq_zero, val, val, exU_rel ζ0 η ξ a h, mul_zpow]
  apply ULift.ext
  simp [mul_comm]

theorem field_tors (i : ℤ) (ζ : Prim q k) (c : ℕ)
    (h : c • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q k →₀ ULift.{1} (ZMod q)) ⧸ twRel q i k) = 0) :
    q ∣ c := by
  have h2 := congrArg ((twRel q i k).liftQ (fn i ζ) (rel_le i ζ)) h
  rw [map_nsmul, map_zero, Submodule.liftQ_apply, fn, Finsupp.linearCombination_single, val, exU_self] at h2
  have h3 := congrArg ULift.down h2
  simp at h3
  exact (ZMod.natCast_eq_zero_iff c q).1 (by simpa using h3)
end Field2

theorem twF_map_mk {q : ℕ} (i : ℤ) {A B : CommRingCat.{0}} (φ : A ⟶ B) (ζ : Prim q A) :
    ((twF q i).map φ).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      Submodule.Quotient.mk (Finsupp.single (ζ.map φ.hom) 1) := by
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map φ.hom) (Finsupp.single ζ 1)) = _
  rw [Finsupp.mapDomain_single]

theorem ring_tors {q : ℕ} [NeZero q] (i : ℤ) {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (c : ℕ)
    (h : c • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) = 0) :
    q ∣ c := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  let f : A →+* A ⧸ m := Ideal.Quotient.mk m
  have h2 := congrArg (Submodule.mapQ _ _ (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q)) (Prim.map f))
    (twRel_le q i f)) h
  rw [map_nsmul, map_zero, Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] at h2
  exact field_tors i (ζ.map f) c h2

theorem jsEt : Scheme.JointlySurjective (Scheme.precoverage @AlgebraicGeometry.Etale.{0}) where
  exists_eq {X} R := fun ⟨hR, _⟩ x ↦ by
    rw [Scheme.jointlySurjectivePrecoverage, Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hR
    obtain ⟨Y, g, hg, heq⟩ := hR x
    exact ⟨Y, g, hg, heq⟩

theorem TwTors_of : LateralTheory.EtaleFoundations.TwLocPf.TwTors := by
  intro q _ i U _ ζ c hc
  let P := Scheme.Γ ⋙ twF q i
  let x : P.obj (op U) := Submodule.Quotient.mk (Finsupp.single ζ 1)
  have h1 : (toSheafify Scheme.etaleTopology P).app (op U) (c • x) =
      (toSheafify Scheme.etaleTopology P).app (op U) 0 := by
    have : ((toSheafify Scheme.etaleTopology P).app (op U)).hom (c • x) = 0 := by
      rw [map_nsmul]; exact hc
    simpa using this
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) (c • x) 0 h1
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  haveI := jsEt
  obtain ⟨j, y, -⟩ := 𝒰.exists_eq (Classical.arbitrary U)
  have hj := hle _ _ (Presieve.ofArrows.mk j)
  simp only [Presheaf.equalizerSieve_apply, map_zero] at hj
  have : Nonempty (𝒰.X j) := ⟨y⟩
  have : Nonempty (⊤ : (𝒰.X j).Opens) := ⟨⟨y, trivial⟩⟩
  have h3 : ((twF q i).map (𝒰.f j).appTop).hom (c • x) = 0 := hj
  have h4 : c • ((twF q i).map (𝒰.f j).appTop).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 0 :=
    (map_nsmul ((twF q i).map (𝒰.f j).appTop).hom c _).symm.trans h3
  rw [twF_map_mk] at h4
  exact ring_tors i _ c h4

end LateralTheory.EtaleFoundations.TwTorsPf
end
end

-- bundled from Development.EtaleCohomology.TateTwists.TwpairZcFunPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

section
variable {R : Type} [CommRing R]

lemma zc_pull_mk {K L I : Cx R} (f : K ⟶ L) (n : ℤ) (b : Cocycle L I n) :
    cpull f I n (CohomologyClass.mk b) =
      CohomologyClass.mk (Cocycle.mk ((Cochain.ofHom f).comp b.1 (zero_add n)) (n + 1) rfl
        (by rw [δ_ofHom_comp, Cocycle.δ_eq_zero, Cochain.comp_zero])) := by
  rw [cpre_mk]; congr 1

lemma zc_push_mk {K I J : Cx R} (g : I ⟶ J) (n : ℤ) (a : Cocycle K I n) :
    cpush K g n (CohomologyClass.mk a) =
      CohomologyClass.mk (Cocycle.mk (a.1.comp (Cochain.ofHom g) (add_zero n)) (n + 1) rfl
        (by rw [δ_comp_ofHom, Cocycle.δ_eq_zero, Cochain.zero_comp])) := by
  rw [cpost_mk]; congr 1

end

theorem twpair_zc_fun_of : twpair_zc_fun := by
  intro R _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K I n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    constructor
    · rw [zc_pull_mk]; congr 1; apply Cocycle.ext; simp [Cochain.id_comp]
    · rw [zc_push_mk]; congr 1; apply Cocycle.ext; simp [Cochain.comp_id]
  · intro K L M f g I n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [zc_pull_mk, zc_pull_mk, zc_pull_mk]; congr 1; apply Cocycle.ext
    simp [Cochain.ofHom_comp]
  · intro K I J M f g n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [zc_push_mk, zc_push_mk, zc_push_mk]
    congr 1
  · intro K L I J f g n x
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [zc_push_mk, zc_pull_mk, zc_pull_mk, zc_push_mk]; congr 1; apply Cocycle.ext
    simp
  · intro K L f g ⟨ho⟩ I n
    obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g ho
    constructor
    · ext x
      obtain ⟨b, rfl⟩ := x.mk_surjective
      rw [zc_pull_mk, zc_pull_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub,
        CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
      refine ⟨n.negOnePow • z.comp b.1 (by omega), ?_⟩
      have hb : δ n (n + 1) (b : Cochain L I n) = 0 := Cocycle.δ_eq_zero _ _
      have hz' : δ (-1) 0 z = Cochain.ofHom f - Cochain.ofHom g := by rw [hz]; abel
      rw [δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) rfl]
      simp only [hb, Cochain.comp_zero, zero_add, smul_smul, Int.units_mul_self, one_smul, hz',
        Cochain.sub_comp]
      rfl
    · ext x
      obtain ⟨a, rfl⟩ := x.mk_surjective
      rw [zc_push_mk, zc_push_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub,
        CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
      refine ⟨a.1.comp z (by omega), ?_⟩
      have ha : δ n (n + 1) (a : Cochain I K n) = 0 := Cocycle.δ_eq_zero _ _
      have hz' : δ (-1) 0 z = Cochain.ofHom f - Cochain.ofHom g := by rw [hz]; abel
      rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega)]
      simp only [ha, Cochain.zero_comp, smul_zero, add_zero, hz', Cochain.comp_sub]
      rfl

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.ZmodInjectiveModuleFlatHolds
section
namespace LateralTheory.EtaleFoundations.QFFlat

universe u v

open TensorProduct

theorem zmod_P (q : ℕ) [NeZero q] (a : ZMod q) :
    ∃ b : ZMod q, b * a = 0 ∧ ∀ r : ZMod q, r * b = 0 → ∃ c, c * a = r := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  set n := a.val with hn
  set g := Nat.gcd n q with hg
  have hgq : g ∣ q := Nat.gcd_dvd_right n q
  have hgn : g ∣ n := Nat.gcd_dvd_left n q
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right n hq
  have ha : (n : ZMod q) = a := ZMod.natCast_zmod_val a
  refine ⟨((q / g : ℕ) : ZMod q), ?_, fun r hr => ?_⟩
  · rw [← ha, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    obtain ⟨t, ht⟩ := hgn
    refine ⟨t, ?_⟩
    rw [ht, ← mul_assoc, Nat.div_mul_cancel hgq]
  · have hr' : (r.val : ZMod q) = r := ZMod.natCast_zmod_val r
    rw [← hr', ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hr
    have hqg : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq hgq) hgpos
    have hdiv : g ∣ r.val := by
      have h1 : g * (q / g) ∣ r.val * (q / g) := by rwa [Nat.mul_div_cancel' hgq]
      exact Nat.dvd_of_mul_dvd_mul_right hqg h1
    obtain ⟨j, hj⟩ := hdiv
    have hbez : ((g : ℤ) : ZMod q) = (n : ZMod q) * ((Nat.gcdA n q : ℤ) : ZMod q) := by
      rw [hg, Nat.gcd_eq_gcd_ab n q]
      push_cast
      simp
    refine ⟨((Nat.gcdA n q : ℤ) : ZMod q) * (j : ZMod q), ?_⟩
    rw [← hr', hj, ← ha]
    push_cast at hbez ⊢
    rw [hbez]
    ring

theorem ulift_P (q : ℕ) [NeZero q] (a : ULift.{1} (ZMod q)) :
    ∃ b : ULift.{1} (ZMod q), b * a = 0 ∧ ∀ r : ULift.{1} (ZMod q), r * b = 0 → ∃ c, c * a = r := by
  obtain ⟨b, hb, h⟩ := zmod_P q a.down
  refine ⟨ULift.up b, ULift.ext hb, fun r hr => ?_⟩
  obtain ⟨c, hc⟩ := h r.down (congrArg ULift.down hr)
  exact ⟨ULift.up c, ULift.ext hc⟩

theorem key {R : Type u} {M : Type v} [CommRing R] [Small.{v} R] [AddCommGroup M] [Module R M] (hM : Module.Injective R M)
    (hP : ∀ a : R, ∃ b : R, b * a = 0 ∧ ∀ r : R, r * b = 0 → ∃ c, c * a = r)
    (a : R) (m : M) (h : a • m = 0) : ∃ (b : R) (m' : M), b * a = 0 ∧ m = b • m' := by
  obtain ⟨b, hba, hb⟩ := hP a
  have wd : ∀ c c' : R, c * b = c' * b → c • m = c' • m := by
    intro c c' hcc
    obtain ⟨e, he⟩ := hb (c - c') (by rw [sub_mul, hcc, sub_self])
    rw [← sub_eq_zero, ← sub_smul, ← he, mul_smul, h, smul_zero]
  have hc : ∀ x : Ideal.span {b}, (Ideal.mem_span_singleton'.1 x.2).choose * b = x :=
    fun x => (Ideal.mem_span_singleton'.1 x.2).choose_spec
  let g : Ideal.span {b} →ₗ[R] M :=
    { toFun := fun x => (Ideal.mem_span_singleton'.1 x.2).choose • m
      map_add' := fun x y => by
        rw [← add_smul]
        apply wd
        rw [add_mul, hc, hc, hc, Submodule.coe_add]
      map_smul' := fun r x => by
        rw [RingHom.id_apply, ← mul_smul]
        apply wd
        rw [mul_assoc, hc, hc, Submodule.coe_smul, smul_eq_mul] }
  obtain ⟨G, hG⟩ := Module.Baer.of_injective hM (Ideal.span {b}) g
  refine ⟨b, G 1, hba, ?_⟩
  have hbm : b ∈ Ideal.span {b} := Ideal.subset_span rfl
  rw [← map_smul, smul_eq_mul, mul_one, hG b hbm]
  change m = (Ideal.mem_span_singleton'.1 hbm).choose • m
  conv_lhs => rw [← one_smul R m]
  apply wd
  rw [hc ⟨b, hbm⟩, one_mul]

theorem flat_of {R : Type u} {M : Type v} [CommRing R] [Small.{v} R] [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]
    (hM : Module.Injective R M)
    (hP : ∀ a : R, ∃ b : R, b * a = 0 ∧ ∀ r : R, r * b = 0 → ∃ c, c * a = r) : Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal I
  have mem : a ∈ I := by rw [ha]; exact Submodule.mem_span_singleton_self a
  have hrep : ∀ t : I ⊗[R] M, ∃ m : M, t = (⟨a, mem⟩ : I) ⊗ₜ m := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x n =>
      have hx : (x : R) ∈ Submodule.span R {a} := ha ▸ x.2
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
      refine ⟨c • n, ?_⟩
      rw [← smul_tmul]
      congr 1
      ext
      simp
      rw [← hc, smul_eq_mul]
    | add x y hx hy =>
      obtain ⟨mx, rfl⟩ := hx
      obtain ⟨my, rfl⟩ := hy
      exact ⟨mx + my, by rw [tmul_add]⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨m, rfl⟩ := hrep t
  have ham : a • m = 0 := by simpa using ht
  obtain ⟨b, m', hba, rfl⟩ := key hM hP a m ham
  rw [← smul_tmul]
  have h0 : b • (⟨a, mem⟩ : I) = 0 := Subtype.ext (by simp [hba])
  rw [h0, zero_tmul]

end LateralTheory.EtaleFoundations.QFFlat

theorem LateralTheory.EtaleFoundations.zmod_injective_module_flat_holds : LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat := by
  intro q _ N _ _ hN
  have : IsPrincipalIdealRing (ZMod q) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod q)) ZMod.intCast_surjective
  have : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
    IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := ZMod q)).symm
      (ULift.ringEquiv (R := ZMod q)).symm.surjective
  exact LateralTheory.EtaleFoundations.QFFlat.flat_of hN (LateralTheory.EtaleFoundations.QFFlat.ulift_P q)
end

-- bundled from Development.EtaleCohomology.TateTwists.acycPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.acyc

def LocAcyc {R : Type} [CommRing R] (C : Cx R) : Prop :=
  ∀ (U : Scheme.{0}) (n : ℤ) (z : Sec (C.X n) U), Sec.map (C.d n (n + 1)) z = 0 →
    Loc U fun V g => ∃ y : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) y = Sec.res g z

def ColExact {R : Type} [CommRing R] (C J : Cx R) : Prop :=
  ∀ (U : Scheme.{0}) (s t : ℤ) (x : Sec (C.X s) U ⊗[ULift.{1} R] Sec (J.X t) U),
    TensorProduct.map ((C.d s (s + 1)).hom.app (op U)).hom LinearMap.id x = 0 →
    Loc U fun V g => ∃ y : Sec (C.X (s - 1)) V ⊗[ULift.{1} R] Sec (J.X t) V,
      TensorProduct.map ((C.d (s - 1) s).hom.app (op V)).hom LinearMap.id y =
        TensorProduct.map ((C.X s).obj.map g.op).hom ((J.X t).obj.map g.op).hom x

def acycIff : Prop := ∀ (R : Type) [CommRing R] (C : Cx R), C.Acyclic ↔ LocAcyc C

def column : Prop := ∀ (R : Type) [CommRing R] (C J : Cx R), (∀ t, FlatS (J.X t)) → LocAcyc C → ColExact C J

def stair : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → ColExact C J → LocAcyc T

end LateralTheory.EtaleFoundations.acyc

open LateralTheory.EtaleFoundations.acyc in
theorem LateralTheory.EtaleFoundations.tqis.acyc_of (hI : acycIff) (hC : column) (hS : stair) : LateralTheory.EtaleFoundations.tqis.acyc := by
  intro R _ C J T a b _ _ τ hτ hJ hCa
  exact (hI R T).2 (hS R a b τ hτ (hC R C J hJ ((hI R C).1 hCa)))
end

