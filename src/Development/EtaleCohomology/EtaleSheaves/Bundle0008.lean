module

public import Development.EtaleCohomology.EtaleSheaves.LeafTwSecKillCut
public import Development.EtaleCohomology.EtaleSheaves.Bundle0003

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwGenPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec.Gen

theorem prim_pow_eq_one {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

theorem prim_isPrimitiveRoot {q : ℕ} [NeZero q] {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (ζ : Prim q A) :
    IsPrimitiveRoot (φ ζ.1) q := by
  have hu : IsUnit (q : K) := by simpa using ζ.2.1.map φ
  have : NeZero (q : K) := ⟨hu.ne_zero⟩
  have h := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ.1 (Polynomial.cyclotomic q ℤ)
  rw [ζ.2.2, map_zero] at h
  have h2 : Polynomial.aeval (φ ζ.1) (Polynomial.cyclotomic q ℤ) = 0 := by simpa using h
  rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic, ← Polynomial.IsRoot.def,
    Polynomial.isRoot_cyclotomic_iff] at h2

theorem exists_pow {q : ℕ} [NeZero q] {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (ζ ξ : Prim q A) :
    ∃ k < q, k.Coprime q ∧ φ ξ.1 = φ ζ.1 ^ k := by
  have hζ := prim_isPrimitiveRoot φ ζ
  have hξ := prim_isPrimitiveRoot φ ξ
  obtain ⟨i, hi, e⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  refine ⟨i, hi, ?_, e.symm⟩
  exact (hζ.pow_iff_coprime (NeZero.pos q) i).mp (by rw [e]; exact hξ)

theorem key_ring {A K : Type} [CommRing A] [Field K] (φ : A →+* K) (x y : A) (q k : ℕ) (hq : (q : K) ≠ 0)
    (hx : x ^ q = 1) (hy : y ^ q = 1) (h : φ x = φ y ^ k) :
    φ (∑ b ∈ Finset.range q, (x * y ^ (k * (q - 1))) ^ b) ≠ 0 ∧
    ∀ (B : Type) [CommRing B] (ψ : A →+* B), IsUnit (ψ (∑ b ∈ Finset.range q, (x * y ^ (k * (q - 1))) ^ b)) →
      ψ x = ψ y ^ k := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hkq : k * (q - 1) + k = k * q := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.one_le_iff_ne_zero.mpr hq0); simp [mul_add]; ring
  have hyk : y ^ (k * (q - 1)) * y ^ k = 1 := by rw [← pow_add, hkq, mul_comm, pow_mul, hy, one_pow]
  have hu : (x * y ^ (k * (q - 1))) ^ q = 1 := by
    rw [mul_pow, hx, one_mul, ← pow_mul, mul_comm, pow_mul, hy, one_pow]
  refine ⟨?_, ?_⟩
  · have : φ (x * y ^ (k * (q - 1))) = 1 := by
      rw [map_mul, map_pow, h, ← pow_add, add_comm, hkq, mul_comm, pow_mul, ← map_pow, hy, map_one, one_pow]
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, map_pow, this] using hq
  · intro B _ ψ hs
    have h0 : ψ (∑ b ∈ Finset.range q, (x * y ^ (k * (q - 1))) ^ b) * (ψ (x * y ^ (k * (q - 1))) - 1) = 0 := by
      rw [← map_one ψ, ← map_sub, ← map_mul, geom_sum_mul, hu, sub_self, map_zero]
    have h1 : ψ (x * y ^ (k * (q - 1))) = 1 := by
      have := (hs.mul_right_eq_zero).mp h0
      exact sub_eq_zero.mp this
    calc ψ x = ψ x * ψ (y ^ (k * (q - 1)) * y ^ k) := by rw [hyk, map_one, mul_one]
      _ = ψ (x * y ^ (k * (q - 1))) * ψ y ^ k := by simp only [map_mul, map_pow]; ring
      _ = ψ y ^ k := by rw [h1, one_mul]

theorem isUnit_res {W : Scheme.{0}} (s : Γ(W, ⊤)) :
    IsUnit ((Scheme.Γ.map (W.basicOpen s).ι.op).hom s) := by
  set O := W.basicOpen s
  rw [Scheme.Γ_map_op]
  refine RingedSpace.isUnit_of_isUnit_germ O.toScheme.toRingedSpace ⊤ _ (fun y _ => ?_)
  have hy : y ∈ O.toScheme.basicOpen (O.ι.appTop s) := by
    rw [← Scheme.preimage_basicOpen_top]
    show O.ι y ∈ O
    exact y.2
  exact (Scheme.mem_basicOpen_top _ _ _).mp hy

end LateralTheory.E.E8.TwSec.Gen

namespace LateralTheory.E.E8.TwSec.Gen

theorem map_mk {q : ℕ} (j : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ξ : Prim q A) (r : ULift.{1} (ZMod q)) :
    ((twF q j).map f).hom (Submodule.Quotient.mk (p := twRel q j A) (Finsupp.single ξ r)) =
      Submodule.Quotient.mk (p := twRel q j B) (Finsupp.single (ξ.map f.hom) r) := by
  change Submodule.Quotient.mk (Finsupp.mapDomain _ (Finsupp.single ξ r)) = _
  rw [Finsupp.mapDomain_single]

theorem mk_pow {q : ℕ} (j : ℤ) {B : CommRingCat.{0}} (ζ ξ : Prim q B) (k : ℕ) (hk : k < q) (hc : k.Coprime q)
    (h : ξ.1 = ζ.1 ^ k) :
    (Submodule.Quotient.mk (p := twRel q j B) (Finsupp.single ξ 1) : (twF q j).obj B) =
      ULift.up ((((ZMod.unitOfCoprime k hc) ^ j : (ZMod q)ˣ)) : ZMod q) • twCls j ζ := by
  unfold twCls
  have h1 : (ULift.up ((((ZMod.unitOfCoprime k hc) ^ j : (ZMod q)ˣ)) : ZMod q) : ULift.{1} (ZMod q)) •
      (Submodule.Quotient.mk (p := twRel q j B) (Finsupp.single ζ 1)) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((((ZMod.unitOfCoprime k hc) ^ j : (ZMod q)ˣ)) : ZMod q))) := by
    rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  refine Eq.trans ?_ h1.symm
  rw [Submodule.Quotient.eq]
  refine Submodule.subset_span ⟨ζ, ξ, ZMod.unitOfCoprime k hc, ?_, rfl⟩
  rw [h, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

theorem res_le {q : ℕ} (j : ℤ) {W : Scheme.{0}} {O O' : W.Opens} (h : O' ≤ O) {x y : (twF q j).obj Γ(W, ⊤)}
    (e : ((twF q j).map (Scheme.Γ.map O.ι.op)).hom x = ((twF q j).map (Scheme.Γ.map O.ι.op)).hom y) :
    ((twF q j).map (Scheme.Γ.map O'.ι.op)).hom x = ((twF q j).map (Scheme.Γ.map O'.ι.op)).hom y := by
  rw [← W.homOfLE_ι h, op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp]
  exact congrArg (ModuleCat.Hom.hom ((twF q j).map (Scheme.Γ.map (W.homOfLE h).op))) e

theorem core {q : ℕ} [NeZero q] (j : ℤ) {W : Scheme.{0}} (ζ ξ : Prim q Γ(W, ⊤)) (w0 : W) :
    ∃ (O : W.Opens) (c : ZMod q), w0 ∈ O ∧
      ((twF q j).map (Scheme.Γ.map O.ι.op)).hom (Submodule.Quotient.mk (p := twRel q j Γ(W, ⊤)) (Finsupp.single ξ 1)) =
        ((twF q j).map (Scheme.Γ.map O.ι.op)).hom (ULift.up c • twCls j ζ) := by
  obtain ⟨k, hk, hc, e⟩ := exists_pow (W.Γevaluation w0).hom ζ ξ
  have hq : ((q : ℕ) : W.residueField w0) ≠ 0 := by
    have := ζ.2.1.map (W.Γevaluation w0).hom
    simpa using this.ne_zero
  obtain ⟨h1, h2⟩ := key_ring (W.Γevaluation w0).hom ξ.1 ζ.1 q k hq (prim_pow_eq_one ξ) (prim_pow_eq_one ζ) e
  refine ⟨W.basicOpen (∑ b ∈ Finset.range q, (ξ.1 * ζ.1 ^ (k * (q - 1))) ^ b),
    (((ZMod.unitOfCoprime k hc) ^ j : (ZMod q)ˣ) : ZMod q),
    (W.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) w0 trivial _).mp h1, ?_⟩
  have hs := h2 _ (Scheme.Γ.map (W.basicOpen (∑ b ∈ Finset.range q, (ξ.1 * ζ.1 ^ (k * (q - 1))) ^ b)).ι.op).hom
    (isUnit_res _)
  refine (map_mk j _ ξ 1).trans ?_
  refine Eq.trans ?_ (LinearMap.map_smul _ _ _).symm
  refine Eq.trans ?_ (congrArg _ (map_mk j _ ζ 1).symm)
  exact mk_pow j _ _ k hk hc hs

end LateralTheory.E.E8.TwSec.Gen

namespace LateralTheory.E.E8.TwSec

open Gen in
theorem LeafTwGen_of : LeafTwGen := by
  intro q _ j W ζ t w0
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (twRel q j Γ(W, ⊤)) t
  induction f using Finsupp.induction_linear with
  | zero =>
    refine ⟨⊤, 0, trivial, ?_⟩
    have hm : (Submodule.Quotient.mk 0 : (twF q j).obj Γ(W, ⊤)) = 0 := Submodule.Quotient.mk_zero _
    have h0 : (ULift.up (0 : ZMod q) : ULift.{1} (ZMod q)) • twCls j ζ = 0 := zero_smul _ _
    rw [hm, h0]
    exact rfl
  | add f g hf hg =>
    obtain ⟨O1, c1, h1, e1⟩ := hf
    obtain ⟨O2, c2, h2, e2⟩ := hg
    refine ⟨O1 ⊓ O2, c1 + c2, ⟨h1, h2⟩, ?_⟩
    have hm : (Submodule.Quotient.mk (f + g) : (twF q j).obj Γ(W, ⊤)) =
        (Submodule.Quotient.mk f : (twF q j).obj Γ(W, ⊤)) + (Submodule.Quotient.mk g : (twF q j).obj Γ(W, ⊤)) :=
      Submodule.Quotient.mk_add _
    rw [hm]
    refine (LinearMap.map_add _ _ _).trans ?_
    rw [res_le j inf_le_left e1, res_le j inf_le_right e2]
    refine (LinearMap.map_add _ _ _).symm.trans ?_
    congr 1
    exact (add_smul _ _ _).symm
  | single ξ r =>
    obtain ⟨O, c, h, e⟩ := core j ζ ξ w0
    refine ⟨O, r.down * c, h, ?_⟩
    have hr : Finsupp.single ξ r = r • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    have hm : (Submodule.Quotient.mk (r • Finsupp.single ξ (1 : ULift.{1} (ZMod q))) : (twF q j).obj Γ(W, ⊤)) =
        r • (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q j).obj Γ(W, ⊤)) :=
      Submodule.Quotient.mk_smul _ _ _
    rw [hr, hm]
    refine (LinearMap.map_smul _ _ _).trans ?_
    rw [e]
    refine (LinearMap.map_smul _ _ _).symm.trans ?_
    congr 1
    exact smul_smul _ _ _

end LateralTheory.E.E8.TwSec
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwPairUniquePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairUniquePf

def PairHtpy {R : Type} [CommRing R] {I J K : Cx R} (μ μ' : Pair I J K) : Prop :=
  ∃ h : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w + 1 →
      Sec (I.X s) U →ₗ[ULift.{1} R] Sec (J.X t) U →ₗ[ULift.{1} R] Sec (K.X w) U,
    (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (hw : s + t = w + 1) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.res g (h U s t w hw a b) = h V s t w hw (Sec.res g a) (Sec.res g b)) ∧
    ∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      μ.mul U s t w hw a b - μ'.mul U s t w hw a b =
        Sec.map (K.d (w - 1) w) (h U s t (w - 1) (by omega) a b) +
          h U (s + 1) t w (by omega) (Sec.map (I.d s (s + 1)) a) b +
          s.negOnePow • h U s (t + 1) w (by omega) a (Sec.map (J.d t (t + 1)) b)

def LeafTwPairHtpy : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) (μ μ' : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j)))),
  IsTwPair μ → IsTwPair μ' → PairHtpy μ μ'

def LeafHtpyAW : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ μ' : Pair I J K), PairHtpy μ μ' →
  ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ'.IsAW hk α.1 β.1 γ'.1 →
    CohomologyClass.mk γ = CohomologyClass.mk γ'

theorem cup_eq_of_aw {R : Type} [CommRing R] {I J K : Cx R} (hc : LateralTheory.E.CupProductRingLaws.LeafCupSpec) (μ μ' : Pair I J K)
    (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (hAW : ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
      (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ'.IsAW hk α.1 β.1 γ'.1 →
      CohomologyClass.mk γ = CohomologyClass.mk γ') :
    μ.cup E hk = μ'.cup E hk := by
  obtain ⟨ex, sp⟩ := hc R μ E hk
  obtain ⟨ex', sp'⟩ := hc R μ' E hk
  ext a b
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := ex α β
  obtain ⟨γ', hγ'⟩ := ex' α β
  rw [sp α β γ hγ, sp' α β γ' hγ']
  exact hAW α β γ γ' hγ hγ'

end LateralTheory.E.LeafTwPairUniquePf

open LateralTheory.E.LeafTwPairUniquePf in
theorem LateralTheory.E.CupProductRingLaws.LeafTwPairUnique_of (hc : LateralTheory.E.CupProductRingLaws.LeafCupSpec) (hh : LeafTwPairHtpy)
    (ha : LeafHtpyAW) : LateralTheory.E.CupProductRingLaws.LeafTwPairUnique := by
  intro q _ i j μ μ' hμ hμ' E n m k hk
  exact cup_eq_of_aw hc μ μ' E hk (ha (ZMod q) μ μ' (hh q i j μ μ' hμ hμ') E hk)
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwPtPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec

theorem twF_res_comp {q : ℕ} (j : ℤ) {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : (twF q j).obj Γ(Z, ⊤)) :
    ((twF q j).map (Scheme.Γ.map (a ≫ b).op)).hom x =
      ((twF q j).map (Scheme.Γ.map a.op)).hom (((twF q j).map (Scheme.Γ.map b.op)).hom x) := by
  rw [op_comp, Functor.map_comp, Functor.map_comp]; rfl

theorem twF_map_cls {q : ℕ} (j : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ζ : Prim q A) (c : ZMod q) :
    ((twF q j).map f).hom (ULift.up c • twCls j ζ) = ULift.up c • twCls j (ζ.map f.hom) := by
  rw [map_smul]
  congr 1
  unfold twCls
  change Submodule.mapQ _ _ _ (twRel_le q j f.hom) _ = _
  rw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem twF_eq_zero_of_not_unit {q : ℕ} (j : ℤ) {A : CommRingCat.{0}} (hq : ¬ IsUnit (q : A)) (t : (twF q j).obj A) :
    t = 0 := by
  haveI : IsEmpty (Prim q A) := ⟨fun ζ => hq ζ.2.1⟩
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  rw [Subsingleton.elim f 0]
  exact Submodule.Quotient.mk_zero _

theorem LeafTwPt_of (hA : LeafTwAdj) (hG : LeafTwGen) (hF : LeafTwFieldZ) : LeafTwPt := by
  intro q _ j U u t V g v hgv ht
  by_cases hq : IsUnit (q : Γ(U, ⊤))
  swap
  · refine ⟨U, 𝟙 U, inferInstance, ⟨u, rfl⟩, ?_⟩
    rw [twF_eq_zero_of_not_unit j hq t]; exact map_zero _
  obtain ⟨W₁, w₁, hw₁, ⟨w, hw⟩, ⟨ζ⟩⟩ := hA q U u hq
  haveI := hw₁
  obtain ⟨O, c, hwO, hO⟩ := hG q j W₁ ζ (((twF q j).map (Scheme.Γ.map w₁.op)).hom t) w
  have hO' : ((twF q j).map (Scheme.Γ.map (O.ι ≫ w₁).op)).hom t =
      ULift.up c • twCls j (ζ.map (Scheme.Γ.map O.ι.op).hom) := by
    rw [twF_res_comp, hO]; exact twF_map_cls j _ ζ c
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := O.ι ≫ w₁) (g := g)
    (⟨w, hwO⟩ : O.toScheme) v (by rw [hgv]; exact hw)
  have hc : c = 0 := by
    let P := pullback (O.ι ≫ w₁) g
    let φ := P.evaluation ⊤ p trivial
    have e : ((twF q j).map (Scheme.Γ.map (pullback.fst (O.ι ≫ w₁) g ≫ O.ι ≫ w₁).op)).hom t = 0 := by
      rw [pullback.condition, twF_res_comp, ht, map_zero]
    rw [twF_res_comp, hO', twF_map_cls] at e
    have key := twF_map_cls j φ (Prim.map (Scheme.Γ.map (pullback.fst (O.ι ≫ w₁) g).op).hom
      (Prim.map (Scheme.Γ.map O.ι.op).hom ζ)) c
    exact hF q j (P.residueField p) (Field.toIsField _) _ c
      (key.symm.trans ((congrArg (fun x => ((twF q j).map φ).hom x) e).trans (map_zero _)))
  refine ⟨O, O.ι ≫ w₁, inferInstance, ⟨⟨w, hwO⟩, hw⟩, ?_⟩
  rw [hO', hc]
  exact zero_smul (ULift (ZMod q)) _

end LateralTheory.E.E8.TwSec
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocallyConstantH0
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut

namespace LateralTheory.E.LocallyConstantH0

def gam {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) : Prim q Γ(Spec (CommRingCat.of B), ⊤) :=
  ζ.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom

def IsLCMap (q : ℕ) [NeZero q] (i : ℤ)
    (m : ∀ (B : Type) [CommRing B], Prim q B → (LocallyConstant (PrimeSpectrum B) (ZMod q) →+ Sec (tw q i) (Spec (CommRingCat.of B)))) :
    Prop :=
  (∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C) (ζ : Prim q B) (φ : LocallyConstant (PrimeSpectrum B) (ZMod q)),
      Sec.res (Spec.map (CommRingCat.ofHom f)) (m B ζ φ) = m C (ζ.map f) (lcMap f φ)) ∧
  ∀ (B : Type) [CommRing B] (ζ : Prim q B) (c : ZMod q), m B ζ (LocallyConstant.const _ c) = c.val • twGen i (gam ζ)

def LCMap : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ m, IsLCMap q i m

def LCBij : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) m, IsLCMap q i m →
  ∀ (B : Type) [CommRing B] (ζ : Prim q B), Function.Bijective (m B ζ)

theorem localConstant_H0 (hM : LCMap) (hB : LCBij) : LateralTheory.E.t_E1Cut.EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions := by
  intro hA9 q _ i
  obtain ⟨m, hm⟩ := hM q i
  obtain ⟨-, e0, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  refine ⟨fun B _ ζ => (AddEquiv.ofBijective (m B ζ) (hB q i m hm B ζ)).trans (e0 (Spec (CommRingCat.of B))), ?_⟩
  intro B C _ _ f ζ φ
  simp only [AddEquiv.trans_apply, AddEquiv.ofBijective_apply]
  rw [hnat, hm.1]

end LateralTheory.E.LocallyConstantH0
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PullInjOfIso
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.MVPf

def MVSpc : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  ∀ n : ℤ, (∀ c : H R (pullback f g) F n, ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) →
  ∀ x : H R E F (n + 1), pull R f F _ x = 0 → pull R g F _ x = 0 → x = 0

def StdCover : Prop := ∀ (R : Type) [CommRing R] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  Cover2 R (spMap (algebraMap S (Localization.Away f))) (spMap (algebraMap S (Localization.Away g)))

def StdPB : Prop := ∀ (S : Type) [CommRing S] (f g : S),
  ∃ e : sp (Localization.Away (f * g)) ⟶
      pullback (spMap (algebraMap S (Localization.Away f))) (spMap (algebraMap S (Localization.Away g))),
    IsIso e ∧ e ≫ pullback.fst _ _ = spMap (LateralTheory.E.t_E1Cut.rL f g) ∧ e ≫ pullback.snd _ _ = spMap (LateralTheory.E.t_E1Cut.rR f g)

theorem pull_inj_of_iso (R : Type) [CommRing R] {E E' : Spc} (e : E ⟶ E') [IsIso e] (F : Shv R) (n : ℤ) :
    Function.Injective (pull R e F n) := by
  intro x y h
  have hx : pull R (inv e) F n (pull R e F n x) = x := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  have hy : pull R (inv e) F n (pull R e F n y) = y := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  rw [← hx, ← hy, h]

end LateralTheory.E.MVPf

open LateralTheory.E.MVPf in
theorem LateralTheory.E.t_E1Cut.MV_of (h1 : MVSpc) (h2 : StdCover) (h3 : StdPB) : LateralTheory.E.t_E1Cut.MV := by
  intro hA1 R _ F S _ f g hfg n hc x hxf hxg
  refine h1 hA1 R F _ _ (h2 R S f g hfg) n ?_ x hxf hxg
  intro c
  obtain ⟨e, he, hfst, hsnd⟩ := h3 S f g
  obtain ⟨a, b, hab⟩ := hc (pull R e F n c)
  refine ⟨a, b, pull_inj_of_iso R e F n ?_⟩
  rw [hab, map_sub, ← pull_comp, ← pull_comp, hfst, hsnd]
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.QAClosedPf
section
noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.QAClosedPf

open LateralTheory.E.t_E1Cut

theorem aic_of_surj {T S : Type} [CommRing T] [CommRing S] (π : T →+* S) (hT : AIC T)
    (hπ : Function.Surjective π) : AIC S := by
  intro p hp hdeg
  have hl : p ∈ lifts π := (lifts_iff_coeff_lifts p).2 fun n => hπ _
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hp
  obtain ⟨a, ha⟩ := hT q hqm (hqd ▸ hdeg)
  refine ⟨π a, ?_⟩
  rw [← hq, eval_map, eval₂_at_apply, ha, map_zero]

theorem aic_away {T : Type} [CommRing T] [IsDomain T] (hT : AIC T) (t : T) (ht : t ≠ 0) :
    AIC (Localization.Away t) := by
  classical
  have : IsDomain (Localization.Away t) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  intro p hp hdeg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (Submonoid.powers t)
    (p.support.image p.coeff)
  set c : Localization.Away t := algebraMap T _ b
  have hcu : IsUnit c := IsLocalization.map_units _ b
  have hl : p.scaleRoots c ∈ lifts (algebraMap T (Localization.Away t)) := by
    refine (lifts_iff_coeff_lifts _).2 fun i => ?_
    rw [coeff_scaleRoots]
    by_cases hi : i ∈ p.support
    · have hle : i ≤ p.natDegree := le_natDegree_of_mem_supp i hi
      rcases lt_or_eq_of_le hle with hlt | heq
      · obtain ⟨z, hz⟩ := hb _ (Finset.mem_image_of_mem _ hi)
        refine ⟨z * b ^ (p.natDegree - i - 1), ?_⟩
        rw [map_mul, hz, Algebra.smul_def, map_pow]
        rw [show c ^ (p.natDegree - i) = c * c ^ (p.natDegree - i - 1) by
          rw [← pow_succ']; congr 1; omega]
        simp only [c]
        ring
      · subst heq
        refine ⟨1, ?_⟩
        rw [hp.coeff_natDegree, Nat.sub_self, pow_zero, one_mul, map_one]
    · rw [Polynomial.notMem_support_iff.1 hi]
      exact ⟨0, by simp⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff c).2 hp)
  rw [natDegree_scaleRoots] at hqd
  obtain ⟨a, ha⟩ := hT q hqm (hqd ▸ hdeg)
  refine ⟨hcu.unit⁻¹ * algebraMap T _ a, ?_⟩
  have h1 : eval (algebraMap T _ a) (p.scaleRoots c) = 0 := by
    rw [← hq, eval_map, eval₂_at_apply, ha, map_zero]
  have h2 : algebraMap T (Localization.Away t) a = (RingHom.id _) c * (hcu.unit⁻¹ * algebraMap T _ a) := by
    rw [RingHom.id_apply, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  rw [eval, h2, scaleRoots_eval₂_mul] at h1
  rw [eval]
  exact (mul_eq_zero.1 h1).resolve_left (by simpa using (hcu.pow _).ne_zero)

theorem QAClosed_of : QAClosed := by
  intro S _ hS
  obtain ⟨T, _, _, π, hT, hπ⟩ := hS
  refine ⟨aic_of_surj π hT hπ, ?_, ?_⟩
  · intro f
    obtain ⟨t, rfl⟩ := hπ f
    by_cases ht : t = 0
    · have hu : IsUnit (algebraMap S (Localization.Away (π t)) (π t)) :=
        IsLocalization.Away.algebraMap_isUnit _
      rw [show algebraMap S (Localization.Away (π t)) (π t) = 0 by rw [ht, map_zero, map_zero]] at hu
      have : Subsingleton (Localization.Away (π t)) := subsingleton_of_zero_eq_one (isUnit_zero_iff.1 hu)
      exact ⟨T, inferInstance, inferInstance, (algebraMap S _).comp π, hT, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
    · have : IsDomain (Localization.Away t) :=
        IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
      have : IsLocalization (Submonoid.map π (Submonoid.powers t)) (Localization.Away (π t)) := by
        rw [Submonoid.map_powers]; infer_instance
      exact ⟨Localization.Away t, inferInstance, inferInstance, _, aic_away hT t ht,
        IsLocalization.map_surjective_of_surjective (Submonoid.powers t) (Localization.Away t)
          (Localization.Away (π t)) hπ⟩
  · intro J
    exact ⟨T, inferInstance, inferInstance, (Ideal.Quotient.mk J).comp π, hT,
      (Ideal.Quotient.mk_surjective).comp hπ⟩

end LateralTheory.E.QAClosedPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ZarLocalPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.ZarLocalPf

def LocSH : Prop := ∀ (S : Type) [CommRing S], AIC S → ∀ p : PrimeSpectrum S, SH (Localization.AtPrime p.asIdeal)

def LocDiag : Prop := ∀ (S : Type) [CommRing S] (p : PrimeSpectrum S),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D),
    Nonempty (IsColimit c) ∧ (SH (Localization.AtPrime p.asIdeal) → SH c.pt) ∧
    ∃ (j0 : J) (a : S →+* D.obj j0), ∀ (k : J) (m : j0 ⟶ k), ∃ f : S, f ∉ p.asIdeal ∧
      ∃ r : D.obj k →+* Localization.Away f, r.comp ((D.map m).hom.comp a) = algebraMap S (Localization.Away f)

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem ZarLocal_of (hSH : LocSH) (hD : LocDiag) : LateralTheory.E.t_E1Cut.ZarLocal := by
  intro hB1 hB2 q S _ hS hq n i hn x p
  obtain ⟨J, _, _, D, c, ⟨hc⟩, hpt, j0, a, hk⟩ := hD S p
  have hsh : SH c.pt := hpt (hSH S hS p)
  set y := pull _ (spMap a) _ _ x with hy
  have hqa : IsUnit ((q : ℕ) : D.obj j0) := by simpa using hq.map a
  have h0 : pull _ (spMap (c.ι.app j0).hom) _ _ y = 0 := by
    exact @Subsingleton.elim _ (hB2 (ZMod q) c.pt hsh (tw q i) n hn) _ _
  obtain ⟨k, m, hm⟩ := (hB1 q D c hc n i).2 j0 y hqa h0
  obtain ⟨f, hf, r, hr⟩ := hk k m
  refine ⟨f, hf, ?_⟩
  rw [← hr, spMap_comp, pull_comp, spMap_comp, pull_comp, ← hy, hm, map_zero]

end LateralTheory.E.ZarLocalPf
end
end

