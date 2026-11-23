module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplittingAbsenceSpreads
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0087
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Hilbert90LocalOfCocycleTensor
section
open TensorProduct

namespace GlobalTheory.FlatDescent

theorem hilbert90_local_of_cocycle : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R] [Module.Finite R S]
    [Module.FaithfullyFlat R S] (c : (S ⊗[R] S)ˣ),
    Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) (c : S ⊗[R] S) *
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S) =
      Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S) →
    ∀ p : Ideal R, p.IsPrime → ∃ r ∉ p, ∃ m s : S, ∃ n : ℕ,
      (m ⊗ₜ[R] (1 : S)) * (c : S ⊗[R] S) = (1 : S) ⊗ₜ[R] m ∧ m * s = algebraMap R S r ^ n := by
  intro R S _ _ _ _ _ _ c hc p hp
  classical
  let θ : S →ₗ[S] S ⊗[R] S := LinearMap.toSpanSingleton S (S ⊗[R] S) (c : S ⊗[R] S)
  have hθ : ∀ n, θ n = (n ⊗ₜ[R] (1 : S)) * (c : S ⊗[R] S) := fun n => by
    simp [θ, Algebra.smul_def]

  let ψ : (S ⊗[R] S) ⊗[R] S →ₐ[R] S ⊗[R] S :=
    Algebra.TensorProduct.lift (S := R) (AlgHom.id R (S ⊗[R] S))
      (Algebra.TensorProduct.includeRight) (fun _ _ => Commute.all _ _)
  have h1 : ∀ x, ψ (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) x) = x := by
    intro x; simp [ψ, ← Algebra.TensorProduct.one_def]
  have h2 : ∀ x, ψ (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S))
      (AlgHom.id R S) x) = (1 : S) ⊗ₜ[R] Algebra.TensorProduct.lmul' R x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, tmul_add]
    | tmul a b => simp [ψ]
  have h3 : ∀ x, ψ (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S))
      (AlgHom.id R S) x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b => simp [ψ]
  have hμ : Algebra.TensorProduct.lmul' R (c : S ⊗[R] S) = 1 := by
    have h := congrArg ψ hc
    rw [map_mul, h1, h2, h3] at h
    have h' : (1 : S) ⊗ₜ[R] Algebra.TensorProduct.lmul' R (c : S ⊗[R] S) = (1 : S) ⊗ₜ[R] (1 : S) :=
      (Units.mul_right_inj c).1 (h.trans (mul_one _).symm)
    exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S) S h'
  have hact : ∀ x, act R S S x = Algebra.TensorProduct.lmul' R x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b => simp
  have hcounit : ∀ n, act R S S (θ n) = n := by
    intro n
    have hθ' : θ n = n • (c : S ⊗[R] S) := rfl
    rw [hθ', (act R S S).map_smul, hact, hμ, smul_eq_mul, mul_one]

  let e := (TensorProduct.assoc R S S S)
  have hL0 : ∀ (a b : S) (z : S ⊗[R] S), a ⊗ₜ[R] (b • z) =
      e (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) (a ⊗ₜ[R] b) *
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S))
          (AlgHom.id R S) z) := by
    intro a b z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add, smul_add, tmul_add]
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.includeLeft_apply, AlgHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, e, TensorProduct.assoc_tmul, smul_tmul',
        smul_eq_mul]
  have hL : ∀ x : S ⊗[R] S, (θ.restrictScalars R).lTensor S x =
      e (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) x *
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S))
          (AlgHom.id R S) (c : S ⊗[R] S)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, add_mul]
    | tmul a b =>
      rw [LinearMap.lTensor_tmul, LinearMap.coe_restrictScalars]
      exact hL0 a b _
  have hR : ∀ x : S ⊗[R] S, (TensorProduct.mk R S S 1).lTensor S x =
      e (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S))
        (AlgHom.id R S) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b => simp [e]
  have hsmul : ∀ (g : S →ₗ[R] S ⊗[R] S) (n : S) (x : S ⊗[R] S),
      g.lTensor S (n • x) = n • g.lTensor S x := by
    intro g n x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
    | tmul a b => simp [smul_tmul']
  have hcoassoc : ∀ n, (θ.restrictScalars R).lTensor S (θ n) = (TensorProduct.mk R S S 1).lTensor S (θ n) := by
    intro n
    have hθ' : θ n = n • (c : S ⊗[R] S) := rfl
    rw [hθ', hsmul, hsmul, hL, hR, hc]
  have hD : IsDescentDatum θ := ⟨hcounit, hcoassoc⟩
  haveI : Module.Invertible R (invariants θ) := hD.invertible_invariants

  obtain ⟨f, m, hfm⟩ : ∃ (f : Module.Dual R (invariants θ)) (m : invariants θ), f m ∉ p := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨T, hT⟩ := ((Module.Invertible.linearEquiv R (invariants θ)).symm 1).exists_finset
    have h1 : (1 : R) = ∑ i ∈ T, i.1 i.2 := by
      have := congrArg (Module.Invertible.linearEquiv R (invariants θ)) hT
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Module.Invertible.linearEquiv, map_sum] using this
    exact hp.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ Ideal.sum_mem _ fun i _ => hcon i.1 i.2))
  have hcomm : ∀ x : invariants θ, f m • x = f x • m := by
    intro x
    have := congrArg (TensorProduct.lift ((LinearMap.lsmul R (invariants θ)).comp f))
      (Module.Invertible.tmul_comm (m₁ := m) (m₂ := x))
    simpa using this
  obtain ⟨y, hy⟩ := hD.bijective_extend.2 1
  have hspan : ∀ y : S ⊗[R] invariants θ,
      algebraMap R S (f m) * extend S (invariants θ) y ∈ Ideal.span {(m : S)} := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), mul_add]; exact Ideal.add_mem _ hx hy
    | tmul b x =>
      have hx : algebraMap R S (f m) * (x : S) = algebraMap R S (f x) * (m : S) := by
        have := congrArg Subtype.val (hcomm x)
        simpa [Algebra.smul_def] using this
      rw [extend_tmul, smul_eq_mul, mul_left_comm, hx, ← mul_assoc]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (hspan y)
  refine ⟨f m, hfm, m, s, 1, ?_, ?_⟩
  · rw [← hθ]; exact mem_invariants.1 m.2
  · rw [pow_one, mul_comm, hs, hy, mul_one]

end GlobalTheory.FlatDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointEqOfOpenCover
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

set_option autoImplicit false

namespace GlobalTheory.HilbGlue

theorem idealSheaf_ext_of_openImmersions {P : Scheme.{0}} {ι : Type*} {X : ι → Scheme.{0}}
    (f : ∀ i, X i ⟶ P) [∀ i, IsOpenImmersion (f i)] (hf : ∀ x : P, ∃ i y, f i y = x)
    (I J : P.IdealSheafData) (h : ∀ i, I.comap (f i) = J.comap (f i)) : I = J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := Σ i, (X i).affineOpens)
    (fun a => ⟨f a.1 ''ᵁ a.2.1, a.2.2.image_of_isOpenImmersion (f a.1)⟩) ?_ ?_
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨i, y, rfl⟩ := hf x
    obtain ⟨W, hW, hyW⟩ : ∃ W : (X i).Opens, IsAffineOpen W ∧ y ∈ W := by
      obtain ⟨_, ⟨W, hW, rfl⟩, hy, -⟩ := (X i).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ y) isOpen_univ
      exact ⟨W, hW, hy⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, W, hW⟩, ⟨y, hyW, rfl⟩⟩
  · rintro ⟨i, W⟩
    have e := congrArg (fun K : (X i).IdealSheafData => K.ideal W) (h i)
    simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at e
    exact Ideal.comap_injective_of_surjective _
      ((ConcreteCategory.bijective_of_isIso ((f i).appIso W).inv).2) e

end GlobalTheory.HilbGlue

theorem GlobalTheory.HilbGlue.HPt.ext_openCover : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x x' : GlobalTheory.HilbGlue.HPt z r Y), (∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x = GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x') → x = x' := by
  intro S Z z r Y 𝒰 x x' e
  obtain ⟨g, I⟩ := x
  obtain ⟨g', I'⟩ := x'
  obtain rfl : g = g' := 𝒰.hom_ext _ _ fun i => congrArg Sigma.fst (e i)
  rw [HPt.mk_eq_mk_iff]
  have hP : ∀ i : 𝒰.I₀, IsPullback (pullback.snd z (𝒰.f i ≫ g)) (bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl) (𝒰.f i)
      (pullback.snd z g) := fun i => (isPullback_bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl).flip
  haveI : ∀ i : 𝒰.I₀, IsOpenImmersion (bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl) := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hP i) inferInstance
  refine idealSheaf_ext_of_openImmersions (ι := 𝒰.I₀) (X := fun i => pullback z (𝒰.f i ≫ g)) (fun i => bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl) ?_ I.1 I'.1 fun i => ?_
  · intro x
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (pullback.snd z g x)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd z g)
      (g := 𝒰.f i) x y hy.symm
    refine ⟨i, (isPullback_bc z (𝒰.f i) g (𝒰.f i ≫ g) rfl).isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw]
  · have := (HPt.mk_eq_mk_iff _ _).1 (e i)
    exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointGlueOpenCover
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue

namespace GlobalTheory.HilbGlue

section
variable {S Z : Scheme.{0}} (z : Z ⟶ S)

theorem bc_fst {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    bc z c g k w ≫ pullback.fst z g = pullback.fst z k := by
  simp only [bc, pullback.map, pullback.lift_fst, Category.comp_id]

theorem bc_snd {T T' : Scheme.{0}} (c : T' ⟶ T) (g : T ⟶ S) (k : T' ⟶ S) (w : c ≫ g = k) :
    bc z c g k w ≫ pullback.snd z g = pullback.snd z k ≫ c := by
  simp only [bc, pullback.map, pullback.lift_snd]

end

theorem isFinFlatRk_of_cover {V Y : Scheme.{0}} (g : V ⟶ Y) (𝒰 : Y.OpenCover) (r : ℕ)
    (h : ∀ i, ∃ (Q : Scheme.{0}) (p : Q ⟶ V) (q : Q ⟶ 𝒰.X i), IsPullback p q g (𝒰.f i) ∧ IsFinFlatRk q r) :
    IsFinFlatRk g r := by
  choose Q p q hP hq using h
  have i1 : IsZariskiLocalAtTarget @IsFinite.{0} := by
    set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
  have i2 : IsZariskiLocalAtTarget @Flat.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0})
  have hq' : ∀ i, IsFinFlatRk (pullback.snd g (𝒰.f i)) r := fun i => by
    rw [← (hP i).isoPullback_inv_snd]
    exact (hq i).iso_comp _
  have hF : IsFinite g := IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) 𝒰 fun i => (hq' i).1
  have hL : Flat g := IsZariskiLocalAtTarget.of_openCover (P := @Flat) 𝒰 fun i => (hq' i).2.1
  refine ⟨hF, hL, fun y => ?_⟩
  obtain ⟨i, y', rfl⟩ := 𝒰.exists_eq y
  rw [← Scheme.Hom.finrank_of_isPullback (p i) (q i) g (𝒰.f i) (hP i) y', (hq i).2.2]

theorem HPt.exists_glue : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x : ∀ i, GlobalTheory.HilbGlue.HPt z r (𝒰.X i)), (∀ i j (R : Scheme.{0}) (b : R ⟶ 𝒰.X i) (c : R ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → GlobalTheory.HilbGlue.HPt.map b (x i) = GlobalTheory.HilbGlue.HPt.map c (x j)) → ∃ y : GlobalTheory.HilbGlue.HPt z r Y, ∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) y = x i := by
  intro S Z z r Y 𝒰 x hx
  obtain ⟨f, hf⟩ : ∃ f : Y ⟶ S, ∀ i, 𝒰.f i ≫ f = (x i).1 :=
    ⟨𝒰.glueMorphisms (fun i => (x i).1) fun i j =>
      congrArg Sigma.fst (hx i j _ _ _ pullback.condition), fun i => 𝒰.ι_glueMorphisms _ _ i⟩
  let e : ∀ i, pullback z (x i).1 ⟶ pullback z f := fun i => bc z (𝒰.f i) f (x i).1 (hf i)
  have hP : ∀ i, IsPullback (e i) (pullback.snd z (x i).1) (pullback.snd z f) (𝒰.f i) :=
    fun i => isPullback_bc z _ _ _ (hf i)
  have he : ∀ i, IsOpenImmersion (e i) := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hP i).flip inferInstance
  have hcov : ∀ p : ↥(pullback z f), ∃ i, p ∈ Set.range (e i) := by
    intro p
    obtain ⟨i, y', hy'⟩ := 𝒰.exists_eq (pullback.snd z f p)
    obtain ⟨q, hq⟩ : p ∈ Set.range (pullback.fst (pullback.snd z f) (𝒰.f i)) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨y', hy'⟩
    refine ⟨i, (hP i).isoPullback.inv q, ?_⟩
    rw [← hq, ← Scheme.Hom.comp_apply, (hP i).isoPullback_inv_fst]
  have fi : ∀ i, e i ≫ pullback.fst z f = pullback.fst z (x i).1 := fun i => by
    simp only [e, bc, pullback.map, pullback.lift_fst, Category.comp_id]
  have hK : ∀ i j (Q : Scheme.{0}) (a : Q ⟶ pullback z (x i).1) (b : Q ⟶ pullback z (x j).1),
      a ≫ e i = b ≫ e j → (x i).2.1.comap a = (x j).2.1.comap b := by
    intro i j Q a b hab
    have hbc : (a ≫ pullback.snd z (x i).1) ≫ 𝒰.f i = (b ≫ pullback.snd z (x j).1) ≫ 𝒰.f j := by
      rw [Category.assoc, Category.assoc, ← (hP i).w, ← (hP j).w, reassoc_of% hab]
    have H := hx i j Q _ _ hbc
    have w : (a ≫ pullback.snd z (x i).1) ≫ (x i).1 = (b ≫ pullback.snd z (x j).1) ≫ (x j).1 :=
      congrArg Sigma.fst H
    have H' := (HPt.map_eq_mk_iff _ (x i) w ((x j).2.pull _ rfl)).1 H
    have hs : (a ≫ pullback.fst z (x i).1) ≫ z = 𝟙 Q ≫ (b ≫ pullback.snd z (x j).1) ≫ (x j).1 := by
      rw [Category.id_comp, ← w, Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨s, hs1, hs2⟩ : ∃ s : Q ⟶ pullback z ((b ≫ pullback.snd z (x j).1) ≫ (x j).1),
        s ≫ pullback.fst _ _ = a ≫ pullback.fst z (x i).1 ∧ s ≫ pullback.snd _ _ = 𝟙 Q :=
      ⟨pullback.lift _ _ hs, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have hfst : a ≫ pullback.fst z (x i).1 = b ≫ pullback.fst z (x j).1 := by
      rw [← fi i, ← fi j, reassoc_of% hab]
    have ha : a = s ≫ bc z (a ≫ pullback.snd z (x i).1) (x i).1 _ w := by
      apply pullback.hom_ext
      · rw [Category.assoc, bc_fst, hs1]
      · rw [Category.assoc, bc_snd, reassoc_of% hs2]
    have hb : b = s ≫ bc z (b ≫ pullback.snd z (x j).1) (x j).1 _ rfl := by
      apply pullback.hom_ext
      · rw [Category.assoc, bc_fst, hs1, hfst]
      · rw [Category.assoc, bc_snd, reassoc_of% hs2]
    have e1 : (x i).2.1.comap a = ((x i).2.1.comap (bc z (a ≫ pullback.snd z (x i).1) (x i).1 _ w)).comap s := by
      rw [← Scheme.IdealSheafData.comap_comp, ← ha]
    have e2 : (x j).2.1.comap b = ((x j).2.1.comap (bc z (b ≫ pullback.snd z (x j).1) (x j).1 _ rfl)).comap s := by
      rw [← Scheme.IdealSheafData.comap_comp, ← hb]
    rw [e1, e2, H']
    rfl
  obtain ⟨I, hI⟩ := GlobalTheory.T.exists_idealSheafData_glue_of_openImmersions GlobalTheory.T.exists_idealSheafData_of_compatible_ideals (ι := 𝒰.I₀) (fun i : 𝒰.I₀ => pullback z (x i).1) e he hcov (fun i : 𝒰.I₀ => (x i).2.1) hK
  have hfr : IsFinFlatRk (I.subschemeι ≫ pullback.snd z f) r := by
    refine isFinFlatRk_of_cover _ 𝒰 r fun i => ⟨(I.comap (e i)).subscheme, _, _,
      (isPullback_comap I (e i)).flip.paste_vert (hP i), ?_⟩
    have := (x i).2.2
    rw [← hI i] at this
    exact this
  refine ⟨⟨f, I, hfr⟩, fun i => ?_⟩
  exact (HPt.map_eq_mk_iff (𝒰.f i) ⟨f, I, hfr⟩ (hf i) (x i).2).2 (hI i)

end GlobalTheory.HilbGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypersurfacePartGeometricIrreducibleSpreads
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem hypersurface_part_preirreducible_spreads : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (i : σ), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) → (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : σ → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv i (MvPolynomial.map ψ f)) ≠ 0) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map φ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map φ g}) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map ψ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map ψ g}) := by
  intro A _ σ _ f g i h0 hd Ω _ _ φ hirr
  have h3 := _root_.GlobalTheory.hypersurface_part_no_splitting_factorisation Ω σ (MvPolynomial.map φ f) (MvPolynomial.map φ g) i f.totalDegree
    (hd Ω φ) hirr
  obtain ⟨a, I, ha, hI, h⟩ := _root_.GlobalTheory.splitting_absence_spreads A σ f g f.totalDegree Ω φ h3
  refine ⟨a, I, ha, hI, fun k _ _ ψ hψa hψI => ?_⟩
  refine GlobalTheory.T.hypersurface_diff_isPreirreducible_of_no_splitting k σ (MvPolynomial.map ψ f) (MvPolynomial.map ψ g) f.totalDegree
    (h0 k ψ) ?_ (h k ψ hψa hψI)
  exact Finset.sup_mono (MvPolynomial.support_map_subset ψ f)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealKilledByRingMapsWithPropertyLeKerApp
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem fromSpec_Sp_eq (R' : Type) [CommRing R'] {W : (Sp R').Opens} (hW : IsAffineOpen W) :
    hW.fromSpec = spMap ((Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫
      (Sp R').presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (𝟙 (Sp R')) (isAffineOpen_top (Sp R')) hW le_top
  rw [Category.comp_id, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  rw [← h]
  simp [spMap, Scheme.Hom.appLE]

theorem killIdeal_le_ker_app : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S),
    P R' x → P R'' (spMap g ≫ x)) →
  ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), P R' x →
    ∀ (V : S.Opens) (hV : IsAffineOpen V), killIdeal (ptQ P V hV) ≤ RingHom.ker (x.app V).hom := by
  intro S P hP R' _ x hx V hV a ha
  rw [RingHom.mem_ker]
  apply (Sp R').IsSheaf.section_ext
  intro p hp
  obtain ⟨W, hWa, hpW, hWle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Sp R').isBasis_affineOpens) hp
  refine ⟨W, hWle, hpW, ?_⟩
  have hW : IsAffineOpen W := hWa
  have e : hW.fromSpec ≫ x = spMap (x.appLE V W hWle).hom ≫ hV.fromSpec := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec x hV hW hWle]; rfl
  have hy : ptQ P V hV _ (x.appLE V W hWle).hom := by
    show P _ (spMap (x.appLE V W hWle).hom ≫ hV.fromSpec)
    rw [← e, fromSpec_Sp_eq]
    exact hP _ _ _ x hx
  have h0 := ha _ _ hy
  rw [map_zero]
  simpa [Scheme.Hom.appLE] using h0

end GlobalTheory.PtClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealRepresentsOfAwayCover
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem exists_pow_mul_eq_zero_of_represents_away {A : Type} [CommRing A]
    {Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop}
    (hbc : ∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (f : A →+* R'),
      Q R' f → Q R'' (g.comp f))
    (a : A) {Ja : Ideal (Localization.Away a)}
    (hJa : Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
      Q R' (h.comp (algebraMap A (Localization.Away a)))) Ja)
    {R' : Type} [CommRing R'] (f : A →+* R') (hf : Q R' f) (x : A)
    (hx : algebraMap A (Localization.Away a) x ∈ Ja) : ∃ m : ℕ, f a ^ m * f x = 0 := by
  have e : (Localization.awayMap f a).comp (algebraMap A (Localization.Away a)) =
      (algebraMap R' (Localization.Away (f a))).comp f := IsLocalization.map_comp _
  have h1 : Q _ ((algebraMap R' (Localization.Away (f a))).comp f) :=
    hbc _ _ (algebraMap R' (Localization.Away (f a))) f hf
  rw [← e] at h1
  have h2 := (hJa _ (Localization.awayMap f a)).1 h1 hx
  rw [RingHom.mem_ker, ← RingHom.comp_apply, e, RingHom.comp_apply,
    IsLocalization.map_eq_zero_iff (Submonoid.powers (f a))] at h2
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := h2
  exact ⟨m, hm⟩

theorem represents_of_away_cover : ∀ (A : Type) [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (f : A →+* R'),
    Q R' f → Q R'' (g.comp f)) →
  (∀ (R' : Type) [CommRing R'] (f : A →+* R') (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
    (∀ r ∈ t, Q (Localization.Away r) ((algebraMap R' (Localization.Away r)).comp f)) → Q R' f) →
  ∀ (s : Finset A), Ideal.span (s : Set A) = ⊤ →
  (∀ a ∈ s, ∃ J : Ideal (Localization.Away a),
    Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
      Q R' (h.comp (algebraMap A (Localization.Away a)))) J) →
  ∃ J : Ideal A, Represents Q J := by
  classical
  intro A _ Q hbc hloc s hs hJ
  choose! J' hJ' using hJ
  refine ⟨⨅ a ∈ s, (J' a).comap (algebraMap A (Localization.Away a)),
    fun R' _ f ↦ ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩⟩
  · intro x hx
    simp only [Submodule.mem_iInf, Ideal.mem_comap] at hx
    rw [RingHom.mem_ker]
    have hspan : Ideal.span ((f : A → R') '' (s : Set A)) = ⊤ := by
      rw [← Ideal.map_span, hs, Ideal.map_top]
    have := Submodule.mem_of_span_eq_top_of_smul_pow_mem (⊥ : Submodule R' R') _ hspan (f x) ?_
    · simpa using this
    rintro ⟨_, b, hb, rfl⟩
    obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_represents_away hbc b (hJ' b hb) f hf x (hx b hb)
    exact ⟨m, by simpa [smul_eq_mul] using hm⟩
  · apply hloc R' f (s.image f)
    · rw [Finset.coe_image, ← Ideal.map_span, hs, Ideal.map_top]
    intro r hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hr
    have e : (Localization.awayMap f a).comp (algebraMap A (Localization.Away a)) =
        (algebraMap R' (Localization.Away (f a))).comp f := IsLocalization.map_comp _
    rw [← e]
    refine ((hJ' a ha) _ (Localization.awayMap f a)).2 ?_
    intro j hj
    obtain ⟨⟨y, _, n, rfl⟩, hy⟩ := IsLocalization.surj (Submonoid.powers a) j
    simp only at hy
    have hyJ : algebraMap A (Localization.Away a) y ∈ J' a := hy ▸ Ideal.mul_mem_right _ _ hj
    have hb : ∀ b ∈ s, ∃ m : ℕ, algebraMap A (Localization.Away b) (a ^ m * y) ∈ J' b := by
      intro b hbs
      let p : A →+* (Localization.Away b ⧸ J' b) :=
        (Ideal.Quotient.mk (J' b)).comp (algebraMap A (Localization.Away b))
      have hp : Q _ p := ((hJ' b hbs) _ (Ideal.Quotient.mk (J' b))).2 (by rw [Ideal.mk_ker])
      obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_represents_away hbc a (hJ' a ha) p hp y hyJ
      refine ⟨m, ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [p] using hm
    choose! m hm using hb
    have hM : a ^ (s.sup m) * y ∈ ⨅ b ∈ s, (J' b).comap (algebraMap A (Localization.Away b)) := by
      simp only [Submodule.mem_iInf, Ideal.mem_comap]
      intro b hbs
      have : a ^ (s.sup m) * y = a ^ (s.sup m - m b) * (a ^ m b * y) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Finset.le_sup hbs)]
      rw [this, map_mul]
      exact Ideal.mul_mem_left _ _ (hm b hbs)
    have h0 := hf hM
    rw [RingHom.mem_ker, map_mul, map_pow] at h0
    rw [RingHom.mem_ker]
    have hu : IsUnit (Localization.awayMap f a (algebraMap A _ (a ^ n))) := by
      rw [← RingHom.comp_apply, e, RingHom.comp_apply, map_pow]
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f a)) (f a)).pow n
    have h3 : Localization.awayMap f a j * Localization.awayMap f a (algebraMap A _ (a ^ n)) = 0 := by
      rw [← map_mul, hy, ← RingHom.comp_apply, e, RingHom.comp_apply,
        IsLocalization.map_eq_zero_iff (Submonoid.powers (f a))]
      exact ⟨⟨_, s.sup m, rfl⟩, h0⟩
    exact (hu.mul_left_eq_zero).1 h3

end GlobalTheory.PtClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataExtOfOpenCoverStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheafData_ext_of_openCover' : ∀ {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : X, ∃ i y, f i y = x) →
    ∀ (I I' : X.IdealSheafData), (∀ i, I.comap (f i) = I'.comap (f i)) → I = I' := by
  first | (exact @GlobalTheory.HilbAff.idealSheafData_ext_of_openCover) | (exact GlobalTheory.HilbAff.idealSheafData_ext_of_openCover) | (intros; apply GlobalTheory.HilbAff.idealSheafData_ext_of_openCover  <;> assumption)
end

