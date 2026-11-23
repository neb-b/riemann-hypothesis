module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LinearIndependentOfCommSmul
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.linearIndependent_of_comm_smul {K G V : Type} [Field K] [AddCommGroup V] [Module K V]
    [Nontrivial V] (A : G → V →ₗ[K] V) (c : G → G → K) (hA : ∀ x, Function.Injective (A x))
    (h : ∀ x y v, A x (A y v) = c x y • A y (A x v)) (hc : Function.Injective c) :
    LinearIndependent K A := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro g hg i hi
  by_contra hgi

  have htwist : ∀ y, ∑ x ∈ s, (g x * (c x y - c i y)) • A x = 0 := by
    intro y
    ext v
    have h0 := LinearMap.congr_fun hg v
    have h1 := LinearMap.congr_fun hg (A y v)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.zero_apply] at h0 h1 ⊢
    have h2 : A y (∑ x ∈ s, (g x * c x y) • A x v) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← h1]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul, h x y v, smul_smul]
    have h3 : ∑ x ∈ s, (g x * c x y) • A x v = 0 :=
      hA y (by rw [h2, map_zero])
    simp_rw [mul_sub, sub_smul, Finset.sum_sub_distrib, h3, zero_sub, neg_eq_zero]
    have h4 : ∑ x ∈ s, (g x * c i y) • A x v = c i y • ∑ x ∈ s, g x • A x v := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [smul_smul, mul_comm]
    rw [h4, h0, smul_zero]
  have hothers : ∀ x ∈ s, x ≠ i → g x = 0 := by
    intro x hx hxi
    by_contra hgx
    apply hxi
    apply hc
    funext y
    have hrel : ∑ z ∈ s.erase i, (g z * (c z y - c i y)) • A z = 0 := by
      rw [← htwist y, ← Finset.sum_erase_add s _ hi, sub_self, mul_zero, zero_smul, add_zero]
    have := ih (s.erase i) (Finset.erase_ssubset hi) _ hrel x (Finset.mem_erase.2 ⟨hxi, hx⟩)
    rcases mul_eq_zero.1 this with h5 | h5
    · exact absurd h5 hgx
    · exact sub_eq_zero.1 h5
  have hsingle : g i • A i = 0 := by
    rw [← hg, Finset.sum_eq_single_of_mem i hi]
    intro x hx hxi
    rw [hothers x hx hxi, zero_smul]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply hv
  apply hA i
  have := LinearMap.congr_fun hsingle v
  simp only [LinearMap.smul_apply, LinearMap.zero_apply] at this
  rw [map_zero]
  exact (smul_eq_zero.1 this).resolve_left hgi


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.heisenberg_family_irreducible : ∀ (K G V : Type) [Field K] [CommGroup G] [Finite G] [AddCommGroup V] [Module K V] [Module.Finite K V] (U : G → V ≃ₗ[K] V) (e : G → G →* Kˣ), (∀ x y v, U x (U y v) = (e x y : K) • U y (U x v)) → Function.Injective e → Module.finrank K V ^ 2 ≤ Nat.card G → ∀ W : Submodule K V, (∀ x v, v ∈ W → U x v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro K G V _ _ _ _ _ _ U e hU he hcard W hW
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact Or.inl (Submodule.eq_bot_of_subsingleton)
  haveI : Fintype G := Fintype.ofFinite G
  have hind : LinearIndependent K (fun x => (U x : V →ₗ[K] V)) := by
    refine _root_.GlobalTheory.linearIndependent_of_comm_smul (fun x => (U x : V →ₗ[K] V))
      (fun x y => (e x y : K)) (fun x => (U x).injective) (fun x y v => hU x y v) ?_
    intro x x' hxx'
    apply he
    ext y
    exact congr_fun hxx' y
  have hdim : Module.finrank K (V →ₗ[K] V) = Module.finrank K V ^ 2 := by
    rw [Module.finrank_linearMap, sq]
  have hle := hind.fintype_card_le_finrank
  rw [hdim] at hle
  rw [Nat.card_eq_fintype_card] at hcard
  have hspan := hind.span_eq_top_of_card_eq_finrank (le_antisymm hle hcard |>.trans hdim.symm)

  let S : Submodule K (V →ₗ[K] V) :=
    { carrier := {f | ∀ w ∈ W, f w ∈ W}
      add_mem' := fun hf hg w hw => W.add_mem (hf w hw) (hg w hw)
      zero_mem' := fun w _ => by simp
      smul_mem' := fun a f hf w hw => W.smul_mem a (hf w hw) }
  have hS : ∀ f : V →ₗ[K] V, ∀ w ∈ W, f w ∈ W := by
    intro f
    have : f ∈ Submodule.span K (Set.range fun x => (U x : V →ₗ[K] V)) := by
      rw [hspan]; exact Submodule.mem_top
    have hsub : Submodule.span K (Set.range fun x => (U x : V →ₗ[K] V)) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩ w hw
      exact hW x w hw
    exact hsub this
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K V, φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff K w).1 hcon)
  rw [eq_top_iff]
  intro v _
  have := hS ((φ w)⁻¹ • φ.smulRight v) w hwW
  simpa [LinearMap.smulRight_apply, smul_smul, inv_mul_cancel₀ hφ] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NatCardEqOfEquivPiField
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace MulLaw

theorem natCard_eq_of_equiv_pi_field {R : Type} [Field R] {U V : Type} [AddCommGroup U]
    [Module R U] [AddCommGroup V] [Module R V] {X : Type} (e : U ≃ₗ[R] (X → V)) {m : ℕ}
    (hm : 0 < m) (hU : Module.finrank R U = m) (hV : Module.finrank R V = 1) :
    Nat.card X = m := by
  classical
  haveI : Module.Finite R U := Module.finite_of_finrank_pos (hU ▸ hm)
  haveI : Module.Finite R V := Module.finite_of_finrank_pos (hV ▸ Nat.one_pos)
  have e₁ : V ≃ₗ[R] R := LinearEquiv.ofFinrankEq V R (by rw [hV, Module.finrank_self])
  have e₂ : U ≃ₗ[R] (X → R) := e.trans (LinearEquiv.piCongrRight fun _ => e₁)
  haveI : Module.Finite R (X → R) := Module.Finite.equiv e₂
  haveI : Finite X := (Pi.linearIndependent_single_one X R).finite
  haveI := Fintype.ofFinite X
  rw [← hU, e₂.finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

theorem natCard_eq_of_equiv_pi {R : Type} [CommRing R] (hR : IsField R) {U V : Type}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V] {X : Type}
    (e : U ≃ₗ[R] (X → V)) {m : ℕ}
    (hm : 0 < m) (hU : Module.finrank R U = m) (hV : Module.finrank R V = 1) :
    Nat.card X = m := by
  letI := hR.toField
  exact natCard_eq_of_equiv_pi_field e hm hU hV

noncomputable def basePointsEquiv {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'}
    [GrpObj A] [GrpObj A'] {g : A'.left ⟶ A.left} (hg : IsPullback g A'.hom A.hom f)
    (hmul : ∀ (T : Over S') (x y : T ⟶ A'),
      toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) (T : Over S') :
    (T ⟶ A') ≃* (Over.mk (T.hom ≫ f) ⟶ A) where
  toFun x := toBase hg.w x
  invFun y := Over.homMk (hg.lift y.left T.hom (Over.w y)) (hg.lift_snd _ _ _)
  left_inv x := by
    apply Over.OverMorphism.ext
    apply hg.hom_ext
    · exact hg.lift_fst _ _ _
    · exact (hg.lift_snd _ _ _).trans (Over.w x).symm
  right_inv y := by
    apply Over.OverMorphism.ext
    exact hg.lift_fst _ _ _
  map_mul' x y := hmul T x y

end MulLaw

theorem mulN_of_decomposition :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n j : ℕ), (n : K) ≠ 0 → 1 ≤ j → Nonempty (SecM P.A P.L ((n ^ 2 * j : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K))) ≃ₗ[Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)] ({x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ n = 1} → SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K)))))) → GlobalSectionsRankAlgClosed → PolBaseChangeSt → MulNSt := by
  intro hQ hRel hH hBC S _ P n hn
  obtain ⟨h1, h2, h3, h4⟩ := hQ S P n hn
  refine ⟨h1, h2, h3, h4, fun k _ _ t hk => ?_⟩
  obtain ⟨P', g, hg, hdim, hmul, -⟩ := hBC S _ t P
  obtain ⟨e⟩ := hRel k P' n 1 hk le_rfl
  have hn2 : 1 ≤ n ^ 2 * 1 := by
    rw [Nat.mul_one]; exact Nat.one_le_pow _ _ hn
  have hU := hH k P' (n ^ 2 * 1) hn2
  have hV := hH k P' 1 le_rfl
  rw [one_pow] at hV
  have hF : IsField Γ((baseOver (Spec (CommRingCat.of k))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)
  have hcard := MulLaw.natCard_eq_of_equiv_pi hF e (Nat.pow_pos hn2) hU hV
  have φ : (baseOver (Spec (CommRingCat.of k)) ⟶ P'.A) ≃* (Over.mk t ⟶ P.A) := by
    have ψ := MulLaw.basePointsEquiv hg hmul (baseOver (Spec (CommRingCat.of k)))
    have ht : (baseOver (Spec (CommRingCat.of k))).hom ≫ t = t := Category.id_comp t
    rw [ht] at ψ
    exact ψ
  rw [← Nat.card_congr (φ.toEquiv.subtypeEquiv
    (p := fun x => x ^ n = 1) (q := fun x => x ^ n = 1) (fun x => by
      show x ^ n = 1 ↔ φ x ^ n = 1
      rw [← map_pow, map_eq_one_iff φ φ.injective])), hcard, hdim, Nat.mul_one, ← pow_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.OneTmulNeZeroOfDomain
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatFibreInjective

open TensorProduct

theorem one_tmul_ne_zero_of_domain {A P k : Type} [CommRing A] [IsDomain A] [AddCommGroup P]
    [Module A P] [Field k] [Algebra A k] (hinj : Function.Injective (algebraMap A k)) (y : P)
    (hy : ∀ a : A, a • y = 0 → a = 0) : (1 : k) ⊗ₜ[A] y ≠ 0 := by
  intro h1
  letI : Algebra (FractionRing A) k := (IsFractionRing.lift hinj).toAlgebra
  haveI : IsScalarTower A (FractionRing A) k :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsFractionRing.lift_algebraMap hinj a).symm)
  haveI : Module.Flat A (FractionRing A) := IsLocalization.flat _ (nonZeroDivisors A)
  haveI : Module.Free (FractionRing A) k := Module.Free.of_divisionRing _ _
  haveI : Module.Flat (FractionRing A) k := Module.Flat.of_free
  haveI : Module.Flat A k := Module.Flat.trans _ (FractionRing A) _
  have hi : Function.Injective (LinearMap.toSpanSingleton A P y) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    exact hy
  have h2 : (1 : k) ⊗ₜ[A] (1 : A) = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := k) _ hi
    rw [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, one_smul, map_zero, h1]
  have h3 := congrArg (TensorProduct.rid A k) h2
  rw [TensorProduct.rid_tmul, one_smul, map_zero] at h3
  exact one_ne_zero h3

theorem one_tmul_ne_zero {R₀ P k : Type} [CommRing R₀] [AddCommGroup P] [Module R₀ P]
    [Field k] [Algebra R₀ k] (p : Ideal R₀) (hk : ∀ a, algebraMap R₀ k a = 0 ↔ a ∈ p)
    (hP : Module.IsTorsionBySet R₀ P p) (y : P) (hy : ∀ a : R₀, a • y = 0 → a ∈ p) :
    (1 : k) ⊗ₜ[R₀] y ≠ 0 := by
  intro h
  have hker : p = RingHom.ker (algebraMap R₀ k) := by
    ext a; simp [RingHom.mem_ker, hk]
  haveI : p.IsPrime := hker ▸ RingHom.ker_isPrime _
  letI : Module (R₀ ⧸ p) P := hP.module
  haveI : IsScalarTower R₀ (R₀ ⧸ p) P := hP.isScalarTower
  letI : Algebra (R₀ ⧸ p) k :=
    (Ideal.Quotient.lift p (algebraMap R₀ k) (fun a ha => (hk a).2 ha)).toAlgebra
  haveI : IsScalarTower R₀ (R₀ ⧸ p) k := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap (R₀ ⧸ p) k) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hk a).1 ha)
  refine one_tmul_ne_zero_of_domain (A := R₀ ⧸ p) hinj y ?_ ?_
  · intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hy a ha)
  · have := congrArg (TensorProduct.mapOfCompatibleSMul (R₀ ⧸ p) R₀ R₀ k P) h
    rwa [TensorProduct.mapOfCompatibleSMul_tmul, map_zero] at this

theorem one_tmul_eq_zero {R₀ M C₀ C₁ k : Type} [CommRing R₀] [AddCommGroup M] [Module R₀ M]
    [AddCommGroup C₀] [Module R₀ C₀] [AddCommGroup C₁] [Module R₀ C₁]
    [Field k] [Algebra R₀ k] (φ : C₀ →ₗ[R₀] C₁) (hφ : Function.Injective (φ.baseChange k))
    (y : M ⊗[R₀] C₀) (hy : φ.lTensor M y = 0) : (1 : k) ⊗ₜ[R₀] y = 0 := by
  obtain ⟨g, hg⟩ := (φ.baseChange k).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hφ)
  have key : ∀ z : M ⊗[R₀] C₀,
      TensorProduct.leftComm R₀ M k C₀ ((g.restrictScalars R₀).lTensor M
        ((TensorProduct.mk R₀ k C₁ 1).lTensor M (φ.lTensor M z))) = (1 : k) ⊗ₜ[R₀] z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m c =>
      have := LinearMap.congr_fun hg ((1 : k) ⊗ₜ[R₀] c)
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.id_apply] at this
      simp [this]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, tmul_add]
  rw [← key, hy]
  simp

theorem exists_of_torsion {R₀ N C : Type} [CommRing R₀] [AddCommGroup N] [Module R₀ N]
    [AddCommGroup C] [Module R₀ C] [Module.Flat R₀ C] (p : Ideal R₀) (hp : p.FG)
    (x : N ⊗[R₀] C) (hx : ∀ a ∈ p, a • x = 0) :
    ∃ y, (Submodule.torsionBySet R₀ N p).subtype.rTensor C y = x := by
  classical
  obtain ⟨s, rfl⟩ := hp
  let g : N →ₗ[R₀] (s → N) := LinearMap.pi fun a => (a : R₀) • LinearMap.id
  have hex : Function.Exact (Submodule.torsionBySet R₀ N (Ideal.span (s : Set R₀))).subtype g := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, ← Submodule.torsionBySet_eq_torsionBySet_span]
    ext n
    simp [g, funext_iff, LinearMap.mem_ker]
  have h := Module.Flat.rTensor_exact C hex x
  refine h.1 ?_
  apply (TensorProduct.piLeft R₀ C (fun _ : s => N)).injective
  have key : ∀ z : N ⊗[R₀] C, ∀ a : s,
      TensorProduct.piLeft R₀ C (fun _ : s => N) (g.rTensor C z) a = (a : R₀) • z := by
    intro z a
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul n c => simp [g, smul_tmul']
    | add u v hu hv => simp only [map_add (f := _), Pi.add_apply, hu, hv, smul_add]
  funext a
  rw [key, hx _ (Ideal.subset_span a.2)]
  simp

theorem injective_baseChange :
    ∀ (R₀ R C₀ C₁ : Type) [CommRing R₀] [IsNoetherianRing R₀] [CommRing R] [Algebra R₀ R]
      [AddCommGroup C₀] [Module R₀ C₀] [AddCommGroup C₁] [Module R₀ C₁] [Module.Flat R₀ C₀]
      [Module.Flat R₀ C₁] (φ : C₀ →ₗ[R₀] C₁),
      (∀ (k : Type) [Field k] [Algebra R k] [Algebra R₀ k] [IsScalarTower R₀ R k],
        Function.Injective (φ.baseChange k)) → Function.Injective (φ.baseChange R) := by
  intro R₀ R C₀ C₁ _ _ _ _ _ _ _ _ _ _ φ H
  change Function.Injective (φ.lTensor R)
  rw [← LinearMap.ker_eq_bot]
  by_contra hne
  haveI : Nontrivial (LinearMap.ker (φ.lTensor R)) := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty R₀ (LinearMap.ker (φ.lTensor R))
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp
  obtain ⟨hp, ⟨x, hx0⟩, hx⟩ := hp
  have hann : ∀ a : R₀, a • x = 0 ↔ a ∈ p := by
    intro a
    rw [hx]
    simp [Submodule.mem_colon_singleton]
  let M := Submodule.torsionBySet R₀ R p
  obtain ⟨y, rfl⟩ : ∃ y, M.subtype.rTensor C₀ y = x :=
    exists_of_torsion p (IsNoetherian.noetherian p) x (fun a ha => (hann a).2 ha)
  have hy0 : φ.lTensor M y = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := C₁) M.subtype M.injective_subtype
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor]
    exact hx0
  have hkill : ∀ a : R₀, (∀ m : M, a • m = 0) → ∀ z : M ⊗[R₀] C₀, a • z = 0 := by
    intro a ha z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m c => rw [smul_tmul', ha, zero_tmul]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]
  have hy : ∀ a : R₀, a • y = 0 → a ∈ p := by
    intro a ha
    rw [← hann, ← map_smul, ha, map_zero]
  have hcm : (p.map (algebraMap R₀ R)).comap (algebraMap R₀ R) = p := by
    refine le_antisymm ?_ Ideal.le_comap_map
    intro a ha
    refine hy a (hkill a (fun m => ?_) y)
    have hle : p.map (algebraMap R₀ R) ≤ LinearMap.ker (LinearMap.toSpanSingleton R R m) := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      have := (Submodule.mem_torsionBySet_iff _ _).1 m.2 ⟨b, hb⟩
      simpa [Algebra.smul_def] using this
    have := hle ha
    apply Subtype.ext
    simpa [Algebra.smul_def] using this
  obtain ⟨q, hq, hqp⟩ := (Ideal.comap_map_eq_self_iff_of_isPrime p).1 hcm
  refine one_tmul_ne_zero (k := q.ResidueField) p ?_ ?_ y hy
    (one_tmul_eq_zero φ (H q.ResidueField) y hy0)
  · intro a
    rw [IsScalarTower.algebraMap_apply R₀ R q.ResidueField, Ideal.algebraMap_residueField_eq_zero,
      ← hqp]
    rfl
  · intro z a
    refine hkill a (fun m => Subtype.ext ?_) z
    exact (Submodule.mem_torsionBySet_iff _ _).1 m.2 a

end GlobalTheory.FlatFibreInjective
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroOfDvdPowUniformiser
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sec_eq_zero_of_chart {X : Scheme.{0}} [IsIntegral X] (N : LB X) (s : LB.Sec N)
    (j : N.ι) (x : X) (hx : x ∈ N.U j) (hj : s.f j = 0) (i : N.ι) : s.f i = 0 := by
  by_cases hi : (N.U i : Set X).Nonempty
  · have hij : ((N.U i ⊓ N.U j : X.Opens) : Set X).Nonempty :=
      nonempty_preirreducible_inter (N.U i).isOpen (N.U j).isOpen hi ⟨x, hx⟩
    have : Nonempty (N.U i ⊓ N.U j : X.Opens) := hij.to_subtype
    have h := s.compat i j
    rw [hj, map_zero, mul_zero] at h
    apply map_injective_of_isIntegral X (homOfLE (inf_le_left : N.U i ⊓ N.U j ≤ N.U i))
    rw [map_zero]
    exact h
  · have : N.U i = ⊥ := by
      ext1
      simpa using Set.not_nonempty_iff_eq_empty.1 hi
    have : Subsingleton Γ(X, N.U i) := by rw [this]; infer_instance
    exact Subsingleton.elim _ _

theorem eq_zero_of_mem_pow_span {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) (x : X) (hx : x ∈ U) (a b : Γ(X, U)) (ha : x ∉ X.basicOpen a)
    (hb : ∀ e : ℕ, b ∈ Ideal.span {a} ^ e) : b = 0 := by
  apply germ_injective_of_isIntegral X x hx
  rw [map_zero]
  rw [X.mem_basicOpen a x hx] at ha
  have hI : Ideal.span {(X.presheaf.germ U x hx).hom a} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  have h := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hI
  rw [← Ideal.mem_bot, ← h, Ideal.mem_iInf]
  intro e
  have := Ideal.mem_map_of_mem (X.presheaf.germ U x hx).hom (hb e)
  rwa [Ideal.map_pow, Ideal.map_span, Set.image_singleton] at this

theorem sec_eq_zero_of_dvd_pow_uniformiser :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f →
      GeometricallyIntegral f) → Semi.lemmaBSt.{0} := by
  intro H V _ _ _ G _ _ _ _ _ _ N hN s π hπ hs
  have : GeometricallyIntegral G.hom := H _ _ _ inferInstance inferInstance
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨x, hx⟩ := G.hom.surjective (IsLocalRing.closedPoint V)
  obtain ⟨j, hj⟩ : ∃ j, x ∈ N.U j := by
    have : x ∈ ⨆ i, N.U i := by rw [hN.cover]; trivial
    exact Opens.mem_iSup.1 this
  refine sec_eq_zero_of_chart N s j x hj ?_
  refine eq_zero_of_mem_pow_span (N.U j) x hj _ _ ?_ (hs j)
  intro h
  have h2 := ((Scheme.basicOpen_res G.left _ (homOfLE (le_top :
    N.U j ≤ G.hom ⁻¹ᵁ ⊤)).op).le h).2
  have h3 : x ∈ G.hom ⁻¹ᵁ (Spec (CommRingCat.of V)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv π) := by
    rw [Scheme.preimage_basicOpen]
    exact h2
  rw [basicOpen_eq_of_affine] at h3
  have h4 : G.hom x ∈ PrimeSpectrum.basicOpen π := h3
  rw [hx] at h4
  exact h4 ((IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit)

end GlobalTheory
end

