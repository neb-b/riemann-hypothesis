module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CommuteImageAbelianByPrimePowerOfNormalCentral
section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.commute_all : ∀ (G : Type) [Group G] [Finite G] (M : Type) [Monoid M] (φ : G →* M), _root_.GlobalTheory.BI.AbByP G → (∀ B : Subgroup G, B.Normal → (∀ a ∈ B, ∀ b ∈ B, φ a * φ b = φ b * φ a) → ∀ b ∈ B, ∀ g : G, φ b * φ g = φ g * φ b) → ∀ a b : G, φ a * φ b = φ b * φ a := by
  intro G _ _ M _ φ hG hyp
  obtain ⟨p, hp, A, hAn, hAc, hpow⟩ := hG
  let Z : Subgroup G :=
    { carrier := {b | ∀ g, φ b * φ g = φ g * φ b}
      mul_mem' := fun {x y} hx hy g => by
        rw [map_mul, mul_assoc, hy g, ← mul_assoc, hx g, mul_assoc]
      one_mem' := fun g => by simp
      inv_mem' := fun {x} hx g => by
        have h1 : φ x⁻¹ * φ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        have h2 : φ x * φ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        calc φ x⁻¹ * φ g = φ x⁻¹ * φ g * (φ x * φ x⁻¹) := by rw [h2, mul_one]
          _ = φ x⁻¹ * (φ x * φ g) * φ x⁻¹ := by rw [hx g]; simp only [mul_assoc]
          _ = φ g * φ x⁻¹ := by rw [← mul_assoc, h1, one_mul] }
  have hZ : ∀ b, b ∈ Z ↔ ∀ g, φ b * φ g = φ g * φ b := fun b => Iff.rfl
  have hZn : Z.Normal := ⟨fun b hb g => by
    rw [hZ] at hb ⊢
    intro h
    have e : φ (g * b * g⁻¹) = φ b := by
      rw [map_mul, map_mul, ← hb g, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    rw [e]
    exact hb h⟩
  have hAZ : A ≤ Z := fun a ha => (hZ a).2 (hyp A hAn (fun x hx y hy => by
    rw [← map_mul, ← map_mul, hAc x hx y hy]) a ha)
  suffices hZtop : Z = ⊤ by
    intro a b
    exact (hZ a).1 (hZtop ▸ Subgroup.mem_top a) b
  by_contra hne
  have hP : IsPGroup p (G ⧸ Z) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k, hk⟩ := hpow g
      exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hAZ hk⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial (G ⧸ Z) := QuotientGroup.nontrivial_iff.mpr hne
  haveI := hP.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center (G ⧸ Z))
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (z : G ⧸ Z)
  have hzc : ∀ q : G ⧸ Z, ∀ i : ℤ, q * (z : G ⧸ Z) ^ i = (z : G ⧸ Z) ^ i * q := fun q i =>
    ((Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ z.2 i)) q)
  let C : Subgroup G := (Subgroup.zpowers (z : G ⧸ Z)).comap (QuotientGroup.mk' Z)
  have hmemC : ∀ c ∈ C, ∃ i : ℤ, ∃ b ∈ Z, c = g ^ i * b := by
    intro c hc
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hc
    refine ⟨i, (g ^ i)⁻¹ * c, ?_, by group⟩
    rw [← QuotientGroup.eq, QuotientGroup.mk_zpow, hg]
    exact hi
  have hCn : C.Normal := ⟨fun c hc h => by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hc
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
    simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hi ⊢
    rw [← hi, hzc, mul_assoc, mul_inv_cancel, mul_one]⟩
  have hCc : ∀ x ∈ C, ∀ y ∈ C, φ x * φ y = φ y * φ x := by
    intro x hx y hy
    obtain ⟨i, b1, hb1, rfl⟩ := hmemC x hx
    obtain ⟨j, b2, hb2, rfl⟩ := hmemC y hy
    rw [hZ] at hb1 hb2
    have key : ∀ (i j : ℤ) (b1 b2 : G), (∀ g, φ b1 * φ g = φ g * φ b1) →
        φ (g ^ i * b1) * φ (g ^ j * b2) = φ (g ^ (i + j)) * (φ b1 * φ b2) := by
      intro i j b1 b2 hb1
      rw [map_mul, map_mul, mul_assoc, ← mul_assoc (φ b1), hb1, mul_assoc, ← mul_assoc,
        ← map_mul, ← zpow_add]
    rw [key i j b1 b2 hb1, key j i b2 b1 hb2, add_comm, hb1 b2]
  have hgC : g ∈ C := Subgroup.mem_zpowers_iff.mpr ⟨1, by simp [hg]⟩
  have hgZ : g ∈ Z := (hZ g).2 (hyp C hCn hCc g hgC)
  apply hz1
  apply Subtype.ext
  rw [← hg]
  exact (QuotientGroup.eq_one_iff g).mpr hgZ

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassOfCharpolyCardCyclicVectors
section
open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace GlobalTheory.CuspGL.CyclicMass

variable {F : Type} [Field F]

theorem charpoly_mulLeft_root (D : F[X]) (hD : D.Monic) [FiniteDimensional F (AdjoinRoot D)] :
    LinearMap.charpoly (LinearMap.mulLeft F (AdjoinRoot.root D)) = D := by
  have h := charpoly_leftMulMatrix (AdjoinRoot.powerBasis' hD)
  rw [AdjoinRoot.powerBasis'_gen] at h
  have h2 : minpoly F (AdjoinRoot.root D) = D := by
    rw [AdjoinRoot.minpoly_root hD.ne_zero, hD.leadingCoeff]; simp
  rw [h2] at h
  rw [← LinearMap.charpoly_toMatrix _ (AdjoinRoot.powerBasis' hD).basis]
  exact h

theorem map_mk {V : Type} [AddCommGroup V] [Module F V] (D : F[X]) (f : AdjoinRoot D →ₗ[F] V)
    (g : Module.End F V) (h : ∀ a, f (AdjoinRoot.root D * a) = g (f a)) (p : F[X]) :
    f (AdjoinRoot.mk D p) = aeval g p (f 1) := by
  induction p using Polynomial.induction_on with
  | C a =>
    have : AdjoinRoot.mk D (C a) = a • (1 : AdjoinRoot D) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [this, map_smul]; simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    have : C a * X ^ (n + 1) = X * (C a * X ^ n) := by ring
    rw [this, map_mul, AdjoinRoot.mk_X, h, ih, map_mul (aeval g) X, aeval_X, Module.End.mul_apply]

theorem cyclic_one (D : F[X]) (U : Submodule F (AdjoinRoot D))
    (hU : ∀ a ∈ U, AdjoinRoot.root D * a ∈ U) (h1 : (1 : AdjoinRoot D) ∈ U) : U = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  induction p using Polynomial.induction_on with
  | C a =>
    have : AdjoinRoot.mk D (C a) = a • (1 : AdjoinRoot D) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [this]; exact U.smul_mem _ h1
  | add p q hp hq => rw [map_add (f := _)]; exact U.add_mem (hp trivial) (hq trivial)
  | monomial n a ih =>
    have : C a * X ^ (n + 1) = X * (C a * X ^ n) := by ring
    rw [this, map_mul, AdjoinRoot.mk_X]
    exact hU _ (ih trivial)

theorem card_pairs {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (D : F[X]) (hD : D.Monic)
    (hV : Module.finrank F V = D.natDegree) :
    Nat.card (AdjoinRoot D ≃ₗ[F] V) =
      Nat.card (Σ g : {g : Module.End F V // LinearMap.charpoly g = D},
        {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g.1 x ∈ U) → v ∈ U → U = ⊤}) := by
  haveI : FiniteDimensional F (AdjoinRoot D) := (AdjoinRoot.powerBasis' hD).finite
  have hA : Module.finrank F (AdjoinRoot D) = D.natDegree := (AdjoinRoot.powerBasis' hD).finrank
  let Φ : (AdjoinRoot D ≃ₗ[F] V) → (Σ g : {g : Module.End F V // LinearMap.charpoly g = D},
        {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g.1 x ∈ U) → v ∈ U → U = ⊤}) := fun e =>
    ⟨⟨e.conj (LinearMap.mulLeft F (AdjoinRoot.root D)), by
        rw [LinearEquiv.charpoly_conj, charpoly_mulLeft_root D hD]⟩,
      ⟨e 1, fun U hU h1 => by
        have := cyclic_one D (U.comap e.toLinearMap) (fun a ha => by
          have := hU _ ha
          simpa [LinearEquiv.conj_apply] using this) h1
        rw [eq_top_iff]
        intro v _
        have h2 : e.symm v ∈ U.comap e.toLinearMap := this ▸ Submodule.mem_top
        simpa using h2⟩⟩
  have hΦ : ∀ (e : AdjoinRoot D ≃ₗ[F] V) (p : F[X]),
      e (AdjoinRoot.mk D p) = aeval (Φ e).1.1 p (Φ e).2.1 := fun e p =>
    map_mk D e.toLinearMap _ (fun a => by simp [Φ, LinearEquiv.conj_apply]) p
  refine Nat.card_congr (Equiv.ofBijective Φ ⟨?_, ?_⟩)
  · intro e e' h
    ext a
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hΦ, hΦ, h]
  · rintro ⟨⟨g, hg⟩, ⟨v, hv⟩⟩
    have h0 : aeval g D = 0 := hg ▸ LinearMap.aeval_self_charpoly g
    let f : AdjoinRoot D →ₗ[F] V :=
      (LinearMap.applyₗ v) ∘ₗ (aeval g).toLinearMap ∘ₗ AdjoinRoot.modByMonicHom hD
    have hf : ∀ p, f (AdjoinRoot.mk D p) = aeval g p v := fun p => by
      simp [f, AdjoinRoot.modByMonicHom_mk, Polynomial.aeval_modByMonic_eq_self_of_root h0]
    have hf1 : f 1 = v := by simpa using hf 1
    have hfx : ∀ a, f (AdjoinRoot.root D * a) = g (f a) := fun a => by
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
      rw [← AdjoinRoot.mk_X, ← map_mul, hf, hf]; simp
    have hs : Function.Surjective f := by
      rw [← LinearMap.range_eq_top]
      refine hv _ ?_ ⟨1, hf1⟩
      rintro _ ⟨a, rfl⟩
      exact ⟨_, hfx a⟩
    have hi : Function.Injective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hA.trans hV.symm)).2 hs
    refine ⟨LinearEquiv.ofBijective f ⟨hi, hs⟩, ?_⟩
    have hg' : (Φ (LinearEquiv.ofBijective f ⟨hi, hs⟩)).1 = ⟨g, hg⟩ := by
      apply Subtype.ext
      ext w
      obtain ⟨a, rfl⟩ := (LinearEquiv.ofBijective f ⟨hi, hs⟩).surjective w
      simp only [Φ, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      exact hfx a
    refine Sigma.ext hg' ?_
    refine (Subtype.heq_iff_coe_eq ?_).2 hf1
    intro w
    rw [hg']

end GlobalTheory.CuspGL.CyclicMass

namespace GlobalTheory.CuspGL

theorem mass_card_cyclic (F : Type) [Field F] [Finite F] (D : F[X]) (hD : D.Monic) :
    mass (fun g : Module.End F (Fin D.natDegree → F) =>
      (Nat.card {v : Fin D.natDegree → F // ∀ U : Submodule F (Fin D.natDegree → F),
        (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) D = glCard F D.natDegree := by
  classical
  haveI : FiniteDimensional F (AdjoinRoot D) := (AdjoinRoot.powerBasis' hD).finite
  have hA : Module.finrank F (AdjoinRoot D) = D.natDegree := (AdjoinRoot.powerBasis' hD).finrank
  have h := CyclicMass.card_pairs (V := Fin D.natDegree → F) D hD (by simp)
  haveI : Finite (Module.End F (Fin D.natDegree → F)) :=
    Finite.of_injective _ DFunLike.coe_injective
  haveI := Fintype.ofFinite {g : Module.End F (Fin D.natDegree → F) // LinearMap.charpoly g = D}
  rw [Nat.card_sigma] at h
  let e0 : AdjoinRoot D ≃ₗ[F] (Fin D.natDegree → F) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hA])
  have h2 : Nat.card (AdjoinRoot D ≃ₗ[F] (Fin D.natDegree → F)) = Nat.card (GL (Fin D.natDegree) F) := by
    refine Nat.card_congr (Equiv.trans ?_ (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F _)).toEquiv.symm)
    exact ⟨fun e => e0.symm.trans e, fun e => e0.trans e, fun e => by ext; simp, fun e => by ext; simp⟩
  rw [glCard, ← h2, h, mass, ← finsum_set_coe_eq_finsum_mem, Nat.cast_sum]
  exact finsum_eq_sum_of_fintype (α := {g : Module.End F (Fin D.natDegree → F) // LinearMap.charpoly g = D}) _

end GlobalTheory.CuspGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfFinsumMulStarPowEqZero
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem eq_zero_of_finsum_mul_star_pow_eq_zero {K : Type} [Field K] (θ : K →* ℂ)
    (hθ : ∀ x y : K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (N : ℕ) (hN : 0 < N) (c : K → ℂ)
    (h : ∀ l : ℕ, ∑ᶠ α ∈ {α : K | α ^ N = 1}, c α * star (θ α ^ l) = 0) :
    ∀ α ∈ {α : K | α ^ N = 1}, c α = 0 := by
  classical
  have hS : {α : K | α ^ N = 1} = ((Polynomial.nthRootsFinset N (1 : K) : Finset K) : Set K) := by
    ext x
    simp [Polynomial.mem_nthRootsFinset hN]
  intro β hβ
  have hβ' : β ^ N = 1 := hβ
  set S := Polynomial.nthRootsFinset N (1 : K) with hSdef
  have hmem : ∀ x, x ∈ S ↔ x ^ N = 1 := fun x => Polynomial.mem_nthRootsFinset hN 1
  have h' : ∀ l : ℕ, ∑ α ∈ S, c α * star (θ α ^ l) = 0 := by
    intro l
    have := h l
    rwa [hS, finsum_mem_coe_finset] at this
  have hpow : ∀ x : K, x ^ N = 1 → θ x ^ N = 1 := fun x hx => by rw [← map_pow, hx, map_one]
  have hunit : ∀ x : K, x ^ N = 1 → star (θ x) * θ x = 1 := by
    intro x hx
    have h1 : ‖θ x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (hpow x hx) hN.ne'
    have := Complex.conj_mul' (θ x)
    rw [h1] at this
    simpa using this
  have hne : ∀ x : K, x ^ N = 1 → x ≠ 0 := by
    rintro x hx rfl
    rw [zero_pow hN.ne'] at hx
    exact zero_ne_one hx
  have key : ∀ α ∈ S, ∑ l ∈ Finset.range N, (θ β * star (θ α)) ^ l
      = if α = β then (N : ℂ) else 0 := by
    intro α hα
    have hα' := (hmem α).1 hα
    split_ifs with hab
    · subst hab
      rw [mul_comm, hunit α hα']
      simp
    · have hz : θ β * star (θ α) ≠ 1 := by
        intro hz
        apply hab
        apply hθ α β (hne α hα') (hne β hβ')
        calc θ α = (θ β * star (θ α)) * θ α := by rw [hz, one_mul]
          _ = θ β := by rw [mul_assoc, hunit α hα', mul_one]
      rw [geom_sum_eq hz, mul_pow, ← star_pow, hpow β hβ', hpow α hα']
      simp
  have hsum : ∑ l ∈ Finset.range N, θ β ^ l * ∑ α ∈ S, c α * star (θ α ^ l) = 0 := by
    simp only [h', mul_zero, Finset.sum_const_zero]
  have h2 : ∑ l ∈ Finset.range N, θ β ^ l * ∑ α ∈ S, c α * star (θ α ^ l)
      = ∑ α ∈ S, c α * ∑ l ∈ Finset.range N, (θ β * star (θ α)) ^ l := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_pow, star_pow]
    ring
  rw [h2, Finset.sum_congr rfl (fun α hα => by rw [key α hα])] at hsum
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', (hmem β).2 hβ', if_true] at hsum
  exact (mul_eq_zero.1 hsum).resolve_right (Nat.cast_ne_zero.2 hN.ne')

theorem torus_fourier_injective : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n : ℕ, 0 < n → ∀ c : AlgebraicClosure F → ℂ, (∀ l : ℕ, ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, c α * star (θ α ^ l) = 0) → ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, c α = 0 := by
  intro F _ _ θ hθ n hn c h
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hN : 0 < Nat.card F ^ n - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' hq)
  exact eq_zero_of_finsum_mul_star_pow_eq_zero θ hθ _ hN c h

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
section
namespace GlobalTheory

theorem exists_common_eigenvector_of_commute {L : Type} [Field L] [IsAlgClosed L] {ι : Type}
    {V : Type} [AddCommGroup V] [Module L V] [FiniteDimensional L V] [Nontrivial V]
    (f : ι → Module.End L V) (hf : ∀ a b, f a * f b = f b * f a) :
    ∃ v : V, v ≠ 0 ∧ ∀ b, ∃ μ : L, f b v = μ • v := by
  first
  | exact @_root_.GlobalTheory.UnimodularLatticeLemma.main
  | exact _root_.GlobalTheory.UnimodularLatticeLemma.main
  | (apply _root_.GlobalTheory.UnimodularLatticeLemma.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnimodularLatticeLemma.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnimodularLatticeLemma.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnimodularLatticeLemma.main ..)

theorem exists_character_eigenvector_of_commute :
    ∀ (L : Type) [Field L] [IsAlgClosed L] (B : Type) [Group B] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] [Nontrivial V] (ρ : Representation L B V), (∀ a b, ρ a * ρ b = ρ b * ρ a) → ∃ (lam : B →* Lˣ) (v : V), v ≠ 0 ∧ ∀ b, ρ b v = (lam b : L) • v := by
  intro L _ _ B _ V _ _ _ _ ρ h
  obtain ⟨v, hv0, hv⟩ := exists_common_eigenvector_of_commute (fun b => ρ b) h
  choose μ hμ using hv
  have hinj : Function.Injective fun c : L => c • v := smul_left_injective L hv0
  let χ : B →* L :=
    { toFun := μ
      map_one' := hinj (by
        have := hμ 1
        simp only [map_one, Module.End.one_apply] at this
        simpa using this.symm)
      map_mul' := fun a b => hinj (by
        have h1 := hμ (a * b)
        simp only [map_mul, Module.End.mul_apply] at h1
        have h2 := hμ a
        have h3 := hμ b
        simp only at h2 h3 ⊢
        rw [← h1, h3, map_smul, h2, smul_smul, mul_comm]) }
  exact ⟨χ.toHomUnits, v, hv0, fun b => hμ b⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsConjEqAddOfIsCoprime
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem intertwine_aeval_apply {F : Type} [Field F] {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] (f : V →ₗ[F] W) (a : Module.End F V) (b : Module.End F W) (h : ∀ x, f (a x) = b (f x))
    (p : F[X]) (x : V) : f (aeval a p x) = aeval b p (f x) := by
  have hpow : ∀ (n : ℕ) (x : V), f ((a ^ n) x) = (b ^ n) (f x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c => simp [aeval_monomial, hpow]

theorem nilRad_eq_zero_of_commute {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A)
    (hc : IsCoprime (LinearMap.charpoly (g.restrict hg))
      (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))))
    (u : Module.End F V) (hu : u ∈ nilRad A) (hug : ∀ x, u (g x) = g (u x)) : u = 0 := by
  obtain ⟨a, b, hab⟩ := hc
  set p₁ := LinearMap.charpoly (g.restrict hg) with hp₁
  set p₂ := LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) with hp₂
  have h1 : ∀ y ∈ A, aeval g p₁ y = 0 := by
    intro y hy
    have := intertwine_aeval_apply A.subtype (g.restrict hg) g (fun x => rfl) p₁ ⟨y, hy⟩
    rw [hp₁, LinearMap.aeval_self_charpoly] at this
    simpa using this.symm
  have h2 : ∀ y, aeval g p₂ y ∈ A := by
    intro y
    have := intertwine_aeval_apply A.mkQ g (A.mapQ A g (fun x hx => hg x hx)) (fun x => rfl) p₂ y
    rw [hp₂, LinearMap.aeval_self_charpoly] at this
    simpa using this
  ext x
  have hx : x = aeval g p₁ (aeval g a x) + aeval g p₂ (aeval g b x) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← LinearMap.add_apply, ← map_add (f := _),
      mul_comm p₁, mul_comm p₂, hab]
    simp
  rw [hx, map_add (f := _), hu.2 _ (h2 _), intertwine_aeval_apply u g g hug, h1 _ (hu.1 _)]
  simp

theorem exists_conj_eq_add_of_isCoprime : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A),
    IsCoprime (LinearMap.charpoly (g.restrict hg)) (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) →
    ∀ h ∈ nilRad A, ∃ e : V ≃ₗ[F] V, e.conj g = g + h := by
  intro F _ _ V _ _ _ A g hg hc h hh
  let N : Submodule F (Module.End F V) :=
    { carrier := nilRad A
      add_mem' := fun {a b} ha hb => ⟨fun x => A.add_mem (ha.1 x) (hb.1 x), fun x hx => by
        simp [ha.2 x hx, hb.2 x hx]⟩
      zero_mem' := ⟨fun x => A.zero_mem, fun x _ => rfl⟩
      smul_mem' := fun c a ha => ⟨fun x => A.smul_mem c (ha.1 x), fun x hx => by simp [ha.2 x hx]⟩ }
  let D : Module.End F V →ₗ[F] Module.End F V := LinearMap.mulRight F g - LinearMap.mulLeft F g
  have hD : ∀ u x, D u x = u (g x) - g (u x) := fun u x => rfl
  have hDN : ∀ u ∈ N, D u ∈ N := by
    intro u hu
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · rw [hD]; exact A.sub_mem (hu.1 _) (hg _ (hu.1 _))
    · rw [hD, hu.2 _ hx, hu.2 _ (hg _ hx)]; simp
  have hinj : Function.Injective (D.restrict hDN) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro u hu
    apply Subtype.ext
    refine nilRad_eq_zero_of_commute A g hg hc u.1 u.2 fun x => ?_
    have h0 : D u.1 = 0 := congrArg Subtype.val hu
    have := hD u.1 x
    rw [h0] at this
    exact sub_eq_zero.1 this.symm
  obtain ⟨u, hu⟩ := LinearMap.surjective_of_injective hinj ⟨h, hh⟩
  have hu' : D u.1 = h := congrArg Subtype.val hu
  obtain ⟨u, huA, hu0⟩ := u
  have huu : ∀ x, u (u x) = 0 := fun x => hu0 _ (huA x)
  refine ⟨LinearEquiv.ofLinearMap (1 + u) (1 - u) ?_ ?_, ?_⟩
  · ext x; simp [huu]
  · ext x; simp [huu]
  · ext x
    have h3 : u (g (u x)) = 0 := hu0 _ (hg _ (huA x))
    have h4 : h x = u (g x) - g (u x) := by rw [← hu']; rfl
    simp [LinearEquiv.conj_apply, h3, h4]
    abel

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsMonomialBasisOfImprimitive
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem exists_monomial_basis_of_imprimitive (k : Type) [Field k] (G : Type) [Group G] [Finite G]
    (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k G V)
    (T : Subgroup G) (W : Submodule k V)
    (hind : iSupIndep (fun q : G ⧸ T => W.map (ρ q.out)))
    (hsup : ⨆ q : G ⧸ T, W.map (ρ q.out) = ⊤)
    (hW : ∃ (n : ℕ) (b : Module.Basis (Fin n) k W), ∀ t ∈ T, ∀ i : Fin n,
      ∃ (j : Fin n) (c : k), ρ t (b i : V) = c • (b j : V)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k V), ∀ (g : G) (i : Fin n),
      ∃ (j : Fin n) (c : k), ρ g (b i) = c • b j := by
  classical
  obtain ⟨n, b, hb⟩ := hW
  have hinj : ∀ g : G, Function.Injective (ρ g) := by
    intro g x y h
    have h2 := congrArg (ρ g⁻¹) h
    simpa [← Module.End.mul_apply, ← map_mul] using h2
  have hint : DirectSum.IsInternal (fun q : G ⧸ T => W.map (ρ q.out)) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup
  let bq : ∀ q : G ⧸ T, Module.Basis (Fin n) k (W.map (ρ q.out)) := fun q =>
    b.map (Submodule.equivMapOfInjective (ρ q.out) (hinj _) W)
  let B := hint.collectedBasis bq
  have hB : ∀ (q : G ⧸ T) (i : Fin n), B ⟨q, i⟩ = ρ q.out (b i : V) := by
    intro q i
    simp [B, bq]
  haveI : Fintype (G ⧸ T) := Fintype.ofFinite _
  let e := Fintype.equivFin (Σ _ : G ⧸ T, Fin n)
  refine ⟨_, B.reindex e, fun g i => ?_⟩
  obtain ⟨⟨q, i⟩, rfl⟩ := e.surjective i
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul T (g * q.out)
  obtain ⟨j, c, hj⟩ := hb (t⁻¹ : T) (t⁻¹).2 i
  refine ⟨e ⟨(QuotientGroup.mk (g * q.out) : G ⧸ T), j⟩, c, ?_⟩
  simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, hB]
  rw [← map_smul, ← hj, ht, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  simp

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsWeightIdempotentStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weight_idempotent_of_eigenvector : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module L V] (ρ : Representation L G V) (B T : Subgroup G) (lam : B →* Lˣ) (v : V), B.Normal → v ≠ 0 → (∀ b : B, ρ b v = (lam b : L) • v) → (∀ g : G, g ∈ T ↔ ∀ b b' : B, (b' : G) = g⁻¹ * b * g → lam b' = lam b) → ∃ e : Module.End L V, e ≠ 0 ∧ e * e = e ∧ (∀ b : B, ρ b * e = (lam b : L) • e) ∧ (∀ t ∈ T, ρ t * e = e * ρ t) ∧ ∀ g ∉ T, e * ρ g * e = 0 := by
  first | exact @GlobalTheory.exists_weight_idempotent | exact GlobalTheory.exists_weight_idempotent | (intros; apply GlobalTheory.exists_weight_idempotent <;> assumption)
end

