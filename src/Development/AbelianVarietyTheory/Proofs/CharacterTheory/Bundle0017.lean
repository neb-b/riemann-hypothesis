module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumMobiusInverseCharpolyTransversalSubspaces
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.TraceLiftMonomialMatrixEqSumEigenvalues
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyEndomorphismDensityGLRecursion
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem cyclic_conj {F : Type} [Field F] {V V' : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup V'] [Module F V'] (e : V ≃ₗ[F] V') (g : Module.End F V) (v : V) :
    (∀ U : Submodule F V, (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤) ↔
      (∀ U : Submodule F V', (∀ x ∈ U, (e.conj g) x ∈ U) → e v ∈ U → U = ⊤) := by
  constructor
  · intro h U hU hv
    have h1 : U.comap (e : V →ₗ[F] V') = ⊤ := by
      refine h _ (fun x hx => ?_) hv
      have := hU (e x) hx
      simpa [LinearEquiv.conj_apply] using this
    refine eq_top_iff.2 fun y _ => ?_
    have : e.symm y ∈ U.comap (e : V →ₗ[F] V') := h1 ▸ Submodule.mem_top
    simpa using this
  · intro h U hU hv
    have h1 : U.comap (e.symm : V' →ₗ[F] V) = ⊤ := by
      refine h _ (fun x hx => ?_) (by simpa using hv)
      have := hU (e.symm x) hx
      simpa [LinearEquiv.conj_apply] using this
    refine eq_top_iff.2 fun y _ => ?_
    have : e y ∈ U.comap (e.symm : V' →ₗ[F] V) := h1 ▸ Submodule.mem_top
    simpa using this

theorem glCard_ne_zero_of_finite (F : Type) [Field F] [Finite F] (n : ℕ) : glCard F n ≠ 0 := by
  unfold glCard
  exact_mod_cast (Nat.card_pos (α := GL (Fin n) F)).ne'

theorem mass_const {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (c : ℂ) (P : F[X]) :
    mass (fun _ : Module.End F V => c) P = c * mass (fun _ : Module.End F V => (1 : ℂ)) P := by
  unfold mass
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Finite.of_injective (fun g : Module.End F V => (g : V → V))
    DFunLike.coe_injective
  have hs : {g : Module.End F V | LinearMap.charpoly g = P}.Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ hs]
  simp [mul_comm]

theorem mu_one (F : Type) [Field F] : mu (1 : F[X]) = 1 := by
  unfold mu
  have h : ∀ n : ℕ, n = 0 →
      mass (fun _ : Module.End F (Fin n → F) => (1 : ℂ)) 1 / glCard F n = 1 := by
    rintro n rfl
    have h1 : glCard F 0 = 1 := by
      unfold glCard
      haveI : Subsingleton (GL (Fin 0) F) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
      rw [Nat.card_unique]
      simp
    have h2 : {g : Module.End F (Fin 0 → F) | LinearMap.charpoly g = 1} = {0} := by
      ext g
      have hg : g = 0 := Subsingleton.elim _ _
      have hc : LinearMap.charpoly g = 1 := by
        apply (LinearMap.charpoly_monic g).natDegree_eq_zero.1
        rw [LinearMap.charpoly_natDegree]
        simp
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact ⟨fun _ => hg, fun _ => hc⟩
    unfold mass
    rw [h1, h2, finsum_mem_singleton]
    simp
  exact h _ natDegree_one

theorem mu_rec : ∀ (F : Type) [Field F] [Finite F] (P : F[X]), P.Monic →
    (Nat.card F : ℂ) ^ P.natDegree * mu P = conv (fun _ => 1) mu P ∧ mu (1 : F[X]) = 1 := by
  intro F _ _ P hP
  refine ⟨?_, mu_one F⟩
  have key := _root_.GlobalTheory.CuspGL.MassMult.mass_mult F (Fin P.natDegree → F)
    (fun V _ _ _ g => (Nat.card {v : V // ∀ U : Submodule F V, (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ))
    (by
      intro V V' _ _ _ _ _ _ e g
      congr 1
      exact (Nat.card_congr (e.toEquiv.subtypeEquiv fun v => cyclic_conj e g v)).symm)
    P hP (by simp)
  simp only [_root_.GlobalTheory.CuspGL.finsum_card_cyclic_eq] at key
  rw [mass_const] at key
  have hr : conv (fun D : F[X] => mass (fun g : Module.End F (Fin D.natDegree → F) =>
      (Nat.card {v : Fin D.natDegree → F // ∀ U : Submodule F (Fin D.natDegree → F),
        (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) D / glCard F D.natDegree) mu P
      = conv (fun _ => 1) mu P := by
    unfold conv
    refine finsum_mem_congr rfl fun x hx => ?_
    beta_reduce
    rw [GlobalTheory.T.endomorphismMassOfCharpoly_card_cyclic_vectors F x.1 hx.1, div_self (glCard_ne_zero_of_finite F _)]
  rw [← hr, ← key]
  unfold mu
  simp [mul_div_assoc]

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumMobiusInverseCharpolyTransversalSubspacesStatement
section
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_mobiusInverseCharpoly_transversal_subspaces : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ) (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A), ∑ᶠ x : {x : Module.End F V × Submodule F V // x.1 ∈ nilRad A ∧ x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2}, psi s x.1.2 ((g + x.1.1).restrict x.2.2.2) = (Nat.card (nilRad A) : ℂ) * s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) := by
  first | exact @GlobalTheory.CuspGL.finsum_psi_transversal | exact GlobalTheory.CuspGL.finsum_psi_transversal | (intros; apply GlobalTheory.CuspGL.finsum_psi_transversal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumUnipotentRadicalEqZeroStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_unipotent_radical_eq_zero_of_isPrimitive : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (φ : Module.End F (Fin d → F) → ℂ), IsPrimitive φ → ∀ a : ℕ, 0 < a → a < d → ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}, φ (Matrix.toLin' (u : Matrix (Fin d) (Fin d) F)) = 0 := by
  first | exact @GlobalTheory.CuspGL.IsPrimitive.finsum_unipotentRadical_eq_zero | exact GlobalTheory.CuspGL.IsPrimitive.finsum_unipotentRadical_eq_zero | (intros; apply GlobalTheory.CuspGL.IsPrimitive.finsum_unipotentRadical_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InnerProductRootPowerSumEqOfFrobeniusModEq
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem exists_algEquiv_pow_card_pow (F : Type) [Field F] [Finite F] (i : ℕ) :
    ∃ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, ∀ α, σ α = α ^ (Nat.card F ^ i) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  refine ⟨FiniteField.frobeniusAlgEquivOfAlgebraic F (AlgebraicClosure F) ^ i, fun α => ?_⟩
  induction i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ← pow_mul,
      Nat.card_eq_fintype_card, ← pow_succ]

theorem ipGL_rootSum_eq_of_modEq (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ) (φ : Module.End F V → ℂ) (hc : IsClassFn φ)
    (hp : IsPrimitive φ) (hn : 0 < Module.finrank F V) (k l i : ℕ)
    (h : k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ Module.finrank F V - 1)]) :
    ipGL φ (fun g : Module.End F V => rootSum θ k (LinearMap.charpoly g)) =
      ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_algEquiv_pow_card_pow F i
  rw [_root_.GlobalTheory.CuspGL.ipGL_rootSum_eq_sum_torus F V θ φ hc hp hn k, _root_.GlobalTheory.CuspGL.ipGL_rootSum_eq_sum_torus F V θ φ hc hp hn l]
  set N := Nat.card F ^ Module.finrank F V - 1 with hN
  have hmem : ∀ α : AlgebraicClosure F, α ^ N = 1 ↔ σ α ^ N = 1 := by
    intro α
    rw [← map_pow]
    exact ⟨fun h => by rw [h, map_one], fun h => σ.injective (by rw [h, map_one])⟩
  have hbij : Set.BijOn σ {α : AlgebraicClosure F | α ^ N = 1} {α : AlgebraicClosure F | α ^ N = 1} := by
    refine ⟨fun α hα => (hmem α).1 hα, σ.injective.injOn, fun β hβ => ⟨σ.symm β, ?_, σ.apply_symm_apply β⟩⟩
    show (σ.symm β) ^ N = 1
    rw [hmem, σ.apply_symm_apply]
    exact hβ
  refine (finsum_mem_eq_of_bijOn σ hbij fun α hα => ?_).symm
  have hα' : α ^ N = 1 := hα
  have hm : minpoly F (σ α) = minpoly F α := minpoly.algEquiv_eq σ α
  have hθ : θ α ^ N = 1 := by rw [← map_pow, hα', map_one]
  have key : ∀ a : ℕ, θ α ^ a = θ α ^ (a % N) := by
    intro a
    conv_lhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, hθ, one_pow, mul_one]
  have hpow : θ α ^ (Nat.card F ^ i * k) = θ α ^ l := by
    rw [key, key l, mul_comm]
    exact congrArg _ h
  rw [hm, hσ, map_pow, ← pow_mul, hpow]

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleCharacterLinearOrInducedAbelianByPrim
section
open GlobalTheory.BI
namespace GlobalTheory.BI

def weightStabiliser {L G : Type} [Field L] [Group G] (B : Subgroup G) (hB : B.Normal)
    (lam : B →* Lˣ) : Subgroup G where
  carrier := {g | ∀ b b' : B, (b' : G) = g⁻¹ * b * g → lam b' = lam b}
  one_mem' := by
    intro b b' h
    have : b' = b := Subtype.ext (by simpa using h)
    rw [this]
  mul_mem' := by
    intro g h hg hh b b' e
    have hc : g⁻¹ * (b : G) * g ∈ B := by
      simpa using hB.conj_mem b b.2 g⁻¹
    have h1 := hg b ⟨_, hc⟩ rfl
    have h2 := hh ⟨_, hc⟩ b' (by rw [e]; simp [mul_assoc])
    rw [h2, h1]
  inv_mem' := by
    intro g hg b b' e
    exact (hg b' b (by rw [e]; simp [mul_assoc])).symm

theorem nontrivial_of_isIrreducible {L G V : Type} [Field L] [Group G] [AddCommGroup V]
    [Module L V] (ρ : Representation L G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  obtain ⟨x, y, hxy⟩ := h.toNontrivial.exists_pair_ne
  exact hxy (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem irrChar_linear_or_induced : ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G] (χ : G → L), AbByP G → IsIrrChar L L χ → (∃ lam : G →* Lˣ, ∀ g, χ g = (lam g : L)) ∨ ∃ T : Subgroup G, T ≠ ⊤ ∧ ∃ ψ : T → L, IsChar L L ψ ∧ χ = ind T ψ := by
  intro L _ _ _ G _ _ χ hG ⟨n, ρ, hρ, hχ⟩
  have hχ' : ∀ g, χ g = ρ.character g := fun g => by simpa using hχ g
  haveI := nontrivial_of_isIrreducible ρ hρ
  by_cases hR : ∃ T : Subgroup G, T ≠ ⊤ ∧ ∃ ψ : T → L, IsChar L L ψ ∧ χ = ind T ψ
  · exact Or.inr hR
  left
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.idempotent_eq_one_and_character_eq_of_isIrreducible L G (Fin n → L) ρ hρ
  have hcomm : ∀ a b : G, ρ a * ρ b = ρ b * ρ a := by
    refine _root_.GlobalTheory.BI.commute_all G (Module.End L (Fin n → L)) ρ hG ?_
    intro B hB hBc
    obtain ⟨lam, v, hv, hlam⟩ := _root_.GlobalTheory.exists_character_eigenvector_of_commute L B (Fin n → L) (ρ.comp B.subtype)
      (fun a b => hBc a a.2 b b.2)
    obtain ⟨e, he0, hee, heB, heT, heN⟩ := GlobalTheory.T.exists_weight_idempotent_of_eigenvector L G (Fin n → L) ρ B
      (weightStabiliser B hB lam) lam v hB hv hlam (fun _ => Iff.rfl)
    obtain ⟨ψ, hψ, hind⟩ := _root_.GlobalTheory.BI.character_eq_ind_of_imprimitive L G (Fin n → L) ρ _ e hρ he0 hee heT heN
    have hT : weightStabiliser B hB lam = ⊤ := by
      by_contra hT
      exact hR ⟨_, hT, ψ, hψ, funext fun g => (hχ' g).trans (hind g)⟩
    have he1 : e = 1 := hs1 e he0 hee (fun g => heT g (hT ▸ Subgroup.mem_top g))
    intro b hb g
    have := heB ⟨b, hb⟩
    rw [he1, mul_one] at this
    change ρ b = _ at this
    rw [this, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  obtain ⟨lam, v, hv, hlam⟩ := _root_.GlobalTheory.exists_character_eigenvector_of_commute L G (Fin n → L) ρ hcomm
  exact ⟨lam, fun g => (hχ' g).trans (hs2 lam v hv hlam g)⟩

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterBrauerLiftAbelianByPrimePower
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem basis_smul_eq_smul_cancel {k V ι : Type} [Field k] [AddCommGroup V] [Module k V]
    (b : Module.Basis ι k V) {x y : k} {i j : ι} (hx : x ≠ 0) (h : x • b i = y • b j) :
    i = j ∧ x = y := by
  classical
  have h1 := congrArg (fun v => b.repr v i) h
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one, Finsupp.single_apply] at h1
  by_cases hij : j = i
  · subst hij
    simpa using h1
  · simp [hij, hx] at h1

theorem isChar_brauerLift : ∀ (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ), (∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (G : Type) [Group G] [Finite G], AbByP G → (Nat.card G : k) ≠ 0 → ∀ (n : ℕ) (ρ : G →* GL (Fin n) k), IsChar ℂ ℂ (fun g => ((Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) k)).roots.map θ).sum) := by
  intro k _ _ θ hθ G _ _ hG hc n ρ
  classical
  let R : Representation k G (Fin n → k) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _).toMonoidHom.comp
      (Units.coeHom _)).comp ρ
  have hR : ∀ g, R g = Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) k) := fun g => rfl
  obtain ⟨m, b, hb⟩ := _root_.GlobalTheory.CuspGL.exists_monomial_basis_of_abByP k G (Fin n → k) R hG hc
  choose s c hsc using hb
  have hc0 : ∀ g i, c g i ≠ 0 := by
    intro g i h0
    have h1 : R g (b i) = 0 := by rw [hsc, h0, zero_smul]
    have h2 : R (g⁻¹ * g) (b i) = 0 := by
      rw [map_mul, Module.End.mul_apply, h1, map_zero]
    rw [inv_mul_cancel, map_one, Module.End.one_apply] at h2
    exact b.ne_zero i h2
  have hmul : ∀ g h i, s (g * h) i = s g (s h i) ∧ c (g * h) i = c g (s h i) * c h i := by
    intro g h i
    apply basis_smul_eq_smul_cancel b (hc0 _ _)
    rw [← hsc, map_mul, Module.End.mul_apply, hsc, map_smul, hsc, smul_smul, mul_comm]
  have hone : ∀ i, s 1 i = i ∧ c 1 i = 1 := by
    intro i
    apply basis_smul_eq_smul_cancel b (hc0 _ _)
    rw [← hsc, map_one, Module.End.one_apply, one_smul]
  let σ : G → Equiv.Perm (Fin m) := fun g =>
    { toFun := s g
      invFun := s g⁻¹
      left_inv := fun i => by rw [← (hmul _ _ _).1, inv_mul_cancel, (hone i).1]
      right_inv := fun i => by rw [← (hmul _ _ _).1, mul_inv_cancel, (hone i).1] }
  let L : G →* Matrix (Fin m) (Fin m) ℂ :=
    { toFun := fun g => Matrix.of fun i j => if i = σ g j then θ (c g j) else 0
      map_one' := by
        ext i j
        simp [σ, (hone j).1, (hone j).2, Matrix.one_apply]
      map_mul' := by
        intro g h
        ext i j
        simp [σ, Matrix.mul_apply, (hmul g h j).1, (hmul g h j).2] }
  have hM : ∀ g, (Matrix.of fun i j => if i = σ g j then c g j else 0 : Matrix (Fin m) (Fin m) k)
      = LinearMap.toMatrix b b (R g) := by
    intro g
    ext i j
    simp [σ, LinearMap.toMatrix_apply, hsc, Finsupp.single_apply, eq_comm]
  refine ⟨m, (Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ℂ ≃ₐ[ℂ] _).toMonoidHom.comp L, fun g => ?_⟩
  have h1 : (Matrix.of fun i j => if i = σ g j then c g j else 0 : Matrix (Fin m) (Fin m) k)
      ^ Nat.card G = 1 := by
    rw [hM, LinearMap.toMatrix_pow, ← map_pow, pow_card_eq_one', map_one, LinearMap.toMatrix_one]
  have h2 : L g ^ Nat.card G = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
  have h3 := _root_.GlobalTheory.MonoTrace.trace_lift_monomial k θ hθ m (Nat.card G) (σ g) (c g) (hc0 g) hc h1 h2
  rw [hM, LinearMap.charpoly_toMatrix, hR, Matrix.charpoly_toLin'] at h3
  show _ = LinearMap.trace ℂ _ (Matrix.toLin' (L g))
  rw [Matrix.trace_toLin'_eq]
  exact h3.symm

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInductionIrreducible
section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.isChar_induction :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G]
      [Finite G] (Q : (G → L) → Prop), Q 0 →
      (∀ φ c : G → L, _root_.GlobalTheory.BI.IsIrrChar K L φ → _root_.GlobalTheory.BI.IsChar K L c →
        Q c → Q (φ + c)) → ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → Q a := by
  intro K L _ _ _ _ _ G _ _ Q h0 hstep
  have hchar : ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → ∃ n : ℕ, a 1 = n := by
    intro a ha
    unfold _root_.GlobalTheory.BI.IsChar at ha
    obtain ⟨n, ρ, hρ⟩ := ha
    exact ⟨n, by rw [hρ 1, Representation.char_one, Module.finrank_fin_fun, map_natCast]⟩
  have hirr : ∀ φ : G → L, _root_.GlobalTheory.BI.IsIrrChar K L φ →
      ∃ m : ℕ, 0 < m ∧ φ 1 = m := by
    intro φ hφ
    unfold _root_.GlobalTheory.BI.IsIrrChar at hφ
    obtain ⟨m, ρ, hρirr, hρ⟩ := hφ
    refine ⟨m, Nat.pos_of_ne_zero fun hm => ?_, by
      rw [hρ 1, Representation.char_one, Module.finrank_fin_fun, map_natCast]⟩
    subst hm
    have hs : IsSimpleOrder (Subrepresentation ρ) := hρirr
    obtain ⟨x, y, hxy⟩ := hs.toNontrivial.exists_pair_ne
    apply hxy
    ext v
    rw [Subsingleton.elim v 0]
    exact ⟨fun _ => y.toSubmodule.zero_mem, fun _ => x.toSubmodule.zero_mem⟩
  have key : ∀ n : ℕ, ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → a 1 = n → Q a := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha ha1
      by_cases hz : a = 0
      · rw [hz]; exact h0
      obtain ⟨φ, c, hφ, hc, rfl⟩ := _root_.GlobalTheory.BI.exists_irrChar_add K L G a ha hz
      obtain ⟨m, hm, hφ1⟩ := hirr φ hφ
      obtain ⟨k, hk1⟩ := hchar c hc
      have hn : n = m + k := by
        have hsum : ((m + k : ℕ) : L) = n := by
          rw [Nat.cast_add, ← hφ1, ← hk1]
          exact ha1
        exact_mod_cast hsum.symm
      exact hstep φ c hφ hc (ih k (by omega) c hc hk1)
  intro a ha
  obtain ⟨n, hn⟩ := hchar a ha
  exact key n a ha hn

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersOfAbelianByPrimePower
section
noncomputable section
namespace GlobalTheory.BI

theorem mem_virt_of_forall_abByP (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K]
    [CharZero L] (G : Type) [Group G] [Finite G]
    (hH : ∀ H : Subgroup G, AbByP H → ∀ ψ : H → L, IsChar L L ψ → IsChar K L ψ) :
    ∀ χ : G → L, IsChar L L χ → χ ∈ Virt K L G := by
  let S : AddSubgroup (G → ℤ) :=
    { carrier := {f | ∀ χ : G → L, IsChar L L χ → (fun g => (f g : L) * χ g) ∈ Virt K L G}
      zero_mem' := by
        intro χ _
        have : (fun g => (((0 : G → ℤ) g : ℤ) : L) * χ g) = 0 := by
          funext g; simp
        rw [this]; exact zero_mem _
      add_mem' := by
        intro a b ha hb χ hχ
        have : (fun g => (((a + b) g : ℤ) : L) * χ g)
            = (fun g => (a g : L) * χ g) + (fun g => (b g : L) * χ g) := by
          funext g; simp [add_mul]
        rw [this]; exact add_mem (ha χ hχ) (hb χ hχ)
      neg_mem' := by
        intro a ha χ hχ
        have : (fun g => (((-a) g : ℤ) : L) * χ g) = -(fun g => (a g : L) * χ g) := by
          funext g; simp
        rw [this]; exact neg_mem (ha χ hχ) }
  have hS : ∀ f : G → ℤ, f ∈ S ↔
      ∀ χ : G → L, IsChar L L χ → (fun g => (f g : L) * χ g) ∈ Virt K L G := fun _ => Iff.rfl
  have hmul : ∀ f ∈ S, ∀ f' ∈ S, f * f' ∈ S := by
    intro f hf f' hf'
    rw [hS] at hf hf' ⊢
    intro χ hχ
    obtain ⟨a, b, ha, hb, hab⟩ := (_root_.GlobalTheory.BI.mem_virt_iff_sub K L G _).1 (hf' χ hχ)
    have : (fun g => (((f * f') g : ℤ) : L) * χ g)
        = (fun g => (f g : L) * a g) - (fun g => (f g : L) * b g) := by
      funext g
      have h := congrFun hab g
      simp only [Pi.sub_apply] at h
      simp only [Pi.mul_apply, Pi.sub_apply, Int.cast_mul]
      rw [mul_assoc, h, mul_sub]
    rw [this]
    exact sub_mem (hf a (GlobalTheory.BI.isChar_baseChange K L G a ha)) (hf b (GlobalTheory.BI.isChar_baseChange K L G b hb))
  have hperm : ∀ H : Subgroup G, AbByP H →
      (fun g => (Nat.card (MulAction.fixedBy (G ⧸ H) g) : ℤ)) ∈ S := by
    intro H hA
    rw [hS]
    intro χ hχ
    obtain ⟨hres, hconj, -⟩ := GlobalTheory.isChar_restrict_conj_one L L G χ hχ
    have h1 : IsChar K L (fun h : H => χ h) := hH H hA _ (hres H H.subtype)
    have h2 := _root_.GlobalTheory.BI.isChar_ind K L G H _ h1
    have : (fun g => (((Nat.card (MulAction.fixedBy (G ⧸ H) g) : ℤ)) : L) * χ g)
        = ind H (fun h : H => χ h) := by
      funext g
      rw [_root_.GlobalTheory.BI.ind_restrict_eq_card_fixedBy_mul L G H χ hconj g, Int.cast_natCast]
    rw [this]
    exact AddSubgroup.subset_closure h2
  have hone : (1 : G → ℤ) ∈ S := by
    refine GlobalTheory.T.one_mem_of_mul_mem_of_forall_prime_exists_not_dvd G S hmul fun x p hp => ?_
    obtain ⟨H, hA, hp'⟩ := _root_.GlobalTheory.BI.exists_abelianByPrimePower_not_dvd_card_fixedBy₂ G x p hp
    exact ⟨_, hperm H hA, fun h => hp' (Int.natCast_dvd_natCast.1 h)⟩
  intro χ hχ
  simpa using (hS 1).1 hone χ hχ

end GlobalTheory.BI
end
end

